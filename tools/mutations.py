"""Apply each mutation to a green tree, build, record the failure, restore.

A proof that has never been observed failing is decoration. This script is how
`MUTATIONS.md` is produced, and re-running it is how the claim is re-checked.

Files are read and written as bytes so the round-trip is exact, and captured
output is filtered so that no absolute path from the machine that ran it reaches
the committed file.

    python tools/mutations.py
"""

import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ENV = dict(os.environ)
_elan = os.path.join(os.path.expanduser("~"), ".elan", "bin")
if os.path.isdir(_elan):
    ENV["PATH"] = _elan + os.pathsep + ENV.get("PATH", "")

MUTATIONS = [
    dict(
        name="The empty clause is given a free pass instead of needing a pivot",
        file="Ratified/Proof.lean",
        old="  | [] => false\n  | p :: _ => isRAT f c p",
        new="  | [] => true\n  | p :: _ => isRAT f c p",
        rule="`ratOnHead` returns `false` on the empty clause",
        why="A checker that lets the last line through as a formality accepts every "
            "file that ends in `0`. The empty clause has to be RUP.",
    ),
    dict(
        name="A proof that runs out without deriving the empty clause is accepted",
        file="Ratified/Proof.lean",
        old="  | [] => false\n  | .add c :: rest =>",
        new="  | [] => true\n  | .add c :: rest =>",
        rule="`checkProof` returns `false` on the empty step list",
        why="Reaching the end of a proof is not the same as refuting the formula.",
    ),
    dict(
        name="Propagation assigns literals no clause forces",
        file="Ratified/Propagate.lean",
        old="  decide (l ∈ c) && isUnassigned t l &&\n"
            "    c.all (fun l' => decide (l' = l) || isFalse t l')",
        new="  decide (l ∈ c) && isUnassigned t l",
        rule="`isUnitOn` requires every other literal of the clause to be false",
        why="Refute's own source calls this one out: a bug that assigns a literal no "
            "clause forces makes every subsequent check easier to pass, and on the "
            "DRAT path there is nothing in the file to contradict it.",
    ),
    dict(
        name="Propagation is allowed to reassign a variable",
        file="Ratified/Propagate.lean",
        old="  decide (l ∈ c) && isUnassigned t l &&\n"
            "    c.all (fun l' => decide (l' = l) || isFalse t l')",
        new="  decide (l ∈ c) &&\n"
            "    c.all (fun l' => decide (l' = l) || isFalse t l')",
        rule="`isUnitOn` requires the forced literal to be unassigned",
        why="Without it propagation can put a variable on the trail twice, and the "
            "fuel bound stops being finite for the reason `fuelFor` claims. This is "
            "what makes the progress theorems load-bearing rather than decorative.",
    ),
    dict(
        name="The candidate set is truncated",
        file="Ratified/RAT.lean",
        old="  f.filter (fun d => decide (p.negate ∈ d))",
        new="  (f.filter (fun d => decide (p.negate ∈ d))).take 1",
        rule="`ratCandidates` returns every clause holding the negated pivot",
        why="Miss one clause and the RAT condition was never checked for it, so an "
            "arbitrary clause is added on evidence that looks fine.",
    ),
    dict(
        name="The lemma is dropped from its own resolvent",
        file="Ratified/RAT.lean",
        old="  c ++ d.filter (fun l => decide (l ≠ p.negate))",
        new="  d.filter (fun l => decide (l ≠ p.negate))",
        rule="`resolvent` is the whole of `C ∨ (D \\ {¬p})`, lemma included",
        why="Checking the wrong clause is checking nothing.",
    ),
    dict(
        name="Propagation is given no fuel",
        file="Ratified/RUP.lean",
        old="  f.foldl (fun n cl => n + cl.length) 0 + c.length + 1",
        new="  (f.foldl (fun n cl => n + cl.length) 0 + c.length) * 0",
        rule="`fuelFor` allows enough propagation to reach the conflicts that exist",
        why="This is the one rule here that is about completeness rather than "
            "soundness, and the mutation demonstrates the difference exactly: every "
            "soundness theorem still compiles, because none of them depends on the "
            "fuel being generous. What fails is the executable side -- the checker "
            "stops accepting real refutations. A soundness proof cannot catch this "
            "and is not supposed to.",
    ),
]


def build():
    proc = subprocess.run(
        ["lake", "build"],
        cwd=REPO,
        env=ENV,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        shell=(os.name == "nt"),
    )
    return proc.returncode, (proc.stdout or "") + (proc.stderr or "")


def sanitise(text, limit=8):
    """Error lines only, and never one carrying a path from this machine."""
    keep = []
    for line in text.splitlines():
        low = line.lower()
        if ":\\" in low or ":/" in low or "lean_path" in low or low.startswith("trace:"):
            continue
        if "error:" in line:
            keep.append(line.rstrip())
        if len(keep) >= limit:
            keep.append("... (truncated)")
            break
    return keep


def caught_by(errors):
    """Which gate fired: a soundness proof, or an executable check."""
    for line in errors:
        if line.startswith("error: ") and ".lean:" in line:
            module = line[len("error: "):].split(":", 1)[0]
            kind = (
                "an executable check"
                if module.endswith(("Examples.lean", "Audit.lean"))
                else "a soundness proof"
            )
            return "`{}`, {}".format(module, kind)
    return "the build, location not recorded"


def main():
    code, out = build()
    if code != 0:
        print("baseline is not green, aborting", file=sys.stderr)
        print(out[:2000], file=sys.stderr)
        return 1
    print("baseline green")

    results = []
    for mutation in MUTATIONS:
        path = os.path.join(REPO, mutation["file"].replace("/", os.sep))
        with open(path, "rb") as handle:
            original = handle.read()
        old = mutation["old"].encode("utf-8")
        new = mutation["new"].encode("utf-8")
        found = original.count(old)
        if found != 1:
            print(
                "anchor matched {} times for {!r}, expected exactly 1".format(
                    found, mutation["name"]
                ),
                file=sys.stderr,
            )
            return 1
        try:
            with open(path, "wb") as handle:
                handle.write(original.replace(old, new))
            code, out = build()
        finally:
            with open(path, "wb") as handle:
                handle.write(original)
        killed = code != 0
        results.append((mutation, killed, sanitise(out)))
        print(("KILLED   " if killed else "SURVIVED ") + mutation["name"])

    code, out = build()
    if code != 0:
        print("restore failed, tree is not green again", file=sys.stderr)
        print(out[:2000], file=sys.stderr)
        return 1
    print("restored, green")

    killed_count = sum(1 for _, killed, _ in results if killed)
    lines = [
        "# Mutation evidence",
        "",
        "A proof that has never been observed failing is decoration. Every rule in",
        "this development that could be quietly dropped is listed here with the",
        "mutation that drops it and the resulting build failure. Each was applied to a",
        "green tree, built, and reverted, and the tree was rebuilt green afterwards.",
        "",
        "Regenerate with `python tools/mutations.py`, which does exactly that and",
        "rewrites this file.",
        "",
        "**{} of {} mutations killed.**".format(killed_count, len(results)),
        "",
    ]
    for mutation, killed, errors in results:
        lines.append("## " + mutation["name"])
        lines.append("")
        lines.append("- **Rule:** " + mutation["rule"])
        lines.append("- **Why it is load-bearing:** " + mutation["why"])
        lines.append("- **File:** `" + mutation["file"] + "`")
        lines.append(
            "- **Verdict:** "
            + ("KILLED, the build fails" if killed else "SURVIVED, NOT PINNED")
        )
        if killed:
            lines.append("- **Caught by:** " + caught_by(errors))
        lines.append("")
        lines.append("```diff")
        for line in mutation["old"].splitlines():
            lines.append("-" + line)
        for line in mutation["new"].splitlines():
            lines.append("+" + line)
        lines.append("```")
        lines.append("")
        if errors:
            lines.append("```")
            lines.extend(errors)
            lines.append("```")
            lines.append("")
    with open(os.path.join(REPO, "MUTATIONS.md"), "w", encoding="utf-8", newline="\n") as handle:
        handle.write("\n".join(lines))
    print("wrote MUTATIONS.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
