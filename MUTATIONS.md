# Mutation evidence

A proof that has never been observed failing is decoration. Every rule in
this development that could be quietly dropped is listed here with the
mutation that drops it and the resulting build failure. Each was applied to a
green tree, built, and reverted, and the tree was rebuilt green afterwards.

Regenerate with `python tools/mutations.py`, which does exactly that and
rewrites this file.

**6 of 6 mutations killed.**

## The empty clause is given a free pass instead of needing a pivot

- **Rule:** `ratOnHead` returns `false` on the empty clause
- **Why it is load-bearing:** A checker that lets the last line through as a formality accepts every file that ends in `0`. The empty clause has to be RUP.
- **File:** `Ratified/Proof.lean`
- **Verdict:** KILLED, the build fails
- **Caught by:** `Ratified/Proof.lean`, a soundness proof

```diff
-  | [] => false
-  | p :: _ => isRAT f c p
+  | [] => true
+  | p :: _ => isRAT f c p
```

```
error: Ratified/Proof.lean:69:10: unsolved goals
error: Lean exited with code 1
error: build failed
```

## A proof that runs out without deriving the empty clause is accepted

- **Rule:** `checkProof` returns `false` on the empty step list
- **Why it is load-bearing:** Reaching the end of a proof is not the same as refuting the formula.
- **File:** `Ratified/Proof.lean`
- **Verdict:** KILLED, the build fails
- **Caught by:** `Ratified/Proof.lean`, a soundness proof

```diff
-  | [] => false
-  | .add c :: rest =>
+  | [] => true
+  | .add c :: rest =>
```

```
error: Ratified/Proof.lean:103:8: unsolved goals
error: Lean exited with code 1
error: build failed
```

## Propagation assigns literals no clause forces

- **Rule:** `isUnitOn` requires every other literal of the clause to be false
- **Why it is load-bearing:** Refute's own source calls this one out: a bug that assigns a literal no clause forces makes every subsequent check easier to pass, and on the DRAT path there is nothing in the file to contradict it.
- **File:** `Ratified/Propagate.lean`
- **Verdict:** KILLED, the build fails
- **Caught by:** `Ratified/Propagate.lean`, a soundness proof

```diff
-  decide (l ∈ c) && isUnassigned t l &&
-    c.all (fun l' => decide (l' = l) || isFalse t l')
+  decide (l ∈ c) && isUnassigned t l
```

```
error: Ratified/Propagate.lean:98:12: Function expected at
error: Lean exited with code 1
error: build failed
```

## The candidate set is truncated

- **Rule:** `ratCandidates` returns every clause holding the negated pivot
- **Why it is load-bearing:** Miss one clause and the RAT condition was never checked for it, so an arbitrary clause is added on evidence that looks fine.
- **File:** `Ratified/RAT.lean`
- **Verdict:** KILLED, the build fails
- **Caught by:** `Ratified/RAT.lean`, a soundness proof

```diff
-  f.filter (fun d => decide (p.negate ∈ d))
+  (f.filter (fun d => decide (p.negate ∈ d))).take 1
```

```
error: Ratified/RAT.lean:93:18: Invalid `⟨...⟩` notation: The expected type
error: Lean exited with code 1
error: build failed
```

## The lemma is dropped from its own resolvent

- **Rule:** `resolvent` is the whole of `C ∨ (D \ {¬p})`, lemma included
- **Why it is load-bearing:** Checking the wrong clause is checking nothing.
- **File:** `Ratified/RAT.lean`
- **Verdict:** KILLED, the build fails
- **Caught by:** `Ratified/RAT.lean`, a soundness proof

```diff
-  c ++ d.filter (fun l => decide (l ≠ p.negate))
+  d.filter (fun l => decide (l ≠ p.negate))
```

```
error: Ratified/RAT.lean:102:47: Application type mismatch: The argument
error: Ratified/RAT.lean:104:35: Application type mismatch: The argument
error: Ratified/RAT.lean:105:66: Application type mismatch: The argument
error: Ratified/RAT.lean:105:15: unsolved goals
error: Lean exited with code 1
error: build failed
```

## Propagation is given no fuel

- **Rule:** `fuelFor` allows enough propagation to reach the conflicts that exist
- **Why it is load-bearing:** This is the one rule here that is about completeness rather than soundness, and the mutation demonstrates the difference exactly: every soundness theorem still compiles, because none of them depends on the fuel being generous. What fails is the executable side -- the checker stops accepting real refutations. A soundness proof cannot catch this and is not supposed to.
- **File:** `Ratified/RUP.lean`
- **Verdict:** KILLED, the build fails
- **Caught by:** `Ratified/Examples.lean`, an executable check

```diff
-  f.foldl (fun n cl => n + cl.length) 0 + c.length + 1
+  (f.foldl (fun n cl => n + cl.length) 0 + c.length) * 0
```

```
error: Ratified/Examples.lean:31:0: Expression
error: Ratified/Examples.lean:36:70: Tactic `decide` proved that the proposition
error: Ratified/Examples.lean:57:0: Expression
error: Ratified/Examples.lean:58:0: Expression
error: Lean exited with code 1
error: build failed
```
