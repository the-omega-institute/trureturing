---
slug: oeis-a397436-general-supercongruence
bibkey: oeis2026a397436
doi: null
url: https://oeis.org/A397436/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation
---

# A397436: the unrestricted product supercongruence

## Problem

The selected external assertion is OEIS A397436 revision 44, Conjecture 3,
quoted in Library/ArithSums/oeis2026a397436.md. It asserts the following
complete same-r event, with arbitrary signed m and inclusive endpoints:

```lean
noncomputable def U {r : ℕ} (m : Fin r → ℤ) (M n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (M * n + 1), ∏ i : Fin r, Ring.choose (m i * (n : ℤ)) k

def claim : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (m : Fin r → ℤ) (M : ℕ), 0 < M →
    ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
      (p : ℤ) ^ (3 * r) ∣ U m M (p ^ r) - U m M (p ^ (r - 1))

theorem result : ¬ claim
```

The last line displays the theorem type; its proof lives in D5. Natural
subtraction r-1 agrees with the source exponent because r is positive.

## Motivation

`question_answered`: does the published unrestricted universal congruence
hold? A single admissible tuple suffices to refute it. This is a Tier 1
source-labelled candidate, with prospective formal-unit registration at
https://github.com/the-omega-institute/trureturing/issues/23456#issuecomment-6485402841.
The registration body SHA-256 is
`9a1097346c21436cfb9bfa7382a3945ff78c8807555eef6bc92baec1074c1746`.

## Gap

`dominating_theorem_search: not-found-in-searched-scope`. Repository searches
including private declarations and pinned Mathlib found no exact claim
refutation. IntegerIndexBinomial has a natural upper argument and cannot
encode the full signed event. The related A375178 result concerns a
different binomial-cube sum. A supplied exact-ID third-party Lean search
returned no hits. The bounded literature scope and access limits are in
the source note; no exhaustive absence or priority claim follows.

## Route

Instantiate the same r everywhere by 1, take m(0)=1, M=1 and p=5. Positivity,
primality and the lower bound on p are discharged in Lean. Fin 1 gives one
factor. Ring.choose_natCast rewrites its positive upper argument to
Nat.choose. The inclusive high row is 1,5,10,10,5,1 and the low row is 1,1.
Thus U(5)=32, U(1)=2 and their difference is 30. The requested modulus is
5^(3*1)=125, which does not divide 30. This contradicts the complete claim.

## Falsifier

A mismatch in the signed domain, inclusive truncation, shared r or modulus
would invalidate source fidelity. Failure of the two sum evaluations or
nondivisibility would invalidate the witness. A prior complete external
settlement would invalidate open-problem eligibility independently of the
kernel proof. An intended restriction absent from the printed assertion
would define a different target requiring separate qualification.

## Evidence

The canonical mathematical source is
D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.lean. Its declarations
are U, claim : Prop, and result : ¬ claim. It uses the pinned Mathlib
Ring.choose_natCast bridge, kernel-reduced finite arithmetic and no native
decision oracle. The Blueprint attaches ResolutionKind.Refuted to result.
No freezing, independent delivery review, required CI or merge is asserted.

## Triage

`proof_shape: bind-only` for result: instantiate the universal statement,
apply the existing generalized-binomial bridge, normalize finite arithmetic
and derive contradiction. U and claim are required source encodings, not
separate theorem results. The consumed evaluation fact is local to result.
`admission_basis: open-problem-resolution`; `escape_witness: none`;
`computational_content.kind: certified-instance`; utility uses the exact
`refutes=gid:D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.claim`
edge. There are no direct frozen project dependencies. The designated
refutation result is exempt from four-slot escape registration; there are
no other public theorems in this delivery.

The failure mechanism is already present in a permitted one-factor,
positive-parameter case: the two binomial row totals differ by 30 rather
than a multiple of 125. Signed upper arguments are not the cause of this
witness. This result addresses only the unrestricted item 3. It does not
settle Conjectures 1 or 2, or prove or refute the special negative-parameter
two-factor sequence's supercongruence. Whether additional source-motivated
restrictions yield valid adjacent statements remains unproved here.

## ASSUMED-UNVERIFIED

Source fidelity, proof-shape classification and external eligibility need
independent review. The source note's original-source and literature readings
are supplied completed qualification evidence, not freshly reproduced
primary-byte or worldwide literature checks. Author intent beyond the
printed statement, novelty and priority remain outside this result.
