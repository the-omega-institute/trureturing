---
slug: nathanson-2025-sumset-intersection-nonmaximal
bibkey: nathanson2025sumsetintersection
doi: 10.1017/S0004972726101270
url: https://arxiv.org/abs/2512.23574v3
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.result
---

# Nathanson Problem 2: nonmaximal nonbases and sumset intersections

## Problem

M. B. Nathanson, *Intersections of sumsets in additive number theory*, arXiv:2512.23574v3, Problem 2, p. 6, asks:

> Let $A$ be a subset of the infinite abelian semigroup $S$ such that $A$ is a nonbasis of order $h$ but not a maximal nonbasis of order $h$ for $S$. Does there exist an asymptotically strictly decreasing sequence $(A_q)_{q=1}^{\infty}$ of subsets of $S$ such that $A=\bigcap_{q=1}^{\infty}A_q$ and $hA=\bigcap_{q=1}^{\infty}hA_q$? In particular, consider this problem for $S=\mathbb Z$.

The universal assertion is false. The Lean refutation uses $S=\mathbb Z$, $h=2$ and $A=\{n\in\mathbb Z:\operatorname{Even}(n)\land n\ne2\}$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Infinite abelian semigroup $S$ | `S : Type`, `AddCommSemigroup S`, `Infinite S` in `claim` | No additive identity is required. |
| Positive order $h$ | Natural-number order and the premise $1\le h$ | The refutation specializes it to $h=2$. |
| $h$ not necessarily distinct summands from $A$ | `sumset` | Positive-order recursion uses pointwise set addition; its auxiliary zero-order value is empty and never enters `claim`. |
| A nonbasis of order $h$ | Negation of `IsBasis h A` | `IsBasis` is equality of `sumset A h` with the ambient universal set. |
| Not a maximal nonbasis | Negation of the literal conjunction in `claim` | Maximality retains nonbasis status and basis status of every proper superset. |
| Decreasing, with infinitely many unequal successive terms | `AsymptoticallyStrictlyDecreasing` | Successor inclusion and an unequal step beyond every natural bound; the index starts at zero. |
| $A=\bigcap_q A_q$ | The first intersection equality in `claim` | Equality is oriented with the intersection on the left. |
| $hA=\bigcap_q hA_q$ | The second intersection equality in `claim` | Equality is oriented with the intersection on the left. |
| Existence for every source-admissible $S,h,A$ | `claim` and its negation `result` | All hypotheses and both intersection equalities are retained. |

Every public binder and conjunct is accounted for above. The positive-index integer predicate in `NathansonProblem12AffineInvariance` is restricted to integer sets; it does not define the required arbitrary-semigroup predicate. Mathlib's monoid natural scalar action needs an identity and has a different zero-order value. Neither is substituted for a literal convention here. The maximal-nonbasis condition is inlined literally in `claim`; the private proof uses Mathlib `Maximal` via `Set.maximal_iff_forall_ssuperset`, with no duplicate predicate.

## Motivation

The settling GID is `D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal.result`. Its admission basis is `open-problem-resolution (#20722; Refuted)`. [Preregistration #20722](https://github.com/the-omega-institute/trureturing/issues/20722) supplies the question, literal conventions, proof and bounded literature screen. The source note is `Library/ArithUnits/nathanson2025sumsetintersection.md`.

## Gap

Being a nonmaximal nonbasis does not ensure the required approximation. A proper nonbasis superset can differ from $A$ by only finitely many elements, whereas an asymptotically strictly decreasing approximation must have infinitely many extra elements at every stage. In this example those extra elements force odd representations in every stage sumset.

The escape audit for `D5.S3.Arith.Additive.NathansonSumsetIntersectionNonmaximal.result` is unfinished under [#27767](https://github.com/the-omega-institute/trureturing/issues/27767). With `utility: none`, this symbolic result has no utility-refutation exemption. No Reg mirror or validated registration is claimed. Missing evidence is a faithful typed realization/readout of the exact source assertion, its reconstruction bridge and variation/sensitivity proofs.

## Route

The private helper `stage_sdiff_infinite` bounds the disappearance indices of a hypothetical finite stage difference using `Finite.exists_le`; antitonicity would then make the sequence eventually constant. The helper `stage_odd_infinite` removes the exceptional even integer $2$ by `Set.Infinite.sdiff`. The helper `odd_mem_stage_sumset` uses `Set.Infinite.exists_notMem_finite` to choose an odd $b$ distinct from $n-2$, and represents each odd $n$ as $(n-b)+b$. The parity and pointwise-addition facts come from pinned Mathlib; no D5 module is imported. `result` applies these steps to $n=1$ and contradicts the asserted sumset equality.

## Falsifier

For the refutation to fail, there would have to be an asymptotically strictly decreasing family with intersection $A=2\mathbb Z\setminus\{2\}$ and with $1$ absent from some stage's two-fold sumset, or $1$ present in $A+A$. The private lemmas exclude the former and parity excludes the latter. Finite samples alone establish neither universal exclusion.

## Evidence

`D5.S3.Arith.Additive.NathansonSumsetIntersectionNonmaximal.result` proves the negation of the literal universal assertion. The public surface consists of four necessary definitions and this one theorem. Five private theorems and the private concrete witness serve that result. The module has `generality: I`, `utility: none`, `proof_shape: bind-only`, and no claimed escape witness. Its Scribe carries one Refuted `OpenProblemResolutionClaim` on the settling node.

### Finite experiment

[Experiment at immutable commit `941e62fe339291b2adfdf1720fa4b905f1666363`](https://github.com/the-omega-institute/trureturing-experiments/tree/941e62fe339291b2adfdf1720fa4b905f1666363/docs/reports/nathanson-2025-sumset-intersection-nonmaximal).

Command: `git -C /Users/auric/trureturing-experiments show 941e62fe339291b2adfdf1720fa4b905f1666363:docs/reports/nathanson-2025-sumset-intersection-nonmaximal/check.py | python3`; exit 0. Script SHA-256: `e90d02ac2cec489534c978c19f93f947f7353acae3d9c48ee1bd338112e36db5`. Its successful finite checks use input integers in $[-400,400]$ and compare sumsets on $[-60,60]$, with intermediate sums restricted to $[-1200,1200]$. The introduction's tail example is tested for $q\in\{1,3,7\}$ and $h\in\{2,3,4\}$. Maximality of $h\mathbb Z$ is checked in its residue formulation for $2\le h\le40$. For $F\in\{\{2\},\{0\},\{2,4,10\},\{-6,8\}\}$ and $h\in\{2,3,4\}$, the program checks the window equality for $hA_F$, the proper even nonbasis superset, and three sampled stages per pair. All sampled stages contain every odd integer in the comparison window in their order-$h$ sumset. These are finite stage samples, not a computation of an infinite sequence or an infinite intersection.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Negative answer to Problem 2 | Proved; kernel-checked | `result` refutes the universal assertion using the single integer instance $h=2$, $F=\{2\}$. |
| Nonbasis | Proved; kernel-checked private lemma | `not_basis_of_subset_even` excludes a two-fold basis for every subset of the evens; it is applied to the witness by `result`. |
| Nonmaximality | Proved; kernel-checked private lemma | `punctured_even_not_maximal` uses the proper nonbasis superset of all even integers. |
| Infinite stage difference | Proved; kernel-checked private lemma | `stage_sdiff_infinite` proves this for arbitrary decreasing families with the specified intersection and arbitrarily late strict changes. |
| Infinite odd subset and odd representations | Proved; kernel-checked private lemmas | `stage_odd_infinite` and `odd_mem_stage_sumset` give every odd integer in each stage's two-fold sumset for the witness. |
| Failure mechanism beyond maximal nonbases | Proved in prose | The finite-puncture derivation below explains how infinitely many elements of the other parity class force every stage to be a basis. |
| Every finite nonempty $F\subseteq2\mathbb Z$ and every $h\ge2$ | Proved in prose | The derivation below proves $hA_F=2\mathbb Z$ and $hA_q=\mathbb Z$ for every admissible family. It is not an additional Lean theorem. |
| Existence of admissible families | Proved in prose | The odd-tail construction below has intersection $A_F$ and changes at every step. |
| Introduction example | Computed | The pinned experiment verifies exactly the windows and parameters given in Evidence. |
| Maximality of $h\mathbb Z$ iff $h$ is prime | Computed | Only the residue check for $2\le h\le40$ is asserted as computed here. |
| Finite punctures and sampled stage sums | Computed | Four punctures, three orders and three sampled stages per pair, with the window bounds given in Evidence. |
| Order-one sumset equality | Proved in prose | Since the one-fold sumset equals the set itself, its intersection equality is automatic for any family. |
| Surviving source statements | Literature reading | Source Theorems 5 and 6 retain their stated scopes, as explained below. |
| Other source results | Literature reading | The question is posed as a problem; no theorem is claimed invalidated. Theorem 6's maximality condition remains sufficient, but is not necessary for the obstruction. |
| Classification of nonmaximal nonbases admitting a preserving approximation | Open | No such classification is established. |
| Proof shape, admission and utility | Judgement | All delivered theorem rows are bind-only; the named external settlement supplies admission, and the proof has no computational utility claim. |
| Literature completeness | Open; `ASSUMED-UNVERIFIED` | The bounded literature screen below does not establish exhaustive absence of prior solutions. |
| Four-slot escape audit | Open | #27767 identifies the public `result` and the missing registration evidence. |

Let $E=2\mathbb Z$, let $F\subset E$ be finite and nonempty, and put $A_F=E\setminus F$. For any $n\in E$, the set $F\cup\{n-f:f\in F\}$ is finite, so choose an even $a$ outside it. Then $a,n-a\in A_F$, proving $2A_F=E$. Choose $a_0\in A_F$. For $h\ge2$, represent $n-(h-2)a_0$ by two elements of $A_F$ and append $h-2$ copies of $a_0$. Parity proves the reverse inclusion, hence $hA_F=E$. The proper superset $E$ remains a nonbasis, so $A_F$ is nonmaximal.

For an admissible family, if $A_q\setminus A_F$ were finite, each extra element would leave at a finite index; a common bound for those indices would force every later set to equal $A_F$, contradicting arbitrarily late strict changes. Thus each stage difference is infinite. Removing its possible elements of $F$ leaves infinitely many odd elements. For odd $n$, choose an odd $b\in A_q$ outside the finite set $\{n-f:f\in F\}$. Then $n-b\in A_F\subseteq A_q$, so $n\in2A_q$. Also $E=2A_F\subseteq2A_q$, hence $2A_q=\mathbb Z$. Padding a representation of $n-(h-2)a_0$ gives $hA_q=\mathbb Z$ for every $h\ge2$. Consequently $\bigcap_qhA_q=\mathbb Z\ne E=hA_F$. This proves the finite-puncture family in prose; only its $F=\{2\}$, $h=2$ refutation is kernel-checked here.

Admissible sequences exist: $A_q=A_F\cup\{2m+1:m\in\mathbb Z,\ m\ge q\}$ decreases strictly and has intersection $A_F$. For $h=1$, sumsets equal the original sets, so the intersection equality itself is automatic. These are prose deductions, not further Lean declarations.

Source Theorem 5 states existence for infinite integer sets bounded below that omit arbitrarily large integers; the punctured even sets are unbounded below. Source Theorem 6 supplies an obstruction for maximal nonbases. Both statements remain compatible with this refutation and neither is on this module's dependency path. The remaining classification problem above stays open.

### Literature status

The preregistration records the search seat's readings of the source versions and journal statement, and the orchestrator's readings of arXiv:2603.14510, 2603.15556 and 2604.04781. No direct settlement was found in that bounded screen. The asymptotic-basis conventions in older papers do not establish the literal equality notion used here. The 1974 paper *Minimal bases and maximal nonbases in additive number theory* is not recorded as fully read. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Exhaustive literature completeness and global absence of a prior published solution are `ASSUMED-UNVERIFIED`. The finite-puncture family, higher orders, admissible-family construction and order-one boundary are proved in prose, not by additional Lean declarations. Finite computations have only their stated scope. The four-slot escape audit is unfinished under #27767; no `declared_validated` status is claimed.
