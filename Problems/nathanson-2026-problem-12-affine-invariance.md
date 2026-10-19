---
slug: nathanson-2026-problem-12-affine-invariance
bibkey: nathanson2026sumintersections
doi: 10.48550/arXiv.2604.04781
url: https://arxiv.org/abs/2604.04781v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.result
---

# Nathanson's Problem 12: affine invariance of sum intersection sets

## Problem

Melvyn B. Nathanson, *Problems and results on intersections of product sets and sumsets in semigroups*, arXiv:2604.04781v2, Problem 12, p. 21, asks:

> Let $(A_q)$ and $(A'_q)$ be asymptotically strictly decreasing sequences of sets of integers such that $A'_q=sA_q+t$ for all $q\in\mathbb N$ and some $s,t\in\mathbb Z$ with $s\notin\{0,\pm1\}$. Does this imply $H(A_q)=H(A'_q)$?

The paper takes $\mathbb N=\{1,2,3,\ldots\}$, defines $A=\bigcap_q A_q$ and $H(A_q)=\{h\in\mathbb N:hA=\bigcap_q hA_q\}$, and uses $hB$ for the $h$-fold sumset. Asymptotically strict decrease means $A_{q+1}\subseteq A_q$ at every index, with infinitely many strict changes. The answer to Problem 12 is affirmative.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Two sequences of integer sets indexed by positive integers | `A A' : ℕ+ → Set ℤ` in `claim` | The paper's positive-natural indexing is literal. |
| Both sequences asymptotically strictly decreasing | `AsymptoticallyStrictlyDecreasing A` and its primed counterpart | The definition retains adjacent inclusion and infinitely many unequal neighbours. |
| The $h$-fold sumset | Pointwise `h • B` | This is repeated set addition, with independent summands. |
| Positive sum lengths and the sum-intersection equality | `H` | Its natural-number carrier is restricted by `0 < h`. |
| $A'_q=sA_q+t$ at every index | The affine `Set.image` hypothesis in `claim` | It is the literal set $\{sa+t:a\in A_q\}$. |
| Integer $s,t$ and $s\notin\{0,\pm1\}$ | Integer parameters and the exclusion hypothesis in `claim` | All three excluded values are retained. |
| $H(A_q)=H(A'_q)$ | Conclusion of `claim`; `result : claim` | No source premise is dropped from the delivered statement. |

Every explicit binder and conjunct comes from these clauses. The Boolean-free formulas in the Scribe display the three definition bodies and the complete proposition of the settling theorem.

## Motivation

The settling GID is `D5/S3/Arith/Additive/NathansonProblem12AffineInvariance.result`, with `admission_basis: open-problem-resolution (#18994; Proved)`. [Preregistration #18994](https://github.com/the-omega-institute/trureturing/issues/18994) supplies the source, literal Lean conventions and literature screen. The source is recorded in `Library/ArithUnits/nathanson2026sumintersections.md`.

## Gap

Theorem 15 of the source treats unit multipliers through an affine equivalence relation. Problem 12 asks about non-unit multipliers, for which an inverse integer multiplier is unavailable. The proof needs injectivity rather than surjectivity.

The escape audit for `D5.S3.Arith.Additive.NathansonProblem12AffineInvariance.result` is unfinished under [#19056](https://github.com/the-omega-institute/trureturing/issues/19056). The missing evidence is a compiled source-faithful realization and original-telescope bridge, occurrence selection for the sum-intersection readout, and whole-family variation, sensitivity and actual observational-dependence proofs. No Reg registration is delivered or claimed validated.

## Route

For each $h$, let $f_h(x)=sx+ht$. The non-unit hypothesis supplies $s\ne0$, and cancellation makes $f_h$ injective. The local `hinj` uses `mul_left_cancel₀` and `add_right_cancel`. The local `hinter` directly applies `Set.InjOn.image_iInter_eq`, using the nonempty positive-natural index type. The local `hsum` composes `nsmul_add`, `Set.image_nsmul` and `Set.nsmul_singleton` to transport $h$-fold sumsets. The local `hbase` transports the family intersection. Finally `Set.image_eq_image` reflects equality under $f_h$. These are pinned Mathlib dependencies used by `result`; no D5 owner is imported.

## Falsifier

A source-admissible pair of families and a non-unit multiplier with unequal sum-intersection sets would falsify the affirmative answer. The proof checks the affine-image relation, both decrease premises, the multiplier exclusion and equality of the complete sets of positive sum lengths. Finite tests alone do not establish this unbounded assertion.

## Evidence

`D5.S3.Arith.Additive.NathansonProblem12AffineInvariance.result` proves `claim`. The public surface is the three necessary definitions and this single theorem; the auxiliary facts remain local to its proof. The module has `generality: G` and `utility: none`. Its proof shape is `bind-only`, with no new general escape content claimed. Its Scribe carries exactly one Proved `OpenProblemResolutionClaim` on `result`.

### Finite experiment

[Experiment at commit `cbc37a1af11d37601b3a816a0f94a1bb87a93a41`](https://github.com/the-omega-institute/trureturing-experiments/tree/cbc37a1af11d37601b3a816a0f94a1bb87a93a41/docs/reports/nathanson-2026-problem12-affine-invariance).

Command: `git -C /Users/auric/trureturing-experiments show cbc37a1af11d37601b3a816a0f94a1bb87a93a41:docs/reports/nathanson-2026-problem12-affine-invariance/check.py | python3`; exit 0. Script SHA-256: `43ff71f338b0a9c896edeeee2d964e3ba6229d69971c58cabde1484fcb066f9d`. The script tests 400 random finite families of two to five finite integer sets with a nonempty common core, at every $s\in\{-3,-2,2,3,5\}$ and $t\in\{-4,0,7\}$. It compares membership in $H$ only for $1\le h\le4$: 6,000 affine cases, zero mismatches, and 291 families missing at least one tested sum length. This is a finite computation on arbitrary, potentially non-nested families, rather than a check of infinite decreasing sequences.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Settlement of Problem 12 | Proved; kernel-checked | `D5.S3.Arith.Additive.NathansonProblem12AffineInvariance.result` proves the full literal `claim`. |
| Decisive mechanism | Proved in prose | The injective affine transport derivation below proves the identity; surjectivity and an inverse integer multiplier are unnecessary. |
| Arbitrary families and every nonzero integer multiplier | Proved in prose | The derivation uses no decrease premise and only $s\ne0$. The Lean theorem retains the source's stronger premises; no companion theorem is delivered. |
| Injective affine maps in torsion-free modules | Proved in prose | For modules over $\mathbb Z$, the same derivation applies whenever multiplication by the chosen scalar is injective; torsion-freeness and $s\ne0$ suffice. The index set must be nonempty. This extension is not a Lean theorem in this module. |
| Zero multiplier in the arbitrary-family extension | Proved in prose | The decreasing nonempty family below has $H=\{1\}$, while its zero-multiplier image has every positive sum length. The image family is constant and hence not asymptotically strictly decreasing. |
| New general module and escape novelty | Open literature boundary | No separate general module or new general escape witness is claimed. The named-problem settlement is subject to literature completeness `ASSUMED-UNVERIFIED`. |
| Finite check | Computed | The pinned experiment in Evidence has exactly the stated 6,000-case scope and does not establish any additional universal theorem. |
| Theorem 15 and other source questions | Literature reading | Theorem 15 states the unit case and is compatible with the nonzero-multiplier identity. It is not on this module's dependency path. The other source questions receive no additional settlement claim. |

For the transport derivation, let $Q$ be nonempty, $A=\bigcap_{q\in Q}A_q$, and $f_h(x)=sx+ht$. If multiplication by $s$ is injective, each $f_h$ is injective. For any family $C_q$, an element of every $f_h(C_q)$ has a preimage at one fixed index. Injectivity forces all its other preimages to equal that one, proving $f_h(\bigcap_q C_q)=\bigcap_q f_h(C_q)$. Distributing a sum of $h$ affine terms gives $h(f_1(B))=f_h(hB)$, with the converse obtained from the same $h$ summands. Thus $\bigcap_q A'_q=f_1(A)$, $h(\bigcap_q A'_q)=f_h(hA)$, and $\bigcap_q hA'_q=f_h(\bigcap_q hA_q)$. Equality on the primed side is equivalent to equality on the unprimed side by injectivity. This proves the arbitrary-family and injective-scalar extensions in prose.

For the zero-scalar boundary, take $A_q=\{0\}\cup\{z\in\mathbb Z:|z|\ge q\}$ for positive $q$. Their intersection is $\{0\}$ and they decrease strictly. For any $z$ choose a positive integer $n$ so large that $n\ge q$ and $n-z\ge q$. Then $z=n+(z-n)$ is a sum of two elements of $A_q$, so $2A_q=\mathbb Z$; padding by zero gives $hA_q=\mathbb Z$ for $h\ge2$. Consequently $H(A_q)=\{1\}$. At $s=0$, every affine image is $\{t\}$ and every positive sum length satisfies the intersection identity. This is a prose counterexample to dropping nonzeroness in the arbitrary-family extension; it is not a counterexample to the source statement.

### Literature status

The preregistration records readings of arXiv:2604.04781v2, Sections 1–2, Lemma 7, Theorem 15 and Problem 12, and the search seat's screen of van Doorn–Monticone–Tang, arXiv:2604.18869v2. That paper's advertised resolutions concern Problems 10, 11 and parts of 4 and 7. The recorded repository and issue screen found no settlement of Problem 12. These bounded readings are not an exhaustive literature search.

## ASSUMED-UNVERIFIED

Literature completeness and the absence of every prior published solution are `ASSUMED-UNVERIFIED`. The arbitrary-family, nonzero-scalar, torsion-free-module and zero-scalar discussions above are prose proofs, not additional kernel-checked declarations. The four-slot escape audit remains unfinished under #19056; no registration is claimed `declared_validated`.
