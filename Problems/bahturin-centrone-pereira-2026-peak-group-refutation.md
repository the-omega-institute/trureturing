---
slug: bahturin-centrone-pereira-2026-peak-group-refutation
bibkey: bahturincentronepereira2026peak
doi: 10.48550/arXiv.2608.21936
url: https://arxiv.org/abs/2608.21936v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.result
---

## Problem

Bahturin, Centrone and Pereira, *Quantum regularity of finite dimensional semisimple algebras*, arXiv:2608.21936v1, Conjecture 31, asks whether every peak group satisfies exactly one of solvability and the stated Frobenius-complement alternative. The preregistration is [#19254](https://github.com/the-omega-institute/trureturing/issues/19254).

The settling declaration is `D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.result`. It proves the negation of the literal `claim`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A peak group has a greatest irreducible-character degree for divisibility. | `BCP31.IsPeak` and `BCP31.degreeSet` | The degree set is defined by simple finite-dimensional complex representations, and every degree divides the selected degree. |
| A Frobenius complement is nontrivial, proper, and has trivial intersection with each conjugate outside it. | `BCP31.IsFrobeniusWithComplement` | The subgroup-map expression is the literal conjugation condition. |
| The complement quotient contains the specified `SL(2, 5) × T` normal subgroup, with cyclic Sylows and excluded primes. | `BCP31.ComplementCondition` and `BCP31.AlternativeTwo` | The quantified finite group `T` and all three structural conditions are retained. |
| Exactly one of solvability and the Frobenius alternative holds for every finite peak group. | `BCP31.claim` | The result proves the full negation, including the exclusive-or conjunction. |

## Motivation

The counterexample is the direct product $B \times C_2$, where $B$ is the source's semidirect product of $(\mathbb{Z}/11\mathbb{Z})^2$ by $\mathrm{SL}(2,5)$. The supporting declarations show that $B$ has peak degree $120$, that adjoining the abelian factor preserves the simple degree set, and that the resulting group is nonsolvable.

## Gap

The source leaves Conjecture 31 open. The settlement addresses the conjecture through the concrete group specified in #19254. Literature completeness remains `ASSUMED-UNVERIFIED`; the source and the recorded literature screen do not establish an exhaustive search of later work.

## Route

The module constructs the sparse $\mathrm{SL}(2,5)$ action on $(\mathbb{Z}/11\mathbb{Z})^2$, verifies the finite action certificates, forms the semidirect product and its direct product with $C_2$, constructs a simple degree-$120$ representation, and proves that every simple degree divides $120$. The abelian-product theorem transfers peakness. The central-obstruction theorem shows that a nontrivial central element rules out every Frobenius complement, while the $\mathrm{SL}(2,5)$ quotient rules out solvability.

## Falsifier

A finite group satisfying the literal `claim` would not falsify the result. A contradiction would require a counterexample to one of the kernel-checked declarations, especially the degree divisibility, degree-$120$ simplicity, or central obstruction statements.

## Evidence

The compiled settling module has the public definitions `degreeSet`, `IsPeak`, `IsFrobeniusWithComplement`, `fitting`, `HasCyclicSylows`, `HasAllowedOrder`, `ComplementCondition`, `AlternativeTwo`, and `claim`, together with the public theorem `result`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The other public theorems in the delivered modules have an unfinished escape audit recorded in [#19389](https://github.com/the-omega-institute/trureturing/issues/19389).

## Triage

### What the settlement shows

- **Mechanism — proved, kernel-checked.** `FrobeniusCentralObstruction.central_eq_one_of_frobenius` proves that a Frobenius complement forces every central element to be the identity. The direct $C_2$ factor supplies a nontrivial central element, so the peak group is not Frobenius.
- **Peakness — proved, kernel-checked.** `ComplexCharacterAbelianProducts.degreesProdAbelian` preserves the simple degree set under a finite abelian direct product. The settling declarations establish the degree-$120$ member and divisibility of all simple degrees, so the constructed direct product is peak.
- **Nonsolvability — proved, kernel-checked.** The settling path uses the nonsolvability of $\mathrm{SL}(2,5)$ and the semidirect-product quotient to prove that the constructed group is not solvable.
- **Nearest surviving statement — proved, kernel-checked.** For any group $B$ and finite abelian group $A$, the delivered theorem `ComplexCharacterAbelianProducts.degreesProdAbelian` states equality of the simple degree sets of $B \times A$ and $B$.
- **Source dependence — literature reading.** Conjecture 31 is the final mathematical statement in the cited source section; this settlement makes no claim about later source results.
- **Follow-up: trivial centre — open.** Whether an analogue of Conjecture 31 holds for peak groups with trivial centre is outside `result`.
- **Follow-up: direct indecomposability — open.** Whether an analogue holds for directly indecomposable peak groups is outside `result`.
- **Experiment — `ASSUMED-UNVERIFIED`.** The supplied preregistration does not name an experiment repository, commit, script hash, or exit code. No experiment citation is asserted.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The experiment citation requested by the lane is absent from the supplied issue material, so no experiment result is used as evidence. The two follow-up questions are recorded as open repository follow-ups rather than as separately verified published open problems.
