---
slug: uhlmann-2023-diagonal-majorization-question
bibkey: uhlmann2023spectralmajorization
doi: 10.46571/JCI.2023.2.4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.result
url: https://arxiv.org/abs/2309.01302v1
---

# Uhlmann's unrestricted diagonal-majorization question

## Problem

Jeffrey Uhlmann, *Partial Proof of a Conjecture with Implications for Spectral Majorization*, arXiv:2309.01302v1, Section 4, asks about removing the dimensional restriction from the diagonal-spectrum majorization relationship:

> However, the fact that such a construction does not generally exist for n > 6 does not necessarily imply that the diagonal-spectrum majorization relationship does not hold in general.

> Empirical investigation may be able to provide sufficient evidence to justify a conjecture or, alternatively, empirical and/or analytical efforts may identify counterexamples that constrain such generalizations

The assertion is that for every natural dimension $n$, every real symmetric positive definite $P$, and every real diagonal $D$, the diagonal of $PDP^{-1}$ majorizes its spectrum. The spectrum is the vector of diagonal entries of $D$. Section 3 defines $x\prec y$ by $x=Sy$ for a doubly stochastic matrix $S$. Preregistration: [#18572](https://github.com/the-omega-institute/trureturing/issues/18572).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $x\prec y$ iff $x=Sy$, with $S$ doubly stochastic | `Majorizes y x` | Literal existential definition using Mathlib's `doublyStochastic`. |
| Every dimension | `n : ℕ` in `claim` | No upper bound is imposed. |
| Real symmetric positive definite $P$ | `P : Matrix (Fin n) (Fin n) ℝ` and `P.PosDef` | Over the reals, Mathlib's Hermitian condition is symmetry. |
| Every real diagonal $D$ | `d : Fin n → ℝ` and `Matrix.diagonal d` | All real entries are allowed. |
| Spectrum of $PDP^{-1}$ is majorized by its diagonal | Final `Majorizes` expression in `claim` | The diagonal is the majorizing vector and `d` the majorized vector. |
| The unrestricted assertion is false | `result : ¬ claim` | One seven-dimensional instance refutes the universal statement. |

No positivity requirement on $D$ is added; the chosen witness also has positive diagonal entries. The source's small-dimension theorem retains its dimensional hypothesis.

## Motivation

The settling GID is `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.result`. Its admission basis is `open-problem-resolution (#18572; Refuted)`. Its proof shape is bind-only after expansion of the private helpers, using pinned Mathlib criteria and finite arithmetic. No separate escape witness is asserted.

## Gap

Positive definiteness of the similarity matrix alone does not ensure the doubly stochastic relationship in unrestricted dimension. In the witness, the least diagonal entry of the similarity is strictly greater than the least spectral entry, which contradicts a necessary convex-combination bound.

## Route

Let $e\in\mathbb R^5$ have every entry one, and set

$$
P=\begin{pmatrix}10&1&2e^{\mathsf T}\\1&10&2e^{\mathsf T}\\2e&2e&10I_5\end{pmatrix},
\qquad D=\operatorname{diag}(1,20,2,2,2,2,2).
$$

The private helper `p_sos` verifies

$$
(x,y,z)^{\mathsf T}P(x,y,z)=10\sum_{i=1}^{5}(z_i+(x+y)/5)^2+\frac72(x+y)^2+\frac92(x-y)^2.
$$

Its vanishing forces $x=y=0$ and then all $z_i=0$. `p_posDef` uses `Matrix.PosDef.of_dotProduct_mulVec_pos` to obtain positive definiteness. `p_mul_q` verifies the exact right inverse; `p_inv` uses `Matrix.inv_eq_right_inv`. `diag_eq` evaluates the diagonal to

$$v=(64/63,1565/63,36/35,36/35,36/35,36/35,36/35).$$

`v_lower` bounds every entry below by $64/63$. `not_majorizes` uses the unit row sums and nonnegative entries of a doubly stochastic matrix, with `convex_Ici(...).sum_mem`, to bound its first coordinate applied to $v$ below by $64/63$. That coordinate cannot equal the first spectral entry $1$. `result` applies this obstruction to `claim`.

## Falsifier

An error in positive definiteness, the exact inverse, the diagonal evaluation, or the stochastic lower bound would invalidate this witness. The named private helpers and public `result` check those obligations without additional hypotheses or axioms beyond the standard closure. No classification of all positive definite similarities is claimed by the Lean module.

## Evidence

The Lean module and corresponding Scribe mirror carry the fixed-instance refutation. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other public theorems or published owners in this delivery.

Experiment: [uhlmann-2023-pd-diagonalizable-majorization at `65de77d642c949fc7345e8925672d34307a37483`](https://github.com/the-omega-institute/trureturing-experiments/tree/65de77d642c949fc7345e8925672d34307a37483/docs/reports/uhlmann-2023-pd-diagonalizable-majorization). Command: `python3 check.py` in that directory; exit 0. Script SHA-256: `7e2bce3c0890339462b9868b892f54fc5ae6b6eccf29c54941f1fa5e7bb75cef`.

The exact SymPy computation checks positive definiteness, the sum-of-squares identity, the seven diagonal entries, their sum $31$, minimum $64/63>1$ and maximum $1565/63>20$. It verifies symbolic diagonal formulas for $D(c,r)=\operatorname{diag}(c,c+r,c+1,c+1,c+1,c+1,c+1)$. Its control tests the necessary minimum/maximum majorization inequalities on 200 seeded random positive definite matrices in dimension four. The control does not test the full majorization relation or prove a universal statement.

## Triage

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| Settlement | **Kernel-checked:** `result` refutes `claim`. | The unrestricted assertion; a fixed $7\times7$ witness. |
| Admitted settlement and helper classification | **Kernel-checked proof with semantic classification:** `result` and its seven consumed private helpers are bind-only; the admission basis is the preregistered external open-problem resolution. | No claim of an escape witness or additional public theorem. |
| Preregistration | **Source reading:** #18572 is a read-only input specifying the source, conventions and settlement. | No modification of that issue is part of this delivery. |
| Failure mechanism | **Kernel-checked:** `p_posDef`, `diag_eq`, `v_lower`, `not_majorizes`, used by `result`. | Positive definiteness coexists with $\min\operatorname{diag}(PDP^{-1})>\min\operatorname{spec}(D)$. |
| Exact sum, maximum and symbolic family formulas | **Computed:** the experiment in Evidence. | The fixed instance and the displayed symbolic seven-dimensional family. |
| Incomparability of the two fixed vectors | **Proved in prose:** the minimum obstruction is checked in Lean; conversely, $1565/63>20$ excludes expressing $v$ as a doubly stochastic image of `d`. | The fixed vectors only. |
| Parameter family | **Proved in prose:** the derivation below from the computed exact formulas. | $c>0$ and $18<r<39/2$; not formalized here. |
| Higher dimensions | **Proved in prose:** the direct-sum argument below. | Every $n\ge7$; not formalized here. |
| Four-dimensional control | **Computed:** 200 random matrices, seed 1, as in Evidence. | Necessary extreme-coordinate inequalities only. |
| Surviving source results | **Literature reading:** Section 3's dimensional restriction and constructions using factors satisfying the property retain their stated hypotheses. | The unrestricted extension is the proposition refuted. |
| Sharp dimensional boundary and classification | **Open:** this module does not decide every dimension below seven or characterize all admissible $P$. | Separate mathematical questions. |
| Literature status | **ASSUMED-UNVERIFIED:** the screen recorded in #18572 found no settlement in its searched scope. | Exhaustiveness and the secondary-source readings are not established by this Lean proof. |

### Prose extensions and limits

For the same $P$, the experiment verifies

$$
\operatorname{diag}(PD(c,r)P^{-1})-c\mathbf1=
\left(\frac{r-18}{63},\frac{80r-18}{63},\frac{39-2r}{35},\frac{39-2r}{35},\frac{39-2r}{35},\frac{39-2r}{35},\frac{39-2r}{35}\right).
$$

When $18<r<39/2$, all entries on the right are positive. The least spectral entry is $c$, whereas every diagonal entry exceeds $c$. The same convex-combination argument therefore refutes the relationship throughout this parameter interval. This is a prose consequence of the computed symbolic identity, rather than a kernel-checked family theorem.

For $n>7$, append $I_{n-7}$ to $P$ and append diagonal entries $2$ to the fixed $D$. The resulting similarity is the direct sum of the original similarity and $2I_{n-7}$. Positive definiteness is preserved, the least spectral entry remains $1$, and every diagonal entry still exceeds $1$. This proves the higher-dimensional extension in prose; the Lean module checks only dimension seven.

The source's theorem for special PD-diagonalizable matrices includes its dimensional restriction. Its small-dimension results are not contradicted by this witness. The broader constructions that assume the required factor property keep that premise; this refutation supplies no unrestricted replacement for it.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source v1 Sections 3–4 and the preregistration supply the problem statement. The preregistration reports that the journal revision keeps the passage; that Uhlmann, DOI 10.1515/spma-2022-0185, retains a dimensional restriction; and that Uhlmann–Wang, arXiv:1906.00931, Section 6, gives an inverse-RGA obstruction rather than this diagonal-spectrum counterexample. These secondary-source readings are reported from the preregistration, not independently re-established by this delivery. The parameter-family and direct-sum arguments are prose proofs, not additional Lean theorems.
