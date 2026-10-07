---
slug: bourin-lee-2021-essentially-hermitian-block-norm
bibkey: bourinlee2021inradius
doi: 10.1142/S0129167X22500094
url: https://arxiv.org/abs/2111.15180v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/BlockNorm/EssentiallyHermitian.result
---

# Essentially Hermitian off-diagonal blocks

## Problem

J.-C. Bourin and E.-Y. Lee, *Eigenvalue inequalities for positive block matrices with the inradius of the numerical range*, arXiv:2111.15180v1, printed page 6, Conjecture 3.3, states:

> Let $X\in\mathbb{M}_n$. If the inequality
>
> $$\left\|\begin{bmatrix}A&X\\X^*&B\end{bmatrix}\right\|_\infty\le\|A+B\|_\infty$$
>
> holds for all positive block-matrix with $X$ as off-diagonal block, then $X$ is essentially Hermitian.

The source says: “If W(T) is line segment, then T is a so-called essentially Hermitian matrix.” The binding convention of [#13752](https://github.com/the-omega-institute/trureturing/issues/13752) is the literal affine expression $X=\alpha H+\beta I$, with $H=H^*$ and $\alpha,\beta\in\mathbb C$, including points. The norm is the Euclidean operator norm, and positive means positive semidefinite. The same question is Conjecture 7.3.3 of Bourin's *A journey into Matrix Analysis*, arXiv:2307.03064v1, printed page 114.

## Motivation

The inequality tests every positive completion of a fixed off-diagonal matrix. Its consequence is a global spectral geometry: all eigenvalues lie on one real affine line. The statement ranges over every $n\ge1$ and every complex $n\times n$ matrix, without invertibility or distinct singular values.

## Gap

Issue #13752 preregisters this Tier 1 published conjecture before Lean work. Its literature readings distinguish Hayashi's normality theorem for invertible matrices with distinct singular values, arXiv:1808.00181, from the full affine-Hermitian conclusion. The issue records MathDB's zero-solution listing, checks of arXiv:2609.20094 and arXiv:2402.06791, and repository searches: no settlement found in that searched scope. These are bounded literature evidence, not an exhaustive priority claim.

## Route

For Hermitian $D$, set $K_X(D)=\begin{bmatrix}D&X\\X^*&-D\end{bmatrix}$. Positive scalar shifts and unitary block reflection imply $\lambda_{\max}(K_X(D))+\lambda_{\min}(K_X(D))=0$.

For a unit vector $v$, Hermitian $S$ with $Sv=0$, and $D=t vv^*+S$, the finite-parameter edge-sum estimate is

$$\left|\lambda_{\max}(K_X(D))+\lambda_{\min}(K_X(D))-\frac{a}{t}-\frac{b}{t^2}\right|\le\frac{1782L^4}{t^3},$$

where $t\ge96L$, $L\ge\max(1,\|K_X(S)\|)$,
$a=\|X^*v\|^2-\|Xv\|^2$, and
$b=\operatorname{Re}\langle Xv,SXv\rangle-\operatorname{Re}\langle X^*v,SX^*v\rangle$.
The individual positive-edge enclosure has error $891L^4/t^3$; block reflection gives the negative-edge enclosure. A reduced-resolvent construction supplies the approximate eigenvector and residual; the frozen residual-energy estimate bounds the upper error.

The vanishing edge sum forces $a=0$ and $b=0$. The first identity gives normality. Testing the second with the difference of two projected rank-one matrices gives their equality. Unitary diagonalization and the centered cross-product identity then reconstruct $X=\alpha H+\beta I$.

## Falsifier

Replacing the operator norm by the Frobenius norm changes the conclusion to normality. Replacing the universal positive-completion hypothesis by one completion changes the statement. Neither replacement is the encoded conjecture. The public definitions use the literal block matrix, positivity and affine expression.

## Evidence

The canonical Lean sources are `D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate.lean` and `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.lean`. The public settling theorem is `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.result : claim`. Its Scribe carries a `Proved` resolution for this dossier. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

`positive_spike_enclosure` supplies the quantitative content of the first module. The three bind-only public helpers `upper_shift_iff`, `outer_action` and `outer_hermitian` have consumers in the spike or settling proofs. The second module exposes only `EssentiallyHermitian`, `CompletionBound`, `claim` and `result`; all its private helpers are on the settling proof path. Diagonalization code is adapted from the TauCeti contributors under Apache-2.0, with source and license in [the Library note](../Library/QuantumStates/bourinlee2021inradius.md).

## Triage

Tier 1; `theorem`; resolution `proved`. `SpikeEdgeEstimate` has `admission_basis: escape-witness`, with `positive_spike_enclosure`. `EssentiallyHermitian` has `admission_basis: open-problem-resolution` under #13752 and `proof_shape: content` for `result`. This is an analytic all-dimension theorem, with `utility: none`; no finite enumeration or certified instance is delivered. There is no digestion atom. Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module — Hayashi's normality question.** The private `completion_bound_normal`, used by `result`, gives $X^*X=XX^*$ from the universal operator-norm completion bound in every $n\ge1$. It requires neither invertibility nor distinct singular values, and therefore includes the normality question in Problem 4 of arXiv:1808.00181.
- **Proved as a consequence of `result` — existence of violating positive completions.** For every matrix that is not essentially Hermitian, there are $A,B$ with $\begin{bmatrix}A&X\\X^*&B\end{bmatrix}\succeq0$ and $\|A+B\|<\|\begin{bmatrix}A&X\\X^*&B\end{bmatrix}\|$. The classical contrapositive is checked by the Lean example below. **Open:** a separately exported algorithm, an explicit formula for these $A,B$ for arbitrary $X$, and effective extraction of a finite threshold. The proof uses finite rank-one spikes; existence does not supply an algorithmic interface.
- **Proved in the delivered modules — decisive mechanism.** `positive_spike_enclosure` and `edge_sum_bound` give uniform finite-$t$ error bounds. The private `edge_symmetry`, `completion_bound_normal`, `completion_bound_projected_outer` and `centered_outer_eq_implies_affine_real` establish the spectral symmetry, normality, projected rank-one equality and affine reconstruction on the path to `result`.
- **Open — further unitarily invariant norms.** No characterization for other norms is proved here. The Frobenius case is excluded from this open item because the source already settles it.
- **Proved in the cited source — Frobenius characterization.** Proposition 3.4, printed page 6, states that the universal Frobenius-norm inequality is equivalent to normality; the monograph repeats it as Proposition 7.3.4, printed page 114. It is not newly formalized in this delivery, and the operator-norm conclusion is stronger.
- **Proved for the named implication — source and monograph.** `result` settles Conjecture 3.3 and its identical Conjecture 7.3.3 restatement. The source's known converse supplies the other direction of the operator-norm characterization in literature. The independent numerical-range bounds and Frobenius proposition retain their stated conclusions. **Open in this delivery:** a Lean formalization of that converse and a combined equivalence; no new downstream corollary is exported.
- **Open — sharpness and extensions.** The constants $96$, $891$ and $1782$ are sufficient; their optimality is not proved. The all-dimension result includes scalar matrices, singular matrices and repeated singular values. Infinite-dimensional extensions and weaker completion hypotheses are not established.

This transient example imports the delivered result and proves only its classical contrapositive; it adds no named declaration:

```lean
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open D5.S3.Quantum.BlockNorm.EssentiallyHermitian
example {n : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ¬ EssentiallyHermitian X) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ,
      (Matrix.fromBlocks A X Xᴴ B).PosSemidef ∧
      ‖A + B‖ < ‖Matrix.fromBlocks A X Xᴴ B‖ := by
  by_contra h
  apply hX
  apply result n hn X
  intro A B hp
  by_contra hnorm
  exact h ⟨A,B,hp,lt_of_not_ge hnorm⟩
```

## ASSUMED-UNVERIFIED

The bounded literature check does not prove exhaustive worldwide novelty or priority. Source-proved converse and Frobenius results are literature evidence; their Lean formalizations are outside this delivery. No model-family diversity is claimed.
