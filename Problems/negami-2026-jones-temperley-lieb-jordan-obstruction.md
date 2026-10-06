---
slug: negami-2026-jones-temperley-lieb-jordan-obstruction
bibkey: negami2026middle
doi: 10.48550/arXiv.2610.00293
url: https://arxiv.org/abs/2610.00293v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.result
---

# The Jordan obstruction for the Jones–Temperley–Lieb endpoint-sector seeds

## Problem

H. Negami, *Quantum gates from the middle convolution of twisted Burau
representations*, arXiv:2610.00293v1, builds braid representations for quantum
gates by the Katz–Long–Moody construction: a seed representation of
$F_n\rtimes B_n\cong B_{1,n}$ on $V$ gives operators $S_i$ on $V^{\oplus n}$,
$S_i=s_i^{\oplus n}\,\mathrm{diag}(I,R_i,I)$ with
$R_i=\begin{pmatrix}0&g_i\\I&I-g_{i+1}\end{pmatrix}$, and a quotient by
$K+L_\lambda$, $K=\bigoplus_j\mathrm{Ker}(g_j-I)$. Remark 6.7(b) tests seeds
from the endpoint sectors of the Jones–Temperley–Lieb path representations
($\rho(\sigma_i)=\alpha_\ell I+\alpha_\ell^{-1}E_i$, $\alpha_\ell=ie^{-\pi
i/(2\ell)}$) for $n=3$, $\ell\in\{4,5,6,7,8,10,12,16\}$ and $n=4$,
$\ell\in\{5,7\}$: in sectors with $K=0$ finite-precision rank tests suggest
non-trivial Jordan blocks of the ambient $S_i$, which "by themselves …
establish neither non-semisimplicity nor unboundedness". Problem 6.8 ends:
"Also prove the Jordan obstruction for the Jones--Temperley--Lieb
endpoint-sector seeds". The verbatim statements are in
[the literature note](../Library/QuantumStates/negami2026middle.md).

Issue [#13581](https://github.com/the-omega-institute/trureturing/issues/13581)
fixes the reading: the obstruction is a Jordan chain of length two of $S_1$ (all
$S_i$ are conjugate to it in the braid group) in a sector with $K=0$, with the
standard path-model operators $E_i$ (which the source names without writing
their entries), and it is proved for every $n\ge3$, $\ell\ge4$ and every
endpoint sector of dimension at least two.

## Motivation

A non-semisimple braid generator rules out any invariant positive-definite
Hermitian form, so these seeds cannot produce unitarizable KLM gate
representations; the paper's large sampled word norms are the numerical shadow
of this. `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.result`
proves the obstruction exactly and uniformly.

## Gap

Issue #13581 records the literature check before any Lean: the paper has a
single version (2026-09-25); its summary table says "An exact obstruction
remains open"; the related KLM papers 2609.11793 and 2608.01727 treat the Hecke
scalar family and general triangularization, not path-model endpoint sectors;
the repository had only the Temperley–Lieb projection laws of the path model
(`WeightedLegalPathTemperleyLieb`). Zenodo title searches ("Temperley-Lieb"
"Long-Moody", "Long-Moody" Jordan, Negami) and a web search for the obstruction
(2026-10-06) returned no settlement. `not-found-in-searched-scope`.

## Route

Let $a=\alpha_\ell$, $\delta=2\cos(\pi/\ell)=-(a^2+a^{-2})$, $b=-a^{-3}$.

1. **Temperley–Lieb relation.** With $\mu_c=\sin(c\pi/\ell)$,
   $\sum_{d\sim c}\mu_d=\delta\mu_c$ (the missing boundary neighbours would
   contribute $\sin0=\sin\pi=0$), so the frozen theorem gives
   $E_j^2=\delta E_j$, hence $(\rho_j-a)(\rho_j+a^{-3})=0$.
2. **$K=0$.** Every $g_j$ is conjugate to $\rho_0^2$, so
   $(g_j-a^2)(g_j-a^{-6})=0$; for $\ell\ge4$ neither $a^2$ nor $a^{-6}$ equals
   1, so $g_j$ has no fixed vector.
3. **A local block.** A sector with two paths contains a path beginning
   $1,2,1$ (`loop_path`) and its partner with vertex 2 replaced by 3; on their
   span, in a basis $f_0,f_1$, $\rho_0=\begin{pmatrix}-a^{-3}&a\\0&a\end{pmatrix}$
   and $\rho_1=\begin{pmatrix}a&0\\a^{-3}&-a^{-3}\end{pmatrix}$
   (`local_vectors`).
4. **Jordan chain.** On slots 1 and 2 of that span, $S_1=\begin{pmatrix}0&UG\\U&U(I-H)\end{pmatrix}$
   with $U=\rho_1$, $G=\rho_0^2$, $H=UGU^{-1}$; an explicit Laurent-polynomial
   vector $w$ gives $(S_1-b)^2w=0$ and $(S_1-b)w\ne0$ because $a^6\ne1$
   (`sector_jordan`).

## Falsifier

The proof would fail if $a^2$ or $a^{-6}$ were 1 (it is at $\ell=3$, where
$3\pi/\ell=\pi$), or if a sector of dimension at least two contained no path
beginning $1,2,1$.

## Evidence

The canonical source is
`D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.lean`. Its
public declarations are `adj`, `mu`, `delta`, `v1`, `Sector`, `E`, `alpha`,
`rho`, `s`, `seed`, `g`, `S1`, `b`, `claim` and `result`, with instances for
`DecidableRel (adj ℓ)`, `Fintype` and `DecidableEq` on the sectors. It imports
the frozen `D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb`
(`LegalPath`, `pathProjection`, `weighted_legal_path_temperley_lieb`) and the frozen
`D5/S3/QuantumBounds/ReferenceFrameTax` (`sine_reference_eigenvector`, the zero-boundary
sine eigenvector relation behind the Perron–Frobenius weights); the adjacency is
Mathlib's `SimpleGraph.pathGraph`, and the proof applies Mathlib's sine and cosine
positivity, `Real.sin_two_mul`, `Complex.exp_nat_mul` and the nonsingular-inverse lemmas.
It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`;
no `sorry`, `native_decide`, or new axiom. The module statement is
`sha256:7c54306aac355610e4a98f524609bd8b78367e684156ec02ef42326826b20363`, the `result`
statement `sha256:81d8490d2baa9fc1f1cb395e70d32a3e56207ba543060f724de8738bd0a22563` and the `claim` statement
`sha256:092bc5b9520961e1ac46c1856a375b050c33a631c6613c16fbf68525883bc8d4`. The Freeze event is
`sha256:940f0d828cb2930549906e443194a8633509c459d457791124cfece5e883f85b`; its
project-level prerequisites are `sha256:4596e4b3f62f1bf4c28dd053935ac6ed2f262f7926b61592d319479015e27798` and
`sha256:57be3e0134327e85e5920fac333ec9d9338b42abf2c25b0982e639a15929c2b8`, the frozen
`WeightedLegalPathTemperleyLieb` and `ReferenceFrameTax`. The event also records `v1.congr_simp` and `lmBlock.congr_simp`, congruence lemmas that
Lean realizes while `simp` elaborates, and `seed.eq_def`, the equation lemma Lean generates for
the recursive definition `seed`; none is an authored declaration.

Numerical check (60-digit arithmetic for the remark's seeds, double precision
for the wide scan): all 20 endpoint sectors of dimension at least two for the
remark's ten $(n,\ell)$ have $K=0$ and
$\dim\ker(S_1-b)^2>\dim\ker(S_1-b)$; a wide scan $n=3,\dots,7$,
$\ell=4,\dots,14$ (141 sectors) has no exception; the braid relations and
$E_i^2=\delta E_i$ hold to $10^{-60}$, and every other eigenvalue of $S_1$ in the
sampled sectors is semisimple.

## Triage

Tier 1 explicit problem of a 2026 paper, preregistered in issue #13581 before
any Lean. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | `loop_path` | open-problem-resolution |

The private theorems `loop_path`, `local_vectors`, `sector_jordan` and
`no_fixed_seed` are content; every other private theorem (`μ_pos`,
`perron_frobenius`, `δ_pos`, `E_square`, `α_data`, `E_triple`, `ρ_inverse`,
`seed_zero_polynomial`, `first_projection`, `block_action`) is bind-only and is
used on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). The
direct frozen dependency is `WeightedLegalPathTemperleyLieb`. Utility is `none`: the module proves a universal statement and
contains no finite enumeration, checker, numeric reduction or certified
instance. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\ge3$, $\ell\ge4$ and every endpoint sector
of dimension at least two, $K=0$ and $S_1$ has a Jordan chain of length two at
$-\alpha_\ell^{-3}$; in particular for all twenty sectors of Remark 6.7(b).

**Established inside the proof.** The whole obstruction lives on a
four-dimensional subspace spanned by two paths in slots 1 and 2, uniformly in
$n$, $\ell$ and the sector; its coupling is the factor $a^6-1$, so the chain is
a genuine non-diagonal block, not a coincidence of eigenvalues
(`local_vectors`, `sector_jordan`).

**Argued, not formalized.**

- Non-unitarizability and unboundedness: $S_1^kw=b^kw+kb^{k-1}v$ with
  $|b|=1$ and $v=(S_1-b)w\ne0$, so $\|S_1^kw\|\to\infty$ linearly and no
  positive-definite invariant Hermitian form exists; every $S_i$ is conjugate to
  $S_1$, so each braid generator is non-semisimple.
- The chain survives every KLM quotient with $\lambda\notin\{0,1\}$: the
  four-dimensional subspace has zero components in slots $3,\dots,n$, and the
  recurrence $z_j=g_{j+1}z_{j+1}$ describing $L_\lambda$ then forces slots 2 and
  1 to vanish, so it meets $K+L_\lambda=L_\lambda$ only in 0.

**Open.** The irreducibility locus and image-closure questions of Problem 6.8
are not addressed.

**Effect on the paper.** The table entry "An exact obstruction remains open"
is settled: the Jones–Temperley–Lieb endpoint-sector seeds give
non-semisimple, hence non-unitarizable, ambient Long–Moody representations in
every endpoint sector of dimension at least two, for every $n\ge3$, $\ell\ge4$; the paper's other results are unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
