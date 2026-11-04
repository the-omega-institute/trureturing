---
slug: han-pedon-metallic-hankel-quasipolynomial
bibkey: han2026shiftedmetallic
doi: 10.48550/arXiv.2610.36132
url: https://arxiv.org/abs/2610.36132v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MetallicHankel/MetallicHankelResiduePolynomials.result
---

# Han–Pedon Conjecture C: all higher-shift metallic Hankel residue polynomials

## Problem

Guo-Niu Han and Emmanuel Pedon, *Hankel determinants for the (n+2)-shifted q-metallic numbers*, arXiv:2610.36132v1, introduction, Conjecture C. The defining quadratic is equation (2.13); equations (1.4) and (1.5) define the shifted determinant and its empty value. The original preregistration is [issue #23253](https://github.com/the-omega-institute/trureturing/issues/23253). The follow-up is distinct from arXiv:2502.05993v2 and its Conjecture E on bounded-shift periodicity and higher-shift unboundedness.

For every natural $n\ge1$, there exists $\Phi\in\mathbb Z[[q]]$ with constant coefficient one satisfying

$$q\Phi^2+\bigl((1+q^n)(1-q)-q[n]_q\bigr)\Phi=1,
\qquad [n]_q=\sum_{i=0}^{n-1}q^i.$$

For every series satisfying these conditions and every natural shift $\ell\ge n+3$, define

$$\Delta_j^{(\ell)}=\det\bigl([q^{\ell+a+b}]\Phi\bigr)_{0\le a,b<j},
\qquad \Delta_0^{(\ell)}=1,$$

and put $\rho=2n(n+1)$ for even $n$ and $\rho=4n(n+1)$ for odd $n$. There is a family $Q_r\in\mathbb Q[X]$, indexed by every $0\le r<\rho$, such that

$$\Delta_{r+m\rho}^{(\ell)}=Q_r(m)\quad\text{for every }m\in\mathbb N,$$

and $Q_r(z)\in\mathbb Z$ for every $z\in\mathbb Z$. Here $\mathbb N$ includes zero. There is no eventual threshold, excluded initial residue, target or neighboring-minor invertibility condition, degree bound, or assertion that $\rho$ is minimal. Existence is a conclusion, and every satisfying metallic series is covered.

### Formal correspondence

`Trureturing.OpenProblems.HanPedonShiftedQMetallicHankel.claim`, defined in `MetallicHankelQuasipolynomialDefs`, retains these clauses literally: `1 ≤ n`, an existential integral metallic series, universal quantification over every satisfying series, `n + 3 ≤ ℓ`, the displayed parity-dependent period, a family indexed by `Fin ρ`, an integer witness for each integer input, and equality at every natural `m`. `IsMetallic` and `shiftedHankel` are the original definitions in `MetallicHankelDefs`; the latter is the determinant on `Fin j`, so size zero is included.

The settling declaration is `D5.S3.Combinatorics.MetallicHankel.MetallicHankelResiduePolynomials.result : Trureturing.OpenProblems.HanPedonShiftedQMetallicHankel.claim`. Its Scribe carries this dossier's `OpenProblemResolutionClaim` with resolution `Proved`.

## Motivation

The earlier higher-shift unboundedness theorem does not describe the complete sequence in each residue. Conjecture C supplies that structure from the first term while retaining all metallic parameters and higher shifts.

## Gap

The original owner #23253 records a partial literature screen with no settlement found in its searched scope. Citation enumeration and capped broad searches were incomplete; this is not an exhaustive novelty claim. The exact C statement is distinct from the older Conjecture E results.

## Route

`normal_family` supplies existence, uniqueness and one identical family of supported continuants at determinant-one sizes $N=K\rho$. The ordinary and reversed block theorems act on those same continuants, including the exceptional $n=1$ cycle. Their endpoint-jet theorem constructs rational coefficient polynomials of every order, with the high endpoint valid at the actual depth $h<2K\rho$.

For $a=\ell-(n+1)$ and each residue $r$, set $K_0=a+1$, $t=K_0\rho-r$ and $u=t-a$. At every $m\ge0$, the normal size $(K_0+m)\rho$ is $r+m\rho+t$. The exact complementary-minor theorem reduces the target determinant to a boundary determinant of fixed size $t$. Its ordered indices, sign, common-degree reversals and zero-support guards retain the original moments. Only the enclosing determinant is required to be a unit. Every boundary depth is below $2t\le2(K_0+m)\rho$, including $r=m=0$.

Replace the boundary coefficients by the four endpoint polynomials and evaluate the fixed determinant. Translation by $K_0+X$ and the constant sign $(-1)^{ar}$ give $Q_r$. The all-natural determinant values are integers. Backward polynomial propagation in the additive subgroup $\mathbb Z\subset\mathbb Q$ extends this to every negative integer as well. Uniqueness transfers the construction to every satisfying metallic series.

## Falsifier

A failure of the stated claim would require a metallic parameter without the asserted existence, or a satisfying series and qualifying shift for which no family has both the all-natural determinant equalities and integer values at every integer. A failed proof route, a nonminimal period or an unproved degree bound does not refute this claim.

## Evidence

This is a Tier 1 externally named conjecture under the original owner #23253, with `admission_basis: open-problem-resolution` for the exact settling result. Its proof includes the fixed-boundary polynomial construction and backward integer-value propagation. Supporting content supplies the normal inverse, exact arbitrary-state block actions, arbitrary endpoint jets and ordered complementary-minor bridge. All selected mathematical modules declare `utility: none`: the delivered conclusions quantify over unbounded inputs rather than asserting a positive finite computed instance. Definitional and normalization helpers are consumed in these proof paths and are not separate novelty claims.

The matrix duality consumer uses the original `Matrix.enumEquiv` and `Matrix.det_submatrix_inl_eq_mul` declarations after removal of `private`; their proofs are unchanged.

## Triage

- Proved: the complete C claim, including metallic existence, every satisfying series, every shift ell>=n+3, every residue for the stated parity-dependent period, all natural m including zero, and integer values at all integers. The mechanism is one fixed boundary determinant per shift and residue, evaluated on the same-family endpoint polynomials and extended to negative integer inputs by backward propagation.
- Proved: this supplies a residue-class polynomial description in addition to the previously established higher-shift unboundedness. It asserts an allowed period and polynomial existence without a minimal-period or degree claim.
- Open: minimal quasiperiods, sharp polynomial degrees and explicit closed forms for the individual residue polynomials. These are separate mathematical questions and are not conclusions of the settling theorem.

## ASSUMED-UNVERIFIED

The source-selection/current-binding audit remains unfinished as disclosed in [issue #23562, comment 6608152759](https://github.com/the-omega-institute/trureturing/issues/23562#issuecomment-6608152759). In particular, the settling result's Reg registration has `sourceSelection := none`; compiled family and registration terms do not supply that missing source binding. The EndpointSpectral registration has no retained mirror or verified current binding; its bounded canonical build timed out while waiting for the shared Lean lock, without establishing a template impossibility. None of these audit gaps supplies a `declared_validated` claim or refutes the mathematical result.

The literature screen remains partial as described under Gap. The current owner body identifies #23253; its earlier body revisions and the full historical filing chronology have not been verified. No exhaustive novelty or chronology claim is made. No theorem in the cited source was identified as conditional on C in the supplied source assessment.
