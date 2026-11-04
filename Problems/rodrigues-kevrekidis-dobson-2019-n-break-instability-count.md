---
slug: rodrigues-kevrekidis-dobson-2019-n-break-instability-count
bibkey: rodrigueskevrekidisdobson2019nbreak
doi: 10.1103/PhysRevE.99.022201
url: https://arxiv.org/abs/1802.03477v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.result
---

# The instability count of a clamped Lennard–Jones chain

## Problem

A. S. Rodrigues, P. G. Kevrekidis and M. Dobson, *N-break states in a chain of nonlinear oscillators*, Phys. Rev. E 99, 022201 (2019), arXiv:1802.03477v2, state in the abstract:

> Each of these higher ``excited state'' solutions possesses an additional unstable pair of eigenvalues. We thus conjecture that $k$ break solutions will possess at least $k-1$ (and at most $k$) pairs of unstable eigenvalues.

This quotation is from `oscillatorsNN_resubmit.tex`, lines 55–59, in the v2 source, whose MD5 is `f0e3a2d64045c090b53b217d75e86a05`. The model and terminology are documented in [the literature note](../Library/StatisticalMechanics/rodrigueskevrekidisdobson2019nbreak.md).

The module uses $m$ free particles, displacements $u_0,\ldots,u_{m+1}$, and zero-based bond indices $j=0,\ldots,m$. Its definitions are

$\phi(r)=r^{-12}-2r^{-6}$, $r_i=(13/7)^{1/6}$, and $r_j=d+u_{j+1}-u_j$.

The force at free particle $n+1$, indexed by $n=0,\ldots,m-1$, is $F_n=\phi'(r_{n+1})-\phi'(r_n)$. With $c_j=\phi''(r_j)$, the defined matrix $J$ has entries $J_{nn}=-c_n-c_{n+1}$, $J_{n,n+1}=J_{n+1,n}=c_{n+1}$, and zero elsewhere.

Issue [#23865](https://github.com/the-omega-institute/trureturing/issues/23865) fixes the reading: for every $m\ge1$, $d>0$, and displacement vector with $u_0=u_{m+1}=0$, $F_n=0$ at every free particle, and all $r_j>0$, if exactly $k\ge1$ bonds satisfy $r_j>r_i$, then, for every Hermitian witness $h$ for $J$, the number $U=\#\{i\in\mathrm{Fin}\,m:0<h.\mathrm{eigenvalues}(i)\}$ satisfies $k-1\le U\le k$. The eigenvalues are counted with multiplicity. This is proved as `result : claim`.

## Motivation

The conjecture turns a count of broken bonds into a count of unstable spectral directions, independently of chain size and break placement. Rodrigues, Kevrekidis and Dobson (2019), arXiv:1802.03477v2, motivate it with branches containing two through five breaks in the abstract and §IV.A. The count separates the possibility of a single-break state with no positive Jacobian eigenvalue from the unavoidable positive eigenvalues when there are at least two breaks; the dynamical interpretation is explained below.

## Gap

The bounded literature check recorded in #23865 reports:

- the arXiv v2 source retains the conjecture;
- Crossref lists one citing work, Theodorou, J. Chem. Phys. 161, 184905 (2024), concerning Morse-bond chain rupture rates, and the reported abstract reading does not address this eigenvalue count;
- repository issue searches for `1802.03477`, `Kevrekidis` and `N-break` found no prior work on this conjecture.

`not-found-in-searched-scope`.

## Route

1. **Curvature signs.** For every real $r>0$, `curvature_formula` gives $\phi''(r)=12(13-7r^6)/r^{14}$, and `inflection_iff` gives $r_i<r$ precisely when $13<7r^6$. With the same positivity hypothesis, `curvature_sign` gives $\phi''(r)<0$ precisely when $r_i<r$.
2. **Factorization.** For every natural $m$, real $d$, and $u:\mathrm{Fin}(m+2)\to\mathbb R$, without endpoint or equilibrium assumptions, `jacobian_factorization` constructs $B\in\mathbb R^{(m+1)\times m}$ with $B_{jn}=\mathbf1_{j=n}-\mathbf1_{j=n+1}$ and $c_j=\phi''(r_j)$, and gives $J=-B^{\mathsf T}\operatorname{diag}(c)B$. For any real matrix $B$ with precisely these entries, `bond_difference_injective` proves injectivity of $x\mapsto Bx$, and `bond_difference_range` gives range dimension $m$, hence codimension one in $\mathbb R^{m+1}$.
3. **Quadratic form.** For arbitrary real matrices $A\in\mathbb R^{m\times m}$ and $B\in\mathbb R^{(m+1)\times m}$ and real coefficients $c$, assuming $A=-B^{\mathsf T}\operatorname{diag}(c)B$, `factorization_form` gives $x^{\mathsf T}Ax=-\sum_j c_j(Bx)_j^2$ for every $x\in\mathbb R^m$.
4. **Both inertia bounds.** The hypotheses of `inertia_lower_bound` and `inertia_upper_bound` are $m\ge1$, $d>0$, $u:\mathrm{Fin}(m+2)\to\mathbb R$, all $r_j>0$, a natural $k\ge1$, exactly $k$ bonds with $r_j>r_i$, and a Hermitian witness $h$ for $J$. For the lower bound, let $E$ be the coordinate subspace supported on those broken bonds. It has dimension $k$. Injectivity identifies $B^{-1}E$ with $\operatorname{range}(B)\cap E$, whose dimension is at least $k-1$. The form of $J$ is strictly positive on every nonzero vector in $B^{-1}E$. For a Hermitian matrix and a subspace with this positivity property, `RHLinalg.finrank_le_posIndex_of_posDefOn` bounds the subspace dimension by the positive eigenvalue count. For the upper bound, `RHLinalg.posIndex_eq_max_finrank_posDefOn`, assuming the matrix is Hermitian, supplies a positive-definite subspace of dimension $U$. Projection of its $B$-image to the broken coordinates is injective: a vector with those coordinates zero has $-\sum_j c_j(Bx)_j^2\le0$, so positivity forces it to vanish. Its dimension is therefore at most $k$.

These private bound lemmas have no endpoint or steady-state hypotheses. `result` applies both under all the hypotheses retained in `claim`.

## Falsifier

The proof would not answer the registered reading if the curvature sign, matrix sign, bond count or multiplicity convention differed from the source. The module uses the source's potential, positive lengths, and strict broken-bond threshold. A bond at $r_i$ is not counted as broken; its zero curvature does not invalidate either bound. The counted eigenvalues are strictly positive eigenvalues of the force Jacobian, rather than of the energy Hessian, and their indices run through all $m$ eigenvalues with multiplicity.

The type of `claim` explicitly takes a Hermitian witness. The identification of the defined matrix with the derivative of the force, its symmetry, and the conversion to unstable pairs in the second-order evolution are explained arguments below, rather than additional conclusions of `result`. Existence of equilibria with a specified number of breaks is outside the claim.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.lean.json`.

Declaration statements:

- `result`: `sha256:2a102102770f526a416a29d20555da51580fef6e927e75d47b6cc46769a52b93`;
- `claim`: `sha256:fc4ca678b7ad0a5f3f80ef0b17dcf63770d559b16b2958a9e815bdf956b70e52`.

## Triage

Tier 1 conjecture stated in the abstract of a 2019 paper, preregistered in issue #23865 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $m\ge1$, real $d>0$, and $u:\mathrm{Fin}(m+2)\to\mathbb R$ with zero endpoint displacements, zero force at every free particle, and all bond lengths positive, if exactly $k\ge1$ bonds are strictly longer than $r_i$, then for every Hermitian witness $h$ for the defined Jacobian, its positive eigenvalue count, with multiplicity, lies between $k-1$ and $k$.

**Computed, not formalized:** none.

**Argued, not formalized**.

- *Spectral interpretation.* On positive bond lengths, differentiating $F_n=\phi'(r_{n+1})-\phi'(r_n)$ with respect to the free displacements gives exactly the displayed tridiagonal entries; the shared off-diagonal entries also show symmetry. At an equilibrium, substituting a perturbation $e^{\lambda t}v$ into $\ddot u=F(u)$ gives $Jv=\lambda^2v$, as in Rodrigues, Kevrekidis and Dobson (2019), arXiv:1802.03477v2, §II, lines 204–250. Diagonalizing the real symmetric $J$ reduces each mode to $\ddot a=\mu a$: each $\mu>0$ contributes the real pair $\lambda=\pm\sqrt\mu$, with multiplicity. Thus $k\ge2$ entails an unstable pair, while $k=1$ allows either zero or one positive eigenvalue. Zero eigenvalues are not counted; this count does not certify nonlinear stability.
- *Mechanism and extension.* The codimension-one constraint can remove at most one negative direction from the bond-curvature form. For the matrix $B$ specified in `jacobian_factorization`, summing its rows against any vector telescopes to zero; its rank $m$ therefore identifies its image with $W=\{w:\sum_jw_j=0\}$. For any real diagonal coefficients with exactly $k\ge1$ negative entries, their coordinate subspace intersects $W$ in dimension at least $k-1$, and projection of any negative-definite subspace of $W$ to the negative coordinates is injective. This gives the same two bounds for any twice differentiable nearest-neighbour potential with exactly $k$ negative bond curvatures and all others nonnegative. That general-potential statement is not formalized in this module. For the Lennard–Jones potential, the compiled `inertia_lower_bound` and `inertia_upper_bound` already omit equilibrium and endpoint conditions under their full hypotheses listed in Route; `result` retains them.
- *Sharpness of the structural bounds.* For arbitrary curvature coefficients, the lower endpoint is forced when all $m+1$ coefficients are negative: the diagonal form is negative on every nonzero vector of $W$, so $U=m=k-1$. For $1\le k\le m$, choose the $k$ negative coefficients equal to $-1$ and all other coefficients equal to $\varepsilon$ with $0<\varepsilon<1/k$. Given arbitrary broken coordinates $a_1,\ldots,a_k$, put $-\sum_i a_i$ on one unbroken coordinate and zero on the others. These vectors form a $k$-dimensional subspace of $W$, with form $-\sum_i a_i^2+\varepsilon(\sum_i a_i)^2\le(-1+\varepsilon k)\sum_i a_i^2<0$ for nonzero $a$. Hence $U=k$. This establishes sharpness for unrestricted curvature data; attainment of both endpoints by Lennard–Jones equilibria for each feasible $(m,k)$ remains open here.
- *Effect on the paper and neighbouring questions.* The baseline count of at least $k-1$ unstable pairs underlying §IV.A, lines 493–510, and §V, lines 881–898, follows for the equilibria covered by `claim` through the spectral interpretation above. The bound leaves at most one additional unstable pair. It does not select which branch has that pair, locate its transition using energy monotonicity, establish existence of the branches, identify their eigendirections, or justify the subsequent nonlinear break-elimination dynamics. The next-nearest-neighbour and higher-dimensional questions in §V, lines 900–915, remain open here: their bond maps and constraints require separate analysis.

## ASSUMED-UNVERIFIED

The bounded literature check in #23865 does not establish exhaustive worldwide novelty or priority. The v2 TeX and its quoted conjecture are verified source readings; the reported Theodorou abstract, Crossref citation count and repository-search results have not been independently reproduced for this dossier. The arXiv v1 source and the cited work have not been independently checked. The source's numerical continuation and evolution computations have not been reproduced.

Beyond the named Lean lemmas, the spectral interpretation, zero-sum range identification, general-potential extension, sharpness construction and consequences for the source's remaining statements are not formalized in this module. Endpoint attainment for every feasible Lennard–Jones equilibrium count, the branch-selection criterion, prescribed-break existence, nonlinear dynamics and the source's proposed extensions remain outside this settlement.
