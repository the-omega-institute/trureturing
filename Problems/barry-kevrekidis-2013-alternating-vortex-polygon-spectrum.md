---
slug: barry-kevrekidis-2013-alternating-vortex-polygon-spectrum
bibkey: barrykevrekidis2013vortex
doi: 10.1088/1751-8113/46/44/445001
url: https://arxiv.org/abs/1306.1545v2
triage: theorem
motivation_gids:
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.result
---

# The alternating vortex polygon has exactly $N/2-2$ distinct real eigenvalue pairs

## Problem

A. M. Barry and P. G. Kevrekidis, *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*, J. Phys. A: Math. Theor. 46, 445001 (2013), arXiv:1306.1545v2, Section 4.1, Conjecture 4.4 (`BEC_VFP6.tex`, lines 630–631):

> For $N\geq 6$, the $N$-gon has $\frac{N}{2}-2$ distinct pairs of real eigenvalues.

The setting is the precessing point-vortex system of Section 2, Eqs. (1)–(2), with $b=2$:

$$\dot x_j=-S_j\Omega y_j-\sum_{k\ne j}S_k\frac{y_j-y_k}{(x_j-x_k)^2+(y_j-y_k)^2},\qquad
\dot y_j=S_j\Omega x_j+\sum_{k\ne j}S_k\frac{x_j-x_k}{(x_j-x_k)^2+(y_j-y_k)^2}.$$

Section 4.1 specifies the charges:

> We will assume hereafter that the vortices are of alternating charge, namely $S_j=(-1)^{j+1}$, $j=1,2, \dots,N$.

This is `BEC_VFP6.tex`, lines 506–507. The polygon has vertices $z_j=e^{2\pi i j/N}$, $1\le j\le N$ (line 515); the even polygon is an equilibrium at $\Omega=1/2$ (Lemma 4.2, lines 524–532). Thus the conjecture concerns even $N\ge6$ in this equilibrium family.

Issue [#26188](https://github.com/the-omega-institute/trureturing/issues/26188) fixes the reading. For every natural $m\ge3$, let $J_{2m}$ be the real Cartesian Jacobian of this field at the unit regular $2m$-gon. Every real root of its characteristic polynomial is accompanied by its negative, and the set of nonzero real roots has exactly $2(m-2)$ elements. Pairs count distinct nonzero values, without algebraic multiplicity. This statement is proved.

The source and encoding are described in [the literature note](../Library/FluidDynamics/barrykevrekidis2013vortex.md).

## Motivation

The conjecture specifies how many distinct real eigenvalue pairs occur as the alternating vortex polygon grows. It strengthens the existence of a real instability in Lemma 4.3 to an exact count for every even $N\ge6$. Distinct eigenvalue values and dimensions of unstable eigenspaces are different questions; this settlement concerns the former. The source also compares its particle model with vortex polygons in a Bose–Einstein condensate, but an ODE spectrum does not by itself establish a PDE spectrum.

## Gap

The bounded literature check reported in #26188 covers the five citing works returned by Semantic Scholar and two additional papers concerning other boundary or PDE models. The search seat reported no all-even-$N$ spectrum or proof of the required distinctness in that scope; the issue also records a repository search with no prior settlement of this conjecture. The downloaded arXiv v2 TeX retains Conjecture 4.4 at the locator above.

`not-found-in-searched-scope`.

## Route

Write $N=2m$, with $m$ natural and $m\ge3$. The following lemma names, except those explicitly qualified by `InverseChordCirculant`, belong to `AlternatingPolygonSpectrum`; its proof helpers are private.

1. **Differentiate the source field.** For every natural $N$ and distinct $j,k\in\mathrm{Fin}\,N$, `chord_sq_ne_zero` proves that the squared distance between `polygon N` vertices is nonzero; `chord_sq` identifies it with $4\sin^2(\pi(j-k)/N)$. For every natural $N$ and coordinate indices $p,q\in\mathrm{Fin}\,N\oplus\mathrm{Fin}\,N$, `entry_formula` computes `jacobian N p q` by differentiating `field N` along the coordinate direction $q$. For natural $m\ge3$, `equilibrium` proves `field (2*m) (polygon (2*m)) = 0`.

2. **Obtain the block matrix.** Put $W=\texttt{InverseChordCirculant.weights}\ m$, so $W_{jj}=0$ and $W_{jk}=1/(4\sin^2(\pi(j-k)/(2m)))$ for $j\ne k$. Put $D=\operatorname{diag}((-1)^j)$, $a=((2m)^2-1)/12-m^2/2$, $B=(aI-W)D$ and $C=((a+1)I-W)D$, the definitions `blockB m` and `blockC m`. For every natural $N$, `rotation_mul_transpose` proves $R_NR_N^{\mathsf T}=I$ for the radial and tangential coordinate matrix `rotation N`. For natural $m\ge3$, `rotated_jacobian` proves
   $R_{2m}^{\mathsf T}J_{2m}R_{2m}=\begin{pmatrix}0&B\\C&0\end{pmatrix}$.

3. **Use the Fourier product spectrum.** For natural $m$ with $\mathrm{NeZero}(2m)$, $m\ge3$, and every real $y$, `InverseChordCirculant.product_spectrum` proves
   $\det(yI-CB)=\prod_{k\in\mathbb Z/(2m)}(y-\gamma_m(k))$,
   where `gamma m k` is $(m-r)^2(r^2-2)/4$ with $r=\min(k.\mathrm{val},2m-k.\mathrm{val})$. `InverseChordCirculant.chordWeight_dft`, for every natural $N$ with $\mathrm{NeZero}\,N$ and every $k\in\mathbb Z/N$, computes the inverse-squared-chord Fourier coefficient as $(N^2-1)/12-k.\mathrm{val}(N-k.\mathrm{val})/2$. Alternating signs shift Fourier modes by $m$, as `InverseChordCirculant.alternating_chord_dft` proves for natural $m$ with $\mathrm{NeZero}(2m)$ and every $k\in\mathbb Z/(2m)$.

4. **Identify the nonzero real roots.** For natural $m\ge3$ and real $x\ne0$, `nonzero_root_iff` proves that $x$ is a characteristic root of $J_{2m}$ exactly when $\det(x^2I-CB)=0$. Under precisely the same hypotheses, `root_iff_mode` proves the equivalence with existence of a natural $r$ satisfying $2\le r<m$ and $x^2=(m-r)^2(r^2-2)/4$. For natural $m,r$ with $2\le r<m$, `positiveRoot_pos` proves positivity of $p_m(r)=(m-r)\sqrt{r^2-2}/2$; for natural $m,r$ with $2\le r$, `positiveRoot_sq` computes its square. Hence the nonzero real roots are exactly $\pm p_m(r)$ for $2\le r<m$.

5. **Separate the candidate values and count them.** For natural $m,k,l$ with $2\le k<l<m$, `distinctness_certificate` proves $(m-k)^2(k^2-2)\ne(m-l)^2(l^2-2)$. With $s=k+l$ and $Q(t)=st^2-2(k^2+kl+l^2-2)t+s(k^2+l^2-2)$, their difference is $(k-l)Q(m)$. The proof gives $Q(l)<0$ and $Q(s-1)<0$, and a quadratic interpolation identity gives $Q(m)<0$ when $l<m\le s-1$. When $m\ge s$, writing $h=m-s\ge0$ gives $Q(m)=2s+(2kl+4)h+sh^2>0$. Integrality places every admissible $m$ in one of these ranges. For natural $m\ge3$, `real_root_count` identifies the nonzero-root set with the disjoint positive and negative images of the finite interval $2\le r<m$, proves its cardinality $2(m-2)$, and proves sign symmetry of all real roots, including zero. `result : claim` applies this lemma for every natural $m\ge3$.

## Falsifier

A counterexample to the registered statement would be a natural $m\ge3$ for which the actual Cartesian Jacobian has a real characteristic root without its negative, or its set of nonzero real characteristic roots has cardinality other than $2(m-2)$. A proof about a postulated block matrix alone would not identify that Jacobian.

The encoding closes that identification: `field` is the Cartesian field with $b=2$ and $\Omega=1/2$; `polygon` uses angle $2\pi(j.\mathrm{val}+1)/N$; and `charge` uses $(-1)^{j.\mathrm{val}+2}$, matching the source's one-based labels. `jacobian` is defined by actual directional derivatives, and `entry_formula` computes them using nonzero distances between distinct polygon vertices. The finite-set identification in `real_root_count`, for natural $m\ge3$, supplies finiteness as well as the count. Zero roots, algebraic multiplicities, and eigenvectors are excluded from the counted set.

## Evidence

The canonical source is `D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum.lean.json`.

Declaration statements:

- `result`: `sha256:f074972b96df331b7434476cc267ddfab4a0f1e12927ddfd86a0318e188c9d80`;
- `claim`: `sha256:bf6ed926635ff41397b65b5f25df01a9af5581c539d0fd891be330f8e7f05816`.

## Triage

Tier 1 conjecture of a 2013 paper, preregistered in issue #26188 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $m\ge3$, every real characteristic root $x$ of `jacobian (2*m)` has $-x$ as a characteristic root, and the set of its nonzero real characteristic roots has exactly $2(m-2)$ elements.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and the integral boundary.* The separation argument uses the integer lattice, rather than monotonicity of a continuously parametrized root formula. Its extension to arbitrary real parameters is false: for $k=2$, $l=3$ and $f_m(r)=(m-r)^2(r^2-2)$, one has $f_m(2)-f_m(3)=-5m^2+34m-55$. This vanishes at $m=(17+\sqrt{14})/5$, which lies strictly between $4$ and $5$. Thus continuous interpolation can merge these two candidate values even though the natural parameters in `distinctness_certificate`, $2\le k<l<m$, separate them. This is an observation about interpolation of the formula, not a polygon with a noninteger number of vertices.
- *Radial scaling.* Keep $b=2$, choose a radius $R>0$, and set $\Omega=1/(2R^2)$. The interaction term is homogeneous of degree $-1$, while the precession term is linear, so the field at $Ru$ is $R^{-1}$ times the normalized field at $u$. Differentiating this identity at the unit polygon gives $J_{\Omega,R}=R^{-2}J_{1/2,1}$. Its characteristic roots are therefore multiplied by the positive factor $R^{-2}=2\Omega$, preserving the distinct-pair count for natural $m\ge3$. The parameter-dependent field and this scaling identity are not part of `result`.
- *ODE instability and the source's dependent discussion.* For $m\ge3$, the proved count is positive; sign symmetry therefore supplies a positive real characteristic root $\alpha$. Singularity of $\alpha I-J_{2m}$ gives a nonzero real vector $v$ with $J_{2m}v=\alpha v$, and $e^{\alpha t}v$ is a growing solution of the linearized ODE. This recovers the particle-model instability of Lemma 4.3 and gives the exact number of distinct real pairs asked for in Conjecture 4.4. The PDE explanation that “each additional destabilization adds a real eigenvalue pair to the linear spectrum” (`BEC_VFP6.tex`, lines 638–639) still needs a separate relation between the particle and PDE linearizations; neither that relation nor the PDE bifurcations are established here.
- *Neighbouring questions.* The all-even-$N\ge6$ count is exact, rather than an upper or lower estimate. The theorem does not determine algebraic multiplicities, eigenvectors, Krein signatures, or nonlinear stability. It does not settle the source's collinear questions in Section 4.2, other charge patterns, odd polygons, or the $N=2,4$ cases outside its quantifiers.

## ASSUMED-UNVERIFIED

The bounded literature check in #26188 does not establish exhaustive worldwide novelty or priority. The five citing works, the two additional papers, completeness of the citation listing, and the reported latest-version status were not independently verified; the source text actually checked is arXiv:1306.1545v2. The orchestrator's finite-difference reading and the search seat's symbolic and cyclotomic readings in #26188 were not independently reproduced. The exact-integer computation above is a finite check and supplies no inference beyond its stated range.

The interpolation, scaling, dynamical interpretation and consequences discussed under “Argued, not formalized” are not additional formal conclusions of `result`. The full complex spectrum, algebraic multiplicities, eigenvectors, Krein signatures, nonlinear stability, the Gross–Pitaevskii PDE spectrum, and transfer between the ODE and PDE models remain outside this settlement.
