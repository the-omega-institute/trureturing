---
bibkey: "teschl2009mathematical"
authors: "Gerald Teschl"
year: 2009
title: "Mathematical Methods in Quantum Mechanics: With Applications to Schrodinger Operators"
doi: null
url: "https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf"
claim: "The maximal L2 domain of a real multiplication operator is exactly the set of vectors whose pointwise product is in L2; the strong derivative domain of its unitary exponential equals that operator domain."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Maximal multiplication domains and physical modulation

Teschl, Graduate Studies in Mathematics 99, equation (2.21), printed pages 59-60, gives the maximal multiplication domain. Theorem 5.1(ii), printed pages 123-124, identifies the strong derivative domain of the unitary exponential with the domain of its self-adjoint generator. For the real multiplier A(x) = -(b dot x)/hbar, the convention U(t) = exp(-itA) gives positive modulation and derivative (i/hbar)(b dot x)f. These are known results, with this parameter correspondence.

## Physical modulation

For every natural number d, let E = EuclideanSpace Real (Fin d), with Lebesgue measure volume, and H = Lp Complex 2 volume. For every positive hbar, b in E, and f,v in H, let

```math
M_b(t)f=[x\mapsto e^{it\langle b,x\rangle/\hbar}f(x)].
```

The complete derivative graph is

```math
\operatorname{HasDerivAt}(t\mapsto M_b(t)f,v,0)
\iff
\exists h:\operatorname{MemLp}(x\mapsto\langle b,x\rangle f(x),2,\mathrm{volume}),\quad
v=\frac{i}{\hbar}\,h.\operatorname{toLp}(x\mapsto\langle b,x\rangle f(x)).
```

All directions, including zero, and all finite dimensions, including zero, are included. There is no finite-volume, global L1, Schwartz, or product-integrability premise on the derivative side.

Set a(x) = (b dot x)/hbar, z(x) = (b dot x)f(x), c = i/hbar, and k = cz. The quotient representative q_t(x) = t^(-1)(exp(it a(x))-1)f(x) converges pointwise to k. The phase derivative has norm |a(x)|, so |q_t(x)| is at most |k(x)| and |q_t(x)-k(x)| is at most 2|k(x)|. If z is square integrable, dominated convergence for the squared error proves convergence in the actual L2 norm and hence the derivative formula.

Conversely, a strong derivative v makes the quotient classes at t_n = 1/(n+1) converge to v in L2. Convergence in measure gives a strictly increasing subsequence converging almost everywhere. The countably many representative equalities hold together outside one null set. The scalar derivative forces the same subsequence to converge to k, so v=k almost everywhere. Thus k is in L2; since c is nonzero, z is in L2. The condition and toLp value are invariant under changes on null sets.

## Locator

https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf

Equation (2.21), printed pages 59-60; Theorem 5.1(ii), printed pages 123-124. The author-hosted file identifies the 2009 first edition, Graduate Studies in Mathematics volume 99. The online-use permission appears on its title page; this note cites the source and paraphrases the argument.
## Finite-measure Fourier mean squares

In the same retained first-edition PDF, Theorem 5.4, Section 5.2,
printed pp.126–127, equations (5.8)–(5.9), states Wiener's theorem for
every finite complex Borel measure $\mu$ on $\mathbb R$:

$$
\widehat\mu(t)=\int e^{-it\lambda}d\mu(\lambda),\qquad
\lim_{T\to\infty}\frac1T\int_0^T|\widehat\mu(t)|^2dt
=\sum_{\lambda\in\mathbb R}|\mu(\{\lambda\})|^2.
$$

The source uses the unnormalized angular transform, and the atomic sum
is finite. The inspected PDF SHA-256 is
`8dc8de0b58aa0a3fedfe594a345f9b5875322e5526ea581cb640a98d55b82818`;
its author-hosted title page dates the online text to 12 February 2009.
The source theorem is reused, without a new proof or priority claim.

For the project's real even finite signed prime-minus-continuum head,
the atoms are exactly $\pm\log n$, with masses $\Lambda(n)/\sqrt n$.
The negative continuous component has no atomic mass. The
[fixed-head scalar-budget application](../../docs/reports/theta-mixed-matrix/signed-low-row.md#fixed-head-band-expansion-has-a-classical-obstruction)
uses this same theorem to diagnose a frequency-envelope loss. It does
not assert growth of the actual weighted operator norm, an obstruction
to a growing arithmetic cutoff, or an RH/Robin conclusion. No compiled
project application is claimed.

## Schur criterion for the local frequency kernel

The same retained first-edition PDF gives Lemma 0.32, printed pp.28--29,
the Schur criterion for a measurable integral kernel dominated by
$K_1(x,y)K_2(x,y)$. For conjugate exponents, its separate row and column
norm bounds $C_1,C_2$ give operator norm at most $C_1C_2$. The
[local signed-frequency note](../../docs/reports/theta-mixed-matrix/local-signed-frequency.md)
uses the $L^2$ case with a Lorentzian factorization of the actual Fourier
kernel. It is a direct source-criterion application, with no new theorem
or compiled specialization claimed.

In Section 7.2, equation (7.47), printed p.172, the one-dimensional
free resolvent has kernel $e^{-\sqrt{-z}|x-y|}/(2\sqrt{-z})$.
For $z=-q^2$, $q>0$, this is the inverse angular transform of
$(\xi^2+q^2)^{-1}$ with its $1/(2\pi)$ factor. The local note uses
the resulting classical identity
$\int q^2/(q^2+\xi^2)e^{-i\xi t}d\xi=\pi q e^{-q|t|}$.
The source supplies the transform and generic kernel estimate; it
supplies no value or sign for the project's arithmetic form.

## Equality in Schur's test checks the unprojected theta-edge shortcut

The criterion above and the classical equality condition in
Cauchy–Schwarz are reused here. The application concerns the
[original minimal even theta form](../Weil/fukushima2011dirichlet.md)
and its [known critical family](../Weil/lagarias2004li.md), under those
notes' paper-level model and domain premises. It does not construct a
transfer or supply a new numerical lower bound or Lean certification.

### Keep the signed conductance and the actual core

Write $d\nu=2\Phi(x)\cosh(x/2)dx$, with $\nu(\mathbb R)=1$, and
$D(h)=\tfrac12\iint|h(y)-h(x)|^2J(dx,dy)$ on the actual minimal even
form domain $\mathcal F$. Every prime power remains in $J_p$, and
$J_\Gamma=\Phi(x)\Phi(y)\psi_\Gamma(|x-y|)dxdy$, where
$\psi_\Gamma(t)=e^{-t/2}/(1-e^{-2t})$ for $t>0$.

On $X=\{(x,y):x\ne y\}$ the half-slack
$q(h)=D(h)-\operatorname{Var}_\nu(h)/2$ has signed conductance
$J-(\nu\otimes\nu)/2$. Its positive and negative parts are

$$
\begin{aligned}
K_+={}&J_p+\Phi(x)\Phi(y)
 [\psi_\Gamma(|x-y|)-2\cosh(x/2)\cosh(y/2)]_+dxdy,\\
K_-={}&\Phi(x)\Phi(y)
 [2\cosh(x/2)\cosh(y/2)-\psi_\Gamma(|x-y|)]_+dxdy.
\end{aligned} \tag{S1}
$$

The prime graphs are singular to $dxdy$, so all remain in $K_+$.
Both edge measures are $\sigma$-finite. In particular, $K_+$ is not
finite: $\psi_\Gamma(t)\sim1/(2t)$ at zero gives logarithmically
infinite mass near the diagonal. The increment cancels this singularity
in the form, and Schur's test below uses $\sigma$-finite spaces.
Set $\mathscr E_\pm=L^2(K_\pm)$ and
$C_\pm h(x,y)=(h(y)-h(x))/\sqrt2$. Ordinary variance accounting gives

$$
q(h)=\|C_+h\|^2-\|C_-h\|^2,\qquad
\|C_+h\|^2\le D(h),\qquad
\|C_-h\|^2\le\tfrac12\operatorname{Var}_\nu(h). \tag{S2}
$$

These are the same original form and mean term, not a new energy model.
Both maps are continuous for its form norm. For
$v_k=\Phi^{(2k)}/\Phi-4^{-k}$, the existing critical-family result gives
$v_k\in\mathcal F$ and
$\|C_+v_k\|=\|C_-v_k\|$ for every $k\ge1$.

### The precise shortcut being tested

Suppose a measurable complex kernel $s(a,b)$, from positive edges $b$
to negative edges $a$, defines the ordinary integral operator

$$
(Sf)(a)=\int s(a,b)f(b)\,dK_+(b).
$$

Let finite strictly positive measurable weights $w_\pm$ and constants
$a_0,b_0>0$ satisfy

$$
\begin{aligned}
\int |s(a,b)|w_+(b)\,dK_+(b)&\le a_0w_-(a)
 &&(K_-\text{-a.e. }a),\\
\int |s(a,b)|w_-(a)\,dK_-(a)&\le b_0w_+(b)
 &&(K_+\text{-a.e. }b),\\
a_0b_0&\le1.
\end{aligned} \tag{S3}
$$

Schur's test gives $\|S\|\le\sqrt{a_0b_0}$. For these two measure
spaces its usual same-space formulation can be applied to their
disjoint union, with $S$ as the off-diagonal block. The proposed raw
reconstruction requirement is

$$
SC_+h=C_-h
\quad\text{for every original compact smooth even core test }h. \tag{S4}
$$

Under the inherited theta premises, (S3) and (S4) cannot both hold.
This conclusion includes complex signed kernels; it is not a
positivity-preservation argument.

### Theta jets distinguish the radial edge

For $r\ge0$ define

$$
H_r(t)=\frac{\Phi(r+t)+\Phi(r-t)}{2\Phi(r)}.
$$

It is holomorphic on the existing physical strip
$|\Im t|<\pi/4$, has $H_r(0)=1$, zero odd derivatives, and even
derivatives $\Phi^{(2k)}(r)/\Phi(r)$ at zero. Thus, if $|x|\ne|y|$
and $\lambda\ne0$ satisfy

$$
v_k(v)-v_k(u)=\lambda\bigl(v_k(y)-v_k(x)\bigr)
\quad\text{for every }k\ge1,
$$

the analytic identity theorem gives
$H_{|v|}-H_{|u|}=\lambda(H_{|y|}-H_{|x|})$. These functions are
integrable on the real line. Their angular Fourier transforms are
$\Xi(z)\cos(zr)/\Phi(r)$. Canceling $\Xi$ only on its known nonzero
neighborhood of zero gives

$$
\frac{\cos(z|v|)}{\Phi(v)}-\frac{\cos(z|u|)}{\Phi(u)}
=\lambda\left(
\frac{\cos(z|y|)}{\Phi(y)}-\frac{\cos(z|x|)}{\Phi(x)}\right).
\tag{S5}
$$

The finite entire cosine sum then vanishes identically. Independence
of its distinct exponential frequencies identifies its nonzero signed
atomic supports, so
$\{|u|,|v|\}=\{|x|,|y|\}$. An endpoint at zero only combines the two
equal zero-frequency atoms. The same argument shows that the full
vector of critical increments at a nondegenerate radial edge is nonzero.
Consequently its proportionality fiber consists of at most eight signed
and oriented endpoint pairs. No assertion that $\Phi$ is entire in its
physical coordinate, or that $\Xi$ has no zeros, is used.

### Norm attainment forces the ordinary kernel into a null fiber

By (S2), boundedness of $S$ and actual core density extend (S4) to
$\mathcal F$, including every $v_k$. Put $f_k=C_+v_k$ and $g_k=C_-v_k$.
Then $Sf_k=g_k$ and $\|Sf_k\|=\|f_k\|$. If $a_0b_0<1$, all these
vectors vanish. This is impossible: $K_-$ is a nonzero finite
absolutely continuous measure, it gives zero mass to $|x|=|y|$, and
the jet separation above makes the countable critical vector nonzero
at every other edge. Hence $a_0b_0=1$.

Equality now holds throughout the classical row/column Schur bound for
each $f_k$. In particular, row Cauchy–Schwarz is equality almost
everywhere. With
$m(a)=\int|s(a,b)|w_+(b)dK_+(b)$, its equality condition and (S4) give

$$
f_k(b)=w_+(b)e^{-i\arg s(a,b)}\frac{g_k(a)}{m(a)} \tag{S6}
$$

for $|s(a,\cdot)|dK_+$-almost every $b$ in any such row with $m(a)>0$.
The row and column certificates justify these integrals by
Cauchy–Schwarz and Tonelli. Only countably many $k$ occur, so one may
choose a conull set of rows and, inside each row, a common conull set
for all components. There is no uncountable intersection assertion.

At almost every negative edge $a$, some $g_k(a)$ is nonzero, which
forces $m(a)>0$. Equation(S6) makes the complete critical increment
vector at $b$ proportional to the vector at $a$. Equation(S5) confines
that row to the finite fiber with the same unordered radial endpoints.
But $K_+$ gives every point mass zero: its continuous part is a density,
and each prime graph is parametrized by continuous $dx$. Atomic jump
lengths are not point atoms in this edge-pair measure. Therefore the
finite fiber has zero $K_+$-mass, forcing $m(a)=0$, a contradiction.

### What remains available for the actual estimate

This tests an exact full-core reconstruction with an absolute Schur
certificate of product at most one. It excludes neither an abstract
contraction nor a kernel whose actual norm is better than its absolute
certificate. Products greater than one tending to one, controlled
approximate reconstruction, operators specified only on $\mathcal R$,
measure/distribution kernels and other norm estimates remain separate
possibilities. Finite atomic matrices are also outside the atomless
fiber argument.

In particular, let $P_\pm$ project onto
$\overline{C_\pm N}$ and set $e_\pm=(I-P_\pm)C_\pm$. All known
critical vectors have $e_\pm v_k=0$, so the preceding norm-attainment
argument has no stated conclusion for a transfer between those projected
increments. The existing mixed nullity gives an isometry
$U(C_+n)=C_-n$ from $\overline{C_+N}$ onto $\overline{C_-N}$ and
$P_-C_-h=UP_+C_+h$: test the latter identity against the dense family
$C_-N$ and use $q(n,h)=0$. Orthogonal decomposition therefore gives

$$
q(h)=\|e_+h\|^2-\|e_-h\|^2. \tag{S7}
$$

This is the ordinary simultaneous Hilbert-space cancellation applied to
the already specified mixed null family. Bare existence of a contraction
reconstructing $e_-$ from $e_+$ only reformulates the desired norm
domination. Its reconstruction and norm estimates must still be
proved jointly by independent estimates for the same actual transfer.
The original half-bound,
RH, Robin and the cofinal signed comparison remain unresolved. This
section applies existing Schur equality and Fourier uniqueness to the
specified theta family; it claims no new general theorem or Lean result.


## One source correction for the two critical edge projections

The [negative-edge Gram application](../Weil/lagarias2004li.md#a-common-source-inverse-for-both-critical-edge-projections)
uses the same signed edge measures to put an explicit positive symbolic
lower bound on the negative-edge metric, via three common-neighbor
anchors. On the centered critical source space this makes the common
Gram operator boundedly invertible and both critical edge-image ranges
closed. The two projections in (S7) then use the same correction
$n_h=G^{-1}P_NC_-^*C_-h$; it generally differs from $P_Nh$.
The paired edge-error bound for a Neumann truncation uses the exact
$P_N$ and $G$. It is not a finite algorithm, a pointwise error bound,
or a lower bound for the original theta energy. Acquisition of $P_N$
and the projected transfer's joint reconstruction/norm estimate remain
unproved. The path, Gram projection and Neumann tools are classical
applications, with no new general theorem or Lean certification.
