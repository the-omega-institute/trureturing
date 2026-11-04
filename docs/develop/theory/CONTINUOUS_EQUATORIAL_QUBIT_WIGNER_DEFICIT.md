# Continuous equatorial qubit Wigner deficit

## 1. Fixed frame and stabilizer distance

**Definition 1.1 (Wootters product frame).** Let $I,X,Y,Z$ be the Pauli
matrices, with $XY=iZ$, $YZ=iX$ and $ZX=iY$. Order the phase points
$(q,p)$ as $00,01,10,11$, and put

$$
A_{q,p}=\frac{I+(-1)^pX+(-1)^{q+p}Y+(-1)^qZ}{2},\qquad
\rho(r)=\frac{I+r_xX+r_yY+r_zZ}{2}.
$$

Thus $\rho(r)$ is a density matrix precisely when $\|r\|_2\leq1$, and

$$
W(r)=\frac14(1+r_x+r_y+r_z,\ 1-r_x-r_y+r_z,
1+r_x-r_y-r_z,\ 1-r_x+r_y-r_z).
$$

On two qubits use $A_i\otimes A_j$ and the coordinate $4i+j$,
with the first qubit as the outer index. Then
$W_\eta(i,j)=\operatorname{Tr}(\eta(A_i\otimes A_j))/4$ and
$W_{\rho(r)\otimes\rho(s)}=W(r)\otimes W(s)$.
These are the frame and measure of Dutta and Tushar,
[*A Phase-Space Geometric Measure of Magic in Qubit Systems*,
arXiv:2603.20792v5, §§2.3, 3.1–3.3](https://arxiv.org/html/2603.20792v5),
also fixed in the [literature note](../../../Library/QuantumStates/dutta2026wignerdistance.md).

**Definition 1.2 (Full free polytope).** A pure $n$-qubit Pauli stabilizer
state is the rank-one projector onto the common $+1$ eigenspace of an
abelian Pauli subgroup of order $2^n$ that does not contain $-I$.
Let $\mathrm{STAB}_n$ be the convex hull of these projectors and set

$$
\mathcal C(\eta)=\min_{\tau\in\mathrm{STAB}_n}
\|W_\eta-W_\tau\|_1\quad(n=1,2),\qquad
P=\operatorname{conv}\{p_0,\ldots,p_{59}\},\qquad
F(z)=\min_{p\in P}\|z-p\|_1\quad(z\in\mathbb R^{16}).
$$

The vectors $p_i$ are the complete two-qubit stabilizer vectors in
Definition 4.1. In particular $P=W(\mathrm{STAB}_2)$, and $F$ is
defined even for vectors that are not Wigner functions of positive matrices.
The minimum exists because $P$ is a nonempty compact polytope.
The Pauli subgroup, convex hull and distance definitions agree with
`Stab`, `Wfree`, `WignerOne`, `WignerTwo`, `COne` and `CTwo` in
[WignerDistanceMinimum](../../../D5/S3/Quantum/Magic/WignerDistanceMinimum.lean).
The coordinate identification is $(q,p)\mapsto2q+p$; the normalization
is $1/2$ for one-qubit traces and $1/4$ for two-qubit traces.

## 2. Continuous formula and proof

**Theorem 2.1 (Ma–Zhang continuous equatorial deficit).** Let
$r=(x,y,0)$ with $0\leq x,y\leq1$ and $x+y\geq1$, and let
$s=(u,v,w)$ with $0\leq u,v,w\leq1$ and $u+v+w\geq1$. Put

$$
\alpha=\frac{x+y-1}{2},\quad
\beta=\frac{u+v+w-1}{2},\quad
t=\min(\beta,u,v,w),\quad B=\alpha+\beta+\alpha\beta.
$$

Then, throughout this closed domain, including its nonphysical points,

$$
F(W(r)\otimes W(s))
=B-\min\left\{\frac{\alpha(1+t)}2,
\frac{t(1+2\alpha)}2\right\}.
$$

The proof and rational premises below are due to Haobo Ma and Wenlin Zhang.
The source measure and the single-qubit identity
$\mathcal C(\rho(r))=\frac12\max(0,\|r\|_1-1)$ on the physical Bloch ball
are due to Dutta and Tushar (v5, Proposition 4.3). Their
[§8.4(iii)](https://arxiv.org/html/2603.20792v5#S8.SS4)
asks for the positive-sign deficit slopes and breakpoints.

Proof. For any $S\in[-1,1]^{16}$ write
$h_P(S)=\max_i\langle S,p_i\rangle$. For every $p\in P$,
$\langle S,z\rangle-h_P(S)\leq\langle S,z-p\rangle\leq\|z-p\|_1$,
so $F(z)\geq\langle S,z\rangle-h_P(S)$.
Also $F$ is convex: for minimizers $p,p'$ and $0\leq\theta\leq1$,
$\theta p+(1-\theta)p'\in P$ and the triangle inequality bounds the
distance at $\theta z+(1-\theta)z'$ by
$\theta F(z)+(1-\theta)F(z')$. These are internal convex-analysis steps
(compare Dutta–Tushar, v5, Theorem 3.3 and Appendix A).

For the lower bound, regard $S$ as a $4\times4$ matrix. Let $V$ have
rows $(1,-1,-1,-1),(-1,-1,-1,-1),(1,-1,-1,-1),(1,-1,-1,-1)$.
Let $V_j$ change entry $j$ of its second row to $1$, for $j=1,2,3$
(indices start at zero). Let $T$ change the first row of $V$ to all $1$,
and let $T_j$ change entries $j$ of the first and second rows of $T$
to $-1$ and $1$, respectively. The eight witnesses, their exact support
values and the corresponding deficits are given in Definition 4.2.
Substitution of Definition 1.1 and the sixty vectors of Definition 4.1 gives

$$
\langle S_k,W(r)\otimes W(s)\rangle-h_P(S_k)=B-d_k,
\qquad
\{d_k:0\leq k<8\}=
\left\{\frac{\alpha(1+q)}2,\frac{q(1+2\alpha)}2:
q\in\{\beta,u,v,w\}\right\}.
$$

These are polynomial identities and finite maxima, with all coefficients
specified in §4. Since $\alpha,t\geq0$, their maximum is the asserted
lower bound.

For the upper bound, fix $\alpha$. If $\alpha<1/2$, set
$\theta=(x-2\alpha)/(1-2\alpha)\in[0,1]$; then
$r=\theta(1,2\alpha,0)+(1-\theta)(2\alpha,1,0)$.
At $\alpha=1/2$ the two corners coincide with $r=(1,1,0)$.
Fix also $(\beta,t)$. Every allowed $s$ is a convex combination of
permutations of $(1,2\beta-t,t)$, as follows.
If $t=\beta<1$, let $v_i$ have coordinate $1$ at position $i$ and $t$
elsewhere. Then

$$
s=\sum_{i=1}^3\frac{s_i-t}{1-t}v_i,\qquad
\sum_{i=1}^3\frac{s_i-t}{1-t}=1.
$$

If $t<\beta$, choose a smallest coordinate $s_k=t$ and set $b=2\beta-t$.
The other two coordinates sum to $1+b$ and belong to $[b,1]$; hence
they lie on the segment joining $(1,b)$ to $(b,1)$.
Here $0\leq t\leq b\leq1$: the first inequality follows from $t\leq\beta$,
and the last from the bound $s_i+s_j\leq2$.
The endpoints $t=1$ and $b=1$ already have the required corner form.
Thus convexity and distributivity of tensor products reduce the upper bound
to the twelve orientations

$$
r_0(a)=(1,a,0),\quad r_1(a)=(a,1,0),\quad
s_\pi(b,c)=((1,b,c)_{\pi_0},(1,b,c)_{\pi_1},(1,b,c)_{\pi_2}),
\qquad 0\leq a\leq1,\quad0\leq c\leq b\leq1,
$$

where $\pi$ ranges over the six permutations of $(0,1,2)$.
For all these corners $\alpha=a/2$, $\beta=(b+c)/2$ and $t=c$.
Consequently the desired upper bound is $\max(f_1,f_2)$, where

$$
f_1(a,b,c,d,e)=\frac{b+c}{2}+\frac{a+d}{4},\qquad
f_2(a,b,c,d,e)=\frac b2+\frac{2a+d-e}{4},
$$

evaluated at $d=ab,e=ac$.

Use the six lifted vertices $v_0,\ldots,v_5$ of Definition 4.3.
Their barycentric coordinates at $z=(a,b,c,d,e)$ are

$$
\lambda(z)=(1-a-b+d,\ b-d-c+e,\ c-e,\ a-d,\ d-e,\ e).
$$

They sum to one and reconstruct $z$. At a lifted product point they are
$((1-a)(1-b),(1-a)(b-c),(1-a)c,a(1-b),a(b-c),ac)$,
so are nonnegative. Conversely each $v_i$ is a lifted product point;
the convex hull of all lifted product points is therefore exactly this
five-dimensional simplex $\Delta$.
For each orientation define its affine extension on $\mathbb R^5$ by

$$
L_{\varepsilon,\pi}(z)=\sum_{i=0}^5\lambda_i(z)
\bigl(W(r_\varepsilon(a_i))\otimes W(s_\pi(b_i,c_i))\bigr),
\qquad v_i=(a_i,b_i,c_i,d_i,e_i).
$$

Each coordinate of the tensor product is affine in $1,a,b,c,ab,ac$.
The displayed interpolation matches these six functions at the six
vertices; it follows that
$L_{\varepsilon,\pi}(a,b,c,ab,ac)=W(r_\varepsilon(a))\otimes W(s_\pi(b,c))$.

Cut $\Delta$ by $g(z)=2c-a+e=0$. Since
$f_1-f_2=g/4$, $\max(f_1,f_2)$ is affine on each of
$\Delta_+=\Delta\cap\{g\geq0\}$ and $\Delta_-=\Delta\cap\{g\leq0\}$.
The values of $g$ at $v_0,\ldots,v_5$ are $(0,0,2,-1,-1,2)$.
The vertices of a simplex cut by a half-space are its retained vertices
and the intersections with its edges: a new vertex must lie on the
cutting hyperplane and on at least four independent simplex facets,
hence on an edge. There are four edges with opposite strict signs,
joining $\{v_2,v_5\}$ to $\{v_3,v_4\}$.
The union of the vertices of $\Delta_+$ and $\Delta_-$ is the ten points
$z_0,\ldots,z_9$ listed in Definition 4.3.

Definition 4.4 specifies, for every one of the twelve orientations and
every one of these ten points, rational weights $m_i\geq0$ of sum one
with the exact equality

$$
\left\|L_{\varepsilon,\pi}(z_j)-\sum_{i=0}^{59}m_ip_i\right\|_1
=\max(f_1(z_j),f_2(z_j)).
$$

All terms of these 120 finite equalities are explicitly defined by the
tables; in particular their left sides are finite rational sums of
absolute values. They give upper bounds for $F$ at every cut vertex.
For any convex decomposition $z=\sum_j\mu_jz_j$ within either cut
polytope, affine linearity of $L$, convexity of $F$ and the affineness of
the active $f_k$ give

$$
F(L(z))\leq\sum_j\mu_jF(L(z_j))
\leq\sum_j\mu_j f_k(z_j)=f_k(z).
$$

This proves the upper bound on both entire polytopes, hence on every
lifted product point and every auxiliary corner family.
Finally the original convex decompositions keep $\alpha,\beta,t$ fixed,
so have a common right side. Applying convexity once more proves the
upper bound for every original $r,s$. The lower bound gives equality. $\square$

## 3. Physical states, symmetry and parameter regions

**Corollary 3.1 (Physical positive-sign branch).** Suppose $\rho,\sigma$
are physical qubits, $r_z=0$, $\mathcal C(\rho)>0$,
$\mathcal C(\sigma)>0$ and $s_xs_ys_z>0$. Define

$$
\alpha=\frac{|r_x|+|r_y|-1}{2}=\mathcal C(\rho),\quad
\beta=\frac{|s_x|+|s_y|+|s_z|-1}{2}=\mathcal C(\sigma),\quad
t=\min(\beta,|s_x|,|s_y|,|s_z|).
$$

Then the physical deficit
$D=(1+\mathcal C(\rho))(1+\mathcal C(\sigma))-1-\mathcal C(\rho\otimes\sigma)$
is strictly positive and equals

$$
D=\begin{cases}
\alpha(1+t)/2,&\alpha\leq t/(1-t),\\
t(1+2\alpha)/2,&\alpha\geq t/(1-t).
\end{cases}
$$

Proof. Pauli conjugation flips any prescribed pair of Bloch signs.
Because $r_z=0$, a choice of even sign changes makes both nonzero
equatorial coordinates nonnegative. Since $s_xs_ys_z>0$, there are an
even number of negative coordinates of $s$, and another such conjugation
makes all three positive. These conjugations permute the four sign
triples $(1,1,1),(-1,-1,1),(1,-1,-1),(-1,1,-1)$ of the fixed frame.
On two qubits they therefore permute Wigner coordinates, preserve the
full stabilizer polytope and preserve the $\ell_1$ norm.
The single-qubit identity of Dutta–Tushar, Proposition 4.3, identifies
$\alpha,\beta$ with the stated distances. Theorem 2.1 applies.
The physical bounds are $0<\alpha\leq(\sqrt2-1)/2$ and
$0<\beta\leq(\sqrt3-1)/2<1$, so $0<t<1$.
Comparing the two expressions gives $\alpha(1-t)\leq t$ for the first
piece. Both expressions are strictly positive. $\square$

**Corollary 3.2 (Closed boundaries and coordinate regions).** Under the
closed-domain hypotheses of Theorem 2.1 the algebraic deficit $B-F$ is
zero if and only if $\alpha=0$ or $t=0$.
The regions for the minimum coordinate are
$t=\beta$ when $\beta\leq u,v,w$, $t=u$ when $u\leq\beta,v,w$,
and the analogous regions for $v,w$. Ties give the same value.
On the physical domain, whenever $t<1$ the two pieces meet at
$\alpha=t/(1-t)$. For a fixed physical $\sigma$ in Corollary 3.1,
the second piece has nonempty relative interior in the nonnegative
physical equatorial disk precisely when $t<3-2\sqrt2$.
At equality it touches that disk only at $(1,1,0)/\sqrt2$.

Proof. The minimum of the two nonnegative expressions in Theorem 2.1
vanishes precisely on the two stated boundaries. The coordinate regions
are the definition of a minimum. For the last assertion compare
$t/(1-t)$ with the maximum $(\sqrt2-1)/2$ of $\alpha$;
equality in the equatorial Cauchy–Schwarz bound occurs only at the
displayed point in the nonnegative quadrant. $\square$

**Proposition 3.3 (Deficit ratios).** For $\alpha>0$ and physical $t<1$,
the ratio $D/\alpha$ is $(1+t)/2$ on the first piece and
$t+t/(2\alpha)$ on the second. It depends only on $\alpha$ and
$\beta,|s_x|,|s_y|,|s_z|$, and is independent of the equatorial
direction at fixed $\alpha$. For $s=(7,4,2)/10$, $\beta=t=3/20$,
the breakpoint is $3/17$, the first ratio is $23/40$, and the ratio at
$r=(1,1,0)/\sqrt2$ is $3(2+\sqrt2)/20$.

Proof. Divide the two pieces by $\alpha$ and substitute the given
rational values and $\alpha=(\sqrt2-1)/2$. $\square$

## 4. Exact rational premises

**Definition 4.1 (All sixty stabilizer vectors).** Each row of the first
table specifies the three signed nonidentity elements of a stabilizer
group $G_i$, with identity implicit. For a signed Pauli $\epsilon AB$
in that row put

$$
\tau_i=\frac14\left(I\otimes I+
\sum_{\epsilon AB\in G_i\setminus\{I\otimes I\}}
\epsilon A\otimes B\right),\qquad
p_i(4j+k)=\frac{1+\sum_{\epsilon AB\in G_i\setminus\{I\otimes I\}}
\epsilon\chi_A(j)\chi_B(k)}{16},
$$

where $\chi_I=1$, $\chi_X(q,p)=(-1)^p$,
$\chi_Y(q,p)=(-1)^{q+p}$ and $\chi_Z(q,p)=(-1)^q$.
Thus the displayed Wigner vector is also determined directly by the
signed group; indices in every subsequent mixture refer to this table.
The table includes entangled stabilizers as well as product stabilizers.
Completeness follows by enumerating the maximal commuting unsigned Pauli
triples: the fifteen nonidentity labels each commute with six distinct
nonidentity labels, and each triple accounts for six ordered pairs,
giving fifteen triples. Each has four consistent sign choices, hence
sixty distinct rank-one projectors. The rows give all these choices;
distinctness also follows from Pauli trace orthogonality. This is the
same signed-commuting-generator classification expressed by
`Enumeration.candidates`, `stabilizer_two_generators` and `projector_wigner`
in [QubitWignerDistanceTensorRules](../../../D5/S3/Quantum/Magic/QubitWignerDistanceTensorRules.lean).

| $i$ | Signed nonidentity group elements | $p_i$ in coordinate order |
| --- | --- | --- |
| 0 | +IZ +ZI +ZZ | 1/4 1/4 0 0 1/4 1/4 0 0 0 0 0 0 0 0 0 0 |
| 1 | +IZ +XI +XZ | 1/4 1/4 0 0 0 0 0 0 1/4 1/4 0 0 0 0 0 0 |
| 2 | +IX +ZI +ZX | 1/4 0 1/4 0 1/4 0 1/4 0 0 0 0 0 0 0 0 0 |
| 3 | +IX +XI +XX | 1/4 0 1/4 0 0 0 0 0 1/4 0 1/4 0 0 0 0 0 |
| 4 | +IZ +YI +YZ | 1/4 1/4 0 0 0 0 0 0 0 0 0 0 1/4 1/4 0 0 |
| 5 | +XX -YY +ZZ | 1/8 1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 1/8 1/8 |
| 6 | +IY +ZI +ZY | 1/4 0 0 1/4 1/4 0 0 1/4 0 0 0 0 0 0 0 0 |
| 7 | +IX +YI +YX | 1/4 0 1/4 0 0 0 0 0 0 0 0 0 1/4 0 1/4 0 |
| 8 | +IY +XI +XY | 1/4 0 0 1/4 0 0 0 0 1/4 0 0 1/4 0 0 0 0 |
| 9 | +IZ -YI -YZ | 0 0 0 0 1/4 1/4 0 0 1/4 1/4 0 0 0 0 0 0 |
| 10 | +IZ -XI -XZ | 0 0 0 0 1/4 1/4 0 0 0 0 0 0 1/4 1/4 0 0 |
| 11 | +XY +YX +ZZ | 1/4 0 0 0 0 1/4 0 0 0 0 0 1/4 0 0 1/4 0 |
| 12 | +XZ +YY +ZX | 1/4 0 0 0 0 0 1/4 0 0 1/4 0 0 0 0 0 1/4 |
| 13 | -IY +ZI -ZY | 0 1/4 1/4 0 0 1/4 1/4 0 0 0 0 0 0 0 0 0 |
| 14 | -IX +ZI -ZX | 0 1/4 0 1/4 0 1/4 0 1/4 0 0 0 0 0 0 0 0 |
| 15 | +IX -YI -YX | 0 0 0 0 1/4 0 1/4 0 1/4 0 1/4 0 0 0 0 0 |
| 16 | +IX -XI -XX | 0 0 0 0 1/4 0 1/4 0 0 0 0 0 1/4 0 1/4 0 |
| 17 | +IY +YI +YY | 1/4 0 0 1/4 0 0 0 0 0 0 0 0 1/4 0 0 1/4 |
| 18 | +XX +YZ +ZY | 1/4 0 0 0 0 0 0 1/4 0 0 1/4 0 0 1/4 0 0 |
| 19 | -IY +XI -XY | 0 1/4 1/4 0 0 0 0 0 0 1/4 1/4 0 0 0 0 0 |
| 20 | -IX +XI -XX | 0 1/4 0 1/4 0 0 0 0 0 1/4 0 1/4 0 0 0 0 |
| 21 | -XY -YX +ZZ | 0 1/4 0 0 1/4 0 0 0 0 0 1/4 0 0 0 0 1/4 |
| 22 | +IZ -ZI -ZZ | 0 0 0 0 0 0 0 0 1/4 1/4 0 0 1/4 1/4 0 0 |
| 23 | -XX +YY +ZZ | 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 |
| 24 | +XZ -YX +ZY | 1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 1/8 -1/8 -1/8 1/8 1/8 1/8 |
| 25 | -XY +YZ +ZX | 1/8 1/8 1/8 -1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 1/8 -1/8 1/8 |
| 26 | -XZ -YY +ZX | 0 0 1/4 0 1/4 0 0 0 0 0 0 1/4 0 1/4 0 0 |
| 27 | +XZ -YY -ZX | 0 1/4 0 0 0 0 0 1/4 1/4 0 0 0 0 0 1/4 0 |
| 28 | -IZ +ZI -ZZ | 0 0 1/4 1/4 0 0 1/4 1/4 0 0 0 0 0 0 0 0 |
| 29 | +IY -YI -YY | 0 0 0 0 1/4 0 0 1/4 1/4 0 0 1/4 0 0 0 0 |
| 30 | +XX -YZ -ZY | 0 0 1/4 0 0 1/4 0 0 1/4 0 0 0 0 0 0 1/4 |
| 31 | +IX -ZI -ZX | 0 0 0 0 0 0 0 0 1/4 0 1/4 0 1/4 0 1/4 0 |
| 32 | +IY -XI -XY | 0 0 0 0 1/4 0 0 1/4 0 0 0 0 1/4 0 0 1/4 |
| 33 | -IX -XI +XX | 0 0 0 0 0 1/4 0 1/4 0 0 0 0 0 1/4 0 1/4 |
| 34 | -IY +YI -YY | 0 1/4 1/4 0 0 0 0 0 0 0 0 0 0 1/4 1/4 0 |
| 35 | -IX +YI -YX | 0 1/4 0 1/4 0 0 0 0 0 0 0 0 0 1/4 0 1/4 |
| 36 | -XZ +YX +ZY | 1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 1/8 -1/8 1/8 1/8 1/8 1/8 1/8 1/8 -1/8 |
| 37 | +XY +YZ -ZX | 1/8 1/8 -1/8 1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 1/8 -1/8 |
| 38 | +XY -YZ +ZX | 1/8 -1/8 1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 -1/8 1/8 1/8 1/8 |
| 39 | +XZ +YX -ZY | 1/8 1/8 1/8 -1/8 -1/8 1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 1/8 |
| 40 | -IZ +XI -XZ | 0 0 1/4 1/4 0 0 0 0 0 0 1/4 1/4 0 0 0 0 |
| 41 | -IZ -ZI +ZZ | 0 0 0 0 0 0 0 0 0 0 1/4 1/4 0 0 1/4 1/4 |
| 42 | +XX +YY -ZZ | 1/8 -1/8 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 -1/8 1/8 |
| 43 | -IY -YI +YY | 0 0 0 0 0 1/4 1/4 0 0 1/4 1/4 0 0 0 0 0 |
| 44 | -IX -YI +YX | 0 0 0 0 0 1/4 0 1/4 0 1/4 0 1/4 0 0 0 0 |
| 45 | +IY -ZI -ZY | 0 0 0 0 0 0 0 0 1/4 0 0 1/4 1/4 0 0 1/4 |
| 46 | -IY -XI +XY | 0 0 0 0 0 1/4 1/4 0 0 0 0 0 0 1/4 1/4 0 |
| 47 | -XX -YZ +ZY | 0 0 0 1/4 1/4 0 0 0 0 1/4 0 0 0 0 1/4 0 |
| 48 | -IX -ZI +ZX | 0 0 0 0 0 0 0 0 0 1/4 0 1/4 0 1/4 0 1/4 |
| 49 | -IZ -XI +XZ | 0 0 0 0 0 0 1/4 1/4 0 0 0 0 0 0 1/4 1/4 |
| 50 | -IZ +YI -YZ | 0 0 1/4 1/4 0 0 0 0 0 0 0 0 0 0 1/4 1/4 |
| 51 | -XX +YZ -ZY | 0 1/4 0 0 0 0 1/4 0 0 0 0 1/4 1/4 0 0 0 |
| 52 | +XY -YX -ZZ | 0 0 0 1/4 0 0 1/4 0 1/4 0 0 0 0 1/4 0 0 |
| 53 | -XZ +YY -ZX | 0 0 0 1/4 0 1/4 0 0 0 0 1/4 0 1/4 0 0 0 |
| 54 | -XY +YX -ZZ | 0 0 1/4 0 0 0 0 1/4 0 1/4 0 0 1/4 0 0 0 |
| 55 | -XZ -YX -ZY | -1/8 1/8 1/8 1/8 1/8 1/8 1/8 -1/8 1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 1/8 |
| 56 | -XY -YZ -ZX | -1/8 1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 1/8 -1/8 1/8 1/8 |
| 57 | -IZ -YI +YZ | 0 0 0 0 0 0 1/4 1/4 0 0 1/4 1/4 0 0 0 0 |
| 58 | -IY -ZI +ZY | 0 0 0 0 0 0 0 0 0 1/4 1/4 0 0 1/4 1/4 0 |
| 59 | -XX -YY -ZZ | -1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 1/8 1/8 1/8 1/8 -1/8 |

**Definition 4.2 (Eight dual witnesses).** The rows of the second table
are flattened in the same first-qubit-outer order as $p_i$.
They are $(V,T,V_3,V_2,V_1,T_2,T_3,T_1)$ in that order.
Their support values are the maxima of the sixty dot products with
Definition 4.1, and their $d_k$ entries specify the polynomial identities
used in Theorem 2.1.

| $k$ | $S_k$ | Sixteen entries | $h_P(S_k)$ | $d_k$ |
| --- | --- | --- | --- | --- |
| 0 | $V$ | 1 -1 -1 -1 -1 -1 -1 -1 1 -1 -1 -1 1 -1 -1 -1 | 0 | $\alpha(1+\beta)/2$ |
| 1 | $T$ | 1 1 1 1 -1 -1 -1 -1 1 -1 -1 -1 1 -1 -1 -1 | 1/2 | $\beta(1+2\alpha)/2$ |
| 2 | $V_3$ | 1 -1 -1 -1 -1 -1 -1 1 1 -1 -1 -1 1 -1 -1 -1 | 0 | $\alpha(1+v)/2$ |
| 3 | $V_2$ | 1 -1 -1 -1 -1 -1 1 -1 1 -1 -1 -1 1 -1 -1 -1 | 0 | $\alpha(1+u)/2$ |
| 4 | $V_1$ | 1 -1 -1 -1 -1 1 -1 -1 1 -1 -1 -1 1 -1 -1 -1 | 0 | $\alpha(1+w)/2$ |
| 5 | $T_2$ | 1 1 -1 1 -1 -1 1 -1 1 -1 -1 -1 1 -1 -1 -1 | 1/2 | $u(1+2\alpha)/2$ |
| 6 | $T_3$ | 1 1 1 -1 -1 -1 -1 1 1 -1 -1 -1 1 -1 -1 -1 | 1/2 | $v(1+2\alpha)/2$ |
| 7 | $T_1$ | 1 -1 1 1 -1 1 -1 -1 1 -1 -1 -1 1 -1 -1 -1 | 1/2 | $w(1+2\alpha)/2$ |

**Definition 4.3 (Lifted and cut vertices).** The first six rows of the
following table are $v_0,\ldots,v_5$, also denoted $z_0,\ldots,z_5$.
The remaining rows are the four cut-edge intersections.

| $j$ | $z_j=(a,b,c,d,e)$ |
| --- | --- |
| 0 | $(0,0,0,0,0)$ |
| 1 | $(0,1,0,0,0)$ |
| 2 | $(0,1,1,0,0)$ |
| 3 | $(1,0,0,0,0)$ |
| 4 | $(1,1,0,1,0)$ |
| 5 | $(1,1,1,1,1)$ |
| 6 | $(2/3,1/3,1/3,0,0)$ |
| 7 | $(2/3,1,1/3,2/3,0)$ |
| 8 | $(1,1/3,1/3,1/3,1/3)$ |
| 9 | $(1,1,1/3,1,1/3)$ |

**Definition 4.4 (Rational attaining mixtures).** A row
$(\varepsilon,\pi,j,V,m)$ in the final table specifies the orientation
of Theorem 2.1, the point $z_j$, the common value
$V=\max(f_1(z_j),f_2(z_j))$, and a finite list $i:m_i$ of nonzero
mixture coefficients. Every unlisted coefficient is zero. In every row
$m_i\geq0$, $\sum_i m_i=1$ and
$\sum_{\ell=0}^{15}|L_{\varepsilon,\pi}(z_j)_\ell-\sum_i m_i p_i(\ell)|=V$.
The table contains one row for every
$\varepsilon\in\{0,1\}$, permutation $\pi$ of $(0,1,2)$ and
$j\in\{0,\ldots,9\}$; this is the full finite premise of the upper bound.

| $\varepsilon$ | $\pi$ | $j$ | $V$ | Nonzero coefficients $i:m_i$ |
| --- | --- | --- | --- | --- |
| 0 | 0,1,2 | 0 | 0 | 3:1 |
| 0 | 0,1,2 | 1 | 1/2 | 3:1/2 8:1/2 |
| 0 | 0,1,2 | 2 | 1 | 1:1 |
| 0 | 0,1,2 | 3 | 1/2 | 3:1/2 7:1/2 |
| 0 | 0,1,2 | 4 | 5/4 | 3:1/4 7:1/4 8:1/4 30:1/4 |
| 0 | 0,1,2 | 5 | 3/2 | 22:1 |
| 0 | 0,1,2 | 6 | 1/2 | 3:2/3 7:1/3 |
| 0 | 0,1,2 | 7 | 1 | 7:1/3 8:1/3 42:1/3 |
| 0 | 0,1,2 | 8 | 2/3 | 3:1/3 7:2/3 |
| 0 | 0,1,2 | 9 | 7/6 | 7:1/3 8:1/3 42:1/3 |
| 0 | 0,2,1 | 0 | 0 | 3:1 |
| 0 | 0,2,1 | 1 | 1/2 | 1:1/2 3:1/2 |
| 0 | 0,2,1 | 2 | 1 | 1:1 |
| 0 | 0,2,1 | 3 | 1/2 | 3:1/2 7:1/2 |
| 0 | 0,2,1 | 4 | 5/4 | 3:1/4 4:1/4 7:1/4 54:1/4 |
| 0 | 0,2,1 | 5 | 3/2 | 22:1 |
| 0 | 0,2,1 | 6 | 1/2 | 3:2/3 7:1/3 |
| 0 | 0,2,1 | 7 | 1 | 3:1/3 4:1/3 39:1/3 |
| 0 | 0,2,1 | 8 | 2/3 | 3:1/3 7:2/3 |
| 0 | 0,2,1 | 9 | 7/6 | 3:1/3 4:1/3 39:1/3 |
| 0 | 1,0,2 | 0 | 0 | 8:1 |
| 0 | 1,0,2 | 1 | 1/2 | 3:1/2 8:1/2 |
| 0 | 1,0,2 | 2 | 1 | 1:1 |
| 0 | 1,0,2 | 3 | 1/2 | 8:1/2 17:1/2 |
| 0 | 1,0,2 | 4 | 5/4 | 3:1/4 7:1/4 8:1/4 30:1/4 |
| 0 | 1,0,2 | 5 | 3/2 | 22:1 |
| 0 | 1,0,2 | 6 | 1/2 | 8:2/3 17:1/3 |
| 0 | 1,0,2 | 7 | 1 | 7:1/3 8:1/3 42:1/3 |
| 0 | 1,0,2 | 8 | 2/3 | 8:1/3 17:2/3 |
| 0 | 1,0,2 | 9 | 7/6 | 7:1/3 8:1/3 42:1/3 |
| 0 | 1,2,0 | 0 | 0 | 1:1 |
| 0 | 1,2,0 | 1 | 1/2 | 1:1/2 3:1/2 |
| 0 | 1,2,0 | 2 | 1 | 1:1 |
| 0 | 1,2,0 | 3 | 1/2 | 1:1/2 4:1/2 |
| 0 | 1,2,0 | 4 | 5/4 | 3:1/4 4:1/4 7:1/4 54:1/4 |
| 0 | 1,2,0 | 5 | 3/2 | 22:1 |
| 0 | 1,2,0 | 6 | 1/2 | 1:2/3 4:1/3 |
| 0 | 1,2,0 | 7 | 1 | 3:1/3 4:1/3 39:1/3 |
| 0 | 1,2,0 | 8 | 2/3 | 1:1/3 4:2/3 |
| 0 | 1,2,0 | 9 | 7/6 | 3:1/3 4:1/3 39:1/3 |
| 0 | 2,0,1 | 0 | 0 | 8:1 |
| 0 | 2,0,1 | 1 | 1/2 | 1:1/2 8:1/2 |
| 0 | 2,0,1 | 2 | 1 | 1:1 |
| 0 | 2,0,1 | 3 | 1/2 | 8:1/2 17:1/2 |
| 0 | 2,0,1 | 4 | 5/4 | 1:1/4 4:1/4 17:1/4 51:1/4 |
| 0 | 2,0,1 | 5 | 3/2 | 22:1 |
| 0 | 2,0,1 | 6 | 1/2 | 8:2/3 17:1/3 |
| 0 | 2,0,1 | 7 | 1 | 1:1/3 17:1/3 37:1/3 |
| 0 | 2,0,1 | 8 | 2/3 | 8:1/3 17:2/3 |
| 0 | 2,0,1 | 9 | 7/6 | 1:1/3 17:1/3 37:1/3 |
| 0 | 2,1,0 | 0 | 0 | 1:1 |
| 0 | 2,1,0 | 1 | 1/2 | 1:1/2 8:1/2 |
| 0 | 2,1,0 | 2 | 1 | 1:1 |
| 0 | 2,1,0 | 3 | 1/2 | 1:1/2 4:1/2 |
| 0 | 2,1,0 | 4 | 5/4 | 1:1/4 4:1/4 17:1/4 51:1/4 |
| 0 | 2,1,0 | 5 | 3/2 | 22:1 |
| 0 | 2,1,0 | 6 | 1/2 | 1:2/3 4:1/3 |
| 0 | 2,1,0 | 7 | 1 | 1:1/3 17:1/3 37:1/3 |
| 0 | 2,1,0 | 8 | 2/3 | 1:1/3 4:2/3 |
| 0 | 2,1,0 | 9 | 7/6 | 1:1/3 17:1/3 37:1/3 |
| 1 | 0,1,2 | 0 | 0 | 7:1 |
| 1 | 0,1,2 | 1 | 1/2 | 7:1/2 17:1/2 |
| 1 | 0,1,2 | 2 | 1 | 4:1 |
| 1 | 0,1,2 | 3 | 1/2 | 3:1/2 7:1/2 |
| 1 | 0,1,2 | 4 | 5/4 | 3:1/4 7:1/4 8:1/4 30:1/4 |
| 1 | 0,1,2 | 5 | 3/2 | 22:1 |
| 1 | 0,1,2 | 6 | 1/2 | 3:1/3 7:2/3 |
| 1 | 0,1,2 | 7 | 1 | 7:1/2 8:1/6 17:1/6 53:1/6 |
| 1 | 0,1,2 | 8 | 2/3 | 3:1/3 7:2/3 |
| 1 | 0,1,2 | 9 | 7/6 | 7:1/3 8:1/3 42:1/3 |
| 1 | 0,2,1 | 0 | 0 | 7:1 |
| 1 | 0,2,1 | 1 | 1/2 | 4:1/2 7:1/2 |
| 1 | 0,2,1 | 2 | 1 | 4:1 |
| 1 | 0,2,1 | 3 | 1/2 | 3:1/2 7:1/2 |
| 1 | 0,2,1 | 4 | 5/4 | 3:1/4 4:1/4 7:1/4 54:1/4 |
| 1 | 0,2,1 | 5 | 3/2 | 22:1 |
| 1 | 0,2,1 | 6 | 1/2 | 3:1/3 7:2/3 |
| 1 | 0,2,1 | 7 | 1 | 3:1/3 4:1/3 39:1/3 |
| 1 | 0,2,1 | 8 | 2/3 | 3:1/3 7:2/3 |
| 1 | 0,2,1 | 9 | 7/6 | 3:1/3 4:1/3 39:1/3 |
| 1 | 1,0,2 | 0 | 0 | 17:1 |
| 1 | 1,0,2 | 1 | 1/2 | 7:1/2 17:1/2 |
| 1 | 1,0,2 | 2 | 1 | 4:1 |
| 1 | 1,0,2 | 3 | 1/2 | 8:1/2 17:1/2 |
| 1 | 1,0,2 | 4 | 5/4 | 3:1/4 7:1/4 8:1/4 30:1/4 |
| 1 | 1,0,2 | 5 | 3/2 | 22:1 |
| 1 | 1,0,2 | 6 | 1/2 | 8:1/3 17:2/3 |
| 1 | 1,0,2 | 7 | 1 | 7:1/2 8:1/6 17:1/6 53:1/6 |
| 1 | 1,0,2 | 8 | 2/3 | 8:1/3 17:2/3 |
| 1 | 1,0,2 | 9 | 7/6 | 7:1/3 8:1/3 42:1/3 |
| 1 | 1,2,0 | 0 | 0 | 4:1 |
| 1 | 1,2,0 | 1 | 1/2 | 4:1/2 7:1/2 |
| 1 | 1,2,0 | 2 | 1 | 4:1 |
| 1 | 1,2,0 | 3 | 1/2 | 1:1/2 4:1/2 |
| 1 | 1,2,0 | 4 | 5/4 | 3:1/4 4:1/4 7:1/4 54:1/4 |
| 1 | 1,2,0 | 5 | 3/2 | 22:1 |
| 1 | 1,2,0 | 6 | 1/2 | 1:1/3 4:2/3 |
| 1 | 1,2,0 | 7 | 1 | 3:1/3 4:1/3 39:1/3 |
| 1 | 1,2,0 | 8 | 2/3 | 1:1/3 4:2/3 |
| 1 | 1,2,0 | 9 | 7/6 | 3:1/3 4:1/3 39:1/3 |
| 1 | 2,0,1 | 0 | 0 | 17:1 |
| 1 | 2,0,1 | 1 | 1/2 | 4:1/2 17:1/2 |
| 1 | 2,0,1 | 2 | 1 | 4:1 |
| 1 | 2,0,1 | 3 | 1/2 | 8:1/2 17:1/2 |
| 1 | 2,0,1 | 4 | 5/4 | 1:1/4 4:1/4 17:1/4 51:1/4 |
| 1 | 2,0,1 | 5 | 3/2 | 22:1 |
| 1 | 2,0,1 | 6 | 1/2 | 8:1/3 17:2/3 |
| 1 | 2,0,1 | 7 | 1 | 1:1/3 17:1/3 37:1/3 |
| 1 | 2,0,1 | 8 | 2/3 | 8:1/3 17:2/3 |
| 1 | 2,0,1 | 9 | 7/6 | 1:1/3 17:1/3 37:1/3 |
| 1 | 2,1,0 | 0 | 0 | 4:1 |
| 1 | 2,1,0 | 1 | 1/2 | 4:1/2 17:1/2 |
| 1 | 2,1,0 | 2 | 1 | 4:1 |
| 1 | 2,1,0 | 3 | 1/2 | 1:1/2 4:1/2 |
| 1 | 2,1,0 | 4 | 5/4 | 1:1/4 4:1/4 17:1/4 51:1/4 |
| 1 | 2,1,0 | 5 | 3/2 | 22:1 |
| 1 | 2,1,0 | 6 | 1/2 | 1:1/3 4:2/3 |
| 1 | 2,1,0 | 7 | 1 | 1:1/3 17:1/3 37:1/3 |
| 1 | 2,1,0 | 8 | 2/3 | 1:1/3 4:2/3 |
| 1 | 2,1,0 | 9 | 7/6 | 1:1/3 17:1/3 37:1/3 |

## 追加锚（本行以下为增补区）
