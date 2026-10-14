# AURIC FIB-ATOM: index realization, exact syzygies and self-dual elliptic carriers — continuation

> This continuation of [Circulation Control, KL Action and Toric Relations](AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md) follows its chapter 24. Its chapter 23 supplies the five-mode dictionary, four-corner relation, singular quadric and finite Bargmann quotient. [Pyramid Correlation and Native Continuation](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md), chapter 26, supplies the Hibi history kernel, feasible sectors and one zero ray per sector. The applications below identify these quotient spaces with kernels of explicitly graded elliptic complexes on smooth ambient projective spaces; their metrics and positive spectra are separate structures.

## 25. AURIC FIB-ATOM index realization: the four-corner quotient and its elliptic carrier

### 25.1 The relation source and the comparison to be made

**Definition 25.1 (The five-mode relation with its original labels).**
Continue [Toric Relations, chapter 24][T25]; the supplier of the present
relation is that volume's §§23.1, 23.3 and 23.7. The mode order is
$(0,1,2,3,13)$, meaning input supports
$(\varnothing,\{1\},\{2\},\{3\},\{1,3\})$.
Their output names are respectively
$(\mathrm{null},[2],[3],[5],[2,5])$; input mode $13$ is not an output
integer thirteen. In low, high, middle coordinate order the columns are

$$
v_0=(0,0,0),\quad v_1=(1,0,0),\quad v_2=(0,0,1),
\quad v_3=(0,1,0),\quad v_{13}=(1,1,0).
$$

The augmented occupancy map and its supplied primitive integer kernel are

$$
A=\begin{pmatrix}
1&1&1&1&1\\0&1&0&0&1\\0&0&0&1&1\\0&0&1&0&0
\end{pmatrix},\qquad
\ker_{\mathbb Z}A=\mathbb Z(1,-1,0,-1,1).
$$

Use the sign convention

$$
f=z_1z_3-z_0z_{13},\qquad
Q_0=\{f=0\}\subset\mathbb {CP}^{4},\qquad
R_3=\mathbb C[z_0,z_1,z_2,z_3,z_{13}]/(f).
$$

The sign is opposite to the monomial difference attached to the displayed
kernel generator, which leaves its ideal unchanged. The three in $R_3$
counts positions, not the dimension of the ambient projective space.
The derivative in the indicated mode order is

$$
\nabla f=(-z_{13},z_3,0,z_1,-z_0).
$$

Thus the supplier's singular point is exactly $[0:0:1:0:0]$.
All elliptic operators in this chapter are on the smooth ambient
$\mathbb {CP}^{4}$ unless a smooth quadric is explicitly specified.
The singular $Q_0$ is not silently treated as a smooth compact base.

**Definition 25.2 (Finite carrier and its quotient map).**
For an integer $m\ge0$, let $\mathcal P_m$ be the homogeneous degree $m$
polynomials in these five variables, and put $\mathcal P_d=0$ for $d<0$.
The supplied Bargmann inner product is

$$
\langle z^\alpha,z^\beta\rangle=\delta_{\alpha\beta}\alpha!,
\qquad \alpha!=\prod_s\alpha_s!.
$$

The original normalized occupation vector maps to
$z^\alpha/\sqrt{\alpha!}$. Multiplication and its finite adjoint are

$$
M_f:\mathcal P_{m-2}\longrightarrow\mathcal P_m,\qquad
A_m=M_f^\dagger=\partial_1\partial_3-\partial_0\partial_{13},
\qquad H_m=A_m^\dagger A_m.
$$

The exact supplier is Toric Theorem 23.6: the nonzero polynomial $f$
in a domain makes $M_f$ injective, so $A_m$ is surjective and

$$
\ker H_m=\ker A_m=(f\mathcal P_{m-2})^\perp
\xrightarrow{\ q\mapsto[q]\ }(R_3)_m
$$

is an isomorphism. Its inverse chooses the orthogonal representative;
this choice depends on the stated inner product. The resulting dimension is

$$
N_m=\binom{m+4}{4}-\binom{m+2}{4}
=\frac{(m+1)(m+2)(2m+3)}6.
\tag{25.1}
$$

Here and below a binomial representing a negative-degree polynomial space
is zero. In particular the second term is zero for $m=0,1$.
A finite self-adjoint map $H_m:\mathcal P_m\to\mathcal P_m$ has index zero;
$A_m:\mathcal P_m\to\mathcal P_{m-2}$ has index $N_m$.
Neither assertion by itself is an Atiyah–Singer realization.
The application below adds an elliptic complex whose cohomology is this
same quotient, so its relation to the finite zero space is stronger than
an equality of two dimension formulas.

### 25.2 An ambient Dolbeault totalization with the negative odd layer

**Theorem 25.3 (Elliptic realization of the supplied finite quotient).**
On $X=\mathbb {CP}^{4}$ consider the holomorphic complex

$$
E^{-1}=\mathcal O(m-2)\xrightarrow{\ f\ }
E^0=\mathcal O(m),
\tag{25.2}
$$

in relation degrees $-1,0$. Its Dolbeault total complex is

$$
C^j=\Omega^{0,j}(\mathcal O(m))
\oplus\Omega^{0,j+1}(\mathcal O(m-2)),\qquad -1\le j\le4,
$$

where form spaces outside degrees $0,\ldots,4$ vanish, and

$$
\delta(\alpha,\beta)=
\bigl(\bar\partial\alpha+(-1)^{j+1}f\beta,
\bar\partial\beta\bigr).
\tag{25.3}
$$

Equip $X$ with Fubini–Study metric and the line bundles with smooth
Hermitian metrics. Take the direct sum metrics on total degrees and set

$$
D=\sqrt2(\delta+\delta^\dagger),\qquad
D^+:C^{\mathrm{even}}\longrightarrow C^{\mathrm{odd}}.
$$

Here $C^{-1}=\Omega^{0,0}(\mathcal O(m-2))$ is an odd summand.
Let $\mathscr E^\pm$ denote the smooth bundles of these even and odd
forms. The bounded realization

$$
D^+:H^1(X,\mathscr E^+)\longrightarrow L^2(X,\mathscr E^-)
\tag{25.4}
$$

is Fredholm, and its smooth kernels satisfy

$$
\ker D^+\simeq(R_3)_m\simeq\ker H_m,
\qquad \ker D^-=0,\qquad \operatorname{ind}D^+=N_m.
\tag{25.5}
$$

The first and last isomorphisms pass through the quotient; they identify
neither the two chosen inner products nor the positive spectra.

Proof. Holomorphicity of $f$ and the consecutive signs in (25.3) cancel
the two cross terms in $\delta^2$, while $\bar\partial^2=0$.
Multiplication by $f$ and its adjoint are of order zero. Consequently
the principal symbol of $D$ is the direct sum of the Dolbeault–Dirac
symbols on the two line bundles, with the parity on $E^{-1}$ reversed.
For a nonzero real cotangent vector $\xi$, exterior multiplication by
$\xi^{0,1}$ and contraction obey the Clifford anticommutator; their
square is a nonzero scalar multiple of $|\xi|^2$ times the identity.
Thus this symbol is invertible and $D^+$ is elliptic.

For the cohomology calculation, [Stacks Lemma 30.8.1, tag 01XT][PC25]
gives $H^0(\mathbb P^4,\mathcal O(d))=\mathcal P_d$ and
$H^q(\mathbb P^4,\mathcal O(d))=0$ for $q>0,d\ge-4$.
Both $d=m$ and $d=m-2$ lie in this range, including $-2,-1$.
These are initially algebraic cohomology groups. Serre's
[GAGA, §12, Théorème 1][GA25] identifies them with the analytic
cohomology of the corresponding holomorphic bundles on the same
projective complex variety. The analytic Dolbeault resolutions therefore
compute the hypercohomology of (25.2). Since the bundles are acyclic in
positive sheaf degree, its spectral sequence reduces to

$$
0\longrightarrow\mathcal P_{m-2}\xrightarrow{M_f}
\mathcal P_m\longrightarrow0.
$$

The supplied injectivity leaves only degree-zero cohomology $(R_3)_m$.
In particular there is no surviving degree $-1$ cohomology.

The classical Hodge theorem for elliptic complexes on compact manifolds,
as used in the analytic index framework of [Atiyah–Singer][AS25] and
[Freed, §§3.1–3.2 and Theorem 4.9][FR25], identifies each total cohomology class with its
unique harmonic representative. Indeed
$\langle D^2s,s\rangle=2(\|\delta s\|^2+\|\delta^\dagger s\|^2)$;
elliptic regularity makes weak kernel vectors smooth, and the orthogonal
Hodge decomposition identifies harmonic vectors with cohomology.
All cohomology is in even degree zero, which proves (25.5).
The compact elliptic estimate and Rellich compactness give Fredholmness
of (25.4). Its cokernel is the $L^2$ orthogonal complement of its range,
namely weak solutions of the formal adjoint equation $D^-s=0$;
regularity again makes these smooth. This is not a claim that the bounded
Hilbert adjoint of an $H^1\to L^2$ map is itself the same differential
operator between the same Hilbert spaces. The closed unbounded operator
on $L^2$ has Sobolev domain $H^1$ and formal adjoint $D^-$ on that domain.
These precise analytic choices supply the asserted index. $\square$

### 25.3 Todd integral, character and the nonsimple pyramid

**Theorem 25.4 (Topological and equivariant realization of the same count).**
Normalize $h=c_1(\mathcal O(1))$ by $\int_Xh^4=1$.
The symbol class of Theorem 25.3 is the Dolbeault symbol twisted by
$[\mathcal O(m)]-[\mathcal O(m-2)]$. Its index integral is

$$
\begin{aligned}
\operatorname{ind}D^+
&=\int_{\mathbb {CP}^{4}}
(e^{mh}-e^{(m-2)h})\left(\frac h{1-e^{-h}}\right)^5\\
&=\frac{m^3}{3}+\frac{3m^2}{2}+\frac{13m}{6}+1=N_m.
\end{aligned}
\tag{25.6}
$$

For the compact torus $T=(S^1)^3$, use the polynomial representation
convention in which $z_0,z_1,z_2,z_3,z_{13}$ have characters
$1,a,c,b,ab$. The bundle linearizations are chosen so that these are the
characters of $H^0(\mathcal O(1))$; this specifies the convention even if
a contragredient convention for geometric point coordinates is used.
Then the equivariant complex is

$$
\mathcal O(m-2)\otimes\mathbb C_{ab}
\xrightarrow{f}\mathcal O(m),
\tag{25.7}
$$

not the untwisted source with its original linearization. With invariant
metrics, its harmonic representation has graded character

$$
\sum_{m\ge0}\operatorname{ch}_T\ker D_m^+\,t^m
=\frac{1-abt^2}
{(1-t)(1-at)(1-bt)(1-ct)(1-abt)}.
\tag{25.8}
$$

Each legal occupancy character $a^Ub^Vc^W$ occurs once in degree $m$.

Proof. The Euler sequence for projective space gives
$\operatorname{Td}(TX)=(h/(1-e^{-h}))^5$ in cohomology.
Its required truncation is

$$
1+\frac52h+\frac{35}{12}h^2+\frac{25}{12}h^3+h^4.
$$

The classical Dolbeault index formula (Atiyah–Singer, with the complex
Riemann–Roch specialization described in Freed §§2.2, 3.1 and 4) is the
intermediate input in
(25.6). For direct coefficient evaluation, the $h^4$ coefficient of
$e^{dh}\operatorname{Td}(TX)$ is

$$
\frac{d^4}{24}+\frac{5d^3}{12}
+\frac{35d^2}{24}+\frac{25d}{12}+1
=\frac{(d+1)(d+2)(d+3)(d+4)}{24}.
$$

Subtract its values at $d=m$ and $m-2$ to obtain (25.6).
This polynomial calculation is compatible with the vanishing cases
$m=0,1$, rather than interpreting a negative polynomial degree as a
nonexistent negative replica space. The small values are

| $m$ | Candidate monomials $\dim\mathcal P_m$ | Relation-source monomials $\dim\mathcal P_{m-2}$ | $N_m$ |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 0 | 1 |
| 1 | 5 | 0 | 5 |
| 2 | 15 | 1 | 14 |
| 3 | 35 | 5 | 30 |
| 4 | 70 | 15 | 55 |
| 5 | 126 | 35 | 91 |

Both terms in $f$ have character $ab$, which proves equivariance with
exactly the twist (25.7). Average any Hermitian metrics over the compact
torus. The differential and its adjoint then intertwine the action;
harmonic representatives, the quotient map, and the finite Bargmann
orthogonal realization are equivariant. Injectivity of multiplication
gives the character difference and hence the product series (25.8).

For the multiplicity statement, put $R=m-W$. The monomials in the target
sector have exponent vectors

$$
\nu(k)=(R-U-V+k,U-k,W,V-k,k),
\quad \max(0,U+V-R)\le k\le\min(U,V).
\tag{25.9}
$$

If the interval has $D$ integer points, the relation source in (25.7)
has ordinary sector $(m-2,U-1,V-1,W)$. Its interval has $D-1$ points:
its lower bound is the same as in (25.9) and its upper bound is smaller
by one. If $D=1$ this source is empty, including the low-degree cases.
The difference of multiplicities is one. This is the sector calculation
of Toric §§23.5–23.7, now matched to the equivariant elliptic complex.

The legal sectors are precisely the lattice points of

$$
mP,\qquad
P=\{(x,y,z):0\le z\le1,\ 0\le x,y\le1-z\}.
$$

At each integer $W$, $U,V$ range independently from zero to $m-W$.
Thus their number is $\sum_{W=0}^m(m-W+1)^2=N_m$.
At the apex four facets meet in dimension three, so this pyramid is
nonsimple. No smooth Delzant conclusion is inferred from it.
The original $D$-dimensional sector remains a whole weight space under
torus averaging: an invariant density operator can retain all
within-sector coherence. The positive operator $H_m$ selects only its
one zero direction. Averaging and zero-energy selection are different
operations. $\square$

The toric Euler–Maclaurin literature, for example Cappell–Maxim–Schürmann–
Shaneson, [*Equivariant toric geometry and Euler-Maclaurin formulae — an
overview*][EM25], supplies general equivariant counting context.
The proof above uses the explicitly twisted polynomial sequence and
smooth ambient index; it does not apply a smooth toric formula directly
to the singular apex.

### 25.4 A smooth threefold and deformations that preserve only the index

**Theorem 25.5 (Smooth quadric realization and its limits).**
For real $\varepsilon\ne0$, set

$$
f_\varepsilon=f+\varepsilon z_2^2,\qquad
Q_\varepsilon=\{f_\varepsilon=0\}\subset\mathbb {CP}^{4},\qquad
L=\mathcal O(1)|_{Q_\varepsilon}.
$$

This is a smooth compact complex threefold. Its twisted Dolbeault index
for $L^m$, $m\ge0$, is also $N_m$. It uses the canonical complex
$\operatorname{Spin}^c$ structure and does not assume an ordinary spin
structure. This realization preserves the count, not the full original
three-weight symmetry or the original probability/phase control model.

Proof. The five gradient coordinates are
$(-z_{13},z_3,2\varepsilon z_2,z_1,-z_0)$, which cannot vanish at a
projective point. The normal bundle is $\mathcal O(2)|_{Q_\varepsilon}$.
The tangent-normal sequence and the Euler sequence give, through degree
three,

$$
c(TQ_\varepsilon)=\frac{(1+h)^5}{1+2h}
=1+3h+4h^2+2h^3,
$$

$$
\operatorname{Td}(TQ_\varepsilon)
=1+\frac32h+\frac{13}{12}h^2+\frac12h^3,
\qquad \int_{Q_\varepsilon}h^3=2.
$$

The classical complex index formula therefore yields

$$
\int_{Q_\varepsilon}e^{mh}\operatorname{Td}(TQ_\varepsilon)
=2\left(\frac{m^3}{6}+\frac{3m^2}{4}
+\frac{13m}{12}+\frac12\right)=N_m.
$$

Equivalently, the hypersurface sequence
$0\to\mathcal O(m-2)\to\mathcal O(m)\to\mathcal O_{Q_\varepsilon}(m)\to0$
and the same projective cohomology and GAGA inputs show vanishing of its
higher cohomology and give its $H^0$ dimension. The real dimension is six.
The lattice normalization gives
$\operatorname{Vol}(P)=\int_0^1(1-z)^2\,dz=1/3$, matching the leading
coefficient $2/3!$ of this degree-two threefold.
But $z_2^2$ has character $c^2$, not $ab$, so the full torus of (25.7)
does not preserve the smoothing; only a subgroup satisfying $c^2=ab$
can preserve the equation with its fixed coefficient. Neither smoothness
nor equality of the index supplies a control realization. $\square$

**Proposition 25.6 (The index distinguishes neither gaps nor individual
kernel dimensions under arbitrary fixed-symbol deformation).**
For the real family $f_s=sf$ and the associated total elliptic operators,

$$
\begin{array}{c|cc}
&\dim\ker D_s^+&\dim\ker D_s^-\\\hline
s\ne0&N_m&0\\
s=0&\binom{m+4}{4}&\binom{m+2}{4}
\end{array}
\tag{25.10}
$$

and the index is $N_m$ throughout. On the finite Bargmann carrier,
$H_{m,s}=s^2H_m$ for real $s$; for complex $s$ the coefficient is $|s|^2$.
For $\epsilon>0$, $H_m+\epsilon I$ has no zero modes and is a different
operator problem. For the unshifted finite pair one has, for every $t>0$,

$$
\operatorname{Tr}_{\mathcal P_m}e^{-tA_m^\dagger A_m}
-\operatorname{Tr}_{\mathcal P_{m-2}}e^{-tA_mA_m^\dagger}=N_m.
\tag{25.11}
$$

Proof. When $s\ne0$, multiplication has the same image and kernel as
before. When $s=0$, the total cohomology is the direct sum of
$H^0(\mathcal O(m))$ in even degree zero and
$H^0(\mathcal O(m-2))$ in odd degree minus one. Higher cohomology still
vanishes, giving (25.10). More generally the index of a continuous
elliptic family with fixed symbol is constant by the classical Fredholm
index theorem ([Freed §3.2][FR25]); compactness of the base and continuity as $H^1\to L^2$
maps are the hypotheses in use. This guarantees only the difference of
kernel dimensions. The scalar family already shows why gaps and kernel
sizes need not be invariant, and says nothing about preparation cost.

Taking finite adjoints proves the real and complex scaling formulas.
If $\lambda>0$ and $A_m^\dagger A_m v=\lambda v$, then $A_mv\ne0$ and
$A_mA_m^\dagger(A_mv)=\lambda A_mv$; the inverse on that eigenspace is
$A_m^\dagger/\lambda$. Thus the two positive spectra, with multiplicity,
pair and cancel in (25.11). Only the zero-space difference remains.
This is the finite instance of classical supersymmetric spectral pairing
and heat supertrace ([Freed §6.1][FR25]), used here for the specified
relation operator.
Strict positivity of $H_m+\epsilon I$ follows from
$\langle(H_m+\epsilon I)v,v\rangle\ge\epsilon\|v\|^2$.
No invariance assertion for that shift follows from (25.10). $\square$

### 25.5 Four positions: the counting bridge and the missing-map question

**Definition 25.7 (The adjacent-window comparison).**
Four consecutive positions give two overlapping length-three windows,
not two disjoint complete windows. Their legal modes are

$$
B_4=\{\varnothing,1,2,3,4,13,14,24\}.
$$

The occupancy semigroup records replica number $m$ and four totals
$c_i$, subject to $c_i\ge0$ and $c_i+c_{i+1}\le m$.
[Correlation, Theorems 26.4, 26.6 and 26.9][C25] supply, respectively,
feasible sectors, the Hibi relation kernel, and one zero ray per sector
for its explicitly declared exchange Hamiltonian. A count of these
sectors is not a count of ordered replica histories. In particular,
$L$ actual disjoint three-position windows with their inter-window guard
have $F_{3L+2}$ legal histories, not $5^L$.

**Proof input 25.8 (Four-position counting data for the elliptic comparison).**
Write $b=c_2,c=c_3$. Correlation Theorem 26.11 already identifies sector counts with its
zero-space dimension. For the four-position complex constructed below,
the required specialization at replica degree $m$ is

$$
\begin{aligned}
N_4(m)
&=\sum_{\substack{b,c\ge0\\b+c\le m}}(m-b+1)(m-c+1)\\
&=\frac{(m+1)(m+2)(5m^2+15m+12)}{24}.
\end{aligned}
\tag{25.12}
$$

Its Hilbert series is

$$
\sum_{m\ge0}N_4(m)t^m
=\frac{1+3t+t^2}{(1-t)^5}
=\frac{1-5t^2+5t^3-t^5}{(1-t)^8}.
\tag{25.13}
$$

Five quadrics in its relation ideal are

$$
\begin{aligned}
f_1&=z_1z_3-z_0z_{13},&f_2&=z_1z_4-z_0z_{14},\\
f_3&=z_2z_4-z_0z_{24},&f_4&=z_2z_{14}-z_1z_{24},\\
f_5&=z_4z_{13}-z_3z_{14}.
\end{aligned}
\tag{25.14}
$$

The relations

$$
z_4f_1-z_3f_2+z_0f_5=0,\qquad
z_2f_2-z_1f_3+z_0f_4=0
\tag{25.15}
$$

are two explicit syzygies. The alternating numerator (25.13), by itself,
does not construct a free resolution or prove exactness. Chapter 26
supplies the actual maps and exactness, thereby resolving that specific
missing-map question; (25.13) is not being presented as their proof.

Proof. Once $b,c$ are fixed with $b+c\le m$, the choices of $c_1$ and
$c_4$ are independently $0\le c_1\le m-b$ and $0\le c_4\le m-c$.
The cited feasibility theorem realizes every such sector. Put $n=m+1$
and $u=n-b$. Summing first over $c=0,\ldots,u-1$ gives

$$
\sum_{c=0}^{u-1}u(n-c)
=\frac12u^2(2n+1-u),
$$

so (25.12) is
$\frac12\sum_{u=1}^{m+1}u^2(2m+3-u)$.
Use $\sum_{u=1}^nu^2=n(n+1)(2n+1)/6$ and
$\sum_{u=1}^nu^3=n^2(n+1)^2/4$ and simplify to get the displayed
polynomial. Equivalently it equals
$\binom{m+4}{4}+3\binom{m+3}{4}+\binom{m+2}{4}$,
with negative spaces zero. Summing these binomial series gives the first
fraction in (25.13); multiplying its numerator by $(1-t)^3$ gives the
second. Expanding each side of (25.15) cancels all its monomials.
These computations exhibit counts and some dependencies, without
asserting that no other homology survives. $\square$

The comparison uses the same quotient at each stage: the finite
Bargmann orthogonal representative, the analytic harmonic representative
and the topological Euler characteristic. The first two depend on
metrics; the last retains only a signed dimension. The character twist
adds equivariance only for the compact torus and invariant metrics
specified in Theorem 25.4. The four-position construction below adds
relations between relations, which the one-relation quotient cannot supply.

[T25]: AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md
[C25]: AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md
[AS25]: https://celebratio.org/Atiyah_MF/article/40/
[FR25]: https://arxiv.org/html/2107.03557
[PC25]: https://stacks.math.columbia.edu/tag/01XT
[GA25]: https://www.numdam.org/item/AIF_1956__6__1_0.pdf
[EM25]: https://arxiv.org/abs/2403.19715

## 26. AURIC FIB-ATOM: exact four-position syzygies and the elliptic index

### 26.1 Integral normal form and the five particular relations

**Definition 26.1 (Coefficient rings and the forgetful map).**
Let

$$
S_{\mathbb Z}=\mathbb Z[z_0,z_1,z_2,z_3,z_4,z_{13},z_{14},z_{24}],
\quad\deg z_I=1,\qquad
\varphi(z_I)=t_0\prod_{i\in I}t_i.
$$

The target is $\mathbb Z[t_0,t_1,t_2,t_3,t_4]$.
Let $f=(f_1,\ldots,f_5)^{\mathsf T}$ be (25.14) and $I=(f_1,\ldots,f_5)$.
All five polynomials have integer coefficients. Write
$R_{4,\mathbb Z}=\operatorname{im}\varphi$;
for a field $K$ use $S_K$ and $R_{4,K}$ for the same presentation over $K$.
The map remembers only the replica number and occupancy totals, not an
ordering of replicas or a native processing history. In particular it
forgets the ordered choices even when each individual row is a legal
four-position word; the variable $z_I$ names that entire row.

**Theorem 26.2 (The integral relation kernel used by the explicit complex).**
One has $\ker\varphi=I$ over $\mathbb Z$, and the identical generating
list describes the kernel over every field. Its sector normal forms
have one basis monomial for every feasible $(m,c_1,c_2,c_3,c_4)$.

Proof and supplier correspondence. Correlation §§26.1–26.2 already
prove the general field-valued Hibi kernel and its finite sorting
normal form. Here their $n$ is four, their $u$ is the incidence vector
of $I\in B_4$, and their alternating complement is

$$
y=(u_1,1-u_2,u_3,1-u_4),\qquad y_1\le y_2\ge y_3\le y_4.
$$

The corresponding distributive lattice of eight binary vectors is
closed under coordinatewise minimum and maximum. The complete list of
incomparable unordered mode pairs is

| Pair | Meet and join, in mode names | Join–meet difference |
| --- | --- | --- |
| $(0,14)$ | $(4,1)$ | $-f_2$ |
| $(1,3)$ | $(0,13)$ | $f_1$ |
| $(2,4)$ | $(24,0)$ | $f_3$ |
| $(2,14)$ | $(24,1)$ | $f_4$ |
| $(3,14)$ | $(4,13)$ | $-f_5$ |

The pair order in the middle column names meet first and join second
in the $y$ order. This explicit list and its signs connect the existing
Hibi supplier to exactly (25.14), rather than to an unnamed isomorphic
ideal. For instance the $y$ vectors of modes $0,14$ are $0101,1100$;
their meet $0100$ is mode $4$ and join $1101$ is mode $1$.

For the integral extension needed here, the supplier's sorting proof
uses no division. For two incomparable rows with $a>0$ one-coordinates
exclusive to one and $b>0$ exclusive to the other, replacing them by
meet and join increases
$E=\sum_{\text{rows }y}(\sum_i y_i)^2$ by $2ab$.
For $m$ rows, $0\le E\le16m$, so sorting terminates.
The terminal chain is uniquely determined by its column sums: in each
column the zeros precede the ones and the number of ones is fixed.
Those column sums are $c_i$ for odd $i$ and $m-c_i$ for even $i$.
Thus monomials of equal image differ, modulo the five listed quadrics,
by zero: both reduce to the same chain monomial.

For a polynomial in the kernel, group terms by their image monomial.
The target is free over $\mathbb Z$ on monomials, so the coefficient sum
in each group is zero. Subtract that group's common normal monomial
from each term, using the sorting congruences; its residual coefficient
is zero. This proves the reverse inclusion over $\mathbb Z$.
The same argument over a field proves the field claim directly, without
an unsupported assertion that arbitrary base change preserves exactness.
It also proves independence of the sector normal forms. The classical
join–meet interpretation is Hibi theory, with the exact alternating
complement and Laurent monomial correspondence supplied in Correlation
Theorem 26.6; it is an intermediate input to the integral complex here.
$\square$

### 26.2 Pfaffians, all five syzygy columns and integral exactness

**Theorem 26.3 (An exact resolution with the specified integer maps).**
Put

$$
M=\begin{pmatrix}
0&-z_{24}&z_{14}&-z_4&0\\
z_{24}&0&-z_{13}&z_3&z_2\\
-z_{14}&z_{13}&0&0&-z_1\\
z_4&-z_3&0&0&z_0\\
0&-z_2&z_1&-z_0&0
\end{pmatrix}.
\tag{26.1}
$$

With $S(-a)_m=S_{m-a}$, the sequence

$$
0\longrightarrow S_{\mathbb Z}(-5)
\xrightarrow{f} S_{\mathbb Z}(-3)^5
\xrightarrow{M} S_{\mathbb Z}(-2)^5
\xrightarrow{f^{\mathsf T}} S_{\mathbb Z}
\longrightarrow R_{4,\mathbb Z}\longrightarrow0
\tag{26.2}
$$

is exact. The same matrices give an exact minimal graded resolution over
every field, including characteristic two.

Proof. For a four-by-four alternating matrix whose upper entries are
$a,b,c,d,e,f$ in lexicographic order, its Pfaffian is $af-be+cd$.
Deleting row and column $i$ in (26.1) gives

$$
f_i=(-1)^{i+1}\operatorname{Pf}(M_{\widehat i}),
\qquad\det M_{\widehat i}=f_i^2.
\tag{26.3}
$$

For clarity the five Pfaffians, before the alternating sign, are
$f_1,-f_2,f_3,-f_4,f_5$. Expanding the displayed four-by-four formula
proves these identities integrally. The five columns of $M$ express
all of the following particular syzygies:

$$
\begin{aligned}
z_{24}f_2-z_{14}f_3+z_4f_4&=0,\\
-z_{24}f_1+z_{13}f_3-z_3f_4-z_2f_5&=0,\\
z_{14}f_1-z_{13}f_2+z_1f_5&=0,\\
-z_4f_1+z_3f_2-z_0f_5&=0,\\
z_2f_2-z_1f_3+z_0f_4&=0.
\end{aligned}
\tag{26.4}
$$

Each is verified by replacing its $f_i$ by (25.14): every cubic
monomial occurs with opposite coefficients. Thus $f^{\mathsf T}M=0$;
skew symmetry gives $Mf=0$ as well. The fourth equation is the negative
of the first relation in (25.15), and the fifth is the second one.
All arrows have degree zero with the shifts in (26.2): their entries
have degrees two, one and two from right to left.

The classical exactness input is Buchsbaum–Eisenbud,
[*What Makes a Complex Exact?*, §1, theorem and Corollary 1][BE73].
Its local version is [Stacks Proposition 10.102.9, tag 00N1][AC26]
in section 00MR. For a finite free complex, with the expected ranks
$r_i$ and ranks of the modules $r_i+r_{i+1}$, it suffices that the
$r_i$-minor ideals of the $i$th maps contain regular sequences of
length $i$, with the standard unit-ideal exception. We verify this
for the maps from the right, whose ranks are $1,4,1$.

The fraction field calculation works over $\mathbb Z$ and over every
field of coefficients. The nonzero vector $f$ is in the kernel of $M$,
so its rank is at most four; the nonzero minor $f_1^2$ makes the rank
four. The row and column $f$ have rank one. This supplies the rank
identities $1=1$, $5=1+4$, $5=4+1$, $1=1$.

Here is an integral regular-sequence check, rather than a grade claim
inferred from the Hilbert numerator. Order monomials by positive weights

$$
(z_0,z_1,z_2,z_3,z_4,z_{13},z_{14},z_{24})
\longmapsto(1,5,5,5,5,1,12,1)
$$

and break ties by any fixed monomial order. The leading monomials of
$f_1,f_2,f_3$ are respectively

$$
z_1z_3,\quad z_0z_{14},\quad z_2z_4,
$$

with coefficients $1,-1,1$; they are pairwise coprime.
After multiplying $f_2$ by minus one these polynomials are monic.
For completeness, monic polynomials with pairwise coprime leading
monomials form a Gröbner basis over $\mathbb Z$: the two leading terms
in each S-polynomial cancel, and reducing the remaining two terms by
the two original monic polynomials yields zero. Division therefore has
a remainder supported on monomials divisible by none of those leading
monomials, with no division of integer coefficients.

Apply this successively. If $g_jq$ lies in the ideal generated by the
preceding $g_i$, reduce $q$ by those preceding monic polynomials to a
remainder $r$. If $r\ne0$, then
$\operatorname{lm}(g_jr)=\operatorname{lm}(g_j)\operatorname{lm}(r)$.
Any preceding leading monomial dividing this product would, by
coprimality, divide $\operatorname{lm}(r)$, a contradiction.
The coefficient ring is a domain, so that leading coefficient cannot
vanish. Hence $r=0$ and multiplication by $g_j$ is injective on the
preceding quotient. The ideals are proper, since their leading
monomials have positive degree. This proves that $f_1,f_2,f_3$ is a
regular sequence. The same argument with squared leading monomials
proves that $f_1^2,f_2^2$ is a regular sequence.

Consequently the minor ideals needed for (26.2) have the witnesses

$$
\begin{aligned}
I_1(f^{\mathsf T})&\supseteq(f_1),\\
I_4(M)&\supseteq(f_1^2,f_2^2),\\
I_1(f)&\supseteq(f_1,f_2,f_3).
\end{aligned}
\tag{26.5}
$$

The polynomial ring over $\mathbb Z$ is Noetherian. Localize at an
arbitrary prime. If a minor ideal becomes the unit ideal its grade
condition is automatic; otherwise the displayed contained regular
sequence localizes to the required regular sequence. The local
acyclicity criterion applies, and exactness at every prime implies
exactness of the original finitely generated modules. The cokernel on
the right is $R_{4,\mathbb Z}$ by Theorem 26.2. Injectivity on the left
also follows immediately from the domain property and $f\ne0$.

Over any field repeat the same monic division, minor and localization
argument. No step divides by two; in characteristic two (26.1) remains
alternating, the integral identities reduce correctly, and the same
nonzero leading monomials remain. This proves exactness directly there.
Every matrix entry has positive ordinary degree, so tensoring with the
residue field at the homogeneous maximal ideal makes every differential
zero. This is precisely minimality of the graded free resolution.
The maps are the application of the classical odd alternating
Pfaffian construction, not a new general Pfaffian theorem. $\square$

### 26.3 Counts, the smooth ambient complex and its kernels

**Proposition 26.4 (Exact homological accounting for the four-mode-position
application).** Over $\mathbb C$, the degree $m$ strand of (26.2) yields

$$
N_4(m)=\binom{m+7}{7}-5\binom{m+5}{7}
+5\binom{m+4}{7}-\binom{m+2}{7}.
\tag{26.6}
$$

It equals (25.12), and its series is (25.13).
The degree-by-degree accounting for $m=2,3,4,5$ is

| $m$ | Candidates $S_m$ | Relation sources $5S_{m-2}$ | First syzygies $5S_{m-3}$ | Last source $S_{m-5}$ | Quotient |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 36 | 5 | 0 | 0 | 31 |
| 3 | 120 | 40 | 5 | 0 | 85 |
| 4 | 330 | 180 | 40 | 0 | 190 |
| 5 | 792 | 600 | 180 | 1 | 371 |

Proof. Exactness gives the alternating dimension formula. The ordinary
Hilbert series of $S(-a)$ is $t^a/(1-t)^8$, so (26.2) gives (25.13).
Its reduced form is the series already obtained from the independent
occupancy sum. Each weight has dimension one by the integral chain
normal form in Theorem 26.2, which is why summing sectors counts this
quotient. The table substitutes the dimensions of eight-variable
homogeneous polynomials and uses zero for negative degrees.
This supplies the homological justification that the numerator alone
in §25.5 did not supply. $\square$

**Theorem 26.5 (The four-position elliptic complex and its index).**
On smooth $X_4=\mathbb {CP}^{7}$ sheafify (26.2), twist by $m\ge0$, and
place its bundles in cochain degrees $-3,-2,-1,0$:

$$
\mathcal O(m-5)\xrightarrow{f}
\mathcal O(m-3)^5\xrightarrow{M}
\mathcal O(m-2)^5\xrightarrow{f^{\mathsf T}}\mathcal O(m).
\tag{26.7}
$$

For $E^{-i}=\widetilde F_i(m)$ form the total Dolbeault complex with
total degree $j=q-i$ and differential

$$
\delta=\bar\partial+(-1)^q d_{\rm rel}
\quad\hbox{on }\Omega^{0,q}(E^{-i}).
\tag{26.8}
$$

Choose smooth Hermitian metrics and put $D=\sqrt2(\delta+\delta^\dagger)$,
with even-to-odd part $D^+$. Its $H^1\to L^2$ Sobolev realization is
Fredholm, and

$$
\ker D^+\simeq(R_{4,\mathbb C})_m,\qquad
\ker D^-=0,\qquad\operatorname{ind}D^+=N_4(m).
\tag{26.9}
$$

With $\int_{\mathbb {CP}^{7}}h^7=1$, the index is

$$
\int_{\mathbb {CP}^{7}}e^{mh}
(1-5e^{-2h}+5e^{-3h}-e^{-5h})
\left(\frac h{1-e^{-h}}\right)^8.
\tag{26.10}
$$

Proof. Holomorphicity makes $\bar\partial$ commute with $d_{\rm rel}$
before the totalization sign, and (26.2) gives $d_{\rm rel}^2=0$.
The signs in (26.8) make the cross terms cancel, hence $\delta^2=0$.
All relation arrows are order zero on the base; the principal symbol
is a direct sum of Dolbeault symbols, with parity reversed when $i$ is
odd. In particular total degrees $-3$ and $-1$ are retained as odd,
not discarded. The symbol is invertible away from the zero cotangent
section, as in Theorem 25.3. The underlying projective relation variety
may be singular; the differential operator is on smooth $X_4$.

The smallest bundle twist is $m-5\ge-5$. Stacks 01XT on $\mathbb P^7$
vanishes in positive sheaf degrees for every twist at least $-7$.
After the same Serre GAGA comparison, the Dolbeault hypercohomology is
therefore computed by the degree $m$ strand of (26.2). Its only
cohomology is the quotient in degree zero, by actual exactness.
The compact elliptic Hodge decomposition gives (26.9). The Sobolev
domain, weak formal-adjoint description of the cokernel and elliptic
regularity are exactly those in (25.4), with the present finite bundle
sum on $X_4$; they are not a bounded-adjoint identification.

The even relation bundles are $\mathcal O(m)$ and
$\mathcal O(m-3)^5$, and the odd ones are
$\mathcal O(m-2)^5$ and $\mathcal O(m-5)$.
The classical Dolbeault index formula on the smooth ambient space
therefore gives (26.10), equal to the alternating projective Euler
characteristics in (26.6). Directly,

$$
1-5e^{-2h}+5e^{-3h}-e^{-5h}=5h^3+O(h^4).
$$

The constant, linear and quadratic coefficients vanish; the cubic
coefficient is $40/6-135/6+125/6=5$.
This explains why the count has degree four despite the ambient
projective dimension seven. It does not erase the higher-degree
terms or the relation maps. $\square$

**Proposition 26.6 (Finite zero spaces and a wrong-map comparison).**
On the Bargmann degree $m$ space in eight variables define

$$
H_{4,m}=\sum_{j=1}^5 f_j(\partial)^\dagger f_j(\partial).
$$

Then $\ker H_{4,m}=I_m^\perp\simeq(R_{4,\mathbb C})_m$.
This identification and (26.9) use the common quotient, not equality of
metrics or complete spectra. At $m=3$, replacing all relation arrows
in (26.7) by zero leaves its principal symbol and index $85$ unchanged,
but its positive kernel dimension becomes $125$ and its negative kernel
dimension becomes $40$, instead of $85$ and zero.

Proof. The quadratic form of the sum is
$\sum_j\|f_j(\partial)v\|^2$, so its kernel is the intersection of the
five annihilation kernels. The finite adjoint of $f_j(\partial)$ is
multiplication by $f_j$, whose image is $f_jS_{m-2}$.
The orthogonal complement of their sum is exactly $I_m^\perp$.
Orthogonal projection gives its quotient isomorphism, as in §25.1.
The self-adjoint finite map $H_{4,m}$ still has Fredholm index zero.

If all relation arrows vanish, the total cohomology is the direct sum
of the bundles' Dolbeault cohomologies. At $m=3$ its even spaces are
$H^0(\mathcal O(3))$ of dimension $120$ and five copies of
$H^0(\mathcal O(0))$, giving $125$. Its odd spaces are five copies of
$H^0(\mathcal O(1))$ of total dimension $40$, and
$H^0(\mathcal O(-2))=0$. Higher cohomology vanishes. Thus the index is
still $125-40=85$. Atiyah–Singer alone controls this difference;
exactness and vanishing were essential to the particular zero spaces
in (26.9). $\square$

[BE73]: https://eisenbud.github.io/papers/pdfs/1973-002.pdf
[AC26]: https://stacks.math.columbia.edu/tag/00N1

## 27. Path-semigroup duality as a supplier for all-length elliptic realizations

### 27.1 The exact lattice and the interior shift

**Definition 27.1 (Positions, replicas and the normal semigroup).**
For $n\ge2$ positions, set

$$
\begin{aligned}
B_n&=\{I\subseteq[n]:I\text{ contains no adjacent pair}\},\\
P_n&=\{x\in\mathbb R^n:x_i\ge0,\ x_i+x_{i+1}\le1\ (1\le i<n)\},\\
\mathcal S_n&=\{(m,c)\in\mathbb Z_{\ge0}^{n+1}:
 c_i+c_{i+1}\le m\ (1\le i<n)\},\\
R_n&=\mathbb C[\mathcal S_n].
\end{aligned}
\tag{27.1}
$$

The real cone is $C_n=\{(m,c):m\ge0,\ c\in mP_n\}$.
Every variable $z_I$ in
$S_n=\mathbb C[z_I:I\in B_n]$ has multidegree
$a_I=(1,\mathbf1_I)$ and maps to the corresponding semigroup monomial.
The ordinary degree is its first coordinate. The number of variables is
$D_n=|B_n|=F_{n+2}$, where $F_0=0,F_1=1$.
This presentation is the general Hibi history supplier of Correlation
chapter 26 with its $K=\mathbb C$; $n$ is the number of positions and
$m$ the number of replicas. Neither is a time-step count.

The literature input for the following application is the path case of
Jiang–Yang–Zhong, [*Transfer Matrices and Ehrhart Theory for Path and
Cyclic Block Polytopes*, Theorem 1.6, Remark 1.7 and §3][PA27].
Its block parameter is $a=1$, its block count is our $n$, and its
dilation variable is our $m$. Its codegree, interior translation,
reciprocity and palindromy are used as existing path-polytope results,
not claimed as new standalone theorems. The following verification fixes
the exact lattice and shift required by the resolution and index.

**Theorem 27.2 (The path supplier determines the duality shift of this
mode algebra).** For (27.1), the cone interior lattice points are

$$
\operatorname{int}(C_n)\cap\mathbb Z^{n+1}
=(3,\mathbf1)+\mathcal S_n.
\tag{27.2}
$$

The algebra $R_n$ is normal, Cohen–Macaulay and Gorenstein, with
multigraded canonical module

$$
\omega_{R_n}\simeq R_n(-(3,\mathbf1)).
\tag{27.3}
$$

Consequently, with $c_n=D_n-n-1$ and

$$
\Sigma_n=\sum_{I\in B_n}a_I,\qquad
\Theta_n=\Sigma_n-(3,\mathbf1),
\tag{27.4}
$$

the minimal multigraded free resolution $F_\bullet$ of $R_n$ over $S_n$
has length $c_n$, last module $S_n(-\Theta_n)$, and duality

$$
F_i\simeq\operatorname{Hom}_{S_n}(F_{c_n-i},S_n)(-\Theta_n),
\qquad
\beta_{i,\gamma}=\beta_{c_n-i,\Theta_n-\gamma}.
\tag{27.5}
$$

For $n=2$ this means $c_n=0$, $\Theta_n=0$ and $F_0=S_n$;
there is no nontrivial last relation module in that case.

Proof with the classical inputs kept explicit. For $n\ge2$ every
coordinate has a neighbor, so $0\le x_i\le1$ follows from (27.1).
The polytope is bounded and full dimensional: the constant vector with
all coordinates $1/4$ satisfies every displayed inequality strictly.
Its vertices are integral. One way to see this is the supplied
alternating complement to the fence order polytope: it is an affine
lattice isomorphism, and the latter is the convex hull of its binary
filters. This is Stanley's [*Two Poset Polytopes*, Corollary 1.3, Theorem 2.3 and
Example 4.3][ST27], with the same mapping as Correlation Proposition 26.2.
Each $x_i=0$ is a facet, by making the other coordinates positive and
small. Each $x_i+x_{i+1}=1$ is a facet, by taking those two coordinates
$1/2$, all other coordinates small and positive, and varying in that
hyperplane. These are therefore exactly the listed facets; no separate
upper-coordinate facet is needed.

For an integer $m>0$, strict inequalities for $mP_n$ are

$$
c_i\ge1,\qquad c_i+c_{i+1}\le m-1.
$$

Putting $c=\mathbf1+b$ transforms these exactly into
$b_i\ge0$ and $b_i+b_{i+1}\le m-3$.
There are no such points for $m=1,2$; at $m=3$ the only one is
$c=\mathbf1$, because every nonnegative $b_i$ has a neighbor and each
neighboring sum must be zero. The same inequalities in the full cone
give (27.2), including the degree-zero semigroup element on the right.
This is the precise path-supplier interior translation in our variables.

For normality, first prove generation in degree one. To represent
$(m,c)$ choose $c_1$ of $m$ rows for the first column; for each subsequent
column choose $c_i$ rows outside those occupied in the preceding column.
The inequality $c_{i-1}+c_i\le m$ makes this possible. Each resulting row
is in $B_n$, and their sum is $c$. The zero mode and all singleton modes
show that the generated group is all $\mathbb Z^{n+1}$: subtract the
zero-mode vector from a singleton vector to obtain $(0,e_i)$.
The nonnegative real cone generated by the modes is $C_n$, and
$\mathcal S_n=C_n\cap\mathbb Z^{n+1}$; the integer decomposition just
proved supplies equality, not merely containment. This is a saturated
affine semigroup in its full group lattice, hence its algebra is normal.

Hochster's theorem for normal affine semigroup algebras supplies
Cohen–Macaulayness. The Danilov–Stanley canonical-module formula supplies
the ideal generated by monomials whose exponents are interior lattice
points. A precise source for both inputs in this setting is
Brennan–Dupont–Villarreal,
[*Duality, a-invariants and canonical modules of rings arising from
linear optimization problems*, equations (1.2), (3.2) and §3][CA27].
Their semigroup algebra $K[F]$ is the present $\mathbb C[\mathcal S_n]$,
their cone is $C_n$, and the integer group has just been checked to be
full. Formula (27.2) makes this canonical ideal the principal monomial
ideal of degree $(3,\mathbf1)$, proving (27.3) and Gorensteinness.
These general commutative-algebra assertions are cited intermediate
inputs to the explicit mode-degree correspondence.

The semigroup has group rank $n+1$, so $\dim R_n=n+1$.
The regular polynomial ring $S_n$ has dimension $D_n$.
Auslander–Buchsbaum, in [Stacks Proposition 10.111.1, section 090U][AB27],
applied at the homogeneous maximal ideal gives projective dimension
$c_n=D_n-n-1$, since the depth of the Cohen–Macaulay module is $n+1$.
Minimal multigraded resolutions exist by successively choosing
homogeneous minimal generators of kernels; Hilbert syzygy ensures
termination. This supplies a constructive algebraic rule, not an
explicit list of all the matrices for all $n$.

To fix the shift in duality, the polynomial canonical module is
$\omega_{S_n}=S_n(-\Sigma_n)$, and graded canonical duality says

$$
\operatorname{Ext}^{c_n}_{S_n}(R_n,S_n(-\Sigma_n))
\simeq\omega_{R_n}=R_n(-(3,\mathbf1)),
$$

with the other Ext degrees zero for this Cohen–Macaulay module.
Thus $\operatorname{Ext}^{c_n}_{S_n}(R_n,S_n)
\simeq R_n(\Theta_n)$.
Dualize the minimal resolution and reverse its order, then shift by
$-\Theta_n$. This gives another minimal resolution of $R_n$.
Uniqueness of minimal graded resolutions gives (27.5); in particular
the dual of $F_0=S_n$ is the stated last rank-one module.
This is the standard canonical-Ext proof of Gorenstein resolution
duality, as in Buchsbaum–Eisenbud's
[*Algebra structures for finite free resolutions, and some structure
theorems for ideals of codimension 3*][BE77], Theorem 1.5 and the
codimension-three specialization in Theorem 2.1. Only the resolution
and duality content is used; no uniqueness assertion requiring two to
be invertible is imported into Theorem 26.3.

For $n=2$, the modes $0,1,2$ have linearly independent augmented
vectors, so the presentation is polynomial. Directly
$\Sigma_2=(3,1,1)$ and $\Theta_2=0$, agreeing with the zero-length
interpretation. $\square$

The restriction $n\ge2$ is essential for this definition of $P_n$.
For $n=1$ the inequalities as written give an unbounded half-line.
If one separately defines the bounded interval $0\le x_1\le1$, its
codegree is two, its interior shift is $(2,1)$, and its two-mode algebra
is polynomial. It is not an instance of (27.2) with codegree three.

### 27.2 Explicit multidegrees, palindromy and negative evaluation

**Proposition 27.3 (The duality degrees of the concrete path modes).**
The degree in (27.4) is

$$
\Theta_n=\bigl(F_{n+2}-3;
F_iF_{n-i+1}-1\ (1\le i\le n)\bigr).
\tag{27.6}
$$

The following tuples list $(D_n,c_n,\Theta_{n,0};\Theta_{n,\rm occ})$:

$$
\begin{array}{c|c}
n&\text{tuple}\\\hline
3&(5,1,2;1,0,1)\\
4&(8,3,5;2,1,1,2)\\
6&(21,14,18;7,4,5,5,4,7).
\end{array}
$$

For $n=4$, the matrix (26.1) respects exactly this multigrading.
The duality is a statement about algebraic modules; it is not Hermitian
self-duality of quantum states or a claim about time evolution.

Proof. The usual independent-set recursion gives
$D_n=D_{n-1}+D_{n-2}$, with $D_0=1,D_1=2$.
A mode containing position $i$ cannot contain its neighbors.
Its independent remaining left and right segments have lengths
$i-2$ and $n-i-1$. Their counts are $F_i$ and $F_{n-i+1}$.
At an endpoint the absent segment has count one, agreeing with $F_1=1$;
this also handles the apparent length minus one in that notation.
Multiplying gives the number of mode variables whose $i$th occupancy
degree is one. Subtracting $(3,\mathbf1)$ proves (27.6).

For the four-position complex the five quadratic multidegrees are

$$
\begin{aligned}
b_1&=(2;1,0,1,0),&b_2&=(2;1,0,0,1),\\
b_3&=(2;0,1,0,1),&b_4&=(2;1,1,0,1),\\
b_5&=(2;1,0,1,1),&\Theta_4&=(5;2,1,1,2).
\end{aligned}
$$

Thus $F_1=\bigoplus_iS_4(-b_i)$ and
$F_2=\bigoplus_jS_4(-(\Theta_4-b_j))$.
For every nonzero matrix entry, its degree must be
$\Theta_4-b_i-b_j$. The eight upper-triangular nonzero entries have
indices $12,13,14,23,24,25,35,45$ with respectively
$z_{24},z_{14},z_4,z_{13},z_3,z_2,z_1,z_0$ and their displayed signs. Substitution of the five $b_i$ verifies
each equality. The initial $f$ column maps degree $\Theta_4$ to degree
$\Theta_4-b_i$ by an entry of degree $b_i$, and the last row maps degree
$b_i$ to zero by the same entry. Ordinary degrees recover $5,3,2,0$.
For $n=6$, fourteen is the projective dimension of a resolution with
ranks determined by this algebra, not fourteen temporal operations.
$\square$

**Definition 27.4 (Ehrhart data supplied to the ambient index).**
Let $N_n(m)=\dim(R_n)_m=|mP_n\cap\mathbb Z^n|$ for $m\ge0$.
The numerator in

$$
\sum_{m\ge0}N_n(m)t^m=\frac{h_n^*(t)}{(1-t)^{n+1}}
$$

has degree $n-2$ and is palindromic:

$$
h_n^*(t)=t^{n-2}h_n^*(t^{-1}).
\tag{27.7}
$$

For the small path lengths,

$$
\begin{aligned}
h_3^*&=1+t,\\
h_4^*&=1+3t+t^2,\\
h_5^*&=1+7t+7t^2+t^3,\\
h_6^*&=1+14t+31t^2+14t^3+t^4.
\end{aligned}
\tag{27.8}
$$

The Ehrhart polynomial extension satisfies

$$
N_n(-m)=(-1)^nN_n(m-3).
\tag{27.9}
$$

This evaluates a polynomial at negative integers; it does not count
negative replicas.

Supplier correspondence for Theorem 27.5. The lattice polytope hypotheses
were verified above. Theorem 1.6 and §3 of [Jiang–Yang–Zhong][PA27], with
$a=1$, supply codegree three, degree $n-2$, reciprocity and palindromy.
In the present coordinates their interior count is exactly
$|\operatorname{int}(mP_n)\cap\mathbb Z^n|=N_n(m-3)$ for $m\ge3$,
by (27.2). Ehrhart reciprocity identifies the left count with
$(-1)^nN_n(-m)$; equality at infinitely many positive integers proves
(27.9) as a polynomial identity. Equivalently the canonical shift of
ordinary degree three makes the Hilbert numerator symmetric of degree
$(n+1)-3$. This is the same supplied theorem in the algebra used here.

For completeness the small numerators in (27.8) can be obtained without
unspecified tabulated data. Let $a_1^{(m)}(j)=1$ for $0\le j\le m$ and

$$
a_{r+1}^{(m)}(j)=\sum_{k=0}^{m-j}a_r^{(m)}(k),\qquad
N_r(m)=\sum_{j=0}^ma_r^{(m)}(j).
\tag{27.10}
$$

These formulas count legal occupancy columns by their last value.
They give $N_3(1)=5,N_4(1)=8,N_5(1)=13,N_6(1)=21$;
for $m=2$, the three-coordinate recurrence gives, through lengths one
to six, the vectors
$(1,1,1),(3,2,1),(6,5,3),(14,11,6),(31,25,14),(70,56,31)$,
whose last two sums give $N_5(2)=70$ and $N_6(2)=157$.
The coefficient identity

$$
h_{n,j}^*=\sum_{q=0}^j(-1)^q\binom{n+1}{q}N_n(j-q)
$$

gives $h_{n,1}^*=D_n-(n+1)$, namely $1,3,7,14$.
For $n=6$, $h_{6,2}^*=157-7\cdot21+21=31$.
Degree and palindromy determine the remaining coefficients for
$n=3,4,5,6$, giving (27.8). The recurrence specializes the supplier to the concrete mode counts
needed by Theorem 27.5. Codegree, reciprocity and palindromy here are
intermediate literature inputs, not additional standalone path theorems.

### 27.3 General ambient realization and the reduced integral

**Theorem 27.5 (All-position elliptic quotient realization from a minimal
resolution).** Fix $n\ge2$ and $m\ge0$. Choose a minimal multigraded
resolution of $R_n$ over $S_n$ and forget only its occupancy grading.
Write its summands as $S_n(-j)^{\beta_{i,j}}$ and set
$E^{-i}=\widetilde F_i(m)$ on $X_n=\mathbb {CP}^{D_n-1}$.
Totalize its Dolbeault resolution with the sign (26.8), include all
negative total degrees, and use any smooth Hermitian metrics.
Then $D^+:H^1(X_n,\mathscr E^+)\to L^2(X_n,\mathscr E^-)$ is elliptic
Fredholm and

$$
\ker D^+\simeq(R_n)_m,\qquad \ker D^-=0,
\qquad\operatorname{ind}D^+=N_n(m).
\tag{27.11}
$$

Let

$$
B_n(t)=\sum_{i,j}(-1)^i\beta_{i,j}t^j
=(1-t)^{c_n}h_n^*(t).
\tag{27.12}
$$

The index has the two equal coefficient expressions

$$
\begin{aligned}
N_n(m)
&=[h^{D_n-1}]\ e^{mh}B_n(e^{-h})
 \left(\frac h{1-e^{-h}}\right)^{D_n}\\
&=[h^n]\ e^{mh}h_n^*(e^{-h})
 \left(\frac h{1-e^{-h}}\right)^{n+1}.
\end{aligned}
\tag{27.13}
$$

Proof. All ordinary shifts in a minimal resolution are nonnegative:
start with $F_0=S_n$, and choose homogeneous generators of each kernel
inside the preceding positively graded free module. A nonzero
homogeneous element cannot have negative ordinary degree.
By (27.5), each occurring shift $j$ pairs with
$D_n-3-j$, which is also nonnegative. Therefore

$$
0\le j\le D_n-3.
$$

Every line-bundle twist in the sheaf complex is thus at least
$m-(D_n-3)\ge-(D_n-3)>-D_n$.
On $\mathbb P^{D_n-1}$, Stacks 01XT therefore gives vanishing in all
positive sheaf degrees. Serre GAGA and the Dolbeault resolution identify
the analytic total cohomology with the degree $m$ strand of the chosen
exact resolution. Its sole cohomology is $(R_n)_m$ in degree zero.
The principal symbol is the parity-shifted sum of Dolbeault symbols;
all relation maps are order zero. Compact elliptic Hodge theory and the
same Sobolev/formal-adjoint regularity argument as in Theorem 25.3 prove
(27.11). For $n=2$ the complex consists just of $\mathcal O(m)$ on
$\mathbb P^2$, exactly as the trivial resolution requires.

The Hilbert-series alternating sum of the resolution is
$B_n(t)/(1-t)^{D_n}$; comparison with the supplied Ehrhart series proves
(27.12). The first expression in (27.13) is the classical index formula
for its virtual sum of line bundles on $X_n$.
Substituting (27.12) and using $D_n-c_n=n+1$ gives formally

$$
(1-e^{-h})^{c_n}\left(\frac h{1-e^{-h}}\right)^{D_n}
=h^{c_n}\left(\frac h{1-e^{-h}}\right)^{n+1}.
$$

Since $D_n-1-c_n=n$, coefficient extraction proves the second
expression. All series are used only through the finite cohomological
degree in question; the factor $h/(1-e^{-h})$ has a regular formal
power series at zero. This equality neither identifies $X_n$ with
$\mathbb P^n$ nor compresses its relation matrices or state spaces to
$n$ dimensions. $\square$

The specified construction gives actual integer maps in the four-position
case and an existence construction by minimal homogeneous syzygies for
general $n$. It does not claim explicit matrices in every length.
The classical path and canonical-module results supply their own general
claims; the application here connects their precise shifts to this mode
algebra, its resolution parity and its analytic quotient kernel.
The wrong-map example in Proposition 26.6 remains the reason an index
alone is insufficient to certify any of these kernel identifications.

[PA27]: https://arxiv.org/html/2607.22008
[ST27]: https://math.mit.edu/~rstan/pubs/pubfiles/66.pdf
[CA27]: https://arxiv.org/html/0812.0823
[AB27]: https://stacks.math.columbia.edu/tag/090U
[BE77]: https://eisenbud.github.io/papers/pdfs/1977-002.pdf

## 追加锚（本行以下为增补区）
