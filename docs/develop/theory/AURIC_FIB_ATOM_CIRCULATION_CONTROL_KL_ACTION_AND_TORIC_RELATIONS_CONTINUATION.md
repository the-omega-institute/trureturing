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

## 28. Common-copy seam closure and the cyclic mode map

### 28.1 The occupancy observation and its boundary data

**Definition 28.1 (A common array of histories and its observed sector).**
Fix integers $n\ge1$ and $m\ge0$. An open history is a binary word
$u=(u_1,\ldots,u_n)$ with $u_iu_{i+1}=0$ for $1\le i<n$.
Write $B_n^{\mathrm{op}}$ for these words, identifying a word with its
occupied subset of $[n]$. A common-copy realization is an array
$(u^{(r)})_{r=1}^m$ of such words on the same row set $[m]$.
Its observation is

$$
\mathcal A_m(u^{(1)},\ldots,u^{(m)})
=(m,c),\qquad c_i=\sum_{r=1}^m u_i^{(r)}.
\tag{28.1}
$$

The empty array has observation $(0,0)$. The integer $n$ counts
positions in one word; $m$ counts copies, or ordinary homogeneous degree.
Let $L_n^{\mathrm{op}}(m)$ count distinct possible $c$, with each
observation counted once regardless of the number of arrays realizing it.
For $n\ge3$, a closed history additionally satisfies $u_nu_1=0$.
Write $B_n^{\mathrm{cyc}}$ for this subset of $B_n^{\mathrm{op}}$, and set

$$
Q_n=\operatorname{conv}\{\mathbf1_I:I\in B_n^{\mathrm{cyc}}\},
\qquad L_n^{\mathrm{cyc}}(m)=|mQ_n\cap\mathbb Z^n|.
\tag{28.2}
$$

All cyclic subscripts below are interpreted modulo $n$.
A seam is tested in each row before applying (28.1).
The local five-mode dictionary is Definition 25.1: on three consecutive
positions it is $0,1,2,3,13$, with the same incidence columns and
relation $z_1z_3-z_0z_{13}$. The distinction between a common realization
and separate marginal completions is that of [Hidden Relations,
Definition C-16.1 and Proposition C-16.2][SE28]. Their two-window
condition preserves prescribed full five-state marginals; (28.1) retains
only position totals and asks for existence of some array. The domains
and conclusions of those two questions are different.

**Theorem 28.2 (The common-copy observation fixes the seam contraction
and its odd-cycle loss).**
For the observation (28.1), open realizability is equivalent to

$$
0\le c_i\le m,\qquad c_i+c_{i+1}\le m\quad(1\le i<n).
\tag{28.3}
$$

Define the $(m+1)$-by-$(m+1)$ matrix and all-ones column by

$$
T_m(a,b)=\mathbf1_{\{a+b\le m\}},\quad 0\le a,b\le m,
\qquad \mathbf e=(1,\ldots,1)^{\mathsf T}.
\tag{28.4}
$$

Then

$$
L_n^{\mathrm{op}}(m)=\mathbf e^{\mathsf T}T_m^{n-1}\mathbf e.
\tag{28.5}
$$

Joining an open left segment of length $a\ge1$ and an open right segment
of length $b\ge1$ across an edge, while keeping their two end positions
distinct, contracts their endpoint-resolved counts as

$$
L_{a+b}^{\mathrm{op}}(m)=\ell^{\mathsf T}T_m r,
\quad
\ell_j=\#\{\text{left totals with last total }j\},
\quad r_j=\#\{\text{right totals with first total }j\}.
\tag{28.6}
$$

The pairing on arbitrary boundary data has rank $m+1$ and determinant
$(-1)^{m(m+1)/2}$. An exact factorization of this bilinear pairing through
a vector space of dimension $d$ requires $d\ge m+1$.

For a closed word of even length, the cyclic versions of the local
inequalities in (28.3) are sufficient. For $n=2k+1$ odd they are
sufficient precisely after adding

$$
\sum_{i=1}^n c_i\le km.
\tag{28.7}
$$

These descriptions give the lattice points of $mQ_n$, each realized by
$m$ common closed histories. In particular,

$$
L_n^{\mathrm{cyc}}(m)=
\begin{cases}
\operatorname{Tr}(T_m^n),&n\text{ even},\\[2mm]
\displaystyle\operatorname{Tr}(T_m^n)
-\sum_{j=1}^{\lfloor m/2\rfloor}
 \binom{m-2j+n-1}{n-1},&n=2k+1.
\end{cases}
\tag{28.8}
$$

Thus an aggregate trace closes the local inequalities, while the second
line removes exactly the observations that have no common-copy lift.

Proof. The path feasibility used in Theorem 27.2 applies to these same
columns. Its following explicit version also includes $n=1$ and fixes
the row convention. In each odd column occupy the first $c_i$ rows,
and in each even column occupy the last $c_i$ rows. Neighboring occupied
row sets are disjoint by (28.3), so every row is an open history.
Conversely, adjacent ones in a row are forbidden, giving each inequality
by summation. For $n=1$ the bound $c_1\le m$ is essential; for $n\ge2$
each coordinate has a neighbor and the local edge bounds already imply
it. With $m=0$, the construction means the empty array.

Expanding the product of matrix entries in (28.5) counts one for each
sequence of totals satisfying (28.3). For reference,

$$
T_1=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
T_2=\begin{pmatrix}1&1&1\\1&1&0\\1&0&0\end{pmatrix}.
\tag{28.9}
$$

For (28.6), choose a left and a right total sequence. The sole new
inequality is between their endpoint totals. Every allowed pair has a
common array by the preceding construction on the whole path. This
establishes the contraction for counts of observations, without claiming
that it preserves two separately prescribed arrays. It is an edge join,
not identification of the two boundary positions.

Let $J_m$ reverse the $m+1$ columns. Then
$(T_mJ_m)_{a,b}=\mathbf1_{\{a\le b\}}$ is upper triangular with diagonal
one. The reversal has $m(m+1)/2$ inversions, proving the determinant
and rank. If $\ell^{\mathsf T}T_mr=(U\ell)^{\mathsf T}K(Vr)$ for all
$\ell,r$ and maps into $d$-dimensional spaces, then
$T_m=U^{\mathsf T}KV$ and $m+1=\operatorname{rank}T_m\le d$.
The same argument applies to an arbitrary bilinear form on a
$d$-dimensional intermediate space. This is a linear factorization
bound for arbitrary boundary data. It makes no computational lower-bound
claim for unrestricted encodings, nor a minimal-realization assertion
from the unmarked scalar sequence (28.5) alone.

The arithmetic consequence for two length-three pieces is

| $m$ | $L_3^{\mathrm{op}}(m)$ | Independent product $(L_3^{\mathrm{op}}(m))^2$ | Sewn $L_6^{\mathrm{op}}(m)$ |
| ---: | ---: | ---: | ---: |
| 1 | 5 | 25 | 21 |
| 2 | 14 | 196 | 157 |
| 3 | 30 | 900 | 707 |

To obtain the entries directly, start with $v_1(j)=1$ and use
$v_{s+1}(j)=\sum_{i=0}^{m-j}v_s(i)$; summing $v_3$ or $v_6$ gives the
indicated counts. For $m=3$ the vectors $v_3=(10,9,7,4)$ and
$v_6=(246,216,160,85)$ give $30$ and $707$.
The product counts all pairs before imposing the extra edge. In the
index realization of chapter 27, an index equals the corresponding
sector count under that chapter's hypotheses; multiplying these two
indices before retaining and contracting their seam data would instead
give the middle column.

For an even ring the odd/even row construction works also across the
last edge, since its endpoints have opposite parity. For an odd ring
$n=2k+1$, every independent set has at most $k$ vertices: its occupied
vertices have distinct unoccupied cyclic successors. Summing this bound
over $m$ rows proves (28.7).

Here is the integral sufficiency argument, including zero coordinates.
Proceed by induction on $m$. The case $m=0$ is immediate. If some $c_i=0$,
delete that vertex. The remaining cycle becomes a path, or its nonzero
support becomes disjoint paths. Color each such path alternately and
use the first/last-row construction on the same set of $m$ row indices.
Put zeros in deleted columns. Edges touching those columns impose no
further condition, and all rows are closed histories.

Otherwise every $c_i\ge1$. There is a slack edge $\{i,i+1\}$ with
$c_i+c_{i+1}\le m-1$: if all edges were saturated, summing them would
give $2\sum c_i=nm>2km$. Choose the independent set

$$
I=\{i+2,i+4,\ldots,i+2k\}\pmod n.
\tag{28.10}
$$

It has size $k$, meets every edge once except $\{i,i+1\}$, and all its
chosen coordinates are positive. Subtracting $\mathbf1_I$ leaves
nonnegative coordinates; every met edge now has sum at most $m-1$,
and the one unmet edge already did. The total drops by $k$ and is at
most $k(m-1)$. Induction realizes the remainder by $m-1$ rows, to which
we append $I$. This proves the integer decomposition property in the
exact degree used in (28.1), not only fractional realizability.

To identify the real polytope as well, let $P$ be the bounded rational
polyhedron given by the local inequalities at $m=1$, with (28.7) when
$n$ is odd. It contains $Q_n$. Any rational point of $P$ has a common
denominator $d>0$; the integer construction expresses its multiple as
$d$ independent sets and therefore puts that point in $Q_n$.
Rational points are dense in $P$, since a bounded rational polyhedron
is the convex hull of its rational vertices. The polytope $Q_n$ is
closed, so $P\subseteq Q_n$. This proves equality and (28.2)'s
interpretation in every degree. These stable-set descriptions are the
classical cycle descriptions, recorded in [Miyazaki, §2][MI28]; their
role here is the lift of the specified occupancy observation.

Finally, expand the trace in (28.8). It counts tuples
$(c_1,\ldots,c_n)$ with $c_i+c_{i+1}\le m$, including the last-first
edge, once per tuple with its fixed position labels. It does not divide
by rotations. For odd $n$, partition the tuples violating (28.7) by

$$
\sum_i c_i=km+j,\qquad
1\le j\le\lfloor m/2\rfloor.
$$

The upper bound follows by summing the edge inequalities. Set

$$
a_i=m-c_i-c_{i+1}\ge0,\qquad \sum_i a_i=m-2j.
\tag{28.11}
$$

There is a bijection between such tuples and weak compositions of
$m-2j$ into $n$ parts. Its inverse is

$$
c_i=j+\sum_{r=0}^{k-1}a_{i+1+2r}.
\tag{28.12}
$$

Indeed, the summands in $c_i+c_{i+1}$ cover every $a$ except $a_i$;
thus that sum is $2j+\sum a-a_i=m-a_i$. Also each $a_i$ occurs $k$
times in the sum of (28.12), giving $\sum c_i=km+j$.
The coordinates are nonnegative and the edge equations bound them by
$m$. Uniqueness follows because a difference solving
$d_i+d_{i+1}=0$ alternates sign and, on an odd ring, returns with
opposite sign, hence is zero. Stars and bars counts the compositions
as $\binom{m-2j+n-1}{n-1}$, proving (28.8). This proof exhibits the
missing common-copy constraint in the same coordinates as the mode map.
$\square$

**Proposition 28.3 (The trace excess and its first seven-position
obstruction).** Put
$E_n(m)=\operatorname{Tr}(T_m^n)-L_n^{\mathrm{cyc}}(m)$ for odd $n\ge3$.
Then

$$
\sum_{m\ge0}E_n(m)t^m
=\frac{t^2}{(1-t^2)(1-t)^n}.
\tag{28.13}
$$

For seven positions the count is

| $m$ | $\operatorname{Tr}(T_m^7)$ | $L_7^{\mathrm{cyc}}(m)$ | $E_7(m)$ |
| ---: | ---: | ---: | ---: |
| 1 | 29 | 29 | 0 |
| 2 | 289 | 288 | 1 |
| 3 | 1640 | 1633 | 7 |
| 4 | 6604 | 6575 | 29 |
| 5 | 21122 | 21031 | 91 |

At $m=2$ the only extra tuple is $\mathbf1=(1,\ldots,1)$.
It cannot be the observation of two closed histories.

Proof. Put $s=m-2j$ in the sum in (28.8). The generating function is
$\sum_{j\ge1}t^{2j}\sum_{s\ge0}\binom{s+n-1}{n-1}t^s$, giving
(28.13). To compute the trace entries without an implicit counting
convention, set $A_0(a,b)=\mathbf1_{a=b}$ and recursively
$A_{r+1}(a,b)=\sum_{d=0}^{m-b}A_r(a,d)$ for $0\le a,b\le m$.
Then $A_r=T_m^r$ and the first column in the table is
$\sum_a A_7(a,a)$. Formula (28.8) gives respectively
$0,1,7,\binom86+1=29,\binom96+7=91$ for the excess.
For $m=2$ the only slack composition has $j=1$ and all $a_i=0$;
(28.12) gives $c=\mathbf1$. If two rows realized it, every position
would be assigned to exactly one row and adjacent positions would
have different rows. This would two-color an odd ring, which is
impossible. Equivalently $7>3\cdot2$ violates (28.7).
This is the integer common-copy version of the half-filled odd-cycle
obstruction in [Pyramid Local Fillings, §9][PY28]. The transfer matrix
has counted its stated local domain correctly. $\square$

### 28.2 The actual relation presentation under seam closure

**Definition 28.4 (The cyclic subalgebra with the unchanged degree map).**
Let

$$
\mathcal S_n^{\mathrm{cyc}}
=\{(m,c):m\ge0,\ c\in mQ_n\cap\mathbb Z^n\},\qquad
R_n^{\mathrm{cyc}}=\mathbb C[\mathcal S_n^{\mathrm{cyc}}].
$$

Write $X^{(m,c)}=t_0^m\prod_{i=1}^n t_i^{c_i}$.
Use the polynomial ring of mode names
$S_n^{\mathrm{cyc}}=\mathbb C[z_I:I\in B_n^{\mathrm{cyc}}]$ and map

$$
\varphi_n^{\mathrm{cyc}}(z_I)=X^{(1,\mathbf1_I)},
\qquad I_n^{\mathrm{cyc}}=\ker\varphi_n^{\mathrm{cyc}}.
\tag{28.14}
$$

Write $S_n^{\mathrm{op}}=\mathbb C[z_I:I\in B_n^{\mathrm{op}}]$ and
$I_n^{\mathrm{op}}$ for the kernel of its path map from Definition 27.1.
The map (28.14) is its restriction to cyclically allowed generators.
An exponent vector $\alpha$ in the
mode variables is an unordered multiset of rows, and

$$
\deg z^\alpha
=\left(\sum_I\alpha_I,\ \sum_I\alpha_I\mathbf1_I\right).
\tag{28.15}
$$

Passing from $\alpha$ to (28.15) can forget correlations even after row
ordering has already been discarded.

**Proposition 28.5 (Seam closure changes the relation complex through
a subalgebra, not a forbidden-mode quotient).**
There are degree-preserving inclusions and presentations

$$
\begin{aligned}
S_n^{\mathrm{cyc}}&\subseteq S_n^{\mathrm{op}},&
R_n^{\mathrm{cyc}}&\subseteq R_n,\\
I_n^{\mathrm{cyc}}&=I_n^{\mathrm{op}}\cap S_n^{\mathrm{cyc}},&
R_n^{\mathrm{cyc}}&\simeq S_n^{\mathrm{cyc}}/I_n^{\mathrm{cyc}}.
\end{aligned}
\tag{28.16}
$$

The cyclic ideal consists of the span of the equal-occupancy binomial
relations in these variables. Its degree-$m$ quotient has dimension
$L_n^{\mathrm{cyc}}(m)$ and exactly one basis monomial per feasible
observation, rather than one per unordered array.
For $n=7$, setting the path variables containing both $1$ and $7$ equal
to zero does not produce this algebra with its specified mode map.
Nevertheless every three-consecutive-position five-mode relation is
still present in the cyclic algebra.

Proof. Theorem 28.2 gives generation of $\mathcal S_n^{\mathrm{cyc}}$
by the vectors $(1,\mathbf1_I)$. Both mode algebras are subalgebras of
the same polynomial ring in $t_0,\ldots,t_n$, and the cyclic generators
are a subset of the path generators. This proves the inclusions and
kernel contraction in (28.16). Grouping terms of any polynomial in the
kernel by their target monomial proves the binomial description:
within each group the coefficient sum is zero, so subtraction of a
chosen representative expresses the group as a linear combination of
differences of monomials with the same (28.15). Conversely every such
difference maps to zero. Distinct target monomials are linearly
independent, giving the degree count and the claimed basis.

The path ring contains the relation

$$
z_1z_7=z_0z_{17}.
\tag{28.17}
$$

The mode $17$ is legal on the path and forbidden on the ring, whereas
$0,1,7$ remain legal. Killing $z_{17}$ in the path ring forces
$z_1z_7=0$. In $R_7^{\mathrm{cyc}}$ its image is the nonzero monomial
$X^{(2;e_1+e_7)}$: one copy uses position $1$ and the other position $7$.
Thus the forbidden-mode quotient destroys an allowed two-copy
observation and cannot be the required degree-map-preserving algebra.
The contraction in (28.16), or equivalently elimination from the path
ideal, is the appropriate polynomial-ideal statement.

For a cyclic triple $i,i+1,i+2$ in seven positions, the five generators
with all other coordinates zero have modes
$0,\{i\},\{i+1\},\{i+2\},\{i,i+2\}$ and satisfy

$$
z_{\{i\}}z_{\{i+2\}}-z_0z_{\{i,i+2\}}=0.
\tag{28.18}
$$

Their augmented degree matrix is Definition 25.1's matrix, with its
rows put in position order, so its primitive kernel is the supplied
four-corner relation. This identifies a local relation supplier inside
the actual cyclic presentation. It does not assert that these seven
quadrics generate the full cyclic ideal or all relations between them.
The seven overlapping triples are seven choices of positions in one
word, not seven disjoint native windows with separately available
copies or operations.

There is already a correlation loss within (28.18): the two unordered
arrays $\{\{i\},\{i+2\}\}$ and $\{\varnothing,\{i,i+2\}\}$ have
identical totals but different full five-mode frequencies on that
triple. They are not related by a row permutation. Thus feasibility
of (28.15) recovers neither prescribed full marginals nor row order.
The native initialization, guard, and continuation conditions of
[Hidden Relations, C-1.3][SE28] remain additional conditions. Likewise
[Static Seams, Definition 21.1 and Theorem 21.2][SS28] distinguish
compatible visible data from a common full law; (28.16) grants no
initialization reachability or native operational authority. $\square$

[SE28]: AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md
[SS28]: AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md
[PY28]: AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS_SOFT_TO_RIGID_AND_ODD_CYCLE_OBSTRUCTIONS.md
[MI28]: https://arxiv.org/html/2205.01409v1

## 29. The seven-position relation complex and its canonical defect

### 29.1 The interior source of the same mode algebra

**Definition 29.1 (Cyclic degree, interior module and facet deficit).**
Specialize (28.14) to seven positions and write

$$
\begin{aligned}
\mathcal S&=\{(m,c)\in\mathbb Z_{\ge0}^{8}:
 c_i+c_{i+1}\le m,\ \sum_i c_i\le3m\},\\
R&=R_7^{\mathrm{cyc}}=\mathbb C[\mathcal S],\qquad
S=\mathbb C[z_I:I\in B_7^{\mathrm{cyc}}],\qquad I=\ker(S\to R),\\
\delta(m,c)&=3m-\sum_i c_i,\\
\Omega&=\operatorname{span}_{\mathbb C}
 \{X^{(m,c)}:c_i\ge1,\ c_i+c_{i+1}\le m-1,
                    \ \sum_i c_i\le3m-1\}.
\end{aligned}
\tag{29.1}
$$

Here $\Omega$ is an $R$-submodule of $R$, since addition of a semigroup
point preserves the strict cone inequalities. Put

$$
\nu_3=(3;\mathbf1),\qquad \nu_5=(5;2\mathbf1),\qquad
J=\operatorname{span}_{\mathbb C}\{X^s:s\in\mathcal S,\ \delta(s)\ge1\}.
\tag{29.2}
$$

The nonnegative additive function $\delta$ makes $J$ an ideal.
Use $S(-a)_d=S_{d-a}$ for ordinary shifts, and the corresponding
convention for vectors of degrees. Let $L(m)=L_7^{\mathrm{cyc}}(m)$
for $m\ge0$, and let $L^\circ(m)$ count the interior lattice points of
$mQ_7$ for $m>0$.

**Theorem 29.2 (The common-copy obstruction determines the end of the
cyclic relation complex).**
For the mode map of Definition 29.1, $R$ is normal and Cohen–Macaulay
of dimension eight, and $\Omega$ is its multigraded canonical module
$\omega_R$. Its two minimal generators are $X^{\nu_3},X^{\nu_5}$.
The quotient by the global-facet ideal has the presentation

$$
R/J\simeq\mathbb C[y_0,\ldots,y_6],\qquad \deg y_j=1,
\tag{29.3}
$$

where $y_j$ is the mode of the maximum independent set
$M_j=\{j+2,j+4,j+6\}$, with residues modulo seven represented in $[7]$.
There is an exact sequence of multigraded $R$-modules

$$
0\longrightarrow R(-\nu_3)
\xrightarrow{\ 1\mapsto X^{\nu_3}\ }\omega_R
\longrightarrow (R/J)(-\nu_5)\longrightarrow0.
\tag{29.4}
$$

For ordinary degree this is
$0\to R(-3)\to\omega_R\to(R/J)(-5)\to0$.
Consequently the interior sector count and its series are

$$
\begin{aligned}
L^\circ(m)&=L(m-3)+\binom{m+1}{6}\quad(m\ge3),\\
H_{\omega_R}(t)-t^3H_R(t)&=\frac{t^5}{(1-t)^7}.
\end{aligned}
\tag{29.5}
$$

The binomial in the first line is zero at $m=3,4$.
The minimal multigraded resolution of this actual $S/I$ has projective
dimension $21$ and last free module

$$
F_{21}
=S(-(26;7\mathbf1))\oplus S(-(24;6\mathbf1)).
\tag{29.6}
$$

In particular its last ordinary shifts are $26$ and $24$, with total
rank two. The obstruction that distinguishes these two canonical
generators is exactly

$$
\nu_5-\nu_3=(2;\mathbf1)\notin\mathcal S,
\tag{29.7}
$$

the extra local-trace observation of Proposition 28.3.

Proof. The canonical and face calculations used below are classical
intermediate suppliers. In Miyazaki, [*Non-Gorenstein locus and almost
Gorenstein property of the Ehrhart ring of the stable set polytope of a
cycle graph*, §4][MI28], put $\ell=3$, identify the vertex function with
$c$ and its value at $-\infty$ with $m$.
His $\eta_1,\eta_2$ are our $\nu_3,\nu_5$; the image of
$\varphi:R\to\omega_R(3)$ in Lemma 4.1 is our shifted injection.
His Lemmas 4.2–4.3 identify the face algebra $R^{(0)}$ with a polynomial
ring, and Lemma 4.4 gives $C_2=X^{\nu_5}R^{(0)}$.
The argument immediately preceding Theorem 4.5 proves minimality of
these canonical generators; Theorem 4.5 identifies the resulting
almost-Gorenstein property. These are supplied facts, not a new cycle
classification. The proof here fixes their full correspondence to
(28.14), proves the $R$-module quotient map required in (29.4), and
then consumes it in the relation complex and ambient index.

### 29.2 Interior translation inside the proof of Theorem 29.2

The cyclic polytope description and integer decomposition are those
proved in Theorem 28.2. Its cone has full group lattice: the zero mode
and singleton modes generate $(1,0)$ and, by subtraction, every
$(0,e_i)$. It is full dimensional, since at scale one a constant vector
with sufficiently small positive entries satisfies all inequalities
strictly. The semigroup is the intersection of this rational cone with
its group lattice, hence saturated and normal. The semigroup dimension
is its group rank, eight.

The facets for an even cycle of length at least four are the coordinate
and edge inequalities. For an odd cycle of length $2k+1\ge5$, add the
global facet $\sum x_i\le k$. A coordinate facet has a point with that
coordinate zero and all other coordinates small positive. An edge facet
has its endpoints equal to $1/2$ and all other coordinates sufficiently
small positive; all other inequalities are strict. For the global
facet, the edge slacks $a_i=1-x_i-x_{i+1}$ satisfy $\sum a_i=1$ and

$$
x_i=\sum_{r=0}^{k-1}a_{i+1+2r}.
\tag{29.8}
$$

This is an affine bijection from the simplex $a_i\ge0$, $\sum a_i=1$
onto that face: the adjacent sums are $1-a_i$, and summing the
coordinates gives $k$. Uniqueness uses the odd-cycle linear equations
as in (28.12). Its dimension is $n-1$, proving the facet assertion.
Thus the strict inequalities used in (29.1) describe precisely the
interior integer points, rather than a smaller selected subset.

This also specifies exactly where the path translation of Theorem 27.2
survives closing a seam. For an even cycle and $m\ge3$, its interior
integer points are

$$
\mathbf1+\bigl((m-3)Q_n\cap\mathbb Z^n\bigr).
\tag{29.9}
$$

For $n=2k+1\ge5$, subtracting $\mathbf1$ from the strict inequalities
gives instead

$$
\operatorname{int}(mQ_n)\cap\mathbb Z^n
=\mathbf1+
\left\{b\in\mathbb Z_{\ge0}^n:
 b_i+b_{i+1}\le m-3,\quad
 \sum b_i\le k(m-3)+(k-2)\right\}.
\tag{29.10}
$$

Indeed $c_i\ge1$ and $c_i+c_{i+1}\le m-1$ become the first two
conditions, and $\sum c_i\le km-1$ becomes the last one. This proves
both formulas directly. At $k=2$, (29.10) has exactly the same
three-degree translation as the path. For $k\ge3$, take

$$
m=2k-1,\qquad c=(k-1)\mathbf1.
\tag{29.11}
$$

All coordinates are positive, each edge sum is $m-1$, and the total
is $km-1$, so this is interior. After subtracting $(3;\mathbf1)$,
the remaining degree is $2k-4$ and the remaining total exceeds
$k(2k-4)$ by $k-2>0$. It is not a semigroup point.
For the triangle, the polytope is the simplex
$x_i\ge0$, $\sum x_i\le1$; the edge inequalities are redundant.
The strict integer conditions give the four-degree shift
$(4;1,1,1)$ instead. The one-position open interval has the separate
two-degree shift already specified in chapter 27.

Hochster's theorem and the Danilov–Stanley interior-monomial formula,
with the exact normal-semigroup hypotheses used in Theorem 27.2 and
its source [Brennan–Dupont–Villarreal, (1.2), (3.2), §3][CA27], now give
Cohen–Macaulayness and identify the interior ideal with the canonical
module. Thus (29.9) and the $k=2$ instance of (29.10) give principal
canonical modules; the triangle does too with its distinct shift.
For odd length at least seven the only degree-three interior point is
$\mathbf1$, since its edge sums must be at most two. There is no
interior point in smaller degree. If the canonical module were
principal, its homogeneous generator would therefore be a scalar
multiple of $X^{(3;\mathbf1)}$. Point (29.11) prevents this.
This recovers precisely the known Gorenstein boundary used here:
open paths with $n\ge2$, even rings, and the five-ring have shift three;
the triangle has shift four; odd rings of length at least seven are
not Gorenstein. The even-cycle precedent is Ohsugi–Hibi,
Theorem 2.1(b), and the odd-cycle precedent is Hibi–Tsuchiya,
Theorem 1, as identified in [Miyazaki, introduction and §2][MI28].
They enter only to delimit the inherited path-duality argument.

### 29.3 The two generators and the quotient action in Theorem 29.2

For seven positions, both $\nu_3$ and $\nu_5$ satisfy the strict
inequalities. If $(m,c)$ is interior and $\delta(m,c)\ge2$, subtract
$\nu_3$. The remainder has nonnegative coordinates, edge sums at most
$m-3$, and deficit $\delta(m,c)-2\ge0$, hence belongs to $\mathcal S$.
The original degree is at least three, as just proved.

It remains to treat $\delta(m,c)=1$, or $\sum c_i=3m-1$.
Every coordinate is at least two. For if $c_i=1$, pair the other six
vertices into three edges of the path obtained by deleting $i$.
The strict edge bounds give
$\sum c_i\le1+3(m-1)=3m-2$, a contradiction.
Consequently $m\ge5$, because any edge has sum at least four and at
most $m-1$. Subtracting $\nu_5$ leaves nonnegative coordinates, edge
sums at most $m-5$, and total exactly $3(m-5)$. It belongs to the face
semigroup of deficit zero. Conversely, adding either generator to any
semigroup point is interior. Hence

$$
\omega_R=X^{\nu_3}R+X^{\nu_5}R.
\tag{29.12}
$$

The difference in (29.7) satisfies all local edge bounds but has total
seven at degree two, violating the total bound six. Thus $X^{\nu_5}$
is not an $R$-multiple of $X^{\nu_3}$; the reverse divisibility is
impossible by ordinary degree. Since monomials form a basis, no linear
combination of monomial multiples changes that conclusion. This proves
minimality and connects the canonical obstruction to the actual
common-copy obstruction, rather than only to a numerical type.

For a face point $s=(q,b)$ with $\sum b_i=3q$, define

$$
a_i=q-b_i-b_{i+1},\qquad
\sum_i a_i=q,\qquad
b_i=a_{i+1}+a_{i+3}+a_{i+5}.
\tag{29.13}
$$

These assignments are inverse additive maps between the face semigroup
and $\mathbb N^7$: for any nonnegative $a$, set $q=\sum a_i$ and
use the last formula. Then $b_i+b_{i+1}=q-a_i$, and $\sum b_i=3q$.
Conversely the odd-cycle edge equations have a unique solution.
The basis vector $a_j=1$ corresponds to the degree-one mode $M_j$.
Distinct monomials in these seven modes therefore have distinct
exponents, proving that their face algebra is polynomial.

The quotient $R/J$ has exactly this algebra structure. Products of
zero-deficit monomials remain on the face. Multiplication by a
positive-deficit monomial takes a face monomial into $J$.
The map that kills positive-deficit monomials and retains face
monomials is consequently an algebra homomorphism, with kernel $J$;
it identifies the quotient with the face subalgebra and proves (29.3).
This is a quotient by a face ideal inside the cyclic ring, a different
operation from the invalid path-mode quotient in Proposition 28.5.

To fix the $R$-module structure of the canonical quotient, for
$s=(q,b)\in\mathcal S$ compute

$$
\begin{aligned}
X^{\nu_5+s}\in X^{\nu_3}R
&\ \Longleftrightarrow\ s+(2;\mathbf1)\in\mathcal S\\
&\ \Longleftrightarrow\ \delta(s)\ge1.
\end{aligned}
\tag{29.14}
$$

Nonnegativity and the edge inequalities of the shifted point are
automatic; its deficit is $\delta(s)-1$, giving the last equivalence.
The $R$-linear map
$r\mapsto[X^{\nu_5}r]$ from $R$ to $\omega_R/X^{\nu_3}R$ is
surjective by (29.12). Its monomial kernel is exactly $J$ by (29.14),
and independence of exponents shows that no further polynomial kernel
occurs. The degree shift is $\nu_5$, giving (29.4).
The left injection uses the domain property of $R$.

This exact sequence is not an assertion of an $R$-module splitting.
For example, $X^{(1;0)}\in J$ annihilates every class of $R/J$,
whereas multiplication by that nonzero element is injective on
$\omega_R\subset R$. A nonzero $R$-linear embedding of $R/J$ into
$\omega_R$ is therefore impossible. The vector-space separation of
the two deficit ranges, or freeness over the face subalgebra, must not
be mistaken for such a splitting.

Taking degree $m$ in the exact sequence gives (29.5): the quotient's
dimension is the dimension of degree $m-5$ polynomials in seven
variables, namely $\binom{m+1}{6}$ for $m\ge5$, and zero for $m<5$.
In particular the interior points omitted by the path-style shift are

| $m$ | $L^\circ(m)-L(m-3)$ |
| ---: | ---: |
| 5 | 1 |
| 6 | 7 |
| 7 | 28 |
| 8 | 84 |
| 9 | 210 |

These are the dimensions of the successive face degrees, obtained by
stars and bars from (29.13). They count a polyhedral facet contribution;
no analytic boundary condition is involved.

### 29.4 Last syzygies in the given mode grading

There are $29$ degree-one variables in $S$. The independent subsets of
the seven-ring comprise one empty set, seven singletons, fourteen
nonadjacent pairs, and seven triples. The pair count is
$\binom72-7=14$. Each triple has exactly one uncovered edge: its three
occupied vertices force three distinct unoccupied successors, leaving
one further unoccupied vertex, so its three gaps have lengths $1,1,2$.
Conversely each choice of uncovered edge gives exactly the triple
(28.10). This proves the triple count and identifies these seven modes
with the $M_j$ of (29.3).

A fixed vertex occurs in eight modes: after selecting it, delete it and
its two neighbors; the remaining four vertices form a path, with
$|B_4|=8$ by Definition 25.7. Therefore the sum of all variable
multidegrees is

$$
\Sigma=\sum_{I\in B_7^{\mathrm{cyc}}}(1,\mathbf1_I)
=(29;8\mathbf1),\qquad \omega_S=S(-\Sigma).
\tag{29.15}
$$

Since $R$ is Cohen–Macaulay of dimension eight, the
Auslander–Buchsbaum and canonical-Ext inputs of Theorem 27.2 apply to
this presentation and give

$$
\operatorname{pd}_S R=29-8=21,\qquad
\operatorname{Ext}^{21}_S(R,S(-\Sigma))\simeq\omega_R,
\tag{29.16}
$$

with all other Ext groups zero. These are the same classical
commutative-algebra suppliers [AB27] and [BE77]; the polynomial ring
and grading have now changed from the path presentation to (28.14).
Choose a minimal multigraded resolution $F_\bullet$. Such a resolution
exists by homogeneous generator selection and Hilbert syzygy, as in
Theorem 27.2. If $S(-\gamma)$ is a summand of $F_{21}$, its dual into
$S(-\Sigma)$ has generator degree $\Sigma-\gamma$.
Every differential of a minimal resolution has entries in the
homogeneous maximal ideal, and dualizing preserves that property.
Thus the cokernel of the last dual differential has precisely these
minimal generator degrees; reduction modulo the maximal ideal makes
the differential zero. By (29.12) those degrees are exactly
$\nu_3,\nu_5$. Subtraction from (29.15) gives (29.6).

For comparison, the open seven-position path of chapter 27 has
$34$ mode variables (the Fibonacci number $F_9$), dimension eight,
projective dimension $26$,
and one last generator of ordinary degree $34-3=31$.
Closing the seam removes five degree-one modes, but the surviving
cyclic relation algebra has two canonical generators and two last
syzygy summands. The local four-corner identities (28.18) persist while
the rank-one terminal duality of the path ceases to apply.
Here $21$ is the length of a minimal free resolution, and (29.6)
specifies only its final module. No full list of its twenty-one
matrices, intermediate Betti numbers, or native operations is asserted.
This completes the proof of Theorem 29.2. $\square$

## 30. Smooth ambient index of the common-copy defect

### 30.1 The elliptic carrier and the embedded face

**Definition 30.1 (A resolved module on the smooth ambient space).**
Keep the actual $29$-variable ring $S$ of (29.1), and let $M$ be a
finitely generated ordinarily graded $S$-module. Choose a finite graded
free resolution $F^M_\bullet\to M$ and an integer twist $d$.
On $X=\mathbb {CP}^{28}$ put

$$
E^{-i}_{M,d}=\widetilde F^M_i(d),\qquad
C^j_{M,d}=\bigoplus_{q-i=j}\Omega^{0,q}(X,E^{-i}_{M,d}),
\qquad
\delta=\bar\partial+(-1)^q d_M.
\tag{30.1}
$$

The algebraic differential $d_M$ raises the cochain degree $-i$ by
one and is holomorphic. With smooth Hermitian metrics and the
Fubini–Study metric, define

$$
D_{M,d}=\sqrt2(\delta+\delta^\dagger),\qquad
D^+_{M,d}:H^1(X,\mathscr E^{\mathrm{even}}_{M,d})
\longrightarrow L^2(X,\mathscr E^{\mathrm{odd}}_{M,d}).
\tag{30.2}
$$

Total degree is $q-i$, so negative odd degrees are retained.
This is the construction of Theorems 25.3 and 26.5 with the particular
cyclic relation presentation in place of the one-relation or
four-position presentation. Its general module meaning is sheaf
hypercohomology; equality with a module's degree piece requires a
separate vanishing argument.

**Theorem 30.2 (The seam defect has a linear-face index correction).**
For every $M,d$ in Definition 30.1, $D^+_{M,d}$ is elliptic Fredholm and

$$
\operatorname{ind}D^+_{M,d}
=\chi(\mathbb {CP}^{28},\widetilde M(d)).
\tag{30.3}
$$

This index is additive for short exact sequences of graded modules
with compatible twists. For the particular sequence (29.4), the
quotient sheaf is the pushforward of a line bundle along the explicit
linear inclusion

$$
\begin{aligned}
\iota:\mathbb {CP}^{6}&\hookrightarrow\mathbb {CP}^{28},\\
[y_0:\cdots:y_6]&\longmapsto[z_I]_{I\in B_7^{\mathrm{cyc}}},\qquad
z_{M_j}=y_j,\quad z_I=0\text{ if }|I|<3.
\end{aligned}
\tag{30.4}
$$

For every $m\ge3$ one has

$$
\begin{aligned}
\operatorname{ind}D^+_{\omega_R,m}
-\operatorname{ind}D^+_{R,m-3}
&=\operatorname{ind}\bigl(\bar\partial+\bar\partial^\dagger\bigr)^+
 _{\mathbb {CP}^{6},\mathcal O(m-5)}\\
&=\binom{m+1}{6}=L^\circ(m)-L(m-3).
\end{aligned}
\tag{30.5}
$$

The positive constant $\sqrt2$ may be included on the right without
changing its index. With $h=c_1(\mathcal O(1))$ on $\mathbb {CP}^{6}$
and $\int h^6=1$, the correction is also

$$
[h^6]\ e^{(m-5)h}\left(\frac{h}{1-e^{-h}}\right)^7.
\tag{30.6}
$$

For $m\ge5$ it is the dimension of degree $m-5$ homogeneous polynomials
in seven variables. For $m=3,4$ the bundles $\mathcal O(-2)$ and
$\mathcal O(-1)$ are acyclic and the correction is zero.
These are smooth closed ambient manifolds; the facet in (29.1) does
not become an analytic boundary.

Proof. Holomorphicity and the alternating sign in (30.1) give
$\delta^2=0$. The sheafified resolution is exact off its terminal
cohomology $\widetilde M(d)$, since localization followed by taking
homogeneous degree zero is exact. Its Dolbeault total complex therefore
computes the analytic hypercohomology of that sheaf. Algebraic and
analytic cohomology agree by the Serre GAGA comparison used in
Theorem 25.3 [GA25].

Every matrix entry of $d_M$ acts by an order-zero bundle map. The
principal symbol of (30.2) is thus the direct sum of the
Dolbeault–Dirac symbols, with parity reversed for odd $i$.
At a nonzero real cotangent vector, wedge by its $(0,1)$ part and
contraction have nonzero scalar Clifford anticommutator, so the symbol
is invertible. The compact elliptic estimate and Rellich compactness
give Fredholmness. The Hodge decomposition for this elliptic complex
identifies its smooth harmonic spaces with its total cohomology;
the index is the alternating sum of those dimensions, giving (30.3).
As in Theorem 25.3, the cokernel of the $H^1\to L^2$ realization is
identified by weak solutions of the formal adjoint equation and
elliptic regularity, not by an unsupported equality of bounded
Hilbert adjoints. These analytic inputs are the classical elliptic
complex results cited there in [AS25] and [FR25].

A short exact sequence sheafifies exactly and its long cohomology
sequence has alternating dimension zero. This proves index additivity
without requiring compatible choices of metrics or of free resolutions.
For arbitrary $M$ it does not identify (30.3) with $\dim M_d$ in every
degree. For instance $M=S/(z_I:I\in B_7^{\mathrm{cyc}})$ has
$M_0=\mathbb C$, but its sheaf is zero: localizing at any projective
coordinate kills it. Its index at $d=0$ is zero, not one.

For the quotient at hand there is more information than an abstract
isomorphism of Proj spaces. A degree-one mode of size $s$ has deficit
$3-s$. Thus all $22$ modes of sizes zero, one and two lie in $J$,
and the seven modes $M_j$ have deficit zero.
The composite homomorphism

$$
S\longrightarrow R\longrightarrow R/J=\mathbb C[y_0,\ldots,y_6]
\tag{30.7}
$$

sends exactly these $22$ variables to zero and sends $z_{M_j}$ to $y_j$.
Its kernel is precisely the ideal generated by the $22$ vanished
variables. Indeed, after setting them equal to zero the residual
polynomial is in the seven maximum-mode variables; (29.13) proves
that their monomials are independent, so no further relation survives.
This proves (30.4) as a linear closed immersion with its specified
homogeneous coordinates.

For completeness, the corresponding sheaf identity follows on the
standard affine charts by localizing (30.7). On $D_+(z_{M_j})$ its
homogeneous degree-zero module is the coordinate ring of
$D_+(y_j)\subset\mathbb P^6$, with the same grading shift for a twist.
On a chart of any of the $22$ killed coordinates the quotient localizes
to zero, just as the inverse image of that chart under $\iota$ is empty.
These identifications agree on intersections and prove

$$
\widetilde{R/J}(d)=\iota_*\mathcal O_{\mathbb P^6}(d).
\tag{30.8}
$$

In particular the twist is inherited from the same degree-one mode
coordinates; it is not an arbitrarily chosen line bundle on an
abstractly isomorphic space. A closed immersion has exact direct image
on these sheaves, and the same chart cohomology, or the composition of
global sections with that direct image, gives
$H^q(\mathbb P^{28},\iota_*\mathcal O(d))=H^q(\mathbb P^6,\mathcal O(d))$.
Sheafifying (29.4), twisting by $m$, and using additivity now reduces
the left side of (30.5) to $\chi(\mathbb P^6,\mathcal O(m-5))$.

[Stacks Lemma 30.8.1, tag 01XT][PC25] states the exact line-bundle
cohomology used here: on $\mathbb P^r$, nonnegative twist has only
$H^0$, of dimension $\binom{d+r}{r}$, and twists $-r\le d\le-1$
have no cohomology at all. The possible negative-twist top cohomology
starts at $d\le-r-1$. With $r=6$ and $d=m-5$, this gives precisely the
cases in (30.5). The classical complex index formula, with the Euler
sequence $\operatorname{Td}(T\mathbb P^6)=(h/(1-e^{-h}))^7$, gives
(30.6). Thus the analytic and the algebraic count use the same face
quotient and the same twist.

One can also justify the two individual Hilbert-function identifications
in (30.5), rather than just their difference. Let $F_\bullet$ be the
minimal resolution of $R$ from Theorem 29.2, and write $j$ for any of
its ordinary shifts. All such $j$ are nonnegative, since $F_0=S$ and
each later module is generated by homogeneous elements of a positively
graded preceding module. The reversed dual complex

$$
G_i=\operatorname{Hom}_S(F_{21-i},S(-29))
\tag{30.9}
$$

is a minimal free resolution of $\omega_R$, by the Ext vanishing in
(29.16). Its initial generators have degrees three and five.
Successive homogeneous generators cannot have smaller degree than
three, so every shift $29-j$ in (30.9) is at least three. Hence
$0\le j\le26$ for $F_\bullet$, and all shifts of $G_\bullet$ are at
most $29$.

For $d=m-3\ge0$ every line bundle in $\widetilde F_\bullet(d)$ has
twist at least $-26$, and for $m\ge3$ the same holds for
$\widetilde G_\bullet(m)$. Both are above the threshold $-29$ for top
cohomology on $\mathbb P^{28}$. Stacks 01XT and GAGA therefore make
these two Dolbeault hypercohomologies the ordinary degree strands of
their exact free resolutions. They have only degree-zero cohomology,
respectively $R_{m-3}$ and $(\omega_R)_m$. The elliptic Hodge theorem
gives their positive kernels these spaces and their negative kernels
zero. This is the additional argument specific to these modules and
this range; it does not remove the arbitrary-module distinction after
(30.3). Their dimensions are the two counts in (29.5).

The result concerns an index and, in this specified range, harmonic
representatives of the stated quotients. It equates no full spectra or
metrics of the two ambient constructions. Neither manifold has a
boundary, so there is no Atiyah–Patodi–Singer boundary problem,
eta-invariant, or analytic cutting-and-gluing assertion in (30.5).
$\square$

### 30.2 The count polynomial and the reciprocity correction

**Proposition 30.3 (The Hilbert numerator of this cyclic occupancy
quotient).**
For the seven-position relation map (28.14),

$$
H_R(t)=\sum_{m\ge0}L(m)t^m
=\frac{1+21t+84t^2+85t^3+21t^4+t^5}{(1-t)^8}.
\tag{30.10}
$$

In particular its numerator is not palindromic. The count polynomial,
with the convention that $\binom{x}{7}=x(x-1)\cdots(x-6)/7!$ as a
polynomial in $x$, is

$$
\begin{aligned}
L(x)={}&\binom{x+7}{7}+21\binom{x+6}{7}
+84\binom{x+5}{7}+85\binom{x+4}{7}\\
&\quad+21\binom{x+3}{7}+\binom{x+2}{7}.
\end{aligned}
\tag{30.11}
$$

Its reciprocity defect relative to the path translation is the
polynomial identity

$$
-L(-x)=L(x-3)+\binom{x+1}{6}.
\tag{30.12}
$$

For integers $m\ge3$ its last term is the index correction (30.5).
Values at negative arguments are polynomial evaluations, not counts
of negative copies.

Proof. A degree bound is needed before finitely many counts determine
a Hilbert numerator. Here it follows from the canonical calculation.
Because $R$ is standard graded, Cohen–Macaulay, and eight-dimensional
over the infinite field $\mathbb C$, choose a linear homogeneous
system of parameters that is a regular sequence. Quotienting by its
eight linear forms gives a finite-dimensional graded algebra with
polynomial Hilbert series $h(t)$; the successive multiplication exact
sequences give $H_R(t)=h(t)/(1-t)^8$ and $h(0)=1$.

The canonical Hilbert-series relation is

$$
H_{\omega_R}(t)=\frac{t^8h(t^{-1})}{(1-t)^8}.
\tag{30.13}
$$

This is the canonical duality used in [Miyazaki, §5, proof of
Theorem 5.2][MI28]. It follows here directly by alternating the
Hilbert series of the reversed dual resolution (30.9): a shift $j$
becomes $29-j$, reversal contributes $(-1)^{21}$, and
$(1-t^{-1})^{29}=-t^{-29}(1-t)^{29}$. Therefore the result is
$H_R(t^{-1})$, which is (30.13) because the ring dimension is even.
These manipulations are identities of rational functions before the
expansion at zero.

The least degree of $\omega_R$ is three with a one-dimensional degree
piece, by §29.2. The least exponent of $t^8h(t^{-1})/(1-t)^8$ is
$8-\deg h$, since the denominator has constant term one.
Thus $\deg h=5$ and the leading coefficient is one.
Substituting (30.13) into (29.5) gives

$$
t^5h(t^{-1})-h(t)=t^2-t^3.
\tag{30.14}
$$

Write $h(t)=\sum_{j=0}^5h_jt^j$. The count $L(0)=1$ gives $h_0=1$;
the $29$ actual modes give
$h_1=L(1)-8L(0)=21$. Proposition 28.3 gives $L(2)=288$, and hence

$$
h_2=L(2)-8L(1)+28L(0)=288-232+28=84.
$$

Equation (30.14) now forces $h_5=h_0=1$, $h_4=h_1=21$ and
$h_3=h_2+1=85$. This proves every coefficient of (30.10) with a
justified degree bound, and explains the nonsymmetry $84\ne85$ by
the face quotient rather than by an unexplained finite table.
It is the $\ell=3$ specialization of the asymmetry relation in
Miyazaki's Theorem 5.2, used here for this mode-map application.

Expanding $(1-t)^{-8}$ gives (30.11) for nonnegative integers.
For $0\le m<j\le5$, the nominal upper argument $m+7-j$ is a
nonnegative integer less than seven, so the displayed polynomial
binomial is zero, just as the absent degree term requires.
Thus (30.11) is valid in all nonnegative degrees, not only eventually.
Theorem 28.2 identifies this same function with the lattice-point count
of the seven-dimensional lattice polytope $Q_7$.

To see reciprocity explicitly, use the polynomial identity
$\binom{-a}{7}=-\binom{a+6}{7}$. It gives

$$
-L(-m)=\sum_{j=0}^5h_j\binom{m+j-1}{7}.
\tag{30.15}
$$

For $m\ge1$ the right side is exactly the degree-$m$ coefficient of
(30.13): terms below their starting degree have upper argument between
zero and six and vanish. By the interior description of $\omega_R$
this is $L^\circ(m)$. This is the classical Ehrhart reciprocity sign
$(-1)^7$ in the precise lattice of (28.2), here derived from the
canonical-series supplier. For $m\ge3$, (29.5) identifies it with the
right side of (30.12). Both sides of (30.12) are polynomials agreeing
at all those integers, so they agree identically. The positive-degree
index interpretation uses the range in Theorem 30.2; polynomial
continuation does not introduce any negative-copy realization.
$\square$

### 30.3 A consequence connecting the two counting corrections

**Proposition 30.4 (Trace-excess difference and the canonical face).**
Let $E(m)=E_7(m)$ for $m\ge0$, and set $E(m)=0$ for negative integers.
Then for every $m\ge3$,

$$
L^\circ(m)-L(m-3)
=E(m-3)-E(m-5)
=\operatorname{ind}D^+_{\omega_R,m}
 -\operatorname{ind}D^+_{R,m-3}
=\binom{m+1}{6}.
\tag{30.16}
$$

Proof. Formula (28.13) gives
$(1-t^2)\sum_{r\ge0}E(r)t^r=t^2/(1-t)^7$.
The coefficient at $t^{m-3}$ is
$E(m-3)-E(m-5)=\binom{m+1}{6}$ when $m\ge5$ and is zero at $m=3,4$.
The other equalities are (29.5) and (30.5).
The difference identity consumes the already identified local-trace
excess; it does not equate that excess itself to the canonical defect
in the same degree. $\square$

**Theorem 30.5 (The same obstruction across the occupancy, relation and
index observations).**
For the seven-position cyclic subalgebra with the degree map (28.15),
the locally feasible degree vector $w=(2;\mathbf1)$ has the
following linked consequences: it is the only degree-two local-trace
tuple without a common-copy lift; it is the difference of the two
minimal canonical generator degrees; the canonical quotient is the
shifted seven-variable face module in (29.4); and that quotient has
the smooth linear-face index correction (30.5). The two terminal
syzygy degrees are $\Sigma-\nu_3$ and $\Sigma-\nu_5$, not the
single path terminal degree. These conclusions remain statements of
the specified occupancy and algebraic observations, even though each
local five-mode relation is preserved.

Proof. The degree-two slack bijection in Proposition 28.3 identifies
$w$ uniquely and proves its failure to lift. Equation (29.7) identifies
the same vector, with the same position and copy coordinates, as
$\nu_5-\nu_3$. More precisely the membership calculation
$s+w\in\mathcal S\Longleftrightarrow\delta(s)\ge1$ is (29.14);
its failure on the face identifies the annihilator $J$ of the
canonical quotient. The additive inverse coordinates (29.13) then
identify that face with the actual seven maximum modes. Formula
(29.16) transports their canonical generator degrees through Ext to
(29.6). The coordinate map (30.7) places the face as the specified
linear subspace of the same ambient mode space, so the short exact
sequence has precisely the pushforward quotient (30.8), and its
Euler characteristic yields (30.5). Each step uses an explicit map
or exact sequence; equal numerical counts alone are not its premise.

For a finite relation-space realization, choose any finite homogeneous
binomial generating family $f_a$ of $I\subset S$ and let $d_a$ be their
ordinary degrees. Such a family exists: the grouped-monomial argument
in Proposition 28.5 generates the kernel by binomials, and $S$ is
Noetherian. With the Bargmann inner product of Definition 25.2 on
$S_m$, put

$$
M_{f_a}:S_{m-d_a}\to S_m,\qquad
A_{a,m}=M_{f_a}^{\dagger},\qquad
H_m^{\mathrm{cyc}}=\sum_a A_{a,m}^{\dagger}A_{a,m}.
\tag{30.17}
$$

Negative-degree source spaces are zero. Positivity gives
$\ker H_m^{\mathrm{cyc}}=\bigcap_a\ker A_{a,m}$.
The sum of the images of $M_{f_a}$ is $I_m$, because the $f_a$
generate the ideal. Taking orthogonal complements therefore gives

$$
\ker H_m^{\mathrm{cyc}}=I_m^\perp\simeq(S/I)_m=R_m,
\qquad\dim\ker H_m^{\mathrm{cyc}}=L(m).
\tag{30.18}
$$

This is the same quotient mechanism as Proposition 26.6 applied to
the actual cyclic ideal. It does not supply a complete generating
list of $I$, its full resolution matrices, or a native Hamiltonian
implementation. The metrics and positive eigenvalues depend on the
chosen family and inner products; the finite self-adjoint map in
(30.17) itself has index zero. The graded elliptic index in (30.5)
is a different construction with an explicitly identified quotient.

Finally, the two arrays in Proposition 28.5 have the same observation
but different three-position mode distributions. Hence even perfect
knowledge of a feasible $(m,c)$ cannot recover prescribed full
marginals or the unordered array, and therefore cannot recover an
ordered history either. A construction of some common array does not
prove that it was the supplied initialized native history. The
relation maps, canonical module and elliptic carrier contain no
initialization or allowed-action data that could discharge those
additional obligations. Seven positions are still seven positions,
and a polytope facet is still a face of a convex set. Neither the
local relation identities nor the index correction changes these
domains into seven native windows, a physical boundary, or an
APS/full-spectrum theorem. $\square$

## 追加锚（本行以下为增补区）

## 31. Odd-cycle defect layers and the action retained by common-copy coordinates

### 31.1 The cyclic observation and its additive coordinates

**Definition 31.1 (Position totals, slack and deficit).**
Fix $k\ge3$ and $n=2k+1$. In this chapter positions are indexed by
$\mathbb Z/n\mathbb Z$, represented by $0,\ldots,n-1$; thus the
one-based position $i+1$ of chapter 28 is the position $i$ here.
A legal history is a binary word on these positions with no neighboring
ones, including across the last-first edge. Let $\mathcal B_n$ be its
set of occupied subsets. A common array of $m$ such histories has
observation $(m,c)$, where $c_i$ counts the histories occupying position
$i$. As in Definition 28.1, copies share one row set, and observations
are counted once regardless of their number of realizations. Put

$$
\begin{aligned}
\mathcal S_k&=\left\{(m,c)\in\mathbb Z_{\ge0}^{n+1}:
 c_i+c_{i+1}\le m,\quad \sum_i c_i\le km\right\},\\
Q_n&=\operatorname{conv}\{\mathbf1_I:I\in\mathcal B_n\},\qquad
R_k=\mathbb C[\mathcal S_k],\\
a_i(m,c)&=m-c_i-c_{i+1},\qquad
\delta(m,c)=km-\sum_i c_i,\\
|a|&=\sum_i a_i,\qquad
B_i(a)=\sum_{r=0}^{k-1}a_{i+1+2r}.
\end{aligned}
\tag{31.1}
$$

All cyclic indices in $B_i$ are reduced modulo $n$. Write $X^s$ for
the monomial with exponent $s=(m,c)$; its ordinary degree is $m$.
The notation $R_k$ uses the half-length parameter, whereas the
$R_n^{\mathrm{cyc}}$ of Definition 28.4 uses the number of positions:
$R_k=R_{2k+1}^{\mathrm{cyc}}$. In particular $n$ does not count windows.

The integer decomposition in Theorem 28.2 identifies $\mathcal S_k$
with the actual common-copy observations, including $(0,0)$.
The same theorem identifies $Q_n$ with the real polytope given by
$x_i\ge0$, $x_i+x_{i+1}\le1$ and $\sum x_i\le k$.
The real conclusion uses a separate step: scaling a rational point by
a common denominator gives the integer decomposition, division gives
a convex combination of legal histories, and density of rational
points together with closedness gives every real point. Thus (31.1) uses the supplied real convex hull, and its lattice points
in degree $m$ are exactly the observations of common arrays of $m$
legal histories.

**Definition 31.2 (The canonical quotient and its face coordinates).**
Let $\omega_{R_k}$ be realized as the interior-monomial ideal, and put

$$
\begin{aligned}
\nu_j&=(2j+1;j\mathbf1),\qquad 1\le j\le k-1,\\
A_k&=\operatorname{span}_{\mathbb C}
 \{X^s:s\in\mathcal S_k,\ \delta(s)=0\},\\
J_k&=\operatorname{span}_{\mathbb C}
 \{X^s:s\in\mathcal S_k,\ \delta(s)>0\},\\
\mathcal C_k&=\omega_{R_k}/X^{\nu_1}R_k.
\end{aligned}
\tag{31.2}
$$

The interior realization and all canonical generators will be justified
inside Theorem 31.3. Deficit is additive and nonnegative on
$\mathcal S_k$, so $A_k$ is a subalgebra and $J_k$ is an ideal.
For the maximum independent set

$$
M_i=\{i+2,i+4,\ldots,i+2k\}\pmod n,
\qquad y_i=X^{(1,\mathbf1_{M_i})},
\tag{31.3}
$$

the slack vector is the $i$th standard basis vector. The symbols
$e_j=[X^{\nu_j}]$, $2\le j\le k-1$, denote classes in $\mathcal C_k$;
they will be an $A_k$-basis, with $\deg e_j=2j+1$.
As usual $A_k(-d)_m=(A_k)_{m-d}$, and a negative homogeneous degree
piece is zero.

**Theorem 31.3 (The exact action behind the odd-cycle layer count).**
For the common-copy algebra (31.1), the following coordinates are
mutually inverse additive descriptions:

$$
(m,c)\longleftrightarrow(a,\delta),\qquad
m=|a|-2\delta,\qquad c_i=B_i(a)-\delta,
\tag{31.4}
$$

with feasible domain precisely

$$
a\in\mathbb Z_{\ge0}^n,\qquad \delta\in\mathbb Z,\qquad
0\le\delta\le\min_i B_i(a).
\tag{31.5}
$$

The ring $R_k$ is a normal standard graded Cohen–Macaulay domain of
dimension $n+1$. Its canonical ideal has exactly the minimal monomial
generators $X^{\nu_1},\ldots,X^{\nu_{k-1}}$. Its quotient in (31.2)
has an exact sequence and an $A_k$-module decomposition

$$
0\longrightarrow R_k(-\nu_1)
\xrightarrow{\ 1\mapsto X^{\nu_1}\ }\omega_{R_k}
\longrightarrow\mathcal C_k\longrightarrow0,
\qquad
\mathcal C_k=\bigoplus_{j=2}^{k-1}A_ke_j,
\tag{31.6}
$$

where $A_k=\mathbb C[y_0,\ldots,y_{n-1}]$ is polynomial and
$R_k/J_k\simeq A_k$. The complete multiplication on this free
$A_k$-module is

$$
\rho(X^s)=y^{a(s)}N^{\delta(s)},\qquad
Ne_2=0,\quad Ne_j=e_{j-1}\ (j\ge3),
\quad N^{k-2}=0.
\tag{31.7}
$$

Here $N$ is $A_k$-linear of ordinary degree $-2$, $N^0$ is the
identity, and $y^a=\prod_i y_i^{a_i}$. Thus $X^se_j$ is nonzero
exactly when $\delta(s)\le j-2$, and then it equals
$y^{a(s)}e_{j-\delta(s)}$. In particular the free layers in (31.6)
are not a direct sum of $R_k$-submodules when $k\ge4$.

Proof and attribution of the intermediate classification.
The canonical classification and the free face layers are the general
odd-cycle results of Miyazaki, *Non-Gorenstein locus and almost
Gorenstein property of the Ehrhart ring of the stable set polytope of
a cycle graph*, [§4, Lemmas 4.1–4.4 and the argument before
Theorem 4.5][MI31]. The correspondence is his $\ell=k$, his vertex
function $\eta(v_i)=c_i$, his $\eta(-\infty)=m$, his $\eta_j=\nu_j$,
and his $R^{(0)}=A_k$. His $C_j$ is the layer $A_ke_j$ before
passing to the quotient, and his $\operatorname{Cok}\varphi$ is
$\mathcal C_k(3)$, because his injection is into $\omega_{R_k}(3)$.
These supplied classification statements are intermediate inputs to
the action (31.7) and its comparison to the trace and index below.
The following proof gives all general-$k$ details needed for that
application in the coordinates of (31.1).

### 31.2 Coordinate feasibility and the canonical generators in Theorem 31.3

The two index identities

$$
B_i(a)+B_{i+1}(a)=|a|-a_i,
\qquad \sum_i B_i(a)=k|a|
\tag{31.8}
$$

hold because the two alternating index sets partition all indices
except $i$, and each coordinate occurs in exactly $k$ of the sums.
For $(m,c)$, summing the edge slacks gives
$|a|=nm-2\sum c_i=m+2\delta$. The candidate
$B_i(a)-\delta$ has adjacent sums
$|a|-a_i-2\delta=m-a_i$, the same as $c_i+c_{i+1}$.
A difference vector with zero adjacent sums alternates sign around
the odd ring, so it is zero. This proves both inverse formulas in
(31.4), and all the maps are additive integer-linear maps.

The forward feasibility conditions follow from $a_i\ge0$, $\delta\ge0$
and $c_i=B_i(a)-\delta\ge0$. Conversely, suppose (31.5) holds and
define $m,c$ by (31.4). The coordinates $c_i$ are nonnegative integers.
Nonnegativity of $m$ requires proof as well: summing
$\delta\le B_i(a)$ gives $n\delta\le k|a|$, whence

$$
n m=n|a|-2n\delta\ge(n-2k)|a|=|a|\ge0.
\tag{31.9}
$$

Thus $m\ge0$. Formula (31.8) gives
$c_i+c_{i+1}=m-a_i\le m$ and
$km-\sum c_i=\delta\ge0$. Hence $(m,c)\in\mathcal S_k$.
This includes $m=0$: (31.9) forces $a=0$ and then $\delta=c=0$.
The supplied integer decomposition consequently realizes every point
of (31.5) by common histories. If $m$ is fixed in advance, its slack
vector already determines

$$
\delta=\frac{|a|-m}{2},\qquad
c_i=B_i(a)-\frac{|a|-m}{2}.
\tag{31.10}
$$

In that fixed-degree domain, feasible $a$ have the indicated parity
and bounds; there is no additional missing deficit to recover.
The usefulness of $(a,\delta)$ is that it expresses multiplication
across all degrees additively.

Normality is the general odd-cycle cone argument of §29.2, applied to
the polytope and integer decomposition of Theorem 28.2: the zero mode
and singleton modes generate the full group $\mathbb Z^{n+1}$, and
$\mathcal S_k$ is the intersection of its rational cone with that
lattice. Its generators have degree one, so the ring is standard
graded; the cone is full dimensional and has group rank $n+1$.
The facet verification in §29.2 applies to every $2k+1\ge5$.
Consequently an exponent is interior precisely when

$$
c_i\ge1,\qquad a_i\ge1,\qquad\delta\ge1.
\tag{31.11}
$$

Hochster's Cohen–Macaulay theorem and the Danilov–Stanley description
of the canonical module now apply. A multigraded reference with the
needed hypotheses is Barile–Bruns, *$\mathbb Z^r$-graded rings and
their canonical modules*, [§5 and Theorem 5.1][BB31]. Here their
normal affine monoid $M$ is $\mathcal S_k$, their $r$ is $n+1$ and
their coefficient field is $\mathbb C$; the cone is pointed and the
group lattice is full, as checked above. The theorem identifies
$\omega_{R_k}$ with the monomial ideal (31.11), while the domain
property follows from its inclusion in a polynomial ring.

For each $1\le j\le k-1$, $\nu_j$ has slack vector $\mathbf1$,
deficit $k-j$, and positive occupancy $j\mathbf1$. Thus it is interior.
Let $p=(m,c)$ be any interior exponent. If $\delta(p)\ge k-1$,
subtract $\nu_1=(3;\mathbf1)$. The degree is nonnegative because
$c_i,c_{i+1}\ge1$ and $c_i+c_{i+1}\le m-1$ imply $m\ge3$.
The remaining occupancies are nonnegative, its edge sums are at most
$m-3$, and its deficit is $\delta(p)-(k-1)\ge0$. Therefore
$p-\nu_1\in\mathcal S_k$.

If $1\le\delta(p)\le k-2$, set $j=k-\delta(p)$, so
$2\le j\le k-1$. Delete position $i$ and partition the remaining
$2k$ positions into the $k$ edges
$\{i+1,i+2\},\ldots,\{i+2k-1,i+2k\}$. Their strict edge bounds give

$$
km-\delta(p)=\sum_r c_r\le c_i+k(m-1),
\qquad c_i\ge k-\delta(p)=j.
\tag{31.12}
$$

This holds for every $i$, so $m\ge2j+1$ by an edge bound.
The exponent $p-\nu_j$ has nonnegative degree and coordinates,
edge sums at most $m-(2j+1)$, and deficit zero. It is a face point.
Conversely adding $\nu_j$ to any semigroup point preserves (31.11).
These two cases prove generation by the stated $k-1$ monomials.

To prove minimality without overlooking a possible smaller interior
divisor, suppose $\nu_j-s$ is interior for some
$s=(q,b)\in\mathcal S_k$. Its edge slacks are $1-a_i(s)$ and
must be at least one. Since $a_i(s)\ge0$, all $a_i(s)$ vanish.
Thus $b_i+b_{i+1}=q$ on every edge. Oddness forces $b_i=q/2$ for
every $i$. The global inequality for $s$ then gives
$nq/2\le kq$, so $q\le0$. As $q\ge0$, $q=0$ and $b=0$.
No nonzero semigroup exponent can be subtracted from any $\nu_j$
while remaining interior. Generation proves that every other
interior exponent has one of these as a divisor; if it is different,
that divisor uses a nonzero semigroup remainder. Thus there are
exactly these minimal exponents. Monomial independence extends the
minimality assertion to generators of the ideal, not just to a list
of monomials.

### 31.3 Free face layers and their multiplication in Theorem 31.3

At $\delta=0$, (31.4) becomes the additive bijection

$$
\mathbb N^n\longrightarrow\{s\in\mathcal S_k:\delta(s)=0\},
\qquad a\longmapsto(|a|,B(a)).
\tag{31.13}
$$

It takes the standard basis vectors to the modes (31.3), so distinct
monomials in the $y_i$ have distinct semigroup exponents and every
face monomial is one of them. This proves the polynomial presentation
of $A_k$, with $\deg y_i=1$. The map $\pi:R_k\to A_k$ that fixes
face monomials and kills positive-deficit monomials is multiplicative:
the deficit of a product is zero exactly when both factors have
deficit zero. Hence $\ker\pi=J_k$ and $R_k/J_k\simeq A_k$.

The image $X^{\nu_1}R_k$ consists exactly of the interior monomials
of deficit at least $k-1$, by the first case of the generation proof.
Every remaining interior exponent has a unique deficit $k-j$ with
$2\le j\le k-1$, and the second case gives its unique form

$$
p=\nu_j+(|b|,B(b)),\qquad b=a(p)-\mathbf1\in\mathbb N^n.
\tag{31.14}
$$

The uniqueness of $j$ comes from deficit and the uniqueness of $b$
comes from slack. Within a layer the face monomials are independent;
different layers have different deficits and are independent as well.
Thus their images give exactly the $A_k$-free direct sum in (31.6).
Multiplication by the nonzero monomial $X^{\nu_1}$ is injective in
the domain $R_k$, which proves the displayed exact sequence.

For $s=(m,c)\in\mathcal S_k$ write $d=\delta(s)$. Multiplying $e_j$
by $X^s$ gives an interior exponent of deficit $k-j+d$.
It vanishes in the quotient if and only if $k-j+d\ge k-1$,
equivalently $d\ge j-1$. Otherwise $j-d\ge2$, and

$$
\nu_j+s-\nu_{j-d}=(m+2d;c+d\mathbf1).
\tag{31.15}
$$

This exponent has nonnegative coordinates and degree, slack $a(s)$,
and deficit
$k(m+2d)-\sum_i(c_i+d)=d+(2k-n)d=0$.
It therefore is the face point of (31.13) with exponent $a(s)$,
and its monomial is $y^{a(s)}$. This proves (31.7) on every basis
vector, including the precise condition for a nonzero image.

The formula also proves directly that it is an honest algebra action.
Scalars $y^a$ commute with $N$, $a(s+t)=a(s)+a(t)$ and
$\delta(s+t)=\delta(s)+\delta(t)$, so

$$
\rho(X^{s+t})=
y^{a(s)+a(t)}N^{\delta(s)+\delta(t)}
=\rho(X^s)\rho(X^t).
\tag{31.16}
$$

The same equality covers products that hit the bottom layer, because
both sides then act by zero. The zero semigroup element gives the
identity, and extending linearly proves the representation law for
arbitrary polynomials in $R_k$. It respects ordinary degrees:
$|a(s)|=m+2d$, so multiplication by $y^{a(s)}N^d$ has degree
$m+2d-2d=m$. In the full multigrading the lowering map has degree
$(-2;-\mathbf1)$, while the face coefficient has degree
$(m+2d;c+d\mathbf1)$, again giving degree $s$.

The successive sums $\bigoplus_{r=2}^jA_ke_r$ are $R_k$-submodules;
their successive quotients are $A_k(-(2j+1))$ with action through
$\pi$. This is a filtration, not an assertion that those successive
quotients split as $R_k$-modules. For $k\ge4$, any mode of size $k-1$
has deficit one and sends $e_3$ to a nonzero multiple of $e_2$.
Thus the layer $A_ke_3$ itself is not stable. When $k=3$ there is
only $e_2$, $N=0$, and (31.6)–(31.7) are exactly the seven-position
quotient of (29.4), with the change from degree labels $\nu_3,\nu_5$
there to subscripts $\nu_1,\nu_2$ here. No additional seven-cycle
classification is needed. This completes the proof. $\square$

### 31.4 The annihilator and a nine-position matrix

**Proposition 31.4 (Sharp nilpotence and the ideal it does not identify).**
The positive-deficit ideal satisfies

$$
J_k^{k-2}\mathcal C_k=0,\qquad
J_k^{k-3}\mathcal C_k\ne0,
\tag{31.17}
$$

and the full annihilator is

$$
\operatorname{Ann}_{R_k}\mathcal C_k
=\operatorname{span}_{\mathbb C}
 \{X^s:s\in\mathcal S_k,\ \delta(s)\ge k-2\}.
\tag{31.18}
$$

Its radical is $J_k$. For $k=3$, (31.18) is $J_k$; for $k\ge4$
it is strictly larger than $J_k^{k-2}$ and strictly smaller than $J_k$.

Proof. Every product of $r$ positive-deficit monomials has deficit at
least $r$. Formula (31.7) annihilates all layers at deficit at least
$k-2$, which proves the first assertion of (31.17).
The legal set $I=\{0,2,\ldots,2k-4\}$ has size $k-1$ and its
mode $s_I=(1,\mathbf1_I)$ has deficit one. Consequently

$$
(X^{s_I})^{k-3}e_{k-1}
=y^{(k-3)a(s_I)}e_2\ne0.
\tag{31.19}
$$

For $k=3$ the exponent is zero: $J_k^0=R_k$, the monomial power is
$1$, $N^0=\mathrm{id}$, and the right side is $e_2\ne0$.
This proves sharpness in that endpoint case as well.

All monomials on the right of (31.18) annihilate $\mathcal C_k$.
For the converse, combine equal monomials in a nonzero polynomial
$f=\sum_s\lambda_sX^s$ and apply it to the highest layer $e_{k-1}$.
The surviving terms have $0\le\delta(s)\le k-3$ and are

$$
\lambda_s y^{a(s)}e_{k-1-\delta(s)}.
\tag{31.20}
$$

Different deficits give different basis layers. At a fixed deficit,
different semigroup exponents have different slack vectors by
(31.4), so their face monomials are linearly independent. No
cancellation of surviving terms is possible. Thus $f$ annihilates
the module only if every term has deficit at least $k-2$, proving
the entire polynomial annihilator, not just its monomial elements.

The inclusions $J_k^{k-2}\subseteq\operatorname{Ann}\mathcal C_k
\subseteq J_k$, together with $R_k/J_k=A_k$ a domain, give the
radical assertion. For $k\ge4$, the deficit-one mode just used lies
in $J_k$ but not in the annihilator. On the other side the empty
mode $X^{(1,0)}$ has deficit $k$ and therefore belongs to the
annihilator. It cannot lie in $J_k^{k-2}$: each nonzero homogeneous
element of $J_k$ has degree at least one, and $k-2\ge2$, whereas
this empty mode has degree one. Hence the inclusions are strict.
The nilpotence of an ideal action consequently does not identify
its annihilator with that ideal power. $\square$

**Proposition 31.5 (The first two-layer action).**
For $n=9$, $k=4$, in the ordered basis $(e_2,e_3)$ and the
zero-based mode $I=\{0,2,4\}$, one has

$$
\delta(s_I)=1,\quad
a(s_I)=(0,0,0,0,0,1,1,1,0),\qquad
\rho(X^{s_I})=
\begin{pmatrix}0&y_5y_6y_7\\0&0\end{pmatrix}.
\tag{31.21}
$$

Proof. Its occupied positions are pairwise nonadjacent, including
across the seam. Every edge except $\{5,6\}$, $\{6,7\}$ and
$\{7,8\}$ has one occupied endpoint; those three edges have none.
This gives the displayed slack vector, and $4-|I|=1$ gives deficit.
Formula (31.7) yields $X^{s_I}e_3=y_5y_6y_7e_2$ and
$X^{s_I}e_2=0$, so the columns of the matrix are exactly the stated
images. The polynomial entry has degree three and the lowering has
degree minus two, making the action degree one as required.
The square of this matrix is zero although the matrix is nonzero.
It records multiplication between canonical layers; it is not a
physical-time evolution or a native execution step. $\square$

[MI31]: https://arxiv.org/html/2205.01409v1
[BB31]: https://arxiv.org/html/2505.11402v1

## 32. The canonical correction as a difference of trace errors at two degrees

### 32.1 Counts of the supplied layers in the common-copy observation

**Definition 32.1 (Interior correction and local trace excess).**
Keep $n=2k+1$, $k\ge3$, and write
$L_n(m)=L_n^{\mathrm{cyc}}(m)$ for $m\ge0$, with $L_n(m)=0$ for
negative integer $m$. Let $L_n^\circ(m)$ count the interior lattice
points of $mQ_n$ for $m>0$, and set $L_n^\circ(0)=0$.
Define

$$
C_k(m)=\dim_{\mathbb C}(\mathcal C_k)_m,\qquad
E_k(q)=\operatorname{Tr}(T_q^n)-L_n(q)\quad(q\ge0),
\tag{32.1}
$$

and set $C_k(m)=0$ and $E_k(q)=0$ for negative integer arguments.
Here $T_q(a,b)=\mathbf1_{a+b\le q}$ for $0\le a,b\le q$, exactly
as in (28.4). In particular $E_k(q)$ is $E_{2k+1}(q)$ in the
notation of Proposition 28.3. The trace counts position-labelled
local tuples, without identifying rotations. It does not already
enforce the global common-copy constraint.

**Theorem 32.2 (The finite band of trace errors measured by the canonical
quotient).** For every integer $m\ge0$,

$$
\begin{aligned}
C_k(m)
&=\sum_{j=2}^{k-1}\dim(A_k)_{m-2j-1}\\
&=\sum_{j=2}^{k-1}\binom{m+2k-2j-1}{2k}\\
&=E_k(m-3)-E_k\bigl(m-(2k-1)\bigr).
\end{aligned}
\tag{32.2}
$$

Each binomial is the corresponding homogeneous polynomial-space
dimension and is zero when $m<2j+1$. In particular for $m\ge3$,

$$
L_n^\circ(m)=L_n(m-3)+C_k(m),\qquad
H_{\mathcal C_k}(t)=
\frac{t^5+t^7+\cdots+t^{2k-1}}{(1-t)^{2k+1}}.
\tag{32.3}
$$

The two-scale difference has a bijection proof: after subtracting
$\mathbf1$ from an interior occupancy vector and three from its
degree, the quotient keeps exactly excesses $1,\ldots,k-2$ above
the global bound. The remaining excess tail is a translate of the
entire local trace error in degree $m-(2k-1)$.

Proof. The exact sequence (31.6) in degree $m$ gives
$\dim(\omega_{R_k})_m=\dim(R_k)_{m-3}+C_k(m)$.
The first term counts interior monomials, and standard grading and
the integer decomposition identify the second term with $L_n(m-3)$.
The $A_k$-basis in that theorem gives the first sum in (32.2).
Stars and bars in its $n=2k+1$ degree-one variables gives
$\dim(A_k)_d=\binom{d+2k}{2k}$ for $d\ge0$, and zero otherwise.
This proves the binomial sum and the Hilbert series. No splitting of
$R_k$-modules has been used in taking these dimensions.

For the trace comparison use the slack/excess bijection already proved
in Theorem 28.2. A tuple counted by the error in degree $q\ge0$
has excess $\ell=\sum b_i-kq>0$ and slack
$a_i=q-b_i-b_{i+1}\ge0$. Its exact parameters and inverse are

$$
1\le\ell\le\lfloor q/2\rfloor,\qquad
|a|=q-2\ell,\qquad b_i=B_i(a)+\ell.
\tag{32.4}
$$

The forward and inverse nonnegativity and odd-cycle uniqueness are
the statements of (28.11)–(28.12), now with $j=\ell$, $m=q$ and
the zero-based indices of (31.1). Thus, as the supplied trace-error
formula in this notation,

$$
E_k(q)=\sum_{\ell=1}^{\lfloor q/2\rfloor}
\binom{q-2\ell+2k}{2k},\qquad
H_{E_k}(t)=\frac{t^2}{(1-t^2)(1-t)^{2k+1}}.
\tag{32.5}
$$

These formulas retain their original domain of locally feasible
tuples failing the global inequality. The new comparison is which
part of that domain becomes the interior quotient.

### 32.2 The retained band and the entire translated tail

For $m\ge3$ set $q=m-3$ and $b=c-\mathbf1$. The strict inequalities
for an interior exponent $(m,c)$ become

$$
b_i\ge0,\qquad b_i+b_{i+1}\le q,\qquad
\sum_i b_i\le kq+(k-2).
\tag{32.6}
$$

Indeed the global bound is
$\sum c_i\le km-1=k(q+3)-1$, and subtracting $n=2k+1$ gives
$kq+k-2$. This is the same interior translation as (29.10).
Those tuples with $\sum b_i\le kq$ correspond precisely to the
interior exponents in $\nu_1+\mathcal S_k$ of degree $m$, whose
monomials are removed in $\mathcal C_k$.
The remaining tuples have

$$
\sum_i b_i=kq+\ell,\qquad 1\le\ell\le k-2,
\qquad \delta(m,c)=k-1-\ell.
\tag{32.7}
$$

The last equality follows by substituting
$m=q+3$ and $\sum c_i=kq+\ell+n$ into $km-\sum c_i$.
In particular this is the layer $j=\ell+1$ of (31.14).
Conversely a locally feasible $b$ of excess in this range gives
$c=b+\mathbf1$ satisfying all strict inequalities, and has deficit
between one and $k-2$; it therefore represents a nonzero quotient
monomial. The correspondence is inverse in both directions.

It remains to remove all larger excesses, not merely compare two
formal series. Write $h=k-2$ and let

$$
\mathcal T(q)=\{b\in\mathbb Z_{\ge0}^n:
 b_i+b_{i+1}\le q,\ \sum_i b_i=kq+\ell
 \text{ for some }\ell\ge h+1\}.
\tag{32.8}
$$

For $b\in\mathcal T(q)$, (32.4) gives
$b_i=B_i(a)+\ell\ge\ell\ge h+1$ and $q=|a|+2\ell$.
Consequently

$$
q'=q-2h\ge2,
\qquad b'=b-h\mathbf1\in\mathbb Z_{\ge0}^n,
\qquad b'_i+b'_{i+1}\le q'.
\tag{32.9}
$$

The excess of $b'$ is

$$
\sum_i b'_i-kq'
=(kq+\ell)-nh-k(q-2h)=\ell-h\ge1,
\tag{32.10}
$$

since $n-2k=1$. Its slack vector is unchanged, and its inverse in
(32.4) is $b'_i=B_i(a)+(\ell-h)$. This proves that (32.9) maps
the whole tail into the domain counted by $E_k(q')$.

Conversely take any tuple counted by $E_k(q')$ for $q'\ge0$.
Let its excess be $\ell'\ge1$, put $q=q'+2h$ and
$b=b'+h\mathbf1$. These coordinates are nonnegative and their
edge sums are at most $q$. Their total excess is

$$
\sum_i b_i-kq
=(kq'+\ell')+nh-k(q'+2h)=\ell'+h\ge h+1.
\tag{32.11}
$$

Thus $b\in\mathcal T(q)$, and subtraction recovers $b',q'$.
If $q'=q-2h<0$, no tail can exist, because its first direction
would force $q'\ge2$. If $q'=0$ or $1$, the source of this
inverse is empty by $\ell'\le\lfloor q'/2\rfloor$, and the tail
is empty as well. These observations include every low-degree
case; they do not treat negative parameters as occupancy spaces.
Therefore $|\mathcal T(q)|=E_k(q-2h)$ with the zero convention of
Definition 32.1. Removing the tail from all errors in degree $q$
leaves exactly (32.7), proving

$$
C_k(m)=E_k(q)-E_k(q-2h)
=E_k(m-3)-E_k(m-(2k-1))
\tag{32.12}
$$

for $m\ge3$. At $m=0,1,2$, both error arguments are negative
and $C_k(m)=0$ by its smallest generator degree five, so the
identity holds for all $m\ge0$.

The generating-function form records the same degree translations:

$$
\begin{aligned}
H_{\mathcal C_k}(t)
&=(t^3-t^{2k-1})H_{E_k}(t)\\
&=\frac{t^5(1-t^{2(k-2)})}{(1-t^2)(1-t)^{2k+1}}
=\frac{\sum_{j=2}^{k-1}t^{2j+1}}{(1-t)^{2k+1}}.
\end{aligned}
\tag{32.13}
$$

In particular $E_k(m)$ itself is not the canonical correction in
degree $m$. The subtraction of two translated errors selects its
finite excess band. $\square$

**Proposition 32.3 (The first correction dimensions).**
The canonical degrees and the corrections in the first three
odd lengths of this application are

| Positions $n$ | Canonical generator degrees | $C_k(5)$ | $C_k(6)$ | $C_k(7)$ | $C_k(8)$ | $C_k(9)$ |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 7 | $3,5$ | 1 | 7 | 28 | 84 | 210 |
| 9 | $3,5,7$ | 1 | 9 | 46 | 174 | 540 |
| 11 | $3,5,7,9$ | 1 | 11 | 67 | 297 | 1068 |

For all three rows, $C_k(m)=0$ for $0\le m\le4$.

Proof. The canonical degrees are $2j+1$ for $1\le j\le k-1$;
the quotient omits degree three. For seven positions its count is
$\binom{m+1}{6}$. For nine positions it is
$\binom{m+3}{8}+\binom{m+1}{8}$, and for eleven it is
$\binom{m+5}{10}+\binom{m+3}{10}+\binom{m+1}{10}$.
All terms use the homogeneous-degree convention of (32.2).
For example at $m=7$ the three counts are respectively
$28$, $45+1=46$, and $66+1+0=67$; at $m=9$ they are
$210$, $495+45=540$, and $1001+66+1=1068$.
At $m=8$ they are $84$, $165+9=174$, and $286+11=297$.
The remaining displayed entries are the constant and linear face
degrees, and the zero range precedes the first quotient generator.
The first row is the correction already used in (29.5) and (30.16).
$\square$

## 33. The canonical layers determine every terminal mode multidegree

**Definition 33.1 (The polynomial presentation in all cyclic modes).**
Let

$$
S_n=\mathbb C[z_I:I\in\mathcal B_n],\qquad
z_I\longmapsto X^{(1,\mathbf1_I)},\qquad
\gamma_I=\deg z_I=(1,\mathbf1_I).
\tag{33.1}
$$

This is the cyclic mode presentation of (28.14), now using the
zero-based positions of Definition 31.1. Its image is $R_k$ by the
common-copy integer decomposition. Put $D_n=|\mathcal B_n|$ and
$\Sigma_n=\sum_{I\in\mathcal B_n}\gamma_I$.
Use $F_\bullet$ for a minimal multigraded free resolution of $R_k$
over $S_n$. The symbol $F_i$ for a free module is distinct from the
Fibonacci numbers $F_r^{\mathrm{Fib}}$, which here satisfy
$F_0^{\mathrm{Fib}}=0$, $F_1^{\mathrm{Fib}}=1$ and the usual recursion.

**Theorem 33.2 (Terminal syzygies of the algebra carrying the layer action).**
For this exact mode presentation,

$$
\begin{aligned}
D_n&=F_{n-1}^{\mathrm{Fib}}+F_{n+1}^{\mathrm{Fib}},\\
\Sigma_n&=(D_n;F_{n-1}^{\mathrm{Fib}}\mathbf1),\qquad
p_n=\operatorname{pd}_{S_n}R_k=D_n-n-1,\\
F_{p_n}&=\bigoplus_{j=1}^{k-1}S_n(-\Theta_j),\\
\Theta_j&=\Sigma_n-\nu_j
=\bigl(D_n-(2j+1);(F_{n-1}^{\mathrm{Fib}}-j)\mathbf1\bigr).
\end{aligned}
\tag{33.2}
$$

Thus the last module has rank $k-1$. The same interior degrees
$\nu_j$ that define the canonical layers and the action (31.7)
give all these terminal multidegrees by subtraction from the sum
of the actual mode degrees. This statement specifies the final
module; it does not specify all differential matrices.

Proof. Independent sets in a path of $r\ge0$ positions are counted
by $F_{r+2}^{\mathrm{Fib}}$: split according to whether the first
position is unoccupied or occupied, leaving paths of lengths
$r-1$ and $r-2$, with initial counts one and two for lengths zero
and one. In the $n$-cycle, sets omitting position zero leave a
path of length $n-1$, with count $F_{n+1}^{\mathrm{Fib}}$.
Sets containing zero omit its two neighbors and leave a path of
length $n-3$, with count $F_{n-1}^{\mathrm{Fib}}$.
This proves the first formula. The latter argument at any fixed
position proves that it occurs in exactly $F_{n-1}^{\mathrm{Fib}}$
mode variables. Summing the degree vectors therefore gives the
second formula, including every occupancy coordinate.

The ring $R_k$ has dimension and depth $n+1$ by Theorem 31.3,
whereas the polynomial ring $S_n$ has dimension $D_n$.
Auslander–Buchsbaum at the homogeneous maximal ideal, as in
[Stacks, Proposition 10.111.1, section 090U][AB27], gives
$p_n=D_n-n-1$. A minimal multigraded resolution exists by choosing
minimal homogeneous generators successively; Hilbert syzygy gives
a finite free resolution, and its minimal length is this projective
dimension. These are the same hypotheses used in §29.4 for seven
positions, now for the mode set (33.1).

The polynomial canonical module is $\omega_{S_n}=S_n(-\Sigma_n)$:
the top exterior product of the variable differentials has degree
the sum of their degrees. The precise multigraded canonical-Ext
input is [Barile–Bruns, Theorem 4.5(a)][BB31]. Their regular
graded-local ring is $S_n$, its homogeneous maximal ideal is
$(z_I)_I$, and its Cohen–Macaulay residue ring is the stated
quotient $R_k$. The codimension is $p_n$, so their result and its
Ext vanishing give

$$
\operatorname{Ext}^{p_n}_{S_n}(R_k,S_n(-\Sigma_n))
\simeq\omega_{R_k},\qquad
\operatorname{Ext}^{i}_{S_n}(R_k,S_n(-\Sigma_n))=0
\quad(i\ne p_n).
\tag{33.3}
$$

In particular the canonical module used here has the same full
grading as the interior ideal, by their Theorem 5.1 and the
correspondence in the proof of Theorem 31.3.

Dualizing $F_\bullet$ into $S_n(-\Sigma_n)$ shows that
$\omega_{R_k}$ is the cokernel of the map into
$\operatorname{Hom}_{S_n}(F_{p_n},S_n(-\Sigma_n))$.
Minimality means that every original differential has entries in
$(z_I)_I$; the dual map has this property too. Reducing its
cokernel modulo that maximal ideal therefore leaves one basis
vector for every summand of this final dual free module, with
its degree unchanged. If the original summand is $S_n(-\Theta)$,
the dual summand has generator degree $\Sigma_n-\Theta$.
The minimal generator degrees of $\omega_{R_k}$ are exactly
$\nu_1,\ldots,\nu_{k-1}$, each once, by the generation and
minimality proof in §31.2. There are no others. Equating these
degrees gives precisely all the summands in (33.2).
This argument uses the actual canonical module and minimal
resolution, not just an alternating Hilbert numerator. $\square$

**Proposition 33.3 (Terminal degree table in the first three lengths).**
In the order $j=1,\ldots,k-1$, the complete terminal data are

| $n$ | $D_n$ | $F_{n-1}^{\mathrm{Fib}}$ | $\dim R_k$ | $p_n$ | Last ordinary degrees | Last occupancy degrees | Last rank |
| ---: | ---: | ---: | ---: | ---: | --- | --- | ---: |
| 7 | 29 | 8 | 8 | 21 | $26,24$ | $7\mathbf1,6\mathbf1$ | 2 |
| 9 | 76 | 21 | 10 | 66 | $73,71,69$ | $20\mathbf1,19\mathbf1,18\mathbf1$ | 3 |
| 11 | 199 | 55 | 12 | 187 | $196,194,192,190$ | $54\mathbf1,53\mathbf1,52\mathbf1,51\mathbf1$ | 4 |

Proof. The Fibonacci values required are
$F_6^{\mathrm{Fib}}=8$, $F_8^{\mathrm{Fib}}=21$,
$F_{10}^{\mathrm{Fib}}=55$, and $F_{12}^{\mathrm{Fib}}=144$.
Thus $D_7=8+21=29$, $D_9=21+55=76$, and
$D_{11}=55+144=199$. Subtract $n+1$ for the projective dimensions;
subtract the canonical ordinary degrees $3,5,\ldots,2k-1$ for
the last ordinary degrees, and subtract $j$ from the fixed-position
count for each occupancy coordinate. These operations give every
entry of the table by (33.2). The seven-position row is exactly
(29.6). The indices $21,66,187$ are homological lengths, with no
interpretation as temporal operations. $\square$

## 34. A smooth index for the layers and its loss of the nilpotent action

### 34.1 The carrier after restricting to the face algebra

**Definition 34.1 (The bundle and the positive Dolbeault operator).**
Restrict scalars in $\mathcal C_k$ along $A_k\hookrightarrow R_k$.
By (31.6) its associated bundle on the smooth projective space
$X_k=\operatorname{Proj}A_k=\mathbb {CP}^{2k}$, twisted by $m$, is

$$
\mathcal E_{k,m}
=\widetilde{\operatorname{Res}_{A_k}^{R_k}\mathcal C_k}(m)
=\bigoplus_{j=2}^{k-1}\mathcal O_{X_k}(m-2j-1).
\tag{34.1}
$$

Take $m\ge0$, the Fubini–Study metric on $X_k$, and smooth
Hermitian metrics on the line bundles. Let
$\mathscr E_{k,m}^{+}=\Lambda^{0,\mathrm{even}}T^*X_k\otimes
\mathcal E_{k,m}$ and
$\mathscr E_{k,m}^{-}=\Lambda^{0,\mathrm{odd}}T^*X_k\otimes
\mathcal E_{k,m}$, where parity is the Dolbeault form degree.
Write $\bar\partial_{\mathcal E}$ for the holomorphic Dolbeault
differential and $\bar\partial_{\mathcal E}^{\dagger}$ for its
formal adjoint. Define

$$
D_{k,m}=\sqrt2\bigl(\bar\partial_{\mathcal E}
+\bar\partial_{\mathcal E}^{\dagger}\bigr),\qquad
D_{k,m}^+:H^1(X_k,\mathscr E_{k,m}^+)
\longrightarrow L^2(X_k,\mathscr E_{k,m}^-).
\tag{34.2}
$$

Here $H^1$ is the first Sobolev space; sheaf cohomology will always
be written as $H^q(X_k,\mathcal E_{k,m})$.
The differential expression $D_{k,m}^-$ is the restriction from odd
to even forms. This is the twisted Dolbeault–Dirac operator for the
canonical complex $\operatorname{Spin}^c$ structure. No ordinary
spin structure or boundary condition is part of the definition.
Restriction to $A_k$ in (34.1) is essential: this construction has
forgotten the extra multiplication maps (31.7).

**Theorem 34.2 (The common-copy defect is a smooth positive index).**
For every $k\ge3$ and $m\ge0$, (34.2) is elliptic Fredholm,
its weak kernel vectors are smooth, and

$$
\ker D_{k,m}^+\simeq(\mathcal C_k)_m,\qquad
\ker D_{k,m}^-=0,\qquad
\operatorname{ind}D_{k,m}^+=C_k(m).
\tag{34.3}
$$

The first isomorphism uses harmonic representatives and the
$A_k$-basis $e_j$; it is an isomorphism of vector spaces in the
stated degree, not a recovery of the full $R_k$-action. If
$h=c_1(\mathcal O_{X_k}(1))$ and $\int_{X_k}h^{2k}=1$, the same
number is

$$
\begin{aligned}
\operatorname{ind}D_{k,m}^+
&=\int_{\mathbb {CP}^{2k}}
\left(\sum_{j=2}^{k-1}e^{(m-2j-1)h}\right)
\left(\frac{h}{1-e^{-h}}\right)^{2k+1}\\
&=\sum_{j=2}^{k-1}\binom{m+2k-2j-1}{2k}\\
&=E_k(m-3)-E_k(m-(2k-1)).
\end{aligned}
\tag{34.4}
$$

Proof. The projective-space cohomology input is [Stacks Lemma
30.8.1, tag 01XT][PC25], in the context of [section 30.8, tag
01XS][PC34]. For $r\ge1$, it identifies $H^0(\mathbb P^r,\mathcal
O(d))$ with degree-$d$ homogeneous polynomials when $d\ge0$.
There is no intermediate cohomology. For $-r\le d\le-1$ all
cohomology vanishes; the negative top cohomology starts only at
$d\le-r-1$, since its basis consists of Laurent monomials with
all $r+1$ exponents strictly negative.

Here $r=2k$ and the smallest twist in (34.1) is

$$
d_{\min}=m-(2k-1)\ge-(2k-1)>-(2k+1).
\tag{34.5}
$$

Thus every summand has zero higher cohomology. A summand with
negative twist lies in the acyclic range, so it contributes zero
even to $H^0$. This is precisely the convention that negative
homogeneous polynomial degrees are zero; no negative-copy space
is introduced. Algebraic and analytic cohomology agree by the
Serre GAGA comparison [§12, Théorème 1][GA25], and the analytic
Dolbeault resolution therefore gives

$$
\begin{aligned}
H^0(X_k,\mathcal E_{k,m})
&=\bigoplus_{j=2}^{k-1}(A_k)_{m-2j-1}e_j
\simeq(\mathcal C_k)_m,\\
H^q(X_k,\mathcal E_{k,m})&=0\quad(q>0).
\end{aligned}
\tag{34.6}
$$

For the analytic bridge, the principal symbol of $D_{k,m}$ is the
Dolbeault Clifford symbol tensored with the identity on
$\mathcal E_{k,m}$. Wedge multiplication by the $(0,1)$ part of a
nonzero real cotangent vector and its adjoint contraction have
anticommutator equal to its squared norm times the identity.
With the differential symbol's factor of $\sqrt{-1}$, the symbol
of $D_{k,m}$ is consequently invertible off the zero section and
exchanges the two parities. Thus $D_{k,m}^+$ is elliptic.

On the compact smooth base the elliptic estimate
$\|u\|_{H^1}\le C(\|D_{k,m}^+u\|_{L^2}+\|u\|_{L^2})$,
the corresponding estimate for the formal adjoint, and Rellich
compactness give closed range and finite-dimensional kernel and
cokernel for (34.2). The cokernel is the orthogonal complement
of the range in $L^2$, hence consists of distributional solutions
of the formal adjoint equation $D_{k,m}^-v=0$.
Elliptic regularity makes both such solutions and the weak positive
kernel smooth. The closed differential operator on $L^2$ has
Sobolev domain $H^1$. This argument identifies its formal-adjoint
kernel with the cokernel; it does not equate the bounded Hilbert
adjoint of the map $H^1\to L^2$ with that differential expression
between the same two Hilbert spaces.

For a smooth form $u$, integration by parts gives

$$
\langle D_{k,m}^2u,u\rangle
=2\left(\|\bar\partial_{\mathcal E}u\|^2
+\|\bar\partial_{\mathcal E}^{\dagger}u\|^2\right).
\tag{34.7}
$$

The Hodge decomposition for this elliptic complex identifies its
harmonic forms in degree $q$ with $H^q(X_k,\mathcal E_{k,m})$.
All these groups vanish except degree zero by (34.6), so the
negative kernel is zero and the positive kernel is exactly the
stated polynomial-space sum. These are the classical Dolbeault,
Hodge and elliptic Fredholm inputs described in Freed, *The
Atiyah–Singer Index Theorem*, [§§3.1–3.2][FR34], applied to this
specific bundle and Sobolev domain. They prove (34.3), including
the kernel assertion stronger than an index equality alone.

The classical Hirzebruch–Riemann–Roch formula, equivalently the
Dolbeault case of Atiyah–Singer, gives
$\chi(X_k,\mathcal E)=\int_{X_k}\operatorname{ch}(\mathcal E)
\operatorname{Td}(TX_k)$; see [Freed, Theorem 2.7 and §4][FR34].
Additivity for the line bundles gives the sum of exponentials in
(34.4). The Euler sequence
$0\to\mathcal O\to\mathcal O(1)^{\oplus(2k+1)}\to TX_k\to0$
gives the displayed Todd factor. These are classical index inputs
to the count in (32.2), not assertions about a singular toric base.

One may also evaluate the coefficient directly, keeping negative
twists in their proper range. For an integer $d$ and $r=2k$, use
formal residues and the change of variable $u=1-e^{-h}$, whose
linear term is $h$:

$$
\begin{aligned}
[h^r]\ e^{dh}\left(\frac{h}{1-e^{-h}}\right)^{r+1}
&=\operatorname{Res}_{h=0}\frac{e^{dh}}{(1-e^{-h})^{r+1}}\,dh\\
&=\operatorname{Res}_{u=0}\frac{(1-u)^{-d-1}}{u^{r+1}}\,du\\
&=[u^r](1-u)^{-d-1}=\binom{d+r}{r}.
\end{aligned}
\tag{34.8}
$$

For $d\ge0$ this is the polynomial-space dimension. For
$-r\le d\le-1$, the middle series is a polynomial of degree at
most $r-1$, and its $u^r$ coefficient is zero. Thus (34.8) agrees
with every vanishing term in (34.6). Setting $d=m-2j-1$ and
summing proves the first two equalities in (34.4); Theorem 32.2
gives the final one. For $k=3$ this is precisely the single
$\mathcal O(m-5)$ face carrier of chapter 30, now with its
vanishing argument also valid at $m=0,1,2$. $\square$

### 34.2 The same index with a different action

**Definition 34.3 (A split comparison with the identical graded layers).**
On the graded $A_k$-module
$\bigoplus_{j=2}^{k-1}A_ke_j$ define a second $R_k$-module
$\mathcal C_k^{\mathrm{split}}$ by restriction of the action along
$\pi:R_k\to A_k$. Explicitly,

$$
\rho_{\mathrm{split}}(X^s)e_j=
\begin{cases}
y^{a(s)}e_j,&\delta(s)=0,\\
0,&\delta(s)>0.
\end{cases}
\tag{34.9}
$$

The ordinary grading and the basis degrees are unchanged. Since
$\pi$ is a graded algebra homomorphism, this is a well-defined
graded action, rather than an arbitrary collection of zero maps.

**Theorem 34.4 (Equality of all layer indices does not recover
the cyclic multiplication).**
The two modules $\mathcal C_k$ and $\mathcal C_k^{\mathrm{split}}$
have identical restrictions to $A_k$, identical graded dimensions
in every degree, and the identical bundle (34.1). For identical
metrics they therefore have the same operators (34.2) and all the
same indices (34.4). Nevertheless for every $k\ge4$ they are not
isomorphic as $R_k$-modules, even without a grading condition.
For $k=3$ their actions agree.

Under the mode presentation $S_n\to R_k$, the reduced face is the
linear subspace $\iota:\mathbb P^{2k}\hookrightarrow\mathbb P^{D_n-1}$
given by keeping the maximum-mode coordinates $z_{M_i}=y_i$ and
setting all smaller-mode coordinates to zero. The split module
has sheaf

$$
\widetilde{\mathcal C_k^{\mathrm{split}}}(m)
=\iota_*\mathcal E_{k,m}.
\tag{34.10}
$$

For $k\ge4$, the full $R_k$-module $\mathcal C_k$ does not have
that reduced-face pushforward sheaf. Its annihilator has radical
$J_k$, but its positive-deficit action remains nonzero after
localizing on a maximum-mode chart.

Proof. Both restrictions are literally
$\bigoplus_{j=2}^{k-1}A_k(-(2j+1))$, so their degree-$m$ dimensions
are both the sum in (32.2). Sheafification of these restricted
modules gives the same bundle, with the same holomorphic structure.
Choosing the same metrics gives the same Dolbeault differential,
formal adjoint, symbol, Sobolev realization and harmonic spaces.
Consequently (34.3)–(34.4) give the same index for every $m\ge0$;
the equality is not merely an agreement in one selected degree.

On the split module $J_k$ acts by zero. For $k\ge4$, $e_3$ is
present and the size-$(k-1)$ mode $s_I$ of (31.19) satisfies
$X^{s_I}e_3=y^{a(s_I)}e_2\ne0$ in the actual module.
If an $R_k$-linear isomorphism to the split module existed, it
would send this nonzero vector to
$X^{s_I}\phi(e_3)=0$, contradicting injectivity.
This proves the claimed nonisomorphism without any requirement
that the isomorphism preserve layer labels or degrees. For $k=3$
there is only $e_2$ and every positive deficit kills it by (31.7),
so (34.9) is its actual action.

More precisely, the successive layer filtration itself is
nonsplit above its first layer when $k\ge4$. For $3\le j\le k-1$,
a lift of the generator of the quotient
$A_ke_j$ in $\bigoplus_{r=2}^jA_ke_r$ has the form
$e_j+\sum_{r<j}f_re_r$. Multiplication by the deficit-one mode
$X^{s_I}$ has nonzero $e_{j-1}$ coefficient $y^{a(s_I)}$;
the lower terms land in layers at most $j-2$ and cannot cancel it.
The quotient generator is killed by $J_k$, so it admits no
$R_k$-linear section. Separately, the canonical exact sequence
(31.6) is nonsplit for every $k\ge3$: the nonzero empty mode
$X^{(1,0)}$ annihilates $\mathcal C_k$ by (31.18) but is a
nonzerodivisor on $\omega_{R_k}\subset R_k$. Hence every
$R_k$-linear map $\mathcal C_k\to\omega_{R_k}$ is zero,
whereas a section would be nonzero.

For the geometric assertion, $S_n\to R_k\to A_k$ kills exactly
the variables for independent sets of size less than $k$.
Every size-$k$ independent set is some $M_i$: such a set leaves
$k+1$ unoccupied vertices distributed among $k$ nonempty gaps,
so exactly one gap has length two and all others have length one.
Its unique edge with both endpoints unoccupied is $i,i+1$,
which determines $M_i$. The polynomial independence in (31.13)
therefore implies that the composite map's kernel consists exactly
of the smaller-mode variables. This proves the stated linear
closed immersion and, by localization on its standard charts,
the reduced-face sheaf identity (34.10), with the same ordinary
degree twists. It is the general version of the coordinate
identification (30.7)–(30.8) for a module whose action factors
through the face quotient.

The actual module has a different local action when $k\ge4$.
On any maximum-mode chart $y_r\ne0$, its localized degree-zero
module contains $e_3/y_r^7$, and

$$
\frac{X^{s_I}}{y_r}\,\frac{e_3}{y_r^7}
=\frac{y^{a(s_I)}e_2}{y_r^8}\ne0.
\tag{34.11}
$$

The degrees match since $|a(s_I)|=3$. Nonvanishing follows from
freeness over $A_k$ and the fact that its nonzero monomial
$y^{a(s_I)}$ remains nonzero after inverting $y_r$.
But $X^{s_I}/y_r$ belongs to the ideal of the reduced face, which
annihilates every sheaf pushed forward from that face. Thus the
actual sheaf cannot be (34.10). The radical support statement
is Proposition 31.4; the nonzero nilpotent action is information
additional to that reduced support. The bundle carrier in
Definition 34.1 is obtained by forgetting to $A_k$, not by
asserting that the full $R_k$-module already factors through the
reduced face. $\square$

**Proposition 34.5 (Scope of the linked observations).**
The maps in these chapters identify the following data of the
same cyclic common-copy algebra: the nonnegative slack/deficit
domain, the canonical quotient with its exact multiplication,
its correction to the interior count, its two-scale trace-error
difference, all terminal mode multidegrees, and the smooth index
of its restriction to the face algebra. They do not make the
index determine the relation maps or the full $R_k$-action, and
they do not make occupancy totals determine a supplied history.

Proof. The required correspondences are the inverse map (31.4),
the exponent difference (31.15), the band and tail bijections
(32.7)–(32.11), the canonical-Ext degree subtraction (33.3), and
the cohomology identification (34.6). Each retains the same
position and ordinary-degree conventions. In particular fixing
$m$ permits the deficit recovery (31.10); it does not recover
which histories contributed to $c$.
For any three consecutive positions, the two common arrays
$\{\{i\},\{i+2\}\}$ and
$\{\varnothing,\{i,i+2\}\}$ have identical totals and degree two,
but different frequencies of the five local modes. Both are legal
in every $n\ge7$ considered here, and they are not row permutations.
This is the common-copy ambiguity already exhibited in
Proposition 28.5. Theorem 34.4 supplies an independent ambiguity:
even all the bundle indices together fail to distinguish the
actual multiplicative action from the split one for $k\ge4$.

The canonical classification, polynomial face and free layers
used in the argument belong to Miyazaki's general odd-cycle
results; the multigraded canonical-module and Ext identifications
are the classical results supplied by Barile–Bruns; the
cohomology and index inputs are those of Stacks, GAGA and the
Dolbeault–Hirzebruch–Riemann–Roch theory cited above.
Their application here consists of the explicit slack/deficit
action, the two-scale error comparison, and the relation between
that algebraic information and the common-copy seam and smooth
index observations. Changing the labels does not constitute a
new general canonical classification or an originality claim.

The free-resolution calculation determines its last module and
length, without constructing all intervening matrices. The
elliptic calculation determines the stated index and, using the
proved vanishing range, the stated harmonic kernels. It does
not identify full positive spectra, metrics, native Hamiltonians,
preparation procedures or allowed physical operations. The
polytope facet is not an analytic boundary: $\mathbb {CP}^{2k}$
is smooth, compact and without boundary, so no APS boundary
condition or eta correction enters (34.4). The inverse maps and
the displayed counterexamples establish exactly these scopes.
$\square$

[PC34]: https://stacks.math.columbia.edu/tag/01XS
[FR34]: https://arxiv.org/html/2107.03557v1

## 追加锚（本行以下为增补区）

## 35. AURIC FIB-ATOM: shared-root gluing, synchronized irreducibility and canonical growth

### 35.1 One root, one degree and one array of rows

**Definition 35.1 (The shared-root occupancy algebra).**
Fix integers $k\ge2$ and $b\ge1$. Let $G_{k,b}$ consist of $b$
labelled copies of $C_{2k+1}$ meeting precisely at one vertex $o$.
On cycle $a$ use positions $0,1,\ldots,2k$, with position $0=o$;
write its other vertices as $(a,i)$, $1\le i\le2k$.
All these nonroot vertices are distinct, and the only edges are the
cyclic edges in these $b$ copies. Thus $|V(G_{k,b})|=2kb+1$.
Let $\mathcal B_{k,b}$ be the independent subsets of this graph,
including the empty subset. A common array of $m$ rows consists of
$m$ members of $\mathcal B_{k,b}$ on a single row set $[m]$.
Its occupancy observation is $(m,c)$, with $c_v$ the number of rows
containing $v$ and $t=c_o$ the root occupancy.

For a vector $p=(m,c)$, let $p_a=(m,c^{(a)})$ be its restriction to
cycle $a$, retaining the root and degree. Put

$$
\begin{aligned}
\mathcal S_{k,b}=\{(m,c)\in\mathbb Z_{\ge0}^{2kb+2}:&\quad
 c_u+c_v\le m\text{ for every edge }\{u,v\},\\
 &\quad t+\sum_{i=1}^{2k}c_{a,i}\le km\text{ for every }a\},\\
\delta_a(m,c)&=km-t-\sum_{i=1}^{2k}c_{a,i},\\
R_{k,b}&=\mathbb C[\mathcal S_{k,b}].
\end{aligned}
\tag{35.1}
$$

The root occurs once in each cycle inequality; it is one coordinate
of the global vector. Write $X^p$ for a semigroup monomial and
$X^pX^s=X^{p+s}$. The ordinary degree is $m$, and the boundary
bigrading is $(m,t)$. The single-cycle ring $R_k$ of Definition 31.1
is used also for $k=2$, with the same inequalities. This is an
occupancy algebra, without a specified order of the rows.

**Theorem 35.2 (Common-root realization and its canonical interior).**
Every point of $\mathcal S_{k,b}$ is the observation of $m$ actual
global independent sets. Restriction gives an addition-preserving
bijection

$$
\mathcal S_{k,b}\longleftrightarrow
\{(p_1,\ldots,p_b)\in\mathcal S_k^b:
             \deg_{(m,t)}p_1=\cdots=\deg_{(m,t)}p_b\}.
\tag{35.2}
$$

Consequently there is an isomorphism of boundary-bigraded algebras

$$
R_{k,b}\simeq
\bigoplus_{m\ge0}\ \bigoplus_{0\le t\le m}
 (R_k)_{(m,t)}\otimes_{\mathbb C}\cdots\otimes_{\mathbb C}
 (R_k)_{(m,t)},
\tag{35.3}
$$

with $b$ tensor factors. The ring is a normal standard graded
Cohen–Macaulay domain of dimension $2kb+2$. In its full exponent
lattice its canonical module is the ideal with monomial basis

$$
\omega_{R_{k,b}}=
\operatorname{span}_{\mathbb C}\{X^p:p\in\mathcal S_{k,b}^{\circ}\},
\qquad
\mathcal S_{k,b}^{\circ}=
\{(m,c):c_v\ge1,\ c_u+c_v\le m-1,\ \delta_a(m,c)\ge1\}.
\tag{35.4}
$$

In particular $p$ is interior if and only if all its cycle
restrictions are interior with the same $(m,t)$.

Proof. The single-cycle integer decomposition of Theorem 28.2 applies
to each $p_a$, including the five-cycle. Choose $m$ local independent
sets realizing it. Exactly $t$ of its rows contain the root. Permute
the rows separately in each cycle so that these are precisely rows
$1,\ldots,t$. In each row take the union of the local independent
sets, identifying their root vertices. All root choices now agree.
An edge is entirely in a single cycle, where that row is independent;
there is no cross edge. The rowwise union is therefore a global
independent set, and its occupancies are exactly $c$. For $m=0$ this
is the empty array. Conversely any global array restricts to such
local arrays and satisfies every inequality in (35.1).

The supplied local decomposition is more than local real feasibility:
it uses exactly $m$ rows and exactly $t$ root-one rows. This is why the
permutations establish a simultaneous realization. The bijection
(35.2) itself is between exponent vectors, not between chosen arrays:
the nonroot coordinates and the common root reconstruct $c$ uniquely.
Restriction and reconstruction both commute with addition.

Map a pure tensor of monomials in (35.3) to the reconstructed global
monomial. The monomial tensor bases and (35.2) make this a linear
bijection. Multiplication is explicitly

$$
(X^{p_1}\otimes\cdots\otimes X^{p_b})
(X^{s_1}\otimes\cdots\otimes X^{s_b})
=X^{p_1+s_1}\otimes\cdots\otimes X^{p_b+s_b}.
\tag{35.5}
$$

Its boundary degree is $(m+q,t+u)$ when the two factors have boundary
degrees $(m,t)$ and $(q,u)$. Equation (35.2) identifies (35.5) with
$X^{p+s}$, proving the algebra assertion. This is the specified
bigraded Segre-style diagonal, not an ordinary product of local
ungraded spaces or an independent product of their degree counts.

For the real geometry, let $P$ be the polyhedron in degree one defined
by the nonnegativity, edge and cycle inequalities in (35.1). It is
bounded since each vertex has a neighbor and hence $0\le c_v\le1$.
It contains the convex hull of the global independent-set indicators.
For any rational point of $P$, multiply by a positive common denominator
$m$ and apply the row construction; division by $m$ expresses the
point as an average of global indicators. Rational points are dense
in this rational polytope, and that convex hull is closed. Thus $P$
is exactly the stable-set polytope of $G_{k,b}$. Its homogenized real
cone $K_{k,b}$ is exactly the cone given by (35.1) over the reals:
at degree zero the edge bounds force every coordinate to be zero.

The degree-one empty set gives $(1,0)$, and subtracting it from the
degree-one singleton at $v$ gives $(0,e_v)$. These generate the full
group lattice $\mathbb Z^{2kb+2}$. At degree one a sufficiently small
constant positive occupancy has every edge sum less than one and
every cycle sum less than $k$. Together with $m>0$ these strict
inequalities exhibit a full-dimensional neighborhood in the cone.
Thus $\dim K_{k,b}=2kb+2$. The cone is rational and pointed, and

$$
\mathcal S_{k,b}=K_{k,b}\cap\mathbb Z^{2kb+2}.
\tag{35.6}
$$

The row decomposition also proves finite generation by the degree-one
indicators. Equation (35.6) proves saturation in the full group lattice,
hence normality. The ring is a domain by its monomial embedding into
$\mathbb C[z_0,(z_v)_{v\in V}]$ and is standard graded by that same
degree-one generation.

Every linear inequality used here is a nonzero supporting form of this
full-dimensional cone. If one is an equality, its supporting hyperplane
prevents an ambient open ball. If they are all strict, finitely many
positive margins give such a ball. Therefore their simultaneous
strictness describes the interior, even without assuming a minimal
facet list. For integral points this is precisely (35.4); the coordinate
and edge strictness already force $m\ge3$. Adding a semigroup point
preserves all strict inequalities, so their monomials form an ideal.

Hochster's theorem gives Cohen–Macaulayness for this normal affine
monoid ring. The Danilov–Stanley formula in Barile–Bruns,
*$\mathbb Z^r$-graded rings and their canonical modules*,
[§5 and Theorem 5.1][BB35], identifies its canonical module with the
interior ideal. In that theorem take the coefficient field to be
$\mathbb C$, the monoid to be $\mathcal S_{k,b}$ and
$r=2kb+2$; finite generation, normality, full group and full cone
dimension have just been established. These are the same classical
inputs used in §§29.2 and 31.2, now for the global cone.

There is also an exact literature correspondence for the gluing step.
Matsuda–Ohsugi–Shibata, *Toric rings and ideals of stable set polytopes*,
[Proposition 1.3][MOS35], states that for a clique sum the stable-set
toric ideal is a toric fiber product, and that its ring is normal if
and only if both constituent rings are normal. Here the intersection
is the singleton clique $\{o\}$, and the edge set is exactly the union
of the two edge sets at each successive gluing. The two singleton-clique
states, root absent and root present, have multiplicities $m-t$ and $t$;
these determine and are determined by $(m,t)$. Thus its fiber grading
matches (35.2). The proposition is a precedent for this specific
clique sum, whereas (35.2)–(35.5) give the actual maps used here.
The ordinary Segre product for disconnected graphs in their Example 1.2
has a different boundary condition. Neither result by itself proves
the synchronized interior subtraction below. $\square$

### 35.2 Uniform descent and every minimal canonical generator

**Definition 35.3 (Interior basic exponents).**
An exponent $p\in\mathcal S_{k,b}^{\circ}$ is basic if no nonzero
$s\in\mathcal S_{k,b}$ has $p-s\in\mathcal S_{k,b}^{\circ}$.
Use the same definition for a single cycle. In its local coordinates put

$$
\nu_j=(2j+1;j\mathbf1),\qquad 1\le j\le k-1.
\tag{35.7}
$$

These are local vectors; a global vector whose restrictions all equal
$\nu_j$ will be written $(2j+1;j\mathbf1_V)$.

**Theorem 35.4 (Synchronized descent at a single common root).**
A global interior exponent is basic if and only if at least one of its
cycle restrictions is exactly one of (35.7). Equivalently, all global
basic exponents are the compatible tuples of local interior exponents
of common degree $2j+1$ and root occupancy $j$, with at least one entry
$\nu_j$, for exactly one $j\in\{1,\ldots,k-1\}$.
Their monomials are exactly the minimal monomial generators of
$\omega_{R_{k,b}}$.

Proof. The needed local classification is the supplied result of
Theorem 31.3 and §31.2. Its primary source for $k\ge3$ is Miyazaki,
*Non-Gorenstein locus and almost Gorenstein property of the Ehrhart ring
of the stable set polytope of a cycle graph*, [§4][MI35]. His length is
$2\ell+1\ge7$; substitute $\ell=k$, his vertex function $\eta(v_i)=c_i$
and $\eta(-\infty)=m$. His $\eta_j$ is (35.7). Lemma 4.1 identifies
the translate by $\nu_1$; Lemmas 4.2–4.3 identify the maximum-set face
algebra; Lemma 4.4 supplies its free canonical layers. The argument
immediately before Theorem 4.5 establishes that $\eta_1,\ldots,
\eta_{\ell-1}$ are the minimal canonical generators. His map has target
$\omega_{R_k}(3)$, so its cokernel is $\mathcal C_k(3)$ in the notation
of Definition 31.2. Theorem 4.5 itself concerns the Ulrich and
almost-Gorenstein conclusions; those conclusions are not substituted
for the preceding generator classification.

Here are the exact local consequences, including their proof in the
coordinates needed for descent. For a local interior $p=(m,c)$ write
$\delta=km-\sum_i c_i$. If $\delta\ge k-1$, then $p-\nu_1$ has
nonnegative coordinates, edge sums at most $m-3$, nonnegative deficit
and degree $m-3\ge0$. Thus it is a local semigroup point. Otherwise
$1\le\delta\le k-2$ and put $j=k-\delta$. For each $i$, deleting
vertex $i$ leaves $k$ disjoint edges covering the other $2k$ vertices;
the strict edge bounds give

$$
km-\delta=\sum_r c_r\le c_i+k(m-1),\qquad c_i\ge k-\delta=j.
\tag{35.8}
$$

An edge then implies $m\ge2j+1$. Subtracting $\nu_j$ leaves
nonnegative coordinates and degree, edge bounds in degree $m-2j-1$
and deficit zero. Hence every local interior is $\nu_j+s$ with
$s\in\mathcal S_k$. Conversely these sums are interior, since
$\nu_j$ has coordinate $j$, edge slack one and deficit $k-j\ge1$.
When $k=2$, only the first case occurs: every interior is
$\nu_1+\mathcal S_2$. This directly proves the five-cycle assertion,
without extending Miyazaki's length-at-least-seven hypothesis.

For local minimality, suppose $\nu_j-s$ is interior, where
$s=(q,d)\in\mathcal S_k$. Each edge slack of $\nu_j$ is one,
so the nonnegative edge slacks of $s$ must all be zero. Then
$d_i+d_{i+1}=q$ for every edge. Oddness forces $d_i=q/2$ for all
$i$, and the cycle inequality gives $(2k+1)q/2\le kq$. Thus
$q=0$ and $d=0$. This proves that precisely the $\nu_j$ are local
basic exponents. All other interior exponents have a representation
$\nu_j+s$ with $s\ne0$, so $q=\deg s>0$.

It is not enough to subtract any local independent set separately.
For such a nonbasic local exponent, retain its common boundary $(m,t)$
and write

$$
p=\nu_j+s,\qquad q=m-2j-1>0,\qquad u=t-j.
\tag{35.9}
$$

The single-cycle integer decomposition realizes $s$ by $q$ rows,
exactly $u$ containing the root. Choose a row according to the rule

$$
\varepsilon(m,t)=
\begin{cases}
0,&2t<m,\\
1,&2t\ge m.
\end{cases}
\tag{35.10}
$$

This choice is always available. If $2t<m$, then $2u<q+1$.
Since $u,q$ are integers and $q>0$, this implies $u<q$, so there
is a root-zero row. If $2t\ge m$, then $2u\ge q+1>0$, so
$u>0$ and there is a root-one row. At equality $2t=m$, the
formula gives $2u=q+1$; in particular $q$ is odd and $u\ge1$,
so the root-one choice remains valid. Removing the chosen row
$I$ leaves a semigroup point $s-(1,\mathbf1_I)$. Consequently
$p-(1,\mathbf1_I)=\nu_j+(s-(1,\mathbf1_I))$ is still interior.
The rule depends only on $(m,t)$, even when different cycles use
different $j$ in (35.9).

Now suppose all local restrictions of a global interior $p$ are
nonbasic. Apply (35.10) to every cycle and take the union of the
chosen rows. They have the same root bit and no cross edges, so the
union is a legal global independent set $I$. The global remainder
$p-(1,\mathbf1_I)$ restricts to interior vectors on every cycle
and is therefore interior by (35.4). Thus $p$ is not basic.

Conversely suppose $p_a=\nu_j$ for some $a$. Any nonzero global
$s\in\mathcal S_{k,b}$ has positive degree: degree zero forces
all coordinates to vanish. Its restriction $s_a$ has that same
positive degree and is nonzero. If $p-s$ were interior, then
$\nu_j-s_a$ would be local interior, contradicting local minimality.
Thus $p$ is basic. The boundary of $\nu_j$ forces $m=2j+1,t=j$,
and two different $j$ cannot occur at that same boundary.

Repeated descent lowers the integer degree and stops at a basic
interior exponent. It therefore generates the whole interior ideal
from precisely the asserted monomials. A basic monomial cannot be a
positive-degree multiple of any other interior monomial. Distinct
exponents are linearly independent, so the basic classes form a basis
of $\omega_{R_{k,b}}/R_{k,b,+}\omega_{R_{k,b}}$. This proves both
minimality and completeness for arbitrary polynomial generators as
well. $\square$

### 35.3 Root-conditioned transfer counts and the growth of type

**Theorem 35.5 (All canonical generator counts).**
For $1\le j\le k-1$ define

$$
\begin{aligned}
T_q(a,c)&=\mathbf1_{a+c\le q},\quad 0\le a,c\le q,\\
M_{k,j}&=(T_{2j-2}^{\,2k+1})_{j-1,j-1},\\
\mu_{k,b,j}&=M_{k,j}^{\,b}-(M_{k,j}-1)^b.
\end{aligned}
\tag{35.11}
$$

There are exactly $\mu_{k,b,j}$ minimal canonical generators in
degree $2j+1$ and no minimal generators in any other degree. Thus

$$
\operatorname{type}R_{k,b}
=\sum_{j=1}^{k-1}\bigl(M_{k,j}^{\,b}-(M_{k,j}-1)^b\bigr).
\tag{35.12}
$$

Proof. A local interior exponent of degree $2j+1$ has edge sums at
most $2j$. Summing the $2k+1$ edge bounds yields
$\sum_i c_i\le(2k+1)j$. For $j\le k-1$,

$$
(2k+1)j\le k(2j+1)-1.
\tag{35.13}
$$

Hence the strict cycle inequality is automatic in these degrees.
Set $d_i=c_i-1$. Its conditions are $d_i\ge0$,
$d_i+d_{i+1}\le2j-2$ and root $d_0=j-1$. Each coordinate lies
between zero and $2j-2$ because it has a nonnegative neighbor.
The closed transfer walk starting and ending at $j-1$ counts exactly
these labelled vectors, with each factor imposing one cyclic edge.
This proves that $M_{k,j}$ is their number. For $j=1$ the matrix
$T_0=[1]$ has one state, so $M_{k,1}=1$; no empty-matrix convention
is involved.

At this fixed boundary the $b$ cycle vectors can be chosen independently
and then glued by (35.2); there are $M_{k,j}^b$ tuples. Exactly one
of the $M_{k,j}$ possibilities in each cycle is $\nu_j$. The tuples
with no such entry number $(M_{k,j}-1)^b$, and Theorem 35.4 excludes
precisely those tuples from the basic set. Different $j$ give different
degrees and hence disjoint sets. Their number is the minimal number
of generators of the canonical module, which for this Cohen–Macaulay
ring is its type. This proves (35.11)–(35.12). It counts all compatible
local interiors with a basic entry, rather than multiplying the local
types. $\square$

**Proposition 35.6 (One seven-cycle has type two; two have type 202).**
For the shared-root seven-cycle family,

$$
\operatorname{type}R_{3,b}=1+101^b-100^b.
\tag{35.14}
$$

In particular the types for $b=1,2,3$ are $2,202,30302$.
For every $b\ge1$ the five-cycle family has type one.

Proof. For $k=3$ the two local canonical degrees are three and five.
At degree three $M_{3,1}=1$. At degree five use

$$
T_2=\begin{pmatrix}1&1&1\\1&1&0\\1&0&0\end{pmatrix}.
\tag{35.15}
$$

Starting at the middle state, its row vectors for powers zero through
seven are

$$
\begin{aligned}
&(0,1,0),\ (1,1,0),\ (2,2,1),\ (5,4,2),\\
&(11,9,5),\ (25,20,11),\ (56,45,25),\ (126,101,56).
\end{aligned}
\tag{35.16}
$$

Each step replaces $(a,b,c)$ by $(a+b+c,a+b,a)$, proving the
entries directly. Thus $M_{3,2}=101$. There are $100$ other local
interiors at boundary $(5,2)$, besides $\nu_2$. For two labelled
cycles the basic degree-five tuples divide into $(\nu_2,\nu_2)$,
$(\nu_2,p)$ and $(p,\nu_2)$ with $p\ne\nu_2$. Their counts are
$1,100,100$, giving $201$. Including the single degree-three
basic exponent gives $202$, whereas the product of the two local
types would be $2\cdot2=4$. For three cycles the calculation is
$1+101^3-100^3=30302$.

For an explicit mixed tuple, take on one seven-cycle
$p=\nu_1+(2;\mathbf1_{\{0\}})=(5;2,1,1,1,1,1,1)$.
The remainder is realized by one root singleton and one empty row,
so $p$ is locally reducible. Pair it with $\nu_2$ on the other
cycle; both have boundary $(5,2)$. This tuple is globally basic:
any global subtraction lowers the common degree on the second cycle
as well and contradicts minimality of $\nu_2$. A local reduction
cannot leave the other cycle's degree unchanged. This explains the
extra generators without treating the rings as independent factors.

For $k=2$ the only index is $j=1$, so (35.12) gives
$1^b-0^b=1$ for $b\ge1$. The direct five-cycle proof in Theorem
35.4 supplies the endpoint classification. $\square$

[MI35]: https://arxiv.org/pdf/2205.01409v1
[MOS35]: https://arxiv.org/pdf/1603.01850v1
[BB35]: https://arxiv.org/pdf/2505.11402v1

## 36. Root-resolved canonical layers and the complete quotient counts

### 36.1 Keeping the root in the local layers

**Definition 36.1 (Legal, interior and exceptional root sectors).**
For one cycle define

$$
\begin{aligned}
L_k(m,t)&=\#\{(m,c)\in\mathcal S_k:c_0=t\},\\
I_k(m,t)&=\#\{(m,c)\in\mathcal S_k^\circ:c_0=t\},\\
B_k(m,t)&=L_k(m-3,t-1),\\
E_k(m,t)&=I_k(m,t)-B_k(m,t).
\end{aligned}
\tag{36.1}
$$

A count is zero for negative degree, negative root occupancy or root
occupancy exceeding the degree of the object counted; the interior
count is also zero whenever its strict inequalities are infeasible.
In particular $I_k(0,t)=0$ and $L_k(0,t)=\mathbf1_{t=0}$.
The two-argument $E_k(m,t)$ here is an exceptional canonical count.
It is different from the one-argument local-trace error $E_k(q)$ of
Definition 32.1; the latter counts locally feasible tuples without a
common-copy lift. No equality between those two counts is implicit.

**Theorem 36.2 (Root resolution of the supplied face layers).**
For $k\ge3$ one has

$$
E_k(m,t)=
\sum_{\substack{2\le j\le k-1\\t\ge j,\ m-t\ge j+1}}
\binom{t-j+k-1}{k-1}
\binom{m-t-j+k-1}{k}.
\tag{36.2}
$$

For $k=2$ the sum is empty and $E_2(m,t)=0$. Let

$$
\nu=(3;\mathbf1_V),\qquad
C_{k,b}=\omega_{R_{k,b}}/X^\nu R_{k,b}.
\tag{36.3}
$$

Then the complete degree counts are

$$
\begin{aligned}
\dim_{\mathbb C}(\omega_{R_{k,b}})_m
 &=\sum_{t=0}^{m}I_k(m,t)^b,\\
\dim_{\mathbb C}(X^\nu R_{k,b})_m
 &=\dim_{\mathbb C}(R_{k,b})_{m-3}
   =\sum_{t=0}^{m}B_k(m,t)^b,\\
\dim_{\mathbb C}(C_{k,b})_m
 &=\sum_{t=0}^{m}\bigl((B_k(m,t)+E_k(m,t))^b-B_k(m,t)^b\bigr).
\end{aligned}
\tag{36.4}
$$

The right sides are zero for $m<0$. For $b=2$ the last summand is
$2B_k(m,t)E_k(m,t)+E_k(m,t)^2$ at each common root occupancy.

Proof. In the local canonical classification used in Theorem 35.4,
translation by $\nu_1$ is exactly the range $\delta\ge k-1$.
It changes the boundary by $(3,1)$, giving the ordinary count $B_k$.
The remaining exponents are exactly the disjoint free face layers

$$
p=\nu_j+s_0,\qquad 2\le j\le k-1,\qquad\delta(s_0)=0.
\tag{36.5}
$$

These are Miyazaki's Lemma 4.4 layers, with the parameter and shift
correspondence in Theorem 35.4; their additive face coordinates are
(31.13)–(31.14). To retain the root, write $s_0=(q,d)$ and put

$$
\alpha_i=q-d_i-d_{i+1}\ge0,\qquad
q=\sum_{i=0}^{2k}\alpha_i,\qquad
d_i=\sum_{r=0}^{k-1}\alpha_{i+1+2r}.
\tag{36.6}
$$

All indices are modulo $2k+1$. The two alternating sums for adjacent
$i$ cover every $\alpha$ except $\alpha_i$, so the edge equations
hold. Summing the occupancies gives $\sum_i d_i=kq$. Conversely
these odd-cycle edge equations have unique solution, since a difference
alternates sign around an odd cycle and must vanish. Thus (36.6)
is precisely the bijection between the face semigroup and
$\mathbb N^{2k+1}$ already supplied in §31.3.

At the root, $d_0=\alpha_1+\alpha_3+\cdots+\alpha_{2k-1}$ is the
sum of exactly $k$ coordinates. The complementary $k+1$ coordinates
sum to $q-d_0$. In (36.5), therefore,

$$
q=m-2j-1,\qquad d_0=t-j,\qquad q-d_0=m-t-j-1.
\tag{36.7}
$$

These are nonnegative precisely under the restrictions in (36.2).
Stars and bars for the two specified, disjoint coordinate sets gives
respectively $\binom{t-j+k-1}{k-1}$ and
$\binom{m-t-j+k-1}{k}$. The deficit of (36.5) is $k-j$,
so different layers cannot overlap. This proves (36.2) and its zero
conventions. For $k=2$ direct translation already exhausts the local
interior, so there are no layers to count.

A global interior vector is a tuple of local interiors at the same
$(m,t)$ by Theorem 35.2, giving the first line of (36.4). The vector
$\nu$ is interior: its coordinates are one, edge slack one and each
cycle deficit $k-1\ge1$. Since $R_{k,b}$ is a domain, multiplication
by $X^\nu$ is injective, with boundary shift $(3,1)$. To be in its
image every local interior must lie in its ordinary translated sector;
subtracting the same $\nu_1$ in each cycle leaves compatible boundary
$(m-3,t-1)$ and hence a global semigroup point. This proves the
second line. The quotient of two monomial spaces has as basis exactly
the interior exponents outside this image, so subtraction proves the
last line, with no unproved module splitting.

For two cycles the cross terms count one ordinary and one exceptional
local sector at this same $(m,t)$, in either labelled order. The term
$E_k^2$ counts two exceptional sectors. Summing local exceptional
counts first, or tensoring unrelated root degrees, would lose this
compatibility. The counts are amplified only by actual compatible
global exponents. $\square$

### 36.2 Three full tables for two seven-cycles

**Proposition 36.3 (All root sectors in degrees five, six and seven).**
For $k=3,b=2$ the root-resolved entries of (36.4) are the following.
Here $B=B_3(m,t)$, $E=E_3(m,t)$, $I=I_3(m,t)$; the last three
columns count global interior monomials, ordinary translates and
surviving quotient monomials in that root sector.

| $m=5$, $t$ | $B$ | $E$ | $I=B+E$ | $I^2$ | $B^2$ | $I^2-B^2$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 1 | 157 | 0 | 157 | 24649 | 24649 | 0 |
| 2 | 100 | 1 | 101 | 10201 | 10000 | 201 |
| 3 | 31 | 0 | 31 | 961 | 961 | 0 |
| 4 | 0 | 0 | 0 | 0 | 0 | 0 |
| 5 | 0 | 0 | 0 | 0 | 0 | 0 |
| Total | 288 | 1 | 289 | 35811 | 35610 | 201 |

| $m=6$, $t$ | $B$ | $E$ | $I=B+E$ | $I^2$ | $B^2$ | $I^2-B^2$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 1 | 707 | 0 | 707 | 499849 | 499849 | 0 |
| 2 | 543 | 4 | 547 | 299209 | 294849 | 4360 |
| 3 | 298 | 3 | 301 | 90601 | 88804 | 1797 |
| 4 | 85 | 0 | 85 | 7225 | 7225 | 0 |
| 5 | 0 | 0 | 0 | 0 | 0 | 0 |
| 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| Total | 1633 | 7 | 1640 | 896884 | 890727 | 6157 |

| $m=7$, $t$ | $B$ | $E$ | $I=B+E$ | $I^2$ | $B^2$ | $I^2-B^2$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 1 | 2353 | 0 | 2353 | 5536609 | 5536609 | 0 |
| 2 | 1978 | 10 | 1988 | 3952144 | 3912484 | 39660 |
| 3 | 1359 | 12 | 1371 | 1879641 | 1846881 | 32760 |
| 4 | 695 | 6 | 701 | 491401 | 483025 | 8376 |
| 5 | 190 | 0 | 190 | 36100 | 36100 | 0 |
| 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| 7 | 0 | 0 | 0 | 0 | 0 | 0 |
| Total | 6575 | 28 | 6603 | 11895895 | 11815099 | 80796 |

Proof. There is only the local layer $j=2$ for seven positions.
Formula (36.2) becomes

$$
E_3(m,t)=\binom{t}{2}\binom{m-t}{3}
\quad\text{if }t\ge2,\ m-t\ge3,
\tag{36.8}
$$

and is zero otherwise. This gives the $E$ columns directly: in degree
five only $t=2$ contributes one; in degree six the values at $t=2,3$
are four and three; in degree seven those at $t=2,3,4$ are ten,
twelve and six.

For a complete finite recurrence determining the $B$ columns, fix a
local degree $q$ and root $u\in\{0,\ldots,q\}$. Let
$H_r(v,h)$ count choices of the first $r$ path coordinates
$c_1,\ldots,c_r$, with $c_r=v$ and $h=u+\sum_{i=1}^r c_i$,
respecting all edges encountered from the root. Start with
$H_0(u,u)=1$, all other values zero, and for $0\le r<2k$ use

$$
H_{r+1}(w,h+w)=\sum_{\substack{v\ge0\\v+w\le q}}H_r(v,h).
\tag{36.9}
$$

Only $0\le w\le q$ is needed. Closure and the total constraint give

$$
L_k(q,u)=\sum_{\substack{v+u\le q\\h\le kq}}H_{2k}(v,h).
\tag{36.10}
$$

Each admissible vector has one unique sequence of intermediate states,
so (36.9)–(36.10) count it once. For $k=3$, their evaluations at
$q=2,3,4$, with root columns in increasing order, are

$$
\begin{aligned}
(L_3(2,u))_{u=0}^2&=(157,100,31),\\
(L_3(3,u))_{u=0}^3&=(707,543,298,85),\\
(L_3(4,u))_{u=0}^4&=(2353,1978,1359,695,190).
\end{aligned}
\tag{36.11}
$$

Inserting $q=m-3,u=t-1$ gives every $B$ entry. Adding (36.8)
gives $I$, squaring at each common root gives the next two columns,
and subtraction gives the last. Their sums are the stated totals.
For instance the degree-six difference is
$2\cdot543\cdot4+4^2+2\cdot298\cdot3+3^2=6157$;
the degree-seven difference is $39660+32760+8376=80796$.
The sums of the first three numerical columns are local counts;
they are not to be squared to obtain the last three totals.

At degree five every surviving quotient monomial is one of the $201$
additional minimal canonical generators in Proposition 35.6, since
there is no quotient in smaller degree. The numbers $6157$ and $80796$
are entire degree pieces of the quotient, including positive-degree
multiples. They count no new minimal canonical generators in degrees
six or seven: Theorem 35.5 places all such generators for $k=3$ in
degrees three and five, with the unique degree-three generator removed
in $C_{3,2}$. $\square$

## 37. Cyclewise deficit action, polynomial annihilators and sharp ideal depth

### 37.1 The full action and its simultaneous threshold

**Theorem 37.1 (The shared-root canonical quotient action).**
For $k\ge3$, a monomial $X^p$ with $p$ interior has nonzero class in
$C_{k,b}$ precisely when

$$
1\le\delta_a(p)\le k-2\quad\text{for at least one }a.
\tag{37.1}
$$

The action of any semigroup monomial on this basis is

$$
X^s[X^p]=
\begin{cases}
[X^{p+s}],&\delta_a(p)+\delta_a(s)\le k-2
                         \text{ for at least one }a,\\
0,&\delta_a(p)+\delta_a(s)\ge k-1\text{ for every }a.
\end{cases}
\tag{37.2}
$$

For arbitrary polynomials, extended linearly, its full annihilator is

$$
\operatorname{Ann}_{R_{k,b}}C_{k,b}
=\operatorname{span}_{\mathbb C}
 \{X^s:s\in\mathcal S_{k,b},\ \delta_a(s)\ge k-2\text{ for every }a\}.
\tag{37.3}
$$

For $k=2$ one instead has $\omega_{R_{2,b}}=X^\nu R_{2,b}$,
$C_{2,b}=0$ and $\operatorname{Ann}_{R_{2,b}}C_{2,b}=R_{2,b}$.

Proof. Subtract $\nu=(3;\mathbf1_V)$ from an interior $p=(m,c)$.
The degree is nonnegative since $m\ge3$, the coordinates are
nonnegative, and an edge sum becomes at most $m-3$, as required
at the new degree. The only remaining conditions are the cycle
inequalities, whose deficits become

$$
\delta_a(p-\nu)=\delta_a(p)-(k-1),
\tag{37.4}
$$

because $\delta_a(\nu)=3k-(2k+1)=k-1$ on each cycle.
Thus $p-\nu$ is a global semigroup point if and only if every
$\delta_a(p)\ge k-1$. The image $X^\nu R_{k,b}$ is a monomial
ideal, so the complementary exponents are a quotient basis. Since
interior deficits are positive integers, this is exactly (37.1).
For $k=2$ every interior already satisfies all thresholds in (37.4),
proving its separate zero-quotient assertion.

Each $\delta_a$ is additive on the actual common-root exponent:
the degree and the root occupancy are each added once in that cycle's
formula. Adding $s\in\mathcal S_{k,b}$ preserves the strict
coordinate and edge inequalities. Applying (37.1) to $p+s$ gives
(37.2). It is an algebra action, since exponent addition is associative
and the removed monomials form an ideal. Equivalently, once every
deficit has reached $k-1$, adding nonnegative deficits can never make
a class survive again. This is the global counterpart of the local
slack/deficit action in (31.7), retaining a vector of cycle deficits.

If all deficits of $s$ are at least $k-2$, then adding $s$ to any
interior $p$ gives every deficit at least $k-1$, so $X^s$ annihilates
the module. For the converse there is a single common witness

$$
p_*=(2k-1;(k-1)\mathbf1_V),\qquad
\delta_a(p_*)=1\quad\text{for every }a.
\tag{37.5}
$$

Its coordinates are positive and each edge has sum $2k-2$, one
below its degree. The displayed deficits prove interior membership.
For $k\ge3$ it survives (37.1). If some $\delta_a(s)<k-2$,
then $\delta_a(p_*+s)\le k-2$, so $X^s[X^{p_*}]\ne0$.
This proves the monomial criterion.

To obtain the entire polynomial annihilator, combine equal exponents
in $f=\sum_s\lambda_sX^s$, with distinct $s$ and nonzero coefficients.
Multiplication by $[X^{p_*}]$ kills exactly the terms satisfying all
thresholds in (37.3). Every other term survives by the same witness.
Translation in the torsion-free exponent lattice is injective:
$p_*+s=p_*+s'$ implies $s=s'$. Hence these surviving exponents are
distinct members of the quotient monomial basis and cannot cancel.
Therefore $f[X^{p_*}]=0$ forces every term of $f$ into the displayed
threshold set. Conversely such a polynomial annihilates every class
by the first direction. This proves (37.3) for polynomials, including
all linear combinations, and makes clear that the threshold must hold
on every cycle, not just one. $\square$

### 37.2 Face primes and the exact depth of the ideal action

**Definition 37.2 (The cycle face primes and their intersection).**
For $k\ge3$ and each labelled cycle set

$$
\mathfrak p_a=\operatorname{span}_{\mathbb C}
 \{X^s:\delta_a(s)>0\},\qquad
J=\bigcap_{a=1}^b\mathfrak p_a.
\tag{37.6}
$$

The powers $J^r$ below are ordinary ideal powers; $J^0=R_{k,b}$.

**Theorem 37.3 (Radical support and sharp simultaneous nilpotence).**
Each $\mathfrak p_a$ is the prime ideal of the face $\delta_a=0$.
Moreover

$$
\begin{aligned}
J&=\operatorname{span}_{\mathbb C}
      \{X^s:\delta_a(s)\ge1\text{ for every }a\},\\
\sqrt{\operatorname{Ann}_{R_{k,b}}C_{k,b}}&=J,\\
J^{k-2}C_{k,b}&=0,\qquad J^{k-3}C_{k,b}\ne0.
\end{aligned}
\tag{37.7}
$$

When $k=3$, $\operatorname{Ann}C_{3,b}=J$ and the nonvanishing
statement is $J^0C_{3,b}=C_{3,b}\ne0$. When $k\ge4$,

$$
J^{k-2}\subsetneq\operatorname{Ann}C_{k,b}\subsetneq J.
\tag{37.8}
$$

Proof. Since $\delta_a$ is nonnegative and additive on the semigroup,
its zero locus is a face submonoid: if $\delta_a(s+s')=0$, both
summands have deficit zero. The linear map fixing its monomials and
killing the positive-deficit monomials is therefore a surjective
algebra homomorphism onto its semigroup algebra. Its kernel is
$\mathfrak p_a$. That algebra is a domain, as a monomial subalgebra
of the same ambient polynomial ring; thus $\mathfrak p_a$ is prime.
The face is proper: the empty degree-one mode has deficit $k>0$,
whereas simultaneous root-zero maximum sets on all cycles give
nonzero points on it. The forms $\delta_a$ are supporting forms of
$K_{k,b}$, so this is exactly the asserted face prime.

The ideals have a common monomial basis. A polynomial is in all of
them if and only if each of its terms has positive deficit on every
cycle; this proves the first line of (37.7). It also proves directly
that no cancellation changes membership in their intersection.
For distinct cycles the primes are distinct: take a degree-one global
set with root zero, size $k-1$ on cycle $a$, and size $k$ on every
other cycle. It has deficit one on $a$ and zero on the others.
Such sets exist on the $2k$-vertex paths, for example the odd positions
through $2k-3$ and through $2k-1$, respectively.

Every product of $r$ monomials from $J$ has deficit at least $r$
on each cycle. Extending by linearity and taking $r=k-2$ gives
$J^{k-2}\subseteq\operatorname{Ann}C_{k,b}$ by Theorem 37.1.
That theorem also gives $\operatorname{Ann}C_{k,b}\subseteq J$.
A finite intersection of primes is radical, so taking radicals in

$$
J^{k-2}\subseteq\operatorname{Ann}C_{k,b}\subseteq J
\tag{37.9}
$$

proves the radical assertion. It describes a union of the cycle-face
supports; it does not replace the full annihilator by a reduced ideal.

For sharpness choose the single global independent set $U$ whose
root is zero and whose occupied positions on every cycle are
$\{1,3,\ldots,2k-3\}$. Its local size is $k-1$, so its mode
$s_U=(1,\mathbf1_U)$ has $\delta_a(s_U)=1$ for all $a$ and
$X^{s_U}\in J$. Acting on the common witness (37.5) gives

$$
(X^{s_U})^{k-3}[X^{p_*}]
=[X^{p_*+(k-3)s_U}]\ne0,
\qquad\delta_a(p_*+(k-3)s_U)=k-2.
\tag{37.10}
$$

The strict inequalities persist under addition. For $k=3$ this is
exponent zero: the monomial power is $1$, $J^0=R_{3,b}$ and
$[X^{p_*}]$ is nonzero. Thus the endpoint is included rather than
silently requiring a positive power.

If $k\ge4$, the same $X^{s_U}$ lies in $J$ but fails the threshold
$k-2\ge2$, proving the right strict inclusion in (37.8). The empty
degree-one mode has every deficit $k$, so belongs to the annihilator.
It is not in $J^{k-2}$: every monomial in $J$ has degree at least one,
and hence that power has no nonzero element of degree less than
$k-2\ge2$. This proves the other strict inclusion. In particular
ordinary ideal powers are not identified with the monomial threshold
ideal. For $k=3$ the threshold is one, giving the stated equality.
The $k=2$ zero module has annihilator and radical equal to the whole
ring by Theorem 37.1 and is outside (37.6)–(37.10). $\square$

### 37.3 Two seven-cycles and a nonzero action of every positive power

**Proposition 37.4 (Two complementary deficit directions).**
In $R_{3,2}$, choose the root-zero global sets

$$
\begin{array}{c|cc}
 &\text{cycle 1}&\text{cycle 2}\\ \hline
I_x&\{1,3\}&\{1,3,5\}\\
I_y&\{1,3,5\}&\{1,3\}
\end{array}
\qquad
x=X^{(1,\mathbf1_{I_x})},\quad y=X^{(1,\mathbf1_{I_y})}.
\tag{37.11}
$$

Their deficit vectors are $(1,0)$ and $(0,1)$, respectively, and

$$
xC_{3,2}\ne0,\qquad yC_{3,2}\ne0,\qquad xyC_{3,2}=0,
\qquad x^qC_{3,2}\ne0\quad\text{for every integer }q\ge1.
\tag{37.12}
$$

Proof. On each seven-cycle the nonroot vertices form the path
$1,\ldots,6$. Both displayed subsets are independent on this path
and the root is absent, so they are legal also across the two edges
to the root. Their sizes are two and three; subtracting from $k=3$
gives the stated deficit vectors. Use the same nonzero class
$[X^{p_*}]$ with $p_*=(5;2\mathbf1_V)$. Its deficits are $(1,1)$.
After multiplication by $x$ they are $(2,1)$, and after multiplication
by $y$ they are $(1,2)$. A deficit one remains in each case, so
both images are nonzero by (37.2).

The mode $xy$ has deficit $(1,1)$, which meets every annihilator
threshold for $k=3$, so it kills the entire quotient, not merely
this chosen class. In contrast, $x^q$ has deficit $(q,0)$, and
$x^q[X^{p_*}]$ has deficits $(q+1,1)$. It survives for every
$q\ge1$ because the second cycle is untouched. This supplies one
class witnessing every claimed nonzero operator; it does not assert
that $x$ acts nontrivially on every nonzero class. For example
$y[X^{p_*}]\ne0$ but $x(y[X^{p_*}])=0$.

The equality $JC_{3,2}=0$ from Theorem 37.3 is consistent with all
of this: $x\notin J$ and $y\notin J$, whereas $xy\in J$.
A positive deficit in one direction does not force a positive deficit
in the other, and repeated application of $x$ does not eventually
annihilate the whole quotient. The simultaneous condition in
(37.3) is essential. $\square$

## 38. The complete terminal module of the shared-root relation presentation

### 38.1 Actual modes, projective dimension and canonical duality

**Definition 38.1 (The polynomial ring in global independent sets).**
Let $F_0=0$, $F_1=1$, $F_{r+2}=F_{r+1}+F_r$ be the Fibonacci
numbers. To distinguish free resolution modules from these integers,
write $\mathcal F_i$ for the free modules below. Put

$$
\begin{aligned}
\mathscr P_{k,b}&=\mathbb C[z_I:I\in\mathcal B_{k,b}],\\
z_I&\longmapsto X^{\gamma_I},\qquad
\gamma_I=(1,\mathbf1_I),\\
D_{k,b}&=|\mathcal B_{k,b}|,\qquad
\Sigma_{k,b}=\sum_{I\in\mathcal B_{k,b}}\gamma_I.
\end{aligned}
\tag{38.1}
$$

Every global independent set, including the empty set, has one variable.
The map is onto $R_{k,b}$ by Theorem 35.2. Its kernel is the toric
relation ideal for these actual modes. Use the shift convention
$\mathscr P(-d)_m=\mathscr P_{m-d}$, and the analogous convention
for full exponent degrees. Let $\mathcal G_{k,b,j}$ be the complete
set of basic exponents at boundary $(2j+1,j)$ in Theorem 35.4.

**Theorem 38.2 (All terminal summands, with their degree shifts).**
For this presentation,

$$
\begin{aligned}
D_{k,b}&=F_{2k+2}^{\,b}+F_{2k}^{\,b},\\
\dim R_{k,b}&=2kb+2,\\
c_{k,b}=\operatorname{pd}_{\mathscr P_{k,b}}R_{k,b}
 &=D_{k,b}-2kb-2.
\end{aligned}
\tag{38.2}
$$

The complete final module in a minimal ordinarily graded free
resolution is

$$
\mathcal F_{c_{k,b}}=
\bigoplus_{j=1}^{k-1}
\mathscr P_{k,b}\bigl(-(D_{k,b}-2j-1)\bigr)^{\mu_{k,b,j}}.
\tag{38.3}
$$

More precisely its full multigrading is

$$
\mathcal F_{c_{k,b}}=
\bigoplus_{j=1}^{k-1}\ \bigoplus_{p\in\mathcal G_{k,b,j}}
\mathscr P_{k,b}\bigl(-(\Sigma_{k,b}-p)\bigr).
\tag{38.4}
$$

Thus (35.11) supplies every terminal multiplicity as well as every
ordinary degree, and the compatible-tuple description supplies every
full exponent shift. No intervening resolution matrices are specified.

Proof. A path of length $r$ vertices has $F_{r+2}$ independent sets:
separating the first vertex according to absence or presence leaves
paths of lengths $r-1$ and $r-2$, with initial counts one for the
empty path and two for a one-vertex path. If a global independent
set omits the root, each of the $b$ cycles leaves a path of $2k$
vertices and the choices are independent, giving $F_{2k+2}^b$.
If it contains the root, its two neighbors on every cycle are absent,
leaving a path of $2k-2$ vertices in each cycle, giving $F_{2k}^b$.
These cases are disjoint and exhaustive. Their sum proves the first
line of (38.2), and the dimension is the full lattice rank from
Theorem 35.2.

The polynomial ring has $D_{k,b}$ variables and depth $D_{k,b}$
at its homogeneous maximal ideal $\mathfrak n=(z_I)_I$.
Its nonzero finite quotient $R_{k,b}$ is Cohen–Macaulay of depth
$2kb+2$. Hilbert syzygy gives finite projective dimension over the
polynomial ring. Apply Auslander–Buchsbaum after localizing at
$\mathfrak n$: [Stacks, §10.111, tag 090U, Proposition 10.111.1][AB38]
states for a nonzero finite module of finite projective dimension
over a Noetherian local ring that depth of the ring equals projective
dimension plus depth of the module. It gives the last line of (38.2).
A minimal graded resolution localizes to a minimal local resolution
at $\mathfrak n$, so its length is this same $c_{k,b}$.

Choose a minimal resolution in the full exponent grading. Such a
choice is possible by homogeneous generator selection: the grading
has a positive ordinary coarsening and finite-dimensional pieces,
and all variables have positive ordinary degree. Its differentials
have entries in $\mathfrak n$. The canonical module of the polynomial
ring in this grading is
$\omega_{\mathscr P_{k,b}}=\mathscr P_{k,b}(-\Sigma_{k,b})$,
since the top exterior product of the variable differentials has
degree equal to the sum of their degrees.

Barile–Bruns [Theorem 4.5(a)][BB35] applies to the regular graded-local
ring $\mathscr P_{k,b}$ and its Cohen–Macaulay residue ring $R_{k,b}$.
Their codimension is $c_{k,b}$, and their graded canonical module is
the one identified with the full-lattice interior ideal by Theorem 5.1.
The theorem and the Ext vanishing in its proof give

$$
\operatorname{Ext}^{c_{k,b}}_{\mathscr P_{k,b}}
 (R_{k,b},\mathscr P_{k,b}(-\Sigma_{k,b}))
 \simeq\omega_{R_{k,b}},\qquad
\operatorname{Ext}^{i}_{\mathscr P_{k,b}}
 (R_{k,b},\mathscr P_{k,b}(-\Sigma_{k,b}))=0\ (i\ne c_{k,b}).
\tag{38.5}
$$

This is the same duality supplier as (33.3), with the actual global
mode set and its full lattice replacing the single-cycle data.

Dualize the chosen resolution into $\mathscr P_{k,b}(-\Sigma_{k,b})$.
By (38.5) the reversed dual complex resolves $\omega_{R_{k,b}}$.
In particular the canonical module is the cokernel of the map into
$\operatorname{Hom}(\mathcal F_{c_{k,b}},
\mathscr P_{k,b}(-\Sigma_{k,b}))$. Tensoring this cokernel with
$\mathscr P_{k,b}/\mathfrak n=\mathbb C$ makes the incoming map
zero, because the original and the dual differentials both have
entries in $\mathfrak n$. Consequently each summand of that final
dual free module contributes exactly one minimal canonical generator,
with no hidden cancellation. A summand $\mathscr P_{k,b}(-\Theta)$
dualizes to a free module whose generator has degree
$\Sigma_{k,b}-\Theta$. By Theorems 35.4–35.5 the full set of such
generator degrees is precisely $\bigcup_j\mathcal G_{k,b,j}$,
each once. Solving $\Sigma_{k,b}-\Theta=p$ proves (38.4).
Coarsening to ordinary degree gives $D_{k,b}-(2j+1)$ with multiplicity
$\mu_{k,b,j}$ and proves (38.3). This establishes the entire last
module from the canonical generators, rather than inferring it from
an alternating Hilbert numerator alone. $\square$

**Proposition 38.3 (Explicit full-degree sum and the two-seven-cycle end).**
Set $A=F_{2k+2}$ and $B=F_{2k}$. The root coordinate of
$\Sigma_{k,b}$ is $B^b$. For $1\le i\le2k$ on any cycle its
nonroot coordinate is

$$
(\Sigma_{k,b})_{a,i}
=A^{b-1}F_iF_{2k-i+1}+B^{b-1}v_i,
\qquad
v_i=
\begin{cases}
0,&i=1\text{ or }i=2k,\\
F_{i-1}F_{2k-i},&2\le i\le2k-1.
\end{cases}
\tag{38.6}
$$

For two seven-cycles in particular,

$$
\begin{aligned}
D_{3,2}&=21^2+8^2=505,\qquad c_{3,2}=505-14=491,\\
\mathcal F_{491}
 &=\mathscr P_{3,2}(-502)\oplus\mathscr P_{3,2}(-500)^{201}.
\end{aligned}
\tag{38.7}
$$

The last rank is $202$, the Cohen–Macaulay type. A single seven-cycle
has type two, with one canonical generator in degree three and one
in degree five; the shared-root pair has one in degree three and
$201$ in degree five.

Proof. A mode contains the root in exactly the root-one case counted
above, proving $B^b$. In the root-zero case, requiring position $i$
on one path removes it and its two neighboring path positions. The
remaining left and right paths have independent-set counts $F_i$
and $F_{2k-i+1}$, including the endpoint cases where one contribution
is $F_1=1$. All other cycles contribute $A^{b-1}$. In the root-one
case positions $1,2k$ are forbidden. For any other $i$, the remaining
path from $2$ through $2k-1$, with $i$ required, has counts
$F_{i-1}$ and $F_{2k-i}$ on its two remaining sides. The other cycles
contribute $B^{b-1}$. This proves (38.6) and completely evaluates
the degree vector used in (38.4).

For $k=3,b=2$, the root coordinate is $64$, and on each cycle the
six nonroot coordinates of $\Sigma_{3,2}$ are
$(168,129,142,142,129,168)$. They follow from
$F_iF_{7-i}=(8,5,6,6,5,8)$ and
$(v_1,\ldots,v_6)=(0,3,2,2,3,0)$ in (38.6).
Thus (38.4), with these coordinates and the basic tuples of Theorem
35.4, also fixes every full shift in (38.7). Formula (38.2) gives
$505$ modes and projective dimension $491$; Proposition 35.6 gives
multiplicities one and $201$. Subtracting canonical degrees three
and five from $505$ gives $502$ and $500$. For $b=1$, (35.14)
is $1+101-100=2$, agreeing with Theorem 29.2 and (33.2).
The pair's $202$ is therefore a synchronized amplification of a
single-cycle type of two, not a correction to a supposed type one.
$\square$

### 38.2 The mathematical boundary of the common-root application

**Proposition 38.4 (What the shared-root correspondence preserves).**
The conclusions (35.2), (35.10)–(35.12), (36.2)–(36.4),
(37.2)–(37.12) and (38.2)–(38.7) concern the graph consisting of
one common vertex and otherwise disjoint labelled odd cycles, with no
additional edges. They neither identify the full middle of the relation
resolution nor determine a supplied ordered history or a physical
operator. The terminal rank $202$ in (38.7) is an algebraic type, not
a physical dimension, a full zero-mode count or an Atiyah–Singer index.

Proof. The forward realization in Theorem 35.2 uses the fact that a
root state is a single bit, and that agreement of its multiplicity
$t$ allows all local root-one rows to be moved to the same positions.
The union remains independent because every edge is already tested
in one constituent cycle. The descent in Theorem 35.4 uses the stronger
fact that the local interior generators have degree $2j+1$ and root
$j$; it is this relation that makes the inequality $2t<m$ choose a
root-zero row for every local representation, with the complementary
case including equality. Neither proof supplies that property for
an arbitrary shared boundary. With several shared vertices or a
shared path, separate vertex totals need not specify the frequencies
of joint boundary states, and a common removable boundary state would
require a new proof. Extra cross edges can invalidate a rowwise union
even when every local row is legal. Those graph classes are excluded.

The maps retain occupancies, degree, root and the stated algebraic
action. They do not retain row order: even permuting two distinct
rows leaves $(m,c)$ unchanged. They can also lose unordered row
correlations. On any one of the constituent cycles, the arrays
$\{\{1\},\{3\}\}$ and $\{\varnothing,\{1,3\}\}$, with all
other vertices empty, are both legal and have identical degree-two
occupancies. They are not the same unordered array. Thus no recovery
of a prescribed native ordered FIB history or an allowed physical
operation follows from the existence of some common realization.

The rank in (38.7) counts summands in one final free module. Computing
an alternating invariant of a complex requires its other terms and
maps or a justified equivalent description. A zero-mode or analytic
index interpretation additionally requires an operator, its domain,
its grading and the appropriate kernel or ellipticity comparison.
None is specified by (38.7); the analytic constructions of chapters
30 and 34 have their own stated modules and operators and are not
transported to this graph by equality of a number. The complete final
module does not claim a list of the $491$ differential matrices or
all intermediate Betti numbers.

The local integer decomposition is Theorem 28.2; the canonical
classification and face layers are Miyazaki's §4 results with the
explicit correspondence in Theorem 35.4, as used in chapters 29 and
31–32. The action and terminal-duality precedents are §§31.3–31.4
and chapter 33; chapter 34 distinguishes an action from observations
that forget it. Matsuda–Ohsugi–Shibata's Proposition 1.3 supplies
the singleton-clique toric-fiber precedent, Barile–Bruns supply the
interior and Ext identifications, and Stacks supplies the precise
Auslander–Buchsbaum formula. These are intermediate suppliers in
the common-root application. Its additional derivation is the uniform
root-compatible descent, the resulting complete compatible-tuple
classification and counts, and their consequences for the shared-root
quotient action and terminal module. This attribution makes no global
priority claim for the classic supplier results or for graph gluing
in general. $\square$

[AB38]: https://stacks.math.columbia.edu/tag/090U

## 追加锚（本行以下为增补区）

## 39. Separator completeness for common-copy occupancy observations

**Definition 39.1 (A shared induced separator and its attainable histograms).**
Let $H$ be a finite simple graph with $q$ vertices, and let
$G_1,\ldots,G_b$, $b\ge1$, be finite simple graphs whose pairwise
vertex intersections are exactly $V(H)$. Each induces exactly $H$
there. Their private vertex sets are disjoint. The union graph $G$
has precisely the union of their edge sets, with no extra cross edges.
Write $\Sigma_H=\operatorname{Ind}(H)$, including the empty set.
A realization of local totals $c^{(a)}$ in degree $m\ge0$ is an
array of $m$ independent sets of $G_a$, with occupancy $c^{(a)}_v$
at each vertex $v$. All branches use the same number $m$ of rows.
For such an array define the separator histogram

$$
h_J=\#\{r:I_r\cap V(H)=J\},\qquad J\in\Sigma_H.
\tag{39.1}
$$

Its entries are nonnegative integers satisfying

$$
\sum_{J\in\Sigma_H}h_J=m,\qquad
c_v=\sum_{J\ni v}h_J\quad(v\in V(H)).
\tag{39.2}
$$

Thus one-point separator totals are a projection of the full
histogram. For specified local totals put

$$
\mathcal B_a(m,c^{(a)})=
\{h:\text{some local realization of }c^{(a)}\text{ has histogram }h\}.
\tag{39.3}
$$

This set ranges over every realization of those totals. It is not
the histogram of one arbitrarily chosen array. Unless otherwise
stated the local totals are realizable and agree on $V(H)$.
A global realization asks for one array of independent sets of $G$
with all those restrictions; it does not ask to recover a supplied
ordered array. This is the occupancy observation of Definition 28.1
on an overlapping family of graphs.

**Theorem 39.2 (The separator criterion and its universal first-moment boundary).**
In Definition 39.1, a global realization exists exactly when

$$
\bigcap_{a=1}^{b}\mathcal B_a(m,c^{(a)})\ne\varnothing.
\tag{39.4}
$$

For a fixed $H$ and any fixed $b\ge2$, the following universal
property holds if and only if $H$ is complete: for every family
$G_1,\ldots,G_b$ of the stated kind, every $m\ge0$, and every
family of realizable local totals agreeing on $H$, a global
realization exists. Equivalently the same characterization holds
when one quantifies over all finite families with $b\ge2$.

Proof. Restrict a global array to each branch. Its separator
histogram is the same in every restriction, proving necessity
in (39.4). Conversely choose $h$ in the intersection and choose,
on each branch, a realization producing this $h$. Partition each
array into blocks indexed by $J\in\Sigma_H$. Each $J$ block
has $h_J$ rows on every branch. Match these rows in any order
within each block and take their rowwise unions. All copies of
the separator agree. Every edge of $G$ belongs to some branch,
where that row is independent, so the union is independent.
Its private and shared occupancies are the required ones. This
proves sufficiency for all $b$, not only two.

If $H$ is the complete graph on $q$ vertices, its legal patterns
are just $\varnothing$ and the $q$ singletons. Every realization
has the uniquely determined histogram

$$
h_{\{v\}}=c_v,\qquad
h_{\varnothing}=m-\sum_{v\in V(H)}c_v.
\tag{39.5}
$$

Local realizability ensures the last entry is nonnegative.
Matching one-point totals therefore makes all the nonempty sets
$\mathcal B_a$ contain this same unique histogram, proving the
universal property. This is the elementary row-level clique
gluing underlying Matsuda–Ohsugi–Shibata, *Toric rings and ideals
of stable set polytopes*, [Proposition 1.3][MOS39]; the present observation
also specifies the existential quantifier over local arrays.

If $H$ is not complete, choose distinct nonadjacent vertices
$a_0,b_0$ of $H$. On the left add one private vertex $x$ and the
edges $a_0-x-b_0$; on the right add private vertices $y,z$ and the
edges $a_0-y-z-b_0$. Add no other private edges. Retain all original
edges of $H$, so both induced separators are exactly $H$.
Take $m=2$, occupancy one at $a_0,b_0,x,y,z$ wherever present, and
zero at every other vertex of $H$. On the left the two rows,
in the order $(a_0,x,b_0)$, can be $101$ and $010$; on the right,
in the order $(a_0,y,z,b_0)$, they can be $1010$ and $0101$.
All added separator coordinates are zero in both arrays.

Every edge in either path joins two vertices of occupancy one.
Their occupied row sets are disjoint singleton subsets of two
rows, hence are complements. Along the length-two left path,
$a_0$ and $b_0$ must occupy the same row. Along the length-three
right path, they must occupy opposite rows. Thus all left
histograms have $h_{\{a_0,b_0\}}=1$, and all right histograms have
$h_{\{a_0,b_0\}}=0$. Their intersection is empty despite identical
one-point totals. Equivalently the five occupied vertices form
the odd cycle $a_0-x-b_0-z-y-a_0$ and cannot be colored by two rows.
For any prescribed $b>2$, take the extra branches to be copies
of $H$ itself, with the same separator vertices and totals; each
is locally realizable, and the first two branches still obstruct
the intersection. This proves the converse with its full
universal quantifiers. $\square$

**Proposition 39.3 (Degenerate boundaries and the two gluing questions).**
The criterion (39.4) includes $b=1$, $m=0$, and the empty
separator. These cases do not extend the universal converse to
$b=1$ or to a test restricted to degree zero. Compatible
prescribed histograms and compatible total fibres are distinct
questions even for the same graphs.

Proof. For $b=1$, (39.4) says precisely that the supplied local
totals are realizable, regardless of $H$. For $m=0$, realizability
forces every total and histogram entry to be zero; the empty
array is global for every $H$. If $q=0$, the separator has only
the empty pattern and $h_{\varnothing}=m$; arbitrary local arrays
can be aligned. The empty graph on zero vertices is complete
under the pairwise adjacency convention, consistently with
Theorem 39.2. A noncomplete separator can also have compatible
particular totals, for example all-zero occupancies in any
degree; its failure is failure of the universal guarantee.

For prescribed local arrays, row permutations align their
separator patterns exactly when their full histograms agree.
For totals alone one may choose another array in each fibre,
and the correct condition is the intersection (39.4). Neither
criterion identifies an unknown original array. The joint
coordinate and quantitative mismatch for the three-position
separator are developed in §40 of the
[same-subject continuation](AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS_CONTINUATION_2.md),
followed there by the shared-edge canonical application. $\square$

[MOS39]: https://arxiv.org/html/1603.01850v1

## 追加锚（本行以下为增补区）
