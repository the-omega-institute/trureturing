# Native FIB: guarded global attainment near the transition

This volume gives the new handwritten results N1--N6 for the full open native
four-coordinate problem. The unrestricted spectral reduction, scalar
attainment, and guard criterion are credited premises from [*Native FIB:
unrestricted four-dimensional spectral reduction and attainment*](FIB_NATIVE_FOUR_DIMENSIONAL_SPECTRAL_REDUCTION_AND_ATTAINMENT.md),
Theorems 3.2--3.4 and Sections 8--11; call this manuscript [S]. The trial
profile below is never identified with the scalar optimum.

## 1. Native source and credited scalar interface

**Definition 1.1 (Open source and commands).** Fix $0<Z<1$, put
$r=1-Z$ and $H=r/2$, and write the current ray as
$(k,\alpha,\beta)\in(0,H)\times\mathbb T^2$. For signed real $h,t$,

$$
P_h(k,\alpha,\beta)=(k+h,\alpha,\beta),\quad 0<k+h<H,
$$

and

$$
Q_t(k,\alpha,\beta)=\left(k,\alpha+t/2,\beta+(1/2-k/r)t\right).
$$

The first domain is exactly the displayed strict inequality and the second is
all of the source. All finite lawful histories, prefixes, and prescribed
simultaneous paths are retained.

**Definition 1.2 (Original output metric).** With the five ordered edges
$((0,1),(0,2),(0,3),(1,13),(3,13))$, let $D$ be the preparation-dependent
real map from two complex coordinates to the ten original outputs. On the
source,

$$
y=D(A(k)e^{i\alpha},B(k)e^{i\beta}),\quad
A(k)=2\sqrt{k(H-k)},\quad B(k)=2\sqrt{Zk},
$$

and

$$
D^{\mathsf T}D=4I_2\oplus I_2,\qquad
\|D(z,w)\|_2^2=4|z|^2+|w|^2.
$$

**Definition 1.3 (Unrestricted contracts).** An at-most-$n$ literal model has
an arbitrary encoder into at most $n$ real coordinates, one fixed affine
decoder, and fixed affine ambient updates for every signed $P_h,Q_t$ on
their source domains. Both affine offsets and arbitrary encoder irregularity
are allowed. $\mathsf G$ additionally requires straight domains to be
saturated under encoder fibers; $\mathsf P$ requires one affine update for
every prescribed path on its full all-times domain; $\mathsf{GP}$ requires
both. Thus

$$
\mathsf{GP}\subseteq\mathsf G\subseteq\mathsf L,\qquad
\mathsf{GP}\subseteq\mathsf P\subseteq\mathsf L.
$$

Errors use the original ten-output Euclidean norm and the supremum over the
open source.

**Definition 1.4 (Normalized scalar family).** Put

$$
\tau=\frac Z{4H}=\frac Z{2(1-Z)},\quad
Z=\frac{2\tau}{1+2\tau},\quad
H=\frac1{2(1+2\tau)},\quad s(x)=\sqrt{x(1-x)}.
$$

The scalar variable is $x=k/H$, so $0<x<1$ on the source. Let $\mathcal E_2$ contain

$$
R(x)=c_1e^{\lambda_1x}+c_2e^{\lambda_2x},
\qquad
R(x)=(c_0+c_1x)e^{\lambda x},
$$

with arbitrary complex coefficients and exponents, including zero,
one-mode, vanishing-coefficient, collision, and confluent cases. Define

$$
J_\tau(R)=\max_{0\le x\le1}
\left(|R(x)-s(x)|^2+\tau x\right),\qquad
T_4(\tau)=\min_{R\in\mathcal E_2}J_\tau(R).
$$

The closed scalar maximum is equal to the open-source supremum by continuity
and interior limits; no endpoint source ray is introduced.

**Theorem 1.5 (Credited premise [S]).** We use the following exact source
results. Every unrestricted at-most-four literal competitor is dominated by
some $R\in\mathcal E_2$, every such profile has a lawful four-real-coordinate
realization, and

$$
(e_{4,\mathsf L}^{\rm aff}(Z))^2=16H^2T_4(\tau).
$$

A scalar minimum exists for every $\tau>0$, and every minimizer has minimal
order two when $0<\tau<1$. In that range all four contracts have common
infimum $4H\sqrt{T_4(\tau)}$. This endpoint is attained in $\mathsf G$ if
and only if at least one global minimizer is (i) confluent with nonzero
linear coefficient, (ii) distinct with some $\operatorname{Re}\lambda_j\ne0$,
or (iii) purely imaginary $\lambda_j=i\omega_j$ with
$|\omega_1-\omega_2|\le2\pi$. A minimal purely imaginary pair with
$\Omega=|\omega_1-\omega_2|>2\pi$ is bad; $\Omega=2\pi$ is good because
the first alias is across the absent scalar endpoints. A profile realizes
squared original error $16H^2J_\tau(R)$. The credited realization preserves
all preparations, signed commands, affine offsets, finite histories,
prescribed paths, and full all-times guards.

## 2. N1: every legal alias multiple

**Definition 2.1 (Bad pair and defect).** Fix $0<\tau<1$, set
$a=1-\tau$, and for a bad pair write

$$
R(x)=c_1e^{i\omega_1x}+c_2e^{i\omega_2x},\quad
c_1c_2\ne0,\quad \Omega=|\omega_1-\omega_2|>2\pi.
$$

Put $p=2\pi/\Omega<1$, $T=J_\tau(R)$ and $\delta=T-\tau$. Then

$$
|R(x)-s(x)|\le\sqrt{T-\tau x}\quad(0\le x\le1).
\tag{2.1}
$$

**Lemma 2.2 (N1, periodic-modulus obstruction).** For every positive integer
$n$ with $d=np<1$,

$$
\sqrt{d(1-d)}\le\sqrt\delta+\sqrt{\delta+\tau d}.
\tag{2.2}
$$

Whenever also $d<a$,

$$
\delta\ge\frac{d(a-d)^2}{4(1-d)}.
\tag{2.3}
$$

**Proof.** Since $(\omega_1-\omega_2)p=\pm2\pi$, there is a unit $q$ with
$R(x+p)=qR(x)$. Thus $|R(1-d)|=|R(1)|$. At $x=1$, (2.1) gives
$|R(1)|\le\sqrt\delta$ and $\delta\ge0$. At $x=1-d$, put
$S=\sqrt{d(1-d)}$. The triangle inequality and (2.1) give

$$
S\le |R(1-d)|+|R(1-d)-S|
\le\sqrt\delta+\sqrt{\delta+\tau d}.
$$

This is (2.2). If $d<a$, put $t=\sqrt\delta$ and
$h=(S^2-\tau d)/(2S)>0$. If $t\ge S$ then $t\ge h$; if $t<S$, squaring
$S-t\le\sqrt{t^2+\tau d}$ gives $t\ge h$. Hence

$$
\delta\ge h^2
=\frac{[d(a-d)]^2}{4d(1-d)}
=\frac{d(a-d)^2}{4(1-d)}.
$$

This uses arbitrary coefficient phases and arbitrary common frequency. $\square$

## 3. N2: a common-frequency-free cusp bound

**Lemma 3.1 (N2, coefficient and cusp estimates).** If a bad pair has
$T\le1$, then

$$
|c_1|+|c_2|\le\frac32,\qquad
\bigl||c_1|-|c_2|\bigr|\le\sqrt\delta,
\tag{3.1}
$$

and

$$
\delta\ge\frac{a^4}{9216\,\Omega^2}.
\tag{3.2}
$$

**Proof.** The corridor gives $|R(x)|\le1/2+\sqrt T\le3/2$. Over an
interval of length $p<1$, the relative phase makes a full turn, so the
summands align at some point and $|c_1|+|c_2|\le3/2$. The reverse triangle
inequality at $x=1$ gives the second part of (3.1).

Relabel so $|c_1|\ge|c_2|$, put $\Delta=\omega_2-\omega_1$, and compare
the value at $1-y$ with that at $1$ after multiplying by a unit phase.
Using $|e^{iv}-1|\le|v|$ and $|c_2|\le3/4$,

$$
|R(1-y)|\le\sqrt\delta+\frac{3\Omega}{4}y.
\tag{3.3}
$$

The reverse corridor and $\sqrt{\delta+\tau y}\le
\sqrt\delta+\sqrt\tau\sqrt y$ give

$$
|R(1-y)|\ge[\sqrt{1-y}-\sqrt\tau]\sqrt y-\sqrt\delta.
\tag{3.4}
$$

For $0\le y\le a/2$,

$$
\sqrt{1-y}-\sqrt\tau
=\frac{a-y}{\sqrt{1-y}+\sqrt\tau}\ge\frac a4.
$$

Combining (3.3)--(3.4),

$$
\frac a4\sqrt y\le2\sqrt\delta+\frac{3\Omega}{4}y.
\tag{3.5}
$$

Choose $y=a^2/(36\Omega^2)$; it is positive and below $a/2$ because
$a<1$ and $\Omega>2\pi$. Substitution into (3.5) gives

$$
\frac{a^2}{24\Omega}
\le2\sqrt\delta+\frac{a^2}{48\Omega},
$$

so $\sqrt\delta\ge a^2/(96\Omega)$ and (3.2) follows. The common
frequency has disappeared; only $\Omega$ remains. $\square$

## 4. N3: the uniform sixth-power bad-class gap

**Theorem 4.1 (N3).** Every bad profile obeys

$$
J_\tau(R)>\tau+\frac{(1-\tau)^6}{65536\pi^2}
\qquad(0<\tau<1).
\tag{4.1}
$$

Consequently,

$$
\inf_{\text{bad }R}J_\tau(R)\ge
\tau+\frac{(1-\tau)^6}{65536\pi^2}.
\tag{4.2}
$$

The infimum conclusion is intentionally non-strict.

**Proof.** Write $B=\tau+a^6/(65536\pi^2)$. Since $B<\tau+a=1$,
$T>1$ implies $T>B$. Suppose $T\le1$. If $p\le3a/4$, let $n$ be the
least positive integer with $np\ge a/8$. Then

$$
a/8\le d=np<a/8+p\le7a/8<a.
$$

Lemma 2.2 gives $\delta\ge a^3/2048$, which is strictly larger than
$a^6/(65536\pi^2)$ because $a^3<32\pi^2$. If $p>3a/4$, then
$\Omega=2\pi/p<8\pi/(3a)$ and Lemma 3.1 gives

$$
\delta\ge\frac{a^4}{9216\Omega^2}
>\frac{a^6}{65536\pi^2},
$$

using $9216=9\cdot1024$. The two cases exhaust $p\in(0,1)$, proving
(4.1). Taking an infimum keeps only (4.2), since pointwise strict
inequalities need not give a strict infimum. $\square$

## 5. N4: an explicit good witness

**Definition 5.1 (Trial profile).** For $3/4\le\tau<1$ let

$$
a=1-\tau,\qquad c=\frac{a^{3/2}}2,\qquad
b=\frac{a^{7/2}}{12},\qquad L=\frac1{c^2}=\frac4{a^3},
$$

and define

$$
R_\tau(x)=b+c(1-e^{-L(1-x)})
=(b+c)-ce^{-L}e^{Lx}.
\tag{5.1}
$$

**Lemma 5.2 (Elementary exponential bounds).** For $u\ge0$,

$$
(1-e^{-u})^2\le u/2,
\tag{5.2}
$$

for $0\le u\le1$, $1-e^{-u}\ge u/2$, and for $u\ge1$,
$1-e^{-u}>1/2$.

**Proof.** For $g(u)=(1-e^{-u})^2$,

$$
g'(u)=2e^{-u}(1-e^{-u})\le1/2
$$

because $t(1-t)\le1/4$ on $[0,1]$; integration from $0$ proves
(5.2). Also $e^{-v}\ge1-v$, so
$1-e^{-u}=\int_0^u e^{-v}\,dv\ge u-u^2/2\ge u/2$ for $u\le1$.
The $u\ge1$ claim follows from $1-e^{-u}\ge1-e^{-1}>1/2$. $\square$

**Theorem 5.3 (N4, exact seventh-power feasible value).** The profile
$R_\tau$ has minimal order two, is good, and

$$
J_\tau(R_\tau)=\tau+\frac{a^7}{144}.
\tag{5.3}
$$

Thus $T_4(\tau)\le\tau+a^7/144$ on $[3/4,1)$.

**Proof.** The exponents $0,L$ are distinct and both coefficients in (5.1)
are nonzero, so the order is two. The positive real exponent makes the
profile good under Theorem 1.5.

Put $y=1-x$, $u=y/c^2$,

$$
r(y)=b+c(1-e^{-u}),\quad S(y)=\sqrt{y(1-y)},\quad
V(y)=\sqrt{b^2+\tau y}.
$$

It suffices to prove $|r-S|\le V$ on $[0,1]$. For $0\le y\le1/2$,
Lemma 5.2 gives

$$
0\le c(1-e^{-y/c^2})\le\sqrt{y/2}\le S(y),
$$

so $r\le S+V$. For $1/2\le y\le1$, $b/c=a^2/6<1$, hence
$r<b+c<2c=a^{3/2}$. Since $a\le1/4$ and $\tau\ge3/4$,

$$
a^3\le1/64<3/8\le\tau/2\le\tau y,
$$

so $r<\sqrt{\tau y}\le V\le S+V$. This proves the upper side.

For the lower side let $\ell=S-V$. If $y\ge a$, then $1-y\le\tau$, so
$\ell\le0<r$. If $0\le y\le a$, discard $b^2$ from $V$:

$$
\ell\le\frac{(a-y)\sqrt y}{\sqrt{1-y}+\sqrt\tau}.
$$

The denominator is at least $2\sqrt\tau\ge\sqrt3$, while the maximum of
$(a-y)\sqrt y$ on $[0,a]$ is $2a^{3/2}/(3\sqrt3)$. Therefore
$\ell\le2a^{3/2}/9<c/2$. If $u\le1$, Lemma 5.2 and $b=a^2c/6$ give

$$
r\ge b+\frac y{2c},\qquad
b+\frac y{2c}-\frac{a\sqrt y}{\sqrt3}
=\left(\sqrt{\frac y{2c}}-a\sqrt{\frac c6}\right)^2\ge0,
$$

so $r\ge a\sqrt y/\sqrt3\ge\ell$. If $u\ge1$, then
$r\ge b+c(1-e^{-1})>c/2>\ell$. Thus the corridor holds. At $x=1$,
$R_\tau(1)=b$ and $s(1)=0$, giving equality $\tau+b^2$; hence
$J_\tau(R_\tau)=\tau+a^7/144$. The endpoint is a scalar limit, not a
native endpoint state. This is a feasible value only, not an optimum claim.
$\square$

**Proposition 5.4 (Native witness, decoder, and all-times guards).** The
trial profile has a four-real-coordinate model with squared error

$$
16H^2\left(\tau+\frac{a^7}{144}\right).
\tag{5.4}
$$

**Proof.** Store the real and imaginary parts of

$$
z_0=e^{i\alpha},\qquad z_1=e^{Lk/H}e^{i\alpha}.
$$

Use the fixed real-linear decoder

$$
\mathcal D(z_0,z_1)=D(2H((b+c)z_0-ce^{-L}z_1),0),
$$

initialize at any prepared $k_0$ by $(z_0,z_1)=(1,e^{Lk_0/H})$, and set

$$
\mathcal U_h(z_0,z_1)=(z_0,e^{Lh/H}z_1),\qquad
\mathcal V_t=e^{it/2}I.
$$

These satisfy the native update equations for every lawful signed command,
including negative and zero commands; maps on empty domains are still
assigned. On the actual image,

$$
\kappa(z_0,z_1)=H\log|z_1|/L=k.
$$

Thus the straight guard is $0<\kappa+h<H$. For a prescribed path with
height velocity $a_c(u)$ and phase velocity $b_c(u)$, define

$$
\eta(u)=\int_0^u a_c(v)\,dv,\quad
\Delta=\eta(T_{\rm p}),\quad
L_{\rm path}=\int_0^{T_{\rm p}}b_c(u)\,du,\quad
C=\int_0^{T_{\rm p}}\eta(u)b_c(u)\,du.
$$

The exact source guard is

$$
0<k+\eta(u)<H\quad(0\le u\le T_{\rm p}),
$$

and the source endpoint is

$$
k'=k+\Delta,\quad
\alpha'=\alpha+L_{\rm path}/2,\quad
\beta'=\beta+(1/2-k/r)L_{\rm path}-C/r.
$$

The encoded path map is the fixed affine map
$e^{iL_{\rm path}/2}\mathcal U_\Delta$. For two successive relative paths,
the mixed integral is $C_1+C_2+\Delta_1L_2$, exactly as in the native
source. Every truncation uses its own integrals and full all-times guard,
and every finite concatenation preserves the same current-state error.
The Gram identity and (5.3) give (5.4). $\square$

## 6. N5: a nonempty guarded global-attainment window

**Definition 6.1 (Window constant).** Set

$$
\varepsilon_0=\frac9{4096\pi^2}.
$$

**Theorem 6.2 (N5, every minimizer is good near $\tau=1$).** If

$$
1-\varepsilon_0\le\tau<1,
\tag{6.1}
$$

then every global minimizer over the entire complex $\mathcal E_2$ is good.
Consequently, for every allowed preparation, both $\mathsf G$ and
$\mathsf{GP}$ attain their common infimum whenever

$$
\frac{2(1-\varepsilon_0)}{3-2\varepsilon_0}\le Z<\frac23.
\tag{6.2}
$$

**Proof.** Let $a=1-\tau$. Then $0<a\le\varepsilon_0<1/4$ and Theorem
5.3 applies. Since $\varepsilon_0=144/(65536\pi^2)$,

$$
T_4(\tau)\le\tau+\frac{a^7}{144}
\le\tau+\frac{a^6}{65536\pi^2}.
\tag{6.3}
$$

Theorem 1.5 supplies a global minimizer and says that every one is minimal
order two. If a minimizer were bad, Theorem 4.1 would give the strict
opposite inequality to (6.3), a contradiction. Hence every minimizer is
good. At $a=\varepsilon_0$ the two comparison bounds tie, but the
individual bad-profile lower bound is strict, so the lower window endpoint
is included. Theorem 1.5 now supplies an attained $\mathsf{GP}$ optimum and
therefore an attained $\mathsf G$ optimum with value
$4H\sqrt{T_4(\tau)}$. The trial value is not substituted for $T_4$.
The map $Z=2\tau/(1+2\tau)$ is strictly increasing, and gives exactly
(6.2). All original preparations, signed commands, offsets, finite
histories, and full all-times path guards remain in force. $\square$

**Corollary 6.3 (Guarded tolerance endpoint).** In the interval (6.1), the
finite tolerance set of each guarded class is

$$
[4H\sqrt{T_4(\tau)},\infty).
$$

**Proof.** The endpoint is attained by Theorem 6.2, all four infima agree by
Theorem 1.5, and smaller tolerances are infeasible. $\square$

## 7. N6: necessary and sufficient comparisons

**Proposition 7.1 (Necessary conditions for a surviving bad optimum).** If
$0<\tau<1$ and even one global minimizer is bad, then

$$
T_4(\tau)>\tau+\frac{(1-\tau)^6}{65536\pi^2},
$$

every legal multiple $d=np<1$ obeys (2.2), and (2.3) holds for $d<1-\tau$.
Moreover $T_4(\tau)<1$, so (3.1)--(3.2) apply, and necessarily
$\tau<1-\varepsilon_0$.

**Proof.** The zero profile has

$$
J_\tau(0)=\max_{0\le x\le1}\bigl(x(1-x)+\tau x\bigr)
=\frac{(1+\tau)^2}{4}<1,
$$

so $T_4<1$. Apply Theorem 4.1 and Lemmas 2.2 and 3.1 to a bad minimizer.
The window theorem excludes bad minimizers for
$\tau\ge1-\varepsilon_0$, proving the final necessary restriction. This
does not assert existence below the window. $\square$

**Theorem 7.2 (Feasible-witness sufficiency).** If $0<\tau<1$ and some
$W\in\mathcal E_2$ satisfies

$$
J_\tau(W)\le\tau+\frac{(1-\tau)^6}{65536\pi^2},
\tag{7.1}
$$

then every global minimizer is good and both guarded endpoints are attained.

**Proof.** The inequality gives $T_4\le J_\tau(W)$; Theorem 1.5 supplies a
global minimal-order-two minimizer. Theorem 4.1 strictly excludes every bad
one, including equality in (7.1), and all remaining minimal forms are good.
The credited native realization then attains both guarded endpoints. $\square$

**Proposition 7.3 (Transition bad-minimizer witness).** At $\tau=1$ (hence
$Z=2/3$), put

$$
R_\star(x)=\frac{\sin(2\pi(1-x))}{4\pi}
=\frac{e^{-2\pi i x}-e^{2\pi i x}}{8\pi i}.
$$

Then $R_\star$ has minimal order two and is transition-bad in the same
spectral sense because its two frequencies have separation $4\pi>2\pi$, and

$$
J_1(R_\star)=T_4(1)=1.
$$

The zero profile $W=0$ also satisfies the displayed threshold in (7.1),
$J_1(W)=1$. Thus the transition has a bad global minimizer in this spectral sense. This does not imply
nonattainment: the credited transition attainment result in [S] separately
supplies guarded attainment at $\tau=1$.

**Proof.** The two displayed coefficients are nonzero and the exponents are
distinct. The profile has zeros at $x=0$ and $x=1/2$ but is nonzero at
$x=1/4$, whereas a nonzero one-mode profile $ce^{\lambda x}$ has no zeros;
therefore its order is exactly two. Write $y=1-x$,

$$
r(y)=R_\star(1-y)=\frac{\sin(2\pi y)}{4\pi},\qquad
S(y)=\sqrt{y(1-y)},\qquad V(y)=\sqrt y.
$$

For $0\le y\le1/2$, $0\le r(y)\le y/2\le V(y)$ and
$0\le S(y)\le V(y)$, so $|r(y)-S(y)|\le V(y)$. For
$1/2\le y\le1$, one has $-1/(4\pi)\le r(y)\le0$. Also

$$
V(y)-S(y)=\sqrt y\bigl(1-\sqrt{1-y}\bigr)>\frac18,
$$

because $\sqrt y\ge1/2$, $\sqrt{1-y}\le1/\sqrt2<3/4$, and
$\pi>2$. Hence $r(y)>S(y)-V(y)$, while $r(y)\le0\le S(y)+V(y)$.
Thus $|R_\star(x)-s(x)|^2\le1-x$ on the whole closed scalar interval,
so $J_1(R_\star)\le1$. At $x=1$, $s(1)=0$ and every profile satisfies
$|R(1)-s(1)|^2+1\ge1$, so $T_4(1)\ge1$; equality at $x=1$ for $R_\star$
gives $J_1(R_\star)=T_4(1)=1$. The two exponents differ by $4\pi$, so the
profile is transition-bad in this spectral sense. Finally, $J_1(0)=\max_{0\le x\le1}(2x-x^2)=1$, so the
threshold in (7.1) is met at equality. The final statement uses the
separately credited transition attainment conclusion and makes no claim that
a bad minimizer forces nonattainment. $\square$

**Corollary 7.4 (Exact remaining obligation).** The interval
$0<\tau<1-\varepsilon_0$ remains unresolved. This volume does not evaluate
$T_4$, classify all global minimizing spectra, prove uniqueness, or establish
sharpness of any displayed constant. A bad minimizer would not exclude a
different good minimizer, and failure of the trial comparison would not prove
nonattainment.

**Proof.** Proposition 7.1 is necessary and Theorem 7.2 is sufficient; neither
is an equivalence on the complementary range. Theorem 1.5 uses existence of
at least one good global minimizer, not exclusion of one bad minimizer. $\square$

The quantifiers are distinct. One bad minimizer does not imply
nonattainment, because another minimizer may be good. Nonattainment would
require that all global minimizers are bad. Theorem 7.2 instead supplies a
sufficient upper threshold that excludes all bad minimizers at once and
hence guarantees at least one good minimizer.

## 8. Boundary and degeneracy conventions

**Proposition 8.1 (Scope at boundaries).** The following conventions are part
of the statements.

1. $\tau=1$ is excluded from the trial and window; the credited transition
   result handles $\tau\ge1$, and $a,c,b,L$ are not continued to $a=0$.
2. $\tau=3/4$ is included in N4, including all overlap points $y=0,1/2,a,1$
   and $u=1$.
3. $\tau=1-\varepsilon_0$ is included because N3 is strict pointwise.
4. $\Omega=2\pi$ is good; badness is strictly $\Omega>2\pi$, with arbitrary
   common frequency.
5. Zero coefficients, lower-order profiles, collisions, and confluent forms
   remain in $\mathcal E_2$; no separate-coefficient bound near collisions is
   assumed.
6. Scalar endpoint evaluations are limits on the closed scalar interval and
   do not add endpoint source rays or endpoint guards.

**Proof.** Items 1 and 5 are part of Definitions 1.4 and Theorem 1.5. Item 2
follows from the closed inequalities in Lemma 5.2 and Theorem 5.3. Item 3
uses the strict inequality of Theorem 4.1. Item 4 follows from the exact
period spacing in Lemma 2.2 and the credited guard criterion. Item 6 is
Definition 1.4. $\square$

## 9. Result map and original consequence

**Definition 9.1 (Attribution map).**

| Result | Location | Source status |
|---|---|---|
| Native source, commands, metric, contracts | Definitions 1.1--1.3 | Reused from [S], Sections 1--2 |
| Full unrestricted $\mathcal E_2$ reduction and error factor | Theorem 1.5 | Credited [S], Theorems 3.2--3.4, Proposition 8.1 |
| Scalar minimum and minimal order | Theorem 1.5 | Credited [S], Theorems 3.3, 9.4--9.6 |
| Good/bad criterion and path/guard bridge | Theorem 1.5 | Credited [S], Theorems 3.4, 11.1--11.4 |
| Alias obstruction | Lemma 2.2 | New N1 |
| Cusp estimate | Lemma 3.1 | New N2 |
| Sixth-power gap | Theorem 4.1 | New N3 |
| Seventh-power witness and native model | Theorem 5.3, Proposition 5.4 | New N4 |
| Guarded window | Theorem 6.2 | New N5 using [S] |
| Necessary/sufficient threshold statements | Proposition 7.1, Theorem 7.2 | New N6 using [S] |
| Transition bad-minimizer witness | Proposition 7.3 | New boundary witness using [S] for transition attainment |
| Complementary interval | Corollary 7.4 | Explicit remaining open obligation |

**Proposition 9.2 (Native consequence in the certified window).** For every
allowed preparation and every $Z$ in (6.2), an actual four-real-coordinate
model attains

$$
4H\sqrt{T_4(\tau)}
$$

in both guarded contracts, with the original ten-output norm, all signed real
commands, all finite lawful histories, and every prescribed path on its full
all-times domain.

**Proof.** Theorem 6.2 gives a good global minimizer, and Theorem 1.5 gives
its native realization, affine updates, height-fiber guard saturation,
prescribed-path maps, truncations, and concatenations. Its scalar error
identity gives the displayed original value. The guard is always the source
condition $0<k+\eta(u)<H$ at every prescribed time; no endpoint-only guard is
used. $\square$

## 10. Remaining exact questions

**Openproblem 10.1 (Complementary guarded attainment).** Decide whether
every $0<\tau<1-\varepsilon_0$ has at least one good global minimizer. A
nonattainment proof must exclude every good global minimizer, not merely
exhibit a bad one.

**Openproblem 10.2 (Exact scalar minimax).** Determine $T_4(\tau)$ and the
complete minimizing spectra in the unresolved range, including distinct,
confluent, real, complex, and purely imaginary possibilities. The displayed
trial value is a feasible upper bound and is not an evaluation.

## 追加锚（本行以下为增补区）
