# FIB strict-real joint incidence: overlap-stratified finite response lifts

## 1. The four-endpoint relation and its overlap index

Use the complete fixed-terminal inverse and the same-base relation from
\`FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X\`, especially Definition 6.3.
Thus \(p\ne24\), the two \(J\)-endpoints \(W_0,W_1\) have independently
chosen terminal values \(m_0,m_1\), and the two \(M\)-endpoints \(W_2,W_3\)
have the common terminal value \(m\). The within-pair conditions are

$$
W_0\ne W_1,\qquad W_2\ne W_3.
$$

Define the cross-pair overlap index

$$
\boxed{\kappa
=\left|\{W_0,W_1\}\cap\{W_2,W_3\}\right|}
\in\{0,1,2\}.
$$

For each endpoint write

$$
\tau_i\in\{O,E\},
$$

according as \(W_i\) is reconstructed from the ordinary layer
\(\mathcal R(p,v,m_i)\) or the exceptional layer
\(\mathcal E(p,v,m_i)\), with \(m_2=m_3=m\). Equal worlds have equal
labels and equal terminal values. This label records the inverse chart used
to count the endpoint; it does not add a new source or relax any strict
guard.

The purpose of \(\kappa\) is only to stratify the unresolved relation. It
does not assert that any stratum is nonempty.

## 2. The overlap-stratified lift

**Proposition 2.1 (Finite response lift by overlap stratum).** Fix
\((p,v)\) with \(p\ne24\) and a solution of Definition 6.3. Then:

1. If \(\kappa=2\), the unordered endpoint sets coincide. Consequently
   \(m_0=m_1=m\). After fixing \((p,v,m)\), the number of ordered
   four-endpoint realizations in this stratum is at most

   $$
   4\binom{7}{2}=2\cdot7\cdot6=84.
   $$

2. If \(\kappa=1\), there are indices \(i\in\{0,1\}\) and
   \(j\in\{2,3\}\) with \(W_i=W_j\). Hence \(m_i=m\), while the other
   \(J\)-terminal \(m_{1-i}\) remains independent. After fixing
   \((p,v,m,m_{1-i})\), the number of ordered four-endpoint realizations
   with this specified shared-slot pair is at most

   $$
   7\cdot6\cdot7=294,
   $$

   and allowing the four choices of \((i,j)\) gives the uniform bound

   $$
   4\cdot7\cdot6\cdot7=1176.
   $$

3. If \(\kappa=0\), all four endpoints are distinct. After fixing the
   complete response tuple \((p,v,m_0,m_1,m)\), the number of ordered
   four-endpoint realizations is at most

   $$
   7^4=2401.
   $$

The corresponding response-coordinate projections are respectively

$$
\begin{array}{c|c}
\kappa & \text{response coordinates}\\ \hline
2 & (p,v,m),\\
1 & (p,v,m,m_{1-i}),\\
0 & (p,v,m_0,m_1,m).
\end{array}
$$

Thus the endpoint multiplicity is finite in every stratum; it cannot by
itself contribute an additional continuous response coordinate.

**Proof.** By Theorem 5.2 of the preceding continuation, every fixed
\((p,v,q)\) fibre

$$
\mathcal R(p,v,q)\sqcup\mathcal E(p,v,q)
$$

has at most seven worlds. If an exceptional layer is present, it has at
most two worlds and the ordinary layer at most five.

When \(\kappa=2\), two two-element sets with intersection of size two are
equal. Every world in the \(M\)-pair has terminal value \(m\), while every
world in the \(J\)-pair has its assigned terminal value \(m_0\) or \(m_1\).
Equality of the two sets therefore forces \(m_0=m_1=m\). Choose the two
distinct worlds from a fibre of size at most seven and order them for the
\(J\)-pair and \(M\)-pair independently. This gives
\(4\binom72=84\).

When \(\kappa=1\), choose the shared \(J\)-slot \(i\) and \(M\)-slot \(j\).
The shared world lies in the \(m\)-fibre, and the other \(M\)-slot must be a
different world in that fibre, giving at most \(7\cdot6\) choices. The
other \(J\)-slot lies in the fibre with terminal value \(m_{1-i}\), giving
at most seven choices. There are four choices for the pair \((i,j)\). If
\(m_{1-i}=m\), this product is only a uniform upper bound; the distinctness
conditions can reduce it further.

When \(\kappa=0\), each endpoint is chosen from one of the three fixed
terminal fibres, each of cardinality at most seven. Multiplying the four
bounds gives \(7^4\). The within-pair inequalities only reduce this count.

The coordinate statements are exactly the terminal equalities forced in
the first two cases and the independent choices allowed in the third.
The ordinary/exceptional refinement follows by replacing each factor seven
with the cardinality of its selected layer. \(\square\)

## 3. Ordinary/exceptional refinements

For \(q\in\mathbb R\), set

$$
c_O(p,v,q)=|\mathcal R(p,v,q)|,\qquad
c_E(p,v,q)=|\mathcal E(p,v,q)|.
$$

Theorem 5.2 gives

$$
c_E(p,v,q)\le2,
$$

and, whenever \(c_E(p,v,q)>0\),

$$
c_O(p,v,q)\le5;
$$

otherwise \(c_O(p,v,q)\le7\). For a fixed type vector
\(\tau=(\tau_0,\tau_1,\tau_2,\tau_3)\), the corresponding raw endpoint
count is bounded by

$$
\prod_{i=0}^{3}c_{\tau_i}(p,v,m_i),
\qquad m_2=m_3=m.
$$

In the \(\kappa=2\) stratum, equal endpoints also require equal type
labels. In the \(\kappa=1\) stratum, the shared pair has the same label,
and the remaining labels are unconstrained except by their own layer
membership. These are finite-count refinements of Proposition 2.1; they do
not assert that every \(O/E\) pattern occurs.

## 4. What this does and does not settle

The proposition supplies a faithful finite-fibre lift of the unresolved
four-endpoint relation. It separates the only three possible overlap
patterns and prevents the fixed-\((p,v,m)\) bound seven from being applied
to the independent \(m_0,m_1,m\) problem. It also identifies the precise
coordinate reduction available in the fully overlapping stratum: only
\((p,v,m)\) remains continuous there.

It does not construct a point of \(D_J\cap D_M\), prove that any overlap
stratum is nonempty, or prove a global absence theorem. It does not infer
that the number of response coordinates is a physical space dimension,
that a semialgebraic dimension equals the displayed coordinate count, or
that raw or complex lifts are strict-real witnesses. The remaining joint
question still ranges over ordinary/exceptional mixtures, repeated roots,
degree drops, zero drift, sampled gain zeros, and singular sources exactly
as in Definition 6.5 of the preceding continuation.

The result is a combinatorial reduction over the exact real inverse. Its
role is to turn a single unstructured search into three finite-fibre
strata; a subsequent exact or exclusion argument must still address the
actual equality of the \(J\)-responses and the independently chosen
\(M\)-pair.

## 追加锚（本行以下为增补区）

## 5. Equal-tail-ratio cubic J response incidence

### 5.1 Result and unchanged question

The original joint-existence question remains unresolved. This result supplies an exact cubic secant law for the part of the projected J-collision locus whose two endpoints have the same tail ratio. It also excludes an explicit response line from every two-world fixed-ratio fibre. These are statements about original strict complete worlds, not about unconstrained complex roots. The different-ratio J stratum remains part of the target.

The target is the existence of real $p\ne24,v$ and complete worlds $W_0,W_1,W_2,W_3$ in the **same entire** $C(p,v)$, with

$$
W_0\ne W_1,\quad a(W_0)=a(W_1),\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3).
\tag{5.1.1}
$$

The two pairs are independently chosen. Cross-pair overlap is allowed, and their common terminal values are unrelated. No joint witness or promising common-base candidate is claimed here. In particular the new fixed-ratio condition is a stratum of (5.1.1), not a replacement success criterion.

### 5.2 Original worlds and reused interfaces

An original world is

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad 0<r<1,\quad b>0,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

Each world has its own fixed real $d$, one entire polynomial $g$, and the literal actions $J,M,J,M,M,M$. At clocks zero through six its readings are
$(0,24,147/5,24,18,p,v)$. At clock seven J and M are alternatives on the same world. No reset, copy, new port, shared drift, or source-box substitution is used. Write

$$
j=b+r(1-r)/b,\quad n=j+r,\quad T_0=1+b,\quad U_0=1+2b.
$$

The original traces are
$(1,j,T_0,n,U_0,U_0+n,2U_0+n)$, and the terminal traces are
$T_0+2j+4r$ and $3U_0+2n$. Thus

$$
a=d+(T_0+2j+4r)g(7),\qquad
m=d+(3U_0+2n)g(7).
\tag{5.2.1}
$$

The following ordinary sources provide the cited interfaces and their stated limits.

| Source | Reused content and limit |
|---|---|
| `FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md`, Definitions 1.1–1.3 and Theorems 2.1–2.2, 12.3 | Original whole-world converse; on $p\ne24$, $d\ne24$; uniqueness at fixed source and p, including singular sources. |
| `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md`, Sections 1–6 and 9–11 | Original traces and the full guarded ordinary/exceptional fixed-terminal inverse. The entire $x=x_{\mathrm{exc}}$ layer is separated by p alone. No region of the response plane is imposed as a global restriction. |
| `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_XI.md`, Sections 1–4 | The lossless independent-pair relation and overlap strata. Neither pair's common value is identified with the other's. |
| `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VI.md`, Sections 16, 23, 28–29 | The printed local and entire-child statements only; they are not a global J-injectivity theorem and are not a hypothesis of the new law. |
| `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md`, Sections 1–2, 35–42 | Literal source maps, printed negative-J/source-class scope, and the exact exterior counterexample. No implication $v<2p$ is assumed. |

The parent lift, fixed-node interpolation, and uniqueness facts are reused. The mathematical assertions below are the positive drift quadratic, the response-line obstruction, the cubic secant identity (5.5.3) with its equal-response equivalence (5.5.4), and the exact projection (5.6.1). The reconstruction records the guards and converse explicitly. Polynomial interpolation and quadratic remainder algebra are classical tools; the interpolation reference already printed in the sources is Berrut–Trefethen, *SIAM Review* 46 (2004), Section 2.

### 5.3 A division-safe description over a fixed base

Fix real $p\ne24,v$, and put

$$
x=n/U_0>0,\qquad u=1/U_0\in(0,1),\qquad h=U_0g,
\qquad D=x(x+1)(x+2)>0.
$$

The entire polynomial $h$ is the unique cubic-or-lower interpolant with samples

$$
h(3)=(24-d)/x,\quad h(4)=18-d,\quad
h(5)=(p-d)/(x+1),\quad h(6)=(v-d)/(x+2).
\tag{5.3.1}
$$

Define $C_i=Dh(i)$ at $i=0,1,2,7$. Direct fixed-node evaluation gives

$$
\begin{aligned}
C_0={}&(45x^3+89x^2-32x-40)d+36x(x+2)p-10x(x+1)v\\
 &-810x^3-1950x^2-180x+960,\\
C_1={}&(20x^3+39x^2-16x-20)d+15x(x+2)p-4x(x+1)v\\
 &-360x^3-840x^2+480,\\
C_2={}&(6x^3+11x^2-7x-8)d+4x(x+2)p-x(x+1)v\\
 &-108x^3-228x^2+72x+192,\\
C_7={}&(-4x^3-9x^2+3x+2)d-6x(x+2)p+4x(x+1)v\\
 &+72x^3+192x^2+72x-48.
\end{aligned}
\tag{5.3.2}
$$

For clarity, all $C_i$, and the following symbols, are polynomials in $(x,d,p,v)$. Set

$$
\begin{aligned}
B_2&=C_2+(2d-294/5)D,\\
\Phi&=\frac52(C_0B_2-dDC_2)=f_2d^2+f_1d+f_0,\\
S&=C_0^2+C_2^2,\\
\Omega&=-dDC_0-C_2B_2,\\
R&=xC_1-(24-d)D,\\
\mathcal G&=(S-\Omega)\{2(24-d)DC_1S-(S-\Omega)C_1^2\}
          -4RS(\Omega C_1-RS).
\end{aligned}
\tag{5.3.3}
$$

Let $\mathcal H(p,v;x,d)$ mean all of

$$
\begin{gathered}
x>0,\quad d\ne24,\quad \Phi=0,\quad \mathcal G=0,\quad S>0,\\
0<\Omega<S,\qquad RC_1>0,\qquad
(\Omega C_1-RS)C_1>0.
\end{gathered}
\tag{5.3.4}
$$

The strict guards imply $C_1\ne0$. Reconstruction is

$$
u=\Omega/S,\qquad b=(1-u)/(2u),\qquad
r=R/(uC_1),\qquad g=uh,\qquad W=(P(r,b),g,d).
\tag{5.3.5}
$$

**Theorem 5.3.1 (Faithful guarded endpoints).** For the fixed off-24 base, (5.3.4)–(5.3.5) are in bijection with every original world in $C(p,v)$. In particular a fixed $(p,v,x,d)$ represents at most one whole world.

**Proof.** Clock zero and clock two are the two equations

$$
uC_0+dD=0,\qquad uC_2+B_2=0.
\tag{5.3.6}
$$

Their compatibility is $\Phi=0$. Their sum-of-squares solution is (5.3.5), since

$$
uC_0+dD=-\frac{C_2}{S}(C_0B_2-dDC_2),\qquad
uC_2+B_2=\frac{C_0}{S}(C_0B_2-dDC_2).
\tag{5.3.7}
$$

For an original world $S>0$: otherwise clock zero gives $d=0$ and clock two gives $d=147/5$. Since $p\ne24$, the reused parent saturation gives $d\ne24$, and clock one gives $C_1\ne0$. Clock one and $n=x/u$ yield

$$
j=(24-d)D/(uC_1),\qquad r=x/u-j=R/(uC_1).
$$

The source identity $bj=b^2+r(1-r)$ has precisely the cleared form

$$
4\Omega^2C_1^2\{bj-b^2-r(1-r)\}=\mathcal G.
\tag{5.3.9}
$$

Every original world therefore satisfies (5.3.4).

Conversely the guards imply $b>0$ and $0<r<1$. Equation (5.3.9) gives the original $j=b+r(1-r)/b$, and then $n=j+r=x/u$, $U_0=1/u$, $T_0=(1+u)/(2u)$. Equations (5.3.7) give clocks zero and two; the definition of j gives clock one. The four samples (5.3.1) give clocks three through six. Thus all seven original acquired rows use the same degree-at-most-three polynomial $g=uh$ and fixed d. The gain cannot be identically zero because the first two readings differ. Every reconstructed parameter is unique. This proves the converse and the bijection. ∎

There is no division by drift, $C_0$, $C_2$, $g(7)$, a leading gain coefficient, a root separation, the regular-parent coefficient $\Lambda$, or X's quartic K. Hence this description includes zero drift, vanishing gain samples, degree drops, repeated roots, singular sources, the golden layer, and the exceptional $x=x_{\mathrm{exc}}$ layer. A single vanishing $C_0$ or $C_2$ is retained. Their simultaneous vanishing is impossible for an original endpoint, rather than discarded by a chart convention.

### 5.4 A positive quadratic and an excluded response line

The leading coefficient in (5.3.3) is independent of the responses. To distinguish the positive drift polynomial from the source matrix $P(r,b)$, write it as $\Pi(x)$:

$$
f_2=5\Pi(x),\qquad
\Pi(x)=177x^6+724x^5+542x^4-742x^3-629x^2+196x+160.
\tag{5.4.1}
$$

**Theorem 5.4.1 (Positivity of the drift coefficient).** $\Pi(x)>0$ for every $x\ge0$.

**Proof.** On the four successive intervals in the following table, the entries are the seven degree-six Bernstein coefficients after the affine substitution $x=a+(b-a)y$, $0\le y\le1$. Every entry is positive. Bernstein basis functions are nonnegative and sum to one, proving positivity on each interval.

| $[a,b]$ | Bernstein coefficients, in increasing index |
|---|---|
| $[0,1/2]$ | $160,529/3,10931/60,13833/80,17537/120,5065/48,4305/64$ |
| $[1/2,5/8]$ | $4305/64,44315/768,741671/15360,804273/20480,7608751/245760,4661699/196608,4703705/262144$ |
| $[5/8,3/4]$ | $4703705/262144,4787717/393216,2585533/327680,180471/32768,451389/81920,207685/24576,61273/4096$ |
| $[3/4,1]$ | $61273/4096,85943/3072,70739/1280,65193/640,3481/20,3355/12,428$ |

For $x=1+y$, $y\ge0$, the polynomial is

$$
177y^6+1786y^5+6817y^4+12206y^3+10292y^2+3562y+428>0.
$$

This covers the remaining interval. ∎

Consequently every fixed $(p,v,x)$ admits at most two original worlds, counted as distinct worlds rather than multiplicities. Define

$$
\delta=f_1^2-4f_0f_2,\qquad
d_\pm=\frac{-f_1\pm\sqrt\delta}{2f_2}
\quad(\delta>0).
\tag{5.4.3}
$$

Two distinct worlds with the same $(p,v,x)$ must have these two different drifts. A double root $\delta=0$ represents at most one whole world. The leading coefficient has no positive denominator-zero stratum.

Define the response line

$$
L=(36x^2+4x-128)p+(-15x^2+9x+20)v
       -738x^2-1050x+1872.
\tag{5.4.4}
$$

We also need the explicit quadratic-in-responses polynomial

$$
\begin{aligned}
B={}&(41650 x^{4} + 119000 x^{3} - 3750 x^{2} - 124800 x + 51200)p^{2}\\ &+(- 26600 x^{4} - 47700 x^{3} + 28300 x^{2} + 29100 x - 16000)pv\\ &+(476910 x^{5} + 446070 x^{4} - 3364050 x^{3} - 2076690 x^{2} + 4533120 x - 1305600)p\\ &+(4250 x^{4} + 3100 x^{3} - 3850 x^{2} - 1500 x + 1250)v^{2}\\ &+(- 159210 x^{5} + 2910 x^{4} + 914280 x^{3} - 136530 x^{2} - 577170 x + 204000)v\\ &+(5434857 x^{6} + 14774994 x^{5} - 4247514 x^{4} - 5389542 x^{3} + 22161789 x^{2} - 32267016 x + 11744928).
\end{aligned}
\tag{5.4.5}
$$

**Theorem 5.4.2 (Paired-endpoint restriction).** Suppose the two real roots in (5.4.3) both reconstruct original worlds. Write $S_\pm=S(x,d_\pm,p,v)$. Then

$$
S_+S_-=\frac{2D^4 L^2 B}{25\Pi^2}>0.
\tag{5.4.6}
$$

In particular $L\ne0$ and $B>0$. The whole line $L=0$ is excluded from two-world fixed-$(p,v,x)$ incidence, for every $x>0$. This is not an assertion that the line contains no single original endpoint.

**Proof.** Write $S=s_2d^2+s_1d+s_0$. Its remainder modulo $\Phi$ is

$$
S\equiv(\alpha d+\beta)/f_2,\quad
\alpha=s_1f_2-s_2f_1,\quad \beta=s_0f_2-s_2f_0.
$$

Vieta's identities give

$$
f_2^3S_+S_-=\alpha^2 f_0-\alpha\beta f_1+\beta^2f_2
               =10D^4\Pi L^2B.
\tag{5.4.8}
$$

The last polynomial identity follows by substitution of (5.3.2)–(5.3.3); (5.4.5) gives all its coefficients. Substitution of $f_2=5\Pi$ proves (5.4.6). The original guards give $S_\pm>0$, so L cannot vanish and B must be positive. ∎

The discriminant and (5.4.6) are restrictions on the two endpoints at the **same base**. They do not compare separately optimal sources or infer joint attainability from unrelated marginal data.

### 5.5 The cubic secant law

The actual terminal responses, without any gain-sample division, are

$$
\begin{aligned}
m(x,d)&=d+(2x+3)C_7/D,\\
a(x,d)&=\frac{N_J}{Q_J},\\
N_J&=2dDSC_1+C_7\{((1+8x)S+\Omega)C_1-4(24-d)DS\},\\
Q_J&=2DSC_1.
\end{aligned}
\tag{5.5.1}
$$

Indeed $a=d+\{(1+u)/2+4x-2(24-d)D/C_1\}h(7)$, the trace formula (5.2.1). Equation (5.5.1) is valid when $d=0$, $g(7)=0$, or $C_0=0$, since the only divisions use the established strict guards.

Define

$$
\mathcal T(x;p,v)=\sum_{i+j\le3} t_{ij}(x)p^iv^j,
\tag{5.5.2}
$$

with coefficients given in Section 5.7. This is a nonzero polynomial of bidegree $(11,3)$ in $(x,(p,v))$.

**Theorem 5.5.1 (Exact equal-ratio J secant).** Suppose two different original worlds have the same off-24 $(p,v,x)$. Use the drift ordering $d_+>d_-$, and write $a_\pm=a(x,d_\pm)$, $C_{1,\pm}=C_1(x,d_\pm,p,v)$. Then

$$
\boxed{
\frac{a_+-a_-}{d_+-d_-}
   =\frac{D\,\mathcal T(x;p,v)}{5\Pi L C_{1,+}C_{1,-}}.
}
\tag{5.5.3}
$$

All denominator factors are nonzero consequences of two original endpoints. In particular

$$
a_+=a_-\quad\Longleftrightarrow\quad \mathcal T(x;p,v)=0.
\tag{5.5.4}
$$

**Proof.** The two entire gains and all source traces are already fixed by (5.3.1)–(5.3.5). In particular (5.5.1) is their actual J response, not a refitted seventh gain.

The following finite quadratic reduction proves the secant identity. Let $\rho_i,\sigma_i$ be the entries in this table:

| i | $\rho_i$ | $\sigma_i$ |
|---|---|---|
| 0 | $f_2^3$ | 0 |
| 1 | 0 | $f_2^3$ |
| 2 | $-f_0f_2^2$ | $-f_1f_2^2$ |
| 3 | $f_0f_1f_2$ | $(f_1^2-f_0f_2)f_2$ |
| 4 | $f_0^2f_2-f_0f_1^2$ | $-f_1^3+2f_0f_1f_2$ |

Thus $f_2^3d^i\equiv\rho_i+\sigma_i d\pmod\Phi$. Write $N_J=\sum_{i=0}^4 n_id^i$, $Q_J=\sum_{i=0}^3 q_id^i$, and set

$$
A_N=\sum n_i\sigma_i,\quad B_N=\sum n_i\rho_i,\quad
A_Q=\sum q_i\sigma_i,\quad B_Q=\sum q_i\rho_i.
$$

Direct polynomial expansion using (5.3.2), (5.3.3), and the coefficient list in Section 5.7 gives

$$
A_NB_Q-B_NA_Q=1000D^7\Pi^3 L B\mathcal T.
\tag{5.5.6}
$$

This identity, together with (5.4.8), is also a short determinant definition of the cubic. No source equation or numerical fit is used in these two polynomial identities.

For either drift root,
$a=(A_Nd+B_N)/(A_Qd+B_Q)$ and
$A_Qd+B_Q=f_2^3Q_J\ne0$. Subtract the two fractions. Their denominator product is

$$
f_2^6 Q_J(d_+)Q_J(d_-)
=4D^2f_2^6S_+S_-C_{1,+}C_{1,-}.
$$

Insert (5.4.6), (5.5.6), and $f_2=5\Pi$. Cancellation gives (5.5.3). Theorems 5.4.1–5.4.2 and the guards give the asserted nonzero factors, so the equivalence (5.5.4) follows. ∎

This is a relation between two independently realized whole endpoints over one base. It eliminates both unknown drifts from their J equality and reduces that equality to a cubic in the response-plane coordinates. The factor L is proved nonzero on a legal two-endpoint fibre; it is not silently discarded. Formula (5.4.6) is what makes that cancellation legitimate even if one endpoint has zero drift or a zero clock-zero gain sample.

For comparison, the same two roots satisfy

$$
m(x,d_+)-m(x,d_-)=-\frac{K(x)}D(d_+-d_-),\qquad
K=8x^4+29x^3+18x^2-15x-6.
\tag{5.5.8}
$$

This is the fixed-terminal drift identity in `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md`, in the present normalization. Thus a distinct equal-M pair at equal x would require $x=x_{\mathrm{exc}}$, the unique positive root of K. the p-only separation in `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md` on that entire layer excludes it. The cited identity has this scope only; it does not assert a global M obstruction. Every selected M pair in (5.1.1) therefore has unequal x; the selected J pair need not.

### 5.6 Exact use in the common-base incidence problem

Let $D_J^=$ be the projection of distinct equal-J pairs with equal $x$, and let $D_J^{\ne}$ be the projection of the remaining distinct equal-J pairs.

**Theorem 5.6.1 (Exact equal-x J projection).** The equal-x J-collision projection is exactly

$$
\boxed{
(p,v)\in D_J^=
\iff
p\ne24\ \land\ \exists x>0:\quad
\delta>0,\quad
\mathcal H(p,v;x,d_+),\quad\mathcal H(p,v;x,d_-),\quad
\mathcal T(x;p,v)=0.
}
\tag{5.6.1}
$$

**Proof.** A pair supplies two different drift roots by Theorems 5.3.1 and 5.4.1, so it supplies the right-hand side by Theorem 5.5.1. Conversely, the two guarded roots reconstruct two original complete worlds with different drifts, hence different worlds, in the same entire $C(p,v)$. Theorem 5.5.1 gives their actual J equality. ∎

Necessary response-plane filters in this description are

$$
\delta>0,\qquad L\ne0,\qquad B>0,\qquad \mathcal T=0.
\tag{5.6.2}
$$

They are **not sufficient** without both $\mathcal G=0$ equations and all the strict guards in (5.3.4). In particular the cubic's real zeros are not automatically original-source points. Equation (5.6.1), rather than the naked cubic, is the incidence relation.

For the independently chosen M pair, use exactly X's full inverse $\mathcal R(p,v,m)\sqcup\mathcal E(p,v,m)$, its strict guards, and two distinct reconstructed worlds. Its common $m$ is independent of the J value computed from (5.5.1).

**Theorem 5.6.2 (Independent M-pair decomposition).** The original target is equivalent to nonemptiness of

$$
(D_J^=\cap D_M)\cup(D_J^{\ne}\cap D_M).
\tag{5.6.3}
$$

**Proof.** The two distinct J endpoints either have equal $x$ or they do not, so their projection lies in exactly one of $D_J^=$ and $D_J^{\ne}$. The independently chosen distinct M pair lies in $D_M$ by the full inverse in `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md`; the overlap strata and unrelated terminal values are those of `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_XI.md`. Conversely, a point in either intersection supplies the two J endpoints and the two M endpoints in the same entire $C(p,v)$ with the required within-pair inequalities. ∎

The first term now has the explicit cubic law (5.6.1), with no J endpoint source or drift left free once $(p,v,x)$ is fixed. X supplies the M endpoints at the same $p$ and $v$. Cross-pair overlap is not prohibited. The second term remains fully present: it requires two independent $x$ values for the J endpoints and is not excluded by the cubic law. The four-endpoint meaning and overlap alternatives remain those of XI.

The resulting relation is a projected collision relation and a real guard that can be intersected with the projected M relation in the **same** response plane. It is not an assertion that either intersection is nonempty and not a substitution of equal-ratio J endpoints for the original goal.

### 5.7 Explicit cubic coefficients

The following ten polynomials completely specify (5.5.2). Missing monomials are zero.

$$
t_{30}(x)=2808000 x^{10} + 12032550 x^{9} - 8036130 x^{8} - 81627240 x^{7} - 19436220 x^{6} + 197265810 x^{5} + 90269790 x^{4} - 151448280 x^{3} - 40894560 x^{2} + 25641600 x + 9600000.
\tag{5.7.1}
$$

$$
t_{21}(x)=- 3243600 x^{10} - 11144175 x^{9} + 14386350 x^{8} + 67537175 x^{7} - 21617480 x^{6} - 153381225 x^{5} - 16527750 x^{4} + 99842505 x^{3} + 21741480 x^{2} - 18188240 x - 6640000.
\tag{5.7.2}
$$

$$
t_{20}(x)=24364800 x^{11} - 18929160 x^{10} - 727607034 x^{9} - 871800576 x^{8} + 3588186492 x^{7} + 5030385972 x^{6} - 6453464670 x^{5} - 7274390832 x^{4} + 5396100048 x^{3} + 2257963872 x^{2} - 828604800 x - 384000000.
\tag{5.7.3}
$$

$$
t_{12}(x)=1232640 x^{10} + 3275880 x^{9} - 6356470 x^{8} - 16830230 x^{7} + 13365090 x^{6} + 33564990 x^{5} - 2959380 x^{4} - 20987880 x^{3} - 3564260 x^{2} + 4043000 x + 1380000.
\tag{5.7.4}
$$

$$
t_{11}(x)=- 21211200 x^{11} + 17378460 x^{10} + 484331529 x^{9} + 250870395 x^{8} - 2423507022 x^{7} - 1592766582 x^{6} + 4159619613 x^{5} + 2013019095 x^{4} - 2444669904 x^{3} - 881063412 x^{2} + 391579440 x + 179040000.
\tag{5.7.5}
$$

$$
t_{10}(x)=- 873763200 x^{11} - 2995991280 x^{10} + 9383853852 x^{9} + 37359844740 x^{8} - 21204116568 x^{7} - 119429717796 x^{6} + 35957993004 x^{5} + 143493280776 x^{4} - 57451980816 x^{3} - 36959578848 x^{2} + 8311633920 x + 5074560000.
\tag{5.7.6}
$$

$$
t_{03}(x)=- 153600 x^{10} - 298240 x^{9} + 799280 x^{8} + 1206755 x^{7} - 1500050 x^{6} - 2270270 x^{5} + 549270 x^{4} + 1429015 x^{3} + 174600 x^{2} - 286500 x - 90000.
\tag{5.7.7}
$$

$$
t_{02}(x)=4608000 x^{11} - 3520320 x^{10} - 77586180 x^{9} + 3373761 x^{8} + 346381680 x^{7} + 51372210 x^{6} - 498447858 x^{5} - 120714123 x^{4} + 261654486 x^{3} + 80240460 x^{2} - 43765800 x - 18540000.
\tag{5.7.8}
$$

$$
t_{01}(x)=382665600 x^{11} + 1073911320 x^{10} - 3760055442 x^{9} - 10203888420 x^{8} + 12447102348 x^{7} + 27395087976 x^{6} - 21480462054 x^{5} - 23751521136 x^{4} + 13344031296 x^{3} + 7536384288 x^{2} - 1929561120 x - 1194480000.
\tag{5.7.9}
$$

$$
t_{00}(x)=7672838400 x^{11} + 44059351680 x^{10} + 15441446880 x^{9} - 254456026560 x^{8} - 166995837000 x^{7} + 659763985320 x^{6} + 200943791280 x^{5} - 817817290560 x^{4} + 169938622080 x^{3} + 187929866880 x^{2} - 24694951680 x - 22187520000.
\tag{5.7.10}
$$


### 5.8 Remaining boundary

A finite set of tested points does not prove global absence. The remaining mathematical boundary is the disjunction: a point of $D_J^=\cap D_M$ satisfying (5.6.1) and all of the M guards in `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md` exists, or a point of $D_J^{\ne}\cap D_M$ exists. Any proof of either clause must retain the simultaneous equations for all four original whole worlds, their strict guards, and within-pair distinctness. A global exclusion must cover both terms of (5.6.3), every ordinary and exceptional layer, every singular source, and every allowed gain and drift stratum. All values of $v$ permitted by the acquisition model remain in scope, and distinct worlds may have distinct drifts.

## 追加锚（本行以下为增补区）
