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

**Proof.** The two distinct J endpoints either have equal $x$ or they do not, so their projection lies in at least one of $D_J^=$ and $D_J^{\ne}$. The independently chosen distinct M pair lies in $D_M$ by the full inverse in `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md`; the overlap strata and unrelated terminal values are those of `FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_XI.md`. Conversely, a point in either intersection supplies the two J endpoints and the two M endpoints in the same entire $C(p,v)$ with the required within-pair inequalities. ∎

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

## 6. A second-source unequal-ratio J opening and a strict finite pair

### 6.1 Original worlds and the full incidence relation

**Definition 6.1.1 (Original domain and independent pairs).** Retain the complete worlds and the entire child of Section 5.2 and [common-parent geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3. Thus

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad 0<r<1,\quad b>0,\quad d\in\mathbb R,
\quad 0\ne g\in\mathbb R[s],\quad\deg g\le3.
\tag{6.1.1}
$$

The actions, left products and readings are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
Q_0=I,\quad Q_i=E_iQ_{i-1},\qquad
y_i=d+g(i)\operatorname{tr}(Q_iP).
\tag{6.1.2}
$$

The acquired word is literally $J,M,J,M,M,M$, with

$$
(y_0,\ldots,y_6)=(0,24,147/5,24,18,p,v),\qquad p\ne24.
\tag{6.1.3}
$$

Each world uses its own fixed real drift and its one entire gain polynomial at every clock. At clock seven, J and M are alternatives on that same world. There is no reset, copy, shifted clock, additional port, shared drift, or replacement of the entire child by a source box. Put

$$
j=b+r(1-r)/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,
\quad x=n/U.
\tag{6.1.4}
$$

The acquired traces are $(1,j,T,n,U,U+n,2U+n)$, and the actual terminal readings are

$$
a(W)=d+(T+2j+4r)g(7),\qquad
m(W)=d+(3U+2n)g(7).
\tag{6.1.5}
$$

For the entire original child $C(p,v)$ define

$$
\begin{aligned}
D_J&=\{(p,v):p\ne24,\ \exists W_0\ne W_1\in C(p,v),\ a(W_0)=a(W_1)\},\\
D_M&=\{(p,v):p\ne24,\ \exists W_2\ne W_3\in C(p,v),\ m(W_2)=m(W_3)\}.
\end{aligned}
\tag{6.1.6}
$$

The remaining independent-pair problem is $D_J\cap D_M\ne\varnothing$. Its pairs may overlap or be disjoint, and their common terminal answers are unrelated. In particular $m(W_0)$ and $m(W_1)$ are independent auxiliary values. The full relation is that of [Support X](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md), Definition 6.3 and Proposition 6.4, with the overlap strata of Proposition 2.1 above.

**Definition 6.1.2 (Undivided parent).** The parent used in the full problem is the zero-safe parent of common-parent geometry, Theorem 2.1. In the present normalization it is

$$
e=d-24,\qquad
\Lambda=1+6/T+1/U-4/j-4/n,\qquad
e\Lambda+\frac{24}{5}(b-1/8)\left(\frac6T-\frac2U\right)=0.
\tag{6.1.7}
$$

Its one whole gain is the unique cubic-or-lower interpolant at $0,1,2,3$ with samples

$$
\bigl(g(0),g(1),g(2),g(3)\bigr)
=\bigl(-24-e,-e/j,(27/5-e)/T,-e/n\bigr).
\tag{6.1.8}
$$

There is no global condition $\Lambda\ne0$. Singular sources, zero drift, sampled gain zeros, repeated gain roots and degree drops remain in (6.1.6).

### 6.2 The attributed regular source circuit

**Definition 6.2.1 (Whole-world regular lift).** Use the regular circuit of [Support VI](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VI.md), Lemma 2.2, in the original coordinates $z=(r,b)$, equivalently [Support IX](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md), equations (18.4)–(18.8). Define

$$
\begin{aligned}
D&=5\{(b^2+8b+4)jn-2TU(j+n)\},&
S&=(8b-1)(2+5b),\\
C_0&=-24D+3Sjn,&C_1&=3Sn,\\
C_2&=3(49b+34)jn-54U(j+n),&C_3&=3Sj,\\
B_5&=-4C_0+15C_1-20C_2+10C_3,\\
B_6&=-10C_0+36C_1-45C_2+20C_3,\\
B_7&=-20C_0+70C_1-84C_2+35C_3.
\end{aligned}
\tag{6.2.1}
$$

On the strict source domain with $D\ne0$, the reused lift is

$$
\begin{aligned}
d(z)&=-C_0/D,\\
g_z(s)&=\frac1D\sum_{i=0}^3C_i
 \prod_{\substack{0\le l\le3\\l\ne i}}\frac{s-l}{i-l},\\
p(z)&=\frac{-C_0+(U+n)B_5}{D},&
v(z)&=\frac{-C_0+(2U+n)B_6}{D},\\
a(z)&=\frac{-C_0+(T+2j+4r)B_7}{D},&
m(z)&=\frac{-C_0+(3U+2n)B_7}{D},\\
W(z)&=(P(r,b),g_z,d(z)),&F(z)&=(p(z),v(z),a(z)).
\end{aligned}
\tag{6.2.2}
$$

The correspondence in this definition is the attributed parent converse, with $D=(5/2)TUjn\Lambda$. To spell out its original-clock content, put $C_4=-C_0+4C_1-6C_2+4C_3$. Substitution in (6.2.1) gives

$$
\begin{gathered}
-C_0+C_0=0,\qquad -C_0+jC_1=24D,\\
-C_0+TC_2=(147/5)D,\qquad -C_0+nC_3=24D,\\
-C_0+UC_4=18D,\qquad Dg_z(i)=B_i\quad(i=5,6,7).
\end{gathered}
\tag{6.2.3}
$$

These identities give all seven acquired readings and both terminal alternatives using the traces in (6.1.4)–(6.1.5). The fixed-node evaluation rows at $5,6,7$ are respectively $(-4,15,-20,10)$, $(-10,36,-45,20)$ and $(-20,70,-84,35)$; hence the three $B_i$ are evaluations of the same interpolant. Its gain is nonzero because an identically zero gain would make the first two readings equal to the same drift. Conversely the first four readings fix the whole interpolant, and the fifth original row is exactly (6.1.7). This is the parameter correspondence of the cited parent and circuit, rather than an additional generic reconstruction result. Distinct-node interpolation is the classical formula of Berrut–Trefethen, *Barycentric Lagrange Interpolation*, Section 2, equations (2.1)–(2.4), [doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).

### 6.3 The exact second critical source

**Definition 6.3.1 (Critical polynomials and rational box).** Put

$$
\mathcal J=b^2+r-r^2,\qquad \mathcal N=\mathcal J+br,\qquad
\widehat D=5\{(b^2+8b+4)\mathcal J\mathcal N-2bTU(\mathcal J+\mathcal N)\}.
\tag{6.3.1}
$$

Thus $j=\mathcal J/b$, $n=\mathcal N/b$, $\widehat D=b^2D$. Let $\widehat C_i=b^2C_i$ and $\widehat B_i=b^2B_i$, using (6.2.1), so all hatted expressions are polynomials. Define

$$
\begin{aligned}
Q&=b\widehat D,\\
P_p&=-b\widehat C_0+(bU+\mathcal N)\widehat B_5,\\
P_v&=-b\widehat C_0+(2bU+\mathcal N)\widehat B_6,\\
P_a&=-b\widehat C_0+(bT+2\mathcal J+4br)\widehat B_7.
\end{aligned}
\tag{6.3.2}
$$

Then $(p,v,a)=(P_p,P_v,P_a)/Q$. For polynomials $P,R$ set

$$
\mathcal H(P,R)=(P_rR_b-P_bR_r)Q
 +(P_bR-PR_b)Q_r+(PR_r-P_rR)Q_b.
\tag{6.3.3}
$$

Define the integer polynomials $E_1,E_2$ by the exact polynomial quotients

$$
\mathcal H(P_p,P_v)=-45bE_1,\qquad
\mathcal H(P_p,P_a)=-45bE_2.
\tag{6.3.4}
$$

Each has $r$-degree $15$, $b$-degree $17$ and $134$ nonzero terms. Equations (6.2.1) and (6.3.1)–(6.3.4) specify every coefficient, without choosing roots of an eliminated univariate polynomial. Set

$$
\begin{aligned}
\bar r&=0.8995316741215982684097269764207819803504111050038539630302674411010601,\\
\bar b&=0.1285667303082647572172438018797839441494924309943980919070932795322297,\\
c_*&=(\bar r,\bar b),\qquad \rho_*=10^{-35},\qquad
X_*=c_*+[-\rho_*,\rho_*]^2.
\end{aligned}
\tag{6.3.5}
$$

All terminating decimals in Section 6 denote exact rationals.

**Theorem 6.3.2 (Isolated strict rank-one source).** There is exactly one zero $z_*=(r_*,b_*)$ of $(E_1,E_2)$ in $X_*$. The following bounds are strict at that zero:

| Quantity | Lower bound | Upper bound |
|---|---:|---:|
| $D(z_*)$ | $-0.047846390145$ | $-0.047846390144$ |
| $p_*=p(z_*)$ | $-10.890381011470$ | $-10.890381011469$ |
| $v_*=v(z_*)$ | $-8.153583918938$ | $-8.153583918937$ |
| $p_b(z_*)$ | $132006.077494$ | $132006.077495$ |
| $k_*=-p_r(z_*)/p_b(z_*)$ | $-1.218947510$ | $-1.218947509$ |

The source is strict and regular, $p_*\ne24$, and $DF(z_*)$ has rank exactly one. This source is distinct from the first J-critical source of Support IX, Definition 19.1, whose coordinates lie near $(0.0474992,0.0463261)$.

Proof. The first rational inclusion of Theorem 6.4.2 gives existence and uniqueness in $X_*$. Direct differentiation gives the exact identity

$$
\det D(P/Q,R/Q)=\frac{\mathcal H(P,R)}{Q^3}.
\tag{6.3.6}
$$

Indeed, expanding the determinant of the two quotient-rule gradients first gives a numerator with denominator $Q^4$; its terms with two derivatives of $Q$ cancel, leaving $Q\mathcal H(P,R)$. On $X_*$, $b>0$ and the displayed D bound excludes zero, so $Q=b^3D\ne0$. Equations (6.3.4) and (6.3.6) give $\det D(p,v)=\det D(p,a)=0$ at $z_*$. The rational endpoint evaluations prescribed in Section 6.4 give the table, including $p_b\ne0$. Thus the $p$ row is nonzero and both other rows are its scalar multiples: the rank is one, and

$$
F_r(z_*)+k_*F_b(z_*)=0.
\tag{6.3.7}
$$

The source box gives $0<r_*<1,b_*>0$; the D bound gives regularity and the p bound gives $p_*\ne24$. The two disjoint source enclosures distinguish this zero from the cited first source. The regular lift (6.2.2) supplies its original whole world. ∎

### 6.4 Exact rational inclusions and derivative enclosures

**Definition 6.4.1 (The two inclusion prescriptions).** For the critical inclusion use

$$
G_*=(E_1,E_2),\qquad c=c_*,\quad \rho=\rho_*,\quad X=X_*,
\qquad C_*=DG_*(c_*)^{-1}.
\tag{6.4.1}
$$

In particular the exact rational preconditioner is specified by

$$
C_*=
\left.
\frac1{E_{1,r}E_{2,b}-E_{1,b}E_{2,r}}
\begin{pmatrix}E_{2,b}&-E_{1,b}\\-E_{2,r}&E_{1,r}\end{pmatrix}
\right|_{c_*}.
\tag{6.4.2}
$$

The denominator here is a nonzero rational obtained from (6.3.1)–(6.3.5). For the finite inclusion use $h_0=1/1000$ and

$$
S_F(R,B,k,h)=\frac{F(R+h,B+kh)-F(R-h,B-kh)}{2h}
\quad(h\ne0),
\tag{6.4.3}
$$

with

$$
G_0=S_F(\,\cdot\,,h_0),\qquad c=c_0,\quad\rho=\rho_0=10^{-30},
\quad X=X_0=c_0+[-\rho_0,\rho_0]^3,\qquad C=C_0^{\mathrm{pre}}.
\tag{6.4.4}
$$

The centre $c_0$ and the rational matrix $C_0^{\mathrm{pre}}$ are given in Definition 6.7.1. For either of these two prescriptions define the interval matrix and the centred inclusion image

$$
\begin{aligned}
\mathcal B&=I-C\,DG(X),\qquad \eta=\|CG(c)\|_\infty,\\
\mathscr K-c&=-CG(c)+\mathcal B[-\rho,\rho]^n.
\end{aligned}
\tag{6.4.5}
$$

For an interval matrix, $\|\mathcal B\|_\infty$ means the maximum row sum of the largest absolute endpoints of its entries.

All interval endpoints and arithmetic in these prescriptions are rational. For intervals $I=[a,b]$, $J=[c,d]$ use

$$
\begin{aligned}
I+J&=[a+c,b+d],& I-J&=[a-d,b-c],\\
IJ&=[\min(ac,ad,bc,bd),\max(ac,ad,bc,bd)],&
I^{-1}&=[1/b,1/a]\quad(0\notin I).
\end{aligned}
\tag{6.4.6}
$$

Powers are repeated interval multiplications. Expand $E_i$ as specified in (6.3.4), differentiate its monomials, and evaluate the resulting polynomials termwise. For $G_0$ use the rational circuit (6.2.1)–(6.2.2). Its derivative columns in the order $(R,B,k)$ are exactly

$$
\frac{F_r(z_+)-F_r(z_-)}{2h_0},\qquad
\frac{F_b(z_+)-F_b(z_-)}{2h_0},\qquad
\frac{F_b(z_+)+F_b(z_-)}2,
\quad z_\pm=(R\pm h_0,B\pm kh_0).
\tag{6.4.7}
$$

For source derivatives through order three evaluate the same circuit as a truncated jet with interval coefficients, substituting $r=X_r+\xi$, $b=X_b+\zeta$ and discarding all monomials of total degree at least four. The underlying exact-point algebra is

$$
\mathbb Q[\xi,\zeta]/(\xi,\zeta)^4.
\tag{6.4.8}
$$

For a jet $c+u$, with zero constant term in $u$ and $0\notin c$, its inverse is evaluated as

$$
(c+u)^{-1}=c^{-1}\{1-u/c+(u/c)^2-(u/c)^3\}
\pmod{(\xi,\zeta)^4}.
\tag{6.4.9}
$$

The coefficient of $\xi^i\zeta^j$, multiplied by $i!j!$, encloses $\partial_r^i\partial_b^j f$ throughout the box for $i+j\le3$. This follows by the truncated Taylor identity at every point of the box and the inclusion property of (6.4.6). All inversions first exclude zero: the source bounds exclude $b=0$, the D bounds exclude $D=0$, and the $p_b$ and determinant bounds used below exclude their respective denominators. Matrix inversion for the coefficients below uses the adjugate divided by the determinant. The construction is the classical rational interval/Newton contraction applied to these two stated systems; compare R. Krawczyk, *Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken*, Computing 4 (1969), 187–201, [doi:10.1007/BF02234767](https://doi.org/10.1007/BF02234767).

**Theorem 6.4.2 (The two strict box inclusions).** With the exact prescriptions of Definition 6.4.1, the critical system satisfies

$$
\|\mathcal B_*\|_\infty<10^{-18},\qquad
\eta_*/\rho_*+\|\mathcal B_*\|_\infty<10^{-18},
\tag{6.4.10}
$$

and the finite system satisfies

$$
\|\mathcal B_0\|_\infty<6\cdot10^{-18},\qquad
\eta_0/\rho_0+\|\mathcal B_0\|_\infty<6\cdot10^{-18}.
\tag{6.4.11}
$$

Each system has a unique zero in its stated closed box. Neither assertion is a uniqueness statement outside that box.

Proof. The source-box substitutions in the rational prescription first give positive b intervals and

$$
\begin{aligned}
D(X_*)&\subset(-0.047846390145,-0.047846390144),\\
D(z_+(X_0))&\subset(-0.031581090465,-0.031581090464),\\
D(z_-(X_0))&\subset(-0.064012570271,-0.064012570270).
\end{aligned}
\tag{6.4.12}
$$

Here $z_\pm(X_0)$ are the affine endpoint boxes of (6.4.7). These are box evaluations before any zero is selected, so every rational source division used in the two inclusions is defined. For (6.4.10), substitute the exact centre (6.3.5) into (6.3.1)–(6.3.4), use (6.4.2) at the centre, and use the monomial derivative evaluation of (6.4.6) on $X_*$. Form $I-C_*DG_*(X_*)$ and its maximum absolute row sums as in (6.4.5). The rational endpoint comparisons are exactly the two strict inequalities (6.4.10). For (6.4.11), substitute the exact centre and rational matrix of Definition 6.7.1 into (6.4.3)–(6.4.5). Evaluate the source circuit at both affine endpoint boxes and use the three derivative columns (6.4.7). The same rational endpoint rules give (6.4.11). These operations specify both centre evaluations, both derivative enclosures, both preconditioners and the two scalar comparisons without an approximate root being used in place of an exact centre.

For completeness, the contraction implication in these applications is direct. Let $T_G(z)=z-CG(z)$ on its box. The mean-value formula along a line segment in the box and the enclosure $DG(X)$ imply

$$
\|T_G(z)-T_G(w)\|_\infty
\le\|\mathcal B\|_\infty\|z-w\|_\infty,
\qquad
T_G(X)-c\subseteq\mathscr K-c.
\tag{6.4.13}
$$

Consequently

$$
\|T_G(z)-c\|_\infty
\le\eta+\rho\|\mathcal B\|_\infty<\rho.
\tag{6.4.14}
$$

Thus $T_G$ maps the closed box strictly into itself and has contraction constant less than one. Iteration is Cauchy in this complete box and yields its unique fixed point. Also $\|I-CDG(c)\|_\infty<1$, so $CDG(c)$ is invertible by the convergent Neumann series; since the matrices are square, $C$ is invertible. The fixed-point equation is therefore equivalent to $G=0$. Every zero in the box is a fixed point, proving the claimed uniqueness there. This is the classical contraction argument used as an intermediate tool for the two systems, with the strict margins (6.4.10)–(6.4.11). ∎

### 6.5 Third-order coefficients at the second source

**Definition 6.5.1 (Fixed-direction jets).** All derivatives here are in the original independent coordinates $(r,b)$ at the exact root $z_*$ of Theorem 6.3.2. Hold $k_*$ fixed when taking directional derivatives. For $f=p,v,a$ put

$$
A_f=(f_{rr}+k_*f_{rb},\ f_{rb}+k_*f_{bb},\ f_b)_{z_*},\qquad
T_f=\frac16(f_{rrr}+3k_*f_{rrb}+3k_*^2f_{rbb}+k_*^3f_{bbb})_{z_*}.
\tag{6.5.1}
$$

Let $A$ be the matrix with rows $A_p,A_v,A_a$, and define

$$
\begin{pmatrix}R_2\\B_2\\k_2\end{pmatrix}
=-A^{-1}\begin{pmatrix}T_p\\T_v\\T_a\end{pmatrix}.
\tag{6.5.2}
$$

The common-base and endpoint-difference coefficients are

$$
\begin{aligned}
P_2&=(p_rR_2+p_bB_2)_{z_*}
 +\tfrac12(p_{rr}+2k_*p_{rb}+k_*^2p_{bb})_{z_*},\\
V_2&=(v_rR_2+v_bB_2)_{z_*}
 +\tfrac12(v_{rr}+2k_*v_{rb}+k_*^2v_{bb})_{z_*},\\
L_x&=(x_r+k_*x_b)_{z_*},\qquad
L_m=(m_r+k_*m_b)_{z_*}.
\end{aligned}
\tag{6.5.3}
$$

These are the divided-secant coefficient definitions used at the first source in Support IX, (19.3)–(19.8), with its exact source replaced by $z_*$. The variable $k_*$ is not differentiated as a vector field.

**Theorem 6.5.2 (Evaluated second-source opening coefficients).** The matrix in (6.5.1) is invertible, and its determinant and the coefficients in (6.5.3) satisfy all the following strict bounds:

| Quantity | Strict lower bound | Strict upper bound |
|---|---:|---:|
| $\det A$ | $2.0346787949\cdot10^{14}$ | $2.0346787951\cdot10^{14}$ |
| $P_2$ | $-102.407582$ | $-102.407581$ |
| $V_2$ | $-57.385139$ | $-57.385138$ |
| $L_x$ | $2.853626$ | $2.853627$ |
| $L_m$ | $-78.900271$ | $-78.900270$ |

Proof. Evaluate the source circuit and its third-order jets by (6.4.6)–(6.4.9) over the whole box $X_*$. The denominator exclusions are the positive b interval and (6.4.12). The same derivative evaluation gives $132006.077494<p_b<132006.077495$ throughout $X_*$, so evaluate $k=-p_r/p_b$ only after this exclusion of zero. Insert those derivative intervals and that interval for $k$ into (6.5.1). The determinant endpoint comparison gives the first row of the table, so inversion of A by its adjugate is permitted. Substitution in (6.5.2)–(6.5.3), with the same rational interval operations, gives the other four rows. At any point of the box, its pointwise value of $k$ is held fixed in these formulas. The resulting intervals therefore contain, in particular, the fixed-$k_*$ coefficients at the same exact root $z_*$. This proves the bounds without identifying a rounded source with that root. ∎

### 6.6 The realized local unequal-ratio J germ

**Theorem 6.6.1 (Analytic germ, exact local correspondence and projected opening).** There are a neighborhood $\mathcal U$ of $(r_*,b_*,k_*)$, a number $\delta>0$, and even real analytic functions $R(h),B(h),k(h)$ for $|h|<\delta$, with initial value $(r_*,b_*,k_*)$, such that

$$
S_F(R,B,k,h)=0\quad\Longleftrightarrow\quad
(R,B,k)=(R(h),B(h),k(h))
\quad\bigl((R,B,k)\in\mathcal U,\ |h|<\delta\bigr).
\tag{6.6.1}
$$

Here $S_F$ has its analytic extension at $h=0$. For $0<h<\delta$, put

$$
z_\pm(h)=(R(h)\pm h,\ B(h)\pm k(h)h),\qquad
W_\pm(h)=W(z_\pm(h)).
\tag{6.6.2}
$$

These are distinct strict regular original worlds in the same entire child $C(\bar p(h),\bar v(h))$ and have equal actual J readings. Their common acquired base is even analytic and satisfies

$$
\bar p(h)=p_*+P_2h^2+O(h^4),\qquad
\bar v(h)=v_*+V_2h^2+O(h^4).
\tag{6.6.3}
$$

Their tail ratios and alternative M readings satisfy

$$
\begin{aligned}
x(z_+(h))-x(z_-(h))&=2L_xh+O(h^3)>0,\\
m(z_+(h))-m(z_-(h))&=2L_mh+O(h^3)<0.
\end{aligned}
\tag{6.6.4}
$$

Thus the projected J germ initially moves to smaller p and smaller v, lies in the unequal-x J stratum, and its own two endpoints have unequal M readings. The local correspondence (6.6.1) is confined to its stated neighborhood; no positive numerical value of $\delta$ is specified.

Proof. This is the analytic symmetric-secant construction of Support IX, (21.5)–(21.10), at the exact root $z_*$. Write $w(k)=(1,k)$ and $z=(R,B)$. For $h\ne0$, the fundamental theorem of calculus gives

$$
S_F(R,B,k,h)=\frac12\int_{-1}^{1}DF(z+thw(k))w(k)\,dt.
\tag{6.6.5}
$$

Near $(z_*,k_*,0)$ the source denominators remain nonzero. Hence F is rational analytic there; its convergent Taylor series may be integrated termwise on a smaller neighborhood, uniformly for $t\in[-1,1]$. The odd powers in t integrate to zero, giving the analytic even extension and its expansion

$$
\begin{aligned}
S_F(R,B,k,0)&=F_r(R,B)+kF_b(R,B),\\
S_F(R,B,k,h)&=DF(z)w(k)
 +\frac{h^2}{6}D^3F(z)[w(k),w(k),w(k)]+O(h^4).
\end{aligned}
\tag{6.6.6}
$$

At the same exact root $z_*$, (6.3.7) gives $S_F(z_*,k_*,0)=0$. The derivative with respect to $(R,B,k)$ at this point is exactly A, invertible by Theorem 6.5.2. The analytic implicit-function theorem therefore gives (6.6.1). One may apply the holomorphic theorem after complexifying the rational circuit, and then restrict to the real locus: the denominators are nonzero, the zero is exact, and the indicated $3\times3$ Jacobian is invertible. Local uniqueness and real coefficients force the solution to be real for real h. This is precisely the local graph statement in J. Lebl, *Tasty Bits of Several Complex Variables*, Theorem 1.3.8, [author's text](https://www.jirka.org/scv/scv.pdf). Evenness of $S_F$ and the same local uniqueness imply that the three functions are even.

Write

$$
\begin{pmatrix}R(h)\\B(h)\\k(h)\end{pmatrix}
=\begin{pmatrix}r_*\\b_*\\k_*\end{pmatrix}
 +h^2\begin{pmatrix}R_2\\B_2\\k_2\end{pmatrix}+O(h^4).
\tag{6.6.7}
$$

The $h^2$ coefficient of $S_F=0$ in (6.6.6) is $A(R_2,B_2,k_2)^{\mathsf T}+(T_p,T_v,T_a)^{\mathsf T}=0$, proving exactly (6.5.2). The $k_2$ term in an endpoint b coordinate first occurs as $\pm k_2h^3$, so it contributes nothing to the quadratic common-base coefficient. For $f=p,v$, the quadratic coefficient of either endpoint response is

$$
Df(z_*)(R_2,B_2)+\tfrac12D^2f(z_*)[(1,k_*),(1,k_*)],
\tag{6.6.8}
$$

which is $P_2$ or $V_2$ as defined. The linear coefficient vanishes by (6.3.7). For nonzero h, the exact equation $S_F=0$ is equivalent to $F(z_+)=F(z_-)$. Exchanging h and $-h$ exchanges the endpoints, making their common values even analytic and justifying the $O(h^4)$ remainders in (6.6.3).

Conversely, for any endpoints with $r_+\ne r_-$ define

$$
R=\frac{r_++r_-}{2},\quad B=\frac{b_++b_-}{2},\quad
h=\frac{r_+-r_-}{2},\quad k=\frac{b_+-b_-}{r_+-r_-}.
\tag{6.6.9}
$$

If these coordinates are in the neighborhood of (6.6.1), equality of the three actual responses is equivalent to $S_F=0$, and hence to that same local graph. This gives both directions of the local correspondence without replacing the root by its rational centre or asserting a classification of pairs outside the neighborhood.

Continuity, after decreasing $\delta$, gives $0<r_\pm(h)<1$, $b_\pm(h)>0$, $D(z_\pm(h))\ne0$, and $\bar p(h)\ne24$. The reused lift (6.2.2)–(6.2.3) then gives every original acquired reading with a single whole gain and a fixed drift for each world. The r coordinates differ by exactly $2h$, so their source matrices and complete worlds are distinct. For $f=x,m$, the endpoint difference is odd analytic and has derivative $2(f_r+k_*f_b)_{z_*}$ at zero. This yields (6.6.4); its strict signs follow from Theorem 6.5.2. The negative $P_2,V_2$ give the asserted projected direction. No condition on other companions in the entire child has entered this argument. ∎

### 6.7 An independently isolated finite J pair

**Definition 6.7.1 (Finite centre and rational preconditioner).** Set $h_0=1/1000$, $\rho_0=10^{-30}$ and

$$
\begin{aligned}
\bar R&=0.8995309197957798790286776582916565786548962027642586430930282950130813,\\
\bar B&=0.1285664820084968586773083651111633947152053709228424905272618383235844,\\
\bar k&=-1.218941298820345919523723807358533335069648080354060526783734477790392,\\
c_0&=(\bar R,\bar B,\bar k),\qquad X_0=c_0+[-\rho_0,\rho_0]^3.
\end{aligned}
\tag{6.7.1}
$$

The exact rational preconditioner for (6.4.4) is

$$
C_0^{\mathrm{pre}}=\begin{pmatrix}
\frac{-13975583622427558943304161471840912394729851440397547878904474023}{2500000000000000000000000000000000000000000000000000000000000000000} & \frac{6882167700642461190623489260937297122416805139056516872217487561}{5000000000000000000000000000000000000000000000000000000000000000000} & \frac{26250960076184444581638255324286656702754002176282137240782537797}{1000000000000000000000000000000000000000000000000000000000000000000000} \\
\frac{13632483344892035579213202729514041097122578719991717747207750383}{2000000000000000000000000000000000000000000000000000000000000000000} & \frac{-16796928300132939095506324294313574011403294734052405617936997769}{10000000000000000000000000000000000000000000000000000000000000000000} & \frac{-3945359023792686211774244213944111832075393743975309952322122761}{125000000000000000000000000000000000000000000000000000000000000000000} \\
\frac{1232354630508002273440460988478139179132792433173848646907174967}{100000000000000000000000000000000000000000000000000000000000000000} & \frac{-25539723188950892027333758401097315885268122366741958418158880117}{10000000000000000000000000000000000000000000000000000000000000000000} & \frac{-1055794513474065447665565180936309033144961025576262369878733763}{5000000000000000000000000000000000000000000000000000000000000000000}
\end{pmatrix}
\tag{6.7.2}
$$

**Theorem 6.7.2 (Strict finite original J pair).** There is a unique zero $(R_0,B_0,k_0)$ of $S_F(\,\cdot\,,1/1000)$ in $X_0$. Define its exact endpoints by

$$
r_\pm=R_0\pm1/1000,\qquad b_\pm=B_0\pm k_0/1000,
\qquad W_\pm=W(r_\pm,b_\pm).
\tag{6.7.3}
$$

Each endpoint uses its own whole gain and drift from (6.2.2). These worlds have equal exact p, v and a, and the following strict enclosures:

| Quantity | Plus world | Minus world |
|---|---|---|
| $r$ | $(0.900530919795779878,0.900530919795779881)$ | $(0.898530919795779878,0.898530919795779881)$ |
| $b$ | $(0.127347540709676511,0.127347540709676514)$ | $(0.129785423307317203,0.129785423307317206)$ |
| $d$ | $(30.765383329012990998,30.765383329012991002)$ | $(30.846249957719705455,30.846249957719705460)$ |
| $D$ | $(-0.031581090465,-0.031581090464)$ | $(-0.064012570271,-0.064012570270)$ |
| $x$ | $(1.379832002062135673,1.379832002062135677)$ | $(1.374124732145660566,1.374124732145660570)$ |
| $m$ | $(104.508734223405322671,104.508734223405322675)$ | $(104.666534446288672599,104.666534446288672603)$ |

Their common acquired and terminal J responses satisfy

$$
\begin{aligned}
-10.890483419191447750&<p<-10.890483419191447745,\\
-8.153641304213516424&<v<-8.153641304213516418,\\
95.981162469139639674&<a<95.981162469139639680.
\end{aligned}
\tag{6.7.4}
$$

In particular the sources are strict and regular, $p\ne24$, $r_+-r_-=1/500$ exactly, $x_+>x_-$ and $m_+<m_-$. This is an actual original-world J pair, whose selected endpoints do not form an equal-M pair. Its existence and box uniqueness do not identify it with a point of the local germ of Theorem 6.6.1.

Proof. The finite inclusion (6.4.11) supplies the unique exact zero in $X_0$. Evaluating the affine endpoints (6.7.3), followed by (6.2.1)–(6.2.2), with the exact interval rules (6.4.6) gives the endpoint table and (6.7.4). The nonzero D intervals permit every division in the source circuit. The strict r and b intervals put both endpoints in the original source domain. At the exact zero, the defining divided secant has nonzero denominator $2h_0$, so its zero means equality of p, v and a themselves, not merely overlap of their displayed intervals. The p interval excludes 24, and the exact r separation proves that the complete worlds are different.

To give each entire gain also in Newton form, put $q_i=C_i/D$ at its own endpoint. Then

$$
\begin{aligned}
g(s)={}&q_0+(q_1-q_0)s
 +\frac{q_2-2q_1+q_0}{2}s(s-1)\\
 &+\frac{q_3-3q_2+3q_1-q_0}{6}s(s-1)(s-2),\qquad d=-q_0.
\end{aligned}
\tag{6.7.5}
$$

This is the same unique polynomial as (6.2.2), by its values at $0,1,2,3$; compare Berrut–Trefethen, Section 2, equation (2.4). The identities (6.2.3) give the entire acquired history and both terminal alternatives, with this one polynomial and its fixed drift at each endpoint. The unequal first two readings again show that neither whole gain is zero. Finally, subtraction of the two strict x intervals gives $x_+>x_-$, and subtraction of the two strict M intervals gives, more explicitly,

$$
-0.157800222883349932<m_+-m_-<-0.157800222883349924<0.
\tag{6.7.6}
$$

These establish all the guards and the M inequality for the selected pair. The proof uses the finite box inclusion alone; no continuation from $h=0$ to $h=1/1000$ is asserted. ∎

### 6.8 The full remaining common-base problem

**Definition 6.8.1 (Unrestricted independent-pair relation).** In the original problem retain the full fixed-terminal inverse of Support X, Theorems 3.3 and 4.3, and Definition 6.3. For arbitrary real $p\ne24,v$, choose $m_0,m_1,m$ independently and reconstruct

$$
\begin{aligned}
W_0&\text{ from }\mathcal R(p,v,m_0)\sqcup\mathcal E(p,v,m_0),\\
W_1&\text{ from }\mathcal R(p,v,m_1)\sqcup\mathcal E(p,v,m_1),\\
W_2,W_3&\text{ independently from }\mathcal R(p,v,m)\sqcup\mathcal E(p,v,m).
\end{aligned}
\tag{6.8.1}
$$

The actual J values of the first pair are exactly

$$
a_i=d_i+\left(\frac{1+u_i}{2}+2x_i+2u_ir_i\right)
                 \frac{m_i-d_i}{2x_i+3},\qquad i=0,1.
\tag{6.8.2}
$$

There is no division by $m_i-d_i$. In the notation and polynomial definitions of Support X, (3.1), every ordinary root retains all the guards

$$
\begin{gathered}
F=G=0,\qquad x>0,\qquad K\ne0,\qquad D_*>0,\qquad
0<W_*<D_*,\\
ZZ_1>0,\qquad (W_*Z_1-ZD_*)Z_1>0,
\end{gathered}
\tag{6.8.3}
$$

and is reconstructed by exactly its inverse (3.5). The F and G in (6.8.3) are those inverse polynomials, not the three-component source map of (6.2.2). The exceptional coordinate is the positive root $\kappa$ of

$$
K(x)=8x^4+29x^3+18x^2-15x-6.
\tag{6.8.4}
$$

Its entire layer is retained with Support X, (4.5)–(4.8): $N(\kappa)=0$, the drift equation $\Phi_\kappa(d)=0$, the sum-of-squares condition $H_0^2+H_2^2>0$, $H_1\ne0$, $0<u<1$, $0<r<1$, and the exact source identity $bj=b^2+r(1-r)$, with the whole interpolant and reconstruction prescribed there. Singular original sources, zero drift, sampled gain zeros, lower degrees, repeated roots, the golden-coordinate layer and the exceptional layer all remain in the full relation.

In these variables the unresolved problem is still

$$
\begin{gathered}
\exists p\ne24,\ v,\ m_0,m_1,m,\quad
W_0,W_1,W_2,W_3\in\text{the same entire }C(p,v):\\
W_0\ne W_1,\qquad a_0=a_1,\qquad
W_2\ne W_3,\qquad m(W_2)=m(W_3)=m,
\end{gathered}
\tag{6.8.5}
$$

with no cross-pair inequalities, no equation between the common terminal answers, and no requirement $m_0=m_1$. The selected pair of Theorem 6.7.2 belongs to $D_J^{\ne}$ of Section 5.6; its unequal M values impose no exclusion on any independently selected M pair among other companions. Theorem 6.6.1 likewise imposes no condition on equal-x J pairs elsewhere. The evaluated second-source opening and the strict finite pair provide J incidence only. Neither result supplies an independent equal-M pair at the same base, an inventory of an entire child, a global uniqueness assertion, or an all-domain absence theorem. In particular they do not decide either intersection in (5.6.3).

## 追加锚（本行以下为增补区）

## 7. A connected finite second-J arc through the singular parent

### 7.1 The selected family and its undivided equations

**Definition 7.1.1 (Original worlds and selected secants).** The ambient domain is exactly (6.1.1): every source matrix is entrywise strictly positive, rank one and trace one; the gain is any nonzero real polynomial of degree at most three; and the constant drift is any real number. Signs, sampled zeros, repeated roots and degree drops have no additional ambient restriction. The acquired history is the literal history (6.1.2)–(6.1.3). In particular the initial observation counts, each action is immediately read, and the seventh J and M are alternative actions. The parameter below is a coordinate on a family of worlds, not an additional acquired observation.

For a strict source $(r,b)$ and a real $e$, retain $j,n,T,U$ from (6.1.4), and set

$$
\begin{aligned}
B_{\mathrm{coef}}&=6/T-2/U=2(2+5b)/(TU),\\
\Lambda&=1+6/T+1/U-4/j-4/n,\\
H(r,b,e)&=e\Lambda+\frac{24}{5}(b-1/8)B_{\mathrm{coef}},\\
q_0&=-24-e,&q_1&=-e/j,&q_2&=(27/5-e)/T,&q_3&=-e/n,\\
d&=24+e,&
g_{r,b,e}(s)&=\sum_{i=0}^3q_i
 \prod_{\substack{0\le a\le3\\a\ne i}}\frac{s-a}{i-a}.
\end{aligned}
\tag{7.1.1}
$$

Each endpoint uses its own polynomial in this formula. The actual response circuit is

$$
\begin{aligned}
g_5&=-4q_0+15q_1-20q_2+10q_3,\\
g_6&=-10q_0+36q_1-45q_2+20q_3,\\
g_7&=-20q_0+70q_1-84q_2+35q_3,\\
p&=24+e+(U+n)g_5,\\
v&=24+e+(2U+n)g_6,\\
a&=24+e+(T+2j+4r)g_7,\\
m&=24+e+(3U+2n)g_7,\qquad x=n/U.
\end{aligned}
\tag{7.1.2}
$$

Use the two-coefficient algebra with elements $A+\epsilon B$ and relation $\epsilon^2=t$. Its arithmetic is

$$
\begin{aligned}
(A,B)+(C,D)&=(A+C,B+D),\\
(A,B)(C,D)&=(AC+tBD,AD+BC),\\
(A,B)^{-1}&=(A,-B)/(A^2-tB^2).
\end{aligned}
\tag{7.1.3}
$$

For $y=(R,B,E,k,\ell)$ substitute

$$
r=(R,1),\qquad b=(B,k),\qquad e=(E,\ell)
\tag{7.1.4}
$$

in (7.1.1)–(7.1.2). Write the two coefficients of any resulting quantity $f$ as $(f_{\mathrm{av}},f_{\mathrm{sec}})$. The five-equation system is

$$
G(y,t)=
\bigl(H_{\mathrm{av}},H_{\mathrm{sec}},
      p_{\mathrm{sec}},v_{\mathrm{sec}},a_{\mathrm{sec}}\bigr)=0.
\tag{7.1.5}
$$

For $t=h^2\ge0$, evaluation at $\epsilon=\pm h$ gives the endpoints

$$
r_\pm=R\pm h,\qquad b_\pm=B\pm kh,\qquad
 e_\pm=E\pm\ell h,\qquad
W_\pm=(P(r_\pm,b_\pm),g_{r_\pm,b_\pm,e_\pm},24+e_\pm).
\tag{7.1.6}
$$

The circuit divides only by fixed interpolation constants and source traces, or their products represented by (7.1.3). It has no quotient by $h$, $\Lambda$, the regular $D$ of (6.2.1), drift, a gain sample, a leading coefficient or a gain-root separation. At $t=0$ the algebra is the algebra of dual numbers: $f_{\mathrm{sec}}$ is the derivative in direction $(1,k,\ell)$. Thus (7.1.5) is defined at the coalescence point as well as at a singular-parent source.

### 7.2 Rational boxes and their finite inequalities

**Definition 7.2.1 (The continuation tubes).** All terminating decimals in Section 7 are exact rationals. Define componentwise rounding by

$$
Q_{45}(u)=10^{-45}\left\lfloor10^{45}u+\frac12\right\rfloor.
\tag{7.2.1}
$$

Start with

$$
c_{-1}=(0.8995316741215983,\ 0.1285667303082648,
6.80570463553447,\ -1.2189475090087154,\ -40.43312488361048).
\tag{7.2.2}
$$

For $i=0,\ldots,127$ put

$$
\begin{gathered}
T_i=[i/8000000,(i+1)/8000000],\qquad
 t_i=(2i+1)/16000000,\qquad \Delta=1/16000000,\\
c_i^{(0)}=c_{i-1},\qquad
c_i^{(a+1)}=Q_{45}\!\left(c_i^{(a)}-
 [D_yG(c_i^{(a)},t_i)]^{-1}G(c_i^{(a)},t_i)\right)
\quad(0\le a<5),\\
c_i=c_i^{(5)},\qquad C_i=Q_{45}\bigl([D_yG(c_i,t_i)]^{-1}\bigr),\\
\rho=(1/4000000,\ 1/4000000,\ 1/20000,\ 1/400000,\ 3/40000),\\
X_i=\prod_{j=1}^5[c_{i,j}-\rho_j,c_{i,j}+\rho_j],\qquad
\|z\|_\rho=\max_j |z_j|/\rho_j.
\end{gathered}
\tag{7.2.3}
$$

Here $\rho_B=\rho_2$ and $\rho_k=\rho_4$. Matrix rounding is entrywise. These formulas define rational centres and preconditioners, rather than approximations used as exact roots. The 128 closed parameter cells cover exactly $[0,1/62500]$.

Here is a rational enclosure prescription for every inequality used below. A scalar interval operation first uses the endpoint rules (6.4.6), then replaces its lower endpoint $a$ by $2^{-240}\lfloor2^{240}a\rfloor$ and its upper endpoint $b$ by $2^{-240}\lceil2^{240}b\rceil$. Singleton rational constants are enclosed by the same rule. Products use the four endpoint products; powers mean repeated multiplication. Inverses are formed only after excluding zero. In particular these operations are enclosures, not floating point equalities.

Differentiate the displayed circuit in the six independent variables $(R,B,E,k,\ell,t)$. For an interval value $u$ with derivative vector $\dot u$, propagate

$$
\begin{aligned}
\dot{(u+v)}&=\dot u+\dot v,\\
\dot{(uv)}&=\dot u\,v+u\,\dot v,\\
\dot{(u^{-1})}&=-\dot u\,u^{-1}u^{-1}.
\end{aligned}
\tag{7.2.4}
$$

These rules apply to the scalar operations inside (7.1.3), including the derivative of its factor $t$. They specify enclosures of $G,D_yG,G_t$ without numerical differentiation. Matrix inversion in (7.2.3) can be enclosed by Gauss–Jordan elimination: use diagonal pivots in increasing order, normalize the entire pivot row, and eliminate that column in every other row. No row interchange is required here. Each pivot interval excludes zero; for every rounded entry in (7.2.3), both enclosure endpoints give the same integer in (7.2.1). Hence this enclosure prescription determines the exact rounded rational recurrence.

For a vector or matrix of intervals let $|\cdot|_{\sup}$ mean the largest absolute endpoint, entrywise. Define the rational numbers

$$
\begin{aligned}
q_i&=\max_j\sum_{k=1}^5
 \bigl|[I-C_iD_yG(X_i,T_i)]_{jk}\bigr|_{\sup}\frac{\rho_k}{\rho_j},\\
\beta_i&=\max_j\frac{
 |[C_iG(c_i,t_i)]_j|_{\sup}
 +\Delta|[C_iG_t(c_i,T_i)]_j|_{\sup}}{\rho_j},\\
D_i&=\frac{1}{1-q_i}\max_j
 \frac{|[C_iG_t(X_i,T_i)]_j|_{\sup}}{\rho_j}.
\end{aligned}
\tag{7.2.5}
$$

In particular the derivative enclosure in $D_i$ uses the whole tube, while the one in $\beta_i$ has fixed centre $c_i$.

For a common seam $\sigma_i=(i+1)/8000000$, $0\le i<127$, put

$$
\begin{gathered}
\widetilde c_i=(c_i+c_{i+1})/2,\qquad
\widetilde\rho_{i,j}=\rho_j+|c_{i,j}-c_{i+1,j}|/2,\\
\widetilde X_i=\prod_j[
\widetilde c_{i,j}-\widetilde\rho_{i,j},
\widetilde c_{i,j}+\widetilde\rho_{i,j}],\\
\widetilde q_i=\max_j\sum_k
 |[I-C_iD_yG(\widetilde X_i,\sigma_i)]_{jk}|_{\sup}
 \frac{\widetilde\rho_{i,k}}{\widetilde\rho_{i,j}}.
\end{gathered}
\tag{7.2.6}
$$

This is a box containing the convex hull of the two neighboring tubes; both neighboring seam roots are in that box.

**Lemma 7.2.2 (Uniform rational inequalities).** The recurrence and enclosures (7.2.1)–(7.2.6) have the following bounds:

| Quantity | Rational upper bound | Sufficient strict bound |
|---|---:|---:|
| $\max_i q_i$ | $110094427447/250000000000$ | $441/1000$ |
| $\max_i\beta_i$ | $263610622981/1000000000000$ | $264/1000$ |
| $\max_i\widetilde q_i$ | $47763641509/200000000000$ | $239/1000$ |
| $\max_i\rho_BD_i$ | $247533043797/100000000000$ | $5/2$ |
| $\max_i\rho_kD_i$ | $247533043797/10000000000$ | $25$ |

In particular $q_i+\beta_i<141/200<1$. All inverses in these enclosures are defined. On all tubes, $B>0.1285$ and $k<-1.2188$. For both scalar endpoints (7.1.6), the following larger rational intervals contain the enclosures, uniformly over the cells and $0\le h\le1/250$, $h^2\in T_i$:

| Quantity | Lower endpoint | Upper endpoint |
|---|---:|---:|
| $r_\pm$ | $447759700931/500000000000$ | $903519901863/1000000000000$ |
| $b_\pm$ | $3092177973/25000000000$ | $8339901701/62500000000$ |
| $e_\pm$ | $1661423734033/250000000000$ | $3484642346261/500000000000$ |
| $d_\pm$ | $7661423734033/250000000000$ | $15484642346261/500000000000$ |
| $p_\pm$ | $-13368909895949/1000000000000$ | $-4212208536209/500000000000$ |
| $x_{\mathrm{sec}}$ | $1426727197703/500000000000$ | $2853937651871/1000000000000$ |

Consequently the simpler strict bounds are

$$
\begin{gathered}
0.8955<r_\pm<0.9036,\qquad
0.1236<b_\pm<0.1335,\\
6<e_\pm,\qquad30<d_\pm<32,\qquad
-13.37<p_\pm<-8.42,\qquad2.85<x_{\mathrm{sec}}<2.86.
\end{gathered}
\tag{7.2.7}
$$

Proof. The two finite index ranges in this lemma are $0\le i<128$ and $0\le i<127$; the centres for every index are fixed by (7.2.2)–(7.2.3). Apply (7.2.4) to (7.1.1)–(7.1.5), enclose the inverse and the five successive rounded corrections at each $t_i$, and substitute the resulting $c_i,C_i$ into (7.2.5). The maximum row sums and weighted residual sums give the first two rows of the first table. The same derivative enclosure on (7.2.6), weighted now by $\widetilde\rho_i$, gives its third row. Substituting the full-tube $G_t$ and the first row in the last line of (7.2.5) gives its last two rows. Every number in these comparisons is rational, with the outward rounding specified above. The first two sufficient bounds sum to $141/200$.

For the endpoint rows use scalar evaluations of (7.1.1)–(7.1.2), independently of the coefficient evaluation (7.1.3). More explicitly, set $M_0=10^{60}$ and enclose $h$ in cell $i$ by

$$
\frac{\lfloor M_0\sqrt{i/8000000}\rfloor}{M_0}
\le h\le
\frac{\lceil M_0\sqrt{(i+1)/8000000}\rceil}{M_0}.
\tag{7.2.8}
$$

The integers here are characterized solely by integer square comparisons. Insert this interval and $X_i$ into (7.1.6), followed by the scalar circuit. The minimum lower and maximum upper endpoints are enclosed by the first five rows of the second table. The sixth row instead comes from the second coefficient of $x$ in (7.1.3). The centre intervals for $B,k$ give the two asserted uniform inequalities directly. The strict positive source bounds also show $j,n,T,U>0$. For a pair inverse its exact denominator is the product of its two scalar endpoint values. The outward enclosures in the prescription exclude zero for those denominators as well as for the matrix pivots. Thus no source or matrix inverse in the two tables presupposes the existence of a zero. These explicit rational recurrences, enclosure rules and scalar comparison bounds constitute the finite inequalities of the lemma. ∎

The interval step is the classical preconditioned interval contraction, as in R. Krawczyk, *Newton-Algorithmen zur Bestimmung von Nullstellen mit Fehlerschranken*, Computing 4, 187–201, [doi:10.1007/BF02234767](https://doi.org/10.1007/BF02234767). Its use here concerns the particular five-equation source circuit; it is not a new general interval theorem.

### 7.3 The connected finite arc theorem

**Theorem 7.3.1 (Finite second-J arc, attachments and singular passage).** There is a continuous graph

$$
y(t)=(R(t),B(t),E(t),k(t),\ell(t)),\qquad
0\le t\le1/62500,
\tag{7.3.1}
$$

with $G(y(t),t)=0$, lying in $X_i$ whenever $t\in T_i$. At every point it has a locally real analytic extension. In each $X_i$ the zero is unique for fixed $t\in T_i$, and the two neighboring roots agree at every common seam. These are the uniqueness domains of the theorem; no maximal-component assertion is part of it.

For every $0<h\le1/250$, put $t=h^2$ and use (7.1.6). The resulting complete worlds are distinct and legal, realize every original acquired row, and satisfy

$$
\begin{gathered}
\bar p(h)=p(W_+(h))=p(W_-(h))\ne24,\\
\bar v(h)=v(W_+(h))=v(W_-(h)),\qquad
\bar a(h)=a(W_+(h))=a(W_-(h)),\\
W_+(h),W_-(h)\in C(\bar p(h),\bar v(h)),\qquad
2.85(2h)<x(W_+(h))-x(W_-(h))<2.86(2h).
\end{gathered}
\tag{7.3.2}
$$

The family has the exact critical/local-germ attachment of Theorems 6.3.2 and 6.6.1 at $t=0$, where the two worlds coalesce, and the exact finite-pair attachment of Theorem 6.7.2 at $h=1/1000$.

There is exactly one occurrence of $\Lambda=0$ among these two selected endpoints for $0<h\le1/250$. It occurs at the plus endpoint, at a parameter $h_*$ satisfying the rational bracket

$$
0.0029244590442435<h_*<0.0029244590442437.
\tag{7.3.3}
$$

At that parameter,

$$
b_+(h_*)=1/8,\qquad r_+(h_*)=\varrho_+,\qquad
\bar v(h_*)=s_+(\bar p(h_*)),
\tag{7.3.4}
$$

where $\varrho_+$ and $s_+$ are exactly the designated root and original singular response line of [Support X](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md), (13.6)–(13.11). The crossing is transverse: $d\Lambda_+/dh>0$ there. The minus endpoint has $\Lambda_-<0$ throughout. The same complete-world graph continues through this event and includes the entire strict post-crossing interval $[3/1000,1/250]$.

The numerical source and positive-drift bounds (7.2.7) are properties of this constructed family. The ambient domain remains Definition 7.1.1. The common base in (7.3.2) is chosen separately at each same $h$; no worlds from different $h$ are combined. At $h=0$ the coalesced world is an attachment, not a distinct-pair witness. The quantifiers in this theorem concern this selected ordered pair and the stated tubes. The independent-pair quantifiers of (6.8.5), which range over the entire child and independent terminal values, remain the definition of the broader problem.

Proof of the graph and its complete-world assertions. For fixed $t\in T_i$ define

$$
\mathcal T_{i,t}(y)=y-C_iG(y,t).
\tag{7.3.5}
$$

The line-segment mean-value formula and (7.2.5) give a Lipschitz constant $q_i<1$ on the convex box $X_i$ in the $\rho$ norm. The parameter mean-value formula at the fixed centre gives

$$
\|C_iG(c_i,t)\|_\rho\le\beta_i.
\tag{7.3.6}
$$

Thus, for $y\in X_i$,

$$
\|\mathcal T_{i,t}(y)-c_i\|_\rho
\le\beta_i+q_i\|y-c_i\|_\rho<1.
\tag{7.3.7}
$$

Iteration is Cauchy in the complete closed box: successive distances are bounded by a geometric series with ratio $q_i$. Its limit is a fixed point, unique in that box. At every point of the tube, $\|I-C_iD_yG\|_\rho<1$, so the convergent Neumann series in $I-C_iD_yG$ inverts $C_iD_yG$. Since both matrices are square, both $C_i$ and $D_yG$ are invertible. Consequently the fixed points in question are exactly the zeros of $G$. This is the contraction principle of S. Banach, *Sur les opérations dans les ensembles abstraits et leur application aux équations intégrales*, Fundamenta Mathematicae 3, 133–181, [doi:10.4064/fm-3-1-133-181](https://doi.org/10.4064/fm-3-1-133-181), applied to these explicit boxes; the preceding geometric-series argument gives the needed implication in full.

Comparing fixed-point equations at two parameters gives continuity: the parameter term is bounded by a constant times $|t-t'|$, and the difference in fixed points is bounded by that term divided by $1-q_i$. Taylor expansion of $G$ at a zero, with this continuity and the invertible $y$ Jacobian, gives

$$
y_t=-(D_yG)^{-1}G_t,\qquad
\|y_t\|_\rho\le D_i,\qquad |B_t|<5/2,\quad |k_t|<25.
\tag{7.3.8}
$$

These bounds hold up to a seam from either side. The rational circuit is analytic wherever its denominators are nonzero. For completeness, local analytic dependence can also be seen without any uniform analytic radius: complexify near an exact zero, precondition by its exact inverse $y$ Jacobian, and choose small complex balls where the derivative of the fixed-point map has norm less than one. For nearby complex $t$ the map sends the smaller closed ball into itself. Its holomorphic iterates converge locally uniformly by the same geometric bound. The Cauchy integral formula passes to the limit, making the fixed point holomorphic. Real coefficients and uniqueness make it real for real $t$. This is the usual analytic implicit-function theorem, also stated in J. Lebl, *Tasty Bits of Several Complex Variables*, Theorem 1.3.8, [author's text](https://www.jirka.org/scv/scv.pdf).

At $t=\sigma_i$, both zeros belong to $\widetilde X_i$. If they were $u,v$, their zero equations and (7.2.6) would imply

$$
\|u-v\|_{\widetilde\rho_i}
=\|(u-C_iG(u,\sigma_i))-(v-C_iG(v,\sigma_i))\|_{\widetilde\rho_i}
\le\widetilde q_i\|u-v\|_{\widetilde\rho_i}.
\tag{7.3.9}
$$

Since $\widetilde q_i<1$, they coincide. This is uniqueness on a common containing box, not an inference from overlap of rounded root coordinates. Local implicit uniqueness identifies their analytic extensions across the seam. All cells therefore give one continuous, locally analytic graph on the full closed interval. The graph is connected as the continuous image of that interval.

When $t=h^2$, evaluation at $\epsilon=\pm h$ is an algebra homomorphism in (7.1.3). Its inverses are legitimate by the source and denominator bounds of Lemma 7.2.2. Equations $H_{\mathrm{av}}=H_{\mathrm{sec}}=0$ imply $H(r_\pm,b_\pm,e_\pm)=0$; the other three zero coefficients imply exact equality of the two p, v and a values. These are identities of the actual response functions, rather than overlap of numerical response intervals.

The fixed-node polynomial in (7.1.1) has samples $q_i$ at clocks $i=0,1,2,3$ and the rows (7.1.2) at clocks $5,6,7$. Its clock-four value is $g(4)=-q_0+4q_1-6q_2+4q_3$, and direct substitution gives

$$
24+e+Ug(4)-18=U H(r,b,e).
\tag{7.3.10}
$$

Hence each endpoint gives exactly $(0,24,147/5,24,18,p,v)$ at the original clocks zero through six. The acquired traces and the two clock-seven traces are exactly (6.1.4)–(6.1.5), with the chronological left products (6.1.2); these are the whole-world interfaces of [common-parent geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3 and Theorem 2.1. Both endpoints share the actual ancestor $H_4=(0,J,24,M,147/5,J,24,M,18)$, followed by the same fifth-M response $\bar p(h)$ and sixth-M response $\bar v(h)$ at that fixed $h$.

The interpolation is the classical distinct-node formula; see J.-P. Berrut and L. N. Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review 46, 501–517, Section 2, [doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715). Here it supplies one polynomial per world, at all original clocks, including the terminal alternatives. An identically zero gain would make the first two readings equal to the same drift, contradicting $0\ne24$. The bounds $0<r_\pm<1,b_\pm>0$ make $P(r_\pm,b_\pm)$ strictly positive, trace one and determinant zero, hence rank one. The two r coordinates differ by $2h$, so for $h>0$ the complete worlds are distinct. Lemma 7.2.2 gives $p\ne24$. Its $x_{\mathrm{sec}}$ row gives the last inequality in (7.3.2) because $x_+-x_-=2h x_{\mathrm{sec}}$. Finally all four gain coefficients and both drifts vary continuously by (7.1.1). Thus the passage is a connected passage in complete-world coordinates as well as in source coordinates. The attachments and singular assertions are proved in Sections 7.4–7.6. ∎

### 7.4 Exact identification of the two attachments

**Lemma 7.4.1 (Small-box inclusions at the two anchors).** At each named parameter in the following table, perform five rounded Newton corrections as in (7.2.3), starting from the centre $c_i$ of a containing parameter cell; use $i=0$ at $t=0$ and $i=7$ at $t=10^{-6}$. Recompute the preconditioner there. With radius

$$
\rho^{\mathrm{tight}}=10^{-38}(1,1,200,10,300),
\tag{7.4.1}
$$

the resulting boxes lie strictly inside the corresponding $X_i$ and have a unique zero. Their rational centres are:

| Coordinate | $t=0$ | $t=1/1000000$ |
|---|---|---|
| $R$ | $0.899531674121598268409726976420781980350411105$ | $0.899530919795779879028677658291656578654896203$ |
| $B$ | $0.128566730308264757217243801879783944149492431$ | $0.128566482008496858677308365111163394715205371$ |
| $E$ | $6.805704635534469639189632374509777994071045443$ | $6.805816643366348228487842227674526738692718910$ |
| $k$ | $-1.218947509008715401675263421889754639362546698$ | $-1.218941298820345919523723807358533335069648080$ |
| $\ell$ | $-40.433124883610480451982746582403325602528193723$ | $-40.433314353357228754415347410117133065899974444$ |

Using (7.2.5) with these radii, fixed $t$ and $\Delta=0$, the respective upper bounds for $q+\beta$ are

$$
\frac{2717869591}{10^{18}}<10^{-7},\qquad
\frac{23574135691}{10^{18}}<10^{-7}.
\tag{7.4.2}
$$

The first $(R,B)$ box lies strictly in $X_*$ of (6.3.5); the second $(R,B,k)$ box lies strictly in $X_0$ of (6.7.1).

Proof. The prescription is the same rational circuit, differentiation and outward arithmetic as Definition 7.2.1, now with a singleton parameter interval. Its weighted residual and derivative sums give (7.4.2). The strict containments in $X_i$ follow coordinatewise from $|c_j^{\mathrm{tight}}-c_{i,j}|+\rho_j^{\mathrm{tight}}<\rho_j$. The source-box containments follow by comparing the displayed rational centres with (6.3.5) and (6.7.1), with their radii $10^{-35}$ and $10^{-30}$. The contraction argument (7.3.5)–(7.3.7) then supplies the unique zero of each tight box, and uniqueness in $X_i$ identifies it with the graph root at that same $t$. No equality between rounded coordinates and an exact source has been used. ∎

Proof of the attachment clauses of Theorem 7.3.1. At $t=0$ the root has $B>1/8$ and $E>6$. Thus $H=0$ implies $\Lambda<0$. The regular implicit solution of $H=0$ is

$$
e(r,b)=-\frac{(24/5)(b-1/8)B_{\mathrm{coef}}}{\Lambda}.
\tag{7.4.3}
$$

This elimination is used only near the regular attachment. The coefficient equation $H_{\mathrm{sec}}=0$ gives $\ell=e_r+k e_b$. Consequently the remaining three equations at zero are precisely

$$
F_r(R,B)+kF_b(R,B)=0
\tag{7.4.4}
$$

for the exact regular map $F=(p,v,a)$ of (6.2.2). Indeed $D=(5/2)TUjn\Lambda$, and substitution of (7.4.3) in (7.1.1) gives $d=-C_0/D$ and $q_i=C_i/D$ of (6.2.1)–(6.2.2). The interpolants are therefore the same entire polynomial.

On $X_*$, the existing $p_b$ bound of Section 6.5 excludes zero. The p row of (7.4.4) gives $k=-p_r/p_b$. The other two rows imply $\det D(p,v)=\det D(p,a)=0$, hence $E_1=E_2=0$ by (6.3.4)–(6.3.6). Lemma 7.4.1 puts $(R,B)$ in $X_*$; uniqueness in Theorem 6.3.2 now gives $(R,B)=z_*$ exactly, and then $k=k_*$. Equation (7.4.3) fixes $E$, and $H_{\mathrm{sec}}=0$ fixes $\ell$. This identifies the complete coalesced world with the exact second critical world, not merely with its displayed approximation.

For sufficiently small positive $h$, continuity keeps both endpoints regular and places $(R(h^2),B(h^2),k(h^2))$ in the uniqueness neighborhood of Theorem 6.6.1. Eliminating $e_\pm$ by (7.4.3) makes their p, v and a equations exactly its $S_F=0$. The local uniqueness (6.6.1) therefore identifies this projection with that even analytic germ. This proves the germ attachment, including its existing entire gains, without a numerical comparison of two germs.

At $t=10^{-6}$, Lemma 7.4.1 gives both $b_\pm>1/8$, so $H_\pm=0$ and $e_\pm>6$ again imply $\Lambda_\pm<0$. The same exact regular elimination gives $S_F(R,B,k,1/1000)=0$. Its $(R,B,k)$ lies in $X_0$, so Theorem 6.7.2 identifies it with that unique exact finite zero. Formula (7.1.1) then identifies both entire polynomials and drifts with (6.2.2), not only their sources or responses. This is the finite bridge between the local germ and the independently isolated pair. ∎

### 7.5 The selected singular crossing and its rational bracket

**Lemma 7.5.1 (Two rational signs).** Set

$$
h_L=0.0029244590442435,\qquad h_U=0.0029244590442437.
\tag{7.5.1}
$$

For each $t=h_L^2,h_U^2$, use the tight-box prescription of Lemma 7.4.1, starting at $c_i$ with $i=\lfloor8000000t\rfloor$. The boxes are strictly contained in their $X_i$. Their respective upper bounds for $q+\beta$ are

$$
\frac{11716015439}{250000000000000000}<10^{-7},\qquad
\frac{44016049399}{10^{18}}<10^{-7}.
\tag{7.5.2}
$$

The exact graph values satisfy

$$
\begin{aligned}
120/10^{18}&<b_+(h_L)-1/8<121/10^{18},\\
-124/10^{18}&<b_+(h_U)-1/8<-123/10^{18}.
\end{aligned}
\tag{7.5.3}
$$

Proof. The parameter values in this prescription are the exact squares of the rationals (7.5.1). With the same singleton-parameter weighted sums as (7.4.2), the enclosure prescription gives (7.5.2). Direct substitution of the resulting tight B and k intervals into $B+kh-1/8$ gives the respective enclosing intervals

$$
\begin{aligned}
&\left[\frac{120287721883177}{10^{30}},
        \frac{60143860941589}{5\cdot10^{29}}\right],\\
&\left[-\frac{61880183664779}{5\cdot10^{29}},
        -\frac{123760367329557}{10^{30}}\right].
\end{aligned}
\tag{7.5.4}
$$

Each is strictly within its interval in (7.5.3). The tight-box containments and contraction identify these roots with the same full-interval graph, so these are signs at exact graph points. ∎

Proof of the crossing and continuation clauses of Theorem 7.3.1. By (7.3.8) and the uniform k bound,

$$
\begin{aligned}
\frac{db_+}{dh}
 &=k+2hB_t+2h^2k_t\\
 &<-1.2188+2(1/250)(5/2)+2(1/250)^2(25)\\
 &=-599/500<0.
\end{aligned}
\tag{7.5.5}
$$

Meanwhile $b_-=B-kh>B>0.1285>1/8$ for $h>0$. Equations (7.5.3), continuity and strict monotonicity give exactly one $h_*$ in (7.3.3) with $b_+(h_*)=1/8$. Since $e_\pm>6$ and $B_{\mathrm{coef},\pm}>0$, the two parent equations give

$$
\operatorname{sign}\Lambda_\pm
=-\operatorname{sign}(b_\pm-1/8).
\tag{7.5.6}
$$

Thus this is exactly the sole selected $\Lambda=0$ event. At the event, differentiation of the undivided equation gives

$$
e_+(h_*)\frac{d\Lambda_+}{dh}(h_*)
=-\frac{24}{5}B_{\mathrm{coef},+}(h_*)
  \frac{db_+}{dh}(h_*)>0.
\tag{7.5.7}
$$

This proves transversality and the direction of the crossing. No division by a vanishing parent coefficient appears.

At width $1/8$ the existing singular identity is

$$
960jn\Lambda=\Phi(r),\qquad
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853.
\tag{7.5.8}
$$

Support X, (13.6)–(13.7), classifies exactly two strict roots. Its $\varrho_-$ lies in $(0.1348,0.1349)$, while its $\varrho_+$ lies in the rational interval

$$
\left[
\frac{902449681772056265377872651296542856186276499}{10^{45}},
\frac{902449681772056265377872651296542856186276500}{10^{45}}
\right].
\tag{7.5.9}
$$

The graph source satisfies $0.8955<r_+(h_*)<0.9036$. It is a strict root of (7.5.8), so the existing classification excludes $\varrho_-$ and identifies it exactly with $\varrho_+$. This identity uses the quartic equation and the separated root classification, not closeness of a numerical event source to a printed root.

The Jacobian $D_yG$ is invertible on the same graph at this event by (7.3.7)–(7.3.8). The five-equation circuit itself has no singularity there. Consequently the local analytic graph and its own entire gains extend through the event; the finite tubes already continue it all the way to $h=1/250$. Since $h_U<3/1000$, every $h\in[3/1000,1/250]$ lies strictly after the crossing, with $\Lambda_+>0$ and $\Lambda_-<0$ and with the legal full-world bounds already proved. ∎

### 7.6 The original same-base singular response and its complete lift

At the event use exactly the singular functions $s_\sigma$ of Support X, (13.8). To make the algebraic response line unambiguous, its definition is

$$
\begin{aligned}
\mathcal D&=1731744020342106665,\\
A_s(z)&=13656112734222647296z^3-33583101098863014400z^2\\
 &\quad+20502976421172725312z-3401342974535580372,\\
B_s(z)&=-327746705621343535104z^3+916826043674607172160z^2\\
 &\quad-616757003572777087368z+31411654798932835643,\\
s_+(p)&=-3\{pA_s(\varrho_+)+B_s(\varrho_+)\}/\mathcal D.
\end{aligned}
\tag{7.6.1}
$$

This is a reused singular response line, not a new response classification. In particular it has the original full-world normalization and holds for negative p as well as positive p.

Proof of the same-base clause (7.3.4) and the zero-safe reconstruction. Set $r=\varrho_+$, $b=1/8$, $j=1/8+8r(1-r)$, $n=j+r$. The singular source has $T=9/8$ and $U=5/4$. Use the quantities of Support X, (13.9):

$$
\begin{aligned}
F_5&=jn+(n+5/4)\{(196/9)jn-15n-10j\},\\
F_6&=jn+(n+5/2)\{50jn-36n-20j\},\qquad F_0=84+24n.
\end{aligned}
\tag{7.6.2}
$$

Substitution of the single interpolant (7.1.1) into the actual fifth and sixth rows gives

$$
(p-24)jn=eF_5,\qquad (v-F_0)jn=eF_6.
\tag{7.6.3}
$$

At the graph point $p=\bar p(h_*)\ne24$, so $F_5\ne0$. Thus its own $e$ is exactly $(p-24)jn/F_5$, and its actual sixth response is $F_0+(p-24)F_6/F_5$. The two polynomial remainders in Support X, (13.11), are zero:

$$
\begin{aligned}
\operatorname{rem}(\mathcal D F_6+3A_sF_5,\Phi)&=0,\\
\operatorname{rem}(\mathcal D(F_0F_5-24F_6)+3B_sF_5,\Phi)&=0.
\end{aligned}
\tag{7.6.4}
$$

Evaluating these existing identities at the exact root and dividing only by the nonzero $\mathcal D F_5$ gives $\bar v(h_*)=s_+(\bar p(h_*))$. The other endpoint has exactly this same p and v by (7.3.2); the response line is therefore attained at the actual common base, rather than at a separately chosen singular source with unrelated responses.

There is also a zero-safe expression for the entire lift at a fixed source and fifth response. Namely, use the already established formula of Support X, (13.4)–(13.5), equivalently common-parent geometry, Lemma 12.2 and Theorem 12.3:

$$
\begin{aligned}
V&=U+n,\qquad A_5=1+V(4-15/j+20/T-10/n),\\
K_5&=96(b-1/8)V/T,\qquad Z=\Lambda^2+A_5^2>0,\\
e&=\frac{-(24/5)(b-1/8)B_{\mathrm{coef}}\Lambda
          +A_5(p-24-K_5)}{Z}.
\end{aligned}
\tag{7.6.5}
$$

At this singular point $K_5=\Lambda=0$, and (7.6.3) gives $A_5=F_5/(jn)\ne0$. Thus (7.6.5) reduces to $e=(p-24)/A_5$, with a positive denominator $Z=A_5^2$ in its displayed zero-safe form. Substituting this e and the exact singular source into (7.1.1) supplies its entire gain, and $d=24+e$ supplies its fixed drift. The gain uses the original clocks at every row, by (7.3.10). This is exactly the fixed-source fifth-response world of the cited uniqueness theorem. At no step at the event is there division by $\Lambda$ or the regular $D$, and the gain is not refitted after any action. This completes the proof of Theorem 7.3.1. ∎

### 7.7 Source interfaces, mathematical use and scope

The source-specific content of Theorem 7.3.1 is the connected finite extension of the second-J germ over $0<h\le1/250$, the bridge to the exact finite pair, and its actual singular-parent passage. The zero-safe parent and full-world converse are those of common-parent geometry, Theorem 2.1; the regular circuit, critical isolation, local germ and finite pair are those of Sections 6.2–6.7; the singular classification and affine response line are those of Support X, Section 13.2. They are interfaces used with their existing scopes. In particular the first negative-J family already classified in Support X, Section 14, supplies no new assertion here. The old exact $p_J$ is supplied by the all-response volume, Sections 24.2–24.3.

The finite arc places the original base curve $(\bar p(h),\bar v(h))$ in the unequal-ratio J incidence set throughout its stated interval. It also makes that actual base curve meet the existing singular response line while retaining two legal, distinct, equal-J worlds. These are consumers in the same-child problem: they replace the separate local and finite witnesses by one connected family with a common actual ancestor at each parameter. An equal-M witness in that same entire child would still have to satisfy the independent quantifiers (6.8.5); the selected J pair and its finite bounds impose no condition on arbitrary companions.

Support VII, Theorems 25.1–25.2 and Sections 28–30, already supply singleton inventories at both exact critical bases and M-injectivity on unspecified open base neighborhoods. Those entire-child results are reused; a further local M exclusion is not part of Theorem 7.3.1. Tube uniqueness here neither inventories $C(\bar p(h),\bar v(h))$ nor transfers that local M-injectivity to the full finite base curve. The theorem does not specify an independently selected equal-M pair, a global $D_J\cap D_M$ conclusion, a maximal connected component, continuation beyond $1/250$, or an earliest event among other companions. Its only event-count quantifier ranges over the two selected endpoints. No uniform inequality for their alternative M responses is asserted over the finite interval.

Fixed48, V(18.12)(i), rootQ, the common-tree obligations and the original full-domain eight/nine-read recovery question retain their original definitions. The changed common-base family is no resolution of those questions. In particular no source box, positive drift, gain-sign condition, nonvanishing sampled gain, simple-root hypothesis or full-degree hypothesis replaces the original W3 domain.

The literature correspondence is bounded to the methods used above: fixed-node interpolation in Berrut–Trefethen, the contraction principle in Banach, preconditioned interval enclosures in Krawczyk, and the analytic implicit-function theorem as in Lebl's stated theorem. Their classical content is reused, with the contraction and parameter-passage implications given explicitly here. The finite rational source circuit, its inequalities and its two attachments are repo-derived ordinary mathematics. Neither these citations nor the finite continuation imply a global priority or originality claim. The proof concerns the declared original acquisition model and its exact full-world relations.

## 追加锚（本行以下为增补区）

## 8. A closed entire-child M exclusion containing the finite second-J arc

### 8.1 Complete worlds and the quantitative statement

**Definition 8.1.1 (The rectangle and its entire children).** Retain the
complete worlds of Definition 7.1.1. Explicitly,

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad0\ne g\in\mathbb R[s],\quad\deg g\le3,
\quad d\in\mathbb R.
\tag{8.1.1}
$$

Let $Q_0=I$, $Q_i=E_iQ_{i-1}$, with the original actions
$(E_1,\ldots,E_6)=(J,M,J,M,M,M)$ and
$y_i=d+g(i)\operatorname{tr}(Q_iP)$. The entire child $C(p,v)$ consists
of all such worlds with

$$
(y_0,\ldots,y_6)=(0,24,147/5,24,18,p,v),\qquad
m(W)=d+g(7)\operatorname{tr}(MQ_6P).
\tag{8.1.2}
$$

The matrices $J,M$ are those of (6.1.1)–(6.1.3). Thus the initial read
counts, each atomic action is immediately read, and clock-seven $J$
and $M$ are alternative actions on this same history. No operation,
clock, source copy or observation is added here. Each world retains one
whole gain and one fixed drift; different worlds can have unrelated
drifts. All finite decimals in Section 8 denote exact rational numbers.
Set

$$
\begin{gathered}
\mathcal B=[-10.893,-10.890]\times[-8.155,-8.153],\\
p_c=-10.8915,\quad p_H=0.0015,\qquad
v_c=-8.154,\quad v_H=0.001.
\end{gathered}
\tag{8.1.3}
$$

**Theorem 8.1.2 (Closed-rectangle separation and whole-arc containment).**
For every $(p,v)\in\mathcal B$, the function
$m:C(p,v)\longrightarrow\mathbb R$ is injective. In particular equality
of the alternative $M$ readings forces equality of the complete worlds,
including their entire gain polynomials and fixed drifts.

For the very same graph $y(t)$ of Theorem 7.3.1 and its actual common
base, including the coalesced attachment at $h=0$,

$$
\begin{gathered}
-10.892041<\bar p(h)<-10.890360,\\
-8.154582<\bar v(h)<-8.153505,
\qquad0\le h\le1/250.
\end{gathered}
\tag{8.1.4}
$$

Consequently this entire finite base arc lies strictly inside
$\mathcal B$. For every $0<h\le1/250$ its child contains the distinct
$J$ pair of Theorem 7.3.1 but contains no distinct equal-$M$ pair at all.
This excludes (6.8.5) at every base of this arc, including its selected
singular passage. At $h=0$ only the attachment, not a distinct $J$ pair,
is asserted.

The ambient quantifiers in the theorem include every sign of the gain,
all lower degrees, sampled zeros, repeated roots, zero drift, singular
parent sources and unrelated unused companions. They do not impose the
positive-drift bounds of the selected family on an arbitrary child.

### 8.2 The all-world carrier and the forced response

Write $\mathscr R$ for exactly the carrier of
[Support VII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md),
(15.4)–(15.6), rather than a differently normalized parent eliminant.
The following finite polynomial definitions fix that normalization and
the additional polynomials used in the bounds. Put

$$
\begin{gathered}
D=x(x+1)(x+2),\qquad z_3=(24-d)(x+1)(x+2),\qquad z_4=(18-d)D,\\
z_5=(p-d)x(x+2),\qquad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\qquad
a_2=4z_3-6z_4+4z_5-z_6,\\
z_*=xa_1-D(24-d),\\
f=5dDa_2+a_0\bigl((294-10d)D-5a_2\bigr),\\
K=4a_0^2z_*^2+2a_0(dD-a_0)z_*a_1
 -(a_0+dD)\bigl(dD+(1-2x)a_0\bigr)a_1^2,\\
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480.
\end{gathered}
\tag{8.2.1}
$$

In the polynomial ring, write $f=A_fd^2+B_fd+C_f$ and
$K=\sum_{i=0}^4K_id^i$. Form the six-by-six Sylvester matrix whose
rows are the coefficients of $d^3f,d^2f,df,f,dK,K$, in the columns
$d^5,d^4,\ldots,1$. Then define $\mathscr R$ by

$$
\det\mathsf S=256D^8F_0^2\mathscr R.
\tag{8.2.2}
$$

This is exact polynomial division, not pointwise cancellation at
$F_0=0$. The quotient has integer coefficients, $512$ nonzero terms and
multidegree $(18,6,6)$ in $(x,p,v)$, with

$$
[x^0]\mathscr R=10^6(32p-5v-366)^2
 (120p^2-38pv-3360p+3v^2+522v+23112)^2.
\tag{8.2.3}
$$

Keep the polynomial drift identity of Support VII, (16.1)–(16.3):

$$
\begin{aligned}
\alpha={}&K_4(-B_f^3+2A_fB_fC_f)
 +K_3A_f(B_f^2-A_fC_f)-K_2A_f^2B_f+K_1A_f^3,\\
\zeta={}&K_4(-B_f^2C_f+A_fC_f^2)
 +K_3A_fB_fC_f-K_2A_f^2C_f+K_0A_f^3,\\
A={}&\alpha/(32D^3),\qquad Z=\zeta/(32D^3),\qquad Z_1=Z/F_0.
\end{aligned}
\tag{8.2.4}
$$

All three quotients in the last line are polynomials. Define further

$$
\begin{aligned}
B_n={}&-20(x+1)(x+2)+45D-36x(x+2)+10x(x+1),\\
B_1={}&\frac{-2A-(B_n+D)Z_1}{2D},\\
L_7={}&-24(x+1)(x+2)+72D-6p\,x(x+2)+4v\,x(x+1),\\
T_7={}&(x+1)(x+2)-4D+6x(x+2)-4x(x+1),\\
N={}&\frac{-ZD+(3+2x)(L_7A-T_7Z)}{D},\qquad
\Omega=N_xA-NA_x.
\end{aligned}
\tag{8.2.5}
$$

Here too $B_1,N$ are polynomial quotients with zero remainder. Thus
these definitions do not introduce divisions by the numerical value of
$F_0$ or $D$ when their coefficients are formed. For an explicit
coefficient construction, expand every product by finite convolution,
expand $\det\mathsf S$ as its $6!$ signed products, and perform the
indicated exact divisions over $\mathbb Q[x,p,v]$. The numbers of
nonzero terms of $(\alpha,\zeta,A,Z,Z_1,B_1,N,\Omega)$ are
$(280,405,220,315,190,190,334,1512)$, respectively.

The necessary, faithful all-world interface used below is Support VII,
Section 15 and Lemma 15.1. In that interface

$$
\begin{gathered}
x=(j+r)/U>0,\qquad j=b+r(1-r)/b,\qquad U=1+2b,\\
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H(s)=\sum_{i=3}^6h_i
 \prod_{\substack{3\le k\le6\\k\ne i}}\frac{s-k}{i-k},\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\quad
H_2=4h_3-6h_4+4h_5-h_6,\\
H_7=-h_3+4h_4-6h_5+4h_6,\\
B_0=294/5-2d-H_2,\quad C_0=d^2+B_0^2,\\
U=(-dH_0+B_0H_2)/C_0,\quad
b=(U-1)/2,\quad j=U(24-d)/H_1,\quad r=xU-j,\\
g=H/U,\qquad m=d+(3+2x)H_7.
\end{gathered}
\tag{8.2.6}
$$

At every actual off-$24$ world this interface gives
$D>0$, $d\ne24$, $H_1\ne0$, $C_0>0$, $U>1$,
$f=K=\mathscr R=0$ and $\alpha d+\zeta=0$.
It includes $d=0$, $F_0=0$, singular original sources and all degree
drops; the map from complete worlds to $(x,d)$ is injective. These are
reused results, not converses from a resultant root.

In particular, wherever $A\ne0$, an actual world has

$$
d=-Z/A,\qquad m=\mu(x;p,v):=N/A,\qquad
\mu_x=\Omega/A^2.
\tag{8.2.7}
$$

The extra source filter on a label where also $Z_1\ne0$ is

$$
b=B_1/Z_1.
\tag{8.2.8}
$$

To verify these new polynomial forms directly, expansion gives
$a_0=-2F_0+B_nd$ and $DH_7=L_7+T_7d$. Substituting $d=-Z/A$ in the
second identity gives (8.2.7). If $Z,Z_1\ne0$, then $d\ne0$ and the
actual equation $dU=-H_0$ gives

$$
U=\frac{-2F_0A-B_nZ}{DZ}
  =\frac{-2A-B_nZ_1}{DZ_1},\qquad
\frac{U-1}{2}=\frac{B_1}{Z_1}.
\tag{8.2.9}
$$

This establishes (8.2.8) only where it will be guarded below; no
nonzero-drift assumption is made on the central interval. The identity
$\alpha d+\zeta=0$ follows without dividing by $A_f$: polynomially,

$$
\begin{gathered}
A_f^3K-\alpha d-\zeta=fQ,\\
Q=K_4(A_f^2d^2-A_fB_fd+B_f^2-A_fC_f)
  +K_3A_f(A_fd-B_f)+K_2A_f^2.
\end{gathered}
\tag{8.2.10}
$$

Thus no assumption that the specialized quadratic retains its degree
enters the forced drift.

### 8.3 Finite rational enclosure definitions

**Definition 8.3.1 (Coefficient and interval enclosures).** For any of
the polynomials $P(x,p,v)$ above, define its translated coefficients by

$$
\begin{aligned}
P(c+X,p_c+P_0,v_c+V_0)
 &=\sum_{i,j,k}q_{ijk}^{(c)}X^iP_0^jV_0^k,\\
q_{ijk}^{(c)}
 &=\sum_{a\ge i,\,b\ge j,\,e\ge k}
 [x^ap^bv^e]P\binom ai\binom bj\binom ek
 c^{a-i}p_c^{b-j}v_c^{e-k},\\
s_c(P;\delta)
 &=\sum_{i+j+k>0}|q_{ijk}^{(c)}|\delta^ip_H^jv_H^k.
\end{aligned}
\tag{8.3.1}
$$

Zero powers, including $0^0$ in this finite coefficient formula, mean
one. For $\delta\ge0$, let

$$
\mathcal E_c(P;\delta)
=\mathcal O_{160}\bigl([q_{000}^{(c)}-s_c(P;\delta),
                       q_{000}^{(c)}+s_c(P;\delta)]\bigr),\qquad
\mathcal O_q([l,u])=
[2^{-q}\lfloor2^ql\rfloor,2^{-q}\lceil2^qu\rceil].
\tag{8.3.2}
$$

The coefficient sums in (8.3.1) are exact rational sums before this
last rounding. They enclose $P$ on
$[c-\delta,c+\delta]\times\mathcal B$, even for $\delta=0$.

For subsequent interval expressions use the ordinary endpoint rules,
then apply $\mathcal O_{160}$ after every scalar addition,
subtraction, multiplication and reciprocal; rational inputs are first
enclosed by this same rule. A product uses all four endpoint products.
A reciprocal is formed only for $0\notin[l,u]$, and is $[1/u,1/l]$
before outward rounding. Negation reverses endpoints. Powers mean
successive multiplication starting from one. Displayed sums and
products are left associated in their displayed order, and finite sums
start from zero in increasing index order. Thus all interval operations
are enclosing rational operations.

For a gap $[a,b]$ define $T_l(P_0,V_0)$ by the exact expansion

$$
(1+w)^{18}\mathscr R\!\left(\frac{a+bw}{1+w},
                   p_c+P_0,v_c+V_0\right)
 =\sum_{l=0}^{18}T_l(P_0,V_0)w^l,\qquad
T_l=\sum_{j,k}t_{ljk}P_0^jV_0^k.
\tag{8.3.3}
$$

For the final half-line $[a,\infty)$ instead expand
$\mathscr R(a+w,p_c+P_0,v_c+V_0)$ in $w$ to define these coefficients.
No rational function remains in (8.3.3). In either case set

$$
\theta_{a,b}=
\max_{0\le l\le18}
\frac{\sum_{j+k>0}|t_{ljk}|p_H^jv_H^k}{|t_{l00}|}.
\tag{8.3.4}
$$

The nonzero denominators in this definition are part of the following
coefficient comparisons.

**Lemma 8.3.2 (Exhaustive positive cover and legality filter).** The
coefficients of (8.3.3) satisfy this table: every $t_{l00}$ has the
indicated strict sign, and the final column is exactly
$\lceil10^6\theta_{a,b}\rceil$.

| $a$ | $b$ | Sign of all $t_{l00}$ | $\lceil10^6\theta_{a,b}\rceil$ |
|---:|---:|:---:|---:|
| $0$ | $0.31$ | $+$ | $590$ |
| $0.34$ | $0.48$ | $-$ | $421$ |
| $0.52$ | $1.07$ | $+$ | $1129$ |
| $1.11$ | $1.21$ | $-$ | $1886$ |
| $1.24$ | $1.295$ | $+$ | $18221$ |
| $1.32$ | $1.36$ | $-$ | $808191$ |
| $1.395$ | $2.13$ | $-$ | $742848$ |
| $2.18$ | $2.80$ | $+$ | $12509$ |
| $2.86$ | $\infty$ | $-$ | $14965$ |

Define

$$
\begin{aligned}
I_1&=[0.31,0.34],&I_2&=[0.48,0.52],&I_3&=[1.07,1.11],\\
I_4&=[1.21,1.24],&I_5&=[1.295,1.32],&I_6&=[2.13,2.18],\\
I_7&=[2.80,2.86],&&I_*=[1.36,1.395].
\end{aligned}
\tag{8.3.5}
$$

Every positive root of $\mathscr R(\cdot;p,v)$ over $\mathcal B$ lies
in their union. All actual worlds lie in $I_*$.

Here are complete finite bounds for the last assertion. Starting with
each $[a,b]=I_k$, repeat four times the following root-retaining
inclusion, with each new interval used in the next step:

$$
\begin{gathered}
c=(a+b)/2,\quad\delta=(b-a)/2,\quad
V=\mathcal E_c(\mathscr R;0),\quad
L=\mathcal E_c(\mathscr R_x;\delta),\\
[l,u]=[a,b]\cap\bigl(\mathcal O_{160}([c,c])-V/L\bigr),\qquad
[a,b]_{\mathrm{new}}=
[10^{-9}\lfloor10^9l\rfloor,10^{-9}\lceil10^9u\rceil].
\end{gathered}
\tag{8.3.6}
$$

All $28$ derivative intervals $L$ exclude zero. Writing their endpoints
as $L_-,L_+$, they satisfy

$$
\max\frac{L_+-L_-}{|L_++L_-|}<570877/10^6<1.
\tag{8.3.7}
$$

Every pair in the next table is the pair of integer endpoints of
$10^9[a,b]_{\mathrm{new}}$ after the indicated step.

| $k$ | Step 1 | Step 2 | Step 3 | Step 4 |
|---:|:---|:---|:---|:---|
| $1$ | $(326288597,328336555)$ | $(326892048,326919206)$ | $(326906144,326910357)$ | $(326906145,326910353)$ |
| $2$ | $(499726399,499864488)$ | $(499808288,499824244)$ | $(499808292,499824223)$ | $(499808292,499824223)$ |
| $3$ | $(1090257932,1090713981)$ | $(1090367550,1090414690)$ | $(1090368232,1090414432)$ | $(1090368232,1090414431)$ |
| $4$ | $(1226585675,1228656991)$ | $(1227237557,1227302251)$ | $(1227251578,1227293002)$ | $(1227251578,1227292995)$ |
| $5$ | $(1308630812,1309829217)$ | $(1308989261,1309089523)$ | $(1309004558,1309079111)$ | $(1309004558,1309079103)$ |
| $6$ | $(2155241979,2156493938)$ | $(2155354138,2155758090)$ | $(2155358123,2155757478)$ | $(2155358125,2155757459)$ |
| $7$ | $(2830771782,2834764461)$ | $(2831152307,2832052116)$ | $(2831191601,2832023839)$ | $(2831191783,2832023535)$ |

On each final interval, using its midpoint $c$ and radius $\delta$,

$$
\begin{gathered}
\sup\mathcal E_c(A;\delta)<-10^{13},\\
\inf\{|z|:z\in\mathcal E_c(Z;\delta)\}>10^{14},\qquad
\inf\{|z|:z\in\mathcal E_c(Z_1;\delta)\}>10^{10}.
\end{gathered}
\tag{8.3.8}
$$

In particular all three enclosures exclude zero. On the first final
interval evaluate $d=-\mathcal E_c(Z;\delta)/\mathcal E_c(A;\delta)$,
then the circuit (8.2.6), using the whole intervals for $x,p,v$. Its
bounds are

$$
-32<H_1<-28,\qquad216<C_0<223,\qquad7<r<8.
\tag{8.3.9}
$$

For the other six intervals the polynomial ratio
$\mathcal E_c(B_1;\delta)/\mathcal E_c(Z_1;\delta)$ is strictly inside
the corresponding open interval in this table.

| $k$ | Strict enclosure for the forced $b$ |
|---:|:---|
| $2$ | $(-7,-5)$ |
| $3$ | $(-0.09,-0.08)$ |
| $4$ | $(-0.45,-0.43)$ |
| $5$ | $(-0.60,-0.51)$ |
| $6$ | $(-0.16,-0.15)$ |
| $7$ | $(-0.27,-0.26)$ |

Proof of the finite comparisons and their implications. Equations
(8.2.1)–(8.2.5), convolution and the six-by-six determinant specify all
coefficients used here. For the gap comparison, first translate $p,v$
by the binomial sum (8.3.1). For each coefficient of $P_0^jV_0^k$,
replace each $x^i$ by $(a+bw)^i(1+w)^{18-i}$ and collect powers of $w$;
for the half-line replace it by $(a+w)^i$. This gives the signed
$t_{l00}$ and the nine rational maxima (8.3.4). Their ceilings are the
nine integers displayed above. All are below $10^6$, so throughout the
whole rectangle every coefficient $T_l$ retains that strict sign.
For $w\ge0$ the transformed polynomial cannot vanish. For a finite
gap its constant coefficient excludes $a$, and its leading coefficient,
which is $\mathscr R(b;p,v)$, excludes $b$. This proves the stated
positive-root cover, including the unbounded positive half-line.
There is no root-count or multiplicity inference.

For (8.3.6), the translated coefficient formula gives $V,L$ by finite
rational sums; the endpoint rules of Definition 8.3.1 give the four
successive integer pairs in each row. The $28$ strict unit comparisons
and their maximum ratio give (8.3.7). Evaluation of $A,Z,Z_1$ by the
same formula on the fourth-step pairs gives (8.3.8). Substituting these
intervals in the displayed order of (8.2.6) gives (8.3.9); thus every
division by $x,x+1,x+2,H_1,C_0,A$ used in this row is guarded.
For the last six rows form the ratio in (8.2.8) after its two polynomial
enclosures; (8.3.8) guards its denominator. These are finite rational
inequalities: after substituting (8.3.1), each floor or ceiling is
specified by its adjacent-integer inequalities, and clearing positive
integer denominators gives exactly the table comparisons. In particular
they do not require approximate choices of roots.

To see why the inclusions retain every root, fix its actual base. If
$x\in[a,b]$ and $\mathscr R(x;p,v)=0$, the real mean-value theorem gives
$x=c-\mathscr R(c;p,v)/\mathscr R_x(\xi;p,v)$ for some $\xi$ between
$c$ and $x$. The prescribed $L$ contains this derivative and excludes
zero. Hence $x$ remains in the intersection and in its outward-rounded
successor. Four such inclusions put any root originally in $I_k$ in
the corresponding final row, without asserting that it lifts.

For an actual world (8.3.8) forces $d=-Z/A$, with $d\ne0$ on these
seven rejected rows. Its necessary reconstruction in the first row has
$r>7$, contrary to $r<1$. In each other row (8.2.9) forces $b<0$,
contrary to $b>0$. Thus none of these rows contains an actual world.
Every actual positive label lies in $I_*$, as claimed. ∎

### 8.4 Separation on the full surviving interval

**Lemma 8.4.1 (Strict forced-M monotonicity).** On all of
$I_*\times\mathcal B$, one has $A\ne0$ and

$$
-33<\frac{\Omega}{A^2}<-16.
\tag{8.4.1}
$$

Proof. Partition $I_*$ into the $32$ closed cells

$$
J_i=\left[\frac{34}{25}+\frac{7i}{6400},
          \frac{34}{25}+\frac{7(i+1)}{6400}\right],
\quad c_i=\operatorname{mid}J_i,\quad
\delta_i=7/12800,\qquad0\le i<32.
\tag{8.4.2}
$$

These $c_i$ are used only in this lemma and are not the five-coordinate
tube centres of (7.2.3). Evaluate (8.3.1)–(8.3.2) for $A,\Omega$ at
each of these $32$ rational midpoints. The complete finite comparisons
are

$$
\begin{gathered}
\max_{0\le i<32}\sup\mathcal E_{c_i}(A;\delta_i)<-10^{13},\\
\bigcup_{i=0}^{31}
\frac{\mathcal E_{c_i}(\Omega;\delta_i)}
     {\mathcal E_{c_i}(A;\delta_i)^2}
\ \subseteq\
\frac{[-32935095741486,-16484504306425]}{10^{12}}
\ \subset(-33,-16).
\end{gathered}
\tag{8.4.3}
$$

Here the square and quotient are interval operations of Definition
8.3.1. The first comparison excludes zero before the reciprocal.
The second follows by substituting the binomial coefficient sums for
the $1512$-term polynomial $\Omega$ and the $220$-term polynomial $A$,
forming the endpoint products for the square and the guarded
reciprocal, and taking the minimum lower and maximum upper endpoints
over the finite range $0\le i<32$. This gives the displayed rational
outer endpoints. The enclosure property and the exact derivative in
(8.2.7) prove (8.4.1) on every cell and their shared boundaries. ∎

Proof of the rectangle assertion in Theorem 8.1.2. Fix any
$(p,v)\in\mathcal B$. It is off $24$. By the reused all-world carrier
necessity, every $W\in C(p,v)$ has $x>0$, $\mathscr R(x;p,v)=0$ and
$\alpha d+\zeta=0$. Lemma 8.3.2 puts all of these worlds in $I_*$.
There $A$ never vanishes, so their drifts and terminal responses are
exactly (8.2.7). At this fixed base the rational function $\mu$ is
differentiable on the entire interval $I_*$, including between any two
actual labels. Lemma 8.4.1 and the mean-value theorem make it strictly
decreasing there. Equal terminal readings therefore force equal $x$.
The same forced drift gives equal $d$. Finally the faithful reconstruction
(8.2.6) gives equal $U,b,j,r$ and the identical interpolant $H$, hence
the identical whole gain $g=H/U$. The complete worlds are equal.

The proof has not assumed equal drifts, regular sources, source
compactness or realizability of any particular resultant root. It has
not divided by a gain sample, a leading coefficient, a root difference,
$F_0$ at an actual point, or the original singular-parent factor. The
positive $D$ and the actual guards $H_1\ne0$, $C_0>0$, $U>1$ come from
the reused complete-world interface. Thus the rectangle assertion has
the whole domain of (8.1.1). ∎

### 8.5 Bounds on the actual published graph

**Definition 8.5.1 (Centred response bounds on the given tubes).** In
this subsection $c_i,X_i,T_i,t_i,\rho,\Delta$ are exactly those of
(7.2.2)–(7.2.3), with $0\le i<128$. In particular the centres use that
same seed, the same five $Q_{45}$-rounded Newton corrections per cell,
and the same ordering $y=(R,B,E,k,\ell)$; they are not independently
selected points on another branch. All centre definitions retain the
$240$-bit outward enclosure prescription of Section 7.2. The following
new response bounds use Definition 8.3.1's $160$-bit prescription.

For all source-circuit enclosures in this subsection, fix the following
expression convention. Use the first expression
$B_{\mathrm{coef}}=6/T-2/U$ in (7.1.1), not its algebraically equal
single quotient. Every displayed rational constant, such as $24/5$,
$27/5$ or $1/8$, is one rational input. Other quotients mean multiplication
of the numerator by the reciprocal of the denominator. Evaluate the
named quantities $j,n,T,U$ by (6.1.4), then the displayed expressions
(7.1.1)–(7.1.5), with powers before products and products before sums;
within either level use the displayed left-to-right order. No terms
are collected, cancelled or replaced by an algebraically equivalent
expression. Scalar inputs to the two-coefficient algebra are $(u,0)$.
In its product use exactly
$(AC+(tB)D,AD+BC)$; in its inverse form
$L=(A A)-t(B B)$, then $(A L^{-1},(-B)L^{-1})$.
All operations in these scalar expressions are rounded outward at the
specified precision. Negation reverses endpoints exactly.

Differentiate each scalar operation by (7.2.4) in its displayed order.
Thus the product derivative is $\dot u\,v+u\,\dot v$, and the reciprocal
derivative is $((-\dot u)u^{-1})u^{-1}$, with the same enclosed
reciprocal at both occurrences. Differentiate the explicit factor $t$
in the pair operations as well. Matrix products use increasing-index
sums starting at zero. In Gauss–Jordan elimination retain the old pivot
and the old elimination factor for each entire row operation; multiply
by the enclosed pivot reciprocal to normalize every row entry.
These conventions also apply at $240$ bits when determining the exact
rounded centres and preconditioners of (7.2.3). Norm sums formed from
absolute interval endpoints and rational weights, and the final scalar
quotient in $D_i$, are exact rational operations. Lemma 8.5.3 gives
sufficient continuation bounds with this convention, replacing the
tight upper-bound column of the first table in Lemma 7.2.2 wherever
that table is used here.

Evaluate precisely the rational circuit (7.1.1)–(7.1.5) in the algebra
$\epsilon^2=t$, with $r=R+\epsilon$, $b=B+k\epsilon$,
$e=E+\ell\epsilon$. Set

$$
f_p(y,t)=p_{\mathrm{av}}(y,t),\qquad
f_v(y,t)=v_{\mathrm{av}}(y,t),\qquad
J_i=D_yG(c_i,t_i).
\tag{8.5.1}
$$

The exact rational row and scalar for either $f\in\{f_p,f_v\}$ are

$$
u_{f,i}=D_yf(c_i,t_i)J_i^{-1},\qquad
b_{f,i}=f(c_i,t_i)-u_{f,i}G(c_i,t_i).
\tag{8.5.2}
$$

Every $J_i$ is invertible by the ordered pivot bounds of Lemma 8.5.2;
alternatively the sufficient contraction bounds of Lemma 8.5.3 and
(7.3.5)–(7.3.8) imply invertibility also at the tube centre.

Here are finite enclosure definitions for these rational quantities and
the needed derivatives. Differentiate the six-variable scalar circuit
using (7.2.4), including the derivative of $t$ in pair multiplication
and in its inverse. Enclose the point values of $G,D_yG,f,D_yf$ at
$(c_i,t_i)$ by the $160$-bit endpoint rules. Invert the interval point
matrix enclosing $J_i$ by Gauss–Jordan elimination on its augmentation
by the identity. Use pivots $1,\ldots,5$ in order, normalize the entire
pivot row, then eliminate that column in every other row in increasing
row order; use the old elimination factor for the entire row update.
No row interchange or replacement of an interval pivot by an exact
one is made. Let $\mathcal C_i$ be the resulting interval inverse.
For interval finite sums use increasing indices starting from zero.
Let $\mathcal U_{f,i}$ be the interval row obtained from the point
$D_yf$ enclosure times $\mathcal C_i$, and let
$\mathcal B_{f,i}$ be the point $f$ enclosure minus that row times the
point $G$ enclosure. They contain $u_{f,i}$ and $b_{f,i}$.

Write $[\partial_jf]_{X_i,T_i}$ and
$[\partial_jG_k]_{X_i,T_i}$ for the derivative enclosures on the
whole product box, in variable order $(R,B,E,k,\ell,t)$. Define

$$
\begin{aligned}
\mathcal D_{f,i,j}
 &=[\partial_jf]_{X_i,T_i}
   -\sum_{k=1}^5(\mathcal U_{f,i})_k
                    [\partial_jG_k]_{X_i,T_i},\\
\eta_{f,i}
 &=\sum_{j=1}^5\rho_j|\mathcal D_{f,i,j}|_{\sup}
       +\Delta|\mathcal D_{f,i,6}|_{\sup},\\
\mathcal V_{f,i}
 &=\mathcal B_{f,i}
      +\mathcal O_{160}([-\eta_{f,i},\eta_{f,i}]).
\end{aligned}
\tag{8.5.3}
$$

The sum defining $\eta$ is an exact rational sum of the interval
absolute endpoints. In differentiating $f-u_{f,i}G$, the row $u_{f,i}$
is fixed at the centre, so its derivatives are not included.

**Lemma 8.5.2 (The 128 whole-tube response comparisons).** All interval
inverses in Definition 8.5.1 are defined. For each pivot position the
absolute values of all its interval endpoints over the $128$ final
point matrices lie strictly between the indicated integers, with the
whole pivot interval excluding zero:

| Pivot position | Strict lower bound for its absolute value | Strict upper bound |
|---:|---:|---:|
| $1$ | $292$ | $293$ |
| $2$ | $350$ | $351$ |
| $3$ | $16$ | $17$ |
| $4$ | $407$ | $408$ |
| $5$ | $26$ | $27$ |

For every $0\le i<128$, the intervals of (8.5.3) obey

$$
\begin{aligned}
\bigcup_i\mathcal V_{f_p,i}
 &\subseteq[-10892040442289,-10890360243799]/10^{12}
 \subset(-10.892041,-10.890360),\\
\bigcup_i\mathcal V_{f_v,i}
 &\subseteq[-8154581108770,-8153505324970]/10^{12}
 \subset(-8.154582,-8.153505).
\end{aligned}
\tag{8.5.4}
$$

Proof. The finite parameter range is the original $128$ cells of
(7.2.3). Obtain their exact rational centres from that recurrence.
The outward $240$-bit evaluation of each of its five corrections puts
both endpoints of each updated coordinate in the same $Q_{45}$
rounding cell, so it fixes exactly the stated rational centre. For the
new bounds, use the point derivatives at those centres and $t_i$,
perform the five ordered interval pivots just defined, and apply
(8.5.3) on $X_i\times T_i$. The minima and maxima of the five pivot
absolute endpoints give the integer bounds in the table. The minimum
lower and maximum upper response endpoints, rounded outward to
multiples of $10^{-12}$, give (8.5.4). These instructions involve only
the displayed rational circuit, the six derivative rules and finite
integer comparisons; in particular they evaluate all $128$ cells,
not just their end cells.

All source denominators are guarded before these evaluations.
The source bounds (7.2.7), with the sufficient continuation bounds of
Lemma 8.5.3, apply on every $X_i\times T_i$:
at both scalar evaluations $\epsilon=\pm\sqrt t$, one has
$0<r<1$, $b>0$, and $j,n,T,U>0$. In the two-coefficient algebra the
denominator of an inverse $(A,B)^{-1}$ is $A^2-tB^2$, the product of
those two scalar values. For $b,j,n,T,U$ these products are positive,
and their outward intervals exclude zero. The remaining new inverse
operations are the five point-matrix pivots; their interval bounds
above exclude zero. Fixed interpolation constants are nonzero.
Consequently the differentiated circuit has no unguarded inverse.
No division by $h$, $\Lambda$, a drift, a gain sample, a leading gain
coefficient or a gain-root difference occurs. ∎

Proof of the graph assertion in Theorem 8.1.2. The sufficient bounds of
Lemma 8.5.3 justify the contraction and seam implications of Section 7.3
for the same tubes and graph. For $t\in T_i$ that graph satisfies
$y(t)\in X_i$ and $G(y(t),t)=0$. Put
$F=f-u_{f,i}G$ for either response $f$. At the centre,
$F(c_i,t_i)=b_{f,i}$, while at that exact graph point
$F(y(t),t)=f(y(t),t)$. Integrate the derivative of $F$ along the straight
segment in the convex product box from $(c_i,t_i)$ to $(y(t),t)$.
The five coordinate displacements are bounded by $\rho_j$, and the
parameter displacement by $\Delta$. The derivative enclosures in
(8.5.3) therefore imply

$$
|f(y(t),t)-b_{f,i}|\le\eta_{f,i},\qquad
f(y(t),t)\in\mathcal V_{f,i}.
\tag{8.5.5}
$$

At a zero of $G$, $p_{\mathrm{sec}}=v_{\mathrm{sec}}=0$, so its
$p_{\mathrm{av}},v_{\mathrm{av}}$ are exactly the two endpoints'
common actual responses. This also defines their continuous common
base at $t=0$. Equation (8.5.4) now gives (8.1.4). Since $t=h^2$ maps
$[0,1/250]$ onto $[0,1/62500]$, the bound covers the entire published
parameter interval, including seams and both attachments. The scalar
source denominators stay positive at the singular passage, so the
argument applies there without a chart change. ∎

**Lemma 8.5.3 (Replacement continuation bounds on the original tubes).**
Use the $240$-bit source-circuit convention of Definition 8.5.1 on the
same centres, preconditioners, boxes and parameter cells of (7.2.3).
Write $q_i^\sharp,\beta_i^\sharp,D_i^\sharp,\widetilde q_i^\sharp$ for
the resulting rational bounds defined by (7.2.5)–(7.2.6). Then

| Quantity | Rational upper bound | Sufficient strict bound |
|---|---:|---:|
| $\max_i q_i^\sharp$ | $440377709788/10^{12}$ | $441/1000$ |
| $\max_i\beta_i^\sharp$ | $263610681681/10^{12}$ | $264/1000$ |
| $\max_i\widetilde q_i^\sharp$ | $238818207545/10^{12}$ | $239/1000$ |
| $\max_i\rho_BD_i^\sharp$ | $2475331406433/10^{12}$ | $5/2$ |
| $\max_i\rho_kD_i^\sharp$ | $24753314064322/10^{12}$ | $25$ |

All source and matrix inverses in these bounds are defined. In
particular $q_i^\sharp+\beta_i^\sharp<141/200<1$ on every cell.
The first table of Lemma 7.2.2 has smaller tight upper bounds for
$\beta_i$, $\rho_BD_i$ and $\rho_kD_i$ that are not bounds for this
expression convention. In fact its last cell satisfies

$$
\begin{aligned}
\frac{263610681680245}{10^{15}}
 &<\beta_{127}^\sharp<
 \frac{263610681680246}{10^{15}},\\
\frac{2475331406432184}{10^{15}}
 &<\rho_BD_{127}^\sharp<
 \frac{2475331406432185}{10^{15}},\qquad
\rho_kD_{127}^\sharp=10\rho_BD_{127}^\sharp.
\end{aligned}
\tag{8.5.6}
$$

The table in this lemma replaces that earlier tight upper-bound column
for the uses in Section 8. Its sufficient strict bounds preserve the
same whole-interval graph, the attachments and the selected singular
passage of Theorem 7.3.1.

Proof. Starting at the exact seed (7.2.2), enclose each of the five
successive Newton corrections per cell at $240$ bits, with the ordered
matrix inverse of Definition 8.5.1. Both endpoints of every updated
coordinate give the same integer under (7.2.1). The same is true for
every entry of the rounded inverse defining $C_i$. Thus these finite
comparisons determine exactly the original $640$ rounded corrections
and all $128$ preconditioners, rather than alternate roots or centres.

For each of the $128$ product boxes evaluate $D_yG,G_t$ by the stated
scalar operations and derivative rules. Evaluate $G(c_i,t_i)$ and
$G_t(c_i,T_i)$ separately for the residual bound. Multiply each of
these enclosures by the fixed rational $C_i$, take absolute endpoints,
and form the exact weighted row sums of (7.2.5). The reciprocal in
$D_i^\sharp$ is formed only after $q_i^\sharp<1$ is established.
For each of the $127$ seams form the rational midpoint and enlarged
radii (7.2.6), and repeat its weighted derivative comparison with
$C_i$. With componentwise interval endpoints and increasing-index
matrix sums, the five maxima, multiplied by $10^{15}$, lie strictly
between the respective integer pairs

$$
\begin{gathered}
(440377709787541,440377709787542),\qquad
(263610681680245,263610681680246),\\
(238818207544966,238818207544967),\qquad
(2475331406432184,2475331406432185),\\
(24753314064321844,24753314064321845).
\end{gathered}
\tag{8.5.7}
$$

These are finite rational comparisons: interval products use the four
endpoint products, each dyadic rounding is characterized by adjacent
integers, and the norm sums and positive scalar quotient are exact.
They give the displayed upper-bound table by outward rounding to
multiples of $10^{-12}$. The same computation at $i=127$ gives
(8.5.6), whose first two lower endpoints strictly exceed the earlier
claimed bounds $263610622981/10^{12}$ and $247533043797/10^{11}$.
Since $\rho_k=10\rho_B$, the earlier third bound fails as well.
All source-pair reciprocal denominators are positive on the enclosed
boxes; all matrix pivots exclude zero before normalization.

For applicability, the contraction proof (7.3.5)–(7.3.7) uses only
$q<1$ and $q+\beta<1$, and the seam argument (7.3.9) uses only
$\widetilde q<1$. The new bounds supply these inequalities on every
original tube and every seam. Thus they give a unique zero in each
$X_i$ at each $t\in T_i$, and the neighboring zeros coincide on every
seam by the same convex-box argument. The real zero equations and the
exact rational recurrence (7.2.3) are unchanged, so this is the same
graph, including $t=0$. Its Jacobian is invertible throughout the
product boxes by the same Neumann-series argument, and its derivative
bounds remain $|B_t|<5/2$, $|k_t|<25$. Therefore the attachment
identifications of Section 7.4 and the crossing argument of Section 7.5
retain their hypotheses, using (7.2.7) for the same source bounds and
their stated exact identities and fixed-parameter inclusions. No new
source restriction or parameter interval is introduced. ∎

### 8.6 The independent-pair consequence and mathematical scope

**Corollary 8.6.1 (No independent M pair along the finite J arc).** For
each $0<h\le1/250$, the literal same-child independent relation
(6.8.5) has no solution at
$(p,v)=(\bar p(h),\bar v(h))$, irrespective of cross-pair overlap or
of the common terminal values assigned separately to the two pairs.

Proof. Theorem 7.3.1 supplies its two distinct legal $J$ endpoints in
that entire child, each with its own whole gain, fixed drift and the
original common acquired history. Equations (8.1.4) put this same
actual base strictly in $\mathcal B$. The rectangle assertion of
Theorem 8.1.2 excludes every distinct equal-$M$ pair in that entire
child, including pairs selected independently of the supplied $J$
endpoints. The two pairs required in (6.8.5) therefore cannot coexist
there. No endpoints at different parameters or different bases have
been combined. ∎

The source-specific content is the explicit closed rectangle,
exhaustive legality filter and forced-M separation, together with
containment of the whole previously constructed finite graph. Support
VII, Theorem 25.2 and Sections 28–30, already give unspecified open
neighborhoods of M-injectivity; they do not specify (8.1.3) or contain
the whole finite arc by a stated radius. Theorem 7.3.1 supplies that
arc, its local-germ and finite-pair attachments, and its singular
crossing. Their existence and attachment proofs are reused, not
replaced by a new choice of graph. Tube uniqueness serves only to
identify that supplied graph; the entire-child inventory reduction
comes instead from Support VII's all-world carrier and faithful
reconstruction. Support, Corollary 18.2, already excludes chosen-M
singular endpoints in the original joint relation, but no regular-only
restriction is needed for the stronger rectangle theorem here.

The fixed-node interpolation in (8.2.6) is the classical formula of
J.-P. Berrut and L. N. Trefethen, *Barycentric Lagrange Interpolation*,
SIAM Review 46, 501–517, §2,
[doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).
The fixed Sylvester determinant is the classical resultant construction;
see S. Basu, R. Pollack and M.-F. Roy, *Algorithms in Real Algebraic
Geometry*, second edition, Chapter 8,
[doi:10.1007/3-540-33099-2](https://doi.org/10.1007/3-540-33099-2).
Their mathematical content is reused. The root-retaining inclusion and
the centred response estimate follow from the ordinary real mean-value
formula as shown above; the endpoint enclosure property follows by
induction on the displayed rational operations. No new general
interpolation, resultant or interval theorem is asserted. The finite
quantitative conclusions of Section 8 are repo-derived; they make no
worldwide priority claim.

This exclusion is confined to (8.1.3) and the entire stated finite XI7
arc. The all-real independent J/M question outside that rectangle,
fixed48 V(18.12)(i), rootQ, the common-tree/ancestor obligations and the
original full-domain eight/nine-read recovery problem remain open.
In particular a changed actual parent response has not resolved the
fixed48 problem, and no selected-source bounds have replaced the
original world domain.

## 追加锚（本行以下为增补区）

## 9. Literal relative indices and a finite original-H outer locus

**Definition 9.1 (Fixed objects and primitive conventions).** Write S, IX
and X for [Support](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md),
[Support IX](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IX.md) and
[Support X](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md). The integer
polynomials $D,a_i,f,K,F_0,\alpha,\beta,R$ are exactly IX, (4.1),
(4.3)–(4.7), with $K=4k$ and

$$
\operatorname{Res}_d(f,K)=256D^8F_0^2R,
\qquad \rho=[x^{18}]R.
\tag{9.1}
$$

In $B=\mathbb Q(p,v)[x]/(R/\rho)$ use the coefficient basis
$1,x,\ldots,x^{17}$. Put $\delta=-\beta/\alpha$ and use the *robust*
functions of S, Theorem 4.3:

$$
\begin{gathered}
H_i=a_i(x,\delta)/D\quad(i=0,1,2,7),\qquad
B_0=294/5-2\delta-H_2,\\
C_0=\delta^2+B_0^2,\qquad N_0=-\delta H_0+B_0H_2,\\
\tau_M=\delta+(2x+3)H_7,\\
\tau_J=\delta+
 \left(4x+\frac12+\frac{C_0}{2N_0}
                    -\frac{2(24-\delta)}{H_1}\right)H_7,\\
\chi_E(z)=\det(zI-M(\tau_E)),\qquad
\iota_E=\det[1,\tau_E,\ldots,\tau_E^{17}].
\end{gathered}
\tag{9.2}
$$

Here $M$ is multiplication in $B$, and the determinant columns in
$\iota_E$ are coefficient vectors. The symbol $\iota$ avoids the
unrelated overlap index $\kappa$ of Section 1. The symbols $C_0,N_0$
are quotient-algebra elements; $N_J,N_M$ below are scalar polynomials.

For an integer polynomial $A\ne0$, let $\operatorname{pp}_+(A)$ mean
division by its positive integer coefficient content, followed by the sign
which makes its lexicographic leading coefficient positive. In scalar
polynomials the order is $p>v$. For a rational function, first cancel its
polynomial numerator-denominator gcd over $\mathbb Q[p,v]$, then clear
rational scalar denominators, and take $\operatorname{pp}_+$ separately
on numerator and denominator. A rational scalar multiplying the resulting
fraction is retained separately. Let $N_E,D_E^{\rm ind}$ be these
primitive numerator and denominator of $\iota_E$.
Thus $N_E$ is literally the polynomial in S, Theorem 4.3.

Let $E_0$ be *that same* theorem's primitive squarefree product: $\rho$,
$\operatorname{Disc}_x(R)$, both sides of the five reduced norms of
$\alpha,D,H_1,C_0,N_0$, all its listed coefficient denominators, and the
two power-determinant denominators. Define

$$
H=(p-24)E_0,\qquad \rho_0=\operatorname{pp}_+(\rho).
\tag{9.3}
$$

In particular no factor $d,H_0,F_0,\beta$, terminal coordinate, or gain
coefficient is added to this inventory. Total degree without a subscript
means degree in the indicated parameter variables, not degree in $x$.

**Theorem 9.2 (Literal M normalization and finite joint outer locus).**
There are uniquely determined primitive positive polynomials
$C_{121},V_{69}\in\mathbb Z[p,v]$, of total degrees $121,69$, for which

$$
N_M=\rho_0^{17}C_{121},\qquad D_M^{\rm ind}=V_{69}.
\tag{9.4}
$$

These are equalities with the primitive conventions in Definition 9.1,
not replacements up to multiplication by factors of $H$. Furthermore

$$
\gcd(C_{121},N_J)=\gcd(C_{121},H)=1
\quad\hbox{in }\mathbb Q[p,v].
\tag{9.5}
$$

Consequently the following set is finite and may be empty:

$$
\begin{aligned}
Z_H
&=\{(p,v)\in\mathbb C^2:H(p,v)\ne0,\ N_J(p,v)=N_M(p,v)=0\}\\
&=\{(p,v)\in\mathbb C^2:H(p,v)\ne0,\
                         N_J(p,v)=C_{121}(p,v)=0\}.
\end{aligned}
\tag{9.6}
$$

Every four-world configuration in (6.8.5), with its two independently
chosen distinct equal-$J$ and equal-$M$ pairs in the same entire
$C(p,v)$, satisfies either $H(p,v)=0$ or $(p,v)\in Z_H$.
This applies to every overlap stratum of Sections 1–3 and to independently
chosen $m_0,m_1,m$. Proofs of (9.4)–(9.6) are given in Sections 10–14.

## 10. A compact polynomial for the literal M response

**Definition 10.1 (Integer terminal resultant circuit).** Use $z$ for a
formal terminal $M$ value and write $a_7=A_7+B_7d$, where

$$
\begin{aligned}
A_7&=72x^3+(192-6p+4v)x^2+(72-12p+4v)x-48,\\
B_7&=-4x^3-9x^2+3x+2,\\
q&=D+(2x+3)B_7=-8x^4-29x^3-18x^2+15x+6,\\
t&=zD-(2x+3)A_7.
\end{aligned}
\tag{10.1}
$$

For $A=\sum_{i=0}^n A_id^i$ define its denominator-cleared substitution
$A[t:q]=\sum_{i=0}^n A_it^iq^{n-i}$, retaining its displayed generic
$d$-degree. Set

$$
\begin{gathered}
f_M=\frac{f[t:q]}{2D^2},\qquad K_M=\frac{K[t:q]}{4D^4},\\
Q=\frac{\operatorname{Res}_x(q,t)}{1152},\qquad
L=\frac{\operatorname{Res}_x(F_0,t)}{2592pv},\\
P_M=\frac{\operatorname{Res}_x(f_M,K_M)}{82944Q^8L^2}.
\end{gathered}
\tag{10.2}
$$

Every quotient here is an exact integer polynomial quotient. No content
or sign adjustment is made to $P_M$. Resultants have their displayed
operand order and generic degrees. They use the convention
$\operatorname{Res}_x(A,B)=a_n^{\deg B}\prod_{A(\xi)=0}B(\xi)$.

**Lemma 10.2 (Exact quotient and characteristic-polynomial identification).**
The polynomial $P_M$ is primitive, of total degree $18$ in $(p,v,z)$,
with $\deg_zP_M=18$ and constant leading coefficient

$$
c=[z^{18}]P_M=33917016093258200081122929199218750000000.
\tag{10.3}
$$

It satisfies $P_M=c\chi_M$ in $\mathbb Q(p,v)[z]$.

Proof. The following finite coefficient identities also specify the
polynomial quotient without an expanded array. The arithmetic convention
for regenerating all the finite identities in this chapter is as follows.
An integer polynomial is its finite monomial-to-coefficient map. Addition,
multiplication and differentiation use coefficient addition, convolution
and the exponent rule. Exact division means leading-monomial division in
lexicographic order $d>x>p>v>z$, with zero remainder; the quotient is
checked by multiplication. Coefficients in a selected variable are
collected before each resultant. For degrees $n,m$, form the Sylvester
matrix from the descending coefficient rows of $A,xA,\ldots,x^{m-1}A$
and $B,xB,\ldots,x^{n-1}B$, ordered to give the above product convention.
Its determinant, or its fraction-free elimination, gives the resultant.
For elimination one may choose the first nonzero pivot in row order,
exchange rows with the corresponding sign, and update a trailing entry
by $(a_{kk}a_{ij}-a_{ik}a_{kj})/a_{k-1,k-1}$, initially with previous
pivot $1$. Each such division is exact. This is the usual Bareiss
calculation of the same determinant. Thus these instructions involve
only finite integer arithmetic; no numerical root or parameter sample
occurs.

Starting with IX, (4.1), (4.3)–(4.7), and (10.1), the divisions and
multiplications in (10.2) give the following inventories:

| Polynomial or identity | Exact result |
| --- | --- |
| $f[t:q]-2D^2f_M$ | $0$; $\deg_x f_M=7$, $74$ monomials |
| $K[t:q]-4D^4K_M$ | $0$; $\deg_x K_M=14$, $525$ monomials |
| $\operatorname{Res}_x(q,t)-1152Q$ | $0$; $Q$ primitive, $35$ monomials, total degree $4$, $z$-degree $4$ |
| $\operatorname{Res}_x(F_0,t)-2592pvL$ | $0$; $L$ primitive, $20$ monomials, total degree $3$, $z$-degree $3$ |
| $\operatorname{Res}_x(f_M,K_M)$ | $32509$ monomials, total degree $56$ |
| $\operatorname{Res}_x(f_M,K_M)-82944Q^8L^2P_M$ | $0$ |
| $P_M$ | content $1$, $1330$ monomials, coordinate degrees $(p,v,z)=(18,18,18)$; (10.3) |

For clarity, the last row is obtained by exact division by the *whole*
displayed divisor, not by selecting a factor of a numerical resultant.
The same monomial rules, including the specified divisions, determine
every coefficient and every zero residual in this table.

At the generic source point, IX, Sections 6–7, identify $B$ with the
original source field and make the actual $\tau_M$ primitive of degree
$18$. The terminal equation gives $t=q\delta$ there. Thus the homogeneous
substitutions defining $f_M,K_M$ vanish at $z=\tau_M$ without dividing
by $q$. Their resultant identity yields

$$
Q(\tau_M)^8L(\tau_M)^2P_M(\tau_M)=0.
\tag{10.4}
$$

A nonzero polynomial of terminal degree $4$ or $3$ cannot annihilate an
element of degree $18$. Hence neither of the first two factors vanishes
in this field, and $P_M(\tau_M)=0$. Comparing degrees and the leading
coefficient proves $P_M=c\chi_M$. This is a generic function-field
identity. Actual-world evaluation is through the robust regular functions
and S, Lemma 9.9; (10.4) does not remove the sets $q=0,Q=0,L=0$ or
$F_0=0$ from the original domain. ∎

## 11. Characteristic-zero degree and repeated-root bounds

**Definition 11.1 (The common degree-five divisor).** Put

$$
\begin{aligned}
T_5={}&(p-24)(55p-28v-1572)(58p-23v-1350)Q_2,\\
Q_2={}&120p^2-38pv-3360p+3v^2+522v+23112,\\
E={}&\operatorname{Disc}_x(R),\qquad F=\operatorname{Disc}_z(P_M).
\end{aligned}
\tag{11.1}
$$

$T_5$ is already primitive with positive lexicographic leading coefficient.

**Lemma 11.2 (Small identities and discriminant divisors).** Over
$\mathbb Q[p,v]$, $T_5$ is squarefree and

$$
T_5^2\mid E,\qquad T_5^2\mid F.
\tag{11.2}
$$

Proof. Here are the finite coefficient substitutions needed for this
assertion. A rational substitution is evaluated by multiplying by the
indicated constant or polynomial denominator to the degree of the
substituted variable, and then using convolution. Zero means the resulting
polynomial is identically zero, not a value at one point.

| Height-one factor | Carrier root $x_*$ | Terminal root $z_*$ |
| --- | --- | --- |
| $p-24$ | $(v-84)/30$ | $(32v-1128)/5$ |
| $55p-28v-1572$ | $-(v+42)/33$ | $(184v-60)/55$ |
| $58p-23v-1350$ | $(4v+144)/(v-138)$ | $(381v-1770)/116$ |

For each row substitute its $p$ as a rational affine function of $v$.
Direct application of the monomial rules of Lemma 10.2 gives

$$
R(x_*)=R_x(x_*)=R_p(x_*)=0,\qquad
P_M(z_*)=(P_M)_z(z_*)=(P_M)_p(z_*)=0.
\tag{11.3}
$$

The specializations of $R_{xx}(x_*),\rho,(P_M)_{zz}(z_*)$ are nonzero
polynomials. Equivalently, the terminal linear polynomials
$32v-5z-1128$, $184v-55z-60$, $381v-116z-1770$ divide the specialized
$P_M$ twice and its transverse $p$ derivative once. These statements can
be regenerated by ordinary univariate polynomial division after the
constant denominator clearing just specified.

For the quadratic row use $x_*=0$ and
$z_*=(1824-135p+54v)/10$. The complete division tests are

$$
\begin{gathered}
Q_2^2\mid R(0),\qquad Q_2^3\nmid R(0),\qquad Q_2\mid R_x(0),\\
R_{xx}(0)\not\equiv0\pmod{Q_2},\qquad
\rho\not\equiv0\pmod{Q_2},\\
Q_2^2\mid 10^{18}P_M(z_*),\qquad
Q_2\mid10^{17}(P_M)_z(z_*),\\
10^{16}(P_M)_{zz}(z_*)\not\equiv0\pmod{Q_2}.
\end{gathered}
\tag{11.4}
$$

For example, the last two divisible quantities have quotients of total
degrees $14,15$ and respectively $120,136$ monomials in the order
$10^{18}P_M(z_*)/Q_2^2$, $10^{17}(P_M)_z(z_*)/Q_2$.
Equations (11.3)–(11.4) are finite exact arithmetic with the explicitly
fixed $R,P_M$; division in $p$ over $\mathbb Q[v]$ gives the displayed
remainders. The leading coefficients of the divisors are constants.

The three linear factors are distinct and none divides $Q_2$.
Moreover

$$
\operatorname{Disc}_p(Q_2)=4(v^2+1200v+48960).
\tag{11.5}
$$

The polynomial in parentheses is coprime to its derivative, so it has
simple roots and is not a square in $\mathbb Q(v)$. Thus $Q_2$ is
irreducible over $\mathbb Q[p,v]$. These facts prove squarefreeness of
$T_5$.

At the height-one local ring of a factor $T$ of $T_5$, translate the
displayed carrier root to $0$. The constant coefficient has valuation at
least $2$, the linear coefficient at least $1$, and the quadratic and
leading coefficients are units. For the linear rows, the constant
coefficient assertion follows from its value and transverse derivative in
(11.3); for $Q_2$ it is the first division in (11.4). The same statements
hold for $P_M$ with its displayed terminal root. The denominators of the
root translations are units at this generic point, including $v-138$
in the third carrier row.

After completion and an unramified residue-field extension, the reduced
polynomial has a factor $y^2$ coprime to its remaining factor, since the
quadratic coefficient is a unit. Hensel factorization gives a monic
quadratic $y^2+by+a$ times that remaining factor. Comparing constant
and linear coefficients gives $a\in(T^2)$ and $b\in(T)$.
Its discriminant $b^2-4a$ is in $(T^2)$. The discriminant of the whole
polynomial is that discriminant times the remaining discriminant and
the square of a resultant, with unit leading-coefficient corrections;
these other factors have nonnegative valuation. Consequently $T^2$
divides each whole discriminant. Multiplying the four coprime factors
proves (11.2). These are divisor calculations, not deletions of any
exceptional curve. ∎

**Lemma 11.3 (Carrier degree at most 199).** The total parameter degree
of $E$ is at most $199$.

Proof. Put $R_i=[x^i]R$ and use $[A]_j$ for the homogeneous degree-$j$
part of a parameter polynomial. Coefficient collection from (9.1) gives

$$
\deg R_i=6\ (0\le i\le16),\qquad \deg R_{17}=5,
\qquad\deg R_{18}=4.
\tag{11.6}
$$

The following small homogeneous identities specify the cancellation at
infinity. Set

$$
\begin{gathered}
A=[R_{18}]_4,\quad B_\infty=[R_{17}]_5,\quad C=[R_{16}]_6,\\
N=-975p^2+720pv-128v^2,\qquad D_\infty=8460p-3840v,\\
F_3(y)=\sum_{i=15}^{18}[R_i]_{21-i}y^{i-15},\qquad
F_4(y)=\sum_{i=14}^{18}[R_i]_{20-i}y^{i-14},\qquad
\ell=N/D_\infty.
\end{gathered}
\tag{11.7}
$$

$A,N,D_\infty$ are nonzero, and exact coefficient arithmetic gives

$$
B_\infty^2=4AC,\quad 2AN+B_\infty D_\infty=0,\quad
F_3(\ell)=0,\quad F_3'(\ell)^2=4AF_4(\ell).
\tag{11.8}
$$

These tests require only the indicated homogeneous coefficient parts of
the $512$-term $R$. For completely polynomial tests, multiply the third
identity by $D_\infty^3$ and the fourth by $D_\infty^4$; expansion and
coefficient subtraction give zero. Thus no resultant expansion is used
for this upper bound.

Take algebraically independent $P,V$ and substitute $p=tP,v=tV$.
Work over an algebraic Puiseux extension of $\mathbb Q(P,V)((t^{-1}))$.
The Newton polygon from (11.6) gives sixteen bounded roots and two roots
of order $t$; the nonzero coefficients $C,A$ give these multiplicities.
The leading equation of the latter two roots $x=ty$ is
$y^{16}(Ay^2+B_\infty y+C)=Ay^{16}(y-\ell)^2$.
Here and in the rest of this argument the homogeneous quantities are
evaluated at $(P,V)$, and $\ell\ne0$.

Substitute $x=t\ell+z$. At the first nonzero order, the equation for
$z$ is, up to the nonzero factor $\ell^{14}$,

$$
A\ell^2z^2+\ell F_3'(\ell)z+F_4(\ell)=0.
\tag{11.9}
$$

The missing order follows from $F_3(\ell)=0$ in (11.8). The
quadratic's discriminant vanishes by the last identity there.
Consequently both roots have the expansion

$$
x=t\ell-\frac{F_3'(\ell)}{2A\ell}+O(t^{-1/2}).
\tag{11.10}
$$

This order estimate also follows by translating the double root in
(11.9): the next coefficients are of order $t^{-1}$, so the Newton
polygon places the translated roots at order at most $t^{-1/2}$.
The difference of the two large roots is therefore $O(t^{-1/2})$.

Use $\operatorname{Disc}(R)=\rho^{34}\prod_{i<j}(x_i-x_j)^2$.
The leading coefficient contributes $34\cdot4=136$. The $32$
large/bounded pairs contribute at most $64$. Bounded/bounded differences
contribute at most $0$, even if some bounded limiting roots coincide.
The large/large difference contributes at most $-1$. Thus the total
exponent is at most $136+64-1=199$. Algebraic independence of $P,V$
identifies that exponent with total parameter degree, proving the bound.
This is a characteristic-zero argument. ∎

**Lemma 11.4 (Terminal degree at most 303).** The total parameter degree
of $F$ is at most $303$.

Proof. Let $P_j$ be the homogeneous total-degree-$j$ part of $P_M$ in
$(p,v,z)$ and put

$$
\ell_M=(-30p+32v)/5,\qquad g_M=30p-32v+5z.
\tag{11.11}
$$

The complete small homogeneous tests, by the coefficient operations of
Lemma 10.2, are

$$
\begin{gathered}
P_{18}=g_M^2S_{16},\qquad
S_{16}(\ell_M)\ne0,\qquad
\gcd(S_{16},\partial_zS_{16})=1,\\
P_{17}(\ell_M)=0,\\
A_M=\tfrac12(\partial_z^2P_{18})(\ell_M)\ne0,\quad
B_M=(\partial_zP_{17})(\ell_M),\quad C_M=P_{16}(\ell_M),\\
B_M^2=4A_MC_M.
\end{gathered}
\tag{11.12}
$$

$S_{16}$ has $153$ monomials and $z$-degree $16$. Its exact division by
$g_M^2$ has zero remainder. Evaluations can all be made polynomial by
using the common multiplier $5^{18}$, and the division by $2$ in $A_M$
is exact over $\mathbb Q$. The gcd is over $\mathbb Q[p,v,z]$ and also
says that no parameter-only content survives in $S_{16}$. To regenerate
it one may perform primitive Euclidean gcd in $z$ over
$\mathbb Q(p,v)$ and take the coefficient-content gcd separately.

Set $\epsilon=t^{-1}$ and consider
$t^{-18}P_M(tP,tV,tZ)$. At $\epsilon=0$ its roots consist of sixteen
simple slopes and the double slope $\ell_M$, by (11.12). Hensel
factorization separates the simple factors from the monic quadratic at
that double slope. In its coordinate $Z=\ell_M+u$, its first terms,
after multiplication by a unit, are

$$
A_Mu^2+\epsilon B_Mu+\epsilon^2C_M
+O(u^3,\epsilon u^2,\epsilon^2u,\epsilon^3).
\tag{11.13}
$$

The term of order $\epsilon$ at $u=0$ vanishes because
$P_{17}(\ell_M)=0$. The quadratic discriminant has order at least
$\epsilon^3$, since its order-$\epsilon^2$ coefficient is
$(B_M^2-4A_MC_M)/A_M^2=0$. The simple-root discriminant and the
cross-resultant are units. Thus the entire discriminant in $Z$ is
$O(\epsilon^3)$. Scaling eighteen roots from $Z$ to $z=tZ$ contributes
$t^{18\cdot17}=t^{306}$. The terminal leading coefficient (10.3) is
constant, so no further parameter degree is introduced. The exponent
is at most $306-3=303$, as asserted. ∎

## 12. Bivariate finite arithmetic and the robust J comparison

**Definition 12.1 (A terminal-linear J circuit).** In this section $z$
is a formal $J$ value. Write $f=ad^2+b_fd+c_f$ as in IX, (4.4), and put

$$
\begin{aligned}
G={}&2Da_0a_1(z-d)\\
 &-\bigl((8x+1)a_0a_1-dDa_1-4(24-d)Da_0\bigr)a_7,\\
g_i={}&[d^i]G,\\
L_J={}&a^2g_1-ab_fg_2+(b_f^2-ac_f)g_3,\\
T_J^{\rm rem}={}&a^2g_0-ac_fg_2+b_fc_fg_3,\\
A_6={}&177x^6+724x^5+542x^4-742x^3-629x^2+196x+160,\\
J_{\rm lin}={}&
\frac{T_J^{\rm rem}\alpha-L_J\beta}{6400D^6F_0A_6^2}.
\end{aligned}
\tag{12.1}
$$

The last division is exact in $\mathbb Z[x,p,v,z]$, with no sign or
content adjustment. This $L_J$ is unrelated to $L$ in (10.2).

**Lemma 12.2 (Faithful generic J equation).** The polynomial
$J_{\rm lin}$ is primitive, has $647$ monomials, $x$-degree $18$,
$z$-degree $1$, and total degree $21$. It represents the robust
$\tau_J$ of (9.2) in the generic carrier field, both in characteristic
zero and after reduction modulo $101$.

Proof. Before substituting $d=\delta$ put
$B_n=294D-10dD-5a_2$, $C_n=25D^2d^2+B_n^2$ and
$N_n=-5dDa_0+B_na_2$. Coefficient expansion gives

$$
5dDN_n+a_0C_n-B_nf=0.
\tag{12.2}
$$

Dividing only in the generic field shows
$dN_0+H_0C_0=0$ on $f=0$. Hence $C_0/N_0=-d/H_0$ where the latter
expression is defined generically. Substitution in (9.2), followed by
multiplication by $2Da_0a_1$, gives exactly $G=0$.
Polynomial division also gives

$$
f\mid a^2G-L_Jd-T_J^{\rm rem},\qquad a=-10A_6.
\tag{12.3}
$$

Combining the linear remainder with $\alpha d+\beta=0$ gives (12.1).
The exact divisions and the generic cancellations are specified by these
finite tests:

| Quantity | Result over $\mathbb Q$ and over $\mathbb F_{101}$ |
| --- | --- |
| $T_J^{\rm rem}\alpha-L_J\beta-6400D^6F_0A_6^2J_{\rm lin}$ | $0$ |
| $\gcd_x(R,6400D^6F_0A_6^2)$ | $1$ |
| $\gcd_x(R,a)$ | $1$ |
| $\gcd_x(R,\alpha)$ | $1$ |
| $\gcd_x(R,([d^0]a_0)\alpha-([d]a_0)\beta)$ | $1$ |
| $\gcd_x(R,[z]J_{\rm lin})$ | $1$ |

Here gcds are monic over the corresponding parameter fraction field;
the same characteristic-zero polynomial identities are used before
reduction. They are regenerated by (12.1)–(12.3), coefficient collection
and Euclidean division. The fourth gcd controls the generic $H_0$
cancellation. Thus $[z]J_{\rm lin}$ is a unit in the generic carrier,
and its equation is $z=\tau_J$. This proves the claimed correspondence.
The five norm calculations below also ensure that the original robust
functions are defined after reduction. This generic comparison does
not impose $d\ne0,H_0\ne0,F_0\ne0$ or $\beta\ne0$ on actual worlds;
all-world evaluation still uses (9.2) and S, Lemma 9.9. ∎

**Lemma 12.3 (Complete bivariate residue family).** Keep $p,v$
algebraically indeterminate and reduce the displayed integer circuits
modulo $101$. An overline denotes this reduction, never a specialization
of either parameter. The following finite arithmetic holds in
$\mathbb F_{101}[p,v]$.

Proof and specification of the arithmetic. For a nonzero polynomial
write $\operatorname{mon}(A)$ for division by its lexicographic leading
coefficient, with order $p>v>z$ when $z$ is present. In the rest of this
proof all gcds are monic. Reduce a rational fraction by its polynomial
gcd and normalize its two polynomial sides separately to be monic,
recording the residual scalar. Gcd in $p,v$ can be regenerated by
collecting coefficients in $p$, computing their contents in
$\mathbb F_{101}[v]$, and using Euclidean division in
$\mathbb F_{101}(v)[p]$ on the primitive parts; clear denominators, remove
content, and restore the content gcd. Apply the same procedure recursively
when $x$ or $z$ is present. The characteristic-zero version uses
$\mathbb Q$ instead of $\mathbb F_{101}$ and Gauss primitive parts.
These instructions, together with the Sylvester determinant in Lemma
10.2, fix all the arithmetic below.

First form $\overline R,\overline\rho,\overline P_M$ by (9.1),
(10.1)–(10.2), using exact polynomial quotients. The degrees of the
operands in the eliminated variable are retained. Put

$$
\begin{gathered}
\mathsf E=-\operatorname{Res}_x(\overline R,\overline R_x)/\overline\rho,
\qquad
\mathsf F=-\operatorname{Res}_z(\overline P_M,
                       \partial_z\overline P_M)/\overline c,\\
\mathsf R_J=\operatorname{Res}_x(\overline R,\overline J_{\rm lin}),\\
\mathsf P_J=\operatorname{mon}
 \left(\mathsf R_J/\gcd_{0\le i\le18}([z^i]\mathsf R_J)\right),
\qquad \mathsf l_J=[z^{18}]\mathsf P_J,\\
\mathsf D_J=-\operatorname{Res}_z(\mathsf P_J,\partial_z\mathsf P_J)
                                      /\mathsf l_J,\\
\mathsf K_M=\frac{\overline\rho^{34}\mathsf F}
                  {\overline c^{34}\mathsf E},\qquad
\mathsf K_J=\frac{\overline\rho^{34}\mathsf D_J}
                  {\mathsf l_J^{34}\mathsf E}.
\end{gathered}
\tag{12.4}
$$

The minus signs are $(-1)^{18\cdot17/2}$. The divisions defining
$\mathsf E,\mathsf F,\mathsf D_J$ are exact polynomial divisions.
The last two expressions are reduced rational fractions.
The content gcd of $\mathsf R_J$ is in $\mathbb F_{101}[p,v]$.
In particular $\mathsf P_J$ is defined *after* modular reduction; no
commutation of characteristic-zero primitive extraction with reduction
is assumed.

Here is the full construction of the numerator and denominator square
roots used in the table. Reduce $\mathsf K_E$ to
$s_E A_E/B_E$ with $A_E,B_E$ separately monic and coprime. Their unique
monic polynomial square roots are $n_E,d_E$. They can be computed without
factorization: start with the square root of the leading monomial and,
if a partial root is $u$, add the leading monomial of the residual
$(A_E-u^2)/(2\operatorname{LT}(u))$; repeat until the residual is zero.
Do the same for $B_E$. Exponents in each division must be nonnegative;
verify by squaring the final roots. Characteristic $101$ makes $2$ a
unit. This prescription gives an unambiguous finite test and the exact
identities

$$
\mathsf K_J=13(n_J/d_J)^2,\qquad
\mathsf K_M=36(n_M/d_M)^2.
\tag{12.5}
$$

These are squares of the literal indices by the Vandermonde identity of
IX, (7.3), and Lemmas 10.2 and 12.2. In the modular carrier the latter
lemma identifies
$\mathsf P_J/\mathsf l_J=\chi_J$ because the norm of its linear equation
is its leading norm times $\chi_J$. Its coefficient content changes only
that scalar rational function of $p,v$. Thus it cancels from (12.4).

| Polynomial or reduced pair | Total degree | Number of monomials |
| --- | --- | --- |
| $\mathsf E$ | $199$ | $19884$ |
| $\mathsf F$ | $303$ | $45881$ |
| $\overline P_M$ | $18$ | $1314$ |
| $\mathsf R_J$ | $192$ | $320281$ |
| $\mathsf P_J$ | $20$ | $1747$ |
| $n_J$ | $228$ | $26098$ |
| $d_J$ | $107$ | $5819$ |
| $n_M$ | $189$ | $17963$ |
| $d_M$ | $69$ | $2459$ |
| $\mathsf C_J=n_J/\operatorname{mon}(\overline\rho)^{17}$ | $160$ | $12915$ |
| $\mathsf C_M=n_M/\operatorname{mon}(\overline\rho)^{17}$ | $121$ | $7429$ |

The additional scalar and leading-coefficient tests are

$$
\begin{gathered}
\overline c=88,\qquad
\deg\overline\rho=4,\qquad \operatorname{content}(\rho)=20250000
                                      \equiv5\pmod{101},\\
\mathsf l_J=28p^2+37pv+20p+51v^2+6v+18,\\
21\mathsf l_J=83p^2+70pv+16p+61v^2+25v+75.
\end{gathered}
\tag{12.6}
$$

Here $\mathsf R_J$ and $\mathsf P_J$ both have terminal degree $18$.
All exact square-root identities in (12.5) have zero residual, and

$$
\begin{gathered}
\gcd(n_J,d_J)=\gcd(n_M,d_M)=1,\\
\gcd(n_J,n_M)=\operatorname{mon}(\overline\rho)^{17},\\
\gcd(\mathsf C_M,n_J)=\gcd(\mathsf C_M,d_J)
=\gcd(\mathsf C_M,d_M)=1,\\
\gcd(\mathsf C_M,\overline\rho)
=\gcd(\mathsf C_M,\mathsf E)
=\gcd(\mathsf C_M,p-24)
=\gcd(\mathsf C_M,\overline T_5)=1.
\end{gathered}
\tag{12.7}
$$

For the common discriminant data there is an equally compact
factorization-free prescription. Define

$$
\begin{gathered}
\mathsf U=\gcd(\mathsf E,\partial_p\mathsf E,\partial_v\mathsf E),
\qquad
\mathsf B=\operatorname{mon}(\mathsf E/\mathsf U^2),\\
\mathsf W=\sqrt{\operatorname{mon}(\mathsf F/\mathsf B)}.
\end{gathered}
\tag{12.8}
$$

Use the monic square-root rule above. The divisions are exact. The
results and residual identities are

$$
\begin{gathered}
\deg\mathsf B=51,\quad |\operatorname{supp}\mathsf B|=1366,
\quad \gcd(\mathsf B,\mathsf B_p,\mathsf B_v)=1,\\
\deg\mathsf U=74,\quad \deg\mathsf W=126,\qquad
\operatorname{mon}(\mathsf E)=\mathsf B\mathsf U^2,
\quad \operatorname{mon}(\mathsf F)=\mathsf B\mathsf W^2,\\
\gcd(\mathsf U,\mathsf W)=\operatorname{mon}(\overline T_5),
\quad \gcd(\mathsf E,\mathsf F)=
                         \mathsf B\operatorname{mon}(\overline T_5)^2,\\
\operatorname{mon}(\mathsf U/\overline T_5)=d_M,
\qquad \operatorname{mon}(\mathsf W/\overline T_5)=\mathsf C_M,
\qquad\gcd(\overline\rho,d_M)=1.
\end{gathered}
\tag{12.9}
$$

In particular the common discriminant gcd has degree $61$. These are
identities in the full bivariate polynomial ring, not a slice through it.
The formulas (12.4), (12.8), the monomial arithmetic, and the explicit gcd
and square-root rules determine all coefficients of all the objects in
(12.5)–(12.9). Multiplication after each exact quotient and squaring
after each square root give their stated zero residuals. The degree and
support counts are obtained by taking the largest exponent sum and
counting the nonzero entries of these same finite coefficient maps.
Thus this supplies reproducible exact finite arithmetic for the entire
family without relying on an expanded coefficient list. ∎

## 13. Every original inversion and denominator

**Proposition 13.1 (The five-norm adjugate inventory).** The original
$E_0$ of Definition 9.1 has precisely the radical support described by
(13.8) below. The following polynomial matrices account for every
inversion in its defining circuit.

Proof. All matrices in this proof are $18$ by $18$, with entries in
$\mathbb Z[p,v]$ except for explicitly displayed scalar denominators.
Number rows and columns $0,\ldots,17$ and put $r=\rho$,
$R=\sum_{i=0}^{18}r_ix^i$. Define

$$
\mathcal T_{i+1,i}=r\ (i<17),\qquad
\mathcal T_{i,17}=-r_i\ (0\le i<18),
\tag{13.1}
$$

with other entries zero. Then $\mathcal X=\mathcal T/r$ is exactly
multiplication by $x$ in the original coefficient basis. Write
$a_i=A_i(x)+B_i(x)d$ and set

$$
\begin{gathered}
\mathcal A=r^{32}\alpha(\mathcal X),\quad
\mathcal B=r^{32}\beta(\mathcal X),\quad
\mathcal D=r^3D(\mathcal X),\\
\mathcal P_i=r^3A_i(\mathcal X),\quad
\mathcal Q_i=r^3B_i(\mathcal X),\\
s_a=\det\mathcal A,\qquad s_d=\det\mathcal D,\qquad
\Delta=-\operatorname{adj}(\mathcal A)\mathcal B,\qquad q_0=s_as_d.
\end{gathered}
\tag{13.2}
$$

The degrees $\deg_x\alpha=\deg_x\beta=32$ and
$\deg_x A_i,\deg_xB_i\le3$, obtained directly from IX, (4.1)–(4.5),
make these polynomial matrices. They all lie in the commutative
multiplication algebra generated by $\mathcal X$. Their adjugates
commute there too, as follows either from the characteristic-polynomial
formula for the adjugate or by passing to the generic inverse.

Define polynomial numerators

$$
\begin{gathered}
Y_i=(\mathcal P_is_a+\mathcal Q_i\Delta)
                                      \operatorname{adj}(\mathcal D),\\
V_b=294q_0I-10s_d\Delta-5Y_2,\\
C_b=25s_d^2\Delta^2+V_b^2,\qquad
N_b=-5s_d\Delta Y_0+V_bY_2,\\
s_1=\det Y_1,\qquad s_C=\det C_b,\qquad s_N=\det N_b.
\end{gathered}
\tag{13.3}
$$

Then the full five-inverse list is

$$
\begin{aligned}
M(\alpha^{-1})&=r^{32}\operatorname{adj}(\mathcal A)/s_a,&
M(D^{-1})&=r^3\operatorname{adj}(\mathcal D)/s_d,\\
M(H_1^{-1})&=q_0\operatorname{adj}(Y_1)/s_1,&
M(C_0^{-1})&=25q_0^2\operatorname{adj}(C_b)/s_C,\\
M(N_0^{-1})&=5q_0^2\operatorname{adj}(N_b)/s_N.
\end{aligned}
\tag{13.4}
$$

Indeed $A\operatorname{adj}(A)=\det(A)I$ proves each equality and
also gives the coefficient formulas

$$
\begin{gathered}
M(\delta)=\Delta/s_a,\qquad M(H_i)=Y_i/q_0,\qquad
M(B_0)=V_b/(5q_0),\\
M(C_0)=C_b/(25q_0^2),\qquad M(N_0)=N_b/(5q_0^2),\qquad
M(U)=5N_b\operatorname{adj}(C_b)/s_C.
\end{gathered}
\tag{13.5}
$$

The last robust reconstruction identity uses $U=N_0/C_0$ and needs
neither a drift inverse nor an $H_0$ inverse.

For completeness the two response denominators and numerators are

$$
\begin{aligned}
q_M={}&rq_0,\\
T_M={}&rs_d\Delta+(2\mathcal T+3rI)Y_7,\\
J_b={}&5s_Ns_1(8\mathcal T+rI)+rs_1C_b\operatorname{adj}(N_b)\\
 &-20rs_Ns_d(24s_aI-\Delta)\operatorname{adj}(Y_1),\\
q_J={}&10rq_0s_Ns_1,\\
T_J={}&10rs_Ns_1s_d\Delta+J_bY_7,\\
M(\tau_E)={}&T_E/q_E\qquad(E=J,M).
\end{aligned}
\tag{13.6}
$$

Substituting (13.5) into the *robust* (9.2) proves (13.6) by common
denominators. In particular $C_0/(2N_0)$ contributes
$C_b\operatorname{adj}(N_b)/(10s_N)$; this accounts for its scalar $5$
and for the factor $s_N$ even on strata where a generic J simplification
would cancel a different expression. Each of (13.4)–(13.6) is a
commutative polynomial cross-product identity after multiplication by its
displayed denominators.

Let $e_0=(1,0,\ldots,0)^t$. All coefficient, characteristic-polynomial
and power-index denominators are now explicit:

$$
\begin{gathered}
\chi_E(z)=\det(q_EzI-T_E)/q_E^{18},\\
\mathcal F_E=\det[e_0,T_Ee_0,T_E^2e_0,\ldots,T_E^{17}e_0],\qquad
\iota_E=\mathcal F_E/q_E^{153},\qquad
153=0+1+\cdots+17.
\end{gathered}
\tag{13.7}
$$

Thus $\mathcal F_E$ is an integer polynomial, without a primitive
normalization. Put $S_*=rs_as_ds_1s_Cs_N$. The exact norm equations are

$$
\begin{gathered}
\operatorname{Nm}(\alpha)=s_a/r^{576},\qquad
\operatorname{Nm}(D)=s_d/r^{54},\qquad
\operatorname{Nm}(H_1)=s_1/q_0^{18},\\
\operatorname{Nm}(C_0)=s_C/(25^{18}q_0^{36}),\qquad
\operatorname{Nm}(N_0)=s_N/(5^{18}q_0^{36}),\\
\operatorname{rad}(E_0)=\operatorname{rad}(ES_*),\qquad
\operatorname{rad}(H)=\operatorname{rad}(ES_*).
\end{gathered}
\tag{13.8}
$$

Radicals here mean products of nonconstant irreducible factors over
$\mathbb Q$, without scalar factors. To prove the first support equality,
$r$ is an original factor. The first two norm equations put every factor
of $s_a,s_d$ in the union of $r$ and the reduced sides of those norms.
Next the third puts all factors of $s_1$ in the preceding support and
the reduced sides of $\operatorname{Nm}(H_1)$. The last two do the same
for $s_C,s_N$. This proves $S_*$-support is contained in the original
inventory. Conversely these exact equations put both reduced sides of
every norm inside $S_*$-support, and (13.5)–(13.7) put every original
coefficient and index denominator there. Including the original $E$
proves the reverse containment. Finally $p-24$ divides $E$ by Lemma
11.2, giving the second equality. This identifies the support of the
original polynomial; it does not replace or redefine $H$.

There is a short resultant recipe for all norm arithmetic, which also
checks factors lost in reduced fractions. For a polynomial $w$ in $x$,
define

$$
\mathcal N(w)=\operatorname{Res}_x(R,w)/r^{\deg_xw},
\qquad \mathcal N(w_1/w_2)=\mathcal N(w_1)/\mathcal N(w_2).
\tag{13.9}
$$

This is the norm because $R/r$ is monic. Put

$$
\begin{gathered}
h_i=A_i\alpha-B_i\beta,\qquad
b_n=294D\alpha+10D\beta-5h_2,\\
c_n=25D^2\beta^2+b_n^2,\qquad
n_n=5D\beta h_0+b_nh_2.
\end{gathered}
\tag{13.10}
$$

The five norms in (13.8) are computed by (13.9) on
$\alpha,D,h_1/(D\alpha),c_n/(25D^2\alpha^2),
n_n/(5D^2\alpha^2)$ respectively. Reduce each complete fraction only
after these operations. Modulo $101$ the results are as follows; each
last-column entry lists all three gcds, separately.

| Original norm | Numerator degree | Denominator degree | Monic denominator | $\gcd(n,d),\gcd(\mathsf C_M,n),\gcd(\mathsf C_M,d)$ |
| --- | --- | --- | --- | --- |
| $\operatorname{Nm}(\alpha)$ | $240$ | $128$ | $\operatorname{mon}(\overline r^{32})$ | $1,1,1$ |
| $\operatorname{Nm}(D)$ | $18$ | $12$ | $\operatorname{mon}(\overline r^3)$ | $1,1,1$ |
| $\operatorname{Nm}(H_1)$ | $14$ | $0$ | $1$ | $1,1,1$ |
| $\operatorname{Nm}(C_0)$ | $32$ | $0$ | $1$ | $1,1,1$ |
| $\operatorname{Nm}(N_0)$ | $32$ | $0$ | $1$ | $1,1,1$ |

This table is regenerated by the exact bivariate resultant and fraction
gcd instructions of Lemma 12.3 applied to the five explicitly displayed
fractions. The scalar norm of a constant is its eighteenth power.
It supplies all ten core-versus-norm-side gcds, not just checks on the
five reduced numerators. All five norms are nonzero.

Polynomial matrix evaluation, determinants and adjugates commute with
reduction. From $\overline r\ne0$ and the first two nonzero modular
norms, $\overline s_a,\overline s_d$ are nonzero. Then the remaining
three norms prove $\overline s_1,\overline s_C,\overline s_N\ne0$.
The norm equations therefore remain identities in
$\mathbb F_{101}(p,v)$. Applying the ten gcds successively to these
same equations, beginning with
$\gcd(\mathsf C_M,\overline r)=1$, gives

$$
\gcd(\mathsf C_M,\overline S_*)=1,
\qquad \gcd(\mathsf C_M,\overline q_J)=1.
\tag{13.11}
$$

For example, $\overline s_a\,d=\overline r^{576}n$ for the reduced
modular norm sides; a common factor of $\mathsf C_M,\overline s_a$
would have to divide $\overline r$ or $n$, already excluded. Continue
with $s_d,s_1,s_C,s_N$. This induction controls raw factors even when
they have canceled from a norm fraction.

Finally (12.5), (12.7) say that the literal reduced modular $J$ index
has numerator proportional to $n_J$, since $13=35^2$ modulo $101$.
Using (13.7) and (13.11) yields

$$
\gcd(\mathsf C_M,\overline{\mathcal F_J})=1,
\qquad
\gcd(\mathsf C_M,\overline E\,\overline S_*)=1.
\tag{13.12}
$$

No assertion about reduction of the characteristic-zero primitive
$N_J$ was needed. ∎

## 14. Degree forcing, literal coprimality and the entire-child consumer

**Lemma 14.1 (Characteristic-zero normalization forced by degrees).**
There are primitive positive polynomials $B_{51},C_{121},V_{69}$ such
that

$$
\begin{gathered}
E=uB_{51}T_5^2V_{69}^2,\qquad
F=wB_{51}T_5^2C_{121}^2,\qquad u,w\in\mathbb Q^*,\\
\iota_M=\lambda\rho_0^{17}C_{121}/V_{69},\qquad
\lambda\in\mathbb Q^*,\qquad v_{101}(\lambda)=0,\\
\gcd(C_{121},V_{69})=\gcd(\rho_0,V_{69})=1.
\end{gathered}
\tag{14.1}
$$

The subscripts are total degrees. Both $C_{121}$ and $V_{69}$ retain
these degrees after reduction; their reductions are scalar multiples of
$\mathsf C_M,d_M$ respectively. In particular (9.4) is literal.

Proof. The monic-carrier Vandermonde identity IX, (7.3), together with
$P_M=c\chi_M$ gives the exact rational identity

$$
\rho^{34}F=c^{34}E\iota_M^2.
\tag{14.2}
$$

The nonzero bivariate residues of degrees $199,303$ in Lemma 12.3
supply the lower bounds for the characteristic-zero polynomials $E,F$.
Lemmas 11.3–11.4 supply the respective upper bounds. Therefore

$$
\deg E=199,\qquad\deg F=303,
\tag{14.3}
$$

and both degrees survive reduction. This uses ordinary
characteristic-zero degree bounds, not a modular upper-bound inference.

Parity of each irreducible valuation in the UFD $\mathbb Q[p,v]$ in
(14.2) says that $E,F$ have the same odd squarefree part. Thus write

$$
E=uBU^2,\qquad F=wBW^2,
\tag{14.4}
$$

where $B,U,W$ are primitive positive integer polynomials and $B$ is
squarefree. All three have $101$-Gauss valuation zero: for a nonzero
polynomial this valuation is the minimum $101$-adic valuation of its
coefficients, which is additive under multiplication by Gauss' lemma.
The nonzero reductions of the raw $E,F$ imply $v_{101}(u)=v_{101}(w)=0$.
Reducing (14.4), the odd squarefree part $\mathsf B$ of $\mathsf E$
in (12.8) must divide $\overline B$. Hence $\deg B\ge51$.

By (11.2), $T_5$ divides both $U,W$: an irreducible exponent at least
$2$ in a discriminant has square-root exponent at least $1$, whether
its parity is odd or even. Put

$$
g=\operatorname{pp}_+(\gcd(U,W)),\qquad
C=\operatorname{pp}_+(W/g),\qquad
V=\operatorname{pp}_+(U/g).
\tag{14.5}
$$

Then $\deg g\ge5$, $\gcd(C,V)=1$, and (14.3)–(14.4) give

$$
\deg C=\frac{303-\deg B}{2}-\deg g\le121,
\qquad
\deg V=\frac{199-\deg B}{2}-\deg g\le69.
\tag{14.6}
$$

The exact index (14.2) now has the form
$\iota_M=\lambda\rho_0^{17}C/V$ for a nonzero rational $\lambda$;
its scalar is rational because this is an identity with the already
rational index. Taking a square does not choose a new square-root
branch. The scalar sign is irrelevant to its separately primitive
numerator and denominator.

We check its $101$-adic status before reducing. Every scalar inversion
in (9.2), (13.2)–(13.7) is a power of $2$ or $5$; the polynomial
inversions have the nonzero reductions proved in Proposition 13.1.
The constants $10,25,256,6400,1152,2592,82944$ reduce respectively to
$10,25,54,37,41,67,23$, and $\overline c=88$ and the content of
$\rho$ reduces to $5$. Thus these constants are $101$-units.
The nonzero literal modular index in (12.5), together with
$\overline q_M\ne0$, gives $\overline{\mathcal F_M}\ne0$ in (13.7).
Consequently $\iota_M$ has Gauss valuation zero. The primitive factors
$\rho_0,C,V$ each have Gauss valuation zero, so
$v_{101}(\lambda)=0$. Reduction of their rational equality is now
legitimate.

By (12.5) the reduced modular $M$ index is a scalar multiple of
$n_M/d_M$; $36=6^2$ in $\mathbb F_{101}$. Its reduced denominator has
degree $69$. But reduction of (14.6) has denominator degree at most
$\deg\overline V\le\deg V\le69$, and cancellation can only decrease
it. Thus equality holds throughout and there is no modular cancellation
between $\overline V$ and the numerator. Equality in (14.6) also forces
$\deg B=51$ and $\deg g=5$. Since $T_5\mid g$, their primitive positive
normalizations give $g=T_5$. Then $\deg C=121$.

The modular numerator has degree $189=17\cdot4+121$. The degree of
$\overline\rho_0$ is $4$, so $\deg\overline C=121$ too. Unique reduced
fractions identify $\operatorname{mon}(\overline C)=\mathsf C_M$ and
$\operatorname{mon}(\overline V)=d_M$. The same no-cancellation
conclusion, or $\gcd(\overline\rho,d_M)=1$ with preserved degrees,
gives $\gcd(\rho_0,V)=1$ in characteristic zero. We already have
$\gcd(C,V)=1$. Naming these polynomials $C_{121},V_{69}$ and $B$ as
$B_{51}$ proves (14.1). The product $\rho_0^{17}C_{121}$ is itself
primitive positive by Gauss' lemma. It is therefore exactly the original
$N_M$, and $V_{69}$ is exactly its primitive denominator. This proves
(9.4), including its scalar/content convention. ∎

**Theorem 14.2 (Original-H transfer and the independent-pair restriction).**
Equations (9.5)–(9.6) and the all-world assertion of Theorem 9.2 hold.

Proof. Here is the degree-preservation argument which transfers the
finite-field gcds. If a primitive positive polynomial $C\in\mathbb Z[p,v]$
retains its total degree after reduction modulo $101$, then every
nonconstant characteristic-zero factor retains its degree too. Indeed
write $C=AB$ with primitive integer factors, using Gauss' lemma.
Both reductions are nonzero, and

$$
\deg\overline C=\deg\overline A+\deg\overline B
\le\deg A+\deg B=\deg C.
\tag{14.7}
$$

Equality forces equality in both degree inequalities. In particular a
nonconstant factor has nonconstant reduction.

Apply this to $C=C_{121}$, whose degree is preserved by Lemma 14.1.
A common irreducible factor of $C_{121}$ and the integer polynomial
$\mathcal F_J$ would, by Gauss' lemma, reduce to a nonconstant common
factor of $\mathsf C_M$ and $\overline{\mathcal F_J}$, contradicting
(13.12). Therefore $\gcd(C_{121},\mathcal F_J)=1$. The reduced primitive
$N_J$ divides $\mathcal F_J$ up to a rational scalar by (13.7), so
$\gcd(C_{121},N_J)=1$.

The same argument with the integer polynomial $ES_*$ and the second
gcd in (13.12) gives $\gcd(C_{121},ES_*)=1$. The exact support identity
(13.8) gives $\gcd(C_{121},H)=1$. This establishes (9.5) for the
*original* $H$. It uses neither a degree-preservation premise for $N_J$
nor a claim that its characteristic-zero primitive extraction commutes
with reduction. The raw determinant and the full original norm inventory
supply the transfer instead.

On $H\ne0$, $\rho_0$ is a unit. Equation (9.4) therefore makes
$N_M=0$ exactly $C_{121}=0$, proving the equality of sets in (9.6).
Also $V_{69}$ is a unit there by its factorization in $E$ in (14.1),
and every original coefficient or index denominator is a unit by its
inclusion in $E_0$. Equivalently the literal index zero loci in
$\mathbb Q[p,v,H^{-1}]$ are the same. If the raw J determinant is used,
(13.7) changes $N_J$ only by a scalar and factors supported on $H$;
these are units on this same open. No saturation or primitive-reduction
commutation is invoked.

For completeness, coprime nonzero polynomials in two variables have a
finite, possibly empty complex affine intersection. One elementary proof
uses their nonzero resultant over $\mathbb Q(p)$ after a generic rational
linear change of coordinates. Every common zero projects to one of the
finitely many zeros of this resultant. At any such coordinate, both
specialized polynomials cannot vanish identically in the other variable:
a common vertical line over an algebraic extension would, with its
conjugates, give a common polynomial factor over $\mathbb Q$.
Each fibre is therefore finite. Coprimality persists over $\mathbb C$ by
the same conjugate-factor argument, or by the resultant identity.
Applying this to $C_{121},N_J$ proves finiteness of (9.6). It does not
assert that $1$ lies in their ideal or that the intersection is empty.

Finally take any original configuration (6.8.5) with $H(p,v)\ne0$.
S, Lemma 9.9, is an all-world statement: every one of its four complete
worlds is represented in this same carrier, distinct worlds have distinct
$x$, and the robust functions (9.2) give their actual clock-seven
responses. The Vandermonde evaluation argument there forces $N_J=0$
from the chosen distinct equal-$J$ pair and $N_M=0$ from the independently
chosen distinct equal-$M$ pair. By (9.6) their common acquired base lies
in $Z_H$. This reasoning is applied at one fixed $(p,v)$ to one entire
child, not to pairs from different bases, branches, parents, or gain
histories. There is no equation $m_0=m_1=m$, and the two common terminal
answers need not be equal. Cross-pair overlaps of size $0,1,2$ are all
allowed, so every overlap stratum is covered simultaneously. This proves
the last assertion of Theorem 9.2. ∎

## 15. Mathematical attribution and the retained world boundary

**Definition 15.1 (Scope of the finite restriction).** The source-specific
result of Sections 9–14 is the literal primitive M normalization, the
coprimality transfer for the unchanged original five-norm exceptional
inventory, and the finite necessary base condition for the full
independent-pair relation. It is repo-derived. The polynomial, valuation
and plane-curve tools used inside its proof are classical: Sylvester
resultants and their gcd criterion are as in M. Moreno Maza,
*Advanced Computer Algebra: The resultant*, “The resultant”, Definition 4
and Propositions 5–7,
[primary text](https://www.csd.uwo.ca/~mmorenom/CS874/Lectures/ResultantGcd.html/node3.html).
The determinant elimination is E. H. Bareiss, “Sylvester's Identity and
Multistep Integer-Preserving Gaussian Elimination”, Mathematics of
Computation 22, 565–578,
[doi:10.1090/S0025-5718-1968-0226829-0](https://doi.org/10.1090/S0025-5718-1968-0226829-0).
Gauss' lemma, height-one UFD valuations, Hensel factorization,
Newton–Puiseux order estimates, discriminant multiplicativity and finite
intersection of coprime plane curves are used in their ordinary
characteristic-zero senses, with the needed applications proved above.
No new general algebraic algorithm or worldwide priority is asserted.
The all-world source and Vandermonde identifications are reused from S,
Theorem 4.3 and Lemma 9.9, and IX, Sections 4–7. The independent-pair
inverse correspondence is the existing X, Definition 6.3 and Proposition
6.4, and XI, Sections 1–4, Theorem 5.3.1 and Definition 6.8.1.

**Proposition 15.2 (Unchanged realization and read obligations).** The
finite restriction is necessary only. It supplies no strict-real lift,
existence or absence at a base of $Z_H$, explicit list or cardinality of
$Z_H$, inverse on it, classification of $H=0$ (including $p=24$), or
full-domain eight/nine-read recovery. All actual worlds in its consumer
retain the following domain and history:

$$
\begin{gathered}
P=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\\
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R,\\
(E_1,\ldots,E_6)=(\mathsf J,\mathsf M,\mathsf J,\mathsf M,\mathsf M,\mathsf M),\\
(y_0,\ldots,y_6)=(0,24,147/5,24,18,p,v),\qquad
 y_i=d+g(i)\operatorname{tr}(Q_iP).
\end{gathered}
\tag{15.1}
$$

Proof. The consumer uses only the implication in S, Lemma 9.9, from
actual worlds to index zeros. None of the steps constructs worlds from
complex zeros or proves that every zero lifts. Conversely, all actual
worlds with this history and $H\ne0$ are covered by that lemma, including
all gain signs, lower degrees, sampled gain zeros, repeated roots, any
fixed real drift, and the original singular-source possibilities.
Each world has its own whole gain and drift; equality of worlds in an
overlap stratum means equality of those complete data. No bound on an
unused companion, no common drift across distinct worlds, and no
additional gain or source guard has entered the proof.

The acquired rows in (15.1) use one nonresettable trajectory. The initial
read is counted; each atomic J or M action is read immediately; terminal
J and M are alternatives at original clock seven. Algebraically comparing
the alternatives does not acquire both on one trajectory. There is no
reset, copy, idle skipped read, unread composite action, extra port or
clock renumbering. In a deterministic history-dependent procedure this
is a conditional restriction at a node with exactly these actual acquired
rows; it imposes no new action or early-stopping rule and proves no
unrestricted adaptive recovery statement.

The real joint question on the remaining finite outer bases and on all
$H=0$ strata is therefore still subject to the original complete-world
and actual-history conditions. The settled first negative-J family and
the old exact $p_J$ classification are not reopened. The local VII
results, XI7 attachments and XI8 whole-arc exclusion retain their stated
scopes; an isolated finite pair is not identified with a local germ by
this argument. Fixed48 V(18.12)(i), rootQ, genuine common-ancestor and
both-child compatibility, and the original full-domain adaptive
8/9-read problem receive no solution from this finite complex outer
restriction. ∎

## 追加锚（本行以下为增补区）

## 16. The actual source as an open of the terminal normalization

**Definition 16.1 (Source chart and terminal order).** Retain S, IX and X
as in Definition 9.1. To distinguish source polynomials from the action
matrices and from the inverse circuits, write

$$
\begin{gathered}
J_s=b^2+r-r^2,\quad N_s=J_s+br,\quad T=1+b,\quad U=1+2b,\\
A_s=(8b-1)(5b+2),\\
C_s=2(b^2+8b+4)J_sN_s-4bTU(J_s+N_s),\\
\mathcal P_s=5eC_s+6A_sJ_sN_s,\\
X_s=V_{\mathbb C}(\mathcal P_s)\cap
 D\bigl(br(1-r)TUJ_sN_s\bigr).
\end{gathered}
\tag{16.1}
$$

This is exactly IX, Definition 2.2. Its actual drift is $d=24+e$,
$j=J_s/b$, $n=N_s/b$, and its actual entire gain $g$ is the unique
polynomial of degree at most three with

$$
(g(0),g(1),g(2),g(3))=
\left(-24-e,-e/j,(27/5-e)/T,-e/n\right).
\tag{16.2}
$$

Use the regular responses $p,v,m$ of IX, (1.8)–(1.9), and put
$x=n/U$, $h=Ug$, $H_i=h(i)$ and $S_0=H_0^2+H_2^2$. In particular

$$
\begin{gathered}
p=d+(U+n)g(5),\quad v=d+(2U+n)g(6),\quad
m=d+(3U+2n)g(7),\\
a=d+(T+2j+4r)g(7).
\end{gathered}
\tag{16.3}
$$

The smooth source chart used below is

$$
\mathcal U=X_s\cap
 D\bigl((p-24)eC_s(x+1)(x+2)(2x+3)H_1S_0\bigr).
\tag{16.4}
$$

The chart imposes no nonzero condition on $d$, $H_0$, $F_0$, $\beta$,
$g(7)$, the leading gain coefficient or the gain discriminant. Gain signs,
lower degrees, sampled zeros, repeated roots and zero drift are retained
whenever consistent with the original readings and nonsingularity.

Let $R_b=\mathbb C[p,v]$, and use the literal polynomial of Definition
10.1, with its original sign and content, to define

$$
\begin{gathered}
c=33917016093258200081122929199218750000000,\\
f_{\rm ter}=P_M/c,\qquad
A=R_b[z]/(f_{\rm ter}),\qquad Y=\operatorname{Spec}(A).
\end{gathered}
\tag{16.5}
$$

Here $z$ is sent to the actual response $m$. Write $K_s=\mathbb C(X_s)$
and let $B$ be the integral closure of $A$ in $K_s$.

**Proposition 16.2 (Full real endpoint coverage and the actual field).**
Every original strict-real off-$24$ nonsingular endpoint belongs to
$\mathcal U$. The chart $\mathcal U$ is a nonempty smooth integral
complex surface, $A$ is a domain finite free of rank eighteen over
$R_b$, and

$$
\operatorname{Frac}(A)=\mathbb C(p,v,m)=K_s.
\tag{16.6}
$$

The morphism $\phi=(p,v,m):\mathcal U\to Y$ is regular and birational.

Proof. IX, Proposition 2.3, identifies every original real world with
its point of $X_s$, including the entire gain (16.2). Strict positivity
makes $b,T,U,j,n,x$ positive and $r(1-r)>0$. The off-$24$ consequence
in X, Assumption 1.2, gives $e\ne0$. Clock one gives
$H_1=-Ue/j\ne0$. Direct multiplication of IX, (2.11), gives

$$
\Lambda=\frac{C_s}{TUJ_sN_s}.
\tag{16.7}
$$

Thus nonsingularity gives $C_s\ne0$. The clock-zero and clock-two
identities of X, (3.6), with $u=1/U$, are

$$
uH_0+d=0,\qquad uH_2+H_2+2d-294/5=0.
\tag{16.8}
$$

If $H_0=H_2=0$ these force both $d=0$ and $2d=294/5$.
For a real world, therefore, $S_0>0$. All the factors in (16.4) are
nonzero. This uses reality only for $S_0>0$; complex points with
$S_0=0$ are not in this chart.

By IX, Theorem 3.1, $X_s$ is absolutely integral. Since
$\partial_e\mathcal P_s=5C_s$ is a unit on $\mathcal U$, the
Jacobian criterion makes this open smooth of dimension two. The point
IX, (3.3), has $b=1,r=1/2,e=1029/121$, $p=9918/121$ and
$\Lambda=-121/105$; the preceding argument puts it in $\mathcal U$.
Thus the open is nonempty and has the same function field as $X_s$.

IX, Theorem 6.1, identifies the degree-eighteen generic acquired fibre
with the original sources and their entire gains and drifts. IX,
Theorem 7.1, makes their actual $m$ a primitive element. These are
statements over $\mathbb C(p,v)$: the source is absolutely integral,
and the displayed nonzero generic determinants remain nonzero after
extending constants to $\mathbb C$. Lemma 10.2 identifies precisely
this minimal polynomial with the monic $f_{\rm ter}$. Consequently
the evaluation map $R_b[z]\to K_s$ has kernel $(f_{\rm ter})$,
by monic division followed by minimality over $\mathbb C(p,v)$.
It gives (16.6), and the monic degree eighteen gives the free basis
$1,z,\ldots,z^{17}$ of $A$ over $R_b$. Finally $f_{\rm ter}(m)=0$
in $K_s$ is an identity of regular functions on $X_s$, so it holds
everywhere there. This proves regularity and birationality of $\phi$.
No factor of the original $H$ has been inverted in this argument. ∎

**Proposition 16.3 (The source normalization open).** The normalization
$\nu:\operatorname{Spec}(B)\to Y$ is finite, and $\phi$ factors as
an open immersion $\mathcal U\hookrightarrow\operatorname{Spec}(B)$
followed by $\nu$.

Proof. First $\phi$ is quasi-finite, including over nonclosed points.
Work over an algebraic closure of any residue field of a point of $Y$;
this is a characteristic-zero field. Use the exact X, (2.5), quartic
and numerator, denoting them $K_{\rm inv},N_{\rm inv}$, and X,
(3.1), denoting its polynomials $F_{\rm inv},G_{\rm inv}$.
The tail denominator $\Delta=(x+1)(x+2)(2x+3)$ is a unit on our
chart. X, Proposition 5.1, proves that $F_{\rm inv}$ never vanishes
identically at any complex response triple. The proof works over every
algebraically closed characteristic-zero field: its polynomial identity
(5.1), the fixed rational coprimalities with $K_{\rm inv}$, and the
contradictory constant terms in $N_{\rm inv}=18K_{\rm inv}$ are
unchanged by field extension. Thus at $K_{\rm inv}\ne0$ there are
at most seven possible $x$, and $d=N_{\rm inv}/K_{\rm inv}$.

At $K_{\rm inv}=0$ there are at most four possible $x$. The coprimalities
in X, Proposition 4.1 and (3.4), give $\Delta\mathscr H\ne0$ at
every such root. By X, (4.10), compatibility of (16.8) is a quadratic
in $d$ whose leading coefficient is $\mathscr H/\Delta^2\ne0$.
There are therefore only finitely many possible $(x,d)$ in this case
also; necessity includes $N_{\rm inv}=0$, without dividing by $K_{\rm inv}$.

For each possible $(x,d)$ the four tail samples of X, (2.2), determine
$h$. With $C_t=H_2+2d-294/5$, equations (16.8) give the unique

$$
 u=-\frac{dH_0+H_2C_t}{S_0},\quad
 b=\frac{1-u}{2u},\quad j=\frac{24-d}{uH_1},\quad
 n=\frac xu,\quad r=n-j,\quad g=uh.
\tag{16.9}
$$

The denominators are units at a point of $\mathcal U$: $S_0,H_1$
by definition and $u=1/U$ by (16.1). These formulas establish
uniqueness among source points, without imposing any real inequalities
on complex fibres. All geometric fibres are finite. The finite-type
morphism $\phi$ is consequently quasi-finite; it is separated since
both source and target are separated over $\mathbb C$.

Normalization of a finite-type complex domain is finite (Stacks Project,
Lemma 33.27.1, [Tag 0BXQ](https://stacks.math.columbia.edu/tag/0BXQ)).
The normal dominant source factors uniquely through this normalization
by Lemma 29.55.5,
[Tag 035E](https://stacks.math.columbia.edu/tag/035E).
For clarity, the relative normalization used in Zariski's main theorem
is exactly $B$ here. Every element of $B$ is integral over each
$\mathcal O_{\mathcal U,w}$ and belongs to its fraction field $K_s$;
normality makes it regular at every $w$. Conversely every element of
$K_s$ integral over $A$ is in $B$ by definition. Thus the integral
closure of $A$ in the regular functions of $\mathcal U$ equals $B$,
and the same holds after localization on $Y$.
The relative-normalization form of Zariski's main theorem, Lemma 37.43.1,
[Tag 02LQ](https://stacks.math.columbia.edu/tag/02LQ), now applies to
the finite-type separated map $\phi$. Its quasi-finite locus is all of
$\mathcal U$, so the induced map is an isomorphism onto an open of
$\operatorname{Spec}(B)$. This proves the claim at all source points. ∎

## 17. Exact generic exclusions of the three terminal double sections

**Definition 17.1 (Component fields and literal inverse circuits).** Put
$T_{55}=55p-28v-1572$, $T_{58}=58p-23v-1350$ and retain $Q_2$ of
(11.1). The following table gives $p_T,v_T,z_T,a_T$ in $\mathbb Q(t)$:

| $T$ | $p_T$ | $v_T$ | $z_T$ | $a_T$ |
| --- | --- | --- | --- | --- |
| $T_{55}$ | $(28t+1572)/55$ | $t$ | $(184t-60)/55$ | $-(t+42)/33$ |
| $T_{58}$ | $(23t+1350)/58$ | $t$ | $(381t-1770)/116$ | $4(t+36)/(t-138)$ |
| $Q_2$ | $18(4t^2-57t+204)/((t-6)(3t-20))$ | $6(23t^2-400t+1680)/((t-6)(3t-20))$ | $(1824-135p_T+54v_T)/10$ | $0$ |

Specialize exactly X, (2.5) and (3.1), by
$(p,v,m)=(p_T,v_T,z_T)$, writing their results $K,N,F,G,Z_i$ in
this section. Thus $K=K_{\rm inv}$, not the drift polynomial $K$
of IX. The exact divisions defining $f_5,f_6,f_7$ remain the polynomial
divisions of X, Proposition 3.2; no rational substitute for them is used.

**Lemma 17.2 (Generic-section certificates).** Over each component
function field, and over every extension of that field,

$$
\gcd(K,N)=1,\qquad \operatorname{mon}(\gcd(F,G))=x-a_T.
\tag{17.1}
$$

There is no point of $\mathcal U$ over the generic point of $T=0$
with $m=z_T$.

Proof. The two line rows identify their component fields with
$\mathbb C(t)$, $t=v$. For the conic, substitute $v=84+t(p-24)$:

$$
Q_2(p,84+t(p-24))=(p-24)
\bigl((3t^2-38t+120)p-72t^2+1026t-3672\bigr).
\tag{17.2}
$$

The polynomial $Q_2$ is absolutely irreducible: its discriminant in $p$
is $4(v^2+1200v+48960)$, whose two roots are simple, hence this
polynomial is not a square even in $\mathbb C(v)$. The linear factor
$p-24$ is not $Q_2$. In its function field $p-24$ is therefore a
unit, so (17.2) yields exactly the conic row. Conversely direct substitution
gives $Q_2(p_T,v_T)=0$ and

$$
p_T-24=-\frac{6(19t-132)}{(t-6)(3t-20)},\qquad
v_T-84=t(p_T-24).
\tag{17.3}
$$

The resulting nonconstant rational parametrization and the inverse
$t=(v-84)/(p-24)$ identify its field with $\mathbb C(t)$.
The denominators $t-6,3t-20,t-138$ in the table are nonzero
field elements; all numerical denominators are nonzero constants.
In particular these are the literal XI, (11.3)–(11.4), terminal
sections over the actual divisor fields.

Here are small exact certificates for (17.1). Substitution into the
four $f_i$ and the three $Z_i$ of X gives the following rational
identities. The entries in the last column are $(Z_0,Z_1,Z_2)/K$
evaluated at $x=a_T$.

| $T$ | $K(a_T)$ | $N(a_T)/K(a_T)$ | $(Z_0,Z_1,Z_2)(a_T)/K(a_T)$ |
| --- | --- | --- | --- |
| $T_{55}$ | $(8t^4+387t^3-16308t^2-508005t+4094064)/1185921$ | $24$ | $(-24/5,0,9/5)$ |
| $T_{58}$ | $2(2063t^4+103236t^3-3802464t^2-68896656t+1049336208)/(t-138)^4$ | $(660-t)/29$ | $(0,0,0)$ |
| $Q_2$ | $-6$ | $24$ | $(24(t-8)/(3t-20),0,-27(t-8)/(5(t-6)))$ |

Each $K(a_T)$ is nonzero. These identities are obtained simply by
inserting $a_T$ in X, (2.5) and (3.1), and multiplying by the displayed
denominators. For example their constant numerators at $t=0$ in the
first two $K$ entries are $4094064$ and $2098672416$.
They give $F(a_T)=G(a_T)=0$: for $F$ use the identity

$$
F=5K^2\bigl(H_0(H_2+2d-294/5)-dH_2\bigr),\quad
H_i=Z_i/K,\quad d=N/K.
\tag{17.4}
$$

The last column makes its right side zero in each row. For $G$, in
the first and third rows $Z_1=0$ and $L=24K-N=0$, hence also
$Z=xZ_1-L=0$ in X, (3.1). In the second row $Z_0=Z_2=0$,
so $D_*=W_*=0$, which also makes $G=0$. Thus
$F_1=F/(x-a_T)$ and $G_1=G/(x-a_T)$ are exact polynomials
in $\mathbb Q(t)[x]$.

For completeness the remaining coprimalities have the following
finite algebra certificates. A vector $[c_0,\ldots,c_n]$ denotes
$\sum c_ix^i$ in $\mathbb F_{101}[x]$. In the next two tables,
reduce the specified exact polynomials by the ring map $t\mapsto0$
and reduction modulo $101$. Their coefficient denominators are units
in $D=\mathbb Z[t]_{(101,t)}$: the circuits and monic division by
$x-a_T$ use only the constant denominators in the table and
$t-138,t-6,3t-20$. The reduced input vectors are:

| $T$ | input | vector |
| --- | --- | --- |
| all | $K$ | $[95,86,18,29,8]$ |
| $T_{55}$ | $N$ | $[58,61,26,91,43]$ |
| $T_{58}$ | $N$ | $[58,37,79,73,43]$ |
| $Q_2$ | $N$ | $[58,25,32,86,43]$ |
| $T_{55}$ | $F_1$ | $[63,72,50,26,20,77,67]$ |
| $T_{55}$ | $G_1$ | $[11,3,16,17,38,78,82,71,72,30,40,96,64,1,86,84,87,32,58,15]$ |
| $T_{58}$ | $F_1$ | $[88,13,60,19,65,22,30]$ |
| $T_{58}$ | $G_1$ | $[36,56,68,44,45,71,95,8,94,85,37,37,75,73,16,10,9,52,75,46]$ |
| $Q_2$ | $F_1$ | $[51,53,67,0,79,96,37]$ |
| $Q_2$ | $G_1$ | $[0,47,79,64,58,52,65,4,68,53,25,84,13,64,87,47,82,3,88,29]$ |

The degrees of $K,N,F_1,G_1$ before and after this map are respectively
$4,4,6,19$ in every row. In particular their leading coefficients are
units of $D$. Starting with the indicated ordered pair, take the ordinary
polynomial remainder and divide each nonzero remainder by its leading
coefficient. For the cofactor pair start with $(G_1,F_1)$. The complete
successive nonzero monic remainder vectors are:

| $T$ | pair | successive vectors |
| --- | --- | --- |
| $T_{55}$ | $(K,N)$ | $[35,85,26,1];\ [19,9,1];\ [66,1];\ [1]$ |
| $T_{58}$ | $(K,N)$ | $[21,65,84,1];\ [17,0,1];\ [78,1];\ [1]$ |
| $Q_2$ | $(K,N)$ | $[39,76,47,1];\ [93,14,1];\ [0,1];\ [1]$ |
| $T_{55}$ | $(G_1,F_1)$ | $[97,58,34,90,50,1];\ [0,87,73,71,1];\ [15,77,5,1];\ [58,15,1];\ [34,1];\ [1]$ |
| $T_{58}$ | $(G_1,F_1)$ | $[72,99,46,14,30,1];\ [10,59,76,91,1];\ [57,39,8,1];\ [18,29,1];\ [56,1];\ [1]$ |
| $Q_2$ | $(G_1,F_1)$ | $[97,29,70,70,87,1];\ [72,23,2,76,1];\ [71,33,89,1];\ [100,86,1];\ [15,1];\ [1]$ |

These are polynomial-division identities with the displayed input
vectors; after $[1]$ the remainder is zero. They certify that the two
resultants in $D$ are units, equivalently that no nonconstant common
factor exists over $\mathbb Q(t)$. One can also see the lifting directly:
$D$ is a normal UFD, and division by the unit leading coefficients
makes both input polynomials monic over $D$. Any monic common factor
over its fraction field $\mathbb Q(t)$ has coefficients integral over
$D$, hence in $D$. Its monic reduction would retain positive degree
and contradict the displayed final remainder $[1]$.
This proves $\gcd(K,N)=\gcd(F_1,G_1)=1$ over $\mathbb Q(t)$.
Together with the exact factors $x-a_T$, it proves (17.1).
Bézout identities over $\mathbb Q(t)[x]$ remain identities over
$\mathbb C(t)$ and every further field extension. No assertion about
a gcd at an exceptional numerical value of $t$ is involved.

Now suppose a source point over the algebraic closure of a component
field has $m=z_T$. The tail and original clock equations give
$Kd=N$ by X, Proposition 2.2. The first coprimality in (17.1)
excludes $K=0$. With $d=N/K$, the actual source gives $F=G=0$
by X, (3.8) and (3.11), whose clearing factors are units on
$\mathcal U$. Hence $x=a_T$. In the $T_{55}$ row the table forces
$d=24$, contrary to $e\ne0$. In the $T_{58}$ row it forces
$H_0=H_2=0$, contrary to (16.8) in characteristic zero. In the
$Q_2$ row it forces $x=0$, whereas $x=N_s/(bU)$ is already a
unit on $X_s$. This proves all three generic source exclusions. ∎

## 18. Every-point separation through the original exceptional divisor

**Theorem 18.1 (Nonsingular M separation outside the literal core).**
The map

$$
\phi:\mathcal U\cap D(C_{121})\longrightarrow Y,\qquad
W\longmapsto(p(W),v(W),m(W))
\tag{18.1}
$$

is injective on geometric points. In particular the conclusion includes
every intersection with the original $H=0$ that lies in the stated
source chart. For original strict-real off-$24$ nonsingular endpoints,
equality of $(p,v,m)$ outside $C_{121}=0$ implies equality of the
complete source, entire gain and drift.

Proof. Identify $\mathcal U$ with the normalization open of Proposition
16.3. The conductor of the finite birational inclusion $A\subset B$ is

$$
I=\operatorname{Hom}_A(B,A)
 =\{h\in A:hB\subset A\}\subset B.
\tag{18.2}
$$

Indeed, after tensoring with the common fraction field $K_s$, every
$A$-linear map is multiplication by a scalar; evaluation at $1$ puts
that scalar in $A$. This identifies the two expressions and their
$B$-module structures. The ideal is nonzero, since clearing denominators
of finitely many $A$-generators of $B$ gives a nonzero $h$ with
$hB\subset A$.

We first show that $I\mathcal O_{\mathcal U}$ is invertible. This is
where the smoothness of the actual source is essential. The polynomial
ring $S_b=\mathbb C[p,v,z]$ has dualizing complex $S_b[3]$.
The resolution $0\to S_b\xrightarrow{f_{\rm ter}}S_b\to A\to0$
gives $R\operatorname{Hom}_{S_b}(A,S_b[3])=A[2]$.
Finite duality therefore gives the dualizing complex
$R\operatorname{Hom}_A(B,A[2])$ of $B$.
Here the precise classical results are Stacks Project, Dualizing
Complexes, Lemmas 47.15.6, 47.15.8 and 47.15.9 (localization, finite
maps and quotients), and Lemmas 47.20.2 and 47.21.3–47.21.4
(Cohen–Macaulay and regular/Gorenstein local rings); their statements
are in the [dualizing-complexes source](https://github.com/stacks/stacks-project/blob/master/dualizing.tex).
The rings in this application are the Noetherian finite-type rings
$S_b,A,B$, and $A\to B$ is the finite map of Proposition 16.3.

The normal surface $\operatorname{Spec}(B)$ is Cohen–Macaulay:
normality gives Serre's $S_2$ condition, and every local dimension is
at most two (Serre's criterion, Lemma 10.157.4,
[Tag 031S](https://stacks.math.columbia.edu/tag/031S)).
Finite duality here preserves normalization at closed points. Since $B$
is equidimensional of dimension two and Cohen–Macaulay, its dualizing
complex is concentrated in degree $-2$; its canonical module is therefore
$H^{-2}(R\operatorname{Hom}_A(B,A[2]))=I$.
Localizing to the smooth open $\mathcal U$ gives an invertible canonical
module, since its local rings are regular. Thus the nonzero ideal
$\mathcal I=I\mathcal O_{\mathcal U}$ is invertible. At any point
where it is not the unit ideal, a local nonzero generator has a
height-one zero component through that point: a minimal prime over
this nonunit principal ideal has height one by the principal ideal
theorem and the domain property. This rules out an isolated
codimension-two failure unless a conductor divisor passes through it.

We now exclude every conductor divisor on $\mathcal U\cap D(C_{121})$.
Let $T$ be an irreducible polynomial of $R_b$ and localize at its
generic point. The ring $O=(R_b)_{(T)}$ is a DVR, and both $A_O$
and $B_O$ are finite torsion-free, hence free, $O$-modules of rank
eighteen. The total quotient field extension is separable in
characteristic zero. If $C$ is the inclusion matrix in free bases,
the trace matrices satisfy $G_A=C^{\mathsf t}G_BC$. Smith normal
form over $O$ gives

$$
\operatorname{ord}_T\operatorname{Disc}(A_O/O)
=\operatorname{ord}_T\operatorname{Disc}(B_O/O)
 +2\operatorname{length}_O(B_O/A_O).
\tag{18.3}
$$

Both discriminants are nonzero; the first is
$\operatorname{Disc}_z(f_{\rm ter})$ in the power basis. The trace
of multiplication on the integral free algebra $B_O$ has entries in
$O$, so its discriminant has nonnegative valuation. A valuation at
most one on the left of (18.3) therefore forces $A_O=B_O$.

By (14.1) and the constant normalization (16.5),

$$
\operatorname{Disc}_z(f_{\rm ter})
=\frac{w}{c^{34}}B_{51}T_5^2C_{121}^2.
\tag{18.4}
$$

The polynomial $B_{51}$ is geometrically squarefree: it is squarefree
over the characteristic-zero field $\mathbb Q$, so separable
extension of its coefficient field cannot create a repeated prime
factor. This can also be checked by the criterion that the polynomial
and all its partial derivatives have no common prime factor, which is
preserved by extending a perfect field. The same holds for $T_5$;
its four factors are distinct over $\mathbb C$, including the absolutely
irreducible $Q_2$ proved in Lemma 17.2. Away from $C_{121}$,
(18.3)–(18.4) leave only the four factors of $T_5$ as possible base
images of conductor divisors.

To justify that this covers every divisor, the composite
$\operatorname{Spec}(B)\to\operatorname{Spec}(R_b)$ is finite.
The closure in $\operatorname{Spec}(B)$ of a divisor in the open
$\mathcal U$ is a height-one integral curve. It has a one-dimensional
image under this finite map, since its coordinate
ring is integral and finite over that of its image. Hence it maps
onto a base divisor, not only to an isolated base point. Its generic
point in $\mathcal U$ cannot lie over $p-24=0$ by (16.4).

Fix one of $T_{55},T_{58},Q_2$ and work at its base DVR $O$.
Theorem 14.2 gives $\gcd(C_{121},H)=1$, and each of these $T$
divides $H$: $T_5^2\mid E$ by Lemma 11.2 and $E$ is in the
original inventory (9.3). Thus $C_{121}$ is a unit in $O$.
The valuation in (18.4) is $2+\epsilon$, where
$\epsilon=\operatorname{ord}_T(B_{51})\in\{0,1\}$.
No coprimality between $B_{51}$ and $T$ is required.

Translate $z$ by the literal lift $z_T$ of Definition 17.1, writing
$y=z-z_T$. The denominators of these lifts are constants, hence
units in $O$. Lemma 11.2 gives

$$
f_{\rm ter}(z_T)\in(T^2),\qquad
(f_{\rm ter})_z(z_T)\in(T),\qquad
(f_{\rm ter})_{zz}(z_T)\in O^*.
\tag{18.5}
$$

For the line rows these follow from the value and transverse $p$
derivative identities (11.3); $z_T$ there is independent of $p$
and $\partial_pT$ is a nonzero constant. For $Q_2$ they are
literally (11.4), since powers of $10$ and $c$ are units. Thus the
residual polynomial is $y^2\overline h$ with
$\overline h(0)\ne0$, and the residual root has exactly multiplicity
two. The completion $\widehat O$ is henselian. The coprime monic
factorization form of Hensel's lemma (Lemmas 10.153.3 and 10.153.9,
[Tag 04GE](https://stacks.math.columbia.edu/tag/04GE)) applies with
residual factors $y^2,\overline h$, giving

$$
f_{\rm ter}(y+z_T)=(y^2+by+a)h(y)
\quad\text{in }\widehat O[y],\qquad h(0)\in\widehat O^*.
\tag{18.6}
$$

The cross-resultant is a unit. Comparing constants and then linear
coefficients with (18.5) gives $a\in(T^2)$ and $b\in(T)$.
The quadratic discriminant $b^2-4a$ has valuation at least two.
Discriminant multiplicativity and (18.4) then give
$\operatorname{ord}_T\operatorname{Disc}(h)\le1$.
The degree-sixteen complementary order $\widehat O[y]/(h)$ is
therefore normal by the same trace/index argument (18.3), applied
to its integral closure. Its total generic algebra is separable,
as its nonzero discriminant shows. Its integral closure is finite,
being the corresponding direct factor of the finite product of complete
DVRs described in the next paragraph. Consequently every generic
conductor point over $T$ must be on the
quadratic block, with residual value $m=z_T$.

Here completion does not introduce or discard a possible conductor
point. Indeed $B_O$ is a semilocal normal one-dimensional ring; its
localizations at the maximal ideals are DVRs. Its $T$-adic completion
is the product of their complete DVRs and is normal. It is finite
birational over $A_O\otimes_O\widehat O$ in its total generic
algebra, hence is precisely that algebra's integral closure. The
coprime factorization (18.6) splits the latter into its quadratic and
complementary parts. Finally the conductor (18.2) commutes with flat
completion, since $B_O$ is a finitely presented $A_O$-module: apply flat base
change to the kernel describing $\operatorname{Hom}_{A_O}(B_O,A_O)$
from a finite presentation. Faithful flatness of completion descends the statement that the
complementary part has unit conductor. Thus the preceding restriction
to the residual double section holds at the original generic divisor.
A generic point of a divisor above $T$ has residue field finite over
$\mathbb C(T)$, since $B$ is finite over $R_b$. Lemma 17.2 excludes
every point of $\mathcal U$ on that section after this field extension.
No conductor divisor on
$\mathcal U\cap D(C_{121})$ remains.

Invertibility of $\mathcal I$ now makes it the unit ideal at every
point of this open: a nonunit stalk would yield the excluded
height-one component. This argument includes all intersections of
the original factors of $H$, with no specialization of the generic
gcds of Lemma 17.2 to those intersections.

Finally let $q\in\mathcal U\cap D(C_{121})$ lie over $y\in Y$.
Unit conductor at $q$ gives some $h\in I$ not in the prime $q$.
Since $I\subset A$, $h$ also avoids the prime $y=q\cap A$.
The inclusion $hB\subset A$ implies $B_h=A_h$. Thus there is
exactly one normalization point over $y$, and the open immersion
of Proposition 16.3 makes $\phi$ injective there. All these statements
persist after algebraically closed extension of constants. Formula
(16.2) identifies equality of source points with equality of the
entire gain and drift. Proposition 16.2 gives the asserted original
real endpoint conclusion. ∎

## 19. The finite all-off24 independent-pair outer restriction

**Theorem 19.1 (Original four-world necessary base set).** Let
$p,v\in\mathbb R$, $p\ne24$, and let $W_0,W_1,W_2,W_3$ be
complete original worlds in one entire child $C(p,v)$, with

$$
W_0\ne W_1,\quad a(W_0)=a(W_1),\qquad
W_2\ne W_3,\quad m(W_2)=m(W_3).
\tag{19.1}
$$

Each world has its own nonzero real polynomial gain of degree at most
three and its own fixed real drift. Cross-pair overlaps of sizes
$0,1,2$ and independent auxiliary M responses at the J endpoints are
permitted. Then

$$
C_{121}(p,v)=0,\qquad H(p,v)N_J(p,v)=0.
\tag{19.2}
$$

Consequently every such base belongs to

$$
V_{\mathbb C}(C_{121},HN_J)\cap D(p-24),
\tag{19.3}
$$

a finite, possibly empty complex set.

Proof. S, Corollary 18.2, applied to the entire child in (19.1),
excludes a singular endpoint of the chosen M pair. It imposes no
nonsingularity condition on the chosen J pair or on unused worlds.
Both $W_2,W_3$ therefore lie in $\mathcal U$ by Proposition 16.2.
If $C_{121}(p,v)\ne0$, Theorem 18.1 applied to their common
$(p,v,m)$ makes these two complete worlds equal, contradicting
(19.1). This proves the first equality in (19.2) for every original
off-$24$ base, including $H=0$.

If $H(p,v)\ne0$, the original all-world implication S, Theorem 4.3
and Lemma 9.9, applies to the chosen distinct equal-J pair and gives
$N_J(p,v)=0$. If $H(p,v)=0$, the second equality in (19.2) already
holds. No equality between $m(W_0),m(W_1)$ and the common M answer
has been used. The reasoning depends only on the two stated
within-pair distinctness conditions, so all permitted overlaps remain.

Theorem 14.2 gives the literal coprimalities
$\gcd(C_{121},H)=\gcd(C_{121},N_J)=1$. Therefore
$C_{121}$ and $HN_J$ are coprime also over $\mathbb C$, and the
plane-curve intersection argument in that theorem makes (19.3)
finite, possibly empty. This reuses the unchanged original five-norm
inventory and its literal $N_J$, rather than replacing its exceptional
set or imposing a common gain or drift.

The source-specific consequence is (18.1) and its application (19.2).
Normalization, finite duality, Hensel factorization, DVR trace indices
and finite plane intersection are the classical intermediate results
cited in their applications above. These implications do not provide
real lifts, a list or count of the complex bases, existence or absence
of a real configuration, or an assertion at $p=24$.
All clocks and read conditions remain (15.1): the initial read and
every post-atom read are immediate and counted, and J and M at
clock seven are alternatives on the original trajectory. The argument
introduces no reset, copy, idle, skipped read, unread composite, extra
port or renumbered clock. It establishes no fixed48, rootQ,
common-ancestor, both-child or global eight/nine-read conclusion. ∎

## 追加锚（本行以下为增补区）
