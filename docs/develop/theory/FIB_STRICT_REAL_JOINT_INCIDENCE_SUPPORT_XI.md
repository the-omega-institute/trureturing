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
