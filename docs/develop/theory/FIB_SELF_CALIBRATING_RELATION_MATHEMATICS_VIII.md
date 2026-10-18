# FIB 自校准关系数学 VIII

## 1. 完整目标、字面历史与已知初根层

**定义 1.1（原时钟的完整三次合同）。** Let $\mathcal W_3$ be the set of
triples $W=(P,g,\delta)$ in which $P$ is a strictly entrywise positive
real $2\times2$ matrix of rank one and trace one,
$0\ne g\in\mathbb R[t]$ has degree at most three, and
$\delta\in\mathbb R$. The known atoms and cumulative matrices are

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{M,J\}.
                                                               \tag{1.1}
$$

The reading at original clock $i$ is

$$
z_i(W)=g(i)\operatorname{tr}(A_iP)+\delta.                       \tag{1.2}
$$

The initial reading counts, and every atom is immediately followed by
its reading on one unresettable, uncopyable trajectory. Eight total
readings use clocks $0,\ldots,7$. Skipped readings, unread compound
actions, empty-action readings, clock renumbering and additional
observation ports are excluded. Actions, stopping and the returned
complete target may be arbitrary deterministic functions of the
entire actual history. No regularity or computability condition is
imposed. All gain signs, lower actual degrees, sampled roots and
repeated roots are retained.

This is the normalized target of
[I, Definitions 39.1 and 44.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md)
and [II, Definition 51.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md).
An unnormalized positive rank-one source $R$ and gain $G$ represent

$$
(P,g,\delta)=
\left(\frac R{\operatorname{tr}R},(\operatorname{tr}R)G,\delta\right).
                                                               \tag{1.3}
$$

Thus positive source scaling is removed, while drift remains a
coordinate of the complete target. All target distinctions below
refer to this triple, rather than just a source or a gain ray.

**定义 1.2（JMMJ 父历史与 JMMJM 实际子历史）。** For arbitrary
$D_0,Y,z\in\mathbb R$ and $\lambda\ne0$, put

$$
\begin{aligned}
H_J^-&=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
                         M,D_0+312\lambda/5),\\
H_J(Y)&=(H_J^-,J,Y),\\
H_{JM}(Y,z)&=(H_J(Y),M,z).
\end{aligned}                                                   \tag{1.4}
$$

These are precisely the histories in
[V, Definition 5.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)
and [VII, Definition 1.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md).
They contain respectively four, five and six readings. Their action
words are chronological; matrix multiplication follows (1.1).
Write $\mathcal F(H)$ for all complete targets realizing every action
and every reading of the literal history $H$. The symbol $D_0$
denotes the initial observed value, not an unrestricted target's drift.

The affine normalization

$$
f=g/\lambda,\qquad d=(\delta-D_0)/\lambda,\qquad
y_i=(z_i-D_0)/\lambda                                         \tag{1.5}
$$

is a bijection on complete targets and histories for either sign of
$\lambda$. In particular, $y_4=(Y-D_0)/\lambda$ and
$y_5=(z-D_0)/\lambda$, and the six normalized readings are
$0,24,48,312/5,y_4,y_5$. Sources and clocks are unchanged.

**定义 1.3（已知初根层与剩余失败谓词）。** Define the whole known classes

$$
\begin{aligned}
K_0(Y,z)&=\mathcal F(H_{JM}(Y,z))\cap\{g(0)=0\},\\
C_0(Y)&=\mathcal F(H_J(Y))\cap\{g(0)=0\},\\
C_0^-&=\mathcal F(H_J^-)\cap\{g(0)=0\}.
\end{aligned}                                                   \tag{1.6}
$$

Since $\operatorname{tr}P=1$, every target in these histories satisfies
$g(0)+\delta=D_0$. Thus the initial-root promise is exactly
$\delta=D_0$, or $f(0)=d=0$ in (1.5). It is a prior condition on the
known class; it is not inferred from the initial reading alone.
No gain ray, terminal root or cardinality bound is included in (1.6).

For a known $K\subseteq\mathcal F(H)$ ending at clock $i$ and
$0\le s\le7-i$, use
[II, Definition 56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md):

$$
\begin{aligned}
L_0(K,H)&\Longleftrightarrow |K|\ge2,\\
L_{s+1}(K,H)&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists v\in\mathbb R:\
L_s(K\cap\mathcal F(H,E,v),(H,E,v)).
\end{aligned}                                                   \tag{1.7}
$$

The recursive line applies for $0\le s<7-i$.
Here each child retains the same fixed worlds and all their ancestor
equations. The negation means that one strategy recovers every member
of the whole known set within the remaining horizon, including the
possibility of earlier stopping. Values predicted for an unchosen
action are mathematical functions of these worlds, not acquired data.

## 2. 整个 JMMJM 初根层的实际逆

**定理 2.1（非零第五响应逆及两支整层恢复）。** For every
$D_0,Y,z\in\mathbb R$ and $\lambda\ne0$, the following policy
recovers every complete target in $K_0(Y,z)$, without any restriction
on the cardinality of this class:

$$
\begin{array}{c|c|c|c}
\text{actual fifth response}&\text{sixth atom}&\text{seventh atom}
                                      &\text{total readings}\\ \hline
z=D_0&M&\text{stop at clock six}&7\\
z\ne D_0&J&J&8
\end{array}                                                     \tag{2.1}
$$

Each selected atom is immediately read. The nonzero fifth-response
branch requires no terminal-root promise. The zero branch is the
application of [V, Theorem 5.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md)
specified below.

Proof. The cumulative matrices at clocks $0,\ldots,5$ are

$$
\begin{gathered}
I,\ J,\ L,\ J+L,\ C,\ Q,\\
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
J+L=\begin{pmatrix}1&1\\2&1\end{pmatrix},\\
C=J(J+L)=\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad
Q=MC=\begin{pmatrix}1&1\\3&2\end{pmatrix}.
\end{gathered}                                                   \tag{2.2}
$$

For a member of $K_0(Y,z)$, set

$$
\begin{gathered}
u=\operatorname{tr}(JP)>0,\qquad R=P/u,\qquad
T=\operatorname{tr}R=1/u,\qquad F=ug/\lambda,\\
r=\operatorname{tr}(LR)>0,\qquad a=R_{11}.
\end{gathered}                                                   \tag{2.3}
$$

The complete target is recovered from these coordinates by

$$
(P,g,\delta)=\left(R/T,\lambda T F,D_0\right).                 \tag{2.4}
$$

Indeed $\operatorname{tr}(JR)=1$ and
$\operatorname{tr}(LR)=T+R_{12}=r$, so

$$
R=\begin{pmatrix}
a&r-T\\1-r+T&T-a
\end{pmatrix}.                                                  \tag{2.5}
$$

Strict positivity and rank one are exactly

$$
\begin{gathered}
r>0,\qquad 0<a<T,\qquad r-1<T<r,\\
a(T-a)=(r-T)(1-r+T).
\end{gathered}                                                   \tag{2.6}
$$

In particular, $T>0$. The first four actual readings imply

$$
F(0)=0,\quad F(1)=24,\quad F(2)=48/r,\quad
F(3)=\frac{312}{5(1+r)}.                                      \tag{2.7}
$$

They determine the entire degree-at-most-three polynomial. More
explicitly, let

$$
\ell_i(t)=\prod_{\substack{0\le j\le3\\j\ne i}}\frac{t-j}{i-j},
\qquad
F_r(t)=24\ell_1(t)+\frac{48}{r}\ell_2(t)
                         +\frac{312}{5(1+r)}\ell_3(t).
                                                               \tag{2.8}
$$

Then $F=F_r$. Evaluating this expression gives

$$
\begin{aligned}
F_r(4)&=\frac{96(5r^2+3r-15)}{5r(r+1)},\\
F_r(5)&=\frac{24(5r-8)(3r+5)}{r(r+1)},\\
F_r(6)&=\frac{48(18r^2-r-45)}{r(r+1)},\\
F_r(7)&=\frac{168(5r-8)(2r+3)}{r(r+1)}.
\end{aligned}                                                   \tag{2.9}
$$

All denominators $r(r+1)$ are positive. Multiplication in (2.2)
also gives the four trace identities

$$
\begin{aligned}
\operatorname{tr}(CR)&=T+a+1,\\
\operatorname{tr}(QR)&=1+2r-a,\\
\operatorname{tr}(JQR)&=2(T+a+1)-r,\\
\operatorname{tr}(MQR)&=T+2+2r.
\end{aligned}                                                   \tag{2.10}
$$

Each trace is strictly positive: the corresponding matrix is nonzero
and entrywise nonnegative, and $R$ is strictly positive. In these
coordinates the two remaining ancestor equations are exactly

$$
y_4=F_r(4)(T+a+1),\qquad y_5=F_r(5)(1+2r-a).                 \tag{2.11}
$$

Conversely, any $(r,T,a)$ satisfying (2.6) and (2.11), with $R$ as in
(2.5) and $F=F_r$, gives by (2.4) a legal complete target realizing
all six readings of $H_{JM}(Y,z)$. Its polynomial is nonzero because
$F_r(1)=24$. Equations (2.6), (2.8) and (2.11) therefore describe the
whole class, including the possibility that it is empty.

Suppose first that $z\ne D_0$. Equation (2.11) and positivity force
$F_r(5)\ne0$, hence $r\ne8/5$. Execute sixth $J$ and read $z_6$;
execute seventh $J$ and read $z_7$. Their cumulative matrices are
$JQ$ and $J^2Q=Q$. Thus the already acquired clock-five response and
the actual clock-seven response give

$$
\rho=\frac{z_7-D_0}{z-D_0}
=\frac{F_r(7)}{F_r(5)}
=\frac{7(2r+3)}{3r+5}.                                      \tag{2.12}
$$

The cancellation uses only the proved $5r-8\ne0$ and positive
$r,r+1,3r+5$. For $r>0$, the last function has

$$
\frac{d\rho}{dr}=\frac7{(3r+5)^2}>0,\qquad
\frac{21}{5}<\rho<\frac{14}{3},\qquad
14-3\rho=\frac7{3r+5}>0.
                                                               \tag{2.13}
$$

Consequently the actual ratio uniquely determines

$$
r=\frac{5\rho-21}{14-3\rho},\qquad
a=1+2r-\frac{y_5}{F_r(5)}.                                  \tag{2.14}
$$

If $F_r(4)\ne0$, recover

$$
T=\frac{y_4}{F_r(4)}-a-1.                                   \tag{2.15}
$$

If $F_r(4)=0$, then $5r^2+3r-15=0$ forces $r>1$, since the left
side is negative for $0<r\le1$. At this root,

$$
18r^2-r-45=\frac{45-59r}{5}<0.
                                                               \tag{2.16}
$$

Hence $F_r(6)\ne0$. The actual sixth reading, already acquired after
$J$, instead recovers

$$
T=\frac12\left(\frac{y_6}{F_r(6)}+r\right)-a-1.              \tag{2.17}
$$

If $F_r(6)=0$, (2.16) shows that $F_r(4)\ne0$, so (2.15) applies.
In particular no simultaneous zero of these two gain samples is
discarded without proof. Equations (2.5), (2.8) and (2.4) now give
the entire target. The sixth reading is not replaced by the
counterfactual response to $M$.

Suppose instead that $z=D_0$. Positivity of the clock-five trace and
(2.9) force $r=8/5$, and (2.8) becomes

$$
F_r(t)=h(t)=t(t-5)(t-7),\qquad h(4)=12,\quad h(6)=-6.
                                                               \tag{2.18}
$$

Thus this branch lies in exactly the baseline-drift, root-seven
class of V, Theorem 5.2. Apply its sixth-$M$ inverse, using the actual
response $z_6$ after that atom. In the present coordinates that
inverse is

$$
T=-\frac{y_6}{6}-\frac{26}{5},\qquad
a=\frac{y_4}{12}-T-1,
                                                               \tag{2.19}
$$

followed by (2.5) and (2.4). These are precisely V, equation (5.5):
putting $U=y_4/12$ and $V=-y_6/6$ there gives
$T=V-26/5$ and $a=U-V+21/5$. The fourth and actual sixth traces
are those in (2.10), so (2.19) uses only nonzero constant gain
samples of $h$. This reuses the published zero-response inverse;
the extension is the nonzero-response branch and the assembly of
both branches over (1.6).

For either branch, an actual compatible target supplies existence
and ensures (2.6), including strict positivity and rank one of the
reconstructed source. Every compatible target producing the same
selected readings gives the same $r,a,T,F$, so the reconstruction is
unique on the whole retained class. No division by the leading
coefficient, a root difference, $F_r(4)$ when it is zero, or $F_r(6)$
when it is zero occurs. The samples at clocks one, two and three
are nonzero by (2.7); every other compatible sample zero is handled
by the branches above. A drop in actual degree or a repeated root
does not change interpolation or any step of the inverse. The sign
of $\lambda$ is unrestricted throughout.

There are six ancestor readings. The first branch adds one actual
atom and stops at clock six; the second adds two and stops at clock
seven. Their total counts are exactly seven and eight. Empty classes
have no reachable input; on histories outside the stated classes the
policy can be completed arbitrarily. No assertion of optimality for
these counts is required. ∎

## 3. 整族消费者与非末根实际输入

**推论 3.1（变第五响应的初根整族策略与失败族必要条件）。** Every
known subset of $C_0(Y)$, finite or infinite, is recoverable within
three further readings, hence at most eight total readings. Every
known subset of $C_0^-$ is recoverable within four further readings
and the same total bound. Every known subset of $K_0(Y,z)$ is
recoverable within two further readings. In particular,

$$
\begin{aligned}
L_2(K,H_{JM}(Y,z))&\Longrightarrow
                 \exists W\in K:\ g_W(0)\ne0,\\
L_3(K,H_J(Y))&\Longrightarrow
                 \exists W\in K:\ g_W(0)\ne0,\\
L_4(K,H_J^-)&\Longrightarrow
                 \exists W\in K:\ g_W(0)\ne0
\end{aligned}                                                   \tag{3.1}
$$

for any compatible $K$ at the indicated node.

Proof. At $H_J(Y)$ execute fifth $M$ and read its actual $z$, then
use the corresponding branch of Theorem 2.1 on the retained subset.
This is one rule on every possible actual fifth-response fiber,
without assuming that $z$ is constant on the known input class.
Its two possible budgets are $5+1+1=7$ and $5+1+2=8$.
At $H_J^-$ first execute fourth $J$ and read $Y$, then apply the
same rule, with budgets $4+1+1+1=7$ and $4+1+1+2=8$.
Restriction of these policies to any known subset preserves
correctness. If one of the losing sets in (3.1) consisted entirely
of initial-root targets, the corresponding whole-class policy would
contradict (1.7).

The conclusion is noncontainment in one promised stratum. It does
not assert that a losing family exists or that it contains both
initial-root and noninitial-root targets, or different drifts.
At each of these literal histories $g(0)\ne0$ is equivalent to
$\delta\ne D_0$; the existential conclusion does not require two
different values of $\delta$ within the family.

For the separate history
$H_4(Y)=(0,M,1,M,23/7,J,331/35,M,Y)$, the analogous assertion that
an $L_3$ family cannot lie entirely in $g(0)=0$ is already
[II, Theorem 62.1 and Proposition 63.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md):
on that history $g(0)=0$ is exactly $\delta=0$. Its rule is fifth
$J$, sixth $J$, then seventh $M$ exactly when the actual sixth
response plus $Y/2$ is zero, otherwise seventh $J$. The exceptional
input is II, Proposition 63.3. These are the existing $MMJM$
decoder, consequence and consumer; no identification of that
history with $JMMJM$ is used in (3.1). ∎

**命题 3.2（非零第五支的非末根消费者）。** The fixed target

$$
P_*=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
g_*(t)=\frac4{25}t(t^2-53t+202),\qquad \delta_*=0
                                                               \tag{3.2}
$$

realizes the whole chronological word $JMMJMJJ$ with the eight
actual readings

$$
\left(0,24,48,\frac{312}{5},\frac{48}{5},-\frac{532}{5},
                         -\frac{1344}{5},-\frac{2352}{5}\right).
                                                               \tag{3.3}
$$

It has $g_*(0)=0$, $g_*(7)=-672/5\ne0$, and belongs to the
nonzero fifth-response branch of Theorem 2.1 at $D_0=0,\lambda=1$.

Proof. The displayed source is strictly positive, rank one and
trace one. The polynomial is nonzero and cubic. The traces at
clocks $0,\ldots,7$ along that word, using (2.2), $JQ$ and $Q$, are

$$
\left(1,1,\frac32,\frac52,\frac52,\frac72,\frac72,\frac72\right).
                                                               \tag{3.4}
$$

Multiplying these traces by the corresponding samples of $g_*$
gives (3.3). In particular $u=T=1$, $r=3/2$ and $a=1/2$ in
(2.3). The actual ratio is $\rho=84/19$, so (2.14) returns $r=3/2$;
then (2.14) and (2.15) return $a=1/2$ and $T=1$.
This is an actual input without a terminal-root promise. ∎

## 4. 同一六读历史中的异漂移连续实际族

**定义 4.1（正来源参数与实际第四、第五响应）。** Put

$$
H^*=\left(0,J,24,M,48,M,\frac{312}{5},J,\frac{48}{5},
                                                  M,-\frac{532}{5}\right).
                                                               \tag{4.1}
$$

For $\alpha,\beta>0$ and $d\in\mathbb R$, define

$$
\begin{gathered}
P(\alpha,\beta)=\frac1{1+\alpha\beta}
                 \begin{pmatrix}1&\beta\\\alpha&\alpha\beta\end{pmatrix},\\
U=\operatorname{tr}(JP)=\frac{\alpha+\beta}{1+\alpha\beta},\qquad
V=\operatorname{tr}(LP)=1+\frac{\beta}{1+\alpha\beta},\qquad
A=P_{11}=\frac1{1+\alpha\beta}.
\end{gathered}                                                   \tag{4.2}
$$

This source is strictly positive, rank one and trace one. Every such
source has these unique positive parameters:
$\alpha=P_{21}/P_{11}$ and $\beta=P_{12}/P_{11}$, since rank one
gives $P_{22}=\alpha\beta P_{11}$ and trace one gives
$P_{11}=1/(1+\alpha\beta)$. In particular $U,V,U+V$ are positive.

Using the same four Lagrange polynomials as in (2.8), let

$$
G_{\alpha,\beta,d}(t)=
-d\ell_0(t)+\frac{24-d}{U}\ell_1(t)
+\frac{48-d}{V}\ell_2(t)
+\frac{312/5-d}{U+V}\ell_3(t).
                                                               \tag{4.3}
$$

With drift $d$, the four actual readings at clocks $0,1,2,3$ along
$JMM$ are exactly $0,24,48,312/5$. No root promise is imposed on
this interpolant. Define its actual fourth-$J$ and fifth-$M$
responses by

$$
\begin{aligned}
\mathcal Y(\alpha,\beta,d)&=d+G_{\alpha,\beta,d}(4)(1+A+U),\\
\mathcal Z(\alpha,\beta,d)&=d+G_{\alpha,\beta,d}(5)(U+2V-A).
\end{aligned}                                                   \tag{4.4}
$$

The trace factors are $\operatorname{tr}(CP)=1+A+U$ and
$\operatorname{tr}(QP)=U+2V-A$. The gain samples in these actual
response functions are explicitly

$$
\begin{aligned}
G_{\alpha,\beta,d}(4)
 &=d+\frac{4(24-d)}U-\frac{6(48-d)}V
                              +\frac{4(312/5-d)}{U+V},\\
G_{\alpha,\beta,d}(5)
 &=4d+\frac{15(24-d)}U-\frac{20(48-d)}V
                              +\frac{10(312/5-d)}{U+V}.
\end{aligned}                                                   \tag{4.5}
$$

Thus (4.4) specifies rational functions of the three parameters,
rather than unconstrained proposed response values.

**定理 4.2（固定 H* 的异漂移连续实现）。** There are $\eta>0$ and
smooth positive functions $\alpha(d),\beta(d)$ for $|d|<\eta$,
with $\alpha(0)=\beta(0)=1$, such that the fixed complete targets

$$
W_d=\left(P(\alpha(d),\beta(d)),
          G_{\alpha(d),\beta(d),d},d\right)
                                                               \tag{4.6}
$$

all belong to $\mathcal F(H^*)$. They satisfy
$g_{W_d}(0)=-d$ and $\delta(W_d)=d$. Distinct $d$ give distinct
complete targets. The center is the target (3.2); every $d\ne0$
lies outside the initial-root stratum.

Proof. At $(\alpha,\beta,d)=(1,1,0)$, (4.2) gives
$U=1,V=3/2,A=1/2$. The polynomial (4.3) agrees with $g_*$ at
$0,1,2,3$, hence is exactly $g_*$. Thus

$$
(\mathcal Y,\mathcal Z)(1,1,0)
                 =\left(\frac{48}{5},-\frac{532}{5}\right).
                                                               \tag{4.7}
$$

For an explicit Jacobian computation, keep $d=0$ and temporarily
regard $U,V,A$ as independent coordinates in (4.4)–(4.5). At
$(U,V,A)=(1,3/2,1/2)$, differentiation at fixed $U$ gives

$$
\frac{\partial(\mathcal Y,\mathcal Z)}{\partial(V,A)}
=\begin{pmatrix}
5504/25&96/25\\81232/75&152/5
\end{pmatrix}.
                                                               \tag{4.8}
$$

For example, at $d=0$ the $V$ derivatives of the two gain samples
in (4.5) are

$$
\partial_VG(4)=\frac{288}{V^2}-\frac{1248}{5(U+V)^2},\qquad
\partial_VG(5)=\frac{960}{V^2}-\frac{624}{(U+V)^2}.
                                                               \tag{4.9}
$$

Multiplication by the factors in (4.4), including the derivative
$\partial_V(U+2V-A)=2$, yields the first column of (4.8).
The second is $(G(4),-G(5))^{\mathsf T}$ at the center.
Differentiating (4.2) at $(\alpha,\beta)=(1,1)$ gives

$$
\partial_\alpha U=\partial_\beta U=0,\qquad
\frac{\partial(V,A)}{\partial(\alpha,\beta)}
=\begin{pmatrix}-1/4&1/4\\-1/4&-1/4\end{pmatrix}.
                                                               \tag{4.10}
$$

Although $U$ varies away from the center, its two first derivatives
vanish at the center, so the ordinary chain rule uses exactly the
product of (4.8) and (4.10). It follows that

$$
\begin{gathered}
\left.\frac{\partial(\mathcal Y,\mathcal Z)}
{\partial(\alpha,\beta)}\right|_{(1,1,0)}
=\begin{pmatrix}
-56&1352/25\\-20878/75&19738/75
\end{pmatrix},\\
\det\left.\frac{\partial(\mathcal Y,\mathcal Z)}
{\partial(\alpha,\beta)}\right|_{(1,1,0)}
=\frac{197952}{625}\ne0.
\end{gathered}                                                   \tag{4.11}
$$

On the open domain $\alpha,\beta>0$, the denominators in
(4.2)–(4.5) do not vanish. Consequently

$$
\Phi(\alpha,\beta,d)=
\left(\mathcal Y(\alpha,\beta,d)-48/5,
      \mathcal Z(\alpha,\beta,d)+532/5\right)
                                                               \tag{4.12}
$$

is smooth near $(1,1,0)$, vanishes there, and has an invertible
derivative in the two unknowns $(\alpha,\beta)$ by (4.11).
The implicit function theorem, with $d$ free, supplies the claimed
smooth $\alpha(d),\beta(d)$ and $\Phi(\alpha(d),\beta(d),d)=0$
on some interval $|d|<\eta$. Shrink that interval to keep both
parameters positive and $|d|<1$. Then
$G_{\alpha(d),\beta(d),d}(1)=(24-d)/U>0$, so the polynomial is
nonzero and has degree at most three. All sources retain strict
positivity, rank one and trace one.

The four interpolation equations supply every ancestor reading
through clock three, and $\Phi=0$ supplies the actual clock-four
and clock-five equations. Hence every $W_d$ realizes exactly
$H^*$, not merely its action word or its final response. Its initial
gain is $-d$, and its drift is $d$, so the targets are distinct for
distinct $d$. Each triple in (4.6) is defined independently of any
subsequent choice of an atom. This is a common fiber of fixed actual
worlds. ∎

**推论 4.3（六读不能认证初根标签）。** The fiber $\mathcal F(H^*)$
contains uncountably many complete targets and contains both an
initial-root target and noninitial-root targets. No function of the
observed history through clock five alone can correctly assign the
label $\mathbf1_{\{g(0)=0\}}$ to every target in this fiber.
Those readings also do not determine the drift.

Proof. The open interval in Theorem 4.2 injects into the fiber via
$d\mapsto W_d$, since the drift coordinate is $d$. Its center has
the initial-root label one; every nonzero parameter in the interval
has label zero. Any function of the six observations takes the same
value on all of them and therefore cannot give both required labels.
The distinct drifts prove the last assertion. In particular $H^*$
neither entails nor excludes $g(0)=0$.

The theorem concerns information available at clock five. It gives
no $L_2$ assertion: the recursive obstruction (1.7) requires suitable
collisions after each possible next atom, which six-read compatibility
alone does not supply. It also gives no failure assertion about the
two further readings of an unrestricted policy. The initial-root
condition used by Theorem 2.1 remains a prior promise at this same
actual history. ∎

## 5. 数学对应与保留的完整问题

**定义 5.1（先例、标准方法与具体对应）。** The mathematical
dependencies and distinctions are as follows.

| Source | Precise correspondence |
| --- | --- |
| [I](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md), Definitions 39.1, 44.1; [II](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), Definitions 51.1–51.2, 56.1 | Original-clock acquisition, normalized complete targets, the separate $MMJM$ history and the whole-set failure recursion. |
| II, Theorem 62.1; Propositions 63.1 and 63.3 | The whole known zero-drift $MMJM$ inverse, its noncontainment consequence and its exceptional actual consumer are reused results. Since the initial read there is zero, their zero-drift stratum is exactly their initial-root stratum. |
| II, Propositions 59.3, 63.4 and 68.2 | Four-point interpolation and the implicit function theorem already construct continuous families at other $MMJM$ histories or promises. The method is shared; the six equations and the exact mixed-drift $H^*$ family in Theorem 4.2 are different. |
| [III](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md), Theorem 4.1 and Proposition 7.1 | The known factor $(1+t^2)(a+bt)$ and the collision for one fixed acquisition word retain their stated domains. They provide neither the arbitrary-gain inverse here nor a general adaptive lower bound. |
| [IV](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md), Theorem 2.1 | Its losing $JMMM$ continuation and the complementary fourth-$J$ continuation share the $JMM$ ancestors; the present parent is the latter. |
| [V](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md), Definition 5.1; Theorem 5.2, equation (5.5) | The literal $JMMJ$ history and the baseline-drift root-seven inverse. The zero fifth-response branch of Theorem 2.1 is exactly this inverse after (2.18). |
| [VI](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md), Theorem 3.2 | The arbitrary-drift $MMJM$ consumer for known sets of at most three targets, and its at-least-four necessary size bound for $L_3$. Its separate $MJMMJ$ child is a different literal history. |
| [VII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md), Definitions 1.1–1.3; Theorems 4.1 and 5.1; Corollary 5.2 | The same $JMMJM$ history, its arbitrary-drift pair exclusion and the at-most-two-target actual-child consumer. The initial-root policy here instead covers arbitrary cardinalities; Corollary 4.3 prevents inferring its promise from the six readings. |
| Yanjun Li, Kiryung Lee, Yoram Bresler, *A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1) | `literature-attested`: identification up to a specified transformation group quantifies over every compatible solution and decomposes into a factor-orbit condition and a conditional-fiber condition. Here trace normalization removes positive scaling, and drift is retained. No fixed-$M,J$ adaptive sampling theorem is transferred. |
| Petra van den Bos, Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [Theorem 6.1 and Example 7](https://arxiv.org/html/1907.11034v2) | `literature-attested`: the suspension-automaton construction uses mutually incompatible distinct states and injective splits; Example 7 shows why the incompatibility hypothesis cannot be dropped from that equivalence. The continuous classes and read budgets here are supplied by their own explicit inverses. |
| Michael Kech, Felix Krahmer, *Optimal Injectivity Conditions for Bilinear Inverse Problems with Applications to Identifiability of Deconvolution Problems*, [Theorems III.1–III.3](https://arxiv.org/html/1603.07316v1) | `literature-attested`: stable injectivity on constrained complex rank-one domains, with lower thresholds and almost-all linear or structured measurement maps. These quantifiers do not give a threshold for positive real sources with drift, fixed atoms and deterministic feedback. |

The nonzero-response inverse and its assembly in Theorem 2.1,
the actual consumer in Proposition 3.2, and the specific family and
label obstruction in Theorem 4.2 and Corollary 4.3 are
`repo-derived` model-specific deductions. Lagrange interpolation,
linear trace reconstruction, monotonic inversion and the implicit
function theorem are standard methods within their proofs; no new
general version of these methods is asserted. Their use gives no
external originality or literature-completeness assertion.

**定义 5.2（保留的原目标）。** At $H_{JM}(Y,z)$, the unrestricted
question remains whether some known compatible set of at least
three fixed complete targets has $L_2$, or every whole unrestricted
fiber admits a two-further-reading decoder. Theorem 2.1 excludes
containment of a losing set in $g(0)=0$; it does not settle the
complement or an unlabeled union. Theorem 4.2 gives an actual
mixed-drift fiber, without establishing that different drifts or
different root labels are necessary in a losing family.

At the separate $MMJM$ parent, the unrestricted $L_3$ question for
at least four targets and the corresponding whole-fiber decoder
question remain. A local losing child would still have to meet the
joint realization conditions for the other actual action children
before determining failure at an ancestor. Neither the sixteen-slot
nor the 256-slot feasibility question of
[IV, Theorems 9.2–9.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md)
is decided by the present inverse or continuous family.

With $n_{\mathrm{det}}(3,0)$ denoting the least uniform total read
budget under Definition 1.1, the original full-domain alternative
remains $n_{\mathrm{det}}(3,0)\ge9$ versus a lawful decoder with at
most eight total readings on all of $\mathcal W_3$. Both initial
actions, all actual histories, all gain and root strata, and every
early stop belong to that problem. The results here supply neither
an original-root nine-reading lower bound nor a universal
eight-reading complete-target decoder.

## 追加锚（本行以下为增补区）
