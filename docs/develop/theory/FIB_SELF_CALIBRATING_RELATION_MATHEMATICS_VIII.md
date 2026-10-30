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

## 6. 六维固定来源族的十一报告边界

### 定义 6.1（六维合同）

令

$$
\mathcal M_6=\left\{\sum_{a=1}^{m}c_a\ell_a:
m\in\{1,2\},\ c_a\in\mathbb R_{>0}^{6},\
\ell_a\in\mathbb R_{>0}^{1\times6}\right\}.
$$

仍只有一条不可复制、不可复位的轨迹；允许的原子为

$$
Ne_j=e_{j+1}\quad(j<5),\qquad Ne_5=0,\qquad
L_0=e_0\mathbf1^{\mathsf T}.
$$

初读和每个原子后的读数都计费。单位容限合同中每份报告的误差满足
$|\eta_i|\le1$，可以相关并依赖全部历史；普通矩阵秩是目标。对纯 $N$ 前缀定义

$$
a_i(R)=\operatorname{tr}(N^iR),
\qquad
b_j^{(q)}(R)=\sum_{h=0}^{5-q}R_{hj}
\quad(0\le q<6).
$$

在首次 $L_0$ 前已有 $q$ 次 $N$ 时，置

$$
B_q=\begin{cases}\{0,\ldots,5\},&q\le4,\\
                 \{0,\ldots,4\},&q=5,
     \end{cases}
\qquad
A_i(x,v)=\sum_{h=0}^{5-i}x_hv_{h+i}.
$$

设已经取得的纯 $N$ 报告为 $u_0,\ldots,u_q$，首次 $L_0$ 后的规范补全报告为
$(w_j)_{j\in B_q}$。实际报告相容系统 $\mathsf D_q(u,w)$ 是
[III 引理 13.2 的 (13.5)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md)
在单位容限、$k=6$ 时的系统：存在同一组 $x,v\in\mathbb R_{>0}^6$ 使

$$
\sum_{h=0}^{5-q}x_h=1,\qquad
|A_i(x,v)-u_i|\le1\quad(0\le i\le q),\qquad
|v_j-w_j|\le1\quad(j\in B_q).
$$

当 $q=5$ 时 $x_0=1$，故 $v_5=A_5$；该坐标只使用已经取得的报告 $u_5$，
不再取得或收费第二份报告。$\mathsf D_q$ 有解恰好表示同一个严格正秩一来源
与全部实际规范报告相容。

另以 $\mathsf C_q(R,u)$ 表示 III 定义 14.3 的辅助系统：保持同一归一化、
严格正性及旧报告约束，把新报告约束换成

$$
|v_j-b_j^{(q)}(R)|\le2\qquad(j\in B_q).
$$

若 $u,w$ 是 $R$ 的一份允许报告，则 $\mathsf D_q(u,w)$ 的每个解也是
$\mathsf C_q(R,u)$ 的解，因为
$|v_j-b_j^{(q)}(R)|\le|v_j-w_j|+|w_j-b_j^{(q)}(R)|\le2$。
反过来，若 $u$ 是 $R$ 的允许纯 $N$ 前缀，则 $\mathsf C_q(R,u)$ 的解保证
存在一份共同允许补全：对 $j\in B_q$
取 $w_j=(v_j+b_j^{(q)}(R))/2$，$q=5$ 的共享报告仍取 $u_5$。
这就是 III 引理 14.4 的中点构造；它不保证任意预先给定的 $w$ 满足
$\mathsf D_q(u,w)$。末端判定使用 $\mathsf D_q$。

### 引理 6.2（显式六维族和纯 $N$ 数据）

沿用 IV 引理 22.2 的函数

$$
\begin{aligned}
d_s&=\frac{37}{2}+s-\frac{125}{44+s},&
\lambda_s&=\frac12+s,&
c_s&=94-d_s-10s,\\
L_s&=\frac{39}{2}-\frac{125}{44+s},&
M&=\frac{39}{2},&
D_s&=\frac{125}{44+s},
\end{aligned}
$$

其中 $0\le s\le1/2$，再置

$$
B=10000,\qquad K_6=10^{12},\qquad
\mu_s=10000-1011-\lambda_s(3-s),
$$

$$
r_s^{(6)}=(B,1000,c_s,3-s,10,1),\qquad
w_s^{(6)}=(1,1,1,d_s,23/2,8),
$$

$$
\nu_s=K_6-B-\bigl(1+\lambda_sc_s+(3-s)+10\mu_s\bigr),
$$

并定义

$$
T_s=
\begin{pmatrix}
r_s^{(6)}\\
w_s^{(6)}\\
\lambda_sr_s^{(6)}\\
r_s^{(6)}\\
\mu_sr_s^{(6)}\\
\nu_sr_s^{(6)}
\end{pmatrix}.
\tag{6.1}
$$

则 $T_s\in\mathcal M_6$，普通秩为二，并且

$$
(a_0,a_1,a_2,a_3,a_4,a_5)(T_s)
=(K_6,10000,100,15,18,1).
\tag{6.2}
$$

其切口列和为

$$
\begin{aligned}
b^{(0)}(T_s)&=(2+\lambda_s+\mu_s+\nu_s)r_s^{(6)}+w_s^{(6)},\\
b^{(1)}(T_s)&=(2+\lambda_s+\mu_s)r_s^{(6)}+w_s^{(6)},\\
b^{(2)}(T_s)&=(2+\lambda_s)r_s^{(6)}+w_s^{(6)},\\
b^{(3)}(T_s)&=(1+\lambda_s)r_s^{(6)}+w_s^{(6)},\\
b^{(4)}(T_s)&=r_s^{(6)}+w_s^{(6)}
=(10001,1001,c_s+1,L_s+2,43/2,9),\\
b^{(5)}(T_s)&=r_s^{(6)}.
\end{aligned}
\tag{6.3}
$$

**证明。** 在 $[0,1/2]$ 上，$70<c_s<80$、$15<d_s<17$、
$1/2\le\lambda_s\le1$，并且 $8986<\mu_s<8988$。因此
$\nu_s>10^{12}-10^5>0$。取

$$
C_s=(1,0,\lambda_s,1,\mu_s,\nu_s)^{\mathsf T},\qquad
e=(0,1,0,0,0,0)^{\mathsf T},\qquad \alpha=\frac1{20000}.
$$

逐项有 $r_s^{(6)}-\alpha w_s^{(6)}>0$ 和
$w_s^{(6)}-\alpha r_s^{(6)}>0$；关键的最小项为
$1-\alpha B=1/2$。于是

$$
T_s=
\frac{(C_s+\alpha e)(r_s^{(6)}-\alpha w_s^{(6)})
 +(\alpha C_s+e)(w_s^{(6)}-\alpha r_s^{(6)})}
 {1-\alpha^2},
\tag{6.4}
$$

是两项严格正外积之和。展开 (6.4) 即得
$T_s=C_sr_s^{(6)}+e(w_s^{(6)})$。向量 $C_s,e$ 独立，且
$r_s^{(6)},w_s^{(6)}$ 的前两坐标子式为
$B-1000=9000\ne0$，故秩恰为二。

由对角线、第一上对角线及其余上对角线逐项求和，分别得到

$$
\begin{aligned}
a_0&=B+1+\lambda_sc_s+(3-s)+10\mu_s+\nu_s=K_6,\\
a_1&=1000+1+\lambda_s(3-s)+10+\mu_s=10000,\\
a_2&=c_s+d_s+10\lambda_s+1=100,\\
a_3&=(3-s)+23/2+\lambda_s=15,\\
a_4&=10+8=18,\qquad a_5=1.
\end{aligned}
$$

这也给出 (6.3)。∎

### 命题 6.3（六维逐来源十一报告上界）

令 $\tau_s=17+s/4$。对每个 $s\in[0,1/2]$，存在完整
$\mathcal M_6$ 上单位容限可靠的确定性协议 $\Pi_s$，并且在 $T_s$ 的每条允许
误差历史上恰以十一次报告输出秩二。

协议先取得 $y_0$，连续执行四次 $N$ 并取得 $y_1,y_2,y_3,y_4$。随后：

$$
\begin{cases}
L_0,N,N,N,N,N,&y_4\le\tau_s,\\
N,L_0,N,N,N,N,&y_4>\tau_s.
\end{cases}
\tag{6.5}
$$

末端使用实际取得的报告，检查 $\mathsf D_4(u,w)$ 或 $\mathsf D_5(u,w)$；
无严格正解时输出秩二，有解时停止而不作秩断言。

**证明。** 任意严格正秩一来源在其允许历史上都给出 $\mathsf D_q$ 的同一个
严格正解，所以该末端规则在完整 $\mathcal M_6$ 上可靠。两条分支都执行十个
原子，初读计入后共有十一份报告；高分支的末坐标沿用旧报告 $u_5$。

对 $T_s$ 的任意允许报告，由定义 6.1，$\mathsf D_q$ 有解蕴含
$\mathsf C_q(T_s,u)$ 有解。因此只需排除相应辅助系统的解。先注意

$$
17\le\tau_s\le\frac{137}{8},
\qquad
y_2\in[99,101],\quad y_3\in[14,16],\quad y_4\in[17,19].
$$

在低分支 $y_4\le\tau_s$ 中，若 $\mathsf C_4$ 有解，写
$x_0=z,x_1=1-z$。由 (6.3) 及闭误差约束，

$$
v_3\ge L_s,\qquad v_4\ge M,\qquad v_5\ge7,
$$

且 $x_2>0$。故

$$
A_3=zv_3+(1-z)v_4+x_2v_5
>M-D_sz.
$$

另一方面 $A_3\le y_3+1\le17$，所以

$$
z>\frac{M-17}{D_s}=\frac52\frac{44+s}{125}=\rho_s.
$$

再由 $v_4\ge M$、$v_5\ge7$，

$$
A_4=zv_4+(1-z)v_5
>7+\frac{25}{2}\rho_s
=18+\frac{s}{4}=\tau_s+1.
$$

但 $y_4\le\tau_s$ 与 $|A_4-y_4|\le1$ 给出
$A_4\le\tau_s+1$，矛盾。严格不等式来自 $x_2>0$。

在高分支 $y_4>\tau_s$ 中，若 $\mathsf C_5$ 有解，则其归一化为
$x_0=1$。由 (6.3)，

$$
1-s\le v_3,\qquad 8\le v_4\le12,\qquad 0<v_5=A_5\le3.
$$

由于 $A_3\le y_3+1\le17$，有

$$
x_1v_4+x_2v_5\le16+s.
$$

而 $x_2v_5>0$，所以 $x_1v_4<16+s$，并且

$$
A_4=v_4+x_1v_5
<v_4+\frac{3(16+s)}{v_4}
\le16+\frac{s}{4}=\tau_s-1.
$$

最后一个不等式是在 $8\le v_4\le12$ 上比较两个端点；函数
$v\mapsto v+3(16+s)/v$ 为凸函数，端点值分别不超过
$14+3s/8$ 与 $16+s/4$。而高分支的旧报告约束给出
$A_4\ge y_4-1>\tau_s-1$，矛盾。两分支穷尽，故命题成立。∎

### 引理 6.4（六个切口的固定伴随）

令

$$
u_s=\tau_s+\frac1{16},\qquad
p_s=(K_6,10000,100,16,u_s,2).
\tag{6.6}
$$

这个纯 $N$ 报告前缀属于 $T_s$ 的单位闭误差盒，因为
$a(T_s)=(K_6,10000,100,15,18,1)$。

对 $q=0,\ldots,5$，存在一个固定严格正秩一来源 $S_{q,s}=x^{[q]}(v^{[q]})^{\mathsf T}$，
满足新旧前缀的共同误差约束，并且在十报告预算内所有可见的 $b$ 坐标均可用同一份
报告表同时兼容 $T_s$ 与 $S_{q,s}$。可见坐标上界为

$$
\begin{array}{c|cccccc}
q&0&1&2&3&4&5\\ \hline
\max j&5&5&5&5&4&3.
\end{array}
\tag{6.7}
$$

**证明。** 对 $q=0$，取 $v=b^{(0)}(T_s)$。有

$$
b_5^{(0)}(T_s)<K_6<b_0^{(0)}(T_s),
$$

因为
$$
b_5^{(0)}=\nu_s+\mu_s+\lambda_s+10
=K_6-B+6+s-\lambda_s(c_s-1)-9\mu_s<K_6,
$$
而
$b_0^{(0)}=B(2+\lambda_s+\mu_s+\nu_s)+1>B\nu_s>K_6$。III 命题 9.6 的严格正凸组合
给出 $x>0$、$\sum x_h=1$ 且 $A_0=K_6$；这就是 $S_{0,s}$。

对新 $q=1,2,3$，分别把 IV 引理 22.4 的旧 $q=0,1,2$ 伴随显式提升；新
$q=4$ 使用 IV 定理 24.2 证明中的固定 q=3 伴随 (24.4)。其中
$0<u-\tau_s<1/8$ 时 (24.4) 的同一正性估计适用，故特别覆盖 $u_s$ 的全部参数。
新 $q=5$ 使用同一定理证明中的固定 q=4 伴随 (24.7)，该伴随对每个
$s\in[0,1/2]$ 都成立。式 (24.7) 中的 $u$ 取本节 $p_s$ 的第五坐标 $u_s$；更一般地，在
$17\le u\le69/4$ 上，同一公式给出
$$
\frac{19}{32}\le x_2
=\frac{16-(3-s)-\frac34(u-\frac32)}2
\le\frac{15}{16}<1,
$$
又有
$$
100-c_s-\frac34(3-s)-x_2(u-3/2)
>100-80-\frac94-\frac{15}{16}\frac{63}{4}>0,
$$
所以 $0<x_3<15$。旧初读中前四项之和满足
$$
1000+\frac34c_s+x_2(3-s)+x_3(u-3/2)
<1000+60+3+15\cdot16<2000,
$$
故 (24.7) 的旧 $x_4>4000$；旧真值仍为
$(A_0,A_1,A_2,A_3,A_4)=(10000,100,16,u,2)$。
统一写法如下：若 $(x,v)$ 是 $Q_s$ 在旧切口
$q-1$ 的伴随，令

$$
\beta_q=b_0^{(q)}(T_s),\qquad
v'=(\beta_q,v),
$$

并定义

$$
x'_5=\frac{K_6-x_0\beta_q-
\sum_{h=1}^{4}x_hv_{h-1}}{v_4},
\qquad x'=(x_0,x_1,x_2,x_3,x_4,x'_5).
\tag{6.8}
$$

直接由定义得到

$$
b_{j+1}^{(q)}(T_s)=b_j^{(q-1)}(Q_s),
\qquad
A'_i=A_{i-1}\quad(1\le i\le5).
\tag{6.9}
$$

因此旧误差约束逐项移位，新首坐标误差为零，且新归一化
$\sum_{h=0}^{5-q}x'_h=1$ 保持。以下逐项给出 (6.8) 的正性界，记

$$
E_q=x_0\beta_q+\sum_{h=1}^{4}x_hv_{h-1},\qquad
H_s=2+\lambda_s+\mu_s<8991.
$$

对新 $q=1$，旧 $q=0$ 伴随满足 $\sum_{h=0}^4x_h=1$，
$\beta_1=BH_s+1<9\cdot10^7$，且旧 $v_h<9\cdot10^6$。
所以 $E_1<9\cdot10^7$。

对新 $q=2,3$，旧 $q=1,2$ 伴随的 $v$ 分别为

$$
\begin{aligned}
&(1000(2+\lambda_s)+1,\ (2+\lambda_s)c_s+1,
  (2+\lambda_s)(3-s)+d_s,\ 10(2+\lambda_s)+23/2,\ 10+\lambda_s),\\
&(1000(1+\lambda_s)+1,\ (1+\lambda_s)c_s+1,
  (1+\lambda_s)(3-s)+d_s,\ 10(1+\lambda_s)+23/2,\ 9+\lambda_s).
\end{aligned}
$$

对新 $q=4$，旧 $v=(1001,c_s+1,L_s,M,7)$；对新 $q=5$，
旧 $v=(1000,c_s,3-s,u-3/2,2)$，其中 $17\le u\le69/4$。
这四种情形均有 $1/2\le v_h\le3001$、$x_0\le1$，且旧
$A_0=\sum_{h=0}^4x_hv_h=10000$，故每个 $x_h<20000$。
又由 (6.3)，$\beta_q\le30001$（$q=2,3,4,5$）。于是

$$
E_q<30001+4\cdot20000\cdot3001<3\cdot10^8<K_6.
$$

所有分母 $v_4$ 严格正，故 (6.8) 的 $x'_5>0$。这些界同时适用于
$0<u-\tau_s<1/8$ 的旧 $q=3$ 伴随；其余旧因子的正性由 IV 引理 22.4
和上述 (24.7) 的范围给出。每个提升后的来源均为完整六维严格正秩一外积。

对新 $q=1,2,3$ 使用旧 $q=0,1,2$ 的完整坐标；对新 $q=4$ 使用旧 $q=3$
的坐标（其公式给出 $v-b^{(3)}=(0,0,-2,-2,-2)$）。对新 $q=5$ 使用旧 $q=4$
的坐标时，预算内的新坐标 $b_1,b_2,b_3$ 分别对应旧的 $b_0,b_1,b_2$，均与旧见证的
对应坐标相同；共享坐标 $v'_5=A'_5=A_4=2$ 也与 $p_{s,5}$ 相同。这正覆盖 (6.7)：
报告数为 $1+q+1+j\le10$，而 $q=5$ 的 $j=4$ 已超出十报告预算。
对每个可见新坐标取 $T_s$ 真值与伴随真值的中点；两端距离至多二，故中点距两者
至多一。固定的伴随在所选切口之后不变，未把不同分支的来源拼接。∎

### 定理 6.5（六维族的逐来源精确十一报告费用）

定义 $c_{6,\varepsilon}(R)$ 为完整 $\mathcal M_6$ 合同下、任意相关闭
$\varepsilon$ 误差中，固定来源 $R$ 的全域可靠确定性协议所需的最少报告数，
初读计费。则对所有 $\varepsilon>0$ 与 $s\in[0,1/2]$，

$$
\boxed{c_{6,\varepsilon}(\varepsilon T_s)=11.}
\tag{6.10}
$$

**证明。** 命题 6.3 给出上界。对单位容限下界，取任意完整域可靠协议，假设它在
$T_s$ 的每条允许历史上十次报告内输出秩二。沿纯 $N$ 前缀报告 $p_s$；在首次
$L_0$ 前停止会被 III 引理 10.3 的固定正秩一来源重放。若在六次 $N$ 后仍未执行
$L_0$，则 $N^6=0$，同一来源继续给出永久零尾，因此首次 $L_0$ 必在
$q\in\{0,1,2,3,4,5\}$ 次 $N$ 后发生。

固定该 $q$，用引理 6.4 的 $S_{q,s}$。在首次 $L_0$ 及其后续可见 $b$ 坐标上，
把报告取为两来源真值的中点；旧纯 $N$ 报告 $p_s$ 对两者均在单位误差内，
中点补全也对两者均在单位误差内。确定性逐前缀归纳使协议在 $T_s$ 与
$S_{q,s}$ 上产生相同动作、报告、停止和输出，不能在前者输出秩二，因为后者
普通秩为一而协议在完整域上可靠。这排除了十报告成功，故单位费用至少十一。

若 $\varepsilon>0$，将全部来源、真实读数、伴随真值和报告误差同时乘以
$\varepsilon$；$R\mapsto\varepsilon R$ 保持严格正性与普通秩，且
$\operatorname{tr}(A\varepsilon R)=\varepsilon\operatorname{tr}(AR)$。
任何 $\varepsilon$ 容限十报告协议除以 $\varepsilon$ 即给出单位容限十报告协议，
反之命题 6.3 的协议把报告乘以 $\varepsilon$。故 (6.10) 成立。∎

### 定理 6.6（十一报告预算下的有限预选不相容性）

对有限 $F\subseteq[0,1/2]$，令 $\nu^{(11)}_{6,\varepsilon}$ 表示：成员为完整
$\mathcal M_6$ 上 $\varepsilon$-可靠、且在所覆盖来源的每条允许历史上十一报告内
成功的确定性协议，运行前预先选定的有限族覆盖 $\{\varepsilon T_s:s\in F\}$ 所需的
最少成员数。则

$$
\nu^{(11)}_{6,\varepsilon}(\{\varepsilon T_s:s\in F\})=|F|.
\tag{6.11}
$$

**证明。** 命题 6.3 给出每个参数的十一报告协议，按正比例缩放得到任意
$\varepsilon>0$ 的上界。定理 7.3 证明，即使没有报告预算，一个完整域可靠的
确定性协议也不能在两个不同的 $\varepsilon T_s$ 上全误差成功；这尤其适用于
十一报告协议。因此下界为 $|F|$。$F=\varnothing$ 时空协议族给出零。∎

### 定义 6.7（全误差成功与完整域可靠性）

固定 $\varepsilon>0$。协议是全部有限动作—报告历史上的确定性规则，选择下一原子、停止及输出；
不要求连续、可测或可计算。来源在每次运行前固定，运行期间不变。
称协议在 $\varepsilon T_s$ 上全误差成功，若对这个来源的每条允许闭
$\varepsilon$ 误差历史，它都在有限时刻输出 $2$，不要求各历史有共同的停止预算。
称协议在完整 $\mathcal M_6$ 上 $\varepsilon$-可靠，若它在每个严格正秩一
来源的每条允许历史上都不输出 $2$。来源域中所有矩阵的普通秩为一或二，
所以输出 $2$ 认证的正是普通秩二。

## 追加锚（本行以下为增补区）

## 7. 六维连续族的无预算有限预选障碍

### 定义 7.1（不限制停止费用的预选覆盖）

固定 $\varepsilon>0$。沿用定义 6.1、6.7 的完整 $\mathcal M_6$、
$N,L_0$、单条不可复制不可复位轨迹与任意相关闭误差合同，令

$$
\operatorname{Succ}_{6,\varepsilon}(\Pi)
=\{R\in\mathcal M_6:\Pi\text{ 在 }R\text{ 的每条允许历史上均有限输出 }2\}.
\tag{7.1}
$$

对 $\mathcal A\subseteq\mathcal M_6$，定义 $\nu_{6,\varepsilon}(\mathcal A)$
为覆盖 $\mathcal A$ 所需的最少预选协议数：每个成员在完整 $\mathcal M_6$ 上
$\varepsilon$-可靠，且
$\mathcal A\subseteq\bigcup_j\operatorname{Succ}_{6,\varepsilon}(\Pi_j)$。
没有有限覆盖时记为 $\infty$，空集的覆盖数为零。协议族在运行前固定；
覆盖的量词为对每个来源存在一个全误差成功的成员，不要求各历史或各来源
有共同的停止预算。

### 引理 7.2（重叠纯前缀的六个完整切口伴随）

设 $0\le s<t\le1/2$、$\tau_s<u<\tau_t$，并置

$$
p=(K_6,10000,100,16,u,2),\qquad
R_q=\begin{cases}T_s,&0\le q\le4,\\T_t,&q=5.\end{cases}
\tag{7.2}
$$

$p$ 同时属于 $T_s,T_t$ 的单位闭误差盒。对每个 $q\in\{0,\ldots,5\}$，
存在一个固定来源 $S_q=X^{[q]}(V^{[q]})^{\mathsf T}\in\mathcal M_6$，
普通秩为一，全部因子严格正，并且

$$
\sum_{h=0}^{5-q}X_h^{[q]}=1,\qquad
|A_i(X^{[q]},V^{[q]})-p_i|\le1\quad(0\le i\le q),\qquad
|V_j^{[q]}-b_j^{(q)}(R_q)|\le2\quad(j\in B_q).
\tag{7.3}
$$

$q=5$ 的同一个 $V_5^{[5]}=A_5(X^{[5]},V^{[5]})=3$ 与
$a_5(T_t)=1$ 共同使用旧报告 $p_5=2$。

**证明。** 由 (6.2)，$p$ 的误差为 $(0,0,0,1,u-18,1)$；
$17<u<137/8<19$，故全部坐标合法。

对 $q=0,1,2,3$，取引理 6.4 的 $T_s$ 伴随。它们的旧约束不涉及 $u$，
且该引理在这些切口给出了全部六个新坐标，而非部分报告伴随。
$q=0$ 直接由 $b_5^{(0)}(T_s)<K_6<b_0^{(0)}(T_s)$ 的严格正凸组合取得；
$q=1,2,3$ 分别用 IV 引理 22.4 的旧 $q=0,1,2$ 伴随及 (6.8)--(6.9)。
引理 6.4 的界给出其最后新增权重的严格正性。

对 $q=4$，复用 IV 引理 22.4 的旧 $q=3$ 完整伴随。明确地，令
$\rho_s=(44+s)/50$、$\delta=u-\tau_s$，并取

$$
\begin{aligned}
h&=\delta/25,&z&=\rho_s+h,&
v&=(1001,c_s+1,L_s,M,7),\\
x_0&=z,&x_1&=1-z,&x_2&=D_sh/7,\\
x_3&=\frac{100-z(c_s+1)-(1-z)L_s-Mx_2}{7},&
x_4&=\frac{10000-\sum_{h=0}^3x_hv_h}{7}.
\end{aligned}
\tag{7.4}
$$

这是同一伴随在 $0<\delta<1/8$ 的实例。具体地，$0<h<1/200$、
$22/25\le\rho_s\le89/100$，所以 $0<z<0.9$；又有
$0<x_2<1/400$，且

$$
z(c_s+1)+(1-z)L_s+Mx_2<82<100,
\qquad
\sum_{h=0}^3x_hv_h<1001+81+1+300<1400.
$$

因此 $0<x_3<100/7$、$x_4>0$。按 (6.8) 取
$\beta_4=10001$、$V^{[4]}=(\beta_4,v)$、
$X^{[4]}=(x_0,\ldots,x_4,x'_5)$。
引理 6.4 的 $E_4<3\cdot10^8<K_6$ 同样适用于 (7.4)，故 $x'_5>0$。
式 (6.9) 给出

$$
\begin{aligned}
(A_0,\ldots,A_4)(X^{[4]},V^{[4]})
  &=(K_6,10000,100,17,\tau_s+1+\delta/2),\\
V^{[4]}-b^{(4)}(T_s)&=(0,0,0,-2,-2,-2).
\end{aligned}
\tag{7.5}
$$

旧报告差为 $(0,0,0,1,1-\delta/2)$，故 (7.3) 在 $q=4$ 成立。

对 $q=5$，使用 IV 引理 22.4 的旧 $q=4$ 完整伴随，取

$$
\begin{aligned}
v&=(1000,c_t,1-t,12,3),&x_0&=1,\\
x_1&=(u-13)/3,&x_2&=4(\tau_t-u)/3,\\
x_3&=\frac{100-c_t-x_1(1-t)-12x_2}{3},&
x_4&=\frac{10000-\sum_{h=0}^3x_hv_h}{3}.
\end{aligned}
\tag{7.6}
$$

其中 $0<x_1<11/8$、$0<x_2<1/6$、$1-t\ge1/2$，且

$$
c_t+x_1(1-t)+12x_2<80+11/8+2<100.
$$

所以 $0<x_3<100/3$；再由

$$
\sum_{h=0}^3x_hv_h
<1000+80\cdot11/8+1/6+12\cdot100/3<1600
$$

得到 $x_4>0$。这些正因子实现旧真值
$(A_0,\ldots,A_4)=(10000,100,17,u-1,3)$。
令

$$
\begin{aligned}
V^{[5]}&=(B,1000,c_t,1-t,12,3),\\
X^{[5]}&=(1,x_1,x_2,x_3,x_4,x'_5),\\
x'_5&=\frac{K_6-B-1000x_1-c_tx_2-(1-t)x_3-12x_4}{3}.
\end{aligned}
\tag{7.7}
$$

旧 $v_h\ge1/2$，旧 $A_0=10000$，故每个旧 $x_h<20000$；于是

$$
B+1000x_1+c_tx_2+(1-t)x_3+12x_4
<30001+4\cdot20000\cdot3001<3\cdot10^8<K_6.
$$

故新增 $x'_5>0$。式 (6.9) 现在给出

$$
\begin{aligned}
(A_0,\ldots,A_5)(X^{[5]},V^{[5]})
 &=(K_6,10000,100,17,u-1,3),\\
(V_j^{[5]}-b_j^{(5)}(T_t))_{j=0}^{4}&=(0,0,0,-2,2).
\end{aligned}
\tag{7.8}
$$

这包括第六切口的新坐标 $j=4$；其共同报告为 $(12+10)/2=11$。
共享末坐标的同一旧报告 $2$ 距真实值 $1$ 与 $3$ 均为一。
全部旧报告差为 $(0,0,0,1,-1,1)$，故 (7.3) 成立。
这里 (7.6) 的完整 $v$ 与 IV (24.7) 的部分伴随不同；后者只在引理 6.4
的十报告合同内使用。每个 $q$ 的全部旧新坐标始终由同一个 $S_q$ 实现。∎

### 定理 7.3（任意完整历史协议的不相容性与精确有限覆盖数）

对每个 $\varepsilon>0$，任意在完整 $\mathcal M_6$ 上
$\varepsilon$-可靠的确定性完整历史协议 $\Pi$ 均满足

$$
\left|\{s\in[0,1/2]:
 \varepsilon T_s\in\operatorname{Succ}_{6,\varepsilon}(\Pi)\}\right|\le1.
\tag{7.9}
$$

因此，对每个有限 $F\subseteq[0,1/2]$（包括空集），

$$
\nu_{6,\varepsilon}(\{\varepsilon T_s:s\in F\})=|F|,
\qquad
\nu_{6,\varepsilon}(\{\varepsilon T_s:0\le s\le1/2\})=\infty.
\tag{7.10}
$$

**证明。** 先取单位容限，反设同一个完整域可靠协议在 $T_s,T_t$ 上均全误差
成功，其中 $s<t$。选 $\tau_s<u<\tau_t$，沿尚未执行 $L_0$ 的纯 $N$ 历史
依次报告引理 7.2 的 $p_i$。这是两目标的共同合法前缀；协议的确定性使首次
$L_0$ 前的所有动作与停止决定相同。

若它在某个 $q\le5$ 的纯 $N$ 前缀停止，由 III 引理 10.3 对正数据
$p_0,\ldots,p_q$ 取一个固定严格正秩一来源，精确实现这段报告。
逐前缀归纳给出相同停止和输出；可靠性排除输出 $2$，全误差成功又要求输出
$2$，矛盾。这也包括初读即停。

若取得 $p_0,\ldots,p_5$ 后仍选择 $N$，则累计矩阵成为 $N^6=0$。
以后无论选择哪个原子均保持零，一直报告零合法。对全部六个正数 $p_i$
应用 III 引理 10.3，固定一个严格正秩一来源；它在此前精确实现同一报告，
此后同样进入永久零状态。确定性使两者在整条零尾上具有相同动作、停止和输出，
而目标上的全误差成功迫使有限输出 $2$，再次违反可靠性。

所以共同前缀必在某个 $q\in\{0,\ldots,5\}$ 首次执行 $L_0$。
这个 $q$ 只由已经取得的共同报告确定。固定引理 7.2 的对应目标 $R_q$
及其一个伴随 $S_q$。此后对每个非零累计矩阵 $N^jL_0N^q$，使用固定报告表

$$
w_j=\frac{b_j^{(q)}(R_q)+V_j^{[q]}}2\quad(j\in B_q),
\qquad
w_5=p_5=2\quad(q=5).
\tag{7.11}
$$

第二项只规定 $q=5$ 的共享坐标；$q\le4$ 时全部六个 $w_j$ 都由第一项给出。
式 (7.3) 保证每个新报告距目标与伴随真值均至多一；共享坐标在两来源上也都合法。
旧报告仍是同一个 $p_{\le q}$，由同一个 $S_q$ 实现其闭误差约束。

III 引理 10.1 的字代数穷尽任意后继历史：再次 $L_0$ 只使非零读数指标
返回 $j=0$，重复坐标使用同一报告；若某段六次 $N$ 导致累计矩阵为零，
此后全部原子保持零并一直报告零。这张表在 $R_q$ 和固定的 $S_q$ 上均给出
完整合法历史，允许相关误差和反复出现的闭端点。对实际历史长度归纳，协议在
两来源上的每个动作、停止决定和输出均相同，不需要其决策函数有任何正则性。
它在 $R_q\in\{T_s,T_t\}$ 上必须有限输出 $2$，因而也在严格正秩一的
$S_q$ 上输出 $2$，矛盾。这里选定切口后目标和伴随各自保持固定，未按报告坐标
切换来源。

这直接证明任意长度历史的 (7.9)。等价地，也可先使用 III 定理 14.2，
由同一个 $\Pi$ 得到同时保留其全部成功来源、绝对停止上界为十一报告的正规形，
再用引理 7.2 的完整切口伴随。该正规形结论不保留原协议逐历史的停止费用，
本证明未使用这种费用保持断言。

对任意 $\varepsilon>0$，映射 $R\mapsto\varepsilon R$ 是完整
$\mathcal M_6$ 的保严格正性、保秩双射，且每个累计字 $A$ 满足
$\operatorname{tr}(A\varepsilon R)=\varepsilon\operatorname{tr}(AR)$。
把每份单位报告乘以 $\varepsilon$ 后交给假设的 $\varepsilon$-协议，逐前缀照做
其动作和停止决定，便得到单位容限协议，保留完整域可靠性和两个目标上的全误差
成功，违反刚证的单位不相容性。报告表 (7.11) 与共享报告同时缩放，
闭误差界恰从一变为 $\varepsilon$，故 (7.9) 对每个正容限成立。

最后 $(T_s)_{0,3}=3-s$，故不同参数给出不同来源。由 (7.9)，任何预选成员
至多覆盖这些来源中的一个，因此有限 $F$ 的覆盖数至少为 $|F|$。
命题 6.3 的逐来源协议按 $\varepsilon$ 缩放给出至多 $|F|$ 个成员；
$F=\varnothing$ 时取空协议族。任意 $m$ 个预选协议至多覆盖 $m$ 个参数，
从 $[0,1/2]$ 取 $m+1$ 个不同参数即排除全族的有限覆盖，证明 (7.10)。∎

## 追加锚（本行以下为增补区）
