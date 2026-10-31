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

## 8. 两套见证同时闭合的有限维归纳

### 定义 8.1（逐维合同与被消费的不变量）

对每个有限整数 $n\ge6$，把定义 6.1 的维数改为 $n$，记所得完整来源域为

$$
\mathcal M_n=\left\{\sum_{a=1}^{m}c_a\ell_a:
m\in\{1,2\},\quad c_a\in\mathbb R_{>0}^{n},\
\ell_a\in\mathbb R_{>0}^{1\times n}\right\}.
$$

普通矩阵秩仍是目标。已知原子为 $Ne_j=e_{j+1}$（$j<n-1$）、
$Ne_{n-1}=0$ 和 $L_0=e_0\mathbf1^{\mathsf T}$；它们只作用于同一条不可复制、
不可复位的轨迹。初读和每个原子后的报告都收费。单位容限为每份报告的闭误差界一，
误差可以任意相关并依赖完整历史。协议的动作、停止和输出是全部实际有限历史的
任意确定性函数，不要求任何正则性。

在维数 $n$ 写

$$
\begin{aligned}
a_i(R)&=\operatorname{tr}(N^iR),&
b_j^{(q)}(R)&=\sum_{h=0}^{n-1-q}R_{hj},&
A_i^{(n)}(x,v)&=\sum_{h=0}^{n-1-i}x_hv_{h+i},\\
B_{n,q}&=\begin{cases}\{0,\ldots,n-1\},&q\le n-2,\\
                      \{0,\ldots,n-2\},&q=n-1,\end{cases}&
J_n(q)&=\min(n-1,\,2n-q-4).
\end{aligned}
\tag{8.1}
$$

$\mathsf D_{n,q}(y,w)$ 与 $\mathsf C_{n,q}(R,y)$ 分别是定义 6.1 在维数
$n$ 的实际报告系统与辅助系统：两者都要求同一组严格正 $x,v$、
$\sum_{h=0}^{n-1-q}x_h=1$ 和
$|A_i^{(n)}(x,v)-y_i|\le1$（$0\le i\le q$）；前者的新约束是
$|v_j-w_j|\le1$，后者是 $|v_j-b_j^{(q)}(R)|\le2$，
其中 $j\in B_{n,q}$。在 $q=n-1$，$x_0=1$、
$v_{n-1}=A_{n-1}^{(n)}$ 只使用同一份旧报告 $y_{n-1}$，
没有第二次读取或第二个误差变量。实际允许报告给出
$\mathsf D_{n,q}\Rightarrow\mathsf C_{n,q}$；反向只给出某份中点补全，
不把任意实际报告的容限一换成容限二。这正是
[III 引理 13.2、定义 14.3 与引理 14.4](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md)
的严格正、同来源、共享报告条件。

以下不变量 $\mathcal I_n$ 同时携带来源、可靠上界所需的安全谓词以及两套不同的伴随。

来源是连续参数族

$$
R_s^{(n)}=
\begin{pmatrix}r_s\\w_s\\c_{2,s}r_s\\\vdots\\c_{n-1,s}r_s\end{pmatrix},
\qquad 0\le s\le\tfrac12,\qquad
\tau_s=17+\tfrac{s}{4}.
\tag{8.2}
$$

$r_s,w_s$ 的每个坐标至少为一，$c_{j,s}>0$，所有参数函数连续，
$r_{n-1,s}=1$、$w_{n-1,s}=8$。首两行末两列的子式为 $137/2$。
“至少为一”约束的是生成行 $r_s,w_s$；倍数行的系数只要求严格正。
族具有连续的两项严格正外积分解，其因子在闭参数区间上有统一正下界。
纯 $N$ 真值向量 $a^{(n)}$ 与 $s$ 无关，且

$$
a^{(n)}=(a_0^{(n)},\ldots,a_{n-5}^{(n)},100,15,18,1),\qquad
p_n(u)=(a_0^{(n)},\ldots,a_{n-5}^{(n)},100,16,u,2).
\tag{8.3}
$$

前面的坐标全为正。对每个 $s$ 的每份允许纯 $N$ 报告 $y$，安全谓词是

$$
\begin{aligned}
y_{n-2}\le\tau_s
 &\ \Longrightarrow\
 \neg\mathsf C_{n,n-2}(R_s^{(n)},y_{\le n-2}),\\
y_{n-2}>\tau_s
 &\ \Longrightarrow\
 \neg\mathsf C_{n,n-1}(R_s^{(n)},y_{\le n-1}).
\end{aligned}
\tag{8.4}
$$

第二行量化于每个允许的最后旧报告 $y_{n-1}$。它不是仅对所选伴随前缀的断言。

第一套是完整重叠伴随。对每个 $0\le s<t\le1/2$、每个
$\tau_s<u<\tau_t$ 和每个 $0\le q<n$，有同一组严格正向量 $(x,v)$ 满足

$$
\begin{aligned}
\sum_{h=0}^{n-1-q}x_h&=1,&
|A_i^{(n)}(x,v)-p_n(u)_i|&\le1\quad(0\le i\le q),\\
|v_j-b_j^{(q)}(R_{\sigma}^{(n)})|&\le2\quad(j\in B_{n,q}),&
\sigma&=\begin{cases}s,&q\le n-2,\\t,&q=n-1.\end{cases}
\end{aligned}
\tag{8.5}
$$

$p_n(u)$ 是两个目标的共同允许纯前缀。
末切口的 $v_{n-1}=A_{n-1}^{(n)}$ 仍服从旧报告
$p_n(u)_{n-1}=2$ 的同一个闭一误差约束。
完整的 $B_{n,q}$ 是无预算不相容性所需的接口。

第二套是部分费用伴随。对每个 $s\in[0,1/2]$，置
$u_s=\tau_s+1/16$。对每个 $0\le q<n$，有另一组严格正 $(x,v)$ 满足

$$
\sum_{h=0}^{n-1-q}x_h=1,\qquad
|A_i^{(n)}(x,v)-p_n(u_s)_i|\le1\ (0\le i\le q),\qquad
|v_j-b_j^{(q)}(R_s^{(n)})|\le2\ (0\le j\le J_n(q)).
\tag{8.6}
$$

$p_n(u_s)$ 属于该目标的允许纯前缀盒。在末切口还保持同一份旧末报告
$2$ 的约束，即 $x_0=1$、$|v_{n-1}-2|\le1$。
这里不要求未列出的未来坐标相容；这套见证只供 $2n-2$ 报告下界消费。

两套伴随可按各自的全部参数和切口选取，使

$$
A_0^{(n)}(x,v)=a_0^{(n)},\qquad
0<x_h\le X_n,\quad 0<v_j\le V_n,\quad v_{n-1}\ge m_n>0.
\tag{8.7}
$$

这些是同一维数上统一的有限界；不要求各 $x_h$ 有统一正下界。
归一化已经蕴含 $x_0\le1$。再记来源界

$$
\begin{aligned}
H_s&=1+\sum_{j=2}^{n-1}c_{j,s}\le H_n,&
T_{n,s}&=w_{0,s}+\sum_{j=2}^{n-1}c_{j,s}r_{j-1,s}\le T_n,\\
1\le r_{j,s}&\le R_n,&1\le w_{j,s}&\le W_n,
\end{aligned}
\tag{8.8}
$$

其中 $H_n,T_n,R_n,W_n$ 均为有限正数。标量 $T_{n,s}$ 与六维矩阵
$T_s$ 是不同对象。式 (8.7) 供新增尾权重的正性与下一维的界使用；
式 (8.8) 只量化闭区间上的来源参数，不把开重叠域变成紧集。

### 定理 8.2（精确六维基例的同时不变量）

引理 6.2 的原矩阵 $R_s^{(6)}=T_s$ 满足 $\mathcal I_6$，可以取

$$
\begin{gathered}
H_6=2\cdot10^{12},\quad T_6=2\cdot10^{13},\quad
R_6=10000,\quad W_6=17,\\
X_6=2\cdot10^{12},\qquad V_6=2\cdot10^{16},\qquad m_6=\tfrac12.
\end{gathered}
\tag{8.9}
$$

证明。来源行形、纯数据 $(10^{12},10000,100,15,18,1)$ 及正分解
直接由引理 6.2 与 (6.4) 给出；生成行的最小坐标为一，
末两列子式为 $10\cdot8-23/2=137/2$。
其中 $\lambda_s\le1$、$\mu_s<8988$、$0<\nu_s<10^{12}$，
所以 $H_s<2\cdot10^{12}$，且

$$
T_{6,s}=1+1000\lambda_s+c_s+(3-s)\mu_s+10\nu_s<2\cdot10^{13}.
$$

生成行的上界为 $10000,17$。正分解的因子连续且在闭区间上严格正，
因此其统一正下界只涉及来源因子。式 (8.4) 正是命题 6.3
已证明的两个辅助系统排除谓词，包括阈值等号的归属。

完整库直接取引理 7.2 的全部六个伴随，部分库取引理 6.4 的六个伴随。
它们的相应可见上界是
$(J_6(0),\ldots,J_6(5))=(5,5,5,5,4,3)$。
特别地，完整库末切口的末真值为三，部分库的末真值为二；
两者都使用旧报告二，却不能互相替代。

还须核对下一维实际消费的界，而非只引用见证存在。
$q=0$ 时 $v=b^{(0)}(T_s)$；上述系数界更具体给出
$H_s<10^{12}+8991$，故由 (6.3)，
$1/2\le v_j\le10000(10^{12}+8991)+17<2\cdot10^{16}$。其余切口的 $v$ 是
(6.8) 的首坐标 $\beta_q$ 加上引理 6.4 或 (7.4)、(7.6) 的旧向量。
$\beta_1<9\cdot10^7$，$\beta_q\le30001$（$q\ge2$）；
旧早切口的 $v_j<9\cdot10^6$，晚切口的 $v_j\le3001$。
所有这些坐标至少为 $1/2$：最小候选是 (7.6) 的 $1-t$；
其余旧早切口向量见
[IV 引理 22.4](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md)，
部分末切口向量见 IV (24.7) 与引理 6.4。
每个伴随都由凸组合或尾权重方程给出 $A_0=10^{12}$，
故正项和 $\sum x_hv_h=10^{12}$ 蕴含 $x_h\le2\cdot10^{12}$。
于是 (8.9) 同时控制两库的所有坐标和末 $v$。

这里没有给 $x$ 的统一正下界：完整库中与
$u-\tau_s$ 或 $\tau_t-u$ 成正比的正坐标可以趋近零。
上述上界与末 $v$ 下界直接来自显式式子，对整个开重叠域有效。∎

### 定理 8.3（同时保存安全谓词与两库的构造）

若 $\mathcal I_n$ 成立，按该维数的有限常数取

$$
\begin{aligned}
B&=H_n+10,\\
K&=2(B+T_n)+BH_n+(n-1)X_nV_n+2,\\
r_s^+&=(B,r_s),\qquad w_s^+=(1,w_s),\qquad
\mu_s=K-B-T_{n,s},\\
R_s^{(n+1)}
&=\begin{pmatrix}
r_s^+\\w_s^+\\c_{2,s}r_s^+\\\vdots\\c_{n-1,s}r_s^+\\\mu_sr_s^+
\end{pmatrix}.
\end{aligned}
\tag{8.10}
$$

则 $\mathcal I_{n+1}$ 成立。以下是一组同时适用的下一维界：

$$
\begin{aligned}
R_{n+1}&=\max(B,R_n),&W_{n+1}&=\max(1,W_n),\\
H_{n+1}&=H_n+K,&T_{n+1}&=1+(H_n+K)R_n,\\
X_{n+1}&=\max(1,X_n,K/m_n),&
m_{n+1}&=\min(m_n,8),\\
V_{n+1}&=\max\{V_n,BH_n+1,(H_n+K)R_{n+1}+W_{n+1}\}.
\end{aligned}
\tag{8.11}
$$

新纯向量与两类报告前缀分别为

$$
a^{(n+1)}=(K,a^{(n)}),\qquad p_{n+1}(u)=(K,p_n(u)).
\tag{8.12}
$$

证明。构造复用
[IV 定理 22.6](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md)
的行提升；需要同时检查的是 (8.4)--(8.7)，而非仅正性。
由 $K>2(B+T_n)$ 得 $\mu_s>B>0$，且 $\mu_s<K$。
生成行的坐标仍至少为一，末两列与原来相同；末项仍为一和八。
新 $H_s^+=H_s+\mu_s\le H_n+K$。
对新 $T_{n+1,s}$，除首项 $w_0^+=1$ 外，每个被乘的生成行坐标都是
旧 $r_s$ 的坐标，故 $T_{n+1,s}\le1+(H_n+K)R_n$。
这证明 (8.11) 的四个来源界。

为明确两项严格正表示，写
$C_s^+=(1,0,c_{2,s},\ldots,c_{n-1,s},\mu_s)^{\mathsf T}$、
$e=e_1$，取常数
$\alpha=[2\max(R_{n+1},W_{n+1})]^{-1}$。则 $0<\alpha<1$，
且 $r_s^+-\alpha w_s^+$、$w_s^+-\alpha r_s^+$ 的每个坐标至少为 $1/2$。
因而

$$
R_s^{(n+1)}
=\frac{(C_s^++\alpha e)(r_s^+-\alpha w_s^+)
       +(\alpha C_s^++e)(w_s^+-\alpha r_s^+)}
      {1-\alpha^2}
\tag{8.13}
$$

是连续的两项严格正外积分解。
所有继承的系数在闭参数区间上有正下界，$\mu_s>B$，
故这里的因子也有统一正下界。非零末子式及两项表示分别给出秩至少二和至多二，
所以普通秩恰为二。此紧致性论证只用于来源参数。

新初读为 $B+T_{n,s}+\mu_s=K$。
每条其余上对角线逐项移位，得 $a_i^{(n+1)}=a_{i-1}^{(n)}$（$1\le i\le n$）。
对旧切口 $q$ 与其新切口 $q+1$，行截断同时给出

$$
b_0^{(q+1)}(R_s^{(n+1)})=\beta_{q,s},\qquad
0<\beta_{q,s}\le BH_n+1,\qquad
b_{j+1}^{(q+1)}(R_s^{(n+1)})=b_j^{(q)}(R_s^{(n)}).
\tag{8.14}
$$

若截断只剩首行则 $\beta_{q,s}=B$；否则它是
$B$ 乘以截断内的生成行系数之和再加一，该系数和不超过 $H_s$。

先证明任意辅助解的反向投影，这是安全性的方向。
给定新切口 $q+1$ 的任意严格正解 $(\widetilde x,\widetilde v)$，
删除 $\widetilde x_n$ 和 $\widetilde v_0$，令
$x_h=\widetilde x_h$、$v_j=\widetilde v_{j+1}$（$h,j<n$）。
直接逐项有

$$
\sum_{h=0}^{n-1-q}x_h=1,\qquad
A_i^{(n)}(x,v)=A_{i+1}^{(n+1)}(\widetilde x,\widetilde v)
\quad(0\le i<n).
\tag{8.15}
$$

式 (8.14) 把旧的全部新坐标约束逐一保留：
非末切口的全部坐标都被投影，末切口的
$B_{n+1,n}=\{0,\ldots,n-1\}$ 则投影到
$B_{n,n-1}=\{0,\ldots,n-2\}$。在后者，
$\widetilde v_n=v_{n-1}$ 与
$A_n^{(n+1)}=A_{n-1}^{(n)}$ 仍用同一份旧末报告。
于是对任意允许新纯前缀 $y^+$，

$$
\mathsf C_{n+1,q+1}(R_s^{(n+1)},y^+)
\ \Longrightarrow\
\mathsf C_{n,q}(R_s^{(n)},(y^+_1,\ldots,y^+_{q+1})).
\tag{8.16}
$$

被保留的报告是旧目标的一份允许前缀，由 (8.12) 即知；
新首报告可为 $[K-1,K+1]$ 中任意值。
取 $q=n-2,n-1$，旧安全谓词 (8.4) 就给出新的两个安全谓词，
阈值仍为 $\tau_s$，分支坐标从 $n-2$ 移到 $n-1$。
这没有把一个选定伴随的正向提升误用成任意解的反向投影。

再提升两库中的选定伴随。对其所配的目标参数 $\sigma$，取
$\beta=\beta_{q,\sigma}$，并定义

$$
\begin{aligned}
v^+&=(\beta,v),&x^+&=(x_0,\ldots,x_{n-1},z),\\
z&=\frac{K-x_0\beta-\sum_{h=1}^{n-1}x_hv_{h-1}}{v_{n-1}}.
\end{aligned}
\tag{8.17}
$$

归一化给 $x_0\le1$，两库共同的界给出

$$
x_0\beta+\sum_{h=1}^{n-1}x_hv_{h-1}
\le BH_n+1+(n-1)X_nV_n<K.
\tag{8.18}
$$

故 $0<z<K/m_n$。所有旧 $A_i$ 向右移一位，新 $A_0^+=K$，
旧归一化恰为新归一化；这是同一组正因子实现的全部约束。
新坐标零由 $\beta$ 精确匹配，其余坐标按 (8.14) 继承。
新末 $v$ 就是旧末 $v$，旧共享报告保持不变。
两库的坐标上界分别由
$\max(X_n,K/m_n)$ 与 $\max(V_n,BH_n+1)$ 控制，末 $v\ge m_n$。

完整库的量词为所有 $s<t$、$\tau_s<u<\tau_t$、所有切口。
新切口 $q+1\le n-1$ 继承旧的 $s$ 伴随，新末切口 $n$ 继承旧的 $t$ 伴随；
所以目标指派与 (8.5) 一致，且每个 $B_{n+1,q+1}$ 坐标均已包含。
部分库仍固定各自的 $u_s$；其坐标范围恰满足

$$
J_{n+1}(q+1)
=\min(n,\,2n-q-3)
=1+\min(n-1,\,2n-q-4)
=1+J_n(q).
\tag{8.19}
$$

因此新范围中的每个 $j\ge1$ 对应旧库已携带的 $j-1$，而 $j=0$ 精确匹配。
新末切口另有的共享旧报告也由同一个提升保留。
这里没有要求部分库额外满足完整库的未来坐标条件。

还缺新切口零，不能靠移位略去。
对其配对目标取 $v^+=b^{(0)}(R_\sigma^{(n+1)})$，则

$$
v_n^+=H_\sigma+\mu_\sigma+8
=K-B-T_{n,\sigma}+H_\sigma+8<K,
\qquad
v_0^+=B(H_\sigma+\mu_\sigma)+1>K.
\tag{8.20}
$$

第一式由 $B=H_n+10$ 与 $T_{n,\sigma}>0$ 得到。
第二式用 $K>2(B+T_{n,\sigma})$ 得
$B\mu_\sigma>K$，因为 $\mu_\sigma>K/2$、$B>2$。
III 命题 9.6 的严格正凸组合给出
$x^+>0$、$\sum_{h=0}^nx_h^+=1$、$A_0^+=K$，从而全部 $x_h^+\le1$。
也可在该引用的构造中为中间坐标先选一个充分小的共同正权重，再由
端点 $v_0^+,v_n^+$ 解出两个剩余正权重；严格夹持保证可行，
不需要一组统一正下界。
这给完整库 $q=0$ 的 $s$ 目标伴随，也给每个部分库的 $q=0$ 伴随。

最后，新零切口的每个 $v_j^+$ 不超过
$(H_n+K)R_{n+1}+W_{n+1}$，其末坐标大于八。
与 (8.17) 的界合并，正好得到 (8.11) 的 $X,V,m$ 三界。
它们逐项成立于两库的整个参数域，包括开重叠域。
新前缀的合法性由 (8.12) 与旧合法性得到；
安全谓词、行形、纯向量及两套库全部保留，故 $\mathcal I_{n+1}$ 成立。∎

## 9. 任意有限维的精确费用与无预算覆盖

### 定理 9.1（同时归纳的完整历史结论）

从原六维 $T_s$ 出发，按 (8.10)--(8.11) 递归定义 $R_s^{(d)}$。
对每个有限整数 $d\ge6$、每个有限实数 $\varepsilon>0$ 和每个
$s\in[0,1/2]$，在定义 8.1 的完整 $\mathcal M_d$ 合同上，

$$
c_{d,\varepsilon}(\varepsilon R_s^{(d)})=2d-1.
\tag{9.1}
$$

这里 $c$ 是定义 6.5 的逐来源全误差报告费用在维数 $d$ 的版本：
取遍完整域可靠的确定性协议，要求在指定来源的每条允许历史上，
都在给定报告预算内输出二；初读也收费。

若不要求共同的停止预算，而只要求每条允许历史有限输出二，
用定义 7.1 的维数 $d$ 版本记成功集与预选覆盖数，则每个完整域
$\varepsilon$-可靠的确定性完整历史协议 $\Pi$ 都满足

$$
\left|\{s\in[0,1/2]:
\varepsilon R_s^{(d)}\in\operatorname{Succ}_{d,\varepsilon}(\Pi)\}\right|
\le1.
\tag{9.2}
$$

因此每个有限 $F\subseteq[0,1/2]$，包括空集，都有

$$
\begin{aligned}
\nu_{d,\varepsilon}(\{\varepsilon R_s^{(d)}:s\in F\})&=|F|,\\
\nu_{d,\varepsilon}(\{\varepsilon R_s^{(d)}:0\le s\le1/2\})&=\infty.
\end{aligned}
\tag{9.3}
$$

若另外限制每个覆盖成员在其覆盖来源上至多 $2d-1$ 报告成功，
有限 $F$ 的覆盖数仍恰为 $|F|$。
各维只使用自己的有限常数；本结论不含维数一致的界。

证明。定理 8.2--8.3 给出每个有限 $d\ge6$ 的 $\mathcal I_d$。
先证明单位容限结论。

上界的协议先取得初读，再连续执行 $d-2$ 次 $N$。
若实际 $y_{d-2}\le\tau_s$，就在切口 $d-2$ 执行
$L_0N^{d-1}$，取得全部 $d$ 个新坐标；
若 $y_{d-2}>\tau_s$，先再执行一次 $N$，在切口 $d-1$
执行 $L_0N^{d-2}$，只取得 $d-1$ 个新坐标。
两个总费用分别为

$$
(d-1)+d=2d-1,\qquad d+(d-1)=2d-1.
\tag{9.4}
$$

高分支末坐标使用已取得的 $y_{d-1}$，不再读取。
末端只在实际报告系统 $\mathsf D_{d,q}$ 无严格正解时输出二，
否则停止而不作秩断言。
对任何严格正秩一来源 $S=c\ell$，以
$t=\sum_{h=0}^{d-1-q}c_h>0$、$x=c/t$、$v=t\ell^{\mathsf T}$
得到其全部实际报告的一个 $\mathsf D$ 解，故协议在完整域上可靠。
对于目标的任意允许报告，$\mathsf D\Rightarrow\mathsf C$，
而 (8.4) 排除所选切口的 $\mathsf C$，故在每条目标历史上均输出二。
这用的是全部允许实际前缀，不只是 (8.3) 的特殊前缀。

费用下界直接针对原协议的付费动作。
假设某完整域可靠协议在固定 $R_s^{(d)}$ 的每条允许历史上都以
至多 $2d-2$ 份报告输出二。首次 $L_0$ 前依次报告 $p_d(u_s)$。
这是一份允许前缀，且全部坐标严格正。
若在任何纯 $N$ 前缀（包括初读）停止，
[III 引理 10.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md)
以这些正数给出精确实现它们的一个固定严格正秩一来源。
确定性使停止与输出相同，可靠性排除输出二。
若执行了第 $d$ 次 $N$，则 $N^d=0$；此后无论选哪个原子都保持零，
一直报告零。对前面全部 $d$ 个正数取同一纯前缀插值来源，
它在整条零尾上仍重放相同历史，也排除有限输出二。
因此假设的成功历史必在某个 $0\le q<d$ 首次执行 $L_0$。

固定该切口的部分库伴随 $S=xv^{\mathsf T}$。
首次 $L_0$ 后，若非零累计矩阵的当前坐标是 $b_j^{(q)}$，
从初读起取得这份报告至少已经支付

$$
1+q+1+j=q+j+2
\tag{9.5}
$$

份报告。确切地，首次 $L_0$ 之前有 $q$ 个 $N$，它本身再付一次；
每个 $N$ 使当前指标增加一，而再次 $L_0$ 只把指标重置为零。
要到达 $j$，最近一次 $L_0$ 后仍至少需要 $j$ 个 $N$，
此前的重复原子只能增加已付费用。若任何一段有 $d$ 个连续 $N$，
状态已经永久为零。这是 III 引理 10.1 的完整字归约，覆盖全部重复操作。
因此 $2d-2$ 报告内可达到的非零指标必满足 $j\le J_d(q)$；
反之每个 $0\le j\le J_d(q)$ 都可由首次 $L_0$ 后连续 $j$ 个 $N$
达到。末切口已有的共享坐标还由同一旧报告二约束，
它不作为额外可取得的数据收费。

对这些可见新坐标固定报告表

$$
w_j=\frac{b_j^{(q)}(R_s^{(d)})+v_j}{2}
\quad(0\le j\le J_d(q)).
\tag{9.6}
$$

部分库保证每个报告距两来源的真值都至多一；
旧前缀也由同一个 $S$ 满足。对重复坐标使用同一 $w_j$，
永久零状态报告零。对实际历史长度归纳，两个来源上
每个动作、报告、停止及输出相同，直到且包括第 $2d-2$ 份报告。
目标上的假设要求在此期间输出二，便在秩一 $S$ 上作出同样输出，
违反完整域可靠性。若需要延长历史，预算后的报告可在各来源上各自合法补全；
矛盾已经发生在共同的有限停止历史，不需要未携带坐标的共同补全。
这证明 (9.1) 的单位下界；没有调用 III 定理 14.2 的正规形来保持原费用。

无预算不相容性另用完整库证明。反设同一可靠完整历史协议在
$R_s^{(d)},R_t^{(d)}$ 上都全误差成功，$s<t$。
选任意 $\tau_s<u<\tau_t$，在首次 $L_0$ 前依次报告共同前缀 $p_d(u)$。
纯前缀停止及越过 $N^d=0$ 后的永久零尾，
分别由刚才的一个固定纯前缀插值来源排除；
在全误差成功假设下，必须有限进入某个实际首次切口 $q<d$。
这个切口由已取得的共同报告确定，不预先选择一个有利动作词。

此时固定完整库对应的一个目标
$R_\sigma^{(d)}$（$q\le d-2$ 时 $\sigma=s$，$q=d-1$ 时 $\sigma=t$）
以及一个严格正秩一伴随 $S=xv^{\mathsf T}$。
整个后继历史只使用这两个固定来源。
在 $j\in B_{d,q}$ 固定全部中点报告

$$
w_j=\frac{b_j^{(q)}(R_\sigma^{(d)})+v_j}{2};
\qquad
w_{d-1}=p_d(u)_{d-1}=2\quad(q=d-1).
\tag{9.7}
$$

第二式使用同一个已取得的旧末报告；它也规定该坐标若在以后真的重复出现，
就仍报告二，而非引入一份独立误差。
(8.5) 给出每个新坐标在两个来源上的闭一误差合法性；
共享坐标的合法性由旧约束和 $v_{d-1}=A_{d-1}$ 给出。

III 引理 10.1 穷尽所有后继：每个非零累计矩阵是
$N^jL_0N^q$，再次 $L_0$ 返回指标零，重复坐标仍用 (9.7)；
达到零累计矩阵后全部报告恒为零。
因而这一张固定表和旧前缀给出两个固定来源上的完整合法历史，
没有按坐标或时间更换伴随。
逐前缀确定性归纳使动作、停止和输出在任意长度均相同，
无需连续性、可测性或停止时间统一有界。
协议在所选目标上全误差成功，迫使这条历史有限输出二；
同一输出发生在秩一 $S$ 上，矛盾。
这直接证明无预算的 (9.2)，并未从费用下界推导它。
固定表允许误差相关及闭端点，符合原合同。

对任意 $\varepsilon>0$，$R\mapsto\varepsilon R$ 是完整
$\mathcal M_d$ 的保严格正性、保普通秩双射，且对每个实际累计字 $A$，

$$
\operatorname{tr}(A\varepsilon R)
=\varepsilon\operatorname{tr}(AR).
\tag{9.8}
$$

把每份单位报告乘以 $\varepsilon$ 后交给一个
$\varepsilon$-协议，逐步执行它选定的原子、停止与输出，
得到单位协议；反向则把报告除以 $\varepsilon$。
这是完整历史及其闭误差的双向对应，覆盖任意相关误差，
保持每条历史的报告费用和完整域可靠性。
中点、阈值与共享旧报告也同时缩放。
因此单位费用上下界和单位不相容性给出所有正容限的 (9.1)--(9.2)。

最后，递归始终保留
$(R_s^{(d)})_{0,d-3}=3-s$，故参数不同就来源不同。
(9.2) 使每个预选成员至多覆盖一个参数；
(9.4) 的逐来源协议给有限 $F$ 的 $|F|$ 个覆盖成员。
空 $F$ 取空协议族，故覆盖数为零。
任意 $m$ 个成员至多覆盖 $m$ 个参数，选 $m+1$ 个不同参数就排除
整个连续族的有限覆盖，得到 (9.3)。同一上界协议都只用 $2d-1$ 报告，
所以另加此预算也不改变有限覆盖数。∎

定理 8.3--9.1 是对 IV22.6 条件递归的同时接口闭合：
来源行提升、严格正分解、字归约、严格正凸组合与实际报告相容判据
分别复用 IV22.6、VIII6.2、III10.1、III9.6、III13--14；
VIII6.4 与 VIII7.2 分别供给两库，新增归纳保留它们不同的量词和坐标范围。
五维的精确九报告费用与同容限有限预选结论仍分别由
[IV 定理 24.2 与定理 22.5](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md)
给出，无需重建该维证明。

相关一般理论的适用条件不能代替这里的同时构造。
van den Bos--Vaandrager，
[*State Identification for Labeled Transition Systems with Inputs and Outputs*，
Theorem 6.1、Definition 16](https://arxiv.org/html/1907.11034v2)
在不同状态两两不相容的 suspension automaton 上，以 injective splits
刻画 adaptive distinguishing graph 的存在；该条件不提供本族的
连续正来源、闭误差中点或精确报告账。
Petreczky--Bako--van Schuppen，
[*Realization theory of discrete-time linear switched systems*，
Theorem 4](https://arxiv.org/html/1103.1343v2)
的可观测性与张成可达性是由所有相应模态字组成的矩阵秩条件，
不把这些字自动合成一条破坏性实际轨迹。
Petreczky--Bako，
[*On the notion of persistence of excitation for linear switched systems*，
Definition 14、Theorem 3](https://arxiv.org/html/1103.1349v1)
的有限激励输入存在定理要求每个模态矩阵可逆；
这里 $N,L_0$ 都奇异，且没有附加控制把状态送回初态。
这些是所引文献中的一般结论；本节的同时带噪正秩族结论为
repo-derived，不据检索未命中宣称外部原创。

上述定理只断言所构造族在每个有限维的逐来源费用和预选覆盖量词。
它们不决定原多项式漂移初根问题，也不构造未知来源的在线选择器；
不涉及随机协议、零容限、物理实现、有效实数判定或位复杂度。
来源域仍是完整严格正的秩一/秩二域，未限制为所构造族，
也没有断言任意正性保持提升都保存这些结论。

## 追加锚（本行以下为增补区）

## 10. 私有随机切口的逐来源最坏成功概率

### 定义 10.1（私有种子、公共因果误差与两种成功事件）

固定有限整数 $d\ge6$ 和有限实数 $\varepsilon>0$，记
$R_{\varepsilon,s}=\varepsilon R_s^{(d)}$，$s\in[0,1/2]$，其中
$R_s^{(d)}$ 恰为定理 8.2--8.3 的递归族。
可靠性的环境域仍为完整的 $\mathcal M_d$，而成功概率的来源下确界只取此族。
原子、单条不可复制不可复位轨迹、普通初始实秩及收费均沿用定义 8.1。

一个私有随机协议由概率空间 $(\Omega,\mathcal F,\mu)$ 和一族确定性完整历史
协议 $(\Pi_\omega)_{\omega\in\Omega}$ 给出。初始种子 $\omega$ 在运行前抽取，
不公开；以后的私有选择都可包含在这个种子中。
实际来源与误差规则在抽种子前固定，各来源和规则都使用同一个种子概率律 $\mu$。
每个固定 $\omega$ 的 $\Pi_\omega$ 都须在完整 $\mathcal M_d$ 上
$\varepsilon$-可靠：对每个来源和每条允许数值误差历史，有限输出二必为正确。
这项逐种子、逐历史的要求是路径可靠性。

公共历史在第 $i$ 个原子前为
$h=(y_0,E_1,y_1,\ldots,E_{i-1},y_{i-1})$，包含已经执行的动作、已经取得的
报告及其顺序。协议先从 $\omega,h$ 选当前动作 $E_i\in\{N,L_0\}$，
然后才取得并计费报告 $y_i$；停止与输出也由 $\omega,h$ 决定。
对固定实际来源 $R$，公共因果误差规则 $\mathcal E_R$ 可以是
$(R,h,E_i)$ 的任意确定性函数，给出满足

$$
 y_i=\operatorname{tr}(A_iR)+\eta_i,\qquad
 A_0=I,\quad A_i=E_iA_{i-1},\qquad |\eta_i|\le\varepsilon
\tag{10.1}
$$

的报告。初读规则只用固定 $R$。规则不能读隐藏种子或未来私有选择，但可以利用
公共历史对种子作出的任何推断；当前动作已经公开。规则须在所有合法输入上满足
闭误差界，不仅在某一实际运行上满足。记这种规则的集合为 $\mathscr E(R)$。
这里没有独立性、均值或非相关条件。

只要求下述种子截面可测：对每个固定 $R\in\mathcal M_d$ 和每个
$\mathcal E_R\in\mathscr E(R)$，事件

$$
 Z_\Pi(R,\mathcal E_R)
 =\{\omega:\Pi_\omega\text{ 在 }(R,\mathcal E_R)
                   \text{ 上有限输出二}\}
 \quad\text{属于 }\mathcal F.
\tag{10.2}
$$

不赋予来源集、规则集或全部历史集共同的 Borel 结构，也不假定这些变量的联合
可测性。一个种子族只有满足 (10.2) 时才作为这里的概率协议；有限种子空间取
幂集 $\sigma$-代数自动满足它。定义操作概率

$$
 v_\Pi(s)=\inf_{\mathcal E\in\mathscr E(R_{\varepsilon,s})}
          \mu Z_\Pi(R_{\varepsilon,s},\mathcal E),\qquad
 V_{d,\varepsilon}=\sup_\Pi\inf_{s\in[0,1/2]}v_\Pi(s).
\tag{10.3}
$$

上确界遍历上述路径可靠且满足 (10.2) 的协议，不限制停止时间或使用的公共历史。
与 (10.2) 不同，种子逐个抗全部误差的事件是

$$
 G_\Pi(s)=\{\omega:R_{\varepsilon,s}
                   \in\operatorname{Succ}_{d,\varepsilon}(\Pi_\omega)\}.
\tag{10.4}
$$

只有另行满足 $G_\Pi(s)\in\mathcal F$ 时才给它概率；
(10.2) 不保证这个含全称量词的事件可测。
$\mu G_\Pi(s)$ 中的误差可随固定种子分别选择，
而 (10.3) 的每个误差规则必须在全部种子间保持同一个公共因果函数。

### 引理 10.2（两个固定目标的种子盲因果报告耦合）

对每个 $0\le s<t\le1/2$ 和每个 $\tau_s<u<\tau_t$，存在两个规则

$$
 \mathcal E_s^{s,t,u}\in\mathscr E(R_{\varepsilon,s}),\qquad
 \mathcal E_t^{s,t,u}\in\mathscr E(R_{\varepsilon,t}),
\tag{10.5}
$$

只依赖已执行的公共动作字，且与协议和隐藏种子无关，使每个定义 10.1 的路径
可靠协议及每个 $\omega\in\Omega$ 都满足

$$
 \mathbf1_{Z_\Pi(R_{\varepsilon,s},\mathcal E_s^{s,t,u})}(\omega)
 +\mathbf1_{Z_\Pi(R_{\varepsilon,t},\mathcal E_t^{s,t,u})}(\omega)
 \le1.
\tag{10.6}
$$

两个实际来源在各自的整条运行上固定；耦合仅在证明中给它们使用同一个种子。
规则不在运行中把一个实际来源换成另一个。

证明。先取单位容限，写 $p=p_d(u)$。由 (8.3)，它与所有目标的纯真值
$a^{(d)}$ 仅在末三个坐标可能不同：报告为 $16,u,2$，真值为 $15,18,1$。
因 $17\le\tau_s<u<\tau_t\le17+1/8$，每个差的绝对值至多一，且所有
$p_i>0$。所以 $p$ 是两个固定目标共同允许的完整纯 $N$ 前缀。

在运行前，用完整库 (8.5) 为每个 $q=0,\ldots,d-2$ 各固定一个
$s$ 目标的伴随 $S_{s,q}=x^{s,q}(v^{s,q})^{\mathsf T}$，再为 $q=d-1$
固定一个 $t$ 目标的伴随 $S_{t,d-1}$。它们都是同一组严格正因子给出的
秩一来源，并同时满足

$$
 \begin{aligned}
 \sum_{h=0}^{d-1-q}x_h^{\sigma,q}&=1,\qquad
 |A_i^{(d)}(x^{\sigma,q},v^{\sigma,q})-p_i|\le1
       &&(0\le i\le q),\\
 |v_j^{\sigma,q}-b_j^{(q)}(R_\sigma^{(d)})|&\le2
       &&(j\in B_{d,q}),
 \end{aligned}
\tag{10.7}
$$

其中 $(\sigma,q)$ 取 $(s,0),\ldots,(s,d-2),(t,d-1)$。
特别地，$q=d-1$ 时 $x_0^{t,q}=1$，
$v_{d-1}^{t,q}=A_{d-1}^{(d)}(x^{t,q},v^{t,q})$，
并由同一份旧报告 $p_{d-1}=2$ 满足闭一误差界。
这里使用的是全部 $B_{d,q}$，没有以部分费用库 (8.6) 代替。

为这些固定伴随预先定义报告表

$$
 \begin{aligned}
 W_{\sigma,q,j}
   &=\frac{b_j^{(q)}(R_\sigma^{(d)})+v_j^{\sigma,q}}2
       &&(j\in B_{d,q}),\\
 W_{t,d-1,d-1}&=p_{d-1}=2.
 \end{aligned}
\tag{10.8}
$$

第一行由 (10.7) 保证距两个真值均至多一。
第二行不是另选中点：目标上
$b_{d-1}^{(d-1)}=a_{d-1}=1$，伴随上
$b_{d-1}^{(d-1)}=v_{d-1}^{t,d-1}=A_{d-1}^{(d)}$，
故旧报告二在两来源上都合法，且在未来确实重复取得该坐标时仍用二。
这直接保留 III 引理 13.2、定义 14.3 与引理 14.4 的同组正因子和共享报告条件。

以下把表变成对每个公共动作字都有定义的两个规则。
初读以及首次 $L_0$ 前的 $N^i$，$i<d$ 时都报告 $p_i$。
若累计矩阵已经为零，就报告零，并在以后永久报告零。
其余情形，III 引理 10.1 给出首次 $L_0$ 前的唯一计数 $q<d$，以及当前
非零累计矩阵的形式 $N^jL_0N^q$，$0\le j<d$。
在实际来源 $R_s^{(d)}$ 上，$q\le d-2$ 时报告 $W_{s,q,j}$，
$q=d-1$ 时报告实际真值 $b_j^{(q)}(R_s^{(d)})$。
在实际来源 $R_t^{(d)}$ 上，$q=d-1$ 时报告 $W_{t,d-1,j}$，
$q\le d-2$ 时报告实际真值 $b_j^{(q)}(R_t^{(d)})$。

每个规则只有自己的一个实际目标。动作字包括刚选择的当前原子，因此第一次
$L_0$ 的报告已经能够合法地使用公开的 $q$。纯 $N$ 达到第 $d$ 次，或者
某个 $L_0$ 后连续执行 $d$ 次 $N$，都会永久进入零分支；再次 $L_0$ 不能
从零恢复。非零时，再次 $L_0$ 只重置 $j=0$，再次取得同一 $j$ 就使用同一
张表的同一个值。以上规则在任意公共报告输入上都满足固定目标的闭误差界，
包括与规则先前输出不一致的输入；它们只读动作字，不读那些报告的数值。
因而它们是整个公共历史空间上的因果规则，不是事后按种子挑出的一条误差序列。

还须验证表确实阻断任意长的有限认证。若 $s$ 目标的运行在某个
$q\le d-2$ 首次执行 $L_0$，就在证明中选用已经预定的那一个 $S_{s,q}$。
此前纯报告由 (10.7) 在这个伴随上合法；以后每个非零坐标由 (10.8) 合法，
每个零尾报告也合法。对固定 $\omega$，从初读开始逐公共前缀重放
$\Pi_\omega$，每个动作、停止及输出都相同。伴随在整个重放中不再改变，
所以路径可靠性排除该运行的任何有限输出二。此论证也适用于 $t$ 目标的
$q=d-1$，并保留旧末报告。任意多次重复动作、重读坐标或任意长停止时间
都被这张完整表覆盖。

纯 $N$ 停止及先湮灭的分支另行处理。III 引理 10.3 对全部正数
$p_0,\ldots,p_{d-1}$ 给出一个运行前固定的严格正秩一来源 $S_*$，精确实现
整个纯前缀。若在首次 $L_0$ 前停止，它重放已经取得的前缀，故不能输出二。
若在首次 $L_0$ 前已执行 $d$ 次 $N$，两个来源在此前使用相同的 $p$，
此后与 $S_*$ 都永久为零，对任意后继动作继续报告零，仍不能有限输出二。
这包括初读即停、永不选择 $L_0$ 以及湮灭以后才选择 $L_0$。

现在把同一个任意种子 $\omega$ 用于两个固定实际目标。
它们首次 $L_0$ 前的报告相同，故动作、早停和首次切口也相同；若已先湮灭，
二者的零尾也相同。早停或先湮灭时二者都不能成功。
其余情形有一个共同的 $q<d$：$q\le d-2$ 时 $s$ 目标被固定的
$S_{s,q}$ 阻断，$q=d-1$ 时 $t$ 目标被固定的 $S_{t,d-1}$ 阻断。
这就逐种子证明 (10.6)。两个规则在选择种子之前已经确定；伴随的量词为
先固定有限的全部表，重放时只按已公开的切口引用其中一个，而不是先看种子
再换误差规则。

最后把实际目标、伴随、每份报告及报告表同时乘以 $\varepsilon$。
对任意动作字的累计矩阵 $A$ 都有
$\operatorname{tr}(A\varepsilon R)=\varepsilon\operatorname{tr}(AR)$；
严格正性、普通秩、每个闭端点和全部重复报告均保留。
给定任意容限 $\varepsilon$ 的协议，把单位报告乘以 $\varepsilon$ 后交给它，
就得到单位协议的同一动作与停止历史；所以刚才的逐种子结论直接给出
(10.5)--(10.6)，费用和任何停止时间均不变。∎

### 定理 10.3（操作值为二分之一及其有界达到）

在定义 10.1 的每个有限 $d\ge6$、每个有限 $\varepsilon>0$ 上，

$$
 V_{d,\varepsilon}=\frac12.
\tag{10.9}
$$

一个不依赖未知 $s$ 的单一协议达到此值，且在完整 $\mathcal M_d$ 的每条运行
上恰于 $2d-1$ 份收费报告后停止。上界则适用于任意完整历史和无统一预算的协议。
更具体地，每个定义 10.1 的协议都满足逐对约束

$$
 v_\Pi(s)+v_\Pi(t)\le1\qquad(s\ne t).
\tag{10.10}
$$

若另要求每个 (10.4) 可测，则更强的种子逐个全误差保证满足

$$
 \sup_{\Pi:\ G_\Pi(s)\in\mathcal F\ \text{对所有 }s}
       \inf_{s\in[0,1/2]}\mu G_\Pi(s)=0.
\tag{10.11}
$$

证明。对上界，固定任意路径可靠协议，任选 $s<t$ 和中间 $u$。
引理 10.2 的两个成功事件由 (10.2) 可测，且逐点不相交。因此

$$
 \begin{aligned}
 v_\Pi(s)+v_\Pi(t)
 &\le\mu Z_\Pi(R_{\varepsilon,s},\mathcal E_s^{s,t,u})
      +\mu Z_\Pi(R_{\varepsilon,t},\mathcal E_t^{s,t,u})\\
 &\le1.
 \end{aligned}
\tag{10.12}
$$

这里的有限相加只是通常的概率可加性；承重步骤是引理 10.2 在同一个种子上
实现了两个固定目标的公共因果规则。没有对每个种子的确定性障碍分别选目标或
误差，再把不相容的选择平均。尤其 (10.12) 不要求共同切口事件可测，也没有
来源上的随机分布、不可数积分、极小极大交换或伴随的可测选择。
由任意两个不同参数即得 $\inf_s v_\Pi(s)\le1/2$。

为达到下界，取 $\Omega=\{0,1\}$、$\mu(0)=\mu(1)=1/2$、
$\mathcal F=2^\Omega$。协议在两个种子下都先取得初读，执行 $d-2$ 次 $N$，
逐次立即取得并计费报告。此公共前缀的行为与种子完全无关。
令 $y_i$ 表示报告除以 $\varepsilon$ 后的数值。
种子零在切口 $q=d-2$ 执行 $L_0N^{d-1}$，取得全部 $d$ 个新坐标；
种子一再执行一次 $N$，在切口 $q=d-1$ 执行 $L_0N^{d-2}$，取得 $d-1$
个新坐标。后一分支的末坐标只使用先前的同一份 $y_{d-1}$。
两个分支都在且仅在单位实际相容系统 $\mathsf D_{d,q}$ 无严格正解时输出二，
否则停止而不作秩断言。各分支的收费分别是

$$
 (d-1)+d=2d-1,\qquad d+(d-1)=2d-1.
\tag{10.13}
$$

验证完整域路径可靠性时，任取普通秩一的 $T\in\mathcal M_d$。
它的每个矩阵项严格正，所以可取 $c_h=T_{h0}$、$\ell_j=T_{0j}/T_{00}$，
得到严格正分解 $T=c\ell$，不论原来的表示使用一项还是两项。
对归一化来源 $T/\varepsilon=(c/\varepsilon)\ell$，令
$C=\sum_{h=0}^{d-1-q}(c_h/\varepsilon)>0$、
$x=(c/\varepsilon)/C$、$v=C\ell^{\mathsf T}$。
III 引理 10.1 的真值公式给出该来源全部纯前缀及新坐标，
所以同一个严格正 $(x,v)$ 满足实际报告系统 $\mathsf D_{d,q}$ 的所有闭一
约束。$q=d-1$ 时 $x_0=1$ 和 $A_{d-1}^{(d)}=v_{d-1}$ 保持共享报告。
这直接核对 III 引理 13.2 的相容性方向，故任何种子的协议在任何秩一来源上
都不输出二。完整域的普通秩只有一或二，两个固定种子都路径可靠。

再固定一个实际目标 $R_{\varepsilon,s}$ 和一个任意
$\mathcal E\in\mathscr E(R_{\varepsilon,s})$。由于两个种子在前 $d-1$ 份报告前
每次选相同动作，且误差只读固定来源和公共历史，对报告数归纳可知两个种子
取得完全相同的前缀，特别是同一个 $y_{d-2}$。

若 $y_{d-2}\le\tau_s$，(8.4) 第一行排除切口 $d-2$ 的
$\mathsf C_{d,d-2}$；种子零必成功。
若 $y_{d-2}>\tau_s$，(8.4) 第二行排除切口 $d-1$ 的
$\mathsf C_{d,d-1}$，而且对随后每个允许的 $y_{d-1}$ 都成立；种子一必成功。
确切地，任意允许实际补全若有 $\mathsf D$ 解，则对每个 $j\in B_{d,q}$，

$$
 |v_j-b_j^{(q)}(R_s^{(d)})|
 \le |v_j-w_j|+|w_j-b_j^{(q)}(R_s^{(d)})|\le2,
\tag{10.14}
$$

给出同一组因子的 $\mathsf C$ 解，与所选安全谓词矛盾。
旧末报告仍由原来的 $A_{d-1}^{(d)}$ 约束提供，既不换成另一份报告，也不
把实际误差界一放宽为二。这正是 III 定义 14.3 与引理 14.4 的安全方向；
阈值等号属于种子零的安全情形，两个闭误差端点均被保留。
两个种子首次可能被公共动作区分是在 $y_{d-2}$ 已报告之后。
此后误差即使从动作识别出切口，安全谓词仍排除该分支的每份允许补全。
所以任意固定公共因果规则至少让两个等概率种子之一成功，
$\mu Z_\Pi(R_{\varepsilon,s},\mathcal E)\ge1/2$。
这对每个 $s$ 与每个规则成立，给出 (10.9) 的下界和达到协议。
全部概率事件在有限种子空间上自动可测，即使误差函数完全没有 Borel 正则性。
事实上此协议每个 $s$ 都有 $v_\Pi(s)=1/2$：下界已证，对任一别的 $t$ 使用
(10.10) 即得反向界。

最后，固定任意每个 $G_\Pi(s)$ 均可测的协议。
定理 9.1 的 (9.2) 直接说明不同参数的 $G_\Pi(s)$ 两两不相交；这里引用其
确定性全误差结论，不把它用于 (10.12) 的操作上界。
对每个正整数 $m$，概率至少 $1/m$ 的这种互不相交事件至多有 $m$ 个，
所以正概率的 $G_\Pi(s)$ 至多可数。
参数区间不可数，故 $\inf_s\mu G_\Pi(s)=0$。
有限种子达到协议也满足这些事件的可测性，协议类非空，得到 (10.11)。
其全称误差事件的零最坏值与 (10.9) 的正操作值具有不同量词，二者同时成立。∎

本定理的概率可加性、有限等概率混合和互不相交正测度集的可数性只是通用工具。
Yao，[*Probabilistic computations: Toward a unified measure of complexity*](https://doi.org/10.1109/SFCS.1977.24)，
提供随机复杂度中分布比较的一般背景；这里不调用其极小极大交换。
Ben-David--Borodin--Karp--Tardos--Wigderson，
[*On the power of randomization in on-line algorithms*](https://doi.org/10.1007/BF01294260)，
研究自适应对手下随机在线算法与确定性算法的比较；其竞争分析结论不供应
(10.7)--(10.8) 的严格正伴随和闭误差共享表。
van den Bos--Vaandrager，
[*State Identification for Labeled Transition Systems with Inputs and Outputs*，Theorem 6.1](https://arxiv.org/html/1907.11034v2)，
供应状态不相容性与自适应区分的相关背景，其 suspension automaton 假设不等于
这里的连续正秩一／秩二域。引理 10.2 将 (8.5) 的完整库同时实现为固定目标、
种子盲的因果规则，定理 10.3 再将 (8.4) 的两套安全谓词用于同一私有协议；
这两个模型内推论为 repo-derived，不据此宣称外部原创。

(10.9)--(10.11) 均以定义 10.1 的路径可靠性和未公开种子为前提。
它们只计算显式族的成功概率，不断言完整 $\mathcal M_d$ 上存在正的统一成功率，
也不计算仅要求几乎处处可靠或种子公开后的最优值。
数学协议使用严格正实变量系统的可行性判定，不附加有效实数、位复杂度或物理
实现主张；原多项式漂移初根问题不属于此概率模型。

## 追加锚（本行以下为增补区）
