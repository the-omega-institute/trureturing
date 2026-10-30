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

本节把 IV 第 22--24 节的五维构造再推进一个明确的维度。这里只证明一个
显式六维族的逐来源费用和一个带十一报告预算的有限预选不相容性。它不把
第 22.6 节的条件递归当作本节证明，也不声称任意维数、原根问题、在线选择器
或 Lean 形式化已经解决。

### 定义 6.1（六维合同）

令

$$
\mathcal M_6=\left\{\sum_{a=1}^{m}c_a\ell_a:
m\in\{1,2\},\ c_a\in\mathbb R_{>0}^{6},\
\ell_a\in\mathbb R_{>0}^{1\times6}\right\}.
$$

仍只有一条不可复制、不可复位的轨迹；允许的原子为

$$
Ne_j=e_{j+1}\quad(j<5),\qquad Ne_5=0,qquad
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

在首次 $L_0$ 前已有 $q$ 次 $N$ 时，共同来源系统
$\mathsf C_q(R,u)$ 使用 III 定义 14.3 的 $k=6$ 特例：

$$
A_i(x,v)=\sum_{h=0}^{5-i}x_hv_{h+i},\qquad
\sum_{h=0}^{5-q}x_h=1,
$$

所有 $x_h,v_j$ 严格为正，旧报告满足
$|A_i-u_i|\le1$，新报告满足
$|v_j-b_j^{(q)}(R)|\le2$。当 $q=5$ 时 $v_5=A_5$ 与已经取得的纯
$N$ 报告共享，不再收费，故 $j=5$ 不属于新的报告坐标集合。

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
B=10000,qquad K_6=10^{12},qquad
\mu_s=10000-1011-\lambda_s(3-s),
$$

$$
r_s^{(6)}=(B,1000,c_s,3-s,10,1),qquad
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
C_s=(1,0,\lambda_s,1,\mu_s,\nu_s)^{\mathsf T},qquad
e=(0,1,0,0,0,0)^{\mathsf T},qquad \alpha=\frac1{20000}.
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

末端在完整的 $\mathsf C_4$ 或 $\mathsf C_5$ 上检查；无正解时输出秩二，
有正解时停止而不作秩断言。

**证明。** 任意严格正秩一来源在其允许历史上给出共同来源系统的严格正解，
所以末端无解才输出秩二在完整环境域上可靠。两条分支都执行十个原子，初读计入
后共有十一份报告。

只需证明 $T_s$ 的相应末端系统无解。先注意

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
1-s\le v_3,\qquad 8\le v_4\le12,qquad 0<v_5=A_5\le3.
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
u_s=\tau_s+\frac1{16},qquad
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
$s\in[0,1/2]$ 都成立。式 (24.7) 中的 $u$ 可取当前纯 $N$ 前缀的第四坐标；在
$17\le u\le69/4$ 上，同一公式给出
$$
\frac{19}{32}\le x_2
=\frac{16-(3-s)-\frac34(u-\frac32)}2
\le\frac{15}{16}<1,
$$
并由 $70<c_s<80$ 得 $0<x_3<15$，且仍有 $A_4=2$。
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
A'_i=A_{i-1}\quad(i\ge1).
\tag{6.9}
$$

因此旧误差约束逐项移位，新首坐标误差为零，且新归一化
$\sum_{h=0}^{5-q}x'_h=1$ 保持。IV 引理 22.4 的显示公式、IV (24.4)
以及 IV (24.7)
的固定 q=4 公式及其界，逐项代入
(6.8) 的移位组合，给出

$$
x_0\beta_q+\sum_{h=1}^{4}x_hv_{h-1}<10^8
$$

对 $q=1,\ldots,5$ 的全部所需旧伴随。这里使用的是移位组合本身的界；不把
$x_h$ 与 $v_j$ 的独立粗界相乘。故 (6.8) 的分子大于
$10^{12}-10^8>0$，从而 $x'_5>0$。

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

**证明。** 上界由命题 6.3 对每个参数分别给出。下界取 $s<t$，选
$\tau_s<u<\tau_t$，并用共同纯 $N$ 前缀

$$
(K_6,10000,100,16,u,2),
$$

它同时属于两个单位误差盒。III 定理 14.2 的有限规范化只保留实际首个
$L_0$ 切口，不增加报告；设该切口前有 $q$ 次 $N$。若 $q\ge6$，则
$N^6=0$，III 引理 10.3 的纯 $N$ 正秩一回放在此后给出永久零尾，
所以一个十一报告内成功的全域可靠成员不可能在这种切口成功。因此 $q\le5$。
若 $q\le2$，引理 6.4 的对应早切口伴随（可取参数 $s$）覆盖十一报告内的全部可见坐标；若
$q=3$，取参数 $s$ 的旧 $q=2$ 伴随。若 $q=4$，取参数 $s$
的旧 $q=3$ 伴随，因为 $u>\tau_s$；此时
$0<u-\tau_s<\tau_t-\tau_s\le1/8$，所以 (24.4) 中的
$h=(u-\tau_s)/25$ 仍在其严格正性区间内。若 $q=5$，取参数 $t$ 的旧 $q=4$
提升伴随，并使用上面 $17\le u\le69/4$ 的固定公式范围。在每一种情形，中点补全给出同一有限历史，迫使
该协议在一个严格正秩一伴随上作出与目标相同的成功输出，违反完整域可靠性。
因此一个成员不能覆盖两个参数；有限覆盖至少 $|F|$ 个成员，结合上界得等号。
当 $F=\varnothing$ 时两边均为零；以下不相容性论证针对非空 $F$。

上面的不相容性先在单位容限写出。对任意 $\varepsilon>0$，同时把
$T_s,T_t$、所用固定秩一伴随、全部真实值、报告中点和阈值乘以
$\varepsilon$。映射 $R\mapsto\varepsilon R$ 是 $\mathcal M_6$ 的保秩双射，且
$\operatorname{tr}(A\varepsilon R)=\varepsilon\operatorname{tr}(AR)$；因此单位历史逐项变成
闭 $\varepsilon$ 历史，旧误差和中点误差分别由 $1$、$2$ 变成
$\varepsilon$、$2\varepsilon$。这既把命题 6.3 的逐来源上界缩放到
$\varepsilon$，也把同一成员覆盖两个参数的假设反向缩放为单位容限的矛盾，故
(6.11) 对所有 $\varepsilon>0$ 成立。

这里的结论专门带有“十一报告预算”限制；不把它升级为无预算的在线选择器或
任意维数的覆盖定理。所有桥梁均为本节显式移位、正性和有限报告表；第 22.6 节
的条件递归没有被用来供应本节结论。∎

### 约定 6.7（范围与验证状态）

本节新增的是六维显式族 $T_s$、其严格正两项分解、六维上界、十报告下界和
十一报告预算下的有限预选不相容性。它不声称 $k\ge7$ 的递归、不声称原根
完整目标、不提供未知来源在线选择器，也不宣称 Lean 编译或外部原创性。误差仍为
任意相关的闭区间误差，来源仍为一项或两项严格正外积之和；非负闭包、随机协议、
有效实数判定和有限位复杂度均不在结论内。

## 追加锚（本行以下为增补区）
