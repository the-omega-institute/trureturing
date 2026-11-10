# FIB 合法边调和负载：有限可见上下文的事件重置非达到

## 1. 原实际律与取得后的上下文支撑

**定义 1.1（实际有限上下文）。** 保持[更新分离卷][R] 定义 1.1、式（1.1）的完整平稳 no11 域、原外部风险 $d(P)$ 及普适最优值 $c_\star$。设 $P$ 的占据锚在两个方向均无界，$\iota=P(X_0=1)>0$。有限非空集 $C$ 上的锚标记由固定严格左、严格右可见半线函数恢复；同一实际标记律记为 $J$。在实际 Palm 律 $Q=J(\,\cdot\mid X_0=1)$ 下写

$$
T_0=0,\qquad G_k=T_{k+1}-T_k\ge2,\qquad C_k=C_{T_k},\qquad
0<\mathbb E_QG_0<\infty.
\tag{1.1}
$$

给定任意映射 $\tau_g:C\to C$，$g\ge2$，要求

$$
C_{k+1}=\tau_{G_k}(C_k)\quad Q\text{-几乎处处},\qquad k\in\mathbb Z.
\tag{1.2}
$$

不预设映射的单射性、半群律或空间时钟结构。置

$$
\nu_c=Q(C_0=c),\quad C_+=\{c:\nu_c>0\},\quad
f_c(g)=Q(G_0=g\mid C_0=c)\quad(c\in C_+).
\tag{1.3}
$$

零质量标签不承担条件律要求。此处不假设事件间隙具有 Markov 性，也不假设隐藏表示。

**命题 1.2（取得后全部活动行的显式正性）。** 对定义 1.1 的同一实际律，若 $d(P)=c_\star$，则

$$
f_c(g)\ge \frac{2^{-(g+1)}}3>0
\quad(c\in C_+,\ g\ge2).
\tag{1.4}
$$

证明。记 $\mathcal E_i=\sigma(X_j:j\ne i)$、$F_i=\{X_{i-1}=X_{i+1}=0\}$。[普适后验卷][U] 定理 3.1 对取得者给出完整外部事件比较：若 $A\in\mathcal E_i$，则

$$
P(A,X_i=0)\ge\tfrac12P(A);
\qquad
\tfrac13P(A,X_i=0)\le P(A,X_i=1)\le P(A,X_i=0)
\quad(A\subseteq F_i).
\tag{1.5}
$$

固定 $c\in C_+$、$g\ge2$，令

$$
A_c=\{X_0=1,\ D^-((X_{-j})_{j\ge1})=c\}.
\tag{1.6}
$$

此事件只依赖坐标 $\le0$，且 $P(A_c)=\iota\nu_c>0$。依次在 $1,\ldots,g+1$ 使用（1.5）的第一项，得到

$$
P(A_c,X_1=\cdots=X_{g+1}=0)
\ge2^{-(g+1)}P(A_c).
\tag{1.7}
$$

在位置 $g$ 的外部事件中保留其余这些零及 $A_c$，两个邻位均为零，故第二项给出

$$
P\bigl(A_c,X_g=1,\ X_j=0\ (1\le j\le g+1,\ j\ne g)\bigr)
\ge \frac{2^{-(g+1)}}3P(A_c).
\tag{1.8}
$$

该事件包含于 $\{X_0=1,C_0=c,G_0=g\}$；严格左解码使用的原坐标没有改变。除以 $\iota\nu_c$ 即得（1.4）。整个论证使用完整可测事件的质量比较，没有在单个无限配置上指定正质量或重新选择后验版本。$\square$

## 2. 常返分量的实际条件化与循环结构

**命题 2.1（取得者的有限上下文循环分解）。** 在定义 1.1 下若 $d(P)=c_\star$，则 $C_+$ 分解为有限个互不相交的集合 $D$。每个 $D$ 对所有 $\tau_g$ 封闭，存在其上的单循环置换 $U_D$，满足

$$
\tau_g|_D=U_D^g\quad(g\ge2).
\tag{2.1}
$$

所有实际锚的标记属于同一个 $D$。记这一事件为 $E_D$，则每个 $P(E_D)>0$，实际条件律 $J_D=J(\,\cdot\mid E_D)$ 及 $P_D=P(\,\cdot\mid E_D)$ 均平稳，并且

$$
d(P)=\sum_D P(E_D)d(P_D),\qquad d(P_D)=c_\star.
\tag{2.2}
$$

两个严格半线解码器、原距离和各行 $f_c$ 都在相应条件分量上保持。

证明。[更新分离卷][R] 式（35.2）的前后锚分割给出同一实际 $Q$ 的事件平稳性，不需间隙 Markov 性。因此

$$
K(c,b)=\sum_{g\ge2}f_c(g)\mathbf1_{\{\tau_g(c)=b\}},\qquad
\nu K=\nu.
\tag{2.3}
$$

这里 $K$ 只是实际一步条件质量组成的有限随机矩阵；未断言标记过程为 Markov 链。命题 1.2 与平稳性说明 $\tau_g(C_+)\subseteq C_+$。在 $C_+$ 上 $\nu$ 处处正，有限随机矩阵的平稳质量不落在暂态状态，故 $C_+$ 是闭常返不可约类 $D$ 的不交并。每个 $D$ 对 $K$ 封闭，而全部 $f_c(g)>0$，所以它对每个 $\tau_g$ 也封闭。沿实际锚转移，类标签几乎处处不变。

类标签可从任意给定位置左侧的最近占据锚及该锚的严格左解码恢复。因此对每个整数 $i$，

$$
E_D\in\sigma(X_j:j<i)\subseteq\mathcal E_i
\quad\text{模 }P\text{-零集}.
\tag{2.4}
$$

锚在左侧无界保证这一恢复总能进行；可数确定位置的解码恒等式先取共同满测集，再选最近锚。原位置零所属的类与移位无关，所以 $E_D$ 位点移位不变，$J_D,P_D$ 平稳。令 $q_i=\mathbb E_P[X_i\mid\mathcal E_i]$。由于（2.4），对任意 $A\in\mathcal E_i$，

$$
\int_A X_i\,dP_D
=\frac{\int_{A\cap E_D}X_i\,dP}{P(E_D)}
=\int_Aq_i\,dP_D.
\tag{2.5}
$$

故原 $q_i$ 仍为 $P_D$ 的完整外部后验，其后验带也保持。按实际分量对 $(X_0-q_0)^2$ 积分得到（2.2）的第一式；每个平稳 $P_D$ 的风险不超过 $c_\star$，因此取得反设使每个正权重项均取得。

每个类的位点质量为正：$P(E_D)\ge P(E_D,X_0=1)=\iota\nu(D)>0$。其实际 Palm 律恰为

$$
Q_D=J_D(\,\cdot\mid X_0=1)
=Q(\,\cdot\mid C_0\in D).
\tag{2.6}
$$

所以在 $c\in D$ 上的条件间隙行仍为 $f_c$，且

$$
\mathbb E_{Q_D}G_0\le\frac{\mathbb E_QG_0}{\nu(D)}<\infty.
\tag{2.7}
$$

原两个解码函数在条件分量上仍恢复同一实际标记。将其在条件分量上的值域限制为 $D$，对其余输入任取一个固定的 $D$ 值，得到[可见相位卷][V] 假设 55.2 的实际双侧标记；严格解码比该供应在锚上包含已知中心位的写法更强。实际一步矩阵为 $K|_D$，不可约；命题 1.2 给全正间隙行，（2.5）给原后验带。于是直接使用该卷定理 57.1，得到

$$
\tau_{l+r}|_D=(\tau_r\circ\tau_l)|_D,\qquad
U_D=(\tau_3|_D)(\tau_2|_D)^{-1},\qquad
\tau_g|_D=U_D^g.
\tag{2.8}
$$

这里置换性和逆映射的存在均由该供应定理推出，并非原假设。该定理还说明 $U_D$ 只有一个轨道，故可标为 $\mathbb Z/|D|\mathbb Z$ 上的加一。$\square$

## 3. 任意有限上下文事件重置的严格非达到

**定理 3.1（有限上下文事件重置排除）。** 取[更新分离卷][R] 定义 8.1 的任意整数 $N\ge1$ 与完整非负参数 $\theta=(\lambda,M_0,M_1)\in\Theta_N$，使用其式（8.2）的实际隐藏、可见联合路径律及可见边缘 $P=P_\theta$。设此律满足定义 1.1 的全部实际锚、有限均值、两个严格半线解码器和任意确定映射条件。若存在隐藏状态上的概率行 $r_c$，使对每个 $k\in\mathbb Z$，

$$
\mathcal L_Q\!\left(H_{T_k+1}\mid\mathcal H_k\right)=r_{C_k},\qquad
\mathcal H_k=\sigma(C_j:j\le k;\ G_j:j<k),
\tag{3.1}
$$

则

$$
d(P)<c_\star.
\tag{3.2}
$$

不要求循环空间时钟、可逆转移、半群律、正标签质量或正间隙条目；零质量标签不承担（3.1）的条件律要求。

证明。反设 $d(P)=c_\star$。先沿[更新分离卷][R] 式（35.7）–（35.9）核对原重置的实际未来路径。锚零以前的全部实际锚、间隙和标记都由可见过去确定，严格左解码因此给出

$$
\mathcal H_0\subseteq\sigma(X_i:i\le0)
\quad\text{模 }Q\text{-零集}.
\tag{3.3}
$$

原路径律（8.2）先给出条件于发出锚一后的隐藏状态及完整隐藏、可见过去的未来乘积律。再按（3.3）、条件期望塔性质和（3.1）混合，得到

$$
Q(X_1\cdots X_\ell=w\mid\mathcal H_0)=r_{C_0}M_w\mathbf1,
\qquad
f_c(g)=r_cM_0^{g-1}M_1\mathbf1\quad(c\in C_+).
\tag{3.4}
$$

实际 Palm 事件平稳性将同一规则传至每个整数事件编号，不把负编号锚当作停止时刻。因此

$$
Q(G_k=g,C_{k+1}=b\mid\mathcal H_k)
=f_{C_k}(g)\mathbf1_{\{b=\tau_g(C_k)\}}.
\tag{3.5}
$$

下一锚几乎必然存在及原有限 Palm 均值保证每个活动行归一化且一阶矩有限。由 no11 与（3.4），$r_cM_1\mathbf1=0$；故取

$$
\alpha_c=r_cM_0,\qquad T=M_0,\qquad b=M_1\mathbf1,
\tag{3.6}
$$

便有非负有限吸收表示

$$
f_c(k+2)=\alpha_cT^kb,\qquad
\alpha_c\mathbf1=1,\qquad T\mathbf1+b=\mathbf1\quad(k\ge0).
\tag{3.7}
$$

不要求整个 $M_0$ 瞬态，也未从标量 no11 条件推出未经裁剪矩阵的平方零。

命题 2.1 把同一实际律分成正权重的循环条件分量 $J_D,P_D,Q_D$，且每个 $d(P_D)=c_\star$。在 Palm 历史中，类事件就是 $\{C_0\in D\}$，已经属于 $\mathcal H_0$，所以（3.5）的完整历史行在条件化后保持。将 $D$ 标为循环相位集后，（2.1）给出原空间距离推进；命题 1.2 给全部行严格正，（2.7）保留有限均值，两个解码器及（3.7）的同一实际行也保留。因此条件分量满足[更新分离卷][R] 定义 11.1、12.1 的全部接口。此处直接使用实际条件分量及其有限相型行，不需要另拟隐藏链或替换原 Palm 权重。

若 $|D|=1$，完整历史规则给出 iid 距离律，使用该卷定理 4.3；若 $|D|=2,3$，使用定理 16.2、17.2；若 $|D|=4$，使用推论 18.2 及定理 19.1、20.1；若 $|D|=5,6,7$，分别使用定理 21.2、30.5、31.1；若 $|D|\ge8$，使用定理 32.1。每个分支均给 $d(P_D)<c_\star$，与实际分量取得矛盾。结合普适上界得到（3.2）。$\square$

**引文与边界 3.2（综合推导的归属）。** 本卷为 `repo-derived` 的实际支撑与条件分量连接。完整外部事件比较复用[普适后验卷][U] 定理 3.1，拆分相容和有限变换分类直接复用[可见相位卷][V] 推论 56.2、定理 57.1；循环有限相型非达到及重置路径接口按[更新分离卷][R] 的原范围消费。命题 1.2、2.1 不要求事件重置或有限隐藏表示；定理 3.1 在其上消费实际重置与有限吸收表示。只有在取得反设下才得到循环分类；一般双侧可见的事件重置律不必满足半群律，相关事件循环反例见[可见相位卷][V] 第 58 节。

外部方法背景为 Marzen–Crutchfield，*Informational and Causal Architecture of Discrete-Time Renewal Processes*，[arXiv:1408.6876v2](https://arxiv.org/html/1408.6876v2)，§II.1、§V、附录 A 的更新与有限隐藏／无限预测记忆边界，以及 Dawid–Lauritzen–Parry，*Proper Local Scoring Rules on Discrete Sample Spaces*，[arXiv:1104.2224v2](https://arxiv.org/html/1104.2224v2)，§4.2、例 4.4、式（14）的条件 Brier 机制。这些文献不供应本卷原 $d,c_\star$ 的非达到结论；其严格正全乘积域也不替代本卷合法、强制及零质量纤维。新增连接不作独立文献新颖性断言。

一般非重置有限隐藏取得问题仍为[更新分离卷][R] 开放问题 9.2。本卷不给所有有限隐藏域的统一正风险差距，不给解码窗口或计算资源上界，也不判定任意有限均值的非相型上下文核是否达到。

[R]: FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md
[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[V]: FIB_LEGAL_EDGE_LOAD_VISIBLE_TAIL_PHASE_RIGIDITY_AND_WINDOW_LIMITS.md

## 追加锚（本行以下为增补区）


## 4. Past-visible resets and the actual future-measure comparison

**Definition 4.1 (Past-visible finite-context class).** Let $N\ge1$ and let $\theta=(\lambda,M_0,M_1)$ range over the entire domain

$$
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\quad
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\quad
\lambda M_1^2\mathbf1=0.
\tag{4.1}
$$

Use the actual stationary joint law of [R, Definition 8.1][R], with hidden states $H_i$ immediately before emission at $i$:

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}).
\tag{4.2}
$$

Write $P=P_\theta$ for its visible marginal. Structural zeros, zero stationary hidden masses, reducibility, periodicity and redundant states are allowed. The last condition in (4.1) is scalar; it does not impose $M_1^2=0$ on the whole matrix. Require $\iota=P(X_0=1)>0$, occupied anchors unbounded in both spatial directions, and a finite nonempty context set $C$. At every occupied anchor $t$, let

$$
C_t=D^-((X_{t-j})_{j\ge1})
\tag{4.3}
$$

for one fixed measurable strict-left decoder. These marks extend (4.2) to a stationary marked law $J$. In its actual Palm law $Q=J(\,\cdot\mid X_0=1)$ enumerate anchors by $T_0=0$, $T_k<T_{k+1}$, and set $G_k=T_{k+1}-T_k\ge2$, $C_k=C_{T_k}$. Require

$$
0<\mu=\mathbb E_QG_0<\infty,\qquad
C_{k+1}=\tau_{G_k}(C_k),\qquad
\mathcal L_Q(H_{T_k+1}\mid\mathcal H_k)=r_{C_k},
\quad
\mathcal H_k=\sigma(C_j:j\le k;G_j:j<k),
\tag{4.4}
$$

for every $k\in\mathbb Z$, where $\tau_g:C\to C$ are arbitrary maps and $r_c$ are probability rows on the original hidden state set. Conditions on a context of zero Palm mass are void. No strict-right context decoder is assumed. This class is defined by (4.1)–(4.4), separately from Definition 1.1.

The objective remains the original one: for legal words $B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\}$, let $\Gamma_n$ have all legal Hamming-one edges with open endpoints, $h(s,t)=st/(s+t)$ for $s+t>0$ and $h(0,0)=0$, and

$$
\Phi_n(\pi)=\sum_{\{u,v\}\in E(\Gamma_n)}h(\pi_u,\pi_v),\qquad
\kappa_n=\max_{\pi\in\mathcal P(B_n)}\Phi_n(\pi),\qquad
c_\star=\lim_n\kappa_n/n.
\tag{4.5}
$$

For the entire exterior $\mathcal E_i=\sigma(X_j:j\ne i)$ choose a Borel version $q_0=\mathbb E_P[X_0\mid\mathcal E_0]\in[0,1]$, and put $q_i=q_0\circ T^i$ for $(Tx)_j=x_{j+1}$. The actual risk is

$$
d(P)=\mathbb E_P(X_0-q_0)^2\le c_\star.
\tag{4.6}
$$

These are [R, §1][R] and [U, §1][U]'s same open-path objective and full-exterior risk, including zero masses and forced fibers.

**Proposition 4.2 (Actual rows and recurrent conditional laws).** Suppose Definition 4.1 holds and $d(P)=c_\star$. Put $\nu_c=Q(C_0=c)$ and $C_+=\{c:\nu_c>0\}$. Every $c\in C_+$ has a normalized finite-mean row

$$
\begin{aligned}
f_c(g)&=Q(G_0=g\mid C_0=c)=r_cM_0^{g-1}M_1\mathbf1
\ge 2^{-(g+1)}/3\quad(g\ge2),\\
Q(G_k=g,C_{k+1}=b\mid\mathcal H_k)
&=f_{C_k}(g)\mathbf1_{\{b=\tau_g(C_k)\}}.
\end{aligned}
\tag{4.7}
$$

In particular, with $\alpha_c=r_cM_0$, $T_0=M_0$ and $b_0=M_1\mathbf1$,

$$
f_c(k+2)=\alpha_cT_0^kb_0,\qquad
\alpha_c\mathbf1=1,\qquad T_0\mathbf1+b_0=\mathbf1.
\tag{4.8}
$$

The positive contexts split into closed irreducible classes $D$ of

$$
K(c,b)=\sum_{g\ge2}f_c(g)\mathbf1_{\{b=\tau_g(c)\}},\qquad\nu K=\nu.
\tag{4.9}
$$

Each class is closed under every $\tau_g$. Its label is spatially invariant and belongs to every strict-left half-line and every exterior field. Conditioning on a class preserves (4.7), (4.8), the original posterior versions and attainment.

Proof. At a Palm anchor, past gaps recover every visible coordinate strictly to its left: their cumulative sums enumerate all preceding occupied sites. Conversely the strict-left decoder recovers every past mark from those coordinates. Thus $\mathcal H_0$ and the visible past at the known anchor agree modulo actual Palm null sets. The path Markov property of (4.2), followed by conditional expectation using (4.4), gives the conditional future cylinders $r_{C_0}M_w\mathbf1$. This proves (4.7) at zero; Palm event stationarity, obtained by the anchor-counting identity [R, (35.2)][R], transports it to all integer event indices. No negative-index stopping-time assertion is needed. Almost-sure next-anchor existence gives normalization. Since $\nu_c>0$ and $\mathbb E_QG_0<\infty$, each row mean is finite. The proof of Proposition 1.2 uses only (4.3) and the attained exterior comparison [U, Theorem 3.1][U], so its lower bound applies here. No11 gives $r_cM_1\mathbf1=0$, hence (4.8).

Event stationarity gives (4.9). A stationary finite stochastic matrix gives zero mass to transient states; positivity of $\nu$ on $C_+$ and of every $f_c(g)$ proves the asserted closed-class decomposition. The class label is constant along anchors. It can be read from an anchor arbitrarily far to the left, so its event $E_D$ belongs to every exterior $\mathcal E_i$ and is invariant under site shifts. The actual conditional laws are stationary and their Palm laws are exactly $Q(\,\cdot\mid C_0\in D)$. Moreover $P(E_D)\ge\iota\nu(D)>0$ and $\mathbb E_{Q(\cdot\mid D)}G_0\le\mu/\nu(D)$. Conditional expectation on an $\mathcal E_i$-measurable component shows that the same $q_i$ is its posterior. Therefore

$$
d(P)=\sum_D P(E_D)d(P(\,\cdot\mid E_D)),
\tag{4.10}
$$

and the upper bound $c_\star$ for each summand forces attainment in each positive component. The class event already belongs to $\mathcal H_k$, so the actual reset and full-history rule also survive conditioning. $\square$

**Proposition 4.3 (Comparison of entire future measures).** Fix one component $D$ of Proposition 4.2 and use its conditional law. Let $F_c$ be the law on $\{2,3,\ldots\}^{\mathbb N_0}$ of the entire future gap sequence starting at a context-$c$ anchor. For $c\in D$ and $l,r\ge2$, put

$$
M=f_c(l+r),\quad B=f_c(l)f_{\tau_l(c)}(r),\quad
 a=\tau_{l+r}(c),\quad b=\tau_r(\tau_l(c)).
$$

As measures on the entire future after the right exterior anchor,

$$
\frac M3F_a\ \le\ B F_b\ \le\ M F_a.
\tag{4.11}
$$

Proof. Specify the nearest exterior anchors at $-l,r$, the strict-left context $c$ at $-l$, and a measurable future-gap event $E$ after $r$. Conditional independence of the full future from the full past given $c$ follows by iterating (4.7) and a monotone-class argument. The center-zero and center-one external subprobability measures, including any full-left-past test, factor respectively as

$$
\iota_D\nu^D_c M\,\kappa_c^-\otimes F_a,
\qquad
\iota_D\nu^D_c B\,\kappa_c^-\otimes F_b.
\tag{4.12}
$$

Here $\kappa_c^-$ is the actual conditional left-past channel and $\iota_D,\nu^D$ are the actual conditional intensity and Palm row. Apply the exterior mass comparison (1.5) to these external tests and cancel the positive common scalar and left channel. This proves (4.11) for every measurable $E$. It gives mutual absolute continuity, not equality, of $F_a,F_b$. $\square$

## 5. The spatial absolute-continuity phase and finite synchronization

**Proposition 5.1 (Predictive quotient and labelled-graph phase).** In a fixed component of Proposition 4.2, first identify contexts having equal entire future laws. The resulting finite state set $S$ has distinct laws $F_s$, well-defined rows $f_s$ and maps $\tau_g$. Next identify states when $F_s$ and $F_t$ are mutually absolutely continuous. On this second quotient the labelled maps are

$$
\bar\tau_g=U^g\quad(g\ge2)
\tag{5.1}
$$

for one cyclic permutation $U$. Thus its classes can be labelled $\mathbb Z/m\mathbb Z$ so that an edge with gap $g$ adds $g$. This quotient is a strongly connected labelled graph; it need not carry a common probability row within a phase. No lumpability of the original $K$ is asserted.

Proof. Equality of future laws implies equality of their first-gap probabilities. Conditioning on any first gap $g$, whose mass is positive, then gives equality of the successor future laws. This constructs the first quotient and its rows. The same conditioning argument shows that mutual absolute continuity passes to successors, so it defines the second quotient's maps. Equation (4.11) gives

$$
\bar\tau_{l+r}=\bar\tau_r\bar\tau_l\quad(l,r\ge2).
\tag{5.2}
$$

The quotient labelled graph is strongly connected because the original component is irreducible and every label has positive probability at every state. Relation (5.2) makes its maps commute. For each $g$, the nonempty image of $\bar\tau_g$ is invariant under all labelled maps. Strong connectivity forces this image to be the whole quotient, so every map is a permutation. Set $A_2=\bar\tau_2$, $A_3=\bar\tau_3$. Then $A_3^2=A_2^3$ and $U=A_3A_2^{-1}$ has $U^2=A_2$, $U^3=A_3$. Relation (5.2), starting with $2,3$, gives (5.1) for every $g\ge2$. Strong connectivity now makes $U$ a single cycle. This is the finite-map algebra of [V, Theorem 57.1][V], applied to labelled maps rather than to representative phase rows. $\square$

**Proposition 5.2 (Two half-line decoders for phase and invariant component).** Write $A_t$ for the absolute-continuity phase at an occupied anchor $t$. For any site $i$ define

$$
S_i=A_t+i-t\pmod m
\tag{5.3}
$$

using a preceding anchor $t<i$. This is independent of the chosen anchor and has both strict-left and strict-right visible decoders. Every invariant component label $E_D$ also belongs to both strict half-lines. These assertions concern only phase and component, not the original contexts or the predictive states inside a phase.

Proof. Formula (5.1) gives anchor independence and $S_{i+1}=S_i+1$. The preceding anchor and its strict-left mark make $S_i$ strictly past measurable. On the stationary component let $\zeta=e^{2\pi\mathrm i/m}$ and $Z=e^{2\pi\mathrm i S_0/m}$. Then

$$
Z\circ T^n=\zeta^n Z.
\tag{5.4}
$$

Finite-past conditional expectations $Z_n=\mathbb E[Z\mid X_{-n},\ldots,X_{-1}]$ tend to $Z$ in $L^2$. The functions $\zeta^{-(n+1)}Z_n\circ T^{n+1}$ depend only on $X_1,\ldots,X_n$ and their distances from $Z$ in $L^2$ equal $\|Z_n-Z\|_2$ by stationarity and (5.4). The future-measurable subspace of $L^2$ is closed; hence $Z$, and therefore $S_0$, has a Borel strict-future version. Countably many shifts give the decoder at every actual anchor. For an invariant component indicator $Z=\mathbf1_{E_D}$ the identical argument uses eigenvalue $1$ under the unconditioned law. Thus component labels are future measurable as well as past measurable. This eigenvalue-$1$ case is also valid when $m=1$. $\square$

**Proposition 5.3 (A common finite word merges each phase).** For a finite normalized deterministic predictive automaton with distinct future laws and strictly positive rows on the countable gap alphabet, there is a nonempty finite word $w$ that merges every pair in each mutual-absolute-continuity class:

$$
\tau_w(s)=\tau_w(t)\quad\text{whenever }F_s\sim F_t.
\tag{5.5}
$$

Here $\tau_v=\tau_{g_k}\cdots\tau_{g_1}$ and

$$
L_s(v)=\prod_{j=1}^k f_{\tau_{g_{j-1}}\cdots\tau_{g_1}s}(g_j)
\quad(v=(g_1,\ldots,g_k)),\qquad L_s(\varnothing)=1.
\tag{5.6}
$$

The conditional probability of $w$ from any state is at least $\varepsilon=\min_s L_s(w)>0$. For disjoint trials of its $k$ gaps, failure in the first $n$ trials has probability at most $(1-\varepsilon)^n$ after any actual event history.

Proof. On the finite ordered unequal-pair set define the substochastic matrix

$$
W_{(s,t),(u,v)}=
\sum_{\substack{g\ge2:\tau_gs=u,\ \tau_gt=v\\u\ne v}}
\sqrt{f_s(g)f_t(g)}.
\tag{5.7}
$$

Cauchy–Schwarz bounds every row sum by $1$. If $\rho(W)=1$, a finite substochastic matrix has a nonempty closed stochastic irreducible class: otherwise every final communicating class loses mass, and every state reaches such a loss, forcing a power to have row sums below $1$. At a row of a closed stochastic class equality in Cauchy–Schwarz gives $f_s(g)=f_t(g)$ for all $g$. Positivity and closure ensure that every positive-symbol successor pair remains unequal in that class. Induction gives $L_s(v)=L_t(v)$ for every finite word $v$, hence $F_s=F_t$, contrary to predictive minimality. Therefore $\rho(W)<1$.

If a pair has no merging word, every word from it stays unequal, and the Hellinger affinity of its length-$n$ prefix laws is exactly $(W^n\mathbf1)_{(s,t)}$, tending to zero. To identify the full-measure limit, dominate both laws by $\eta=(F_s+F_t)/2$. The densities of their restrictions to the prefix fields are the conditional expectations $p_n=\mathbb E_\eta[dF_s/d\eta\mid\mathcal F_n]$, $q_n=\mathbb E_\eta[dF_t/d\eta\mid\mathcal F_n]$. They are bounded by $2$ and converge almost surely to the full densities because the prefix fields generate the gap space. Dominated convergence gives

$$
\lim_n\int\sqrt{p_nq_n}\,d\eta
=\int\sqrt{(dF_s/d\eta)(dF_t/d\eta)}\,d\eta.
\tag{5.8}
$$

Zero affinity means singularity. Consequently an equivalent pair must have a merging word.

Start with an empty common word. Whenever an original same-class pair still has unequal images, those images still have equivalent future laws; append one of their merging words. Equal images cannot separate under later symbols, so each step eliminates at least one of finitely many original pairs. This terminates with (5.5). If all classes were already singletons, any one-symbol word suffices. Countable alphabet size causes no zero-word problem: every selected finite word has a finite product of positive probabilities, and there are only finitely many initial states. The conditional failure bound follows by iterating the uniform lower bound $\varepsilon$ on successive trials.

The pair-graph synchronization method is related to Travers–Crutchfield, *Exact Synchronization for Finite-State Sources*, [§II.4, Definition 5; §III.1, Theorem 1; §IV.1, Definitions 11–12 and Theorem 3](https://arxiv.org/html/1008.4182). Their stated alphabet is finite. The argument (5.7)–(5.8) supplies the countable-gap, within-phase version needed here, without invoking a finite-alphabet theorem outside its hypotheses. $\square$

**Proposition 5.4 (Entire-exterior posterior from a finite future prefix).** Under the attainment hypothesis of Proposition 4.2, consider a free exterior cell $F_0=\{X_{-1}=X_1=0\}$ with nearest anchors $-l,r$ and left context $c$. With $M,B,a,b$ as in Proposition 4.3, any finite observed future gap prefix $v$ after $r$ containing an intact copy of $w$ gives the original posterior

$$
q_0=\frac{B L_b(v)}{M L_a(v)+B L_b(v)}.
\tag{5.9}
$$

On the forced complement $F_0^c$, $q_0=0$.

Proof. The competing states $a,b$ have the same absolute-continuity phase by (4.11). Before the copy of $w$ their successors remain in the same phase, and after it their minimal predictive states coincide, say at $u$. On the prefix cylinder the full future laws factor as $L_a(v)F_u$ and $L_b(v)F_u$. In (4.12) both the common full-left-past channel and this common entire-future tail cancel, proving (5.9) by disintegration on the entire exterior field. This is not a quotient of point masses at infinite configurations. The geometric trial bound makes these prefix cylinders cover almost every future. Countably many prefixes, contexts, distances and spatial shifts admit a common conull formula domain. No right decoder for $c$, $a$ or $b$ is used. $\square$

## 6. Physical guard tails and both original erasure fields

**Proposition 6.1 (Exponential physical waiting lengths).** For each fixed component in Proposition 4.2, gaps and the physical waiting length to a completed copy of $w$ have a positive exponential moment at an anchor, uniformly over its finitely many predictive states. There are constants $C<\infty$, $\beta>0$, depending on the producer and component, such that the probability that a stationary spatial interval of length $j$ contains no complete guard is at most $Ce^{-\beta j}$. The same bound holds for negative spatial intervals.

Proof. In (4.8), telescoping gives

$$
\alpha_cT_0^n\mathbf1
=1-\sum_{k=0}^{n-1}\alpha_cT_0^kb_0\longrightarrow0.
\tag{6.1}
$$

Restrict $T_0$ to the finite survival states reachable from $\alpha_c$. A reachable closed class with no absorption would give positive eternal-survival probability, contradicting (6.1). The restricted substochastic matrix therefore has spectral radius below $1$, so its powers decay exponentially. This proves $\sum_g e^{tg}f_c(g)<\infty$ for some $t>0$. The finite row family permits one common positive $t$; the predictive quotient uses the same rows. Neither full-matrix transience nor a reverse-time transition rule is needed.

Let $k$ be the number of gaps in $w$, $Y=G_0+\cdots+G_{k-1}$ the physical trial length, and $S_k$ its final predictive state. Define

$$
D_t(s,u)=\mathbb E_s[e^{tY}\mathbf1_{\{(G_0,\ldots,G_{k-1})\ne w,\ S_k=u\}}],
\quad
h_t(s)=\mathbb E_s[e^{tY}\mathbf1_{\{(G_0,\ldots,G_{k-1})=w\}}].
\tag{6.2}
$$

Iterated conditioning and the finite row moments make these finite and continuous at $t=0$ for small $t\ge0$. Since $\|D_0\|_\infty\le1-\varepsilon$, choose $t>0$ with $\|D_t\|_\infty<1$. The exponential moment of the physical length through the first successful disjoint trial is the convergent geometric sum

$$
\sum_{n\ge0}D_t^nh_t.
\tag{6.3}
$$

A guard at a stationary origin is reached by first reaching the next anchor and then using (6.3). Palm inversion [R, (11.7)][R] weights a gap of length $g$ by $g/\mu$ and chooses its spatial offset. Its forward residual thus has an exponential moment at any smaller positive exponent, because $g e^{t'g}\le C_t e^{tg}$ when $0<t'<t$. The bound on (6.3) is uniform in the state reached there; integrating it gives an exponential stationary waiting tail. Completion within a window supplies a whole guard inside it. Translation invariance sends the event of no complete guard in a positive interval to that for a negative interval of equal length. This uses stationarity, not a reverse Markov assumption. $\square$

**Proposition 6.2 (Exact retained-field estimators and root summability).** Under Definition 4.1 and $d(P)=c_\star$, use exactly

$$
\begin{aligned}
\mathcal L_j&=\sigma(X_{-j},\ldots,X_{-1},X_1,X_2,\ldots),\\
\mathcal R_j&=\sigma(\ldots,X_{-2},X_{-1},X_1,\ldots,X_j),\\
p_j^L&=\mathbb E_P[X_0\mid\mathcal L_j],\quad
p_j^R=\mathbb E_P[X_0\mid\mathcal R_j],\\
e_L(j)&=\mathbb E_P(q_0-p_j^L)^2,\quad
e_R(j)=\mathbb E_P(q_0-p_j^R)^2\qquad(j\ge0).
\end{aligned}
\tag{6.4}
$$

There are producer-dependent $K<\infty$, $\gamma>0$ such that

$$
e_L(j)+e_R(j)\le Ke^{-\gamma j},\qquad
A_P=\sum_{j\ge0}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr)<\infty.
\tag{6.5}
$$

Proof. Work first in a component. For $j\ge1$ both fields retain the two nearest neighbors, so a forced center has the exactly known posterior zero. On a free exterior, define the $\mathcal L_j$ good event by the existence of a complete guard with both endpoints in $[-j,-1]$. Choose its first such occurrence by a fixed spatial ordering. The entire retained future determines the component and spatial phase by Proposition 5.2; transport that phase to the guard's starting anchor. Proposition 5.3 makes its ending predictive state the common image of all states in that phase. All subsequent observed past gaps then transport this state to the nearest left anchor. The entire retained future supplies the nearest right anchor and a prefix containing another guard. Formula (5.9), now using the recovered left predictive state, is $\mathcal L_j$ measurable and equals $q_0$ on this event. Define $\widehat q_j^L$ by this formula on the good free event and by zero elsewhere, including forced configurations. Every selection uses countably many measurable word tests.

For $\mathcal R_j$, the entire retained past directly gives the left context, component and phase. Its good free event is the existence of a complete guard with endpoints in $[1,j]$. Take the future prefix from the nearest right anchor through this guard. All of it is retained, so (5.9) defines an $\mathcal R_j$-measurable $\widehat q_j^R=q_0$ there; again set the estimator to zero off the good free event. A guard starting at the nearest right anchor is allowed. Thus both estimators are defined on their whole retained fields, with values in $[0,1]$.

Because these fields are subfields of $\mathcal E_0$, the tower property gives $p_j^L=\mathbb E[q_0\mid\mathcal L_j]$ and its right analogue. Projection optimality and boundedness give

$$
e_L(j)\le\mathbb E(q_0-\widehat q_j^L)^2
\le P(\text{no complete guard in }[-j,-1]),
\qquad
e_R(j)\le P(\text{no complete guard in }[1,j]).
\tag{6.6}
$$

Proposition 6.1 bounds both terms exponentially. Enlarging the constant includes $j=0$, where each field still retains its entire opposite half-line and each defect is at most $1$.

For the original finite mixture, Proposition 5.2 with eigenvalue $1$ places every $E_D$ in both retained fields, including at $j=0$. Consequently each conditional projection restricts to its component projection. With $\omega_D=P(E_D)$ the mixing identities are exactly

$$
e_L(j)=\sum_D\omega_D e_{L,D}(j),\qquad
 e_R(j)=\sum_D\omega_D e_{R,D}(j).
\tag{6.7}
$$

There are finitely many positive components. Taking the least of their positive rates and summing their constants proves the first assertion in (6.5). Finally,

$$
A_P\le2\sqrt K\sum_{j\ge0}e^{-\gamma j/2}
=\frac{2\sqrt K}{1-e^{-\gamma/2}}<\infty.
\tag{6.8}
$$

This is the original one-sided root sum, not a two-sided window error or a hidden-state recovery error. $\square$

## 7. Same-law strong zero, inclusive guarded identities and a restricted exclusion

**Proposition 7.1 (Saturated original-loss identities).** Under Definition 4.1 and $d(P)=c_\star$, put $\ell_i(x)=(x_i-q_i(x))^2$. There is one shift-invariant conull domain $\Omega$ saturated under all legal finite changes on which

$$
\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z))=0
\tag{7.1}
$$

absolutely for every $x,z\in\Omega$ differing at finitely many sites. In a fixed component, preserve a complete guard $w$ before the changed interval, a second complete guard after it, and a third after the second. If $A$ is the first guard's starting anchor and $B$ the second guard's ending anchor, then

$$
\sum_{i=A}^{B}\left[(x_i-q_i(x))^2-(z_i-q_i(z))^2\right]=0.
\tag{7.2}
$$

Both boundary anchors are included. Each posterior in (7.2) is expressible using finitely many row entries and the predictive state at an unchanged preceding anchor. These are necessary rational-function identities for all compatible finite guarded patterns and legal fillings having the same physical endpoint length.

Proof. Proposition 6.2 proves $A_P<\infty$ for the same actual $P$. Hence [Strong-zero, Definition 1.4 and Theorem 1.5](FIB_LEGAL_EDGE_LOAD_ATTAINMENT_STRONG_ZERO_EQUIVALENCE_AND_FINITE_OPTIMIZER_COMPARISON.md) applies with the unchanged original versions $q_i$ and losses $\ell_i$. It supplies (7.1) on a saturated conull set.

For completeness, one can choose this domain to carry all the preceding formulas simultaneously. Intersect the structural and formula conull sets over every integer shift, then with the strong-zero domain and with every preimage under a legal replacement of a finite word on a finite integer interval. There are countably many such maps and their finite compositions. They are nonsingular: the attained band gives positive conditional mass to every legal single-site alternative, and deleting to zero then inserting a compatible word connects every legal finite fiber; iterated exterior comparisons preserve null sets. Thus the intersection is still conull and is saturated. Past-decoded component and phase are unchanged by a finite modification, since they can be recovered arbitrarily far to its left. This defines one $\Omega$ carrying original posterior formulas at both $x$ and every modified $z$.

Before $A$, the first intact guard lies wholly after a scored center. It merges the two competing-center predictive paths, so (5.9) cancels all future information beyond that guard. The intervening unchanged coordinates and original left state are the same for $x,z$; hence $q_i(x)=q_i(z)$ for $i<A$. After the changed interval, equal physical displacement gives equal phases at the start of the second guard, regardless of the possibly different predictive states there. That guard merges their actual states. For $i>B$ the same state at $B$ and the unchanged later coordinates give the same left predictive channel and the same entire future, hence equal posteriors. Since the visible bits also agree outside the changed interval, every loss difference outside $[A,B]$ vanishes. This proves (7.2) from (7.1).

For a scored center in $[A,B]$, including an occupied boundary anchor, deleting that center may break either of the first two guards. The third guard is intact in both center completions and lies strictly after the scored interval. Starting from an unchanged anchor preceding $A$, propagate the two finite completions through that third guard and use (5.9); on a forced fiber use zero. This computes each original $q_i$ by finite positive likelihoods, even at $A$ and $B$, and proves that the summands are rational functions of finitely many $f_s(g)$ values.

Finally choose any positive starting state and any compatible guarded finite word. Every required finite gap word has positive probability by (4.7); compatible equal-length fillings have mutually absolutely continuous future channels after the second guard, where their states agree. The preceding starting state and phase have positive actual mass. The scalar expression in (7.2) is constant on this finite pattern with that starting state, independently of the more distant exterior. Its almost-sure zero value therefore forces the same scalar identity for every such pattern and filling. This argument asserts neither unconditional locality on all legal configurations nor a Gibbs specification. $\square$

**Proposition 7.2 (Singleton absolute-continuity classes).** If every absolute-continuity class in each recurrent minimal predictive component of Definition 4.1 is a singleton, then $d(P)<c_\star$.

Proof. Suppose equality held. In each positive component the phase of Proposition 5.1 is now the minimal predictive state itself. Proposition 5.2 supplies both strict half-line decoders for this state; Proposition 4.2 supplies its actual normalized positive finite-mean rows, full-history rule and finite absorption representations. Equal predictive laws have equal rows, so choosing any representative of a predictive state gives the same row and a representation (4.8). Thus the same actual conditional law satisfies [R, Definitions 11.1 and 12.1][R], with actual Palm weights and spatial transport $s\mapsto s+g$. The all-cycle exclusions used in Theorem 3.1 apply: [R, Theorem 4.3][R] for one phase; Theorems 16.2, 17.2 for two and three; Corollary 18.2 and Theorems 19.1, 20.1 for four; Theorems 21.2, 30.5, 31.1 for five through seven; and Theorem 32.1 for at least eight. Every positive conditional law would have risk strictly below $c_\star$, contradicting (4.10). The restriction to singleton classes is essential to this application. $\square$

## 8. A six-state diagnostic with equivalent unequal futures

**Proposition 8.1 (An actual past-visible producer).** In the state order $(q_0,q_1,e_0,e_1,o_0,o_1)$ define

$$
M_0=\begin{pmatrix}
0&0&1&0&0&0\\
0&0&0&1&0&0\\
0&0&0&0&297/400&0\\
0&0&0&0&0&303/400\\
0&0&25/33&0&0&0\\
0&0&0&75/101&0&0
\end{pmatrix},\qquad
M_1=\begin{pmatrix}
0&0&0&0&0&0\\
0&0&0&0&0&0\\
103/400&0&0&0&0&0\\
97/400&0&0&0&0&0\\
0&8/33&0&0&0&0\\
0&26/101&0&0&0&0
\end{pmatrix},
\tag{8.1}
$$

and

$$
\lambda=\left(\frac{679}{5912},\frac{63}{739},\frac{194}{739},
\frac{144}{739},\frac{28809}{147800},\frac{2727}{18475}\right).
\tag{8.2}
$$

These parameters belong to $\Theta_6$. Their actual stationary law satisfies Definition 4.1 with contexts $c\in\{0,1\}$ equal to previous-gap parity,

$$
\tau_g(c)=g\pmod2,\qquad r_c=\delta_{q_c}.
\tag{8.3}
$$

Its actual gap rows, Palm weights, row means and intensity are

$$
\begin{gathered}
f_c(g)=\frac14\left(\frac34\right)^{g-2}A_{c,g\bmod2},\qquad
(A_{c,p})_{c,p=0,1}=
\begin{pmatrix}103/100&24/25\\97/100&26/25\end{pmatrix},\\
\nu=(97,72)/169,\qquad
\sum_g gf_0(g)=872/175,\qquad\sum_g gf_1(g)=878/175,\\
\mu=5912/1183,\qquad\iota=1183/5912.
\end{gathered}
\tag{8.4}
$$

Proof. Every displayed entry is nonnegative and each row of $M_0+M_1$ sums to one. Direct substitution gives $\lambda\mathbf1=1$ and $\lambda(M_0+M_1)=\lambda$. Every $1$ edge ends at a $q$ state, whose $M_1$ row is zero, so $M_1^2=0$. The positive-edge graph is strongly connected: each $q_c$ reaches $e_c$, each $e_c$ reaches $q_0$ and $o_c$, and each $o_c$ reaches $e_c$ and $q_1$. Its finite stationary chain is recurrent and ergodic; positive-frequency $1$ edges therefore yield anchors unbounded in both directions.

After an anchor the state is a $q_c$ and the next symbol is forced zero. Starting from $q_c$, a gap of even length ends by $e_c\to q_0$ and a gap of odd length ends by $o_c\to q_1$. The two-step zero-survival products are

$$
\frac{297}{400}\frac{25}{33}
=\frac{303}{400}\frac{75}{101}=\frac9{16}.
\tag{8.5}
$$

The gap-$2$ masses are $103/400,97/400$; the gap-$3$ masses are $9/50,39/200$. Equation (8.5) then proves every row formula in (8.4) by increments of two. The post-anchor state is exactly $q_{g\bmod2}$, not a hidden mixture depending on earlier history. At a current anchor the nearest strict-left anchor is at relative position $-g$, so its distance $g$ gives the previous-gap parity by a fixed strict-left visible function. The actual post-anchor hidden state is consequently $q_c$ for this visible $c$, so conditioning on the entire marked event history gives exactly the reset (8.3).

Summing the even-gap probabilities gives the actual context transition matrix

$$
K=\begin{pmatrix}103/175&72/175\\97/175&78/175\end{pmatrix},
\tag{8.6}
$$

whose stationary row is $(97,72)/169$. Geometric sums and their first derivatives at $9/16$ give normalization and the means in (8.4). Weighting those means by $\nu$ gives $\mu$; alternatively the actual intensity $\lambda M_1\mathbf1$ equals $1183/5912=1/\mu$. Thus all Palm quantities belong to this same stationary producer. $\square$

**Proposition 8.2 (Full-exterior band without predictive splitting, and a strict risk bound).** For Proposition 8.1, the laws $F_0,F_1$ are distinct and mutually absolutely continuous, with

$$
f_0(2)-f_1(2)=3/200,\qquad
\frac{dF_0}{dF_1}=\frac{f_0(G_0)}{f_1(G_0)}>0.
\tag{8.7}
$$

There is no almost-sure strict-right decoder of the original context. Nevertheless the entire-exterior posterior lies strictly in $(1/4,1/2)$ on every positive free exterior cell and is zero on the forced cells. The split successor future laws differ whenever the left split distance $l$ is odd. The law is strictly nonattaining:

$$
d(P)\le\frac{50349663}{363522968}<\frac17<\frac{1800}{12559}\le c_\star.
\tag{8.8}
$$

Proof. After the first future gap $g$, both starting contexts have successor $g\bmod2$. Factoring on that first-gap cylinder proves the full density ratio (8.7); distinctness follows at $g=2$. Since both actual Palm context masses are positive, a right decoder would separate two equivalent future measures into disjoint probability-one sets, which is impossible.

For a free center with nearest anchors $-l,r$, left context $c$, and next future gap $h$ after $r$, the center-one and center-zero paths reach possibly different contexts at $r$, but coincide after $h$. Their full-exterior odds are therefore exactly

$$
R=\frac{f_c(l)f_{l\bmod2}(r)f_{r\bmod2}(h)}
{f_c(l+r)f_{(l+r)\bmod2}(h)},\qquad q_0=\frac{R}{1+R}.
\tag{8.9}
$$

The full-left channel is common, and the entire tail after $h$ cancels, as a measure factorization. All $A$ entries lie in $[24/25,26/25]$. The geometric factors in (8.9) leave $4/9$, so

$$
\frac{1536}{4225}
=\frac49\frac{(24/25)^3}{(26/25)^2}
\le R\le
\frac49\frac{(26/25)^3}{(24/25)^2}
=\frac{2197}{4050}.
\tag{8.10}
$$

The lower bound exceeds $1/3$ and the upper bound is below $1$, proving the strict band. If $l$ is odd, $\tau_{l+r}(c)\ne\tau_r\tau_l(c)$ and (8.7) shows their future laws differ. Thus the band does not force predictive split equality.

For a simple independent risk bound, let $F_0=\{X_{-1}=X_1=0\}$. The event $\{X_{-1}=X_1=1\}$ is an anchor followed by gap $2$, so inclusion-exclusion gives

$$
Q(G_0=2)=679/2704,\qquad
P(F_0)=1-2\iota+\iota Q(G_0=2)=61489/94592.
\tag{8.11}
$$

Because $X_0=1$ implies $F_0$, the exterior-measurable estimator

$$
\widehat q=\frac{\iota}{P(F_0)}\mathbf1_{F_0}
=\frac{18928}{61489}\mathbf1_{F_0}
\tag{8.12}
$$

has squared risk

$$
\mathbb E(X_0-\widehat q)^2
=\iota-\frac{\iota^2}{P(F_0)}
=\frac{50349663}{363522968}<1/7.
\tag{8.13}
$$

The posterior minimizes squared risk on the full exterior, and [R, §1][R] supplies $c_\star\ge1800/12559>1/7$. This proves (8.8). The example is therefore a counterexample to the band-to-predictive-split implication, not an attaining law. $\square$

## 9. The remaining finite-family exclusion

**Definition 9.1 (Unresolved equality and exclusion).** For the past-visible class of Definition 4.1, exact attainment implies (4.11), the finite spatial absolute-continuity quotient, within-phase synchronization, (6.5), and all the necessary guarded original-loss identities (7.2). A remaining question is whether any actual finite phase-type deterministic predictive family can satisfy all those identities with risk $c_\star$, or whether every such family is excluded. In particular, under exact attainment the equality

$$
F_{\tau_{l+r}(c)}=F_{\tau_r\tau_l(c)}
\quad(c\in C_+,\ l,r\ge2)
\tag{9.1}
$$

is still unproved here. Mutual absolute continuity and a common merging word permit unequal first-gap rows within one phase; Proposition 8.2 rules out deducing (9.1) from the posterior band alone. Proposition 7.2 excludes only the singleton-class branch. The reductions do not establish nonattainment for the general past-visible class, root summability for arbitrary finite-hidden laws, uniform rates or risk gaps, or finite visible order.

## 追加锚（本行以下为增补区）

## 10. Actual reset recursion and finite all-distance tests

**Proposition 10.1 (Actual reset recursion).** Work in the setting of Definition 4.1. Write

$$
Z=M_0,\qquad E=M_1,\qquad A_g=Z^{g-1}E\quad(g\ge2).
\tag{10.1}
$$

At a Palm anchor let
$\mathcal H_0=\sigma(C_j:j\le0;G_j:j<0)$. The strict-left decoder and the past gaps recover one another modulo the actual Palm null sets, so $\mathcal H_0$ is the marked strict visible past at the known anchor. If $C_0=c$ and $f_c(g)>0$, then on $\{G_0=g\}$ the next anchor is at $T_1=g$, and the original joint path law gives

$$
Q\!\left(H_{T_1+1}\in\cdot\mid\mathcal H_0,G_0=g,C_0=c\right)
=\frac{r_cA_g}{f_c(g)}.
\tag{10.2}
$$

The reset condition at index $1$ identifies this conditional row with $r_{\tau_g(c)}$. Hence

$$
\boxed{\quad r_cA_g=f_c(g)r_{\tau_g(c)}
\quad(c\in C_+,\ g\ge2,\ f_c(g)>0).\quad}
\tag{10.3}
$$

Proof. The path product after the anchor is $r_cM_u$ for a finite future word $u$, and summing its terminal hidden state gives $r_cM_u\mathbf1$. For the word consisting of $g-1$ zeros followed by one this scalar is $r_cA_g\mathbf1=f_c(g)$. Conditioning the original product law on the marked past and on the positive event $G_0=g$ therefore gives (10.2), while $T_1=g$ and $C_1=\tau_g(C_0)$ are deterministic on that event. Palm event stationarity transports the same identity to every integer event index; no negative-index stopping-time argument is used. Under attainment, Proposition 4.2 gives $f_c(g)>0$ for every $c\in C_+$ and every $g\ge2$, so this positivity is a scalar gap-mass conclusion and does not assert entrywise positivity of $Z$, $E$, or any hidden row. Conditioning on a recurrent class preserves (10.3), because its event belongs to every marked history. $\square$

**Proposition 10.2 (Entire future laws and the finite all-distance tensor interface).** Work under Definition 4.1 with the attainment hypothesis $d(P)=c_\star$. Proposition 4.2 then makes every scalar gap mass positive and every successor of a positive context belong to $C_+$. Fix $c\in C_+$ and $l,r\ge2$, and set

$$
\begin{aligned}
&p=l-1,\qquad q=r-1,\qquad x=r_c,\\
&v=xZ^{p+q+1}E,\qquad u=xZ^pEZ^qE,\\
&M=v\mathbf1=f_c(l+r),\qquad
 B=u\mathbf1=f_c(l)f_{\tau_l(c)}(r),\\
&a=\tau_{l+r}(c),\qquad b=\tau_r(\tau_l(c)).
\end{aligned}
\tag{10.4}
$$

Let $F_{c_1}$ denote the law of the entire future gap sequence from a positive context $c_1$. The future anchors are unbounded almost surely under Definition 4.1, so on an actual conull set the infinite future bit string and its gap sequence determine one another. Consequently,

$$
F_{c_1}=F_{d_1}
\quad\Longleftrightarrow\quad
(r_{c_1}-r_{d_1})M_t\mathbf1=0
\quad\text{for every finite binary word }t.
\tag{10.5}
$$

Inside the present interface, use the already supplied observable-space stabilization from [the intrinsic null-kernel volume, Theorem 2.2](FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md): with

$$
\mathscr O_0=\operatorname{span}\{\mathbf1\},\qquad
\mathscr O_{k+1}=\mathscr O_k+Z\mathscr O_k+E\mathscr O_k,
\tag{10.6}
$$

one has $\mathscr O_k=\operatorname{span}\{M_t\mathbf1:|t|\le k\}$ and $\mathscr O_{N-1}=\mathscr O_\infty$. Thus (10.5) may be tested using only $|t|\le N-1$; this is cited support for the tensor interface, not a separate observable-span result.

Under attainment, Proposition 4.2 makes the scalar masses $M,B$ positive, and (10.3) gives $r_a=v/M$ and $r_b=u/B$. For $o\in\mathbb R^N$, put

$$
\mathcal A=Z\otimes Z,\qquad
\mathcal H=I\otimes E,\qquad R_c=x\otimes x,
$$

$$
 w_o=(ZE\mathbf1)\otimes(Eo)-(ZEo)\otimes(E\mathbf1)\in\mathbb R^{N^2}.
\tag{10.7}
$$

Because $M_t\mathbf1\in\mathbb R^N$, every terminal column below is the defined lift $w_{M_t\mathbf1}\in\mathbb R^{N^2}$; consequently each displayed tensor product is a scalar at the original $N$-state dimensions. Direct expansion gives

$$
R_c\mathcal A^p\mathcal H\mathcal A^q w_o
=(v\mathbf1)(uo)-(vo)(u\mathbf1)
=MB\,(r_b-r_a)o.
\tag{10.8}
$$

Therefore all split equalities

$$
F_{\tau_{l+r}(c)}=F_{\tau_r(\tau_l(c))}
\qquad(l,r\ge2)
\tag{10.9}
$$

hold if and only if

$$
R_c\mathcal A^p\mathcal H\mathcal A^q w_{M_t\mathbf1}=0
\quad\text{for all }p,q\ge1\text{ and all binary }|t|\le N-1.
\tag{10.10}
$$

For a $d$-dimensional real matrix, Cayley--Hamilton multiplied once by the matrix expresses every positive power in the span of the first $d$ positive powers. Applying this separately to the two powers of $\mathcal A$, with $d=N^2$, yields the finite original-matrix characterization

$$
\boxed{\quad
(10.9)\text{ for every }l,r\ge2
\Longleftrightarrow
R_c\mathcal A^p\mathcal H\mathcal A^q w_{M_t\mathbf1}=0
\quad\begin{matrix}
1\le p,q\le N^2,\\ |t|\le N-1.
\end{matrix}\quad}
\tag{10.11}
$$

Any basis of $\mathscr O_{N-1}$ may replace the finite family of word columns, provided each basis vector is passed through the same map $w_{\,\cdot\,}$. This is a finite algebraic characterization for the specified original representation, including singular matrices and structural zeros; it is not an algorithm for arbitrary exact-real input and does not assert that the tests vanish.

For the sharper rectangle, put

$$
\eta_o=(E\mathbf1)\otimes(Eo)-(Eo)\otimes(E\mathbf1),
\qquad \mathcal H'=E\otimes Z.
\tag{10.12}
$$

Then the same expansion, in the opposite tensor orientation, is

$$
R_c\mathcal A^p\mathcal H'\mathcal A^q\eta_o
=B(vo)-M(uo)=MB\,(r_a-r_b)o.
\tag{10.13}
$$

The exchange involution fixes $R_c$ and commutes with $\mathcal A$; $R_c\mathcal A^p$ lies in the symmetric dual space of dimension $N(N+1)/2$, while $\mathcal A^q\eta_o$ lies in the antisymmetric space of dimension $N(N-1)/2$. Cayley--Hamilton on these invariant spaces reduces the same zero set to

$$
1\le p\le\frac{N(N+1)}2,\qquad
1\le q\le\frac{N(N-1)}2,\qquad |t|\le N-1,
\tag{10.14}
$$

with the terminal column understood as $\eta_{M_t\mathbf1}$. When $N=1$, every $\eta_o$ is zero; the scalar no11 condition then forces $M_1=0$, hence $\iota=0$, so the standing hypothesis $\iota>0$ has no member at $N=1$. The orientation in (10.12), rather than the terminal column in (10.7), is the one for which the antisymmetry assertion is valid.

An optional gap-only version has the explicit finite domain

$$
0\le k\le N-1,\qquad g_1,\ldots,g_k\in\{2,3,\ldots,N+1\},
\tag{10.15}
$$

with terminal columns
$A_{g_1}\cdots A_{g_k}\mathbf1$ (the empty product is $\mathbf1$). Replacing the binary lifts in (10.11) and (10.14) by
$w_{A_{g_1}\cdots A_{g_k}\mathbf1}$ and $\eta_{A_{g_1}\cdots A_{g_k}\mathbf1}$, respectively, for all columns in (10.15), gives the same equality test: the positive powers $Z,Z^2,\ldots,Z^N$ span all positive powers, so these gap matrices span the same stabilized observable space. No conditional law at a zero-mass gap or successor is used in this optional formulation. $\square$

**Proposition 10.3 (Sufficient certificate and the unresolved implication).** For an actual producer in Definition 4.1, suppose that for every $c\in C_+$ all the finitely many expressions in (10.11) vanish (or, equivalently, the sharper rectangle (10.14) vanishes). Then

$$
 d(P)<c_\star.
\tag{10.16}
$$

Proof. Assume for contradiction that $d(P)=c_\star$. Proposition 4.2 supplies positive scalar gap masses and the rows used in Proposition 10.2, so the finite vanishing gives all split equalities. On each recurrent component $D$, first form the quotient

$$
S_D=D/\!\sim,\qquad s\sim t\ \Longleftrightarrow\ F_s=F_t,
\tag{10.17}
$$

of equality of entire future laws. This is the predictive-state carrier; it is formed before the mutual-absolute-continuity quotient or any synchronization argument. The successor maps descend to $S_D$, and the split equalities give
$\bar\tau_{l+r}=\bar\tau_r\bar\tau_l$ for $l,r\ge2$. The positive gap rows make each recurrent component of this finite labelled graph strongly connected. The elementary finite-map algebra on this quotient then makes every $\bar\tau_g$ a permutation and gives $\bar\tau_g=U^g$ for one cyclic permutation $U$.

Proposition 5.3 supplies a finite word merging any pair of predictive states in one mutual-absolute-continuity class. Its action on $S_D$ is a composition of the permutations just obtained, hence is injective. Such a pair must therefore have been the same element of $S_D$, so every mutual-absolute-continuity class of predictive states is a singleton. Proposition 7.2 now gives the contradiction. Thus (10.16) is a sufficient certificate for the actual producer.

The converse implication is deliberately absent: attainment has not been shown to force any expression in (10.11) or (10.14) to vanish. Nonvanishing supplies neither an attaining producer nor a positive lower bound for $c_\star-d(P)$. Without attainment, (10.3) is used only on positive gap events; null contexts and zero completion masses impose no conditional successor law. $\square$

## 11. Future-information deficit under the actual law

**Proposition 11.1 (Quantified split-information deficit).** In the actual-law setting of Proposition 4.3, let

$$
M=f_c(l+r),\qquad B=f_c(l)f_{\tau_l(c)}(r),
$$

and let $F_a,F_b$ be the two entire future gap measures there. For $M,B>0$ put $\rho=F_a+F_b$, choose densities $u=dF_a/d\rho$ and $v=dF_b/d\rho$, and define

$$
\Delta_{c,l,r}
=\frac{MB}{M+B}
-\int\frac{MBuv}{Mu+Bv}\,d\rho,
\tag{11.1}
$$

where the integrand is set to zero on $\{Mu+Bv=0\}$. Let

$$
\eta=\frac{MF_a+BF_b}{M+B},\qquad
p=\frac{Bv}{Mu+Bv},\qquad
\alpha=\frac{B}{M+B}.
\tag{11.2}
$$

Then $\eta$ is a probability measure, $\mathbb E_\eta p=\alpha$, and

$$
\begin{aligned}
\Delta_{c,l,r}
&=(M+B)\operatorname{Var}_\eta(p)\\
&=\frac{M^2B^2}{(M+B)^2}
\int\frac{(u-v)^2}{Mu+Bv}\,d\rho\ \ge0.
\end{aligned}
\tag{11.3}
$$

Proof. Since $d\eta=(Mu+Bv)d\rho/(M+B)$, direct substitution gives the integral term in (11.1) as $(M+B)\mathbb E_\eta[p(1-p)]$, while $(M+B)\alpha(1-\alpha)=MB/(M+B)$. Their difference is the variance in (11.3). This is the actual-measure form of the conditional Brier variance calculation in Dawid--Lauritzen--Parry, *Proper Local Scoring Rules on Discrete Sample Spaces*, §4.2, Example 4.4 and equation (14); the displayed derivation supplies the needed no11-domain identity directly. Equality holds exactly when $F_a=F_b$. The algebra in (11.1)--(11.4), including this equality case, applies to any two positive actual completion channels under Definition 4.1; it does not require the attained comparison (4.11).

Since $\int|u-v|\,d\rho=2\operatorname{TV}(F_a,F_b)$, weighted Cauchy--Schwarz gives

$$
\Delta_{c,l,r}
\ge\frac{4M^2B^2}{(M+B)^3}\operatorname{TV}(F_a,F_b)^2.
\tag{11.4}
$$

Under attainment, Proposition 4.3 gives $M/3\le B\le M$, and hence

$$
\frac{\Delta_{c,l,r}}{M+B}
\ge\frac9{64}\operatorname{TV}(F_a,F_b)^2.
\tag{11.5}
$$

If a binary word $t$ of length at most $N-1$ has

$$
\varepsilon_t=(r_a-r_b)M_t\mathbf1,
\tag{11.6}
$$

then its future cylinder gives $\operatorname{TV}(F_a,F_b)\ge|\varepsilon_t|$. Under the same attainment hypothesis as in (11.5), this yields

$$
\Delta_{c,l,r}\ge\frac9{64}(M+B)\varepsilon_t^2.
\tag{11.7}
$$

The optional gap-only finite domain is exactly the one in (10.15); its positive gap-word cylinders give the analogous bound. These are quantitative actual-law consequences and do not infer an upper bound on any auxiliary risk.

## 12. Exact erasure sum for an explicitly named auxiliary field

**Proposition 12.1 (Future-erasure identity).** Under Definition 4.1, define

$$
\mathcal G=\sigma(X_i:i<0)\vee\sigma(R_+),
\qquad R_+=\min\{j\ge1:X_j=1\},
\tag{12.1}
$$

and its actual-law Brier risk

$$
 d_{\mathcal G}=\mathbb E_P\left[(X_0-\mathbb E_P[X_0\mid\mathcal G])^2\right].
\tag{12.2}
$$

The explicit two-sided unbounded-anchor clause of Definition 4.1 gives $R_+<\infty$ almost surely; this scope is part of the definition and is not inferred merely from $\iota>0$ or $\mu<\infty$. For a positive context $c$ and $l,r\ge2$, put

$$
\begin{aligned}
M&=Q(G_0=l+r\mid C_0=c)=r_cA_{l+r}\mathbf1,\\
B&=Q(G_0=l,G_1=r\mid C_0=c)=r_cA_lA_r\mathbf1,\\
a&=\tau_{l+r}(c),\qquad b=\tau_r(\tau_l(c)).
\end{aligned}
\tag{12.3}
$$

These actual path masses are defined for every $c\in C_+$ and $l,r\ge2$ before any conditional law at a successor is selected. If $f_c(l)>0$, Palm event stationarity gives $\tau_l(c)\in C_+$, and the actual reset recursion gives $B=f_c(l)f_{\tau_l(c)}(r)$. If $f_c(l)=0$, nonnegativity gives $r_cA_l=0$ and hence $B=0$, without evaluating a row at $\tau_l(c)$. In particular, every positive two-gap path has the conditional-product expression. If $M,B>0$, then $a,b\in C_+$ and $\Delta_{c,l,r}$ is the quantity in (11.1), using its algebra for these two positive actual channels. If $M=0$ or $B=0$, define $\Delta_{c,l,r}=0$ and choose no conditional law at a null successor. Thus every $\Delta_{c,l,r}$ is defined without extending a conditional future law through a zero-mass channel.

Then the exact original-law identity is

$$
\boxed{\quad
 d_{\mathcal G}-d(P)
=\iota\sum_{c\in C_+}\nu_c
  \sum_{l,r\ge2}\Delta_{c,l,r}.
\quad}
\tag{12.4}
$$

Proof. The original path law (4.2) and actual reset (4.4) give the masses $r_cA_{l+r}\mathbf1$ and $r_cA_lA_r\mathbf1$ for the one-gap and two-gap completions, respectively. On positive completions, (10.3) identifies the terminal hidden rows as $r_a$ and $r_b$; a zero path mass is the zero subprobability channel. Partition the free cells by their nearest anchors $-l,r$ and strict-left context $c$. On a cell with $M,B>0$, the two completion channels after the right anchor, including every full-left-past test, factor as

$$
\iota\nu_c M\,\kappa_c^-\otimes F_a,
\qquad
\iota\nu_c B\,\kappa_c^-\otimes F_b,
\tag{12.5}
$$

where $\kappa_c^-$ is the actual left-past channel. The field $\mathcal G$ retains the common strict-left past and the location of the nearest right anchor, while it erases the future after that anchor. The common left factor cancels; the full-exterior conditional risk is the second term of (11.1), and the erased-future risk is its first term. If one channel has zero mass, both its contribution and the corresponding summand are zero, so no successor posterior is selected. Forced cells contribute zero to both risks because $\mathcal G$ retains the left neighbor and reveals whether the right neighbor is an anchor. Tonelli's theorem gives (12.4).

When $d(P)=c_\star$, Proposition 4.2 supplies the recurrent component decomposition and the same identity componentwise with the actual $\iota_D,\nu^D$; the mixture relation is

$$
P(E_D)\,\iota_D\nu^D_c=\iota\nu_c.
\tag{12.6}
$$

Since $\mathcal G\subseteq\mathcal E_0$, conditional-variance monotonicity gives $d_{\mathcal G}\ge d(P)$. The original universal comparison applies only to $d(P)$; (12.4) supplies no conclusion of the form $d_{\mathcal G}\le c_\star$ and does not settle the original attainment event. $\square$

## 13. Boundary of the finite interface

**Boundary 13.1 (Unresolved vanishing branch).** The finite identities (10.11), the sharper rectangle (10.14), and the nonnegative deficits (11.1)--(11.7) are exact interfaces for the unchanged original joint law, visible marginal, and Palm law. They provide a sufficient strict-risk certificate when they vanish and a quantitative measure of unequal split futures when they do not. No result in this append proves that an attaining original producer must make them vanish. The full nonnegative hidden domain, all positive contexts, every $l,r\ge2$, the original full-exterior posterior, and the original unresolved event remain the quantified objects.

## 追加锚（本行以下为增补区）

## 14. Periodic actual reset rows and prefix-preserving split tests

**Proposition 14.1 (Actual-law periodic reset normal form).** Assume Definition 4.1 and $d(P)=c_\star$, with the original $N$ hidden states, $Z=M_0$, $E=M_1$, and $C_+=\{c:Q(C_0=c)>0\}$. The finite nonempty set of probability rows

$$
\mathcal R_+=\{r_c:c\in C_+\}
\tag{14.1}
$$

carries well-defined maps

$$
\psi_g(x)=\frac{xZ^{g-1}E}{xZ^{g-1}E\mathbf1}
\quad(x\in\mathcal R_+,\ g\ge2).
\tag{14.2}
$$

Every denominator is positive, $\psi_g(r_c)=r_{\tau_g(c)}$, and each set $\{r_c:c\in D\}$ for a recurrent class $D$ of Proposition 4.2 is preserved by every $\psi_g$. There is one integer $L\ge1$, common to all positive contexts, such that

$$
r_{\tau_{g+L}(c)}=r_{\tau_g(c)}
\quad(c\in C_+,\ g\ge N+1),
\qquad
\psi_{g+L}=\psi_g\quad(g\ge N+1).
\tag{14.3}
$$

Put $B=N+L$ and define, for integers $g\ge2$,

$$
\operatorname{red}(g)=
\begin{cases}
g,&2\le g\le N,\\
N+1+((g-N-1)\bmod L),&g\ge N+1.
\end{cases}
\tag{14.4}
$$

Here the first case is empty if $N=1$. Then $2\le\operatorname{red}(g)\le B$ and $\psi_g=\psi_{\operatorname{red}(g)}$.

For $x,y\in\mathcal R_+$, let $x\sim y$ mean equality of their entire actual future visible laws from an anchor, equivalently of their entire future gap laws. By the interface of Proposition 10.2 this is precisely

$$
(x-y)M_t\mathbf1=0
\quad\text{for every binary word }t\text{ with }|t|\le N-1,
\tag{14.5}
$$

including the empty word. All split-future equalities

$$
\psi_{l+r}(x)\sim\psi_r(\psi_l(x))
\quad(x\in\mathcal R_+,\ l,r\ge2)
\tag{14.6}
$$

are equivalent to the cases $x\in\mathcal R_+$ and $2\le l,r\le B$. Thus every prefix gap $2,\ldots,N$ is retained, and the finite cases still evaluate the sum gaps $l+r$, up to $2B$.

Proof. Proposition 4.2 gives $f_c(g)=r_cZ^{g-1}E\mathbf1>0$ for every $c\in C_+$ and $g\ge2$. Proposition 10.1 gives

$$
r_cZ^{g-1}E=f_c(g)r_{\tau_g(c)}.
\tag{14.7}
$$

The positive contexts are closed under every $\tau_g$, and so are their recurrent classes. Consequently (14.2) maps $\mathcal R_+$ to itself and preserves the stated class row sets. If $r_c=r_d$, the numerator and denominator in (14.2) agree for these two representatives; hence $r_{\tau_g(c)}=r_{\tau_g(d)}$. This is the quotient by equality of reset rows, without requiring equality of context labels.

To obtain a simultaneous period, for $c\in C_+$ and $n\ge1$ write

$$
a_c(n)=r_cZ^nE\mathbf1>0,\qquad
s_c(n)=\frac{r_cZ^nE}{a_c(n)}\in\mathcal R_+.
\tag{14.8}
$$

For a fixed $u\in\mathcal R_+$ and a coordinate $1\le j\le N$, let $e_j$ be the $j$th coordinate column and consider

$$
h_{c,u,j}(n)=r_cZ^nE(e_j-u_j\mathbf1)\quad(n\ge0).
\tag{14.9}
$$

Cayley--Hamilton makes this a real linear recurrence sequence. Equivalently, its formal generating series is rational and regular at zero:

$$
\sum_{n\ge0}h_{c,u,j}(n)z^n
=r_c(I_N-zZ)^{-1}E(e_j-u_j\mathbf1).
\tag{14.10}
$$

The inverse here is the formal power-series inverse of $I_N-zZ$, whose constant term is $I_N$; it requires no inverse of $Z$. The classical Skolem--Mahler--Lech theorem, as stated in Jason P. Bell, *A generalised Skolem-Mahler-Lech theorem for affine varieties*, [arXiv:math/0501309v2, Theorem 1.1 and the rational-series form Theorem 2.1](https://arxiv.org/pdf/math/0501309v2), says that the zero set of each such sequence is a finite union of arithmetic progressions and a finite exceptional set. These statements apply over any characteristic-zero field, in particular $\mathbb R$; neither algebraic entries nor invertibility of $Z$ is needed.

Because $a_c(n)>0$, the set of $n\ge1$ on which $s_c(n)=u$ is exactly the intersection, over $j=1,\ldots,N$, of the zero sets in (14.9). It is therefore ultimately periodic. The distinct rows in $\mathcal R_+$ give a finite partition of the positive integers for each $c$. Taking a common multiple of all the finitely many eventual periods and a common threshold supplies integers $L\ge1$ and $K\ge1$ with

$$
s_c(n+L)=s_c(n)\quad(c\in C_+,\ n\ge K).
\tag{14.11}
$$

The threshold can be moved back to $N$ using only a stable row space. Set $W_k=\operatorname{row}(Z^k)$ for $k\ge0$. These spaces are nested and $W_kZ=W_{k+1}$. If $W_k=W_{k+1}$, right multiplication by $Z$ makes all later spaces equal. Starting with dimension $N$, strict dimension drops cannot continue beyond $N$ steps; hence

$$
V=W_N=W_{N+1},\qquad VZ=V.
\tag{14.12}
$$

Right multiplication $T(v)=vZ$ is a surjective endomorphism of $V$, and is therefore invertible on $V$. Also $V\ne\{0\}$, since otherwise $a_c(N)=0$. Put $d=\dim V\ge1$ and $S=T^L$. The constant coefficient $b_0$ of its characteristic polynomial

$$
\chi_S(t)=t^d+b_{d-1}t^{d-1}+\cdots+b_0
\tag{14.13}
$$

is nonzero because $S$ is invertible.

Fix $c\in C_+$ and $0\le a<L$. Equation (14.11) makes $s_c(N+a+kL)$ one fixed row $u\in\mathcal R_+$ for all sufficiently large integers $k$. Take $v=r_cZ^{N+a}\in V$ and the linear row-valued map $\phi_u(v')=v'E-(v'E\mathbf1)u$. Then

$$
y_k=\phi_u(S^k(v))
=\phi_u(r_cZ^{N+a+kL})\quad(k\ge0)
\tag{14.14}
$$

is eventually zero. Cayley--Hamilton on $V$ gives

$$
y_{k+d}+b_{d-1}y_{k+d-1}+\cdots+b_0y_k=0
\quad(k\ge0).
\tag{14.15}
$$

Since $b_0\ne0$, a zero tail propagates backward one nonnegative index at a time, down to $y_0=0$. Positivity in (14.8) then gives $s_c(N+a+kL)=u$ for every $k\ge0$. All residues $a$ and all positive contexts use the same $L$, so $s_c(n+L)=s_c(n)$ for every $n\ge N$. Substituting $n=g-1$ and using (14.7) proves (14.3). Only $S$ on $V$ was inverted in this reasoning; no negative exponent or exponent below $N$ was used.

Formula (14.4) keeps every gap through $N$ and selects one representative of each tail residue. Thus (14.3) gives equality of maps $\psi_g=\psi_{\operatorname{red}(g)}$ on all of $\mathcal R_+$. For $l,r\ge2$, put $l'=\operatorname{red}(l)$ and $r'=\operatorname{red}(r)$. Since intermediate rows remain in $\mathcal R_+$,

$$
\psi_r(\psi_l(x))=\psi_{r'}(\psi_{l'}(x)).
\tag{14.16}
$$

If both $l,r\le N$, then $l+r=l'+r'$. Otherwise both sums are at least $N+1$ and they are congruent modulo $L$. The tail periodicity therefore gives

$$
\psi_{l+r}(x)=\psi_{l'+r'}(x).
\tag{14.17}
$$

Equations (14.16)--(14.17) reduce each split test to one with $2\le l',r'\le B$; the reverse implication follows by inclusion of the finite cases. Equation (14.5) is exactly the original observable interface (10.5)--(10.6), applied to these actual reset rows; no additional observable-space assertion is required.

The period is existential: this argument supplies no effective period or computational resource bound. Periodicity is equality of reset rows, not of context labels, and does not assert a semigroup law for the maps $\psi_g$, or even (14.6). The periodic destination rows and unequal split futures in Proposition 8.2 show why periodicity alone cannot supply that implication; its producer is strictly nonattaining.

In particular, the implication from attainment to the vanishing in (10.11) or (10.14) remains unproved. Proposition 7.1 forces every compatible equal-length guarded original-score difference to vanish, but no construction here turns a nonzero tensor defect into two positive compatible guarded patterns and fillings with a nonzero such difference. Such a construction must keep the inclusive sum
$\sum_{i=A}^{B}[(x_i-q_i(x))^2-(z_i-q_i(z))^2]$, including both scored boundary anchors, and the third intact guard after $B$. Every $q_i$ must remain the full-exterior conditional mean under the same actual stationary visible marginal and its actual Palm law. Neither the periodic tail nor the nonnegative future-information deficit supplies the missing original-loss sign.

All statements retain the original nonnegative $N$-state presentation: structural zeros, zero stationary hidden masses, reducibility, periodicity and redundant states are allowed. No trimming, strict matrix positivity, irreducibility assumption, inverse of the original $Z$, or strict-right context decoder is used. Null contexts impose no requirement. $\square$

## 追加锚（本行以下为增补区）


## 15. Unequal split futures on an actual guarded Cartesian fibre

**Assumption 15.1 (Original law and predictive notation).** Retain Definition 4.1, including its entire nonnegative hidden domain, original stationary joint law, visible marginal $P$, actual Palm law $Q$, strict-left context decoder and arbitrary context maps. Assume $d(P)=c_\star$. Fix a positive recurrent class $D$ from Proposition 4.2 and work in its actual conditional law. Write $S_D$ for the minimal predictive quotient of $D$ from Proposition 5.1. A context subscript on $F$, $f$, $L$ or $\tau$ may be read in this quotient whenever only its future law is used. In particular equality of predictive states means equality of entire future laws, not equality of context labels or hidden rows. Let $w$ be the common within-phase synchronizing gap word of Proposition 5.3, and let $W=\sum_{g\text{ in }w}g$ be its physical length. All full-exterior posteriors and legal finite changes are taken on the common saturated domain of Proposition 7.1, or on its finite scalar extension to compatible positive patterns. No right decoder for original contexts or predictive states is assumed.

**Proposition 15.2 (Equal physical length with unequal guarded likelihood ratios).** Fix $c\in D$ and $l,r\ge2$, and put

$$
M=f_c(l+r),\quad B=f_c(l)f_{\tau_l(c)}(r),\quad
 a=\tau_{l+r}(c),\quad b=\tau_r(\tau_l(c)).
\tag{15.1}
$$

If $F_a\ne F_b$, there are two finite gap words $u,u'$ ending in $w$ with the same physical length and

$$
0<\frac{L_b(u)}{L_a(u)}\ne\frac{L_b(u')}{L_a(u')}<\infty.
\tag{15.2}
$$

This assertion applies also to the gaps preceding the periodic threshold in Proposition 14.1 and does not require choosing its period $L$.

Proof. The two initial predictive states have the same absolute-continuity phase by (4.11). Every word ending in $w$ therefore merges their terminal predictive states. Once this pair has merged, any suffix multiplies both likelihoods by the same positive number and preserves their ratio.

Suppose instead that all words ending in $w$ of each fixed physical length had a single ratio. Take any two such words $v,v'$ with physical lengths $h,h'$. Choose an integer $J$ so large that $J-h-W\ge2$ and $J-h'-W\ge2$. The two gap words

$$
v\,(J-h-W)\,w,\qquad v'\,(J-h'-W)\,w
\tag{15.3}
$$

both have physical length $J$. Their ratios equal those of $v,v'$ respectively, since merging has already occurred after $v,v'$. The assumed equality at length $J$ forces the original ratios to agree. Thus every guard-ending word has one ratio $k>0$.

On each of these cylinders the two entire future measures factor into their finite likelihoods and a common terminal predictive law. Hence $dF_b/dF_a=k$ there. Proposition 5.3 makes the union of cylinders containing a completed guard have full measure for both laws. Normalization gives $k=1$, so $F_a=F_b$, a contradiction. Positivity of all finite likelihoods follows from (4.7). This argument gives no bound on $J$ or on the witness lengths. The premise $F_a\ne F_b$ can in particular be supplied by a nonzero tested binary cylinder in Proposition 10.2. $\square$

**Proposition 15.3 (Positive actual fibre and original site conditionals).** For the split and witnesses in Proposition 15.2 there are three fixed intact guards, a center coordinate $Y=X_0$, and a finite future filling variable $V$ with the following properties. The nearest center neighbors occupied in both center completions are at $-l,r$. The first guard precedes the center, the second ends at a common anchor $B_\ast>r$, and the third lies strictly after $B_\ast$. Let $A_\ast$ be the first guard's starting anchor and let $R$ be the third guard's ending anchor. Conditional on a positive strict-left context event, the fixed scaffold and the common actual outside, the original law induces a finite probability $p$ with full Cartesian support

$$
\{0,1\}\times\mathcal V.
\tag{15.4}
$$

Here $\mathcal V$ contains all no11-legal fillings of the chosen segment from $r$ to $B_\ast$, with its endpoints and the entire second guard fixed. If $\gamma(v)$ is the gap word of such a filling after $r$, then

$$
a(v):=p(Y=1\mid V=v)
=\frac{B L_b(\gamma(v))}{M L_a(\gamma(v))+B L_b(\gamma(v))},
\qquad \operatorname{Var}_{p_V}(a)>0.
\tag{15.5}
$$

This $a(v)$ is the original full-exterior center posterior. If $i$ is a nonfixed coordinate of $V$ and $Z=V_{-i}$, then

$$
p(V_i=1\mid Y=y,Z=z)=q_i^P(x^{y,v})
\tag{15.6}
$$

on every compatible site fibre. A forced singleton has its common deterministic bit as conditional mean.

Proof. Choose an original positive context $c_\ast\in D$ at an unchanged anchor $T_\ast$. Take a fixed gap, for example $2$, to the starting anchor $A_\ast$ of the first guard. Apply that guard. The resulting original context is still in $D$. Irreducibility of the context chain in (4.9) gives a finite connecting gap word from this context to $c$: each edge of a positive path has at least one gap label realizing it. Fix this connection and place its final anchor at $-l$. All its gap factors, and the two center-completion factors $M,B$, are positive. Thus reaching $c$ after the first guard is part of the construction, rather than an assumption that a guard reaches any prescribed context.

Place $u,u'$ after the common anchor $r$. Their equal physical lengths put the second guard at the same physical coordinates, ending at $B_\ast$. Fix its bits, take a fixed gap after $B_\ast$, and then place the third guard, ending at $R$. Freeze the prefix, the center-neighbor gaps, this later connection and all three guards. Allow every legal filling of the remaining future segment, not only the two witnesses. Legal support is independent of $Y$, since the center is separated from this segment by its fixed right anchor and $l,r\ge2$.

Every filling has a positive finite product by (4.7). Both center choices start the future segment in the same phase, by (4.11). Every filling has the same physical displacement to the second guard's starting anchor, so (5.1) gives the same phase there. Equation (5.5) gives one terminal predictive state at $B_\ast$ for every filling and both center choices. Consequently the finite conditional disintegration has a common left channel and a common entire-right channel; its weights are proportional to

$$
p(0,v)\ \propto\ M L_a(\gamma(v)),\qquad
p(1,v)\ \propto\ B L_b(\gamma(v)).
\tag{15.7}
$$

The fixed prefix factors cancel as well. This disintegration conditions on the actual exterior sigma-field; it never divides point masses of infinite configurations. The compatible finite-pattern event has positive probability. Its scalar weights are positive and independent of the remaining outside on the corresponding conditional domain. Thus (15.4) and (15.5) follow, with positive variance because the two ratios in (15.2) give different values of the strictly increasing function $t\mapsto Bt/(M+Bt)$.

For (15.6), fixing the entire outside, the scaffold, $Y$ and every coordinate of $V$ except $i$ leaves exactly the legal original single-site completions. Including all legal fillings is essential here: retaining only two witness words could remove a legal completion and change the conditional mean. The original conditional-expectation identity therefore gives (15.6); if only one completion is legal it gives the deterministic value. The common saturated domain and positive-pattern extension of Proposition 7.1 supply these statements simultaneously. Only predictive-state synchronization and the phase quotient law (5.1) were used. Neither an original-context semigroup nor positivity of hidden matrix entries was required. $\square$

## 16. Complete original-score response of the guarded fibre

**Definition 16.1 (Inclusive score and frozen response).** For a fibre of Proposition 15.3, put $I=[A_\ast,B_\ast]\cap\mathbb Z$. Partition every site of $I$ into the center $0$, the nonfixed future sites $J$, and all remaining frozen sites $F$. Write $\epsilon_j$ for the fixed bit at $j\in F$. Retain the original losses

$$
\ell_i(y,v)=(x_i^{y,v}-q_i^P(x^{y,v}))^2,\qquad
S_P(y,v)=\sum_{i\in I}\ell_i(y,v),\qquad
D_F(v)=\sum_{j\in F}[\ell_j(1,v)-\ell_j(0,v)].
\tag{16.1}
$$

In particular $A_\ast,B_\ast\in F$ and both are scored. Set $\alpha=p(Y=1)$ and use

$$
\widehat p(y,v)=p_Y(y)p_V(v)
\tag{16.2}
$$

only as scalar coefficients in finite sums of these same losses. For $i\in J$, write $Z_i=V_{-i}$ and define

$$
\begin{aligned}
a_{i,y}(z)&=p(V_i=1\mid Y=y,Z_i=z),\\
\pi_{i,y}(z)&=p(Y=y\mid Z_i=z),\\
m_i(z)&=\sum_{y=0}^1\pi_{i,y}(z)a_{i,y}(z),\\
G_i&=\mathbb E_{p_{Z_i}}\!\left[
\operatorname{Var}_{\pi_i(\cdot\mid Z_i)}(a_{i,Y}(Z_i))
+\sum_{y=0}^1p_Y(y)(a_{i,y}(Z_i)-m_i(Z_i))^2\right],\\
\Gamma_j&=\sum_{y,v}(\widehat p(y,v)-p(y,v))
(\epsilon_j-q_j^P(x^{y,v}))^2\quad(j\in F).
\end{aligned}
\tag{16.3}
$$

All posteriors in these definitions belong to $P$. No posterior is recomputed with coefficients $\widehat p$. The square-loss algebra is the conditional Brier mechanism of Dawid--Lauritzen--Parry, *Proper Local Scoring Rules on Discrete Sample Spaces*, [arXiv:1104.2224v2, §4.2, Example 4.4 and (14)](https://arxiv.org/html/1104.2224v2), used here on the original legal fibres, including their forced singletons. The centering of a boundary response against a posterior is also the algebra used in [Anchor response, Theorem 6.2](FIB_LEGAL_EDGE_LOAD_OPTIMIZER_ANCHOR_RESPONSE_AND_RESET_VARIANCE_DENSITY.md#6-mean-covariance-and-exact-screening). That theorem concerns a finite optimizer's own reset slice; the actual-law identification of $p$, the inclusion of every frozen site and the boundary likelihoods below are supplied by Propositions 15.3 and 16.2.

**Proposition 16.2 (Actual-reset response identity and a sufficient contrast).** On the fibre of Proposition 15.3,

$$
\begin{aligned}
\sum_{y,v}(\widehat p-p)(y,v)S_P(y,v)
&=2\operatorname{Var}_{p_V}(a)+\sum_{i\in J}G_i+\sum_{j\in F}\Gamma_j\\
&=2\operatorname{Var}_{p_V}(a)+\sum_{i\in J}G_i
-\operatorname{Cov}_{p_V}(a,D_F),\qquad G_i\ge0.
\end{aligned}
\tag{16.4}
$$

Every frozen-site posterior, including either boundary anchor, has the following original finite-likelihood expression. Keep the unchanged anchor $T_\ast<A_\ast$ from Proposition 15.3 and its actual row $r_\ast=r_{c_\ast}$. For $j\in F$, let $z_{j,e}^{y,v}$ be the binary completion on $(T_\ast,R]$ obtained by setting site $j$ to $e$. With $M_z$ denoting the spatially ordered product of the original $M_0,M_1$, put

$$
W_{j,e}(y,v)=r_\ast M_{z_{j,e}^{y,v}}\mathbf1,
\qquad
q_j^P(x^{y,v})=\frac{W_{j,1}(y,v)}{W_{j,0}(y,v)+W_{j,1}(y,v)}.
\tag{16.5}
$$

An illegal completion has weight zero, and the denominator is positive on the actual pattern. A legal flip is retained even if it leaves the chosen Cartesian fibre or destroys the first or second guard.

Under the attainment assumption, Proposition 7.1 gives the necessary identity

$$
\operatorname{Cov}_{p_V}(a,D_F)
=2\operatorname{Var}_{p_V}(a)+\sum_{i\in J}G_i>0.
\tag{16.6}
$$

Consequently a witness satisfying the additional inequality

$$
\operatorname{Cov}_{p_V}(a,D_F)<2\operatorname{Var}_{p_V}(a)
\tag{16.7}
$$

contradicts the original guarded-score identity. A constant $D_F$ is sufficient. More generally it is sufficient that some $\delta>0$ satisfy, for every $v,v'\in\mathcal V$,

$$
(a(v)-a(v'))(D_F(v)-D_F(v'))
\le(2-\delta)(a(v)-a(v'))^2.
\tag{16.8}
$$

Proof. At the center the original conditional loss at $v$ is $a(v)-a(v)^2$. The product coefficients give $\alpha-2\alpha a(v)+a(v)^2$. Since $\mathbb E_{p_V}a=\alpha$, their averaged difference is $2\operatorname{Var}_{p_V}(a)$.

At a variable future site $i$, condition on $Z_i=z$ and abbreviate $a_{i,y}(z),\pi_{i,y}(z),m_i(z)$ by $a_y,\pi_y,m$. Proposition 15.3 identifies the unchanged predictor with $a_y$. Under the original coefficients the conditional loss is $m-\sum_y\pi_y a_y^2$. The product coefficients have the same $Z_i$ marginal and the same conditional mean $m$ of $V_i$, while their $Y$ weights are $p_Y$. Their conditional loss is $m-2m\sum_y p_Y(y)a_y+\sum_y p_Y(y)a_y^2$. Subtraction gives

$$
\sum_y\pi_y a_y^2-2m\sum_y p_Y(y)a_y+\sum_y p_Y(y)a_y^2
=\operatorname{Var}_{\pi}(a_Y)+\sum_y p_Y(y)(a_y-m)^2.
\tag{16.9}
$$

Averaging proves exactly the term $G_i$, with its nonnegative sign. A forced site has the same deterministic value for both $y$, so contributes zero to (16.9). Every other site of $I$ is in $F$, and its contribution is exactly $\Gamma_j$. This proves the first line of (16.4), with no unscored scaffold terms.

To prove (16.5), start the original future disintegration at $T_\ast$. Both completions have the same physical endpoint $R$ and an intact third guard. At its starting anchor their phases agree by their common physical displacement from $T_\ast$. The third guard then merges their predictive states by (5.5). Hence their complete remaining future channels cancel, and their finite original weights are precisely $W_{j,0},W_{j,1}$. At least the actual completion has positive weight. Illegal completions have zero visible probability; a forced site gives the deterministic original posterior. Deleting $A_\ast$ or $B_\ast$ can break the first or second guard, but leaves this third guard intact, so it does not invalidate the formula. Structural zeros in the matrices do not invalidate the positive scalar weights of legal gap words.

For each fixed $v$,

$$
(\widehat p-p)(1,v)=p_V(v)(\alpha-a(v)),\qquad
(\widehat p-p)(0,v)=-p_V(v)(\alpha-a(v)).
\tag{16.10}
$$

Thus summing the frozen contributions gives

$$
\sum_{j\in F}\Gamma_j
=\mathbb E_{p_V}[(\alpha-a)D_F]
=-\operatorname{Cov}_{p_V}(a,D_F).
\tag{16.11}
$$

This proves the second line of (16.4). Proposition 7.1 makes the inclusive $S_P$ constant on this entire fibre. The coefficients $\widehat p-p$ sum to zero, so (16.4) has left side zero. Positive variance in (15.5) now gives (16.6). Under (16.7) the right side of (16.4) is strictly positive, a contradiction. For two independent samples $V,V'$ with law $p_V$,

$$
\operatorname{Cov}(a,D_F)
=\tfrac12\mathbb E[(a(V)-a(V'))(D_F(V)-D_F(V'))],\qquad
\operatorname{Var}(a)=\tfrac12\mathbb E[(a(V)-a(V'))^2].
\tag{16.12}
$$

Consequently (16.8) implies (16.7), since $\operatorname{Var}(a)>0$.

Constant total original score alone does not justify deleting a frozen separator's response. As an intermediate finite illustration, take the unique positive optimizer of the original open-path $\Phi_3$ on $\{000,100,010,001,101\}$ supplied by [Positive unique optimizer, Theorem 3.1](FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md#3-唯一性与全部原坐标的正性). Reuse its uniqueness, full support and vertex-score equation (3.8), rather than a new optimizer assertion. Reflection and uniqueness put its masses in the form $(\xi,\eta,\delta,\eta,\zeta)$ in the displayed word order. Write $u=\eta/(\xi+\eta)$, $v=\zeta/(\eta+\zeta)$ and $w=\delta/(\xi+\delta)$. Its complete original scores are

$$
S_{000}=2u^2+w^2,\quad
S_{100}=S_{001}=(1-u)^2+v^2,\quad
S_{101}=2(1-v)^2,\quad S_{010}=(1-w)^2.
\tag{16.13}
$$

They are equal by the supplied vertex-score equation. If the endpoints were independent conditional on the middle bit being zero, then $\xi\zeta=\eta^2$ and $u=v$. Equality of $S_{100},S_{101}$ would force $u=v=1/2$. Equality of $S_{000},S_{010}$ would then force $w=1/4$, but $S_{101}=1/2\ne9/16=S_{010}$. Thus the endpoints are dependent on that Cartesian fibre. The frozen middle loss equals $w^2$ at $000$ and zero at $100,001,101$, so it supplies a genuine nonconstant response. This illustration concerns the existing finite optimizer only, and supplies no stationary attaining law or counterexample to the original actual-reset assertion.

Neither (16.7) nor (16.8) has been deduced from Assumption 15.1. They are sufficient conditions on a witness, not additional conclusions of attainment. In particular the threshold $2\operatorname{Var}(a)$ is not asserted necessary for every possible exclusion: the complete contrast in (16.4) also contains the nonnegative $G_i$. $\square$

## 17. Finite likelihood types and a realizable original-score carrier

**Definition 17.1 (Forward-closed predictive pairs on fixed letters).** Fix a finite gap alphabet $\Gamma\subset\{2,3,\ldots\}$ and a finite nonempty set of actual split seeds in the component $D$. A seed is the ordered predictive pair $(a,b)$ in (15.1) for a specified $c,l,r$. Let $\mathcal P_\Gamma$ be their forward closure under

$$
T_g(s,t)=(\tau_g(s),\tau_g(t))\quad(g\in\Gamma).
\tag{17.1}
$$

It is a finite subset of $S_D\times S_D$, including any diagonal descendants. For $p=(s,t)\in\mathcal P_\Gamma$ define

$$
R_p(v)=\frac{L_t(v)}{L_s(v)},\qquad
\rho_p(g)=\frac{f_t(g)}{f_s(g)},\qquad
\mathbf R(v)=(R_p(v))_{p\in\mathcal P_\Gamma}\quad(v\in\Gamma^*).
\tag{17.2}
$$

The vector is always formed from one common word $v$; its coordinates are not independently selectable.

**Proposition 17.2 (Finite exact likelihood types for the actual split pairs).** Every directed labelled cycle of $\mathcal P_\Gamma$ has likelihood multiplier $1$. Each $R_p$ has finite range on $\Gamma^*$, as does the joint vector $\mathbf R$. They satisfy

$$
R_{(s,t)}(gv)=\frac{f_t(g)}{f_s(g)}
R_{(\tau_g(s),\tau_g(t))}(v),\qquad
\mathbf R(\varnothing)=\mathbf1.
\tag{17.3}
$$

After a common guard has merged a reachable pair, further suffix extension cannot change that word's ratio.

Proof. For each seed $(a,b)$, (4.11) applied to a finite positive cylinder gives

$$
\frac{M}{3B}\le\frac{L_b(v)}{L_a(v)}\le\frac MB
\tag{17.4}
$$

for every finite gap word, with that seed's $M,B$. If a word $u$ reaches $p=(s,t)$ from this seed and $k=L_b(u)/L_a(u)>0$, factorization gives

$$
\frac{M}{3Bk}\le R_p(v)\le\frac{M}{Bk}.
\tag{17.5}
$$

These rescaled bounds apply to all suffixes $v$. In particular, if a word $z$ is a cycle at $p$, then $R_p(z^n)=R_p(z)^n$ for all $n$. The positive finite upper and lower bounds in (17.5) force $R_p(z)=1$.

Use the usual finite-graph loop-erasure argument: remove a segment between repeated ordered-pair states. It is a cycle with multiplier $1$, so removing it preserves both the endpoint pair and the likelihood product of the remaining path. Repeating this operation leaves a simple labelled path of length at most $|\mathcal P_\Gamma|-1$. Because both the state set and the label alphabet are finite, only finitely many such paths exist. Their products include every value of $R_p$. The joint range lies in the finite product of these coordinate ranges, proving its finiteness. Factorization gives (17.3). Merged predictive states have identical suffix likelihoods, proving the last assertion.

The reused loop-erasure principle is also the finite-path argument in [Action graph communication bound, Theorem 1.5](../../../Blueprint/D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.md). Its stated costs are natural-valued additive costs. Here logarithmic likelihood increments may have either sign, so that theorem is not directly applied to them; the two-sided actual bounds (17.5) supply the multiplicative cycle conclusion needed for the same path deletion argument. This is not a separate general graph theorem. The use of predictive synchronization is within Proposition 5.3's countable-gap scope and its stated Travers--Crutchfield comparison, not an extension of their finite-alphabet theorem by citation alone.

Finiteness here requires a fixed finite $\Gamma$. Over all gap sizes there can be infinitely many labelled simple paths even with a fixed finite pair set. No finite representation on the entire countable alphabet, effective period, decision procedure or uniform resource bound follows. $\square$

**Proposition 17.3 (Original scores on a realizable finite carrier).** Fix $G\ge2$, the three finite guards and the fixed boundary connections, with every gap in these data at most $G$. Consider all compatible original guarded patterns whose consecutive gaps, including the gap preceding the first scored anchor, the gap following the terminal scored anchor and the path through the third guard, are at most $G$. Their full-exterior original scores admit a finite exact representation as follows.

Use $\Gamma=\{2,\ldots,G\}$ and include the predictive pairs

$$
\left(\tau_{l+r}(c),\tau_r(\tau_l(c))\right)
\quad(c\in D,\ 2\le l,r\le G)
\tag{17.6}
$$

as seeds, then take their forward closure under $\Gamma$. These include the seeds for occupied-anchor deletions and every legal zero-site subgap split. Retain the original scalar values $f_c(g)$ through $g=2G$ for the merged deletion gaps. For a suffix vector $\mathbf R$ define

$$
\vartheta(c,l,r;\mathbf R)
=\frac{f_c(l)f_{\tau_l(c)}(r)
R_{(\tau_{l+r}(c),\tau_r(\tau_l(c)))}}
{f_c(l+r)+f_c(l)f_{\tau_l(c)}(r)
R_{(\tau_{l+r}(c),\tau_r(\tau_l(c)))}}.
\tag{17.7}
$$

If $h,g$ are consecutive gaps, $s_0$ is the predictive state at the anchor preceding them and $s=\tau_h(s_0)$, the original half-open gap score is

$$
H(s_0,h,g,\mathbf R)
=(1-\vartheta(s_0,h,g;\mathbf R))^2
+\sum_{j=2}^{g-2}\vartheta(s,j,g-j;\mathbf R)^2,
\tag{17.8}
$$

where the suffix vector is taken after the next anchor and an empty sum is zero. In particular, for $A_\ast=T_0<T_1<\cdots<T_n=B_\ast$,

$$
S_P[A_\ast,B_\ast]=\sum_{k=0}^{n-1}H_k+\ell_{T_n}.
\tag{17.9}
$$

The final occupied-anchor loss uses its actual preceding gap, next gap and the suffix through the third guard. It is not absorbed by omitting an endpoint term.

The representation retains the actual forward context, the preceding gap, fixed boundary data and the finite joint suffix vector of Proposition 17.2. Only trajectories arising from a single common original gap word and its fixed terminal guard are admissible. Equivalently the suffix vectors obey (17.3) backwards, with terminal vector $\mathbf1$ at $R$, and are matched to the forward trajectory of that same word.

Proof. Deleting an occupied anchor merges precisely its preceding and following gaps, each at most $G$. Its merged gap can have length $2G$, which explains the retained scalar values. Comparing its occupied and deleted completions gives exactly (5.9), with the seed in (17.6) and the suffix after the next anchor. The original posterior is (17.7), so its occupied loss is $(1-\vartheta)^2$.

At a zero site strictly inside a gap $g$, a legal insertion splits that gap into $j,g-j\ge2$. Its two future states give the corresponding seed from (17.6), and the same actual suffix gives its posterior (17.7). The actual zero loss is $\vartheta^2$. Immediate neighbors of occupied anchors are forced and have zero loss. These account for every site in the half-open interval from one anchor up to, but excluding, the next. This proves (17.8), including $g=2,3$ when there are no nonforced zero sites, and summation gives (17.9).

Every scored comparison ends through the intact third guard. It therefore computes the full-exterior original posterior, even if deleting a scored boundary anchor breaks one of the earlier guards. The comparison words need not have all gaps at most $G$: a deletion is evaluated with its original merged-gap probability through $2G$. Thus no bounded-gap conditional law replaces $P$.

There are finitely many forward contexts, preceding gaps and required scalar values, and Proposition 17.2 gives finitely many suffix vectors. Hence the local data and their scores have finite range. To impose realizability explicitly, write the common word from an unchanged left anchor through $R$ as $g_1\cdots g_m$. At its $k$th anchor let

$$
 c_k=\tau_{g_k}\cdots\tau_{g_1}(c_0),\qquad
 \mathbf R_k=\mathbf R(g_{k+1}\cdots g_m),\qquad
 \mathbf R_m=\mathbf1.
\tag{17.10}
$$

Equation (17.3) is the backward relation between successive $\mathbf R_k$, while the first relation is the forward one. Retaining only these paired trajectories, with the fixed guards and boundary connections, yields the claimed finite carrier. Arbitrary coordinate combinations from the product of ratio ranges are not used.

Every particular fibre in Proposition 15.3 fits some finite $G$: it has finitely many sites and fillings, and all its fixed connections and guards are finite. This observation gives no bound for that $G$ in terms of the period in Proposition 14.1. The period reduces the split-future tests, whereas Proposition 15.2 supplies an equal-length posterior witness and the present construction represents all original scores of a chosen bounded pattern family. None of these statements bounds the nonlinear scaffold response $D_F$.

In particular pair-likelihood cycle multipliers equal to $1$ do not establish a score identity of the form $H(e)=\kappa g(e)+V(\operatorname{head}e)-V(\operatorname{tail}e)$. Any such identity needs its own proof on the realizable combined forward/backward carrier. A score-cycle comparison must be reachable from the common left boundary and extendible through the common third guard, with the terminal loss in (17.9) and all deletion charges retained. Unequal likelihoods can occur on transient pair paths even though every pair cycle has multiplier $1$.

The unresolved original implication is whether the unchanged actual finite-reset hypotheses force every split-future defect to vanish, or supply a nonzero original-score contrast despite all frozen responses. The specific sufficient route (16.7) still requires a witness with response covariance below $2\operatorname{Var}(a)$, or a rigorously realizable weighted contrast accounting for every terminal and deletion charge. Equations (16.6) and (17.3) do not prove that requirement. No strict matrix positivity, right context decoder, original-row semigroup, inverse of $Z$, modified loss or replacement stationary or Palm law is assumed. Structural zeros and null contexts retain the scope of Definition 4.1. These are consequences and representations for the stated actual-law interfaces, with the cited algebraic and graph ingredients reused in their specified scopes; no literature-novelty assertion is made for the connection. $\square$

## 追加锚（本行以下为增补区）

## 18. Equal-physical-length certificate for supplied actual score data

**Assumption 18.1 (Finite actual data and original-compatible boundaries).** Use the original stationary joint law, visible marginal $P$, actual Palm law $Q$ and strict-left reset of Definition 4.1. On a supplied positive actual component, suppose the following structural data are given, without assuming $d(P)=c_\star$ or any score-constancy identity.

There is a finite predictive state set $S$, with actual future laws $F_c$, actual gap rows $f_c(g)>0$ for $g\ge2$, and actual maps $\tau_g:S\to S$. The rows are normalized with finite mean, and the full-history reset rule gives the actual cylinder likelihood

$$
L_c(g_1\cdots g_m)=\prod_{k=1}^m f_{c_{k-1}}(g_k),
\qquad c_k=\tau_{g_k}(c_{k-1}),\qquad L_c(\varnothing)=1.
$$

Fix $G\ge2$ and $\Gamma=\{2,\ldots,G\}$. Supply the original scalar rows through $2G$ and a forward-closed ordered-pair set $\mathcal P\subset S^2$ containing every pair in (17.6). Supply the finite **joint actual** range

$$
\mathcal T=\{\mathbf R(v):v\in\Gamma^*\},\qquad
\mathbf R(v)_{(u,v')}=\frac{L_{v'}(v)}{L_u(v)}.
$$

In particular its coordinates come from one common suffix word. The identity (17.3), used only as actual reset factorization, defines the supplied maps

$$
\bigl(\Phi_g(t)\bigr)_{(u,v)}
=\frac{f_v(g)}{f_u(g)}t_{(\tau_g(u),\tau_g(v))},\qquad
\mathbf R(gz)=\Phi_g(\mathbf R(z)),\qquad
\mathbf R(\varnothing)=\mathbf1.
\tag{18.1}
$$

Finiteness of $S,\mathcal T$ and the phase/guard interfaces is a premise here; no attainment-dependent conclusion of Proposition 17.2 supplies it.

A supplied finite boundary package specifies an unchanged left anchor $T_\ast<A_\ast$, its positive actual reset state, the fixed connections and guards, and an intact third guard ending at $R>B_\ast$. It includes a finite spatial phase clock and the actual rule that the third guard merges predictive states in each common phase. Phase equality denotes mutual absolute continuity of future channels, not equality of predictive states. For each allowed boundary mode, the gap word from $B_\ast$ through $R$ is fixed and nonempty, say $\eta=b\xi$ with $b\in\Gamma$; the fixed prefix from $T_\ast$ determines the state $c$ at the predecessor of $A_\ast$ and its gap $h\in\Gamma$ to $A_\ast$. The package specifies allowed terminal predictive states and phases after $\eta$.

The authorized original words have a fixed prefix, a $\Gamma^*$ interior and fixed closing data, subject to finite phase and guard constraints. All their original gaps, from the predecessor of $A_\ast$ through $R$, are at most $G$. Finite control records the exact allowed language, including its empty or short interiors and any authorized coincidences of joining anchors or scored boundaries. Every entry-to-exit matching constraint and every allowed relation between two boundary modes is finite and is retained in persistent boundary tags; a path cannot change its boundary prescription at a shared interior state. No unauthorized coincidence or empty word is added.

For each allowed pair, the unchanged left reset and fixed left exterior agree; equal physical displacement puts its fixed closing data at the same coordinates and gives a common phase at the third guard. For each legal one-site completion at a scored site, $T_\ast$ stays unchanged, the third guard stays intact, and the two completion channels have this common phase before that guard. Thus the direct structural full-exterior bridge in the proof of (16.5) applies: the common left factor and the synchronized entire future after $R$ cancel in the original posterior. This is a condition on the original law and guards, including completions outside the authorized language. No right decoder, entrywise matrix positivity, inverse context map, or replacement stationary or Palm law is supplied or required.

**Proposition 18.2 (Finite original-score contrast certificate).** Under Assumption 18.1 there is a terminal-pinned finite weighted acceptance presentation of exactly the positive compatible original words, whose path weight is the inclusive original score $S_P[A_\ast,B_\ast]$. Expand its edges into physical unit steps and form the synchronous pair graph with the allowed persistent boundary tags. Trim it by retaining exactly vertices and edges on an entry-to-exit path. Write $d_e$ for the left-minus-right edge weight, $\alpha_i$ for each entry-record offset and $\beta_f$ for each exit-record offset. Every equal-physical-length compatible original contrast vanishes if and only if the following finite real system has a solution:

$$
V_v-V_u=d_e\quad(e:u\longrightarrow v),\qquad
V_{v(i)}=\alpha_i\quad\hbox{for every entry record }i,\qquad
V_{v(f)}=-\beta_f\quad\hbox{for every exit record }f.
\tag{18.2}
$$

Distinct records at the same vertex impose their equations separately. The empty trim graph gives a vacuous system. If (18.2) is inconsistent and $n\ge1$ is the number of trim **unit-pair vertices**, excluding virtual boundary bookkeeping nodes, there are genuine positive compatible original patterns with nonzero contrast, common displacement at most $2n-1$ and inclusive scored length at most $2n$.

Proof. Write $\theta=\vartheta$ from (17.7), and retain $H$ from (17.8). For a boundary mode put

$$
t_B=\mathbf R(\eta)=\Phi_\eta(\mathbf1),\qquad
t_+=\mathbf R(\xi)=\Phi_\xi(\mathbf1),\qquad
\beta(c,h)=(1-\theta(c,h,b;t_+))^2,
\tag{18.3}
$$

where $\Phi_{g_1\cdots g_m}=\Phi_{g_1}\circ\cdots\circ\Phi_{g_m}$. Thus the type is $\mathbf1$ at $R$, but is $t_B$, generally different from $\mathbf1$, at $B_\ast$. The final loss uses the suffix *after* the following gap $b$, hence $\mathbf R(\xi)$ in (18.3).

A carrier vertex consists of finite language/phase control, its persistent boundary tag, and $(c,h,t)\in S\times\Gamma\times\mathcal T$. Its current anchor has predictive state $\tau_h(c)$. A permitted outgoing gap $g\in\Gamma$ gives an edge

$$
(c,h,t)\longrightarrow(\tau_h(c),g,t')
\quad\Longleftrightarrow\quad t=\Phi_g(t'),
\qquad \operatorname{length}(e)=g,\qquad
\operatorname{weight}(e)=H(c,h,g;t'),
\tag{18.4}
$$

with the corresponding control update and unchanged tag. Entry records have the prescribed actual $(c,h)$, arbitrary $t\in\mathcal T$, and weight zero. Exit records require accepting control, $t=t_B$, and the specified predictive/phase test after propagating $\tau_h(c)$ through $\eta$; their weight is $\beta(c,h)$.

An authorized word supplies its forward trajectory and its joint suffix types, so gives an accepting path. Conversely, for a path with gaps $g_1,\ldots,g_m$, the exit pin and (18.4) force, by backward induction,

$$
t_k=\mathbf R(g_{k+1}\cdots g_m\eta)\quad(0\le k\le m).
\tag{18.5}
$$

The forward recurrence forces the actual predictive trajectory of that same word, precisely as in (17.10). Noninjectivity of $\Phi_g$ creates no extra accepted assignment: the terminal pin determines every earlier type. The control and tags enforce the authorized boundary matches; positivity of the actual finite gap products gives positive original patterns. This proves exact acceptance without independently mixing attainable coordinates or adding inverse maps.

For completeness, the two weights at a site with adjacent anchor gaps $l,r$ are $M L_a(z)$ and $B L_b(z)$, where $M=f_c(l+r)$, $B=f_c(l)f_{\tau_l(c)}(r)$ and $(a,b)$ is (17.6). The supplied full-exterior bridge identifies their ratio with the original $q_i^P$, giving (17.7). At an occupied anchor its loss is $(1-\theta)^2$; inside the following gap the legal zero insertions contribute the $\theta^2$ terms of (17.8), and forced neighboring zeros contribute zero. The half-open anchor intervals partition $[A_\ast,B_\ast)$, including every fixed scaffold site, and (18.3) adds exactly the remaining occupied endpoint. Thus (17.9) gives

$$
\sum_e\operatorname{weight}(e)+\beta(c_m,h_m)
=S_P[A_\ast,B_\ast],\qquad
\sum_e\operatorname{length}(e)=B_\ast-A_\ast.
\tag{18.6}
$$

Both endpoints are scored. A deletion may destroy an earlier guard or leave the accepted family; its merged gap is still evaluated under the original row, through $2G$. No conditioning of $P$ onto bounded gaps occurs. If an authorized mode has $A_\ast=B_\ast$, an allowed entry/exit coincidence uses $\beta$ once and no $H$. Empty or short interiors and overlapping joining anchors are decided by the finite control, with each physical anchor counted once.

Subdivide every length-$g$ edge into a private chain of $g$ unit edges, placing its weight on the first edge and zero on the others. Entry and exit records remain at original boundary vertices. Pair arbitrary unit steps synchronously, without requiring equal gap labels or equal numbers of gaps, and retain the boundary tags before trimming. Private chains prevent starting or ending inside a gap. Accepted pair paths are exactly the allowed original pairs with equal displacement, hence equal inclusive scored length. Their weight is

$$
\alpha_i+\sum_e d_e+\beta_f
=S_P(x)-S_P(x').
\tag{18.7}
$$

Here $\alpha_i$ is the difference of the two zero entry weights, and $\beta_f$ is the difference of the two losses (18.3). Every boundary record is retained even if several occur at one vertex. The common left reset, spatial phase matching and intact third guard give the same original exterior channels for the two words. Their finite original likelihoods are positive on that disintegration. Consequently any accepted product witness lifts to positive compatible original patterns, rather than merely to a synthetic pair of carrier paths.

A solution of (18.2) telescopes (18.7) to zero. Conversely, suppose every accepted contrast is zero. For a trim vertex $v$, define $V_v$ as the entry offset plus the edge sum of any entry-to-$v$ prefix. Any two such prefixes can be followed by a common $v$-to-exit suffix, including its exit offset. The persistent tags make both concatenations authorized. Their zero contrasts make the two prefix values equal. Appending an edge proves its equation; the empty prefix of each entry record and each complete prefix at an exit record give all boundary equations in (18.2). This also handles disconnected trim components, multiple entries/exits and boundary coincidences. Directed-cycle equations alone would not impose these transient and boundary conditions.

For a constructive bound, choose for every trim vertex $v$ a simple entry-to-$v$ prefix $P_v$ and a simple $v$-to-exit suffix $Q_v$, each with at most $n-1$ unit edges and its chosen boundary record. Let $p(P_v)$ include its entry offset, let $q(Q_v)$ include its exit offset, and set $V_v=p(P_v)$. If the system is inconsistent, these candidate values fail some equation. A failed exit equation makes $P_{v(f)}$ a nonzero accepted contrast. A failed entry equation at $i$ makes the two accepted contrasts

$$
\alpha_i+q(Q_{v(i)})\quad\hbox{and}\quad
p(P_{v(i)})+q(Q_{v(i)})
$$

different, so one is nonzero. A failed edge equation $e:u\to v$ makes the accepted contrasts of $P_u e Q_v$ and $P_vQ_v$ differ by the nonzero residual $V_u+d_e-V_v$, so again one is nonzero. The longest displayed accepted walk has at most

$$
(n-1)+1+(n-1)=2n-1
\tag{18.8}
$$

unit edges. These walks retain the tags and lift by (18.5)--(18.7). Their original displacement is therefore at most $2n-1$, and their inclusive scored length is that displacement plus one, at most $2n$. For its boundary mode the entire unchanged-left-anchor-to-$R$ displacement is also at most $(A_\ast-T_\ast)+(2n-1)+|\eta|$, where $|\eta|$ is physical length. When the trim graph is empty there is no accepted pair and no witness assertion; an authorized zero-edge path instead contributes a trim vertex and its entry/exit equations.

The finite-language control, product, subdivision, additive-potential telescoping and simple-path arguments are standard suppliers used inside this application. [Mohri, *Weighted Automata Algorithms*, §§1 and 6.3](https://cs.nyu.edu/~mohri/pub/hwa.pdf) supplies initial/final-weight, trim and reweighting algebra; its stronger pushing and equivalence hypotheses are not transferred to these signed contrasts. Generic product provenance is [Fliess, *Sur divers produits de séries formelles*, §3, Proposition 1, p.183, and the tensor-product remark, p.187](https://www.numdam.org/item/10.24033/bsmf.1777.pdf), as described in the [corresponding literature note](../../../Library/Automata/fliess1974products.md). The repository's [Zero loop potential equivalence](../../../Blueprint/D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.md) is a connected-groupoid result, and [Action graph communication bound](../../../Blueprint/D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.md) uses natural costs; neither is directly applied to this directed signed boundary system. The actual-word posterior construction and original-pattern lift above provide the FIB application, without a literature-novelty assertion.

All construction and residual tests use exact arithmetic and equality relative to the supplied finite real data and their generated expressions. They do not acquire $\mathcal T$, certify it from numerical approximations, or provide arbitrary-real computability. The bound depends on the resulting graph, with no uniform bound in $G$, guards or the producer and no optimality assertion. The criterion neither asserts an actual inconsistent instance nor proves original-risk attainment or nonattainment; it does not settle the unresolved original implication following (17.10). $\square$

## 追加锚（本行以下为增补区）
