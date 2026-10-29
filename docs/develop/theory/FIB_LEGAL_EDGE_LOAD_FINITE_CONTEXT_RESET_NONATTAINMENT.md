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
