# 局部相容、层级坐标与预测谱

本文把五模式中被均值遗漏的联合关系、完整边界拼接，以及带父块原点的粗粒化放在同一个观察框架中。五模式的闭概率纤维、Markov 最大熵补全和 minimax 由既有文稿供应；在这些结果上，指定经典操作给出尖锐的固定剩余质量预测界。父块同余与两条粗化恒等式则产生选择无关的层级相位。有限字母表、闭性、局部识别、不变测度和有效解码分别是后续拓扑、统计与算法结论的输入。

这里的证明是普通数学证明，没有新增 Lean 声明或新的 kernel 核验。源码引用只承担所列声明及定义的范围，不代替依赖闭包审计。平移字符的谱不供应物理量子态、Born 概率、物理时间或哈密顿量。

## 1. 对象、来源与复用坐标

**约定 1.1（固定来源）。** 项目形式接口取提交 `194597016233d92b0d42fe93e8cda55f2f6ea471`，记为 [T]；以下项目理论供应取共同快照 `e28e989d0a9315863d002ca75f78050985bdedc7`，记为 [B]。Palomar CLARK 来源取 `5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`，记为 [P]。引用以文末的固定地址为准。

| 供应者 | 本文实际使用的域与对应 |
| --- | --- |
| [基础公式卷](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md) §§4、6、7、9 | 全部闭五模式概率单纯形；其模式 $(0,2,3,5,25)$ 对应本文 $(000,100,010,001,101)$，其 $(X,Y,Z)=(m_1,m_3,m_2)$；本文自然熵 $H=(\ln2)H_2$ |
| [局部重建卷](AURIC_FIB_ATOM_LOCAL_RECONSTRUCTION_AND_LOOP_CORRECTION.md) §§1、2、4 | 位置均值 $(u_1,u_2,u_3)=(m_1,m_2,m_3)$；严格接缝的链 Markov 公式；闭支撑和顶点取基础公式卷的较强结论 |
| [边界运输卷](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md) §3 | 五条边的完整左右二元边缘；其 $(X,Y,Z)=(m_1,m_3,m_2)$。本文 §4 使用另一种两端 separator，不把两种边界混同 |
| [选择项演算](AURIC_FIB_ATOM_SELECTION_CALCULUS.md) §§6、15、20–26 | 闭纤维、显式共享网络、同源读口、共同动作和付费取得；其代数顺序 $(x,y,z)$ 对应本文物理位 $(X_1,X_3,X_2)$ |
| [Rutten 文献注](../../../Library/ConceptDynamics/rutten1996universal.md) §7 | 显式有限事实、付费种子和共享标签；不是免费取得结构的承诺 |
| [Wainwright–Jordan 文献注](../../../Library/Estimation/wainwrightjordan2008graphical.md) §2.5.2、式 (2.12)、命题 2.1 | 有限窗口取 clique，完整交集取 separator；概率的树拼接是经典供应 |
| [Dechter 文献注](../../../Library/ConceptDynamics/dechter1996bucket.md) 命题 1–3、§6 | 给定顺序的完整 frontier、有限表和一次计分的 max-sum；本文 §11 给其树袋版本，不把经典消元机制作为新发现 |
| [T] 的恢复、控制商、记录与消息模块 | 目标因子化、共同 monoid 菜单、完整投影相等的关系拼接；集合消息本身不附有限运行时间 |
| [P] 的父块、同余、粗 world 与周期模块 | 合法注册 carrier world、固定目录及证书、整数 pose 原点；§6 给普通数学运输桥，不声称已有对应 Lean 导出 |

本文研究“观察保留了什么，遗漏怎样被操作或拼接消费”。静态存在、观察可识别、实际可取得和资源内可认证是不同问题。所有概率边缘都来自同一个随机对象；用另一来源独立配对会改变联合律。

## 2. 达到像上的恢复与同菜单未来

**数学引文 2.1（恢复判据的精确使用）。** 给集合 $X,Y,Z$、观察 $r:X\to Y$ 和目标 $f:X\to Z$，令 $r(X)$ 为达到像。存在 $D:r(X)\to Z$ 使 $f=D\circ r$，当且仅当

$$
r(x)=r(x')\Longrightarrow f(x)=f(x')\qquad(x,x'\in X).
$$

这是 [T] `TargetRecoveryCriterion.target_recovery_criterion` 的纤维条件；该声明的 decoder 定义在整个 $Y$，并有 `Nonempty X` 前提。其非空域应用在此取 `process=r,target=f`。达到像版本的全部边界如下：必要性由函数相等；充分性把 $D(r(x))$ 定为 $f(x)$，纤维条件保证所定值唯一。若 $X=\varnothing$，达到像为空，空函数就是 decoder，无需选默认值。若要求整个 $Y$ 上的 decoder，$X\ne\varnothing$ 时用任一 $f(x_0)$ 填充未达到点；$X=\varnothing$ 时，若 $Y=\varnothing$ 仍可用空函数，若 $Y\ne\varnothing$ 则恰需 $Z\ne\varnothing$。例如 $X=Z=\varnothing,Y=\{*\}$ 满足纤维条件，却没有整个 $Y$ 上的 decoder。这说明非空前提的具体作用。

**数学引文 2.2（完整未来商）。** 固定所有状态共同使用的一组总操作 $T_a:X\to X$。字 $w=(a_1,\ldots,a_t)$ 按执行顺序定义 $T_w=T_{a_t}\circ\cdots\circ T_{a_1}$，空字为恒等。置

$$
x\sim_{\rm fut}x'\iff\forall w,\ r(T_wx)=r(T_wx').
$$

将 [T] `ControlQuotientUniversalMinimality.control_quotient_universal_minimality` 的 monoid 取为操作字，乘法取“先右字后左字”的复合，即 $T_{uv}=T_u\circ T_v$，读出取 $r$，便得到该等价关系的商、商上当前读出和所有操作更新。等价关系逐个输出成立；稳定性使用 $T_wT_a$ 仍为一个共同允许字。若 $s:X\to M$ 满足

$$
r=d\circ s,\qquad s\circ T_a=F_a\circ s,
$$

字长归纳给 $s(T_wx)=F_w(s(x))$，于是 $s(x)=s(x')$ 蕴含全部未来输出相同。因此有唯一的达到像映射 $s(X)\to X/{\sim_{\rm fut}}$，把 $s(x)$ 送到 $[x]$。这就是“最粗的动作闭合充分摘要”，并不反向说商恢复全部状态。单操作特例也由 [T] `MinimalPredictiveCompletionQuotient.minimal_predictive_completion_quotient` 供应，时间指标为 $t\in\mathbb N$，读出为 $r(F^t x)$。

若许可依赖状态，比较时必须同时保留动作是否允许，或把非法动作总化为显式失败状态，失败输出与合法输出作不交标记。只比较双方碰巧都可做的动作，不能直接应用上述共同总菜单结论。下文的经典 toggle、符号平移及有限求解算法各有自己的许可合同。

## 3. 五模式的任务消费与尖锐熵界

### 3.1 闭纤维与既有完成的直接应用

**约定 3.1（物理位序）。**

$$
\Sigma=(000,100,010,001,101),\qquad
p=(p_0,p_1,p_2,p_3,p_{13}),
$$

$$
m_1=p_1+p_{13},\quad m_2=p_2,\quad m_3=p_3+p_{13},\quad
\kappa=p_{13},\quad r=1-m_2.
$$

位串从首位到中位再到末位。基础公式卷的端—端—中坐标及 [T] `FiveModeMixedCoordinates.visible` 都是 $(m_1,m_3,m_2)$；其 `Fin 5` 下标 $0,1,2,3,4$ 依次就是上述五模式，`hiddenDirection` 为 $(1,-1,0,-1,1)$。

**数学引文 3.2（完整可行域）。** 基础公式卷数学引文 4.2、选择卷定理 6.2 在表 1 的坐标变换下给：可实现均值恰为

$$
m_i\ge0,\qquad m_1+m_2\le1,\qquad m_2+m_3\le1.
$$

每个这样的均值的全部相容律恰为

$$
p_\kappa=(1-m_1-m_2-m_3+\kappa,\ m_1-\kappa,\ m_2,\ m_3-\kappa,\ \kappa),
$$

$$
L=\max(0,m_1+m_2+m_3-1)\le\kappa\le
U=\min(m_1,m_3).
$$

差为 $(\kappa'-\kappa)(1,-1,0,-1,1)$，宽度 $U-L=\min(m_1,m_3,r-m_1,r-m_3)$。这直接重标供应者的反解、非负区间和宽度证明，包含零质量及单点纤维。确定的位配置由三个逐位读数确定；歧义在概率律的均值投影中。它更不恢复任意量子密度矩阵：[T] `FiveModeDensityFiber.full_rank_local_fibre` 在正定、迹一的五维密度矩阵附近给出三读出纤维的 21 个实局部方向。该处 `means` 的实际顺序为首—中—末，与本文一致，区别于 `visible` 的首—末—中；不把满秩局部维数扩展成边界态的维数断言。

**数学引文 3.3（闭支撑最大熵与 minimax）。** 本节使用自然对数，$0\ln0=0$；KL 中若 $p_s>0=q_s$ 则取 $+\infty$。基础公式卷 §§6、9 的较强闭域定理直接供应

$$
\kappa_M=\frac{m_1m_3}{r}\quad(r>0),\qquad
\Delta H:=H(p_{\kappa_M})-H(p_\kappa)
=I(X_1;X_3\mid X_2)=D(p_\kappa\Vert p_{\kappa_M})\ge0.
$$

具体映射是 $(x,y,z)=(X_1,X_3,X_2)$，概率分量按约定 3.1 重标，所有 bit 熵、KL 和互信息乘 $\ln2$。该供应者的底面条件互信息乘 $r$ 恰是此处的条件互信息，因为 $X_2=1$ 时两端确定为零。$r>0$ 时的底面条件表为

$$
\frac1r\begin{pmatrix}r-m_1-m_3+\kappa&m_3-\kappa\\m_1-\kappa&\kappa\end{pmatrix};
$$

其边缘参数为 $m_1/r,m_3/r$，乘积表对应 $\kappa_M\in[L,U]$。零行、零列中任何相容律都无正质量，故支撑包含、KL 有限，且唯一最大熵仍成立。$r=0$ 时置 $\kappa_M=0$，唯一状态为 $010$；熵差、KL、条件互信息皆零，不定义这个零概率事件上的条件表。闭支撑、顶点和最大熵的唯一性都属于该既有供应，不能作为本节新增结果。

基础公式卷 §§7.2–7.4 对任意有限实目标 $f$ 供应 $\mathbb E_pf=A_f+J_f\kappa$ 及最坏绝对误差 $|J_f|(U-L)/2$，其中本位序 $J_f=f_0+f_{13}-f_1-f_3$。因此只预测 $\kappa$ 时 minimax 选择为 $(L+U)/2$。例如 $m_1=m_3=1/4,m_2=0$，最大熵选 $1/16$，minimax 选 $1/8$；前者是完成准则，后者是指定损失下的最坏情形准则，均不证明真实来源已被观测。

### 3.2 许可的经典操作与曲率

**命题 3.4（遗漏关系的明确未来读口）。** 把置换

$$
T_2:000\leftrightarrow010,\qquad100,001,101\text{ 不变}
$$

明确列入经典菜单，并将分布按该置换推前，则

$$
m_2^+=p_0=1-m_1-m_2-m_3+\kappa,\qquad
\kappa=m_2^+-1+m_1+m_2+m_3.
$$

证明。$T_2$ 后中位为一的唯一原像是 $000$。故新中位均值为 $p_0$，代入引文 3.2 即得。相同当前均值而不同 $\kappa$ 的两律给不同未来读数，因而三均值的商不支持此操作的确定更新。这个经典许可不授予任何受限量子等待菜单额外控制。∎

**定理 3.5（固定 $r$ 的尖锐预测界）。** 用 $p_{\kappa_M}$ 预测命题 3.4 的未来中位，令 $\delta=\kappa-\kappa_M$。误差恰为 $\delta$，且对每个 $r\in(0,1]$ 和该剩余质量下全部相容均值，

$$
\Delta H\ge\frac8r\delta^2,\qquad
|m_2^+-\widehat m_{2,M}^+|\le\sqrt{\frac{r\Delta H}{8}}.
$$

系数 $8/r$ 在固定 $r$ 的这整个类上不能统一增大。

证明。误差由命题 3.4 相减得到。单点纤维上 $\delta=0$，两边皆零。非单点时 $0<m_1,m_3<r$。乘积四格

$$
(r-m_1)(r-m_3)/r,\quad m_1(r-m_3)/r,\quad
m_3(r-m_1)/r,\quad m_1m_3/r
$$

全正，所以 $\kappa_M$ 严格位于 $(L,U)$。在此开区间令

$$
\chi(\kappa)=\ln\frac{p_0p_{13}}{p_1p_3},\qquad
H'(\kappa)=-\chi(\kappa),\qquad
\chi'(\kappa)=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}.
$$

导数中常数项相消，因为概率方向和为零；$p_2=m_2$ 不变。四个可变概率之和为 $r$，Cauchy–Schwarz 给 $\chi'\ge16/r$，而乘积点满足 $\chi(\kappa_M)=0$。若 $\kappa>\kappa_M$，

$$
\Delta H=\int_{\kappa_M}^{\kappa}\chi(t)\,dt
\ge\int_{\kappa_M}^{\kappa}\frac{16}{r}(t-\kappa_M)\,dt
=\frac8r(\kappa-\kappa_M)^2.
$$

若 $\kappa<\kappa_M$，$\chi(t)=-\int_t^{\kappa_M}\chi'(s)\,ds\le-(16/r)(\kappa_M-t)$，故

$$
\Delta H=-\int_{\kappa}^{\kappa_M}\chi(t)\,dt
\ge\frac8r(\kappa-\kappa_M)^2.
$$

端点通过 $-t\ln t$ 在 $t=0$ 的连续延拓取得，无需在端点计算 $\chi$。固定 $r$，取 $m_1=m_3=r/2$。此时 $\kappa_M=r/4$，四格皆 $r/4$，$H'(\kappa_M)=0$，$-H''(\kappa_M)=16/r$。Taylor 公式给非零 $\delta\to0$ 时

$$
\frac{\Delta H}{\delta^2}\longrightarrow\frac8r,
$$

所以任何更大统一系数均失败。开区间含这些小偏移，锐性不靠不可行扰动。∎

若以 bit 计熵，下界为 $8\delta^2/(r\ln2)$，误差上界为 $\sqrt{r(\ln2)\Delta H_2/8}$。$r=0$ 时误差为零，不能代入含 $1/r$ 的式子。$m_2=0$ 时上述证明在四格支撑面进行，未调用要求五概率皆正的 `openSimplex` 图。严格五概率正时，$\chi$ 就是 [T] `hiddenChi`，沿 $\nu=(1,-1,0,-1,1)$ 的 Fisher 二次量为

$$
g_p(\nu,\nu)=\sum_s\frac{\nu_s^2}{p_s}=\chi'(\kappa).
$$

在 $p_2=0$ 的支撑面只对四个正格求和；不计算 $0/0$。$\chi$ 是经典对数交叉比，非量子相位角。该二次界是此任务的尖锐后果；一般 KL 二次估计和 Fisher 曲率本身是标准方法。

## 4. 完整 separator 的概率消费与遗漏见证

**命题 4.1（有限树窗口的概率延拓，经典供应的具体应用）。** 令非空有限树的节点为窗口 $C_i$，$V=\bigcup_i C_i$ 有限，各变量取有限非空值集。每个变量出现的节点连通。给窗口概率律 $\mu_i$，则全局联合律存在，当且仅当每条树边两侧在整个 $S_{ij}=C_i\cap C_j$ 上的联合边缘相同；成立时唯一最大熵延拓 $\mu_M$ 满足

$$
H(\mu_M)=\sum_iH(\mu_i)-\sum_{ij\in E}H(\mu_{S_{ij}}).
$$

这是 Wainwright–Jordan §2.5.2、式 (2.12)、命题 2.1 的 junction-tree 域；窗口取其 clique，允许空 separator，空赋值的概率为一。以下核证明说明此应用包括零概率和唯一最大熵，而不是把概率结论冒领为关系源码的输出。

证明。必要性由同一全局律边缘化。选根并按父先子后处理。对非根 $j$，父为 $i$，置 $S_j=C_i\cap C_j$、$B_j=C_j\setminus S_j$。若变量同时属于 $C_j$ 与此前某窗口，其出现连通性迫使它属于父，故与此前全部变量的交恰为 $S_j$。正质量 $s$ 上定义

$$
K_j(b\mid s)=\mu_j(s,b)/\mu_{S_j}(s).
$$

零质量 $s$ 上任选 $B_j$ 的概率核；有限非空变量值集保证可选，$B_j=\varnothing$ 时只有空赋值。根按 $\mu_{\rm root}$ 采样，再依次按 $K_j$ 添加新变量。每步保留旧边缘，在正 separator 上恢复 $\mu_j$；零 separator 事件实际概率为零，且其所有非负局部格也为零。因此得到所需全局律，零事件上的核选择不改变它。

链式熵给该构造的熵为 $H(\mu_{\rm root})+\sum_{j\ne\rm root}H(B_j\mid S_j)$，即所列公式。任意延拓 $\nu$ 则有

$$
H_\nu(B_j\mid\text{此前全部变量})\le H_\nu(B_j\mid S_j)
=H(\mu_j)-H(\mu_{S_j}).
$$

不等式之差是有限条件互信息：在每个正 $S_j$ 下，联合律到条件边缘乘积的 KL，其非负性和唯一等号由引文 3.3 的有限 log 不等式给出。因此总熵至多上述值。等号要求每一步在给定 $S_j$ 后新块与其余过去条件独立；在所有正概率历史上核只能是 $K_j$。从根递推，这唯一确定全局律，零历史不贡献质量，故最大熵延拓唯一。∎

**数学引文 4.2（关系版本与恢复边界）。** [T] `RunningIntersectionRecords.local_row_extends_raw_join` 取节点为这里的树、`S i=C_i`、`Value v` 为变量值集、$\Gamma_i$ 为非空局部允许关系。其 `EdgeProjectionConsistency` 要求完整交集上的投影像相等；结论是每个指定根行可延拓，绝不是全局唯一恢复。概率一致会使正支撑的完整投影像一致，因此支撑关系可应用该定理；反向关系一致不保证两份概率边缘相等。概率最大熵的唯一性也不说“任意全局来源只有一个”。

**例 4.3（两 FIB 窗口的一阶边界遗漏）。** 取 $C_U=\{1,2,3\}$、$C_V=\{1,4,3\}$，各自位序分别为 $(1,2,3)$、$(1,4,3)$，并令

$$
\mu_U=\tfrac12\delta_{000}+\tfrac12\delta_{101},\qquad
\mu_V=\tfrac12\delta_{100}+\tfrac12\delta_{001}.
$$

两窗口的三均值均为 $(1/2,0,1/2)$，但完整共同端点 $(1,3)$ 在前者总相同、后者总相反，$\kappa_U=1/2,\kappa_V=0$。同一对变量不可能有这两种不同边缘，故无全局概率延拓。两节点本来就是树，失败在完整 separator 信息，不在环路。这个例子使用两端联合边界；边界运输卷 §3 则把每个三位词当作从前二位到后二位的边，并保存两份完整二元边缘。两种切口都必须按自己的域读完整关系。

**例 4.4（环路是另一种障碍）。** 三个二元关系 $x=y$、$y=z$、$x\ne z$ 在各单变量投影上均允许 $\{0,1\}$，但前两个迫使 $x=z$，与第三个矛盾。它们的三角窗口图不满足所需运行交集树条件。不能把任意铺砌接触图直接当作这种树。

**命题 4.5（合法联合矩的完整性）。** 给有限变量集 $V$ 及非空向下闭合族 $\mathcal K\subseteq2^V$，概率 $p_B$ 定义在 $B\in\mathcal K$ 上；令 $m_A=\sum_{B\supseteq A}p_B$，特别 $m_\varnothing=1$。则对每个 $B\in\mathcal K$，

$$
p_B=\sum_{\substack{A\in\mathcal K\\A\supseteq B}}(-1)^{|A\setminus B|}m_A.
$$

证明。代入并交换有限和。固定 $p_C$ 的系数为零（若 $B\not\subseteq C$），否则为

$$
\sum_{B\subseteq A\subseteq C}(-1)^{|A\setminus B|}=(1-1)^{|C\setminus B|}.
$$

向下闭合保证该区间无遗漏；系数仅在 $C=B$ 为一。这就是有限集合的 Möbius 反演在此合法域的应用。∎

五模式取 $\mathcal K=\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\}$，得到引文 3.2 的概率反解；唯一遗漏的非平凡合法联合矩是 $\kappa=m_{\{1,3\}}$。一般 separator 无二阶充分性：在 $t\ge1$ 个二值变量上，均匀偶校验与均匀奇校验律不同，而每个真子集的边缘相同。证明是：给定 $j<t$ 位后，余下 $t-j\ge1$ 位中恰有 $2^{t-j-1}$ 种补全满足任一指定校验，故每个 $j$ 位赋值概率均为 $2^{-j}$。$t=1$ 时真子集只有空集，仍成立。

## 5. 由粗粒化恒等式产生相位塔

**定义 5.1（代数粗化合同）。** 固定整数 $q\ge2,d\ge1$。集合 $X$ 有 $\mathbb Z^d$ 作用 $\tau_v$。每个 $W$ 给非空锚点集 $P(W)\subseteq\mathbb Z^d$，满足

$$
a-b\in q\mathbb Z^d\quad(a,b\in P(W)),\qquad
P(\tau_vW)=P(W)+v.
$$

对 $a\in P(W)$ 给 $C_a(W)\in X$，满足

$$
C_b(W)=\tau_{(a-b)/q}C_a(W),\qquad
C_{a+v}(\tau_vW)=C_a(W).
\tag{5.1}
$$

除法逐坐标整除；不要求锚点填满整个陪集，也暂不假定拓扑、概率、局部可识别性或有效算法。

**定理 5.2（选择无关的相容相位）。** 令 $G_n=(\mathbb Z/q^n\mathbb Z)^d$，$n\in\mathbb N$，$G_0$ 为单点。存在映射 $\alpha_n:X\to G_n$，使任取 $a\in P(W)$ 都有

$$
\alpha_0=0,\qquad
\alpha_{n+1}(W)=[a]_{q^{n+1}}+q\alpha_n(C_aW),
$$

$$
\alpha_{n+1}(W)\bmod q^n=\alpha_n(W),\qquad
\alpha_n(\tau_vW)=\alpha_n(W)+[v]_{q^n}.
\tag{5.2}
$$

这里 $q:G_n\to G_{n+1}$ 为 $[z]\mapsto[qz]$，与整数代表选择无关。

证明。对 $n$ 同时归纳良定义性与协变性。$n=0$ 平凡。若第 $n$ 级已定义并协变，任意两个锚点给

$$
\begin{aligned}
[b]+q\alpha_n(C_bW)
&=[b]+q\alpha_n(\tau_{(a-b)/q}C_aW)\\
&=[b]+q\alpha_n(C_aW)+[a-b]\\
&=[a]+q\alpha_n(C_aW)\quad\text{于 }G_{n+1}.
\end{aligned}
$$

所以递推不依赖选择。对 $\tau_vW$ 选锚点 $a+v$，用 (5.1) 的第二式立即给新一级的协变性。每步值唯一，因而递推定义全部 $\alpha_n$，无需固定一条任意锚点选择链。

相容性另归纳：$n=0$ 的目标群是单点；若 $n\ge1$ 且前一级相容，则

$$
\begin{aligned}
\alpha_{n+1}(W)\bmod q^n
&=[a]_{q^n}+q\bigl(\alpha_n(C_aW)\bmod q^{n-1}\bigr)\\
&=[a]_{q^n}+q\alpha_{n-1}(C_aW)=\alpha_n(W).
\end{aligned}
$$

这也核对了递推、取模和乘 $q$ 的类型。∎

## 6. CLARK 注册 carrier world 的普通数学桥

### 6.1 源码域及保持合法性的具体前提

[P] 的 `RegisteredWorld d` 由 pose 集 $W.tiles$、每个整数 cell 有占有者、两个占有同一 cell 的 pose 必相等组成。`Legal L` 要求每对不同、实际有单位面接触的成员，其相对 pose `normalize p q` 属于 $L$。姿态由置换、符号和整数平移 `shift` 组成。`shift` 是 pose 的欧氏平移参数；反射 cell 的下角另有一格偏移，不可替换成 bounding-box 的左下角。

**约定 6.1（固定合法世界类）。** 取 $d\ge3$，固定如下 [P] 数据，不把它们藏进“可重复粗化”一句话：

- 角色规则 $\sigma:\mathrm{Bits}(d)\to\mathrm{Perm}(d)$，坐标置换 $\gamma$ 及 `Function.Involutive γ`、`EquivariantChildren σ γ`；此处用 $\gamma$ 避免和 §3 的剩余质量 $r$ 混淆。
- 有限 canonical 表 $\mathcal C$、接触语言 $L$，以及 `IsCanonicalTable σ C`、`GaugeClosed γ L`、每个 $k\in L$ 的 `LocalCatalogFacts σ γ k`。
- 索引 coarse 行 `rows : ρ → CoarseRow d`，每行的 `witness.Valid C L pose`；并且每个 $a,b\in\mathcal C,k\in L$，只要 `parentCandidate a b k` 的每个 shift 坐标为偶数，就等于某行的 pose。

这些正是 `RegisteredWorld.coarsen_legal` 的目录与证书前提。$X$ 取在这些固定数据下所有满足 `Legal L` 的注册 carrier world，状态只按 tile pose 集相等，不把合法性证明当作额外可观测资料。这里只在该域应用下述桥；不另行宣称任意抽象目录都存在世界。完整父块 `CompleteParent σ γ W.tiles p` 的含义是：每个 $\sigma$-child pose 都有一个在 $W$ 中的 gauge 等价成员。`GaugeRel` 只允许原 pose 或右乘 $\gamma$，保持 shift。`ParentContains` 也是通过这些 child 与 gauge 定义。

[P] `complete_parent_exists`、`unique_physical_parent`、`parent_cells_tile`、`all_parents_even` 在这些域分别供应完整父块存在、唯一物理父归属、carrier 父支撑分割及所有父锚点差为偶数。取

$$
P(W)=\{p.shift:p\text{ 是 }W\text{ 的完整父块}\}.
$$

世界覆盖任一 cell，故有 tile；父块存在给 $P(W)\ne\varnothing$。同余定理给一个 $2\mathbb Z^d$ 陪集；无需该集合包含陪集的每一点。

### 6.2 任意平移后的世界与父块

**命题 6.2（跨世界平移运输）。** 对 $v\in\mathbb Z^d$，令 $D_vp$ 保留置换、符号，将 shift 加 $v$；定义

$$
(\tau_vW).tiles=\{D_vp:p\in W.tiles\}.
$$

则它仍属约定 6.1 的 $X$，$\tau$ 为群作用，且

$$
p\text{ 完整于 }W\iff D_vp\text{ 完整于 }\tau_vW,
\qquad P(\tau_vW)=P(W)+v.
$$

`ParentContains`、物理父归属也在同时平移父与 child 时双向保持。

证明。pose 的反 cell 公式逐坐标为：若输出行 $i$ 不反射，取 $c_i-p.shift_i$；若反射，取 $p.shift_i-1-c_i$，再按置换放入对应坐标。因此

$$
(D_vp).inverseCell(c+v)=p.inverseCell(c),
$$

故 `Occupies` 及 `ParentOccupies` 同时平移不变。对 cell $c$ 先在 $W$ 覆盖 $c-v$ 再平移，得到新覆盖。若两个新 pose 占有 $c$，去平移后占有同一 $c-v$，旧 disjoint 给相等；$D_v$ 的逆是 $D_{-v}$，得到新 disjoint。

单位 cell 面邻接只由坐标差为 $\pm1$ 或零定义，故接触也双向保持。`normalize p q` 是相对刚体 pose，$p^{-1}q$ 中共同平移相消：姿态未变，相对 shift 是旧两 shift 之差经旧线性逆作用，仍完全相同。所以每个新接触的相对 pose 仍属同一个 $L$，合法性保持。逐 shift 相加给 $\tau_0W=W$、$\tau_u\tau_vW=\tau_{u+v}W$。

children 由 `centralChild p` 和 `compose p (outerPose a (σ a))` 组成。前者 shift 为 $p.shift+p.sign$，后者为 $p.shift$ 加固定姿态作用于 outer shift；故

$$
\mathrm{children}(D_vp)=D_v\bigl(\mathrm{children}(p)\bigr).
$$

gauge 只改右置换，保留 shift 和符号，因此 $\mathrm{GaugeRel}(s,t)$ 当且仅当 $\mathrm{GaugeRel}(D_vs,D_vt)$。若 $p$ 完整，把每个 child 的旧成员见证同时平移就得到 $D_vp$ 完整于新世界；反向用 $-v$。同一个见证还运输 `ParentContains`；父块物理类的双向运输由 gauge 相容性给出。对完整父 shift 取集合即得锚点等式。∎

[P] `CarrierHierarchyPeriods.CompleteParent.translate` 的原声明要求 `W.IsPeriod v`，结论仍在同一个 $W$ 中。命题 6.2 证明的是 $W\to\tau_vW$ 的普通数学桥，其证明不假设 $v$ 是周期；没有把原声明的前提删除，也没有声称这里已新增 Lean 导出。

### 6.3 实际 coarse 集合与两条恒等式

[P] 的 `coarsePose a p` 保留置换和符号，只把 shift 改为 $(p.shift-a)/2$。对 $a\in P(W)$ 定义

$$
C_a(W).tiles=
\left\{\mathrm{coarsePose}_a(\mathrm{centralParent}(t)):
 t\in W.tiles,\ \mathrm{centralParent}(t)\text{ 完整于 }W\right\}.
\tag{6.1}
$$

这恰是 `RegisteredWorld.coarsen` 的 tile 集：传入任一 shift 为 $a$ 的完整父 $p_0$，定义只消费 $p_0.shift$，不消费它的姿态。`CompleteParent.actual_center` 供应每个物理父由一个实际中心 tile 表示；因此 (6.1) 不任意同步 gauge，也不引入每层独立的代表选择。`all_parents_even` 保证集合内所有被减 shift 与 $a$ 同奇偶，除法是精确整数除法，含负坐标。

**命题 6.3（合法 coarse world 及恒等式）。** 约定 6.1 下，(6.1) 定义 $X$ 中的 world，且对 $a,b\in P(W)$、$v\in\mathbb Z^d$，

$$
C_b(W)=\tau_{(a-b)/2}C_a(W),\qquad
C_{a+v}(\tau_vW)=C_a(W).
\tag{6.2}
$$

证明。world 的覆盖与不交由 [P] `RegisteredWorld.coarsen` 供应，合法性由同一固定目录及行证书的 `RegisteredWorld.coarsen_legal` 供应；它们的全部额外前提已在约定 6.1 列出。其 `coarse_occupies_iff` 是

$$
\mathrm{Occupies}(\mathrm{coarsePose}_a p,c)
\iff\mathrm{ParentOccupies}(p,2c+a)
$$

并要求 $p.shift-a$ 各坐标偶数。这个对应在此确实可用，不把不相交 bounding box 触碰当作细 cell 面接触。

对 (6.1) 内一个父 pose，记 shift 为 $s$。换原点后姿态不变，且

$$
\frac{s-b}{2}=\frac{s-a}{2}+\frac{a-b}{2}.
$$

集合所枚举的实际中心 $t$ 和完整性条件不变，故每个元素精确变为 $D_{(a-b)/2}$ 下的像。反向换回原点给反向包含，得到第一式。

命题 6.2 使 $t\mapsto D_vt$ 成为旧、新世界成员的双射，并运输完整性；定义还给 $\mathrm{centralParent}(D_vt)=D_v\mathrm{centralParent}(t)$。于是新集合对应元素的 shift 为

$$
\frac{(s+v)-(a+v)}2=\frac{s-a}2,
$$

姿态也相同。双射给两个集合相等，得到第二式。这里 $v$ 可以是任意整数向量，两个减法先相消；没有对 $v/2$ 作未许可的取整。∎

所以约定 6.1 的合法 carrier 世界类满足定义 5.1，取 $q=2$。这不是把父块 carrier 当作物理 keyed body 的同位似剖分：[P] `CarrierHierarchyCells.DoubleCell` 是 doubled undecorated chair 的单位 cell 支撑；`centralChild` 也明确是该未装饰父构造。物理 body 的 key、几何注册、合法接触绑定分别有它们的源码接口。

### 6.4 物理 T5 端点的准确范围

[P] `Tile5Existence.T5_hasTiling` 陈述 literal unmarked $T5$ body 的实际铺砌存在；`T5Aperiodicity.T5_period_eq_zero` 的参数是任意 `IsTiling T5 tiles` 与实向量 $v\in\mathbb R^5$ 的 `IsPeriod tiles v`，结论 $v=0$。该端点允许任意欧氏等距复制，含旋转、平移和反射。`PhysicalT5PeriodComposition` 用 `T5_global_registered_frames` 及 native contact law 接到注册世界的周期定理，而不是假定物理铺砌一开始已有格点坐标。

`FiniteSymmetry.T5_symmetries_embed_signed_permutations` 在某个共同根 frame 中编码全部欧氏铺砌对称；`T5_euclidean_symmetry_card_le_3840` 给 $2^5 5!$ 上界；`T5_strong_aperiodic_bound` 合并紧致 body、存在和该有限群界。这里 strong 指该源码定义中的完整对称群有限，不指群必为平凡群。上述是固定声明及其证明体的范围核对，不是本卷重建全部 kernel 证明。

同一注册 frame 是比较相位的坐标输入。下节的整数平移结论不能单独替代该实平移端点，也不能把“有共同坐标”说成无参考系的绝对物理坐标。实际 T5 的紧致有限符号编码、相位局部识别和有效半径仍须 §12 的独立接口，不能由这里的 pose 算术自动获得。

## 7. 平移别名、非周期与完整对称

**定理 7.1（各级精确别名）。** 在定义 5.1 的域内，对 $n\ge0$、$v\in\mathbb Z^d$，

$$
\alpha_n(\tau_vx)=\alpha_n(x)\iff v\in q^n\mathbb Z^d.
$$

每个状态无非零整数平移周期；$v_n=q^ne_i$（$1\le i\le d$）在第 $0,\ldots,n$ 级均不可见，第 $n+1$ 级可见。

证明。协变性把相位相等化为有限群内 $[v]_{q^n}=0$，即逐坐标整除。若 $\tau_vx=x$，对所有 $n$ 均整除；任一非零整数坐标的绝对值小于某个 $q^n$，不可能被它整除，故 $v=0$。$q^ne_i$ 恰被前 $n$ 级模数整除而不被 $q^{n+1}$ 整除。$n=0$ 时所有平移在单点相位上别名，最后断言仍成立。∎

**推论 7.2（有限线性部分的群界）。** 对一个实际欧氏铺砌，另已知它没有非零实平移对称，且同一 frame 中所有对称的线性部分都属于有限群 $F$。则完整对称群 $G$ 满足 $|G|\le|F|$。

证明。取线性部分是群同态 $G\to F$；其核是平移对称，由前提只有恒等，故单射。若 $F$ 是五维带符号坐标置换，独立的五个符号和 $5!$ 个坐标置换给 $|F|=2^5 5!=3840$。∎

这里若只先取得定理 7.1 的整数非周期，尚须几何注册或另一个桥将实际平移对称送到该整数域，才能使用本推论的实平移前提。[P] 物理端点已经另行供应这一部分，§6.4 列出了准确范围。

## 8. 紧致符号实现、状态纤维与观察信息

### 8.1 独立的符号合同

**约定 8.1（拓扑输入）。** 从此取有限非空字母表 $A$，非空闭平移不变集

$$
\Omega\subseteq A^{\mathbb Z^d},\qquad
(\tau_vx)(u)=x(u-v).
$$

各 $\alpha_n:\Omega\to G_n$ 满足 (5.2)，且有非负整数半径 $R_n$ 和局部 decoder

$$
\alpha_n(x)=h_n(x|_{B_{R_n}}),\qquad B_R=\{u:\|u\|_\infty\le R\}.
$$

decoder 只需定义在实际达到的图案上；可取 $R_0=0$。该条件可以通过一个与 §5 系统平移相容的编码供应，也可以独立作为相位系统假设；没有在这里断言实际 CLARK 已满足它。

有限离散字母表的可数乘积紧致，闭子集 $\Omega$ 紧致。直接的序列说明是：对越来越大的有限窗口逐次选取图案恒定子列，再作对角选择，得到逐坐标收敛子列，闭性保留极限。局部公式使每个 $\alpha_n$ 连续。反之若已知有限值 $\alpha_n$ 连续，紧致性给有限个局部常值柱集的覆盖，取覆盖所用窗口的并，包含于某个 $B_R$，即得到有限半径；这只是存在性，不给有效半径或程序。

**定理 8.2（满射逆极限因子）。** 定义

$$
\mathbb Z_q^d=\varprojlim_{n\ge0}G_n
=\{(a_n):a_{n+1}\bmod q^n=a_n\}.
$$

则 $\alpha_\infty(x)=(\alpha_n(x))_n$ 连续、满射，满足 $\alpha_\infty(\tau_vx)=\alpha_\infty(x)+v$，整数按所有剩余类嵌入。这里不要求 $q$ 是素数。

证明。相容性使像落在逆极限，逐坐标连续及协变给前后两性质。固定 $x_0\in\Omega$，$\alpha_n(\tau_vx_0)=\alpha_n(x_0)+[v]$ 遍历 $G_n$，故每级满射。对任意相容串 $a$，令 $F_n=\{x:\alpha_n(x)=a_n\}$。它们非空闭且递减，紧性给共同点，该点映到 $a$。∎

紧性不能从最后一步删除。例取 $X=\mathbb Z^d$、$\tau_vx=x+v$、$\alpha_n(x)=[x]_{q^n}$，每级满射且相容，但整数的像可数，逆极限不可数：每个坐标有任意 $q$ 进制数字串，前缀是有限剩余类，得到至少 $\{0,1\}^{\mathbb N}$ 那么多个相位。因此整数轨道不是满射模型；它在逆极限中稠密而不紧。

### 8.2 全相位仍合并状态

**定理 8.3（至少一个非单点纤维）。** 约定 8.1 下，$\alpha_\infty$ 不可能单射。

证明。若单射，定理 8.2 使它成为紧空间到 Hausdorff 空间的连续双射，故逆连续。于是

$$
f:\mathbb Z_q^d\to A,\qquad f(a)=\bigl(\alpha_\infty^{-1}(a)\bigr)(0)
$$

是有限值连续函数。每个点都有某个有限级圆柱邻域使 $f$ 恒定；取有限子覆盖，并取所用级数的最大值 $N$。若两个相位模 $q^N$ 相同，任取包含前者的覆盖柱集，后者也在其中，故函数值相同。因此 $f$ 只依赖第 $N$ 级。由作用的符号约定，$x(u)=(\tau_{-u}x)(0)$，所以

$$
x(u)=f(\alpha_\infty(x)-u).
$$

将 $u$ 改成 $u+q^Ne_1$ 不改变有限级相位，得每个 $x$ 有非零周期 $q^Ne_1$，与定理 7.1 矛盾。$N=0$ 时函数为常值，得到周期 $e_1$，同样矛盾。∎

结论只保证至少一个非单点纤维，没有证明每个纤维都非单点。若需一个纤维处处扩大的条件例，取

$$
\Omega'=\Omega\times\{0,1\}^{\mathbb Z^d}
\subseteq(A\times\{0,1\})^{\mathbb Z^d},
$$

用对角平移、相位只读取第一分量。它仍非空、闭、有限字母表且局部解码；每个已达到相位的纤维包含一整份二值 full shift。第二分量因此不能被这些相位恢复。

与此不同，若当前读出是原点符号、菜单允许全部平移，则完整 profile 为

$$
v\longmapsto(\tau_vx)(0)=x(-v).
$$

任意 $u$ 取 $v=-u$ 就得到 $x(u)$，所以该 profile 单射。完整相位与完整符号 profile 是不同观察族。

### 8.3 未来充分性与尺度信息

**命题 8.4（固定级数的未来闭合）。** 固定 $n$，只允许平移、只读 $\alpha_n$，则

$$
\bigl[\forall v,\alpha_n(\tau_vx)=\alpha_n(\tau_vy)\bigr]
\iff\alpha_n(x)=\alpha_n(y).
$$

证明。必要性取 $v=0$，充分性在共同初始相位上加 $[v]$。更新 $a\mapsto a+[v]$ 已完全由相位决定，故该相位就是本菜单的完整未来充分摘要。若动作按以往输出自适应选择，同相位初始值产生相同历史，策略就选相同动作，归纳给每一步相同输出；带共同随机种子的策略也可逐种子用此归纳。它不会自动取得高一级相位。∎

**命题 8.5（每级真正的新读出）。** 每个 $\alpha_n$ 纤维内，$\alpha_{n+1}$ 取遍粗相位的全部 $q^d$ 个提升。因此它不是 $\alpha_n$ 的函数；若 $(\alpha_n,r')$ 精确恢复 $\alpha_{n+1}$，$r'$ 在每个粗纤维至少取 $q^d$ 个不同值。固定宽度二进制编码 $\alpha_n$ 至少需 $\lceil nd\log_2q\rceil$ 位。

证明。$\alpha_{n+1}$ 满射，实现每个细相位；相容性使这些实现都位于指定粗纤维。不同细相位若有相同附加读出，引文 2.1 的纤维条件就失败。最后 $|G_n|=q^{nd}$，$b$ 位至多有 $2^b$ 个码，故 $b\ge\lceil\log_2|G_n|\rceil$。$n=0$ 给零位，仍有 $q^d$ 个第一级提升。∎

**约定 8.6（统计输入）。** 另给 $\Omega$ 上的平移不变 Borel 概率 $\mu$。以下不需要遍历性，但不把尚未绑定到具体物理 world 类的概率选择当作它的天然物理测度。

**命题 8.7（尺度熵与固定分辨率历史熵）。** 在约定 8.6 下，有限相位均匀，且对 $T\in\mathbb N$、$v\in\mathbb Z^d$，

$$
H_2(\alpha_n)=nd\log_2q,\qquad
H_2(\alpha_{n+1}\mid\alpha_n)=d\log_2q,
$$

$$
H_2\bigl(\alpha_n(x),\alpha_n(\tau_vx),\ldots,\alpha_n(\tau_{Tv}x)\bigr)
=nd\log_2q.
$$

证明。对任意两相位选 $v$ 使其差为 $[v]$；协变性和测度不变性使两个原子的概率相同，总和为一，故每个为 $q^{-nd}$。均匀熵给第一式。细相位决定粗相位，链式熵的差给条件熵。历史向量由初始相位确定且包含该相位，因此二者互相确定，熵相等。∎

条件性的 $q=2,d=5$ 模型每级增加 5 bit，第 $n$ 级为 $5n$ bit。这是观察分辨率的信息量，不是每个时间步产生 5 bit，也不是单位空间体积的熵率。世界可以固定而观察划分变细。

## 9. 相位因子的字符与平移谱

继续采用约定 8.1、8.6。在复 $L^2(\Omega,\mu)$ 中取内积 $\langle f,g\rangle=\int\overline f g\,d\mu$，定义 $U_vf=f\circ\tau_v$。对 $k\in G_n$ 置

$$
\chi_{n,k}(x)=\exp\left(\frac{2\pi i}{q^n}\,k\cdot\alpha_n(x)\right).
$$

改变任一整数代表使指数只增 $2\pi i$ 的整数倍，故定义无歧义。$n=0$ 时只有常数字符一。

**定理 9.1（精确本征关系与所覆盖的空间）。** 每个 $U_v$ 酉，且

$$
U_v\chi_{n,k}=e^{2\pi i k\cdot v/q^n}\chi_{n,k}.
\tag{9.1}
$$

同一级的 $q^{nd}$ 个字符是全部 $\alpha_n$ 可测函数的正交标准基。令 $\mathcal H_n$ 为该有限维子空间，则

$$
\overline{\bigcup_n\mathcal H_n}
=L^2\bigl(\Omega,\sigma(\alpha_\infty),\mu\bigr),
\tag{9.2}
$$

右侧按零测集完成；等式不声称它是整个 $L^2(\Omega,\mu)$。

证明。$\tau_v$ 可逆且保测，故保持范数并以 $U_{-v}$ 为逆。协变性代入指数给 (9.1) 的正号；这是 $U_v=f\circ\tau_v$ 的约定所决定的。相位均匀给

$$
\langle\chi_{n,k},\chi_{n,\ell}\rangle
=q^{-nd}\sum_{a\in G_n}e^{2\pi i(\ell-k)\cdot a/q^n}
=\mathbf1_{k=\ell}.
$$

该和分解为 $d$ 个有限几何级数：非平凡根的和为零，平凡根的和为 $q^n$。每个相位原子正质量，$\mathcal H_n$ 的维数正是 $|G_n|$，得到标准基。相容性给 $\mathcal H_n\subseteq\mathcal H_{n+1}$；相应字符也可能重复，具体 $\chi_{n,k}=\chi_{n+1,qk}$，不把各级并集算成互不相交的基。

为证明闭包，设 $\mathcal H$ 为左侧。有限级圆柱集合的指示函数在 $\mathcal H$ 中；这些圆柱集合的并族因级数嵌套而构成代数，生成 $\sigma(\alpha_\infty)$。指标在 $\mathcal H$ 内的集合类包含此代数，且对递增或递减集合列封闭：其指标由有限测度的连续性在 $L^2$ 收敛，$\mathcal H$ 闭。单调类定理于是包含全部生成的可测集；按值截断并划分值域，可测 $L^2$ 函数由有限简单函数在 $L^2$ 中逼近。因此右侧包含于 $\mathcal H$。反向每个有限级函数都可测于该 sigma 代数，该可测子空间在 $L^2$ 中闭（收敛子列几乎处处收敛即可），故包含整个 $\mathcal H$。零测集完成不改变 $L^2$ 等价类。∎

对整数时间 $t$，

$$
\chi_{n,k}(\tau_{tv}x)=e^{2\pi i t k\cdot v/q^n}\chi_{n,k}(x).
$$

单个模式可有精确周期，而完整符号配置仍无非零平移周期。有限字符及其极限闭包使相位因子具有纯点平移谱；这里没有证明整个系统纯点谱，也未证明这是最大等连续因子。概率输入是 $\mu$，并无 Born 规则或连续物理时间；整数平移酉表示不唯一确定一个连续时间生成元。

## 10. 有限窗口证书与两种接近

**定理 10.1（排除有界候选周期的局部证书）。** 若 $n\ge0$、$0<\|v\|_\infty<q^n$，则对所有 $x\in\Omega$，

$$
x|_{B_{R_n}}\ne(\tau_vx)|_{B_{R_n}}.
$$

给整数 $K\ge0$，取 $n=\lceil\log_q(K+1)\rceil$，便排除所有 $0<\|v\|_\infty\le K$。若另有 $R_n\le Cq^n$（$C\ge0$），两个待比较窗口各自半径至多 $Cq(K+1)$；若仅允许读取一个以原点为中心的窗口，半径 $R_n+K$ 足够。

证明。相同图案经同一个 decoder 得相同相位，由定理 7.1 迫使 $v\in q^n\mathbb Z^d$。这样的非零向量范数至少 $q^n$，矛盾。所选 $n$ 满足

$$
K+1\le q^n<q(K+1).
$$

$K=0$ 时 $n=0$，候选集为空，断言无须检查一个非零向量；可用常数相位的 $R_0=0$。平移图案在 $B_{R_n}$ 的数据等于原配置在 $B_{R_n}-v$ 的数据，两个集合都包含在 $B_{R_n+K}$，故一窗口界成立。∎

若另证识别递推 $R_{n+1}\le qR_n+B$、$B\ge0$，归纳得到

$$
R_n\le q^nR_0+B\frac{q^n-1}{q-1}
\le\left(R_0+\frac B{q-1}\right)q^n.
$$

归纳步是将前式乘 $q$ 再加 $B$，几何和增加最后一项；$n=0$ 为等号。这说明一个明确识别合同如何供应定理的 $C$，而不是对实际 CLARK 的半径宣告。相位输出仅 $O(n)$ bit，但显式读取 $B_{R_n}$ 有 $(2R_n+1)^d$ 个符号；朴素两个窗口或共同窗口的取得成本按体积及每符号读费计算。在固定 $d,q,C$ 的该上界下，可达 $O((K+1)^d)$ 个读取，而 $K$ 的二进制长度仅 $O(\log(K+2))$；这个朴素上界对该长度是指数级，不是对任意 decoder 的下界。逐个检查全部候选向量另有至多 $(2K+1)^d-1$ 次比较，不能只按输出位数计总费。

**定理 10.2（紧性本身给出的统一有限见证）。** 不用相位，任意非空紧致平移不变有限字母表空间及非零整数 $v$ 都有

$$
\operatorname{Fix}_\Omega(\tau_v)=\varnothing
\iff\exists R\ge0\ \forall x\in\Omega\ \exists u\in B_R:\ x(u)\ne x(u-v).
$$

证明。右侧排除不动点。反向令 $D_R=\{x:\exists u\in B_R,x(u)\ne x(u-v)\}$。这是递增开集列；无不动点即它们覆盖 $\Omega$。紧性给有限子覆盖，取最大半径即可。证书涉及的两个位置都在 $B_{R+\|v\|_\infty}$，若只允许单窗口，须读取这一范围。∎

这个紧性证明不提供寻找 $R$ 的有效程序，更不提供复杂度界。若先验比较类已经只含非周期配置，目标“是否非周期”在其中是常值一，可从任何观察恢复。讨论无此先验时有限样本能否认证，必须先给更大的比较类、证书规则及允许的读取；不能从上述常值问题制造不可恢复性。

**定理 10.3（相位超伪距离与符号一致拓扑）。** 令

$$
N(x,y)=\sup\{n\ge0:\alpha_n(x)=\alpha_n(y)\},\qquad
 d_H(x,y)=q^{-N(x,y)},\quad q^{-\infty}=0.
$$

它是超伪距离。对 $n\ge0,1\le i\le d$，

$$
d_H(x,\tau_{q^ne_i}x)=q^{-n}.
$$

在完整符号距离

$$
\rho(x,y)=2^{-\min\{\|u\|_\infty:x(u)\ne y(u)\}},\qquad\rho(x,x)=0
$$

中，对每个非零整数 $v$ 有

$$
\sup_{x\in\Omega}\rho(\tau_vx,x)=1.
$$

证明。第零级总相等，故 $N$ 的集合非空；相容性使它是初段。若 $x,y$ 和 $y,z$ 共享前 $n$ 级，$x,z$ 也共享，故 $N(x,z)\ge\min(N(x,y),N(y,z))$，即超度量不等式；对称性和对角零显然。不同状态同完整相位可距离零，由定理 8.3 确有这种可能，所以只称伪距离。定理 7.1 给指定平移前 $n$ 级相等、第 $n+1$ 级不同，得到精确值。

符号距离中任一不同对的差异坐标范数是非负整数，最小值存在，距离不超过一。任取 $x\in\Omega$，定理 7.1 排除周期 $v$，故有 $u$ 使 $x(u)\ne x(u-v)$。令 $y=\tau_{-u}x\in\Omega$，则 $y(0)=x(u)$、$(\tau_vy)(0)=x(u-v)$，差异在原点，距离为一，达到上确界。∎

所以 $q^ne_i$ 在相位观察几何中趋于零，但在完整符号空间上相应平移不一致趋于恒等。这里未排除某些状态的逐点收敛，也未把一致位移范数冒作强算子收敛的结论。[T] 相容预测波卷定理 22.2 在同一个有限维复 Hilbert 空间上，给定包含已校准相位的精确二分 $U_{n+1}^2=U_n$ 与相同时间单位后，还需 $U_n\to I$ 才得到连续生成元；定理 22.4 的近似版本则另要求加权可求和的细分误差。空间相位细化不自动供应这些前提。

## 11. 有限消息、数量目标与付清的编译

### 11.1 裸局部合法性与给定分解的算法

**例 11.1（局部 FIB 不强制层级）。** 双无限二值链每个连续三窗口都属于 $\Sigma$，等价于没有相邻的两个一。一个方向由允许五词逐项检查；另一个方向枚举三个二值位置，没有相邻一的恰为这五词。全零链与交替链 $1010\cdots$ 因而都合法，分别有周期一和二。无限层级须有额外的规则与证明。

**命题 11.2（有限、显式且给定树袋的消息算法）。** 给显式有限变量集 $V$、大小 $a\ge1$ 的有限非空值域、$m\ge0$ 个有限关系约束，以及非空树上的 $b\ge1$ 个袋 $C_i$，满足：袋覆盖 $V$；每变量的出现节点连通；每个约束的整个支撑包含于某袋；$|C_i|\le w+1$，$w\ge0$。关系表示、变量编码和树袋均计入输入位长度 $N$，局部判定、投影和表访问的成本都收费。则可以确定全局可满足性，并在可满足时输出一个全局赋值。

在已建好索引、可直接访问的有限表模型上，袋赋值枚举、约束测试与分隔消息需

$$
O\bigl((b+m)a^{w+1}\operatorname{poly}(w+1,\log(a+1))\bigr)
\tag{11.1}
$$

次有界字操作，乘以实际声明的局部判定/查表成本，另加输入读取、索引构建和分解取得成本。不是给任意长名称或整数免费常数成本。在顺序位机上也可得到

$$
O\bigl((b+m)a^{w+1}\operatorname{poly}(N,(w+1)\log(a+1))\bigr)
\tag{11.2}
$$

的保守位时间界，局部测试程序的实际位成本另乘；若本来按显式列表逐项查表，其总长度已在 $N$ 内。

证明。选根，给每约束指定一个包含其完整支撑的归属袋，先核验这些有限结构条件。对非根袋 $j$，父为 $i$，记 $S_j=C_j\cap C_i$。枚举本袋所有 $a^{|C_j|}$ 个赋值 $t$，保留满足归属约束、且对每个子袋 $h$ 都有 $t|_{S_h}\in M_h$ 的赋值，投影到 $S_j$ 得 $M_j$。根不再投影，只检查保留集是否非空。

消息不变量为：$s\in M_j$ 当且仅当 $j$ 的整个子树中存在一个满足所有归属约束的赋值，边界为 $s$。叶子由定义成立。归纳步的必要性是限制任一子树解；充分性选择各子消息的延拓，并与当前袋赋值合并。不同子树间共同变量，或子树与当前袋外部的共同变量，因出现节点连通而必须位于对应的 separator；因此所选赋值在每个共同变量上相容。合并给子树解，证明不变量。根的非空性遂等价于全局可满足。为每个保留消息存一个达到它的袋赋值，根选一行再自顶向下取这些见证，得到一致的全局赋值。

袋枚举总数不超过 $ba^{w+1}$。每条子边在其父袋每行做一次完整 separator 测试，树边共 $b-1$；每个约束只归属一次，每次测试至多涉及其袋的赋值，故总测试数不超过 $(b+m)a^{w+1}$ 的常数倍。投影和赋值编码需 $\operatorname{poly}(w+1,\log(a+1))$ 工作，给 (11.1)。索引和地址位长包括 $O((w+1)\log(a+1)+\log(N+2))$，这些字并非任意精度免费整数。

在位机上，可把每条边的父袋候选行按该 separator 码排序，与子消息的排序列表归并；每个列表至多 $a^{w+1}$ 行，比较码和记录长为所列参数的多项式，排序的 $\log(a^{w+1}+1)$ 因子也包含其中。约束列表查找可逐表扫描，或收费建立相应索引。每袋、每边、每约束只做上述有限次数的批处理，给 (11.2)。回取见证用已存父索引或按层扫描，至多另乘输入长度的多项式，仍在此界的多项式因子内。空变量集时所有袋可为空，仅有常数约束，空赋值直接测试；无约束时任意赋值通过；空 separator 只有一行。∎

此机制复用 Dechter 文献注的 frontier 消元与完整记录原则，树袋上的归纳写清了其接口。[T] `RunningIntersectionMessages.raw_join_nonempty_iff_root` 的 `Γ i` 在此取袋上满足归属约束的行集、`S i=C_i`、值域取给定字母表，消息是同一子树投影关系。原声明允许无限关系和值类型，且 `separatorMessages` 是 `noncomputable` 集合定义；(11.1)–(11.2) 依赖本节新增的有限表示与实际操作成本，不能从原声明直接读出。

固定 $a$，若总输入长度、分解大小与取得分解的成本皆为原实例长度的多项式，局部检查也多项式，且 $w=O(\log(N+2))$，则上界为多项式。字母表变化时还需控制 $(w+1)\log a$；仅报“宽度小”不够。关系表很长、分解难取得或解码很贵，都不能藏在袋数中。

### 11.2 精确的 FIB 数量目标与一次计分

**命题 11.3（共享 FIB 的独立集对应）。** 给有限简单图 $G=(V,E)$ 和整数阈值 $k$。每个顶点有二值变量 $x_v$；为每条边 $e=\{u,v\}$ 增加 $z_e$，约束为

$$
z_e=0,\qquad (x_u,x_v,z_e)\in\Sigma,
\qquad \sum_{v\in V}x_v\ge k.
\tag{11.3}
$$

三元组按物理首—中—末顺序排列，故被固定的是物理第三槽。系统有解当且仅当图有至少 $k$ 个顶点的独立集。这一带数量目标的实例族是 NP 完全的；删除数量目标后，全零赋值总是解。

证明。第三槽为零时允许词恰是 $000,100,010$，所以每条边禁止 $x_u=x_v=1$。取值一的顶点构成独立集，其大小就是总和；反向由独立集令对应位为一、所有 $z_e=0$，满足全部约束。构造与验证皆为输入长度的多项式。$k\le0$ 时空集已满足，$k>|V|$ 时不可能，$V=\varnothing$ 也由这两条件完全处理。

Karp 原文 §4 定义 5、Main Theorem 的第 5 项 NODE COVER，供应“是否有大小至多 $\ell$ 的顶点覆盖”为 NP 完全问题。这里使用顶点集合的补集：$R\subseteq V$ 覆盖每条边，当且仅当 $V\setminus R$ 独立，因为一条边两端均在补集内正是覆盖失败。于是

$$
|R|\le\ell\iff |V\setminus R|\ge |V|-\ell.
$$

将 $k=|V|-\ell$ 再用上述编码，是多项式归约；阈值越界按前段处理。一个 $V$ 上的二值见证和确定的零辅助变量可多项式核验，故该语言在 NP 中并为 NP 困难。原文印刷页 98 的 CLIQUE 到 NODE COVER 另取图补 $G'=\overline G$ 和 $\ell=|V|-k$：$S$ 在 $G$ 为 clique 当且仅当在 $G'$ 为独立集，再由上述顶点补集得到覆盖。这里直接从同一图的覆盖到独立集取顶点补集；图补、顶点补集和语言补集不是同一个运算。∎

选择项演算 §15 的同类共享网络采用代数槽 $(x,y,z)=(u_v,0,u_{v'})$。按表 1 换到物理槽就是 $(u_v,u_{v'},0)$，与 (11.3) 一致。若把零放入物理中槽 $(x_u,0,x_v)$，$101$ 合法，便不禁止相邻两顶点同选，不能用于该归约。任意共享、零端口和数量目标都是明确输入能力，不从裸相邻三窗口链自动取得。

**命题 11.4（树袋的数量消息）。** 对 (11.3) 的局部约束部分，若给命题 11.2 的树袋分解，则全局数量阈值可用相同 separator 的 max-sum 消息处理，无需把整个求和支撑塞进一个袋。每个原顶点只计一次；辅助 $z_e$ 不计分。

证明。为每个原顶点 $v$ 指定一个含它的归属袋 $o(v)$，定义本袋得分

$$
g_j(t)=\sum_{v:o(v)=j}t(v).
$$

对非根袋 $j$ 和父 separator 赋值 $s$ 定义

$$
D_j(s)=\max_{\substack{t:C_j\to\{0,1\}\\t|_{S_j}=s,\ t\text{ 满足归属局部约束}}}
\left[g_j(t)+\sum_{h\text{ 子袋}}D_h(t|_{S_h})\right],
\tag{11.4}
$$

无可行候选时为 $-\infty$，任一 $-\infty$ 加数使整行不可行。根对无父限制的同式取最大。其不变量是：$D_j(s)$ 等于边界为 $s$ 的子树解中，归属袋在该子树的原顶点总得分的最大值。叶子按定义成立。一般步由命题 11.2 的合并论证，子解的兼容性只依赖完整 separator；归属将全部计分顶点分成不交部分，所以分数相加不重不漏。任意子树解限制成这些候选，反向任何相容候选可合并，最大值的两方向均成立。根得到全局独立集最大大小，与 $k$ 比较即决定目标；存达到最大值的行可回取实际独立集。

有限分数在 $[0,|V|]$，使用 $O(\log(|V|+2))$ 位和一个不可行标记即可。每行对子消息求和及比较须付相应位成本；消息行数不超过可行性算法的行数，增加的计数、加法和比较成本是多项式。空图的根分数为零，负阈值或过大阈值亦照常决定。该构造是 Dechter 文献注 §6 已有“一次插入／一次计分、忘掉内部赋值但保留最大得分”的树袋适配。∎

**推论 11.5（统一付费编译的条件后果）。** 假设有一个固定确定性算法，对所有 (11.3) 实例按其输入位长度 $N_0$ 在多项式时间内，输出等价可满足性实例及其树袋分解，并满足：输出总规模是 $\operatorname{poly}(N_0)$，字母表为常数，局部检查成本多项式，袋宽 $O(\log(N_0+2))$。则 $P=NP$。若输出保留数量目标，另须其目标有命题 11.4 这种付费多项式消息实现；不是只保留一个难解的全局黑盒。

证明。运行该编译器，再对输出运行命题 11.2 的算法，或局部部分加命题 11.4 的数量算法。输出规模多项式且 $a^{O(\log N_0)}$ 多项式，取得及解码的成本也已在前提内，故得到该 NP 完全语言的确定性多项式决定器。命题 11.3 的归约与 Karp 完全性于是给 NP 的每个语言都有多项式决定器；$P\subseteq NP$ 恒成立，故相等。∎

这个推论不声称编译器存在。仅有“每个 YES 实例存在某个好结构”，不能决定 NO；即便每个实例都有合适结构，若没有统一的收费取得算法，也不满足前提。选择项演算 §§20–26 和 Rutten 文献注 §7 分别区分辅助传播、选择、共同来源读口及终端完成，正适用于此处：静态表示含答案，不等于已取得答案。

## 12. 三条连接及实际实现的剩余接口

在固定共同来源与操作合同下，本文有三条可组合的链。

1. 五模式的闭纤维遗漏 $\kappa$；经典 $T_2$ 把它送入未来中位，完整端点 separator 也消费它。既有 Markov 完成提供预测值，定理 3.5 把其熵损失转为尖锐误差界。最大熵是选择，真实关系仍须观察。
2. 同余父锚点、合法粗化及两条恒等式产生选择无关相位；各级保留精确平移别名，全部级数排除整数周期。§6 的注册 carrier 运输桥满足代数合同，并保持其具体目录和证书前提。
3. 独立的紧致局部符号实现把相位变成满射逆极限因子；统计合同供应均匀相位和精确字符波模。完整相位仍不能恢复全部符号状态；固定级数的未来闭合也不免费获得下一分辨率或付费算法。

**实际 CLARK 的接口清单。** 下表区分已给的普通桥、固定源码供应和仍待具体绑定的实现；“待绑定”不是把条件结论结算为实际 CLARK 结论。

| 接口 | 当前数学结论与尚需的对象 |
| --- | --- |
| 合法注册 world 与锚点平移 | 在约定 6.1 的具体目录、gauge 和 coarse 行证书前提下，命题 6.2 已证明跨 world 合法性、child/gauge/完整父双向运输；物理到注册 frame 的来源另为 §6.4，不声称新 Lean 导出 |
| 两条 coarse 恒等式 | 命题 6.3 对源码实际中心 tile 的 image-set 定义已证明换原点和共同平移等式，$q=2$；除法只在已对齐整数上使用，未把 carrier 当作 keyed body 的同位似剖分 |
| 有限字母表与闭编码 | 仍需给目标 world 类到有限姿态／有界胞腔偏移字母表的明确映射，证明平移相容、图案一致性、所保留 gauge 信息、像的闭性及反向合法 world 重建；有限姿态数量本身不证明这些条件 |
| 相位局部识别与半径 | 仍需在该编码上证明每级相位由有限窗口决定；数值界如 $R_{n+1}\le2R_n+B$ 还需独立证据。全局唯一父归属不自动给局部 decoder 或有效半径 |
| 不变概率 | 统计与 $L^2$ 结论须指定该符号空间上的不变 Borel 概率及其与所比较对象的关系；均匀有限相位不选择完整状态纤维中的条件律，也不供应物理概率解释 |
| 有效、付费解码与结构取得 | 仍需算法、输入编码、有限图案合法性判定、读费／位费、半径取得和分解取得合同；连续局部函数的存在、紧性见证及非计算集合消息均不能替代它们 |

因此，实际物理 T5 的存在、实平移非周期与 3840 上界是各自固定源码端点；本文条件符号结论及其有限窗口成本以表中未绑定接口为界。它们不重开既有供应者的结论，也不把尚无具体模型的假设说成已完成的实例化。

## 13. 固定引用

下列地址中的提交号是来源版本，非本卷的形式核验声明。

- **[T] 项目形式接口**，`194597016233d92b0d42fe93e8cda55f2f6ea471`：[TargetRecoveryCriterion](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)、[ControlQuotientUniversalMinimality](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality.lean)、[MinimalPredictiveCompletionQuotient](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient.lean)、[RunningIntersectionRecords](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean)、[RunningIntersectionMessages](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages.lean)、[FiveModeMixedCoordinates](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates.lean)、[FiveModeDensityFiber](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/D5/S3/Quantum/Fibers/FiveModeDensityFiber.lean)。量子模块的 `means` 顺序由其定义体而非名称猜测。
- **[B] 项目理论供应**，共同快照 [e28e989d0a9315863d002ca75f78050985bdedc7](https://github.com/the-omega-institute/trureturing/tree/e28e989d0a9315863d002ca75f78050985bdedc7)：表 1 所列基础公式、局部重建、边界运输、选择项演算及文献注，具体条款在正文标明。[T 的 Omega 静态相容纤维理论](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md) §§1、3–5 提供对象和表示范围；[T 的相容预测波与关系谱](https://github.com/the-omega-institute/trureturing/blob/194597016233d92b0d42fe93e8cda55f2f6ea471/docs/develop/theory/AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md) §§19、21–23 提供观察未来及另附连续性条件的极限比较。
- **[P] Palomar 注册世界与父块**，`5f5ceedee770b76c21e8f1105e5e4e3b84b8d676`：[CarrierHierarchyCharts](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyCharts.lean)、[CarrierHierarchyCells](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyCells.lean)、[CarrierHierarchyParent](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyParent.lean)、[CarrierHierarchyPartition](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyPartition.lean)、[CarrierHierarchyCoset](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyCoset.lean)。
- **[P] 粗化及周期**：[CarrierHierarchyCoarsening](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyCoarsening.lean)、[CarrierHierarchyCoarseWorldLaw](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyCoarseWorldLaw.lean)、[CarrierHierarchyPeriods](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/CarrierHierarchyPeriods.lean)。
- **[P] 实际物理端点**：[Tile5Existence](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/Tile5Existence.lean)、[T5Monotile](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/T5Monotile.lean)、[T5Aperiodicity](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/T5Aperiodicity.lean)、[PhysicalT5PeriodComposition](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/PhysicalT5PeriodComposition.lean)、[FiniteSymmetry](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/SparseMonotiles/FiniteSymmetry.lean)。注册及 carrier 世界不因此获得本文未绑定的符号与有效接口。
- **经典概率与消元**：Martin J. Wainwright、Michael I. Jordan，*Graphical Models, Exponential Families, and Variational Inference*，[作者原文](https://people.eecs.berkeley.edu/~jordan/papers/wainwright-jordan-fnt.pdf)，§2.5.2、式 (2.12)、命题 2.1，印刷页 32–33；互信息式 (4.13)、KL 式 (5.9)。Rina Dechter，*Bucket Elimination: A Unifying Framework for Probabilistic Inference*，[原文](https://arxiv.org/pdf/1302.3572)，§2 及后续 width-dependent inference；本文精确 frontier、位成本和计数版本采用表 1 的仓内文献注，不把树袋宽度直接等同于原文某固定消元序的 induced width。
- **复杂度原料**：Richard M. Karp，*Reducibility Among Combinatorial Problems*，[含作者引言的原文重印](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf)，原文 §4、印刷页 93–94，定义 5、Main Theorem、第 5 项 NODE COVER，以及印刷页 98 的 CLIQUE 到 NODE COVER 补图归约。本文只借用该完全性，独立集取顶点补集及 FIB 编码见命题 11.3。
## 追加锚（本行以下为增补区）

## 14. 数量目标的原顶点参数计数与最优完成

**约定 14.1（应用的供应与完整输入）。** 本节在命题 11.3 的共享 FIB 编码上，使用[选择项演算引文 27.2、定理 27.3](AURIC_FIB_ATOM_SELECTION_CALCULUS.md) 的条件计数供应。外部来源固定为 OpenAI, [*The Exponential Time Hypothesis is False*，修订版 Theorem 1.1、Corollary 1.3](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf)；独立集的二 CNF 保计数编码已经由 Corollary 1.3 给出，自归约和 counting-to-generation 也为既有供应。本节的 `repo-derived` 项目应用是：在 (11.3) 的实际 FIB 端口上消去已知边钉值，加入确定性线性辅助结构，保持**原顶点**参数、完整计数和最优终端解码；不是重新发现一般图计数算法。

输入为显式有限简单图 $G=(V,E)$、声明的不同顶点全集 $V$、有符号二进制整数阈值 $k$，可另有显式顶点钉值。令 $v=|V|,e=|E|$，全部名称、边、顶点次序、钉值及阈值编码计入 $N$；孤立顶点保留。重复边可去重且不改变解数；按简单图语法，环、自称非顶点的端点、重复顶点声明或坏整数编码拒绝。合法但矛盾的钉值则给零解。有限小输入和 $v=0$ 在同一合同内，不从二进制整数的数值大小取得免费资源。下面以 $\rho$ 表示选择卷 (58) 的正则化尺度。

**定理 14.2（保计数、原参数及数量完成）。** 在引文 27.2 的固定三 CNF 精确计数供应前提下，存在一个统一确定性编译，将 (11.3) 及其顶点钉值、数量阈值编译为三 CNF $F_{G,k}$，满足：

1. 新声明变量数 $n'\le C(v+1)$，非平凡 $v\ge1$ 时为 $O(v)$；子句数 $O(v+e+\text{钉值条数}+1)$，规范编码及构造位成本为 $\operatorname{poly}(N)$。
2. 满足 $F_{G,k}$ 的**完整赋值**与满足原 FIB 网络和数量阈值的完整赋值双射；每个符合阈值及钉值的独立集恰贡献一，不另乘辅助线的取值数。
3. 阈值计数、判定，以及有解时原 FIB 的完整解码，在

   $$
   \operatorname{poly}(N)\,2^{O(\rho(v))}
   \tag{14.1}
   $$

   位时间、$\operatorname{poly}(N)$ 空间内完成。对未钉图，最大独立集大小、最优集数及一组最优完成也在该界内；有顶点钉值时，先判是否有相容独立集，有则同样求其约束最优值。

证明。**已知边变量先代入。** (11.3) 对每条边有 $z_e=0$，三个物理端口为 $(x_u,x_w,z_e)$。五模式在第三槽固定零时仅有 $000,100,010$，故它等价于

$$
\neg x_u\lor\neg x_w.
\tag{14.2}
$$

每个原顶点赋值的边辅助扩展都唯一为全零。编译前将这些已知位代入并删去 $e$ 个边变量，是双射的消元；解码时填回全零。不可把物理中槽固定零：那会允许 $101$，得不到 (14.2)。每条边直接输出一条二子句，不为整个边合取另建一个逐边门电路。于是即使 $e=\Theta(v^2)$，边只增加输入和子句量，不增加计数器的变量参数。

**数量比较的实际门数。** 先在读入后比较有符号 $k$ 与 $0,v$，成本按其全部位长计入 $N$。$k\le0$ 时删掉恒真阈值，仍保留所有边和顶点钉值；$k>v$ 时加入空子句使计数为零。余下仅需处理 $1\le k\le v$，常数的有效位长为 $O(\log(v+2))$。

为使 $\sum_{i=1}^v x_i\ge k$ 使用 $O(v)$ 个至多二输入确定门，采用标准 carry-save 全加器作为中间构造。把每个 $x_i$ 放在权重一的列中；只要某列有三信号 $a,b,c$，替换为该列的 $s$ 及下一列的 $t$，其中

$$
u=a\mathbin{\mathrm{xor}}b,\quad
s=u\mathbin{\mathrm{xor}}c,\quad
 t=(a\land b)\lor(u\land c),\qquad
 a+b+c=s+2t.
\tag{14.3}
$$

$x_i$ 的每次使用仍引用其同一个变量，门输出则各取一个新名字。式 (14.3) 使用两个 XOR、两个 AND、一个 OR 共五个二输入门。恒等式由 $a=b$ 与 $a\ne b$ 两种情形立即给出，因而逐赋值保持加权总和。活跃信号总数每次从三变二，故替换次数少于 $v$。更强的纯结构不变量为所有活跃信号的**权重之和**恒为 $v$：$3\cdot2^j=2^j+2^{j+1}$，所以不依赖信号取值也不可能产生权重大于 $v$ 的列。终态每列至多两信号，最高列 $O(\log(v+2))$；把它们分成两个二进制数，补零后用 ripple-carry 加法及与 $k$ 的逐位比较，再花 $O(\log(v+2))$ 门。输出为所需阈值位，总门数 $O(v)$。$v=1$ 直接比较一位；$v=0$ 已在边界分支决定。

该构造是被当前数量消费者使用的标准布尔算术，不单列为新的一般阈值电路定理。这里选择它的作用在于控制辅助变量数；例如逐项累加若给出 $O(v\log v)$ 门的实现，就不能直接声称已经得到本条的 $O(v)$ 参数。

**完整门关系和唯一扩展。** 对每个至多二输入门 $c=g(a,b)$ 使用选择卷 (61) 的禁止模式子句编译完整双向关系，作用域至多三个变量、每门至多八子句；非门亦可如此处理，常数用钉值。按门的构造次序归纳，每个原顶点赋值给所有门输出唯一值，反过来任何满足这些双向门约束的赋值必为该唯一求值。最后把阈值输出钉为一。因此正确顶点赋值有且仅有一个门扩展，错误者没有；只编码单向蕴含会失去这个结论。顶点钉值继续作单位子句，不增加变量。已消去的 $z_e$ 亦唯一填回，给两种完整解之间的双射，包含其投影多重性结论。编译只加 $O(v)$ 个门变量和常数位，给第 1 项。空子句、空边集和空顶点集无须伪造一个指数大的编码。

外部计数调用以 $n'$ 为变量数，全部声明变量都保留，故孤立顶点和未使用的输入位也被计数。选择卷 (59) 给规范长度 $L'=\operatorname{poly}(N)$。当 $v$ 无界时 $n'\le Cv$，有 $\rho(n')=O(\rho(v))$；有界的 $v$ 由常数代价吸收。因此一次调用给 (14.1)，空间多项式。若用每边一个门或保留所有固定 $z_e$ 再直接以 $v+e$ 调用，只能先得到以 $v+e$ 为指数参数的较弱界；这不是这里所用的消元与编译。

**最优值与终端取得。** 写 $Z_k(G)$ 为符合顶点钉值且大小至少 $k$ 的独立集数。它关于整数 $k$ 单调不增。对未钉图，$Z_0>0,Z_{v+1}=0$，在 $[0,v]$ 二分搜索至多 $O(\log(v+2))$ 次计数便得最大可行值 $\alpha$。有钉值先检查 $Z_0$，为零则报告不存在相容完成；正时使用同一搜索。最优集数恰为 $Z_\alpha$，因为 $Z_{\alpha+1}=0$；更一般地，准确大小为 $k$ 的集数为 $Z_k-Z_{k+1}$。

恢复一组最优解时固定阈值为 $\alpha$，只在**原顶点**次序上增长：数当前前缀再加下一位零的实例，正则选零，否则选一。这些都是原顶点单位子句，门数和 $n'$ 界不变。选择卷 (63)–(64) 的非空保持给至多 $v+1$ 次调用；不需要逐门、逐边反复查计数。终端已选顶点集 $S$ 满足全部边、钉值且 $|S|=\alpha$。确定求值门线并给所有 $z_e$ 填零，直接验证原 (11.3) 及阈值；这正是选择卷 (56) 要求的成功解码。若请求整个原网络赋值，$v+e$ 个输出位、辅助门位及原验证费用均为 $\operatorname{poly}(N)$，已经收费；只请求顶点集时输出 $v$ 位。对 $v=0$，$k\le0$ 时唯一空解的计数为一，$k>0$ 为零，未钉最优值为零、最优集数为一。各计数至多 $2^v$，数的输出与相减使用 $O(v+1)$ 位。

二分、增长与最终解码累计只乘一个固定多项式因子，所有外部调用顺序执行并复用空间，故仍有第 3 项。∎

**推论 14.3（已给树袋与一般计数供应的并行适用域）。** 定理 14.2 不替命题 11.2、11.4 取得一个好分解，也不削弱推论 11.5 的编译条件。对同一个显式数量任务，若原局部约束已有收费取得的宽 $w$ 树袋及字母表 $a$，一次计分的 max-sum 仍给相应 $\operatorname{poly}(N)a^{w+1}$ 上界；它可以直接求最优值，无须先把数量电路的线加入原袋。

证明。命题 11.4 把每个顶点仅归属一个袋，分数加法不重不漏；标准先例为 [Dechter 文献注 §6](../../../Library/ConceptDynamics/dechter1996bucket.md)，其原文 [§2 的 ordered graph 和 induced width](https://arxiv.org/pdf/1302.3572) 只供应经典消元背景，不将此处具体袋宽与任意消元序的 induced width 混同。在同样的完整 separator 上，令 $V_j$ 为子树袋的变量并集，$S_j$ 为父 separator；计数消息 $M_j(s)$ 只数 $V_j\setminus S_j$ 的赋值。若 $A_j(t)$ 是满足本袋归属约束的指示函数，则

$$
M_j(s)=\sum_{\substack{t:C_j\to\{0,1\}\\t|_{S_j}=s}} A_j(t)\prod_{h\text{ 子袋}}M_h(t|_{S_h}).
\tag{14.4}
$$

根取 $S_j=\varnothing$。运行交集性质使 $V_h\cap C_j=S_h$，不同子树在父袋外没有共同变量，故各乘子只数不交的内部选择；$C_j\setminus S_j$ 在本层恰计一次。这逐项证明消息数完整延拓而非边界行数，包含空 separator、未出现于边的顶点和零消息。每个计数至多 $2^v$，其位长、乘加、查表及分解表示仍须收费。这个计数版本是经典 sum-product 消元的应用，不将布尔存在消息的行数直接冒充完整解数。

定理 14.2 走的是外部固定宽度计数器路线，既不使用也不证明小宽度。若任意实例都有统一多项式取得、常数字母表、对数宽度、局部测试及解码均多项式的编译器，推论 11.5 的条件性 $P=NP$ 结论仍立；当前亚指数供应并不构造它。同理，选择卷命题 27.7 的全输入严格误差预测器若能统一多项式取得，才给该命题的单向后果。∎

## 追加锚（本行以下为增补区）
