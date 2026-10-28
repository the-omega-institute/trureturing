# 递归关系观察：测量相对量子边界续卷 I——等待读出递归

**约定。** 来源空间、实际仪器、被动实帧及单份/双份精度合同采用 [原卷](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md) 的相应条目；WR1 编号属于本续卷。

## 等待读出递归 1. 同一仪器的边缘稳定、完整历史与持续变标

**定义 WR1.1（固定来源、固定等待与读后指标）。** 保留[原卷假设 1.1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#1-五模式来源实际仪器与共同端口) 的同一个五维来源和[原卷定义 1.2](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#1-五模式来源实际仪器与共同端口) 的实际仪器，写 $P_i=\Pi_i$、$U_t=U(t)$。固定一个已标定的 $t\ge0$，每轮都执行同一个分支族

$$
\mathcal I_i^{(t)}(X)=P_iU_tXU_t^\dagger P_i,
\qquad \Phi_t=\sum_{i\in\mathsf S}\mathcal I_i^{(t)}.
\tag{WR1.1}
$$

一次运行从固定的 $\rho$ 开始；$\pi_{t,n}$ 是执行 $n$ 轮、完整保留所有读数、再 Stop 的确定策略。比较 $\rho,\sigma$ 时，$t$、仪器、控制、记录和停止规则全部相同。不在两轮间换来源、复位、补充新副本或按未取得的信息改选动作。每个有限 $n$ 都是[原卷定义 1.2](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#1-五模式来源实际仪器与共同端口) 的原有协议。

令 $I_k$ 为第 $k$ 次实际读数，$\rho_n=\Phi_t^n(\rho)$。这里 $\rho_n$ 对全部既有读数取边缘；在正概率历史上，实际条件窗口态是 $P_{I_n}$。任意初态的首读分布是

$$
p_1(i)=\operatorname{tr}(P_iU_t\rho U_t^\dagger),\qquad
M_{ij}(t)=|\langle e_i,U_te_j\rangle|^2,
\quad u=\mathbf1/5,\quad J=\mathbf1\mathbf1^{\mathsf T}/5.
\tag{WR1.2}
$$

$M_{ij}$ 的列 $j$ 是读后状态 $P_j$ 的下一读数律。因此任意初态从首读之后才有 $p_n=M^{n-1}p_1$、$n\ge1$；若 $\rho=\sum_jp_0(j)P_j$ 已对角，则从 $n=0$ 起有 $p_n=M^np_0$。原量子态的相干项不在首读之前被假定消失。

此处直接消费 [Static Fiber §15 的定义 35.1 与命题 37](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)：取其 $d=5$、$v_j(t)=U_t^\dagger e_j$，等价地在[原卷约定 1.4](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#1-五模式来源实际仪器与共同端口) 的被动实帧中取 $v_j(t)=O(t)^{\mathsf T}e_j$，则

$$
B_{ij}(t)=|U_{t,ji}|^2,\qquad M(t)=B(t)^{\mathsf T},\qquad
\kappa(t)=\|M(t)-J\|_{2\to2}=\|B(t)-J\|_{2\to2}.
\tag{WR1.3}
$$

相位坐标变换 $D$ 不改模方。这里的经典转移解释来自每轮实际执行的秩一读出；没有把不经读出的酉演化当成 $M$。谱证书及其有理计算沿用来源，不重新证明。距离约定为

$$
D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1,\qquad
\operatorname{TV}(p,q)=\tfrac12\sum_i|p_i-q_i|
=\sup_A|p(A)-q(A)|.
$$

**命题 WR1.2（同一重复协议的三种结论）。** 若固定的 $t$ 满足 $\kappa=\kappa(t)<1$，则边缘窗口满足

$$
\begin{aligned}
\rho\text{ 已对角}:\quad&D(\Phi_t^n(\rho),I_5/5)\le\kappa^n
&& (n\ge0),\\
\rho\text{ 任意}:\quad&D(\Phi_t^n(\rho),I_5/5)\le\kappa^{n-1}
&& (n\ge1).
\end{aligned}
\tag{WR1.4}
$$

对任意两个初态及每个 $n\ge1$，同一策略的完整记录仍满足

$$
\operatorname{TV}(P_\rho^{\pi_{t,n}},P_\sigma^{\pi_{t,n}})
=\operatorname{TV}(p_1^\rho,p_1^\sigma).
\tag{WR1.5}
$$

固定 $\rho,t$ 的相容无限读数律下，标签最终恒定的事件满足

$$
\Pr_\rho\{\exists m\ge1\ \exists i\in\mathsf S\ \forall k\ge m:I_k=i\}=0.
\tag{WR1.6}
$$

证明。酉性使 $M$ 双随机，所以 $MJ=JM=J$。对任意概率向量 $p$，$\|p-u\|_2^2=\sum_ip_i^2-1/5\le4/5$。对角初态因而有

$$
\begin{aligned}
p_n-u&=(M-J)^n(p_0-u),\\
D(\rho_n,I_5/5)&=\tfrac12\|p_n-u\|_1
\le\tfrac{\sqrt5}{2}\kappa^n\|p_0-u\|_2\le\kappa^n.
\end{aligned}
$$

任意初态经过第一轮后对角，再应用 $n-1$ 轮的界。式 (WR1.5) 直接使用[原卷定理 2.1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#2-秩一首读与全部有限历史的相同量度) 证明中的固定策略首读恒等式，其后缀核在本处取

$$
L_i(i_2,\ldots,i_n)=\prod_{k=2}^nM_{i_k,i_{k-1}},\qquad
P_\rho^{\pi_{t,n}}(i_1,\ldots,i_n)=p_1^\rho(i_1)L_{i_1}(i_2,\ldots,i_n).
$$

首结果保留，后缀核归一且与原输入无关，恰满足该既有恒等式的条件；这里不另立首读定理。

这些有限律在删除末读数下相容，在有限字母表的柱集上由标准概率扩张唯一给出无限路径律。若 $M_{ii}=1$，则 $Me_i=e_i$，于是 $(M-J)(e_i-u)=e_i-u\ne0$，与 $\kappa<1$ 矛盾。因此每个 $M_{ii}<1$，并且

$$
\Pr\{I_m=I_{m+1}=\cdots=i\}
=p_m(i)\lim_{r\to\infty}M_{ii}^{\,r}=0.
$$

对五个 $i$ 和可数个 $m$ 取并即得 (WR1.6)，无需把各读数假设为独立。$\square$

**推论 WR1.3（既有两个设置及退化边界）。** 命题 37 的同一证书给

$$
\kappa(2/3)<2/3,\qquad \kappa(1)<23/50.
$$

故 (WR1.4) 对角起点的两上界可分别换成 $(2/3)^n$、$(23/50)^n$，任意起点在 $n\ge1$ 时换成相应的 $n-1$ 次幂；(WR1.5)–(WR1.6) 同时适用。证明只需代入 (WR1.4)。若 $\kappa=0$，约定 $\kappa^0=1$，对角起点一步后均匀，任意起点至迟两步后均匀。若 $t=0$，则 $M=I$、$\kappa=1$，第一轮后窗口保持其对角分布，后续标签恒定；这不满足 (WR1.6) 的严格假设。

该结论将谱收缩用于取边缘后的窗口。完整历史的初态区别按 (WR1.5) 保持，单条路径的标签按 (WR1.6) 不会最终定格。无限律是理想相容模型；每个实际前缀只执行有限 $n$，含 $n$ 次等待和 $n$ 次读，等待时长合计 $nt$，另须承担读出、保存与控制的资源。无限记录不由某个有限存储或有限执行自动实现。

### 等待读出递归 1.1. 应用的来源与假设桥

以下接口说明命题 WR1.2 使用了哪一种递归、稳定和资源条件。它们是该应用的适用条件与成熟工具的参数对应。

**接口 I–II（同更新与有限结构闭包）。** [自生成预测记忆定义 1.3](RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md#1-the-source-and-the-continuing-decoder-contract) 的同更新公式在首读后的本应用取 $Z=\mathsf S$、$e_j(i)=M_{ij}$、$U(j,i)=i$，所以预测续接和取得新读数都更新到同一个标签 $i$。启动阶段另有发射行 $p_1$；它依赖固定来源，公式并不授予未知 $p_1$ 的无误取得。该来源卷的被动隐藏链与本处量子等待的物理来源不同，复用的是同更新合同。若摘要还包含学习状态、守卫或门记录，则须满足该卷定义 11.1、命题 11.2 的逐分支交织及动作合法性，不能只保存当前答案。

对于固定有限载体与有限动作、输出、末端族，直接用 [关系丛定理 8.4](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md#obs-thm-predictive) 的 $W_{n+1}=W_n+\sum_{a,o}\Phi_{a,o}^*W_n$、$N=W_\infty^\perp$ 和 $\Phi_{a,o}N\subseteq N$；五维、$W_0=\operatorname{span}\{P_i\}$ 时，其通用词长界为 $W_\infty=W_{20}$。这只是可观测方向的有限闭包，不给状态、概率或实际标签的收敛。平滑参数族的常秩像核丛及正概率后验下降复用 [定理 8.6](AURIC_FIB_RELATIONAL_BUNDLE_AND_PREDICTIVE_CLOSURE_THEORY.md#obs-thm-bundle)；增加寄存器或菜单后，须重新指定载体，原 $20$ 界不作统一增长界。

**接口 III（预算分辨率与收缩的充分条件）。** 在共同来源域上固定同一个非空合法协议族 $\Pi_R$，令

$$
d_R(x,y)=\sup_{\pi\in\Pi_R}\operatorname{TV}(P_x^\pi,P_y^\pi).
\tag{WR1.7}
$$

逐协议的对称性、三角不等式在取上确界后保持，故 $d_R$ 是伪度量；不同来源可有零距离，在零距离商上得到度量。预算嵌套须显式要求 $R\le R'\Rightarrow\Pi_R\subseteq\Pi_{R'}$，这时才有 $d_R\le d_{R'}$。固定 $R,\varepsilon>0$ 的尾部稳定指 $\sup_{m,k\ge n}d_R(x_m,x_k)\le\varepsilon$，不能换成无预算限制的永久不可区分。

若另有非空完备度量空间 $(X,d)$、自映射 $T:X\to X$、$0\le q<1$，且 $d(Tx,Ty)\le qd(x,y)$、$d_R\le d$，则 Banach 不动点定理及其几何级数估计供应唯一固定点 $x_*$，并对 $x_{n+1}=Tx_n$、$r_0=d(x_1,x_0)$ 给出

$$
d(x_n,x_*)\le\frac{q^nr_0}{1-q},\qquad
\sup_{m,k\ge n}d_R(x_m,x_k)\le\frac{q^nr_0}{1-q}.
$$

后一估计直接对 $m>k\ge n$ 的相邻增量 $d(x_{j+1},x_j)\le q^jr_0$ 求和。仅当 $0<q<1$、$r_0>0$ 时，用对数选深度为

$$
N_\varepsilon=\max\left\{0,
\left\lceil\frac{\log(r_0/((1-q)\varepsilon))}{-\log q}\right\rceil\right\}.
$$

$q=0$ 时一步到固定点；$r_0=0$ 时起点已固定。若只把状态量化成标签，还须有 $a>0$ 使 $B_d(x_*,a)$ 位于同一量化单元，才由最终误差小于 $a$ 推出标签不变；极限在单元边界时不成立。该条件不是随机读数 $I_k$ 的定格条件。幺正共轭对迹距离等距，本身没有这种严格收缩；等距轨道若收敛，其恒定相邻距离 $d(Tx_0,x_0)$ 必为零，故起点已固定。本应用的收缩来自实际非选择读出及其边缘转移。

**接口 IV（近似尾部与移动隐藏核）。** 同一 Banach 条件下，若 $d(\widetilde x_{n+1},T\widetilde x_n)\le\eta_n$，一次三角不等式迭代给

$$
d(\widetilde x_n,x_*)\le q^nd(\widetilde x_0,x_*)+
\sum_{k=0}^{n-1}q^{n-1-k}\eta_k.
$$

若 $\eta_k\le\eta$，只得 $\limsup_n d(\widetilde x_n,x_*)\le\eta/(1-q)$，不保证实际轨迹收敛，亦不把这个上界称为必达误差。

框架变化则使用 [SO5 延续卷 §71，定义 91.1、命题 91.2 的固定版本](https://github.com/the-omega-institute/trureturing/blob/02a0b90ac978ddc7716d1cd0cfedee2ee929eba1/docs/develop/theory/AURIC_OMEGA_SO5_PATH_RECONSTRUCTION_CONTINUATION.md#71-可取得预测商接入路径输运的条件)。其参数对应为 $E=\operatorname{Herm}_0(\mathscr H)$、效果列 $C_{\rm sup}$、观测映射 $C_{\rm VI}=C_{\rm sup}^{\mathsf T}$、$N=\ker C_{\rm VI}$、$P:E\to N^\perp$。给定环境连接时，商连接下降的充要条件是 $q_N\nabla^E n=0$ 对所有隐藏截面成立，其中 $q_N:E\to E/N$。在度量相容、常秩、$C^1$ 路径条件下，已有估计是

$$
\|P_{\gamma(t)}T(t,0)h\|
\le\|h\|\int_0^t\|\nabla^E_{\dot\gamma(s)}P\|_{\rm op}\,ds,
\qquad h\in N_{\gamma(0)}.
$$

正观测谱隙不替代核平行；数学输运也不自动加入[原卷的物理菜单](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#1-五模式来源实际仪器与共同端口)。只有效果列确实覆盖全部允许未来事件时，这个商才有全未来解释。

**接口 V（未归一化分支、被动参考与因果接线）。** 混合相容性要求未归一化分支线性，因而在归一化输入集合上仿射；正概率条件态 $\mathcal I_i(\rho)/\operatorname{tr}\mathcal I_i(\rho)$ 一般非线性。每个局部分支对任意未触及参考的放大 $\mathcal I_i\otimes\mathrm{id}_R$ 都须正，才是完全正；仅要求同一映射的所有正张量幂不够。转置 $\mathsf T$ 的每个 $\mathsf T^{\otimes r}$ 都是全转置，保持正性，而 $(\mathsf T\otimes\mathrm{id})(|\Omega_2\rangle\langle\Omega_2|)=F_{\rm swap}/2$ 在反对称向量上有本征值 $-1/2$，其中 $|\Omega_2\rangle=(|00\rangle+|11\rangle)/\sqrt2$，$F_{\rm swap}|a,b\rangle=|b,a\rangle$。保留失败、停止等全部输出后，分支和须保迹。这些是矩阵模型的操作假设，不从递归一词推出。

多步接线直接用 [Context Geometry §11，定义 11.5、定理 11.6](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) 及其原始供应 [Chiribella–D'Ariano–Perinotti，arXiv:0904.4483v2，定理 3、5](https://arxiv.org/pdf/0904.4483v2)：有限维、固定有限因果次序，输入 $A_k$ 对应文献 $H_{2k-2}$、输出 $B_k$ 对应 $H_{2k-1}$，采用未归一化 Choi 算子，按过去端口在前排列有

$$
R^{(k)}\ge0,\qquad
\operatorname{Tr}_{B_k}R^{(k)}=R^{(k-1)}\otimes I_{A_k'},\qquad R^{(0)}=1.
$$

它供应带记忆通道的实现；回流环境须沿同一记忆边保留。整体保迹不足以保证这个时间次序，也没有任意自指网络或所有时域共用有限记忆的结论。

**接口 VI（继续—停止语义与截断所需的尾部）。** 这是另一种递归接口：取非零有限维 $H,K$，CP 映射 $\mathcal C:\mathcal L(H)\to\mathcal L(H)$、$\mathcal S:\mathcal L(H)\to\mathcal L(K)$，要求

$$
\mathcal C^*(I_H)+\mathcal S^*(I_K)=I_H,
\qquad F_n=\sum_{k=0}^{n-1}\mathcal S\mathcal C^k,\quad F_0=0.
$$

停轮数对应可区分分支，以上求和遗忘其标签；它不是未记录路径的振幅相加。[Selinger，*Towards a Quantum Programming Language*，§§6.3–6.5、Lemma 6.4](https://www.mathstat.dal.ca/~selinger/papers/qpl-2up.pdf) 供应 CP 不增迹映射的最小语义。具体对应取继续边为 $\mathcal C$、返回边为 $\mathcal S$：CP 顺序递增的 $F_n$ 在有限维收敛到最小 CP 不增迹解 $F=\mathcal S+F\mathcal C$，不保证 $F$ 保迹。望远镜恒等式给

$$
H_n=(\mathcal C^*)^nI_H\downarrow H_\infty,\qquad
F_n^*(I_K)=I_H-H_n,\qquad F^*(I_K)=I_H-H_\infty.
$$

这也给一个直接有限维核对：$F_n$ 的正 Choi 矩阵递增且迹有界；任一 CP 固定点 $G$ 满足 $G=F_n+G\mathcal C^n$，故极限最小。其 CP 残差满足

$$
F-F_n=F\mathcal C^n,\qquad
\|F-F_n\|_\diamond=\|H_n-H_\infty\|_{\rm op}.
\tag{WR1.8}
$$

所用成熟 CP 范数恒等式为 $\|\Psi\|_\diamond=\|\Psi^*(I)\|_{\rm op}$：Kraus 族组成的 Stinespring 算子给上界，效果最大本征态给下界；这里 $\diamond$ 是完整的、未除二的范数。非终止质量 $H_\infty$ 不能计作返回近似误差。若进一步 $\mathcal C^*(I_H)\le qI_H$、$0\le q<1$，才有 $H_n\le q^nI_H$、$H_\infty=0$、$F$ 保迹；块条件 $(\mathcal C^*)^rI_H\le qI_H$ 则给 $q^{\lfloor n/r\rfloor}$，其中 $r\ge1$、$0\le q<1$。反例 $\mathcal C=\mathrm{id},\mathcal S=0$ 的最小返回语义为零，系统永不返回。

在这个终止条件下，有限执行的完成通道及理想通道为

$$
G_n(X)=F_n(X)\oplus\operatorname{tr}(\mathcal C^n(X))|\perp\rangle\langle\perp|,
\qquad G_\infty(X)=F(X)\oplus0.
$$

两者都保迹。差值的返回残差和旗标来自两个 CP 映射，其 diamond 范数均为 $\|H_n\|_{\rm op}\le q^n$；三角不等式给

$$
\tfrac12\|G_n-G_\infty\|_\diamond\le q^n,
\qquad \|G_n-G_\infty\|_\diamond\le2q^n.
$$

对任意联合态 $\tau_{HR}$，旗标块的参考算子必须是 $\operatorname{Tr}_H[(\mathcal C^n\otimes\mathrm{id}_R)(\tau)]$；它通常带有条件相关，不能把它替为概率乘一个独立参考态。整个完成通道不触及 $R$，其总参考边缘仍是 $\tau_R$。若保留全部停轮数，返回载体为可数正交和 $\bigoplus_{k\ge0}K$；这和有限 $K$ 上遗忘停轮数的 $F$ 是两个输出合同。CP 语义、范数界与有限展开均不供应新的允许门、输运或执行效率。

**接口 VII–VIII（本应用与新副本精度任务的区别）。** 命题 WR1.2 的同一窗口持续读出没有新副本。若扩大为独立新样本，单次小差异不能代替统一未来距离：对不同 Bernoulli 参数 $p,r$，成熟的乘积亲和度界给 $\operatorname{TV}(\operatorname{Bern}(p)^{\otimes m},\operatorname{Bern}(r)^{\otimes m})\ge1-(\sqrt{pr}+\sqrt{(1-p)(1-r)})^m\to1$；它来自 $\min(a,b)\le\sqrt{ab}$ 及乘积求和。自生成预测记忆定理 3.1 的对应结论还要求其特定源、有限同更新观察者、所有实际历史和所有未来长度的统一误差 $\epsilon<1$，只强制闭不可约同步分量上的精确发射，不能移作任意观察者定理。

精度接口直接使用 [Measurement Boundary 固定版本 §18，定义 18.1、定理 18.2、18.4、推论 18.5](https://github.com/the-omega-institute/trureturing/blob/02a0b90ac978ddc7716d1cd0cfedee2ee929eba1/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#18-adaptive-terminal-real-pair-acquisition-and-precision-confidence-order)。其共同实验族每次取得一份或两份独立新副本，每个完整结果拉回到未过滤输入上的总 POVM 效果在同一个固定实帧中均实对称，包含过滤的全部失败前缀；每次后舍弃所有来源依赖量子寄存器、后继及环境，只留完整经典历史。共同种子、设置、失败、停止及随机解码均计入历史。每条运行历史有限，至多 $m$ 次双份尝试，失败也收费；不是按成功数或期望停止时间计费。单份插入可任意多，但每条历史仍有限。

其固定源为 $\rho_\theta=I_5/5+\theta Y$、$Y=i(E_{12}-E_{21})$、$0\le\theta\le1/10$，其中 $E_{ab}$ 是该实帧的标准矩阵单位；同一未知 $\theta$ 贯穿全部尝试。定理 18.2 在每个已取得历史下将双份读数归为同一个谱律的来源无关后处理，供应

$$
1+\chi^2(P_\theta\Vert P_0)\le(1+100\theta^4)^m.
$$

这是完整自适应记录的界。它没有把来源改为每次独立随机选共轭符号的混合物。精度对象是[原卷式 (15.2)](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#15-a-total-rational-gram-decoder-for-the-original-complete-record) 的同一共同共轭商：若 $\rho=S+iA$、输出 $T+iB$，仅忘掉一个全局符号，距离为 $\min_{\sigma=\pm1}\|S+iA-(T+i\sigma B)\|_{\rm F}$。对 $0<h\le1/40$、$0<\delta\le1/4$，该实验族在理想标定、平稳独立制备下的最小统一双份尝试预算为

$$
m_*(h,\delta)=\Theta\!\left(h^{-4}\log(1/\delta)\right).
$$

上界的具体对应沿用[原卷推论 16.2](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#16-finite-record-confidence-for-the-rational-point-output)：$s=\lceil\log_2(1/h)\rceil$、$d=\lceil\log_2(1/\delta)\rceil$、$A_*=80621568001$、$b=47+2s$、$N=2304(d+8)A_*^2\,2^{4s}$、$m=50N$。它要求原十五单份、五十双份设置和 $F=\operatorname{diag}(1,2,3,4,5)/6$ 的精确校准、完整可读的绑定记录、已供应的制备与探测，以及 [原卷 §§15–16](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#15-a-total-rational-gram-decoder-for-the-original-complete-record) 指定的有理 Gram 枚举解码。由 [原卷式 (16.5)](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#16-finite-record-confidence-for-the-rational-point-output) 同次运行使用 $115N$ 份制备、$155N$ 个填充记录位；所有失败、过滤调用和末端探测的费用仍按该式另计。

解码的额外工作区界不包括记录、可读 backing 和输出存储。具体 [原卷式 (15.15)–(15.17)](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#15-a-total-rational-gram-decoder-for-the-original-complete-record) 还保留 $G_b=(2^{b+1}+1)^{50}-1$ 个候选、$w=b+\lceil\log_2(N+1)\rceil+\lceil\log_2(B_0+2)\rceil+64$，以及位时间 $O((B_0+155N+G_b+1)w^2)$、额外 $O(w)$ 位空间和另计的绑定输出；$B_0$ 为元数据位长。故该 $\Theta$ 只断言尝试预算阶，不断言解码高效、总存储最优或任意量子记忆实验的下界。非实效果、一次相干访问两份以上、跨尝试保留来源依赖量子记忆、未校准漂移或新来源依赖资源均需另立合同。

**接口 IX（条件链的范围）。** 同更新给出相容有限历史；固定载体上的逐分支闭包给可递归摘要；真正的收缩或返回尾部给相应量度下的有限精度逼近。它们与命题 WR1.2 的边缘极限、完整历史保存及几乎必然持续变标相容。矩阵态空间、混合规则、任意被动参考下的合法性、固定因果接线和许可菜单是各自明确的前提；这条条件链没有从递归、五个标签或有限分辨率重建物理量子理论，也不把抽象极限变成已取得记录。成熟固定点、CP 程序语义、概率扩张与因果梳结果在此只作已归属的接口供应，本文的结论是它们与同一实际等待读出消费者的上述对应。

## 追加锚（本行以下为增补区）

## 2. Fresh independent-copy terminal-discard acquisition: consumer quotient and statistical crossover

**Definition 2.1 (source, terminal consumers and quadratic coordinates).** Work in the same fixed passive real frame on $\mathbb C^5$ as [the parent volume, Definition 6.1 and §§13–18](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md); the supplier version is [the fixed source snapshot](https://github.com/the-omega-institute/trureturing/blob/e0086a9b94dd0c152d16222363adf13d7d9d6c2d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md). A lawful source is a density matrix

$$
\rho=S+iA,\qquad S^T=S,\quad A^T=-A,\qquad
 a=a(A)=(A_{ij})_{i<j}\in\mathbb R^{10}.
$$

Here each attempt obtains one or two fresh independent preparations of this same unknown $\rho$, and discards every source-dependent quantum register, successor and environment at its end. Only classical records survive. This is the acquisition class of parent Definition 18.1. WR1 instead evolves and rereads one window without replenishment; no statistical conclusion below is asserted for that experiment.

A terminal consumer is any finite real symmetric POVM on one fresh copy or on two fresh copies. Its complete output includes all failures and filter prefixes if it is implemented through filtering. For the same selected consumer $M$, let $p_\rho^M$ be its output law, and define

$$
\begin{aligned}
d_{\mathrm{cons}}(\rho,\sigma)
 &=\sup_{M\text{ as above}}\operatorname{TV}(p_\rho^M,p_\sigma^M),
 &\operatorname{TV}(p,q)&=\tfrac12\sum_z|p(z)-q(z)|,\\
\Xi(\rho)&=(S,aa^T),
 &\Sigma_2(\rho)&=\tfrac12(\rho^{\otimes2}+\overline\rho^{\otimes2})
                 =S\otimes S-A\otimes A.
\end{aligned}
\tag{2.1}
$$

For another lawful $\sigma=T+iB$ put $b=a(B)$ and

$$
\begin{aligned}
x&=\|S-T\|_{\mathrm F},\qquad y=\|aa^T-bb^T\|_{\mathrm F},
 &d_\Xi(\rho,\sigma)&=x+y,\\
d&=\min\{\|a-b\|_2,\|a+b\|_2\},
 &D&=\max\{\|a-b\|_2,\|a+b\|_2\},\\
\mathfrak d(\rho,\sigma)
 &=\min_{\epsilon=\pm1}\|S+iA-(T+i\epsilon B)\|_{\mathrm F}
 =\sqrt{x^2+2d^2}.
\end{aligned}
\tag{2.2}
$$

The two representatives $\sigma,\overline\sigma$ describe one common-conjugation orbit. There is only one common sign, not separately chosen signs for coordinates. Both $S$ and $\Sigma_2(\rho)$ are real density matrices: each is an average of positive trace-one matrices. This is an exact probability representation for the specified real effects, not a preparation service that randomizes the source's conjugation sign.

**Theorem 2.2 (exact terminal distance, quotient and global norm constants).** On all lawful sources,

$$
\boxed{
 d_{\mathrm{cons}}(\rho,\sigma)
 =\max\left\{\tfrac12\|S-T\|_1,
              \tfrac12\|\Sigma_2(\rho)-\Sigma_2(\sigma)\|_1\right\},
 \qquad \tfrac15d_\Xi\le d_{\mathrm{cons}}\le5d_\Xi.
}
\tag{2.3}
$$

This is a pseudometric whose zero classes are exactly $\{\rho,\overline\rho\}$. It therefore induces a metric on that quotient; $d_\Xi$ and $\mathfrak d$ are also metrics there. The product comparison is

$$
\boxed{\frac{dD}{\sqrt2}\le y\le dD.}
\tag{2.4}
$$

Moreover $d_\Xi\le\sqrt{3/2}\,\mathfrak d$. The parent observation map $\mathcal O(\rho)=(S,Q_F(A))$, with its Euclidean product norm, satisfies the global inverse estimate

$$
 d_\Xi(\rho,\sigma)
 \le(1+K_0)\|\mathcal O(\rho)-\mathcal O(\sigma)\|,
 \qquad K_0=40310784000.
\tag{2.5}
$$

Proof. A real symmetric effect has zero trace pairing with a purely imaginary skew matrix. Single-copy probabilities therefore pair with $S$, and pair probabilities with $\Sigma_2(\rho)$. For a real symmetric trace-zero matrix $H$, any POVM output difference satisfies

$$
 \tfrac12\sum_z|\operatorname{tr}(M_zH)|
 \le\tfrac12\operatorname{tr}|H|.
$$

Indeed $H=H_+-H_-$, positivity gives $|\operatorname{tr}(M_zH)|\le\operatorname{tr}(M_z(H_++H_-))$, and completeness sums this bound to $\operatorname{tr}|H|$. The positive spectral projection $P_+(H)$ is real and gives the binary POVM $\{P_+(H),I-P_+(H)\}$ with equality. This is the finite-dimensional Holevo–Helstrom variational argument, here restricted without loss to real projections; see [Watrous, *The Theory of Quantum Information*, Theorem 3.4](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf), with equal prior $1/2$ and respectively the real states $S,T$ and $\Sigma_2(\rho),\Sigma_2(\sigma)$. Taking the supremum over the two consumer types proves the equality in (2.3). The supremum grants a mathematical comparison, not installation or selection of its optimal measurement from an unknown source.

Write $R_0=\|a\|_2^2$, $R_1=\|b\|_2^2$ and $c=a^Tb$. Direct expansion gives

$$
\begin{aligned}
d^2D^2&=(R_0+R_1)^2-4c^2,\\
y^2&=R_0^2+R_1^2-2c^2,\\
2y^2-d^2D^2&=(R_0-R_1)^2\ge0,\\
d^2D^2-y^2&=2(R_0R_1-c^2)\ge0.
\end{aligned}
$$

The last inequality is Cauchy–Schwarz, proving (2.4) also when one vector is zero. The linear embedding $a\mapsto A$ has Frobenius scale $\sqrt2$, so its tensor square has scale $2$. Consequently

$$
 \|A\otimes A-B\otimes B\|_{\mathrm F}=2y,
 \qquad
 \|S\otimes S-T\otimes T\|_{\mathrm F}\le2x.
\tag{2.6}
$$

For the second bound, telescope the tensor product and use $\|S\|_{\mathrm F},\|T\|_{\mathrm F}\le1$. Put $Z=\Sigma_2(\rho)-\Sigma_2(\sigma)$ and $q=d_{\mathrm{cons}}(\rho,\sigma)$. The first formula in (2.3) gives $x\le2q$ and $\|Z\|_{\mathrm F}\le2q$. From (2.6), $2y\le2x+\|Z\|_{\mathrm F}$, hence $x+y\le2x+q\le5q$. In the other direction, the trace/Frobenius comparisons in dimensions $5$ and $25$ give

$$
 \tfrac12\|S-T\|_1\le\tfrac{\sqrt5}{2}x,
 \qquad
 \tfrac12\|Z\|_1\le\tfrac52\|Z\|_{\mathrm F}
                         \le5(x+y).
$$

This proves both constants in (2.3).

Every fixed consumer's total variation is a pseudometric, and taking the supremum preserves its triangle inequality. By (2.3), zero distance is equivalent to $S=T$ and $aa^T=bb^T$. A nonzero rank-one matrix $aa^T$ determines the real vector $a$ up to sign; if $a=0$, the equality forces $b=0$. Thus the zero classes are precisely common conjugation. Conversely conjugation leaves every real terminal law invariant. Distances are independent of the chosen representatives, so the pseudometric descends to a metric. The injection $[\rho]\mapsto\Xi(\rho)$ proves the metric assertion for $d_\Xi$. The isometric two-element conjugation action gives the triangle inequality for $\mathfrak d$: compose the two minimizing signs and apply the Frobenius triangle inequality.

Parent Theorem 17.2 gives $\|a\|_2,\|b\|_2\le1/2$. Hence $D\le\|a\|_2+\|b\|_2\le1$, and (2.4) yields $y\le d$. Therefore $x+y\le x+d\le\sqrt{3/2}\sqrt{x^2+2d^2}$. Finally the exact parent polarization certificate (Theorem 13.4 and (14.2)) is

$$
 dD\le K_0\|Q_F(A)-Q_F(B)\|_2.
\tag{2.7}
$$

It holds for all real skew matrices, including zero and all singular strata. Applying $y\le dD$ and bounding each observation component by the product norm gives (2.5). This is a global Lipschitz inverse into quadratic coordinates; conversion from those coordinates to $a$ can still lose a square root. $\square$

**Theorem 2.3 (prediction from the same nominal decoder, including fixed drift).** Supply the original fifteen single-copy and fifty pair settings, independent preparations and instrument initialization, the complete padded record and readable binding, and the nominal rational Gram decoder $\mathsf{Dec}_b$ of parent Definitions 15.1–15.4. The nominal filter is $F=\operatorname{diag}(1,2,3,4,5)/6$. The actual filter is one fixed real contraction $\widetilde F$ at every attempt and depth, with supplied bound $\|\widetilde F-F\|_{\mathrm{op}}\le\eta$ and failure Kraus operator $(I-\widetilde F^T\widetilde F)^{1/2}$. The decoder and its fifty integer polynomials still use $F$, with no access to $\widetilde F$. For $N\ge1$, $b\ge3$, $0<\delta<1$, put

$$
 E=24\sqrt{\frac{\log(130/\delta)}N}+512\,2^{-b},
 \qquad C_{\mathrm{cal}}=\frac{16\sqrt{10}}7,
 \qquad r_A=\|a(A)\|_2.
\tag{2.8}
$$

Its output $\widehat\rho=T+iB$ is lawful on every grammatical record. On one event of probability at least $1-\delta$,

$$
\boxed{
 d_\Xi(\rho,\widehat\rho)
 \le(1+K_0)(E+2C_{\mathrm{cal}}\eta r_A^2),\qquad
 d_{\mathrm{cons}}(\rho,\widehat\rho)
 \le5(1+K_0)(E+2C_{\mathrm{cal}}\eta r_A^2).
}
\tag{2.9}
$$

Thus at fixed confidence the terminal prediction error is $O(N^{-1/2}+2^{-b}+\eta r_A^2)$ for this fixed detector certificate, without a positive-radius restriction on $\eta$.

Proof. Parent Theorem 17.3 applies to exactly these preparations, actual failure records and unchanged decoder. On its single confidence event, with $v=E+2C_{\mathrm{cal}}\eta r_A^2$, it gives $x\le v$ and $dD\le K_0v$. Equation (2.4) gives $y\le K_0v$ and (2.3) gives (2.9). The radius bound $r_A\le1/2$, the constant $C_{\mathrm{cal}}$ and the coefficient $2$ in the nominal residual are those of parent (17.3), (17.6), (17.10)–(17.12); no inverse certificate for the actual perturbed map is assumed. Failed attempts contribute zero to the specified means and remain in the denominator $N$.

For completeness, the resource statement of parent Corollary 17.4 applies without change to this decoder or the ideal special case $\eta=0$. With $U_1$ the actual first successes among the $30N$ specimens at depth two and $C_T$ the actual double successes among the $30N$ filtered pairs, its charges are

$$
\begin{array}{c|c}
\text{all setting attempts}&65N=15N+50N\\
\text{attempted pairs, including failures}&50N\\
\text{source preparations}&115N\\
\text{single-copy detector calls}&15N\\
\text{local filter calls}&60N+U_1\le90N\\
\text{joint detector calls}&20N+C_T\le50N\\
\text{retained padded outcome bits}&155N.
\end{array}
\tag{2.10}
$$

Both prescribed filter chains execute even if the other specimen fails; only unexecuted detectors are padded. There are no free replacement successes. In the finite-bit model of parent Definition 15.4 set

$$
 n=\lceil\log_2(N+1)\rceil,\quad
 \ell_0=\lceil\log_2(B_0+2)\rceil,\quad
 w=b+n+\ell_0+64,\quad
 G_b=(2^{b+1}+1)^{50}-1,
$$

where $B_0$ is the binding metadata length. The very same exhaustive bank and exact integer score comparisons give

$$
\begin{aligned}
\text{bit time}&=O((B_0+155N+G_b+1)w^2),\\
\text{additional workspace}&=O(w)\text{ bits},\\
\text{matrix-description output}&\le60b+200\text{ bits},\\
\text{total output with copied binding}&\le B_0+2\ell_0+60b+210\text{ bits},\\
\text{separately retained input}&=155N+B_0+O(n+\log(b+1)+\ell_0)\text{ bits}.
\end{aligned}
\tag{2.11}
$$

These are the parent's signed-binary multitape-machine bounds, counting reads, writes, candidate enumeration and arithmetic, not unit-cost real operations. Additional workspace includes counters, current and best candidate matrices, arithmetic scratch, finite control and address cursors. The retained input is read-only and the output is write-only; their backing and allocation, the fixed program, actual permissions and installation/calibration descriptions are separate resources. Copying metadata does not authenticate it. Acquiring a certified $\eta$ is also a supplied resource. Neither (2.10) nor (2.11) asserts efficient decoding, elementary gate counts, physical time or energy, or preparation of the returned density. $\square$

**Definition 2.4 (uniform loss and worst-run attempted-pair budgets).** Let $\mathcal E_m$ be precisely the parent Definition 18.1 class described in Definition 2.1. A common controller may adapt its finite-outcome real POVM to its entire classical history and source-independent random seed. Every run has finite history and at most $m$ attempted pairs, including failed attempts. Any number of single-copy insertions is allowed provided every history is finite. All settings, source-call positions, prefixes, outcomes, failures, stop decisions and randomized decoding are part of that history. There is no surviving source-dependent quantum memory, source-dependent starting resource or free postselection. The same policy is used under the sources compared.

For a nonnegative loss $\ell$ and source set $\mathcal S$, define the confidence minimax risk and its budget threshold by

$$
\begin{aligned}
 R_m^{\ell}(\mathcal S,h)
 &=\inf_{(\pi,\widehat\rho)\in\mathcal E_m}
       \sup_{\rho\in\mathcal S}
       \Pr_\rho^\pi\{\ell(\rho,\widehat\rho)>h\},\\
 m^{\ell}(\mathcal S,h,\delta)
 &=\min\{m\in\mathbb N_0:\ \exists(\pi,\widehat\rho)\in\mathcal E_m,
       \ \sup_{\rho\in\mathcal S}\Pr_\rho^\pi\{\ell(\rho,\widehat\rho)>h\}\le\delta\}.
\end{aligned}
\tag{2.12}
$$

The second definition requires an actual estimator attaining the confidence requirement, irrespective of whether the infimum defining $R_m^\ell$ is attained. Outputs are lawful density-orbit descriptions; the upper bounds below use the finite rational description of Definition 15.2. With $\mathcal D=\mathcal D(\mathbb C^5)$ put

$$
 \mathcal S_r=\{S+iA\in\mathcal D:\|a(A)\|_2\ge r\},\qquad
 m_*(r,h,\delta)=m^{\mathfrak d}(\mathcal S_r,h,\delta),\qquad
 m_{\mathrm{pred}}(h,\delta)=m^{d_{\mathrm{cons}}}(\mathcal D,h,\delta).
\tag{2.13}
$$

These optimize only the worst-run pair coordinate under ideal calibration and stationary independent preparation. They do not bound total preparations, record storage or processing for arbitrary competing procedures; those resources are explicitly retained for the exhibited upper procedure in (2.10)–(2.11). Mathematical availability of real POVMs is part of this statistical class, not an implementation theorem.

**Theorem 2.5 (conditional information for two nonzero radii and the larger prediction domain).** Write $J_{12}=E_{12}-E_{21}$, $Y=iJ_{12}$ and

$$
 \rho_\theta=I_5/5+\theta Y,\qquad 0\le\theta\le1/\sqrt{40}.
\tag{2.14}
$$

These are strictly positive density matrices. For any common experiment of $\mathcal E_m$, including its output, let $P_j$ be its complete-history law for $\rho_{\theta_j}$, $j=0,1$. Define

$$
 q_\theta(a,b)=\frac1{25}+\theta^2y_ay_b,
 \quad y=(1,-1,0,0,0),\quad
 c(\theta_1,\theta_0)=\frac{100(\theta_1^2-\theta_0^2)^2}{1-625\theta_0^4}.
\tag{2.15}
$$

Then, with natural logarithms,

$$
\begin{aligned}
 1+\chi^2(P_1\Vert P_0)&\le(1+c(\theta_1,\theta_0))^m,\\
 D_{\mathrm{KL}}(P_1\Vert P_0)&\le m\log(1+c(\theta_1,\theta_0)),\\
 \operatorname{TV}(P_1,P_0)&\le\tfrac12\sqrt{(1+c(\theta_1,\theta_0))^m-1}.
\end{aligned}
\tag{2.16}
$$

Proof. The eigenvalues of $\rho_\theta$ are $1/5\pm\theta$ and three copies of $1/5$. Since $1/\sqrt{40}<1/5$, all are positive throughout (2.14). At a fixed classical history $H$, a complete real pair effect $Q_{H,z}$ obeys the direct identity

$$
\begin{aligned}
 \rho_\theta^{\otimes2}
 &=I_{25}/25+\tfrac\theta5(Y\otimes I+I\otimes Y)+\theta^2Y\otimes Y,\\
 \operatorname{tr}(Q_{H,z}\rho_\theta^{\otimes2})
 &=\operatorname{tr}(Q_{H,z}(I_{25}/25+\theta^2Y\otimes Y)).
\end{aligned}
\tag{2.17}
$$

The omitted pairing is zero because its transpose is its negative. A fixed orthonormal eigenbasis $u_a$ of $Y$ has eigenvalues $y_a$. Thus the conditional output law is $q_\theta K_H$, where

$$
 K_H(z\mid a,b)=\langle u_a\otimes u_b,Q_{H,z}(u_a\otimes u_b)\rangle\ge0,
 \qquad \sum_zK_H(z\mid a,b)=1.
\tag{2.18}
$$

This kernel depends on the fixed history and common policy, not on $\theta$. It includes failures and source-independent ancillas through their total input effects. The eigenbasis labels are only a probability representation; nonreal eigenbasis controls are not supplied. Each real single-copy law equals $\operatorname{tr}(PI_5/5)$, independent of $\theta$.

On this entire interval $q_\theta\ge1/25-1/40=3/200>0$. Only four entries differ between $q_{\theta_1}$ and $q_{\theta_0}$, two of each sign. With $\Delta=\theta_1^2-\theta_0^2$, direct summation gives

$$
 \chi^2(q_{\theta_1}\Vert q_{\theta_0})
 =\frac{2\Delta^2}{1/25+\theta_0^2}
  +\frac{2\Delta^2}{1/25-\theta_0^2}
 =c(\theta_1,\theta_0).
\tag{2.19}
$$

For the observed conditional likelihood $\lambda_H$, conditional expectation of the spectral likelihood under $q_{\theta_0}$ and Jensen give

$$
 \mathbb E_0(\lambda_H\mid H)=1,\qquad
 \mathbb E_0(\lambda_H^2\mid H)\le1+c,
 \qquad
 D(p_{1,H}\Vert p_{0,H})\le\log(1+c).
\tag{2.20}
$$

For the last inequality, $\mathbb E_1\log\lambda_H\le\log\mathbb E_1\lambda_H=\log\mathbb E_0\lambda_H^2$. These are the classical data-processing and order-one/order-two comparisons; their general forms are [van Erven–Harremoës, *Rényi Divergence and Kullback–Leibler Divergence*, Theorems 1, 3, 9 and Example 2](https://arxiv.org/html/1206.2459v2). Here both use one common finite kernel, and all densities are positive; (2.19) supplies their exact specialization.

Include the seed and all randomization in $H$. Group the single-copy insertions before the first pair, and after each pair up to the next pair or stop. The initial block has a common law. Conditional on a fixed past, all the subsequent single-only steps use source-independent kernels, even when their finite length is random. The finite paths have total mass one by the finite-history assumption. Thus each pair together with the following block still satisfies (2.20). Pad unused slots after stopping with a common dummy symbol up to $m$. This neither adds nor loses information. If $L_t$ is the likelihood after $t$ such slots, then

$$
 L_t=L_{t-1}\lambda_t,\qquad
 \mathbb E_0(L_t^2\mid H_{t-1})\le(1+c)L_{t-1}^2.
$$

Iteration proves the chi-square bound. Every $q_\theta$ lies between $3/200$ and $13/200$, so the spectral, observed and block likelihood factors lie between $3/13$ and $13/3$, or equal one in dummy slots. Their log likelihoods are integrable even with continuous seeds and unbounded finite single-only blocks. The conditional chain rule therefore gives $D(P_1\Vert P_0)\le m\log(1+c)$. Cauchy–Schwarz applied to $\tfrac12\mathbb E_0|L_m-1|$ gives the last line of (2.16). This directly proves the extension beyond parent Theorem 18.2's $\theta\le1/10$ domain; no out-of-domain application of that theorem is used. A source-dependent quantum carrier between attempts would destroy the common classical-kernel argument. $\square$

**Theorem 2.6 (radius–precision–confidence crossover for full orbit loss).** Uniformly for

$$
 0\le r\le1/20,\qquad 0<h\le1/80,\qquad 0<\delta\le1/4,
\tag{2.21}
$$

under ideal calibration,

$$
\boxed{
 m_*(r,h,\delta)
 =\Theta\!\left(\frac{\log(1/\delta)}{h^2(r+h)^2}\right).
}
\tag{2.22}
$$

An explicit lower constant is

$$
 m_*(r,h,\delta)\ge
 \frac{\log(1/\delta)}{131072\,h^2(r+h)^2}.
\tag{2.23}
$$

Proof of the upper bound. Set $H=h(r+h)$ and use the original acquisition and the same decoder from Theorem 2.3 with $\eta=0$ and

$$
 N=\left\lceil(768K_0)^2H^{-2}\log(130/\delta)\right\rceil,
 \qquad
 b=\max\left\{3,\left\lceil\log_2\frac{16384K_0}{H}\right\rceil\right\},
 \qquad m=50N.
\tag{2.24}
$$

Each of the two terms of $E$ is at most $H/(32K_0)$, so $E\le H/(16K_0)$. On its probability-$1-\delta$ event the parent product certificate yields $dD\le K_0E\le H/16$, and the parallelogram identity gives

$$
 D^2=\|a\|_2^2+\|b\|_2^2+2|a^Tb|
 \ge\|a\|_2^2\ge r^2,\qquad D\ge d.
$$

For $r\le h$, $d^2\le H/16\le h^2/8$. For $r>h$, $d\le H/(16r)\le h/8$. This includes $r=0$ without division by zero. Furthermore $r+h\le1/16$ on (2.21), so $x\le E\le h/(256K_0)$. In both cases

$$
 \mathfrak d^2=x^2+2d^2
 \le h^2\left((256K_0)^{-2}+\tfrac14\right)<h^2.
\tag{2.25}
$$

The displayed procedure is in $\mathcal E_m$, has lawful output on every record, and succeeds uniformly on $\mathcal S_r$. Its acquisition, failure, record and finite-bit computation charges are exactly (2.10)–(2.11) with (2.24). In particular $b$ grows logarithmically in $1/H$, while the exhaustive bank of exponent fifty remains. Because

$$
 \log(130/\delta)\le\left(1+\frac{\log130}{\log4}\right)\log(1/\delta),
$$

and the ceiling adds at most one, $50N=O(H^{-2}\log(1/\delta))$ with one constant on (2.21).

Proof of the lower bound, including full confidence dependence. Compare (2.14) at $\theta_0=r$ and $\theta_1=r+4h$. Both lie in $\mathcal S_r$, and $\theta_1\le1/10$ by (2.21). Their quotient distance is $\sqrt2(\theta_1-\theta_0)=4\sqrt2h>2h$. The triangle inequality for $\mathfrak d$ makes their closed $h$-balls disjoint. From any estimator successful on both sources, select source one exactly when the estimate lies in its $h$-ball. Both testing errors are at most $\delta$, including any decoder randomization already in the history.

Here $\Delta=8rh+16h^2\le16h(r+h)=16H$ and $625r^4\le1/256$. The exact constant (2.19) therefore obeys

$$
 c(\theta_1,\theta_0)
 \le\frac{6553600}{255}H^2\le32768H^2=:c_*.
\tag{2.26}
$$

For clarity, the confidence argument uses both second moment and relative entropy. A test with error sum at most $2\delta$ requires $\operatorname{TV}(P_1,P_0)\ge1-2\delta$. From (2.16),

$$
 m\log(1+c_*)\ge\log(1+4(1-2\delta)^2).
\tag{2.27}
$$

Let $\alpha=\int\sqrt{dP_1\,dP_0}$ be the affinity. With $L=dP_1/dP_0$, Jensen under $P_1$ gives $\alpha=\mathbb E_1L^{-1/2}\ge e^{-D(P_1\Vert P_0)/2}$. Cauchy–Schwarz on $(\sqrt p-\sqrt q)(\sqrt p+\sqrt q)$ gives $\operatorname{TV}\le\sqrt{1-\alpha^2}$. Every test consequently has error sum at least

$$
 1-\operatorname{TV}\ge1-\sqrt{1-\alpha^2}
 \ge\alpha^2/2\ge\tfrac12e^{-D(P_1\Vert P_0)}.
$$

Using its error sum at most $2\delta$ and (2.16) yields

$$
 m\log(1+c_*)\ge\log(1/(4\delta)).
\tag{2.28}
$$

Write $A_\delta$ for the maximum of the right sides of (2.27) and (2.28). For $1/16\le\delta\le1/4$, its first term is at least $\log2\ge\tfrac14\log(1/\delta)$. For $\delta<1/16$, its second term is at least $\tfrac12\log(1/\delta)$. Thus always $A_\delta\ge\tfrac14\log(1/\delta)$. Since $\log(1+c_*)\le c_*$, (2.23) follows. This is a worst-run attempted-pair bound: the proof includes every failure and allows arbitrary finite single-copy insertions; it is not a success-count or expected-stopping-time bound. Together with (2.24) it proves (2.22). $\square$

For $r\le h$, $h\le r+h\le2h$, so (2.22) is $\Theta(h^{-4}\log(1/\delta))$. For $r>h$, $r<r+h<2r$, so it is $\Theta(r^{-2}h^{-2}\log(1/\delta))$, with the same uniform interpretation. The $N^{-1/4}$ global orbit scale and the $r^{-1}N^{-1/2}$ positive-radius scale thus concern inversion of the quadratic coordinates, while terminal prediction below does not invert that final square root.

**Theorem 2.7 (all-source terminal prediction minimax order).** On $0<h\le1/80$, $0<\delta\le1/4$, the same ideal experiment class has

$$
\boxed{
 m_{\mathrm{pred}}(h,\delta)=\Theta(h^{-2}\log(1/\delta)),
 \qquad
 m_{\mathrm{pred}}(h,\delta)\ge\frac{\log(1/\delta)}{1600h^2}.
}
\tag{2.29}
$$

The constants are independent of $h,\delta$, and hence also of any $r$ in (2.21); this prediction assertion is over the full class $\mathcal D$, not only $\mathcal S_r$.

Proof of the upper bound. Use exactly the same nominal decoder and schedule with

$$
 N=\left\lceil(240(1+K_0))^2h^{-2}\log(130/\delta)\right\rceil,
 \qquad
 b=\max\left\{3,\left\lceil\log_2\frac{5120(1+K_0)}h\right\rceil\right\},
 \qquad m=50N.
\tag{2.30}
$$

The statistical and bank terms of $E$ are each at most $h/(10(1+K_0))$. Therefore (2.9), at $\eta=0$, gives $d_{\mathrm{cons}}\le5(1+K_0)E\le h$ except on a probability-$\delta$ event, for every lawful source, including real states. The logarithm comparison in the proof of Theorem 2.6 gives the stated uniform upper order. Its full resource coordinates remain (2.10)–(2.11), with $N,b$ as in (2.30); there is no replacement of the bank by an efficient optimizer.

Proof of the lower bound. Use $\rho_0$ and $\rho_\theta$ from (2.14) with $\theta^2=2h$. In this entire precision range,

$$
 \theta\le1/\sqrt{40}<1/5,\qquad
 \lambda_{\min}(\rho_\theta)=1/5-\theta>0,\qquad
 q_\theta\ge3/200>0.
$$

In particular $\theta$ may exceed $1/10$; Theorem 2.5 proves the needed reduction directly on its actual domain. The single-copy difference is zero and the pair difference is $\theta^2Y\otimes Y$. The eigenvalues of $Y$ are $1,-1,0,0,0$, so $\|Y\|_1=2$ and $\|Y\otimes Y\|_1=4$. Equation (2.3) consequently gives the exact separation

$$
 d_{\mathrm{cons}}(\rho_\theta,\rho_0)=2\theta^2=4h>2h,
 \qquad \chi^2(q_\theta\Vert q_0)=100\theta^4=400h^2.
\tag{2.31}
$$

The disjoint $h$-balls in this quotient metric produce the same two-error-$\delta$ test as above. Apply (2.16) with $c_*=400h^2$ and repeat (2.27)–(2.28):

$$
 m\log(1+400h^2)\ge A_\delta\ge\tfrac14\log(1/\delta).
$$

The inequality $\log(1+400h^2)\le400h^2$ gives the lower constant in (2.29). All source probabilities and conditional likelihoods remain positive, and the confidence argument includes $\delta=1/4$. This proves prediction optimality for the stated attempted-pair coordinate, without implying any lower bound for an experiment retaining quantum memory between attempts. $\square$

**Corollary 2.8 (bounded classical-discard future consumption).** Fix a nonnegative integer $L$ and a common initial classical record, for example one particular acquired record. Conditional on that same record, compare only newly generated future outputs, with the same initial seed law in both comparisons. Consider one common future policy making at most $L$ terminal-consumer calls of Definition 2.1, each on fresh independent input, and retaining only classical history. It may adapt its real single/pair POVM and stopping to that history and common randomness. If $P_\rho^{\pi,L},P_\sigma^{\pi,L}$ are these conditional complete future-history laws, then

$$
 \operatorname{TV}(P_\rho^{\pi,L},P_\sigma^{\pi,L})
 \le\min\{1,L\,d_{\mathrm{cons}}(\rho,\sigma)\}.
\tag{2.32}
$$

Proof. Include the seed and pad stopped calls with a common dummy output. At a fixed past history the same next action is selected, so its two conditional output laws differ by at most $q=d_{\mathrm{cons}}(\rho,\sigma)$. For history laws $P,Q$ and their next-step kernels $K_\rho,K_\sigma$, insert the intermediate law $PK_\sigma$. Contraction of total variation under a common kernel and the pointwise bound give

$$
 \operatorname{TV}(PK_\rho,QK_\sigma)
 \le\int\operatorname{TV}(K_\rho(\cdot\mid H),K_\sigma(\cdot\mid H))\,dP(H)
     +\operatorname{TV}(P,Q)
 \le q+\operatorname{TV}(P,Q).
$$

Induction over $L$ calls, starting from the common seed, proves (2.32), with the trivial cap one. At $L=0$ the distance is zero. On the confidence event of Theorem 2.3 one may substitute its particular lawful $\widehat\rho$ for $\sigma$ and multiply (2.9) by $L$. This is a statement about subsequent conditional prediction laws; preparing $\widehat\rho$ or evaluating arbitrary supplied effects with finite arithmetic has not thereby been implemented. The bound supplies no fixed error for unlimited future calls, coherent consumers on arbitrarily many copies, or surviving source-dependent quantum memory. $\square$

The inverse and decoder constants used here are the exact parent §§13–17 suppliers: the nonsingular-polarization certificate, product-distance bound, rational Gram scan, bounded-independent concentration event and fixed-filter perturbation. Their concentration step uses the ranges two and one and the $65$-setting union bound in parent Proposition 14.2; no new concentration hypothesis is imposed. The external inputs used in the displayed intermediate arguments are finite-dimensional Holevo–Helstrom discrimination with equal priors, and classical data processing/order comparison for probability laws. The new conclusions are the repository-derived combination into the specified consumer quotient, unchanged-decoder prediction estimate and uniform crossover and prediction budgets; they assert no historical priority, new general discrimination theorem, quantum-memory rate, or physical installation of the granted measurement class.

## 追加锚（本行以下为增补区）

## 3. One fixed DU installation: acquired finite acceptance and paid current-state use

**Convention 3.1 (a separate source domain).** This section uses the single-preparation source of [Compatible Predictive Waves V, Definition 91.1 and Proposition 91.3](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_V.md), and the complete outgoing-record lift class of [Compatible Predictive Waves VI, Assumption 101.2 and Theorem 101.3](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md), abbreviated CPW V and CPW VI. Repository supplier statements in this section mean their texts at `ebf00c8ca5334b897d9aedb5bcb5cc97e638bd06`. This is a separately named **fixed-DU installation**. It replaces neither the waiting-window source of §1 nor the fresh-independent-copy source of §2; the opening parent-source convention of this volume does not identify these three sources.

The exact scalar anchor CPW VI (101.5) is **not** assumed. Its role is replaced by a finite acquired test, with the weaker guarantees below. The fixed control, outgoing-carrier identity, readout, memorylessness and full-matrix-domain assumptions remain supplied structural premises. They are not consequences of that test.

**Definition 3.2 (source, supplied controls and full branches).** On $Q=\mathbb C^3$ set

$$
\begin{gathered}
U=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\qquad
D=\operatorname{diag}(1,1,-1),\qquad N=DU,\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\quad
e=(1,1,-2)^{\mathsf T}/\sqrt6,\quad
f=(1,-1,0)^{\mathsf T}/\sqrt2,\quad q=(\xi+e)/\sqrt2,\\
\psi=\sqrt d\,Uq+i\sqrt{1-d}\,Uf,\qquad
\rho_0=\psi\psi^\dagger,\qquad 0<d<1,\\
V_0=Ue^{i\pi W/4},\qquad V_1=V_0W,\qquad
P_y=(I+yW)/2\quad(y\in\{+1,-1\}).
\end{gathered}
\tag{3.1}
$$

The preparation is performed once. The controller is independent of $d$ and never requests its value. The one installed deterministic control is $N$; the formulas for $D,U$ do not grant separate calls to them. Indeed $N\xi=D\xi$ is not proportional to $\xi$, so this installation satisfies CPW V's mixing condition. The angle is fixed at $\pi/4$.

Use the genuine original outgoing record basis $g_0,g_1$ of CPW VI (101.2), and abbreviate it by $|0\rangle,|1\rangle$ only within this section. For one unknown fixed $\gamma\in\mathbb C$, $|\gamma|\le1$, each source call $\mathsf J$ has the complete CPTP action

$$
\begin{aligned}
\mathcal L_\gamma(X)=\tfrac12[&V_0XV_0^\dagger\otimes|0\rangle\langle0|
 +V_1XV_1^\dagger\otimes|1\rangle\langle1|\\
 &+\gamma V_0XV_1^\dagger\otimes|0\rangle\langle1|
 +\bar\gamma V_1XV_0^\dagger\otimes|1\rangle\langle0|].
\end{aligned}
\tag{3.2}
$$

This is the parametrization supplied by CPW VI Theorem 101.3 of its entire structural class (101.4), not an inferred law for an unrestricted unknown instrument. Each call has the same $\gamma$, a fresh ready two-dimensional outgoing carrier, and no persistent hidden state affecting later calls. Every earlier retained classical cell and every untouched finite reference $Z$ sees the identity map. Tensoring the following formulas with $\operatorname{id}_Z$ is part of the premise, including when the current $Q$ is correlated with $Z$.

The authorized record-only read settings are the original $g$ setting and the fixed $F$ setting with vectors $(|0\rangle\pm|1\rangle)/\sqrt2$. A read returns its actual bit, copies it to owned classical storage and retires the measured carrier. Its **complete returned-system** branches are supplied to be

$$
\begin{aligned}
A_j(X)&=\tfrac12V_jXV_j^\dagger\quad(j=0,1),\\
C_y^\gamma(X)&=\tfrac14V_0
 [X+WXW+y\gamma XW+y\bar\gamma WX]V_0^\dagger,\\
\Lambda&=A_0+A_1=C_+^\gamma+C_-^\gamma
 =\operatorname{Ad}_U\circ\mathcal P,\qquad
\mathcal P=(\operatorname{id}+\operatorname{Ad}_W)/2,\\
\Theta&=\Lambda^2\circ\operatorname{Ad}_N\circ\Lambda^2.
\end{aligned}
\tag{3.3}
$$

Thus effects alone are not the readout contract. The sum of the two branches is trace preserving, and both branches are completely positive by (3.2). A wash block realizes $\Theta$ by the chronological word $\mathsf J\mathsf J\mathsf N\mathsf J\mathsf J$, leaving its four outgoing carriers unread and disposing of them outside the accessible interface. Neither their labels nor a coherent copy is returned. The call $\mathsf N$ realizes $\operatorname{Ad}_N$ on the current system. There is no reset, inverse, additional preparation, forced outcome, arbitrary record unitary, return wire or archive decoder.

For physical source placement take $H=\mathbb C^5$, $u_H=(e_0+e_3)/\sqrt2$, $v_H=(e_1+e_4)/\sqrt2$, $z_H=e_2$ and $B=(u_H,v_H,z_H)$. The actual initial state is $B\rho_0B^\dagger$, the control is $\widetilde N=BNB^\dagger+I_5-BB^\dagger$, and the port is the same outgoing carrier as in CPW VI (101.1)–(101.3). The lift and read branches are transported by $B$ on this code. This is the original preparation's code realization from CPW V Proposition 91.3; arbitrary mathematical input matrices below do not supply preparations of them.

**Definition 3.3 (controller, rights and accessible output).** Before preparation supply public integers $h,p,s\ge1$, an owned finite task word

$$
v\in\{\mathsf N,\mathsf J_g,\mathsf J_F\}^{\le h},
\qquad \varepsilon=2^{-p},\quad\delta=2^{-s}.
\tag{3.4}
$$

The installed finite program has bit reads/writes, Boolean tests, sequential cell allocation and cursor moves, and finite control jumps. Integer addition/comparison and the finite loops below are routines over these instructions, with their bit work charged. Integers, counters, records and outputs occupy growing finite storage. A binary increment scans through the trailing ones and writes the first zero; comparison scans lengths and then digits; fixed multiplication by 7 or 12 uses shifts and additions. The mismatch routine stores the first actual bit and sets a persistent Boolean on a later unequal bit. The fixed program and the actual variable inputs are installed and retained, with their own source-binding and owner references. No source-dependent seed or unknown-parameter input is available.

The authorized owner may repeatedly call $\mathsf J,\mathsf N$, select either specified immediate read setting, write the returned bits, hold the current system and its reference without drift between these calls, and retire carriers as just specified. Owned storage is readable by this program and may actually supply its later tests and annotations. Source identity, carrier/readout calibration, reference identity and permissions stay fixed. Their finite encodings and physical backing, and the backing of the supplied untouched reference, are additional resources, not outputs inferred from the bit tape. Exact implementation of these primitives is a model premise; no physical precision, energy or duration bound is asserted.

The complete accessible output includes every measured calibration bit in chronological order, the acquired test flag, all stored task inputs and fixed reference/rights data, every later measured bit and requested annotation, the actual live $QZ$ successor, and the controller's phase, cursor and work cells. Inconclusive runs return their actual state and record as well. The inaccessible disposal sink and the retired quantum carriers are not returned outputs or later callable references. Disposing of them does not erase them from a global physical completion, nor make their supply free. A claim with access to that sink would be a different output contract.

### 3.1 A rate available from the installed matrices

**Lemma 3.4 (explicit wash bound).** For every complex traceless $X\in M_3$,

$$
\|\Theta X\|_2^2\le\tfrac5{12}\|X\|_2^2,
\qquad
\|\Theta^nX\|_2\le(2/3)^n\|X\|_2.
\tag{3.5}
$$

Consequently, for every density matrix $\sigma$ and integer $n\ge0$,

$$
\|\Theta^n\sigma-I/3\|_2\le\sqrt{2/3}(2/3)^n.
\tag{3.6}
$$

**Proof.** All inner products here are complex Hilbert–Schmidt inner products. Set $\mathcal Q=(\operatorname{id}+\operatorname{Ad}_{UWU})/2$. Since $U^2=I$, $A:=\Lambda^2=\mathcal Q\mathcal P$. Both $\mathcal P,\mathcal Q$ are orthogonal projections. The transpositions $W$ and $UWU$ generate the six permutation matrices. Their conjugation average $\mathcal G$ is the orthogonal projection onto

$$
\mathscr F=\operatorname{span}_{\mathbb C}\{I,P_\xi\}.
$$

Indeed a matrix commuting with every permutation has one common diagonal entry and one common off-diagonal entry. Expanding the three factors gives

$$
A^*A=\mathcal P\mathcal Q\mathcal P
       =\tfrac14(\mathcal P+3\mathcal G).
\tag{3.7}
$$

For completeness, writing $S=\operatorname{Ad}_W$, $T=\operatorname{Ad}_{UWU}$, the numerator of the left side is $2I+2S+T+ST+TS+STS$. The six group terms are $I,S,T,ST,TS,STS$, giving exactly the right side. Thus $A$ fixes $\mathscr F$, preserves $\mathscr F^\perp$ and has norm at most $1/2$ there. This supplies a numerical bound in the fixed installation; the general strict-contraction criterion itself is CPW VI Theorem 103.2.

On the traceless subspace put $u=(P_\xi-I/3)/\sqrt{2/3}$ and $K=\operatorname{Ad}_N$. The only component in $\mathscr F$ is a multiple of $u$. Since $\langle\xi,N\xi\rangle=1/3$,

$$
\langle u,Ku\rangle
 =\frac{|\langle\xi,N\xi\rangle|^2-1/3}{2/3}=-1/3.
\tag{3.8}
$$

Write $X=\alpha u+y$ with $y\perp\mathscr F$, and $z=Ay$, so $z\perp u$ and $\|z\|_2\le\|y\|_2/2$. Unitarity of $K$ gives $|\langle u,Kz\rangle|^2\le(8/9)\|z\|_2^2$. Applying the final $A$ to the $u$ component and its perpendicular complement, then using $|b+c|^2\le2|b|^2+2|c|^2$, yields

$$
\begin{aligned}
\|AKA X\|_2^2
 &\le\tfrac14(|\alpha|^2+\|z\|_2^2)
     +\tfrac34|-\alpha/3+\langle u,Kz\rangle|^2\\
 &\le\tfrac5{12}|\alpha|^2+\tfrac{19}{12}\|z\|_2^2
 \le\tfrac5{12}|\alpha|^2+\tfrac{19}{48}\|y\|_2^2
 \le\tfrac5{12}\|X\|_2^2.
\end{aligned}
\tag{3.9}
$$

Here $\Theta=AKA$, and $\sqrt{5/12}<2/3$. It is unital and trace preserving. Apply the bound repeatedly to $\sigma-I/3$, whose squared Hilbert–Schmidt norm is $\operatorname{tr}(\sigma^2)-1/3\le2/3$, proving (3.5)–(3.6). $\square$

**Lemma 3.5 (reference-safe paid refresh).** Let $Z$ be any finite untouched reference and $\sigma_{QZ}$ any density matrix, including an actual state conditioned on an earlier measured tape. Then

$$
\left\|(\Theta^n\otimes\operatorname{id}_Z)(\sigma_{QZ})
      -\tfrac I3\otimes\sigma_Z\right\|_1
 \le\min\{2,3(2/3)^n\}.
\tag{3.10}
$$

This conclusion returns the earlier tape and reference, but excludes all new wash carriers as in Definition 3.3.

**Proof.** Put $\mathcal D(X)=\operatorname{tr}(X)I/3$ and $\Delta=\Theta^n-\mathcal D$. The identity component is killed, and (3.5) bounds the Hilbert–Schmidt operator norm of $\Delta$ by $(2/3)^n$ on all matrices. Tensoring with an identity preserves this Hilbert–Schmidt operator norm. For a pure $QZ$ input, its Schmidt support in $Z$ has dimension at most three and is preserved by $\Delta\otimes\operatorname{id}$. The output is supported on at most nine dimensions. Cauchy–Schwarz on its singular values gives $\|Y\|_1\le3\|Y\|_2\le3(2/3)^n$. Decompose a mixed input into pure states and use linearity and the triangle inequality. Both states in (3.10) are normalized, which also gives the cap two. Including the old finite classical tape in $Z$ is permitted. Including the discarded new carriers would change $\Theta$ and invalidate this proof. $\square$

### 3.2 One actual finite calibration tape

**Definition 3.6 (the installed gate).** Define the following integers and rational threshold from the actual input (3.4):

$$
\begin{gathered}
t=s+2,\qquad B_0=128t,\qquad
\kappa=\frac{\varepsilon^2}{8h^2},\qquad
m=1+16t h^2 4^p=1+\frac{2t}{\kappa},\\
L=9,\qquad L_0=2p+5.
\end{gathered}
\tag{3.11}
$$

First repeat $B_0$ times: execute $L$ wash blocks, then one $\mathsf J$ with an immediate $F$ read. Append every bit $x_i\in\{+1,-1\}$ to its chronological tape slot, and increment an integer $K_+$ on the actual plus replies. Next execute $m$ cycles consisting of one $\mathsf J$ with an immediate $F$ read followed by one $\mathsf N$. Append every reply $y_i$ in order, and maintain the first reply and a mismatch bit. Position means its slot ordinal in this ordered tape, not an additional timestamp field or free clock read. Both stages finish their fixed lengths, also after an early mismatch. The acquired flag is

$$
\mathsf{PASS}\quad\Longleftrightarrow\quad
12K_+\ge7B_0\quad\hbox{and}\quad y_1=y_2=\cdots=y_m.
\tag{3.12}
$$

Otherwise return $\mathsf{INCONCLUSIVE}$. This report is not an assertion that $\gamma\ne1$. On PASS the program actually executes $L_0$ further wash blocks and enables one finite use of the stored task word $v$. It never substitutes an unexecuted reset for this refresh.

**Lemma 3.7 (the word statistic without an independent-specimen premise).** Put $a=\operatorname{Re}\gamma$ and $R=NV_0=D e^{i\pi W/4}$. Then $[R,W]=0$. For $\mathcal G_y=\operatorname{Ad}_N\circ C_y^\gamma$, every full sector block obeys

$$
\mathcal G_y(P_wXP_z)
 =\frac{1+wz+y(\gamma z+\bar\gamma w)}4
       R(P_wXP_z)R^\dagger,
\qquad w,z\in\{+1,-1\}.
\tag{3.13}
$$

For every entrance density matrix $\sigma$, the actual $m$-reply law is therefore

$$
\Pr_\gamma(y_1,\ldots,y_m\mid\sigma)
 =\sum_{w=\pm1}\operatorname{tr}(P_w\sigma)
          \prod_{i=1}^m\frac{1+y_iwa}{2}.
\tag{3.14}
$$

The probability of a constant word is, for every such entrance,

$$
q_a^m+(1-q_a)^m,\qquad q_a=(1+a)/2.
\tag{3.15}
$$

The same statement applies conditional on every positive-probability earlier calibration history, without asserting that its entrance is $\rho_0$.

**Proof.** $D$ commutes with $W$, giving the commutation for $R$. Multiply (3.3) on the left and right by the two spectral projections to obtain (3.13). A diagonal block is multiplied at each cycle by $(1+ywa)/2$; the remaining conjugation preserves its trace and its $W$ sector. Every off-diagonal sector block remains off diagonal and has trace zero. Taking traces of the iterated full maps proves (3.14). Summing the all-plus and all-minus words eliminates the entrance weights, since exchanging $w$ exchanges the two products, giving (3.15). References can first be traced out for this probability calculation. Equation (3.13), rather than a classical mixture replacement, remains the full quantum successor contract: there can still be off-diagonal blocks. $\square$

**Theorem 3.8 (finite acquired acceptance, uniform on the structural class).** For every $d\in(0,1)$, $h,p,s\ge1$ and every fixed $|\gamma|\le1$, the actual gate terminates after the fixed calls of Definition 3.6. It satisfies

$$
\sup_{\substack{|\gamma|\le1\\\operatorname{Re}\gamma\le1-\kappa}}
       \Pr_\gamma(\mathsf{PASS})\le e^{-t}\le\delta,
\qquad
\Pr_1(\mathsf{PASS})\ge1-e^{-t}\ge1-\delta.
\tag{3.16}
$$

The inequalities hold for the same one evolving source, with its actual entire measured F tape retained. They are not posterior probabilities for $\gamma$ and do not certify that an unknown device belongs to the structural class.

**Proof.** For any current conditional marginal $\sigma$, an immediate F read has plus probability $[1+a\operatorname{tr}(W\sigma)]/2$. After $L=9$ washes, (3.6) and tracelessness of $\sigma-I/3$ give

$$
\left|p_+-\left(\tfrac12+\tfrac a6\right)\right|
 \le\tfrac12\|W-I/3\|_2\sqrt{2/3}(2/3)^9
 =\tfrac23(2/3)^9\le\tfrac1{48}.
\tag{3.17}
$$

Here $\|W-I/3\|_2^2=8/3$ and $(2/3)^9\le1/32$. These estimates apply conditional on all earlier measured bits, because each conditional density is a legitimate input to the next actual wash. If $a\le0$, every conditional plus mean is at most $25/48$. If $\gamma=1$, it is at least $31/48$. The sign threshold $7/12=28/48$ has gap $1/16$ in either case.

Let $X_i=1_{\{x_i=+1\}}$, $\mu_i=\mathbb E(X_i\mid x_1,\ldots,x_{i-1})$ and $M_n=\sum_{i=1}^n(X_i-\mu_i)$. The bounded-variable Hoeffding lemma gives, conditionally, $\mathbb E(e^{\lambda(X_i-\mu_i)}\mid\text{past})\le e^{\lambda^2/8}$. Applying the tower property and then Markov's inequality, and minimizing $e^{-\lambda B_0u+B_0\lambda^2/8}$ at $\lambda=4u$, gives

$$
\Pr(M_{B_0}\ge B_0u),\quad
\Pr(M_{B_0}\le-B_0u)\le e^{-2B_0u^2}.
\tag{3.18}
$$

At $u=1/16$ this is $e^{-t}$. Thus the sign test alone bounds acceptance when $a\le0$ and bounds sign rejection when $\gamma=1$. No independent preparations, independent sign samples or state estimation have been used.

For $0<a\le1-\kappa$, Lemma 3.7 gives, for every entrance after the entire sign tape,

$$
\begin{aligned}
\Pr(\text{constant word}\mid\text{sign tape})
 &=q_a^m+(1-q_a)^m\\
 &\le\max(q_a,1-q_a)^{m-1}
 \le(1-\kappa/2)^{m-1}\le e^{-t}.
\end{aligned}
\tag{3.19}
$$

The first inequality uses $q_a+(1-q_a)=1$. The cases $a\le0$ and $0<a\le1-\kappa$ are disjoint parameter cases, so no sum of two error probabilities is needed. For $\gamma=1$, the word is constant with probability one for every entrance, and only the sign test can reject. Finally $e^{-(s+2)}\le2^{-s}$. This proves (3.16). The constant-word statistic alone also accepts $\gamma=-1$ with probability one; this explains the sign stage for this particular construction, without a necessity claim for all possible assays. $\square$

### 3.3 Full output maps, current-state comparison and reference preservation

**Definition 3.9 (all actual calibration cells).** Tensor every system map below with $\operatorname{id}_Z$. Write

$$
\begin{gathered}
\mathcal S_{x_i}=C_{x_i}^\gamma\circ\Theta^9,\qquad
E_{x,y}=(\mathcal G_{y_m}\circ\cdots\circ\mathcal G_{y_1}
          \circ\mathcal S_{x_{B_0}}\circ\cdots\circ\mathcal S_{x_1}
          \otimes\operatorname{id}_Z)(\rho_0\otimes\zeta_Z),\\
c=(x,y),\qquad a(c)=1_{\{\text{(3.12) holds}\}},\qquad
\mu_c=\operatorname{tr}E_c,\qquad E_c^Z=\operatorname{tr}_Q E_c.
\end{gathered}
\tag{3.20}
$$

Here $\zeta_Z$ is the actual supplied untouched reference state. Since $\rho_0$ is pure, every extension with that original system marginal has this product form; no correlated initial preparation is being added. Conditional correlations created later, and old classical tapes, are covered by Lemma 3.5. Retain the whole $c$, its deterministic counters and flag, not just the sufficient statistic $K_+$.

For a task word $v$, let $b$ range over all its actual g/F bit strings. Let $\mathcal F_{v,b}^\gamma$ be the chronological product of $\operatorname{Ad}_N$, $A_j$ or $C_y^\gamma$ prescribed by $v,b$. A word of length zero has the identity map and one empty output. The complete accessible mass-one instrument has rejection cells

$$
|c,0\rangle\langle c,0|\otimes E_c
\quad(a(c)=0)
\tag{3.21}
$$

and accepted cells

$$
|c,1,b\rangle\langle c,1,b|\otimes
 \bigl((\mathcal F_{v,b}^\gamma\circ\Theta^{L_0})
                  \otimes\operatorname{id}_Z\bigr)(E_c)
\quad(a(c)=1).
\tag{3.22}
$$

Deterministic controller work, retained fixed inputs, cursor values and the annotations of §3.4 are attached to each classical cell by their specified common update. Equations (3.20)–(3.22) include every branch, its complete live-system and reference successor and the failed gate's actual output. No zero cell is divided by its mass. Summing traces over all $c,b$ gives one, since each complete stage is trace preserving. Physical transport is by $B$ at every step; $\widetilde NB=BN$ and the branch intertwining identities prove this by induction, preserving all masses, references and successors. The original terminal effects are not used as unspecified post-measurement channels.

**Lemma 3.10 (one-call and finite complete-output stability).** Use the unhalved trace norm. On every density matrix $\sigma_{QZ}$,

$$
\|((\mathcal L_\gamma-\mathcal L_1)\otimes\operatorname{id}_Z)(\sigma)\|_1
       =|1-\gamma|.
\tag{3.23}
$$

Reading in either declared setting and retiring the measured carrier cannot increase this bound. For any one common classical-read task word $v$ with at most $h$ source calls, the complete joint output, including all actual bits, final system and reference, changes by at most $h|1-\gamma|$ when all its lifts are replaced by $\mathcal L_1$ at the same entrance.

**Proof.** In record-first order, (3.2) is conjugation of $\tau_\gamma\otimes X$ by the mathematical block unitary with blocks $V_0,V_1$, where

$$
\tau_\gamma=\tfrac12\begin{pmatrix}1&\gamma\\\bar\gamma&1\end{pmatrix}.
$$

The same factorization holds with references. The two eigenvalues of $\tau_\gamma-\tau_1$ are $\pm|\gamma-1|/2$; tensor multiplicativity of the trace norm and $\|\sigma\|_1=1$ give (3.23). This factorization is a proof of a norm identity, not an additional callable controlled unitary or ancilla supply. A common CPTP read/retirement map contracts trace norm on Hermitian differences. To compare whole words, insert hybrids replacing one source call at a time. Prior complete histories form a normalized classical–quantum state; applying (3.23) to that state, with its old record in the reference, bounds this replacement by $|1-\gamma|$. Later common complete maps contract it. Sum over at most $h$ replacements. This argument compares complete branch tables, not individual normalized rare branches. $\square$

**Theorem 3.11 (acquired gate followed by paid, callable finite use).** For every fixed source and inputs of Definitions 3.2–3.3, let $A$ be the event PASS and $P_A=\Pr_\gamma(A)$. Let $\Omega_A$ be the actual accepted subnormalized output obtained by summing (3.22). Define its mathematical comparator $\widetilde\Omega_A$ by keeping the **actual** calibration cells, flags, task inputs and their masses, and replacing only each accepted quantum input and suffix by

$$
\widetilde\Omega_{c,b}
 =|c,1,b\rangle\langle c,1,b|\otimes
     (\mathcal F_{v,b}^1\otimes\operatorname{id}_Z)
                       (I/3\otimes E_c^Z).
\tag{3.24}
$$

Attach the same deterministic work/annotation outputs in both tables. Then

$$
\operatorname{tr}\Omega_A=\operatorname{tr}\widetilde\Omega_A=P_A,
\qquad
\|\Omega_A-\widetilde\Omega_A\|_1
       \le\varepsilon P_A+2\delta.
\tag{3.25}
$$

More precisely, when $\operatorname{Re}\gamma>1-\kappa$, the bound is $\varepsilon P_A$; when $\operatorname{Re}\gamma\le1-\kappa$, it is $2P_A\le2\delta$. If $P_A>0$, a valid normalized conditional bound is

$$
\left\|\frac{\Omega_A}{P_A}-\frac{\widetilde\Omega_A}{P_A}\right\|_1
 \le\min\{2,\varepsilon+2\delta/P_A\}.
\tag{3.26}
$$

Adding the identical actual rejection cells (3.21) to both tables yields mass-one outputs with the same difference bound. The comparator is neither the original preparation $\rho_0$ nor a rerun of calibration at $\gamma=1$. It is not an asserted preparation procedure for $I/3\otimes E_c^Z/\mu_c$. Actual refresh is the executed $\Theta^{L_0}$ on the actual current state.

**Proof.** First suppose $a>1-\kappa$. The disk constraint gives

$$
|1-\gamma|^2=1-2a+|\gamma|^2\le2(1-a)<2\kappa,
\qquad h|1-\gamma|<\varepsilon/2.
\tag{3.27}
$$

For every positive-mass accepted $c$, apply Lemma 3.5 to $E_c/\mu_c$ and its actual $Z$ marginal. The actual refresh output differs from $I/3\otimes E_c^Z/\mu_c$ by at most

$$
3(2/3)^{L_0}=3(2/3)^{2p+5}
 =\frac{32}{81}(8/9)^p\,\varepsilon<\varepsilon/2.
\tag{3.28}
$$

Apply the actual complete suffix to both entrances; it contracts this difference. Lemma 3.10 then replaces that suffix by the ideal one, with added error less than $\varepsilon/2$. The resulting full-cell bound is $\varepsilon\mu_c$. Summing over the orthogonal calibration cells gives $\varepsilon P_A$. Zero cells vanish by positivity. If $a\le1-\kappa$, Theorem 3.8 gives $P_A\le\delta$, and two positive operators of the same mass $P_A$ differ by at most $2P_A$. These are alternative fixed-parameter cases, proving (3.25). Division when $P_A>0$ and the trivial cap two give (3.26). At $P_A=0$ both accepted tables are zero and no conditional law is defined. $\square$

### 3.4 An installed finite prefix consumer

**Definition 3.12 (one callable entry and exact annotations).** After the actual accepted refresh, the controller offers one Ready entry to execute its owned task word $v$, with its original length bound $h$. Its selector reads only the acquired flag, the phase, the task cursor and the next symbol of that word; failure leaves the inconclusive successor in (3.21), and only PASS enables this entry. At a $\mathsf J_g$ or $\mathsf J_F$ slot it calls the original lift, uses that declared immediate record read, writes the actual returned bit and advances the cursor. At $\mathsf N$ it calls the fixed control and advances. Thus the gate and the finite word really select the lawful operations; a table indexed by an unavailable $\gamma$ is never used.

In parallel the program maintains one nominal unnormalized $3\times3$ matrix $T$ initialized to $I/3$. At each actual slot it applies the corresponding fixed map

$$
T\longmapsto
\begin{cases}
NTN^\dagger,&\mathsf N,\\
A_j(T),&\mathsf J_g\text{ with actual }j,\\
C_y^1(T)=UP_yTP_yU^\dagger,&\mathsf J_F\text{ with actual }y.
\end{cases}
\tag{3.29}
$$

It can return the current exact rational $\operatorname{tr}T$ and the two exact rational unnormalized next-branch weights for either permitted next read, by evaluating its two fixed maps and taking their traces. The caller requesting these annotations is the same owned finite program; copies actually returned are retained and charged. The live quantum system is not set to $T/\operatorname{tr}T$. The annotation makes no division, and remains defined on a zero nominal-probability prefix.

**Theorem 3.13 (finite arithmetic, route agreement and the actual-law guarantee).** The entry of Definition 3.12 is an installed finite algorithm on every actual acquired tape and every task word (3.4). For a length-$k$ task prefix, $T$ is exactly the chronological ideal branch product applied to $I/3$. The forward recurrence, that ordered product, and the backward effect pairing give the same joint prefix weight. On every good fixed parameter $a>1-\kappa$ and every positive-mass accepted calibration cell $c$, the entire actual future-bit law differs from the nominal law by total variation at most $\varepsilon/2$. Its complete quantum output obeys the stronger unhalved bound $\varepsilon$ of Theorem 3.11. The same total variation bound holds after deterministic annotation of those bits.

At most $h$ updates of (3.29) take $O(h^2)$ bit operations and $O(h)$ bits for one current nominal matrix in an explicit Gaussian-integer representation. Retaining annotations at every prefix instead of only a current callable value takes $O(h^2)$ additional output bits; copying requested outputs costs their actual length. These are upper bounds for this finite algorithm, without an optimality assertion.

**Proof.** The ideal F identity follows from $V_0P_y=e^{iy\pi/4}UP_y$. Also

$$
\begin{aligned}
A_j(X)&=\tfrac14 U(I+iW)W^jXW^j(I-iW)U^\dagger,\\
C_y^1(X)&=\tfrac14 U(I+yW)X(I+yW)U^\dagger.
\end{aligned}
\tag{3.30}
$$

All coefficients are Gaussian rationals with denominator dividing four; $N$ is a signed permutation. Store $T=Z_k/(3\cdot4^k)$, with $Z_k$ a fixed-size Gaussian-integer matrix; these exact fractions need not be reduced. At an $N$ step multiply the conjugated numerator by four to maintain this common denominator. At the other steps (3.30) is a fixed finite collection of additions and multiplication by fixed Gaussian integers. Positivity and subnormalization give $|T_{ij}|\le1$, hence every real and imaginary numerator has $O(k+1)$ bits. Each update therefore takes $O(k+1)$ bit operations and workspace. The denominator is stored by its exponent and factor three, or explicitly with $O(k+1)$ bits. Taking traces and computing either two-way next-branch table has the same bound. Summing over $k\le h$ gives the stated work and output bounds. No arbitrary real inverse, bank scan, unknown matrix entry or physical state preparation is required by this arithmetic.

Induction on the slots proves equality with the ordered branch product. For a prefix with maps $M_1,\ldots,M_k$, repeatedly using the trace-dual identity gives

$$
\operatorname{tr}(M_k\cdots M_1(I/3))
 =\operatorname{tr}[(M_1^*\cdots M_k^*(I))\,I/3].
\tag{3.31}
$$

Thus the alternative routes agree on this same task and source. The sum over the two next-read branches is the current joint prefix mass, since the complete instrument is trace preserving; all next masses are nonnegative. This supplies a normalized ideal law when summed over the complete task. Finally, trace out the final system/reference from the good-parameter bound in the proof of Theorem 3.11, conditional on this same actual $c$, and divide the trace norm by two for classical total variation. Deterministic annotations contract total variation. These are joint-law guarantees. Dividing a rare prefix's joint weights by its mass need not preserve this error, so no uniform conditional forecast or certainty about the realized next bit follows. $\square$

### 3.5 Resources on that same executed run

**Proposition 3.14 (simultaneous physical and logical bill).** Let $j_f,n_f$ be the actual numbers of $\mathsf J$ and $\mathsf N$ slots in the stored task word, so $j_f+n_f\le h$. An inconclusive run uses

$$
\#\mathsf J=37B_0+m,\qquad
\#\mathsf N=9B_0+m,\qquad
\#\text{F reads}=B_0+m.
\tag{3.32}
$$

An accepted run, including refresh and the complete callable task, uses

$$
\begin{aligned}
\#\mathsf J&=37B_0+m+4L_0+j_f,\\
\#\mathsf N&=9B_0+m+L_0+n_f,\\
\#\text{g/F reads}&=B_0+m+j_f.
\end{aligned}
\tag{3.33}
$$

The sign and word calibration uses $47B_0+3m$ source/control/read occurrences. An accepted run adds $5L_0+2j_f+n_f$. In particular their upper order is

$$
O\bigl((s+1)h^2\varepsilon^{-2}+p\bigr).
\tag{3.34}
$$

These counts start after the one original preparation. Its actual supply and installation cost is a separate input coordinate, as are control/readout installation and reference calibration; the F samples do not acquire those interfaces or set their costs to zero. Each source call consumes one fresh ready two-dimensional carrier. Of these, $36B_0$ calibration wash carriers and, on acceptance, $4L_0$ refresh carriers are discarded unread. The $B_0+m+j_f$ measured carriers on an accepted run are retired after their individual actual bits have been stored. Only one carrier at a time need remain in flight; no coherent archive is used. The one five-dimensional code specimen, untouched reference and accessible storage persist. All carrier material supplied or retired is counted even though it is outside the later accessible output.

There are exactly $B_0+m$ measured calibration bits, retained with their phase framing; counters, first-bit and mismatch state do not replace this tape. Sequential backing allocation, framing, permissions and references are additional charged fields. The fixed finite program has a fixed code-size charge; parameters and schedule counters need $O(p+s+\log(h+1))$ working bits as a conservative bound. The task word and its future raw bits use $O(h)$ bits, the one nominal matrix uses $O(h)$ bits, and a complete annotation transcript uses the separate $O(h^2)$ output bound of Theorem 3.13. Source binding and reference identities need their actual encoding lengths, and the supplied reference has its actual dimension/backing; neither is hidden in the constant of a source-independent memory claim.

For sequential binary counters, bit tests, loop control and append/copy storage, a conservative bound for calibration/refresh scheduling is $O(T\log(T+2))$ bit operations, where $T$ is the executed source/control/read count above, plus the actual encoding/install and reference-handling costs. The nominal prefix arithmetic adds $O(h^2)$, and output copies add their length. This is a logical bit model with growing storage, not a claim that a finite program has bounded total memory, nor an identification with PR57's receipt-per-tape-occurrence runtime.

**Proof.** Each of the $B_0$ sign cycles has nine wash blocks and one read source call, hence 37 source calls, nine controls and one F read. Each of the $m$ word cycles has one of each. The refresh has four source calls and one control per block, and the task counts its actual slots and one immediate read per source call. Adding gives (3.32)–(3.33). Substitution of (3.11) gives (3.34), since $h\ge1$, $\varepsilon\le1/2$. The storage bill follows from writing every measured reply once, maintaining bounded-width counters for these finite lengths and using the exact arithmetic representation already proved. Increment/comparison on $O(\log(T+2))$ bits at each scheduled occurrence yields the conservative bit bound. Forming the finite schedule integers by shifts, addition and schoolbook multiplication is within this bound for (3.11); the supplied task and external encoding/install costs are separate. No branch forcing, unobserved measurement reply or replayed preparation is included in any count. $\square$

### 3.6 Source correspondence and remaining mathematical boundaries

**Proposition 3.15 (what has and has not been recovered).** Within this fixed installation, the chronological measured F record actually supplies the gate in (3.12); that gate selects an executed finite refresh and a legal owned finite consumer. Equations (3.20)–(3.22) are their common-source full successor maps, (3.24)–(3.28) give their exact finite comparison domain, and (3.29)–(3.31) give agreement of the installed nominal prefix routes. This supplies finite acquisition and continued callable use without a fresh specimen or an unknown-source numerical oracle.

No four-view maps, equality of their task kernels or pairwise inverses are constructed here. The theorem's data have narrower operational meanings: spatial support is the actual code, outgoing carriers and accessible tensor cut; chronology is the executed source/control/read order; boundary data specify the installed complete instrument, read settings and access/disposal rights; memory consists of the acquired measured tape, work cells and callable annotations. None is defined as an unrestricted copy of all the others. In particular the count statistic forgets chronological reply order; no inverse from the classical tape to the unknown full quantum state is proved or assumed, and no readout of physical metric or elapsed duration is defined. The claims above recover only their explicitly proved directed operational correspondences.

**Proof.** The actual acquired selector and the paid continuation are Definitions 3.6 and 3.12; their operational correctness and complete outputs are Theorems 3.8, 3.11 and 3.13. For the count's loss of order, sign strings with one plus in two different positions have the same $K_+$; at $\gamma=0$, every measured F sign has probability $1/2$ at every entrance, so both such strings are actual positive-probability records. The retained full tape distinguishes them while the count does not. A full quantum-state inverse is not asserted by any of these maps: (3.14) is a record-law mixture, (3.13) retains the separate successor blocks, and the only refresh claim is (3.10) with its declared disposal. Hence no missing inverse is used to justify the continuation. $\square$

**Supplier correspondence.** The reused mathematics and the additional source-specific conclusion have different scopes.

| Supplier | Reused content and boundary |
| --- | --- |
| CPW V §§54, 91 and CPW VI §§101–103 | The actual five-dimensional code/preparation, stationary full-matrix lift class, fixed outgoing F setting, branch/reference transport and general wash contraction. The exact-law anchor (101.5), coherent archive and Schmidt-control availability are not hypotheses here. Lemma 3.4 adds a direct numerical rate only for the displayed installed DU matrices. |
| CPW VI §§106–110 | These retain their different same-carrier return-wire assumptions and full-completion conclusions. No return wire is used here; their finite-original-history separation is not the acquired gate/current-state/finite-prefix theorem above. |
| [Gaussian Adaptive Record Kernel, Definitions 1.1–1.4](RECURSIVE_RELATIONAL_OBSERVATION_GAUSSIAN_ADAPTIVE_RECORD_KERNEL.md) | Its source is an unknown spectral preparation with parameter-independent QND continuations and a fixed earlier target time. Here $\gamma$ occurs in each repeated lift, and the source is the single CPW preparation; neither model's record kernel is substituted for the other's. |
| [Native Clocked Recovery](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), [Native Paid View Conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), [Native Callable Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md), [Transport Memory Completion §57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), [Process Geometry §§19, 34](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) | Their declared source/controller/permissions, actual acquisition and full-response distinctions are preserved. The native tree/tape serializers and view inverses do not install the CPW quantum source or its F readout. The present supplied bit-control model does not inherit their native four-view equivalence, literal journals, raw exits or original task guarantees. |
| [FiniteKrausInstrumentBornMarginal.lean](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean), [WordProbabilityTraceRepresentation.lean](../../../D5/S3/Quantum/Measurement/WordProbabilityTraceRepresentation.lean), [FiniteLocalProtocol.lean](../../../D5/S3/Quantum/Recovery/FiniteLocalProtocol.lean), and their owning Scribes | Existing finite Kraus/Born marginal, chronological trace-dual representation and complete finite-tree trace accounting. These generic identities are reused; they do not certify this section's new calibration, rate, controller or resource theorem. |
| [FiniteDiamondDistance.lean](../../../D5/S3/Quantum/Foundation/FiniteDiamondDistance.lean) and the reference/contraction parts of [SchurChannelMixedUnitaryDistance.lean](../../../D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance.lean), with their owning Scribes | Reference amplification, finite-dimensional pure-input compression and trace-norm contraction are mature suppliers. All trace-norm errors here are unhalved; total variation introduces its explicit factor one half. No Schur mixed-unitary distance theorem is required for this particular lift. |

The sector-record argument is an application of quantum non-demolition likelihood structure; see Bauer–Bernard, [*Convergence of repeated quantum non-demolition measurements and wave function collapse*, equations (1)–(3)](https://arxiv.org/abs/1106.4953v2). The conditional bounded-variable step (3.18) is the Hoeffding lemma/tower argument; the pinned mathlib `Mathlib/Probability/Moments/SubGaussian.lean` at `56a005855ea17e0b0958f73ec801ae140b0a1679` supplies bounded-variable Hoeffding and conditional subgaussian-sum theory. Neither a new general QND theorem nor a new concentration inequality is claimed. The source-local contribution is their combination with the fixed-DU identities into a finite acquired gate, an actually paid reference-safe current-state refresh, the complete accepted-output bound and the finite callable rational-prefix implementation on that same source. This is a repository-derived synthesis, without a claim of historical priority or new Lean certification.

All original fixed-$G_{gc}$, original-$Q$, parked-consumer and unchanged-initialization obligations retain their stated domains. This installation does not prove their missing acquisition bridges. It also leaves open physical conformance and acquisition of the supplied CP/readout/reference/rights interface, general-$N$ herald/archive consumers, all-raw-carrier retention, supplied-contrast operation synthesis, native-to-quantum correspondence, full four-view mutual recovery, universal alpha/beta sufficiency or minimality, and unlimited continued-use bounds. Finite confidence does not become an exact anchor; subnormalized output comparison does not become rare-branch certainty; a mathematical comparison state does not become an extra preparation. None of these remaining bridges is removed by the finite result.

## 追加锚（本行以下为增补区）

## 4. Fixed-DU acquisition with selective adaptive F-read counts

**Definition 4.1 (the compared source and legal observation histories).**
Retain exactly the fixed-DU installation of Definitions 3.2–3.3. In every
comparison fix the same $d\in(0,1)$, original preparation
$B\rho_0(d)B^\dagger$, finite untouched reference and its initial state,
public task inputs, source binding, rights, physical readout calibration,
program and initialized classical cells. The parameter $\gamma$ alone changes
within the stationary memoryless lift class (3.2). On the code, the common
initial state is $\rho_0(d)\otimes\zeta_Z$. Later system/reference correlations
are retained. Every branch below acts as its displayed system map tensored
with $\operatorname{id}_Z$.

A legal classical policy uses the installed finite instructions and owned
storage of Definition 3.3. At each settled cut it selects, from its actually
available classical cells, a control $\mathsf N$, a source call with immediate
$g$ or $F$ read, a source call whose carrier is discarded unread, a local
classical instruction or hold, or a terminal decision. It cannot select from
the unknown $d,\gamma$, an unmeasured quantum state, an inaccessible disposal
record or a parameter-dependent initial seed. The supplied state and the
entire initialized receiver, including metadata and any accessible advice,
are matched across the compared parameters. Intermediate framing and
enabledness have the common semantics of Definition 3.3. There is no reset,
inverse, new preparation, delayed carrier read, additional measurement
setting, return wire or coherent archive.

A finite history $r$ records the actual issued instructions, their replies
and terminal decision, when present. It is a probability-space index; using
it in a proof supplies no additional stored copy to a policy that erased or
compressed earlier data. The policy can use only its actual retained cells.
Let $c(r)$ be those cells and all classical outputs actually returned at the
cut. The finite binary instructions, finite strings and bit replies give a
countable set of finite histories. Complete histories retain refusals and
all measured outcomes; a branch is never selected by forcing an outcome.

Write $\mathcal E_\gamma(r)$ for the chronological system branch map, and put

$$
\begin{gathered}
E_{\gamma,d}(r)
 =(\mathcal E_\gamma(r)\otimes\operatorname{id}_Z)
                  (\rho_0(d)\otimes\zeta_Z),\\
p_{\gamma,d}(r)=\operatorname{tr}E_{\gamma,d}(r),\\
F(r)=\#\{\hbox{actual immediate F reads in }r\}.
\end{gathered}
\tag{4.1}
$$

The complete returned substate at that cut is
$|c(r)\rangle\langle c(r)|\otimes E_{\gamma,d}(r)$, with the fixed inputs
and reference data included in $c(r)$. On the physical code replace its
quantum part by $(B\otimes I_Z)E_{\gamma,d}(r)(B^\dagger\otimes I_Z)$.
Different histories with the same returned cells are summed when those
histories are no longer distinguished by the accessible output. The measured
carriers have retired, and the unread carriers and disposal sink remain
inaccessible, precisely as in Definition 3.3.

Let $\mathcal A$ be any set of finite terminal accepting histories of this
policy. It is prefix free. Its probability is the nonnegative sum
$\Pr_{\gamma,d}(\mathcal A)=\sum_{r\in\mathcal A}p_{\gamma,d}(r)$.
This sum is at most one: at any finite instruction depth, pad terminal
leaves by identities; completeness of each read instrument and trace
preservation of common steps give total mass one. Accepted terminal
leaves up to that depth have mass at most one, and increasing the depth
exhausts their countable union.
The statements below require neither a uniform terminal depth nor finite
expected stopping cost. They apply even when some other paths never
terminate; such paths are outside $\mathcal A$. Every accepted path must
actually terminate after finitely many instructions and reads. For a gate
promising termination, that additional promise means almost-sure finite
termination at each parameter in its declared domain.

For maps, $\Phi\succeq_{\rm CP}\Psi$ means that $\Phi-\Psi$ is completely
positive. For matrices, $X\succeq Y$ means $X-Y$ is positive semidefinite.
The two orders are distinct; CP order is used before tensoring arbitrary
untouched references.

**Theorem 4.2 (selective domination of full adaptive branch successors).**
For every policy and common initialization of Definition 4.1, every
$0<\kappa<2$, and every finite history $r$, set

$$
a=1-\kappa,\qquad q=\frac{1+a}{2}=1-\frac\kappa2\in(0,1).
\tag{4.2}
$$

Then the source-specific branch maps and their actual returned substates
satisfy

$$
\mathcal E_a(r)\succeq_{\rm CP}q^{F(r)}\mathcal E_1(r),
\qquad
E_{a,d}(r)\succeq q^{F(r)}E_{1,d}(r).
\tag{4.3}
$$

Both statements include histories having zero probability at either
parameter. They preserve the actual returned $QZ$ successor and its
classical cells, without an equality assumption on normalized conditional
states. In particular, writing
$\alpha=\Pr_{1,d}(\mathcal A)$ and
$\beta=\Pr_{a,d}(\mathcal A)$, one has

$$
\boxed{\quad
\beta\ \ge\ \sum_{r\in\mathcal A}q^{F(r)}p_{1,d}(r)
       =\mathbb E_{1,d}[\mathbf1_{\mathcal A}q^F].
\quad}
\tag{4.4}
$$

The expectation denotes the displayed finite-terminal sum; it requires no
definition of $q^F$ on nonterminating paths.

If a separately paid, finite classical random seed is supplied with a
parameter-independent law, (4.3) holds conditional on its common value
and (4.4) holds after averaging over that law. Its actual finite encoding
and backing are charged. This permits no parameter-dependent seed and
installs no additional randomization primitive.

**Proof.** The complete F branches in (3.3), with the same fixed matrices,
give the exact identity

$$
\begin{aligned}
C_y^a
 &=q C_y^1+(1-q)C_y^{-1},\\
C_y^{-1}&=C_{-y}^1,\\
C_y^a-q C_y^1&=(1-q)C_{-y}^1\succeq_{\rm CP}0.
\end{aligned}
\tag{4.5}
$$

Indeed $q-(1-q)=a$, so the two cross coefficients in (3.3) have exactly
the real value $a$; changing $\gamma=1$ to $-1$ exchanges $y$ and $-y$.
Here the superscript $-1$ denotes the parameter $\gamma=-1$, not an
inverse operation. The endpoint branches are CP by the supplied lift.
Equation (4.5) is an
identity of actual branch maps, not a callable random coin or an
authorization to choose the other endpoint instrument. By contrast the
$g$ branches $A_j$, unread channel $\Lambda$, control
$\operatorname{Ad}_N$ and hold are the same at both parameters. These
common maps incur no factor $q$.

Fix a finite history. The same classical prefix fixes the same next
instruction and the same next retained-cell update at both parameters.
This is a statement about the common program at a specified history; the
history need not have positive probability in both experiments. Induct on
the actual instruction sequence. At the empty prefix the two maps agree.
For a common CP next map $M$, composition gives

$$
M\circ\mathcal E_a-q^fM\circ\mathcal E_1
   =M\circ(\mathcal E_a-q^f\mathcal E_1)\succeq_{\rm CP}0.
$$

At an F outcome $y$, use instead

$$
\begin{aligned}
C_y^a\circ\mathcal E_a-q^{f+1}C_y^1\circ\mathcal E_1
 &=C_y^a\circ(\mathcal E_a-q^f\mathcal E_1)\\
 &\quad+q^f(C_y^a-q C_y^1)\circ\mathcal E_1
 \succeq_{\rm CP}0.
\end{aligned}
\tag{4.6}
$$

CP maps are closed under composition, addition and multiplication by a
nonnegative scalar. Deterministic local instructions and terminal labels
only update common classical cells, so they preserve this induction.
This proves the map assertion in (4.3). Complete positivity permits the
actual reference amplification, and evaluation on the same positive
initial state gives its matrix assertion. Appending the same classical
output cell, summing cells that coincide, or transporting by $B\otimes I_Z$
preserves positive order. This accounts for the full declared returned
output; no order on an accessible complementary disposal environment has
been asserted.

The trace of each positive residual is nonnegative. Sum the resulting
$p_{a,d}(r)\ge q^{F(r)}p_{1,d}(r)$ over any finite subset of accepting
leaves. Increase those subsets to their countable union. Nonnegative
monotone sums give (4.4), without truncating a stopping time, exchanging
signed limits or assigning conditional states to zero-mass branches.
The finite branch/trace interpretation is the one used in (3.20)–(3.22).
For a supplied classical seed, apply this argument to each fixed seed
and sum the nonnegative terms with its common probabilities. Finite
strings form a countable seed space, so the same monotone-sum argument
applies to their joint histories.
$\square$

**Corollary 4.3 (accepted means, caps and finite null events).** In
Theorem 4.2, $\alpha>0$ implies $\beta>0$. If $0<\beta<\alpha$, put
$r_q=-\ln q>0$. Then

$$
\begin{aligned}
\mathbb E_{1,d}[F\mid\mathcal A]
 &\ge\frac{\ln(\alpha/\beta)}{r_q},\\
\mathbb E_{1,d}[F;\mathcal A]
 :=\sum_{r\in\mathcal A}F(r)p_{1,d}(r)
 &\ge\frac{\alpha\ln(\alpha/\beta)}{r_q}.
\end{aligned}
\tag{4.7}
$$

These are extended nonnegative expectations and may be infinite. Under
$0<\beta<\alpha$, if $F\le K$ almost surely on ideal accepted paths
for a finite $K$, then

$$
\beta\ge\alpha q^K,\qquad
K\ge\frac{\ln(\alpha/\beta)}{r_q}.
\tag{4.8}
$$

In particular any worst-run cap on all paths obeys this bound. If
$\beta=0$, necessarily $\alpha=0$, even when the putative ideal
accepted cost has infinite mean.

**Proof.** On every finite accepted history the weight $q^{F(r)}$ is
strictly positive. A positive sum of ideal accepting masses therefore
has a positive weighted sum, proving the first and last assertions.
For a finite conditional mean $\mu$, convexity of $x\mapsto e^{-r_qx}$
and (4.4) give

$$
q^\mu\le\mathbb E_{1,d}[q^F\mid\mathcal A]\le\beta/\alpha.
\tag{4.9}
$$

Taking logarithms proves the first line of (4.7); multiplying by $\alpha$
proves the second. If $\mu=\infty$, both lower bounds hold directly.
Under the cap, $q^F\ge q^K$ on the same accepted paths, so (4.4) gives
(4.8). This is the usual exponential/Jensen argument applied to the
selectively counted actual F reads; it assumes no independent samples.
$\square$

## 5. Necessary F-read price for the specified acquired gate

**Definition 5.1 (the gate contract and the counted cut).** Fix
$0<\kappa<1$ and $0<\delta<1/2$. A gate for this installation is one
common installed policy, independent of $d,\gamma$, terminating almost
surely at every $d\in(0,1)$ and $|\gamma|\le1$, with terminal report
PASS or INCONCLUSIVE, and satisfying

$$
\begin{gathered}
\Pr_{1,d}(\mathsf{PASS})\ge1-\delta
                  \quad\text{for every }d\in(0,1),\\
\Pr_{\gamma,d}(\mathsf{PASS})\le\delta
 \quad\text{for every }d\in(0,1),\ |\gamma|\le1,
                         \ \operatorname{Re}\gamma\le1-\kappa.
\end{gathered}
\tag{5.1}
$$

The counted calibration ends at this decision, before any accepted refresh
or later task. Let $F_{\rm cal}$ be the actual number of F reads up to that
cut. The gate may make an unbounded but finite number of calls on its
different runs. Any additional same-source consumer is charged separately.
INCONCLUSIVE has the same meaning as in Definition 3.6 and need not assert
nonideality. Contract (5.1) is a frequentist acceptance/rejection condition,
not a posterior probability or an exact-law assertion on a PASS tape.

**Theorem 5.2 (matching one-coordinate order for the public gate).** Every
gate satisfying (5.1) has, at each fixed $d\in(0,1)$,

$$
\begin{aligned}
\mathbb E_{1,d}[F_{\rm cal};\mathsf{PASS}]
 &\ge \mathcal B(\kappa,\delta)
 :=\frac{(1-\delta)\ln((1-\delta)/\delta)}
                 {-\ln(1-\kappa/2)},\\
\mathbb E_{1,d}[F_{\rm cal}]
 &\ge\mathcal B(\kappa,\delta),\\
\mathbb E_{1,d}[F_{\rm cal}\mid\mathsf{PASS}]
 &\ge\frac{\ln((1-\delta)/\delta)}{-\ln(1-\kappa/2)}.
\end{aligned}
\tag{5.2}
$$

Every finite ideal accepted cap obeys the last lower bound as well.
For the actual dyadic inputs

$$
h,p\ge1,\quad s\ge2,\quad
\varepsilon=2^{-p},\quad\delta=2^{-s},\quad
\kappa=\frac{\varepsilon^2}{8h^2}\le\frac1{32},
\tag{5.3}
$$

the accepted weighted mean and total ideal mean are each at least

$$
\frac38\,\kappa^{-1}\ln(1/\delta),
\tag{5.4}
$$

and the conditional mean and accepted cap are each at least
$\tfrac12\kappa^{-1}\ln(1/\delta)$. The already installed gate of
Definition 3.6 satisfies the same contract and has the simultaneous
deterministic calibration counts

$$
\begin{aligned}
M:=F_{\rm cal}&=B_0+m
       =128(s+2)+1+\frac{2(s+2)}\kappa,\\
J_{\rm cal}&=37B_0+m,\\
N_{\rm cal}&=9B_0+m,
\end{aligned}
\tag{5.5}
$$

on both accepted and inconclusive runs. In particular

$$
M\le\frac{14}{\ln2}\,\kappa^{-1}\ln(1/\delta)
\quad\text{on (5.3)}.
\tag{5.6}
$$

Thus the infimal possible ideal expected F count, ideal accepted weighted
and conditional F counts, ideal accepted cap and uniform all-run F cap
have order $\Theta(\kappa^{-1}\ln(1/\delta))$ for this gate contract,
with uniform constants on (5.3). The assertions concerning infima mean
that every lawful gate obeys the displayed lower bounds and one actual
gate attains all the displayed upper orders. They assert neither an
optimal leading constant nor an optimum for any other resource vector.

**Proof.** Fix $d$, and compare the gate at $1$ with its permitted bad
alternative $a=1-\kappa$. With $\mathcal A=\mathsf{PASS}$, contract
(5.1) gives $\alpha\ge1-\delta>\delta\ge\beta$. Corollary 4.3
ensures $\beta>0$. Consequently

$$
\ln(\alpha/\beta)\ge\ln((1-\delta)/\delta)>0,
\quad
\alpha\ln(\alpha/\beta)
 \ge(1-\delta)\ln((1-\delta)/\delta).
$$

Equations (4.7)–(4.8) prove (5.2) and its cap statement. The total mean
dominates the accepted weighted mean because all costs are nonnegative.
No nonideal expected-cost assumption has been used.

For $0<\kappa\le1$,

$$
-\ln(1-\kappa/2)
 =\int_0^{\kappa/2}\frac{du}{1-u}
 \le\frac{\kappa/2}{1-\kappa/2}\le\kappa.
\tag{5.7}
$$

For $\delta\le1/4$, $1-\delta\ge3/4$ and
$1-\delta\ge\sqrt\delta$, so
$\ln((1-\delta)/\delta)\ge\tfrac12\ln(1/\delta)$.
These estimates prove (5.4) and the conditional/cap constant.

Theorem 3.8 supplies (5.1) for Definition 3.6, uniformly in the original
$d$. Proposition 3.14 supplies precisely (5.5); its schedule always
finishes calibration, including after an early mismatch. For (5.6),
$128(s+2)\le4(s+2)/\kappa$ on (5.3), hence
$M\le7(s+2)/\kappa\le14s/\kappa$; use
$s=\ln(1/\delta)/\ln2$. Its F calibration count equals $M$ when
conditioned on acceptance, its total F mean is $M$, and its accepted
weighted mean is at most $M$. This same fixed-length gate bounds the
uniform all-run cap, without combining favorable counts from different
schedules. Taking the specified infima gives the asserted order.
$\square$

The attained upper in this comparison remains the complete construction
of §3, including its paid consumer. On an accepted run, its actual
refresh and owned task word add

$$
\Delta J=4L_0+j_f,\qquad
\Delta N=L_0+n_f,\qquad
\Delta(\hbox{g/F reads})=j_f,\qquad
L_0=2p+5,\quad j_f+n_f\le h.
\tag{5.8}
$$

The actual F subset of those later $j_f$ reads is counted in a full-run
F bill; it is not part of $F_{\rm cal}$. Equations (5.5) and (5.8)
refer to that one executed calibration/refresh/task trajectory. In
particular (5.2) also lower-bounds its full-run F expectation, but does
not make contract (5.1) necessary for every possible finite task.

Theorem 3.11 retains the **actual** calibration cells and masses in its
comparison, with accepted bound $\varepsilon P_A+2\delta$ and normalized
bound $\min\{2,\varepsilon+2\delta/P_A\}$ when $P_A>0$.
Its good-parameter comparison is to the nominal suffix at $I/3$ with
the actual reference marginal, following an actually executed refresh.
It is not a rerun of calibration at $\gamma=1$, a preparation of that
comparison state, or a uniform rare-prefix conditional guarantee.
The callable annotations and their forward/product/backward route
agreement are exactly Definition 3.12 and Theorem 3.13. The converse
adds no decoder, measurement setting or acquisition service to them.

Only the F coordinate is priced necessarily by (5.2). Every such read
uses a genuine fresh ready carrier supplied to an actual $\mathsf J$
call. The full upper bill still includes $36B_0$ unread calibration
wash carriers, $4L_0$ unread accepted refresh carriers, all measured
retired carriers, one persistent five-mode code specimen and its
untouched reference, and the $B_0+m$-bit chronological calibration tape.
The program, counters, phase/cursor, task inputs and outcomes, source
and reference bindings, grants, actual storage/backing and output copies
remain paid. If a competing policy compresses its tape, the theorem
neither grants that tape for free nor imposes the upper construction's
storage strategy on it. Counting histories in (4.4) is not an additional
record resource available to that policy.

The upper's exact nominal matrix, annotation output and scheduling bit
costs remain the separate $O(h)$, $O(h^2)$ and
$O(T\log(T+2))+O(h^2)$ bounds of Theorem 3.13 and Proposition 3.14,
plus actual input/installation/reference/output handling. The preparation,
control and readout installation, reference calibration and physical
carrier supply remain supplied premises with their own costs. Neither
the selective lower bound nor a finite program bounds lifetime storage,
precision, physical duration or energy, and no total Pareto optimum is
asserted.

## 6. The finite exact-law boundary and its asymmetric limits

**Definition 6.1 (a finite positive certificate).** Within the supplied
class (3.2), a certificate of the exact coherent law is a terminal
classical report $\mathsf{EXACT}$, computed by a legal policy from its
actual retained records, meaning $\gamma=1$. Soundness means

$$
\Pr_{\gamma,d}(\mathsf{EXACT})=0
\quad\text{for every }d\in(0,1),\ |\gamma|\le1,\ \gamma\ne1.
\tag{6.1}
$$

Every path returning this report must finish in finite time, without
a uniform depth or mean-cost requirement. Other paths may be
inconclusive or nonterminating. A positive certificate requires
$\Pr_{1,d}(\mathsf{EXACT})>0$ for at least one original $d$.
The target is the full lift $\mathcal L_1$, with the fixed outgoing
record coordinates and reference action, not just its common unread
channel or original $g$ instrument.

**Theorem 6.2 (no finite positive exact coherent-law certificate).**
No policy of Definition 6.1 is both sound and positive. More strongly,
at every fixed original $d$ and every chosen real $a\in(-1,1)$,

$$
\Pr_{a,d}(\mathsf{EXACT})=0
\quad\Longrightarrow\quad
\Pr_{1,d}(\mathsf{EXACT})=0.
\tag{6.2}
$$

This includes policies with unbounded finite stopping records and
infinite ideal expected F cost.

**Proof.** Take $\kappa=1-a\in(0,2)$ and the accepting set of finite
$\mathsf{EXACT}$ histories in (4.4). Corollary 4.3 transports the
zero probability in exactly the direction (6.2). Equivalently, every
finite accepted history with positive ideal mass has positive
alternative mass at least $q^{F(r)}p_{1,d}(r)$. Positive ideal
certification would therefore contradict soundness at this one
permitted nonideal alternative. No expectation or uniform truncation
is involved.

For the target's source correspondence, [CPW VI, Theorem
101.3](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VI.md#101-同一原交互的单制备记录锚)
identifies $\gamma=1$ in its full-matrix CP class with
$\mathcal L(X)=S_\theta XS_\theta^\dagger$ for every $X\in M_3$,
including untouched references. In this fixed installation
$\theta=\pi/4$. Its scalar anchor is
$p_+(\gamma)=(1+\omega_d\operatorname{Re}\gamma)/2$ with
$\omega_d=(2-d)/4>0$; the exact value $(6-d)/8$ forces
$\operatorname{Re}\gamma=1$, hence $\gamma=1$ in the unit disk.
Thus certifying that anchor or that full coherent lift from finite
records with the soundness in (6.1) is excluded. The CP class,
calibration and rights are still premises of this deduction, and
their truth is not inferred from a record. An authentically supplied
exact anchor is a different input from a finite acquired PASS flag.
$\square$

**Proposition 6.3 (zero-F tasks, finite refutations and infinite events).**
The preceding conclusions have the following precise limits within
the same installation.

1. Every owned finite word consisting only of $\mathsf N$ controls
   can be executed with zero F reads and with identical full output
   and successor at every $\gamma$.
2. At $\delta=1/2$, a terminating gate with ideal and nonideal PASS
   probabilities both $1/2$ uses zero F reads.
3. For the actual repeated word cycles $\mathsf J_F;\mathsf N$,
   a finite mismatch has probability zero at $\gamma=1$ and positive
   probability at each real $a\in(-1,1)$ after two cycles. The event
   that the entire infinite word is constant has probability one at
   $\gamma=1$ and zero at each such $a$. It is not a finite positive
   certificate.

**Proof.** In the first case the initial state and every control are
common across parameters; iterate $\operatorname{Ad}_N\otimes
\operatorname{id}_Z$ and the common classical updates. This proves
equality of the full successors, not just an equality of reported bits.

For the second case actually perform one $\mathsf J_g$ read and
report PASS precisely on $j=0$. Its branch probability is
$\operatorname{tr}A_0(\sigma)=1/2$ for every entrance density
matrix, since $V_0$ is unitary. The other bit gives INCONCLUSIVE,
and the real post-read state is returned. This uses one source
call, one genuine $g$ read and its stored bit, with no F or free coin.
It satisfies the boundary error $1/2$ without satisfying any
contract (5.1) with $\delta<1/2$.

For the third case use Lemma 3.7 at the actual entrance to the word,
including any earlier acquired record and its conditional state.
For real $a$ put $q_a=(1+a)/2$. The first $m$ replies are constant
with probability

$$
q_a^m+(1-q_a)^m.
\tag{6.3}
$$

At $a=1$ this is one. At $-1<a<1$ both terms are positive, and
the two-cycle mismatch has probability $2q_a(1-q_a)>0$.
The constant-prefix events decrease with $m$, and (6.3) tends
to zero at every such interior alternative. Continuity of
probability on decreasing events gives the infinite-word assertion.
Every finite constant prefix still has positive probability there.
A report based on observing no future mismatch would require an
infinite observation, outside Definition 6.1. The finite mismatch
can refute an ideal implication; it cannot certify ideality with
positive ideal probability. No mutual absolute continuity of
infinite path laws is asserted. $\square$

The classical null-event step and exponential convexity used above
are mature tools. The adaptive channel-discrimination comparison
has the mature CP-order/max-relative-entropy framework of
Wilde–Berta–Hirche–Kaur,
[*Amortized Channel Divergence for Asymptotic Quantum Channel
Discrimination*, Proposition 10, Lemma 12, Remark 13 and Lemma
14](https://arxiv.org/html/1808.01498v2): channel max-relative
entropy has a CP-order characterization, and a fixed-number
adaptive protocol obeys the corresponding divergence converse.
Here the new source-specific deduction is (4.5) through (5.4):
only the actual F branches incur a factor, the intervening allowed
maps incur none, the bound survives full disturbed/reference
successors, and summation over unbounded finite terminal leaves
gives both the selective accepted cost and the exact finite
certificate obstruction. The general CP-order or discrimination
principle is not reintroduced as a new theorem.

The existing declarations
[`finite_kraus_instrument_born_marginal`](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean),
[`word_probability_trace_representation`](../../../D5/S3/Quantum/Measurement/WordProbabilityTraceRepresentation.lean)
and [`complete_subtree_trace`](../../../D5/S3/Quantum/Recovery/FiniteLocalProtocol.lean),
with their [Born-marginal](../../../Blueprint/D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.scribe.cs),
[word-trace](../../../Blueprint/D5/S3/Quantum/Measurement/WordProbabilityTraceRepresentation.scribe.cs)
and [finite-protocol](../../../Blueprint/D5/S3/Quantum/Recovery/FiniteLocalProtocol.scribe.cs)
owners, supply the finite instrument, chronological trace and complete
finite-tree interpretation. The private trace-fold helper in the
word-trace source supplies its backward-effect step. Those facts
do not supply (4.5), a selective F count, or the passage to countably
many finite terminal leaves. The existing
[`equivalent_probability_laws_exclude_perfect_separator`](../../../D5/S3/Observer/MeasureSeparation/EquivalentMeasuresExcludePerfectSeparator.lean)
and its [owner](../../../Blueprint/D5/S3/Observer/MeasureSeparation/EquivalentMeasuresExcludePerfectSeparator.scribe.cs)
express a general null-set obstruction under mutual absolute
continuity. Here only the one-way finite-terminal implication is
needed and proved; the infinite-word example forbids promoting
it to mutual equivalence of the infinite laws.

The independent-copy attempted-pair bounds of §2 retain their own
fresh-preparation, terminal-discard, real-effect and no-surviving-
quantum-memory hypotheses. They do not price this one evolving
source, and (5.2) does not price their attempted pairs. CPW VI
§§106–110 retain their different same-carrier return interaction;
its accessible complementary information is not added to
Definition 4.1. The native known/unknown-law acquisition and
same-material transfer results in [Native Leaf Boundary
Acquisition II, §§77–79](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md#77-wlab-ord-acquiring-an-unknown-law-on-one-ordered-native-source)
also retain their rational-field, ordered-roster and literal-Read
contracts. Their acquired law or fresh-Read price does not supply
the quantum lift, and no absence of such native results is used
to justify this converse. This is a source-relative synthesis,
without a claim of worldwide priority.

The independent meanings and recovery limits of Proposition 3.15
remain exact: the spatial data are the actual code/carrier/access
cut; chronology is performed order; boundary data are the
installed complete branches and access rights; memory is the
actual retained record and callable cells. Theorems 4.2–6.2
constrain the acquired boundary-law information and its necessary
read price. They construct no inverse from a finite classical tape
to an arbitrary unknown quantum state, no new four-view mutual
recovery, no physical metric or elapsed-time readout, and no
recovery of an erased preparation, inaccessible carrier or
arbitrary past. The nominal route agreement remains the precise
finite task statement (3.29)–(3.31), on its supplied source and
retained context.

All original fixed-$G_{gc}$/original-$Q$, parked-consumer,
unchanged-initialization and final-no-Ready obligations retain
their original scopes. The common actual-apparatus bridge among
native, path, quantum and continuous installations still requires
one genuine initialization and acquisition, legal selectors and
actions, complete outputs and successors, retained callable records,
references, rights and a simultaneous resource correspondence.
Numerical inversion and likelihood bounds manufacture none of
those premises. Physical conformance and acquisition of this
stationary full-CP/readout/reference interface, general-$N$
herald/archive operation, all-raw-carrier retention,
supplied-contrast synthesis, native-to-quantum correspondence,
full four-expression recovery and unlimited-use bounds remain
separate unresolved bridges. Alpha/beta remains a candidate
foundation, not a proved universal reduction or minimum. The
gate-specific price and finite certificate boundary neither
identify the separate installations as one source nor complete
the common internal-observer objective.

## 追加锚（本行以下为增补区）

## 7. Current-public supplier reconciliation for the quantum converse

**Supplier correspondence 7.1 (the changed coherent-reconstruction source).** The current public [coherent reconstruction §36](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md#36-同一被动等待的极分解与完整原生读取的不相容)
uses the fixed five-mode $D$-frame, its polar factor and the original
complete-read menu. It proves a waiting-compatible polar structure and a
source-specific full-read effect obstruction, including a positive
total-variation separation for the displayed input pair. It does not provide
a common state--effect--instrument composition, a finite positive exact-law
certificate, or a new preparation/reference/right. The selective F-read
converse and finite exact-certificate boundary in §§4--6 therefore retain
their own fixed-DU hypotheses and are neither strengthened nor replaced by
§36.

**Supplier correspondence 7.2 (analytic current sources).** The current
public [Native Free Diffusion §§24--28](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md#24-timed-entrance-and-killed-releases-from-the-original-source)
supplies original-source causal releases, released-state accuracy and a
prospective native consumer under the exact-real timed-service and actuation
premises of Assumptions 25.1 and 26.1. The current public [attractive gluing
§35](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GLUING.md#35-实际慢共振输入有限相容修正与修正后的物理质量)
supplies a finite analytic compatibility correction and positive corrected
mass while leaving the full residual estimate open. [Appendix II §120](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#120-a-positive-quadratic-direction-on-every-original-emission-overlap)
supplies a positive quadratic direction for an original passive emission
overlap, with deterministic attainment unresolved. None of these sources
installs the fixed-DU CP/readout/reference interface, supplies a quantum
finite-bit or finite-shot bridge, or identifies the separate installations
with the present source.

**Boundary 7.3 (remaining obligations).** The quantum contribution remains a
fixed-DU selective adaptive F-read result with its supplied preparation,
reference, rights, calibration, retained record and finite callable prefix.
It does not establish physical acquisition of those interfaces, arbitrary
unknown-state reconstruction, general-$N$ herald/archive operation, a native
or continuous common apparatus, full four-view recovery, or unlimited-use
bounds. The original fixed-model and common-realization obligations retain
their exact scopes.

## 追加锚（本行以下为增补区）
