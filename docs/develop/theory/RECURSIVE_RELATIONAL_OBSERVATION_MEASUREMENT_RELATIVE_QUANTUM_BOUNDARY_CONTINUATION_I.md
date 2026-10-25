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
