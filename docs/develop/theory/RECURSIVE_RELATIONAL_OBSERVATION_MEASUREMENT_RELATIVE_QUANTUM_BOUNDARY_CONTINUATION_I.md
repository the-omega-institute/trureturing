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
