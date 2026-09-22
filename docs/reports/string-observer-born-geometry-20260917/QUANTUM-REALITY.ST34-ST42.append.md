
---

<a id="observer-constructive-recovery-closure"></a>

# 恢复器、逻辑代数与全局运输的显式构造

## 定义 ST34.1：有限构造域及其原始数据

取非零有限维复 Hilbert 空间 $L=\mathbb C^d$、$H=\mathbb C^n$，内积为正定。矩阵伴随记为 $\dagger$，矩阵单位为 $e_{ij}=|i\rangle\langle j|$。量子通道以有限 Kraus 矩阵作为原始数据：

$$
\mathcal N(X)=\sum_{a=1}^m E_aXE_a^\dagger,
\qquad \sum_a E_a^\dagger E_a=I_d.
\tag{ST34.1}
$$

密度态满足 $\rho\ge0$、$\operatorname{tr}\rho=1$，效果满足 $0\le F\le I$，实验概率为 $\operatorname{tr}(F\rho)$。这些是本节采用的有限量子理论定义，不由以下恢复定理重新推出。有限经典记录用块对角矩阵表示；所有通道允许张量一个任意有限、未受操作的参考系统。公开仪器的每个结果对应一组 Kraus 矩阵，不把后选择作为默认操作。

对半正定矩阵 $Q$，定义 $P_Q$ 为其正本征空间投影，定义 $Q^{[-1/2]}$ 在本征值 $q>0$ 上取 $q^{-1/2}$、在零本征空间取零。该谱函数与对角化所选基无关。固定逻辑单位向量 $|0\rangle$，只用于恢复映射在原通道不可到达的补空间上的保迹扩展。

## 定理 ST34.2：由任意 Kraus 数据直接构造一个归一恢复候选

由(ST34.1)计算

$$
Q=\mathcal N(I_d)=\sum_aE_aE_a^\dagger,\qquad
P=P_Q,\qquad W=Q^{[-1/2]}.
$$

令

$$
R_a=E_a^\dagger W,
\qquad R_{\perp b}=|0\rangle\langle b|(I-P),\quad b=1,\ldots,n.
\tag{ST34.2}
$$

则这些矩阵定义一个从 $M_n$ 到 $M_d$ 的 CPTP 映射：

$$
\boxed{
\mathcal R_{\mathcal N}(X)
=\mathcal N^*(WXW)+\operatorname{tr}[(I-P)X]|0\rangle\langle0|.
}
\tag{ST34.3}
$$

此处不预先假设 $\mathcal N$ 可逆。该构造在任意有限通道上存在，但只有满足下一定理的通道被它精确反演。它是在均匀逻辑参考态下的 transpose/Petz 型恢复，相关一般构造与近似恢复背景见[ST34-BK]。

**证明。** 有限谱分解给出 $WQW=P$，于是

$$
\sum_aR_a^\dagger R_a=P,
\qquad
\sum_bR_{\perp b}^\dagger R_{\perp b}=(I-P)^2=I-P.
$$

所有分量均由显式 Kraus 矩阵给出，完全正性和保迹性随之成立。若 $v\in\ker Q$，则 $0=v^\dagger Qv=\sum_a\|E_a^\dagger v\|^2$，所以 $PE_a=E_a$，原通道输出确实支持在 $P$ 内。公式(ST34.3)用的仅是通道、其 Hilbert–Schmidt 伴随及 $Q$，因此对 Kraus 表示的酉混合不变。∎

## 定理 ST35.1：可检验的恢复充要条件与反演构造

由原始矩阵定义

$$
c_{ab}=\frac1d\operatorname{tr}(E_a^\dagger E_b),
\qquad D_{ab}=E_a^\dagger E_b-c_{ab}I_d.
\tag{ST35.1}
$$

下列三个条件等价：

$$
\boxed{
\exists\mathcal R\ {m CPTP}:\mathcal R\mathcal N=\mathrm{id}
\quad\Longleftrightarrow\quad
D_{ab}=0\quad\forall a,b
\quad\Longleftrightarrow\quad
\mathcal R_{\mathcal N}\mathcal N=\mathrm{id}.
}
\tag{ST35.2}
$$

这里等号均指全部逻辑矩阵，因而同时保留未知输入与参考系统的纠缠。充要条件属于 Knill–Laflamme 纠错理论；可逆通道的附加态正规形属于 Nayak–Sen 的既有定理。[ST27-KL][ST34-NS] 以下证明同时给出本节需要的每个构造。

**证明：必要性。** 设恢复 Kraus 为 $A_t$。复合通道的 Choi 矩阵为 $|I_d\rangle\!\rangle\langle\!\langle I_d|$，是秩一正矩阵。因此各向量 $|A_tE_a\rangle\!\rangle$ 必须与 $|I_d\rangle\!\rangle$ 共线，记 $A_tE_a=z_{ta}I_d$。由恢复保迹得

$$
E_a^\dagger E_b
=\sum_tE_a^\dagger A_t^\dagger A_tE_b
=\Bigl(\sum_t\overline{z_{ta}}z_{tb}\Bigr)I_d.
$$

取迹确定该标量正是$c_{ab}$，故$D_{ab}=0$。

**证明：充分性及实际求解。** $c$ 是 Kraus 矩阵的归一 Hilbert–Schmidt Gram 矩阵，故半正定且$\operatorname{tr}c=1$。取有限酉对角化 $V^\dagger cV=\operatorname{diag}(\lambda_j)$，令$F_j=\sum_aV_{aj}E_a$。则

$$
F_j^\dagger F_k=\lambda_j\delta_{jk}I_d.
$$

$\lambda_j=0$时$F_j=0$。正权重时令$S_j=F_j/\sqrt{\lambda_j}$，得到$S_j^\dagger S_k=\delta_{jk}I_d$。因此

$$
Q=\sum_{\lambda_j>0}\lambda_jS_jS_j^\dagger,
\qquad WF_j=S_j.
$$

对同一 Kraus 混合，候选恢复的支持部分变为$\sum_jS_j^\dagger X S_j$，故

$$
\mathcal R_{\mathcal N}\mathcal N(\rho)
=\sum_{j,k}\lambda_kS_j^\dagger S_k\rho S_k^\dagger S_j
=\sum_k\lambda_k\rho=\rho.
$$

补空间项在原通道输出上为零。最后一个条件显然给出第一个。∎

## 推论 ST35.2：公开结果的恢复器逐项构造，包括零概率结果

设公开仪器为$\mathcal I_a(X)=\sum_\ell E_{a\ell}XE_{a\ell}^\dagger$。若

$$
E_{a\ell}^\dagger E_{ak}=c^{(a)}_{\ell k}I_d,
\qquad p_a=\operatorname{tr}c^{(a)},
$$

则对每个$a$直接以$Q_a=\mathcal I_a(I)$构造(ST34.2)的恢复 Kraus，得到归一$\mathcal R_a$且

$$
\boxed{\mathcal R_a\mathcal I_a=p_a\mathrm{id}.}
\tag{ST35.3}
$$

**证明。** 充分性证明无需先将分支除以$p_a$；相同计算给出$\sum_j\lambda_j=p_a$。$p_a=0$时全部分支 Kraus 为零，$Q_a=W_a=P_a=0$，只保留显式复位通道。它与零分支的复合确实为零。公开标签间无需交叉条件；删除标签后则必须对合并后的全部 Kraus 检查(ST35.1)。∎

## 定理 ST36.1：从可逆通道提取全体逻辑观测代数

设(ST35.2)成立。对任意逻辑矩阵$A$定义

$$
\boxed{\pi(A)=W\mathcal N(A)W.}
\tag{ST36.1}
$$

则

$$
\pi(I)=P,\quad \pi(A)^\dagger=\pi(A^\dagger),\quad
\pi(A)\pi(B)=\pi(AB),\quad
[Q,\pi(A)]=0,\quad \mathcal N(A)=Q\pi(A).
\tag{ST36.2}
$$

**证明。** 采用ST35证明中实际构造的$S_j$，有$\pi(A)=\sum_jS_jAS_j^\dagger$。逐项乘法和正交性给出前三式。$Q=\sum_j\lambda_jS_jS_j^\dagger$使后两式成立。这些等式在原通道表示下由(ST36.1)唯一确定，不依赖辅助对角化的选择。∎

## 定理 ST36.2：无需选择综合征基的全局解码 Kraus

令$F_{ij}=\pi(e_{ij})$，定义$d\times n$矩阵

$$
T_b=\sum_{i=1}^d|i\rangle\langle b|F_{1i},\quad b=1,\ldots,n.
\tag{ST36.3}
$$

则

$$
\sum_bT_b^\dagger T_b=P,
\qquad
\Bigl[\sum_bT_bXT_b^\dagger\Bigr]_{ij}
=\operatorname{tr}(F_{ji}X).
\tag{ST36.4}
$$

加入$|0\rangle\langle b|(I-P)$即得完整CPTP解码$\mathcal D_\pi$。它等于(ST34.3)的恢复器。

**证明。** 矩阵单位关系$F_{ij}F_{kl}=\delta_{jk}F_{il}$给出

$$
\sum_bT_b^\dagger T_b=\sum_iF_{i1}F_{1i}=\sum_iF_{ii}=P.
$$

第$(i,j)$元为$\sum_b\langle b|F_{1i}XF_{j1}|b\rangle=\operatorname{tr}(F_{ji}X)$。另一方面，$\mathcal N^*(WXW)$的第$(i,j)$元也是$\operatorname{tr}(W\mathcal N(e_{ji})WX)$。两者及其补空间项相同。∎

## 定理 ST37.1：参数族的光滑恢复与确定的综合征丛

令$B$为紧致光滑参数流形。设$x\mapsto\mathcal N_x:M_d\to M_n$是光滑通道族，每一点满足(ST35.2)，且$Q_x=\mathcal N_x(I)$的秩恒为$kd$。则$P_x,W_x,\pi_x$及$\mathcal D_{\pi_x}$均全局光滑。

记$E_x=\operatorname{Ran}P_x$，定义

$$
F_x=\operatorname{Ran}\pi_x(e_{11}).
$$

它是秩$k$光滑子丛。映射

$$
\boxed{
\Theta_x:F_x\otimes\mathbb C^d\longrightarrow E_x,
\qquad v\otimes|i\rangle\longmapsto\pi_x(e_{i1})v
}
\tag{ST37.1}
$$

是全局光滑的酉丛同构。令$\sigma_x=Q_x|_{F_x}$，则$\sigma_x>0$、$\operatorname{tr}_{F_x}\sigma_x=1$，并有

$$
\boxed{
\mathcal N_x(\rho)=\Theta_x(\sigma_x\otimes\rho)\Theta_x^\dagger.
}
\tag{ST37.2}
$$

**证明。** 恒秩与紧致性使$Q_x$的正谱与零之间有共同正距离。在包围正谱且避开零的适当复平面围道上，

$$
P_x=\frac1{2\pi i}\oint(zI-Q_x)^{-1}dz,\quad
W_x=\frac1{2\pi i}\oint z^{-1/2}(zI-Q_x)^{-1}dz.
$$

矩阵逆与围道微分给出光滑性；局部围道可拼接，因为定义的是相同谱函数。无需选择全局本征向量。$\pi_x$和ST36的解码随后光滑。矩阵单位给出

$$
\langle F_{i1}v,F_{j1}w\rangle=\delta_{ij}\langle v,w\rangle,
\quad\sum_iF_{i1}F_{1i}=P.
$$

所以$\Theta$等距且满。$Q$与全部$F_{ij}$交换，故$\Theta^\dagger Q\Theta=\sigma\otimes I_d$。由于$\operatorname{tr}Q=d$，有$\operatorname{tr}\sigma=1$。最后用$\mathcal N(\rho)=Q\pi(\rho)$。∎

恒秩是一项足以保障该统一光滑公式的条件；它不是所有光滑恢复族存在的必要条件。秩改变时，不允许无证明地微分伪逆。

## 定理 ST37.2：不选全局向量框也能构造光滑实验扩张

在ST37.1条件下，采用未归一化Choi矩阵

$$
J_x=\sum_{ij}e_{ij}\otimes\mathcal N_x(e_{ij}).
$$

令$A_\mu(x)$为$J_x^{1/2}$第$\mu$列的逆向量化，使用$\operatorname{vec}A=\sum_i|i\rangle\otimes A|i\rangle$约定。则

$$
\mathcal N_x(\rho)=\sum_{\mu=1}^{dn}A_\mu(x)\rho A_\mu(x)^\dagger,
\quad\sum_\mu A_\mu^\dagger A_\mu=I_d.
$$

相应$V_xv=\sum_\mu A_\mu(x)v\otimes|\mu\rangle$是显式光滑Stinespring等距映射。

**证明。** Choi平方根乘其伴随恢复$J_x$，矩阵元展开给出通道和保迹恒等式。由ST35的正交错误分解，$\operatorname{rank}J_x=k$恒定，故与ST37.1相同的正谱论证给出$J_x^{1/2}$光滑。∎

这是一组可冗余的全局Kraus矩阵；其存在不产生原秩$kd$子丛的一组全局向量基。环境维数$dn$与访问/复位操作在构造中明列。

## 定理 ST38.1：全局可恢复逻辑维数的整除障碍

在闭定向曲面$\Sigma$上，若一个固定全局逻辑空间$\mathbb C^d$具有ST37的光滑精确可恢复编码，物理支持丛为$E$，则

$$
\boxed{\operatorname{rank}E=kd,\qquad c_1(E)=d\,c_1(F).}
\tag{ST38.1}
$$

所以$d$必须同时整除$\operatorname{rank}E$和第一Chern数。

**证明。** 秩由(ST37.1)。取$F$的局部酉框及过渡函数$g_{\alpha\beta}$；通过$\Theta$，$E$的过渡函数为$g_{\alpha\beta}\otimes I_d$，其行列式为$(\det g_{\alpha\beta})^d$。因此行列式线丛的第一Chern类乘以$d$。∎

这个必要条件针对一个全局已识别的逻辑矩阵代数及指定物理支持；它没有声称仅凭这两个整数就足以分类任意参数流形上的全部编码。

## 定理 ST38.2：处处有隙、处处可编码，却没有全局可恢复的二态寄存器

沿用ST25规范，$p(\boldsymbol n)=(I+\boldsymbol n\cdot\boldsymbol\sigma)/2$在$S^2$上是$C_1=-1$的秩一投影。令

$$
P_{\rm bad}(\boldsymbol n)=p(\boldsymbol n)\oplus1\in M_3,
\qquad H_{\rm bad}=\Delta(2P_{\rm bad}-I_3),\quad\Delta>0.
$$

其支持秩为二、第一Chern数为$-1$，Hamiltonian能隙恒为$2\Delta$。每个点可选一个秩二等距编码，但不存在以该支持为像、来自同一个逻辑量子比特的全局光滑可恢复通道族。

**证明。** 直和一条平凡线不改变$C_1$，投影Hamiltonian直接给出能谱。若有全局通道，则ST38.1要求$2\mid-1$，矛盾。逐点有限Hilbert空间当然同构于$\mathbb C^2$，故局部存在与全局不可能并不冲突。∎

作为严格对照，ST32的$P_{\rm good}=p\otimes I_2$也为秩二、能隙$2\Delta$，但$C_1=-2$；$\mathcal E(\rho)=p\otimes\rho$与偏迹确实实现全局恢复。非零Chern数排除向量框，与(ST38.1)排除全局逻辑通道，是不同强度的障碍。

## 定理 ST39.1：只由逻辑矩阵单位构造运输生成元

沿有限时间区间，设$F_{ij}(t)=\pi_t(e_{ij})$为$C^1$矩阵族，满足

$$
F_{ij}F_{kl}=\delta_{jk}F_{il},\quad F_{ij}^\dagger=F_{ji},\quad
P=\sum_iF_{ii}.
$$

定义

$$
Z=\frac1d\sum_{ij}\dot F_{ij}F_{ji},
\qquad\boxed{K=Z-P\dot P.}
\tag{ST39.1}
$$

则

$$
\boxed{K^\dagger=-K,\qquad [K,F_{ij}]=\dot F_{ij},\qquad[K,P]=\dot P.}
\tag{ST39.2}
$$

$d=1$时，$K=[\dot P,P]$，恢复通常的投影平行运输生成元。一般$d$时，式(ST39.1)同时固定内部逻辑代数的运输，不只固定支持投影。

**证明。** 微分$\sum_{ij}F_{ij}F_{ji}=dP$得$Z+Z^\dagger=\dot P$。又微分$P^2=P$得$P\dot P+\dot PP=\dot P$，故$K+K^\dagger=0$。

对固定$k,l$，矩阵单位和它的导数给出

$$
ZF_{kl}=\frac1d\sum_j\dot F_{kj}F_{jl},
\quad
F_{kl}Z=\frac1d\sum_j\dot F_{kj}F_{jl}-\dot F_{kl}P.
$$

因此$[Z,F_{kl}]=\dot F_{kl}P$。由$P\dot PP=0$及$PF_{kl}=F_{kl}P=F_{kl}$，有$[P\dot P,F_{kl}]=-F_{kl}\dot P$。微分$F_{kl}P=F_{kl}$后得到$[K,F_{kl}]=\dot F_{kl}$。求和得投影式。∎

定义全局酉运输$G(t)$为下述显式收敛级数：

$$
G(t)=I+\sum_{m\ge1}\int_{0\le t_m\le\cdots\le t_1\le t}
K(t_1)\cdots K(t_m)\,dt_m\cdots dt_1.
\tag{ST39.3}
$$

若$\|K\|\le M$，第$m$项范数至多$(Mt)^m/m!$，所以一致收敛，可积分求导得$\dot G=KG$、$G(0)=I$。$\partial_t(G^\dagger G)=0$给出酉性；微分$G^\dagger F_{ij}G$得

$$
\boxed{F_{ij}(t)=G(t)F_{ij}(0)G(t)^\dagger.}
\tag{ST39.4}
$$

唯一性由同一积分方程的迭代余项界或Gronwall不等式得到。这里已经实际构造运输，不另外假设存在一条正确的holonomy。

## 定理 ST40.1：同时实现任意规定逻辑动力学与移动编码的物理Hamiltonian

在ST37及ST39的一条时间路径上，给定连续逻辑Hermitian矩阵$h_L(t)$、常数$\hbar>0$和$\Delta>0$。定义

$$
\boxed{
H_{\rm phys}(t)=i\hbar K(t)+\pi_t(h_L(t))+\Delta(I-P_t).
}
\tag{ST40.1}
$$

逻辑酉$V_L$由$i\hbar\dot V_L=h_LV_L$的同类Dyson级数构造。令

$$
V(t)=G(t)\left[\pi_0(V_L(t))+e^{-i\Delta t/\hbar}(I-P_0)\right].
\tag{ST40.2}
$$

则$V$酉，满足$i\hbar\dot V=H_{\rm phys}V$、$V(0)=I$，且

$$
\boxed{\mathcal D_{\pi_t}\circ\operatorname{Ad}_{V(t)}\circ\mathcal N_0
=\operatorname{Ad}_{V_L(t)}.}
\tag{ST40.3}
$$

**证明。** $K$反Hermitian，故$H_{\rm phys}$Hermitian。方括号在$P_0$和其补空间上分别酉，因此整体酉。求导并用(ST39.4)验证Schrödinger方程。令$\widetilde Q_t=GQ_0G^\dagger$，它与$\pi_t(M_d)$交换，并有$\operatorname{tr}(F_{11}(t)\widetilde Q_t)=1$。于是输出为

$$
\widetilde Q_t\,\pi_t(V_L\rho V_L^\dagger).
$$

应用(ST36.4)，或者使用$\Theta_t$下的偏迹，即得到(ST40.3)。实际运输后的综合征态无需恰好等于预先参数化的$\sigma_t$，只需它仍在综合征因子且迹一。∎

这是主动控制的明确数学实现；原系统若不提供$H_{\rm phys}$，不能把它视为自然出现。所增加的几何项满足可直接读出的上界

$$
\|i\hbar K\|\le\hbar\left(\frac1d\sum_{ij}\|\dot F_{ij}\|+\|\dot P\|\right).
$$

它不包含真实设备的控制带宽、能耗或局域可实现性。无跃迁驱动的普遍思想归于既有工作。[ST19-Berry]

若一条闭路上$\pi_T=\pi_0$且$h_L=0$，则$G(T)$与全部逻辑矩阵单位交换。在$E_0\cong F_0\otimes\mathbb C^d$中，闭路作用具有$V_F\otimes I_d$的形式：综合征可以发生非平凡运输，逻辑通道仍为恒等。这个结论使用了整个逻辑代数的运输，不能只由$P_T=P_0$推出。

## 定理 ST40.2：规定的全部有限逻辑实验都有显式物理实现

给定任一逻辑仪器$\{L_{a\ell}\}$、$\sum_{a\ell}L_{a\ell}^\dagger L_{a\ell}=I_d$，在参数$t$处构造物理Kraus

$$
\widetilde L_{a\ell}=\pi_t(L_{a\ell}),\qquad
\widetilde L_\perp=I-P_t.
\tag{ST40.4}
$$

最后一项附加一个单独的失败结果。从支持$P_t$内的编码态出发，该结果概率为零，其余分支的逻辑统计与原仪器完全相同。用(ST40.1)连接不同参数时刻，则任意有限次按已有经典记录选择操作的逻辑协议，都有相应的完整物理协议；所有联合记录及最终解码的未归一化分支态相等。

**证明。** $\sum\widetilde L^\dagger\widetilde L=P_t$，补项给$I-P_t$，故物理仪器归一。以$\widetilde Q\pi_t(\rho)$为支持态、$\widetilde Q$在交换子代数内且综合征迹一时，每一分支成为

$$
\widetilde Q\,\pi_t\left(\sum_\ell L_{a\ell}\rho L_{a\ell}^\dagger\right).
$$

ST36的解码读取括号内矩阵。运输按ST40.1保留这一形式。对有限协议长度归纳即可；固定一条经典历史后各控制都已确定，因此证明覆盖自适应选择。张量参考系统时矩阵恒等式不变。∎

本命题构造所规定实验的实现，未声称原物理模型中任意额外操作都会保持逻辑。增加新的操作，需要重新检验对应通道。

## 定理 ST41.1：一般酉错误下，公开记录必须区分射影酉作用

给定输入无关$p_j\ge0$、$\sum_jp_j=1$，逻辑酉$V_j$及经典记录核$T(r|j)$。可访问仪器为

$$
\mathcal M_r(\rho)=\sum_jp_jT(r|j)V_j\rho V_j^\dagger.
$$

存在依赖公开$r$的确定性恢复，使每个结果后的逻辑通道为$q_r\mathrm{id}$，当且仅当每个$r$内所有正权重分支的$V_j$只相差整体相位。

**证明。** 对分支Kraus$E_{rj}=\sqrt{p_jT(r|j)}V_j$应用(ST35.2)的逐结果版本。交叉乘积是非零标量乘$V_j^\dagger V_k$，它为恒等倍数当且仅当两酉相差单位相位。充分性时选择一个受支持$V_j$的逆作分支恢复。∎

对于确定性记录，最少结果数是正概率分支中不同共轭通道$\operatorname{Ad}_{V_j}$的数量。一般维数下本命题只解决零误差条件；非零最优钻石误差没有被ST30的量子比特相位公式自动覆盖。

## 定理 ST41.2：普通通道数据无法唯一补出相干控制的相位

不存在仅依赖酉共轭通道$\operatorname{Ad}_V$的规则，能对每个酉代表$V$都返回受控酉$C_V=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes V$的共轭通道。

**证明。** $\operatorname{Ad}_I=\operatorname{Ad}_{-I}$，但$C_I=I$，$C_{-I}=Z\otimes I$。在控制输入$|+\rangle$上，输出分别为$|+\rangle$和$|-\rangle$，正交可分。相同输入数据不可能唯一决定两个不同输出通道。∎

该简单相位障碍与已有未知操作受控化禁限定理相容。[ST34-Control] 它并不禁止已知物理实现的相干控制：提供带相位的Stinespring实现、参考路径和控制器后，就已增加了必要数据。ST40的闭合针对明确的经典自适应仪器语言；把两条路径相干叠加时，应把路径参考及其相位实现一起加入原始数据，不能从已被删除的信息中补出它。

## 定理 ST42.1：有限观察者理论的构造性闭合

给定ST34中的通道数据，以及需要参数变化时ST37的光滑恒秩通道族，执行以下有限谱运算与显式积分构造：

1. 计算全部$D_{ab}$。它们全零时，ST34给出归一恢复器，ST35证明其正确性；某项非零时，ST35给出不存在任何精确CPTP逆的数学见证。
2. 从$Q,W$计算$\pi$与$F_{ij}$，ST36给出逻辑观测量及无需综合征基的解码Kraus。
3. 在参数族中用谱函数构造全局恢复，并用$F=\operatorname{Ran}F_{11}$及$\Theta$构造全局因子化。ST38提供不允许的逻辑维数/支持拓扑组合的明确排除条件。
4. 沿规定参数路径由(ST39.1)计算$K$、由收敛级数计算$G$，再用(ST40.1)与(ST40.4)实现规定的逻辑演化和仪器。

这些等式以精确矩阵数据表述；数值容差不会证明等式精确成立，本文不提供一般实数oracle的有限判等程序。

由这些实际构造得到的全部有限联合记录、逻辑恢复和路径运输，在同一正Hilbert空间模型中相容。闭合不以“存在一个正确恢复器”“存在一个正确全局框”“存在一个正确控制”为额外输入。

**证明。** 第1项的存在与拒绝均由ST35的等价关系，而非未经验证的求解器状态。第2项的乘法、伴随和保迹关系由ST36。第3项通过谱围道和矩阵单位构造，不调用未指定的全局本征向量选择。第4项通过收敛级数和显式Kraus给出存在与归一性，联合记录由ST40.2的归纳证明。∎

## 定理 ST42.2：上述闭合不能唯一选择时空引力动力学

ST34–ST42的有限通道前提不唯一决定Lorentz时空维数、局域传播算子、曲率耦合或Einstein反作用方程。

**证明。** 同一有限量子通道及同一参数路径可被张量加入一个完全解耦的、具有任意有限能谱的量子系统，而不改变指定实验的任何矩阵。更具体地，在平直背景的标量有效场子模型中，$D_g=-\nabla^2I+\xi R_gI+\mathsf M$于$R_g=0$不含$\xi$；不同$\xi$具有相同该背景响应，却具有ST7中不同的线性曲率贡献。故当前数据至少对$\xi$不可识别，更不能唯一决定完整几何动力学。∎

因此，本节完成的是已明确原始数据之有限理论的演绎闭合。相对论与弦微观实现需要提供各自的物理态空间、局域性、约束和背景/反作用作用量；这些不是本节已经构造的有限矩阵对象。将它们纳入同一物理理论时，必须给出实际相容实现，不能以有限模型的闭合代替自然界的理论选择。

## ST34–ST42 文献

[ST34-BK]: https://arxiv.org/abs/quant-ph/0004088 "H. Barnum and E. Knill, Reversing quantum dynamics with near-optimal quantum and classical fidelity, J. Math. Phys. 43, 2097–2106 (2002), DOI 10.1063/1.1459754. Prior transpose-channel construction; the general approximate-fidelity theorem is not reproved here."
[ST34-NS]: https://arxiv.org/abs/quant-ph/0605041 "Ashwin Nayak and Pranab Sen, Invertible Quantum Operations and Perfect Encryption of Quantum States, Quantum Information and Computation 7(1&2), 103–110 (2007), DOI 10.26421/QIC7.1-2-6. Theorem 2.1 and its proof give the classical reversible-channel normal form."
[ST34-Control]: https://arxiv.org/abs/1309.7976 "Mateus Araújo, Adrien Feix, Fabio Costa and Časlav Brukner, Quantum circuits cannot control unknown operations, New J. Phys. 16, 093026 (2014), DOI 10.1088/1367-2630/16/9/093026. General no-control result; ST41.2 gives its elementary phase obstruction."

---
