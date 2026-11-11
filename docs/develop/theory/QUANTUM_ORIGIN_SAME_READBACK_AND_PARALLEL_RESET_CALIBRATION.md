# 同一实际读回与并行全重置的概率校准

本卷给出条件性的纸面数学论证。既有比较、分类、方向规则及其文献条件均沿用 [Part IV《量子起源：内生切分图谱与离散重构边界 IV》](QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_IV.md) §§66–69；下文标有「Part IV」的章节、定义、定理与公式均指该卷，本卷的条目和公式使用第 1 章编号。

## 1. 同一实际读回与并行全重置的概率校准

### 1.1 完整保留的比较与组合前件

**定义 1.1（前交叉系统与原始迹）。** 本章完整保留Part IV 定义 66.1、Part IV 命题 66.2 的前 C13 条件及其条件纸面桥，具体包括：

1. 每个 $X=A,D,E$ 非零、有限维，具有闭尖生成锥、严格正归一化、完整紧态基及全部对偶效应。比较按 Part IV (66.1) 的最少确认定义，对每个纯参照、每个有限纯态族和每组概率权重满足完整有限 $S$，即 Part IV (66.2)，而不只要求纯端点互反。
2. 完整 $S$ 到一般有限 EJA 及忠实归一化的桥恰为 Part IV §66.1、Part IV (66.3) 所引条件纸面结果；项目性、共同框架及滤波纯性的义务保持其原范围，不新增独立 Jordan 输入。原态、原效应、原比较单位和配对均保留，每个本原元迹一。
3. 唯一原始映射仍是实双线性 $L:D\times A\to E$ 和同一个实线性 $p:E\to D$，分别在整个 $D_+\times A_+$、整个 $E_+$ 上正，包括全部纠缠正元。原参考是 $\omega=1_D/\operatorname{Tr}_D1_D$。
4. 全部实际内部映射仍按 Part IV (66.5) 定义：$\mathcal B=pL$、$K(a)=\mathcal B(\omega,a)$、$M(a,b)=\mathcal B(K(a),b)$、$J=M(-,1_A)$、$H=L(-,1_A)$、$B_1=pH$、$Q(a,b,c)=L(M(a,b),c)$、$U=M(1_A,1_A)$。形成 $M$ 的两次读回是同一个原 $p$，没有独立供应的准备。
5. 保留 $\operatorname{span}_{\mathbb R}M(A,A)=D$、$\operatorname{span}_{\mathbb R}L(D,A)=E$，以及 Part IV (66.6) 的全部 $D_J,D_H,Z$：两个单位切片保持正交正元的零比较，$D_H$ 覆盖整个 $D_+$，而 $B_1M(a,b)=\operatorname{Tr}_A(a)Jb$ 对全部实输入成立。

这里不预加 C13、范数校准、原始保单位或保迹。直接使用Part IV 定理 66.3–66.7 的分类及完整逆向。在其保原迹坐标中，所有有序块均存在：

$$
A=\bigoplus_iH_{n_i}(\mathbb C),\quad
D=\bigoplus_{i,j}H_{n_in_j}(\mathbb C),\quad
E=\bigoplus_{i,j,k}H_{n_in_jn_k}(\mathbb C),\quad n=\sum_i n_i>0.
$$

扇区集有限非空，$n_i\ge1$；迹是各完整矩阵块的普通迹之和。正定 $u_{ij}\in H_{n_j}$、$g_{ijk}\in H_{n_k}$ 和有序位 $\varepsilon_{ij},\delta_{ijk}$ 满足 Part IV (66.20)，以及已由原始内部构造推出的逆迹平衡

$$
\sum_{i,j}n_i\operatorname{Tr}(u_{ij}^{-1})=n^2.
\tag{1.1}
$$

本章始终使用 Part IV (66.16) 的实际加权映射

$$
\begin{aligned}
M(a,b)_{ij}&=a_i\otimes\sqrt{u_{ij}}b_j^{T^{\varepsilon_{ij}}}\sqrt{u_{ij}},\\
Q(a,b,c)_{ijk}&=a_i\otimes\sqrt{u_{ij}}b_j^{T^{\varepsilon_{ij}}}\sqrt{u_{ij}}
 \otimes\sqrt{g_{ijk}}c_k^{T^{\delta_{ijk}}}\sqrt{g_{ijk}}.
\end{aligned}
\tag{1.2}
$$

它们区别于辅助归一化接口 $F,N$。实际 $p$ 仍是 Part IV (66.17) 的唯一加权读回，全部内部映射仍是 Part IV (66.18)，不将 $p$ 换成另选的信道。

### 1.2 由乘积指定的唯一全重置

**定义 1.2（固定局部重置及其实际并行延拓）。** 事先固定一个扇区 $j_0$ 和其中任意 $\sigma\ge0$、$\operatorname{Tr}\sigma=1$。令 $\rho_0\in A$ 仅在 $j_0$ 块等于 $\sigma$，并置

$$
R(a)=\operatorname{Tr}_A(a)\rho_0,\qquad
q_2=M(\rho_0,\rho_0),\qquad q_3=Q(\rho_0,\rho_0,\rho_0).
$$

允许 $\sigma$ 具有任意秩。指定实际二份、三份重置的乘积关系为

$$
\begin{aligned}
R_2M(a,b)&=M(Ra,Rb),\\
R_3Q(a,b,c)&=Q(Ra,Rb,Rc)\qquad(a,b,c\in A).
\end{aligned}
\tag{1.3}
$$

Part IV 命题 66.2 的可逆实线性化给出存在性：

$$
R_2=\widetilde M(R\otimes R)\widetilde M^{-1},\qquad
R_3=\widetilde Q(R\otimes R\otimes R)\widetilde Q^{-1}.
\tag{1.4}
$$

两条实张成又使 $Q(A,A,A)$ 实张满 $E$，因此 (1.3) 唯一确定整个 $D,E$ 上的映射，包括纠缠输入。实张成不表示正元皆可分离。

这两个实际映射的全空间公式为

$$
\begin{gathered}
R_m(X)=\operatorname{Tr}(V_mX)q_m\quad(m=2,3),\\
(V_2)_{ij}=I_i\otimes u_{ij}^{-1},\qquad
(V_3)_{ijk}=I_i\otimes u_{ij}^{-1}\otimes g_{ijk}^{-1}.
\end{gathered}
\tag{1.5}
$$

证明逆迹公式时，在自然 Hermitian 张量坐标中，将实际线性化写成 $\operatorname{Ad}_{S_m}P_m$。这里 $P_2$ 的块为 $\mathrm{id}_i\otimes T_j^{\varepsilon_{ij}}$，$P_3$ 的块为 $\mathrm{id}_i\otimes T_j^{\varepsilon_{ij}}\otimes T_k^{\delta_{ijk}}$；$S_2,S_3$ 分别是 Part IV (66.15) 的 $A_{ij},C_{ijk}$。其逆的顺序是 $P_m\operatorname{Ad}_{S_m^{-1}}$，而 $\operatorname{Tr}(P_mY)=\operatorname{Tr}Y$，故

$$
\operatorname{Tr}(\widetilde M^{-1}X)=\operatorname{Tr}(S_2^{-2}X),\qquad
\operatorname{Tr}(\widetilde Q^{-1}X)=\operatorname{Tr}(S_3^{-2}X).
$$

将局部张量重置 $Y\mapsto\operatorname{Tr}(Y)\rho_0^{\otimes m}$ 代入 (1.4)，即得 (1.5)。逆映射先撤合同、再转置，最后的总迹消去该转置；$V_2,V_3$ 不再额外转置，也没有交换同一腿上的非交换矩阵。

由 (1.2)，$q_m$ 是非零正元；此结论包括纯态、中间秩和满秩 $\sigma$，不使用 $\sigma^{-1}$。$V_m>0$。直接复用 Part IV (69.14) 的正泛函乘正输出接口及 [Watrous 定理 2.22、2.26](../../../Library/Quantum/watrous2018theory.md#complete-channel-representations)，(1.5) 的复线性延拓是 CP，且令 $a_m=\operatorname{Tr}q_m>0$，有

$$
R_m\text{ 在全部实际态上 TP}
\quad\Longleftrightarrow\quad a_mV_m=1_{D\text{ 或 }E}.
\tag{1.6}
$$

这是一条完整算子等式，只检查重置自身的某个输出态不能代替它。CP 在此是矩阵映射性质，不证明重置的物理可用性，也不要求 $\widetilde M^{-1},\widetilde Q^{-1}$ 为正。

### 1.3 同一读回使一个重置条件充分

**定理 1.3（同数据的操作性校准等价）。** 在定义 1.1 的全部条件下，对任意事先固定的定义 1.2 重置，下列条件等价：

$$
\begin{aligned}
& p\text{ 在整个 }E\text{ 上 TP，且 }R_2\text{ 在整个 }D\text{ 上 TP};\\
& p\text{ 在整个 }E\text{ 上 TP，且 }R_3\text{ 在整个 }E\text{ 上 TP};\\
& u_{ij}=I_j\ (\forall i,j),\qquad g_{ijk}=I_k\ (\forall i,j,k).
\end{aligned}
\tag{1.7}
$$

这些是同一个实际 $A,D,E,L,p$ 上的等价条件。此时另一重置也 TP，两个重置均 CPTP，且任意总迹一局部态 $a,b,c$ 都满足 $\operatorname{Tr}_E Q(a,b,c)=1$；后两项无需另设为假设。

证明。首先复用 Part IV (66.8) 在全部实输入上的恒等式

$$
pQ(a,b,c)=\operatorname{Tr}_A(a)M(b,c).
\tag{1.8}
$$

取任意迹一 $a_0$，则 $pQ(a_0,b,c)=M(b,c)$；$M$ 实张成 $D$，故实际 $p:E\to D$ 线性满射。又因 $R$ 局部保迹，(1.3)、(1.8) 在每个 $Q$ 乘积上给出

$$
\begin{aligned}
pR_3Q(a,b,c)&=\operatorname{Tr}(a)M(Rb,Rc)\\
&=R_2pQ(a,b,c).
\end{aligned}
$$

由 $Q$ 实张成，得到整个空间的交换关系 $pR_3=R_2p$。若原 $p$ TP，则对每个 $X\in E$，

$$
\operatorname{Tr}_E(R_3X)-\operatorname{Tr}_EX
=\operatorname{Tr}_D(R_2pX)-\operatorname{Tr}_D(pX).
\tag{1.9}
$$

因此 $R_2$ TP 蕴含 $R_3$ TP；反向对任意 $Y\in D$ 由满射取 $pX=Y$，也得 $R_2$ TP。不需要正右逆，也不使用 $p$ 的 CP。这个迹下降步骤只是有限维线性满射与交换关系的直接应用。

现由 $R_2$ TP 及 (1.6)，在每个有序块有 $u_{ij}=a_2I_j$。将其代入保留的 (1.1)，得 $n^2=n^2/a_2$，所以 $a_2=1$、全部 $u_{ij}=I_j$。此时实际二元公式准确地是

$$
M(b,c)_{jk}=b_j\otimes c_k^{T^{\varepsilon_{jk}}}.
\tag{1.10}
$$

第一因子 $b_j$ 不转置。固定任意有序 $i,j,k$，令 $a,b,c$ 分别是只在这些扇区支撑的迹一正元。原 $p$ TP 及 (1.8) 给

$$
\operatorname{Tr}(g_{ijk}c_k^{T^{\delta_{ijk}}})
=\operatorname{Tr}_EQ(a,b,c)
=\operatorname{Tr}_DpQ(a,b,c)
=\operatorname{Tr}_DM(b,c)=1.
$$

遍历 $k$ 块的全部密度矩阵，迹配对分离 Hermitian 矩阵，故 $g_{ijk}^{T^{\delta_{ijk}}}=I_k$，亦即 $g_{ijk}=I_k$。

反向，全部 $u,g$ 为单位时，Part IV (66.15)、Part IV (66.17) 给实际 $p=p_0$，它按Part IV 命题 66.2 保迹；这只识别原有映射。转置保持迹，故 $a_2=a_3=1$、$V_2=1_D,V_3=1_E$，(1.6) 给两个重置 TP。对任意跨扇区混合的迹一 $a,b,c$，直接取 (1.2) 的总迹得

$$
\operatorname{Tr}_EQ(a,b,c)
=\sum_{i,j,k}\operatorname{Tr}a_i\operatorname{Tr}b_j\operatorname{Tr}c_k=1.
$$

所有步骤逐块成立，不要求等维、标签互异、非标量扇区或 $\sigma$ 满秩；总维数一也包括在内。$\square$

同一定义域上的既有迹分类可直接对接：按 Part IV (67.4) 记 $\delta=\operatorname{Tr}_E(H1_D)$、$\gamma=\operatorname{Tr}_D(p1_E)$，此标量 $\delta$ 与方向位 $\delta_{ijk}$ 不同。由 (1.6)、(1.1) 及Part IV 定理 67.6，

$$
R_2,R_3\text{ 均 TP}
\ \Longleftrightarrow\ u_{ij}=I_j,\ g_{ijk}=tI_k\text{，同一 }t>0
\ \Longleftrightarrow\ \delta\gamma=n^6.
$$

其中 $\delta=tn^3,\gamma=n^3/t$，而原 $p$ 的迹尺度为 $1/t$；原 $p$ TP 恰固定 $t=1$。由Part IV 定理 67.7，(1.7) 也恰是既有 $\delta+\gamma\le2n^3$ 的校准类。这复用已有共同尺度与联合校准分类，不另作静态分类或独立公理数的结论。

### 1.4 两个概率条件与方向条件的删除边界

**命题 1.4（保留完整前件的必要区分）。** (1.7) 中删除原 $p$ TP，或删除所列重置 TP，都不能推出单位权重；保留全部概率校准仍不能推出 C13。

证明。删除原 $p$ TP 时，在任一普通直和张量模型取零方向位、$u_{ij}=I_j$、$g_{ijk}=tI_k$，$t>0,t\ne1$。逆迹平衡成立，Part IV 定理 66.7 给完整原始系统。$q_3$ 乘 $t$、$V_3$ 乘 $1/t$，故两个重置均 TP，但实际 $p$ 是普通首腿偏迹求和的 $1/t$ 倍。其迹尺度不是一。

删除重置 TP 时，取两个标量扇区、零方向位，并令

$$
u_{ij}=s_{ij},\qquad
s=\begin{pmatrix}2&2\\2/3&2/3\end{pmatrix},\qquad
g_{ijk}=s_{jk}/s_{ij}.
\tag{1.11}
$$

逆迹和为 $1/2+1/2+3/2+3/2=4=n^2$；由 Part IV (66.17)，实际 $p$ 恰是 $(pz)_{jk}=\sum_i z_{ijk}$，所以在整个 $E$ 上正且 TP。Part IV 定理 66.7 保证同一 $p$ 两次及其余全部前件。取 $\rho_0=e_1$，则 $q_2=2e_{11},q_3=2e_{111}$，而

$$
R_2(e_{22})=3e_{11},\qquad R_3(e_{i22})=3e_{111}\quad(i=1,2).
$$

两个实际重置的这些迹一输入都产生总迹三，故均非 TP。

最后直接取Part IV 命题 66.11 的单位 qubit 模型 $\varepsilon=1,\delta=0$。原 $p$ 在整个锥上正且 TP，两个重置由 (1.5)–(1.6) 均 CPTP，但原 Part IV (66.39) 的 13 插入在端点 Bell 投影上仍有特征值 $-1/2$。这里使用原式插入的未归一化中间单位。概率校准没有排除相对转置错误。$\square$

### 1.5 完整方向预选与有限量子对应

**推论 1.5（带完整 Bell 条件的同数据候选）。** 在定义 1.1 全部条件上，增加 (1.7) 的任一操作性条件，再保留Part IV 定义 67.10、Part IV 定义 68.3 的完整模型依赖预选规则与整个输出正性，则得到Part IV 定理 67.11 的同一实际有限静态量子结构。

证明。定理 1.3 先给单位权重，故 $C_D=C_E=\mathrm{id}$、$F=M$；此时Part IV 定理 67.7 的同数据校准条件齐备。预选规则仍只读取 $A,D$ 的比较几何、预定标签及基和实际 $M$，在每个有序非标量端点对 $(i,k)$ 的两维子空间取 Bell 投影 $b_{ik}$，用初始正规形 Part IV (68.14) 的 $V_{ik}$ 送回实际块，得到 $\beta_{ik}$。令 $r$ 为这些有序对的数目，并取

$$
\sigma_*=\begin{cases}r^{-1}\sum_{(i,k)}\beta_{ik},&r>0,\\1_D/n^2,&r=0.\end{cases}
$$

所有同维而不同标签的块仍分开；规约在测试前固定，不读取 $Q,I_{13}$ 或输出。在一般未校准系统中须按 Part IV (68.15) 使用 $\rho_*=C_D\sigma_*/\operatorname{Tr}(C_D\sigma_*)$；这里单位权重使它正好等于 $\sigma_*$。要求的额外条件完整地是

$$
I_{13}(\sigma_*)\in E_+,\qquad
I_{13}=\widetilde{\mathcal T}\widetilde M^{-1},\quad
\mathcal T(a,c)=Q(a,1_A,c).
\tag{1.12}
$$

它覆盖每个中间扇区，包括标量旁观者，要求整个输出 PSD。由Part IV 定理 68.4 或Part IV 定义 67.10 所用Part IV 定理 64.10，(1.12) 等价于这个实际 $I_{13}$ 的整锥正性。Part IV 定理 67.11 随即给出保原迹 Jordan 坐标中的普通 $M(a,b)_{ij}=a_i\otimes b_j$、$L(d,c)_{ijk}=d_{ij}\otimes c_k$，原 $p$ 为普通首腿偏迹求和；其余两个读回是 Part IV (67.28) 的偏迹求和，$p_{13}=I_{13}^*$ 正且 TP。没有选择一个对所有模型通用的固定 Bell 态；Part IV 定理 68.7 的固定一态障碍仍成立。

原全态、全效应及概率仍是 Part IV (66.27)：直和 PSD 块总迹一、各块效应 $0\le e\le I$、Born 迹配对；纯态为 $\coprod_i\mathbb{CP}^{n_i-1}$，同区比较是平方重叠、异区为零。全标量经典扇区、经典与量子混合扇区及全部纠缠态均允许。逆向，标准有限直和张量数据满足定义 1.1、两个实际重置 TP、原 $p$ TP 和此预选整输出条件，故候选在同一实际数据上双向闭合。$\square$

### 1.6 完整中文候选与几何范围

**定义 1.6（关系校准候选的朴素表述）。** 在真实给定的单份、双份、三份非零有限系统中，保留所有状态和所有效应，用确定接受纯参照时的最少接受率定义比较，要求任意有限随机纯制备与交换端点后逐项平均一致。沿用 Part IV §66.1 明确的条件 Jordan 桥并忠实保留原归一化、单位和配对；只给整个双份正锥上的正接合与整个三份正锥上的同一个正读回，从原参考两次使用它定义第一准备。保留两条实张成、两个单位切片的零比较保持（第二个覆盖全部双份正元）、全部实方向的 $Z$，以及由这些原始关系推出的逆迹平衡。然后要求这个原读回保持整个三份系统的总概率，并要求：把所有局部输入统一重置到一个事先固定扇区内的任意固定态时，按实际乘积关系唯一延拓的二份或三份并行全重置保持整个输入态空间的总概率。另一份数的全重置和所有归一化乘积三元输出的总概率由此推出。最后仍按实际第一准备预选所有有序活跃端点的合成 Bell 态，并要求实际交叉插入的整个输出为正；这才接回同时相容的普通有限张量与读回。

几何上，重置读取的是整个实际空间的正迹泛函 $\operatorname{Tr}(V_m-)$；概率守恒要求其密度乘准备总量恰为单位。原逆迹平衡消去二份共同尺度，同一个保迹读回再固定三份权重。方向相容性则由完整 Bell 输出的锥归属判断，不能由这些总量等式替代。纯端点互反也不等于时间中的操作交换，Part IV (66.40) 的控制仍适用。

本章的关系应用是实际加权乘积所确定的重置、与同一读回的交换关系及同数据校准等价（repo-derived）。有限复载体、原始分类及逆向、双迹刚性、模型适配 Bell 规则分别复用Part IV §§66、67、68；正泛函乘正输出的 CP 与全态 TP 判据复用 Part IV (69.14) 和上述 Watrous 文献接口（literature-attested）。有限维线性满射与迹对偶只是推导中间步骤，不另立一般新定理。这些对应不证明独立公理减少、最少性或文献新颖性。

该条件候选不从物理来源推出完整比较律、全部效应、全锥关系或实张成，不证明参考、探针、滤波、重置及一般 CP 映射的物理可用性。不选择单一非经典扇区，不识别独立给定的另一三份括号载体，不提供四份、任意多份或无限维一致性，也不产生动力学、时间、Hamiltonian、$\hbar$ 或经验对应；有限静态量子结构与完整物理起源之间的这些桥仍须分别建立。

## 追加锚（本行以下为增补区）
