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

## 123. 正规锚点的原单位提升费用与有限实际球负证书

**约定 123.0（原实现、卷名与条件范围）。** 本章的121、122均指[THREE_COPY第七卷121][Q123121]、[THREE_COPY第七卷122][Q123122]；VII103—104指[完整排除面第七卷][Q123VII]，VIII112—113指[排除球第八卷][Q123VIII]，IX116、118、120指[排除球第九卷][Q123IX]。本章使用同一个原 $V,C,u,K,P,\mathcal E$ 和全部完整 $D_p$。本卷第1章的有限联合校准前件不属于这里的EB3+Inj前件，不能把该章的共同读回、Jordan供应或复合结构输入本章。以下为纸面条件推导；静态分类沿既有完整接口复用，有限实际相容性仍是明确的open桥。

### 123.1 完整原域与整个纯标签域上的正规锚点

取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，以及在 $C\setminus\{0\}$ 上严格正的原单位 $u\in V^*$。定义

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\quad
T_p(x)=\min_{f\in\mathcal F_p}f(x),\quad
D_p=\{x\in K:T_p(x)=0\},\\
\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\},\qquad
\mathcal B(p)=\{h\in\mathcal E:h(p)=0\}.
\end{gathered}
\tag{Q123.1}
$$

$K$ 是整个紧态基，$P$ 是全部原纯点，$\mathcal E$ 是全部原效应；不先假设 $P$ 闭。EB3表示每个完整 $D_p$ 仿射等价于整个闭三球，Inj表示 $D_p=D_q\Rightarrow p=q$。原关系 $p\perp q$ 表示同一张原全域效应在两端取一、零；它由补效应对称，等价于 $q\in D_p$，且 $p\notin D_p$。真实三角只要求三条这样的边分别存在，不预装同一实际三结果仪器。

复用VII103.2、104.1：各 $D_p$ 是紧暴露极大真面，$\mathcal A_p$ 非空；全部非空真面只有纯单点与完整球。对完整球 $F$，$P\cap F=\partial_{\rm rel}F$ 且 $F=\operatorname{conv}(P\cap F)$；不同完整球相交时仅交于一个原纯点。在EB3+Inj中，任意 $e\in\mathcal A_p$ 的原零面恰为 $D_p$，原一值面恰为 $\{p\}$。特别地，这个一值面结论也量化全部原混态。

固定原效应范数 $\|h\|_K=\max_{x\in K}|h(x)|$ 及其Hausdorff距离。令

$$
\begin{split}
P_0&=\{p\in P:\mathcal A_p\text{ 为单点}\},\\
\operatorname{Cont}(\mathcal B)&=\{p\in P:\ \forall(p_n)\subset P,
\ p_n\to p\Rightarrow d_H(\mathcal B(p_n),\mathcal B(p))\to0\},\\
P_{\rm reg}&=P_0\cap\operatorname{Cont}(\mathcal B).
\end{split}
\tag{Q123.2}
$$

**命题 123.1（已付残余接口的准确取域）。** 在EB3+Inj中，$P_{\rm reg}$ 是整个原 $P$ 中的稠密 $G_\delta$。

证明。THREE_COPY第七卷121.5—121.7已给 $P$ 的Baire性质、$P_0$ 稠密 $G_\delta$，以及包含于 $\operatorname{Cont}(\mathcal B)$ 的稠密 $G_\delta$。对任意度量空间到度量空间的映射，连续点集本身是 $G_\delta$：令 $U_j$ 为所有存在开邻域、其像的直径小于 $1/j$ 的点之并，则连续点集恰为 $\bigcap_jU_j$。将值域取为 $\mathcal E$ 的非空紧子集所成Hausdorff度量空间，得到 $\operatorname{Cont}(\mathcal B)$ 是 $G_\delta$，又含已有稠密集，故稠密。与 $P_0$ 相交仍含THREE_COPY第七卷121.7的同一稠密 $G_\delta$，完成断言。证毕。

这里量化的是从整个 $P$ 趋近锚点的全部纯序列，没有把残余集限制到某颗 $S(D_p)\cong S^2$ 来取得密度。

**命题 123.2（完整零效应稳定所给的整球与任取完整确认稳定）。** 若 $p\in P_{\rm reg}$、$p_n\in P$、$p_n\to p$，则

$$
d_H(D_{p_n},D_p)\to0,\qquad
\sup_{e\in\mathcal A_{p_n}}\|e-e_p\|_K\to0,\qquad
\mathcal A_p=\{e_p\}.
\tag{Q123.3}
$$

证明。先固定任意 $s\in S(D_p)=P\cap D_p$ 及任意 $h_s\in\mathcal A_s$。有 $h_s(p)=0$，故 $h_s\in\mathcal B(p)$。完整零效应稳定允许在每个 $\mathcal B(p_n)$ 取 $b_n\to h_s$。置 $M_n=\max_Kb_n$；由一致收敛有 $M_n\to\max_Kh_s=1$。所以只有有限初项可能 $M_n=0$，这些初项在各完整球面任取 $s_n$。在其余项，最大面非空紧，选其原纯点 $s_n$；$b_n/M_n\in\mathcal E$，确认 $s_n$、零于 $p_n$，因而 $s_n\in S(D_{p_n})$。同时 $h_s(s_n)\to1$。紧 $K$ 中任一聚点都在 $h_s$ 的完整原一值面 $\{s\}$，所以 $s_n\to s$。没有预设这些极点聚点仍纯，纯性是由同一原一值面最后取得。

每个 $x\in D_p$ 是有限个 $S(D_p)$ 点的凸组合；以相同系数混合对应 $s_n$，得到 $x_n\in D_{p_n}$、$x_n\to x$。这一步保留整个原球的全部混态。若下Hausdorff包含不成立，在紧 $D_p$ 中选违反者及其聚点，再用该聚点的上述逼近就矛盾。上Hausdorff包含来自原关联的闭图：$p_n\to p\in P$、$x_n\in D_{p_n}$、$x_n\to x$ 时，取真实确认零见证并在紧 $\mathcal E$ 中取极限，得到 $x\in D_p$。两侧合起来给整球Hausdorff收敛。

最后，任取 $e_n\in\mathcal A_{p_n}$ 的收敛子列 $e_n\to e$。原评价给 $e(p)=1$。对每个 $x\in D_p$，刚证整球逼近给 $x_n\in D_{p_n}$、$x_n\to x$，于是 $e(x)=\lim e_n(x_n)=0$。故 $e\in\mathcal A_p=\{e_p\}$。紧效应区间上的反证法将此升级为(Q123.3)中对任取完整确认的统一断言。证毕。

这是IX118.10—118.11及THREE_COPY第七卷121的完整稳定接口在同一正规锚点的应用，不是新的分类，也不把全域WZ或全标签球连续性当作已得结果。

### 123.2 固定原球、真实花瓣球与两个不能混同的对径

以下先固定任意 $p\in P_0$。写

$$
\begin{gathered}
\mathcal A_p=\{e_p\},\quad g=g_p=u-e_p,\quad
D_p=c+B\mathbb B^3,\quad N_p=\{h\in C^*:h(p)=0\},\quad
S_p=\operatorname{span}N_p,\\
H=(H_1,H_2,H_3),\quad H(c+Bw)=w,\quad H_i\in S_p,\quad
\rho(v)=\rho_p(v)=\sup_{x\in K\setminus\{p\}}
             \frac{-v\cdot H(x)}{g(x)}.
\end{gathered}
\tag{Q123.4}
$$

IX120.8—120.12及THREE_COPY第七卷122.2已经给：限制 $S_p\to\operatorname{Aff}(D_p)$ 是同构；$\dim S_p=4$；$g\in\operatorname{ri}N_p$；$g>0$ 于 $K\setminus\{p\}$；$\|H(x)\|\le M_Hg(x)$；$\rho$ 有限、Lipschitz、正齐次、次可加，且 $\rho(v)\ge\|v\|$。此外

$$
N_p=\{\alpha g+b\cdot H:\alpha\ge\rho(b)\}.
\tag{Q123.5}
$$

对每个 $v\in S^2$，原球上的点、其完整邻球和邻确认分别是

$$
q_v=c+Bv\in P_0,\qquad F_v=D_{q_v},\qquad
e_{q_v}=\frac{\rho(v)g+v\cdot H}{1+\rho(v)}.
\tag{Q123.6}
$$

$p\in S(F_v)$，而不同 $F_v$ 只交于 $p$。定义 $a_v$ 为 $p$ 在真实整球 $F_v$ 内的对径点，并置

$$
m(v)=g(a_v)=\max_{F_v}g>0,\qquad
z_v=\frac{H(a_v)}{g(a_v)}.
\tag{Q123.7}
$$

$a_v$ 是原纯点且属于 $P_0$，因为 $q_v\in P_0$ 的所有邻标签仍在 $P_0$。它是在另一颗完整球 $F_v$ 内定义的对径端，不能预先认同为在原 $D_p$ 内与 $q_v$ 对径的 $q_{-v}$；二者相等须由相应接触另证。THREE_COPY第七卷122.4已经给整个 $F_v$ 上的原线性关系

$$
H|_{F_v}=z_vg|_{F_v},\qquad (-v)\cdot z_v=\rho(v).
\tag{Q123.8}
$$

它包括整个邻球的混态，不只两端。

### 123.3 全原空间确认恒等式与原球上的序下界

**定理 123.3（两个实际球图给出的精确系数）。** 对任意 $p\in P_0$、$v\in S^2$，令

$$
r=\rho_p(v),\quad t=e_p(a_v)=1-m(v),\quad d=e_{a_v}(p).
$$

则 $0\le t,d<1$，在整个原 $V$ 上有

$$
\boxed{\quad e_{a_v}=d e_p+\gamma_v(g-v\cdot H),\qquad
\gamma_v=\frac{1-dt}{(1-t)(1+r)},\qquad
\frac1{1+r}\le\gamma_v\le\frac12.\quad}
\tag{Q123.9}
$$

特别地，在整个原球 $D_p$ 上有相对原序下界

$$
\begin{split}
e_{a_v}|_{D_p}
 &=\gamma_v(1-v\cdot H)|_{D_p}\\
 &\ge(u-e_{q_v})|_{D_p}
   =\frac{1-v\cdot H}{1+\rho_p(v)}\Big|_{D_p}.
\end{split}
\tag{Q123.10}
$$

这里的不等式仅指限制在 $D_p$ 上逐态成立；没有将它误写成整个 $C^*$ 上的序支配。

证明。在同一个原 $q=q_v$ 的球图写 $F_v=c_q+B_q\mathbb B^3$，$p=c_q+B_qs$，$a_v=c_q-B_qs$，$\|s\|=1$。令

$$
R=\rho_q(s)\ge1,\qquad T=\rho_q(-s)\ge1,\qquad g_q=u-e_q.
$$

两端都是真实邻标签，IX120.12分别给出整个原 $V$ 上的等式

$$
e_p=\frac{Rg_q+s\cdot H^q}{1+R},\qquad
 e_{a_v}=\frac{Tg_q-s\cdot H^q}{1+T}.
\tag{Q123.11}
$$

在 $F_v$ 上 $g_q=1$；代入 $a_v$ 和 $p$ 得

$$
m(v)=\frac2{1+R},\qquad
 t=\frac{R-1}{R+1},\qquad d=\frac{T-1}{T+1}.
\tag{Q123.12}
$$

$R,T$ 逐点有限，故 $t,d<1$。消去同一个 $s\cdot H^q$，得到

$$
e_{a_v}=\frac{T+R}{1+T}g_q-\frac{1+R}{1+T}e_p.
$$

另一方面，(Q123.6)准确给 $g_q=e_p+(g-v\cdot H)/(1+r)$。代入并整理，$e_p$ 的系数为 $(T-1)/(T+1)=d$，其余系数为

$$
\gamma_v=\frac{T+R}{(1+T)(1+r)}
=\frac{d+(1-d)/m(v)}{1+r}
=\frac{1-dt}{(1-t)(1+r)}.
\tag{Q123.13}
$$

由于 $R\ge1$，$(T+R)/(1+T)\ge1$，故 $\gamma_v\ge1/(1+r)$。在原态 $q_{-v}\in D_p$ 评价(Q123.9)，得到 $e_{a_v}(q_{-v})=2\gamma_v\le1$，给上界。最后 $e_p|_{D_p}=0$ 且 $1-v\cdot H\ge0$ 于整颗原球，完成(Q123.10)。证毕。

恒等式由两个真实完整球图在原 $V$ 上消元得到；没有把只在一个球上的仿射等式直接延拓，也没有预付跨球连续或倒向刻度的统一界。

### 123.4 正规锚点处全部真实对径端统一不塌缩

**定理 123.4（同一锚点、全部方向的正高度）。** 对每个 $p\in P_{\rm reg}$，存在同一个 $\sigma_p>0$，使

$$
\boxed{\qquad \forall v\in S^2:\quad
 g_p(a_v)=\max_{D_{q_v}}g_p\ge\sigma_p.\qquad}
\tag{Q123.14}
$$

证明。固定 $p$，令 $R_p=\max_{v\in S^2}\rho_p(v)<\infty$。若不存在共同正下界，取 $v_n$ 使 $g(a_{v_n})\to0$。紧 $K$ 中任一聚点 $a$ 都满足 $g(a)=0$，而 $g$ 的原零面为 $\{p\}$，故整个 $a_{v_n}\to p$。每个 $a_{v_n}$ 都是原纯点，命题123.2适用并给

$$
\|e_{a_{v_n}}-e_p\|_K\to0.
$$

然而在移动的真实原点 $q_{-v_n}\in D_p$ 上，定理123.3给

$$
e_p(q_{-v_n})=0,\qquad
 e_{a_{v_n}}(q_{-v_n})=2\gamma_{v_n}
 \ge\frac2{1+R_p}>0.
\tag{Q123.15}
$$

这与全原态上一致收敛矛盾。证毕。

现在才可由(Q123.12)得全部倒向实际刻度的共同上界

$$
\rho_{q_v}(s_v)\le2/\sigma_p-1\qquad(v\in S^2).
\tag{Q123.16}
$$

这不是先把每个有限倒向函数当作统一有界；统一性由完整零效应稳定及(Q123.10)支付。常数只依赖这个原锚点，没有对全部 $P$ 宣称共同下界，也没有由此把所有到达标签 $q_v$ 放进 $P_{\rm reg}$。

### 123.5 完整实际影像闭合、严格凸与非零方向的可微性

沿用THREE_COPY第七卷122.3的实际比值影像及闭影壳

$$
Z_p=\{H(x)/g(x):x\in K\setminus\{p\}\},\qquad
\overline Z_p=S.
\tag{Q123.17}
$$

已有结论是 $Z_p$ 有界凸、含整个 $\mathbb B^3$，且

$$
h_S(-v)=\rho_p(v),\qquad
 Z_p\cap\operatorname*{argmax}_{z\in S}(-v)\cdot z=\{z_v\}.
\tag{Q123.18}
$$

**定理 123.5（同一正规锚点域上的紧完整影像）。** 若 $p\in P_{\rm reg}$，取定理123.4的 $\sigma=\sigma_p\le1$，则

$$
\boxed{\quad Z_p=S=
 \left\{\frac{H(x)}{g(x)}:x\in K,\ g(x)\ge\sigma\right\}.\quad}
\tag{Q123.19}
$$

因此 $Z_p$ 是三维紧凸且严格凸的完整实际影像；全部支撑值仍由真实原态达到。$v\mapsto z_v$ 在整个 $S^2$ 连续，$\rho_p$ 在 $\mathbb R^3\setminus\{0\}$ 上为 $C^1$，并且

$$
\nabla\rho_p(v)=-z_{v/\|v\|},\qquad
 C+(\operatorname{span}N_p)^\perp\text{ 闭}.
\tag{Q123.20}
$$

证明。令(Q123.19)右侧为 $A$。它是紧集的连续像，故紧，且 $A\subseteq Z_p\subseteq S$。它也凸：若 $x_i\in K$、$g_i=g(x_i)\ge\sigma$，按THREE_COPY第七卷122.4的实际混合公式

$$
x=\frac{\lambda x_1/g_1+(1-\lambda)x_2/g_2}
         {\lambda/g_1+(1-\lambda)/g_2}
\quad(0\le\lambda\le1)
$$

有 $x\in K$，比值为两比值的同系数凸组合，且
$g(x)=1/(\lambda/g_1+(1-\lambda)/g_2)\ge\sigma$。每个真实支撑值 $z_v$ 又由 $a_v$ 实现，且 $g(a_v)\ge\sigma$，所以 $z_v\in A$。于是对每个单位方向 $-v$，$h_A(-v)=h_S(-v)$。若 $S\not\subseteq A$，紧凸分离会在某一方向给严格不同的支撑值，矛盾。因此 $A=S=Z_p$。

由(Q123.18)，现在每个完整支撑面都只有一个点。若边界存在非平凡线段，在其中点取支撑超平面，整段都会处于同一支撑面，矛盾；故严格凸。所有支撑函数最大值由 $a_v$ 实际达到。对 $v_n\to v$，紧 $Z_p$ 中任一 $z_{v_n}$ 的聚点都最大化方向 $-v$；该最大点唯一为 $z_v$，故整个映射连续。

为明确可微结论，对非零法向 $n$ 令 $z(n)$ 为 $n\cdot z$ 的唯一最大点。若 $n+k\ne0$，最大值的两侧比较给

$$
0\le h_S(n+k)-h_S(n)-k\cdot z(n)
\le k\cdot(z(n+k)-z(n)).
$$

右侧绝对值至多 $\|k\|\|z(n+k)-z(n)\|=o(\|k\|)$，故 $\nabla h_S(n)=z(n)$；刚证连续性使导数连续。代入 $\rho_p(v)=h_S(-v)$ 即得(Q123.20)的梯度公式。

最后令 $\Pi=(g,H)$、$L=(\operatorname{span}N_p)^\perp$。已付限制同构给 $\Pi$ 满射、$\ker\Pi=L$。准确像为

$$
\Pi(C)=\{0\}\cup\{s(1,z):s>0,\ z\in Z_p\}.
\tag{Q123.21}
$$

紧有界 $Z_p$ 使此锥闭，故 $C+L=\Pi^{-1}(\Pi(C))$ 闭；这也是THREE_COPY第七卷122.6的准确闭像接口。证毕。

THREE_COPY第七卷122.5已有 $S$ 每个边界点的唯一支撑超平面；本定理补上严格凸，而不是重证该法锥分类。THREE_COPY第七卷122.8在任意 $P_0$ 锚点所描述的平支撑面，会迫使一串真实邻球的高度趋零；(Q123.14)表明这样的平面在 $P_{\rm reg}$ 锚点不能发生。这里用的是锚点自身的全原标签稳定性，并未把残余集限制到到达球面。

本结论只量化 $p\in P_{\rm reg}$ 的这些法向面。它不证明原 $C^*$ 对每个面都具有闭延拓，即不主张全局FDC或niceness；更不制造原单位保持的正过滤。

### 123.6 最省原单位提升费用及保留单位的更大闭凸像

**定义 123.6（原单位费用）。** 固定 $p\in P_{\rm reg}$，对 $z\in\mathbb R^3$ 定义

$$
\Lambda_p(z)=\inf\{u(y):y\in C,\ g_p(y)=1,\ H_p(y)=z\},
\tag{Q123.22}
$$

空集的下确界为 $+\infty$。可行域恰为 $Z_p$。所用单位始终是原 $u$；不在法向商上另设单位。

**定理 123.7（达到性、凸性、下半连续及准确单位成本层）。** 对每个 $z\in Z_p$，(Q123.22)的下确界达到，且

$$
1\le\Lambda_p(z)\le1/\sigma_p,\qquad
\{z:\Lambda_p(z)\le1\}=\{z:\Lambda_p(z)=1\}=\mathbb B^3.
\tag{Q123.23}
$$

作为 $\mathbb R^3$ 上取扩展实值的函数，$\Lambda_p$ 凸且下半连续。每个真实支撑点有精确费用

$$
\boxed{\qquad \Lambda_p(z_v)=\frac1{g_p(a_v)}=\frac1{m(v)}.\qquad}
\tag{Q123.24}
$$

证明。由(Q123.19)，每个 $z\in Z_p$ 可取原 $x\in K$，$g(x)\ge\sigma_p$，比值为 $z$。置 $y=x/g(x)$，即有可行提升及 $u(y)=1/g(x)\le1/\sigma_p$。任何可行 $y$ 又由 $0\le g\le u$ 得 $u(y)\ge1$。

取逼近下确界的可行序列，使其费用均不超过某个固定有限 $M$。集合 $\{y\in C:u(y)\le M\}$ 紧：它是紧 $[0,M]\times K$ 在 $(t,x)\mapsto tx$ 下的像。闭的 $g=1,H=z$ 约束使聚点可行并达到费用最小值。凸组合两个最省提升仍可行且费用为同一凸组合，给凸性。对任意有限 $M$，费用子水平集恰是紧凸集

$$
\{H(y):y\in C,\ g(y)=1,\ u(y)\le M\},
\tag{Q123.25}
$$

故闭，给扩展实值下半连续性，包括 $Z_p$ 边界与可行域外。

若费用一，取最省提升 $y$，有 $u(y)=g(y)=1$，即 $e_p(y)=0$，所以 $y\in D_p$，$H(y)\in\mathbb B^3$。反之每个 $z\in\mathbb B^3$ 由原 $c+Bz\in D_p$ 给费用一。这证明准确单位成本层，既没有删除混态，也没有把小于一的费用归一掉。

最后，若可行提升在 $z_v$，其原归一态 $x=y/u(y)$ 的比值也是 $z_v$。THREE_COPY第七卷122.4的完整接触纤维等式使 $x\in F_v\setminus\{p\}$，故 $g(x)\le m(v)$，$u(y)=1/g(x)\ge1/m(v)$。原对径点 $a_v/m(v)$ 达到等号，完成(Q123.24)。证毕。

**命题 123.8（把原单位一并保留的闭凸提升像）。** 定义

$$
\widehat C_p=(u,g_p,H_p)(C)\subset\mathbb R\times\mathbb R\times\mathbb R^3.
\tag{Q123.26}
$$

则 $\widehat C_p$ 是闭凸锥，并且

$$
\begin{split}
\widehat C_p={}&\{(t,0,0):t\ge0\}\\
&\cup\{(t,s,sz):s>0,\ z\in Z_p,\ t\ge s\Lambda_p(z)\}.
\end{split}
\tag{Q123.27}
$$

证明。线性像保凸与锥性。若像中序列收敛，第一坐标 $u(y_n)$ 有界，严格正原单位使原提升 $y_n$ 落在一个紧截锥内；取聚点便得到极限仍属该像，故闭。若 $s=g(y)=0$，原零面给 $y\in\mathbb R_+p$，所以 $H(y)=0$、$t=u(y)\ge0$。若 $s>0$，$y/s$ 可行，故 $z=H(y)/s\in Z_p$ 且 $u(y)\ge s\Lambda_p(z)$。反向取最省提升 $y_z$，再加非负的 $(t-s\Lambda_p(z))p$，其 $g,H$ 都不变而原单位费用恰变成 $t$。证毕。

原单位一切片对应准确的紧凸读数像

$$
(g,H)(K)=\{(0,0)\}\cup
 \{(s,sz):s>0,\ z\in Z_p,\ s\Lambda_p(z)\le1\}.
\tag{Q123.28}
$$

由(Q123.27)直接取 $t=1$ 即得，故这是原态的实际读数像，不是另加的状态许可。它说明 $\Lambda_p$ 是保留原单位后剩余的准确边界函数；遗忘第一坐标才得到(Q123.21)的法向商锥。

$p\in L=(\operatorname{span}N_p)^\perp$，但 $u(p)=1$。因而 $u$ 不下降为 $V/L$ 上的线性泛函。闭商像只记得 $(g,H)$，会把 $p$ 与零合并；$(u,g,H)$ 的较大闭像保留二者不同的第一坐标。无论(Q123.27)多么规则，最省提升通常是依 $z$ 选择的非线性对象，没有给出保单位正线性截面、正回缩、实际制备、仪器或动力学。THREE_COPY第七卷122.7中只商 $\mathbb Rp$ 的非闭性也仍成立；它与使用更大准确核 $L$ 的闭像不是同一个商。

### 123.7 影壳边界的最小原单位费用与完整静态候选

**定义 123.9（边界原单位接触）。** 对 $p\in P_{\rm reg}$ 定义

$$
\theta_p=\min_{z\in\partial Z_p}\Lambda_p(z),\qquad
\mathsf{UC}_{\rm reg}:\quad
\overline{\{p\in P_{\rm reg}:\theta_p=1\}}^{\,P}=P.
\tag{Q123.29}
$$

边界相对于 $\mathbb R^3$，因为整颗 $\mathbb B^3\subset Z_p$。紧非空 $\partial Z_p$ 与下半连续性给最小值达到；$1\le\theta_p\le1/\sigma_p$。这里最小值是一，不是只要求费用有限或有界。

**定理 123.10（同原实现的完整候选等价）。** 在(Q123.1)完整原域，下列模型类完全相同：

1. EB3+Inj+$\mathsf{UC}_{\rm reg}$；
2. EB3加THREE_COPY第七卷122的原接触标签稠密 $\mathsf{DC}$；
3. EB3加THREE_COPY第七卷121的全标签中点接触 $\mathsf{MC}$；
4. EB3加 $W(D_p)=1$ 对全部 $p\in P$；
5. 存在同原锥、同原单位的实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V,
\qquad \Phi(\mathrm{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\tag{Q123.30}
$$

证明。先在EB3+Inj及固定 $p\in P_{\rm reg}$ 下，定理123.7给

$$
\theta_p=1
\Longleftrightarrow\partial Z_p\cap\mathbb B^3\ne\varnothing
\Longleftrightarrow\exists v\in S^2:\rho_p(v)=1
\Longleftrightarrow W(D_p)=1.
\tag{Q123.31}
$$

第一等价使用最小值达到和准确费用一层。第二等价也可直接核对：若 $z\in\mathbb B^3\cap\partial Z_p$，取单位外法向 $n$，有 $h_{Z_p}(n)=n\cdot z\le1$，而 $\mathbb B^3\subset Z_p$ 给反向，故 $h_{Z_p}(n)=1$；取 $v=-n$。反向若支撑值一，原内球点 $-v$ 就在影壳边界。最后一等价直接消费THREE_COPY第七卷122.13及THREE_COPY第七卷121.2，不重作中点证明。

因此1给一个在整个 $P$ 稠密的原接触标签子集，即2。THREE_COPY第七卷122.2已经在裸EB3中证明2、3、4、5互相等价；顺序是先得全W1，再得Inj、纯点紧性及全Pair，然后消费IX116.17和VII104.2—104.3。这里不提前输入全共同仪器。

为完整支付5到1的反向，考察全部矩阵原域并经同一 $\Phi$ 运输。每个纯态为任意秩一投影 $p=zz^*/(z^*z)$；全部确认效应矩阵恰为 $p\oplus A$，$0\preceq A\preceq I_{z^\perp}$。所以对任意原混态 $\rho$，$T_p(\rho)=\operatorname{Tr}(p\rho)$，完整 $D_p$ 是 $z^\perp$ 上全部密度矩阵，是整颗Bloch三球，其支撑确定 $z^\perp$，故Inj成立，且 $\mathcal A_p=\{f_p\}$。对每个 $0\preceq A\preceq I$、$\operatorname{Tr}(Ap)=0$，正性给 $Ap=0$；当任意纯 $p_n\to p$ 时，令 $Q_n=I-p_n$，则 $A_n=Q_nAQ_n$ 仍是全域效应且零于 $p_n$，并满足 $\|A_n-A\|_{\rm op}\le2\|p_n-p\|_{\rm op}$。原零效应的上包含由紧性和连续评价给出，故整个 $\mathcal B(p_n)\to\mathcal B(p)$，从而每个 $p$ 都属于 $P_{\rm reg}$。

在该矩阵原球图中，对每个混态 $\rho$，$Q\rho Q$ 是 $z^\perp$ 上质量 $g_p(\rho)=\operatorname{Tr}(Q\rho)$ 的正矩阵；其归一Bloch坐标为 $H_p(\rho)/g_p(\rho)$。因而 $Z_p=\mathbb B^3$，并且每个 $z\in\mathbb B^3$ 都由 $D_p$ 内原迹一态取得，$\Lambda_p(z)=1$。所以 $\theta_p=1$ 对全部原纯 $p$ 成立，特别给1要求的稠密性。这同时量化全部纯点、混态、效应和原单位，而非只展示一个兼容模型。证毕。

本候选可写成一句：完整EB3、标签不重复，以及在所有原纯标签中稠密的一批正规锚点，其影壳边界至少一点只需一份原单位即可提升。它是既有全接触条件的准确费用表达；没有证明独立假设减少、公理最少、裸EB3自动给Inj，或EB3+Inj自动给费用一。紧影像、光滑严格凸和费用统一有限都止于此条件之前；一般凸几何中的 $r\mathbb B^3$、$r>1$ 可以完整包住内球而不接触，但这幅图没有被构造成完整EB3原反模型。

### 123.8 两个原法向张成空间的交线与唯一第三候选

以下重新只要求 $p\in P_0$，不要求 $p\in P_{\rm reg}$。记 $S_q=\operatorname{span}N_q$。对每个 $v\in S^2$ 定义整个原 $V$ 上的第三候选

$$
r_v=u-e_p-e_{q_v}
=\frac{g-v\cdot H}{1+\rho_p(v)}.
\tag{Q123.32}
$$

$r_v$ 此时只是原线性泛函，尚未断言非负。

**定理 123.11（准确交线、全域正性与真实三元补全）。** 在EB3+Inj中，对任意 $p\in P_0$、$v\in S^2$，

$$
S_p\cap S_{q_v}=\mathbb Rr_v,
\tag{Q123.33}
$$

且下列条件等价：$r_v\in C^*$；$\rho_p(-v)=1$；$\rho_p(v)=1$；存在原纯 $b$ 与 $p,q_v$ 构成三条真实原边的三角；这条边具有原全域数学三结果补全。成立时

$$
b=q_{-v}=a_v,\qquad r_v=e_b,\qquad e_p+e_{q_v}+e_b=u,
\qquad e_i(p_j)=\delta_{ij}.
\tag{Q123.34}
$$

证明。若 $h\in N_{q_v}$，其在原整球 $D_p$ 上非负且在 $q_v=c+Bv$ 取零；球上的Cauchy–Schwarz等号使限制恰为 $\alpha(1-v\cdot w)$，$\alpha\ge0$。取线性张成后，任意 $h\in S_{q_v}$ 的限制均为这个函数的实倍数。再限制 $h\in S_p$，IX120.8的限制单射便给 $h\in\mathbb R(g-v\cdot H)$。反向 $r_v=g-e_{q_v}\in S_p$；又 $r_v=(u-e_{q_v})-e_p\in S_{q_v}$，因为 $u-e_{q_v}\in N_{q_v}$、$e_p\in N_{q_v}$。其在 $q_{-v}$ 的值为 $2/(1+\rho_p(v))>0$，所以非零，交恰为该直线。

由准确原正锥公式(Q123.5)，$r_v\ge0$ 恰等价于 $1\ge\rho_p(-v)$，也就是 $\rho_p(-v)=1$。若此值为一，(Q123.6)用于方向 $-v$ 给

$$
e_{q_{-v}}=(g-v\cdot H)/2,\qquad e_{q_{-v}}(q_v)=0.
$$

这是真实原效应，所以 $q_{-v}\perp q_v$。原零关系的对称及完整确认的零面使 $e_{q_v}(q_{-v})=0$；而它按(Q123.6)恰为 $(\rho_p(v)-1)/(1+\rho_p(v))$，故 $\rho_p(v)=1$。交换 $v,-v$ 也证明反向。现在(Q123.32)就是 $e_{q_{-v}}$，且 $p,q_v,q_{-v}$ 两两原零，三个效应全域非负、和恰为 $u$，这独立证明数学共同三结果。

反之，若 $b\perp p,q_v$，则 $b\in D_p\cap D_{q_v}$。$e_{q_v}$ 在 $D_p$ 上的原读数只能在 $\rho_p(v)=1$、$b=q_{-v}$ 时为零。因此该真实三角迫使上述正性和补全。若已给数学三结果且第三效应确认某个原纯 $b$、在 $p,q_v$ 取零，则三点的原边也随之成立，故同样回到上述条件。最后，$e_p$ 在 $F_v$ 上于 $p$ 为一、在 $q_{-v}$ 为零，球上两极值使这两个点为其对径端，故 $a_v=q_{-v}$。证毕。

这里“数学三结果补全”专指三个原非负效应在三个原纯点具有Kronecker读数且和为 $u$。它没有预装实际菜单或同族仪器，也没有声称交线的每个有向生成元都为正；未接触时，正是指定的 $r_v$ 会失去全原域非负性。

### 123.9 所有原法向正性可由真实对径端检验

**定理 123.12（完整原正性的真实点检验）。** 对每个 $p\in P_0$ 和每个 $h=\alpha g+b\cdot H\in S_p$，

$$
\begin{split}
h\in C^*
&\Longleftrightarrow\forall w\in S^2:\ h(a_w)\ge0\\
&\Longleftrightarrow\alpha\ge\rho_p(b).
\end{split}
\tag{Q123.35}
$$

更准确地，若 $b\ne0$，

$$
\inf_{x\in K\setminus\{p\}}\frac{h(x)}{g(x)}
=\alpha-\rho_p(b)
=\frac{h(a_{b/\|b\|})}{g(a_{b/\|b\|})}.
\tag{Q123.36}
$$

证明。$h(p)=0$，且其余全部原态的 $g$ 严格正，故原全域正性可通过比值检验。方向函数定义给下确界 $\alpha-\rho_p(b)$；(Q123.8)给真实端点达到该值，正齐次性包括任意 $b\ne0$ 的尺度。若 $b=0$，所有端点的 $g>0$，所以检验准确地要求 $\alpha\ge0=\rho_p(0)$。最后由 $C=\mathbb R_+K$，全原态检验也就是全原锥检验。证毕。

定理不要求 $a_w$ 随 $w$ 连续，不要求影像闭，也没有把任意抽象支撑点替换成物理准备。

### 123.10 同一有限批真实球的统一负第三效应证书

对任意固定 $\omega\in\operatorname{ri}K$，完整保留THREE_COPY第七卷121的归一化

$$
\mathscr H_\omega=\{h\in C^*:h(\omega)=1\},\qquad
\beta_\omega(p)=\min_{\substack{x\in D_p\\h\in\mathscr H_\omega}}
                  \frac{h(p)+h(x)}2.
\tag{Q123.37}
$$

它满足准确原预算等价

$$
\forall x\in D_p:\ p+x-2\epsilon\omega\in C
\quad\Longleftrightarrow\quad0\le\epsilon\le\beta_\omega(p)
\qquad(\epsilon\ge0).
\tag{Q123.38}
$$

因此 $\beta_\omega$ 中的 $1/2$ 不可删除，亦不把下面的方向支撑差误认成 $\beta_\omega$ 的数值。

**定理 123.13（全方向失败的三种准确有限表达）。** 在EB3+Inj中，对每个 $p\in P_0$，以下等价：

1. $\beta_\omega(p)>0$，即存在同一 $\epsilon>0$ 使(Q123.38)对整个原 $D_p$ 成立；
2. 存在有限真实方向 $w_1,\ldots,w_m\in S^2$ 和 $\eta>0$，其真实对径端 $a_i=a_{w_i}$、$z_i=H(a_i)/g(a_i)$ 满足

$$
(1+\eta)\mathbb B^3\subseteq\operatorname{conv}\{z_1,\ldots,z_m\};
\tag{Q123.39}
$$

3. 存在同一有限批真实 $a_1,\ldots,a_m$ 及同一 $\varepsilon_0>0$，使

$$
\forall v\in S^2\ \exists i\in\{1,\ldots,m\}:\quad
r_v(a_i)\le-\varepsilon_0.
\tag{Q123.40}
$$

没有要求某个固定 $i$ 对所有方向都负；要求的是同一有限批覆盖全部候选，并用同一严格负裕量。

证明。THREE_COPY第七卷121.2—121.3及THREE_COPY第七卷122.13已经给

$$
\beta_\omega(p)>0
\Longleftrightarrow W(D_p)<1
\Longleftrightarrow\rho_p(v)>1\ (\forall v\in S^2).
\tag{Q123.41}
$$

有限连续 $\rho_p$ 在紧 $S^2$ 上达到最小值，因此1等价于

$$
\delta_p:=\min_{v\in S^2}(\rho_p(v)-1)>0.
\tag{Q123.42}
$$

对每个单位方向 $n$，由真实端点(Q123.8)取 $w=-n$，有 $n\cdot z_w=\rho_p(-n)\ge1+\delta_p$。对这个固定真实 $z_w$，集合
$\{n'\in S^2:n'\cdot z_w>1+\delta_p/2\}$ 是含 $n$ 的开集。它们覆盖紧球面，取有限子覆盖，得到同一有限批 $z_i$，对每个 $n$ 均有 $\max_i n\cdot z_i>1+\delta_p/2$。令 $\eta=\delta_p/2$，有限凸包的每个方向支撑值都至少为 $1+\eta$，由凸分离恰给(Q123.39)。这没有使用 $w\mapsto a_w$ 连续。

反向，若2成立，有限凸包属于 $Z_p\subseteq S=\overline Z_p$；即便此时 $Z_p$ 未证闭也无碍。每个方向 $n$ 的支撑值至少为 $1+\eta$，故 $\rho_p(-n)\ge1+\eta$，给(Q123.42)及1。这包围的是整个放大的单位球，不只是原点或某几个坐标方向。

证明2到3。令 $m_i=g(a_i)>0$，$m_*=\min_i m_i>0$，$R_p=\max_{v\in S^2}\rho_p(v)<\infty$。对每个 $v$，2给一个 $i$ 使 $v\cdot z_i\ge1+\eta$，而(Q123.32)给准确原读数

$$
r_v(a_i)=\frac{m_i}{1+\rho_p(v)}(1-v\cdot z_i)
\le-\frac{m_*\eta}{1+R_p}.
\tag{Q123.43}
$$

故取 $\varepsilon_0=m_*\eta/(1+R_p)>0$。在 $P_{\rm reg}$ 上还可用 $m_*\ge\sigma_p$，但该有限批论证本身在全部 $P_0$ 都有效。

反向若3成立，对每个 $v$ 选指定负点，就有

$$
v\cdot z_i\ge1+\frac{\varepsilon_0(1+\rho_p(v))}{m_i}
\ge1+2\varepsilon_0,
\tag{Q123.44}
$$

因为 $\rho_p(v)\ge1$、$m_i\le1$。于是有限凸包在全部单位方向的支撑值至少为 $1+2\varepsilon_0$，由分离得到2，甚至可取 $\eta=2\varepsilon_0$。这完成所有反向。证毕。

证书中的每个点都来自同一原实现的一颗完整真实球 $D_{q_{w_i}}$，且原负读数在真实原纯点 $a_i$ 上出现；没有引入外来抽象顶点。不过它是证明第三候选全域不正的数学证书，既不是共同制备协议，也不是一台把所有候选同时读出的仪器。$\beta_\omega$ 的正性与证书等价不表示其数值等于 $\delta_p,\eta$ 或 $\varepsilon_0$；原预算始终是(Q123.38)的 $2\epsilon$。

### 123.11 有限实际相容性F的准确作用与未证联合关系

**定义 123.14（有限实际相容性）。** 对固定 $p\in P_0$，$\mathsf F(p)$ 表示

$$
\boxed{\quad
\forall m\ge1\ \forall w_1,\ldots,w_m\in S^2\quad
\exists v\in S^2\ \forall i\le m:\quad
v\cdot H_p(a_{w_i})\le g_p(a_{w_i}).\quad}
\tag{Q123.45}
$$

重复方向允许，所有点都由同一原 $p$ 的真实邻球定义。按(Q123.32)，它恰要求每个有限批有一个单位方向，其第三候选在整批原点上均非负；$v$ 必须对该有限批共同，不能逐点选择。

**定理 123.15（排除有限证书恰为原接触）。** 对每个 $p\in P_0$，下列等价：$\mathsf F(p)$；不存在定理123.13的有限负证书；存在同一 $v\in S^2$ 使 $r_v(a_w)\ge0$ 对全部 $w\in S^2$；$\beta_\omega(p)=0$；$W(D_p)=1$。

证明。若存在对全部 $w$ 有效的同一 $v$，显然给每个有限批的F。反之，对每个实际方向 $w$ 令

$$
A_w=\{v\in S^2:v\cdot H(a_w)\le g(a_w)\}.
$$

它闭于紧 $S^2$。F恰为这族闭集的有限交性质；若全交为空，其开补集有有限子覆盖，与F矛盾。因此存在同一 $v$ 对全部实际端点非负。定理123.12将此升级成原全域 $r_v\ge0$，定理123.11再给真实三元补全及 $W(D_p)=1$。反向满宽由THREE_COPY第七卷122.13给某个 $\rho_p(v)=1$，交换方向后定理123.11给全域正的第三候选，因而给F。$\beta_\omega=0$ 与满宽是THREE_COPY第七卷121的原归一接口；与不存在有限证书的等价也可直接由定理123.13取否定得到。证毕。

因此在 $P_{\rm reg}$ 上，$\mathsf F(p)$ 还准确等价于 $\theta_p=1$。若能由EB3+Inj的原联合关系在 $P$ 中稠密的正规锚点证明F，定理123.10就给完整同原静态模型；若只证明每个点自己的不等式、或只证明固定小批次，则不够。F目前没有从这些前件得到证明，把它写成条件并不减少完成原目标所需的证明义务。

**命题 123.16（至多三个点的检验没有球族结构内容）。** 对任意 $m\le3$ 个 $z_i\in\mathbb R^3$，存在单位 $v$ 使 $v\cdot z_i\le0$ 对全部 $i$ 成立。所以这些批次必满足F，甚至不需要EB3。

证明。若这些向量张成维数小于三，取其张成空间的单位垂直向量，所有读数为零。剩下只能是三个线性独立向量；方程 $v_0\cdot z_i=-1$ 有唯一非零解，归一化为 $v=v_0/\|v_0\|$ 即使所有读数严格负。对真实 $a_i$，$g(a_i)>0$，于是该更强不等式立即蕴含F。证毕。

四个点可以在一般三维几何中包住放大的整个单位球，但这只表明第一种非平凡有限配置的规模，不证明原域允许它。即使核对了所有四元组，也不能未经新证明推广到所有有限 $m$。Carathéodory只把一个指定凸包点写为至多四点的凸组合，不给出同时包住整颗球的同一四点；各方向所需的四点可以不同。这里的约束是在球面上取共同单位向量，$A_w$ 也不是自动适用通常凸Helly定理的凸域。不能把某个有限子族存在、某个固定 $m$ 的排除或包围原点替换为(Q123.45)的全部有限族。

**原域剩余桥。** 已付的是所有真实花瓣球、精确全空间确认恒等式、正规锚点的正高度、紧且光滑严格凸的影像、全部方向的真实支撑以及有界原单位费用。尚缺的是这些真实球在同一原 $C,u$ 中的联合相容性，强到禁止(Q123.39)的有限包围配置，等价地保证一个共同单位方向同时满足全部批内原不等式。它必须来自原球之间、确认效应和单位预算之间的新联合论证，不能由逐球有限性、闭商像、逐方向支持或单独三条边重复获得。裸EB3自动供应Inj与接触仍是更大的open问题；本章既未反驳它，也未解决F。

任何反模型都须完整给出原 $V,C,u,K,P,\mathcal E$、全部原纯标签的完整 $D_p$，并验证所有这些集合恰为整颗三球。孤立多边形、抽象图、选择性效应体、球族图或单张光滑外壳只能检验抽取条件的逻辑边界；不能冒充同域完整EB3反模型。

### 123.12 全部静态QM公理与原数学对象的准确字典

仅在定理123.10的完整等价条件成立后，使用同一个保原锥、保原单位 $\Phi$。中点接触与满宽消费THREE_COPY第七卷121；稠密到全称接触消费THREE_COPY第七卷122；全W1到全Pair与同原复三能级消费IX116.17；共同三结果及矩阵效应／谱接口消费VII104.2—104.3与VIII113.8—113.9。这不是从本章有限费用直接跳到Jordan分类。

| 静态QM内容 | 同一原实现中的完整对应 |
| --- | --- |
| 状态射线与全部纯点 | 对全部非零 $z\in\mathbb C^3$，$p_z=\Phi(zz^*/(z^*z))$，恰为整个 $P\cong\mathbb{CP}^2$ |
| 全部混态、混合与质量 | 整个 $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$；保持每个有限凸组合，$C$ 保留零和全部非负缩放，$\dim_{\mathbb R}V=9$ |
| 原单位、全效应与Born配对 | $u\Phi=\operatorname{Tr}$；整个 $\mathcal E$ 恰为 $f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$，$0\preceq A\preceq I_3$，包括全部原混态输入、零、单位、补 |
| least确认与全部完整排除球 | least效应为对应秩一投影；$T_{p_z}(\Phi\rho)=\operatorname{Tr}(zz^*\rho)/(z^*z)$；完整 $D_{p_z}$ 恰为 $z^\perp$ 上全部密度矩阵 |
| 纯—纯概率与原二元零边 | $T_{p_z}(p_w)=|z^*w|^2/((z^*z)(w^*w))$，零恰为复内积正交 |
| 真三角、框架与数学共同结果 | 每条原正交边有唯一第三原纯点；三秩一投影之和为 $I_3$，对应三原非负效应之和为 $u$；容量恰为三 |
| 全部有限数学POVM | 对每个有限结果数，所有原 $f_j\ge0,\sum_jf_j=u$ 恰对应全部 $A_j\succeq0,\sum_jA_j=I_3$ |
| 谱公理与全部可观测量 | 每个原混态有三项正交谱分解，允许零权和重谱；全部实线性可观测量对应全部Hermitian矩阵并有实谱分解 |
| 中心、共同内积与Jordan结构 | 分别为 $\Phi(I_3/3)$、$B(\Phi X,\Phi Y)=\operatorname{Tr}(XY)$、$\Phi((XY+YX)/2)$，均为条件重构后的派生结构 |

这些内容恢复完整单体静态模型，不只匹配纯态比较表。向量叠加作为同一复射线模型的数学结构随之可表达；实际相干制备、相位参考和可调用门仍各需来源与操作合同。相容的静态表示不证明原物理来源满足这些条件，也不自动产生复合、事件、仪器、时间或经验解释。

### 123.13 原来源、操作、全部有限复合与动态合同完整保留

**共同来源及全部原操作。** 完整保留VIII113.11及其所引VIII112.9、IX120.11、THREE_COPY第七卷121.12和THREE_COPY第七卷122.14的同一原装饰元组 $\mathcal O$、共同来源域、全部中点实现、原概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签及每种同中点实现；全部非负质量及零／次归一／不等质量，以及过程和参考各自的完整相关联合输入域。原 $L,p,\omega,K,M$、两次同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE之后的整个H13、每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量和空活跃集，仍由原消费者承担。这里沿用操作合同中的原映射名 $p$，不把它与本章锚点混为同一类型。

设备／事件／来源绑定、全部菜单分支、参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来及每个中间切口，以及VI89.9—89.10的原生／细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption与资源合同全部保留。最省提升、影像凸组合和有限证书不供应这些物理制备或接线。

**全部有限联合层级。** 对每个有限 $N\ge1$ 仍需实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、完整 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 与整个原效应区间。对每个实际分块 $a+b=N$ 保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
\tag{Q123.46}
$$

同一产品配对、严格张量单位、全部原因子置换及其逆的正性、规范重括号和指定运输下的不连续位置分块都保留。比较仍量化整个 $S_2$：每个产品或纠缠纯点 $p\in P_2$、每个有限纯准备族 $q_\ell\in P_2$、全部 $t_\ell\ge0$、$\sum_\ell t_\ell=1$，包括零权和重复标签，满足VIII111.35；不能只检验产品态。

三项具名供应仍分别是：原低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥；唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩与实维乘法的复型选择；同一实际两因子的产品正规形。非经典支路还保留同一保迹局部坐标中同一最大块 $n_r=L\ge2$ 的 $\mathsf F_{\max}$：同一含相位正交基给

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,
\quad \Delta_r=|g_r\rangle\langle g_r|\in C_3,
\quad u_3(\Delta_r)=L.
\tag{Q123.47}
$$

其余三份扇区零，原归一源为 $\Delta_r/L$；不预付三份纯性或实际制备。全经典 $L=1$ 支路不要求这项资源。只有这些联合前件及三项供应齐备后才消费既有全有限层级定理。单体几何不制造 $S_2$、叉口资源、纠缠来源或全部有限张量锥；复三能级二、三份秩为九、二十七，高阶载体不再要求满足单体EB3或秩三W。

**全旁观CP、事件与同族仪器。** 数学全旁观正性仍量化每个 $b\ge0$ 及任意含纠缠的同一共同输入，要求

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{Q123.48}
$$

全联合层级已供应以后，通常CP、矩形跨扇区Kraus与逐输入TP/TNI预算才沿原Choi桥取得。同一事件的CP仍需原完整提升、实际探针及相容核；全部数学CP-TNI分支成为实际事件仍需原事件饱和选择。仪器保留同族共同输入预算、接线、记录、粗粒化与校准；只对正质量分支作条件归一，零质量分支不强定归一条件态。Lüders更新另需同一分支的锐效应、接受态中性及输出校准。三条真实原边、数学三效应和为 $u$、全部数学POVM以及有限负证书均不能替代这些合同。

**时间、生成元、Hamiltonian和 $\hbar$。** 原钟、实际动态来源、连续齐次可逆时间群、单位与 $\hbar$ 仍为独立前件。若另给同一载体上全部实时间的连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，有限维生成元只描述这项额外供应，静态几何并不选择它。在已重构复块中，给定保迹酉时间族的通常表达为

$$
U_t=\exp(-itH/\hbar),\quad
\rho_t=U_t\rho U_t^*,\quad
\mathcal L(\rho)=-\frac{i}{\hbar}[H,\rho],\quad H=H^*.
\tag{Q123.49}
$$

该式量化该已给时间族的全部输入和时间，不由球方向参数、邻球行走或证明弧制造物理时间。$H$ 的标量平移不改变态作用；时间重标改变生成元尺度却保留同一静态模型。恒等族与非平凡Hamiltonian族可共享全部静态数据，故实际 $H$、数值 $\hbar$、能量标定、时空及物理空间维数仍未由本章取得。

### 123.14 复用、原域综合与原始来源的适用范围

本章复用的承重前置是VII103.2、104.1的完整原面，IX118.10—118.11的原零效应最大值／唯一一值面接口，IX120.8—120.12的限制同构及全原空间邻确认公式，THREE_COPY第七卷121的残余稳定、中点、带 $1/2$ 余量和其下半连续性，以及THREE_COPY第七卷122的完整实际影像、接触纤维、影壳光滑与准确闭像关系。静态分类只经IX116.17及VIII113.8—113.9；这些既有结果不再计为本章新分类。

原域联合综合是：两个真实完整球图在全 $V$ 上的确认消元及原球序下界；以整个纯标签域的正规稳定排除全部真实远端塌缩；将所有比值影像压到同一正高度紧截面；原单位最省提升费用及其精确费用一层、真实支撑费用和保单位的更大闭凸像；两个法向张成空间的准确交线；以及同一有限批真实球的放大整球包含、统一负第三效应与原归一正余量的双向等价。紧性、分离、投影、凸费用、下半连续、有限覆盖和支撑函数可微性在这些原对象中作为成熟中间工具使用，不改名为一般新理论，不主张文献穷尽或全球原创。

[Pataki][Q123P] Definition 1、Remark 1定义nice为对每个面 $F\unlhd K$，$K^*+F^\perp$ 闭；Theorem 2刻画同一面处的等价条件。这里若对应该记号，必须取 $K=C^*$、$F=N_p$，所以闭的是原 $C+(\operatorname{span}N_p)^\perp$。本章只在 $P_{\rm reg}$ 的这些面证明它，不把锥与对偶交换，也不由一批局部闭像宣称全局niceness。

[Barnum–Müller–Ududec Theorem 16][Q123BMU]的有限维Jordan入口明确需要projectivity、跃迁概率对称和滤子保纯；Proposition 29关于无三阶干涉与滤子保纯的等价另带Postulates 1、2。[Niestegge Theorem 3][Q123N]明确保留Axioms 1、2、proper效应性质 $(*)$、有限信息容量及对称跃迁概率，才给pre-Hilbert结构与自对偶；唯一完整球确认不等于在全部proper确认效应之下的序least。[Barnum–Hilgert Theorem 1.1、Definitions 3.4—3.5][Q123BH]的入口是每态落在一个共同框架的凸包及各长度有序框架的强对称，不能由三个各自真实的边、原法锥的光滑或有界费用代替。这些条件也与[钉版mathsource的完整S／谱桥][Q123S]及[强对称谱性桥][Q123BHS]保持一致；本章不从已见的几何规则中免费取得它们。

[MixedExclusionGeometry][Q123Mixed]的标签、中心、反射和收缩连续性显式带weakPair；[PositiveComplementaryProjections.whole_positive_projections][Q123Proj]也显式带weakPair，即每个原正交纯对生成真最小面。EB3+Inj没有在本章支付这个前件，故不通过这些接口输入正互补投影、保单位正过滤或跨球全域连续性。这里的最省费用与闭凸提升像也不补这项前件。其他Jordan表示定理只可在各自原前件实际成立后消费，不能以球形、名称或某个二维／三维示意替代。

[Q123VII]: https://github.com/the-omega-institute/trureturing/blob/5f749ade652957c89e6b8b8d7799e7e5e4947903/docs/develop/theory/QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "完整排除面第七卷VII103.2、104.1—104.3；非THREE_COPY第七卷的有限层级103—104。"
[Q123VIII]: https://github.com/the-omega-institute/trureturing/blob/5f749ade652957c89e6b8b8d7799e7e5e4947903/docs/develop/theory/QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "排除球第八卷VIII112.9、113.8—113.11及完整静态与物理合同。"
[Q123IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "排除球第九卷IX116.17、118.10—118.13、120.8—120.12与120.11节完整物理合同。"
[Q123121]: https://github.com/the-omega-institute/trureturing/blob/2f08292714e2f1a90efbe77a5c71c33048191fee/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "THREE_COPY第七卷121；原中点、归一余量、整个原纯标签域的残余稳定及切扇。"
[Q123122]: https://github.com/the-omega-institute/trureturing/blob/129201f3100118257cea7384a73f0b71cfa82818/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "THREE_COPY第七卷122；原三维实际影像、闭影壳、接触纤维、平面塌缩与单位接触。"
[Q123P]: https://arxiv.org/pdf/1202.4043v4 "Gábor Pataki, On the connection of facially exposed and nice cones；Definition 1、Remark 1、Theorem 2；DOI 10.1016/j.jmaa.2012.10.033。"
[Q123BMU]: https://arxiv.org/html/1403.4147v4 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory；Theorem 16、Proposition 29。"
[Q123N]: https://arxiv.org/html/2312.13213v2 "Gerd Niestegge, Quantum transition probability in convex sets and self-dual cones；Axioms 1、2、性质(*)及Theorem 3。"
[Q123BH]: https://arxiv.org/html/1904.03753v1 "Howard Barnum and Joachim Hilgert, Strongly symmetric spectral convex bodies are Jordan algebra state spaces；Theorem 1.1、Definitions 3.4、3.5。"
[Q123S]: https://github.com/the-omega-institute/trureturing/blob/5f749ade652957c89e6b8b8d7799e7e5e4947903/Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge "钉版完整S／proper least／谱性接口及其纸面与形式化范围。"
[Q123BHS]: https://github.com/the-omega-institute/trureturing/blob/5f749ade652957c89e6b8b8d7799e7e5e4947903/Library/QuantumStates/barnumhilgert2019spectral.md "钉版共同框架谱性、全长度强对称及条件Jordan入口。"
[Q123Mixed]: https://github.com/the-omega-institute/trureturing/blob/817dee4ff1398b8a0cedf20bd54e6836d71708b3/D5/S3/Quantum/Foundation/MixedExclusionGeometry.lean "显式weakPair前件的原混态排除几何；非裸EB3输入。"
[Q123Proj]: https://github.com/the-omega-institute/trureturing/blob/1ce3f594c6084f2350b480c2850db393549065cc/D5/S3/Quantum/Foundation/PositiveComplementaryProjections.lean "whole_positive_projections显式要求weakPair，不由本章闭商像代付。"

### 123.15 完整白话

把所有原状态看成同一块完整凸实体，每个原纯态背后都有一颗由全部原测试定义的实心排除球。站在一个对所有趋近原标签都保持全部零测试稳定的正规标签上，原球面每个邻标签又带来一颗真正经过脚下的花瓣球；沿这颗花瓣穿过球心，走到与脚下相反的远端。两个真实球的原测试公式能在整个实体上对起来：远端的确认测试在原球上保留一段由同一原单位量出的最低读数，因此所有这些远端都不能塌回脚下，否则完整确认测试的稳定性会要求这段固定读数同时消失。于是从脚下向外看的三维比值影像不再只剩可能漏点的影子；它完整闭合，外壳光滑而且严格凸，每个方向都由一个真实远端支撑。但外壳仍可能超出里面那颗原单位球，这正是有限费用和一份原单位之间的差别。要把被法向商压掉的原单位找回来，就问每个影点最少需要多少原单位才能从原锥中提升：最小值确实取得，费用有界，费用恰为一的点准确组成原来的整颗单位球，而一个真实支撑点的费用正是那颗花瓣远端高度的倒数。外壳边界若有一点费用一，就接回已有的原中点接触；这种正规标签若在整个原纯标签域稠密，已有定理才把全部原纯态、混态、效应、Born概率、数学POVM和谱结构一起识别成同一复三能级静态模型。若某个标签始终不能接触，失败还能压成同一有限批真实花瓣远端：它们的影像会包住一整颗严格放大的单位球，使每一个方向的第三候选测试都在批内至少一个真实原点上出现统一的严格负值。现在真正要补的，是从这些球同属一个完整原实现、共享全部原测试与同一原单位的关系中，证明任何有限批都留有一个共同单位方向，使批内所有第三候选读数同时非负；这项有限实际相容性F仍未证明，至多三个点的自动相容或抽象几何图都不能替它完成。有限证书、最省提升和闭商图也都不是制备、仪器或时间演化；实际来源、操作、全部有限复合、纠缠资源、全旁观CP、同族事件与仪器、物理钟、Hamiltonian和数值 $\hbar$ 仍完整保留各自原合同。

## 追加锚（本行以下为增补区）
