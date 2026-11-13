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

## 124. 原单位费用边界的准确跳跃、互补确认与反向整球塌缩

**约定 124.0（原域与前置范围）。** 本章的121、122均指[THREE_COPY第七卷121、122][Q124T]，VII103—104指[完整排除面第七卷][Q124VII]，IX116、118、120指[排除球第九卷][Q124IX]。始终使用123.1的同一个有限维原实现：闭尖生成锥 $C\subset V$、严格正原单位 $u$、整个紧态基 $K=C\cap\{u=1\}$、全部原纯点 $P=\operatorname{ext}K$、全部原效应 $\mathcal E=[0,u]_{C^*}$，以及

$$
\mathcal F_b=\{f\in\mathcal E:f(b)=1\},\quad
T_b(x)=\min_{f\in\mathcal F_b}f(x),\quad
D_b=\{x\in K:T_b(x)=0\},\quad
\mathcal A_b=\{e\in\mathcal F_b:e|_{D_b}=0\}.
\tag{Q124.1}
$$

EB3要求每个完整 $D_b$ 都是整个仿射闭三球，Inj要求 $D_b=D_c\Rightarrow b=c$。原零边 $b\perp c$ 仍由同一张原效应的一、零读数定义，通过补效应对称。三条真实边、三个原非负效应在全 $V$ 上和为 $u$、同一实际三结果仪器是三个不同层次。既不输入全纯数值PR，也不输入weakPair、全Pair、正过滤、全域整球连续或 $P$ 紧性。本卷第1章的额外联合前件不属于这里的前件。

除124.7中明确列出的裸EB3候选分支外，以下原域推导均假设EB3+Inj。

直接复用VII103.2、104.1及IX118.10：全部非空真面只有原纯单点和完整 $D_b$；每个 $D_b$ 是暴露极大真面，$P\cap D_b=\partial_{\rm rel}D_b$；不同完整球相交时仅交于一个原纯点。在EB3+Inj中，$e\in\mathcal A_b$ 的原零面恰为 $D_b$，原一值面恰为 $\{b\}$，包括对所有原混态的一值面断言。

### 124.1 同一个完整方向球面上的原对象

固定任意 $p\in P_{\rm reg}$，其中 $P_{\rm reg}=P_0\cap\operatorname{Cont}(\mathcal B)$、$P_0=\{b:\mathcal A_b\text{ 为单点}\}$、$\mathcal B(b)=\{h\in\mathcal E:h(b)=0\}$，连续性量化从整个原 $P$ 趋近的全部纯序列。123.1已给 $P_{\rm reg}$ 在整个 $P$ 中稠密；这里不把它限制到一颗邻球面来取得密度。写

$$
\begin{gathered}
\mathcal A_p=\{e_p\},\quad g=u-e_p,\quad D_p=c+B\mathbb B^3,
\quad H(c+Bw)=w,\quad H_i\in\operatorname{span}N_p,\\
N_p=\{h\in C^*:h(p)=0\},\qquad
\rho(v)=\sup_{x\in K\setminus\{p\}}\frac{-v\cdot H(x)}{g(x)}.
\end{gathered}
\tag{Q124.2}
$$

IX120.8—120.12已经给限制同构、$\dim\operatorname{span}N_p=4$、$g\in\operatorname{ri}N_p$、$g>0$ 于 $K\setminus\{p\}$、$\|H(x)\|\le M_Hg(x)$，以及有限Lipschitz凸正齐次函数 $\rho$。对全部 $v\in S^2$ 定义

$$
\begin{gathered}
q_v=c+Bv\in P_0,\qquad F_v=D_{q_v},\qquad
 e_{q_v}=\frac{\rho(v)g+v\cdot H}{1+\rho(v)},\\
a_v=\text{$p$ 在整颗 $F_v$ 内的对径点}\in P_0,\qquad
m(v)=g(a_v)=\max_{F_v}g,\qquad z_v=H(a_v)/m(v),\\
d(v)=e_{a_v}(p),\qquad G_v=D_{a_v},\qquad
L_v=u-e_{q_v},\qquad R_v=u-e_p-e_{q_v}.
\end{gathered}
\tag{Q124.3}
$$

$a_v$ 与原 $D_p$ 上的 $q_{-v}$ 不能预先等同。$R_v$ 只是全 $V$ 上的原线性泛函，尚未断言属于 $C^*$。$F_v$ 与 $G_v$ 是不同层的完整球：前者标签为 $q_v$，后者标签为 $a_v$，且 $q_v\in G_v$。

复用122.4、123.3—123.7：存在同一个 $\sigma=\sigma_p>0$，使全部方向满足

$$
\begin{gathered}
\sigma\le m(v)\le1,\qquad 0\le d(v)<1,\qquad
H|_{F_v}=z_vg|_{F_v},\\
Z=\{H(x)/g(x):x\in K\setminus\{p\}\}
\text{ 紧、严格凸，含整个 }\mathbb B^3,\\
\rho(v)=h_Z(-v),\qquad \nabla\rho(v)=-z_v\quad(v\in S^2),\qquad
\rho\in C^1(\mathbb R^3\setminus\{0\}),\\
\Lambda(z)=\inf\{u(y):y\in C,\ g(y)=1,\ H(y)=z\},\qquad
\Lambda(z_v)=1/m(v),\qquad \{\Lambda=1\}=\mathbb B^3.
\end{gathered}
\tag{Q124.4}
$$

可行域是 $Z$，最省原单位费用达到，$1\le\Lambda\le1/\sigma$ 于 $Z$，扩展实值 $\Lambda$ 凸且下半连续。122.5还给 $\partial Z$ 每点唯一支撑超平面；123.5给 $v\mapsto z_v$ 连续。以下所有极限使用固定原范数 $\|h\|_K=\max_K|h|$，状态Hausdorff距离使用任一固定辅助有限维范数。

把123.3的全原空间确认恒等式写成

$$
\boxed{\quad
 e_{a_v}=d(v)e_p+A(v)R_v,\qquad
 A(v)=d(v)+\frac{1-d(v)}{m(v)},\qquad
 R_v=\frac{g-v\cdot H}{1+\rho(v)}.
\quad}
\tag{Q124.5}
$$

这是既有恒等式的记号整理，不另作新定理；其原证明由两个真实完整球图在全 $V$ 上消元，不从球内等式擅自延拓。123.4的统一正高度也直接复用，不再次证明。

### 124.2 每个原效应聚点的完整线段与高度跳跃

**定理 124.1（全部方向序列的联合聚点约束）。** 对任意 $v_n\to v$，记 $m_n=m(v_n)$、$d_n=d(v_n)$、$a_n=a_{v_n}$、$e_n=e_{a_n}$。沿任意满足

$$
m_n\to\ell,\qquad d_n\to\delta,\qquad a_n\to a
\tag{Q124.6}
$$

的共同子列，都有

$$
\sigma\le\ell\le m(v),\qquad a\in F_v\setminus\{p\},\qquad
 g(a)=\ell,\qquad H(a)=\ell z_v.
\tag{Q124.7}
$$

原效应沿该子列自动在全域范数收敛，极限是

$$
E=\delta e_p+
\frac{\delta+(1-\delta)/\ell}{1+\rho(v)}(g-v\cdot H).
\tag{Q124.8}
$$

所有这些极限都在同一条完整原效应线段上：

$$
\boxed{\quad E\in[e_{a_v},L_v],\qquad
\delta\in[d(v),1],\qquad
E=\lambda e_{a_v}+(1-\lambda)L_v,\quad
\lambda=\frac{1-\delta}{1-d(v)}.\quad}
\tag{Q124.9}
$$

若 $\ell<m(v)$，必有 $\delta=1$、$E=L_v$，而且 $a\ne a_v$。若 $\delta<1$，必有 $\ell=m(v)$、$a=a_v$。这些陈述不假设 $a$ 纯。

证明。$e_{q_{v_n}}$ 在全原空间连续，且 $e_{q_{v_n}}(a_n)=0$，故 $e_{q_v}(a)=0$，即 $a\in F_v$。原评价给 $g(a)=\ell\ge\sigma>0$，所以 $a\ne p$，而高度最大值给 $\ell\le m(v)$。由(Q124.4)中整个 $F_v$ 的关系取得 $H(a)=\ell z_v$。这里没有把纯序列的极限预先判为纯。紧 $K$ 和紧区间 $[\sigma,1]\times[0,1]$ 允许每个子列再取这样的共同子列。

(Q124.5)的系数在 $m\ge\sigma$ 上连续，$R_{v_n}\to R_v$，故得到全 $V^*$ 的极限(Q124.8)，亦即全 $K$ 上一致收敛。原效应区间闭，故 $E\in\mathcal E$。在 $F_v$ 上有 $v\cdot H=-\rho(v)g$ 和 $e_p=1-g$，所以

$$
E|_{F_v}=\delta+(1-\delta)g/\ell.
\tag{Q124.10}
$$

特别地 $E(a_v)=\delta+(1-\delta)m(v)/\ell\le1$。若 $\ell<m(v)$，唯一可能是 $\delta=1$；此时(Q124.8)变成 $e_p+R_v=L_v$，而 $g(a)<g(a_v)$ 给 $a\ne a_v$。若 $\delta<1$，反过来只能 $\ell=m(v)$；$g$ 在真实球 $F_v$ 上唯一达到最大值的点是对径端 $a_v$，故 $a=a_v$。

剩下 $\ell=m(v)$ 的情形。此时 $E(a_v)=1$、$E(q_v)=0$。把IX120.12的完整原边区间用于锚点 $q_v\in P_0$ 及其真实邻点 $a_v$，得到

$$
\{b\in\mathcal E:b(q_v)=0,b(a_v)=1\}=[L_v,e_{a_v}].
\tag{Q124.11}
$$

这不是球上的限制区间。两端在 $p$ 的读数分别为 $1,d(v)$，后者严格小于一，故评价于 $p$ 唯一确定凸系数，得到(Q124.9)。$\ell<m(v)$ 时 $E=L_v$ 也满足同一结论。证毕。

因此 $m$ 在整个 $S^2$ 上上半连续，这是122.11的已付结论；新取得的方向是

$$
d(v)\le\liminf_{n\to\infty}d(v_n),
\tag{Q124.12}
$$

即反向确认读数下半连续。确实，沿实现下极限的子列再取(Q124.6)，(Q124.9)即给该不等式。若 $a_n$ 有混态聚点，该聚点必满足 $\ell<m(v)$，因为 $\ell=m(v)$ 的唯一点是纯的 $a_v$。若聚点纯，它属于实际 $P\cap F_v$；仅有纯性仍不能把它等同于 $a_v$。

### 124.3 严格跳跃、互补极限与反向完整球

**定理 124.2（严格下降的全序列后果与准确单向界）。** 对任意 $v_n\to v$，若

$$
m(v_n)\longrightarrow\ell<m(v),
\tag{Q124.13}
$$

则整个序列满足

$$
\boxed{\quad d(v_n)\to1,\qquad
\|e_{a_{v_n}}-(u-e_{q_v})\|_K\to0,\qquad
 d_H(G_{v_n},\{q_v\})\to0.\quad}
\tag{Q124.14}
$$

每个端点聚点均在同一个实际 $F_v$ 的高度 $\ell$ 上，并且不同于 $p,a_v$；不排除其为混态，若仍纯则必为非正规纯点。对任意 $v_n\to v$，不加(Q124.13)也有

$$
d(v_n)\to1
\quad\Longleftrightarrow\quad
\|e_{a_{v_n}}-L_v\|_K\to0,
\tag{Q124.15}
$$

这两项都推出(Q124.14)的整球塌缩。

更一般地，若 $d(v_n)\to\delta>d(v)$，则仍有 $G_{v_n}\to\{q_v\}$；当 $\delta<1$ 时，端点却满足 $a_{v_n}\to a_v$、$m(v_n)\to m(v)$。

证明。若严格下降时 $d(v_n)$ 不趋一，选一条保持离一有正距离的子列，再用紧性取(Q124.6)，违反定理124.1。因此全序列 $d(v_n)\to1$。为使全效应极限的控制明确，(Q124.5)给准确恒等式

$$
e_{a_w}-L_w=(1-d(w))
\left[-e_p+\left(\frac1{m(w)}-1\right)R_w\right].
\tag{Q124.16}
$$

$R_w=g-e_{q_w}$ 是两个原效应之差，故 $\|R_w\|_K\le1$，$\|e_p\|_K=1$。方括号在 $p$ 的值是 $-1$，从而

$$
1-d(w)\le\|e_{a_w}-L_w\|_K
\le\frac{1-d(w)}{m(w)}\le\frac{1-d(w)}\sigma.
\tag{Q124.17}
$$

再用 $L_{v_n}\to L_v$ 就得到(Q124.15)，其反向也可直接评价 $p$。

$L_v$ 的完整原零面是 $e_{q_v}$ 的一值面，恰为纯单点 $\{q_v\}$。若有 $x_n\in G_{v_n}$ 离 $q_v$ 保持正距离，紧 $K$ 允许取 $x_n\to x\ne q_v$；全域一致收敛与 $e_{a_{v_n}}(x_n)=0$ 会给 $L_v(x)=0$，矛盾。球非空，故这正是Hausdorff趋于该单点。全部端点聚点的陈述由(Q124.7)及严格高度差取得。

最后考虑 $\delta>d(v)$。对每个子列再取高度与端点的共同聚点，(Q124.9)把效应极限唯一确定为 $\lambda e_{a_v}+(1-\lambda)L_v$，其中 $0\le\lambda<1$。这两个非负效应的共同零面是 $\{q_v\}$：$L_v$ 仅在 $q_v$ 为零，且 $q_v\in G_v$。因此每个子列有同一效应极限，整个序列收敛，刚才的紧性论证再给整球塌缩。若 $\delta<1$，定理124.1使每个高度及端点聚点分别等于 $m(v),a_v$，所以全序列也如此收敛。证毕。

**纯极限与逆向的边界。** 若严格下降的一条端点子列收敛到 $a\in P_{\rm reg}$，123.2会给 $D_{a_{v_n}}\to D_a$，与(Q124.14)冲突。因此严格下降不能有正规纯聚点；它并未被证明不能有其他纯聚点。若聚点混，IX118.4的已付结论恰给 $a\in\operatorname{ri}D_{q_v}=\operatorname{ri}F_v$，与这里的原面位置一致，不构成矛盾。

没有证明 $d(v_n)\to1$ 必有严格高度下降。它允许极限效应的一值面扩大为整个 $F_v$，但并不指定端点在该面内的哪一高度。也没有证明 $G_{v_n}\to\{q_v\}$ 必有 $d(v_n)\to1$；定理已说明 $d(v_n)\to\delta\in(d(v),1)$ 也足以产生同一塌缩，而没有断言这种序列必在某个完整EB3模型中存在。尤其不能把零面极限单点误读为一值标签的极限仍纯。

这里塌缩的是第二层 $G_{v_n}=D_{a_{v_n}}$。第一层 $F_{v_n}$ 已由123.4保留正高度，因 $p,a_{v_n}\in F_{v_n}$，其直径有正下界 $\sigma/\|g|_{\ker u}\|$；分母非零，因为 $g$ 在某条这些原弦上不恒定。不能把这两层完整球混为一颗。

### 124.4 跨真实远端的确认检验与支撑余差

**定理 124.3（同原实现的高度差估计）。** 对全部 $v,w\in S^2$ 定义同一凸支撑函数的Bregman余差

$$
\mathfrak B(v,w)=\rho(v)-\rho(w)-\nabla\rho(w)\cdot(v-w)\ge0.
\tag{Q124.18}
$$

则在实际原态 $a_w$ 上有精确读数

$$
R_v(a_w)=m(w)\left(1-\frac{\mathfrak B(v,w)}{1+\rho(v)}\right),
\tag{Q124.19}
$$

以及准确约束

$$
\begin{split}
(1-d(v))(m(w)-m(v))
&\le\bigl(d(v)m(v)+1-d(v)\bigr)m(w)
       \frac{\mathfrak B(v,w)}{1+\rho(v)}\\
&\le\frac{\mathfrak B(v,w)}{1+\rho(v)}.
\end{split}
\tag{Q124.20}
$$

因而

$$
m(w)-m(v)\le
\frac{\mathfrak B(v,w)}{(1-d(v))(1+\rho(v))}.
\tag{Q124.21}
$$

Bregman余差是成熟凸分析记号；这里的新增关系是同一个原确认在另一个真实远端上的全域上界，给出了(Q124.20)的原高度约束。

证明。由 $H(a_w)=m(w)z_w$、$\nabla\rho(w)=-z_w$、$w\cdot z_w=-\rho(w)$，

$$
1-v\cdot z_w=1+\rho(v)-\mathfrak B(v,w).
$$

代入 $R_v$ 的全原空间公式即得(Q124.19)。原效应满足 $e_{a_v}(a_w)\le1$；使用(Q124.5)、$e_p(a_w)=1-m(w)$，得到

$$
d(v)+(1-d(v))\frac{m(w)}{m(v)}
-A(v)m(w)\frac{\mathfrak B(v,w)}{1+\rho(v)}\le1.
$$

移项后乘以 $m(v)>0$，就是(Q124.20)第一行。因为 $m(v),m(w)\le1$、$0\le d(v)<1$，系数 $\bigl(d(v)m(v)+1-d(v)\bigr)m(w)\le1$，给第二行。最后除以严格正的 $1-d(v)$ 即可。没有把 $R_v$ 当成正效应；原上界用的是完整合法的 $e_{a_v}$，所以没有预付接触或F。证毕。

### 124.5 连续费用边界的常值刚性

**定理 124.4（五个全方向表述的准确等价）。** 在同一个固定 $p\in P_{\rm reg}$，以下五项等价：

1. $\Lambda|_{\partial Z}$ 连续；
2. $m:S^2\to[\sigma,1]$ 连续；
3. 真正原端点映射 $v\mapsto a_v\in K$ 连续；
4. 存在同一 $M_p\in[\sigma,1]$，使 $m(v)=M_p$ 对全部 $v\in S^2$；
5. 存在同一 $\lambda_p\in[1,1/\sigma]$，使 $\Lambda(z)=\lambda_p$ 对全部 $z\in\partial Z$。

成立时 $\lambda_p=1/M_p$。前三项也逐点等价：$\Lambda|_{\partial Z}$ 在 $z_v$ 连续，当且仅当 $m$ 在 $v$ 连续，当且仅当真实原端点映射在 $v$ 连续。更局部地，若 $m$ 在一个连通开方向域 $U\subset S^2$ 连续，它在 $U$ 上为常数。

证明。先说明 $v\mapsto z_v$ 是 $S^2\to\partial Z$ 的同胚。其连续性由123.5支付；每个边界点有支撑超平面，而支撑点唯一，给满射；122.5的唯一支撑超平面使 $z_v=z_w$ 只能 $v=w$，给单射。紧域到Hausdorff域的连续双射是同胚。因此 $\Lambda(z_v)=1/m(v)$ 及 $m\ge\sigma$ 给1与2等价，并给4与5等价。

若2成立，对任意 $v_n\to v$，每个 $a_{v_n}$ 聚点由定理124.1在 $F_v$ 中达到高度 $m(v)$；唯一性迫它为 $a_v$，紧性给整个序列收敛，所以3成立。反过来 $m(v)=g(a_v)$ 使3直接给2。

剩下2到4是真正的常值结论。$\rho$ 在非零方向 $C^1$，其梯度在单位球面的一个紧邻壳上一致连续。对充分接近的 $v,w$，沿连接它们的线段积分梯度，得到

$$
0\le\mathfrak B(v,w)
\le\|v-w\|\,\omega(\|v-w\|),\qquad \omega(t)\longrightarrow0.
\tag{Q124.22}
$$

此处只用一阶连续可微性，不假设二阶光滑。沿任意光滑方向弧 $v(t)$，令连续函数 $f(t)=m(v(t))$。对每个固定的 $t$，(Q124.21)中的分母 $1-d(v(t))$ 严格正；$\|v(t+h)-v(t)\|=O(h)$ 及(Q124.22)给

$$
\limsup_{h\downarrow0}\frac{f(t+h)-f(t)}h\le0.
\tag{Q124.23}
$$

这一步不需要 $d$ 连续，也不需要沿整弧的统一反向缺口。

为把该局部不等式变成全弧结论，若某 $s<t$ 有 $f(t)>f(s)$，取 $0<\varepsilon<(f(t)-f(s))/(t-s)$。连续函数 $f(\tau)-\varepsilon\tau$ 在 $[s,t]$ 达到最小值，因末值大于首值，某个最小点 $\tau_0<t$。向右的差商在这个最小点非负，然而(Q124.23)使其上极限至多 $-\varepsilon<0$，矛盾。因此 $f$ 沿该弧非增。对反向参数化重复同一论证，便得整弧常值。

连通开 $U$ 可由有限段光滑弧连接任意两点，故得到局部版本。整个 $S^2$ 连通且可如此连接，给4。4显然给2，完成全部等价。证毕。

边界费用的下半连续性是123.7已有结果；本定理没有把下半连续升级成连续，而是证明一旦全边界连续，其值必须恒定。逐点的 $m>0$、统一的 $m\ge\sigma$、$z_v$ 连续以及光滑严格凸影壳都不等于这个额外连续性结论。

### 124.6 反向确认缺口、连续性与两层非塌缩

**定理 124.5（不同稳定条件的准确蕴含）。** 对固定 $p\in P_{\rm reg}$，有以下结论。

(a) 在每个 $v$，$d$ 在 $v$ 连续，当且仅当 $w\mapsto e_{a_w}$ 在 $v$ 按全原效应范数连续。这两项均推出 $m$ 和 $a$ 在 $v$ 连续。

(b) 若存在方向开邻域 $U\ni v$ 与 $\varepsilon>0$，使 $d(w)\le1-\varepsilon$ 对全部 $w\in U$ 成立，则 $m,a$ 在 $U$ 连续，且 $m$ 在 $U$ 每个连通分支上为常数。特别地，全 $S^2$ 上的统一反向确认缺口给定理124.4的五项。

(c) 若存在方向开邻域 $U\ni v$ 与 $\eta>0$，使 $\operatorname{diam}G_w\ge\eta$ 对全部 $w\in U$ 成立，则 $d,e_a,m,a$ 在 $U$ 全部连续，且 $m$ 在每个连通分支上为常数。全 $S^2$ 上的 $\inf_w\operatorname{diam}G_w>0$ 因而还给 $d$ 全方向连续和某个统一反向确认缺口。

(d) 定义

$$
\Omega_{\rm rev}=\bigcup_{j\ge1}
\operatorname{int}_{S^2}\{v:d(v)\le1-1/j\}.
\tag{Q124.24}
$$

则 $\Omega_{\rm rev}$ 开稠密，$m$ 在其中局部常值。该结论来自这个同一方向域中的下半连续性与Baire性质；没有把整个 $P$ 上的残余集限制到球面。

证明。(a)若 $d$ 在 $v$ 连续，每条 $v_n\to v$ 都有 $d_n\to d(v)<1$；定理124.1排除所有严格高度下降，故 $m_n\to m(v)$、$a_n\to a_v$。代入(Q124.5)得到原效应范数连续。反向评价固定原态 $p$ 即得 $d$ 连续。

(b)在 $U$ 任取趋近某 $w\in U$ 的方向序列，尾项留在 $U$。若 $m$ 不连续，上半连续性和紧高度区间给一条 $m_n\to\ell<m(w)$ 的子列，定理124.2迫使 $d_n\to1$，违反共同缺口。因此 $m$ 在 $U$ 连续，定理124.4给端点连续及分支常值。

(c)若 $d$ 在某 $w\in U$ 不连续，已证下半连续性允许取 $w_n\to w$、$d(w_n)\to\delta>d(w)$。定理124.2使 $G_{w_n}\to\{q_w\}$，违反直径下界。因此 $d$ 在 $U$ 每点连续，(a)给其余连续性，124.4给局部常值。若下界在全方向成立，$d<1$ 连续于紧 $S^2$，其最大值严格小于一，故取得共同 $\varepsilon>0$。

(d)因 $d$ 下半连续，每个 $\{d\le1-1/j\}$ 闭；又每个 $d(v)<1$，这些闭集覆盖 $S^2$。若它们的内部之并不稠密，在某非空开方向域内，这些闭集全都无处稠密却可数覆盖该Baire域，矛盾。在每个这样的内部应用(b)，便得局部常值。证毕。

上述蕴含没有被改写成未经证明的双向关系。未证明费用边界连续会给 $d$ 连续、统一反向缺口或反向整球非塌缩；未证明统一反向缺口会给 $d$ 连续或 $G_w$ 非塌缩；也未证明 $d$ 连续足以让整个 $G_w$ Hausdorff连续。效应连续只直接控制其零面的上极限，不能自动供应零面的下逼近。第一层 $F_w$ 的直径下界已由123.4得到，却不等于(c)的第二层下界。

这些未证反向不是完整EB3中的反例断言。任意给定光滑凸壳、凸费用函数或抽象球族，都没有同时给出同一个原 $C,u$ 的全部纯点、混态、效应及每个完整三球，不能用来反驳这些同域反向。

### 124.7 常值高度仍缺原单位接触

**定理 124.6（常值分支中的接触值与完整静态候选）。** 对某固定 $p\in P_{\rm reg}$，若定理124.4的等价条件成立，记其共同高度为 $M_p$，则

$$
\mathsf F(p)
\Longleftrightarrow W(D_p)=1
\Longleftrightarrow \theta_p=1
\Longleftrightarrow M_p=1
\Longleftrightarrow Z_p=\mathbb B^3.
\tag{Q124.25}
$$

这里 $\theta_p=\min_{\partial Z_p}\Lambda_p$，而123.14的有限实际相容性完整保留为

$$
\mathsf F(p):\quad
\forall k\ge1\ \forall w_1,\ldots,w_k\in S^2\quad
\exists v\in S^2\ \forall i\le k:\quad
v\cdot H_p(a_{w_i})\le g_p(a_{w_i}).
\tag{Q124.26}
$$

不要求额外稳定性的完整原静态候选仍是以下相同模型类：

$$
\begin{array}{c}
\mathrm{EB3}+\mathrm{Inj}+\overline{\{p\in P_{\rm reg}:\mathsf F(p)\}}^{\,P}=P\\
\Updownarrow\\
\mathrm{EB3}+\mathsf{DC}
\quad\Longleftrightarrow\quad\mathrm{EB3}+\mathsf{MC}
\quad\Longleftrightarrow\quad\mathrm{EB3}+\forall b\in P:\ W(D_b)=1\\
\Updownarrow\\
\exists\,\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V
\text{ 实线性},\quad\Phi(\mathrm{PSD}_3)=C,\quad u\Phi=\operatorname{Tr}.
\end{array}
\tag{Q124.27}
$$

准确地，令 $W(F)=\max_{f\in\mathcal E}(\max_Ff-\min_Ff)$，令

$$
\mathcal T_{\rm mid}=\{b\in P:\exists x\in D_b,\ (b+x)/2\in\partial_{\rm rel}K\}.
$$

$\mathsf{DC}$ 表示 $\overline{\mathcal T_{\rm mid}}^{\,P}=P$，$\mathsf{MC}$ 表示 $\mathcal T_{\rm mid}=P$，准确沿121.1、122.1—122.2的定义。等价式是123.10、123.15及122.2的复用，不计为新的静态分类。

证明。在常值分支，定理124.4给 $\theta_p=1/M_p$；123.15和(Q123.31)已给F、满宽、$\theta_p=1$等价，故前四项等价。若 $M_p=1$，全部 $a_v$ 都在 $D_p$，亦在 $F_v$；123.11使每个 $\rho_p(v)=1$。全方向支撑函数于是与单位球相同，故 $Z_p=\mathbb B^3$。反向若 $Z_p=\mathbb B^3$，123.7的准确单位费用层给全部边界费用一，从而 $M_p=1$。

对(Q124.27)的正向，正规F标签稠密给原接触标签稠密；122.2以原宽度的上半连续把稠密接触升级成全部原标签满宽，然后才由IX116.17及VII104、VIII113的完整前件取得同原 $\Phi$、全Pair和全域数学三元补全。没有在Pair之前输入共同仪器或正互补投影。

反向量化整个矩阵原模型：任意纯 $p=zz^*/(z^*z)$ 的全部确认矩阵恰为 $p\oplus A$，$0\preceq A\preceq I_{z^\perp}$；对任意密度矩阵 $\rho$，$T_p(\rho)=\operatorname{Tr}(p\rho)$，完整 $D_p$ 是 $z^\perp$ 上全部密度矩阵，故EB3和Inj成立且 $e_p=f_p$。对任意纯 $p_n\to p$、任意完整零效应矩阵 $0\preceq A\preceq I$、$\operatorname{Tr}(Ap)=0$，正性给 $Ap=0$。令 $Q_n=I-p_n$，则 $Q_nAQ_n$ 为零于 $p_n$ 的合法全域效应，且

$$
\|Q_nAQ_n-A\|_{\rm op}\le2\|p_n-p\|_{\rm op},
$$

统一量化整个零效应集合；上包含由紧性与评价给出。因此全部 $P=P_{\rm reg}$。每个 $v$ 有 $a_v=q_{-v}$、$m(v)=1$、$d(v)=0$、$Z_p=\mathbb B^3$、$\Lambda_p|_{Z_p}\equiv1$，所以全部正规标签满足F，给回整个稠密性条件。矩阵模型也满足124.5中全部稳定条件：$d=0$，而 $G_v$ 含原 $p,q_v$，紧 $D_p$ 不含 $p$，故在任一固定原状态范数下有共同正直径。所有计算通过同一个 $\Phi$ 运输；这些条件在此是反向模型计算，不是推导F的免费前件。证毕。

**准确未决桥。** 新关系支付的是：高度真跳跃必伴随互补确认和第二层整球塌缩；反向确认读数的下半连续性；真实远端之间的合法确认上界给支撑余差控制；费用边界若全连续，其高度必常值。它们没有把常数 $M_p$ 证明成一。若额外假设反向缺口或第二层非塌缩，其后果仍须按124.5称为条件结论，不能当作EB3+Inj已推出这些稳定性。

剩下的联合步骤仍是：由同一原实现中的全部球、效应与同一个原单位，排除123.13的某个有限真实端点批包住严格放大单位球，或直接证明(Q124.26)对每个有限批存在一个共同单位方向；再使这样的正规锚点在整个 $P$ 中稠密。即使已处于常值稳定分支，这一步仍须把 $M_p<1$ 排除。仅仅排除跳跃、取得连续性或常值性，没有检验所有方向的单位预算。没有证明该稳定分支允许 $M_p<1$ 的完整EB3反模型，也没有证明它必为一。全域(O)、WZ或全体原标签的统一球直径下界一旦成立会接回IX118的已有分类，但固定 $p$ 的局部球族条件不能未经证明替代这些全域量词。

裸EB3自动给Inj与F仍为更大的未决目标。本章不宣称独立公理数减少、物理公理最少、全球原创，亦不把已有条件换名计作新增数学。

### 124.8 同一原单体的完整静态QM字典

只在(Q124.27)的完整条件成立后，使用同一个 $\Phi$；以下是123.12及其既有前置的完整静态对应。

| QM内容 | 全部原对象的对应 |
| --- | --- |
| 纯态与复射线 | 全部非零 $z\in\mathbb C^3$ 给 $p_z=\Phi(zz^*/(z^*z))$，恰为整个 $P\cong\mathbb{CP}^2$ |
| 混态、质量与混合 | 整个 $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$；$C=\Phi(\mathrm{PSD}_3)$ 保留零与全部非负质量，所有有限凸组合保持，$\dim_{\mathbb R}V=9$ |
| 单位、全部效应与Born概率 | $u\Phi=\operatorname{Tr}$；整个 $\mathcal E$ 恰为 $f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$、$0\preceq A\preceq I_3$，包括所有混态输入、零、单位与补 |
| least确认与完整排除球 | least效应为秩一投影；$T_{p_z}(\Phi\rho)=\operatorname{Tr}(zz^*\rho)/(z^*z)$，完整 $D_{p_z}$ 为 $z^\perp$ 上全部密度矩阵 |
| 纯比较与二元零边 | $T_{p_z}(p_w)=\lvert z^*w\rvert^2/((z^*z)(w^*w))$，零边恰为复内积正交 |
| 框架与数学三元完成 | 每条原正交边有唯一第三纯点；三秩一投影之和为 $I_3$，三原非负效应之和为 $u$，Kronecker读数成立，容量为三 |
| 全部有限数学POVM | 每个有限结果数的全部 $f_j\ge0,\sum_jf_j=u$ 恰对应全部 $A_j\succeq0,\sum_jA_j=I_3$ |
| 谱与全部可观测量 | 每个混态有三项正交谱分解，含零权、重复谱；全部实线性可观测量对应全部Hermitian矩阵并有实谱分解 |
| 派生结构 | 中心 $\Phi(I_3/3)$、内积 $B(\Phi X,\Phi Y)=\operatorname{Tr}(XY)$、Jordan积 $\Phi((XY+YX)/2)$ 都在条件重构后取得 |

向量叠加作为同一复射线模型的数学结构可表达；实际相干制备、相位参考与可调用门仍各需原来源及操作合同。这个静态字典量化全部原纯态、混态、效应和单位，既不是只匹配纯比较表，也没有自动供应复合、事件、仪器或物理时间。

### 124.9 原来源、操作、有限复合、仪器与时间合同

**共同来源与全部原操作。** 123.13及其所引VIII113.11、VIII112.9、IX120.11、121.12、122.14的同一原装饰元组 $\mathcal O$ 完整保留：共同来源域、全部中点实现、原概率像紧性、全测试表及闭性、零／单位／补／有界倍增、重复标签及每种同中点实现；全部非负质量、零／次归一／不等质量，过程与参考各自的完整相关联合输入域。原 $L,p,\omega,K,M$、两次同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE之后的整个H13、每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量及空活跃集都由原消费者承担。操作合同的原映射 $p$ 与本章锚点不是同一类型。

设备／事件／来源绑定、全部菜单分支、参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来与每个中间切口，以及VI89.9—89.10的原生／细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption和资源合同均保留。最省提升、商读数、支撑余差、极限球和有限负证书都是数学对象，不供应这些实际制备或接线。

**所有有限联合层级。** 对每个有限 $N\ge1$ 仍需实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、完整 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 与整个原效应区间。每个实际分块 $a+b=N$ 均保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
\tag{Q124.28}
$$

同一产品配对、严格张量单位、全部原因子置换及逆的正性、规范重括号、指定运输下不连续位置分块都保留。二份比较量化整个联合 $S_2$：每个产品或纠缠纯点 $b\in P_2$、每个有限纯准备族 $q_\ell\in P_2$、全部非负 $t_\ell$ 且和为一，包括零权和重复标签，满足VIII111.35；不是只检验产品态。

三项具名供应分别保留：原低二份 $q=1,2$ 的least／谱性／正面投影与保纯到Jordan桥；唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩与实维乘法的复型选择；同一实际两因子的产品正规形。非经典支路保留同一保迹局部坐标、同一最大块 $n_r=L\ge2$ 的 $\mathsf F_{\max}$：同一含相位正交基给

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad
u_3(\Delta_r)=L.
\tag{Q124.29}
$$

其余三份扇区零，归一原源为 $\Delta_r/L$；不预付三份纯性或实际制备。全经典 $L=1$ 支路不要求该资源。只有联合前件与三项供应齐备后，才消费已有全有限层级定理。单体几何不制造 $S_2$、纠缠来源、叉口资源或高阶张量锥；复三能级二、三份秩为九、二十七，高阶载体不再要求满足单体EB3或秩三W。

**全旁观CP、事件与同族仪器。** 原数学全旁观正性仍量化每个 $b\ge0$ 和任意含纠缠的共同输入：

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{Q124.30}
$$

只有全联合层级已供应，通常CP、矩形跨扇区Kraus与逐输入TP/TNI预算才沿原Choi桥取得。同一事件的CP需原完整提升、实际探针与相容核；全部数学CP-TNI分支成为实际事件仍需事件饱和选择。仪器需同族共同输入预算、接线、记录、粗粒化与校准；仅正质量分支条件归一，零质量分支不强定归一条件态。Lüders更新另需同一分支锐效应、接受态中性与输出校准。三条真实原边、数学和为 $u$、全部数学POVM、有限证书及极限线段都不能替代同族实际仪器。

**时间、Hamiltonian与 $\hbar$。** 原钟、实际动态来源、连续齐次可逆时间群、单位与 $\hbar$ 仍为独立合同。若另给同一载体的全实时间连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，有限维生成元只描述该额外供应，静态几何不选择它。已重构复块中，给定保迹酉时间族的通常表达为

$$
U_t=\exp(-itH/\hbar),\quad\rho_t=U_t\rho U_t^*,\quad
\mathcal L(\rho)=-\frac i\hbar[H,\rho],\quad H=H^*.
\tag{Q124.31}
$$

全部输入与时间的量词保留。方向参数、邻球行走、极限或证明弧不是物理钟。$H$ 的标量平移不改变态作用；时间重标改变生成元尺度而保留静态模型。恒等族与非平凡Hamiltonian族共享全部静态数据，故实际 $H$、数值 $\hbar$、能量标定、时空和物理空间维数都未由本章取得。

### 124.10 复用与原始文献的准确条件

IX118.4的纯／混标签判据、118.10的零效应最大值与唯一一值面、118.12的固定零测试失稳，121的Baire与残余稳定、122的实际纤维与影壳光滑、123的全空间确认公式、正规正高度、严格凸完整影像与原单位费用均为已付前置。全域非塌缩／开放关系到维数九、全Pair及同原静态重构，已由IX116.12—116.17与IX118.3—118.8承担，不重新计为本章分类。

本章的原域综合是124.1—124.3的全部效应聚点线段、反向读数下半连续、严格高度下降与互补确认及第二层整球塌缩，以及124.3—124.5的跨真实远端确认估计、连续费用边界的常值刚性和反向缺口的局部常值后果。凸Bregman余差、紧性、上／下半连续、Baire、支撑函数一阶可微与单调差商原理都只作成熟中间工具。这里的文献状态为repo-derived的原对象联合推导，不声称全球原创，也不将纸面证明称为kernel核验。

[Alfsen–Shultz][Q124AS]印刷页160的Hilbert ball property量化每一对原极点生成的最小面，要求它是norm-exposed且仿射同构Hilbert球，不只量化已给的排除球。印刷页188 Corollary 7.5对有限维紧凸集准确要求(i) Hilbert ball property与(iii)每个norm-exposed face projective；strong spectrality不是该推论另列的第三个前件。印刷页158在其order-unit／base-norm对偶中的P-projection是弱星连续正压缩投影，须存在同类quasicomplement；两投影在原空间及其对偶上均须满足正核／正像互补。上述两个几何前件和P-projection没有由EB3+Inj、费用连续或(Q124.20)自动取得，所以这个成熟Jordan接口仍为条件接口。

[Kramer][Q124K] §6.3.5要求局部紧、有限覆盖维ANR，才把相应整数局部同调群条件识别为广义流形。§6.4.1要求同一个 $\mathcal I\to P,\mathcal I\to L$ 的实际局部平凡束，纤维分别为同伦 $m'$、$m$ 球；纤维与底须局部紧、有限维ANR，$P,L,\mathcal I$ 须分别为维数 $r-m',r-m,r$ 的广义流形，且同一双映射柱为同调 $(r+1)$ 球。集合论纤维逐个球形、单个固定锚点的连续费用或反向缺口都不自动支付这些量词。

[Labardini-Fragoso–Neumann-Coto–Takane][Q124L] Lemma 2的固定秩面Hausdorff紧性要求面格modular，Lemma 3还要求irreducible，Theorem 1从projective面格出发。未得全Pair或相应面格结构时，不能用这些结论提前封住本章的混态聚点或球塌缩。原MixedExclusionGeometry和PositiveComplementaryProjections的weakPair前件也继续保留，不由名称“互补确认”代付。

[Q124VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2、104.1—104.3；完整排除面接口。"
[Q124IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116、118、120；原域、全域分类、零测试失稳与准确原边区间。"
[Q124T]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "121—122；中点接触、残余稳定、实际影像与支撑纤维。"
[Q124AS]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf "E. M. Alfsen and F. W. Shultz, State spaces of Jordan algebras, Acta Mathematica 140, DOI 10.1007/BF02392307；印刷页158、160、187—188。"
[Q124K]: https://arxiv.org/pdf/math/0104064 "Linus Kramer, Compact polygons；§6.3.5与§6.4.1的ANR、广义流形、真实局部平凡束和双映射柱条件。"
[Q124L]: https://arxiv.org/pdf/0903.0643v1 "Daniel Labardini-Fragoso, Max Neumann-Coto and Martha Takane, Cones and convex bodies with modular face lattices；Lemmas 2、3与Theorem 1。"

### 124.11 完整白话

把同一原状态体想成一块完整凸实体，站在一个对所有趋近原标签都保持全部零测试稳定的正规锚点上，身后是一颗由全部原测试定义的完整排除球。它的球面每个方向都标出一个真实邻点；邻点又带来一颗真正经过脚下的花瓣球，穿过花瓣球心走到另一端，就得到一个真实远端。前一章已经保证这些远端在同一原单位量出的高度不会掉到零，三维影壳也完整、光滑而严格凸。本章追问的是另一种失稳：方向轻轻变化，远端的高度会不会突然比极限方向的远端更低？如果真下降，远端不一定趋向纯态；若极限为混态，它就在极限花瓣的相对内部。与此同时，它的完整确认测试却被迫趋于那个邻点确认测试的补，反向排除的整颗实心球一起缩成邻点，连球里的全部混态也无处可留。这是第二层球的塌缩，不是前一章已经保住高度的第一层花瓣。更细地看，所有确认测试的聚点只能落在真实远端确认与这个补测试之间的一条确定线段上；趋近方向的反向读数下极限，不能低于极限方向本身的反向读数；严格高度下降更迫使这些趋近读数升到一。再让一个真实远端的确认测试去检查另一个远端，因为它在整块原实体上都不能读过一，便得到高度差受到同一影壳支撑余差的约束。余差比方向的一阶变化更小，所以如果整张费用边界连续，沿任何球面弧都不能真正涨高，反向走也不能涨高，最后高度只能处处相同；远端连续与费用连续恰好是这同一件事。反向确认始终离一留有共同缺口，就足以取得这项常值性；若第二层整球也保持非塌缩，还能取得完整确认的连续性。但“处处同高”仍没有把这个高度证明成一，也没有把每个最省提升压到一份原单位。真正缺的仍是同一个完整原实现的联合约束：任何有限批真实花瓣远端，都必须留下一个共同单位方向，使所有第三候选读数同时非负，或等价地排除真实影点包住严格放大单位球。只有这种F在整个原纯标签域的正规锚点中稠密，才接回已有的全部原纯态、混态、效应、Born概率、有限数学POVM和谱结构的复三能级静态模型。三条真实边、数学效应和为单位、同一实际仪器继续分开；商、提升、支撑余差和有限证书都不是物理操作。共同来源、全部原操作、所有有限复合与纠缠输入、叉口资源、全旁观CP、同族事件和仪器、物理钟、Hamiltonian及数值 $\hbar$ 的完整原合同也仍须分别供应。

## 追加锚（本行以下为增补区）

## 125. 单个真实三角的九维原态—效应配对与邻边校准缺口

### 125.1 完整原域、种子层次与既有三窗口结果

**约定 125.1（同一原实现与前件范围）。** 本章的VII103—105指[完整排除面第七卷][Q125VII]，VIII109—111指[排除球第八卷][Q125VIII]，IX116、118、120指[排除球第九卷][Q125IX]，121—122指[THREE_COPY第七卷][Q125T]，123—124指本卷已有章节。取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，以及在 $C\setminus\{0\}$ 上严格正的 $u\in V^*$。始终保留

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_b=\{f\in\mathcal E:f(b)=1\},\qquad
T_b(x)=\min_{f\in\mathcal F_b}f(x),\\
D_b=\{x\in K:T_b(x)=0\},\qquad
\mathcal A_b=\{e\in\mathcal F_b:e|_{D_b}=0\},\\
N_b=\{h\in C^*:h(b)=0\},\qquad
\mathcal B(b)=N_b\cap\mathcal E,\qquad S_b=\operatorname{span}N_b.
\end{gathered}
\tag{Q125.1}
$$

这里是整个原紧态基、全部原纯点、全部原效应和每个标签的完整排除集合。EB3表示每个 $D_b$ 仿射同构于整个闭三球，Inj表示 $D_b=D_c\Rightarrow b=c$。除125.9保留的裸EB3候选外，本章均取EB3+Inj。定义

$$
\begin{gathered}
b\perp c\quad\Longleftrightarrow\quad
\exists f\in\mathcal E:\ f(b)=1, f(c)=0,\\
P_0=\{b\in P:\mathcal A_b\text{ 是单点}\},\qquad
\mathcal A_b=\{e_b\}\quad(b\in P_0),\\
\mathcal T=\{b\in P:\exists c,d\in P,
\ b\perp c, b\perp d, c\perp d\}.
\end{gathered}
\tag{Q125.2}
$$

补效应使原边对称，且 $b\perp c\Longleftrightarrow c\in D_b$，$b\notin D_b$。真实三角只表示三条各自真实的原边。三个非负数学效应在整个 $V$ 上和为 $u$，以及同一实际三结果仪器，是另外两个层次。

直接复用VII103.2、104.1和IX120.2：每个 $D_b$ 是非点紧暴露极大真面，$\mathcal A_b\ne\varnothing$；全部非空真面只有纯单点和完整球；不同完整球相交时仅交于一个原纯点。每个完整球 $F$ 满足 $P\cap F=\partial_{\rm rel}F$、$F=\operatorname{conv}(P\cap F)$。Inj还给每张 $e\in\mathcal A_b$ 的一值面恰为 $\{b\}$，零面恰为 $D_b$；一值面结论包括全部原混态。

**既有结果的准确范围。** VIII109.2—109.3、111.2已经在
$\mathsf W=\mathrm{EB}_{\ge1}+\mathrm{Pair}_{\perp}$ 下证明三球可见空间、共同盲核、直和分解和联合零效应分离的等价式；VIII111.12给其完整几何解释。该入口已经供应全纯least确认、共同正延拓及正面投影。固定全部球均为三球时，VIII113及IX116的既有分类还已给整个 $V$ 九维。以下不把这些结论重计为新的全W结果；所证增量是在未支付全域 $\mathrm{Pair}_{\perp}$、正投影或全纯框架完成的EB3+Inj域，仅从一个实际三角取得准确局部张成，并在一个 $P_0$ 种子上取得双侧配对。121.9已有无需种子的 $\dim V\ge9$，本章不把该维数下界计为新结论。

种子条件有三个层次：$\mathcal T\ne\varnothing$、$P_0\cap\mathcal T\ne\varnothing$、$P_{\rm reg}\cap\mathcal T\ne\varnothing$。其中

$$
P_{\rm reg}=P_0\cap\operatorname{Cont}(\mathcal B)
\tag{Q125.3}
$$

沿123.1量化整个 $P$ 中全部趋近纯序列。第三层蕴含第二层，第二层蕴含第一层；本章不证明反向。$P_0$、$P_{\rm reg}$ 在整个 $P$ 中稠密，仅凭这一稠密性不能推出它们与非空相对闭集 $\mathcal T$ 相交，也不能取得任何固定 $\partial D_b$ 上的相交稠密性；这些相交结论仍未在此取得。

### 125.2 一个真实三角的三球横向方向

**定义 125.2（只由三角与实际球定义的空间）。** 固定任意真实三角 $\triangle=(p_1,p_2,p_3)$，暂不要求其顶点属于 $P_0$。任取 $a_i\in\mathcal A_{p_i}$，记

$$
D_i=D_{p_i},\qquad M_i=\operatorname{span}D_i,\qquad
U_\triangle=M_1+M_2+M_3,\qquad
\eta_\triangle=(p_1+p_2+p_3)/3.
\tag{Q125.4}
$$

对互异 $i,j,k$，$a_j$ 在 $D_i$ 上于 $p_j,p_k$ 取一、零。完整仿射球上一个 $[0,1]$ 值仿射函数若取得一、零，两极值点必为对径。因此

$$
c_i=(p_j+p_k)/2,\qquad d_i=(p_j-p_k)/2.
\tag{Q125.5}
$$

令 $W_i=\operatorname{lin}(D_i-c_i)$，以该球为单位球定义其欧氏内积 $g_i$；于是 $g_i(d_i,d_i)=1$。定义相对于这条三角直径的横向二平面

$$
L_i=\{z\in W_i:g_i(z,d_i)=0\}.
\tag{Q125.6}
$$

这里 $W_i$ 三维，$L_i$ 二维；没有把不同球的内积拼成共同内积。球内的极值公式给

$$
\begin{gathered}
a_j(c_i+z)=\tfrac12(1+g_i(d_i,z)),\qquad
a_k(c_i+z)=\tfrac12(1-g_i(d_i,z)),\\
a_i|_{M_i}=0,\qquad
M_i=\mathbb Rp_j\oplus\mathbb Rp_k\oplus L_i.
\end{gathered}
\tag{Q125.7}
$$

这些限制与所选 $a_i$ 无关，故 $L_i$ 也可写成 $M_i\cap\ker a_j\cap\ker a_k$。

### 125.3 原正法向直接分离九个方向

**定理 125.3（无需全域W的准确三球张成）。** 在EB3+Inj中，每个真实三角满足

$$
\boxed{\quad
U_\triangle=
\mathbb Rp_1\oplus\mathbb Rp_2\oplus\mathbb Rp_3
\oplus L_1\oplus L_2\oplus L_3,
\qquad \dim U_\triangle=9.
\quad}
\tag{Q125.8}
$$

而且 $\eta_\triangle\in\operatorname{ri}K\subset\operatorname{int}C$。这里不推出 $U_\triangle=V$。

证明。先说明唯一支撑所给的跨球消去。非负仿射函数 $h(c+Bz)=\alpha+\ell\cdot z$ 在单位球上非负，并在单位端点 $v$ 为零时，$\alpha\ge\|\ell\|$、$\ell\cdot v=-\alpha$ 迫使 $\ell=-\alpha v$。故该函数是该端点唯一支撑函数的非负倍数，包含恒零情形。

固定互异 $i,j,k$。任意 $h\in N_{p_i}$ 在球 $D_j$ 上非负，在其对径端 $p_i$ 为零。以另一端 $p_k$ 的值确定倍数，得到

$$
h|_{M_j}=h(p_k)a_k|_{M_j},\qquad
h(L_j)=0.
\tag{Q125.9}
$$

这里先在整个仿射球得到等式，再因 $D_j$ 线性张成 $M_j$ 而延至 $M_j$，没有延至整个 $V$。交换 $j,k$，亦得 $h(L_k)=0$。因此 $N_{p_i}$ 消去另外两球的横向平面。

另一方面，$N_{p_i}$ 分离自己的 $L_i$。给定 $0\ne w\in L_i$，取实际球面点

$$
s=c_i+w/\|w\|_{g_i}\in P\cap D_i
$$

及任意 $a_s\in\mathcal A_s$。零边对称给 $p_i\in D_s$，故 $a_s\in N_{p_i}$。它在 $D_i$ 上不超过一，在 $s$ 取一；由于整个原一值面只有 $s$，其限制非恒定。球上仿射函数的最大值方向唯一，故存在 $\beta>0$，使其线性部分沿 $w/\|w\|_{g_i}$，从而

$$
a_s(w)=\beta\|w\|_{g_i}>0.
\tag{Q125.10}
$$

这一步使用Inj所支付的一值面单点性，没有假设 $s$ 已进入某个三角。

(Q125.7)已给三球和由所列九个方向张成。若

$$
\sum_{i=1}^3\alpha_i p_i+w_1+w_2+w_3=0,
\qquad w_i\in L_i,
$$

作用 $a_i$，由(Q125.7)得 $a_i(w_j)=0$ 对全部 $i,j$ 成立，且 $a_i(p_j)=\delta_{ij}$，故全部 $\alpha_i=0$。再固定 $i$，作用全部 $N_{p_i}$；(Q125.9)消去 $w_j,w_k$，(Q125.10)的分离性迫使 $w_i=0$。所以确为直和，维数为 $3+2+2+2=9$。

最后，若 $\eta_\triangle$ 在原相对边界，取包含它的一个真支撑面。面性质使其包含三个 $p_i$。该面非点，原面分类使其为某完整球 $F$。它与 $D_1$ 同含不同的 $p_2,p_3$，只能 $F=D_1$；但它又含 $p_1\notin D_1$，矛盾。因此 $\eta_\triangle\in\operatorname{ri}K$。严格正单位的径向坐标 $(t,x)\mapsto tx$ 把 $t>0$ 与 $K$ 的相对内部化为 $C$ 的内部，故也有锥内点结论。证毕。

在这个证明中，$a_1+a_2+a_3=u$ 只已在 $U_\triangle$ 上成立：双方在三个顶点与三个横向平面上的值相同。未假设顶点属于 $P_0$ 时，这个球上张成论证不把该等式推广至全部 $V$。即使重心是全锥内点，也不能将一个经过它的九维线性截面认作整个 $V$；同样不能把在该截面上为零的有符号泛函认作全域为零。

### 125.4 唯一确认种子的九维原效应空间

**定理 125.4（单种子的双侧非退化配对）。** 另设真实三角的一个顶点属于 $P_0$。则三个顶点均属于 $P_0$；写 $e_i=e_{p_i}$，有

$$
e_1+e_2+e_3=u\quad\text{于整个 }V.
\tag{Q125.11}
$$

定义

$$
S_i=S_{p_i},\qquad
\mathcal S_\triangle=S_1+S_2+S_3,\qquad
\mathcal Q_i=\{f\in S_i:f(p_j)=f(p_k)=0\}.
\tag{Q125.12}
$$

则 $\dim S_i=4$、$\dim\mathcal Q_i=2$，且

$$
\begin{gathered}
S_i=\operatorname{span}\{e_j,e_k\}\oplus\mathcal Q_i,\\
\mathcal S_\triangle=
\operatorname{span}\{e_1,e_2,e_3\}
\oplus\mathcal Q_1\oplus\mathcal Q_2\oplus\mathcal Q_3,
\qquad\dim\mathcal S_\triangle=9,\\
\operatorname{res}_{U_\triangle}:\mathcal S_\triangle
\overset\sim\longrightarrow U_\triangle^*.
\end{gathered}
\tag{Q125.13}
$$

证明。IX120.12使一个 $P_0$ 标签的全部真实邻点仍在 $P_0$，故三个顶点均属 $P_0$。在每颗球上，另外两顶点由确认效应读一、零，确为对径；沿IX120.14的实际对径行走恰形成三周期。于是IX120.18—120.19给(Q125.11)，这是全 $V$ 上的恒等式，不是仅在九维空间上相加。

IX120.8给每个限制 $S_i\to\operatorname{Aff}(D_i)$ 为线性同构，维数四。$e_j,e_k\in N_{p_i}$，其在 $p_j,p_k$ 的读数是两条坐标向量，故两个端点评价独立，$\mathcal Q_i$ 维数二，且给第一行直和。

一个在球 $D_i$ 上于对径两端为零的仿射函数，常数项及直径方向系数均为零；其余正是 $L_i$ 上的任意线性函数。因此限制

$$
\mathcal Q_i\longrightarrow L_i^*
\tag{Q125.14}
$$

是同构。$S_i$ 全在 $p_i$ 为零，故 $\mathcal Q_i$ 在全部三个顶点为零。(Q125.9)对正泛函成立，因而对其线性张成 $S_i$ 也成立，所以 $\mathcal Q_i$ 消去 $L_j,L_k$。

于是(Q125.13)的效应块与(Q125.8)的态向量块逐块配对：三个 $e_i$ 分离三个顶点并消去全部横向平面；$\mathcal Q_i$ 只读自己的 $L_i$，且给其全部线性读数。这证明所列效应和为直和，并且限制到 $U_\triangle$ 的矩阵逐块可逆，得到九维及同构。证毕。

这里使用 $S_i$ 的线性同构，尚未使用或证明 $N_{p_i}$ 对整个球正仿射锥满射。后者是正性问题，不能由四维数相同或限制线性可逆代付。

### 125.5 规范剩余、联合零测试与旧TFD关系

**定理 125.5（准确盲核及同一原态上的反事实）。** 在定理125.4的前件下，令

$$
R_\triangle=\mathcal S_\triangle^\perp
=\{z\in V:f(z)=0\ (f\in\mathcal S_\triangle)\}.
\tag{Q125.15}
$$

则有规范线性分解与投影

$$
\begin{gathered}
V=U_\triangle\oplus R_\triangle,\qquad
\dim R_\triangle=\dim V-9,\qquad R_\triangle\subseteq\ker u,\\
\pi_\triangle:V\to U_\triangle,\qquad
f(\pi_\triangle x)=f(x)\quad(f\in\mathcal S_\triangle),\qquad
u\pi_\triangle=u.
\end{gathered}
\tag{Q125.16}
$$

对这个固定三角，定义原联合关系

$$
\begin{split}
\mathsf J_\triangle:\quad
\forall x,y\in K:\quad
\bigl[\forall i\in\{1,2,3\}\ \forall b\in\mathcal E,
\ b(p_i)=0\Rightarrow b(x)=b(y)\bigr]
\Rightarrow x=y.
\end{split}
\tag{Q125.17}
$$

有准确等价

$$
\boxed{\quad
\mathsf J_\triangle
\Longleftrightarrow R_\triangle=0
\Longleftrightarrow U_\triangle=V
\Longleftrightarrow\mathcal S_\triangle=V^*
\Longleftrightarrow\dim V=9.
\quad}
\tag{Q125.18}
$$

证明。定理125.4使 $U_\triangle$ 与 $\mathcal S_\triangle$ 非退化配对。故对每个 $x\in V$，存在唯一 $y\in U_\triangle$，使 $f(y)=f(x)$ 对全部 $f\in\mathcal S_\triangle$ 成立。于是 $x-y\in R_\triangle$，交为零，得到规范直和、投影及维数公式。由(Q125.11)，$u\in\mathcal S_\triangle$，故剩余在 $\ker u$ 内，投影保留 $u$。

任一非零 $h\in N_{p_i}$ 都有 $m=\max_Kh>0$，且 $h/m\in\mathcal B(p_i)$；反向 $\mathcal B(p_i)\subset N_{p_i}$。因此这些全部原零效应张成的空间恰为 $\mathcal S_\triangle$。若 $R_\triangle=0$，两态的全部这些读数相同就使其差为零，得到 $\mathsf J_\triangle$。

反之，若 $0\ne z\in R_\triangle$，用定理125.3的原内点，取充分小的 $\epsilon>0$，使

$$
x_+=\eta_\triangle+\epsilon z\in K,\qquad
x_-=\eta_\triangle-\epsilon z\in K.
\tag{Q125.19}
$$

两者不同，且因 $u(z)=0$ 都仍归一；三个 $\mathcal B(p_i)$ 的全部效应对它们同读，故否定 $\mathsf J_\triangle$。它们仍可被整个原效应区间分离：取 $\ell\in V^*$、$\ell(z)\ne0$，令 $M=\max_K|\ell|>0$，则 $u/2+t\ell\in\mathcal E$ 对 $0<t\le1/(2M)$ 成立，在两态上读数不同。这里的盲向量不是正态，真正反事实是(Q125.19)中的两张原混态。其余等价由直和和双方维数立即得到。证毕。

**关系对应。** $\mathsf J_\triangle$ 逐字就是VIII111.1中 $\mathrm{TFD}_{3,\exists}$ 的固定框架分离子句：取否定形式，即对任意不同 $x,y\in K$，某个在一个顶点读零的原效应能区分它们。在本章 $P_0$ 种子域，对这种三角取存在量词，所得关系是同一存在式TFD关系在该域的使用，不是新命名的一条独立公设。本章未证明一般EB3+Inj域中，一个满足存在式TFD的三角必含 $P_0$ 顶点；(Q125.18)不删去其种子前件。

在旧W域中，$S_i=\operatorname{im}\Pi_{p_i}^*$，所以本章 $R_\triangle$ 正是VIII109.2的 $Z_F$，$U_\triangle$ 正是VIII111.2的 $V_F$，$\pi_\triangle$ 正是其 $\pi_F$：它们有相同像、相同核。旧的无盲核到全部原纯互易及Jordan重构还使用W已经供应的全纯least、正球读回和每个纯点的框架完成；不能只凭同一个分离公式把这些强前置一并搬入本章。

### 125.6 原线性球读回的乘法式与正性的准确费用

**定理 125.6（单种子上的线性七块代数与正性判据）。** 仍在定理125.4的前件下，由 $S_i\to\operatorname{Aff}(D_i)$ 的同构定义唯一线性映射 $T_i:V\to M_i$：

$$
f(T_i x)=f(x)\qquad(f\in S_i).
\tag{Q125.20}
$$

并置 $\mathsf R_i(x)=e_i(x)p_i$。则

$$
\begin{gathered}
T_i^2=T_i,\quad\operatorname{im}T_i=M_i,\quad T_i p_i=0,
\quad uT_i=u-e_i,\\
i\ne j, \{i,j,k\}=\{1,2,3\}:\qquad T_iT_j=T_jT_i=\mathsf R_k,\\
E_i=T_i-\mathsf R_j-\mathsf R_k,\quad
\operatorname{im}E_i=L_i,\qquad
\pi_\triangle=T_1+T_2+T_3-\mathsf R_1-\mathsf R_2-\mathsf R_3.
\end{gathered}
\tag{Q125.21}
$$

三个 $\mathsf R_i$、三个 $E_i$ 及 $I-\pi_\triangle$ 是两两乘积为零、和为 $I$ 的代数投影；最后一个像为 $R_\triangle$。此处只断言线性投影。

更准确地，在任一球图 $D_i=c_i+B_i\mathbb B^3$ 中，令 $g_i^0=u-e_i$，以IX120.10的同构定义 $H^{(i)}$，使 $H^{(i)}(c_i+B_iw)=w$。则

$$
T_i x=g_i^0(x)c_i+B_iH^{(i)}(x).
\tag{Q125.22}
$$

以下四项等价：$T_i(C)\subset C$；$N_{p_i}|_{D_i}=\operatorname{Aff}(D_i)_+$；$\rho_{p_i}(v)=1$ 对全部 $v\in S^2$ 成立；每条原边 $(p_i,s)$、$s\in P\cap D_i$ 都能由某个原纯点完成真实三角。

证明。限制同构与 $D_i$ 对 $M_i$ 的线性张成，使 $S_i$ 和 $M_i$ 非退化配对，故(Q125.20)唯一存在。它在 $M_i$ 上恒等，而 $S_i$ 全在 $p_i$ 为零，故前两项及 $T_ip_i=0$ 成立。$e_j,e_k\in S_i$，而 $e_i|_{M_i}=0$，(Q125.11)便给 $uT_i=e_j+e_k=u-e_i$。

将(Q125.9)线性延至 $S_i$。对 $f\in S_i$、$i\ne j$，有

$$
f(T_iT_jx)=f(T_jx)=f(p_k)e_k(T_jx)=f(p_k)e_k(x).
$$

两端待比较向量都在 $M_i$，非退化配对给 $T_iT_jx=e_k(x)p_k$；交换 $i,j$ 同理。又有 $T_i\mathsf R_i=\mathsf R_iT_i=0$，而 $i\ne j$ 时 $T_i\mathsf R_j=\mathsf R_jT_i=\mathsf R_j$。连同 $\mathsf R_i\mathsf R_j=\delta_{ij}\mathsf R_i$，逐项展开给 $E_i^2=E_i$、$E_iE_j=0$（$i\ne j$），以及 $E_i\mathsf R_j=\mathsf R_jE_i=0$ 对全部 $i,j$ 成立。$E_i$ 的像在 $M_i$ 中，且 $e_jE_i=e_kE_i=0$，故由(Q125.7)包含于 $L_i$；它又固定 $L_i$，所以像恰为 $L_i$。所列六块之和在 $U_\triangle$ 上恒等；$T_i$ 和 $\mathsf R_i$ 都消去 $R_\triangle$，故六块之和等于规范 $\pi_\triangle$。其补 $I-\pi_\triangle$ 因而也是投影，像为 $R_\triangle$，与前六块双向乘积均为零。

$g_i^0,H^{(i)}$ 张成 $S_i$；在 $M_i$ 上它们读出质量和三个球坐标，因而给(Q125.22)。由于 $e_i$ 的零面是 $D_i$，

$$
C\cap M_i=\operatorname{cone}D_i.
\tag{Q125.23}
$$

所以 $T_i$ 为正恰当且仅当 $\|H^{(i)}(x)\|\le g_i^0(x)$ 对全部 $x\in C$ 成立。这又等价于每个球内非负仿射函数 $\alpha+v\cdot w$ 的唯一线性延拓 $\alpha g_i^0+v\cdot H^{(i)}$ 在原锥上非负，即第二项。IX120.11给原正法向准确由 $\alpha\ge\rho_{p_i}(v)$ 刻画，而全部球内非负函数由 $\alpha\ge\|v\|$ 刻画；配合正齐次性和 $\rho_{p_i}\ge\|\cdot\|$，即得第三项。

最后，对 $s=c_i+B_iv$，IX120.13给 $\rho_{p_i}(v)=1$ 恰等价于 $s$ 与该球内对径 $c_i-B_iv$ 原正交。若边 $(p_i,s)$ 由某个 $t$ 完成，则 $s,t\in D_i$，完整确认 $e_s$ 在它们取一、零，球内极值迫使 $t=c_i-B_iv$。因此“某个完成”已经等价于这一指定对径完成，得到第四项。证毕。

这给出正性费用的明确位置：一个原正泛函限制到实际球当然非负，线性逆映射是否把所有球内非负函数送回原正锥，仍须证明。代数乘法、秩、保单位等式均未代付这个序条件。$\pi_\triangle$ 保单位，但其正性也未由上述线性分解取得；若另有 $\mathsf J_\triangle$，它只是变为恒等映射，仍不由此得到各 $T_i$ 的正性。

作为124.6的条件应用，若某个种子顶点 $p_i$ 还属于 $P_{\rm reg}$，且其完整费用边界连续，124.4使高度为常数，已有 $p_i\in\mathcal T$ 又使124.6中的常数为一，故全部 $\rho_{p_i}=1$，上述 $T_i$ 为正，邻边全部完成。这里额外费用连续性仍是实质前件；单个种子不自动提供它，也不使所有到达标签成为正规点。

### 125.7 跨球乘法与种子重心的准确读数偏差

**定理 125.7（同一原效应的跨球读数与边完成判据）。** 固定 $P_0$ 种子三角 $(p,q,r)$。对任意 $s\in P\cap D_p$、$t\in P\cap D_q$，均有

$$
e_s(t)=e_s(r)e_r(t),\qquad
e_t(s)=e_t(r)e_r(s).
\tag{Q125.24}
$$

取 $D_p=c+B\mathbb B^3$，写 $q=c+Bv_0$、$r=c-Bv_0$、$\|v_0\|=1$，令

$$
g=u-e_p,\quad H(c+Bw)=w,\quad s=q_v=c+Bv,\quad
R=\rho_p(v),\quad \tau=v\cdot v_0,\quad
\delta_p(s)=\frac{R-1}{R+1}.
\tag{Q125.25}
$$

则 $0\le\delta_p(s)<1$，有

$$
\begin{aligned}
e_s(q)&=\frac{R+\tau}{1+R},& e_q(s)&=\frac{1+\tau}{2},\\
e_s(r)&=\frac{R-\tau}{1+R},& e_r(s)&=\frac{1-\tau}{2},\\
e_s(q)-e_q(s)&=\frac{1-\tau}{2}\delta_p(s),&
e_s(r)-e_r(s)&=\frac{1+\tau}{2}\delta_p(s),
\end{aligned}
\tag{Q125.26}
$$

以及

$$
\boxed{\quad
\delta_p(s)=e_s(q)+e_s(r)-1
=3e_s(\eta_\triangle)-1
=\min_{x\in D_p}e_s(x)\ge0.
\quad}
\tag{Q125.27}
$$

下列条件等价：$\delta_p(s)=0$；$e_s(q_{-v})=0$；$(p,s,q_{-v})$ 是真实三角；原边 $(p,s)$ 可由某个原纯点完成；$e_s(\eta_\triangle)=1/3$。当 $s\ne q$ 时，还等价于 $e_s(q)=e_q(s)$。

证明。全部到达点属 $P_0$ 已由IX120.12支付。$e_s(p)=0$，而 $p,r$ 是球 $D_q$ 内的对径。(Q125.9)给 $e_s|_{D_q}=e_s(r)e_r|_{D_q}$；在 $t$ 评价即得(Q125.24)第一式。反向把 $e_t$ 限制到 $D_p$ 同理。两个式子保留各自系数，未把它们当作互易性。

种子使 $q\perp r$，IX120.13在 $v_0,-v_0$ 给 $\rho_p(v_0)=\rho_p(-v_0)=1$。IX120.12因而在整个 $V$ 上给

$$
e_q=(g+v_0\cdot H)/2,\quad
e_r=(g-v_0\cdot H)/2,\quad
e_s=(Rg+v\cdot H)/(1+R).
\tag{Q125.28}
$$

在 $q,r,s$ 评价，得到(Q125.26)的前两行；相减并用 $\delta_p(s)=(R-1)/(R+1)$ 即得后两式。$R\ge1$ 且有限，给偏差范围。

两个种子端点读数之和是 $2R/(1+R)$；$e_s(p)=0$，故其减一也等于 $3e_s(\eta_\triangle)-1$。在整个 $D_p$ 上，$e_s(c+Bw)=(R+v\cdot w)/(1+R)$，最小值在唯一对径 $q_{-v}$ 达到，为 $(R-1)/(R+1)$，得到(Q125.27)。

偏差为零恰使这一原效应在 $q_{-v}$ 为零，给 $s\perp q_{-v}$；两者都已与 $p$ 原正交，故为真实三角。反向若任意 $t$ 完成边 $(p,s)$，它也在 $D_p$，$e_s$ 在球上于 $s,t$ 取一、零，迫使 $t=q_{-v}$，故偏差为零。重心条件由(Q125.27)等价。当 $s\ne q$ 时，$\tau<1$，(Q125.26)的严格正系数使最后的互易式也等价。证毕。

IX120.13已经有 $\rho_p(v)=1$ 的局部对径判据；本定理增加的是它与同一实际种子重心、两端原读数及跨球乘法的准确联系。已有的是 $e_s(\eta_\triangle)\ge1/3$ 和两端比较的单向不等式；未证的是它们在全部方向取等。$\delta_p(s)>0$ 精确否定边 $(p,s)$ 的完成，并不否定 $s$ 通过另一组原三角属于 $\mathcal T$。

### 125.8 线性拼全、邻边完成与整个原域覆盖

**命题 125.8（局部校准和全域到达的不同量词）。** 从一个 $P_0$ 种子三角定义

$$
G_0=\{p,q,r\},\qquad
G_{n+1}=G_n\cup\bigcup_{a\in G_n}(P\cap D_a),\qquad
G=\bigcup_{n\ge0}G_n.
\tag{Q125.29}
$$

则 $G\subset P_0$。若另有以下两项条件，才可沿这条路线推出 $\mathcal T=P$：

$$
\begin{split}
&\forall a\in G\cap\mathcal T\quad
\exists b,c\in P:\ (a,b,c)\text{ 是真实三角},\\
&\hspace{23mm}\forall s\in P\cap D_a:\ e_s(b)=e_b(s);\\
&\overline G^{\,P}=P.
\end{split}
\tag{Q125.30}
$$

证明。IX120.12沿每条真实边传播 $P_0$，归纳给 $G\subset P_0$；故(Q125.30)中的完整确认效应均已定义。种子使 $G_0\subset\mathcal T$。若 $G_n\subset\mathcal T$，对每个 $a\in G_n$ 取(Q125.30)的实际三角。定理125.7在 $s\ne b$ 时把互易式变成边 $(a,s)$ 的完成；$s=b$ 时原三角自身给完成。于是所有新增邻标签属于 $\mathcal T$，归纳得 $G\subset\mathcal T$。IX120.4已给 $\mathcal T$ 在 $P$ 中相对闭，再以第二条件取闭包，得到 $\mathcal T=P$。证毕。

(Q125.30)只是对这条路线的充分联合条件，不另计为减少公理的重构。一个标签可沿图到达，不表示该条到达边已完成；一个标签在某个三角中，也不表示其全部出边完成。$G$ 的稠密性还未由种子证明，$P$ 的连通性、原边投影开放性或球面在整个 $P$ 中为邻域均未预付。

本章留下三个不同的缺项。第一，EB3+Inj与一个 $P_0$ 种子是否强迫 $\mathsf J_\triangle$，即三族原零效应分离全部原态；本章只给其准确九维等价式。第二，即使另有 $\mathsf J_\triangle$，还没有证明各 $T_i$ 为正、$\delta_{p_i}$ 全方向为零、全部原标签满足接触，或原全域的least与互易。旧VIII111.4把任意纯点补成框架再作总预算取等；本章不能对任意纯点使用这个尚未支付的步骤。第三，即使局部邻边完成，仍需把所得部分接回整个原 $P$ 的覆盖，或找到直接给全域接触的其他论证。

对九维加种子的这些剩余蕴含，本章既未完成证明，也未给出满足全部EB3的反模型。一般九维线性配对本身不携带原序锥；单张凸影壳的光滑、严格凸、闭性或常值高度也不替代全标签的单位接触。124.4—124.6的常值费用分支若没有种子接触，仍须排除 $M_p<1$；若有正规种子且费用连续，则125.6的条件应用只解决该锚点的邻边，尚未自动给(Q125.30)的全域量词。

### 125.9 完整原域的条件静态候选与反向量词

**条件应用 125.9（沿既有桥保留的完整候选）。** 定义

$$
\begin{gathered}
\mathcal T_{\rm mid}=
\{b\in P:\exists x\in D_b, (b+x)/2\in\partial_{\rm rel}K\},\\
\mathsf{DC}:\ \overline{\mathcal T_{\rm mid}}^{\,P}=P,
\qquad \mathsf{MC}:\ \mathcal T_{\rm mid}=P,\\
W(D_b)=\max_{f\in\mathcal E}\bigl(\max_{D_b}f-\min_{D_b}f\bigr).
\end{gathered}
\tag{Q125.31}
$$

它们从整个原域定义，允许接触端起初为混态。对 $p\in P_{\rm reg}$，沿123定义 $g_p,H_p,q_w$，并令 $a_w$ 为 $p$ 在完整 $D_{q_w}$ 内的对径端。完整有限相容性为

$$
\mathsf F(p):\quad
\forall k\ge1\ \forall w_1,\ldots,w_k\in S^2\quad
\exists v\in S^2\ \forall i\le k:\quad
v\cdot H_p(a_{w_i})\le g_p(a_{w_i}).
\tag{Q125.32}
$$

准确保留124.6的同一模型类：

$$
\begin{array}{c}
\mathrm{EB3}+\mathrm{Inj}+
\overline{\{p\in P_{\rm reg}:\mathsf F(p)\}}^{\,P}=P\\
\Updownarrow\\
\mathrm{EB3}+\mathsf{DC}
\Longleftrightarrow\mathrm{EB3}+\mathsf{MC}
\Longleftrightarrow\mathrm{EB3}+\forall b\in P: W(D_b)=1\\
\Updownarrow\\
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V
\text{ 实线性},\qquad \Phi(\mathrm{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\end{array}
\tag{Q125.33}
$$

证明与反向全模型计算。121.2使中点接触逐标签等价于满宽，且接触端必纯；IX120.4使满宽标签集相对闭；122.2、123.10及123.15给稠密接触与正规F稠密的对应。取得全部原标签满宽后，才消费IX116.17及VIII113的完整条件重构。这里不把存在一个种子、$\dim V=9$ 或 $\mathsf J_\triangle$ 替换入等价链。

反向取整个矩阵实现 $V=\operatorname{Herm}_3(\mathbb C)$、$C=\mathrm{PSD}_3$、$u=\operatorname{Tr}$。对每个非零 $z$，$p=zz^*/(z^*z)$ 是原纯点，全部确认矩阵恰为 $p\oplus A$、$0\preceq A\preceq I_{z^\perp}$。对每个迹一正矩阵 $\rho$，

$$
T_p(\rho)=\operatorname{Tr}(p\rho),\qquad
D_p=\{\rho\succeq0:\operatorname{Tr}\rho=1,\ \rho z=0\}.
\tag{Q125.34}
$$

这是整个 $z^\perp\cong\mathbb C^2$ 上的全部密度矩阵，Pauli坐标给完整三球；不同纯标签给不同正交补，故Inj成立。每条原球直径由一对正交秩一投影给满幅效应，所以每个标签满宽，且每条边都完成三角。每个 $x\in P\cap D_p$ 使 $(p+x)/2$ 秩二，确在原相对边界，故MC成立。

每个 $\mathcal A_p$ 单点。对任意纯序列 $p_n\to p$ 和任意 $0\preceq A\preceq I$、$\operatorname{Tr}(Ap)=0$，正性给 $Ap=0$；令 $Q_n=I-p_n$，$Q_nAQ_n$ 是零于 $p_n$ 的原效应，且

$$
\|Q_nAQ_n-A\|_{\rm op}\le2\|p_n-p\|_{\rm op}\to0.
\tag{Q125.35}
$$

此估计统一量化全部 $A$；另一Hausdorff包含由紧性与评价给出。因此 $P=P_{\rm reg}$。原球图中 $g=\operatorname{Tr}((I-p)\,\cdot)$，$H/g$ 属于单位球，且 $a_w=q_{-w}$、$g(a_w)=1$。于是任意有限批都满足(Q125.32)，因为单位 $v$ 对单位球点均有 $v\cdot H(a_w)\le1$。所有公式经同一个 $\Phi$ 运输，完成全部原纯、混态、效应及单位的反向量词。证毕。

### 125.10 全部静态QM对象的同一对应

以下仅在(Q125.33)的完整条件成立后，复用124.8及既有静态字典。125.3—125.7单独不供应此表。

| 静态数学对象 | 同一原实现的全部量词 |
| --- | --- |
| 复射线与纯态 | 全部 $z\ne0$ 给 $p_z=\Phi(zz^*/(z^*z))$，恰为整个 $P\cong\mathbb{CP}^2$ |
| 混态、概率混合与质量 | 整个 $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$，$C=\Phi(\mathrm{PSD}_3)$ 含零与全部非负质量，保持全部有限凸组合，$\dim_{\mathbb R}V=9$ |
| 单位、全部效应和Born评价 | $u\Phi=\operatorname{Tr}$；整个 $\mathcal E$ 恰为 $f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$、$0\preceq A\preceq I_3$，含全部混态输入及零、单位、补 |
| least确认与完整排除球 | $T_{p_z}(\Phi\rho)=\operatorname{Tr}(zz^*\rho)/(z^*z)$；least效应为相应秩一投影，完整 $D_{p_z}$ 为 $z^\perp$ 上全部密度矩阵 |
| 纯比较与原二元边 | $T_{p_z}(p_w)=|z^*w|^2/((z^*z)(w^*w))$，零恰为复内积正交 |
| 正交完备基和数学三结果 | 每条原边有唯一第三纯点，三秩一投影之和为 $I_3$，三原非负效应之和为 $u$，读数为Kronecker值，容量为三 |
| 全部有限数学POVM | 对每个有限结果数，全部原 $f_j\ge0,\sum_jf_j=u$ 恰对应全部 $A_j\succeq0,\sum_jA_j=I_3$ |
| 谱和全部实可观测量 | 每个混态有三项正交谱分解，允许零权与重复谱；全部实线性可观测量对应全部Hermitian矩阵并有实谱分解 |
| 派生共同几何 | 中心为 $\Phi(I_3/3)$，共同内积为 $B(\Phi X,\Phi Y)=\operatorname{Tr}(XY)$，Jordan积为 $\Phi((XY+YX)/2)$ |

复射线中的叠加是该数学模型的一部分；实际相干准备、相位参考和可调用门仍按各自原来源与操作合同供应。数学POVM和三个种子效应均不自动成为实际共同仪器。

### 125.11 原来源、所有有限复合与实际动态合同

**共同来源与全部原操作。** 124.9及其所引123.13、VIII113.11、VIII112.9、IX120.11、121.12、122.14的同一原装饰元组 $\mathcal O$ 全部保留：共同来源域、全部中点实现、原概率像紧性、全测试表与闭性、零／单位／补／有界倍增、重复标签及每种同中点实现；全部非负质量，零／次归一／不等质量，以及过程和参考各自的完整相关联合输入域。原 $L,p,\omega,K,M$、两次同一读回、两实张成、全实关系、完整(83.8)、VI(89.13)的全部两尺度等式、C2、整个 $G=1_E$、精确PRE之后的整个H13、每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集都由原消费者承担。操作合同的映射 $p$ 与本章纯标签不同型。

设备／事件／来源绑定、全部菜单分支、参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来与每个中间切口，以及VI89.9—89.10的原生／细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后条件未来、source-adoption和资源合同均保留。线性投影 $T_i,\pi_\triangle$、比值读数和图可达集不供应这些实际制备或接线。

**全部有限联合层级。** 对每个有限 $N\ge1$，仍需实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 及整个原效应区间。每个实际分块 $a+b=N$ 保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
\tag{Q125.36}
$$

同一产品配对、严格张量单位、全部原因子置换及逆的正性、规范重括号、指定运输下的不连续位置分块全部保留。二份比较仍是整个联合 $S_2$：对每个产品或纠缠纯点 $p\in P_2$、每个有限原纯准备族 $q_\ell\in P_2$、全部 $t_\ell\ge0$ 且 $\sum_\ell t_\ell=1$，包括零权和重复标签，完整保留VIII111.35：

$$
T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)
=\sum_\ell t_\ell T_{q_\ell}^{(2)}(p),\qquad
T_p^{(2)}(x)=\inf_{\substack{f\in[0,u_2]_{C_2^*}\\ f(p)=1}}f(x).
\tag{Q125.36S}
$$

这不是仅在产品态上的比较。

三项具名供应仍分别是原低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥；唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩和实维乘法的复型选择；同一实际两因子的产品正规形。在同一保迹局部坐标中，非经典支路保留同一最大块 $n_r=L\ge2$ 的 $\mathsf F_{\max}$，要求同一含相位正交基给

$$
g_r=\sum_{a=1}^{L}|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L.
\tag{Q125.37}
$$

其余三份扇区零，归一原源为 $\Delta_r/L$，不预付三份纯性或实际制备；全经典 $L=1$ 支路不要求该资源。仅在全部联合前件与三项供应齐备后使用既有全有限层级定理。单体三球不制造 $S_2$、纠缠来源、叉口资源或高阶张量锥；复三能级的二、三份秩为九、二十七，高阶载体不再要求单体EB3或秩三W。

**全旁观CP、事件和同族仪器。** 数学全旁观正性仍量化每个 $b\ge0$ 及任意含纠缠的同一共同输入，要求

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{Q125.38}
$$

只有全层级已给，通常CP、矩形跨扇区Kraus及逐输入TP/TNI预算才沿既有Choi桥取得。同一事件的CP另需原完整提升、实际探针及相容核；全部数学CP-TNI分支成为实际事件，还需事件饱和选择。同族仪器另需共同输入预算、接线、记录、粗粒化和校准。只对正质量分支作条件归一，零质量分支不强定归一条件态。Lüders更新另需同一分支的锐效应、接受态中性和输出校准。三条真实边、数学效应和为 $u$、全部数学POVM与实际同族仪器继续分开。

**时间、Hamiltonian和 $\hbar$。** 原钟、实际动态来源、连续齐次可逆时间群、单位及 $\hbar$ 各保留自己的合同。若另给同一载体全实时间连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，有限维生成元只描述这个额外供应。已重构复块中，给定保迹酉时间族的通常表达为

$$
U_t=\exp(-itH/\hbar),\qquad
\rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\frac{i}{\hbar}[H,\rho],\qquad H=H^*.
\tag{Q125.39}
$$

全部输入和全部时间的量词保留。球面参数、实际对径行走和证明中的弧均不是物理钟。$H$ 的标量平移不改变态作用，时间重标改变生成元尺度而保留静态模型。恒等时间族和非平凡Hamiltonian族可共享全部静态数据，故实际 $H$、数值 $\hbar$、能量标定、时空与物理空间维数不由本章取得。

### 125.12 复用边界与成熟文献的已付前件

本章的原域综合按repo-derived归属：125.3用实际球唯一支撑与全部原正法向，证明单个真实三角的准确九维张成；125.4—125.6将IX120.8的限制同构接到这个配置，取得效应配对、规范剩余、同一TFD关系及未预设正性的乘法代数；125.7将IX120.12—120.13接到同一实际种子的重心及跨球读数。球支撑的极值计算、有限维非退化配对、消去子和代数投影是成熟中间工具。三角重心内点性在旧W域已有VIII110.5，本章只在所需弱域给同一原面论证；不另作独立新原理。125.8是量词分工的条件应用，125.9—125.11完整复用既有静态及物理接口，不计为新分类。

[Ududec—Barnum—Emerson][Q125UBE] Proposition 1及Appendix已有三缝包含—排除恒等式与二面线性张成的等价。其standing condition要求每个暴露面有唯一的中性互补滤子及唯一补滤子；命题还使用三个两两正交滤子及其生成的多缝滤子。本章125.6只在一个种子上证明线性乘法，未取得其全域滤子前件，故不将本章 $I-\pi_\triangle$ 当作已实现的三缝干涉操作，也不凭相同公式消费其操作结论。

[Alfsen—Shultz][Q125AS]印刷页160的Hilbert ball property要求每一对原极点生成的最小面是norm-exposed且仿射同构Hilbert球。印刷页188 Corollary 7.5在有限维紧凸集上要求该性质与每个norm-exposed face均projective；strong spectrality不是此推论另列的第三个条件。印刷页158的P-projection是其order-unit／base-norm对偶中的弱星连续正压缩投影，存在同类quasicomplement，且两投影在原空间及其对偶上都满足正核／正像互补。单种子三球、九维配对或线性保单位投影均未支付这些全域条件。这里仅引用该已知条件接口，不将其重述为新定理。

现有原源码[PositiveComplementaryProjections.whole_positive_projections][Q125Proj]也明确带weakPair前件，即每个原正交纯对生成真最小面；本章未调用它来提前取得 $T_i$ 正性。所有新增结论的前件均保留EB3对全部原纯标签的完整量词，没有以三张所选球、抽象关联图、选择性效应菜单或一般光滑凸壳替换原模型。本章不主张全球原创、逻辑独立性、自动接触或独立公理数减少。

[Q125VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2、104.1及105：完整原面、强入口的原确认与共同延拓。"
[Q125VIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII109.2—109.3、111.2与111.12：全W三窗口、盲核及联合零效应分离；VIII113：既有分类。"
[Q125IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX120.8、120.12、120.18—120.19：P0限制同构、邻标签传播和三周期全空间单位恒等式；IX116.17：既有静态重构。"
[Q125T]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md "121—122：残余稳定、原切扇、中点接触、实际影像和未证全域桥。"
[Q125UBE]: https://arxiv.org/pdf/0909.4787v1 "Cozmin Ududec, Howard Barnum and Joseph Emerson, Three slit experiments and the structure of quantum theory, standing condition, Proposition 1 and Appendix."
[Q125AS]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf "E. M. Alfsen and F. W. Shultz, State spaces of Jordan algebras, Acta Mathematica 140, DOI 10.1007/BF02392307，印刷页158、160、188。"
[Q125Proj]: https://github.com/the-omega-institute/trureturing/blob/b81f2d41bb9f9bac626c602802613f9722a450c6/D5/S3/Quantum/Foundation/PositiveComplementaryProjections.lean "whole_positive_projections的weakPair前件。"

### 125.13 完整白话

把全部原状态想成同一块完整凸实体，所有原测试都是从零到一读数的尺，任何混态、纯标签和测试都不先删去。现在只找到一个三角：三个实际纯点之间，各有真正的零一边，却还没有宣布这三条边来自一台共同仪器。每个顶点背后的完整排除球，都把另外两个顶点当作自己的一条直径；三颗球因此共有三个顶点方向，每颗又带两个横向方向。关键在原正尺：一把在第一个顶点读零的尺，限制到经过该点的另外两颗球时，只能贴着那个端点的唯一支撑面，所以读不见那两球的横向方向；但用第一颗球上每个真实球面端自己的确认尺，又能看见第一颗球自己的任意非零横向箭头。三个顶点加六条横向方向因此确实互不混淆，三张完整球恰好张成九维；三角重心虽已在整块实体内部，这九维截面仍不自动填满整个原空间。如果种子的一个顶点还有唯一完整确认，原边把这种唯一性传给另外两点，已有三周期公式才使三张确认尺在全部原空间相加为同一单位尺。此时三族全部零尺也恰有九个独立方向，与三球的九维空间逐块配对，留下一个准确的共同盲区；盲区非零时，从同一个原内部态向正反两边各挪一小步，就得到两张真实混态，三族全部零尺对它们同读，别的原尺却能区分。要求这三族尺联合看清整个实体，正是旧有三元二面可辨关系在这个较弱入口的原义，不是一条新起名字的公设。配对还给三张规范线性球读回及同样的投影乘法式，但把箭头线性送回球的张成空间，不等于把正态送回实心球；后者恰要求该球上的每一条邻边都能完成真实三角。沿种子球走到一个新纯点，它自己的确认尺在种子重心的读数只能等于或高于三分之一；超出的三倍，恰是这把尺在整颗原球上的最低读数，也恰控制它与两个种子端点的转移读数不对称。最低读数降到零，原边才由指定对径补出第三点；新点从另一组三角进入过，并不替这条边完成。现在还缺的是为何这些偏差全方向为零、为何三族原零尺没有剩余盲区，以及完成的部分如何到达或逼近每个原纯点。正规种子若再有完整费用连续性，已有常值刚性能把这一锚点的全部邻边校准，但仍不能跳过其余标签。完整接触在整个原域稠密后，才沿已有条件重构接回全部复三能级纯态、混态、效应、Born概率、数学POVM和谱结构；共同来源、实际准备与门、全部有限复合及纠缠、叉口资源、全旁观CP、同族事件仪器、Lüders更新、物理钟、Hamiltonian和数值 $\hbar$ 仍须各自的完整原合同。

## 追加锚（本行以下为增补区）
## 126. 原零关系的闭关联、重复球商与单标签积聚

### 126.0 同一原域与本章前件

本章仍取同一个非零有限维实空间 $V$、闭尖生成锥 $C\subset V$ 及在
$C\setminus\{0\}$ 上严格正的 $u\in V^{\ast}$，并保留整个原对象

$$
 K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
 \mathcal E=[0,u]_{C^{\ast}}.
$$

对每个 $p\in P$ 使用

$$
 \mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
 T_p(x)=\min_{f\in\mathcal F_p}f(x),\qquad
 D_p=\{x\in K:T_p(x)=0\},\qquad
 \mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\}.
 \tag{Q126.1}
$$

本章的几何前件是裸 $\mathrm{EB3}$：每个 $D_p$ 都仿射同构于整个闭三球。完全保留
VII103.2 和 IX116.1 的面分类：每个 $D_p$ 是紧暴露极大真面，全部非空真面只有原纯单点和这些完整球；每个完整球的球边纯点生成整球；不同完整球至多交于一个纯点。这里不假设 $P$ 闭，也不假设
$\mathrm{Inj}$、全 Pair、正投影、projectivity 或共同仪器。

令

$$
 A=\operatorname{aff}K=\{u=1\},\qquad
 S=\partial_{\mathrm{rel}}K,\qquad
 \mathfrak B=\{D_p:p\in P\}.
$$

固定方向空间 $\ker u$ 上的任一欧氏范数，在 $A$ 上用其诱导的距离定义直径和 Hausdorff 距离。由 IX116.8，裸 $\mathrm{EB3}$ 已给 $\dim V\ge7$，故
$S$ 是维数 $m=\dim V-2\ge5$ 的紧拓扑流形，且 $S\cong S^m$。对
$F\in\mathfrak B$ 写

$$
 S(F)=P\cap F=\partial_{\mathrm{rel}}F,\qquad
 I(F)=\{p\in P:D_p=F\}.
$$

若 $I(F)$ 非单点，IX116.2 给出唯一的对侧完整球 $\tau F$，满足

$$
 I(F)=S(\tau F),\qquad I(\tau F)=S(F),\qquad F\cap\tau F=\varnothing,
 \tag{Q126.2}
$$

并且 $F,\tau F$ 都不与第三颗完整球相交。称这类 $F$ 为重复球，记重复球族为
$\mathfrak B_{\mathrm r}$。

### 126.1 全部边界态上的原零关系

定义

$$
 \mathcal Z(x)=
 \{y\in K:\exists f\in\mathcal E,\ f(x)=0,\ f(y)=1\},
 \qquad
 \mathscr Z=\{(x,y)\in K^2:y\in\mathcal Z(x)\}.
 \tag{Q126.3}
$$

**引理 126.1（闭关联及完整纤维）。** $\mathscr Z$ 是 $K^2$ 中的紧闭集，对称，且
$\mathscr Z\subseteq S\times S$。对纯点 $p$，

$$
 \mathcal Z(p)=D_p.
 \tag{Q126.4}
$$

若 $H\in\mathfrak B$ 且 $x\in\operatorname{ri}H$，则

$$
 \mathcal Z(x)=
 \begin{cases}
 \{p_H\},&I(H)=\{p_H\},\\
 \tau H,&H\in\mathfrak B_{\mathrm r}.
 \end{cases}
 \tag{Q126.5}
$$

特别地，若 $F$ 重复，则

$$
 x\in F\quad\Longrightarrow\quad \mathcal Z(x)=\tau F.
 \tag{Q126.6}
$$

证明。先说明 $\mathcal E$ 在原空间 $V^{\ast}$ 中紧。因为
$u\ne0$ 且 $A=\{u=1\}$ 线性张成 $V$，限制映射
$V^{\ast}\to\operatorname{Aff}(A)$ 是线性同构；这里
$\operatorname{Aff}(A)$ 是 $A$ 上实值仿射函数组成的向量空间，不把仿射空间 $A$ 本身当作向量空间。
从 $K$ 中取一组仿射基，它也是 $V$ 的线性基。所有
$f\in\mathcal E$ 在这组基上的读数都在 $[0,1]$ 内，故 $\mathcal E$ 在有限维 $V^{\ast}$ 中有界。
又因 $C^{\ast}$ 闭，$\mathcal E=C^{\ast}\cap(u-C^{\ast})$ 闭，因而紧；经上述限制同构，在
$\operatorname{Aff}(A)$ 中亦紧。于是

$$
 \{(x,y,f)\in K^2\times\mathcal E:f(x)=0,\ f(y)=1\}
$$

是紧集，其在 $K^2$ 上的投影就是 $\mathscr Z$，所以 $\mathscr Z$ 紧闭。若 $f$ 见证
$x\mathrel{\mathcal Z}y$，则 $u-f$ 见证 $y\mathrel{\mathcal Z}x$，故对称。非零的非负仿射函数不能在
$\operatorname{ri}K$ 取零；取 $f(x)=0$ 的见证后，$x$ 与 $y$ 都在 $S$。纯点情形正是
$D_p$ 的定义。

设 $x\in\operatorname{ri}H$，且 $f(x)=0,\ f(y)=1$。因为 $f\ge0$ 且 $x$ 是 $H$ 的相对内点，$f|_H=0$。写
$y=\sum_i\lambda_i p_i$ 为有限个原纯点的严格正凸分解。由
$0\le f(p_i)\le1$ 及 $f(y)=1$，每个 $f(p_i)=1$。于是对 $z\in H$，
$T_{p_i}(z)\le f(z)=0$，从而 $H\subseteq D_{p_i}$；极大性给
$D_{p_i}=H$，即 $p_i\in I(H)$。若 $I(H)=\{p_H\}$，便有 $y=p_H$。反过来，取
$e\in\mathcal A_{p_H}$，它在 $H$ 上为零、在 $p_H$ 上为一，所以
$p_H\in\mathcal Z(x)$。若 $H$ 重复，则
$I(H)=S(\tau H)$，故 $y\in\operatorname{conv}I(H)=\tau H$；反向包含由
IX116.3 的公共效应（零于 $H$、一于 $\tau H$）给出。

现在取任意 $x\in F$，其中 $F$ 重复。若 $x\in\operatorname{ri}F$，上面已经得到
$\mathcal Z(x)=\tau F$。若 $x\in\partial_{\mathrm{rel}}F=S(F)$，则 $x$ 是纯点，且
$D_x=\tau F$（由 $I(\tau F)=S(F)$），所以 $\mathcal Z(x)=D_x=\tau F$。证毕。

### 126.2 两次零关系恰好是同处真面

在 $S$ 上定义闭关系

$$
 \mathscr B_S=
 \left\{(x,y)\in S^2:\frac{x+y}{2}\in S\right\}.
 \tag{Q126.7}
$$

**定理 126.2（零关系平方）。**

$$
 (x,y)\in\mathscr B_S
 \Longleftrightarrow
 x,y\text{ 同处一个原真面},
 \qquad
 \mathscr Z\circ\mathscr Z=\mathscr B_S.
 \tag{Q126.8}
$$

特别地，若 $x\in\operatorname{ri}H$，则

$$
 (\mathscr B_S)_x=H,
 \tag{Q126.9}
$$

若 $F$ 重复且 $x\in F$，则

$$
 (\mathscr B_S)_x=F.
 \tag{Q126.10}
$$

证明。中点在 $S$ 当且仅当存在 $K$ 的支撑仿射函数在该中点取极值；仿射性迫使它在
$x,y$ 上都取同一极值。因此二点同处一个真面。反向由真面的凸性显然。由于
$\mathscr B_S$ 是连续中点映射的闭集，$\mathscr B_S$ 紧。

若 $x\mathrel{\mathcal Z}z\mathrel{\mathcal Z}y$，则
$x,y\in\mathcal Z(z)$。引理126.1说明 $\mathcal Z(z)$ 总是一个纯单点或完整球，因而是凸真面，故
$(x,y)\in\mathscr B_S$。反过来，若 $x,y$ 同处一个真面，按 VII103.2 它要么是纯单点，要么包含于某个完整球
$H$。取一个纯点 $p$ 使 $H=D_p$。零对称给
$x\mathrel{\mathcal Z}p\mathrel{\mathcal Z}y$；纯单点的情形也可先把该点放进某个包含它的完整球再作同一选择。于是
$\mathscr Z\circ\mathscr Z=\mathscr B_S$。式(Q126.9)来自球相对内点所在的唯一完整面；式(Q126.10)对重复球由
IX116.2 的第三球孤立性和引理126.1给出。证毕。

### 126.3 重复块的紧层与实际商

对 $\delta>0$ 定义

$$
 R_\delta=
 \bigcup\left\{
 F\in\mathfrak B_{\mathrm r}:
 \operatorname{diam}F\ge\delta,\
 \operatorname{diam}\tau F\ge\delta
 \right\},
 \qquad
 R=\bigcup_{n\ge1}R_{1/n}.
 \tag{Q126.11}
$$

**定理 126.3（正尺度重复层是紧的）。** 每个 $R_\delta$ 是 $S$ 中的紧集，因而
$R$ 是 $F_\sigma$ 集。

证明。取 $x_n\in R_\delta$、$x_n\to x$，并选择重复对
$F_n,\ G_n=\tau F_n$ 使 $x_n\in F_n$。取
$a_n,b_n\in F_n$、$c_n,d_n\in G_n$ 满足

$$
 \|a_n-b_n\|\ge\delta,\qquad \|c_n-d_n\|\ge\delta.
$$

由 $K$ 紧性取子列，使 $x_n,a_n,b_n,c_n,d_n$ 分别收敛于
$x,a,b,c,d$。于是 $a\ne b,\ c\ne d$。令
$v_n=(a_n+b_n)/2\to v=(a+b)/2$。关系
$(v_n,x_n),(a_n,b_n)\in\mathscr B_S$ 的闭性给出
$(v,x),(a,b)\in\mathscr B_S$。因 $a\ne b$，$v$ 是唯一完整球 $H$ 的相对内点；由
(Q126.9)，$x,a,b\in H$，故 $\operatorname{diam}H\ge\delta$。

另一方面 $c_n,d_n\in\mathcal Z(v_n)$，而 $\mathscr Z$ 闭，故
$c,d\in\mathcal Z(v)$。因 $c\ne d$，式(Q126.5)排除 $H$ 为单标签球，于是
$H$ 重复且 $c,d\in\tau H$，故 $\operatorname{diam}\tau H\ge\delta$。因此
$x\in R_\delta$。有限维紧空间中的序列闭性给出 $R_\delta$ 紧。重复球是正维球，故每个重复
$F$ 与某个 $R_{1/n}$ 相交于它本身，得到(Q126.11)第二式。证毕。

在 $R$ 上定义

$$
 x\sim_R y
 \Longleftrightarrow
 x,y\text{ 属于同一颗重复球}.
 \tag{Q126.12}
$$

**定理 126.4（重复部分的 Hausdorff 商）。** 关系 $\sim_R$ 是 $R^2$ 中的闭等价关系；商映射

$$
 q_R:R\longrightarrow Y_R=R/{\sim_R}
 \tag{Q126.13}
$$

是闭映射，纤维是紧三球，且 $Y_R$ 是 Hausdorff 空间。对任意由完整重复球组成的并
$X\subset R$，限制 $q_R|_X:X\to q_R(X)$ 对子空间拓扑仍是闭商映射，且纤维不变。
这里既不要求 $R$ 在 $S$ 中闭，也不要求 $X$ 闭或紧。

证明。若 $x_n\sim_R y_n$、$x_n\to x\in R$、$y_n\to y\in R$，则
$(x_n,y_n)\in\mathscr B_S$，故 $(x,y)\in\mathscr B_S$。由(Q126.10)，$y$ 与 $x$ 属于同一重复球，所以
$x\sim_Ry$。这证明关系闭。对 $B\subset R$ 相对闭，取其饱和集
$\operatorname{Sat}(B)$。若 $z_n\in\operatorname{Sat}(B)$ 收敛于 $z\in R$，在同一重复球中取
$b_n\in B$。由 $K$ 紧性先取子列 $b_n\to b\in K$。因
$(z_n,b_n)\in\mathscr B_S$，紧共面关系 $\mathscr B_S$ 的闭性给
$(z,b)\in\mathscr B_S$。设 $F$ 为包含 $z$ 的重复球；式(Q126.10)先给
$b\in F\subset R$。现在才能使用 $B$ 在 $R$ 中的相对闭性，得到
$b\in B$，从而 $z\in\operatorname{Sat}(B)$。所以饱和集在 $R$ 中闭，
而 $q_R^{-1}(q_R(B))=\operatorname{Sat}(B)$，由商拓扑定义得 $q_R$ 闭。

每条纤维正是一个紧重复三球。为证明商的 Hausdorff 性，取不同商点
$\eta,\zeta\in Y_R$，其纤维 $F_\eta,F_\zeta$ 是 $R$ 中不交的紧闭集。
$R$ 是度量空间，因而正规，故可取不交开集 $U_\eta,U_\zeta\subset R$，分别包含这两个纤维。
闭映射性质说明

$$
 O_\eta=Y_R\setminus q_R(R\setminus U_\eta),\qquad
 O_\zeta=Y_R\setminus q_R(R\setminus U_\zeta)
$$

是分别含 $\eta,\zeta$ 的开集，且 $q_R^{-1}(O_\eta)\subset U_\eta$、
$q_R^{-1}(O_\zeta)\subset U_\zeta$。由满射性二者不交，证明 $Y_R$ Hausdorff。

最后，设 $X$ 是完整纤维的并，$B\subset X$ 相对闭。取 $R$ 中闭集 $D$ 使
$B=D\cap X$。饱和性给

$$
 q_R(B)=q_R(D)\cap q_R(X).
$$

右侧在 $q_R(X)$ 中相对闭，所以限制是连续、闭的满射，因而为闭商映射。
其目标是 Hausdorff 空间 $Y_R$ 的子空间，纤维仍是原来的完整紧球。证毕。

把同一压缩关系尝试延伸到整个边界：

$$
 Q=\Delta_S\ \cup\!
 \bigcup_{F\in\mathfrak B_{\mathrm r}}F\times F.
 \tag{Q126.14}
$$

不能由现有前件断言 $Q$ 闭。其失闭形式却被完全约束。

**命题 126.5（全局商失闭的唯一通道）。** 若

$$
 x_n,y_n\in F_n,\quad F_n\in\mathfrak B_{\mathrm r},\quad
 x_n\to x,\ y_n\to y,\quad x\ne y,\ (x,y)\notin Q,
 \tag{Q126.15}
$$

则存在单标签完整球 $H$ 及其唯一标签 $p_H$，使

$$
 x,y\in H,\qquad
 \sup_{z\in F_n}d(z,H)\longrightarrow0,\qquad
 d_{\mathrm H}(\tau F_n,\{p_H\})\longrightarrow0.
 \tag{Q126.16}
$$

证明。令 $v_n=(x_n+y_n)/2\to v=(x+y)/2$。由
$(v_n,x_n),(v_n,y_n)\in\mathscr B_S$，极限 $v$ 属于唯一完整球 $H$ 的相对内点，且
$x,y\in H$。任意 $z_n\in F_n$ 的聚点 $z$ 满足
$(v,z)\in\mathscr B_S$，故 $z\in H$；紧性遂给第二个结论。对任意
$w_n\in\tau F_n=\mathcal Z(v_n)$，闭关联给
$w\in\mathcal Z(v)$ 对所有聚点成立。如果 $H$ 重复，则 $x,y\in H$ 使
$(x,y)\in Q$，矛盾。因此 $H$ 单标签，$\mathcal Z(v)=\{p_H\}$，所有
$\tau F_n$ 的聚点都等于 $p_H$，这正是第三个结论。证毕。

### 126.4 不能存在重复球组成的边界开区

**定理 126.6（无非空开重复饱和区）。** 不存在非空 $X\subset S$，同时满足
$X$ 在 $S$ 中开且 $X$ 是若干颗完整重复三球的并。

证明。反设存在这样的 $X$。它是 $R$ 中完整纤维的并，令
$Y=q_R(X)\subset Y_R$，取限制 $q=q_R|_X:X\to Y$。定理126.4最后一段在不要求
$X$ 闭或紧的条件下，已经证明 $q$ 对这个子空间目标为闭商映射，纤维紧且 $Y$ Hausdorff。因为
$X$ 是紧流形 $S\cong S^m$ 的开子流形，固定 $y\in Y$，其紧纤维
$q^{-1}(y)$ 有开邻域 $U\Subset X$。闭性使
$O=Y\setminus q(X\setminus U)$ 是含 $y$ 的开集，且 $q^{-1}(O)\subset U$，从而
$O\subset q(U)\subset q(\overline U)$。这里 $\overline U$ 是在 $X$ 中取得的紧闭包，
$q(\overline U)$ 在 Hausdorff 空间 $Y$ 中紧闭，故 $\overline O\subset q(\overline U)$，
证明 $Y$ 局部紧。对紧集 $C\subset Y$，有限个这样的
$O$ 覆盖 $C$，于是 $q^{-1}(C)$ 是 $X$ 中闭的、并包含于有限个紧集 $\overline U$ 的并，故紧。
因此 $q$ proper，$Y$ 是 Baire 空间。

取一族可数的有理仿射超平面 $L_j\subset A$，每一张都切过
$\operatorname{ri}K$，并且使每个正维完整球与某个 $L_j$ 相交。这样的族可由固定坐标的有理高度枚举：球内任取两个不同点，在它们某一坐标的严格中间选有理高度。于是

$$
 Y=\bigcup_j q(X\cap L_j),
$$

每项因 $q$ 闭而闭。Baire 定理给出某个 $j$ 和非空开集
$O\subset Y$，满足 $O\subset q(X\cap L_j)$。置

$$
 X_1=q^{-1}(O),\qquad X_2=X_1\cap L_j.
 \tag{Q126.17}
$$

$X_1$ 是 $S^m$ 的非空开 $m$-流形；$X_2$ 是

$$
 S\cap L_j=\partial_{\mathrm{rel}}(K\cap L_j)\cong S^{m-1}
$$

的非空开 $(m-1)$-流形。这里 $L_j\cap\operatorname{ri}K\ne\varnothing$ 保证切片的相对内部非空，并保证其边界正是 $S\cap L_j$。

限制映射

$$
 g_1:X_1\to O,\qquad g_2:X_2\to O
 \tag{Q126.18}
$$

都是 proper 连续满射；其纤维分别是完整重复球和该球与 $L_j$ 的非空紧凸交，故均可缩。对局部紧 Hausdorff 空间取一点紧化，proper 性把
$g_i$ 延为保基点连续满射 $g_i^+:X_i^+\to O^+$。Lawson 的 Corollary 3.7
在紧 Hausdorff 连续满射、逐纤维可缩的条件下给出

$$
 \check H_c^j(O;\mathbb F_2)
 \cong \check H_c^j(X_i;\mathbb F_2)\qquad(i=1,2).
 \tag{Q126.19}
$$

这里没有把 $Y$ 或 $O$ 说成流形、ANR 或有限维空间；Lawson 只用于这些实际的一点紧化映射和紧凸纤维。

另一方面，$X_1$ 是非空 $m$-维流形开集，模二 Poincaré 对偶给

$$
 \check H_c^m(X_1;\mathbb F_2)\cong
 H_0(X_1;\mathbb F_2)\ne0,
$$

而 $X_2$ 是维数 $m-1$ 的流形开集，所以

$$
 \check H_c^m(X_2;\mathbb F_2)=0.
$$

这与(Q126.19)矛盾。证毕。

### 126.5 每颗重复球都遭遇单标签纯点积聚

令

$$
 R=\bigcup_{F\in\mathfrak B_{\mathrm r}}F,\qquad
 P_{\mathrm s}=P\setminus R.
 \tag{Q126.20}
$$

**定理 126.7（重复球的单标签积聚）。** 对每颗重复球 $F$，

$$
 \boxed{F\cap\overline{P_{\mathrm s}}^{\,S}\ne\varnothing.}
 \tag{Q126.21}
$$

因此 $R\ne\varnothing$ 时 $P_{\mathrm s}$ 在 $S$ 中不闭；这不推出整个 $P$ 不闭。

证明。反设某个重复球 $F$ 与 $\overline{P_{\mathrm s}}^{\,S}$ 不交，令

$$
 U=S\setminus\overline{P_{\mathrm s}}^{\,S},\qquad
 W=\{x\in S:(\mathscr B_S)_x\subset U\}.
 \tag{Q126.22}
$$

因 $\mathscr B_S$ 紧，

$$
 S\setminus W
 =
 \operatorname{pr}_1\bigl(\mathscr B_S\cap
 (S\times(S\setminus U))\bigr)
$$

闭，故 $W$ 开。由(Q126.10)，$F\subset W$，所以 $W\ne\varnothing$。

取 $x\in W$ 及包含 $x$ 的完整球 $H$。这样的 $H$ 总存在：混合边界点属于其非点真面，纯点
$p$ 则取 $q\in S(D_p)$，由零对称有 $p\in D_q$。若 $H$ 单标签，则其球边纯点全在
$P_{\mathrm s}$：若边界纯点同时属于重复球，IX116.2 的第三球孤立性将被违反。由于
$H\subset(\mathscr B_S)_x\subset U$，这与 $U\cap P_{\mathrm s}=\varnothing$ 矛盾。因此 $H$ 重复。
对每个 $z\in H$，(Q126.10) 给
$(\mathscr B_S)_z=H\subset U$，所以 $H\subset W$。于是 $W$ 是非空、在 $S$ 中开且由完整重复球组成的并，违反定理126.6。证毕。

若 $P_{\mathrm s}$ 在 $S$ 中闭，则
$\overline{P_{\mathrm s}}^{\,S}=P_{\mathrm s}$ 与重复球定义矛盾，故得到上述不闭性；但是积聚点可以是重复球球边上的纯点，不能把它升级成“$P$ 不闭”。

### 126.6 靠近重复球内点时的整球、效应和法向联动

固定重复对 $F,G=\tau F$，取
$x\in\operatorname{ri}F$ 及

$$
 x_n\in S\setminus(F\cup G),\qquad x_n\to x.
 \tag{Q126.23}
$$

对每个 $n$ 任选一颗包含 $x_n$ 的完整球 $H_n$。

**定理 126.8（移动球与互返纤维的统一收敛）。**

$$
 \sup_{z\in H_n}d(z,F)\to0,
 \tag{Q126.24}
$$

$$
 \sup_{p\in I(H_n)}d(p,G)\to0,
 \tag{Q126.25}
$$

并且

$$
 \sup_{\substack{z\in H_n\\y\in\mathcal Z(z)}}d(y,G)\to0.
 \tag{Q126.26}
$$

证明。若(Q126.24)失败，取 $z_n\in H_n$ 距 $F$ 有固定正下界；紧性给
$z_n\to z$ 子列。因 $x_n,z_n$ 同在 $H_n$，
$(x_n,z_n)\in\mathscr B_S$，极限给
$(x,z)\in\mathscr B_S$。式(Q126.9)给 $z\in F$，矛盾。

若 $p_n\in I(H_n)$，则 $x_n\in D_{p_n}$，零对称给
$p_n\in\mathcal Z(x_n)$。取收敛子列并用 $\mathscr Z$ 闭性及
$\mathcal Z(x)=G$，得到 $p_n$ 的所有聚点在 $G$，即(Q126.25)。对(Q126.26)，任取
$z_n\in H_n,\ y_n\in\mathcal Z(z_n)$；第一步给 $z_n$ 的聚点在 $F$，再用
$\mathcal Z|_F\equiv G$ 及闭性，得到 $y_n$ 的聚点在 $G$。证毕。

这三个结论控制的是整颗移动球、它的全部纯标签和每个点的整个零纤维；它们不要求
$H_n$ 单标签，也不要求球半径有统一下界。

**命题 126.11（原效应的定量平坦化）。** 在(Q126.23)的前件下，写

$$
 F=a+A_0\overline{\mathbb B^3},\qquad
 x=a+A_0\xi,\qquad \|\xi\|<1,
$$

其中 $A_0:\mathbb R^3\to\ker u$ 单射，并令

$$
 L_{\mathcal E}=\max_{f\in\mathcal E}\|f|_{\ker u}\|_{\ast}.
$$

则任意 $f\in\mathcal E$ 满足 $f(x_n)=1$ 时

$$
 \sup_{z\in F}(1-f(z))
 \le
 \frac{2L_{\mathcal E}}{1-\|\xi\|}\,\|x_n-x\|,
 \tag{Q126.27}
$$

任意 $h\in\mathcal E$ 满足 $h(x_n)=0$ 时

$$
 \sup_{z\in F}h(z)
 \le
 \frac{2L_{\mathcal E}}{1-\|\xi\|}\,\|x_n-x\|.
 \tag{Q126.28}
$$

证明。$\mathcal E$ 的紧性及限制映射的连续性保证 $L_{\mathcal E}<\infty$。
把 $h(a+A_0v)$ 写成 $\alpha+\langle\beta,v\rangle$。非负性给
$\alpha\ge\|\beta\|$，故

$$
 h(x)\ge(1-\|\xi\|)\alpha,\qquad
 \max_Fh=\alpha+\|\beta\|\le2\alpha.
$$

若 $h(x_n)=0$，则
$h(x)\le L_{\mathcal E}\|x_n-x\|$，得到(Q126.28)。对
$h=u-f$ 应用同一结论即得(Q126.27)。证毕。

**命题 126.12（归一化正法向的统一残值与最大面集中）。** 在(Q126.23)的前件下，令

$$
 \mathcal N_1(x_n)=
 \{h\in\mathcal E:h(x_n)=0,\ \max_Kh=1\}.
 \tag{Q126.29}
$$

每个 $\mathcal N_1(x_n)$ 非空且紧。取 IX116.3 给定重复侧 $G$ 的统一确认残值
$\varepsilon_G>0$，满足

$$
 f(y)\ge\varepsilon_G
 \quad(q\in S(G),\ y\in G,\ f\in\mathcal F_q).
$$

则

$$
 \boxed{\liminf_n\
 \inf_{h\in\mathcal N_1(x_n)}
 \min_{y\in G}h(y)\ge\varepsilon_G.}
 \tag{Q126.30}
$$

而且

$$
 \sup_{h\in\mathcal N_1(x_n)}
 \sup_{\substack{p\in K\\h(p)=1}}d(p,G)\longrightarrow0.
 \tag{Q126.31}
$$

证明。边界点 $x_n$ 的支撑超平面给一个非零 $b_n\in C^{\ast}$，满足 $b_n(x_n)=0$。
因 $K$ 线性张成 $V$，$M_n=\max_Kb_n>0$，所以
$b_n/M_n\in\mathcal N_1(x_n)$。评价和 $h\mapsto\max_Kh$ 连续，故该集合是紧集
$\mathcal E$ 的闭子集。

取任意子列及 $h_n\in\mathcal N_1(x_n)$，再用 $\mathcal E$ 紧性取
$h_n\to h$。有 $h(x)=0$ 且 $\max_Kh=1$，并由 $x\in\operatorname{ri}F$ 得
$h|_F=0$。每个最大面含一个纯点
$p_n$；取子列 $p_n\to p$，则 $p\in\mathcal Z(x)=G$ 且 $h(p)=1$。把
$p$ 写成 $G$ 的有限纯分解，$h(p)=1$ 迫使其中至少一个
$q\in S(G)$ 满足 $h(q)=1$。于是 $h\in\mathcal F_q$，由
$\varepsilon_G$ 得 $h|_G\ge\varepsilon_G$。若(Q126.30)不成立，则存在固定 $\epsilon>0$、
子列及 $h_n\in\mathcal N_1(x_n)$、$y_n\in G$，使
$h_n(y_n)<\varepsilon_G-\epsilon$。同时取 $h_n\to h$、$y_n\to y\in G$，
与刚证的 $h(y)\ge\varepsilon_G$ 矛盾。

若(Q126.31)不成立，则存在固定 $\epsilon>0$、子列及
$h_n\in\mathcal N_1(x_n)$、$t_n\in K$，满足
$h_n(t_n)=1$、$d(t_n,G)\ge\epsilon$。取共同收敛子列 $h_n\to h$、$t_n\to t$，
则 $h(x)=0$、$h(t)=1$，所以 $t\in\mathcal Z(x)=G$，矛盾。证毕。

**推论 126.13（对侧内点确认迫使整侧确认）。** 在(Q126.23)的前件下，若选
$h_n\in\mathcal N_1(x_n)$ 和 $p_n\in P$，满足 $h_n(p_n)=1$ 且
$p_n\to y\in\operatorname{ri}G$，则

$$
 \sup_{z\in G}(1-h_n(z))\longrightarrow0.
 \tag{Q126.32}
$$

证明。任意子列均可再取 $h_n\to h$。连续评价给 $h(x)=0$、$h(y)=1$。
非负性和 $x\in\operatorname{ri}F$ 使 $h|_F=0$；对 $u-h$ 在
$y\in\operatorname{ri}G$ 用同一论证，得到 $h|_G=1$。有限维泛函收敛在紧集 $G$ 上一致，
所以每个这样的子列都满足(Q126.32)；紧性反证遂给原序列的(Q126.32)。
这没有断言整个 $h_n$ 序列收敛到同一个效应。证毕。

定理126.8及命题126.11—推论126.13均未给出 $H_n$ 的半轴正下界，因而不排除其在 $F$ 内缩成低维集。

### 126.7 实际 proper 关联、紧支撑与切片的准确边界

**命题 126.14（原零关联及去除重复对后的 proper 投影）。** 两个原投影

$$
 \pi_1,\pi_2:\mathscr Z\longrightarrow S
 \tag{Q126.33}
$$

连续、满射且 proper，所有纤维都是单点或完整凸三球。

固定重复对 $F,G$，令

$$
 A_0=F\cup G,\qquad B_0=(F\times G)\cup(G\times F).
$$

则

$$
 \pi_1^{-1}(A_0)=B_0=\pi_2^{-1}(A_0).
 \tag{Q126.34}
$$

且限制

$$
 \mathscr Z\setminus B_0
 \ \substack{\xrightarrow{\ \pi_1\ }\\[-1mm]\xrightarrow[\ \pi_2\ ]{}}
 S\setminus A_0
 \tag{Q126.35}
$$

仍是 proper 连续满射，纤维仍为非空紧凸集。目标 $S\setminus A_0$ 是开
$m$-流形，源 $\mathscr Z\setminus B_0$ 是局部紧 Hausdorff 空间。其目标的紧支撑群为

$$
 \check H_c^j(S\setminus A_0;\mathbb F_2)
 \cong\check H^j(S,A_0;\mathbb F_2)
 =
 \begin{cases}
 \mathbb F_2,&j=1\text{ 或 }j=m,\\
 0,&\text{其他 }j.
 \end{cases}
 \tag{Q126.36}
$$

证明。引理126.1及边界上每点属于某颗完整球的事实说明 $\mathcal Z(x)$ 总是非空的纯单点或完整球。
因此两投影满射，纤维由引理126.1和对称性给出。$\mathscr Z$ 紧、$S$ Hausdorff，
故任一紧集的逆像为紧集，即两投影 proper。式(Q126.6)及对称性给(Q126.34)。
若 $C_0\subset S\setminus A_0$ 紧，则它在 $S$ 中仍紧，两条原投影的逆像紧，
且由(Q126.34)完全位于 $\mathscr Z\setminus B_0$。这证明(Q126.35)的 proper 性，
不需要目标的开补集闭或紧。$B_0$ 闭，故其补是紧 Hausdorff 空间 $\mathscr Z$ 的开子空间，因而局部紧。

$A_0$ 是两个不交的紧可缩球。采用 IX116.6 的 Čech 理论及紧支撑约定，紧空间的闭对给
$\check H_c^j(S\setminus A_0;\mathbb F_2)\cong\check H^j(S,A_0;\mathbb F_2)$。
相对长正合列中，$\check H^0(S)\to\check H^0(A_0)$ 是
$\mathbb F_2\to\mathbb F_2^2$ 的对角嵌入；$A_0$ 的正次数群均为零，
而 $S\cong S^m$、$m\ge5$。故一次相对群是该对角嵌入的余核 $\mathbb F_2$，
$m$ 次相对群是 $\check H^m(S)=\mathbb F_2$，其余均为零，得到(Q126.36)。
相同计算对 $m\ge2$ 成立。证毕。

本命题不将 $\mathscr Z\setminus B_0$ 认定为流形、ANR 或球丛。
两条映射拥有同一个目标；(Q126.36)没有产生两个不同维数的目标，不能单独排除重复对。

**命题 126.15（闭切片的双 proper 投影与 Čech 群）。** 对任一切过
$\operatorname{ri}K$ 的仿射超平面 $L\subset A$，定义

$$
 A_L=\{x\in S:\mathcal Z(x)\cap L\ne\varnothing\},\qquad
 \mathscr Z_L=\{(x,y)\in\mathscr Z:y\in L\}.
 \tag{Q126.37}
$$

则 $A_L$ 与 $\mathscr Z_L$ 都紧，且两个投影

$$
 \mathscr Z_L\to A_L,\qquad
 \mathscr Z_L\to S\cap L
 \tag{Q126.38}
$$

都是 proper 连续满射，纤维分别为
$\mathcal Z(x)\cap L$ 与 $\mathcal Z(y)$，均非空紧凸。对每个 $j\ge0$，有

$$
 \check H^j(A_L;\mathbb F_2)
 \cong
 \check H^j(S\cap L;\mathbb F_2)
 \cong
 \check H^j(S^{m-1};\mathbb F_2).
 \tag{Q126.39}
$$

证明。$\mathscr Z_L=\mathscr Z\cap(K\times L)$ 是紧集，$A_L$ 是其第一投影像，故也紧。
第一投影按定义满射，第二投影由 $\mathcal Z(y)\ne\varnothing$ 及零对称满射到 $S\cap L$。
两目标均 Hausdorff，所以映射 proper。纤维由定义及对称性恰为所列两种紧凸集。
对固定 $j$ 取整数 $n>j$，可缩纤维满足 Lawson Corollary 3.7 在
$0,\ldots,n-1$ 次的逐纤维同构条件；在整个紧 Hausdorff 目标上应用该推论，
两个拉回分别给源与各自目标的 Čech 群同构，从而得到(Q126.39)的第一个同构。

因为 $L$ 切过 $\operatorname{ri}K$，$K\cap L$ 在 $L$ 中有非空相对内部。
若其相对内点 $z$ 落在 $S$，取 $K$ 在 $z$ 处的非恒定支撑仿射函数。
截面内点性迫使该函数在 $L$ 上恒为支撑值，这与 $L$ 含有 $K$ 的相对内点矛盾。
因此 $S\cap L=\partial_L(K\cap L)$。从截面内点径向参数化得
$\partial_L(K\cap L)\cong S^{m-1}$，给出第二个同构。证毕。

**命题 126.16（开区限制的截纤维与 proper 障碍）。** 取命题126.15的 $L$，及一个同时在
$S$ 中开放的 $O\subset A_L$。令

$$
 E_O=\{(x,y)\in\mathscr Z_L:x\in O\},\qquad
 B_O=\operatorname{pr}_2(E_O)\subset S\cap L.
$$

第二投影 $E_O\to B_O$ 在 $y\in B_O$ 上的纤维，按第一坐标识别后恰为

$$
 \mathcal Z(y)\cap O.
 \tag{Q126.40}
$$

若该交集在紧空间 $\mathcal Z(y)$ 中不闭，则此第二投影不 proper。

证明。固定第二坐标 $y$，零对称把 $y\in\mathcal Z(x)$、$x\in O$ 恰好改写为
$x\in\mathcal Z(y)\cap O$，得到(Q126.40)。紧 Hausdorff 空间中的非闭子集不紧，
所以所述非闭情形下，紧单点 $\{y\}$ 的逆像不紧，否定 proper 性。证毕。

$A_L$ 仅已知为紧集，不被认定为流形、ANR 或 $K$ 的闭面。
与开集相交并不保留紧凸纤维的闭性、凸性或可缩性；本章没有证明这里的全部截纤维具备这些性质，
也未给出满足全部 EB3 的相反实例。因此(Q126.39)仅适用于闭切片的上述 proper 映射，
尚不能把 IX116.6 的全局商矛盾延伸到这类开邻域。

### 126.8 对原静态候选和完整量子字典的准确回接

**推论 126.17（第125章的同域条件候选与完整静态字典）。** 本章的原域中，
第125章的完整条件等价链为

$$
\begin{array}{c}
\mathrm{EB3}+\mathrm{Inj}+
\overline{\{p\in P_{\rm reg}:\mathsf F(p)\}}^{\,P}=P\\
\Longleftrightarrow
\mathrm{EB3}+\mathsf{DC}
\Longleftrightarrow
\mathrm{EB3}+\mathsf{MC}
\Longleftrightarrow
\mathrm{EB3}+\forall b\in P:\ W(D_b)=1\\
\Longleftrightarrow
\exists\Phi:\operatorname{Herm}_3(\mathbb C)\overset\sim\longrightarrow V
\text{ 实线性},\
\Phi(\mathrm{PSD}_3)=C,\
u\Phi=\operatorname{Tr}.
\end{array}
\tag{Q126.41}
$$

这里 $\mathsf F,\mathsf{DC},\mathsf{MC}$ 及 $W(D_b)$ 使用
Q125.31—Q125.33 的整个原域定义，不把新得到的 $P_{\mathrm s}$ 或重复块积聚误读为接触。

任一等价条件成立时，完整的同域静态字典仍按第125章取得：全部
$\mathbb{CP}^2$ 纯态、整个 $\mathrm{PSD}_3$ 迹一态基、全部
$0\preceq A\preceq I_3$ 效应、Born 评价、有限数学 POVM、谱分解和 Jordan 结构。它们都是同一个
$\Phi$ 下的全部对象，不是只对纯点或选定菜单的匹配。

证明。这里的 $V,C,u,K,P,\mathcal E,D_p$ 与第125章约定125.1是同一组完整原对象。
直接应用125.9的(Q125.31)—(Q125.35)，得到(Q126.41)的双向等价及反向全模型量词。
再由125.10沿同一 $\Phi$ 的全域运输，得到全部态、效应、评价、有限数学POVM和谱／Jordan字典。证毕。

本章的拓扑结果没有证明 $\mathrm{EB3}\Rightarrow\mathrm{Inj}$，也没有证明
$\mathrm{EB3}\Rightarrow\mathsf{DC}$ 或全域接触；(Q126.41)没有删去任何条件。

**约定 126.18（独立的原过程、复合与动态合同）。** 实际来源、制备、共同仪器和事件仍需第125章的原合同。

同样保留全有限 $N$ 的 $W_N,C_N,u_N,K_N,P_N,\mathcal E_N$、全部分块的
$\min/\max$ 张量界、联合 $S_2$、纠缠纯点和高阶锥的独立量词；单体三球及本章的
$\mathscr Z$ 不产生它们。全旁观 CP、同族仪器、Lüders 更新、记录和控制也继续各自需要
原提升、输入预算和事件合同。时间群、Hamiltonian、物理钟和数值 $\hbar$ 不由静态拓扑或
(Q126.41)取得。

### 126.9 来源、文献条件与边界

本章的面与重复块接口直接复用
[完整排除面第七卷][Q126VII] 的 VII103.2 及
[排除球第九卷][Q126IX] 的 IX116.1—116.6；重复块的两侧标签、无第三球交和统一正残值均只在这些前件下使用。第125章的同一原域与静态回接见
[单个真实三角一二五章][Q126T] 的 Q125.1、Q125.31—Q125.33。

本章给出上述原域中的纸面数学证明，不声称 Lean kernel 核验。

[THREE_COPY 第八卷124][Q126VIII] 的定理124.5另以其假设124.1的全部全有限层级条件、
整个原联合 $S_2$、三条条件桥、$L=3$、同一含相位 $\mathsf F_{r,2}$ 种子及
$2/3\le t<1$ 为前件。它对每个有限 $a\ge0,k\ge1$ 分类 $H_{a;k}$ 中的普通秩一 dyad，
并包括零 dyad；不分类全部 $P_N$、原极端射线、整个 $H_{a;k}$ 或
$H_{a;k}\cap\mathrm{PSD}$，也不证明 $\mathsf F_{\max}$。这些较强前件和受限结论
不替代本章的全域静态候选与动态合同。

唯一用于紧支撑同调传递的外部结果是 J. D. Lawson,
*A generalized version of the Vietoris–Begle Theorem*, Fundamenta Mathematicae
65 (1969), 65–72，Corollary 3.7（印刷 p.71）及其 §2 的
Alexander–Wallace–Spanier Čech 理论；本章只用其对紧 Hausdorff 连续满射、逐纤维可缩的
cohomology 传递，并未把未知商目标说成 ENR 或流形。Lawson 原刊扫描见
[Corollary 3.7][Q126L]；一点紧化和紧支撑群的使用遵循 IX116.6 的同一约定。

[Q126VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2：EB条件下完整暴露面与真面穷尽。"
[Q126IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX116.1—116.6：原域、重复球刚性、统一残值、单标签球与Lawson商矛盾。"
[Q126T]: QUANTUM_ORIGIN_SAME_READBACK_AND_PARALLEL_RESET_CALIBRATION.md "Q125.1、Q125.31—Q125.33：同一原域的EB3候选与Herm_3(C)/PSD_3条件静态字典。"
[Q126VIII]: QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md "第124章假设124.1及定理124.5：完整全有限层级、原S2、三条条件桥、L=3、含相位F_{r,2}及2/3≤t<1下的普通秩一dyad分类。"
[Q126L]: https://web.archive.org/web/20250613232023id_/http://matwbn.icm.edu.pl/ksiazki/fm/fm65/fm6517.pdf "J. D. Lawson, A generalized version of the Vietoris–Begle Theorem, Fundamenta Mathematicae 65 (1969), 65–72；§2、Corollary 3.7，印刷p.71。"

### 126.10 完整白话

把整个原边界看成一张实际的球面地图，把每个完整排除三球看成地图上由原零关系刻出的实心街区。重复球对在零图上完全孤立，但闭关联说明：所有边界态的零一关系仍是一张紧的、对称的网；沿网走两步，恰好就是“两个点还在同一个真面里”。所有重复街区的并即使不是闭集，仍可按整颗球取商：先用紧共面关系把相关极限留在同一颗重复球内，再用闭商映射和两颗紧球的不交开邻域分开商点，所以商是 Hausdorff 的。若把这个商扩到所有边界，唯一可能的失闭是：一边的重复球仍有非退化形状，另一边却整体缩到单标签球的一个纯标签。更强的拓扑结论是，任何重复球都不能拥有一块由重复球组成的边界开邻域，所以每颗重复球都必须被单标签区域的纯点从外面逼近。靠近重复球内部时，邻近的整颗球趋近这一侧，它的全部纯标签和所有零纤维趋近对侧；零于邻近点的原效应在这一侧定量变平，归一化正法向在对侧保持统一正残值，全部最大点也集中到对侧。若一列最大纯点还趋于对侧的内点，才进一步得到这些效应在整个对侧一致趋于一。这些积聚约束仍没有证明所有外来 $D_p$ 不会塌缩，也没有证明 $\mathrm{Inj}$ 或全域接触。闭切片上的关联空间有真实的 proper 凸纤维和 Čech 同调，但一旦只截取边界开区，另一侧的纤维会被截断；其闭性、凸性和可缩性尚未证明，这是全局商证明尚未跨过的缺口。若以后补上第125章要求的 Inj 与稠密原接触，同一个 $\Phi$ 才回接完整的 $\mathrm{Herm}_3(\mathbb C)$、$\mathrm{PSD}_3$、迹、全部态与效应、Born、POVM 和谱字典；实际事件、仪器、有限复合与纠缠、$\mathsf F_{\max}$、全旁观 CP、时间、Hamiltonian 与 $\hbar$ 仍保持各自的原合同。

## 追加锚（本行以下为增补区）

## 127. 单次原种子接触、三次纯压缩与全域共同量子几何

### 127.1 同一个完整原模型与明确支付的种子入口

**约定 127.1（原域、原二元关系与条件范围）。** 取非零有限维实空间 $V$、闭尖生成凸锥 $C\subset V$，以及在 $C\setminus\{0\}$ 上严格正的原单位 $u\in V^*$。始终使用

$$
\begin{gathered}
K=C\cap\{u=1\},\qquad P=\operatorname{ext}K,\qquad
\mathcal E=[0,u]_{C^*},\\
\mathcal F_p=\{f\in\mathcal E:f(p)=1\},\qquad
\mathcal T_p(x)=\min_{f\in\mathcal F_p}f(x),\\
D_p=\{x\in K:\mathcal T_p(x)=0\},\qquad
\mathcal A_p=\{e\in\mathcal F_p:e|_{D_p}=0\},\\
N_p=\{h\in C^*:h(p)=0\},\qquad
N_{D_p}=\{h\in C^*:h|_{D_p}=0\},\\
p\perp q\quad\Longleftrightarrow\quad
\exists f\in\mathcal E:\ f(p)=1,\ f(q)=0.
\end{gathered}
\tag{Q127.1}
$$

这里 $\mathcal T_p$ 是前文的标量最低确认函数 $T_p$，与下文的线性种子压缩 $T_i$ 不同型。$D_p$ 是整个原零对一排除集合；$K,P,\mathcal E$ 均不缩小。补效应给原正交对称性，且 $q\in D_p\Longleftrightarrow p\in D_q$ 对纯端点成立。

本章的固定入口记为 $\mathsf{Ent}_\triangle$，逐项包含：

1. EB3：每个原纯标签 $p$ 的完整 $D_p$ 均仿射同构于整个闭三球；Inj：$D_p=D_q\Rightarrow p=q$。
2. 一组实际原正交三角 $\triangle=(p_1,p_2,p_3)$，且至少一个顶点属于 $P_0=\{p:\mathcal A_p\text{ 是单点}\}$。
3. 125.5的同一个联合分离条件 $\mathsf J_\triangle$：对全部 $x,y\in K$，若在任一种子顶点读零的每张原效应均对 $x,y$ 同读，则 $x=y$。
4. 125.6由限制配对唯一确定的三个线性 $T_i$，全部满足 $T_i(C)\subseteq C$。

其中第3项和第4项使用的准确公式分别为

$$
\begin{gathered}
\forall x,y\in K:\quad
\bigl[\forall i\ \forall b\in\mathcal E,\ b(p_i)=0\Rightarrow b(x)=b(y)\bigr]
\Rightarrow x=y,\\
T_i:V\to M_i:=\operatorname{span}D_{p_i},\qquad
h(T_i x)=h(x)\quad(h\in\operatorname{span}N_{p_i},\ x\in V).
\end{gathered}
$$

第二行定义规范线性映射；其全锥正性是第4项另加的序条件。

后面再加的PC1也不是入口定义的隐含部分。真实三角、含 $P_0$ 的三角、联合分离、三个全锥正压缩和PC1分别写明；不把任何尚未推出的条件归给裸EB3。一个实际 $P_0$ 标签存在且确认歧义沿原边不变，已经由[IX119.10][Q127IX]证明；这不保证该标签进入实际三角。目标仍是同一原实现的完整内生量子重构；本章的条件定理只支付完整静态复三能级几何，操作、全部有限复合及时间的其余前件在127.10逐项保留。

直接复用VII103.2、104.1及IX119.1、120.2的完整原面接口：$\mathcal A_p\ne\varnothing$；每个 $D_p$ 是暴露极大真面；全部非空真面只有纯单点或完整排除球；不同完整球相交时只能交于一个原纯点；$P\cap D_p=\partial_{\rm rel}D_p$。任意 $e\in\mathcal A_p$ 的零面恰为 $D_p$，一值面恰为 $\{p\}$，包含对全部原混态的一值面判断。

法向维数只使用既有定理IX119.10的准确公式。若 $a(p)=\dim_{\rm aff}\mathcal A_p$，则

$$
\dim\operatorname{span}N_p=a(p)+4,\qquad
N_{D_p}=\operatorname{cone}\mathcal A_p,\qquad
\dim\operatorname{span}N_{D_p}=a(p)+1.
\tag{Q127.2}
$$

其沿每条原正交边的常数冗余与至少一个原 $P_0$ 标签也按该定理复用。下文只使用这些接口，不另证维数公式。

### 127.2 实际种子球固定的共同内积与三个非负二次量

**定义 127.2（规范种子坐标）。** 在 $\mathsf{Ent}_\triangle$ 下，125.3—125.6和IX120.8、120.12、120.18—120.19已经给出：三个顶点全属 $P_0$；写 $e_i=e_{p_i}$，则 $\sum_i e_i=u$ 于整个 $V$；$w=p_1+p_2+p_3$ 满足 $w/3\in\operatorname{int}C\cap K$；而且

$$
\begin{gathered}
D_i=D_{p_i},\qquad M_i=\operatorname{span}D_i
=\mathbb Rp_j\oplus\mathbb Rp_k\oplus L_i,\qquad \dim L_i=2,\\
V=\mathbb Rp_1\oplus\mathbb Rp_2\oplus\mathbb Rp_3
\oplus L_1\oplus L_2\oplus L_3,\qquad \dim V=9,\\
T_i|_{M_i}=I,\qquad T_i p_i=0,\qquad
T_iL_j=T_iL_k=0,\qquad uT_i=u-e_i,\\
R_i x=e_i(x)p_i,\qquad T_iT_j=T_jT_i=R_k
\quad(\{i,j,k\}=\{1,2,3\}).
\end{gathered}
\tag{Q127.3}
$$

这里九维是联合分离的既有后果，$T_i$ 的全锥正性仍来自入口第4项。记

$$
c_i=(p_j+p_k)/2,\qquad d_i=(p_j-p_k)/2,\qquad
W_i=\operatorname{lin}(D_i-c_i).
$$

以实际球 $D_i-c_i$ 为单位球定义欧氏型 $g_i$。原效应 $e_j$ 在球内对 $p_j,p_k$ 读一、零，所以它们确为实际对径，$g_i(d_i,d_i)=1$，且 $L_i=d_i^{\perp_{g_i}}\cap W_i$。对 $\ell\in L_i$，准确球锥条件为

$$
a p_j+b p_k+\ell\in C_i:=\operatorname{cone}D_i
\quad\Longleftrightarrow\quad
 a,b\ge0,\qquad g_i(\ell,\ell)\le4ab.
\tag{Q127.4}
$$

定义对称正定型 $B$：六个直和块彼此正交，且

$$
B(p_i,p_j)=\delta_{ij},\qquad
B|_{L_i}=\tfrac12g_i|_{L_i},\qquad B(w,x)=u(x).
\tag{Q127.5}
$$

这个尺度是VIII111.3的种子尺度；此处只用实际球和125的配对来确定它，不调用该章更强W入口下的全纯取等。特别地，$B|_{W_i}=g_i/2$，不是 $g_i$。

取各 $L_i$ 上的 $g_i$ 正交单位坐标，写

$$
x=\sum_i a_i p_i+\ell^{(1)}+\ell^{(2)}+\ell^{(3)},\qquad
 a_i=e_i(x),\qquad
z_{jk}=(\ell^{(i)}_1+\mathrm i\ell^{(i)}_2)/2\quad(j<k).
\tag{Q127.6}
$$

其中 $i$ 是 $\{j,k\}$ 的补指标。于是

$$
\begin{gathered}
\Delta_1=a_2a_3-|z_{23}|^2,\qquad
\Delta_2=a_1a_3-|z_{13}|^2,\qquad
\Delta_3=a_1a_2-|z_{12}|^2,\\
\Delta_i(x)\ge0\quad(x\in C),\qquad
B(x,x)=u(x)^2-2\sum_{i=1}^3\Delta_i(x).
\end{gathered}
\tag{Q127.7}
$$

证明这些归一化。写 $a p_j+b p_k+\ell=(a+b)c_i+(a-b)d_i+\ell$；实际球锥要求 $a+b\ge0$ 及 $(a-b)^2+g_i(\ell,\ell)\le(a+b)^2$，等价于(Q127.4)。选择 $z_{jk}$ 的系数 $1/2$ 后，$|z_{jk}|^2=g_i(\ell^{(i)},\ell^{(i)})/4$。全锥正性使 $T_i x=a_jp_j+a_kp_k+\ell^{(i)}\in C_i$，故三个 $\Delta_i$ 非负。按正交块展开 $B(x,x)$，得到(Q127.7)。这些式子也包含零向量和任意非负质量。特别地，整个 $K$ 满足 $B(x,x)\le1$。

若将(Q127.6)放成Hermitian矩阵，所得实线性坐标记为 $\Psi_{\rm coord}:V\to\operatorname{Herm}_3(\mathbb C)$，则

$$
B(x,y)=\operatorname{Tr}(\Psi_{\rm coord}(x)\Psi_{\rm coord}(y)),\qquad
\operatorname{Tr}\Psi_{\rm coord}(x)=u(x).
\tag{Q127.8}
$$

令 $Q_i=I_3-E_{ii}$，并记

$$
F_2=\sum_{i=1}^3\{X\succeq0:X=Q_iXQ_i\},\qquad
Q_2=\{X\in\operatorname{Herm}_3(\mathbb C):Q_iXQ_i\succeq0\ (i=1,2,3)\}.
$$

三张实际种子球锥的和映为 $F_2$，而原正性只给

$$
F_2\subseteq\Psi_{\rm coord}(C)\subseteq Q_2.
\tag{Q127.9}
$$

这是种子代数的夹逼，不是完整PSD判据。各横向平面的独立正交坐标选择不改变 $B$，但此时没有认定任意这种坐标都把整个 $C$ 送成PSD锥。

### 127.3 种子球面标签的实际确认与完整球上的半转

**引理 127.3（原效应与双侧零核）。** 固定 $i$，取 $q\in P\cap D_i$，令 $r$ 为 $q$ 在实际球 $D_i$ 内的对径。设 $g_q$ 是这张球上在 $q,r$ 分别取一、零的仿射效应，并将其唯一线性延至 $M_i$。则

$$
e_q=g_qT_i=B(q,\cdot)\in\mathcal A_q,\qquad
Z_K(e_q)=D_q,\qquad
N_{D_q}=\mathbb R_+e_q,\qquad q\in P_0.
\tag{Q127.10}
$$

这里 $Z_K(h)=\{x\in K:h(x)=0\}$；$C_i^*$ 表示在 $M_i$ 上对 $C_i$ 非负的全部线性泛函。

证明。先核对球内刻度。写 $q=c_i+v$、$r=c_i-v$，$g_i(v,v)=1$。对 $y=c_i+h\in D_i$，

$$
g_q(y)=\frac{1+g_i(v,h)}2=B(q,y).
$$

因为 $B(c_i,c_i)=1/2$、$B(c_i,W_i)=0$ 和 $B|_{W_i}=g_i/2$。这也给其在整个 $C_i$ 上 $0\le g_q\le u|_{M_i}$。故在原整个锥上

$$
0\le g_qT_i\le uT_i=u-e_i\le u.
\tag{Q127.11}
$$

它确为原效应，在 $q$ 取一，在不同的原纯点 $p_i,r$ 取零。其零面是包含这两点的非点真面，原面分类使它为极大真面。该零面包含于完整 $D_q$，所以等于 $D_q$；从而 $g_qT_i\in\mathcal A_q$。$T_i$ 按(Q127.3)是 $B$ 正交投影，$q\in M_i$，所以全 $V$ 上 $g_qT_i=B(q,\cdot)$。

再说明唯一性所用的原对偶接口。对每个 $h\in N_{p_i}$，规范压缩的定义给 $hT_i=h$；其在 $C_i$ 上的限制非负。反之，任意 $h_i\in C_i^*$ 与正 $T_i$ 复合，均在原 $C^*$ 中且零于 $p_i$。因此

$$
N_{p_i}=\{h_iT_i:h_i\in C_i^*\},\qquad
C\cap\ker T_i=\mathbb R_+p_i.
\tag{Q127.12}
$$

第二式由 $uT_i=u-e_i$ 及 $e_i$ 的整个一值面为 $\{p_i\}$ 得到。若 $h\in N_{D_q}$，则 $h(p_i)=h(r)=0$。第一式使 $h=h_iT_i$；Lorentz球锥在极射线 $\mathbb R_+r$ 上只有一条正支撑法向：在单位球图中，非负函数 $\alpha+b\cdot v$ 满足 $\alpha\ge|b|$，若在单位端点 $v_r$ 为零，则 $b=-\alpha v_r$，故它是该端点支撑函数的非负倍数。因此 $h_i$ 是 $g_q$ 的非负倍数，得到 $N_{D_q}=\mathbb R_+e_q$。由(Q127.2)，或直接将完整确认效应按在 $q$ 取一归一，$\mathcal A_q=\{e_q\}$。证毕。

**引理 127.4（受控的完整原球与准确零集）。** 定义线性反射

$$
S_i=2(T_i+R_i)-I,\qquad
\Gamma_i=\{x\in K:\Delta_i(x)=0\}.
\tag{Q127.13}
$$

这里 $S_i$ 专指反射，不沿用125.4中法向张成空间的简写。对每个 $q\in P\cap D_i$，均有

$$
S_i(D_q)=D_q,\qquad
\Gamma_i=\bigcup_{q\in P\cap D_i}D_q,\qquad S_i(\Gamma_i)=\Gamma_i.
\tag{Q127.14}
$$

证明。取引理127.3中的实际对径 $q,r$。对 $x\in D_q$，$g_q(T_i x)=e_q(x)=0$，而 $T_i x\in C_i$。该正锥的这个零面是一条射线，故

$$
T_i x=(1-e_i(x))r,\qquad
(T_i+R_i)x=e_i(x)p_i+(1-e_i(x))r.
\tag{Q127.15}
$$

原效应 $e_i$ 在同一完整实际球 $D_q$ 内于 $p_i,r$ 读一、零。这迫使 $p_i,r$ 是该球的实际对径，且 $e_i$ 是其轴向坐标。因此(Q127.15)是这个球到该直径的轴投影；$2(T_i+R_i)-I$ 在球内固定轴、反转两个横向方向，保持整个 $D_q$。

由(Q127.4)，$\Delta_i(x)=0$ 恰表示 $T_i x$ 是 $C_i$ 的极射线向量或零。非零时取其归一纯点 $r$ 和种子对径 $q$，引理127.3给 $e_q(x)=0$，所以 $x\in D_q$。零时(Q127.12)给 $x=p_i$，它也属于右侧的每个 $D_q$。反向包含由(Q127.15)立即成立，故零压缩没有漏出并集。各球均被 $S_i$ 保持，得到最后一式。证毕。

从原直和直接得到

$$
S_i^2=I,\qquad S_iS_j=S_jS_i=S_k\quad(\{i,j,k\}=\{1,2,3\}),\qquad
\Delta_m(S_i x)=\Delta_m(x)\quad(m=1,2,3).
\tag{Q127.16}
$$

具体地，$S_i$ 固定全部种子顶点及 $L_i$，在 $L_j,L_k$ 上取负号。此处对 $S_i$ 的全锥正性尚无结论；已经合法的只是(Q127.14)列出的整个原球族。

**命题 127.4a（同域零压缩、完整球相交与原中点接触）。** 在同一个 $\mathsf{Ent}_\triangle$ 下，对每个 $i$ 和每个原纯点 $p$，有逐点等价

$$
\begin{aligned}
\Delta_i(p)=0
&\Longleftrightarrow D_p\cap D_i\ne\varnothing\\
&\Longleftrightarrow
\exists q\in P:\ p\perp q\ \text{且}\ p_i\perp q\\
&\Longleftrightarrow \frac{p+p_i}{2}\in\partial_{\rm rel}K.
\end{aligned}
\tag{Q127.16a}
$$

更强地，对全部原混态 $x\in K$，仍有

$$
\begin{aligned}
\Delta_i(x)=0
&\Longleftrightarrow
\exists q\in P\cap D_i:\ x\in D_q\\
&\Longleftrightarrow x,p_i\text{ 同属某个原真面}\\
&\Longleftrightarrow \frac{x+p_i}{2}\in\partial_{\rm rel}K.
\end{aligned}
\tag{Q127.16b}
$$

证明。引理127.4已用实际原效应 $e_q=g_qT_i$ 证明(Q127.16b)第一项与第二项等价。每个这样的完整 $D_q$ 也包含 $p_i$，所以第二项给同属真面，继而给中点在原相对边界。

反向取边界中点的非恒定仿射支撑函数，令它在中点取零、在整个 $K$ 非负，再齐次化为非零 $h\in C^*$。因为两端读数都非负，$h(x)=h(p_i)=0$。以 $M=\max_Kh>0$ 归一，$h/M\in\mathcal E$，其一值面有一个原纯点 $q$。于是同一张原效应确认 $q$ 并零于 $x,p_i$，给 $x,p_i\in D_q$。仅对纯端点 $q,p_i$ 使用补效应互易，得 $q\in P\cap D_i$，回到第二项。这里的支撑、归一和最大面取纯点，正是[VII103.2][Q127VII]的原同面接口；没有对混态第一端点擅用纯标签互易。

现在令 $x=p$ 为原纯态。若 $\Delta_i(p)=0$，第二项给实际 $q\in P\cap D_i$ 且 $p\in D_q$，纯端互易给 $q\in D_p\cap D_i$。反之，非空交 $D_p\cap D_i$ 是整个原 $K$ 的非空紧面，取其中一个极点 $q$，它也是原纯点。故 $q\in P\cap D_i$，由互易有 $p\in D_q$，再由(Q127.14)得 $\Delta_i(p)=0$。交点的这种取得覆盖整个闭球，而非仅检查某个选定截面。中间的两条二元边恰是同一个 $q$ 的原零一关系，故(Q127.16a)成立。

若 $p=p_i$，$T_i p=0$，交集是整个 $D_i$，中点就是原纯点 $p_i$；若 $p\ne p_i$，Inj使两球不同，非空交恰为一个原纯点。对混态的零压缩也没有例外：由(Q127.12)，$T_i x=0$、$x\in K$ 恰给 $x=p_i$，它属于所有上述 $D_q$。因此“接触”包含球相等的情形，不额外要求不同球或非零压缩。证毕。

式(Q127.16a)中的 $(p,p_i,q)$ 只供应两条原边；一般没有 $p\perp p_i$，不能把共同邻点直接当作正交三角。以上等价只使用原效应、原面和同域纯端互易，未另造需要假定单射的标签关系。

### 127.4 原二元失败见证与实际三元提升

**命题 127.5（反射失败必有两个混合压缩）。** 若某个 $S_i(C)\not\subseteq C$，则存在一张原纯态 $p\in P$ 和一张原效应 $f\in\mathcal E$，使

$$
f(S_i p)<0,\qquad
\Delta_i(p)>0,\qquad
\Delta_j(p)>0\ \text{或}\ \Delta_k(p)>0.
\tag{Q127.17}
$$

证明。从一个原正向量的非法像用闭锥分离，取得 $0\ne h\in C^*$，使 $h$ 在该像上为负。以 $m=\max_Kh>0$ 归一，$f=h/m\in\mathcal E$。线性函数 $fS_i$ 在紧基 $K$ 的最小面有一个原纯点 $p$，并满足严格负值。若 $\Delta_i(p)=0$，(Q127.14)使 $S_i p\in K$，与原效应非负矛盾。若另外两个 $\Delta_j(p),\Delta_k(p)$ 都为零，先由(Q127.14)有 $S_kp\in K$，它仍满足 $\Delta_j=0$；再有 $S_jS_kp=S_ip\in K$，仍矛盾。证毕。

见证中的两个对象是实际的 $p,f$；$S_ip$ 在取得正性之前只是原空间中的有符号候选，负数 $f(S_ip)$ 不是某次实际实验的负概率。

此见证还带一组真实有限三元对象。由于 $\Delta_i(p)>0$，实际 $T_i p$ 位于 $C_i$ 内部，可沿一条实际种子直径写成

$$
T_i p=\alpha q+\beta r,\qquad
q,r\in P\cap D_i\text{ 为实际对径},\qquad
\alpha,\beta>0,\qquad\alpha+\beta=1-e_i(p).
\tag{Q127.18}
$$

引理127.3使 $q\perp r$，并在全 $V$ 上给

$$
e_q+e_r=(g_q+g_r)T_i=u-e_i,\qquad
 e_i+e_q+e_r=u.
\tag{Q127.19}
$$

因此 $(p_i,q,r)$ 是实际原正交三角，三张实际原效应也恰和为原单位。若还需要展示第二个内部压缩，对(Q127.17)中的另一正 $\Delta$ 重复同一两端分解即可；无需新增状态或测试域。这不表示原 $p$ 位于上述某张受控排除球中，也不表示两次混合一定导致反射失败。数学三结果效应仍不自动供应共同实际仪器。

### 127.5 PC1在整个实际纯球面上先提升为PC2，再提升为三次纯压缩

**定义 127.6（同种子的PC1、PC2与PC3）。** 对同一个固定种子的三个实际正压缩，记

$$
\mathsf{PC}r:\qquad
\forall p\in P,\qquad
\#\{i\in\{1,2,3\}:\Delta_i(p)=0\}\ge r,
\qquad r=1,2,3.
\tag{Q127.20}
$$

零压缩计为零指标；非零时，$\Delta_i(p)=0$ 恰表示压缩属于实际种子锥的一条极射线。PC1只要求每张原纯态至少有一次这样的压缩，指标可随 $p$ 改变。由命题127.4a，它恰是以下两个原几何条件中的任一个：每张实际 $D_p$ 至少与一张完整种子球相交；每张原纯态与三个种子顶点形成的中点至少有一个在原相对边界。PC2要求至少两次，PC3要求三次。

PC1的否定恰为存在同一张原纯态的三个 $\Delta_i$ 全部严格正；PC2的否定是存在同一张原纯态的至少两个 $\Delta_i$ 严格正。所有量词遍历全部原纯点，不是只在三张种子球或有限几个标签上检查。PC1是另加的条件候选，未由 $\mathsf{Ent}_\triangle$ 推出；本章不借用VIII111.5已另有含义的H2名称。

**引理 127.7（有限零集覆盖固定出球面恒等式）。** 设三个次数不超过二的实多项式 $f_1,f_2,f_3$ 在闭单位三球上非负。若在单位球面的每一点至少 $r$ 个为零，其中 $r=1$ 或 $2$，则至少存在 $r$ 个固定指标 $i$，使

$$
f_i(v)=\lambda_i(1-|v|^2),\qquad\lambda_i\ge0
\quad(v\in\mathbb R^3).
\tag{Q127.21}
$$

证明。先说明球面限制的零集若有相对内部，则限制恒零。取零开片及任意球面目标点，从开片取一个与目标点不共径的点；经过这两点的大圆与开片相交于一段开弧。多项式沿大圆是有限三角多项式；乘适当复指数后成为关于单位圆参数的普通多项式，开弧上无穷多个根迫使整圆恒零。因目标点任意，得到整球面恒零。

所以每个不恒零的限制，其非零集是球面上的开稠密集。有限个开稠密集的交仍稠密且非空：依次将任意非空开片与下一个开稠密集相交，所得仍为非空开片。若恒零指标少于 $r$，在所有其余指标的非零集之交取一点，此点的零指标数就少于 $r$，矛盾。故至少 $r$ 个固定指标在整球面上恒零；这里没有假定逐点所选指标连续。

将其中任一个写成 $f(v)=a+b\cdot v+v^{\mathsf T}Hv$，$H$ 对称。比较单位 $v,-v$ 得 $b=0$；在所有单位向量上 $v^{\mathsf T}Hv=-a$，由坐标单位向量及两两等权和，得到 $H=-aI$。因此 $f=a(1-|v|^2)$ 对全部 $v$ 成立，在球心的非负性给 $a\ge0$。证毕。

**引理 127.7a（一个固定指标拉回另外两个真实种子极射线）。** 固定原纯点 $p$，将其整个实际排除球写成

$$
D_p=c+A\overline{\mathbb B^3},\qquad
A:\mathbb R^3\longrightarrow\ker u\text{ 单射},\quad u(c)=1,
\qquad M_p=\operatorname{span}D_p=\mathbb Rc\oplus A\mathbb R^3.
$$

设某个固定指标 $i$ 满足

$$
\Delta_i(c+Av)=\lambda_i(1-|v|^2)\quad(v\in\mathbb R^3),\qquad \lambda_i\ge0.
$$

则 $\lambda_i=0$ 时 $p\in P\cap D_i$；$\lambda_i>0$ 时有实际满锥同构(Q127.24)，且 $\Delta_j(p)=\Delta_k(p)=0$，其中 $\{i,j,k\}=\{1,2,3\}$。

证明。因为 $\Delta_i$ 是齐次二次型，且 $\Delta_i=\Delta_i\circ T_i$，上述恒等式在整个四维 $M_p$ 上齐次化为

$$
\Delta_i(sc+Av)=\lambda_i(s^2-|v|^2)
\quad(s\in\mathbb R,\ v\in\mathbb R^3).
\tag{Q127.23}
$$

先对 $s\ne0$ 代入 $v/s$，再由多项式连续性覆盖 $s=0$。源实际球锥恰为 $\{sc+Av:s\ge|v|\}$；它是原 $C$ 的一个暴露面锥。

若 $\lambda_i=0$，实际正像 $T_i(\operatorname{cone}D_p)$ 是 $C_i$ 边界中的凸锥。两个不成比例的非零Lorentz边界向量之和在内部：写成 $(t,v),(s,z)$，其中 $t=|v|>0,s=|z|>0$，不成比例使三角不等式严格，$|v+z|<t+s$。所以该像只能包含在一条极射线中，或全为零。全零会由(Q127.12)使整个 $D_p$ 只含 $p_i$，与完整三球矛盾。故存在实际种子纯点 $r$，使该像包含于 $\mathbb R_+r$。取实际种子对径 $q$；原效应 $e_q=g_qT_i$ 零于整个 $D_p$。由(Q127.10)，$D_p\subseteq D_q$；原面极大性给两球相等，原标签Inj给 $p=q\in P\cap D_i$。这里使用的是原 $D$ 的Inj，而非人为定义的新关系的单射性。

若 $\lambda_i>0$，在目标四维 $M_i$ 上，$\Delta_i$ 是非退化Lorentz二次型。对(Q127.23)极化。若 $h\in M_p$ 且 $T_i h=0$，则对每个 $k\in M_p$，源Lorentz配对乘 $\lambda_i$ 等于目标在 $T_i h,T_i k$ 的配对，故为零。源配对非退化，推出 $h=0$。源、靶同为四维，$T_i|_{M_p}$ 因而是线性双射。

还须证明逆像为正。任取 $0\ne y\in C_i$，令 $h$ 为其唯一线性逆像。目标 $\Delta_i(y)\ge0$，(Q127.23)使源Lorentz型在 $h$ 非负，因此 $h$ 或 $-h$ 属于 $\operatorname{cone}D_p$。若只有 $-h$ 为正，已付的 $T_i$ 正性会使 $-y\in C_i$，与 $y\ne0$ 和 $C_i$ 尖性矛盾。故 $h\in\operatorname{cone}D_p$；零点的逆像也是零。于是

$$
T_i:\operatorname{cone}D_p\overset{\sim}{\longrightarrow}C_i
\quad\text{为满的线性锥同构}.
\tag{Q127.24}
$$

现在必须拉回两条实际种子顶点射线，而非只说抽象极射线存在。令

$$
x_j=(T_i|_{M_p})^{-1}p_j,\qquad
x_k=(T_i|_{M_p})^{-1}p_k,\qquad
y_j=\frac{x_j}{u(x_j)},\quad y_k=\frac{x_k}{u(x_k)}.
\tag{Q127.24a}
$$

锥同构已保证 $x_j,x_k$ 是源锥的非零正极射线向量，严格正单位保证分母正。因源锥是原 $C$ 的面锥，$y_j,y_k\in P\cap D_p$，不是一般有符号原像。由 $e_kT_i=e_k$ 得 $e_k(x_j)=e_k(p_j)=0$，故 $y_j\in P\cap D_k$；同理 $y_k\in P\cap D_j$。同域纯端互易将 $y_j,y_k\in D_p$ 变为 $p\in D_{y_j}\cap D_{y_k}$。引理127.4对实际种子球 $D_k,D_j$ 的这些标签给

$$
p\in\Gamma_k\cap\Gamma_j,\qquad
\Delta_k(p)=\Delta_j(p)=0.
\tag{Q127.24b}
$$

这里未假定 $y_j\perp y_k$，也未由一个固定指标就断言 $\Delta_i(p)=0$；$p$ 本身不在自己的 $D_p$ 内。证毕。

**定理 127.8（单次全原种子接触强制两次，再强制三次）。** 在 $\mathsf{Ent}_\triangle$ 下，

$$
\mathsf{PC1}\Longrightarrow\mathsf{PC2}\Longrightarrow\mathsf{PC3},\qquad
\mathsf{PC3}\ \Longleftrightarrow
\forall p\in P:\ \Delta_1(p)=\Delta_2(p)=\Delta_3(p)=0.
\tag{Q127.22}
$$

证明。先处理原边界坐标。若 $p\in P\cap D_i$，则 $a_i(p)=0$，该球中仅有另外两个对角块和自己的横向块。球面条件给 $\Delta_i(p)=0$，其余两项也为零。因此三个种子顶点、任意原零坐标标签及任何零压缩标签均已满足PC3。以下固定 $p\notin D_1\cup D_2\cup D_3$；此时三个 $a_i(p)>0$。

设全原PC1成立。在整个实际球 $D_p=c+A\overline{\mathbb B^3}$ 上，三个 $f_i(v)=\Delta_i(c+Av)$ 均非负；其整个球面均为原纯点，故每一点至少一个 $f_i$ 为零。引理127.7的 $r=1$ 情形给一个固定指标及其系数 $\lambda_i\ge0$。引理127.7a的零系数情形会迫使 $p\in D_i$，与选择矛盾，所以系数严格正；同一引理拉回两个实际种子顶点，给 $\Delta_j(p)=\Delta_k(p)=0$。因此PC2对每个原纯点成立。

再设全原PC2成立，对同一类球面应用引理127.7的 $r=2$ 情形。这次有两个不同的固定指标，其系数均由种子球外条件保证严格正。每个固定指标通过引理127.7a使另外两个指标在原 $p$ 处为零；两个不同补指标集的并是全部三个指标，故 $\Delta_1(p)=\Delta_2(p)=\Delta_3(p)=0$。这完成第二次提升。反向PC3到PC2到PC1由计数直接成立。证毕。

由命题127.4a，在全原PC1成立后，每张 $D_p$ 实际同时与三张种子球相交，三个原种子中点也全部位于原相对边界。

因此PC1还足够使三个 $S_i$ 在整个 $C$ 上为正：在其已推出的PC2下，对每个原纯点，(Q127.14)或(Q127.16)的两次合法球内半转给每个 $S_ip\in K$；$K=\operatorname{conv}P$ 和线性性再推广至全部状态及非负质量。$S_i^2=I$ 使它们成为原锥的数学自同构。这一后果没有被用来预付(Q127.24)，也不提供实际可执行反射。

### 127.6 共同纯球面迫使全部完整原球变圆

**引理 127.9（同一内积下的整球圆性）。** 在 $\mathsf{Ent}_\triangle$ 下，以下两项等价：全部原纯点满足(Q127.22)；全部原纯点满足 $B(p,p)=1$。任一项成立时，每个完整原排除球都有

$$
\begin{gathered}
D_p=c_p+\{v\in H_p:B(v,v)\le R_p^2\},\qquad \dim H_p=3,\\
B(c_p,H_p)=0,\qquad R_p^2=1-B(c_p,c_p)>0.
\end{gathered}
\tag{Q127.25}
$$

证明。等价由(Q127.7)中三个非负数之和为零立即得到。对任一实际球图 $D_p=c+A\overline{\mathbb B^3}$，其整个球面均属 $P$，所以对所有单位 $v$ 有 $B(c+Av,c+Av)=1$。比较 $v,-v$ 得 $B(c,Av)=0$；剩下的恒等式使 $A^*BA$ 是标量矩阵 $R^2I$，$R^2=1-B(c,c)>0$。这便是(Q127.25)。该逐球二次型计算也见[整球卷VI89.3][Q127WholeVI]的证明；这里不输入该卷的群传递性或全二纯面条件。证毕。

### 127.7 原种子效应的非负性固定球心、半径与满宽

**定理 127.10（全标签共同圆球及原效应饱和）。** 在 $\mathsf{Ent}_\triangle$ 下，若全部原纯点的三个 $\Delta_i$ 均为零，则每个原 $p\in P$ 的完整排除球满足

$$
\boxed{\quad
c_p=\frac{w-p}{2},\qquad B(c_p,H_p)=0,\qquad
R_p^2=\frac12,\qquad W(D_p)=1.
\quad}
\tag{Q127.26}
$$

其中宽度使用同一个整个原效应域：

$$
W(D_p)=\max_{f\in\mathcal E}
\left(\max_{x\in D_p}f(x)-\min_{x\in D_p}f(x)\right).
\tag{Q127.27}
$$

证明。固定 $p$，写 $a_i=e_i(p)$，则 $a_i\ge0$、$\sum_i a_i=1$。对 $a_i<1$，实际正压缩 $T_i p$ 的质量为 $1-a_i>0$，且 $\Delta_i(p)=0$，所以

$$
r_i=\frac{T_i p}{1-a_i}\in P\cap D_i,\qquad
q_i=p_j+p_k-r_i\in P\cap D_i
\tag{Q127.28}
$$

是实际种子对径。由引理127.3，$e_{q_i}=g_{q_i}T_i=B(q_i,\cdot)$ 是原效应，且

$$
e_{q_i}(p)=g_{q_i}(T_i p)=0.
$$

故 $p\in D_{q_i}$，原正交对称性给 $q_i\in P\cap D_p$。没有将一个形式上的反极点先认作原态。若 $a_i=1$，则 $p=p_i$ 且 $T_i p=0$，该项的权重为零，直接省略。至少两项权重非零。

在同一个原直和中相加，有

$$
\begin{gathered}
\sum_{i:a_i<1}(1-a_i)=2,\\
\sum_{i:a_i<1}(1-a_i)q_i
=\sum_i(1-a_i)(w-p_i)-\sum_iT_i p=w-p.
\end{gathered}
\tag{Q127.29}
$$

这里含零权项的式子只是线性计算；$\sum_iT_i p=p+\sum_i a_i p_i$ 由(Q127.3)逐块得到。因此

$$
c_0:=\frac{w-p}{2}
=\sum_{i:a_i<1}\frac{1-a_i}{2}q_i\in D_p,\qquad
B(c_0,c_0)=\frac{B(w,w)-2B(w,p)+B(p,p)}4=\frac12.
\tag{Q127.30}
$$

令 $c=c_p$、$R=R_p$，使用引理127.9的同一个 $B$ 圆球。任选一个正权 $q_i$，因其为球面点，可写 $q_i=c+v_i$，$v_i\in H_p$、$B(v_i,v_i)=R^2$。原效应 $e_{q_i}=B(q_i,\cdot)$ 在这颗完整球上的最小值准确为

$$
\begin{aligned}
\min_{x\in D_p}e_{q_i}(x)
&=\min_{h\in H_p,\ B(h,h)\le R^2}
 B(c+v_i,c+h)\\
&=B(c,c)-R^2=2B(c,c)-1.
\end{aligned}
\tag{Q127.31}
$$

这是同一原效应在同一整个原球上的极值。它在原整个 $K$ 非负，故 $B(c,c)\ge1/2$。另一方面，$c_0\in D_p$ 且 $B(c,H_p)=0$，于是

$$
\frac12=B(c_0,c_0)=B(c,c)+B(c_0-c,c_0-c)\ge B(c,c).
$$

两界取等，使 $c=c_0$，再由(Q127.25)得 $R^2=1/2$。

最后，原球中的实际对径

$$
q_i'=2c-q_i=w-p-q_i\in P\cap D_p
$$

满足 $e_{q_i}(q_i)=1$、$e_{q_i}(q_i')=0$。故该原效应在 $D_p$ 的振幅为一，而全部原效应振幅均不超过一，得到 $W(D_p)=1$。同时 $(p,q_i,q_i')$ 是实际三条原边组成的三角。这也覆盖 $p=p_i$、某个 $a_i=0$、只有一个非零 $a_i$ 及全部 $a_i>0$ 的情形；证明只删除零权，不删除任何原标签。证毕。

该论证先获得实际原效应，再用其非负性取得球心下界；不能将 $B(q_i,\cdot)$ 在任意未知标签处的正性预设为共同自对偶。所需的只是种子球面标签已支付的(Q127.10)。

### 127.8 与原全域宽度重构的准确等价及同种子反向

**定理 127.11（固定已付入口内的单接触条件等价）。** 在 $\mathsf{Ent}_\triangle$ 下，下列九项等价：

1. PC1。
2. 对每个原纯点 $p$，至少一个 $i$ 满足实际完整闭球 $D_p\cap D_i\ne\varnothing$。
3. 对每个原纯点 $p$，至少一个 $i$ 满足原中点 $(p+p_i)/2\in\partial_{\rm rel}K$。
4. PC2。
5. PC3，即每个原纯点的三个实际种子压缩均为极射线向量或零，满足(Q127.22)。
6. 每个原纯点位于共同 $B$ 单位球面，即 $B(p,p)=1$。
7. 每个完整原 $D_p$ 是 $B$ 圆球，其三维方向空间 $H_p$ 满足 $B(c_p,H_p)=0$，球心为 $(w-p)/2$、共同平方半径为 $1/2$。
8. 对全部原纯标签 $p$，$W(D_p)=1$。
9. 存在同原全锥、同原单位的实线性双射

$$
\Phi:\operatorname{Herm}_3(\mathbb C)\overset{\sim}{\longrightarrow}V,
\qquad \Phi(\mathrm{PSD}_3)=C,\qquad u\Phi=\operatorname{Tr}.
\tag{Q127.32}
$$

证明。$1\Longleftrightarrow2\Longleftrightarrow3$ 逐点使用命题127.4a；$1\Longrightarrow4\Longrightarrow5$ 是定理127.8，$5\Longrightarrow1$ 直接成立。$5\Longleftrightarrow6$ 是引理127.9；$5\Longrightarrow7$ 及 $5\Longrightarrow8$ 是定理127.10。也可直接检查 $7\Rightarrow6$：对 $q\in P\cap D_p$，令 $b_p=B(p,p)$。第7项的正交球心和半径给

$$
b_q=\frac{3+b_p}{4}.
$$

因为 $p\in D_q$，反向同理 $b_p=(3+b_q)/4$。联立得到 $b_p=b_q=1$；每张非退化原球都有这样的 $q$，故对全部 $p$ 成立。

$8\Longleftrightarrow9$ 直接消费125.9的(Q125.33)、IX120.5及其所引IX116.17、VIII113.8—113.9；这是既有的全域宽度重构，不另做相位分类。

还须证明第9项对本章同一个种子的反向。由同原态效应字典，$\Phi^{-1}p_i$ 是三个两两正交的秩一投影；作一次共同酉共轭，可令它们为 $E_{ii}$。其完整确认效应唯一，故

$$
e_i(\Phi X)=\operatorname{Tr}(E_{ii}X),\qquad
\Phi^{-1}M_i=(I-E_{ii})\operatorname{Herm}_3(\mathbb C)(I-E_{ii}).
$$

在这个矩阵模型，$N_{p_i}$ 恰是由支撑于 $p_i^\perp$ 的全部PSD效应构成的锥，其实张成为该支撑上的全部Hermitian矩阵。因此，保留这些全部原零法向读数且取值于 $M_i$ 的唯一线性映射，正是矩阵角压缩：

$$
\Phi^{-1}T_i\Phi(X)=Q_iXQ_i,\qquad Q_i=I-E_{ii}.
\tag{Q127.33}
$$

这使用125.6定义的唯一性，故对应的是原 $T_i$。秩一PSD矩阵的每个角压缩秩为一或零，第9项因而推出第5项及PC1、PC2。所有蕴含闭合。证毕。

同一反向还固定共同度量，而不要求任意预选横向定向已拼好相位：种子直和在矩阵模型中成为三个对角射线和三个非对角实二平面；实际种子球的单位度量满足 $\operatorname{Tr}((\Phi^{-1}\ell)^2)=g_i(\ell,\ell)/2$。块间的迹配对正交和(Q127.5)于是给

$$
B(\Phi X,\Phi Y)=\operatorname{Tr}(XY),\qquad \Phi(I_3)=w.
\tag{Q127.34}
$$

$\Phi$ 是既有分类给出的共同表示，不声称它逐项等于任意选择的 $\Psi_{\rm coord}$；本章的反向不需要额外全局坐标相位定理。

**推论 127.11a（分类失败的同一原纯态见证与实际有限三元提升）。** 在 $\mathsf{Ent}_\triangle$ 下，不存在(Q127.32)的同原静态表示，恰当且仅当存在一张实际原纯态 $p\in P$，对同一个 $p$ 同时满足

$$
\begin{gathered}
\Delta_1(p)>0,\qquad\Delta_2(p)>0,\qquad\Delta_3(p)>0,\\
D_p\cap D_i=\varnothing,\qquad
\frac{p+p_i}{2}\in\operatorname{ri}K
\quad(i=1,2,3).
\end{gathered}
\tag{Q127.34a}
$$

前三个严格不等式、三个空交及三个内部中点，在这一存在式中逐点等价；只需其中任一组。二元形式是对每个 $i$，都不存在同一实际纯点 $q$ 同时满足 $p\perp q$ 与 $p_i\perp q$。

证明。定理127.11使不存在表示等价于PC1失败；由三个 $\Delta_i\ge0$，后者精确等价于存在同一 $p$ 的三个严格正值。命题127.4a把每个正值等价为该对完整原球不相交及该中点不在原边界。中点始终属于 $K$，故不在相对边界恰为在 $\operatorname{ri}K$。这同样排除了每一对的共同原邻点，未改变任何二元边的定义。

这种 $p$ 必在三张种子球外，所以 $0<a_i(p)<1$。每个实际 $T_i p$ 均为种子球锥的内部正向量，沿任一穿过其归一点的实际种子直径可写成

$$
\begin{gathered}
T_i p=\alpha_i q_i+\beta_i r_i,\qquad
q_i,r_i\in P\cap D_i\text{ 为实际对径},\\
\alpha_i,\beta_i>0,\qquad \alpha_i+\beta_i=1-a_i(p),\\
p_i\perp q_i,\qquad p_i\perp r_i,\qquad q_i\perp r_i,\qquad
e_i+e_{q_i}+e_{r_i}=u\quad\text{于整个 }V.
\end{gathered}
\tag{Q127.34b}
$$

原纯性来自实际种子球的整个球面；引理127.3的两张实际原效应确认这对对径，且其和为 $(g_{q_i}+g_{r_i})T_i=u-e_i$，所以三条原边与全域单位和都成立。于是每个内部压缩均带一个真实有限正交三元组及一对严格正混合权，而三个压缩仍来自同一个失败标签 $p$。当压缩归一点恰为种子球心时任选一条直径即可，未漏掉这一退化方向情形。证毕。

式(Q127.34a)刻画任何满足入口而失败的模型必须具有的障碍，并未构造这样的完整原模型，也未证明其存在或不可能。式(Q127.34b)的数学三结果不自动成为实际同族仪器；这三组有限提升也不使失败标签 $p$ 自己落在任何所列种子球中。

### 127.9 同一个表示下全部静态量子对象

以下仅在定理127.11的等价条件成立时成立，全部字典复用125.10、IX116.17及VIII113.9，并使用同一个 $\Phi$，不把静态结论提前放入入口。

| 静态对象 | 全部原域的准确对应 |
| --- | --- |
| 复射线与全部纯态 | 对全部 $z\in\mathbb C^3\setminus\{0\}$，$p_z=\Phi(zz^*/(z^*z))$；恰覆盖整个 $P\cong\mathbb{CP}^2$，相差非零复标量表示同一纯态 |
| 全部混态与质量 | 整个 $K=\{\Phi\rho:\rho\succeq0,\operatorname{Tr}\rho=1\}$；整个 $C=\Phi(\mathrm{PSD}_3)$ 含零及全部非负质量，保持全部有限凸组合和非负线性组合 |
| 原单位、全部效应和Born评价 | $u\Phi=\operatorname{Tr}$；每个原效应唯一对应 $0\preceq A\preceq I_3$，$f_A(\Phi\rho)=\operatorname{Tr}(A\rho)$；反向每个这样的 $A$ 都是原效应，含零、单位、补和全部混态输入 |
| 全确认、least与完整排除球 | 对归一 $z$，全部 $\mathcal F_{p_z}$ 对应 $zz^*\oplus A$、$0\preceq A\preceq I_{z^\perp}$；least为 $zz^*$，$\mathcal T_{p_z}(\Phi\rho)=\operatorname{Tr}(zz^*\rho)$，完整 $D_{p_z}$ 为 $z^\perp$ 上全部密度矩阵 |
| 纯二元比较与原正交 | $\mathcal T_{p_z}(p_v)=|z^*v|^2/((z^*z)(v^*v))$，零恰为复内积正交，且对全部纯端点互易 |
| 三结果与原完备正交框架 | 每条原正交纯边有唯一第三纯点；三个秩一投影和为 $I_3$，三原效应和为 $u$，容量为三；不把三个数学结果当成一台已实现的仪器 |
| 全部有限数学POVM | 对任意有限结果数，整个原 $f_j\ge0,\sum_jf_j=u$ 恰对应所有 $A_j\succeq0,\sum_jA_j=I_3$，对每个原输入有Born概率及正确总和 |
| 谱与全部实可观测量 | 每张原混态有三项正交谱分解，允许零权和重复谱；全部实线性可观测量对应全部Hermitian矩阵并有实谱分解 |
| Jordan结构、共同尺与中心 | $\Phi(X)\circ\Phi(Y)=\Phi((XY+YX)/2)$，共同内积为(Q127.34)，中心态为 $w/3=\Phi(I_3/3)$，共同排除球中心及半径为(Q127.26) |

由同一迹配对还可得 $C=C^{*B}$ 及 $B(C,C)\ge0$；它们在这里是完整静态重构的后果。复射线中的数学叠加及谱分解不自行生成实际相干准备、相位参考或可调用门。

### 127.10 原来源、全部有限联合、事件仪器和时间的保留合同

**共同来源与全部原操作。** 完整继承125.11及其所引124.9、123.13、VIII113.11、VIII112.9、IX120.11、THREE_COPY第七卷121.12、122.14的同一个原装饰元组 $\mathcal O$。它包括共同来源域、全部中点实现、原概率像紧性、全测试表及其闭性，零／单位／补／有界倍增，重复标签及每种同中点实现；全部非负质量，零／次归一／不等质量，过程和参考各自完整的相关联合输入域。原 $L,p,\omega,K,M$、两次使用同一读回、两实张成、全实关系、完整(83.8)、原VI(89.13)全部两尺度等式、C2、整个 $G=1_E$、精确PRE之后的整个H13及每个原资格态、活跃块严格负方向、共享总迹一、非活跃零质量与空活跃集，均保持各自原定义。这里的操作映射 $p$ 与纯标签按类型区分。

设备／事件／来源绑定、全部菜单分支、实际参考／副本／相关联合、记录／权限／控制、ready／flags、失败／拒绝／停止／销毁／返回、实际混合、原字、全部合法未来及每个中间切口继续保留。原生与细化消费者、terminal futures、联合有符号关系、细标签粗归组、记录后的条件未来、source-adoption及资源合同也继续按原消费者承担。$T_i$ 的正性、数学锥自同构或原三结果效应均不产生这些实际来源和接线。

**全部有限联合载体。** 每个有限 $N\ge1$ 仍须提供实际 $W_N=V^{\otimes_{\mathbb R}N}$、闭尖生成 $C_N$、严格正 $u_N=u^{\otimes N}$、整个 $K_N=C_N\cap\{u_N=1\}$、全部 $P_N=\operatorname{ext}K_N$ 以及完整原效应区间。对每个实际分块 $a+b=N$ 保留

$$
C_a\otimes_{\min}C_b\subseteq C_{a+b}
\subseteq C_a\otimes_{\max}C_b.
\tag{Q127.35}
$$

同一产品配对、严格张量单位、全部原因子置换及逆的正性、规范重括号和指定运输下的不连续位置分块，不能由单体表示替代。二份比较仍是整个实际联合 $S_2$：对任意产品或纠缠纯点 $p,q_\ell\in P_2$、任意有限族、全部 $t_\ell\ge0$ 且 $\sum_\ell t_\ell=1$，含零权和重复标签，要求

$$
\begin{gathered}
\mathcal T_p^{(2)}\!\left(\sum_\ell t_\ell q_\ell\right)
=\sum_\ell t_\ell\mathcal T_{q_\ell}^{(2)}(p),\\
\mathcal T_p^{(2)}(x)=
\inf_{\substack{f\in[0,u_2]_{C_2^*}\\ f(p)=1}}f(x).
\end{gathered}
\tag{Q127.36}
$$

仅产品态上的比较不支付这个合同。原低二份 $q=1,2$ 的least／谱性／正面投影及保纯到Jordan桥，唯一实际自复合 $(W_1,W_1,W_2)$ 的直和扇区限制、秩和实维乘法的复型选择，同一实际两因子的产品正规形，仍是既有全有限层级定理分别使用的三项供应。

原 $\mathsf F_{\max}$ 继续要求同一最大复块 $n_r=L\ge2$、同一含相位正交基上的

$$
g_r=\sum_{a=1}^L|a\rangle_r|a\rangle_r|a\rangle_r,\qquad
\Delta_r=|g_r\rangle\langle g_r|\in C_3,\qquad u_3(\Delta_r)=L,
\tag{Q127.37}
$$

其余三份扇区为零，归一原源为 $\Delta_r/L$，不预付三份纯性或实际制备；全经典 $L=1$ 支路仍按原定理免除此资源。在本章的单体复三能级支路，该最大块为 $L=3$。该三份正性资源不能由写出矩阵 $|g_r\rangle\langle g_r|$ 就取得。只在全部联合前件及三项供应齐备后调用已有全有限层级结论；二、三份的秩为九、二十七，不再要求高阶整个排除集合继续满足单体EB3。

**全旁观CP、实际事件和同族仪器。** 数学全旁观正性仍量化每个 $b\ge0$、任意含纠缠的同一共同输入，并要求

$$
(\operatorname{id}_{W_b}\otimes F)(C_{b+m})\subseteq C_{b+n}.
\tag{Q127.38}
$$

只有完整有限层级与其共同表示已供应，才沿原Choi桥将它识别为通常CP、矩形跨扇区Kraus及逐输入TP／TNI预算。同一实际事件的CP还需原完整提升、实际探针及相容核；让全部数学CP-TNI分支成为实际事件仍需事件饱和选择。共同输入预算、接线、记录、粗粒化和校准负责把分支组成同族仪器。条件态只在严格正质量分支归一，零质量分支不强定归一条件态；Lüders更新另外要求同一分支的锐效应、接受态中性与输出校准。全数学POVM、效应和为单位与可执行的同一仪器继续是不同合同。

**物理时间、Hamiltonian与数值 $\hbar$。** 原钟、实际动态来源、连续齐次可逆时间群和单位各自保留。若另外给定同一载体上全实时间连续线性群 $A_t$，满足 $A_0=I$、$A_{s+t}=A_sA_t$、$A_t(C)=C$、$uA_t=u$，有限维生成元仅描述这项额外供应。在重构的复块中，另给保迹酉时间族后才有通常形式

$$
U_t=\exp(-\mathrm i tH/\hbar),\qquad
\rho_t=U_t\rho U_t^*,\qquad
\mathcal L(\rho)=-\frac{\mathrm i}{\hbar}[H,\rho],\qquad H=H^*.
\tag{Q127.39}
$$

量词覆盖全部原输入和全部实际时间。$H$ 的标量平移不改变态作用，时间重标改变生成元尺度而不改变静态几何。恒等时间族与非平凡Hamiltonian族可共享本章全部静态对象，所以实际 $H$、能量标定、数值 $\hbar$、时空和物理空间维数并未由PC1或球内半转产生。

### 127.11 条件负担、原始来源与尚未推出的桥

定理127.11给的是固定 $\mathsf{Ent}_\triangle$ 内的准确剩余条件。仍缺的原始链条包括：裸EB3是否强迫Inj；在有关模型内能否找到含 $P_0$ 顶点的实际三角；这样的三角是否支付 $\mathsf J_\triangle$；三个规范 $T_i$ 是否全锥正；在这些入口已经支付后，为何每张实际 $D_p$ 必与至少一张种子球相交。最后一项精确等价于入口到PC1的桥，也精确等价于排除(Q127.34a)中的同一原纯点。定理127.8已把PC1到PC2到PC3的条件推导闭合，却没有支付这项自动性；这里既无 $\mathsf{Ent}_\triangle\Rightarrow\mathsf{PC1}$ 的证明，也无满足整个入口而违反PC1的完整反模型。

已有[IX120.3—120.5][Q127IX]的 $\mathrm{EB3}+\mathsf{DT}$ 要求真实三角顶点在整个 $P$ 中稠密；125.9的 $\mathrm{EB3}+\mathsf{DC}$ 要求原中点接触标签稠密。二者已经等价于全原球满宽与同原静态表示，且不把本章种子、$\mathsf J_\triangle$ 或三个正映射另列为输入。125.9的MC只要求每个 $b$ 与某个 $x\in D_b$ 的中点接触；本章第3项则量化每个 $p$ 与至少一个固定种子顶点的中点，未先要求 $p_i\in D_p$。两者定义不同，在本章入口内经各自已证链条才取得等价，不能混用记号或量词。

在固定已付域，PC1、PC2、PC3及全域静态表示逻辑等价。因此“至少一次接触”给出更简洁的直接几何谓词，却不表示同一入口内严格更弱的模型条件。相对于裸EB3，本章显式支付的种子、联合分离和正性也不能因谓词变短而宣称独立公理更少或已证最小。几何推导依次使用：完整原球面上的有限二次零集覆盖、真实Lorentz锥极射线拉回、共同圆球、原效应非负性迫使球心和半径取等，再接既有全满宽分类。

种子分解和规范压缩准确来自125.3—125.6；原完整面、共同支撑及纯端互易来自VII103.2、104.1和IX120.1—120.2；唯一确认及方向函数来自IX120.8、120.12—120.13；全部法向维数、沿边常数冗余和至少一个原 $P_0$ 来自IX119.10，均按其原结论复用。VIII111.3已有相同的种子 $1/2$ 内积尺度，VIII111.4在更强W域已有共同纯球面及共同球心；这里在取得全满宽以前只使用种子刻度，不输入其全纯框架完成。命题127.4a将原同面支撑接到实际种子效应；127.7—127.8的有限零集、二次型、锥极射线和互易推导，以及127.10的原效应饱和，在上述明确前件内组合使用。多项式零集、Lorentz严格三角不等式和二次型极化均已在证明中展开；全部静态分类及字典的承重来源仍是125.9—125.10、IX116.17及VIII113.8—113.9。

[Alfsen—Shultz][Q127AS]印刷页160的Hilbert ball property要求每对极点生成的整个最小面为norm-exposed Hilbert球；印刷页188 Corollary 7.5在有限维还要求每个norm-exposed face均projective。它不将三张正种子投影升级为全域projectivity。[Barnum—Müller—Ududec][Q127BMU] Theorem 16保留有限维、projectivity、对称跃迁概率和全部相应滤子保纯；不能只凭本章三个 $T_i$ 套用其Jordan结论。本章在全原球满宽以后才经既有完整桥消费这些成熟分类，不用文献名称代替未付前件。

[整球卷VI89.1、89.3][Q127WholeVI]在实际紧矩阵群 $H\le\operatorname{Aut}(C,u)$ 对全部原纯点传递，以及L3“每对不同原纯点生成的整个最小面都是三球”的前件下，取得不变内积中的共同纯球面及逐面圆性。EB3只规定零对一排除纤维，未支付这些群与二纯最小面前件。127.6复用的只是其证明中“整个椭球边界位于同一二次球面”的直接展开；本章的共同纯球面先由PC1到PC3取得，不输入群传递性或全二纯面条件。

[Q127VII]: QUANTUM_ORIGIN_FINITE_PURE_POINT_AND_FACET_OBSTRUCTIONS_VII.md "VII103.2、104.1：完整原面及其极大性。"
[Q127VIII]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII.md "VIII111.3—111.5：种子刻度、强W域的共同配对及另义H2；VIII113.8—113.9：同原静态字典。"
[Q127IX]: QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_IX.md "IX119.10及IX119.23—24；IX120.8、120.12—13、120.18—19；IX116.17位于116.13节；IX120.3—120.5：稠密原三角与全原球满宽。"
[Q127WholeVI]: QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VI.md "89.1、89.3：H与L3，以及共同纯球面上的逐面圆性计算。"
[Q127AS]: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6236-11511_2006_Article_BF02392307.pdf "E. M. Alfsen and F. W. Shultz, State spaces of Jordan algebras, Acta Mathematica 140 (1978), 155—190, DOI 10.1007/BF02392307；印刷页160、187—188，Theorem 7.2与Corollary 7.5。"
[Q127BMU]: https://arxiv.org/html/1403.4147v4#Thmtheorem16 "Howard Barnum, Markus P. Müller and Cozmin Ududec, Higher-order interference and single-system postulates characterizing quantum theory, arXiv:1403.4147v4, Theorem 16。"

### 127.12 完整白话

把所有原状态看成同一块完整凸实体，把全部原效应看成从零到一读数的尺。先明确支付EB3、原球标签一一对应、一个含唯一确认顶点的实际正交三角、三族零尺的联合分离和三张读回在整个原锥上的正性，这才得到同一个九维种子坐标。现在只另要求：每张原纯态背后的完整排除球，至少碰到三颗真实种子球中的一颗。这也恰好是它与三个种子顶点的中点至少有一个仍在整体边界，或至少一次种子读回仍为纯射线或零；三个说法用的是同一原态和原尺。

这个“一次”必须对全部原纯点成立，不能只查三个点。在某张完整原排除球的整个纯球面上，逐点可能选择不同种子，但有限个二次零集不可能靠都缺少开片的方式覆盖整张球面，所以至少有一个固定指标在整球面恒零。其系数若为零，会把原球标签迫回种子球；在种子球外，正系数则使整张实际球锥真的映满种子锥。把种子的两个真实顶点拉回来，再沿原正交关系交换两端，就在原标签上得到另外两次纯压缩。于是全原“一次”先变成全原“两次”；再对整球面用一次两指标论证，才把第三次也锁到球边。不能从一个孤立纯点的一次接触直接跳到三次。

随后，所有原纯点落在同一内积的单位球面，所有完整原排除球都成为这把共同尺下的圆球。从种子取得的几个真实反极点都属于同一原排除球，其加权平均是 $(w-p)/2$，平方长度为二分之一；其中一张真正的原确认尺在整颗球上不能读负数，又迫使球心平方长度至少是二分之一。球心是球所在平面里最短的点，两边取等便固定球心和半径。同一张原尺还在该完整球的一条真实直径上读到一和零，所以每张原球都满宽，接回已有的全部复三能级纯态、混态、全效应、Born概率、全部有限数学POVM、谱和Jordan字典。

仍未支付的是：为什么给定入口就排除了某张实际原排除球同时躲开全部三颗种子球。如果条件分类失败，同一张原纯态必须有三个内部压缩，它与三个种子顶点的中点也必须同时钻进整体内部；这是严格的必要且充分障碍形状，没有构造出这样的完整模型。更早的Inj、种子、联合分离及全锥正性也没有由裸EB3自动获得。谓词变短还不等于独立公理更少。完整内生量子重构的目标继续保留：全部有限复合与纠缠、三份正性资源、全旁观CP、实际事件与共同仪器、Lüders更新、记录、物理钟、Hamiltonian和数值 $\hbar$ 仍须各自原合同供应；条件静态三能级字典不替代这些内容。

## 追加锚（本行以下为增补区）
