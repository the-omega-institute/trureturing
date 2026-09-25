# 递归关系观察：联合来源、量子关系与有限时钟

本卷从[运输、任务记忆与完成化卷](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)的合法表示接口出发，研究同一实际来源的联合态、实际效果和相对时钟。完整已获档案 $C$ 以及源、参考、测量分支和时钟记录始终属于观察者；共享相位副本与独立来源、忘记时刻与取得时刻、形式逆与允许反转分别声明。

第1章讨论混合切面、零能量态族及量子几何修复；第2章讨论可执行效果、关系矩、紧轨道与整数能隙关系；第3章讨论有限窗口、随机步骤及共振分辨率。逐态最近点、统一 CPTP 修复、紧轨道恢复与精确实时间恢复是四个不同问题。经典多面体的 Hoffman 界只在其自身合同下成立。

以下是普通数学证明与具有明确版本的成熟结果应用，不是新增 Lean 核验，不因综合而主张原创。式号 TM 与另两卷共同组成唯一地址；所有样本取得和成本前提均是数学合同的一部分。

## 1. 混合切面与量子可行域

### 1.1 切面混合、合法时钟与联合关系

**命题 1.1（混合读数与联合关系）。** 若两份坐标 $A,B$ 已处于实向量空间，令
$$
\begin{pmatrix}A'\\B'\end{pmatrix}
=M\begin{pmatrix}A\\B\end{pmatrix},\qquad
M=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix},\qquad\det M\ne0.
\tag{TM.47}
$$
这是同一份联合数值的可逆编码。若 $A,B$ 是不同类型的记录、权限或关系，并无加法与标量乘法，则须先给合法编码。数值可逆也不保证变换在原预算、操作权限或精度内可取得。

若某个新坐标须作为沿允许过程严格增长的时钟，还要检验其方向。假设全部允许增量满足 $\Delta t>0$、$|\Delta x|\le v\Delta t$，其中 $v\ge0$ 是模型声明的变化率界。对 $t'=\alpha t+\beta x$，
$$
\Delta t'\ge(\alpha-|\beta|v)\Delta t.
\tag{TM.48}
$$
所以 $\alpha>|\beta|v$ 足以保证新时间严格增长；若两端斜率也都允许，此条件也是对全部这些增量严格增长的必要条件。没有变化率限制且所有实斜率都合法时，非零 $\beta$ 不保证严格增。原操作、方向、记录和费用须一起运输；这不指定光速或任何物理运动定律。

正交是指定双线性型的性质。按 $z'=Mz$ 的坐标约定，度量矩阵运输为 $g'=M^{-\mathsf T}gM^{-1}$。单有实数时间参数既不规定度量，也不推出时间与空间正交。

**信息位于联合关系。** 另一个更贴近纠缠的问题不是数值可逆混合，而是完整联合态能否由各部分读数恢复。给两份量子态
$$
|\Phi_\pm\rangle=\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
\tag{TM.49}
$$
两侧的约化态都为 $I/2$，所以任意单侧测量都不能区分正负相位；联合可观测量 $X\otimes X$ 在两态上的读数分别恒为 $+1,-1$。它定位的是关于正负相位的区别存在于共同关联中，不能说每侧完全没有任何信息。仅靠两份边缘态的后处理无法恢复这个区别，取得能力须包括所需联合测量或相关记录访问。

经典概率中也有同边缘、不同联合律的例子，故该现象本身不判定量子纠缠。固定子系统分解 $\mathcal H_A\otimes\mathcal H_B$ 后，量子纠缠要求联合态不能写成 $\sum_i p_i\rho_A^{(i)}\otimes\rho_B^{(i)}$。式(TM.49)的态是纯态而单侧约化态混合；纯可分态必须为乘积向量，故两者确实纠缠。经典混合 $\frac12|00\rangle\langle00|+\frac12|11\rangle\langle11|$ 具有相同单侧约化态和完全相关的计算基读数，但 $X\otimes X$ 的期望为零，这又区分了经典相关与相干联合关系。

固定子系统下，各自的局部酉换基不改变可分性；主动联合操作可以改变纠缠，而把“哪些算局部”改成另一子系统分解则改变问题本身。CNOT 将式(TM.49)变成 $|\pm\rangle\otimes|0\rangle$，使此前位于联合相位中的区别成为第一系统的局部可读区别；但它使用了一项联合耦合，不是对原边缘态作后处理。将它改读为被动表示运输时，状态、子系统算子和允许操作也必须一起变换。

代数上，同一有限维空间的自伴读数 $A,B$ 经实系数式(TM.47)混合，满足
$$
[A',B']=(\alpha\delta-\beta\gamma)[A,B].
\tag{TM.50}
$$
所以原本可交换的联合读数不会仅凭可逆数值混合变成非交换读数。普通程序的操作先后不交换也不自动给量子测量模型；后者还需状态、观测代数、概率和合法仪器。本节没有预设时间本身是量子自伴算子。

这将联合关系问题定位到可检验的关系：固定一份实际整体、接口和读数，哪些区别只能通过联合访问取得；改变合法接口或子系统划分后，这些区别怎样运输。动态规划边界、连续路径塔和量子联合态可以沿这一问题比较，但其状态类型、组合规则、代价及可执行测量各须明确保留。

### 1.2 守能约束、隐藏相干与动态充分边界

仓内已有“隐藏联合关系经过守能作用转成局部差异”的机制。固定快照 `237012b49d0d4729a86f7e9dd252d94df1de8dd0` 的 `docs/develop/theory/QUANTUM-REALITY.md:21994`，定理164.2取 $\gamma=\operatorname{diag}(2/3,1/3)$ 与 $\rho_\pm=\gamma\otimes\gamma\pm(i/9)(|10\rangle\langle01|-|01\rangle\langle10|)$：两侧热边缘相同，同一交换门 $U_{\pi/4}$ 后第二系统激发概率却分别为 $4/9,2/9$。两态对角元也相同，故计算基联合律及由该基对角 Hamiltonian 给出的完整能量分布均相同；该卷 `:21628` 的定理162.1说明此交换门在共同参照激发能相等时守能。以上已构成当前摘要不足以支持全部后续响应的仓内实例。

本节将这一既有机制改写成简并能量层中的简化参数族，详细说明纠缠参数怎样被摘要遗漏，再把初始子族扩充为整个不变状态族，给出 Bloch 坐标的动态闭合与行为商。这里没有把“同能量、同局部读数仍可在后续区分”当作新发现，也不将有限矩阵模型当作物理时空的推导。

#### 1.2.1 同一守能层中，仍有边界没有记录的关系

**反例 1.2（守能层内的隐藏相干）。** 固定两个量子位的子系统分解和计算基次序 $|00\rangle,|01\rangle,|10\rangle,|11\rangle$。取通常的 Pauli 约定，并选择一个无量纲 Hamiltonian：
$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
H=Z\otimes I+I\otimes Z=\operatorname{diag}(2,0,0,-2),\quad
E_0=\ker H=\operatorname{span}\{|01\rangle,|10\rangle\}.
\tag{TM.51}
$$

能量为零的条件本身不决定可分性：$|01\rangle$ 是乘积态，$(|01\rangle+|10\rangle)/\sqrt2$ 是纠缠态，却都属于 $E_0$。以下加强这一比较，让初始局部态也完全相同。对 $c\in\mathbb C$，定义
$$
\begin{aligned}
\rho_c
&=\tfrac12|01\rangle\langle01|+\tfrac12|10\rangle\langle10|
+c|01\rangle\langle10|+\overline c|10\rangle\langle01|\\
&=\begin{pmatrix}
0&0&0&0\\
0&1/2&c&0\\
0&\overline c&1/2&0\\
0&0&0&0
\end{pmatrix},\qquad |c|\le\tfrac12.
\end{aligned}
\tag{TM.52}
$$

它是 Hermitian，迹为一，特征值为 $0,0,1/2+|c|,1/2-|c|$。故所给参数范围恰好保证它是合法密度矩阵；超出此范围则出现负特征值。每个合法参数都有
$$
H\rho_c=0,\qquad
\Pr_{\rho_c}(H=0)=1,\qquad
\operatorname{Tr}_B\rho_c=\operatorname{Tr}_A\rho_c=I/2,\qquad
(p_{00},p_{01},p_{10},p_{11})=(0,1/2,1/2,0).
\tag{TM.53}
$$

第一项说明完整能量分布均为零点上的单位质量，不只是能量均值相同。两个约化态相同，说明任意单侧 POVM 的全部结果概率均相同；计算基联合概率也相同。但这并未指定所有联合测量的结果，因为 $c$ 仍是尚未写进这些摘要的联合相干。

#### 1.2.2 相同摘要不能判定纠缠

**反例 1.3（相同摘要与不同纠缠）。** 对第二系统作部分转置，得到
$$
\rho_c^{T_B}=
\begin{pmatrix}
0&0&0&c\\
0&1/2&0&0\\
0&0&1/2&0\\
\overline c&0&0&0
\end{pmatrix},\qquad
\operatorname{spec}(\rho_c^{T_B})=\{1/2,1/2,|c|,-|c|\}.
\tag{TM.54}
$$

若一份态可分，即可写为 $\sum_j p_j A_j\otimes B_j$，其中 $A_j,B_j$ 均为密度矩阵，则部分转置为 $\sum_jp_j A_j\otimes B_j^{\mathsf T}\succeq0$，因为转置保持正半定性。因此 $c\ne0$ 时出现的负特征值已经证明纠缠。$c=0$ 时，式(TM.52)本身就是两个乘积态的概率混合。因此，本族中“可分”等价于 $c=0$，且其 negativity 为 $(\|\rho_c^{T_B}\|_1-1)/2=|c|$。这里仅使用“可分推出部分转置正半定”的必要条件，没有借用一般维度中并不成立的逆命题。

于是，式(TM.53)的整份数据既不能恢复 $c$，也不能判定这族中的可分性或恢复 negativity。合法性、守恒关系、经典相关与量子纠缠是不同问题；完整保留前三者中的这些指定读数仍然可以遗漏第四者。

反过来，遗漏后续会用到的联合关系也不必是遗漏纠缠。开头所引《量子实在》定理164.2的两态恰好可以显式分解为可分态。为该卷的 $\gamma=\operatorname{diag}(2/3,1/3)$ 定义 $\tau_X^\pm=\gamma\pm X/3$、$\tau_Y^\pm=\gamma\pm Y/3$。这四个局部矩阵迹均为一，本征值为 $(3\pm\sqrt5)/6>0$，所以都是合法密度矩阵。对 $s\in\{+1,-1\}$，逐项展开得到
$$
\begin{aligned}
\rho_s
&=\tfrac14\bigl(
\tau_X^+\otimes\tau_Y^{-s}
+\tau_X^-\otimes\tau_Y^{s}
+\tau_Y^+\otimes\tau_X^{s}
+\tau_Y^-\otimes\tau_X^{-s}\bigr)\\
&=\gamma\otimes\gamma+\tfrac{s}{18}(Y\otimes X-X\otimes Y)\\
&=\gamma\otimes\gamma+\tfrac{si}{9}(|10\rangle\langle01|-|01\rangle\langle10|).
\end{aligned}
$$

故该卷的两态可分，而依然具有相同当前局部摘要、不同未来局部读数。这是所引实例的直接分解说明：纠缠是某些遗漏关系的性质，并非动态不充分性的必要条件。上述可分分解也只判定数学可分性；各局部因子带有相干，不能据此声称无相位参照的局部守能准备协议能够执行该分解。

#### 1.2.3 守能的联合操作把隐藏区别变成未来局部读数

**命题 1.4（合法交换揭示相干）。** 令 $U$ 在 $E_0^\perp$ 上为恒等，在有序基 $|01\rangle,|10\rangle$ 上为 Hadamard 矩阵：
$$
\begin{aligned}
U|00\rangle&=|00\rangle,\qquad U|11\rangle=|11\rangle,\\
U|01\rangle&=(|01\rangle+|10\rangle)/\sqrt2,\\
U|10\rangle&=(|01\rangle-|10\rangle)/\sqrt2.
\end{aligned}
\qquad U^\dagger U=I,\quad U^\dagger=U,\quad [U,H]=0.
\tag{TM.55}
$$

正交直和的每一块都是酉矩阵，故 $U$ 是酉操作；它只在同一个零能量本征子空间中混合，因此与 $H$ 对易，在所有输入上保持 $H$ 的完整能量分布。这是一项联合操作：它能把乘积态 $|01\rangle$ 变成纠缠态，不能解释为两个原局部态分别经过后处理。假设模型允许执行这项操作，才有以下可访问性结论；守能本身不授予实验权限，也不证明实施费用为零。

写 $c=x+iy$，直接进行二阶矩阵乘法得
$$
\left.U\rho_cU^\dagger\right|_{E_0}
=\begin{pmatrix}1/2+x&-iy\\iy&1/2-x\end{pmatrix},\qquad
\operatorname{Tr}\bigl[(Z\otimes I)U\rho_cU^\dagger\bigr]=2\operatorname{Re}c.
\tag{TM.56}
$$

特别地，$U\rho_0U^\dagger=\rho_0$，而 $U\rho_{1/2}U^\dagger=|01\rangle\langle01|$。两者仍以概率一具有能量零，但第一系统的 $Z$ 期望分别为 $0$ 和 $1$。过去读数中遗漏的联合相干，经允许的联合演化进入了后来的局部读数。

为准确表述摘要更新失败，令 $\mathcal D_0$ 为全部支撑于 $E_0$ 的密度矩阵集合，$T(\rho)=U\rho U^\dagger$，并在整个 $\mathcal D_0$ 上定义
$$
q(\rho)=\bigl(H\text{ 的完整分布},\ \operatorname{Tr}_B\rho,\ \operatorname{Tr}_A\rho,\ (\langle ab|\rho|ab\rangle)_{a,b\in\{0,1\}}\bigr).
\tag{TM.57}
$$

式(TM.53)、(TM.56)给出 $q(\rho_0)=q(\rho_{1/2})$，但 $q(T\rho_0)\ne q(T\rho_{1/2})$。因此
$$
\nexists\,\overline T:\operatorname{im}q\longrightarrow\operatorname{im}q
\quad\text{使}\quad
q\circ T=\overline T\circ q\quad\text{在全部 }\mathcal D_0\text{ 上成立}.
\tag{TM.58}
$$

证明只需反证：同一摘要经函数 $\overline T$ 必须产生同一摘要，与上述两态矛盾。这定位了一项实际的信息缺口，不能通过更复杂的摘要后处理补回。

这里必须使用 $\mathcal D_0$ 作为动态定义域。最初的等对角族 $\{\rho_c:|c|\le1/2\}$ 不在 $U$ 下闭合：只要 $\operatorname{Re}c\ne0$，式(TM.56)的两个对角元就不再相等。不能将 $T$ 误写成这一较小初始族的自映射，再以此声称已建立动态系统。

#### 1.2.4 恢复缺失关系需要声明读数权限

**命题 1.5（参考与读数权限）。** 在初始族的承诺下，两个联合相关期望足以恢复遗漏参数：
$$
\langle X\otimes X\rangle_{\rho_c}=2\operatorname{Re}c,\qquad
\langle X\otimes Y\rangle_{\rho_c}=2\operatorname{Im}c,\qquad
c=\tfrac12\bigl(\langle X\otimes X\rangle_{\rho_c}
+i\langle X\otimes Y\rangle_{\rho_c}\bigr).
\tag{TM.59}
$$

这两个等式由式(TM.52)与给定 $Y$ 符号约定直接相乘取迹。它们不是从已知边缘态计算出来的，而是新取得的联合关系。若允许在同一准备协议的不同试次中作局部 Pauli 测量，并对齐两侧结果，就能用结果乘积估计这些相关量；只保留两份未关联的边缘统计则不够。

还需保留三个访问条件。第一，$X\otimes X$ 与 $X\otimes Y$ 不对易，不能将两项期望写成同一份样本上同时确定的两次无扰读数；精确期望是模型对象，有限样本给出带统计误差的估计。第二，重复准备及共同来源须另行提供，不默认存在克隆任意未知态的操作。第三，普通局部 Pauli 测量的仪器并不自动与 $H$ 对易；若协议只允许守能仪器，需要明确可执行的替代实现。下一小节给出“守能联合旋转后读取局部 $Z$”的实现，在 $\mathcal D_0$ 上取得相同的必要坐标。式(TM.59)恢复整态的结论也依赖支撑与固定对角元的承诺，不能用于恢复任意双量子位态。

#### 1.2.5 闭合的整体表示：零能量子空间中的 Bloch 球

**命题 1.6（零能量逻辑量子位的闭合表示）。** 将等对角限制放开，$\mathcal D_0$ 的每个态在 $E_0$ 上唯一具有形式
$$
R(p,c)=\begin{pmatrix}p&c\\\overline c&1-p\end{pmatrix},\qquad
0\le p\le1,\quad |c|^2\le p(1-p).
\tag{TM.60}
$$

这些条件正好是迹为一的二阶 Hermitian 矩阵正半定的条件。将任意 $V\in U(2)$ 作为 $E_0$ 上的酉操作，并在 $E_0^\perp$ 上扩展为恒等，得到 $\widetilde V$。所有这些扩展均与 $H$ 对易，且 $\mathcal D_0$ 在它们之下闭合。

在有序基 $|01\rangle,|10\rangle$ 上，记 Pauli 矩阵为 $\tau_x,\tau_y,\tau_z$。定义
$$
\begin{aligned}
r_x&=2\operatorname{Re}c,\qquad
r_y=-2\operatorname{Im}c,\qquad
r_z=2p-1,\\
R&=\tfrac12\bigl(I+r_x\tau_x+r_y\tau_y+r_z\tau_z\bigr),\qquad
r_x^2+r_y^2+r_z^2\le1,\qquad c=(r_x-ir_y)/2.
\end{aligned}
\tag{TM.61}
$$

由 $|c|^2\le p(1-p)$ 立即得到球内条件，反向代入也恢复正半定条件。这些 Pauli 矩阵作用于简并本征子空间，并不是把原来的两个局部子系统重新认作同一个局部量子位。其与原读数的具体对应为
$$
\left.(X\otimes X)\right|_{E_0}=\tau_x,\qquad
\left.(X\otimes Y)\right|_{E_0}=-\tau_y,\qquad
\left.(Z\otimes I)\right|_{E_0}=\tau_z.
\tag{TM.62}
$$

因而式(TM.59)与 $r_y$ 的负号相容。当前局部 $Z$ 期望为 $r_z$，三项坐标共同确定整个 $R$，并给出每一项允许酉操作的精确更新：
$$
r'_i=\sum_{j\in\{x,y,z\}}O(V)_{ij}r_j,\qquad
O(V)_{ij}=\tfrac12\operatorname{Tr}(\tau_iV\tau_jV^\dagger),\qquad
R'=VRV^\dagger.
\tag{TM.63}
$$

证明为将式(TM.61)代入 $VRV^\dagger$，再用 $\operatorname{Tr}(\tau_i)=0$ 与 $\operatorname{Tr}(\tau_i\tau_j)=2\delta_{ij}$ 取出坐标。系数是实数，因为 Hermitian 矩阵乘积的迹为实；酉共轭保持 Hilbert–Schmidt 内积，所以 $O(V)$ 为正交矩阵，保持球内条件。这里三项坐标是允许动态闭合的表示，而原摘要 $q$ 在 $\mathcal D_0$ 上仅保留 $p$：能量分布固定，两份边缘态及计算基联合概率均只由对角元确定。

这三项坐标还能只用所声明的守能联合操作与局部 $Z$ 读取来取得。令
$$
H_2=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
S=\operatorname{diag}(1,i),\qquad
V_z=I,\quad V_x=H_2,\quad V_y=H_2S^\dagger.
\qquad
V_k^\dagger\tau_zV_k=\tau_k\quad(k=x,y,z).
\tag{TM.64}
$$

其中 $H_2^\dagger\tau_zH_2=\tau_x$，$S\tau_xS^\dagger=\tau_y$，故等式逐项成立。在同一准备态的不同试次中，执行 $\widetilde V_k$ 后读取第一系统 $Z$，其期望即为 $r_k$。所有 $\widetilde V_k$ 与 $H$ 对易；局部 $Z$ 的谱投影也与 $H$ 对易，故这一指定实验无需用不守能的局部 Pauli 仪器替代。它仍需实际的联合控制、重复准备与统计读取资源，并未将三项未知实数变成一次测量可取得的数据。

#### 1.2.6 最小性指行为商，不是无条件的压缩维数

**命题 1.7（行为商的任务最小性）。** 把允许实验明确固定为“任意 $E_0$ 酉操作的恒等扩展，随后读取第一系统 $Z$”，定义 $\rho\sim\sigma$ 当且仅当全部这些实验的结果分布相同。任意连续的允许酉操作仍合成为某个 $V\in U(2)$，故该定义也包含所有有限酉操作词后再读取 $Z$ 的任务。则
$$
\rho\sim\sigma
\quad\Longleftrightarrow\quad
(r_x,r_y,r_z)_\rho=(r_x,r_y,r_z)_\sigma
\quad\Longleftrightarrow\quad
\rho=\sigma\qquad(\rho,\sigma\in\mathcal D_0).
\tag{TM.65}
$$

同态显然给出相同响应。反向只需式(TM.64)的三项实验：二值 $Z$ 分布确定其期望，三个期望确定 Bloch 三元组，再由式(TM.61)恢复密度矩阵。若两态不同，至少一个坐标不同，对应实验便将它们区分。因此，没有两个不同的 $\mathcal D_0$ 态能在保留全部所声明行为的同时被永久合并。

更具体地，若另一摘要 $s:\mathcal D_0\to B$ 能够恢复所有这些实验的分布，记其中三项期望的恢复函数为 $g_x,g_y,g_z$，则
$$
(r_x,r_y,r_z)(\rho)=\bigl(g_x(s(\rho)),g_y(s(\rho)),g_z(s(\rho))\bigr).
\tag{TM.66}
$$

所以每份这样的任务充分摘要都能恢复 Bloch 表示。这是关于观察核与行为商的最小性；它不声称三个任意实数容器在集合论上不能重编码成更少容器，也不声称存在有限比特精确存储全部状态的方法。若限制允许酉操作、测量权限或精度，行为等价关系可能变粗，需要按新任务重新计算。

本节由此把“体／边”具体化为一个可以检验的缺口和补全：同一零能量整体中的部分联合关系，在指定当前边界上完全隐藏；允许的守能联合操作可将其运输到未来局部读数；补入足够的相干坐标后，表示支持该操作族的精确更新。守恒约束决定合法活动的层，动态充分性则决定边界是否记录了这一层内部会被后续操作使用的区别。两者不能相互替代。

仓内已有更一般的预测充分性接口。固定快照 `237012b49d0d4729a86f7e9dd252d94df1de8dd0` 的 `D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean:46`，`all_future_statistics_sufficiency` 在去迹 Hermitian 实向量空间中证明：预测投影相同，当且仅当全部指定读数经给定 Heisenberg 线性算子任意有限次迭代后的内积相同。其量词涉及一个给定算子的迭代；本节任意 $U(2)$ 操作族的具体充分性另由式(TM.64)的三项实验核对，不把范围不同的接口自动混同。

历史候选快照 `29c5504b11a1685c220e0ad2a9705a987fc6cff4`中，`docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md:2117` 的第13.7节已经给出受限态族 $\rho_{a,b,c}=\tfrac14(I+aX\otimes I+bY\otimes Z+cZ\otimes Z)$ 的真实 CPTP 编码、解码与动态交织：通过指定 CNOT 将一个逻辑量子位与固定混合因子编码为两个物理量子位，再经逆酉与偏迹恢复逻辑态。该族不同于本节的零能量支撑族，来源状态也须按这个候选快照识别；它已经承担“受限态族可有精确量子充分表示”的既有机制，本节不据此另开重复的普遍压缩前沿。

另在固定快照 `32cb094685048f37f719e20bcf313657a553135b`，`D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean:81` 的 `dynamic_closure_is_least` 给出指定总操作族下保留原观察的最小动态闭包接口；`D5/S3/Quantum/Decoherence/CanonicalRecordAccessRecovery.lean:42` 的 `reduced_irreversibility_is_canonical_record_access_defect` 处理联合记录保留相干区别、迹掉记录后的不可恢复性及重新访问记录后的恢复。后者本身没有断言上述 Hamiltonian 的守能性质。本节定位为这些已有机制的有限矩阵应用说明与接口连接，未新增 Lean 核验，不将既有定理的应用、本节的显式分解和综合包装成已形式化的新定理或原创性结论。

### 1.3 Bloch 球纤维的精确修复、线性常数与平方根边界

A卷第3.6节的有限多面体结构不能仅凭“状态集有限维、紧且凸”替换。量子位状态集给出一份可以完全计算的比较：固定一个占据概率目标，求完整态到该目标纤维的最近半迹距离。目标位于内部时有锐线性常数；目标到达纯态端点时，最优误差指数变为 $1/2$。这个变化来自球面与目标平面的相交和相切，普通欧氏球也有相同现象。

#### 1.3.1 实际密度态及零能量子空间中的实现

**定义 1.8（密度态及零能量实现）。** 在有序基 $|0\rangle,|1\rangle$ 上，写全部量子位密度态为
$$
R(p,c)=\begin{pmatrix}p&c\\\overline c&1-p\end{pmatrix},\qquad
0\le p\le1,\quad |c|\le r(p),\qquad r(p)=\sqrt{p(1-p)}.
\tag{TM.83}
$$

矩阵 Hermitian、迹为一；两个对角元非负以及行列式 $p(1-p)-|c|^2\ge0$ 恰好保证正半定性。因此这里使用的全是实际密度态，且式(TM.83)穷尽该二维空间上的密度态。等号 $|c|=r(p)$ 等价于行列式为零，即该态为秩一纯态。

此模型直接嵌入B卷第1.2节的零能量子空间。令 $V|0\rangle=|01\rangle$、$V|1\rangle=|10\rangle$，则 $V^\dagger V=I$，并有
$$
\widehat R(p,c)=VR(p,c)V^\dagger
=\begin{pmatrix}
0&0&0&0\\
0&p&c&0\\
0&\overline c&1-p&0\\
0&0&0&0
\end{pmatrix},\qquad
H\widehat R(p,c)=0,\qquad
H=Z\otimes I+I\otimes Z.
\tag{TM.84}
$$

全部嵌入态的完整能量分布仍集中于零。两嵌入态之差只比原二阶差矩阵增加两个零本征值，因此其半迹距离完全相同。占据读数 $p$ 对应 $|01\rangle$ 的概率，也等于第一系统计算基结果为零的概率；在逻辑量子位表示中，它是 $|0\rangle\langle0|$ 的 Born 期望。

固定目标 $p_0\in[0,1]$，令
$$
F_{p_0}=\{R(p_0,d):|d|\le r_0\},\qquad
r_0=r(p_0),\qquad
\delta=|p-p_0|,\qquad
D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1.
\tag{TM.85}
$$

$F_{p_0}$ 对每个目标都非空且紧。$\delta$ 是该二值占据测量的两个输出律之间的总变差；距离则考察完整密度态。

#### 1.3.2 精确纤维距离与唯一最近点

**命题 1.9（精确纤维投影）。** 对任意合法目标相干参数 $d$，差矩阵为
$$
R(p,c)-R(p_0,d)=
\begin{pmatrix}p-p_0&c-d\\\overline c-\overline d&-(p-p_0)\end{pmatrix},\qquad
\operatorname{spec}\bigl(R(p,c)-R(p_0,d)\bigr)
=\left\{\pm\sqrt{(p-p_0)^2+|c-d|^2}\right\}.
\tag{TM.86}
$$

这是由迹为零和特征多项式 $\lambda^2-(p-p_0)^2-|c-d|^2$ 直接得到的。Hermitian 矩阵的迹范数等于本征值绝对值之和，故半迹距离就是式(TM.86)根号中的数。第一项与 $d$ 无关，最小化因此化为复平面中到闭圆盘 $|d|\le r_0$ 的欧氏投影。

若 $|c|\le r_0$，唯一最近点是 $d=c$。若 $|c|>r_0$，反三角不等式给 $|c-d|\ge|c|-r_0$，同相位的圆周点达到下界；等号要求 $|d|=r_0$ 且与 $c$ 同向，所以仍唯一。于是
$$
d_*(p,c;p_0)=
\begin{cases}
c,&|c|\le r_0,\\
r_0c/|c|,&|c|>r_0,
\end{cases}
\qquad
R_*=R(p_0,d_*).
\tag{TM.87}
$$

第二分支自动具有 $c\ne0$，包含 $r_0=0$ 时的唯一值 $d_*=0$，没有除零问题。完整精确距离为
$$
\boxed{
\operatorname{dist}_D(R(p,c),F_{p_0})
=\min_{\sigma\in F_{p_0}}D(R(p,c),\sigma)
=\sqrt{(p-p_0)^2+(|c|-r_0)_+^2}.
}
\tag{TM.88}
$$

因此，相干仍落在目标圆盘内时，只需改变占据概率；相干超过目标允许半径时，还必须同时缩小其模长。这两份改变量在半迹距离的平方中相加。

#### 1.3.3 固定内点的锐线性常数

**命题 1.10（内点锐线性常数）。** 对固定 $0<p_0<1$，定义 $C(p_0)$ 为使 $\operatorname{dist}_D(R(p,c),F_{p_0})\le C(p_0)|p-p_0|$ 对全部合法 $R(p,c)$ 成立的最小常数。在开区间上，
$$
r'(p)=\frac{1-2p}{2r(p)},\qquad
r''(p)=-\frac1{4r(p)^3}<0,\qquad
r(p)-r_0\le r'(p_0)(p-p_0)\le|r'(p_0)|\,\delta.
\tag{TM.89}
$$

前两式由求导及 $4p(1-p)+(1-2p)^2=1$ 得到；最后的不等式是凹函数的切线上界，连续性将它延伸到 $p=0,1$。右端非负，故取正部并使用 $|c|\le r(p)$，得 $(|c|-r_0)_+\le|r'(p_0)|\delta$。代入式(TM.88)给
$$
\operatorname{dist}_D(R(p,c),F_{p_0})
\le\sqrt{1+r'(p_0)^2}\,\delta
=\frac{\delta}{2\sqrt{p_0(1-p_0)}}.
\tag{TM.90}
$$

为证明该常数最小，先设 $p_0\ne1/2$，令 $s=\operatorname{sgn}(1/2-p_0)$，取 $p_t=p_0+st$，其中 $t>0$ 足够小，使 $p_t$ 位于 $p_0$ 与 $1/2$ 之间。取纯态相干 $c_t=r(p_t)>r_0$，于是
$$
\frac{\operatorname{dist}_D(R(p_t,r(p_t)),F_{p_0})}{|p_t-p_0|}
=\sqrt{1+\left(\frac{r(p_t)-r_0}{t}\right)^2}
\longrightarrow\sqrt{1+r'(p_0)^2}
=\frac1{2\sqrt{p_0(1-p_0)}}.
\tag{TM.91}
$$

任何更小常数都会在充分小的 $t$ 处失败。由于 $r$ 严格凹，$p\ne p_0$ 时切线上界严格：若 $r(p)>r_0$，式(TM.90)的比值严格小于所给常数；若 $r(p)\le r_0$，该比值为一，也严格小于非中央目标的常数。因此，非中央内点的锐常数由切线极限给出，不由任何非零有限扰动达到。$p=p_0$ 时距离与剩余量都为零，不作为比值的达到点。

当 $p_0=1/2$，目标半径 $r_0=1/2$ 已是全局最大值，所有合法相干均在该圆盘内，式(TM.88)对所有态直接给 $\operatorname{dist}_D(R,F_{1/2})=|p-1/2|$。取任意 $p\ne1/2$ 可知常数一不可再小。合并得到
$$
\boxed{C(p_0)=\frac1{2\sqrt{p_0(1-p_0)}}\quad(0<p_0<1).}
\qquad
\boxed{
\sup_{p_0\in[a,1-a]}C(p_0)
=\frac1{2\sqrt{a(1-a)}}\quad(0<a\le1/2).
}
\tag{TM.92}
$$

第二式给整个紧内区间的最小统一常数：乘积 $p_0(1-p_0)$ 在该区间的最小值为 $a(1-a)$，且固定端点目标的切线实例已经迫使这一数值。随着目标趋近零，$C(p_0)\sim1/(2\sqrt{p_0})$；趋近一时对称。保持内部正裕度与允许裕度消失是不同的量词范围。

#### 1.3.4 纯态端点的锐平方根尺度

**命题 1.11（端点锐平方根尺度）。** 当 $p_0=0$，正半定性迫使目标相干为零，$F_0$ 只有 $|1\rangle\langle1|$。由式(TM.88)与合法性，
$$
\operatorname{dist}_D(R(p,c),F_0)^2
=p^2+|c|^2\le p^2+p(1-p)=p,
\qquad
\operatorname{dist}_D(R(p,r(p)),F_0)=\sqrt p.
\tag{TM.93}
$$

纯态输入达到上界，因此平方根的常数一是最小的。对任意 $\beta>1/2$，同一纯态族还给
$$
\frac{\operatorname{dist}_D(R(p,r(p)),F_0)}{|p-0|^\beta}
=p^{1/2-\beta}\longrightarrow\infty\qquad(p\downarrow0).
\tag{TM.94}
$$

故不存在任何有限线性常数，也不存在指数大于 $1/2$ 的局部统一 Hölder 界。目标 $p_0=1$ 的结论完全对称：唯一目标为 $|0\rangle\langle0|$，距离平方为 $(1-p)^2+|c|^2\le1-p$，纯态达到 $\sqrt{1-p}$。在B卷第1.2节的嵌入中，这两个逻辑纯态分别对应 $|10\rangle$ 与 $|01\rangle$，始终属于同一个零能量层。

#### 1.3.5 同时覆盖全部目标的锐平方根模

**命题 1.12（全目标锐模）。** 内点线性常数虽在端点附近发散，全部目标仍共享一个常数一的平方根模。先由 $|c|\le r(p)$ 和式(TM.88)得
$$
\operatorname{dist}_D(R(p,c),F_{p_0})^2
\le\delta^2+\bigl(r(p)-r(p_0)\bigr)^2.
\tag{TM.95}
$$

若 $|c|\le r(p_0)$，左侧就是 $\delta^2$；否则 $r(p)>r(p_0)$，正部之差不超过 $r(p)-r(p_0)$，所以这一步涵盖全部情形。

令 $u=\max(p,p_0)$、$v=\min(p,p_0)$，则 $0\le v\le u\le1$、$\delta=u-v$。展开平方给出恒等式
$$
\begin{aligned}
\delta-\left[\delta^2+(r(u)-r(v))^2\right]
&=2\left(\sqrt{uv(1-u)(1-v)}-v(1-u)\right)\ge0,\\
uv(1-u)(1-v)-v^2(1-u)^2
&=v(1-u)(u-v)\ge0.
\end{aligned}
\tag{TM.96}
$$

第二行比较了第一行根号内的数与 $[v(1-u)]^2$；两者非负，故平方根的单调性证明第一行的不等式，包括 $u=1$ 或 $v=0$ 的端点。结合式(TM.95)得到
$$
\boxed{
\operatorname{dist}_D(R(p,c),F_{p_0})
\le\sqrt{|p-p_0|}
\quad\forall p,p_0\in[0,1],\quad |c|\le\sqrt{p(1-p)}.
}
\tag{TM.97}
$$

式(TM.93)、(TM.94)已经说明：这一覆盖全部目标的界，其常数一与最大正 Hölder 指数 $1/2$ 都不能改进。固定紧内区间的线性界与全区间的平方根界同时成立，各自描述不同的统一范围。

#### 1.3.6 对角子族、球面切触与恢复权限

**命题 1.13（对角子族与球面边界）。** 若输入限制为对角态 $c=0$，则任意目标圆盘都容纳该相干值，因而
$$
\operatorname{dist}_D(R(p,0),F_{p_0})
=D(R(p,0),R(p_0,0))
=|p-p_0|\qquad(p,p_0\in[0,1]).
\tag{TM.98}
$$

即使把目标也限制为对角态，结论仍不变，最佳线性常数始终为一。端点的平方根行为由合法相干方向参与完整距离时出现，不能把它归因于占据概率这个标量本身。

在 Bloch 坐标 $\mathbf b=(2\operatorname{Re}c,-2\operatorname{Im}c,2p-1)$ 下，合法态就是闭单位球；式(TM.86)也给 $D(\rho,\sigma)=\tfrac12\|\mathbf b_\rho-\mathbf b_\sigma\|_2$。固定 $p_0$ 是与球相交的水平平面。内部目标给非退化圆盘，端点目标的平面与球相切，邻近球面的横向位移可以是纵向剩余量的平方根。故式(TM.93)也是普通有限维欧氏凸几何中的切触例子；不需要将其解释为量子独有的效应。

这精确限定了A卷第3.6节的迁移：有限维、紧性、凸性足以保证这里的最小距离达到，却不保证线性误差界。经典档案单纯形和固定线性读数的 Hoffman 供应依赖多面体结构；当前完整量子位态集为具有曲面边界的球，固定端点目标已经反驳无条件的线性外推。端点仍有式(TM.97)的连续修复模，并非完全失去稳定性。

对非退化目标 $0<p_0<1$，唯一最近点一般依赖完整相干 $c$。取输入 $p=p_0$、相干分别为 $0$ 与 $r_0/2$，两态都已在目标纤维中，故各自最近点就是自身；相同占据读数不能单独确定修复态或识别该纤维内的未知输入。端点目标的纤维仅有一个态，最近修复恒为该态，与输入相干无关；这个例外也不承担恢复原输入的任务。上述优化没有给出将所有输入送到最近点的 CPTP 通道；圆盘投影的数学定义不自动授予物理实施权限。实际取得相干仍须满足B卷第1.2节所声明的联合操作、测量、共同准备与记录访问条件。精确 Born 期望是模型坐标，有限实验读数及其统计误差须另外处理。

#### 1.3.7 已有供应与本节结论的归属

Bloch 球与迹距离的成熟来源可取 C. Carmeli、T. Heinosaari、J. Schultz、A. Toigo，*Probing quantum state space: does one have to learn everything to learn something?*，[arXiv:1611.04388v2](https://arxiv.org/pdf/1611.04388v2)。PDF第7页第3.2节写 $\rho_{\mathbf r}=\tfrac12(I+\mathbf r\cdot\boldsymbol\sigma)$、$\|\mathbf r\|_2\le1$；第11页 Proposition 3.6 后的实例明确给出 $\|\rho_{\mathbf a}-\rho_{\mathbf r}\|_1=\|\mathbf a-\mathbf r\|_2$。该处称作 trace distance 的量采用完整迹范数，本文采用半迹距离，故B卷第1.3.6节的 Bloch 欧氏距离须乘 $1/2$。上右矩阵元为 $c$ 时坐标为 $(2\operatorname{Re}c,-2\operatorname{Im}c,2p-1)$，与本文 Pauli $Y$ 的约定一致。这个来源承担球几何和范数归一化，不直接承担固定占据圆盘的精确投影或锐残差常数。

固定快照 `237012b49d0d4729a86f7e9dd252d94df1de8dd0` 的 `docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY.md:6537`，定理31.8已使用纯参考态的平方根界，并在第6567、6589行明确归属 Fuchs–van de Graaf 不等式。其标准形式为 $D(\rho,\sigma)\le\sqrt{1-F(\rho,\sigma)^2}$，根保真度约定为 $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$。本节取 $\sigma=|1\rangle\langle1|$ 时，$F^2=\langle1|R(p,c)|1\rangle=1-p$，直接得到式(TM.93)的平方根上界。成熟来源是 C. A. Fuchs、J. van de Graaf，*Cryptographic distinguishability measures for quantum-mechanical states*，IEEE Transactions on Information Theory 45（1999），1216–1227，[arXiv:quant-ph/9712042](https://arxiv.org/abs/quant-ph/9712042)。本节不将该界另立为新的一般结果。

同一快照的 `D5/S3/Quantum/Foundation/FiniteTraceDistance.lean:264` 与 `:455` 给出实际迹范数和半迹距离的定义，`:497` 给出其同型 CPTP 后处理收缩供应。它们确定所用距离及相应合法后处理的已有接口，并未因此自动包含本节的圆盘纤维闭式和精确内点常数。式(TM.83)—(TM.98)按上述直接矩阵与球面几何计算呈现，不宣称已取得新增形式化结论或原创性确认。

一般线性矩阵不等式的 Hölder 误差界可通过 Stefan Sremac、Hugo J. Woerdeman、Henry Wolkowicz，*Error Bounds and Singularity Degree in Semidefinite Programming*，[arXiv:1908.04357v1](https://arxiv.org/pdf/1908.04357v1)，准确接入本例。该文 PDF第2页式(1.1)—(1.2)区分前向与后向误差，第3页规定实对称矩阵空间及 Frobenius 范数，第4页式(2.2)固定谱面 $F=\{X\succeq0:\mathcal A(X)=b\}$。第5页第2.2节将奇异度 $\operatorname{sd}(F)$ 定义为面约化所需最少步数，并说明 $\operatorname{sd}(F)=0$ 当且仅当存在严格正定可行点。同页 Fact 2.2 对非空谱面和有界矩阵族给出：当 $F\ne\{0\}$ 时，前向误差是后向误差的 $2^{-\operatorname{sd}(F)}$ 次阶；零谱面单列为线性界。以该文记号写，
$$
\varepsilon_f(X,F)=\operatorname{dist}_{\mathrm F}(X,F),\qquad
\varepsilon_b(X,F)=\operatorname{dist}_{\mathrm F}(X,L)
 +\operatorname{dist}_{\mathrm F}(X,\mathbb S_+^n),\qquad
\varepsilon_f=O\!\left(\varepsilon_b^{\,2^{-\operatorname{sd}(F)}}\right)
\quad(F\ne\{0\}),
$$
其中 $L=\{X:\mathcal A(X)=b\}$ 固定，渐近界用于所声明的有界族及后向误差趋零范围，不据此给任意变化切面的统一常数。

Fact 2.2 明确将证明归给 Jos F. Sturm，*Error Bounds for Linear Matrix Inequalities*，SIAM Journal on Optimization 10(4)（2000），1228–1248，[doi:10.1137/S1052623498338606](https://doi.org/10.1137/S1052623498338606)，Theorem 3.3。这里的定理供应来自 SWW 的明确重述；Sturm 原定理正文未读到，不能声称独立核实其原始全部量词与证明。SWW 对零谱面的奇异度采用一，而其记载的 Sturm 约定为零，所以将该例外单列；本文端点谱面是 $\{E_{22}\}$ 或 $\{E_{11}\}$，均非零谱面，不需要借用该例外。

**本切面的奇异度可以直接核对。** 暂限实相干，令 $F^{\mathbb R}_{p_0}=\{X\in\mathbb S_+^2:\operatorname{tr}X=1,X_{11}=p_0\}$，$\mathcal A(X)=(\operatorname{tr}X,X_{11})$、$b=(1,p_0)$，因而 $\mathcal A^*y=y_1I+y_2E_{11}$。当 $0<p_0<1$，$\operatorname{diag}(p_0,1-p_0)\succ0$ 给严格可行点，奇异度为零。当 $p_0=0$，取 $y=(0,1)$，则 $\mathcal A^*y=E_{11}\succeq0$ 且 $y^{\mathsf T}b=0$；正性使所有可行矩阵的第一行列为零，暴露到 $e_2$ 支撑面后，可行点是该面中的正标量一。当 $p_0=1$，取 $y=(1,-1)$，相应暴露矩阵是 $E_{22}$、仍有 $y^{\mathsf T}b=0$，约化到 $e_1$ 支撑面后同样严格可行。两个端点在原锥中都无正定可行点，所以都恰需一次面约化，即奇异度为一。

对合法实密度输入 $\rho=R(p,c)$，PSD 剩余量为零。到仿射切面 $L_{p_0}$ 的 Frobenius 最近点只将两个对角元调整 $p_0-p$ 与 $p-p_0$，保留非对角元，所以 $\varepsilon_b=\sqrt2|p-p_0|$。任意两个迹为一的实对称 $2\times2$ 矩阵之差有特征值 $\pm s$，其 Frobenius 范数为 $\sqrt2|s|$、半迹距离为 $|s|$，故 $\varepsilon_f=\sqrt2\operatorname{dist}_D(\rho,F^{\mathbb R}_{p_0})$。这将一般理论的阶数精确匹配到本切面的内部线性与端点平方根。端点实纯态曲线另给 $\varepsilon_f=\sqrt{2p}$、$\varepsilon_b=\sqrt2p$，已经足以反驳更大的局部 Hölder 指数。

SWW 的一般阶估计不直接给本文的唯一最近点、全局精确常数 $1/(2\sqrt{p_0(1-p_0)})$、端点系数一或覆盖全部目标的锐界，也不直接供应复 Hermitian 版本。含复相干的式(TM.83)—(TM.98)及其精确常数由本节此前完整的 $2\times2$ 矩阵与圆盘计算承担；引用成熟阶估计只是说明该有限实例怎样接入面约化结构。精确常数的全球文献优先权没有据此确定。

#### 1.3.8 唯一最近点不保证合法通道

**命题 1.14（最近点修复的通道障碍）。** 记式(TM.87)的唯一最近点映射为 $N_{p_0}(R(p,c))=R(p_0,d_*)$。对每个内部目标，它都没有面向全部未知输入态的单一 CPTP 实现：
$$
0<p_0<1
\quad\Longrightarrow\quad
\nexists\,\Phi:M_2(\mathbb C)\to M_2(\mathbb C)\ \text{为 CPTP},\quad
\Phi(\rho)=N_{p_0}(\rho)\ \text{对全部密度态 }\rho\text{ 成立}.
\tag{TM.99}
$$

端点 $p_0=0,1$ 则存在常值制备通道。以下分别证明这些范围，并将它们与单纯的逐态最小化区分。

**内部目标的完全正性反证。** 假设存在式(TM.99)所排除的 $\Phi$，记 $E_{ij}=|i\rangle\langle j|$、$D_{p_0}=\operatorname{diag}(p_0,1-p_0)$。两个计算基纯态的相干均为零，其最近目标态相同，因此
$$
\Phi(E_{00})=\Phi(E_{11})=D_{p_0}.
\tag{TM.100}
$$

因为 $r_0=\sqrt{p_0(1-p_0)}>0$，可取 $0<\varepsilon\le\min(r_0,1/2)$。以下四态都合法，且其相干位于目标圆盘内，所以最近点保留相干：
$$
\begin{aligned}
R(1/2,\pm\varepsilon)&=I/2\pm\varepsilon X,
&N_{p_0}(R(1/2,\pm\varepsilon))&=D_{p_0}\pm\varepsilon X,\\
R(1/2,\pm i\varepsilon)&=I/2\mp\varepsilon Y,
&N_{p_0}(R(1/2,\pm i\varepsilon))&=D_{p_0}\mp\varepsilon Y.
\end{aligned}
\tag{TM.101}
$$

第二行的符号使用B卷第1.2节固定的 $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$。分别将两行中的正负输入相减，使用假设中 $\Phi$ 的线性性，得到
$$
\Phi(X)=X,\qquad \Phi(Y)=Y,\qquad
\Phi(E_{01})=\Phi((X+iY)/2)=E_{01},\qquad
\Phi(E_{10})=E_{10}.
\tag{TM.102}
$$

这里没有假定最近点映射本身线性；这些等式是某个单一线性通道若能在所列实际输入态上完成任务，就必须满足的条件。式(TM.100)、(TM.102)已经确定它在全部矩阵单位上的作用。

取输入参考指标在前、输出指标在后的张量次序，并按 $00,01,10,11$ 排列基。由上述四个矩阵单位的像，未归一化 Choi 矩阵为
$$
J_\Phi=\sum_{i,j=0}^1|i\rangle\langle j|\otimes\Phi(E_{ij})
=\begin{pmatrix}
p_0&0&0&1\\
0&1-p_0&0&0\\
0&0&p_0&0\\
1&0&0&1-p_0
\end{pmatrix}.
\tag{TM.103}
$$

它的 $00,11$ 主块已经不是正半定；同一事实也有一个不依赖 $p_0$ 的负方向：
$$
\det\begin{pmatrix}p_0&1\\1&1-p_0\end{pmatrix}
=p_0(1-p_0)-1<0,\qquad
v=\frac{|00\rangle-|11\rangle}{\sqrt2},\qquad
v^\dagger J_\Phi v=-\tfrac12.
\tag{TM.104}
$$

完全正性要求通道与任意外部参考的恒等操作拼接后仍保持正性。具体取 $|\Omega\rangle=|00\rangle+|11\rangle$，有 $J_\Phi=(\operatorname{id}_2\otimes\Phi)(|\Omega\rangle\langle\Omega|)$，所以完全正性要求 $J_\Phi\succeq0$，与式(TM.104)矛盾。若使用归一化的实际 Bell 输入，输出是 $J_\Phi/2$，在同一单位向量 $v$ 上的期望为 $-1/4$，同样违反正性。证明只使用完全正性定义的必要方向，不需要任何“正 Choi 矩阵推出通道”的逆向判据，也不构成新的 Choi 定理。

**中央目标的正性与非完全正性。** 当 $p_0=1/2$ 时，全部合法相干都能保留，最近点映射有唯一的线性延拓
$$
\Lambda(A)=\frac{\operatorname{Tr}A}{2}I+A_{01}E_{01}+A_{10}E_{10},\qquad
\Lambda:\ (x,y,z)\longmapsto(x,y,0)\quad\text{在 Bloch 坐标上}.
\tag{TM.105}
$$

该变换将闭单位球送入自身，所以把每个密度态送到密度态；任意非零正半定矩阵都是其迹与某个密度态之积，线性性因此给出整个正锥上的正性。它也保持迹。式(TM.104)仍否定其完全正性。这展示了外部参考的实际作用：单个系统的输出合法性不足以保证它能代表原系统参与任意联合实验。

**非中央目标的非仿射见证。** 当 $p_0\ne1/2$ 且仍在内部，$0<r_0<1/2$。取两个实际输入 $\rho_a=R(1/2,0)$、$\rho_b=R(1/2,1/2)$，由圆盘投影公式有
$$
\begin{aligned}
\tfrac12\bigl(N_{p_0}(\rho_a)+N_{p_0}(\rho_b)\bigr)
&=R(p_0,r_0/2),\\
N_{p_0}\bigl((\rho_a+\rho_b)/2\bigr)
&=R\bigl(p_0,\min(1/4,r_0)\bigr),\\
\min(1/4,r_0)&>r_0/2\qquad(0<r_0<1/2).
\end{aligned}
\tag{TM.106}
$$

最后一行分 $r_0\le1/4$ 与 $r_0>1/4$ 两种情形立即成立。因此这份最近点映射连凸混合都不保持，不能由单一仿射操作实现。这个独立见证描述径向截断的性质；前面的完全正性反证始终只对所假设的 $\Phi$ 使用线性性，没有偷换前提。

**端点的常值准备及其代价。** 若 $p_0=0$，目标为 $|1\rangle\langle1|$；若 $p_0=1$，目标为 $|0\rangle\langle0|$。分别令 $b=1,0$，定义
$$
K_0=|b\rangle\langle0|,\qquad K_1=|b\rangle\langle1|,\qquad
\sum_{j=0}^1K_j^\dagger K_j=I,\qquad
\Phi_b(A)=\sum_{j=0}^1K_jAK_j^\dagger
=\operatorname{Tr}(A)|b\rangle\langle b|.
\tag{TM.107}
$$

这给出明确的 CPTP 常值制备，在全部输入态上实现端点最近点。内部证明所需的正 $\varepsilon\le r_0$ 在端点不存在，所以两种结论相容。常值准备会丢弃输入区别；目标态制备、环境控制和重置等资源须按实际协议计费，通道的数学合法性不使这些资源免费。

**零能量嵌入不解除内部障碍。** 使用式(TM.84)的等距 $V$，编码 $\mathcal E(A)=VAV^\dagger$ 为 CPTP。取 $P_\perp=I-VV^\dagger=|00\rangle\langle00|+|11\rangle\langle11|$，定义全四维输入上合法的解码
$$
\mathcal D(B)=V^\dagger BV+\operatorname{Tr}(P_\perp B)|0\rangle\langle0|,
\qquad\mathcal D\mathcal E=\operatorname{id},\qquad
\mathcal D:\ M_4(\mathbb C)\longrightarrow M_2(\mathbb C).
\tag{TM.108}
$$

其 Kraus 算子可取 $V^\dagger,|0\rangle\langle00|,|0\rangle\langle11|$；各伴随乘积之和为 $VV^\dagger+P_\perp=I_4$，所以解码完全正且保迹。若存在四维 CPTP 映射 $\Psi$，对全部逻辑密度态 $\rho$ 都满足 $\Psi(\mathcal E\rho)=\mathcal E(N_{p_0}\rho)$，则 $\Phi=\mathcal D\Psi\mathcal E$ 是被式(TM.99)排除的逻辑 CPTP 实现。因此，把全部输入放进同一个简并零能量块，也不会产生这个内部目标的单一通道。该反证甚至不需要额外要求 $\Psi$ 守能。

这一结论的量词是：对所有单份未知输入，以同一确定 CPTP 操作精确实现该最近点规则。数学模型中的条件化、已知输入后选择不同制备、带成功旗标的条件实验，以及多份样本的统计估计，具有另外的知识、样本、成功概率或误差条件，不能用本反例一并否定，也不能省略这些条件后声称已经取得上述单一通道。这里反驳的是“唯一最近点自动可实施”这一具体推断，所用正性、Kraus 表示和外部参考约束均归成熟量子通道结构。

## 2. 实际效果、共同关系矩与能量关系

### 2.1 能量相容工具、独立参考与同源制备的观察商

B卷第1.2节的简并零能量块允许内部关系经合法操作进入边界，B卷第1.3节又区分了逐态的几何最优解与对全部未知输入可执行的同一个通道。本节把这两种边界接到一个明确的操作合同：给定能量约束以后，哪些区别可由实际工具读取；加入参考或新增来自同一制备源的样本以后，旧观察商是否仍然充分。单份系统、独立不变参考和共同相位的两份样本使用不同的联合来源，不能只凭单份边缘相同而彼此替代。

以下全部 Hilbert 空间有限维，密度态为正半定、迹为一的矩阵；效果为 $0\le F\le I$，其概率为 $\operatorname{Tr}(F\rho)$。除明确说明外，效果族只规定末端概率，不自动规定测量后的分支状态。精确概率是模型层读数；有限样本估计、控制精度、时间和制备成本不由这些代数条件自动给出。

#### 2.1.1 任意有限 Hamiltonian 的完整相容观察商

**命题 2.1（完整相容观察商）。** 令 $\dim\mathcal H=d\ge1$，$H=H^\dagger$，其不同特征值组成有限集合 $\mathcal E$。用 $\Pi_E$ 表示完整的特征空间投影，包括简并空间，定义
$$
H=\sum_{E\in\mathcal E}E\Pi_E,\qquad
P_H(A)=\sum_{E\in\mathcal E}\Pi_EA\Pi_E,\qquad
\mathcal C_H=\{A=A^\dagger:[A,H]=0\}.
\tag{TM.109}
$$

$\mathcal C_H$ 是 Hermitian 矩阵的实线性子空间。由 $\Pi_E[H,A]\Pi_{E'}=(E-E')\Pi_EA\Pi_{E'}$ 可知，$[A,H]=0$ 当且仅当 $A$ 在不同能量块之间为零。于是 $P_H$ 在 Hermitian 实空间上恰是投向 $\mathcal C_H$ 的正交投影，这里的实内积为 $\langle A,B\rangle=\operatorname{Tr}(AB)$。具体地，迹循环性和投影正交性给出
$$
\operatorname{Tr}(B P_H(A))=\operatorname{Tr}(P_H(B)A),\qquad
P_H^2=P_H,\qquad
\operatorname{Tr}P_H(A)=\operatorname{Tr}A.
\tag{TM.110}
$$

取 Kraus 算子为 $\Pi_E$，由于 $\sum_E\Pi_E^\dagger\Pi_E=I$，$P_H$ 还是 CPTP 通道。这里只说明这份数学通道合法；特定装置能否实施它仍取决于所声明的工具。

若全部与 $H$ 交换的效果均可调用，则对任意两份密度态有精确等价：
$$
\boxed{
P_H(\rho)=P_H(\sigma)
\quad\Longleftrightarrow\quad
\operatorname{Tr}(F\rho)=\operatorname{Tr}(F\sigma)
\quad\forall F:\ 0\le F\le I,\ [F,H]=0.
}
\tag{TM.111}
$$

**证明。** 正向使用式(TM.110)及 $P_H(F)=F$。反向令 $D=P_H(\rho-\sigma)$。它是迹为零的 Hermitian 块对角矩阵。如果 $D\ne0$，其特征值不可能全非正或全非负，否则迹为零会迫使全部特征值为零。取 $Q_+$ 为 $D$ 的严格正特征空间投影。$D$ 与 $H$ 交换，故 $D$ 的谱投影也与 $H$ 交换；于是 $Q_+$ 是允许效果，而且 $\operatorname{Tr}(Q_+(\rho-\sigma))=\operatorname{Tr}(Q_+D)>0$，与全部效果概率相同矛盾。故 $D=0$。证明覆盖退化的 $H$；若 $H$ 是纯数量矩阵，则 $P_H$ 是恒等映射，全部效果可用时没有非平凡观察纤维。

同一结论也可从效果的实张成看出：对任意 $A\in\mathcal C_H$，取 $\alpha>\|A\|_{\mathrm{op}}$，$F=(I+A/\alpha)/2$ 是相容效果，且 $A=\alpha(2F-I)$。因此完整相容效果保留每个简并能量块内的全部矩阵坐标，并非仅保留能量测量的概率。

若所有可用末端效果只限为 $F=f(H)$，其中在谱上 $0\le f(E)\le1$，则恰好只需
$$
q_{\rm en}(\rho)=\bigl(\operatorname{Tr}(\Pi_E\rho)\bigr)_{E\in\mathcal E},\qquad
\operatorname{Tr}(f(H)\rho)=\sum_E f(E)q_{{\rm en},E}(\rho).
\tag{TM.112}
$$

这份能量概率向量对该效果族是精确充分的；取 $f=\mathbf1_{\{E\}}$ 也证明其必要性。若进一步允许的操作仅为 $[U,H]=0$ 的酉，则 $U$ 与每个 $\Pi_E$ 以及每个 $f(H)$ 交换，能量概率在操作后不变，所以这个受限接口对全部此类有限操作词仍然充分。当能谱非简并时，完整块 pinching 与能量概率向量保留相同的可区分信息；一般简并块中则有额外内部方向，不能在要求完整相容观察充分性的同时将其删去。

对完整 pinching，有更强的动态交织：
$$
[U,H]=0
\quad\Longrightarrow\quad
P_H(U\rho U^\dagger)=U P_H(\rho)U^\dagger.
\tag{TM.113}
$$

证明是将 $U\Pi_E=\Pi_EU$ 逐项代入式(TM.109)。所以 $q(\rho)=P_H(\rho)$ 的像上存在精确更新 $q\mapsto UqU^\dagger$。它给出任务商和合法后续更新，不给出从 $P_H(\rho)$ 恢复未知原态 $\rho$ 的逆通道；不同能量块之间的相干仍可能已经合并。

一个直接的简并见证是B卷第1.2节所用 $H=Z\otimes I+I\otimes Z$ 的零能量块。令
$$
|\psi_\pm\rangle=(|01\rangle\pm|10\rangle)/\sqrt2,\qquad
\rho_\pm=|\psi_\pm\rangle\langle\psi_\pm|,\qquad
F_+=|\psi_+\rangle\langle\psi_+|.
\tag{TM.114}
$$

两态的能量读数都以概率一为零，但 $[F_+,H]=0$ 且 $\operatorname{Tr}(F_+\rho_+)=1$、$\operatorname{Tr}(F_+\rho_-)=0$。这说明完整相容效果族能区分更多状态；它不反驳仅 $f(H)$ 效果族的充分性，因为 $F_+$ 在二维零能量块上不是数量矩阵，故不属于该较小效果族。

任意有限 $H$ 的谱差不必有共同周期。若用时间平均解释 $P_H$，可直接在谱块上取长时间 Cesàro 平均：不同能量的因子 $e^{-it(E-E')}$ 平均趋于零，相同能量因子恒为一；也可对时间演化群的紧闭包取 Haar 平均。不能在没有整比谱差条件时将任意 $H$ 的演化先设为一个给定周期的相位圈。这里的谱块证明本身不需要选择这样的周期。

#### 2.1.2 实际工具的 Heisenberg 实线性空间

**命题 2.2（实际效果空间的充要条件）。** 完整相容效果可用是一份明确的强合同。若装置只有效果集合 $\mathcal F$ 与酉操作菜单 $\{U_a:a\in\mathcal A\}$，实际实验暂限为执行有限操作词后作一次末端读数。对 $w=a_1\cdots a_k$ 取 $U_w=U_{a_k}\cdots U_{a_1}$，空词对应 $I$。定义
$$
\mathcal W
=\operatorname{span}_{\mathbb R}
\left(\{I\}\cup\{U_w^\dagger F U_w:F\in\mathcal F,\ w\in\mathcal A^*\}\right)
\subseteq\operatorname{Herm}(\mathcal H).
\tag{TM.115}
$$

有限维保证这是闭实子空间，尽管动作菜单或操作词集合可无限。迹循环性给出全部未来读数的精确判据：
$$
\boxed{
\operatorname{Tr}(F U_w\rho U_w^\dagger)
=\operatorname{Tr}(F U_w\sigma U_w^\dagger)
\quad\forall F,w
\quad\Longleftrightarrow\quad
\rho-\sigma\in\mathcal W^\perp.
}
\tag{TM.116}
$$

**证明。** 每项概率差等于 $\operatorname{Tr}((U_w^\dagger F U_w)(\rho-\sigma))$。这些差全部为零，连同密度态归一化给出的 $\operatorname{Tr}(\rho-\sigma)=0$，恰好等于与式(TM.115)所有生成元正交。实线性性再给与整个 $\mathcal W$ 正交；反向直接取生成元。此处只有实际实验可提供的期望及其线性组合，没有假定两个可测算子之积也成为可测算子，因此不能未经工具核对便把 $\mathcal W$ 换成生成的乘法代数。

对任意允许动作 $a$，把一项未来实验接在 $U_a$ 后面仍是允许的有限词，故 $U_a^\dagger\mathcal W U_a\subseteq\mathcal W$。若 $\rho-\sigma\in\mathcal W^\perp$，则对任意 $A\in\mathcal W$ 有 $\operatorname{Tr}(A U_a(\rho-\sigma)U_a^\dagger)=\operatorname{Tr}(U_a^\dagger A U_a(\rho-\sigma))=0$。所以式(TM.116)定义的纤维关系对这些操作稳定，并保留原末端观察。这是既有全部未来响应与动态闭包机制在 Hermitian 线性表示中的直接实现。

如果每个 $F$ 和每个 $U_a$ 都与 $H$ 交换，则 $\mathcal W\subseteq\mathcal C_H$，pinching 相同必给实际实验相同。在全部密度态上，实际工具恰好实现完整 pinching 商的充要条件为
$$
\boxed{
\bigl[\rho-\sigma\in\mathcal W^\perp
\ \Longleftrightarrow\ P_H(\rho)=P_H(\sigma)
\quad\forall\rho,\sigma\in\mathcal D(\mathcal H)\bigr]
\quad\Longleftrightarrow\quad
\mathcal W=\mathcal C_H.
}
\tag{TM.117}
$$

**证明。** 若两空间相同，式(TM.110)说明 $P_H$ 为到该空间的正交投影，故正交性等价于 $P_H(\rho-\sigma)=0$。反之，若 $\mathcal W$ 是 $\mathcal C_H$ 的真子空间，有限维正交分解给非零 $D\in\mathcal C_H\cap\mathcal W^\perp$。因为 $I\in\mathcal W$，有 $\operatorname{Tr}D=0$。取
$$
\varepsilon=\frac1{2d\|D\|_{\mathrm{op}}}>0,\qquad
\rho_\pm=\frac Id\pm\varepsilon D,\qquad
\rho_\pm\succeq\frac{I}{2d},\qquad
P_H(\rho_+)-P_H(\rho_-)=2\varepsilon D\ne0.
\tag{TM.118}
$$

两者都是实际密度态，且差属于 $\mathcal W^\perp$，所以实际工具全部读数相同，却有不同 pinching，否定式(TM.117)左侧。必要性因此使用了整个态空间内部的合法扰动，不能不加说明地迁移到受限制备族。

具体地，若只允许 $\mathcal S\subseteq\mathcal D(\mathcal H)$，记 $\mathcal S-\mathcal S=\{\rho-\sigma:\rho,\sigma\in\mathcal S\}$。在 $\mathcal W\subseteq\mathcal C_H$ 的同一前件下，正确的任务条件是
$$
\mathcal W^\perp\cap(\mathcal S-\mathcal S)
=\ker P_H\cap(\mathcal S-\mathcal S).
\tag{TM.119}
$$

这由逐对应用式(TM.116)直接等价于两种观察关系在 $\mathcal S$ 上相同。若目标是识别整个受限态而非其 pinching，则条件改为 $\mathcal W^\perp\cap(\mathcal S-\mathcal S)=\{0\}$。例如 $\mathcal S$ 只有一个态时，即使 $\mathcal W$ 很小也已充分；全态空间的张成必要性在这里没有适用前提。该差集判据对应下文 Carmeli 等的现成受限信息完备性接口。

#### 2.1.3 每个相容效果可执行的一份明确资源合同

**命题 2.3（相容效果的执行合同）。** 仅有 $[F,H]=0$ 是代数相容性。下面给出足以把任意这样的二元效果变成实际测量的额外工具：一个二维指针 $P$，其 $H_P=0$；可制备纯空白 $|0\rangle_P$；可实现所需的保持系统与指针总能量的联合酉；可读指针的 $|0\rangle,|1\rangle$ 基。设 $0\le F\le I$ 且 $[F,H]=0$，定义
$$
A=\sqrt{I-F},\qquad B=\sqrt F,\qquad
U_F=A\otimes|0\rangle\langle0|-B\otimes|0\rangle\langle1|
+B\otimes|1\rangle\langle0|+A\otimes|1\rangle\langle1|.
\tag{TM.120}
$$

按指针分块，$U_F=\left(\begin{smallmatrix}A&-B\\B&A\end{smallmatrix}\right)$。因为 $A,B$ 都是 $F$ 的函数，二者交换，并满足 $A^2+B^2=I$；故相乘给 $U_F^\dagger U_F=U_FU_F^\dagger=I$。又因 $F$ 在能量块内，其平方根也逐块作用，所以 $[A,H]=[B,H]=0$，从而 $[U_F,H\otimes I_P]=0$。零 Hamiltonian 指针的任意状态都对能量相位不变，但纯空白的制备仍是一项独立资源。

对纯输入，$U_F(|\psi\rangle\otimes|0\rangle)=A|\psi\rangle\otimes|0\rangle+B|\psi\rangle\otimes|1\rangle$；由线性性，对全部密度态测量指针后得到未归一化分支
$$
\mathcal M_0(\rho)=A\rho A,\qquad
\mathcal M_1(\rho)=B\rho B,\qquad
\Pr(1\mid\rho)=\operatorname{Tr}(B\rho B)=\operatorname{Tr}(F\rho).
\tag{TM.121}
$$

两分支之和保迹，因此确是一份量子仪器。该构造给的是已有测量扩张思想的一份显式二元实现；它不证明任意仅具有某个有限控制菜单的装置都能执行 $U_F$，也不把制备、联合控制、指针读出和重复使用所需的复位视作免费。全效果族合同必须由这些资源或另一份实际实施证明承担，不能由效果矩阵的存在代替。

#### 2.1.4 仪器分支必须分别下降

**命题 2.4（逐分支下降条件）。** 若保留中途结果并依结果选择后续动作，只看未读结果时的平均通道就不够。固定有限结果集的量子仪器 $\{\Phi_y\}_y$，每个 $\Phi_y$ 完全正、迹不增，且 $\sum_y\Phi_y$ 保迹。对未归一化矩阵同样使用 $q=P_H$。使分支观察量只依赖原观察量的一项精确代数条件是
$$
P_H\Phi_y=P_H\Phi_yP_H\quad\forall y,\qquad
\overline\Phi_y(q)=P_H\Phi_y(q)\quad(q\in\operatorname{im}P_H).
\tag{TM.122}
$$

于是 $P_H\Phi_y(\rho)=\overline\Phi_y(P_H\rho)$，概率为 $p_y=\operatorname{Tr}\overline\Phi_y(P_H\rho)$；当 $p_y>0$ 时，更新后的摘要为 $\overline\Phi_y(P_H\rho)/p_y$。这是分支归一化的完整下降规则；概率为零的分支无须定义条件态。若实际条件更强，$P_H\Phi_y=\Phi_yP_H$，则式(TM.122)由 $P_H^2=P_H$ 立即成立。式(TM.121)的两个平方根 Kraus 算子都与 $H$ 交换，逐块计算即给这个更强条件。

如果同一策略只依赖已保存的结果档案，且每一步可选择的仪器都满足式(TM.122)，则两份同摘要输入在第一步各结果概率相同、相应正概率后继摘要相同。沿每个有限历史重复这一事实，归纳得到整个记录词的概率相同以及终端摘要相同。这才是从一次分支合同到自适应后续实验的连接，未把单次末端效果的权限自动扩大成任意仪器权限。

平均通道的下降不能替代分支条件。取量子位的 $Z$ 基 pinching $P_Z$，$X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，令
$$
E_\pm=(I\pm X)/2=|\pm\rangle\langle\pm|,\qquad
\Phi_\pm(C)=\operatorname{Tr}(E_\pm C)I/2,\qquad
K_{b,\pm}=|b\rangle\langle\pm|/\sqrt2\quad(b=0,1).
\tag{TM.123}
$$

这里 $\Phi_\pm(C)=\sum_bK_{b,\pm}CK_{b,\pm}^\dagger$，且 $\sum_bK_{b,\pm}^\dagger K_{b,\pm}=E_\pm$，所以各分支 CP 且迹不增。两分支之和为去极化通道 $\Phi(C)=\operatorname{Tr}(C)I/2$，满足 $P_Z\Phi=\Phi P_Z=\Phi$。可是
$$
P_Z(|+\rangle\langle+|)=P_Z(|-\rangle\langle-|)=I/2,\qquad
P_Z\Phi_+(|+\rangle\langle+|)=I/2,\qquad
P_Z\Phi_+(|-\rangle\langle-|)=0.
\tag{TM.124}
$$

因此 $+$ 结果的概率分别为一和零，分支不经原 pinching 下降。最终未读的量子输出完全相同，保留的经典结果却已经分开两态。这不是对完整能量相容仪器合同的反例：此仪器的 $E_\pm$ 不与 $Z$ 交换，正好不满足所需的分支权限。它反驳的具体推断是“平均通道下降足以保证带记录实验下降”。

#### 2.1.5 独立固定不变参考的总能量恒等式

**命题 2.5（独立不变参考恒等式）。** 增加一个参考系统不必细分旧观察纤维。令 $H_R=\sum_{e\in\mathcal E_R}eQ_e$ 为有限维参考 Hamiltonian，$\tau$ 是一份固定密度态，并满足 $[\tau,H_R]=0$；不同系统输入均与同一 $\tau$ 独立组成 $\rho\otimes\tau$。记
$$
H_{SR}=H\otimes I_R+I\otimes H_R,\qquad
R_\lambda=\sum_{E+e=\lambda}\Pi_E\otimes Q_e,\qquad
P_{H_{SR}}(B)=\sum_\lambda R_\lambda B R_\lambda.
\tag{TM.125}
$$

$R_\lambda$ 是总能量的完整谱投影；不同的 $(E,e)$ 可给同一个 $\lambda$，这些简并不能在定义时被拆成互不相干的小测量。对任意系统矩阵 $A$，逐块展开有
$$
\begin{aligned}
P_{H_{SR}}(A\otimes\tau)
&=\sum_{E+e=E'+e'}
 (\Pi_EA\Pi_{E'})\otimes(Q_e\tau Q_{e'}),\\
Q_e\tau Q_{e'}&=0\quad(e\ne e'),\qquad
\sum_eQ_e\tau Q_e=\tau.
\end{aligned}
\tag{TM.126}
$$

第二行来自 $[\tau,H_R]=0$，允许每个参考简并块内部有任意矩阵。非零项因此必须先有 $e=e'$，再由总能量相等得 $E=E'$。故
$$
\boxed{
P_{H_{SR}}(A\otimes\tau)=P_H(A)\otimes\tau
\qquad\forall A.
}
\tag{TM.127}
$$

这给出完整的张量恒等式，而不仅是一类测试下的上界。若 $P_H(\rho)=P_H(\sigma)$，两份乘积输入的总能量 pinching 相同，式(TM.111)用于联合系统便说明：全部总能量相容效果均不能区分它们。插入任意保持总能量的联合酉词仍不能区分，因为式(TM.113)同样适用于 $H_{SR}$；若还保留仪器记录，则应逐分支使用B卷第2.1.4节的条件。

反过来，若 $P_H(\rho)\ne P_H(\sigma)$，B卷第2.1.1节构造的系统相容效果 $Q_+$ 能区分两者，且 $Q_+\otimes I_R$ 与总能量交换，读取概率不依赖归一化的 $\tau$。所以在全部联合相容效果可用的合同下，加入这份参考前后观察等价关系完全相同。若装置只允许受限联合效果菜单，后者未必包含 $Q_+\otimes I_R$，则不能无条件保留这一逆向断言。

独立、固定和不变是不同条件。已有的相关档案不必是 $\rho\otimes\tau$；相干参考有 $Q_e\tau Q_{e'}\ne0$ 的交叉块，能与相反系统能隙配对；随候选系统态改变的第二份样本也不属于同一个固定 $\tau$ 合同。因此式(TM.127)既不排除关系相位的测量，也不排除同源重复制备增加可区分性。它精确说明在何种资源扩展下旧商得到保持。

#### 2.1.6 同一未知相位的两份样本能细分单份观察纤维

**反例 2.6（同源样本细分单份纤维）。** 令单系统 $H=N=|1\rangle\langle1|$，取
$$
\rho=|+\rangle\langle+|=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
\sigma=I/2,\qquad
P_N(\rho)=P_N(\sigma)=I/2.
\tag{TM.128}
$$

现在额外授予两次来自同一制备源、具有共同相位的样本，候选联合输入分别为 $\rho\otimes\rho$ 和 $\sigma\otimes\sigma$。按 $00,01,10,11$ 排列，$N^{(2)}=N\otimes I+I\otimes N=\operatorname{diag}(0,1,1,2)$。第一份乘积矩阵全部元素为 $1/4$，经总能量 pinching 后为
$$
\begin{aligned}
P_{N^{(2)}}(\rho\otimes\rho)
&=\tfrac14\begin{pmatrix}
1&0&0&0\\
0&1&1&0\\
0&1&1&0\\
0&0&0&1
\end{pmatrix}\\
&=\tfrac14|00\rangle\langle00|
 +\tfrac12|\psi_+\rangle\langle\psi_+|
 +\tfrac14|11\rangle\langle11|,\\
P_{N^{(2)}}(\sigma\otimes\sigma)&=I_4/4,
\qquad |\psi_+\rangle=(|01\rangle+|10\rangle)/\sqrt2.
\end{aligned}
\tag{TM.129}
$$

取合法二元效果
$$
Q=|\psi_+\rangle\langle\psi_+|
=\tfrac12\begin{pmatrix}
0&0&0&0\\
0&1&1&0\\
0&1&1&0\\
0&0&0&0
\end{pmatrix},\qquad
[Q,N^{(2)}]=0,\qquad
\operatorname{Tr}(Q\rho^{\otimes2})=\tfrac12,\quad
\operatorname{Tr}(Q\sigma^{\otimes2})=\tfrac14.
\tag{TM.130}
$$

其余效果为 $I-Q$，也合法。$Q$ 完全位于总能量一的简并块，故交换关系直接成立；将中间 $2\times2$ 块相乘取迹便给两个概率。若采用B卷第2.1.3节对联合系统的指针资源合同，这份效果也有明确的合法实施；仅给出 $Q$ 不替受限装置自动授予该实施能力。

共同相位不能省略。写 $|+_\phi\rangle=(|0\rangle+e^{i\phi}|1\rangle)/\sqrt2$、$\rho_\phi=|+_\phi\rangle\langle+_\phi|$。没有外部相位标准、而两份样本共享同一个均匀未知 $\phi$ 时，联合律为
$$
\begin{aligned}
\Omega_{\rm common}
&=\frac1{2\pi}\int_0^{2\pi}\rho_\phi\otimes\rho_\phi\,d\phi
 =\frac14\sum_{k=0}^{3}\rho_{k\pi/2}\otimes\rho_{k\pi/2}
 =P_{N^{(2)}}(\rho^{\otimes2}),\\
\Omega_{\rm independent}
&=\left(\frac1{2\pi}\int_0^{2\pi}\rho_\phi\,d\phi\right)
 \otimes\left(\frac1{2\pi}\int_0^{2\pi}\rho_\theta\,d\theta\right)
 =I_4/4.
\end{aligned}
\tag{TM.131}
$$

证明只需展开矩阵元素：两样本的总激发数为 $0,1,2$，元素的相位因子为 $e^{im\phi}$，其中 $m\in\{-2,-1,0,1,2\}$。积分及所列四点平均都仅保留 $m=0$，恰得式(TM.129)。独立相位平均则分别消去每份的非对角项，得到第二行。因此两个单份边缘均为 $I/2$，联合读数仍不同；新增结构是实际共同来源保留的相对相位。

式(TM.131)第一行已经给出四个乘积态的合法凸组合，所以这份共同相位平均态是可分态；平均前的 $\rho\otimes\rho$ 更是乘积态。$Q$ 使用联合效果不使被测态因此成为纠缠态。这个例子认证的是特定共同相位资源的可见后果，不能作为纠缠存在性的见证。

同样，“取得第二份样本”不是对单份未知态免费调用一条通道。假设对所有态都有一个线性通道实现 $\rho\mapsto\rho\otimes\rho$，令 $\rho_0=|0\rangle\langle0|$、$\rho_1=|1\rangle\langle1|$，则仿射性要求的输出与所需输出矛盾：
$$
\tfrac12\rho_0^{\otimes2}+\tfrac12\rho_1^{\otimes2}
=\tfrac12\operatorname{diag}(1,0,0,1)
\ne I_4/4
=\left(\tfrac12\rho_0+\tfrac12\rho_1\right)^{\otimes2}.
\tag{TM.132}
$$

所以这里的正确定义是一个可重复调用的制备源及其共同参数、相位重置规则和样本权限；不是在旧摘要上进行后处理。B卷第2.1.5节的参考 $\tau$ 固定且不变，本例在两种假设下加入的第二样本分别是 $\rho$ 与 $\sigma$，本来就不是同一个独立不变参考。两项结论因此可以同时成立：单份观察商对前一种资源扩展保持充分，对后一种来源扩展却可以被严格细分。

#### 2.1.7 有限动作菜单与既有 Bellman 值下降接口

**命题 2.7（有限菜单的值下降）。** 动态摘要还能支持决策，但需匹配已有定理的量词。固定有限非空动作集合 $\mathcal A$，微观态空间为密度态，摘要 $q=P_H$ 取值于其实际像；动作以声明的守能酉作确定更新 $T_a(\rho)=U_a\rho U_a^\dagger$。由式(TM.113)，存在 $\overline T_a(q)=U_aqU_a^\dagger$，并有 $qT_a=\overline T_aq$。另须分别给出阶段报酬与终端报酬的因子分解
$$
r(\rho,a)=\overline r(q(\rho),a),\qquad
 g(\rho)=\overline g(q(\rho)),\qquad
V_0=g,\quad
V_{n+1}(\rho)=\max_{a\in\mathcal A}
\{r(\rho,a)+V_n(T_a\rho)\}.
\tag{TM.133}
$$

宏观值 $\overline V_n$ 以相同递推、$\overline r,\overline g,\overline T_a$ 定义。于是
$$
V_n(\rho)=\overline V_n(q(\rho))\qquad\forall n\in\mathbb N,\ \forall\rho.
\tag{TM.134}
$$

**证明。** 直接应用 `finite_horizon_value_factorization`：微状态是本节密度态，宏状态是 $q=P_H$ 的实际像，动作是所选有限非空菜单，转移为 $T_a$ 与已证明的商转移 $\overline T_a$，阶段奖励和终值为本节两份因子化数据。每项交织、奖励与终值假设均由本节合同给出，故各时域值下降。随机分支及无限动作菜单不属于这份代入。

全部与 $H$ 交换的酉通常构成无限动作族；本节的精确观察商本身允许这种无限族，但现有有限最大值 Lean 接口不能直接承担它。若要改用上确界，需另行说明值域、有限性和相应递推；若声称最优动作达到，还须另给达到条件。带测量分支的随机决策也要连接相应的随机 Bellman 供应，不能仅凭B卷第2.1.4节仪器定义就当作上述确定转移定理的实例。阶段报酬与终端目标是否经摘要下降始终是独立义务；守能本身不使任意指定奖励可见。

#### 2.1.8 仓内现有所有者与本节的复用边界

以下定位统一使用不可变快照 `237012b49d0d4729a86f7e9dd252d94df1de8dd0`。它们说明哪些机制已有正文或 Lean 供应；正文所有者与形式证明所有者分别列明，不把文中的数学推导自动标成 kernel 已认证。

| 既有位置 | 已承担的结构 | 本节连接时保留的边界 |
|---|---|---|
| `docs/develop/theory/QUANTUM-REALITY.md` 第164.2节，约第21994行 | 相同局部态、计算基联合概率和能量分布，在共振交换后产生不同局部读数的两态见证；具体后续读数为 $4/9$ 与 $2/9$ | “边缘与能量相同不保证全部合法未来相同”已经有现成实例；本节不再次申报这一现象为新发现 |
| 同卷第373节，第49984行起；定理373.1在第50026行 | 固定独立、相位不变参考不能读取系统第一阶相位；式373.2—373.4给联合关系效果、参考降低算子及有效读数对比度 | 式(TM.127)将同一机制写成任意有限能谱的完整张量恒等式，仍须独立、固定与不变前件 |
| 同卷第374节，第50124行起 | 有限能级相位参考的最优区分成功概率，定理374.1为 $\tfrac12(1+\cos(\pi/(N+1)))$ | 精度与参考资源已有专门所有者，不从抽象可恢复性推免费、无限精度访问 |
| `D5/S3/Observer/Conditioning.lean:30`、`:37`、`:58`、`:98`、`:108` | `IsRecordMeasurement`、`unreadState`、`unreadState_trace`、`unreadState_idempotent`、`unreadState_fixed_iff` | 有限完备正交自伴记录投影及其 pinching 已有 Lean 定义、迹保持、幂等和无跨块固定点接口；谱投影代入不构成新的通用 pinching 定理 |
| `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean:45`、`:50`、`:58`、`:81` | `DynClosure` 与保留原观察、操作闭合、最小细化三项定理 | 指定全部有限操作词的动态商已有一般供应；将载体换为量子密度态不另造抽象最小性定理 |
| `D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean:46` | 一个指定 Heisenberg 实线性算子、有限中心化效果族的全部未来统计充分性 | 其量词是单算子的迭代；式(TM.115)的多动作词须说明相应表示关系，不能直接冒领原定理的范围 |
| `docs/develop/theory/BEDC-WM.md:219`，B14.C | 已用相同能量概率的 $|+\rangle\langle+|$ 与 $I/2$ 区分观察纤维、群轨道与 twirling 的像 | 观察等价不自动等于同一群轨道，pinching 商也不自动证明状态只差一个相位变换 |
| `D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean:30` | `finite_horizon_value_factorization`，具有 `[Fintype Action] [Nonempty Action]`，并要求转移交织、阶段与终端报酬分解 | 式(TM.133)—(TM.134)使用有限非空菜单；无限相容酉群与随机仪器决策需另匹配接口 |

这份归属也限定内容的新意：本节保留实际工具张成、分支反例、参考张量恒等式和两份共同相位的完整推导，用来澄清来源扩展与组合充分性的关系。它们没有获得新增 Lean 核验，不因换用能量、边界或全息术语就成为新的一般量子定理；文献优先权也没有由这份综合推导确定。

#### 2.1.9 成熟文献供应与统一的适用范围

G. Gour、R. W. Spekkens，*The resource theory of quantum reference frames: manipulations and monotones*，[arXiv:0711.0043v2](https://arxiv.org/pdf/0711.0043v2)，第II.A节、PDF第7—8页、式(13)—(17)，给出群不变态、CP 操作和群平均的基础结构；第8页式(16)及邻接文字明确以群平均相等组织态的等价类。这里引用该处定义与说明，不把它改称为未列出的编号定理。其不变 CP 操作框架比只允许与 Hamiltonian 交换的系统酉更宽；使用时需保持具体工具合同，不能把协变通道和严格守能酉当作同一个操作集合。

S. D. Bartlett、T. Rudolph、R. W. Spekkens，*Reference frames, superselection rules, and quantum information*，[arXiv:quant-ph/0610030v3](https://arxiv.org/pdf/quant-ph/0610030v3)，第II.B节、PDF第5页式(2.9)给出粒子数 pinching，第6页讨论 $\operatorname{span}\{|01\rangle,|10\rangle\}$ 内的允许操作，并明确超选择规则不等于粒子数守恒。第II.C节第7—8页式(2.20)—(2.25)讨论不变效果与 irrep/multiplicity 分解，第8页式(2.25)旁的显示定理给群平均的标准形；其中表示空间的张量分解是虚拟子系统分解，不能自动当作实际空间分区。第9页第III节开头说明，共享同一参考制备的多量子位经历同一个未知变换，为式(TM.131)所区分的共同与独立相位提供成熟语境。第III.C.2节第16—17页式(3.31)、(3.32)的激活与双份蒸馏使用双边局部粒子数超选择规则，属于另一份任务合同；不能将那些结果逐字当作本节可分两份样本的纠缠见证。

C. Carmeli、T. Heinosaari、J. Schultz、A. Toigo，*Tasks and premises in quantum state determination*，[arXiv:1308.5502v2](https://arxiv.org/pdf/1308.5502v2)，§2、PDF第3—4页定义效果范围生成的实算子系统及其 annihilator，第4页式(1)给相应迹正交条件；§3、第5页 Proposition 2 给出在声明的前提态族与目标态族上的信息完备性判据，形如 $\mathcal R(M)^\perp\cap(\mathcal T-\mathcal P)=\{0\}$。式(TM.116)与(TM.119)使用这类线性统计几何，并逐项说明实际动态工具怎样产生效果族。该文关于抽象算子系统对应 POVM 的实现结论不替某个指定 Hamiltonian、指针和控制菜单证明可执行性；后者在B卷第2.1.3节单独承担。

本节给“可组合关系接口”增加的条件可以直接表述：先由实际后续实验确定观察纤维，再说明新接入对象来自什么共同制备、保留哪些记录、允许何种联合操作。独立固定不变参考保持式(TM.127)中的纤维，同源共同相位的两份样本则由式(TM.129)—(TM.131)严格细分原单份纤维；分支记录只有在逐分支下降时才能安全接入旧摘要。这里发生变化的是被允许参与的联合关系，不能从单份状态名、单个守恒数或平均输出独自推出全部未来的充分性。

### 2.2 共享来源的有限阶关系矩、紧轨道与可辨认尺度

B卷第2.1节说明，两份来自同一相位源的样本可以显示单份 pinching 隐藏的关系。本节进一步回答：如果允许任意有限数量的同源样本，究竟还剩下哪些不可区分性；固定有限维模型是否总有某个有限阶就足够；这个存在结论能否给出实际阶数、误差和成本。答案需要同时固定群作用、联合制备与完整效果权限：全部共同平均的关系矩确定的是紧群轨道，固定群作用存在足够的有限阶，但维数单独不能统一约束这个阶数，精确分离也不保证显著的单次区分优势。

本节给出普通数学证明与已有供应的连接，不新增 Lean 核验，不将这种综合自动归为原创结果。特别地，出现一次相邻理想相等，不构成后续全部理想已经稳定的证书。

#### 2.2.1 固定群作用及其全部可取得的实验读数

**定义 2.8（固定共同来源与关系矩）。** 固定 $d\ge1$，令 $\mathcal D_d$ 为 $d$ 维密度态的紧集，$G\le U(d)$ 是一个固定的紧矩阵子群，$\lambda_G$ 为归一化 Haar 概率测度。这里固定的是实际矩阵作用；若从抽象紧群及其连续酉表示开始，就以该表示的紧像作为 $G$。对 $n\ge1$ 定义共享群参数的关系矩
$$
P_n(\rho)=\int_G(U\rho U^\dagger)^{\otimes n}\,d\lambda_G(U),
\qquad \rho\in\mathcal D_d.
\tag{TM.135}
$$

这是作用在 $\mathcal H^{\otimes n}$ 上的密度矩阵。全部 $n$ 份使用同一个 $U$；这与每份分别随机选择 $U_j$ 的实验不同。数学上的群平均也不要求假定世界真的随机抽取 Haar 参数：如果允许的效果对共同群作用不变，它在每个固定未知 $U$ 下的概率本来就一样，平均只是一份给出相同概率的规范代表。

与能量约束相连时，固定 $H=H^\dagger$，取
$$
G=\overline{\{e^{-itH}:t\in\mathbb R\}}\le U(d),\qquad
H^{(n)}=\sum_{j=1}^n I^{\otimes(j-1)}\otimes H\otimes I^{\otimes(n-j)},\qquad
(e^{-itH})^{\otimes n}=e^{-itH^{(n)}}.
\tag{TM.136}
$$

闭包在有限维矩阵拓扑中取；酉群紧，因此 $G$ 紧。若 $\Pi_E^{(n)}$ 是 $H^{(n)}$ 的完整总能量投影，则
$$
\boxed{
P_n(\rho)=P_{H^{(n)}}(\rho^{\otimes n})
=\sum_E\Pi_E^{(n)}\rho^{\otimes n}\Pi_E^{(n)}.
}
\tag{TM.137}
$$

**证明。** 在 $H$ 的特征基中，张量矩阵元的行、列多指标分别具有总能量 $E,E'$。时间变换在该矩阵元上乘 $e^{-it(E-E')}$。这给出 $G$ 上相应连续字符，因为张量作用是连续的，且时间子群稠密。若 $E=E'$，字符在稠密子群上恒为一，故在 $G$ 上恒为一。若 $E\ne E'$，存在实数 $t$ 使字符值不为一；对 Haar 积分用该群元素平移，积分等于自身乘一个非一数，因此积分为零。逐矩阵元积分，恰好保留等总能量项，得到式(TM.137)。简并总能量块内的交叉关系全部保留，不能再逐单份能量分别 pinching。

若每个 $n$ 都允许取得全部总能量相容效果，即 $0\le F\le I$、$[F,H^{(n)}]=0$，则
$$
\boxed{
P_n(\rho)=P_n(\sigma)
\quad\Longleftrightarrow\quad
\operatorname{Tr}(F\rho^{\otimes n})
=\operatorname{Tr}(F\sigma^{\otimes n})
\quad\text{对全部这些实际可取得的 }F.
}
\tag{TM.138}
$$

正向由 $\operatorname{Tr}(F\rho^{\otimes n})=\operatorname{Tr}(FP_n(\rho))$。反向令 $\Delta=P_n(\rho)-P_n(\sigma)$；它与 $H^{(n)}$ 交换且迹为零，若非零，其正谱投影就是能区分两者的相容效果。证明与B卷第2.1.1节相同。对一般紧 $G$，将相容条件换成 $F$ 与全部 $U^{\otimes n}$ 交换，结论同样成立。只知道“已取得的效果都相容”还不够：实际菜单可能遗漏这份区分效果，逆向必须由完整权限或实际效果张成证明承担。B卷第2.1.3节的指针扩张可作为一种明确的实施合同，仍须计入联合控制和记录资源。

#### 2.2.2 全部关系矩精确确定紧群轨道

**命题 2.9（全阶矩确定紧轨道）。** 在上述固定群作用下，对任意 $\rho,\sigma\in\mathcal D_d$，有
$$
\boxed{
P_n(\rho)=P_n(\sigma)\quad\forall n\ge1
\quad\Longleftrightarrow\quad
\exists V\in G:\ \sigma=V\rho V^\dagger.
}
\tag{TM.139}
$$

式(TM.139)是成熟紧群不变量与矩轨道恢复理论在 Hermitian 实表示上的实例；直接来源为B卷第2.2.11节所列 Bandeira 等的矩张量、分离不变量与紧轨道定理。以下通过 Haar 推前、连续函数逼近与测度唯一性保留完整证明，以说明同源量子准备如何满足这份接口。此处的轨道是 $G$ 的实际轨道；当 $G$ 定义为时间演化的闭包时，不将它改写成存在某个精确时刻。

**将一份态变成轨道概率测度。** 令 $K=\mathcal D_d$，定义连续轨道映射 $\alpha_\rho(U)=U\rho U^\dagger$ 及其推前
$$
\mu_\rho=(\alpha_\rho)_*\lambda_G,\qquad
\int_K f(X)\,d\mu_\rho(X)
=\int_G f(U\rho U^\dagger)\,d\lambda_G(U).
\tag{TM.140}
$$

$K$ 是有限维紧度量空间；这些推前是正则 Borel 概率测度。选取 Hermitian 实空间的一组基 $A_1,\ldots,A_{d^2}$，令 $f_j(X)=\operatorname{Tr}(A_jX)$。它们是实值连续线性坐标。张量迹的乘法性质给出任意次数的混合坐标矩：
$$
\int_K\prod_{k=1}^n f_{j_k}(X)\,d\mu_\rho(X)
=\operatorname{Tr}\!\left[
(A_{j_1}\otimes\cdots\otimes A_{j_n})P_n(\rho)
\right].
\tag{TM.141}
$$

所以全部 $P_n$ 相同就使两份测度对任意坐标单项式积分相同；常数项由总质量一处理，线性组合给全部坐标多项式相同。这里使用实 Hermitian 坐标，非对角元素的实部和虚部都包含在基中，没有遗漏混合共轭矩。

**多项式矩确定整个轨道测度。** 坐标多项式在 $C(K,\mathbb C)$ 中形成一个含常数、对复共轭封闭的代数，因为各 $f_j$ 都实值。它分离 $K$ 的点：不同 $X,Y$ 的差 $D=X-Y\ne0$ 是 Hermitian，且 $\operatorname{Tr}(D(X-Y))=\operatorname{Tr}(D^2)>0$；$D$ 是基 $A_j$ 的实线性组合，所以某个坐标必不同。Stone–Weierstrass 定理给该代数在连续函数空间中一致稠密。若多项式 $p_k$ 一致逼近 $f$，则 $|\int(f-p_k)\,d\mu|\le\|f-p_k\|_\infty$，因为测度总质量为一。两份测度的多项式积分相同，取极限即得全部连续函数积分相同。对实连续函数应用 Riesz 表示的测度唯一性，得到 $\mu_\rho=\mu_\sigma$。

**轨道测度具有整个轨道作为支撑。** 有
$$
\operatorname{supp}\mu_\rho=G\cdot\rho
=\{U\rho U^\dagger:U\in G\}.
\tag{TM.142}
$$

轨道是紧空间的连续像，所以在 $K$ 中闭；其外点有不相交开邻域，推前测度为零。另一方面，若 $X=U_0\rho U_0^\dagger$ 属于轨道，任意包含 $X$ 的相对开邻域 $O\subseteq K$ 都有非空开原像 $\alpha_\rho^{-1}(O)$。紧群 Haar 测度在每个非空开集上严格为正：若某个非空开集质量为零，其全部左平移也为零，而紧性使其中有限个平移覆盖 $G$，将推出 $\lambda_G(G)=0$，与归一化矛盾。因此 $\mu_\rho(O)>0$，证明该点属于支撑。

由 $\mu_\rho=\mu_\sigma$ 得支撑相同，故两个轨道相同，尤其 $\sigma\in G\cdot\rho$，完成式(TM.139)正向。反向若 $\sigma=V\rho V^\dagger$，在式(TM.135)中作右平移 $U\mapsto UV$。紧群的归一化 Haar 测度也右不变，故每个 $P_n$ 都相同。至此两个方向均已证明。

该结论不说单个 $P_1$ 的纤维就是群轨道。它用的是整套共同来源的所有有限阶关系矩；扩大实验语言以后，才将原来的更粗纤维细化到这个轨道商。群轨道内部的共同参考选择仍不可由这些不变实验恢复。

#### 2.2.3 固定实际群作用存在足够的有限阶

**命题 2.10（固定群作用的有限分离阶）。** 式(TM.139)使用全部 $n$，但对一个固定有限维矩阵群作用，可以把分离轨道所需的阶数压到某个有限值。这里得到的是存在性，不是一个已知数值上界。 这一存在性也由成熟不变量理论直接供应：Bandeira 等的 Theorem A.31 给有限齐次代数生成元，Theorem A.32 给紧群轨道的分离性；每个齐次次数 $k$ 的不变量可由第 $k$ 阶矩读取，故生成元的最高次数给一个充分阶数。有限分离集可以小于代数生成集，其准确作用由该文 Proposition 3.39 表述。下面的坐标差理想证明给出同一有限性结论的另一份完整接口，不另将固定模型有限阶存在性申报为新的一般结果。

继续固定 $G\le U(d)$。对任意 Hermitian 矩阵用 $d^2$ 个实坐标 $x$ 表示，暂不施加正性或迹条件；式(TM.135)仍可定义一个齐次次数为 $n$ 的矩阵值多项式 $P_n(x)$。原因是 $UxU^\dagger$ 的每个坐标对 $x$ 线性，张量积给次数为 $n$ 的有限多项式，群积分只把系数替换成固定实数或复数。对两组坐标 $x,y$，令 $f_{n,\alpha}$ 遍历 $P_n(x)-P_n(y)$ 的全部实、虚矩阵坐标差，在有限变量多项式环中定义
$$
\mathscr R=\mathbb R[x_1,\ldots,x_{d^2},y_1,\ldots,y_{d^2}],\qquad
I_N=\langle f_{n,\alpha}:1\le n\le N,\ \alpha\rangle,\qquad
I_1\subseteq I_2\subseteq\cdots.
\tag{TM.143}
$$

实数域 Noetherian，Hilbert 基定理保证有限变量多项式环 $\mathscr R$ Noetherian。由理想升链条件，存在一个 $N\ge1$ 使此后全部理想都等于 $I_N$。等价地，全部高阶坐标差都属于 $I_N$。如果某对态的前 $N$ 阶矩相同，$I_N$ 的每个生成元在该对坐标处为零，则其中每个多项式都为零，故全部高阶矩也相同。结合式(TM.139)，得到
$$
\boxed{
\exists N=N(G,d)<\infty\quad\forall\rho,\sigma\in\mathcal D_d:
\bigl[P_n(\rho)=P_n(\sigma)\ (1\le n\le N)\bigr]
\Longleftrightarrow \sigma\in G\cdot\rho.
}
\tag{TM.144}
$$

记号 $N(G,d)$ 中的 $G$ 包含其在 $U(d)$ 内的具体嵌入；只固定抽象群的名称与维数，不固定其表示，并没有取得同一个 $N$。后面的三维整数能谱族将直接检验这个量词。

此外，每个 $U\rho U^\dagger$ 的迹为一，因此部分迹逐项给出
$$
\operatorname{Tr}_{n+1,\ldots,N}P_N(\rho)=P_n(\rho)\quad(1\le n\le N),
\qquad
\boxed{P_N(\rho)=P_N(\sigma)\Longleftrightarrow\sigma\in G\cdot\rho}
\quad\text{对式(TM.144)所给 }N.
\tag{TM.145}
$$

证明第一式只需 $\operatorname{Tr}_{n+1,\ldots,N}(X^{\otimes N})=X^{\otimes n}(\operatorname{Tr}X)^{N-n}$，再用积分线性性；第二式由第一式与式(TM.144)。因此一个足够高阶的完整概率律已经包含所需低阶律，不必把它们当作相互独立的信息源相加。

Noetherian 条件说明**存在最终稳定点**，没有证明“只要某次 $I_N=I_{N+1}$，往后就都不再增长”。本节没有给这些特殊生成理想的单步递推封闭判据，也没有给显式次数界；故任何一次相邻理想平台都不能单独成为停止证书。实际计算还需要可表示的系数、有效生成方法和经证明的终止判据，不能把抽象实系数理想的有限生成性直接报为已实现算法。

#### 2.2.4 固定模型有定性的连续逆，没有自动的数值条件界

**命题 2.11（定性连续逆及其边界）。** 有限阶分离还给一种定性稳定性。对态定义半迹距离 $D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$，在轨道商上定义
$$
d_G([\rho],[\sigma])=\min_{U\in G}D(\rho,U\sigma U^\dagger).
\tag{TM.146}
$$

最小值由 $G$ 紧性达到。它不依赖代表元，因为左右乘固定群元素不改变最小化集合。对称性由取逆和酉不变性得到；三角不等式由插入中间态并组合两个群元素得到；零值由最小值达到给同轨道。因此它是轨道商上的实际度量。作为态对的函数，它还满足对两输入扰动的 Lipschitz 界 $|d_G(\rho,\sigma)-d_G(\rho',\sigma')|\le D(\rho,\rho')+D(\sigma,\sigma')$，直接由三角不等式再对群元素取最小值得到。

固定式(TM.144)中的一个足够阶数 $N$。$[\rho]\mapsto P_N(\rho)$ 是紧轨道商到其实际矩阵像的连续单射，目标空间 Hausdorff，因此是到该像的同胚，逆映射一致连续。也可给出不依赖抽象商定理的直接误差模定义：
$$
\begin{aligned}
\omega_N(\eta)
&=\max\{d_G([\rho],[\sigma]):\rho,\sigma\in\mathcal D_d,
\ D(P_N(\rho),P_N(\sigma))\le\eta\},\\
\omega_N(0)&=0,\qquad \lim_{\eta\downarrow0}\omega_N(\eta)=0,\qquad
d_G([\rho],[\sigma])\le\omega_N\!\left(D(P_N(\rho),P_N(\sigma))\right).
\end{aligned}
\tag{TM.147}
$$

约束集非空，因为可取相同的两态；它是紧集中的闭集，最大值因此达到。$\omega_N(0)=0$ 来自式(TM.145)。若趋零性质失败，存在 $\eta_k\downarrow0$ 与对应态对，使轨道距离至少为某个固定正数；紧性给收敛子序列，极限态对的 $P_N$ 相同，轨道距离却仍严格正，矛盾。其余不等式由最大值定义。

式(TM.147)只是固定群作用、固定阶数与指定距离下的定性一致连续性。它没有提供可计算的显式模、线性常数、Hölder 指数、控制误差或样本预算，也没有跨 Hamiltonian 的统一常数。即使效果空间有限维，可以选有限多个效果构成线性坐标，有限次随机实验一般也不能取得这些概率的精确实数值。将统计误差运输为轨道误差，仍需一份实际概率估计程序及其可信界，然后才可接上已知或另外估计的恢复模。

#### 2.2.5 非退化量子位由二阶共同关系精确确定相位轨道

**命题 2.12（量子位二阶轨道恢复）。** 这个有限阶存在结论在量子位能量相位模型中可以显式实现。取 $H=\operatorname{diag}(E_0,E_1)$，$E_0\ne E_1$，写
$$
\rho=\begin{pmatrix}p&c\\\overline c&1-p\end{pmatrix},\qquad
0\le p\le1,\quad |c|^2\le p(1-p),\qquad
P_1(\rho)=\operatorname{diag}(p,1-p).
\tag{TM.148}
$$

两份系统的三种总能量 $2E_0,E_0+E_1,2E_1$ 各不相同，中间能量块由 $01,10$ 张成。按 $00,01,10,11$ 排列，直接 pinching 得
$$
P_2(\rho)=\begin{pmatrix}
p^2&0&0&0\\
0&p(1-p)&|c|^2&0\\
0&|c|^2&p(1-p)&0\\
0&0&0&(1-p)^2
\end{pmatrix}.
\tag{TM.149}
$$

因此它除占据概率外还保留相干的模。实际效果可取 $Q_\pm=|\psi_\pm\rangle\langle\psi_\pm|$，$|\psi_\pm\rangle=(|01\rangle\pm|10\rangle)/\sqrt2$，二者都与总能量交换，并可与 $I-Q_+-Q_-$ 合成三结果测量。对应概率满足
$$
q_\pm=\operatorname{Tr}(Q_\pm\rho^{\otimes2})=p(1-p)\pm|c|^2,\qquad
|c|^2=(q_+-q_-)/2,\qquad
\operatorname{Tr}_2P_2(\rho)=P_1(\rho).
\tag{TM.150}
$$

正性前件保证所有概率非负。若另一态写为 $\sigma=\left(\begin{smallmatrix}p'&c'\\\overline{c'}&1-p'\end{smallmatrix}\right)$，则
$$
\boxed{
P_2(\rho)=P_2(\sigma)
\Longleftrightarrow p=p',\ |c|=|c'|
\Longleftrightarrow\sigma\in G\cdot\rho.
}
\tag{TM.151}
$$

第一个方向由部分迹与中间块得到，反向代入式(TM.149)。最后一个等价来自非零能隙：$e^{-itH}$ 将 $c$ 乘以 $e^{-it(E_0-E_1)}$，当 $t$ 遍历实数时覆盖全部圆周相位，所以同模的非零相干可互相变换；若两者均零，它们已经是同一态。端点 $p=0,1$ 强迫 $c=0$，也已涵盖。B卷第2.1.6节的 $|+\rangle\langle+|$ 与 $I/2$ 给相同 $P_1$、不同 $P_2$，因此对整个量子位态空间，一阶不足、二阶足够。

这个 $N=2$ 结论适用于所声明的非退化单 Hamiltonian 相位作用，不是对任意抽象紧群在二维空间上的任何表示都给统一二阶界。若 $H$ 是数量矩阵，则 $P_1(\rho)=\rho$，一阶就足够，也不能套用式(TM.148)的去相干公式。

#### 2.2.6 共同相位与独立相位定义不同的联合来源

**反例 2.13（共同相位与独立相位）。** 对任意 $n$，共同与独立群参数分别给
$$
\begin{aligned}
\Omega_{\rm common}^{(n)}(\rho)
&=\int_G(U\rho U^\dagger)^{\otimes n}\,d\lambda_G(U)=P_n(\rho),\\
\Omega_{\rm independent}^{(n)}(\rho)
&=\int_{G^n}\bigotimes_{j=1}^n(U_j\rho U_j^\dagger)\,
 d\lambda_G(U_1)\cdots d\lambda_G(U_n)
 =P_1(\rho)^{\otimes n}.
\end{aligned}
\tag{TM.152}
$$

第二式由有限维逐元素 Fubini 与乘积测度得到。共同来源只在给定同一个未知 $U$ 以后，才把各份写成条件独立的乘积；去掉共同参数之后，平均态可以相关。独立平均则在每份分别删去参考关系，全阶输出仍只是 $P_1$ 的张量幂，不能凭增加份数恢复已删除的相干模。

共同平均态本身是乘积态的概率混合，因此属于可分态集合；有限维中也可把积分看作乘积态凸组合的极限。它可以有足以区分来源的相关性，却不因此成为纠缠态。使用联合效果读取这种相关性，同样不等于取得纠缠见证。B卷第2.1.6节给出的四点可分分解是其二份量子位实例。

这里的 $n$ 份来自获准重复调用的制备源。对单份未知态作 $\rho\mapsto\rho^{\otimes n}$ 不是一般线性通道；$n=2$ 的非仿射反例已经在式(TM.132)给出。因此这套观察语言的扩展需要来源权限、相位是否跨份保留以及记录如何共享，不能用免费克隆或旧摘要后处理替代。如果不同批次的相位重置规则不同，或者允许跨批次保留量子记忆，整个实验又是另一份联合协议，须重新计算可用关系，而不从单批结论自动推断。

#### 2.2.7 不可公度能谱：全部阶相同仍未必有精确时刻

**反例 2.14（紧轨道与精确时刻）。** 考虑固定三维模型
$$
H=\operatorname{diag}(0,1,\sqrt2),\qquad
|\psi\rangle=(|0\rangle+|1\rangle+|2\rangle)/\sqrt3,\qquad
|\varphi\rangle=(|0\rangle+|1\rangle-|2\rangle)/\sqrt3,
\qquad\rho=|\psi\rangle\langle\psi|,\quad\sigma=|\varphi\rangle\langle\varphi|.
\tag{TM.153}
$$

对张量基词 $a\in\{0,1,2\}^n$，记三种标签的占据数为 $k_0(a),k_1(a),k_2(a)$。则
$$
E(a)=k_1(a)+\sqrt2\,k_2(a),\qquad
\langle a|\psi^{\otimes n}\rangle=3^{-n/2},\qquad
\langle a|\varphi^{\otimes n}\rangle=3^{-n/2}(-1)^{k_2(a)}.
\tag{TM.154}
$$

如果 $E(a)=E(b)$，不可公度性强迫两个整数差 $k_1(a)-k_1(b)$ 与 $k_2(a)-k_2(b)$ 都为零；总份数固定再给 $k_0$ 相同。所以每个总能量块中的所有基词都有同一个 $(-1)^{k_2}$ 符号。投影到该块后，两个纯态向量只差一个共同符号，其密度矩阵相同。逐块相加，得到 $P_n(\rho)=P_n(\sigma)$ 对每个有限 $n$ 都成立。

由式(TM.139)，两态处于 $G=\overline{\{e^{-itH}\}}$ 的同一轨道。这也给一个不额外借用稠密性定理的闭包成员证明：$G$ 中每个矩阵都对角且第一对角元为一。若 $U\rho U^\dagger=\sigma$，则 $U|\psi\rangle$ 与 $|\varphi\rangle$ 只差全局相位；第一分量强迫该相位为一，余下两分量迫使 $U=\operatorname{diag}(1,1,-1)$。因此这份具体酉矩阵确在 $G$ 中。

但不存在任何实数 $t$，包括负数，精确实现该态变换。因为相同的第一分量再次固定全局相位，随后必须同时满足
$$
e^{-it}=1,\qquad e^{-it\sqrt2}=-1
\quad\Longrightarrow\quad
t=2\pi k,\qquad 2k\sqrt2\in2\mathbb Z+1,
\qquad k\in\mathbb Z,
\tag{TM.155}
$$

这不可能：$k=0$ 给偶数零，$k\ne0$ 给无理数。闭包成员意味着有时间序列在矩阵拓扑中逼近该酉，不意味着某一项已经相等。全部有限阶相容概率相同因此只能支持所证明的紧闭包轨道等价，不能把近似可达擅自改成存在一次精确时间演化。

#### 2.2.8 三维整数能谱把首次可分阶数推到任意大

**命题 2.15（任意高的首次可分阶）。** 另固定整数 $m\ge2$，取
$$
H_m=\operatorname{diag}(0,1,m),\qquad
G_m=\{\operatorname{diag}(1,z,z^m):|z|=1\},\qquad
\rho=|\psi\rangle\langle\psi|,\quad\sigma=|\varphi\rangle\langle\varphi|,
\tag{TM.156}
$$

其中 $|\psi\rangle,|\varphi\rangle$ 与式(TM.153)相同。这次时间作用以 $2\pi$ 为周期，$G_m$ 已经是该圆周连续像的紧闭群，没有额外的稠密时间闭包。两态不同轨道：若 $\operatorname{diag}(1,z,z^m)$ 把 $|\psi\rangle$ 送到 $|\varphi\rangle$ 的射线，第一分量令全局相位为一，第二分量令 $z=1$，第三分量却要求 $z^m=-1$，矛盾。

在 $n$ 份张量基中，等总能量要求
$$
k_1(a)+m k_2(a)=k_1(b)+m k_2(b)
\quad\Longleftrightarrow\quad
k_1(a)-k_1(b)=m\bigl(k_2(b)-k_2(a)\bigr).
\tag{TM.157}
$$

当 $n<m$ 时，左侧绝对值至多为 $n$，右侧若非零则绝对值至少为 $m$，所以双方只能为零。于是全部占据数相同，每个能量块内两个候选向量仍只差共同符号，得到
$$
P_n^{(m)}(\rho)=P_n^{(m)}(\sigma)\qquad(1\le n<m),
\tag{TM.158}
$$

这里上标 $(m)$ 指明以 $H_m$ 及其群定义平均，避免混同不同 Hamiltonian 的同名 $P_n$。

到 $n=m$ 时，若等能量的两份占据数不同，式(TM.157)的非零右侧绝对值只能等于 $m$。因此两个 $k_1$ 必分别为 $m$ 与零；$k_1=m$ 的词其余占据数均零，另一词必须有一个标签 $2$ 和 $m-1$ 个标签 $0$。所以所有新的相位敏感碰撞都在能量 $m$ 块内，且恰好发生于以下一维方向与 $m$ 个排列之间：
$$
\begin{aligned}
|u\rangle&=|1\rangle^{\otimes m},\qquad
|v_j\rangle=|0\rangle^{\otimes(j-1)}\otimes|2\rangle\otimes|0\rangle^{\otimes(m-j)},\\
|s\rangle&=\sum_{j=1}^m|v_j\rangle,\qquad
\langle u|s\rangle=0,\quad\|s\|=\sqrt m,\qquad a=3^{-m/2},\\
\Pi_m^{(m)}|\psi\rangle^{\otimes m}&=a(|u\rangle+|s\rangle),\qquad
\Pi_m^{(m)}|\varphi\rangle^{\otimes m}=a(|u\rangle-|s\rangle).
\end{aligned}
\tag{TM.159}
$$

$|v_j\rangle$ 两两正交，且均正交于 $|u\rangle$，证明所列范数关系。其他能量块要么只有同一占据数的排列，要么无此相位符号差，因此两候选的密度块相同。令
$$
\begin{aligned}
\Delta_m
&=P_m^{(m)}(\rho)-P_m^{(m)}(\sigma)
 =2\,3^{-m}(|u\rangle\langle s|+|s\rangle\langle u|),\\
\Delta_m\big|_{\operatorname{span}\{u,s/\sqrt m\}}
&=\begin{pmatrix}0&2\sqrt m/3^m\\2\sqrt m/3^m&0\end{pmatrix},
\end{aligned}
\tag{TM.160}
$$

在该二维子空间的正交补上差为零。因此非零特征值恰为 $\pm2\sqrt m/3^m$，得到精确半迹距离
$$
\boxed{
D\!\left(P_m^{(m)}(\rho),P_m^{(m)}(\sigma)\right)
=\tfrac12\|\Delta_m\|_1=\frac{2\sqrt m}{3^m}>0.
}
\tag{TM.161}
$$

这连同式(TM.158)证明此对来源首次可分的份数恰好为 $m$。一个简单但未必最优的效果是投影到 $(|u\rangle+|v_1\rangle)/\sqrt2$，两概率分别为 $2/3^m$ 与零，已经认证首次分离。下面计算使用全部该能量块时的最佳概率。

#### 2.2.9 精确单批区分概率及后选择代价

**命题 2.16（精确单批区分及后选择成本）。** 取 $\Delta_m$ 的正特征投影
$$
\begin{aligned}
|w_+\rangle&=(|u\rangle+|s\rangle/\sqrt m)/\sqrt2,\qquad
Q_m=|w_+\rangle\langle w_+|,\qquad [Q_m,H_m^{(m)}]=0,\\
q_+&=\operatorname{Tr}(Q_m\rho^{\otimes m})
 =\frac{m+1+2\sqrt m}{2\,3^m},\qquad
q_- =\operatorname{Tr}(Q_m\sigma^{\otimes m})
 =\frac{m+1-2\sqrt m}{2\,3^m}.
\end{aligned}
\tag{TM.162}
$$

相容性来自 $|w_+\rangle$ 完全位于能量 $m$ 块。概率由式(TM.159)与 $\langle w_+|(u\pm s)\rangle=(1\pm\sqrt m)/\sqrt2$ 直接得到。两候选等先验、一次实验使用这一批 $m$ 份样本时，测得 $Q_m$ 就判为 $\rho$、否则判为 $\sigma$，成功率为
$$
\boxed{
p_{\rm succ}^{(m)}=\tfrac12q_++\tfrac12(1-q_-)
=\tfrac12+\frac{\sqrt m}{3^m}.
}
\tag{TM.163}
$$

这也是完整相容效果合同下该单批实验的最优值。任意二元决策效果 $0\le F\le I$ 的成功率为 $\tfrac12+\tfrac12\operatorname{Tr}(F\Delta_m)$。将 $\Delta_m$ 分成正负谱部分，得到 $\operatorname{Tr}(F\Delta_m)\le\operatorname{Tr}(\Delta_{m,+})=2\sqrt m/3^m$；$Q_m$ 达到等号，且它自身相容。因此不需要额外假定所有非相容测量也可实施，就已达到这个 Helstrom 最优值。

若先读总能量，并仅保留能量 $m$ 的结果，两候选的保留概率相同：
$$
p_{\rm block}=\frac{m+1}{3^m},\qquad
|\chi_\pm\rangle=\frac{|u\rangle\pm|s\rangle}{\sqrt{m+1}},
\qquad
\rho_{\rm block}=|\chi_+\rangle\langle\chi_+|,
\quad\sigma_{\rm block}=|\chi_-\rangle\langle\chi_-|.
\tag{TM.164}
$$

归一化后的块差就是式(TM.160)除以 $p_{\rm block}$，同一个正特征方向仍最优。因此
$$
D(\rho_{\rm block},\sigma_{\rm block})=\frac{2\sqrt m}{m+1},\qquad
p_{\rm succ\mid block}=\tfrac12+\frac{\sqrt m}{m+1},\qquad
p_{\rm block}p_{\rm succ\mid block}+(1-p_{\rm block})\tfrac12
=\tfrac12+\frac{\sqrt m}{3^m}.
\tag{TM.165}
$$

最后一式把保留概率与条件成功率重新结算。其他块的密度矩阵完全相同，等先验下只能以二分之一成功，故条件优势不能脱离越来越小的保留概率单独当作完整实验优势。式(TM.163)与(TM.165)分别属于不后选择的单批任务和声明了保留事件的条件任务。

所有这些概率都以真实取得 $m$ 份共同相位样本及所需联合效果为前件。它们没有推出任意更大样本块、跨批联合操作或全部自适应策略的统一样本下界；改变批间相位和记忆合同，须重新定义候选联合态。当前结论已经足够区分“精确有不同读数”与“单批有显著成功优势”：首次可分时的优势恰为 $\sqrt m/3^m$，并随 $m$ 衰减。

#### 2.2.10 固定模型的有限性与跨模型的不统一

**命题 2.17（固定模型与跨模型量词）。** 式(TM.158)—(TM.161)在相同维数三中给出任意大的首次分离阶数。因此
$$
\boxed{
\forall N\ge1\ \exists m>N:
P_n^{(m)}(\rho)=P_n^{(m)}(\sigma)\ (1\le n\le N),
\qquad \sigma\notin G_m\cdot\rho,
\qquad P_m^{(m)}(\rho)\ne P_m^{(m)}(\sigma).
}
\tag{TM.166}
$$

对 $N=1$ 可取 $m=2$，其余取 $m=N+1$。故不存在只依赖维数 $d$、适用于任意 Hamiltonian 的统一足够阶数；即使抽象群都叫圆周群，三维表示中的整数权重也足以使阶数无界。固定 $G_m$ 后，B卷第2.2.3节的某个有限足够阶数仍存在，并且由这份例子至少为 $m$。这里没有证明整个三维态空间的最小足够阶数恰好等于 $m$，只证明这个来源对的首次分离阶数等于 $m$，以及完整轨道分离阶数的相应下界。

这与B卷第2.2.7节是两种不同边界：不可公度能谱的两态在紧闭包中同轨道，全部阶都不分离，却没有精确时间代表；整数能谱族中的两态本来不同紧轨道，每个固定实例最终可分离，但需要的份数不能只由维数控制。

如果末端效果只允许 $f(H^{(n)})$，而不允许简并块内部的相容读数，上述纯态候选在任意份数下仍有相同能量分布。原因是它们在全部张量计算基中的对角概率均为 $3^{-n}$，能量投影只对这些对角项求和；相对符号只存在于块内非对角项。故仅能量概率这个较小接口不能应用式(TM.138)的完整效果逆向。类似地，B卷第2.2.5节的 $|+\rangle\langle+|$ 与 $I/2$ 在任意份数下具有相同总能量分布，区分它们的 $Q_\pm$ 正是能量块内部的额外关系读数。

#### 2.2.11 已有供应、原始来源与本节所证明的边界

紧群矩轨道恢复的直接成熟来源是 Afonso S. Bandeira、Ben Blum-Smith、Joe Kileel、Jonathan Niles-Weed、Amelia Perry、Alexander S. Wein，*Estimation under group actions: recovering orbits from invariants*，[arXiv:1712.10163v4](https://arxiv.org/pdf/1712.10163v4)。固定版本 PDF第11页 Definition 2.4 定义 $T_n(\theta)=\mathbb E_g[(g\cdot\theta)^{\otimes n}]$；同页 Definition 2.5 后明确，第 $n$ 阶矩与全部齐次 $n$ 次不变量的取值包含同一信息。第25页 Proposition 3.39 将对每个轨道的唯一恢复等价于有限维不变量子空间具有分离性；第72页 Theorem A.31 给实不变量环的有限生成，第73页 Theorem A.32 证明紧群的不变量环分离全部轨道。后两项是该文明确归于成熟不变量理论的标准结果；本文直接复用其范围。

其对象对应是 $V=\operatorname{Herm}(d)$ 作为 $d^2$ 维实内积空间，内积为 $\operatorname{Tr}(AB)$，群作用为 $X\mapsto UXU^\dagger$。迹循环性证明这个作用实线性且正交；将无效作用核商去不改变轨道。取 Hermitian 实正交基 $A_j$，映射 $A_{j_1}\otimes_{\mathbb R}\cdots\otimes_{\mathbb R}A_{j_n}\mapsto A_{j_1}\otimes\cdots\otimes A_{j_n}$ 将实矩张量的坐标与 $\operatorname{Herm}(\mathcal H^{\otimes n})$ 的矩阵坐标对应，恰把该文的 $T_n(\rho)$ 送到式(TM.135)的 $P_n(\rho)$。这也说明为什么应使用 Hermitian 实表示：原文第11页脚注对直接采用复向量表示的矩约定另有说明，不能省略共轭后套用。正性与迹一仅把环境实空间限制到群不变的密度态子集，不破坏上述轨道分离结论。

该文第2页 Proposition 1.1 的证明也用到轨道分布及其支撑，但其完整统计任务在第10页 Problem 2.1 定义为独立观测 $y_i=g_i\cdot\theta+\xi_i$，其中各 $g_i$ 独立 Haar、各 $\xi_i$ 独立 Gaussian。这里一批 $n$ 份量子准备共享同一个群参数，实验通过允许的联合效果取得 Born 概率；两种数据取得模型不同。第11页及后续的高噪声样本复杂度、估计器和置信度结论不能未经统计归约直接迁移。原文 Definition 2.3 使用欧氏轨道距离，本节式(TM.146)使用半迹轨道距离；有限维范数拓扑相容，但数值常数仍需另换算，B卷第2.2.12节的精确常数由本文所列量子位计算承担。

仓内归属仍固定在 `237012b49d0d4729a86f7e9dd252d94df1de8dd0`。`docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md` 的外部章节31.9证明（约第10386行）验证三角多项式含常数、共轭封闭与分离点的 Stone–Weierstrass 条件；定理31.11（第10425行起，证明约第10444行）已通过一致稠密和 Riesz 唯一性由全部 Fourier 读数确定圆周测度，脚注约第10577行给出相应 Mathlib 供应。那里的对象是该卷构造的相位及剩余测度坐标；本节把同一成熟测度确定机制用于 $\mathcal D_d$ 上的轨道推前测度，并额外证明其全轨道支撑，没有把不同对象的测度定理当作逐字同一陈述。

`docs/develop/theory/BEDC-WM.md:219` 已明确观察纤维、群轨道和 twirling 像不能通用互换。式(TM.139)没有取消这条边界：它补入全部共同来源有限份数的语言和固定紧群作用，才证明全阶等价恰为轨道。`QUANTUM-REALITY.md` 的假设373.1（第49986—50024行）声明系统与参考为乘积、联合效果与总激发交换及其他辅助资源的归属；定理373.1（第50026—50048行）证明不变参考不能区分相位正负。本节只确定相位轨道，量子位正负纯态本来同轨道，因此并未从不变参考恢复原共同相位。B卷第2.1节关于固定独立参考和新同源样本的区别继续适用。

`D5/S3/QuantumChannels/Pinching.lean:16`、`:30`、`:35` 已有标准基量子位 pinching、幂等与 Hilbert–Schmidt 自伴；`D5/S3/QuantumChannels/PinchingProjection.lean:48`、`:68`、`:104` 已有正交、Pythagoras 与丢失相干量接口。B卷第2.1.8节所列 `Observer/Conditioning`、`DynamicClosureMinimality`、`AllFutureStatisticsSufficiency` 也各自承担一般记录投影、动态闭包或单算子未来统计供应。这些既有模块的已读陈述不自动成为任意 $n$ 的紧轨道定理；本节的普通证明也不冒领已完成新增形式化。定向查重只给出上述命中，不构成全仓无同类结果或全球原创性的认定。

成熟参考系框架来自 S. D. Bartlett、T. Rudolph、R. W. Spekkens，*Reference frames, superselection rules, and quantum information*，Reviews of Modern Physics 79（2007），555，[arXiv:quant-ph/0610030](https://arxiv.org/abs/quant-ph/0610030)，[doi:10.1103/RevModPhys.79.555](https://doi.org/10.1103/RevModPhys.79.555)。原始 TeX 来源为 [arXiv source](https://arxiv.org/src/quant-ph/0610030)：小节 “Lacking a phase reference implies a photon-number superselection rule” 的 `eq:LPNSSR2` 给能量／粒子数 pinching；“A general framework for reference frames and superselection rules” 的 `eq:AveragedState` 与 `eq:GinvariantPOVM2` 给 Haar 平均与不变效果；collective 情形明确共同参考导致同一个变换的张量作用，局部互不相关参考则分别平均。B卷第2.1.9节已给对应固定 PDF 版本的页码与公式锚点。这些内容支撑本节的成熟操作框架；没有据此声称该综述逐字证明了式(TM.139)的全部混态矩轨道结论。

Stone–Weierstrass 的固定源码为 Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d` 的 [Topology/ContinuousMap/StoneWeierstrass.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean)，第401行 `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`：紧空间上分离点的实／复连续函数星子代数稠密。Riesz 唯一性的同版本供应为 [MeasureTheory/Integral/RieszMarkovKakutani/Real.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean)，第409—420行的 `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`：两个正则测度对全部紧支撑实连续函数积分相同则测度相同。本节的 $K$ 紧，所以连续函数的支撑均紧，所需条件已在B卷第2.2.2节逐项说明。引用固定源码是复用候选与命题范围核对，不表示本节已经写出或编译了对这些声明的 Lean 应用。

Noetherian 供应为 [Stacks Project，§10.31，tag 00FM](https://stacks.math.columbia.edu/tag/00FM)：该节明确 Noetherian 环的理想有限生成与升链条件等价，Lemma 10.31.1 证明 Noetherian 环上的有限生成环仍 Noetherian，其中包含从系数环到有限变量多项式环的 Hilbert 基定理。B卷第2.2.3节将它作用于固定群作用所给的多项式坐标差；来源没有替本节给显式稳定阶数，更没有将一次相邻平台变成无限后续的证书。

这组结果把离散份数与完整轨道结构接成一条具体关系：增加同源样本可以使更高阶的共同相位关系进入边界；固定有限维群作用下，全部这些区别最终由某个有限阶的完整律承载。与此同时，参考群的闭包、具体表示的谱权重、真实可用效果以及统计取得成本仍各自保留。有限生成性、精确可区分性、实际时间可达性和有限资源可读性由不同命题承担，不能用其中一项替其余项结算。

#### 2.2.12 量子位二阶轨道恢复的精确误差与退化位置

**命题 2.18（量子位二阶恢复误差）。** 对B卷第2.2.5节的非退化量子位 Hamiltonian，可以把B卷第2.2.4节的定性连续逆进一步算成显式关系。以下始终固定能量基、共同相位的两份制备和全部所需相容效果。设两态轨道坐标分别为 $(p,r)$ 与 $(q,s)$，其中 $r=|c|$、$s=|c'|$，$r^2\le p(1-p)$、$s^2\le q(1-q)$。为避免混淆，$p,q$ 在本小节表示两份态的第一个能级占据概率，$q$ 不是前文的摘要映射。

任意两份量子位态之差为去迹 Hermitian 矩阵，其特征值为 $\pm\sqrt{(p-q)^2+|c-c'|^2}$。能量相位作用覆盖全部相对相位，因此在固定相干模下使 $|c-c'|$ 最小，恰好得到 $|r-s|$。故式(TM.146)的轨道距离为
$$
\boxed{d_G([\rho],[\sigma])=\sqrt{(p-q)^2+(r-s)^2}.}
\tag{TM.167}
$$

式(TM.149)中的 $P_2$ 矩阵全部在同一固定正交基 $00,11,\psi_+,\psi_-$ 下对角，特征概率为
$$
\Lambda(p,r)=\bigl(p^2,(1-p)^2,p(1-p)+r^2,p(1-p)-r^2\bigr).
\tag{TM.168}
$$

四项非负、和为一；相应四个投影都与总能量交换。因此在这个具体族中，输出态半迹距离恰好等于一份实际共同测量的四结果总变差。令 $\delta=p-q$、$t=\delta(1-p-q)$、$u=r^2-s^2$。前两个特征概率差的绝对值之和为 $2|\delta|$，后两个差为 $t+u,t-u$。使用实数恒等式 $\tfrac12(|t+u|+|t-u|)=\max(|t|,|u|)$，得到
$$
\boxed{
D_2:=D(P_2(\rho),P_2(\sigma))
=\operatorname{TV}(\Lambda(p,r),\Lambda(q,s))
=|p-q|+\max\bigl(|p-q|\,|1-p-q|,\ |r^2-s^2|\bigr).
}
\tag{TM.169}
$$

这已经给出所有合法两态的精确误差关系，无须只在目标附近线性化。因为 $|\delta|\le1$、$r,s\ge0$，有 $\delta^2\le|\delta|$、$(r-s)^2\le|r^2-s^2|$。另一方面，$|1-p-q|\le1$，且 $r+s\le1$，所以式(TM.169)中的两个最大值分支分别至多为 $|\delta|$、$|r-s|$。因此
$$
\boxed{
d_G([\rho],[\sigma])^2\le D_2\le2\,d_G([\rho],[\sigma]),
\qquad d_G([\rho],[\sigma])\le\sqrt{D_2}.
}
\tag{TM.170}
$$

下界使用 $D_2\ge|\delta|+|r^2-s^2|$。上界使用 $D_2\le|\delta|+\max(|\delta|,|r-s|)\le2\sqrt{\delta^2+(r-s)^2}$。两端均在同一实际态对上比较，没有分别选择互不相容的最优输入。

平方根逆界的常数一及最大正 Hölder 指数 $1/2$ 都不能改进。取合法态对
$$
p=q=\tfrac12,\qquad s=0,\quad0<r\le\tfrac12,\qquad
D_2=r^2,\qquad d_G=r.
\tag{TM.171}
$$

任意 $r>0$ 都达到平方根等号。若存在固定有限 $C$ 及 $\alpha>1/2$，在这些趋近态对上满足 $d_G\le C D_2^\alpha$，就要求 $r^{1-2\alpha}\le C$，与 $r\downarrow0$ 矛盾。这里的目标可以是最大混合态，退化无需发生在纯态边界。

固定目标 $(q,s)$ 且 $s>0$ 时，情况不同。$s\le1/2$，而式(TM.169)给
$$
\begin{aligned}
D_2&\ge|\delta|+(r+s)|r-s|
\ge|\delta|+s|r-s|
\ge s\sqrt{\delta^2+(r-s)^2},\\
&\boxed{d_G([\rho],[\sigma])\le D_2/s.}
\qquad
\text{取 }p=q,r=0\text{ 时： }D_2=s^2,\ d_G=s.
\end{aligned}
\tag{TM.172}
$$

第三个不等式可由 $|\delta|\ge s|\delta|$ 与 $|\delta|+|r-s|\ge\sqrt{\delta^2+(r-s)^2}$ 得到。所列达到输入是该占据概率下的合法对角态，所以对于每一份固定的非零相干目标，这个面向全部合法输入的线性常数 $1/s$ 是精确最优值。它不是声称目标附近的微分条件数也恰好为 $1/s$；这里比较的是全局输入域。

固定目标 $s=0$ 时，内部与端点都不能将局部逆指数提高到 $1/2$ 以上。若 $0<q<1$，取 $p=q$ 和任意充分小的 $r>0$，仍有 $D_2=r^2,d_G=r$。若 $q=0$，取合法纯态曲线；$q=1$ 时作能级交换，分别得到
$$
\begin{aligned}
(q,s)&=(0,0),\quad p=\varepsilon,\quad r=\sqrt{\varepsilon(1-\varepsilon)}:\\
&d_G=\sqrt\varepsilon,\qquad D_2=2\varepsilon-\varepsilon^2;\\
(q,s)&=(1,0),\quad p=1-\varepsilon,\quad r=\sqrt{\varepsilon(1-\varepsilon)}:\\
&d_G=\sqrt\varepsilon,\qquad D_2=2\varepsilon-\varepsilon^2,
\qquad 0<\varepsilon<1.
\end{aligned}
\tag{TM.173}
$$

因为 $2\varepsilon-\varepsilon^2$ 与 $\varepsilon$ 同阶，任何 $\alpha>1/2$ 的有限局部常数仍被 $\varepsilon\downarrow0$ 排除。这个结论已经使用端点的实际正性限制，不将内部的固定 $p$ 扰动照搬到端点。

端点还具有精确的非线性逆模。对目标 $(q,s)=(0,0)$，任意合法输入都满足 $r^2\le p(1-p)$，所以式(TM.169)的最大值固定取 $p(1-p)$；同时 $d_G^2=p^2+r^2\le p$。解出 $p$，得到
$$
\boxed{
D_2=2p-p^2,\qquad
 d_G\le\sqrt{1-\sqrt{1-D_2}}\qquad(0\le D_2\le1).
}
\tag{TM.174}
$$

对每个 $p\in[0,1]$ 取 $r=\sqrt{p(1-p)}$ 即达到等号，而 $p\mapsto2p-p^2$ 在 $[0,1]$ 上遍历 $[0,1]$，故这份点态误差界在整个输出误差范围内精确。目标 $(1,0)$ 以 $p$ 换成 $1-p$ 得同一模。

这些显式公式补足的是固定量子位模型的B卷第2.2.4节：轨道变量 $r$ 通过二阶统计中的 $r^2$ 进入读数，$r=0$ 处因此出现平方根逆退化。B卷第1.3节研究的是另一个问题——固定线性占据读数的目标纤维及其最近修复，不能把两个平方根机制当作同一任务或同一误差合同。这里 $D_2$ 可以由指定四结果测量的概率误差来表达，但实际有限样本估计的置信度与来源成本仍须另给；精确响应坐标和逆界本身不宣称已经取得这些统计资源。

### 2.3 能隙零关系的有限生成、闭路相位与精确副本阶数

B卷第2.2节已经用全部共同关系矩确定紧群轨道，并说明固定实际群作用存在某个有限足够阶数。本节把有限 Hamiltonian 的这份存在结论接到可以逐项描述的对象：能隙零权重单项式、它们的有限生成元，以及读取生成元的同能量联合效果。A卷第1.1节、A卷第1.4节、A卷第2.12节、A卷第2.13节与A卷第2.18节已经承担有限图的基本闭路相位与节点换基；这里使用一份明确的关联矩阵映射，区分那些图闭路与额外的整数能量共振，不重立已有循环—势定理。

以下仍是普通数学供应。固定来源、群作用和效果合同后证明的轨道分离，不等于制备一个选定代表元的物理协议，也不等于某个精确时刻的时间可达性。B卷第2.1节关于同源新准备、独立参考、仪器与控制权限的区分，以及B卷第2.2节关于统计取得和恢复误差的边界，继续适用。所有仓内来源定位在 `237012b49d0d4729a86f7e9dd252d94df1de8dd0`。

#### 2.3.1 有序矩阵坐标与实际零权重关系

**定义 2.19（有序能隙坐标与零关系）。** 固定 $d\ge1$、$H=H^\dagger$，并选定同一个正交能量基。允许重复能量；简并空间内部的基在本节始终固定。写
$$
H=\operatorname{diag}(E_0,\ldots,E_{d-1}),\qquad
z_{ij}(\rho)=\rho_{ij},\qquad w_{ij}=E_i-E_j,
\qquad
M_\alpha(\rho)=\prod_{i,j}\rho_{ij}^{\alpha_{ij}},
\quad |\alpha|=\sum_{i,j}\alpha_{ij},
\quad \alpha\in\mathbb N^{d\times d}.
\tag{TM.175}
$$

指数为零的因子定义为一，包括相应矩阵元为零的情形。沿实际时间作用，每个坐标乘 $e^{-itw_{ij}}$，故一个单项式不变的充要条件是其总权重为零。定义
$$
\begin{aligned}
S_H&=\left\{\alpha\in\mathbb N^{d\times d}:
\sum_{i,j}\alpha_{ij}(E_i-E_j)=0\right\},\\
M_\alpha(e^{-itH}\rho e^{itH})
&=e^{-it\sum_{ij}\alpha_{ij}(E_i-E_j)}M_\alpha(\rho),\\
\overline{\rho_{ij}}&=\rho_{ji},\qquad
\overline{M_\alpha(\rho)}=M_{\alpha^{\mathsf T}}(\rho).
\end{aligned}
\tag{TM.176}
$$

这里的不变量指作为全部 Hermitian 输入上的多项式函数保持，而不是某一份态上恰好取零。时间子群在 $G_H=\overline{\{e^{-itH}:t\in\mathbb R\}}$ 中稠密，坐标连续，所以对时间不变与对 $G_H$ 不变等价。使用全部有序坐标很重要：在 Hermitian 实空间的复值多项式代数中，共轭坐标已经由反向矩阵元供应；不能只保留上三角复坐标而丢弃其共轭。例如非退化量子位的 $|\rho_{01}|^2$ 正是 $\rho_{01}\rho_{10}$。

给定 $\alpha$、$n=|\alpha|\ge1$，把每个有序对 $(i,j)$ 重复 $\alpha_{ij}$ 次，按任意固定顺序列出，得到两个长度 $n$ 的字 $I=(i_1,\ldots,i_n)$、$J=(j_1,\ldots,j_n)$。令 $E_I=\sum_kE_{i_k}$，则
$$
\langle I|\rho^{\otimes n}|J\rangle=M_\alpha(\rho),\qquad
E_I-E_J=\sum_{ij}\alpha_{ij}(E_i-E_j),\qquad
\langle I|P_n(\rho)|J\rangle=
\begin{cases}
M_\alpha(\rho),&\alpha\in S_H,\\
0,&\alpha\notin S_H.
\end{cases}
\tag{TM.177}
$$

最后一式直接使用式(TM.137)的完整总能量 pinching。反过来，每个 $P_n$ 矩阵元都来自某个这样的 $\alpha$。因此全部共同关系矩包含的坐标，恰是全部次数的零权重单项式；没有再逐份平均或删去总能量简并块内部的交叉项。

#### 2.3.2 任意固定实能谱的有限生成：Dickson 短证

**命题 2.20（零关系的有限生成）。** 在 $\mathbb N^{d\times d}$ 上采用逐坐标偏序。令 $\mathcal B_H$ 为 $S_H\setminus\{0\}$ 的极小元集合。Dickson 引理说明有限个自然数坐标的逐坐标序没有无限反链，因而 $\mathcal B_H$ 有限。本处的 $0$ 必须排除，否则唯一极小元是零，不能生成非零关系。

更具体地，若 $\alpha,\beta\in S_H$ 且 $0<\beta\le\alpha$、$\beta\ne\alpha$，则 $\alpha-\beta$ 是非零自然数指数，并且总权重仍为零。所以 $\alpha$ 非极小当且仅当它可写成两个非零 $S_H$ 元素之和。由此，$\mathcal B_H$ 正是全部不可分解零权重指数，且
$$
\mathcal B_H=\operatorname{Min}(S_H\setminus\{0\}),\qquad
|\mathcal B_H|<\infty,\qquad
S_H=\left\{\sum_{\beta\in\mathcal B_H}n_\beta\beta:
 n_\beta\in\mathbb N\right\}.
\tag{TM.178}
$$

**生成性的证明。** 对 $|\alpha|$ 归纳。零指数是空和。给定非零 $\alpha$，非空有限集合 $\{\gamma\in S_H:0<\gamma\le\alpha\}$ 中有一个极小元 $\beta$，它也是整个 $S_H\setminus\{0\}$ 的极小元。若 $\alpha=\beta$ 已完成；否则 $\alpha-\beta\in S_H$ 且总次数更小，应用归纳假设，再加上 $\beta$。每一步总次数严格下降，故分解有限。证毕。

这份证明只使用坐标数 $d^2$ 有限以及零权重关系的减法闭合，不要求能量先写成整数或有理数。它适用于任意固定实能谱。由于每个对角单位指数都在 $\mathcal B_H$ 中，$d\ge1$ 时该集合非空，可以定义 $N_H=\max_{\beta\in\mathcal B_H}|\beta|$。式(TM.177)、乘积关系与B卷第2.2.2节的紧轨道分离共同给出
$$
\boxed{
\begin{aligned}
&\forall\rho,\sigma\in\mathcal D_d:\quad
\bigl[M_\beta(\rho)=M_\beta(\sigma)\quad\forall\beta\in\mathcal B_H\bigr]\\
&\qquad\Longleftrightarrow
\bigl[P_n(\rho)=P_n(\sigma)\quad\forall n\ge1\bigr]
\Longleftrightarrow \sigma\in G_H\cdot\rho,\\
&P_{N_H}(\rho)=P_{N_H}(\sigma)
\Longleftrightarrow \sigma\in G_H\cdot\rho.
\end{aligned}}
\tag{TM.179}
$$

正向的关键是：$\alpha=\sum n_\beta\beta$ 给 $M_\alpha=\prod M_\beta^{n_\beta}$，所以有限生成元的值决定全部零权重单项式；非零权重的 $P_n$ 坐标在两态上均为零。最后一行还使用式(TM.145)的部分迹，将 $P_{N_H}$ 送到各个所需的低阶。逆向由每个生成元的不变性得到。

本结论对零坐标、非满秩密度态以及能量简并均成立，未除以任何矩阵元。若 $E_i=E_j$，对应单个坐标指数已经是一次生成元，完整读数必须保留 $\rho_{ij}$ 的实部和虚部。若 $H$ 为数量矩阵，$S_H=\mathbb N^{d\times d}$、$N_H=1$，直接恢复全部密度矩阵。$N_H$ 是足够阶数；有限代数生成集未必是最小分离集，故一般不能仅由这个定义声称 $N_H$ 是最优值。

#### 2.3.3 半群生成也给完整多项式不变量接口

**命题 2.21（多项式不变量接口）。** 任意 Hermitian 实坐标的复值多项式，都可用有序矩阵元重写：对 $i<j$，实部和虚部分别为 $(z_{ij}+z_{ji})/2$、$(z_{ij}-z_{ji})/(2i)$；对角坐标本身为实数。将这样一个多项式在 $G_H$ 上平均，Haar 字符正交性逐项消去非零权重的单项式。因此若 $f$ 已经不变，其平均就是自身，并有
$$
\mathbb C[\operatorname{Herm}(d)]^{G_H}
=\operatorname{span}_{\mathbb C}\{M_\alpha:\alpha\in S_H\}
=\mathbb C[M_\beta:\beta\in\mathcal B_H].
\tag{TM.180}
$$

左侧表示定义在 Hermitian 实空间上的复值实多项式，不是删去共轭变量后的上三角全纯多项式环。限制到正性、迹一的密度态域仍给分离接口；这些约束没有被当作额外可自由变化的输入。用 $\operatorname{Re}M_\beta,\operatorname{Im}M_\beta$ 作为实读数即可表达相应实不变量；共轭成对的生成元可在核实后去除重复。式(TM.180)是成熟环面不变量论在当前实际表示中的实例，不另作为一般有限生成定理申报。

#### 2.3.4 精确整数表示与具有停止依据的有限盒算法

**命题 2.22（精确整数数据的有限盒算法）。** 有限性的数学证明不等于已知如何从一份数值谱表找全共振。若另外取得精确整数表示，可以使用成熟的有理锥和 Hilbert 基算法。令
$$
\Gamma_H=\sum_{i=0}^{d-1}\mathbb Z(E_i-E_0),\qquad
\Gamma_H=\bigoplus_{a=1}^{r}\mathbb Z\omega_a,\qquad
E_i-E_0=a_i\cdot\omega,\quad a_i\in\mathbb Z^r,\quad a_0=0.
\tag{TM.181}
$$

有限生成的 $\mathbb R$ 加法子群无挠，所以抽象地存在这样一组整数基；$\omega_a$ 在 $\mathbb Q$ 上线性独立。$r=0$ 包含纯数量 Hamiltonian。除去对共轭没有作用的公共数量相位以后，时间闭包的有效作用恰是 $\theta\in\mathbb T^r$ 给出的 $z_{ij}\mapsto e^{i(a_i-a_j)\cdot\theta}z_{ij}$。这里用的是 Kronecker 的紧环面稠密性或等价的字符消失判据；不是说每个 $\theta$ 都由某个精确有限时间取到。原矩阵群 $G_H$ 到该有效作用像的连续映射满射，故没有改变轨道。

把 $a_i-a_j$ 作为整数矩阵 $W$ 的各列，记 $q=d^2$，则
$$
W\in\mathbb Z^{r\times q},\qquad
S_H=\ker_{\mathbb Z}W\cap\mathbb N^q,
\qquad C_W=\{x\in\mathbb R^q:x\ge0,\ Wx=0\}.
\tag{TM.182}
$$

这是一个有理、pointed 的多面锥：若 $x,-x\ge0$，则 $x=0$。可以用精确有理多面计算取得其全部极射线，并在每条射线上选 primitive 整数向量 $v_1,\ldots,v_t\ge0$。若锥只有零点，生成问题平凡；当前完整矩阵坐标中至少有对角零权重射线。定义逐坐标和与有限集合
$$
B=\sum_{\ell=1}^t v_\ell,\qquad
\mathcal F_W=\{b\in\mathbb N^q:0\le b\le B,\ Wb=0\}.
\tag{TM.183}
$$

**有限盒完整性。** 任取 $\alpha\in S_H$。极射线生成锥，故存在 $\lambda_\ell\ge0$ 使 $\alpha=\sum_\ell\lambda_\ell v_\ell$。令 $n_\ell=\lfloor\lambda_\ell\rfloor$，并作同一个整数向量的分解：
$$
\alpha=\sum_{\ell=1}^t n_\ell v_\ell+b,\qquad
b=\sum_{\ell=1}^t(\lambda_\ell-n_\ell)v_\ell\in\mathbb Z^q,
\quad 0\le b\le B,\quad Wb=0.
\tag{TM.184}
$$

$b$ 为整数是因为左侧 $\alpha$ 与已扣除项均为整数；非负与盒界来自每个余系数属于 $[0,1)$，权重零来自线性性。每个 $v_\ell$ 也位于 $\mathcal F_W$，故 $\mathcal F_W$ 生成整个 $S_H$。于是可以有限枚举盒内的整数零权重点，并删除其中可分解的非零点；得到的正是 $\mathcal B_H$。一个盒内点若可分解，其两项也逐坐标不超过该点，因而都在同一盒内；所以这个删除判据本身是有限检查。特别地，全部不可分解元都在此盒内，$\sum_jB_j$ 是一份已由完整极射线数据认证的粗次数上界。

这给出真正的停止依据，与B卷第2.2.3节只观察一次相邻理想相等不同。验证一份候选生成表不能只查每行 $Wb=0$；还须有完整锥射线与上述有限盒证明、经认证的 Hilbert 基算法，或另一份覆盖全部零关系的证明。这里没有运行或声称交付某份一般 $W$ 的计算输出，也没有声称盒或最小生成集规模小。

式(TM.181)中的精确关系数据是额外输入。有限精度近似能谱不能一般认证所有整数关系：$\operatorname{diag}(0,1,m)$ 与 $\operatorname{diag}(0,1,m+\varepsilon)$ 可任意接近，而关系 $mE_1-(m-1)E_0-E_2=0$ 在 $\varepsilon\ne0$ 时失效，相应两字之间的效果也不再精确交换。对于任意描述方式的实数，不能凭本节的存在证明宣称已取得有效整数基；某个代数数表示、已验证结构关系或其他精确判定机制须另行供应。若要研究容许近似不对易或有限时间分辨率的装置，则需另写误差与操作合同。

#### 2.3.5 从每个零关系到同能量的实部、虚部效果

**命题 2.23（零关系的同能量效果）。** 给定一份非零 $\alpha\in S_H$，按B卷第2.3.1节构造 $n=|\alpha|$ 个有序坐标对和字 $I,J$。其核心对应是
$$
E_I=E_J,\qquad
M_\alpha(\rho)=\langle I|\rho^{\otimes n}|J\rangle.
\tag{TM.185}
$$

若 $I=J$，投影 $|I\rangle\langle I|$ 的概率就是实数 $M_\alpha(\rho)$。若 $I\ne J$，两个计算基字正交，对任意已控制的块内相位 $\theta$ 定义
$$
\begin{aligned}
|v_\theta\rangle&=(|I\rangle+e^{i\theta}|J\rangle)/\sqrt2,
\qquad Q_\theta=|v_\theta\rangle\langle v_\theta|,
\qquad [Q_\theta,H^{(n)}]=0,\\
q_\theta(\rho)&=\operatorname{Tr}(Q_\theta\rho^{\otimes n})
=\frac{\langle I|\rho^{\otimes n}|I\rangle+
       \langle J|\rho^{\otimes n}|J\rangle}{2}
 +\operatorname{Re}(e^{i\theta}M_\alpha(\rho)).
\end{aligned}
\tag{TM.186}
$$

$Q_\theta$ 是秩一投影，因此 $0\le Q_\theta\le I$；其像落在同一个总能量特征空间，故交换关系成立。展开 $\langle v_\theta|\rho^{\otimes n}|v_\theta\rangle$ 得到所列概率。四个相位设置中的两组差给出
$$
\boxed{
\operatorname{Re}M_\alpha(\rho)=\frac{q_0(\rho)-q_\pi(\rho)}2,
\qquad
\operatorname{Im}M_\alpha(\rho)=
\frac{q_{-\pi/2}(\rho)-q_{\pi/2}(\rho)}2.
}
\tag{TM.187}
$$

虚部的符号由式(TM.186)固定：$\theta=\pi/2$ 的交叉项是 $-\operatorname{Im}M_\alpha$。每组正负投影还可与其共同支撑的正交补组成一份三结果测量；概率差使用全部批次，不删除正交补结果。这是A卷第2.12节两相位强度恢复机制在一份归一化 Born 测量中的具体对应，基线概率由同一密度矩阵给出，不把未归一化强度当成概率。

同能量块内的相对相位不需要外接时间相位参考，因为共同时间作用只在该块乘一个数量相位。但实际读取实部与虚部仍要求相应块内基选择和控制；“数学上对易”不自动意味着某个受限菜单可执行这些投影。若采用B卷第2.1.3节的零 Hamiltonian 指针、纯空白、所需守能联合酉及读出合同，则可对这些效果使用既有扩张；制备、控制与复位成本继续计入。仅可测总能量的装置，或只可使用固定基下实对称效果的装置，不满足这份完整复读数合同。

若先后选择总能量或两字子空间，必须同时保留其通过概率与失败记录，才能还原式(TM.186)的未条件化概率。生成元次数 $n$ 表示同一批实际取得的 $n$ 份同源准备，条件于同一个未知相位独立；它不是把一份未知态免费复制 $n$ 次。整数指数的二进制表示、重复平方的短算术电路、有限个生成元，以及有限个测量设置，都不自动给出小副本数、短物理时间、有限样本精确概率或稳定的逆误差。B卷第2.2.12节已经给出二阶读数在零相干处的平方根逆退化；高次单项式还可能给很小的区分信号。

#### 2.3.6 固定实际非零支持上的整数格基分离

**命题 2.24（固定实际支持的格基分离）。** 完整 Hilbert 基对所有零模式同时有效，但其生成集合可能很大。若实际非零支持已经给定，可以改用整数关系格的基，只承担轨道分离，不要求生成整个全空间多项式环。

选每个非对角无向坐标对的一条方向作为代表，记复坐标为 $z_e$、整数权重为 $w_e$。反向坐标由 Hermitian 共轭确定。先保留全部对角项及各 $|z_e|$；两份候选的这些值若相同，其非零支持 $\mathcal S$ 也相同。在此固定支持上令
$$
\mathcal S=\{e:z_e\ne0\},\qquad
W_{\mathcal S}=(w_e)_{e\in\mathcal S},\qquad
L_{\mathcal S}=\{k\in\mathbb Z^{\mathcal S}:W_{\mathcal S}k=0\},
\qquad
L_{\mathcal S}=\bigoplus_{\ell=1}^{q_{\mathcal S}}\mathbb Z k^{(\ell)}.
\tag{TM.188}
$$

这里 $q_{\mathcal S}=|\mathcal S|-\operatorname{rank}W_{\mathcal S}$；空支持允许空基。Smith normal form 可以从已给的精确整数矩阵计算一份完整的整数核基，不能用一个仅在 $\mathbb Q$ 上张成的、但遗漏整数格指数的列表替代。对每个核基向量定义普通多项式
$$
F_k(z)=\prod_{k_e>0}z_e^{k_e}
       \prod_{k_e<0}\overline{z_e}^{-k_e},
\qquad \deg F_k=\|k\|_1,\qquad
\sum_e k_ew_e=0.
\tag{TM.189}
$$

因此 $F_k$ 是B卷第2.3.5节可读取的零权重单项式，没有在实际效果中作负幂。对角项可一次读取，$|z_e|^2=z_e\bar z_e$ 可二次读取；若某个 $w_e=0$，该坐标相位本身已是一阶不变量。以下分离结论包含这种能量简并情形。

**固定支持分离命题。** 对任意两份具有相同对角项、相同逐坐标模长的密度态，令 $\mathcal S$ 为其共同实际非零支持。它们同属一个 $G_H$ 轨道，当且仅当所有 $F_{k^{(\ell)}}$ 的值相同。

**证明。** 在 $\mathcal S$ 上可以定义单位模比值 $\delta_e=z_e(\sigma)/z_e(\rho)$。由式(TM.189)及 $|\delta_e|=1$，有
$$
\frac{F_k(z(\sigma))}{F_k(z(\rho))}=\delta^k,
\qquad
\delta^k=1\ (k\in L_{\mathcal S})
\quad\Longleftrightarrow\quad
\delta_e=e^{iw_e\cdot\theta}\ (e\in\mathcal S)
\text{，某个 }\theta\in\mathbb T^r.
\tag{TM.190}
$$

左侧分母非零是因为只对实际非零支持取乘积。对整数格基验证 $\delta^k=1$ 足以对全部整数线性组合验证，负整数次幂在单位圆上合法。

为核实第二个等价，考虑由 $W_{\mathcal S}^{\mathsf T}$ 给出的环面同态 $\mathbb T^r\to\mathbb T^{\mathcal S}$。Smith normal form 给左右幺模整数矩阵，将其变成
$$
P W_{\mathcal S}^{\mathsf T}Q
=\operatorname{diag}(d_1,\ldots,d_s,0),
\qquad d_j\ge1,\qquad s=\operatorname{rank}W_{\mathcal S}.
\tag{TM.191}
$$

整数幺模换基在环面上是自同构，每个映射 $u\mapsto u^{d_j}$ 在 $U(1)$ 上满射，所以变换后的像恰为前 $s$ 个任意单位相位、其余坐标等于一。其所有消失字符正是 $\ker_{\mathbb Z}W_{\mathcal S}$。因此式(TM.190)确实刻画像；不需要假定各 $d_j=1$，有限稳定子不会制造遗漏。得到 $\theta$ 后，它把全部非零坐标运输到对应值，零坐标和对角项也相同，从而给同轨道。反向来自 $F_k$ 不变。证毕。

这是固定支持上的模长加有限相位关系接口。它并不说一份整数核基经非负乘法就生成所有零权重指数；整数格生成与非负半群生成不同。引用 Laurent 代数时也须允许逆，或同时列出正负基向量，不能把单向基单项式称为普通多项式代数的完整生成集。支持已知时的除法仅用于证明或后处理，不授予跨零坐标的连续相位归一化。

#### 2.3.7 全支持格基在零坐标处失效的实际正定反例

**反例 2.25（零坐标使全支持格基失效）。** 固定三能级 $H=\operatorname{diag}(0,1,2)$，按下三角坐标取
$$
(z_1,z_2,z_3)=(\rho_{10},\rho_{21},\rho_{20}),\qquad
W=(1,1,2),\qquad
k^{(1)}=(1,-1,0),\quad k^{(2)}=(2,0,-1).
\tag{TM.192}
$$

这确是一份完整整数核基：若 $x+y+2z=0$，则 $(x,y,z)=(-y)k^{(1)}+(-z)k^{(2)}$。取 $a=1/12$ 并令
$$
\rho_+=\begin{pmatrix}1/3&0&a\\0&1/3&a\\a&a&1/3\end{pmatrix},\qquad
\rho_-=\begin{pmatrix}1/3&0&-a\\0&1/3&a\\-a&a&1/3\end{pmatrix},
\qquad
\operatorname{spec}\rho_\pm=\{1/3,1/3-\sqrt2a,1/3+\sqrt2a\}.
\tag{TM.193}
$$

两态的迹为一，最小特征值严格为正；谱可由中心顶点连接两个叶子的非对角块直接求出，符号只改变连接向量的方向而不改变其范数 $\sqrt2a$。它们对角项与逐坐标模长全部相同，但
$$
F_{k^{(1)}}=z_1\bar z_2=0,\qquad
F_{k^{(2)}}=z_1^2\bar z_3=0\quad\text{在两态上均成立},
\qquad
z_2^2\bar z_3(\rho_+)=a^3,\quad
z_2^2\bar z_3(\rho_-)=-a^3.
\tag{TM.194}
$$

最后一个单项式权重 $2\cdot1-2=0$，已经区分两轨道。全支持格基的两个值在 $z_1=0$ 时同时消失，不能再通过所需除法取得最后一个值。对实际支持 $\mathcal S=\{2,3\}$ 重算整数核，则基向量 $(2,-1)$ 正好供应它。完整 Hilbert 基在所有零模式上都有效，故不存在同样的遗漏。

实际含噪测量若想采用支持分支，还需要已认证支持、最小非零幅度承诺或另一份可验证的分支规则；有限样本没有一般的“精确零”判别。没有这种额外合同，应保留无需除法的全局生成元及其实际误差，不能把非零支持上的 Laurent 恢复公式直接延伸到零坐标。

#### 2.3.8 关联矩阵把图闭路接到能量共振

**命题 2.26（图闭路与能量共振）。** 在全部有序矩阵坐标上，令 $B_{\rm inc}$ 的 $(i,j)$ 列为 $e_i-e_j\in\mathbb Z^d$，把该坐标视作从 $j$ 指向 $i$ 的边；对角坐标是自环，列为零。再令 $A$ 的第 $i$ 列为式(TM.181)中的 $a_i$。则
$$
(B_{\rm inc})_{ij}=e_i-e_j,\qquad
A=(a_0\ \cdots\ a_{d-1}),\qquad
W=A B_{\rm inc}.
\tag{TM.195}
$$

这就是两类相位问题的实际参数映射。完整顶点相位换基 $D=\operatorname{diag}(e^{i\chi_i})$ 使 $\rho_{ij}\mapsto e^{i(\chi_i-\chi_j)}\rho_{ij}$，单项式对全部这些换基不变恰好要求顶点收支向量 $B_{\rm inc}\alpha$ 为零；能量相位只要求经过 $A$ 后为零。因此
$$
B_{\rm inc}\alpha=0\ \Longrightarrow\ W\alpha=0,
\qquad
\text{额外能量共振允许 }B_{\rm inc}\alpha\ne0\text{ 而 }A B_{\rm inc}\alpha=0.
\tag{TM.196}
$$

$B_{\rm inc}\alpha=0$ 的非负整数指数是每个顶点流入流出平衡的有向多重边计数。只要还有边，从任一边开始沿有剩余出边的方向走；流量平衡保证到达的顶点还有后续出边，有限顶点使路径出现闭环。取其中一个有向简单闭路，扣除每条所用边一次，仍保持非负与流量平衡，总边数下降。反复处理得到简单有向闭路分解。故完整顶点相位群的零权重半群由简单闭路生成，包括一次对角环和二次往返环。对闭路 $\gamma=(i_0,i_1,\ldots,i_{\ell-1},i_0)$，相应量为
$$
C_\gamma(\rho)=\rho_{i_0i_1}\rho_{i_1i_2}\cdots\rho_{i_{\ell-1}i_0}
=\operatorname{Tr}(P_{i_0}\rho P_{i_1}\rho\cdots P_{i_{\ell-1}}\rho),
\qquad P_i=|i\rangle\langle i|.
\tag{TM.197}
$$

方向采用关联列的约定时，这个书写顺序表示反向遍历同一闭路；乘积的顶点指数仍逐项抵消。其权重为零，所以也属于B卷第2.3.5节的多副本合法读数。这个迹乘积恒等式迁移的是既有锚定耦合矩阵的代数结构，没有要求实际装置能把非酉算子 $\rho$ 当作一个控制步骤连续施加。

在固定非零无向支持上，两态若模长相同，边比值属于 $U(1)$，逆边比值为逆。沿路径相乘给路径群胚上的交换群值运输。全部闭路比值为一，当且仅当比值来自顶点势；这正是 `ZeroLoopPotentialEquivalence.closed_path_zero_iff_exists_potential` 对 $U(1)$ 的加法记法的直接实例。逐连通分量应用即可，孤立顶点无额外边条件。A卷第1.4节已有的生成树规范因而给：对角项、边模长及一组基本闭路复相位确定矩阵到完整顶点相位换基。零边先删去；归一化的环相位在含零边的环上没有定义，而未归一化乘积式(TM.197)始终有定义。

该结论对 Hamiltonian 轨道充分的精确关系条件是
$$
\ker_{\mathbb Z}(A B_{{\rm inc},\mathcal S})
=\ker_{\mathbb Z} B_{{\rm inc},\mathcal S}.
\tag{TM.198}
$$

这里 $\mathcal S$ 是所比较的固定非零边支持；左侧没有多于图闭路的能量零关系，故B卷第2.3.6节的相位比值判据与完整顶点相位判据一致。一个对全部支持都充分的条件是 $E_1-E_0,\ldots,E_{d-1}-E_0$ 在 $\mathbb Q$ 上独立：若 $b\in\mathbb Z^d$、$\sum_i b_i=0$ 且 $\sum_i b_iE_i=0$，则全部 $b_i=0$。否则一般还有式(TM.196)右侧的关系，基本图闭路数据可能只恢复一个更大的顶点相位轨道，不能替代较小的 $G_H$ 轨道。

这种区分也保护能级简并边界：$E_i=E_j$ 时，单个 $\rho_{ij}$ 已对能量群不变，却未必对任意独立顶点换基不变。固定秩一锚点将共同酉自由度限制成顶点相位，并没有进一步证明那些顶点相位都属于实际时间闭包。若连秩一锚点都未取得，只知简并能量投影，则可用坐标和实验标签还需另行说明。

#### 2.3.9 原有纯态对的首次 $m$ 阶来自非闭路共振

**命题 2.27（纯态对的首次副本阶数）。** 继续B卷第2.2.8节的 $H_m=\operatorname{diag}(0,1,m)$，整数 $m\ge2$。该节纯态对的交叉矩阵元可以直接写成
$$
M_m(\rho)=\rho_{12}\rho_{10}^{m-1},\qquad
\deg M_m=m,\qquad
(1-m)+(m-1)\cdot1=0,
\qquad
B_{\rm inc}\alpha=me_1-(m-1)e_0-e_2\ne0.
\tag{TM.199}
$$

它在能量映射后为零，却不是图的顶点平衡流。对应两字是 $I=1^m$、$J=(2,0,\ldots,0)$，恰为B卷第2.2.8节所用的同能量 $m$ 交叉项。对该节已经固定的
$$
\psi=(1,1,1)/\sqrt3,\qquad \phi=(1,1,-1)/\sqrt3,
\qquad
M_m(|\psi\rangle\langle\psi|)=3^{-m},\quad
M_m(|\phi\rangle\langle\phi|)=-3^{-m}.
\tag{TM.200}
$$

全部普通闭路乘积却相同，因为两态由一个顶点对角相位变换关联；对于纯态密度矩阵，闭路中的各振幅相位本就逐点抵消，乘积是相应模平方之积。因此原有首次 $m$ 阶结论完全保留，并精确展示了图闭路之外的能量关系。它只针对这对来源，不等于对整个三维密度态空间的统一最小阶。

#### 2.3.10 整数零和列给 $H_m$ 的全部态上界

**命题 2.28（整数能谱的全态副本上界）。** 为明确统一量词，定义固定实际 Hamiltonian 的最小轨道分离阶
$$
N_{\rm orb}(H)=\min\left\{N\ge1:
\forall\rho,\sigma\in\mathcal D_d,\quad
P_N(\rho)=P_N(\sigma)\Longleftrightarrow\sigma\in G_H\cdot\rho\right\}.
\tag{TM.201}
$$

B卷第2.3.2节保证集合非空；这个定义固定完整密度态域与具体表示，不仅固定抽象群名称。对 $H_m$，所有非零能隙权重属于
$$
\{\pm1,\ \pm(m-1),\ \pm m\},\qquad m\ge2.
\tag{TM.202}
$$

一个不可分解指数若含零权重坐标，只能是该坐标的一次单位指数，否则已有 proper 零权重分量。其余不可分解指数可展开成只含式(TM.202)中非零整数的零和列；如果这个列有 proper 非空零和子列，相应坐标重数就是可分解指数，矛盾。不同矩阵坐标恰有相同数值权重也不影响这个对应，因为子列仍保留其实际坐标身份。

使用成熟的不可分解整数零和长度界可直接得到上界；下面给出所需弱形式的完整短证。设这样一个列长 $L$，最大正项为 $A$，最大负项绝对值为 $B$。从任一正项开始，每次当前部分和为正就选一个尚未使用的负项，为负就选一个尚未使用的正项。所需符号总能找到，因为剩余项之和是当前部分和的相反数。不可分解性禁止提前出现零；按所述选择，每个 proper 部分和都在整数区间 $[1-B,A]$ 中。两个 proper 部分和若相同，其间已经选择的非空 proper 子列和为零，也被禁止。因此
$$
\{s_1,\ldots,s_{L-1}\}\subset
([1-B,A]\cap\mathbb Z)\setminus\{0\},\qquad
s_j\ne s_k\ (j\ne k),\qquad
L-1\le A+B-1,\quad L\le A+B.
\tag{TM.203}
$$

区间共有 $A+B$ 个整数，去掉零剩 $A+B-1$ 个。范围保持也可逐步核对：正整数部分和至少为一，减去至多 $B$ 的负项后不低于 $1-B$；负整数部分和至多为负一，加上至多 $A$ 的正项后不高于 $A-1$。初始正项不大于 $A$，于是归纳成立。

在式(TM.202)中 $A,B\le m$。若 $A=B=m$，列中已经含有 $m,-m$ 这个二项零和子列，不可分解性强制整列只有两项；其余情形至少一边不大于 $m-1$，故 $A+B\le2m-1$。零权重的一次情况也满足同一上界。因此
$$
\max_{\beta\in\mathcal B_{H_m}}|\beta|\le2m-1,
\qquad
\boxed{N_{\rm orb}(H_m)\le2m-1.}
\tag{TM.204}
$$

$m=2$ 时权重 $1$ 与 $m-1$ 相同，论证仍逐实际项计算；全部不可分解次数至多三。这里没有遗漏单个零权重项或重复权重坐标。

#### 2.3.11 正定稀疏态实现 $2m-1$ 的精确下界

**命题 2.29（稀疏正定态达到精确下界）。** 令 $m\ge2$、$a=1/12$、$\varphi_m=\pi/(m-1)$，取同一能量基中的两态
$$
\rho_m=\begin{pmatrix}
1/3&0&a\\0&1/3&a\\a&a&1/3
\end{pmatrix},\qquad
\sigma_m=\begin{pmatrix}
1/3&0&ae^{-i\varphi_m}\\
0&1/3&a\\
ae^{i\varphi_m}&a&1/3
\end{pmatrix}.
\tag{TM.205}
$$

它们的 Hermitian 对称与迹一可直接读出。将非对角部分视作顶点 $2$ 连接两个叶子的矩阵，其连接向量范数为 $\sqrt{|a|^2+|a|^2}=\sqrt2a$，其非零特征值是这个范数的正负值。因此
$$
\operatorname{spec}\rho_m=\operatorname{spec}\sigma_m
=\left\{\frac13,\frac13-\sqrt2a,\frac13+\sqrt2a\right\},
\qquad \frac13-\frac{\sqrt2}{12}>0.
\tag{TM.206}
$$

两者都是实际正定密度矩阵，而不只是松弛的复坐标表。其共同非零相干是 $z_1=\rho_{21}$、$z_2=\rho_{20}$ 及各自共轭，权重分别为 $m-1,m$。任何在这些坐标上非零的单项式，记两个坐标相对于其共轭的净指数为 $k_1,k_2$。零权重要求
$$
(m-1)k_1+mk_2=0
\quad\Longleftrightarrow\quad
(k_1,k_2)=\ell(m,-(m-1)),\quad\ell\in\mathbb Z,
\qquad
\ell\ne0\ \Longrightarrow\ |k_1|+|k_2|\ge2m-1.
\tag{TM.207}
$$

等价使用 $\gcd(m,m-1)=1$。一个次数为 $n$ 的单项式总有 $|k_1|+|k_2|\le n$；所以 $n<2m-1$ 时，任何非零零权重单项式都必须 $k_1=k_2=0$，只依赖共同对角项与模长，不能看到 $\varphi_m$。使用零坐标 $\rho_{01},\rho_{10}$ 的单项式在两态上均为零。结合式(TM.177)，得到
$$
\begin{aligned}
&P_n(\rho_m)=P_n(\sigma_m)\qquad(1\le n<2m-1),\\
&M_*(\rho)=\rho_{21}^{\,m}\rho_{02}^{\,m-1},\qquad \deg M_*=2m-1,\\
&M_*(\rho_m)=a^{2m-1},\qquad
M_*(\sigma_m)=a^{2m-1}e^{-i(m-1)\varphi_m}=-a^{2m-1}.
\end{aligned}
\tag{TM.208}
$$

选择 $\varphi_m=\pi/(m-1)$ 保证所有 $m\ge2$ 都发生符号翻转；若无条件只取 $\pi$，某些 $m$ 会使这个见证重新相同。该指数支持在权重 $m-1,-m$ 的两个坐标上，最小正整数抵消次数分别为 $m,m-1$，因而它本身也是不可分解零权重生成元。

这份区分有实际的相容效果。置 $L=2m-1$，取两个长度 $L$ 的计算基字
$$
I=(\underbrace{2,\ldots,2}_{m},\underbrace{0,\ldots,0}_{m-1}),\qquad
J=(\underbrace{1,\ldots,1}_{m},\underbrace{2,\ldots,2}_{m-1}),\qquad
E_I=E_J=m^2,
\quad \langle I|\rho^{\otimes L}|J\rangle=M_*(\rho).
\tag{TM.209}
$$

两字不同而正交。投影到其等权实叠加，对这两态所有对角字概率均为 $3^{-L}$，所以
$$
\begin{aligned}
Q_*&=\frac{(|I\rangle+|J\rangle)(\langle I|+\langle J|)}2,
\qquad 0\le Q_*\le I_{\mathcal H^{\otimes L}},\qquad[Q_*,H_m^{(L)}]=0,\\
\operatorname{Tr}(Q_*\rho_m^{\otimes L})&=3^{-L}+a^L,\qquad
\operatorname{Tr}(Q_*\sigma_m^{\otimes L})=3^{-L}-a^L,
\qquad \text{概率差}=2a^L>0.
\end{aligned}
\tag{TM.210}
$$

两个概率均合法，因为 $0<a<1/3$。其值是完整批次的未条件化概率，没有借后选择放大。这已经证明 $P_L$ 不同、两态不同紧轨道，以及任何小于 $L$ 的阶数都不能分离全部合法态。与式(TM.204)合并，得到精确结论
$$
\boxed{
N_{\rm orb}\!\left(\operatorname{diag}(0,1,m)\right)=2m-1
\qquad\text{对每个整数 }m\ge2.
}
\tag{TM.211}
$$

该统一结论包含B卷第2.2.8节的纯态对，但那一对仍在第 $m$ 阶就首次分离；较坏输入是这里的稀疏正定态。式(TM.210)只给一份具体效果的概率差，未计算此新态对全部 $L$ 份效果的 Helstrom 最优值，也未由小概率推出任意更大批次或自适应协议的样本下界。若 $m$ 用二进制编码，较短的整数描述仍对应 $2m-1$ 份的实际最低统一阶数；计算表示长度与制备资源没有因此相同。

#### 2.3.12 成熟所有者、已有闭环接口与结论边界

零权重多项式机制的直接成熟来源是 Peter Bürgisser、M. Levent Doğan、Visu Makam、Michael Walter、Avi Wigderson，*Polynomial time algorithms in invariant theory for torus actions*，固定 [arXiv:2102.07727v1](https://arxiv.org/abs/2102.07727v1)，2021年2月15日；会议版本 [doi:10.4230/LIPIcs.CCC.2021.32](https://doi.org/10.4230/LIPIcs.CCC.2021.32)。引用 [v1 原始源码](https://arxiv.org/src/2102.07727v1)中的 `torus-oci.tex`：§3 “Invariants and orbit closures of torus actions” 的 `pro:3.1` 明确单项式不变当且仅当非负指数在整数权重矩阵的核中，并且不变量环由这些单项式线性张成；§4 “Generating Laurent polynomials and rational invariants” 的 `prop:inv-Laurent`、`thm:smith`、`algo-lattice` 给固定支持的整数关系格和 Smith normal form，`th:laurent` 明确采用含除法的算术电路。调用该接口时保留 Laurent 逆幂，不把一份单向整数格基冒作全局非负半群生成集。§8 “Orbit problems for compact tori” 的首个 proposition 证明：同一紧环面轨道当且仅当同一复环面轨道并且逐坐标绝对值相同。其算法复杂度结论假定输入是精确整数权重矩阵及具有给定比特长度的 Gaussian rational 向量；它没有为未知量子态供应精确坐标，也没有把短电路转成少副本实验。

有理锥 Hilbert 基的成熟来源可见 Winfried Bruns、Richard Sieg、Christof Söger，*The subdivision of large simplicial cones in Normaliz*，固定 [arXiv:1605.07440v1](https://arxiv.org/abs/1605.07440v1)，2016年5月24日；[原始源码](https://arxiv.org/src/1605.07440v1) `Normaliz_ICMS_Extended_Abstract_2016_arxiv.tex` 的§2 “Hilbert basis and Hilbert series” 明确：由 Gordan 引理，$C\cap L$ 有限生成；pointed 情形具有唯一最小 Hilbert 基。式(TM.183)—(TM.184)给这份成熟机制在非负核锥上的完整有限盒证明。B卷第2.3.2节的 Dickson 论证是同一有限生成现象在当前零关系集合上的短证明；它不要求先算出整数 presentation，但也不额外获得有效实数关系判定。

式(TM.204)的整数极值已有精确原始所有者：Marvin Sahs、Papa Sissokho、Jordan Torf，*A zero-sum theorem over Z*，固定 [arXiv:1212.2690v1](https://arxiv.org/abs/1212.2690v1)，2012年12月12日；引用 [原始源码](https://arxiv.org/src/1212.2690v1)。其 Theorem 1（源码 `thm:1`）对不可分解的正整数多重集对 $\{A,B\}$ 给出 $|A|\le\max B$、$|B|\le\max A$，从而对非零整数 $[-k,k]$ 上的不可分解零和列，最大长度为 $2k-1$，$k>1$。原文式(2)给 $k-1$ 个 $k$ 与 $k$ 个 $k-1$ 的达到结构，Corollary 1进一步分类达到者。本节的 $m$ 与 $m-1$ 两个能隙及重数直接对应这一既有极值结构；新增在当前研究里的连接是实际 Hermitian 零模式、正定密度矩阵、同能量效果和最小统一副本阶数的共同实现，不据此声称新的整数零和定理或文献原创。

仓内闭路—势的直接 Lean 所有者是 `D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.lean` 的 `closed_path_zero_iff_exists_potential`。其前件是连通路径群胚、取值于任意 `AddCommGroup` 的路径代价、组合可加和逆向取负；结论是全部闭路为零当且仅当路径代价为顶点势差。本节在每个实际非零支持分量上，将边相位比的乘法运输写成 $U(1)$ 的加法记法，逐项履行这些前件，故一般机制应直接归于该声明。`D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace.lean` 的 `closed_walk_mod_two_mem_simple_cycle_span`、`finite_graph_cycle_space` 已有二元域下的简单闭路、基本闭路基与锚定提升；其系数是 $\mathbb Z/2\mathbb Z$，不能将此形式陈述改报为本节一般整数关系格或 $U(1)$ 环面的全部结论。A卷第1.1节、A卷第1.4节、A卷第2.12节、A卷第2.13节与A卷第2.18节已经给出的相位生成树、两读数与误差接口仍是相应普通供应，不重复取得新增形式化名义。

`docs/develop/theory/QUANTUM-REALITY.md` 第364.1节（固定快照原始48851—48902行）给独立标定秩一锚点与顶点相位剩余自由度；第365节“闭路提供剩余的相位数据”（原始49026—49056行）给式(TM.197)对应的耦合矩阵闭路乘积及生成树恢复；第370.1节（原始49630—49660行）保留控制词正性、已知维数、独立锚点和整个连接分量可达等实际前件。把其中的 Hermitian 内容矩阵换成 $\rho$ 可以迁移坐标相位代数，但不能自动取得其控制词权限或同源准备资源。`docs/develop/theory/QUANTUM-RH.md` 原始29491行起的三态 Gram 例已有 $abc$ 闭环相位及正性约束，原始39501行起的四边形例已有环相位的乘法拼接；这些关系不因名称相同就成为 Levi–Civita 曲率。当前密度矩阵本身正半定，可以写成 Gram 矩阵，例如向量 $\sqrt\rho\,e_i$ 的内积就是 $\rho_{ij}$，从而闭路乘积与 Bargmann 型结构有真实代数对应；这种 Gram 表示没有额外授予那些向量的独立物理制备。

本节因此保留三种不同的有限接口：对全部态使用无需除法的 Hilbert 生成元；对已给实际非零支持使用模长与整数核基；对没有额外能量共振的图相位问题使用基本闭路。各自的充分性、零坐标条件和效果权限已经在上文给出。固定一般实能谱的有效关系取得、一般整数权重下小规模生成表、带噪支持认证及显式统计预算仍需相应输入或进一步结果；本节不声称这些问题已经由有限生成性解决。全部结论是普通后继源草稿，没有新增或编译 Lean，也不把紧闭包轨道等价升级成有限时间可达。

## 3. 有限时钟与共振分辨率

### 3.1 有限时钟平均：共振核、完整记录与可组合误差

B卷第2.2节与B卷第2.3节的精确能量 pinching 保留总能量相等的关系，删去其他交叉项。本节将它接到有限持续时间的实际随机演化：先声明时钟分布、同源副本共享什么、重复步骤之间独立什么，以及读数者能否取得时间记录，再计算留下的能隙模式。固定有限维 Hamiltonian 时，有限窗口平均以可量化的半 diamond 距离趋于完整 pinching；固定有限窗口时，它对 Hamiltonian 的扰动连续。精确共振代数随谱扰动跳变，只在无限窗口的结算中出现。

本节取 $\hbar=1$，生成元均有限维、时间不变且自伴。“时钟”首先指一份被执行的随机时间合同；给出时间分布不等于已经构造有限能量的自治量子钟。通道比较、同源输入限制和仪器权限分别保留。

#### 3.1.1 忘记时间记录后的通道与实际能隙

**定义 3.1（有限时钟与实际能隙）。** 令 $\mathcal H$ 是非零有限维 Hilbert 空间，$H=\sum_{a=1}^rE_a\Pi_a$，不同 $E_a$ 两两不等，$\Pi_a$ 为非零正交能量投影，允许任意有限简并重数。设 $\nu$ 是 $\mathbb R$ 上的 Borel 概率测度。实验从独立于系统输入及其外部参考的随机源取得 $t\sim\nu$，执行 $U_t=e^{-itH}$，最后忘记或隔离 $t$。系统边缘通道为

$$
\mathcal C_\nu^H(X)=\int_{\mathbb R}e^{-itH}Xe^{itH}\,d\nu(t),
\qquad
\widehat\nu(\omega)=\int_{\mathbb R}e^{-it\omega}\,d\nu(t).
\tag{TM.258}
$$

有限维下被积矩阵有界，逐坐标积分存在；任意辅助空间上的正性由随机酉平均保持，迹也保持，故这是完全正保迹通道。若只允许非负等待，应额外要求 $\nu([0,\infty))=1$；一般实线公式不授予负时间演化权限。

谱展开直接给出

$$
\mathcal C_\nu^H(X)
=\sum_{a,b=1}^r\widehat\nu(E_a-E_b)\Pi_aX\Pi_b,
\qquad
\Pi_a\mathcal C_\nu^H(X)\Pi_b
=\widehat\nu(E_a-E_b)\Pi_aX\Pi_b.
\tag{TM.259}
$$

因此实际有限能隙集上的字符值完全决定系统边缘通道。两份时间分布给出相同字符值，不意味着带时间记录的实验相同。$\widehat\nu(0)=1$，每个简并能量块内部的全部算子均保留，不能按任意选定的秩一基向量再次删去交叉项。

#### 3.1.2 时间记录属于哪一位观察者

**命题 3.2（保留及遗忘时刻记录）。** 时间仍可访问时，完整输出用以时间为经典结果的 instrument 表达。对 Borel 集 $B\subseteq\mathbb R$，令

$$
\mathfrak J_\nu^H(B)(X)=\int_B U_tXU_t^\dagger\,d\nu(t),
\qquad
\mathfrak J_\nu^H(\mathbb R)=\mathcal C_\nu^H.
\tag{TM.260}
$$

对密度输入，记录事件 $B$ 的概率是 $\nu(B)$，相应条件态由上述积分归一化。这是一份算子值测度，不必把连续标签 $|t\rangle$ 当成普通有限维密度矩阵中的正交向量。若允许按记录选择可测效果族 $0\le E_t\le I$，通过概率是 $\int\operatorname{Tr}(E_tU_t\rho U_t^\dagger)\,d\nu(t)$，一般不能只从 $\mathcal C_\nu^H(\rho)$ 恢复。

若同时授予根据准确 $t$ 执行 $U_t^\dagger$ 的控制权，记录可用于逐次恢复。对任意外部参考 $R$ 及联合输入 $\rho_{SR}$，

$$
\int (U_t^\dagger\otimes I_R)
 (U_t\otimes I_R)\rho_{SR}(U_t^\dagger\otimes I_R)
 (U_t\otimes I_R)\,d\nu(t)=\rho_{SR}.
\tag{TM.261}
$$

读到数字本身不是逆演化装置。仅有粗粒化时间、存在读数误差或不能执行逆酉时，须使用实际条件时间分布和控制误差；准确连续记录本身也是理想化信息资源。更完整的观察者若仍能取得时间、随机种子或相关环境，关于遗忘记录后边缘的去相位结论不自动描述他的全部信息。

#### 3.1.3 跨步独立与同一批副本共享时间

**命题 3.3（独立步骤与共同副本时钟）。** 对同一个生成元，两段增量 $t\sim\nu$、$s\sim\eta$ 若相互独立并独立于输入，Fubini 定理和 $U_tU_s=U_{t+s}$ 给

$$
\mathcal C_\nu^H\circ\mathcal C_\eta^H=\mathcal C_{\nu*\eta}^H,
\qquad
\widehat{\nu*\eta}(\omega)=\widehat\nu(\omega)\widehat\eta(\omega).
\tag{TM.262}
$$

相关增量须把实际联合律沿 $(t,s)\mapsto t+s$ 推前，不能改成边缘卷积。若增量由已有测量结果自适应选择，须保留 instrument 的条件结构，不能默认存在与输入无关的卷积。生成元不对易时，$e^{-itH}e^{-isK}$ 也一般不由 $t+s$ 决定。两个独立均匀窗口的和具有卷积分布，不是更宽的均匀窗口。

副本之间共同时间是另一层关系。对 $n\ge1$，定义

$$
H^{(n)}=\sum_{j=1}^n
 I^{\otimes(j-1)}\otimes H\otimes I^{\otimes(n-j)},
\qquad
\mathcal C_\nu^{H^{(n)}}(\rho^{\otimes n})
=\int(U_t\rho U_t^\dagger)^{\otimes n}\,d\nu(t).
\tag{TM.263}
$$

右侧是 $n$ 份同源新准备条件于共同时间独立，再对这个时间平均。若每份副本各抽独立时间，输出才是 $(\mathcal C_\nu^H(\rho))^{\otimes n}$。前者保留总能量相同的跨副本关系，后者分别平均。总生成元通道也可作用于一般联合输入，但那超出 $\rho^{\otimes n}$ 的来源限制。

同一批 $n$ 份若经历 $k$ 段彼此独立、各段在副本间共同的时间增量，则

$$
(\mathcal C_\nu^{H^{(n)}})^k
=\mathcal C_{\nu^{*k}}^{H^{(n)}}.
\tag{TM.264}
$$

$n$ 计来源份数，$k$ 计顺序随机步骤。未知态没有被免费复制，短算术描述也未代替实际步骤。副本同步时，共同等待不必乘以 $n$；制备、存储、控制及等待仍须分别计量。

#### 3.1.4 均匀有限窗口及完整 pinching 极限

**命题 3.4（均匀窗口极限）。** 取 $T>0$，$\nu_T(dt)=T^{-1}\mathbf1_{[0,T]}(t)\,dt$，记 $\mathcal A_T^H=\mathcal C_{\nu_T}^H$。直接积分得

$$
k_T(\omega)=\widehat\nu_T(\omega)
=\begin{cases}
\dfrac{1-e^{-i\omega T}}{i\omega T},&\omega\ne0,\\
1,&\omega=0,
\end{cases}
=e^{-i\omega T/2}\operatorname{sinc}(\omega T/2),
\qquad
\operatorname{sinc}(u)=\begin{cases}\sin u/u,&u\ne0,\\1,&u=0.\end{cases}
\tag{TM.265}
$$

于是

$$
\mathcal A_T^H(X)=\sum_{a,b}k_T(E_a-E_b)\Pi_aX\Pi_b,
\qquad
\mathcal P_H(X)=\sum_a\Pi_aX\Pi_a,
\qquad
|k_T(\omega)|\le\min\{1,2/(T|\omega|)\}\quad(\omega\ne0).
\tag{TM.266}
$$

对每个固定非零能隙，系数随 $T\to\infty$ 趋零，故 $\mathcal A_T^H\to\mathcal P_H$。下面给出包含全部参考的 diamond 范数界；不要求能量公度或时间周期。若 $r\ge2$，令

$$
g=\min_{a\ne b}|E_a-E_b|>0.
\tag{TM.267}
$$

$r=1$ 时 $H$ 为数量算子，两通道均为恒等，不定义 $g$。若要包括零窗口，可另定义 $\mathcal A_0^H=\operatorname{id}$，它是 $T\downarrow0$ 的连续延拓。

#### 3.1.5 精确半 diamond 距离

**命题 3.5（精确半 diamond 距离）。** 记 $\|\cdot\|_1$ 为迹范数，$\|\cdot\|_2$ 为 Hilbert–Schmidt 范数，$\|\cdot\|_{\rm op}$ 为算子范数，$d_\diamond(\mathcal E,\mathcal F)=\tfrac12\|\mathcal E-\mathcal F\|_\diamond$。该距离对全部联合输入及最终联合效果取最坏值，对应共同实验空间中没有额外对称性限制的测试权限。

定义 $r\times r$ Hermitian 矩阵与权重矩阵

$$
(C_T)_{aa}=0,\qquad (C_T)_{ab}=k_T(E_a-E_b)\quad(a\ne b),
\qquad
\Delta_r=\{p\in\mathbb R_{\ge0}^r:\sum_ap_a=1\},
\qquad D_p=\operatorname{diag}(\sqrt{p_1},\ldots,\sqrt{p_r}).
\tag{TM.268}
$$

**精确公式。**

$$
\boxed{
d_\diamond(\mathcal A_T^H,\mathcal P_H)
=\frac12\max_{p\in\Delta_r}\|D_pC_TD_p\|_1.
}
\tag{TM.269}
$$

**证明。** 写 $\Phi=\mathcal A_T^H-\mathcal P_H$。它保持 Hermitian 共轭。对任意迹范数一的联合算子 $X$，增添二维辅助空间，构造 $Y=\tfrac12\left(\begin{smallmatrix}0&X\\X^\dagger&0\end{smallmatrix}\right)$。有 $\|Y\|_1=1$，且输出 $Y$ 的迹范数等于输出 $X$ 的迹范数。对 $Y$ 作正负部分分解，其两个正部分的迹之和为一；三角不等式说明一般算子的输出范数不超过密度输入的最坏值。再纯化任意联合混合态，部分迹对 Hermitian 输出的迹范数收缩，故联合纯态已足够。辅助空间可有限增大，不影响取全部参考的上确界。

对联合纯态 $|\Psi\rangle$，令 $|\Psi_a\rangle=(\Pi_a\otimes I)|\Psi\rangle$，$p_a=\|\Psi_a\|^2$。非零 $|e_a\rangle=|\Psi_a\rangle/\sqrt{p_a}$ 两两正交，且

$$
(\Phi\otimes\operatorname{id})(|\Psi\rangle\langle\Psi|)
=\sum_{a\ne b}k_T(E_a-E_b)\sqrt{p_ap_b}\,|e_a\rangle\langle e_b|.
\tag{TM.270}
$$

该输出在这些向量张成的空间上恰有矩阵 $D_pC_TD_p$，其余方向为零，所以迹范数相等。零概率给零行列，不除以零。反过来，对任意 $p$，在每个扇区取单位向量 $v_a$，系统纯态 $\sum_a\sqrt{p_a}v_a$ 就实现相同矩阵，无需参考。连续函数在紧单纯形上达到最大值。证毕。

参考不增加这份通道差的最坏值，不意味着这些系统纯态都能由 $\rho^{\otimes n}$ 制备，也不授予仪器权限。常数相位可移除：令 $R_T=\operatorname{diag}(e^{-iE_aT/2})$，有

$$
S_T=R_T^\dagger C_TR_T,\qquad
(S_T)_{aa}=0,\qquad
(S_T)_{ab}=\operatorname{sinc}((E_a-E_b)T/2)\quad(a\ne b),
\qquad
\|D_pC_TD_p\|_1=\|D_pS_TD_p\|_1.
\tag{TM.271}
$$

这里 $D_p$ 与 $R_T$ 交换。$S_T$ 的对角项仍为零，不能误换成 sinc 相关矩阵的对角项一。

#### 3.1.6 逐块界与平方根维数界

**命题 3.6（扇区通用误差界）。** 对含参考的密度态 $\rho$，令 $P_a=\Pi_a\otimes I$，$p_a=\operatorname{Tr}(P_a\rho)$。Schatten Hölder 给

$$
\|P_a\rho P_b\|_1
=\|(P_a\sqrt\rho)(\sqrt\rho P_b)\|_1
\le\|P_a\sqrt\rho\|_2\|\sqrt\rho P_b\|_2
=\sqrt{p_ap_b}.
\tag{TM.272}
$$

因此原始的足够界为

$$
\frac12\|((\mathcal A_T^H-\mathcal P_H)\otimes\operatorname{id})(\rho)\|_1
\le\frac1{Tg}\sum_{a\ne b}\sqrt{p_ap_b}
=\frac{(\sum_a\sqrt{p_a})^2-1}{Tg}
\le\frac{r-1}{Tg}.
\tag{TM.273}
$$

精确公式给更好的平方根因子。对 $M_p=D_pC_TD_p$，

$$
\begin{aligned}
\|M_p\|_1&\le\sqrt r\,\|M_p\|_2,\\
\|M_p\|_2^2
&=\sum_{a\ne b}p_ap_b|k_T(E_a-E_b)|^2
\le\frac4{T^2g^2}\left(1-\sum_ap_a^2\right)
\le\frac4{T^2g^2}\frac{r-1}{r}.
\end{aligned}
\tag{TM.274}
$$

第一行对奇异值用 Cauchy–Schwarz，最后一步用 $\sum_ap_a^2\ge1/r$。两个通道的半 diamond 距离至多一，故

$$
\boxed{
d_\diamond(\mathcal A_T^H,\mathcal P_H)
\le\min\{1,\sqrt{r-1}/(Tg)\}.
}
\tag{TM.275}
$$

$r$ 是不同能量数，不包括简并重数。

#### 3.1.7 Hilbert 不等式给无维数因子的界

**命题 3.7（Hilbert 不等式的无维数界）。** 使用 Montgomery–Vaughan 的分离频率 Hilbert 不等式：若不同实数 $E_a$ 的距离至少 $g>0$，则对任意复向量 $x,y$，

$$
\left|\sum_{a\ne b}\frac{\overline{y_a}x_b}{E_a-E_b}\right|
\le\frac\pi g\|x\|_2\|y\|_2.
\tag{TM.276}
$$

这是下文作者专著 Theorem G.14 的直接重命名，允许任意实数位置，不要求等间隔或整数。为转成通道界，定义

$$
A_{ab}=\begin{cases}(E_a-E_b)^{-1},&a\ne b,\\0,&a=b,\end{cases}
\qquad A^\dagger=-A,\qquad \|A\|_{\rm op}\le\pi/g,
\qquad Q_T=\operatorname{diag}(e^{iE_aT/2}).
\tag{TM.277}
$$

对非对角项使用 $e^{iu}-e^{-iu}=2i\sin u$，对角项均为零，得到

$$
S_T=\frac{Q_TAQ_T^\dagger-Q_T^\dagger AQ_T}{iT},
\qquad \|S_T\|_{\rm op}\le\frac{2\pi}{Tg}.
\tag{TM.278}
$$

Schatten Hölder 给 $\|D_pS_TD_p\|_1\le\|D_p\|_2\|S_TD_p\|_2\le\|D_p\|_2^2\|S_T\|_{\rm op}=\|S_T\|_{\rm op}$。结合式(TM.269)，有

$$
\boxed{
d_\diamond(\mathcal A_T^H,\mathcal P_H)
\le\min\left\{1,\frac{\sqrt{r-1}}{Tg},\frac{\pi}{Tg}\right\}.
}
\tag{TM.279}
$$

Hilbert 不等式的 $\pi$ 是成熟的一般分离频率常数；没有由此证明最终通道上界中的 $\pi$ 也最优。无显式维数因子仍保留实际 $g$。随副本数增加，总能量间距可缩小，不能换成未证明的统一单副本常数。

#### 3.1.8 两扇区下界与实际来源

**命题 3.8（两扇区下界）。** 取两个扇区单位向量的等幅叠加，式(TM.269)的非零部分是特征值为 $\pm|k_T(E_a-E_b)|/2$ 的二阶矩阵。因此

$$
d_\diamond(\mathcal A_T^H,\mathcal P_H)
\ge\frac12\max_{a\ne b}|\operatorname{sinc}((E_a-E_b)T/2)|,
\qquad
r=2\ \Longrightarrow\
d_\diamond(\mathcal A_T^H,\mathcal P_H)
=\frac12|\operatorname{sinc}(gT/2)|.
\tag{TM.280}
$$

$r=2$ 的上界由 $\sqrt{p_1p_2}\le1/2$ 得到。矩形窗口没有单调的逐频率正下包络：$T\omega=2\pi\ell$，$\ell\ne0$ 为整数时，该非零频率恰被抹去。

来源受限时不必对所有 $p$ 取最大。式(TM.270)对纯输入给实际输出的精确迹距离；对混合输入纯化，再取部分迹，保留相同能量概率，得到

$$
\begin{aligned}
\frac12\|\mathcal A_T^H(|\Psi\rangle\langle\Psi|)
-\mathcal P_H(|\Psi\rangle\langle\Psi|)\|_1
&=\frac12\|D_pC_TD_p\|_1,\quad p_a=\|\Pi_a\Psi\|^2,\\
\frac12\|\mathcal A_T^H(\rho)-\mathcal P_H(\rho)\|_1
&\le\frac12\|D_qC_TD_q\|_1,\quad q_a=\operatorname{Tr}(\Pi_a\rho).
\end{aligned}
\tag{TM.281}
$$

对 $H^{(n)}$ 与 $|\psi\rangle^{\otimes n}$，必须取实际总能量分布 $p_\lambda=\|\Pi_\lambda^{(n)}\psi^{\otimes n}\|^2$，不能任意选择单纯形坐标。对混合产品态使用第二行。若实际占用 $s\ge2$ 个不同总能量，其最小间距为 $g_{\rm supp}$，限制到非零概率坐标可得

$$
\frac12\|\mathcal A_T^{H^{(n)}}(\rho^{\otimes n})
-\mathcal P_{H^{(n)}}(\rho^{\otimes n})\|_1
\le\min\left\{1,\frac{\sqrt{s-1}}{Tg_{\rm supp}},\frac\pi{Tg_{\rm supp}}\right\}.
\tag{TM.282}
$$

只占一个扇区时差为零，不定义 $g_{\rm supp}$。这些界依赖真实来源分布；抽象最坏分布存在，不表示来源合同允许它。

#### 3.1.9 标量优化与扰动积分

**命题 3.9（标量优化与扰动积分）。** 令 $H,K$ 在同一空间上自伴，$D=H-K$。数量平移不改变共轭通道。定义

$$
\delta(H,K)=\inf_{c\in\mathbb R}\|H-K-cI\|_{\rm op}
=\frac{\lambda_{\max}(D)-\lambda_{\min}(D)}2,
\qquad c_*=\frac{\lambda_{\max}(D)+\lambda_{\min}(D)}2.
\tag{TM.283}
$$

任意平移的范数是 $\max\{|\lambda_{\max}-c|,|\lambda_{\min}-c|\}$，其最小值在两极端中点达到。$\delta=0$ 恰表示两生成元只差数量算子，通道完全相同。

令 $K_c=K+cI$。对 $s\mapsto e^{-i(t-s)H}e^{-isK_c}$ 求导并积分，得到 Duhamel 恒等式；对 $t\ge0$，

$$
e^{-itH}-e^{-itK_c}
=-i\int_0^t e^{-i(t-s)H}(H-K_c)e^{-isK_c}\,ds,
\qquad
\|e^{-itH}-e^{-itK_c}\|_{\rm op}\le t\|H-K-cI\|_{\rm op}.
\tag{TM.284}
$$

两酉 $U,V$ 对任意联合密度态的输出差可写成 $(U-V)\rho U^\dagger+V\rho(U^\dagger-V^\dagger)$，故迹范数至多 $2\|U-V\|_{\rm op}$，参考上的恒等因子省略。密度态迹距离又至多一，故

$$
d_\diamond(\operatorname{Ad}_U,\operatorname{Ad}_V)
\le\min\{1,\|U-V\|_{\rm op}\},
\qquad
d_\diamond(\operatorname{Ad}_{e^{-itH}},\operatorname{Ad}_{e^{-itK}})
\le\min\{1,t\delta(H,K)\}.
\tag{TM.285}
$$

对同一个均匀时钟积分，并在积分前保留逐时刻截断，可得

$$
\boxed{
d_\diamond(\mathcal A_T^H,\mathcal A_T^K)
\le\frac1T\int_0^T\min\{1,t\delta(H,K)\}\,dt
=F(T\delta(H,K)),
\qquad F(x)=\begin{cases}
x/2,&0\le x\le1,\\
1-\dfrac1{2x},&x\ge1.
\end{cases}
}
\tag{TM.286}
$$

$\delta=0$ 时取零；$T\delta>1$ 时在 $1/\delta$ 分段积分。于是 $F(x)\le\min\{1,x/2\}$。这里优化标量平移并准确积分充分界，不声称 $F$ 是所有生成元对的最佳可能扰动模函数。

对一般共同概率时钟，相同证明给

$$
d_\diamond(\mathcal C_\nu^H,\mathcal C_\nu^K)
\le\int_{\mathbb R}\min\{1,|t|\delta(H,K)\}\,d\nu(t).
\tag{TM.287}
$$

此界始终有限；若再以一阶矩估计，须验证 $\int|t|\,d\nu<\infty$。比较固定同一载体、同一时间分布及同一检验合同，不能静默改变记录访问权。

总生成元之差是 $\sum_jD^{(j)}$，各项作用于不同 tensor 因子。其谱最大最小值分别为 $n\lambda_{\max}(D)$、$n\lambda_{\min}(D)$，由相应极端特征向量的 tensor 幂达到。因此

$$
\delta(H^{(n)},K^{(n)})=n\delta(H,K),\qquad
d_\diamond(\mathcal A_T^{H^{(n)}},\mathcal A_T^{K^{(n)}})
\le F(nT\delta(H,K))
\le\min\{1,nT\delta(H,K)/2\}.
\tag{TM.288}
$$

这是对全部联合输入的界，产品输入作为子类自动满足它。$H,K$ 不必对易。

#### 3.1.10 共振失谐读数与不交换极限

**命题 3.10（失谐与不交换极限）。** 固定整数 $m\ge2$，令

$$
H_{m,\epsilon}=\operatorname{diag}(0,1,m+\epsilon),\qquad
|\psi\rangle=(|0\rangle+|1\rangle+|2\rangle)/\sqrt3,\qquad
\rho_\psi=|\psi\rangle\langle\psi|.
\tag{TM.289}
$$

先用B卷第2.2.8节的 $m$ 份纯来源。取字 $I=1^m$、$J=(2,0,\ldots,0)$，则

$$
E_I=m,\qquad E_J=m+\epsilon,\qquad
\langle I|\rho_\psi^{\otimes m}|J\rangle=3^{-m},\qquad
\langle I|\mathcal A_T^{H_{m,\epsilon}^{(m)}}(\rho_\psi^{\otimes m})|J\rangle
=3^{-m}k_T(-\epsilon).
\tag{TM.290}
$$

固定效果 $Q_+=\tfrac12(|I\rangle+|J\rangle)(\langle I|+\langle J|)$。两个对角字概率都是 $3^{-m}$，所以完整批次的未条件化概率是

$$
p_{\epsilon,T}
=\operatorname{Tr}\!\left[Q_+\mathcal A_T^{H_{m,\epsilon}^{(m)}}(\rho_\psi^{\otimes m})\right]
=3^{-m}\bigl(1+\operatorname{sinc}(\epsilon T)\bigr).
\tag{TM.291}
$$

固定实效果读 $\operatorname{Re}k_T(-\epsilon)=\sin(\epsilon T)/(\epsilon T)$，整个复相干的衰减模长却是 $|\operatorname{sinc}(\epsilon T/2)|$，不能混用。由同一精确式，

$$
\lim_{T\to\infty}\lim_{\epsilon\to0}p_{\epsilon,T}=2\,3^{-m},\qquad
\lim_{\substack{\epsilon\to0\\\epsilon\ne0}}\lim_{T\to\infty}p_{\epsilon,T}=3^{-m},\qquad
|p_{\epsilon,T}-2\,3^{-m}|\le3^{-m}\frac{(\epsilon T)^2}{6}.
\tag{TM.292}
$$

末项使用 $\operatorname{sinc}(x)=\int_0^1\cos(xs)\,ds$ 与 $0\le1-\cos u\le u^2/2$。这是当前实效果的二阶界，不是所有效果的二阶界。另一正交相位读数可以取得

$$
\operatorname{Im}[3^{-m}k_T(-\epsilon)]
=3^{-m}\frac{1-\cos(\epsilon T)}{\epsilon T}.
\tag{TM.293}
$$

零点按连续延拓取零，首阶项为 $3^{-m}\epsilon T/2$。以 $|v_\theta\rangle=(|I\rangle+e^{i\theta}|J\rangle)/\sqrt2$ 的投影为效果，$\theta=-\pi/2$ 与 $\pi/2$ 的概率差的一半正好给该虚部，失败结果不删除。

B卷第2.3.11节达到统一阶数 $N=2m-1$ 的稀疏正定态也能接入有限窗口。取 $a=1/12$，写

$$
R_\varphi=\begin{pmatrix}
1/3&0&ae^{-i\varphi}\\
0&1/3&a\\
ae^{i\varphi}&a&1/3
\end{pmatrix},\qquad
\rho_m=R_0,\quad \sigma_m=R_{\pi/(m-1)},\qquad N=2m-1.
\tag{TM.294}
$$

其谱为 $1/3,1/3\pm\sqrt2a$，全为正。取 $I_*=(2^m,0^{m-1})$、$J_*=(1^m,2^{m-1})$ 及 $Q_*=\tfrac12(|I_*\rangle+|J_*\rangle)(\langle I_*|+\langle J_*|)$。实际能量和矩阵元给

$$
\begin{aligned}
E_{I_*}(\epsilon)&=m^2+m\epsilon,\qquad
E_{J_*}(\epsilon)=m^2+(m-1)\epsilon,\\
\langle I_*|R_\varphi^{\otimes N}|J_*\rangle
&=a^Ne^{-i(m-1)\varphi},\\
\operatorname{Tr}\!\left[Q_*\mathcal A_T^{H_{m,\epsilon}^{(N)}}(\rho_m^{\otimes N})\right]
&=3^{-N}+a^N\operatorname{sinc}(\epsilon T),\\
\operatorname{Tr}\!\left[Q_*\mathcal A_T^{H_{m,\epsilon}^{(N)}}(\sigma_m^{\otimes N})\right]
&=3^{-N}-a^N\operatorname{sinc}(\epsilon T).
\end{aligned}
\tag{TM.295}
$$

$\epsilon=0$ 恢复B卷第2.3节的差 $2a^N$；固定非零失谐时，当前效果的差随 $T\to\infty$ 趋零。实分量恰为零不代表复模式为零：$\epsilon T=\pi$ 时实 sinc 为零，而 $|k_T(\epsilon)|=2/\pi$。未在此计算两产品来源的全部最优区别，也没有从次数有限推出显著统计信号。

pinching 通道的不连续还可直接展示。对 $|\chi\rangle=(|I_*\rangle+|J_*\rangle)/\sqrt2$，共振时 pinching 保留纯态，非零失谐时删除两字交叉项。两个输出的迹距离为 $1/2$，所以

$$
d_\diamond(\mathcal P_{H_{m,\epsilon}^{(N)}},\mathcal P_{H_{m,0}^{(N)}})\ge\frac12
\quad(\epsilon\ne0),\qquad
d_\diamond(\mathcal A_T^{H_{m,\epsilon}^{(N)}},\mathcal A_T^{H_{m,0}^{(N)}})
\le F(NT|\epsilon|/2).
\tag{TM.296}
$$

后式因单副本扰动谱为 $0,0,\epsilon$，故 $\delta=|\epsilon|/2$。前式用一般总系统纯态作见证，不声称产品来源限制下也有最优值 $1/2$。固定有限 $T,N$ 时后式趋零；两结论对应不同极限次序。

#### 3.1.11 通道区别与严格对称读数

**命题 3.11（通道区别与对称效果）。** 若系统效果 $0\le E\le I$ 满足 $[E,H]=0$，循环移迹逐时刻给

$$
\operatorname{Tr}(E\mathcal C_\nu^H(\rho))
=\operatorname{Tr}(E\rho)
=\operatorname{Tr}(E\mathcal P_H(\rho)).
\tag{TM.297}
$$

在此固定效果语言中，有限平均、恒等通道和完整 pinching 精确不可区分，无需输入本来不变。若先经过从 $H$ 到 $K$ 作用的协变通道 $\mathcal E$，再用 $[F,K]=0$ 的效果，则

$$
\mathcal E(e^{-itH}Xe^{itH})=e^{-itK}\mathcal E(X)e^{itK},\qquad
[F,K]=0\ \Longrightarrow\ [\mathcal E^*(F),H]=0.
\tag{TM.298}
$$

将协变式与 $F$ 配对，利用对偶定义及 $F$ 不变，即证明 Heisenberg 拉回不变。有限串接、包含全部结果记录的协变 instrument 同样按最终拉回条件判断，不能遗漏携带相干的辅助资源。

关键条件是**诱导在被平均系统上的效果**与 $H$ 交换。联合效果对 $H+H_R$ 不变，不在任意参考态下推出系统效果不变。若参考与来源独立且 $[\tau_R,H_R]=0$，取参考期望后确实仍不变，这是B卷第2.1节及既有参考资源来源的接口。相干参考则可诱导不对易系统效果；相关参考必须保留联合输入，不能改写为独立 $\tau_R$。

式(TM.291)、(TM.295)的固定叠加效果在 $\epsilon=0$ 对易，在非零失谐时不对易。其曲线属于允许固定效果的共同外部控制实验，或需要显式关系参考。有限窗口没有自动扩大效果菜单。diamond 范数比较使用全部外部测试，严格对称语言下实际区别仍可为零。

例如已知固定 $\epsilon>0$ 时，添参考 $H_R=\epsilon|1\rangle\langle1|$。$|I_*,0\rangle$ 与 $|J_*,1\rangle$ 总能量相等，故

$$
G=\frac{(|I_*,0\rangle+|J_*,1\rangle)(\langle I_*,0|+\langle J_*,1|)}2,
\qquad [G,H_{m,\epsilon}^{(N)}+H_R]=0,
\qquad
(I_S\otimes\langle+|)G(I_S\otimes|+\rangle)=\frac12Q_*,
\quad |+\rangle_R=(|0\rangle+|1\rangle)/\sqrt2.
\tag{TM.299}
$$

省略的 tensor 恒等因子按总系统理解。这给一份衰减的合法干涉效果；测量 $\{G,I-G\}$ 保留全部结果，不能删去失败后称为免费精确实现 $Q_*$。参考须提供所需谱隙和相干，并作为测量阶段的独立资源；它若也经历遗忘时间平均，应改用实际联合状态。负失谐可交换匹配角色并取 $|\epsilon|$；一份固定有限参考不能一般为连续变化的失谐提供所有精确匹配谱隙。时间记录反馈同样需要显式权限。

#### 3.1.12 重复随机步骤：直接与 Cesàro 极限

**命题 3.12（直接与 Cesàro 极限）。** 固定 $H,\nu$，写 $\kappa_{ab}=\widehat\nu(E_a-E_b)$。各步独立取新增量且忘记记录时，

$$
(\mathcal C_\nu^H)^k(X)=\sum_{a,b}\kappa_{ab}^{\,k}\Pi_aX\Pi_b,
\qquad |\kappa_{ab}|\le1.
\tag{TM.300}
$$

**直接收敛判据。** 通道幂对所有矩阵收敛，当且仅当对每个实际能隙都有

$$
|\widehat\nu(E_a-E_b)|<1\quad\text{或}\quad\widehat\nu(E_a-E_b)=1.
\tag{TM.301}
$$

充分性逐块来自复数幂极限；块数有限，故在有限维线性映射空间的所有范数下收敛，包括 diamond 范数。必要性：若 $|z|=1$、$z\ne1$，则 $|z^{k+1}-z^k|=|z-1|>0$。矩阵单位能隔离该块；用实际密度输入时，两扇区等幅纯态也有不收敛的交叉矩阵元 $z^k/2$。共同固定点存在不替代此判据。

直接极限不存在时，先独立均匀抽取 $k\in\{0,\ldots,K-1\}$、执行 $k$ 步、最后忘记步数的 Cesàro 混合仍有极限：

$$
\frac1K\sum_{k=0}^{K-1}(\mathcal C_\nu^H)^k(X)
=\sum_{a,b}\left(\frac1K\sum_{k=0}^{K-1}\kappa_{ab}^{\,k}\right)\Pi_aX\Pi_b
\ \longrightarrow\ \sum_{\kappa_{ab}=1}\Pi_aX\Pi_b.
\tag{TM.302}
$$

对 $\kappa\ne1$，括号等于 $(1-\kappa^K)/(K(1-\kappa))$，模至多 $2/(K|1-\kappa|)$；$\kappa=1$ 时恒为一。这是不同于固定重复 $K$ 次的协议，步数随机化不能读取来源未来创新。

保留块组成一个 pinching，因为

$$
\widehat\nu(\omega)=1
\ \Longleftrightarrow\
e^{-it\omega}=1\quad\nu\text{-几乎处处},\qquad
\int|e^{-it\omega}-1|^2\,d\nu(t)=2-2\operatorname{Re}\widehat\nu(\omega).
\tag{TM.303}
$$

非负积分证明等价。定义 $a\sim_\nu b$ 当该条件对 $E_a-E_b$ 成立；自反、对称显然，传递在两份全测度集合交上用字符乘法。能隙有限，可共同取同一个全测度集合。对等价类 $\mathcal K$ 令 $P_{\mathcal K}=\sum_{a\in\mathcal K}\Pi_a$，则

$$
\mathcal P_\nu^H(X)=\sum_{\mathcal K}P_{\mathcal K}XP_{\mathcal K},\qquad
\operatorname{Fix}(\mathcal C_\nu^H)
=\bigoplus_{\mathcal K}\mathcal B(P_{\mathcal K}\mathcal H).
\tag{TM.304}
$$

固定点方程是 $(\kappa_{ab}-1)X_{ab}=0$，故给上述代数；它也等于随机酉族在同一全测度时间集上的共同固定代数。$\mathcal P_\nu^H$ 完全正、保迹、幂等，并对该代数左右乘法有模性质，所以是保迹条件期望。Cesàro 极限总是它，直接极限存在时也为它。它不必等于按不同能量分块的 $\mathcal P_H$，因为实际时间支持可让不同能量具有同一字符。

#### 3.1.13 两类可重复时钟与混叠

**命题 3.13（重复时钟与混叠）。** 取 $\tau>0$、$\nu=(\delta_0+\delta_\tau)/2$。独立重复是否等待 $\tau$ 的步骤，系数为

$$
\widehat\nu(\omega)=\frac{1+e^{-i\tau\omega}}2,\qquad
|\widehat\nu(\omega)|=|\cos(\tau\omega/2)|,\qquad
\widehat\nu(\omega)=1\ \Longleftrightarrow\ \tau\omega\in2\pi\mathbb Z.
\tag{TM.305}
$$

模长一恰在最后条件发生，并且此时系数等于一，所以直接幂总收敛。极限按 $e^{-i\tau H}$ 的本征相位分块；相差整数整周的能量被合并。它等于 $\mathcal P_H$ 当且仅当没有实际非零能隙满足该整周条件。纯确定步骤 $\delta_\tau$ 不同：只要有实际字符不等于一，其通道幂就不收敛；所有字符为一时通道原本就是恒等。

取率参数 $\gamma>0$ 的非负指数时钟，

$$
d\nu_\gamma(t)=\mathbf1_{t\ge0}\gamma e^{-\gamma t}\,dt,\qquad
\widehat\nu_\gamma(\omega)=\frac{\gamma}{\gamma+i\omega},\qquad
|\widehat\nu_\gamma(\omega)|=\frac{\gamma}{\sqrt{\gamma^2+\omega^2}}.
\tag{TM.306}
$$

直接积分得到公式，所有非零能隙的模严格小于一，故独立重复的极限恰为 $\mathcal P_H$。$k$ 次实际增量之和的均值为 $k/\gamma$，无限重复不是有限时间取得精确 pinching。原子时钟混叠由完整支持和实际能隙字符共同决定，不仅取决于原子个数或时间跨度。

#### 3.1.14 模式恢复与时钟重标记

**命题 3.14（模式恢复的条件数）。** 对已声明模式，设平均前读数为 $x_\omega$，平均后为 $y_\omega=\widehat\nu(\omega)x_\omega$。系数已知且非零、两个正交分量确实可读时，

$$
x_\omega=\frac{y_\omega}{\widehat\nu(\omega)},\qquad
|\widetilde y_\omega-y_\omega|\le\eta
\ \Longrightarrow\
\left|\frac{\widetilde y_\omega}{\widehat\nu(\omega)}-x_\omega\right|
\le\frac{\eta}{|\widehat\nu(\omega)|}.
\tag{TM.307}
$$

这是读数条件数，不是普适完全正逆通道。若某两扇区系数模严格小于一，两等幅反相态的迹距离由一缩成该模长；通道不能再把距离无损恢复为一，所以这个除法不是物理通道逆。系数为零时，该模式的区别从遗忘记录的边缘中消失。

均匀窗口的条件数为 $|\operatorname{sinc}(T\omega/2)|^{-1}$，在非零整数整周处不可逆。近零的展开与全局包络分别为

$$
|k_T(\omega)|=1-\frac{(T\omega)^2}{24}+O((T\omega)^4),\qquad
\operatorname{Re}k_T(\omega)=1-\frac{(T\omega)^2}{6}+O((T\omega)^4),
\qquad
T\ge\frac2{\eta|\omega|}
\ \Longrightarrow\ |k_T(\omega)|\le\eta
\quad(\eta>0,\ \omega\ne0).
\tag{TM.308}
$$

前两式针对 $T\omega\to0$，末项给充分而非必要抑制时间，因为更早的窗口零点也可抑制。逐模式信息保留不随矩形窗口长度单调变化。统计误差如何由有限样本取得、源相干大小及参考成本必须另外供应。

平均通道接近 pinching，不表示单时刻状态大部分时间在迹距离上接近平衡。两个不同能量的等幅纯态，逐时刻演化与其 pinching 的迹距离恒为 $1/2$；只有遗忘时间后的平均交叉项趋零。这区分了本文平均通道结论和文献中特定测量族的时间平均可分辨性。

重标记必须同时运输轨迹与测度。若 $\nu=f_*\eta$，则

$$
\mathcal C_\nu^H(X)=\int e^{-if(\tau)H}Xe^{if(\tau)H}\,d\eta(\tau).
\tag{TM.309}
$$

若 $f$ 是覆盖 $[0,T]$ 的 $C^1$ 递增可逆变换，同一个均匀物理窗口写成

$$
\mathcal A_T^H(X)
=\frac1T\int_{f^{-1}(0)}^{f^{-1}(T)}
e^{-if(\tau)H}Xe^{if(\tau)H}f'(\tau)\,d\tau.
\tag{TM.310}
$$

删掉 $f'(\tau)$ 并改用均匀新变量，一般改变时间分布；把轨迹改为 $e^{-i\tau H}$ 也一般改变实验。整份推前关系保持才是同一通道的不同表示，不由重命名获得资源节省。

#### 3.1.15 成熟来源与承担的连接

Iman Marvian、Robert W. Spekkens，[*Modes of asymmetry: the application of harmonic analysis to symmetric quantum dynamics and quantum reference frames*, arXiv:1312.0680v2](https://arxiv.org/pdf/1312.0680v2)。固定版本 PDF 第6页式(2.14)—(2.15)给 weighted twirling 及 $\sigma^{(k)}=p_{-k}\rho^{(k)}$；同页 Proposition 1 给协变操作不产生输入缺少的模式。第8页式(2.23)—(2.25)将参考失配分布接到 Fourier 系数，随后的例子说明参考质量依赖任务所需模式。原文用 $U(\theta)\rho U(\theta)^\dagger=\sum_ke^{ik\theta}\rho^{(k)}$，故出现 $p_{-k}$；本文固定 $e^{-itH}$，直接积分产生 $\widehat\nu(E_a-E_b)$，须核对符号。整数 $U(1)$ 模标签不自动涵盖任意实谱；式(TM.259)是有限谱演算给出的实际 Bohr 频率版本。原文未声明本文的 $Tg$ diamond 界。

Hugh L. Montgomery、Robert C. Vaughan，[*Multiplicative Number Theory II: Primes and Sieves*，作者网页 PDF](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf)，Appendix G.4，Theorem G.14 及证明，印刷第422—425页，对应本节所据472页 PDF 的第434—437页。定理对间距至少 $\delta$ 的不同实数给双线性型常数 $\pi/\delta$，证明等价使用非对角元素 $1/(\lambda_m-\lambda_n)$ 的斜 Hermitian 矩阵，式(G.16)给所需范数平方界。本文以 $\delta=g$ 调用，再由式(TM.278)及 Schatten Hölder 得通道界；不将成熟 Hilbert 不等式计为新增结果。此处依据作者稿的定理及证明，而非1974年原刊措辞，也不把当前通道常数的最优性归入其结论。

Anthony J. Short、Terence C. Farrelly，[*Quantum equilibration in finite time*, arXiv:1110.5759v1](https://arxiv.org/pdf/1110.5759v1)。PDF 第3页式(11)积分有限窗口振荡核，随后给相应的 $2/(T|\Delta|)$ 包络。原文矩阵按能隙差 $G_\alpha-G_\beta$ 索引；第4页 Theorem 2 用有效维数、能隙密度和测量结果数控制特定测量族的时间平均可分辨性。本文振荡积分属于同一成熟机制，但式(TM.269)、(TM.279)比较通道并对全部参考取最坏值，不是该论文定理的逐字转述；也不能用本文结论宣称大多数时刻的全态平衡。

仓内参考资源边界接到不可变快照 237012b49d0d4729a86f7e9dd252d94df1de8dd0 的 [QUANTUM-REALITY 第373—374节](https://github.com/the-omega-institute/trureturing/blob/237012b49d0d4729a86f7e9dd252d94df1de8dd0/docs/develop/theory/QUANTUM-REALITY.md)。第373.1节原始49984—50048行要求联合效果保持总激发数，其他辅助系统须不变或明确计入资源，证明独立不变参考诱导系统不变效果；原始50054行起构造关系相位效果。第374.1节原始50124行起给有限参考下的最佳区分概率，只承担其特定参考谱及准备合同的优化。本文迁移共同能量块与参考相干接口，不把这些纸面来源或本文公式报为新增 Lean。

本节补足有限时间接口：遗忘记录后，实际能隙字符值完整决定通道；独立增量使其相乘；扇区矩阵控制全部参考下的通道距离；有限窗口对标量等价类上的谱扰动连续；共同副本失谐有明确的未条件化读数；固定重复、Cesàro 混合和保留时间记录对应不同实验。一般自治钟制备、最优能量—精度成本与有限样本预算未由这些公式解决，也没有从随机平均推出新的时空本体关系。全部内容为普通数学源草稿，完整记录、效果权限及实际来源仍是应用前件。

### 3.2 三原子时钟的分辨率、整数别名与黄金近共振

本文固定有限维自伴生成元、同一随机时钟的实际作用及跨步骤独立增量，研究精确去相位、有限步骤误差和能谱族上的统一性。所有结论为普通数学推导；黄金残差直接复用已有仓内及上游恒等式，不将标准恒等式或以下综合推导宣称为新原创定理。没有新增 Lean 或形式核验。

#### 3.2.1 共同定义与三原子严格收缩

**命题 3.15（三原子时钟严格收缩）。** 固定
$$
H=\sum_{\lambda\in\Lambda}\lambda\Pi_\lambda,\qquad
r=|\Lambda|,\qquad
\nu=p_0\delta_0+p_1\delta_{\tau_1}+p_2\delta_{\tau_2},
$$
其中三个权重严格正、总和为一，两个非零时刻严格正。记
$$
\chi(\Delta)=\widehat\nu(\Delta)
=p_0+p_1e^{-i\tau_1\Delta}+p_2e^{-i\tau_2\Delta},
\qquad
\mathcal P_H(X)=\sum_\lambda\Pi_\lambda X\Pi_\lambda .
\tag{TM.420}
$$
跨步骤的时钟增量独立且同分布，故
$$
(\mathcal C_\nu^H)^k(X)
=\sum_{\lambda,\mu}\chi(\lambda-\mu)^k
 \Pi_\lambda X\Pi_\mu .
\tag{TM.421}
$$
这使用了实际卷积律；重复调用同一个随机增量不满足此式。

令 $\tau_0=0$。由单位复数加权平均的模平方直接展开，
$$
1-|\chi(\Delta)|^2
=4\sum_{0\le i<j\le2}
 p_ip_j\sin^2\!\left(\frac{(\tau_i-\tau_j)\Delta}{2}\right).
\tag{TM.422}
$$
右侧每项非负，且所有权重严格正。因此
$$
|\chi(\Delta)|=1
\iff \tau_1\Delta,\tau_2\Delta\in2\pi\mathbb Z
\iff\chi(\Delta)=1.
\tag{TM.423}
$$
也可由三角不等式取等条件证明：三个单位相位必须相同，而零时刻的相位固定为一。

于是这份三原子律不会产生模为一但不等于一的旋转外围特征值，直接幂极限总存在。它保留的能量块，恰好满足式（TM.423）的共同整数关系。

零时刻的严格正质量不可从该论证中删除。例如只在 $\tau_1,\tau_2$ 两时刻取正质量，取
$\Delta=2\pi/|\tau_1-\tau_2|$，两个相位相同，故平均仍为单位模；当时刻比无理时，该共同相位不为一。此时重复幂可以不收敛。单独证明 $\chi(\Delta)=1$ 只有零频解，不能替代对全部单位模点的检查。

#### 3.2.2 时钟生成的加法群与整数别名

**命题 3.16（生成群与整数别名）。** 定义时刻的整数生成群及其字符零核：
$$
G_\nu=\tau_1\mathbb Z+\tau_2\mathbb Z,\qquad
G_\nu^\perp
=\{\Delta:\Delta t\in2\pi\mathbb Z\ \text{对全部 }t\in G_\nu\}.
\tag{TM.424}
$$
重复极限保留 $(\lambda,\mu)$ 块，当且仅当
$\lambda-\mu\in G_\nu^\perp$。这是对时刻关系的共同核取交。

若 $\tau_1=a\tau,\tau_2=b\tau$，其中 $a,b$ 为正整数、$\tau>0$，令 $d=\gcd(a,b)$。Bézout 等式给
$$
a\tau\Delta,b\tau\Delta\in2\pi\mathbb Z
\iff d\tau\Delta\in2\pi\mathbb Z,
\qquad
G_\nu^\perp=\frac{2\pi}{d\tau}\mathbb Z .
\tag{TM.425}
$$
因此极限是 $e^{-id\tau H}$ 的本征相位块 pinching。它等于能量 pinching，当且仅当实际有限谱中没有非零能隙落在上述别名格。

若 $a,b$ 互素，只将整数时钟恢复到基础时钟 $\tau$ 的分辨能力，仍不能区分差为 $2\pi n/\tau$ 的频率。具体地，取 $a=2,b=3$ 和
$H=\operatorname{diag}(0,2\pi/\tau)$，三个时刻的共轭作用全部是恒等；任意次数重复仍不去除这两个能级间的相干。相关结构由最大公因数和字符核决定，不要求 $a,b$ 各自为素数。

若 $\tau_2/\tau_1\notin\mathbb Q$，两个整数整周条件同时成立且 $\Delta\ne0$，会强制 $\tau_2/\tau_1$ 为有理数。因此
$$
G_\nu^\perp=\{0\},\qquad
|\chi(\Delta)|<1\quad(\Delta\ne0).
\tag{TM.426}
$$
每个固定有限谱于是都直接收敛到 $\mathcal P_H$。同一能量内的简并块保留；此结论并不把能量简并进一步消除。

#### 3.2.3 固定有限谱的半 diamond 误差界

**命题 3.17（固定谱的误差界）。** 假设时刻比无理、$r\ge2$，定义
$$
q_H=\max_{\lambda\ne\mu}|\chi(\lambda-\mu)|<1.
\tag{TM.427}
$$
则对每个整数 $k\ge1$，
$$
d_\diamond\!\left((\mathcal C_\nu^H)^k,\mathcal P_H\right)
\le
\min\!\left\{1,\frac{r-1}{2}q_H^k\right\},
\tag{TM.428}
$$
其中 $d_\diamond$ 取 diamond 范数的一半。该界允许任意外部参考，也允许各能量块有任意简并度。

证明：在B卷第3.1.6节的通用扇区界中，以本节 $H$ 的谱投影为扇区，并将每个非对角乘子取为 $\chi(\lambda-\mu)^k$。跨步骤独立性给出该乘子，式（TM.427）使其模至多 $q_H^k$。该界对任意辅助参考及任意块简并度成立，直接得到式（TM.428）。若 $r=1$，两个通道均为恒等，误差恒为零，不定义空最大值 $q_H$。若 $q_H=0$，一次步骤已精确达到 pinching。

当 $0<q_H<1$、$0<\varepsilon<(r-1)/2$ 时，
$$
k\ge
\frac{\log((r-1)/(2\varepsilon))}{-\log q_H}
\tag{TM.429}
$$
是误差不超过 $\varepsilon$ 的充分步骤条件，实际步骤取满足该式的整数。这是上述上界的充分条件，未宣称对所有输入和通道最优。

#### 3.2.4 固定能隙带上的正面统一界

**命题 3.18（固定能隙带的统一界）。** 固定 $0<g\le M<\infty$，限制生成元族的每个非零能隙满足
$$
g\le|\lambda-\mu|\le M.
\tag{TM.430}
$$
在无理时刻比条件下，$\chi$ 连续，并在紧集
$[-M,-g]\cup[g,M]$ 上处处严格模小于一。因此最大值
$$
q_{\nu,g,M}
=\max_{g\le|\Delta|\le M}|\chi(\Delta)|<1
\tag{TM.431}
$$
存在。整个受限生成元族统一满足
$$
d_\diamond\!\left((\mathcal C_\nu^H)^k,\mathcal P_H\right)
\le
\min\!\left\{1,\frac{r-1}{2}q_{\nu,g,M}^k\right\}.
\tag{TM.432}
$$
若同时限制 $r\le r_0$，可将右侧的 $r$ 换成 $r_0$，取得对该整族的统一常数。

该结论依赖实际能隙带。只给能谱宽度上界而允许非零能隙趋零，因 $\chi(0)=1$ 不能得到相同的严格统一率；只给正下界 $g$ 而不给上界 $M$，则会遇到后文的高频近共振。也可用直接的统一非共振条件替代整个能隙带条件；带宽只是一个充分条件。

一种可检验的相位分离证书是
$$
d_j(\Delta)
=\operatorname{dist}\!\left(\frac{\tau_j\Delta}{2\pi},\mathbb Z\right)
\in[0,1/2],\qquad j=1,2.
$$
由 $\sin(\pi u)\ge2u$ 对 $0\le u\le1/2$ 成立，式（TM.422）推出
$$
1-|\chi(\Delta)|^2
\ge16p_0\bigl(p_1d_1(\Delta)^2+p_2d_2(\Delta)^2\bigr).
\tag{TM.433}
$$
若全部相关能隙满足 $\max(d_1,d_2)\ge\eta>0$，则
$$
|\chi(\Delta)|^k
\le
\exp\!\left[-8k\,p_0\min(p_1,p_2)\eta^2\right].
\tag{TM.434}
$$
因此有限步骤成本由共同相位分离的裕度控制；仅知不存在精确别名，还未提供这份裕度。

#### 3.2.5 两能级的精确距离

**命题 3.19（两能级精确距离）。** 对 $\Delta>0$，取
$$
H_\Delta=\operatorname{diag}(0,\Delta),\qquad
\rho_+=|+\rangle\langle+|,\qquad
|+\rangle=(|0\rangle+|1\rangle)/\sqrt2.
$$
输出差为
$$
\bigl((\mathcal C_\nu^{H_\Delta})^k-\mathcal P_{H_\Delta}\bigr)(\rho_+)
=\frac12
\begin{pmatrix}
0&\overline{\chi(\Delta)^k}\\
\chi(\Delta)^k&0
\end{pmatrix}.
$$
其特征值为 $\pm|\chi(\Delta)|^k/2$，因此迹范数为
$|\chi(\Delta)|^k$。结合式（TM.428）在 $r=2$ 时的上界，得到精确公式
$$
d_\diamond\!\left(
(\mathcal C_\nu^{H_\Delta})^k,\mathcal P_{H_\Delta}
\right)
=\frac12|\chi(\Delta)|^k.
\tag{TM.435}
$$
该等式是允许全部联合输入及终端效果的通道距离。若具体任务仅允许与 $H_\Delta$ 对易的效果，这类效果完全看不到剩余非对角块；不能把式（TM.435）自动解释为受限任务中的可取得信号。

#### 3.2.6 任意无理时刻比仍有高频近共振

**命题 3.20（无理时钟的高频近共振）。** 令 $\alpha=\tau_2/\tau_1$ 无理，取整数 $n\ge1,m$，并置
$$
\Delta_n=\frac{2\pi n}{\tau_1},\qquad
\epsilon_{n,m}=n\alpha-m.
$$
前两个原子的相位精确为一，因此
$$
\chi(\Delta_n)
=1-p_2+p_2e^{-2\pi i\epsilon_{n,m}},
\qquad
|\chi(\Delta_n)|^2
=1-4p_2(1-p_2)\sin^2(\pi\epsilon_{n,m}).
\tag{TM.436}
$$
对每个正整数 $Q$，将 $0,\alpha,\ldots,Q\alpha$ 的小数部分放入 $Q$ 个等长区间，得到整数
$1\le n_Q\le Q$、$m_Q$ 满足
$|n_Q\alpha-m_Q|\le1/Q$。
由于 $\alpha$ 无理，任意有限集合的正整数 $n$ 与整数的距离
$\operatorname{dist}(n\alpha,\mathbb Z)$ 都有正的最小值，故这些 $n_Q$ 必有趋无穷的子序列。沿该子序列，
$\Delta_{n_Q}\to\infty$ 且 $|\chi(\Delta_{n_Q})|\to1$。

于是对任意 $g>0$ 及任意固定有限 $k\ge1$，式（TM.435）给出
$$
\sup_{\Delta\ge g}
d_\diamond\!\left(
(\mathcal C_\nu^{H_\Delta})^k,\mathcal P_{H_\Delta}
\right)=\frac12 .
\tag{TM.437}
$$
每个固定 $\Delta>0$ 的误差仍随 $k\to\infty$ 趋零；上确界中的生成元随 $k$ 和所要求的逼近精度变化。特别地，
$$
\lim_{k\to\infty}\sup_{\Delta\ge g}d_\diamond=\frac12,
\qquad
\sup_{\Delta\ge g}\lim_{k\to\infty}d_\diamond=0 .
\tag{TM.438}
$$
因此不存在只依赖 $r$ 和这份三原子时钟律的统一几何收缩率，甚至只额外指定正能隙下界 $g$ 仍然不够。上述反例固定 $r=2$，使用趋无穷的能隙，不依赖 $\Delta\to0$ 的近简并。

#### 3.2.7 黄金时钟的显式 Fibonacci 证书

**命题 3.21（黄金时钟的 Fibonacci 界）。** 取 $\tau_1=\tau>0,\tau_2=\phi\tau$，其中
$\phi=(1+\sqrt5)/2$。记 $F_0=0,F_1=1$、
$F_{N+2}=F_{N+1}+F_N$。已有黄金残差恒等式为
$$
\phi F_N-F_{N+1}
=-\left(-\frac1\phi\right)^N
=(-1)^{N+1}\phi^{-N}.
\tag{TM.439}
$$
该式直接来自既有声明，不需要重新证明或新增包装。对 $N\ge2$，置
$$
\Delta_N=\frac{2\pi F_N}{\tau},
\qquad H_N=\operatorname{diag}(0,\Delta_N).
$$
第一时刻的相位恰为一；第二时刻的相位由式（TM.439）精确给出。因此
$$
|\chi(\Delta_N)|^2
=1-4p_2(1-p_2)\sin^2(\pi\phi^{-N}),
\tag{TM.440}
$$
且
$$
d_\diamond\!\left(
(\mathcal C_\nu^{H_N})^k,\mathcal P_{H_N}
\right)
=\frac12
\left[1-4p_2(1-p_2)\sin^2(\pi\phi^{-N})\right]^{k/2}.
\tag{TM.441}
$$
因为 $F_N\to\infty$、$\phi^{-N}\to0$，对每个固定有限 $k$，右侧趋于 $1/2$，而能隙趋于无穷。若三权重均为 $1/3$，方括号内系数为
$1-\frac89\sin^2(\pi\phi^{-N})$。

还可直接保留有限尺度下的下界。由
$\sin^2(\pi\phi^{-N})\le\pi^2\phi^{-2N}$ 及
$(1-x)^k\ge1-kx$ 对 $x\in[0,1]$、整数 $k\ge1$ 成立，
$$
d_\diamond\!\left(
(\mathcal C_\nu^{H_N})^k,\mathcal P_{H_N}
\right)
\ge\frac12
\sqrt{\max\{0,\,
1-4\pi^2p_2(1-p_2)k\phi^{-2N}\}}.
\tag{TM.442}
$$
这里先对式（TM.441）的平方使用 Bernoulli 不等式，再开平方，避免将非整数 $k/2$ 直接套入整数版本。若 $k\phi^{-2N}$ 保持很小，剩余误差保持接近 $1/2$。

黄金递推在这个模型中承担的是一份可计算的近共振证书：整数关系越来越接近完整整周，精确别名始终不存在，有限重复却可以任意缓慢。这连接了递推、字符相位和稳定性，不将黄金常数认作普遍最优时钟，也不将它与素数性质等同。

#### 3.2.8 精确分点与连续稳定恢复的区别

**命题 3.22（精确分点与稳定恢复）。** 无理时刻比使联合相位图
$$
J:\mathbb R\to\mathbb T^2,\qquad
J(\Delta)=(e^{-i\tau_1\Delta},e^{-i\tau_2\Delta})
\tag{TM.443}
$$
为连续单射。但式（TM.436）构造了
$\Delta_n\to\infty$、$J(\Delta_n)\to J(0)$，所以逆映射在其实际像上不连续。它不是把整个无界实频率轴同胚地换成两个圆周读数。

将定义域限制到固定紧能隙集合后，连续单射到 Hausdorff 空间才给出到实际像的同胚，且逆映射一致连续。这与式（TM.431）的统一相位裕度相符，但并不直接给出最优 Lipschitz 常数。

这里讨论的是两份联合相位读数的分点性；平均后的单个复数 $\chi(\Delta)$ 没有因此被证明为单射。不能把“共同固定点仅剩零差”改述为“单个平均读数完整识别所有频率”。

#### 3.2.9 共同副本时钟、独立步骤和代价

**命题 3.23（共同副本时钟与成本）。** 若每一步把同一个随机增量 $T_j$ 作用于所有 $m$ 个副本，则生成元为
$$
H^{(m)}=\sum_{\ell=1}^m
 I^{\otimes(\ell-1)}\otimes H\otimes I^{\otimes(m-\ell)}.
$$
当不同步骤 $T_1,\ldots,T_k$ 独立时，上述全部公式应用于
$(\mathcal C_\nu^{H^{(m)}})^k$。它们要求对总能量的不同值计数，并用总能隙计算 $q_H$ 或能隙带；不能沿用单副本的最小非零能隙和能量块数。

若同一步中每个副本各自独立抽时钟，则通道为
$(\mathcal C_\nu^H)^{\otimes m}$，属于不同联合协议。以两个副本、
$H=\operatorname{diag}(0,E)$、$E>0$ 为例，共同时钟完整保留
$|01\rangle\langle10|$，因为两个基字总能量同为 $E$；独立副本时钟在每步给该块乘以
$\chi(-E)\chi(E)=|\chi(E)|^2$，无理时刻比下经过 $k$ 步趋零。它可以在实际输入
$(|01\rangle+|10\rangle)/\sqrt2$ 的密度态中体现。

跨步骤独立同分布增量的总等待时间
$S_k=\sum_{j=1}^kT_j$，其均值为
$$
\mathbb E S_k=k(p_1\tau_1+p_2\tau_2).
\tag{TM.444}
$$
若所有步骤重复使用最初的同一次抽样 $T$，系数变成
$\chi(k\Delta)$，一般不是 $\chi(\Delta)^k$。例如三权重均为 $1/3$ 时，整个共享抽样协议始终是一份至多三相位的混合，不能直接借用独立卷积的几何收缩证明。

#### 3.2.10 相同步数与平均等待，并不固定模式分辨率

**反例 3.24（相同等待成本与不同分辨率）。** 三原子律的平均等待为
$$
\mu=p_1\tau_1+p_2\tau_2>0.
\tag{TM.445}
$$
以相同均值定义另一份实际实验律
$d\eta_\mu(t)=1_{\{t\ge0\}}\mu^{-1}e^{-t/\mu}\,dt$。
直接积分给
$$
\widehat\eta_\mu(\Delta)=\frac1{1+i\mu\Delta},
\qquad
|\widehat\eta_\mu(\Delta)|=(1+\mu^2\Delta^2)^{-1/2}.
\tag{TM.446}
$$
对两能级 $H_\Delta$，式（TM.435）的相同证明给
$$
d_\diamond\!\left(
(\mathcal C_{\eta_\mu}^{H_\Delta})^k,\mathcal P_{H_\Delta}
\right)
=\frac12(1+\mu^2\Delta^2)^{-k/2}.
\tag{TM.447}
$$
因此任意 $g>0$、整数 $k\ge1$ 都有精确比较
$$
\begin{aligned}
\sup_{\Delta\ge g}
d_\diamond\!\left(
(\mathcal C_\nu^{H_\Delta})^k,\mathcal P_{H_\Delta}\right)
&=\frac12,\\
\sup_{\Delta\ge g}
d_\diamond\!\left(
(\mathcal C_{\eta_\mu}^{H_\Delta})^k,\mathcal P_{H_\Delta}\right)
&=\frac12(1+\mu^2g^2)^{-k/2}.
\end{aligned}
\tag{TM.448}
$$
第一行仍取无理时刻比的三原子律；第二行不需要能隙上界。两份协议均跨步骤独立，均执行 $k$ 步，均有平均总等待 $k\mu$。差异来自完整时钟分布的 Fourier 模式：有限原子律有高频近回返，指数律的模随 $|\Delta|$ 增大而下降。相同步数与均值不意味着相同支持、尾部、方差或相位分辨率；该比较不证明指数律在任何更大实验类中最优。

这些通道均指随机时间记录被丢弃之后的系统输出，diamond 比较允许任意输入、外部参考及终端测试。若实验保留实际抽样时间，应改为比较含该记录的联合输出；在允许相应控制时，已知时间还可能用于逆演化，不能把丢弃记录后的去相位当作联合信息已经消灭。若只允许与生成元对易的终端效果，两份输出与输入对这些效果都有相同读数，此 diamond 差异不自动成为该受限语言的信号。

把 $\nu$ 换成 $\eta_\mu$ 改变了随机实验律，并非只换时钟坐标。均值相同只结算一个成本坐标，未认证两种时钟制备、维持或访问具有相同总成本。

#### 3.2.11 已有来源与适用范围

黄金恒等式（TM.439）已有精确仓内 owner，按不可变项目快照
19a8543ea50538700a993a51989d9cbc7b5bf4fd：

- D5/S1/Scale/FibonacciErrorRatio.lean:21，
  D5.S1.Scale.fibonacci_golden_residual，逐字给
  $(F_N:\mathbb R)\phi-F_{N+1}=-(-1/\phi)^N$。
- D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn.lean:113，
  fibonacci_near_return，已组织黄金圆周旋转的 Fibonacci 近回返、交替缺陷及衰减。其回返步长为 $1/\phi$，本文时钟比为 $\phi$；二者模整数关系一致，但不把该声明直接冒充本文的量子通道距离定理。

该快照所钉 Mathlib 修订为
db584cd6d46c92f209a44c0f1c829460d327499d。
Mathlib/NumberTheory/Real/GoldenRatio.lean 中，Real.fib_succ_sub_goldenRatio_mul_fib（第211行）给
$F_{N+1}-\phi F_N=\psi^N$，Real.inv_goldenRatio（第48行）给
$\phi^{-1}=-\psi$；Real.coe_fib_eq（第198行）为 Binet 公式；Real.goldenRatio_irrational（第120行）给黄金比无理性。本文只直接复用这些已存在的算术事实，不新增绑定声明。

式（TM.420）—（TM.448）的整体通道结论是有限模型中的普通推导，尚无新增 Lean 核验。它们不推出任意无限谱上的 diamond 收敛，不赋予受限观察者额外效果权限，不证明时钟制备免费，也不将能量 pinching 自动解释为全部物理熵、测不准或时间箭头。

## 追加锚（本行以下为增补区）

## 4. 时钟是协议读出：共同来源、联合记录与恢复

前面的时钟章节已经区分了共同副本时钟、独立副本时钟以及丢弃实际抽样记录后的通道。这里把这一区别写成同一边界语言：时钟读数不是脱离过程的绝对参数，而是观察者对事件路径的一种协议读出。

### 4.1 路径、时钟和记录的联合边界

令 \(H\) 是同一共同来源上实际可实现的有限路径集合。路径可以包含配置、合法动作、输出和事件记录；令

$$
\tau:H\to T,\qquad
R:H\to\mathcal R
$$

分别是时钟读出和档案读出。对允许协议 \(p\in P\)，设完整评价为

$$
E:H\times P\to L.
$$

只保存时钟的表示 \(\tau\) 对协议族 \(P\) 充分，当且仅当

$$
\tau(h)=\tau(h')
\Longrightarrow
\forall p\in P,\ E(h,p)=E(h',p).
\tag{TM.449}
$$

若存在时钟相同而记录不同、并且某个后续协议能读取该记录的两条路径，则式（TM.449）失败。此时联合边界

$$
B(h)=(\tau(h),R(h))
\tag{TM.450}
$$

至少要保留这份区别；其核是

$$
\ker B=\ker\tau\cap\ker R.
\tag{TM.451}
$$

这不是把“时间”和“记忆”当作两种外部实体，而是说明同一条实际路径的两个读出只有在指定协议下才能分别或联合地被商掉。若 \(R\) 能由 \(\tau\) 的实际像因子化，则它不会增加该任务的区别；否则联合记录是动态充分性的必要候选。

### 4.2 相同边缘时钟不决定共同协议

设单步时钟增量取值于 \(\{0,1\}\)。共同来源模型为

$$
\Omega_{\mathrm{com}}=\{0,1\},\qquad
(T_1,T_2)=(U,U),\qquad U\sim\operatorname{Unif}\{0,1\}.
$$

独立来源模型为

$$
\Omega_{\mathrm{ind}}=\{0,1\}^2,\qquad
(T_1,T_2)=(U_1,U_2),
$$

其中 \(U_1,U_2\) 独立且均匀。两个模型的每个边缘读出都满足

$$
\Pr(T_i=0)=\Pr(T_i=1)=\frac12.
$$

但是协议

$$
p_{\mathrm{eq}}(t_1,t_2)=\mathbf 1_{\{t_1=t_2\}}
$$

在共同来源模型中恒为 \(1\)，在独立来源模型中以概率 \(1/2\) 为 \(1\)。因此

$$
\boxed{
\text{相同的边缘时钟律}
\not\Rightarrow
\text{相同的联合时钟协议}.
}
\tag{TM.452}
$$

若观察者只能读取一份边缘时钟，两个来源可能暂时不可区分；一旦允许比较两个副本或读取共同记录，区别就会进入未来行为。只有把共同来源和联合时钟作为同一 \(H\) 上的实际像，才可以判定两个实验是否属于同一关系过程。

### 4.3 时钟运输的双侧条件

设两个时钟表示的路径状态分别为 \(X_1,X_2\)，允许的协议分别为 \(P_1,P_2\)，评价为

$$
E_i:X_i\times P_i\to L.
$$

状态运输 \(f:X_1\to X_2\) 与协议回拉 \(g:P_2\to P_1\) 只有在

$$
E_2(f(x),p)=E_1(x,g(p))
\tag{TM.453}
$$

时才表示同一个时钟接口的改写。若只给出 \(f\) 而没有 \(g\)，只能说状态数值被重标，不能说所有可执行的时间实验被保留。

两个这样的改写可按

$$
(f_2,g_2)\circ(f_1,g_1)
=(f_2\circ f_1,\;g_1\circ g_2)
\tag{TM.454}
$$

复合；评价保持由式（TM.453）逐项代入得到。若中间时钟只在实际路径像上取值，复合也必须限制在该实际像；把两个边缘时钟的值域自由相乘会重新引入未由共同来源实现的组合。

于是，空间切面、时间读数和记忆记录之间的“同一表达”应采用下列可检验判据：

$$
\boxed{
\text{同一来源实际像}
+
\text{状态运输}
+
\text{协议回拉}
+
\text{评价保持}.
}
\tag{TM.455}
$$

缺少共同来源时，边缘数值可以相同而联合实验不同；缺少协议回拉时，状态坐标可以相互计算而后续操作不再对应；缺少评价保持时，所谓换钟只是改名，不能恢复原任务。

本节的有限共同源计算和双侧运输是对边界动力学第 15 节的应用，未新增 Lean 声明。它把“时钟、空间切面和记忆”统一到同一个联合读出核上，同时保留了实际记录、操作权限和共同来源的区别。

## 4.99 追加锚

## 5. 时钟、协议与记忆的双侧恢复

第 4 节把时钟从外部参数改成路径上的读出。本节把这一点再压缩为一个可检验的双侧接口，并说明何时一个时钟摘要也足以承担记忆的动态任务。

### 5.1 把时钟实验写成评价，而不是单独的数轴

令 $X$ 是包含路径位置、参考、实际档案和权限的联合状态，$P$ 是允许的时钟协议。协议可以要求读取一个 tick、比较两个副本、检查记录、改变切面或报告失败。把所有任务要求的标签打包为

$$
E_{\rm clk}:X\times P\to L,
$$

其中 $L$ 同时承载合法性、时钟读数、事件记录和终止原因。对 $x\in X$ 定义完整时钟行

$$
R_x:P\to L,\qquad R_x(p)=E_{\rm clk}(x,p).
$$

于是两个状态具有相同“时钟”只有在声明的协议族下行相同；一个单独的数值 $\tau(x)$ 只是该行的某个投影。若

$$
\tau(x)=\tau(y)\Longrightarrow R_x=R_y,
\tag{TM.456}
$$

则 $\tau$ 对该时钟任务充分；否则必须把遗漏的记录、参考或权限并入摘要。式（TM.456）把“时钟是时间坐标”改成了一个纤维常值条件。

### 5.2 何时记忆不会增加时钟边界

设 $R:X\to A$ 是档案读出。若存在 $h$ 使

$$
R=h\circ\tau,
\tag{TM.457}
$$

则在这组时钟协议下，档案不会再切开 $\tau$ 的纤维；联合边界 $(\tau,R)$ 与 $\tau$ 具有同一任务商。反之，若有 $x,y$ 满足

$$
\tau(x)=\tau(y),\qquad R(x)\ne R(y),
$$

且某个后续协议能读取这份档案，则只保存时钟会把不同未来行为合并，式（TM.456）失败。

一个最小反例是三条实际路径 $x_a,x_b,x_c$，它们当前 tick 都为 $0$；下一步分别保持 tick 为 $0$、跳到 tick 为 $1$、或保持 tick 为 $1$，并把不同事件写入档案。若协议包含“读取事件标签”，三条路径的行不同；当前 tick 不是动态充分边界。只有把事件标签或等价的未来残余加入边界，才可定义统一的时钟后继。

### 5.3 运输时钟时必须同时运输协议

设另一份时钟接口为 $(X',P',E')$。状态映射 $f:X\to X'$ 与协议回拉 $g:P'\to P$ 表示同一时钟实验，当且仅当

$$
E'(f(x),p')=E(x,g(p'))
\qquad(x\in X,p'\in P').
\tag{TM.458}
$$

若 $f$、$g$ 都落在各自的行列商上，则它们诱导商之间的运输；两个运输按

$$
(f_2,g_2)\circ(f_1,g_1)
=(f_2\circ f_1,\;g_1\circ g_2)
\tag{TM.459}
$$

复合。式（TM.458）逐项给出评价保持，实际像条件则排除把两个边缘时钟的值域自由相乘。

因此，空间切面、时钟读数和记忆记录可以被看作同一个联合评价的不同投影，但只有在

$$
\boxed{
\text{共同来源实际像}
+\text{状态运输}
+\text{协议回拉}
+\text{评价保持}
}
$$

同时成立时，才是同一过程的不同表达。该判据承接边界动力学第 23 节的双侧商；本节的时钟专门化没有新增 Lean 声明。

## 5.99 追加锚

### 5.4 追加勘误：完整时钟行、路径例子与商上的运输

第5.1—5.3节的“时钟”必须始终相对于声明的协议族理解。对联合状态 $x$，完整对象是时钟行
\[
R_x:P\to L,\qquad R_x(p)=E_{\rm clk}(x,p),
\]
而标量 $\tau(x)$ 只是该行的一个投影。只有在明确量化了全部 $p\in P$ 并证明
\[
\tau(x)=\tau(y)\Longrightarrow R_x=R_y
\tag{TM.460}
\]
时，才可称该标量对指定时钟任务充分；单次 tick 数值相同不等于完整协议行为相同。若某协议读出档案、失败标签、权限或参考，均须已经包含在 $E_{\rm clk}$ 的结果值 $L$ 中。

第5.2节的三路径例子应采用数值一致的未来读出。可取三条实际路径 $x_a,x_b,x_c$，当前标量 tick 均为 $0$，而各自下一次完整读出分别为
\[
R_{x_a}(p_*)=(0,\mathsf a),\qquad
R_{x_b}(p_*)=(1,\mathsf b),\qquad
R_{x_c}(p_*)=(2,\mathsf c),
\]
其中第一分量是下一 tick、第二分量是事件标签；其余协议值可按同样方式固定。三行因此可不同，而当前 $\tau=0$ 完全相同，说明标量边界不是动态充分状态。这个修正只使用三种互相一致的未来读出，不把同一路径同时写成互相矛盾的 tick 后继。

若档案读出 $R:X\to A$ 满足 $R=h\circ\tau$，这里的 $h$ 只需定义在实际像 $\operatorname{im}(\tau)$ 上；名义陪域中不可达的标量值不构成观察接口。在此实际像约定下，$(\tau,R)$ 与 $\tau$ 对该档案—时钟任务诱导同一商。反向若存在同一 $\tau$ 纤维中不同的 $R$，且某合法后续协议能读取它，则必须扩大边界。

第5.3节的运输式
\[
E'(f(x),p')=E(x,g(p'))
\tag{TM.461}
\]
首先说明评价保持。要使 $f$ 与 $g$ 真正下降到状态行和协议列的商，必须分别保持相应 kernel：$R_x=R_y$ 应推出 $R'_{f(x)}=R'_{f(y)}$，而 $C_{p'}=C_{q'}$ 应推出 $C_{g(p')}=C_{g(q')}$；在实际像上再由代表元定义诱导映射。满射、双射或明确的实际像双向条件，才足以把这些诱导映射称为等价或互相恢复。没有这些条件，式（TM.461）只是一项评价保持的运输，不是任意时钟结构的可逆同一化。

因此，本卷的时钟结论都限定在固定的实际来源、实际状态像和声明的协议族上。数学定义的完整行 $R_x$ 或有限未来 profile 不是观察者已经取得的档案；只有执行相应协议并把结果写入可访问记忆，才可把该信息用于后续选择。第5.1—5.3节的原有结论保留，但不再把标量读数、未执行的未来表或单向运输冒称为动态完备的时钟坐标。

## 5.99 追加锚（勘误后）

## 5.99 追加勘误：评价类型、正向 kernel 保持与相对时间

为使第5.3—5.4节自足，以下统一记号。令

$$
E:=E_{\rm clk}:X\times P\to L,
$$

并令另一接口评价为

$$
E':X'\times P'\to L'
$$

；若要逐字比较结果，另假设 $L'=L$，否则在运输式中显式加入标签映射 $\lambda:L\to L'$。对 $x\in X$、$x'\in X'$ 和协议 $p\in P,p'\in P'$ 定义

$$
R_x(p):=E(x,p),\qquad R'_{x'}(p'):=E'(x',p'),
$$

以及协议列

$$
C_p(x):=E(x,p),\qquad C'_{p'}(x'):=E'(x',p').
$$

这里 $R$ 是状态行，$C$ 是协议列，避免把档案读出也记作 $R$。若档案读出另记为 $r_{\rm arch}:X\to A$，则 $r_{\rm arch}$ 与时钟行 $R_x$ 不再混用。

在

$$
E'(f(x),p')=E(x,g(p'))
\tag{TM.462}
$$

下，逐点代入立即得到正向 kernel 保持：

$$
R_x=R_y\Longrightarrow R'_{f(x)}=R'_{f(y)},
\tag{TM.463}
$$

以及

$$
C'_{p'}=C'_{q'}\Longrightarrow C_{g(p')}=C_{g(q')}.
\tag{TM.464}
$$

因此 $f$ 和 $g$ 总能在相应方向下降到实际像商。满射、双射或逐像条件只在需要反向反射、商上的满射或双侧等价时增加：例如，$g$ 在实际协议像上满射并结合源状态行分离，才可把协议列的下降提升为反向反射；$f$ 在实际状态像上满射并结合源协议列分离，才可得到状态行的反向反射。原第5.4节若把 (TM.464) 本身写成额外条件，方向是不准确的；本条把它改读为由 (TM.462) 自动推出的正向性质。

同样，跨接口形式 $T:X\to X'$、$G:P'\to P$ 下，

$$
E'(T x,p')=E(x,Gp')
$$

自动给出

$$
R_x=R_y\Longrightarrow R'_{T x}=R'_{T y},
\qquad
C'_{p'}=C'_{q'}\Longrightarrow C_{G p'}=C_{G q'}.
\tag{TM.465}
$$

同接口写法只是 $X'=X$ 的特例。若要声称商上的双射，还必须补上相应实际像的满射或逐像覆盖，以及目标行列的分离条件。

最后，第4.4节关于时间的结论只直接支持因果顺序和严格时间标签的运输。不能仅由 `edge_time`、`path_time` 或平移不变性声称一个接口恢复

$$
\tau(y)-\tau(x).
$$

只有在把

$$
\Delta(x,y):=\tau(y)-\tau(x)
$$

明确声明为读出，并证明它在接口的每个观察纤维上恒定时，才有相对时间差的因子化。现有路径结果足以支持“先后关系”这一较弱结论；绝对原点以及数值差的恢复仍是额外的任务条件。

这些勘误只修正记号、蕴含方向和结论强度，不改变第5.1—5.3节关于完整协议行、共同来源、状态运输和协议回拉的主张。没有新增 Lean 声明，Claim status 仍为 open。

## 5.99 追加锚（类型与方向勘误后）

## 6. 时钟评价的行列商与双侧恢复

第5节的协议回拉可以用一个双侧评价核完全刻画。令

$$
E:X\times P\to L,
$$

并定义状态行与协议列

$$
R_x(p)=E(x,p),qquad C_p(x)=E(x,p).
$$

完整协议 signature 为

$$
\Sigma_E(x):P\to L,qquad \Sigma_E(x)(p)=E(x,p).
$$

仓内 `UnifiedObserverRepresentation.unified_observer_representation` 给出两个实际像判据。首先，

$$
X/\ker(\Sigma_E)
$$

在实际像上与 $\operatorname{im}(\Sigma_E)$ 唯一等价；其次，任意摘要 $r:X\to A$ 能恢复每个固定协议的时钟读出，当且仅当

$$
 r(x)=r(y)\Longrightarrow
\forall p\in P,\quad E(x,p)=E(y,p).
\tag{TM.466}
$$

等价地，$\ker(r)\subseteq\ker(\Sigma_E)$。所以“一个时钟摘要足以支持所有声明协议”不是看它是否包含某个标量，而是看它是否切开了完整协议行的所有差异。实际像上的因子是唯一的；名义陪域中不可达的读数不构成额外状态。

若还要把另一接口 $(X',P',E')$ 证明为同一双侧时钟结构的改写，取状态映射 $f:X\to X'$、协议映射 $g:P\to P'$，并要求存在满射映射与评价因式分解

$$
E(x,p)=E'(f(x),g(p)).
\tag{TM.467}
$$

若目标状态和目标协议分别由全部评价行、列分离，即

$$
\bigl(\forall p',,E'(x'_1,p')=E'(x'_2,p')\bigr)\Longrightarrow x'_1=x'_2,
$$

$$
\bigl(\forall x',,E'(x',p'_1)=E'(x',p'_2)\bigr)\Longrightarrow p'_1=p'_2,
$$

则仓内 `DoubleExtensionalQuotientUniversality.double_extensional_quotient_universal_minimality` 给出状态行商与 $X'$、协议列商与 $P'$ 的唯一双侧等价，并使评价方格交换。这里的状态满射与协议满射是得到商上双射的条件；式 (TM.467) 本身只给评价保持和正向下降。

因此，时钟、空间切面和记忆若都来自同一个评价 $E$，它们的关系层次是：

$$
\boxed{
\text{完整协议行/列}
\longrightarrow
\text{行商与列商}
\longrightarrow
\text{各自的实际像表示}
}
$$

单边摘要只须满足 (TM.466) 的核包含；双侧等价还须满足满射和行列分离。若某个协议读取隐藏档案、失败标签或权限，必须把它们放入 $L$，否则 row kernel 会错误地把不同未来协议合并。

这个双侧结构与边界卷的动态完成相接：把协议词扩展为有限或无限的动作索引，就得到共同未来 profile；把协议限制为某个时钟族，就得到本节的时钟行。动态更新仍需另证交换式 $q\circ F=\bar F\circ q$，静态行列商不能代替授权和后继的下降条件。

本节直接对应仓内 `UnifiedObserverRepresentation` 与 `DoubleExtensionalQuotientUniversality` 的既有形式化结果；理论中的跨接口运输和时钟专门化仍为 open，没有新增 Lean 声明。

## 6.99 追加锚

## 7. 时钟评价的双轴动态半共轭

第6节给出了静态状态行与协议列商。本节加入更新与协议续接，说明什么时候两条轴可以同时下降到商上。

### 7.1 原始评价层的两条交换式

令

$$
E:X\times P\to L,
\qquad F:X\to X,
\qquad \delta:P\to P,
$$

并假设

$$
\boxed{
E(Fx,p)=E(x,\delta p)
\qquad(x\in X,p\in P).
}
\tag{TM.468}
$$

定义状态行与协议列

$$
\Sigma(x):=E(x,-):P\to L,
\qquad
\Gamma(p):=E(-,p):X\to L.
$$

在函数空间上令

$$
S_\delta(r):=r\circ\delta,
\qquad
T_F(c):=c\circ F.
$$

逐点展开 (TM.468) 得到两个交换式

$$
\boxed{
\Sigma\circ F=S_\delta\circ\Sigma,
\qquad
\Gamma\circ\delta=T_F\circ\Gamma.
}
\tag{TM.469}
$$

第一式把状态更新写成协议坐标的回拉，第二式把协议续接写成状态坐标的回拉。这是同时运输两条轴的充分条件；只要求商上的动态下降时，分别保持状态行 kernel 与协议列 kernel 即可，(TM.468) 不必是必要条件。

### 7.2 行商、列商与评价方格

令

$$
X_R:=X/\ker(\Sigma),qquad
P_C:=P/\ker(\Gamma).
$$

由 (TM.469)，$S_\delta$ 在行像上下降到一个映射 $\bar S_\delta$，$T_F$ 在列像上下降到 $\bar T_F$。评价本身也下降为

$$
\bar E([x],[p])=E(x,p),
$$

前提是代表元改变时行、列相等都保持 $E$ 的值。于是

$$
\bar\Sigma\circ\bar F=\bar S_\delta\circ\bar\Sigma,
\qquad
\bar\Gamma\circ\bar\delta=\bar T_F\circ\bar\Gamma,
\tag{TM.470}
$$

并且状态更新、协议续接与双侧评价组成交换方格。`UnifiedObserverRepresentation` 与 `DoubleExtensionalQuotientUniversality` 支撑静态行列商；`DynamicProfileCausalClosure` 支撑状态 profile 的右移，(TM.468)—(TM.470) 补上协议轴的动态回拉。

### 7.3 反射与双射需要满射或逐像条件

若 $\delta$ 满射，则 $r_1\circ\delta=r_2\circ\delta$ 能反推出 $r_1=r_2$；因此协议续接在行坐标上具有反射性。若 $F$ 满射，则 $c_1\circ F=c_2\circ F$ 能反推出 $c_1=c_2$；因此状态更新在列坐标上具有反射性。对实际像而言，也可以用“源行/列由相应像决定”的逐像条件替代全域满射。

若还证明诱导商映射的满射性，则相应动态商映射为双射；两条轴同时满足这些条件时，才可称行商与列商上的时钟过程双向同构。单向 (TM.468) 只保证下降，不保证反向恢复。

一个满足 (TM.468) 但行更新不反射的例子是

$$
X=\{0,1\},\quad P=\{p,q\},\quad F\equiv0,
\quad\delta(p)=\delta(q)=p,
$$

取

$$
E(0,p)=E(0,q)=0,
\quad E(1,p)=0,
\quad E(1,q)=1.
$$

两条源状态行分别为 $(0,0)$ 与 $(0,1)$，但更新后都成为状态 $0$ 的行；由于 $\delta$ 非满射，行商更新不能反射原有行差异。列轴有完全对偶的例子：取非满射 $F$，让两个不同协议列在 $\delta$ 后合并。可见 (TM.468) 的评价保持不等于双轴可逆性。

### 7.4 协议词的闭合

若原语操作为 $a\in A$，并为每个原语指定状态更新 $F_a$ 与协议续接 $\delta_a$，要求

$$
E(F_a x,p)=E(x,\delta_a p).
\tag{TM.471}
$$

并规定

$$
F_{uv}=F_v\circ F_u,
\qquad
\delta_{uv}=\delta_u\circ\delta_v
$$

（按协议回拉的反变方差），则对任意操作词 $w$ 归纳得到

$$
E(F_w x,p)=E(x,\delta_w p).
\tag{TM.472}
$$

若协议本身是自由幺半群，结合律与空词恒等式提供词闭合；若有类型化失败域，必须把可执行性和失败标签一起放进 $E$，不能只在名义 $A^*$ 上写 (TM.472)。`EffectiveProtocolActionMonoid` 与 `DynamicProfileCausalClosure` 分别支撑协议词的有效作用商和完整 profile 的右移。

本节把“时钟读数、状态更新、协议续接”收束为两轴动态半共轭。它明确区分原始评价层的充分条件、商上下降的较弱条件，以及需要满射/逐像分离才能得到的反射和双向恢复。没有新增 Lean 声明，理论结论 Claim status 为 open。

## 7.99 追加锚

## 8. 双侧运输记号与满射条件勘误

第6.3节的 (TM.467) 使用的是正向协议映射

$$
 f:X\to X',\qquad g:P\to P',
$$

并且在需要目标行列商双射时，明确要求 $f$ 与 $g$ 各自在相应实际像上满射；“存在满射映射”不能省略这两个对象。第5.4节的 (TM.461)—(TM.465) 使用的是协议回拉

$$
G:P'\to P,
$$

这是有意的反变方向，不能把它与第6.3节的正向 $g:P\to P'$ 当作同一个符号。两种写法可通过 $G$ 为 $g$ 的回拉或在相应实际像上取逆来连接，但需要额外的双射条件。

第6.3节的目标行列分离条件应逐字理解为

$$
\bigl(\forall p',\ E'(x'_1,p')=E'(x'_2,p')\bigr)\Longrightarrow x'_1=x'_2,
$$

$$
\bigl(\forall x',\ E'(x',p'_1)=E'(x',p'_2)\bigr)\Longrightarrow p'_1=p'_2.
$$

这里的量词后只有一个逗号；该勘误不改变双侧 extensionality 的数学条件。没有满射或逐像覆盖时，评价因式分解只能产生正向运输，不能声称目标商覆盖全部状态和协议。

## 8.99 追加锚

## 9. 时钟作为共同核上的可恢复表达

**本批导航。** 本节把时钟评价接回边界卷的共同核判据：时钟读数只有在它保留同一任务的合法性、读出、记录和后继区别时，才是空间、时间、边界与记忆的可恢复表达。本节不改判第6—8节的静态商、动态半共轭和方向勘误，也不新增 Lean 声明。

### 9.1 从评价方格得到一个时钟表示

设实际联合配置为 $S$，状态投影为 $x:S\to X$，协议投影为 $p:S\to P$，时钟评价为

$$
 E:X\times P\to L.
$$

真正可用的时钟表示不是孤立的数 $E(x,p)$，而是带协议族的行

$$
 r_{\mathrm{clock}}(s):w\longmapsto
 \operatorname{Run}_w(s)\text{ 的时钟读出、合法性和记录标签}.
 \tag{9.1}
$$

若只取 $E(x,p)$，则两个配置可能在当前读数相同，却在下一项协议的权限、失败标签或记忆更新上不同。因而时钟的精确核应定义为

$$
 s\equiv_{\mathrm{clock}}t
 \iff
 \forall w,
 \operatorname{ClockRun}_w(s)=\operatorname{ClockRun}_w(t),
 \tag{9.2}
$$

其中 $\operatorname{ClockRun}$ 至少保留时钟读数、可执行性、失败和记录。它是边界卷式 (35.1) 的未来核在时钟任务上的专门化。

### 9.2 何时能与共同边界互相恢复

令 $\equiv_\star$ 是声明的联合任务共同核，令

$$
 r_{\partial}:S\to R_{\partial},qquad
 r_{\mathrm{clock}}:S\to R_{\mathrm{clock}}
$$

分别是边界和时钟表示的实际像。若

$$
 \ker(r_{\partial})
 =
 \ker(r_{\mathrm{clock}})
 =
 \equiv_\star,
 \tag{9.3}
$$

则存在唯一双射

$$
 g_{\partial,\mathrm{clock}}:R_{\partial}\simeq R_{\mathrm{clock}},qquad
 g_{\partial,\mathrm{clock}}(r_{\partial}(s))=r_{\mathrm{clock}}(s).
 \tag{9.4}
$$

若更新和协议续接在共同核上下降，则式 (9.4) 还与相应的动态作用交换。反之，若时钟读数只满足

$$
 E(x,p)=E(x',p')
$$

而不满足式 (9.2)，式 (9.4) 只能是从边界到读数的有损投影；不能由当前时钟值恢复未来权限或完整档案。

### 9.3 递归校准不增加新的本体层

把一次校准视为协议 $c:P\to P$ 或状态参考更新 $\rho:X\to X$。若校准满足

$$
 E(\rho x,p)=E(x,c p)
$$

且校准的合法性、记录和后继同样只依赖共同核，则它仍属于同一评价方格；迭代校准给出

$$
 E(\rho^{n}x,p)=E(x,c^{n}p).
 \tag{9.5}
$$

若每次校准扩展协议族，时钟核按包含关系收缩；在有限商上最终稳定，在无限协议族上只得到交核。这里的“更高阶时钟”是协议族的闭包，不是系统外再加一个观察者。

### 9.4 反向时钟读数的边界

正向半共轭只给出

$$
 E(Fx,p)=E(x,\delta p).
$$

要从新读数恢复旧读数，至少需要：

1. $F$ 在实际来源像上可逆，或来源已限制到稳定周期核心；
2. $\delta$ 在实际协议像上有相应的逆或唯一回拉；
3. 反向协议的合法性、失败标签和档案也包含在评价中。

二点常值更新 $F(0)=F(1)=0$ 违反第一项：正向时钟可区分瞬态初态，过去线程却只有零的周期核心。故“时间读数可正向推进”与“时间读数可双向恢复”是两个不同的命题。

本节是对边界卷第35节的时钟专门化；它只给出核判据与普通数学推导。形式化结果仍以仓内既有声明为准，本节 Claim status 为 open。

## 9.99 追加锚

## 10. 剖面回拉、协议箭头与恢复层级

**本批导航。** 本节依据独立 Pro 审查，对第7—9节的动态时钟表述作一层只增勘误：严格的半共轭发生在状态行、协议列的剖面空间，而不是直接把 $F$ 与 $\delta$ 当成同方向的普通半共轭；满射性控制反射和恢复，不是商下降的前提；协议正向因子映射、回拉和动态协议更新使用不同箭头。本节不改写前文，只给出更精确的补充判据。

### 10.1 半共轭的对象是剖面空间

令

$$
 E:X\times P\to\Lambda,
 \qquad
 r_E(x):=E(x,-)\in\Lambda^P,
 \qquad
 c_E(p):=E(-,p)\in\Lambda^X.
 \tag{10.1}
$$

定义回拉算子

$$
 \delta^*:\Lambda^P\to\Lambda^P,\quad
 \delta^*(\varphi)=\varphi\circ\delta,
 \qquad
 F^*:\Lambda^X\to\Lambda^X,\quad
 F^*(\psi)=\psi\circ F.
 \tag{10.2}
$$

动态评价方程

$$
 E(Fx,p)=E(x,\delta p)
 \tag{10.3}
$$

逐点等价于

$$
\boxed{
 r_E\circ F=\delta^*\circ r_E,
 \qquad
 c_E\circ\delta=F^*\circ c_E .
}
\tag{10.4}
$$

因此，状态更新经状态行进入协议回拉的剖面空间，协议更新经协议列进入状态回拉的剖面空间。直接说“$F$ 与 $\delta$ 被 $E$ 半共轭”会掩盖这两个回拉对象的反变方向；只有在端点相同并且只看内部自映射时，方向差异才不显眼。

### 10.2 规范双商的下降不需要满射

定义

$$
 x\sim_X y\iff r_E(x)=r_E(y),
 \qquad
 p\sim_P q\iff c_E(p)=c_E(q).
 \tag{10.5}
$$

只由 (10.3) 即得

$$
 x\sim_Xy\Longrightarrow Fx\sim_XFy,
 \qquad
 p\sim_Pq\Longrightarrow \delta p\sim_P\delta q.
 \tag{10.6}
$$

故有唯一的诱导映射

$$
 \bar F:X/{\sim_X}\to X/{\sim_X},
 \qquad
 \bar\delta:P/{\sim_P}\to P/{\sim_P},
 \tag{10.7}
$$

以及规范评价

$$
 \bar E([x],[p])=E(x,p)
$$

满足

$$
 \bar E(\bar F[x],[p])
 =
 \bar E([x],\bar\delta[p]).
 \tag{10.8}
$$

这里不需要 $F$、$\delta$ 满射、单射或可逆。满射性属于之后的恢复问题；把它提前写进下降定理会把合法的非可逆动态商排除在外。

### 10.3 动态反射只需要像分离

状态商上的 $\bar F$ 是否能反推出旧状态类，取决于 $\operatorname{im}\delta$ 是否足以分离状态行：

$$
\boxed{
 \bar F\text{ 单射}
 \iff
 \Bigl[
 \forall x,y,
 \bigl(\forall p\in\operatorname{im}\delta,\ E(x,p)=E(y,p)\bigr)
 \Longrightarrow x\sim_Xy
 \Bigr].
}
\tag{10.9}
$$

对偶地，

$$
\boxed{
 \bar\delta\text{ 单射}
 \iff
 \Bigl[
 \forall p,q,
 \bigl(\forall x\in\operatorname{im}F,\ E(x,p)=E(x,q)\bigr)
 \Longrightarrow p\sim_Pq
 \Bigr].
}
\tag{10.10}
$$

诱导映射的满射也应写成模等价形式：

$$
 \bar F\text{ 满射}
 \iff
 \forall x\in X,\ \exists y,\ Fy\sim_Xx,
 \tag{10.11}
$$

$$
 \bar\delta\text{ 满射}
 \iff
 \forall p\in P,\ \exists q,\ \delta q\sim_Pp.
 \tag{10.12}
$$

所以原始 $F$ 或 $\delta$ 非满射，并不自动否定商上的双向恢复；反过来，商上双射也不说明原始元素可逆。真正需要检查的是像分离和模等价满射。

### 10.4 原始协议更新只在协议商上唯一

若同一 $F$ 与两个映射 $\delta,\delta':P\to P$ 都满足 (10.3)，则

$$
 E(x,\delta p)=E(Fx,p)=E(x,\delta'p)
 \qquad(\forall x,p),
$$

从而

$$
 \delta p\sim_P\delta'p
 \qquad(\forall p).
 \tag{10.13}
$$

因此动态评价唯一确定的是协议商上的映射

$$
 \bar\delta=\bar\delta',
$$

而不是原始协议元素本身。只有当协议列外延，即

$$
 p\sim_Pq\Longrightarrow p=q,
 \tag{10.14}
$$

才可由评价方程推出 $\delta=\delta'$。状态更新 $F$ 的唯一性有完全对偶条件。理论正文中若出现“由时钟评价唯一恢复协议更新”，应明确写成“唯一恢复到协议等价类”。

### 10.5 受限协议族的三级闭合

取受限协议族 $Q\subseteq P$，并定义

$$
 x\sim_Qy\iff
 \forall q\in Q,\ E(x,q)=E(y,q).
 \tag{10.15}
$$

要使 $F$ 在 $X/{\sim_Q}$ 上下降，准确条件是

$$
 x\sim_Qy
 \Longrightarrow
 \forall q\in Q,\ E(x,\delta q)=E(y,\delta q).
 \tag{10.16}
$$

这比字面条件 $\delta(Q)\subseteq Q$ 弱。应区分：

1. **字面闭合**：$\delta(Q)\subseteq Q$，得到原始协议族上的自映射；
2. **模列等价闭合**：每个 $\delta q$ 在协议商中由某个 $q'\in Q$ 表示，得到协议等价类上的内部运输；
3. **语义因子闭合**：满足 (10.16)，恰好足以让状态商上的下一步良定义，即使 $\delta q$ 没有单个 $Q$ 元素代表。

因此，“协议族不字面闭合就必然失败”是过强命题；真正的失败判据是语义因子闭合不成立。单输入系统的安全闭包通常取轨道族

$$
 Q^{\mathrm{orb}}
 :=
 \{\delta^n q:n\ge0,\ q\in Q\}.
 \tag{10.17}
$$

### 10.6 三种协议箭头不可混用

统一记号如下：

| 用途 | 箭头 | 评价方程 |
| --- | --- | --- |
| 静态因子或重标记 | $g:P\to P'$ | $E(x,p)=E'(f x,g p)$ |
| 求值空间回拉 | $G:P'\to P$ | $E'(f x,p')=E(x,G p')$ |
| 动态协议更新 | $\delta:P\to P$ | $E(Fx,p)=E(x,\delta p)$ |

第一行是正向重标记，第二行是协议反变回拉，第三行是同一动态端点下的协议更新。端同态把两端写成同一个 $P$ 时，方向差异容易被隐藏；涉及不同协议对象时必须保留符号区别。

非满射正向映射 $g:P\to P'$ 即使允许某个目标评价存在，也通常只能确定目标评价在 $\operatorname{im}g$ 上的值；未被覆盖的协议点可以任意延拓，因而不能声称唯一运输。正向下降本身还要求

$$
 gp=gp'\Longrightarrow
 \forall x,\ E(x,p)=E(x,p').
 \tag{10.18}
$$

否则同一目标协议会要求两个不同的源读数。

本节结论可与 CanonicalRowColumnSeparation、DoubleExtensionalEvaluationDescent、DynamicProfileCausalClosure 和既有协议闭包结果对接；它们提供静态商、剖面更新或闭包的不同支点，未合成一个新的 Lean 定理。本节 Claim status 为 open。

## 10.99 追加锚

## 11. 跨接口运输、路径无关与时钟分辨率

**本批导航。** 第10节已经区分原始评价层半共轭、状态行与协议列的商下降、像分离和协议箭头方向。本节只增加两个后续结构：不同接口之间运输时协议端的反变复合，以及分辨率改变时动态作用的跨层交换式。它们说明双侧下降、路径无关和严格时钟增长是三种不同的要求。

### 11.1 有类型的跨接口合同

令接口 $i$ 具有状态端 $X_i$、协议端 $P_i$ 和评价

$$
E_i:X_i\times P_i\to\Lambda.
$$

一条从 $i$ 到 $j$ 的合法运输由

$$
F_e:X_i\to X_j,
\qquad
\delta_e:P_j\to P_i
$$

给出。协议映射从目标端回到源端，是因为评价的第二个参数在运输中以回拉方式使用。相容律写成

$$
\boxed{
E_j(F_e x,p)=E_i(x,\delta_e p).
}
\tag{11.1}
$$

若各端取自己的评价核商 $q_i^X:X_i\twoheadrightarrow\bar X_i$、$q_i^P:P_i\twoheadrightarrow\bar P_i$，则 (11.1) 给出

$$
q_j^X\circ F_e=\bar F_e\circ q_i^X,
\qquad
q_i^P\circ\delta_e=\bar\delta_e\circ q_j^P.
\tag{11.2}
$$

这里的商映射满射只是规范商的性质，不是 $F_e$ 或 $\delta_e$ 的动态满射假设。反射和双向恢复仍需第10节的像分离、模等价满射或更强的源端满射条件。

若先走 $e:i\to j$，再走 $f:j\to k$，则状态端协变复合为

$$
F_{f\circ e}=F_f\circ F_e,
$$

而协议端反变复合为

$$
\delta_{f\circ e}=\delta_e\circ\delta_f:P_k\to P_i.
\tag{11.3}
$$

把两式写成相同次序会把回拉方向隐藏，并可能在三段以上的路径中得到错误的协议箭头。

### 11.2 平行路径的双侧等价与 holonomy

设 $\gamma,\eta$ 是从同一接口到同一接口的两条合法路径，每一步都满足 (11.1)，并记其商上的复合为 $\bar F_\gamma,\bar\delta_\gamma$ 与 $\bar F_\eta,\bar\delta_\eta$。若端点评价行、列分别外延，则有

$$
\boxed{
\bar F_\gamma=\bar F_\eta
\quad\Longleftrightarrow\quad
\bar\delta_\gamma=\bar\delta_\eta.
}
\tag{11.4}
$$

证明使用相容律把一侧动作的相等转成另一侧在全部源端口上的评价相等，再用相应的行列外延性；不需要原始动作满射。这个判据比较的是**有效动作**，即已经按评价不可区分关系商掉的动作。

因此，路径无关必须作为单独条件声明：所有被视为同一运输的平行路径都应满足 (11.4)。若接口和运输形成群胚，并且逆路径也在合法协议中，则这等价于每个闭路在两侧商上都作用为恒等。若只有有向不可逆路径，不能用“没有非平凡闭路”替代平行路径检查。

同时保持评价并不等于 holonomy 平凡。取

$$
X=P=\{0,1\},
\qquad
E(x,p)=\mathbf 1_{\{x=p\}},
$$

令 $F$ 和 $\delta$ 都翻转 $0,1$。则 (11.1) 成立，评价配对被保持；但两侧商上的单步作用仍是非恒等翻转。只有把这条闭路视为允许的 gauge 变换，或把它加入目标共同核，才能称其为“平凡”。

### 11.3 动态运输通常跨越分辨率层

令协议族按分辨率嵌套：$P_r\subseteq P_s$。定义只测试 $P_r$ 的状态商

$$
x\sim_r y
\quad\Longleftrightarrow\quad
\forall p\in P_r, E(x,p)=E(y,p),
\qquad
q_r:X\twoheadrightarrow X_r.
\tag{11.5}
$$

全局评价相容律为

$$
E(Fx,p)=E(x,\delta p).
\tag{11.6}
$$

若存在分辨率映射 $\rho$ 满足

$$
\delta(P_r)\subseteq P_{\rho(r)},
\tag{11.7}
$$

则存在唯一的跨层更新

$$
\boxed{
F_r:X_{\rho(r)}\to X_r,
\qquad
q_r\circ F=F_r\circ q_{\rho(r)}.
}
\tag{11.8}
$$

证明只需检查：若两状态在 $P_{\rho(r)}$ 上相同，则由 (11.6) 它们在 $P_r$ 上的后继读数相同。这里 $F_r$ 一般不是 $X_r$ 上的自映射；只有 $\rho(r)=r$ 或另有层标识时才能这样写。

若 $r\le s$ 且粗化映射 $\pi_{s,r}:X_s\to X_r$ 由协议包含诱导，在相应的闭合条件下有

$$
\boxed{
\pi_{s,r}\circ F_s
=
F_r\circ\pi_{\rho(s),\rho(r)}.
}
\tag{11.9}
$$

这才是“改变分辨率后仍代表同一动态运输”的交换式。它不自动给出逆极限中的实际来源，也不提供数值稳定性或观察者取得成本界。

若 (11.7) 失败，可以构造有限反例：取 $P_r=\{p_0\}$、$P_{\rho(r)}=\{p_0\}$，但 $\delta(p_0)=p_1$，其中 $p_1$ 不在低分辨率协议族；再取两个状态在 $p_0$ 上相同而在 $p_1$ 上不同。它们属于同一个 $X_{\rho(r)}$ 类，却被 $F$ 送到不同的 $X_r$ 类，因此不存在 $F_r$。缺失的不是一个数值精度，而是跨层动态闭合。

### 11.4 时钟严格增长与闭路记录不可混用

设时钟读出 $\tau:X\to T$ 从某个行为商因子化，并存在非空动作词 $w$ 使

$$
\bar F_w=\operatorname{id}
$$

在该行为商上成立。则

$$
\tau(F_w x)=\tau(x).
\tag{11.10}
$$

所以同一个闭路中的每一步不可能都要求一个只依赖商状态的标量时钟严格增加。若仍要区分绕行次数，边界必须增加路径记录、圈数或相应的 holonomy 标签；也可以限制允许路径，或放弃全局严格单调性。

这不是把“时钟”和“过程历时”拆成两个外部宇宙，而是说明它们是同一合法路径上的不同读出：时钟数值可以回到原值，事件档案和累积费用仍然不同。路径累积量只有在额外的势差条件下才可由端点表示。

### 11.5 本节的范围

本节新增的是跨接口的反变协议复合、平行路径的双侧等价、跨分辨率交换式和闭路时钟的限制。第10节的商下降、像分离和协议族闭合仍是基础；本节没有把这些普通数学推导写成新的 Lean 声明，也没有声称任意分辨率塔的逆极限都由实际配置实现。

## 11.99 追加锚

## 12. Renewal 时钟、活性策略与分辨率交换

**本批导航。** 时钟卷已有跨接口反变运输、平行路径和闭路限制。本节把“重复校准/重新取得端口”视为 renewal 事件，并区分三种常被混淆的量：路径步数、预测边界的细化深度、以及 renewal 的无穷频次。

### 12.1 路径时钟与 renewal 计数

设局部配置沿合法路径产生状态 $s_0,s_1,\ldots$，每步有非负费用 $c_t$，并给出 renewal 指示 $r_t\in\{0,1\}$. 定义

$$
T_n=\sum_{t<n}c_t,
\qquad
N_n=\sum_{t<n}r_t.
\tag{12.1}
$$

$T_n$ 是累积时钟或资源费用，$N_n$ 是实际 renewal 次数。即使每步 $c_t=1$，也可能 $N_n$ 有限；反之，零费用的校准事件可以使 $N_n$ 无限而 $T_n$ 不反映取得难度。若费用依赖动作和来源，严格的路径拼接律是

$$
T_{u v}(s)=T_u(s)+T_v(T_u s),
\tag{12.2}
$$

而不是端点标量的自动差值。`D5/S0/History/Accounting/CumulativeTax.lean` 的 `terminal_balance_eq_initial_add_tax` 是有限累加望远镜的直接形式化锚；它没有把所有路径费用化成势函数。

预测细化深度另有定义。仓内 `ClockTimeVersusRefinementDepth.clock_time_does_not_determine_refinement_depth` 给出一状态可运行任意时钟步数而边界深度为零，以及延迟四状态循环在短时钟后仍需更深预测商的反例。因此不能用 $T_n$ 或 $N_n$ 代替完成层数。

### 12.2 活性条件在时钟上的两种读法

对 renewal 集 $R$，

$$
\square\Diamond R
\quad\Longleftrightarrow\quad
\forall N\ \exists n\ge N:\ s_n\in R
\quad\Longleftrightarrow\quad
\lim_{n\to\infty}N_n=+\infty.
\tag{12.3}
$$

最后一个等价只对 $r_t=\mathbf1_R(s_t)$ 的离散事件计数成立。它没有给出相邻 renewal 之间的最大等待时间，也没有给出 $\lim T_n=\infty$；若费用可以为零，二者独立。有限控制系统中的 Büchi 秩可以给出一条所选策略下的有限回到界，但这个界属于策略和对手后继合同，不能从时钟读数单独推出。

若把 renewal 作为边界可见事件，需有

$$
\mathbf1_R(s)=\bar r(q(s)),
\qquad
q(T_a s)=\bar T_a(q(s)),
\tag{12.4}
$$

并且费用也在纤维上因子化 $c_a(s)=\bar c_a(q(s))$. 此时 (12.1) 的两种累积量都能在边界上递推。若同一 $q$-纤维含有 renewal 与非-renewal 状态，则 $\bar r$ 不存在；即使普通时钟 $T_n$ 仍可下降，活性时钟也不能由该边界计算。

### 12.3 跨分辨率的 renewal 交换式

设细、粗边界由 $\rho_{s,r}:B_s\to B_r$ 连接，动作更新为 $F_s,F_r$，renewal 标签为 $r_s,r_r$. 要让 renewal 计数在粗化后仍代表同一过程，至少要有

$$
\rho_{s,r}\circ F_s=F_r\circ\rho_{s,r},
\qquad
r_r\circ\rho_{s,r}=r_s,
\qquad
\bar c_r\circ\rho_{s,r}=\bar c_s.
\tag{12.5}
$$

第一式只说明动态交换，第二式才保证活性事件不被粗化混淆，第三式才保证费用读数一致。若策略由边界决定，还需

$$
\pi_r\circ\rho_{s,r}=\pi_s.
\tag{12.6}
$$

缺少任一项，就只能说状态轨迹有一个粗投影，不能说时钟、活性和选择器组成同一跨层过程。若恢复器 $R_r$ 只在实际来源像上定义，(12.5) 的反向交换也只能在共同实际像上声明。

### 12.4 时钟与闭路

若某个合法闭路 $w$ 在边界上诱导恒等，而每条边费用严格正，则边界上的标量时钟不能同时是状态势差：

$$
\bar F_w=\operatorname{id}
\quad\Longrightarrow\quad
V(\bar F_w b)-V(b)=0,
$$

但闭路累积费用为正。要保留绕行次数，必须把路径记录、圈数或 renewal 计数加入记忆；或者只要求费用满足 (12.2) 的路径累积而不要求端点势差。这个限制与第11.4节的闭路时钟结论一致，新增的是 renewal 事件和跨分辨率条件。

本节只给有限、确定、已声明动作与费用的普通推导。概率活性、无限费用、连续时间停止时刻和测量反作用需要额外的联合核及可积性假设。Claim status: open；没有新增 Lean 声明。

## 12.99 追加锚

## 13. 档案能否恢复路径时钟：同步状态对与有限反例界

**本批导航。** 第12节区分了路径费用、renewal 次数和预测细化深度，但尚未回答一个有限判定问题：观察者不保存每步时钟增量，只保留动作与读数时，能否在每一个有限前缀恢复累计时钟？本节给出同步状态对判据、状态数平方的失败证人长度界，以及实现恢复时仍需增加计数记忆的例子。这里只研究精确给定的有限确定性模型，Claim status: open。

### 13.1 共同模型、可见档案与隐藏时钟

设非空有限配置集 $X$ 的大小为 $n$，初始可能配置为非空集合 $X_0\subseteq X$。所有初始时钟均为零。动作集 $A$ 与读数集 $Y$ 有限，每个动作给出部分函数

$$
F_a:D_a\to X,\qquad
\ell_a:D_a\to Y,\qquad
c_a:D_a\to\mathbb Z .
\tag{13.1}
$$

费用可取负数以包含校准差；非负整数时钟是其特例。一个合法执行的可见档案与累计时钟分别为

$$
w=(a_0,y_0)\cdots(a_{k-1},y_{k-1}),
\qquad
C(w;x_0)=\sum_{t<k}c_{a_t}(x_t),
\tag{13.2}
$$

其中 $x_{t+1}=F_{a_t}(x_t)$、$y_t=\ell_{a_t}(x_t)$。动作也留在档案中，避免把不同操作的相同输出误认为同一实验。若任务保留失败，须为失败声明一个记录和后继，再纳入同一有限系统；本节的合法档案不把失败隐去后继续运行。

称时钟可由档案逐前缀恢复，是指存在实际档案集上的函数 $\Gamma$，使每个初始配置及其每段合法执行都满足

$$
\Gamma(w)=C(w;x_0).
\tag{13.3}
$$

这比只在某个终止点恢复总费用强；中间误差在后面抵消，不能满足 (13.3)。

### 13.2 同步状态对判据

构造顶点集 $X\times X$ 上的有向图。若 $x,\tilde x\in D_a$ 且

$$
\ell_a(x)=\ell_a(\tilde x)=y,
$$

便有一条具名同步边

$$
(x,\tilde x)
 \xrightarrow{a/y}
(F_a x,F_a\tilde x),
\qquad
\delta_a(x,\tilde x)=c_a(x)-c_a(\tilde x).
\tag{13.4}
$$

初始顶点集为 $X_0\times X_0$。同步路径恰好代表具有相同完整可见档案的两条实际执行；沿路径的 $\delta$ 之和就是两条累计时钟之差。图中的同步只用于比较实际候选，不授予观察者同时取得两个隐藏配置的权限。

**定理 13.1（逐前缀时钟恢复的局部证书）。** 以下三项等价：

1. 存在满足 (13.3) 的档案恢复器。
2. 每条从初始状态对出发的同步有限路径，费用差总和为零。
3. 每条起点可从 $X_0\times X_0$ 到达的同步边，都有 $\delta=0$。

证明。前两项由同步路径和成对实际执行的对应得到。第三项使路径上的每项费用差为零，推出第二项。反向，对任意可达同步边，取到其起点的同步路径；第二项分别作用于此前缀和再接一条边的路径，两式相减得到该边的 $\delta=0$。这里必须保留每个前缀，不能只使用终止路径。证毕。

这给出了比“存在某个因子化”更具体的有限证书：查找可达状态对，并逐边核对费用差。它无需枚举全部长度的历史。

### 13.3 不可恢复性有状态数平方的有限证人

**定理 13.2（有限时钟歧义界）。** 若 (13.3) 失败，则存在两条来自 $X_0$、可见档案相同而累计时钟不同的执行，其共同长度不超过 $n^2$。

证明。由定理13.1，存在可达且 $\delta\ne0$ 的同步边。取从初始顶点集到其起点的最短路径；它没有重复顶点，长度 $k$ 至多为 $n^2-1$。若这条前缀的总费用差已经非零，它就是长度 $k$ 的证人；若其总费用差为零，接上所选边后费用差非零，得到长度 $k+1\le n^2$ 的证人。证毕。

因此，针对这个完整、精确给定的模型，

$$
\begin{gathered}
\text{所有长度不超过 }n^2\text{ 的同档案执行具有同一时钟}\\
\Longleftrightarrow
\text{所有有限长度都可由档案恢复时钟}.
\end{gathered}
\tag{13.5}
$$

这个界是充分界，本节不主张其锐性。它既不是“任意有限观察都能认证无限模型”，也不是一个未知系统的样本复杂度界：$X$、全部合法边、读数和费用都必须已被精确给出。若费用以一般可计算实数名字给出，逐边判等未必可判；本节采用整数费用，避开了这个额外问题。

### 13.4 恢复器怎样成为内部记忆更新

对实际档案 $w$，令

$$
B(w)=\{x_k:\text{某个 }x_0\in X_0
              \text{ 产生档案 }w\}.
\tag{13.6}
$$

这是同一模型和同一档案下的实际末态集合。读到下一对 $(a,y)$ 后，

$$
B(w(a,y))
=
\{F_a x:x\in B(w)\cap D_a,\ \ell_a(x)=y\}.
\tag{13.7}
$$

当定理13.1成立且该分支非空时，集合右侧的全部来源状态都具有同一费用。把此公共值记为 $d(B(w),a,y)$，便有

$$
(B,C)\xrightarrow{a/y}
\bigl(B',C+d(B,a,y)\bigr).
\tag{13.8}
$$

证明公共值存在时，任取两个候选来源状态；它们分别有一条产生同一 $w$ 的实际历史，故形成一个可达同步顶点。再接相同 $(a,y)$ 的边，定理13.1给出费用相等。由 (13.8) 归纳即可在内部维护 $\Gamma(w)$，不需要读取真正的隐藏状态。

候选集合的取值至多为 $2^n-1$，但累计整数 $C$ 仍可能无界。因此“存在恢复规则”“有限种候选边界”和“固定有限 bit 记忆能保存全部时钟”是三个不同结论。实际选择动作还须使用可访问记忆，并对希望保证成功的所有候选检查合法性；(13.7) 的事后分支过滤不等于事前已取得执行权限。

### 13.5 端口空间的恢复与隐藏状态的恢复分开

给定空间接口读出 $s:X\to I$，在实际档案 $w$ 后恢复当前接口的充要条件是 $s$ 在 $B(w)$ 上恒定。对全部档案同时成立，等价于每个可达同步顶点 $(x,\tilde x)$ 都满足

$$
s(x)=s(\tilde x).
\tag{13.9}
$$

恢复原始当前配置则要求更强的条件 $x=\tilde x$，即全部可达同步顶点都在对角线上。一般接口条件 (13.9) 与时钟恢复的逐边条件 $\delta=0$ 互不推出；但若在每个前缀都能恢复完整当前配置，则每条可达同步边的两个来源相同，确定性费用立即给出 $\delta=0$，因而必能恢复时钟。反向不成立，费用相同的不同隐藏配置仍可永久无法区分。

若接口条件 (13.9) 与定理13.1同时成立，档案可确定当前接口和累计时钟；内部记忆 $(B,C)$ 通过 (13.7)–(13.8)同时更新二者。仍可能有多个隐藏配置属于 $B$，所以这只给任务读出的联合恢复，不给原始世界的逆映射。若未来任务还包含新的隐藏读数，就需重新检查相应的同步条件。

### 13.6 三个有限模型揭示不同恢复层次

**例 13.3（空间可恢复而时钟不可恢复）。** 取 $X_0=X=\{u,v\}$，两个配置都位于同一个接口，唯一动作在两点均自环并输出同一个符号，但费用分别为 $1,2$。同步顶点 $(u,v)$ 有费用差 $-1$ 的自环，一步即出现时钟歧义。接口已知不代表时钟已知。

**例 13.4（时钟可恢复而空间不可恢复）。** 保留两点自环和同一输出，把两点费用都设为 $1$，端口分别设为 $i_0,i_1$。每条同步边费用差为零，故长度为 $k$ 的档案确定时钟 $k$；当前端口仍有两个候选，空间恢复失败。

**例 13.5（一步核对不足，且指定终止协议恢复弱于逐前缀恢复）。** 取 $X=\{u,v,t,p,q,z\}$、$X_0=\{u,v\}$。动作 $a$ 在 $u,v$ 均自环且费用为零；动作 $b$ 分别将 $u$ 送到 $u$、将 $v$ 送到 $t$，费用均为零；动作 $c$ 将 $u$ 送到 $p$、将 $t$ 送到 $q$，费用分别为 $1,2$；终止动作 $f$ 将 $p,q$ 都送到 $z$，费用分别为 $2,1$。这些是全部合法边，每条边输出同一符号。动作 $c$ 在 $v$ 非法，所以初始时两条同档案执行不能共同使用它。长度一的全部同档案执行都具有相同时钟，而档案 $bc$ 产生 $1,2$ 两种时钟。指定终止协议 $bcf$ 的两个分支总费用都为 $3$；这仍不能修复中间前缀 $bc$ 的歧义。

另一个单点模型足以说明记忆成本：唯一动作自环、输出固定、费用为一。定理13.1成立，但精确报告任意长度的累计时钟需要区分所有 $0,1,2,\ldots$。若完整可访问记忆只有有限状态，且不另给当前步数或外部档案，就不可能全部保存。有限图的精确恢复器不自动是固定容量的计数器。

### 13.7 与既有形式化结果的接口及适用边界

仓内 D5/S3/ObserverMemory/PredictionCertificates/ClockTimeVersusRefinementDepth.lean 的 clock_time_does_not_determine_refinement_depth 给出一状态与四状态系统中的时钟—预测深度分离。本节沿用这种分型；定理13.2的界是同一有限模型上时钟歧义证人的长度界，不能改报成预测完成深度。

过程卷第9节已经处理路径加法、势差与闭路。本节不重复取得这些结果的新内容名义，而是把实际同档案的状态对、逐前缀恢复和有限诊断界接在一起。若限制为某个固定有限控制器允许的档案，应先将该控制器状态与 $X$ 联合再用上述构造；若控制器需要无界记忆，本节没有给一个只依赖原始 $n$ 的诊断界。随机转移、连续时间、近似时钟和未知模型的统计取得均不在定理13.1–13.2中。Claim status: open；没有新增 Lean 声明。

## 13.99 追加锚

## 14. 实际制备的时钟边界：局部最小性与共同来源的精确粘合

固定同一个可逆来源、模时钟和实际制备后，各个局部边界都能精确保存自己的当前读数与时钟，却仍可能在空间相容、时钟相等的粘合中引入来源没有经历过的状态。本节把这个差额归结为制备相位集合的交，并辨认差额所属的完整运输轨道。以下为 repo-derived synthesis，Claim status: open；陈述与证明是普通数学，不主张新增 Lean 结果或文献原创性。

### 14.1 可逆来源及制备相位

**定义 14.10（固定制备的模时钟来源）。** 取有限群胚 $\mathcal G$，对象集为 $X$，取 $C=\mathbb Z/m\mathbb Z$，$m\ge1$。每条箭头 $e:x\to y$ 有指定费用 $c(e)\in C$，满足

$$
c(f\circ e)=c(e)+c(f),\qquad c(e^{-1})=-c(e),
\qquad (x,t)\xrightarrow{e}(y,t+c(e)).
\tag{14.40}
$$

恒等箭头费用由加法消去律等于零。群胚中的箭头及逆箭头均允许执行，合法性与费用不依赖额外隐藏历史。实际制备是固定非空 $P\subseteq X$，每个 $p\in P$ 都从时钟零出发。记 $R_P\subseteq X\times C$ 为 $P\times\{0\}$ 经有限合法运输得到的实际集合；$R_P(x)=\{t:(x,t)\in R_P\}$。所保留的联合任务是完整当前对象及其指定模时钟 $(x,t)$ 和这些量的未来运输，不要求反演初始制备点或整份过去档案。比较切分时，$\mathcal G,c,P$ 与初始钟值固定。

先作后续粘合所需的标准归一化。在与 $P$ 相交的连通分支 $O$ 上，选根 $o$ 及箭头 $r_x:o\to x$，令 $r_o=\mathrm{id}$、$\kappa_x=c(r_x)$，并记

$$
H_O=\{c(\ell):\ell:o\to o\}\le C,
\qquad
U_O(P)=\bigcup_{p\in P\cap O}(-\kappa_p+H_O).
\tag{14.41}
$$

$H_O$ 是子群：恒等、复合及逆箭头分别给零、加法及加法逆元。通过 $r_x$ 共轭闭路不改变它在交换群 $C$ 中的费用像。对任意 $e:p\to x$，根闭路 $r_x^{-1}\circ e\circ r_p$ 的费用为 $\kappa_p+c(e)-\kappa_x$，故 $c(e)\in\kappa_x-\kappa_p+H_O$。反过来，对实现 $h\in H_O$ 的根闭路 $\ell$，箭头 $r_x\circ\ell\circ r_p^{-1}$ 实现费用 $\kappa_x-\kappa_p+h$。因此精确的实际纤维及其计数是

$$
R_P(x)=\kappa_x+U_O(P),\qquad
|R_P\cap(O\times C)|=|O|\,|U_O(P)|.
\tag{14.42}
$$

这是闭路运输与实际轨道的已有机制在加法时钟上的使用。运输记忆卷 [TransportMemoryCompletion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) §1.7 已给生成树归一化，§2.1–2.3 已区分实际初态轨道与任务商。图论背景中，Jenča，*Voltage lifts of graphs from a category theory viewpoint*，[arXiv:2008.12055v3](https://arxiv.org/abs/2008.12055v3)，Definition 2.7 的提升将群坐标沿边乘上电压，Proposition 2.9 给其典范投影为覆盖；此处交换钟群改用加法记号。Jonoska–Krajčevski–McColm，*Lifting Voltages in Graph Covers*，[arXiv:2501.17135v1](https://arxiv.org/abs/2501.17135v1)，Proposition 4.10 对连通电压图及其电压值生成的群作提升，将每个分支同构于生成树归一化后电压子群上的提升。这里只借用提升及闭路分支机制；这些结果没有给出下文的观察器资源下界或两个局部制备像的粘合判据。

式(14.42)保留所有实际制备给出的陪集并，不取它生成的子群。若有 $r_O$ 个不同的 $-\kappa_p+H_O$，则每个当前对象上的时钟纤维大小为 $r_O|H_O|$。更换参考箭头只改变表达中的代表，不改变实际纤维。没有实际制备的连通分支不属于 $R_P$。

作为这一计算的恢复含义，在每个实际分支上有

$$
\begin{aligned}
&t\text{ 可由完整当前对象 }x\text{ 唯一恢复}\\
&\quad\Longleftrightarrow |U_O(P)|=1\\
&\quad\Longleftrightarrow H_O=\{0\}\text{ 且所有 }p\in P\cap O\text{ 的 }\kappa_p\text{ 相等}.
\end{aligned}
\tag{14.43}
$$

第一步是每个非空纤维必须为单点。第二步用每个相位陪集都含 $|H_O|$ 个元素；当 $H_O=\{0\}$ 时，各单点相等恰是制备势对齐。不同连通分支可分别选势常数，因为当前对象已辨认分支。仓内 `D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.lean` 的 `closed_path_zero_iff_exists_potential` 要求连通群胚、`AddCommGroup`、复合费用相加及逆箭头费用取负，结论是所有闭路费用为零当且仅当存在势 $V$ 使 $c(e)=V(y)-V(x)$。在这里逐分支使用它；它不保证所有零钟制备点的势相等，也不承担局部像粘合。非零闭路费用或未对齐的实际制备能使完整当前对象仍有多种钟值，进一步压缩当前对象无法恢复被它遗漏的区别。

### 14.2 等变切分与完整状态资源合同

**定义 14.11（公开标记的群运输和空间切分）。** 以下专取任意有限群 $G$、子群 $K\le G$、左陪集空间 $X=G/K$ 及同态 $c:G\to C$。不假设 $G$ 交换或 $K$ 正规。每个公开动作标记 $h\in G$ 同时指定运输及其费用：

$$
h\cdot(gK,t)=(hgK,t+c(h)).
\tag{14.44}
$$

也可只将一组生成元及其逆作为一步公开标记，任意有限词仍实现全部 $G$。群乘法按左作用解释：先 $h_1$ 后 $h_2$ 的总作用是 $h_2h_1$。不同标记即使诱导相同的物理位置映射，也不能合并其费用；时钟必须按实际公开标记更新。制备是非空 $P\subseteq G/K$，每点钟值零。对 $K\le L\le G$，指定局部当前读数为 $p_L(gK)=gL$。其实际当前与时钟像记为 $B_L=\{(gL,t):(gK,t)\in R_P\}$。

**定义 14.12（封闭确定性状态计数）。** 一个局部观察器的完整持久状态集为 $W_L$。初始化仅取得实际局部初始读数 $g_pL$ 及已知初始钟值零；此后输入仅为当前公开动作标记。要求有确定性映射

$$
\begin{gathered}
\mathrm{Init}_L:p_L(P)\times\{0\}\longrightarrow W_L,\\
\mathrm{Update}_L:W_L\times G\longrightarrow W_L,\\
\mathrm{Decode}_L:W_L\longrightarrow G/L\times C,
\end{gathered}
\tag{14.45}
$$

使每条从 $P\times\{0\}$ 出发的执行及其每个前缀都由所计状态单独解出 $(p_L(x),t)$。只公开生成元时，将更新的第二因子换为该标记集。以下 $|W_L^{\mathrm{reach}}|$ 只计实际可达状态；无用的未达状态可以去掉。

解码与后续更新没有免费重读的当前值传感器、源状态、时钟、档案、控制器相位或历史索引。所有反复参与更新或解码的信息都属于所计持久状态。状态可以依赖历史，不预设它只是实际对的函数。模型、动作表及解码规则是固定的；任何随执行变化而影响答案的信息不能藏在这些固定规则之外。联合观察器采用同一合同，把指定读数改为完整 $gK$。

对于有 $N\ge1$ 个实际可区分状态的有限边界，原始状态数、对数容量与定长二进制位宽分别为

$$
N,\qquad \log_2N,\qquad \lceil\log_2N\rceil.
\tag{14.46}
$$

后二者一般不同。这里计的是承担指定任务的完整持久状态，不是允许免费访问来源的辅助工作空间，也不是仅要求一个联合解码器能读钟时的最小分布式总存储。两个局部观察器各自都必须解出自己的指定当前值和完整钟值。

### 14.3 同一实际来源的局部边界与精确粘合

**定理 14.13（制备敏感的局部最小边界及其粘合）。** 在定义14.11–14.12的同一模型下，为每个 $p\in P$ 选代表 $g_p$，对每个 $K\le L\le G$ 令

$$
U_L(P)=\bigcup_{p\in P}\bigl(-c(g_p)+c(L)\bigr).
\tag{14.47}
$$

这些集合不依赖制备代表的选择。实际联合边界等于 $B_K$，各局部实际像及其最小状态数为

$$
\begin{gathered}
B_L=\{(gL,t):t-c(g)\in U_L(P)\},\\
N_L=|B_L|=|G:L|\,|U_L(P)|,\\
R_P=B_K,\qquad N_{\mathrm{joint}}=|G:K|\,|U_K(P)|.
\end{gathered}
\tag{14.48}
$$

每个 $N_L$ 都是在上述封闭合同下的精确最小值；同一来源的投影同时达到这些局部最小值，并与存储实际联合对达到的联合最小值相容。局部当前值单独恢复钟值当且仅当 $|U_L(P)|=1$，亦即 $c(L)=\{0\}$ 且全部 $c(g_p)$ 相等。

再取两个子群 $K_A,K_B$，满足 $K_A\cap K_B=K$。定义实际物理相容关系

$$
Q=\{(gK_A,gK_B):g\in G\}
\subseteq G/K_A\times G/K_B.
\tag{14.49}
$$

映射 $gK\mapsto(gK_A,gK_B)$ 双射到 $Q$；不要求 $Q$ 等于整个乘积。局部边界的粘合仅保留 $Q$ 中的当前值对，并要求两边钟值相等。经此双射将粘合视为 $G/K\times C$ 的子集，则

$$
F_P=\{(gK,t):t-c(g)\in U_{K_A}(P)\cap U_{K_B}(P)\}.
\tag{14.50}
$$

实际来源始终包含于该粘合，且

$$
\begin{gathered}
|F_P|=|G:K|\,|U_{K_A}(P)\cap U_{K_B}(P)|,\\
R_P\subseteq F_P,\qquad
F_P=R_P\ \Longleftrightarrow\\
U_{K_A}(P)\cap U_{K_B}(P)=U_K(P),\\
|F_P\setminus R_P|=|G:K|\bigl(|U_{K_A}(P)\cap U_{K_B}(P)|-|U_K(P)|\bigr).
\end{gathered}
\tag{14.51}
$$

证明。先求实际像。换代表 $g_p$ 为 $g_pk$，$k\in K$，只会把 $-c(g_p)+c(L)$ 平移 $-c(k)\in c(L)$，不改该陪集。类似地，换当前代表 $g$ 为 $g\ell$，$\ell\in L$，不改变式(14.48)的成员条件，因为 $U_L(P)$ 是 $c(L)$ 的陪集并。

从制备 $g_pK$ 执行总运输 $h$，局部终点为 $gL$ 当且仅当 $hg_pL=gL$。这是左陪集相等，等价于存在 $\ell\in L$ 满足

$$
h=g\ell g_p^{-1},\qquad
c(h)=c(g)-c(g_p)+c(\ell).
\tag{14.52}
$$

反过来，每个这样的 $\ell$ 确实给一条可执行的总运输，且初始钟值零使终钟恰为 $c(h)$。取所有实际 $p$ 与 $\ell$ 就得到 $B_L$ 的两个包含方向；取 $L=K$ 得到联合来源。每个固定 $gL$ 的实际钟值是平移集合 $c(g)+U_L(P)$，恰有 $|U_L(P)|$ 个元素，故得到计数式。整个推导只使用 $c$ 的同态性，不交换 $G$ 中任何因子，也不用 $L$ 正规。

其次，局部对有封闭更新及局部初始化：

$$
\begin{gathered}
\mathrm{Init}_L(g_pL,0)=(g_pL,0),\\
\mathrm{Update}_L((gL,t),h)=(hgL,t+c(h)),\\
\mathrm{Decode}_L(gL,t)=(gL,t).
\end{gathered}
\tag{14.53}
$$

左乘在左陪集上良定义，且更新后 $(t+c(h))-c(hg)=t-c(g)$，故仍在 $B_L$。初始化只用被允许的局部输入；所有前缀都精确保存所需对。任一其他精确观察器的状态解码像必须包含每个实际局部对：每一对都有一条实际执行，而两个不同的对不能由同一状态解出。因此 $\mathrm{Decode}_L$ 从其实际可达状态满射到 $B_L$，得到 $|W_L^{\mathrm{reach}}|\ge|B_L|$；保存该对达到等号。联合情形相同。这正是运输记忆卷 §2.1–2.3、§2.7 的未来任务商最小性在“即时读出已区分整个任务对”时的使用；该卷逐已知顶点计分支记忆，本定理则将当前陪集也纳入状态单独解码的任务，不能把外部顶点知识当作免费内部存储。

所有局部状态都取自同一个 $R_P$ 的投影，且这些投影与每个公开动作的更新交换，故上述最小值能在同一执行上同时达到。对于这里的两切分，实际局部状态向量还唯一恢复联合对；其实际像有 $|R_P|$ 个元素。这个事实不把两个局部状态集的自由乘积当作实际集合，也不宣称放松局部解码任务后相同的总位宽仍最优。局部当前读数恢复钟值的判据由每个非空纤维的大小得到；陪集并为单点的条件与式(14.43)相同。

最后，$P$ 非空且全部群运输可执行，故每个 $gK$ 都是实际可达的当前位置。若 $gK_A=g'K_A$ 且 $gK_B=g'K_B$，则 $g^{-1}g'\in K_A\cap K_B=K$，所以 $gK=g'K$。满射到 $Q$ 则由定义成立。对一个相容当前值对，选其共同 $gK$ 后，两个局部边界都允许钟值 $t$ 恰好要求 $t-c(g)$ 同时属于两个局部相位集合，得到式(14.50)。$c(K)\subseteq c(K_A),c(K_B)$ 给 $U_K(P)\subseteq U_{K_A}(P)\cap U_{K_B}(P)$。若相位集合相等，两个来源表达式立即相等。若反向包含失败，选 $d\in(U_{K_A}(P)\cap U_{K_B}(P))\setminus U_K(P)$，则 $(K,d)$ 在 $F_P$ 而不在 $R_P$；因此来源相等也强制相位集合相等。每个 $gK$ 上分别平移这两个集合，差集大小恒定，乘以 $|G:K|$ 得最后的计数。证毕。

这条判据始终使用同一实际 $P$。两侧局部可达所用的制备点及运输可以不同；要求存在一个共同实际执行，正是交集中可能缺失的额外关系。对单制备 $P=\{K\}$，$U_L=c(L)$，判据化为 $c(K_A\cap K_B)=c(K_A)\cap c(K_B)$。同时，$B_L$ 是 $(L,0)$ 的轨道，其稳定子为 $L\cap\ker c$；标准轨道—稳定子对应给 $B_L\cong G/(L\cap\ker c)$，映射为 $h(L\cap\ker c)\mapsto(hL,c(h))$。这是定理中的局部计数的陪集表达，仍是 $G$-集合而非自动成为商群。

### 14.4 错误粘合增加哪些运输扇区

**命题 14.14（单制备的相位缺陷及其轨道）。** 在定理14.13下先取 $P=\{K\}$，简记 $R=R_P,F=F_P$，并令

$$
H=c(K),\qquad I=c(K_A)\cap c(K_B),\qquad D=I/H,
\qquad \delta(gK,t)=t-c(g)+H.
\tag{14.54}
$$

$D$ 是有限交换群，$\delta:F\to D$ 是满射且在提升的 $G$ 作用下不变，零纤维恰为实际单制备来源 $R$。每个纤维都是一个 $G$ 轨道。

证明。这里 $U_L=c(L)$，故 $H\le I\le C$。换当前代表 $g\mapsto gk$ 只减去 $c(k)\in H$，所以 $\delta$ 良定义。每个 $d\in I$ 给 $(K,d)\in F$，其像为 $d+H$，故满射。更新后相位差不变，且 $\delta=0$ 恰为 $t-c(g)\in H$，即实际来源条件。

对扇区 $d+H$ 选代表 $(K,d)$。若 $(gK,t)$ 属于该扇区，则 $t-c(g)-d\in H$；选 $k\in K$ 实现 $c(k)=t-c(g)-d$，运输 $gk$ 即把 $(K,d)$ 送到 $(gK,t)$。在 $(K,d)$ 处，稳定子恰为 $M=K\cap\ker c$，因为同时固定陪集和钟值等价于这两个条件。于是标准轨道—稳定子对应具体给出

$$
G/M\longrightarrow\delta^{-1}(d+H),\qquad
hM\longmapsto(hK,d+c(h)),
\tag{14.55}
$$

为 $G$-集合的同构。若另一点写为 $h\cdot(K,d)$，它的稳定子为 $hMh^{-1}$，不将根处的稳定子字面套给所有点。因而

$$
|\delta^{-1}(d+H)|=|G:(K\cap\ker c)|=|R|,
\qquad |F|=|D|\,|R|.
\tag{14.56}
$$

错误粘合恰增加 $|D|-1$ 个完整运输扇区；并非只有若干孤立的错误钟值。轨道—稳定子工具及陪集作用的角色沿用运输记忆卷 §2.2，不另立一般轨道分类结论。证毕。

一般 $G$ 下，上述 $G/M$ 是陪集作用集合，$F,R$ 不自动是群。若进一步假设 $G$ 交换，则 $G/K$ 为群，$F$ 是 $(G/K)\times C$ 的子群，$R$ 是同态 $g\mapsto(gK,c(g))$ 的像，$\delta$ 也为同态。此时才在本节断言短正合列

$$
0\longrightarrow R\longrightarrow F\xrightarrow{\delta}D\longrightarrow0.
\tag{14.57}
$$

确实，$F$ 的成员条件在加法及取负下保持，核条件是 $t-c(g)\in H$，满射已证。这只是交换 $G$ 下的充分适用范围，不声称交换性在所有其他构造中必要，也不声称该列分裂。

对一般非空制备，仍可用 $H=c(K)$，把提升的整个 $G/K\times C$ 按 $t-c(g)+H\in C/H$ 分扇区。每个扇区仍是式(14.55)所描述的一个轨道，但实际选中的扇区与粘合选中的扇区分别只是集合

$$
S_P=\{u+H:u\in U_K(P)\},\qquad
T_P=\{u+H:u\in U_{K_A}(P)\cap U_{K_B}(P)\}.
\tag{14.58}
$$

$S_P\subseteq T_P$，精确粘合等价于 $S_P=T_P$。每个错误扇区有 $|G:(K\cap\ker c)|$ 个状态，故其数目也给出式(14.51)的差额。这里 $S_P,T_P$ 不必是子群，不把它们补成子群，不由它们写群正合列。

### 14.5 同一模四来源上的两种空间切分

**命题 14.15（非零闭路相位保留下的切分改进）。** 固定

$$
G=(\mathbb Z/4\mathbb Z)^2,\quad c(r,s)=r+s\pmod4,\quad
K=\{(r,s):r,s\text{ 均为偶数}\},\quad
X=G/K\cong(\mathbb Z/2\mathbb Z)^2.
\tag{14.59}
$$

写当前位置为 $(u,v)$，实际制备仅为 $P=\{(0,0)\}$，初钟零。一步公开动作是 $e_1^{\varepsilon}=(\varepsilon,0)$ 或 $e_2^{\varepsilon}=(0,\varepsilon)$，$\varepsilon\in\{1,-1\}$，费用均为 $\varepsilon\pmod4$。比较期间固定这些来源、制备、钟、动作及完整联合任务 $(u,v,t)$。

实际闭路费用像为 $c(K)=\{0,2\}$，联合来源为

$$
R=\{(u,v,t):t\bmod2=u+v\bmod2\},\qquad |R|=8.
\tag{14.60}
$$

第一种切分读 $u$ 与 $v$；局部完整边界各有八态，而等钟粘合有十六态。第二种切分读 $w=u+v\pmod2$ 与 $v$；局部完整边界分别四态、八态，等钟粘合恰为原来的八态联合来源。联合最小状态数在两种切分中都为八；两个独立局部解码器的最小定长位宽之和从六变为五。

证明。$K$ 的费用为零或二，并且二由 $(2,0)$ 实现；所以闭路相位非零。式(14.48)给固定 $(u,v)$ 上恰有两个同奇偶钟值，得到式(14.60)。也可直接选 $r=u+2a,s=v+2b$，$a,b\in\{0,1\}$，其和遍历恰好这两个钟值。

第一种切分对应 $K_A=\{(r,s):r\text{ 偶}\}$、$K_B=\{(r,s):s\text{ 偶}\}$，交为 $K$，而两者费用像都是 $C$。于是 $B_A=\{0,1\}\times C$、$B_B=\{0,1\}\times C$ 各八态。对公开标记 $e_i^{\varepsilon}$，局部更新为

$$
\begin{aligned}
(u,t)&\longmapsto(u+\mathbf1_{\{i=1\}}\bmod2,\ t+\varepsilon\bmod4),\\
(v,t)&\longmapsto(v+\mathbf1_{\{i=2\}}\bmod2,\ t+\varepsilon\bmod4).
\end{aligned}
\tag{14.61}
$$

初始化均为 $(0,0)$，解码就是保存的对。$+e_i$ 与 $-e_i$ 在当前物理位上都翻转同一位，却分别给模四增量 $1,3$；抹去动作标记中的符号会破坏这个时钟更新。

四个 $(u,v)$ 全部物理相容，但每个等钟局部组合都通过，故粘合是十六个三元组。伪状态 $(0,0,1)$ 的 $A$ 局部对 $(0,1)$ 可由实际状态 $(0,1,1)$ 见证，来自执行 $+e_2$；它的 $B$ 局部对 $(0,1)$ 可由实际状态 $(1,0,1)$ 见证，来自执行 $+e_1$。这两个局部证人各自有效，却没有共同实际三元组 $(0,0,1)$。

第二种切分取 $K_{A'}=\{(r,s):r+s\text{ 偶}\}$，仍用 $K_B$。其交为 $K$，且 $c(K_{A'})=\{0,2\}$、$c(K_B)=C$。在同一个 $R$ 上，$w=t\bmod2$，故

$$
B_{A'}=\{(t\bmod2,t):t\in C\},\qquad
q_{A'}=t,\quad
\mathrm{Update}_{A'}(q_{A'},e_i^{\varepsilon})=q_{A'}+\varepsilon,
\quad
\mathrm{Decode}_{A'}(q)=(q\bmod2,q).
\tag{14.62}
$$

四态编码从零初始化；它不需要初始化之后重新读取 $w$。若直接存局部对，则更新为 $(w,t)\mapsto(w+1\bmod2,t+\varepsilon\bmod4)$，与上述编码一致。$B$ 仍用式(14.61)。两局部值通过 $u=w+v\pmod2$ 恢复原来的完整位置；时钟相等时 $w=t\bmod2$ 又恰好强制式(14.60)，所以粘合精确。

第一种切分的缺陷及运输扇区可写成

$$
D\cong\mathbb Z/2\mathbb Z,\qquad
\delta(u,v,t)=t-u-v\pmod2.
\tag{14.63}
$$

$\delta=0$ 是原来的八态实际来源，$\delta=1$ 是错误增加的整个八态轨道。第一种切分的正合列各群阶为 $8,16,2$；第二种切分的缺陷群平凡。

| 固定模四单制备的切分 | 局部原始状态数 | 联合最小状态数 | 空间相容且等钟的粘合数 | 两局部定长位宽之和 |
| --- | --- | --- | --- | --- |
| 14.15中的第一切分：$u/v$ | $8/8$ | $8$ | $16$ | $3+3=6$ |
| 14.15中的第二切分：$(u+v)/v$ | $4/8$ | $8$ | $8$ | $2+3=5$ |

本例各计数都是二的幂，对数容量与取整位宽恰相等；联合边界在两行都是三位。改变的是 $A$ 的指定局部当前读数，由 $u$ 变为 $u+v$；完整联合任务及当前来源并未改变。式(14.62)使用实际相位关系保存新任务，不能解释为从原始 $u$ 单独恢复 $u+v$。非零闭路相位 $\{0,2\}$ 始终保留：即使完整 $(u,v)$ 或新的 $w$ 已知，仍须区分两个模四钟值。当前切分没有消除这一个二态的闭路区别。证毕。

**命题 14.16（单独的模二比较）。** 另取 $G=(\mathbb Z/2\mathbb Z)^2$、$K=\{0\}$、$C=\mathbb Z/2\mathbb Z$、$c(u,v)=u+v$ 及单零制备。此时实际来源为 $t=u+v$ 的四态图像。$u/v$ 切分的局部对各四态，$(u+v)/v$ 切分的局部对分别二态、四态；前者任一当前位不能独自读钟，后者 $A'$ 当前值就是整个钟。

证明。对固定 $u$，变 $v$ 可使 $t$ 取两值；对固定 $v$ 同理。新读数 $w=u+v=t$，所以 $(w,t)$ 只有两值，而 $(v,t)$ 仍有四值。每次单坐标翻转使 $t$ 翻转，故存这些对都有定义14.12的封闭更新；定理14.13给其最小性。这是另一指定钟群与来源，不把它当作命题14.15比较中途更换钟任务。证毕。

### 14.6 制备改变与相位集合不能省略

**命题 14.17（同一旧切分的边缘可掩盖不同制备）。** 保留命题14.15的群、钟及动作，将制备改为 $P^+=\{(0,0),(1,0)\}$，两点仍从钟值零出发。这是一个不同的实际制备。此时

$$
U_K(P^+)=\{0,2\}\cup\{1,3\}=C,
\qquad R_{P^+}=X\times C,\qquad |R_{P^+}|=16.
\tag{14.64}
$$

第一种 $u/v$ 切分的局部像保持八态／八态；第二种 $(u+v)/v$ 切分的局部像变为八态／八态，其中 $A'$ 从四态增加到八态。因此“局部边缘不变而联合来源改变”只指第一种切分，不能套给第二种切分。

证明。新增制备代表 $(1,0)$ 的费用为一，故其相位陪集为 $-1+c(K)=\{1,3\}$，与原陪集并成 $C$。旧 $K_A,K_B$ 的费用像原已为 $C$，增加制备不会扩大这两个八态像。新 $K_{A'}$ 的费用像为 $\{0,2\}$，新增制备则把它的相位并也扩为 $C$，故 $|B_{A'}|=2\cdot4=8$；$B_B$ 仍八态。尤其初态 $(1,0,0)$ 的 $w=1$ 而 $t=0$，直接否定单制备时的 $w=t\bmod2$；这时须保留 $(w,t)$ 的全部八种区别；保存该对仍可用 $(w,t)\mapsto(w+1,t+\varepsilon)$ 更新。两种切分的粘合此时都为十六态，联合最小位宽为四，两个局部定长位宽之和均为六。命题14.15的六到五比较始终只在原单制备上成立。证毕。

**命题 14.18（单制备子群判据不能替代任意制备判据）。** 取加法群 $G=C=\mathbb Z/6\mathbb Z$、$c=\mathrm{id}$、$K=\{0\}$，以及

$$
K_A=\{0,3\},\qquad K_B=\{0,2,4\},\qquad
c(K_A)\cap c(K_B)=c(K)=\{0\}.
\tag{14.65}
$$

单制备 $P=\{0\}$ 时，实际联合来源、两个局部像与粘合各有六态，粘合精确。但取 $P=\{0,5\}$，仍让每个制备的钟值为零，则

$$
\begin{gathered}
U_K(P)=\{0,1\},\qquad U_{K_A}(P)=\{0,1,3,4\},
\qquad U_{K_B}(P)=\mathbb Z/6\mathbb Z,\\
|R_P|=12,\qquad |B_{K_A}|=|B_{K_B}|=12,
\qquad |F_P|=24.
\end{gathered}
\tag{14.66}
$$

证明。执行 $h$ 从制备 $p$ 得到 $x=p+h,t=h$，故 $t-x=-p$。单制备只允许差零；两制备允许差 $0,-5=1$，每个 $x$ 恰有两钟值。对 $K_A$，这两个差分别加上 $\{0,3\}$ 得 $\{0,1,3,4\}$；对 $K_B$，偶数陪集与奇数陪集并成全钟群。三个 $G/K_A$ 当前值各有四种钟值，两个 $G/K_B$ 当前值各有六种钟值，得局部各十二态。两切分的交为零，空间上六个位置都由局部对唯一恢复，而等钟条件还允许每个位置四个差，故二十四态。

例如 $(x,t)=(0,3)$ 不属于实际两制备来源。它的 $A$ 局部对可由实际 $(3,3)$ 见证，来自制备零；它的 $B$ 局部对可由实际 $(2,3)$ 见证，来自制备五。两侧恰使用不同实际制备，仍不能给共同的 $(0,3)$。式(14.65)始终成立，却没有排除这个伪状态；必须使用式(14.51)的制备相位集合等式。证毕。

### 14.7 非正规切分及实际空间相容域

**命题 14.19（$S_3$ 中只有六个空间相容对）。** 取 $G=S_3$，$C=\mathbb Z/2\mathbb Z$，$c(g)$ 为置换奇偶性，$K=\{e\}$，单制备 $P=\{e\}$。令 $a=(12),b=(23)$，取 $K_A=\{e,a\}$、$K_B=\{e,b\}$。它们均非正规，交为 $K$。两个三点陪集空间的九个形式当前值对中恰有六个物理相容对，且

$$
|R|=6,\quad |B_{K_A}|=|B_{K_B}|=6,\quad
F=S_3\times\mathbb Z/2\mathbb Z,\quad |F|=12.
\tag{14.67}
$$

证明。$bab^{-1}=(13)\notin K_A$，$aba^{-1}=(13)\notin K_B$，故两子群非正规；两个不同二阶子群只交于单位。由定理14.13的单射，六个 $g$ 给六个不同相容对，而全乘积有 $3\cdot3=9$ 个。两子群的奇偶费用像均为 $C$，故各局部边界有 $3\cdot2=6$ 态，每个相容位置又容许两个等钟值，粘合十二态。实际来源只是 $(g,c(g))$ 的六态图像。

相位 $\delta(g,t)=t-c(g)\pmod2$ 给两个六态轨道；根处稳定子 $K\cap\ker c=\{e\}$，所以每个都是正则 $S_3$ 作用集合。对 $L\in\{K_A,K_B\}$，局部更新是 $(gL,t)\mapsto(hgL,t+c(h))$，不需要正规性。若省掉物理相容关系，仅在九个局部当前值对上匹配钟值，会得到十八个形式组合，其中六个连共同当前位置都没有；定理的十二态粘合已经先排除了这些组合。证毕。

### 14.8 静态恢复不授予动态下降

**命题 14.20（制备势歧义与静态切分的两个界限）。** 一般群胚中，零闭路费用不保证多零钟制备下的当前对象恢复时钟；即使时钟能由一个静态切分恢复，该切分与时钟的对也不必有局部确定性更新。

证明。第一项取对象 $0,1$ 的二点对群胚，每对对象间只有一条箭头，费用 $c(p\to x)=x-p\pmod3$。复合费用相加，所有闭路费用零，势为 $V(x)=x$。若两个对象都作为零钟制备，实际集合为

$$
R_{\{0,1\}}=\{(0,0),(0,2),(1,0),(1,1)\},
\qquad U=\{0,2\}\subset\mathbb Z/3\mathbb Z.
\tag{14.68}
$$

两个对象上各有两钟值；$U$ 不是子群，因为 $2+2=1\notin U$。把它替换成生成子群会把四态实际集合错误扩为六态。

第二项取三点 $X=\mathbb Z/3\mathbb Z$ 的可逆旋转作用，全部动作费用零，制备仅为零。三个当前位置都可达，时钟恒零。静态切分 $p(0)=p(1)=0,p(2)=1$ 已能恢复时钟。然而公开的正旋转把同一局部对 $(p(0),0)=(p(1),0)=(0,0)$ 分别送到 $(p(1),0)=(0,0)$ 与 $(p(2),0)=(1,0)$。因此不存在仅凭该对及同一旋转标记决定后继的函数。定理14.13依靠陪集切分的等变性取得动态闭合，不能省去这一前提。证毕。

一般静态 $p:X\to Y$ 的精确读钟条件，是对每个实际 $y$，集合 $\bigcup_{x\in p^{-1}(y)}R_P(x)$ 为单点；未达 $x$ 的纤维为空。这是观察纤维上的唯一性条件。它既不提供合法性下降，也不提供 $p(x)$ 的后继下降，命题14.20的第二部分甚至在所有动作处处合法时就使后者失败。

### 14.9 来源关系及陈述范围

**注记 14.21（所连接的既有工具与任务边界）。** 本节的关系链从同一制备出发：闭路归一化给实际相位陪集并；等变切分给这些实际像的封闭局部运输；完整状态解码使像的大小成为所声明任务的最小状态数；空间相容且等钟的粘合再以相位集合的交检验共同来源。TransportMemoryCompletion §1.7、§2.1–2.3、§2.7 分别承担归一化、实际轨道、未来任务商、陪集最小性及相位记忆的既有工具。本节增加的是这些工具在固定模时钟、指定局部解码任务与共同制备上的连接及错误粘合扇区，不另行声称一般最小化或 holonomy 理论。

[ProcessGeometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) §9 的路径加法及势差区分，在这里对应式(14.40)与式(14.43)；§29 的联合标签律与实际时钟恢复区分，要求继续把共同来源关系与边缘像分开。本卷 §13 保留完整可见档案来研究逐前缀路径钟恢复；这里给定公开动作费用，以有限模钟状态保存当前任务，没有将完整档案恢复等同于当前对象读钟。`D5/S3/ObserverMemory/PredictionCertificates/ClockTimeVersusRefinementDepth.lean` 的 `clock_time_does_not_determine_refinement_depth` 具体给出一状态系统在任意钟步下完成深度为零，以及一个满足 $\tau(\mathrm{zero})=\mathrm{one}$ 且 $\mathrm{completionDepth}(\tau,q)\ge2$ 的四状态系统；它支持钟步与预测完成深度的分型，不给本节状态数或运输扇区的公式。

所有计数依赖有限且已指定的群、钟及实际制备，所有局部最小值依赖定义14.12的完整状态访问合同。一般静态切分须另证动作及合法性下降；多制备须保留实际相位集合，不能改用其子群闭包。所用模钟允许逆动作的负增量，不是严格递增的实时间或热力学量。未指定钟校准的记忆、双线性恢复、自由作用的闭包约减以及其他边界扩张不属于这些陈述。Claim status: open；普通证明不改变既有形式化结果的范围。

## 14.99 追加锚

## 15. 任意有限校准的补偿图：删钟记忆与原相位恢复

### 15.1 同一来源上的三种状态解码任务

**定义 15.10（单零制备与实际校准像）。** 设 $A,B$ 为有限交换群，$C=\mathbb Z/m\mathbb Z$，$m\ge1$，$H\le C$ 为实际原钟群，$f:A\times B\to C$ 为固定已知函数。取

$$
S=A\times B\times H,\qquad z_0=(0,0,0),\qquad
\ell(a,b,h)=h+f(a,b),\qquad n_S=|A||B||H|.
\tag{15.30}
$$

制备是双方已知的单点 $z_0$。一步公开标记 $u=(s,t,k)\in S$ 对应处处合法的平移 $\tau_u(z)=z+u$，同一标记同时输入两端。也允许只取一个生成全部 $S$ 的标记集 $U$ 及其逆；所有有限词均允许执行。以下 $U=S$ 或这样的生成集均可，空词也算历史。任意 $z\in S$ 都从 $z_0$ 可达。空间坐标 $a,b$ 属于来源状态；外部类型顶点只有一个固定值，不随 $a,b,h$ 改变。

校准后的实际坐标域及其逆为

$$
\begin{gathered}
\Omega_f=\{(a,b,\lambda)\in A\times B\times C:
                    \lambda-f(a,b)\in H\},\\
F_f:S\longrightarrow\Omega_f,\quad
F_f(a,b,h)=(a,b,h+f(a,b)),\qquad
F_f^{-1}(a,b,\lambda)=(a,b,\lambda-f(a,b)).
\end{gathered}
\tag{15.31}
$$

因此 $|\Omega_f|=n_S$，只有 $H=C$ 时它才是整个 $A\times B\times C$。在此域上的运输是

$$
\widetilde\tau_u(a,b,\lambda)=
\bigl(a+s,b+t,\lambda+k+f(a+s,b+t)-f(a,b)\bigr).
\tag{15.32}
$$

初始校准读数为 $f(0,0)$，不预设它为零。若改用 $\ell-f(0,0)$，须对全部校准输出作同一个常数平移。

**定义 15.11（完整持久状态与同源联合像）。** 每端 $i\in\{A,B\}$ 的状态集 $W_i$ 可有限或无限。初始化是固定状态 $\mathrm{Init}_i\in W_i$；更新只接收自身状态及当前公开标记，解码只接收自身状态。令 $z(w)=\sum_{u\text{ 在 }w\text{ 中}}u$，要求

$$
\begin{gathered}
\sigma_i(\varnothing)=\mathrm{Init}_i,\qquad
\sigma_i(wu)=\mathrm{Update}_i(\sigma_i(w),u),\qquad
\mathrm{Decode}_i(\sigma_i(w))=o_i(z(w)),\\
W_i^{\mathrm{reach}}=\{\sigma_i(w):w\in U^*\},\qquad
Q=\{(\sigma_A(w),\sigma_B(w)):w\in U^*\}.
\end{gathered}
\tag{15.33}
$$

精确解码要求包含初始边界及每个有限前缀，两端之间没有运行时通信。没有另给的当前 $a$、$b$、$h$、$\ell$、步数或过去输入词；任何能再次参与更新或解码的档案、计数器、索引、缓存及控制状态均属于所计的 $W_i$。状态允许依赖历史，不要求存在 $S\to W_i$ 使它只依赖当前来源点。固定的 $f$、群运算、更新及解码函数是模型参数，不含随实际执行变化的外置状态。

三种任务保持定义15.10的来源、制备和标记不变，只改变 $o_i$：

| 15.11的任务 | $o_A(a,b,h)$ | $o_B(a,b,h)$ |
| --- | --- | --- |
| $T_+$：保留原钟及己方位置 | $(a,h,\ell)$ | $(b,h,\ell)$ |
| $T_-$：删除原钟显示，保留己方位置 | $(a,\ell)$ | $(b,\ell)$ |
| $T_\ell$：只保留校准钟 | $\ell$ | $\ell$ |

每个输出空间可取指定函数的实际像。$Q$ 只包含同一公共历史产生的局部状态对，通常不等于 $W_A^{\mathrm{reach}}\times W_B^{\mathrm{reach}}$。对任务 $T$，记 $M_A^T,M_B^T,J^T$ 分别为所有满足上述条件的实现中 $|W_A^{\mathrm{reach}}|,|W_B^{\mathrm{reach}}|,|Q|$ 的最小值；三项分别取下确界，以下将给出使三项同时达到的有限实现。

### 15.2 补偿图决定未来核及局部联合最小值

**定理 15.12（任意校准的补偿分类与同时达到）。** 在定义15.10–15.11下，令 $E=A\times B$，并定义恒定差方向及其增量：

$$
\begin{gathered}
D_f=\{d\in E:\ f(x+d)-f(x)\text{ 与 }x\in E\text{ 无关}\},
\qquad \chi_f(d)=f(d)-f(0),\\
D_{f,H}=\{d\in D_f:\chi_f(d)\in H\},\qquad
\Gamma_H=\{(s,t,-\chi_f(s,t)):(s,t)\in D_{f,H}\}\subseteq S.
\end{gathered}
\tag{15.34}
$$

再取两条坐标轴上的限制：

$$
\begin{aligned}
P_A&=\{s\in A:(s,0)\in D_f\},&
\chi_A(s)&=\chi_f(s,0),& P_A^H&=\chi_A^{-1}(H),&P_A^0&=\ker\chi_A,\\
P_B&=\{t\in B:(0,t)\in D_f\},&
\chi_B(t)&=\chi_f(0,t),& P_B^H&=\chi_B^{-1}(H),&P_B^0&=\ker\chi_B.
\end{aligned}
\tag{15.35}
$$

这些方向集均为相应群的子群，$\chi_f,\chi_A,\chi_B$ 为同态，$\Gamma_H\le S$。两来源点 $z,z'$ 在同端的所有共同未来词后读数相同，当且仅当 $z'-z$ 属于下列对应子群：

$$
\begin{aligned}
N_A^+&=\{(0,t,0):t\in P_B^0\},&
N_B^+&=\{(s,0,0):s\in P_A^0\},\\
N_A^-&=\{(0,t,-\chi_B(t)):t\in P_B^H\},&
N_B^-&=\{(s,0,-\chi_A(s)):s\in P_A^H\},\\
N_A^\ell&=\Gamma_H,&N_B^\ell&=\Gamma_H.
\end{aligned}
\tag{15.36}
$$

最小值为

| 15.12的任务最小值 | $M_A^T$ | $M_B^T$ | $J^T$ |
| --- | --- | --- | --- |
| 双钟任务 $T_+$的同时最小实现 | $n_S/|P_B^0|$ | $n_S/|P_A^0|$ | $n_S$ |
| 删原钟任务 $T_-$的同时最小实现 | $n_S/|P_B^H|$ | $n_S/|P_A^H|$ | $n_S$ |
| $T_\ell$的同时最小实现 | $n_S/|D_{f,H}|$ | $n_S/|D_{f,H}|$ | $n_S/|D_{f,H}|$ |

每行均有一对局部实现同时达到该行三项；实现依赖任务行。两端各自保存 $S/N_i^T$，它们同源联合像的大小是

$$
\left|\{(z+N_A^T,z+N_B^T):z\in S\}\right|
=[S:N_A^T\cap N_B^T].
\tag{15.37}
$$

证明。先在本校准计算中使用恒定差的标准加法性质。有限向量空间中的 additive translator 及其子群性见 Lai，*Additive and Linear Structures of Cryptographic Functions*，FSE 1994，LNCS 1008（1995），§2、Theorem 1 及式(5)，[DOI](https://doi.org/10.1007/3-540-60590-8_6)。有限交换群上的差分关系 $f(x+d)=f(x)+c$ 亦见 Baudrin 等，*Commutative Cryptanalysis as a Generalization of Differential Cryptanalysis*（2025），Definition 1，[DOI](https://doi.org/10.1007/s10623-025-01625-9)。这里无需域结构：零方向的差为零；对 $d,e\in D_f$，

$$
f(x+d+e)-f(x)
=\bigl(f(x+d+e)-f(x+d)\bigr)+\bigl(f(x+d)-f(x)\bigr)
=\chi_f(e)+\chi_f(d).
\tag{15.38}
$$

且 $f(x-d)-f(x)=-\chi_f(d)$。这证明 $D_f$ 是子群及 $\chi_f$ 可加；其轴限制、核、$H$ 的原像也为子群。补偿图是同态 $d\mapsto(d,-\chi_f(d))$ 的像，其第一坐标投影单射，故 $|\Gamma_H|=|D_{f,H}|$。这些已知的恒定差性质在此只承担补偿分类中的一步。

设 $z=(a,b,h)$，$z'-z=(s,t,k)$。共同续接总增量 $(u,v,w)$ 后的校准读数之差为

$$
k+f(a+u+s,b+v+t)-f(a+u,b+v).
\tag{15.39}
$$

全部平移可由允许词实现，故 $(a+u,b+v)$ 遍历 $E$。式(15.39)恒为零恰好要求 $(s,t)\in D_f$ 且 $k=-\chi_f(s,t)$；$k\in H$ 又恰给 $D_{f,H}$。于是只读 $\ell$ 的未来核为 $\Gamma_H$。加入 $A$ 端的己方位置输出，空续接就强制 $s=0$；再加入原钟输出就强制 $k=0$。$B$ 端对称，得到式(15.36)。反向逐项代入式(15.39)，即可见每个所列差在所有未来词后保持对应读数相等。此论证也覆盖生成元输入，因为任何所需总增量有一个合法生成元词。

现在应用既有未来行为商的最小性。[TransportMemoryCompletion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) §2.1–2.3 的实际轨道、历史摘要满射与陪集计数在这里取作用群 $S$、来源轨道 $S$、初态稳定子 $\{0\}$，并取唯一的类型顶点。因而该卷允许外部已知的顶点不携带任何免费位置或钟值。有限确定性机器的经典背景是 Moore，*Gedanken-experiments on Sequential Machines*（1956），Theorem 4，pp.142–143，[原文](https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf)；本平移系统由生成元及逆连通，满足其强连通前提。

仓内 `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean` 的 `controlled_behavior_universal_property` 则适用于有限来源 $Y$、有限状态 $W$、满射实现 $Y\to W$ 及交换的更新、读出方程。这里可取 $Y=S$、来源更新 $z\mapsto z+u$、指定读出 $o_i$；但一般历史摘要未必有这样的 $S\to W$。对于定义15.11所允许的全部候选，所需的历史论证如下。若 $\sigma_i(w)=\sigma_i(w')$，确定性更新使任意共同续接后的状态仍相同，精确解码遂给相同未来读数。因此

$$
\pi_i:W_i^{\mathrm{reach}}\longrightarrow S/N_i^T,
\qquad \pi_i(\sigma_i(w))=z(w)+N_i^T
\tag{15.40}
$$

良定义。每个来源点可达，所以 $\pi_i$ 满射，得到 $|W_i^{\mathrm{reach}}|\ge[S:N_i^T]$，不要求 $W_i$ 有限。对同一历史产生的状态对，$\pi_A,\pi_B$ 一起满射到式(15.37)左侧的实际像，故联合下界也是该像的大小。两个来源点在此像下相等恰好是差同时落在 $N_A^T,N_B^T$ 中；每条纤维为其交的一个陪集，得到式(15.37)的指数，而不是两个局部指数之积。

达到构造只使用各端自身的商状态：

$$
\begin{gathered}
W_i=S/N_i^T,\qquad \mathrm{Init}_i=0+N_i^T,\\
\mathrm{Update}_i(z+N_i^T,u)=(z+u)+N_i^T,
\qquad \mathrm{Decode}_i(z+N_i^T)=o_i(z).
\end{gathered}
\tag{15.41}
$$

平移保持陪集相等，空未来词保证读数在陪集上常值，故更新与解码均良定义。所有商状态可达；初态解出的校准钟是 $f(0,0)$。两端从同一零制备出发，按同一标记更新，实际状态对恰遍历式(15.37)的像。这给每行的局部与联合同时达到。

最后，$N_A^+\cap N_B^+=N_A^-\cap N_B^-=\{0\}$，因为交中两个空间分量均须为零，钟分量也随之为零。故前两行的联合最小值均为 $n_S$。也可从联合当前输出恢复 $a,b,\ell$，再由 $h=\ell-f(a,b)$ 恢复整个 $S$。最后一行两核均为 $\Gamma_H$；两端取同一商后，联合像是该商的对角像。代入各子群的阶得到全表。证毕。

### 15.3 删钟比例、相位纤维与坐标运输

**定理 15.13（原钟的精确歧义与位宽差）。** 令

$$
L_A=\operatorname{im}\chi_A\cap H,\qquad
L_B=\operatorname{im}\chi_B\cap H.
\tag{15.42}
$$

在 $A$ 端的规范 $T_-$ 未来行为类 $z+N_A^-$ 中，原钟的可能值恰为 $h+L_B$；$B$ 端为 $h+L_A$。因此原钟能由该端的完整 $T_-$ 未来行为唯一恢复，恰好当相反轴的 $L$ 为零子群。同时

$$
\frac{M_A^+}{M_A^-}=|L_B|,\qquad
\frac{M_B^+}{M_B^-}=|L_A|,\qquad
1\le |L_A|,|L_B|\le |H|.
\tag{15.43}
$$

令 $R_A=|L_B|,R_B=|L_A|$。若以定长二进制字保存端 $i$ 的有限状态，则其最小位宽差满足

$$
\begin{gathered}
\Delta_i^{\mathrm{bits}}=
\lceil\log_2 M_i^+\rceil-\lceil\log_2 M_i^-\rceil,\\
\lfloor\log_2R_i\rfloor
\le\Delta_i^{\mathrm{bits}}
\le\lceil\log_2R_i\rceil
\le\lceil\log_2|H|\rceil.
\end{gathered}
\tag{15.44}
$$

原钟不在规范商上可恢复时，并不排除更大的非最小 $T_-$ 状态保存它；完整过去公共词也总能恢复原钟。

证明。$A$ 端同类来源点恰写为 $(a,b+t,h-\chi_B(t))$，$t\in P_B^H$。$\chi_B(P_B^H)=L_B$，而子群在取负下不变，故原钟像精确为 $h+L_B$。每个这样的来源点都可达，所以这里没有虚构相位。像为单点当且仅当 $L_B=\{0\}$。这正是函数在观察纤维上常值的恢复判据；其一般有效像形式见 `D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean` 的 `refinement_iff_kernel_inclusion_on_effective_images`，在此以原钟为待恢复函数、未来行为商为观察函数。$B$ 端同理。

限制同态 $\chi_B:P_B^H\to L_B$ 满射，任意像值的纤维都是 $P_B^0$ 的陪集。因此 $|P_B^H|=|P_B^0||L_B|$；另一轴同理。将这一步通常的同态纤维计数代入定理15.12即得式(15.43)。无论 $H$ 是否等于 $C$，交 $\operatorname{im}\chi_i\cap H$ 都不可删去。

含 $M$ 个状态的定长二进制编码需要且只需 $\lceil\log_2M\rceil$ 位，因为 $b$ 位恰有 $2^b$ 个字。置 $x=\log_2M_i^-$、$y=\log_2R_i$，则 $M_i^+=R_iM_i^-$。由

$$
\lceil x\rceil+\lfloor y\rfloor
\le\lceil x+y\rceil
\le\lceil x\rceil+\lceil y\rceil
\tag{15.45}
$$

得到式(15.44)。左式来自 $x+\lfloor y\rfloor\le x+y$ 及整数平移下的取整等式；右式来自 $x+y\le\lceil x\rceil+\lceil y\rceil$。对数状态数之差恰为 $\log_2R_i$，定长位宽差一般只是相邻两个整数之一；若 $R_i$ 为二的幂，两者相同。

若一个候选达到局部最小有限状态数，式(15.40)的满射必为双射，因此它与规范未来商有相同的原钟恢复判据。但保存整个 $S$ 并按平移更新也是一个 $T_-$ 候选，它总能读出 $h$。再者，完整公共历史 $w=u_1\cdots u_r$ 从零制备恢复 $z(w)=\sum_j u_j$，特别是 $h=\sum_j k_j$；不恢复结论只约束所指定的压缩边界，不能用于这个额外提供档案的访问模型。本卷 §13 的逐前缀档案恢复与保存其值所需记忆的区分，在此分别对应完整词和式(15.33)的持久状态。证毕。

**命题 15.14（校准共轭保留固定任务）。** $F_f$ 是定义15.10的原坐标系统与实际域 $\Omega_f$ 上系统的共轭。对一个固定任务 $o_i$，若同时将它运输为 $\widetilde o_i=o_i\circ F_f^{-1}$，则未来行为商及局部、联合最小状态数保持。相反，$T_+\to T_-$ 删除输出中的 $h$，是指定任务的改变，其可能节省恰由式(15.43)给出。将 $f$ 加上任意常数不改变这些最小值。

证明。式(15.31)的两个映射互逆，直接代入式(15.32)得 $\widetilde\tau_u F_f=F_f\tau_u$；且新钟减去新位置的 $f$ 等于 $h+k\in H$，故更新保持 $\Omega_f$。对每个词归纳并使用 $\widetilde o_iF_f=o_i$，可见两种坐标下每个来源的全部指定输出逐词相同。原来的状态、初始化、更新与解码于是原样承担运输后的任务，逆方向亦然，给相同最小值。沿词的校准增量还满足

$$
\ell(z')-\ell(z)=h'-h+f(a',b')-f(a,b),
\tag{15.46}
$$

这是 [ProcessGeometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) §9 的群值势差在此来源上的形式。删除 $h$ 没有运输原输出函数，而是对它再作投影，故应改用新的未来核。最后，$f+c$ 与 $f$ 的差分相同，因而 $D_f,\chi_f$ 和全部核不变；校准输出仅加上固定 $c$，原点输出也相应改变。证毕。

### 15.4 真子群时钟上的混合模四校准

**命题 15.15（一个局部节省而联合不变的混合校准）。** 取

$$
A=B=C=\mathbb Z/4\mathbb Z,\qquad H=\{0,2\},\qquad
f(a,b)=2ab+b\pmod4.
\tag{15.47}
$$

三种任务的 $(M_A^T,M_B^T,J^T)$ 依次为

$$
T_+:(32,16,32),\qquad T_-:(16,16,32),\qquad T_\ell:(8,8,8).
\tag{15.48}
$$

证明。平移差为 $2at+2sb+2st+t$。分别将 $a$、$b$ 增加一，常值条件强制 $t,s$ 都为偶数；这也充分。于是

$$
\begin{gathered}
D_f=\{0,2\}\times\{0,2\},\qquad \chi_f(s,t)=t,\qquad D_{f,H}=D_f,\\
P_B^H=\{0,2\},\quad P_B^0=\{0\},\qquad
P_A^H=P_A^0=\{0,2\}.
\end{gathered}
\tag{15.49}
$$

$|S|=32$，定理15.12给式(15.48)。以下把同时达到写成直接的局部坐标。置 $r=h+b\pmod4$、$p=a\pmod2$，各项都从零初始化：

| 15.15的任务状态 | $A$端保存 | $B$端保存 |
| --- | --- | --- |
| 混合模四双钟任务 $T_+$ | $(a,b,h)$ | $(b,h,p)$ |
| 混合模四删原钟任务 $T_-$ | $(a,r)$ | $(b,h,p)$ |
| 混合模四 $T_\ell$ | $(p,r)$ | $(p,r)$ |

公共增量 $(s,t,k)$ 下，上表所需各坐标分别按

$$
\begin{aligned}
(a,b,h)&\longmapsto(a+s,b+t,h+k),\\
(b,h,p)&\longmapsto(b+t,h+k,p+s\bmod2),\\
(a,r)&\longmapsto(a+s,r+t+k),\\
(p,r)&\longmapsto(p+s\bmod2,r+t+k)
\end{aligned}
\tag{15.50}
$$

更新，模四分量在模四中计算，$h,k\in H$。由 $h$ 为偶数可得

$$
\ell=(2a+1)r=(2p+1)r=h+b+2pb\pmod4.
\tag{15.51}
$$

这些等式及已保存的己方位置、原钟给每行所需解码。$(a,r)$ 的十六值全部可达，$(b,h,p)$ 的十六值及 $(p,r)$ 的八值也全部可达。前两行的状态对恢复整个 $(a,b,h)$，恰三十二个同源值；最后一行是八个标签的对角像。

空历史到达 $z=(0,0,0)$，公开增量 $(0,2,2)$ 到达 $z'=(0,2,2)$。它们的 $A$ 端 $T_-$ 状态同为 $(a,r)=(0,0)$，原钟却为 $0,2$；差属于 $N_A^-$，所以任何共同未来词后仍给相同 $(a,\ell)$。$T_+$ 当前即用原钟区分二者。这里 $L_B=\{0,2\}$ 而 $L_A=\{0\}$，正好解释两端节省的不对称。证毕。

### 15.5 进位校准的斜向补偿

**命题 15.16（模四高位给出四态的只钟未来商）。** 取 $A=B=\mathbb Z/4\mathbb Z$、$C=H=\mathbb Z/2\mathbb Z$，令 $f(a,b)=g(a+b)$，和先在模四中计算，其中

$$
g(0)=g(1)=0,\qquad g(2)=g(3)=1.
\tag{15.52}
$$

则

$$
\begin{gathered}
D_f=\{(s,t):s+t\in\{0,2\}\},\qquad D_{f,H}=D_f,\\
\chi_f(s,t)=
\begin{cases}0,&s+t=0\pmod4,\\1,&s+t=2\pmod4,\end{cases}\\
T_+:(32,32,32),\qquad T_-:(16,16,32),\qquad T_\ell:(4,4,4).
\end{gathered}
\tag{15.53}
$$

证明。对 $g$，平移零的差为零，平移二的差恒为一。平移一在 $x=0,1$ 的差分别为零、一；平移三在 $x=0,1$ 的差分别为一、零，均非常值。由于 $a+b$ 遍历模四，得到所列 $D_f$ 与 $\chi_f$。每条轴的 $P_i^H=\{0,2\}$、$P_i^0=\{0\}$，$|D_f|=8$，代入定理15.12即得三行最小值。特别地 $(1,1)\in D_f$ 且 $\chi_f(1,1)=1$，$(1,3)\in\ker\chi_f$；它们都不在 $P_A\times P_B$。故只钟任务的全补偿群不能换成两条轴向方向的乘积，恒定非零差方向也不能混作严格周期。

还有如下四态坐标，直接表现进位的未来作用。令 $j=a+b\pmod4$，$p=j\pmod2$。对公共 $(s,t,k)$，取 $v$ 为 $s+t\pmod4$ 在 $\{0,1,2,3\}$ 中的代表，并定义

$$
\kappa(p,v)=\left\lfloor\frac{p+v}{2}\right\rfloor\pmod2,
\qquad
(p,\ell)\longmapsto
\bigl(p+v\bmod2,\ \ell+k+\kappa(p,v)\bmod2\bigr).
\tag{15.54}
$$

写 $j=p+2q$，$q\in\{0,1\}$，则 $g(j)=q$ 且 $g(j+v)-g(j)=\kappa(p,v)$，所以该更新无需读取 $j$ 的高位。$T_\ell$ 两端都保存 $(p,\ell)$ 并输出第二分量。$T_-$ 两端分别保存 $(a,p,\ell)$、$(b,p,\ell)$，在式(15.54)之外各更新己方位置。四态和两个十六态局部像均完全可达；$T_-$ 的联合像由 $p=a+b\pmod2$ 约束，含三十二态，且由 $h=\ell-g(a+b)$ 恢复原来源。$T_+$ 两端各存 $(a,b,h)$ 即同时达到三十二态。各实现初始均为零。

本例不能写为双加性配对加两轴同态及常数：若 $f=\beta+u+v+c$ 有这种形式，由 $f(0,0)=0$ 得 $c=0$，由零行得 $g(b)=v(b)$；但同态必须满足 $v(2)=2v(1)=0$，与 $g(2)=1$ 矛盾。证毕。

### 15.6 仿射族的最大节省及取整

**命题 15.17（两端同时达到原钟群阶的比例）。** 对任意 $n\ge1$，取 $A=B=C=\mathbb Z/n\mathbb Z$、任意 $H\le C$，并令 $f(a,b)=a+b$。此时两端删钟比例都为 $|H|$；三行最小值分别为

$$
\begin{aligned}
T_+&:(n^2|H|,n^2|H|,n^2|H|),\\
T_-&:(n^2,n^2,n^2|H|),\\
T_\ell&:(n,n,n).
\end{aligned}
\tag{15.55}
$$

特别是 $H=C$ 时为 $(n^3,n^3,n^3)$、$(n^2,n^2,n^3)$、$(n,n,n)$。这给出可达到最大比例的群族；不要求对任意固定的 $A,B,H$ 都能选择某个 $f$ 达到同一上界。

证明。$D_f=A\times B$、$\chi_f(s,t)=s+t$；两轴字符均为恒等同态，故 $P_i^0=\{0\}$、$P_i^H=H$、$L_i=H$。对每个 $s$ 及每个 $h_0\in H$，恰有一个 $t=h_0-s$，故 $|D_{f,H}|=n|H|$。定理15.12给式(15.55)。显式地，$T_+$ 两端保存全来源；$T_-$ 两端保存 $(a,\ell)$、$(b,\ell)$；$T_\ell$ 两端都保存 $\ell$。它们从零初始化，原钟按 $h\mapsto h+k$、己方位置按平移更新，新钟统一按 $\ell\mapsto\ell+s+t+k$ 更新。前两行的状态对恢复全来源，最后一行是模 $n$ 标签的对角像。

当 $n=3,H=C$ 时，局部状态数从 $27$ 降为 $9$，对数状态数减少 $\log_2 3$，定长位宽却从 $\lceil\log_2 27\rceil=5$ 降为 $\lceil\log_2 9\rceil=4$，只减少一位。另一方面，若固定 $A=B=\{0\}$、$H=C=\mathbb Z/2\mathbb Z$，则任意 $f$ 都只有零轴方向，$L_A=L_B=\{0\}$，两端删钟比例恒为一。因此最大比例的可达性确实需要对群族作上述限定。证毕。

### 15.7 零节省的充分条件及非必要性

**命题 15.18（恒定行、双加性校准与轴相位）。** 若存在 $a_*\in A$ 使 $b\mapsto f(a_*,b)$ 为常数，则 $L_B=\{0\}$，$A$ 端删除原钟显示不减少最小状态数；恒定列给对称结论。特别地，若 $f=\beta$ 是双加性配对，令

$$
K_A=\{s:\ \beta(s,b)=0\ \forall b\in B\},\qquad
K_B=\{t:\ \beta(a,t)=0\ \forall a\in A\},
\tag{15.56}
$$

则 $D_\beta=K_A\times K_B$、$\chi_\beta=0$，两端均无删钟节省，并且

$$
\begin{aligned}
T_\pm&:\left(\frac{n_S}{|K_B|},\frac{n_S}{|K_A|},n_S\right),\\
T_\ell&:\left(\frac{n_S}{|K_A||K_B|},
                 \frac{n_S}{|K_A||K_B|},
                 \frac{n_S}{|K_A||K_B|}\right).
\end{aligned}
\tag{15.57}
$$

证明。对任意 $t\in P_B$，在恒定行取差即得 $\chi_B(t)=f(a_*,b+t)-f(a_*,b)=0$，所以 $L_B=\{0\}$。双加性校准有零行及零列；进一步，其平移差为 $\beta(a,t)+\beta(s,b)+\beta(s,t)$。若此差恒定，比较 $a$ 与零、$b$ 与零分别迫使 $t\in K_B,s\in K_A$，此时剩下的常数 $\beta(s,t)$ 也为零。反向这些根方向都给零差，故得到 $D_\beta$ 及 $\chi_\beta$，代入定理15.12给式(15.57)。这是补偿分类的双加性特化。证毕。

**命题 15.19（每行非恒定仍可完全没有删钟节省）。** 取 $A=\mathbb Z/2\mathbb Z$、$B=C=H=\mathbb Z/3\mathbb Z$，令 $r(0)=0,r(1)=1$，并取

$$
f(a,b)=r(a)+b^2\pmod3.
\tag{15.58}
$$

两行都非恒定，但 $P_B=\{0\}$，所以 $A$ 端删钟比例为一。事实上 $D_f=\{(0,0)\}$，三种任务的两个局部最小值及联合最小值全为十八。

证明。每行在 $b=0,1$ 的值相差一，故无恒定行。对 $t\ne0$，$B$ 方向差为 $2bt+t^2$；其在 $b=0,1$ 的差是 $2t\ne0\pmod3$，所以没有非零 $B$ 恒定差方向。一般方向 $(s,t)$ 的差为 $r(a+s)-r(a)+2bt+t^2$，在 $b$ 上恒定先强制 $t=0$。若 $s=1$，剩下的差在 $a=0,1$ 分别为一、负一，两者在模三不同，故还须 $s=0$。于是 $D_f$ 平凡、全部未来核平凡，而 $|S|=2\cdot3\cdot3=18$，定理15.12给所述各最小值。恒定行是命题15.18中的充分条件，并非零节省的必要条件。证毕。

## 15.99 追加锚

## 16. 和校准时钟的同源接口与任务记忆分裂

### 16.1 单零来源、完整状态与和校准商

**定义 16.60（和校准的封闭预测问题）。** 在定义15.10–15.11中取 $A=B=E$，其中 $E$ 为有限交换群；本节的 $E$ 表示每一端的位置群。仍令 $C=\mathbb Z/m\mathbb Z$、$m\ge1$、$H\le C$，固定已知函数 $g:E\to C$，并取

$$
S=E\times E\times H,\qquad s_0=(0,0,0),\qquad
f(a,b)=g(a+b),\qquad \ell(a,b,h)=g(a+b)+h.
\tag{16.30}
$$

唯一外部类型顶点固定不变。每个 $(u,v,k)\in S$ 都是处处合法的公开标记，同时作用于两端，使来源变为 $(a+u,b+v,h+k)$。从已知 $s_0$ 出发允许所有有限词；每个来源点都由一个标记可达。指定局部任务为 $o_A=(a,\ell)$、$o_B=(b,\ell)$，另比较只输出 $\ell$ 的任务。精确性要求空词和每个有限前缀均正确。

预测器的初始化固定，更新只读其完整持久状态与当前标记，解码只读其状态。己方位置也须保存在所计状态内；当前来源、传感器、原钟、校准钟、步数、历史和控制状态均不作为额外输入。固定的群运算与 $g$ 属于更新、解码的参数。允许任意依赖过去词的候选状态，不预设候选只依赖当前来源。初始输出是 $g(0)$，不要求 $g(0)=0$。

定义

$$
\begin{gathered}
D=\{d\in E:\ g(x+d)-g(x)\text{ 对全部 }x\in E\text{ 是同一 }H\text{ 中元素}\},\\
\chi(d)=g(d)-g(0)\quad(d\in D),\qquad
K=\{(d,-\chi(d)):d\in D\}\le E\times H,\\
\widehat Q=(E\times H)/K,\qquad B_0=E/D,\\
\Psi:S\to\widehat Q,\quad \Psi(a,b,h)=[(a+b,h)],\qquad
\sigma:\widehat Q\to B_0,\quad \sigma([(x,h)])=[x].
\end{gathered}
\tag{16.31}
$$

这里 $[x]=x+D$，而 $[(x,h)]$ 是模 $K$ 的类；$B_0$ 与观察端 $B$ 不同。$\widehat Q$ 专指任务商，定义15.11的 $Q$ 仍指实际联合像。恒定差的可加性及取逆性质由定理15.12的式(15.38)给出，故 $D\le E$、$\chi:D\to H$ 是同态、$K$ 是子群。$\sigma$ 良定义，因为改变代表元只使 $x$ 增加 $D$ 中元素。由 $H\le C$，以下涉及 $H$ 的和、差也可在 $C$ 内计算。

### 16.2 未来任务商与两个完全可达的局部空间

**定理 16.61（和校准的最小闭合状态）。** 在定义16.60下，$\widehat Q$ 恰为只钟任务的全部未来行为商，且

$$
|\widehat Q|=\frac{|E||H|}{|D|},\qquad
W_A=E\times\widehat Q,\quad W_B=E\times\widehat Q.
\tag{16.32}
$$

上述两个局部空间全部可达，分别实现 $o_A,o_B$ 的最小状态数 $|E||\widehat Q|$；只钟任务的最小状态数为 $|\widehat Q|$。这些下界覆盖定义16.60允许的全部历史依赖候选。

令 $q_0=[(0,0)]$，$\delta([(x,h)])=g(x)+h$，$t=u+v$。达到下界的固定状态律为

$$
\begin{aligned}
\mathrm{Init}_{\ell}&=q_0,&
\mathrm{Update}_{\ell}(q;(u,v,k))&=q+[(t,k)],&
\mathrm{Decode}_{\ell}(q)&=\delta(q),\\
\mathrm{Init}_A&=(0,q_0),&
\mathrm{Update}_A((a,q);(u,v,k))&=(a+u,q+[(t,k)]),&
\mathrm{Decode}_A(a,q)&=(a,\delta(q)),\\
\mathrm{Init}_B&=(0,q_0),&
\mathrm{Update}_B((b,q);(u,v,k))&=(b+v,q+[(t,k)]),&
\mathrm{Decode}_B(b,q)&=(b,\delta(q)).
\end{aligned}
\tag{16.33}
$$

证明。定理15.12的补偿分类在 $f(a,b)=g(a+b)$ 下只需考察总位置 $x=a+b$。两点 $(x,h),(x',h')$ 的全部未来校准输出相同，恰好是

$$
\forall t\in E,\quad g(x+t)+h=g(x'+t)+h'
\quad\Longleftrightarrow\quad
x'-x\in D,\quad h'-h=-\chi(x'-x).
\tag{16.34}
$$

未来原钟增量在两边相消，每个 $t$ 由 $(t,0,0)$ 实现。因此该等价关系正是模 $K$ 相等，且 $|K|=|D|$。$\delta$ 良定义是因为 $g(x+d)+h-\chi(d)=g(x)+h$。式(16.33)随来源平移交换，初始解码为 $g(0)$。任取 $q=[(x,h)]$，来源 $(a,x-a,h)$ 达到任意 $A$ 状态 $(a,q)$；来源 $(x-b,b,h)$ 达到任意 $B$ 状态 $(b,q)$。己方位置不同时空续接已区分，位置相同而 $q$ 不同时式(16.34)给一个共同未来标记区分。

最小性所用的是定理15.12及 [TransportMemoryCompletion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) §2.1–2.3的封闭未来商机制：此处作用群与实际轨道都是 $S$，初态稳定子为 $\{0\}$，类型顶点只有一个。对任意候选，两个历史若到达同一完整内部状态，确定性更新与精确解码使它们所有共同续接的任务输出相同。因此从候选可达状态到这里的任务商、或相应局部空间，按“取产生它的历史的当前来源类”给出良定义满射。每个来源可达保证满射性，故上述状态数下界也适用于不经 $S\to W$ 因子分解的历史摘要。证毕。

### 16.3 局部快照的当前同源条件

**定理 16.62（同一当前来源的精确恢复）。** 对定理16.61中的任意两个单独可达状态 $(a,q_A)$ 与 $(b,q_B)$，它们同属一个来源点的局部像，当且仅当

$$
q_A=q_B=q,\qquad [a]+[b]=\sigma(q).
\tag{16.35}
$$

若条件成立，任取代表元 $q=[(x,r)]$，令 $d=a+b-x\in D$，则唯一来源为

$$
(a,b,h),\qquad h=r-\chi(d).
\tag{16.36}
$$

所得 $h\in H$ 与代表元选择无关。因此实际局部状态对恢复整个 $S$。这里的同源条件是当前来源的可实现性；它不判定两份已发生历史是否相同。

证明。若来源为 $(a,b,h)$，两端任务坐标都等于 $\Psi(a,b,h)$，投影到 $B_0$ 得式(16.35)。反向，$d\in D$ 使

$$
(a+b,r-\chi(d))=(x,r)+(d,-\chi(d)),
\tag{16.37}
$$

故其任务类为 $q$，且来源由一个公开标记可达。若另取 $(x+e,r-\chi(e))$，其中 $e\in D$，则新的差为 $d-e$，恢复值是 $r-\chi(e)-\chi(d-e)=r-\chi(d)$。固定 $a+b$ 后，$[(a+b,h)]=[(a+b,h')]$ 强制 $(0,h'-h)\in K$，而 $K\cap(\{0\}\times H)=\{0\}$，故 $h=h'$。

这证明的是存在同一个当前来源；对这里仅依赖来源的最小实现，也等价于存在一份共同历史实现该对状态。它不恢复给定的过去词：空词与单个零标记已是不同历史，却产生同一来源与同一局部状态。证毕。

### 16.4 可比较的共同标签、矩形支持与锐字母表

**定理 16.63（精确同源接口的最小共同标签）。** 定义两端各自从已计状态计算的标签

$$
\begin{aligned}
c_A:E\times\widehat Q&\to B_0\times\widehat Q,&c_A(a,q)&=([a],q),\\
c_B:E\times\widehat Q&\to B_0\times\widehat Q,&c_B(b,q)&=(\sigma(q)-[b],q).
\end{aligned}
\tag{16.38}
$$

则局部状态对实际同源当且仅当 $c_A=c_B$。其支持由 $|B_0||\widehat Q|$ 个完整的 $|D|\times|D|$ 矩形组成，两侧投影分别互不相交。每个共同标签有恰好 $|D|^2$ 个来源点；完整状态对则只有一个来源点。

在所有以两个确定性标签的相等恰好判定同源性的接口中，实际使用的标签数至少为 $|B_0||\widehat Q|$，式(16.38)达到此数。若 $q$ 已由单独的相等测试匹配，则余下测试条件下的补充字母表至少为 $|B_0|$，也能达到。这里计数的是从现有局部状态算出的接口值，不增加持久状态，也不宣称任意交互通信协议的位数下界。

两端的标签在同一公开标记 $(u,v,k)$ 下都按

$$
(z,q)\longmapsto\bigl(z+[u],q+[(u+v,k)]\bigr)
\tag{16.39}
$$

更新。当任务坐标已经匹配时，缺陷 $[a]+[b]-\sigma(q)$ 在共同运输下不变。

证明。式(16.38)相等正是式(16.35)。固定 $(z,q)\in B_0\times\widehat Q$，相应两侧纤维为

$$
\begin{aligned}
\mathcal A_{z,q}&=\{(a,q):[a]=z\},\\
\mathcal B_{z,q}&=\{(b,q):[b]=\sigma(q)-z\}.
\end{aligned}
\tag{16.40}
$$

两者各有 $|D|$ 个元素且非空。任取其中一对，定理16.62给唯一来源，所以其整个乘积都在实际像内。不同 $(z,q)$ 的两侧纤维分别不交，全部实际对又必在其中某个乘积内。由定理16.62的单射恢复，标签在 $S$ 上的纤维大小就是这个乘积的大小。

将相容关系表示为两侧投影不交的完整矩形，所用的一般关系事实是 Riguet，*Relations binaires, fermetures, correspondances de Galois*（1948），§7，Proposition 11，pp.132–133，[DOI:10.24033/bsmf.1401](https://doi.org/10.24033/bsmf.1401) 的双函数关系刻画。这里已由式(16.35)直接算出具体矩形；该一般刻画只承担支持结构的对应。

设另有 $\lambda_A:W_A\to L$、$\lambda_B:W_B\to L$，对所有局部状态对满足“同源当且仅当标签相等”。在一个非空完整矩形内，固定一侧的一个点，可见另一侧所有点同值；再交换两侧，整个矩形同值。两个不同矩形若共用该值，取第一个的 $A$ 点与第二个的 $B$ 点便被错误接受，故每个矩形必须有不同值。这给锐下界；固定 $q$ 后有 $|B_0|$ 个同样非空的矩形，给条件字母表下界。事实上，只要求两个函数在全部实际对上相等，它们就都经式(16.38)因子分解；要求相等还足以判定同源，才进一步要求不同矩形的值不同。

$A$ 端的标签运输由 $a'=a+u$ 直接得到。$B$ 端则用

$$
\sigma\bigl(q+[(u+v,k)]\bigr)-[b+v]
=\sigma(q)+[u+v]-[b]-[v]
=\sigma(q)-[b]+[u].
\tag{16.41}
$$

两侧已匹配的 $q$ 在运输后仍匹配，且新缺陷为 $[a+u]+[b+v]-\sigma(q)-[u+v]$，等于旧缺陷。标签只是式(16.33)状态的函数，上述相等测试本身没有引入运行时的跨端输入。证毕。

### 16.5 共同标签细化与任务扩张的两个正合列

**命题 16.64（同源缺陷取第一位置商）。** 令 $\Gamma=\ker\Psi$，令 $N_A,N_B$ 为定理16.61的两个来源到局部状态同态的核，并令 $N_\Sigma=N_A+N_B$。则

$$
\begin{gathered}
\Gamma=\{(u,v,-\chi(u+v)):u+v\in D\},\\
N_A=\{(0,d,-\chi(d)):d\in D\},\qquad
N_B=\{(d,0,-\chi(d)):d\in D\},\\
N_\Sigma=\{(d_1,d_2,-\chi(d_1+d_2)):d_1,d_2\in D\},\qquad
N_A\cap N_B=\{0\},\\
\Gamma/N_\Sigma\cong B_0,\quad
(u,v,k)+N_\Sigma\longmapsto[u],\\
S/N_\Sigma\cong B_0\times\widehat Q,\quad
(a,b,h)+N_\Sigma\longmapsto([a],\Psi(a,b,h)).
\end{gathered}
\tag{16.42}
$$

特别地，这里的缺陷同构使用第一位置 $u$ 模 $D$；$u+v$ 在 $\Gamma$ 上模 $D$ 恒为零。

共同标签对任务标签的细化正合列，总能按所示坐标分裂：

$$
0\longrightarrow B_0\xrightarrow{z\mapsto(z,0)}
B_0\times\widehat Q\xrightarrow{(z,q)\mapsto q}
\widehat Q\longrightarrow0.
\tag{16.43}
$$

而任务记忆本身具有另一条带标记正合列

$$
0\longrightarrow H\xrightarrow{\iota}\widehat Q
\xrightarrow{\sigma}B_0\longrightarrow0,
\qquad \iota(h)=[(0,h)].
\tag{16.44}
$$

它的分裂问题保留所示核与商标记。实际局部对与只匹配任务标签的局部对分别有

$$
|\mathcal R_{\rm actual}|=|E|^2|H|,
\qquad
|\mathcal R_{q}|=|E|^2|\widehat Q|,
\qquad
\frac{|\mathcal R_q|}{|\mathcal R_{\rm actual}|}=|B_0|.
\tag{16.45}
$$

其中 $\mathcal R_q=\{((a,q),(b,q)):a,b\in E,q\in\widehat Q\}$；在来源上，每个任务标签的纤维有 $|E||D|$ 个点。

证明。各核由式(16.31)、(16.33)直接取得；$\chi$ 可加给 $N_\Sigma$ 的表达式。$\Gamma\to B_0$ 的第一位置投影满射，因为 $(u,-u,0)\in\Gamma$；其核要求 $u\in D$，再由 $u+v\in D$ 得 $v\in D$，所以核恰为 $N_\Sigma$。这证明第一同构。对第二同构，映射 $([a],\Psi(a,b,h))$ 是同态；任给 $(z,[(x,h)])$，选择 $[a]=z$ 并令 $b=x-a$ 得其原像。核同样为 $N_\Sigma$。

一般的实际像与观察核商的对应可用已有 [`finiteObservationQuotientEquivRange`](../../../D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange.lean)：取来源 $X=S$、指标集 $I=\{A,B\}$、预算为两指标全体、观察为两个局部状态映射；余域分别是 $W_A,W_B$，取的是该联合映射的实际像。这里两个核交为零，再由定理16.62取得单射恢复；不能把实际像换成两个余域的全乘积。这个已有构造只要求有限观察指标，不额外要求每个组合可实现。

式(16.43)的截面是 $q\mapsto(0,q)$，在 $S/N_\Sigma$ 中对应选择 $q=[(x,h)]$ 后的 $(0,x,h)+N_\Sigma$，与代表元选择无关。对于式(16.44)，$\iota$ 单射由 $K\cap(\{0\}\times H)=\{0\}$ 得到，$\sigma$ 满射。若 $\sigma([(x,h)])=0$，则 $x\in D$ 且 $[(x,h)]=[(0,h+\chi(x))]$，故 $\ker\sigma=\operatorname{im}\iota$。

实际对按定理16.62与 $S$ 双射，也按定理16.63分为 $|B_0||\widehat Q|$ 个大小 $|D|^2$ 的矩形，二者均给 $|E|^2|H|$。匹配 $q$ 时两个位置各有 $|E|$ 种，得到式(16.45)。$\Gamma$ 中先选 $u\in E$ 及 $u+v\in D$，其余坐标唯一，所以 $|\Gamma|=|E||D|$，即任务来源纤维大小。两条正合列分别描述“补充哪些共同区别才能胶合”和“任务坐标能否按标记加法分开”，它们的核、商及问题均不同。证毕。

### 16.6 原钟值域内的加性校准

**定理 16.65（任务坐标分裂的精确条件）。** 定义16.60的任务扩张(16.44)作为带标记交换群扩张分裂，当且仅当 $\chi:D\to H$ 延拓为同态 $\alpha:E\to H$。等价地，存在这样的同态和函数 $\bar g:B_0\to C$，使

$$
g(x)=\alpha(x)+\bar g([x])\qquad(x\in E).
\tag{16.46}
$$

只要求 $\alpha$ 取值于较大的 $C$ 不足。分裂时，一个保标记的群坐标同构及其闭合任务律为

$$
\begin{gathered}
\widehat Q\longrightarrow B_0\times H,\qquad
[(x,h)]\longmapsto\bigl([x],h+\alpha(x)\bigr),\\
\mathrm{Init}=(0,0),\qquad
\mathrm{Update}((y,r);(u,v,k))=
\bigl(y+[u+v],r+k+\alpha(u+v)\bigr),\\
\mathrm{Decode}(y,r)=\bar g(y)+r.
\end{gathered}
\tag{16.47}
$$

这仍有 $|\widehat Q|$ 个状态；局部预测器再加上所计的己方位置，按式(16.33)运输该位置。

证明。先在本任务商中使用交换群扩张的标准机制：$\widehat Q$ 是 $0\to D\to E\to B_0\to0$ 沿 $\chi:D\to H$ 的推出，其关系正是 $(d,-\chi(d))=0$。推出及对应的 Hom–Ext 正合段见 Stacks Project，§12.6 “Extensions”，[tag 010I](https://stacks.math.columbia.edu/tag/010I)，推出构造与 Lemma 12.6.4；在该引理中取 $(M_1,M_2,M_3,N)=(D,E,B_0,H)$。连接映射把 $\chi$ 送至这里的扩张类，以下显式核查本校准所需的延拓与分裂对应。

若 $\alpha$ 存在，定义收缩同态

$$
r_\alpha:\widehat Q\to H,\qquad
r_\alpha([(x,h)])=\alpha(x)+h,
\qquad r_\alpha\iota=\operatorname{id}_H.
\tag{16.48}
$$

其在 $K$ 上为零，所以良定义。同时 $j([x])=[(x,-\alpha(x))]$ 与代表元无关，且 $\sigma j=\operatorname{id}_{B_0}$。式(16.47)第一行的逆是 $(y,r)\mapsto j(y)+\iota(r)$，得到带标记分裂。

反向，分裂给出一个同态截面 $j:B_0\to\widehat Q$。由 $\ker\sigma=\operatorname{im}\iota$，可定义唯一的收缩同态 $r:\widehat Q\to H$，使 $\iota(r(q))=q-j(\sigma(q))$，于是 $r\iota=\operatorname{id}_H$。令 $\alpha(x)=r([(x,0)])$；它是 $E\to H$ 的同态，而对 $d\in D$，$[(d,0)]=[(0,\chi(d))]$，故 $\alpha(d)=\chi(d)$。

若 $\alpha$ 延拓 $\chi$，则 $g-\alpha$ 在每个 $D$ 陪集上恒定，得到式(16.46)。反之，式(16.46)在 $x$ 与 $x+d$ 的差强制 $\alpha(d)=\chi(d)$。运输 $x\mapsto x+u+v$、$h\mapsto h+k$ 给式(16.47)的更新，解码等于 $g(x)+h$。由于 $\alpha(0)=0$、$\bar g(0)=g(0)$，初始输出也正确。证毕。

### 16.7 不分裂时的固定截面与闭合进位

**命题 16.66（最小任务状态仍有集合乘积坐标）。** 不论式(16.44)是否分裂，固定任一集合截面 $\tau:B_0\to E$，满足 $[\tau(y)]=y$、$\tau(0)=0$。每个 $q\in\widehat Q$ 唯一写为 $[(\tau(y),r)]$，其中 $(y,r)\in B_0\times H$。对代表元 $q=[(x,h)]$，相应坐标及闭合律为

$$
\begin{gathered}
y=[x],\qquad r=h+\chi(x-\tau(y)),\qquad \mathrm{Init}=(0,0),\\
t=u+v,\qquad y'=y+[t],\qquad
r'=r+k+\chi\bigl(\tau(y)+t-\tau(y')\bigr),\\
\mathrm{Decode}(y,r)=g(\tau(y))+r.
\end{gathered}
\tag{16.49}
$$

更新中的 $\chi$ 参数总在 $D$ 中；连续更新与标记相加相容，使用恰好 $|B_0||H|=|\widehat Q|$ 个可达状态。不分裂阻止的是按指定原钟群与位置商的加性分离，不阻止精确闭合预测或这种集合编码。

证明。$x-\tau([x])\in D$，由模 $K$ 关系得到表示存在。其 $y$ 被 $\sigma(q)$ 唯一确定，固定第一坐标后 $H$ 坐标由定理16.62证明中的 $K\cap(\{0\}\times H)=\{0\}$ 唯一确定。改变 $(x,h)$ 的代表元时，$h$ 的变化与 $\chi(x-\tau(y))$ 的变化相消。反向，每个 $(y,r)$ 对应 $[(\tau(y),r)]$，所以这确为集合双射。

更新先得到 $[(\tau(y)+t,r+k)]$，再换成 $\tau(y')$ 代表便给式(16.49)。$[\tau(y)+t-\tau(y')]=y+[t]-y'=0$，保证表达式有定义。若再接总位置增量 $t_2$ 及钟增量 $k_2$，记 $y''=y'+[t_2]$，两个进位之和为

$$
\begin{aligned}
&\chi\bigl(\tau(y)+t-\tau(y')\bigr)
 +\chi\bigl(\tau(y')+t_2-\tau(y'')\bigr)\\
&\hspace{2em}=\chi\bigl(\tau(y)+t+t_2-\tau(y'')\bigr).
\end{aligned}
\tag{16.50}
$$

故连续更新等于合并标记的更新；零标记给恒等，初态及每次解码由代表表达式正确。每个任务类可达，所以全部集合坐标可达。

此处使用的截面进位是 [TransportMemoryCompletion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) §6.1的已知坐标构造。具体取该节 $(K,G,Q,\iota,q)=(H,\widehat Q,B_0,\iota,\sigma)$，截面为 $s(y)=[(\tau(y),0)]$，则进位的 $H$ 坐标是 $\chi(\tau(y)+\tau(z)-\tau(y+z))$。已有 [截面进位构造](../../../D5/S1/Deficit/Cocycles/AdditiveCarryCocycle.lean)的 `kernelCarry`、`section_carry_cocycle` 取加法交换群 $X=\widehat Q$、$B=B_0$、商同态 $\sigma$ 及右逆 $s$，经 $\iota:H\cong\ker\sigma$ 运输到 $H$；归一化另外由 $\tau(0)=0$ 保证。对一个标记，其核坐标为 $k+\chi(t-\tau([t]))$，与上述两坐标进位相加恰为式(16.49)。标准截面构造在这里只承担任务状态运输这一步。证毕。

### 16.8 模四高位和校准的八值共同接口

**命题 16.67（四态任务不能独自认证十六态局部对）。** 取命题15.16的模型 $E=\mathbb Z/4\mathbb Z$、$C=H=\mathbb Z/2\mathbb Z$，令 $g(0)=g(1)=0$、$g(2)=g(3)=1$。记 $\operatorname{hi}(x)$ 为模四代表 $0,1,2,3$ 的高位。则 $D=\{0,2\}$、$\chi(2)=1$，且

$$
\widehat Q\cong\mathbb Z/4\mathbb Z,\qquad
[(x,h)]\longmapsto\rho=x+2h\pmod4.
\tag{16.51}
$$

任务初始化为 $\rho=0$，更新为 $\rho'=\rho+u+v+2k$，解码为 $\operatorname{hi}(\rho)$。两端分别保存 $(a,\rho)$、$(b,\rho)$，更新己方位置并解码己方位置与 $\operatorname{hi}(\rho)$。各局部有十六态，任务有四态；精确共同标签有八值。实际对有三十二个，匹配 $\rho$ 的对有六十四个。精确同源条件为

$$
\rho_A=\rho_B=\rho,\qquad a+b\equiv\rho\pmod2;
\qquad
c_A=(a\bmod2,\rho),\quad c_B=((\rho-b)\bmod2,\rho).
\tag{16.52}
$$

在“己方位置、任务相位”坐标中，$A=(0,0)$ 与 $B=(1,0)$ 是两个单独可达、任务相位相同而不能同源的状态。任务扩张是非分裂的 $0\to\mathbb Z/2\mathbb Z\xrightarrow{h\mapsto2h}\mathbb Z/4\mathbb Z\to\mathbb Z/2\mathbb Z\to0$。

证明。$D$ 与 $\chi$ 的值由命题15.16的恒定差计算取得。式(16.51)的同态核是 $\{(0,0),(2,1)\}=K$，且满射，故给所示同构。$\operatorname{hi}(x+2h)=g(x)+h$，更新由来源平移得到。定理16.61–16.63与命题16.64给可达性、最小值与共同标签计数；每个标签的支持矩形为 $2\times2$，有四个来源。来源 $(0,0,0)$ 实现所列 $A$ 状态，来源 $(3,1,0)$ 实现所列 $B$ 状态；合并后二位置和为奇数，违反式(16.52)。任何同态 $\alpha:\mathbb Z/4\mathbb Z\to\mathbb Z/2\mathbb Z$ 都满足 $\alpha(2)=2\alpha(1)=0$，不能等于 $\chi(2)=1$，故由定理16.65非分裂。证毕。

### 16.9 真子群原钟下相同计数与不同扩张

**命题 16.68（计数与较大值域校准均不决定分裂）。** 固定 $E=C=\mathbb Z/4\mathbb Z$、$H=\{0,2\}\le C$，仍取和校准。比较 $g_1(x)=x$ 与 $g_2(0)=g_2(2)=0$、$g_2(1)=g_2(3)=1$。两者均有 $D=\{0,2\}$、$|\widehat Q|=4$、局部最小值十六与十六、共同标签八值、实际对三十二个、只匹配任务类的对六十四个；但 $g_1$ 的任务扩张非分裂，$g_2$ 的任务扩张分裂。具体为

$$
\begin{aligned}
g_1:&\quad\chi_1(2)=2,\qquad
\widehat Q_1\cong\mathbb Z/4\mathbb Z,\quad[(x,h)]\mapsto x+h;\\
g_2:&\quad\chi_2=0,\qquad
\widehat Q_2\cong(\mathbb Z/2\mathbb Z)\times H,\quad[(x,h)]\mapsto([x],h).
\end{aligned}
\tag{16.53}
$$

$g_1$ 的恒定差同态延拓到 $E\to C$ 已经存在，却不存在所需 $E\to H$ 延拓。$g_2$ 则给出任务扩张分裂而任务标签相等仍不足以胶合的模型。

证明。对 $g_1$，每个方向的差为该方向本身，要求差落在 $H$ 恰使 $D=H$。同态 $(x,h)\mapsto x+h$ 的核为 $\{(0,0),(2,2)\}=K$，商为模四；$\iota$ 对应嵌入 $H=\{0,2\}$。若 $\alpha:E\to H$ 为同态，则 $\alpha(2)=2\alpha(1)=0$，不可能等于二。恒等映射 $E\to C$ 的确延拓 $\chi_1$，这也证明较大值域条件不足。此任务直接用 $\rho=x+h$，初始零、更新 $\rho'=\rho+u+v+k$、解码 $\rho$，有四态。

对 $g_2$，方向二的差为零，方向一在 $x=0,1$ 的差分别为一、三而不恒定，方向三同样如此，故 $D=\{0,2\}$、$\chi_2=0$。取 $\alpha=0$，$\bar g(0)=0$、$\bar g(1)=1$，式(16.47)给初态 $(0,0)$、更新 $(y,r)\mapsto(y+[u+v],r+k)$、解码 $\bar g(y)+r$。$H\cong\mathbb Z/2\mathbb Z$，所以两个任务群分别为 $\mathbb Z/4\mathbb Z$ 与 $(\mathbb Z/2\mathbb Z)^2$。其余相同计数由共同的 $|E|=4,|H|=|D|=2$ 得到。第二模型中取任务类 $q=0$ 及局部对 $(0,q),(1,q)$；两者单独可达却违反 $[a]+[b]=0$，从而分裂不保证只按任务标签胶合。证毕。

### 16.10 改变指定读出后的非和校准边界

**命题 16.69（非和任务可非分裂而仅按任务类精确胶合）。** 保持命题16.67的来源 $S=(\mathbb Z/4\mathbb Z)^2\times\mathbb Z/2\mathbb Z$、已知零制备、全部公开平移及封闭访问条件，但将指定校准读出改为

$$
f(a,b)=\operatorname{hi}(a),\qquad
\ell=\operatorname{hi}(a)+h.
\tag{16.54}
$$

这是指定任务的改变；不把原来的 $\operatorname{hi}(a+b)+h$ 作为读出随坐标运输。两个局部任务仍分别输出己方位置与这个新的 $\ell$。令 $\rho=a+2h\pmod4$，只钟任务有四个最小状态；两个局部最小可达空间分别为

$$
W_A^{\rm reach}=\{(a,\rho)\in(\mathbb Z/4\mathbb Z)^2:a\equiv\rho\pmod2\},
\quad |W_A^{\rm reach}|=8;
\qquad
W_B^{\rm reach}=(\mathbb Z/4\mathbb Z)^2,
\quad |W_B^{\rm reach}|=16.
\tag{16.55}
$$

这些空间上的固定闭合律为

$$
\begin{aligned}
\mathrm{Init}_{\ell}&=0,&\mathrm{Update}_{\ell}(\rho;(u,v,k))&=\rho+u+2k,&
\mathrm{Decode}_{\ell}(\rho)&=\operatorname{hi}(\rho),\\
\mathrm{Init}_A&=(0,0),&\mathrm{Update}_A((a,\rho);(u,v,k))&=(a+u,\rho+u+2k),&
\mathrm{Decode}_A(a,\rho)&=(a,\operatorname{hi}(\rho)),\\
\mathrm{Init}_B&=(0,0),&\mathrm{Update}_B((b,\rho);(u,v,k))&=(b+v,\rho+u+2k),&
\mathrm{Decode}_B(b,\rho)&=(b,\operatorname{hi}(\rho)).
\end{aligned}
\tag{16.56}
$$

对任意单独可达的局部状态，只要 $\rho_A=\rho_B$ 就恰好同源。全部三十二个任务类匹配对都是实际对，每个对恢复唯一 $h$。任务群仍为带标记的非分裂扩张 $0\to\mathbb Z/2\mathbb Z\xrightarrow{h\mapsto2h}\mathbb Z/4\mathbb Z\to\mathbb Z/2\mathbb Z\to0$，其中商记录 $a\bmod2$。

证明。$\operatorname{hi}(a)+h=\operatorname{hi}(a+2h)$，全部未来只钟输出由 $\rho$ 决定，式(16.56)只使用状态与标记。任意 $\rho$ 由 $(a,b,h)=(\rho,0,0)$ 达到。若 $\rho\ne\rho'$，取共同未来 $u=-\rho$，把第一相位化为零。若差为二或三，高位立即不同；若差为一，改取 $u=1-\rho$，两相位分别为一与二，高位也不同；均可令 $v=k=0$。所以四相位全部未来可分。

$A$ 的奇偶约束由 $\rho=a+2h$ 得到，且在更新中保持。满足它时有唯一 $h\in\mathbb Z/2\mathbb Z$ 使 $2h=\rho-a$，任取 $b$ 即达到该 $A$ 状态。$B$ 的任意 $(b,\rho)$ 可由 $(a,b,h)=(\rho,b,0)$ 达到。$A$ 的不同 $a$、$B$ 的不同 $b$ 由当前己方位置输出区别；己方位置相同而 $\rho$ 不同时，由上段的共同未来标记区别。定理16.61证明中的历史满射论证只用确定性更新、可达性与未来区分，因此在这个改变后的任务中分别给八、十六的下界；式(16.56)达到它们。

现在令两个可达局部状态的相位相等为 $\rho$。$A$ 的可达域已经保证 $2h=\rho-a$ 有唯一解，配上任意所给 $b$ 就是一个共同来源。反向，实际同源显然给相等 $\rho$。每个相位有两个 $A$ 状态、四个 $B$ 状态，形成 $2\times4$ 完整矩形；四个矩形共三十二个对，并各自对应八个来源。任务映射 $S\to\mathbb Z/4\mathbb Z$ 为 $(a,b,h)\mapsto a+2h$，满射且核为 $\{(a,b,h):a+2h=0\}$，故任务群与所示模四群同构。它的核标记为 $h\mapsto2h$、商标记为奇偶；模二非零元的两个模四提升均为四阶，不能给群同态截面，所以非分裂。此例中任务类在 $A$ 的可达域上已约束己方位置奇偶，不能用和校准中 $E\times\widehat Q$ 的全乘积假设替代。证毕。

### 16.11 和校准内部的单向蕴含

**推论 16.70（任务相等、精确胶合与加性分裂的范围）。** 在定义16.60的和校准族内，下列条件等价：对任意单独可达局部状态，任务类相等即足以保证实际同源；$D=E$；$B_0$ 为平凡群。它们都推出任务扩张(16.44)分裂，逆向蕴含不成立。若去掉和校准限制，“非分裂推出仅按任务类胶合失败”也不再成立。

证明。由式(16.45)，任务匹配关系包含实际关系，两者相等当且仅当 $|B_0|=1$，亦即 $D=E$。也可直接由式(16.35)看到：$D=E$ 时位置商条件恒成立；$D\ne E$ 时取 $q=0,a=0$ 和某个 $b\notin D$，得到单独可达的假匹配。$D=E$ 时 $\chi$ 自身已是 $E\to H$ 的延拓，定理16.65给分裂。命题16.68的 $g_2$ 模型给分裂却不能只按任务类胶合。命题16.69则给改变指定读出后的非和模型，其中任务扩张非分裂而任务匹配恰好都是实际对。三个判据分别量化全部共同未来输出、两个当前局部状态的实际来源、以及保留核与商标记的群运算；上述蕴含只在各自声明的来源、任务与可达域下成立。证毕。

## 16.99 追加锚

## 17. 空间切法、最小局部记忆与完整时钟标签的同源胶合

### 17.1 任意有限交换因子上的操作桥

**定义 17.10（固定来源与随切法改变的己方任务）。** 设 $A,B$ 为任意有限交换群，固定 $V=A\oplus B$、$C=\mathbb Z/m\mathbb Z$、$m\ge1$、$H\le C$ 及函数 $f:V\to C$。记 $C_r=\mathbb Z/r\mathbb Z$，其中 $C_1$ 为平凡群。来源、校准钟及来源数为

$$
S=V\times H,\qquad z_0=(0,0),\qquad
\ell(v,h)=f(v)+h,\qquad N=|V||H|.
\tag{17.60}
$$

初始校准钟为 $f(0)$，不预设为零。采用定义15.10–15.11的封闭访问条件：已知零制备，只有一个固定外部类型顶点；每个 $u\in S$ 都可作为公开平移输入，同时送达两端，在每个有限前缀均可继续使用任意这样的输入。每端从固定状态出发，确定性更新只读自身状态及当前输入，解码只读自身状态，在空历史及全部有限前缀精确输出。两端无运行时通信；任何能再次参与更新或解码的历史、档案、计数器、位置、钟值及控制信息都计入持久状态。竞争实现可保留任意历史，状态集可无限，不要求状态只经当前来源点因子分解。固定群运算、$f$ 及更新、解码函数不随执行变化。

一个合法有序切法是 $V=L_A\oplus L_B$，其中 $L_A\cong A,L_B\cong B$，即原两因子在某个 $V$ 的自同构下的像。令 $p_A,p_B$ 为沿此切法的投影。两端任务是

$$
o_A(v,h)=(p_Av,\ell(v,h)),\qquad
o_B(v,h)=(p_Bv,\ell(v,h)).
\tag{17.61}
$$

改变切法时，$S,f,H$、零制备与全部平移保持固定，所要求的己方坐标随切法改变；若用选定因子的内部坐标，公开输入也作相同的已知坐标转换。这是改变己方任务的优化问题。对一个固定旧任务同时运输读出与坐标的共轭问题仍由命题15.14处理。

沿用定理15.12的恒定差与补偿图，记

$$
\begin{gathered}
D_f=\{d\in V:f(x+d)-f(x)\text{ 与 }x\in V\text{ 无关}\},
\qquad \chi(d)=f(d)-f(0),\\
D=\{d\in D_f:\chi(d)\in H\},\qquad
\Gamma=\{(d,-\chi(d)):d\in D\},\qquad Q_\ell=S/\Gamma.
\end{gathered}
\tag{17.62}
$$

该定理给出 $D\le V$、$\chi|_D:D\to H$ 为同态及 $\Gamma\le S$；$Q_\ell$ 是完整未来校准钟类，而非只取当前钟值。当前钟由 $L(z+\Gamma)=\ell(z)$ 良定义地解码。再令

$$
\begin{gathered}
D_A=D\cap L_A,\quad D_B=D\cap L_B,\quad
d_A=|D_A|,\quad d_B=|D_B|,\\
K_A=\{(d,-\chi(d)):d\in D_B\},\qquad
K_B=\{(d,-\chi(d)):d\in D_A\},\qquad W_i=S/K_i.
\end{gathered}
\tag{17.63}
$$

$K_A$ 对应保持 $A$ 端己方坐标不变的 $B$ 轴方向，$K_B$ 对称。称切法使 $D$ **沿轴分裂**，若 $D=D_A\oplus D_B$。

**定理 17.11（最小记忆的实际像与同源判据）。** 在定义17.10下，最小可达局部状态数与最小实际联合状态数同时可达，分别为

$$
M_A=\frac{N}{d_B},\qquad M_B=\frac{N}{d_A},\qquad J_{\min}=N.
\tag{17.64}
$$

达到构造取 $W_A,W_B$。其自然满射 $\rho_i:W_i\to Q_\ell$ 给出钟类匹配空间 $F=W_A\times_{Q_\ell}W_B$，同源实际像由 $j(z)=(z+K_A,z+K_B)$ 给出。它们满足

$$
j(S)\subseteq F,\qquad |j(S)|=N,\qquad
|F|=\frac{N|D|}{d_A d_B},\qquad
j(S)=F\ \Longleftrightarrow\ D=D_A\oplus D_B.
\tag{17.65}
$$

对任意代表元 $x,y\in S$，实际性与完整钟类匹配分别等价于

$$
\begin{aligned}
(x+K_A,y+K_B)\in j(S)&\ \Longleftrightarrow\ y-x\in K_A+K_B,\\
(x+K_A,y+K_B)\in F&\ \Longleftrightarrow\ y-x\in\Gamma.
\end{aligned}
\tag{17.66}
$$

每个实际对都唯一恢复来源；使每个钟类匹配对均有来源的充要条件是沿轴分裂。各端最小载体嵌入己方坐标与完整钟类的乘积，其像在 $q=(v_0,h_0)+\Gamma$ 上的纤维恰为

$$
\begin{aligned}
\iota_A:W_A&\hookrightarrow L_A\times Q_\ell,
&\iota_A((v,h)+K_A)&=(p_Av,(v,h)+\Gamma),\\
\iota_B:W_B&\hookrightarrow L_B\times Q_\ell,
&\iota_B((v,h)+K_B)&=(p_Bv,(v,h)+\Gamma),\\
\iota_A(W_A)_q&=p_Av_0+p_A(D),
&\iota_B(W_B)_q&=p_Bv_0+p_B(D).
\end{aligned}
\tag{17.67}
$$

纤维大小依次为 $|D|/d_B,|D|/d_A$，不预设它们填满各自轴。式(17.65)–(17.67)通过可达状态的商同构转移到任意一对各自达到局部最小值的预测器；任意历史竞争者都受式(17.64)的下界约束。

证明。把定义15.10–15.11及定理15.12的删原钟任务应用于此切法，其两个未来核正是 $K_A,K_B$。所用的既有商构造在这里为

$$
\operatorname{Init}_i=0+K_i,\qquad
\operatorname{Update}_i(z+K_i,u)=z+u+K_i,\qquad
\operatorname{Decode}_i(z+K_i)=o_i(z).
\tag{17.68}
$$

全部来源可达，故全部商状态可达。若两段历史到达任意竞争者的同一状态，确定性更新与精确解码迫使它们在每个共同续接下同输出。因而“取产生该状态的历史的来源终点，再取 $K_i$ 类”给出 $W_i^{\mathrm{reach}}\twoheadrightarrow S/K_i$，即式(15.40)的历史满射。它不要求存在反向的 $S\to W_i^{\mathrm{reach}}$。对同一历史产生的联合状态，该满射对也满射到 $j(S)$。由于 $K_A\cap K_B=\{0\}$，$j$ 单射；结合商的阶即得式(17.64)，且式(17.68)同时达到三项。

每个 $\rho_i$ 的纤维是 $\Gamma/K_i$ 的陪集。用 $|Q_\ell|=N/|D|$ 计数，得到式(17.65)中的 $|F|$。两个代表陪集相交恰好要求 $y-x\in K_A+K_B$；若 $y-x=k_A+k_B$，则 $z=x+k_A=y-k_B$ 是共同来源。它唯一，因为两个核的交为零。钟类匹配只要求差落在 $\Gamma$。图同态 $d\mapsto(d,-\chi(d))$ 单射且可加，故 $K_A+K_B=\Gamma$ 等价于 $D_A+D_B=D$；两轴交为零，亦等价于 $d_A d_B=|D|$。

式(17.67)良定义。若同端两类在该映射下相等，来源差既在 $\Gamma$ 又保持己方坐标，故在 $K_i$，证明单射。固定 $q$ 的来源恰为 $(v_0,h_0)+\Gamma$，其己方坐标依次遍历所列仿射像；$p_A|_D,p_B|_D$ 的核分别为 $D_B,D_A$，得到纤维数。在这些实际像上，输入 $u=(u_V,u_H)$ 的闭合更新及解码为

$$
(a,q)\longmapsto(a+p_Au_V,q+(u+\Gamma)),\qquad
(b,q)\longmapsto(b+p_Bu_V,q+(u+\Gamma)),
\tag{17.69}
$$

解码分别为 $(a,L(q))$、$(b,L(q))$。实际匹配对的来源也可直接恢复为 $v=a+b$、$h=L(q)-f(v)$；实际性保证 $h\in H$ 及该来源具有标签 $q$。

若一个竞争者达到有限局部最小值，上述可达状态满射必为双射，并保持初始化、更新和输出。故两个这样的双射把同一历史的实际对恰好送到 $j(S)$，也把它们的完整钟类匹配送到 $F$，给出所称转移。证毕。

**命题 17.12（冗余历史使非最小状态的钟类匹配过宽）。** 取 $A=B=C=H=\{0\}$、$f=0$。两端均可保存输入词长度的奇偶性，初值为零，每次唯一的零输入使该位翻转，输出恒为零。这是各有两个可达状态的精确封闭预测器；其实际联合像有两个元素，而完整钟类匹配有四个元素。

证明。任意来源及全部未来输出均唯一，故 $D$ 平凡、切法分裂、最小局部状态数均为一。冗余预测器的同源状态对恰为 $(0,0),(1,1)$，但四个局部状态对都具有唯一的钟类。因而分裂后的胶合结论不能不加最小性限定便推广到任意冗余历史状态。证毕。

### 17.2 同阶循环因子的分裂最优性与整除支配

**定理 17.20（同阶二维来源的最小局部乘积）。** 在定义17.10中进一步取 $V=(\mathbb Z/n\mathbb Z)^2$、$n\ge1$；合法切法由 $GL_2(\mathbb Z/n\mathbb Z)$ 的有序基给出，两轴均为 $n$ 阶循环群。对每个由式(17.62)得到的 $D$，存在沿轴分裂的合法切法，且

$$
\min_{\text{合法切法}}M_A M_B=\frac{N^2}{|D|}.
\tag{17.70}
$$

达到此乘积最小值的切法恰为沿轴分裂的切法，亦恰为最小预测器可仅凭完整钟类匹配便精确胶合的切法。

证明。$n=1$ 时直接成立。设 $n>1$，把 $D$ 提升为 $\widetilde D=\{x\in\mathbb Z^2:x\bmod n\in D\}$，其中 $n\mathbb Z^2\subseteq\widetilde D$。以 $D$ 的整数代表及 $ne_1,ne_2$ 为列得到有限秩二生成矩阵。使用 [RRO 主卷 axiom 54.1](RECURSIVE_RELATIONAL_OBSERVATION.md) 所引的既有整数 Smith 标准形，即 Elman，*Lectures on Abstract Algebra*，Appendix D，[Theorem D.2，PDF 页862](https://www.math.ucla.edu/~rse/algebra_book.pdf#page=862)，存在左幺模矩阵 $U$ 及右幺模生成元变换，使

$$
U\widetilde D=s_1\mathbb Ze_1\oplus s_2\mathbb Ze_2,
\qquad 0<s_1\mid s_2.
\tag{17.71}
$$

右变换不改变所生成的格。关键是左变换满足 $U(n\mathbb Z^2)=n\mathbb Z^2$，所以 $s_1,s_2$ 都整除 $n$，$U$ 模 $n$ 后给合法自同构，并把 $D$ 送到 $(s_1\mathbb Z/n\mathbb Z)\times(s_2\mathbb Z/n\mathbb Z)$。取标准轴的逆像即得分裂切法。这里 Smith 标准形只作为对子群提升格的已有中间工具。

对任意切法，$D_A\oplus D_B\le D$，故 $d_A d_B\le|D|$，且取等号当且仅当沿轴分裂。将它代入式(17.64)，再用式(17.65)，即得全部结论。证毕。

**定理 17.21（逐素数整除支配与完整 Pareto 集）。** 在定理17.20的条件下，每个合法切法都存在一个分裂切法，使其轴交阶满足

$$
d_A\mid d'_A,\qquad d_B\mid d'_B;
\qquad \frac{M_A}{M'_A}=\frac{d'_B}{d_B}\in\mathbb N_{>0},\qquad
\frac{M_B}{M'_B}=\frac{d'_A}{d_A}\in\mathbb N_{>0}.
\tag{17.72}
$$

若原切法不分裂，至少一个比值为不小于二的整数。因此局部计数对 $(M_A,M_B)$ 的 Pareto 最小集恰为乘积最优计数对集。具体地，对每个 $p\mid n$，写

$$
D_p\cong C_{p^{r_{p,1}}}\oplus C_{p^{r_{p,2}}},\qquad
r_{p,1}\ge r_{p,2}\ge0,
\tag{17.73}
$$

其中 $D_p$ 是 $D$ 的 $p$ 主部分，$C_1$ 表示平凡群。独立地为每个素数选择 $(s_p,t_p)$ 为 $(r_{p,1},r_{p,2})$ 的一个排列。完整 Pareto 集为

$$
\mathcal P=
\left\{\left(\frac{N}{\prod_{p\mid n}p^{t_p}},
                  \frac{N}{\prod_{p\mid n}p^{s_p}}\right):
(s_p,t_p)\in\{(r_{p,1},r_{p,2}),(r_{p,2},r_{p,1})\}\right\}.
\tag{17.74}
$$

若有 $k$ 个素数满足 $r_{p,1}>r_{p,2}$，它恰有 $2^k$ 个不同有序对。对 $D=\{0\}$，所有切法均分裂且计数对为 $(N,N)$；对 $D=V$，所有切法均分裂且为 $(N/n,N/n)$；对 $n=1$，空素数积给唯一计数对 $(|H|,|H|)$。

证明。固定 $p$，省略其下标。原两轴交的 $p$ 部分是 $D_p$ 中两个相交平凡的循环子群，设阶为 $p^a,p^b$。由 $D_p$ 的指数知 $a,b\le r_1$。还必有 $\min(a,b)\le r_2$：否则把这两个子群各乘 $p^{r_2}$，得到循环 $p$ 群 $p^{r_2}D_p$ 中两个非零子群；它们仍分别包含在原两个子群中，故交平凡。但循环 $p$ 群的任意非零子群都含唯一的 $p$ 阶子群，矛盾。因此

$$
\max(a,b)\le r_1,\qquad \min(a,b)\le r_2.
\tag{17.75}
$$

从定理17.20的 Smith 分裂基出发，写 $n=\prod_{p\mid n}p^{e_p}$，在每个模 $p^{e_p}$ 分量上，把较大交阶的 Smith 轴指派给原交阶较大的轴；相等时任选。式(17.75)保证新两指数分别不小于旧指数。这些指派可独立进行：在每个 $GL_2(\mathbb Z/p^{e_p}\mathbb Z)$ 中选恒等或换轴矩阵，逐项用中国剩余定理合成模 $n$ 的矩阵，其行列式在每个素数处分量为单位，故整体可逆。将此矩阵用于 Smith 基所得两条全局轴仍使 $D$ 分裂。每个素数的指数分别增加，给出式(17.72)中的整除，而不只给数值大小。

相同构造实现式(17.74)的每一种指派。反过来，任意分裂切法把 $D_p$ 写成两循环轴交的直和；其阶与指数分别给 $a+b=r_1+r_2$、$\max(a,b)=r_1$，故无序指数只能是 $r_1,r_2$。这证明列表无遗漏；不同的不等指数素数指派改变 $d_A$ 的相应赋值，故计数为 $2^k$。

非分裂切法的乘积严格大于 $N^2/|D|$，其整除支配切法至少严格改善一个坐标。所有分裂计数对的正乘积相同，不同对之间不能有坐标支配。于是非分裂对都非 Pareto 最小，分裂对全部 Pareto 最小。平凡情形直接代入轴交的阶。证毕。

### 17.3 独立二进制存储的取整最小值

**推论 17.30（二进制位宽的每个最优切法均分裂）。** 对定理17.20的来源，采用两端分别定长二进制编码其完整可达状态的资源模型，令 $b(M)=\lceil\log_2M\rceil$，$b(1)=0$。在全部合法切法及精确封闭预测器上，最小总位宽是

$$
B_{\min}=\min_{(M_A,M_B)\in\mathcal P}
\bigl(b(M_A)+b(M_B)\bigr).
\tag{17.76}
$$

每个达到此最小位宽的切法都沿轴分裂，但并非每个分裂切法都达到它。若改用局部计数上的任意坐标单调不减函数 $P:\mathbb N_{>0}^2\to\mathbb R$ 作为罚函数，$\mathcal P$ 仍足以取得最小值，但其外的切法可以并列；二进制总位宽没有这种非分裂并列。

证明。$M$ 个状态的定长编码存在当且仅当 $M\le2^b$；任选单射编码并运输更新与解码即可达到 $b(M)$，未使用码字不属于可达状态。因此固定切法下的最小位宽由式(17.64)给出，即使有冗余实现因取整而使用同样多的位，也不能低于它。

对非分裂切法，定理17.21给整除支配分裂切法。至少一端的整数比 $M_i/M'_i\ge2$，从而

$$
b(M_i)\ge b(2M'_i)=b(M'_i)+1,
\qquad b(M_{i'})\ge b(M'_{i'}).
\tag{17.77}
$$

总位宽至少下降一位，排除了全部非分裂最优切法。逐坐标单调性则给式(17.76)和一般罚函数结论；常值罚函数在存在非分裂切法时即给其外并列。不同分裂切法的位宽不必相同，下一命题给具体取值。证毕。

**命题 17.31（两种不能交换的取整）。** 取 $H=\{0\}$、$C=\mathbb Z/2\mathbb Z$、$V=(\mathbb Z/n\mathbb Z)^2$ 及 $f(x,y)=\mathbf1_{y=0}$。在 $n=15$ 时，$D=(\mathbb Z/15\mathbb Z)\times\{0\}$、$N=225$，全部分裂计数对恰为

$$
(225,15),\ (75,45),\ (45,75),\ (15,225).
\tag{17.78}
$$

四者乘积均为 $3375$，但两外侧对总位宽为十二，另两对为十三。标准基实现 $(225,15)$，而有序基 $u=(10,6),w=(6,10)$ 实现 $(45,75)$。在 $n=6$ 时，$D=(\mathbb Z/6\mathbb Z)\times\{0\}$、$N=36$，全部分裂计数对是

$$
(36,6),\ (18,12),\ (12,18),\ (6,36),
\qquad B_{\min}=9>\lceil\log_2 216\rceil=8.
\tag{17.79}
$$

因此分裂只固定最优乘积，不固定分别取整的和；即使再对切法取最优，分别取整之和仍不能换成乘积对数的一次取整。

证明。对这两个 $n$，若 $y$ 方向平移非零，模二指标函数之差在 $0$ 处为一，在避开 $0$ 及该平移的负值的某点处为零，故非常值。于是 $D_f=D$ 且 $\chi=0$。定理17.21的逐素数指派分别给出式(17.78)及式(17.79)。模十五所列基的行列式为 $4$，是单位；其第一轴交阶由 $6a=0\pmod{15}$ 得三，第二轴交阶由 $10b=0\pmod{15}$ 得五，故式(17.64)给 $(45,75)$。各位宽依次为 $8+4=12$、$7+6=13$；模六则为 $6+3=9$、$5+4=9$，交换两端不变。由推论17.30可知这些列表上的最小值也是全部切法的最小值。证毕。

### 17.4 非零补偿与真子群原钟的实际局部载体

**命题 17.40（模四分裂切法上的仿射像限制）。** 取 $V=(\mathbb Z/4\mathbb Z)^2$、$C=\mathbb Z/4\mathbb Z$、$H=\{0,2\}$ 及 $f(x,y)=x+y$。则

$$
D_f=V,\qquad \chi(x,y)=x+y,\qquad
D=\{(x,y):x+y\equiv0\pmod2\},\qquad
|D|=8,\quad N=32,\quad |Q_\ell|=4.
\tag{17.80}
$$

标准切法有 $d_A=d_B=2$，局部最小计数为 $(16,16)$，完整钟类匹配有六十四对，实际对仅三十二。切法 $u=(1,1),w=(0,1)$ 有 $d_A=4,d_B=2$，局部最小计数为 $(16,8)$，钟类匹配与实际像均为三十二对；其 $B$ 端实际载体是真子集

$$
W_A^{\mathrm{img}}=(\mathbb Z/4\mathbb Z)^2,
\qquad
W_B^{\mathrm{img}}=\{(b,q)\in(\mathbb Z/4\mathbb Z)^2:q\equiv b\pmod2\}.
\tag{17.81}
$$

证明。$f$ 可加，所以每个方向的差恒为 $x+y$，但只有偶增量能由实际 $H$ 补偿；例如方向 $(1,1)$ 具有非零补偿增量二。完整钟标签可取 $q=\ell=x+y+h$，因为 $\ell$ 的任意未来变化仅由公开输入决定，其核正为 $\Gamma$。标准两轴的可补偿元素都是偶坐标，给所称交阶及计数。标准载体上的 $(x,q)=(0,0)$ 与 $(y,q)=(1,0)$ 各自可达且钟类相同，合起来却要求 $h=-1\notin H$，故为假匹配。

新切法的坐标为 $a=x,b=y-x$，于是 $q=2a+b+h$。第一轴全部四点在 $D$ 中，第二轴只有两个偶点在 $D$ 中，故分裂。固定 $a,q$ 可选 $b=q-2a,h=0$，得到全部十六个 $A$ 状态；固定 $b,q$ 可达当且仅当 $q-b$ 为偶，此时取 $a=0,h=q-b$ 即实现，得到八个 $B$ 状态。双方均从 $(0,0)$ 初始化。公开原坐标输入 $(s,t,k)$ 的更新是

$$
(a,q)\longmapsto(a+s,q+s+t+k),\qquad
(b,q)\longmapsto(b+t-s,q+s+t+k),
\tag{17.82}
$$

全部坐标模四，解码为己方坐标及 $q$。$B$ 载体的差 $q-b$ 增加 $2s+k$，仍为偶，故更新封闭。匹配 $q$ 的两个实际局部状态恢复 $x=a,y=a+b,h=q-2a-b\in H$；该来源唯一。计数亦由定理17.11直接给出。证毕。

### 17.5 不同阶因子的不可分裂障碍

**命题 17.50（$C_8\oplus C_2$ 的嵌入障碍及操作计数）。** 取

$$
V=C_8\oplus C_2,\qquad D_*=\langle(2,1)\rangle,
\qquad C=C_2,\qquad H=\{0\},\qquad f=\mathbf1_{D_*}.
\tag{17.83}
$$

子群嵌入 $C_{p^2}\to C_{p^3}\oplus C_p$ 的包含／投影构造见 [arXiv:2312.01451v2，Remark 1.4(1)](https://arxiv.org/html/2312.01451v2#S1.Thmthm4)；此处 $p=2$ 给 $t\mapsto(2t,t\bmod2)$。对该既有嵌入采用定义17.10的来源、输入和任务，则 $D_f=D=D_*$、$\chi=0$。对全部从有序因子类型 $(C_8,C_2)$ 经自同构得到的合法切法，均有

$$
d_A=2,\quad d_B=1,\quad N=16,\quad |Q_\ell|=4,
\qquad (M_A,M_B)=(16,8),
\qquad |j(S)|=16,\quad |F|=32.
\tag{17.84}
$$

因而没有合法切法使 $D$ 沿轴分裂，最小局部乘积为 $128>N^2/|D|=64$。独立局部二进制位宽是四与三，而保存整个来源只需四位；完整钟类匹配在每个合法切法都容许非实际对。

证明。定义满同态 $\phi(x,y)=x-2y\pmod4$，其核正为 $D_*$。故 $V/D_*\cong C_4$，$f=\mathbf1_{\phi=0}$。在 $C_4$ 上，零点指标函数对任意非零平移的模二差，在零处为一，在避开零及负平移的点处为零，故没有非零恒定差方向。这证明 $D_f=D_*$ 且增量为零；$Q_\ell$ 可用 $q=\phi(x,y)$ 标记，当前钟为 $\ell=\mathbf1_{q=0}$。

任意八阶轴的生成元形为 $u=(r,s)$，其中 $r$ 为奇数、$s\in\{0,1\}$。任意二阶补轴生成元只能是 $w=(4t,1)$，$t\in\{0,1\}$：二阶元素的第一坐标是零或四；第二坐标为零的唯一非零二阶元素 $(4,0)$ 已在每个八阶轴内。反过来，这些 $u,w$ 全部给出直和，因为八阶轴唯一的二阶非零元素为 $(4,0)$，与 $w$ 不同。这列出全部十六个有序生成基；每个八阶轴有四个生成元，每个二阶轴有一个，故恰为四个有序轴对。

$D_*$ 的四阶元素为 $(2,1),(6,1)$；八阶轴的四阶元素均为其生成元的二倍或六倍，第二坐标为零。因此每个合法切法都有

$$
D_*\cap\langle u\rangle=\{(0,0),(4,0)\},\qquad
D_*\cap\langle w\rangle=\{(0,0)\}.
\tag{17.85}
$$

二者阶的乘积为二，小于 $|D_*|=4$。定理17.11对任意有限交换因子适用，给式(17.84)及所述最小值。

还可对每个所列切法直接给出达到构造。唯一写 $(x,y)=au+bw$，其中 $a\in C_8,b\in C_2$，置奇数 $k=r-2s\pmod4$。则

$$
q=ka+2b\pmod4,\qquad \ell=\mathbf1_{q=0}.
\tag{17.86}
$$

$A$ 端保存 $(a,b)\in C_8\times C_2$，$B$ 端保存 $(c,b)\in C_4\times C_2$，$c=a\bmod4$。都从零初始化；当前钟初值为一。公开平移的新坐标为 $(\alpha,\beta)$ 时，更新及解码为

$$
\begin{aligned}
(a,b)&\longmapsto(a+\alpha,b+\beta),
&\operatorname{Decode}_A(a,b)&=(a,\mathbf1_{ka+2b=0}),\\
(c,b)&\longmapsto(c+\alpha\bmod4,b+\beta),
&\operatorname{Decode}_B(c,b)&=(b,\mathbf1_{kc+2b=0}).
\end{aligned}
\tag{17.87}
$$

所有这些局部状态可达，更新只使用自身计数状态与当前公开输入。实际像恰为

$$
\{((a,b),(a\bmod4,b)):a\in C_8,b\in C_2\}.
\tag{17.88}
$$

$A$ 状态 $(0,0)$ 与 $B$ 状态 $(2,1)$ 在每个奇数 $k$ 下都给完整标签 $q=0$，但不在式(17.88)中。每个 $q$ 上有四个 $A$ 状态与两个 $B$ 状态，四个标签共给三十二个匹配对，只有十六个实际对。

此处不能用定理17.20的整数提升步骤推出合法分裂：环境关系格为 $8\mathbb Z\times2\mathbb Z$，一般左幺模变换不保持它；例如换轴把 $(0,2)$ 送到不在该格的 $(2,0)$。于是单独把子群提升格化成 Smith 形，并不保证变换下降为 $C_8\oplus C_2$ 的自同构。对于此类来源，定理17.11的轴分裂充要条件仍成立，而同阶情形的普遍分裂存在性及 Pareto 列表不再由该 Smith 论证给出。证毕。

## 17.99 追加锚

## 17.9 分裂与位宽最优的量词更正

**命题 17.90（推论17.30的量词范围）。** 在定理17.20的每个固定来源及推论17.30的独立定长二进制编码模型下，每个达到最小总位宽的合法切法都沿轴分裂。推论17.30中“但并非每个分裂切法都达到它”这一子句由以下限定陈述替代：分裂并不在所有这类来源中都足以保证位宽最优，但有些来源的所有分裂切法均最优；不能断言每个来源都存在非最优的分裂切法。式(17.76)的最小值公式、式(17.77)的非分裂严格改进及其整除论证、一般单调罚函数结论和命题17.31的全部例子仍成立。

证明。固定任一这样的来源。由定理17.21及推论17.30的整数比论证，每个非分裂切法都有一个分裂切法满足两端 $M_i/M'_i$ 均为正整数，且至少一端的比值不小于二。因此该端 $b(M_i)\ge b(M'_i)+1$，另一端位宽不增，总位宽严格下降；这证明每个最优切法均分裂，并保留式(17.76)。

命题17.31在 $n=15$ 时列出的全部分裂计数对 $(225,15),(75,45),(45,75),(15,225)$，其位宽依次为 $8+4=12$、$7+6=13$、$6+7=13$、$4+8=12$，所以此来源确有非最优分裂切法。该命题在 $n=6$ 时列出的全部分裂计数对 $(36,6),(18,12),(12,18),(6,36)$，其位宽依次为 $6+3=9$、$5+4=9$、$4+5=9$、$3+6=9$；结合式(17.76)，此来源的每个分裂切法都最优。平凡情形也可全部并列：由定理17.21，$D=\{0\}$ 时所有切法的计数对均为 $(N,N)$，$D=V$ 时均为 $(N/n,N/n)$，$n=1$ 时为 $(|H|,|H|)$；这些情形的所有合法切法均分裂，故也均达到各自来源的最小位宽。证毕。

## 17.100 追加锚

## 18. 多端时钟的共同来源、高阶关系与分裂切法

### 18.1 封闭预测器的实际局部像

**定义 18.10（多端坐标任务与完整钟商）。** 设 $R=\mathbb Z/n\mathbb Z$、$V=R^r$，其中 $n\ge1$、$r\ge3$；设 $C=\mathbb Z/m\mathbb Z$、$m\ge1$，$H\le C$，固定已知函数 $f:V\to C$。令

$$
S=V\times H,\qquad N=|S|,\qquad
\ell(x,h)=h+f(x).
\tag{18.1}
$$

沿用定义15.10–15.11的访问条件：共同制备为已知的 $(0,0)$，外部类型只有一个固定值；每个 $(u,v)\in S$ 都是处处合法的平移输入，同时公开给全部 $r$ 端，任意有限输入词及其任意续接均合法。各端从固定状态出发，更新只读自身完整持久状态与当前输入，解码只读自身状态，在空历史及每个有限前缀精确输出。各端无运行时通信；所有可再参与更新或解码的历史、档案、计数器、控制量及位置或钟信息都计入状态，不另给步数、过去输入词或完整钟标签。竞争状态集可无限，可保留任意历史，不要求状态经当前来源 $S$ 因子分解。固定群运算、$f$、更新与解码函数不随执行变化。

合法切法是 $L\in GL_r(R)$，令 $\lambda_i(x)=(Lx)_i$。此切法指定第 $i$ 端输出 $(\lambda_i(x),\ell(x,h))$，原钟 $h$ 不是额外的局部输出。对历史 $w$，记累积来源为 $z(w)$、局部状态为 $\sigma_i(w)$；实际同源联合像记为

$$
J=\{(\sigma_1(w),\ldots,\sigma_r(w)):w\in S^*\}.
\tag{18.2}
$$

它要求一个共同历史，不是分别选取各端可达状态的笛卡尔积。依定理15.12的恒定差与补偿图，取

$$
\begin{gathered}
D=\{d\in V:\ f(x+d)-f(x)=\chi(d)\in H
                  \text{ 对全部 }x\in V\text{ 成立}\},
\qquad \chi(d)=f(d)-f(0),\\
\Gamma=\{(d,-\chi(d)):d\in D\},\qquad
Q_{\mathrm{clock}}=S/\Gamma,\qquad
q_0=|Q_{\mathrm{clock}}|=N/|D|,\\
D_L=LD,\qquad
K_i=\{(d,-\chi(d)):d\in D\cap\ker\lambda_i\}.
\end{gathered}
\tag{18.3}
$$

这里 $D$ 是子群、$\chi:D\to H$ 是同态，$\Gamma$ 为其负图；$Q_{\mathrm{clock}}$ 专指完整钟未来商，与实际联合像 $J$ 不同。其类记为 $q=[(x,h)]_\Gamma$，并令 $\bar\ell(q)=h+f(x)$；补偿关系保证该函数良定义。对 $I\subseteq\{1,\ldots,r\}$，$\pi_I$ 表示空间坐标投影，$\pi_i=\pi_{\{i\}}$。

**定理 18.11（多端最小状态与实际载体）。** 在定义18.10下，第 $i$ 端的最小可达状态数及实际联合像的最小大小为

$$
M_i(L)=q_0\,|\lambda_i(D)|=q_0\,|\pi_iD_L|,
\qquad \min|J|=N.
\tag{18.4}
$$

它们可同时达到。规范局部载体有如下两种同构表示：

$$
W_i^0=S/K_i\ \cong\
\{(\lambda_i(x),[(x,h)]_\Gamma):(x,h)\in S\}
\subseteq R\times Q_{\mathrm{clock}}.
\tag{18.5}
$$

给定 $q$ 的任一代表 $(x_q,h_q)$，它的实际纤维恰为

$$
\{(b_i,q):b_i\in\lambda_i(x_q)+\lambda_i(D)\}.
\tag{18.6}
$$

任一达到 $M_i(L)$ 的实现，其可达部分均经保持初始化、更新和输出的双射同构于 $W_i^0$。这些最小值下界适用于任意历史竞争实现。

证明。定理15.12的未来商及历史摘要满射论证在此只需把两端换为 $r$ 端。两来源差为 $(d,k)$ 时，共同空间续接 $u$ 后的钟差是 $k+f(x+u+d)-f(x+u)$；$u$ 遍历 $V$，故全部未来钟差为零恰好要求 $(d,k)\in\Gamma$。再要求己方坐标一致，恰加上 $\lambda_i(d)=0$，给出核 $K_i$。

对任何竞争实现，若两个历史到达同一完整局部状态，确定性续接及精确解码使其全部未来输出相同。因此 $\sigma_i(w)\mapsto z(w)+K_i$ 良定义；每个来源都可达，故该映射满射。沿用定理15.12式(15.40)–(15.41)的构造，以 $S/K_i$ 为状态、公开平移为更新、代表元的指定输出为解码即达到下界。由 $|K_i|=|D|/|\lambda_i(D)|$ 得式(18.4)的局部计数；达到这个有限计数时满射必为双射，且按构造与更新、输出交换。

两个来源在式(18.5)的成对表示中相等恰为其差属于 $K_i$，而标签 $q$ 的全部来源是 $(x_q,h_q)+\Gamma$，故得到实际纤维。该表示的更新为 $(b_i,q)\mapsto(b_i+\lambda_i(u),q+[(u,v)]_\Gamma)$，解码为 $(b_i,\bar\ell(q))$；标签包含在所计状态内，初始钟输出为 $f(0)$。

全部 $K_i$ 的交为零，因为 $L$ 可逆使 $\lambda_i(d)=0$ 对全部 $i$ 成立时必有 $d=0$，继而 $k=-\chi(0)=0$。规范联合像因而与 $S$ 双射。任意竞争实现的实际同历史元组经上述各端满射一起映到该规范像，并满射到它，故联合下界为 $N$。亦可由全部当前输出取回 $b=Lx$ 与 $\ell$，再取 $x=L^{-1}b$、$h=\ell-f(x)$。证毕。

### 18.2 指定来源的投影与共同标签胶合

**定理 18.20（完整元组及子元组的同源判据）。** 对定理18.11的规范载体，或经其商同构识别后的各端最小可达实现，设局部状态为 $(b_i,q_i)$。完整元组属于实际联合像 $J$ 当且仅当

$$
q_1=\cdots=q_r=q,\qquad b-Lx_q\in D_L,
\qquad b=(b_1,\ldots,b_r).
\tag{18.7}
$$

此时其唯一来源为

$$
d=L^{-1}(b-Lx_q),\qquad
x=x_q+d,\qquad h=h_q-\chi(d).
\tag{18.8}
$$

对非空 $I\subseteq\{1,\ldots,r\}$，子元组属于同一指定 $J$ 的实际投影 $J_I$，当且仅当所含标签相等于某个 $q$，且

$$
b_I-(Lx_q)_I\in\pi_ID_L,
\qquad |J_I|=q_0\,|\pi_ID_L|.
\tag{18.9}
$$

证明。固定 $q$ 的实际来源恰为 $(x_q+d,h_q-\chi(d))$，$d\in D$；其全部空间读数为仿射陪集 $Lx_q+D_L$，对子集投影即得式(18.9)。指定全部 $b$ 后，$L$ 可逆给唯一 $d$，继而给唯一 $h$。换代表元为 $(x_q+e,h_q-\chi(e))$ 只把偏移减去 $Le\in D_L$；新参数为 $d-e$，故条件及重建来源均不变。不同 $q$ 的子元组因非空标签位置而不重合，逐标签计数得到所列大小。每个构造出的来源均从零制备可达。

这里恢复的是一个指定的实际关系 $J$。不同 $I$ 的投影成员资格各自允许一个来源见证，不能把这些存在量词直接换成同一个见证。所用投影连接含义是标准的 natural join 与 join dependency：一个关系等于它的若干投影之连接，见 Beeri–Fagin–Maier–Yannakakis，*On the Desirability of Acyclic Database Schemes*，JACM 30(3)（1983），§2，印刷页481，[DOI](https://doi.org/10.1145/2402.322389)。该文印刷页485的 global consistency 要求存在某个通用关系，Theorem 3.4（印刷页488）的无环条件针对这种存在性；它不能替代式(18.7)对指定 $J$ 的恢复证明。

对保留冗余历史的一般竞争实现，局部商映射仍给出必要条件及定理18.11的下界，但通过商条件不保证给定原始状态元组可由同一历史达到。上述原始元组的充要胶合只用于规范载体或逐端最小实现。另一方面，已知完整初始化和同步更新时，可以直接由共同历史确定真实同步可达关系；投影条件的不足并不等于在所有信息接口下都不能确定 $J$。证毕。

**定理 18.21（共同钟类上的高阶检验与字符支撑）。** 对定义18.10的固定切法及 $1\le k\le r$，令

$$
B_k(D_L)=\bigcap_{|I|=k}\pi_I^{-1}(\pi_ID_L).
\tag{18.10}
$$

以下接受计数与完备性均限制在 $q_1=\cdots=q_r=q$ 的候选元组上。该元组的全部 $k$ 端实际投影检验均通过，当且仅当 $b-Lx_q\in B_k(D_L)$。在所有共同标签上，接受元组数、实际元组数及检验完备条件分别为

$$
\#\mathrm{Acc}_k=q_0|B_k(D_L)|,\qquad
|J|=q_0|D_L|=N,\qquad
\mathrm{Acc}_k=J\ \Longleftrightarrow\ B_k(D_L)=D_L.
\tag{18.11}
$$

子群满足 $D_L=B_r(D_L)\subseteq B_{k+1}(D_L)\subseteq B_k(D_L)$。通过检验后尚未排除的支撑关系由

$$
[b-Lx_q]\in B_k(D_L)/D_L
\tag{18.12}
$$

表示，零类恰为实际同源。此类不依赖代表元。对 $k\ge2$，全部实际 $k$ 端检验已强制所有标签相同；$k=1$ 的检验本身不强制这一点。

在 $V=R^r$ 上以完美配对

$$
\langle c,a\rangle_n
=\exp\!\left(\frac{2\pi\mathrm i}{n}\sum_{j=1}^r c_ja_j\right)
\tag{18.13}
$$

识别字符，令 $D_L^\perp=\{c:\langle c,d\rangle_n=1\text{ 对全部 }d\in D_L\}$，并令 $\mathcal K_k$ 为其中支撑大小至多 $k$ 的字符所生成的子群。$\mathcal K_k$ 是字符子群，与局部状态核 $K_i\le S$ 不同。则本共同标签检验还有等价表述

$$
B_k(D_L)=\mathcal K_k^\perp,
\qquad
\mathrm{Acc}_k=J\ \Longleftrightarrow\
\mathcal K_k=D_L^\perp.
\tag{18.14}
$$

这些结论对合数 $n$ 及 $n=1$ 均成立。

证明。式(18.9)逐个用于所有 $|I|=k$ 即得接受条件。每个坐标都属于某个这样的 $I$，所以接受偏移自动满足实际单端纤维条件。给定 $q$ 后，$b\leftrightarrow b-Lx_q$ 是双射，故接受数为 $|B_k|$，再乘 $q_0$。任一较小子集可扩张到大小 $k$，给出较小阶检验及所列嵌套；$k=r$ 时就是完整空间条件。由于 $D_L\le B_k$，零商类恰为 $D_L$，换代表元又只减去 $D_L$ 中元素。对 $k\ge2$，任意两端都能包含在同一个大小 $k$ 的子集中；该实际子元组的标签必相等，从而全部标签相同。单元素子集没有这种约束。

字符步骤使用标准有限交换群事实：子群字符可延拓，非零元素可由字符分离，字符群与原群同阶，见 Keith Conrad，[*Characters of Finite Abelian Groups*](https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf)，Theorems 3.3、3.5及 Corollary 3.7。具体地，式(18.13)给出的字符由标准坐标取值唯一确定；若 $c\ne0$，选一个非零坐标并与其单位向量配对即可分离，故这 $n^r$ 个字符是全部字符。对任意子群 $A\le V$，若 $a\notin A$，对 $V/A$ 使用字符分离再拉回，得到一个消灭 $A$ 却不消灭 $a$ 的字符。这证明 $A^{\perp\perp}=A$，无需域假设；$n=1$ 时各群平凡，结论直接成立。

对固定 $I$，空间 $\pi_I^{-1}(\pi_ID_L)$ 的消灭字符恰是支撑包含于 $I$ 的 $D_L^\perp$ 元素：空间包含全部 $I$ 外坐标方向，故字符必须在这些坐标为零；其余条件正是消灭 $\pi_ID_L$。由双重消灭，空间本身是这些字符共同的核。取所有 $I$ 的交，就是取这些字符生成群的消灭空间。每个支撑至多 $k$ 的字符均包含于某个大小 $k$ 的 $I$，故得到式(18.14)，再取双重消灭即得完备性等价。这是有限字符支撑在本来源检验中的应用。

商 $B_k(D_L)/D_L$ 在这里仅描述集合支撑上未检出的关系；未指定验证器访问、通信协议、状态更新合同或概率律，故它的阶本身不定义最小验证器记忆、通信代价、熵或概率律的恢复定理。证毕。

**命题 18.22（单端检验的标签端点）。** 取 $n=1$、$r\ge3$、$C=H=\mathbb Z/2\mathbb Z$、$f=0$。则 $D=V=\{0\}$、$\Gamma=\{0\}$、$Q_{\mathrm{clock}}\cong C_2$、$B_1(D)=D$。每端的两个状态 $(0,0)$、$(0,1)$ 均可达，但同时含两种标签的完整元组没有共同来源。全部单端检验接受 $2^r$ 个原始元组，限制到共同标签后仅有两个，且恰为实际元组。

证明。空间群平凡，来源仅为原钟 $h$，规范状态为 $(0,h)$。两个 $h$ 均可从零达到；同一来源在全部端给相同标签。分别的单端可达性不约束端间标签，故有 $2^r$ 种组合，共同标签只留下全零与全一。证毕。

### 18.3 每个真子集均可实现的补偿时钟

**命题 18.30（全阶约束隐藏于所有真投影）。** 对每个 $r\ge3$，取 $R=C_4$、$V=R^r$、$C=H=C_2$，并取恒等切法，令

$$
j(x)=\sum_{i=1}^r x_i\pmod4,\qquad
f(x)=g(j(x)),\qquad (g(0),g(1),g(2),g(3))=(0,0,1,1).
\tag{18.15}
$$

这是命题15.16的两轴高位校准在 $r$ 轴总和上的应用。其补偿群、非零补偿同态及完整钟类为

$$
\begin{gathered}
D=\{d:j(d)\equiv0\pmod2\},\qquad
\chi(d)=\frac{j(d)}2\pmod2,\qquad |D|=4^r/2,\\
Q_{\mathrm{clock}}\cong C_4,\qquad
t(x,h)=j(x)+2h\pmod4,\qquad q_0=4.
\end{gathered}
\tag{18.16}
$$

这里在 $\chi$ 中取 $j(d)\in\{0,2\}$。每端的实际载体是全部十六个 $(x_i,t)\in C_4^2$，初态为 $(0,0)$，公开 $(u,v)\in C_4^r\times C_2$ 的更新及解码为

$$
(x_i,t)\longmapsto
\left(x_i+u_i,\ t+\sum_{j=1}^r u_j+2v\right)\pmod4,
\qquad \mathrm{Decode}_i(x_i,t)=(x_i,g(t)).
\tag{18.17}
$$

实际完整关系恰为

$$
t_1=\cdots=t_r=t,\qquad
\sum_{i=1}^r x_i\equiv t\pmod2.
\tag{18.18}
$$

它唯一恢复原钟：$h$ 是 $C_2$ 中满足 $2h=t-j(x)$ 于 $C_4$ 的唯一元素。每个非空真子集的实际关系却允许共同 $t$ 下的全部坐标选择。因此，对每个 $k<r$，

$$
B_k(D)=V,\qquad B_k(D)/D\cong C_2,\qquad
D^\perp=\{0,(2,\ldots,2)\}.
\tag{18.19}
$$

全部共同标签元组数为 $4^{r+1}$，实际数为 $2\cdot4^r$；特别地 $r=3$ 时分别为 $256$ 与 $128$，$r=4$ 时分别为 $1024$ 与 $512$。

证明。命题15.16计算的 $g$ 平移差只有零和二是常值，分别为零和一；$j$ 满射，所以恒定差方向正是偶总和方向，且 $\chi(2e_1)=1$。同态 $t:S\to C_4$ 满射，核为 $\Gamma$，故给出完整钟商。恒等式 $g(j+2h)=g(j)+h$ 给解码，来源平移给式(18.17)，全程只用本端状态和当前公开输入。

更一般地，给非空真子集 $I$、任意 $x_I$ 与 $t$，选一个缺失坐标 $a\notin I$，令其余缺失坐标为零，并取

$$
x_a=t-\sum_{i\in I}x_i\pmod4,\qquad h=0.
\tag{18.20}
$$

此实际来源总和为 $t$，从而实现所给子元组；单元素 $I$ 同时证明十六态局部载体全部可达。固定全部坐标后，方程 $2h=t-j(x)$ 可解恰为差是偶数，且 $C_2\to C_4$ 的 $h\mapsto2h$ 单射，证明式(18.18)及唯一恢复。定理18.11遂给每端最小值 $16$ 及联合最小值 $2\cdot4^r$。

例如 $r=3$ 时，$((1,0),(0,0),(0,0))$ 的三对分别由来源 $(x,h)=((1,0,1),1)$、$((1,1,0),1)$、$((0,0,0),0)$ 实现，对应端集依次为 $\{1,2\}$、$\{1,3\}$、$\{2,3\}$。它们都有 $t=0$，但完整元组要求 $1+2h=0\pmod4$，无解。各对的来源见证不同，不能合并为一段历史。任意 $r\ge3$ 的 $x=(1,0,\ldots,0)$、$t=0$ 给同样的完整障碍，式(18.20)仍实现其每个真子集。

每个真投影 $\pi_ID$ 是整个 $R^I$，因为可用一个缺失坐标修正总和的奇偶；故 $B_k=V$，商为总和奇偶给出的 $C_2$。$D$ 在 $V$ 中指数为二，其消灭群也有二元，非零字符 $(2,\ldots,2)$ 正是总和奇偶字符，支撑为全部 $r$ 端。每个 $t$ 下有 $4^r$ 种坐标组合，其中一半满足式(18.18)，给出全部计数。证毕。

### 18.4 局部乘积的最小值与缺失关系

**定理 18.40（分裂切法与共同标签的多余组合）。** 在定义18.10的全部合法切法中，记各端最小状态数之积为 $P(L)$。则

$$
P(L)=q_0^r\prod_{i=1}^r|\pi_iD_L|,\qquad
\min_LP(L)=q_0^r|D|=Nq_0^{r-1}.
\tag{18.21}
$$

达到最小值恰好要求坐标分裂 $D_L=\prod_i\pi_iD_L$，亦恰好要求实际局部载体仅凭完整钟标签一致即可精确胶合。任意切法的乘积超额与未检出的共同标签组合有同一个精确比值：

$$
\frac{P(L)}{\min_{L'}P(L')}
=\frac{|B_1(D_L)|}{|D_L|}
=|B_1(D_L)/D_L|
=\frac{\#\mathrm{Acc}_1}{|J|},
\tag{18.22}
$$

其中 $\mathrm{Acc}_1$ 始终限于共同 $Q_{\mathrm{clock}}$ 标签。各端重复保存的标签仍分别计费。

证明。定理18.11给出乘积式。因 $D_L\subseteq\prod_i\pi_iD_L=B_1(D_L)$，有限集合的阶给下界 $q_0^r|D|$，且取等恰为两个集合相等。分裂存在性只需主卷 [axiom 54.1](RECURSIVE_RELATIONAL_OBSERVATION.md) 的整数 Smith 标准形，沿用定理17.20所引 Elman，*Lectures on Abstract Algebra*，Appendix D，[Theorem D.2](https://www.math.ucla.edu/~rse/algebra_book.pdf#page=862) 作为中间工具：当 $n>1$ 时令

$$
\widetilde D=\{a\in\mathbb Z^r:a\bmod n\in D\},\qquad
n\mathbb Z^r\subseteq\widetilde D.
\tag{18.23}
$$

用 $D$ 的整数代表和 $ne_1,\ldots,ne_r$ 生成这个满秩格。Smith 标准形给左幺模矩阵 $U$，使 $U\widetilde D=\bigoplus_i s_i\mathbb Ze_i$，其中 $s_i>0$。右幺模变换只换生成元；关键是左变换满足 $U(n\mathbb Z^r)=n\mathbb Z^r$。于是各 $s_i\mid n$，$U$ 模 $n$ 是合法的 $GL_r(R)$ 元素，并把 $D$ 送到 $\prod_i(s_i\mathbb Z/n\mathbb Z)$。这给达到下界的切法；$n=1$ 时空间平凡，直接达到。由式(18.11)的共同标签计数和 $B_1=\prod_i\pi_iD_L$，得到式(18.22)及胶合等价。

这里优化的任务随 $L$ 改变。若只被动重写为 $y=Lx$，同时把原任务运输为 $((L^{-1}y)_i,h+f(L^{-1}y))$，则来源与公共输入的可逆重标记在两方向运输每个竞争实现，不改变任何可达状态计数或最小值。本定理要求的新己方输出是 $y_i$，不由该被动运输取得，也不保证可从旧的最小局部状态直接算出。证毕。

**推论 18.41（进位例的总和切法）。** 对命题18.30，合法切法

$$
y_1=\sum_{i=1}^r x_i\pmod4,\qquad y_i=x_i\quad(2\le i\le r)
\tag{18.24}
$$

给出 $D_L=2C_4\times C_4^{r-1}$，同时最小局部计数为 $(8,16,\ldots,16)$。在实际局部载体内，共同标签已足以精确胶合；乘积为 $8\cdot16^{r-1}$，达到式(18.21)。若各端分别以定长二进制存储完整状态，该切法较原坐标任务共节省一位，并在这个例子中达到最小总位宽。

证明。逆变换为 $x_i=y_i$（$i\ge2$）、$x_1=y_1-\sum_{i\ge2}y_i$，故切法合法；$D$ 的偶总和条件恰为 $y_1$ 偶。完整标签仍为 $t=y_1+2h$，第一个实际载体是 $\{(y_1,t):y_1\equiv t\pmod2\}$，含八态；其余端仍各有十六态。任取这些载体内具有共同 $t$ 的元组，第一端已保证 $t-y_1$ 偶，唯一 $h$ 再连同全部 $y$ 恢复来源。更新由式(18.17)把第一坐标增量换成 $\sum_i u_i$ 得到。

原任务的局部计数均为 $16$，总位宽为 $4r$；新计数全是二的幂，总位宽为 $3+4(r-1)=4r-1$。任意切法与精确实现的总位宽至少为 $\log_2\prod_iM_i(L)\ge\log_2\min_LP(L)=4r-1$，故此例达到该下界。此计算只使用本例的二幂计数，不把一般乘积最优等同于取整位宽最优。

新第一端任务也确实不能总由旧第一端最小状态计算：来源 $(x,h)=((0,\ldots,0),0)$ 与 $((0,2,0,\ldots,0),1)$ 在旧第一端都给 $(x_1,t)=(0,0)$，而新输出 $y_1$ 分别为零与二。故节省比较的是重新指定并从零运行的局部任务，而非对旧局部记忆作被动坐标改写。证毕。

## 18.99 追加锚

## 19. 最小闭状态之间的同时切法转换

**定义 19.1（来源、旧任务与和坐标任务）。** 记 $C_k=\mathbb Z/k\mathbb Z$，$[a]_k$ 为模 $k$ 的标准非负代表。固定 $r\ge2$，取

$$
S=C_4^r\times C_2,\qquad
Y=\sum_{i=1}^r x_i\in C_4,\qquad
t=Y+2h\in C_4,\qquad
\ell=g(Y)+h=g(t)\in C_2,
\quad (g(0),g(1),g(2),g(3))=(0,0,1,1).
\tag{19.1}
$$

共同初态为已知的 $(x,h)=(0,0)$，全部平移 $(u,v)\in C_4^r\times C_2$ 都公开、处处合法，作用为 $(x,h)\mapsto(x+u,h+v)$，故每个来源可达。沿用定义15.10–15.11及定义18.10的完整持久状态计数和局部更新约定。旧第 $i$ 端输出 $(x_i,\ell)$；改变任务后，第一个端口输出 $(Y,\ell)$，其余端口仍输出 $(x_i,\ell)$。

以下直接使用定理15.12的未来行为商最小性和命题15.16的高位校准；$r\ge3$ 的旧载体与同源关系已由命题18.30给出。完整钟标签是 $t$：四个未来响应行 $(g(t+d))_{d=0}^3$ 分别为 $0011,0110,1100,1001$。己方位置或 $Y$ 又是当前输出，故旧任务与新第一端任务的完整未来标签分别为

$$
L_i=(x_i,t)\in C_4^2,\qquad
L'_1=(Y,t)\in W'_1:=\{(y,t)\in C_4^2:y\equiv t\pmod2\}.
\tag{19.2}
$$

这些标签在公共平移下闭合。任给 $(x_i,t)=(a,b)$，在另一个坐标放置 $b-a$ 并取 $h=0$，得到全部十六个旧标签；任给等奇偶的 $(y,t)$，取 $x_1=y$、其余坐标为零及 $h=[t-y]_4/2$，得到全部八个新标签。因此上述既有最小性结论给旧端最小可达状态数 $16$、新第一端最小可达状态数 $8$，亦涵盖 $r=2$。取最小旧实现时，可通过其到未来行为商的典范同构将状态识别为 $L_i$；此识别不增加历史信息。

旧状态的实际同源联合关系及其逆中的原钟为

$$
\mathcal J_{\rm old}
=\left\{((x_1,t),\ldots,(x_r,t)):\sum_i x_i\equiv t\pmod2\right\},
\qquad h=\frac{[t-\sum_i x_i]_4}{2}.
\tag{19.3}
$$

故 $|\mathcal J_{\rm old}|=|S|=2\cdot4^r$，联合固定二进制位宽为 $2r+1$。各端分别保存其最小状态的总位宽则为 $4r$；改变任务后相应总位宽为 $3+4(r-1)=4r-1$。这里联合计数使用实际关系，不使用局部载体的笛卡尔积。

**定义 19.2（压缩后快照的同时转换契约）。** 旧任务先运行并压缩到定义19.1的最小旧状态，任务改变请求在任意可达快照到达。转换只使用这些旧状态：第 $i\ge2$ 端同时发送一条确定性消息

$$
e_i(x_i,t)\in A_i,\qquad
b_i=\lceil\log_2|A_i|\rceil,\qquad
\Phi(x,h)=\bigl(x_1,t,e_2(x_2,t),\ldots,e_r(x_r,t)\bigr).
\tag{19.4}
$$

非空有限字母表 $A_i$、编码映射与固定包宽 $b_i$ 事先选定，其容量不随 $t$ 变化。第一端仅见自身 $(x_1,t)$ 与全部消息，必须对每个 $(x,h)\in S$ 确定性地精确恢复 $Y$。发送者之间无通信，第一端无反馈。旧公共输入词、额外保留的控制资料、刚消费的输入、依赖来源的请求触发、时序、沉默、未来探测及额外知晓来源的发送者均不是转换的可用输入或信道。固定函数与群运算不携带执行相关资料。

这个求值问题有直接的经典来源。固定共同已知的 $t$，作局部代换

$$
z_1=x_1-t\pmod4,\qquad z_i=x_i\ (i\ge2),\qquad
\sum_i z_i\equiv0\pmod2,\qquad
F(z)=\frac{[\sum_i z_i]_4}{2}=h,\qquad Y=t+2F(z)\pmod4.
\tag{19.5}
$$

确有 $\sum_i z_i=Y-t=-2h=2h$ 于 $C_4$，而每个偶和 $z$ 都由 $x_1=z_1+t$、$x_i=z_i$、$h=F(z)$ 对应到一个实际来源。三方的偶和承诺及此布尔函数见 Buhrman、Cleve、van Dam，*Quantum Entanglement and Communication Complexity*，[quant-ph/9705033v1](https://arxiv.org/pdf/quant-ph/9705033v1)，PDF第3页§2式(1)–(4)。其通信接口为广播，且所有参与者都须学得答案；该文的四位结论不能充作本单接收端契约的四位下界。Buhrman、van Dam、Høyer、Tapp，*Multiparty Quantum Communication Complexity*，[quant-ph/9710054v2](https://arxiv.org/pdf/quant-ph/9710054v2)，PDF第2页§2称此问题为 Modulo-4 Sum，第4–5页§3式(4)–(5)的多方族在参数 $n=2$ 时正是式(19.5)。该文相应渐近下界要求 $n\ge\log_2 r$，不能覆盖固定 $n=2$ 的任意 $r$。以下刻画的是此既有承诺函数在式(19.4)的发送者乘积限制下的精确恢复条件，并将它接到式(19.2)的闭动态边界最小值。

**定理 19.3（发送者乘积条件、和恢复与来源恢复等价）。** 在定义19.2的完整契约下，记 $e_{i,t}(a)=e_i(a,t)$。下列三项等价：

1. 存在解码函数，对全部 $(x,h)\in S$ 从 $\Phi(x,h)$ 精确恢复 $Y$。
2. 对每个 $t\in C_4$，每个发送者都满足 $e_{i,t}(0)\ne e_{i,t}(2)$、$e_{i,t}(1)\ne e_{i,t}(3)$，且至多一个 $e_{i,t}$ 非单射。
3. $\Phi:S\to C_4^2\times\prod_{i=2}^r A_i$ 在 $S$ 上单射。

因此来源由接收端旧状态与消息元组共同决定；这里的单射不要求消息元组独自确定来源，也不要求解码运算实际存出所有来源坐标。

证明。先设第一项成立，并固定 $t$。若某发送者 $j$ 将同奇偶的 $a,a+2$ 合并，令其他发送者坐标为零，选同一个 $x_1\in\{0,1\}$ 满足 $x_1+a\equiv t\pmod2$，再取唯一的 $h$ 使钟标签为 $t$。把 $x_j$ 加二并把 $h$ 加一，得到另一个实际来源；其 $t$、$x_1$ 及全部消息不变，而 $Y$ 相差二，矛盾。

于是每次碰撞都在异奇偶值之间。若不同发送者 $j,k$ 都非单射，各取一对碰撞值。$C_4$ 中任一异奇偶无序对都能定向为 $a\to a+1$；将两对分别写为 $a\to a+1$、$c\to c+1$。令其他发送者坐标为零，选一个共同的 $x_1\in\{0,1\}$ 满足 $x_1+a+c\equiv t\pmod2$，并取使初始来源具有标签 $t$ 的 $h$。同时作这两个加一变化，再将 $h$ 加一，便使 $Y$ 加二而保持 $t$。两个来源均实际可达，接收端状态及全部消息完全相同，再次矛盾。这同时使用了一个共同来源约束和同一个接收端值；对所有接收端值精确的要求保证所选 $x_1$ 属于适用范围。第一项遂蕴含第二项。

若第二项成立，固定实际观测中的 $t$。所有发送映射都单射时，逐个反演即可恢复 $x$。否则唯一例外的下标 $j=j(t)$ 由既定映射和已知 $t$ 决定。反演其余发送者后，令

$$
a=x_1+\sum_{i\ne1,j}x_i\pmod4,\qquad
B_j=e_{j,t}^{-1}(m_j),\qquad
x_j\equiv t-a\pmod2.
\tag{19.6}
$$

同奇偶分离保证 $B_j$ 中每种奇偶至多一个值，实际来源保证所需奇偶的值存在，故 $x_j$ 唯一。随后 $Y=a+x_j$，且 $h=[t-Y]_4/2$ 唯一，证明第三项。第三项允许在实际像上反演来源并求和，像外输入可任意解码，故蕴含第一项。证毕。

**推论 19.4（固定包宽的精确代价及达到）。** 定义19.2的最小总传输位数为 $2r-3$；若允许额外的集中式发送者使用任意来源函数提供修复标签，则其最小位数为一。因此严格的分布式与集中式差距从 $r=3$ 开始，$r=2$ 时两者均为一位。达到 $2r-3$ 的全局字母表容量，按一个固定发送者置换，恰为 $(2,4,\ldots,4)$。

证明。每个固定接收端状态 $(x_1,t)$ 的来源纤维恰有

$$
\left|\{(x,h)\in S:L_1(x,h)=(x_1,t)\}\right|
=\frac{4^{r-1}}2=2^{2r-3}.
\tag{19.7}
$$

其余 $r-1$ 个坐标只受一个奇偶等式约束，且每组坐标确定唯一的 $h$。定理19.3迫使这些来源具有互异消息元组，所以

$$
2^{\sum_{i=2}^r b_i}\ \ge\ \prod_{i=2}^r|A_i|
\ \ge\ 2^{2r-3},\qquad \sum_{i=2}^r b_i\ge2r-3.
\tag{19.8}
$$

取一个固定发送者 $j\ge2$ 只发 $q_j=g(x_j)=[x_j]_4\mathbin{\mathrm{div}}2$，其余 $r-2$ 个发送者各发完整 $x_i$。接收端计算

$$
a=x_1+\sum_{i\ne1,j}x_i\pmod4,\qquad
\lambda=[t-a]_2,\qquad
\widehat x_j=2q_j+\lambda,\qquad
\widehat Y=a+\widehat x_j\pmod4.
\tag{19.9}
$$

实际奇偶关系给 $\lambda=[x_j]_2$，故恢复精确，总宽为 $2(r-2)+1=2r-3$；$r=2$ 时该和为空。这里使用已有的完整输入加高位构造：上述 Buhrman、van Dam、Høyer、Tapp 文的 PDF第3页§2.1让 Bob 发完整输入、Carol 发高位，再由 Alice 广播答案。本式保留其奇偶恢复步骤并用于任意 $r$ 的单接收端同时消息，省去答案广播；该文§2.2的后发 Carol 可依赖 Bob 的消息，也不能直接替代定理19.3的发送映射条件。

每个发送者都至少需两个符号。若两个全局容量小于四，则它们在每个 $t$ 都非单射，违反定理19.3；故至少 $r-2$ 个包各需两位。总宽取等号时，恰有一个固定发送者宽为一、容量为二，其余宽为二且容量至少四，因而容量恰为四。这证明固定置换的容量结论。三个符号的例外编码同样允许，例如只合并 $0,1$ 而将 $2,3$ 分开，但其包宽为两位。非最小协议也可随 $t$ 改变例外发送者；任何在某个 $t$ 上单射的发送者仍需全局容量至少四，不能按各 $t$ 分别选取最便宜的包宽。

最后，每个接收端纤维中的 $Y$ 都有已知奇偶 $[t]_2$，恰有两个可能值：对任一来源作 $x_2\mapsto x_2+2$、$h\mapsto h+1$，保持接收端状态而交换这两个值。集中式一位标签 $g(Y)$ 连同该奇偶即可确定 $Y$，零位则不能。此标签允许读取整个来源，通常不是合法的发送者局部函数；故其一位最优值不抵消式(19.8)。证毕。

**命题 19.5（转换后的闭更新与最小旧记忆前提）。** 转换后第一端只保存 $(Y,t)$，其余端继续保存 $(x_i,t)$，即可精确执行改变后的全部未来任务。分别持久存储的总宽由 $4r$ 降到 $4r-1$，实际联合状态的来源位宽仍为 $2r+1$。若任务在制备前已选定，转换消息可为零；若允许旧第一端预先保存 $(x_1,Y,t)$，其可达状态数为 $32$，也可在请求时零消息转换。因此推论19.4限定于最小旧状态，不构成任意旧实现之间的记忆与通信前沿。

证明。对当前公共平移令 $d=\sum_i u_i\pmod4$。局部更新为

$$
(Y,t)\longmapsto(Y+d,t+d+2v),\qquad
(x_i,t)\longmapsto(x_i+u_i,t+d+2v)\quad(i\ge2).
\tag{19.10}
$$

它们由来源平移直接诱导，解码分别为 $(Y,g(t))$、$(x_i,g(t))$。从转换后的正确状态归纳，任意未来词下都正确。联合状态又由

$$
x_1=Y-\sum_{i\ge2}x_i\pmod4,\qquad h=\frac{[t-Y]_4}{2}
\tag{19.11}
$$

恢复来源，故联合实际像仍有 $2\cdot4^r$ 个元素。局部最小宽度由式(19.2)给出。这里改变的是所要求的第一端输出；把旧任务被动写成和坐标仍要求 $x_1=Y-\sum_{i\ge2}x_i$，与新任务不同。这正承接命题15.14的固定任务运输边界及推论18.41的总和切法比较。

若预先选定新任务，从 $(Y,t)=(0,0)$ 直接用式(19.10)即可。对另一种旧实现，第一端保存 $(x_1,Y,t)$：任意 $x_1,Y\in C_4$ 及与 $Y$ 同奇偶的 $t$ 均可实现，取 $x_2=Y-x_1$、其他坐标为零并选唯一 $h$ 即可，故有 $4\cdot4\cdot2=32$ 态。其闭更新为 $(x_1,Y,t)\mapsto(x_1+u_1,Y+d,t+d+2v)$，可输出旧任务，且请求时直接投影到 $(Y,t)$。这些结论分别计量一次传输和后续持久状态，不给出转换期间工作空间的最小值，也不定义二者之间的兑换或回本关系。证毕。

**命题 19.6（限制快照承诺会破坏来源恢复结论）。** 取 $r=3$，若将转换的来源承诺限制为 $x_1=1,t=0$，两发送者各只发 $q_i=g(x_i)$ 就能恢复 $Y$，但接收端旧状态与消息不能恢复来源。同一编码不满足定义19.2的全部来源精确性。

证明。写 $x_i=2q_i+\lambda_i$，$\lambda_i\in\{0,1\}$。受限来源满足 $1+\lambda_2+\lambda_3\equiv0\pmod2$，所以整数和 $\lambda_2+\lambda_3=1$，并有

$$
Y=2+2(q_2+q_3)\pmod4.
\tag{19.12}
$$

但来源 $((1,0,1),1)$ 与 $((1,1,0),1)$ 都满足承诺，并有相同接收端状态及两个零高位，来源却不同。放回全部来源，$((0,0,0),0)$ 与 $((0,1,1),1)$ 都有接收端状态 $(0,0)$ 及两个零消息，而 $Y$ 分别为零和二，故相同编码失败。这里改变的是转换时的快照支持；只限制制备而仍允许随后全部平移，任何非空制备都仍可到达 $S$ 中每一点，不能产生这个受限快照承诺。证毕。

## 19.99 追加锚

## 20. 三端补偿钟的一位公共反馈分类与闭边界

**定义 20.1（先反馈、后同时回复的快照契约）。** 取定义19.1的三端来源，记为

$$
S=C_4^3\times C_2,\qquad z=(a,u,v,h),\qquad
Y=a+u+v\in C_4,\qquad t=Y+2h\in C_4.
\tag{20.1}
$$

从零来源经公开平移可达全部 $128$ 个来源。调用在任意可达来源上发生，转换期间来源固定；三个端口的完整旧状态恰为 $(a,t),(u,t),(v,t)$。沿用定义19.2的快照访问限制：没有旧输入历史、刚消费的增量、额外控制器、免费探测、依赖来源的触发、时序、沉默或其他旁信道。接收端先在一个固定二值时隙广播

$$
b=q(a,t)\in\{0,1\},\qquad
r=e_2(u,t,b),\quad s=e_3(v,t,b)\in\{0,1\}.
\tag{20.2}
$$

此广播由两个发送端共同读到，传输代价只计一次；随后两条定向回复各占一个固定二值时隙，同时送达接收端，发送端不能读取对方回复。所有映射预先固定且确定性；任意解码函数 $D(a,t,b,r,s)$ 必须在全部 $S$ 上给出 $Y$。转换后的持续输出任务明确取为 $(Y,t)$；$t$ 在转换前已知。后续公共平移只是状态更新输入，不是转换时的免费信息。以下量词只覆盖这个固定接口，不扩展到不限轮交互、随机或量子协议、变长消息及免费信道。

记 $[x]_4\in\{0,1,2,3\}$ 为标准代表，$L(x)=[x]_4\bmod2$，$H(x)=\lfloor[x]_4/2\rfloor$，并令 $p=L(t-a)$。位运算使用 $\oplus$，位的乘积是普通 $0,1$ 乘法，模四等式中的位按其整数代表嵌入。固定 $t$ 时，局部代换 $(z_1,z_2,z_3)=(a-t,u,v)$ 给出

$$
\sum_{i=1}^3 z_i\equiv0\pmod2,\qquad
F(z_1,z_2,z_3)=\frac{[z_1+z_2+z_3]_4}{2}=h,
\qquad Y=t+2F\pmod4.
\tag{20.3}
$$

这里的偶和承诺及布尔求值函数已有于 Buhrman、Cleve、van Dam，*Quantum Entanglement and Communication Complexity*，[quant-ph/9705033v1](https://arxiv.org/pdf/quant-ph/9705033v1)，PDF第3页§2式(1)–(4)：其原式为 $F(x,y,z)=[x+y+z]_4/2$。式(20.3)由 $Y-t=-2h=2h$ 得到。原文使用每位广播且全体参与者最终获知答案的接口；下述单接收端、先一位广播再两条同时定向回复的分类需在定义20.1内另证。

**定理 20.2（任意查询、任意二值回复与任意解码的充要分类）。** 定义20.1的协议精确，当且仅当存在位 $c_t$ 及按 $(t,p)$ 取值的位 $A,B,c_2,c_3$，使

$$
\begin{gathered}
q(a,t)=p\oplus c_t,\qquad A\oplus B=1\oplus p,\\
e_2(u,t,b)=H(u)\oplus A L(u)\oplus c_2,\qquad
e_3(v,t,b)=H(v)\oplus B L(v)\oplus c_3,
\qquad p=b\oplus c_t,
\end{gathered}
\tag{20.4}
$$

且解码函数在实际观测像上满足

$$
D(a,t,b,r,s)
=a+p+2\bigl(r\oplus s\oplus c_2\oplus c_3\oplus Bp\bigr)\pmod4.
\tag{20.5}
$$

每个固定 $t$ 的两种广播标签都实际出现；每个固定 $(a,t)$ 上四种回复对 $(r,s)$ 都实际出现。式(20.4)对回复的全部局部输入成立，解码在实际像外可任取。

证明。固定 $(a,t)$。每对满足 $L(u)\oplus L(v)=p$ 的 $(u,v)$ 都给出实际来源，且原钟唯一为 $h=[t-a-u-v]_4/2$。先不限制查询、回复及解码的形式。对任何非空分支 $(t,b)$，选一个进入该分支的 $a$。若第二端将 $x,x+2$ 合并，取一个与 $x$ 奇偶相容的第三端坐标；把第二端坐标加二、把 $h$ 加一，得到相同 $(a,t,b,r,s)$ 而 $Y$ 相差二的两个实际来源，任意解码都不可能精确。第三端同理。因此每个已用分支的每个二值发送映射 $e$ 都满足 $e(0)\ne e(2)$、$e(1)\ne e(3)$，从而唯一写成

$$
e(x)=H(x)\oplus A L(x)\oplus c,
\qquad c=e(0),\quad A=e(0)\oplus e(1).
\tag{20.6}
$$

在此分支分别记两端系数为 $A,B$，常数为 $c_2,c_3$。写

$$
u=l+2U,\qquad v=(l\oplus p)+2V,
\qquad l,U,V\in\{0,1\}.
\tag{20.7}
$$

两种低位分配 $l=0,1$ 均实际存在；对每种分配，$U,V$ 独立遍历两位，所以每种回复对均出现。整数低位和为 $l+(l\oplus p)=p+2(1-p)l$，代入回复表达式即得

$$
Y=a+p+2\bigl(r\oplus s\oplus c_2\oplus c_3\oplus Bp
             \oplus(A\oplus B\oplus1\oplus p)l\bigr)\pmod4.
\tag{20.8}
$$

固定任意回复对，在两种低位分配中各取产生该回复对的高位。若最后的 $l$ 系数非零，这两个来源的观测相同而 $Y$ 相差二。因此无论解码是否事先写成异或形式，都必须有 $A\oplus B=1\oplus p$，并被迫在全部实际回复对上取式(20.5)。同一个 $(t,b)$ 分支不能同时服务 $p=0$ 与 $p=1$，因为二者要求的系数关系相反。

每个固定 $t$ 上，$a$ 遍历 $C_4$，两种 $p$ 均存在。只有两个广播标签，且每个标签的非空原像只能包含一种 $p$，所以每种 $p$ 恰占一个标签，查询被迫为 $p\oplus c_t$。两个分支遂都非空，前述回复形式覆盖全部 $(t,b)$。$p$ 可由 $(t,b)$ 得到，故按 $(t,p)$ 指定系数不违反发送端访问限制。

反向，给定式(20.4)，每个来源都满足式(20.7)；式(20.8)中的 $l$ 项消失，式(20.5)即精确等于 $Y$。每个 $(a,t)$ 及每个低位分配都允许独立选择 $U,V$，故全部回复对可达。查询两标签的可达性已由两种 $p$ 给出。证毕。

**推论 20.3（信号重标记后的规范形与反馈的作用）。** 只允许按 $t$ 补广播位、按 $(t,b)$ 分别补回复位并相应调整解码，且把实际像上相同的解码视为相同；不作来源自同构或发送端互换。在此等价下，每个精确协议唯一由各 $(t,p)$ 上的一个自由位 $A_{t,p}$ 指定，可取

$$
\begin{gathered}
b=p,\qquad r=H(u)\oplus A_{t,p}L(u),\qquad
s=H(v)\oplus\bigl(A_{t,p}\oplus1\oplus p\bigr)L(v),\\
Y=a+p+2\bigl(r\oplus s\oplus
                  (A_{t,p}\oplus1\oplus p)p\bigr)\pmod4.
\end{gathered}
\tag{20.9}
$$

一般标签中，反馈所补足的是给定 $t$ 后的 $p$，即 $p=b\oplus c_t$，不要求 $b$ 单独全局表示该奇偶。对每个固定 $t$，在 $p=0,1$ 两分支之间恰有一个发送端改变其无标签输入分割；是哪一端可随 $t$ 改变。

证明。先补去 $c_t$，再按已知 $(t,p)$ 补去 $c_2,c_3$，定理20.2给 $B=A\oplus1\oplus p$，得到式(20.9)。输入分割由式(20.6)中的 $A$ 决定；回复位取补不改变 $A$，广播标签取补不改变按实际 $p$ 索引的 $A_{t,p}$，故该规范形唯一。固定 $t$，两分支的 $A\oplus B$ 分别为一和零，因此 $(A_{t,0}\oplus A_{t,1})\oplus(B_{t,0}\oplus B_{t,1})=1$，两端恰有一个改变分割。定理20.2又说明任何成功的二值反馈都必须区分两种 $p$，这就是此接口内接收端信号的必要作用。证毕。

**命题 20.4（实际观测的两点来源纤维）。** 对任意定理20.2中的精确协议，令

$$
O(z)=(a,t,b,r,s),\qquad \mathcal O=O(S).
\tag{20.10}
$$

固定任意实际观测，按式(20.5)恢复 $Y$，其来源纤维恰为以下两点，参数 $l=0,1$：

$$
\begin{gathered}
u_l=l+2\bigl(r\oplus c_2\oplus Al\bigr),\\
v_l=(l\oplus p)+2\bigl(s\oplus c_3\oplus B(l\oplus p)\bigr),\\
h_l=\frac{[t-Y]_4}{2},\qquad z_l=(a,u_l,v_l,h_l).
\end{gathered}
\tag{20.11}
$$

两点有相同的 $a,Y,t,h$，但两个发送端坐标都分别不同；因此观测能恢复这些共同量，却不能恢复任一发送端坐标。实际观测像有 $64$ 个元素。

证明。给定 $l$，由两回复式分别反解高位，唯一得到式(20.11)。其低位满足实际来源奇偶约束，式(20.8)及系数条件保证两点具有同一个已恢复的 $Y$；于是 $t-Y$ 为偶数，所列 $h_l$ 唯一且使钟标签确为 $t$。反向，每个来源的 $l=L(u)$ 必为零或一，故没有第三点。两点的 $u$ 低位不同，$v$ 低位也不同，遂不能分别恢复 $u$ 或 $v$。$16$ 种 $(a,t)$ 各有四种回复对且 $b$ 已被确定，故 $|\mathcal O|=64$，亦等于 $128/2$。

特别地，取 $A_{t,p}=1-p$、$B=0$ 及全部补位常数为零，得到合法协议

$$
b=p,\qquad r=H(u)\oplus(1-b)L(u),\qquad s=H(v),\qquad
Y=a+b+2(r\oplus s)\pmod4.
\tag{20.12}
$$

来源 $(0,0,1,0)$ 与 $(0,1,0,0)$ 均给 $O=(0,1,1,0,0)$，且 $Y=t=1$。这是式(20.11)的一条完整两点纤维。证毕。

**推论 20.5（相同计费与不同的必然中间披露）。** 对三端全部来源，定义20.1的精确协议计费为三位，接收端观测必有两点来源纤维；定义19.2的无反馈同时接口最小计费同为三位，但其任意精确协议的接收端旧状态与回复联合确定整个来源。两者都可在转换后仅保留八态 $(Y,t)$。因此此处的差别是中间来源可恢复性，不是三位基线上的通信节省或最终记忆节省。

证明。先反馈接口计一次公共广播及两条各一位的定向回复，式(20.12)达到，命题20.4给每个精确协议的两点纤维。无反馈侧直接使用定理19.3及推论19.4的 $r=3$ 特例；其中完整输入加高位构造的文献归属沿用推论19.4。两侧恢复 $Y$ 后均已有 $t$，可按命题19.5的闭更新保存 $(Y,t)$；下面定理20.6就这里明确要求的成对输出给出八态最小值。上述比较只涉及一次通信、接收端中间观测及最终持久状态，不给出转换工作空间的最小值。证毕。

**定理 20.6（观测到闭动态消费者的因子化）。** 定义20.1的持续输出任务具有八态闭实现

$$
\mathcal C=\{(Y,t)\in C_4^2:L(Y)=L(t)\},\qquad
F:S\longrightarrow\mathcal C,\quad F(z)=(Y,t).
\tag{20.13}
$$

对任意来源平移 $d=(s_1,s_2,s_3,k)\in C_4^3\times C_2$，令 $\delta=s_1+s_2+s_3\in C_4$，则

$$
U_d(Y,t)=(Y+\delta,\ t+\delta+2k),\qquad
F(z+d)=U_d(F(z)).
\tag{20.14}
$$

每个精确协议都给满射因子化 $S\xrightarrow{O}\mathcal O\xrightarrow{\pi}\mathcal C$，其中 $\pi(a,t,b,r,s)=(D(a,t,b,r,s),t)$。$F$ 的来源核为

$$
K=\{(s_1,s_2,s_3,k):s_1+s_2+s_3=0\text{ 于 }C_4,\ k=0\},
\qquad |K|=16,
\tag{20.15}
$$

且 $F$ 的纤维正是 $K$ 的陪集。该八态实现对任意有限后续输入词精确，并在定义15.11的完整持久状态口径下最小，包括状态可依赖整个历史的实现。若持续任务只输出 $Y$，相应最小状态数为四。

证明。等奇偶关系由 $t=Y+2h$ 直接得到，并在式(20.14)下保持。对任意等奇偶的 $(y,t)$，来源 $(y,0,0,[t-y]_4/2)$ 映到它，故 $F$ 满射，$|\mathcal C|=8$。来源平移使 $Y$ 加 $\delta$、$h$ 加 $k$，因此 $t$ 加 $\delta+2k$，得到一步交换式。以转换时正确恢复的 $(Y,t)$ 为初态，对词长归纳可得每个有限后续词的正确输出。

定理20.2保证 $\pi\circ O=F$，两箭头按实际像取值均满射。$F$ 是群同态；$F(d)=(0,0)$ 恰要求 $\delta=0$、$2k=0$ 于 $C_4$，后者等价于 $k=0$ 于 $C_2$。任取 $s_1,s_2$ 后 $s_3=-s_1-s_2$ 唯一，故 $|K|=16$，纤维为其陪集。

最小性沿用定义15.11所计的全部可再次参与解码或更新的状态，不另给免费钟或历史。八种 $(Y,t)$ 都能在调用时出现，而当前输出已要求这个有序对。任意精确实现若把产生不同当前输出的两条历史送到同一完整状态，其确定性解码立即矛盾，故至少需要八个可达状态，不必假设历史状态经 $S$ 因子化。式(20.14)达到该下界。只输出 $Y$ 时，同样由四个可达当前值给四态下界，更新 $Y\mapsto Y+\delta$ 在四态上达到；因此八态结论依赖成对输出的明确要求。证毕。

**命题 20.7（快照纤维不必是平移合同）。** 式(20.12)的观测 $O$ 没有满足 $O(z+d)=V_d(O(z))$ 的全平移更新族 $V_d:\mathcal O\to\mathcal O$，尽管其因子 $F=\pi\circ O$ 有定理20.6的闭更新。

证明。取命题20.4的同观测来源 $z=(0,0,1,0)$、$z'=(0,1,0,0)$，共同平移 $d=(0,0,1,0)$。直接代入式(20.12)得到

$$
\begin{gathered}
O(z)=O(z')=(0,1,1,0,0),\\
O(z+d)=(0,2,0,0,1),\qquad O(z'+d)=(0,2,0,1,0),\\
F(z+d)=F(z'+d)=(2,2).
\end{gathered}
\tag{20.16}
$$

相同的旧观测和相同输入不能经确定性更新给出两个不同的新观测，故此 $V_d$ 不存在。这里 $O(z+d)$ 是在平移后来源上重新求值的快照观测；闭消费者更新无需重跑转换。由来源观测恢复当前任务值，并不自动使该观测的等值关系对后续平移封闭；因子化 $S\to\mathcal O\to\mathcal C$ 中的 $\mathcal C$ 才承担本协议给出的八态闭边界。证毕。

## 20.99 追加锚

## 21. 四端以上补偿钟的有限接收端查询与来源恢复

**定义 21.1（有限公共查询与固定包宽）。** 固定 $r\ge4$，沿用定义19.1的实际来源与完整最小旧状态：

$$
S=C_4^r\times C_2,\qquad
Y=\sum_{i=1}^r x_i\in C_4,\qquad t=Y+2h\in C_4,\qquad
L_i=(x_i,t).
\tag{21.1}
$$

全部公共平移可达 $S$ 的每一点。记 $L(x)=[x]_4\bmod2$、$H(x)=\lfloor[x]_4/2\rfloor$。旧端实际输出为 $(x_i,\ell)$，其中 $\ell=H(t)$；$L_i$ 的十六态最小值是定义19.1所引用的完整未来行为最小值。式(19.3)的旧状态实际联合像有 $2\cdot4^r$ 个元素；这两个计数沿用旧状态标签的含义。

一次独立调用在预定时隙发生，来源在调用期间固定，精确性要求覆盖全部 $S$。接收端只读取 $(x_1,t)$，先向所有发送端作一次公共查询广播，再由各发送端同时向接收端回复：

$$
c=q(x_1,t)\in C,\qquad
m_i=e_i(x_i,t,c)\in A_i\quad(2\le i\le r),\qquad
\Phi_q(x,h)=(x_1,t,m_2,\ldots,m_r).
\tag{21.2}
$$

$C,A_2,\ldots,A_r$ 均为预先声明的非空有限字母表，$q:C_4^2\to C$ 与 $e_i:C_4^2\times C\to A_i$ 是全局固定的确定性映射。不同 $(t,c)$ 可选用不同局部回复函数。发送端不能读取其他发送端的回复；旧输入词、刚消费的公共增量、另存历史、免费钟、探测、依赖来源的触发、时序、沉默及额外控制器均不提供信息。查询由接收端已有状态确定，故接收端可重算 $c$，无需在 $\Phi_q$ 中另列它。只有接收端须输出 $Y$，其解码器为 $D:C_4^2\times\prod_{i=2}^r A_i\to C_4$；精确性指 $D\circ\Phi_q=Y$。

本契约采用预先声明容量的固定包宽：

$$
w_0=\lceil\log_2|C|\rceil,\qquad
w_i=\lceil\log_2|A_i|\rceil,\qquad
W_{\mathrm{in}}=\sum_{i=2}^r w_i,\qquad
W_{\mathrm{tot}}=w_0+W_{\mathrm{in}}.
\tag{21.3}
$$

每个包时隙均按其声明宽度计费，宽度不随来源或分支变化，未用标签及填充不使已声明的位免费；公共查询广播只计一次。单元素查询字母表的时隙宽度为零，不形成依赖来源的沉默信道。若改用允许重编码的有效查询像计费，应将查询字母表明确改为 $\operatorname{im}q$，并以 $\lceil\log_2|\operatorname{im}q|\rceil$ 代替 $w_0$；这与保留原声明 $C$ 的计费是不同契约。本节不取期望长度或变长长度，随机、量子、噪声及多轮交互也不在上述量词内。

式(19.5)的固定 $t$ 代换 $z_1=x_1-t$、$z_i=x_i$ 将此来源化为偶和承诺，并给出 $F(z)=[\sum_i z_i]_4/2=h$ 与 $Y=t+2F(z)$。这一承诺函数的归属沿用定义19.2所引 Buhrman、Cleve、van Dam，*Quantum Entanglement and Communication Complexity*，[quant-ph/9705033v1](https://arxiv.org/pdf/quant-ph/9705033v1)，PDF第3页§2式(1)–(4)，以及 Buhrman、van Dam、Høyer、Tapp，*Multiparty Quantum Communication Complexity*，[quant-ph/9710054v2](https://arxiv.org/pdf/quant-ph/9710054v2)，PDF第2页§2及第4–5页§3式(4)–(5)的 $n=2$ 特例。此对应只识别函数及来源关系；原文的广播、全体输出和有序一轮通信接口不等于式(21.2)。后一文§3的多方下界要求 $n\ge\log_2 r$，不用于固定 $n=2$ 的任意 $r$。

**定理 21.2（任意有限查询下的精确分支条件）。** 对定义21.1的固定查询与回复映射，记

$$
B(t,c)=\{a\in C_4:q(a,t)=c\},\qquad
f_i^{t,c}(x)=e_i(x,t,c).
\tag{21.4}
$$

称 $B(t,c)\ne\varnothing$ 的分支可达。下列三项等价：

1. 存在解码器从 $\Phi_q$ 在全部 $S$ 上精确恢复 $Y$。
2. 每个可达 $(t,c)$ 上，每个发送者均满足
   $f_i^{t,c}(0)\ne f_i^{t,c}(2)$ 与 $f_i^{t,c}(1)\ne f_i^{t,c}(3)$，且至多一个 $f_i^{t,c}$ 非单射。
3. $\Phi_q$ 在 $S$ 上单射，即接收端旧状态与回复元组共同确定整个来源。

唯一非单射发送者若存在，其下标可依赖 $(t,c)$，不要求在全部分支固定。空分支没有条件。三值映射也可作为唯一非单射例外，例如将 $0,1$ 合并而将 $2,3$ 分开；其固定包宽仍至少为两位。来源可恢复性是观测的性质，不要求接收端实际保存全部来源坐标。

证明。先设存在精确解码器。固定一个可达 $(t,c)$，再固定任意 $a\in B(t,c)$。与该接收端情境相容的发送端元组恰为

$$
\mathcal P_{a,t}
=\left\{(x_2,\ldots,x_r)\in C_4^{r-1}:
             a+\sum_{i=2}^r x_i\equiv t\pmod2\right\},
\qquad h=\frac{[t-a-\sum_{i=2}^r x_i]_4}{2}.
\tag{21.5}
$$

每个这样的元组给出唯一实际来源。以下始终保持同一个 $a,t,c$，并只在 $\mathcal P_{a,t}$ 内比较来源。

若某个 $f_i^{t,c}$ 将 $b,b+2$ 合并，取另一发送者 $k\ne i$，令其余发送者坐标为零，并取 $x_k\in\{0,1\}$ 使 $a+b+x_k\equiv t\pmod2$。先置 $x_i=b$，再将其改为 $b+2$。两个发送端元组同属 $\mathcal P_{a,t}$，其唯一原钟满足 $h'=h+1$ 于 $C_2$；全部观测相同而 $Y'=Y+2$，矛盾。因此每个回复映射都分离同奇偶的不同值。

若两个不同发送者 $i,j$ 的映射都非单射，则各有一对异奇偶碰撞。$C_4$ 的每个异奇偶无序对都可定向为 $b\to b+1$，故可取

$$
f_i^{t,c}(b_i)=f_i^{t,c}(b_i+1),\qquad
f_j^{t,c}(b_j)=f_j^{t,c}(b_j+1).
\tag{21.6}
$$

因 $r-1\ge3$，存在不同于 $i,j$ 的第三个发送者 $k$。令其他发送者坐标为零，并取 $x_k\in\{0,1\}$ 满足

$$
a+b_i+b_j+x_k\equiv t\pmod2.
\tag{21.7}
$$

从 $x_i=b_i,x_j=b_j$ 的实际来源出发，同时将这两坐标各加一，保持第三发送者及所有其他坐标不变。总和加二，奇偶约束仍成立，唯一原钟相应加一；接收端的 $a,t,c$ 和全部回复均不变，而 $Y$ 相差二，再次矛盾。第二项得证。这里补足奇偶的是第三个发送者，既未更换接收端值，也未把实际来源支持换成无约束的乘积。

反向设第二项成立，给定一个实际观测，先由 $(x_1,t)$ 重算 $c$。若该分支的回复映射全都单射，逐个反演即可恢复所有 $x_i$。否则令 $j=j(t,c)$ 为唯一例外，反演其他发送者后计算

$$
x_j\equiv t-x_1-\sum_{i\ne1,j}x_i\pmod2,
\qquad x_j\in (f_j^{t,c})^{-1}(m_j).
\tag{21.8}
$$

同奇偶分离使该回复纤维中每种奇偶至多有一个值，实际来源保证所需值存在，故 $x_j$ 唯一。于是 $Y=\sum_i x_i$，再由 $h=[t-Y]_4/2$ 恢复原钟，第三项成立。第三项允许在实际观测像上反演来源并求和，在像外任取解码值，即得第一项。证毕。

**推论 21.3（每个固定查询的最小回复代价）。** 对每个固定的 $q:C_4^2\to C$，在定义21.1的有限全局回复字母表、回复映射与精确解码器之间取最小值，有

$$
\min W_{\mathrm{in}}=2r-3,\qquad
\min W_{\mathrm{tot}}=\lceil\log_2|C|\rceil+2r-3.
\tag{21.9}
$$

若连同查询字母表与查询一起优化，则最小总位数为 $2r-3$，由单元素零宽查询达到。

证明。取任一可达分支。定理21.2使每个发送者至少有两个回复符号，并使至少 $r-2$ 个发送者的回复映射单射于四个输入。因此这些发送者的全局字母表至少有四个元素，得到

$$
W_{\mathrm{in}}\ge 2(r-2)+1=2r-3.
\tag{21.10}
$$

宽度在全部分支共用；随 $(t,c)$ 改变例外下标不能降低这一全局下界。达到构造直接取推论19.4及式(19.9)：一个固定发送者只发 $H(x_j)$，其余发送者发送完整坐标，所有回复均忽略 $c$。接收端用已知奇偶恢复剩余低位，所以该构造对每个 $q$ 都精确，回复宽度恰为 $2r-3$。完整输入加高位构造的来源沿用推论19.4所引 Buhrman、van Dam、Høyer、Tapp 文的 PDF第3页§2.1；这里只将同一构造用于任意查询。加上式(21.3)固定且只计一次的查询费用，得到式(21.9)。最后取 $|C|=1$ 即达全体查询的最小值。若改为有效查询像计费，同一论证给查询项 $\lceil\log_2|\operatorname{im}q|\rceil$，不能在保留较大声明字母表的式(21.9)中免费删去填充。证毕。

**命题 21.4（三端边界与第三发送者的作用）。** 定理21.2的来源恢复必要性在 $r=3$ 不成立：存在一次一位公共查询及两条各一位同时回复的全来源精确协议，其总费用为三位、接收端每个实际观测的来源纤维恰有两点。因此 $r\ge4$ 时查询既不能降低最小入向回复位数，也不能消除中间观测的来源可恢复性；三端则能改变后一性质。

证明。三端直接采用式(20.12)的协议；命题20.4给出全部实际观测的两点来源纤维，推论20.5给出一次广播加两次回复的三位计费及与无反馈接口的比较。其精确性并不违反式(21.6)–(21.7)的论证：只有两个发送者时，两对碰撞按加一定向后的起点之和可以不满足固定接收端的实际奇偶承诺，因而起点及双移后的终点均不在该来源纤维内。$r\ge4$ 才能保留接收端及查询，用第三个发送者独立补足该奇偶。推论21.3与定理21.2给出四端以上的两个结论；所比较的接口均只有一次接收端查询和同时回复，不涉及不限轮交互的下界。证毕。

**命题 21.5（来源可辨观测与八态持续成对任务）。** 对 $r\ge4$ 的任意精确协议，若从转换完成时起接收端每次输出都明确要求有序对 $(Y,t)$，则它可只保留

$$
\mathcal C=\{(y,t)\in C_4^2:y\equiv t\pmod2\},\qquad
F:S\to\mathcal C,\quad F(x,h)=(Y,t).
\tag{21.11}
$$

$|\mathcal C|=8$，$F$ 的每条来源纤维有 $4^{r-1}$ 个元素；而转换观测 $\Phi_q$ 的每条实际来源纤维为单点。该成对任务有八态闭实现，且在完整持久状态口径下最小。

证明。任给 $(y,t)\in\mathcal C$，任取 $x_2,\ldots,x_r$，再令 $x_1=y-\sum_{i=2}^r x_i$、$h=[t-y]_4/2$，得到全部且互异的 $4^{r-1}$ 个原像，亦证 $F$ 满射。由定理21.2与精确性，映射 $\pi:\Phi_q(S)\to\mathcal C$，$\pi(a,t,m_2,\ldots,m_r)=(D(a,t,m_2,\ldots,m_r),t)$，给出 $F=\pi\circ\Phi_q$，其中 $\Phi_q$ 在实际来源上单射，$\pi$ 则把上述来源合并为同一个任务值。

后续公共平移 $(u,v)$ 令 $d=\sum_i u_i$，直接沿用式(19.10)的闭更新 $(Y,t)\mapsto(Y+d,t+d+2v)$。因此从已恢复的成对状态出发即可完成所有后续有限词的任务，无须保留旧输入词。八个当前成对输出均实际可达，完整持久状态若少于八个便会合并两个不同的必需当前输出，故八态最小。这个闭状态大小沿用命题19.5的转换消费者；强制来源可辨的中间观测不要求永久保留整个来源，也不改变该八态持久状态值。证毕。

## 21.99 追加锚

## 22. 二元特征的分裂、精确边界与持续成对记忆

**定义 22.1（指定特征与固定查询接口）。** 设 $G$ 为有限阿贝尔群，以加法记群运算；$\chi:G\twoheadrightarrow C_2$ 为指定满同态，$H=\ker\chi$，$r\ge4$。本节的实际来源、目标与完整旧载体明确规定为

$$
S=G^r\times H,\qquad Y=\sum_{i=1}^r x_i,\qquad
 t=Y+h,\qquad L_i=(x_i,t),\qquad a=x_1.
\tag{22.10}
$$

这里 $h$ 是 $H$ 中的元素；规定完整载体 $L_i$ 不包含任何关于未指定旧任务的最小性断言。来源在一次调用期间固定，接收端读取 $(a,t)$，先作一次公共查询，再接收同时、局部的回复：

$$
c=q(a,t)\in C,\qquad e_i(x_i,t,c)\in A_i\quad(2\le i\le r),\qquad
\Phi_q(x,h)=(a,t,e_2(x_2,t,c),\ldots,e_r(x_r,t,c)).
\tag{22.11}
$$

$C,A_2,\ldots,A_r$ 是预先声明的非空有限字母表，$q:G^2\to C$ 固定，$e_i:G^2\times C\to A_i$ 为确定性映射。发送者只读取自己的 $(x_i,t)$ 与公共 $c$，不能读取其他回复；没有另存历史、额外侧信息、来源依赖的触发、时序或沉默信道。精确性指存在 $D:G^2\times\prod_{i=2}^r A_i\to G$，在全部实际 $S$ 上满足 $D\circ\Phi_q=Y$。查询可由接收端重算，却仍按其声明宽度收费：

$$
w_0=\lceil\log_2|C|\rceil,\qquad w_i=\lceil\log_2|A_i|\rceil,\qquad
W_{\rm in}=\sum_{i=2}^r w_i,\qquad W_{\rm tot}=w_0+W_{\rm in}.
\tag{22.12}
$$

广播只计一次，各时隙按固定宽度计费，未用标签也收费；单元素字母表允许零宽时隙。本节的最小值只在这个一次查询、同时回复、接收端输出的确定性接口内取，不是期望码长、渐近速率或任意交互下界。

记 $B(t,c)=\{a:q(a,t)=c\}$、$f_i^{t,c}(x)=e_i(x,t,c)$；$B(t,c)\ne\varnothing$ 称可达分支。固定 $a\in B(t,c)$ 后，实际发送端纤维恰为

$$
\mathcal P_{a,t}=\left\{(x_2,\ldots,x_r):
 \chi(a)+\sum_{i=2}^r\chi(x_i)=\chi(t)\right\},\qquad
h=t-a-\sum_{i=2}^r x_i\in H.
\tag{22.13}
$$

每个纤维元组对应唯一来源。以下使用的有限支持判据是：同一实际支持内，相同回复元组必须给出相同目标值。它是 Deylam Salehi、Chaouchi，*Support-Aware Telemetry Compression for 5G Positioning via Conditional Conflict Graphs*，[arXiv:2609.12933v1](https://arxiv.org/pdf/2609.12933v1)，PDF第2页 Proposition 1 的乘积分割判据；同页 Definition 1 的条件冲突图固定其他编码后，也比较这种实际支持上的冲突。这里在每个固定 $(a,t,c)$ 上将其支持取为 $\mathcal P_{a,t}$、目标取为 $a+\sum_{i=2}^r x_i$。仅借用该有限精确性判据，不移用其应用模型或速率结论，也不从广播、全体输出或有序通信模型移入下界。

**定理 22.2（可达分支的全部碰撞条件）。** 定义22.1的协议能精确恢复 $Y$，当且仅当每个可达 $(t,c)$ 同时满足以下条件：每个 $f_i^{t,c}$ 在 $\chi^{-1}(0)$ 与 $\chi^{-1}(1)$ 上分别单射；并且或者至多一个发送者非单射，或者存在该分支的元素 $\tau$，使

$$
\chi(\tau)=1,\qquad 2\tau=0,\qquad
f_i^{t,c}(x)=f_i^{t,c}(x'),\ x\ne x'
\ \Longrightarrow\ x'-x=\tau
\quad(2\le i\le r).
\tag{22.14}
$$

不要求每个可合并对都被合并：部分碰撞也允许。例外发送者与 $\tau$ 均可随分支改变，空分支无条件。在精确协议中，$\Phi_q$ 在实际 $S$ 上单射，当且仅当每个可达分支至多有一个非单射发送者。

证明。固定可达 $(t,c)$ 及一个实际 $a\in B(t,c)$。若某个发送者把同特征的不同 $b,b'$ 合并，取另一发送者补足式(22.13)的奇偶，其余坐标固定为零。只将 $b$ 改为 $b'$ 仍在同一实际纤维中；按式(22.13)分别取唯一的 $h$，便得到相同观测而总和相差非零 $b'-b$ 的两个来源。因此同特征必须分离，每个非平凡碰撞差都满足 $\chi(d)=1$。

现取两个不同的非单射发送者 $i,j$，任选其碰撞对 $b_i,b_i+d$ 与 $b_j,b_j+e$。存在第三个发送者 $k\ne i,j$，因为 $r-1\ge3$。先用 $k$ 补足起点 $x_i=b_i,x_j=b_j$ 的奇偶，同时将两坐标改为 $b_i+d,b_j+e$。两点仍属 $\mathcal P_{a,t}$，全部回复相同，故精确性要求 $d+e=0$。再以 $x_i=b_i,x_j=b_j+e$ 为起点，重新用 $k$ 补足奇偶，改为 $b_i+d,b_j$；同理得到 $d-e=0$。两次比较都保持原来的 $a,t,c$；补足坐标只在各自比较的两点之间保持不变。于是

$$
d=e=-e,\qquad 2d=0.
\tag{22.15}
$$

固定其中一个发送者的一对碰撞，再与其他发送者的任意碰撞比较；随后反过来固定另一发送者，便使所有非平凡碰撞差都等于同一个 $\tau=d$。这证明必要性，也涵盖一个发送者有多对部分碰撞的情形。

反之，比较两个相同实际观测。它们有相同的 $a,t,c$。若至多一个发送者非单射，其余坐标由回复唯一决定，式(22.13)决定剩余坐标的特征，同特征单射再唯一决定该坐标，故来源完全相同。若满足式(22.14)，两个来源的每个发送端坐标之差非零时必为 $\tau$；式(22.13)迫使非零差的个数为偶数，因 $2\tau=0$，两总和相同。目标因而在每条实际观测纤维上恒定，在观测像上定义解码器、像外任取值即可。

最后，若精确分支至少有两个非单射发送者，取各一对碰撞并用第三个发送者补足奇偶；同时改动两坐标产生两个不同来源，观测相同，总和因 $2\tau=0$ 而不变，$h$ 也不变。故该分支破坏来源单射性。结合上一段的唯一恢复即得最后的等价。证毕。

**命题 22.3（指定扩张的分裂与总和商观测）。** 对定义22.1的指定扩张

$$
0\longrightarrow H\longrightarrow G\mathrel{\mathop{\longrightarrow}^{\chi}} C_2\longrightarrow0,
\tag{22.16}
$$

若它不分裂，则每个精确 $Y$ 协议都恢复当前整个来源。若它分裂，取任一满足 $\chi(\tau)=1$、$2\tau=0$ 的元素，存在对任意固定 $q$ 都精确、却不恢复来源的协议：每个发送者回复

$$
p_\tau(x_i)=x_i-\chi(x_i)\tau\in H,\qquad
Y=p_\tau(a)+\sum_{i=2}^r p_\tau(x_i)+\chi(t)\tau.
\tag{22.17}
$$

这里二元特征作为 $0,1$ 系数；这个全商构造的每条实际观测纤维恰有 $2^{r-2}$ 个来源。

证明。分裂的标准含义是 $\chi$ 有同态截面，见 Keith Conrad，*Splitting of Short Exact Sequences for Groups*，[Theorem 3.3、Definition 3.4](https://kconrad.math.uconn.edu/blurbs/grouptheory/splittinggp.pdf)，PDF第5、7页；第7页还说明阿贝尔情形的半直积为直积。用于式(22.16)时，截面由 $1\mapsto\tau$ 决定，恰要求 $\chi(\tau)=1$ 与 $2\tau=0$；这只是该标准群论判据的具体化。无此元素时，定理22.2排除每个分支的两个非单射发送者，因此精确观测必为来源单射。

有此元素时，$G=H\oplus\langle\tau\rangle$，$p_\tau$ 是到 $H$ 的同态投影。由于 $h\in H$，有 $\chi(Y)=\chi(t)$，给出式(22.17)的解码公式。固定一个实际观测后，$a,t$ 与每个 $p_\tau(x_i)$ 已知，发送端坐标只能是 $p_\tau(x_i)+\epsilon_i\tau$；$r-1$ 个二元值仅受一个方程

$$
\sum_{i=2}^r\epsilon_i=\chi(t)-\chi(a)\quad\text{于 }C_2
\tag{22.18}
$$

约束，故有 $2^{r-2}$ 种选择。每种选择的 $Y$ 都由式(22.17)给定，$h=t-Y$ 唯一，所以计数恰好且全部实际可达。例如全零来源与 $x_2=x_3=\tau$、其余 $x_i=0,h=0$ 的来源都有 $a=t=Y=0$，全部回复相同。这一恒定纤维计数只针对式(22.17)的全商构造，不适用于定理22.2允许的任意部分碰撞。证毕。

**定理 22.4（每个固定查询的尖锐包宽）。** 令 $m=|H|$、$N=|G|=2m$、$b=\lceil\log_2m\rceil$。对每个固定的非空有限 $C$ 及 $q:G^2\to C$，在全局回复字母表与精确协议之间取最小值，则

$$
\min W_{\rm in}=
\begin{cases}
(r-2)\lceil\log_2N\rceil+\lceil\log_2m\rceil,&\text{式(22.16)不分裂},\\
(r-1)b,&\text{式(22.16)分裂},
\end{cases}
\qquad
\min W_{\rm tot}=\lceil\log_2|C|\rceil+\min W_{\rm in}.
\tag{22.19}
$$

证明。先取任一可达分支。由定理22.2，各发送者在每个大小为 $m$ 的特征纤维上单射，故其全局字母表满足 $|A_i|\ge m$。不分裂时，这个分支至少有 $r-2$ 个发送者在整个 $G$ 上单射，故存在 $J\subseteq\{2,\ldots,r\}$、$|J|=r-2$，使

$$
|A_i|\ge N\ (i\in J),\qquad |A_i|\ge m\ (2\le i\le r).
\tag{22.20}
$$

先得到这些全局容量下界，再分别取二进制宽度的上取整并求和，即得式(22.19)的两个下界。不同分支更换例外下标不改变这些全局容量义务；不能只对字母表乘积取一次上取整来代替固定的逐包收费。

为达到不分裂情形的界，任取 $\chi(\sigma)=1$，选定一个固定发送者 $j$，令它发送 $p_\sigma(x_j)=x_j-\chi(x_j)\sigma\in H$，其余发送者发送完整 $x_i\in G$。$p_\sigma$ 在两条特征纤维上分别双射到 $H$，不要求它是群同态。接收端从完整坐标与 $t$ 得到

$$
\epsilon_j=\chi(t)-\chi(a)-\sum_{i\ne1,j}\chi(x_i),\qquad
x_j=p_\sigma(x_j)+\epsilon_j\sigma.
\tag{22.21}
$$

于是整个来源可恢复，所用字母表恰为一个 $H$ 与 $r-2$ 个 $G$。分裂情形由式(22.17)让全部发送者使用 $H$，达到 $(r-1)b$。两种构造均忽略查询，因而对每个固定 $q$ 都成立。加上只计一次的声明查询宽度得到总宽度；连同查询一起优化时可取 $|C|=1$。当 $H=\{0\}$ 时必分裂，总和已由 $t$ 确定，所有回复均为单元素字母表，入向宽度确为零。上述结论给出最小值及达到构造，不断言最优容量配置唯一，也不分类全部最优编码器。证毕。

**推论 22.5（同一来源上的完整来源消费者）。** 在同一 $S$ 与同一固定 $q$ 上，若接收端改为必须恢复整个 $(x,h)$，则无论式(22.16)是否分裂，最小入向宽度均为

$$
W_{\rm source}^{\min}=(r-2)\lceil\log_2N\rceil+\lceil\log_2m\rceil.
\tag{22.22}
$$

因此在一个固定的分裂来源上，仅要求精确 $Y$ 比要求完整来源恰好节省 $r-2$ 个入向位。

证明。来源恢复蕴含精确 $Y$，且 $\Phi_q$ 单射，故定理22.2使每个可达分支至多有一个非单射发送者。式(22.20)的全局容量下界随即成立。式(22.21)的一个固定例外构造对两种扩张都恢复来源，达到下界。因 $N=2m$，有 $\lceil\log_2N\rceil=b+1$；从式(22.22)减去分裂情形的 $(r-1)b$，差为 $r-2$。比较保持实际来源、查询、局部可读信息与计费规则完全相同，只改变所需输出；这不是转换工作空间下界。证毕。

**命题 22.6（成对消费者的闭记忆及其最小值）。** 对定义22.1的来源，每个旧载体的实际像有 $N^2$ 个元素，全体旧载体的实际联合像有 $N^r m$ 个元素。若转换后立即及以后每个有限公共输入词之后均要求输出有序对 $(Y,t)$，公共输入为平移 $(u,k)\in G^r\times H$，则最小完整持久状态数为 $Nm$，其固定二进制存储宽度为 $\lceil\log_2(Nm)\rceil$。具体闭状态为

$$
\mathcal C_\chi=\{(y,t)\in G^2:t-y\in H\},\qquad
F:S\to\mathcal C_\chi,\quad F(x,h)=(Y,Y+h).
\tag{22.23}
$$

$F$ 满射，每条纤维有 $N^{r-1}$ 个来源，且作为群同态有

$$
\ker F=\{(u,k)\in G^r\times H:\textstyle\sum_i u_i=0,\ k=0\}.
\tag{22.24}
$$

证明。任给 $x_i,t\in G$，取另一坐标为 $t-x_i$，其余坐标及 $h$ 为零，即实现该旧载体值，故局部像恰为 $G^2$。全部旧载体确定全部 $x_i,t$，进而确定 $h=t-\sum_i x_i$，所以旧载体联合映射单射于 $S$，联合像大小为 $N^r m$。

任给 $y\in G,h\in H$，令 $t=y+h$，再任取 $x_2,\ldots,x_r$ 并令 $x_1=y-\sum_{i=2}^r x_i$，得到全部且恰为 $N^{r-1}$ 个原像。因此 $|\mathcal C_\chi|=Nm$，$F$ 满射；令两输出均为零立即给出式(22.24)。公共平移将来源改为 $(x+u,h+k)$，若 $\delta=\sum_i u_i$，则

$$
(Y,t)\longmapsto(Y+\delta,t+\delta+k).
\tag{22.25}
$$

这个更新只用当前成对状态与本次公共输入，且因 $k\in H$ 保持 $\mathcal C_\chi$，可递推所有有限输入词。任意精确临时观测均通过 $\pi(a,t,m_2,\ldots,m_r)=(D(a,t,m_2,\ldots,m_r),t)$ 满足 $F=\pi\circ\Phi_q$，故转换后可以只保留这个闭状态；这不要求任意 $\Phi_q$ 本身对平移闭合。

全部 $Nm$ 个不同当前成对输出均实际可达；在下一输入到来之前就须正确输出。任何从完整持久状态读取输出的实现，其状态若少于 $Nm$，必合并两个不同的必需输出，矛盾。实现的状态可依赖先前历史，这一下界仍成立；若历史还需参与输出，它也属于完整持久状态而不能免费外置。式(22.25)达到此界。对 $Nm$ 个状态统一编码给出 $\lceil\log_2(Nm)\rceil$，并不要求分别编码两个分量后将取整宽度相加。这一存储量只计闭合后的完整持久状态，不是历史长度或转换工作空间的界。证毕。

**命题 22.7（同一环境群的两种实际关系）。** 取 $G=C_4\times C_2$，分别指定

$$
\chi_1(a,b)=a\bmod2,\quad H_1=\{0,2\}\times C_2;
\qquad
\chi_2(a,b)=b,\quad H_2=C_4\times\{0\}.
\tag{22.26}
$$

第一扩张不分裂，第二扩张由 $\tau=(0,1)$ 分裂。对相同 $r\ge4$，两者的最小精确 $Y$ 入向宽度分别为 $3r-4$ 与 $2r-2$；但旧载体局部像数、旧载体联合像数、持续成对状态数分别都等于 $64$、$4\cdot8^r$、$32$。这些相等的计数没有识别两者的实际来源关系。

证明。若 $\chi_1(a,b)=1$，则 $a$ 为奇数，$2(a,b)=(2,0)\ne0$，故不存在所需的奇特征二阶元。对 $\chi_2$，元素 $(0,1)$ 满足条件。代入 $N=8,m=4,b=2$，定理22.4与命题22.6给出全部宽度和计数。以共同坐标 $(x_1,\ldots,x_r,t)$ 表示实际旧联合关系时，全部 $x_i=0,t=(0,1)$ 只属于第一关系，全部 $x_i=0,t=(1,0)$ 只属于第二关系，因为此时实际条件恰为 $t\in H_j$。此外两核的群指数（各元素阶的最小公倍数）分别为 $2$ 与 $4$；环境群的自同构不能将前者映为后者，因而不能通过同一环境自同构识别这两种指定特征关系。第21节的 $C_4$ 情形对应不分裂一侧，但本例中的两种实际支持始终各由自己的 $H_j$ 指定。证毕。

## 22.99 追加锚

## 23. 接收端快照在全部公开平移下的闭性

**定义 23.1（任意二元特征源与快照）。** 设 $G$ 是有限阿贝尔群，$\chi:G\twoheadrightarrow C_2$ 是固定满同态，$H=\ker\chi$，并取 $r\ge2$。来源、目标和接收端可读的第一坐标与钟为

$$
S=G^r\times H,
\qquad Y=\sum_{i=1}^r x_i,
\qquad t=Y+h,
\qquad a=x_1 .
\tag{23.1}
$$

一次调用在固定来源上进行。接收端读取 $(a,t)$，计算可重算的公共查询 $c=q(a,t)$，并同时收到

$$
m_i=e_i(x_i,t,c)\quad(2\le i\le r),
\qquad O(x,h)=(a,t,m_2,\ldots,m_r).
\tag{23.2}
$$

所有字母表有限，映射预先固定且确定性；没有历史、未来来源观察、免费钟、时序或其他旁信道。精确性指存在 $D$ 使 $D(O(x,h))=Y$ 对全部 $S$ 成立。允许的公共输入是全部 $d=(u,k)\in G^r\times H$ 的平移

$$
(x,h)\longmapsto(x+u,h+k).
\tag{23.3}
$$

本节问的是整个快照 $O$ 是否存在 $O(s+d)=V_d(O(s))$ 的闭更新；较小的 $F=(Y,t)$ 任务只在后面的因子化中比较，不替代这个 $O(s+d)$ 问题。

**命题 23.2（正则作用的观察同余）。** 若存在映射 $V_d:O(S)\to O(S)$ 使

$$
O(s+d)=V_d(O(s))\qquad(s\in S,d\in S),
\tag{23.4}
$$

则

$$
K=\{v\in S:O(v)=O(0)\}
\tag{23.5}
$$

是 $S$ 的子群，且

$$
O(s)=O(s')\iff s'-s\in K.
\tag{23.6}
$$

反之，若 (23.6) 对某个子群 $K$ 成立，则 (23.4) 有唯一的 $V_d$，并且

$$
V_{d+e}=V_e\circ V_d .
\tag{23.7}
$$

这里使用的只是正则平移作用的标准同余原则：Milne, *Group Theory* v4.01, printed p.60, Proposition 4.7 给出传递作用的陪集表示；Bojańczyk--Klin--Lasota (2014), Lemma 3.5 与 Proposition 8.2 给出等变等价关系的商作用和子群陪集表示。这些是先有的群作用背景；本命题的 $O$ 不因重标记而成为群同态。

证明。若 $O(s)=O(s')$，(23.4) 对任意 $d$ 给出 $O(s+d)=O(s'+d)$，所以观察相等关系对平移不变。令 $s=0$ 即得 (23.6)。于是 $0\in K$；若 $v,w\in K$，先将相等关系平移 $v$ 得 $O(v)=O(v+w)=O(w)=O(0)$，故 $v+w\in K$；将 $O(v)=O(0)$ 平移 $-v$ 得 $O(0)=O(-v)$，故 $-v\in K$。这证明 $K$ 是子群。反向若两个点的差在 $K$，平移不变性给出观察相等。若 (23.6) 已知，定义 $V_d(O(s))=O(s+d)$；(23.6) 使定义与代表元无关，且给出唯一性和 (23.7)。证毕。

**定理 23.3（精确快照的闭性充要分类）。** 在定义23.1中，精确观察 $O$ 具有 (23.4)，当且仅当满足以下两者之一：

1. $O$ 在 $S$ 上单射；
2. $r\ge3$，存在一个固定的奇特征二阶元
   $$
   \tau\in G,\qquad 2\tau=0,\qquad \chi(\tau)=1,
   \tag{23.8}
   $$
   和一个固定集合 $J\subseteq\{2,\ldots,r\}$、$|J|\ge2$，使每个可达分支 $\mathfrak b=(a,t,c)$ 的局部映射
   $$
   f_i^{\mathfrak b}(x)=e_i(x,t,c)
   \tag{23.9}
   $$
   在 $i\in J$ 时的纤维恰为 $\{x,x+\tau\}$，在 $i\notin J$ 时单射。这里“可达”指存在来源产生该 $(a,t,c)$；空分支没有条件。分支的标签和局部映射可以改变，但 $J$ 与 $\tau$ 不得改变。

非单射情形中观察同余（纤维差）子群恰为

$$
K_J=\left\{(u,0):u_1=0,\ u_i\in\{0,\tau\}\ (i\in J),\ u_i=0\ (i\notin J),\ \#\{i:u_i=\tau\}\equiv0\pmod2\right\},
\tag{23.10}
$$

故每条纤维有 $2^{|J|-1}$ 个点，且

$$
|O(S)|=\frac{|G|^r|H|}{2^{|J|-1}}.
\tag{23.11}
$$

证明。先看 $r=2$。由精确性，从 $(a,t)$ 和回复得到 $Y$，因而

$$
 x_2=Y-a,
 \qquad h=t-Y
\tag{23.12}
$$

均唯一；不需要对未使用的局部输入作任何分类，所以 $O$ 单射，且由命题23.2的逆向构造闭合。

以下设 $r\ge3$。固定 $a,t$。任给发送者 $i\ge2$ 的一个 $x_i\in G$，可选另一发送者 $j\ne1,i$ 的特征值使

$$
\chi\!\left(a+\sum_{\ell=2}^r x_\ell\right)=\chi(t),
\tag{23.13}
$$

其余坐标任取零；随后唯一取 $h=t-a-\sum_{\ell=2}^r x_\ell\in H$。因此每个分支中每个发送者的每个输入都实际出现；单点分支也完全局部可达。

精确性还直接给出每个局部映射在每条特征纤维上的单射性：若同一分支中 $f_i^{\mathfrak b}(x)=f_i^{\mathfrak b}(x')$ 且 $\chi(x)=\chi(x')$ 而 $x\ne x'$，令 $\delta=x'-x\in H$，把一个来源的 $x_i$ 改为 $x'$ 并把 $h$ 改为 $h-\delta$；观察不变而 $Y$ 改变非零的 $\delta$，矛盾。

假设 $O$ 闭合，取 $K$ 如 (23.5)。精确性和观察中固定的 $a,t$ 给出

$$
K\subseteq L:=\{(u,k):u_1=0,\ \textstyle\sum_i u_i=0,\ k=0\}.
\tag{23.14}
$$

事实上，观察相等先给出 $u_1=0$ 与 $\sum_i u_i+k=0$，精确解码再给出 $\sum_i u_i=0$，于是 $k=0$。对 $i\ge2$ 令 $P_i$ 为 $K$ 在第 $i$ 坐标的投影。任取 $p\in P_i$，把 (23.13) 中实现任意 $x_i=x$ 的来源与其 $K$-平移比较，得到

$$
 f_i^{\mathfrak b}(x+p)=f_i^{\mathfrak b}(x)
\tag{23.15}
$$

对每个可达分支和每个 $x$ 成立；所以 $P_i$ 是每个该局部映射的全局周期。若 $0\ne p\in P_i\cap H$，只改变 $x_i$ 为 $x_i+p$ 并把 $h$ 改为 $h-p$，观察不变而 $Y$ 改变 $p$，违反精确性。因此

$$
P_i\cap H=\{0\},
\tag{23.16}
$$

而 $G/H\cong C_2$，故每个 $P_i$ 不是零就是 $\{0,\tau_i\}$，其中 $\tau_i$ 是奇特征二阶元。

若 $K\ne0$，(23.14) 使任一非零元至少有两个非零坐标，故至少两个 $P_i$ 非零。对两个这样的下标 $i,j$，用 (23.15) 同时作 $x_i\mapsto x_i+\tau_i$、$x_j\mapsto x_j+\tau_j$，并把 $h$ 改为 $h-(\tau_i+\tau_j)\in H$，得到相同观察而目标差为 $\tau_i+\tau_j$。精确性迫使 $\tau_i+\tau_j=0$，所以所有非零 $P_i$ 共有同一个 $\tau$。令

$$
J=\{i\ge2:P_i=\{0,\tau\}\}.
\tag{23.17}
$$

(23.15) 说明 $i\in J$ 时至少有 $\tau$-陪集碰撞。若该映射还有碰撞 $f_i(x)=f_i(x+\delta)$，精确性直接排除 $\delta\in H\setminus\{0\}$；将此碰撞与任意 $j\in J$ 的 $\tau$ 周期配对并补偿 $h$，精确性给出 $\delta+\tau=0$，故 $\delta=\tau$。同一论证若用于 $i\notin J$，任何碰撞都会迫使 $\tau$ 成为其周期，矛盾，故这些映射单射。于是 $J$ 与 $\tau$ 具有声明的固定形式。

由 (23.14)--(23.17)，任意 $v\in K$ 恰是 (23.10) 的元素：非零坐标只能是 $\tau$，总和为零又等价于出现偶数个 $\tau$。反向，偶数个 $\tau$ 的平移保持 $a,t$，并逐项保持所有回复，故都在 $K$ 中。这证明 $K=K_J$ 及 (23.11)。

最后反设已有固定 $J,\tau$ 的局部形式。两个相同观察的来源在 $i\notin J$ 上坐标相同，在 $i\in J$ 上差只能为 $0$ 或 $\tau$；总和与 $t$ 相同且 $2\tau=0$，故非零差数为偶数且 $h$ 不变，差属于 $K_J$。反向每个 $K_J$-平移显然保持观察。于是 (23.6) 成立，命题23.2给出对所有平移的闭更新。若 O 单射，则 K=\{0\}，命题23.2的逆向构造给出同样的闭更新。证毕。

**推论 23.4（非单射闭视图的存在边界）。** 存在非单射而闭合的精确观察，当且仅当 $r\ge3$ 且 $G$ 含满足 (23.8) 的奇特征二阶元。若存在该元，取常值查询，固定任意 $J$、$|J|\ge2$，在 $J$ 上发送 $G/\langle\tau\rangle$ 的单射标签，在其余坐标上发送 $G$ 的单射标签，即得此类观察；解码时由 $t$ 的特征确定所选陪集代表中 $\tau$ 的总系数奇偶，因 $2\tau=0$，目标 $Y$ 唯一。若无该元，定理23.3迫使一切精确闭观察都源注入。$H=\{0\}$ 和 $G=C_2$ 均包含唯一的奇特征二阶元，适用同一结论；空分支可任意填充，非空分支在 $r\ge3$ 时按 (23.13) 完全局部可达。这里没有字母表最优、转换工作空间、廉价更新或历史恢复的断言。

证明。构造的局部纤维正是 $\tau$-陪集，且所有活动坐标的差只有 $\tau$；特征约束确定这些差的奇偶，从而和式不变并能精确解码。定理23.3给出必要性。证毕。

**命题 23.5（分支变化的反例）。** 分支间更换陪集划分会破坏闭性，即使奇特征二阶元存在。取

$$
G=C_2\times C_2,
\qquad (\alpha,\beta)\in G,
\qquad \chi(\alpha,\beta)=\alpha,
\qquad r=3,
\tag{23.18}
$$

取常值查询，并令两个发送者的回复为

$$
 e_i(x_i,t)=\beta_i+\alpha(t)\alpha_i\pmod2\qquad(i=2,3).
\tag{23.19}
$$

固定 $t$ 的陪集周期为 $\tau(t)=(1,\alpha(t))$，随分支改变。解码器可取

$$
Y_\alpha=\alpha(t),
\qquad
Y_\beta=\beta(a)+e_2+e_3+\alpha(t)\bigl(\alpha(t)+\alpha(a)\bigr)\pmod2.
\tag{23.20}
$$

令 $v=(1,0)$、$s=(0,0,0,0)$、$s'=(0,v,v,0)$，并取 $d=(v,0,0,0)$。直接计算得

$$
O(s)=O(s')=(0,0,0,0),
\qquad
O(s+d)=(v,v,0,0),
\qquad
O(s'+d)=(v,v,1,1),
\tag{23.21}
$$

而

$$
F(s+d)=F(s'+d)=(v,v).
\tag{23.22}
$$

所以不存在确定性 $V_d$。这也说明仅有逐分支的非单射形式不足以替代固定的全局 $J,\tau$。

证明。式 (23.20) 中 $\alpha(Y)=\alpha(t)$；又 $\alpha_2+\alpha_3=\alpha(t)+\alpha(a)$，代入 (23.19) 即得 $\beta(Y)$，故观察精确。对 $s,s'$ 有 $\alpha(t)=0$，两回复均为零；平移后共同有 $t=v$，此时 $\alpha(t)=1$，$s+d$ 的两回复为 $(0,0)$，而 $s'+d$ 的两回复为 $(1,1)$。两者的 $(Y,t)$ 均为 $(v,v)$，故 (23.21)--(23.22) 成立。证毕。

**命题 23.6（与成对任务 $F=(Y,t)$ 的关系及第20节边界）。** 令

$$
F:S\to F(S),\qquad F(x,h)=(Y,t),
\qquad
L=\{(u,k):\textstyle\sum_i u_i=0,\ k=0\}.
\tag{23.23}
$$

则 $F(S)=\{(y,t):t-y\in H\}$，$|F(S)|=|G||H|$，且其直接闭更新为

$$
U_{(u,k)}(y,t)=\left(y+\sum_i u_i,\ t+\sum_i u_i+k\right).
\tag{23.24}
$$

每个精确观察都有因子化 $F=\pi\circ O$，其中 $\pi(a,t,m_2,\ldots,m_r)=(D(a,t,m_2,\ldots,m_r),t)$。若 $O$ 闭合，则

$$
S\longrightarrow S/K\ \widetilde{\longrightarrow}\ O(S)\longrightarrow S/L\ \widetilde{\longrightarrow}\ F(S)
\tag{23.25}
$$

是等变因子链，且 $K\subseteq L$；$O$ 是重标记的商观察，不必是群同态。$F$ 的闭态空间与 $O$ 的闭性是两个不同问题。

在第20节的 $S=C_4^3\times C_2$ 中，补偿嵌入是 $h\mapsto2h$ 于 $H=\{0,2\}\le C_4$，所以没有满足 (23.8) 的奇特征二阶元。因而 $r=3$ 的精确闭 $O$ 必须恢复全部 $128$ 个来源；20.4 的每个精确二元反馈快照有 $64$ 个观察、每条两点纤维，故都不闭合，而 $F$ 仍是八态闭消费者。命题20.7保留为先前的具体见证，此处不另立新例。

证明。给定 $y\in G$ 和 $h\in H$，取 $t=y+h$ 即得 $F(S)$；(23.24) 由 (23.3) 直接计算并保持 $t-y\in H$。精确性给出 $F=\pi\circ O$。闭合时命题23.2把 $O(S)$ 识别为 $S/K$，而 $F$ 的核正是 $L$，故得到 (23.25)。在 $C_4$ 中所有奇元的两倍都是 $2\ne0$，所以不存在奇特征二阶元；定理23.3与命题20.4遂给出所述第20节结论。证毕。

## 23.99 追加锚

## 23.100 闭性陈述的范围与投影步骤补充

**命题 23.101（23.3—23.5的范围澄清）。** 在定义23.1的同一实际来源上，作如下补充。

1. 命题23.5开头的“分支间更换陪集划分会破坏闭性”应读为“分支间更换陪集划分**可以**破坏闭性”，不是对所有观察的全称断言，尤其不适用于来源单射的观察。其式(23.18)—(23.22)所展示的反例仍然正确；但在同一 $G=C_2\times C_2$、$\chi(\alpha,\beta)=\alpha$、$r=3$ 和常值查询下，取 $e_2(x_2,t)=\beta_2+\alpha(t)\alpha_2$、$e_3(x_3,t)=x_3$，则发送者 $i=2$ 的配对随 $t$ 改变，而整个 $O$ 来源单射且闭合。
2. 推论23.4的 $H=\{0\}$ 退化情形是指环境群 $G\cong C_2$，其唯一非零元为奇特征二阶元；并非说 $H$ 含有该元。事实上 $H=\ker\chi$ 不含任何奇特征元素。
3. 定理23.3在式(23.17)后的局部碰撞步骤须选取 $j\in J$ 且 $j\ne i$，构造两条实际相同观察的来源，再用它们的差属于 $K$，在 $i\notin J$ 时得到第 $i$ 坐标投影的矛盾；当 $i\in J$ 时，所需的不同下标由 $|J|\ge2$ 保证。

证明。先证第一项。以下二元坐标的运算均在 $C_2$ 中。固定 $t$ 时，$e_2$ 的每条纤维恰为 $\{x,x+(1,\alpha(t))\}$，故在 $\alpha(t)=0,1$ 两类可达分支中配对不同。由于同一来源满足 $h\in H$ 和 $t=a+x_2+x_3+h$，观察 $o=(a,t,m_2,x_3)$ 给出

$$
\alpha_2=\alpha(t)+\alpha(a)+\alpha_3,
\qquad
\beta_2=m_2+\alpha(t)\alpha_2,
\qquad
x_2=(\alpha_2,\beta_2),
\qquad
Y=a+x_2+x_3,
\qquad
h=t-Y.
$$

这些等式恢复原来的全部来源，记恢复映射为 $R:O(S)\to S$，则 $R(O(s))=s$。任给允许的公开平移 $d\in S$，定义 $V_d(o)=O(R(o)+d)$；因 $S=G^3\times H$ 对加法封闭，右端仍取自同一实际来源空间，且 $V_d(O(s))=O(s+d)$。又 $R(V_d(o))=R(o)+d$，故 $V_e(V_d(o))=V_{d+e}(o)$。这直接证明了闭性，并反驳开头的全称读法；命题23.5原例让两个发送者都使用变化的配对，其相等观察在平移后分离的式(23.21)不受本构造影响。

第二项中，$H=\{0\}$ 使 $\chi$ 单射，再由满射性得 $\chi:G\cong C_2$。令 $g=\chi^{-1}(1)$，则 $g\ne0$、$\chi(g)=1$，且 $\chi(2g)=0$ 蕴含 $2g=0$。另一方面每个 $h\in H$ 都满足 $\chi(h)=0$，所以该奇元属于 $G\setminus H$。

最后补全第三项。沿用23.3在式(23.17)处已经得到的 $K\subseteq L$、$P_i$、固定 $\tau$ 与 $J$。固定一个可达分支 $\mathfrak b=(a,t,c)$，若 $f_i^{\mathfrak b}(x)=f_i^{\mathfrak b}(x+\delta)$、$\delta\ne0$，特征纤维上的单射性先给出 $\chi(\delta)=1$。选 $j\in J\setminus\{i\}$。令 $x_i=x$、$x_j=\epsilon\tau$、其余发送者坐标为零，其中 $\epsilon\in\{0,1\}$ 选成

$$
\epsilon=\chi(t)-\chi(a)-\chi(x),
\qquad
h=t-a-x-\epsilon\tau\in H.
$$

这实现了该分支的一条实际来源 $s$；$j$ 的两个可用输入相差 $\tau$，可选所需奇偶，并由式(23.15)保持其回复。再把 $x_i$ 改为 $x+\delta$、$x_j$ 改为 $x_j+\tau$、$h$ 改为 $h-(\delta+\tau)$。因 $\delta+\tau\in H$，所得 $s'$ 仍在 $S$ 中且具有同一 $a,t,c$；局部碰撞与 $j$ 的 $\tau$ 周期给出 $O(s')=O(s)$。因此式(23.6)给出 $s'-s\in K\subseteq L$，其坐标和为 $\delta+\tau=0$，即 $\delta=\tau$。若 $i\notin J$，该差的第 $i$ 坐标把非零 $\tau$ 放入 $P_i=\{0\}$，矛盾；若 $i\in J$，这排除了 $\tau$ 配对以外的碰撞。这里的奇偶选择和 $h$ 补偿都在实际来源上完成，没有把独立的形式输入指派当作联合可实现性。证毕。

## 23.199 追加锚

## 24. 整个快照的持续细化与全局周期

**定义 24.1（完整未来输出与全局周期）。** 设 $G$ 为有限阿贝尔群，
$\chi:G\twoheadrightarrow C_2$ 为满同态，$H=\ker\chi$，且 $r\ge2$；沿用定义23.1的来源

$$
S=G^r\times H,
\qquad Y=\sum_{i=1}^r x_i,
\qquad t=Y+h,
\qquad a=x_1,
$$

固定一个精确当前快照 $O:S\to\Omega$，并允许全部公开平移
$d=(u,k)\in G^r\times H$。给定有限输入词
$(d_1,\ldots,d_n)$，要求的输出是

$$
\bigl(O(s),O(s+d_1),O(s+d_1+d_2),\ldots,
 O(s+d_1+\cdots+d_n)\bigr),
\tag{24.1}
$$

其中 $n=0$ 的空词也必须输出当前的 $O(s)$。因此“整个重新评估”包含空继续和所有后续公开平移，不只包含当前目标 $Y$ 或成对消费者 $F=(Y,t)$。定义全局周期群

$$
K_*:=\{v\in S:\text{对所有 }s\in S,\ O(s+v)=O(s)\}.
\tag{24.2}
$$

它是 $S$ 的子群：$0$ 显然在其中；若 $v,w\in K_*$，则先后应用两次周期等式得 $v+w\in K_*$；由 $O(s)=O(s+v)$ 将 $s$ 换为 $s-v$ 得 $-v\in K_*$。因而 $S/K_*$ 是由快照诱导的最粗闭细化。

**命题 24.2（完整输出的商下界）。** 确定性实现由有限（或任意）状态集 $Q$、全源准备映射 $I:S\to Q$、确定性更新 $U_d:Q\to Q$ 以及输出映射 $\rho:Q\to\Omega$ 组成，并满足

$$
\rho\bigl(U_{d_n}\cdots U_{d_1}(I(s))\bigr)=O(s+d_1+\cdots+d_n)
\tag{24.3}
$$

对所有 $s$ 和所有有限词。这里 $Q$ 包含实现保留的全部历史；不能把另存历史当作免费存储。则

$$
|Q|\ge |S/K_*|.
\tag{24.4}
$$

等号可由全源准备的商实现达到：以 $I(s)=[s]$ 初始化，以
$U_d([s])=[s+d]$ 更新，并以 $\rho([s])=O(s)$ 输出。

证明。若 $I(s)=I(s')$，确定性和式(24.3)在空词上先给出
$O(s)=O(s')$，在任意后续词上给出

$$
O(s+d_1+\cdots+d_n)=O(s'+d_1+\cdots+d_n).
$$

令 $v=s'-s$；对固定的初始化来源对 $s,s'$，任给 $x\in S$，取单步继续 $d=x-s$，即得 $O(x+v)=O(x)$，所以 $v\in K_*$。因此不同的 $K_*$-陪集不能由同一状态初始化，得到(24.4)。反向，若 $s'-s\in K_*$，(24.2) 对每个有限平移词逐项保持(24.1)，故 $O$ 在陪集上定义良好。商上的 $U_d$ 和 $\rho$ 因而确定，并实现(24.3)。这给出下界的达到构造。这个论证正是 PROCESS_GEOMETRY Theorem 6.2(a)--(c) 所归属的通用残差最小性在本平移系统上的具体化；仓内冻结声明 finite_state_minimality（ObserverMemory/PredictionFactors/ReachableBehaviorMinimality）和 behavior_completion_is_least_stable_refinement（ObserverMemory/RefinementClosure/BehaviorCompletionMinimality）是相应的所有权锚。这里仅使用它们的确定性未来行为含义，不把它们的其他假设移作本节分类的证明。经典有限机背景见 Moore, *Gedanken-experiments on Sequential Machines* (1956), Theorem 4, pp.142--143；本系统的全部平移给出强连通的全源轨道。证毕。

**命题 24.3（只由当前快照初始化的充要条件）。** 设初始化被限制为
$I=j\circ O$，其中 $j:O(S)\to Q$ 只能读取当前快照。存在满足(24.3)的这种初始化，当且仅当 $O$ 自身在全部公开平移下闭合，即存在 $V_d:O(S)\to O(S)$ 使

$$
O(s+d)=V_d(O(s))\qquad(s\in S,d\in S).
\tag{24.5}
$$

证明。若 $O(s)=O(s')$，则 $I(s)=I(s')$；由确定性和空词、任意后续词，所有未来输出相等。取 $v=s'-s$ 即得 $v\in K_*$。反之，(24.2) 总说明 $K_*$-陪集内的当前快照相等，所以 $O$ 的相等关系必须恰为 $K_*$ 的陪集关系。于是

$$
V_d(O(s)):=O(s+d)
$$

与代表元无关，这就是(24.5)，亦即命题23.2的商作用。若(24.5)成立，命题24.2的商实现可取 $j(O(s))=[s]$；其良定义由(24.5)给出的相等关系及(24.2)成立。特别地，额外确定性记忆或计算不能区分具有相同初始 $O$ 的两个来源；全源准备是一个明确的来源访问假设，不能由当前快照自动授予。证毕。

**定义 24.4（发送者的全局周期）。** 现在设 $r\ge3$。对每个可达分支
$\mathfrak b=(a,t,c)$，写

$$
f_i^{\mathfrak b}(x):=e_i(x,t,c),
\qquad
\operatorname{Per}(f_i^{\mathfrak b})
 :=\{p\in G:\forall x\in G,\ f_i^{\mathfrak b}(x+p)=f_i^{\mathfrak b}(x)\}.
$$

定义发送者 $i$ 的全局周期为所有实际使用分支的交

$$
P_i:=\bigcap_{\mathfrak b\text{ 可达}}\operatorname{Per}(f_i^{\mathfrak b}).
\tag{24.6}
$$

空分支不进入交集。这里的“可达”仍按定义23.1：存在同一实际来源产生 $(a,t,c)$。

**定理 24.5（$r\ge3$ 时的全局周期分类）。** 对定义23.1的精确快照，令 $P_i$ 如(24.6)。则

1. 每个固定的可达 $(a,t,c)$ 分支中，每个发送者的每个 $x\in G$ 都实际可达；
2. 每个 $P_i$ 不是平凡群就是 $\{0,\tau_i\}$，其中
   $$
   \tau_i\ne0,\qquad \chi(\tau_i)=1,\qquad 2\tau_i=0;
   \tag{24.7}
   $$
3. 若 $P_i$ 与 $P_j$ 都非平凡，则 $\tau_i=\tau_j$。令
   $$
   J:=\{i\in\{2,\ldots,r\}:P_i\ne\{0\}\}.
   \tag{24.8}
   $$
   若 $J\ne\varnothing$，记这些非平凡 $P_i$ 的共同生成元为 $\tau$；$J=\varnothing$ 时不选择 $\tau$。

则全局周期群恰为

$$
K_*=\left\{(u,0):u_1=0,\ u_i\in P_i\ (i\ge2),\ \sum_{i=1}^r u_i=0\right\}.
\tag{24.9}
$$

因此 $|J|\le1$ 时 $K_*=\{0\}$；$|J|\ge2$ 时所有 $i\in J$ 共享同一奇特征二阶元 $\tau$，并且

$$
K_*\cong\{\text{在 }J\text{ 上取偶数个 }\tau\text{ 的开关}\},
\qquad |K_*|=2^{|J|-1}.
\tag{24.10}
$$

这里 $P_i$ 是跨所有使用分支的交集；某个发送者在单一分支中的部分碰撞或分支特定碰撞，若不在该交集中，就不增加 $K_*$。这正是全局周期与局部碰撞的区别。

证明。固定可达的 $a,t,c$。因 $r\ge3$，给定任一发送者 $i\ge2$ 的 $x_i=x$，可选另一个 $j\ne1,i$ 的特征值使

$$
\chi\!\left(a+\sum_{\ell=2}^r x_\ell\right)=\chi(t),
$$

其余坐标取零，随后唯一取 $h=t-a-\sum_{\ell=2}^r x_\ell\in H$。所以每个分支的每个局部输入都在同一实际支持中出现。

精确性还给出每个可达分支上的特征纤维单射性。若
$\chi(x)=\chi(x')$、$x\ne x'$ 且 $f_i^{\mathfrak b}(x)=f_i^{\mathfrak b}(x')$，取一个实现 $x_i=x$ 的实际来源，把 $x_i$ 改为 $x'$ 并把 $h$ 改为 $h-(x'-x)\in H$。$a,t$ 与全部回复不变而 $Y$ 改变非零的 $x'-x$，矛盾。因此每个 $f_i^{\mathfrak b}$ 在 $\chi^{-1}(0)$ 与 $\chi^{-1}(1)$ 上分别单射。

若 $0\ne p\in P_i\cap H$，把任一实际来源的 $x_i$ 改为 $x_i+p$ 并把 $h$ 改为 $h-p$。$a,t$ 和全部回复不变而 $Y$ 改变 $p$，与精确性矛盾。因此

$$
P_i\cap H=\{0\}.
\tag{24.11}
$$

若 $P_i$ 含非零 $p$，则 $p\notin H$，故 $\chi(p)=1$。于是 $2p\in H$ 且仍为周期，由(24.11)得 $2p=0$。若另有非零 $q\in P_i$，则 $p+q\in P_i\cap H$，故 $q=p$；这证明了第二项。

取非平凡 $P_i,P_j$ 的生成元 $p,q$。将同一实际来源的 $x_i,x_j$ 同时改为 $x_i+p,x_j+q$，并把 $h$ 改为 $h-(p+q)$；因为两个元均为奇特征，$p+q\in H$，且两个局部回复都保持不变。观察相同而目标改变 $p+q$，精确性迫使 $p+q=0$，即 $p=q$（它们均为二阶元）。

最后取任意 $v=(u,k)\in K_*$。首坐标相等给出 $u_1=0$；钟坐标相等给出

$$
\sum_i u_i+k=0.
$$

对每个实际分支和每个局部输入，观察相等给出 $u_i\in P_i$；精确解码又给出 $\sum_i u_i=0$，故 $k=0$，从而得到(24.9)。反向，若(24.9)成立，$a,t$ 不变，且每个局部回复由 $u_i\in P_i$ 保持，故 $O(s+v)=O(s)$。若 $J$ 中有开关，零和条件正好要求开关数为偶数，得到(24.10)。证毕。

**命题 24.6（全源准备的最小细化）。** 令 $J$ 如定理24.5；若 $J\ne\varnothing$，取其共同生成元 $\tau$，并定义

$$
p_\tau(x):=x-\chi(x)\tau\in H.
\tag{24.12}
$$

全源准备可以保留实际像中的状态

$$
R(s)=\left(a,t,\ (x_i)_{i\notin J,\ i\ge2},\ (p_\tau(x_i))_{i\in J}\right).
\tag{24.13}
$$

当 $J=\varnothing$ 时，投影元组为空，$R$ 保留 $a,t$ 和全部发送者坐标，不使用 $\tau$。其纤维恰为 $K_*$ 的陪集，因此状态数为 $|S|/|K_*|$，达到命题24.2的下界。对公开平移 $d=(u,k)$，对 $i\in J$ 记 $z_i=p_\tau(x_i)$，显式更新为

$$
\begin{aligned}
 a'&=a+u_1,\\
 t'&=t+\sum_i u_i+k,\\
 x_i'&=x_i+u_i &&(i\notin J),\\
 z_i'&=z_i+p_\tau(u_i) &&(i\in J).
\end{aligned}
\tag{24.14}
$$

其中只取(24.13)的实际像。$J\ne\varnothing$ 时，因为 $2\tau=0$ 且 $\chi$ 是同态，$p_\tau$ 是到 $H$ 的同态投影；$J=\varnothing$ 时没有投影坐标的更新。式(24.14)保持实际像。

证明。$J=\varnothing$ 时，由 $h=t-a-\sum_{i=2}^r x_i$ 可从 $R$ 恢复全部来源。若 $J\ne\varnothing$ 且两个来源有相同(24.13)，则 $a,t$ 及 $J$ 外坐标相同，而每个 $J$ 内坐标之差为 $0$ 或 $\tau$。由 $t-y\in H$，固定的 $a,t$ 及所有外部特征确定这些差中 $\tau$ 的总数为偶数；于是差属于(24.9)，且钟关系再给出 $h$ 不变。反向，$K_*$ 的任一偶数开关显然保持(24.13)。故纤维恰为 $K_*$ 陪集。

对 $i\in J$，所有使用分支的 $f_i$ 都以 $\tau$ 为周期，所以从 $z_i$ 任取一个满足 $p_\tau(x_i)=z_i$ 的代表，回复

$$
\widehat m_i=e_i(\widehat x_i,t,q(a,t))
$$

与代表无关，并且对原来源满足 $\widehat m_i=m_i$；$J$ 外部坐标则直接读出原来的 $x_i$ 并计算同一回复。这给出 $O$ 的确定性原标签读出。式(24.14)由坐标加法及 $J\ne\varnothing$ 时(24.12)的加性直接计算，因而与公开平移相容。$|R(S)|=|S|/|K_*|$，再用命题24.2即得最小性。若 $K_*=\{0\}$，$R$ 在来源上单射，状态数为 $|S|=|G|^r|H|$；当 $|J|=1$ 时，(24.13) 仍保存一个投影坐标，但其省去的特征位由 $a,t$ 和其余发送者坐标的总奇偶约束唯一恢复。保存完整来源是另一种达到该下界的表示，仍以全源准备为前提；这里没有由此推出通信、更新时间或其他操作成本的优势。证毕。

当 $r=2$ 时无需上述局部分类：精确性从当前 $(a,t)$ 与回复得到 $Y$，直接给出

$$
x_2=Y-a,\qquad h=t-Y,
$$

所以快照在来源上单射，$K_*=\{0\}$，并由命题24.2达到完整来源状态下界。

**命题 24.7（$C_2^2$ 家族的全局周期与比值）。** 取

$$
G=C_2^2,\qquad x_i=(b_i,z_i),\qquad \chi(b,z)=b,
\qquad H=\{(0,z):z\in C_2\}.
$$

令公共查询为 $c=b_1$，并令

$$
e_i(x_i,t,c)=(0,z_i+c\cdot b_i)\qquad(2\le i\le r).
\tag{24.15}
$$

这是精确快照；若回复的第二坐标记为 $w_i$，则解码器为

$$
Y=\left(b_t,\ z_1+\sum_{i=2}^r w_i+b_1\cdot b_t+b_1\right),
\tag{24.16}
$$

其中 $b_t=\chi(t)$。每条实际快照纤维有 $2^{r-2}$ 个来源，且

$$
|O(S)|=2^{r+3},\qquad
\min |Q|=|S|=2\cdot4^r,\qquad
\frac{\min |Q|}{|O(S)|}=2^{r-2}.
\tag{24.17}
$$

证明。由 $h\in H$，有 $b_t=\sum_i b_i$。又

$$
z(Y)=z_1+\sum_{i=2}^r z_i
      =z_1+\sum_{i=2}^r w_i+b_1\cdot\sum_{i=2}^r b_i
      =z_1+\sum_{i=2}^r w_i+b_1\cdot b_t+b_1,
$$

得到(24.16)。固定 $a,t$ 和全部 $w_i$ 后，每个 $z_i$ 由 $b_i$ 唯一确定，而 $b_2,\ldots,b_r$ 只受一个总奇偶方程约束，故有 $2^{r-2}$ 个选择；每个选择的 $h=t-Y\in H$ 唯一。$|S|=2\cdot4^r$，除以该纤维数即得 $|O(S)|=2^{r+3}$。

当 $c=0$ 时，(24.15) 的周期是 $(1,0)$；当 $c=1$ 时，周期是 $(1,1)$。两类分支都实际使用，故每个 $P_i$ 是这两个周期子群的交，即 $P_i=\{0\}$。定理24.5给出 $K_*=\{0\}$，命题24.2给出(24.17)的准备最小值。

这是一个实际的共同平移分离对。令 $r\ge3$，其余坐标均为零，取

$$
s:(x_1,x_2,x_3,h)=((0,0),(0,0),(0,0),(0,0)),
$$

$$
s':(x_1,x_2,x_3,h)=((0,0),(1,0),(1,0),(0,0)),
$$

则 $O(s)=O(s')$。令 $d$ 只把 $x_1$ 加上 $(1,0)$；此时两者的 $(a,t)$ 仍相同，但 $s+d$ 的两个回复为 $(0,0),(0,0)$，而 $s'+d$ 的两个回复为 $(0,1),(0,1)$，故 $O(s+d)\ne O(s'+d)$。证毕。

**命题 24.8（$r=4$ 的 proper-$J$ 部分碰撞）。** 在命题24.7的 $G=C_2^2$、$H=\{(0,z)\}$ 上取 $r=4$ 和单元素查询。令

$$
e_2(x_2)=z_2,\qquad e_3(x_3)=z_3,
$$

并令 $e_4=g$，其中三个标签 $A,B,C$ 满足

$$
g(0,0)=g(1,0)=A,\qquad g(0,1)=B,\qquad g(1,1)=C.
\tag{24.18}
$$

解码时 $b(Y)=b_t$，并由 $A$ 读出 $z_4=0$、由 $B,C$ 读出 $z_4=1$，再计算 $z(Y)=z_1+e_2+e_3+z_4$。因此协议精确，且

$$
|O(S)|=4\cdot4\cdot2\cdot2\cdot3=192,
\qquad |S|=2\cdot4^4=512.
\tag{24.19}
$$

这里 $P_2=P_3=\{0,(1,0)\}$，而 $P_4=\{0\}$；故 $J=\{2,3\}$，$|K_*|=2$，持续重新评估所需的准备最小值为 $512/2=256$。式(24.18)只有一对部分碰撞；它不是 $P_4$ 的全局周期，所以没有扩大 $K_*$。这个例子只用于区分全局周期和局部部分碰撞。

**命题 24.9（成对消费者及边界情形）。** 对同一来源，较粗的消费者

$$
F(x,h)=(Y,t)
$$

有

$$
F(S)=\{(y,t):t-y\in H\},\qquad |F(S)|=|G||H|,
\tag{24.20}
$$

并在公开平移下按

$$
(y,t)\longmapsto\left(y+\sum_i u_i,\ t+\sum_i u_i+k\right)
\tag{24.21}
$$

闭合。因此 $F$ 的持续状态数是 $|G||H|$；这是 $O$ 经 $O\to F$ 投影后的另一个任务，不是 $O$ 的全局周期细化。第20节的来源为 $C_4^3\times C_2$，其中 $H=\{0,2\}\le C_4$。在定义20.1规定的一位公共反馈、两条二值同时回复的协议类中，每个精确协议的快照由命题20.4有 $64$ 个观察值；$C_4$ 没有满足 $2\tau=0$ 且奇特征的元，所以定理24.5给出 $K_*=\{0\}$，整个 $O$ 的持续细化需要 $128$ 个完整状态；(24.20) 的 $F$ 只需 $|C_4||H|=8$ 个状态。

若 $H=\{0\}$、$G\cong C_2$，则 $t=Y$ 且唯一非零元是奇特征二阶元；以上局部可达性、周期交集和(24.9)--(24.14)仍逐字适用。单元素查询只固定一个 $c$ 值，并不只留下一个 $(a,t,c)$ 分支；(24.6)仍须遍历全部实际可达的 $t$ 和 $(a,t,c)$ 分支取交集，未使用分支不产生任何条件。对分支标签作重命名只是同时重命名 $c$ 和相应的局部映射，不改变(24.6)的周期交集或任何商计数。

以上结论是普通数学证明及针对性有限计算的结果；没有 Lean 核验或原创性声明。

## 24.99 追加锚

## 25. 合法平移子群下的上下文轨道与持续记忆

**定义 25.1（投影快照与受限公共作用）。** 设 $G$ 为有限阿贝尔群，$\chi:G\twoheadrightarrow C_2$ 为满同态，$H=\ker\chi$，$r\ge3$。取非空集合
$T\subseteq\{c\in G:\chi(c)=1,\ 2c=0\}$ 及预先固定、已知的选择映射 $\theta:G^2\to T$。沿用定义23.1的同一实际来源与整个快照消费者，专取如下局部编码：

$$
\begin{gathered}
S=G^r\times H,\qquad Y(s)=\sum_{i=1}^r x_i,\qquad
t(s)=Y(s)+h,\qquad a(s)=x_1,\qquad B(s)=(a(s),t(s)),\\
p_c(x)=x-\chi(x)c,\qquad c=\theta(B(s)),\qquad
O(s)=\bigl(a,t,p_c(x_2),\ldots,p_c(x_r)\bigr).
\end{gathered}
\tag{25.10}
$$

二元特征作为 $0,1$ 系数乘以二阶元。接收端读取 $(a,t)$ 并发出公共查询 $c$；发送者 $i\ge2$ 只读取自己的 $(x_i,t)$ 与 $c$，同时返回带下标的 $p_c(x_i)$。所有 $s\in S$ 都允许，查询由 $(a,t)$ 确定。

声明子群 $D\le S$ 为合法公共输入集；每个 $d=(u_1,\ldots,u_r,k)\in D$ 都是可在任何来源上执行的单步平移，所有有限输入词（含空词）均允许。要求在每个词的每个前缀之后读出整个重新评估的 $O$。输入改变上下文的同态及其像为

$$
\lambda:S\to G^2,\qquad
\lambda(u,k)=\left(u_1,\sum_i u_i+k\right),\qquad
\Lambda=\lambda(D),\qquad B(s+d)=B(s)+\lambda(d).
\tag{25.11}
$$

定义 $s\sim_D s'$ 当且仅当对每个 $n\ge0$ 和每个 $(d_1,\ldots,d_n)\in D^n$，有

$$
O(s+d_1+\cdots+d_n)=O(s'+d_1+\cdots+d_n).
\tag{25.12}
$$

称上下文 $B$ 为常值轨道上下文，若 $\theta$ 在 $B+\Lambda$ 上恒定。令 $\mathcal C_0$ 为这些上下文的集合，$\mathcal C_1=G^2\setminus\mathcal C_0$，$c_j=|\mathcal C_j|$。这里 $c_j$ 数上下文，不数轨道；$c_0+c_1=|G|^2$。两集合都是 $\Lambda$-轨道的并。

**定理 25.2（实际纤维与轨道上的完全保留或完全分离）。** 对定义25.1的编码，令 $q=2^{r-2}$。每个 $B=(a,t)\in G^2$ 与每个 $(z_2,\ldots,z_r)\in H^{r-1}$ 都由恰好 $q$ 个实际来源实现为观察 $(a,t,z_2,\ldots,z_r)$。接收端的精确解码为

$$
Y=p_c(a)+\sum_{i=2}^r z_i+\chi(t)c,\qquad c=\theta(a,t).
\tag{25.13}
$$

对每个 $c\in T$ 定义偶开关子群

$$
K_c=\left\{(0,\epsilon_2c,\ldots,\epsilon_rc,0)\in S:
 \epsilon_i\in C_2,\ \sum_{i=2}^r\epsilon_i=0\text{ 于 }C_2\right\}.
\tag{25.14}
$$

每条当前 $O$ 纤维是 $K_{\theta(B)}$ 的陪集，且对任意 $s\in S$，其未来行为类恰为

$$
[s]_{\sim_D}
=s+\bigcap_{\ell\in\Lambda}K_{\theta(B(s)+\ell)}
=\begin{cases}
s+K_{\theta(B(s))},& B(s)\in\mathcal C_0,\\
\{s\},& B(s)\in\mathcal C_1.
\end{cases}
\tag{25.15}
$$

因此在常值轨道上整条当前纤维保留；在非恒定轨道上每条当前纤维完全分离。这个编码族的未来等价关系对 $D$ 的依赖只通过 $\Lambda$。

证明。由 $2c=0$ 与 $\chi(c)=1$，映射 $p_c$ 是到 $H$ 的同态投影：二元系数相加产生的偶数倍 $c$ 为零，且 $p_c|_H=\mathrm{id}_H$、$\ker p_c=\{0,c\}$。这直接给出命题22.3式(22.17)所用的投影构造；以下不使用第22节对任意编码的 $r\ge4$ 分类。

固定 $a,t,z_2,\ldots,z_r$，所有候选坐标必须且可以写为

$$
x_1=a,\qquad x_i=z_i+\epsilon_i c\ (i\ge2),\qquad
\sum_{i=2}^r\epsilon_i=\chi(t)-\chi(a)\text{ 于 }C_2,\qquad
h=t-a-\sum_{i=2}^r x_i.
\tag{25.16}
$$

这个唯一的奇偶约束保证 $h\in H$；任取前 $r-2$ 个二元值，最后一个唯一确定，故恰有 $q$ 个选择。每个选择都在同一实际 $S$ 中，且产生指定观察；不同选择产生不同来源。又 $\chi(Y)=\chi(t)$，而 $p_c(Y)=p_c(a)+\sum_{i\ge2}z_i$，得到(25.13)，故这些选择的 $Y$、$h=t-Y$ 均相同。两个选择之差于是恰为(25.14)的偶开关；反向加上任一偶开关保持 $a,t$ 和全部回复。这同时证明实际像为 $G^2\times H^{r-1}$、纤维为所述陪集，且 $|K_c|=q$。

因为 $D$ 是子群，每个有限词的总增量仍在 $D$；每个 $d\in D$ 又本来就是合法单步输入。因此(25.12)等价于对全部 $d\in D$ 比较 $O(s+d)$ 与 $O(s'+d)$，其中 $d=0$ 也比较当前观察。不同当前观察已经由空词分离。若当前观察相同，记 $B=B(s)=B(s')$、$c=\theta(B)$、$v=s'-s\in K_c$。对同一个实际合法 $d$，两来源仍有共同上下文 $B+\lambda(d)$，其差仍为 $v$。刚证出的纤维公式给出

$$
O(s+d)=O(s'+d)
\iff v\in K_{\theta(B+\lambda(d))}.
\tag{25.17}
$$

遍历 $D$，其上下文像恰为 $\Lambda$，遂得(25.15)的交集式。若轨道上选择恒为 $c$，交集就是 $K_c$。若轨道非恒定，可取 $\ell\in\Lambda$ 使 $c'=\theta(B+\ell)\ne c$，并按 $\Lambda=\lambda(D)$ 取一个实际 $d=(u,k)\in D$ 满足 $\lambda(d)=\ell$。由于 $\{0,c\}\cap\{0,c'\}=\{0\}$，有 $K_c\cap K_{c'}=\{0\}$，交集因而平凡。

分离也可在原标签上直接看见。若 $v=(0,\epsilon_2c,\ldots,\epsilon_rc,0)\ne0$，则在这同一个 $d$ 之后，第 $i$ 个回复之差为

$$
p_{c'}(x_i+\epsilon_i c+u_i)-p_{c'}(x_i+u_i)
=p_{c'}(\epsilon_i c)=\epsilon_i(c-c').
\tag{25.18}
$$

至少一个 $\epsilon_i=1$，故该带下标回复改变。公共输入的各 $u_i,k$ 可以相关；它们在两来源的回复差中抵消，并通过同一个 $\lambda(d)$ 确定查询，没有另选不合法的坐标平移。证毕。

**推论 25.3（完整状态最小值与初始化访问条件）。** 考虑有限完整状态集 $M$、全源初始化 $\iota:S\to M$、读出 $g:M\to O(S)$ 及确定性更新 $V_d:M\to M$，满足对所有来源和有限词

$$
g\bigl(V_{d_n}\cdots V_{d_1}(\iota(s))\bigr)
=O(s+d_1+\cdots+d_n).
\tag{25.19}
$$

完整状态包含实现保留并用于将来响应的全部历史；初始化之后只接收声明的公共输入，不重新读取来源或其他隐藏信息。令 $M_{\rm reach}$ 为从全部 $\iota(s)$ 经全部有限词到达的状态并。在允许全源准备时，其精确最小值为

$$
N_D:=\min |M_{\rm reach}|
=|H|^{r-1}(c_0+q c_1),\qquad q=2^{r-2}.
\tag{25.20}
$$

若准备只能读取当前快照，即要求 $\iota=j\circ O$，则这种持续实现存在当且仅当 $\mathcal C_1=\varnothing$。全源准备与此快照访问限制是不同条件。

证明。通用的“所有来源及合法残余的行为并”最小性归属 [PROCESS_GEOMETRY 定理6.2(c)](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)；这里对本编码的全部初始化直接给出下界，不将单锚轨道的最小值相加。若 $\iota(s)=\iota(s')$，无论状态怎样存储历史，确定性都使同一输入词之后的状态及读出相同。由(25.19)，必有 $s\sim_D s'$。因此从每个未来类选一个代表，它们的初始完整状态两两不同，且均在 $M_{\rm reach}$ 中。这里没有假定竞争实现的 $V_d$ 满足群作用律，也没有假定状态只依赖词的总增量。

定理25.2给出：每个 $\mathcal C_0$ 上下文有 $|H|^{r-1}$ 个类，每个 $\mathcal C_1$ 上下文有 $q|H|^{r-1}$ 个单点类。不同上下文已由当前观察分离，所以这些计数可以相加，得到(25.20)的下界。

为达到下界，取以下带标签的实际并为状态集，并按所示映射初始化：

$$
\begin{gathered}
M_*=\{(0,O(s)):B(s)\in\mathcal C_0\}
\ \sqcup\ \{(1,s):B(s)\in\mathcal C_1\},\\
\iota_*(s)=
\begin{cases}(0,O(s)),&B(s)\in\mathcal C_0,\\(1,s),&B(s)\in\mathcal C_1.\end{cases}
\end{gathered}
\tag{25.21}
$$

第一部分直接读出所存的 $O$，第二部分从所存当前来源计算 $O$。在第一部分，记当前快照为 $(a,t,z_2,\ldots,z_r)$、$c=\theta(a,t)$，对 $d=(u,k)\in D$ 更新为

$$
(a,t,z_2,\ldots,z_r)\longmapsto
\left(a+u_1,\ t+\sum_i u_i+k,
z_2+p_c(u_2),\ldots,z_r+p_c(u_r)\right).
\tag{25.22}
$$

轨道常值性保证更新后的查询仍为 $c$，投影加性保证右端就是 $O(s+d)$。在第二部分更新 $(1,s)\mapsto(1,s+d)$。轨道类型被 $D$ 保持，故两种更新都留在对应的实际像中，逐词归纳即得(25.19)。每个表示的状态已经在某个来源的初始化时出现，因而可达状态数就是(25.20)。标签由上下文确定，不能再乘一个独立的模式数。

若 $\mathcal C_1=\varnothing$，上述构造只需 $O$，故可令 $j(o)=(0,o)$。反之，若 $B\in\mathcal C_1$，由 $r\ge3$ 有 $q\ge2$，该上下文的任一观察纤维包含两个不同实际来源；定理25.2使它们未来可分。$j\circ O$ 却给它们相同初态，确定性无法满足(25.19)。增加确定性记忆的容量也不改变这同一初始化障碍。

若把本编码改取 $r=2$，(25.16)只有一个二元值，已由 $a,t$ 唯一确定。公式(25.13)仍给出 $Y$，继而 $x_2=Y-a$、$h=t-Y$，所以 $O$ 来源单射。此时任意 $D$、$\theta$ 都允许快照初始化：先由 $O$ 恢复当前来源，再按来源加法更新；空词已有 $|S|$ 个不同输出，最小值为 $|S|$。因此“所有轨道常值”的必要性专属于 $r\ge3$。

边界条件也由同一证明确定。$D=\{0\}$ 时每条上下文轨道为单点；$\theta$ 恒定或 $T$ 为单元素时每条轨道也恒定，均有 $N_D=|O(S)|=|G|^2|H|^{r-1}$。若 $H=\{0\}$，满同态 $\chi$ 是 $G\cong C_2$ 的同构，$T$ 只能含唯一奇二阶元；全部回复为零而 $(a,t)$ 的四个值均可达，故整个 $O$ 的持续任务恰需四态。若 $D=S$，对任意 $(b_1,b_2)\in G^2$ 取 $u_1=b_1,u_2=b_2-b_1$、其余增量及 $k$ 为零，得 $\Lambda=G^2$；故 $\theta$ 全局恒定时为上述 $|O(S)|$，否则为 $|S|$。若 $D\subseteq D'$，每个 $D$ 词也是 $D'$ 词，故 $\sim_{D'}\subseteq\sim_D$、$N_D\le N_{D'}$。式(25.20)计算给定作用的精确值，不断言两个端点之间的每个整数都能实现，也不引入单条纤维的部分分裂。

成对消费者 $F=(Y,t)$ 仍是命题23.6、24.9的另一任务：其实际像有 $|G||H|$ 个值，式(23.24)的显式更新限制到任意 $D$ 仍适用，空词下界仍为该实际像大小。因此其最小完整状态数对每个 $D$ 都是 $|G||H|$，并可由(25.13)从快照初始化。在 $H=\{0\}$ 时它只需两态。证毕。

**命题 25.4（七十二态的受限作用见证）。** 取 $G=C_2^2$，$\chi(\alpha,\beta)=\alpha$，$H=\{0\}\times C_2$，$r=3$。记

$$
v=(1,0),\qquad w=(0,1),\qquad
\tau_0=v,\qquad \tau_1=v+w,\qquad T=\{\tau_0,\tau_1\},
\qquad
\theta(B)=\begin{cases}\tau_1,&B=(0,0),\\\tau_0,&B\ne(0,0),\end{cases}
\tag{25.23}
$$

并令 $d=(v,v,0,0)\in G^3\times H$、$D=\{0,d\}$。则有十六个上下文、八条上下文轨道，$c_0=14,c_1=2$，且

$$
|S|=128,\qquad |O(S)|=64,\qquad
N_D=72,\qquad (N_{\{0\}},N_D,N_S)=(64,72,128).
\tag{25.24}
$$

其 $D$-未来分割有五十六个双点类、十六个单点类；它对 $D$ 的平移稳定，却不是某一个 $S$ 子群的全局陪集分割。

证明。$d$ 为二阶元，且 $\lambda(d)=(v,0)$，故上下文作用为 $(a,t)\mapsto(a+v,t)$，十六个上下文两两配对。恰有轨道 $\{(0,0),(v,0)\}$ 上的 $\theta$ 非恒定，其余七条轨道恒为 $\tau_0$。每个上下文有 $|H|^2=4$ 个观察、每条观察纤维有 $q=2$ 个来源。十四个常值上下文贡献 $14\cdot4=56$ 个双点未来类，两个非恒定上下文贡献 $2\cdot4\cdot2=16$ 个单点类，总数为 $72$；这些类共含 $56\cdot2+16=128$ 个来源。

具体取实际来源 $s=(0,0,0,0)$ 与 $s'=(0,\tau_1,\tau_1,0)$。两者的 $a=t=0$、查询为 $\tau_1$、回复均为 $(0,0)$，故 $O(s)=O(s')$。共同合法输入 $d$ 后，两者上下文为 $(v,0)$，查询变为 $v$；$s+d$ 的回复为 $(p_v(v),p_v(0))=(0,0)$，而 $s'+d$ 的回复为 $(p_v(\tau_1+v),p_v(\tau_1))=(w,w)$，确实分离。

未来等价对 $D$ 稳定，因为对任意 $e,d'\in D$，继续增量 $e+d'$ 仍在 $D$；或者直接用(25.21)--(25.22)的良定义更新。若这些类是某个子群 $K\le S$ 的全部陪集，类数必须为 $[S:K]$ 并整除 $128$，但 $72$ 不整除 $128$，矛盾。$D=0$ 时保留全部 $64$ 条当前纤维；$D=S$ 时 $\Lambda=G^2$ 且 $\theta$ 非恒定，全部 $128$ 个来源分离，得到(25.24)的作用链。这里失效的是额外要求单个全局 $S$-陪集表示；按声明的 $D$ 取未来行为商仍给出推论25.3的最小实现。证毕。

## 25.99 追加锚

## 26. 单向循环钟的有限时域、游程几何与倒计时记忆

**定义 26.1（显式编码与有限时域）。** 固定偶数 $m\ge2$、$r\ge3$，令 $C_m=\mathbb Z/m\mathbb Z$，并规定

$$
G=C_2\times C_m,\quad \chi(b,z)=b,\quad H=\{0\}\times C_m,\quad
S=G^r\times H,\quad Y=\sum_{i=1}^r x_i,\quad t=Y+h,\quad a=x_1.
\tag{26.10}
$$

记 $z:G\to C_m$ 为第二坐标，$f:C_m\to C_2$ 为公开的固定函数。接收端选择 $c=\tau_{f(z(a))}$，其中

$$
\tau_0=(1,0),\qquad \tau_1=(1,m/2),\qquad
\Delta=\tau_1-\tau_0=(0,m/2)\ne0,\qquad
p_c(x)=x-\chi(x)c.
\tag{26.11}
$$

每个发送者 $i=2,\ldots,r$ 仅回复 $p_c(x_i)\in H$；所需输出始终是整个快照

$$
O(s)=(a,t,p_c(x_2),\ldots,p_c(x_r)).
\tag{26.12}
$$

查询 $c$ 已由 $a$ 与公开 $f$ 确定。此处采用命题22.3的全商编码公式；该节的分类假设是 $r\ge4$，本节不将其分类结论移用到 $r=3$，而在下文直接构造全部实际来源。

唯一单位动作是

$$
g=(0,1),\qquad d=(g,-g,0,\ldots,0;0),\qquad D(s)=s+d.
\tag{26.13}
$$

合法词仅为 $d$ 的非负次数重复，正重复的每一步费用为一；即使某个平移可由多步达到，也不将其另列为单位动作。$Y,t,h$ 在动作下不变，$a$ 的相位每步增加一。对 $n\ge0$，定义

$$
F_n(s)=(O(s),O(Ds),\ldots,O(D^ns)),\qquad
sR_ns'\ \Longleftrightarrow\ F_n(s)=F_n(s'),\qquad
N_n=|S/R_n|.
\tag{26.14}
$$

时域包含初始输出，故 $n$ 步对应 $n+1$ 个快照。此为既有 [FiniteHorizonKernelRecurrence](../../../D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.lean) 中 `finiteHorizonKernel` 的单更新含义；最短分离词的通用概念归属 [ControlledDistinguishingDepth](../../../D5/S3/ObserverMemory/Algorithms/ControlledDistinguishingDepth.lean) 的 `shortestDistinguishingDepth`。以下计算这个编码的实际纤维与精确深度，不另设通用核或最短词定理。

**定理 26.2（奇偶纤维、首次分离与游程尾数）。** 置 $q=2^{r-2}$、$C=4m^r$，并令

$$
A_n=\#\{z\in C_m:f(z)=f(z+1)=\cdots=f(z+n)\}.
\tag{26.15}
$$

任给 $a,t\in G$ 和 $u_2,\ldots,u_r\in H$，它们均组成实际快照；其原像恰由下式给出：

$$
x_1=a,\qquad x_i=u_i+\epsilon_i c\ (2\le i\le r),\qquad
\bigoplus_{i=2}^r\epsilon_i=\chi(t)-\chi(a),\qquad
h=t-Y.
\tag{26.16}
$$

每条纤维恰有 $q$ 个来源，且 $a,Y,t,h$ 均在其中固定。固定接收端相位 $z(a)=z$ 时，实际快照数恰为 $C$。同一快照纤维在 $R_n$ 下或者全部保持合并，或者全部分成单点；前者恰在式(26.15)的常值窗口发生。因此

$$
N_n=C\bigl[qm-(q-1)A_n\bigr],\qquad
N_0=4m^{r+1},\qquad |S|=2^r m^{r+1}.
\tag{26.17}
$$

若 $f$ 非常值，定义有向首次改变深度与循环极大常值游程长度为

$$
\delta(z)=\min\{j\ge1:f(z+j)\ne f(z)\},\qquad
\ell_1,\ldots,\ell_b,\qquad L=\max_j\ell_j.
\tag{26.18}
$$

则 $1\le\delta(z)\le L\le m-1$，且

$$
A_n=\sum_{j=1}^b\max(\ell_j-n,0),\qquad
N_n=|S|\ \Longleftrightarrow\ n\ge L.
\tag{26.19}
$$

同一相位 $z$、同一初始快照内的任意不同实际来源对，最短分离步数恰为 $\delta(z)$。具有不同初始快照的来源对已在深度零分离。在相位 $z$，取得两种选择子对应的两个快照，便可恢复全部发送端坐标及 $h$；首次取得所需改变的选择子恰需 $\delta(z)$ 次合法动作。对已经给出的两个端点，逆算用 $O(r)$ 次群运算和比较，不由此断言算术最优性、位时间、通信量或物理用时。

证明。两个 $\tau$ 均满足 $2\tau=0$、$\chi(\tau)=1$，所以 $p_c$ 是到 $H$ 的同态投影；$p_c(x)=u$ 当且仅当 $x=u+\epsilon c$，$\epsilon\in C_2$。因为 $h\in H$，实际来源必须满足式(26.16)的唯一奇偶方程。反向，任取满足该式的位串，则 $\chi(t-Y)=0$，故由该式确定的 $h$ 确在 $H$ 中。每个位串给出不同来源，且全部原像均已列出。位串共有 $2^{r-2}$ 个，这一论证直接适用于两个发送者的 $r=3$ 情形。

令 $b_0=\chi(t)-\chi(a)\in C_2$，将其作为 $0,1$ 系数。由于 $2c=0$，式(26.16)同时给出

$$
Y=a+\sum_{i=2}^r u_i+b_0c,\qquad h=t-Y.
\tag{26.20}
$$

故纤维内这些量固定。两个原像的位串之差为 $\eta=(\eta_2,\ldots,\eta_r)$，且 $\bigoplus_i\eta_i=0$；其实际差为发送端的偶数个 $c$ 翻转，接收端与 $h$ 均不动。这使纤维成为偶校验群 $\{\eta\in C_2^{r-1}:\bigoplus_i\eta_i=0\}$ 的自由传递作用空间。计数时，固定 $z$ 后 $a$ 有两种、$t$ 有 $2m$ 种、回复元组有 $m^{r-1}$ 种，且刚才的构造证明每一种均实际可达，故 $C=2(2m)m^{r-1}$。

现固定同一初始纤维中的实际来源对 $s,s'$，不能在不同时刻另换来源来拼接碰撞。令 $c_j=\tau_{f(z+j)}$。第 $j$ 步两来源中发送者2都承受同一个已知平移 $-jg$，其他发送者不动。该公共平移在回复差中相消，并有

$$
p_{c_j}(x_i'+v_i)-p_{c_j}(x_i+v_i)
 =\eta_i(c-c_j),\qquad
v_2=-jg,\quad v_i=0\ (i\ge3).
\tag{26.21}
$$

这里 $\chi(v_i)=0$。若 $c_j=c$，全部差为零；若 $c_j\ne c$，则 $c-c_j=\Delta$，任何非零 $\eta$ 至少给一个非零回复差。两来源的 $a+jg,t$ 始终相同。因而常值窗口内整条纤维保持合并，一遇不同选择子即分成单点；以后即使选择子返回，已包含首差的整段迹也不再合并。不同初始快照本来就属于不同的 $R_n$ 类。对 $A_n$ 个相位各计 $C$ 类，其余 $m-A_n$ 个相位各计 $Cq$ 类，得到式(26.17)。$A_0=m$ 给出 $N_0$，而 $|G|^r|H|=(2m)^rm$ 给出来源数。

在一条长度为 $\ell$ 的循环极大常值游程内，由起点到首次改变的有向距离依次为 $\ell,\ell-1,\ldots,1$。恰有 $\max(\ell-n,0)$ 个起点满足 $n<\delta(z)$，这与式(26.15)相同，求和得式(26.19)。非常值使每条游程都有实际边界，所以最大长度至多 $m-1$。由 $q>1$，全部来源恢复恰要求 $A_n=0$，也就是 $n\ge L$。

分离深度还有直接的两翻转见证。任取相位 $z$，置 $a=(0,z)$，令 $s$ 的全部发送端坐标及 $h$ 为零；令 $s'$ 保持相同的 $a,h$，仅置 $x_2'=x_3'=c=\tau_{f(z)}$。两个来源均实际存在，且两者 $Y=t=a$、初始回复全零。由式(26.21)，其首次分离恰在 $\delta(z)$。对任意 $1\le j\le L$，取最长游程中距下一边界恰为 $j$ 的相位，就取得延迟恰为 $j$ 的实际见证；故最大深度不是仅由计数给出的上界。

恢复算法也保持同一来源。取 $j=\delta(z)$，将两个端点中的回复记为 $u_i^{(0)},u_i^{(j)}$，并先撤去发送者2的已知平移：

$$
\widetilde u_i^{(j)}=
\begin{cases}u_2^{(j)}+jg,&i=2,\\u_i^{(j)},&i\ge3,\end{cases}
\qquad
\widetilde u_i^{(j)}-u_i^{(0)}=\chi(x_i)(c-c_j)=\chi(x_i)\Delta.
\tag{26.22}
$$

$0$ 与 $\Delta$ 不同，故逐一确定 $\epsilon_i=\chi(x_i)$，再用 $x_i=u_i^{(0)}+\epsilon_i c$ 及 $h=t-\sum_i x_i$ 恢复初始来源。任意已知时刻的两个不同选择子端点也可按同法先撤去各自平移。每个发送者用常数次群运算和比较，最后求和，给出所述 $O(r)$ 算术上界。唯一动作字母保证长度 $j$ 的词只有 $d^j$；较短迹对上述不同来源相同，所以不能提前取得来源恢复。

若 $n<\delta(z)$，残余仍为式(26.16)的整个奇偶作用空间，且其共同迹可仅由初始快照内部计算：

$$
O(D^js)=(a+jg,t,u_2-jg,u_3,\ldots,u_r)\qquad(0\le j\le n).
\tag{26.23}
$$

这给出一个可计算的残余，而非默认观察者能再查隐藏来源。若 $f$ 恒定，式(26.23)对所有 $j\ge0$ 都成立，$A_n=m$、$N_n=N_0<|S|$，任何有限或无限迹均不能恢复全来源。恒定圆周没有首次改变边界，不能把它当作一条长度 $m$ 的普通有限游程代入式(26.19)。证毕。

**定理 26.3（标量剖面的可恢复部分与带标签关系的严格区别）。** 固定偶数 $m\ge2$ 及 $r\ge3$，限制于非常值 $f$。标量序列 $(N_n)_{n\ge0}$ 恰确定无颜色的游程长度多重集；两个函数的该剖面相等，当且仅当其无颜色游程多重集相等。已知 $N_0,\ldots,N_m$ 即足够，具体恢复式为

$$
A_n=\frac{qm-N_n/C}{q-1},\qquad
\#\{i:\ell_i=j\}=A_{j-1}-2A_j+A_{j+1}\quad(1\le j\le m-1).
\tag{26.24}
$$

这一剖面不能一般恢复循环次序，即使将旋转、反射和整体补色视为同一类。相反，带相位标签的 $\delta(z)$ 确定边界边及 $f$ 的整体补色类；在固定来源坐标与固定 $\tau_0,\tau_1$ 标签下，仅带来源标签的关系 $R_0\subseteq S\times S$ 就精确确定 $f$。单独一个已经饱和的相等关系则不必保留 $f$。上述对象均指给定的模型数据；它们不是从一条来源轨迹免费获得的额外访问能力，且 $f$ 从定义起就是公开的。

证明。式(26.17)及 $q-1>0$ 给出 $A_n$。对一个整数游程长度 $\ell$，函数 $a_n=\max(\ell-n,0)$ 在 $j\ge1$ 的二阶差分 $a_{j-1}-2a_j+a_{j+1}$ 恰在 $j=\ell$ 时为一，其余为零。逐项求和得到式(26.24)。非常值保证 $\ell\le m-1$，所以只需到 $A_m=0$ 为止；反向，游程多重集由式(26.19)决定全部 $A_n$，继而决定全部 $N_n$，得到充要性。这一统计计算整个窗口均为常值的起点数，不是仅比较窗口两端的通常循环自相关：端点相同可以在中间经过两次改变，故不能用端点相同数替代 $A_n$。

一个具体的次序损失实例取 $m=10,r=3$，按相位 $0,\ldots,9$ 写出

$$
f=0110001111,\qquad f'=0111001111.
\tag{26.25}
$$

两者从相位零起的循环游程依次为 $(1,2,3,4)$ 与 $(1,3,2,4)$。由四个游程逐项求和，两者都有

$$
(A_0,A_1,A_2,A_3,A_4,\ldots)=(10,6,3,1,0,\ldots),\qquad
(N_0,N_1,N_2,N_3,N_4,\ldots)=(40000,56000,68000,76000,80000,\ldots).
\tag{26.26}
$$

这里 $q=2,C=4000$。然而唯一的长度一游程，在前者的两个邻居长度为 $\{2,4\}$，在后者为 $\{3,4\}$；旋转、反射及补色都保留这一无序邻居对，故两词不在同一类。也可由无序颜色总数分别为 $\{4,6\}$ 与 $\{3,7\}$ 看出不等价。本例仅给出损失次序的实际见证，不主张长度最小。

对带标签深度，有 $\delta(z)=1$ 当且仅当边 $z\to z+1$ 跨越颜色边界。任选 $f(0)$ 后沿整个圆周依次在这些边翻转，便恢复全部 $f$；两个起始选择恰互为整体补色。数据来自实际循环词，故绕圆一周相容。

对带来源标签的 $R_0$，固定任意 $z$，比较两个明确指定的来源：两者均有 $a=(0,z),h=0$，第一个的全部发送端为零，第二个仅将 $x_2=x_3=\tau_0$，其余仍为零。$2\tau_0=0$ 使两者的 $t$ 均为 $a$。若 $f(z)=0$，两者全部回复均为零；若 $f(z)=1$，第二个来源在发送者2、3的回复均为 $p_{\tau_1}(\tau_0)=\Delta\ne0$。因此

$$
(s_z,s'_z)\in R_0\quad\Longleftrightarrow\quad f(z)=0.
\tag{26.27}
$$

这些都是 $S$ 中实际来源，故关系数据逐相位决定 $f$，不需要不存在的反事实支持。此步骤要求至少两个发送者，也解释了 $r\ge3$ 的作用。另一方面，式(26.25)的两词均有 $L=4$，其带来源标签的 $R_4$ 都是同一 $S$ 上的对角关系，却有不同 $f$。所以一个饱和关系不足以反推此前的选择子；标量剖面的次序损失也不能推广为所有带标签商关系的损失。证毕。

**定义 26.4（一次全源准备的有限任务）。** 固定时域 $n$，一个确定性实现由完整状态集 $M$、一次准备映射 $I:S\to M$、读出 $\rho:M\to O(S)$ 与总更新 $U:M\to M$ 组成，满足

$$
\rho(U^jI(s))=O(D^js)\qquad(s\in S,\ 0\le j\le n).
\tag{26.28}
$$

准备时允许读取整个来源，之后输出由内部状态生成，不再观察隐藏来源。凡参与后继或读出的控制器、历史、计数器都属于 $M$，不能借免费外置时钟改变 $U$。$|I(S)|$ 是实际初始完整状态数，$|M|$ 是总载体容量；两者不同。若限制 $I=J\circ O$，称仅由初始快照准备。时域之后无输出正确性要求，也不要求发出额外停机符号。一般残余实现与最小性归属 [PROCESS_GEOMETRY 定理6.2](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)；其单锚可达版本见 [ReachableBehaviorMinimality](../../../D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.lean) 的 `finite_state_minimality`。下述全来源、有限任务的计数直接在定义26.4的量词下证明，不将单锚最小值相加。

**定理 26.5（初始下界、分级达到构造与固定时域闭性）。** 对定义26.4的任意实现，$|I(S)|\ge N_n$。存在达到该初始下界的实现，其完整载体、读出及更新为

$$
\mathcal M_n=\coprod_{k=0}^n\{k\}\times S/R_k,\qquad
I(s)=(n,[s]_n),\qquad \rho(k,[s]_k)=O(s),
\tag{26.29}
$$

$$
U(k,[s]_k)=
\begin{cases}
(k-1,[Ds]_{k-1}),&k>0,\\
(0,[s]_0),&k=0.
\end{cases}
\qquad
T_n=|\mathcal M_n|=\sum_{k=0}^nN_k.
\tag{26.30}
$$

每个等级均全部可达，$T_n$ 包含倒计时，是这一具体构造的总容量，不是总平稳载体容量的最小值声明。另有直接保存全来源的 $|S|$ 状态实现，可永久持续输出。

固定 $R_n$ 对来源动作 $D$ 稳定，当且仅当 $R_n=R_{n+1}$，在本有限模型中又当且仅当 $N_n=N_{n+1}$。对非常值 $f$ 及 $r\ge3$，该闭性恰从 $n=L$ 开始。在全部来源上，仅由初始 $O$ 准备可完成 $n=0$，但不能完成任意 $n\ge1$；若只要求一个固定初始相位 $z$ 的全部来源，则恰在 $n<\delta(z)$ 时可行。恒定 $f$ 的闭性从零开始，仅由 $O$ 可完成任意时域，但仍不恢复来源。

若将定义26.1单独改取 $r=2$，则 $q=1$，$O$ 已在来源上单射，所有 $N_n=|S|=4m^3$，全来源恢复与闭性深度均为零，仅由 $O$ 准备对所有时域充分；标量 $N_n$ 不再含游程信息。以上偶数 $m$ 的结论包括 $m=2$，不涉及 $r=1$。

证明。若 $I(s)=I(s')$，确定性使每次相同次数更新后的完整状态相等；由式(26.28)，$F_n(s)=F_n(s')$。从每个 $R_n$ 类选一个来源，它们的准备状态必须两两不同，故 $|I(S)|\ge N_n$。历史可以计入状态，但不能破坏这一推理；若输出还依赖来源侧的新观测，就不满足定义26.4。

式(26.14)使 $R_k\subseteq R_0$，所以式(26.29)的读出良定；$sR_ks'$、$k>0$ 时，原迹的时刻 $1,\ldots,k$ 相等，故 $DsR_{k-1}Ds'$，式(26.30)的下降更新也良定。归纳给出时刻 $j\le n$ 的状态为 $(n-j,[D^js]_{n-j})$，验证式(26.28)。零等级自环已经是总更新，无需增设任务后停机符号。初始像恰有 $N_n$ 个元素。固定 $k$，从所有 $s$ 的初始状态出发，经过 $n-k$ 步得到全部 $(k,[D^{n-k}s]_k)$；平移 $D$ 是双射，故这些正是该等级的全部状态。各等级不交，得到 $T_n$。

这个商构造具有不再查询来源的具体表示。对当前剩余时域 $k$、当前 $a$，公开 $f$ 决定窗口 $f(z(a)),\ldots,f(z(a)+k)$ 是否常值。若常值，定理26.2说明 $[s]_k$ 恰由 $O(s)$ 表示；若非常值，类为单点，可由 $O(s)$ 加 $r-2$ 个独立位 $\epsilon_2,\ldots,\epsilon_{r-1}$ 表示，余下的

$$
\epsilon_r=\chi(t)-\chi(a)-\sum_{i=2}^{r-1}\epsilon_i\quad\text{于 }C_2
\tag{26.31}
$$

确定全来源。后一分支每个实际快照恰有 $q$ 种表示，前一分支恰有一种，与式(26.17)逐等级计数一致；分支标志由已计入状态的 $k,a$ 及固定公开函数决定，不需另添来源信息。

若当前窗口常值且 $k>0$，下降一步后的窗口是原窗口的尾部，仍为常值，按式(26.23)即可从当前 $O$ 生成下一 $O$。若当前窗口非常值，存储的位串先恢复当前来源，内部施加 $D$、计算新快照，再按下一窗口是否常值保留或丢弃这些位；这没有重新读取外部隐藏来源。$D$ 的坐标平移均在 $H$，所以所存特征位在这一步也保持不变。等级零直接保持自身。由此在包含倒计时的完整载体上实现了式(26.30)。另一种实现取 $M=S,I=\mathrm{id},U=D,\rho=O$，给出总容量 $|S|$ 且对全部未来时刻正确。因此不能把 $T_n$ 或初始商未闭误报为所有有限任务机器的总容量最小值或不存在性；总容量的精确综合是另外的问题。

最后，有限核的首步递推在此写为

$$
R_{n+1}=R_0\cap(D\times D)^{-1}R_n,\qquad R_{n+1}\subseteq R_n.
\tag{26.32}
$$

它是定义26.1所引有限时域核递推的首步形式。若 $R_n$ 对 $D$ 稳定，则 $R_n\subseteq(D\times D)^{-1}R_n$，再用 $R_n\subseteq R_0$ 得 $R_n\subseteq R_{n+1}$，故相等。反之，相等时式(26.32)直接给稳定性。有限集合上一个分割细化另一个且类数相同，必没有任何类被拆开，故相等又等价于 $N_n=N_{n+1}$。非常值情形有

$$
N_{n+1}-N_n=C(q-1)\#\{j:\ell_j>n\},
\tag{26.33}
$$

所以第一次平台恰为 $L$。也可对每个 $n<L$，在最长游程中选 $\delta(z)=n+1$，使用定理26.2的实际两翻转来源对：它们满足 $sR_ns'$，但其后继在自己的时刻 $n$ 被分离，不满足 $DsR_nDs'$。因此同一等级的候选映射 $[s]_n\mapsto[Ds]_n$ 此时不良定；下降等级的式(26.30)却一直良定，两种更新不可混淆。

非常值循环词至少有一条边界，故存在 $\delta(z)=1$。该处两翻转来源对有相同初始 $O$、不同一步后 $O$；任何 $I=J\circ O$ 都会合并它们，所以全来源任务在所有 $n\ge1$ 均不可能。其他相位的长延迟不改变这一全称量词。对固定相位，$n<\delta(z)$ 时可用式(26.23)与计入状态的倒计时实现；$n\ge\delta(z)$ 时同一两翻转见证排除可行性。$n=0$ 直接存 $O$ 即可。恒定 $f$ 时，式(26.23)给出闭合的 $O$ 更新，且所有纤维仍有 $q>1$ 个来源。

若 $r=2$，式(26.16)只有一个发送端位，其值已由 $a,t$ 唯一决定，故 $O$ 单射。所有 $R_n$ 都是对角关系，$|S|=(2m)^2m=4m^3$；先由 $O$ 恢复来源再内部更新即可。式(26.17)仍成立，但 $q-1=0$，式(26.24)的反解不能使用，也不能从恒定的计数读出任何游程。$m=2$ 时 $\Delta=(0,1)\ne0$，上述每个分离与恢复论证保持有效。证毕。

## 26.99 追加锚
