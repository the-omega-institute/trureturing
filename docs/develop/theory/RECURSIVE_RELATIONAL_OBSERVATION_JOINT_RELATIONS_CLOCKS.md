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
