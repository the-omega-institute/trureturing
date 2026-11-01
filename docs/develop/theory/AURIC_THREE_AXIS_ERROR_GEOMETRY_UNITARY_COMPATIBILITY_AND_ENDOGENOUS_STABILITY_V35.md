# AURIC：三轴误差几何、酉相容与内生稳定

从二元关系到五模式纠错与可证明的累积控制

定义、定理与纸面证明　v35.0

2026 年 10 月 31 日　Asia/Singapore

<a id="abstract"></a>

## 摘要

本文将“误差也应满足两个读出、一个关系及归一化，并在三个稳定轴上表示”
推进为三个有明确前件的数学结论。第一，二阶正关系矩阵恰等价于一个正总量与一个 Bloch 球点；
误差方向归一化时必须另保留总量。第二，两个反对易轴上的相对酉误差
$e^{-i\alpha A}e^{-i\beta B}$，恰由四元数归一化及 $ab_C=b_Ab_B$ 刻画；
第三轴记录门序造成的法向误差。第三，利用项目已有有限 Kraus 精确恢复判据，
推出可在五模式输出中完整恢复逻辑 qubit 的误差综合征秩至多为二。
在固定正交综合征编码下，逻辑轴与综合征轴形成两个彼此对易的内部代数，
综合征可以变化而全部逻辑读出保持。
本文同时证明三轴未来闭合判据、共同酉演化与相对误差累积的区别、
强制保存两条锐轴的通道限制、近似恢复与逐层误差界，
并从新入库 CZX 交换幂等窗口构造导出一个显式收敛速率。
原 AURIC 三条占据读口是对易的，不能直接等同于上述 Pauli 轴；
完整五模式空间的奇数维数也禁止全空间幺元下的反对易锐轴对。
所有对象均解释为同一静态整体内部的角色、记录与接口。
本文提供解析证明和固定来源核对，不声称已取得实际原生控制与全输入误差证书。

> **编者注（来源归属）。** 正文关于完整取得 theory 与 D5 树、24 个文件的 blob 核对及未执行 Lean 等工作的叙述，均为作者在固定版本中的历史报告。本文保留这些原文；所引固定源码的选读不构成对该完整历史审计的重新认证。文中的 CZX 通道解释、定量速率及其他纸面推导不表示本次新增 Lean 核验；实际控制、制备、读出、记录资源和全输入误差合同仍各须供应。

<a id="section-1"></a>

## 1. 本轮结论、固定来源与研究前提

用户的核心直觉可以加强为：**误差必须在与读出相容的代数中保持正性、归一化与可组合性；
若要据此控制长期结果，还必须保留误差大小，证明未来读口闭合，并控制相对误差的累积。**
酉性支持这套结构，但单独的酉性并不推出误差小或误差趋零。

本轮固定项目 `dev` 提交为
`64369c37c781a34e67281ba38b315dc31fdf9115`，
时间为 2026-10-31 02:48:10（新加坡）；比较基线为 v34 的
`98d92f3c4013a4c4fba51ece2d8cd9d84aafc7fa`。
本次 theory 与 D5 树均完整取得；直接相关的新结果是 CZX 窗口映射的交换、幂等和极限投影。
二元读出 v28、原控制仪器稳定性及有限 Kraus 恢复供应链则是既有结果。
本文从这些供应条件推导新的组合结论，不把既有经典纠错判据或 Bloch 表示称为新发现。
来源审计包含 24 个当前文件的 Git blob 哈希核对；未执行 Lean、CAS、数值数学或门搜索。
[[1](#ref-head)，[2](#ref-v28)，[3](#ref-finite)，[4](#ref-necessary)，[9](#ref-czxsteady)]

继续使用固定单一整体 $(\mathcal A,\omega)$：观察者、程序、准备角色、综合征、记录与内部索引均在其中。
下文的有限维矩阵、通道和张量因子是内部接口表示。
$n$ 表示门序深度，$t$ 表示数学半群参数；它们不另行建立外部物理时间。
复线性量子接口、实际可用的制备和读出、实际保留的标记、误差合同是分开的前件。
几何图形本身不供应这些操作。

| 对象 | 三个坐标 | 坐标控制的内容 |
| --- | --- | --- |
| 原五模占据读口 | $(X,Y,Z)$ | 三个对易占据平均；仍有隐藏概率与相干关系。 |
| 逻辑 qubit 状态 | $\mathbf r$ | 固定 Pauli 代数上的全部归一态；$\vert \mathbf r\vert \le1$。 |
| 相对酉门 | $\mathbf b$，另有 $a$ | $E=aI-i\mathbf b\cdot\boldsymbol\sigma$；$a^2+\vert \mathbf b\vert ^2=1$。 |
| 二元综合征态 | $\mathbf s$ | 固定综合征编码中的误差关系；$\vert \mathbf s\vert \le1$。 |

这些三元组可以通过明确编码建立联系，但不能只因都有三个实坐标便彼此认同。
下文采用半迹距离 $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$。
归一态的 $D$ 始终不超过一；“误差发散”在这里应精确区分为离开目标小邻域、
持续振荡、累计参数无界或缺乏统一小误差界，而不是把有界的 $D$ 说成趋于无穷。

<a id="section-2"></a>

## 2. 二元正关系、归一化与三轴误差

<a id="definition-2-1"></a>

**定义 2.1（二元正关系）。**

令
$$
G=\begin{pmatrix}p&\bar c\\c&q\end{pmatrix},\qquad
p,q\ge0,\quad N=p+q>0,\quad |c|^2\le pq.
$$
$p,q$ 是两个非负强度，$c$ 是一个复关系，$G\ge0$ 是相容条件。
这里一个复关系包含两个实分量；它不是一个任意实标量约束。

<a id="theorem-2-2"></a>

**定理 2.2（正关系锥的尺度与三轴分解）。**

定义
$$
r_x=\frac{2\Re c}{N},\qquad r_y=\frac{2\Im c}{N},\qquad
r_z=\frac{p-q}{N}.
$$
这给出非零 $2\times2$ 正矩阵与 $N>0,\ |\mathbf r|\le1$ 的一一对应，且
$$
G=\frac N2\begin{pmatrix}1+r_z&r_x-ir_y\\r_x+ir_y&1-r_z\end{pmatrix},
\qquad
1-|\mathbf r|^2=\frac{4\det G}{N^2}.
$$
秩一对应球面，秩二对应球内部。

<a id="proof-1"></a>

**证明。**

直接展开得
$$
|\mathbf r|^2
=\frac{4|c|^2+(p-q)^2}{N^2}
=1-\frac{4(pq-|c|^2)}{N^2}.
$$
正性给球条件。反之，球条件给 $1\pm r_z\ge0$ 与非负行列式，
故所列逆矩阵正半定。各矩阵元由 $N,\mathbf r$ 唯一恢复。

<a id="proof-end-1"></a>

□

当 $p=|u|^2,q=|v|^2,c=\bar u v$ 时，归一后得到纯态球面。
这延续项目 v28 的二复振幅结果：两个复振幅去掉归一尺度和公共相位后有两个独立实参数，
以三个带约束坐标表达。约束降低自由度，不凭空创造一个自由度。[[2](#ref-v28)]

<a id="proposition-2-3"></a>

**命题 2.3（归一误差形状不能替代误差大小）。**

若 $\eta=(\eta_0,\eta_1)\ne0$ 是二元振幅误差，$G_\eta=\eta\eta^*$，
则归一三轴不能确定 $N_\eta=\|\eta\|^2$。
若误差是两个归一态之差 $\Delta=\rho-\sigma$，则 $\operatorname{Tr}\Delta=0$，
不能把它按迹归一成一个概率态。真正 qubit 上有
$$
\boxed{D(\rho,\sigma)=\tfrac12|\mathbf r_\rho-\mathbf r_\sigma|.}
$$

<a id="proof-2"></a>

**证明。**

$G_{z\eta}=|z|^2G_\eta$ 在除以迹后保持不变，而总量乘以 $|z|^2$。
两态之差的迹为 $1-1=0$。
最后令 $\delta\mathbf r=\mathbf r_\rho-\mathbf r_\sigma$，
$\Delta=\delta\mathbf r\cdot\boldsymbol\sigma/2$。
Pauli 关系给 $(\delta\mathbf r\cdot\boldsymbol\sigma)^2=|\delta\mathbf r|^2I$，
故 $\Delta$ 的特征值为 $\pm|\delta\mathbf r|/2$，即得距离公式。

<a id="proof-end-2"></a>

□

因此，振幅误差需要“总量 $N_\eta$ 加归一三轴”；态误差需要“两态三轴之差”。
如果只保留归一误差方向，任意小误差与放大后的误差将不可区分。

<a id="theorem-2-4"></a>

**定理 2.4（两个反对易锐读出生成有向三轴）。**

在复 Hilbert 空间上，设
$$
A=A^*,\quad B=B^*,\quad A^2=B^2=I,\quad AB=-BA,
\qquad C=-iAB.
$$
则 $C=C^*,C^2=I$，且
$$
AB=iC,\qquad BC=iA,\qquad CA=iB.
$$
对任意正归一态 $\omega$，
$$
\omega(A)^2+\omega(B)^2+\omega(C)^2\le1.
$$
有限维时，此三元组酉等价于 $(Z,X,Y)\otimes I_{\mathcal K}$。

<a id="proof-3"></a>

**证明。**

$C^*=iBA=-iAB=C$，$C^2=-ABAB=I$；其余乘法式直接展开。
对实 $u,v,w$，两两反对易给
$(uA+vB+wC)^2=(u^2+v^2+w^2)I$。
态在自伴算子上的范数界遂给
$|u\omega(A)+v\omega(B)+w\omega(C)|\le\sqrt{u^2+v^2+w^2}$，
取系数等于三个期望即得结论。
有限维时令 $\mathcal K$ 为 $A$ 的正特征空间；$B$ 将其等距双射到负特征空间。
映射 $W(\lvert 0\rangle \otimes v)=v$、$W(\lvert 1\rangle \otimes v)=Bv$ 是酉映射，直接验证给所述表示。

<a id="proof-end-3"></a>

□

给定两个期望 $a,b$，第三期望一般只能限定在
$[-\sqrt{1-a^2-b^2},\sqrt{1-a^2-b^2}]$；
只有所观察 qubit 为纯态时，才缩为带符号的两个端点。
普通几何正交不足以替代反对易：$Z\otimes I$ 与 $I\otimes Z$ 在矩阵内积下正交，
却可在 $\lvert 00\rangle$ 同时取得期望一。
若从实空间开始推导复结构，项目 v28 使用的是三个反对易实对称对合及 $J=ABC$；
本文两轴公式已明确假设复量子接口，不把 $i$ 当作几何图形自动提供的对象。[[2](#ref-v28)]

<a id="section-3"></a>

## 3. 原 AURIC 金字塔轴与未来闭合条件

项目的五模式次序为 $(N,2,3,5,25)$，占据读口为
$$
\begin{split}
N_1&=\operatorname{diag}(0,1,0,0,1),\qquad N_2=\operatorname{diag}(0,0,1,0,0),\\
N_3&=\operatorname{diag}(0,0,0,1,1),
\qquad (X,Y,Z)=(\operatorname{Tr}\rho N_1,\operatorname{Tr}\rho N_3,\operatorname{Tr}\rho N_2).
\end{split}
$$
三个算子彼此对易。项目 v28 已明确讨论它们与 Bloch 三轴之间的区别。[[2](#ref-v28)]

<a id="proposition-3-1"></a>

**命题 3.1（归一化原三轴仍隐藏最大误差）。**

给定 $(X,Y,Z)$，相容对角概率具有形式
$$
p_\kappa=(1-X-Y-Z+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
$$
其中 $\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y)$，并要求 $Z\ge0$。
存在原三轴完全相同、完整半迹距离为一的两态；即使限定严格正概率，距离仍可任意接近一。

<a id="proof-4"></a>

**证明。**

令最后一个概率为 $\kappa$，由三个读口和总概率一依次解出其余四项；非负性恰给所列约束。
取
$$
p^{(0)}=(0,\tfrac12,0,\tfrac12,0),\qquad
p^{(1)}=(\tfrac12,0,0,0,\tfrac12).
$$
两者的 $(X,Y,Z)$ 均为 $(\tfrac12,\tfrac12,0)$，支撑却不交，故距离为一。
将两者均替换为 $(1-\epsilon)p^{(j)}+\epsilon(1,1,1,1,1)/5$，
仍有同一可见三轴，每项严格正，距离为 $1-\epsilon$。

<a id="proof-end-4"></a>

□

这说明原三条轴的误差为零，并不保证完整五模式误差小。
若选择某个特定截面 $\kappa=\kappa(X,Y,Z)$，还需要证明实际态留在该截面及其相干限制中；
给出一个归一化公式并不完成这项不变性证明。

<a id="proposition-3-2"></a>

**命题 3.2（五模式中的 Pauli 轴必须有明确支撑）。**

在完整 $\mathbb C^5$ 上，不存在满足定理 [2.4](#theorem-2-4) 前件的全空间锐轴对。
此外，任何等距编码 $J:\mathbb C^2\to\mathbb C^5$ 下，
三个压缩占据效应 $J^*N_iJ$ 不能同时成为三个不同的锐 Pauli 投影。

<a id="proof-5"></a>

**证明。**

反对易锐轴会使 $A$ 的正、负特征空间由 $B$ 双射，故总维数必为偶数，不能等于五。
对第二项，五个压缩模式投影 $J^*\lvert j\rangle \langle j\rvert J$ 是一个共同 POVM，
三个效应都是其粗粒化，因而共同可测。两个共同可测的锐投影必对易：
联合正效应分别被投影和其补投影支配，遂分别支撑在两个正交子空间，
求和后另一边缘效应与该投影对易。不同 Pauli 锐投影不对易，产生矛盾。

<a id="proof-end-5"></a>

□

可行构造是在二维代码或四维正交综合征支撑 $P\mathcal H_5$ 上建立 Pauli 代数，
其单位元是 $P$，轴平方等于 $P$；剩余模式及泄漏质量需要按实际接口处理。
这与将原占据读口直接改称 Pauli 轴有不同的数学内容。

<a id="theorem-3-3"></a>

**定理 3.3（三轴未来预测闭合的充要条件）。**

设有限维观察代数
$\mathcal B=\operatorname{span}_{\mathbb C}\{I,A,B,C\}\simeq M_2\otimes I_{\mathcal K}$，
$\Phi$ 是一个 CPTP 通道。下列两项等价：

1. 任意两态在当前三轴上一致，经过 $\Phi$ 后仍在三轴上一致。

2. $\Phi^*(\mathcal B)\subseteq\mathcal B$。

酉通道时，该条件等价于 $U^*\mathcal B U=\mathcal B$。
若每个允许操作均满足闭合，则当前三轴决定所有有限操作字后的三轴预测。

<a id="proof-6"></a>

**证明。**

包含条件下，任何未来 $B_0\in\mathcal B$ 的期望等于当前 $\Phi^*(B_0)$ 的期望，故充分。
反之，若自伴 $H=\Phi^*(B_0)\notin\mathcal B$，令
$D_0=H-E_{\mathcal B}(H)\ne0$，其中 $E_{\mathcal B}$ 是矩阵内积正交投影。
$D_0$ 自伴、迹零，且与 $\mathcal B$ 正交。
取充分小的 $\epsilon>0$，$\rho_\pm=I/d\pm\epsilon D_0$ 是两态，当前三轴相同，
但未来 $B_0$ 期望差为 $2\epsilon\operatorname{Tr}(D_0^2)>0$，矛盾。
酉共轭保持子空间维数，故包含提升为等号。反复应用包含给有限操作字结论。

<a id="proof-end-6"></a>

□

三轴可以是*任务相对完整*的接口，无须重建整个整体；精确条件是未来闭合。
若没有闭合，$\lvert 0\rangle \langle 0\rvert \otimes\lvert 0\rangle \langle 0\rvert$ 与
$\lvert 0\rangle \langle 0\rvert \otimes\lvert 1\rangle \langle 1\rvert$ 当前第一因子的三轴相同、全态距离却为一，
内部 SWAP 会立即把差异带回读口。
含内部重数时，三轴距离普遍只给
$|\delta\mathbf r|/2\le D(\rho,\sigma)$；
固定共同提升 $\rho=\rho_2\otimes\tau$ 时才恢复等号。

<a id="section-4"></a>

## 4. 两轴酉误差如何精确生成第三轴

本节在一个明确的逻辑 qubit 上工作，取定理 [2.4](#theorem-2-4) 的有向轴 $(A,B,C)$。
相对门表示实际实现相对于理想实现的偏差；整体相位不改变状态读出。

<a id="theorem-4-1"></a>

**定理 4.1（相对酉误差的四元数表示与操作大小）。**

去掉整体相位后，每个相对酉门可以写成
$$
E=aI-i(b_AA+b_BB+b_CC),\qquad
a,b_A,b_B,b_C\in\mathbb R,\qquad a^2+|\mathbf b|^2=1.
$$
对于纯态三轴 $\mathbf r$，
$$
D(E\rho_{\mathbf r}E^*,\rho_{\mathbf r})^2
=|\mathbf b|^2-(\mathbf b\cdot\mathbf r)^2,
\qquad
\sup_{\rho\ \mathrm{pure}}D(E\rho E^*,\rho)=|\mathbf b|.
$$

<a id="proof-7"></a>

**证明。**

$SU(2)$ 矩阵有形式
$\begin{pmatrix}z&w\\-\bar w&\bar z\end{pmatrix}$，$|z|^2+|w|^2=1$；
分开实虚部即得所列四个实系数，Pauli 乘法给 $E^*E=(a^2+|\mathbf b|^2)I$。
纯态重叠为 $\operatorname{Tr}(\rho_{\mathbf r}E)=a-i\mathbf b\cdot\mathbf r$。
对两个单位向量，半迹距离等于重叠模平方之补的平方根；
在它们张成的至多二维空间中对两投影之差求特征值即可得到该公式。
于是距离平方等于 $1-a^2-(\mathbf b\cdot\mathbf r)^2$。
选取单位 $\mathbf r\perp\mathbf b$ 达到上界；$\mathbf b=0$ 时结论亦成立。

<a id="proof-end-7"></a>

□

此处三个 $b$ 分量保留了最坏输入误差的大小；若再把 $\mathbf b$ 归一到单位球面，大小仍会丢失。
恢复完整相对门还需要 $a$ 的分支信息；$E$ 与 $-E$ 表示相同的态变换。

<a id="theorem-4-2"></a>

**定理 4.2（两个轴参数、一个相容关系、一个归一化）。**

对实数 $a,b_A,b_B,b_C$，以下两项等价：

1. 存在实数 $\alpha,\beta$，使
   $$
   e^{-i\alpha A}e^{-i\beta B}=aI-i(b_AA+b_BB+b_CC).
   $$

2. $$
\boxed{a^2+b_A^2+b_B^2+b_C^2=1,\qquad ab_C=b_Ab_B.}
$$

<a id="proof-8"></a>

**证明。**

展开两因子并用 $AB=iC$，得到
$$
\begin{array}{ll}
a=\cos\alpha\cos\beta,& b_A=\sin\alpha\cos\beta,\\
b_B=\cos\alpha\sin\beta,& b_C=\sin\alpha\sin\beta.
\end{array}
$$
归一化和乘积关系立即成立。
反之，令
$$
Q=\begin{pmatrix}a&b_B\\b_A&b_C\end{pmatrix}.
$$
相容关系给 $\det Q=0$，归一化给 $\|Q\|_F=1$，故 $Q$ 为非零秩一实矩阵。
其唯一非零奇异值为一，因而 $Q=uv^{\mathsf T}$，其中 $u,v$ 是实单位向量。
写 $u=(\cos\alpha,\sin\alpha)$、$v=(\cos\beta,\sin\beta)$ 即恢复四个系数。
证明没有除以任何坐标，因此也覆盖 $a=0$ 等边界。

<a id="proof-end-8"></a>

□

这给用户所说结构一种精确实现：两轴旋转在同一三轴代数中闭合，法向轴不是任意补上的数。
这里刻画的是两次指定轴旋转的二参数误差族，而非全部三参数相对酉门。
矩阵按所写乘法次序解释，右因子先作用。

<a id="corollary-4-3"></a>

**推论 4.3（第三轴记录门序；误差组合仍保持酉性）。**

保持 $C=-iAB$ 的定向不变，交换两因子的次序会改变 $b_C$ 的符号，且
$$
\left\|e^{-i\alpha A}e^{-i\beta B}-e^{-i\beta B}e^{-i\alpha A}\right\|
=2|\sin\alpha\sin\beta|.
$$
更一般地，$E_j=a_jI-i\mathbf b_j\cdot\boldsymbol\sigma$ 满足
$$
\begin{split}
a_{21}&=a_2a_1-\mathbf b_2\cdot\mathbf b_1,\\
\mathbf b_{21}&=a_2\mathbf b_1+a_1\mathbf b_2+\mathbf b_2\times\mathbf b_1
\end{split}
$$
其中 $E_{21}=E_2E_1$。

<a id="proof-9"></a>

**证明。**

两种次序的差仅为 $-2i\sin\alpha\sin\beta C$，且 $\|C\|=1$。
一般式由
$(\mathbf u\cdot\boldsymbol\sigma)(\mathbf v\cdot\boldsymbol\sigma) =(\mathbf u\cdot\mathbf v)I+i(\mathbf u\times\mathbf v)\cdot\boldsymbol\sigma$
展开而得。乘积仍酉，故新的四元数仍满足归一式。

<a id="proof-end-9"></a>

□

这里第三轴记录的是所选 $SU(2)$ 代表中的次序差异，算符差范数并非模整体相位的操作距离。
例如 $\alpha=\beta=\pi/2$ 时，两种乘积相差负号，态通道相同。
是否可通过所选读出区分门序，需要按相位等价后的通道比较。
同轴同向误差可以累积，逆向误差可以抵消，不同轴可以产生法向误差。
归一化保证组合合法；是否靠近单位门由点积、叉积和累计角度共同决定。

<a id="section-5"></a>

## 5. 酉性、归一化与长期稳定不是同一个条件

<a id="proposition-5-1"></a>

**命题 5.1（酉性保持共同演化下的误差，却容许相对误差增大）。**

对于同一酉 $U$，$D(U\rho U^*,U\sigma U^*)=D(\rho,\sigma)$。
但令理想门恒为 $I$、实际门恒为 $e^{-i\epsilon Z}$、初态为 $\lvert +\rangle$，则
$$
D_n=|\sin(n\epsilon)|.
$$
取 $\epsilon=\pi/(2N)$，单步门误差随 $N$ 增大而任意小，第 $N$ 步却有 $D_N=1$。

<a id="proof-10"></a>

**证明。**

共同酉式来自迹范数酉不变性。第二式中纯态重叠为
$\langle +\rvert e^{-in\epsilon Z}\lvert +\rangle =\cos(n\epsilon)$，应用纯态距离公式即可。
而 $\|e^{-i\epsilon Z}-I\|=2|\sin(\epsilon/2)|\le|\epsilon|$。

<a id="proof-end-10"></a>

□

每一步都严格酉，所有态都严格归一，三轴都留在球面，仍不能保证相对目标误差小。
更强地，取 $\epsilon_n=1/(n+1)$，单步误差趋零且平方可和，但累积角度
$H_n=\sum_{j<n}\epsilon_j$ 无界。首次越过 $k\pi$ 及 $k\pi+\pi/2$ 的超调趋零，
分别给出密度态趋近 $\lvert +\rangle \langle +\rvert$ 和 $\lvert -\rangle \langle -\rvert$ 的子序列，因此实际态不收敛。
这针对确定性相干误差；独立、零均值或已证抵消关系是额外条件。

<a id="theorem-5-2"></a>

**定理 5.2（相对误差递推与可和预算）。**

令
$$
G_n=U_{n-1}\cdots U_0,\quad H_n=V_{n-1}\cdots V_0,\quad E_n=G_n^*H_n.
$$
则
$$
E_{n+1}=W_nE_n,\qquad W_n=G_n^*U_n^*V_nG_n,
\qquad \|W_n-I\|=\|U_n-V_n\|.
$$
若 $\epsilon_n=\|U_n-V_n\|$，则
$$
\|E_N-I\|\le\sum_{j<N}\epsilon_j.
$$
若 $\sum_n\epsilon_n<\infty$，则 $E_n$ 收敛到一个酉门 $E_\infty$。

<a id="proof-11"></a>

**证明。**

代入 $G_{n+1}=U_nG_n$、$H_{n+1}=V_nH_n$ 得递推。
酉不变性给范数等式及
$\|E_{n+1}-E_n\|=\|(W_n-I)E_n\|\le\epsilon_n$。
望远镜和给第一界；可和性给 Cauchy 性，酉群在算符范数下闭合，故极限仍酉。

<a id="proof-end-11"></a>

□

相对门收敛给稳定残余误差，不强制 $E_\infty=I$；理想轨迹自身若不停变化，
也不能据此声称实际态趋向固定态。统一小预算给统一小相对误差，
而严格趋零还需要校准、恢复、抵消或相应的收缩结构。

<a id="proposition-5-3"></a>

**命题 5.3（保存整个球并不充分保证量子相容）。**

转置映射保持 qubit 正性、迹和 Bloch 距离，但不是完全正映射。

<a id="proof-12"></a>

**证明。**

在标准 Pauli 坐标中转置为 $(r_x,r_y,r_z)\mapsto(r_x,-r_y,r_z)$，
故它保持球和欧氏距离。对内部 Bell 态 $\lvert \Phi^+\rangle =(\lvert 00\rangle +\lvert 11\rangle )/\sqrt2$，
一个因子上的转置给 $\mathrm{SWAP}/2$，其在反对称向量上的特征值为 $-1/2$。
因此该局部规则不能与任意内部相关态一致组合。

<a id="proof-end-12"></a>

□

所以“归一化误差仍在球内”只检验单接口正性；完整量子操作还要求完全正性。
酉共轭给保向旋转 $SO(3)$，并非任意保持球的反射。

<a id="theorem-5-4"></a>

**定理 5.4（精确保留两条锐逻辑轴的限制）。**

设 $\Phi(\rho)=\sum_jK_j\rho K_j^*$ 为同一有限空间上的 CPTP 通道，
$A,B$ 满足定理 [2.4](#theorem-2-4) 的前件。
若对全部输入都精确保留两轴期望，即 $\Phi^*(A)=A$、$\Phi^*(B)=B$，
则每个 $K_j$ 与 $A,B,C$ 对易。
在裸 qubit 上 $\Phi=\operatorname{id}$；在 $\mathbb C^2\otimes\mathcal K$ 表示下，
$\Phi=\operatorname{id}_2\otimes\Psi$。

<a id="proof-13"></a>

**证明。**

由 $\sum_jK_j^*K_j=I$ 和 $A^2=I$，
$$
\sum_j(AK_j-K_jA)^*(AK_j-K_jA)
=2I-\Phi^*(A)A-A\Phi^*(A)=0.
$$
每项正半定，故每个交换子为零；同理与 $B$ 对易，遂与其生成的完整 Pauli 代数对易。
该代数在裸 qubit 上的交换子代数只有标量，在带重数表示下为 $I_2\otimes M(\mathcal K)$。
因此 $K_j=I_2\otimes L_j$，归一性给所述通道。

<a id="proof-end-13"></a>

□

“稳定轴”若指固定、可校准的读出代数，并不要求其所有期望对任意过程恒定。
若确实要求任意未知逻辑态的两轴都守恒，那么可纠错的方向必须安置在代码冗余或综合征中。
对所有逻辑差异作严格收缩，会同时抹去本应保存的逻辑信息。

<a id="section-6"></a>

## 6. 五模式精确纠错：何时整族误差共用一个三轴标架

项目已有 `FiniteKrausReversibility` 与 `KrausLeftInverseNecessity`
给出有限 Kraus 精确恢复的充分、必要条件；来源明确归属于经典
Knill–Laflamme / Nayak–Sen 判据。正交综合征及其全空间 CPTP 解码由另两个源文件供应。
[[3](#ref-finite)，[4](#ref-necessary)，[5](#ref-syndrome)，[6](#ref-channel)]
本节重新给出适合本问题的纸面证明，并将它应用于五模式与变化误差的共同标架。

<a id="definition-6-1"></a>

**定义 6.1（实际有限误差族与共同恢复）。**

设 $T$ 是非空有限集合。每个 $t\in T$ 给一个实际有限 Kraus 通道
$$
\mathcal E_t(X)=\sum_aE_{t,a}XE_{t,a}^*,\qquad
E_{t,a}:\mathbb C^2\longrightarrow\mathbb C^5,\qquad
\sum_aE_{t,a}^*E_{t,a}=I_2.
$$
共同精确恢复是一个有限归一 Kraus 通道 $\mathcal R:M_5\to M_2$，
使 $\mathcal R\mathcal E_t(X)=X$ 对全部 $t$ 和全部逻辑矩阵 $X$ 成立。
若物理误差算子为 $L_{t,a}$、初始编码为 $J$，则 $E_{t,a}=L_{t,a}J$。

<a id="theorem-6-2"></a>

**定理 6.2（五模式共同恢复与固定二元综合征的充要刻画）。**

对上述有限误差族，下列三项等价：

1. 存在共同精确恢复 $\mathcal R$。

2. 全部跨误差乘积在逻辑空间上均为标量：
   $$
   \boxed{E_{t,a}^*E_{u,b}=c_{ta,ub}I_2\quad\text{对所有 }t,u,a,b.}
   $$

3. 存在一个固定等距映射与一族综合征态
   $$
   W:\mathbb C^2_L\otimes\mathbb C^r_S\longrightarrow\mathbb C^5, \qquad 1\le r\le2,\qquad \tau_t\ge0,\quad\operatorname{Tr}\tau_t=1,
   $$
   使
   $$
   \boxed{\mathcal E_t(X)=W(X\otimes\tau_t)W^*.}
   $$

这里 $W$ 对整族固定；允许变化的是 $\tau_t$。

<a id="proof-14"></a>

**证明。**

先证 $1\Rightarrow2$。写 $\mathcal R(Y)=\sum_bR_bYR_b^*$。
对固定 $t$，复合 Kraus 算子 $F_{b,a}=R_bE_{t,a}$ 实现恒等通道。
任意纯输入 $\lvert \psi\rangle \langle \psi\rvert$ 的输出仍为同一秩一投影，因此正项
$\lvert F_{b,a}\psi\rangle \langle F_{b,a}\psi\rvert$ 都支撑在 $\mathbb C\psi$。
故每个 $F_{b,a}$ 将每个向量映到其自身张成的一维空间。
对一组基向量及每两个基向量之和应用该性质，得到
$R_bE_{t,a}=\lambda_{b,t,a}I_2$。
利用恢复归一性，
$$
E_{t,a}^*E_{u,c}
=\sum_b(R_bE_{t,a})^*(R_bE_{u,c})
=\left(\sum_b\bar\lambda_{b,t,a}\lambda_{b,u,c}\right)I_2.
$$

再证 $2\Rightarrow3$。令 $\mathcal V=\operatorname{span}_{\mathbb C}\{E_{t,a}\}$。
标量乘积条件使
$$
F^*G=\langle F,G\rangle_{\mathcal V}I_2
$$
定义其上的正定内积：$F^*F=\lambda I_2\ge0$，且 $\lambda=0$ 当且仅当 $F=0$。
选一组该内积的正交单位基 $S_1,\ldots,S_r$，则
$$
S_j^*S_k=\delta_{jk}I_2.
$$
每个 $S_j$ 都是逻辑 qubit 的等距副本，像空间两两正交，所以
$$
\boxed{2r\le5,\qquad r\le2.}
$$
定义 $W(\psi\otimes\lvert j\rangle )=S_j\psi$ 即得固定等距映射。
展开 $E_{t,a}=\sum_jv_{t,a,j}S_j$，令
$$
\tau_t=\sum_av_{t,a}v_{t,a}^*.
$$
此矩阵正半定；通道归一性给 $\sum_{a,j}|v_{t,a,j}|^2=1$，故迹一。
将展开式代回 Kraus 和，得到 $\mathcal E_t(X)=W(X\otimes\tau_t)W^*$。

最后证 $3\Rightarrow1$。令 $P=WW^*=\sum_jS_jS_j^*$，取固定逻辑纯态 $\rho_*$，定义
$$
\boxed{\mathcal R(Y)=\sum_jS_j^*YS_j+\operatorname{Tr}[(I_5-P)Y]\rho_*.}
$$
第一项是 Kraus 映射且总效应为 $P$；第二项有互补总效应 $I_5-P$，
可用其支撑的一组正交基与 $\rho_*$ 的准备向量写成有限 Kraus 和。
故 $\mathcal R$ 完全正且保迹。
编码输出支撑于 $P$，第二项消失，而第一项等于 $(\operatorname{Tr}\tau_t)X=X$。

<a id="proof-end-14"></a>

□

此定理把“误差也落在稳定三轴”转化成了可检验的代数条件。
**整族误差需要共同恢复，也就是全部跨误差乘积的标量性；
分别存在恢复映射并不够。**
例如 $E_t=SU_t$，其中 $S:\mathbb C^2\to\mathbb C^5$ 为固定等距映射，
$U_t$ 为不同逻辑酉门。每个单独通道都有恢复且单独 Gram 矩阵均为 $(1)$，
但 $E_t^*E_u=U_t^*U_u$ 一般不为标量，因而不存在所需共同恢复。
单独误差的秩或谱没有固定其逻辑标架。

<a id="corollary-6-3"></a>

**推论 6.3（单个五模式可逆误差的综合征秩界）。**

若一个有限通道 $\mathcal E:M_2\to M_5$ 可精确恢复全部逻辑输入，
定义 $C_{ab}$ 为 $E_a^*E_b=C_{ab}I_2$，则
$$
C\ge0,\qquad\operatorname{Tr} C=1,\qquad\boxed{\operatorname{rank} C\le2.}
$$

<a id="proof-15"></a>

**证明。**

任取复系数 $z_a$，
$\|\sum_az_aE_a\psi\|^2=z^*Cz$ 对单位 $\psi$ 成立，故 $C\ge0$。
由 $\sum_aE_a^*E_a=I_2$ 得 $\sum_aC_{aa}=1$。
$C$ 是 $E_a$ 在上述正定内积中的 Gram 矩阵，故其秩等于它们张成空间的维数，
维数界由定理 [6.2](#theorem-6-2) 得到。

<a id="proof-end-15"></a>

□

当整族的共同综合征维数 $r=2$ 时，固定综合征基给
$$
\tau_t=\frac12(I+s_{t,x}\sigma_x+s_{t,y}\sigma_y+s_{t,z}\sigma_z),
\qquad|\mathbf s_t|\le1.
$$
当共同综合征维数 $r=1$ 时，综合征代数只有标量，没有独立的非平凡综合征三轴；
共同 $r=2$ 时某个 $\tau_t$ 为纯态，并不使综合征代数降为一维。
形式上补成纯 qubit 需要额外选定第二个副本，不能将其当作已有物理结构。
一般 Kraus 标记约定下，若等距映射写为 $\sum_aE_a\otimes\lvert a\rangle$，
其相干标记态是 $C^{\mathsf T}$，与 $C$ 同谱；二者不应在有复相位时不加说明地等同。

<a id="theorem-6-4"></a>

**定理 6.4（同一支撑上的逻辑轴与综合征轴）。**

在定理 [6.2](#theorem-6-2) 的固定 $W$ 下，令
$$
\pi_L(A)=W(A\otimes I_r)W^*,\qquad
\pi_S(B)=W(I_2\otimes B)W^*.
$$
两者分别保持乘法且彼此对易；其共同单位元为 $P=WW^*$。
对任意逻辑态 $\rho$ 与综合征态 $\tau$，
$$
\operatorname{Tr}[W(\rho\otimes\tau)W^*\pi_L(A)]=\operatorname{Tr}(\rho A),\qquad
\operatorname{Tr}[W(\rho\otimes\tau)W^*\pi_S(B)]=\operatorname{Tr}(\tau B).
$$
当 $r=2$ 时，两套 Pauli 三轴各自在支撑上成立，轴平方为 $P$。

<a id="proof-16"></a>

**证明。**

由 $W^*W=I$，例如
$\pi_L(A)\pi_L(B)=W(AB\otimes I)W^*=\pi_L(AB)$。
两个张量因子上的操作对易，迹分解及 $\operatorname{Tr}\rho=\operatorname{Tr}\tau=1$ 给两式。

<a id="proof-end-16"></a>

□

因此综合征关系可以变化，而未知逻辑态的全部读出保持。
这给“在约束下保持结果稳定”的一个精确实现：
可变误差被组织在独立的内部关系中，逻辑信息由同一代数保存。
上述乘法关系与相干综合征解码在项目已有来源中有直接对应。[[5](#ref-syndrome)，[6](#ref-channel)]

必须明确五维界的输出范围：它针对非选择的 $M_2\to M_5$ 通道。
若实际可用输出还包括保留的经典记录，输出空间便不再只有五维，应在完整输出上重新建模。
例如 $E_a=\sqrt{p_a}S$ 可有任意多个已记录标签，尽管相干 Gram 秩为一。
所以 $r\le2$ 不给完整观察历史的一比特存储上界，也不准许访问原本丢弃的 Kraus 标签。

<a id="definition-6-5"></a>

**定义 6.5（全输入与内部参考误差）。**

对同型通道定义
$$
d_{\rm ref}(\Phi,\Psi)=
\sup_{R,\rho_{LR}}D((\Phi\otimes\operatorname{id}_R)(\rho_{LR}),
                         (\Psi\otimes\operatorname{id}_R)(\rho_{LR})),
$$
其中 $R$ 遍历有限内部参考角色，$\rho_{LR}$ 遍历归一联合态。
这一距离同时检验输入及与整体内部其他角色的相关关系。

<a id="proposition-6-6"></a>

**命题 6.6（共同恢复的实际误差界）。**

设理想编码为 $\mathcal E_t$、理想共同恢复为 $\mathcal R$。
若实际通道满足
$$
d_{\rm ref}(\widetilde{\mathcal E}_t,\mathcal E_t)\le\epsilon_t,
\qquad d_{\rm ref}(\widetilde{\mathcal R},\mathcal R)\le\delta,
$$
则
$$
\boxed{d_{\rm ref}(\widetilde{\mathcal R}\widetilde{\mathcal E}_t,\operatorname{id})
\le\epsilon_t+\delta.}
$$

<a id="proof-17"></a>

**证明。**

插入 $\mathcal R\widetilde{\mathcal E}_t$，第一段由恢复误差界控制，
第二段由 $\mathcal R$ 的迹距离收缩及编码误差控制；$\mathcal R\mathcal E_t=\operatorname{id}$。
所有步骤张量同一个内部参考后成立。

<a id="proof-end-17"></a>

□

精确可恢复性是代数前件；实际协议还须供应同一个可用恢复及上述完整误差证书。
项目实际恢复文档明确区分有限输入族恢复、全部输入及参考一致恢复与原生资源桥梁。[[7](#ref-robust)]
精确的综合征秩界也不直接变成近似通道的秩界；任意小的一般扰动可能提高 Kraus 秩。
近似结论应使用完整操作距离表述。
逐周期都使用逻辑输入、逻辑输出的完整复合通道时，误差至多累加为
$\sum_t(\epsilon_t+\delta_t)$；若只在物理代码上证明恢复，则还需计入下一轮的泄漏和重新编码。

<a id="section-7"></a>

## 7. 与整体酉性相容的五模式稳定化

<a id="proposition-7-1"></a>

**命题 7.1（有限通道的内部酉实现）。**

给定有限同型 Kraus 通道 $\Lambda(\rho)=\sum_yM_y\rho M_y^*$，
$\sum_yM_y^*M_y=I$，定义
$$
V\psi=\sum_yM_y\psi\otimes\lvert y\rangle .
$$
则 $V$ 为等距映射，且存在同一整体内部载体上的酉 $U$，使
$U(\psi\otimes\lvert 0\rangle )=V\psi$。
限制到原读出因子得到 $\Lambda$。

<a id="proof-18"></a>

**证明。**

$\langle V\phi,V\psi\rangle=\sum_y\langle\phi,M_y^*M_y\psi\rangle =\langle\phi,\psi\rangle$。
输入子空间 $\mathcal H\otimes\lvert 0\rangle$ 与其像子空间同维，选取各自正交补的正交基，
把等距映射延拓到整个 $\mathcal H\otimes\mathbb C^{\#y}$ 的酉映射。
对内部标记求限制，即得到 Kraus 和。

<a id="proof-end-18"></a>

□

因此有效读出的收缩可以与整体酉性并存：整体可区分信息仍保留在内部记忆和相关关系中。
这是一项表示存在证明；实施某个内部酉、取得准备态及重复使用的记录资源仍需实际供应。
它不提供无需记录与准备资源的无限重复协议，也不声称保留完整旧档案后的全态距离严格收缩。

<a id="theorem-7-2"></a>

**定理 7.2（保持逻辑内容的五模式综合征稳定化）。**

取定理 [6.2](#theorem-6-2) 的固定 $W$、完整恢复 $\mathcal R$，以及一个固定综合征态 $\tau_*$。
定义五模式通道
$$
\Pi(Y)=W(\mathcal R(Y)\otimes\tau_*)W^*,\qquad
T_\kappa=\kappa\operatorname{id}+(1-\kappa)\Pi,\quad 0\le\kappa<1.
$$
则 $\Pi,T_\kappa$ 为 CPTP，且
$$
\Pi^2=\Pi,\quad \mathcal R\Pi=\mathcal R,\quad
T_\kappa^n=\Pi+\kappa^n(\operatorname{id}-\Pi),
\qquad
D(T_\kappa^n\rho,\Pi\rho)=\kappa^nD(\rho,\Pi\rho).
$$
对编码输入 $W(\rho_L\otimes\tau)W^*$，逻辑态 $\rho_L$ 恒定，而综合征更新为
$$
\tau\longmapsto\kappa\tau+(1-\kappa)\tau_*.
$$
当 $r=2$ 时，其三轴满足
$$
\boxed{\mathbf s_n-\mathbf s_*=
\kappa^n(\mathbf s_0-\mathbf s_*).}
$$

<a id="proof-19"></a>

**证明。**

编码与恢复都是 CPTP，故 $\Pi$ 是 CPTP；凸组合亦然。
由 $\mathcal R\operatorname{Enc}_{\tau_*}=\operatorname{id}$，得到
$\Pi^2=\Pi$ 及 $\mathcal R\Pi=\mathcal R$。
写 $T_\kappa=\Pi+\kappa(\operatorname{id}-\Pi)$，两个投影部分交叉乘积为零，
所以幂次为所列式；迹范数齐次性给距离等式。
对固定 $\rho_L$ 的编码族直接展开，得到综合征凸组合，Bloch 坐标是矩阵的线性函数，
遂得到三轴几何衰减。

<a id="proof-end-19"></a>

□

对含代码外泄漏的一般输入，全空间保留的读出是
$$
\mathcal R^*(A)=\pi_L(A)+\operatorname{Tr}(\rho_*A)(I_5-P),
\qquad T_\kappa^*\mathcal R^*(A)=\mathcal R^*(A).
$$
裸支撑轴 $\pi_L(A)$ 的保存应限定于 $P$ 支撑；上述全域扩展一般不是平方为 $I_5$ 的锐轴。

这一模型正面实现了用户要求的三件事：误差态始终正且归一，误差在固定三轴中更新，
相对于指定综合征目标的误差确实衰减，同时保留任意未知逻辑态。
其整体实现可用命题 [7.1](#proposition-7-1)，所有辅助角色均在同一整体内部。
这里数学上构造出的 $W,\mathcal R,\tau_*$ 与 $T_\kappa$ 的实际原生实现仍是待供应接口。

<a id="theorem-7-3"></a>

**定理 7.3（守恒漂移与可收缩误差的分离定理）。**

设 $\Pi,T$ 是有限维 CPTP 映射，满足
$$
\Pi^2=\Pi,\qquad\Pi T=T\Pi=\Pi.
$$
设存在 $0\le q<1$，使任意自伴 $X\in\ker\Pi$ 都满足
$\|TX\|_1\le q\|X\|_1$。
实际迭代为 $\rho_{n+1}=\Phi_n(\rho_n)$，定义
$$
\begin{split}
w_n&=\Phi_n(\rho_n)-T(\rho_n),\qquad
\sigma_n=\Pi\rho_n,\qquad z_n=(\operatorname{id}-\Pi)\rho_n,\\
d_n&=\tfrac12\|\Pi w_n\|_1,\qquad
b_n=\tfrac12\|(\operatorname{id}-\Pi)w_n\|_1.
\end{split}
$$
则
$$
\sigma_{n+1}-\sigma_n=\Pi w_n,\qquad
z_{n+1}=Tz_n+(\operatorname{id}-\Pi)w_n,
$$
以及
$$
\boxed{\tfrac12\|z_n\|_1\le
q^n\tfrac12\|z_0\|_1+\sum_{j<n}q^{n-1-j}b_j.}
$$
若 $\sum_nd_n<\infty$ 且 $b_n\to0$，则存在 $\sigma_\infty\in\operatorname{ran}\Pi$，使
$$
\boxed{\rho_n\longrightarrow\sigma_\infty,\qquad
D(\sigma_\infty,\Pi\rho_0)\le\sum_nd_n.}
$$

<a id="proof-20"></a>

**证明。**

对实际一步分别作用 $\Pi$ 与 $\operatorname{id}-\Pi$，利用交换关系即得两个精确递推。
第二递推的三角不等式与 $\ker\Pi$ 上的收缩给几何卷积界。
第一递推和 $\sum d_n<\infty$ 使 $\sigma_n$ 为 Cauchy 列；它们均为归一正态，
极限也是态，连续性给 $\Pi\sigma_\infty=\sigma_\infty$。
对卷积和取一个充分晚的截点：有限前缀乘以趋零的几何系数，尾部至多为
$\sup_{j\ge J}b_j/(1-q)$，故 $z_n\to0$。
于是 $\rho_n=\sigma_n+z_n\to\sigma_\infty$，第一递推的望远镜界给最终偏移估计。

<a id="proof-end-20"></a>

□

这给出一个更精确的稳定原则：**要保留的内容方向需要累计漂移预算；
能够收缩的误差方向只需要残余误差趋零。**
精确保约束 $\Pi\Phi_n=\Pi$ 时 $d_n=0$，最终目标固定为 $\Pi\rho_0$。
若此时 $b_n\le b$，则
$$
\limsup_nD(\rho_n,\Pi\rho_0)\le\frac{b}{1-q}.
$$
若只知道完整一步误差 $D(\Phi_n(\rho),T(\rho))\le e_n$，
可得 $d_n\le e_n$、$b_n\le2e_n$；所以 $e_n\to0$ 本身并不控制守恒方向的累计漂移。
定理 [7.2](#theorem-7-2) 正是此框架中 $q=\kappa$ 的明确五模式模型。

最后，归一化条件分支仍需保留事件质量。
两套完整记录态若主分支相同、概率 $p$ 的稀有分支分别为正交态，则完整距离为 $p$，
稀有分支各自归一后的距离却为一。这直接来自块对角迹范数求和。
因此不能删除失败分支或低概率标记，再把其余三轴的稳定性当作完整输出的同一个误差界。

<a id="section-8"></a>

## 8. 与本轮 CZX 增量及原控制稳定性直接接合

<a id="subsection-8-1"></a>

### 8.1 交换幂等窗口给出可证明的稳定机制

新 CZX 源文件定义四站点窗口映射，并给出窗口交换性、幂等性及偶数环上的极限投影。
其局部构造由酉共轭、块钳制、偏迹、归一乘法空间态 $I_4/4$ 重插入和逆酉共轭组成。
从这些构造可在纸面上确认 CPTP：块钳制有投影 Kraus，偏迹有基向量收缩 Kraus，
插入正归一态有其谱分解给出的 Kraus，复合与张量恒等保持 CPTP。
源文件中的比例 $\nu/\mu=1/4$ 正是重插入的归一系数。
该 CPTP 解释及下述定量速率不冒称为已在本轮执行验证的 Lean 定理。[[8](#ref-czxwindow)，[9](#ref-czxsteady)]

<a id="theorem-8-1"></a>

**定理 8.1（交换幂等通道的投影收敛与约束内收缩）。**

设 $\mathcal E_1,\ldots,\mathcal E_m$ 两两交换、CPTP 且幂等，$m\ge1$。
令
$$
\mathcal L=\sum_i(\mathcal E_i-\operatorname{id}),\qquad
T_t=e^{t\mathcal L},\qquad\Pi=\prod_i\mathcal E_i,\qquad t\ge0.
$$
则
$$
T_t=\prod_i[e^{-t}\operatorname{id}+(1-e^{-t})\mathcal E_i],\qquad
\Pi^2=\Pi,\quad\Pi T_t=T_t\Pi=\Pi,
$$
且
$$
\boxed{d_{\rm ref}(T_t,\Pi)
\le a(t):=1-(1-e^{-t})^m\le me^{-t}.}
$$
任意自伴 $X\in\ker\Pi$ 都有 $\|T_tX\|_1\le a(t)\|X\|_1$。
因此固定 $t=\tau>0$ 后，同一 $\Pi$ 内容纤维内严格收缩。

<a id="proof-21"></a>

**证明。**

单个幂等映射分解给
$e^{t(\mathcal E-\operatorname{id})}=\mathcal E+e^{-t}(\operatorname{id}-\mathcal E)$。
交换性允许把总指数写成乘积，也给出 $\Pi$ 的幂等和吸收关系。
展开乘积为所有子集组合的凸和。全集项是 $\Pi$，权重为 $(1-e^{-t})^m$，
其余项仍是 CPTP，权重总和为 $a(t)$。
每项作用于同一个含内部参考的归一态后，与 $\Pi$ 输出的距离至多一，
由凸性得到参考一致误差界；伯努利不等式给 $a(t)\le me^{-t}$。

若 $\Pi X=0$，全集项消失。其余 CPTP 项对自伴 $X$ 的迹范数不增：
写 $X=X_+-X_-$，由正性、保迹及三角不等式得
$\|\Phi(X)\|_1\le\operatorname{Tr}\Phi(X_+)+\operatorname{Tr}\Phi(X_-)=\|X\|_1$。
再乘剩余权重即得核空间收缩。
当 $\Pi\rho=\Pi\sigma$ 时 $\rho-\sigma\in\ker\Pi$，因此满足同一收缩界。

<a id="proof-end-21"></a>

□

项目 CZX 偶数环 $N\ge4$ 中，偶起点窗口数为 $m=N/2$，因而本文推论给
$$
d_{\rm ref}(T_t,\Pi_N)\le\tfrac N2e^{-t}.
$$
源文件本身给出的全算子投影公式为
$$
\boxed{\Pi_N(a)=2^{-N}\bigl[(\operatorname{Tr} a)I+
\operatorname{Tr}(U_{\rm CZX}^*a)U_{\rm CZX}\bigr].}
$$
它保留一个对称系数。来源的具体初态极限为
$$
T_t\bigl(2^{-N}(I+X^{\otimes N})\bigr)
\longrightarrow 2^{-N}\bigl(I+2^{1-N/2}U_{\rm CZX}\bigr),
$$
与最大混态的极限不同，因此不是全输入唯一固定态吸引子。[[9](#ref-czxsteady)]
这里真正成立的是“保留指定内容，消除其余方向”的稳定性。
配合定理 [7.3](#theorem-7-3)，实际周期若保持同一内容约束且横向误差趋零，
便有稳健收敛；只给每步归一或酉性无法替代这两个条件。

<a id="subsection-8-2"></a>

### 8.2 原控制来源已显示累计误差不能由坐标接近替代

项目既有原控制仪器文档研究完整首失效时间、模式标记与终端成功输出。
其定理 3.2 构造一致趋近等待轨迹的控制序列，同时具有共同支持裕量、
速度与总变差上界、零相对相位和相同端点，但终端生存率始终为 $1/2$，
与等待的完整仪器距离也始终为 $1/2$。
越来越密集的小振荡维持了非零累计损失；这不违反本稿所需的累计预算条件。[[10](#ref-control)]

同一来源给出正面充分条件。令两条高度保持在 $[\eta,c-\eta]$，
设 $\delta=\|k-\tilde k\|_\infty$、$e=\|k'-\tilde k'\|_{L^1}$、
$M=\operatorname{TV}(\tilde k)$，则
$$
\|\lambda-\tilde\lambda\|_{L^1}
\le B:=\frac e\eta+\frac{M\delta}{\eta^2},\qquad
\|S-\tilde S\|_\infty\le B.
$$
证明分别控制速度项与高度分母的变化，再对累计危险率取指数。
如果同时取得终端成功 Kraus 误差 $\kappa$ 与实际失效密度的归一 $L^1$ 误差 $b_i$，
则完整输出误差满足
$$
d_{\rm op}\le\kappa+\tfrac12\max_i b_i.
$$
这些是来源 §5 已有的完整仪器结果；不能用三个归一坐标的一致接近替换其前件。[[10](#ref-control)]

> **编者注（原控制界的适用域）。** 此处沿用[来源 10](#ref-control)定义 1.1–1.4 与命题 5.1–5.2 的同一指定完整仪器：在该来源的记号中，固定 $0<Z<1,\ c=(1-Z)/2,\ a\in(0,c)$ 及有限时长；共同初始高度、基底和初始相位均固定。控制的两个实坐标连续且绝对连续，或同具有限分段的连续可微正则性、每个闭片上的速度连续；比较使用相同输入与未改动的参考。支撑条件为 $0<\eta\le c/2$，且共同初始模式概率 $p_i(a)>0$。具体误差量为 $\kappa=\|K_T-\widetilde K_T\|_{\mathrm{op}}$ 与 $b_i=p_i(a)^{-1}\int_0^T|f_i(t)-\widetilde f_i(t)|\,dt$，其中 $f_i=F_i'$ 是来源初态族的实际模式失效密度。终端 Kraus 误差包括终端相位，密度误差包括实际时间与模式校准；它们不能换成各分支条件归一化后的误差。


<a id="section-9"></a>

## 9. 本轮形成的定理链与仍需实际供应的接口

现在可以给出一种完整且条件明确的表述。
**两个非负读出与一个复关系在正性下形成二阶正矩阵；
尺度和三轴完整表示该矩阵。两个反对易逻辑轴又通过乘法生成第三轴，
两次轴旋转的误差恰满足一个乘积关系与四元数归一化。
整族误差若满足共同恢复条件，在五模式输出中可被组织为至多二元的固定综合征；
在这个固定标架上可以构造保持全部逻辑内容而使综合征三轴收敛的通道。**

这条链同时回答了“表示”“可组合”“可恢复”和“长期稳定”，每一层都有自己的前件。
新增维数推论与稳定化构造是对项目供应的应用；一般 Bloch、精确纠错、有限通道酉扩张及
几何递推是标准工具或本文重述证明，没有世界优先权主张。

| 目标 | 已给出的数学条件与证明 | 实际接口要求 |
| --- | --- | --- |
| 用三轴保留误差信息 | 定理 [2.2](#theorem-2-2)、命题 [2.3](#proposition-2-3)；保留尺度或相对态差 | 指明具体编码、可读轴与总质量。 |
| 两轴酉误差闭合 | 定理 [4.2](#theorem-4-2) 与精确组合律 | 实际反对易轴、门序和相位标架。 |
| 三轴决定全部未来 | 定理 [3.3](#theorem-3-3) 的代数闭合 | 允许操作集和隐藏自由度的真实作用。 |
| 整族误差共同可恢复 | 定理 [6.2](#theorem-6-2) 的全部跨乘积标量性 | 固定实际噪声族、共同可执行恢复、完整保留输出。 |
| 保持逻辑同时稳定误差 | 定理 [7.2](#theorem-7-2) 的固定综合征投影 | 内部酉实现、准备态与重复记录资源。 |
| 近似实际过程长期稳定 | 定理 [7.3](#theorem-7-3) 的漂移预算与横向收缩 | 全输入误差合同、约束保持证书及有效误差尾界。 |

原 AURIC 占据三轴与上述逻辑、综合征三轴之间，仍需明确的编码和读出交织关系。
在这座桥被实际建立之前，本轮证明的是有严格前件的可行结构与误差判据。
当这些前件成立时，用户的直觉可精确写为：
$$
\boxed{\text{酉相容的整体结构}
\ +\ \text{固定关系标架}
\ +\ \text{守恒内容预算}
\ +\ \text{可纠错方向收缩}.}
$$
其中酉性保存整体信息，约束确定应保存的内容，恢复与收缩决定误差是否消退。

<a id="bibliography"></a>

## 固定来源

<a id="ref-head"></a>

**[1]**
[固定 dev 提交 64369c37c781](https://github.com/the-omega-institute/trureturing/commit/64369c37c781a34e67281ba38b315dc31fdf9115)。
2026-10-30 18:48:10 UTC；以下全部仓库链接固定于此提交。

<a id="ref-v28"></a>

**[2]**
[AURIC Binary Readout, Full-Frame Compatibility and E8 Golden Gate Bridge v28](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/docs/develop/theory/AURIC_BINARY_READOUT_FULL_FRAME_COMPATIBILITY_AND_E8_GOLDEN_GATE_BRIDGE_V28.md)。
§§3–4：二复振幅、Bloch 球、全标架条件与复结构；§§6.3–6.6：五模式占据读口及压缩边界。

<a id="ref-finite"></a>

**[3]**
[FiniteKrausReversibility.lean](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/D5/S3/Quantum/Recovery/FiniteKrausReversibility.lean)。
`scalar_products_construct_left_inverse`：标量误差乘积构造有限归一恢复。

<a id="ref-necessary"></a>

**[4]**
[KrausLeftInverseNecessity.lean](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/D5/S3/Quantum/Recovery/KrausLeftInverseNecessity.lean)。
`left_inverse_error_products`：实际有限 Kraus 左逆强制标量乘积。

<a id="ref-syndrome"></a>

**[5]**
[OrthogonalSyndromeDecoding.lean](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding.lean)。
`orthogonal_syndrome_recovery`：含相干综合征的全矩阵恢复。

<a id="ref-channel"></a>

**[6]**
[OrthogonalSyndromeChannel.lean](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel.lean)。
完整 CPTP 解码补全、正综合征编码与逻辑表示乘法律。

<a id="ref-robust"></a>

**[7]**
[AURIC FIB：实际仪器保留量子输出的稳健恢复障碍](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/docs/develop/theory/AURIC_FIB_ROBUST_ACTUAL_QUANTUM_RECOVERY.md)。
§1 与 §§11–12：实际完整输出、有限族与全参考恢复的量词及未决资源桥梁。

<a id="ref-czxwindow"></a>

**[8]**
[CZXParentLindbladianWindowChannel.lean](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/D5/S3/Quantum/TensorNetworks/CZXParentLindbladianWindowChannel.lean)。
四站点窗口的明确构造，`window_channels_commute` 与 `window_idempotent`。

<a id="ref-czxsteady"></a>

**[9]**
[CZXParentLindbladianSteadyState.lean](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState.lean)。
交换幂等指数极限、全算子投影公式及具体 CZX 初态的极限。

<a id="ref-control"></a>

**[10]**
[Stability of the Original-Control Instrument](https://github.com/the-omega-institute/trureturing/blob/64369c37c781a34e67281ba38b315dc31fdf9115/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md)。
§§1–5：完整输出距离、振荡反例与强导数误差充分条件。

## 追加锚（本行以下为增补区）
