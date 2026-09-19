
---

<a id="string-observer-born-geometry"></a>

# 谱约化的 Born 归一化、实验闭合与参数几何

## 接续 ST0–ST9 的理论增订 ST10–ST18

**范围与证明状态。** 本增订给出有限维复 Hilbert 空间上的证明、反例和误差界，承接 ST2 的带源 Schur 约化、ST3 的规范相容性和 ST5 的对偶运输。所有新命题均为普通数学证明，尚未生成或编译 Lean 真源。谱约化、Schrieffer–Wolff 变换、几何相位、子丛几何和无跃迁驱动各有既有文献；本文不主张这些一般机制首次发现。[ST10-Feshbach][ST10-SW][ST10-Subbundle][ST10-Driving]

以下正内积和 Born 规则是明确前提。接入弦场论时，必须先构造适当的物理态空间及其正内积，或者给出确切满足以下假设的子模型。含不定内积的整个 ghost/BRST 空间不能直接代入。BV 主方程、物理态正性、空间因果性与实验闭合是不同义务。有限矩阵证明不会自行建立弦真空、连续场论或 Einstein 方程。

固定 $\hbar>0$。未特别标注时，$\|\cdot\|$ 为算子范数，$\|\cdot\|_F$ 为 Frobenius 范数。这里的可见/隐藏分解是正交**直和** $\mathcal H=V\oplus W$，不是张量积分解上的偏迹。前者描述保留哪些态分量，后者描述子系统约化，二者不能混用。

## ST10．能量依赖消元同时决定物理范数

### 假设 ST10.1

设 $V,W$ 为非零有限维复 Hilbert 空间，

$$
H=\begin{pmatrix}A&B\\B^\dagger&C\end{pmatrix}=H^\dagger.
$$

取实数 $E\notin\operatorname{spec}C$，定义

$$
R_E=(C-EI)^{-1},\quad X_E=-R_EB^\dagger,\quad
L_E=\begin{pmatrix}I\\X_E\end{pmatrix},
$$

$$
S(E)=A-EI-BR_EB^\dagger.
$$

本节固定 $H$ 求能量导数。$E$ 可以位于完整 $H$ 的谱中，唯一排除的是隐藏块的谱。

### 定理 ST10.2：重建、范数与能量导数恒等式

有

$$
(H-EI)L_E=\begin{pmatrix}S(E)\\0\end{pmatrix},
\qquad
\ker S(E)\xrightarrow{\ L_E\ }\ker(H-EI)
\text{ 为线性同构},
\tag{ST10.1}
$$

以及

$$
\boxed{
G(E):=L_E^\dagger L_E
=I+B(C-EI)^{-2}B^\dagger
=-\partial_E S(E)>0.
}
\tag{ST10.2}
$$

**证明。** 块乘法给出(ST10.1)第一式。任一完整本征向量 $(v,w)$ 的第二块方程强制 $w=X_Ev$；若 $v=0$ 则 $w=0$。因此重建双向成立。又因 $R_E=R_E^\dagger$，有 $L_E^\dagger L_E=I+BR_E^2B^\dagger$。对 $(C-EI)R_E=I$ 求导，得 $\partial_E R_E=R_E^2$，代入 $S$ 得到最后一式。对 $v\ne0$，$v^\dagger Gv=\|v\|^2+\|X_Ev\|^2>0$。∎

### 推论 ST10.3：Born 读数及可见谱权重

对任意效果 $0\le O\le I_{\mathcal H}$ 和非零 $v\in V$，重建态的概率为

$$
\boxed{
p_O(v)=\frac{v^\dagger L_E^\dagger O L_Ev}{v^\dagger G(E)v}.
}
\tag{ST10.3}
$$

令 $\delta=\operatorname{dist}(E,\operatorname{spec}C)>0$。则

$$
I\le G(E)\le\left(1+\frac{\|B\|^2}{\delta^2}\right)I,
\qquad
\frac1{1+\|B\|^2/\delta^2}\le
Z(v):=\frac{\|v\|^2}{v^\dagger G(E)v}\le1.
\tag{ST10.4}
$$

**证明。** 将 $L_Ev$ 归一化并应用原空间的 Born 规则即可。有限维谱定理给出 $\|R_E\|=1/\delta$，再用 $\|R_EB^\dagger v\|\le\|B\|\|v\|/\delta$。∎

$Z$ 是完整纯态在原可见直和分量上的权重。保留非线性本征方程 $S(E)v=0$，却继续用 $v^\dagger v$ 代替完整范数，一般会改变概率。本定理没有从能谱独自推导 Born 公理；它推导的是给定 Born 公理在消元后的精确形式。不同能量上的 $G(E)$ 也不能直接拼成一个对任意叠加态有效的单一动力学，ST12处理这一问题。

## ST11．同一范数决定极点留数与能级几何响应

### 定理 ST11.1：简单极点留数

设 $E$ 为 $H$ 的简单本征值且 $E\notin\operatorname{spec}C$。取非零 $v\in\ker S(E)$，记 $P_V:\mathcal H\to V$ 为坐标投影。则

$$
\boxed{
\operatorname*{Res}_{z=E}
P_V(zI-H)^{-1}P_V^\dagger
=\frac{vv^\dagger}{v^\dagger G(E)v}.
}
\tag{ST11.1}
$$

**证明。** 归一化的完整本征向量为 $\psi=L_Ev/\sqrt{v^\dagger Gv}$。谱分解中 $(zI-H)^{-1}$ 的该留数为 $\psi\psi^\dagger$，左右投影即可。注意这里使用 $zI-H$；使用 $H-zI$ 时留数符号相反。∎

### 定理 ST11.2：参数化 Hellmann–Feynman 公式的下降

设 $H(u)$ 为 $C^1$ Hermitian 矩阵族，$E(u)$ 是简单本征值分支，且在所论区域始终不属于 $C(u)$ 的谱。令 $v(u)\ne0$ 满足 $S(E(u),u)v(u)=0$。则

$$
\boxed{
\frac{dE}{du}
=\frac{v^\dagger(\partial_u S)v}{v^\dagger Gv}
=\frac{(L_Ev)^\dagger(\partial_u H)(L_Ev)}{\|L_Ev\|^2}.
}
\tag{ST11.2}
$$

其中 $\partial_u S$ 在固定 $E$ 下取偏导。

**证明。** 在 $S v=0$ 上微分，左乘 $v^\dagger$，含 $dv/du$ 的项消失：

$$
v^\dagger(\partial_u S)v+\frac{dE}{du}v^\dagger(\partial_E S)v=0.
$$

用(ST10.2)得第一个等号。固定 $E$ 时，$S=L_E^\dagger(H-EI)L_E$，且 $\partial_uL_E$ 的上块为零。由 $(H-EI)L_E=(S,0)^{\mathsf T}$，求导中的两个 $\partial_uL_E$ 项消失，得到

$$
\partial_u S=L_E^\dagger(\partial_u H)L_E.
$$

这给出第二个等号。∎

若 $u$ 是已经定义好的度量、曲率或钟耦合扰动，式(ST11.2)给出相应能级响应。仍须从实际模型定义 $H(u)$；不能仅通过将 $u$ 命名为“几何”就得到引力场方程。$\partial_uH$ 的实验与能动量解释也需由原作用量确定。

### 例 ST11.3：省略范数会改变隐藏能量响应

取

$$
H=\begin{pmatrix}0&b\\b&c\end{pmatrix},\quad b,c>0,
\qquad E_-=\frac{c-\sqrt{c^2+4b^2}}2,
\quad r=\frac b{c-E_-}.
$$

则 $L_{E_-}(1)=(1,-r)^{\mathsf T}$，

$$
Z=\frac1{1+r^2},\qquad
\frac{\partial E_-}{\partial c}=\frac{r^2}{1+r^2}=1-Z.
\tag{ST11.3}
$$

在 $b=c=\Delta>0$ 时，$r=\varphi^{-1}$，隐藏权重为

$$
1-Z=\frac12\left(1-\frac1{\sqrt5}\right).
$$

省略分母会得到错误的 $\varphi^{-2}$。黄金数在这里来自一个明确二阶特征方程；参数关系 $b=c$ 是模型选择，不是所有量子系统必须遵守的规律。

## ST12．由不变图子空间构造真正的有效量子理论

### 假设 ST12.1

给定 $X:V\to W$，满足矩阵 Riccati 方程

$$
B^\dagger+CX=X(A+BX).
\tag{ST12.1}
$$

定义

$$
L=\begin{pmatrix}I\\X\end{pmatrix},\quad
G=I+X^\dagger X,\quad K=A+BX,\quad
U=LG^{-1/2},\quad\Pi=UU^\dagger.
$$

这等价于 $\operatorname{Ran}L$ 为 $H$ 的不变图子空间。一个预选谱子空间能用这样的 $X$ 表示，当且仅当其到 $V$ 的投影为同构；这是一项横截性条件。本文不假设任意截断都满足它，也不把任意不变子空间自动称为低能子空间。其与严格 Schrieffer–Wolff/子空间旋转构造的关系见[ST10-SW]。

### 定理 ST12.2：等距重建与自伴有效 Hamiltonian

有

$$
HL=LK,\quad GK=K^\dagger G,\quad U^\dagger U=I,
$$

$$
\boxed{
h:=U^\dagger HU=G^{1/2}KG^{-1/2}=h^\dagger,
\qquad HU=Uh.
}
\tag{ST12.2}
$$

从而对全部实数 $t$，

$$
\boxed{e^{-itH/\hbar}U=Ue^{-ith/\hbar}.}
\tag{ST12.3}
$$

**证明。** Riccati 方程给出块等式 $HL=LK$。$L^\dagger HL$ 为 Hermitian，故 $GK=K^\dagger G$。正定平方根给出 $U^\dagger U=I$。共轭 $K$ 得到 $h$ 并验证交织式；将交织式逐次相乘，再代入矩阵指数的绝对收敛幂级数，得到(ST12.3)。∎

### 推论 ST12.3：实际效果与全部叠加态一同转移

映射 $\rho\mapsto U\rho U^\dagger$ 为 CPTP 编码，$O\mapsto U^\dagger OU$ 为幺完全正的效果拉回。对任意密度态 $\rho$、效果 $O$ 和实数 $t$，完整编码态与有效态给出相同的该时刻读数。

**证明。** 两个映射均有单 Kraus 表示，$U^\dagger U=I$ 给出保迹/保单位性。迹的循环性与(ST12.3)给出统计相等。∎

这保证初始编码后、一次最终读数的相等；中途仪器会不会把态推出编码子空间，仍需下一节的独立条件。

## ST13．能谱闭合不能替代连续实验闭合

### 定理 ST13.1：仪器压缩的精确漏出算子

取有限 Kraus 仪器 $\{K_{a\ell}\}$，满足

$$
\sum_{a,\ell}K_{a\ell}^\dagger K_{a\ell}=I_{\mathcal H}.
$$

令 $k_{a\ell}=U^\dagger K_{a\ell}U$。则

$$
\boxed{
\sum_{a,\ell}k_{a\ell}^\dagger k_{a\ell}=I_V-\Lambda,
\quad
\Lambda=\sum_{a,\ell}U^\dagger K_{a\ell}^\dagger(I-\Pi)K_{a\ell}U\ge0.
}
\tag{ST13.1}
$$

以下条件等价：$\Lambda=0$；全部 $K_{a\ell}\operatorname{Ran}U\subseteq\operatorname{Ran}U$；压缩 Kraus 家族组成归一仪器。

**证明。** 在每个 $U^\dagger K^\dagger KU$ 中插入 $I=\Pi+(I-\Pi)$，得到恒等式。且

$$
v^\dagger\Lambda v=
\sum_{a,\ell}\|(I-\Pi)K_{a\ell}Uv\|^2.
$$

它对所有 $v$ 为零，当且仅当每个漏出算子都为零。归一性等价由(ST13.1)立即得到。∎

一次结果 $a$ 的正确压缩效果始终是

$$
F_a=U^\dagger\left(\sum_\ell K_{a\ell}^\dagger K_{a\ell}\right)U
=\sum_\ell k_{a\ell}^\dagger k_{a\ell}+\Lambda_a.
$$

因此单步概率可保持，而丢掉 $\Lambda_a$ 后的状态更新未必合法。单独加一个“漏出”经典标签可以补上总概率，但该标签一般不能决定漏出态的全部未来实验。

### 定理 ST13.2：有限自适应记录的精确转移

采用 ST12 的固定编码 $U$。假设每一种允许控制 Hamiltonian 均保留 $\operatorname{Ran}U$，且每一个允许仪器满足 ST13.1 的零漏出条件。则对任意初始密度态、任意有限轮按以往结果选取操作的协议，压缩模型与完整编码模型的所有联合记录概率及每条未归一化分支态完全相容。

**证明。** 对每个允许 Kraus 算子，零漏出给出 $KU=Uk$；对每段演化用(ST12.3)。任一固定历史的算子词因而满足 $W_{\mathbf a}U=Uw_{\mathbf a}$。对不可见 Kraus 标签求和后，各分支仍满足

$$
\mathcal I_{\mathbf a}(U\rho U^\dagger)
=U\,\mathfrak i_{\mathbf a}(\rho)U^\dagger.
$$

取迹得到联合概率相等。自适应协议在固定历史上确定一个这样的词，故逐历史成立；零概率历史不被删除。∎

### 反例 ST13.3：质量隙再大也不保证任意实验闭合

取 $H=\operatorname{diag}(0,\Delta)$，$\Delta>0$，$U(1)=|0\rangle$。这是精确不变子空间，原跨块耦合为零。允许一次 Pauli $X$ 操作，则 $U^\dagger XU=0$，$\Lambda=1$。完整实验将 $|0\rangle$ 送到 $|1\rangle$，压缩操作却消灭了全部范数。

所以，允许仪器的实验语言是有效理论的一部分。仅检查质量隙或有效能谱，不能认证任意测量历史。

## ST14．由 Riccati 残差控制全部最终记录

### 定理 ST14.1：非精确图子空间的动力学误差

不再假设 Riccati 方程。仍由任意 $X$ 构造 $L,G,U,\Pi$，并令 $h=U^\dagger HU$。定义

$$
\mathcal R_X=B^\dagger+CX-X(A+BX),\quad
D=HU-Uh.
$$

则

$$
\boxed{
D=(I-\Pi)\begin{pmatrix}0\\\mathcal R_X\end{pmatrix}G^{-1/2},
\qquad r:=\|D\|\le\|\mathcal R_X\|.
}
\tag{ST14.1}
$$

并且

$$
\boxed{
\|e^{-itH/\hbar}U-Ue^{-ith/\hbar}\|
\le\min\{2,|t|r/\hbar\}.
}
\tag{ST14.2}
$$

**证明。** 有 $HL=L(A+BX)+(0,\mathcal R_X)^{\mathsf T}$。左乘 $I-\Pi$ 后第一项为零，得到(ST14.1)。$G\ge I$ 给出范数界。对 $e^{-i(t-s)H/\hbar}Ue^{-ish/\hbar}$ 求导并积分：

$$
e^{-itH/\hbar}U-Ue^{-ith/\hbar}
=-\frac{i}{\hbar}\int_0^t
 e^{-i(t-s)H/\hbar}D e^{-ish/\hbar}\,ds.
$$

两侧演化均酉，故积分范数至多 $|t|r/\hbar$；两个等距映射之差另有上界2。∎

### 推论 ST14.2：Born 记录的统一误差预算

从同一输入态出发，比较以上两种编码演化，再实施任意共同的 CPTP 实验并保留全部结果。允许初始态与一个不参与演化的有限参考系统纠缠。最终联合记录分布满足

$$
\boxed{\operatorname{TV}(p,q)\le\min\{1,|t|r/\hbar\}.}
\tag{ST14.3}
$$

**证明。** 对纯化输入，两种输出向量之差范数不超过(ST14.2)中的 $|t|r/\hbar$，其纯态迹距离不超过向量差范数。对混态用纯化及偏迹收缩性。随后共同 CPTP 实验保持迹距离收缩，最终经典化得到总变差界。∎

多个演化段之间若采用 ST13 的精确子空间保持仪器，可用逐段替换和通道收缩性将上界相加。第 $j$ 段由既往记录 $a$ 决定时，一个安全预算为

$$
\min\left\{1,\sum_j\sup_a\frac{|t_j(a)|r_j(a)}{\hbar}\right\}.
$$

这个界控制完整未后选择的记录；稀有事件条件化需另外给出成功概率下界。存在仪器漏出时，$\mathcal R_X$ 并未计入它，不能继续沿用仅含 $r$ 的预算。

## ST15．移动的保留空间产生连接、曲率和跃迁代价

### 假设 ST15.1

在一个参数开集内，$X=X(\lambda)$ 为 $C^2$ 矩阵族，$U=LG^{-1/2}$。先固定一个物理上已标定的环境 Hilbert 基，使用普通导数。定义

$$
\mathcal A_i=iU^\dagger\partial_iU,\quad
N_i=(I-\Pi)\partial_iU,\quad
\mathcal Q_{ij}=N_i^\dagger N_j.
$$

$\mathcal A_i$ 为 Hermitian；参数 $\lambda$ 可以是耦合、动量或已标定背景参数，不能默认就是物理时空坐标。

### 定理 ST15.2：隐藏图的量子几何张量

有

$$
\boxed{
\mathcal Q_{ij}
=G^{-1/2}(\partial_iX)^\dagger
(I_W+XX^\dagger)^{-1}(\partial_jX)G^{-1/2}.
}
\tag{ST15.1}
$$

相应连接曲率为

$$
\boxed{
\mathcal F_{ij}:=\partial_i\mathcal A_j-\partial_j\mathcal A_i
-i[\mathcal A_i,\mathcal A_j]
=i(\mathcal Q_{ij}-\mathcal Q_{ji}).
}
\tag{ST15.2}
$$

**证明。** $\partial_iU=(\partial_iL)G^{-1/2}+L\partial_iG^{-1/2}$。投影到法向时第二项为零。对下块嵌入 $E_W:w\mapsto(0,w)$，块计算与 Woodbury 恒等式给出

$$
E_W^\dagger(I-\Pi)E_W
=I-X(I+X^\dagger X)^{-1}X^\dagger
=(I+XX^\dagger)^{-1}.
$$

这证明(ST15.1)。再令 $K_i=U^\dagger\partial_iU=-i\mathcal A_i$。展开 $\partial_iK_j-\partial_jK_i+[K_i,K_j]$，用 $\partial_iU=UK_i+N_i$ 消掉切向项，剩余 $\mathcal Q_{ij}-\mathcal Q_{ji}$，乘以 $i$ 即得(ST15.2)。∎

对任意参数系数与内部向量族，$\sum_{ij}v_i^\dagger\mathcal Q_{ij}v_j=\|\sum_jN_jv_j\|^2\ge0$。因此 $g_{ij}^{\mathrm{par}}=\operatorname{Re}\operatorname{tr}\mathcal Q_{ij}$ 半正定。它是参数可辨识几何；其号型一般不是洛伦兹号型，不能将它直接等同于本卷第29节的时空度量。该子丛机制的广义几何背景见[ST10-Subbundle]。

### 定理 ST15.3：不变谱子空间的间隙控制

再假设 $H(\lambda)U(\lambda)=U(\lambda)h(\lambda)$。令保留与正交补中完整 Hamiltonian 的谱距离为 $\Delta>0$，它与 ST10 的隐藏块距离 $\delta$ 是不同对象。则

$$
\boxed{
\|N_i\|_F\le
\frac{\|(I-\Pi)(\partial_iH)U\|_F}{\Delta}.
}
\tag{ST15.3}
$$

因而

$$
\|\mathcal F_{ij}\|
\le\frac{2}{\Delta^2}
\|(I-\Pi)(\partial_iH)U\|_F
\|(I-\Pi)(\partial_jH)U\|_F.
\tag{ST15.4}
$$

**证明。** 微分交织式并投影到补空间，得到 Sylvester 方程

$$
H_\perp N_i-N_i h=-(I-\Pi)(\partial_iH)U.
$$

分别选择 $H_\perp,h$ 的正交本征基，每个矩阵元被相应能量差除，绝对值分母至少为 $\Delta$。对平方求和即得 Frobenius 界；再用(ST15.2)及 $\|N\|\le\|N\|_F$。没有把任意交错谱下的该 Frobenius 论证误当成同常数的算子范数逆 Sylvester 定理。∎

### 定理 ST15.4：移动编码的生成元与确切控制项

沿光滑时间路径，编码内方程的 Hermitian 生成元是

$$
\boxed{h_{\mathrm{mov}}=U^\dagger HU-i\hbar U^\dagger\dot U
=h-\hbar\mathcal A_t.}
\tag{ST15.5}
$$

相对于完整 Schrödinger 方程，它的法向残差为

$$
D_t=(I-\Pi)HU-i\hbar N_t.
$$

对应传播子的等距交织误差至多 $\hbar^{-1}\int\|D_t\|dt$。

**证明。** 将 $\psi=Uv$ 代入 $i\hbar\dot\psi=H\psi$ 并左乘 $U^\dagger$ 得到(ST15.5)。剩余法向部分为 $D_t$。对两个时变酉传播子采用与 ST14 相同的微分积分恒等式。∎

即使 $HU=Uh$ 逐时刻成立，$N_t$ 仍可能非零。此时上述粗界是 $\int\|N_t\|dt$，减慢沿同一路径的运动并不会自动缩小这个路径长度界；更锐的绝热定理还需能隙、光滑性和振荡抵消分析。

若允许加入实际控制 Hamiltonian

$$
\boxed{H_{\mathrm{cd}}=i\hbar[\dot\Pi,\Pi],}
\tag{ST15.6}
$$

则对逐时刻不变子空间有 $(I-\Pi)H_{\mathrm{cd}}U=i\hbar N_t$，所以法向残差严格为零。且 $U^\dagger H_{\mathrm{cd}}U=0$，$\|H_{\mathrm{cd}}\|=\hbar\|N_t\|$。

**证明。** 由 $\Pi^2=\Pi$ 得 $\Pi\dot\Pi\Pi=0$，且微分 $\Pi U=U$ 给出 $\dot\Pi U=N_t$。因此(ST15.6)作用在 $U$ 上为 $i\hbar N_t$。$\dot\Pi$ 对子空间/补空间只有非对角块，块范数即给出最后的等式。该控制有实际作用强度和实现条件，不能被当作免费的观察者坐标选择；一般无跃迁驱动机制见[ST10-Driving]。∎

## ST16．相同定态响应可以隐藏不同的闭路相位

### 定理 ST16.1：一个完全可算的不可识别性见证

取 $c>a$、$b>0$，在固定环境基中令

$$
H(\theta)=
\begin{pmatrix}a&be^{-i\theta}\\be^{i\theta}&c\end{pmatrix},
\qquad
E_-=\frac{a+c-\sqrt{(c-a)^2+4b^2}}2,
\qquad r=\frac b{c-E_-}.
$$

对应归一化基态可取

$$
U(\theta)=\frac{(1,-re^{i\theta})^{\mathsf T}}{\sqrt{1+r^2}},
\quad Z=\frac1{1+r^2},\quad p=1-Z.
$$

只从第一分量驱动并读取，其全部冻结参数响应为

$$
\boxed{
\chi_{00}(z;\theta)
=\frac{z-c}{(z-a)(z-c)-b^2},
}
\tag{ST16.1}
$$

与 $\theta$ 无关，但完整绕行 $0\le\theta\le2\pi$ 的几何相位为

$$
\boxed{\gamma=-2\pi p=-2\pi(1-Z)\pmod{2\pi}.}
\tag{ST16.2}
$$

**证明。** 直接块逆得到(ST16.1)。该本征向量光滑且周期闭合，$iU^\dagger\partial_\theta U=-p$；积分即得(ST16.2)。这里的几何相位在适当绝热实现中可读取，也可借 ST15.6 的显式控制实现精确的无泄漏运输。控制须计入完整实验。∎

对照实验固定 $H(0)$ 不变，而只让一个无物理作用的标签绕行，得到相同的全部冻结响应，却得到零几何相位。因为 $0<p<1/2$，两个相位在模 $2\pi$ 后仍不同。因此，冻结响应数据不能唯一决定这类时序实验。

在 $a=0,c=b=\Delta>0$ 的例子中，$r=\varphi^{-1}$，

$$
\gamma=-\pi\left(1-\frac1{\sqrt5}\right).
$$

此值直接连接 ST11 的隐藏权重与闭路相位。它是该具体二态模型的精确结果，不是一个由黄金算术唯一决定的普适引力常数。

### ST16.2：主动改变耦合与被动换基的区别

虽然 $H(\theta)=W(\theta)H(0)W(\theta)^\dagger$，其中 $W=\operatorname{diag}(1,e^{i\theta})$，但对时变态坐标 $\psi'=W\psi$，被动变换后的生成元包含

$$
H'=WHW^\dagger+i\hbar\dot W W^\dagger.
$$

直接令真实实验的 Hamiltonian 等于 $H(\theta)$ 没有自动包含这个惯性项，因而是不同的驱动。运输全部探针与连接后，纯粹换基不会改变物理结果。本反例没有否定对偶；它说明 ST5 中逐参数的响应相等，不足以代替整条实验路径的运输相等。

这一实验层区分与 Oh–Murakami 2026年预印本关于有效 Hamiltonian 还需配套物理位置/电流接口的讨论相邻；本节证明仅依赖上述二态矩阵，不将该预印本的所有结论作为前提。[ST10-Embedding]

## ST17．已有背景曲率与子空间选择曲率的协变组合

### 假设 ST17.1

在参数域的环境 Hermitian 向量丛上，给定连接

$$
\nabla_i=\partial_i-i\Gamma_i,\qquad \Gamma_i=\Gamma_i^\dagger,
\qquad
F^{\mathrm{full}}_{ij}=\partial_i\Gamma_j-\partial_j\Gamma_i-i[\Gamma_i,\Gamma_j].
$$

对局部等距框 $U$，定义

$$
\mathcal A_i=iU^\dagger\nabla_iU
=U^\dagger\Gamma_iU+iU^\dagger\partial_iU,
\qquad N_i=(I-\Pi)\nabla_iU.
$$

### 定理 ST17.2：有效曲率的协变分解

有

$$
\boxed{
\mathcal F_{ij}
=U^\dagger F^{\mathrm{full}}_{ij}U
+i\left(N_i^\dagger N_j-N_j^\dagger N_i\right).
}
\tag{ST17.1}
$$

**证明。** 写 $K_i=U^\dagger\nabla_iU=-i\mathcal A_i$，则 $\nabla_iU=UK_i+N_i$。相容连接保持内积，微分 $K$ 并反对称化得

$$
\partial_iK_j-\partial_jK_i+[K_i,K_j]
=U^\dagger[\nabla_i,\nabla_j]U
+N_i^\dagger N_j-N_j^\dagger N_i.
$$

使用 $[\nabla_i,\nabla_j]=-iF^{\mathrm{full}}_{ij}$，乘以 $i$ 即得。∎

在内部框变换 $U\mapsto UV(\lambda)$，$V$ 酉时，

$$
\mathcal A_i\mapsto V^\dagger\mathcal A_iV+iV^\dagger\partial_iV,
\qquad\mathcal F_{ij}\mapsto V^\dagger\mathcal F_{ij}V.
$$

所以适当闭路 holonomy 的共轭类是框不变量。若连环境基也改变，必须一同运输 $\Gamma$。这正是 ST16 被动变换必须保留惯性项的协变表达。

若 $\Gamma=\Gamma_V\oplus\Gamma_W$ 保持原分块，ST15.1 中的 $\partial_iX$ 可替换成

$$
D_iX=\partial_iX-i\Gamma_{W,i}X+iX\Gamma_{V,i},
$$

得到 $N_i^\dagger N_j$ 的同样图坐标公式。证明只需在法向投影前写出 $\nabla_iL-L(-i\Gamma_{V,i})=(0,D_iX)^{\mathsf T}$。

该式是向量子丛几何中的经典结构；Oancea–Mieling–Palumbo 已在2026年论文中系统研究了含环境曲率的量子几何张量，并讨论曲时空 Dirac 场的应用。[ST10-Subbundle] 本文增加的是与前述 Schur/Born 范数、实际仪器闭合和可计算二态见证的同一套记号与证明接口，不将(ST17.1)的普遍形式据为新发现。

**几何类型边界。** $F^{\mathrm{full}}$ 是已指定量子态运输连接的曲率。只有在另有明确构造时，它才可来自某个时空自旋连接或其他物理几何。$\mathcal F$ 的第二项来自保留子空间的变化。二者都不能单靠同名“曲率”与 Einstein 张量认同。环境本来有曲率时，将有效曲率全部归于隐藏模式，也会漏掉第一项。

## ST18．谱、实验与几何的共同约化命题

### 定理 ST18.1：协议保持的有限维约化

在正 Hilbert 空间中固定 Hermitian Hamiltonian、一个横截的不变子空间及其图坐标 $X$，并规定允许控制与仪器族。若所有允许操作保留该子空间，则由

$$
U=(I,X)^{\mathsf T}(I+X^\dagger X)^{-1/2}
$$

构造的有效理论具有以下同时成立的性质：完整态范数与效果读数由 ST10–ST12 的等距编码保持；所有有限自适应联合记录由 ST13 保持；在光滑参数变化及给定环境连接下，诱导连接和曲率由 ST15–ST17 确定。近似图子空间的演化误差可用 ST14 的残差控制，仪器漏出仍需单独控制。

**证明。** 静态部分由 ST12.2 与 ST12.3；词级实验部分由 ST13.2；几何部分由定义等距编码后直接应用 ST15.2、ST17.2。ST14明确量化离开精确不变性时的误差。能量依赖的单根图与固定整个子空间的图不互相替代，故只在各自假设覆盖处使用 ST10与ST11。∎

**接入弦论的条件性推论。** 若一个指定弦模型的规范相容有效构造，进一步提供以上正态空间、Hamiltonian、保留子空间、实际仪器及连接，则本命题可用于认证该模型中相应实验的约化。Sen 的量子 BV 积分和弦场论的树级同伦转移提供规范结构方面的外部输入，仍须逐项识别这些正 Hilbert 空间对象；不能用 BV 方程自动替代仪器零漏出，也不能把有限维误差界无条件用于无限弦塔。[ST-Sen][ST10-HomotopyII]

由此形成三个有不同反例的条件：ST3控制规范恒等式，ST13控制干预后继续预测的能力，ST17控制对整条参数路径的相容运输。ST13.3和ST16.1分别证明，只有精确能谱或全部冻结响应时，后两项仍可能失败。

**书目与归属。** 以下为本增订新增主要来源；日期状态核对至2026-09-17。本文有限矩阵证明自含，数值核验仅作错误探测，不替代普遍证明；未对全部既有文献或仓库逐定理穷尽查重。

[ST10-Feshbach]: https://arxiv.org/abs/2105.02058 "Genevieve Dusson, Israel Sigal, Benjamin Stamm, The Feshbach-Schur map and perturbation theory (2021). Discrete self-adjoint spectra and explicit estimates."
[ST10-SW]: https://arxiv.org/abs/1105.0675 "Sergey Bravyi, David DiVincenzo, Daniel Loss, Schrieffer-Wolff transformation for quantum many-body systems, Annals of Physics 326 (2011) 2793–2826, DOI 10.1016/j.aop.2011.06.004."
[ST10-Subbundle]: https://arxiv.org/abs/2503.17163 "Marius A. Oancea, Thomas B. Mieling, Giandomenico Palumbo, Quantum geometric tensors from sub-bundle geometry, Quantum 10, 1965 (2026), DOI 10.22331/q-2026-01-14-1965. The general framework and extra ambient-curvature contribution belong to these authors."
[ST10-Driving]: https://doi.org/10.1088/1751-8113/42/36/365303 "M. V. Berry, Transitionless quantum driving, Journal of Physics A: Mathematical and Theoretical 42 (2009) 365303."
[ST10-Embedding]: https://arxiv.org/html/2607.21882v1 "Chang-geun Oh and Shuichi Murakami, Orbital Embedding and the Physical Definition of Quantum Geometry, arXiv:2607.21882v1, 24 July 2026. Preprint, used for the neighboring operational question, not as a premise for the two-state proof."
[ST10-HomotopyII]: https://arxiv.org/abs/2106.08343 "Alex S. Arvanitakis, Olaf Hohm, Chris Hull, Victor Lekeu, Homotopy Transfer and Effective Field Theory II: Strings and Double Field Theory, Fortschritte der Physik 70 (2022) 2200004, DOI 10.1002/prop.202200004. Tree-level scope retained."

---
