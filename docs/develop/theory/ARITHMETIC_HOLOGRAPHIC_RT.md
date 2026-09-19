# 算术全息量子网络与 Ryu–Takayanagi 型恒等式

本卷研究有限循环环上的量子张量网络、几何最小割、相干历史与跨尺度量子通道。全文结论采用明确的有限维假设；证明为纸面数学证明，尚无配套 Lean 内核证明，不据此认领原始引力 RT、物理 AdS/CFT 对偶或开放问题结算。具体构造的文献优先权尚未确认。

## 1. 对象、来源与证明边界

所有对数取自然对数。密度矩阵的熵为 $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$，零本征值按连续延拓处理。$R_d=\mathbb Z/d\mathbb Z$，其中 $d\ge3$ 为奇数。$\omega_d=\exp(2\pi i/d)$。本卷使用循环环 $\mathbb Z/p^n\mathbb Z$，不以有限域 $\mathbb F_{p^n}$ 替代。

图的内部顶点四价，悬空腿视为接到独立边界顶点的边；每条边承载 $\mathbb C^d$。对边界子集 $C$，$m(C)$ 是在所有内部顶点的二侧分配中，将 $C$ 与其补集分开的最少割边数，边界边允许被割。割容量 $m(C)\log d$ 先由图定义，独立于网络态。

本卷接续以下已有接口，而不重复认领其形式化内容：

- `D5/S3/Quantum/Entanglement/QutritThresholdSharing.lean` 的编码、单份最大混合与两份恢复。
- `D5/S3/Observer/WindowRegister.lean`、`D5/S3/Quantum/Algebra/WeylPhaseArithmetic.lean` 的循环窗口、原始单位根及相位运算。
- `D5/S3/Fourier/FinitePoisson.lean` 的有限字符正交性与湮灭子。
- `D5/S3/Quantum/Entanglement/CoherentHistorySchmidt.lean` 的实际系数矩阵、秩和 Schmidt 权重。

上述源码在提交 `280905f8378cd6ed5c3ba94076853d3814b139be` 已有。本卷是新证明输入，不声称这些源码已经证明本卷结论。与既有卷的关系是：[情境时空算术量子卷](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) 提供量子记录与相干历史语境；[QUANTUM-RH](QUANTUM-RH.md) 评注 29.4 提供 M2 相容读数和算术全息接口。本卷独立处理量子态的谱、图割与相位，不把边界可重建直接等同于 RT。

## 2. 奇数循环窗口上的局部完美张量

**定义 2.1。** 令

$$
|T_d\rangle=\frac1d\sum_{x,y\in R_d}|x,y,x+y,x+2y\rangle.
$$

**命题 2.2。** $T_d$ 的任意二腿约化态都是 $I_{d^2}/d^2$，任意单腿约化态都是 $I_d/d$。

**证明。** 四个线性形式 $x,y,x+y,x+2y$ 中任取两个，其系数矩阵的行列式为 $\pm1$ 或 $\pm2$，在奇数模环中都是单位。故对任意二对二划分，两侧的坐标映射都是 $R_d^2$ 的双射。偏迹后所有交叉项消失，恰有 $d^2$ 个相等对角项。单腿结论由进一步偏迹得到。将该张量看作从至多两条腿到其余腿的映射时，乘以相应正常数即为等距映射。证毕。

当 $d=3$ 时，仓库编码为

$$
V|s\rangle=\frac1{\sqrt3}\sum_j|j,j+s,j+2s\rangle.
$$

将输入与参考 qutrit 最大纠缠，取 Choi 态并交换前两腿，即得 $T_3$。这给出了局部张量与实际已有编码的对象对应。

## 3. 普通闭环的精确算术熵亏损

取 $L\ge3$ 个顶点组成一个简单环。顶点 $i$ 的内部变量为 $x_i,x_{i+1}$，普通缝合要求 $x_L=x_0$；边界输出为

$$
a_i=x_i+x_{i+1},\qquad b_i=x_i+2x_{i+1}.
$$

令 $A$ 含全部 $a_i$，$B$ 含全部 $b_i$。归一化态为

$$
|\Psi^0_{d,L}\rangle=d^{-L/2}\sum_{x\in R_d^L}|(I+P)x\rangle_A|(I+2P)x\rangle_B,
$$

其中 $(Px)_i=x_{i+1}$。联合映射单射，因为 $b-a=Px$，故此归一化准确。

**定理 3.1（奇环亏损）。** 若 $L$ 为奇数，则

$$
S(\rho_A)=L\log d-\log\gcd(d,2^L+1).
$$

非零本征值全部相等；所有正阶 Rényi 熵也等于右侧。

**证明。** $\det(I+P)=2$，故 $I+P$ 在 $R_d$ 上可逆。对 $A$ 偏迹后，$\rho_B$ 是线性映射 $I+2P$ 的均匀像分布。其核满足

$$
x_{i+1}=-2^{-1}x_i,\qquad (2^L+1)x_0=0\pmod d.
$$

末式恰有 $g=\gcd(d,2^L+1)$ 个解。每个像点都有 $g$ 个原像，故实际秩为 $d^L/g$，每个非零本征值为 $g/d^L$。证毕。

这个划分的几何最小割恰为 $L$：每个内部顶点各接一个 $A$ 叶和一个 $B$ 叶，无论顶点归于哪侧都至少割一条边界边；将所有内部顶点归于同侧达到 $L$。

对 $d=3^n$，亏损为

$$
Ln\log3-S(\rho_A)=\min\{n,v_3(2^L+1)\}\log3.
$$

例如 $L=3$ 时，$S(\rho_A)=[3n-\min(n,2)]\log3$。因此局部完美性不足以保证任意闭环的精确 RT 饱和；此例没有建立物理引力对偶，不能作为物理 RT 的反例。

## 4. 保持连接维数的 Fourier 相位缝合

**定义 4.1。** 对 $\alpha\in R_d$，令

$$
U_\alpha(u,v)=d^{-1/2}\omega_d^{uv+\alpha v^2}.
$$

它是归一化 Fourier 矩阵与对角二次相位的乘积，因此幺正。只把环的一条内部连接由普通指标相等收缩改为 $U_\alpha$，其余张量、图和连接维数保留。

相应归一化边界态明确为

$$
|\Psi^\alpha_{d,L}\rangle=d^{-(L+1)/2}
\sum_{x_0,\ldots,x_L\in R_d}
\omega_d^{x_0x_L+\alpha x_0^2}
\bigotimes_{i=0}^{L-1}|x_i+x_{i+1}\rangle_{a_i}|x_i+2x_{i+1}\rangle_{b_i}.
$$

路径到全部边界输出的映射仍单射。缝合连接仍为最大纠缠连接。该操作改变全局量子态；它没有同时在相邻张量做补偿，故不只是内部基底换名。

## 5. 所有区域精确饱和的充要判据

**定理 5.1（相位单位判据）。** 定义

$$
c_k=2\alpha+(-1)^L\bigl(2^{-k}+2^{-(L-k)}\bigr)\in R_d,
\qquad 0\le k\le L.
$$

第 4 节的态对每个边界子集 $C$ 满足

$$
S(\rho_C)=m(C)\log d
$$

当且仅当所有 $c_k$ 都是 $R_d$ 的单位。

**证明。** 分三步。

任意含 $q$ 条边的割给出跨割指标空间 $\mathbb C^{d^q}$，故 $\operatorname{rank}\rho_C\le d^q$、$S(\rho_C)\le q\log d$。对割取最小值，得到全局上界。

先处理每个顶点恰有一条边界腿属于 $C$ 的情形。令其选择的输出系数为 $w_i\in\{1,2\}$，补集系数为 $\bar w_i=3-w_i$。固定 $C$ 输出 $c$ 后，递推

$$
x_{i+1}=w_i^{-1}(c_i-x_i)
$$

只留下自由变量 $z=x_0$，且

$$
x_L=s_Cz+f(c),\qquad s_C=(-1)^L\left(\prod_iw_i\right)^{-1}.
$$

偏迹交叉项要求两条路径的补集输出相同。它们的差满足

$$
\delta x_{i+1}=-\bar w_i^{-1}\delta x_i,
\qquad \delta x_0=t,\qquad \delta x_L=s_{\bar C}t.
$$

给定两组 $C$ 输出时，$t$ 若存在便唯一，因为 $\delta c_0=(w_0-\bar w_0)\delta x_1$，其系数为单位。令 $Q(x)=x_0x_L+\alpha x_0^2$，直接计算得

$$
Q(x+\delta x)-Q(x)=(2\alpha+s_C+s_{\bar C})tz+\text{与 }z\text{ 无关的项}.
$$

若 $C$ 选择了 $k$ 条 $b_i$，其交叉项因而含有字符和

$$
\sum_{z\in R_d}\omega_d^{c_ktz}.
$$

$c_k$ 为单位时，该和对所有非零 $t$ 都为零；对角项给出 $\rho_C=I_{d^L}/d^L$。这一划分的最小割为 $L$，故达到上界。

反过来，若 $c_k$ 非单位，存在非零 $t$ 满足 $c_kt=0$。沿上述差路径移动得到不同的 $C$ 输出，交叉项的绝对值为 $d^{-L}$，因此 $\rho_C\ne I_{d^L}/d^L$，其熵严格小于 $L\log d$。所有单位条件也必要。

最后处理其余划分。此时某个环顶点的两条边界腿同属一侧，利用命题 2.2 将该顶点吸收到该侧。尚未吸收的内部图变成森林。森林叶顶点至多连接一个未吸收邻居，至少三条腿已由两侧标记，其中至少两条同侧；再次用完美张量等距吸收，直到结束。单腿上的 $U_\alpha$ 可并入相邻张量而保持完美性。最终两侧是局部等距映射，中间为 $q$ 条最大纠缠连接。它们给出实际割和精确 Schmidt 分解，故 $S(\rho_C)=q\log d$；结合全局上界与 $m(C)\le q$，得到 $q=m(C)$。证毕。

## 6. 三进窗口与附树单环

**定理 6.1。** 对任意 $n\ge1$、$L\ge3$，取 $d=3^n$ 和

$$
\alpha_L=\begin{cases}1,&L\text{ 为奇数},\\0,&L\text{ 为偶数}.\end{cases}
$$

则对所有边界区域 $C$，

$$
S(\rho_C)=m(C)n\log3.
$$

**证明。** 模 $3$ 时 $2^{-1}=-1$。若 $L$ 为奇数，$s_C+s_{\bar C}=0$，故 $c_k=2$；若 $L$ 为偶数，$c_k=2(-1)^k$。所有系数均非零，因而在每个 $\mathbb Z/3^n\mathbb Z$ 中都是单位。应用定理 5.1。证毕。

**推论 6.2。** 在该环的外部腿上连接任意有限树，所有内部顶点仍四价且使用 $T_d$，所有悬空腿作为边界。环顶点保留第 3 节所定的两条环内腿，树上腿排列可任意固定。保持原环上一条边的缝合规则，则上述等式对完整装饰图的全部边界区域成立。

**证明。** 从附加树的外部叶顶点开始等距吸收。若环被打断，余下按森林处理；若完整环保留，其每个顶点有两条已标记外部腿。同侧时再次打断；否则核心正是第 5 节的逐顶点分腿问题。等距映射和已分离的最大纠缠连接保留所述 Schmidt 分解与实际割。证毕。

此处限定一个简单环，$L\ge3$，不包含自环、双边环或任意多环图。

## 7. 文献定位与尚未证明的接口

RT 原文 [RT] 将边界纠缠熵与对偶引力最小面积联系起来；[LM] 在引力复制构造的假设下推导相应关系。[HaPPY] 和 [Harlow] 已建立完美张量、量子纠错及互补恢复中的 RT 型结果。[HMPS] 已处理 Bruhat–Tits 树及 Schottky 商的对偶网络，包括连接和不连接区域。本卷的固定四腿循环模环网络不等同于其具体构造，第 3 节不是该工作的反例。

本卷尚未构造一套对任意逻辑体态定义的编码 $\mathcal E_n$ 及合法粗化通道，使

$$
R^{\mathrm{bdry}}_{n+1,n}\circ\mathcal E_{n+1}
=\mathcal E_n\circ R^{\mathrm{bulk}}_{n+1,n}.
$$

局部窗口精度 $n$ 不自动等同于图的径向截断尺度。完整 Bruhat–Tits 树的边界为 $\mathbb P^1(\mathbb Q_p)$；$\mathbb Z_p$ 是自然紧开部分。本卷没有把有限边界腿直接视为完整 CFT。

从有限等式进入原始引力 RT，仍需独立给定的边界理论与态、共同调节下的熵控制、图割到满足同调约束的几何面积的极限，以及 $1/(4G_N)$ 系数的物理识别。固定纯态的全区域熵恒等式本身不建立完整体内量子纠错码或引力动力学。秩饱和、平坦谱和物理面积必须分别证明；[QMF]、[FixedArea] 提供相关比较。

## 参考文献

[RT] S. Ryu, T. Takayanagi. Holographic Derivation of Entanglement Entropy from AdS/CFT. Phys. Rev. Lett. 96 (2006), 181602. arXiv:hep-th/0603001.

[LM] A. Lewkowycz, J. Maldacena. Generalized gravitational entropy. JHEP 08 (2013), 090. arXiv:1304.4926.

[HaPPY] F. Pastawski, B. Yoshida, D. Harlow, J. Preskill. Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence. JHEP 06 (2015), 149. arXiv:1503.06237.

[Harlow] D. Harlow. The Ryu–Takayanagi Formula from Quantum Error Correction. Commun. Math. Phys. 354 (2017), 865–912. arXiv:1607.03901.

[HMPS] M. Heydeman, M. Marcolli, S. Parikh, I. Saberi. Nonarchimedean Holographic Entropy from Networks of Perfect Tensors. Adv. Theor. Math. Phys. 25 (2021), 591–721. arXiv:1812.04057.

[QMF] S. X. Cui, M. H. Freedman, O. Sattath, R. Stong, G. Minton. Quantum Max-flow/Min-cut. J. Math. Phys. 57 (2016), 062206. arXiv:1508.04644.

[FixedArea] X. Dong, D. Harlow, D. Marolf. Flat entanglement spectra in fixed-area states of quantum gravity. JHEP 10 (2019), 240. arXiv:1811.05382.

[Stabilizer] D. Fattal, T. S. Cubitt, Y. Yamamoto, S. Bravyi, I. L. Chuang. Entanglement in the stabilizer formalism. arXiv:quant-ph/0406168.
