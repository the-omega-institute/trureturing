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

## 8. 有限交换群二次历史态的完整谱

**定理 8.1。** 设 $V,X,Y$ 是有限交换群，$A:V\to X$、$B:V\to Y$ 为群同态，$(A,B)$ 单射。设 $q:V\to U(1)$ 满足 $q(0)=1$，且

$$
\beta(u,v)=\frac{q(u+v)}{q(u)q(v)}
$$

是双字符。定义归一化态、核及右根基

$$
|\psi\rangle=|V|^{-1/2}\sum_{v\in V}q(v)|Av\rangle|Bv\rangle,
\quad K_A=\ker A,\quad K_B=\ker B,
$$

$$
R_B=\{b\in K_B:\ \beta(a,b)=1\text{ 对所有 }a\in K_A\}.
$$

则约化态的所有非零本征值相等，且秩为

$$
r=\frac{|V|}{|K_A|\,|R_B|}
=\frac{|V|}{|K_A|\,|K_B|}\,
\left|\operatorname{im}\bigl(K_B\to\widehat{K_A},\ b\mapsto\beta(\cdot,b)\bigr)\right|.
$$

因此 $S(\rho_X)=\log r$，所有正阶 Rényi 熵也等于 $\log r$。这里不假设核是自由模，也不假设任何短正合列分裂。

**证明。** 单射性给出 $K_A\cap K_B=0$，故 $K_A+K_B$ 中的分解唯一。将 $V$ 按 $K_A+K_B$ 的陪集分块。不同陪集在两侧局部 Hilbert 空间中分别具有互相正交的支撑：若 $A(v_0)+A(K_B)$ 与 $A(v_1)+A(K_B)$ 相交，则 $v_0-v_1\in K_A+K_B$；另一侧同理。

在代表元 $v_0$ 的块中写 $v=v_0+a+b$。利用

$$
q(v_0+a+b)=q(v_0)q(a)q(b)\beta(v_0,a)\beta(v_0,b)\beta(a,b),
$$

去掉两侧分别依赖 $a$ 或 $b$ 的局部对角相位，得到归一化系数矩阵

$$
M_{a,b}=\frac{\beta(a,b)}{\sqrt{|K_A||K_B|}}.
$$

$A$ 在 $K_B$ 上及 $B$ 在 $K_A$ 上均单射，所以这些确为原态的局部正交基。字符正交性给出

$$
(M^*M)_{b,b'}=\frac1{|K_B|}\,\mathbf 1_{b'-b\in R_B}.
$$

按 $K_B/R_B$ 分块后，每块是常数矩阵，非零本征值为 $|R_B|/|K_B|$，数量为 $|K_B|/|R_B|$。陪集块数为 $N=|V|/(|K_A||K_B|)$，每块权重 $1/N$，故全态的非零本征值为 $|K_A||R_B|/|V|$，数量为所述 $r$。证毕。

这一推导与 [Stabilizer]、[ModularClifford] 的模算术稳定子框架相容。本卷采用有限群陪集和实际系数矩阵证明，避免将合数循环模环上的核错误当作域上线性空间；不据此认领稳定子平坦谱的一般原理为新结果。

**推论 8.2（任意奇数模数的精确缝合亏损）。** 对第 4 节的态，若区域 $C$ 在每个顶点恰好选择一条边界腿，其中 $k$ 条是 $b_i$，则

$$
S(\rho_C)=L\log d-\log\gcd(d,c_k),
\qquad r_C=\frac{d^L}{\gcd(d,c_k)}.
$$

这里 $c_k$ 取任意整数代表元，最大公因子与代表元无关。

**证明。** 取 $V=R_d^{L+1}$，$A,B$ 为两侧边界输出，$q(x)=\omega_d^{x_0x_L+\alpha x_0^2}$。两核分别由初始变量参数化，均有 $d$ 个元素，且交为零。第 5 节计算的限制双字符为 $(z,t)\mapsto\omega_d^{c_kzt}$，其右根基大小为 $\gcd(d,c_k)$。定理 8.1 给出完整谱及熵。证毕。

**推论 8.3（精度方向的精确斜率）。** 固定奇素数 $p$、$L$、整数 $\alpha$ 和 $k$，将

$$
c_k=2\alpha+(-1)^L(2^{-k}+2^{-(L-k)})
$$

视为 $\mathbb Z_p$ 元素，令 $\nu=v_p(c_k)$，约定 $v_p(0)=\infty$。在 $d=p^n$ 的循环窗口中，

$$
S_n(C)=\bigl[Ln-\min(n,\nu)\bigr]\log p.
$$

若 $c_k\ne0$，则 $n\ge\nu$ 后绝对熵亏损稳定为 $\nu\log p$，且 $S_n(C)/(n\log p)\to L$。若 $c_k=0$，则 $S_n(C)=(L-1)n\log p$。证明为推论 8.2 与素数幂环的核计数。此极限仅是熵数值的精度渐近；没有给出跨不同 Hilbert 空间的态收敛或量子通道相容性。

## 9. 所有奇数连接维数的统一构造

**引理 9.1（二次非剩余缝合证书）。** 设 $p$ 为奇素数，$L\ge3$，$a=2^{-L}\in\mathbb F_p^\times$，$\chi_p$ 为取值 $0,1,-1$ 的二次特征。若

$$
\chi_p(\alpha^2-a)=-1,
$$

则 $c_k\ne0\pmod p$ 对所有 $0\le k\le L$ 同时成立。

**证明。** 若某个 $c_k=0$，置 $x=2^{-k}\ne0$，则

$$
x+a/x=-2(-1)^L\alpha=:t.
$$

$x$ 是 $X^2-tX+a$ 的根，而该二次多项式的判别式为

$$
t^2-4a=4(\alpha^2-a),
$$

按假设为非平方，矛盾。证毕。此证书是充分条件；$k$ 只遍历有限指定集合，因此不声称非剩余条件也是必要条件。

**引理 9.2（证书总存在）。** 对任意 $a\in\mathbb F_p^\times$，满足 $\chi_p(\alpha^2-a)=-1$ 的 $\alpha$ 恰有

$$
N_-=\frac{p-\chi_p(a)}2>0
$$

个。

**证明。** 方程 $y^2=x^2-a$ 等价于 $(x-y)(x+y)=a$。因为 $2$ 可逆，任取非零的 $x-y$ 都唯一决定 $x+y$，故共有 $p-1$ 对解。另一方面解数为 $\sum_x[1+\chi_p(x^2-a)]$，所以特征和为 $-1$。零点数为 $1+\chi_p(a)$；结合 $N_++N_-+N_0=p$ 与 $N_+-N_-=-1$，得到所述计数。证毕。

**定理 9.3（全奇数模数、全区域单环 RT）。** 对任意奇数 $d\ge3$、任意 $L\ge3$，存在一个与边界区域无关的 $\alpha\in R_d$，使第 4 节网络对所有边界子集 $C$ 同时满足

$$
S(\rho_C)=m(C)\log d.
$$

同一个构造适用于推论 6.2 的任意有限附树单环。对每个固定奇素数 $p$ 与环长 $L$，还可选择一个整数 $\alpha$，使上述结论对全部 $d=p^n$、$n\ge1$ 同时成立。

**证明。** 对每个 $p\mid d$，由引理 9.2 选择 $\alpha_p$ 使 $\alpha_p^2-2^{-L}$ 为非剩余。由中国剩余定理取 $\alpha\equiv\alpha_p\pmod p$。引理 9.1 保证所有 $c_k$ 不被 $d$ 的任何素因子整除，因此均为 $R_d$ 的单位。应用定理 5.1 和同一森林吸收论证。固定 $p,L$ 时，任取 $\alpha_p$ 的整数提升，其在每个 $p^n$ 中都满足单位判据。证毕。

这一定理保持四腿局部张量 $T_d$、单边缝合形式和全部边界区域的同一态。它扩大了连接维数范围，没有扩大为任意多环图，也没有把精度族自动提升为相容量子系统。

## 10. 保留算术余数的局部粗化：尖锐熵障碍

**定义 10.1。** 固定奇素数 $p$、$n\ge1$，令 $d=p^n$、$D=pd$。研究单条缝合连接的最大纠缠纯态

$$
|\Omega_{D,\alpha}\rangle=\frac1D\sum_{x,y\in R_D}
\exp\!\left(\frac{2\pi i(xy+\alpha x^2)}D\right)|x,y\rangle,
$$

其中 $\alpha$ 为整数。设局部通道 $\Phi_A,\Phi_B:M_D(\mathbb C)\to M_d(\mathbb C)$ 完全正且保迹，并逐个计算基态保留算术余数：

$$
\Phi_A(|x\rangle\langle x|)=|x\bmod d\rangle\langle x\bmod d|,
\qquad
\Phi_B(|x\rangle\langle x|)=|x\bmod d\rangle\langle x\bmod d|.
$$

输出为 $\rho=(\Phi_A\otimes\Phi_B)(|\Omega_{D,\alpha}\rangle\langle\Omega_{D,\alpha}|)$。通道采用局部乘积，不包含通信或额外共享纠缠辅助资源。

**定理 10.2（最佳纯态逼近与最小输出熵）。** 在上述假设下，

$$
\lambda_{\max}(\rho)\le p^{-1},\qquad
S(\rho)\ge\log p,\qquad
\langle\varphi|\rho|\varphi\rangle\le p^{-1}
$$

对每个归一化纯态 $|\varphi\rangle$ 成立。对每个 $p,n,\alpha$，存在满足假设的局部通道，使 $\rho$ 恰为秩 $p$ 的平坦谱态，因而最大本征值和熵的界同时达到。

**证明。** 写 $x=a+db$、$y=c+de$，其中 $0\le a,c<d$、$0\le b,e<p$。有限维 Stinespring 表示与每个计算基输出的纯性给出

$$
V_A|a+db\rangle=|a\rangle|e_{a,b}\rangle,
\qquad V_B|c+de\rangle=|c\rangle|f_{c,e}\rangle.
$$

对固定 $a$，$\{e_{a,b}\}_b$ 正交归一；对固定 $c$，$\{f_{c,e}\}_e$ 正交归一。不要求不同 $a$ 的环境标架相互正交。由于 $p\mid d$，相位满足

$$
\frac{xy+\alpha x^2}{D}
=\frac{ac+\alpha a^2}{D}
+\frac{(c+2\alpha a)b+ae}{p}\pmod{\mathbb Z}.
$$

定义环境 Fourier 标架

$$
|\nu_{a,t}\rangle=p^{-1/2}\sum_b\omega_p^{tb}|e_{a,b}\rangle,
\qquad
|\mu_{c,s}\rangle=p^{-1/2}\sum_e\omega_p^{se}|f_{c,e}\rangle.
$$

固定 $a$ 或 $c$ 时，这些仍正交归一。通道的全输出纯化向量为

$$
\frac1d\sum_{a,c}
\exp\!\left(\frac{2\pi i(ac+\alpha a^2)}D\right)
|a,c\rangle|\nu_{a,c+2\alpha a}\rangle|\mu_{c,a}\rangle,
$$

环境指标按模 $p$ 读取。故环境约化态为

$$
\tau=d^{-2}\sum_{a,c}
|\nu_{a,c+2\alpha a}\rangle\langle\nu_{a,c+2\alpha a}|
\otimes|\mu_{c,a}\rangle\langle\mu_{c,a}|.
$$

固定 $a$，按 $t=c+2\alpha a\pmod p$ 分组，每组有 $d/p$ 个 $c$，从而

$$
\tau_a=\frac1p\sum_{t\in R_p}
|\nu_{a,t}\rangle\langle\nu_{a,t}|\otimes\sigma_{a,t},
\qquad \tau=\frac1d\sum_a\tau_a,
$$

其中每个 $\sigma_{a,t}$ 都是密度矩阵。正交性与 $\sigma_{a,t}\le I$ 给出 $\tau_a\le I/p$，故 $\tau\le I/p$。$\rho$ 与 $\tau$ 作为同一纯态的互补边缘，非零谱相同，遂得最大本征值界；熵界来自 $-\log\lambda_j\ge\log p$，纯态重叠界由 Rayleigh 商得到。

为证明尖锐性，选取 $p$ 维环境并指定

$$
\nu_{a,t}=|t-(2\alpha+1)a\bmod p\rangle,
\qquad \mu_{c,s}=|c-s\bmod p\rangle.
$$

每组为正交基，逆 Fourier 变换给出合法的 $e,f$ 标架，从而给出合法等距 $V_A,V_B$。此时条件环境向量为 $|c-a\rangle\otimes|c-a\rangle$。$c-a\pmod p$ 均匀分布，因此 $\tau$ 具有 $p$ 个相等的非零本征值 $1/p$，$\rho$ 亦然。证毕。

**推论 10.3（普通丢弃高位的额外损失）。** 取自然数字分解 $W|a+db\rangle=|a\rangle|b\rangle$ 并在两侧分别丢弃高位。此时输出恰有 $p^2$ 个非零本征值 $p^{-2}$，所以

$$
S(\rho)=2\log p,\qquad \operatorname{Tr}(\rho^2)=p^{-2}.
$$

**证明。** 此时 $e_{a,b}=|b\rangle$、$f_{c,e}=|e\rangle$。环境 Fourier 向量仅依赖 $(c+2\alpha a,a)\pmod p$，该线性变换可逆；这 $p^2$ 个正交向量等权出现。证毕。特别地，$D=9,d=3$ 时输出为整个 $3\times3$ 系统的最大混合态 $I_9/9$。

定理 10.2 排除的是同时保持两侧普通算术余数的局部纯态粗化，不排除其他读出方式，也不排除有额外资源的联合操作。它给出第 7 节跨尺度义务的一条必要警告：对象层面的余数相容，不能单独保证相干连接在量子层面的纯态相容。

## 11. 互补读出的非恒定相容通道塔

**定义 11.1。** 对 $d\mid D$，令自然数字粗化通道

$$
Q_{D,d}(|a+db\rangle\langle a'+db'|)
=\delta_{b,b'}|a\rangle\langle a'|,
$$

其中 $0\le a,a'<d$、$0\le b,b'<D/d$。令 $F_d$ 为正指数归一化 Fourier 矩阵，$D_{d,\alpha}=\operatorname{diag}(\omega_d^{\alpha x^2})$，并记 $\operatorname{Ad}_U(\rho)=U\rho U^*$。定义

$$
\mathcal C^Z_{D,d}
=\operatorname{Ad}_{D_{d,\alpha}}\circ Q_{D,d}\circ\operatorname{Ad}_{D_{D,\alpha}^*},
$$

$$
\mathcal C^F_{D,d}
=\operatorname{Ad}_{F_d}\circ Q_{D,d}\circ\operatorname{Ad}_{F_D^*}.
$$

**定理 11.2（严格相容与缝合纯态保留）。** 上述通道完全正、保迹、非恒定，且对 $e\mid d\mid D$，在全部输入矩阵上满足

$$
\mathcal C^Z_{d,e}\circ\mathcal C^Z_{D,d}=\mathcal C^Z_{D,e},
\qquad
\mathcal C^F_{d,e}\circ\mathcal C^F_{D,d}=\mathcal C^F_{D,e}.
$$

此外

$$
(\mathcal C^Z_{D,d}\otimes\mathcal C^F_{D,d})
(|\Omega_{D,\alpha}\rangle\langle\Omega_{D,\alpha}|)
=|\Omega_{d,\alpha}\rangle\langle\Omega_{d,\alpha}|.
$$

**证明。** $Q$ 是数字分解等距之后的偏迹，因此完全正且保迹。把 $x$ 写为

$$
x=a+eb+dc,\qquad 0\le a<e,\quad0\le b<d/e,\quad0\le c<D/d,
$$

可在矩阵单位上直接得到 $Q_{d,e}Q_{D,d}=Q_{D,e}$：连续丢弃 $c,b$ 等价于一次丢弃 $b+(d/e)c$。中间幺正变换互相抵消，给出两族 $\mathcal C$ 的严格复合律。

令 $|\Phi_D\rangle=D^{-1/2}\sum_x|x,x\rangle$。有

$$
|\Omega_{D,\alpha}\rangle=(D_{D,\alpha}\otimes F_D)|\Phi_D\rangle.
$$

两侧数字分解把 $\Phi_D$ 精确化为 $\Phi_d\otimes\Phi_{D/d}$，丢弃后者留下纯态 $\Phi_d$，再施加低维幺正即得结论。最后，$Q$ 把每个低维密度矩阵 $\sigma$ 的输入 $W^*(\sigma\otimes|0\rangle\langle0|)W$ 送到 $\sigma$，故满射且非恒定；幺正共轭保持此性质。证毕。

$\mathcal C^Z$ 保留计算基的普通余数。$\mathcal C^F$ 保留 Fourier 读出中的数字，不同时满足定理 10.2 的计算基余数条件。例如

$$
\mathcal C^F_{9,3}(|3\rangle\langle3|)=|1\rangle\langle1|,
$$

而 $3\bmod3=0$。因此定理 11.2 与尖锐障碍一致。

**适用边界。** 定理 11.2 已在单条缝合连接上构造非恒定、对全部输入可复合的通道塔，并对指定连接态证明精确相容。它没有声称完整网络的每个顶点也与这些腿通道相容。将其接入第 9 节的全区域 RT 精度族，还需证明共享腿采用同一读出约定时的顶点交织关系，并处理环上这些约定的全局一致性。完整体态编码的第 7 节交换图仍为未证义务。

## 增补文献

[ModularClifford] E. Hostens, J. Dehaene, B. De Moor. Stabilizer states and Clifford operations for systems of arbitrary dimensions, and modular arithmetic. Phys. Rev. A 71 (2005), 042315. arXiv:quant-ph/0408190v2.

第 8 节的有限交换群谱公式、第 9 节的特征计数和 CRT 选择、第 11 节的通道共轭各有成熟的数学基础。本卷的具体网络证书、尖锐粗化界及其组合尚未完成等价构造的全面优先权排查；数学证明与文献新颖性分别承担，不使用“首次”或原始 RT 已解决的声明。
