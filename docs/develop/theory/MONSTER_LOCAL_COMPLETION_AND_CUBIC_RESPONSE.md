# 魔群为何出现：局部完成、三阶响应与祖先标记

> 2026-09-28，`generic-v1` 理论研究稿。本卷承接 PR #10310，研究用户新明确的目标：给出 Monster 出现的数学物理解释。原 QCA 卷继续承担其分类问题，本卷不复制其证明。本文区分已发表构造、本文推论和未完成的选择问题；无 Lean 核验、独立同行审定、实验实现或全球原创性声明。

研究基点为 PR 头 `4e4cdebe0cea76deea94dc5be8a421c408e0557d`；本轮另读取 dev `8a1eb042cb44cc73c6d5ef1b9627d40de774ebe9`。主接口是实际局部场的乘法及相关函数。文中 Monster 指有限单群 $\mathbb M$；与仅有二元运算的 magma 完全分开。

## 1. 两个排除结果确定魔群应出现在哪一层

### 1.1 扇区范畴和全体局部场的不同信息

采用已经构造的月光 VOA $V^\natural$ 及其局部共形网 $\mathcal A^\natural$。已发表输入 [KL05, Theorem 3.6、Example 3.8、Theorem 5.4] 给出：网是 holomorphic，只有真空不可约 DHR 扇区，且

$$
\operatorname{DHR}(\mathcal A^\natural)\simeq\mathrm{Vec},
\qquad
\operatorname{Aut}(\mathcal A^\natural)\cong\operatorname{Aut}(V^\natural)\cong\mathbb M.
\tag{MC.1}
$$

因此，只保留 DHR 简单扇区、融合或其编织自等价作用，会把这个实际魔群作用送到平凡群。这里没有把共形网当作原 QCA 定义中的有限迹融合自旋链；两者的对象衔接仍需新的定理。式（MC.1）只直接证明该类粗观察会遗漏局部场对称。

仓内 [MonsterPrimitiveMobiusRecovery](https://github.com/the-omega-institute/trureturing/blob/930316bfabefbed08c26ee7611e173380ca82c43/D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery.lean) 的实际声明输入任意整数系数 $c$ 与一个已给对数展开，结论为 Möbius 恢复。它可以复用来恢复字符系数；它没有构造 $V^\natural$、局部乘法或魔群作用。本轮读取该源，没有重新编译。

### 1.2 已算得的平移群本身不能解释小层数中的魔群

**命题 1.1（有限群在平移半直积中的容量限制）。** 若有限群 $G$ 单射到 $\mathbb Z^m\rtimes S_m$，则它单射到 $S_m$。特别地，使用魔群非平凡复不可约表示的最小维数 $196883$，当 $m<196884$ 时，该半直积不含魔群子群。

证明。投影到 $S_m$ 的核包含于无挠群 $\mathbb Z^m$，也是有限群，故核平凡。若 $\mathbb M\hookrightarrow S_m$，则它在 $\mathbb C^m$ 的置换表示中固定全一向量，且在其 $m-1$ 维正交补上仍忠实。该补空间必含非平凡不可约分量，故 $m-1\ge196883$。证毕。

最小表示维数是 [KL05, Lemma 5.1 proof] 采用的既有魔群事实。应用到原卷的 $\Gamma_m/\mathrm{FDQC}\cong\mathbb Z^m\rtimes S_m$ 时，保留该原证明稿的验证边界。纯群论命题独立于原 QCA 推导。特别是，仅用 24 或 48 个层的平移与排列，不能产生所求魔群。一般 QCA 群和局部场自同构群未被这个命题排除。

## 2. 已有非循环构造提供的出现机制

### 2.1 固定具体的构造范围

令 $\Lambda$ 为正定、偶、自对偶、无长度平方二向量的秩 24 格。这个条件唯一选出 Leech 格，是外部格分类输入。格 VOA 的状态由振子和动量格态组成，$c=24$。反射 $\lambda\mapsto-\lambda$ 提升为阶二自同构 $\theta$。

只取固定点 $V_\Lambda^+$ 会遗漏扭曲局部化数据。标准 bosonic 反射 orbifold 使用扭曲模的整数权部分 $V_\Lambda^{T,\mathrm{int}}$，组成

$$
V^\natural=V_\Lambda^+\oplus V_\Lambda^{T,\mathrm{int}}.
\tag{MC.2}
$$

扭曲模的存在、互相作用、VOA 的 Jacobi/局部性和这个和上的唯一扩展结构，是 FLM 构造的实质输入 [ALY, §1；GL11]。式（MC.2）作为向量空间直和不能独自承担这些结论。环面变换会交换时间方向插入与空间方向扭曲，说明完成化有物理意义；整个 Monster 的同时 gauging 则另受第 8 节的反常限制。

**命题 2.1（权重一消失与首层完成计数）。** 在上述标准构造中，$V_1^\natural=0$，而权重二的两个加数维数为

$$
\dim(V_\Lambda^+)_2=300+98280=98580,
\qquad
\dim(V_\Lambda^{T,\mathrm{int}})_2=24\cdot2^{12}=98304.
\tag{MC.3}
$$

所以 $\dim V_2^\natural=196884$。

证明。权重一的振子 $h(-1)\mathbf1$ 在反射下为奇，因而被固定点投影去掉。格无根，故没有权重一动量态。标准反射扭曲振子有半整数频率，扭曲最低权为 $24/16=3/2$；其整数权部分没有权重一。

在权重二，固定点振子来自 $\operatorname{Sym}^2(\mathbb C^{24})$，维数 $24\cdot25/2=300$。$h(-2)\mathbf1$ 仍为奇。Leech 格的 theta 级数是 $E_4^3-720\Delta$：权重 12 模形式空间由 $E_4^3,\Delta$ 张成，常数项一与无根的 $q$ 系数零决定这两个系数。其 $q^2$ 系数为 196560，反射将这些长度平方四向量配成 98280 对。扭曲基态维数 $2^{12}$，加一个频率 $1/2$ 的 24 种振子即到权重二，给 98304。证毕。

以上计数属于既有构造的直接展开，未以数字巧合识别群。它说明恢复局部/模相容性所加入的扭曲部分，恰好与未扭曲部分在相同能级相遇；之后是否能混合，取决于真实乘法。

### 2.2 为什么自同构群会超出保留某次构造的子群

[GL11] 从 $(V_{\sqrt2E_8}^+)^{\otimes3}$ 的简单流扩展出发，先构造 VOA，再得到两个不同的自同构子群，证明它们生成有限的 Monster 型群，并引用群论唯一性识别为 Monster。它没有在开始就输入一个 196883 维 Monster 表示。

这一已知构造说明，局部兼容条件可以真正产生所求群。它还保留了一个重要边界：正定性、低权约束和模不变性单独没有在本文中被证明足以选择整套乘法。第 3 节明确说明它们目前能选择到哪里，第 4 节再给出完整乘法的识别接口。

## 3. 中心荷 24 的两种有边界的选择证书

### 3.1 较小中心荷的电流障碍

本段采用 CFT 型、酉、holomorphic、强有理的 bosonic VOA，并显式调用 [Z96] 的字符模变换定理。字符 $\chi_V$ 非零，在 $\tau=i$ 为正，张成 $\mathrm{SL}_2(\mathbb Z)$ 的一维表示。$S$ 固定 $i$，故 $\rho(S)=1$；$T$ 的特征值为 $e^{-2\pi ic/24}$，群关系 $(ST)^3=S^2$ 给 $e^{-2\pi ic/8}=1$。于是正中心荷属于 $8\mathbb Z$。对 $c=8,16$，$\eta^c\chi_V$ 分别属于一维模形式空间 $M_4,M_8$，真空首项将其固定为 $E_4,E_4^2$。故

$$
\chi_V=\frac{E_4}{\eta^8}=q^{-1/3}(1+248q+\cdots),\qquad
\chi_V=\frac{E_4^2}{\eta^{16}}=q^{-2/3}(1+496q+\cdots).
\tag{MC.4}
$$

因而在这些标准假设下，第一个可能没有权重一电流的正中心荷是 24。在 $c=24,V_1=0$ 时，标量模函数的唯一一阶极点及常数项固定字符为 $J=j-744$。这个推导只确定谱计数，不确定 OPE。

尤其不把 $c=24$ 称作物理时空维数 24。它在此是手征共形中心荷；格构造恰用 24 个手征振子实现它。

### 3.2 独立的低权各向同性条件

称 VOA 在权重至八没有额外对称不变量，是指其实际全自同构群在 $V_{\le8}$ 的不动向量恰为真空 Virasoro 后裔。这是 Matsuo 的 class $S^8$，不在定义中指定群为 Monster，但它是强假设，需要单独验证。

[M01, §3.1] 在 $V_1=0$、非退化不变形式、适用的 Virasoro Gram 非退化条件和一个非平凡共形幂等元下，推出下述两个等式。记 $d=\dim V_2$：

$$
B(c)d=A(c),\qquad D(c)d=C(c),
\tag{MC.5}
$$

其中

$$
\begin{aligned}
A(c)&=70c^3+955c^2+2388c,\\
B(c)&=2c^2-110c+1496,\\
C(c)&=5250c^5+155250c^4+1369715c^3+3507098c^2+1497768c,\\
D(c)&=125c^4-4770c^3-23382c^2+1561868c+1032240.
\end{aligned}
$$

**命题 3.1（显示迹恒等式的正性选择）。** 若 $c>0,d\ge2$ 满足式（MC.5），则 $c=24,d=196884$。

证明。无需除以可能为零的分母，交叉消去得

$$
AD-BC=-c(c-24)(2c-1)(5c-142)(5c+22)(5c+44)(7c+68)=0.
\tag{MC.6}
$$

因此正候选只有 $1/2,24,142/5$。代入 $Bd=A$ 时 $B$ 在三点均非零，得到 $d=1,196884,-164081$。前件排除首尾，只剩所述值。证毕。

这个选择结论是 Matsuo 已发表理论的重用；本文推导重点是后续三阶响应与标记恢复接口。实际读取的 arXiv v1 中，Theorem 3.2 证明的负候选列表与其显示公式的直接消元不同；式（MC.6）已经精确展开检错。本文只使用正分支证明，未将那个负根列表当作依据，未声称核对了期刊版该排印位置。

### 3.3 不能跳过的选择缺口

$c=24,V_1=0$ 和字符 $J$ 不能在本文中替代全部局部乘法。[DGL05, Theorem 1] 的已核唯一性定理另有关键前件：$V_2$ 的乘法同构于 Griess 代数。本文保留这一前件，不宣称去掉它，也不根据旧文献擅自报告 2026 年一般唯一性问题的最终状态。

## 4. 从局部三点函数恢复完整首层乘法

### 4.1 可形式化的有限数据

固定月光 VOA 的正定实形式。令 $B=(V_2^\natural)_{\mathbb R}$，并定义

$$
a\cdot b=a_{(1)}b,\qquad
\langle a,b\rangle\mathbf1=a_{(3)}b,
\qquad e=\omega/2.
\tag{MC.7}
$$

这里 $\mathbf1\in V_0$ 是真空，$e\in B$ 才是这个有限代数的单位。VOA 的实际运算给出交换乘法、不变正定形式、$e\cdot a=a$、$\|e\|^2=3$。乘法一般不结合。令

$$
W=e^\perp,\quad d_W=196883,\quad
T(u,v,w)=\langle u\cdot v,w\rangle\quad(u,v,w\in W).
\tag{MC.8}
$$

$T$ 是对称三线性形式。因 $V_1=0$，$W$ 中向量是权重二的 Virasoro primary：$L_1u=0$，$L_2u=\langle u,\omega\rangle\mathbf1=0$，更高正模因权重为负而为零。

其二、三点真空相关函数为

$$
\langle\phi_u(z_1)\phi_v(z_2)\rangle
=\frac{\langle u,v\rangle}{z_{12}^4},\qquad
\langle\phi_u(z_1)\phi_v(z_2)\phi_w(z_3)\rangle
=\frac{T(u,v,w)}{z_{12}^2z_{23}^2z_{13}^2}.
\tag{MC.9}
$$

度量和三线性形式是剥去固定坐标因子后的局部相关数据；需要保留相位/符号及共同场标定。

**定理 4.1（三阶关系的完整恢复）。** 对任意有单位、正定不变形式的有限实交换代数，若 $\|e\|^2=3$，则度量、$e$ 和 $T|_{W^3}$ 唯一恢复整个乘法：

$$
(ae+u)\cdot(be+v)
=\left(ab+\frac{\langle u,v\rangle}{3}\right)e
+av+bu+T^\sharp(u,v),
\tag{MC.10}
$$

其中 $\langle T^\sharp(u,v),w\rangle=T(u,v,w)$。因此 $\operatorname{Stab}_{O(W)}T$ 与保持度量的全代数自同构群自然同构。

证明。不变性给 $\langle u\cdot v,e\rangle=\langle u,v\rangle$，所以 $e$ 方向系数为右式；正定形式的非退化性唯一确定剩下的 $W$ 分量。单位律和双线性给全部乘法。任意保持 $T$ 的 $U\in O(W)$ 延拓为 $e\mapsto e$，由式（MC.10）保持乘法。反向，代数自同构固定唯一单位，保度量时保持 $W$，并保持 $T$。证毕。

将已构造的实际 Griess 代数代入，使用其全自同构群识别 [G81、M01、GL11]，得到

$$
\boxed{\operatorname{Stab}_{O(196883)}T^\natural\cong\mathbb M.}
\tag{MC.11}
$$

这是给定模型的精确识别证书，未凭空选定 $196883^3$ 个系数再称为解释。系数须从式（MC.2）的真实局部完成构造取得。纯代数恢复证明对其他有限代数同样成立；只有这里的具体 $T^\natural$ 具有 Monster 稳定子。

### 4.2 二阶与无相位谱系的明确失败证人

**推论 4.2（二阶退化及奇次信息必要性）。** 月光 primary 场的全部二点数据在 $O(W)$ 下不变。映射 $u\mapsto-u$ 还在共轭下逐点固定定义在 $W$ 上的任意正交投影，因而任何仅由这些投影及其乘积迹组成的无相位谱系读数都看不见该映射；但它将 $T^\natural$ 变成 $-T^\natural\ne T^\natural$。

证明。二点数据由度量给出。$(-I)P(-I)=P$ 对每个投影成立，任意积与迹也保持。三线性使三点张量变号。若 $T^\natural=0$，式（MC.10）会让整个 $O(W)$ 成为 Griess 代数对称，与式（MC.11）的有限性矛盾，所以其非零。证毕。

这直接限制“树形谱系”解释：只保存投影、重叠概率或成对关系，至少遗漏一个实际可被三点函数区分的符号。它没有声称任何任意标记的二维或三维几何图都必须失败；结论针对上述明确观察类。

## 5. 三阶脉冲响应：一个有限时间、有限精度的证书

### 5.1 响应算符与外部输入

对 $u\in W$，取实际零模在 $B_{\mathbb C}$ 上的限制

$$
R_u(a)=u\cdot a.
$$

它是有限维自伴算符。[M01, Corollary 4.1] 的 Norton 迹公式给

$$
\operatorname{Tr}_B(R_uR_v)=4620\langle u,v\rangle,
\qquad
\operatorname{Tr}_B(R_uR_vR_w)=900T^\natural(u,v,w).
\tag{MC.12}
$$

原文一般公式含 $\omega$ 分量；这里只因 $u,v,w\perp\omega$ 才化为式（MC.12）。数字 4620、900 是明确的文献输入，本批未从完整 VOA 再证明 Norton 公式。

**推论 5.1（低阶响应的识别阈值）。** 固定上述实际响应族。实线性可逆重标记 $U:W\to W$ 保持所有二阶及三阶响应，当且仅当 $U$ 来自 Monster。仅保持二阶响应的群为 $O(W)$。

证明。二阶等式与 $4620>0$ 强制保度量。三阶等式与 $900\ne0$ 强制保 $T^\natural$，由定理 4.1 及式（MC.11）得结论，反向直接成立。证毕。

### 5.2 实际有限脉冲，不以零时导数作为实验输入

以下实验权限单独声明：可制备 $B_{\mathbb C}$ 上的最大混合态，使用相同场标定的脉冲 $e^{itR_u}$，并通过一个参考量子比特的受控脉冲干涉取得归一化复迹。它是精确的有限维实验模型，VOA 或共形网的存在本身不保证这些控制已由装置实现。

固定单位向量 $u,v,w\in W$、$t>0$，对 $S\subseteq\{1,2,3\}$，按 $u,v,w$ 的固定次序定义 $U_S$ 为选中脉冲的乘积。记 $N=196884$ 和 $z_S=N^{-1}\operatorname{Tr}U_S$。定义

$$
\widehat T_t(u,v,w)
=\frac{N}{900}\operatorname{Re}\left[
\frac{1}{(it)^3}
\sum_{S\subseteq\{1,2,3\}}(-1)^{3-|S|}\widehat z_S\right].
\tag{MC.13}
$$

不同项对应独立重复制备的设置；相减在经典数据处理中进行，未假定负时间脉冲合法。空词迹已知为一，保守误差界仍按八项计算。

**定理 5.2（显式有限脉冲与测量误差界）。** 若每个归一化复迹满足 $|\widehat z_S-z_S|\le\epsilon$，则

$$
\boxed{
|\widehat T_t-T^\natural(u,v,w)|
\le29645\sqrt{4620}\,t^2+\frac{43752}{25}\frac{\epsilon}{t^3}.
}
\tag{MC.14}
$$

因此，误差上界自身的最优正步长为

$$
t_*^5=\frac{65628}{741125\sqrt{4620}}\epsilon\quad(\epsilon>0),
\tag{MC.15}
$$

所给上界具有 $\epsilon^{2/5}$ 的阶。这里用到了实际实形式的奇偶结构；不增加脉冲设置数。未宣称这个实验估计器在全部可能协议中 minimax 最优。

证明。置 $D_u(t)=(e^{itR_u}-I)/(it)=\int_0^1e^{istR_u}R_u\,ds$，$L=\sqrt{4620}$。式（MC.12）给单位标签的 $\|R_u\|_{\mathrm{HS}}=L$。对 $p=0,1,2$，酉性、谱分解和积分给

$$
\|D_u^{(p)}(t)\|_{\mathrm{HS}},\ \|D_u^{(p)}(t)\|_{\mathrm{op}}
\le \frac{L^{p+1}}{p+1}.
$$

不交换乘法的分配律仍给 $\prod(e^{itR}-I)=\sum_S(-1)^{3-|S|}U_S$，次序固定。因此无噪估计为 $\operatorname{Re}F(t)/900$，其中 $F(t)=\operatorname{Tr}(D_u(t)D_v(t)D_w(t))$。

实际 $R_u,R_v,R_w$ 是实对称矩阵，故 $F(-t)=\overline{F(t)}$，特别地 $\operatorname{Re}F'(0)=0$。这里无需假定三个矩阵交换。对二阶导数的三个单因子二阶项和六个双因子一阶项，使用 $|\operatorname{Tr}ABC|\le\|A\|_{\mathrm{HS}}\|B\|_{\mathrm{op}}\|C\|_{\mathrm{HS}}$ 及循环移位，得到

$$
|F''(t)|\le3\frac{L^3}{3}L^2+6\frac{L^2}{2}\frac{L^2}{2}L
=\frac52L^5.
$$

二阶积分余项于是给 $|\operatorname{Re}F(t)-F(0)|\le5L^5t^2/4$。由 $F(0)=900T^\natural(u,v,w)$，除以 900 后偏差常数为 $L^5/720=29645\sqrt{4620}$。保留实形式消去了一阶偏差；直接对复余项取绝对值只会得到更弱的 $35574t$。上述估计没有额外乘矩阵维数。

八个归一化迹误差的和不超过 $8\epsilon$；式（MC.13）的归一化还原确实引入 $N$，给 $8N\epsilon/(900t^3)=43752\epsilon/(25t^3)$。取实部不扩大绝对误差。微分右式得式（MC.15）。证毕。

受控 $U_S$ 作用于 $|+\rangle\langle+|\otimes I/N$ 后，参考比特的 $X,Y$ 期望分别为 $\operatorname{Re}z_S,\operatorname{Im}z_S$，由二阶块密度矩阵直接取偏迹可验证。统计取得 $\epsilon$、最大混合态制备、零模控制和参考相位校准都有成本。逐个三元组的误差界不能冒充整个高维张量的低成本层析。

## 6. “固定祖先”严格缩小到哪个群？

令 $z\in\mathbb M$ 是式（MC.2）的量子对称，对未扭曲项取 $+1$，扭曲项取 $-1$。其 Monster 类型是 2B；[GL11, §3] 给出

$$
C_{\mathbb M}(z)\text{ 的群形状为 }2^{1+24}.\mathrm{Co}_1.
\tag{MC.16}
$$

点号表示扩张结构，不擅自断言分裂。令 $W=U\oplus T_-$，其中 $T_-=(V_\Lambda^{T,\mathrm{int}})_2$、$\dim T_-=98304$，$U$ 为未扭曲权重二去掉 $e$ 后的空间、$\dim U=98579$。记正交投影 $P_-$。

**定理 6.1（祖先标记的精确稳定子）。** 在实际完整场对称群中，保留这一个未扭曲/扭曲分解的群恰为 $C_{\mathbb M}(z)$。

证明。保度量变换保留 $T_-$ 当且仅当与 $P_-$ 对易，等价于与 $z|_W=I-2P_-$ 对易。Monster 在 $W$ 的表示忠实，所以表示中的对易等价于群中对易。反向显然。证毕。

本结论不把“忘记标记”当作产生新群的证明。完整自同构首先须由真实局部完成构造出来；定理说明，一旦错误要求所有对称都固定某次构造的祖先分解，便只会看到它的真子群。

**定理 6.2（祖先分解在全对称下的定量混合）。** 利用 $W$ 的绝对不可约性，有

$$
\frac1{|\mathbb M|}\sum_g gP_-g^{-1}
=\frac{98304}{196883}I_W.
\tag{MC.17}
$$

对任意单位 $u\in U$，

$$
\frac1{|\mathbb M|}\sum_g\|P_-gu\|^2
=\frac{98304}{196883}>0.
\tag{MC.18}
$$

证明。左边的平均算符与群作用对易；绝对不可约性给实 Schur 引理，所以等于标量单位。迹决定标量为秩除维数。对 $u$ 取二次型并用 $g\leftrightarrow g^{-1}$ 的求和双射得到式（MC.18）。证毕。

因此全群必有元素把未扭曲 primary 方向送入带非零扭曲分量的方向。这个平均是数学恒等式，不声称能均匀抽样巨大群或将所有元素实现为固定深度量子门。扭曲/未扭曲标签相对于所选子理论有意义；在完整 holomorphic 理论中它们不成为两个不可约 DHR 扇区。

## 7. 近似三阶关系是否仍能识别离散群？

### 7.1 可复用的稳定性定理

固定有限维实欧氏空间 $W$、非零对称三线性张量 $T$，其正交稳定子 $K$ 为有限群。取张量 Hilbert–Schmidt 范数，定义 $\rho(U)T=T(U^{-1}\cdot,U^{-1}\cdot,U^{-1}\cdot)$。对斜对称 $A$，令 $\mathcal L_T(A)=\left.\frac{d}{dt}\right|_{0}\rho(e^{tA})T$，并设

$$
\kappa_T=\min_{A^T=-A,\ \|A\|_F=1}\|\mathcal L_T(A)\|_F.
\tag{MC.19}
$$

维数至少二时该球非空；以下以此为前件。一维正交群的情况是有限枚举，不使用这个定义。

**定理 7.1（局部线性稳定性与有噪输入）。** $\kappa_T>0$。存在 $\eta_T>0$，若 $\|\rho(U)T-T\|_F<\eta_T$，则

$$
\operatorname{dist}_F(U,K)\le\frac{2}{\kappa_T}\|\rho(U)T-T\|_F.
\tag{MC.20}
$$

若 $\|\widetilde T-T\|_F\le\epsilon$，候选满足 $\|\rho(U)\widetilde T-\widetilde T\|_F\le\delta$ 且 $\delta+2\epsilon<\eta_T$，则右式可换成 $2(\delta+2\epsilon)/\kappa_T$。

证明。若 $\mathcal L_T(A)=0$，三槽张量表示的生成元杀掉 $T$，于是其指数对任意时间都固定 $T$；$e^{tA}$ 全落在有限群 $K$。连续性使它恒为单位，故 $A=0$。有限维单位球紧，连续正范数的最小值严格正。

记 $a=\|A\|_F$。三槽表示生成元的算子范数至多 $3a$，且表示正交。因此二阶积分余项给

$$
\|\rho(e^A)T-T-\mathcal L_T(A)\|_F\le\frac92\|T\|_F a^2.
$$

当 $a\le\kappa_T/(9\|T\|_F)$，得到残差至少 $\kappa_T a/2$。取一个更小的正指数坐标半径 $r<\min\{1,\kappa_T/(9\|T\|_F)\}$。删去所有 $g\exp\{A:\|A\|_F<r\}$ 后，$O(W)$ 中剩下的紧集不含稳定子，若此补集非空，残差在其上有正最小值，取更小的 $\eta_T$；若补集为空，任取正 $\eta_T$。残差小于该阈值的 $U$ 位于某个邻域，由 $\|e^A-I\|_F\le\|A\|_F$ 得式（MC.20）。最后正交性和三角不等式给真实残差不超过 $\delta+2\epsilon$。证毕。

这将精确三点稳定子识别转成一个抗小扰动的数学接口。一般紧群轨道的稳定性方法是成熟工具；本卷明确应用于实际月光立方张量，未认领一般方法原创性。

### 7.2 月光张量的一个实际尺度，及尚未计算的尺度

**命题 7.2（实际立方张量范数）。** 在式（MC.7）的标准规范下，

$$
\|T^\natural\|_F^2=\frac{2728404614}{3}.
\tag{MC.21}
$$

证明。用单位向量 $e/\sqrt3$ 和 $W$ 正交基分解 $R_u$，其块矩阵为

$$
R_u=\begin{pmatrix}0&u^T/\sqrt3\\u/\sqrt3&T_u\end{pmatrix},
\qquad\langle T_uv,w\rangle=T^\natural(u,v,w).
$$

式（MC.12）给 $\operatorname{Tr}T_uT_v=(4620-2/3)\langle u,v\rangle$。对 $W$ 的 196883 个单位基向量求和得式（MC.21）。证毕。

本文没有计算实际 $\kappa_{T^\natural}$ 或 $\eta_{T^\natural}$；它们的存在不能被报道成数值认证。若只掌握每个张量系数误差至多 $a$，保守 Frobenius 界为 $d_W^{3/2}a$，维数成本不能删除。定理 5.2 是单个三元组的实际脉冲预算，与本节全张量预算分开结算。

## 8. 数学物理解释还必须通过反常检查

### 8.1 群作用严格结合，缺陷结点仍可带三余循环

一个严格作用于 VOA 的有限群 $G$，可以具有标记为 $g\in G$ 的对称缺陷 $D_g$。选定一维融合结点 $D_gD_h\to D_{gh}$ 后，两种三重融合次序相差 $\omega(g,h,k)\in U(1)$。四重重组的一致性给

$$
\omega(h,k,l)\omega(g,hk,l)\omega(g,h,k)
=\omega(gh,k,l)\omega(g,h,kl).
\tag{MC.22}
$$

结点改相位 $b(g,h)$ 将 $\omega$ 乘以三上边界，因此物理障碍是 $[\omega]\in H^3(G,U(1))$。这个层面与式（MC.1）的普通 DHR 范畴分开；$\mathrm{Vec}_G^\omega$ 的标签一开始就输入 $G$，不能借它循环推导 Monster 的存在。

[JF19, Theorem 1] 证明月光作用的反常类有精确阶 24。已读取该文 arXiv v3 和 2019 在线、2020 卷期的一页勘误；勘误只更正 handling editor，不修改该定理。后续 [L22, §3] 也明确采用精确阶 24。

**命题 8.1（局部结点不能无代价严格化）。** 若 $[\omega]\ne0$，不存在结点改相位使全部结合相位同时为一。叠放 $k$ 份相同手征月光作用时，其内部群反常类为 $k[\omega]$，恰在 $24\mid k$ 时消失。与反手征共轭理论作对角群作用时，两个内部类相消。

证明。第一项正是三余循环代表被上边界消去的定义。张量积结点的结合相位相乘，所以类相加；阶的定义给整除条件。共轭结点把单位复相位取共轭，类取负。证毕。

严格 onsite、可独立按格点 gauging 的普通一维 bosonic 内部群作用具有平凡的这一 $H^3$ 障碍。因此月光单手征作用不能被直接等同于这种 onsite 实现。可以研究非 onsite、带高维体补偿或反手征配对的实现；消去内部类只是必要一致性检查，不自动构造一个有限深度电路。

手征中心荷导致的引力反常另行计算。24 个同手征副本并不因此具有零净手征中心荷；与共轭副本配对才同时有 $c_L-c_R=0$。这两个“24”的角色需要分别证明，不能因数字相同而互相替代。

## 9. 本轮形成的解释与剩余的真正目标

当前可支持的解释链是：在明确的根格/局部完成构造中，去掉权重一电流并补齐扭曲局部性，在权重二形成两个必须共同参与乘法的来源；真实三点乘法的精确对称是 Monster；保留一个来源分解只剩 $2^{1+24}.\mathrm{Co}_1$；完整作用必混合这些来源；其物理实现还携带非平凡缺陷结合类。

本文的推导重点为三项可检验结果：有限脉冲恢复三阶关系的显式误差界，祖先标记的精确稳定子及定量混合，以及三阶关系近似保持到离散对称的稳定性接口。式（MC.1）、FLM/Griess–Lam 构造、Norton 迹公式、条件唯一性和月光反常属于明确引用的既有成果。

更强的选择问题仍明确保留：能否从不预设 Griess 乘法的局部性、正性、低权缺口和合适的极小性条件，唯一构造 $T^\natural$？式（MC.5）目前选择的是 $c,d$，并未选择全部结构常数。下一步应直接研究三点系数与高阶 crossing/VOA Jacobi 的约束，不能把条件“已有 Griess 代数”藏进待证明结论。

本卷也没有推出物理宇宙必须选择这个模型，没有证明四大力统一、引力 RT 公式、Fibonacci 链必然流到 Moonshine CFT，或构造新的单群。它给出一个真实数学物理模型中的出现原因与可反驳的进一步选择问题。

## 10. 后续形式化的具体依赖

有限部分先定义带单位的正定实 Frobenius 代数、正交补、对称三线性张量与其正交作用。按式（MC.10）证明双向重构，按式（MC.19）构造实际有限线性导数算子及范数；不得将“稳定子恰为 Monster”作为一般引理的字段。本模型的 Monster 识别须引用或最终形式化实际 Griess 构造。

脉冲部分以有限自伴矩阵、矩阵指数、Schatten 范数和八个有序子词为输入，证明望远镜误差，再实例化已核的 4620、900 迹公式。定理 5.2 的非负时长、归一化迹、标签单位范数、复误差及 $N$ 因子都不可省略。

标记部分先形式化有限正交群作用、投影与中央化子的等价、绝对不可约条件下的群平均。缺陷部分先定义群上三余循环及二维结点改相位；Monster 的实际阶 24 仍是外部定理。无限 VOA/共形网、最低权模、扭曲扩展和 DHR 全识别是独立而实质性的后续工作。

没有新 Lean 或 Scribe 绑定。简单的数值计数、条件恢复公式或本稿文本均不计为形式化真值。

## 11. 文献和实际验证范围

[G81] R. L. Griess Jr., *A construction of F1 as automorphisms of a 196,883-dimensional algebra*, PNAS 78 (1981), 689–691. https://doi.org/10.1073/pnas.78.2.689 。实际读取原作者摘要，并取得其短文 PDF；没有把它当作 1982 年完整构造的重验；立方形式实现的原有地位明确保留。完整 1982 构造 DOI 为 https://doi.org/10.1007/BF01389186 ，本轮仅取得其出版记录，不冒称全文重验。

[GL11] R. L. Griess Jr. and C. H. Lam, *A new existence proof of the Monster by VOA theory*, arXiv:1103.1414v2. https://arxiv.org/pdf/1103.1414 。读取构造路线、中央化子与有限性论证；PDF 第 2 页已视觉核对。Monster 型群的唯一性仍为该文引用的群论输入。

[KL05] Y. Kawahigashi and R. Longo, *Local conformal nets arising from framed vertex operator algebras*, arXiv:math/0407263v2. https://arxiv.org/pdf/math/0407263 。使用 Theorem 3.6、Example 3.8、Lemma 5.1、Theorem 5.4；PDF 第 15、20 页已视觉核对。本文只采用其具体 Moonshine 网，不将 2005 年对一般 VOA/net 关系的旧状态描述当作当前状态。

[M01] A. Matsuo, *Norton's Trace Formulae for the Griess Algebra of a Vertex Operator Algebra with Larger Symmetry*, Commun. Math. Phys. 224 (2001), 565–591. https://doi.org/10.1007/s00220-001-0565-3 ，本轮实际读取 https://arxiv.org/pdf/math/0007169v1 。使用 §§1、3.1、Corollary 4.1；PDF 第 7、13、16 页已视觉核对。显示多项式和负候选列表的差异按第 3.2 节记录。

[DGL05] C. Dong, R. L. Griess Jr. and C. H. Lam, *On the uniqueness of the moonshine vertex operator algebra*, arXiv:math/0506321v1. https://arxiv.org/pdf/math/0506321 。实际核对 Theorem 1 的全部前件，PDF 第 1 页已视觉核对。不能删除 Griess 乘法前件。

[ALY] T. Abe, C. H. Lam and H. Yamada, *A remark on Z_p-orbifold constructions of the Moonshine vertex operator algebra*, arXiv:1705.09022v4. https://arxiv.org/html/1705.09022v4 。使用 §1 的反射构造及其他 prime orbifold 构造范围，不认领其新颖性。

[JF19] T. Johnson-Freyd, *The Moonshine Anomaly*, Commun. Math. Phys. 365 (2019), 943–970. https://arxiv.org/html/1707.08388v3 。Theorem 1 及 §2 的物理/数学缺陷解释。勘误全文 https://link.springer.com/content/pdf/10.1007/s00220-019-03636-9.pdf 已读取且截图核对，只更正编辑署名。

[Z96] Y. Zhu, *Modular invariance of characters of vertex operator algebras*, J. Amer. Math. Soc. 9 (1996), 237–302. https://doi.org/10.1090/S0894-0347-96-00182-8 。本轮读取作者上传全文的导言及 Theorem 5.3.2 的导言说明；模变换定理作为外部输入，未重验整篇证明。

[L22] Ying-Hsuan Lin, *Topological modularity of Monstrous Moonshine*, arXiv:2207.14076v3. https://arxiv.org/html/2207.14076v3 。使用 §3 对月光反常和有限子群 gauging 限制的陈述。

实际标准库精确检查见 [`monster_completion_checks.py`](../../reports/monster-local-completion/monster_completion_checks.py) 和 [`monster_completion_results.json`](../../reports/monster-local-completion/monster_completion_results.json)。检查了 orbifold 字符有限系数、权重二计数、显示多项式消元、响应常数、明确标为 toy 的有限置换模型中的标记/中央化子/平均、立方导数和循环群结点五边形。错误的二阶充分性预测被显式拒绝。

程序没有存储或计算实际 196883 维 Monster 矩阵、完整 Griess 张量、VOA 公理、月光反常上同调或实际 $\kappa,\eta$。有限诊断不升级一般证明、物理实验或原 QCA 反例的审定状态。未运行 Lean、CI、独立同行评审，也未建立本文推论组合的全球优先权。

## 追加锚（本行以下为后续增补区）

## 12. 二阶谱选择的补入：不先给定魔群或 Griess 乘法

本批日期为 2026-09-28，接续 PR #10310 的 `beb3c5b9c87d201626bd413afebfc95b8d64ea98`，沿用本文件为魔群研究唯一主卷。此前对话附件 `MONSTER_SELECTOR_APPEND.md` 中的循环谱、逆轨形和字符选择结果在第 12–13 节补入；该附件原拟接到 QCA 卷，尚未写回。本次按实际远端归属接入这里，已有三阶响应、标记、反常和 QCA 正文均保留。以下为普通数学证明稿，无 Lean、独立审定或全球优先权声明。

### 12.1 候选理论与实际循环缺陷

**定义 12.1（本批的循环谱前提）。** $V$ 为复数域上简单、强有理、全纯、CFT 型且带相容正定酉结构的 VOA，$c=24,V_1=0$。每个使用到的非恒等二阶自同构 $g$ 有唯一不可约扭曲模 $V(g)$；其最低权 $h_g>0$，并且 $h_g\in\frac12\mathbb Z$，即循环 type $2\{0\}$。有限对称族是实际忠实同态 $E=\mathbb F_2^r\hookrightarrow\operatorname{Aut}(V)$，每个 $g\ne0$ 都满足上述条件。自同构保真空、共形向量及全部 $Y(a,z)$，并非仅保某层维数的矩阵。

使用 [EMS20, §3] 的规范化循环模变换及轨形定理。记 $q=e^{2\pi i\tau}$、$a_g=\dim V(g)_{1/2}$，以及

$$
t=\left(\frac{\eta(\tau)}{\eta(2\tau)}\right)^{24}
=q^{-1}-24+276q-2048q^2+\cdots,\quad
t(-1/\tau)=4096/t(\tau/2).
\tag{MD.1}
$$

另有 $Z_V=J=j-744=q^{-1}+196884q+\cdots$ [DM02, Lemma 2.1]。所有谱函数都在上半平面收敛；在尖点的展开由规范化模变换确定。定义 $F_g=\operatorname{Tr}_V(gq^{L_0-1})$，$Z_g=\operatorname{Tr}_{V(g)}q^{L_0-1}$。

**定理 12.2（两个尖点的谱二分）。**

$$
F_g=t+24+4096a_g/t,\quad
Z_g=a_gt(\tau/2)+24+4096/t(\tau/2),\quad
 a_g\in\{0,1\}.
\tag{MD.2}
$$

并且 $\dim V(g)_1=24(1-a_g)$、$\operatorname{Tr}_{V_2}g=276+4096a_g$。

证明。循环 type 零的四个固定点模 $W^{(i,j)}$ 的权重模一为 $ij/2$，$S$ 矩阵为 $2^{-1}(-1)^{il+jk}$。对其字符取 $\chi_{00}-\chi_{01}$，得到 $F_g(-1/\tau)=Z_g$。原整数权与扭曲半整数权使 $F_g$ 在 $\Gamma_0(2)$ 上乘子平凡。在无穷尖点，真空和 $V_1=0$ 给 $q^{-1}+0+O(q)$；另一尖点至多有一个关于 $x=q^{1/2}$ 的单极点，因为 $h_g\ge1/2$。该模曲线以 $t$ 为有理坐标，只有两个尖点可有极点，故 $F_g=At+B+C/t$。比较首项和常数得 $A=1,B=24$；用式（MD.1）比较另一尖点的首项得 $C=4096a_g$。其接续常数项为 $24(1-a_g)$。这和 $a_g$ 都是非负整数，所以只剩零与一。比较原 $q$ 系数给最后一式。证毕。

记谱型 A 为 $a_g=1$，谱型 B 为 $a_g=0$。这是未知候选理论中的谱定义，未预先使用 Monster 的共轭类。A 扭曲模最低权为 $1/2$，该层一维且权重一为空；B 最低权为一，该层二十四维。type 条件不能由 $g^2=1$ 自动代替。

### 12.2 一个 B 型缺陷的完整逆识别

**定理 12.3（Montague–Tuite 识别机制的严格输入版本）。** 定义 12.1 的候选若存在 B 型缺陷，则 $V\cong V^\natural$，从而 $\operatorname{Aut}(V)\cong\mathbb M$。

证明。循环轨形 $W=V^{\operatorname{orb}(g)}=W^{(0,0)}\oplus W^{(1,0)}$ 是强有理全纯 VOA。原 $V_1=0$，整数权扭曲部分在权重一恰有二十四个态。对偶量子自同构 $z$ 在两个直和分量上分别为正、负，所以在 $W_1$ 上为 $-I$。任意 $u,v\in W_1$ 的括号 $u_0v\in W_1$ 同时满足

$$
z(u_0v)=(zu)_0(zv)=u_0v,\qquad z(u_0v)=-u_0v.
$$

故 $W_1$ 阿贝尔。[DM02, Theorem 3(b)] 识别 $W\cong V_\Lambda$ 为 Leech 格 VOA。

还需识别真实逆自同构。令 $\theta$ 为格反射的标准提升。$z\theta^{-1}$ 固定全部 Heisenberg 流；它保每个动量 Fock 模，并在其一维最高权线上为标量 $\chi(\lambda)$。格 OPE 的非零首项使 $\chi(\lambda+\mu)=\chi(\lambda)\chi(\mu)$。于是 $z=s_\chi\theta$。自由阿贝尔格上逐基取平方根，得字符 $\psi^2=\chi^{-1}$。由 $\theta s_\psi\theta^{-1}=s_{\psi^{-1}}$，有 $s_\psi z s_\psi^{-1}=\theta$。逆轨形定理遂给

$$
V\cong W^{\operatorname{orb}(z)}
\cong V_\Lambda^{\operatorname{orb}(\theta)}=V^\natural.
\tag{MD.3}
$$

最后的场构造与完整自同构识别用 FLM 的已知定理。证毕。

这一机制在 [T93, §3.6] 明确追溯 Montague，本批不认领其原创性。它选择完整 VOA，未以同一个 $J$ 函数替代同构。Leech 反射的扭曲最低权 $3/2$ 与本定理候选上的对偶 B 型最低权一，属于两个不同理论，不混同。

## 13. 秩十三旧判据、缺陷分布与所有能级的单插入盲性

### 13.1 把此前未写回的字符约束补齐

令 $\mathcal B=\{g\ne0:a_g=0\}$，$b=|\mathcal B|$，对实字符 $\xi:E\to\{\pm1\}$ 写 $S_\xi=\sum_{g\in\mathcal B}\xi(g)$。

**定理 13.1（精确重数及旧选择阈值）。** 权重二的字符重数满足

$$
m_1=4372+2^{12-r}(47-b),\qquad
m_\xi=2^{12-r}(47-S_\xi)\quad(\xi\ne1).
\tag{MD.4}
$$

每项必须是非负整数。因此 $r\ge13$ 时 $\mathcal B\ne\varnothing$；由定理 12.3 识别月光模型。

证明。$2^{-r}\sum_g\xi(g)g|_{V_2}$ 是投影到相应特征空间。恒等迹为 $196884$，非恒等迹通常为 $4372$，在 $\mathcal B$ 上减去 $4096$。对平凡与非平凡字符分别求和即得式（MD.4）。若 $b=0$，非平凡重数为 $47\,2^{12-r}$，$r\ge13$ 时不是整数。证毕。

同样，当 $r\ge13$，$b\equiv S_\xi\equiv47\pmod{2^{r-12}}$，且非平凡 $S_\xi\le47$。由 $\mathcal B$ 的元素作列得到的评价码，码字重 $w_\xi=(b-S_\xi)/2$ 全被 $2^{r-13}$ 整除；若 $b>47$，评价映射必单射，否则某个非平凡字符在全部列上为正，违反 $S_\xi\le47$。这些是必要条件，不保证有 VOA 实现。

### 13.2 多检查高能系数仍不能排除全 A 的秩十二分支

**定理 13.2（所有能级的单插入字符实现）。** 令 $F_A=t+24+4096/t$、$P=1/t=q\prod_{n\ge1}(1+q^n)^{24}$。有形式级数恒等式

$$
J-F_A=4096H,\qquad H=47P+4096P^2\in q\mathbb Z_{\ge0}[[q]].
\tag{MD.5}
$$

在全 A 假设下，对每个 $1\le r\le12$，单插入数据在所有能级都可由抽象分级 $E$ 表示

$$
F_A\,\mathbf1+2^{12-r}H\,\mathbb C[E]
\tag{MD.6}
$$

实现。式中级数系数表示相应表示的重数，不是 VOA 的直和公式。

证明。经典二级模恒等式 $j=(t+256)^3/t^2$ 给 $J=t+24+196608P+16777216P^2$；减去 $F_A$ 得式（MD.5）。该经典式也可在 $X_0(2)$ 上比较两尖点全部主部和常数证明：两边在上半平面无极点，减差为紧曲线上的常数，再在无穷尖点消去。$P$ 的正系数乘积使 $H$ 所有系数非负整数。全 A 假设下 $F_A(\tau)=Z_A(2\tau)$ 直接由式（MD.2）代入得到；故它的系数是实际扭曲维数，非负整数。取平凡表示和正整数倍正则表示，恒等元的迹为 $F_A+4096H=J$，所有非恒等元的正则迹为零，给 $F_A$。证毕。

这里的 $F_A=Z_A(2\tau)$ 直接由 $Z_A(\tau)=F_A(\tau/2)$ 可见，不需要额外的 moonshine genus-zero 猜想。此结论排除了“只要再查更多单插入能级就能降到十二”的策略。分级表示没有被提升成局部场乘法或扭曲模的共同实现。

## 14. 必须显式保留的共同扭曲迹实现

### 14.1 共同归一化的具体条件

**定义 14.1（共同环面迹条件）。** 在定义 12.1 的实际 $E$ 作用上，另给每个 $g$ 的扭曲模一个保权的诚实群作用 $\rho_g:E\to\operatorname{GL}(V(g))$，实现 $E$ 对扭曲顶点算子的作用；$V(0)=V$、$\rho_0$ 是原作用。要求

$$
\rho_g(g)=e^{2\pi iL_0},\qquad
Z(g,h;\tau)=\operatorname{Tr}_{V(g)}\rho_g(h)q^{L_0-1},
\tag{MD.7}
$$

以及对同一套全部 $\rho_g$，

$$
Z(g,h;-1/\tau)=Z(h,g;\tau),\qquad
Z(g,h;\tau+1)=Z(g,g+h;\tau).
\tag{MD.8}
$$

迹在上半平面全纯，尖点展开由式（MD.8）给出。不能对不同 $(g,h)$ 独立改相位后声称满足此条件；每一行必须来自同一个群表示。定义只要求实际模块、表示和变换方块，不输入任何识别缺陷、Griess 乘法或 Monster 结论。

本批秩四定理以这个条件为显式额外前提。原秩十三定理只用循环数据，不依赖它。这是加强可用接合资料后的阈值改进，不将两个不同前提集混写为已经在原全部假设下完成降阶。

### 14.2 一个能产生共同条件的明确范畴接口

**命题 14.2（量子双重的字符实现）。** 假定实际固定点 VOA $V^E$ 的不可约模有与 $E\times E^*$ 相容的标记 $M_{g,\xi}$，$V(g)=\bigoplus_\xi M_{g,\xi}$，$E$ 在该分量上按 $\xi$ 作用，且实际字符满足

$$
\chi_{g,\xi}(-1/\tau)=|E|^{-1}\sum_{k,\eta}\xi(k)\eta(g)\chi_{k,\eta}(\tau),\quad
\chi_{g,\xi}(\tau+1)=\xi(g)\chi_{g,\xi}(\tau).
\tag{MD.9}
$$

则这些分量上的作用给定义 14.1。

证明。作用按字符定义，诚实群律逐块成立。$T$ 的权重相位给 $\rho_g(g)=e^{2\pi iL_0}$。令 $Z(g,h)=\sum_\xi\xi(h)\chi_{g,\xi}$，对 $S$ 使用 $\sum_\xi\xi(h+k)=|E|\delta_{h,k}$，恰得 $Z(h,g)$；对 $T$ 用 $\xi(h)\xi(g)=\xi(h+g)$。证毕。

式（MD.9）是无扭曲 Drinfeld double 的标准模资料，但必须是实际字符的资料。[K02, §5, Lemma 5.3、Theorem 5.12] 构造零结合障碍下的共同群作用和双重范畴；[CM18, Corollary 5.25] 给可解群固定点的正则性，Theorem 6.2 给扭曲迹模协变，后一条单独只保证到非零标量。[GPRV14, §3.1, equations (39)–(40)] 展示这些标量怎样受三余循环支配，其式（40）下的双星号脚注保留从所有不可约字符变换导出通式的证明边界。[JF19, §2.2] 对共形网给严格反常框架，并说明 VOA/net 的接口条件。

本批不把上述范围不同的定理未经对象核对就拼成“任意候选 VOA 自动满足定义 14.1”。已给无反常双重实现的模型可使用命题 14.2；一般输入还须完成该实现核对。这是一个明确的前件边界，有限计算不会替代它。

## 15. 二元缺陷的循环检查能控制哪一种整体障碍？

**定理 15.1（初等二群三上同调的循环检测）。** 对 $E=\mathbb F_2^r$，若 $[\omega]\in H^3(E,U(1))$ 在每个阶二循环子群上的限制为零，则 $[\omega]=0$。

证明。$U(1)$ 可除，通用系数定理给 $H^3(E,U(1))=\operatorname{Hom}(H_3(E,\mathbb Z),U(1))$。由 $H_1(\mathbb Z_2)=H_3(\mathbb Z_2)=\mathbb Z_2,H_2(\mathbb Z_2)=0$ 及分裂的整数 Künneth 序列，归纳得 $H_1(E)=\mathbb Z_2^r$、$H_2(E)=\mathbb Z_2^{\binom r2}$，以及

$$
H_3(E)=\mathbb Z_2^{r+\binom r2+\binom r3}.
\tag{MD.10}
$$

具体地，从 $r$ 加到 $r+1$ 时，$H_3$ 指数增加 $1+\binom r2+r$，分别来自新因子的 $H_3$、$H_2(E)\otimes H_1(\mathbb Z_2)$ 和 $\operatorname{Tor}(H_1(E),H_1(\mathbb Z_2))$。

下列符号给相同数目的独立三余循环：

$$
(-1)^{a_i b_i c_i},\quad
(-1)^{a_j b_i c_i}\ (i<j),\quad
(-1)^{a_i b_j c_k}\ (i<j<k).
\tag{MD.11}
$$

指数各槽可加，直接代入五边形验证余循环。在 $\langle g\rangle$ 上，类由 $\omega(g,g,g)\in\{\pm1\}$ 决定；规范化三上边界在该三元组恒为一。各代表的对角限制依次为布尔单项式 $g_i,g_ig_j,g_ig_jg_k$。这些平方自由单项式在全部布尔输入上独立：从空支持到大小三的支持逐层消元即可。故式（MD.11）的类独立，结合式（MD.10）的总阶，它们穷尽全部类；所有循环限制为零迫使全部系数零。证毕。

只检查一组生成元不够：$(-1)^{a_1b_2c_3}$ 在三个坐标轴上平凡，在 $g=(1,1,1)$ 上非平凡。必须检查全部非零群元素。本定理专属于这里的初等二群，不外推到一般有限群。

对已建立的缺陷反常接口，循环类由 $e^{4\pi ih_g}$ 检测；type $2\{0\}$ 因而使该 $H^3$ 类为零。选择一个消去该类的共同二维余链，是一致归一化的自然路线。该纯上同调结论不单独构造实际 $V^E$ 字符，也不替代命题 14.2 的对象实现。若共同归一化已存在，剩余二维离散扭转将 $Z(g,h)$ 乘以交错双字符；它在初等二群上对称，因此不改变后文两方向符号乘积。

## 16. 三个尖点迫使两个 A 型缺陷的互易符号为负

假定定义 14.1，且一个二维子群的三个非零元素 $g,h,g+h$ 全为 A 型。$g$-扭曲模的权重 $1/2$ 基态是一条直线；$E$ 在其上是符号字符，记为

$$
\varepsilon(g,h)\in\{\pm1\},\quad
\varepsilon(g,h+k)=\varepsilon(g,h)\varepsilon(g,k),\quad
\varepsilon(g,g)=-1.
\tag{MD.12}
$$

**定理 16.1（三尖点刚性）。** 对独立的 $g,h$，

$$
Z(g,h;\tau)=16\varepsilon(g,h)R(\lambda(\tau)),\qquad
R(z)=z^{-1}-(1-z)^{-1}-z+\tfrac12,
\tag{MD.13}
$$

其中 $\lambda=\vartheta_2^4/\vartheta_3^4$ 为二级模 lambda。特别地

$$
\varepsilon(g,h)\varepsilon(h,g)=-1.
\tag{MD.14}
$$

证明。共同模变换使该迹是 $\Gamma(2)$ 上的模函数。其三个尖点分别由 $g,h,g+h$ 的扭曲模控制，每个至多有一个关于 $x=q^{1/2}$ 的单极点，且常数项全为零，因为三个扭曲模都没有权重一态。经典 $X(2)\cong\mathbb P^1$ 以 $\lambda$ 为坐标，三个尖点对应 $0,1,\infty$，且

$$
\lambda=16x-128x^2+O(x^3),\quad
\lambda(S\tau)=1-\lambda,\quad
\lambda(T\tau)=\lambda/(\lambda-1).
\tag{MD.15}
$$

这些是二级模曲线的标准输入 [Mi17, §2] 与 theta 变换。上述极点限制使 $Z=A/\lambda+B/(1-\lambda)+C\lambda+D$。分别在 $\tau,S\tau,TS\tau$ 展开，其常数为

$$
A/2+B+D,\qquad A+B/2+C+D,\qquad C/2+D.
\tag{MD.16}
$$

例如 $\lambda(TS\tau)=1-1/\lambda(\tau)=-1/(16x)+1/2+O(x)$，给第三项。令三项均为零，唯一得到 $B=-A,C=-A,D=A/2$。无穷尖点首项为 $A/(16x)$，实际基态迹为 $\varepsilon(g,h)/x$，故 $A=16\varepsilon(g,h)$。直接通分给 $R(1-z)=-R(z)$，再用共同 $S$ 变换，得 $Z(h,g)=-Z(g,h)$；比较非零基态系数给式（MD.14）。证毕。

同一经典函数也可写为 $16R(\lambda)=E_6/\eta^{12}=q^{-1/2}-492q^{1/2}-22590q^{3/2}+\cdots$。可由 theta 公式通分或同样的三尖点首项唯一性核对。此函数本身不作为新发现；本批使用的是其在未知理论的三条缺陷谱同时受限时产生的符号约束。负系数是插入自同构的迹，允许为负，不是负的态空间维数。

## 17. 九对缺陷的矛盾与秩四选择

**定理 17.1（共同扭曲迹条件下的秩四选择）。** 在定义 12.1 和 14.1 的全部前提下，若 $r\ge4$，则存在 B 型缺陷。因此 $V\cong V^\natural$，其完整 VOA 自同构群为 Monster。

证明。假设所有非零元素为 A 型。取不交的二维子空间 $U=\langle u_1,u_2\rangle$、$W=\langle v_1,v_2\rangle$，$U\cap W=0$。各有三个非零元素，且这些三个元素的和为零。由每一行的真实字符律，

$$
\prod_{h\in W\setminus0}\varepsilon(g,h)=1\quad(g\in U\setminus0),\qquad
\prod_{g\in U\setminus0}\varepsilon(h,g)=1\quad(h\in W\setminus0).
\tag{MD.17}
$$

因此九对缺陷两方向符号的总乘积为正一。但每对独立，且它们的和也是非零 A 型，所以定理 16.1 使每对乘积为负一，总乘积为 $(-1)^9=-1$。矛盾。存在 B 型以后应用定理 12.3。证毕。

证明不输入 Monster 的角色表或最大子群分类，不需要十三阶群平均，也不假设 Griess 乘法已经给定。它实际使用的新增信息是两个不同扭曲方向的共同模协变及同一基态线上全部群元素的乘法。四个生成元指四个对易独立对称，不等于四个任意量子门、量子位或空间维度。

### 17.1 不止存在一个：每个四维子空间都必须遇到 B 型

**定理 17.2（识别缺陷的全局数量下界）。** 若上述共同条件在 $E$ 上成立，$r\ge4$，则

$$
|\mathcal B|\ge2^{r-3}-1.
\tag{MD.18}
$$

因此秩十二至少有 $511$ 个 B 型，秩十三至少有 $1023$ 个。

证明。限制到任意四维子空间仍满足同一前提，故由定理 17.1，每个这样的子空间都有 B 型。若 $b<2^{r-3}-1$，归纳构造与 $\mathcal B$ 不交的子空间。已有维数 $k\le3$ 的 $U$ 时，其非零陪集数为 $2^{r-k}-1>b$，至少有一个陪集完全不含 $\mathcal B$。选代表 $v$，则 $U\oplus\langle v\rangle=U\cup(v+U)$ 仍不交。重复四次得到不含 B 型的四维子空间，矛盾。证毕。

这是一个独立的有限几何阻挡集论证。非零的余维三子空间达到纯几何界，但通常不能同时满足式（MD.4）的字符约束，故本稿不声称 VOA 可达到等号。比如 $r\ge9$ 时该下界大于 $47$，式（MD.4）还迫使 $\mathcal B$ 张成整个 $E$。此前仅按 Fourier 条件构造的某些抽象例，如秩十三中只放一个 B 型，现被共同接合判据排除；它们从未被声明为实际 VOA。

## 18. 秩三边界与剩余选择问题

**命题 18.1（基态符号条件的精确有限边界）。** 仅要求式（MD.12）及全部独立非零对上的式（MD.14），秩三有解，秩四无解。秩三的解恰有八个，彼此相差交错双线性形式。

证明。以 $1,2,4$ 为 $\mathbb F_2^3$ 的二进基，用标准点积标记对偶线性形式。按非零 $g=1,2,3,4,5,6,7$ 排列，取

$$
\ell_g=1,3,6,7,4,5,2,\qquad
\varepsilon(g,h)=(-1)^{\ell_g\cdot h}.
\tag{MD.19}
$$

逐个点积给 $\ell_g(g)=1$，以及 $\ell_g(h)+\ell_h(g)=1$ 对所有 $g\ne h$；这是七行、二十一对的有限验证。秩四无解已由九对证明。若 $\ell,\ell'$ 为两个解，差 $d(g,h)$ 对第二变量线性，且 $d(g,h)=d(h,g),d(g,g)=0$。由对称性，它对第一变量也线性，故为交错双线性形式。反向，加入任意这种形式保持条件。三维空间的交错双形式维数为三，所以恰有 $2^3$ 个解。证毕。

八个符号表只说明这一级有限约束相容，未构造 VOA、缺陷 OPE 或完整高能谱。若要继续降到秩三，必须使用更多实际结构，并先核查是否已有满足全 A 条件的真实秩三例；不能仅因当前方法到边界就断言三必不可能。

本批的出现解释现在具有具体逻辑：中心荷与低能缺口限制单缺陷谱；双方向环面接合强制互易负号；足够多共同对称使这些负号不能全局相容；被迫出现的另一种缺陷通过逆轨形选择整个月光场代数。普遍 FLM 唯一性、从给定 Fibonacci 自旋链导出此 VOA、以及任何真实材料的实现均未由此解决。

## 19. 形式化顺序、来源与实际交付检查

有限证明先实现：分级有限表示的字符投影；式（MD.5）的模恒等式接口与整系数 Euler 乘积；$\mathbb F_2$ 三余循环及循环限制；有理函数的三尖点主部与常数线性方程；一维表示的符号乘法；九对矛盾；陪集递推阻挡界；秩三显式点积表。条件 14.1 必须由实际模块及模变换方块承载，不能将“存在 B 型”或“同构于月光”作为它的字段。完整 VOA、Zhu 模性、循环轨形、Leech/FLM 识别仍是实质性外部依赖。

[DM02] C. Dong and G. Mason, *Holomorphic Vertex Operator Algebras of Small Central Charges*, arXiv:math/0203005. https://arxiv.org/pdf/math/0203005 。本批读取 Lemma 2.1 和 Theorem 3(b)，用于字符和二十四维阿贝尔流刚性。

[EMS20] J. van Ekeren, S. Möller and N. R. Scheithauer, *Dimension Formulae in Genus Zero and Uniqueness of Vertex Operator Algebras*, IMRN 2020, 2145–2204; arXiv:1704.00478v3. https://arxiv.org/pdf/1704.00478 。使用 §3 的循环规范化及逆轨形、§4.1 的 eta 主模；PDF 第 9、15 页已视觉核对。其二阶维数机制已有 Montague 来源。

[T93] M. P. Tuite, *On the Relationship between Monstrous Moonshine and the Uniqueness of the Moonshine Module*, arXiv:hep-th/9305057. https://arxiv.org/pdf/hep-th/9305057 。§3.6 的逆轨形识别是定理 12.3 的历史归属。FLM 完整群识别与本卷原 §2 保持相同外部来源。

[GPRV14] M. R. Gaberdiel, D. Persson, H. Ronellenfitsch and R. Volpato, *Generalised Mathieu Moonshine*, arXiv:1211.7074v3. https://arxiv.org/pdf/1211.7074 。采用 §3.1 对一般 holomorphic orbifold 的项目作用、余循环和模变换的说明，不采用该文后续对 Mathieu 扭曲椭圆亏格的猜测作为证明。PDF 第 17、18 页已视觉核对；第 18 页式（40）下双星号脚注的一般推导边界保留在 §14.2。

[K02] A. Kirillov Jr., *Modular categories and orbifold models*, Commun. Math. Phys. 229 (2002), 309–335; arXiv:math/0104242. https://arxiv.org/pdf/math/0104242 。读取引言的完整假设、§5 的结合三余循环、Lemma 5.3 和 Theorem 5.12。使用的是零余循环下的真实双重范畴构造，不能直接以它删去实际字符实现义务。

[CM18] S. Carnahan and M. Miyamoto, *Regularity of fixed-point vertex operator subalgebras*, arXiv:1603.05645v4. https://arxiv.org/pdf/1603.05645 。读取 Corollaries 5.25–5.26、Theorem 6.2；正则性及到标量的协变不被混称为自动已固定全部相位。

[Mi17] J. S. Milne, *Modular Functions and Modular Forms*, v1.31 (2017). https://www.jmilne.org/math/CourseNotes/MF.pdf 。使用 §2 的紧模曲线与尖点基础；式（MD.15）的 lambda 规范与 theta 变换另列为标准二级模函数输入。式（MD.13）的常数消元与符号结论由正文直接证明。

[CC26] S. Carpi and G. Codogni, *Vertex operator algebras, partition functions and Teichmüller modular forms*, arXiv:2605.26972v1. https://arxiv.org/html/2605.26972v1 。本轮重新读取其一般 FLM 唯一性仍开放的说明，不把条件识别定理升级为该猜想的解答。缺陷反常的来源继续使用本卷 [JF19]，本轮亦读取其 §2.2 的 VOA/net 范围区别。

本批定向检索没有建立秩四选择及其阻挡集组合的全球优先权。三余循环、模函数、逆轨形和有限几何工具都有既有来源；这里的研究增量是把它们接到明确的未知场论选择条件，并给出可逐项核对的证明。检索返回的若干相关性不足结果未用作依据。

实际执行文件为 [`twisted_pair_checks.py`](../../reports/monster-twisted-pair-selection/twisted_pair_checks.py)，输出为 [`twisted_pair_results.json`](../../reports/monster-twisted-pair-selection/twisted_pair_results.json)。使用标准库整数和 Fraction 到截断阶 40，检查式（MD.5）、lambda 的独立 theta 乘积与 $E_6/\eta^{12}$、三尖点消元、九对矛盾、秩三完整表和余循环限制。另以全体低维输入检查余循环方程及 32 个低维四子空间。输出复跑逐字节一致。此前附件的 `monster_selector_checks.py` 也实际复跑，与其原结果一致，未把这次重放计算作新增理论结果。

上述程序没有构造真实 VOA、共同扭曲迹条件、范畴–解析字符的衔接、Leech 格或 Monster。新结论仍接受独立数学复核；没有 Lean/Scribe、CI 或物理实验成功声明。原主卷所有字节保持，原 QCA 卷和已有并行三阶响应内容未改写。

## 追加锚（本行以下为后续增补区，MD 批次结束）
