# 算术全息 RT：复制不变量、局部粗化与单环谱

本篇接续 [算术全息量子网络与 RT 型恒等式](ARITHMETIC_HOLOGRAPHIC_RT.md)，研究该卷的顶点粗化义务及其与公开完美张量问题的关系。全部新增证明是有限维纸面数学证明，尚无配套 Lean 内核证明。文献已知结果与本篇推导分别标明；具体结论的优先权尚未全面排除，不认领原始引力 RT、完整 TPTN 大维数谱问题或具名开放问题的完整结算。

## 1. 对象与外部锚点

所有对数取自然对数。对奇数阶有限交换群 $G$，定义

$$
|T_G\rangle=\frac1{|G|}\sum_{x,y\in G}|x,y,x+y,x+2y\rangle.
$$

当 $G=\mathbb Z/d\mathbb Z$ 时记为 $T_d$。因为乘以 $2$ 是 $G$ 的自同构，四个坐标中任取两个均唯一确定 $(x,y)$；故任意二方约化态为 $I/|G|^2$。这就是 AME$(4,|G|)$。乘积群满足

$$
T_{G\times H}=T_G\otimes T_H
$$

其中张量积按四个参与方分别重组。母卷的 $T_3$ 来自已有 `D5/S3/Quantum/Entanglement/QutritThresholdSharing.lean` 编码的 Choi 态。

本篇使用的外部定理是 [RRKL23] Theorem 1：所有 AME$(4,3)$ 在四方局部幺正变换下等价。该结论已经发表，不能再次作为未解决猜想。它使九维顶点能否独立局部粗化成三维完美顶点成为一个可判定的具体问题。

另一个外部锚点是 [TPTN26] 第 5.1 节的模型和第 7 节提出的谱平坦性问题。其模型在完美张量每条腿上施加独立 Haar 幺正变换；内部相邻两腿的变换可以合并成每条边的一个独立 Haar 幺正矩阵。该文第 5.2 节的 RT 推导是大连接维数推导，并在式 (5.23) 前注明无领先简并的假设。下面给出有限单环的精确二阶矩与非平坦例子，不把这些结论外推成该文全部大维数论断的反驳。

## 2. 检测三挠元的四副本局部幺正不变量

**定义 2.1。** 用 $i=0,1,2,3$ 标记副本，取四个置换的像数组

$$
\sigma_1=(0,1,2,3),\quad \sigma_2=(1,0,3,2),\quad
\sigma_3=(2,3,1,0),\quad \sigma_4=(3,2,0,1).
$$

对归一化四方态 $\psi$，定义收缩

$$
I(\psi)=\sum_{(z_{\ell,i})}
\prod_{i=0}^3\psi_{z_{1,i},z_{2,i},z_{3,i},z_{4,i}}
\overline{\psi_{z_{1,\sigma_1(i)},z_{2,\sigma_2(i)},z_{3,\sigma_3(i)},z_{4,\sigma_4(i)}}}.
$$

同一参与方的各副本指标取相同局部基。此表达式等于 $\operatorname{Tr}(W\rho^{\otimes4})$，其中 $W$ 是相应四组局部副本置换的张量积，$\rho=|\psi\rangle\langle\psi|$。$W$ 与每个 $U_\ell^{\otimes4}$ 交换，故 $I$ 在任意四方局部幺正变换下不变。按参与方重组张量积时，收缩分离，故 $I(\psi\otimes\varphi)=I(\psi)I(\varphi)$。复制收缩作为局部幺正不变量的方法已有文献基础 [RRKL23]；下式是此特定收缩在当前算术张量族上的求值。

**定理 2.2（四副本三挠谱）。** 记 $G[3]=\{a\in G:3a=0\}$，则

$$
\boxed{I(T_G)=\frac{|G[3]|^2}{|G|^6}.}
$$

**证明。** 对四个 ket 副本写变量 $(x_i,y_i)$。前两条腿的匹配将 bra 变量确定为 $(x_i,y_{\sigma_2(i)})$。剩余条件是

$$
x_i+y_{\sigma_2(i)}=x_{\sigma_3(i)}+y_{\sigma_3(i)},\qquad
x_i+2y_{\sigma_2(i)}=x_{\sigma_4(i)}+2y_{\sigma_4(i)}.
$$

所有解恰由 $s,t\in G$ 与 $a,c\in G[3]$ 唯一参数化：

$$
(x_0,x_1,x_2,x_3)=(s,s+c,s+2a+c,s+a),
$$

$$
(y_0,y_1,y_2,y_3)=(t+a,t+2a+c,t,t+c).
$$

为验证充要性，先取 $s=x_0,t=y_2,a=y_0-y_2,c=y_3-y_2,b=y_1-y_2$。指标 $i=0,3,1$ 的第一类等式依次给出 $x_2=s+b$、$x_3=s+a$、$x_1=s+c$。第二类等式依次给出 $2b=a+2c$、$b=2a+c$、$b+2c=2a$、$a=c+2b$，等价于 $b=2a+c$、$3a=0$、$3c=0$，继而得到所列参数化。反向代入八条等式逐项成立。因此解数为 $|G|^2|G[3]|^2$。每项包含八个振幅因子 $|G|^{-1}$，得到结论。证毕。

**推论 2.3。** $T_9$ 与按参与方重组的 $T_3\otimes T_3$ 不局部幺正等价，因为

$$
I(T_9)=3^{-10}=\frac1{59049},\qquad
I(T_3\otimes T_3)=3^{-8}=\frac1{6561}.
$$

更一般地，$n\ge2$ 时 $T_{3^n}$ 与 $T_3\otimes T_{3^{n-1}}$ 不局部幺正等价。这一结论只比较所写的规范张量因子，不声称已经分类任意高维 AME 因子。

二者全部子系统谱却相同：它们都是 AME$(4,9)$，任意一方熵为 $\log9$，任意两方熵为 $2\log9$，三方熵由纯性等于 $\log9$。因此全部二分熵和全部二分 Rényi 谱无法区分此例，四副本收缩可以。

**推论 2.4（局部等价的定量分离）。** 对任意四方局部幺正 $U$，

$$
\frac12\left\||T_9\rangle\langle T_9|-U(|T_3\otimes T_3\rangle\langle T_3\otimes T_3|)U^*\right\|_1
\ge\frac1{59049}.
$$

**证明。** 对任意密度矩阵 $\rho,\tau$，张量积望远镜展开与 $\|W\|_\infty=1$ 给出

$$
|I(\rho)-I(\tau)|\le\|\rho^{\otimes4}-\tau^{\otimes4}\|_1\le4\|\rho-\tau\|_1.
$$

代入不变量差 $8/59049$。证毕。此界针对局部幺正因子化；不未经额外稳定性证明就当作一般近似量子通道的误差界。

## 3. 任意独立局部量子通道的纯态粗化障碍

**引理 3.1（纯 AME 输出迫使层分解）。** 设 $D=de$，$\psi$ 是 AME$(4,D)$，$\varphi$ 是 AME$(4,d)$。存在四个局部 CPTP 通道 $\Phi_i:M_D(\mathbb C)\to M_d(\mathbb C)$ 使

$$
(\Phi_1\otimes\Phi_2\otimes\Phi_3\otimes\Phi_4)(|\psi\rangle\langle\psi|)=|\varphi\rangle\langle\varphi|
$$

当且仅当 $\psi$ 在按参与方重组后局部幺正等价于 $\varphi\otimes\eta$，其中 $\eta$ 是某个 AME$(4,e)$。

**证明。** 取每个通道的局部 Stinespring 等距 $V_i$。纯输出意味着整体纯化因子化：

$$
(\otimes_iV_i)|\psi\rangle=|\varphi\rangle\otimes|\eta\rangle.
$$

单方约化态满足

$$
\frac{V_iV_i^*}{D}=\frac{I_d}{d}\otimes\eta_i.
$$

左侧是秩 $D$ 的归一化投影。因此 $\eta_i$ 恰有 $e$ 个非零本征值，均为 $1/e$。把其支撑识别为 $\mathbb C^e$ 后，$V_i$ 是从 $\mathbb C^D$ 到 $\mathbb C^d\otimes\mathbb C^e$ 的幺正映射。任意二方输入约化态也为最大混合；与 $\varphi_{ij}=I_{d^2}/d^2$ 比较得 $\eta_{ij}=I_{e^2}/e^2$。于是 $\eta$ 是 AME$(4,e)$。反向先实施局部幺正分解再分别偏迹环境即得。证毕。

**定理 3.2（九维循环顶点不能独立局部粗化成三维完美顶点）。** 对任意 AME$(4,3)$ 纯态 $\varphi$，不存在四个 CPTP 通道使

$$
(\otimes_{i=1}^4\Phi_i)(|T_9\rangle\langle T_9|)=|\varphi\rangle\langle\varphi|.
$$

**证明。** 若存在，引理 3.1 迫使 $T_9$ 局部幺正等价于两个 AME$(4,3)$ 的张量积。[RRKL23] Theorem 1 将这两个因子各自局部幺正化为 $T_3$，与推论 2.3 矛盾。证毕。

这一定理没有保留计算基余数的附加要求，也没有将局部操作限制为 Fourier 或 Clifford 类。局部辅助系统和局部丢弃均已包含在 CPTP 中。它还排除共享经典随机变量混合的乘积通道：纯输出是态空间极点，混合中的每个正权分支都必须产生同一个纯态，然后逐分支应用定理。没有排除通信、自适应 LOCC、共享纠缠辅助资源、联合多腿操作、混合输出或近似输出。

**推论 3.3（母卷顶点义务的明确否定范围）。** 母卷第 11 节的纯缝合连接通道塔，无法仅由四条腿各自独立的 CPTP 粗化拼成保持 $T_9\mapsto T_3$ 纯顶点的精确 $9\to3$ 步骤。这是一个顶点级障碍，不是任意整体网络粗化的不存在定理。

**推论 3.4。** 相同 RT 型熵数据不能决定纯顶点的局部粗化能力。$T_3\otimes T_3$ 和 $T_9$ 的所有二分谱相同，前者按方偏迹一层可得到 $T_3$，后者被定理 3.2 排除。

## 4. 两条输出腿上的可逆进位修正

障碍可以由明确的联合操作跨过。令 $d,e\ge3$ 为奇数，$D=de$，每条腿实施数字分解

$$
W|a+db\rangle=|a\rangle_d|b\rangle_e.
$$

写内部变量 $x=a+db,y=c+df$，其中 $0\le a,c<d$、$0\le b,f<e$。令

$$
r=(a+c)\bmod d,\qquad s=(a+2c)\bmod d,
$$

$$
\kappa_1=(a+c-r)/d,\qquad \kappa_2=(a+2c-s)/d.
$$

低位输出 $(r,s)$ 唯一恢复 $a=(2r-s)\bmod d$、$c=(s-r)\bmod d$，故两个进位也是 $(r,s)$ 的确定函数。

**定理 4.1（联合进位消除）。** 在第三、第四参与方上定义置换幺正

$$
C_{d,e}:|r,k\rangle_3|s,h\rangle_4
\longmapsto|r,k-\kappa_1(r,s)\rangle_3|s,h-\kappa_2(r,s)\rangle_4,
$$

高位减法取模 $e$。则按低、高层重组后有精确等式

$$
\boxed{C_{d,e}W^{\otimes4}|T_{de}\rangle=|T_d\rangle\otimes|T_e\rangle.}
$$

**证明。** $x+y$ 的高位为 $b+f+\kappa_1$，$x+2y$ 的高位为 $b+2f+\kappa_2$，均取模 $e$。$C_{d,e}$ 保留低位并按其确定值平移高位，因此可逆。修正后四方低位为 $(a,c,a+c,a+2c)$，高位为 $(b,f,b+f,b+2f)$，且系数 $1/(de)$ 分离为 $(1/d)(1/e)$。证毕。

这给出具体的联合门及随后偏迹的精确粗化。$d=e=3$ 时，独立局部通道不可能，允许第三、第四方之间这一联合置换就足够。本篇不宣称最少基本门数或最少通信量。

若 $\gcd(d,e)=1$，另一个精确因子化由每方中国剩余定理基变换 $|x\rangle\mapsto|x\bmod d,x\bmod e\rangle$ 给出，无须跨方操作。素数幂的数字分解不具备该 CRT 条件，不能沿用这一局部证明。

## 5. Haar 修饰单环的精确平均纯度

取长度 $L\ge3$ 的环，每个顶点放归一化 AME$(4,d)$，两条腿作为环内连接，另外两条为边界。在每条内部边独立取 Haar 幺正 $U\in U(d)$，用归一化最大纠缠态

$$
|U\rangle=(U\otimes I)|\Phi_d\rangle,\qquad
|\Phi_d\rangle=d^{-1/2}\sum_j|j,j\rangle
$$

进行收缩。边界腿上的独立局部幺正不影响任何区域谱。此定义是 [TPTN26] 式 (5.6) 在单环图上的实例。记未归一化网络态为 $|V\rangle$，$Z=\langle V|V\rangle$。取区域 $A$ 在每个顶点恰好包含一条边界腿。

**定理 5.1（任意有限维的精确二阶矩）。** 对上述网络，逐个样本均有 $Z=d^{-2L}$，且

$$
\boxed{\mathbb E\operatorname{Tr}(\rho_A^2)=\frac{2}{d^L}.}
$$

这里期望是归一化态的真实期望，没有以分子、分母期望之比代替随机比值。二者在此相同的原因是 $Z$ 本来就是常数。

**证明。** 每个 AME 顶点对两条外腿偏迹后，环内两腿约化态为 $I_{d^2}/d^2$。各归一化边态的迹为一，所以网络范数平方恒为 $d^{-2L}$。

令 $F$ 表示两副本上的交换。单条 Haar 边的二阶矩为

$$
\mathbb E\bigl[(|U\rangle\langle U|)^{\otimes2}\bigr]
=\frac{I\otimes I+F\otimes F-d^{-1}(I\otimes F+F\otimes I)}{d^2(d^2-1)}.
$$

可以由两副本 Haar 平均的交换子空间求得：平均结果在两端的 $I,F$ 张成空间内；四个迹约束是 $1,1/d,1/d,1$，解其四元线性方程即得所列系数。这里与 [TPTN26] 使用同一 Haar 二阶矩，后面的单环收缩保留所有有限 $d$ 项。

用二进标号表示每个半边上是否交换。边权矩阵与区域 $A$ 的顶点矩阵分别为

$$
M=\begin{pmatrix}1&-d^{-1}\\-d^{-1}&1\end{pmatrix},\qquad
V_A=\begin{pmatrix}d^{-1}&d^{-2}\\d^{-2}&d^{-1}\end{pmatrix}.
$$

顶点矩阵来自 AME 的约化纯度：两个外腿中一个交换，两个内腿各按其标号交换，选中腿数为 $1+s+t$，其纯度是 $d^{-\min(1+s+t,3-s-t)}$。因此未归一化纯度分子 $N_A=\operatorname{Tr}[(\operatorname{Tr}_{\bar A}|V\rangle\langle V|)^2]$ 满足

$$
\mathbb E N_A=[d^2(d^2-1)]^{-L}\operatorname{Tr}[(MV_A)^L].
$$

精确相乘得

$$
MV_A=\frac{d^2-1}{d^3}I_2,
$$

所以 $\mathbb E N_A=2d^{-5L}$。除以常数 $Z^2=d^{-4L}$ 得结论。证毕。

**推论 5.2（谱偏差的明确尺度）。** 令 $N=d^L$。这一平衡划分的最小割为 $L$，并有

$$
\mathbb E\left[N\operatorname{Tr}(\rho_A-I_N/N)^2\right]=1.
$$

因此相对于最大混合态的归一化 Hilbert–Schmidt 平均平方偏差，不随 $d\to\infty$ 消失。另一方面，未归一化的平均平方距离为 $1/N$，确实趋于零。这两种范数尺度不能混用。

此外

$$
-\log\mathbb E\operatorname{Tr}(\rho_A^2)=L\log d-\log2,
$$

且由 Jensen 不等式和 $S\ge S_2$ 得

$$
L\log d-\log2\le\mathbb E S_2(\rho_A)\le\mathbb E S(\rho_A)\le L\log d.
$$

所以领先熵仍满足 RT 斜率，完整谱却没有由这一领先斜率唯一确定。此图至少具有把所有内部顶点分别归入两侧的两个同容量最小割，不符合 [TPTN26] 明示的无领先简并条件。本篇不把上式当作该受限推导的反例，也未从平均二阶矩直接断言任意其他谱距离的概率极限。

**推论 5.3（循环算术顶点的几乎处处非平坦性）。** 对奇数 $d\ge3$，若每个顶点为母卷的 $T_d$，则在内部 Haar 幺正乘积测度下，上述 $\rho_A$ 几乎处处满秩且非平坦。

**证明。** 母卷定理 9.3 给出一个内部幺正参数点，使全部边界区域达到最大割熵，特别地 $\rho_A=I_N/N$，故 $\det\rho_A$ 作为连通实解析流形 $U(d)^L$ 上的实解析函数不恒为零。其零集 Haar 测度为零。又由定理 5.1，实解析非负函数 $\operatorname{Tr}(\rho_A^2)-1/N$ 不恒为零，其零集也为零测集。满秩且纯度严格大于 $1/N$，便不能有平坦谱。证毕。这里只用实解析非零函数的零集零测这一标准事实；没有声称所有具体参数点都非平坦。

## 6. 六 qutrit 的精确非平坦例子

取 $d=L=3$，三个顶点均为 $T_3$。两条内部边用恒等缝合，第三条用

$$
U=F_3\operatorname{diag}(1,1,-1),
$$

其中 $F_3$ 取正指数约定。每个被修饰的局部张量仍完美。归一化边界态可写为

$$
|\Psi\rangle=\frac19\sum_{x_0,x_1,x_2,x_3\in\mathbb Z_3}
\omega_3^{x_0x_3}g(x_0)
\bigotimes_{i=0}^2|x_i+x_{i+1},x_i+2x_{i+1}\rangle,
\quad g=(1,1,-1).
$$

**命题 6.1。** 对每个顶点选择第一条输出的区域 $A$，完整谱为

$$
\operatorname{spec}(\rho_A)=
\{(1/81)^{\times9},(4/81)^{\times18}\}.
$$

**证明。** 两侧的线性输出映射在路径群 $\mathbb Z_3^4$ 上各有一维核，且核交为零。按二核之和分解共有九个互相局部正交的陪集块，每块权重 $1/9$。在任一块中，两侧局部对角相位和基置换消去 Fourier 二次相位；其限制交叉双字符为母卷 $L=3,k=0,\alpha=0$ 的 $c_0=0\pmod3$。余下归一化系数矩阵为

$$
H_{ab}=g(a+b+t)/3,\qquad a,b\in\mathbb Z_3,
$$

其中 $t$ 只改变行列的循环置换。$g$ 的未归一化 Fourier 变换模平方为 $1,4,4$，因此每块的 Schmidt 权重为 $1/9,4/9,4/9$。乘以块权重 $1/9$ 得完整谱。证毕。

于是

$$
\operatorname{Tr}\rho_A^2=\frac{11}{243},\qquad
\operatorname{Tr}\rho_A^3=\frac{43}{19683},\qquad
\operatorname{Tr}\rho_A^3-(\operatorname{Tr}\rho_A^2)^2=\frac8{59049}>0,
$$

$$
S(\rho_A)=4\log3-\frac89\log4<3\log3=m(A)\log3.
$$

对任意密度矩阵，最后的三阶矩差是以本征值自身为概率权重时的本征值方差，故非负，且为零当且仅当所有非零本征值相等。该见证可以写成两副本、三副本局部循环置换的期望值。这里给出了可由有限量子线路表达的观测量，没有声称已经完成实验制备或硬件测量。

## 7. 外部小问题的定位与可迁移内容

[TPTN26] 第 7 节询问 TPTN 是否具有平坦纠缠谱，第 5.2 节则讨论大 $d$ 及其假设。本篇定理 5.1 和命题 6.1 为其中有限单环问题给出精确答案：一般样本并不精确平坦，归一化平均平方谱偏差恒为一；领先熵仍可趋向 RT 值。未解决的问题包括排除最小割简并后的典型谱极限、其他范数下的收敛，以及完整体态编码的区域恢复。

[BZ24] Conjecture 1 是另一个明确的外部目标：该文的 $\mathcal H(\alpha)$、$U_1$、$U_2$、$U_3(a)$ 四个 36 阶矩阵族，在其全部指定参数上两两既不局部幺正等价，也不 Hadamard 等价。论文给出了矩阵和参数化。局部幺正等价与 Hadamard 单项式等价是不同关系；本文四副本收缩可用于前者，不能未经证明就用于后者。该猜想在本篇检索的原文与相关来源中没有找到完整结算，不能将有限检索的未发现表述为已穷尽文献。

本篇尚未完整证明或反驳 [BZ24] Conjecture 1。维数九的挠元不变量给出可迁移的判别机制；第 8 节把它作用于该文的实际矩阵，并写清已知固定代表和仍未闭合的参数量词。已解决的 AME$(4,3)$ 唯一性只作为 [RRKL23] 的现成定理使用。

目前具体可复用的数学产出是：有限群三挠元的四副本求值；任意独立局部量子通道的九维纯顶点粗化障碍；两条输出腿的精确进位修正；有限单环 Haar 纯度的全尺寸公式和精确非平坦样本。它们分别约束粗化操作、局部等价、可实现的纠缠谱与 RT 型熵数据，未补齐物理边界理论、连续几何和引力动力学。

## 参考文献

[RRKL23] S. A. Rather, N. Ramadas, V. Kodiyalam, A. Lakshminarayan. Absolutely maximally entangled state equivalence and the construction of infinite quantum solutions to the problem of 36 officers of Euler. Physical Review A 108 (2023), 032412. DOI: 10.1103/PhysRevA.108.032412. arXiv:2212.06737v2. 使用 Theorem 1；局部幺正复制不变量的背景见正文。

[TPTN26] G. Arora, M. Headrick, A. Lawrence, M. Sasieta, B. Swingle, C. Wolfe. Twirled Perfect Tensor Networks: Computationally covariant holographic tensor networks. arXiv:2605.23670v1 (2026). 使用第 5.1 节定义、第 5.2 节大连接维数范围和第 7 节公开问题；预印本身份不改称已发表定理。

[BZ24] W. Bruzda, K. Życzkowski. Two-unitary complex Hadamard matrices of order 36. Special Matrices 12 (2024), 20240010. DOI: 10.1515/spma-2024-0010. 使用第 4 节 Conjecture 1。

[Tan26] I. Tan. Transversal gates of the ((3,3,2)) qutrit code and local symmetries of the absolutely maximally entangled state of four qutrits. arXiv:2601.19677 (2026). 作为完美 qutrit 顶点与量子纠错实际操作的相关文献，不以其替代本篇证明。

## 8. 实际 36 阶矩阵上的精确证书及参数切片

本节使用 [BZ24] 式 (10)–(15) 的原始矩阵。固定代表的不可等价性也已见于 [Rather24] 第 5.2 节；本节的固定三点证书属于已知结果的精确验证，不计作新的开放问题解决。该文矩阵与 [BZ24] 的形式相差两侧局部 Fourier 因子，不改变局部等价问题。

令 $\zeta=e^{i\pi/3}$，$\lambda_j(a,b)$ 为 [BZ24] 的三个长度 36 相位向量按 $6\times6$ 排列后的整数指数。前两个向量的分母为六；第三个向量原分母为三，转成 $\zeta$ 指数时须乘以二。按该文的正指数 Fourier 约定，直接展开式 (13) 得

$$
(U_j)_{kl,mn}=\frac{\zeta^{lk+nm}}{36}
\sum_{a,b=0}^5\zeta^{a(l-n)-b(k+m)+\lambda_j(a,b)}.
$$

因此 $H_j=6U_j$ 的每个元素都是六次单位根；对应归一化四方态为 $\psi_j=H_j/36$。

**证书 8.1（固定三代表）。** 对定义 2.1 的同一四副本收缩，精确值为

$$
I(\psi_1)=\frac{35}{419904}=\frac{70}{839808},\qquad
I(\psi_2)=\frac{79}{839808},\qquad
I(\psi_3)=\frac1{15552}=\frac{54}{839808}.
$$

这三个不同值证明固定 $U_1,U_2,U_3(0)$ 两两不局部幺正等价。未归一化分子依次为

$$
235146240,\quad265379328,\quad181398528,
$$

公共分母为 $36^8=2821109907456$。这些值由附录的 $\mathbb Z[\zeta]/(\zeta^2-\zeta+1)$ 精确整数收缩得出，没有使用浮点拟合、奇异值阈值或优化失败来断言不等价。

**证书 8.2（非恒等相位参数的精确谱缺陷）。** 用 $z\in U(1)$ 表示 [BZ24] 式 (15) 中实际乘到指定元素上的相位，避免其 $a$ 与 $2\pi a$ 的角度记法混淆。令 $M$ 是该式零一掩码，$U_3(z)=U_3\circ z^M$。则对全部 $|z|=1$，

$$
\|U_3(z)U_3(z)^*-I\|_F^2=0,
$$

$$
\|U_3(z)^R(U_3(z)^R)^*-I\|_F^2
=\|U_3(z)^\Gamma(U_3(z)^\Gamma)^*-I\|_F^2
=\frac{17}{6}-\frac{17}{12}(z+z^{-1}).
$$

所以当 $z=e^{i\theta}$，任一相应二方约化态的纯度是

$$
\operatorname{Tr}(\rho_R(z)^2)
=\frac1{36}+\frac{17}{7776}(1-\cos\theta).
$$

**精确验证。** 将掩码内、外的 $H_3$ 分成 $A+zB$。对三个重排分别计算

$$
(A+zB)(A^*+z^{-1}B^*)-36I
$$

的平方 Frobenius 范数，再除以 $36^2$。环内收缩给出的 $z^{-2},z^{-1},1,z,z^2$ 系数，对原排列全部为零，对另两种排列分别为

$$
(0,-17/12,17/6,-17/12,0).
$$

有限 Laurent 多项式的系数完全相等即覆盖整个单位圆。状态归一化还要除以 $36^2$，得到纯度式。附录给出可重放计算。证毕。

**推论 8.3。** $z\ne1$ 时，$U_3(z)$ 不与任何二幺正矩阵局部幺正等价。因此对于 [BZ24] 的所有 $\alpha$，它不与 $\mathcal H(\alpha)$、$U_1$ 或 $U_2$ 局部幺正等价。$z=1$ 时与 $U_1,U_2$ 的分离由证书 8.1 给出，与 $\mathcal H(\alpha)$ 的关系仍未由本篇解决。

[BZ24] 表 1 已提示非零相位通常破坏二幺正性，本节给出其实际相位 $z$ 的精确恒等式和所有周期回返 $z=1$ 的边界，不以该提示冒充新发现。仍缺少 $\mathcal H(\alpha)$ 与三个固定代表之间的全参数局部不等价证明，以及完整的 Hadamard 不等价部分。没有将本节证书登记成完整 Conjecture 1 的解决。

[Rather24] S. A. Rather. Construction of perfect tensors using biunimodular vectors. Quantum 8 (2024), 1528. DOI: 10.22331/q-2024-11-20-1528. arXiv:2309.01504v2. 第 5.2 节已说明固定三个 biunimodular 代表的局部不等价性。

## 附录 A. 证书 8.1 与 8.2 的精确整数重放

以下 Python 程序依赖 NumPy 和 opt_einsum；后者仅决定收缩顺序。所有承重数组为带符号 64 位整数，根环元写为 $a+b\zeta$，乘法为 $(ac-bd)+(ad+bc+bd)\zeta$，共轭为 $(a+b)-b\zeta$。完整收缩最多有 $6^{16}$ 个单位根项，分量中间运算的保守界 $3\cdot6^{16}<2^{63}$，不会溢出。原始相位向量和掩码来自 [BZ24]；此程序是有限等式的计算证书，不是 Lean 内核检查。

```python
import itertools
from fractions import Fraction
import numpy as np
import opt_einsum as oe

perms = ((0,1,2,3),(1,0,3,2),(2,3,1,0),(3,2,0,1))
units = np.array([(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)], dtype=np.int64)
vectors = [
 [0,1,0,1,3,3,3,3,1,5,2,4,2,1,3,1,2,3,1,1,2,0,3,5,5,3,2,3,2,5,4,4,1,5,5,1],
 [0,2,3,3,2,0,0,3,2,2,0,4,2,0,3,5,0,0,0,5,0,0,2,0,2,2,5,3,2,4,2,3,0,2,0,0],
 [0,2,2,0,0,1,0,1,1,1,2,1,0,2,0,2,2,2,2,0,2,2,2,1,1,1,2,0,2,2,0,1,2,2,1,0]
]

def conj(a,b):
    return a+b, -b

def mm(a,b,c,d):
    return a@c-b@d, a@d+b@c+b@d

def make_h(j):
    lam = np.array(vectors[j]).reshape(6,6)*(2 if j == 2 else 1)
    a = np.zeros((6,)*4, dtype=np.int64)
    b = a.copy()
    for k,l,m,n in itertools.product(range(6), repeat=4):
        v = sum((units[(x*(l-n)-y*(k+m)+int(lam[x,y]))%6]
                 for x,y in itertools.product(range(6), repeat=2)),
                np.zeros(2,dtype=np.int64))
        assert np.all(v%6 == 0)
        c,d = v//6
        e,f = units[(l*k+n*m)%6]
        value = (e*c-f*d, e*d+f*c+f*d)
        assert value in [tuple(u) for u in units]
        a[k,l,m,n], b[k,l,m,n] = value
    return a,b

def invariant(a,b):
    labels = [[4*l+i for l in range(4)] for i in range(4)]
    labels += [[4*l+perms[l][i] for l in range(4)] for i in range(4)]
    expr = ','.join(''.join(oe.get_symbol(v) for v in ds) for ds in labels)+'->'
    ac,bc = conj(a,b)
    work = [(a,b)]*4+[(ac,bc)]*4
    _,info = oe.contract_path(expr,*([a]*8),optimize='auto-hq')
    for ids,_,eq,_,_ in info.contraction_list:
        assert len(ids) == 2
        (a,b),(c,d) = [work.pop(i) for i in ids]
        ac = oe.contract(eq,a,c,optimize=False)
        bd = oe.contract(eq,b,d,optimize=False)
        ad = oe.contract(eq,a,d,optimize=False)
        bc = oe.contract(eq,b,c,optimize=False)
        work.append((ac-bd,ad+bc+bd))
    assert len(work) == 1 and int(work[0][1]) == 0
    return Fraction(int(work[0][0]),36**8)

expected = [Fraction(35,419904),Fraction(79,839808),Fraction(1,15552)]
axes_list = [(0,1,2,3),(0,2,1,3),(0,3,2,1)]
for j in range(3):
    a,b = make_h(j)
    for axes in axes_list:
        x = a.transpose(axes).reshape(36,36)
        y = b.transpose(axes).reshape(36,36)
        c,d = conj(x.T,y.T)
        g,h = mm(x,y,c,d)
        assert np.array_equal(g,36*np.eye(36,dtype=np.int64)) and not np.any(h)
    assert invariant(a,b) == expected[j]
    print('fixed invariant',j+1,expected[j])

mask = np.zeros((36,36),dtype=np.int64)
mask[[1,13,25],:] = [0,1,0,0,1,0,0,0,1,0,0,1,1,0,0,1,0,0,
                     0,1,0,0,1,0,0,0,1,0,0,1,1,0,0,1,0,0]
a,b = make_h(2)
for index,axes in enumerate(axes_list):
    x = a.transpose(axes).reshape(36,36)
    y = b.transpose(axes).reshape(36,36)
    m = mask.reshape((6,)*4).transpose(axes).reshape(36,36)
    parts = [(x*(1-m),y*(1-m)),(x*m,y*m)]
    coeff = {k:(np.zeros((36,36),np.int64),np.zeros((36,36),np.int64))
             for k in (-1,0,1)}
    for k,(x,y) in enumerate(parts):
        for l,(v,w) in enumerate(parts):
            v,w = conj(v.T,w.T)
            value = mm(x,y,v,w)
            coeff[k-l] = tuple(u+v for u,v in zip(coeff[k-l],value))
    coeff[0] = (coeff[0][0]-36*np.eye(36,dtype=np.int64),coeff[0][1])
    poly = {k:np.zeros(2,np.int64) for k in range(-2,3)}
    for k,(x,y) in coeff.items():
        for l,(v,w) in coeff.items():
            v,w = conj(v,w)
            poly[k-l] += [np.sum(x*v-y*w),np.sum(x*w+y*v+y*w)]
    assert all(v[1] == 0 for v in poly.values())
    values = [Fraction(int(poly[k][0]),36**2) for k in range(-2,3)]
    target = [Fraction(0)]*5 if index == 0 else [0,Fraction(-17,12),Fraction(17,6),Fraction(-17,12),0]
    assert values == target
    print('Laurent coefficients',index,values)
```
