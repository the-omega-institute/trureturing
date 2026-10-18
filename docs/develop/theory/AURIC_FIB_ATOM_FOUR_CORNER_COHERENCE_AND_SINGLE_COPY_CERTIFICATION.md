# Auric FIB-ATOM：四角相干的菱形—正方形几何与单份认证

## 116. 底面两因子与共同标签来源

**定义 C-116.1（载体、分割与继承记号）。** 沿用
[统计、相位与接缝续卷 C-94、C-96](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS_CONTINUATION.md#94-五模式混态底面张量结构与完整双副本测量)
的五模式空间 $\mathcal H_5$、底面投影 $P_{\mathrm b}$ 和等距嵌入 $\iota$：

$$
\Sigma=(0,1,2,3,13),\qquad
0=00,\quad1=10,\quad3=01,\quad13=11.
$$

对任意 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，记
$r=\operatorname{Tr}(P_{\mathrm b}\rho)$。当 $r>0$ 时，
$\sigma=\iota^\dagger\rho\iota/r$ 是归一化底面态。
以下在底面公式中省略 $\iota$，将底面恒等记为 $I_{\mathrm b}$；
嵌回五维后 $I_{\mathrm b}=P_{\mathrm b}$。
“底面可分离”始终相对于 $\mathbb C_A^2\mid\mathbb C_B^2$，
不把五维空间本身分解成两个量子位。
多份来源的“份间可分离”则相对于
$\mathcal H_5^{(1)}\mid\cdots\mid\mathcal H_5^{(N)}$。
其中底面 $A\mid B$ 不同于
[混态容量与认证续卷 C-105–C-115](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md#105-完整-product-plus-omega-菜单中的纠缠盲纤维与参数读口)
中的完整双份来源分割；本章份间分割在 $N=2$ 时就是
$\mathcal H_5^{(1)}\mid\mathcal H_5^{(2)}$，
但来源集合、允许操作及通道任务仍各按其自身定义。

取 $0<r<1$，固定

$$
\begin{aligned}
|e_0\rangle&=(|0\rangle+|3\rangle)/\sqrt2=|0\rangle_A|+\rangle_B,\\
|e_1\rangle&=(|1\rangle-|13\rangle)/\sqrt2=|1\rangle_A|-\rangle_B,\\
|G_\pm\rangle&=(|e_0\rangle\pm|e_1\rangle)/\sqrt2,\\
\rho_\pm&=(1-r)|2\rangle\langle2|+r|G_\pm\rangle\langle G_\pm|,\\
\sigma_0&=(|e_0\rangle\langle e_0|+|e_1\rangle\langle e_1|)/2,\\
\bar\rho&=(\rho_++\rho_-)/2=(1-r)|2\rangle\langle2|+r\sigma_0.
\end{aligned}
\tag{C116.1}
$$

这里 $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$。
$\sigma_0$ 是 C-96.1 在 $\nu=1/2$、$b_0=|+\rangle$、$b_1=|-\rangle$
和 $\gamma=0$ 的同一状态，而非另设相干族。

**命题 C-116.2（所有份数上的共同标签反例）。** 对每个 $N\ge2$，令

$$
\Gamma_N=\tfrac12\rho_+^{\otimes N}+\tfrac12\rho_-^{\otimes N}.
\tag{C116.2}
$$

这些来源置换不变、在完整五维份间完全可分离，且组成偏迹相容的族。
每个单份边缘都是 $\bar\rho$，其条件底面 $\sigma_0$ 可分离。
任取 $k$ 个不同位置，它们同时进入底面的概率都是 $r^k$。
然而任意两份在 C-94.3 的实际交换测量下满足

$$
\begin{array}{c|ccc}
\text{实际两份来源}&q_{--}&q_{-+}&
\Pr(\text{两份均在底面})\\ \hline
\Gamma_2&r^2/4&0&r^2\\
\bar\rho\otimes\bar\rho&r^2/8&r^2/8&r^2
\end{array}
\tag{C116.3}
$$

故相等边缘、可交换性、完整份间可分离性，甚至全部底面选择指示量的乘积律，
同时成立也不能推出实际来源为 iid 的 $\bar\rho$ 副本。

证明。每个张量幂均为份间乘积态，二项凸混合给完全可分离性；
置换保持每个张量幂。$\operatorname{Tr}\rho_\pm=1$ 给偏迹相容性和所列边缘。
两个 $e_j$ 都是底面乘积向量，给 $\sigma_0$ 的可分离分解。
在每个分支中，任意指定 $k$ 次底面投影的期望为 $r^k$；
对分支取平均不改变该数。底面与其补的任意指示模式同理有 Bernoulli 乘积律。

$G_\pm$ 的两侧约化态均为 $I_2/2$，底面纯度为一。
分别对实际乘积来源 $\rho_\pm\otimes\rho_\pm$ 使用 C-94.4，
给 $q_{--}=r^2/4$、$q_{-+}=0$；再用测量概率对来源的线性性得到第一行。
$\sigma_0$ 的两个约化态仍为 $I_2/2$，而
$\operatorname{Tr}\sigma_0^2=1/2$，所以对真正的
$\bar\rho\otimes\bar\rho$ 使用同一定理得到第二行。
$r>0$ 时两个测量概率不同，故两个来源不同。证毕。

本命题的来源限定消费 Mintert–Buchleitner，
*An observable entanglement measure for mixed quantum states*，
[quant-ph/0605250v3](https://arxiv.org/abs/quant-ph/0605250v3)，式 (1)–(3)
及末段明确的实际 $\rho\otimes\rho$ 前提；共同未知参数的区分见 van Enk，
*Can measuring entanglement be easy?*，
[quant-ph/0606017v1](https://arxiv.org/abs/quant-ph/0606017v1)，式 (3)–(4)。
共同参数混合一般不等于平均态的张量幂是成熟前置；
(C116.1)–(C116.3) 将它接到本库指定的五模式、固定对角及交换事件。
C-94 与 C-98 的乘积来源条件仍分别保留在其原结论中。

## 117. 原占位基中的固定对角实投影

**定义 C-117.1（两个底面读数）。** 在五模式上定义自伴算子

$$
\begin{aligned}
K_1&=|0\rangle\langle1|+|1\rangle\langle0|
-|3\rangle\langle13|-|13\rangle\langle3|
=\iota(X_A\otimes Z_B)\iota^\dagger,\\
K_2&=|0\rangle\langle3|+|3\rangle\langle0|
-|1\rangle\langle13|-|13\rangle\langle1|
=\iota(Z_A\otimes X_B)\iota^\dagger.
\end{aligned}
\tag{C117.1}
$$

两者在 $|2\rangle$ 上为零。这里 $X,Y,Z$ 为 Pauli 算子，
区别于 C-94 的占位均值 $X,Y,Z$ 时加下标标明因子。
设 $C_{ij}=\langle j|\rho|i\rangle$，对 $r>0$ 定义

$$
\begin{aligned}
u&=\operatorname{Tr}(\sigma X_A\otimes Z_B)
=\frac2r\operatorname{Re}(C_{01}-C_{3,13}),\\
v&=\operatorname{Tr}(\sigma Z_A\otimes X_B)
=\frac2r\operatorname{Re}(C_{03}-C_{1,13}).
\end{aligned}
\tag{C117.2}
$$

**定理 C-117.2（同一完整对角上的正方形与菱形）。**
任意底面态在 $(u,v)$ 平面的像恰为 $[-1,1]^2$；
底面可分离态的像恰为 $|u|+|v|\le1$。
对于每个固定 $0<r<1$，这两个完整投影区域仍能分别在同一五模式对角

$$
p^{(r)}=(r/4,r/4,1-r,r/4,r/4)
\tag{C117.3}
$$

上达到。它们是读数映射的像，不是全部密度态空间或可分离态空间的识别。

证明。由 Pauli 反对易关系
$XZ=-iY$、$ZX=iY$，两个局部负号抵消，故

$$
K_1^2=K_2^2=P_{\mathrm b},\qquad
K_1K_2=K_2K_1=\iota(Y_A\otimes Y_B)\iota^\dagger.
\tag{C117.4}
$$

因此每个条件期望均在 $[-1,1]$。
为在原占位基中给出全部达到态，取 $s,t\in\{-1,1\}$，置

$$
\begin{aligned}
|G_{st}\rangle&=(|0\rangle+s|1\rangle+t|3\rangle-st|13\rangle)/2,\\
\Pi_{st}&=\tfrac14(P_{\mathrm b}+sK_1)(P_{\mathrm b}+tK_2)
=|G_{st}\rangle\langle G_{st}|.
\end{aligned}
\tag{C117.5}
$$

直接逐项作用得 $K_1G_{st}=sG_{st}$、$K_2G_{st}=tG_{st}$。
四个向量归一且互相正交，故右侧确为四个秩一联合谱投影；
每个在原底角 $0,1,3,13$ 上的对角均为 $1/4$。
给定任意 $(u,v)\in[-1,1]^2$，令

$$
q_{st}=\frac{(1+su)(1+tv)}4,\qquad
\sigma(u,v)=\sum_{s,t}q_{st}|G_{st}\rangle\langle G_{st}|.
\tag{C117.6}
$$

权重非负、和一，并有 $\sum s q_{st}=u$、$\sum t q_{st}=v$。
因此该态达到读数且原占位对角均匀。

对一个乘积底面态，设两侧 Bloch 向量为
$(x_A,y_A,z_A)$、$(x_B,y_B,z_B)$，各自 Euclidean 范数不超过一。
于是 $u=x_Az_B$、$v=z_Ax_B$，Cauchy–Schwarz 给

$$
|u|+|v|\le
\sqrt{x_A^2+z_A^2}\sqrt{z_B^2+x_B^2}\le1.
\tag{C117.7}
$$

凸混合及三角不等式将此界推广到所有可分离态。
反向令 $\sigma_{j,\varepsilon}=(I_{\mathrm b}+\varepsilon K_j)/4$
（此处 $K_j$ 限于底面），$\varepsilon=\pm1$。
例如以 $P_L^\pm=(I\pm L)/2$ 记局部谱投影，有

$$
\begin{aligned}
\sigma_{1,\varepsilon}
&=\tfrac12(P_X^\varepsilon\otimes P_Z^+
+P_X^{-\varepsilon}\otimes P_Z^-),\\
\sigma_{2,\varepsilon}
&=\tfrac12(P_Z^+\otimes P_X^\varepsilon
+P_Z^-\otimes P_X^{-\varepsilon}).
\end{aligned}
\tag{C117.8}
$$

它们分别达到 $(\varepsilon,0)$ 与 $(0,\varepsilon)$，可分离且原占位对角均匀。
任意菱形点可取这些顶点和 $I_{\mathrm b}/4$ 的凸组合，
例如权重 $|u|,|v|,1-|u|-|v|$，符号按非零读数选择。
最后将每个构造嵌入
$\rho=(1-r)|2\rangle\langle2|+r\sigma$，便给 (C117.3)。证毕。

两生成元线性见证 $I-X_AZ_B-Z_AX_B$ 消费 Tóth–Gühne，
*Entanglement Detection in the Stabilizer Formalism*，
[quant-ph/0501020v2](https://arxiv.org/abs/quant-ph/0501020v2)，式 (35)–(36)
的 $N=2$ 情形。相关几何的成熟前置亦见 Horodecki–Horodecki，
*Information-theoretic aspects of quantum inseparability of mixed states*，
[quant-ph/9607007v1](https://arxiv.org/abs/quant-ph/9607007v1)，Propositions 3–4
的 Bell 对角四面体和可分离八面体。这里的固定对角达到性由 (C117.5)–(C117.8)
在原占位基中证明，不以局部 Clifford 换基后的对角性质代替。

**推论 C-117.3（固定概率圆与非平凡相干读数并存）。**
对 (C117.3) 的全部达到态，C-94 的均值及隐藏概率都是

$$
X=Y=r/2,\qquad Z=1-r,\qquad\kappa=r/4,\qquad
r\kappa-XY=0,\qquad
\eta=\frac18\log\frac{p_0p_{13}}{p_1p_3}=0.
\tag{C117.9}
$$

因此原概率关联椭圆始终满足其圆条件，而相干实读数仍可遍历整个正方形。

证明。将 (C117.3) 代入 C-94.1 和 C-84.7 即得。
$\eta$ 只依赖对角，不能区别定理 C-117.2 的不同非对角达到态；
概率圆条件没有将混态集合或它的读数像变成一个圆。证毕。

## 118. 复读数与精确的占位相位群

**定义 C-118.1（理想复期望）。** 对 $r>0$ 令

$$
a=\frac2r(C_{01}-C_{3,13}),\qquad
b=\frac2r(C_{03}-C_{1,13}).
\tag{C118.1}
$$

于是 $u=\operatorname{Re}a$、$v=\operatorname{Re}b$。
这里 $a,b$ 为状态的精确复期望，不是有限样本模长估计。

**定理 C-118.2（双复圆盘、复菱形与固定对角达到性）。**
全部底面态的 $(a,b)$ 像恰为
$\{(a,b)\in\mathbb C^2:|a|\le1,|b|\le1\}$；
全部可分离底面态的像恰为
$\{(a,b):|a|+|b|\le1\}$。
两者仍能在每个 (C117.3) 的固定完整对角上达到。
因此

$$
2\bigl(|C_{01}-C_{3,13}|+|C_{03}-C_{1,13}|\bigr)>r
\tag{C118.2}
$$

足以排除底面可分离性。

证明。对任意实 $\phi$，算子
$(\cos\phi X_A+\sin\phi Y_A)\otimes Z_B$ 的算子范数为一，
其在 $\sigma$ 中的期望为 $\operatorname{Re}(e^{-i\phi}a)$。
取相位使该实部为 $|a|$，得到 $|a|\le1$；交换两因子得到 $|b|\le1$。
对乘积态直接由矩阵元得到

$$
a=(x_A+iy_A)z_B,\qquad b=z_A(x_B+iy_B).
\tag{C118.3}
$$

故

$$
|a|+|b|\le
\sqrt{x_A^2+y_A^2+z_A^2}\,
\sqrt{z_B^2+x_B^2+y_B^2}\le1,
\tag{C118.4}
$$

其中应用二维 Cauchy–Schwarz 于
$(\sqrt{x_A^2+y_A^2},|z_A|)$ 和
$(|z_B|,\sqrt{x_B^2+y_B^2})$。
三角不等式及凸性给可分离混态的同一界。

为了达到任意目标，先用 C-117.2 达到实非负读数 $(|a|,|b|)$，
再主动施加底面局部对角酉

$$
U_{\varphi,\psi}
=\operatorname{diag}(1,e^{i\varphi})_A\otimes
\operatorname{diag}(1,e^{i\psi})_B.
\tag{C118.5}
$$

在固定的原占位读数下，该态变换使
$a\mapsto e^{i\varphi}a$、$b\mapsto e^{i\psi}b$，
并保持每个占位对角以及可分离性。
选 $\varphi=\arg a$、$\psi=\arg b$；目标为零时相应相位任取。
这同时证明全态与可分离态的反向包含和固定对角达到性。
(C118.2) 就是可分离界的逆否命题。证毕。

**命题 C-118.3（固定读数下模长和不变的最大对角相位群）。**
设 $D=\sum_{j\in\Sigma}e^{i\theta_j}|j\rangle\langle j|$，
主动变换 $\rho\mapsto D\rho D^\dagger$，保持 (C117.1)、(C118.1) 的读数定义不变。
对于所有 $r>0$ 的五模式态均保持 $|a|+|b|$ 的对角酉恰满足

$$
\theta_0+\theta_{13}=\theta_1+\theta_3\pmod{2\pi},
\qquad\theta_2\text{ 任意}.
\tag{C118.6}
$$

该条件下，底面限制恰为共同相位乘一个局部对角酉，且

$$
a\longmapsto e^{i(\theta_1-\theta_0)}a,\qquad
b\longmapsto e^{i(\theta_3-\theta_0)}b.
\tag{C118.7}
$$

证明。主动对角共轭使
$C_{ij}\mapsto e^{i(\theta_j-\theta_i)}C_{ij}$。
(C118.6) 恰使 $C_{01},C_{3,13}$ 具有相同相因子，
也使 $C_{03},C_{1,13}$ 具有相同相因子，给 (C118.7)。
底面酉此时为
$e^{i\theta_0}\operatorname{diag}(1,e^{i(\theta_1-\theta_0)})_A
\otimes\operatorname{diag}(1,e^{i(\theta_3-\theta_0)})_B$。

为证必要性，取底面乘积向量
$|+\rangle_A|+\rangle_B=(|0\rangle+|1\rangle+|3\rangle+|13\rangle)/2$，
其 $a=b=0$。令
$\delta=\theta_0+\theta_{13}-\theta_1-\theta_3$，
共轭后由四个振幅直接得

$$
a'=\tfrac12e^{i(\theta_1-\theta_0)}(1-e^{i\delta}),\qquad
b'=\tfrac12e^{i(\theta_3-\theta_0)}(1-e^{i\delta}).
\tag{C118.8}
$$

所以 $|a'|+|b'|=2|\sin(\delta/2)|$，
要保持原来的零值必须 $\delta=0\bmod2\pi$。
可在 $|2\rangle$ 加质量 $1-r$ 得任意 $0<r<1$ 的同一反例。
$\theta_2$ 不进入底面矩阵元，故完全自由。证毕。

**命题 C-118.4（主动作用与被动换基的边界）。**
命题 C-118.3 比较固定 $\iota,K_1,K_2$ 下的不同状态。
若改为被动换基，则状态、读数和底面张量识别均须按同一坐标规则运输，
迹配对保持不变；任意被动基变换的这一事实不扩大 (C118.6) 的主动相位群。

证明。若 $W$ 将新坐标送入旧坐标，则被动表示为
$\rho'=W^\dagger\rho W$、$K_j'=W^\dagger K_jW$、
$\iota'=W^\dagger\iota$，于是
$\operatorname{Tr}(\rho'K_j')=\operatorname{Tr}(\rho K_j)$，且
$\iota'^\dagger\rho'\iota'=\iota^\dagger\rho\iota$。
主动作用固定读数时，必要条件已经由 (C118.8) 给出。
例如固定读数下 $\theta_{13}=\pi$、其余底角相位为零，
把上面的乘积向量送到 $G_{++}$；其 $a=b=1$。
该态的系数矩阵有行列式 $-1/2$，故 concurrence 为一。
这一非局部主动相位作用改变了底面纠缠及读数，不能当作保持原张量任务的相位重标记。证毕。

## 119. 固定复读数的尖锐 concurrence 包络

**定理 C-119.1（原对角上的精确最小值）。**
采用 C-96.3 的两量子位凸屋顶 concurrence $\mathcal C$。
对每个 $|a|,|b|\le1$，所有具有这些复读数的底面态满足

$$
\mathcal C(\sigma)\ge\max\{0,|a|+|b|-1\},
\tag{C119.1}
$$

且最小值恰为右端。
即使再要求底面原占位对角全为 $1/4$，最小值仍相同；
五模式实现因而可保持 (C117.3) 的每个概率。

证明。局部酉保持纯态的 $2|\det B|$，且双向运输全部纯态分解，
所以保持其凸屋顶。使用 (C118.5) 将读数转为
$s=|a|\ge0$、$t=|b|\ge0$ 即可。
令 $G=G_{++}$，则在底面联合本征基中直接有算子不等式

$$
|G\rangle\langle G|\succeq(K_1+K_2)/2.
\tag{C119.2}
$$

四个本征位置的左、右值依次为 $(1,1),(0,0),(0,0),(0,-1)$。
又 $G$ 是最大纠缠向量，因为其系数矩阵
$\tfrac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ 的两奇异值均为 $1/\sqrt2$。
若归一化纯态 $\phi$ 的系数矩阵奇异值为 $d_1,d_2$，
则 $d_1^2+d_2^2=1$、$\mathcal C(\phi)=2d_1d_2$。
在其 Schmidt 基下，最大纠缠向量的每个矩阵元模不超过 $1/\sqrt2$，
故三角不等式给

$$
|\langle G|\phi\rangle|^2
\le\tfrac12(d_1+d_2)^2=\frac{1+\mathcal C(\phi)}2.
\tag{C119.3}
$$

对 $\sigma$ 的任意纯态分解取平均，再取凸屋顶下确界，得到
$2\langle G|\sigma|G\rangle-1\le\mathcal C(\sigma)$。
与 (C119.2) 合并给 $s+t-1\le\mathcal C(\sigma)$；非负性给 (C119.1)。

为达到下界，沿用 C-117.2 的
$\sigma_1=(I_{\mathrm b}+K_1)/4$、$\sigma_2=(I_{\mathrm b}+K_2)/4$。
若 $s+t\le1$，取

$$
\sigma_*=s\sigma_1+t\sigma_2+(1-s-t)I_{\mathrm b}/4.
\tag{C119.4}
$$

其读数为 $(s,t)$，且可分离，所以 concurrence 为零。
若 $s+t>1$，令 $\ell=s+t-1$，取

$$
\sigma_*=\ell|G\rangle\langle G|+(1-t)\sigma_1+(1-s)\sigma_2.
\tag{C119.5}
$$

三个权重非负且和一，读数分别合成为
$\ell+1-t=s$、$\ell+1-s=t$。
凸屋顶的凸性及 $\mathcal C(G)=1$ 给 $\mathcal C(\sigma_*)\le\ell$，
恰与下界相等。所有分量都在原占位基中对角均匀；
最后用局部对角酉恢复目标复相位，保留对角与 concurrence。证毕。

此处使用的凸屋顶定义及一般两量子位 concurrence 来源为 Wootters，
*Entanglement of Formation of an Arbitrary State of Two Qubits*，
[quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (7)、(10)、(19)–(22)，
亦见[本库文献注](../../../Library/QuantumStates/wootters1998formationfunction.md)。
从有限见证期望求相容态上的最小纠缠量是成熟方法：Gühne–Reimpell–Werner，
*Estimating entanglement measures in experiments*，
[quant-ph/0607163v2](https://arxiv.org/abs/quant-ph/0607163v2)，式 (1)–(4)；
Eisert–Brandão–Audenaert，*Quantitative entanglement witnesses*，
[quant-ph/0607167v4](https://arxiv.org/abs/quant-ph/0607167v4)，节 “Paradigm of quantitative tests”。
本条的 repo-derived 综合将这些成熟结构用于指定复读数和原占位固定对角的共同约束；
(C119.4)–(C119.5) 是该约束下的显式达到态。
所引凸屋顶及定量见证方法为 literature-attested 中间结构；
该归属不将本综合表述为文献全域中的原创性定理。

**命题 C-119.2（复菱形内仍有纠缠态）。** 底面纯态

$$
|\psi\rangle=(|0\rangle+|1\rangle+|3\rangle+e^{i\pi/3}|13\rangle)/2
\tag{C119.6}
$$

满足 $\mathcal C(\psi)=1/2$ 而 $|a|+|b|=1$。
因此复菱形成员资格只说明存在相同读数的可分离态，不能认证实际态可分离。

证明。系数矩阵的行列式为 $(e^{i\pi/3}-1)/4$，
其模为 $1/4$，纯态 concurrence 因而为 $1/2$。
直接按 (C118.1) 有 $a=b=(1-e^{i\pi/3})/2$，各自模为 $1/2$。
由 C-118.2 确有相同复读数的可分离达到态。证毕。

## 120. 已有相干族的线性读口

**推论 C-120.1（C-96 中心族的同对角读数）。**
在 C-96.1 中取 $\nu=1/2$、$b_0=|+\rangle$、$b_1=|-\rangle$，
保持其原参数 $0\le\gamma\le1$。则同一个族满足

$$
a(\sigma_\gamma)=\gamma,\qquad b(\sigma_\gamma)=1,
\qquad\mathcal C(\sigma_\gamma)=\gamma,
\qquad\operatorname{diag}\rho_\gamma=p^{(r)}.
\tag{C120.1}
$$

C-94 实际双份乘积测量的旧对照与单份线性读数分别为

$$
q_{--}-q_{-+}=\frac{r^2\gamma^2}{4},\qquad
\operatorname{Tr}\rho_\gamma(K_1+K_2-P_{\mathrm b})=r\gamma.
\tag{C120.2}
$$

证明。$K_1e_0=e_1$、$K_1e_1=e_0$，而 $K_2e_j=e_j$。
将 C-96.1 的二阶支撑矩阵代入，即得实读数 $\gamma,1$；
所有振幅取实，故虚部为零。
对角与 concurrence 直接分别应用 C-96.2 和 C-96.3，
后者在 $\nu=1/2$ 给 $\mathcal C=2\gamma\sqrt{1/4}=\gamma$。
同样直接应用 C-96.2 的 $h=r^2/4$ 给第一个对照式；
第二个由线性期望及底面质量 $r$ 得到。
此处的线性与二次响应比较限定在同一个已给相干族及各自实际读口上。证毕。

## 121. 每轮一份的历史条件认证

**假设 C-121.1（实际投影测量、设置独立性与条件零假设）。**
令 $\mathcal F_{n-1}$ 包含第 $n$ 轮前全部已观察历史及过去随机设置。
给定该历史，第 $n$ 轮的一份五模式状态 $\rho_n$ 在当前设置选择前已经固定。
允许它随历史变化，不要求跨轮独立同分布。
随后以独立于当前来源、给定历史后仍均匀的随机数
$J_n\in\{1,2\}$ 选择并实际执行可信的三结果 PVM

$$
E_{j,+}=(P_{\mathrm b}+K_j)/2,\qquad
E_{j,-}=(P_{\mathrm b}-K_j)/2,\qquad
E_{j,0}=I_5-P_{\mathrm b}.
\tag{C121.1}
$$

给定历史与设置，结果概率恰为
$\operatorname{Tr}(\rho_nE_{j,o})$。
这些实际效果及其 Born 概率是本假设的一部分，不能由线性算子的存在
推得某个未指定的原生 instrument 已经提供该测量。
由 (C117.4)，三个效果是正交投影且和为 $I_5$，所以确为数学上的 PVM。

零假设为：几乎处处对每个观察历史，若
$r_n=\operatorname{Tr}(P_{\mathrm b}\rho_n)>0$，
则当前条件底面态 $\sigma_n=\iota^\dagger\rho_n\iota/r_n$ 可分离。
$r_n=0$ 时不定义条件底面态；该轮以概率一产生结果 $0$。
本假设允许 $r_n=1$ 及合法零占位概率。

**定义 C-121.2（全轮计数与固定线性得分）。**
在观察结果前固定 $0<\lambda<1/3$、$0<\alpha<1$。
每轮一份来源、一次所选 PVM，令

$$
V_n=\begin{cases}
1,&\text{结果 }+,\\
-3,&\text{结果 }-,\\
0,&\text{结果 }0,
\end{cases}
\qquad
E_0=1,\quad E_N=\prod_{n=1}^N(1+\lambda V_n),
\tag{C121.2}
$$

$$
\tau=\inf\{N\ge1:E_N\ge1/\alpha\},\qquad\inf\varnothing=+\infty.
\tag{C121.3}
$$

$N$ 计入全部轮次，包括所有非底面及零得分轮次。
“单份”指每轮只消费一份，不表示整个认证仅观察一个样本。

**定理 C-121.3（历史条件零假设下的随时误判界）。**
在假设 C-121.1 下，(C121.2) 是非负超鞅，并满足

$$
\Pr(\exists N\ge1:E_N\ge1/\alpha)\le\alpha.
\tag{C121.4}
$$

这一结论无需轮内成对输入或跨轮 iid。

证明。给定历史，平均两个等概率设置的正、负概率得到

$$
\begin{aligned}
\Pr(V_n=1\mid\mathcal F_{n-1})
&=\frac{r_n}{2}+\frac14\operatorname{Tr}\rho_n(K_1+K_2),\\
\Pr(V_n=-3\mid\mathcal F_{n-1})
&=\frac{r_n}{2}-\frac14\operatorname{Tr}\rho_n(K_1+K_2),\\
\mathbb E[V_n\mid\mathcal F_{n-1}]
&=\operatorname{Tr}\rho_n(K_1+K_2)-r_n\le0.
\end{aligned}
\tag{C121.5}
$$

$r_n>0$ 时最后一步用 C-117.2 的可分离界 $u_n+v_n\le1$；
$r_n=0$ 时压缩为零，等式右端和得分均为零。
每个乘因子位于 $[1-3\lambda,1+\lambda]$，严格为正。
有限 $N$ 时 $E_N\le(1+\lambda)^N$ 可积，且条件期望不超过 $E_{N-1}$。

为直接证明全时间界，固定有限整数 $m$，逐步条件期望给
$\mathbb E E_{\tau\wedge m}\le E_0=1$。
具体每一步的差为
$\mathbf1_{\{\tau\ge n\}}(E_n-E_{n-1})$，
其中指标在第 $n-1$ 轮后已可知，所以其期望非正。
在 $\{\tau\le m\}$ 上停止值至少 $1/\alpha$，其余路径非负，故

$$
\Pr(\tau\le m)\le\alpha\,\mathbb E E_{\tau\wedge m}\le\alpha.
\tag{C121.6}
$$

令 $m\uparrow\infty$，事件单调收敛即得 (C121.4)。
整个论证只使用有限停止和非负性，没有预设 $\tau$ 有限或可积。证毕。

本条消费 Ville 的非负超鞅最大不等式，见 Howard–Ramdas–McAuliffe–Sekhon，
*Time-uniform Chernoff bounds via nonnegative supermartingales*，
[1808.03204v8](https://arxiv.org/abs/1808.03204v8)，Lemma 1、式 (2.11)，
及[本库文献注](../../../Library/Dynamics/howard2020timeuniform.md)。
本应用的五模式 PVM、得分和条件可分离零假设由 (C121.1)–(C121.5) 指定。

**命题 C-121.4（线性检验与理想复判据的区别）。**
固定 (C121.1)–(C121.2) 的单轮正平均得分条件是 $u+v>1$；
它不同于 $|a|+|b|>1$。例如 $G_-$ 满足
$(a,b)=(-1,1)$，理想复判据严格违反可分离界，
但固定线性得分的平均值为 $-r$。

证明。均值公式是 (C121.5)。
由 $K_1G_-=-G_-$、$K_2G_-=G_-$ 得所列读数与平均值。
因此有限数据的规则针对预定线性读口；
它没有将未知复期望的模长替换为未经风险控制的样本模长。
主动调相若用于另一规则，须另给相应选择与风险合同。证毕。

**命题 C-121.5（无条件边缘可分离不足以替代历史条件）。**
(C116.2) 可给每轮无条件边缘均为 $\bar\rho$ 的相容来源，
但在 (C121.1) 的观察历史下，未来条件底面可以是最大纠缠的 $G_+$ 或 $G_-$。

证明。先等概率选择共同标签 $S=\pm$，然后按该标签给出条件乘积来源。
未观察时每轮边缘都是 $\bar\rho$，其底面 $\sigma_0$ 可分离。
在第一轮事件 $\{J_1=1,\text{结果 }+\}$ 上，
$K_1$ 的本征值使标签只能为 $+$；此事件概率为 $r/4>0$。
未来各轮的条件来源因而为 $\rho_+$，底面为 $G_+$。
负结果同理给标签 $-$。
这已违反 C-121.1 的历史条件零假设，虽未违反无条件边缘可分离性。

因此，(C121.4) 的越界结论是在指定实际 PVM 与设置独立性下拒绝
“每个观察历史后的当前底面均可分离”这一全轮合同。
若另有固定 iid 状态前提，该合同的否定认证该固定底面纠缠；
对自适应或相关来源，不能据此将某个固定初始边缘判为纠缠。证毕。

## 122. 固定 iid 相干族上的成本及同族比较

**假设 C-122.1（成本所需的固定来源与相位）。**
除 C-121.1 的实际测量和独立均匀设置外，每轮实际输入独立同分布的
C-120.1 状态 $\rho_\gamma$，相对于固定读数具有已校准的实非负相位。
固定 $r\in(0,1)$ 及最低相干 $g=\gamma_0\in(0,1)$，
承诺 $\gamma\in[g,1]$，在数据之前选 $\lambda=g/3$。
固定 $\alpha\in(0,1)$，令 $A=\log(1/\alpha)$；以下均为自然对数。
这是假设于有功效来源的成本结论，不把纠缠来源作为 C-121.1 的可分离零假设。

**定理 C-122.2（有限停止给出的平均单份成本界）。**
在假设 C-122.1 下，设

$$
d_{\mathrm s}(g)=\frac{3+g}{4}\log(1+g/3)
+\frac{1-g}{4}\log(1-g).
\tag{C122.1}
$$

则 $d_{\mathrm s}(g)>0$，且 (C121.3) 的停止时刻满足

$$
\mathbb E\tau\le B_{\mathrm s}(r,g,\alpha)
:=\frac{A+\log(1+g/3)}{r\,d_{\mathrm s}(g)}<\infty.
\tag{C122.2}
$$

$\tau$ 既是全部轮数，也是实际制备份数。

证明。由 C-120.1 与 (C121.5)，得分 iid 且分布为

$$
\Pr(V=1)=\frac{r(3+\gamma)}4,\qquad
\Pr(V=-3)=\frac{r(1-\gamma)}4,\qquad
\Pr(V=0)=1-r.
\tag{C122.3}
$$

令 $Y_n=\log(1+(g/3)V_n)$、$S_N=\sum_{n=1}^NY_n=\log E_N$，
则 $\log(1-g)\le Y_n\le b_g:=\log(1+g/3)$，并且

$$
\begin{aligned}
\mu:=\mathbb E Y_n
&=r\,d_{\mathrm s}(g)
+\frac{r(\gamma-g)}4\log\frac{1+g/3}{1-g}
\ge r\,d_{\mathrm s}(g),\\
d_{\mathrm s}(0)&=0,\qquad
d_{\mathrm s}'(g)=\tfrac14\log\frac{1+g/3}{1-g}>0.
\end{aligned}
\tag{C122.4}
$$

故 $\mu>0$。先只在有限 $m$ 上停止：

$$
S_{\tau\wedge m}=\sum_{n=1}^mY_n\mathbf1_{\{\tau\ge n\}},\qquad
\mathbb E S_{\tau\wedge m}=\mu\,\mathbb E(\tau\wedge m).
\tag{C122.5}
$$

此等式由有限求和、$Y_n$ 与过去的独立性及
$\{\tau\ge n\}\in\mathcal F_{n-1}$ 得到。
若 $\tau\le m$，首次越界前 $S_{\tau-1}<A$，故
$S_\tau<A+b_g$；若 $\tau>m$，则 $S_m<A$。
所以在所有路径上 $S_{\tau\wedge m}\le A+b_g$，进而

$$
\mathbb E(\tau\wedge m)\le\frac{A+b_g}{\mu}
\le\frac{A+b_g}{r\,d_{\mathrm s}(g)}.
\tag{C122.6}
$$

对非负停止时间使用单调收敛，得到 (C122.2)，同时证明有限均值及几乎必然停止。
没有对尚未证明可积的无界停止时间使用可选停止或 Wald 恒等式。证毕。

**推论 C-122.3（小相干的明确渐近范围）。** 当 $g\downarrow0$ 时，

$$
d_{\mathrm s}(g)=\frac{g^2}{6}+\frac{g^3}{27}+O(g^4).
\tag{C122.7}
$$

固定 $\alpha\in(0,1)$ 时，所构造单份规则满足
$\mathbb E\tau=O(\log(1/\alpha)/(r g^2))$。
该上界对 $0<\alpha\le\alpha_*<1$ 一致成立，常数可依赖 $\alpha_*$；
不声明对无限制的 $\alpha\uparrow1$ 一致。

证明。由 (C122.4) 逐项微分，
$d_{\mathrm s}''(g)=1/((3+g)(1-g))$，
所以 $d_{\mathrm s}''(0)=1/3$、$d_{\mathrm s}'''(0)=2/9$。
在任意 $[0,g_*]$、$g_*<1$ 上，四阶导数有界，Taylor 余项给 (C122.7)。
又 $d_{\mathrm s}''(g)\ge1/3$，积分两次给
$d_{\mathrm s}(g)\ge g^2/6$，且 $b_g\le g/3$。
若 $A\ge\log(1/\alpha_*)>0$，则
$A+b_g\le A(1+1/(3\log(1/\alpha_*)))$，代入 (C122.2) 即得一致范围。
例如 $\alpha=e^{-g^4}$ 时所述大 $O$ 右端趋零而 $\tau\ge1$，
故不能去掉风险范围限制。证毕。

**命题 C-122.4（同一家族上两个指定规则的理论上界值）。**
对同一个 C-120.1 家族，另用
[混态容量与认证续卷 C-98–C-99](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md#99-相干承诺下的有限平均认证成本)
的双份规则：每轮实际给 $\rho_\gamma\otimes\rho_\gamma$，
跨轮 iid，固定 $\lambda_{\mathrm p}=g^2$、同一风险 $\alpha$。
其 $w=r/2$，故 C-99.2 给成对轮数上界

$$
\begin{aligned}
d_{\mathrm p}(x)&=\frac{1+x}{2}\log(1+x)+\frac{1-x}{2}\log(1-x),\\
B_{\mathrm p}(r,g,\alpha)
&=\frac{A+\log(1+g^2)}{(r^2/4)d_{\mathrm p}(g^2)}.
\end{aligned}
\tag{C122.8}
$$

平均制备份数上界为 $2B_{\mathrm p}$；单份规则的对应上界为 $B_{\mathrm s}$。
固定 $r,\alpha$ 且 $g\downarrow0$，这两个界的渐近关系是

$$
B_{\mathrm s}\sim\frac{6A}{rg^2},\qquad
B_{\mathrm p}\sim\frac{8A}{r^2g^4},\qquad
\frac{B_{\mathrm s}}{2B_{\mathrm p}}\sim\frac{3r g^2}{8}.
\tag{C122.9}
$$

在 $r=4/5$、$\alpha=1/100$ 时，下表是这些公式值的近似显示：

| 最低相干 $g$ | 单份 $B_{\mathrm s}$ | 双份成对轮数 $B_{\mathrm p}$ | 双份制备份数 $2B_{\mathrm p}$ |
| --- | ---: | ---: | ---: |
| $1/2$ | $\approx123.328$ | $\approx955.453$ | $\approx1910.905$ |
| $1/4$ | $\approx527.885$ | $\approx14920.814$ | $\approx29841.628$ |

表格比较的是同一家族、所列来源与相位假设下两个指定规则的理论上界值。
它既不比较实际平均停止时间，也不推出全部允许测量中的全局最优性；
两项上界的大小顺序不单独决定实际均值的大小顺序。

证明。双份界直接应用 C-99.2，未重新定义其来源零假设。
C-99.3 给 $d_{\mathrm p}(g^2)=g^4/2+O(g^8)$，
而 (C122.7) 给单份分母的首项。
固定 $A>0$ 时两个分子的首项都是 $A$，除法得到 (C122.9)。

近似显示也可由有限有理区间导出：对任意正有理 $v$，令
$z=(v-1)/(v+1)$。有限项式

$$
L_m(v)=2\sum_{k=0}^{m-1}\frac{z^{2k+1}}{2k+1},\qquad
|\log v-L_m(v)|
\le\frac{2|z|^{2m+1}}{(2m+1)(1-z^2)}
\tag{C122.10}
$$

由 $\log v=2\operatorname{artanh}z$ 的幂级数和几何尾界给出。
对 $v=100,7/6,1/2,13/12,3/4,5/4,17/16,15/16$ 取 $m=2048$，
所有 $|z|\le99/101$，尾界均小于 $10^{-36}$。
将这些有理包络代入 (C122.1)、(C122.2)、(C122.8)，
分母下端均严格正，区间除法给

$$
\begin{array}{c|ccc}
g&B_{\mathrm s}&B_{\mathrm p}&2B_{\mathrm p}\\ \hline
1/2&(123.327996,123.327998)&(955.452630,955.452632)&(1910.905260,1910.905264)\\
1/4&(527.884597,527.884600)&(14920.814102,14920.814105)&(29841.628204,29841.628210)
\end{array}
\tag{C122.11}
$$

其中双份 $g=1/2$ 所需 $\log(3/4)$、$g=1/4$ 所需 $\log(15/16)$
已列在同一包络中。所有小数端点在此表示有限十进有理数，
上下端向外取整；表格只保留其近似值，精确成本界始终由公式决定。证毕。

## 追加锚（本行以下为增补区）

## 123. 全五维复输入上的原生 Ramsey 相干认证

**定义 C-123.1（同一原生载体、固定能量基与实际信号）。** 采用
[原生卷定义 55.1、假设 55.2](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#35-交替位置编码与单处固定相位) 及
[定义 68.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#48-固定初始五人口的全单纯形相位增益)
的整个 $\mathcal K_3$、无漂移独立翻转菜单及被动标架，
并采用其命题 59.1 另行允许的末次二值 PVM $\{n_1,I-n_1\}$。
本章起 $e_j$ 专指该卷的物理标准基，不沿用 (C116.1) 的派生向量名称：

$$
(e_0,e_1,e_2,e_3,e_4)=(|000\rangle,|100\rangle,|010\rangle,|001\rangle,|101\rangle),
\quad D=\operatorname{diag}(1,i,i,i,1),
\quad n_1=\operatorname{diag}(0,1,0,0,1).
\tag{C123.1}
$$

置 $P_3=|e_3\rangle\langle e_3|$、$P_C=I-P_3$、$C=\operatorname{ran}P_C$，并定义

$$
\begin{aligned}
\psi&=(e_0+e_4)/\sqrt2,& z&=(e_0-e_4)/\sqrt2,\\
A_1&=|e_1\rangle\langle e_0|-|e_0\rangle\langle e_1|,&
A_3&=|e_2\rangle\langle e_4|-|e_4\rangle\langle e_2|,\\
A&=A_1+3A_3,&R(t)&=e^{tA},\qquad H=iA,\\
O\psi&=e_1,\quad Oz=e_0,\quad Oe_1=e_2,&
Oe_2&=e_3,\quad Oe_3=-e_4,\\
W_{\rm ph}(t)&=DOR(t)D^\dagger,&
p_\rho(t)&=\operatorname{Tr}\bigl(n_1W_{\rm ph}(t)\rho W_{\rm ph}(t)^\dagger\bigr).
\end{aligned}
\tag{C123.2}
$$

这里 $A_1,A_3$ 是两个指定目标平面旋转，不是原生翻转生成元。
输入 $\rho$ 遍历全部五维复密度矩阵。$H$ 在 $C$ 上的固定本征向量为

$$
v_{1\pm}=(e_0\pm i e_1)/\sqrt2,\qquad
v_{3\pm}=(e_4\pm i e_2)/\sqrt2,
\qquad
\mathcal B=(Dv_{1+},Dv_{1-},Dv_{3+},Dv_{3-},e_3).
\tag{C123.3}
$$

相应物理谱模型 $H_{\rm ph}=DHD^\dagger$ 在 $\mathcal B$ 中的能量为
$(1,-1,3,-3,0)$。这个谱模型指定信号的数学参数，尚不表示安装了裸驱动。
记 $\operatorname{cn}_{\mathcal B}(\rho)\le3$ 当且仅当存在有限分解

$$
\rho=\sum_{a=1}^{N}q_a|\phi_a\rangle\langle\phi_a|,
\quad q_a\ge0,\quad\sum_aq_a=1,\quad\|\phi_a\|=1,
\quad\#\{b\in\mathcal B:\langle b|\phi_a\rangle\ne0\}\le3\quad(\forall a).
\tag{C123.4}
$$

这是同一个固定能量基中的混态 ensemble 条件，不是密度矩阵的逐项稀疏性。
沿用 [ThreeCoherenceRamseyThreshold 的定义 1.3–1.4、1.8–1.11 和定理 1.12](../../../Blueprint/D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.md)：

$$
M_q(p)=\frac1{2\pi}\int_0^{2\pi}p(t)^q\,dt,
\qquad R_3(p)=\frac{M_3(p)}{M_1(p)^2},
\qquad T=\frac{\operatorname{thresholdN}(\alpha)}{\operatorname{thresholdD}(\alpha)},
\quad \frac{6169}{5000}<\alpha<\frac{12339}{10000},
\quad\operatorname{thresholdP}(\alpha)=0,
\tag{C123.5}
$$

其中选择该定理所供应的一个 $\alpha$；$T$ 是其 `admissibleValues` 的最大元。

**定理 C-123.2（实际秩二读口的全空间阈值）。** 对每个五维复密度矩阵，令
$\lambda=\langle e_3|\rho|e_3\rangle$。则实际拉回效应及第一矩为

$$
\begin{aligned}
F(t)&=W_{\rm ph}(t)^\dagger n_1W_{\rm ph}(t)
=D\bigl[R(t)^T|\psi\rangle\langle\psi|R(t)+P_3\bigr]D^\dagger,\\
M_1(p_\rho)&=\frac{1+3\lambda}{4}\ge\frac14.
\end{aligned}
\tag{C123.6}
$$

若 (C123.4) 成立，则

$$
R_3(p_\rho)\le
\frac{16\lambda^3-12\lambda^2+12\lambda+T(1-\lambda)^3}{(1+3\lambda)^2}
\le T.
\tag{C123.7}
$$

因而 $R_3(p_\rho)>T$ 排除整个五维基 $\mathcal B$ 中的三相干 ensemble，
无需承诺 $\rho$ 支持于 $C$。结论限定于 (C123.2) 的实际协议。

证明。$O$ 把一组正交归一基送到另一组；
$(\psi,z,e_1,e_2,e_3)$ 与 $(e_1,e_0,e_2,e_3,-e_4)$ 的定向均为正，
所以 $O\in SO(5)$。读扇区 $\operatorname{span}(e_1,e_4)$ 的原像为
$\operatorname{span}(\psi,e_3)$，故 $O^Tn_1O=|\psi\rangle\langle\psi|+P_3$。
又 $R(t)$ 固定 $e_3$ 且保持 $C$，得到 (C123.6) 的效应式。
它在全载体上始终秩二，对 $C\oplus\mathbb Ce_3$ 分块对角；
跨块相干的实部、虚部均不进入迹配对。这是算符恒等式，不是对实际态执行去相干。

设 $\lambda<1$，置

$$
\sigma=D^\dagger\rho D,\qquad
\sigma_C=\frac{P_C\sigma P_C}{1-\lambda},\qquad
s(t)=\operatorname{Tr}\bigl(|\psi\rangle\langle\psi|R(t)\sigma_CR(t)^T\bigr).
\tag{C123.8}
$$

压缩正性与迹一给 $\sigma_C\in\mathsf D(C)$，而效应式给

$$
p_\rho(t)=\lambda+(1-\lambda)s(t),\qquad 0\le s(t)\le1.
\tag{C123.9}
$$

四个主动能量互异，$\langle v_{j\pm}|\psi\rangle=1/2$，
周期平均消去主动块的非对角项，所以 $M_1(s)=\operatorname{Tr}(\sigma_C)/4=1/4$。
这证明 (C123.6) 的均值式，未限制 $\rho$ 的复相干。

现在假设 (C123.4)。令 $u_a=P_CD^\dagger\phi_a$、$b_a=\|u_a\|^2$。
舍弃 $b_a=0$ 的项后有有限归一分解

$$
\sigma_C=\sum_{a:b_a>0}\frac{q_ab_a}{1-\lambda}
\left|\frac{u_a}{\sqrt{b_a}}\right\rangle
\left\langle\frac{u_a}{\sqrt{b_a}}\right|,
\qquad\sum_aq_ab_a=1-\lambda.
\tag{C123.10}
$$

$D^\dagger$ 将物理能量基运到被动能量基， inactive 坐标仅多一个相位；
$P_C$ 只删除该坐标。每个保留向量仍在同一四能量基中至多三稀疏，
每个范数为一，权重非负且和一。
在所引最大元定理中取 $d=4$、此有限 ensemble、
$n=(1,-1,3,-3)$、$\chi=(1/2,1/2,1/2,1/2)$，
则 `mixedSignal` 恰为 $s$，读出归一且第一矩 $1/4>0$。
因此 $M_3(s)\le T/16$。这个投影和重新加权仅用于证明，不要求物理后选择权限。

所需 $4/3<T<2$ 可直接由供应阈值和有理估计得到。
三个能量 $0,1,2$、输入与读出均为 $(1,1,1)/\sqrt3$ 的单项 ensemble 可容许；
$(1+x+x^2)^3$ 的系数为 $(1,3,6,7,6,3,1)$，平方和为 $141$。
故它有 $M_1=1/3$、$M_3=141/729=47/243$、$R_3=47/27$，给 $T\ge47/27>4/3$。
另一方面 $123/100<\alpha<31/25$，正参数上的两个多项式
$N=\operatorname{thresholdN}$、$D_{\rm poly}=\operatorname{thresholdD}$ 各自正且严格递增。
于是

$$
T<\frac{N(31/25)}{D_{\rm poly}(123/100)}<2,
\qquad
2D_{\rm poly}(123/100)-N(31/25)
=\frac{12274038070201}{500000000000}>0.
\tag{C123.11}
$$

此处不需要假设比值 $N/D_{\rm poly}$ 单调。

由 $M_2(s)\le M_1(s)=1/4$ 展开 (C123.9)，得到

$$
\begin{aligned}
M_3(p_\rho)
&=\lambda^3+\tfrac34\lambda^2(1-\lambda)
 +3\lambda(1-\lambda)^2M_2(s)+(1-\lambda)^3M_3(s)\\
&\le\lambda^3+\tfrac34\lambda(1-\lambda)+\tfrac T{16}(1-\lambda)^3.
\end{aligned}
\tag{C123.12}
$$

除以 $((1+3\lambda)/4)^2$ 即为 (C123.7) 第一界。
第二界的分子差为

$$
\begin{aligned}
&T(1+3\lambda)^2-\bigl[16\lambda^3-12\lambda^2+12\lambda+T(1-\lambda)^3\bigr]\\
&\qquad=\lambda\bigl[(9T-12)+(6T+12)\lambda+(T-16)\lambda^2\bigr].
\end{aligned}
\tag{C123.13}
$$

方括号关于 $\lambda$ 凹，在 $0,1$ 的值分别为 $9T-12$、$16(T-1)$，均非负。
因此在 $[0,1]$ 上非负。
若 $\lambda=1$，其余对角元皆为零；正性给
$|\rho_{jk}|^2\le\rho_{jj}\rho_{kk}$，迫使 $\rho=P_3$。
此时 $p_\rho=1$、$M_1=M_3=R_3=1\le T$，直接满足两界，无须除以 $1-\lambda$。

背景组合也可用成熟的透视凸性解释。对 $x\ge0,y>0$，
$\Phi(x,y)=x^3/y^2$ 的 Hessian 在方向 $(u,v)$ 上的二次型为
$6x(yu-xv)^2/y^4\ge0$。
对连续非负周期信号 $f,g$、各自正均值 $m_f,m_g$ 及 $0\le a\le1$，在
$(f(t),m_f),(g(t),m_g)$ 应用凸性再平均，得到
$R_3(af+(1-a)g)\le aR_3(f)+(1-a)R_3(g)$。
代入 $f=1,g=s,a=\lambda$，即有
$R_3(p_\rho)\le\lambda+(1-\lambda)T\le T$。
这是同一固定协议的另一条中间推导；粗矩展开所用 $4/3$ 不是恒亮背景组合的必要门槛。证毕。

**推论 C-123.3（实际四能量见证及共同三维源）。** 对供应输入
$\rho_\psi=|\psi\rangle\langle\psi|$，同一个协议满足

$$
\begin{aligned}
p_\psi(t)&=\frac{(\cos t+\cos3t)^2}{4}
=\frac14+\frac38\cos2t+\frac14\cos4t+\frac18\cos6t,\\
M_1(p_\psi)&=\frac14,\qquad M_2(p_\psi)=\frac{11}{64},\qquad
M_3(p_\psi)=\frac{145}{1024},\qquad R_3(p_\psi)=\frac{145}{64}>2>T.
\end{aligned}
\tag{C123.14}
$$

对[原生卷定义 65.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#45-原支持三维输入的精确末次秩二边缘)
及 [GC 定理 21.2](FIB_NATIVE_COMPLETE_CONTINUATION_GLOBAL_ACTUAL_COUNTS.md#21-the-fixed-complex-linear-five-mode-dictionary)
的同一复线性编码，在当前物理坐标写

$$
E=\bigl((e_0+e_4)/\sqrt2,(e_1+e_3)/\sqrt2,e_2\bigr).
\tag{C123.15}
$$

对每个复 qutrit 密度态 $\tau$，$\rho=E\tau E^\dagger$ 满足
$\lambda=\tau_{11}/2$，其中 $\tau_{11}$ 是中间列的逻辑人口。
所以定理 C-123.2 覆盖整个 $E$ 源，包括 $\lambda>0$ 的情形；
它不自动断言每个 $E$ 输出违反阈值。

证明。$D^\dagger\psi=\psi$，$\langle\psi|R(t)|\psi\rangle=(\cos t+\cos3t)/2$。
置 $\zeta=e^{2it}$，见证信号的 Laurent 系数从 $-3$ 到 $3$ 为
$(1,2,3,4,3,2,1)/16$。
平方的常数项为 $44/256=11/64$；立方的常数项为 $580/4096=145/1024$。
后者也由 $(1+x+x^2+x^3)^3$ 的系数
$(1,3,6,10,12,12,10,6,3,1)$ 的平方和 $580$ 得到。
零次系数和均值归一化给其余矩及比值。
最后三列正交归一，直接配对得
$E^\dagger P_3E=\operatorname{diag}(0,1/2,0)$，于是
$\operatorname{Tr}(P_3E\tau E^\dagger)=\tau_{11}/2$。证毕。

## 124. 两个可变参数的统一零相位有限字

**定理 C-124.1（整个载体上的固定模板）。** 在定义 C-123.1 的原生菜单下，
存在一个有限槽模板与整数 $L$，使对所有 $t\in\mathbb R$ 及所有五维输入，
模板精确求值为 $W_{\rm ph}(t)$。模板不调用指定门
$S_{\star,3}=\operatorname{diag}(1,1,1,1,i)$；仅两个 $H_2$ 槽的参数随 $t$ 变化。
更具体地，存在固定纯翻转字，长度为 $m_O,m_1,m_3$，使

$$
\begin{aligned}
W_{\rm ph}(t)&=O_{\rm ph}Q_1e^{-itH_2}Q_1^\dagger
                         Q_3e^{-i3tH_2}Q_3^\dagger,
\qquad O_{\rm ph}=DOD^\dagger,\\
L&=m_O+2m_1+2m_3+2.
\end{aligned}
\tag{C124.1}
$$

右端先作用；零参数保留为恒等槽。这里的 $L$ 是存在性界，不给数值脉冲数或时长最优值。

证明。原生 $H_2=|e_0\rangle\langle e_2|+|e_2\rangle\langle e_0|$，所以

$$
G=-iD^\dagger H_2D=|e_0\rangle\langle e_2|-|e_2\rangle\langle e_0|.
\tag{C124.2}
$$

定义实矩阵 $Q_1$ 固定 $e_0,e_3,e_4$，送 $e_1\mapsto e_2$、$e_2\mapsto-e_1$；
$Q_3$ 固定 $e_1,e_3$，送 $e_0\mapsto e_4$、$e_4\mapsto e_0$、$e_2\mapsto-e_2$。
二者正交且行列式一，均只混合同一 $D$ 相位的坐标，故与 $D$ 对易。
逐个秩一项共轭给

$$
Q_1GQ_1^T=A_1,\qquad Q_3GQ_3^T=A_3,\qquad
[A_1,A_3]=0,\qquad e^{-itH_2}=De^{tG}D^\dagger.
\tag{C124.3}
$$

因此 $R(t)=e^{tA_1}e^{3tA_3}$，相乘得到整个五维算符的 (C124.1)。
由[原生卷定理 64.1 的 (IX.1)](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#44-固定相位菜单的实际有限字达到)，
一次性选择分别求值为 $O_{\rm ph},Q_1,Q_3$ 的三个纯翻转有限字；
$Q_j=DQ_jD^\dagger$ 保证它们属于该精确纯翻转群。
每个逆字通过反转因子次序并反号参数取得，长度不变。
将三个固定字和两个逆字代入 (C124.1)，再保留两个可变 $H_2$ 槽，即得
$\exists(\text{模板},L)\,\forall t\,\forall\rho$，而非仅逐点的 $\forall t\,\exists\text{字}$。
这里只使用 (IX.1) 的实际有限字，不使用相位辅助 (IX.2) 或闭包极限。证毕。

**命题 C-124.2（周期、支持与参数的精确范围）。** 此模板可以将每个原生参数
取为模 $2\pi$ 的非负代表而保持整个算符不变。所有实际信号共同以 $\pi$ 为周期；
$W_{\rm ph}$ 的全算符以 $2\pi$ 为周期，$\pi$ 不是其全算符周期。
原生字前缀无须保持 $C$，但每个脉冲及其中途均保持整个合法 $\mathcal K_3$。

证明。假设 55.2 中每个单位系数 $H_j$ 为二态翻转块与零块之直和，
故 $H_j^3=H_j$，其指数有 $2\pi$ 周期；固定字、逆字及两个可变槽均适用。
令 $J=P_3-P_C$。主动能量全为奇数，inactive 能量为零，所以

$$
R(t+\pi)=R(t)J,\qquad W_{\rm ph}(t+\pi)=W_{\rm ph}(t)J,
\qquad F(t+\pi)=JF(t)J=F(t).
\tag{C124.4}
$$

$J\ne I$，甚至在全空间上不是标量，故不能把信号的 $\pi$ 周期当作全算符周期。
整块 $Q_1,Q_3,H_2$ 固定 $e_3$，但所选择的有限原生实现没有逐前缀保持 $C$ 的要求；
末端 $O_{\rm ph}$ 还把 $e_2$ 送到 $e_3$。
整个合法域的保持来自假设 55.2 的每个原生控制，而非 $C$ 支持承诺。
$H_{\rm ph}$ 的 $(e_2,e_4)$ 矩阵元为 $-3$，在每个瞬时原生 $H_j$ 中均为零。
故有限字综合不等于提供该裸 Hamiltonian。
$D$ 从未作为物理门插入；模周期选参也不提供校准时钟或把 $t$ 等同于物理经过时间。证毕。

## 125. 同一固定谱模型的有限矩求积与受限最小性

**定理 C-125.1（全五维复信号的十节点矩公式）。** 对所有五维复密度矩阵，置
$t_j=\pi j/10$、$j=0,\ldots,9$，则

$$
M_q(p_\rho)=\frac1{10}\sum_{j=0}^9p_\rho(t_j)^q,
\qquad q=1,2,3.
\tag{C125.1}
$$

证明。主动能量差为 $0,\pm2,\pm4,\pm6$；(C123.6) 排除与 inactive 能量的跨块项。
故包括任意 $\lambda$ 与任意复相干的整个信号族都具有形式

$$
p_\rho(t)=c_0+\sum_{k=1}^3(a_k\cos2kt+b_k\sin2kt),
\qquad c_0=(1+3\lambda)/4.
\tag{C125.2}
$$

在 $\zeta=e^{2it}$ 中，$p_\rho^q$ 的 Laurent 次数不超过 $3q\le9$。
而 $10^{-1}\sum_{j=0}^9e^{2\pi i kj/10}=0$ 对 $0<|k|\le9$ 成立。
有限节点平均与积分均只保留常数项，得 (C125.1)。
$\pi$ 周期函数在 $[0,\pi]$ 的归一平均与 (C123.5) 的 $2\pi$ 归一平均相同。证毕。

**定理 C-125.2（固定加权三次幂求积类恰需十节点）。** 设节点 $s_1,\ldots,s_m$
及实权重 $w_1,\ldots,w_m$ 不依赖 $\rho$，并要求对同一个实际谱模型的每个密度态都有

$$
M_3(p_\rho)=\sum_{j=1}^m w_jp_\rho(s_j)^3.
\tag{C125.3}
$$

即使允许负权重，也必须至少有十个模 $\pi$ 不同的节点。
因此 (C125.1) 在这个固定节点、固定权重直接作用于三次幂的类中达到最小节点数；
另要求第一、第二矩精确不改变这个下界。

证明。将主动物理能量基按 $(-3,-1,1,3)$ 排序，构造实际态

$$
\rho_{\rm act}=I_4/4+X,\qquad
X_{0k}=2(a_k-i b_k),\quad X_{k0}=2(a_k+i b_k)\quad(1\le k\le3),
\tag{C125.4}
$$

其余元素为零，并在 inactive 坐标补零。
$X$ Hermitian、迹零，其非零本征值为
$\pm2r$，$r=\sqrt{\sum_{k=1}^3(a_k^2+b_k^2)}$。
这由 $X$ 的星形二块矩阵或 $X^3=4r^2X$ 得到。
所以 $r<1/8$ 时主动块严格正，嵌回后为实际五维密度态。
固定读出各坐标为 $1/2$，第 $0,k$ 项贡献

$$
\tfrac14\bigl[2(a_k-i b_k)e^{2ikt}+2(a_k+i b_k)e^{-2ikt}\bigr]
=a_k\cos2kt+b_k\sin2kt.
\tag{C125.5}
$$

这些实际态恰实现 $c=1/4$ 周围六个非恒定实系数的开放球。
此构造用于检验普遍量词，不主张菜单供应这些态的制备。

令 $I$ 为归一积分、$Q(f)=\sum_jw_jf(s_j)$、$\mathcal L=I-Q$，并置
$V=\operatorname{span}_{\mathbb R}\{\cos2kt,\sin2kt:1\le k\le3\}$。
假设给 $\mathcal L((c+v)^3)=0$ 在 $V$ 的上述开放球上成立。
这是六个实系数的三次多项式恒等式。
常数、一次、二次、三次系数及极化分别给

$$
\mathcal L(1)=\mathcal L(v)=\mathcal L(vw)=\mathcal L(vwu)=0
\quad(v,w,u\in V).
\tag{C125.6}
$$

复化后 $V$ 包含 $\zeta^{\pm1},\zeta^{\pm2},\zeta^{\pm3}$。
每个 $|k|\le9$ 的 $\zeta^k$ 都是至多三个这样的因子的乘积，或为常数。
故 $Q$ 必须精确积分全部九次三角多项式。
合并模 $\pi$ 重复节点后，若不同节点数 $d\le9$，则

$$
F_*(t)=\prod_{j=1}^{d}|e^{2it}-e^{2is_j}|^2
\tag{C125.7}
$$

是次数 $d$ 的非负、非恒零三角多项式，有 $I(F_*)>0$；
但所有节点上为零，使任意权重下 $Q(F_*)=0$，矛盾。
空节点集直接由常数函数排除。结合 C-125.1 完成最小性证明。证毕。

**命题 C-125.3（七节点 Fourier 重构的类外边界）。** 若允许从精确概率值
先重构信号、再非线性计算矩，则七个等距设置 $s_j=\pi j/7$ 已足以计算三个矩。
这一算法不属于 (C125.3) 的固定加权三次幂求积类。

证明。在 (C125.2) 中写 $p(t)=\sum_{k=-3}^3c_ke^{2ikt}$。
七个指数 $-3,\ldots,3$ 在模七中互异，故离散反演给

$$
c_k=\frac17\sum_{j=0}^6p(\pi j/7)e^{-2\pi i kj/7},
\qquad
M_q(p)=\sum_{\substack{k_1,\ldots,k_q\in\{-3,\ldots,3\}\\k_1+\cdots+k_q=0}}c_{k_1}\cdots c_{k_q}.
\tag{C125.8}
$$

三次卷积中出现不同节点值的乘积，未要求表示为固定权重的 $p(s_j)^3$ 之和。
若可以普遍这样表示，就与 C-125.2 矛盾。
所以十节点最小性不是一般测量设置最优性，也不是对所有统计算法的样本下界。证毕。

## 126. 固定校准与新 iid 输入下的有限样本认证

**假设 C-126.1（额外供应的重复来源与固定规则）。** 在数据以前固定
$0<\delta<1$、整数 $n\ge1$、C-125.1 的十个设置及以下分析规则。
每个设置供应 $n$ 份新的、独立且同分布的相同未知密度态 $\rho$；
各试次使用同一个已校准的理想 $W_{\rm ph}(t_j)$ 和末端二值传感器。
于是总共 $10n$ 个记录具有固定概率的独立 Bernoulli 模型

$$
X_{jr}\sim\operatorname{Bernoulli}(p_j),\qquad
p_j=p_\rho(t_j),\qquad
\widehat p_j=\frac1n\sum_{r=1}^{n}X_{jr}.
\tag{C126.1}
$$

这是原生单输入菜单之外的供应前提，不是对原未知输入作重置或反复使用。
同一个固定校准模型、来源与规则适用于全部试次；不允许据数据选 $n$ 或可选停止。
以下 $\log$ 均为自然对数。

**定义 C-126.2（截断下置信比）。** 置

$$
\begin{aligned}
\varepsilon&=\sqrt{\frac{\log(20/\delta)}{2n}},&
\ell_j&=\max(0,\widehat p_j-\varepsilon),&
u_j&=\min(1,\widehat p_j+\varepsilon),\\
L_3&=\frac1{10}\sum_{j=0}^9\ell_j^3,&
U_1&=\frac1{10}\sum_{j=0}^9u_j,&
\widehat R_{\rm low}&=\frac{L_3}{U_1^2}.
\end{aligned}
\tag{C126.2}
$$

由于 $\varepsilon>0$，每个数据集均有 $u_j\ge\min(1,\varepsilon)>0$，故 $U_1>0$。

**定理 C-126.3（条件置信覆盖与频率学误报界）。** 在假设 C-126.1 下，
对每个固定五维复密度态 $\rho$，

$$
\Pr_\rho\bigl(\widehat R_{\rm low}\le R_3(p_\rho)\bigr)\ge1-\delta,
\qquad
\sup_{\operatorname{cn}_{\mathcal B}(\rho)\le3}
\Pr_\rho(\widehat R_{\rm low}>T)\le\delta.
\tag{C126.3}
$$

阈值改用 $\widehat R_{\rm low}>2$ 仍有相同误报界。
这是固定状态与供应模型下重复实验的误报概率，不是数据后关于状态的后验概率。

证明。对任意 $X\sim\operatorname{Bernoulli}(p)$，包括 $p=0,1$，定义

$$
\begin{aligned}
h(\theta)&=\log\mathbb E e^{\theta(X-p)}
=\log(1-p+pe^\theta)-p\theta,\\
q_\theta&=\frac{pe^\theta}{1-p+pe^\theta},\qquad
h(0)=h'(0)=0,\qquad h''(\theta)=q_\theta(1-q_\theta)\le\frac14.
\end{aligned}
\tag{C126.4}
$$

分母始终正。Taylor 积分式对所有实 $\theta$ 给
$h(\theta)=\theta^2\int_0^1(1-v)h''(v\theta)\,dv\le\theta^2/8$。
独立性使中心化和的矩母函数不超过 $e^{n\theta^2/8}$。
对 $\theta=4\varepsilon>0$，指数 Markov 给

$$
\Pr\left(\sum_{r=1}^n(X_{jr}-p_j)>n\varepsilon\right)
\le e^{-n\theta\varepsilon+n\theta^2/8}=e^{-2n\varepsilon^2}.
\tag{C126.5}
$$

下尾对负中心化和同理，得到
$\Pr(|\widehat p_j-p_j|>\varepsilon)\le2e^{-2n\varepsilon^2}=\delta/10$。
对十设置取并集界，事件

$$
\mathcal G=\bigcap_{j=0}^9\{|\widehat p_j-p_j|\le\varepsilon\}
\quad\text{满足}\quad\Pr_\rho(\mathcal G)\ge1-\delta.
\tag{C126.6}
$$

在此事件上，因 $0\le p_j\le1$，截断保留
$0\le\ell_j\le p_j\le u_j\le1$。
由 C-125.1，$0\le L_3\le M_3(p_\rho)$，
$U_1\ge M_1(p_\rho)\ge1/4$，于是 $L_3/U_1^2\le R_3(p_\rho)$。
若再有 (C123.4)，同一事件上 C-123.2 给
$\widehat R_{\rm low}\le R_3(p_\rho)\le T$，所以误报事件包含于 $\mathcal G^c$。
这个界对每个零假设态使用同一 $\delta$，取上确界即得 (C126.3)。
$T<2$ 给更保守触发规则的结论。证毕。

**推论 C-126.4（同一估计器的两个充分样本界）。** 在假设 C-126.1 的见证来源
$\rho=\rho_\psi$ 上，每设置取

$$
n\ge\left\lceil131072\log(20/\delta)\right\rceil
\tag{C126.7}
$$

即可保证 $\Pr_{\rho_\psi}(\widehat R_{\rm low}>2)\ge1-\delta$。
利用同一见证的第二矩，可将充分条件改进为

$$
n\ge\left\lceil18432\log(20/\delta)\right\rceil.
\tag{C126.8}
$$

这两个界使用同一截断估计器与误报规则；较小常数不是样本最优性结论。

证明。在 (C126.6) 的同一事件上，
$0\le p_j-\ell_j\le2\varepsilon$ 且 $u_j\le p_j+2\varepsilon$。
$x^3$ 在 $[0,1]$ 上的 Lipschitz 常数为三，故

$$
L_3\ge\frac{145}{1024}-6\varepsilon,\qquad U_1\le\frac14+2\varepsilon.
\tag{C126.9}
$$

若 $\varepsilon\le1/512$，分子下界为正，并有

$$
\widehat R_{\rm low}\ge
\frac{133/1024}{(65/256)^2}=\frac{8512}{4225}>2.
\tag{C126.10}
$$

由 $512^2/2=131072$，(C126.7) 足以保证此 $\varepsilon$ 条件。
更精细地，逐节点有

$$
p_j^3-\ell_j^3
=(p_j-\ell_j)(p_j^2+p_j\ell_j+\ell_j^2)
\le6\varepsilon p_j^2.
\tag{C126.11}
$$

用 C-125.1 的第二矩公式和 (C123.14)，得到
$L_3\ge145/1024-(33/32)\varepsilon$。
因此 $\varepsilon\le1/192$ 时

$$
\widehat R_{\rm low}\ge
\frac{279/2048}{(25/96)^2}=\frac{2511}{1250}>2.
\tag{C126.12}
$$

$192^2/2=18432$，所以向上取整的 (C126.8) 给该条件。
两次推导均在同一概率至少 $1-\delta$ 的事件上成立。证毕。

## 127. 资源、频谱与文献适用边界

**命题 C-127.1（条件协议的实际资源范围）。** 在 C-124.1 与 C-126.1 的条件下，
十设置、每设置 $n$ 次的完整固定规则消费 $10n$ 份新输入及 $10n$ 次末端二值记录，
至多使用 $10nL$ 个原生脉冲槽，指定 $S_{\star,3}$ 调用数为零。
源制备、固定校准、参数精度、时钟、SSR 或参考系兼容性及物理时长均为额外供应或未评价成本。

证明。每份输入仅施加所选设置的一次 $L$ 槽字并作一次末端二值测量，
然后转到下一份新输入；总计直接相乘。
C-124.1 的模板只由原生翻转字组成；$D$ 为被动坐标。
假设 55.2 没有承诺初始化或硬件成本界，C-126.1 则明确增加重复输入与校准前提。
因此这些成本不能由零指定相位计数、字的存在或概率可识别性消去。
本结论不供应 $\psi$ 或 $E\tau E^\dagger$ 的制备，也不授予跨 SSR 的相干操作。证毕。

**命题 C-127.2（无固定谱模型时的有限节点反例）。** 在全部连续、$\pi$ 周期、
取值于 $[0,1]$ 的概率函数类中，任意有限节点的精确函数值不足以决定第一、第三矩。
即使节点值固定为实际见证 $p_\psi$ 的值，也不足以决定第一矩。

证明。对给定有限节点 $s_1,\ldots,s_m$，令

$$
g(t)=\prod_{j=1}^{m}\frac{1-\cos(2(t-s_j))}{2}.
\tag{C127.1}
$$

它连续、$\pi$ 周期且在 $[0,1]$ 中，所有节点上为零，除有限个零点外为正。
所以 $0$ 与 $g$ 有相同节点值，而 $M_1(g),M_3(g)>0$。
再取任意 $0<a\le1$，置

$$
q(t)=p_\psi(t)+a p_\psi(t)(1-p_\psi(t))g(t).
\tag{C127.2}
$$

$0\le q\le p_\psi+p_\psi(1-p_\psi)\le1$，节点值仍等于 $p_\psi$。
见证在某个开区间内严格介于零与一，去掉有限节点后增量在那里严格正，
故 $M_1(q)>M_1(p_\psi)$。
这些反例属于无模型的连续函数类，不断言它们可由 (C123.2) 的同一固定谱设备实现。
因此它们不反驳 C-125.1，只说明不能删除其频谱条件。证毕。

**适用边界 C-127.3（证书对象与尚未确定的量）。** C-123–C-126 的组合仅认证
固定物理能量基 $\mathcal B$ 中的混态相干数。
它不将原生秩二传感器任意更换为别的秩二读出，不给任意秩二传感器的通用阈值定理。
与 C-121 的历史条件、随机设置及三结果 PVM 不同，C-126 使用固定 iid 源、固定设置与末端二值读口；
两套假设不能互相替代。C-116.2 的共同标签反例仍排除以相同边缘或可交换性代替 iid。
精确矩、脉冲模板存在、模型内误报控制均不证明源独立性、实际校准、物理安装或本体解释。
数值 $L$、脉冲数和时长最优值、一般算法的最小设置数、最优样本数均未在此确定。
[相位增益与 qutrit 恢复卷定义 6.2](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#6-class-optimization-and-remaining-mathematical-obligations)
的正 $\beta$ 全实编码器类尖锐恢复曲线仍是另一未解决问题。

**数学引文 C-127.4（供应结果与中间工具的范围）。**
三相干阈值复用
[ThreeCoherenceRamseyThreshold.result](../../../D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.lean)
及其 [Blueprint](../../../Blueprint/D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold.md)、
[文献注](../../../Library/QuantumBounds/dive2020multilevelcoherence.md) 的显式有限 ensemble 量词。
Dive、Koukoulekidis、Mousafeiris、Mintert，
*Characterisation of multi-level quantum coherence without ideal measurements*，
[arXiv:1901.08599v3](https://arxiv.org/abs/1901.08599v3)，§II、式 (1)–(4)、Table I、Appendix A，
[Phys. Rev. Research 2, 013220](https://doi.org/10.1103/PhysRevResearch.2.013220)，
供应固定共同 Hamiltonian、归一秩一读出和混态矩比凸性的背景。
该文 $C_k$ 符号在定义与阈值表的操作读法间需区分，故这里以 (C123.4) 为准；
精确代数最大值引用仓内结果，不归给该文的解析上界或数值表。
实际秩二读口的适用性由 (C123.6)–(C123.13) 的全空间分解承担。

有限 Fourier 正交性及周期梯形求积为成熟工具，见 Trefethen–Weideman，
*The Exponentially Convergent Trapezoidal Rule*，
[SIAM Review 56(3), 385–458](https://doi.org/10.1137/130932132)，Corollary 3.3，印刷页 398：
次数 $d$ 的三角多项式在节点数 $N>d$ 时由等距周期梯形规则精确积分。
C-125.1 直接证明所需有限正交式；C-125.2 另用实际正密度的六系数开放球守住其普遍量词。

Bernoulli 尾界属于 Hoeffding，
*Probability Inequalities for Sums of Bounded Random Variables*，
[JASA 58(301), 13–30](https://doi.org/10.1080/01621459.1963.10500830) 的有界变量浓缩框架。
这里使用的精确常数和全部概率步骤由 (C126.4)–(C126.6) 自包含证明，不依赖该文定理编号。
透视凸性、Fourier 求积及浓缩不等式均为中间工具；
本章的 repo-derived 综合是将其接到同一个实际原生字、全五维复源、指定能量基及明确新增供应的统计协议，
不作这些工具或该综合的全域新颖性、优先权主张。

## 追加锚（本行以下为增补区）

## 128. 固定能量基、共同三维源与认证零假设

**定义 C-128.1（固定物理基中的两个来源域）。** 沿用 (C123.1)–(C123.3)、
(C123.15) 的同一物理五态顺序、能量基、目标及编码，记

$$
\begin{aligned}
(e_0,e_1,e_2,e_3,e_4)&=(000,100,010,001,101),\\
\mathcal B=(b_1,b_2,b_3,b_4,b_5)
&=\left(\frac{e_0-e_1}{\sqrt2},\frac{e_0+e_1}{\sqrt2},
\frac{e_4-e_2}{\sqrt2},\frac{e_4+e_2}{\sqrt2},e_3\right),\\
\psi&=(e_0+e_4)/\sqrt2,\qquad \eta=(e_1+e_3)/\sqrt2,\\
E&=(\psi,\eta,e_2),\qquad Q=\operatorname{ran}E,\qquad P_Q=EE^\dagger,\\
P_x&=|x\rangle\langle x|\quad(\|x\|=1),\qquad
P=P_\psi,\qquad C=\operatorname{span}(e_0,e_1,e_2,e_4),\quad P_C=I-P_{e_3}.
\end{aligned}
\tag{C128.1}
$$

这里 $\mathcal B$ 恰为 (C123.3) 的物理能量基，能量仍为 $(1,-1,3,-3,0)$。
所有相干数均相对于这一个基，不相对于逻辑列基 $(\psi,\eta,e_2)$。
令 $\mathsf D(Q)=\{\rho\succeq0:\operatorname{Tr}\rho=1,\rho=P_Q\rho P_Q\}$，并置

$$
\begin{aligned}
\mathcal F_{\rm all}
&=\operatorname{conv}_{\rm fin}\{P_x:\|x\|=1,
\#\{j:\langle b_j|x\rangle\ne0\}\le3\},\\
\mathcal F_Q&=\mathcal F_{\rm all}\cap\mathsf D(Q).
\end{aligned}
\tag{C128.2}
$$

$\operatorname{conv}_{\rm fin}$ 指所有有限凸混合，向量振幅允许任意复数，凸权重为非负实数且和为一。
第一域是 (C123.4) 的整个五维零假设；第二域另有实际输入支持于 $Q$ 的承诺。
这个 $E$ 来自[原生卷定义 65.1、(IX.7)](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#45-原支持三维输入的精确末次秩二边缘)，
不同于其定义 55.1 的交替位置编码。给定等距矩阵、给定支持与实际制备该源是不同前提。

**定义 C-128.2（无条件风险与指定目标功效）。** 对 $n\ge1$ 个已供应输入，
目标为 $P^{\otimes n}$。对其联合零假设域 $\mathcal N$ 和无条件宣告效果 $0\preceq T\preceq I$，定义

$$
\beta_{\mathcal N}(T)=\sup_{\rho\in\mathcal N}\operatorname{Tr}(T\rho),\qquad
\alpha_n(T)=\operatorname{Tr}(TP^{\otimes n}),\qquad
A_{\mathcal N}(\delta)=
\sup_{\substack{0\preceq T\preceq I\\\beta_{\mathcal N}(T)\le\delta}}\alpha_n(T),
\quad 0\le\delta\le1.
\tag{C128.3}
$$

风险计算包括全部输出，不能先丢弃失败分支再把条件成功率代入。
$A$ 首先允许全部测量效果，因而是原生菜单的放松；原生达到性须另行给出实际供应。
单输入时记 $\alpha=\alpha_1$。以下计算固定目标的功效，不要求对全部四相干态具有同一功效。

## 129. 共同源与三相干零假设的完整八射线交集

**定理 C-129.1（任意复振幅与全部混态分解）。** 对任意复数 $a,b,c$，
向量 $a\psi+b\eta+ce_2$ 在固定 $\mathcal B$ 中的坐标为

$$
\left(\frac{a-b}{2},\frac{a+b}{2},
\frac a2-\frac c{\sqrt2},\frac a2+\frac c{\sqrt2},\frac b{\sqrt2}\right).
\tag{C129.1}
$$

在 $Q$ 内归一化且至多三支持的向量，除共同整体相位外恰为以下八条射线：

$$
e_2,\quad\eta,\quad
u_t=\sqrt{\frac23}\psi+\frac{t}{\sqrt3}e_2,\quad
v_{st}=\sqrt{\frac25}(\psi+s\eta)+\frac{t}{\sqrt5}e_2,
\qquad s,t\in\{-1,1\}.
\tag{C129.2}
$$

此处 $u_t$ 为两条、$v_{st}$ 为四条。每个 $Q$ 支持密度态的每一种有限纯态分解，
其每个正权重分量都实际位于 $Q$。特别地，

$$
\mathcal F_Q=
\operatorname{conv}\{P_{e_2},P_\eta,P_{u_+},P_{u_-},P_{v_{++}},P_{v_{+-}},P_{v_{-+}},P_{v_{--}}\}.
\tag{C129.3}
$$

证明。逐项与 (C128.1) 的五个基向量配对得 (C129.1)。
先分类非零向量。若 $a=0$ 且 $b,c$ 均非零，则五个坐标全部非零，不合条件。
若 $a=0$，只剩 $b=0$ 或 $c=0$ 两种可能，分别给 $e_2$、$\eta$ 的射线。

若 $a\ne0,b=0$，第一、第二坐标均非零，第五为零；
要使总支持不超过三，第三、第四坐标至少一个为零，故
$c=ta/\sqrt2$，$t=\pm1$。二者不能同时为零。
由 $E$ 等距，范数平方为 $3|a|^2/2$，归一化后恰为 $u_t$，只留共同整体相位。

若 $a\ne0,b\ne0$，第五坐标非零；前四坐标至少两个必须为零。
第一对坐标不能同时为零，第二对也不能同时为零，否则均会迫使 $a=0$。
所以每对恰有一个零，给出

$$
b=sa,\qquad c=ta/\sqrt2,\qquad s,t\in\{-1,1\}.
\tag{C129.4}
$$

这是复数的精确等式，已经固定全部相对相位，不能另添任意相位族。
此时范数平方为 $5|a|^2/2$，归一化得 $v_{st}$。
反向代入可知 $e_2$ 恰有两个非零坐标，其余七条恰有三个，且八条互不相同。
上述各情况穷尽全部复 $a,b,c$ 及零坐标退化。

再令 $\rho\in\mathsf D(Q)$，取任意有限分解
$\rho=\sum_\ell p_\ell P_{x_\ell}$，其中 $p_\ell>0$、$\|x_\ell\|=1$。
以 $R=I-P_Q$ 得

$$
0=\operatorname{Tr}(R\rho)=\sum_\ell p_\ell\|Rx_\ell\|^2.
\tag{C129.5}
$$

每项非负，故每个 $Rx_\ell=0$。这对每一种分解成立，不只对某种特选分解成立。
若 $\rho$ 还在 $\mathcal F_{\rm all}$，将其三支持见证分解用于这一结论，
每个正权重向量就必须属于刚分类的八射线，给 (C129.3) 的正向包含。
反向包含由各射线三支持和 $Q$ 支持直接得到。混合中相干项的抵消不能抵消非负支撑泄漏。证毕。

## 130. 原生固定读口在承诺源上的精确达到

**定理 C-130.1（同一定向字与全部八射线概率）。** 使用 C-123.1 的同一理想菜单：
每次独立选择一个受约束翻转，其余驱动与漂移为零，参数为任意实数，
允许有限串行字及逆，末端另行供应 $\{n_1,I-n_1\}$。
取 (C123.2) 中的定向映射

$$
O:\left(\psi,\frac{e_0-e_4}{\sqrt2},e_1,e_2,e_3\right)
\longmapsto(e_1,e_0,e_2,e_3,-e_4),\qquad O_{\rm ph}=DOD^\dagger.
\tag{C130.1}
$$

它有一个实际纯翻转有限字实现，指定 $S_{\star,3}$ 调用数为零。
以该字之后的末次结果 $1$ 为宣告事件，其效果和压缩为

$$
F_0=O_{\rm ph}^\dagger n_1O_{\rm ph}=P+P_{e_3},\qquad
E^\dagger F_0E=\operatorname{diag}(1,1/2,0).
\tag{C130.2}
$$

全部八射线及目标的概率为

| 输入射线 | 条数 | $\operatorname{Tr}(PP_x)$ | $\operatorname{Tr}(F_0P_x)$ |
| --- | ---: | ---: | ---: |
| $e_2$ | 1 | $0$ | $0$ |
| $\eta$ | 1 | $0$ | $1/2$ |
| $u_t$ | 2 | $2/3$ | $2/3$ |
| $v_{st}$ | 4 | $2/5$ | $3/5$ |
| $\psi$（目标） | 1 | $1$ | $1$ |

因此固定的确定性事件恰有

$$
\beta_{\mathcal F_Q}(F_0)=2/3,\qquad \alpha(F_0)=1,
\qquad \beta_{\mathcal F_{\rm all}}(F_0)=1.
\tag{C130.3}
$$

证明。C-123.2 已证 (C130.1) 的两组有序正交基均正定向，故 $O\in SO(5)$；
其读扇区原像为 $\operatorname{span}(\psi,e_3)$。
$D$ 与 $n_1$ 对易，且固定 $P$、$P_{e_3}$，给 (C130.2)，亦即 (C123.6) 在 $t=0$ 的效果。
[原生卷定理 64.1 的 (IX.1)](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#44-固定相位菜单的实际有限字达到)
在链长三时供应实际有限字群 $\mathcal V_3=DSO(5)D^\dagger$，故供应这个 $O_{\rm ph}$ 本身。
这里使用已给的精确有限字结论，不把 Lie 代数闭包或稠密性单独当作实际达到。
$D$ 始终是被动坐标，未作为物理门插入；此处不调用带指定相位门的更大群结论。

压缩矩阵使 $a\psi+b\eta+ce_2$ 的通过概率为 $|a|^2+|b|^2/2$，
目标重叠为 $|a|^2$。逐行代入 (C129.2) 得表。
由 C-129.1 的完整混态桥及线性性，承诺零假设的最大通过概率为 $2/3$，在 $u_t$ 达到。
但 $b_5=e_3$ 是物理能量基中的一支持零假设态，且 $F_0e_3=e_3$，
故全域风险为一。证毕。

**命题 C-130.2（显示缩放的实际随机化供应）。** 若另行供应一个独立于输入、
控制及末端结果的经典 Bernoulli 随机数 $Z$，$\Pr(Z=1)=t\in[0,1]$，
仅在末端结果和 $Z$ 均为一时宣告，则效果为 $tF_0$，承诺域的风险、目标功效恰为
$(2t/3,t)$。

证明。对任意输入 $\rho$，联合宣告概率为
$t\operatorname{Tr}(F_0\rho)$；对全部输入成立即确定效果 $tF_0$。
代入 (C130.3) 即得。无此额外供应时，固定事件本身只给 $(2/3,1)$ 这一点。
这不声称其他原生字必须使用硬币，也不声称菜单供应秩一效果 $P$。证毕。

## 131. 单输入的两个尖锐风险—功效前沿

**定理 C-131.1（全域放松与承诺域原生达到）。** 对所有 $\delta\in[0,1]$，
定义 C-128.2 的单输入前沿为

$$
A_{\mathcal F_{\rm all}}(\delta)=\min\{1,4\delta/3\},\qquad
A_{\mathcal F_Q}(\delta)=\min\{1,3\delta/2\}.
\tag{C131.1}
$$

第一式的达到效果 $tP$ 是不限测量的放松；未由此供应其全域原生实现。
第二式除 $tP$ 的数学达到外，在 C-130.1 菜单与 C-130.2 的独立最终硬币下，
由实际 $tF_0$ 达到，$t=\min\{1,3\delta/2\}$。

证明。目标在 $\mathcal B$ 中为 $(1,1,1,1,0)/2$。
对归一化复三支持向量 $x=\sum_jx_jb_j$，令
$J=\{j\le4:x_j\ne0\}$，Cauchy–Schwarz 给

$$
|\langle\psi|x\rangle|^2
=\frac14\left|\sum_{j\in J}x_j\right|^2
\le\frac{|J|}{4}\sum_{j\in J}|x_j|^2\le\frac34.
\tag{C131.2}
$$

有限凸混合保持该界。令

$$
\phi_j=\frac1{\sqrt3}\sum_{\substack{1\le k\le4\\k\ne j}}b_k
\quad(j=1,2,3,4),\qquad
\sigma_{\rm all}=\frac14\sum_{j=1}^4P_{\phi_j}
=\frac34P+\frac{P_C-P}{12}.
\tag{C131.3}
$$

每个 $\phi_j$ 恰三支持且达到重叠 $3/4$。
四投影的平均在前四个 $\mathcal B$ 坐标上对角为 $1/4$、非对角为 $1/6$，
第五行列为零，证明最后的等式。
$P_C-P$ 是秩三正交投影，所以这是实际零假设混态，谱为
$3/4,1/12,1/12,1/12,0$，且 $\sigma_{\rm all}\succeq(3/4)P$。

承诺域由 C-129.1 得最大目标重叠为 $2/3$，且实际零假设混态

$$
\sigma_Q=\frac12(P_{u_+}+P_{u_-})=\frac23P+\frac13P_{e_2}
\succeq\frac23P.
\tag{C131.4}
$$

分别记 $(\mathcal F,c,\sigma)$ 为
$(\mathcal F_{\rm all},3/4,\sigma_{\rm all})$ 或
$(\mathcal F_Q,2/3,\sigma_Q)$。对任意 $0\preceq T\preceq I$，

$$
\beta_{\mathcal F}(T)\ge\operatorname{Tr}(T\sigma)
=c\alpha(T)+\operatorname{Tr}(T(\sigma-cP))\ge c\alpha(T).
\tag{C131.5}
$$

最后一项非负，因为它等于
$\operatorname{Tr}(T^{1/2}(\sigma-cP)T^{1/2})$，不要求 $T$ 与 $\sigma$ 对易。
结合 $\alpha\le1$ 给两条上界。
反向取 $t=\min\{1,\delta/c\}$，则 $0\preceq tP\preceq I$，
其风险恰为 $tc\le\delta$，功效为 $t$，达到上界。
在承诺域，C-130.1–C-130.2 给 $tF_0$ 同样的风险和功效。
这包括 $\delta=0,c,1$；当 $\delta\ge c$ 时只需风险 $c$，无需用尽风险额度。

若协议只消费这一未知输入，允许的辅助态、设置、随机资料均与输入无关，
则将其固定供应和全部控制并入同一通道 $\Lambda$，末端宣告效果为 $M$，
在输入上的效果就是 $T=\Lambda^\dagger(M)$，满足 $0\preceq T\preceq I$。
对内部随机资料平均仍给这样的效果。
所以 (C131.5) 也约束这类协议的全部无条件宣告；此效果约化不提供逆向的原生实现。
若只承诺 $Q$ 支持，$E^\dagger TE$ 是任意三维效果，反向可延拓为 $ESE^\dagger$；
压缩没有删去任何放松测量，但压缩后的零假设仍必须是八射线凸包。证毕。

(C131.2) 消费标准纯态多级相干重叠见证：Ringbauer 等，
*Certification and Quantification of Multilevel Quantum Coherence*，
[arXiv:1707.05282v3](https://arxiv.org/html/1707.05282v3)，§I.4、式 (9) 后的重叠恒等式、
Theorem 2／式 (10)、式 (11)，[Phys. Rev. X 8, 041007](https://doi.org/10.1103/PhysRevX.8.041007)。
在本基中取 $k=3$，三个最大振幅模平方和正是 $3/4$。
Johnston、Li、Plosker、Poon、Regula，
*Some notes on the robustness of k-coherence and k-entanglement*，
[arXiv:1806.00653v3](https://arxiv.org/html/1806.00653v3)，§II 式 (2)–(3)、§III Theorem 1，
[Phys. Rev. A 98, 022328](https://doi.org/10.1103/PhysRevA.98.022328)，
在五维 $k=3$、目标振幅 $(1/2,1/2,1/2,1/2,0)$ 时给标准及广义稳健性 $1/3$。
(C131.3) 是此处直接展示的实际原始见证；这些一般结果不分类 $\mathcal F_Q$。

(C131.5) 的正序支配机制亦属成熟资源区分方法，见 Takagi、Regula、Bu、Liu、Adesso，
*Operational Advantage of Quantum Resources in Subchannel Discrimination*，
[arXiv:1809.01672v3](https://arxiv.org/html/1809.01672v3)，式 (1)–(5)、Theorem 2，
[Phys. Rev. Lett. 122, 140402](https://doi.org/10.1103/PhysRevLett.122.140402)。
该定理优化子通道任务与测量，不供应这里的传感器。
对承诺域须在压缩空间 $Q$ 上核对其满秩自由态条件：
$(\sigma_Q+P_\eta)/2$ 在 $(\psi,\eta,e_2)$ 中为
$\operatorname{diag}(1/3,1/2,1/6)\succ0$。
相对广义稳健性为 $1/2$：$\sigma_Q=(P+(1/2)P_{e_2})/(3/2)$ 给上界；
任何自由混合 $(P+s\tau)/(1+s)$ 的目标重叠至少 $1/(1+s)$，
而 (C129.3) 将其限制为至多 $2/3$，故 $s\ge1/2$。
这些是固定源证明内的标准一致性对应，不另立一般相干或稳健性定理。

## 132. 独立新输入及其零假设乘积分支

**定义 C-132.1（三种实际输入域）。** 对 $\mathcal F\in\{\mathcal F_{\rm all},\mathcal F_Q\}$，
$n\ge1$，分别定义

$$
\begin{aligned}
\mathcal I_n(\mathcal F)&=\{\rho^{\otimes n}:\rho\in\mathcal F\},\\
\mathcal P_n(\mathcal F)&=\{\rho_1\otimes\cdots\otimes\rho_n:\rho_i\in\mathcal F\ (\forall i)\},\\
\mathcal S_n(\mathcal F)&=\operatorname{conv}_{\rm fin}\mathcal P_n(\mathcal F).
\end{aligned}
\tag{C132.1}
$$

它们依次为 iid、独立但可不同分布，以及每个分支的每个因子均属于零假设的乘积混合。
最后一种允许由混合标签产生关联，不要求无条件独立；其限定是每个分支的全部因子均为零假设。
$\operatorname{conv}_{\rm fin}\mathcal I_n$ 亦包含在最后一域中。

**定理 C-132.2（独立输入的两条精确前沿）。** 对任意上述四种域
$\mathcal N=\mathcal I_n(\mathcal F),\operatorname{conv}_{\rm fin}\mathcal I_n(\mathcal F),
\mathcal P_n(\mathcal F),\mathcal S_n(\mathcal F)$，均有

$$
\begin{aligned}
A_{\mathcal N}(\delta)&=\min\{1,\delta/(3/4)^n\}
&&\text{若 }\mathcal F=\mathcal F_{\rm all},\\
A_{\mathcal N}(\delta)&=\min\{1,\delta/(2/3)^n\}
&&\text{若 }\mathcal F=\mathcal F_Q,
\qquad 0\le\delta\le1.
\end{aligned}
\tag{C132.2}
$$

全域的达到为不限测量效果 $tP^{\otimes n}$。
承诺域由原生全通过事件 $F_0^{\otimes n}$，再配一个独立最终硬币，以
$t=\min\{1,\delta/(2/3)^n\}$ 达到。
逆向上界允许全部集体效果，故也约束原生测量的任意组合。

证明。取 C-131.1 对应的 $c,\sigma$，写 $R=\sigma-cP\succeq0$。
有限张量展开中，每个非全目标项都是正算子的张量积，故

$$
\sigma^{\otimes n}=(cP+R)^{\otimes n}\succeq c^nP^{\otimes n}.
\tag{C132.3}
$$

这个实际混态属于最小的 iid 零假设域，因此对每个所列域和全部集体效果均有
$\beta_{\mathcal N}(T)\ge c^n\alpha_n(T)$。
不需要假设最不利态为纯态，也未将不同最优值冒充同时达到。

反向对每个实际乘积逐项计算

$$
\operatorname{Tr}\bigl(P^{\otimes n}(\rho_1\otimes\cdots\otimes\rho_n)\bigr)
=\prod_{i=1}^n\operatorname{Tr}(P\rho_i)\le c^n.
\tag{C132.4}
$$

所有因子同时选 $P_{\phi_1}$（全域）或 $P_{u_+}$（承诺域）即达到等号，且已属 iid 域。
凸混合由线性性保持该上界。故 $tP^{\otimes n}$ 的风险恰为 $tc^n$、目标功效为 $t$，
给 (C132.2)，包括所有端点。

在承诺域，将同一个 C-130.1 固定字分别作用于每个新输入，记录每次末端比特，
仅当全部为一时宣告，实际效果就是 $F_0^{\otimes n}$。
由 (C130.3) 逐因子相乘，其零假设风险恰为 $(2/3)^n$，目标功效为一；
在乘积混合中仍成立。
最后只用一个概率 $t$ 的独立硬币决定是否保留整个宣告，才同时乘以 $t$。
若改为每个输入各用概率 $t$ 的独立硬币再要求全通过，效果是
$(tF_0)^{\otimes n}=t^nF_0^{\otimes n}$，目标功效变为 $t^n$。证毕。

乘积分支与复合 iid 族的框架见 Berta、Brandão、Hirche，
*On Composite Quantum Hypothesis Testing*，
[arXiv:1709.07268v2](https://arxiv.org/html/1709.07268v2)，式 (9)–(15)、Theorem 1.1，
[Commun. Math. Phys.](https://doi.org/10.1007/s00220-021-04133-8)。
该定理处理渐近误差指数，并要求每对备择／零假设的支持包含条件 (13)。
这里零假设含与 $\psi$ 正交的 $e_2$，故不能直接以其定理代替 (C132.3) 的有限 $n$ 逆向证明。
近期纯目标投影检验的对应见 Simpson、Palias、Jose，
*Sample Complexity of Composite Quantum Hypothesis Testing*，
[arXiv:2601.08588v4](https://arxiv.org/html/2601.08588v4)，§II.C 式 (5)–(7)、§III.C.1 Theorem 9／式 (15)。
其纯目标、紧致 iid 不确定集可取 $\mathcal F_{\rm all}$ 或压缩后的 $\mathcal F_Q$；
证明中的投影检验给先验权重 $p$ 下的对称错误上界 $(1-p)c^n$。
该达到机制与 (C132.4) 相符，但不提供本处固定风险的精确逆向界、原生实现或边缘约束结论。

## 133. 仅承诺各边缘为零假设时的联合前沿

**定义 C-133.1（边缘域与同边缘子域）。** 对同一个 $\mathcal F$，定义

$$
\begin{aligned}
\mathcal M_n(\mathcal F)&=\{\Omega\in\mathsf D(\mathcal K_3^{\otimes n}):
\Omega_i=\operatorname{Tr}_{\ne i}\Omega\in\mathcal F\ (\forall i)\},\\
\mathcal M_n^{=} (\mathcal F)&=\{\Omega\in\mathcal M_n(\mathcal F):
\Omega_1=\cdots=\Omega_n\}.
\end{aligned}
\tag{C133.1}
$$

允许任意复联合态，包括纠缠态。$\mathcal F=\mathcal F_Q$ 时，正性实际还迫使联合态支持于
$Q^{\otimes n}$：对每个位置，$\operatorname{Tr}((I-P_Q)_i\Omega)=0$，
正性使其支持落在每个局部投影的核，取交即得。
但该支持事实不使联合态成为独立乘积。

**定理 C-133.2（两条不随份数改善的精确前沿）。** 对每个 $n\ge1$、
$\delta\in[0,1]$，无论取 $\mathcal N=\mathcal M_n(\mathcal F)$ 还是 $\mathcal M_n^{=}(\mathcal F)$，
均有

$$
\begin{aligned}
A_{\mathcal N}(\delta)&=\min\{1,4\delta/3\}
&&\text{若 }\mathcal F=\mathcal F_{\rm all},\\
A_{\mathcal N}(\delta)&=\min\{1,3\delta/2\}
&&\text{若 }\mathcal F=\mathcal F_Q.
\end{aligned}
\tag{C133.2}
$$

达到效果分别为不限测量的 $tP^{\otimes n}$，以及承诺域可用的原生
$tF_0^{\otimes n}$；$t=\min\{1,\delta/c\}$，缩放仍需 C-130.2 的一个独立最终硬币。

证明。在全域取 $c=3/4$、$\tau=(P_C-P)/3$，在承诺域取
$c=2/3$、$\tau=P_{e_2}$。两种 $\tau$ 都是与 $P$ 正交的正迹一态，且

$$
\sigma=cP+(1-c)\tau\in\mathcal F,\qquad
\Omega_* = cP^{\otimes n}+(1-c)\tau^{\otimes n}
\succeq cP^{\otimes n}.
\tag{C133.3}
$$

$\Omega_*$ 为实际份间可分离态，全部边缘相同且恰为已展示的实际混态 $\sigma$。
故它已属于较小的同边缘子域；任意集体效果均满足
$\beta_{\mathcal N}(T)\ge c\alpha_n(T)$。
这给 (C133.2) 的逆向界，且无需纠缠联合见证。

另一方面，对于任意位置 $i$，

$$
P^{\otimes n}\preceq P_i\otimes I_{\ne i},\qquad
\operatorname{Tr}(P^{\otimes n}\Omega)\le\operatorname{Tr}(P\Omega_i)\le c.
\tag{C133.4}
$$

这里 $P_i$ 表示在第 $i$ 位置的单份投影。
$\Omega_*$ 在全目标投影上的概率恰为 $c$，故此上界可达，缩放得第一种达到效果。
承诺域同理有 $F_0^{\otimes n}\preceq(F_0)_i\otimes I_{\ne i}$，
由零假设边缘给风险至多 $2/3$；又 $F_0\psi=\psi$、$F_0e_2=0$，
所以同一 $\Omega_*$ 达到风险 $2/3$，目标通过概率一。
一个独立最终硬币完成缩放。证毕。

**命题 C-133.3（可分离与零假设因子混合的严格区别）。** 对 $n\ge2$，
(C133.3) 的 $\Omega_*$ 虽为可分离、置换不变且有相同零假设边缘，
却不属于 $\mathcal S_n(\mathcal F)$。$n=1$ 时它就是 $\sigma$，全部相应单输入域及前沿重合。

证明。$0<c<1$，故
$\operatorname{Tr}(P^{\otimes n}\Omega_*)=c>c^n$。
C-132.2 已给 $\mathcal S_n(\mathcal F)$ 上的同一重叠至多 $c^n$，矛盾。
可分离分解的每个因子允许为有资源的 $P$；零假设因子乘积混合则禁止这样的分支。
当 $n=1$，(C133.3) 直接化为 $\sigma$，且单份边缘就是态本身。证毕。

C-116.2 与 C-121.5 已在各自底面／历史任务中给出共同标签障碍；
这里 (C133.3) 把该机制接到固定物理 $\mathcal B$、八射线源、同一实际 $F_0$ 及尖锐逆向见证，
不是从那些任务的统计界偷换联合零假设。
独立通过概率与全好／全坏经典关联的成熟区分亦见 Zhu–Hayashi，
*Efficient Verification of Pure Quantum States in the Adversarial Scenario*，
[arXiv:1909.01900v2](https://arxiv.org/html/1909.01900v2)，式 (2)–(3) 及式 (4)–(5) 前的
“Adversarial scenario” 段，[Phys. Rev. Lett. 123, 260504](https://doi.org/10.1103/PhysRevLett.123.260504)。
该文测试若干系统后条件认证一个未测系统；这里是对已供应全部输入的宣告检验，二者任务不同。

## 134. 功效恰为一时的最少新输入与资源计数

**推论 C-134.1（独立输入的精确整数界）。** 对 C-132.1 的各域，
目标功效要求恰为一时，$0<\delta<1$ 下最少新输入数为

$$
n_{\min}(\delta;c)=\left\lceil\frac{\log\delta}{\log c}\right\rceil,
\qquad c=3/4\text{（全域放松）},\quad c=2/3\text{（承诺域原生）}.
\tag{C134.1}
$$

具体的相邻有理边界为

| 域与达到菜单 | 风险额度 $\delta$ | $n_{\min}$ | $c^{n_{\min}-1}>\delta$ | $c^{n_{\min}}\le\delta$ |
| --- | ---: | ---: | ---: | ---: |
| 全五维，不限测量放松 | $1/20$ | 11 | $59049/1048576$ | $177147/4194304$ |
| 全五维，不限测量放松 | $1/100$ | 17 | $43046721/4294967296$ | $129140163/17179869184$ |
| $Q$ 承诺，原生菜单 | $1/20$ | 8 | $128/2187$ | $256/6561$ |
| $Q$ 承诺，原生菜单 | $1/100$ | 12 | $2048/177147$ | $4096/531441$ |

证明。C-132.2 给功效一的充要条件 $c^n\le\delta$。
$\log c<0$，取对数并反向除法即得 (C134.1)。表中各数是相应幂的精确值；
交叉相乘给所列严格与非严格关系，因 $c^n$ 严格递减，正好确定最小整数。
若 $\delta=0$，任何有限 $n$ 都不能在功效一时达到；若 $\delta=1$，限定 $n\ge1$ 时最少为一。
在 C-133.1 的仅边缘域，功效一要求 $\delta\ge c$，与 $n$ 无关；
特别是这两个表列风险额度下，不存在任何有限 $n$ 的功效一方案。证毕。

**命题 C-134.2（原生达到实际消费的供应）。** 一次性选择 C-130.1 的某个固定有限字，
记其翻转数为有限但未评价的 $L_0$。在 $n$ 个新输入上的承诺域全通过构造消费
$n$ 份新输入、$n$ 个末端二值事件、$n$ 次这个固定字，即 $nL_0$ 个翻转，
指定 $S_{\star,3}$ 调用数为零。若显示缩放 $t<1$，还消费一个概率 $t$ 的独立最终硬币。
在 (C134.1) 的功效一边界使用未缩放全通过，故无需此缩放硬币。

证明。每份输入上完整执行同一字一次，再作其一次末端测量，最后取全部事件的合取。
计数逐项相加，零指定相位调用由 C-130.1 保持。
$L_0$ 只计固定 $O_{\rm ph}$ 字，不与 C-124.1 的可变 Ramsey 模板长度 $L$ 混同。
原生实现并不要求联合量子控制；任意联合输入上的局部测量全通过效果仍是张量积。
新输入的实际来源律则分别由 C-132.1 或 C-133.1 指定，不能由测量效果推出。证毕。

## 135. 制备、信息供应与原恢复目标的边界

**命题 C-135.1（支持承诺不能替代物理相干数零假设）。**
$P$ 支持于 $Q$，在逻辑列基中是一支持态，却在物理能量基 $\mathcal B$ 中恰为四支持纯态，
故 $P\notin\mathcal F_Q$。另一方面，$P_{e_2},P_\eta\in\mathcal F_Q$。
所以仅凭 $Q$ 支持、或把逻辑 qutrit 中至多三支持作为零假设，均不能得到本处的认证问题。
全域逆向见证 $\sigma_{\rm all}$ 也不能用作承诺域见证。

证明。$\psi=(b_1+b_2+b_3+b_4)/2$，目标有四个非零物理能量振幅。
纯态的每个正权重分解向量都位于其一维支持，故不存在三支持分解。
$e_2,\eta$ 的物理支持计数已由 C-129.1 给出。
逻辑三维的所有纯向量都至多三支持，特别包括目标；
若零假设含目标，则任何功效一的效果已有风险至少一。
此外由 (C131.3)，

$$
\operatorname{Tr}((I-P_Q)\sigma_{\rm all})
=\frac{\operatorname{Tr}((I-P_Q)P_C)}{12}
=\frac{3/2}{12}=\frac18>0.
\tag{C135.1}
$$

所以 $\sigma_{\rm all}$ 实际不在 $\mathsf D(Q)$，不能跨域借用。
例如 $\tfrac12(P_{e_0}+P_{e_4})=\tfrac12(P_\psi+P_z)$，
$z=(e_0-e_4)/\sqrt2\perp Q$，虽抵消了相应非对角项，仍有 $1/2$ 的支撑泄漏。证毕。

**命题 C-135.2（固定目标功效与后验概率的两个反例）。**
全域达到效果 $P$ 不对所有四相干纯态统一有正功效。
承诺域八输入全通过的风险小于 $1/20$，也不推出通过后的目标后验概率至少 $19/20$。

证明。归一化向量

$$
x=(b_1+b_2-b_3-b_4)/2
\tag{C135.2}
$$

有四个非零物理能量振幅，却与 $\psi$ 正交，故 $\operatorname{Tr}(PP_x)=0$。
它还属于 $C$，所以 $F_0$ 在它上的通过概率也为零。
再取只含两个假设的明确先验：目标 $P^{\otimes8}$ 的概率为 $1/1000$，
零假设 $P_{u_+}^{\otimes8}$ 的概率为 $999/1000$。
C-130.1 给目标全通过概率一，零假设全通过概率 $256/6561<1/20$。
Bayes 公式却给

$$
\Pr(\text{目标}\mid\text{全通过})
=\frac{1}{1+999\cdot256/6561}=\frac{243}{9715}.
\tag{C135.3}
$$

因此频率学最坏零假设风险与数据后的先验依赖概率是不同量。证毕。

**命题 C-135.3（额外副本与假设相关旗标改变模型）。**
对全部 $Q$ 支持密度态，没有一个输入上的线性通道可自动供应其独立张量平方。
若另行供应可访问且与实际假设相关的旗标，C-131–C-133 的输入内逆向界不再适用于该扩充问题。

证明。假设通道 $\Lambda$ 对全部 $\rho\in\mathsf D(Q)$ 满足
$\Lambda(\rho)=\rho\otimes\rho$。它在 $P,P_{e_2}$ 上的该作用及线性性，迫使

$$
\Lambda(\sigma_Q)=\frac23P^{\otimes2}+\frac13P_{e_2}^{\otimes2}.
\tag{C135.4}
$$

但 $\sigma_Q^{\otimes2}$ 在 $P\otimes P_{e_2}$ 上的期望为 $2/9$，
(C135.4) 的同一期望为零，矛盾。
故将一个未知输入重置、再访问或重复控制，不能当作本处 $n$ 个独立新输入的服务。
此反例仅用线性性，不否认另行供应源的制备能力。

对旗标例子，把目标改为 $P^{\otimes n}\otimes|1\rangle\langle1|$，
每个零假设联合态改为 $\Omega\otimes|0\rangle\langle0|$。
读取效果 $I\otimes|1\rangle\langle1|$ 即有功效一、风险零。
这是额外输入相关信息，违反 C-131.1 效果约化所需的共同输入无关辅助供应，
不反驳原输入域上的正序见证。设置也不能依赖尚未知的实际假设标签。证毕。

**适用边界 C-135.4（源与恢复的不同义务）。** (C129.1)–(C133.4) 的固定模型组合
连接实际 $E$ 源、同一物理 $\mathcal B$、八射线零假设、原生 $F_0$ 与各自联合输入域。
标准多级相干见证、正序支配、张量正性、效果约化与关联反例均是中间工具；
其一般数学不作为新增资源定理，固定模型综合亦不附全域原创性或优先权断言。

精确有限字的供应仅在理想无漂移独立控制合同内成立，未给已评价的脉冲参数表、
数值 $L_0$、精度或漂移容错界、硬件实现与物理时长。
支持承诺、$\psi$ 或其他 $E$ 输出的制备、承诺真实性的认证、独立新输入供应、
校准、相位时钟及 SSR／参考系兼容性仍需各自额外前提。
这里不引入数超选择规则下的新有限参考模型。
$Q$ 的固定相干关系作为数学定义存在，不等于制备或参考供应。
全部前沿为理想模型内的普通数学结果；本处不作形式内核核验或经验实现断言。
全五维的 $tP^{\otimes n}$ 只给不限测量放松的达到，
全五维原生最优值及其实现未在此确定；承诺域的原生达到不能跨越这个供应边界。

[相位增益与 qutrit 恢复卷定义 6.2](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#6-class-optimization-and-remaining-mathematical-obligations)
中，正 $\beta$、整个实 Kraus 编码器类 $M_3\to M_5$ 的尖锐 diamond 恢复曲线仍未解决。
认证目标态的风险—功效前沿既不构造该类的统一恢复通道，也不证明其全类尖锐性，
原恢复目标及其全部输入、参考与共同恢复量词保持原义。

## 追加锚（本行以下为增补区）

## 136. 同一五态源上的数守恒效应与已供应参考

**定义 C-136.1（物理粒子数与固定源的记号）。** 保持 (C128.1)–(C128.2)
的物理五态、能量基 $\mathcal B$、$\psi,\eta,Q,P_Q,P$ 及两个零假设域不变，记

$$
\begin{aligned}
\widehat N&=\operatorname{diag}(0,1,1,1,2)_{(e_0,e_1,e_2,e_3,e_4)},\\
S&=\operatorname{span}(e_0,e_4),\qquad \Pi_S=P_{e_0}+P_{e_4},\\
\psi_-&=(e_0-e_4)/\sqrt2,\qquad P_-=P_{\psi_-}.
\end{aligned}
\tag{C136.1}
$$

$\widehat N$ 是物理粒子数算符，不是恢复问题中的通道 $N$。
(C128.1) 的等距矩阵 $E=(\psi,\eta,e_2)$ 在此亦记作 $E_N$；
它始终是固定嵌入 $\mathbb C^3\to\mathcal K_3$，不是以下联合宣告效果 $\mathsf E$。
相干数仍按物理能量基 $\mathcal B$ 定义，不按 $\widehat N$ 的本征基定义。
复振幅、全部有限混态分解及 $\mathcal F_Q=\mathcal F_{\rm all}\cap\mathsf D(Q)$
的量词均沿用 C-128.1、C-129.1。

**假设 C-136.2（单输入与参考的共同供应）。** 每次试验供应一份未知系统输入，
目标为 $P$，零假设为 $\mathcal F_{\rm all}$ 或 $\mathcal F_Q$ 中的任意态。
参考空间 $R$ 为有限维，带固定整数电荷表示
$\widehat N_R=\sum_\ell\ell R_\ell$；允许各电荷有简并。
若供应参考，则它是一个固定、已给定的密度态 $\zeta$，与系统输入独立，
目标和每个零假设下均为同一个 $\zeta$。每次试验重新供应一份；
不附参考返还、保持、跨试验复用、重置或制备服务。
所有设置均不依赖未知的实际假设标签，也不附额外源副本或可访问的标签旗标。

**定义 C-136.3（新声明的测量比较菜单）。** 无参考时允许全部
$0\preceq T\preceq I$、$[T,\widehat N]=0$ 的系统效果。
有参考时允许全部

$$
0\preceq\mathsf E\preceq I,\qquad
[\mathsf E,L]=0,\qquad
L=\widehat N\otimes I_R+I\otimes\widehat N_R.
\tag{C136.2}
$$

这是按效果声明的数学菜单，未把 C-130.1 的独立翻转、相位调用预算与末端
$n_1$ PVM 合成能力扩充为 (C136.2)。无条件宣告概率为

$$
\alpha^\zeta(\mathsf E)=\operatorname{Tr}(\mathsf E(P\otimes\zeta)),\qquad
\beta^\zeta_{\mathcal F}(\mathsf E)
=\sup_{\rho\in\mathcal F}\operatorname{Tr}(\mathsf E(\rho\otimes\zeta)).
\tag{C136.3}
$$

令 $A^0_{\mathcal F}(\delta)$ 为无参考菜单在
$\beta_{\mathcal F}(T)\le\delta$ 下的最大目标功效，
$A^\zeta_{\mathcal F}(\delta)$ 为 (C136.2) 在
$\beta^\zeta_{\mathcal F}(\mathsf E)\le\delta$ 下的最大目标功效，$0\le\delta\le1$。
下文的构造与有限维紧性给出这些最大值的存在。
不加上标的 $A_{\mathcal F}$ 保留 C-128.2 的不限系统效果含义。
效果只规定一个事件的概率，不规定条件输出态或测量仪器。

## 137. 无参考前沿与任意有限参考下的承诺不增益

**定理 C-137.1（全域与承诺域的分别逆向界和达到）。** 在 C-136.2 的共同供应下，
对每个 $\delta\in[0,1]$ 及每个固定有限参考 $\zeta$，

$$
A^0_{\mathcal F_{\rm all}}(\delta)=\delta,\qquad
A^0_{\mathcal F_Q}(\delta)
=A^\zeta_{\mathcal F_Q}(\delta)=\min\{1,3\delta/2\}.
\tag{C137.1}
$$

证明。令 $\mathcal D_{\widehat N}$ 为物理粒子数去相位。
$e_0,e_4$ 各只有两个非零 $\mathcal B$ 坐标，故

$$
\mathcal D_{\widehat N}(P)=\tfrac12(P_{e_0}+P_{e_4})\in\mathcal F_{\rm all}.
\tag{C137.2}
$$

对每个数守恒 $T$，
$\alpha(T)=\operatorname{Tr}(T\mathcal D_{\widehat N}(P))
\le\beta_{\mathcal F_{\rm all}}(T)$。
反向取 $T=\delta\Pi_S$，其功效为 $\delta$，风险至多 $\delta$；
零假设 $P_{e_0}$ 达到此风险，故第一式是全部复数、混态零假设下的精确前沿。

承诺域使用固定嵌入的压缩恒等式

$$
P_Q\Pi_SP_Q=P,
\tag{C137.3}
$$

因为 $\Pi_S\psi=\psi$、$\Pi_S\eta=\Pi_Se_2=0$。
由 C-129.1 的完整八射线凸包，承诺域的最大目标重叠恰为 $2/3$。
所以数守恒效果 $T=t\Pi_S$ 的承诺风险为 $2t/3$、目标功效为 $t$。
取 $t=\min\{1,3\delta/2\}$ 给出达到。

逆向直接消费 (C131.4) 的实际混态见证
$\sigma_Q=\frac23P+\frac13P_{e_2}\in\mathcal F_Q$。
对任意固定 $\zeta\succeq0$、$\operatorname{Tr}\zeta=1$，有

$$
\sigma_Q\otimes\zeta\succeq\tfrac23P\otimes\zeta,
\qquad
\beta^\zeta_{\mathcal F_Q}(\mathsf E)
\ge\operatorname{Tr}(\mathsf E(\sigma_Q\otimes\zeta))
\ge\tfrac23\alpha^\zeta(\mathsf E).
\tag{C137.4}
$$

它约束每个正联合效果，甚至不必假定其数守恒；结合功效至多一给所需上界。
$\mathsf E=t\Pi_S\otimes I_R$ 满足 (C136.2)，并在每个 $\zeta$ 下达到上述风险与功效。
这同时涵盖混参考、简并电荷及 $\delta=0,2/3,1$。
(C137.2) 不能用于承诺域的逆向界：$\psi_-\perp Q$，且
$\operatorname{Tr}((I-P_Q)\mathcal D_{\widehat N}(P))=1/2$。
这里复用 C-129.1 的复数分类和混态支撑桥、C-131.1 的正序见证，不另作分类证明。证毕。

## 138. 指定两电荷参考的全部复效果及其精确约化域

**定义 C-138.1（指定的一份参考）。** 取

$$
R=\operatorname{span}(f_0,f_2),\qquad
\widehat N_Rf_0=0,\quad\widehat N_Rf_2=2f_2,\qquad
r=(f_0+f_2)/\sqrt2,\quad\zeta_r=P_r.
\tag{C138.1}
$$

$A^r_{\mathcal F}$ 是 $A^{\zeta_r}_{\mathcal F}$ 的简记。
$e_if_j$ 表示 $e_i\otimes f_j$，不把两个参考电荷误作额外系统能级。

**定理 C-138.2（全部联合块与相同功效下的全域约化）。** 对 (C138.1)，
(C136.2) 的全部允许效果恰为下表总电荷块上的 Hermitian 正收缩算符：

| 总电荷 | 有序基 | 维数 | 效果块 |
| --- | --- | ---: | --- |
| $0$ | $e_0f_0$ | 1 | $x_0$ |
| $1$ | $e_1f_0,e_2f_0,e_3f_0$ | 3 | $A_1$ |
| $2$ | $e_0f_2,e_4f_0$ | 2 | $M$ |
| $3$ | $e_1f_2,e_2f_2,e_3f_2$ | 3 | $A_3$ |
| $4$ | $e_4f_2$ | 1 | $x_4$ |

即 $\mathsf E=x_0\oplus A_1\oplus M\oplus A_3\oplus x_4$，
$0\le x_0,x_4\le1$、$0\preceq A_1,A_3\preceq I_3$、$0\preceq M\preceq I_2$，
初始块允许任意复非对角元。其有效系统效果为

$$
\begin{aligned}
T&=(I\otimes\langle r|)\mathsf E(I\otimes|r\rangle)=T_S\oplus H,\\
T_S&=\frac12\begin{pmatrix}x_0+M_{11}&M_{12}\\M_{21}&M_{22}+x_4\end{pmatrix}_{(e_0,e_4)},
\qquad H=\frac{A_1+A_3}{2}\quad\text{于 }\operatorname{span}(e_1,e_2,e_3).
\end{aligned}
\tag{C138.2}
$$

对全零假设 $\mathcal F_{\rm all}$，每个允许复效果在相同目标功效下，
均可换成风险不增加的允许效果，其有效形式为

$$
T(a,c)=\begin{pmatrix}a&c\\c&a\end{pmatrix}_{(e_0,e_4)}\oplus0,
\qquad 0\le c\le\tfrac14,\quad c\le a\le1-c.
\tag{C138.3}
$$

此实参数域中的每一点反过来均由允许联合效果实现。

证明。总电荷块维数为 $1+3+2+3+1=10$，对易恰排除异块矩阵元。
直接与 $r$ 收缩得 (C138.2)。参考没有电荷差一模式，故系统粒子数一子空间
与 $S$ 之间没有有效矩阵元，未对 $A_1,A_3,M$ 作实数假设。

先将 $A_1,A_3$ 置零。这删除正块 $H$，保持目标功效，且每个零假设上的接受概率不增加。
定义基置换 $V,J$ 为

$$
\begin{gathered}
Ve_0=e_4,\quad Ve_4=e_0,\quad Ve_1=e_2,\quad Ve_2=e_1,\quad Ve_3=e_3,\\
Jf_0=f_2,\quad Jf_2=f_0,\quad W=V\otimes J.
\end{gathered}
\tag{C138.4}
$$

有 $V\widehat NV^\dagger=2I-\widehat N$、
$J\widehat N_RJ^\dagger=2I-\widehat N_R$、$Jr=r$，从而
$WLW^\dagger=4I-L$。
所以 $\mathsf E\mapsto W\mathsf EW^\dagger$ 将允许效果映回允许效果；
与原效果取平均仍合法。它保持目标，因为 $V\psi=\psi$。
同时 $V$ 在能量基上置换为

$$
(b_1,b_2,b_3,b_4,b_5)\longmapsto(b_3,b_4,b_1,b_2,b_5).
\tag{C138.5}
$$

因此它双向保持每个复三支持纯态集合，进而保持全部有限凸混合
$V\mathcal F_{\rm all}V^\dagger=\mathcal F_{\rm all}$。
平均后风险不超过两个相同风险的平均，目标功效不变。
有效二阶块于是有相等对角元 $a$ 和实非对角元 $c$。
这是允许效果集合中的数学对称化，不安装 $V$ 或 $J$ 为可执行门；
不要求、也不使用 $V$ 保持 $Q$。

若 $c<0$，功效 $p=a+c\in[0,1]$，而零假设 $P_{e_0}$ 给风险至少 $a\ge p$。
改取允许效果 $p\Pi_S\otimes I_R$，功效和全域风险均为 $p$。
因此相同功效的全域最优化可限制到 $c\ge0$。

对称化后的联合非零块写成

$$
x_0=x_4=x,\qquad M=\begin{pmatrix}b&2c\\2c&b\end{pmatrix}.
\tag{C138.6}
$$

块约束精确为 $0\le x\le1$、$2c\le b\le1-2c$，且 $a=(x+b)/2$。
这给出 (C138.3) 的必要性。反向给定该域中的 $(a,c)$，取
$b=\max\{2c,2a-1\}$、$x=2a-b$。
由 $c\le1/4$、$a\le1-c$ 得 $b\le1-2c$；由 $a\ge c$ 得 $b\le2a$，
故 $x\ge0$，而 $b\ge2a-1$ 得 $x\le1$。
所有块约束均成立，(C138.2) 恰实现指定 $T(a,c)$。
这证明精确域与全部复效果的约化，而非对某个实效果子类的猜测。证毕。

## 139. 十个复能量压缩与指定参考的精确全域风险

**定理 C-139.1（固定模型中的全部压缩谱）。** 在 (C138.3) 的参数域内，令

$$
d(a,c)=\sqrt{a^2/16+c^2/2},\qquad q_\pm(a,c)=3a/4\pm d(a,c).
\tag{C139.1}
$$

$T(a,c)$ 在所有复数与有限混合零假设上的精确风险为

$$
\beta_{\mathcal F_{\rm all}}(T(a,c))
=q(a,c):=q_+(a,c)=\frac{3a}{4}+\sqrt{\frac{a^2}{16}+\frac{c^2}{2}}.
\tag{C139.2}
$$

证明。对任意 Hermitian $T$，令 $\Pi_J=\sum_{j\in J}P_{b_j}$。
本题中三支持纯向量均位于某个 $|J|=3$ 的坐标子空间，复 Rayleigh 原理及线性性给

$$
\beta_{\mathcal F_{\rm all}}(T)
=\max_{\substack{J\subseteq\{1,\ldots,5\}\\|J|=3}}
\lambda_{\max}\!\left((\Pi_JT\Pi_J)|_{\operatorname{ran}\Pi_J}\right).
\tag{C139.3}
$$

每个最大特征向量本身就是归一化三支持复零假设，故右端是实际达到的风险；
支持小于三与有限凸混合均已包含。这消费固定基多级相干的标准主压缩条件，
取 Ringbauer 等 [arXiv:1707.05282v3](https://arxiv.org/pdf/1707.05282v3)
式 (1)、Theorem 2／式 (10) 中的 $d=5,k=3,W=\delta I-T$。
此一般工具在下列固定矩阵计算内使用。

由 (C128.1)，

$$
[T(a,c)]_{\mathcal B}=\frac12
\begin{pmatrix}
a&a&c&c&0\\a&a&c&c&0\\c&c&a&a&0\\c&c&a&a&0\\0&0&0&0&0
\end{pmatrix}.
\tag{C139.4}
$$

十个压缩的全部三个特征值（含重数）如下，指标均指固定能量基：

| $J$ | $\operatorname{spec}((\Pi_JT(a,c)\Pi_J)|_{\operatorname{ran}\Pi_J})$ |
| --- | --- |
| $\{1,2,3\}$ | $0,q_-(a,c),q_+(a,c)$ |
| $\{1,2,4\}$ | $0,q_-(a,c),q_+(a,c)$ |
| $\{1,3,4\}$ | $0,q_-(a,c),q_+(a,c)$ |
| $\{2,3,4\}$ | $0,q_-(a,c),q_+(a,c)$ |
| $\{1,2,5\}$ | $0,0,a$ |
| $\{3,4,5\}$ | $0,0,a$ |
| $\{1,3,5\}$ | $0,(a-c)/2,(a+c)/2$ |
| $\{1,4,5\}$ | $0,(a-c)/2,(a+c)/2$ |
| $\{2,3,5\}$ | $0,(a-c)/2,(a+c)/2$ |
| $\{2,4,5\}$ | $0,(a-c)/2,(a+c)/2$ |

第一类的重复坐标反对称组合为零方向，其余二阶矩阵为
$\begin{pmatrix}a&c/\sqrt2\\c/\sqrt2&a/2\end{pmatrix}$，特征方程给 $q_\pm$。
第二类只剩一个相同坐标对，第三类只剩跨两对的一行一列，分别给表中余谱。
由 $a\ge c\ge0$，$q_+\ge a\ge(a+c)/2$，所以 (C139.3) 的最大值恰为 (C139.2)。
当 $a=c=0$ 时表中全部特征值均为零。
这枚举的是复 Hilbert 空间上的全部主压缩，而非实振幅抽样。证毕。

## 140. 指定参考的固定功效最优效果与闭式前沿

**定理 C-140.1（残余反对称响应与两处分段阈值）。** 对 (C138.1) 的参考和全部
$\delta\in[0,1]$，令

$$
\delta_*=(9+\sqrt{17})/16.
\tag{C140.1}
$$

全零假设前沿为

$$
A^r_{\mathcal F_{\rm all}}(\delta)=g(\delta):=
\begin{cases}
4\delta/3,&0\le\delta\le3/8,\\[3pt]
(1+6\delta-\sqrt{1+4\delta^2})/4,&3/8\le\delta\le\delta_*,\\[3pt]
1,&\delta_*\le\delta\le1.
\end{cases}
\tag{C140.2}
$$

在每个固定目标功效 $p\in[0,1]$，可取最小风险有效效果

$$
T_p=pP+\max\{0,p-1/2\}P_-.
\tag{C140.3}
$$

证明。C-138.2 将每个允许复联合效果在相同功效下约化到风险不增的 $T(a,c)$。
置 $p=a+c$，则 (C138.3) 的精确域等价于

$$
0\le p\le1,\qquad0\le c\le\min\{p/2,1/4\},\qquad
T(a,c)=pP+(p-2c)P_-.
\tag{C140.4}
$$

固定 $p$ 增大 $c$ 时，$T(a,c)$ 按正半定序减小，
故每个零假设的接受概率及其上确界均不增加。
取最大的允许 $c$ 就得到 (C140.3)。因此它既给达到候选，也给全部允许效果的逆向界。
代入 (C139.2) 得固定功效的精确最小风险

$$
r_{\min}(p)=
\begin{cases}
3p/4,&0\le p\le1/2,\\[3pt]
\bigl(3(p-1/4)+\sqrt{(p-1/4)^2+1/2}\bigr)/4,&1/2\le p\le1.
\end{cases}
\tag{C140.5}
$$

两支在 $p=1/2$ 一致，值为 $3/8$；在 $p=1$ 值为 $\delta_*$。
第一支严格递增；第二支以 $a=p-1/4$ 写，其导数为
$3/4+a/(4\sqrt{a^2+1/2})>0$。
故 $r_{\min}$ 连续且严格递增，所有风险额度的最优功效由反解及功效上限一确定。

在曲线支，$4\delta-3a=\sqrt{a^2+1/2}\ge0$。
平方给 $8a^2-24\delta a+16\delta^2-1/2=0$；
两根中加号根使 $4\delta-3a<0$，故只能取
$a=(6\delta-\sqrt{1+4\delta^2})/4$。
加上 $1/4$ 即为 (C140.2) 中支。
两公共端点分别给 $p=1/2,1$，与直线及饱和支一致。
下一定理给每个 $p$ 的允许联合效果，故此逆向界对全部 $\delta$ 实际达到。证毕。

## 141. 逐点联合达到、参考增益与锐效果边界

**定理 C-141.1（全部风险额度上的守恒联合效果）。** 定义

$$
\chi=(e_0f_2+e_4f_0)/\sqrt2,\qquad
B_0=P_{e_0f_0},\quad B_4=P_{e_4f_2}.
\tag{C141.1}
$$

对每个 $p\in[0,1]$，效果

$$
\mathsf E_p=
\begin{cases}
2pP_\chi,&0\le p\le1/2,\\[3pt]
P_\chi+(2p-1)(B_0+B_4),&1/2\le p\le1
\end{cases}
\tag{C141.2}
$$

在其余子空间为零，满足 (C136.2)，有效效果恰为 $T_p$。
取 $p=g(\delta)$ 对每个 $\delta\in[0,1]$ 达到 (C140.2)。

证明。三个投影互相正交，分别位于总电荷 $2,0,4$，
且所有系数均在 $[0,1]$，故 $0\preceq\mathsf E_p\preceq I$、$[\mathsf E_p,L]=0$。
当 $p\le1/2$，(C138.2) 给 $a=c=p/2$，即有效效果 $pP$；
当 $p\ge1/2$，给 $a=p-1/4,c=1/4$，即 $pP+(p-1/2)P_-$。
目标功效为 $p$，全域风险由 C-139.1 精确等于 $r_{\min}(p)$。
$\delta=0$ 取零效果；$\delta=3/8$ 取 $P_\chi$；
$\delta=\delta_*$ 取 $P_\chi+B_0+B_4$。
整个 $\delta\ge\delta_*$ 区间继续用后一效果，风险为 $\delta_*\le\delta$、功效为一，
无需用尽风险额度。所有假设均使用同一份规定参考态。证毕。

**推论 C-141.2（四个前沿及功效一的风险阈值）。** 结合 C-137.1、C-131.1，
全部 $\delta\in[0,1]$ 上有

| 测量菜单 | $\mathcal F_{\rm all}$ 前沿 | $\mathcal F_Q$ 前沿 | 全域功效一的最小风险 | 承诺域功效一的最小风险 |
| --- | --- | --- | --- | --- |
| 无参考、全部数守恒系统效果 | $\delta$ | $\min\{1,3\delta/2\}$ | $1$ | $2/3$ |
| 一份指定 $r$、全部总数守恒联合效果 | $g(\delta)$ | $\min\{1,3\delta/2\}$ | $(9+\sqrt{17})/16$ | $2/3$ |
| 不限系统效果的比较放松 | $\min\{1,4\delta/3\}$ | $\min\{1,3\delta/2\}$ | $3/4$ | $2/3$ |

无参考的承诺增益为 $\min\{1,3\delta/2\}-\delta$。
指定参考在全域上的额外增益精确为

$$
g(\delta)-\delta=
\begin{cases}
\delta/3,&0\le\delta\le3/8,\\[3pt]
(1+2\delta-\sqrt{1+4\delta^2})/4,&3/8\le\delta\le\delta_*,\\[3pt]
1-\delta,&\delta_*\le\delta\le1,
\end{cases}
\qquad A^r_{\mathcal F_Q}(\delta)-A^0_{\mathcal F_Q}(\delta)=0.
\tag{C141.3}
$$

证明。前三个定理及 (C131.1) 分别给表中各行，取前沿首次等于一的位置得阈值。
逐支相减得 (C141.3)。中支的 $1+2\delta>\sqrt{1+4\delta^2}$ 对 $\delta>0$ 成立，
所以全域参考增益在 $0<\delta<1$ 严格为正，在两端为零。
承诺域恒等来自 C-137.1 的同一混态逆向见证，不是对参考形状的数值观察。证毕。

**命题 C-141.3（有效 $tP$ 与功效一不是同一锐测量要求）。** 在指定参考模型中，
$0\le t\le1$ 时，全五维有效效果 $tP$ 可实现当且仅当 $t\le1/2$。
功效一则可达到，其 (C140.3) 最优代表为
$T_1=P+\frac12P_-$，不同于全空间的锐效果 $P$。

证明。充分性由 (C141.2) 的第一支给出。
必要性不预设对称实效果：若某个允许复联合效果的有效效果为 $tP$，
(C138.2) 中 $M$ 是二阶正收缩算符，故 $|M_{12}|\le1/2$，
因为 $\|M-I_2/2\|\le1/2$，其非对角元模亦至多 $1/2$。
因此所有允许有效效果均有 $|T_{04}|\le1/4$，而 $tP$ 的该元为 $t/2$，故 $t\le1/2$。
功效一时 (C141.2) 第二支已经给出实际允许效果。
在约化族中，固定功效 $p>1/2$ 必须保留至少 $p-1/2$ 的 $P_-$ 响应，
因为 $p-2c\ge p-1/2$。
另一方面，承诺域内 $P_Q\Pi_SP_Q=P$，
所以 $\Pi_S$ 在 $Q$ 上与锐 $P$ 有相同事件统计，仍不等于全空间效果 $P$。
以上均是概率效果的陈述，不推出仪器、可重复性、参考保持或非扰动。证毕。

## 142. 任意有限参考的精确半定规划与缺失差二模式的结论

**定理 C-142.1（固定有限参考的精确优化及最大值存在）。** 对 C-136.2
中的每个固定有限参考态和整数电荷表示，定义线性有效效果映射

$$
\Phi_\zeta(\mathsf E)
=\operatorname{Tr}_R\!\left[(I\otimes\sqrt\zeta)\mathsf E(I\otimes\sqrt\zeta)\right].
\tag{C142.1}
$$

令 $\Gamma_q$ 为 $L$ 的谱投影，$I_q$ 为其子空间恒等算符。
$A^\zeta_{\mathcal F_{\rm all}}(\delta)$ 精确等于下列有限 Hermitian 半定规划的最大值：

$$
\begin{aligned}
\text{最大化}\quad&\operatorname{Tr}(P\Phi_\zeta(\mathsf E)),\\
\text{约束}\quad&\mathsf E=\bigoplus_q\mathsf E_q,\qquad0\preceq\mathsf E_q\preceq I_q,\\
&\Pi_J\Phi_\zeta(\mathsf E)\Pi_J\preceq\delta\Pi_J
\quad\text{对每个 }J\subseteq\{1,\ldots,5\},\ |J|=3.
\end{aligned}
\tag{C142.2}
$$

承诺域将十个压缩约束换成 C-129.1 八射线 $w$ 的八个标量约束
$\langle w|\Phi_\zeta(\mathsf E)|w\rangle\le\delta$，其最大值恒为
$\min\{1,3\delta/2\}$。

证明。正夹心和偏迹给 $0\preceq\Phi_\zeta(\mathsf E)\preceq I$；
上界使用 $\Phi_\zeta(I)=\operatorname{Tr}_R(I\otimes\zeta)=I$。
迹的循环性给每个系统密度态的恒等式

$$
\operatorname{Tr}(\Phi_\zeta(\mathsf E)\rho)
=\operatorname{Tr}(\mathsf E(\rho\otimes\zeta)).
\tag{C142.3}
$$

不要求 $\zeta$ 满秩、纯或与 $\mathsf E$ 对易。
(C139.3) 的复主压缩条件使十个 LMI 精确等价于全部有限混合全零假设的风险约束；
总电荷块条件精确等价于 (C136.2)。固定 $\zeta$ 后，所有映射和约束均为线性或半定的。
有限个正收缩块的直积是紧集，十个 LMI 切出闭子集，且零效果在全部 $\delta\in[0,1]$ 可行。
连续线性目标在非空紧集上取得最大值，不需严格可行性前提。
承诺域的八个约束由 (C129.3) 精确给出；其值和达到效果已由 C-137.1 证明。
这给任意混参考及简并电荷的精确有限优化，不给一般 $\zeta$ 的全域闭式公式。证毕。

**定理 C-142.2（无参考差二模式时的全域前沿）。** 若固定参考满足

$$
R_{\ell+2}\zeta R_\ell=0\qquad\text{对所有整数 }\ell,
\tag{C142.4}
$$

则对全部 $\delta\in[0,1]$，有 $A^\zeta_{\mathcal F_{\rm all}}(\delta)=\delta$。

证明。选参考电荷本征基 $f_\alpha$，电荷为 $\ell_\alpha$，
简并指标保留在 $\alpha$ 中。由 (C142.3)，有效矩阵元为

$$
T_{ij}=\sum_{\alpha,\beta}\mathsf E_{i\alpha,j\beta}\zeta_{\beta\alpha},
\qquad
\mathsf E_{i\alpha,j\beta}\ne0\ \Longrightarrow\
n_i+\ell_\alpha=n_j+\ell_\beta,
\tag{C142.5}
$$

其中 $(n_0,n_1,n_2,n_3,n_4)=(0,1,1,1,2)$。
$i=0,j=4$ 时，允许项须有 $\ell_\alpha=\ell_\beta+2$。
(C142.4) 及其伴随使相应 $\zeta_{\beta\alpha}$ 全为零，故 $T_{04}=0$。
于是目标功效与风险满足

$$
\operatorname{Tr}(TP)=\tfrac12(T_{00}+T_{44})
\le\max\{T_{00},T_{44}\}\le\beta_{\mathcal F_{\rm all}}(T),
\tag{C142.6}
$$

最后一步只用 $P_{e_0},P_{e_4}\in\mathcal F_{\rm all}$。
即使参考有差一模式，其他有效矩阵元也不改变此论证。
$\mathsf E=\delta\Pi_S\otimes I_R$ 给风险和功效均为 $\delta$ 的守恒达到。
指定参考 $P_r$ 去相位后满足 (C142.4)，故其全域增益消失。
此结论只有所写方向；存在差二模式本身不在此推出任意参考的严格增益、
某条统一闭式曲线或充分实现条件。一般情形保留 (C142.2) 的精确有限规划。证毕。

## 143. 源承诺、能量相干与参考资源的适用范围

**命题 C-143.1（支持承诺与粒子数对称性不同）。** $Q$ 不在一般物理粒子数
$U(1)$ 作用下不变，$\mathcal F_{\rm all}$ 也不是该作用的不变态集合。
因此 (C137.1)、(C140.2) 比较的是在明确供应条件下的检测能力，
不把源承诺或给定参考的制备成本定为零。

证明。$\psi_-\perp Q$，并且

$$
e^{-i\theta\widehat N}\psi
=e^{-i\theta}(\cos\theta\,\psi+i\sin\theta\,\psi_-).
\tag{C143.1}
$$

当 $\sin\theta\ne0$ 时该向量不在 $Q$。
另一方面，$P_{b_1}\in\mathcal F_{\rm all}$ 是一支持能量零假设，
但 $b_1=(e_0-e_1)/\sqrt2$ 具有粒子数差一相干，故
$[P_{b_1},\widehat N]\ne0$。
物理能量基相干数、数守恒测量限制和源的支持承诺是三个不同条件。
(C137.3) 解释承诺域中数守恒效果何以已给目标统计，却不供应支持于 $Q$ 的源，
也不认证其承诺真实性或建立其 SSR／参考系制备兼容性。证毕。

**约定 C-143.2（引文的条件与固定模型增量）。** 固定基相干凸包、纯态最大
三项权重和主压缩条件使用 Ringbauer 等，
*Certification and Quantification of Multilevel Quantum Coherence*，
[arXiv:1707.05282v3](https://arxiv.org/pdf/1707.05282v3)，式 (1)、式 (9)、Theorem 2／式 (10)。
在这里取同一 $\mathcal B$、$d=5,k=3,W=\delta I-T$；
纯态重叠和混态正序见证已经用于 C-131.1，未作为新增一般相干理论重立。

先验输入信息与已供应不对称资源态对测量能力的不同作用，见 Ahmadi、Jennings、Rudolph，
*The WAY theorem and the quantum resource theory of asymmetry*，
[arXiv:1209.0921v1](https://arxiv.org/pdf/1209.0921v1)，
Section II E.1 “The possession of prior information” 与
Section II E.2 “The possession of asymmetry resource states”。
该文的测量／区分论证带有自己的本征态系综和装置条件；
这里仅借用先验与资源供应须分列的背景，不从该文导出八射线或四个本模型前沿。

电荷模式的必要性背景见 Marvian、Spekkens，
*Modes of asymmetry: the application of harmonic analysis to symmetric quantum dynamics and quantum reference frames*，
[arXiv:1312.0680v2](https://arxiv.org/pdf/1312.0680v2)，Sections II、V，Lemma 17、Proposition 18。
这些条目以给定参考态与 $G$ 协变联合模拟通道为前提，给出必要模式包含关系。
本处 (C142.5) 直接在声明的守恒联合效果中证明缺失差二模式的结论，
不把必要模式条件当作测量仪器的实现、参考保持或充分条件。

本模型的增量是把 C-128.1 的同一源与能量基、C-129.1 的八射线／混态支撑桥、
C-131.1 的实际混态见证，接到指定两电荷参考的精确块域 (C138.3)、
全部十个压缩谱、固定功效残余响应 (C140.3)、闭式前沿 (C140.2)
及逐点守恒联合达到 (C141.2)，并接到任意有限参考的 (C142.2)、(C142.4)–(C142.6)。
支持、正序、主压缩、模式选择和有限凸优化均为这些固定模型证明内部消费的标准工具。
此综合不附全局原创性、优先权或新一般资源理论的断言。

**适用边界 C-143.3（效果、供应与原恢复任务）。** C-136.2 是额外声明的比较菜单。
C-130.1–C-130.2 在其理想独立控制与最终硬币合同内的承诺域原生结果仍按原义成立；
它们没有供应本处全部总数守恒联合效果，(C141.2) 也没有给出原翻转／相位／末端
$n_1$ 菜单的合成证明。数学对称化不等于安装新的控制服务。

每次参考与系统独立且在所有假设下相同，重新供应一份；
没有假设相关参考、免费制备或重置、参考催化返还、跨试验复用、额外副本、
可访问环境或未计价相位时钟。效果达到不确定测后参考态，
故不推出保持、重复测量或非扰动服务，也不构成对守恒测量限制的违反。
$Q$ 支持与参考供应各自承担资源前提；所得前沿不比较其总制备成本或转换率。

[相位增益与 qutrit 恢复卷定义 6.2](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#6-class-optimization-and-remaining-mathematical-obligations)
的原目标仍为正 $\beta$、整个实 Kraus 编码器类 $M_3\to M_5$ 的尖锐 diamond 恢复曲线，
包括全部复 qutrit 输入、被动参考及共同恢复量词；该全类目标仍未解决。
单个 $P$ 的检测前沿不构造统一恢复通道，不改变该目标或其完成判据。
以上为所列假设下的普通数学推导，不附 Lean／形式内核、硬件实现、源认证或经验保证。

## 追加锚（本行以下为增补区）

## 144. 同一原编码器类中的两个实际通道

**定义 C-144.1（完整 Kraus 列与物理坐标）。** 固定 $0<\beta\le1/2$、
$a=1-\beta$，令 $H=\mathbb C^3$、$K=\mathbb C^5$。
本批中 $P_j=|j\rangle\langle j|$ 是 $H$ 上的投影，
$R_j=|e_j\rangle\langle e_j|$ 是 $K$ 上的投影；
物理五态顺序、$\mathcal B$、$E=(\psi,\eta,e_2)$ 仍为 C-128.1 的对象。
定义两个被动坐标通道 $N\in\{\mathcal A,\mathcal B_c\}$：

$$
\begin{aligned}
A_0&=(\sqrt a\,e_0,\sqrt a\,e_1,e_4),&
A_1&=(\sqrt\beta\,e_2,\sqrt\beta\,e_3,0),\\
B_0&=(\sqrt a\,e_0,\sqrt a\,e_1,\sqrt a\,e_2),&
B_1&=(\sqrt\beta\,e_3,\sqrt\beta\,e_4,\sqrt\beta\,e_1),\\
\mathcal A(X)&=\sum_{j=0}^1A_jXA_j^\dagger,&
\mathcal B_c(X)&=\sum_{j=0}^1B_jXB_j^\dagger.
\end{aligned}
\tag{C144.1}
$$

下标 $c$ 只将通道 $\mathcal B_c$ 与固定能量基 $\mathcal B$ 区分。
两者的物理 Kraus 矩阵均为 $DK_jL^\dagger$，其中
$D=\operatorname{diag}(1,i,i,i,1)$、$L=\operatorname{diag}(1,i,i)$，即

$$
N^{\rm ph}=\operatorname{Ad}_D\circ N\circ\operatorname{Ad}_{L^\dagger}.
\tag{C144.2}
$$

这是[相位恢复卷 (P.1)、(P.5)](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#1-actual-channels-physical-coordinates-and-the-native-contract)
的同一坐标合同，未安装 $L^\dagger$ 或 $D$ 为物理门。
以下始终保留 (C144.1) 的全部原始 Kraus 项与第三列。

**定理 C-144.2（实际 CPTP、相位谱与原生增益）。** 两个物理通道均属于上述
相位恢复卷定义 1.3 的原实被动 Kraus 类 $\mathcal R_\beta$，且原菜单相位增益均为 $\beta$。

证明。Kraus 形式给完全正性，且

$$
\begin{aligned}
A_0^\dagger A_0+A_1^\dagger A_1
&=\operatorname{diag}(a,a,1)+\operatorname{diag}(\beta,\beta,0)=I_3,\\
B_0^\dagger B_0+B_1^\dagger B_1&=aI_3+\beta I_3=I_3.
\end{aligned}
\tag{C144.3}
$$

这些实矩阵定义整个复矩阵代数上的通道。具体地，对任意复 $X=(X_{ij})$，

$$
\begin{aligned}
\mathcal A(X)
&=a\sum_{i,j=0}^1X_{ij}|e_i\rangle\langle e_j|
+\beta\sum_{i,j=0}^1X_{ij}|e_{i+2}\rangle\langle e_{j+2}|+X_{22}R_4\\
&\quad+\sqrt a\sum_{i=0}^1
\left(X_{i2}|e_i\rangle\langle e_4|+X_{2i}|e_4\rangle\langle e_i|\right),\\
\mathcal B_c(X)
&=a\sum_{i,j=0}^2X_{ij}|e_i\rangle\langle e_j|
+\beta\sum_{i,j=0}^2X_{ij}|e_{f(i)}\rangle\langle e_{f(j)}|,
\qquad(f(0),f(1),f(2))=(3,4,1).
\end{aligned}
\tag{C144.4}
$$

故第三输入方向及全部复跨块项都未被截断。令
$J_{pq}=i(|e_q\rangle\langle e_p|-|e_p\rangle\langle e_q|)$，
$\chi_\pm=(|0\rangle\pm i|1\rangle)/\sqrt2$。两个实际输出差分别为
$aJ_{01}+\beta J_{23}$ 与 $aJ_{01}+\beta J_{34}$，各自的两个平面正交，
谱均为 $(a,\beta,0,-\beta,-a)$，且为纯虚反对称 Hermitian 矩阵。
物理输入 $\theta_\pm=(|0\rangle\pm|1\rangle)/\sqrt2$ 满足
$L^\dagger\theta_\pm=\chi_\mp$；因此物理差在被动坐标中取上述差的负号，
仍有同一对称谱。相位恢复卷定理 2.1 的参数为 $d=5,p=1,r=2$、
权重 $(a,\beta)$，直接给 $B_0=0,B_1=a,B_k=1$（$k\ge2$）及
$\gamma=B_2-B_1=\beta$。这是该原生相位任务的既有结论；
不由它推出以下其他输出效果的原生实现或源的制备。证毕。

## 145. 固定八射线源的被动输运与混目标读口

**定义 C-145.1（同一物理零假设的精确输运）。** 令
$\mathcal F=E^\dagger\mathcal F_QE$，其含义为 C-129.1 已分类的整个逻辑凸包，
并令 $\mathcal F_p=L^\dagger\mathcal FL$。
记 $P_x=|x\rangle\langle x|$，则

$$
\begin{aligned}
u_t^p&=\sqrt{2/3}|0\rangle-\frac{it}{\sqrt3}|2\rangle,\\
v_{st}^p&=\sqrt{2/5}(|0\rangle-is|1\rangle)
-\frac{it}{\sqrt5}|2\rangle,\qquad s,t\in\{-1,1\},\\
\mathcal F_p&=\operatorname{conv}\{P_1,P_2,P_{u_+^p},P_{u_-^p},
P_{v_{++}^p},P_{v_{+-}^p},P_{v_{-+}^p},P_{v_{--}^p}\}.
\end{aligned}
\tag{C145.1}
$$

这里复用 C-129.1 对任意复振幅与全部有限混态分解的完整分类，不重新分类源。
被动输入 $\rho_p$ 对应物理源 $EL\rho_pL^\dagger E^\dagger$，而
$N^{\rm ph}(L\rho_pL^\dagger)=DN(\rho_p)D^\dagger$。
此对应是 $Q$ 上的坐标识别，不供应 $E^\dagger$ 预处理、源制备或门。
相干数仍在固定物理 $\mathcal B$ 中定义，不在逻辑列基中定义。
特别地，$EP_0E^\dagger=P$ 仍是四相干目标。
通道输出零假设只取实际像 $\mathcal F_N=N(\mathcal F_p)$，
未改定义为某个输出基中的相干数凸包。

**定理 C-145.2（实际目标、剩余态与共同事件）。** 置 $m=2/3$，有

$$
\sigma=\tfrac12(P_{u_+^p}+P_{u_-^p})=mP_0+(1-m)P_2\in\mathcal F_p,
\qquad\max_{\rho\in\mathcal F_p}\operatorname{Tr}(P_0\rho)=m.
\tag{C145.2}
$$

$P_0,P_1,P_2,\sigma$ 在 $L$ 输运下不变。对每个同一通道 $N$ 定义
$\tau_N=N(P_0)$、$\kappa_N=N(P_2)$、$\vartheta_N=N(\sigma)$，实际值为

| 通道 $N$ | $\tau_N$ | $\kappa_N$ | $Q_N$ |
| --- | --- | --- | --- |
| $\mathcal A$ | $aR_0+\beta R_2$ | $R_4$ | $R_0+R_2$ |
| $\mathcal B_c$ | $aR_0+\beta R_3$ | $aR_2+\beta R_1$ | $R_0+R_3$ |

两目标在全部所定 $\beta$ 上都恰为秩二，且

$$
N^\dagger(Q_N)=P_0,\qquad
\vartheta_N=m\tau_N+(1-m)\kappa_N,\qquad
\operatorname{Tr}(Q_N\tau_N)=1,\quad
\operatorname{Tr}(Q_N\kappa_N)=0.
\tag{C145.3}
$$

证明。(C145.2) 是 (C131.4) 与 C-129.1 的完整源经过 $L^\dagger$ 输运后的
同一见证；八射线的 $P_0$ 概率依次为 $0,0,2/3,2/3$ 及四个 $2/5$。
表及伴随式逐项代入完整 (C144.1) 即得；线性性给 $\vartheta_N$。
由于 $DQ_ND^\dagger=Q_N$，亦有 $(N^{\rm ph})^\dagger(Q_N)=P_0$。
这些是实际通道的概率效果，未将混目标替换为 $R_0$，未把输出共同事件
认作 C-130.1 的那个固定字。抽象测量菜单允许该投影；原末端 $n_1$ 菜单
是否合成它是另外的实现义务。证毕。

## 146. 同一实际通道下的六种源域与优化量

**定义 C-146.1（源律与其精确像）。** 对每个整数 $n\ge1$，定义

$$
\begin{aligned}
\mathrm{IID}_n&=\{\rho^{\otimes n}:\rho\in\mathcal F_p\},&
\mathrm{cIID}_n&=\operatorname{conv}_{\rm fin}\mathrm{IID}_n,\\
\mathrm{Prod}_n&=\{\rho_1\otimes\cdots\otimes\rho_n:\rho_i\in\mathcal F_p\},&
\mathrm{cProd}_n&=\operatorname{conv}_{\rm fin}\mathrm{Prod}_n,\\
\mathrm{Marg}_n&=\{\omega\in\mathsf D(H^{\otimes n}):\omega_i\in\mathcal F_p\ (\forall i)\},&
\mathrm{Marg}_n^{=}&=\{\omega\in\mathrm{Marg}_n:\omega_1=\cdots=\omega_n\}.
\end{aligned}
\tag{C146.1}
$$

$\omega_i$ 是第 $i$ 个偏迹边缘，所有联合态允许任意复数及纠缠。
IID 中的单份 $\rho$ 可以是混态；乘积混合中每个分支的每个因子均须为零假设。
对每个所列域 $\mathcal D_n$，实际输出域精确取
$\mathcal D_{N,n}=N^{\otimes n}(\mathcal D_n)$。
给定同一个复集体效果 $0\preceq T\preceq I_{K^{\otimes n}}$，定义

$$
\begin{aligned}
r_{N,\mathcal D_n}(T)
&=\sup_{\omega\in\mathcal D_n}\operatorname{Tr}\!\left[TN^{\otimes n}(\omega)\right],\\
p_{N,n}(T)&=\operatorname{Tr}(T\tau_N^{\otimes n}),\\
f_{N,\mathcal D_n}(\delta)
&=\sup_{\substack{0\preceq T\preceq I\\r_{N,\mathcal D_n}(T)\le\delta}}
p_{N,n}(T),\qquad0\le\delta\le1.
\end{aligned}
\tag{C146.2}
$$

风险与功效消费同一 $N^{\otimes n}$、同一已声明的源律及同一个无条件效果。
目标输入为 $P_0^{\otimes n}$，输出是实际混态 $\tau_N^{\otimes n}$。
这里不把不同通道、不同分支的独立最优值拼成共同实现。
所供效果是不限复测量的数学资源，未继承 C-136.3 的守恒限制，
也未扩充原生翻转／相位／末端 $n_1$ 菜单。

## 147. 两个实际编码器的全部乘积分支前沿

**定理 C-147.1（四域、全部份数及风险额度）。** 对 $N=\mathcal A,\mathcal B_c$，
$n\ge1$、$\delta\in[0,1]$，以及
$\mathcal D_n\in\{\mathrm{IID}_n,\mathrm{cIID}_n,\mathrm{Prod}_n,\mathrm{cProd}_n\}$，

$$
f_{N,\mathcal D_n}(\delta)=\min\{1,\delta/m^n\},\qquad m=2/3.
\tag{C147.1}
$$

同一个达到效果为 $T=tQ_N^{\otimes n}$，$t=\min\{1,\delta/m^n\}$。

证明。复用 C-132.2 的正张量见证机制，但见证与目标均先经过所比较的实际通道。
同一实际源 $\sigma^{\otimes n}$ 已属于最小 IID 域，而

$$
N^{\otimes n}(\sigma^{\otimes n})=\vartheta_N^{\otimes n}
=\bigl(m\tau_N+(1-m)\kappa_N\bigr)^{\otimes n}
\succeq m^n\tau_N^{\otimes n}.
\tag{C147.2}
$$

有限展开的其余每项均为 PSD 张量积，故任意复正效果均有
$r(T)\ge m^np(T)$，无需与见证对易。这给 (C147.1) 的上界。
反向由 (C145.3)，同一实际效果满足

$$
\operatorname{Tr}\!\left[Q_N^{\otimes n}N^{\otimes n}
(\rho_1\otimes\cdots\otimes\rho_n)\right]
=\prod_{i=1}^n\operatorname{Tr}(P_0\rho_i)\le m^n.
\tag{C147.3}
$$

全部因子同时取 $P_{u_+^p}$ 就在 IID 域达到等号，凸混合保持上界。
目标的全通过概率为一；因此 $tQ_N^{\otimes n}$ 的风险恰为 $tm^n$、功效恰为 $t$。
在 $\delta=0$ 取零效果，在 $\delta=m^n$ 及整个 $\delta\ge m^n$ 区间取未缩放事件，
包括 $\delta=1$，不要求用尽额度。证毕。

## 148. 仅边缘承诺的实际联合前沿

**定理 C-148.1（一般边缘与相同边缘）。** 对同一两个通道、全部 $n\ge1$、
$\delta\in[0,1]$，

$$
f_{N,\mathrm{Marg}_n}(\delta)
=f_{N,\mathrm{Marg}_n^{=}}(\delta)=\min\{1,\delta/m\}
=\min\{1,3\delta/2\}.
\tag{C148.1}
$$

证明。C-133.2 的共同标签见证在被动源上为

$$
W_n=mP_0^{\otimes n}+(1-m)P_2^{\otimes n},\qquad
\Gamma_{N,n}=N^{\otimes n}(W_n)
=m\tau_N^{\otimes n}+(1-m)\kappa_N^{\otimes n}
\succeq m\tau_N^{\otimes n}.
\tag{C148.2}
$$

$W_n$ 的每个边缘都恰为 $\sigma$，故它已属于较小的同边缘源域。
于是每个允许效果均有 $r(T)\ge mp(T)$。另一方面，
$Q_N^{\otimes n}\preceq(Q_N)_i\otimes I_{\ne i}$，实际编码边缘为 $N(\omega_i)$，
所以其风险至多 $\operatorname{Tr}(Q_NN(\omega_i))\le m$。
同一个 $W_n$ 在该事件上的概率为 $m$，目标概率为一。
取 $t=\min\{1,\delta/m\}$、$T=tQ_N^{\otimes n}$ 即得恰为 $(tm,t)$ 的风险与功效。
$\delta=0$、阈值 $m$ 及全部饱和区间均由这些实际效果覆盖。证毕。

**命题 C-148.2（同边缘可分离见证的分支限制）。** $n\ge2$ 时，
$W_n$ 虽可分离且置换不变，却不是零假设因子乘积的有限混合；
其实际像 $\Gamma_{N,n}$ 也不在 $N^{\otimes n}(\mathrm{cProd}_n)$ 中。
$n=1$ 时，六种源域均为 $\mathcal F_p$，上述前沿相同。

证明。$\operatorname{Tr}(P_0^{\otimes n}W_n)=m>m^n$，
而 (C147.3) 的源侧乘积界在 $\mathrm{cProd}_n$ 上至多 $m^n$；
实际像上同一 $Q_N^{\otimes n}$ 亦以 $m>m^n$ 区分二者。
可分离分解允许有资源的 $P_0$ 因子，零假设因子混合禁止该分支。
单份时 $W_1=\sigma$，边缘就是态本身。证毕。

## 149. 任意输出零边缘域严格大于实际源像

**定义 C-149.1（另行扩大的输出域）。** 在 $K^{\otimes n}$ 上另定义

$$
\begin{aligned}
\widehat{\mathrm{Marg}}_{N,n}
&=\{\Omega\in\mathsf D(K^{\otimes n}):\Omega_i\in\mathcal F_N\ (\forall i)\},\\
\widehat{\mathrm{Marg}}_{N,n}^{=}
&=\{\Omega\in\widehat{\mathrm{Marg}}_{N,n}:\Omega_1=\cdots=\Omega_n\}.
\end{aligned}
\tag{C149.1}
$$

在这些域上定义 $\widehat f$ 时，风险直接为 $\sup_\Omega\operatorname{Tr}(T\Omega)$，
目标仍为同一 $\tau_N^{\otimes n}$。它们不是 (C146.1) 的源律定义。

**定理 C-149.2（严格包含与前沿数值相同）。** 对每个 $N$，

$$
\begin{aligned}
N^{\otimes n}(\mathrm{Marg}_n)&\subseteq\widehat{\mathrm{Marg}}_{N,n},\\
N^{\otimes n}(\mathrm{Marg}_n^{=})&\subseteq\widehat{\mathrm{Marg}}_{N,n}^{=}.
\end{aligned}
\tag{C149.2}
$$

两包含在 $n=1$ 均为相等，在每个 $n\ge2$ 均严格；然而两扩大域的优化前沿仍均为
$\min\{1,3\delta/2\}$，对全部 $\delta\in[0,1]$ 成立。

证明。局部通道与偏迹相容，给 (C149.2)；单份时均为 $\mathcal F_N$。
为严格性写 $\vartheta_N=\sum_{j=0}^4p_j^NR_j$，其中

$$
\begin{aligned}
(p_j^{\mathcal A})_{j=0}^4&=(ma,0,m\beta,0,1-m),\\
(p_j^{\mathcal B_c})_{j=0}^4&=(ma,(1-m)\beta,(1-m)a,m\beta,0),\\
\Omega_{N,n}&=\sum_{j=0}^4p_j^NR_j^{\otimes n}.
\end{aligned}
\tag{C149.3}
$$

这是真实正迹一输出联合态，每个边缘恰为 $\vartheta_N\in\mathcal F_N$，
故已属于较小的扩大同边缘域。置 $r_{\mathcal A}=2,r_{\mathcal B_c}=3$。
完整原 Kraus 列给

$$
N^\dagger(R_0)=aP_0,\qquad N^\dagger(R_{r_N})=\beta P_0.
\tag{C149.4}
$$

因此任意复联合输入 $\xi\in\mathsf D(H^{\otimes n})$（无需零假设或可分离限制）
的实际编码输出，在前两个位置都满足

$$
\begin{aligned}
\operatorname{Tr}\!\left[(R_0\otimes R_{r_N}\otimes I)N^{\otimes n}(\xi)\right]
&=a\beta\operatorname{Tr}\!\left[(P_0\otimes P_0\otimes I)\xi\right]\\
&=\frac\beta a\operatorname{Tr}\!\left[(R_0\otimes R_0\otimes I)N^{\otimes n}(\xi)\right].
\end{aligned}
\tag{C149.5}
$$

对 (C149.3)，左端为零，右端为 $(\beta/a)ma=m\beta>0$。
故它不在任何输入联合态的实际通道像中，尤其不在 (C149.2) 任一左域中。
这证明全部 $n\ge2$ 的严格性，而非只区分零假设分支。

最后，实际 $\Gamma_{N,n}$ 仍属于扩大同边缘域，(C148.2) 给全部效果的上界。
对任意扩大域中的 $\Omega$，单边缘满足
$\operatorname{Tr}(Q_N\Omega_i)\le m$，故投影不等式给全通过风险至多 $m$。
同一 $\Gamma_{N,n}$ 达到 $m$，而目标通过概率一；缩放仍给 $(tm,t)$。
所以相同的是优化数值，不是联合态集合，也不是所有单项统计。证毕。

## 150. 相同观察签名中的严格恢复差

**定义 C-150.1（所保留的观察及完整恢复范数）。** $\mathcal O(N)$ 只包含
相位增益 $\beta$，以及 (C146.1) 六个具名源域和 (C149.1) 两个另行具名输出域的
所有优化单目标前沿数值，指标为全部 $n\ge1$、$\delta\in[0,1]$。
域名指各通道自身的上述精确源像或另行输出域，不将两个通道的输出态集合认作相同。
该签名不保存全部原始目标统计、全部效果或每个有限区分任务。
按相位恢复卷定义 1.4，记

$$
\Delta_N=\inf_{\substack{\mathcal R:M_5\to M_3\\\mathcal R\ {\rm complex\ CPTP}}}
\|\mathcal R\circ N-\mathrm{id}_3\|_\diamond,
\quad
\|\Phi\|_\diamond=
\sup_{\substack{R\ {\rm finite}\\\rho\in\mathsf D(H\otimes R)}}
\|(\Phi\otimes\mathrm{id}_R)(\rho)\|_1
\tag{C150.1}
$$

（后一式用于这里的通道差）。迹范数与 diamond 范数均不除以二；
一个共同恢复作用于整个复输入代数，包含全部有限参考，不按输入或系综另选恢复。

**定理 C-150.2（实际观察纤维与恢复分离）。** 两个实际通道满足

$$
\mathcal O(\mathcal A)=\mathcal O(\mathcal B_c),\qquad
\Delta_{\mathcal A}=1-\sqrt a,\qquad
\Delta_{\mathcal B_c}\ge\beta,\qquad
\Delta_{\mathcal B_c}-\Delta_{\mathcal A}\ge\sqrt a-a>0.
\tag{C150.2}
$$

证明。观察相同由 C-144.2、C-147.1、C-148.1、C-149.2 给出。
$\mathcal A$ 恰为[相位恢复卷 (P.11)](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#4-an-actual-upper-family-and-its-individual-optimum)，
故直接使用其定理 4.1／(P.12) 的个体最优值，参数 $u=\sqrt a$。
$\mathcal B_c$ 恰为[完整恢复卷定理 9.1／(R.38)](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#9-an-actual-entangled-kernel-and-an-exact-all-input-endpoint-value)，
故直接使用该定理对每个共同复 CPTP 恢复的下界 $\beta$。
物理恢复与被动恢复按相位恢复卷 (P.16) 一一对应，
连同所有参考保持 diamond 范数，故此差也属于同一物理通道比较。
相减得 $\beta-(1-\sqrt a)=\sqrt a-a$，因 $0<a<1$ 而严格为正。
这里不重证既有恢复定理，不计算或宣称 $\mathcal B_c$ 的精确最优值。证毕。

## 151. 切开该纤维的两个相反方向的源关系测量

**定理 C-151.1（同输入标签的两组二元实验）。** 每次另行供应所指定的两个源标签之一，
先验各为 $1/2$，并允许任意复输出二元 POVM。用未除二的迹范数，两个实验为

| 同一对被动源输入 | $\mathcal A$ 输出距离 | $\mathcal B_c$ 输出距离 | $\mathcal A$ 最优成功率 | $\mathcal B_c$ 最优成功率 |
| --- | --- | --- | --- | --- |
| $P_1,P_2$ | $2$ | $2a$ | $1$ | $1-\beta/2$ |
| $P_{u_+^p},P_{u_-^p}$ | $4\sqrt{2a}/3$ | $4\sqrt2/3$ | $1/2+\sqrt{2a}/3$ | $1/2+\sqrt2/3$ |

两组标签均已属于 (C145.1) 的实际源，不使用任意新输入替换原标签。
在保持同输入标签的输出 CPTP 后处理序中，不存在
$\mathcal A=\Phi\circ\mathcal B_c$，也不存在 $\mathcal B_c=\Phi\circ\mathcal A$。

证明。第一组在 $\mathcal A$ 下为 $aR_1+\beta R_3$ 与 $R_4$，支持正交。
在 $\mathcal B_c$ 下的差为
$(a-\beta)R_1-aR_2+\beta R_4$；$a\ge\beta$ 给范数 $2a$，包括 $a=\beta$。
按输出是否位于 $\operatorname{span}(e_1,e_3)$（$\mathcal A$）或
$\operatorname{span}(e_1,e_4)$（$\mathcal B_c$）作二元测量即达到表中第一行。

第二组的实际被动差为

$$
X=P_{u_+^p}-P_{u_-^p}
=\frac{2i\sqrt2}{3}(|0\rangle\langle2|-|2\rangle\langle0|).
\tag{C151.1}
$$

由全部原 Kraus 列，

$$
\begin{aligned}
\mathcal A(X)&=\frac{2i\sqrt{2a}}3
(|e_0\rangle\langle e_4|-|e_4\rangle\langle e_0|),\\
\mathcal B_c(X)&=\frac{2i\sqrt2}3
\left[a(|e_0\rangle\langle e_2|-|e_2\rangle\langle e_0|)
+\beta(|e_3\rangle\langle e_1|-|e_1\rangle\langle e_3|)\right].
\end{aligned}
\tag{C151.2}
$$

每个非零二阶块的谱为相反两数，$\mathcal B_c$ 的两块正交，
故范数分别为 $4\sqrt{2a}/3$ 与 $4\sqrt2(a+\beta)/3$。
令 $g_{pq}=(e_p-ie_q)/\sqrt2$，第二组达到测量的标签加效果可分别取
$P_{g_{04}}$ 与 $P_{g_{02}}+P_{g_{31}}$，其余效果为补投影。
这是输出差的正谱投影；零谱空间的分配不改变成功率。
标准 Holevo–Helstrom 公式给 $p_{\rm succ}=1/2+\|\rho_+-\rho_-\|_1/4$，
故得表中全部成功率。其精确引文为 Watrous，
[*The Theory of Quantum Information*, Chapter 3, Theorem 3.4, (3.11)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf)，
取 $\lambda=1/2$、$X=K$；这里只在这两个具体实验内消费该标准公式。

若 $\mathcal A=\Phi\circ\mathcal B_c$，第一行违反 CPTP 迹范数收缩，
因为 $2>2a$。若 $\mathcal B_c=\Phi\circ\mathcal A$，第二行违反同一收缩，
因为 $4\sqrt2/3>4\sqrt{2a}/3$。收缩亦可直接由二元效果经
$\Phi^\dagger$ 拉回仍是二元 POVM 得到，未加实数或对易限制。证毕。

**适用边界 C-151.2（有限比较与物理供应）。** 第一行与第二行是两个不同的、
同输入标签保持的有限实验，各自有自己的输出测量；它们不要求量子参考。
物理源标签分别为 $ELP_jL^\dagger E^\dagger$ 与
$ELP_{u_t^p}L^\dagger E^\dagger$，物理输出效果按 $D$ 共轭，概率和距离不变。
这给明确的关系测量如何区分该观察纤维，不供应这些源或输出 POVM 的原生实现。
两个严格不等式仅排除所写的输出 CPTP 后处理，未排除任意输入预处理、
superchannel 或改变源标签的模拟，也不建立原菜单的成本排序。

同一目标上的原始统计本来就可以不同：
$\operatorname{Tr}(R_2\mathcal A(P_0))=\beta$，
$\operatorname{Tr}(R_2\mathcal B_c(P_0))=0$。
所以 (C150.2) 的不足性仅属于 $\beta$ 加上述优化单目标前沿数值，
不属于全部原始目标数据、每个有限实验或全部原生装置。
本处的理想二元测量例子亦不声称有限样本误差、样本复杂度或无需校准的识别。

## 152. 实际观察纤维的内容与未解决的全类恢复边界

**约定 C-152.1（被消费的既有结果与本构造的范围）。** 八射线、混态支持桥及
固定物理能量基直接复用 C-128.1、C-129.1，正序／张量与共同标签证明模式
复用 C-131.1、C-132.2、C-133.2–C-133.3。
相位增益与 $\mathcal A$ 的个体 diamond 最优值取相位恢复卷定理 2.1、4.1，
$\mathcal B_c$ 的下界取完整恢复卷定理 9.1，物理恢复输运取 (P.16)。
PSD 张量正性、CPTP 收缩与二元最优测量是上述实际证明内消费的标准工具，
不另立为新的一般相干、恢复或统计比较定理。

本批的 repo-derived 综合是把同一固定八射线物理源输运到这两个完整实际编码器，
用各自同一个源律、混目标及事件给出全部具名前沿，
并同时给出严格输出域反例、恢复差和两个相反方向的同标签实验。
这不附全局原创性、优先权或穷尽文献搜索的断言。

**适用边界 C-152.2（抽象效果与原任务的量词）。** $tQ_N^{\otimes n}$
是允许的抽象效果；若将缩放解释为实验操作，另需一个独立于源、控制及结果的
最终 Bernoulli 随机数，仅以概率 $t$ 保留整个全通过宣告。
逐份各缩放 $t$ 会给 $t^n$，不是这里的 $t$。
源律必须实际供应；源支持、独立新副本、共同边缘和相关分支不能由事件推出。
坐标识别不安装 $E^\dagger$，抽象最优效果不安装原生 POVM、源、ancilla、
量子 bypass 或额外参考；这里也没有参考保持、重置或跨试验复用服务。

检测只要求给定支持承诺下的目标与零假设统计，恢复则仍要求一个共同通道作用于
全部复 qutrit 输入及其任意有限参考。前者的精确前沿和源承诺不构造后者。
[相位恢复卷定义 6.2](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md#6-class-optimization-and-remaining-mathematical-obligations)
与[完整恢复卷定义 10.2](AURIC_OMEGA_FULL_INPUT_RECOVERY_CERTIFICATES.md#10-standard-sources-and-unresolved-uniform-certificate-problem)
的正 $\beta$ 原全类尖锐问题仍未解决：须证明整个 $\mathcal R_\beta$ 的恢复 infimum
为 $1-\sqrt{1-\beta}$，或给出实际该类编码器与一个完整复 CPTP 恢复，
使全参考、未除二 diamond 误差严格更小。
当前构造既没有对全部剩余编码器的统一匹配下界，也没有这样的改进恢复；
$\mathcal B_c$ 的更差恢复能力不结算这个 infimum 问题。
全部陈述为明确假设下的普通数学推导，不附 Lean／形式内核、
原生合成、源认证、经验物理或有限样本保证。

## 追加锚（本行以下为增补区）
