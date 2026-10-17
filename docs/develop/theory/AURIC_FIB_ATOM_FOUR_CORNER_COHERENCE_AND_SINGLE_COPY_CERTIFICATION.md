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
