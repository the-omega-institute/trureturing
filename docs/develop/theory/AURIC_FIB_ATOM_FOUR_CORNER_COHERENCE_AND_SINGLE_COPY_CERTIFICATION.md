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
