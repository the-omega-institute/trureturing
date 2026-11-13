# 实际四次检测的有限仿射模型与六方向正枢轴

## 190. 原十四次域、实际系数源与唯一检测约定

**定义 190.1（原系数局部环及其实际正纤维）。** 设 $F$ 为任意特征零域，$D/F$ 为实际可分**域**扩张，$[D:F]=14$。任取本原元 $\theta$，固定非零体积形式 $\nu:\det_FD\to F$，置

$$
C=\langle1,\theta,\ldots,\theta^6\rangle_F,
\qquad V=F[T]_{\le5},\qquad W=\bigwedge^2V.
\tag{190.1}
$$

对同一个 $D$ 中的七维窗口 $C'$ 及其包含帧 $E_{C'}$，定义

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr).
\tag{190.2}
$$

$M_x$ 是这个域中的乘法。取有限 Galois 分裂域，保持原嵌入标签及其固定次序，原系数写为

$$
P_{C'}(x)=\sum_{|I|=7}c_I(C')x_I,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{190.3}
$$

$p_I$ 是实际帧的行子式，$\epsilon_I$ 为互补行序符号，$\alpha$ 为体积因子。令 $S$ 为此射影系数像在 $p=[P_C]$ 处的原 $F$ 局部环。连续幂窗口的所有最大行子式均为非零 Vandermonde 行列式，所以属于所有 $p_I\ne0$ 的统一开集。采用 039，定义 111.1、命题 111.2、定理 113.1、115.1、117.1 的同一个原乘法商、Gale 对合和有限正规化，在唯一上方点取正规化局部环 $B$，记

$$
\mathscr T=\widehat S\hookrightarrow\mathscr B=\widehat B,
\qquad Q_S=\mathfrak m_S/\mathfrak m_S^2,
\qquad J:Q_S\longrightarrow\mathfrak m_B/\mathfrak m_B^2,
\qquad R=\ker J.
\tag{190.4}
$$

$S$ 是 Noetherian 局部 $F$ 代数，源与正规化的剩余域均为 $F$。$R$ 是原系数余切映射的**源核**，不是正规化侧的外四次余核。分裂标签函数不自动是原 $F$ 函数。

采用 042，§133 的实际对合相容横截面，先记其正变量为 $X=(X_1,\ldots,X_{21})$，负变量为 $Y=(Y_1,\ldots,Y_{15})$，于是

$$
\mathscr B=F[[X,Y]]^{Y\mapsto-Y}.
\tag{190.5}
$$

正变量来自七维窗口上的交错图，负变量来自对称图模实际 Hankel 轨道。对 $e_i=T^i$ 固定

$$
z_{ij}(Y)=Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1})
\longleftrightarrow e_i\wedge e_j,
\quad 0\le i<j\le5,
\tag{190.6}
$$

并约定 $z_{ji}=-z_{ij}$、$z_{ii}=0$。这些 $z_{ij}$ 是负线性坐标；以下所有比较保持这组 $Y$ 及此归一化。

合法正枢轴是 $s=(s_1,\ldots,s_{21})\in\mathfrak m_S^{21}$，使 $J[s_i]$ 的正分量构成正余切空间的基。“正”指对合正特征方向，不要求 $F$ 有序。对每组给定的合法 $s$，始终定义

$$
B_{0,s}=\mathscr B/(s)\mathscr B\simeq F[[Y]]^{Y\mapsto-Y},
\qquad \pi_s:\mathscr T\longrightarrow B_{0,s},
\qquad A_s=\operatorname{im}\pi_s.
\tag{190.7}
$$

在 $F[[Y]]$ 中置 $\mathfrak q=(Y)$，定义

$$
J_4(A_s)=\operatorname{im}\bigl(A_s\cap\mathfrak q^4
\xrightarrow{\operatorname{in}_4}\mathfrak q^4/\mathfrak q^6\bigr)
\subseteq\operatorname{Sym}^4W.
\tag{190.8}
$$

这要求常数与实际二次项均为零，不收集任意二次提升的裸四次尾项。只自动知道 $(s)\mathscr T\subseteq\ker\pi_s$，不把 $A_s$ 换成 $\mathscr T/(s)\mathscr T$。

**定义 190.2（二次核、实际乘积与检测器）。** 置

$$
Q_2=\operatorname{Sym}^2W,\quad G=\bigwedge^4V,\quad
\mu:Q_2\longrightarrow G,\quad \mu(ab)=a\wedge b,\quad
K=\ker\mu,
\tag{190.9}
$$

$$
P_4=\operatorname{im}\bigl(\operatorname{Sym}^2K
\xrightarrow{\mathrm{mult}}\operatorname{Sym}^4W\bigr),
\quad \mathcal D=\bigwedge^6V\otimes W,\quad
\Omega=e_0\wedge\cdots\wedge e_5.
\tag{190.10}
$$

$P_4=K K$ 只表示两个 $K$ 元素乘积的线性张成。全文唯一的检测器是 045，定义 168.1 的

$$
\Psi:\operatorname{Sym}^4W\longrightarrow\mathcal D,
\qquad
\Psi(a_1a_2a_3a_4)=
\sum_{i=1}^4\left(\bigwedge_{j\ne i}a_j\right)\otimes a_i.
\tag{190.11}
$$

记 $E_s=\Psi(J_4(A_s))$。复用 045，定理 168.2 的精确等式 $\ker\Psi=P_4$。特别地，不能将被消去的空间扩大为 $KQ_2$。

040，定理 122.1 的 (122.8)、命题 122.2 给原域上的耦合像

$$
M=\operatorname{im}J\subseteq P_+^\vee\oplus Q_2,
\qquad \operatorname{pr}_{P_+^\vee}M=P_+^\vee,
\qquad M\cap Q_2=K.
\tag{190.12}
$$

042，引理 134.2 给每个实际纤维的全部二次像为 $K$。045，引理 170.1 还给一个可在枢轴以前固定的原 $F$ 线性提升

$$
u:K\longrightarrow\mathfrak m_S,
\qquad J[u(k)]=(0,k),\qquad
\pi_s(u(k))=k+O(Y^4)
\quad\text{对每个合法 }s.
\tag{190.13}
$$

同一来源给 $P_4\to\mathfrak m_S^2$ 的共同线性提升，其在每个实际纤维中的四次符号是指定的 $P_4$ 元素。这些是实际原源提升，不是向源中添加任意环境多项式。$\mu$ 满射，因为每个基四向量都是两个基二向量的外积，故

$$
\dim W=15,\qquad \dim G=15,\qquad \dim K=120-15=105.
\tag{190.14}
$$

## 191. 一次居中的实际图与全部合法补偿

**定义 191.1（固定一次的基枢轴图）。** 任选一组实际合法基枢轴 $s^0$，在原正坐标中作常数可逆归一化，使其正一次矩阵为恒等。此后只作一次坐标替换

$$
U_i=s_i^0(X,Y),\qquad Y\text{ 保持不变}.
\tag{191.1}
$$

对每组未来的合法枢轴，只以常数可逆 $F$ 矩阵线性组合其二十一条方程，使相对于这组 $U$ 的正一次矩阵为恒等。以下 $s$ 均表示这个归一化后的组；其在 $\mathscr B$ 中生成的理想、实际纤维及 $A_s$ 不因这一步线性组合改变。给变量指定权重

$$
\mathrm{wt}(U_i)=2,\qquad \mathrm{wt}(Y_j)=1.
\tag{191.2}
$$

$O_{\mathrm{wt}}(d)$ 表示所有单项式的权至少为 $d$。图、原源函数及负识别在全部后续公式中固定。

**定理 191.2（全部实际正枢轴到 $K^{21}$ 的满射）。** 在定义 191.1 的一张图内，

$$
M=\langle U_1,\ldots,U_{21}\rangle_F\oplus K.
\tag{191.3}
$$

每组归一化合法实际枢轴有唯一的

$$
k_s=(k_{s,1},\ldots,k_{s,21})\in\mathcal H:=K^{21},
\qquad
s_i=U_i+k_{s,i}(Y)+O_{\mathrm{wt}}(4),
\tag{191.4}
$$

且其实际消元为

$$
U_i=-k_{s,i}(Y)+O(Y^4).
\tag{191.5}
$$

反之，每个 $k\in\mathcal H$ 都由同一个原 $S$ 中的一组合法枢轴同时实现。因而 $\dim\mathcal H=2205$。

证明。在光滑覆盖上，$(X,Y)\mapsto(s^0(X,Y),Y)$ 的常数 Jacobian 可逆，故给形式坐标自同构。每个 $s_i^0$ 是对合不变量，此自同构与 $Y\mapsto-Y$ 交换，因此也给 $\mathscr B$ 的坐标图。由于新 $U_i$ 本身是实际源函数的像，其余切类均在 $M$ 中。对任意 $m\in M$，减去具有相同正分量的 $U_i$ 线性组合，余项属于 $M\cap Q_2=K$。这给 (191.3)，并且解释了为什么必须先居中才能使用这个直和。

不变量环的极大理想由 $U_i$ 和 $Y_aY_b$ 生成，其平方只含权至少四的项。故归一化后的 $s_i-U_i$ 在余切中恰给一个 $k_{s,i}\in K$，证明唯一性。形式隐函数定理与偶性给唯一偶解 $U=O(Y^2)$；将权二部分代入，得到 (191.5)。

共同提升 $u$ 在换图后仍有余切类 $(0,k)$：其正分量为零，故坐标替换的纯二次校正不改变这个负二次类。给任意二十一条 $k_i\in K$，同时定义

$$
s_i(k)=s_i^0+u(k_i)\in\mathfrak m_S.
\tag{191.6}
$$

它们的正一次矩阵仍为恒等，故合法，且其补偿恰为 $k_i$。所有选择都在原 $F$ 中，未把分别存在的枢轴拼成一个未经实现的对象。证毕。

## 192. 原余切关系上的代表无关四阶数据

**定义 192.1（混合项与纯四次项）。** 对 $r\in R$，任选原代表 $h\in\mathfrak m_S$，$[h]=r$。在固定图中，$J[h]=0$ 意味着 $h\in\mathfrak m_{\mathscr B}^2$，所以其权四部分唯一写为

$$
h^{[4]}=A_h(U)+\sum_{i=1}^{21}U_i c_i(h)(Y)+d(h)(Y),
\quad
A_h\in\operatorname{Sym}^2\langle U\rangle,
\quad c_i(h)\in Q_2,\quad d(h)\in\operatorname{Sym}^4W.
\tag{192.1}
$$

其余项属于 $O_{\mathrm{wt}}(6)$。候选数据为

$$
\gamma_i(r)=\mu(c_i(h))\in G,
\qquad \delta(r)=\Psi(d(h))\in\mathcal D.
\tag{192.2}
$$

对 $k\in K$、$t\in G$，取任意 $c\in Q_2$ 满足 $\mu(c)=t$，候选配对为

$$
\beta(k,t)=\Psi(kc)\in\mathcal D.
\tag{192.3}
$$

**定理 192.2（实际源关系数据与配对良定义）。** 式 (192.2) 给不依赖原代表 $h$ 的线性映射

$$
\gamma_i:R\longrightarrow G,\qquad
\delta:R\longrightarrow\mathcal D;
\tag{192.4}
$$

式 (192.3) 给不依赖 $c$ 的双线性映射 $\beta:K\times G\to\mathcal D$。这些数据相对于唯一固定的基枢轴图定义，不声称在任意重新选图后坐标值不变。

证明。偶性使不变量单项式的权均为偶数。极大理想由权二单项式生成；将单项式按这些生成元分组，可见其平方恰由权至少四的级数组成。故 $J[h]=0$ 确实排除了全部权二项，(192.1) 列尽权四项。

若 $h'$ 是同一源余切类的另一原代表，则 $h'-h\in\mathfrak m_S^2$，是有限个实际零常数源函数乘积之和。由 (191.3)，每个因子的权二部分形如 $a\cdot U+q$，$q\in K$。两个这样的部分相乘为

$$
(a\cdot U+q)(b\cdot U+q')
=(a\cdot U)(b\cdot U)
+\sum_i U_i(a_iq'+b_iq)+qq'.
\tag{192.5}
$$

因此混合系数的差属于 $K$，纯四次项的差属于 $P_4$。分别应用 $\mu$ 和 $\Psi$ 后差均为零。加法及数乘也可用原代表实行，故得到所述线性映射。

$\mu$ 满射，因而 (192.3) 总可定义。若 $c'$ 也是 $t$ 的提升，则 $c-c'\in K$，所以 $k(c-c')\in P_4=\ker\Psi$。这证明配对与提升无关；从 $K\times Q_2$ 上的双线性乘法因子化，得到双线性。特别地，任意混合系数 $c_i(h)$ 没有被认作实际源的二次符号；这里只取其外乘商。证毕。

## 193. 每个固定实际纤维的整个检测像

**定理 193.1（有限仿射检测公式与完整反向包含）。** 对 $k\in\mathcal H$，定义

$$
T_k:R\longrightarrow\mathcal D,
\qquad
T_k(r)=\delta(r)-\sum_{i=1}^{21}\beta(k_i,\gamma_i(r)).
\tag{193.1}
$$

则每组事先固定的实际合法枢轴满足

$$
\boxed{E_s=\operatorname{im}T_{k_s}},\qquad
J_4(A_s)/P_4\simeq\operatorname{im}T_{k_s},\qquad
J_4(A_s)=\Psi^{-1}(\operatorname{im}T_{k_s}).
\tag{193.2}
$$

所以在固定负坐标中，整个四次符号空间及整个检测像只依赖 $k_s$，不依赖未来枢轴的四次及更高尾项。这些等式本身不计算 $T_{k_s}$ 的秩，也不把完整实际环认作只依赖 $k_s$。

证明。取 $r$ 的原代表 $h$，将 (191.5) 代入 (192.1)，得

$$
\operatorname{in}_4\pi_s(h)
=d(h)-\sum_i k_{s,i}c_i(h)+A_h(-k_s).
\tag{193.3}
$$

$h$ 没有权二项，所以其实际像至少四阶。$A_h(-k_s)$ 是两个 $K$ 元素乘积的有限线性和；检测后它消失，其余项给 $T_{k_s}(r)$。在权四项中把 $U$ 的 $O(Y^4)$ 尾项代入 $UY^2$ 或 $U^2$，只能贡献六阶及以上；原 $O_{\mathrm{wt}}(6)$ 项在 $U=O(Y^2)$ 下也至少六阶。因此没有遗漏额外四次补偿，且 $\operatorname{im}T_{k_s}\subseteq E_s$。

反向取任意 $a\in\mathscr T$，要求其像 $\pi_s(a)\in A_s\cap\mathfrak q^4$。这允许任意完成源元素，不限于评价函数。映射保持常数，故 $a$ 的剩余类为零。Noetherian 完成给

$$
S/\mathfrak m_S^3\simeq\mathscr T/\mathfrak m_{\mathscr T}^3.
\tag{193.4}
$$

可取 $a_0\in\mathfrak m_S$，使 $a-a_0\in\mathfrak m_{\mathscr T}^3$。源零常数元素在实际纤维上至少二阶，故这个差的像至少六阶，$a$ 与 $a_0$ 有相同的二次及四次符号。

按 (191.3) 写

$$
J[a_0]=\sum_i\alpha_iU_i+q,\qquad q\in K.
$$

其纤维二次项为 $q-\sum_i\alpha_i k_{s,i}$，所以零二次条件给 $q=\sum_i\alpha_i k_{s,i}$。实际原函数

$$
g=a_0-\sum_i\alpha_i s_i\in\mathfrak m_S
\tag{193.5}
$$

满足 $J[g]=0$，且其纤维四次符号与 $a$ 相同。令 $r=[g]\in R$。若定义 192.1 采用另一原代表 $h$，则 $g-h\in\mathfrak m_S^2$；其实际四次符号是实际二次符号两两相乘之和，恰在 $P_4$ 中，检测为零。因此

$$
\Psi(\operatorname{in}_4\pi_s(a))=T_{k_s}(r),
$$

得到 $E_s\subseteq\operatorname{im}T_{k_s}$。此处只减去真实枢轴和真实源乘积，没有以正规化中的任意二次函数修补源代表。反向论证也不需要 $\ker\pi_s=(s)\mathscr T$。

最后 $P_4\subseteq J_4(A_s)$，且 $\ker\Psi=P_4$，故限制检测器给所述同构。若 $f\in\operatorname{Sym}^4W$ 的检测属于 $E_s$，选 $g_4\in J_4(A_s)$ 与它同检测；则 $f-g_4\in P_4\subseteq J_4(A_s)$，从而 $f\in J_4(A_s)$。这给最后的原像等式。证毕。

## 194. 实际六方向商的九个多项式系数

**定义 194.1（共同六方向及其多项式读取）。** 044，(155.5)、(156.6)、(157.5) 的确切六个向量是

$$
\begin{aligned}
v_0&=2z_{14}-z_{05}-z_{23},&v_1&=2z_{13}-z_{04},&v_2&=3z_{12}-z_{03},\\
v_3&=2z_{24}-z_{15},&v_4&=3z_{34}-z_{25},&w&=z_{05}+z_{14}-8z_{23}.
\end{aligned}
\tag{194.1}
$$

置 $L_6=\langle v_0,v_1,v_2,v_3,v_4,w\rangle_F$，$L=\Omega\otimes L_6$。044，定理 157.1 给同一原 $S$ 中的六个函数，在每个已经固定的实际纤维中有检测值 $2\Omega\otimes(v_0,v_1,v_2,v_3,v_4,w)$。故 $L\subseteq E_s$ 对每组固定 $s$ 成立。

令 $\mathcal Q=F[T]_{\le8}$，定义

$$
\omega:\bigwedge^2F[T]_{\le5}\longrightarrow\mathcal Q,
\qquad \omega(f\wedge g)=fg'-f'g,
\qquad
\rho:\mathcal D\longrightarrow\mathcal Q,
\quad \rho(\Omega\otimes v)=\omega(v).
\tag{194.2}
$$

**定理 194.2（原实际六方向之外的完整九系数判据）。** 对定义 190.1 的每个原域族，

$$
\ker\omega=L_6,\qquad \ker\rho=L,\qquad
\mathcal D/L\xrightarrow[\rho]{\ \sim\ }\mathcal Q.
\tag{194.3}
$$

因而对每个给定实际 $s$，六方向之外的整个检测像恰为

$$
\rho(E_s)=\operatorname{im}\overline T_{k_s},
\qquad \overline T_k:=\rho T_k:R\longrightarrow\mathcal Q,
\tag{194.4}
$$

并由次数零至八的九个普通多项式系数完整读取。

证明。式 (194.2) 是交替双线性式，故在外二次幂上良定义；两个五次首项的九次系数相消，所以值域确实是 $\mathcal Q$。在固定的原负基上有

$$
\omega(z_{ij})=(j-i)T^{i+j-1}.
\tag{194.5}
$$

将 (194.1) 的六个实际向量代入，非零候选系数分别为

$$
6-5-1,\quad4-4,\quad3-3,\quad4-4,\quad3-3,\quad5+3-8,
$$

全为零。$v_2,v_1,v_3,v_4$ 分别支撑在指标和 $3,4,6,7$，而 $v_0,w$ 支撑在指标和 $5$，其 $z_{05},z_{14}$ 系数行列式为 $-3$。因此这六个向量独立，给六维核子空间。

044，(165.2) 的九个补向量在 $\omega$ 下依次为

$$
\begin{array}{c|ccccccccc}
v&z_{01}&z_{02}&z_{03}&z_{04}&z_{23}&z_{15}&z_{25}&z_{35}&z_{45}\\
\hline
\omega(v)&1&2T&3T^2&4T^3&T^4&4T^5&3T^6&2T^7&T^8.
\end{array}
\tag{194.6}
$$

特征零使九个系数均可逆，故 $\omega$ 满射，核维数是 $15-9=6$，恰为 $L_6$。取定 $\Omega$ 后立即得到 (194.3)，再用定理 193.1 得 (194.4)。例如第四次系数是 $5[z_{05}]+3[z_{14}]+[z_{23}]$，但只检查这一条不能替代全部九条。

此处的经典 Wronski 构造对应 Eremenko--Gabrielov，[*Degrees of real Wronski maps*，arXiv:math/0108133v4，Introduction，式 (1) 及紧接的 Grassmannian--Plücker 投影说明](https://arxiv.org/html/math/0108133v4)：取其 $p=2,m=4$，源多项式次数至多五，目标次数至多八。该文讨论实数、复数上的 Wronski 投影；这里的任意特征零 $F$ 上线性公式及其与实际六向量的对应已由 (194.5)--(194.6) 直接证明。文献的实映射次数结论不作为本题原源相容性的输入，也没有假设 $SL_2$ 或 $PGL_2$ 是固定实际纤维的对称群。证毕。

## 195. 精确秩、六方向枢轴集合与实际嵌入维数

**定义 195.1（完整仿射相容性映射）。** 在固定图中置

$$
\overline\delta=\rho\delta\in\operatorname{Hom}_F(R,\mathcal Q),
\qquad
\mathcal L:\mathcal H\longrightarrow\operatorname{Hom}_F(R,\mathcal Q),
\quad
\mathcal L(k)(r)=\sum_{i=1}^{21}\rho\beta(k_i,\gamma_i(r)).
\tag{195.1}
$$

$\mathcal L$ 是线性映射，而

$$
\overline T_k=\overline\delta-\mathcal L(k)
\tag{195.2}
$$

对 $k$ 仿射线性、对 $r$ 线性。定义六方向参数集合

$$
Z_6=\{k\in\mathcal H:\mathcal L(k)=\overline\delta\}.
\tag{195.3}
$$

“六方向枢轴”专指 $E_s=L$ 的实际合法枢轴，不只是某一个评价的九系数为零。

**定理 195.2（所有固定枢轴的精确维数与六方向刻画）。** 对每个预先固定的实际合法 $s$，有

$$
\boxed{\dim_FE_s=6+\operatorname{rank}\overline T_{k_s}},
\qquad
\boxed{\operatorname{edim}A_s=111+\operatorname{rank}\overline T_{k_s}}.
\tag{195.4}
$$

因此 $E_s=L$ 当且仅当 $k_s\in Z_6$；全部六方向合法枢轴恰为满射 $s\mapsto k_s$ 下 $Z_6$ 的逆像。$Z_6$ 若非空，则对其中任意 $k^*$，

$$
Z_6=k^*+\ker\mathcal L,
\qquad \operatorname{codim}_{\mathcal H}Z_6=\operatorname{rank}\mathcal L.
\tag{195.5}
$$

对一个给定 $s$，有第七方向等价于 $\overline T_{k_s}\ne0$；检测达到全部十五维等价于 $\operatorname{rank}\overline T_{k_s}=9$。

证明。由共同实际六函数，$L\subseteq E_s$ 且 $\dim L=6$。由 (194.3)，$\rho|_{E_s}$ 的核恰为 $L$，像为 $\operatorname{im}\overline T_{k_s}$，秩核公式给 (195.4) 第一式。故 $E_s=L$ 等价于 $\overline T_{k_s}=0$，再由 (195.2) 得全部枢轴的精确刻画。若有一个解 $k^*$，将方程相减就得到 (195.5)；这里既未假设存在解，也未以仿射线性形式决定其可解性。

嵌入维数使用 046，定理 174.1、178.1、推论 178.2 的实际纤维短正合列。记 $\mathfrak m_s=\mathfrak m_{A_s}$，$\mathfrak n_s=\mathfrak m_{B_{0,s}}$，这些结果给

$$
\mathfrak n_s^3=\mathfrak m_s^3\subseteq\mathfrak m_s^2,
\qquad
0\longrightarrow J_4(A_s)/P_4
\longrightarrow\mathfrak m_s/\mathfrak m_s^2
\xrightarrow{\operatorname{in}_2}K\longrightarrow0.
\tag{195.6}
$$

该短列使用相同的域次数十四、相同负识别、相同检测器及任意预固定的实际 $s$；$P_4$ 正是其中的精确两重像 $K^2$。由 (193.2) 和 $\dim K=105$，取维数得到

$$
\operatorname{edim}A_s=105+\dim E_s
=111+\operatorname{rank}\overline T_{k_s}.
$$

047，定理 182.2 在这里取 $m=7$、阈值 $\lfloor(m-1)/2\rfloor=3$，给同一个尾项包含；其命题 186.1 给第一层 $K$ 和第二层 $J_4(A_s)/K^2$，命题 187.1 给同一检测商。故 (195.6) 及维数综合与该一般精确幂结论一致，没有添加未计算的高阶纤维余切残差。

这里没有计算完整源余切 $Q_S$：一个非零源类可以在取实际纤维像后成为乘积。短列也只给典范正合性，不给典范分裂。最后两个等价由目标 $\mathcal Q$ 的维数九及第一式得到。证毕。

## 196. 一个实际原源行给出的九余维下界

**定理 196.1（六方向集合为空或仿射余维至少九）。** 对定义 190.1 的每个 $F,D,\theta$ 及任意固定基枢轴图，

$$
\operatorname{rank}\mathcal L\ge9.
\tag{196.1}
$$

因此 $Z_6$ 为空，或为 $\mathcal H$ 中余维至少九的仿射 $F$ 子空间；非空时 $\dim Z_6\le2196$。更精确地，存在一个实际原源关系 $r_4\in R$，使

$$
H_4:=\{k\in\mathcal H:\overline T_k(r_4)=0\}
\tag{196.2}
$$

总是非空且余维恰九，并有 $Z_6\subseteq H_4$。$\mathcal H\setminus Z_6$ 是非空 Zariski 开稠密集；这不判定任何事先指定点是否属于 $Z_6$。

证明。取实际原函数

$$
h_4(C')=\frac{P_{C'}(\theta^4)}{P_{C'}(\theta^7)}\in S.
\tag{196.3}
$$

分母在 $C$ 是非零幂基体积，是原局部环中的单位。在 $C$ 处，十四列并置矩阵的列空间为 $\langle1,\theta,\ldots,\theta^{10}\rangle$，维数十一。行列式的每个低于三阶扰动项仍至少包含十二条原列，所以为零。故 $h_4$ 在完整光滑图中至少普通三阶消失；其一次正项和纯负二次项为零，$r_4=[h_4]\in R$。

用原交错图的 $u_{ij}$ 标记二十一条正一次方向，并令所选 $s^0$ 已对它们归一化为恒等。这与定义 191.1 相容。044，定理 163.2 的同一个原源变化适用于任意起始枢轴：只将第 $(1,5)$ 条改变为 $s^0_{15}+u(\kappa)$，$\kappa\in K$，检测差恰为

$$
-4\Omega\otimes\partial_{23}\kappa,
\qquad \partial_{23}=\frac{\partial}{\partial z_{23}}.
\tag{196.4}
$$

它保留同一 $Y$，而在一次居中图中对应 $k_{15}=\kappa$、其余 $k_i=0$。共同提升换用 (190.13) 不改变这个差，因为差只取决于提升的二次符号。具体地，044，(163.4)--(163.5) 的实际四次差是 $-2b^2\kappa$，$b=z_{05}+z_{14}$；其外乘满足 $\mu(b^2)=2e_{0145}$，只有 $z_{23}$ 与 $e_{0145}$ 外乘非零，按同一 $\Psi$ 约定给 (196.4)。没有另用一个比例未定的检测器。

复用 044，引理 163.1 的原 $F$ 右逆 $\mathcal R:W\to K$：

$$
\begin{aligned}
\mathcal R(z_{23})&=\tfrac12z_{23}^2,\\
\mathcal R(z_{ij})&=z_{23}z_{ij}
&&\bigl(\{i,j\}\cap\{2,3\}\ne\varnothing,\ (i,j)\ne(2,3)\bigr),\\
\mathcal R(z_{ij})&=z_{23}z_{ij}+z_{2i}z_{3j}
&&\bigl(\{i,j\}\cap\{2,3\}=\varnothing\bigr),\quad i<j.
\end{aligned}
\tag{196.5}
$$

前两类外乘因重复指标为零，第三类两个外乘项相消；修正项又不含 $z_{23}$，所以 $\mathcal R(W)\subseteq K$，$\partial_{23}\mathcal R=\operatorname{id}_W$。

若 $\delta(r_4)=\Omega\otimes d_0$，则由定理 193.1 与 (196.4)，上述实际枢轴给

$$
T_k(r_4)=\Omega\otimes(d_0-4\partial_{23}\kappa).
\tag{196.6}
$$

令 $\kappa=\mathcal R((d_0-\tau)/4)$，可把这个单独实际函数的检测调为任意 $\Omega\otimes\tau$。这正是已有单评价轨道在本图中的表达，未将不同目标拼成一个纤维内的多个方向。尤其 $\tau=0$ 也可实现。

对 (196.6) 施 $\rho$，因 $\omega:W\to\mathcal Q$ 满射，线性映射

$$
\operatorname{ev}_{r_4}\mathcal L:\mathcal H\longrightarrow\mathcal Q
\tag{196.7}
$$

已经满射。故 $\operatorname{rank}\mathcal L\ge9$，$H_4$ 是非空余维九的一个仿射纤维。$Z_6\subseteq H_4$ 由全关系方程蕴含这一行方程得到，再用 (195.5) 得维数界。若 $Z_6$ 非空，它是严格真仿射子空间，补集开稠密；若为空，补集就是整个 $\mathcal H$。$F$ 无限，真仿射子空间不能包含全部 $F$ 点，所以补集也有实际原域补偿，并由 (191.6) 实现。

$H_4$ 非空只说明 $h_4$ 的九系数可同时消去，不能说明完整系统有解；$Z_6$ 为真子集或空集也不能单独决定一个预固定 $k_s$。证毕。

## 197. 只用原系数函数的有限方程条目

**定义 197.1（完整原系数展示及权四条目）。** 在 $D$ 的原幂基上写 $x=\sum_{j=0}^{13}x_j\theta^j$，取原齐次多项式 $P_{C'}(x)$ 的全部 $F$ 系数线性泛函 $\lambda_\alpha$。令 $\lambda_0(P)=P(\theta^7)$，在 $\lambda_0\ne0$ 图上定义有限组中心化实际函数

$$
f_\alpha(C')=
\frac{\lambda_\alpha(P_{C'})}{\lambda_0(P_{C'})}
-\frac{\lambda_\alpha(P_C)}{\lambda_0(P_C)}
\in\mathfrak m_S,
\qquad 1\le\alpha\le N.
\tag{197.1}
$$

这里可以保留全部有限系数，不要求挑出最小组；重复或线性冗余不影响定义。它们给完整原系数图的坐标，类张成 $Q_S$；统一开集及局部化只反演在该点非零的函数，不增加余切生成元。

在固定基枢轴图中，分别取每个实际 $f_\alpha$ 的权二及权四项：

$$
f_\alpha^{[2]}=\sum_i A_{\alpha i}U_i+q_\alpha,
\qquad q_\alpha\in K,
\tag{197.2}
$$

$$
f_\alpha^{[4]}=A_\alpha^{(4)}(U)
+\sum_iU_i c_{\alpha i}(Y)+d_\alpha(Y),
\quad c_{\alpha i}\in Q_2,\quad d_\alpha\in\operatorname{Sym}^4W.
\tag{197.3}
$$

所有项均从实际函数在这同一图中的形式展开取出，包括居中坐标带来的校正；不使用未经运输的裸图项替代。定义有限原系数关系空间

$$
R_{\mathrm{lin}}=
\left\{t\in F^N:
\sum_\alpha t_\alpha A_{\alpha i}=0\ (1\le i\le21),\quad
\sum_\alpha t_\alpha q_\alpha=0\right\}.
\tag{197.4}
$$

取其任意 $F$ 基 $t_1,\ldots,t_m$，置

$$
h_j=\sum_\alpha t_{j\alpha}f_\alpha\in\mathfrak m_S,
\qquad r_j=[h_j]\in R.
\tag{197.5}
$$

再取 $K$ 的任意 $F$ 基 $b_1,\ldots,b_{105}$。定义矩阵和右端的全部条目为

$$
\begin{aligned}
\mathsf D_{\nu j}
&=[T^\nu]\rho\Psi\left(\sum_\alpha t_{j\alpha}d_\alpha\right),\\
\mathsf B_{\nu j;ia}
&=[T^\nu]\rho\Psi\left(b_a\sum_\alpha t_{j\alpha}c_{\alpha i}\right),
\end{aligned}
\quad
\begin{gathered}
0\le\nu\le8,\quad1\le j\le m,\\
1\le i\le21,\quad1\le a\le105.
\end{gathered}
\tag{197.6}
$$

这些是原 $F$ 中的有限条目，不由分裂标签中任意另选的源给出。它们分别等于 $[T^\nu]\overline\delta(r_j)$ 和 $[T^\nu]\rho\beta(b_a,\gamma_i(r_j))$。

**定理 197.2（完整实际像与六方向集合的有限原系数系统）。** 自然映射

$$
R_{\mathrm{lin}}\longrightarrow R,
\qquad t\longmapsto\left[\sum_\alpha t_\alpha f_\alpha\right]
\tag{197.7}
$$

满射，其核被全部 $\gamma_i$ 和 $\delta$ 消去。因此若 $k_i=\sum_a x_{ia}b_a$，则

$$
\boxed{k\in Z_6\quad\Longleftrightarrow\quad
\sum_{i,a}\mathsf B_{\nu j;ia}x_{ia}=\mathsf D_{\nu j}
\quad\text{对全部 }\nu,j.}
\tag{197.8}
$$

同时 $\operatorname{rank}\overline T_k$ 恰为有限矩阵

$$
\left(\mathsf D_{\nu j}-\sum_{i,a}\mathsf B_{\nu j;ia}x_{ia}\right)_{\nu,j}
\tag{197.9}
$$

的秩。这个展示不要求计算完整源余切的关系理想或维数。

证明。$f_\alpha$ 的类张成 $Q_S$。任意 $r\in R$ 先用它们在 $Q_S$ 中表示；所得系数向量的 $J$ 像为零，按 (197.2) 恰在 $R_{\mathrm{lin}}$ 中，故 (197.7) 满射。若一个向量映为零，则相应实际原函数在 $\mathfrak m_S^2$ 中，定理 192.2 已证明其全部 $\gamma_i,\delta$ 为零。故可能未知的源关系只给重复方程，不改变任何实际检测值。

对 $h_j$，权二项为零，(197.3) 中的混合项、纯四次项正是定义 192.1 的项。将 $k_i$ 的基展开代入 (193.1)，再取九系数，就得到 (197.8) 和 (197.9)。$r_j$ 张成 $R$，所以该矩阵的列张成 $\operatorname{im}\overline T_k$，不要求 $r_j$ 线性独立。

这也与 047，命题 187.1 的固定纤维公式相容：若原理想生成元在实际纤维上展开为 $d_i+e_i+O(Y^6)$，该公式是 $E_s=\Psi D_4(\ker D_2)$。本式以完整原系数生成元在一张固定图内的权二、权四项展示同一零二次条件，并用 (193.5) 将其转为 $R$ 上的关系，因而没有用较小评价子族代替完整原源。证毕。

## 198. 原系数相容性的必要充分有限对偶证书

**定理 198.1（六方向集合空性的原源证书等价）。** 对定义 190.1 的每个固定原域族，下列条件等价：

1. $Z_6=\varnothing$。
2. 存在 $\eta\in\operatorname{Hom}_F(R,\mathcal Q)^\vee$，使 $\eta\circ\mathcal L=0$ 且 $\eta(\overline\delta)=1$。
3. 存在有限个原 $F$ 数 $y_{\nu j}$，使

$$
\sum_{\nu,j}y_{\nu j}\mathsf B_{\nu j;ia}=0
\quad\text{对每个 }i,a,
\qquad
\sum_{\nu,j}y_{\nu j}\mathsf D_{\nu j}=1.
\tag{198.1}
$$

4. 存在九个原源关系 $r_0',\ldots,r_8'\in R$，每个都可取实际原函数代表 $h_\nu'\in\mathfrak m_S$，使

$$
\sum_{\nu=0}^8[T^\nu]\rho\beta(b_a,\gamma_i(r_\nu'))=0
\quad\text{对每个 }i,a,
\qquad
\sum_{\nu=0}^8[T^\nu]\overline\delta(r_\nu')=1.
\tag{198.2}
$$

取得任一个这样的证书后，这同一有限批实际原函数在每个预固定实际纤维上至少有一个检测值超出 $L$。若反而取得 (197.8) 的完整解 $x^*$，则

$$
s_i^*=s_i^0+\sum_a x_{ia}^*u(b_a)
\tag{198.3}
$$

给原 $F$ 中的实际六方向合法枢轴。本定理是证书存在的充要判据，不断言已取得任何这样的具体证书或完整解。

证明。所有空间均有限维。$Z_6$ 为空恰为 $\overline\delta\notin\operatorname{im}\mathcal L$。若如此，它在商空间

$$
\operatorname{Hom}_F(R,\mathcal Q)/\operatorname{im}\mathcal L
$$

中的类非零；将这个类扩充为一组基，在该类上取值一、其余基向量上取值零，拉回得到条件 2 的 $\eta$。反之，若 $\mathcal L(k)=\overline\delta$，条件 2 会给 $0=1$，矛盾。这只是本原源相容性方程所需的有限维分离步骤。

按定理 197.2，用 $R_{\mathrm{lin}}$ 的基拉回后，完整系统就是有限线性映射 $x\mapsto\mathsf Bx$ 的方程 $\mathsf Bx=\mathsf D$。同样在其像的商空间上分离 $\mathsf D$，得到左零空间中取右端值一的 $y$，恰为 (198.1)；反向乘方程求和仍给矛盾。因此条件 1 与 3 等价。这没有假定 $R_{\mathrm{lin}}\simeq R$。

令 $\varepsilon^\nu\in\mathcal Q^\vee$ 为第 $\nu$ 次系数泛函。有限维对偶的正确对应是

$$
\operatorname{Hom}_F(R,\mathcal Q)^\vee
\simeq R\otimes\mathcal Q^\vee,
\qquad
r\otimes\lambda\longmapsto\bigl(A\mapsto\lambda(A(r))\bigr).
\tag{198.4}
$$

这里不可删掉 $\operatorname{Hom}$ 外面的对偶号。每个 $\eta$ 唯一写为 $\sum_{\nu=0}^8r_\nu'\otimes\varepsilon^\nu$；条件 $\eta\mathcal L=0$ 只需对 $\mathcal H$ 的各基坐标检验，正好给 (198.2)。反向也由此构造 $\eta$，证明条件 2 与 4 等价。矩阵形式中还可明确取

$$
h_\nu'=\sum_jy_{\nu j}h_j,\qquad
r_\nu'=[h_\nu'],
\tag{198.5}
$$

每个代表都属于同一个真实原 $S$。

若这些条件成立，则对任意一个固定 $k$ 都有

$$
\sum_{\nu=0}^8[T^\nu]\overline T_k(r_\nu')=1.
\tag{198.6}
$$

故至少一项来自非零 $\overline T_k(r_\nu')$。该 $h_\nu'$ 在这个实际纤维中常数、二次项为零，检测超出 $L$，而共同六个原函数在同一纤维中同时存在。这是 $\forall s\,\exists\nu$ 的结论，不要求一个固定的 $\nu$ 对全部枢轴有效，也没有合并不同纤维的值。

若有完整解 $x^*$，(191.6) 保证 (198.3) 实际且合法，(197.8) 和 (195.4) 给 $E_{s^*}=L$、$\operatorname{edim}A_{s^*}=111$。最后，(197.8) 在任意域扩张后可解当且仅当在原 $F$ 上可解：若原域无解，(198.1) 的原域证书在扩域后仍给 $0=1$；若原域有解则直接扩域。此事实消除了这个有限线性系统额外的算术下降障碍，但不决定实际右端是否属于像。证毕。

## 199. 消去已知单行后的首个未定原源相容性

**定义 199.1（已消去的四次评价与剩余方程）。** 用定理 196.1 的 $r_4$，写 $\delta(r_4)=\Omega\otimes d_0$。取补偿 $k^4\in\mathcal H$ 为

$$
k^4_{15}=\mathcal R(d_0/4),\qquad
k^4_i=0\quad(i\ne15),
\tag{199.1}
$$

其中 $15$ 表示原交错标记 $(1,5)$。这是实际可达的补偿，且 $T_{k^4}(r_4)=0$。定义

$$
\mathcal H_0=\ker(\operatorname{ev}_{r_4}\mathcal L),
\qquad
\mathcal C_0=\{A\in\operatorname{Hom}_F(R,\mathcal Q):A(r_4)=0\},
\tag{199.2}
$$

$$
\Delta=\overline\delta-\mathcal L(k^4)\in\mathcal C_0,
\qquad
\mathcal L_0=\mathcal L|_{\mathcal H_0}:\mathcal H_0\longrightarrow\mathcal C_0.
\tag{199.3}
$$

**定理 199.2（剩余原源问题的精确形式与受限族边界）。** 在这些定义下，

$$
Z_6=k^4+\{v\in\mathcal H_0:\mathcal L_0(v)=\Delta\},
\qquad
Z_6\ne\varnothing\quad\Longleftrightarrow\quad
\Delta\in\operatorname{im}\mathcal L_0.
\tag{199.4}
$$

若只在一个实际原源子空间 $R'\subseteq R$ 上要求 $\overline T_k|_{R'}=0$，记解集为 $Z(R')$，则 $Z_6\subseteq Z(R')$。因此受限系统无解足以证明完整系统无解；受限系统有解不能推出 $Z_6$ 非空，除非另证全部剩余关系也满足方程。

证明。$k^4$ 使 $r_4$ 的完整检测为零，故 $\Delta(r_4)=0$。若 $k\in Z_6$，则 $\mathcal L(k)=\overline\delta$，在 $r_4$ 上减去 $k^4$ 的方程，得到 $k-k^4\in\mathcal H_0$，且 $\mathcal L_0(k-k^4)=\Delta$。反向将这两个式子相加即可恢复完整方程，给 (199.4)。受限集合的包含直接由限制映射得到，两个推论随之成立。

例如 $R'$ 可取 044，§§157--159 的全部原互素二元三次有理评价类的张成。这些函数确实属于原 $S$，且其全部固定纤维检测均属于 $L$；该限制不能提供新的第七方向。也可取任何已证明属于 $R$ 的较大实际评价族，但有限环境张量或未证明原源成员资格的候选不构成这样的 $R'$。证毕。

**定义 199.3（尚未判定的原源问题，open）。** 对给定的 $F,D,\theta$ 及基枢轴图，首个完整相容性问题是 (199.4) 的 $\Delta\in\operatorname{im}\mathcal L_0$ 与否，等价地是 (197.8) 是否有原 $F$ 解。一个完整解和一个满足 (198.1) 的非零归一化对偶证书是互斥的两种数学见证；这里均未指定其实际系数。

对每个预先给定且不改变的 $s$，首个方向问题仍是 $\overline T_{k_s}\ne0$ 与否。所需新函数必须来自同一个实际原源，并在这个纤维上有零常数、零二次项。定理 196.1 的单行满射、一般参数的七方向及九余维界都不能代替完整方程的相容性判定，也不能决定 $Z_6$ 为空或非空。即使确定某个 $E_s$ 达到十五维，也只是该实际纤维的检测像结论。

## 200. 完整的普通中文数学释义

**定义 200.1（“调节”“只余六方向”与有限证书的含义）。** 本文的“调节”是保持一个实际十四次域、一个本原元、七个连续幂窗口、全部原符号标签系数和同一组负坐标不变，只改变原系数局部环中的二十一条合法正枢轴。先选一次真实基枢轴，把它们本身作为正坐标。每个未来枢轴归一化后，其二次差是一百零五维二次核空间中的一个元素；二十一条差可以在原域里任意同时指定，都有真正的原系数函数实现。

一个原函数在正规化中没有一次正项和纯负二次项时，它的源余切类属于关系空间。它接下来可能有正变量两两相乘的项、正变量乘负二次的项，以及纯负四次项。纯负四次项经检测得到一个固定向量；每个混合项只需保留其外四次商。真正解掉枢轴后，整个检测值就是这个固定向量减去二十一项补偿配对。正变量两两相乘的贡献是两个真实可见二次信息的乘积，检测后为零。换原代表也只改变这些真实乘积，所以公式与代表无关。

这不只是某批评价函数的公式。任意完成源函数，只要在指定实际纤维上的常数和二次项都消失，都可以先用一个原函数匹配到足够阶数，再减去真实枢轴，得到上述关系类；它们检测值完全相同。因此整个实际四次检测像正好是这个有限线性映射的像。未来枢轴更高阶的尾巴不影响它，但这没有把整个实际环认作相同，也没有把源环简单除以枢轴理想。

已知六个方向在每一个同一固定纤维中同时存在。它们恰好是一个多项式 Wronski 线性映射的核，所以六方向以外的全部信息可以无遗漏地写成一个至多八次多项式的九个系数。一个固定纤维的检测维数，精确等于六加这个九系数映射的秩。检测维数再加上一百零五，就是实际纤维的嵌入维数，因此它精确等于一百一十一加同一个秩；六次及更高的纤维尾项已由真实乘积吸收，不再另留余切方向。

“只余六方向”要求所有原源关系的九系数同时为零，因此是一个共同的有限仿射线性方程组。解集若存在，就是一个仿射子空间，余维至少九；也允许它完全没有解。单个四次评价可以通过一条实际枢轴变化被调到任意检测值，包括零。这证明至少九个独立调节约束，却不说明全部原源关系能否同时调零。不同调节后纤维中的分别可达值，不能合成原来那个固定纤维中的十五个方向。

完整方程只需原系数函数的一次有限展示及权二、权四项，不必先知道完整源关系理想。若找到有限个原域权重，使所有未知补偿列的加权和为零、而右端加权和为一，就证明方程无解；还可把这些权重合成为九个真实原函数，它们在每个固定纤维中至少有一个提供第七方向。反之，若找到完整方程的一个原域解，就能直接构造真正只有六方向的合法枢轴。给出这个必要充分判据，不等于已经找到了其中任何一种实际系数。尚未确定的正是全部原系数关系是否共同相容；因而任意预固定枢轴的统一第七方向、例外集的空或非空，以及统一十五维结论仍不能由本文的有限归约直接断言。

## 201. 数学前置的精确范围

**定义 201.1（固定来源与实际原源综合的边界）。** 本文的原族前置限于下列固定数学来源，文献中的经典 Wronski 构造只在定理 194.2 的实际源商证明内使用。

| 固定来源 | 采用的精确数学内容 |
| --- | --- |
| [039，e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb，§§111、113、115、117](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) | 原符号标签系数像、实际乘法商、有限正规化、原剩余域及对合横截面。 |
| [040，f32f2d3b8219fae2014e5db4ab3c31575edf0672，定理 122.1、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) | 原耦合余切像、正投影满射及纯负交恰为 $K$；不计算完整源余切。 |
| [042，fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6，§§132--134、定理 139.1](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) | 原负识别、实际正纤维、全部二次像和源核到实际四次商的满射。 |
| [044，74b08723d9c5fb45657df8015bfd47a366f7b199，§§151--153、157--159、163、165](https://github.com/the-omega-institute/trureturing/blob/74b08723d9c5fb45657df8015bfd47a366f7b199/docs/develop/theory/AURIC_R5_044_RATIONAL_EVALUATOR_QUARTICS_AND_ACTUAL_POSITIVE_PIVOT_CONTROL.md) | 共同六个原函数及确切六基、完整有理三次族的检测范围、全部实际补偿、单个 $\theta^4$ 评价轨道及九维补空间。 |
| [045，a5a20d82984bbb32282adccee504bbcd41fc7ac1，定义 168.1、定理 168.2、引理 170.1、§172](https://github.com/the-omega-institute/trureturing/blob/a5a20d82984bbb32282adccee504bbcd41fc7ac1/docs/develop/theory/AURIC_R5_045_FAITHFUL_QUARTIC_DETECTION_AND_COMPLETE_ORIGINAL_EVALUATOR_RELATIONS.md) | 唯一检测约定、精确核 $P_4$、共同实际原源乘积提升，以及高阶源类与纤维类的区别。 |
| [046，9b1e19f102fb2f399677cae4b720d631afcc1245，定理 174.1、178.1、推论 178.2、§179](https://github.com/the-omega-institute/trureturing/blob/9b1e19f102fb2f399677cae4b720d631afcc1245/docs/develop/theory/AURIC_R5_046_EXACT_CUBIC_PRODUCTS_AND_ACTUAL_HIGH_ORDER_FIBRE_CLOSURE.md) | 次数十四的实际六阶尾项闭合、余切短列与固定纤维有限四次公式。 |
| [047，e644713d989718374b8ae490ade60d371381837f，定理 182.2、命题 186.1--186.2、命题 187.1](https://github.com/the-omega-institute/trureturing/blob/e644713d989718374b8ae490ade60d371381837f/docs/develop/theory/AURIC_R5_047_EXACT_QUADRATIC_POWERS_AND_UNIFORM_ACTUAL_FIBRE_CUTOFF.md) | 一般域次数的精确幂与有限实际源层；这里只用 $m=7$ 的阈值三及二、四次层，未把其他次数的层数误作本题层数。 |

此有限对应中的 `repo-derived` 内容是把原源关系上的代表无关数据组织成同一仿射族，精确给出整个实际检测像、九系数六方向集合、九余维界、原系数有限条目及必要充分对偶证书，并接到实际纤维余切短列。Wronski 投影及有限维分离是 `literature-attested` 的经典工具；它们本身不给原源混合项、实际枢轴实现或完整反向包含。上述对应不声称穷尽仓内或外部文献，不提出全球新颖性判断。

本文未决定 (199.4) 的实际相容性，未计算完整源或完整评价源余切，未证明 $\ker\pi_s=(s)\mathscr T$，也未从四次符号及嵌入维数推出完整形式芽分类、全局导子、H10 或物理结论。全部实际公式的量词保持同一个可分域、本原元、原连续幂窗口和指定的固定纤维。

## 追加锚（本行以下为增补区）
