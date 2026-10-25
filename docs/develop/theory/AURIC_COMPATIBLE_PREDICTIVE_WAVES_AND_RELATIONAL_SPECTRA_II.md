# AURIC 相容预测波与关系谱 II：原生标签历史的后继辨识

## 39. 固定原生仪器、完整联合记录与后继接口

**定义 39.1（供应对象与复数约定）。** 本卷接续[第一卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)，编号从 §39 起。固定第一卷 §17.1、定义 29.1、定义 35.1 的同一个五维物理空间 $H=\mathbb C^5$、等距嵌入 $B:\mathbb C^3\to H$、实际 Kraus 算子 $K_0,K_1$、qutrit 酉 $U,W$ 及向量 $\xi,e,f,q,r$。记

$$
\begin{gathered}
P_+=(I_3+W)/2,\qquad P_-=ff^\dagger,\qquad
E=qq^\dagger,\qquad P=BEB^\dagger,\\
(a,h_{\rm out},g)=(Uq,Ur,Uf),\qquad
C=(a+h_{\rm out})(a+h_{\rm out})^\dagger=2\xi\xi^\dagger,\\
0<d<1,\qquad t=\sqrt d,\qquad \beta=1-d,\qquad
e_d=(6-5d)/16,\qquad \tau=3-2\sqrt2.
\end{gathered}
\tag{39.1}
$$

这里 $h_{\rm out}$ 是后继基向量；下文的 $h$ 专指时间词。通道均为复线性 CPTP，伴随为迹配对伴随，$M_k=M_k(\mathbb C)$。正性与迹约束作用于全部复 Hermitian 矩阵。原通道纤维 $\mathcal F_t$、忠实后继集合 $\mathcal K_d$ 取第一卷 (35.1)、(35.4)–(35.5)，不限制原通道的输出支持或 Kraus 秩。第一卷定理 35.2、35.4 供应

$$
\begin{aligned}
\{\mathcal GT:T\in\mathcal F_t\}
 &=\{S_\rho:\rho\in\mathcal K_d\},\\
S_\rho(X)
 &=B\bigl[UP_+XP_+U^\dagger+(f^\dagger Xf)\rho\bigr]B^\dagger,
 \qquad X\in M_3.
\end{aligned}
\tag{39.2}
$$

此供应等式包括所有复输入矩阵及任意有限未触动参考。每个 $\rho\in\mathcal K_d$ 都有原域提升 $T\in\mathcal F_t$；本卷不把仅满足部分矩条件的矩阵替代为完整相容集合。

**假设 39.2（实际扩大的记录菜单与精确数据）。** 固定一个已知实角度 $\theta$。同一物理仪器的两个实际分支为

$$
A_0=\cos\theta K_0+\mathrm i\sin\theta K_1,
\qquad
A_1=\mathrm i\sin\theta K_0+\cos\theta K_1.
\tag{39.3}
$$

每次使用具有原供应的就绪环境、相互作用、固定测量基和环境丢弃规则。允许在 $S_\rho$ 的输出上重复这一固定仪器，保留每个实际标签，并在事先指定的有限终点测原二元任务 $(P,I_5-P)$。终点独立于随机历史给定；比较不同终点的数据不要求同一份样本同时具有多个终点。所有分支、终端结果及其原始联合权重均在记录内。没有在分支间插入量子反馈、修正或其他门。

本卷的算子数据版本以精确给定的响应算子为前提。概率数据版本以相应输入合同实际给定的精确联合概率为前提；它不赋予原合同之外的输入制备、系综、独立副本或参考读出。有限样本不等同于精确实概率。已知 $\theta$ 是条件，不包含标定 $\theta$ 的操作，也不包含改变它的控制。

复 Hilbert 空间、CPTP 组合和 Born 迹配对是本卷的模型前提。保留标签与重复原仪器不增加环境量子访问、环境基选择、新相位参考、逆操作、任意门或时钟资源。终点的指定仅沿用供应的时序合同。

**定理 39.3（实际联合效果的时间词桥）。** 置

$$
\begin{gathered}
V_0=U\exp(\mathrm i\theta W),\qquad V_1=V_0W,\\
h=(j_1,\ldots,j_n),\qquad
A_h=A_{j_n}\cdots A_{j_1},\qquad
V_h=V_{j_n}\cdots V_{j_1},\\
A_\varnothing=I_5,\qquad V_\varnothing=I_3,\qquad
M_h=V_h^\dagger EV_h,\qquad Z_h=2^{-n}M_h.
\end{gathered}
\tag{39.4}
$$

词中最左字母 $j_1$ 最早作用。对任意有限词，实际压缩效果及其补效果恰为

$$
\begin{aligned}
A_hB&=2^{-n/2}BV_h,\\
B^\dagger A_h^\dagger PA_hB&=Z_h,\\
B^\dagger A_h^\dagger(I_5-P)A_hB&=2^{-n}I_3-Z_h.
\end{aligned}
\tag{39.5}
$$

因此对任意 qutrit 密度 $\eta$，事件“历史为 $h$ 且终端回答为是”的概率为 $\operatorname{Tr}(\eta Z_h)$，该历史的总概率为 $2^{-n}$。这些是完整联合事件，不是归一化条件实验。

证明。第一卷 §17.1 的原矩阵恒等式给

$$
K_0B=BU/\sqrt2,\qquad K_1B=BUW/\sqrt2.
$$

由于 $W^2=I_3$，$\exp(\mathrm i\theta W)=\cos\theta I_3+\mathrm i\sin\theta W$，故

$$
\begin{aligned}
A_0B&=\tfrac1{\sqrt2}BU(\cos\theta I_3+\mathrm i\sin\theta W)
      =\tfrac1{\sqrt2}BV_0,\\
A_1B&=\tfrac1{\sqrt2}BU(\mathrm i\sin\theta I_3+\cos\theta W)
      =\tfrac1{\sqrt2}BV_0W.
\end{aligned}
$$

这里的次序是 $U\exp(\mathrm i\theta W)$。逐步相乘得到 (39.5) 第一式；再用 $B^\dagger PB=E$、$B^\dagger B=I_3$ 和 $V_h$ 酉性，得到其余两式。两种终端结果求和给 $2^{-n}I_3$，故历史总概率没有依赖 $\eta$，也没有丢弃任何其他历史。∎

**定理 39.4（任意非理想后继的成对数据桥）。** 对 $y\in\{0,1\}$ 置 $P_1=P$、$P_0=I_5-P$，并定义原输入上的响应

$$
D_{h,y}(\rho)=S_\rho^\dagger(A_h^\dagger P_yA_h),\qquad
M_{h,1}=M_h,\qquad M_{h,0}=I_3-M_h.
\tag{39.6}
$$

则对全部 $\rho\in\mathcal K_d$ 和所有有限词，

$$
D_{h,y}(\rho)
=2^{-|h|}\bigl[P_+U^\dagger M_{h,y}UP_+
       +\operatorname{Tr}(\rho M_{h,y})ff^\dagger\bigr].
\tag{39.7}
$$

令

$$
\mathcal V_\theta
=\operatorname{span}_{\mathbb R}\bigl(\{I_3\}\cup\{Z_h:h\text{ 为有限词}\}\bigr).
\tag{39.8}
$$

对任意 $\rho,\sigma\in\mathcal K_d$，下列条件等价：全部扩大的响应算子相等；对全部原输入密度矩阵，完整联合概率表相等；$\rho-\sigma\in\mathcal V_\theta^\perp$。正交补取 Hermitian 空间内的实迹配对。

证明。将 (39.5) 代入 (39.2) 的迹伴随，直接得 (39.7)。两后继的响应差为

$$
D_{h,y}(\rho)-D_{h,y}(\sigma)
=2^{-|h|}\operatorname{Tr}((\rho-\sigma)M_{h,y})ff^\dagger.
\tag{39.9}
$$

密度矩阵的迹同为一，故只需是效果及 $I_3$。零响应差显然给全部输入概率相等；反向，Hermitian 响应差在所有密度矩阵上的期望为零便是零算子。也可在 (39.9) 中直接取输入 $ff^\dagger$。因而完整数据相等恰是消去全部词效果。

这里消费的是[量子原则与相干重建](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)定义 11.3、定理 11.4 和应用 28.2 的观察空间判据。其参数对应为：完整载体 $\mathbb C^3$，单一固定动作的两个分支 $X\mapsto V_jXV_j^\dagger/2$，初始效果空间 $\operatorname{span}_{\mathbb R}\{I_3,E\}$。相应分支对偶为 $H\mapsto V_j^\dagger HV_j/2$；词域是全部有限二元时间词，补效果由同一分支总质量确定。

同一对应把[延续效果闭包](../../../Blueprint/D5/S3/Quantum/Measurement/ContinuationEffectClosure.md)定理 1.3 应用于 (39.8)：其数学声明为 [continuationSpace_closure](../../../D5/S3/Quantum/Measurement/ContinuationEffectClosure.lean)，矩阵维数为三，每个分支只有一个 Kraus 算子 $V_j/\sqrt2$，初始实维数为二。它给最小分支对偶不变空间及至多第七层的稳定。下节对这一个实际源给出更短的明确基和全部角度的精确分类。此处没有把有限维闭包或观察空间的一般判据另立为新定理。∎

## 40. 全实角度的有限轨道与精确消去子

**定理 40.1（固定源的全部角度分类）。** 对每个实 $\theta$，(39.8) 满足

$$
\mathcal V_\theta=
\begin{cases}
\operatorname{Herm}_3(\mathbb C),&\sin(2\theta)\ne0,\\
\operatorname{span}_{\mathbb R}\{I_3,E,C,aa^\dagger\},
  &\theta\in(\pi/2)\mathbb Z.
\end{cases}
\tag{40.1}
$$

第一种情形的一个实际有限基为 $I_3$ 和以下八个词的联合是效果：

$$
\mathcal H=(\varnothing,0,1,00,10,000,010,100).
\tag{40.2}
$$

最大词长为三。第二种情形的空间实维数恰为四，第零层实维数为二，第一个延续层即已达到全部空间。没有其他例外角度。

更精确地，在正交基 $(\xi,e,f)$ 中对 Hermitian 矩阵取实坐标

$$
\operatorname{coord}(H)
=(H_{00},H_{11},H_{22},\Re H_{01},\Re H_{02},\Re H_{12},
  \Im H_{01},\Im H_{02},\Im H_{12})^{\mathsf T}.
\tag{40.3}
$$

按列次序 $I_3,M_\varnothing,M_0,M_1,M_{00},M_{10},M_{000},M_{010},M_{100}$ 组成坐标矩阵 $\mathscr M_\theta$；把各 $M_h$ 换成实际 $Z_h$ 得 $\mathscr Z_\theta$。则

$$
\det\mathscr M_\theta=\frac{6561}{2^{21}}\sin^7(2\theta),\qquad
\det\mathscr Z_\theta=\frac{6561}{2^{36}}\sin^7(2\theta).
\tag{40.4}
$$

证明。在 $(\xi,e,f)$ 中原矩阵为

$$
U=\begin{pmatrix}1&0&0\\0&-1/2&\sqrt3/2\\0&\sqrt3/2&1/2\end{pmatrix},\quad
W=\operatorname{diag}(1,1,-1),\quad
E=\frac12\begin{pmatrix}1&1&0\\1&1&0\\0&0&0\end{pmatrix}.
\tag{40.5}
$$

置 $z=e^{-2\mathrm i\theta}$。仅在计算共轭效果时，可从两个 $V_j$ 同时去掉公共标量相位 $e^{\mathrm i\theta}$，写成

$$
V'_0=U\operatorname{diag}(1,1,z),\qquad
V'_1=U\operatorname{diag}(1,1,-z).
\tag{40.6}
$$

这不改变任何 $M_h$ 或联合概率。令 $x_h=(V'_h)^\dagger q$；则 $M_h=x_hx_h^\dagger$。以下四个向量完全确定需要的八个效果，连同 $x_\varnothing=q$：

$$
\begin{aligned}
x_0&=\begin{pmatrix}1/\sqrt2\\-1/(2\sqrt2)\\\sqrt6/(4z)\end{pmatrix},\\
x_{00}&=\begin{pmatrix}1/\sqrt2\\\sqrt2(z+3)/(8z)\\-\sqrt6(z-1)/(8z^2)\end{pmatrix},\\
x_{000}&=\begin{pmatrix}1/\sqrt2\\-\sqrt2(z^2+6z-3)/(16z^2)\\\sqrt6(z+1)^2/(16z^3)\end{pmatrix},\\
x_{010}&=\begin{pmatrix}1/\sqrt2\\-\sqrt2(z^2+3)/(16z^2)\\\sqrt6(z^2+4z-1)/(16z^3)\end{pmatrix}.
\end{aligned}
\tag{40.7}
$$

例如 $x_{j_1\cdots j_n}=(V'_{j_1})^\dagger\cdots(V'_{j_n})^\dagger q$，故 (40.7) 由 (40.5)–(40.6) 逐次相乘得到；这也钉定了词的方向。又因 $V'_1=V'_0W$，

$$
M_1=WM_0W,\qquad M_{10}=WM_{00}W,\qquad
M_{100}=WM_{000}W.
\tag{40.8}
$$

以下给出行列式的实代数分块。记 $c_\theta=\cos(2\theta)$、$s_\theta=\sin(2\theta)$，在本证明的矩阵中简写为 $c,s$。对三个词对

$$
(u_1,v_1)=(0,1),\quad (u_2,v_2)=(00,10),\quad
(u_3,v_3)=(000,100)
$$

取 $S_\ell=(M_{u_\ell}+M_{v_\ell})/2$、$D_\ell=(M_{u_\ell}-M_{v_\ell})/2$。$S_\ell$ 在 $H\mapsto WHW$ 下为偶，$D_\ell$ 为奇。偶空间坐标取

$$
(H_{00},H_{11},H_{22},\Re H_{01},\Im H_{01}),
$$

奇空间坐标取 $(\Re H_{02},\Re H_{12},\Im H_{02},\Im H_{12})$。把 (40.7) 代入，列 $I_3,E,S_1,S_2,S_3$ 的偶坐标矩阵恰为

$$
\mathscr E=\frac1{32}
\begin{pmatrix}
32&16&16&16&16\\
32&16&4&10+6c&13-6c-3c^2\\
32&0&12&6-6c&3+6c+3c^2\\
0&16&-8&4+12c&12c^2-12c-8\\
0&0&0&-12s&12(1-c)s
\end{pmatrix}.
\tag{40.9}
$$

列 $D_1,D_2,D_3,M_{010}$ 的奇坐标矩阵恰为

$$
\mathscr O=\frac{\sqrt3}{32}
\begin{pmatrix}
8c&8c^2-4c-4&8c^3+8c^2-4c-4&-8c^3+16c^2+8c-8\\
-4c&2c^2+2c-4&-c^3-4c^2-c+2&c^3-2c^2-c-2\\
-8s&(4-8c)s&(-8c^2-8c)s&(8c^2-16c-4)s\\
4s&(-2c-2)s&(c^2+4c+3)s&(-c^2+2c-1)s
\end{pmatrix}.
\tag{40.10}
$$

这两张矩阵的条目只使用 $z=c-\mathrm i s$、$z^{-1}=c+\mathrm i s$ 和 $c^2+s^2=1$。沿 (40.9) 最后一行展开，以及在 (40.10) 后两行各取出 $s$ 后展开，分别给

$$
\begin{aligned}
\det\mathscr E
 &=-\frac{81}{2048}s(c-1)(c+1)=\frac{81}{2048}s^3,\\
\det\mathscr O
 &=\frac{81}{8192}s^2(c-1)(c+1)=-\frac{81}{8192}s^4.
\end{aligned}
\tag{40.11}
$$

为同时核对完整行列式的符号与常数，把 $\mathscr M_\theta$ 的每一词对换成其平均和半差。三个二列变换的总行列式为 $(-1/2)^3$。把所得列排为

$$
(I_3,E,S_1,S_2,S_3,D_1,D_2,D_3,M_{010})
$$

并把坐标 (40.3) 排为先偶后奇，这两次重排均为偶置换。于是得到以 $\mathscr E,\mathscr O$ 为对角块的上三角块矩阵；$M_{010}$ 的偶部分仅出现在右上块。因此

$$
\det\mathscr M_\theta
=-8\det\mathscr E\det\mathscr O
=\frac{6561}{2^{21}}s^7.
\tag{40.12}
$$

等价的 Laurent 形式是

$$
\det\mathscr M_\theta
=-\frac{6561\mathrm i}{2^{28}}\frac{(z-1)^7(z+1)^7}{z^7},
\qquad z-z^{-1}=-2\mathrm i\sin(2\theta).
\tag{40.13}
$$

实际八个词长的和为 $0+1+1+2+2+3+3+3=15$；各列的原联合权重再给 $2^{-15}$，证明 (40.4)。当 $s\ne0$，九列因而独立，达到整个九维 Hermitian 空间。更深效果仍为 Hermitian，不能再扩大它。

当 $\theta=k\pi/2$ 时，$\exp(\mathrm i\theta W)=\mathrm i^kW^k$。所以 $V_j$ 为 $UW^{k+j}$ 的标量相位倍数。记

$$
E_a=aa^\dagger,\qquad E_b=Waa^\dagger W.
$$

由 (40.5)，$U^\dagger EU=E_a$、$U^\dagger E_aU=E$、$U^\dagger E_bU=E_b$，而 $WEW=E$、$WE_aW=E_b$、$WE_bW=E_a$。因此 $H\mapsto U^\dagger HU$ 和 $H\mapsto (UW)^\dagger H(UW)$ 在 $\{E,E_a,E_b\}$ 上分别作用为

$$
\begin{array}{c|ccc}
H&E&E_a&E_b\\\hline
U^\dagger HU&E_a&E&E_b\\
(UW)^\dagger H(UW)&E_b&E&E_a
\end{array}.
\tag{40.14}
$$

任意更长 $M_h$ 仍为这三个投影之一；实际分支对偶只再乘 $1/2$。$I_3,E,M_0,M_1$ 在第一层已包含 $I_3,E,E_a,E_b$。直接相加得

$$
E+E_a+E_b=\frac34I_3+\frac38C.
\tag{40.15}
$$

$I_3,E,C,E_a$ 独立：在 (40.5) 基中，$E_a$ 的 $02$ 条目为 $\sqrt3/4\ne0$，其他三者的该条目为零；去掉 $E_a$ 后，$E$ 的 $01$ 条目为 $1/2$，其他两者为零；$I_3$ 和 $C=\operatorname{diag}(2,0,0)$ 又独立。故空间维数为四且不再增长。第零层只有独立的 $I_3,E$，所以第一层确是达到层。结合非零行列式部分，例外集合恰为所述周期集合。∎

**定理 40.2（例外角度的完整复消去子）。** 在 $\theta\in(\pi/2)\mathbb Z$ 时，$\mathcal V_\theta^\perp$ 在基 $(a,h_{\rm out},g)$ 中恰为

$$
H(Y,w_0,v_0,m_0,n_0)=
\begin{pmatrix}
0&-Y/2+\mathrm i v_0&(-3w_0+\mathrm i m_0)/\sqrt6\\
-Y/2-\mathrm i v_0&Y&(w_0+\mathrm i n_0)/\sqrt6\\
(-3w_0-\mathrm i m_0)/\sqrt6&(w_0-\mathrm i n_0)/\sqrt6&-Y
\end{pmatrix},
\qquad (Y,w_0,v_0,m_0,n_0)\in\mathbb R^5.
\tag{40.16}
$$

其真实维数为五，包含三个独立的虚相干方向。非例外角度的消去子为 $\{0\}$。

证明。定理 40.1 把条件化为 $\operatorname{Tr}H=\operatorname{Tr}(EH)=\operatorname{Tr}(CH)=a^\dagger Ha=0$。最后一式给 $H_{aa}=0$，迹条件给 $H_{gg}=-H_{hh}$，而 $C=(a+h_{\rm out})(a+h_{\rm out})^\dagger$ 给 $\Re H_{ah}=-H_{hh}/2$。在此基中

$$
q=\tfrac14a+\tfrac34h_{\rm out}+\tfrac{\sqrt6}{4}g.
\tag{40.17}
$$

将前三个等式代入 $q^\dagger Hq=0$，余下的实约束恰为 $\Re H_{ag}+3\Re H_{hg}=0$。取 $Y=H_{hh}$、$w_0=\sqrt6\Re H_{hg}$ 及三个任意虚部即得 (40.16)，反向代回四个配对均为零。五个参数逐项可从矩阵恢复，故独立且穷尽。非例外情形由全部 Hermitian 空间的迹配对非退化性得到。∎

## 41. 任意复相容后继的有限精确重建

**定理 41.1（一般角度的成对辨识与 Gram 反演）。** 固定 $\sin(2\theta)\ne0$，并保持假设 39.2。对任意 $\rho,\sigma\in\mathcal K_d$，(40.2) 八个词的是响应相等，当且仅当 $\rho=\sigma$，亦当且仅当 $S_\rho=S_\sigma$。它们还等价于全部有限词、两种终端结果的响应相等。

明确地，按 (40.2) 顺序记 $h_1,\ldots,h_8$，置

$$
F_0=I_3,\qquad F_i=M_{h_i}\quad(1\le i\le8),\qquad
G_{ij}=\operatorname{Tr}(F_iF_j)\quad(0\le i,j\le8).
\tag{41.1}
$$

从实际精确响应 $D_{h_i,1}(\rho)$ 定义实数

$$
b_0=1,\qquad b_i=2^{|h_i|}f^\dagger D_{h_i,1}(\rho)f.
\tag{41.2}
$$

则 $G$ 正定，且

$$
\rho=\sum_{i,j=0}^8F_i(G^{-1})_{ij}b_j.
\tag{41.3}
$$

把此 $\rho$ 代入 (39.2) 即恢复整个复线性后继通道及其所有有限参考放大。

证明。定理 40.1 使 $F_0,\ldots,F_8$ 成为 Hermitian 空间的一组实基。对任意非零 $x\in\mathbb R^9$，

$$
x^{\mathsf T}Gx
=\operatorname{Tr}\left(\left(\sum_i x_iF_i\right)^2\right)>0,
$$

故 $G$ 可逆。由于 $P_+f=0$，(39.7) 给 $b_i=\operatorname{Tr}(\rho F_i)$。若 $\rho=\sum_i\lambda_iF_i$，则 $b=G\lambda$，得到 (41.3)。这里 $2^{|h_i|}$ 只用于已给定实数数据的线性代数运算；实际联合效果始终为 $Z_{h_i}$，没有实施选支或物理条件化。

同一公式表明八个是响应相等便给同一 $\rho$。而 (39.2) 给 $S_\rho(ff^\dagger)=B\rho B^\dagger$，所以 $S_\rho=S_\sigma$ 也迫使 $\rho=\sigma$。剩余等价由定理 39.4 得到。

复域与参考的量词可直接展开：对任意 $X\in M_k\otimes M_3$，定义

$$
X_{ff}=(I_k\otimes f^\dagger)X(I_k\otimes f).
$$

则

$$
\begin{aligned}
(\operatorname{id}_{M_k}\otimes S_\rho)(X)
={}&(I_k\otimes BUP_+)X(I_k\otimes P_+U^\dagger B^\dagger)\\
&+X_{ff}\otimes B\rho B^\dagger.
\end{aligned}
\tag{41.4}
$$

不要求 $X$ 为实、纯态或无参考输入。这正是第一卷定理 35.2 的忠实后继接口，而非把理想通道的刚性定理用于两个任意非理想通道。∎

**定义 41.2（重建对象和精确性的范围）。** (41.3) 的对象是原域提升 $T$ 的共同后继 $S_\rho=\mathcal GT$。响应 (39.6) 通过 $T\mapsto\mathcal GT$ 因子化；它没有提供恢复此前 $T$ 的结论。若只给某个固定输入的概率，则 (41.2) 所需响应未必由该输入合同给定；只有在原合同实际供应这些精确响应或所需精确概率时，(41.3) 才是数据反演。

取 $F_i$ 的 Gram 逆是数学反演，不是可调用的量子逆通道。式 (40.4) 在例外角度趋零；这里的逐角度精确可辨识性没有统一噪声界、统计稳定性或有限样本精度保证。独立重复制备、共同来源、输入选择和概率取得的权限均保留假设 39.2 的范围。

## 42. 例外角度的完整残留纤维与原域双世界

**定理 42.1（新增数据恰为一个人口及其全部纤维）。** 固定 $\theta=k\pi/2$，令 $j_*=k\bmod2\in\{0,1\}$。对任意 $\rho,\sigma\in\mathcal K_d$，

$$
D_{h,y}(\rho)=D_{h,y}(\sigma)\quad\text{对全部 }h,y
\quad\Longleftrightarrow\quad \rho_{aa}=\sigma_{aa}.
\tag{42.1}
$$

取实际相容的值 $\rho_{aa}=d+s$。相应全部后继态在基 $(a,h_{\rm out},g)$ 中恰为

$$
\rho(s;y,w,v,m,n)=
\begin{pmatrix}
d+s&-(s+y)/2+\mathrm i v&(4s-3w+\mathrm i m)/\sqrt6\\
-(s+y)/2-\mathrm i v&y&(w+\mathrm i n)/\sqrt6\\
(4s-3w-\mathrm i m)/\sqrt6&(w-\mathrm i n)/\sqrt6&1-d-s-y
\end{pmatrix},
\tag{42.2}
$$

其中 $y,w,v,m,n\in\mathbb R$，且必须同时满足

$$
\rho\succeq0,\qquad s\ge0,\qquad
v^2+\frac{[y+(1+2\tau)s]^2}{4}\le d(y-\tau^2s).
\tag{42.3}
$$

每个满足这些条件的矩阵都有原域提升。五参数表示不表示每个边界截面都具有统一的五维相对内部。

对直接输入仪器的后继 qutrit 态 $\rho$，两条单步联合是概率按实际标签 $j_*,1-j_*$ 排序为

$$
\bigl(\operatorname{Tr}(\rho Z_{j_*}),
       \operatorname{Tr}(\rho Z_{1-j_*})\bigr)
=\left(\frac{d+s}{2},\frac{e_d-s}{2}\right).
\tag{42.4}
$$

这也正是先经过 $S_\rho$、原输入为 $ff^\dagger$ 时的两条联合是概率。

证明。$\mathcal K_d$ 中所有态已有相同的 $I_3,E,C$ 期望 $1,e_d,d$。定理 40.1、39.4 因而把所有新数据相等恰化为 $aa^\dagger$ 的期望相等，证明 (42.1)。固定 $s$ 后，第一卷定理 35.6 的六实参数式 (35.9) 恰给 (42.2)–(42.3)，其中的正性不可省去。反向，第一卷定理 35.4 的全域提升使每个这些态对应真实原通道，故并未额外扩大或缩小纤维。

又 $k+j_*$ 为偶数，故 $V_{j_*}$ 为 $U$ 的标量相位倍数，$M_{j_*}=E_a$，另一效果为 $E_b$。由 (40.15)，

$$
\operatorname{Tr}(\rho E)=e_d,\qquad
\operatorname{Tr}(\rho E_a)=d+s,\qquad
\operatorname{Tr}(\rho E_b)
=\frac34+\frac38d-e_d-d-s=e_d-s.
\tag{42.5}
$$

最后一个等号使用 $e_d=(6-5d)/16$。乘原始 $1/2$ 得 (42.4)。非负性随这些实际投影和 $\rho\succeq0$ 保留。表 (40.14) 还表明更深每个联合是概率，只是 $e_d,d+s,e_d-s$ 三者之一乘以 $2^{-|h|}$；没有其他自由响应。∎

**定理 42.2（既有效果 $Q_a$ 的原响应对应）。** 取第一卷定理 37.5 已有的效果

$$
P_a=Baa^\dagger B^\dagger,\qquad Q_a=\mathcal G^\dagger(P_a).
\tag{42.6}
$$

对每个原域提升 $T\in\mathcal F_t$，若 $\mathcal GT=S_\rho$，则在 $\theta=k\pi/2$ 时有

$$
2D_{j_*,1}(\rho)
=E+\rho_{aa}ff^\dagger
=T^\dagger(Q_a).
\tag{42.7}
$$

因此例外角度的原生联合数据提供与 $Q_a$ 相同的这一响应信息；它不是把 $Q_a$ 当成新构造，也不是物理选支。

证明。$M_{j_*}=aa^\dagger$ 且 $U^\dagger a=q\in\operatorname{ran}P_+$，由 (39.7) 立得第一等式。另一方面

$$
T^\dagger(Q_a)
=(\mathcal GT)^\dagger(P_a)=S_\rho^\dagger(P_a)
=E+\rho_{aa}ff^\dagger,
$$

这是既有定理 37.5 的对应。两端均为完整原输入响应。乘二是由联合概率表恢复该响应的代数关系；实际执行仍保留两种标签和两种终端结果及各自权重。特别地，若这个响应值为 $E+dff^\dagger$，原有的 $\mathcal K_d^0$ 切口恰被取得；一般测得 $s$ 时则是定理 42.1 的固定 $s$ 纤维。∎

**定理 42.3（每个 $0<d<1$ 的真实原域不可辨双世界）。** 对每个 $0<d<1$，第一卷定义 29.1 的既有相位符号通道 $T_{t,+},T_{t,-}$，$t=\sqrt d$，属于同一个 $\mathcal F_t$，且在每个例外角度具有完全相同的全部扩大数据，但后继不同，并满足

$$
\|\mathcal GT_{t,+}-\mathcal GT_{t,-}\|_\diamond
=4\sqrt{d(1-d)}>0.
\tag{42.8}
$$

范数为第一卷定义 18.1、(29.2) 的不除以二的完整 diamond 范数。

证明。明确对应既有通道的参数，取第一卷 (29.1) 的

$$
\begin{gathered}
c_H=(e_0+e_1-e_3-e_4)/2,\qquad p=Bq,\\
w_\pm=\sqrt{1-d}\,c_H\pm\mathrm i\sqrt d\,p,\\
T_{t,\pm}(X)=BP_+XP_+B^\dagger+(f^\dagger Xf)w_\pm w_\pm^\dagger.
\end{gathered}
\tag{42.9}
$$

第一卷定理 29.2 已证明它们是原域 CPTP、具有全部原深度的相同完整算子数据，并给出 (42.8)。在 (39.2) 接口中，它们对应

$$
\rho_\pm=v_\pm v_\pm^\dagger,\qquad
v_\pm=\sqrt{1-d}\,g\pm\mathrm i\sqrt d\,a.
\tag{42.10}
$$

二者的 $aa$ 人口均为 $d$，故定理 42.1 使所有有限扩大数据相等。这一应用同时保留相同原输入域及所有历史，没有把任意 Hermitian 消去方向当成可行通道。

为核对非零差及参考范围，$\rho_+-\rho_-$ 在 $(g,a)$ 上的非零块为

$$
\begin{pmatrix}
0&-2\mathrm i\sqrt{d(1-d)}\\
2\mathrm i\sqrt{d(1-d)}&0
\end{pmatrix}.
$$

其迹范数为 $4\sqrt{d(1-d)}$；第一卷 (29.8)–(29.9)、定理 35.5 的差映射压缩等式把此值接到任意复输入、任意有限参考的 diamond 范数。这里复用的是已供应的相位符号见证与范数等式。∎

**定理 42.4（严格固定人口纤维中的五个实际自由度）。** 对每个 $0<d<1$，令

$$
\varepsilon=\frac{d(1-d)}{100},\qquad
s=\varepsilon,\qquad y=\varepsilon,\qquad w=v=m=n=0.
\tag{42.11}
$$

则 (42.2) 的矩阵严格正，(42.3) 的最后不等式严格成立。在固定 $s=\varepsilon$ 下，$(y,w,v,m,n)$ 的一个非空开邻域全部满足完整相容条件。因此存在五实维的实际相容后继家族，它们具有相同的全部扩大数据和相同的 $Q_a$ 响应。这一结论同时包含实与虚相干不确定性。

证明。此矩阵为

$$
\rho_\varepsilon=
\begin{pmatrix}
d+\varepsilon&-\varepsilon&4\varepsilon/\sqrt6\\
-\varepsilon&\varepsilon&0\\
4\varepsilon/\sqrt6&0&\beta-2\varepsilon
\end{pmatrix}.
\tag{42.12}
$$

由于 $\varepsilon>0$ 且 $\beta-2\varepsilon\ge(49/50)\beta>0$，对后两个对角条目取 Schur 补，严格正性等价于

$$
d-\frac{8\varepsilon^2}{3(\beta-2\varepsilon)}>0.
$$

其被减项有明确上界

$$
\frac{8\varepsilon^2}{3(\beta-2\varepsilon)}
\le\frac{d^2\beta}{3675}<d.
\tag{42.13}
$$

另一方面，(42.3) 的左右两边分别为 $(1+\tau)^2\varepsilon^2$ 和 $d\varepsilon(1-\tau^2)$，故严格不等式等价于

$$
\frac{\varepsilon}{d}<\frac{1-\tau}{1+\tau}=\frac1{\sqrt2}.
$$

左边为 $\beta/100<1/100$，于是成立。正定锥和严格标量不等式均为开条件；在固定 $s$ 的仿射参数空间内，小邻域仍满足它们。五个剩余参数分别可由 $hh$ 条目、$hg$ 实部及三个虚部恢复，仿射映射因而单射，邻域维数确为五。定理 35.4 供应每一点的原域提升，定理 42.1 使这些后继的数据相同。

这里的实际五维邻域位于一个明确的严格截面。若固定 $s$ 位于其他可行边界，正性或 $B_d$ 约束可以压低维数；上述结论没有给这些边界截面统一维数。∎

## 43. 数学来源、取得前提与结论域

**定义 43.1（供应结果与源特定综合的归属）。** §§39–42 是 `repo-derived` 的源特定综合与应用：承重关系是固定实际仪器的全角度有限轨道 (40.4)、任意非理想复 $\mathcal K_d$ 上的成对辨识和反演，以及例外角度的完整固定人口纤维。一般观察空间判据、有限闭包、理想通道刚性与稳定性、$Q_a$ 效果和相位符号双世界均为中间供应，不主张其为本卷新构造，也不主张全域文献原创性。

供应对象的精确对应为：

- [第一卷](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md) §17.1、定义 29.1、定理 29.2 给实际物理仪器、完整相位符号双世界和其 diamond 差；定理 35.2、35.4、35.6 给全复后继接口、穷尽原域提升及六实参数条件；定理 35.5 给完整参考的差范数等式；定理 37.5 给 $Q_a$ 及其条件切口。
- [尖锐任务与保留环境记忆](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md) 定义 1.1–1.2、§11、定理 5.2、13.1 给相同标签约定、完整联合任务及理想 $\operatorname{Ad}_B$ 的刚性；§17、定理 18.1、19.1 与[续卷](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY_II.md) §20 给其声明域的理想通道稳定性和指定制备接口。那些理想目标结论不代替两个任意非理想 $S_\rho,S_\sigma$ 的成对分析。
- [量子原则与相干重建](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md) §11、§19、应用 28.2 给未来效果闭包、完整前缀质量及原生环境读口的资源区分。定理 39.4 已逐项映射其载体、分支、词域和初始效果族。
- [延续效果闭包的数学声明](../../../D5/S3/Quantum/Measurement/ContinuationEffectClosure.lean)及其[对应叙述](../../../Blueprint/D5/S3/Quantum/Measurement/ContinuationEffectClosure.md)定理 1.3 给有限分支对偶的最小不变闭包；本卷使用 $d_{\rm matrix}=3$、初始维数二、单 Kraus 分支 $V_j/\sqrt2$。本卷的达到深度三或一由具体矩阵决定。

一般可观察性观点的文献先例为 D. D’Alessandro，[*On Quantum State Observability and Measurement*, arXiv:quant-ph/0307127v1](https://arxiv.org/html/quant-ph/0307127v1)，定理 1–2 和 §4，DOI [10.1088/0305-4470/36/37/310](https://doi.org/10.1088/0305-4470/36/37/310)。该文以可选 Lie 群酉控制和期望读出研究轨道张成、不可区分态及初态确定，是 `literature-attested` 的一般中间观点。其可选控制不提供这里的原生固定随机分支菜单；这里的 $2^{-|h|}$ 完整记录、全角度例外集合及 $\mathcal K_d$ 原域桥由上述源特定推导承担。该文 §4 对可辨识性与实际初态取得的区分，也不授予本卷额外制备或读出权限。

**定义 43.2（辨识与取得的逻辑边界）。** 假设 39.2 中实际提供的关系由三部分共同指定：保留真实分支标签；在所需的指定有限终点重复同一固定已知角度仪器；提供原二元终端任务的精确算子响应或合同所需的精确联合概率。定理 41.1 以这些条件推出非例外角度的后继辨识；定理 42.1–42.4 给例外角度的全部残留分类。

历史的一次实际出现不等于可选择它发生；数学地选取联合概率表的某一坐标不等于丢弃其他历史。所有实概率均保持原始联合权重，所有复输入及未触动参考的通道结论均通过 (39.2)、(41.4) 承担。不由这些数学关系增添新标定、选支、门、逆、环境基、环境访问、相位参考、时钟、独立副本、准备或系综资源。

逐角度精确可辨识性与有限精度取得性是不同命题；本卷不给后者的统一噪声或统计稳定界。原擦除标签菜单的完整精确最小最大问题仍是第一卷定义 38.3 的 (38.6)，其最优中心和匹配下证书不由本卷的扩大菜单分类给出。复 Hilbert、CPTP 与 Born 配对在本卷处于前提侧，关于这些量子结构从更基础关系产生的命题也不由本卷条件定理推出。

## 追加锚（本行以下为增补区）
