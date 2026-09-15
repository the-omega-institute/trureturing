# 情境时空算术的量子扩展

## 1. 载体、状态与算术桥接

**定义 1.1（有限量子载体及记号分层）。** 沿用[《情境时空算术》（CSA）定义 1–6、20、22](CONTEXTUAL_SPACETIME_ARITHMETIC.md)的情境、丰富表示、平衡域及运算，以及[《情境时空算术的 Zeckendorf 扩展》（Z 卷）定义 1–4、9、11](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的数位观察。特别地，$X=(C,A)$、$A\subseteq\Omega\subseteq E$，且选择不必向下闭；来源树记为$\rho$，密度矩阵另记$\varrho$。固定
$$
G_0=1,\quad G_1=2,\quad G_{j+2}=G_{j+1}+G_j,\qquad
\lambda(p,j)=(p,j,0).
$$
对每个整数$L\ge0$，只使用有限开放窗口
$$
\mathcal W_L=\{(c_0,\ldots,c_{L-1})\in\{0,1\}^L:
c_jc_{j+1}=0\text{ 当 }0\le j< L-1\},\qquad
V(c)=\sum_{j=0}^{L-1}G_jc_j.
$$
所有字串均按低位到高位书写，第一位是第零位；不把两端相接。$\mathcal W_0$只有空字串；空和为零，空积为一。记$\widehat c:\mathbb N\to\mathbb N$为$c$在$j\ge L$补零的行，$s(a)$为自然数$a$的有限支撑规范行，$\mathcal R=\mathbb N^{(\operatorname{Pr}\times\mathbb N)}$。原始表与规范表的映射仍为
$$
V_p(r)=\sum_jG_jr(p,j),\quad D(r)=\prod_p p^{V_p(r)},\quad
\nu(r)(p,\cdot)=s(V_p(r)),\quad K(n)(p,\cdot)=s(v_p(n)).
$$
$K(n)$以素数和数位的二元组为索引，$s(n)$只以数位为索引。原CSA未加权读数为$q(X)=\sum_{e\in A}\sigma(e)$；Z 卷的累积观察使用整数阈值$T$：
$$
r_X^T(p,j)=\sum_{t\le T}Z_X(t,\lambda(p,j)),\qquad
N_X(T)=D(r_X^T).
$$
总表$r_X=\sum_t Z_X(t,\lambda(\cdot,\cdot))$、总读数$N_X=D(r_X)$及总估值$a_p^X=V_p(r_X)$区别于指定$T$的累积量。

固定素数$p$和窗口$L$，定义丰富表示到配置的观察
$$
\begin{aligned}
\mathcal X_{p,L}=\{X\in\mathcal B_\lambda^+:\;&r_X(p,j)=0\ (j\ge L),\quad
r_X(p',j)=0\ (p'\ne p),\\
&(r_X(p,0),\ldots,r_X(p,L-1))\in\mathcal W_L\},\\
\pi_{p,L}:\mathcal X_{p,L}\longrightarrow\mathcal W_L,\qquad
&\pi_{p,L}(X)=(r_X(p,0),\ldots,r_X(p,L-1)).
\end{aligned}
$$
这是在原选择空间中取一个观察子域；同一配置可有不同的丰富表示。

对非空有限集合$S$，令$\mathcal H_S=\mathbb C^S$，标准正交基为$\{|s\rangle:s\in S\}$，并规定
$$
\langle v,w\rangle=\sum_{s\in S}\overline{v_s}w_s.
$$
内积对第一变量共轭线性，对第二变量线性；$A^\dagger$表示共轭转置，$\|A\|$为算子范数，$[A,B]=AB-BA$。令$\mathcal H_L=\mathcal H_{\mathcal W_L}$，包括$\mathcal H_0\cong\mathbb C$。量子演化参数为$\tau\in\mathbb R$，与原CSA档案时刻$t(e)\in\mathbb Z$及累积阈值$T\in\mathbb Z$分别取型，不指定它们之间的等同关系。

**假设 1.2（额外量子规则）。** 在每个所选有限Hilbert空间上，态为$\varrho\ge0$、$\operatorname{tr}\varrho=1$；单位向量$\psi$对应纯态$|\psi\rangle\langle\psi|$。效应为$0\le M\le I$，其概率规定为$\operatorname{tr}(\varrho M)$。有限测量$(M_a)_a$满足$\sum_aM_a=I$。独立制备的两个系统使用张量积态；一般联合态允许不是乘积态。

允许的有限记录操作由同一输入、输出空间之间的一族矩阵$(K_a)_a$给定，其中$\sum_aK_a^\dagger K_a=I$：记录结果$a$的未归一化输出为$K_a\varrho K_a^\dagger$，丢弃结果后的输出为各项之和。对有限系统与环境，部分迹的坐标约定为
$$
(\operatorname{tr}_{\mathcal E}R)_{xy}
=\sum_a R_{(x,a),(y,a)},
$$
其中$(|a\rangle)_a$是环境的正交基。封闭、时间无关的动力学由自伴Hamiltonian及常数$\hbar>0$指定；$\hbar$有能量乘时间量纲，$\tau$有时间量纲。这些是额外模型假设，不是整数读数或来源树的推论。振幅及Hamiltonian的标准解释参见 R. P. Feynman、R. B. Leighton、M. Sands，*The Feynman Lectures on Physics*, Vol. III，[第 3 章 Probability Amplitudes](https://www.feynmanlectures.caltech.edu/III_03.html)及[第 8 章 The Hamiltonian Matrix](https://www.feynmanlectures.caltech.edu/III_08.html)。

**定理 1.3（完整窗口的酉重标记与算术算符）。** 对每个$L\ge0$，映射
$$
J_L:\mathcal H_L\longrightarrow\mathbb C^{\{0,\ldots,G_L-1\}},\qquad
J_L|c\rangle=|V(c)\rangle
$$
为酉映射。因此$\dim\mathcal H_L=G_L=F_{L+2}$，其中$F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$。对$c\in\mathcal W_L$，规范行与窗口串的精确关系为
$$
\widehat c=s(V(c)),\qquad s(V(c))|_{\{0,\ldots,L-1\}}=c.
$$
定义
$$
n_j|c\rangle=c_j|c\rangle\quad(0\le j<L),\qquad
V_Z=\sum_{j=0}^{L-1}G_jn_j.
$$
则$V_Z$自伴，且谱恰为$\{0,\ldots,G_L-1\}$，每个本征值的重数为一。

证明。 直接使用[Z 卷定理 10](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)：$c\mapsto V(c)$是所列有限集合之间的双射，且补零后的规范行唯一。因此$J_L$把一组完整正交基双射到另一组完整正交基，保持内积并满射；规范行等式及其截取式也由该唯一性得到。每个$n_j$是实对角投影，而$V_Z|c\rangle=V(c)|c\rangle$；谱和重数由同一双射立即得到。$L=0$时唯一字串为空，$V_Z=0$，结论仍成立。整数谱只作算术可观测量标签，不赋予能量或物理距离的解释。相同的相邻占据排除条件见 [ForbiddenNeighbourDeterminant 的 adm_iff_no_adjacent_true](../../../D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.lean)；该处 forbidden_neighbour_determinant 在奇数长度及非负权重条件下还给出加权构型、Gram 行列式及量子读数关系。证毕。

**定理 1.4（原CSA载体上的逐构型实现）。** 固定素数$p$、$L\ge0$及整数$T_0$。存在同一情境中的丰富表示族$X_c$，$c\in\mathcal W_L$，满足逐单元背景电荷为零、$\pi_{p,L}(X_c)=c$，并且
$$
r_{X_c}(p,j)=\widehat c_j,\qquad r_{X_c}(p',j)=0\ (p'\ne p),
$$
$$
q(X_c)=\sum_{j<L}c_j,\qquad a_p^{X_c}=V(c),\qquad N_{X_c}=p^{V(c)}.
$$
对整数$T<T_0$，$N_{X_c}(T)=1$；对$T\ge T_0$，$N_{X_c}(T)=p^{V(c)}$。特别地，$\pi_{p,L}$满射，且
$$
K(N_{X_c})(p,\cdot)=\widehat c=s(V(c)),\qquad
K(N_{X_c})(p',\cdot)=0\quad(p'\ne p).
$$

证明。 使用[Z 卷定理 13](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的同槽正负对平衡实现。在固定时刻$T_0$，为每个$j<L$保留其中的一对互异HF事件出现$e_j^+,e_j^-$，位置同为$\lambda(p,j)$、符号分别为$+1,-1$，来源取$\operatorname{leaf}(j)$。共同情境取这些事件组成的$E=\Omega$及空偏序，令$A_c=\{e_j^+:c_j=1\}$。保留未选对使所有$c$共用同一情境；Z13 的逐单元背景抵消仍成立。选择净电荷在时刻$T_0$的第$j$槽为$c_j$，其他单元为零。代入[Z 卷定义 4、定理 5](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)即得未加权$q$、估值及累积读数；第1.3条和 Z 卷定义 11 给出$K$的逐行等式。$L=0$时取空档案，所有读数按空和、空积约定成立。这个实现只选取原CSA允许选择空间中的一个子族；$\lambda(p,j)$仍是原坐标嵌入，不是实验室原子距离。证毕。

**定理 1.5（多素数复合及$K$的正确类型）。** 固定有限且互异的素数集合$P$，并为每个$p\in P$给定$L_p\ge0$。令
$$
\mathcal N_{P,L}=\{n\in\mathbb N_+:v_{p'}(n)=0\text{ 对 }p'\in\operatorname{Pr}\setminus P,\quad v_p(n)<G_{L_p}\text{ 对 }p\in P\}.
$$
则
$$
(c^{(p)})_{p\in P}\longmapsto n=\prod_{p\in P}p^{V(c^{(p)})}
$$
为$\prod_{p\in P}\mathcal W_{L_p}$到$\mathcal N_{P,L}$的双射，并诱导
$$
\bigotimes_{p\in P}\mathcal H_{L_p}\cong\mathbb C^{\mathcal N_{P,L}}.
$$
在此对应下，对$p\in P$，$K(n)(p,\cdot)=\widehat{c^{(p)}}$是补零后的行，$K(n)(p,\cdot)|_{\{0,\ldots,L_p-1\}}=c^{(p)}$是其窗口截取；$p\notin P$的行全零。这是素数估值表，区别于整数本身的单行$s(n)$。

证明。 素因数分解唯一性把$n$唯一分解为指数族$(v_p(n))_{p\in P}$，[Z 卷定理 10](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)又把每个指数唯一分解为相应窗口字串，得到互逆映射。乘积基与张量积基均按这些字串族索引，故诱导映射酉。Z 卷定义 11 给$K(n)(p,\cdot)=s(v_p(n))$，由第1.3条恰为$\widehat{c^{(p)}}$。将第1.4条各素数的实现作原$\boxplus$，Z 卷定理 6 使原始表相加、整数读数相乘，提供同一结论的CSA实现。若$P$为空，两端都只有一个基态，对应$n=1$。这里的张量复合是独立系统的量子复合；它没有把原档案乘法$\boxtimes$改定义为张量积。证毕。

**定理 1.6（构型分布不能决定相位）。** 两个密度矩阵$\varrho,\sigma$对所有构型对角Hermitian算符给出相同期望，当且仅当
$$
\langle c|\varrho|c\rangle=\langle c|\sigma|c\rangle\qquad(c\in\mathcal W_L).
$$
两个单位向量有同一构型分布，当且仅当其每个非零坐标分别相差一个模为一的因子；这些因子不必相同。

证明。 必要性取对角投影$P_c=|c\rangle\langle c|$。充分性把任意实对角算符写为$\sum_ca_cP_c$，用迹的线性性。纯态的对角元为$|\psi_c|^2$，故相同分布等价于$|\psi_c|=|\phi_c|$；在非零坐标处取$\phi_c/\psi_c$，其模为一，零坐标处两者均为零。对$L=2$，
$$
|B\rangle=(|10\rangle+|01\rangle)/\sqrt2,\qquad
|D\rangle=(|10\rangle-|01\rangle)/\sqrt2
$$
分布同为$(0,1/2,1/2)$，但两向量正交，不可能仅差全局相位。因此构型分布及由其得到的$V_Z$分布均不能决定量子态。证毕。

## 2. 开放阻塞链与有限演化

**定理 2.1（连接边界与前缀正交分解）。** 对$M,N\ge1$，$\mathcal H_{M+N}$自然等同于$\mathcal H_M\otimes\mathcal H_N$中下列投影的像：
$$
Q_{M,N}=I-n_{M-1}\otimes n_0.
$$
若一段长度为零，则使用恒等投影。这里以串接的配置基给出酉识别；$M,N\ge1$时该像是张量积中的真子空间。另对$L\ge2$，定义
$$
J_0|w\rangle=|0w\rangle,\qquad J_{10}|w\rangle=|10w\rangle.
$$
则
$$
\mathcal H_L=J_0\mathcal H_{L-1}\ \mathbin{\oplus^\perp}\ J_{10}\mathcal H_{L-2}.
$$
这个正交直和本身不声明任何动力学不变性。

证明。 两段内部已经满足no11；串接后唯一新增限制是左段最高位与右段最低位不得同时为一。$n_{M-1}\otimes n_0$恰投影到违反此限制的乘积基态，故其补投影的像正是允许串接字串。两段各自在相接端点取一个单激发时，该乘积基态被排除，故像为真子空间；例如$\dim\mathcal H_2=3<4=\dim(\mathcal H_1\otimes\mathcal H_1)$。按占据基可把$\mathcal H_L$等距嵌入$(\mathbb C^2)^{\otimes L}$，但约束空间本身没有因此成为$L$个独立二维因子的张量积。对前缀分解，首位为零时余串任意属于$\mathcal W_{L-1}$；首位为一时第二位必须为零，余串任意属于$\mathcal W_{L-2}$。两类不交并覆盖全部基态，所以对应嵌入等距、像互相正交且合起来满射。动力学是否保持各像还须检查Hamiltonian的非对角块，第2.5条给出该检查。证毕。

**假设 2.2（理想近邻硬阻塞Hamiltonian）。** 在$\mathcal H_L$上，对$0\le j<L$定义受限升算符$T_j$：若$c_j=0$且所有存在的近邻位都为零，则$T_j|c\rangle=|c+e_j\rangle$；否则取零。这里$e_j$为长度$L$的第$j$个单位字串，加法逐位进行；端点外的不存在位置按零占据处理。固定与$\tau$无关的$h_j\in\mathbb C$、$d_j\in\mathbb R$，规定
$$
H_L=\sum_{j<L}(h_jT_j+\overline{h_j}T_j^\dagger)+\sum_{j<L}d_jn_j.
$$
这里$h_j,d_j$有能量量纲；若使用实Rabi角频率$\Omega_j$、实失谐角频率$\Delta_j$及实相位$\phi_j$，可采用$h_j=\hbar\Omega_je^{i\phi_j}/2$、$d_j=-\hbar\Delta_j$。相位为零时的系数约定见 H. Bernien 等，*Probing many-body dynamics on a 51-atom quantum simulator*, Nature **551**, 579–584 (2017)，[式 (1)，DOI: 10.1038/nature24622](https://doi.org/10.1038/nature24622)；其 Methods 的 “Dynamics after sudden quench” 以端点外基态投影为恒等规定开放链。局部投影翻转结构见 C. J. Turner、A. A. Michailidis、D. A. Abanin、M. Serbyn、Z. Papić，*Weak ergodicity breaking from quantum many-body scars*, Nature Physics **14**, 745–749 (2018)，[DOI: 10.1038/s41567-018-0137-5](https://doi.org/10.1038/s41567-018-0137-5)，及其预印本 *Quantum many-body scars*，[arXiv:1711.03528v2，式 (1)](https://arxiv.org/abs/1711.03528v2)。这里的边界采用定义1.1的开放窗口。

本条假定精确排除相邻激发，并忽略未写入的远程相互作用和耗散；再令所有$d_j=0$才得到纯投影翻转模型。有限阻塞强度下的误差界不属于这些假设。所有关于本$H_L$的结论均以这个固定理想模型为条件。$H_0=0$；在$(|0\rangle,|1\rangle)$基底中，$H_1=\begin{pmatrix}0&\overline{h_0}\\h_0&d_0\end{pmatrix}$。

**定理 2.3（自伴性、酉演化与概率归一化）。** 假设 2.2的$H_L$自伴。对每个$\tau\in\mathbb R$，
$$
U_L(\tau)=\exp(-i\tau H_L/\hbar)
$$
为酉算符，对任意$\tau,\eta\in\mathbb R$满足$U_L(\tau+\eta)=U_L(\tau)U_L(\eta)$，并有$i\hbar U_L'(\tau)=H_LU_L(\tau)$。演化$\varrho(\tau)=U_L(\tau)\varrho U_L(\tau)^\dagger$保持密度矩阵条件；任意假设 1.2中的有限测量给出非负且总和为一的概率。

证明。 每个$h_jT_j+\overline{h_j}T_j^\dagger$等于其伴随，$d_jn_j$亦然，故$H_L^\dagger=H_L$。矩阵指数级数在算子范数下由$\sum_n(|\tau|\|H_L\|/\hbar)^n/n!$控制而绝对收敛；在紧$\tau$区间上导数级数也一致收敛。因此可逐项取伴随和求导，并可用绝对收敛的Cauchy乘积得到群律。于是$U_L(\tau)^\dagger=U_L(-\tau)$，两者相乘为$I$。

对任意向量$v$，$\langle v,\varrho(\tau)v\rangle=\langle U_L(\tau)^\dagger v,\varrho U_L(\tau)^\dagger v\rangle\ge0$；迹由循环性保持为一。将$\varrho(\tau)$作有限谱分解$\sum_k\lambda_k|v_k\rangle\langle v_k|$，有$\operatorname{tr}(\varrho(\tau)M_a)=\sum_k\lambda_k\langle v_k,M_av_k\rangle\ge0$，对$a$求和则为$\operatorname{tr}\varrho(\tau)=1$。所用无穷级数已有明确绝对收敛控制，不是未证明的无限历史换序。证毕。

**定理 2.4（二位链的亮暗态及相位敏感读数）。** 取$L=2$、$d_0=d_1=0$、$h_0=h_1=g\in\mathbb R$，并按$(00,10,01)$排列基底，则
$$
H=g\begin{pmatrix}0&1&1\\1&0&0\\1&0&0\end{pmatrix},\qquad
H|B\rangle=\sqrt2g|00\rangle,\quad H|D\rangle=0.
$$
这里$g$为实能量系数，$B,D$取第1.6条的精确相位约定；令$\omega=\sqrt2g/\hbar$，并简记$U(\tau)=U_2(\tau)$。若在$\tau=0$的初态分别为$B,D$，则
$$
P_{00}^{B}(\tau)=\sin^2(\omega \tau),\qquad P_{00}^{D}(\tau)=0.
$$
若初态为$00$，则其返回概率为$\cos^2(\omega \tau)$，不是前一个正弦平方。更一般地，对
$$
|\psi_\theta\rangle=(|10\rangle+e^{i\theta}|01\rangle)/\sqrt2
$$
有$P_{00}^{\psi_\theta}(\tau)=\tfrac{1+\cos\theta}{2}\sin^2(\omega \tau)$。

证明。 由受限翻转定义直接得到所列矩阵，并有$H|00\rangle=\sqrt2g|B\rangle$。在$\operatorname{span}\{00,B\}$上，$H=\sqrt2g\begin{pmatrix}0&1\\1&0\end{pmatrix}$，在$D$上为零。指数的偶次、奇次幂分别给余弦、正弦，故
$$
U(\tau)|B\rangle=\cos(\omega \tau)|B\rangle-i\sin(\omega \tau)|00\rangle,\qquad U(\tau)|D\rangle=|D\rangle.
$$
同理$U(\tau)|00\rangle=\cos(\omega \tau)|00\rangle-i\sin(\omega \tau)|B\rangle$。最后，$\psi_\theta$的亮态系数为$(1+e^{i\theta})/2$，其模平方为$(1+\cos\theta)/2$，暗态部分不贡献$00$振幅。各式也涵盖$g=0$。证毕。

**定理 2.5（带边界注入的Hamiltonian递归）。** 对$L\ge2$，在第2.1条前缀分解下，令$J:\mathcal H_{L-2}\to\mathcal H_{L-1}$为$J|w\rangle=|0w\rangle$。使用移位后的尾部参数，恰有
$$
H_L\cong
\begin{pmatrix}
H_{L-1}(h_1,\ldots;d_1,\ldots)&\overline{h_0}J\\
h_0J^\dagger&d_0I+H_{L-2}(h_2,\ldots;d_2,\ldots)
\end{pmatrix}.
$$
首位零、首位一的两个前缀子空间同时为动力学不变子空间，当且仅当$h_0=0$。若$\Pi_0$投影到首位零部分，则
$$
\|[\Pi_0,H_L]\|=|h_0|.
$$
当$h_0\ne0$时，每个非对角块的秩为$G_{L-2}$。

证明。 在$0w$分支，除第零位外的允许翻转及占据能量恰组成第一条尾链。在$10w$分支，第零位贡献$d_0$，第一位被阻塞而固定为零，剩余操作恰组成第二条尾链。两个分支间只有第零位翻转：$00w\mapsto10w$的系数为$h_0$，逆向系数为$\overline{h_0}$，故得到所列块。

$J$等距且定义域维数$G_{L-2}\ge1$。因此非对角块全零等价于$h_0=0$，非零时各秩等于$G_{L-2}$。自伴矩阵保持一个子空间就也保持其正交补；结合指数展开及在$\tau=0$求导，动力学不变等价于相应非对角块为零。交换子为$\begin{pmatrix}0&\overline{h_0}J\\-h_0J^\dagger&0\end{pmatrix}$，其伴随乘自身为$|h_0|^2\operatorname{diag}(JJ^\dagger,I)$，范数即$|h_0|$。证毕。

**定理 2.6（算术标号的演化与非距离性）。** 假设 2.2下，
$$
[V_Z,T_j]=G_jT_j,\qquad
[H_L,V_Z]=\sum_{j<L}G_j(-h_jT_j+\overline{h_j}T_j^\dagger).
$$
对任意演化态，
$$
\frac{d}{d\tau}\operatorname{tr}(\varrho(\tau)V_Z)
=\frac{2}{\hbar}\sum_{j<L}G_j\operatorname{Im}\bigl(h_j\operatorname{tr}(\varrho(\tau)T_j)\bigr).
$$
$V_Z$作为算符对全部时间保持不变，当且仅当所有$h_j=0$。当$L\ge2$时，允许的构型单翻转图有边的算术标号差大于一。

证明。 允许升位使$V(c)$增加恰好$G_j$，不允许升位时交换子两项均为零，故第一式逐基成立。取伴随得到降位交换式，再线性相加即得第二式。由第2.3条，$\varrho'(\tau)=-(i/\hbar)[H_L,\varrho(\tau)]$；迹的循环性给导数为$(i/\hbar)\operatorname{tr}(\varrho(\tau)[H_L,V_Z])$。又$\operatorname{tr}(\varrho T_j^\dagger)=\overline{\operatorname{tr}(\varrho T_j)}$，故得到所列虚部公式。

若全部$h_j=0$，Hamiltonian对角，当然与$V_Z$交换。反之，对全零构型和仅第$j$位为一的构型，$[H_L,V_Z]$的对应矩阵元为$-G_jh_j$；它不能由其他位的项抵消。因此交换子为零迫使每个$h_j=0$。算符守恒与交换子为零的等价由指数展开及零时刻求导得到。最后，第$j$位的单激发与零构型在构型图中距离为一，而标号差为$G_j$，当$j\ge1$时至少为二。所以标号差不是此图距离；其能量解释也不能由窗口双射获得。证毕。

**定理 2.7（较长阻塞的递推改变）。** 固定整数$R\ge1$。对每个整数$L\ge0$，令$\mathcal W_L^{(R)}\subseteq\{0,1\}^L$由满足
$$
c_ic_j=0\qquad(0\le i,j<L,\quad0<|i-j|\le R)
$$
的字串组成，并记$A_L^{(R)}=|\mathcal W_L^{(R)}|$。完整初值为$A_0^{(R)}=1,A_1^{(R)}=2,\ldots,A_R^{(R)}=R+1$；约定辅助值$A_k^{(R)}=1$用于整数$k<0$，不定义负长度字串。则对整数$L\ge1$，
$$
A_L^{(R)}=A_{L-1}^{(R)}+A_{L-R-1}^{(R)}.
$$
对$0\le L\le R+1$，有$A_L^{(R)}=L+1$。作为对全部非负$L$定义的字串族，恰在$R=1$时等于本卷的完整no11窗口族；$R\ge2,L\ge3$时为其真子集。

证明。 首位为零时删除首位，得到任意长度$L-1$的允许字串。首位为一时，后面存在的至多$R$位被迫为零；若还有余串，其长度为$L-R-1$，否则只有一个选择。两类不交，得到递推及所给非正下标约定。当$L-1\le R$时任意两位都不得同时为一，允许字串为全零或任选一个单激发，共$L+1$个。

$R=1$时字串集就是[Z 卷定义 9](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的$\mathcal W_L$。若$R\ge2,L\ge3$，原no11允许的第零、第二位同时为一已被排除，故为真子集。例如$R=2,L=4$的旧权重数值集为$\{0,1,2,3,5,6\}$：唯一允许的双激发为$1001$，数值六；数值四对应的$1010$不再允许。原$V$在子集上仍单射，但完整区间结论不再成立。证毕。

**定理 2.8（有限步传播的路径合成）。** 令$S$为非空有限构型集，$U$为$\mathcal H_S$上的酉算符。对整数$m\ge1$及$a,b\in S$，
$$
(U^m)_{ba}=\sum_{c_1,\ldots,c_{m-1}\in S}\prod_{r=0}^{m-1}U_{c_{r+1},c_r},\qquad c_0=a,\ c_m=b.
$$
$m=0$另定义为恒等传播$U^0=I$，故$(U^0)_{ba}=\delta_{ba}$；$m=1$时中间指标族为空，唯一空指标选择留下因子$U_{ba}$。若初态为$|a\rangle$，终点概率为上述总振幅的模平方，且对$b$求和为一。

证明。 $m=1$就是矩阵元本身。将$U^{m+1}=UU^m$的矩阵元按中间指标展开，再代入归纳式，得到多一层的有限和；所有求和与乘积均有限。概率规则来自假设 1.2，而$\sum_b|(U^m)_{ba}|^2=\|U^m|a\rangle\|^2=1$。这是一种插入完整基底的展开，并没有假定中间基态被测量，也没有为每条路径建立独立的物理记录。若$U=\exp(-i\tau H/\hbar)$，其矩阵元也不必仅在$H$的单翻转边上非零。有限振幅串接参见 Feynman、Leighton、Sands，*The Feynman Lectures on Physics*, Vol. III，[第 3 章 Probability Amplitudes](https://www.feynmanlectures.caltech.edu/III_03.html)；可数路径和及换序仍须另给[Z 卷假设 477.2](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)所要求的绝对收敛或有证明的指定极限条件。证毕。

## 3. 环境记录与规范化的量子边界

**定理 3.1（一般有限记录的Gram实现）。** 给定非空有限指标集$\mathscr H$及矩阵$G\in\mathbb C^{\mathscr H\times\mathscr H}$。存在有限维复环境$\mathcal E$中的单位向量$(e_h)_{h\in\mathscr H}$满足
$$
G_{hk}=\langle e_h,e_k\rangle
$$
当且仅当$G$正半定且$G_{hh}=1$。正半定指$G=G^\dagger$且$z^\dagger Gz\ge0$对每个复列向量$z$成立。实现指定$G$所需的最小环境维数为$\operatorname{rank}G$。按定义1.1的内积方向，复用 [SingletonRecordClassicality 的 recordGram](../../../D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality.lean)时，坐标换算为
$$
\operatorname{recordGram}(e)_{hk}
=\sum_a(e_h)_a\overline{(e_k)_a}
=\langle e_k,e_h\rangle=G_{kh}.
$$
因此既有记录通道所用的Hadamard乘子矩阵为$\operatorname{recordGram}(e)=G^{\mathsf T}$。

证明。 若向量存在，则$G_{kh}=\overline{G_{hk}}$，且对任意复系数族$z$，
$$
z^\dagger Gz=\left\|\sum_hz_he_h\right\|^2\ge0;
$$
对角条件由单位范数给出。令$A$的列为$e_h$，则$G=A^\dagger A$，其核等于$A$的核，所以$\operatorname{rank}G=\operatorname{rank}A$不超过环境维数。

反之，将$G$作有限谱分解，保留正特征值并取平方根，可构造一个具有$r=\operatorname{rank}G$行的矩阵$A$，满足$A^\dagger A=G$。取其各列为$e_h\in\mathbb C^r$，由$G_{hh}=1$知每列为单位向量。这既给出实现，也达到下界。证毕。

**定理 3.2（记录重叠决定的约化态与终点概率）。** 给定第3.1条的记录、非空有限终点集$S$、映射$b:\mathscr H\to S$和复振幅$\alpha_h$。令$\mathscr H_x=b^{-1}(x)$，$G_x$为相应主子矩阵，$\alpha_x$为相应列向量；空纤维的二次型取零。若
$$
Z=\sum_{x\in S}\alpha_x^\dagger G_x\alpha_x>0,
$$
则联合单位向量
$$
|\Psi\rangle=Z^{-1/2}\sum_h\alpha_h|b(h)\rangle\otimes|e_h\rangle
$$
的系统约化态为
$$
\varrho_S=\frac1Z\sum_{h,k}\alpha_h\overline{\alpha_k}\,G_{kh}\,|b(h)\rangle\langle b(k)|,
$$
终点概率为$P(x)=\alpha_x^\dagger G_x\alpha_x/Z$。注意密度矩阵式中的指标是$G_{kh}$，而二次型中的指标是$G_{hk}$。

证明。 先在保留全部地址$h$的空间$\mathcal H_{\mathscr H}$上，令$R_e|h\rangle=|h\rangle\otimes e_h$。直接应用 [EnvironmentMarginalChannel 的 environment_marginal_channel](../../../D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel.lean)：对任意有限维地址矩阵$A$，
$$
\operatorname{tr}_{\mathcal E}(R_e A R_e^\dagger)
=\operatorname{recordGram}(e)\odot A,
$$
其中$\odot$为逐项乘积。这是任意有限系统和环境维数的既有公式。这里取$A=\alpha\alpha^\dagger$，并定义线性归并$C_b|h\rangle=|b(h)\rangle$。按部分迹的有限坐标定义，
$$
\operatorname{tr}_{\mathcal E}\bigl((C_b\otimes I)R(C_b^\dagger\otimes I)\bigr)
=C_b(\operatorname{tr}_{\mathcal E}R)C_b^\dagger.
$$
这里$(C_b A C_b^\dagger)_{xy}=\sum_{h\in\mathscr H_x}\sum_{k\in\mathscr H_y}A_{hk}$，所以地址归并后的约化矩阵为$C_b(\operatorname{recordGram}(e)\odot\alpha\alpha^\dagger)C_b^\dagger$。不同终点基态正交，故
$$
\left\|\sum_h\alpha_h|b(h)\rangle\otimes e_h\right\|^2
=\sum_{h,k}\overline{\alpha_h}\alpha_k\,
\delta_{b(h),b(k)}G_{hk}
=\sum_{x\in S}\alpha_x^\dagger G_x\alpha_x=Z.
$$
在外积的每个$(h,k)$项中，环境因子为
$$
\operatorname{tr}(|e_h\rangle\langle e_k|)=\langle e_k,e_h\rangle=G_{kh},
$$
这与上述既有公式的$\operatorname{recordGram}(e)_{hk}=G_{kh}$一致；除以$Z$即得到所列约化态。取系统对角元并交换两个有限求和指标，即得到$\alpha_x^\dagger G_x\alpha_x/Z$。正性、非负概率和总和为一也分别由联合外积、各Gram主子矩阵正性及$Z$的定义得到。

若同一终点内全部记录相同，则$G_x$全为一，对$Z$的贡献为$|\sum_{h\in\mathscr H_x}\alpha_h|^2$。若该纤维内记录正交，则贡献为$\sum_{h\in\mathscr H_x}|\alpha_h|^2$。若在该纤维内仅有$e_h=e^{i\theta_h}e$，则相干和应为$\sum_{h\in\mathscr H_x}\alpha_he^{i\theta_h}$，不能遗漏这些相位。这些条件由记录内积决定，不由是否有人阅读记录决定。

$R_e$保留系统地址，单位记录使它等距；非单射$b$的$C_b$不等距。本条只给出归并后指定向量的归一化及部分迹公式，不保证任意振幅和记录分配来自保范演化。将正交输入确定性归并为$b(h)$时所需的附加条件由第3.5条给出。$Z=0$时没有可按此式归一化的态。证毕。

**定理 3.3（复记录重叠的亮态可见度）。** 在第2.4条模型中，令$e_a,e_b$为单位环境向量，$\gamma=\langle e_a,e_b\rangle$，取初始联合态
$$
|\Psi_\theta\rangle=\frac{|10\rangle\otimes e_a+e^{i\theta}|01\rangle\otimes e_b}{\sqrt2}.
$$
仅对系统施加$U(\tau)$，则
$$
P_{00}(\tau,\theta)=\frac{\sin^2(\omega \tau)}2\left[1+\operatorname{Re}(e^{i\theta}\gamma)\right].
$$
当$\sin^2(\omega \tau)>0$时，扫描$\theta$所得可见度$(P_{\max}-P_{\min})/(P_{\max}+P_{\min})$恰为$|\gamma|\le1$。

证明。 两个系统基态正交，故联合态已经归一化，不需要假定$e_a,e_b$正交。由第2.4条，两个系统分量到$00$的振幅均为$-i\sin(\omega \tau)/\sqrt2$。因此$00$分量的环境向量为$-i\sin(\omega \tau)(e_a+e^{i\theta}e_b)/2$，取范数平方即得概率式。由Cauchy–Schwarz不等式，$|\gamma|\le1$；扫描相位时实部的最大、最小值分别为$\pm|\gamma|$，代入可见度定义即得结论。若$\sin^2(\omega \tau)=0$，两极值均为零，该比值未定义，不把它人为指定为某个可见度。证毕。

**定理 3.4（记录操作与局部约化态的充分性）。** 对假设 1.2的$(K_a)_a$，映射
$$
W\psi=\sum_aK_a\psi\otimes|a\rangle
$$
等距，且丢弃记录给出$\Phi(\varrho)=\sum_aK_a\varrho K_a^\dagger$。$\Phi$保迹，并在张量任意有限辅助系统后保持正性。

对同一有限复合空间$\mathcal H_S\otimes\mathcal E$上的两个联合密度矩阵$\varrho,\sigma$，它们对全部系统局部Hermitian算符有相同期望，当且仅当$\operatorname{tr}_{\mathcal E}\varrho=\operatorname{tr}_{\mathcal E}\sigma$。

证明。 记录基正交给$W^\dagger W=\sum_aK_a^\dagger K_a=I$。展开$W\varrho W^\dagger$并取记录部分迹，只保留相同记录指标，得到$\Phi$。迹的循环性给$\operatorname{tr}\Phi(\varrho)=\operatorname{tr}\varrho$。对任何有限辅助空间，张量后的每一项都是$(K_a\otimes I)R(K_a^\dagger\otimes I)$，当$R\ge0$时该项非负，故总和非负。

按部分迹的有限坐标定义直接展开，得
$$
\operatorname{tr}\bigl(\varrho(A\otimes I)\bigr)=\operatorname{tr}\bigl((\operatorname{tr}_{\mathcal E}\varrho)A\bigr).
$$
因此约化态相等充分。反向直接应用 [LocalObservationPartialTraceEquivalence 的 local_observation_partial_trace_equivalence](../../../D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.lean)：将这里的张量因子交换为$\mathcal E\otimes\mathcal H_S$，其 partialTraceFirst 就是本条的$\operatorname{tr}_{\mathcal E}$。上式把原联合态的局部期望换成约化态的Hermitian读数，满足该判据的全部假设，故约化态相等。这说明丢弃环境精确保留全部系统局部观测，而不恢复原联合态。证毕。

**定理 3.5（确定性纤维量子提升的最小环境）。** 设$S\ne\varnothing$有限，$f:S\to\mathcal T=f(S)$，$\mathcal E$为有限维复环境。将不同$s\in S$指定为正交输入基态，并定义线性映射$W:\mathcal H_S\to\mathcal H_{\mathcal T}\otimes\mathcal E$的确定性基态输出为
$$
W|s\rangle=|f(s)\rangle\otimes e_s.
$$
则$W$等距，当且仅当
$$
\delta_{f(s),f(t)}\langle e_s,e_t\rangle=\delta_{s,t}\qquad(s,t\in S).
$$
等价地，每个$e_s$为单位向量，且每个纤维内部不同输入的记录互相正交；不同纤维之间不要求正交。最小环境维数恰为
$$
M_f=\max_{y\in\mathcal T}|f^{-1}(y)|.
$$

证明。 两个输出基像的内积就是等式左侧；输入基正交，故保持全部基内积等价于等距，并立即给出单位条件和同纤维正交条件。最大纤维中有$M_f$个正交单位记录。若它们的线性组合为零，分别与每个记录取内积便得全部系数为零，所以它们线性无关，$\dim\mathcal E\ge M_f$。这个量子下界适用于任意满足条件的环境向量。

上界直接使用 [MinimumRollbackAlphabet 的 minimum_rollback_alphabet](../../../D5/S0/History/Coding/MinimumRollbackAlphabet.lean)的现有构造：存在
$$
\ell:S\longrightarrow\{0,\ldots,M_f-1\},\qquad
s\longmapsto(f(s),\ell(s))\text{ 单射}.
$$
取$\mathcal E=\mathbb C^{M_f}$、$e_s=|\ell(s)\rangle$。同纤维不同输入的标签必不同，其记录因而正交；不同纤维可以复用标签。这个$W$正是 [SequentialRegisterCircuit 的 coordinateEmbedding](../../../D5/S3/Quantum/Entanglement/SequentialRegisterCircuit.lean)应用于该单射后的坐标等距，coordinate_embedding_basis 给出$|s\rangle\mapsto|f(s),\ell(s)\rangle$，在乘积基与张量基的识别下即为所需基像。由已证内积条件，上界$M_f$可达；经典标签的最小性无需重新证明，也没有被用来替代上述量子下界。

对任意输入Hermitian算符$A$，保留记录后可用$\widetilde A=WAW^\dagger$恢复它，因为$W^\dagger\widetilde AW=A$。精确的全空间酉扩张可在共同有限ambient空间
$$
\mathcal A=\mathcal H_S\oplus(\mathcal H_{\mathcal T}\otimes\mathcal E),\qquad
\iota_{\rm in}(x)=(x,0),\quad\iota_{\rm out}(y)=(0,y)
$$
中表述。两个映射$\iota_{\rm in}$及$\iota_{\rm out}W$都是从同一个$\mathcal H_S$到$\mathcal A$的等距嵌入，直接应用同一 [SequentialRegisterCircuit 的 exists_unitary_agree](../../../D5/S3/Quantum/Entanglement/SequentialRegisterCircuit.lean)，得到
$$
\mathscr U:\mathcal A\longrightarrow\mathcal A\text{ 酉},\qquad
\mathscr U\iota_{\rm in}=\iota_{\rm out}W.
$$
其基底表述是把上述两组$|S|$个正交单位向量各自补成$\dim\mathcal A=|S|+|\mathcal T|\dim\mathcal E$个向量的正交基，再逐基对应。酉算符的定义域和值域是同一个$\mathcal A$；维数可能不同的$\mathcal H_S$与$\mathcal H_{\mathcal T}\otimes\mathcal E$之间只有所述等距$W$。额外ambient空间没有消除输出记录，$M_f$的最小性指确定性提升中该记录因子的维数。

本条的$S$是可独立制备的正交输入标号。第2.8条对同一个输入插入基底所得的路径项，并未被假定为这些正交输入，所以本条不禁止未写入路径记录时的相干合成。证毕。

**定理 3.6（Zeckendorf规范化的无损记录代价）。** 对任意非空有限原始表族$S\subset\mathcal R$，确定性规范化$f=\nu|_S$的最小无损环境维数为
$$
\max_{c\in\nu(S)}|\{r\in S:\nu(r)=c\}|.
$$
只要$S$含有同一素数$p$上的
$$
r=e_{p,0}+e_{p,1},\qquad r'=e_{p,2},
$$
无记录规范化就不是等距映射，环境维数至少为二。对全部$\mathcal R$，不存在对所有有限输入族都适用的统一有限维无损环境。

证明。 第一式直接将第3.5条用于$\nu|_S$，各$r\in S$按定义1.1作为互相正交的输入标号。所列两表是[Z 卷定理 25](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的规范化反例：$G_0+G_1=1+2=3=G_2$，且$\nu(r)=\nu(r')=e_{p,2}$。两个正交输入若都映到同一输出基态，则$(|r\rangle-|r'\rangle)/\sqrt2$被送到零，故不能等距；第3.5条的量子下界给出至少二维记录。

对任意自然数$a$，考虑同一素数上的不同原始表
$$
r_k=(a-2k)e_{p,0}+ke_{p,1},\qquad 0\le k\le\lfloor a/2\rfloor.
$$
它们因$r_k(p,1)=k$而互异，每个表的该素数估值都是$a$，所以全在$\nu$的同一纤维中，纤维至少有$\lfloor a/2\rfloor+1$个元素。给定任何非负整数环境维数$d$，取$a=2d$，这个有限输入族就需要至少$d+1$维环境，矛盾。所有这些原始表均可用 Z 卷定理 13 在原CSA中平衡实现。这里的否定只用了有限子集，没有交换任何无限振幅和。证毕。

**定理 3.7（后续观察下降的充要条件与原运算边界）。** 设$f:S\to f(S)$为有限集合上的映射，$q:S\rightharpoonup Y$为部分观察，并用与正常值不交的新符号$\bot$记录失败。存在粗观察$\bar q$满足$q_\bot=\bar q\circ f$，当且仅当同一$f$-纤维内的定义性相同，且在有定义时读数相同。

若$S\ne\varnothing$且$q:S\to\mathbb R$为总读数，第3.5条的等距提升允许仅用输出系统上的对角算符读出$q$，当且仅当$q$在每个$f$-纤维上常值。

证明。 若粗观察存在，同一$f$值当然给相同的包含失败标签的输出。反之，在每个纤维任选一个元素，用它的$q_\bot$值定义$\bar q$；纤维常值条件保证定义与选择无关。

对实总读数，令$A_q=\sum_sq(s)|s\rangle\langle s|$，输出对角算符写成$B=\sum_yb(y)|y\rangle\langle y|$。第3.5条的内积条件给
$$
W^\dagger(B\otimes I)W=\sum_sb(f(s))|s\rangle\langle s|.
$$
因此它等于$A_q$，恰当且仅当$q=b\circ f$。保留记录后可按第3.5条恢复一般读数；只看粗系统则不能突破这个条件。

把上述判据用于[Z 卷定理 25](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的$r=e_{p,0}+e_{p,1}$、$r'=e_{p,2}$：两者具有相同规范表，但原$q$为二、一；筛选$\lambda(p,0)$后为一、零，故这些读数不能下降到规范表。再用第1.4条分别在时刻零、二实现$e_{2,0}$，得到$X_0,X_2$，并在时刻一实现$e_{3,0}$，得到$Y$。这是 Z 卷定理 26 的实现：两左输入的规范表相同，而原守卫分别是$0<1$和$2<1$，所以固定右输入$Y$后的原$\triangleright$定义性也不能下降。

此外，直接使用[Z 卷定理 27–28](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)：第1.4条在时刻零、槽$\lambda(2,0)$、$\lambda(3,0)$的单选实现，经原$\boxtimes$所得唯一已选新事件位于$\lambda(5,0)$，整数读数为五而非六；两个$\lambda(2,0)$输入相乘则产生槽外位置$(4,0,0)$，离开$\mathcal B_\lambda^+$。普通数位索引卷积也有$e_1*e_1=e_2$，而$G_2=3\ne G_1^2=4$。所以原档案运算、数位卷积、整数乘法和独立系统复合仍是不同的操作。证毕。

## 4. 允许后续操作与真正的可辨识性

**定义 4.1（实际后续效应空间）。** 固定正整数$d$、$d$维系统、有限测量$(M_a)_a$及一族实际允许的通道$\mathscr C$，每个通道由第3.4条的矩阵族给定，输入和输出均为此系统。定义其对偶
$$
\Phi^*(A)=\sum_bK_b^\dagger A K_b,
\qquad \operatorname{tr}(\Phi(\varrho)A)=\operatorname{tr}(\varrho\Phi^*(A)).
$$
每个操作词$w=(\Phi_1,\ldots,\Phi_m)$有限，先施加$\Phi_1$，故$\Phi_w=\Phi_m\circ\cdots\circ\Phi_1$，$\Phi_w^*=\Phi_1^*\circ\cdots\circ\Phi_m^*$；空词的通道与对偶均为恒等。规定$\varrho\approx_{\mathscr C}\sigma$当且仅当每个这样的词及每个测量结果都有相同概率，包括空词。

在实向量空间$\operatorname{Herm}(d)$上使用内积$(A,B)=\operatorname{tr}(AB)$，并定义
$$
\mathcal O_0=\operatorname{span}_{\mathbb R}\{I,M_a:a\},
$$
$$
\mathcal O_{k+1}=\operatorname{span}_{\mathbb R}\left(\mathcal O_k\cup\bigcup_{\Phi\in\mathscr C}\Phi^*(\mathcal O_k)\right),\qquad
\mathcal O_\infty=\bigcup_{k\ge0}\mathcal O_k.
$$
线性张成仅使用有限线性组合；$\mathscr C$可以是无限集合。这里不把生成的乘法代数自动视为允许测量族，也不把条件筛选后的失败删除。

**定理 4.2（有限维观察闭包、稳定深度及完备性）。** 令$d_0=\dim_{\mathbb R}\mathcal O_0$。则存在$k\le d^2-d_0$使$\mathcal O_k=\mathcal O_\infty$，并且
$$
\varrho\approx_{\mathscr C}\sigma
\quad\Longleftrightarrow\quad
\varrho-\sigma\in\mathcal O_\infty^\perp.
$$
这些观察能够区分全部密度矩阵，当且仅当$\mathcal O_\infty=\operatorname{Herm}(d)$。增加允许通道，或增加可选测量并保留全部旧效应，只能细化观察等价。

证明。 迹的循环性证明定义 4.1的对偶恒等式，且$\Phi^*(I)=\sum_bK_b^\dagger K_b=I$。重复应用该恒等式，把任意有限操作词后的概率写成初态对$\Phi_w^*(M_a)$的期望。对$k$归纳，$\mathcal O_k$恰由长度至多$k$的这些效应及$I$实线性张成。故全部词的概率相等，恰等价于差矩阵对$\mathcal O_\infty$正交。

嵌套空间$\mathcal O_k$的维数不超过$d^2$。若某一步相等，则该空间已经对每个$\Phi^*$不变，以后不再增长；若未相等，维数至少增加一。因此最多$d^2-d_0$次严格增长后必稳定，给出所列深度界。

若$\mathcal O_\infty$为全部Hermitian空间，取差矩阵自身作测试，便知差为零。反之若它是真子空间，取非零$D\in\mathcal O_\infty^\perp$。因$I\in\mathcal O_\infty$，有$\operatorname{tr}D=0$。取$0<\varepsilon\le1/(d\|D\|)$，则$I/d\pm\varepsilon D$是两个不同密度矩阵，而差属于同一个正交补，所以全部允许观察相同。最后，扩充操作或效应使每层可见空间只增不减，等价关系因而只能细化。

这在密度矩阵载体、实际通道签名及概率向量读数上给出[原CSA定义 16、命题 16–17](CONTEXTUAL_SPACETIME_ARITHMETIC.md)的观察等价与扩签名细化的一个实例。深度界依赖有限维和所给线性演化，不是原CSA任意部分结构的统一深度界。证毕。

**定理 4.3（完整矩阵代数仍不等于实际观察完备）。** 对$L\ge1$，若假设 2.2中全部$h_j\ne0$，则$V_Z$与$H_L$生成的含幺复$*$-代数是$\operatorname{End}(\mathcal H_L)$。但是，在第2.4条$g\ne0$模型中，若只允许自由演化$\tau\ge0$以及末端构型测量、不允许额外中间操作，则其可见Hermitian空间只有六维。

具体地，在正交基$(z,B,D)$，其中$z=00$，记$P_r=|r\rangle\langle r|$，并定义
$$
X_{rs}=|r\rangle\langle s|+|s\rangle\langle r|,\qquad
Y_{rs}=i(|s\rangle\langle r|-|r\rangle\langle s|).
$$
实际可见空间及其正交补为
$$
\mathcal O_\infty=\operatorname{span}_{\mathbb R}\{P_z,P_B,P_D,Y_{zB},X_{BD},Y_{zD}\},
$$
$$
\mathcal O_\infty^\perp=\operatorname{span}_{\mathbb R}\{X_{zB},X_{zD},Y_{BD}\}.
$$

证明。 由第1.3条的简单谱，每个构型投影$P_c$都是$V_Z$的Lagrange插值多项式。若$c,d$相差一次允许翻转，则$P_cH_LP_d$是非零系数乘矩阵单位$|c\rangle\langle d|$。所有no11构型都可逐次删除激发到达全零，故单翻转图连通。沿图路径相乘这些矩阵单位，可得任意$|c\rangle\langle d|$，从而生成完整矩阵代数。

现在只考察所指定的自由演化观察。由第2.3条的群律，任何有限操作词等于非负总时长的单次自由演化。令$\theta=\omega\tau$。第2.4条给出
$$
U(\tau)^\dagger P_zU(\tau)=\cos^2\theta P_z+\sin^2\theta P_B+\sin\theta\cos\theta Y_{zB},
$$
$$
U(\tau)^\dagger(P_{10}-P_{01})U(\tau)=\cos\theta X_{BD}-\sin\theta Y_{zD}.
$$
三个构型投影之和为$I$，所以全部末端效应均在所列六维空间内。反过来，取$\theta$模$2\pi$分别为$0,\pi/2,\pi/4$，第一式产生$P_z,P_B,Y_{zB}$，再由$I$产生$P_D$；第二式产生$X_{BD},Y_{zD}$。因$g\ne0$，这些角度都可由适当非负时间实现。六个矩阵实线性独立，故空间恰为六维。九维Hermitian矩阵的标准对角、实非对角、虚非对角基再给出所列三维正交补。

例如对$0<\varepsilon\le1/3$，
$$
\varrho_\pm=I_3/3\pm\varepsilon X_{zB}
$$
的特征值均为$1/3+\varepsilon,1/3-\varepsilon,1/3$，故是不同密度矩阵，却在全部这些自由演化末端观测下不可区别。因此“$H_L,V_Z$生成完整矩阵代数”不能替代“实际允许控制与测量已经完备”。证毕。

## 5. Fibonacci融合联系的精确边界

**定理 5.1（指定边界的融合路径双射）。** 使用两种离散融合标号$1,\boldsymbol{\tau}$及规则$1\times\boldsymbol{\tau}=\boldsymbol{\tau}$、$\boldsymbol{\tau}\times\boldsymbol{\tau}=1+\boldsymbol{\tau}$。粗体$\boldsymbol{\tau}$是融合标号，与实演化参数$\tau$分型；右式的加号列出允许结果，不表示复振幅相加。对整数$L\ge0$，令$\mathcal F_{L+1}^{\boldsymbol{\tau},\boldsymbol{\tau}}$为路径集合
$$
(a_0,a_1,\ldots,a_{L+1}),\qquad a_0=a_{L+1}=\boldsymbol{\tau},
$$
其中每个$a_k\in\{1,\boldsymbol{\tau}\}$，且对$0\le k\le L$，$a_{k+1}$是$a_k\times\boldsymbol{\tau}$的允许结果。则
$$
c_j=1\ \Longleftrightarrow\ a_{j+1}=1\qquad(0\le j<L)
$$
给出$\mathcal F_{L+1}^{\boldsymbol{\tau},\boldsymbol{\tau}}$与$\mathcal W_L$的双射，进而在以各条路径为正交单位基的$\mathbb C^{\mathcal F_{L+1}^{\boldsymbol{\tau},\boldsymbol{\tau}}}$与$\mathcal H_L$之间给出酉同构。

证明。 融合标号为$1$时下一个必须为$\boldsymbol{\tau}$，因此内部标号$1$不能相邻；端点均为$\boldsymbol{\tau}$，不产生额外限制。所以任一路径给出no11字串。反过来，从no11字串恢复内部标号，补上两个$\boldsymbol{\tau}$端点：当前标号为$1$时，下一标号因no11或端点条件为$\boldsymbol{\tau}$；当前为$\boldsymbol{\tau}$时，下一标号可为$1$或$\boldsymbol{\tau}$，都允许。两构造互逆，基底同构即得。维数$F_{L+2}$直接引用第1.3条，不重证窗口计数。

这里激发位$1$对应平凡融合输出$1$，未激发位$0$对应$\boldsymbol{\tau}$；它不是“每个激发就是一个$\boldsymbol{\tau}$任意子”的对应。此编码的边界与标号见 I. Lesanovsky、H. Katsura，*Interacting Fibonacci anyons in a Rydberg gas*, Physical Review A **86**, 041601(R) (2012)，[图 1、式 (1)，DOI: 10.1103/PhysRevA.86.041601](https://doi.org/10.1103/PhysRevA.86.041601)，[arXiv:1204.0903v1](https://arxiv.org/abs/1204.0903v1)。该处$N-1$个原子编码$N$个$\boldsymbol{\tau}$融合步骤的中间结果，本条取$N=L+1$并固定两端为$\boldsymbol{\tau}$。边界不可省略：例如两次融合、初始标号改为$1$、终点固定为$\boldsymbol{\tau}$时，中间标号只能是$\boldsymbol{\tau}$，仅有一条路径；初始为$\boldsymbol{\tau}$时中间标号可为$1$或$\boldsymbol{\tau}$，有两条。证毕。

**定理 5.2（融合投影、局部参数匹配与动力学互绕）。** 令$\varphi=(1+\sqrt5)/2$，$J\in\mathbb R$为实能量系数。取第5.1条融合规则下、允许所列外部标号的两个五维局部空间，其有序正交基分别为源基
$$
\mathcal B_{\rm s}=(1\boldsymbol{\tau}1,\boldsymbol{\tau}\boldsymbol{\tau}1,
1\boldsymbol{\tau}\boldsymbol{\tau},\boldsymbol{\tau}1\boldsymbol{\tau},
\boldsymbol{\tau}\boldsymbol{\tau}\boldsymbol{\tau})
$$
及重结合后的目标基
$$
\mathcal B_{\rm t}=(111,\boldsymbol{\tau}\boldsymbol{\tau}1,
1\boldsymbol{\tau}\boldsymbol{\tau},\boldsymbol{\tau}1\boldsymbol{\tau},
\boldsymbol{\tau}\boldsymbol{\tau}\boldsymbol{\tau}).
$$
在源基$(a,b,c)$中先取$b\in a\times\boldsymbol{\tau}$，再取$c\in b\times\boldsymbol{\tau}$；在目标基$(a,b',c)$中先融合这两个$\boldsymbol{\tau}$得到$b'\in\{1,\boldsymbol{\tau}\}$，再令$c\in a\times b'$，其中$1\times1=1$、$\boldsymbol{\tau}\times1=\boldsymbol{\tau}$。这里$x\in a\times b$表示$x$是该融合的允许结果。在这些路径规则之外，额外指定从目标坐标到源坐标的重结合矩阵为
$$
F=I_3\oplus\begin{pmatrix}\varphi^{-1}&\varphi^{-1/2}\\\varphi^{-1/2}&-\varphi^{-1}\end{pmatrix},\qquad
P_{\rm t}=\operatorname{diag}(1,0,0,1,0),\qquad
\Pi=FP_{\rm t}F^\dagger.
$$
$P_{\rm t}$在目标基中投影到$b'=1$，即中间两个$\boldsymbol{\tau}$融合到$1$的结果。按这两组有序基各自识别为$\mathbb C^5$后，矩阵$F$满足$F^\dagger=F=F^{-1}$；$\Pi$是源基中的正交投影，并且
$$
\Pi=\operatorname{diag}(1,0,0)\oplus
\begin{pmatrix}\varphi^{-2}&\varphi^{-3/2}\\\varphi^{-3/2}&\varphi^{-1}\end{pmatrix}.
$$
采用上述源基中的局部块
$$
h=\operatorname{diag}(f_1,f_2,\alpha)\oplus
\begin{pmatrix}\beta&\Omega\\\Omega&\gamma\end{pmatrix},\quad
f_1=\Delta+V_2-\beta+2\gamma,\quad f_2=\Delta-\alpha-\beta+3\gamma,
$$
其中$\alpha,\beta,\gamma,\Omega,\Delta,V_2$均为实能量系数。若取
$$
\alpha=0,\quad\beta=-J\varphi^{-2},\quad\gamma=-J\varphi^{-1},
$$
$$
\Omega=-J\varphi^{-3/2},\quad
\Delta=-J(\varphi^{-2}-3\varphi^{-1}),\quad V_2=-J\varphi,
$$
则$h=-J\Pi$。本条的驱动非对角元使用能量系数$\Omega$，失谐贡献使用$+\Delta$；它们区别于假设2.2中带$\hbar/2$及负失谐号的角频率。局部块、两组重结合基、投影及参数见 Lesanovsky–Katsura，[Physical Review A **86**, 041601(R)，式 (2)–(5)，DOI: 10.1103/PhysRevA.86.041601](https://doi.org/10.1103/PhysRevA.86.041601)。

另对任意有限维复Hilbert空间$\mathcal H,\mathcal H'$上的自伴Hamiltonian$H,H'$及指定酉映射$J_0:\mathcal H\to\mathcal H'$，在固定能量零点、使用同一$\hbar>0$的条件下，
$$
J_0H=H'J_0
\quad\Longleftrightarrow\quad
\bigl(\forall\tau\in\mathbb R,\quad
J_0e^{-i\tau H/\hbar}=e^{-i\tau H'/\hbar}J_0\bigr).
$$
若同时把态和测量按$J_0$输运，则这个条件保证全部相应测量概率相同。

证明。 由$\varphi^{-2}+\varphi^{-1}=1$，$F$的二阶块平方为$I_2$，非对角元相消；它是实对称矩阵，故$F^\dagger F=I$。以酉矩阵共轭一个对角投影仍为投影，直接乘法给出$\Pi$的所列矩阵。将参数代入，得到$f_2=0$，并由$\varphi=1+\varphi^{-1}$得到$f_1=-J$，其余矩阵元逐项正好为$-J\Pi$。因此局部等式已被证明。

若$J_0H=H'J_0$，对幂次归纳并代入绝对收敛的矩阵指数级数即得传播互绕；反向在$\tau=0$求导即可。输运态$J_0\varrho J_0^\dagger$和效应$J_0MJ_0^\dagger$后，概率相等由该互绕及迹的循环性得到。若仅比较态与概率，则对实常数能量$\kappa$，$H'=J_0HJ_0^\dagger+\kappa I$只使传播多出全局相位$e^{-i\tau\kappa/\hbar}$，不会改变这些概率。

局部等式$h=-J\Pi$只能用于上述五维块。将它提升为某个完整开放链的Hamiltonian等式，还须逐项匹配该链两端的作用、整体能量常数及任何保留的远程相互作用和有限阻塞修正。这些是另需履行的全链条件；上述局部证明不推出固定能量零点下的完整开放链等式。原论文对主Hamiltonian、边界与修正项的区分见上述式 (1)–(2)附近的定义。纯投影翻转模型在$J\ne0$时也不能自动满足$V_2=-J\varphi$的局部参数要求。

最后，维数相同本身不足以保证动力学等价：在同一个第2.4条三维空间上，$H=0$与$H_g$在$g\ne0$时分别有谱$\{0,0,0\}$和$\{-\sqrt2g,0,\sqrt2g\}$，即使允许整体能量平移也不能相互酉共轭。第5.1条只给指定边界的路径正交基对应，本条再给指定重结合矩阵下的局部投影。编织算符及其关系、拓扑保护和实验实现均需要额外结构与证明，不能从这些维数和基底等式推出。证毕。

## 追加锚（本行以下为增补区）

## 6. 后选择规范化的相干界

**定理 6.1（共同振幅与全态成功概率）。** 设非空有限集$S$、$\mathcal T=f(S)$，$\mathcal H_S=\mathbb C^S$、$\mathcal H_{\mathcal T}=\mathbb C^{\mathcal T}$均以标号为正交基，所有输入、输出基向量的相位固定，内积沿用定义1.1的首变量共轭线性约定。记
$$
S_y=f^{-1}(y),\qquad n_y=|S_y|,\qquad M=\max_{y\in\mathcal T}n_y,\qquad
F|s\rangle=|f(s)\rangle.
$$
所谓共同振幅成功支路，要求同一个线性Kraus算子$K:\mathcal H_S\to\mathcal H_{\mathcal T}$满足
$$
K|s\rangle=\lambda|f(s)\rangle\qquad(s\in S),
$$
其中$\lambda\in\mathbb C$与$s$无关，且该成功支路自身不另留依赖$s$的记录；失败输出不受规范标签要求约束。这比仅指定基态输出密度矩阵更强。

此支路可实现当且仅当$|\lambda|\le M^{-1/2}$；最大共同振幅的模为$M^{-1/2}$。对任意密度矩阵$\varrho$及单位向量$\psi=\sum_{s\in S}\alpha_s|s\rangle$，
$$
p_\lambda(\varrho)=|\lambda|^2\operatorname{tr}(F\varrho F^\dagger),\qquad
p_\lambda(\psi)=|\lambda|^2\sum_{y\in\mathcal T}\left|\sum_{s\in S_y}\alpha_s\right|^2.
$$
成功概率为正时，条件输出为
$$
\frac{F\varrho F^\dagger}{\operatorname{tr}(F\varrho F^\dagger)};
$$
纯态对应$F\psi/\|F\psi\|$，忽略全局相位。成功概率为零时，条件态不定义。

最优取$\lambda=M^{-1/2}$时，每个基态的成功率都是$1/M$，但对所有单位叠加态存在严格正的统一下界，当且仅当$f$单射；此时成功率恒为一。若$f$非单射，最小成功率为零，最大为一；即使排除零成功态，成功率下确界仍为零。

证明。 线性性迫使$K=\lambda F$。置
$$
u_y=\frac1{\sqrt{n_y}}\sum_{s\in S_y}|s\rangle\qquad(y\in\mathcal T),
$$
则$u_y$两两正交且均为单位向量，直接作用于基向量可得
$$
F^\dagger F=\sum_{y\in\mathcal T}n_y|u_y\rangle\langle u_y|.
$$
故$\|F\|^2=M$，单Kraus支路的必要条件$K^\dagger K\le I$恰等价于$|\lambda|^2M\le1$。充分性可将$K$与失败算子
$$
L=(I-K^\dagger K)^{1/2}
$$
组成等距映射$\psi\mapsto K\psi\oplus L\psi$，再测量两个正交输出扇区。概率和条件态公式由$K\varrho K^\dagger$立即得到。

最优时
$$
p(\psi)=\sum_{y\in\mathcal T}\frac{n_y}{M}|\langle u_y,\psi\rangle|^2.
$$
若$f$单射，$F^\dagger F=I$。否则在最大纤维取不同$s,t$，
$$
d=\frac{|s\rangle-|t\rangle}{\sqrt2}
$$
满足$Fd=0$；该纤维的$u_y$记为$u$，满足$p(u)=1$且$d\perp u$。于是
$$
\psi_\varepsilon=\sqrt{1-\varepsilon^2}\,d+\varepsilon u\qquad(0<\varepsilon\le1)
$$
为单位向量且成功率为$\varepsilon^2$，证明全部极值与下确界。若将若干成功Kraus算子$K_j=\lambda_jF$合并，约束变为
$$
\left(\sum_j|\lambda_j|^2\right)M\le1,
$$
也不能提升共同相干支路的总基态成功率。

进一步，令$\mathcal H_+=\operatorname{span}\{u_y:y\in\mathcal T\}$。$F$的核恰由每个纤维内系数和都为零的向量组成，维数为$|S|-|\mathcal T|$；在$\mathcal H_+$的单位态上，最优支路的最小成功率恰为
$$
\frac{\min_{y\in\mathcal T}n_y}{M}.
$$
这是指定输入子空间后的正下界，不能替代全部输入上的保证；以上结论均直接由所示谱分解得到。证毕。

本条的测量算子、概率及条件态框架见 John Watrous，*The Theory of Quantum Information*，Cambridge University Press，2018，[DOI: 10.1017/9781316848142](https://doi.org/10.1017/9781316848142)，[作者公开预出版版本](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，§2.3.2，印刷页111–113（PDF页119–121），式 (2.255)–(2.262)。其中式 (2.255)–(2.256)给出每结果一个算符及完备性，式 (2.257)给出分支概率和正概率时的条件态；$K^\dagger K\le I$是完备性的直接必要推论，充分性由本条的失败支路补全给出。一般量子仪器结果不自动等于单Kraus支路。仓内 [FiniteKrausInstrumentBornMarginal 的 finite_kraus_instrument_born_marginal](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean)在完整归一化有限Kraus家族、输入输出同一有限非空载体上给出分支迹等于相应效应的Born权重；该结果不提供本条的最优振幅或统一成功率界。

一般概率纯态变换见 Anthony Chefles、Richard Jozsa、Andreas Winter，*On the existence of physical transformations between sets of quantum states*，International Journal of Quantum Information **2**(1)，11–21（2004），[DOI: 10.1142/S0219749904000031](https://doi.org/10.1142/S0219749904000031)。这里所用正文定位为 [arXiv:quant-ph/0307227v1](https://arxiv.org/pdf/quant-ph/0307227v1)（2003年7月30日），第6页定理3及式 (7)–(8)、第7页式 (9)。该判据以Gram矩阵的Hadamard分解及半正定不等式处理一般概率变换，允许输入相关余记录；在固定基向量相位、共同复振幅且无输入相关余记录的本条条件下，单成功项的系数矩阵才特化为$\Pi=|\lambda|^2\mathbf1\mathbf1^\dagger$，其中$\mathbf1$为全一列向量。仅共同成功概率不能推出这一特化。所列页码属于arXiv v1，本条是该成熟框架下的有限函数特化。

**定理 6.2（最小记录环境可达与测量平均）。** 沿用定理6.1的$S,f,M,F$。定理3.5（确定性纤维量子提升的最小环境）的$M$维正交记录上界构造已经足以达到定理6.1的最优值，不必增大被测记录空间。这里$M$计量测量前的量子记录环境，测量结果另作为经典输出；并未将测量及读出也要求为此空间内的封闭酉演化。此为可选构造的存在性，不保证任意预先固定的最小记录构造均可只靠环境测量达到。

证明。 将各纤维枚举为$s_{y,1},\ldots,s_{y,n_y}$，直接使用定理3.5的正交记录上界，取等距映射
$$
W|s_{y,j}\rangle=|y\rangle\otimes b_j,
$$
其中$b_1,\ldots,b_M$为同一环境$\mathcal E$的正交基。取
$$
h=\frac1{\sqrt M}\sum_{j=1}^M b_j,\qquad P=|h\rangle\langle h|,
$$
测量投影$P$及$I-P$，并只接受$P$。因为$\langle h,b_j\rangle=M^{-1/2}$，
$$
(I\otimes P)W\psi=\frac{F\psi}{\sqrt M}\otimes h.
$$
故成功支路恰为$K=F/\sqrt M$，成功后的环境向量$h$与输入无关。$M=1$时$P=I$，失败结果概率为零。

对已固定的等距记录$W|s\rangle=|f(s)\rangle\otimes e_s$，环境单独产生共同振幅$\lambda$的无记录支路，当且仅当存在$\|h\|\le1$使
$$
\langle h,e_s\rangle=\lambda\qquad(s\in S).
$$
确实，若成功环境算子$B$为收缩且满足$Be_s=\lambda\eta$、$\|\eta\|=1$，取$h=B^\dagger\eta$即可，因为
$$
\langle B^\dagger\eta,e_s\rangle=\langle\eta,Be_s\rangle=\lambda.
$$
反之取$B=|\eta\rangle\langle h|$，其为收缩且$Be_s=\lambda\eta$。两个二元纤维分别使用记录$(b_1,b_2)$与$(b_1,-b_2)$，仍是定理3.5允许的最小构造，却要求
$$
\langle h,b_2\rangle=\langle h,-b_2\rangle=\lambda,
$$
迫使$\lambda=0$。

若固定环境恰为$M$维且$\lambda=1/\sqrt M$，则任一最大纤维的记录构成环境的正交基，上述内积条件唯一确定
$$
h=\frac1{\sqrt M}\sum_{s\in S_y}e_s;
$$
此向量还必须满足其余纤维的全部条件。因此，环境维数达到最小值，不等于跨纤维记录已经相位对齐。

回到本条开头的枚举记录构造，将失败投影细分，取$\mathcal E$的正交基$h_1=h,h_2,\ldots,h_M$，记
$$
K_j=(I\otimes\langle h_j|)W.
$$
忘记测量结果并丢弃环境后，由定理3.2、3.4所用的部分迹公式，
$$
\Phi(\varrho)=\sum_{j=1}^M K_j\varrho K_j^\dagger
=\operatorname{tr}_{\mathcal E}(W\varrho W^\dagger),\qquad
\sum_{j=1}^M K_j^\dagger K_j=I.
$$
对这里的有限矩形Kraus家族，直接应用 [FiniteKrausChannel 的 finite_kraus_quantum_channel](../../../D5/S3/Quantum/Foundation/FiniteKrausChannel.lean)的完备性构造，$\Phi$是保迹通道，且
$$
\Phi(|s\rangle\langle s|)=|f(s)\rangle\langle f(s)|.
$$
当$M>1$时，$\Phi$不同于仅有成功项$F\varrho F^\dagger/M$：定理6.1的$d$在成功支路概率为零，平均通道却将其以总概率一送到该纤维的标签纯态。故基态确定输出并不等于共同振幅的相干汇聚；零成功率输入的条件态没有定义，不能以除法归一化将失败当成成功。证毕。

测量结果的条件化及其通道之和沿用 Watrous，前引 §2.3.2，式 (2.257)–(2.262)：式 (2.258)–(2.260)给出一般完全正仪器求和为通道，式 (2.261)–(2.262)给出单算符特例及经典结果寄存器。在联合空间对完整正交投影测量作条件化时，亦可使用 [Conditioning 的 conditionalState_isState](../../../D5/S3/Observer/Conditioning.lean)的非零记录权重条件；它不定义零概率条件态。记录维数与一般部分迹直接复用定理3.5及上述既有公式，所引有限Kraus通道构造不承担任意单支收缩的补全或后选择最优界。

**定理 6.3（Zeckendorf大纤维的后选择代价）。** 沿用定理3.6（Zeckendorf规范化的无损记录代价）的原始表、规范化$\nu$与低位到高位位序。对固定素数$p$和整数$a\ge0$，恰取有限输入族
$$
S_a=\left\{r_k=(a-2k)e_{p,0}+ke_{p,1}:0\le k\le\lfloor a/2\rfloor\right\},
$$
其中$k$取整数。记
$$
m_a=\lfloor a/2\rfloor+1,\qquad c_a=\nu(ae_{p,0}).
$$
在定理6.1的固定基态相位、共同振幅且成功支路无输入相关余记录条件下，共同振幅的最优模为$m_a^{-1/2}$，每个表基态成功率为$1/m_a$，而任意单位叠加$\psi=\sum_{k=0}^{m_a-1}\alpha_k|r_k\rangle$的最优成功率为
$$
p(\psi)=\frac1{m_a}\left|\sum_{k=0}^{m_a-1}\alpha_k\right|^2.
$$
不存在适用于全部有限原始表族的正的统一共同基态成功率下界。

证明。 定理3.6已给出这些表互异且均满足$\nu(r_k)=c_a$，故$\nu|_{S_a}$只有一个大小为$m_a$的纤维，直接应用定理6.1与6.2即可。同相均匀纯态
$$
\frac1{\sqrt{m_a}}\sum_{k=0}^{m_a-1}|r_k\rangle
$$
的成功率为一，均匀经典混合
$$
\varrho_{\mathrm{mix}}=\frac1{m_a}\sum_{k=0}^{m_a-1}|r_k\rangle\langle r_k|
$$
的成功率为$1/m_a$；$m_a\ge2$时，任何系数和为零的单位态成功率为零。由于$m_a$任意大，最优共同基态成功率趋于零。更强地，若收缩算子
$$
K:\ell^2(\mathcal R)\longrightarrow\ell^2(\nu(\mathcal R))
$$
对全部原始表基态满足同一振幅等式$K|r\rangle=\lambda|\nu(r)\rangle$，限制到每个$S_a$都须满足$m_a|\lambda|^2\le1$，故只能有$\lambda=0$；此论证只用有限限制。

回到有限输入族$S_a$，取其最优支路$K=F/\sqrt{m_a}$。若输入另与未测有限维参考空间$\mathcal H_R$纠缠，写成单位向量
$$
\Psi=\sum_{k=0}^{m_a-1}|r_k\rangle\otimes v_k,\qquad
\sum_{k=0}^{m_a-1}\|v_k\|^2=1,
$$
则同一最优支路给出
$$
(K\otimes I_{\mathcal H_R})\Psi
=|c_a\rangle\otimes\frac1{\sqrt{m_a}}\sum_{k=0}^{m_a-1}v_k,
\qquad
p(\Psi)=\frac1{m_a}\left\|\sum_{k=0}^{m_a-1}v_k\right\|^2.
$$
因而参考向量两两正交时成功率仍为$1/m_a$：只测量新增环境，不能同时擦去存于其他寄存器的历史。对固定$S_a$的这个正的统一率伴随参考记录保留，不是无记录归并的反例。此式由$K\otimes I_{\mathcal H_R}$逐项作用得到。

因此，保留历史给出定理3.5、3.6的确定性无损提升；仅输出规范标签的后选择支路能消除同纤维记录并相干求和，却消去原始表空间中的全部零和方向，不能无损保留任意原始叠加。忽略结果仍回到定理6.2的平均通道，而非确定性无记录相干归并。这里的正交性属于可独立制备的原始表输入，不把同一个输入的未记录路径项另当正交历史。证毕。

## 追加锚（本行以下为增补区）

## 7. 有限记录的可读冗余与时段稳定性

**定义与假设 7.1（等重叠记录、独立擦除及指定保留动力学）。** 沿用定义1.1的复内积方向、假设1.2的有限密度矩阵、Born效应概率及有限Kraus操作。固定整数$n\ge2$，指定系统空间、正交分支基及其投影为
$$
\mathcal H_S=\mathbb C^n,\qquad |i\rangle\ (1\le i\le n),\qquad P_i=|i\rangle\langle i|.
$$
这些是可分别制备的标签，不把第2.8条中未经记录的路径展开项另当作互斥历史。若将这些标签嵌入某个$\mathcal H_L$，可选$n\le G_L$个构型基态；其张成空间是否在指定的$H_L$下不变，仍须另验。本章的动力学和记录结构是额外假设，不从CSA的整数读数、来源树或Z卷的规范化推出。

固定实数$0\le\mu<1$，令记录信号空间$\mathcal Q=\mathbb C^n$的标准基为$(f_i)_{i=1}^n$，$\mathbf1$为全一列向量，并取
$$
G_\mu=(1-\mu)I_n+\mu\mathbf1\mathbf1^\dagger,\qquad
e_i=G_\mu^{1/2}f_i.
$$
$G_\mu$在$\mathbf1$方向和其正交补上的特征值分别为$1+(n-1)\mu$与$1-\mu$，故它正定。这是定理3.1的指定Gram实现，满足
$$
\langle e_i,e_j\rangle=
\begin{cases}1,&i=j,\\ \mu,&i\ne j.\end{cases}
$$
每个记录单元另带正交擦除标志，记
$$
\mathcal E=\mathcal Q\oplus\mathbb C|\bot\rangle,\qquad
Q_i=|e_i\rangle\langle e_i|,\qquad Q_\bot=|\bot\rangle\langle\bot|.
$$
固定整数$m\ge1$及复振幅列向量$\alpha=(\alpha_1,\ldots,\alpha_n)^{\mathsf T}$，其中
$$
p_i=|\alpha_i|^2,\qquad \sum_{i=1}^n p_i=1.
$$
指定记录写入完成后的联合态为
$$
|\Psi_\alpha\rangle=\sum_{i=1}^n\alpha_i|i\rangle\otimes e_i^{\otimes m}.
$$
它因系统基正交而归一化。给定制备标签$i$后的记录是乘积$e_i^{\otimes m}$；一般联合态并不自动具有这个结构。

保留阶段不补写记录、不作纠错，也不施加系统与记录之间的反馈或再耦合。固定有限擦除率$\kappa\ge0$，其量纲为时间的倒数；对$\tau\ge0$规定
$$
\eta(\tau)=e^{-\kappa\tau},\qquad
\mathcal N_\tau(X)=\eta(\tau)X+[1-\eta(\tau)]\operatorname{tr}(X)Q_\bot.
$$
这是$\mathcal E$上的完全正保迹通道：对$\mathcal E$的任一正交基$(a_j)_{j=1}^{n+1}$，取
$$
K_*=\sqrt{\eta(\tau)}I_{\mathcal E},\qquad
K_j=\sqrt{1-\eta(\tau)}|\bot\rangle\langle a_j|.
$$
它们满足$K_*^\dagger K_*+\sum_jK_j^\dagger K_j=I_{\mathcal E}$，其Kraus和恰为$\mathcal N_\tau$。替换映射$X\mapsto\operatorname{tr}(X)Q_\bot$幂等，故$\mathcal N_{\tau+\sigma}=\mathcal N_\tau\circ\mathcal N_\sigma$。

系统使用时间无关的自伴Hamiltonian $H$，并沿用$\hbar>0$。定义
$$
H_{\mathrm d}=\sum_i\langle i|H|i\rangle P_i,\qquad
V=H-H_{\mathrm d},\qquad U_H(\tau)=e^{-i\tau H/\hbar},\qquad
\theta(\tau)=\frac{\tau\|V\|}{\hbar}.
$$
$\theta(\tau)$是无量纲偏差预算。不同记录单元独立擦除，联合保留通道为
$$
\mathcal T_\tau=\operatorname{Ad}_{U_H(\tau)}\otimes\mathcal N_\tau^{\otimes m},\qquad
\operatorname{Ad}_U(X)=UXU^\dagger.
$$
对$J\subseteq\{1,\ldots,m\}$，记$a=|J|$，$J^c$为记录单元中的补集，定义
$$
\varrho_{SJ}(\tau)=\operatorname{tr}_{J^c}\mathcal T_\tau(|\Psi_\alpha\rangle\langle\Psi_\alpha|),\qquad
\sigma_i(\tau)=\eta(\tau)Q_i+[1-\eta(\tau)]Q_\bot,
$$
$$
\omega_{SJ}(\tau)=\sum_i p_iP_i\otimes\sigma_i(\tau)^{\otimes a},\qquad
D(\varrho,\sigma)=\frac12\|\varrho-\sigma\|_1,\qquad
\|X\|_1=\operatorname{tr}\sqrt{X^\dagger X}.
$$
空张量积使用一维空间，空乘积为一；特别约定$\mu^0=1$，包括$\mu=0$。其他概率幂的零次幂也按空积处理。

$\omega_{SJ}(\tau)$在系统标签上是经典混合，但不同标签的条件记录态未必具有正交支撑。R. Horodecki、J. K. Korbicz、P. Horodecki，*Quantum origins of objectivity*，Physical Review A **91**, 032122（2015），[DOI: 10.1103/PhysRevA.91.032122](https://doi.org/10.1103/PhysRevA.91.032122)，[arXiv:1312.6588](https://arxiv.org/abs/1312.6588)，所讨论的谱广播结构要求各片段对不同标签具有正交支撑。本章在$\mu>0$或存在共同擦除分量时一般不满足此要求，故使用明确的迹距离和解码错误率，不把$\omega_{SJ}$直接称为精确谱广播态。

片段读出允许在该片段内部实施任意有限POVM，不借用其他片段，也不作跨片段联合量子操作；全擦除事件计入错误率，不作后选择。时段保证指在给定区间任选一个时刻读出，不声称连续反复测量同一片段而无额外扰动。$m$只计每个维数为$n+1$的记录单元，不计擦除通道外部的酉扩张载体；通道中的擦除不表示信息从整个封闭世界消失。以下结论均限于这些数学假设，不构成实验验证或Lean形式验证的声明。

**定理 7.2（可见补集控制的精确相干误差与Hamiltonian稳定界）。** 定义
$$
c(p)=\frac12\left\|\alpha\alpha^\dagger-\operatorname{diag}(p_1,\ldots,p_n)\right\|_1.
$$
此值只依赖$p$，满足$0\le c(p)\le1$；等权$p_i=1/n$时，$c(p)=1-1/n$。在定义与假设7.1下，若$V=0$，则对每个$J$和每个$\tau\ge0$，
$$
D(\varrho_{SJ}(\tau),\omega_{SJ}(\tau))
=c(p)\mu^{m-a}\bigl[\eta(\tau)+(1-\eta(\tau))\mu\bigr]^a.
$$
一般$H$下有
$$
D(\varrho_{SJ}(\tau),\omega_{SJ}(\tau))
\le\min\left\{1,\ c(p)\mu^{m-a}\bigl[\eta(\tau)+(1-\eta(\tau))\mu\bigr]^a+\theta(\tau)\right\}.
$$
特别地，$V=0$且只看系统时，
$$
D\left(\varrho_S(\tau),\sum_i p_iP_i\right)=c(p)\mu^m;
$$
记录擦除不改变这个系统约化态的误差。此外，对单独制备的任一系统分支$P_i$，
$$
1-\operatorname{tr}\bigl(P_iU_H(\tau)P_iU_H(\tau)^\dagger\bigr)
\le\min\{1,\theta(\tau)^2\}.
$$

证明。 先说明所用迹范数事实。Hermitian矩阵$X$的正负谱分解为$X=X_+-X_-$；若$\operatorname{tr}X=0$，则
$$
\operatorname{tr}X_+=\operatorname{tr}X_-=\frac12\|X\|_1.
$$
因此任一效应$0\le M\le I$满足$|\operatorname{tr}(MX)|\le\|X\|_1/2$。对正且保迹的映射$\Phi$，三角不等式给出
$$
\|\Phi(X)\|_1\le\|\Phi(X_+)\|_1+\|\Phi(X_-)\|_1
=\operatorname{tr}X_++\operatorname{tr}X_-=\|X\|_1.
$$
故通道及部分迹不增大密度矩阵间的迹距离。迹范数在酉共轭下不变，在正交直和上相加；这两条由有限奇异值分解直接得到。迹距离与效应概率差的标准背景见 John Watrous，*The Theory of Quantum Information*，Cambridge University Press，2018，[DOI: 10.1017/9781316848142](https://doi.org/10.1017/9781316848142)，[作者公开版本](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，§3.1；本证明已写出实际需要的不等式。

在$\alpha_i\ne0$时写$\alpha_i=\sqrt{p_i}e^{i\phi_i}$，在零坐标任取$\phi_i=0$。以相位对角酉共轭可将$\alpha$变为$(\sqrt{p_i})_i$，而不改变$\operatorname{diag}(p)$，所以$c(p)$与相位无关。两个矩阵都是密度矩阵，三角不等式给$c(p)\le1$。等权时，差矩阵在$\alpha$方向的特征值为$1-1/n$，在其正交补上为$-1/n$，取迹范数即得$c(p)=1-1/n$。

现在令$V=0$。直接使用定理3.2的部分迹公式：系统外积$|x\rangle\langle y|$对应的被丢弃记录因子是$\langle e_y,e_x\rangle$，当$x\ne y$时为$\mu$。方向仍是先$e_y$、后$e_x$，没有转置该约定。对可见记录上的擦除项，同样有
$$
\mathcal N_\tau(|e_x\rangle\langle e_y|)
=\eta(\tau)|e_x\rangle\langle e_y|
+[1-\eta(\tau)]\langle e_y,e_x\rangle Q_\bot.
$$
对$J^c$施加保迹记录通道后再取部分迹，与直接丢弃$J^c$相同，故其中$m-a$个单元各贡献一个非对角因子$\mu$。

擦除标志将可见输出分成互相正交的模式。固定幸存集合$A\subseteq J$，令$k=|A|$，其权重为
$$
w_A=\eta(\tau)^k[1-\eta(\tau)]^{a-k}.
$$
该权重与标签无关。删除本模式中固定的擦除标志后，参考块为$w_A\Omega_A$，实际块为
$$
w_A\left[(1-\mu^{m-k})\Omega_A+\mu^{m-k}|\phi_A(\tau)\rangle\langle\phi_A(\tau)|\right],
$$
其中
$$
\Omega_A=\sum_i p_i|i,e_i^{\otimes k}\rangle\langle i,e_i^{\otimes k}|,\qquad
|\phi_A(\tau)\rangle=\sum_i\alpha_i e^{-i\tau\langle i|H|i\rangle/\hbar}|i,e_i^{\otimes k}\rangle.
$$
确实，$m-a$个不可见单元与$a-k$个可见但已擦除单元各给非对角项一个$\mu$，合计为$\mu^{m-k}$；对角项保持原权重。这是块的未归一化恒等式，即使$w_A=0$也成立，不需要对零概率事件作条件化。

因为系统标签正交，$(|i,e_i^{\otimes k}\rangle)_i$是一组正交单位向量。相位对角酉不改变迹范数，故该块差的半迹范数为$w_Ac(p)\mu^{m-k}$。在正交模式上相加，得到
$$
\begin{aligned}
D(\varrho_{SJ}(\tau),\omega_{SJ}(\tau))
&=c(p)\sum_{k=0}^a\binom ak\eta(\tau)^k[1-\eta(\tau)]^{a-k}\mu^{m-k}\\
&=c(p)\mu^{m-a}\bigl[\eta(\tau)+(1-\eta(\tau))\mu\bigr]^a.
\end{aligned}
$$
最后一步是非负整数次幂的二项式恒等式，不使用除以$\mu$，所以覆盖$\mu=0$。取$a=0$便得到系统单独观察的等式。

对一般$H$，对$U_H(\tau-s)U_{H_{\mathrm d}}(s)$求导并从零积分到$\tau$，得到Duhamel公式
$$
U_H(\tau)-U_{H_{\mathrm d}}(\tau)
=-\frac{i}{\hbar}\int_0^\tau U_H(\tau-s)VU_{H_{\mathrm d}}(s)\,ds.
$$
两边取算子范数，利用两个传播算子酉，得
$$
\|U_H(\tau)-U_{H_{\mathrm d}}(\tau)\|\le\frac{\tau\|V\|}{\hbar}=\theta(\tau).
$$
若$U,W$酉而$R$为任意密度矩阵，则
$$
URU^\dagger-WRW^\dagger=(U-W)RU^\dagger+WR(U^\dagger-W^\dagger).
$$
将$R$作谱分解，并使用$\||u\rangle\langle v|\|_1=\|u\|\|v\|$，右边两项的迹范数各不超过$\|U-W\|$，从而
$$
D(URU^\dagger,WRW^\dagger)\le\|U-W\|.
$$
此论证也适用于$U\otimes I$、$W\otimes I$及带任意有限辅助系统的$R$，因为张量恒等不改变算子范数。将同一记录通道应用后的联合态用于该不等式，再取部分迹，并与$H_{\mathrm d}$情形作三角比较，得一般上界；另有密度矩阵迹距离至多一。

最后，$U_{H_{\mathrm d}}(\tau)|i\rangle$只改变相位，所以
$$
(I-P_i)U_H(\tau)|i\rangle
=(I-P_i)\bigl(U_H(\tau)-U_{H_{\mathrm d}}(\tau)\bigr)|i\rangle.
$$
其范数平方正是离开标签$i$的概率，至多$\theta(\tau)^2$，也至多一，证明最后一式。证毕。

本条的擦除通道可同时降低可见联合态的残余相干和记录的可读性；丢失记录不等于恢复系统干涉。两种误差须由不同任务分别衡量。

**定理 7.3（独立擦除下对称片段的精确最坏分支判别误差）。** 固定片段大小$s\ge1$。它在制备标签$i$下的条件态及最优最坏分支错误率为
$$
\xi_i^{(s)}(\tau)=\sigma_i(\tau)^{\otimes s},\qquad
\mathsf E_{n,s}(\tau)=
\min_{\substack{M_i\ge0\ (1\le i\le n)\\\sum_iM_i=I_{\mathcal E^{\otimes s}}}}
\max_{1\le i\le n}\left[1-\operatorname{tr}\bigl(M_i\xi_i^{(s)}(\tau)\bigr)\right].
$$
这里对全部$n$个标签逐个保证，包含实际$p_i=0$的标签，不利用$(p_i)$的偏置降低平均错误率。对$0\le x\le1$，定义
$$
q_n(x)=\frac{\sqrt{1+(n-1)x}+(n-1)\sqrt{1-x}}{n},\qquad
\epsilon_n(x)=1-q_n(x)^2.
$$
则精确错误率为
$$
\mathsf E_{n,s}(\tau)=\sum_{k=0}^s\binom sk\eta(\tau)^k[1-\eta(\tau)]^{s-k}\epsilon_n(\mu^k).
$$
存在一个仅依赖$n,\mu,s$的固定POVM，在全部时刻、每个标签上均达到此同一错误率。它不依赖$(p_i)$或擦除模式的概率，且不删除全擦除事件。端点满足
$$
q_n(0)=1,\quad\epsilon_n(0)=0,\qquad
q_n(1)=\frac1{\sqrt n},\quad\epsilon_n(1)=1-\frac1n.
$$
特别地，$k=0$项使用$\mu^0=1$。有上下界
$$
\left(1-\frac1n\right)[1-\eta(\tau)]^s
\le\mathsf E_{n,s}(\tau)
\le\min\left\{1-\frac1n,\ (n-1)\bigl[1-\eta(\tau)(1-\mu^2)\bigr]^s\right\}.
$$
$\mathsf E_{n,s}(\tau)$随$\tau$不减，随整数$s$不增。无擦除时它等于$\epsilon_n(\mu^s)$；$\mu=0$时恰等于$(1-1/n)[1-\eta(\tau)]^s$；形式上的全擦除端点$\eta=0$给$1-1/n$，也是$\kappa>0$时的无穷时间极限。

证明。 先处理固定$k$个幸存单元，令$v_i=e_i^{\otimes k}$、$x=\mu^k$。当$k=0$时，所有$v_i$都是同一个一维单位向量。这些向量的Gram矩阵均为
$$
G_x=(1-x)I_n+x\mathbf1\mathbf1^\dagger.
$$
令$A$为以$v_i$为列的矩阵，$T=AA^\dagger$，$\mathcal K=\operatorname{span}\{v_i:1\le i\le n\}$，$\Pi_{\mathcal K}$为相应正交投影。$T$的负次幂只在正谱上定义，在核上取零。置
$$
|m_i\rangle=T^{-1/2}v_i,\qquad
M_i^{(k)}=|m_i\rangle\langle m_i|+\frac1n(I-\Pi_{\mathcal K}).
$$
由于
$$
\sum_i|m_i\rangle\langle m_i|=T^{-1/2}TT^{-1/2}=\Pi_{\mathcal K},
$$
这些效应非负且和为恒等。对$A$作奇异值分解，正奇异值上的逐项乘法给出
$$
A^\dagger T^{-1/2}A=\sqrt{A^\dagger A}=\sqrt{G_x}.
$$
$\sqrt{G_x}$的全部对角元相同，值为$q_n(x)$，故
$$
\langle v_i,M_i^{(k)}v_i\rangle
=|\langle m_i,v_i\rangle|^2=q_n(x)^2
$$
对每个$i$成立。

为证明最优性，对任意向量$z$，因$v_i\in\mathcal K$，Cauchy–Schwarz不等式给
$$
\begin{aligned}
|\langle v_i,z\rangle|^2
&=|\langle T^{-1/4}v_i,T^{1/4}z\rangle|^2\\
&\le\langle v_i,T^{-1/2}v_i\rangle\langle z,T^{1/2}z\rangle
=q_n(x)\langle z,T^{1/2}z\rangle.
\end{aligned}
$$
因此$|v_i\rangle\langle v_i|\le q_n(x)T^{1/2}$。任意POVM $(N_i)_i$的等权平均正确率满足
$$
\frac1n\sum_i\langle v_i,N_iv_i\rangle
\le\frac{q_n(x)}n\operatorname{tr}T^{1/2}
=q_n(x)^2,
$$
其中最后一步使用$T$和$G_x$有相同的非零谱，故$\operatorname{tr}T^{1/2}=\operatorname{tr}\sqrt{G_x}=nq_n(x)$。最小分支正确率不超过等权平均正确率，而所构造测量使全部分支都达到这个上界。因此最优最坏分支错误率恰为$\epsilon_n(x)$。本论证允许$G_x$秩亏：$x=1$时$T=n|v\rangle\langle v|$，各效应在$\mathcal K$上都是$\Pi_{\mathcal K}/n$，加上补空间后恰为$I/n$。$x=0$时向量正交，正确率为一，两个端点由此直接成立。

该谱计算属于平方根测量的成熟方法。相关方法与几何均匀态族的最优性见 Yonina C. Eldar、G. David Forney Jr.，*On Quantum Detection and the Square-Root Measurement*，IEEE Transactions on Information Theory **47**, 858–872（2001），[arXiv:quant-ph/0005132v2，§8、定理4](https://arxiv.org/abs/quant-ph/0005132v2)。这里的等重叠Gram矩阵在标签循环置换下不变，因此其向量族可由相应酉循环作用生成；上面的直接证明还给出本任务所需的逐标签最坏情形结论，不以文献中的平均正确率代替它。

回到$s$个可能擦除的单元。先读取每个位置在$\mathcal Q$还是在$\mathbb C|\bot\rangle$，再在幸存位置实施$M_i^{(k)}$；全擦除时均匀随机输出一个标签。这两步合起来是原片段上的一个有限POVM。不同模式互相正交，且模式权重$\eta(\tau)^k[1-\eta(\tau)]^{s-k}$与标签无关。任意POVM在模式之间的非对角块都不贡献条件态上的概率，其在每个模式的压缩仍是完整POVM。于是逐块的等权平均正确率受上面已证界约束；而所构造的逐块测量在每一标签同时达到该界。将全部模式相加，就得到精确有限和及整体的最坏分支最优性。模式测量与各$M_i^{(k)}$均不使用$\eta$，所以同一个POVM适用于全部时刻。

还需证明误差上界。$\sqrt{G_x}$的非对角元均为
$$
d_n(x)=\frac{\sqrt{1+(n-1)x}-\sqrt{1-x}}{n}.
$$
由$G_x$的对角元为一，$q_n(x)^2+(n-1)d_n(x)^2=1$，故
$$
\epsilon_n(x)=\frac{n-1}{n^2}\bigl(\sqrt{1+(n-1)x}-\sqrt{1-x}\bigr)^2
=\frac{(n-1)x^2}{\bigl(\sqrt{1+(n-1)x}+\sqrt{1-x}\bigr)^2}
\le(n-1)x^2.
$$
分母至少为一，且端点处不为零。代入模式和并用二项式定理，得到
$$
\mathsf E_{n,s}(\tau)\le(n-1)\bigl[(1-\eta(\tau))+\eta(\tau)\mu^2\bigr]^s.
$$
总可用均匀随机猜测得到错误率$1-1/n$，这给出上界的另一项。全擦除模式的概率为$[1-\eta(\tau)]^s$，其最优错误率为$1-1/n$，仅保留此非负项就得下界。

较晚时刻的条件态可以由较早时刻的条件态再施加独立擦除通道得到，故晚时刻的任一测量都能拉回成早时刻的允许POVM，最优错误率不能随时间下降。多一个单元时总可忽略它而实施原测量，所以最优错误率不随$s$增加。最后，$\eta=1$时只有$k=s$项；$\mu=0$时全部$k\ge1$项为零；$\eta=0$时只有$k=0$项。有限和的连续性再给出所列极限。证毕。

**定理 7.4（指定任务的精确最小记录数与一般动力学的充分预算）。** 固定定义与假设7.1中的$n,\mu,\alpha,\kappa,H$，有限保留时长$\tau_*\ge0$及整数$R\ge2$。将$m$个记录单元分成两两不交、非空的可访问片段$F_1,\ldots,F_R$及不访问的补集$B$，记
$$
F=\bigcup_{r=1}^R F_r,\qquad b=|B|,\qquad s_r=|F_r|\ge1,\qquad m=b+\sum_{r=1}^R s_r.
$$
划分在整个保留区间内固定。

先设$V=0$，给定$0<\delta<1$和$0<\beta<1-1/n$。精确最小值所针对的任务是：对同一初态$|\Psi_\alpha\rangle$，每个$\tau\in[0,\tau_*]$均满足
$$
D(\varrho_{SF}(\tau),\omega_{SF}(\tau))\le\delta,
$$
并且每个片段各有一个只作用于自身、与$\tau$无关的固定POVM，对每个单独制备标签$i\in\{1,\ldots,n\}$的错误率均至多$\beta$。此任务只允许选择记录总数、划分和这些POVM，记录质量$\mu$及写入、保留模型保持上述指定值。令
$$
b_\delta=\min\{b\in\mathbb Z_{\ge0}:c(p)\mu^b\le\delta\},\qquad
s_\beta=\min\{s\in\mathbb Z_{\ge1}:\mathsf E_{n,s}(\tau_*)\le\beta\}.
$$
这两个整数均有限，且该任务的精确最小单元总数为
$$
m_{\min}=b_\delta+R s_\beta.
$$
其中$0<\mu<1$时
$$
b_\delta=
\begin{cases}
0,&c(p)\le\delta,\\
\left\lceil\dfrac{\log(c(p)/\delta)}{\log(1/\mu)}\right\rceil,&c(p)>\delta,
\end{cases}
$$
而$\mu=0$时直接取$b_\delta=0$或$1$，分别对应$c(p)\le\delta$或$c(p)>\delta$。

再允许一般$H$。各片段使用定理7.3的固定解码器，系统使用末端投影测量$(P_i)_i$，输出分别记为$Z_1,\ldots,Z_R$及$Z_S$。在$\varrho_{SF}(\tau)$上同时实施这些不同因子的测量，则
$$
\Pr[Z_S=Z_1=\cdots=Z_R]
\ge\prod_{r=1}^R[1-\mathsf E_{n,s_r}(\tau)]-\theta(\tau).
$$
$V=0$时，上式为等式。这里片段仍解码初始制备标签；系统输出则是读出时刻的当前标签。

给定总态误差目标$\delta\in(0,1)$及同时读出失败目标$\varepsilon\in(0,1)$，假设
$$
\theta_*:=\frac{\tau_*\|V\|}{\hbar}<\min\{\delta,\varepsilon\},\qquad
\eta_*=e^{-\kappa\tau_*},\qquad \gamma_\delta=\delta-\theta_*,\quad
\gamma_\varepsilon=\varepsilon-\theta_*.
$$
当$0<\mu<1$时，令$r_*=1-\eta_*(1-\mu^2)\in(0,1)$，并取
$$
b_{\mathrm{suff}}=
\begin{cases}
0,&c(p)\le\gamma_\delta,\\
\left\lceil\dfrac{\log(c(p)/\gamma_\delta)}{\log(1/\mu)}\right\rceil,&c(p)>\gamma_\delta,
\end{cases}
\qquad
s_{\mathrm{suff}}=\max\left\{1,\left\lceil
\frac{\log\bigl(R(n-1)/\gamma_\varepsilon\bigr)}{\log(1/r_*)}
\right\rceil\right\}.
$$
当$\mu=0$时，不使用$\log(1/\mu)$，而分别定义
$$
b_{\mathrm{suff}}=
\begin{cases}0,&c(p)\le\gamma_\delta,\\1,&c(p)>\gamma_\delta,
\end{cases}
\qquad
s_{\mathrm{suff}}=
\begin{cases}
1,&\eta_*=1,\\
\max\left\{1,\left\lceil\dfrac{\log\bigl(R(1-1/n)/\gamma_\varepsilon\bigr)}{\log(1/(1-\eta_*))}\right\rceil\right\},&0<\eta_*<1.
\end{cases}
$$
有限$\kappa,\tau_*$保证$\eta_*>0$，所以这些情形穷尽所需端点。保留
$$
m_{\mathrm{suff}}=b_{\mathrm{suff}}+R s_{\mathrm{suff}}
$$
个单元，取补集大小$b_{\mathrm{suff}}$、各片段大小$s_{\mathrm{suff}}$，则对所有$\tau\in[0,\tau_*]$同时保证
$$
D(\varrho_{SF}(\tau),\omega_{SF}(\tau))\le\delta,\qquad
\Pr[Z_S=Z_1=\cdots=Z_R]\ge1-\varepsilon.
$$
任一单独制备分支的系统标签离开概率还至多为$\min\{1,\theta_*^2\}$。一般$H$的$m_{\mathrm{suff}}$只是上述两个目标的充分预算，不宣称最优；不满足$\theta_*<\min\{\delta,\varepsilon\}$时，这个充分判据不作保证，也不据此断言任务不可能。

证明。 先证明$V=0$的精确结论。定理7.2应用于$J=F$给出
$$
D(\varrho_{SF}(\tau),\omega_{SF}(\tau))
=c(p)\mu^b\bigl[\eta(\tau)+(1-\eta(\tau))\mu\bigr]^{m-b}.
$$
方括号在零时刻为一，以后不增，故全时段的态误差要求恰等价于$c(p)\mu^b\le\delta$，也即$b\ge b_\delta$。$c(p)=0$时$b_\delta=0$；$c(p)>0$且$0<\mu<1$时，几何衰减保证可达，取对数给出所列整数值；$\mu=0$时由$\mu^0=1$及$\mu^b=0$（$b\ge1$）直接得到二分情形。

第$r$个片段在$\tau_*$的任何POVM，其最坏分支错误率都不小于$\mathsf E_{n,s_r}(\tau_*)$。因而任务要求迫使$s_r\ge s_\beta$，从而$m\ge b_\delta+R s_\beta$。反过来，取$b=b_\delta$且每个$s_r=s_\beta$。定理7.3给出同一个对全部时刻适用的解码器，且错误率以$\tau_*$为最大，因此达到全部条件。$s_\beta$确实存在：有限$\tau_*$下
$$
0\le 1-e^{-\kappa\tau_*}(1-\mu^2)<1,
$$
定理7.3的几何上界随$s$趋于零；底数为零时一个单元即可零错误。故所求下界与可达上界相同。随$s$不增的性质还说明所有$s\ge s_\beta$都可用。

现证明同时读出的概率。先设$V=0$，并令$M_i^{(r)}$为第$r$个解码器的第$i$个效应。“全部输出相同”对应效应
$$
M_{\mathrm{eq}}=\sum_{i=1}^n P_i\otimes\bigotimes_{r=1}^R M_i^{(r)},\qquad
0\le M_{\mathrm{eq}}\le I.
$$
系统投影$P_i$消去不同系统标签间的交叉项；给定这一测量标签后，各片段条件态为乘积$\bigotimes_r\sigma_i(\tau)^{\otimes s_r}$。各解码器对每个$i$都有相同正确率$1-\mathsf E_{n,s_r}(\tau)$，所以
$$
\begin{aligned}
\operatorname{tr}\bigl(M_{\mathrm{eq}}\varrho_{SF}(\tau)\bigr)
&=\sum_i p_i\prod_{r=1}^R\operatorname{tr}\bigl(M_i^{(r)}\sigma_i(\tau)^{\otimes s_r}\bigr)\\
&=\prod_{r=1}^R[1-\mathsf E_{n,s_r}(\tau)].
\end{aligned}
$$
这是指定联合测量的概率计算，不预设已经选定一个全局隐藏结果。对一般$H$，定理7.2证明中的Duhamel比较给实际可见态与$H_{\mathrm d}$比较态的迹距离至多$\theta(\tau)$。效应概率差至多此迹距离，于是得到一般下界。无需再加退相干误差项，因为比较模型中的$M_{\mathrm{eq}}$本身已在系统标签上对角。

最后验证充分预算。$b_{\mathrm{suff}}$的各分支定义均保证
$$
c(p)\mu^{b_{\mathrm{suff}}}\le\gamma_\delta.
$$
在$[0,\tau_*]$上，定理7.2的方括号至多一，且$\theta(\tau)\le\theta_*$，因此态误差至多$\gamma_\delta+\theta_*=\delta$。

当$0<\mu<1$时，由定理7.3及$r(\tau)=1-\eta(\tau)(1-\mu^2)\le r_*$，所选$s_{\mathrm{suff}}$保证
$$
\mathsf E_{n,s_{\mathrm{suff}}}(\tau)
\le(n-1)r_*^{s_{\mathrm{suff}}}\le\frac{\gamma_\varepsilon}{R}.
$$
当$\mu=0$时，使用精确错误率$(1-1/n)[1-\eta(\tau)]^s$；若$\eta_*=1$，一个单元足够，否则所列对数取整同样保证该错误率至多$\gamma_\varepsilon/R$。所有这些对数分母均严格为正。对$0\le x_r\le1$，归纳使用$(1-x)(1-y)\ge1-x-y$可得
$$
\prod_{r=1}^R(1-x_r)\ge1-\sum_{r=1}^R x_r.
$$
代入同时读出下界，其失败概率至多$R(\gamma_\varepsilon/R)+\theta_*=\varepsilon$。标签离开概率由定理7.2直接得到。证毕。

例如$V=0,\mu=0,\kappa=0$时，$s_\beta=1$；若$\delta<c(p)$，则$b_\delta=1$、$m_{\min}=R+1$，否则$m_{\min}=R$。这里的精确性只针对上述固定模型及任务，不是脱离记录质量、访问划分、容许误差和保留动力学的普适经典性阈值。

**定理 7.5（片段容量下界、擦除下界与有限保留寿命）。** 对任意$d$维片段及其$n$个条件密度矩阵$\rho_i$，若某POVM $(M_i)_{i=1}^n$对每个标签的正确率均至少为$1-\beta$，其中$0\le\beta<1$，则
$$
d\ge\lceil n(1-\beta)\rceil.
$$
在定义与假设7.1的独立擦除模型中，若$0<\beta<1-1/n$且$0<\eta(\tau_*)<1$，则$\mathsf E_{n,s}(\tau_*)\le\beta$的必要条件为
$$
s\ge\left\lceil
\frac{\log\bigl((1-1/n)/\beta\bigr)}{\log\bigl(1/(1-\eta(\tau_*))\bigr)}
\right\rceil.
$$
等价地，固定有限$s\ge1$且$\kappa>0$时，任何满足$\mathsf E_{n,s}(\tau)\le\beta$的时刻必有
$$
\tau\le\frac1\kappa\log\left(
\frac1{1-\bigl(\beta/(1-1/n)\bigr)^{1/s}}
\right).
$$
这是必要的寿命上界，不保证在界内一定达到目标。在本章不补写、不纠错的模型中，若$\kappa>0$，任意固定有限片段均不能对全部时间维持严格优于无信息猜测的统一错误率；更精确地，固定$s$时$\mathsf E_{n,s}(\tau)\to1-1/n$。$\kappa=0$时没有由擦除给出的有限寿命结论，且该全时间不可能性陈述不适用。

证明。 密度矩阵的非负特征值之和为一，故$0\le\rho_i\le I$。对每个非负效应$M_i$，$\operatorname{tr}(M_i\rho_i)\le\operatorname{tr}M_i$，于是
$$
n(1-\beta)\le\sum_i\operatorname{tr}(M_i\rho_i)
\le\sum_i\operatorname{tr}M_i=\operatorname{tr}I=d.
$$
$d$为整数，给出容量下界。这是对每个标签均需正确读取的结论；若仅要求某个偏置先验的平均正确率，不能直接沿用左端。

定理7.3的全擦除项给出必要条件
$$
\beta\ge\left(1-\frac1n\right)[1-\eta(\tau_*)]^s.
$$
因为$0<1-\eta(\tau_*)<1$，取对数时$\log(1-\eta(\tau_*))<0$，除以它须反向不等号，整理并取整数上整即得$s$的下界。再令
$$
a_\beta=\left(\frac{\beta}{1-1/n}\right)^{1/s}\in(0,1).
$$
同一必要条件等价于$1-e^{-\kappa\tau}\le a_\beta$，也即$e^{-\kappa\tau}\ge1-a_\beta$，从而得到所列$\tau$上界。其右端有限，所以任何固定有限$s$都不能保持全时间保证。$\tau=0$时必要条件自然成立，无需对$1-\eta(0)=0$取对数；$\kappa=0$时该底数对全部时间均为零，故上述有限寿命推导不适用。证毕。

容量与冗余还须分开计量。对任意$m\ge1$，整个环境分支族$(e_i^{\otimes m})_i$的Gram矩阵为$G_{\mu^m}$，其秩仍为$n$。直接应用定理3.1，这个整体向量族可以在$n$维空间中实现，保持全部分支内积；但这个整体压缩没有保留指定的$R$个可独立访问张量片段及各自读出操作。因此最小Gram实现维数不等于定理7.4所定义的最小冗余记录预算，单说环境维数大也不能替代片段读出的任务条件。

**命题 7.6（无关重复、局部退相干、时间稳定与唯一全局结果的四个反边界）。** 以下均取二分支标签$0,1$，并使用归一化态。第一个构造取消记录质量条件，第二个取消给定标签后的乘积记录条件；它们说明这些假设不可省。后两个构造在正交乘积记录模型内分别检验系统动力学和全局态的边界。

（一）任意多份无关记录不保证退相干或可读性。对任意$m\ge1$及任意单位环境向量$e$，取
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|\Psi\rangle=|+\rangle\otimes e^{\otimes m}.
$$
两标签的环境条件态完全相同；这是重叠为一的反例，位于7.1的$\mu<1$假设之外。系统约化态为$|+\rangle\langle+|$，其与$I_2/2$之差在$(|0\rangle,|1\rangle)$基中是
$$
\frac12\begin{pmatrix}0&1\\1&0\end{pmatrix},
$$
特征值为$1/2,-1/2$，故迹距离恰为$1/2$。对任意环境二输出POVM，两标签产生同一输出分布$(r_0,r_1)$，且$r_0+r_1=1$；较小的标签正确率至多$1/2$，均匀猜测可达。因此即便联合读取整个环境，最优最坏分支错误率仍为$1/2$，增加$m$不改变这两个结论。

（二）精确的系统退相干不保证任何真片段可读。对$m\ge2$个环境二能级单元，取归一化GHZ记录
$$
|e_\pm\rangle=\frac{|0\rangle^{\otimes m}\pm|1\rangle^{\otimes m}}{\sqrt2},\qquad
|\Psi\rangle=\frac{|0\rangle_S\otimes|e_+\rangle+|1\rangle_S\otimes|e_-\rangle}{\sqrt2}.
$$
两个记录单位向量正交，所以由定理3.2，系统约化态精确为$I_2/2$。但对任何非空真片段$J\subsetneq\{1,\ldots,m\}$，令$j=|J|$，有
$$
\operatorname{tr}_{J^c}|e_+\rangle\langle e_+|
=\operatorname{tr}_{J^c}|e_-\rangle\langle e_-|
=\frac12\left(
|0\rangle^{\otimes j}\langle0|^{\otimes j}
+|1\rangle^{\otimes j}\langle1|^{\otimes j}\right).
$$
这是因为$J^c$非空，交叉项的部分迹包含$\langle1,0\rangle=0$。两个条件态相同，重复（一）的POVM论证便知任何这样的片段均只能达到最坏错误率$1/2$。整个环境却可用正交投影区分$e_+$与$e_-$，错误率为零。这些环境条件态不具有7.1的单元乘积结构；反例的不可读结论只针对真片段，不针对整个环境。

（三）完美冗余不自动保护当前系统标签。取$\mu=0$、$\kappa=0$及任意多份正交记录，记录向量为$e_0=|0\rangle$、$e_1=|1\rangle$；擦除标志空间可保留但不占据。给定$\tau_*>0$，令
$$
X=|0\rangle\langle1|+|1\rangle\langle0|,\qquad
H=\frac{\pi\hbar}{2\tau_*}X.
$$
由于$X^2=I_2$，指数级数给
$$
U_H(\tau_*)=\cos(\pi/2)I_2-i\sin(\pi/2)X=-iX.
$$
对任一初始制备标签$i$，系统在$\tau_*$必在$1-i$，每份未擦除记录仍完美保存$i$。等权相干初态在该时刻具体为
$$
-\frac{i}{\sqrt2}\left(
|1\rangle_S|0\rangle^{\otimes m}+|0\rangle_S|1\rangle^{\otimes m}
\right).
$$
因而对任意$R$个非空不交片段，使用读取原标签的完美记录测量和系统当前标签测量，有
$$
\Pr[Z_S=Z_1=\cdots=Z_R]=0.
$$
这个结论固定了解码器的标签语义；它不禁止知道翻转时刻后人为重标记输出。此处$H_{\mathrm d}=0$且$\theta(\tau_*)=\pi/2$，所以不满足7.4的小扰动充分条件。增加记录数没有减小这个Hamiltonian偏差，也没有保护当前标签。

（四）退相干、可读冗余与时段稳定同时完美成立，仍不推出唯一全局结果。取$H=0$、$\kappa=0$、$\mu=0$、整数$R\ge2$及$m=R+1$，令全局态为
$$
|\Psi_+\rangle=\frac{
|0\rangle_S|0\rangle^{\otimes m}+|1\rangle_S|1\rangle^{\otimes m}
}{\sqrt2}.
$$
将一个环境单元留在不访问的$B$中，每个可访问片段各含一个单元。取$F=\bigcup_rF_r$，则在全部时间上
$$
\varrho_{SF}=\omega_{SF}
=\frac12\sum_{i=0}^1P_i\otimes|i\rangle^{\otimes R}\langle i|^{\otimes R}.
$$
确实，对$B$取部分迹使两个全局分支的交叉项为零；$H=0$且无擦除使此态不随时间变化。每片段用计算基测量可零错误读取标签，且与系统末端标签全部一致。因此可见联合态的误差、片段错误率及同时读出失败率都为零，单独制备的系统标签也从不离开。

但是包含$B$的全局态仍是上述纯态，区别于非相干全局混合
$$
\Xi=\frac12|0\rangle^{\otimes(m+1)}\langle0|^{\otimes(m+1)}
+\frac12|1\rangle^{\otimes(m+1)}\langle1|^{\otimes(m+1)}.
$$
在系统及全部$m$个记录单元上定义Hermitian算符
$$
W=|0\rangle^{\otimes(m+1)}\langle1|^{\otimes(m+1)}
+|1\rangle^{\otimes(m+1)}\langle0|^{\otimes(m+1)}.
$$
它交换两个全局分支，在其正交补上为零，故$\|W\|=1$，且直接计算得
$$
\langle\Psi_+|W|\Psi_+\rangle=1,\qquad\operatorname{tr}(\Xi W)=0.
$$
所以两个全局密度矩阵不同；例如效应$(I+W)/2$也能给出不同概率。此见证涉及包括$B$在内的全局相干操作，不属于本章限定的片段局部读出。可见约化态与混合完全相同，并不使包含不可见补集的全局纯态变成混合，更没有从保留通道中产生选择一个全局分支的附加规则。

四个构造分别证明：单元数量不能替代记录质量；系统局部退相干不能替代真片段的可读性；历史记录的冗余不能替代当前系统标签的动力学稳定；这些操作性条件全部成立也不构成唯一全局结果定理。证毕。

上述结论只给出指定有限模型中的误差、预算与反例，不给出普适经典性阈值，不作实验或Lean验证声明，也不声称解决唯一结果问题。Gram实现及一般部分迹直接使用第3章，平方根测量和谱广播结构的思想归属于所引文献；本章没有将第6章的后选择成功率当作保留记录的无条件可读率。

## 追加锚（本行以下为增补区）

## 8. 新鲜环境的有限时间合成与相干衰减

**定义与假设 8.1（固定标签、新鲜时间因子与一般复记录）。** 设$\mathcal I$为非空有限标签集，$n=|\mathcal I|$，$\mathcal H_S=\mathbb C^{\mathcal I}$带固定相位的正交基$(|i\rangle)_{i\in\mathcal I}$。记$P_i=|i\rangle\langle i|$、$E_{ij}=|i\rangle\langle j|$。输入为任意密度矩阵$\varrho=\sum_{i,j}\varrho_{ij}E_{ij}$，允许混态、零布居及秩亏。内积首变量共轭线性；本章专用的记录矩阵取乘子方向
$$
G_t(i,j)=\langle e_j^{(t)},e_i^{(t)}\rangle.
$$
它是第3.1条通常Gram矩阵的转置，不能把两种下标方向混用。

固定有限整数$N\ge0$及时间指标集$T=\{1,\ldots,N\}$。每个$t$有非零有限维环境$\mathcal E_t$、预备单位向量$|0_t\rangle$及单位记录向量$|e_i^{(t)}\rangle$。初态严格为
$$
\varrho\otimes\bigotimes_{t\in T}|0_t\rangle\langle0_t|.
$$
因此各未用环境不仅有指定边缘态，而且与系统、旧记录及其他未用因子均无初始关联。第$t$步只作用于$\mathcal H_S\otimes\mathcal E_t$，在其预备子空间上满足受控非破坏条件
$$
U_t(|i\rangle\otimes|0_t\rangle)
=e^{i\theta_{i,t}}|i\rangle\otimes|e_i^{(t)}\rangle,
\qquad \theta_{i,t}\in\mathbb R.
$$
这里$U_t$可取酉算符；若只给出该子空间上的等距映射，也只使用它在该子空间上的值。右边的向量因系统标签正交而两两正交，故任何这样的指定都能通过补齐正交基延拓成同一有限空间上的酉算符。无须假定同一时刻的记录正交、线性无关、等重叠或实重叠。

各步按$t$递增执行；已用环境不再与系统或其他环境相互作用，不复用、不回注，不按中间测量结果选择后续操作，不作后选择。除了上述各步，没有混合标签的系统演化；若另有保持每个$P_i$的系统酉演化，其对角相位已经计入$\theta_{i,t}$。本章的保留记录在末端读取前不经历额外噪声。所谓丢弃是无条件部分迹，不是选择一次测量结果；在这些无反馈条件下，丢弃可以在该因子使用后立即进行，也可以推迟到末端。

对任意$A\subseteq T$，令
$$
\Theta_i(A)=\sum_{t\in A}\theta_{i,t},\qquad
|e_i^A\rangle=\bigotimes_{t\in A}|e_i^{(t)}\rangle,\qquad
\Gamma_A(i,j)=\prod_{t\in A}G_t(i,j).
$$
张量因子始终按时间递增排列。空和为零，空积为一，空张量空间为$\mathbb C$且$|e_i^\varnothing\rangle=1$；因而$\Gamma_\varnothing$是全部元素为一的矩阵，不是单位矩阵。取$N=0$时只剩恒等系统演化。阶段的重叠和相位可以逐时刻、逐标签变化，全部陈述只涉及这个有限时间集合。

对时间单元取迹，指对$\mathcal E_t$这个环境记录因子取迹；没有把抽象时间本身当作Hilbert空间，也没有把同一个系统在不同时刻的状态当作独立张量因子。

**定理 8.2（任意保留时间集合的精确部分迹）。** 设$A\subseteq T$为实际执行的时间集合，$R\subseteq A$为末端保留集合，$D=A\setminus R$为丢弃集合。未执行的时间步连同其预备因子省略。输出的系统与保留记录联合态恰为
$$
\varrho_{SR}^{A}
=\sum_{i,j\in\mathcal I}\varrho_{ij}
e^{i[\Theta_i(A)-\Theta_j(A)]}\Gamma_D(i,j)
E_{ij}\otimes|e_i^R\rangle\langle e_j^R|.
$$
此式对不连续的$R,D$同样成立，不要求它们是时间区间。定义
$$
C_{A;D}(i,j)=e^{i[\Theta_i(A)-\Theta_j(A)]}\Gamma_D(i,j),
\qquad J_R|i\rangle=|i\rangle\otimes|e_i^R\rangle,
$$
则$J_R^\dagger J_R=I_S$，并且
$$
\varrho_{SR}^{A}=J_R(C_{A;D}\odot\varrho)J_R^\dagger.
$$
这里$\odot$表示逐元素乘法。若进一步把$R$也丢弃，系统态为
$$
\Phi_A(\varrho)=C_A\odot\varrho,\qquad
C_A=C_{A;A},\qquad
C_A(i,j)=e^{i[\Theta_i(A)-\Theta_j(A)]}\Gamma_A(i,j).
$$
只迹掉$D$时的联合态不能直接称为系统通道$\Phi_D(\varrho)$：它还含$R$的算符张量，且相位来自全部已执行步骤$A$。若实际只执行$D$并丢弃其全部环境，才得到相位为$\Theta(D)$的$\Phi_D$。

证明。 对单个矩阵元，预备子空间上的指定给出
$$
U_t(E_{ij}\otimes|0_t\rangle\langle0_t|)U_t^\dagger
=e^{i(\theta_{i,t}-\theta_{j,t})}E_{ij}
\otimes|e_i^{(t)}\rangle\langle e_j^{(t)}|.
$$
由于后一步只触及系统及其新鲜因子，归纳得到整个$A$上的输出
$$
\sum_{i,j}\varrho_{ij}e^{i[\Theta_i(A)-\Theta_j(A)]}
E_{ij}\otimes\bigotimes_{t\in A}|e_i^{(t)}\rangle\langle e_j^{(t)}|.
$$
对任意单位向量$u,v$及任意正交基$(a_k)_k$，
$$
\operatorname{tr}|u\rangle\langle v|
=\sum_k\langle a_k,u\rangle\langle v,a_k\rangle
=\langle v,u\rangle.
$$
逐因子取迹，恰得到$\prod_{t\in D}\langle e_j^{(t)},e_i^{(t)}\rangle$；保留因子的秩一算符按定义合成$|e_i^R\rangle\langle e_j^R|$。这证明第一式，也核定了内积方向。归一化及系统标签正交给
$$
\langle i\otimes e_i^R,j\otimes e_j^R\rangle=\delta_{ij},
$$
故$J_R$是等距映射，矩阵元展开即得第二式。再迹掉$R$乘上$\Gamma_R$，由$R\cap D=\varnothing$得$\Gamma_D\odot\Gamma_R=\Gamma_A$。后续操作不触及已弃因子，所以其部分迹与后续操作可交换；这也证明即时丢弃与末端丢弃等价。$D=\varnothing$时没有衰减乘子，$R=\varnothing$时$J_R$自然等同于系统恒等映射，全部公式仍成立。证毕。

**定理 8.3（复Gram乘子的完全正性与秩亏边界）。** 对任意复矩阵$C\in\mathbb C^{\mathcal I\times\mathcal I}$，映射$M_C(X)=C\odot X$完全正且保持迹，当且仅当$C$为Hermitian正半定矩阵并满足$C(i,i)=1$。此时$M_C$也保持恒等算符。定义8.1中的$G_t,\Gamma_D,C_{A;D}$都满足这些矩阵条件；特别地，$\Phi_A$是完全正且保持迹的通道。完全正性无需任何Gram矩阵可逆。

证明。 先设$C\ge0$且对角元为一。有限谱分解给出$C=BB^\dagger$；只保留正特征值即可，允许$B$为$n\times r$矩阵，其中$r=\operatorname{rank}C$。令
$$
K_a=\sum_{i\in\mathcal I}B_{ia}P_i\quad(1\le a\le r).
$$
直接比较矩阵元得到
$$
\sum_aK_aXK_a^\dagger=C\odot X,\qquad
\sum_aK_a^\dagger K_a=\sum_i C(i,i)P_i=I_S.
$$
任意有限辅助空间上的扩张同样是$(K_a\otimes I)$的共轭和，因此保持非负；这就是完全正性。第二个等式给保持迹。又$C\odot I_S=I_S$，故保持恒等算符。

反之，令$|\Omega\rangle=\sum_i|i\rangle\otimes|i\rangle$。若$M_C$完全正，则
$$
(M_C\otimes\operatorname{id})(|\Omega\rangle\langle\Omega|)
=\sum_{i,j}C(i,j)|ii\rangle\langle jj|\ge0.
$$
将此算符沿等距嵌入$|i\rangle\mapsto|ii\rangle$压缩，得到$C\ge0$。保持迹应用于$P_i$给$C(i,i)=1$。这同时证明了必要性。

最后核对记录矩阵。固定每个环境的一组正交基，将$e_i^{(t)}$的坐标写为$a_{i\alpha}^{(t)}$，则
$$
G_t(i,j)=\sum_\alpha a_{i\alpha}^{(t)}\overline{a_{j\alpha}^{(t)}}.
$$
因此$G_t=B_tB_t^\dagger\ge0$，其对角元为一。若$C(i,j)=\sum_a b_{ia}\overline{b_{ja}}$、$F(i,j)=\sum_b d_{ib}\overline{d_{jb}}$，则
$$
(C\odot F)(i,j)=\sum_{a,b}(b_{ia}d_{ib})\overline{(b_{ja}d_{jb})},
$$
所以正半定矩阵的逐元素乘积仍正半定。重复使用这个Gram证明即得$\Gamma_D\ge0$；空积对应所有标签取同一个标量向量$1$。令$z_i=e^{i\Theta_i(A)}$，则
$$
C_{A;D}=\operatorname{diag}(z)\Gamma_D\operatorname{diag}(z)^\dagger,
$$
故正半定性与单位对角均保持。此处不对零特征值取逆，重复记录与线性相关记录全部允许。证毕。

这一判据是有限维Schur乘子的标准结论，见 John Watrous，*The Theory of Quantum Information*（2018），[第4.1.3节，命题4.17、4.18，印刷页219、220](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。上述证明将其直接写成Kraus分解及最大纠缠向量的压缩；相应完全正映射表示的对应见同书定理2.22。

**定理 8.4（时间合成、指针代数及完整不动空间）。** 对互不相交的时间集合$A,B\subseteq T$，每步均满足定义8.1且输入环境保持新鲜，则
$$
\Gamma_{A\cup B}=\Gamma_A\odot\Gamma_B,\qquad
C_{A\cup B}=C_A\odot C_B,\qquad
\Phi_{A\cup B}=\Phi_B\circ\Phi_A=\Phi_A\circ\Phi_B.
$$
这里交换的是指定记录通道；不宣称$U_s,U_t$在任意非预备的环境输入上可交换。相交集合若仍用上式复合，会把交集步骤计算两次，只能解释为另备独立副本后再次执行，不能解释为原时间集合的并。

定义指针代数$\mathcal D=\{\sum_i a_iP_i:a_i\in\mathbb C\}$。每个$E_{ij}$是$\Phi_A$的特征算符，且
$$
\Phi_A(E_{ij})=C_A(i,j)E_{ij},\qquad
\Phi_A|_{\mathcal D}=\operatorname{id}_{\mathcal D},\qquad
\operatorname{Fix}(\Phi_A)=\operatorname{span}\{E_{ij}:C_A(i,j)=1\}.
$$
对偶通道在$E_{ij}$上的特征值为$\overline{C_A(i,j)}$，因此同样逐点固定$\mathcal D$；系统的指针布居和全部对角观察均保持。仅有$|C_A(i,j)|=1$不保证$E_{ij}$固定，还须总相位使$C_A(i,j)=1$。

更精确地，令$w_i=e^{i\Theta_i(A)}e_i^A$。关系$i\sim_Aj$定义为$C_A(i,j)=1$，等价于$w_i=w_j$，故是等价关系。不动空间是各等价类上的完整矩阵代数的直和。它恰为$\mathcal D$的充要条件是每个$i\ne j$都有$C_A(i,j)\ne1$；一个充分条件是每个异标签对至少有一步$t\in A$满足$|G_t(i,j)|<1$。

证明。 不交集合上的有限和与有限积分别相加、相乘，给出前两式；逐元素乘法的结合律和交换律给出通道复合式。对特征算符的结论直接来自$C_A\odot E_{ij}=C_A(i,j)E_{ij}$。矩阵元构成一组线性无关的基，故固定一个矩阵当且仅当其在$C_A(i,j)\ne1$的位置为零。Kraus分解中的$K_a$都对角；将共轭次序反向即得对偶的共轭特征值。

按既定内积方向，$C_A(i,j)=\langle w_j,w_i\rangle$且$\|w_i\|=1$。若其值为一，则
$$
\|w_i-w_j\|^2=2-2\operatorname{Re}\langle w_j,w_i\rangle=0.
$$
反向蕴含显然。因而等价类内的矩阵元全部固定，类间全部不固定，得到直和描述。Cauchy–Schwarz给$|G_t(i,j)|\le1$；若其中一个严格小于一，则$|C_A(i,j)|<1$，不可能等于一。空时间集合时所有$w_i=1$，不动代数为整个$\operatorname{End}(\mathcal H_S)$，与恒等通道相符。证毕。

相位的分拆本身不是额外物理数据。若改取$e_i^{(t)}\mapsto e^{i\chi_{i,t}}e_i^{(t)}$并同时令$\theta_{i,t}\mapsto\theta_{i,t}-\chi_{i,t}$，预备子空间上的$U_t$不变，$C_A$及定理8.2的联合态亦不变。这个结论由每步的相位因子相消直接得到；对部分保留情形，剩余的$R$相位恰与$|e_i^R\rangle\langle e_j^R|$的相位相消。因此不能先忽略复重叠的相位，再用其模判定不动点。

**定理 8.5（一般混态的精确相干距离与有限时间预算）。** 令$\Delta(X)=\sum_iP_iXP_i$，$p_i=\varrho_{ii}$。在定理8.2的划分下，取比较态
$$
\omega_{SR}^{A}=\sum_i p_iP_i\otimes|e_i^R\rangle\langle e_i^R|.
$$
它具有相同的指针布居和每个单独制备标签的保留记录。记迹距离为$\mathsf d(\sigma,\tau)=\frac12\|\sigma-\tau\|_1$，并定义
$$
L_D=\Gamma_D\odot(\varrho-\Delta(\varrho)),\qquad
Q_D=\sum_{i\ne j}|\varrho_{ij}|^2\prod_{t\in D}|G_t(i,j)|^2.
$$
则有精确公式及上下界
$$
\mathsf d(\varrho_{SR}^{A},\omega_{SR}^{A})=\frac12\|L_D\|_1,
$$
$$
\frac12\sqrt{Q_D}
\le\mathsf d(\varrho_{SR}^{A},\omega_{SR}^{A})
\le\min\left\{\frac{\sqrt n}{2}\sqrt{Q_D},\,
\frac12\sum_{i\ne j}|\varrho_{ij}|\prod_{t\in D}|G_t(i,j)|\right\}.
$$
新增环境对这个距离的作用取决于访问划分：追加并保留新记录不改变原$D$对应的距离；追加并丢弃新记录使此距离不增。完整丢弃后的各矩阵元满足
$$
|\Phi_A(\varrho)_{ij}|=|\varrho_{ij}|\prod_{t\in A}|G_t(i,j)|.
$$
因此在新鲜、固定标签且无反馈的有限序列内，各异标签相干的模不增；其复值仍可因相位旋转而改变。

若$D$含$k$个时刻，且有给定$q\in(0,1)$使这些时刻的每个异标签对均满足$|G_t(i,j)|\le q$，令
$$
\mathcal C_1(\varrho)=\sum_{i\ne j}|\varrho_{ij}|,
$$
则
$$
\mathsf d(\varrho_{SR}^{A},\omega_{SR}^{A})
\le\frac12\mathcal C_1(\varrho)q^k.
$$
对指定容许误差$\delta>0$，若$\mathcal C_1(\varrho)>2\delta$，一个充分的丢弃时间样本数为
$$
k\ge\left\lceil\frac{\log(\mathcal C_1(\varrho)/(2\delta))}{\log(1/q)}\right\rceil;
$$
若$\mathcal C_1(\varrho)\le2\delta$，$k=0$已经满足这个上界。样本数必须不超过可用有限时间数，且所选各步必须实际满足该重叠界；不存在所需步骤时此充分判据不作保证。$q=0$时一个满足全体异标签零重叠的丢弃步骤足以使距离为零；$q=1$只给不增性，不能据它推出衰减。上述预算针对给定初态、误差、标签基与记录质量，不是普适经典性阈值。

证明。 设$Z_A=\sum_ie^{i\Theta_i(A)}P_i$。由定理8.2及$\Gamma_D(i,i)=1$，
$$
\varrho_{SR}^{A}-\omega_{SR}^{A}=J_R Z_A L_D Z_A^\dagger J_R^\dagger.
$$
酉共轭保持奇异值；等距嵌入$J_R$只在正交补上补零，也保持全部非零奇异值。因此得到精确迹范数式。注意记录$e_i^R$之间可以相同或线性相关；使$J_R$等距的是系统标签的正交性，不是记录的独立性。

$L_D$为Hermitian矩阵，且$\|L_D\|_2^2=Q_D$，其中$\|\cdot\|_2$为Hilbert–Schmidt范数。对其至多$n$个奇异值应用平方和与和之间的不等式，得到
$$
\|L_D\|_2\le\|L_D\|_1\le\sqrt n\|L_D\|_2.
$$
又因$\|E_{ij}\|_1=1$，逐项三角不等式给出另一上界。

若新增丢弃集合$B$与$D$不交，则$L_{D\cup B}=M_{\Gamma_B}(L_D)$。定理8.3说明此映射正且保持迹。对任意Hermitian矩阵$L=L_+-L_-$的正负谱分解，
$$
\|M_{\Gamma_B}(L)\|_1
\le\operatorname{tr}M_{\Gamma_B}(L_+)+\operatorname{tr}M_{\Gamma_B}(L_-)
=\operatorname{tr}L_++\operatorname{tr}L_-=\|L\|_1.
$$
这证明距离不增。若只增加保留步骤，$D$及$L_D$均不变，精确式给距离相同。逐矩阵元公式由$C_A$的模直接得到。将统一重叠界代入逐项上界得$q^k$，在$q\in(0,1)$时对正数取对数并除以正数$\log(1/q)$即得整数预算；零相干输入与两个$q$端点按原乘积处理，无须对零取对数。证毕。

对仅有$x,y$两个标签的系统，上述距离还有更强的精确形式：$L_D$是对角为零、非对角为$\varrho_{xy}\Gamma_D(x,y)$及其共轭的二阶矩阵，其特征值为$\pm|\varrho_{xy}\Gamma_D(x,y)|$，故
$$
\mathsf d(\varrho_{SR}^{A},\omega_{SR}^{A})
=|\varrho_{xy}|\prod_{t\in D}|G_t(x,y)|.
$$
若$\varrho_{xy}=0$，任意$D$的距离都为零；若其非零，有限时刻精确消相干当且仅当$D$中至少一个重叠为零。逐步重叠严格小于一但非零只给有限乘积缩小，不给有限步精确归零。

**定理 8.6（保留时间片段的两标签判别与精确最小样本数）。** 固定两个不同标签$x,y\in\mathcal I$及任意保留时间集合$R\subseteq T$。在分别制备系统标签$x$或$y$的任务中，片段条件态为
$$
\sigma_x^R=|e_x^R\rangle\langle e_x^R|,\qquad
\sigma_y^R=|e_y^R\rangle\langle e_y^R|,
\qquad s_R=|\Gamma_R(x,y)|=\prod_{t\in R}|G_t(x,y)|.
$$
条件态指指定标签制备的输出，不假设任意相干输入已经选中了某个隐藏标签。允许在$\bigotimes_{t\in R}\mathcal E_t$上实施任意联合二输出POVM；在此前不读出、不反馈。则
$$
\mathsf d(\sigma_x^R,\sigma_y^R)=\sqrt{1-s_R^2}.
$$
若两制备的先验为$\pi,1-\pi$，其中$0\le\pi\le1$，最小平均错误率为
$$
P_{\mathrm{err}}^{\pi}(R)
=\frac{1-\sqrt{1-4\pi(1-\pi)s_R^2}}2.
$$
特别地，等先验时$P_{\mathrm{err}}^{1/2}(R)=(1-\sqrt{1-s_R^2})/2$。任意先验的公式针对平均错误率；等先验的这个值还等于最优最坏标签错误率，记为$\beta_{xy}(R)$。这里仍允许联合测量，不保证先分别测量各个时间单元后还能达到相同最优值。

现固定等先验任务、可用有限时间集合$T$及目标$0<\beta<1/2$。可任意选择保留子集，每个时间样本成本均为一。令
$$
\ell_t=-\log|G_t(x,y)|^2\in[0,+\infty],\qquad
B_\beta=\log\frac1{4\beta(1-\beta)}>0,
$$
其中零重叠定义为$\ell_t=+\infty$。将这些权重按非增次序排成$\ell_{(1)}\ge\cdots\ge\ell_{(N)}$。则达到$P_{\mathrm{err}}^{1/2}(R)\le\beta$的精确最小样本数为
$$
k_{\min}=\min\left\{k\in\{0,\ldots,N\}:\sum_{a=1}^k\ell_{(a)}\ge B_\beta\right\},
$$
若右边集合为空，则在这组有限可用样本中不可达。若只能保留按时间到达的前缀，则把排序前缀换成原时间前缀，精确最早达到时刻为
$$
k_{\mathrm{first}}=\min\left\{k\in\{0,\ldots,N\}:\sum_{t=1}^k\ell_t\ge B_\beta\right\},
$$
并作同样的不可达约定。$\beta=0$时存在可达片段当且仅当某个可用重叠为零；$\beta\ge1/2$时空片段即可。$R=\varnothing$或$s_R=1$时两个条件态相同，最优错误率为$\min\{\pi,1-\pi\}$；$s_R=0$时可零错误区分。

若系统恰有$x,y$两个标签，还可以同时要求系统与保留记录的联合相干误差至多$\delta>0$，以及保留片段最坏标签错误率至多$0<\beta<1/2$。令$c=|\varrho_{xy}|$，并定义
$$
B_{\mathrm c}=\begin{cases}
0,&c\le\delta,\\
2\log(c/\delta),&c>\delta.
\end{cases}
$$
对任意已执行集合$A=D\mathbin{\dot\cup}R$，两个任务同时达标的充要条件恰为
$$
\sum_{t\in D}\ell_t\ge B_{\mathrm c},\qquad
\sum_{t\in R}\ell_t\ge B_\beta.
$$
因此在给定有限序列内，允许每次对已写入前缀选择访问划分时，精确最早可达轮数是
$$
\min\left\{k\in\{0,\ldots,N\}:\exists\,D\mathbin{\dot\cup}R=\{1,\ldots,k\},\quad
\sum_{t\in D}\ell_t\ge B_{\mathrm c},\quad
\sum_{t\in R}\ell_t\ge B_\beta\right\},
$$
集合为空仍表示在该有限序列内不可达。这是两个不交集合的分配条件，单有总和至少$B_{\mathrm c}+B_\beta$不充分。若任务只要求系统边缘态的相干误差，以及另行联合读取全部$A$的能力，则条件改为$\sum_{t\in A}\ell_t\ge\max\{B_{\mathrm c},B_\beta\}$；该任务没有要求系统与全部记录的联合态接近指针对角比较态。

证明。 先取$u=e_x^R,v=e_y^R$。更换$v$的整体相位不改变其投影，故可在计算谱时使$\langle u,v\rangle=s_R\ge0$。若$s_R<1$，在二者张成空间的一组正交基中可写
$$
u=\begin{pmatrix}1\\0\end{pmatrix},\qquad
v=\begin{pmatrix}s_R\\\sqrt{1-s_R^2}\end{pmatrix}.
$$
差$|u\rangle\langle u|-|v\rangle\langle v|$的迹为零、行列式为$-(1-s_R^2)$，故特征值为$\pm\sqrt{1-s_R^2}$，得到迹距离。$s_R=1$时两投影相同，此公式仍成立，不需要构造第二个基向量。

二输出测量写为$(M,I-M)$，其中$0\le M\le I$，$M$表示猜$x$。令
$$
H_\pi=\pi|u\rangle\langle u|-(1-\pi)|v\rangle\langle v|.
$$
正确率为$1-\pi+\operatorname{tr}(MH_\pi)$。在$H_\pi$的特征基中，每个$M$的对角元介于零与一，所以最大值由正谱投影达到，且
$$
\max_{0\le M\le I}\operatorname{tr}(MH_\pi)
=\operatorname{tr}(H_\pi)_+
=\frac{\|H_\pi\|_1+2\pi-1}{2}.
$$
在上述二阶表示中，$\operatorname{tr}H_\pi=2\pi-1$、$\det H_\pi=-\pi(1-\pi)(1-s_R^2)$。两个候选特征值为
$$
\lambda_\pm=\frac{2\pi-1\pm\sqrt{1-4\pi(1-\pi)s_R^2}}2.
$$
当$0<\pi<1$且$s_R<1$时它们一正一负，故其绝对值之和为根号项。$\pi=0,1$或$s_R=1$时直接计算秩一算符，仍得相同的迹范数公式。代入正确率的最优值即得所述错误率。这是二元量子判别的Helstrom公式在纯记录态上的具体谱计算；一般判别定理见 Watrous，*The Theory of Quantum Information*，[第3章，定理3.4](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。

为证明等先验值也是最坏标签最优值，仍令$\langle u,v\rangle=s_R$。当$s_R<1$时取
$$
u_+=\frac{u+v}{\sqrt{2(1+s_R)}},\qquad
u_-=\frac{u-v}{\sqrt{2(1-s_R)}},\qquad
m_x=\frac{u_++u_-}{\sqrt2},\qquad m_y=\frac{u_+-u_-}{\sqrt2}.
$$
这两组向量各自正交归一。以$m_x,m_y$的投影为两个效应，并将它们张成空间的正交补各分一半，得到完整POVM。由
$$
u=\sqrt{\frac{1+s_R}{2}}u_++\sqrt{\frac{1-s_R}{2}}u_-,\qquad
v=\sqrt{\frac{1+s_R}{2}}u_+-\sqrt{\frac{1-s_R}{2}}u_-
$$
可见两个标签的正确率同为$(1+\sqrt{1-s_R^2})/2$。最坏错误率总不小于等先验平均错误率，而该测量使两者同时达到已证的平均最优值，所以也达到最坏最优值。$s_R=1$时均匀猜测达到最坏错误率$1/2$。

对$0<\beta<1/2$，两边非负使平方变形合法，
$$
P_{\mathrm{err}}^{1/2}(R)\le\beta
\quad\Longleftrightarrow\quad
s_R^2\le4\beta(1-\beta)
\quad\Longleftrightarrow\quad
\sum_{t\in R}\ell_t\ge B_\beta.
$$
没有零重叠时最后一步是有限乘积的对数；有零重叠时两边都按上述扩展实数约定成立。任何$k$元子集的权重和不超过最大的$k$项之和，且选择这$k$项就达到该最大值。因此排序前缀第一次达到预算的位置既必要又充分；若所有权重总和仍不足，则任何片段都不可能达标。仅允许时间前缀时没有重排序自由，直接使用原顺序的累计和。两个误差端点和空片段由原错误率公式给出。

联合任务的相干距离由定理8.5精确等于$c\exp(-\frac12\sum_{t\in D}\ell_t)$。当$c\le\delta$时它自动达标，否则取对数给出$D$的预算；$R$的预算已经证明。对每个前缀的这组充要条件取最小值，就得到最早可达轮数。为核对总预算不充分，取$B_{\mathrm c}=B_\beta=1$，一轮重叠模为$e^{-1}$而其余轮重叠模均为一。唯一正权重为$2$，总和达到两预算之和，但这一个时间单元不能同时分配给$D$与$R$，所以任一划分都会有一个预算为零。最后，系统边缘任务及读取全部记录的任务都用$A$的同一个乘积，两下界合取就是它们的最大值。证毕。

在二标签系统且$\varrho_{xy}\ne0$时，同一时间集合$A$还有精确关系
$$
\left(\frac{\mathsf d(\Phi_A(\varrho),\Delta(\varrho))}{|\varrho_{xy}|}\right)^2
+\mathsf d(\sigma_x^A,\sigma_y^A)^2=1.
$$
这是定理8.5的二阶谱式与本定理的纯态距离式相加所得。它把“丢弃整个$A$后系统还剩多少相干”和“若保留整个$A$能区分多少制备信息”对应起来；同一实际访问划分中的两种乘积仍分别取$D$与$R$，不能把它们替换成同一个集合。

**定理 8.7（一般有限标签族的联合读取界与零误差覆盖）。** 设$n\ge2$，固定有限时间集合$A\subseteq T$，并允许联合读取整个$\bigotimes_{t\in A}\mathcal E_t$。定义
$$
q_A=\max_{i\ne j}|\Gamma_A(i,j)|,\qquad
\beta_A=\min_{\substack{M_i\ge0\\\sum_iM_i=I}}
\max_i\left[1-\langle e_i^A,M_ie_i^A\rangle\right].
$$
则最优最坏标签错误率满足
$$
\beta_A\ge\frac{1-\sqrt{1-q_A^2}}2.
$$
若$u_A=(n-1)q_A<1$，则还有
$$
\beta_A\le\min\left\{1-\frac1n,\left(1-\sqrt{1-u_A}\right)^2\right\}.
$$
这个一般非对称记录族的上界由一个具体测量达到不超过该值的错误率，不宣称该测量必为精确最优。相应系统通道满足有限界
$$
\frac{q_A}{2}\le\sup_{\varrho}\mathsf d(\Phi_A(\varrho),\Delta(\varrho))
\le\frac{n-1}{2}q_A,
$$
上确界取所有系统密度矩阵。因此对固定有限标签数，全部逐对重叠足够小会同时给出整个记录的联合可读性及系统边缘态的退相干界；不能在保留纯条件记录和完整联合访问的条件下把这两个结论任意割裂。

以下三个有限条件等价：$\Phi_A=\Delta$；全部标签可由$A$的记录零错误联合判别；每个异标签对$i,j$都存在$t\in A$使$G_t(i,j)=0$。若记
$$
\mathcal P_t=\{\{i,j\}:i\ne j,\ G_t(i,j)=0\},
$$
则它们等价于
$$
\bigcup_{t\in A}\mathcal P_t=\{\{i,j\}:i\ne j\}.
$$
这是对有限标签对的覆盖条件，不要求某一个时间单元单独区分全部标签。

证明。 有限维POVM的集合闭且有界，目标函数连续，所以定义中的最小值存在。任意$n$输出POVM若每个标签错误率均至多$b$，固定$i\ne j$，保持$i$输出而把其余输出统合为$j$，就得到对这两个标签错误率均至多$b$的二输出测量。定理8.6的最坏标签结论迫使$b\ge(1-\sqrt{1-|\Gamma_A(i,j)|^2})/2$。取重叠最大的标签对即得下界。

为构造上界，令$v_i=e_i^A$，$V$以$v_i$为列，并使用通常方向的Gram矩阵
$$
H=V^\dagger V,\qquad H(i,j)=\langle v_i,v_j\rangle=\Gamma_A(j,i).
$$
$H-I$的每行绝对值之和不超过$u_A$。对任一特征向量，选择绝对值最大的坐标代入特征方程，得到$|\lambda-1|\le u_A$。当$u_A<1$时所有特征值为正，可以定义
$$
m_i=VH^{-1/2}|i\rangle,\qquad
\Pi=VH^{-1}V^\dagger,\qquad
M_i=|m_i\rangle\langle m_i|+\frac1n(I-\Pi).
$$
由于$(VH^{-1/2})^\dagger(VH^{-1/2})=I$，$m_i$正交归一，$\Pi$是其张成空间的正交投影，所列效应非负且和为恒等。$v_i$位于这个空间，且$\langle m_i,v_i\rangle=(\sqrt H)_{ii}$。由$H(i,i)=1$，
$$
1-\langle v_i,M_iv_i\rangle
=1-(\sqrt H)_{ii}^2
=\sum_{j\ne i}|(\sqrt H)_{ji}|^2
\le\|\sqrt H-I\|^2.
$$
逐特征值有
$$
|\sqrt\lambda-1|=\frac{|\lambda-1|}{\sqrt\lambda+1}
\le\frac{u_A}{\sqrt{1-u_A}+1}=1-\sqrt{1-u_A}.
$$
这给出逐标签上界；均匀猜测另给$1-1/n$。若$u_A\ge1$，这里的逆矩阵构造不作保证，但下界、随机猜测界和其余有限结论仍有效。秩亏记录族并未被排除出整个定理，只是在$u_A<1$这个充分条件下其记录自动线性无关。

定理8.5给出系统距离不超过$\frac12q_A\sum_{i\ne j}|\varrho_{ij}|$。密度矩阵的二阶主子矩阵非负，故$|\varrho_{ij}|\le\sqrt{p_ip_j}$，从而
$$
\sum_{i\ne j}|\varrho_{ij}|
\le\left(\sum_i\sqrt{p_i}\right)^2-1\le n-1.
$$
最后一步使用$\sum_i p_i=1$和Cauchy–Schwarz不等式。反向取达到$q_A$的标签对$i,j$及初态$(|i\rangle+|j\rangle)/\sqrt2$，二阶谱计算给距离$q_A/2$，得到上确界的下界。

完整退相干等价于$C_A(i,j)=0$对每个$i\ne j$成立，相位非零使它等价于$\Gamma_A(i,j)=0$。有限乘积为零当且仅当至少一个因子为零，给出覆盖条件。若全部记录两两正交，投影测量可零错误区分，并可将未占据正交补任意分配给各效应；反之，零错误判别由已证二标签下界迫使所有重叠为零。故三个条件等价。$A=\varnothing$时$q_A=1$，所有条件记录相同，最优最坏错误率为$1-1/n$，完整退相干及零错误读取均不成立。$n=1$时无需取异标签最大值：通道本来就是恒等与$\Delta$，读取唯一标签的错误率为零，覆盖条件为空条件。证毕。

上界采用平方根测量方法，方法来源见第7.3条所引 Eldar 与 Forney（2001）。这里直接证明的是一般有限复Gram矩阵的逐标签充分界；第7.3条对单一实等重叠模型的精确最优性不被用于任意非对称族。

**命题 8.8（无条件取迹与实际记录测量的分界）。** 在定理8.2的$A=D\mathbin{\dot\cup}R$中，若在末端实际对$D$实施有限POVM $(B_a)_a$，再丢弃被测因子，结果$a$对应的未归一化系统与保留记录态为
$$
\widetilde\varrho_{SR}^{A,a}
=\sum_{i,j}\varrho_{ij}e^{i[\Theta_i(A)-\Theta_j(A)]}
\langle e_j^D,B_a e_i^D\rangle
E_{ij}\otimes|e_i^R\rangle\langle e_j^R|.
$$
结果概率以及正概率结果的条件指针布居分别为
$$
p(a)=\sum_i p_i\langle e_i^D,B_ae_i^D\rangle,\qquad
p(i\mid a)=\frac{p_i\langle e_i^D,B_ae_i^D\rangle}{p(a)}\quad(p(a)>0).
$$
忘记结果给出$\sum_a\widetilde\varrho_{SR}^{A,a}=\varrho_{SR}^{A}$。当$p(a)=0$时不定义归一化条件态。

证明。 将结果$a$的环境操作写成Kraus族$(L_{a\nu})_\nu$，满足$\sum_\nu L_{a\nu}^\dagger L_{a\nu}=B_a$。即使测量仪器使用额外输出空间，只要该输出随$D$一起丢弃，循环迹公式仍给
$$
\sum_\nu\operatorname{tr}\left(L_{a\nu}|e_i^D\rangle\langle e_j^D|L_{a\nu}^\dagger\right)
=\langle e_j^D,B_ae_i^D\rangle.
$$
将此式代入取迹前的全局矩阵元展开，即得未归一化态。再取系统与$R$的迹，系统标签正交消去$i\ne j$项，得到$p(a)$；$p(a)>0$时除以它即得条件布居。最后使用$\sum_aB_a=I$，逐项恢复定理8.2的$\Gamma_D$。证毕。

因此无条件布居保持与条件化后的布居改变并不矛盾。取部分迹本身不指定某个结果，也不要求已经实施一次测量；条件化是另一操作，本命题没有将其结果送入后续动力学作反馈。

**命题 8.9（非实秩亏记录与分布在不同时刻的标签信息）。** 本章允许不能通过各记录的相位重选而同时变实的Gram矩阵；即使总体记录已使全部异标签重叠为零，每个单独时间单元也不必能读出完整标签。

证明。 第一例取三个标签$0,1,2$，一个二能级环境及记录
$$
e_0=|0\rangle,\qquad e_1=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
e_2=\frac{|0\rangle+i|1\rangle}{\sqrt2}.
$$
按$G(i,j)=\langle e_j,e_i\rangle$，直接计算得
$$
G=\begin{pmatrix}
1&1/\sqrt2&1/\sqrt2\\
1/\sqrt2&1&(1-i)/2\\
1/\sqrt2&(1+i)/2&1
\end{pmatrix}.
$$
这三个记录张成二维空间，所以$G$正半定、单位对角且秩为二。各记录乘相位会使$G(i,j)$乘以$e^{i(\chi_i-\chi_j)}$，但循环乘积
$$
G(0,1)G(1,2)G(2,0)=\frac{1-i}{4}
$$
不变且非实，故不可能把所有元素同时变成实数。它仍完全满足定理8.3，无须压缩成单一实重叠参数。

第二例取四个标签$(a,b)\in\{0,1\}^2$、两个新鲜二能级时间因子、零阶段相位及记录
$$
e_{(a,b)}^{(1)}=|a\rangle,\qquad e_{(a,b)}^{(2)}=|b\rangle.
$$
它们可分别由标签控制的比特翻转在预备态$|0\rangle$上实现，系统标签保持不变。单步矩阵及时间乘积为
$$
G_1((a,b),(a',b'))=\delta_{aa'},\qquad
G_2((a,b),(a',b'))=\delta_{bb'},\qquad
\Gamma_{\{1,2\}}((a,b),(a',b'))=\delta_{aa'}\delta_{bb'}.
$$
因此完整丢弃两时间因子的通道恰为$\Delta$，而保留全部记录时四个记录$|a\rangle\otimes|b\rangle$正交，可零错误联合读出完整标签。

但是只读取第一时间单元时，$(a,0)$与$(a,1)$的条件态相同。对等先验四标签任务及任何四输出POVM $(M_{ab})_{a,b}$，平均正确率为
$$
\frac14\sum_{a=0}^1\langle a,(M_{a0}+M_{a1})a\rangle\le\frac12,
$$
因为每个$M_{a0}+M_{a1}\le I$。测出$a$后对$b$均匀猜测达到$1/2$。第二时间单元的结论对称成立。故所有异标签的总体重叠归零只保证整个记录空间中的可辨识性，不能把标签信息在时间之间的分布自动变成每个片段都完整可读的冗余。证毕。

**命题 8.10（相关环境、复用环境与非对角Hamiltonian的反例）。** 去掉新鲜乘积条件、一次使用条件或固定标签演化条件，定理8.4的时间乘积律与定理8.5的单调性均不再是一般保证。以下为三个有限维的具体构造。

证明。 （一）两个尚未与系统接触的环境单元也可以已有相关性。取两个二能级环境的初态
$$
|\Phi_+\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\qquad
|\Phi_-\rangle=\frac{|00\rangle-|11\rangle}{\sqrt2},
$$
系统初态为$|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$。令$Z=|0\rangle\langle0|-|1\rangle\langle1|$，第$t=1,2$步分别实施$P_0\otimes I+P_1\otimes Z_t$，各自只接触一次对应环境单元。第一步后全局态为
$$
\frac{|0\rangle|\Phi_+\rangle+|1\rangle|\Phi_-\rangle}{\sqrt2},
$$
因$\langle\Phi_-,\Phi_+\rangle=0$，系统态为$I_2/2$。第二步中$Z_2|\Phi_-\rangle=|\Phi_+\rangle$，于是全局态回到$|+\rangle|\Phi_+\rangle$，系统相干完全恢复。

这里每个环境边缘态为$I_2/2$，若把两个边缘误当作独立新鲜输入，各自的受控相位通道都会给相干乘子$\operatorname{tr}((I_2/2)Z)=0$，相乘仍为零。真实两步乘子却是
$$
\langle\Phi_+,(Z\otimes Z)\Phi_+\rangle=1,
$$
不等于两个单步边缘期望的乘积。第一步后各单环境在两个标签下的条件边缘态也都为$I_2/2$，信息在环境关联中；第二步仍访问携带该关联的另一因子。因此“每个单元只碰一次”不足以替代初始张量乘积假设。

（二）复用一个环境可以撤销先前写入。取单个预备为$|0\rangle_E$的二能级环境及
$$
X=|0\rangle\langle1|+|1\rangle\langle0|,\qquad
U=P_0\otimes I+P_1\otimes X.
$$
系统从$|+\rangle$出发。第一次作用给$(|00\rangle+|11\rangle)/\sqrt2$，系统约化态为$I_2/2$，预备输入上的记录重叠为零。但$U^2=I$，第二次作用于同一个环境后输出$|+\rangle|0\rangle_E$，系统态恢复为$|+\rangle\langle+|$。不能把第二次调用也按$U(|i\rangle|0\rangle)$的预备子空间公式处理：此时它的输入已与系统相关，且标签$1$分支的环境为$|1\rangle$。如果第一次就真正丢掉旧环境，第二步另备$|0\rangle$，系统态仍为$I_2/2$，不会得到上述恢复。

（三）允许混合标签的系统Hamiltonian时，可以从指针对角态重新生成该基中的相干。取$p\in(0,1)$且$p\ne1/2$，从正交记录态
$$
|\Psi\rangle=\sqrt p\,|0\rangle|0\rangle_E
+\sqrt{1-p}\,|1\rangle|1\rangle_E
$$
得到系统约化态$\varrho_0=\operatorname{diag}(p,1-p)$。令$\omega>0$且系统Hamiltonian为$H=\hbar\omega X/2$，环境此后完全不动。由$X^2=I$，
$$
V(\tau)=e^{-iH\tau/\hbar}
=\cos(\omega\tau/2)I-i\sin(\omega\tau/2)X.
$$
记$c=\cos(\omega\tau/2)$、$s=\sin(\omega\tau/2)$，则
$$
\varrho(\tau)=V(\tau)\varrho_0V(\tau)^\dagger
=\begin{pmatrix}
pc^2+(1-p)s^2&i(2p-1)cs\\
-i(2p-1)cs&ps^2+(1-p)c^2
\end{pmatrix}.
$$
因此
$$
\mathsf d(\varrho(\tau),\Delta(\varrho(\tau)))
=\frac{|2p-1|}{2}|\sin(\omega\tau)|.
$$
此距离从零增加到$\tau=\pi/(2\omega)$时的$|2p-1|/2>0$，以后又可回到零。它是给定指针基中的相干再生，并未恢复迹掉环境所失去的原始相位信息，也未把系统混态变成纯态。$p=1/2$时系统为最大混态，此Hamiltonian不能生成相干，所以该参数已明确排除。这里$H$不与$P_0,P_1$对易，正好违反定义8.1的固定标签动力学条件。

三个构造分别显示：跨时刻的初始环境关联可以破坏独立乘积律；与旧记录重新相互作用可以撤销记录；混合指针标签的系统动力学可以生成新的基相干。有限乘积定理的单调性依赖其明确的动力学假设，不能由记录数量单独推出。部分迹及最优判别只规定约化态和操作概率，不添加选择唯一全局分支的演化规则。证毕。

## 追加锚（本行以下为增补区）

**定义与假设 8.11（自由演化后的持续补写与固定标签 Schur 通道）。** 本节另建一个与定义8.1至命题8.10分开的模型。那些条款中的产品公式要求整个有限前缀始终由一个固定标签控制，并把每个新鲜记录写成同一初始标签的条件向量；本节允许自由Hamiltonian在相邻轮次之间混合标签，因此不能把新记录合并成依赖一个固定初始标签的单一张量积记录。

取有限指针集$\mathsf X$，$d=|\mathsf X|\ge2$，$\mathcal H_S=\mathbb C^{\mathsf X}$，$P_x=|x\rangle\langle x|$，以及$\Delta(A)=\sum_xP_xAP_x$。给定$\tau_*>0$和$N\ge1$，令
$$
h=\frac{\tau_*}{N},\qquad U(s)=\exp\!\left(-\frac{isH}{\hbar}\right),\qquad H_d=\sum_x\langle x|H|x\rangle P_x,\qquad V=H-H_d,
$$
并定义每一小段的无量纲扰动量和总时段扰动量
$$
a_*:=\frac{\tau_*\|V\|}{N\hbar}=\frac{h\|V\|}{\hbar},\qquad a:=Na_*=\frac{\tau_*\|V\|}{\hbar}.
$$
其中$a_*$是单个自由演化小段的局部扰动量，而$a=Na_*$是整个时段的总量。下文递推中的局部量始终使用$a_*$。

第$k$轮先施加$U(h)$，再把系统与一个全新的准备单元作固定标签的非破坏写入。该写入在系统边缘上是
$$
R_k=\operatorname{Ad}_{Z_k}\circ\Phi_k,\qquad \Phi_k(A)=\Gamma_k\odot A,\qquad \Gamma_k(x,y)=\gamma_k(x,y),
$$
其中$Z_k$为对角酉，$\Gamma_k$是由新鲜记录向量得到的正半定单位对角Gram矩阵，并且存在固定的$0\le r<1$使
$$
|\gamma_k(x,y)|\le r\qquad(k=1,\ldots,N,\ x\ne y).
$$
记录单元在写入后立即从系统边缘取迹，随后不再反馈；没有测量结果反馈，也没有旧记录的再耦合。这里把写入视为理想的离散通道，$\tau_*$只计入自由演化小段；结论不覆盖有限持续时间写入脉冲内部的动力学，也不保证当$h$缩小时能以固定强度、带宽或能量维持同一个$r$。若$\sigma_0$为初态，则写入时刻的递推是
$$
\sigma_k=R_k\!\left(U(h)\sigma_{k-1}U(h)^\dagger\right),\qquad k=1,\ldots,N.
$$
轮间任意时刻只由$U(s)$给出，$0\le s\le h$。这里的“补写”是每轮一个新鲜固定标签 Schur 通道，且记录随后被取迹；它不等同于前面固定标签产品模型的全程环境张量积。

**定理 8.12（持续弱记录的有限轮相干与人口漂移界）。** 沿用定义8.11。设初态为任意对角态$\sigma_0=\sum_xp_xP_x$。当$0<r<1$时定义
$$
\Lambda_{r,d}:=1+\frac{2\sqrt d\,r}{1-r}.
$$
对任意已完成的写入轮次以及任意轮间时刻$\tau\in[0,\tau_*]$，有
$$
\mathsf d(\sigma(\tau),\Delta(\sigma(\tau)))\le C_N:=\frac{\sqrt d\,a_*}{1-r}=\frac{\sqrt d\,a}{N(1-r)},
$$
以及
$$
\mathsf d(\Delta(\sigma(\tau)),\sigma_0)\le B_N:=N a_*^2\Lambda_{r,d}=\frac{a^2\Lambda_{r,d}}{N}.
$$
因而
$$
\mathsf d(\sigma(\tau),\sigma_0)\le C_N+B_N.
$$
若$\sigma_0=P_x$，则在任意这些时刻
$$
1-\operatorname{tr}(P_x\sigma(\tau))\le\min\{1,B_N\}.
$$
给定$\delta,\varepsilon>0$，下列有限轮预算是充分的：
$$
N\ge\max\left\{1,\left\lceil\frac{\sqrt d\,a}{\delta(1-r)}\right\rceil,\left\lceil\frac{a^2\Lambda_{r,d}}{\varepsilon}\right\rceil\right\}.
$$
这只是充分条件，不声称最优。$r=0$时每轮写入后的状态精确对角；同一Duhamel估计给出$C_N=\sqrt d\,a_*$和$B_N=Na_*^2=a^2/N$，而写入之间仍可有至多$\sqrt d\,a_*$的相干。若$V=0$，则$a_*=a=0$，两个预算均为零。若$r=1$，本定理的收缩预算发散，不能从“频繁”推出稳定性。

证明。 记$Q(A)=A-\Delta(A)$，并令$q_k=\|Q(\sigma_k)\|_2$。对$0\le s\le h$，Duhamel公式及$H=H_d+V$给出
$$
\left\|U(s)-\exp\!\left(-\frac{isH_d}{\hbar}\right)\right\|\le\frac{s\|V\|}{\hbar}\le a_*.
$$
对任意矩阵$A$，$\Delta$是Hilbert--Schmidt内积下的正交投影，且酉共轭保持Hilbert--Schmidt范数；因此
$$
\left\|Q\!\left(U(h)AU(h)^\dagger\right)\right\|_2
\le\|Q(A)\|_2+2a_*\|A\|_2.
$$
在本定理中$A$是密度矩阵，故$\|A\|_2\le1$。Schur写入只把每个非对角元乘以模不超过$r$的数，对角相位不改变范数，故
$$
q_k\le r(q_{k-1}+2a_*),\qquad q_0=0.
$$
若初态允许含有相干，则同一递推保留瞬态项
$$
q_k\le r^kq_0+\frac{2a_*r(1-r^k)}{1-r}.
$$
本定理的对角初态给出$q_0=0$，于是归纳得到
$$
q_k\le\frac{2a_*r(1-r^k)}{1-r}\le\frac{2a_*r}{1-r}.
$$
写入前的一段自由演化至多再增加$2a_*$，所以所有轮间时刻均满足
$$
\|Q(\sigma(\tau))\|_2\le\frac{2a_*}{1-r}.
$$
由于$|X|_1\le\sqrt d\,|X|_2$，并且迹距离带有因子$1/2$，得到$C_N=\sqrt d\,a_* /(1-r)$。

再估计人口。写$\sigma=D+O$，其中$D=\Delta(\sigma)$、$O=Q(\sigma)$。对角部分是指针投影的凸组合；由同一Duhamel估计，每个$P_x$在一个长度为$h$的自由段中离开自身标签的概率至多为$a_*^2$，从而
$$
\mathsf d\!\left(\Delta(U(h)DU(h)^\dagger),D\right)\le a_*^2.
$$
对$O$部分，因$\Delta(\exp(-ihH_d/\hbar)O\exp(ihH_d/\hbar))=0$，迹范数收缩性与两项展开给出
$$
\frac12\left\|\Delta(U(h)OU(h)^\dagger)\right\|_1
\le a_*\|O\|_1
\le\sqrt d\,a_*\|O\|_2.
$$
在第$k$轮之前用$q_{k-1}\le2a_*r/(1-r)$，人口每轮变化至多为
$$
a_*^2+\sqrt d\,a_*q_{k-1}\le a_*^2\left(1+\frac{2\sqrt d\,r}{1-r}\right)=a_*^2\Lambda_{r,d}.
$$
Schur写入本身保持人口；累加至多$N$轮得到$B_N$。轮间任意截断时刻只减少已计入的段数，故同一界成立。对角态与$P_x$的迹距离正好是$1-\operatorname{tr}(P_x\sigma)$，三角不等式给出总态界。最后把$C_N\le\delta$和$B_N\le\varepsilon$分别改写为所列整数条件。证毕。

若允许记录质量随$N$变化为$r_N<1$，同一证明给出$C_N\le\sqrt d\,a/[N(1-r_N)]$，以及$B_N\le a^2[1+2\sqrt d\,r_N/(1-r_N)]/N$。因此固定总扰动$a$时，充分的渐近条件是$N(1-r_N)\to+\infty$；仅增加轮数而不控制每轮记录强度没有同一保证。这个有限轮估计与Zeno或重复相互作用文献的主题相近；Ciccarello等人的重复碰撞综述以及Facchi--Pascazio关于Zeno子空间的论文只作背景引用，除非逐式核查，不能作为本定理常数的直接出处。

**推论 8.13（形成、保留记录与持续补写的联合预算）。** 设形成阶段结束时系统与旧记录$F$的实际态为$\rho_{SF}^{\mathrm{form}}$，给定
$$
\Omega_{SF}=\sum_xp_xP_x\otimes\xi_x^F,\qquad
\mathsf d(\rho_{SF}^{\mathrm{form}},\Omega_{SF})\le e_{\mathrm{form}}.
$$
在补写阶段旧记录$F$保持不变、不擦除、不再与系统耦合；只有新的记录单元按定义8.11作用，并在描述系统与旧记录时全部取迹。则定理8.12的任意保证时刻满足
$$
\mathsf d(\rho_{SF}(\tau),\Omega_{SF})
\le e_{\mathrm{form}}+C_N+B_N.
$$
若旧记录有一个固定POVM$(M_x)_x$，且对每个标签有$\operatorname{tr}(M_x\xi_x^F)\ge1-\beta$，则同时测量当前系统的$(P_x)_x$与旧记录的$(M_x)_x$，并令$Z_S,Z_F$为两个输出，有
$$
\Pr[Z_S=Z_F]\ge(1-\min\{1,B_N\})(1-\beta)-e_{\mathrm{form}}.
$$
这里新记录已被取迹，旧记录仍是同一固定解码对象；补写轮数不能替代旧记录的读取误差。若形成阶段本身是定义8.1的固定标签模型，可取$\xi_x^F=|e_x^F\rangle\langle e_x^F|$及$e_{\mathrm{form}}$为相应的形成相干距离。

证明。 令$\sigma_x(\tau)$为从$P_x$开始的补写动力学，并令
$$
\widetilde\Omega_{SF}(\tau)=\sum_xp_x\sigma_x(\tau)\otimes\xi_x^F.
$$
定理8.12给出每个$x$的$\mathsf d(\sigma_x(\tau),P_x)\le C_N+B_N$；张量乘上固定密度矩阵不增加迹距离，故
$$
\mathsf d(\widetilde\Omega_{SF}(\tau),\Omega_{SF})\le C_N+B_N.
$$
同一个完全正保迹的补写演化作用于实际态与形成参考态，初始距离至多保持$e_{\mathrm{form}}$，三角不等式即得第一式。

令一致输出事件对应的效应为
$$
M_{\mathrm{eq}}=\sum_yP_y\otimes M_y.
$$
在参考态上，其概率至少为
$$
\sum_xp_x\operatorname{tr}(P_x\sigma_x(\tau))\operatorname{tr}(M_x\xi_x^F)
\ge(1-\min\{1,B_N\})(1-\beta).
$$
实际态与参考态的效应概率相差至多$e_{\mathrm{form}}$，得到第二式。相干预算$C_N$仍由第一式控制，但一致输出事件只读取系统的对角人口，故下界中不需额外扣除$C_N$。证毕。

**定理 8.14（固定有限标签的有限前缀累积等价）。** 现在回到定义8.1的固定标签、新鲜时间因子模型。标签集$\mathsf X$固定且有限，令$d=|\mathsf X|\ge2$；取一列按$t\ge1$编号的新鲜记录，而所有陈述只在每个有限前缀$I_N=\{1,\ldots,N\}$上定义，不构造无限张量积态。这里$\gamma_t(x,y)=G_t(x,y)$沿用§8.1的单轮记录重叠，不引入定义8.11的统一$r<1$假设。令
$$
L_{xy}(N)=\sum_{t=1}^{N}-\log|\gamma_t(x,y)|,\qquad
q_N=\max_{x\ne y}\prod_{t=1}^{N}|\gamma_t(x,y)|,
$$
其中零重叠贡献$+\infty$，并定义全部有限前缀记录的最优最坏标签错误率
$$
\beta_N=\min_{\substack{M_x\ge0\\\sum_xM_x=I}}
\max_x\left[1-\langle e_x^{I_N},M_xe_x^{I_N}\rangle\right].
$$
以下四项等价：
$$
\left(\forall x\ne y,\ L_{xy}(N)\longrightarrow+\infty\right)
\Longleftrightarrow q_N\longrightarrow0
\Longleftrightarrow\sup_{\varrho}\mathsf d\!\left(\Phi_{I_N}(\varrho),\Delta(\varrho)\right)\longrightarrow0
\Longleftrightarrow\beta_N\longrightarrow0.
$$
对每个有限$N$，有有限标签的平方根测量界
$$
\frac{1-\sqrt{1-q_N^2}}2\le\beta_N,
$$
且当$u_N=(d-1)q_N<1$时
$$
\beta_N\le\min\left\{1-\frac1d,\left(1-\sqrt{1-u_N}\right)^2\right\}.
$$
同时
$$
\frac{q_N}{2}\le\sup_{\varrho}\mathsf d\!\left(\Phi_{I_N}(\varrho),\Delta(\varrho)\right)
\le\frac{d-1}{2}q_N.
$$
这些是有限前缀的陈述；极限只表示这些有限数列的极限，不表示存在一个无限时间的全局量子态。

证明。 因为标签对只有有限多个，$\prod_t|\gamma_t(x,y)|=\exp[-L_{xy}(N)]$，故第一项与第二项等价。定理8.5给出系统上界；反向取达到$q_N$的标签对$x,y$以及初态$(|x\rangle+|y\rangle)/\sqrt2$，二阶谱计算给出距离$q_N/2$，所以系统距离趋零也蕴含$q_N\to0$。

任意$d$输出POVM若所有标签错误率均不超过$b$，把所有非$x$输出合并为$y$，便得到对标签对$x,y$错误率均不超过$b$的二输出测量。定理8.6给出
$$
b\ge\frac{1-\sqrt{1-|\Gamma_{I_N}(x,y)|^2}}2.
$$
取最大重叠得到平方根下界。上界取记录向量为列的矩阵$V$，通常方向Gram矩阵$G=V^\dagger V$，令$u_N=(d-1)q_N$。当$u_N<1$时，Gershgorin型坐标估计给$1-u_N\le\lambda(G)\le1+u_N$。定义平方根测量
$$
m_x=VG^{-1/2}|x\rangle,\qquad M_x=|m_x\rangle\langle m_x|+\frac1d(I-\Pi),\qquad \Pi=VG^{-1}V^\dagger.
$$
它是POVM，且$\langle m_x,e_x^{I_N}\rangle=(\sqrt G)_{xx}$。因$G_{xx}=1$，逐标签错误率为
$$
1-((\sqrt G)_{xx})^2=\sum_{y\ne x}|(\sqrt G)_{yx}|^2\le\|\sqrt G-I\|^2\le(1-\sqrt{1-u_N})^2.
$$
随机猜测给出$1-1/d$。最后，定理8.5的上界为$(d-1)q_N/2$；下界仍由二标签初态达到。于是四项全等价。证毕。

这里的平方根测量上界沿用Eldar--Forney（2001）的有限维方法；Watrous关于Schur通道和二态判别的结果、以及重复相互作用和Zeno文献均只作为背景或已明确核查的基础，不把任何未经逐式核查的文献陈述写成这些有限前缀常数的来源。

**命题 8.15（访问集合、混态准备、联合相位与过弱补写的操作性反例）。** 下列构造都只涉及有限维、有限轮次，且不建立无限张量积状态。

（零）每轮都有严格辨识力仍不保证无限前缀完全退相干。取二标签并令每轮重叠模为$|\gamma_t(0,1)|=\exp(-2^{-t})$，则$L_{01}(N)=\sum_{t=1}^N2^{-t}=1-2^{-N}$，从而$|\Gamma_{I_N}(0,1)|=\exp(-(1-2^{-N}))\to e^{-1}>0$。对初态$|+\rangle\langle+|$，系统相干距离趋于$e^{-1}/2$，全部记录的最优最坏二标签错误率趋于$(1-\sqrt{1-e^{-2}})/2>0$。缺少的是发散的累积区分预算，而不是形式上的无限个时间单元。

（一）不可访问时间片与可读取时间片承担不同任务。取二标签，第一轮记录为$e_0^{(1)}=|0\rangle$、$e_1^{(1)}=|1\rangle$，其余轮次取同一个与标签无关的单位向量。令$D=\{1\}$、$F=\{2,\ldots,N\}$。则$\Gamma_D(0,1)=0$，而$|e_0^F\rangle=|e_1^F\rangle$。因此系统与可见记录已经精确达到由$D$控制的参考态，但在指定可读集合$F$上最优最坏错误率仍为$1/2$。若交换$D$与$F$，保留片段的可读性随之交换，而系统边缘仍由同一已执行的动力学决定；对有非零初始相干的输入，系统与新的可见片段的联合相干距离为$|\varrho_{01}|$，不能把“不可访问”自动算作“可读取”。

（二）混态环境可造成边缘退相干而不提供可读记录。每轮取环境输入$I_2/2$，并用
$$
U=P_0\otimes I+P_1\otimes Z,\qquad Z=|0\rangle\langle0|-|1\rangle\langle1|.
$$
系统非对角乘子是$\operatorname{tr}((I_2/2)Z)=0$，所以系统边缘完全退相干；但两个标签下的环境输出都仍为$I_2/2$，任何读取POVM都不能获得标签信息。这一构造故意不满足定义8.1的纯准备态假设，说明“边缘退相干”与“条件记录可读”不能无条件推广为同一命题。

（三）相同逐对重叠模不决定有限多标签联合判别误差。取三个标签、两轮、零阶段相位，并令
$$
G_+=\frac12I_3+\frac12\mathbf1\mathbf1^\dagger,\qquad
G_-=\frac32I_3-\frac12\mathbf1\mathbf1^\dagger.
$$
两者都正半定且对角元为一，非对角元分别为$1/2$和$-1/2$。模型甲两轮都用$G_+$，模型乙第一轮用$G_-$、第二轮用$G_+$。两模型每个标签对的第一轮重叠模都是$1/2$，两轮联合重叠模都是$1/4$，但联合Gram矩阵分别为
$$
G_{\mathrm A}=\frac34I_3+\frac14\mathbf1\mathbf1^\dagger,\qquad
G_{\mathrm B}=\frac54I_3-\frac14\mathbf1\mathbf1^\dagger.
$$
设$h_{\mathrm A}=[\sqrt{3/2}+\sqrt3]/3$，$h_{\mathrm B}=[1/\sqrt2+\sqrt5]/3$。两个Gram矩阵的平方根均有恒定对角元，平方根测量分别达到逐标签正确率
$$
s_{\mathrm A}=h_{\mathrm A}^2=\frac{(\sqrt{3/2}+\sqrt3)^2}{9},\qquad
s_{\mathrm B}=h_{\mathrm B}^2=\frac{(1/\sqrt2+\sqrt5)^2}{9},
$$
且$s_{\mathrm A}\ne s_{\mathrm B}$。为证其为最坏标签最优值，令$A$为联合记录列矩阵、$T=AA^\dagger$，并令$T^{-1/2}$表示在$\operatorname{supp}T$上的逆平方根、在$\ker T$上为零的Moore--Penrose逆。由于每个$v_x$属于$\operatorname{supp}T$，对任意向量$z$，Cauchy--Schwarz给出
$$
|\langle v_x,z\rangle|^2\le\langle v_x,T^{-1/2}v_x\rangle\langle z,T^{1/2}z\rangle=h\langle z,T^{1/2}z\rangle,
$$
其中$h$是相应的恒定平方根对角元。因此$|v_x\rangle\langle v_x|\le hT^{1/2}$，任意POVM的等先验平均正确率至多为$h^2$；平方根测量达到该值，且逐标签相同，故最坏任务也达到该值。这个反例只改变联合Gram的相位符号，保留全部逐对模资料，却改变有限联合解码误差。

（四）旧记录的零重叠不阻止后续Hamiltonian从不均匀人口制造指针基相干。取$0<p<1$且$p\ne1/2$，先写入并隐藏正交记录，使系统为$\rho_d=pP_0+(1-p)P_1$。给定$\tau_0>0$，令
$$
Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\qquad H=\frac{\pi\hbar}{4\tau_0}Y.
$$
则$U(\tau_0)=\exp(-i\pi Y/4)$，直接计算得
$$
U(\tau_0)\rho_dU(\tau_0)^\dagger=\frac12\begin{pmatrix}1&2p-1\\ 2p-1&1\end{pmatrix},\qquad
\mathsf d\!\left(U\rho_dU^\dagger,\Delta(U\rho_dU^\dagger)\right)=\frac{|2p-1|}{2}>0.
$$
旧记录仍有零重叠，但它没有把后续系统Hamiltonian限制在指针代数内；这也没有恢复已经丢弃的初始相位。$p=1/2$时初态是最大混态，单独的酉不能制造相干，故该端点不属于反例。

（五）任意密集但过弱的新鲜补写仍可能让系统翻转。取二标签、$\sigma_0=P_0$及
$$
H=\frac{\pi\hbar}{2\tau_*}X,\qquad X=|0\rangle\langle1|+|1\rangle\langle0|,\qquad r_N=\exp(-1/N^2).
$$
每个长度$h=\tau_*/N$的自由段后施加合法的新鲜Schur通道$\Phi_{r_N}=r_N\operatorname{id}+(1-r_N)\Delta$。没有写入时，$N$段自由演化把$P_0$变为$P_1$。对任意态$\rho$，
$$
\mathsf d(\Phi_{r_N}(\rho),\rho)=(1-r_N)\mathsf d(\Delta(\rho),\rho)\le1-r_N.
$$
逐轮用通道收缩性比较有写入和无写入的演化，得到
$$
\mathsf d(\sigma_N,P_1)\le N(1-r_N)\le\frac1N,\qquad
\operatorname{tr}(P_0\sigma_N)\le\frac1N.
$$
虽然轮次任意增加，$r_N\to1$且$N(1-r_N)\to0$；系统仍趋近翻转态。这个例子与定理8.12的预算一致，说明“任意频繁”必须和每轮记录强度一起计量。

上述六个构造（零）至（五）分别隔离累积预算、访问权限、准备态纯度、联合Gram相位、后续非对角动力学和补写强度。它们不提供实验或Lean验证，不给出普适经典性，不规定唯一全局结果；所有极限仍只是固定有限标签下有限前缀数列的极限。证毕。

本节明确区分两类模型：前者依赖一个固定标签的有限产品记录，后者是“自由演化—新鲜固定标签Schur通道—取迹、无反馈”的交错递推。重复相互作用背景可参见Francesco Ciccarello、Salvatore Lorenzo、Vittorio Giovannetti、G. Massimo Palma，*Quantum collision models: open system dynamics from repeated interactions*，*Physics Reports* 954（2022）1--70，arXiv:2106.11974v2；Zeno背景可参见P. Facchi、S. Pascazio，*Quantum Zeno subspaces*，*Physical Review Letters* 89（2002）080401，arXiv:quant-ph/0201115v2。除已直接核查的Schur判据和二态判别基础外，不宣称这些背景文献给出本节常数或本节命题的优先性。本文没有实验、Lean或唯一结果的断言。

## 追加锚（新终端）
## 9. 有限前缀的项目一致性与辅助系统稳定性

### 9.1 固定标签模型的前缀态

本章继续使用定义8.1的固定标签、新鲜记录模型。标签集为有限集$\mathsf X$，系统基为$\{|x\rangle:x\in\mathsf X\}$。第$t$个记录单元初态为$|0_t\rangle$，并满足
$$
U_t\bigl(|x\rangle|0_t\rangle\bigr)
=e^{i\theta_{x,t}}|x\rangle|e_x^{(t)}\rangle .
$$
记
$$
G_t(x,y)=\langle e_y^{(t)}|e_x^{(t)}\rangle,
\qquad
\Theta_x(N)=\sum_{t=1}^{N}\theta_{x,t},
$$
以及有限前缀记录向量
$$
|e_x^{\le N}\rangle=\bigotimes_{t=1}^{N}|e_x^{(t)}\rangle .
$$
对系统初态$\rho=\sum_{x,y}\rho_{xy}|x\rangle\langle y|$，定义保留系统和前$N$个记录单元的态
$$
\rho_N
=
\sum_{x,y}\rho_{xy}
 e^{i(\Theta_x(N)-\Theta_y(N))}
 |x\rangle\langle y|\otimes
 |e_x^{\le N}\rangle\langle e_y^{\le N}| .
$$
每个$\rho_N$只涉及有限维空间；本章不把这列有限态预先解释成无限张量积态。

### 9.2 含系统前缀的项目一致性 no-go

**定理 9.1（非平凡记录破坏朴素项目一致性）。** 对任意$N\ge0$，令
$$
 c_{xy}^{N+1}
 =e^{i(\theta_{x,N+1}-\theta_{y,N+1})}G_{N+1}(x,y).
$$
则
$$
\operatorname{tr}_{E_{N+1}}\rho_{N+1}=\rho_N
$$
当且仅当
$$
 c_{xy}^{N+1}=1
\qquad\text{对每个满足 }\rho_{xy}\ne0\text{ 的有序对 }(x,y).
$$

特别地，若要求该等式对所有系统初态都成立，则对每个$x\ne y$必须有
$$
|G_{N+1}(x,y)|=1
\quad\text{且}\quad
e^{i(\theta_{x,N+1}-\theta_{y,N+1})}G_{N+1}(x,y)=1.
$$
在有限维Hilbert空间中，$|G_{N+1}(x,y)|=1$意味着$|e_x^{(N+1)}\rangle$与$|e_y^{(N+1)}\rangle$只差一个相位；上式再要求该相位被系统相位完全抵消。因此这一步记录在相位补偿后对标签不携带可读区分信息。只要某个标签对满足$|G_{N+1}(x,y)|<1$，就存在一个初态使含系统前缀族不满足项目一致性。

证明。对$\rho_{N+1}$取迹只作用于最后一个记录因子，并使用
$$
\operatorname{tr}\!\left(|e_x^{(N+1)}\rangle\langle e_y^{(N+1)}|\right)
=G_{N+1}(x,y).
$$
因此
$$
\operatorname{tr}_{E_{N+1}}\rho_{N+1}
=
\sum_{x,y}\rho_{xy}e^{i(\Theta_x(N)-\Theta_y(N))}
 c_{xy}^{N+1}
 |x\rangle\langle y|\otimes
 |e_x^{\le N}\rangle\langle e_y^{\le N}| .
$$
对角项满足$c_{xx}^{N+1}=1$。系统矩阵单位$|x\rangle\langle y|$两两线性独立，且每个记录算子$|e_x^{\le N}\rangle\langle e_y^{\le N}|$非零，所以与$\rho_N$相等恰好等价于所有非零系数满足$c_{xy}^{N+1}=1$。若要求对所有初态成立，可选取只在$x,y$两维上有非零相干的纯态；于是每个$x\ne y$都必须满足该条件。最后由Cauchy--Schwarz等号条件得到条件环境向量只差相位。证毕。

这个结论区分了两件事：每个有限前缀都可以精确定义，以及这些前缀能否通过朴素的“删除最后一个记录因子”组成同一个含系统历史的项目族。真正的记录步骤通常改变系统与保留记录之间的相干结构，所以第二件事不能从第一件事自动推出。第8.14节的有限数列极限因此不能单独被解释成一个全局密度矩阵。

**反例 9.2（最小非平凡记录）。** 取两个标签、一个新增记录单元，令$\theta_{0,1}=\theta_{1,1}=0$，并令
$$
\langle e_1^{(1)}|e_0^{(1)}\rangle=\mu,
\qquad 0\le|\mu|<1.
$$
对初态$|+\rangle\langle+|$，$\rho_0=|+\rangle\langle+|$，而
$$
\operatorname{tr}_{E_1}\rho_1
=\frac12
\begin{pmatrix}
1&\mu\\
\overline\mu&1
\end{pmatrix}
\ne
\frac12
\begin{pmatrix}
1&1\\
1&1
\end{pmatrix}
=\rho_0.
$$
因此“保留更多记录后再把它删掉”并不会恢复此前的含系统态；删去记录与把记录从未写入过是两个不同操作。

### 9.3 记录边缘的正面一致性

**定理 9.3（记录-only边缘的一致性）。** 令
$$
\chi_N=\operatorname{tr}_S\rho_N.
$$
若初态系统对角人口为$p_x=\rho_{xx}$，则
$$
\chi_N
=\sum_x p_x|e_x^{\le N}\rangle\langle e_x^{\le N}|,
$$
并且对每个$N$都有
$$
\operatorname{tr}_{E_{N+1}}\chi_{N+1}=\chi_N.
$$

证明。取系统迹只保留$x=y$项，因而所有系统相位和初始系统相干都消失。再对最后一个记录因子取迹，$\langle e_x^{(N+1)}|e_x^{(N+1)}\rangle=1$，逐项得到所示等式。证毕。

所以记录边缘给出一个真正一致的有限前缀族，可以作为记录历史的项目数据。这个结论仍只说有限边缘之间的兼容性；若要选择具体的无限记录Hilbert空间、向量或可观测代数，还必须另行指定表示。含系统历史则应使用时间有序过程、过程张量或准局域代数，把“每个有限窗口的态”与“跨窗口的限制映射”分开描述。

### 9.4 纠缠参考下的有限前缀稳定界

项目一致性讨论的是态能否拼接；另一个独立问题是，有限前缀退相干是否对任意旁参考系统都稳定。令$C$为一个有限标签Schur Gram矩阵，$C_{xx}=1$，并令
$$
\Phi_C(A)=C\odot A,
\qquad
\Delta(A)=\sum_xP_xAP_x,
\qquad
q(C)=\max_{x\ne y}|C_{xy}|.
$$
定义辅助系统允许的最坏相干缺陷
$$
\varepsilon_\diamond(C)
=\frac12\|\Phi_C-\Delta\|_\diamond
=\sup_{R,\,\omega_{SR}}
\mathsf d\!\left((\Phi_C\otimes\operatorname{id}_R)(\omega_{SR}),
(\Delta\otimes\operatorname{id}_R)(\omega_{SR})\right),
$$
其中$R$可取有限维，且只需考察密度态$\omega_{SR}$。

这里$\Phi_C-\Delta$是保厄米、迹消失的线性映射，因此标准稳定化定义可等价地写成密度态上的最大迹距离；辅助系统维数取不超过系统维数$d$即可达到该上确界。

**定理 9.4（辅助系统一致的有限前缀界）。** 对标签数$d=|\mathsf X|\ge2$，有
$$
\frac{q(C)}2
\le \varepsilon_\diamond(C)
\le \frac{d-1}{2}q(C).
$$
因此在固定有限$d$下，任意一列有限前缀Schur通道满足
$$
q(C_N)\longrightarrow0
\quad\Longleftrightarrow\quad
\varepsilon_\diamond(C_N)\longrightarrow0.
$$
这个结论只给出上下界，不声称一般情形下的精确diamond范数公式。

证明。取任意参考系统$R$和密度态$\omega_{SR}$，按系统标签分块为$\omega_{SR}=[\omega_{xy}]_{x,y}$，并令$p_x=\operatorname{tr}(\omega_{xx})$。正块矩阵的Cauchy--Schwarz因子化给出
$$
\|\omega_{xy}\|_1\le\sqrt{p_xp_y}.
$$
于是
$$
\begin{aligned}
\mathsf d\!\left((\Phi_C\otimes\operatorname{id})(\omega),
(\Delta\otimes\operatorname{id})(\omega)\right)
&\le \frac12\sum_{x\ne y}|C_{xy}|\,\|\omega_{xy}\|_1\\
&\le \frac{q(C)}2\sum_{x\ne y}\sqrt{p_xp_y}\\
&=\frac{q(C)}2\left[\left(\sum_x\sqrt{p_x}\right)^2-1\right]\\
&\le\frac{d-1}{2}q(C),
\end{aligned}
$$
其中最后一步使用Cauchy--Schwarz和$\sum_xp_x=1$。下界取一个达到$q(C)$的标签对$x,y$，并使用系统纯态$(|x\rangle+e^{i\varphi}|y\rangle)/\sqrt2$、参考系统一维；此时输出差的迹距离为$q(C)/2$。证毕。

定理9.4把第8.14节的系统态上界提升为带任意有限纠缠参考的操作性上界，但它仍然是固定有限标签、有限前缀的陈述。它不说明记录是否可访问，也不把项目一致性no-go变成全局态存在定理：可操作稳定性与跨前缀可拼接性是两个独立条件。

### 9.5 三个约束不能互相替代

第9章的三个量分别回答不同问题：

$$
\begin{array}{c|c}
\text{量}&\text{它控制的性质}\\ \hline
c_{xy}^{t}&\text{含系统前缀能否按删除映射一致限制}\\
|G_t(x,y)|&\text{该记录步骤对标签的可区分性}\\
q(C_N),\ \varepsilon_\diamond(C_N)&\text{有限前缀对系统及旁参考的退相干稳定性}
\end{array}
$$

因此“保留多少约束”没有脱离模型的单一整数答案。增加记录单元可以使$q(C_N)$变小，却同时破坏含系统前缀的朴素项目一致性；相位补偿可以使某个$c_{xy}^{t}$等于$1$，却不增加标签可读性；而小的系统退相干缺陷也不保证可读取记录存在。稳定经典描述需要分别指定限制映射、访问集合和动力学预算，再在同一有限前缀上检验它们。

本章没有构造无限时间全局量子态，也没有把记录一致性、退相干稳定性或有限前缀极限解释成普适经典现实。它只把“历史保留多少才稳定”拆成三个可计算的有限问题：前缀能否一致限制、记录是否区分标签、以及包含旁参考时后续操作是否仍看不见相干。

## 10. 约束保留的预测充分性与相位访问预算

“保留多少约束才得到稳定的经典现实”必须先拆成有限任务：保留的数据能否读取，能否预测指定的未来粗读数，以及这些读数是否在给定时段内保持。下面的量分别回答这三个问题；它们不等价于完整量子态已经被确定。

### 10.1 粗标签、预测通道与读取误差

取有限维空间$\mathcal H$和$m\ge2$个非零正交投影
$$
Q_aQ_b=\delta_{ab}Q_a,\qquad \sum_{a=1}^{m}Q_a=I.
$$
定义粗标签分布、粗块代数和粗块去相干映射
$$
C_Q(\rho)_a=\operatorname{tr}(Q_a\rho),
\qquad
\mathcal A_Q=\operatorname{span}_{\mathbb C}\{Q_1,\ldots,Q_m\},
\qquad
B_Q(X)=\sum_aQ_aXQ_a.
$$
$C_Q$只保留粗标签概率，$B_Q$还保留每个粗块内部的量子态。因此$B_Q(\rho)=\rho$不表示$C_Q(\rho)$已经决定$\rho$。

固定有限时刻$0=\tau_0<\tau_1<\cdots<\tau_N=\tau_*<\infty$和CPTP通道$\mathcal E_k$，令
$$
\rho_k=\mathcal E_k(\rho_{k-1}),
\qquad p_k=C_Q(\rho_k).
$$
用列随机矩阵$K_k$表示目标经典比较动力学：
$$
K_k(b\mid a)\ge0,
\qquad \sum_bK_k(b\mid a)=1.
$$
预测$ p_k\approx K_k\cdots K_1p_0$和保持$ p_k\approx p_0$是两个不同要求；精确可预测的动力学可以是确定翻转。

记录写入取有限等距映射
$$
W\psi=\sum_aQ_a\psi\otimes E_a,
\qquad \|E_a\|=1,
\qquad E_a\in\mathcal H_F\otimes\mathcal H_B,
$$
其中只有$F$可读取，$B$不可访问。令
$$
\sigma_a^F=\operatorname{tr}_B|E_a\rangle\langle E_a|,
$$
并定义可读取记录的最坏标签错误
$$
\beta_F=\min_{\substack{M_a\ge0\\\sum_aM_a=I_F}}
\max_a\left[1-\operatorname{tr}(M_a\sigma_a^F)\right].
$$
若某个解码器的逐标签错误至多为$\beta$，则其输出分布$\widehat p_0$满足
$$
\operatorname{TV}(\widehat p_0,p_0)\le\beta,
\qquad
\operatorname{TV}(p,q)=\frac12\sum_a|p_a-q_a|.
$$
这是记录边缘上的经典通道误差，不把一次解码结果当作完整隐藏历史。

### 10.2 粗标签预测的精确缺陷

对通道$\mathcal E$、列随机矩阵$K$和$B\subseteq\{1,\ldots,m\}$，记
$$
Q_B=\sum_{b\in B}Q_b,
\qquad K(B\mid a)=\sum_{b\in B}K(b\mid a),
$$
以及
$$
\epsilon_Q(\mathcal E,K)
=\max_B\left\|
\mathcal E^*(Q_B)-\sum_aK(B\mid a)Q_a
\right\|.
$$

**定理 10.1（粗标签预测缺陷）。** 有精确等式
$$
\epsilon_Q(\mathcal E,K)
=\sup_\rho\operatorname{TV}\!\left(C_Q(\mathcal E(\rho)),KC_Q(\rho)\right),
$$
上确理由全部系统密度矩阵取得。对全部输入态存在零缺陷的经典律，当且仅当
$$
\mathcal E^*(\mathcal A_Q)\subseteq\mathcal A_Q.
$$
此时$K$唯一，并满足
$$
K(b\mid a)=\frac{\operatorname{tr}\left(Q_a\mathcal E^*(Q_b)\right)}{\operatorname{rank}Q_a}.
$$

一般情形的最优缺陷
$$
\epsilon_Q^*(\mathcal E)=\min_K\epsilon_Q(\mathcal E,K)
$$
可由有限半正定优化取得：最小化$\epsilon$，约束$K$列随机以及对全部$B$
$$
-\epsilon I\preceq
\mathcal E^*(Q_B)-\sum_aK(B\mid a)Q_a
\preceq\epsilon I.
$$

证明。对概率向量有$\operatorname{TV}(p,q)=\max_B|p(B)-q(B)|$；对Hermitian$D$有$\sup_\rho|\operatorname{tr}(\rho D)|=\|D\|$，且上确界由某个纯态达到。交换有限最大值与态空间上的上确界即得第一式。零缺陷等价于每个$\mathcal E^*(Q_b)$属于粗块代数；正性与$\mathcal E^*(I)=I$给出非负系数和列和为一，压缩到$Q_a$并取迹得到唯一系数。有限随机矩阵集上的连续最小化达到，算子范数界等价于两侧半正定约束。证毕。

将缺陷拆成
$$
\mathcal E^*(Q_B)-\sum_aK(B\mid a)Q_a
=\bigl[\mathcal E^*(Q_B)-B_Q(\mathcal E^*(Q_B))\bigr]
+\bigl[B_Q(\mathcal E^*(Q_B))-\sum_aK(B\mid a)Q_a\bigr]
$$
可分别看出粗块间相干和粗块内部状态对未来读数的影响。粗块间退相干只消除第一项。

### 10.3 预测、保持与有限预算

令
$$
\epsilon_k=\epsilon_Q(\mathcal E_k,K_k),
\qquad
\lambda_k=\max_a[1-K_k(a\mid a)],
\qquad
\bar p_0=\widehat p_0,
\qquad
\bar p_k=K_k\cdots K_1\widehat p_0.
$$
**定理 10.2（有限前缀的预测与保持预算）。** 若初始读取满足$\operatorname{TV}(\widehat p_0,p_0)\le\beta$，则对每个$k\le N$有
$$
\operatorname{TV}(p_k,\bar p_k)
\le\min\left\{1,\beta+\sum_{j=1}^{k}\epsilon_j\right\},
$$
以及
$$
\operatorname{TV}(p_k,p_0)
\le\min\left\{1,\sum_{j=1}^{k}(\epsilon_j+\lambda_j)\right\}.
$$
因此
$$
\beta+\sum_{j=1}^{N}\epsilon_j\le\delta_{\rm pred},
\qquad
\sum_{j=1}^{N}(\epsilon_j+\lambda_j)\le\delta_{\rm stay}
$$
是同时覆盖这些有限时刻的充分预算。

证明。随机矩阵不增大总变差距离，故
$$
\operatorname{TV}(p_k,\bar p_k)
\le\epsilon_k+\operatorname{TV}(p_{k-1},\bar p_{k-1}).
$$
另一方面，对任意概率向量$p$，$\operatorname{TV}(K_kp,p)\le\lambda_k$；结合三角不等式递推第二式。证毕。

二标签例子中，令
$$
\mathcal E_\lambda(\rho)=(1-\lambda)\Delta(\rho)+\lambda X\Delta(\rho)X,
\qquad 0\le\lambda\le1.
$$
其精确经典矩阵为
$$
K_\lambda=
\begin{pmatrix}1-\lambda&\lambda\\\lambda&1-\lambda\end{pmatrix},
$$
所以$\epsilon_Q=0$；但$\lambda=1$时标签确定翻转，预测完全精确，而对尖锐初始标签的保持性达到最坏失败。若$\lambda=10^{-3}$、$N=20$，从一个标签出发的末端离开概率为
$$
\frac{1-(1-2\lambda)^{20}}2\approx0.0196245.
$$
端点界不自动覆盖轮间时刻；若需要连续时段，必须为每个$\tau_{k-1}+s$另给实际通道和比较矩阵。

### 10.4 未来读数所需的最小特征保留

取有限细标签集$\mathsf X$及其完整正交基投影$P_x=|x\rangle\langle x|$、目标读数$g:\mathsf X\to\mathsf Y$，以及有限通道族$\Psi_k$，其中$\Psi_0=\operatorname{id}$。令
$$
Q_b^g=\sum_{g(x)=b}P_x,
\qquad A_{k,b}=\Psi_k^*(Q_b^g).
$$
给定有限可访问特征指标集$\mathcal J_{\rm acc}$及特征$h_j:\mathsf X\to\mathsf Z_j$，保留$J\subseteq\mathcal J_{\rm acc}$时的标签为$f_J(x)=(h_j(x))_{j\in J}$。若某个$A_{k,b}$在细标签基中有非对角元，则任何只保留$f_J$的经典标签都不能对全部输入态精确预测该读数。若所有$A_{k,b}$均对角，定义
$$
 v(x)=\bigl(\langle x|A_{k,b}|x\rangle\bigr)_{k,b},
$$
以及
$$
\mathcal P=\{\{x,y\}:v(x)\ne v(y)\},
\qquad
S_j=\{\{x,y\}\in\mathcal P:h_j(x)\ne h_j(y)\}.
$$
**定理 10.3（最小特征覆盖）。** 对全部输入态精确预测所有指定读数的充要条件是
$$
\bigcup_{j\in J}S_j=\mathcal P.
$$
给定正成本$c_j$，最小保留成本为
$$
C_{\min}
=\min_{\substack{J\subseteq\mathcal J_{\rm acc}\\\bigcup_{j\in J}S_j=\mathcal P}}
\sum_{j\in J}c_j,
$$
不可行时取$+\infty$；若$\mathcal P=\varnothing$，空集成本为零。

证明。对所有密度态成立的概率等式等价于每个$A_{k,b}$在每个$f_J$纤维上取常值；细标签对被保留特征分开恰好等价于覆盖条件。反向以共同常值定义列随机矩阵，正性和完备性保证其列和为一。证毕。

将$k=0$纳入读数族，表示当前必需标签也必须被保留；不能把所有标签合并成一个常标签来规避原任务。$c_j$只计量指定经典特征的保留成本，不包含写入、控制、存储寿命或读取扰动。

### 10.5 关联记录的相位访问

取二标签系统及有限关联记录$E_0,E_1\in\mathcal H_F\otimes\mathcal H_B$，$\|E_0\|=\|E_1\|=1$，并令
$$
W|x\rangle=|x\rangle|E_x\rangle.
$$
定义
$$
\sigma_x^F=\operatorname{tr}_B|E_x\rangle\langle E_x|,
\qquad
T_F=\operatorname{tr}_B|E_0\rangle\langle E_1|,
$$
以及
$$
D_F=\frac12\|\sigma_0^F-\sigma_1^F\|_1,
\qquad
V_F=\|T_F\|_1.
$$
$D_F$衡量只读$F$时的等先验标签区分能力；对应最优平均错误为$(1-D_F)/2$。对
$$
|\Psi_\phi\rangle=\frac{|0\rangle|E_0\rangle+e^{i\phi}|1\rangle|E_1\rangle}{\sqrt2}
$$
并在$B$上取迹，得到
$$
\mathsf d(\rho_\phi^{SF},\rho_\psi^{SF})
=\left|\sin\frac{\phi-\psi}{2}\right|V_F,
$$
以及
$$
\mathsf d(\rho_\phi^{SF},\Delta_S\rho_\phi^{SF})=\frac{V_F}{2}.
$$
更一般地，对系统输入矩阵元$\rho_{01}$，有
$$
\mathsf d\!\left(\operatorname{tr}_B(W\rho W^\dagger),
\Delta_S\operatorname{tr}_B(W\rho W^\dagger)\right)
=|\rho_{01}|V_F.
$$
只读取$F$的边缘态与输入相位无关；$V_F$度量的是系统与可访问记录之间仍可被联合操作利用的相位。

对任意$F$上的酉$U_F$，有
$$
V_F=\max_{U_F}\left|\langle E_1|(U_F\otimes I_B)|E_0\rangle\right|.
$$
若随后施加受控酉$P_0\otimes U_0+P_1\otimes U_1$并丢弃$F$，恢复后的系统相干乘子为
$$
\operatorname{tr}(U_0T_FU_1^\dagger),
$$
其最大模为$V_F$；对输入$|+\rangle$，相位校正后的最大$|+\rangle$重叠概率为
$$
\frac{1+V_F}{2}.
$$
这只对所列受控酉操作类作最优性陈述。

### 10.6 不可访问记录的相位阈值与反例

若不可访问部分$B$上存在二输出测量，使等先验平均标签错误率不超过$0\le\beta<1/2$，则
$$
V_F\le2\sqrt{\beta(1-\beta)}.
$$
因此所有二标签输入满足
$$
\mathsf d\!\left(\operatorname{tr}_B(W\rho W^\dagger),
\Delta_S\operatorname{tr}_B(W\rho W^\dagger)\right)
\le2|\rho_{01}|\sqrt{\beta(1-\beta)}
\le\sqrt{\beta(1-\beta)}.
$$
给定$0\le\nu<1$，充分条件
$$
\beta\le\frac{1-\sqrt{1-\nu^2}}2
$$
保证$V_F\le\nu$。这只给充分条件，记录数量不出现在阈值中。

证明。令不可访问部分上的二输出效应为$M_0,M_1$，并定义$\varepsilon_0=\operatorname{tr}(M_1\tau_0^B)$、$\varepsilon_1=\operatorname{tr}(M_0\tau_1^B)$，其中$\tau_x^B=\operatorname{tr}_F|E_x\rangle\langle E_x|$；其平均值$\beta'=(\varepsilon_0+\varepsilon_1)/2\le\beta$。对任意$U_F$，插入$M_0+M_1=I_B$并对每一项使用Cauchy--Schwarz，得到
$$
\left|\langle E_1|(U_F\otimes I_B)E_0\rangle\right|
\le\sqrt{(1-\varepsilon_0)\varepsilon_1}
 +\sqrt{\varepsilon_0(1-\varepsilon_1)}
\le2\sqrt{\beta'(1-\beta')}.
$$
取$U_F$的最大值即得$V_F\le2\sqrt{\beta(1-\beta)}$；再使用$|\rho_{01}|\le1/2$得到相干距离界，解二次不等式得到所列充分条件。证毕。

三个有限反例说明数量本身不能替代任务覆盖：

1. **完全关联的重复记录。** 对$0<\beta<1/2$和有限$r\ge2$，取
$$
E_0=\sqrt{1-\beta}|0\rangle^{\otimes r}+\sqrt\beta|1\rangle^{\otimes r},
\qquad
E_1=\sqrt\beta|0\rangle^{\otimes r}+\sqrt{1-\beta}|1\rangle^{\otimes r}.
$$
每个非空真片段$F$（$1\le|F|\le r-1$）都有读取错误$\beta$，但其相位访问量为$V_F=2\sqrt{\beta(1-\beta)}$，与片段大小无关；增加记录没有增加独立证据。若$F$取全部记录，则$B=\varnothing$且$V_F=1$，这是不同的端点。

2. **大量独立但未约束目标自由度的约束。** 取
$$
\mathcal H=\mathbb C^2_L\otimes(\mathbb C^2)^{\otimes r},
\qquad C_j=I_L\otimes Z_j.
$$
所有条件$C_j=+1$彼此独立并严格保持，但
$$
H=\frac{\pi\hbar}{2\tau_*}X_L\otimes I
$$
与它们交换，却在$\tau_*$翻转逻辑标签。约束数量任意大仍不能稳定未被约束的自由度。

3. **完美粗标签遗漏内部相位。** 取
$$
Q_A=|0\rangle\langle0|+|1\rangle\langle1|,
\qquad Q_B=|2\rangle\langle2|,
$$
以及$|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$和
$$
H=\hbar\Omega(|2\rangle\langle+|+|+\rangle\langle2|),
\qquad \tau_*=\frac{\pi}{2\Omega}.
$$
$\Omega>0$。$|+\rangle$和$|−\rangle$具有相同粗标签和相同细基布居，但
$$
U(\tau_*)|+\rangle=-i|2\rangle,
\qquad
U(\tau_*)|−\rangle=|−\rangle.
$$
因此末端粗标签分布的总变差距离为$1$，任何数量的初始$A/B$标签副本都不能确定上述未来$A/B$读数；演化之后新取得的记录可以区分这两个状态。

这些反例分别隔离关联冗余、约束覆盖不足和粗标签内部信息缺失。它们说明稳定经典描述需要同时指定访问集合、未来读数、动力学比较律和误差预算；没有脱离这些数据的单一“所需约束数量”。本章所有对象仍为有限维、有限时段；不构造无限张量积态、不主张普适经典性、不提供实验或Lean结论，也不选择唯一全局结果。

## 追加锚（新终端）

## 第 11 章：粗标签读数的项目一致性桥接

第 9 章的项目一致性条件作用于完整含系统态：删除一个未来记录后，含系统与既有记录前缀的边缘是否保持不变。第 10 章的粗标签缺陷则描述单步动力学是否能由粗标签概率闭合预测。两者之间还缺少一个可直接计算的桥接：**删除记录之后，粗标签测量本身的概率是否保持不变。** 这一问题只涉及测量事件，不要求完整密度矩阵保持不变。

### 11.1 一步记录与粗事件

设有限系统基为 $\{|x\rangle\}_{x\in X}$，一步记录丢弃通道为
$$
M_C(\rho)=C\odot\rho,
$$
其中 $C=(c_{xy})$ 是单位对角的相关矩阵，因此 $C\succeq0$ 且 $c_{yx}=\overline{c_{xy}}$。记 $J$ 为全 1 矩阵，即 $J_{xy}=1$；它是 Schur 乘法的单位元。令 $\{Q_b\}_{b\in\mathcal B}$ 是有限粗标签的投影测量：
$$
Q_bQ_{b'}=\delta_{bb'}Q_b,
\qquad
\sum_{b\in\mathcal B}Q_b=I.
$$
对事件 $B\subseteq\mathcal B$，记
$$
Q_B=\sum_{b\in B}Q_b.
$$
粗标签分布记为
$$
C_Q(\rho)_b=\operatorname{tr}(Q_b\rho).
$$
定义删除前后的事件概率差的最坏值为
$$
\delta_B(C)
=
\sup_{\rho}\left|
\operatorname{tr}\!\left(Q_BM_C(\rho)\right)
-
\operatorname{tr}(Q_B\rho)
\right|,
$$
以及所有粗事件的缺陷
$$
\delta_Q(C)=\max_{B\subseteq\mathcal B}\delta_B(C).
$$
这里的上确界遍历系统上的所有密度算子。

Schur 通道的对偶为
$$
M_C^*(A)=\overline C\odot A,
$$
因为
$$
\operatorname{tr}\!\left(A(C\odot\rho)\right)
=
\operatorname{tr}\!\left((\overline C\odot A)\rho\right).
$$
所以定义粗事件缺陷算子
$$
D_B(C)=M_C^*(Q_B)-Q_B
=(\overline C-J)\odot Q_B.
$$
$D_B(C)$ 是 Hermitian 算子，因而
$$
\delta_B(C)=\|D_B(C)\|_\infty.
$$
这里使用了有限维事实
$$
\sup_{\rho}\left|\operatorname{tr}(\rho A)\right|=\|A\|_\infty
$$
对任意 Hermitian $A$ 成立。

### 11.2 最坏粗读数误差的精确公式

对每个输入态，粗标签分布的总变差距离满足
$$
\operatorname{TV}\!\left(
C_Q(M_C(\rho)),C_Q(\rho)
\right)
=
\max_{B\subseteq\mathcal B}
\left|
\operatorname{tr}\!\left(Q_BM_C(\rho)\right)
-
\operatorname{tr}(Q_B\rho)
\right|.
$$
因此
$$
\boxed{
\sup_{\rho}\operatorname{TV}\!\left(
C_Q(M_C(\rho)),C_Q(\rho)
\right)
=
\delta_Q(C)
=
\max_{B\subseteq\mathcal B}
\left\|(\overline C-J)\odot Q_B\right\|_\infty.
}
$$
证明只用有限最大值与态空间上确界的交换：对任意 $\rho$，每个事件差都不超过相应的算子范数，给出一个上界；反之，固定达到最大值的事件 $B$，取其 Hermitian 缺陷算子的最大特征向量态即可达到该事件的范数。证毕。

于是粗读数对所有输入态项目一致，当且仅当
$$
\boxed{
(\overline{c_{xy}}-1)(Q_B)_{xy}=0
\quad
\text{对所有 }B\subseteq\mathcal B\text{ 与所有 }x,y\in X.
}
$$
由于 $c_{xy}=1$ 与 $\overline{c_{xy}}=1$ 等价，也可写成：
$$
(Q_B)_{xy}=0
\quad\text{只要 }c_{xy}\ne1.
$$
这是一条比完整态项目一致性更弱、但比单纯保留对角布居更强的精确条件。

### 11.3 Gram 几何与等价类块对角性

在受控记录模型中，若
$$
 c_{xy}=e^{i(\theta_x-\theta_y)}\langle e_y,e_x\rangle,
$$
令
$$
 w_x=e^{i\theta_x}e_x,
$$
则
$$
 c_{xy}=\langle w_y,w_x\rangle.
$$
因为 $w_x,w_y$ 都是单位向量，Cauchy--Schwarz 等号条件给出
$$
 c_{xy}=1
\iff
w_x=w_y.
$$
于是关系
$$
 x\sim_C y
\iff
c_{xy}=1
$$
是一个等价关系。粗事件 $Q_B$ 的项目一致性条件等价于：每个 $Q_B$ 相对于这些等价类分解都是块对角的。也就是说，只有相位补偿后的记录向量满足 $w_x=w_y$ 的系统标签之间，粗投影才允许保留非零矩阵元；记录向量不同的标签之间，粗投影必须没有相干矩阵元。

这给出三种可区分的情况：

1. 完整含系统态可能不满足项目一致性，因为某个 $c_{xy}\ne1$；
2. 指针基投影 $Q_B=\sum_{x\in B}|x\rangle\langle x|$ 始终满足条件，因为它没有非对角元；
3. 粗标签若把不同指针态相干叠加为同一事件投影，则会暴露记录删除造成的相位或幅度变化。

因此，“粗读数稳定”不能推出“完整态稳定”；它只说明所选观测代数没有访问被记录抹除的矩阵元。

### 11.4 二标签最小反例

取 $X=\{0,1\}$，并令粗测量为
$$
Q_+=|+\rangle\langle+|,
\qquad
Q_-=|-\rangle\langle-|,
$$
其中
$$
|\pm\rangle=\frac{|0\rangle\pm|1\rangle}{\sqrt2}.
$$
设一步记录的非对角 Schur 因子为
$$
 c_{01}=re^{i\phi}\ne1,
\qquad
c_{10}=\overline{c_{01}},
\qquad
0\le r\le1.
$$
对事件 $\{+\}$，有
$$
Q_+=
\frac12
\begin{pmatrix}
1&1\\
1&1
\end{pmatrix},
$$
从而
$$
D_+(C)=
\frac12
\begin{pmatrix}
0&\overline{c_{01}}-1\\
c_{01}-1&0
\end{pmatrix}.
$$
其算子范数为
$$
\|D_+(C)\|_\infty=\frac{|1-c_{01}|}{2}.
$$
$Q_-$ 给出相同范数，因此
$$
\boxed{
\delta_Q(C)=\frac{|1-c_{01}|}{2}.
}
$$
若改用指针测量
$$
Q_0=|0\rangle\langle0|,
\qquad
Q_1=|1\rangle\langle1|,
$$
则所有 $D_B(C)$ 都为零，故
$$
\delta_Q(C)=0
$$
即使完整含系统态的非对角元已经被记录改变。这一对测量明确展示了“同一个物理记录，对一个读数代数不可见，对另一个读数代数可见”。

### 11.5 多步删除与联合预算

若连续删除记录的 Schur 因子为 $C_1,\ldots,C_k$，则总通道为
$$
M_{1:k}=M_{C_k}\circ\cdots\circ M_{C_1}
=M_{C_1\odot\cdots\odot C_k}.
$$
令
$$
C_{1:k}=C_1\odot\cdots\odot C_k.
$$
经过前 $k$ 步删除后，所选粗测量的累计读数缺陷精确为
$$
\delta_Q(C_{1:k})
=
\max_B\left\|(\overline{C_{1:k}}-J)\odot Q_B\right\|_\infty.
$$
相应地，累计因子 $c_{xy}^{(1:k)}=\prod_{t=1}^k c_{xy}^{(t)}$ 定义累计记录等价类；各步等价关系的交集是一个充分条件，但在存在相位抵消时不必等于累计等价类。只有累计因子回到 $1$ 的标签对之间，粗投影才可持续保留非对角矩阵元。

若只知道各步的粗读数预算
$$
\delta_Q(C_t)\le\eta_t,
$$
则不能仅由这些单步标量确定总缺陷的精确值；不同步的非对角元可能相互抵消，也可能相互增强。不过，Schur 乘法对应的单位保持完全正映射收缩算子范数，因此总有保守上界
$$
\delta_Q(C_{1:k})\le\sum_{t=1}^k\delta_Q(C_t)\le\sum_{t=1}^k\eta_t.
$$
若需要更尖锐的上界，可对标量乘积作望远镜展开：令
$$
C_{<t}=C_1\odot\cdots\odot C_{t-1},
\qquad C_{<1}=J,
$$
则对每个粗事件有
$$
(\overline{C_{1:k}}-J)\odot Q_B
=
\sum_{t=1}^k
\bigl(\overline{C_{<t}}\odot(\overline{C_t}-J)\bigr)\odot Q_B.
$$
因此
$$
\delta_Q(C_{1:k})
\le
\max_B\sum_{t=1}^k
\left\|
\bigl(\overline{C_{<t}}\odot(\overline{C_t}-J)\bigr)\odot Q_B
\right\|_\infty.
$$
这里每一项由前缀 Schur 通道对算子范数的收缩性控制，因而不超过相应的单步缺陷；显示的累计因子界通常比 $\sum_t\eta_t$ 更尖锐。

第 10 章的预测缺陷 $\epsilon_Q(\mathcal E,K)$ 与本章的删除缺陷 $\delta_Q(C)$ 作用在不同方向：前者衡量动力学后验是否仍由粗标签闭合，后者衡量环境记录被删除后粗事件概率是否改变。若二者均有预算，则对任意参考粗分布 $\bar p_k$ 可先用第 10 章的动力学界，再增加本章的记录删除误差；这只是三角不等式得到的联合上界，不意味着存在与模型无关的最小约束数量。

本章给出了“保留多少约束才能稳定经典读数”的一个可检验答案：约束数量本身不是充分变量，决定粗读数稳定性的是粗投影的非对角支撑是否落在 $c_{xy}=1$ 的记录等价类内。不同读数代数可以对同一条记录给出不同的稳定性结论；因此经典现实的稳定范围必须连同读数代数、记录 Gram 几何和后续动力学一起指定。

## 追加锚（新终端）

## 12. 实际前缀、访问范围与持续读数

### 12.1 第11章比较对象与达到态的勘注

本节限定第11章中“删除前后”的物理解释，并修正其达到态措辞；第11.1—11.4节的缺陷公式、零缺陷判据和二标签数值不变；这些公式均对任意一步系统输入态取上确界，实际前缀的可达态限制见第12.2节。第11.5节的累计等价类只判断端点，不能把其中“持续保留”理解为全部中间记录前缀节点都一致。

对同一个联合态 $\omega_{SE}$，偏迹的定义始终给出
$$
\operatorname{tr}[(Q_B\otimes I_E)\omega_{SE}]
=\operatorname{tr}[Q_B\operatorname{tr}_E\omega_{SE}].
$$
因此偏迹本身不改变局部测量概率。取记录等距映射 $V_C|x\rangle=|x\rangle\otimes|w_x\rangle$，第11章的 $M_C(\rho)$ 是 $\operatorname{tr}_E(V_C\rho V_C^\dagger)$。它与 $\rho$ 的比较发生在**记录作用之前与作用之后**，并非同一时刻保留或忽略环境描述造成了扰动。下文将 $\delta_Q(C)$ 称为记录作用的粗读数缺陷。它正是定理10.1取 $\mathcal E=M_C$、经典比较律为恒等映射的特例；第11章的事件范数等式不另主张一个独立的一般定理。

第11.2节的范数达到态应为“绝对值最大的特征值所对应的单位特征向量态”，不是最大代数特征值的特征向量。比如 $C=I_3$、$Q=J_3/3$，其中 $J_3$ 为全一矩阵，则
$$
D=(I_3-J_3)/3,\qquad
\operatorname{spec}(D)=\{-2/3,1/3,1/3\}.
$$
其范数 $2/3$ 由最负特征值达到。此修正只影响证明中的达到态选择，不改变所陈述的算子范数等式。

### 12.2 既有记录限制可达输入

固定第9.1节的有限新鲜记录模型；所有步骤均在同一指针基上受控写入，中间没有额外控制、系统跃迁或旧记录反馈。记
$$
A_N=C_1\odot\cdots\odot C_N,\qquad A_0=J,
\qquad \sigma_N=\operatorname{tr}_{E_{1:N}}\rho_N=M_{A_N}(\rho).
$$
$\rho$ 是任意初始系统密度矩阵。实际第 $N$ 个时刻的局部输入只遍历 $M_{A_N}$ 的像，不能重新视为全部密度矩阵。沿用第11章的固定投影测量 $\{Q_b\}$，定义
$$
\alpha_{Q,N}=\sup_\rho\operatorname{TV}
\bigl(C_Q(\sigma_{N+1}),C_Q(\sigma_N)\bigr).
$$

**定理 12.1（可达前缀的精确读数缺陷）。** 有
$$
\alpha_{Q,N}
=\max_{B\subseteq\mathcal B}
\left\|\overline{A_N}\odot(\overline{C_{N+1}}-J)\odot Q_B\right\|_\infty
\le\delta_Q(C_{N+1}).
$$
其为零当且仅当对全部 $B,x,y$ 有
$$
A_N(x,y)\bigl(c_{xy}^{N+1}-1\bigr)(Q_B)_{xy}=0.
$$
这也恰好是以 $Q_B\otimes I_{E_{1:N}}$ 比较 $\operatorname{tr}_{E_{N+1}}\rho_{N+1}$ 与 $\rho_N$ 的最坏事件缺陷。

证明。系统边缘递推为 $\sigma_{N+1}=M_{C_{N+1}}M_{A_N}(\rho)$。把固定事件概率差通过两次对偶拉回初态，缺陷算子为
$$
M_{A_N}^*\bigl(M_{C_{N+1}}^*(Q_B)-Q_B\bigr)
=\overline{A_N}\odot(\overline{C_{N+1}}-J)\odot Q_B.
$$
使用第11.2节的有限事件最大值与Hermitian范数公式得到等式。单位保持正映射对Hermitian算子的算子范数收缩，给出上界。范数为零等价于每个矩阵元为零；系数的复共轭不影响其是否为零，得到所列判据。对全部旧记录取迹，再用偏迹恒等式，得到最后的联合空间比较。证毕。

例如 $A_N(x,y)=0$ 时，这一对历史已对局部读数不可见；后来 $c_{xy}^{N+1}\ne1$ 不再使它产生局部概率变化。这不意味着联合系统中的那一对历史已被删除。

### 12.3 端点恢复与每个前缀都一致

**定理 12.2（有限窗口的逐步判据）。** 固定整数 $0\le N_0<K$。要求对所有初态和窗口内每对相邻时刻都有
$$
C_Q(\sigma_{N+1})=C_Q(\sigma_N)
\qquad(N_0\le N<K),
$$
当且仅当每个满足 $A_{N_0}(x,y)(Q_B)_{xy}\ne0$ 的 $B,x,y$ 均满足
$$
c_{xy}^{t}=1\qquad(N_0<t\le K).
$$
特别地，从 $N_0=0$ 开始要求全部前缀一致时，$Q_B$ 的非零矩阵元必须位于各步关系 $c_{xy}^{t}=1$ 的交集内。

证明。固定一个所列非零矩阵元。定理12.1在 $N_0$ 迫使首个新因子为 $1$，故下一步累计因子仍等于原非零值；归纳迫使所有后续因子均为 $1$。若初始窗口因子或投影矩阵元为零，该对矩阵元在以后的Schur作用下持续为零，不产生条件。反向逐项代入定理12.1。证毕。

若只要求对所有初态比较 $\sigma_K$ 与 $\sigma_0$，条件则仅为 $A_K(x,y)=1$ 覆盖全部粗事件的非零支撑。二标签取两个相关矩阵
$$
C_1=C_2=\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
\qquad A_2=J_2.
$$
它们均为合法的秩一相关矩阵。对 $Q_\pm$ 测量和初态 $|+\rangle$，三个时刻的 $+$ 概率依次为 $1,0,1$。末端恢复精确成立，中间记录节点的变化仍为 $1$。各步记录不区分标签，变化完全来自相位；有模长严格小于 $1$ 的因子时，后续模长至多为 $1$ 的因子不能将该累计乘积恢复为 $1$。

### 12.4 固定时刻之后的有限窗口预算

定义端点比较
$$
\alpha_Q(N,M)=\sup_\rho\operatorname{TV}
\bigl(C_Q(\sigma_M),C_Q(\sigma_N)\bigr),\qquad N<M.
$$
定理12.1的同一对偶计算直接给出
$$
\alpha_Q(N,M)=\max_B
\left\|\overline{A_N}\odot
(\overline{C_{N+1}\odot\cdots\odot C_M}-J)\odot Q_B\right\|_\infty.
$$
由同一初态轨迹上的三角不等式还有
$$
\alpha_Q(N,M)\le\min\left\{1,\sum_{t=N}^{M-1}\alpha_{Q,t}\right\}.
$$

**推论 12.3（纯记录尾窗的统一充分界）。** 令 $d\ge2$、$q_N=\max_{x\ne y}|A_N(x,y)|$。对任意有限 $M>N$、任意有限旁参考 $R$ 以及任意初态 $\omega_{SR}$，有
$$
\mathsf d\bigl((M_{A_M}\otimes\operatorname{id}_R)(\omega),
(M_{A_N}\otimes\operatorname{id}_R)(\omega)\bigr)
\le\min\{1,(d-1)q_N\}.
$$
所以任意系统粗测量也满足 $\alpha_Q(N,M)\le\min\{1,(d-1)q_N\}$，该界不随这个有限尾窗的长度增长。

证明。每个相关矩阵元素模长至多为 $1$，故 $q_M\le q_N$。以 $(\Delta\otimes\operatorname{id}_R)(\omega)$ 为共同中间态，两次应用定理9.4，得到 $(d-1)(q_N+q_M)/2\le(d-1)q_N$；迹距离至多为 $1$。测量收缩给出粗分布界。证毕。

本推论复用定理9.4的界，不宣称常数在所有维数都最优。其条件是同一指针基上只继续记录；任意Hamiltonian控制、重新访问旧记录或反馈均不能不加检验地代入。这一有限尾窗结论也不把单时刻边缘提升为多时刻联合历史分布。

### 12.5 可访问旧记录后的联合见证

**命题 12.4（局部不可见与联合可见可以并存）。** 保留全部旧记录，令 $W_N|x\rangle=e^{i\Theta_x(N)}|x\rangle\otimes|e_x^{\le N}\rangle$。由于系统标签正交，$W_N$ 为等距映射，且
$$
\rho_N=W_N\rho W_N^\dagger,\qquad
\operatorname{tr}_{E_{N+1}}\rho_{N+1}
=W_NM_{C_{N+1}}(\rho)W_N^\dagger.
$$
对任意系统投影测量 $\{Q_b\}$，在像空间上选择 $R_b=W_NQ_bW_N^\dagger$，并把 $I-W_NW_N^\dagger$ 加入其中一个输出使其成为全空间投影测量。则此联合测量的最坏读数变化恰为 $\delta_Q(C_{N+1})$，不带局部读数中的既有记录因子 $A_N$。

证明。新Schur通道只乘系统矩阵单位的系数，逐项作用于 $W_N\rho W_N^\dagger$ 得到第二式。两态均支撑在 $W_N$ 的像内，因而补空间输出对它们的概率为零。用 $W_N^\dagger W_N=I$ 将联合测量拉回系统，即为第11章的比较。证毕。

最小实例取二标签、第一步为正交记录、初态 $|+\rangle$，于是
$$
\rho_1=|\Phi^+\rangle\langle\Phi^+|,\qquad
|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2,
\qquad \sigma_1=I_2/2.
$$
再写入并忽略一个正交记录，有
$$
\operatorname{tr}_{E_2}\rho_2
=\tfrac12(|00\rangle\langle00|+|11\rangle\langle11|),
\qquad \sigma_2=I_2/2.
$$
事实上这一两步模型对任意初态都满足 $\sigma_2=\sigma_1$。但联合事件 $|\Phi^+\rangle\langle\Phi^+|$ 的概率由 $1$ 变成 $1/2$。局部的精确稳定与旧记录可访问时的联合变化相容；稳定性必须标明观察者可以访问哪些系统。

本章为第9—11章有限模型内的推导与勘注。所用偏迹、Schur对偶和谱范数事实沿用前章及其Watrous基础文献；没有新增Lean声明，也不把这些有限读数判据解释为唯一结果或普适经典性的证明。

## 追加锚（新终端）

## 13. 同一次读取中的经典预测与未知相位恢复

第 9–12 章分别刻画记录的前缀一致性、粗读数预测、记录作用的可见缺陷与访问条件。本章固定已经写入的有限记录，研究一个联合任务：同一次处理既留下经典预测输出，又恢复未知输入的相干；两项目标由同一个读取仪器实现。

读取前的相位访问量不能直接充当读取后的恢复能力。本章给出一般有限关联记录下的精确半正定规划、乘积记录下的尖锐边界及其访问成本。这里的推进相对于本文已有模型而言，不主张基础矩阵方法或信息与干扰关系的文献优先性。

### 13.1 有限记录库与指定预测任务

**定义 13.1（记录、访问划分与预测误差）。** 固定二标签系统

$$
\mathcal H_S=\mathbb C^2,
\qquad
P_x=|x\rangle\langle x|,
\qquad x\in\{0,1\}.
$$

输入是未知密度矩阵，允许与任意有限维参考系统纠缠；协议不能依赖输入的振幅、相位或其纯化。令记录指标集为 $\mathsf I=\{1,\ldots,r\}$，其中 $r\ge0$，并给定

$$
\mathcal H_E=
\left(\bigotimes_{j\in\mathsf I}\mathcal H_{E_j}\right)
\otimes\mathcal H_{B_0}.
$$

所有记录因子均为非零有限维 Hilbert 空间。固定单位条件记录向量 $E_0,E_1\in\mathcal H_E$，写入等距映射为

$$
W|x\rangle=|x\rangle|E_x\rangle.
$$

全部准备、写入、读取与反馈都发生在给定有限时段内，使用有限步操作。一般的 $E_x$ 可以具有跨单元关联，不预设独立时间记录的乘积结构。

给定允许访问的指标集 $\mathcal J_{\mathrm{acc}}\subseteq\mathsf I$。选择 $J\subseteq\mathcal J_{\mathrm{acc}}$ 后，记

$$
\mathcal H_{F_J}=\bigotimes_{j\in J}\mathcal H_{E_j},
\qquad
\mathcal H_{B_J}=
\left(\bigotimes_{j\in\mathsf I\setminus J}\mathcal H_{E_j}\right)
\otimes\mathcal H_{B_0}.
$$

张量顺序固定，空张量空间为 $\mathbb C$。暂固定 $J$，简写 $F,B$，并令

$$
\sigma_x=\operatorname{tr}_B|E_x\rangle\langle E_x|,
\qquad
T=\operatorname{tr}_B|E_0\rangle\langle E_1|.
$$

$T$ 一般不是 Hermitian 矩阵。写入后对 $B$ 取部分迹，得到

$$
\mathcal W_F(\rho)=
\begin{pmatrix}
\rho_{00}\sigma_0&\rho_{01}T\\
\rho_{10}T^\dagger&\rho_{11}\sigma_1
\end{pmatrix}.
$$

固定有限个预测时刻

$$
0\le\tau_1<\cdots<\tau_N\le\tau_*<\infty,
\qquad N\ge1.
$$

第 $k$ 个理想任务由 CPTP 通道 $\Psi_k$ 和有限 POVM $(Q_{k,b})_{b\in\mathsf Y_k}$ 指定。定义

$$
A_{k,b}=\Psi_k^*(Q_{k,b}),
\qquad
p_{k,b}(\rho)=\operatorname{tr}(\rho A_{k,b}).
$$

这些概率对应未插入本章读取与恢复操作的指定理想过程，输入仍为 $\rho$。若当前标签也是必需读数，应把 $\Psi=\operatorname{id}$、$Q_x=P_x$ 加入任务清单。

预测输出保存在有限经典寄存器

$$
\mathsf Z=\prod_{k=1}^N\mathsf Y_k.
$$

只在 $F$ 上读取 POVM $(M_z)_{z\in\mathsf Z}$。令

$$
p_z(x)=\operatorname{tr}(M_z\sigma_x).
$$

第 $k$ 个预测坐标的分布为

$$
q_{k,b}^M(\rho)=
\sum_{x=0}^1\rho_{xx}
\sum_{z:z_k=b}p_z(x).
$$

定义最坏预测误差

$$
e_k(M)=\sup_\rho\operatorname{TV}\bigl(p_k(\rho),q_k^M(\rho)\bigr),
\qquad
\operatorname{TV}(p,q)=\frac12\sum_b|p_b-q_b|.
$$

这里比较概率分布，不要求一个预测样本等于同次运行中尚未产生的未来随机结果。多个预测坐标也不声称复现非交换测量的真实联合历史分布。

### 13.2 留下经典输出后的恢复操作

**定义 13.2（读取与反馈协议）。** 先在 $F$ 上实施读取仪器，把结果 $z$ 留在经典寄存器 $Z$。允许保留仪器的有限维量子余系统 $K$，随后按 $z$ 实施受控酉

$$
U_z=P_0\otimes U_{z,0}+P_1\otimes U_{z,1}.
$$

最后丢弃量子余系统，保留经典输出。系统只充当相干控制，不直接测量系统标签；不在读取前利用系统重写记录，不访问 $B$，不后选择，也不相干重合并已经留下的经典输出。全部随机分支都计入无条件输出。

这类协议包含规范实现：结果 $z$ 的读取算子为 $\sqrt{M_z}$，余系统仍为 $F$，随后实施上述受控酉。也允许同一读取结果对应多个 Kraus 算子。

取系统边缘后，整个写入、读取与反馈协议保持每个 $P_x$，因此具有形式

$$
\mathcal R(\rho)=
\begin{pmatrix}
\rho_{00}&\kappa\rho_{01}\\
\overline\kappa\rho_{10}&\rho_{11}
\end{pmatrix}.
$$

定义恢复误差

$$
\eta(\mathcal R)=\frac12\|\mathcal R-\operatorname{id}_S\|_\diamond.
$$

该误差要求恢复所有未知输入及其有限维纠缠参考，不能用重新制备一个已知相干态替代。计算系统边缘时忽略 $Z$，并不表示实际协议没有留下该经典输出。

### 13.3 一般关联记录的精确联合优化

对事件 $B'\subseteq\mathsf Y_k$，定义

$$
A_{k,B'}=\sum_{b\in B'}A_{k,b},
\qquad
L_{k,B'}(M)=
\sum_{x=0}^1
\left(\sum_{z:z_k\in B'}\operatorname{tr}(M_z\sigma_x)\right)P_x.
$$

下文 $I_F$ 与 $I_S$ 分别表示两个空间的恒等算符，与记录指标集 $\mathsf I$ 不同。

**定理 13.3（同一仪器的精确半正定规划）。** 给定非负预测预算 $\boldsymbol\varepsilon=(\varepsilon_1,\ldots,\varepsilon_N)$。若预测要求可行，则定义 13.2 中满足 $e_k(M)\le\varepsilon_k$ 的最小恢复误差恰为

$$
\eta_J^*(\boldsymbol\varepsilon)
=\frac{1-v_J^*(\boldsymbol\varepsilon)}2,
$$

其中 $v_J^*$ 是以下有限半正定规划的最大值：

$$
\begin{aligned}
\text{最大化}\quad&
\operatorname{Re}\sum_{z\in\mathsf Z}\operatorname{tr}(TX_z),\\
\text{满足}\quad&
\sum_{z\in\mathsf Z}M_z=I_F,\\
&\begin{pmatrix}M_z&X_z\\X_z^\dagger&M_z\end{pmatrix}\succeq0
&&\text{对所有 }z\in\mathsf Z,\\
&-\varepsilon_k I_S
\preceq A_{k,B'}-L_{k,B'}(M)
\preceq\varepsilon_k I_S
&&\text{对所有 }k\text{ 及 }B'\subseteq\mathsf Y_k.
\end{aligned}
$$

变量为 Hermitian 矩阵 $M_z$ 和任意复矩阵 $X_z$。可行时最大值达到，且 $0\le v_J^*\le1$；不可行时定义 $\eta_J^*=+\infty$。因此，对 $0\le\bar\eta\le1/2$，联合目标可达当且仅当上述约束连同

$$
\operatorname{Re}\sum_z\operatorname{tr}(TX_z)\ge1-2\bar\eta
$$

可行。这是同一协议的精确判据。

证明。首先，将第10.2节的事件范数论证用于这些预测效应，得到

$$
\begin{aligned}
e_k(M)
&=\sup_\rho\max_{B'\subseteq\mathsf Y_k}
\left|\operatorname{tr}\!\left(\rho\,[A_{k,B'}-L_{k,B'}(M)]\right)\right|\\
&=\max_{B'\subseteq\mathsf Y_k}
\|A_{k,B'}-L_{k,B'}(M)\|_\infty.
\end{aligned}
$$

因此规划中的两侧矩阵不等式恰好表达全部预测要求。这也覆盖未来效应 $A_{k,b}$ 具有非对角元的情形。

其次，固定 POVM。规范读取与受控酉给出的相干乘子为

$$
\kappa=
\sum_z\operatorname{tr}\!\left(
U_{z,0}\sqrt{M_z}\,T\sqrt{M_z}\,U_{z,1}^\dagger
\right).
$$

记 $T_z=\sqrt{M_z}\,T\sqrt{M_z}$。有限奇异值分解给出

$$
\max_{U\text{ 酉}}\operatorname{Re}\operatorname{tr}(T_zU)
=\|T_z\|_1.
$$

每个结果的相对酉 $U_{z,1}^\dagger U_{z,0}$ 可独立选择，使所有贡献同时为非负实数。因此固定读取 POVM 的最大恢复乘子为

$$
v(M)=\sum_z\|\sqrt{M_z}\,T\sqrt{M_z}\|_1.
$$

一般读取仪器在结果 $z$ 下可由 Stinespring 算子

$$
V_z:F\longrightarrow K\otimes A,
\qquad V_z^\dagger V_z=M_z
$$

表示，其中 $A$ 是可能丢弃的仪器余环境。在 $\operatorname{supp}M_z$ 上作极分解 $V_z=J_z\sqrt{M_z}$，其中 $J_z$ 等距。反馈贡献可写成

$$
\operatorname{tr}(T_zK_z),
\qquad
K_z=J_z^\dagger
\bigl(U_{z,1}^\dagger U_{z,0}\otimes I_A\bigr)J_z,
\qquad
\|K_z\|_\infty\le1.
$$

把 $K_z$ 在支撑正交补上延拓为零即可。因此该贡献的绝对值不超过 $\|T_z\|_1$。规范实现已经达到上界，一般读取仪器不能提高固定 POVM 的最优值。

再次，对任意 $M\succeq0$，标准块正性分解给出

$$
\begin{pmatrix}M&X\\X^\dagger&M\end{pmatrix}\succeq0
\iff
X=\sqrt M\,K\sqrt M
\quad\text{其中 }\|K\|_\infty\le1.
$$

当 $M$ 正定时，以 $\operatorname{diag}(M^{-1/2},M^{-1/2})$ 作合同变换，归结为块矩阵 $\begin{pmatrix}I&K\\K^\dagger&I\end{pmatrix}$ 的正性，即 $I-K^\dagger K\succeq0$。当 $M$ 秩亏时，块正性先迫使 $X$ 与 $X^\dagger$ 消去 $\ker M$，再在支撑空间应用同一论证。于是由迹的循环性和迹范数对偶，

$$
\max_{\left(\begin{smallmatrix}M&X\\X^\dagger&M\end{smallmatrix}\right)\succeq0}
\operatorname{Re}\operatorname{tr}(TX)
=\|\sqrt M\,T\sqrt M\|_1.
$$

逐结果应用该等式，便得到所列半正定规划。对任意规划可行点，都可固定其 $M_z$，再选择逐结果的极分解酉，构造目标值至少同样好的实际协议。

最后，设 $\Delta=\mathcal R-\operatorname{id}_S$，令任意系统与有限参考上的算符写成 $A=[A_{xy}]$。取 $Z_S=P_0-P_1$，其非对角部分为

$$
A_{\mathrm{off}}
=\frac12\bigl(A-(Z_S\otimes I)A(Z_S\otimes I)\bigr),
\qquad
\|A_{\mathrm{off}}\|_1\le\|A\|_1.
$$

非对角块矩阵的奇异值给出

$$
\begin{aligned}
\|(\Delta\otimes\operatorname{id})(A)\|_1
&=|1-\kappa|\bigl(\|A_{01}\|_1+\|A_{10}\|_1\bigr)\\
&=|1-\kappa|\,\|A_{\mathrm{off}}\|_1\\
&\le|1-\kappa|\,\|A\|_1.
\end{aligned}
$$

无参考输入 $|+\rangle\langle+|$ 达到上界，故

$$
\eta(\mathcal R)=\frac{|1-\kappa|}{2}.
$$

每个结果的正块矩阵

$$
\begin{pmatrix}
\sqrt{M_z}\sigma_0\sqrt{M_z}&T_z\\
T_z^\dagger&\sqrt{M_z}\sigma_1\sqrt{M_z}
\end{pmatrix}\succeq0
$$

由 $\mathcal W_F(|+\rangle\langle+|)$ 的正性得到。块正性分解与 Hilbert–Schmidt Cauchy–Schwarz 不等式因而给出

$$
\|T_z\|_1\le\sqrt{p_z(0)p_z(1)},
\qquad
v(M)\le\sum_z\sqrt{p_z(0)p_z(1)}\le1.
$$

任意协议满足 $|\kappa|\le v(M)\le1$；规范最优反馈可使 $\kappa=v(M)\ge0$，于是固定 POVM 的最小恢复误差为 $(1-v(M))/2$。

规划可行集闭且有界：POVM 满足 $0\preceq M_z\preceq I_F$，块正性同时约束 $X_z$；故可行时最大值达到。取全部 $X_z=0$ 可知最优值非负。证毕。

### 13.4 访问成本与后续读数保证

**推论 13.4（有限访问成本与恢复后的边缘读数）。** 给定访问成本 $c_j>0$，固定全部已经写入的记录，只优化访问集合和读取与反馈协议，则精确最小联合成本为

$$
C^*(\boldsymbol\varepsilon,\bar\eta)
=\min_{\substack{J\subseteq\mathcal J_{\mathrm{acc}}\\
\eta_J^*(\boldsymbol\varepsilon)\le\bar\eta}}
\sum_{j\in J}c_j.
$$

空集成本为零，不可行时取 $+\infty$。外层为有限子集选择，内层为定理 13.3 的精确规划。

若一个协议达到预测预算 $\boldsymbol\varepsilon$ 和恢复预算 $\bar\eta$，并在恢复后的系统上实施同一个理想后续过程，则

$$
\sup_\rho
\operatorname{TV}\bigl(q_k^M(\rho),p_k(\mathcal R(\rho))\bigr)
\le\min\{1,\varepsilon_k+\bar\eta\}.
$$

证明。成本公式逐一应用定理 13.3。第二式以 $p_k(\rho)$ 为中间分布，使用通道与测量对迹距离的收缩性，以及三角不等式。证毕。

该结论比较两个边缘分布，不控制预测输出与后续结果的逐样本相符概率。它也不是标签保持性定理：$\Psi_k$ 仍可能使标签翻转。成本只计指定已写入记录的访问；未访问的记录仍属于 $B_J$，不能当作从未写入。

有限枚举不意味着大规模计算高效。任意实数输入也不自动具有精确可计算的表示；浮点求解器的状态不能代替可核查的可行性与最优性证据。

### 13.5 乘积记录下的尖锐预测与恢复边界

**定理 13.5（乘积记录的精确联合前沿）。** 假设固定访问划分下的条件记录满足

$$
E_x=f_x\otimes b_x,
\qquad
s=|\langle f_1,f_0\rangle|,
\qquad
b=|\langle b_1,b_0\rangle|,
$$

各向量均为单位向量。固定一个未来二值读数，其 Heisenberg 效应为

$$
A_1=\frac{1-d}{2}P_0+\frac{1+d}{2}P_1,
\qquad
A_0=I_S-A_1,
\qquad0\le d\le1.
$$

例如，先读取指针，再以概率 $(1-d)/2$ 翻转输出，就实现该任务。取预测误差上限 $0\le\varepsilon\le1/2$，令

$$
t=(d-2\varepsilon)_+,
\qquad
(u)_+=\max\{u,0\}.
$$

则预测要求可行当且仅当

$$
t\le\sqrt{1-s^2}.
$$

可行时，留下该经典预测输出后的精确最优值为

$$
\boxed{
v^*(\varepsilon)=b\sqrt{1-t^2},
\qquad
\eta^*(\varepsilon)=\frac{1-b\sqrt{1-t^2}}2.
}
$$

等价地，对 $0\le\nu\le1$，预测误差至多为 $\varepsilon$ 且恢复乘子至少为 $\nu$ 的充要条件是

$$
\boxed{
s^2+t^2\le1,
\qquad
\nu^2\le b^2(1-t^2).
}
$$

这里恢复乘子由最优反馈调成非负实数；后一目标等价于恢复误差至多为 $(1-\nu)/2$。

证明。二输出预测器由效应 $M_1$ 给出。写 $q_x=\langle f_x,M_1f_x\rangle$。目标与预测效应均对角，故误差要求等价于

$$
\left|q_0-\frac{1-d}{2}\right|\le\varepsilon,
\qquad
\left|q_1-\frac{1+d}{2}\right|\le\varepsilon.
$$

当 $t>0$ 时，这迫使 $q_1-q_0\ge t$。测量输出的分布差不能超过两纯态的迹距离 $\sqrt{1-s^2}$，得到可行性的必要条件；当 $t=0$ 时，该必要条件自动成立。

由于

$$
T=\langle b_1,b_0\rangle\,|f_0\rangle\langle f_1|,
$$

定理 13.3 给出

$$
v(M)=b\left[\sqrt{q_0q_1}+\sqrt{(1-q_0)(1-q_1)}\right].
$$

对任意概率分布 $p,q$，令

$$
\mathcal B(p,q)=\sum_z\sqrt{p_zq_z}.
$$

Cauchy–Schwarz 不等式给出

$$
\begin{aligned}
\operatorname{TV}(p,q)
&=\frac12\sum_z|\sqrt{p_z}-\sqrt{q_z}|(\sqrt{p_z}+\sqrt{q_z})\\
&\le\sqrt{1-\mathcal B(p,q)^2}.
\end{aligned}
$$

因此 $v(M)\le b\sqrt{1-t^2}$。当 $t=0$ 时，该上界就是 $b$。

下面构造达到上界的同一仪器。令 $D=\sqrt{1-s^2}$。若 $D>0$，在两记录张成空间上取

$$
S=\operatorname{sign}\bigl(|f_0\rangle\langle f_0|-|f_1\rangle\langle f_1|\bigr),
$$

在其正交补上取零。括号内差矩阵在该二维空间的迹为零、行列式为 $-(1-s^2)$，故特征值为 $D,-D$。其符号矩阵等于差矩阵除以 $D$，从而

$$
\langle f_0,Sf_0\rangle=D,
\qquad
\langle f_1,Sf_1\rangle=-D.
$$

取

$$
M_0=\frac12\left(I_F+\frac tD S\right),
\qquad
M_1=\frac12\left(I_F-\frac tD S\right).
$$

由 $t\le D$，它们构成 POVM，并产生

$$
q_0=\frac{1-t}{2},
\qquad
q_1=\frac{1+t}{2}.
$$

预测误差为 $(d-t)/2\le\varepsilon$，两个输出分布的 $\mathcal B$ 值恰为 $\sqrt{1-t^2}$。再采用定理 13.3 的逐结果受控酉，即达到恢复上界。

若 $D=0$，可行性要求 $t=0$，取 $M_0=M_1=I_F/2$。若 $b=0$，所有协议的最大恢复乘子为零，原式仍成立。证毕。

当预测任务就是当前标签，或经已知标签置换后再将输出重标记为当前标签时，$d=1$。此时

$$
s^2\le4\varepsilon(1-\varepsilon),
\qquad
v^*(\varepsilon)=2b\sqrt{\varepsilon(1-\varepsilon)}.
$$

这条前沿同时计入已经不可访问的记录，以及本次必须留下的预测结果。

### 13.6 已写入记录库的精确成本实例

**推论 13.6（乘积记录的访问成本）。** 若整个条件记录为乘积

$$
E_x=
\left(\bigotimes_{j\in\mathsf I}f_{j,x}\right)\otimes b_x^{(0)},
$$

记

$$
a_0=|\langle b_1^{(0)},b_0^{(0)}\rangle|,
\qquad
a_j=|\langle f_{j,1},f_{j,0}\rangle|.
$$

则对每个访问集合

$$
s_J=\prod_{j\in J}a_j,
\qquad
b_J=a_0\prod_{j\in\mathsf I\setminus J}a_j.
$$

对定理 13.5 的任务，恢复乘子目标为 $\nu$ 时，精确成本为

$$
C_{\mathrm{vis}}^*(\varepsilon,\nu)
=\min_{\substack{J\subseteq\mathcal J_{\mathrm{acc}}\\
s_J^2+t^2\le1\\
\nu^2\le b_J^2(1-t^2)}}
\sum_{j\in J}c_j,
\qquad
C_{\mathrm{vis}}^*(\varepsilon,\nu)
=C^*\!\left(\varepsilon,\frac{1-\nu}{2}\right).
$$

空积为一，零重叠允许，不可行时取 $+\infty$。

证明。每个访问划分都满足定理 13.5 的乘积假设，将其两条充要条件代入有限成本最小化即可。证毕。

例如取两个均可访问的已写入单元，

$$
c_1=c_2=1,
\qquad
a_1=a_2=\frac35,
\qquad a_0=1.
$$

要求预测标签，并取

$$
d=1,
\qquad
\varepsilon=\frac1{10},
\qquad
\nu=\frac12,
\qquad
t=\frac45.
$$

全部访问选择的精确比较为：

| 访问集合 | 成本 | $s_J$ | $b_J$ | 预测要求达标 | 预测约束下最大恢复乘子 |
| --- | ---: | ---: | ---: | --- | ---: |
| $\varnothing$ | $0$ | $1$ | $9/25$ | 不可行 | 不适用 |
| $\{1\}$ 或 $\{2\}$ | $1$ | $3/5$ | $3/5$ | 可行 | $9/25$ |
| $\{1,2\}$ | $2$ | $9/25$ | $1$ | 可行 | $3/5$ |

由于 $9/25<1/2\le3/5$，联合最小成本恰为 $2$；仅要求相同预测精度时，最小成本为 $1$。表中各项由充要条件与达到边界的测量构造得到，是该实例的解析最优性证明，不是数值求解器的输出。

### 13.7 两个尖锐反例

**反例 13.7（分别最优不等于同次可达）。** 令全部记录可访问，

$$
E_0=|0\rangle_F,
\qquad
E_1=|1\rangle_F,
\qquad
\mathcal H_B=\mathbb C.
$$

单独优化读取时可以零错误区分标签；单独优化恢复时可以完全撤销记录写入。但要求同一次操作留下零错误标签输出时，定理 13.5 给出

$$
d=1,
\qquad
\varepsilon=0,
\qquad
v^*=0,
\qquad
\eta^*=\frac12.
$$

该恢复误差必要且可达。相反，允许标签预测误差为 $1/2$ 时，独立均匀随机输出配合受控擦除给出 $v^*=1$、$\eta^*=0$。因此读取前的两个单独最优值不能被当作同一个协议的性能。

**反例 13.8（相同读取前标量不足以决定联合前沿）。** 两个模型均取二维 $F$ 与二维 $B$，预测当前标签，容许最坏预测误差为 $1/10$。

模型甲取

$$
E_0=\frac{3|00\rangle+|11\rangle}{\sqrt{10}},
\qquad
E_1=\frac{|00\rangle+3|11\rangle}{\sqrt{10}}.
$$

直接取部分迹得到

$$
\sigma_0=\operatorname{diag}(9/10,1/10),
\qquad
\sigma_1=\operatorname{diag}(1/10,9/10),
\qquad
T=\frac3{10}I_2.
$$

读取前的两个标量为

$$
D_F:=\frac12\|\sigma_0-\sigma_1\|_1=\frac45,
\qquad
V_F:=\|T\|_1=\frac35.
$$

计算基读取对两个标签的错误均为 $1/10$；对任何 POVM，

$$
v(M)=\sum_z\left\|\frac3{10}M_z\right\|_1
=\frac3{10}\operatorname{tr}I_2
=\frac35.
$$

因此模型甲的精确联合最优值为

$$
v_A^*\!\left(\frac1{10}\right)=\frac35,
\qquad
\eta_A^*=\frac15.
$$

模型乙取乘积记录

$$
f_0=b_0=|0\rangle,
\qquad
f_1=b_1=\frac35|0\rangle+\frac45|1\rangle,
\qquad
E_x=f_x\otimes b_x.
$$

它同样满足 $D_F=4/5$、$V_F=3/5$，但定理 13.5 给出

$$
v_B^*\!\left(\frac1{10}\right)
=\frac35\sqrt{1-\left(\frac45\right)^2}
=\frac9{25},
\qquad
\eta_B^*=\frac8{25}.
$$

两个模型具有相同的可访问标签迹距离与读取前相位访问量，而且都能达到指定的最坏预测误差，却具有不同的精确联合恢复误差。差别来自 $T$ 与读取效应的相对结构：甲的 $T$ 是正的标量矩阵，乙的 $T$ 是不同记录向量之间的秩一算子。因此，一般关联记录的联合预算不能只由 $D_F$、$V_F$ 或记录数量决定。

### 13.8 范围与方法归属

本章的最优性限定于先读记录、留下经典结果、再以系统标签相干控制的恢复类。不包括读取前任意重编码系统、量子纠错编码、访问不可见因子、后选择，或重新取得全部经典输出副本的相干控制。

精确规划针对二标签系统。记录维数、单元数量、预测输出集合与预测时刻都是任意给定的有限对象。多标签情形中，不同标签对各自最优的反馈酉未必兼容，不能把逐对边界自动拼成全系统可达定理。

恢复误差控制带有限参考的系统通道稳定性；预测误差控制指定读数的边缘分布。两者不保证标签不变、记录永久存活或预测样本等于真实未来随机结果。控制能量、带宽、脉冲时长与噪声实现成本均未纳入本章预算。

块正性与收缩因子分解是标准有限矩阵方法，见 John Watrous，[《Simpler semidefinite programs for completely bounded norms》](https://arxiv.org/html/1207.5726v2)，§2.1，Lemma 2。两路信息与干涉可见度的约束属于已有互补性背景，见 Berthold-Georg Englert，[《Fringe Visibility and Which-Way Information: An Inequality》](https://doi.org/10.1103/PhysRevLett.77.2154)，*Physical Review Letters* **77**，2154–2157（1996）。本章的联合任务、规划等价性与成本实例由正文中的有限模型推导承担。

本章不构造无限时间或无限张量积态，不推断项目一致性，不主张普适经典现实、唯一全局结果、实验验证或 Lean 验证。

## 追加锚（新终端）

## 14. 多标签相位环与写入后的最优恢复

### 14.1 有限记录与写入后的恢复类

**定义 14.1（不访问记录的写入后恢复误差）。** 固定有限整数 $d\ge2$，系统空间为 $\mathcal H_S=\mathbb C^d$，标签为 $x\in\{0,\ldots,d-1\}$。不可访问记录空间 $\mathcal H_B$ 非零且有限维，条件记录 $e_x\in\mathcal H_B$ 均为单位向量。写入等距映射和相关矩阵为

$$
W|x\rangle=|x\rangle|e_x\rangle,
\qquad
C_{xy}=\langle e_y,e_x\rangle.
$$

因此 $C\succeq0$、$C_{xx}=1$；对 $B$ 取部分迹得到第 8.3 条的 Schur 通道

$$
M_C(\rho)=C\odot\rho.
$$

记录已写入后，允许在系统上实施任意 CPTP 恢复通道 $\mathcal R:\mathcal L(\mathcal H_S)\to\mathcal L(\mathcal H_S)$。恢复可以使用与未知输入及 $B$ 初始无关的有限维辅助系统、有限结果的仪器和按结果控制的后续操作；全部结果分支都计入无条件系统输出。恢复不访问 $B$，不在写入前编码，不后选择；若产生经典输出，本章不要求该输出满足额外预测任务。

定义

$$
\eta(C)
= \inf_{\mathcal R\ {\rm CPTP}}
\frac12\|\mathcal R\circ M_C-\operatorname{id}_S\|_\diamond.
$$

输入是未知密度矩阵，允许与任意有限维参考系统纠缠；$\mathcal R$ 不依赖输入或参考上的信息。上述误差比较写入前输入与写入、丢弃记录及恢复之后的系统通道，要求整个未知输入的恢复，而非某个已知状态的重新制备。操作和辅助系统均有限，不引入无限次恢复过程。

当第 13 章的可访问记录空间取 $F=\mathbb C$ 时，其仪器与标签控制反馈合成的无条件系统通道属于此恢复类。此处还允许混合标签布居的系统通道，且不对任何经典输出施加预测约束。若允许访问非平凡记录 $F$，则恢复作用域包含记录空间，不属于本定义。带参考误差沿用第 13.2 节的半 diamond 范数约定，比较目标固定为恒等通道。

Schur 通道的完全正性、保迹条件与对角 Kraus 表示见 John Watrous，[《The Theory of Quantum Information》](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，§4.1.3，命题 4.17–4.18 与定理 4.19；保 Hermitian 映射的 diamond 范数可在纯态输入及同维参考上达到，见同书定理 3.51、式 (3.291)。

### 14.2 任意系统恢复的谱下界

**定理 14.2（相关矩阵最大特征值给出的恢复障碍）。** 在定义 14.1 中，记 $\lambda_{\max}(C)$ 为 $C$ 的最大特征值。对每个允许的恢复通道 $\mathcal R$，都有

$$
\frac12\|\mathcal R\circ M_C-\operatorname{id}_S\|_\diamond
\ge
1-\frac{\lambda_{\max}(C)}d.
$$

从而

$$
\eta(C)\ge1-\frac{\lambda_{\max}(C)}d.
$$

此界允许 $\mathcal R$ 混合标签布居；不以对角反馈或布居保持为前提。

证明。 取一个 $d$ 维参考系统 $A$ 及归一化最大纠缠态

$$
|\Omega_d\rangle
=\frac1{\sqrt d}\sum_{x=0}^{d-1}|x\rangle_S|x\rangle_A.
$$

令 $(A_\alpha)_\alpha$ 为 $\mathcal R$ 的有限 Kraus 族，满足 $\sum_\alpha A_\alpha^\dagger A_\alpha=I_S$，并定义

$$
b_{\alpha,x}=\overline{(A_\alpha)_{xx}}.
$$

恢复输出与目标最大纠缠态的重叠为

$$
\begin{aligned}
f_{\mathcal R}
&=
\langle\Omega_d|
[(\mathcal R\circ M_C)\otimes\operatorname{id}_A]
(|\Omega_d\rangle\langle\Omega_d|)
|\Omega_d\rangle\\
&=
\frac1{d^2}\sum_{\alpha,x,y}
C_{xy}(A_\alpha)_{xx}\overline{(A_\alpha)_{yy}}\\
&=
\frac1{d^2}\sum_\alpha b_\alpha^\dagger Cb_\alpha.
\end{aligned}
$$

由 $C\preceq\lambda_{\max}(C)I_d$ 和 Kraus 完备关系，

$$
\begin{aligned}
f_{\mathcal R}
&\le
\frac{\lambda_{\max}(C)}{d^2}
\sum_{\alpha,x}|(A_\alpha)_{xx}|^2\\
&\le
\frac{\lambda_{\max}(C)}{d^2}
\sum_{\alpha,x,y}|(A_\alpha)_{yx}|^2\\
&=
\frac{\lambda_{\max}(C)}{d^2}
\operatorname{tr}\!\left(\sum_\alpha A_\alpha^\dagger A_\alpha\right)
= \frac{\lambda_{\max}(C)}d.
\end{aligned}
$$

对输出与 $|\Omega_d\rangle\langle\Omega_d|$ 施加二输出测量

$$
\{|\Omega_d\rangle\langle\Omega_d|,
I_{SA}-|\Omega_d\rangle\langle\Omega_d|\},
$$

所得分布的总变差距离为 $1-f_{\mathcal R}$。量子态迹距离不小于此测量距离，而 diamond 距离的优化包含该最大纠缠输入。因此

$$
\frac12\|\mathcal R\circ M_C-\operatorname{id}_S\|_\diamond
\ge1-f_{\mathcal R}
\ge1-\frac{\lambda_{\max}(C)}d.
$$

对 $\mathcal R$ 取下确界得到结论。由于 $C\succeq0$ 且 $\operatorname{tr}C=d$，有 $1\le\lambda_{\max}(C)\le d$，故右端是非负的有限误差下界。证毕。

### 14.3 Fourier 对角相关矩阵的精确可达性

**定理 14.3（对角规范不变性与循环相关矩阵的精确最优恢复）。** 对任意对角酉矩阵 $D_0$，都有

$$
\eta(D_0CD_0^\dagger)=\eta(C).
$$

进一步，设某个对角酉 $D_0$ 使 $C'=D_0CD_0^\dagger$ 在标准离散 Fourier 基下对角。明确地，令

$$
\omega=e^{2\pi i/d},
\qquad
v_k=(\omega^{kx})_{x=0}^{d-1},
\qquad
f_k=\frac{v_k}{\sqrt d},
\qquad 0\le k<d,
$$

并假设 $C'f_k=\lambda_k f_k$。则

$$
\eta(C)=1-\frac{\max_k\lambda_k}d
=1-\frac{\lambda_{\max}(C)}d.
$$

设 $k_*$ 是任意达到最大特征值的指标，定义

$$
Z=\operatorname{diag}(1,\omega,\ldots,\omega^{d-1}),
\qquad
\mathcal R_*
=\operatorname{Ad}_{Z^{-k_*}D_0},
\qquad
\operatorname{Ad}_U(X)=UXU^\dagger.
$$

则 $\mathcal R_*$ 达到上述最小值。最优误差同时由不带参考的输入 $|s_d\rangle=d^{-1/2}\sum_x|x\rangle$ 达到。

上述等式与达到协议以完整相关矩阵经对角规范变换后具有所列 Fourier 特征基为假设；对一般相关矩阵，定理 14.2 只给出恢复误差的下界。

证明。 对角酉的矩阵元计算给出

$$
M_{D_0CD_0^\dagger}
=\operatorname{Ad}_{D_0}\circ M_C.
$$

当 $\mathcal R$ 遍历全部 CPTP 恢复时，$\mathcal R\circ\operatorname{Ad}_{D_0}$ 也遍历全部 CPTP 恢复，因为右侧复合的逆由 $\operatorname{Ad}_{D_0^\dagger}$ 给出。这证明 $\eta$ 的对角规范不变性。

Fourier 向量 $(f_k)_{k=0}^{d-1}$ 正交归一，因此

$$
C'=\sum_{k=0}^{d-1}\frac{\lambda_k}d v_kv_k^\dagger,
\qquad
p_k:=\frac{\lambda_k}d\ge0,
\qquad
\sum_kp_k=1.
$$

逐项使用 $(v_kv_k^\dagger)_{xy}=\omega^{k(x-y)}$，得到

$$
M_{C'}=\sum_{k=0}^{d-1}p_k\operatorname{Ad}_{Z^k}.
$$

故恢复后的通道为

$$
\mathcal R_*\circ M_C
=\sum_{k=0}^{d-1}p_k\operatorname{Ad}_{Z^{k-k_*}},
$$

其中恒等通道的权重为 $p_{k_*}$。任意两个通道的 diamond 距离至多为 $2$，所以三角不等式给出

$$
\frac12\|\mathcal R_*\circ M_C-\operatorname{id}_S\|_\diamond
\le\sum_{k\ne k_*}p_k
=1-p_{k_*}.
$$

另一方面，向量 $(Z^{k-k_*}|s_d\rangle)_k$ 正交归一；对输入 $|s_d\rangle\langle s_d|$，恢复输出是这些正交纯态按 $p_k$ 的混合，目标 $|s_d\rangle\langle s_d|$ 对应指标 $k_*$。二者的迹距离恰为 $1-p_{k_*}$，故上界达到。定理 14.2 排除了任何其他 CPTP 恢复获得更小误差的可能性。证毕。

### 14.4 三标签相位环的精确恢复误差

**命题 14.4（命题 8.9 的三标签记录具有精确恢复误差）。** 按定义 1.1 的低位到高位约定及定理 1.3，系统标签 $0,1,2$ 可分别取两位置 Zeckendorf 合法基底 $|00\rangle,|10\rangle,|01\rangle$。取命题 8.9 的不可访问二能级记录

$$
e_0=|0\rangle,
\qquad
e_1=\frac{|0\rangle+|1\rangle}{\sqrt2},
\qquad
e_2=\frac{|0\rangle+i|1\rangle}{\sqrt2}.
$$

其相关矩阵记作 $C_\circ$，即

$$
C_\circ=
\begin{pmatrix}
1&r&r\\
r&1&(1-i)/2\\
r&(1+i)/2&1
\end{pmatrix},
\qquad r=\frac1{\sqrt2}.
$$

则定义 14.1 的全部写入后 CPTP 恢复的最优误差为

$$
\eta(C_\circ)=\frac{3-\sqrt3}{6},
$$

并由对角酉

$$
D_*=\operatorname{diag}(1,e^{i\pi/12},e^{-i\pi/12})
$$

达到。

证明。 命题 8.9 已经证明上述矩阵正半定、单位对角且秩为二，并计算了对角规范不变的非实循环乘积

$$
(C_\circ)_{01}(C_\circ)_{12}(C_\circ)_{20}
=\frac{1-i}{4}.
$$

令 $a=r e^{-i\pi/12}$，直接相乘得到

$$
C_*:=D_*C_\circ D_*^\dagger
= \begin{pmatrix}
1&a&\bar a\\
\bar a&1&a\\
a&\bar a&1
\end{pmatrix}.
$$

三个有向循环位置 $(0,1),(1,2),(2,0)$ 的相位均为 $-\pi/12$。取定理 14.3 中的 $d=3$ Fourier 基，逐行相乘得

$$
\lambda_k
=1+2r\cos\!\left(\frac{2\pi k}3-\frac\pi{12}\right),
\qquad k=0,1,2.
$$

其精确值依次为

$$
\lambda_0=\frac{3+\sqrt3}{2},
\qquad
\lambda_1=\frac{3-\sqrt3}{2},
\qquad
\lambda_2=0.
$$

最大值在 $k_*=0$ 取得，故定理 14.3 直接给出所述最优值及恢复酉 $D_*$。具体地，令 $Z=\operatorname{diag}(1,e^{2\pi i/3},e^{4\pi i/3})$，有

$$
\operatorname{Ad}_{D_*}\circ M_{C_\circ}
= \frac{3+\sqrt3}{6}\operatorname{id}_S
+
\frac{3-\sqrt3}{6}\operatorname{Ad}_Z.
$$

两个酉分支对均匀叠加输入给出正交输出，这也显示了误差的达到方式。对任意包含 $\operatorname{Ad}_{D_*}$ 且包含于定义 14.1 的恢复类，定理 14.2 的下界与同一达到协议仍给出最优误差 $(3-\sqrt3)/6$。证毕。

### 14.5 相同逐对恢复能力与不同联合最优值

**命题 14.5（逐对模资料不足以确定多标签恢复误差）。** 固定命题 14.4 的 $r=1/\sqrt2$，另取三标签相关矩阵

$$
C_+=(1-r)I_3+r\mathbf1\mathbf1^\dagger,
\qquad
\mathbf1=(1,1,1)^{\mathsf T}.
$$

两个模型 $C_\circ$ 与 $C_+$ 的全部异标签重叠模都等于 $r$。对任意一个标签对单独构成的二标签恢复问题，两个模型的最优误差都为

$$
\eta_{\rm pair}^*=\frac{1-r}{2}=\frac{2-\sqrt2}{4}.
$$

但三标签联合恢复最优值满足

$$
\eta(C_+)=\frac{2(1-r)}3=\frac{2-\sqrt2}{3},
$$

以及严格差异

$$
\eta(C_\circ)-\eta(C_+)
= \frac{2\sqrt2-\sqrt3-1}{6}>0.
$$

因此全部逐对重叠模、乃至每对的精确恢复最优值，都不足以决定整个三标签通道的恢复最优值。

证明。 $C_+$ 的特征值为 $1+2r,1-r,1-r$，均非负，且其对角元为一，因此它是合法的条件记录相关矩阵。两组记录若需使用同一环境空间，可全部置于 $\mathbb C^3$：命题 8.9 的二能级记录作等距嵌入，而 $C_+$ 由其正半定平方根构造三维记录即可。更明确地，取 $V=(C_+^{\mathsf T})^{1/2}$，以 $V$ 的各列作为条件记录，则 $V^\dagger V=C_+^{\mathsf T}$，所以按本章 $C_{xy}=\langle e_y,e_x\rangle$ 的方向得到 $C_+$。该比较不要求两个矩阵具有相同秩。

对每个标签对，相关矩阵都具有形式

$$
C_{xy}^{(2)}=
\begin{pmatrix}
1&r e^{i\phi_{xy}}\\
r e^{-i\phi_{xy}}&1
\end{pmatrix}.
$$

该二阶矩阵经对角酉规范变换可使非对角元变为正实数 $r$，特征值为 $1+r$ 和 $1-r$。使用定理 14.3 的 $d=2$ 情形，任意写入后 CPTP 恢复的最优误差为 $(1-r)/2$。这里允许每个二标签问题分别选择自己的恢复；没有假设这些选择能同时组成一个三标签协议。

矩阵 $C_+$ 已在三维 Fourier 基下对角，其最大特征值是 $1+2r$。定理 14.3 给出

$$
\eta(C_+)=1-\frac{1+2r}{3}=\frac{2(1-r)}3,
$$

由恒等恢复达到。它的通道分解为

$$
M_{C_+}
=\frac{1+2r}{3}\operatorname{id}_S
+\frac{1-r}{3}\operatorname{Ad}_Z
+\frac{1-r}{3}\operatorname{Ad}_{Z^2}.
$$

结合命题 14.4，相减得到所述精确差。由于 $2\sqrt2>1+\sqrt3$，该差严格为正；此不等式可由两边为正并比较平方 $8>4+2\sqrt3$ 得到。两个三标签最优误差的十进制展开依次为 $0.2113248654\ldots$ 与 $0.1952621459\ldots$，每对的最优误差为 $0.1464466094\ldots$。证毕。

### 14.6 固定逐对模的全部三标签相位范围

**命题 14.6（固定重叠模下的相位分类与完整恢复误差范围）。** 令 $A$ 为三阶 Hermitian 矩阵，满足 $A_{xx}=1$，以及 $|A_{xy}|=r=1/\sqrt2$ 对所有 $x\ne y$ 成立。取有向循环乘积的主辐角

$$
\phi=\operatorname{Arg}(A_{01}A_{12}A_{20})\in(-\pi,\pi].
$$

则 $A$ 是合法相关矩阵当且仅当

$$
|\phi|\le\frac\pi4.
$$

循环相位 $\phi$ 完全分类这一固定模矩阵族的对角酉规范轨道。对每个合法 $A$，定义 14.1 中全部写入后 CPTP 恢复的最优误差为

$$
\eta(A)=\frac{2-\sqrt2\cos(\phi/3)}3.
$$

该误差在 $|\phi|\in[0,\pi/4]$ 上严格递增，其全部可达值恰为

$$
\left[\frac{2-\sqrt2}{3},\frac{3-\sqrt3}{6}\right].
$$

命题 14.5 的正实矩阵 $C_+$ 达到最小值，命题 14.4 的 $C_\circ$ 达到最大值。合法矩阵在 $|\phi|<\pi/4$ 时秩为三，在 $|\phi|=\pi/4$ 时秩为二。

证明。 对角酉规范变换使每个有向边 $A_{xy}$ 乘以一个顶点相位差，故循环乘积中的这些相位相消；这正是命题 8.9 已使用的不变量。为证明它在本矩阵族中也足以确定规范轨道，选择实数 $\alpha_{01},\alpha_{12},\alpha_{20}$，使

$$
A_{01}=r e^{i\alpha_{01}},
\qquad A_{12}=r e^{i\alpha_{12}},
\qquad A_{20}=r e^{i\alpha_{20}}.
$$

它们满足 $\alpha_{01}+\alpha_{12}+\alpha_{20}=\phi$ 模 $2\pi$。定义

$$
D_\phi
=\operatorname{diag}\!\left(
1,
e^{i(\alpha_{01}-\phi/3)},
e^{i(\phi/3-\alpha_{20})}
\right),
\qquad
a_\phi=r e^{i\phi/3}.
$$

逐个有向边相乘给出

$$
A_\phi:=D_\phi A D_\phi^\dagger
=\begin{pmatrix}
1&a_\phi&\overline{a_\phi}\\
\overline{a_\phi}&1&a_\phi\\
a_\phi&\overline{a_\phi}&1
\end{pmatrix}.
$$

因此相同循环相位的两个矩阵都能规范到同一个 $A_\phi$；不同循环相位则由不变性排除规范等价。这证明分类陈述。

行列式展开给出

$$
\det A
=1-3r^2+2r^3\cos\phi
=-\frac12+\frac{\cos\phi}{\sqrt2}.
$$

任意二阶主子块的特征值都是 $1+r$ 和 $1-r$，均严格为正。固定一个这样的主子块，用其 Schur 补将 $A$ 作可逆合同变换，得到该正定二阶块与一个实标量的直和；标量等于 $\det A/(1-r^2)$。所以 $A\succeq0$ 当且仅当 $\det A\ge0$，等价于 $\cos\phi\ge1/\sqrt2$。结合主辐角范围，这恰好给出 $|\phi|\le\pi/4$。同一 Schur 补还表明：严格不等号对应秩三，端点对应秩二。

在定理 14.3 的 Fourier 方向约定下，$A_\phi$ 的三个特征值为

$$
\lambda_k(\phi)
=1+\sqrt2\cos\!\left(\frac\phi3+\frac{2\pi k}3\right),
\qquad k=0,1,2.
$$

对合法相位，$\phi/3\in[-\pi/12,\pi/12]$。此时 $\cos(\phi/3)>0$，而另外两项的余弦都为负：$k=1$ 的角落在 $[7\pi/12,3\pi/4]$，$k=2$ 的角落在 $[5\pi/4,17\pi/12]$。因此 $\lambda_0(\phi)$ 始终是最大特征值。定理 14.3 适用，得到

$$
\eta(A)
=1-\frac{\lambda_0(\phi)}3
=\frac{2-\sqrt2\cos(\phi/3)}3,
$$

并由恢复 $\operatorname{Ad}_{D_\phi}$ 达到。这一等式使用定理 14.2 对全部 CPTP 恢复的下界，而非仅在对角反馈中求最优。

误差只依赖 $t=|\phi|$。函数 $\cos(t/3)$ 在 $t\in[0,\pi/4]$ 上连续且严格递减，所以 $\eta$ 连续且严格递增。端点分别为

$$
\eta(0)=\frac{2-\sqrt2}{3},
\qquad
\eta(\pi/4)
=\frac{2-\sqrt2\cos(\pi/12)}3
=\frac{3-\sqrt3}{6}.
$$

每个 $\phi\in[-\pi/4,\pi/4]$ 都由已证明正半定、单位对角的 $A_\phi$ 实现，它可按命题 14.5 的平方根方法构造有限维条件记录。因此误差取遍所列闭区间。$C_+$ 的循环相位为零，$C_\circ$ 的循环相位为 $-\pi/4$，故二者达到两端。证毕。

## 追加锚（新终端）

## 15. 可访问旧记录、完整扰动与控制范围

沿用第8、9章的有限新鲜记录假设。除第15.5节另行允许控制外，系统始终在同一指针基上受控写入，旧记录不再参与相互作用。所有Hilbert空间、测量结果集和时间窗口均有限；比较的是分别选定的记录前缀节点上的无条件态。令标签集为 $\mathsf X$、$d=|\mathsf X|\ge2$，$J$ 为全一矩阵。第 $t$ 步的单位对角相关矩阵 $C_t=(c_{xy}^{t})$ 与累计系统相位为
$$
c_{xy}^{t}
=e^{i(\theta_{x,t}-\theta_{y,t})}\langle e_y^{(t)},e_x^{(t)}\rangle,
\qquad
\Theta_x(m)=\sum_{t=1}^{m}\theta_{x,t}.
$$
记
$$
A_N=C_1\odot\cdots\odot C_N,\qquad A_0=J,
\qquad F_{m,n}=C_{m+1}\odot\cdots\odot C_n,\qquad F_{m,m}=J.
$$
系统边缘仍为 $\sigma_N(\rho)=M_{A_N}(\rho)$。算子范数记为 $\|\cdot\|_\infty$，迹范数记为 $\|\cdot\|_1$，迹距离为 $\mathsf d(\rho,\sigma)=\|\rho-\sigma\|_1/2$。

### 15.1 读数自身的剩余非对角量

固定第12章的投影测量 $Q=(Q_b)_{b\in\mathcal B}$，并令 $Q_B=\sum_{b\in B}Q_b$。对任意算符 $X$，$\operatorname{diag}(X)$ 表示其指针基对角部分。定义
$$
r_N(Q)=\max_{B\subseteq\mathcal B}
\left\|\overline{A_N}\odot\bigl(Q_B-\operatorname{diag}(Q_B)\bigr)\right\|_\infty.
$$

**推论 15.1（依赖读数的尖锐尾窗界）。** $r_N(Q)$ 随 $N$ 不增。对每个有限窗口 $m\le u\le v\le n$，有
$$
\alpha_Q(u,v)\le\min\{1,r_u(Q)+r_v(Q)\}
\le\min\{1,2r_m(Q)\},
$$
其中 $\alpha_Q$ 沿用第12.4节，且 $\alpha_Q(u,u)=0$。若 $q_m=\max_{x\ne y}|A_m(x,y)|$，则
$$
r_m(Q)\le\frac{d-1}{2}q_m.
$$
在前缀 $m$ 之后，无论再施加哪一个新鲜Schur记录通道，$Q$ 的分布都对所有初态保持不变，当且仅当 $r_m(Q)=0$。统一尾窗界中的系数 $2$ 不能减小。

证明。令 $X_{N,B}=\overline{A_N}\odot(Q_B-\operatorname{diag}(Q_B))$。有 $X_{N+1,B}=M_{C_{N+1}}^*(X_{N,B})$，而单位保持正映射收缩Hermitian算子的算子范数，故 $r_{N+1}\le r_N$。第12.4节的对偶公式中对角部分相消，给出 $\alpha_Q(u,v)=\max_B\|X_{v,B}-X_{u,B}\|_\infty$；三角不等式及总变差至多为 $1$ 得到尾窗界。另一方面，按定理10.1的事件与谱范数计算，$r_m(Q)$ 恰为对所有初态取最坏值的
$$
\operatorname{TV}\bigl(C_Q(M_{A_m}(\rho)),C_Q(\Delta(\rho))\bigr).
$$
定理9.4的迹距离上界与测量收缩给出所列 $q_m$ 界。

若 $r_m=0$，每个 $X_{m,B}$ 都为零，任意继续记录也保持其为零，故以后读数不变。反之，取下一步为完全退相干通道 $M_{I_d}=\Delta$，定理12.1的精确缺陷即为 $r_m$。最后取二标签、$A_m(0,1)=a\in(0,1]$、$Q_+=|+\rangle\langle+|$ 与 $Q_-=I-Q_+$，则 $r_m=a/2$。下一步取 $c_{01}=-1$ 的相位翻转，得到 $\alpha_Q(m,m+1)=a=2r_m$。所需两种矩阵均为合法相关矩阵。证毕。

### 15.2 任意旧记录子集的压缩读数

固定 $0\le m\le n$，并指定可访问的旧记录子集 $R\subseteq\{1,\ldots,m\}$；系统本身也可访问。以时间升序排列记录张量因子，令
$$
G^{m,R}_{xy}
=\prod_{t\in\{1,\ldots,m\}\setminus R}
\langle e_y^{(t)},e_x^{(t)}\rangle,
$$
$$
W_{m,R}|x\rangle
=e^{i\Theta_x(m)}|x\rangle\otimes
\bigotimes_{t\in R}|e_x^{(t)}\rangle.
$$
空张量积为一维空间中的单位向量。$G^{m,R}$ 是单位对角相关矩阵；由于系统标签正交，$W_{m,R}$ 为等距映射，无需记录向量线性无关。在这一固定窗口中简称它们为 $G,W$。令 $\tau_t^R(\rho)$ 为第 $t\ge m$ 个前缀在同一子系统 $S+E_R$ 上的态，即忽略全部不可访问旧记录以及全部 $m$ 之后的新记录。

**命题 15.2（部分旧记录可访问时的精确压缩）。** 对 $m\le t\le n$，有
$$
\tau_t^R(\rho)=W\bigl((G\odot F_{m,t})\odot\rho\bigr)W^\dagger.
$$
给定可访问空间上的有限POVM $P=(P_b)_{b\in\mathcal B}$，记 $C_P(\tau)_b=\operatorname{tr}(P_b\tau)$。其压缩效应
$$
\widetilde P_b=W^\dagger P_bW,\qquad
\widetilde P_B=\sum_{b\in B}\widetilde P_b=W^\dagger P_BW
$$
构成系统空间上的POVM，且
$$
\sup_\rho\operatorname{TV}
\bigl(C_P(\tau_n^R(\rho)),C_P(\tau_m^R(\rho))\bigr)
=\max_{B\subseteq\mathcal B}
\left\|\overline G\odot(\overline{F_{m,n}}-J)\odot\widetilde P_B\right\|_\infty.
$$
即使 $P$ 是投影测量，$\widetilde P$ 也只保证为POVM；此公式不把未经压缩的 $P_B$ 当作系统矩阵。

证明。直接在定理8.2的部分迹公式中保留集合 $R$。不可访问的旧记录贡献 $G_{xy}$，后续步骤的相位与被忽略新记录合计贡献 $(F_{m,t})_{xy}$，旧相位和保留向量均包含于 $W$，得到第一式。由 $W^\dagger W=I$ 可知 $\widetilde P_b\ge0$ 且 $\sum_b\widetilde P_b=I$。把概率差拉回系统，再应用定理10.1所用的有限事件最大值与Hermitian范数论证，得到第二式。该论证只需效应非负且和为恒等，因而适用于POVM。证毕。

### 15.3 完整访问扰动的精确有限优化

定义
$$
H_R(m,n)=G^{m,R}\odot(F_{m,n}-J),
\qquad
\Delta_R(m,n)=\sup_\rho
\mathsf d\bigl(\tau_n^R(\rho),\tau_m^R(\rho)\bigr).
$$
$H_R(m,n)$ 为Hermitian矩阵且对角元为零。对概率单纯形中的 $p=(p_x)_{x\in\mathsf X}$，记 $D_p=\operatorname{diag}(\sqrt{p_x})$。

**定理 15.3（Schur差值的精确扰动与参考系统无增益）。** 有
$$
\boxed{
\Delta_R(m,n)=\frac12\max_{p_x\ge0,\ \sum_xp_x=1}
\left\|D_pH_R(m,n)D_p\right\|_1.
}
$$
这也等于同时优化初态及可访问空间上全部有限POVM所得的总变差变化。若允许任意有限旁参考 $K$ 在最初与系统纠缠，随后保持不动且可被联合测量，同一最坏值仍为 $\Delta_R(m,n)$。此外，
$$
\Delta_R(m,n)=0
\quad\Longleftrightarrow\quad
G^{m,R}_{xy}\bigl((F_{m,n})_{xy}-1\bigr)=0
\quad\text{对所有 }x,y,
$$
且访问范围满足
$$
R\subseteq R'\subseteq\{1,\ldots,m\}
\quad\Longrightarrow\quad
\Delta_R(m,n)\le\Delta_{R'}(m,n).
$$
当全部旧记录可访问时 $G^{m,R}=J$，旧记录的重叠不再出现在该完整扰动公式中。

证明。等距嵌入保持迹范数，故命题15.2将两态之差的范数化为 $\|H_R\odot\rho\|_1$。对纯态 $\psi_x=\sqrt{p_x}e^{i\phi_x}$，该矩阵与 $D_pH_RD_p$ 由对角酉共轭联系。对混态取任意纯态凸分解，迹范数凸性说明其值不超过纯态上的最大值。概率单纯形紧且目标连续，故最大值达到，得到第一式。

再取系统与有限参考的纯态，并写为
$$
|\Psi\rangle=\sum_x\sqrt{p_x}|x\rangle|r_x\rangle,
\qquad \|r_x\|=1\ \text{当 }p_x>0.
$$
零概率标签对应的 $r_x$ 任取单位向量。向量 $|x\rangle|r_x\rangle$ 两两正交；因此 $V|x\rangle=|x\rangle|r_x\rangle$ 是等距映射，且
$$
(M_{H_R}\otimes\operatorname{id}_K)(|\Psi\rangle\langle\Psi|)
=V(D_pH_RD_p)V^\dagger.
$$
再沿 $W\otimes I_K$ 嵌入也不改变范数，故有限参考不能提高第一式。混态仍由凸性处理；取一维参考即可达到原值。这里的无增益只针对所列Schur差值，不外推为一般通道判别结论。

对任意迹为零的Hermitian差值 $T$，其正谱投影与补投影构成的二输出PVM达到总变差 $\|T\|_1/2$，而所有POVM都受迹距离收缩约束，证明测量优化的等价性。若 $H_{R,xy}\ne0$，取在 $x,y$ 上各占 $1/2$ 的 $p$，则得到扰动 $|H_{R,xy}|/2>0$；反向由零矩阵立即成立。最后，对同一输入态，访问集合 $R$ 的两个边缘都由对应 $R'$ 边缘迹掉 $E_{R'\setminus R}$ 得到。部分迹收缩迹距离，随后取初态上确界，得到访问单调性。证毕。

保 Hermitian 映射的 diamond 范数优化与同维有限参考约定见 John Watrous，[《The Theory of Quantum Information》](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)，定理 3.51、式 (3.291)。本定理中参考系统无增益的结论由上述 Schur 差值的等距表示给出。

### 15.4 固定访问范围的有限窗口预算

在窗口起点 $m$ 固定 $R$，并在之后始终使用同一可访问空间 $S+E_R$。对 $m\le t<n$，定义
$$
\xi_t^{m,R}
=\frac12\max_p
\left\|D_p\bigl[G^{m,R}\odot F_{m,t}\odot(C_{t+1}-J)\bigr]D_p\right\|_1,
$$
以及单步完整扰动
$$
\kappa(C)=\frac12\max_p\left\|D_p(C-J)D_p\right\|_1.
$$

**推论 15.4（固定访问窗口的累积预算）。** $\xi_t^{m,R}$ 恰为 $\tau_{t+1}^R$ 与 $\tau_t^R$ 的最坏迹距离，并且
$$
\max_{m\le u\le v\le n}\sup_\rho
\mathsf d\bigl(\tau_v^R(\rho),\tau_u^R(\rho)\bigr)
\le\min\left\{1,\sum_{t=m}^{n-1}\xi_t^{m,R}\right\},
\qquad
\xi_t^{m,R}\le\kappa(C_{t+1}).
$$
同一结论适用于最初与系统纠缠、随后保持不动的任意有限可访问参考系统。

证明。相邻时刻的差值仍为定理15.3所处理的Hermitian Schur差值，其乘子即定义 $\xi_t^{m,R}$ 的方括号。该定理的证明给出精确值及参考系统无增益。固定同一初态后沿窗口作迹距离的三角不等式，再取上确界，得到累积界。矩阵 $G^{m,R}\odot F_{m,t}$ 是相关矩阵；对应通道将 $(M_{C_{t+1}}-\operatorname{id})(\rho)$ 映为这里的差值。CPTP映射对Hermitian算子的迹范数收缩，故 $\xi_t^{m,R}\le\kappa(C_{t+1})$。证毕。

### 15.5 共同处理、交错控制与普遍不扰动

先保留第15.2节无交错控制的两个端点。对两端施加同一个CPTP映射，可以联合处理系统、可访问旧记录与最初携带的有限参考；其后任何测量的总变差变化均不超过 $\Delta_R(m,n)$。这由定理15.3及迹距离收缩直接得到，也包括保留全部经典结果寄存器的无条件处理。

下面另行允许交错控制：比较两个从同一任意态 $\omega_{S\mathcal M}$ 出发的有限协议，其中 $\mathcal M$ 是可访问有限记忆。两协议在各记录步骤之前、之间和之后施加完全相同的CPTP控制；实际协议在步骤 $t=m+1,\ldots,n$ 施加 $M_{C_t}\otimes\operatorname{id}_{\mathcal M}$，比较协议把这些记录通道全部替换为恒等通道。每个新记录均在该步作用后被忽略，此后不再参与控制；控制只访问系统与记忆。存储经典结果并按其反馈可作为共同CPTP控制的一部分，但不对选定结果作后选择。

**定理 15.5（任意共同控制下的混合协议界）。** 两协议的末态满足
$$
\mathsf d(\omega_{\rm actual},\omega_{\rm identity})
\le\min\left\{1,\sum_{t=m+1}^{n}\kappa(C_t)\right\}.
$$
对全部共同初态、全部上述共同控制序列和全部最终POVM，两协议的末端统计完全相同，当且仅当
$$
C_t=J\qquad(m<t\le n).
$$

证明。由定理15.3取 $G=J$，$\kappa(C_t)$ 是 $M_{C_t}$ 与恒等通道在任意有限记忆参与下的精确最大单步迹距离。构造有限条中间协议，逐个把实际记录替换为恒等通道。每对相邻中间协议在唯一不同步骤之前具有同一输入，该步骤后的差距至多为 $\kappa(C_t)$；后续共同通道收缩该差距。对这些末态使用三角不等式，再结合迹距离至多为 $1$，得到第一式。

若全部 $C_t=J$，两协议逐步相同。反之，选一步 $t$ 及一对标签 $x\ne y$，使 $c_{xy}^{t}\ne1$。无需额外记忆：先将系统保持在 $|x\rangle$，使此前所有记录均不改变系统态；在所选步骤之前，用共同酉控制制备 $(|x\rangle+|y\rangle)/\sqrt2$。两协议在该步骤之后的态差在此二维空间中为
$$
T=\frac12\begin{pmatrix}
0&c_{xy}^{t}-1\\
\overline{c_{xy}^{t}}-1&0
\end{pmatrix},
\qquad
\operatorname{spec}(T)=\left\{\frac{|c_{xy}^{t}-1|}{2},-\frac{|c_{xy}^{t}-1|}{2}\right\}.
$$
紧接着选取同一个酉控制，将 $T$ 的正交特征基送到指针基。两协议于是具有非零指针布居差。令以后控制均为恒等；后续每个Schur记录都保持这些布居，而比较协议也保持它们。最后一次指针测量仍得到总变差 $|c_{xy}^{t}-1|/2>0$，反驳普遍相同。证毕。

## 追加锚（新终端）

## 16. 有限经典历史的全输出误差与记录预算

### 16.1 实际记录仪器与理想历史

**定义 16.1（新鲜记录、存储结果与共同控制）。** 固定有限标签集 $\mathsf X=\{0,\ldots,d-1\}$，其中 $d\ge2$，系统 $S=\mathbb C^d$ 的指针投影为 $P_x=|x\rangle\langle x|$。给定有限阶段数 $N\ge1$ 和一个非零有限维可访问记忆空间 $M$；无量子记忆的情形取 $M=\mathbb C$。第 $t$ 步之前的已存储历史为 $h=(z_1,\ldots,z_{t-1})\in\mathsf X^{t-1}$，空历史用于第一步。

每一步先按同一既定策略，对 $S\otimes M$ 施加 CPTP 控制 $\mathcal V_{t,h}$。实际过程与理想过程使用相同的函数 $h\mapsto\mathcal V_{t,h}$；它们各自按自身已经存储的结果选择该函数的相应分支。共同控制不改写已有历史寄存器。所有控制均有有限维实现；控制实现中被丢弃的辅助环境，以及此前记录的被丢弃部分，随后都不再被访问或重新耦合。所需的可访问辅助自由度包含在 $M$ 内。

控制之后，第 $t$ 步使用一个新鲜有限维记录空间 $E_{t,h}$；给定已存历史 $h$ 后，其初始准备与系统、记忆、参考及过去环境处于乘积态。给定单位条件记录 $(e_{t,h,x})_{x\in\mathsf X}$，写入映射为

$$
W_{t,h}|x\rangle=|x\rangle|e_{t,h,x}\rangle.
$$

对该记录施加一个具有标签结果的有限 POVM $(M_{t,h,z})_{z\in\mathsf X}$，把结果 $z$ 永久保存在经典寄存器 $Z_t$，丢弃记录的其余输出。令

$$
q_{t,h,x}
=\langle e_{t,h,x},M_{t,h,x}e_{t,h,x}\rangle.
$$

假设存在 $\beta_t\in[0,1]$，使全部标签和每个允许的历史分支都满足

$$
q_{t,h,x}\ge1-\beta_t.
$$

这个条件逐标签成立，不用某个先验平均正确率替代；策略和误差条件也在概率为零的历史分支上预先定义。

**定义 16.2（实际与理想全历史通道）。** 对 $S\otimes M$ 上的算符 $\rho$，定义实际结果仪器

$$
\mathcal I_{t,h,z}(\rho)
=\sum_{x,y\in\mathsf X}
\langle e_{t,h,y},M_{t,h,z}e_{t,h,x}\rangle
(P_x\otimes I_M)\rho(P_y\otimes I_M),
$$

以及理想 Lüders 仪器

$$
\mathcal J_z(\rho)
=(P_z\otimes I_M)\rho(P_z\otimes I_M).
$$

对应的带经典结果通道为

$$
\mathcal I_{t,h}(\rho)
=\sum_z|z\rangle\langle z|_{Z_t}\otimes\mathcal I_{t,h,z}(\rho),
\qquad
\mathcal J(\rho)
=\sum_z|z\rangle\langle z|_{Z_t}\otimes\mathcal J_z(\rho).
$$

在定义 16.1 的同一共同控制策略下，逐步使用实际仪器或理想仪器，得到从 $S\otimes M$ 到全部历史 $H_N=Z_1\cdots Z_N$、最终系统 $S$ 及可访问记忆 $M$ 的通道

$$
\mathcal H_{\rm actual},\qquad\mathcal H_{\rm ideal}.
$$

全部历史寄存器保持为经典；不按某些历史筛选运行，也不在后续步骤相干重合并已经写出的结果。本章比较这两个无条件全输出通道的半 diamond 距离，允许输入与任意有限维参考系统 $R$ 纠缠。参考系统不参与控制。通道模型、部分迹及结果仪器的矩阵元方向沿用假设 1.2、定理 8.3 与命题 8.8。有限测量仪器、Stinespring 扩张及通道距离的参考系统表述采用 John Watrous，*The Theory of Quantum Information*（2018），[第 2–3 章](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)的标准框架，其中 §2.3.2、式 (2.262) 给出带经典结果寄存器的仪器表示。

### 16.2 共同控制下的乘积界及其达到

**定理 16.3（全存储历史的有限乘积误差界）。** 在定义 16.1–16.2 下，记

$$
\delta_N
=\sqrt{1-\prod_{t=1}^N(1-\beta_t)}.
$$

则

$$
\frac12\|\mathcal H_{\rm actual}-\mathcal H_{\rm ideal}\|_\diamond
\le\delta_N
\le\min\left\{1,\sqrt{\sum_{t=1}^N\beta_t}\right\}.
$$

因此对任意初态及有限参考，整个已存储历史、最终系统、可访问记忆与参考的联合输出迹距离均不超过 $\delta_N$。该结论允许非交换的阶段间控制、按历史反馈及有限量子记忆；不以理想标签过程满足单标签 Markov 性为前提。

证明。 先固定一步和一个历史，省略 $t,h$，令

$$
a=\sqrt{1-\beta},
\qquad
v_x=\sqrt{M_x}e_x,
\qquad
q_x=\|v_x\|^2\ge a^2.
$$

在被丢弃的记录空间中加入一个与实际记录空间正交的单位方向 $\bot$。若 $a>0$，则所有 $q_x>0$，可以定义

$$
b_x=\frac{a}{q_x}v_x+
\sqrt{1-\frac{a^2}{q_x}}\,\bot.
$$

若 $a=0$，对所有 $x$ 定义 $b_x=\bot$，包括 $q_x=0$ 的情形。两种情形都满足

$$
\|b_x\|=1,
\qquad
\langle b_x,v_x\rangle=a.
$$

令 $Z$ 为保留的结果寄存器，$C$ 为不可访问的结果副本，定义两个等距映射

$$
A|x\rangle
=|x\rangle_S\sum_z|z\rangle_Z|z\rangle_C\sqrt{M_z}e_x,
\qquad
B|x\rangle
=|x\rangle_S|x\rangle_Z|x\rangle_C b_x.
$$

它们在记忆及其他旁系统上作用为恒等。$A$ 的等距性由系统基正交和 $\sum_zM_z=I$ 给出；$B$ 的等距性由 $\|b_x\|=1$ 给出。对 $C$ 及记录余系统取部分迹，$A$ 恰好产生实际仪器 $\mathcal I$；$B$ 中的结果副本使异标签交叉项消失，恰好产生理想仪器 $\mathcal J$。

系统基还使 $B^\dagger A$ 的异标签矩阵元为零，而第 $x$ 个对角元为 $\langle b_x,\sqrt{M_x}e_x\rangle=a$。故有精确的标量恒等式

$$
B^\dagger A=aI_S.
$$

按每个历史分支分别实施上述构造，并为不同分支选取一个共同的有限维扩张空间。在第 $t$ 步中，所有分支使用相同的 $a_t=\sqrt{1-\beta_t}$，历史寄存器作为保持不变的控制，因此得到

$$
B_t^\dagger A_t=a_t I_{H_{t-1}SM}.
$$

每个共同 CPTP 控制可选取一个有限 Stinespring 等距实现 $V_t$，由历史控制而不改写历史。记其新引入的不可访问环境为 $D_t$，在数学纯化中保留该环境，并使记录步骤及所有后续操作在它上面作用为恒等。复合等距映射满足

$$
\bigl[(B_t\otimes I_{D_t})V_t\bigr]^\dagger
\bigl[(A_t\otimes I_{D_t})V_t\bigr]
=V_t^\dagger(a_tI_{H_{t-1}SM}\otimes I_{D_t})V_t
=a_tI_{H_{t-1}SM}.
$$

所有此前不可访问环境也同样保留在纯化中并不再作用。若 $A^{(t)},B^{(t)}$ 表示到第 $t$ 步为止的完整等距映射，逐步从末步消去上式得到

$$
(B^{(N)})^\dagger A^{(N)}
=\left(\prod_{t=1}^N a_t\right)I_{SM}.
$$

对任意纯输入及其有限参考，两种完整纯化输出的内积恰为 $\prod_ta_t$，所以它们的迹距离为

$$
\sqrt{1-\left|\prod_ta_t\right|^2}
=\sqrt{1-\prod_t(1-\beta_t)}.
$$

丢弃不可访问环境收缩迹距离，保留全部 $H_N,S,M,R$ 便得到所需输出界。混态输入再加一个有限纯化参考即可。对通道之差，diamond 范数可在带有限参考的密度矩阵输入上取最大值，因而该输出界给出所列半 diamond 界。最后，由 $\prod_t(1-\beta_t)\ge1-\sum_t\beta_t$ 及距离至多为一，得到根号内求和的上界。证毕。

本证明的乘法来自补入正交方向后得到的精确标量关系 $B_t^\dagger A_t=a_tI$；它没有将若干依赖输入的单步重叠下界直接相乘。补入方向只选择理想通道的一个数学扩张，不向可访问系统提供额外记录。

**命题 16.4（保留历次量子输出时乘积界的尖锐性）。** 对任意有限 $N\ge1$ 和任意 $(\beta_t)_{t=1}^N\subseteq[0,1]$，存在一个满足定义 16.1 的二标签协议，使

$$
\frac12\|\mathcal H_{\rm actual}-\mathcal H_{\rm ideal}\|_\diamond
=\delta_N.
$$

该构造将前 $N-1$ 次系统输出保存在可访问量子记忆中，因此达到结论限定于定理 16.3 允许的记忆类。

证明。 每一步取二能级记录和计算基读取，条件记录为

$$
e_{t,0}=\sqrt{1-\beta_t}|0\rangle+\sqrt{\beta_t}|1\rangle,
\qquad
e_{t,1}=\sqrt{\beta_t}|0\rangle+\sqrt{1-\beta_t}|1\rangle.
$$

正确读取概率对两个标签都为 $1-\beta_t$。在系统输入 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 上，实际和理想仪器的结果 $z$ 概率都为 $1/2$。给定结果 $z$，实际系统输出为

$$
|\psi_{t,z}\rangle
=\sqrt{1-\beta_t}|z\rangle+\sqrt{\beta_t}|1-z\rangle,
$$

而理想输出为 $|z\rangle$。

取 $N-1$ 个记忆量子比特，初始均为 $|+\rangle$，系统初始为指针态 $|0\rangle$。第一步共同控制施加 Hadamard，使系统变为 $|+\rangle$；对第 $t\ge2$ 步，共同控制将活动系统与尚未使用的第 $t-1$ 个记忆比特 SWAP。它把前一步的系统输出留在记忆中，并使活动系统重新成为 $|+\rangle$。整个策略不依赖测量结果。

所以全部 $2^N$ 条历史 $z=(z_1,\ldots,z_N)$ 在两个模型中都有概率 $2^{-N}$。按前 $N-1$ 个记忆比特、最后系统的顺序，实际条件输出与理想条件输出分别为

$$
|\Psi_z\rangle=\bigotimes_{t=1}^N|\psi_{t,z_t}\rangle,
\qquad
|z_1,\ldots,z_N\rangle.
$$

两者内积为 $\prod_t\sqrt{1-\beta_t}$。不同历史位于正交经典块，因此全输出迹距离为

$$
\sum_{z\in\{0,1\}^N}2^{-N}
\sqrt{1-\prod_t(1-\beta_t)}
=\delta_N.
$$

这给出通道距离的下界，定理 16.3 给出相同上界。构造包含 $\beta_t=0$ 或 $1$：相应重叠分别为一或零，无需除以零概率。证毕。

若把记忆中的历次系统输出也丢弃，上述达到证明便不再适用；它不宣称只保留最终系统及经典历史的无量子记忆子类也达到同一最坏常数。

### 16.3 无量子记忆的经典路径律与测量边缘化

**定理 16.5（系统酉控制下的理想经典路径与实际全历史近似）。** 在定义 16.1 中取 $M=\mathbb C$，共同控制为系统酉 $U_{t,h}$。给定初始经典标签寄存器 $X_0$ 和有限参考 $R$，初态为

$$
\omega_{X_0SR}
=\sum_{x_0\in\mathsf X}p_0(x_0)
|x_0\rangle\langle x_0|_{X_0}\otimes P_{x_0}\otimes\tau_R^{x_0},
$$

其中 $p_0$ 是概率分布，各 $\tau_R^{x_0}$ 是密度矩阵。$X_0,R$ 保持不变，不参与控制。对历史 $h=z_{<t}$ 定义

$$
K_{t,h}(y\mid x)=|\langle y|U_{t,h}|x\rangle|^2,
\qquad z_0=x_0.
$$

理想全历史及末端系统、参考的联合输出为

$$
\begin{aligned}
\sigma_{X_0H_NSR}
=\sum_{x_0,z_1,\ldots,z_N}
&p_0(x_0)\prod_{t=1}^N K_{t,z_{<t}}(z_t\mid z_{t-1})\\
&\cdot|x_0,z_1,\ldots,z_N\rangle\langle x_0,z_1,\ldots,z_N|_{X_0H_N}
\otimes P_{z_N}\otimes\tau_R^{x_0}.
\end{aligned}
$$

若 $U_{t,h}=U_t$ 不依赖历史，则 $X_0,Z_1,\ldots,Z_N$ 的理想路径分布为转移核 $K_t(y\mid x)=|\langle y|U_t|x\rangle|^2$ 的有限非齐次 Markov 链。一般历史反馈给出所列受历史控制的经典路径律，不自动退化为只依赖当前标签的 Markov 链。

实际全输出 $\rho_{X_0H_NSR}$ 满足

$$
\frac12\|\rho_{X_0H_NSR}-\sigma_{X_0H_NSR}\|_1\le\delta_N.
$$

特别地，实际与理想的整个存储路径分布的总变差距离不超过 $\delta_N$，每个历史事件的概率误差也不超过 $\delta_N$。

若还给定 $\kappa_t\in[0,1]$，使每个 $t,h,x$ 都满足

$$
K_{t,h}(x\mid x)\ge1-\kappa_t,
$$

则同时检验全部存储标签与末端指针读数都等于初始标签的效应

$$
E_{\rm stay}
=\sum_x|x,x,\ldots,x\rangle\langle x,x,\ldots,x|_{X_0H_N}
\otimes P_x\otimes I_R
$$

满足

$$
\operatorname{tr}(E_{\rm stay}\sigma)
\ge\prod_{t=1}^N(1-\kappa_t),
\qquad
\operatorname{tr}(E_{\rm stay}\rho)
\ge\max\left\{0,\prod_{t=1}^N(1-\kappa_t)-\delta_N\right\}.
$$

这里 $\beta_t$ 控制记录历史对指定经典过程的逼近，$\kappa_t$ 另行控制该过程保持同一标签的概率。

证明。 对任意指针输入 $P_x$，先施加 $U_{t,h}$ 再取理想结果 $y$，未归一化系统输出为

$$
P_yU_{t,h}P_xU_{t,h}^\dagger P_y
=K_{t,h}(y\mid x)P_y.
$$

该操作在 $R$ 上为恒等。按初始标签和随后结果归纳，逐步乘入相应 $K_{t,h}$，就得到所列联合态。每个核非负且对 $y$ 求和为一，因为 $U_{t,h}$ 为酉；故路径权重是归一化的有限经典概率律。无历史依赖时，条件转移只取决于上一步标签，给出 Markov 陈述。

将 $X_0R$ 一同作为定理 16.3 的旁参考，得到联合迹距离界。再对系统及参考取部分迹，或读取任意经典历史事件，使用迹距离收缩性即得路径总变差和事件误差界。

对理想态，$E_{\rm stay}$ 选中每个初始标签 $x_0=x$ 对应的常值路径 $z_1=\cdots=z_N=x$；其每个转移因子至少为 $1-\kappa_t$。对 $x$ 按 $p_0(x)$ 求和便得到乘积下界。实际与理想对同一效应的概率差至多为 $\delta_N$，再使用概率非负，得到实际下界。证毕。

上述路径乘积只在本定理的无量子记忆、系统酉控制条件下使用。定理 16.3 的一般量子记忆仍可保留影响未来的自由度，不提供同一个单标签转移核公式。

**命题 16.6（全历史比较的三个有限边界反例）。** 下列三个有限模型分别给出全历史误差的积累、存储结果边缘化与删除测量的差别，以及仅有正确读数对联合仪器控制的不足。

第一，取命题 16.4 的二标签记录族、初态 $P_0$，取全部共同控制为恒等且没有量子记忆。实际与理想系统在每个阶段都恰为 $P_0$，但整个历史及最终系统的联合迹距离为

$$
\frac12\|\rho_{H_NS}-\sigma_{H_NS}\|_1
=1-\prod_{t=1}^N(1-\beta_t).
$$

第二，取二标签、初态 $|0\rangle$、两阶段共同控制均为 Hadamard

$$
H=\frac1{\sqrt2}
\begin{pmatrix}1&1\\1&-1\end{pmatrix},
$$

每次控制之后施加计算基理想仪器。若保留物理操作、仅从最终存储历史中边缘化第一结果，则末次结果为零的概率为 $1/2$；若删除第一次记录和测量相互作用，保留两次 $H$ 以及末次测量，则该概率为一。

第三，若去掉定义 16.2 的非破坏仪器形式，仅要求指针制备输入被正确读出，则即使读取错误率为零，带结果的联合仪器也可以与理想 Lüders 仪器具有最大距离。令

$$
X=|0\rangle\langle1|+|1\rangle\langle0|,
\qquad
\mathcal I_z^{\rm flip}(\rho)=X P_z\rho P_zX.
$$

对每个指针输入 $P_x$，该仪器都以概率一报告原标签 $x$，但在输入 $P_0$ 上，其带结果输出与理想输出的迹距离为一。

证明。 第一例中，对输入 $P_0$，实际仪器两个结果的未归一化系统输出分别为 $(1-\beta_t)P_0$ 与 $\beta_tP_0$；理想仪器只输出标签零及系统 $P_0$。新鲜记录使实际各阶段的读出按这些概率相乘，理想历史则确定为 $0^N$。实际得到 $0^N$ 的概率为 $\prod_t(1-\beta_t)$，与该点质量分布的总变差距离为其余历史的总概率，得到第一式。两个模型中的所有系统边缘都保持 $P_0$，不减小这项完整历史误差。

第二例的两次理想测量共有四条路径，其概率为

$$
p(z_1,z_2)=|\langle z_1|H|0\rangle|^2
|\langle z_2|H|z_1\rangle|^2=\frac14.
$$

因此对 $z_1$ 求和给出 $p(z_2=0)=1/2$。同一结论也可由第一步不选择结果的通道计算：

$$
\Delta(HP_0H^\dagger)=\frac{I_2}{2},
\qquad
H\frac{I_2}{2}H^\dagger=\frac{I_2}{2}.
$$

边缘化已存结果实现的是对理想仪器各结果求和，保留上述 $\Delta$。删除第一次相互作用则不施加 $\Delta$，两次控制合成为 $H^2=I_2$，末次测量必得零。

第三例中，$X^2=I$，所以 $\operatorname{tr}\mathcal I_z^{\rm flip}(P_x)=\delta_{zx}$，确实完美读取初始指针标签。但在输入 $P_0$ 上，实际与理想联合输出分别为

$$
|0\rangle\langle0|_Z\otimes P_1,
\qquad
|0\rangle\langle0|_Z\otimes P_0.
$$

两者支撑正交，迹距离为一。因此定理 16.3 需要其给定的非破坏记录仪器形式；仅保留正确读数的校准条件不能推出同一联合通道界。证毕。

### 16.4 正概率历史事件的条件误差

**定义 16.7（历史事件及条件联合输出）。** 令 $\rho,\sigma$ 是同一有限经典历史寄存器 $H$ 与其余可访问系统 $Q$ 上的 cq 密度矩阵；$Q$ 可以包括最终系统、记忆及参考。对一个历史事件 $E$，令 $\Pi_E$ 为对应的历史投影，并记

$$
X=(\Pi_E\otimes I_Q)\rho(\Pi_E\otimes I_Q),
\qquad
Y=(\Pi_E\otimes I_Q)\sigma(\Pi_E\otimes I_Q),
$$

$$
p=\operatorname{tr}X,
\qquad q=\operatorname{tr}Y.
$$

当 $p>0$ 时定义实际条件态 $\rho_E=X/p$；当 $q>0$ 时定义理想条件态 $\sigma_E=Y/q$。概率为零时不定义相应归一化条件态。

**命题 16.8（全历史误差对正概率条件历史的控制）。** 在定义 16.7 中，若

$$
\frac12\|\rho-\sigma\|_1\le\varepsilon,
\qquad q>\varepsilon,
$$

则 $p>0$，且

$$
\frac12\|\rho_E-\sigma_E\|_1
\le\min\left\{1,\frac{\varepsilon}{q}\right\}.
$$

因此定理 16.3 或 16.5 的全输出界可用于任意理想概率大于 $\delta_N$ 的历史事件。仅有全输出小误差不保证所有稀有事件都有小条件误差，也不保证理想正概率事件在实际模型中必有正概率。

证明。 记 $b=\|X-Y\|_1$。由于 $\rho,\sigma$ 在经典历史上分块，事件与补事件的块迹范数相加，而补事件块的迹差为 $q-p$。故

$$
b+|p-q|\le\|\rho-\sigma\|_1\le2\varepsilon.
$$

又有 $b\ge|p-q|$，所以 $|p-q|\le\varepsilon$，从而 $p\ge q-\varepsilon>0$。利用 $\|X\|_1=p$，得到

$$
\begin{aligned}
\frac12\left\|\frac Xp-\frac Yq\right\|_1
&=\frac12\left\|\frac{X-Y}{q}
+X\left(\frac1p-\frac1q\right)\right\|_1\\
&\le\frac{b+|p-q|}{2q}
\le\frac{\varepsilon}{q}.
\end{aligned}
$$

两个密度矩阵的迹距离至多为一，给出所列截断界。

稀有事件的限制可用有限 cq 态直接检验：取两个历史结果 $E,E^c$，在两模型中令事件 $E$ 都有概率 $q>0$，但其条件量子态分别为正交纯态；在 $E^c$ 上取完全相同的条件态及概率。全输出迹距离为 $q$，事件条件迹距离却为一。另一方面，把理想概率 $q$ 的整个 $E$ 块移到同一个量子态的 $E^c$ 块，得到全输出迹距离 $q$ 而实际 $p=0$ 的例子。故不能删除正概率条件及其 $q$ 依赖。证毕。

### 16.5 逐标签平方根测量与全历史记录预算

设共有 $N\ge1$ 个记录阶段，指针标签数为 $d\ge2$。在每一步及每个允许的既有经典历史下，单份新鲜记录的条件单位向量为 $(e_x)_{x\in\mathsf X}$，并统一满足
$$
|\langle e_y,e_x\rangle|\le\mu<1\qquad(x\ne y).
$$
每个阶段使用 $m\ge1$ 份新鲜记录；该阶段内部不混合系统标签，故条件记录为 $e_x^{\otimes m}$，并允许对该阶段的全部 $m$ 份记录进行联合POVM读取。允许在阶段之间施加共同控制，记录向量及读取测量也可依赖此前已存储的经典历史；新记录的残余自由度在读取后被丢弃且不再参与相互作用。以下预算度量全部存储结果、最终系统与所保留有限记忆的联合无条件输出，相对于同一共同控制下的理想指针投影仪器协议的误差。

**推论 16.9（有限全历史误差的充分副本数）。** 记 $R_m=(d-1)\mu^{2m}$。每阶段存在一个有限POVM，使每个标签及每个允许历史下的读取错误率均不超过
$$
b_m=\frac{R_m}{1+R_m}.
$$
因此定理16.3给出
$$
\frac12\|\mathcal H_{\rm actual}-\mathcal H_{\rm ideal}\|_\diamond
\le\sqrt{1-(1-b_m)^N}
=\sqrt{1-(1+R_m)^{-N}}.
$$
特别地，给定 $0<\varepsilon<1$，令
$$
b_*=1-(1-\varepsilon^2)^{1/N}.
$$
当 $0<\mu<1$ 时，以下整数条件足以使整个输出历史的误差不超过 $\varepsilon$：
$$
m\ge m_{\rm suff}
:=\max\left\{1,\left\lceil
\frac{\log((d-1)(1-b_*)/b_*)}{2\log(1/\mu)}
\right\rceil\right\}.
$$
当 $\mu=0$ 时，$m=1$ 即可得到零误差。当 $0<\mu<1$ 时，选择 $m=m_{\rm suff}$ 的构造使用 $Nm_{\rm suff}$ 份新鲜条件记录；这是充分预算，不宣称最少副本数。

更一般地，若第 $t$ 阶段全部既有历史下的条件记录Gram矩阵都满足非对角平方重叠行和至多为 $R_t\ge0$，则
$$
\frac12\|\mathcal H_{\rm actual}-\mathcal H_{\rm ideal}\|_\diamond
\le\sqrt{1-\prod_{t=1}^N(1+R_t)^{-1}}.
$$
这项充分上界不超过 $\varepsilon$ 的充要条件为
$$
\sum_{t=1}^N\log(1+R_t)\le-\log(1-\varepsilon^2).
$$
例如第 $t$ 阶段使用 $m_t$ 份记录、单份重叠模统一至多为 $\mu_t$ 时，可以取 $R_t=(d-1)\mu_t^{2m_t}$。

证明。先对任意有限单位记录族直接构造读取POVM，此处不要求记录向量线性无关。令 $f_x$ 为 $\mathbb C^d$ 的标准正交基，$Vf_x=e_x$，并记通常方向的Gram矩阵
$$
H=V^\dagger V,\qquad H_{yx}=\langle e_y,e_x\rangle,\qquad H_{xx}=1.
$$
取极分解 $V=U\sqrt H$，其中 $U$ 是从 $\operatorname{supp}H$ 到记录张成空间的部分等距映射，且在 $\ker H$ 上为零。因此
$$
U^\dagger U=P_{\operatorname{supp}H},\qquad
UU^\dagger=P_{\operatorname{ran}V},\qquad
U^\dagger V=\sqrt H.
$$
在记录环境 $\mathcal E$ 上选择
$$
M_x=U|f_x\rangle\langle f_x|U^\dagger
+\frac{I_{\mathcal E}-UU^\dagger}{d}.
$$
各项非负，且 $\sum_xM_x=I_{\mathcal E}$，所以它们构成POVM。这是均匀先验平方根测量在信号张成空间外的一种完成，沿用第7.3节所引的标准平方根测量方法；下面直接估计每个标签，而不假定实际标签分布均匀。

由于 $e_x\in\operatorname{ran}V$，补空间项不贡献正确率，且
$$
q_x:=\langle e_x,M_xe_x\rangle
=|\langle f_x,U^\dagger Vf_x\rangle|^2
=\bigl((\sqrt H)_{xx}\bigr)^2.
$$
对上述成功率，采用[式(8)的逐标签平方根测量界](../../../Library/Quantum/montanaro2007distinguishability.md)。文献中的含先验Gram矩阵在均匀先验下为 $G=H/d$，第 $x$ 个标签对平均成功率的贡献为 $q_x/d$；将该式逐项乘以 $d$，得到此处的逐标签界。下面写出其在单位对角Gram矩阵上的推导。取谱分解 $H=\sum_j\lambda_j|u_j\rangle\langle u_j|$，其中 $\lambda_j\ge0$，并定义
$$
r_x=\sum_{y\ne x}|H_{yx}|^2,
\qquad
\nu_j=\lambda_j|\langle u_j,f_x\rangle|^2\quad(\lambda_j>0).
$$
由于 $H_{xx}=1$，正谱上的这些权重满足
$$
\sum_{\lambda_j>0}\nu_j=1,
\qquad
\sum_{\lambda_j>0}\nu_j\lambda_j
=(H^2)_{xx}=1+r_x.
$$
函数 $s\mapsto s^{-1/2}$ 在 $s>0$ 上凸，因此Jensen不等式给出
$$
(\sqrt H)_{xx}
=\sum_{\lambda_j>0}\nu_j\lambda_j^{-1/2}
\ge\left(\sum_{\lambda_j>0}\nu_j\lambda_j\right)^{-1/2}
=\frac1{\sqrt{1+r_x}}.
$$
从而逐标签有
$$
q_x\ge\frac1{1+r_x},\qquad
1-q_x\le\frac{r_x}{1+r_x}.
$$
零特征值对 $\nu_j$ 的贡献为零；整个不等式只在正谱上求和，因此也适用于秩亏Gram矩阵。这一无秩条件的充分界不要求 $(d-1)\max_{x\ne y}|H_{xy}|<1$。

现在将上述构造应用于每个阶段和历史下的乘积记录族。其Gram矩阵满足
$$
H^{(m)}_{yx}=\langle e_y,e_x\rangle^m,
\qquad
\sum_{y\ne x}|H^{(m)}_{yx}|^2\le(d-1)\mu^{2m}.
$$
由于 $r\mapsto r/(1+r)$ 在 $r\ge0$ 上不减，得到统一的 $b_m=R_m/(1+R_m)$。逐阶段、逐历史选择这些测量，再用定理16.3，就得到 $\sqrt{1-(1-b_m)^N}$。一般的 $R_t$ 同样给出 $1-\beta_t\ge(1+R_t)^{-1}$，代入该定理即得非均匀乘积式。对正量取对数，便得到所列分配条件。

因为 $b_*\in(0,1)$，条件 $b_m\le b_*$ 等价于 $R_m\le b_* /(1-b_*)$，并保证
$$
1-(1-b_m)^N\le\varepsilon^2.
$$
对 $0<\mu<1$ 解这个标量不等式、取上整并满足 $m\ge1$，即得 $m_{\rm suff}$。这里对数分子可以为负，故保留与 $1$ 取最大值的条件。$\mu=0$ 时单份记录已两两正交，直接得到 $b_1=0$。证毕。

如果只需更简单的充分表达，可利用
$$
1-\prod_t(1+R_t)^{-1}
\le\sum_t\frac{R_t}{1+R_t}\le\sum_tR_t,
$$
因此 $\sum_tR_t\le\varepsilon^2$ 足够。等量副本时可以选择
$$
m\ge
\left\lceil\frac{\log((d-1)N/\varepsilon^2)}{2\log(1/\mu)}\right\rceil
\qquad(0<\mu<1).
$$
此式把误差预算分配为每阶段至多 $\varepsilon^2/N$，无需把单步平方根误差先按线性和累积。预算计入的是各阶段新准备的条件记录份数；同一环境反复参与相互作用不满足这里的乘积记录假设。

对定理1.3的Zeckendorf开放窗口，取 $L\ge1$，其合法构型空间满足 $d=\dim\mathcal H_L=G_L=F_{L+2}$。若在该空间上的条件记录与共同控制满足本节假设，则同一充分条件直接写成
$$
N(G_L-1)\mu^{2m}\le\varepsilon^2.
$$
这里合法构型约束通过标签数 $G_L$ 进入历史误差预算；此项代入仍以本节的条件记录与共同控制假设为前提。

## 追加锚（新终端）

## 17. 无量子记忆的全历史乘积界达到

**定义 17.1（实二能级历史反馈协议）。** 固定有限阶段数 $N\ge1$ 和参数 $\beta_t\in[0,1]$，令

$$
a_t=\sqrt{1-\beta_t},\qquad b_t=\sqrt{\beta_t},
\qquad s_0=1,\qquad s_k=\prod_{t=1}^k a_t.
$$

系统为 $S=\mathbb C^2$，指针投影为 $P_z=|z\rangle\langle z|$，$z\in\{0,1\}$。不设置可访问量子记忆。第 $t$ 步使用一个新鲜二能级记录，其单位条件向量为

$$
e_{t,0}=a_t|0\rangle+b_t|1\rangle,
\qquad e_{t,1}=b_t|0\rangle+a_t|1\rangle.
$$

条件写入之后在记录的计算基上读取，实际仪器的两个 Kraus 算子是

$$
K_{t,z}=a_tP_z+b_tP_{1-z}.
$$

它们满足 $\sum_zK_{t,z}^\dagger K_{t,z}=I_S$，对指针制备 $P_x$ 的正确结果概率为 $a_t^2=1-\beta_t$。理想比较仪器的结果算子为 $P_z$。这复用第 16.4 条的记录族与第 16.2 条的 Lüders 比较，但采用下述无量子记忆控制类。

对每个已存历史 $h\in\{0,1\}^{t-1}$，在第 $t$ 次写入前施加一个预先确定的实正交矩阵 $U_{t,h}\in O(2)$；它也是合法的系统酉。实际和理想过程使用同一个控制表 $h\mapsto U_{t,h}$，各自按自身已经存储的历史调用。其未归一化结果更新分别为

$$
\mathcal A_{t,h,z}(\rho)
=K_{t,z}U_{t,h}\rho U_{t,h}^\dagger K_{t,z}^\dagger,
\qquad
\mathcal B_{t,h,z}(\rho)
=P_zU_{t,h}\rho U_{t,h}^\dagger P_z.
$$

所有结果都保存在经典历史寄存器 $H_k=Z_1\cdots Z_k$，不改写旧结果、不后选择；量子记录余系统被丢弃且不再耦合。记经过前 $k$ 步的带全部历史输出通道为

$$
\mathcal H_{{\rm actual},k}^{U},
\qquad
\mathcal H_{{\rm ideal},k}^{U}:
\mathcal L(S)\longrightarrow\mathcal L(H_k\otimes S).
$$

控制表一经确定，这些都是对任意输入定义的线性 CPTP 通道。下述达到见证使用两过程相同的固定输入 $P_0$，且不携带参考系统；通道的 diamond 范数仍按通常定义允许有限参考。

**定理 17.2（一个实量子比特及经典反馈同时达到全部前缀界）。** 对定义 17.1 的任意有限 $N$ 和任意 $(\beta_t)_{t=1}^N$，存在一个控制表 $U$，使每个 $1\le k\le N$ 都满足

$$
\begin{aligned}
\frac12\left\|
\mathcal H_{{\rm actual},k}^{U}(P_0)
-\mathcal H_{{\rm ideal},k}^{U}(P_0)
\right\|_1
&=\frac12\left\|
\mathcal H_{{\rm actual},k}^{U}
-\mathcal H_{{\rm ideal},k}^{U}
\right\|_\diamond\\
&=\sqrt{1-s_k^2}
=\sqrt{1-\prod_{t=1}^k(1-\beta_t)}.
\end{aligned}
$$

因此第 16.3 条的乘积常数在这个无可访问量子记忆的实二能级控制子类中仍不能普遍减小；达到不需要静止纠缠参考。控制表可以在实验前按完整有限历史树计算，运行时只读取已存历史。

证明。 对每个历史 $h$，同时递归计算两个实的未归一化分支向量 $\psi_h,\phi_h\in\mathbb R^2$。它们分别表示固定见证输入 $P_0$ 在实际和理想过程中的分支，初值为

$$
\psi_\varnothing=\phi_\varnothing=|0\rangle.
$$

在深度 $k=|h|$，记

$$
p_h=\|\psi_h\|^2,\qquad
q_h=\|\phi_h\|^2,\qquad
c_h=\phi_h^{\mathsf T}\psi_h.
$$

我们逐层构造共同控制，使每个历史都满足

$$
2c_h=s_k(p_h+q_h).
$$

初始两向量相同且范数为一，故该关系在空历史成立。所有 $s_k$ 非负，因此这同时保证 $c_h\ge0$。

固定深度 $t-1$ 的一个历史，暂写 $\psi=\psi_h$、$\phi=\phi_h$、$p=p_h$、$q=q_h$、$c=c_h$、$s=s_{t-1}$、$a=a_t$、$b=b_t$。定义实对称矩阵

$$
X_h
=\psi\phi^{\mathsf T}+\phi\psi^{\mathsf T}
-s\bigl[(a^2-b^2)\psi\psi^{\mathsf T}
+\phi\phi^{\mathsf T}\bigr]
-sb^2pI_2.
$$

由 $a^2+b^2=1$ 和归纳关系，其迹为

$$
\operatorname{tr}X_h
=2c-s\bigl[(a^2-b^2)p+q\bigr]-2sb^2p
=2c-s(p+q)=0.
$$

若 $X_h=0$，取标准实正交基为 $r_0,r_1$。若 $X_h\ne0$，实对称谱定理给出正交归一的特征向量 $v_+,v_-$，特征值分别为 $\lambda,-\lambda$，其中 $\lambda>0$。令

$$
r_0=\frac{v_++v_-}{\sqrt2},
\qquad
r_1=\frac{v_+-v_-}{\sqrt2}.
$$

它们正交归一，而且两种情形都满足

$$
r_z^{\mathsf T}X_hr_z=0\qquad(z=0,1).
$$

选择共同系统酉 $U_{t,h}$ 的第 $z$ 行为 $r_z^{\mathsf T}$。将历史 $h$ 后附结果 $z$ 记为 $hz$，递归定义

$$
\psi_{hz}=K_{t,z}U_{t,h}\psi_h,
\qquad
\phi_{hz}=P_zU_{t,h}\phi_h.
$$

设 $u_z=r_z^{\mathsf T}\psi$、$v_z=r_z^{\mathsf T}\phi$。直接计算两个分支的范数与内积，得到

$$
p_{hz}=b^2p+(a^2-b^2)u_z^2,
\qquad
q_{hz}=v_z^2,
\qquad
c_{hz}=a u_zv_z.
$$

而 $r_z^{\mathsf T}X_hr_z=0$ 正好等价于

$$
2u_zv_z
=s\bigl[b^2p+(a^2-b^2)u_z^2+v_z^2\bigr]
=s(p_{hz}+q_{hz}).
$$

两边乘以 $a$，便得到下一层所需关系

$$
2c_{hz}=as(p_{hz}+q_{hz})
=s_t(p_{hz}+q_{hz}).
$$

这里没有除以 $a,s,p,q$，也没有对分支向量作归一化，所以 $\beta_t=0$、$\beta_t=1$ 和任一模型中的零概率历史都包含在构造内。每个结点选择一次实正交基，沿有限历史树递归，便得到定义在全部历史上的共同控制表。

由实际 Kraus 完备关系及理想投影完备关系，每个结点都有

$$
\sum_{z=0}^1p_{hz}=p_h,
\qquad
\sum_{z=0}^1q_{hz}=q_h.
$$

因此在任意深度 $k$，两族分支权重各自满足 $\sum_{|h|=k}p_h=\sum_{|h|=k}q_h=1$，实际和理想全输出为

$$
\rho_k=\sum_{|h|=k}|h\rangle\langle h|\otimes
|\psi_h\rangle\langle\psi_h|,
\qquad
\sigma_k=\sum_{|h|=k}|h\rangle\langle h|\otimes
|\phi_h\rangle\langle\phi_h|.
$$

对两个未归一化纯态，标准的秩一差值公式给出

$$
\left\|
|\psi_h\rangle\langle\psi_h|
-|\phi_h\rangle\langle\phi_h|
\right\|_1
=\sqrt{(p_h+q_h)^2-4c_h^2}.
$$

该式也可直接由二阶矩阵的迹 $p_h-q_h$、行列式 $c_h^2-p_hq_h\le0$ 及两个特征值得到，涵盖零向量与共线情形。代入已保持的关系，右端变为 $(p_h+q_h)\sqrt{1-s_k^2}$。不同经典历史块的迹范数相加，故

$$
\frac12\|\rho_k-\sigma_k\|_1
=\frac12\sum_{|h|=k}(p_h+q_h)\sqrt{1-s_k^2}
=\sqrt{1-s_k^2}.
$$

这由固定、无参考的输入 $P_0$ 给出两个通道的半 diamond 距离下界；第 16.3 条适用于该共同反馈策略，给出相同的参考系统一致上界。因此通道距离也等于所列值。构造中的同一个有限控制表保持每层关系，所以各前缀同时达到。证毕。

Acín 等，*Physical Review A* **71**，032338（2005），[§III.B、式 (19)–(20)](https://arxiv.org/abs/quant-ph/0410097v2)，证明了对两个已知纯态的 $N$ 个相同副本作适应逐份测量可达到联合 Helstrom 界，可作为适应判别的背景。该副本任务不同于本定理固定 $K_{t,z}$ 与 $P_z$ 仪器的历史比较，且本章条件记录的重叠是 $\langle e_{t,1},e_{t,0}\rangle=2a_tb_t$；本定理的达到结论由上述实谱基递推证明。

上述控制表使用指定模型、参数和固定见证输入，在实验前计算两族候选分支。运行中不测量未知量子态来选择控制，也不查询正在执行的是实际仪器还是理想仪器；两种实验始终使用同一个函数 $h\mapsto U_{t,h}$。对别的输入，该固定表仍定义合法通道，而定理 16.3 仍提供统一上界。

第 16.4 条用可访问量子记忆及 SWAP 给出达到构造，并没有断言量子记忆是必要条件。本定理把达到构造放进更小的控制类：一个系统量子比特、经典历史及预先计算的实酉反馈。它不限制经典历史或控制表的存储量，也不声称无反馈协议都能达到。

这里最大化的是实际仪器与理想仪器的完整历史差异，用来确定仅依据 $(\beta_t)$ 所能保证的最坏常数。它不是保持某个指针标签的最优策略；标签持久性仍需第 16.5 条的转移条件，不能由本定理的误差达到推出。

## 追加锚（新终端）

## 18. 只读取经典历史时的精确两步边界

**定义 18.1（丢弃系统后的经典历史误差）。** 沿用定义 17.1 的二标签记录族，但允许各历史分支的共同系统控制为任意酉矩阵 $U_{t,h}\in U(2)$。系统初态 $\rho$ 可以是任意二阶密度矩阵；输入不携带参考系统，过程不使用可访问辅助量子记忆。保留全部经典历史 $H_N$，最终丢弃系统，只比较历史分布。所有记录单元仍新鲜准备，读取后的量子余系统不再耦合，不后选择。

对有限阶段数 $N\ge1$ 和参数 $\boldsymbol\beta=(\beta_1,\ldots,\beta_N)\in[0,1]^N$，实际结果算子与理想结果算子分别为

$$
K_{t,z}=\sqrt{1-\beta_t}P_z+\sqrt{\beta_t}P_{1-z},
\qquad P_z,\qquad z\in\{0,1\}.
$$

实际与理想过程使用同一个共同控制表 $U$，各自按已有历史调用它。记其经典路径分布为 $p_{\rho,U}^{\rm actual}$ 与 $p_{\rho,U}^{\rm ideal}$，定义

$$
T_N(\boldsymbol\beta)
=\sup_{\rho,U}
\operatorname{TV}\!\left(p_{\rho,U}^{\rm actual},p_{\rho,U}^{\rm ideal}\right),
\qquad
\operatorname{TV}(p,q)=\frac12\sum_h|p(h)-q(h)|.
$$

本章不保留量子参考，因而该目标不直接等同于允许输出参考的 diamond 范数优化。定理 16.3 的全输出界仍给出本目标的上界，但丢弃系统可能严格减小最优值。本章的最优值始终限定于无输入或输出参考的纯经典分布任务，不推出任意固定协议的量子参考均无增益。

**定理 18.2（两步纯经典历史误差的精确最优值）。** 取 $N=2$，$\beta_1=e$、$\beta_2=f$，其中 $e,f\in[0,1/2]$。则

$$
T_2(e,f)
=\max\left\{
 e+f-ef,\ \sqrt{f^2+(1-2f)e}
\right\}.
$$

第一项由指针初态 $P_0$ 与恒等控制达到；第二项由平衡纯初态 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 及按第一结果选择的末次测量基达到。所有最优值均可使用实正交系统控制实现。

两种策略的平方值差为

$$
f^2+(1-2f)e-(e+f-ef)^2
=e\bigl[1-4f+2f^2-(1-f)^2e\bigr].
$$

该因子式决定在给定 $e,f$ 下哪种达到策略给出较大的历史差异；等于零时两种策略都达到最优值。

证明。 第一共同酉可吸收入初态。对任一固定控制表，经典概率差线性依赖 $\rho$，总变差是其凸函数；将混态作纯态凸分解可知，其值不超过其中某个纯态的值。因此可以只优化纯输入。写作

$$
|\psi\rangle=\sqrt t|0\rangle+e^{i\theta}\sqrt{1-t}|1\rangle,
\qquad 0\le t\le1.
$$

令 $D=\operatorname{diag}(1,e^{i\theta})$。第一步的实际算子与理想投影均与 $D$ 交换；把输入换为相位为零的向量，并把每个第二步共同控制 $U_z$ 换成 $U_zD$，便保留所有经典路径概率。因此可以令 $\theta=0$。

给定第一结果 $z$，记实际和理想未归一化分支向量为

$$
\psi_z=K_{1,z}\psi,
\qquad
\phi_z=P_z\psi,
\qquad
p_z=\|\psi_z\|^2,
\qquad q_z=\|\phi_z\|^2.
$$

于是 $q_0=t$、$q_1=1-t$，并且

$$
p_z=e+(1-2e)q_z,
\qquad
|\langle\phi_z,\psi_z\rangle|^2=(1-e)q_z^2.
$$

令 $d=1-2f\ge0$。第二步共同控制 $U_z$ 之后，结果 $w$ 的实际与理想联合路径概率之差为

$$
\langle w|U_zY_zU_z^\dagger|w\rangle,
\qquad
Y_z=d|\psi_z\rangle\langle\psi_z|
-|\phi_z\rangle\langle\phi_z|+fp_zI_2.
$$

这是因为 $K_{2,w}^\dagger K_{2,w}=fI_2+dP_w$。两个 $Y_z$ 为 Hermitian 矩阵；其迹为 $p_z-q_z$，一般不为零。对任意 Hermitian 矩阵，任意基中的对角元绝对值之和不超过迹范数，在特征基中达到。两个历史分支可以分别选择 $U_z$，所以对固定 $t$ 的精确优化为

$$
\frac12\sum_{z=0}^1\|Y_z\|_1.
$$

输入已取实数，故 $Y_z$ 为实对称矩阵，所需特征基及控制均可选为实的。

令 $r=|2t-1|\in[0,1]$，定义

$$
A=f^2+de,\qquad
B=2f(f+de),\qquad
C=f^2-d^2e(1-e).
$$

对一个二阶 Hermitian 矩阵，迹范数等于其迹绝对值和特征值间距的较大者。这里 $|\operatorname{tr}Y_z|=er$；直接计算特征值间距的平方，两个分支依次给出 $A+Br+Cr^2$ 和 $A-Br+Cr^2$，其中分支次序不影响其和。因而

$$
T_2(e,f)=\max_{0\le r\le1}F(r),
$$

$$
F(r)=\frac12\left[
\max\{er,\sqrt{A+Br+Cr^2}\}
+\max\{er,\sqrt{A-Br+Cr^2}\}
\right].
$$

为核对间距公式，可对 $q=q_z$ 写 $p=e+(1-2e)q$。矩阵 $d|\psi_z\rangle\langle\psi_z|-|\phi_z\rangle\langle\phi_z|$ 加上标量矩阵不改变特征值间距，该间距平方为

$$
(dp+q)^2-4d(1-e)q^2.
$$

代入 $q=(1\pm r)/2$ 即得到上述两个二次式。因此它们在所用区间内均非负。

下面直接证明最大值在 $r=0$ 或 $r=1$ 取得。记

$$
L=e+f-ef,\qquad M=\max\{\sqrt A,L\}.
$$

端点满足

$$
F(0)=\sqrt A,
\qquad
\sqrt{A+B+C}=2f+de,
\qquad
\sqrt{A-B+C}=de,
\qquad F(1)=L.
$$

此外，有 $B\ge0$、$C\le A$，以及

$$
4AC-B^2=-4d^3e^2(1-e)\le0.
$$

置 $u=\sqrt{A+Br+Cr^2}$、$v=\sqrt{A-Br+Cr^2}$，则 $u\ge v$。两个最大值的和可写成

$$
F(r)=\max\left\{er,\frac{er+u}{2},\frac{u+v}{2}\right\}.
$$

第一项不超过 $e\le L\le M$。对第三项，由 $C\le A$ 及 $0\le r\le1$，有 $A-Cr^2\ge0$；同时

$$
(A-Cr^2)^2-
\bigl[(A+Cr^2)^2-B^2r^2\bigr]
=(B^2-4AC)r^2\ge0.
$$

根号中的量等于 $u^2v^2\ge0$，因此 $uv\le A-Cr^2$。由此

$$
\left(\frac{u+v}{2}\right)^2
=\frac{A+Cr^2+uv}{2}\le A,
$$

故第三项也不超过 $\sqrt A\le M$。

对第二项，$2M-er\ge0$。定义

$$
Q(r)=(2M-er)^2-(A+Br+Cr^2)
=4M^2-A-(4Me+B)r+(e^2-C)r^2.
$$

有 $Q(0)=4M^2-A\ge3A$。又因为 $M\ge L=(e+2f+de)/2$，

$$
Q(1)=(2M-e)^2-(2f+de)^2\ge0.
$$

最后，在 $e,f\in[0,1/2]$ 上，

$$
A-(e^2-C)
=2f\bigl[e(1-2e)+f(1-2e+2e^2)\bigr]\ge0.
$$

所以 $e^2-C\le A$。将二次式与其端点连接，得到

$$
\begin{aligned}
Q(r)
&=(1-r)Q(0)+rQ(1)-(e^2-C)r(1-r)\\
&\ge(1-r)3A-Ar(1-r)
=A(1-r)(3-r)\ge0.
\end{aligned}
$$

于是 $u\le2M-er$，第二项也不超过 $M$。结合三个分支，$F(r)\le M$ 对整个闭区间成立；这里没有除以参数或根式，包含所有端点与零根情形。

两种达到策略分别实现两个端点。取初态 $P_0$、全部控制为恒等，则系统始终为 $P_0$，理想历史确定为 $00$，实际得到 $00$ 的概率为 $(1-e)(1-f)$，故总变差为 $L$。

取 $t=1/2$、初态 $|+\rangle$ 时，令 $g=f+de$、$h=d\sqrt{e(1-e)}$，上述两矩阵为

$$
Y_0=\frac12\begin{pmatrix}-g&h\\h&g\end{pmatrix},
\qquad
Y_1=\frac12\begin{pmatrix}g&h\\h&-g\end{pmatrix},
\qquad g^2+h^2=A.
$$

它们各有特征值 $\pm\sqrt A/2$。对每个第一结果 $z$ 选择使 $Y_z$ 对角的共同实控制 $U_z$，便达到 $F(0)=\sqrt A$；$A=0$ 时任取控制即可。该控制表只依赖模型参数与第一结果，实验前即可确定。选取两种策略中较大的一种即得结论；陈述中的策略分界因子式由 $A-L^2$ 直接展开得到。证毕。

**命题 18.3（完全随机读出与末次完美读出的任意有限历史边界）。** 在定义 18.1 的同一纯经典观察类中，有以下两个精确边界。

若全部 $\beta_t=1/2$，则

$$
T_N(1/2,\ldots,1/2)=1-2^{-N}.
$$

若 $\beta_N=0$，其余 $\beta_t\in[0,1]$ 任意，则

$$
T_N(\beta_1,\ldots,\beta_{N-1},0)
=\sqrt{1-\prod_{t=1}^{N-1}(1-\beta_t)}.
$$

空乘积取一，因此第二式在 $N=1$ 时为零。

证明。 第一种情形中，$K_{t,z}=I_2/\sqrt2$，所以任何条件输入及控制下的两个实际结果概率都为 $1/2$。实际全部 $2^N$ 条历史均匀分布，与任意理想概率分布 $q$ 的总变差不超过 $1-2^{-N}$。具体地，令 $m=2^N$，有

$$
\operatorname{TV}(\operatorname{Unif}_m,q)
=1-\sum_h\min\{1/m,q(h)\}\le1-1/m,
$$

因为至少存在一个 $q(h)\ge1/m$。取初态 $P_0$ 和恒等控制使理想历史确定为 $0^N$，便达到该界。

第二种情形中，定理 16.3 对前 $N-1$ 步的全部历史及系统输出给出右端上界。最后一步的共同控制及共同完美测量是同一个 CPTP 后处理，丢弃系统并保留其结果不增加该距离，故此界也控制最终纯经典分布。

为达到它，若 $N\ge2$，采用定理 17.2 对前 $N-1$ 步给出的固定输入 $P_0$ 与共同控制表。对每个旧历史 $h$，记两个未归一化条件系统态之差为

$$
D_h=|\psi_h\rangle\langle\psi_h|-|\phi_h\rangle\langle\phi_h|.
$$

在最后一步，按历史选择同一个系统酉，将 $D_h$ 的特征基送到指针基，再使用 $\beta_N=0$ 的完美指针读出。该末次读取的两个概率差就是 $D_h$ 的两个特征值，因此对最后结果求绝对值之和得到 $\|D_h\|_1$。再对旧历史求和，最后纯经典总变差恰为前缀联合迹距离，即定理 17.2 已达到的右端。零矩阵分支任取测量基，不需要对历史概率归一化。$N=1$ 时实际与理想仪器完全相同，直接得到零。

上述第一式在 $N=2$ 时给出 $T_2(1/2,1/2)=3/4$，与定理 18.2 一致，而定理 17.2 的历史加系统输出最优误差是 $\sqrt3/2$；同一记录精度在不同保留输出上具有不同的最坏边界。第二式的达到构造则把此前留在活动系统中的条件态差异转成经典历史概率差。证毕。

## 追加锚（新终端）

## 19. 经典历史延续的三参数最优递推

**定义 19.1（未归一化分支对的延续代价）。** 沿用定义 18.1 的纯经典历史观察任务：一个活动系统量子比特、任意共同历史控制酉 $U\in U(2)$、新鲜对称非破坏记录、全部结果存储为经典，最后丢弃系统。输入和输出均不保留参考，过程不使用可访问辅助量子记忆。每次记录的实际结果算子为

$$
K_{\beta,z}=\sqrt{1-\beta}P_z+\sqrt\beta P_{1-z},
\qquad z\in\{0,1\},\qquad\beta\in[0,1],
$$

理想结果算子为 $P_z$。两过程使用同一个历史控制表，读取后的量子环境不再耦合，不后选择。

在一个已存历史后，给定两个未归一化候选分支向量 $\psi,\phi\in\mathbb C^2$。因为每个结果只有一个 Kraus 算子，纯初态及按结果更新始终给出这种向量对。定义

$$
p=\|\psi\|^2,\qquad q=\|\phi\|^2,
\qquad k=|\langle\phi,\psi\rangle|^2,
$$

以及三参数域

$$
\mathcal G=\{(p,q,k)\in\mathbb R^3:
 p,q\ge0,\ 0\le k\le pq\}.
$$

分支权重不重新归一化，允许 $p=0$ 或 $q=0$。给定有限剩余参数列 $\boldsymbol\beta=(\beta_1,\ldots,\beta_n)$，从该分支对继续执行共同控制及两种记录仪器，记末端延续历史 $w\in\{0,1\}^n$ 的未归一化向量为 $\psi_w,\phi_w$。延续代价是

$$
\sup_U\sum_{w\in\{0,1\}^n}
\left|\|\psi_w\|^2-\|\phi_w\|^2\right|.
$$

这里不乘 $1/2$，并保留原分支的两个权重。下述定理证明此代价只依赖 $(p,q,k)$，记为 $V_{\boldsymbol\beta}(p,q,k)$。

**定理 19.2（完整酉取向域与精确有限 Bellman 递推）。** 定义 19.1 的延续代价在 $\mathcal G$ 上良定义。对每个 $(p,q,k)\in\mathcal G$，令

$$
\begin{aligned}
\mathcal F(p,q,k)=\bigl\{(u,v)\in[0,p]\times[0,q]:\;&
[k-uv-(p-u)(q-v)]^2\\
&\le4uv(p-u)(q-v)\bigr\}.
\end{aligned}
$$

它非空且紧，恰好等于对同一个共同酉 $U\in U(2)$ 取值时的可达强度对

$$
u=|\langle0|U\psi\rangle|^2,
\qquad v=|\langle0|U\phi\rangle|^2.
$$

对下一步参数 $\beta\in[0,1]$ 和 $(u,v)\in\mathcal F(p,q,k)$，定义后继三元组

$$
\begin{aligned}
G_0^\beta(p,q,k;u,v)
&=\bigl(\beta p+(1-2\beta)u,\ v,\ (1-\beta)uv\bigr),\\
G_1^\beta(p,q,k;u,v)
&=\bigl(\beta p+(1-2\beta)(p-u),\ q-v,\\
&\hspace{5em}(1-\beta)(p-u)(q-v)\bigr).
\end{aligned}
$$

它们都属于 $\mathcal G$。空参数列与一般有限递推满足

$$
V_\varnothing(p,q,k)=|p-q|,
$$

$$
\begin{aligned}
V_{(\beta,\boldsymbol\gamma)}(p,q,k)
=\max_{(u,v)\in\mathcal F(p,q,k)}
\bigl[&V_{\boldsymbol\gamma}(G_0^\beta(p,q,k;u,v))\\
+&V_{\boldsymbol\gamma}(G_1^\beta(p,q,k;u,v))\bigr].
\end{aligned}
$$

所有有限步控制最大值都达到。对固定长度 $n$，$V_{\boldsymbol\beta}(p,q,k)$ 连续依赖 $(\boldsymbol\beta,p,q,k)\in[0,1]^n\times\mathcal G$，包括零分支和秩亏边界。

只剩一步时，有完整参数域上的闭式

$$
V_{(\beta)}(p,q,k)
=\max\left\{|p-q|,
\sqrt{\bigl((1-2\beta)p+q\bigr)^2-4(1-2\beta)k}
\right\}.
$$

定义 18.1 的原始归一化任务因而满足

$$
T_N(\beta_1,\ldots,\beta_N)
=\frac12V_{(\beta_1,\ldots,\beta_N)}(1,1,1).
$$

证明。 先说明三参数确实足以确定未来最优代价。两个向量分别乘整体相位不改变其密度算子，也不改变任何给定后续协议的路径概率。可以选择这些相位，使内积为非负实数 $\sqrt k$；若内积为零，相位任取。此时按列 $(\psi,\phi)$ 的 Gram 矩阵为

$$
G(p,q,k)=\begin{pmatrix}p&\sqrt k\\\sqrt k&q\end{pmatrix}.
$$

$\mathcal G$ 的条件恰使该矩阵正半定，它的正平方根两列就实现任意给定的三元组。

若两对向量有同一个 Gram 矩阵，则按对应向量定义其张成空间之间的线性映射。这个定义良好：任意线性组合的范数平方由同一 Gram 矩阵给出，故初始组合为零时目标组合也为零。它保持内积，两个张成空间维数相等，再为正交补选择对应正交基，就得到整个 $\mathbb C^2$ 上的共同酉。这包含秩二、秩一和零维张成空间。

因此具有相同 $(p,q,k)$ 的两对候选向量，经各自无关的整体相位调整后，可由同一个系统酉相互转换。将该酉与下一步共同控制复合，给出两个控制集合之间的双射，未来最优代价相等；没有剩余步骤时两者都只给出 $|p-q|$。所以 $V$ 良定义。

下面证明 $\mathcal F$ 的取向刻画。固定共同酉并在其输出基中写两向量，内积分成两个坐标贡献，模长分别为

$$
\ell_0=\sqrt{uv},
\qquad \ell_1=\sqrt{(p-u)(q-v)}.
$$

这两个复数之和的模必须等于 $\sqrt k$，故三角不等式给出

$$
|\ell_0-\ell_1|\le\sqrt k\le\ell_0+\ell_1.
$$

平方后，这等价于

$$
|k-\ell_0^2-\ell_1^2|\le2\ell_0\ell_1,
$$

再次平方即为 $\mathcal F$ 的多项式条件。

反过来，设 $(u,v)$ 满足该条件。若 $\ell_0\ell_1>0$，则

$$
\left|\frac{k-\ell_0^2-\ell_1^2}{2\ell_0\ell_1}\right|\le1,
$$

所以可以选择两个复相位，使模长为 $\ell_0,\ell_1$ 的两数之和具有模 $\sqrt k$。若至少一个模长为零，多项式条件强制 $k=\ell_0^2+\ell_1^2$，任意相对相位即可。特别地，二者均为零时必有 $k=0$。

据此构造坐标向量

$$
\psi'=\begin{pmatrix}\sqrt u\\\sqrt{p-u}\end{pmatrix},
\qquad
\phi'=\begin{pmatrix}\sqrt v\,e^{-i\alpha_0}\\
\sqrt{q-v}\,e^{-i\alpha_1}\end{pmatrix},
$$

使 $|\langle\phi',\psi'\rangle|^2=k$。再给 $\phi'$ 乘一个整体相位，可使其 Gram 矩阵与已调整相位的初始向量对完全相同，而强度 $u,v$ 不变。上述共同酉扩张于是将初始对同时送到这对坐标向量。若初始向量先调整过整体相位，将这些无关相位还原也不改变最终坐标强度。因此同一个合法 $U$ 实现所指定 $(u,v)$。

这证明可行域既没有遗漏共同酉，也没有允许两候选态独立旋转。取任意共同酉可知可行域非空；多项式条件定义闭集，且包含在有界矩形中，所以它紧。一般内部可行点依赖复相对相位，不能在此证明中未经论证地把 $U(2)$ 缩成实正交群。

对选定 $(u,v)$，实际结果零与理想结果零的更新向量为 $K_{\beta,0}U\psi$ 和 $P_0U\phi$。它们的范数平方分别为

$$
p_0=(1-\beta)u+\beta(p-u)
=\beta p+(1-2\beta)u,
\qquad q_0=v.
$$

内积只含第零坐标，因此其平方模为 $k_0=(1-\beta)uv$。结果一同理给出 $G_1^\beta$。这些参数非负，且

$$
p_0q_0-k_0=\beta(p-u)v\ge0,
\qquad
p_1q_1-k_1=\beta u(q-v)\ge0.
$$

所以两个后继确实仍在 $\mathcal G$，并满足

$$
p_0+p_1=p,\qquad q_0+q_1=q.
$$

这也解释了 $\beta>1/2$ 时 $1-2\beta$ 为负不造成困难：每个实际分支权重仍是 $u,p-u$ 的非负线性组合。更新没有除以分支权重，参数端点及零概率分支直接保留。

对任何第一步共同酉，已存结果零和一后的控制表可以各自独立指定，两个分支对绝对差异总和的贡献相加。后继代价只取决于已经计算的三元组，故任何延续策略的代价不超过递推右端的相应值。反过来，先实现任意可行 $(u,v)$，再在两个已存结果分支分别采用最优后继策略，就实现它们的和；共同酉取向的完整刻画因此给出所列 Bellman 递推。

为同时证明最大值和连续性，不需要假设随参数移动的可行域有额外正则性。选择 $G(p,q,k)^{1/2}$ 的两列作为规范候选向量。正平方根在正半定矩阵锥上连续，所以该代表在整个 $\mathcal G$ 上连续，包括零矩阵和秩一边界。

给定有限剩余长度 $n$，全部控制表属于固定紧空间

$$
\mathcal U_n
=\prod_{t=1}^{n}\prod_{h\in\{0,1\}^{t-1}}U(2).
$$

空长度时取单点空间。对这个空间中的每个控制表，分支向量由有限次矩阵乘法构成，$K_{\beta,z}$ 连续依赖 $\beta\in[0,1]$，最终绝对差异之和连续依赖规范向量、参数列及控制。紧控制空间上的最大值达到；同一固定紧空间上的连续参数化最大值函数也连续。因此 $V$ 具有所述连续性，且在每个有限历史节点可以选取最优后继策略。再由后继三元组的连续性和 $\mathcal F$ 的紧性，递推右端的最大值也达到。

只有一步时，令 $d_\beta=1-2\beta$ 并定义

$$
Y_\beta
=d_\beta|\psi\rangle\langle\psi|
-|\phi\rangle\langle\phi|+\beta pI_2.
$$

两个末次经典结果的权重差是 $UY_\beta U^\dagger$ 的两个对角元。其绝对值和不超过 $\|Y_\beta\|_1$，由共同酉选择特征基即可达到。矩阵的迹为 $p-q$，一般不为零；去掉标量部分不改变特征值间距，而间距平方为

$$
(d_\beta p+q)^2-4d_\beta k.
$$

二阶 Hermitian 矩阵的迹范数等于迹绝对值与特征值间距两者的最大值，得到所列单步公式。若 $d_\beta\ge0$，根式内由 $k\le pq$ 得到下界 $(d_\beta p-q)^2\ge0$；若 $d_\beta<0$，它是平方项加 $4|d_\beta|k$。因此该式覆盖全部 $\beta\in[0,1]$，以及 $p=0$、$q=0$、$k=0$ 等退化情形。

最后，对原始任务中的固定控制表，经典总变差是共同输入密度矩阵的凸函数；任意混态的值不超过其某个纯态分量的值，所以优化时纯输入足够。两个模型从同一个归一化纯态开始，三参数均为 $(1,1,1)$，其初始取向由第一步共同酉吸收。延续代价没有 $1/2$ 因子，恢复这个因子即得 $T_N=V_{\boldsymbol\beta}(1,1,1)/2$。证毕。

本定理给出有限历史最优值的精确连续递推，不把任意长度的最优值宣称为已有闭式，也不保证该递推的数值求解或经典控制表具有固定复杂度。三元组描述的是同一旧历史上的两个未归一化候选系统态；所有旧历史仍被保留并可供后续控制使用。

**命题 19.3（累计读取误差不能直接替代前两步）。** 令

$$
E=1-(1-\beta_1)(1-\beta_2).
$$

断言 $T_3(\beta_1,\beta_2,\beta_3)=T_2(E,\beta_3)$ 即使在 $E,\beta_3\in[0,1/2]$ 时也不成立。具体地，取三个参数均为 $1/10$，有合法的共同控制策略达到

$$
T_3(1/10,1/10,1/10)
\ge\frac3{20}+\frac{3\sqrt5}{25}
>\frac{9\sqrt5}{50}
=T_2(19/100,1/10).
$$

这里给出可达到的三步下界，它严格超过两步替代值；不宣称该下界是三步全局最优值。

证明。 取初态 $|+\rangle$、第一控制为恒等，第二步按第一结果选择

$$
U_{2,0}=\frac1{\sqrt5}\begin{pmatrix}1&2\\-2&1\end{pmatrix},
\qquad
U_{2,1}=\frac1{\sqrt5}\begin{pmatrix}2&1\\-1&2\end{pmatrix}.
$$

两个矩阵都是实正交酉。前两步后，按已存历史 $ij$ 索引的实际与理想未归一化向量分别为

$$
\begin{array}{c|c|c}
ij&\psi_{ij}&\phi_{ij}\\\hline
00&(3,-1)^{\mathsf T}/(2\sqrt{10})&(1,0)^{\mathsf T}/\sqrt{10}\\
01&(1,-3)^{\mathsf T}/(2\sqrt{10})&(0,-2)^{\mathsf T}/\sqrt{10}\\
10&(3,1)^{\mathsf T}/(2\sqrt{10})&(1,0)^{\mathsf T}/\sqrt{10}\\
11&(1,3)^{\mathsf T}/(2\sqrt{10})&(0,2)^{\mathsf T}/\sqrt{10}.
\end{array}
$$

这些向量由定义 18.1 的两步更新直接给出。例如第一结果为零时，实际第一步向量是 $(3,1)^{\mathsf T}/\sqrt{20}$，经 $U_{2,0}$ 变为 $(1,-1)^{\mathsf T}/2$，再乘两个第二步对角 Kraus 算子即得到 $\psi_{00},\psi_{01}$。理想第一步向量为 $(1,0)^{\mathsf T}/\sqrt2$，经同一控制和相应投影得到所列 $\phi_{00},\phi_{01}$；第一结果为一时计算相同。

实际四分支的权重均为 $1/4$；理想权重在 $j=0$ 时为 $1/10$，在 $j=1$ 时为 $2/5$。最后一步的差值矩阵为

$$
Y_{ij}=\frac45\psi_{ij}\psi_{ij}^{\mathsf T}
-\phi_{ij}\phi_{ij}^{\mathsf T}
+\frac1{10}\|\psi_{ij}\|^2I_2.
$$

直接相乘得

$$
Y_{00}=\frac1{200}\begin{pmatrix}21&-12\\-12&9\end{pmatrix},
\qquad
Y_{10}=\frac1{200}\begin{pmatrix}21&12\\12&9\end{pmatrix},
$$

$$
Y_{01}=\frac1{200}\begin{pmatrix}9&-12\\-12&-39\end{pmatrix},
\qquad
Y_{11}=\frac1{200}\begin{pmatrix}9&12\\12&-39\end{pmatrix}.
$$

按已存 $ij$ 选择共同末次实酉，将 $Y_{ij}$ 的特征基送到计算基。由定理 19.2 的单步证明，最后两个概率差是其两个特征值。$j=0$ 的矩阵正定，迹范数为其迹 $3/20$；$j=1$ 的矩阵行列式为负，迹范数为特征值间距 $3\sqrt5/25$。所以该策略的完整经典历史总变差为

$$
\frac12\sum_{i,j}\|Y_{ij}\|_1
=\frac3{20}+\frac{3\sqrt5}{25}.
$$

另一方面，$E=19/100$，定理 18.2 给出

$$
T_2(19/100,1/10)
=\max\left\{\frac{271}{1000},\frac{9\sqrt5}{50}\right\}
=\frac{9\sqrt5}{50}.
$$

两值的差为

$$
\frac3{20}-\frac{3\sqrt5}{50}
=\frac{3(5-2\sqrt5)}{100}>0,
$$

其中严格不等式由 $25>20$ 得到。控制表只依赖已存历史及固定模型参数，两实验始终使用同一个表，因此是定义 18.1 允许的策略，反驳所列替代断言。证毕。

在该例前两步后的实际权重都是 $p=1/4$，理想权重却分成 $q=1/10$ 与 $q=2/5$，对应平方重叠分别为 $k=9/400$ 与 $k=9/100$。后续读取分别使用这些已存历史上的候选三元组；累计标量 $E$ 不保留它们的分支权重与重叠结构。本章仍只处理丢弃最终系统、没有输入或输出参考的经典路径总变差任务。

## 追加锚（新终端）

## 20. 实反馈的充分性与最终量子输出的价值

**定理 20.1（任意有限经典历史的实反馈达到与一维递推）。** 沿用定义 19.1 的候选分支对、参数域 $\mathcal G$ 和延续代价 $V_{\boldsymbol\beta}$。对任意有限参数列 $\boldsymbol\beta\in[0,1]^n$ 以及任意实候选向量 $\psi,\phi\in\mathbb R^2$，完整 $U(2)$ 共同历史控制的最大值都由一个全部控制属于 $O(2)$ 的反馈表达到。向量可以未归一化、为零、正交或共线；不增加可访问量子记忆或参考系统。

对 $(p,q,k)\in\mathcal G$ 且 $p>0$，定义

$$
v_\pm(u)=
\frac{\left[\sqrt{ku}\pm\sqrt{(pq-k)(p-u)}\right]^2}{p^2},
\qquad 0\le u\le p.
$$

使用定理 19.2 的后继映射 $G_0^\beta,G_1^\beta$，完整复取向域上的 Bellman 递推可以精确缩为

$$
\begin{aligned}
V_{(\beta,\boldsymbol\gamma)}(p,q,k)
&=\max_{\substack{0\le u\le p\\\sigma\in\{-,+\}}}
\bigl[
V_{\boldsymbol\gamma}
\bigl(G_0^\beta(p,q,k;u,v_\sigma(u))\bigr)\\
&\hspace{8em}
+V_{\boldsymbol\gamma}
\bigl(G_1^\beta(p,q,k;u,v_\sigma(u))\bigr)
\bigr].
\end{aligned}
$$

每个节点只需优化一个实区间及两个符号，最大值达到。空参数列仍取 $V_\varnothing(p,q,k)=|p-q|$，零权重边界为

$$
V_{\boldsymbol\beta}(0,q,0)=q,
\qquad
V_{\boldsymbol\beta}(p,0,0)=p.
$$

因此定义 18.1 的原始任务

$$
T_N(\boldsymbol\beta)
=\frac12V_{\boldsymbol\beta}(1,1,1)
$$

也可以用实纯初态和全实共同反馈表达到。

这一结论限定于所给仪器族及最终只读取经典历史的目标。它给出存在一个最优实控制表，不要求复制任意给定复控制表的全部叶分布，也不意味着每个边界取向都最优。一维递推仍保留三参数分支状态和全部已存历史，没有把任意长度的最优值化为闭式，也不保证控制树的规模具有统一效率界。

证明。 首先证明递推所需要的一条权重方向凸性。固定有限尾列 $\boldsymbol\gamma$、$P\ge0$ 和 $c\in[0,P]$，取

$$
\psi_c=\begin{pmatrix}\sqrt c\\\sqrt{P-c}\end{pmatrix},
\qquad
\phi_s=\sqrt s\,|0\rangle,
\qquad s\ge0.
$$

该向量对的三参数是 $(P,s,cs)$。对一个固定的完整共同控制表 $\pi$，令 $A_w^\pi,B_w^\pi$ 分别是末端历史 $w$ 上实际与理想的分支算子乘积，并记

$$
a_w^\pi=\|A_w^\pi\psi_c\|^2,
\qquad
b_w^\pi=\|B_w^\pi|0\rangle\|^2.
$$

固定表的代价就是

$$
J_\pi(s)=\sum_w|a_w^\pi-sb_w^\pi|.
$$

每项都是仿射函数的绝对值，故 $J_\pi$ 关于 $s$ 凸。控制表在所有可能历史上都有定义，包括零概率历史；所有 $s$ 使用同一个控制表空间，虽然实现最优值的表可以随 $s$ 变化。因此对 $s,t\ge0$、$\lambda\in[0,1]$，有

$$
\begin{aligned}
&V_{\boldsymbol\gamma}
\bigl(P,\lambda s+(1-\lambda)t,
c[\lambda s+(1-\lambda)t]\bigr)\\
&\quad=\sup_\pi J_\pi(\lambda s+(1-\lambda)t)\\
&\quad\le\lambda\sup_\pi J_\pi(s)
+(1-\lambda)\sup_\pi J_\pi(t).
\end{aligned}
$$

于是 $s\mapsto V_{\boldsymbol\gamma}(P,s,cs)$ 凸。总分支权重守恒还给出 $J_\pi(s)\le P+s$，所以这些上确界有限；空尾列及 $P=c=0$ 也包括在内。这只建立所列方向的凸性，没有假设 $V$ 关于 $(p,q,k)$ 联合凸。

接着确定共同酉可行域在固定 $u$ 时的完整切片。设 $p>0$。对一个实候选对，先用同一个实正交变换把 $\psi$ 送到 $\sqrt p|0\rangle$，再利用 $\phi$ 的无关整体符号和第二坐标的基反射，得到代表

$$
\psi=\begin{pmatrix}\sqrt p\\0\end{pmatrix},
\qquad
\phi=\begin{pmatrix}\sqrt{k/p}\\\sqrt{q-k/p}\end{pmatrix}.
$$

整体符号不改变候选密度算子或路径概率，这里不把它当作只对一个候选施加的物理控制。上述规范式也为每个 $p>0$ 的合法三元组提供实代表；由定理 19.2 的共同酉不变性，其完整复可行域就是该三元组的 $\mathcal F(p,q,k)$。

固定实际第零坐标强度 $u\in[0,p]$。任何共同复酉的第一行在去掉无关行相位后，都可以写成

$$
r_\theta=
\left(\sqrt{u/p},\ e^{i\theta}\sqrt{(p-u)/p}\right).
$$

在 $u=0$ 或 $u=p$ 时，消失坐标的相位任取。理想第零坐标强度为

$$
v(\theta)=
\frac{ku+(pq-k)(p-u)
+2\sqrt{k(pq-k)u(p-u)}\cos\theta}{p^2}.
$$

任意单位复行向量都可以补成一个酉矩阵，因此定理 19.2 的完整可行域在此 $u$ 上恰为闭区间

$$
\{v:(u,v)\in\mathcal F(p,q,k)\}
=[v_-(u),v_+(u)].
$$

区间内部由不同的 $\cos\theta$ 取得，两个端点则由实正交矩阵

$$
R_\pm(u)=
\begin{pmatrix}
\sqrt{u/p}&\pm\sqrt{(p-u)/p}\\
\mp\sqrt{(p-u)/p}&\sqrt{u/p}
\end{pmatrix}
$$

取得。由于根号项非负，$v_-(u)\le v_+(u)$；又因为它们是范数平方为 $q$ 的向量经酉变换后的一个坐标强度，所以两者均在 $[0,q]$ 中。把 $R_\pm(u)$ 与前述共同实基变换复合，就得到作用于原始实候选对的合法实控制。还原 $\phi$ 的整体符号不会改变强度，输出向量仍然为实。

若 $q=0$、$k=0$、$k=pq$，或 $u$ 为区间端点，上式中相应交叉项为零，闭区间退化成单点，公式直接适用。若 $p=0$，则 $u=k=0$，可行切片为 $[0,q]$，实旋转同样能够把实向量 $\phi$ 的第零坐标强度取成 $0$ 或 $q$。

现在固定第一步参数 $\beta\in[0,1]$ 和 $u$，记

$$
\begin{aligned}
\mathsf p_0&=(1-\beta)u+\beta(p-u),
&c_0&=(1-\beta)u,\\
\mathsf p_1&=(1-\beta)(p-u)+\beta u,
&c_1&=(1-\beta)(p-u).
\end{aligned}
$$

这些量不随 $v$ 变化，并满足

$$
\mathsf p_0-c_0=\beta(p-u)\ge0,
\qquad
\mathsf p_1-c_1=\beta u\ge0.
$$

该 $u$ 上的 Bellman 目标为

$$
F_u(v)=V_{\boldsymbol\gamma}(\mathsf p_0,v,c_0v)
+V_{\boldsymbol\gamma}(\mathsf p_1,q-v,c_1(q-v)).
$$

已经证明的权重方向凸性分别用于 $c_0\le \mathsf p_0$ 和 $c_1\le \mathsf p_1$；第二项再与仿射映射 $v\mapsto q-v$ 复合，仍然凸。因此 $F_u$ 在 $[0,q]$ 上凸。任意可行 $v$ 都满足

$$
F_u(v)\le
\max\{F_u(v_-(u)),F_u(v_+(u))\}.
$$

区间非退化时，这是把 $v$ 写成两端点凸组合后的凸性不等式；区间退化时直接相等。故在保持同一个实际强度 $u$ 的条件下，可以用一个实可达端点代替复内部点，并且不降低最优延续代价。结合定理 19.2 的完整递推，即得所陈述的一维双符号递推。最大值由该定理的连续性和 $[0,p]\times\{-,+\}$ 的紧性达到。

最后对剩余长度归纳，证明整个最优控制表可以为实。空尾列代价为 $|p-q|$，无需控制。若 $p=0$，实际所有分支权重为零，任意控制表的代价都是理想总权重 $q$；同理 $q=0$ 时恒为 $p$。这也证明所列零权重边界。

对非零实际候选，取一个达到 Bellman 最大值的第一步 $(u,v)$，用上述不减值端点替换后，它仍然达到完整最大值。用实共同控制实现该端点；由于实际 $K_{\beta,z}$ 与理想 $P_z$ 都是实矩阵，两种结果后的候选对仍然为实。在每个已存结果分支，归纳假设给出达到完整复控制延续值的实尾表。两个尾表可以按不同的已存结果分别指定，与第一步组合后就成为全实最优反馈表。

该选择只使用固定候选模型、参数及已存历史，两实验始终调用同一张表。证明没有进行分支归一化，也没有除以 $\beta$ 或 $1-\beta$，因此零子分支和 $\beta=0,1$ 均被覆盖。取共同实初态 $|0\rangle$，再用定理 19.2 的 $T_N=V_{\boldsymbol\beta}(1,1,1)/2$，得到原始任务的实达到结论。证毕。

**定理 20.2（最终量子输出的显式访问差距与等号分类）。** 在定义 18.1 的同一无量子记忆、无输入输出参考的控制类中，固定 $N\ge1$ 和 $\beta_t\in[0,1]$，令

$$
f=\beta_N,
\qquad
s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad
E=1-s^2,
$$

其中空积为一。再定义

$$
U(E,f)=\frac{f+\sqrt{f^2+4(1-f)E}}2,
\qquad
\delta_N=\sqrt{1-(1-f)s^2}.
$$

若最终保留全部历史和活动量子比特 $H_N\otimes S$，则最优输出迹距离为 $\delta_N$：上界由定理 16.3 给出，定理 17.2 用实反馈和无参考的共同输入达到。若最终丢弃活动系统，只比较经典历史，则有统一上界

$$
T_N(\beta_1,\ldots,\beta_N)\le U(E,f).
$$

若所有 $\beta_t<1$ 且末次 $0<f<1$，则 $s>0$，并且

$$
T_N\le U(E,f)<\delta_N,
\qquad
\delta_N-T_N
\ge\frac{f(1-f)s^2}{2(2-f)}>0.
$$

在完整参数域上，两个观察任务最优值相等的条件恰为

$$
T_N(\beta_1,\ldots,\beta_N)=\delta_N
\quad\Longleftrightarrow\quad
\bigl[\beta_N=0\ \text{或存在 }t\le N\text{ 使 }\beta_t=1\bigr].
$$

证明。 固定共同历史控制表。经典总变差是共同输入密度矩阵的凸函数，所以证明输入无关的上界时纯输入足够。取共同单位初态，在末次控制之前，对长度为 $N-1$ 的旧历史 $h$，记实际与理想的未归一化分支向量为 $\psi_h,\phi_h$。

第 $t$ 次实际与理想结果算子满足

$$
\sum_{z=0}^1P_zK_{\beta_t,z}
=\sqrt{1-\beta_t}\,I_2.
$$

因此，设该节点调用的共同控制为 $W_h$，便有

$$
\sum_z
\langle P_zW_h\phi_h,K_{\beta_t,z}W_h\psi_h\rangle
=\sqrt{1-\beta_t}\langle\phi_h,\psi_h\rangle.
$$

从共同初态的内积一开始，逐层对所有历史求和，得到

$$
\sum_{|h|=N-1}\langle\phi_h,\psi_h\rangle=s.
$$

这只约束全部历史上的内积之和，不要求每个分支内积单独为实或非负。$N=1$ 时只有空历史，该等式就是初态内积一。

对最后共同控制 $W_h$，定义两种候选前缀若都接受完美指针读取时的经典分布

$$
P(h,z)=|\langle z|W_h\psi_h\rangle|^2,
\qquad
Q(h,z)=|\langle z|W_h\phi_h\rangle|^2.
$$

这里 $P$ 是用于比较的分布，未声称该完美读取已经在实际过程中执行；$Q$ 则恰好是理想全历史分布。两者总质量均为一。它们的 Bhattacharyya 重叠满足

$$
\begin{aligned}
B(P,Q)
&:=\sum_{h,z}\sqrt{P(h,z)Q(h,z)}\\
&\ge\left|\sum_{h,z}
\overline{\langle z|W_h\phi_h\rangle}
\langle z|W_h\psi_h\rangle\right|\\
&=\left|\sum_h\langle\phi_h,\psi_h\rangle\right|=s.
\end{aligned}
$$

实际末次仪器的结果效应为

$$
K_{f,z}^\dagger K_{f,z}
=(1-f)P_z+fP_{1-z}.
$$

所以实际全历史分布 $R$ 精确满足

$$
R(h,z)=(1-f)P(h,z)+fP(h,1-z).
$$

令 $\tau(h,z)=(h,1-z)$，则对任意经典事件 $A$，

$$
\begin{aligned}
R(A)-Q(A)
&=(1-f)P(A)+fP(\tau(A))-Q(A)\\
&\le f+(1-f)P(A)-Q(A).
\end{aligned}
$$

记 $a=1-f$。向量 $aP-Q$ 的元素之和为 $-f$，故其正部之和为

$$
\max_A\bigl[aP(A)-Q(A)\bigr]
=\frac{\|aP-Q\|_1-f}{2}.
$$

概率分布的总变差等于正事件差的最大值，因此

$$
\operatorname{TV}(R,Q)
\le\frac{f+\|aP-Q\|_1}{2}.
$$

对每个坐标分解平方差，再用 Cauchy--Schwarz 不等式，得到

$$
\begin{aligned}
\|aP-Q\|_1
&=\sum_{h,z}
\left|\sqrt{aP(h,z)}-\sqrt{Q(h,z)}\right|
\left(\sqrt{aP(h,z)}+\sqrt{Q(h,z)}\right)\\
&\le\sqrt{\bigl(a+1-2\sqrt a\,B(P,Q)\bigr)
\bigl(a+1+2\sqrt a\,B(P,Q)\bigr)}\\
&=\sqrt{(a+1)^2-4aB(P,Q)^2}\\
&\le\sqrt{(2-f)^2-4(1-f)s^2}\\
&=\sqrt{f^2+4(1-f)E}.
\end{aligned}
$$

于是每个固定策略和纯输入的代价都不超过 $U(E,f)$。对混合输入用同一策略下的凸性，再对全部共同策略取上确界，得到 $T_N\le U(E,f)$。推导使用完整 $U(2)$ 控制表，因此该界不依赖先将控制限制为实。

现设 $s>0$ 且 $0<f<1$，简记 $U=U(E,f)$。它满足二次等式

$$
U^2-fU=(1-f)(1-s^2).
$$

由于 $s>0$，定义中的根式严格小于 $2-f$，所以 $0<U<1$。直接相减得到

$$
\delta_N^2-U^2=f(1-U)>0,
$$

因而 $U<\delta_N$。进一步，由同一个二次等式可得

$$
(1-U)(1+U-f)=(1-f)s^2,
$$

于是

$$
\begin{aligned}
\delta_N-U
&=\frac{f(1-f)s^2}
{(\delta_N+U)(1+U-f)}\\
&\ge\frac{f(1-f)s^2}{2(2-f)}>0.
\end{aligned}
$$

这里两个分母因子均正，并且 $\delta_N,U\le1$。结合 $T_N\le U$，即得所述统一正差距。

还需确定其余参数边界。若末次 $f=0$，则 $U(E,0)=\sqrt E=\delta_N$，命题 18.3 的最终完美读取构造达到这一值，故 $T_N=\delta_N$。

若存在某个 $\beta_t=1$，则 $\delta_N=1$。取指针初态 $|0\rangle$，并在每个历史节点都用恒等控制。因为所有结果算子在指针基中对角，实际非零分支向量始终沿 $|0\rangle$ 方向；理想历史恒为全零，而在所选阶段 $t$，实际结果必为一。因此两种全历史分布的支撑不交，经典总变差达到一。这也包括末次 $f=1$。

反过来，若末次参数不为零且没有参数等于一，则所有 $\beta_t<1$，同时 $0<f<1$，恰好属于已经证明的严格差距条件。因此其最优值不相等。参数域已被这几种情况穷尽，得到所陈述的充要分类。

当 $N=1$ 时，$s=1$、$E=0$，上界给出 $U(0,f)=f$，由指针初态达到，因而一次经典结果的最优差异为 $f$；保留最终量子输出时则为 $\sqrt f$。一般有限步中，$E$ 只用于本定理的统一上界，没有取代第 19 章的分支三参数递推；命题 19.3 所排除的累计标量替代仍然不成立。证毕。

## 追加锚（新终端）

## 21. 惰性参考对两步经典历史辨识的严格增益

**定义 21.1（仅在输入和最终观察时使用的参考）。** 沿用定义 18.1 的二标签记录仪器与共同系统控制表，但允许初始活动系统 $S=\mathbb C^2$ 与一个有限维参考系统 $R$ 处于联合态 $\omega_{SR}$。每个过程内控制只作用于 $S$，只依赖已经存储的经典历史，实际与理想过程始终使用同一个表。所有记录单元新鲜准备，量子记录余系统读取后不再耦合，不后选择；没有另一个可访问辅助量子记忆，也不在过程内对 $R$ 施加操作或与它耦合。

经过 $N$ 步后丢弃活动系统 $S$，保留完整经典历史 $H_N$ 和惰性参考 $R$，允许最终联合测量 $H_N R$。对固定控制表 $U$，记从初始系统到经典历史的两个通道为

$$
\mathcal C_{\mathrm{actual},N}^U,
\qquad
\mathcal C_{\mathrm{ideal},N}^U:
\mathcal L(S)\longrightarrow\mathcal L(H_N).
$$

定义该访问范围中的最优差异为

$$
\begin{aligned}
T_N^{\mathrm{ref}}(\boldsymbol\beta)
&=\sup_{U,R,\omega_{SR}}
\frac12\left\|
\left[
\bigl(\mathcal C_{\mathrm{actual},N}^U
-\mathcal C_{\mathrm{ideal},N}^U\bigr)
\otimes\operatorname{id}_R
\right](\omega_{SR})
\right\|_1\\
&=\sup_U\frac12\left\|
\mathcal C_{\mathrm{actual},N}^U
-\mathcal C_{\mathrm{ideal},N}^U
\right\|_\diamond.
\end{aligned}
$$

输入上确界取两实验共同使用的归一化联合密度矩阵，参考维数可以是任意有限值。第二行是通道辨识中允许输入参考的半 diamond 距离。取平凡参考即可恢复定义 18.1 的观察类，因此 $T_N\le T_N^{\mathrm{ref}}$；下条给出该包含关系导致严格差异的两步见证。

**命题 21.2（一个惰性参考量子比特的显式两步优势）。** 取

$$
e=\beta_1=\frac12,
\qquad
f=\beta_2=\frac15.
$$

在定义 21.1 的任务中，使用一个参考量子比特，准备共同初态

$$
|\Psi\rangle_{SR}
=\frac12|00\rangle+\frac{\sqrt3}{2}|11\rangle,
\qquad
\rho_S=\operatorname{diag}\left(\frac14,\frac34\right),
$$

其中第一个张量因子是活动系统。第一共同控制取恒等；第一结果为 $i$ 时，第二共同系统控制取

$$
U_{2,0}=H
=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},
\qquad
U_{2,1}=X
=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

该策略在最终 $H_2R$ 输出上达到

$$
\frac{13+\sqrt{127}}{40}.
$$

因而

$$
T_2^{\mathrm{ref}}(1/2,1/5)
\ge\frac{13+\sqrt{127}}{40}
>\frac35
=T_2(1/2,1/5).
$$

这是指定策略的可达下界，不宣称已经求出 $T_2^{\mathrm{ref}}$ 的精确最优值。所有系统控制都为实正交矩阵；参考从初始制备到最终测量之间始终接受恒等操作。

证明。 令 $P_j=|j\rangle\langle j|$。由于 $e=1/2$，实际第一步的两个 Kraus 算子均为 $I_2/\sqrt2$，理想第一步算子则为 $P_i$。在 $f=1/5$ 时，实际末次结果效应为

$$
K_{2,j}^\dagger K_{2,j}
=\frac45P_j+\frac15P_{1-j}.
$$

因此对历史 $ij$，实际与理想的初始系统效应分别为

$$
E_{ij}^{\mathrm{actual}}
=\frac12U_{2,i}^\dagger
\left(\frac45P_j+\frac15P_{1-j}\right)U_{2,i},
$$

$$
E_{ij}^{\mathrm{ideal}}
=P_iU_{2,i}^\dagger P_jU_{2,i}P_i.
$$

记 $M_{ij}=E_{ij}^{\mathrm{actual}}-E_{ij}^{\mathrm{ideal}}$，代入 $H$ 和 $X$ 得到

$$
M_{00}=\frac1{20}\begin{pmatrix}-5&3\\3&5\end{pmatrix},
\qquad
M_{01}=\frac1{20}\begin{pmatrix}-5&-3\\-3&5\end{pmatrix},
$$

$$
M_{10}=\operatorname{diag}\left(\frac1{10},-\frac35\right),
\qquad
M_{11}=\operatorname{diag}\left(\frac25,\frac1{10}\right).
$$

例如，$H^\dagger P_0H$ 的每个矩阵元均为 $1/2$，而 $P_0H^\dagger P_0HP_0=P_0/2$，所以相减后得到 $M_{00}$。其余三式使用互补投影及 $X^\dagger P_0X=P_1$。四个差效应之和为零，与两种历史分布均归一化一致。

对所选 Schmidt 初态，系统效应 $E$ 对应的未归一化参考输出为

$$
\sqrt{\rho_S}\,E^{\mathsf T}\sqrt{\rho_S}.
$$

这是因为该参考矩阵的 $(a,b)$ 元为

$$
\sqrt{(\rho_S)_{aa}(\rho_S)_{bb}}\,
\langle b|E|a\rangle,
$$

可由初态在 $|a\rangle_S|a\rangle_R$ 基中的展开直接求出。因此两个最终 $H_2R$ 输出之差是按历史分块的 Hermitian 算子

$$
\Delta_{H_2R}
=\sum_{i,j}|ij\rangle\langle ij|\otimes D_{ij},
\qquad
D_{ij}=\sqrt{\rho_S}\,M_{ij}^{\mathsf T}\sqrt{\rho_S}.
$$

使用 $\sqrt{\rho_S}=\operatorname{diag}(1/2,\sqrt3/2)$，四个参考差块明确为

$$
D_{00}=\frac1{80}\begin{pmatrix}-5&3\sqrt3\\3\sqrt3&15\end{pmatrix},
\qquad
D_{01}=\frac1{80}\begin{pmatrix}-5&-3\sqrt3\\-3\sqrt3&15\end{pmatrix},
$$

$$
D_{10}=\operatorname{diag}\left(\frac1{40},-\frac9{20}\right),
\qquad
D_{11}=\operatorname{diag}\left(\frac1{10},\frac3{40}\right).
$$

前两个矩阵的迹均为 $1/8$，行列式均为 $-51/3200$，所以两个特征值异号。各自的迹范数等于特征值间距：

$$
\|D_{00}\|_1=\|D_{01}\|_1
=\sqrt{\frac1{64}+\frac{204}{3200}}
=\frac{\sqrt{127}}{40}.
$$

另外两个对角块给出

$$
\|D_{10}\|_1=\frac{19}{40},
\qquad
\|D_{11}\|_1=\frac7{40}.
$$

由于不同经典历史对应正交块，整体迹范数是各块迹范数之和，故

$$
\frac12\|\Delta_{H_2R}\|_1
=\frac12\sum_{i,j}\|D_{ij}\|_1
=\frac{13+\sqrt{127}}{40}.
$$

最终观察者可以先读取历史 $ij$，再在参考上测量对应 $D_{ij}$ 的正负谱子空间，以达到该可区分性。该测量只发生在两个记录步骤之后，没有对参考施加过程内控制，也没有丢弃任何历史。

另一方面，定理 18.2 已经优化全部无参考输入和共同系统控制，给出

$$
T_2(1/2,1/5)
=\max\left\{\frac35,\sqrt{\frac{17}{50}}\right\}
=\frac35,
$$

其中 $9/25=18/50>17/50$。所构造参考策略相对此完整无参考最优值的增量为

$$
\frac{13+\sqrt{127}}{40}-\frac35
=\frac{\sqrt{127}-11}{40}>0,
$$

严格不等式由 $127>121$ 得到。这证明了被动保留的初始纠缠参考可以提高该两步任务的最优值。证毕。

## 追加锚（新终端）

## 22. 一个可操作记忆比特的精确最优值与经典达到边界

**定义 22.1（丢弃活动系统而保留可操作记忆）。** 沿用定义 17.1 的二结果仪器族。活动系统 $S=\mathbb C^2$，参数 $\beta_t\in[0,1]$，实际与理想结果算子分别为

$$
K_{t,z}=\sqrt{1-\beta_t}\,P_z+\sqrt{\beta_t}\,P_{1-z},
\qquad P_z=|z\rangle\langle z|,
\qquad z\in\{0,1\}.
$$

允许一个任意非零有限维可操作量子记忆 $M$。每次仪器之前，可以根据全部已存经典历史，在 $S\otimes M$ 上调用预先指定的共同 CPTP 控制；实际和理想实验调用同一张控制表。仪器只作用于 $S$，每次读取的经典结果追加到 $H_t$，旧历史保持不变。已丢弃的控制余系统或仪器余系统不再耦合，无后选择。末次仪器之后丢弃 $S$，输出为 $H_N\otimes M$。

固定 $M$ 和共同控制表 $\Pi$ 后，这定义实际与理想通道

$$
\mathcal C_{{\rm A},N}^{\Pi},\mathcal C_{{\rm J},N}^{\Pi}:
\mathcal L(S\otimes M)\longrightarrow\mathcal L(H_N\otimes M).
$$

记无参考共同输入的最优输出差异为

$$
T_N^{\rm mem}(\boldsymbol\beta)
=\sup_{\substack{1\le\dim M<\infty,\,\Pi\\
\rho\ge0,\,\operatorname{tr}\rho=1}}
\frac12\left\|
\mathcal C_{{\rm A},N}^{\Pi}(\rho)
-\mathcal C_{{\rm J},N}^{\Pi}(\rho)
\right\|_1.
$$

输入 $\rho$ 位于 $S\otimes M$。对固定通道还可以使用惰性参考 $R$ 定义 diamond 距离，此时控制不作用于 $R$，最终同时保留 $R$。$M$ 允许与活动系统耦合；这一访问权限不同于仅保留一个始终不可操作的参考系统。

**定理 22.2（精确记忆最优值及一次 SWAP 的达到）。** 对定义 22.1 的任意有限 $N\ge1$ 和完整参数域 $\beta_t\in[0,1]$，令

$$
f=\beta_N,\qquad a=1-f,\qquad
s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},\qquad E=1-s^2,
$$

其中空积为一。使用第 20.2 条的函数

$$
U(E,f)=\frac{f+\sqrt{f^2+4(1-f)E}}2
=\frac{f+\sqrt{(a+1)^2-4as^2}}2,
$$

有

$$
T_N^{\rm mem}(\boldsymbol\beta)=U(E,f).
$$

更强地，每个固定有限维记忆及共同控制表都满足

$$
\frac12\left\|
\mathcal C_{{\rm A},N}^{\Pi}
-\mathcal C_{{\rm J},N}^{\Pi}
\right\|_\diamond\le U(E,f).
$$

一个初态为 $|0\rangle$ 的记忆量子比特即可达到等号：前 $N-1$ 步完全不操作记忆，只在活动比特上执行共同实反馈；末次仪器前把 $S$ 与 $M$ 作一次 SWAP。达到使用共同输入 $|0\rangle_S|0\rangle_M$，无需惰性参考。该结论给出此仪器族及保留输出的精确最优值，不断言每个参数选择都比无记忆经典历史任务更优。

证明。先证明对任意记忆和参考一致的上界。给共同输入作纯化，并给实际、理想实验中的共同 CPTP 控制使用同一个 Stinespring 等距。每次仪器使用结果标签及其丢弃副本，实际、理想两种等距的交叉算子为

$$
\sum_zP_zK_{t,z}=\sqrt{1-\beta_t}\,I_S.
$$

共同历史控制保持完整纯化的内积，每次仪器则将其乘以所示标量。经过前 $N-1$ 次仪器及末次共同控制后，全部保留与纯化寄存器上的两个单位向量可以取为 $|A\rangle,|J\rangle$，满足

$$
\langle J|A\rangle=s.
$$

纯化中保留的丢弃寄存器只用于分析，不允许重新接回协议；惰性参考也始终不参与控制。

在两候选上都假设末次作完美指针读取并丢弃 $S$，得到归一化经典量子态 $\mathsf P,\mathsf Q$，其空间为 $H_N\otimes M\otimes R$。它们是 $|A\rangle,|J\rangle$ 经同一通道的输出，而 $\mathsf Q$ 正好是理想最终态。对 Hermitian 算子的迹范数收缩及秩一差值公式给出

$$
\begin{aligned}
\|a\mathsf P-\mathsf Q\|_1
&\le\|a|A\rangle\langle A|-|J\rangle\langle J|\|_1\\
&=\sqrt{(a+1)^2-4a|\langle J|A\rangle|^2}\\
&=\sqrt{(a+1)^2-4as^2}.
\end{aligned}
$$

令 $\tau$ 只翻转最后一个经典结果位，保持旧历史、记忆和参考不动。对末次仪器前任意历史块 $\omega_h$，实际结果 $z$ 的记忆参考块为

$$
\begin{aligned}
&\operatorname{Tr}_S\bigl[
(K_{N,z}\otimes I)\omega_h(K_{N,z}\otimes I)
\bigr]\\
&\qquad=a\langle z|\omega_h|z\rangle
+f\langle1-z|\omega_h|1-z\rangle.
\end{aligned}
$$

两指针之间的交叉项在部分迹后为零，故实际最终态严格满足

$$
\mathsf R=a\mathsf P+f\tau(\mathsf P).
$$

因为 $\tau(\mathsf P)$ 是迹范数为一的密度矩阵，

$$
\begin{aligned}
\frac12\|\mathsf R-\mathsf Q\|_1
&\le\frac12\bigl(\|a\mathsf P-\mathsf Q\|_1+f\bigr)\\
&\le U(E,f).
\end{aligned}
$$

这对任意共同输入及参考一致，因而也是所述半 diamond 上界。

为构造达到，把定理 17.2 的零对角递推用于不等初始权重。前缀中不操作记忆，实际与理想物理分支向量记为 $x_h,y_h$，初态均为 $|0\rangle$。只在控制表计算中引入

$$
\psi_h=\sqrt a\,x_h,\qquad\phi_h=y_h,
$$

并定义

$$
\begin{aligned}
p_h&=\|\psi_h\|^2,&q_h&=\|\phi_h\|^2,
&c_h&=\phi_h^{\mathsf T}\psi_h,\\
r_k&=\frac{2\sqrt a}{a+1}
\prod_{t=1}^k\sqrt{1-\beta_t}.
\end{aligned}
$$

逐层构造共同实控制，使每个深度 $k$ 的历史满足

$$
2c_h=r_k(p_h+q_h).
$$

初始 $p=a,q=1,c=\sqrt a$，故关系成立。分母 $a+1$ 总为正，而且 $0\le r_k\le1$。

固定一个深度 $t-1$ 的节点，暂略历史下标，写 $\alpha=\sqrt{1-\beta_t}$、$b=\sqrt{\beta_t}$、$r=r_{t-1}$。定义实对称矩阵

$$
X=\psi\phi^{\mathsf T}+\phi\psi^{\mathsf T}
-r\bigl[(\alpha^2-b^2)\psi\psi^{\mathsf T}
+\phi\phi^{\mathsf T}\bigr]-rb^2pI_2.
$$

由归纳关系及 $\alpha^2+b^2=1$，

$$
\operatorname{tr}X
=2c-r[(\alpha^2-b^2)p+q]-2rb^2p
=2c-r(p+q)=0.
$$

按定理 17.2 的实对称谱基构造，取正交归一的 $v_0,v_1$ 使 $v_z^{\mathsf T}Xv_z=0$，并以 $v_z^{\mathsf T}$ 为共同控制矩阵的第 $z$ 行。$X=0$ 时任取实正交基。令 $u_z=v_z^{\mathsf T}\psi$、$w_z=v_z^{\mathsf T}\phi$，子分支满足

$$
p_{hz}=b^2p+(\alpha^2-b^2)u_z^2,
\qquad q_{hz}=w_z^2,
\qquad c_{hz}=\alpha u_zw_z.
$$

零对角关系等价于 $2u_zw_z=r(p_{hz}+q_{hz})$，两边乘以 $\alpha$ 即得

$$
2c_{hz}=r_t(p_{hz}+q_{hz}).
$$

这个递推没有除以 $a,\alpha,b,p,q$，所以零向量、零概率历史及 $\beta_t=0,1$ 都包括在内。$a=0$ 时加权实际向量全为零，但物理实际向量仍按同一个控制表定义；加权只用于选择控制，不要求从零向量反演物理分支。仪器完备性给出每层总权重 $\sum_hp_h=a$、$\sum_hq_h=1$。

令 $\rho_A,\rho_J$ 是前 $N-1$ 步的历史加活动系统输出。逐历史使用秩一差值公式，得到

$$
\begin{aligned}
\|a\rho_A-\rho_J\|_1
&=\sum_{|h|=N-1}\sqrt{(p_h+q_h)^2-4c_h^2}\\
&=\sum_{|h|=N-1}(p_h+q_h)\sqrt{1-r_{N-1}^2}\\
&=\sqrt{(a+1)^2-4as^2}.
\end{aligned}
$$

最后把活动比特与尚未参与、初态为 $|0\rangle$ 的记忆比特 $M$ 作 SWAP。前缀候选量子态进入记忆，两实验中的活动系统都成为 $|0\rangle$。末次实际结果零、一的概率为 $a,f$，理想结果恒为零。识别 SWAP 前后的比特空间，最终输出差关于末次经典结果的两个直和块恰为

$$
(a\rho_A-\rho_J)\ \oplus\ f\rho_A.
$$

所以最终迹距离为

$$
\frac12\bigl(\|a\rho_A-\rho_J\|_1+f\bigr)=U(E,f).
$$

无参考纯输入已达到参考一致上界，故该固定控制表的半 diamond 距离也达到同一值。$N=1$ 时前缀为空，结果为 $f$；$f=0$ 时为 $\sqrt{1-s^2}$；$f=1$ 或某个前缀参数为一时为一。有限反馈表按模型参数与已存历史预先计算，两实验始终使用同一表。证毕。

**定理 22.3（无记忆经典历史的等号分类）。** 令 $T_N$ 仍表示定义 18.1 的原始任务：单活动量子比特、全部共同历史依赖 $U(2)$ 控制、无可操作记忆、无输入参考，末端只保留经典历史。对完整参数域 $\beta_t\in[0,1]$，$N=1$ 时总有

$$
T_1=U(0,f)=f.
$$

对 $N\ge2$，有充要分类

$$
T_N=U(E,f)
\quad\Longleftrightarrow\quad
\left[
\beta_{N-1}=0\ \text{或}\ \beta_N=0
\ \text{或存在 }t\le N\text{ 使 }\beta_t=1
\right].
$$

因此，若 $N\ge2$、$0<\beta_N<1$、所有 $\beta_t<1$ 且 $\beta_{N-1}>0$，则

$$
T_N<U(E,f)=T_N^{\rm mem}.
$$

这里比较的是两个控制与访问任务各自优化后的值。严格情形中一个可操作记忆比特足以取得增益；所列等号边界则无需该记忆。该分类不确定只允许惰性参考而禁止系统参考耦合的最优值。

证明。第 20.2 条给出 $T_N\le U(E,f)$。$N=1$ 时，指针初态达到 $f=U(0,f)$。若 $f=0$，命题 18.3 的最终完美读取达到 $\sqrt E=U(E,0)$。若某个 $\beta_t=1$，取指针初态和恒等控制，实际与理想历史支撑不交，达到 $1=U(E,f)$。

设 $N\ge2$ 且 $\beta_{N-1}=0$。对前 $N-2$ 步使用定理 22.2 证明中的加权实反馈，得到历史加活动系统态 $\rho_A,\rho_J$，满足

$$
\|a\rho_A-\rho_J\|_1
=\sqrt{(a+1)^2-4as^2}.
$$

倒数第二步参数为零，所以 $s$ 与前 $N-2$ 步的重叠乘积相同。对每个长度 $N-2$ 的历史 $g$，将 Hermitian 块

$$
D_g=a|x_g\rangle\langle x_g|-|y_g\rangle\langle y_g|
$$

的特征基通过共同系统酉送入指针基，随后作倒数第二次完美读取。若该步后的两种经典分布为 $p_h,q_h$，逐块读取特征值给出

$$
\sum_h|ap_h-q_h|=\|a\rho_A-\rho_J\|_1.
$$

读取结果 $y$ 后，两实验中非零系统分支都沿已知指针 $|y\rangle$。按该经典结果使用 $X^y$ 把它送到 $|0\rangle$，其中 $X|0\rangle=|1\rangle$、$X|1\rangle=|0\rangle$。再执行末次仪器，末次结果零、一上的实际分布分别为 $ap_h,fp_h$，理想分布为 $q_h,0$，故

$$
\operatorname{TV}
=\frac12\sum_h\bigl(|ap_h-q_h|+fp_h\bigr)
=U(E,f).
$$

该方案完全不使用量子记忆，零概率历史任意指定控制。$N=2$ 时前缀为空，上述构造仍成立。

剩下证明必要性。设 $N\ge2$、$0<f<1$、所有参数小于一且 $\beta_{N-1}>0$。于是 $a>0$、$s>0$，并有 $0<\beta_{N-1}<1$。若 $T_N=U(E,f)$，由定理 19.2 的纯输入归约和有限控制树紧性，存在纯初态及共同控制表真正达到此值。

固定该策略，在末次控制前，对每个长度 $N-1$ 的历史 $h$ 记未归一化候选向量为 $x_h,y_h$，末次控制为 $W_h$。定义

$$
P(h,z)=|\langle z|W_hx_h\rangle|^2,
\qquad
Q(h,z)=|\langle z|W_hy_h\rangle|^2.
$$

实际最终分布是 $R=aP+f\tau P$，其中 $\tau$ 翻转末次结果。第 20.2 条的内积递推与三角不等式给出

$$
\sum_h\langle y_h,x_h\rangle=s,
\qquad
B(P,Q):=\sum_{h,z}\sqrt{P(h,z)Q(h,z)}\ge s.
$$

上界可以写为

$$
\begin{aligned}
2\operatorname{TV}(R,Q)
&=\|aP-Q+f\tau P\|_1\\
&\le\|aP-Q\|_1+f\\
&\le\sqrt{(a+1)^2-4aB(P,Q)^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

达到最终界强制每一步等号。因为 $a,s>0$，最后一步等号强制 $B(P,Q)=s$。

考察加权 Cauchy--Schwarz 步骤。对坐标 $i=(h,z)$，令

$$
u_i=|\sqrt{aP_i}-\sqrt{Q_i}|,
\qquad v_i=\sqrt{aP_i}+\sqrt{Q_i}.
$$

等号要求存在 $\lambda\ge0$ 使所有坐标满足 $u_i=\lambda v_i$，其中

$$
\lambda^2
=\frac{a+1-2\sqrt a\,B(P,Q)}
{a+1+2\sqrt a\,B(P,Q)}<1.
$$

分母正，而 $a>0$、$B(P,Q)=s>0$。若某坐标 $P_i,Q_i$ 恰有一个为零，则 $u_i=v_i>0$，与 $\lambda<1$ 矛盾。因此 $P,Q$ 逐坐标具有相同支撑。

因为 $\sum_i(aP_i-Q_i)=-f<0$，存在负坐标 $(h,z)$，使 $d_i=aP_i-Q_i<0$。第一个迹范数三角等号逐坐标要求

$$
P(h,1-z)=0.
$$

否则负数 $d_i$ 与严格正的 $fP(h,1-z)$ 相加会使三角不等式严格。由相同支撑，$Q(h,1-z)=0$；该负坐标自身则有 $P(h,z),Q(h,z)>0$。所以末次控制后的两候选向量都是同一指针 $|z\rangle$ 的非零倍数，控制前的 $x_h,y_h$ 也非零且共线。

写 $h=g\ell$，其中 $\ell$ 为倒数第二次结果。令倒数第二次控制后的父候选为

$$
\xi=U_{N-1,g}x_g,
\qquad \eta=U_{N-1,g}y_g,
$$

并记 $\alpha=\sqrt{1-\beta_{N-1}}>0$、$b=\sqrt{\beta_{N-1}}>0$。于是

$$
x_{g\ell}=(\alpha P_\ell+bP_{1-\ell})\xi,
\qquad y_{g\ell}=P_\ell\eta.
$$

$y_{g\ell}$ 非零并沿 $|\ell\rangle$，共线性强制实际向量也沿该指针。由于 $\alpha,b>0$，这迫使 $\xi$ 非零并沿 $|\ell\rangle$。因此兄弟历史 $h'=g(1-\ell)$ 的实际向量

$$
x_{h'}=(\alpha P_{1-\ell}+bP_\ell)\xi=b\xi
$$

非零且沿 $|\ell\rangle$。如果理想向量 $y_{h'}=P_{1-\ell}\eta$ 为零，该历史下 $Q$ 的两个末次坐标都为零，而 $P$ 至少一个为正，违反相同支撑。故 $y_{h'}$ 非零并沿 $|1-\ell\rangle$，从而

$$
\langle y_{h'},x_{h'}\rangle=0.
$$

但相同支撑和非零分支权重又强制

$$
B_{h'}:=\sum_z\sqrt{P(h',z)Q(h',z)}>0.
$$

对每个历史都有 $B_h\ge|\langle y_h,x_h\rangle|$，对 $h'$ 严格。因此

$$
B(P,Q)=\sum_hB_h
>\sum_h|\langle y_h,x_h\rangle|
\ge\left|\sum_h\langle y_h,x_h\rangle\right|=s,
$$

与等号所需 $B(P,Q)=s$ 矛盾。没有策略达到 $U(E,f)$，而原任务的最优值确实达到，所以 $T_N<U(E,f)$。参数域已经穷尽，得到所述分类。证毕。

## 追加锚（新终端）

## 23. 惰性参考的实参数归约与记忆权限分离

**定理 23.1（两步惰性参考任务的有限实参数最大值）。** 在定义 21.1 的两步任务中，令 $e=\beta_1,f=\beta_2\in[0,1]$。任意有限参考维数、共同混合输入及复系统酉控制的上确界，可以由一个参考量子比特、实系数纯输入、第一控制恒等及两个实正交末次控制达到。

更明确地，定义紧参数域

$$
\mathcal D_{\mathbb R}^+
=\left\{
\rho(t,w)=\begin{pmatrix}t&w\\w&1-t\end{pmatrix}:
0\le t\le1,\quad 0\le w\le\sqrt{t(1-t)}
\right\}.
$$

记第一步的实际 Kraus 算子为

$$
K_i=\sqrt{1-e}\,P_i+\sqrt e\,P_{1-i},
\qquad i\in\{0,1\}.
$$

对每个第一结果 $i$，独立取 $u_i\in[0,1]$ 及 $\eta_i\in\{-1,1\}$，并定义互补实秩一投影

$$
Q_{i0}=
\begin{pmatrix}
u_i&\eta_i\sqrt{u_i(1-u_i)}\\
\eta_i\sqrt{u_i(1-u_i)}&1-u_i
\end{pmatrix},
\qquad Q_{i1}=I_2-Q_{i0}.
$$

两个实验对应的初始系统差效应为

$$
M_{ij}=K_i\bigl[fI_2+(1-2f)Q_{ij}\bigr]K_i-P_iQ_{ij}P_i.
$$

对二阶 Hermitian 矩阵 $M$ 和任意二阶密度矩阵 $\rho$，定义

$$
\mathfrak n_\rho(M)=
\begin{cases}
\sqrt{[\operatorname{tr}(\rho M)]^2-4\det(\rho)\det(M)},&\det(M)<0,\\
|\operatorname{tr}(\rho M)|,&\det(M)\ge0.
\end{cases}
$$

则精确最优值为

$$
T_2^{\mathrm{ref}}(e,f)
=\frac12
\max_{\substack{\rho\in\mathcal D_{\mathbb R}^+\\
u_0,u_1\in[0,1],\ \eta_0,\eta_1\in\{-1,1\}}}
\sum_{i,j=0}^1\mathfrak n_\rho(M_{ij}).
$$

该式仍是四个连续实参数及两个符号的有限最大化，并未把 $T_2^{\mathrm{ref}}$ 求成参数 $e,f$ 的显式函数。实控制充分性在本条仅针对两步、末端丢弃活动系统的参考任务；不将其外推到任意长度的参考反馈协议。

证明。固定控制表时，最终差算子的迹范数关于共同输入密度矩阵是凸函数。将任意混合输入分解成纯态，其中至少一个纯态分量的值不小于该混合输入。因此优化纯输入足够。活动系统为二维，每个纯输入的 Schmidt 秩不超过二；参考全程不被操作，其 Schmidt 支撑可等距压缩进 $\mathbb C^2$，且输出迹范数不变。秩一支撑补一个零坐标即可使用同一参考空间。

将第一共同酉吸收到自由选择的输入中，第一控制可取恒等。归一化两比特纯态的单位球面与两张末次酉矩阵的 $U(2)^2$ 均紧，输出迹范数连续，故任意有限参考的上确界已在这个有限参数空间达到。

令 $\rho$ 为纯输入的系统边缘态。具有相同 $\rho$ 的纯化之间只差参考上的等距，因而给出相同输出迹范数。可以选取规范纯化

$$
|\Psi_\rho\rangle
=\sum_{a,b=0}^1(\sqrt\rho)_{ab}|a\rangle_S|b\rangle_R.
$$

对初始系统效应 $E$，对应的参考输出为

$$
\bigl(\sqrt\rho\,E\sqrt\rho\bigr)^{\mathsf T}.
$$

这是从纯化系数求部分迹所得；转置保持迹范数。因此，对任意共同末次酉 $U_i$，令 $Q_{ij}=U_i^\dagger P_jU_i$，并按陈述定义 $M_{ij}$，最终差异为

$$
\frac12\sum_{i,j}
\left\|\sqrt\rho\,M_{ij}\sqrt\rho\right\|_1.
$$

该表达式仅依赖末次酉的两个互补测量效应。原因是末端已丢弃活动系统，参考块只取决于结果效应；末次系统向量的额外相位不再进入输出。

对任意二阶 Hermitian $M$，矩阵 $A=\sqrt\rho M\sqrt\rho$ 的迹和行列式分别是 $\operatorname{tr}(\rho M)$ 和 $\det(\rho)\det(M)$。若 $\det(M)<0$ 且 $\rho$ 满秩，$A$ 两特征值异号，迹范数为特征值间距，即 $\mathfrak n_\rho(M)$ 的第一式。若此时 $\rho$ 秩亏，$A$ 至多秩一，同一公式退为 $|\operatorname{tr}A|$。若 $\det(M)\ge0$，二阶 Hermitian 矩阵 $M$ 为半正定或半负定，合同变换保持这一性质，故迹范数为绝对迹。于是全部退化情形也满足

$$
\left\|\sqrt\rho\,M\sqrt\rho\right\|_1
=\mathfrak n_\rho(M).
$$

由于 $K_i$ 和 $P_i$ 都是对角矩阵，可以同时作

$$
\rho\longmapsto D\rho D^\dagger,
\qquad Q_{ij}\longmapsto DQ_{ij}D^\dagger,
$$

其中 $D$ 为任意对角酉。这时 $M_{ij}\mapsto DM_{ij}D^\dagger$，合同矩阵的迹范数不变。选择一个 $D$，可使系统边缘态的非对角元为非负实数；原非对角元为零时无需选择相位。因此可以限制 $\rho\in\mathcal D_{\mathbb R}^+$。

固定这样的 $\rho$，再固定第一结果 $i$ 及末次第零投影的对角元 $u$。其一般复形式为

$$
Q_{i0}(\phi)=
\begin{pmatrix}
u&\sqrt{u(1-u)}e^{-i\phi}\\
\sqrt{u(1-u)}e^{i\phi}&1-u
\end{pmatrix},
\qquad Q_{i1}(\phi)=I_2-Q_{i0}(\phi).
$$

当 $u=0$ 或 $u=1$ 时已经是实矩阵。对任意 $u\in[0,1]$，每个差效应 $M_{ij}(\phi)$ 的对角元都不依赖 $\phi$，非对角元则是一个固定实系数乘以 $e^{\pm i\phi}$。因此 $\det M_{ij}(\phi)$ 不随 $\phi$ 改变，而

$$
\operatorname{tr}\bigl(\rho M_{ij}(\phi)\bigr)
=A_{ij}+B_{ij}\cos\phi
$$

具有固定实系数 $A_{ij},B_{ij}$。

若该固定行列式为负，令 $c_{ij}=-4\det(\rho)\det(M_{ij})\ge0$，相应迹范数作为 $x=\cos\phi$ 的函数为

$$
\sqrt{(A_{ij}+B_{ij}x)^2+c_{ij}}.
$$

它是二维向量 $(A_{ij}+B_{ij}x,\sqrt{c_{ij}})$ 的 Euclidean 范数，故为凸函数。若行列式非负，迹范数为 $|A_{ij}+B_{ij}x|$，也为凸函数。因此固定 $i$ 的两个结果范数之和在 $[-1,1]$ 上为凸函数，至少一个端点 $x=1$ 或 $x=-1$ 的值不小于任何给定内部点。取 $\phi=0$ 或 $\phi=\pi$ 即可将该分支替换为实投影而不降低总目标。

两个第一结果的末次控制可以独立选择，所以对 $i=0,1$ 分别替换即可。陈述中的实投影由下面的实正交矩阵实现：

$$
U_i=
\begin{pmatrix}
\sqrt{u_i}&\eta_i\sqrt{1-u_i}\\
-\eta_i\sqrt{1-u_i}&\sqrt{u_i}
\end{pmatrix},
\qquad U_i^{\mathsf T}P_jU_i=Q_{ij}.
$$

实对称正半定 $\rho$ 的正平方根也为实矩阵，故所选规范纯化具有实系数。由此，每个复策略均有值不小于它的实参数策略。反方向，所列参数都定义合法输入与共同控制。两类上确界相同，而右侧紧参数域上的目标等于连续的迹范数之和，确有最大值。这证明了所述归约与精确有限最大化式。证毕。

**定理 23.2（惰性参考与可操作记忆的严格分离）。** 沿用定义 21.1 的惰性参考任务和定义 22.1 的可操作记忆任务。对任意 $0<e,f<1$，有

$$
T_2^{\mathrm{ref}}(e,f)
<T_2^{\mathrm{mem}}(e,f)
=U(e,f)
=\frac{f+\sqrt{f^2+4(1-f)e}}2.
$$

在完整参数域 $(e,f)\in[0,1]^2$ 上，两种最优值相等的条件恰为

$$
T_2^{\mathrm{ref}}(e,f)=T_2^{\mathrm{mem}}(e,f)
\quad\Longleftrightarrow\quad
\bigl[e\in\{0,1\}\ \text{或}\ f\in\{0,1\}\bigr].
$$

这是两个访问范围各自优化后的严格分离及等号分类，不给出内域 $T_2^{\mathrm{ref}}(e,f)$ 的精确公式，也不提供显式的正差距常数。

证明。 第 23.1 条已经将惰性参考优化归约到参考量子比特上的纯联合输入及紧的有限控制参数域，并证明最优值达到。第一共同系统酉可以吸收入自由选择的联合初态。下面的严格性论证允许任意复纯输入和两个末次共同酉 $U_0,U_1\in U(2)$，不另外假设控制或输入为实。

固定 $0<e,f<1$，记

$$
a=1-f,
\qquad \alpha=\sqrt{1-e}>0,
\qquad b=\sqrt e>0.
$$

若纯联合初态的系统边缘态秩为一，则该初态为乘积态。由于过程内不操作参考，参考在每个历史上保持同一个固定张量因子；最终迹距离等于一个合法无参考协议的经典总变差。定理 22.3 在 $\beta_1=e$、$\beta_2=f$ 均严格介于零和一之间时给出 $T_2(e,f)<U(e,f)$，故秩一初态不能达到可操作记忆的最优值。

剩下处理系统边缘态满秩的纯初态。写成

$$
|\Psi\rangle_{SR}
=|0\rangle\otimes x+|1\rangle\otimes y,
\qquad \|x\|^2+\|y\|^2=1,
$$

其中参考向量 $x,y\in\mathbb C^2$ 线性无关。令 $r_0=x$、$r_1=y$，以及 $q_i=\|r_i\|^2$，则 $0<q_i<1$。

实际第一步在结果 $i$ 上的算子是 $K_{1,i}=\alpha P_i+bP_{1-i}$，理想算子是 $P_i$。令实际首支向量为

$$
\xi_i=(K_{1,i}\otimes I_R)|\Psi\rangle
=\alpha|i\rangle\otimes r_i
+b|1-i\rangle\otimes r_{1-i},
\qquad
p_i=\|\xi_i\|^2=\alpha^2q_i+b^2(1-q_i).
$$

于是 $p_0+p_1=1$。在第一历史 $i$ 上、尚未执行最后控制时，加权实际与理想的 $SR$ 差块是

$$
Z_i=a|\xi_i\rangle\langle\xi_i|
-|i\rangle\langle i|\otimes|r_i\rangle\langle r_i|.
$$

理想未归一化向量 $|i\rangle\otimes r_i$ 与 $\xi_i$ 的内积为 $\alpha q_i$，所以秩一差值公式给出

$$
L_i:=\|Z_i\|_1
=\sqrt{(ap_i+q_i)^2-4a\alpha^2q_i^2}.
$$

实二维向量 $(L_i,2\sqrt a\,\alpha q_i)$ 的欧氏范数是 $ap_i+q_i$。对这两个向量使用三角不等式，有

$$
(L_0+L_1)^2+4a\alpha^2(q_0+q_1)^2
\le\bigl[a(p_0+p_1)+q_0+q_1\bigr]^2.
$$

代入两种总权重均为一及 $\alpha^2=1-e$，得到

$$
L_0+L_1\le\sqrt{(a+1)^2-4a(1-e)}.
$$

固定第一结果 $i$，在其末次控制 $U_i$ 之后定义两个参考向量

$$
v_j=(\langle j|U_i\otimes I_R)\xi_i,
\qquad j\in\{0,1\}.
$$

因为 $x,y$ 线性无关、$\alpha,b>0$ 且 $U_i$ 可逆，$v_0,v_1$ 也线性无关。逆酉关系给出

$$
\alpha r_i=\sum_{j=0}^1\overline{(U_i)_{ji}}\,v_j.
$$

分别改变 $v_j$ 的代表相位，不改变其秩一投影。可据此把上式写成

$$
r'_i:=\alpha r_i=c_0v_0+c_1v_1,
\qquad c_j=|(U_i)_{ji}|\ge0,
\qquad c_0^2+c_1^2=1.
$$

这只是向量代表的选择，不是对参考施加操作。在这些代表中，理想最终参考块为 $(c_j^2/\alpha^2)|r'_i\rangle\langle r'_i|$，实际最终参考块为

$$
a|v_j\rangle\langle v_j|
+f|v_{1-j}\rangle\langle v_{1-j}|.
$$

记

$$
B_{ij}=a|v_j\rangle\langle v_j|
-\frac{c_j^2}{\alpha^2}|r'_i\rangle\langle r'_i|,
\qquad
F_{ij}=B_{ij}+f|v_{1-j}\rangle\langle v_{1-j}|.
$$

$F_{ij}$ 正是最终历史 $ij$ 上的实际减理想参考差块。$B_{ij}$ 则由 $Z_i$ 经过共同末次系统酉、完美指针读取以及丢弃系统得到，故迹范数收缩给出

$$
\sum_j\|B_{ij}\|_1\le L_i.
$$

对实际末次噪声项使用三角不等式，得到

$$
\|F_{ij}\|_1
\le\|B_{ij}\|_1+f\|v_{1-j}\|^2.
$$

每个 $i$ 上都有 $\|v_0\|^2+\|v_1\|^2=p_i$，而 $p_0+p_1=1$，所以对全部历史求和可得

$$
\begin{aligned}
\sum_{i,j}\|F_{ij}\|_1
&\le\sum_{i,j}\|B_{ij}\|_1+f\\
&\le L_0+L_1+f\\
&\le\sqrt{(a+1)^2-4a(1-e)}+f=2U(e,f).
\end{aligned}
$$

只需证明对满秩初态，这条链至少有一步严格。以下只考察第一历史 $i=0$ 就足够。

若该历史的末次控制满足 $c_0c_1=0$，将两个末次结果互换后可记为 $c_0=1,c_1=0$。这时 $v_0=\alpha r_i$，另一个向量 $v_1$ 与 $b r_{1-i}$ 只差一个整体相位。令 $q=q_i$，有

$$
B_{i0}=(a\alpha^2-1)|r_i\rangle\langle r_i|,
\qquad
B_{i1}=ab^2|r_{1-i}\rangle\langle r_{1-i}|.
$$

记 $A_*=a\alpha^2q$、$B_*=ab^2(1-q)$。由于 $a\alpha^2<1$，完美读取后的加权块迹范数之和为

$$
J_i:=\|B_{i0}\|_1+\|B_{i1}\|_1
=q-A_*+B_*.
$$

此时 $L_i^2=(A_*+B_*+q)^2-4A_*q$，直接相减得到

$$
L_i^2-J_i^2
=4A_*B_*
=4a^2(1-e)e\,q(1-q)>0.
$$

因此 $J_i<L_i$，这个历史上的迹范数收缩已经严格，整体最终值也严格小于 $U(e,f)$。

现在设 $c=c_0>0$、$d=c_1>0$，并简记 $r=r'_i=cv_0+dv_1$。两个比较矩阵为

$$
B_0=a|v_0\rangle\langle v_0|
-\frac{c^2}{\alpha^2}|r\rangle\langle r|,
\qquad
B_1=a|v_1\rangle\langle v_1|
-\frac{d^2}{\alpha^2}|r\rangle\langle r|.
$$

令

$$
A=\|v_0\|^2,
\qquad B=\|v_1\|^2,
\qquad C=\langle v_0,v_1\rangle.
$$

线性无关性给出 $AB-|C|^2>0$，并且

$$
\det B_0=\det B_1
=-\frac{a}{\alpha^2}c^2d^2(AB-|C|^2)<0.
$$

因此 $B_0,B_1$ 都是可逆不定 Hermitian 矩阵。

下面使用迹范数三角等号的一条直接后果。设 $D$ 是可逆不定的二阶 Hermitian 矩阵，$\kappa>0$。若

$$
\|D+\kappa|v\rangle\langle v|\|_1
=\|D\|_1+\kappa\|v\|^2,
$$

则 $v$ 必须属于 $D$ 的正谱子空间。为核对这一点，取实现左端迹范数对偶最大值的 Hermitian 收缩算子 $S$，即 $-I\le S\le I$。等号要求

$$
\operatorname{tr}(SD)=\|D\|_1,
\qquad
\langle v,Sv\rangle=\|v\|^2.
$$

在 $D$ 的特征基中，非零正、负特征值迫使 $S$ 的两个对角元分别为 $1,-1$，收缩条件再迫使非对角元为零。因此 $S=\operatorname{sign}(D)$，而第二个等号表示 $v$ 的负谱投影为零。这里没有使用迹范数的严格凸性。

假设同一第一历史中的两个三角不等式都取等。因为 $f>0$，上述后果分别要求

$$
B_0v_1=\lambda_0v_1,
\qquad
B_1v_0=\lambda_1v_0,
\qquad \lambda_0,\lambda_1>0.
$$

在独立基 $v_0,v_1$ 中展开。第一式沿 $v_1$ 的系数、第二式沿 $v_0$ 的系数分别为

$$
\lambda_0=-\frac{c^2d}{\alpha^2}(cC+dB),
\qquad
\lambda_1=-\frac{cd^2}{\alpha^2}(cA+d\overline C).
$$

这些系数为实且非负，迫使 $C$ 为实数，并且

$$
C\le-\frac dcB,
\qquad
C\le-\frac cdA.
$$

所以 $|C|^2\ge AB$，与独立向量的严格 Cauchy--Schwarz 不等式矛盾。两个末次结果的三角不等式不能同时取等，因而这个第一历史已经给出严格损失，最终值仍严格小于 $U(e,f)$。

每个纯两比特初态的系统边缘态秩只能是一或二。秩一情形由无参考严格界排除；满秩情形的末次控制则被上述 $c_0c_1=0$ 与 $c_0c_1>0$ 两类穷尽。因此每个纯初态及控制表的值都严格小于 $U(e,f)$。再使用第 23.1 条的最优值达到性，便得到优化后的 $T_2^{\mathrm{ref}}(e,f)<U(e,f)$。定理 22.2 已给出 $T_2^{\mathrm{mem}}=U$，从而得到两个访问范围在参数方形内域的严格分离。

最后核对四条边界。若 $e=0$，指针初态与恒等控制给出实际全零历史概率 $1-f$、理想全零历史概率一，所以无参考差异达到 $f=U(0,f)$。若 $f=0$，命题 18.3 的末次完美读取构造达到 $\sqrt e=U(e,0)$。若 $e=1$ 或 $f=1$，指针初态与恒等控制使两种经典历史支撑不交，达到 $1=U(e,f)$。这些方案都不需要参考或可操作记忆，结合定理 22.2 的统一上界，四条边界上的两个最优值相等。参数域被内域与四条边界穷尽，得到所述充要分类。证毕。

## 追加锚（新终端）

## 24. 任意有限历史下惰性参考与可操作记忆的完整等号分类

**定理 24.1（两种访问权限的有限历史等号分类）。** 沿用定义 21.1 的惰性参考任务与定义 22.1 的可操作记忆任务。前者允许初始 $SR$ 纠缠，过程内仅使用依赖已存经典历史的共同系统控制 $U\in U(2)$，不操作参考、不与参考耦合，最终丢弃活动系统并输出 $H_NR$；后者允许任意有限维记忆和共同 $SM$ CPTP 控制，最终丢弃活动系统并输出 $H_NM$。对任意有限 $N\ge1$ 和参数 $\beta_t\in[0,1]$，令

$$
f=\beta_N,
\qquad a=1-f,
\qquad s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad E=1-s^2,
$$

其中空积为一，并令

$$
U(E,f)=\frac{f+\sqrt{(a+1)^2-4as^2}}2.
$$

总有

$$
T_N^{\mathrm{ref}}(\boldsymbol\beta)
\le T_N^{\mathrm{mem}}(\boldsymbol\beta)=U(E,f).
$$

当 $N=1$ 时，两者都等于 $f$。当 $N\ge2$ 时，完整等号分类为

$$
\begin{aligned}
&T_N^{\mathrm{ref}}(\boldsymbol\beta)
=T_N^{\mathrm{mem}}(\boldsymbol\beta)=U(E,f)\\
&\quad\Longleftrightarrow\quad
\left[
\beta_{N-1}=0\ \text{或}\ \beta_N=0
\ \text{或存在 }t\in\{1,\ldots,N\}\text{ 使 }\beta_t=1
\right].
\end{aligned}
$$

因此，所有参数均小于一、且最后两项均为正时，惰性参考的最优值严格低于可操作记忆的最优值；更早位置的零参数不改变这个严格性结论。本定理比较上述两个指定控制类，不给出严格区域内惰性参考最优值的显式公式或统一正差距常数。

证明。定理 22.2 给出记忆任务的精确值及包含惰性参考的共同 CPTP 控制上界。无参考系统幺正任务包含于惰性参考任务，惰性参考任务又可作为不操作记忆的特殊协议，故

$$
T_N\le T_N^{\mathrm{ref}}\le T_N^{\mathrm{mem}}=U(E,f).
$$

$N=1$ 时，指针初态达到 $f=U(0,f)$。当 $N\ge2$ 且所列三个条件之一成立时，定理 22.3 的无参考构造已经达到 $U(E,f)$，从而以上夹逼给出充分性。

为证明必要性，以下固定 $N\ge2$，并假设

$$
0\le\beta_t<1\quad(1\le t\le N),
\qquad \beta_{N-1}>0,
\qquad \beta_N>0.
$$

于是 $a,f,s$ 均为正。先将任意有限参考的上确界化为达到的有限维最大值。对固定控制表，输出迹距离关于共同输入密度矩阵凸，故任意混合输入的某个纯态分量不比它差。活动系统为二维，纯输入的 Schmidt 秩至多为二；参考全程不被操作，其 Schmidt 支撑可等距识别为参考量子比特的子空间，输出迹范数不变。秩一时补一个零坐标即可。因此纯两比特联合输入已经包含原上确界。

对固定有限 $N$，全部共同系统控制表属于有限个 $U(2)$ 的直积，一个矩阵对应历史树中的一个控制节点。这个空间与归一化两比特纯态的单位球面均紧，最终输出迹范数连续，故 $T_N^{\mathrm{ref}}$ 的最大值达到。

如果纯输入的系统边缘态秩为一，初态便是乘积态。参考在全部历史上始终是同一个固定因子，最终差异等于相应无参考协议的经典历史差异。定理 22.3 在当前参数条件下给出 $T_N<U(E,f)$。所以只需排除系统边缘态满秩的纯输入及控制表达到上界的可能性。

先处理所有参数均非零的情形，此时全部 $\beta_t\in(0,1)$。固定系统边缘态满秩的纯初态和共同系统控制表。对每个长度 $N-1$ 的旧历史 $h$，记实际与理想的未归一化 $SR$ 分支向量为 $\xi_h,\eta_h$，并令

$$
p_h=\|\xi_h\|^2,
\qquad q_h=\|\eta_h\|^2,
\qquad \gamma_h=\langle\eta_h,\xi_h\rangle.
$$

因为 $0<\beta_t<1$，实际每个 $K_{t,z}$ 都可逆，共同系统酉也可逆。局部可逆算子的有限乘积保持 Schmidt 秩，故每个实际前缀分支 $\xi_h$ 都具有 Schmidt 秩二，特别地 $p_h>0$。理想前缀至少经历了一次秩一系统投影，因此

$$
\eta_h=|i_h\rangle\otimes r_h,
\qquad i_h=h_{N-1},
$$

其中参考向量 $r_h$ 可以为零。

对每步的同一历史控制，实际与理想仪器满足

$$
\sum_zP_zK_{t,z}=\sqrt{1-\beta_t}\,I_S.
$$

共同系统酉保持分支内积，因而从相同初态的内积一开始，逐步对全部历史求和得到

$$
\sum_h\gamma_h=s>0.
$$

同时仪器完备性给出 $\sum_hp_h=\sum_hq_h=1$。内积求和式没有要求每个 $\gamma_h$ 单独为实或非负，但它保证存在一个历史 $h_*$ 满足 $\gamma_{h_*}\ne0$；于是该历史的理想向量也非零。

令末次仪器前的加权差块为

$$
Z_h=a|\xi_h\rangle\langle\xi_h|
-|\eta_h\rangle\langle\eta_h|.
$$

秩一差值公式给出

$$
L_h:=\|Z_h\|_1
=\sqrt{(ap_h+q_h)^2-4a|\gamma_h|^2}.
$$

二维实向量 $(L_h,2\sqrt a\,|\gamma_h|)$ 的范数是 $ap_h+q_h$。对全部历史使用欧氏三角不等式，再用复数三角不等式，得到

$$
\begin{aligned}
\left(\sum_hL_h\right)^2
&\le(a+1)^2-4a\left(\sum_h|\gamma_h|\right)^2\\
&\le(a+1)^2-4as^2.
\end{aligned}
$$

固定历史 $h$，令其末次共同控制为 $W_h$，并定义

$$
v_{h,j}=(\langle j|W_h\otimes I_R)\xi_h,
\qquad
c_{h,j}=|\langle j|W_h|i_h\rangle|,
\qquad j\in\{0,1\}.
$$

有 $c_{h,0}^2+c_{h,1}^2=1$，而两个参考向量 $v_{h,0},v_{h,1}$ 线性无关。这是因为 $\xi_h$ 的 Schmidt 秩为二，末次系统酉保持该秩。两向量范数平方之和为 $p_h$。

实际和理想最终参考块之差为

$$
F_{h,j}=a|v_{h,j}\rangle\langle v_{h,j}|
+f|v_{h,1-j}\rangle\langle v_{h,1-j}|
-c_{h,j}^2|r_h\rangle\langle r_h|.
$$

记其中不含末次翻转项的比较块为

$$
B_{h,j}=a|v_{h,j}\rangle\langle v_{h,j}|
-c_{h,j}^2|r_h\rangle\langle r_h|.
$$

这两个 $B_{h,j}$ 正是 $Z_h$ 经共同末次系统酉、假想完美指针读取和丢弃系统后的输出块，故

$$
\sum_j\|B_{h,j}\|_1\le L_h.
$$

再对末次翻转项使用迹范数三角不等式，得到

$$
\begin{aligned}
\sum_{h,j}\|F_{h,j}\|_1
&\le\sum_{h,j}\|B_{h,j}\|_1
+f\sum_hp_h\\
&\le\sum_hL_h+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

下面只考察已经选出的 $h_*$，并省略该历史下标。记 $r=r_{h_*}\ne0$、$v_j=v_{h_*,j}$、$c_j=c_{h_*,j}$。只要在这个历史上证明收缩或三角不等式中的一步严格，整体最终值就严格低于 $U(E,f)$。

先设 $c_0c_1=0$。互换末次结果后可取 $c_0=1,c_1=0$；理想控制后向量是 $|0\rangle\otimes r$，差一个无关整体相位。令

$$
p_0=\|v_0\|^2,
\qquad p_1=\|v_1\|^2,
\qquad q=\|r\|^2,
\qquad k=|\langle r,v_0\rangle|^2.
$$

线性无关性给出 $p_1>0$；共同酉保持完整分支内积，因此 $k=|\gamma_{h_*}|^2>0$。于是

$$
L_{h_*}^2=\bigl[a(p_0+p_1)+q\bigr]^2-4ak,
$$

而假想完美读取后的加权迹范数之和为

$$
J:=\|B_{h_*,0}\|_1+\|B_{h_*,1}\|_1
=\sqrt{(ap_0+q)^2-4ak}+ap_1.
$$

直接相减得到

$$
L_{h_*}^2-J^2
=2ap_1\left[ap_0+q
-\sqrt{(ap_0+q)^2-4ak}\right]>0.
$$

根式为实数，因为 $k\le p_0q$；方括号严格为正，因为 $a,k>0$。因此 $J<L_{h_*}$，该历史的迹范数收缩严格。

现设 $c_0,c_1>0$。由于 $v_0,v_1$ 是参考空间的一组基，存在复系数 $\ell,m$ 使

$$
r=\ell v_0+mv_1.
$$

这里的展开系数不要求与系统控制幅度 $c_0,c_1$ 相同。两类系数将分开保留。当 $\ell,m$ 同时非零时，先独立选择 $v_0,v_1$ 的代表相位，使这两个展开系数均为正实数；这不改变参考投影或目标值。若有一个系数为零，则不必改动相位。在相应代表下统一记

$$
A=\|v_0\|^2,
\qquad B=\|v_1\|^2,
\qquad C=\langle v_0,v_1\rangle,
\qquad AB-|C|^2>0.
$$

使用第 23.2 条证明中的迹范数等号后果：若二阶 Hermitian 矩阵 $D$ 可逆且不定、$\kappa>0$，则

$$
\|D+\kappa|v\rangle\langle v|\|_1
=\|D\|_1+\kappa\|v\|^2
$$

要求 $v$ 属于 $D$ 的正谱子空间。其理由是取实现左端的 Hermitian 对偶收缩算子；等号迫使它同时实现 $D$ 的迹范数和正项的迹，而 $D$ 可逆不定时前一个条件唯一决定该算子为 $\operatorname{sign}(D)$。

如果 $\ell,m$ 都非零，按照已选代表有 $\ell,m>0$。两个比较块

$$
B_0=a|v_0\rangle\langle v_0|-c_0^2|r\rangle\langle r|,
\qquad
B_1=a|v_1\rangle\langle v_1|-c_1^2|r\rangle\langle r|
$$

满足

$$
\det B_0=-ac_0^2m^2(AB-|C|^2)<0,
\qquad
\det B_1=-ac_1^2\ell^2(AB-|C|^2)<0.
$$

若两个末次结果的三角不等式同时取等，$f>0$ 和上述等号后果要求

$$
B_0v_1=\lambda_0v_1,
\qquad B_1v_0=\lambda_1v_0,
\qquad \lambda_0,\lambda_1>0.
$$

在独立基 $v_0,v_1$ 中比较系数，得到

$$
\lambda_0=-c_0^2m(\ell C+mB),
\qquad
\lambda_1=-c_1^2\ell(\ell A+m\overline C).
$$

这些特征值为实且非负，迫使 $C$ 为实数，并满足

$$
C\le-\frac m\ell B,
\qquad
C\le-\frac\ell m A.
$$

所以 $|C|^2\ge AB$，与向量独立性矛盾。因此两个三角不等式不能同时取等。

还需处理展开系数为零的情况。若 $\ell=0$，则 $m\ne0$，$r=mv_1$，并且

$$
B_0=a|v_0\rangle\langle v_0|
-c_0^2|m|^2|v_1\rangle\langle v_1|
$$

是可逆不定矩阵。若其三角不等式取等，$v_1$ 必为 $B_0$ 的正特征向量。然而

$$
B_0v_1=aCv_0-c_0^2|m|^2\|v_1\|^2v_1.
$$

独立性与 $a>0$ 先迫使 $C=0$，随后对应特征值等于 $-c_0^2|m|^2\|v_1\|^2<0$，矛盾。若 $m=0$，对 $B_1$ 和 $v_0$ 使用同一计算，也得到严格三角不等式。因为 $r\ne0$，两个系数不会同时为零。这穷尽了 $c_0,c_1>0$ 的全部情况。

因此，所有参数均非零时，每个满秩纯输入和控制表都有某一步严格不等式，不能达到 $U(E,f)$。

还需处理存在更早零参数的情形。选取一个 $k\le N-2$ 使 $\beta_k=0$。这一步实际和理想结果算子均为秩一投影 $P_z$，所以每个非零历史分支在这一步之后都成为 $S$ 与 $R$ 的乘积向量。后续所有算子仅作用于系统，乘积结构一直保持；实际与理想分支的参考因子可以不同。特别地，倒数第二步之前的每个父历史已经具有这种乘积结构。

反设某个纯输入及控制表达到 $U(E,f)$。对每个长度 $N-1$ 的历史 $h$，把末次共同控制之前的实际、理想分支写成

$$
\xi_h=x_h\otimes r_h^{\mathrm A},
\qquad
\eta_h=y_h\otimes r_h^{\mathrm J},
$$

允许因子未归一化或为零。令末次共同系统控制为 $W_h$。在两候选上都假想使用完美末次指针读取，所得未归一化纯参考向量是

$$
u_{h,j}=\langle j|W_hx_h\rangle\,r_h^{\mathrm A},
\qquad
v_{h,j}=\langle j|W_hy_h\rangle\,r_h^{\mathrm J}.
$$

这里的 $u_{h,j}$ 是假想完美读取的实际候选参考向量，不是带有末次错误的最终参考态。用 $i=(h,j)$ 简记最终经典坐标，并设

$$
P_i=\|u_i\|^2,
\qquad Q_i=\|v_i\|^2,
\qquad \delta_i=\langle v_i,u_i\rangle.
$$

共同末次控制及假想完美读取保持内积总和。由前缀交叉算子恒等式与仪器完备性，仍有

$$
\sum_i P_i=\sum_i Q_i=1,
\qquad \sum_i\delta_i=s>0.
$$

定义

$$
D_i=a|u_i\rangle\langle u_i|-|v_i\rangle\langle v_i|,
\qquad
L_i=\|D_i\|_1
=\sqrt{(aP_i+Q_i)^2-4a|\delta_i|^2},
\qquad
C=\sum_i|\delta_i|\ge s.
$$

真正的最终实际、理想差块则是

$$
D_{h,j}+f|u_{h,1-j}\rangle\langle u_{h,1-j}|.
$$

对本协议最终半迹距离 $T$，迹范数三角不等式和欧氏三角不等式给出

$$
\begin{aligned}
2T
&\le\sum_iL_i+f\\
&\le\sqrt{(a+1)^2-4aC^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

在假设的达到情形下，每一步都必须取等。因为 $a>0$、$s>0$，根式关于 $C$ 严格递减，故 $C=s$。同时，向量 $(L_i,2\sqrt a\,|\delta_i|)$ 的范数为 $aP_i+Q_i$，欧氏三角不等式取等迫使所有非零向量同向。因此对每个活坐标，即 $P_i+Q_i>0$ 的坐标，精确有

$$
|\delta_i|=\frac{s(aP_i+Q_i)}{a+1}>0.
$$

于是 $P_i>0$ 当且仅当 $Q_i>0$，而且每个活坐标的两个参考向量都非零、内积非零。这里相同的是最终经典坐标上的非零质量支撑，不要求参考向量平行，也不要求它们的秩一密度算子具有相同支撑。

另一方面，

$$
\sum_i\operatorname{tr}D_i=a-1=-f<0.
$$

所以存在一个坐标 $(h,j)$ 满足 $\operatorname{tr}D_{h,j}<0$。它是活坐标，故其 $u=u_{h,j}$、$v=v_{h,j}$ 都非零且 $\langle v,u\rangle\ne0$。乘积结构保证 $u_{h,1-j}$ 与 $u$ 平行。下面证明它必须为零。

如果 $u,v$ 线性无关，$D=a|u\rangle\langle u|-|v\rangle\langle v|$ 在二维参考空间上可逆不定。若 $u_{h,1-j}\ne0$，末次迹范数三角不等式取等要求该噪声向量属于 $D$ 的正谱子空间，因而要求 $u$ 是 $D$ 的特征向量。但

$$
Du=a\|u\|^2u-\langle v,u\rangle v
$$

并不与 $u$ 平行，因为内积非零且两向量独立，矛盾。如果 $u,v$ 平行，负迹条件使 $D$ 成为非零负半定秩一算子。任何沿同一方向的非零正算子与它相加，标量三角不等式都严格，同样矛盾。因此 $u_{h,1-j}=0$。经典坐标非零质量支撑相同又给出 $v_{h,1-j}=0$。

选中坐标的 $u_{h,j},v_{h,j}$ 均非零，所以经过 $W_h$ 后，实际和理想的系统因子都指向同一个指针 $|j\rangle$。共同系统酉可逆，故控制之前的两个系统因子平行。这一步没有断言完整 $SR$ 分支向量平行。

将该历史写为 $h=g\ell$，其中 $\ell$ 是倒数第二次结果。因为完美读取已经在深度 $k\le N-2$ 发生，父历史 $g$ 的两候选均为乘积态。把倒数第二次共同控制后的系统因子分别记作 $x,y$，并保留各自非零的参考因子。令

$$
\alpha=\sqrt{1-\beta_{N-1}}>0,
\qquad b=\sqrt{\beta_{N-1}}>0.
$$

选中理想子分支非零，其系统因子为 $P_\ell y$，指向 $|\ell\rangle$；选中实际子分支系统因子与它平行。因此

$$
(\alpha P_\ell+bP_{1-\ell})x
\ \parallel\ |\ell\rangle,
$$

且左端非零。由于 $\alpha,b>0$，比较两个指针分量得到 $x$ 非零且指向 $|\ell\rangle$。

考察兄弟历史 $h'=g(1-\ell)$。其实际系统因子为

$$
(\alpha P_{1-\ell}+bP_\ell)x=bx\ne0,
$$

仍指向 $|\ell\rangle$。若兄弟理想子分支为零，则其两个最终假想完美读取坐标均有 $Q_i=0$，而实际分支非零保证至少一个坐标有 $P_i>0$，违反非零质量支撑相同。故兄弟理想分支也非零，系统因子 $P_{1-\ell}y$ 指向另一个指针。两候选在这个兄弟历史上的完整分支内积因系统正交而为零。因此，无论其末次共同控制如何，

$$
\sum_j\delta_{h',j}=0.
$$

兄弟历史的实际分支非零，至少一个最终坐标是活坐标；该坐标的 $\delta$ 非零。于是

$$
\sum_j|\delta_{h',j}|>0
=\left|\sum_j\delta_{h',j}\right|.
$$

对其他历史使用复数三角不等式，便得到

$$
\begin{aligned}
C=\sum_{h,j}|\delta_{h,j}|
&>\sum_h\left|\sum_j\delta_{h,j}\right|\\
&\ge\left|\sum_{h,j}\delta_{h,j}\right|=s,
\end{aligned}
$$

与达到所必需的 $C=s$ 矛盾。这排除了更早存在完美读取时达到上界的可能性。

当前参数条件下，秩一输入、所有参数非零时的满秩输入、以及更早存在零参数时的满秩输入已被穷尽。所有纯输入及共同系统幺正控制表都不能达到 $U(E,f)$，而紧性保证惰性参考任务的最大值确实达到，因此

$$
T_N^{\mathrm{ref}}(\boldsymbol\beta)<U(E,f)
=T_N^{\mathrm{mem}}(\boldsymbol\beta).
$$

这给出所列等号条件的必要性，并与充分性合成完整分类。证毕。

## 追加锚（新终端）

## 25. 两步惰性参考任务中系统 CPTP 控制的完整归约

**定义 25.1（无可操作记忆的两步系统 CPTP 控制）。** 在定义 21.1 的两步任务中，令 $e=\beta_1\in[0,1]$、$f=\beta_2\in[0,1]$。保持任意有限维惰性参考 $R$、两候选共同联合输入和最终输出 $H_2R$ 的约定，只把系统控制从共同历史依赖 $U(2)$ 扩大为共同历史依赖的系统 CPTP 映射。第一控制无历史可用，第二控制只依赖已存第一结果；实际与理想过程使用同一张控制表。控制只作用于活动系统 $S=\mathbb C^2$，可以丢弃余系统，但这些余系统不再被访问或重新耦合。没有另一个可操作量子记忆，不操作参考、不与参考耦合，不后选择，末次仪器之后丢弃活动系统。对所有允许的共同输入、共同控制表和有限参考取最优半迹距离，记为 $T_2^{\mathrm{ref,CPTP}}(e,f)$；定义 21.1 的原系统幺正任务仍记作 $T_2^{\mathrm{ref}}(e,f)$。

**定理 25.2（两步 CPTP 归约、高末次错误率精确值及最小记忆维数）。** 对定义 25.1 的完整参数域，有

$$
T_2^{\mathrm{ref,CPTP}}(e,f)
=T_2^{\mathrm{ref}}(e,f).
$$

当 $0\le f\le\tfrac12$ 时，对任意固定共同输入和共同 CPTP 控制表，吸收第一控制后的共同输入作为新初态，再逐个第一历史选择依赖该输入的共同系统幺正替换，即可使最终半迹距离不减。当 $\tfrac12\le f\le1$ 时，两类任务都有精确值

$$
T_2^{\mathrm{ref,CPTP}}(e,f)
=T_2^{\mathrm{ref}}(e,f)
=e+f-ef.
$$

后一数值无需参考，指针初态和两步恒等控制即可达到。

进一步，在定义 22.1 的两步可操作记忆任务中，仍允许任意共同 $SM$ CPTP 控制，并允许额外任意有限维惰性参考 $R$，最终保留 $H_2MR$。以达到定理 22.2 的最优值 $U(e,f)$ 为目标，所需非零可操作记忆 $M$ 的最小维数恰为

$$
d_{\min}(e,f)=
\begin{cases}
2,&0<e<1\ \text{且}\ 0<f<1,\\
1,&e\in\{0,1\}\ \text{或}\ f\in\{0,1\}.
\end{cases}
$$

结论限定于两步及上述访问权限、控制类和保留输出，不把一般多步任务的控制类或最小记忆维数等同，也不求 $f<\tfrac12$ 时原惰性参考最优值的闭式。

证明。记 $a=1-f$、$\alpha=\sqrt{1-e}$、$b=\sqrt e$，并令

$$
P_i=|i\rangle\langle i|,
\qquad K_i=\alpha P_i+bP_{1-i},
\qquad i\in\{0,1\}.
$$

第一共同系统 CPTP 控制对任意共同联合输入 $\omega_{SR}$ 的输出仍是一个允许的共同联合态。由于初态自由选择，把这个输出直接作为新初态，并把第一控制改为恒等，不改变后续两个候选输出。因此只需考虑第一控制恒等的协议，且不必限制输入为纯态或参考维数。

固定第一历史 $i$，记其末次共同系统 CPTP 控制为 $\Lambda_i$。因为末次仪器之后丢弃活动系统，这个控制对最终参考块的作用只通过效应算子

$$
E_i=\Lambda_i^*(P_0),
\qquad 0\le E_i\le I,
\qquad \Lambda_i^*(P_1)=I-E_i
$$

体现。这里星号表示 Heisenberg 对偶。实际末次结果 $0$ 的效应为 $fI+(a-f)E_i$，结果 $1$ 的效应为 $aI+(f-a)E_i$；理想末次的两个效应为 $E_i,I-E_i$。这来自

$$
K_{2,0}^\dagger K_{2,0}=aP_0+fP_1,
\qquad
K_{2,1}^\dagger K_{2,1}=aP_1+fP_0
$$

及 $\Lambda_i^*(I)=I$。

对固定共同输入和第一历史，两个最终参考差块关于 $E_i$ 都是仿射函数，故它们迹范数之和 $G_i(E_i)$ 是凸函数。任意二阶效应算子都可以写成

$$
E_i=\lambda_{\min}I
+(\lambda_{\max}-\lambda_{\min})Q
+(1-\lambda_{\max})0,
\qquad
0\le\lambda_{\min}\le\lambda_{\max}\le1,
$$

其中 $Q$ 是秩一正交投影；重特征值时任选 $Q$。这是 $I,Q,0$ 的凸组合。因此存在一个 $E_i'\in\{I,Q,0\}$，使 $G_i(E_i')\ge G_i(E_i)$。秩一投影 $Q$ 可写成 $V_i^\dagger P_0V_i$，由一个共同系统幺正 $V_i$ 实现；效应 $I$ 与 $0$ 分别由把系统重置为 $|0\rangle$ 与 $|1\rangle$ 的 CPTP 映射实现。

先设 $f\le\tfrac12$，于是 $a\ge f$。下面证明两个常值效应都可由系统幺正控制支配。对当前第一历史 $i$，定义输入的两个对角参考块

$$
X=\langle i|\omega_{SR}|i\rangle,
\qquad Y=\langle1-i|\omega_{SR}|1-i\rangle.
$$

它们可以为零，且都半正定。第一步后，实际候选的参考边缘块为 $(1-e)X+eY$，理想候选的参考块为 $X$。定义 Hermitian 算子

$$
D=[a(1-e)-1]X.
$$

若末次效应 $E_i=I$，两个最终参考差块分别为

$$
D+aeY,
\qquad f(1-e)X+feY.
$$

第二块半正定，故对应迹范数之和为

$$
G_i(I)=\|D+aeY\|_1
+f(1-e)\operatorname{tr}X+fe\operatorname{tr}Y.
$$

改用指针投影效应 $E_i=P_i$，两个最终参考差块则为

$$
D+feY,
\qquad f(1-e)X+aeY,
$$

从而

$$
G_i(P_i)=\|D+feY\|_1
+f(1-e)\operatorname{tr}X+ae\operatorname{tr}Y.
$$

因为 $(a-f)eY$ 半正定，迹范数三角不等式给出

$$
\|D+aeY\|_1
\le\|D+feY\|_1+(a-f)e\operatorname{tr}Y.
$$

代入即得 $G_i(I)\le G_i(P_i)$。常值效应 $E_i=0$ 只把 $E_i=I$ 的两个末次结果交换，因此 $G_i(0)=G_i(I)$，同样被一个指针投影效应支配。

由此，任意效应先取不劣的 $I,Q,0$ 之一，再把常值效应替换为不劣的指针投影，最终总能取到一个不劣的秩一投影。两个第一历史的控制可独立选取，最终经典历史块的迹范数相加，所以逐历史替换使完整输出半迹距离不减。所有替换都作用于系统，保持同一个共同输入和惰性参考。结合第一控制的吸收，任意系统 CPTP 协议均被一个合法系统幺正协议支配，故

$$
T_2^{\mathrm{ref,CPTP}}(e,f)
\le T_2^{\mathrm{ref}}(e,f)
\qquad(0\le f\le\tfrac12).
$$

反向不等式来自控制类包含，低参数区间的等式成立。

现设 $f\ge\tfrac12$，于是 $a\le f$。仍把第一控制吸收到输入中，并记当前第一历史上两个末次理想效应为

$$
E_{i,0}=E_i,
\qquad E_{i,1}=I-E_i.
$$

整个两步过程对初始系统的实际、理想历史效应分别为

$$
A_{ij}=K_i\bigl[fI+(a-f)E_{i,j}\bigr]K_i,
\qquad
J_{ij}=P_iE_{i,j}P_i.
$$

因为 $0\le E_{i,j}\le I$，有

$$
fI+(a-f)E_{i,j}\ge aI,
\qquad 0\le J_{ij}\le P_i.
$$

设 $c=a(1-e)$。逐个历史的算子序给出

$$
A_{ij}\ge aK_i^2
=a(1-e)P_i+aeP_{1-i}
\ge cP_i\ge cJ_{ij}.
$$

实际、理想历史效应各自构成 POVM，故

$$
A_{ij}-cJ_{ij}\ge0,
\qquad
\sum_{i,j}(A_{ij}-cJ_{ij})=(1-c)I.
$$

这里 $c\le\tfrac12$，所以 $1-c>0$。因此

$$
C_{ij}=\frac{A_{ij}-cJ_{ij}}{1-c}
$$

也是一组 POVM。记三个相应的量子到经典通道为 $\mathcal A,\mathcal J,\mathcal C$，逐效应恒等式给出真正的通道凸分解

$$
\mathcal A=c\mathcal J+(1-c)\mathcal C.
$$

对任意有限惰性参考和任意共同联合输入，$\mathcal C\otimes\operatorname{id}_R$ 与 $\mathcal J\otimes\operatorname{id}_R$ 的输出都是密度矩阵，两者迹距离至多为一。因此

$$
\frac12\left\|
\bigl[(\mathcal A-\mathcal J)\otimes\operatorname{id}_R\bigr](\omega_{SR})
\right\|_1
\le1-c=e+f-ef.
$$

这个界对任意末次系统 CPTP 控制和共同输入成立。

取无参考初态 $|0\rangle$，第一控制和两个末次历史控制均为恒等。实际与理想候选的系统在每个非零历史上都保持指针 $|0\rangle$。理想历史必为 $00$；实际历史为 $00$ 的概率是 $(1-e)(1-f)=c$。因此最终经典历史的总变差恰为 $1-c=e+f-ef$，已经由原系统幺正任务达到。结合上界与控制类包含，高参数区间的精确值以及两类任务的等式均成立。两段在 $f=\tfrac12$ 相容，并穷尽完整参数域。

最后证明所述最小记忆维数。$\dim M=1$ 时，$SM$ 上的任意共同 CPTP 控制正是系统共同 CPTP 控制，任意额外惰性参考也正是定义 25.1 允许的输入及最终参考。因此该维数下的最优值等于本定理已经确定的 $T_2^{\mathrm{ref}}(e,f)$。当 $e,f\in(0,1)$ 时，定理 23.2（亦为定理 24.1 的两步情形）给出

$$
T_2^{\mathrm{ref}}(e,f)<U(e,f),
$$

故一维可操作记忆不足以达到目标，即使允许任意额外惰性参考也不例外。定理 22.2 的一个记忆量子比特及末次一次 SWAP 已经达到 $U(e,f)$，所以二维足够，内域的最小维数为二。

若 $e\in\{0,1\}$ 或 $f\in\{0,1\}$，定理 22.3 的两步边界构造在无参考、无可操作记忆的系统幺正任务中已达到 $U(e,f)$。它可在 $\dim M=1$ 的任务中原样实现，而记忆维数按定义必须为正，所以四边的最小维数为一。这完成全部结论。证毕。

## 追加锚（新终端）

## 26. 高末次错误率公式向三步推广的精确反例

**定理 26.1（三步共同幺正反馈超过简单成功概率界）。** 在定义 18.1 的无参考、无可操作记忆任务中，取

$$
N=3,
\qquad \beta_1=\beta_2=\frac1{10},
\qquad \beta_3=\frac12.
$$

存在共同初态 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 和共同历史依赖实正交系统控制表，使最终三位经典历史的实际、理想总变差恰为

$$
T(\Pi)=\frac14+\frac{\sqrt{13}}{10}.
$$

因此，该参数下原无参考最优值满足

$$
T_3\!\left(\frac1{10},\frac1{10},\frac12\right)
\ge\frac14+\frac{\sqrt{13}}{10}
>\frac{119}{200}
=1-\prod_{t=1}^3(1-\beta_t).
$$

这个反例否定把定理 25.2 的两步高末次错误率公式推广为任意有限步数的等式或上界 $1-\prod_t(1-\beta_t)$，即使仍有 $\beta_N\ge\tfrac12$。本例在共同系统幺正类内实现，不证明 CPTP 控制比幺正控制更优，也不主张达到可操作记忆上界；所有参数都在定理 24.1 的严格区域中。

证明。第一共同控制取恒等。令

$$
P_i=|i\rangle\langle i|,
\qquad
K_i=\frac3{\sqrt{10}}P_i+\frac1{\sqrt{10}}P_{1-i},
\qquad i\in\{0,1\},
$$

它们分别是前两步共同使用的理想、实际结果算子。第一结果为 $i$ 时，记实际、理想未归一化系统向量为

$$
x_i=K_i|+\rangle,
\qquad y_i=P_i|+\rangle.
$$

定义实对称矩阵

$$
D_i=\frac1{20}\|x_i\|^2I
+\frac25|x_i\rangle\langle x_i|
-|y_i\rangle\langle y_i|.
$$

第二共同控制 $U_i\in O(2)$ 取为 $D_i$ 的一个正交本征基，即令 $U_iD_iU_i^{\mathsf T}$ 为对角矩阵。本征值的排列任意，控制表在实验之前由上述固定矩阵确定，实际与理想过程始终使用同一个 $U_i$。

设前两位历史是 $ij$，其实际、理想概率分别为

$$
p_{ij}=\|K_jU_ix_i\|^2,
\qquad q_{ij}=\|P_jU_iy_i\|^2.
$$

因为

$$
K_j^\dagger K_j=\frac1{10}I+\frac45P_j,
$$

有

$$
\begin{aligned}
\frac12p_{ij}-q_{ij}
&=\frac1{20}\|x_i\|^2
+\frac25|\langle j|U_ix_i\rangle|^2
-|\langle j|U_iy_i\rangle|^2\\
&=\langle j|U_iD_iU_i^{\mathsf T}|j\rangle.
\end{aligned}
$$

按本征基选择控制，便得到

$$
\sum_j\left|\frac12p_{ij}-q_{ij}\right|=\|D_i\|_1.
$$

第三共同控制取 $W_{ij}=X^j$，其中 $X|0\rangle=|1\rangle$、$X|1\rangle=|0\rangle$。每个非零理想前缀分支在第二次读取后都指向 $|j\rangle$，因此这个控制使理想末次结果恒为零。实际末次参数为 $\beta_3=\tfrac12$，两个结果算子都为 $I/\sqrt2$，无论分支系统态如何，两个末次结果的条件概率均为一半。故三位最终历史 $ijk$ 的概率满足

$$
p_{ij0}=p_{ij1}=\frac12p_{ij},
\qquad q_{ij0}=q_{ij},
\qquad q_{ij1}=0.
$$

使用 $\sum_{i,j}p_{ij}=1$，该协议的最终总变差为

$$
\begin{aligned}
T(\Pi)
&=\frac12\sum_{i,j}
\left(\left|\frac12p_{ij}-q_{ij}\right|
+\frac12p_{ij}\right)\\
&=\frac14+\frac12\sum_i\|D_i\|_1.
\end{aligned}
$$

这里的末次读数归约只用实际末次均匀读取以及共同控制使理想末次结果确定；它把本例的输出距离转化为两个具体加权差矩阵的迹范数。

直接代入初态得到

$$
x_0=\frac1{\sqrt{20}}\begin{pmatrix}3\\1\end{pmatrix},
\qquad y_0=\frac1{\sqrt2}\begin{pmatrix}1\\0\end{pmatrix},
\qquad x_1=Xx_0,
\qquad y_1=Xy_0.
$$

所以

$$
D_0=\frac1{200}
\begin{pmatrix}-59&12\\12&9\end{pmatrix},
\qquad D_1=XD_0X.
$$

两个矩阵的本征值都是

$$
\lambda_\pm=-\frac18\pm\frac{\sqrt{13}}{20}.
$$

一正一负，因而

$$
\|D_0\|_1=\|D_1\|_1=\frac{\sqrt{13}}{10},
\qquad
T(\Pi)=\frac14+\frac{\sqrt{13}}{10}.
$$

另一方面，简单成功概率表达式是

$$
1-\prod_{t=1}^3(1-\beta_t)
=1-\frac9{10}\frac9{10}\frac12
=\frac{119}{200}.
$$

两者之差为

$$
\frac14+\frac{\sqrt{13}}{10}-\frac{119}{200}
=\frac{20\sqrt{13}-69}{200}>0,
$$

因为 $20^2\cdot13=5200>4761=69^2$。这给出精确的严格反例。

定理 22.2 在本参数下的记忆最优值为

$$
U\!\left(\frac{19}{100},\frac12\right)
=\frac14+\frac{3\sqrt7}{20},
$$

而本构造严格低于它，因为 $2\sqrt{13}<3\sqrt7$ 等价于 $52<63$。本例超过的是被推广的简单成功概率表达式，与定理 24.1 的访问权限严格分离相容。证毕。

## 追加锚（新终端）

## 27. 任意有限历史的末次 CPTP 控制分类与加权前缀目标

**定义 27.1（任意有限历史的系统 CPTP 控制与惰性参考）。** 对任意有限 $N\ge1$ 和参数 $\boldsymbol\beta\in[0,1]^N$，沿用定义 25.1 的系统 CPTP 控制访问权限，推广为 $N$ 次读取。活动系统为 $S=\mathbb C^2$，允许任意有限维惰性参考 $R$ 和两候选共同使用的归一化联合输入。每次仪器之前，只根据已经存储的经典历史，在 $S$ 上施加共同 CPTP 控制；实际与理想过程使用同一张控制表。控制余系统一旦丢弃，就不再被访问或重新耦合；没有可操作量子记忆，不操作参考、不与参考耦合，不后选择。第 $t$ 次实际、理想结果算子仍为

$$
K_{t,z}=\sqrt{1-\beta_t}\,P_z+\sqrt{\beta_t}\,P_{1-z},
\qquad P_z=|z\rangle\langle z|,
\qquad z\in\{0,1\}.
$$

末次仪器之后丢弃 $S$，输出 $H_NR$。对所有允许的共同输入、共同系统 CPTP 控制表和有限参考取最优半迹距离，记作 $T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)$。

**定理 27.2（末次控制的完整分段归约）。** 对定义 27.1 的 $N\ge2$，令 $f=\beta_N$、$a=1-f$。固定共同输入和前 $N-1$ 步的共同控制表。对每个长度 $N-1$ 的历史 $h$，记末次控制之前实际、理想未归一化分支态为 $\rho_h^{\mathrm A},\rho_h^{\mathrm J}$，并令

$$
X_h=\operatorname{Tr}_S\rho_h^{\mathrm A},
\qquad Q_h=\operatorname{Tr}_S\rho_h^{\mathrm J}.
$$

当 $0\le f\le\tfrac12$ 时，任意末次共同系统 CPTP 控制都可逐历史替换为一个共同系统幺正控制，使最终半迹距离不减。替换可依赖已固定的输入和前缀分支态。

当 $\tfrac12\le f\le1$ 时，对这个固定前缀，末次共同系统重置

$$
\mathcal R_0(\sigma)=|0\rangle\langle0|\operatorname{tr}\sigma
$$

已经最优；相应最优半迹距离恰为

$$
\frac12\sum_h\left(\|aX_h-Q_h\|_1+f\operatorname{tr}X_h\right).
$$

因而在高末次错误率区间，有精确表达

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=\frac f2+\frac12\sup_{\text{共同输入、有限参考及前缀共同 CPTP 控制}}
\sum_{h\in\{0,1\}^{N-1}}\|aX_h-Q_h\|_1.
$$

右端前缀使用给定的前 $N-1$ 个仪器参数，包含所有共同输入和前 $N-1$ 次系统控制；其控制余系统仍不可再访问。$N=1$ 时另有 $T_1^{\mathrm{ref,CPTP}}(\beta_1)=\beta_1$。本定理只归约末次控制，不把此前的系统 CPTP 控制等同于幺正控制；高错误率表达仍保留对完整前缀的优化，不将它化为简单成功概率乘积。

证明。理想过程在倒数第二次仪器后刚经历秩一指针投影。无论共同输入是否混合、参考维数为何、此前系统 CPTP 控制怎样选择，每个理想分支都满足

$$
\rho_h^{\mathrm J}=P_{i_h}\otimes Q_h,
\qquad i_h=h_{N-1}.
$$

零分支也包含在内。两候选仪器和控制均保持总迹，所以

$$
X_h,Q_h\ge0,
\qquad \sum_h\operatorname{tr}X_h
=\sum_h\operatorname{tr}Q_h=1.
$$

固定一个历史，暂时省略下标 $h$，把 $i_h$ 记为 $i$、实际分支记为 $\rho$。若末次系统控制为 $\Lambda$，令

$$
E=\Lambda^*(P_0),
\qquad 0\le E\le I.
$$

末次丢弃系统之后，实际两个参考块只依赖效应 $fI+(a-f)E$ 与 $aI+(f-a)E$，理想两个参考块则为 $uQ,(1-u)Q$，其中

$$
u=\langle i|E|i\rangle\in[0,1].
$$

因此，固定前缀分支后，两个参考差块关于 $E$ 是仿射函数，它们迹范数之和 $G(E)$ 是凸函数。任意二阶效应都可按其特征值分解为

$$
E=\lambda_{\min}I
+(\lambda_{\max}-\lambda_{\min})\Pi
+(1-\lambda_{\max})0,
\qquad 0\le\lambda_{\min}\le\lambda_{\max}\le1,
$$

其中 $\Pi$ 为秩一正交投影；重特征值时可任选。故 $I,\Pi,0$ 之中至少一个效应的目标不小于 $G(E)$。秩一效应可由系统幺正实现，而 $I,0$ 分别由重置到两个指针实现。

先处理 $f\le\tfrac12$，即 $a\ge f$。在当前理想指针基下，定义实际分支的两个参考对角块

$$
Y=\langle i|\rho|i\rangle,
\qquad Z=\langle1-i|\rho|1-i\rangle,
\qquad Y,Z\ge0,
\qquad Y+Z=X.
$$

令 $D=aY-Q$。常值效应 $E=I$ 的两个参考差块为

$$
D+aZ,
\qquad fY+fZ,
$$

故

$$
G(I)=\|D+aZ\|_1+f\operatorname{tr}Y+f\operatorname{tr}Z.
$$

指针投影效应 $E=P_i$ 的两个参考差块为

$$
D+fZ,
\qquad fY+aZ,
$$

故

$$
G(P_i)=\|D+fZ\|_1+f\operatorname{tr}Y+a\operatorname{tr}Z.
$$

因为 $(a-f)Z$ 半正定，

$$
\|D+aZ\|_1
\le\|D+fZ\|_1+(a-f)\operatorname{tr}Z,
$$

代入即得 $G(I)\le G(P_i)$。效应 $E=0$ 只交换常值效应 $I$ 的两个结果，因此 $G(0)=G(I)$，也被指针投影支配。结合凸分解，任意末次效应都可替换为一个不劣的秩一投影。这些投影在每个历史上分别选择，由共同系统幺正实现；历史块的迹范数相加，所以整体目标不减。证明没有要求实际分支与理想分支的参考因子相同，也没有把替换断言为对所有输入同时成立的通道支配。

现处理 $f\ge\tfrac12$，即 $a\le f$。记任意末次控制之后的实际联合分支为

$$
\sigma=(\Lambda\otimes\operatorname{id}_R)(\rho),
\qquad Y_j=\langle j|\sigma|j\rangle.
$$

系统 CPTP 控制保持参考边缘，因此 $Y_0+Y_1=X$。实际末次两个参考块为

$$
A_0=aY_0+fY_1,
\qquad A_1=fY_0+aY_1.
$$

它们满足

$$
A_0+A_1=X,
\qquad A_0\ge aX,
\qquad A_1\ge aX.
$$

理想两个参考块仍为 $uQ,(1-u)Q$，$u\in[0,1]$。固定当前 $A_0,A_1$，函数

$$
g(v)=\|A_0-vQ\|_1+\|A_1-(1-v)Q\|_1
$$

关于 $v\in[0,1]$ 凸，所以 $g(u)\le\max\{g(0),g(1)\}$。这里两个端点只用于数学上界，不要求它们与固定的 $A_0,A_1$ 来自同一个可实现控制。

对 $v=1$，令 $B=A_0-aX\ge0$。迹范数三角不等式与 $A_1\ge0$ 给出

$$
\begin{aligned}
g(1)
&=\|A_0-Q\|_1+\operatorname{tr}A_1\\
&\le\|aX-Q\|_1+\operatorname{tr}B+\operatorname{tr}A_1\\
&=\|aX-Q\|_1+f\operatorname{tr}X.
\end{aligned}
$$

最后一步使用 $B+A_1=X-aX=fX$。交换 $A_0,A_1$，同样得到 $g(0)$ 不超过这个值。因此，任何末次系统 CPTP 控制的当前历史贡献均不超过

$$
\|aX-Q\|_1+f\operatorname{tr}X.
$$

共同重置 $\mathcal R_0$ 把实际联合分支送到 $P_0\otimes X$，把理想联合分支送到 $P_0\otimes Q$。它的实际末次参考块是 $aX,fX$，理想末次参考块是 $Q,0$，恰好达到所示上界。这一构造可以在所有历史上同时采用。因此固定前缀的最优值就是定理中的块范数之和；再用 $\sum_h\operatorname{tr}X_h=1$ 并对所有允许前缀取上确界，得到精确加权前缀表达。这里不需要证明参考维数归约或最优前缀达到。

在共同边界 $f=\tfrac12$，实际末次参考块始终是 $X/2,X/2$。把理想指针 $|i\rangle$ 幺正地送到 $|0\rangle$，就与重置产生相同的最终参考块，因此两种归约相容。

最后，$N=1$ 没有先前的理想指针投影，不能对任意固定输入套用上述分支乘积论证。此时把唯一共同 CPTP 控制的输出吸收为自由共同输入；定理 22.2 的参考一致上界给出 $T_1^{\mathrm{ref,CPTP}}\le U(0,\beta_1)=\beta_1$。指针输入与恒等控制已达到 $\beta_1$，所以所述单步值成立。这完成全部有限步数的相应结论。证毕。

## 追加锚（新终端）

## 28. 连续高错误率尾段的精确消去与成功概率公式

**定义 28.1（共同系统 CPTP 前缀的加权参考差异）。** 固定定义 27.1 的前缀参数 $\beta_1,\ldots,\beta_k$，其中 $k\ge1$。对每个允许的共同输入、有限维惰性参考和前 $k$ 次共同系统 CPTP 控制，在第 $k$ 次仪器后对活动系统取部分迹，记历史 $h\in\{0,1\}^k$ 的实际、理想未归一化参考块为 $X_h,Q_h$。这些部分迹只定义前缀的参考读数；续接时仍保留活动系统。对 $c\in[0,1]$，定义

$$
W_k(c)=\sup_{\text{共同输入、有限参考及前 }k\text{ 次共同 CPTP 控制}}
\sum_{h\in\{0,1\}^k}\|cX_h-Q_h\|_1.
$$

参数前缀由下标所指的给定仪器确定，记号中省略；两候选使用共同输入与控制表，控制余系统仍不可再访问，参考始终不可操作。系数 $c$ 只用于比较输出，不改变实际仪器或物理输入的归一化。

**定理 28.2（高错误率尾段的加权消去及全高尾段闭式）。** 对任意有限 $N\ge k\ge1$，假设

$$
\beta_t\ge\frac12
\qquad(k+1\le t\le N),
\qquad
C=\prod_{t=k+1}^N(1-\beta_t),
$$

其中空积为一。则定义 27.1 的最优值精确满足

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=\frac{1-C}{2}+\frac12W_k(C).
$$

对每个固定的前 $k$ 步协议，尾段所有共同控制都取为重置到 $|0\rangle$，已经达到该固定前缀的最优续接值；前缀的全局优化仍按定义取上确界。

单步加权值在全部 $\beta_1,c\in[0,1]$ 上为

$$
W_1(c)=1+c-2c(1-\beta_1).
$$

因此，只要每个 $t=2,\ldots,N$ 都满足 $\beta_t\ge\tfrac12$，便有完整精确值

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=1-\prod_{t=1}^N(1-\beta_t).
$$

它由无参考指针输入 $|0\rangle$ 和全部恒等系统控制达到。所需条件覆盖整个被消去尾段；只知道最后一个参数至少为一半时，仍须保留较长前缀的 $W_k(C)$，不能据此套用单步公式。本结论不比较一般中间 CPTP 控制与系统幺正控制的最优值。

证明。首先把定理 27.2 的高末次错误率论证用于加权实际块。设 $j\ge2$、$\beta_j\ge\tfrac12$，记 $b=\beta_j$、$d=1-b$，并固定前 $j-1$ 步的协议。对一个旧历史，实际分支记为 $\rho$，参考边缘为 $X$；理想分支为 $P_i\otimes Q$。此乘积结构来自第 $j-1$ 次理想指针读取，对混合输入和任意此前共同系统 CPTP 控制同样成立。

对任意第 $j$ 次共同系统 CPTP 控制，记实际两个输出参考块为 $A_0,A_1$。如第 27.2 条，它们满足

$$
A_0+A_1=X,
\qquad A_0,A_1\ge dX,
$$

理想两个输出参考块为 $uQ,(1-u)Q$，其中 $u\in[0,1]$。在当前加权目标中，实际块变为 $cA_0,cA_1$。固定这些块，对理想系数使用凸性，得到

$$
\begin{aligned}
&\|cA_0-uQ\|_1+\|cA_1-(1-u)Q\|_1\\
&\quad\le\max\left\{
\|cA_0-Q\|_1+c\operatorname{tr}A_1,
\ c\operatorname{tr}A_0+\|cA_1-Q\|_1
\right\}.
\end{aligned}
$$

因为 $c\ge0$，有 $c(A_0-dX)\ge0$。迹范数三角不等式给出

$$
\begin{aligned}
\|cA_0-Q\|_1+c\operatorname{tr}A_1
&\le\|cdX-Q\|_1
+c\operatorname{tr}(A_0-dX)+c\operatorname{tr}A_1\\
&=\|cdX-Q\|_1+cb\operatorname{tr}X.
\end{aligned}
$$

另一个端点同理。共同重置到 $|0\rangle$ 时，实际两块为 $dX,bX$，理想两块为 $Q,0$，恰好达到这个界。整个推导没有除以 $c$，所以也覆盖 $c=0$；加权只是把实际正块乘以非负标量，不要求它们仍是归一化态。

对全部旧历史相加，物理实际分支的总迹始终满足 $\sum_h\operatorname{tr}X_h=1$，从而第 $j$ 步的固定前缀最优加权值为

$$
cb+\sum_h\|cdX_h-Q_h\|_1.
$$

再对全部允许的共同前缀取上确界，得到精确递推

$$
W_j(c)=c\beta_j+W_{j-1}\bigl(c(1-\beta_j)\bigr)
\qquad(j\ge2,\ \beta_j\ge\tfrac12).
$$

上界对任意第 $j$ 次控制成立，达到由重置给出；这两方向保证是等式。对固定更早前缀也可重复同一论证，因此无需先假定最优前缀达到。

现在对定理中的尾段反向应用递推。设

$$
c_j=\prod_{t=j+1}^N(1-\beta_t)
\qquad(k\le j\le N).
$$

于是 $c_N=1$、$c_k=C$，且对 $j=k+1,\ldots,N$ 有

$$
c_{j-1}=c_j(1-\beta_j),
\qquad c_j\beta_j=c_j-c_{j-1}.
$$

由于定义直接给出 $2T_N^{\mathrm{ref,CPTP}}=W_N(1)$，逐步消去尾段并对常数项望远镜求和，得到

$$
\begin{aligned}
2T_N^{\mathrm{ref,CPTP}}
=W_N(1)
&=\sum_{j=k+1}^Nc_j\beta_j+W_k(c_k)\\
&=1-C+W_k(C).
\end{aligned}
$$

空尾段时求和为零，这个式子仍成立。对每个固定前缀，逐步达到使用尾段每次共同重置。也可直接核对：实际尾段的全零记录概率为 $C$，其余记录的总概率为 $1-C$，每种尾段记录都只把同一参考块 $X_h$ 乘以对应标量；理想尾段确定全零，参考块为 $Q_h$。故该固定前缀的最优续接半迹距离为

$$
\frac12\sum_h\left(\|CX_h-Q_h\|_1
+(1-C)\operatorname{tr}X_h\right),
$$

与递推所得表达一致。

还需计算单步加权值。第一共同系统 CPTP 控制的输出可吸收为自由共同输入 $\omega_{SR}$。令

$$
Z_i=\langle i|\omega_{SR}|i\rangle,
\qquad Z_i\ge0,
\qquad \operatorname{tr}Z_0+\operatorname{tr}Z_1=1.
$$

一次实际、理想仪器之后，参考块分别为 $(1-\beta_1)Z_i+\beta_1Z_{1-i}$ 与 $Z_i$。加权差块是

$$
[c(1-\beta_1)-1]Z_i+c\beta_1Z_{1-i}.
$$

由于 $0\le c\le1$，两个所需系数 $1-c(1-\beta_1)$ 与 $c\beta_1$ 都非负。逐块三角不等式给出

$$
\begin{aligned}
&\sum_i\bigl\|[c(1-\beta_1)-1]Z_i+c\beta_1Z_{1-i}\bigr\|_1\\
&\quad\le\bigl[1-c(1-\beta_1)\bigr]
\sum_i\operatorname{tr}Z_i
+c\beta_1\sum_i\operatorname{tr}Z_{1-i}\\
&\quad=1+c-2c(1-\beta_1).
\end{aligned}
$$

无参考指针输入 $|0\rangle$ 与恒等控制使两个结果的加权差分别为 $c(1-\beta_1)-1$ 和 $c\beta_1$，一非正、一非负，恰好达到上界。这证明全部参数域上的单步公式。

当每个 $t\ge2$ 都满足高错误率条件时，取 $k=1$，代入 $W_1(C)$ 即得

$$
T_N^{\mathrm{ref,CPTP}}
=\frac{1-C}{2}
+\frac{1+C-2C(1-\beta_1)}2
=1-\prod_{t=1}^N(1-\beta_t).
$$

这个值也由全部恒等控制及初态 $|0\rangle$ 达到：理想记录确定全零，实际记录全零的概率恰为成功概率乘积，系统在所有非零分支上一直保持同一个指针。$N=1$ 时高尾段条件为空，所得数值就是 $\beta_1$，与单步结论一致。

第 26.1 条的参数 $\beta_1=\beta_2=\tfrac1{10}$、$\beta_3=\tfrac12$ 只允许在这里取 $k=2$ 消去最后一步，留下 $W_2(1/2)$；第二步不满足继续消去到单步所需的高错误率条件。因此本定理的成功概率公式不适用于那个反例。证毕。

## 追加锚（新终端）

## 29. 加权两步参考差异的 Pauli 协变放宽与解析上界

**定义 29.1（两步加权目标与保留活动系统的放宽）。** 在定义 28.1 的两步任务中，显式写出参数

$$
W_2(c;e,g),
\qquad 0\le c,e\le1,\quad 0\le g\le\frac12,
$$

其中 $e=\beta_1$、$g=\beta_2$。共同输入、惰性参考、共同历史依赖系统 CPTP 控制和末端部分迹的约定均不变。令

$$
a=1-g,\qquad z=1-2g,
\qquad K_i=\sqrt{1-e}\,P_i+\sqrt e\,P_{1-i}.
$$

定义系统退极化通道

$$
\mathcal D_g(\sigma)=z\sigma+g\operatorname{tr}(\sigma)I_S.
$$

由于 $\mathcal D_g$ 是恒等通道与完全退极化通道 $\sigma\mapsto\operatorname{tr}(\sigma)I_S/2$ 按权重 $1-2g,2g$ 的混合，它是 CPTP 映射。它满足任意系统幺正 $U$ 下的协变性

$$
\mathcal D_g(U\sigma U^\dagger)
=U\mathcal D_g(\sigma)U^\dagger.
$$

以 $H_1$ 存储第一次结果，定义两个从 $S$ 到 $H_1S$ 的通道

$$
\mathcal A_{e,g}(\sigma)
=\bigoplus_{i=0}^1\mathcal D_g(K_i\sigma K_i),
\qquad
\mathcal J_e(\sigma)
=\bigoplus_{i=0}^1P_i\sigma P_i,
$$

以及 Hermitian 保持线性映射

$$
\mathcal F_c=c\mathcal A_{e,g}-\mathcal J_e.
$$

记保留 $H_1S$ 并允许惰性参考的加权差异为

$$
\mathcal B(c;e,g)
=\sup_{\substack{1\le\dim R<\infty\\
\omega_{SR}\ge0,\ \operatorname{tr}\omega_{SR}=1}}
\left\|(\mathcal F_c\otimes\operatorname{id}_R)(\omega_{SR})\right\|_1.
$$

这里以保留 $H_1S$ 的固定通道定义放宽目标；其与原任务的关系由下述共同后处理建立，$\mathcal F_c$ 不再包含对控制表的优化。系数 $c$ 不是物理通道的成功概率，也不改变输入归一化。

**定理 29.2（两步解析上界、严格改进与精确参数区间）。** 对定义 29.1 的全部参数域，令

$$
B(c;e,g)
=cg+\sqrt{
\bigl[1-c(1-g)(1-2e)\bigr]^2
+4c^2(1-2g)^2e(1-e)}.
$$

则

$$
W_2(c;e,g)\le\mathcal B(c;e,g)=B(c;e,g).
$$

放宽目标 $\mathcal B$ 的上确界由一个参考量子比特和 Bell 输入

$$
|\Phi\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2}
$$

达到；这不声称原目标 $W_2$ 达到 $B$。若另记

$$
A(c;e,g)
=cg+\sqrt{\bigl[1-c(1-g)\bigr]^2+4c(1-g)e},
$$

则在全部参数域有 $B\le A$，且

$$
c>0,\quad 0<e<1,\quad 0<g\le\frac12
\quad\Longrightarrow\quad B<A.
$$

在精确参数 $c=7/20$、$e=3/10$、$g=1/10$ 上，有

$$
\frac{\sqrt{534}}{25}
\le W_2\left(\frac7{20};\frac3{10},\frac1{10}\right)
\le\frac7{200}+\frac{\sqrt{207433}}{500}.
$$

结合定理 28.2，这给出相应三步任务的精确区间

$$
\frac{13}{40}+\frac{\sqrt{534}}{50}
\le T_3^{\mathrm{ref,CPTP}}
\left(\frac3{10},\frac1{10},\frac{13}{20}\right)
\le\frac{137}{400}+\frac{\sqrt{207433}}{1000}.
$$

证明。先证明任意允许的两步协议都被 $\mathcal B$ 控制。第一共同系统 CPTP 控制的输出可吸收为自由共同输入。末次控制的低错误率幺正归约也适用于当前加权目标：在定理 27.2 的逐历史证明中，将实际未归一化分支 $\rho$ 换成 $c\rho$，保留理想分支 $P_i\otimes Q$。该证明只使用实际块的半正定性、效应的凸分解与迹范数三角不等式，没有使用分支归一化。具体地，以

$$
Y=c\langle i|\rho|i\rangle,
\qquad Z=c\langle1-i|\rho|1-i\rangle,
\qquad D=aY-Q
$$

代入，仍有

$$
\|D+aZ\|_1\le\|D+gZ\|_1+(a-g)\operatorname{tr}Z.
$$

因此两个常值效应被指针投影支配，任意末次共同 CPTP 控制均可换成一个使当前加权目标不减的共同系统幺正。该替换针对固定输入逐历史选择，允许依赖这一输入。

对第一历史 $i$，把其末次共同幺正记作 $U_i$。在任意联合分支 $\rho_{SR}$ 上，第二次实际仪器产生的第 $j$ 个参考块为

$$
a\langle j|U_i\rho_{SR}U_i^\dagger|j\rangle
+g\langle1-j|U_i\rho_{SR}U_i^\dagger|1-j\rangle.
$$

这恰好等于先施加 $\mathcal D_g\otimes\operatorname{id}_R$，再施加 $U_i$ 并作完美指针读取所得的参考块；交叉项在系统部分迹后为零。理想候选同样在其第一分支上施加 $U_i$ 并完美读取。因此，原两步输出的加权差异由

$$
(\mathcal F_c\otimes\operatorname{id}_R)(\omega_{SR})
$$

经同一个依赖 $H_1$ 的 CPTP 后处理得到：调用 $U_i$、完美读取第二结果并丢弃 $S$。Hermitian 算子的迹范数在这一后处理下收缩，所以每个原协议的值不超过 $\mathcal B$，从而 $W_2\le\mathcal B$。

下面直接证明 $\mathcal B$ 的 Bell 达到性。令 $X,Z$ 是系统 Pauli 矩阵，$X_H$ 交换历史基 $|0\rangle,|1\rangle$。从

$$
K_iZ=ZK_i,\qquad P_iZ=ZP_i,
\qquad K_iX=XK_{1-i},\qquad P_iX=XP_{1-i}
$$

及 $\mathcal D_g$ 的协变性，得到

$$
\begin{aligned}
\mathcal F_c(Z\sigma Z)
&=(I_H\otimes Z)\mathcal F_c(\sigma)(I_H\otimes Z),\\
\mathcal F_c(X\sigma X)
&=(X_H\otimes X)\mathcal F_c(\sigma)(X_H\otimes X).
\end{aligned}
$$

故对于四个系统 Pauli 算子 $V_p\in\{I,X,Z,XZ\}$，各存在输出幺正 $\widetilde V_p$，使 $\mathcal F_c(V_p\sigma V_p^\dagger)=\widetilde V_p\mathcal F_c(\sigma)\widetilde V_p^\dagger$。

任取有限参考和归一化纯输入 $|\psi\rangle_{SR}$，以四维辅助参考 $F$ 构造

$$
|\Omega\rangle_{SRF}
=\frac12\sum_{p=0}^3
(V_p\otimes I_R)|\psi\rangle_{SR}\otimes|p\rangle_F.
$$

这个向量归一化。若 $\rho_S=\operatorname{Tr}_R|\psi\rangle\langle\psi|$，则

$$
\operatorname{Tr}_{RF}|\Omega\rangle\langle\Omega|
=\frac14\sum_pV_p\rho_SV_p^\dagger=\frac{I_S}{2}.
$$

把 $\mathcal F_c$ 作用于 $S$，再对 $F$ 去相干，所得 Hermitian 算子是四个块的直和。每块为

$$
\frac14(\widetilde V_p\otimes I_R)
(\mathcal F_c\otimes\operatorname{id}_R)
(|\psi\rangle\langle\psi|)
(\widetilde V_p^\dagger\otimes I_R).
$$

块迹范数相加与幺正不变性表明，去相干后的总迹范数恰等于原输入 $|\psi\rangle$ 的目标值。去相干是 CPTP 映射，所以去相干前、即输入 $|\Omega\rangle$ 的目标值不小于原值。

另一方面，$|\Omega\rangle$ 是系统边缘为 $I_S/2$ 的纯态。其两个参考系数正交且模长均为 $1/\sqrt2$，故存在等距 $V:\mathbb C^2\to R\otimes F$，使

$$
|\Omega\rangle=(I_S\otimes V)|\Phi\rangle.
$$

映射只作用于 $S$，参考等距不改变输出迹范数，因此 $|\Omega\rangle$ 的值等于 Bell 输入的值。Bell 输入于是支配所有有限参考纯输入。对混合输入按纯态分解使用迹范数凸性，结论仍成立。Bell 输入本身可行，所以 $\mathcal B$ 的上确界确实由它达到。辅助标记 $F$ 仅用于这项放宽目标的证明，未被放回原协议作为可操作记忆。

计算 Bell 输出。第一历史 $i$ 的实际、理想向量分别为

$$
|x_i\rangle
=\frac{\sqrt{1-e}|ii\rangle+\sqrt e|1-i,1-i\rangle}{\sqrt2},
\qquad
|y_i\rangle=\frac{|ii\rangle}{\sqrt2}.
$$

该历史的放宽差块是

$$
c z|x_i\rangle\langle x_i|
+cg I_S\otimes\operatorname{Tr}_S|x_i\rangle\langle x_i|
-|y_i\rangle\langle y_i|.
$$

在子空间 $\operatorname{span}\{|ii\rangle,|1-i,1-i\rangle\}$ 上，它的矩阵为

$$
M=\frac12
\begin{pmatrix}
ca(1-e)-1&cz\sqrt{e(1-e)}\\
cz\sqrt{e(1-e)}&cae
\end{pmatrix}.
$$

另外两个正交方向的特征值是 $cg(1-e)/2$ 与 $cge/2$，均非负。注意

$$
\det M
=\frac{ce}{4}\bigl[cg(2-3g)(1-e)-(1-g)\bigr]\le0.
$$

事实上，括号内的负号由

$$
(1-g)-cg(2-3g)(1-e)
\ge1-3g+3g^2
=3\left(g-\frac12\right)^2+\frac14>0
$$

保证。因而 $ce>0$ 时 $M$ 的两特征值异号；$ce=0$ 时同一迹范数公式以连续性或直接计算成立。两特征值的间距给出

$$
\|M\|_1
=\frac12\sqrt{[1-ca(1-2e)]^2+4c^2z^2e(1-e)}.
$$

每个第一历史的块范数为 $cg/2+\|M\|_1$，两历史的表达相同，相加得到 $\mathcal B=B$。

比较两个解析表达，直接展开得

$$
\begin{aligned}
(B-cg)^2
&=(1-ca)^2+4cae
-4c^2g(2-3g)e(1-e)\\
&=(A-cg)^2-4c^2g(2-3g)e(1-e).
\end{aligned}
$$

两个平方根均非负，减去的项在完整参数域非负，在陈述的严格域为正。因此 $B\le A$，并得到所述严格不等式。

最后给出精确区间中的可实现下界。取无参考共同输入 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$、第一控制恒等。令 $x_i=K_i|+\rangle$、$y_i=P_i|+\rangle$，并定义系统 Hermitian 矩阵

$$
D_i=cg\|x_i\|^2I_S+czx_ix_i^\dagger-y_iy_i^\dagger.
$$

选择每个第一历史的共同末次幺正 $U_i$，使 $U_iD_iU_i^\dagger$ 对角。其第二结果 $j$ 的加权实际概率减理想概率恰为该矩阵的第 $j$ 个对角元。因此这个合法协议的目标值为 $\sum_i\|D_i\|_1$。

在指定参数上，直接得到

$$
D_0=\frac1{2000}
\begin{pmatrix}
-769&28\sqrt{21}\\
28\sqrt{21}&119
\end{pmatrix},
\qquad D_1=XD_0X.
$$

$D_0$ 的行列式为负，其两特征值间距为

$$
\sqrt{\left(\frac{-888}{2000}\right)^2
+4\left(\frac{28\sqrt{21}}{2000}\right)^2}
=\frac{\sqrt{534}}{50}.
$$

两历史相加得到 $\sqrt{534}/25$ 的可实现下界；它来自明确输入与共同控制，不依赖数值搜索。上界则将相同参数代入 $B$，使用

$$
cg=\frac7{200},
\qquad
[1-ca(1-2e)]^2+4c^2z^2e(1-e)=\frac{207433}{250000}.
$$

三步参数的高错误率末段为 $\beta_3=13/20$。定理 28.2 给出 $T_3^{\mathrm{ref,CPTP}}=13/40+W_2(7/20;3/10,1/10)/2$，代入两端即得最后一个区间。证毕。

## 追加锚（新终端）

## 30. 无参考加权两步目标的有限闭式与三步精确值

**定义 30.1（无参考的加权两步经典历史差异）。** 在定义 28.1 中把参考维数限制为一，并显式记第一、第二仪器参数为 $e,g$。共同系统 CPTP 控制的余系统不可再访问，无可操作记忆，无后选择，最终只保留两位经典历史。对所有共同输入和共同系统控制，记实际、理想历史概率为 $p_{ij},q_{ij}$，并定义

$$
W_2^{\mathrm{cl}}(c;e,g)
=\sup\sum_{i,j\in\{0,1\}}|cp_{ij}-q_{ij}|,
\qquad c,e\in[0,1],\quad g\in[0,1/2].
$$

系数 $c$ 仅为输出比较权重。无参考三步系统 CPTP 任务的最优半迹距离记作 $T_3^{\mathrm{cl,CPTP}}$；定义 18.1 原无参考系统幺正任务的最优值仍记作 $T_3$。

**定理 30.2（有限显式候选及三步无参考精确值）。** 在定义 30.1 的完整参数域，令

$$
d=c(1-2g),\qquad r=1-2e,\qquad v=1-cr,
$$

并定义端点与对称候选

$$
P=1+c-2c(1-e)(1-g),
\qquad B=\sqrt{(1-d)^2+4de}.
$$

若 $d=0$ 或 $e\in\{0,1\}$，则

$$
W_2^{\mathrm{cl}}(c;e,g)=P.
$$

这包含 $c=0$ 时的值一、$e=0$ 时的 $1-d$、$e=1$ 时的 $1+c$，以及 $g=1/2$ 时的 $1+ce$。这些情形不使用下述可能退化的分母。

在其余情形 $d>0$、$0<e<1$，令

$$
q_2=1-2d+d^2r^2,
\qquad q_1=2de(1+dr),
\qquad q_0=d^2e^2,
$$

$$
\eta=v+\frac{2q_2+q_1}{2[1-d(1-e)]}.
$$

若 $\eta\ge0$，精确值为

$$
W_2^{\mathrm{cl}}(c;e,g)=\max\{P,B\}.
$$

若 $\eta<0$，则必有 $q_2<0$。定义

$$
h=-q_2>0,
\qquad m=\frac{q_1}{2h},
\qquad \kappa=q_0+\frac{q_1^2}{4h}>0,
$$

$$
M=c(1-e)-1+vm+
\sqrt{\frac{\kappa(h+v^2)}h}.
$$

此时精确值为

$$
W_2^{\mathrm{cl}}(c;e,g)=\max\{P,B,M\}.
$$

第三个候选来自一个交叉项的唯一内部驻点，不需要对连续参数再作优化。上述每个最终最大值都可由纯共同输入、第一控制恒等及两个实正交末次共同控制达到，故这里的系统 CPTP 最优值也等于系统幺正类的最优值。公式没有额外断言第三候选总能被前两个排除。

对任意 $f\in[1/2,1]$，相应无参考系统 CPTP 三步值为

$$
T_3^{\mathrm{cl,CPTP}}(e,g,f)
=\frac f2+\frac12W_2^{\mathrm{cl}}(1-f;e,g).
$$

在 $f=1/2$ 的共同边界，原无参考系统幺正任务也满足

$$
T_3(e,g,1/2)
=\frac14+\frac12W_2^{\mathrm{cl}}(1/2;e,g).
$$

特别地，第 26.1 条的可达下界在这个原无参考任务中已经是精确最优值：

$$
T_3(1/10,1/10,1/2)
=\frac14+\frac{\sqrt{13}}{10}.
$$

这个升级只针对无参考任务，不把该数值宣告为惰性参考任务或可操作记忆任务的最优值。

证明。第一共同系统 CPTP 控制的输出可以吸收为自由共同输入。第二控制的加权幺正归约由定理 27.2 的低错误率证明得到：只需把实际分支乘以非负系数 $c$，其半正定性、效应凸分解和指针投影三角不等式均保持。因此，对每个固定输入，第二控制可取为两个共同系统幺正。

对固定幺正控制表，目标关于共同输入密度矩阵凸，故某个纯态分量的目标不低于混合输入。纯输入的相对相位可写成系统对角幺正；这个幺正与第一步的全部实际、理想结果算子交换，可以吸收到两个第二控制中。因此只需考虑

$$
|\psi_t\rangle=\sqrt t\,|0\rangle+\sqrt{1-t}\,|1\rangle,
\qquad t\in[0,1],
$$

并取第一控制恒等。记

$$
K_i=\sqrt{1-e}\,P_i+\sqrt e\,P_{1-i},
\qquad x_i=K_i|\psi_t\rangle,
\qquad y_i=P_i|\psi_t\rangle.
$$

在第一历史 $i$ 上，定义实对称矩阵

$$
D_i(t)=cg\|x_i\|^2I+d|x_i\rangle\langle x_i|-|y_i\rangle\langle y_i|.
$$

若第二控制为 $U_i$，则该历史的第二结果 $j$ 满足

$$
cp_{ij}-q_{ij}
=\langle j|U_iD_i(t)U_i^\dagger|j\rangle.
$$

对角元绝对值之和不超过 Hermitian 矩阵的迹范数；选择 $D_i(t)$ 的实正交本征基则达到等号。所以固定 $t$ 的最优值是

$$
F(t)=\|D_0(t)\|_1+\|D_1(t)\|_1,
\qquad W_2^{\mathrm{cl}}=\max_{0\le t\le1}F(t).
$$

这里最大值存在，因为 $F$ 连续。交换两个系统指针给出 $D_1(t)=XD_0(1-t)X$。令

$$
p(t)=e+rt,
\qquad L(t)=cp(t)-t=ce-vt,
\qquad R(t)=\sqrt{q_2t^2+q_1t+q_0}.
$$

$D_0(t)$ 的迹为 $L(t)$，两个本征值的间距为 $R(t)$。具体地，间距平方等于

$$
[de+(1-d)t]^2+4d^2e(1-e)t(1-t),
$$

展开就是上述 $q_2,q_1,q_0$。同时，$D_0(t)$ 在方向 $|1\rangle$ 上的二次型为

$$
cg\,p(t)+de(1-t)\ge0,
$$

所以其较大本征值非负。这保证 $-L(t)\le R(t)$，由二阶 Hermitian 矩阵的迹范数公式得到

$$
\|D_0(t)\|_1=\max\{L(t),R(t)\},
$$

从而

$$
F(t)=\max\{L(t),R(t)\}
+\max\{L(1-t),R(1-t)\}.
$$

先处理退化情形。若 $d=0$，则 $R(t)=t$；若 $e=0$，则 $R(t)=(1-d)t$；若 $e=1$，则 $R(t)=d+(1-d)t$。这些情形中的 $L,R$ 都是仿射函数，故 $F$ 凸。又有 $F(t)=F(1-t)$，所以最大值由 $t=0$ 或 $t=1$ 达到。直接代入得 $F(0)=P$，证明全部所列边界值，也避免了端点根为零时的求导。

以下设 $d>0$、$0<e<1$。此时 $R(t)>0$，并且

$$
4q_2q_0-q_1^2=-16d^3e^2(1-e)<0.
$$

因此

$$
R''(t)=\frac{4q_2q_0-q_1^2}{4R(t)^3}<0,
$$

即 $R$ 严格凹。把 $F$ 中的两个最大值展开成四种和，便有

$$
\begin{aligned}
F(t)=\max\{&L(t)+L(1-t),\ R(t)+R(1-t),\\
&L(t)+R(1-t),\ R(t)+L(1-t)\}.
\end{aligned}
$$

第一项恒为 $c-1\le0$。第二项由凹性在 $t=1/2$ 达到最大值

$$
2R(1/2)=\sqrt{(1-d)^2+4de}=B.
$$

两个交叉项在 $t\mapsto1-t$ 下互换，故具有相同最大值。令 $u=1-t$，则其中一个是

$$
L(t)+R(1-t)=L(1)+vu+R(u),
\qquad L(1)=c(1-e)-1.
$$

于是问题精确化为

$$
W_2^{\mathrm{cl}}
=\max\left\{B,\ L(1)+\max_{0\le u\le1}H(u)\right\},
\qquad H(u)=R(u)+vu.
$$

这一步只是有限最大值的分配，没有把两个函数各自凹误认为它们的逐点最大值仍凹。

$H$ 严格凹，且

$$
H'(0)=1+dr+v>0,
\qquad
H'(1)=v+\frac{2q_2+q_1}{2[1-d(1-e)]}=\eta.
$$

分母严格为正，因为 $1-d(1-e)\ge e>0$。若 $\eta\ge0$，严格凹性使 $H$ 在整个区间上不减，最大值取在 $u=1$。相应交叉值为

$$
L(1)+H(1)=ce+R(1)=P,
$$

于是 $W_2^{\mathrm{cl}}=\max\{P,B\}$，也包括 $\eta=0$ 的端点驻点。

若 $\eta<0$，则 $H'$ 从正变负且严格递减，存在唯一内部最大点。由于 $q_1>0$，$q_2\ge0$ 会使 $R'$ 全程为正，故此时必须有 $q_2<0$。按陈述中的 $h,m,\kappa$ 完成平方，得到

$$
R(u)=\sqrt{\kappa-h(u-m)^2}.
$$

方程 $H'(u)=0$ 的唯一适当符号解是

$$
u_*=m+v\sqrt{\frac{\kappa}{h(h+v^2)}}\in(0,1).
$$

代入得

$$
\max_{0\le u\le1}H(u)
=vm+\sqrt{\frac{\kappa(h+v^2)}h}.
$$

所以交叉项最大值为 $M$。因为这个内部最大值严格高于端点值，$M>P$；保留端点候选仍可统一写成 $W_2^{\mathrm{cl}}=\max\{P,B,M\}$。

这些公式也给出达到控制。端点候选取 $t=0$，对称候选取 $t=1/2$；若第三候选为最终最大项，取 $t=1-u_*$。在最后一种情况下，$F(1-u_*)\ge M$，而已证全局上界就是 $M$，因此该输入确实达到最优。随后在两个第一历史上分别用 $D_i(t)$ 的实正交本征基作第二共同控制。这完成有限闭式及幺正达到的证明；不需要再判断第三候选是否总被其他候选支配。

把定理 28.2 的同一加权尾段论证限制到平凡参考，便得到任何 $f\ge1/2$ 下的三步系统 CPTP 等式

$$
T_3^{\mathrm{cl,CPTP}}(e,g,f)
=\frac f2+\frac12W_2^{\mathrm{cl}}(1-f;e,g).
$$

在 $f=1/2$ 时，定理 27.2 已说明末次重置可以用把理想前缀指针送到 $|0\rangle$ 的系统幺正替代，而本定理已用系统幺正实现前两步加权最优值。因此整个三步值由原无参考系统幺正协议达到；控制类包含给出反向界，从而原 $T_3$ 也满足陈述中的精确式。

最后代入 $c=1/2$、$e=g=1/10$，得到

$$
d=\frac25,\quad r=\frac45,\quad v=\frac35,
\qquad q_2=\frac{189}{625},\quad q_1=\frac{66}{625},\quad q_0=\frac1{625},
$$

$$
\eta=\frac{231}{200}>0,
\qquad P=\frac{69}{100},
\qquad B=\frac{\sqrt{13}}5>P.
$$

因此 $W_2^{\mathrm{cl}}(1/2;1/10,1/10)=\sqrt{13}/5$，进而

$$
T_3(1/10,1/10,1/2)
=\frac14+\frac{\sqrt{13}}{10}.
$$

这把第 26.1 条同一无参考幺正构造的可达下界提升为该任务的精确值，且没有扩大其参考或记忆访问权限。证毕。

## 追加锚（新终端）

## 31. 高末次错误率下任意 CPTP 控制的记忆等号分类

**定理 31.1（任意有限前缀的加权上界）。** 令 $W_j(c)$ 为定义 28.1 的共同系统 CPTP 前缀目标，允许任意有限维惰性参考，没有可操作量子记忆。对任意有限 $j\ge1$、$c\in[0,1]$ 和仪器参数 $\beta_1,\ldots,\beta_j\in[0,1]$，记

$$
b=\beta_j,\qquad a=1-b,
\qquad s=\prod_{t=1}^{j-1}\sqrt{1-\beta_t},
$$

其中空积为一。则

$$
W_j(c)
\le cb+\sqrt{(1+ca)^2-4ca s^2}.
$$

这个界同时适用于任意共同输入、有限参考和全部共同历史依赖系统 CPTP 控制；它不要求前缀幺正，也不声称一般参数下达到该加权上界。

证明。当 $j=1$ 时，定理 28.2 的单步计算给出

$$
W_1(c)=1+c-2c(1-b)=cb+1-ca.
$$

由于 $0\le ca\le1$，这等于 $cb+\sqrt{(1+ca)^2-4ca}$，证明空前缀情形。

以下设 $j\ge2$，固定任意共同输入、有限参考和共同 CPTP 控制表。给共同输入作纯化；每个共同控制使用同一个 Stinespring 等距实现，并在分析中保留其余系统。对不同旧历史使用的等距按历史作共同受控调用。控制余系统始终不重新接入协议；保留它们只是为了表示完整纯化，计算物理输出时仍将它们取部分迹。

以 $B_t$ 存储本次新结果、$E_t$ 存储其丢弃副本，一次仪器可以由如下两种等距表示：

$$
V_{{\rm A},t}=\sum_{z=0}^1
|z\rangle_{B_t}|z\rangle_{E_t}\otimes K_{t,z},
\qquad
V_{{\rm J},t}=\sum_{z=0}^1
|z\rangle_{B_t}|z\rangle_{E_t}\otimes P_z.
$$

旧历史寄存器在此不变，$E_t$ 在物理协议中被丢弃。交叉算子满足

$$
V_{{\rm J},t}^\dagger V_{{\rm A},t}
=\sum_zP_zK_{t,z}
=\sqrt{1-\beta_t}\,I_S.
$$

共同受控等距保持完整纯化的内积，每个仪器则将该内积乘以上述标量。因此，经过前 $j-1$ 次仪器及第 $j$ 次共同 CPTP 控制后，完整纯化中的两候选可取为归一化向量 $|A\rangle,|J\rangle$，满足

$$
\langle J|A\rangle=s.
$$

惰性参考不参与控制。共同输入的纯化寄存器、控制余系统及历史副本只属于分析空间，不增加原协议的访问权限。

在两候选上都假设最后作完美指针读取，存储最后一位历史并丢弃活动系统和全部分析余系统。所得归一化经典量子态记为 $\mathsf P,\mathsf Q$，输出空间是 $H_jR$。它们来自 $|A\rangle,|J\rangle$ 经同一个 CPTP 映射，其中 $\mathsf Q$ 正好是理想最终输出。令 $\tau$ 仅翻转最后一位经典结果，保持旧历史和参考不动。

对第 $j$ 次控制后的任意实际联合历史分支 $\omega_h$，最后实际结果 $z$ 的参考块为

$$
\begin{aligned}
&\operatorname{Tr}_S\bigl[
(K_{j,z}\otimes I_R)\omega_h(K_{j,z}\otimes I_R)
\bigr]\\
&\qquad=a\langle z|\omega_h|z\rangle
+b\langle1-z|\omega_h|1-z\rangle.
\end{aligned}
$$

两个指针间的交叉项在系统部分迹后为零，所以实际最终态严格等于

$$
\mathsf R=a\mathsf P+b\tau(\mathsf P).
$$

这里没有限制最后共同控制的形式。于是

$$
\begin{aligned}
\|c\mathsf R-\mathsf Q\|_1
&=\|ca\mathsf P-\mathsf Q+cb\tau(\mathsf P)\|_1\\
&\le\|ca\mathsf P-\mathsf Q\|_1+cb\\
&\le\bigl\|ca|A\rangle\langle A|-|J\rangle\langle J|\bigr\|_1+cb\\
&=\sqrt{(1+ca)^2-4ca|\langle J|A\rangle|^2}+cb\\
&=\sqrt{(1+ca)^2-4ca s^2}+cb.
\end{aligned}
$$

第一项估计使用迹范数三角不等式及 $\|\tau(\mathsf P)\|_1=1$；第二项使用共同 CPTP 输出映射对 Hermitian 算子的迹范数收缩；最后使用两个加权秩一算子之差的迹范数公式。该公式也覆盖 $ca=0$，整个论证没有除以权重或分支概率。

物理输出对历史分块，因此 $\|c\mathsf R-\mathsf Q\|_1=\sum_h\|cX_h-Q_h\|_1$。上界不依赖共同输入、参考维数或共同控制表，对所有允许协议取上确界即得结论。证毕。

**定理 31.2（高末次错误率的完整等号域与最小可操作记忆）。** 对定义 27.1 的任意有限 $N\ge2$，假设最后参数

$$
f=\beta_N\in[1/2,1].
$$

记

$$
c=1-f,\qquad b=\beta_{N-1},\qquad a=1-b,
\qquad s=\prod_{t=1}^{N-2}\sqrt{1-\beta_t},
\qquad E=1-as^2.
$$

令 $U(E,f)$ 为定理 22.2 的可操作记忆最优值。在没有可操作记忆、允许任意有限惰性参考及所有共同历史依赖系统 CPTP 控制时，有完整等号分类

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)=U(E,f)
\quad\Longleftrightarrow\quad
\beta_{N-1}=0
\ \text{或}\ 
\exists t\in\{1,\ldots,N\},\ \beta_t=1.
$$

进一步定义

$$
r=\sqrt{(1+ca)^2-4ca s^2},
\qquad A=cb+r,
\qquad C=\sqrt{(1+c)^2-4ca s^2}.
$$

则

$$
T_N^{\mathrm{ref,CPTP}}\le\frac{f+A}{2}
\le\frac{f+C}{2}=U(E,f).
$$

在其余参数域，即 $b>0$ 且所有 $\beta_t<1$ 时，这个上界给出显式严格差距

$$
U(E,f)-T_N^{\mathrm{ref,CPTP}}
\ge\frac{cb(1+ca-r)}{C+A}>0.
$$

考虑定义 22.1 的可操作记忆任务，允许任意共同 $SM$ CPTP 控制和额外任意有限维惰性参考 $R$，最终输出 $H_NMR$。以达到 $U(E,f)$ 为目标，所需非零可操作记忆 $M$ 的最小维数为

$$
d_{\min}(\boldsymbol\beta)=
\begin{cases}
1,&\beta_{N-1}=0\ \text{或存在 }t\text{ 使 }\beta_t=1,\\
2,&\beta_{N-1}>0\ \text{且全部 }\beta_t<1.
\end{cases}
$$

当 $N=1$ 时，在完整参数域另有 $T_1^{\mathrm{ref,CPTP}}(\beta_1)=U(0,\beta_1)=\beta_1$，且 $d_{\min}=1$。本条多步等号分类和最小记忆结论限定于 $f\ge1/2$，不判定 $f<1/2$ 下任意中间系统 CPTP 控制的等号域。

证明。定理 27.2 对高末次错误率给出精确前缀表达

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)
=\frac f2+\frac12W_{N-1}(c).
$$

对这个任意 CPTP 前缀应用定理 31.1，得到 $W_{N-1}(c)\le cb+r=A$。这一步覆盖混合共同输入、任意有限参考及全部此前系统 CPTP 控制，不需要把中间控制替换为幺正。

由 $E=1-as^2$ 和 $f=1-c$，可操作记忆值中的平方根满足

$$
f^2+4(1-f)E
=(1+c)^2-4ca s^2=C^2,
$$

故 $U(E,f)=(f+C)/2$。直接展开得

$$
\begin{aligned}
C^2-A^2
&=(1+c)^2-(1+ca)^2-c^2b^2-2cbr\\
&=2cb(1+ca-r).
\end{aligned}
$$

所有系数非负，且 $r\le1+ca$，所以 $C^2\ge A^2$；由于 $C,A\ge0$，得到 $A\le C$。

设 $b>0$ 且全部 $\beta_t<1$。由于 $f<1$，有 $c>0$；由于 $b<1$，有 $a>0$；此前每个参数也小于一，故 $s>0$。因此

$$
(1+ca)^2-r^2=4ca s^2>0,
$$

从而 $1+ca-r>0$。这使 $C^2-A^2>0$，即 $A<C$。此外 $C\ge1-c=f\ge1/2$，所以 $C+A>0$，且

$$
\begin{aligned}
U(E,f)-T_N^{\mathrm{ref,CPTP}}
&\ge\frac{C-A}{2}\\
&=\frac{C^2-A^2}{2(C+A)}\\
&=\frac{cb(1+ca-r)}{C+A}>0.
\end{aligned}
$$

这是一条对所有允许协议统一成立的严格界，无需证明最优前缀达到。前面若有参数等于零，仍有 $s>0$，因此它们不被遗漏。

反过来，若存在某个 $\beta_t=1$，取无参考指针初态 $|0\rangle$ 和所有控制恒等。理想历史确定全零，而实际在该时刻必输出一，因此两种完整历史支撑不交，半迹距离为一。此时 $U(E,f)=1$，所以无需参考或可操作记忆即达到等号。

若 $\beta_{N-1}=0$，定理 22.3 已给出无参考、共同系统幺正控制达到 $U(E,f)$ 的构造。该协议包含于当前允许类中；结合统一上界，再次得到等号。这两个条件的补集恰为 $b>0$ 且全部 $\beta_t<1$，其严格不等式已证，故等号分类完整。

最后确定记忆维数。$\dim M=1$ 时，对 $SM$ 的共同 CPTP 控制恰退化为系统 CPTP 控制，额外惰性参考和最终保留的 $R$ 完全对应 $T_N^{\mathrm{ref,CPTP}}$。在严格域，统一差距排除 $\dim M=1$ 达到 $U$。另一方面，定理 22.2 已用一个初始为 $|0\rangle$ 的记忆量子比特、末次前的一次 SWAP 和此前共同实反馈达到 $U$，不需要惰性参考，所以 $\dim M=2$ 足够。在等号域，上述无参考构造以 $\dim M=1$ 已经达到；非零记忆空间的维数不能更小，得到所述最小维数。

$N=1$ 的共同系统 CPTP 控制可吸收为自由共同输入，定理 27.2 的单步值为 $\beta_1$；指针输入已经达到定理 22.2 的 $U(0,\beta_1)=\beta_1$。因此单步所需最小记忆维数为一，且不需要高错误率假设。证毕。

## 追加锚（新终端）

## 32. 低末次错误率下任意 CPTP 控制的严格记忆差距

**定理 32.1（低末次错误率的完整 CPTP 等号分类）。** 对定义 27.1 的任意有限 $N\ge2$，设

$$
0<f=\beta_N<\frac12,
\qquad a=1-f,
\qquad s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad E=1-s^2.
$$

允许任意有限维惰性参考、共同联合输入和全部共同历史依赖系统 CPTP 控制，没有可操作量子记忆，最终丢弃活动系统。则

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)=U(E,f)
\quad\Longleftrightarrow\quad
\beta_{N-1}=0
\quad\text{或}\quad
\exists t\in\{1,\ldots,N\},\ \beta_t=1,
$$

其中 $U(E,f)$ 是定理 22.2 的可操作记忆最优值。特别地，若 $\beta_{N-1}>0$ 且全部 $\beta_t<1$，则

$$
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)<U(E,f).
$$

这里的严格性覆盖任意中间系统 CPTP 控制；它不把这些控制逐一等同于系统幺正控制。结合第 31 章和末次完美读取的边界，等号条件与第 24 章的系统幺正参考任务一致。

证明。先说明优化域的有限维归约与最大值存在性。第一共同系统 CPTP 控制的输出可以吸收为自由共同输入，并把第一控制取为恒等。固定余下共同控制表，最终差异的迹范数关于共同输入密度矩阵凸。因此，任意混合输入都有一个纯态分量，其目标不低于混合输入。这里选择的是另一个允许的共同输入，没有对仪器结果作后选择。

活动系统为二维，纯输入的 Schmidt 秩至多为二。参考始终不被操作，故其 Schmidt 支撑可等距压缩到 $\mathbb C^2$，保持所有系统控制及最终迹范数不变；秩一情形补一个零坐标即可。因此全体有限参考的上确界等于参考固定为一个量子比特、共同输入为归一化纯态、第一控制恒等时的上确界。

每个系统 CPTP 映射的 Choi 矩阵满足正半定与固定输出部分迹条件，构成有限维紧集。固定有限 $N$ 的历史树只有有限个控制节点，全部共同控制表属于这些紧集的有限乘积。归一化两比特纯态的单位球面也紧，而有限步输出及其迹范数连续。因此 $T_N^{\mathrm{ref,CPTP}}$ 的最大值在上述有限维域中达到。

若 $\beta_{N-1}=0$ 或存在某个 $\beta_t=1$，定理 22.3 的无参考系统幺正构造已经达到 $U(E,f)$。它属于当前允许类，结合定理 22.2 的参考一致上界，即得等号的充分性。

以下设 $\beta_{N-1}>0$ 且全部 $\beta_t<1$，所以

$$
a>0,\qquad f>0,\qquad s>0,
\qquad 0<\beta_{N-1}<1.
$$

反设某个允许协议达到 $U(E,f)$。按上述归约，可取共同纯输入、参考维数至多二及第一控制恒等。定理 27.2 对低末次错误率允许逐历史把最后的共同 CPTP 控制换成系统幺正，使目标不减。由于所有协议仍受 $U(E,f)$ 上界约束，替换后也达到等号。记最后的共同系统幺正为 $W_h$，此前的系统 CPTP 控制仍完全任意。

对前 $N-1$ 步使用共同受控 Stinespring 纯化，保留控制余系统及仪器的历史副本，仅在分析中使用这些寄存器。物理协议仍将它们丢弃且不重新访问。对每个长度 $N-1$ 的历史 $h$，把末次幺正之前的完整纯化分支记为

$$
|x_h\rangle,|y_h\rangle\in S\otimes R\otimes\mathcal E,
$$

其中 $\mathcal E$ 包含所有分析余系统；不同分支可补齐为同一个有限维空间。令

$$
p_h=\|x_h\|^2,\qquad q_h=\|y_h\|^2,
\qquad \delta_h=\langle y_h,x_h\rangle,
$$

$$
\rho_h^{\rm A}=\operatorname{Tr}_{\mathcal E}|x_h\rangle\langle x_h|,
\qquad
\rho_h^{\rm J}=\operatorname{Tr}_{\mathcal E}|y_h\rangle\langle y_h|.
$$

共同受控等距保持完整内积，每次实际、理想仪器的交叉算子为 $\sum_zP_zK_{t,z}=\sqrt{1-\beta_t}I$。因此

$$
\sum_hp_h=\sum_hq_h=1,
\qquad \sum_h\delta_h=s.
$$

理想过程第一次读取后，每个非零物理分支已成为系统指针与纯参考向量的乘积。后续控制只作用于系统，不能改变该分支的纯参考因子；每次理想读取再把系统投影到秩一指针。所以末次控制之前

$$
\rho_h^{\rm J}=|\eta_h\rangle\langle\eta_h|,
\qquad
\eta_h=|i_h\rangle\otimes r_h,
\qquad i_h=h_{N-1},
$$

允许 $\eta_h=0$。这项纯性来自纯共同输入与理想秩一仪器，不要求中间系统控制幺正。

令

$$
G_h=\|a\rho_h^{\rm A}-\rho_h^{\rm J}\|_1,
\qquad
L_h=\sqrt{(ap_h+q_h)^2-4a|\delta_h|^2},
\qquad \Gamma=\sum_h|\delta_h|.
$$

$L_h$ 是完整纯化上两个加权秩一算子之差的迹范数，因此部分迹收缩给出 $G_h\le L_h$。最后实际读取等于完美读取结果按权重 $a,f$ 保留或翻转；对共同末次幺正和完美读取使用迹范数收缩，再对翻转正项使用三角不等式，得到

$$
\begin{aligned}
2T_N^{\mathrm{ref,CPTP}}
&\le\sum_hG_h+f\\
&\le\sum_hL_h+f\\
&\le\sqrt{(a+1)^2-4a\Gamma^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

第三步的理由是二维实向量 $(L_h,2\sqrt a|\delta_h|)$ 的范数为 $ap_h+q_h$，对这些向量应用欧氏三角不等式；第四步使用 $\Gamma\ge|\sum_h\delta_h|=s$。

在假设的达到情形中，以上每一步都必须取等。因为 $a,s>0$，最后一步强制 $\Gamma=s$。欧氏三角不等式的等号又要求全部非零向量同向，故每个活历史，即 $p_h+q_h>0$ 的历史，都满足

$$
|\delta_h|=\frac{s(ap_h+q_h)}{a+1}>0.
$$

特别地，每个活历史都有 $p_h,q_h>0$。有限项不等式 $G_h\le L_h$ 也必须逐项取等。

下面把这项环境部分迹等号转为物理纯性。固定一个活历史，省略下标。理想物理分支为纯态，故完整理想向量可分解为

$$
y=\eta\otimes e,
\qquad \|e\|=1,
\qquad \|\eta\|^2=q.
$$

把实际向量按同一个环境方向正交分解为

$$
x=\xi_0\otimes e+x_\perp,
\qquad
(I_{SR}\otimes\langle e|)x_\perp=0.
$$

令 $p_0=\|\xi_0\|^2$、$p_1=\|x_\perp\|^2$，则 $p=p_0+p_1$、$\delta=\langle\eta,\xi_0\rangle\ne0$，并有

$$
\rho^{\rm A}=|\xi_0\rangle\langle\xi_0|+\rho_\perp,
\qquad \rho_\perp\ge0,
\qquad \operatorname{tr}\rho_\perp=p_1.
$$

定义

$$
L_0=\sqrt{(ap_0+q)^2-4a|\delta|^2}.
$$

三角不等式给出 $G\le L_0+ap_1$，而直接相减得到

$$
\begin{aligned}
L^2-(L_0+ap_1)^2
&=2ap_1\bigl[ap_0+q-L_0\bigr].
\end{aligned}
$$

因为 $a>0$ 且 $\delta\ne0$，方括号严格为正。如果 $p_1>0$，便有 $G<L$，与逐历史的部分迹等号矛盾。因此 $p_1=0$。恢复下标后，每个活历史都可写为

$$
x_h=\xi_h\otimes e_h,
\qquad y_h=\eta_h\otimes e_h,
\qquad \|e_h\|=1.
$$

于是实际物理分支也纯，并且

$$
\rho_h^{\rm A}=|\xi_h\rangle\langle\xi_h|,
\qquad \delta_h=\langle\eta_h,\xi_h\rangle\ne0.
$$

这没有宣称中间 CPTP 控制可逆；它只是达到假设迫使末次前缀的两候选完整纯化共用同一个环境方向。

接着使用第 24 章证明中的单分支末次严格估计。其准确前提是：实际物理向量 $\xi$ 具有 Schmidt 秩二，理想物理向量为非零 $|i\rangle\otimes r$，二者内积非零，$a,f>0$，末次控制是共同系统幺正。该局部估计不要求更早的控制幺正。下面在当前变量中展开其两种情形，以核对这些前提和结论的对应。

假设某个活历史的 $\xi_h$ 具有 Schmidt 秩二。省略该历史下标，定义

$$
v_j=(\langle j|W\otimes I_R)\xi,
\qquad c_j=|\langle j|W|i\rangle|,
\qquad j=0,1.
$$

则 $v_0,v_1$ 线性无关，且 $c_0^2+c_1^2=1$。定义完美读取比较块及实际最终差块

$$
B_j=a|v_j\rangle\langle v_j|-c_j^2|r\rangle\langle r|,
\qquad
F_j=B_j+f|v_{1-j}\rangle\langle v_{1-j}|.
$$

若 $c_0c_1=0$，交换末次标签后可取 $c_0=1,c_1=0$。令 $p_j=\|v_j\|^2$、$q=\|r\|^2$、$k=|\langle r,v_0\rangle|^2$。Schmidt 秩二给出 $p_1>0$，共同幺正保持内积给出 $k=|\delta_h|^2>0$。完美读取后的范数和为

$$
J=\sqrt{(ap_0+q)^2-4ak}+ap_1.
$$

当前物理加权差块的范数为 $G_h=L_h$，并满足

$$
G_h^2-J^2
=2ap_1\left[ap_0+q-\sqrt{(ap_0+q)^2-4ak}\right]>0.
$$

所以完美读取已经严格收缩，不能取等。

若 $c_0,c_1>0$，参考空间至多二维，而 $v_0,v_1$ 独立，故存在复系数 $\ell,m$，使

$$
r=\ell v_0+mv_1.
$$

这两个展开系数独立于控制幅度 $c_0,c_1$。若 $\ell,m$ 均非零，可选择 $v_0,v_1$ 的代表相位使 $\ell,m>0$；这不改变任何参考投影或比较块。记

$$
A=\|v_0\|^2,\qquad B=\|v_1\|^2,
\qquad C=\langle v_0,v_1\rangle,
\qquad AB-|C|^2>0.
$$

此时

$$
\det B_0=-ac_0^2m^2(AB-|C|^2)<0,
\qquad
\det B_1=-ac_1^2\ell^2(AB-|C|^2)<0.
$$

第 24 章所用的迹范数等号事实是：对可逆不定 Hermitian 矩阵 $D$，若向它加一个非零正秩一算子仍在三角不等式中取等，则该正算子的向量必须属于 $D$ 的正谱子空间。这来自迹范数的 Hermitian 对偶收缩算子；可逆性使取到 $D$ 范数的算子唯一为 $\operatorname{sign}(D)$。

若两个 $F_j$ 的正噪声三角不等式都取等，就必须有

$$
B_0v_1=\lambda_0v_1,\qquad
B_1v_0=\lambda_1v_0,
\qquad \lambda_0,\lambda_1>0.
$$

在独立基 $v_0,v_1$ 中比较系数，得到

$$
\lambda_0=-c_0^2m(\ell C+mB),
\qquad
\lambda_1=-c_1^2\ell(\ell A+m\overline C).
$$

两式的实正性迫使 $C$ 为实数，且

$$
C\le-\frac m\ell B,
\qquad C\le-\frac\ell m A.
$$

这推出 $|C|^2\ge AB$，与向量独立性矛盾。

若 $\ell=0$，则 $r=mv_1$ 且 $m\ne0$。此时 $B_0$ 可逆不定，而

$$
B_0v_1=aCv_0-c_0^2|m|^2Bv_1.
$$

让 $v_1$ 成为它的正特征向量，先要求 $C=0$，随后又得到负特征值 $-c_0^2|m|^2B$，矛盾。$m=0$ 的情形对 $B_1,v_0$ 对称。由于 $r\ne0$，两系数不会同时为零。因此 $c_0,c_1>0$ 时至少一个正噪声三角不等式严格。

两种控制情形都给出

$$
\sum_j\|F_j\|_1<G_h+fp_h.
$$

这会使总目标严格小于 $U(E,f)$，与达到假设矛盾。因此，所有活历史中的实际纯物理向量都只能具有 Schmidt 秩一，即可以写成

$$
\xi_h=x_h^{S}\otimes r_h^{\rm A},
\qquad
\eta_h=y_h^{S}\otimes r_h^{\rm J},
$$

其中理想系统因子 $y_h^S$ 沿指针 $|i_h\rangle$。这里参考因子 $r_h^{\rm A},r_h^{\rm J}$ 可以不同。

最后处理这些纯乘积分支。对共同末次幺正后的假想完美读取，定义纯参考向量

$$
u_{h,j}=\langle j|W_hx_h^S\rangle r_h^{\rm A},
\qquad
v_{h,j}=\langle j|W_hy_h^S\rangle r_h^{\rm J}.
$$

以 $k=(h,j)$ 简记最终经典坐标，并令

$$
P_k=\|u_k\|^2,\qquad Q_k=\|v_k\|^2,
\qquad \gamma_k=\langle v_k,u_k\rangle.
$$

由于前缀的环境方向已逐历史相同，并且末次幺正与完美读取保持内积总和，

$$
\sum_kP_k=\sum_kQ_k=1,
\qquad
\sum_k\gamma_k=\sum_h\delta_h=s.
$$

记

$$
D_k=a|u_k\rangle\langle u_k|-|v_k\rangle\langle v_k|,
\qquad
\ell_k=\|D_k\|_1
=\sqrt{(aP_k+Q_k)^2-4a|\gamma_k|^2}.
$$

实际最终差块为 $D_{h,j}+f|u_{h,1-j}\rangle\langle u_{h,1-j}|$。对最终坐标重复正噪声三角不等式、欧氏三角不等式及复数三角不等式，得到

$$
\begin{aligned}
2T_N^{\mathrm{ref,CPTP}}
&\le\sum_k\ell_k+f\\
&\le\sqrt{(a+1)^2-4a\left(\sum_k|\gamma_k|\right)^2}+f\\
&\le\sqrt{(a+1)^2-4as^2}+f=2U(E,f).
\end{aligned}
$$

达到假设再次强制全部等号。因而每个活坐标 $P_k+Q_k>0$ 都满足

$$
|\gamma_k|=\frac{s(aP_k+Q_k)}{a+1}>0.
$$

所以 $P_k>0$ 当且仅当 $Q_k>0$，且活坐标上的两个参考向量内积非零。这是经典坐标的非零质量支撑相同，不要求两参考向量平行。

另一方面，

$$
\sum_k\operatorname{tr}D_k=a-1=-f<0.
$$

因此存在一个坐标 $(h,j)$ 满足 $\operatorname{tr}D_{h,j}<0$。该坐标活跃，故 $u=u_{h,j}$、$v=v_{h,j}$ 都非零，且 $\langle v,u\rangle\ne0$。实际前缀的乘积结构保证 $u_{h,1-j}$ 与 $u$ 平行。

若 $u,v$ 线性无关，则 $D=a|u\rangle\langle u|-|v\rangle\langle v|$ 在二维参考空间上可逆不定。如果 $u_{h,1-j}\ne0$，正噪声三角等号就要求 $u$ 为 $D$ 的正特征向量。然而

$$
Du=a\|u\|^2u-\langle v,u\rangle v
$$

不与 $u$ 平行，因为内积非零且 $u,v$ 独立，矛盾。若 $u,v$ 平行，负迹条件使 $D$ 成为非零负半定秩一算子；任何沿同方向的非零正噪声都会使标量三角不等式严格。因此两种情形都要求

$$
u_{h,1-j}=0.
$$

非零质量支撑相同再给出 $v_{h,1-j}=0$。选中坐标的两参考向量均非零，所以共同末次幺正之后的两个系统因子都沿 $|j\rangle$。共同系统幺正可逆，故控制之前的实际系统因子与理想系统因子平行，即实际物理分支的系统支撑为 $P_{i_h}$。

把选中历史写成 $h=g\ell$，其中 $\ell=i_h$ 是倒数第二次结果。令 $\sigma_g^{\rm A}$ 为倒数第二次共同 CPTP 控制之后、该仪器之前的实际物理 $SR$ 分支。其结果算子

$$
K_\ell=\sqrt{1-\beta_{N-1}}\,P_\ell
+\sqrt{\beta_{N-1}}\,P_{1-\ell}
$$

可逆，并满足

$$
\rho_h^{\rm A}=(K_\ell\otimes I_R)
\sigma_g^{\rm A}(K_\ell\otimes I_R).
$$

选中实际分支非零、纯且系统沿 $|\ell\rangle$。只反演这个仪器结果算子，得到

$$
\sigma_g^{\rm A}
=\frac{1}{1-\beta_{N-1}}\rho_h^{\rm A}.
$$

因此该父分支也是纯乘积，系统仍沿同一指针。这一步没有反演或限制此前的 CPTP 控制。

考察兄弟历史 $h'=g(1-\ell)$。实际分支为

$$
\rho_{h'}^{\rm A}
=\frac{\beta_{N-1}}{1-\beta_{N-1}}\rho_h^{\rm A}\ne0,
$$

系统支撑仍为 $P_\ell$。理想兄弟分支如果为零，则其完整纯化与实际分支的内积为零；如果非零，则理想秩一读取使其系统支撑为 $P_{1-\ell}$，同样与实际系统支撑正交。因此无论哪一种情况，都有

$$
\delta_{h'}=\langle y_{h'},x_{h'}\rangle=0.
$$

但实际兄弟分支非零，使 $h'$ 成为活历史，违反前缀等号条件对每个活历史给出的 $|\delta_{h'}|>0$。矛盾。

这排除了当前参数条件下任何达到 $U(E,f)$ 的协议。前面已经证明允许类的最大值存在，故其最优值严格小于 $U(E,f)$。与充分性结合，得到完整低末次错误率等号分类。证毕。

**推论 32.2（全部参数域的 CPTP 等号分类与最小记忆维数）。** 对任意有限 $N\ge2$ 和全部参数 $\beta_t\in[0,1]$，令

$$
f=\beta_N,
\qquad E=1-\prod_{t=1}^{N-1}(1-\beta_t).
$$

在定义 27.1 的系统 CPTP 与惰性参考任务中，完整等号条件为

$$
\begin{aligned}
T_N^{\mathrm{ref,CPTP}}(\boldsymbol\beta)=U(E,f)
\quad\Longleftrightarrow\quad
&\beta_N=0\ \text{或}\ \beta_{N-1}=0\\
&\text{或存在 }t\in\{1,\ldots,N\}\text{ 使 }\beta_t=1.
\end{aligned}
$$

考虑允许任意共同 $SM$ CPTP 控制、额外任意有限维惰性参考 $R$、最终保留 $H_NMR$ 的可操作记忆任务。以达到定理 22.2 的 $U(E,f)$ 为目标，所需非零记忆 $M$ 的最小维数恰为

$$
d_{\min}(\boldsymbol\beta)=
\begin{cases}
1,&\beta_N=0\ \text{或}\ \beta_{N-1}=0\ \text{或某个 }\beta_t=1,\\
2,&\beta_N>0,\ \beta_{N-1}>0\ \text{且全部 }\beta_t<1.
\end{cases}
$$

当 $N=1$ 时，在全部参数域有 $T_1^{\mathrm{ref,CPTP}}(\beta_1)=U(0,\beta_1)=\beta_1$，且 $d_{\min}=1$。这些结论分类的是达到可操作记忆最优值所需的记忆维数，不断言任意中间系统 CPTP 控制与系统幺正控制的一般最优值相等。

证明。$f=0$ 时，定理 22.3 的无参考共同系统幺正构造已经达到 $U(E,0)$，并由定理 22.2 的上界确定等号。$0<f<1/2$ 时应用定理 32.1；$1/2\le f\le1$ 时应用定理 31.2。三个互不重叠的参数范围穷尽 $f\in[0,1]$，给出所述完整等号条件。

当 $\dim M=1$ 时，共同 $SM$ CPTP 控制就是系统 CPTP 控制，任意额外惰性参考与最终输出恰对应 $T_N^{\mathrm{ref,CPTP}}$。因此，在等号条件的补集上，严格不等式排除了维数一的记忆达到 $U$。定理 22.2 用一个初始为 $|0\rangle$ 的可操作记忆量子比特、末次前的一次 SWAP 及此前共同实反馈达到 $U$，不需要额外参考，所以维数二足够。在等号域，定理 22.3 的无参考系统幺正构造已以维数一达到；非零记忆的维数不能小于一。单步值由定理 27.2 与定理 22.2 给出，指针输入以维数一的记忆达到。这证明全部维数结论。证毕。

## 追加锚（新终端）

## 33. 一个经典判别比特达到全部参数域的记忆最优值

**定理 33.1（达到最优值不需要在记忆中保留相干）。** 沿用定义 22.1 的可操作记忆任务及全部参数 $\beta_t\in[0,1]$，令

$$
f=\beta_N,\qquad a=1-f,
\qquad s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad E=1-s^2.
$$

对任意有限 $N\ge1$，存在一个使用二维记忆 $M$、无惰性参考、共同输入为 $|0\rangle_S|0\rangle_M$ 的允许协议，达到

$$
\frac12\|\rho^{\rm A}_{H_NM}-\rho^{\rm J}_{H_NM}\|_1
=U(E,f)
=\frac{f+\sqrt{(a+1)^2-4as^2}}2.
$$

该协议的记忆在一个固定正交基中始终为经典寄存器：在离散模型的每个控制和仪器节点之后，两候选的联合态均可写为

$$
\sum_{m=0}^1\sigma^{\rm A/J}_{H_tS,m}\otimes|m\rangle\langle m|_M,
\qquad \sigma^{\rm A/J}_{H_tS,m}\ge0.
$$

特别地，$M$ 与其余保留系统之间没有纠缠，且不需要保留不同记忆标签之间的相干。前 $N-1$ 次读取完全不操作 $M$；只有末次读取之前，才把一个二结果判别测量的结果写入 $M$，并把 $S$ 重置为 $|0\rangle$。

这里的经典性指上述离散 CPTP 控制模型中的保留寄存器，不是对任意微观连续实现作额外断言。活动系统的前缀态与控制仍属于量子任务；本结论只确定达到该指定二元区分目标所需的记忆性质。

证明。使用定理 22.2 的共同无记忆前缀构造。对每个长度 $N-1$ 的历史 $h$，记末次控制之前的实际、理想未归一化系统态为 $\rho_h^{\rm A},\rho_h^{\rm J}$。该构造使用共同初态 $|0\rangle_S$ 及依赖已存历史的共同实系统控制，并满足

$$
\sum_h\operatorname{tr}\rho_h^{\rm A}
=\sum_h\operatorname{tr}\rho_h^{\rm J}=1,
$$

$$
\sum_h\|D_h\|_1
=\sqrt{(a+1)^2-4as^2},
\qquad D_h=a\rho_h^{\rm A}-\rho_h^{\rm J}.
$$

$N=1$ 时前缀为空，唯一的两个候选系统态均为 $|0\rangle\langle0|$，上述恒等式仍成立。$a=0$、零概率历史及全部端点也已由同一定理覆盖。记忆初态为 $|0\rangle_M$，此前始终不变。

对每个 $h$，令 $\Pi_{h,+}$ 为 Hermitian 矩阵 $D_h$ 的严格正谱投影，并令

$$
\Pi_{h,-}=I_S-\Pi_{h,+}.
$$

零谱统一归入负标签；若某一投影为零，相应测量结果就没有概率。这是一个共同的二结果测量，满足

$$
\operatorname{tr}(\Pi_{h,+}D_h)\ge0,
\qquad
\operatorname{tr}(\Pi_{h,-}D_h)\le0,
$$

$$
\sum_{m\in\{+,-\}}
\left|\operatorname{tr}(\Pi_{h,m}D_h)\right|
=\|D_h\|_1.
$$

两投影可以由已知仪器参数、共同输入、共同前缀控制表和旧历史 $h$ 预先计算；计算它们需要使用两个候选模型，但不需要知道实验实际采用了哪个候选。实际与理想过程调用同一个投影对，不发生按真候选选择控制或后选择。

在既有记忆 $M$ 中固定标签 $|+\rangle_M=|0\rangle_M$、$|-\rangle_M=|1\rangle_M$；这里的正负号只是两个正交经典标签，不表示叠加态。把原来的末次 SWAP 替换为共同 $SM$ CPTP 控制

$$
\mathcal F_h(\omega_{SM})
=\sum_{m\in\{+,-\}}
\operatorname{tr}\!\left[(\Pi_{h,m}\otimes I_M)\omega_{SM}\right]
\bigl(|0\rangle\langle0|_S\otimes|m\rangle\langle m|_M\bigr).
$$

这是先测量、再制备的通道：测量效应非负且总和为 $I_{SM}$，输出是归一化的正交标签态与固定系统态，因此完全正且保持迹。它对整个 $SM$ 输入空间都有定义；现有记忆的旧内容被覆盖。测量结果只写入模型已经允许的 $M$，没有向旧历史追加额外永久标签，也没有保留另一个可访问余系统。

定义未归一化的经典记忆概率

$$
p_{h,m}=\operatorname{tr}(\Pi_{h,m}\rho_h^{\rm A}),
\qquad
q_{h,m}=\operatorname{tr}(\Pi_{h,m}\rho_h^{\rm J}).
$$

末次控制之后，两候选系统都为 $|0\rangle$。因此末次实际结果零、一的联合概率分别为 $ap_{h,m},fp_{h,m}$；末次理想结果零、一的联合概率分别为 $q_{h,m},0$。最终差态在经典坐标 $(h,z_N,m)$ 上对角，其对角元素为

$$
d_{h,0,m}=ap_{h,m}-q_{h,m}
=\operatorname{tr}(\Pi_{h,m}D_h),
\qquad
d_{h,1,m}=fp_{h,m}\ge0.
$$

故最终半迹距离为

$$
\begin{aligned}
\frac12\sum_{h,z,m}|d_{h,z,m}|
&=\frac12\left(\sum_h\|D_h\|_1
+f\sum_{h,m}p_{h,m}\right)\\
&=\frac{\sqrt{(a+1)^2-4as^2}+f}{2}
=U(E,f).
\end{aligned}
$$

前缀中 $M$ 始终为固定 $|0\rangle$，而末次控制的输出在固定 $M$ 基上对角，并且 $S$ 是共同固定纯态。末次仪器只作用于 $S$，于是整个离散协议都满足所述记忆经典性与可分性。两候选最终态也是完全经典的联合分布。

该协议属于定理 22.1 的允许类，所以定理 22.2 的上界仍适用；现在给出的经典记忆构造已经达到它。这证明无需在 $M$ 中保留相干，也能达到全部参数域的记忆最优值。证毕。

**推论 33.2（最小经典记忆大小与最终输出压缩）。** 对上述任务，在共同 $SM$ CPTP 控制允许写入经典记忆的条件下，达到 $U(E,f)$ 所需经典记忆的最少标签数与推论 32.2 的 $d_{\min}$ 相同。$N\ge2$ 时为

$$
d_{\min}^{\rm classical}(\boldsymbol\beta)=
\begin{cases}
1,&\beta_N=0\ \text{或}\ \beta_{N-1}=0\ \text{或某个 }\beta_t=1,\\
2,&\beta_N>0,\ \beta_{N-1}>0\ \text{且全部 }\beta_t<1.
\end{cases}
$$

$N=1$ 时为一。即使允许额外任意有限维惰性参考，这个最少标签数也不改变。

此外，对定理 33.1 的达到协议，末端可以先丢弃全部旧历史 $H_{N-1}$，只保留 $(z_N,m)$，而保持半迹距离 $U(E,f)$。再按固定规则把这四个标签压缩成一个最终判别比特 $B$：

$$
B=\begin{cases}
\mathrm A,&z_N=1\ \text{或}\ (z_N=0,m=+),\\
\mathrm J,&z_N=0,m=-,
\end{cases}
$$

得到的两个二元分布仍有总变差距离 $U(E,f)$。这个最后的输出后处理不改变原任务的构造；它说明已输出信息可以进一步压缩，不向协议新增永久输出寄存器。

证明。一个标签对应 $\dim M=1$，属于推论 32.2 已完整分类的无可操作记忆任务；额外惰性参考也包含在该推论的排除范围内。等号边界使用既有无记忆构造即可，其余参数域必须至少有两个标签。定理 33.1 给出两个经典标签的达到，所以这个下界精确。

对于输出压缩，正负谱标签在所有历史上统一。由前面的差坐标公式，固定 $(z,m)$ 后，各历史的差具有同一符号：

$$
d_{h,0,+}\ge0,
\qquad d_{h,0,-}\le0,
\qquad d_{h,1,+},d_{h,1,-}\ge0.
$$

所以逐 $(z,m)$ 合并历史时没有异号抵消，精确有

$$
\sum_{z,m}\left|\sum_h d_{h,z,m}\right|
=\sum_{h,z,m}|d_{h,z,m}|.
$$

丢弃旧历史因此保持最终迹范数。再将三个非负差坐标合并为标签 $\mathrm A$、唯一非正差坐标作为标签 $\mathrm J$，仍没有异号抵消，同样保持迹范数与总变差距离。零差坐标归入任一标签均不影响结论。

这里压缩的是协议结束后的输出。前缀反馈仍允许读取并使用原模型的完整经典历史 $H_t$；本结论没有把控制器在运行期间的总存储压缩成一个比特。这个经典比特只保留为指定候选模型和权重选择的判别结果，不保留可供任意后续量子操作使用的完整状态。因而，推论 32.2 的最小维数二应理解为需要一个额外可写、可读的二标签寄存器，不能单凭该维数结论推断必须使用相干量子存储。

本构造使用标准二元判别的正负谱测量，以及测量后制备的 CPTP 通道。关于正负谱测量的一般最优性，见 Watrous，*The Theory of Quantum Information*，[第 3 章定理 3.4 及式 (3.16)–(3.18)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)；关于测量后制备与纠缠破坏通道的刻画，见 Horodecki、Shor、Ruskai，[*General Entanglement Breaking Channels*（2003），定理 4](https://arxiv.org/abs/quant-ph/0302031)。Bisio、D’Ariano、Perinotti、Sedlak，[*Memory cost of quantum protocols*（2012），§IV](https://arxiv.org/abs/1112.3853) 把量子辅助维数与经典记忆辅助明确区分，并把经典记忆建模为固定正交基上保持对角的寄存器。其资源任务是实现给定量子策略；这里优化的是指定二元区分值，不要求保留该策略对所有后续用途的完整量子输出。证毕。

## 追加锚（新终端）

## 34. 后揭判别权重与经典存储的两问障碍

**定义 34.1（固定存储之后才揭示权重的二态任务）。** 给定系统 $S=\mathbb C^2$ 上两个已知候选密度算子 $A,J$。实际输入是哪一个候选未知。存储阶段对两个候选使用同一个 CPTP 映射 $\Phi$；权重的两个可能值 $c_1,c_2>0$ 在存储前已知，但最终采用哪一个只在存储结束后揭示，并允许根据揭示的 $c$ 选择最终判别。存储映射不能依赖后来揭示的 $c$。

定义存储前、后的加权判别量

$$
L(c)=\|cA-J\|_1,
\qquad L_\Phi(c)=\|c\Phi(A)-\Phi(J)\|_1.
$$

它们对应先验为 $c/(1+c)$ 与 $1/(1+c)$ 的二态判别；存储后的最优成功概率为

$$
\frac12\left(1+\frac{L_\Phi(c)}{1+c}\right).
$$

有限经典存储指输出在同一固定正交基上对角。它等价于一个有限 POVM $\{E_k\}_{k=1}^m$，满足 $E_k\ge0$、$\sum_kE_k=I$，并具有形式

$$
\Phi(\rho)=\sum_{k=1}^m\operatorname{tr}(E_k\rho)|k\rangle\langle k|.
$$

于是

$$
L_\Phi(c)=\sum_{k=1}^m
\left|\operatorname{tr}\bigl[E_k(cA-J)\bigr]\right|.
$$

这个任务允许最终判别使用全部经典记录和已经揭示的权重；限制只在于存储阶段使用同一个映射。它把权重的揭示时刻作为新假设，不改写前述仪器模型中参数预先给定的约定。

**定理 34.2（两个不同权重排除经典无损存储）。** 在定义 34.1 中，设

$$
A=|u\rangle\langle u|,\qquad
J=|v\rangle\langle v|,
\qquad \|u\|=\|v\|=1,
\qquad 0<|\langle u,v\rangle|<1.
$$

对任意两个不同的正权重 $c_1,c_2$，不存在有限经典存储 $\Phi$ 同时满足

$$
L_\Phi(c_1)=L(c_1),
\qquad L_\Phi(c_2)=L(c_2).
$$

一个量子比特的恒等存储则对全部 $c>0$ 同时保持等号。若最终采用的权重在存储前已经告知存储方，对该权重的一个二元谱测量就能保持等号。

证明。记 $D_c=cA-J$。在 $\operatorname{span}\{u,v\}$ 上直接计算行列式，得到

$$
\det D_c=-c\left(1-|\langle u,v\rangle|^2\right)<0.
$$

所以 $D_c$ 有一个严格正特征值和一个严格负特征值。记其正谱投影为 $P_c$。对于任意效应 $0\le F\le I$，

$$
\operatorname{tr}(FD_c)\le\operatorname{tr}(P_cD_c),
$$

而等号强制 $F=P_c$。事实上，在 $D_c$ 的正交特征基中，达到上界要求 $F$ 的正特征方向对角元为一、负特征方向对角元为零；$F\ge0$ 与 $I-F\ge0$ 随即使非对角元为零。这也给出

$$
\|D_c\|_1
=2\operatorname{tr}(P_cD_c)-\operatorname{tr}D_c.
$$

反设某个有限 POVM 对权重 $c$ 保持范数。把满足 $\operatorname{tr}(E_kD_c)>0$ 的结果集合记为 $S_c$，并令 $F_c=\sum_{k\in S_c}E_k$。则

$$
\sum_k|\operatorname{tr}(E_kD_c)|
=2\operatorname{tr}(F_cD_c)-\operatorname{tr}D_c.
$$

范数等号及最优效应的唯一性因此给出 $F_c=P_c$。迹为零的结果可以放入补集，上式仍精确成立。

若同一个 POVM 对 $c_1,c_2$ 都保持范数，按一个结果是否属于 $S_{c_1}$、$S_{c_2}$ 分成四组。相应四个效应记作 $G_{++},G_{+-},G_{-+},G_{--}$，满足

$$
\begin{aligned}
P_{c_1}&=G_{++}+G_{+-},&
I-P_{c_1}&=G_{-+}+G_{--},\\
P_{c_2}&=G_{++}+G_{-+},&
I-P_{c_2}&=G_{+-}+G_{--}.
\end{aligned}
$$

若 $0\le G\le P$ 且 $P$ 是正交投影，则 $PG=GP=G$；这是因为 $G$ 在 $\ker P$ 上的二次型为零，正性使该子空间包含于 $\ker G$。因此

$$
P_{c_1}P_{c_2}=G_{++}=P_{c_2}P_{c_1}.
$$

两个正谱投影可交换，意味着两个二阶 Hermitian 算子 $D_{c_1},D_{c_2}$ 可交换。然而

$$
[D_{c_1},D_{c_2}]=(c_2-c_1)[A,J]\ne0.
$$

最后的不等号来自 $c_1\ne c_2$ 以及两个不同且非正交的秩一投影不可交换，矛盾。故任何固定有限经典存储至少损失一个权重的判别量。

恒等量子存储保留 $A,J$ 本身，当然保持全部加权差的迹范数。对于存储前已知的最终权重 $c$，使用 $P_c,I-P_c$ 作二元测量，把正、负谱分别记入两个经典结果，所得绝对迹之和恰为 $\|D_c\|_1$。这里两种权重可以各自选择不同的存储测量；定理排除的是同一个经典存储同时无损。证毕。

**命题 34.3（两个后揭权重的精确经典和界）。** 在定义 34.1 中取

$$
A=|0\rangle\langle0|,
\qquad J=|+\rangle\langle+|,
\qquad |+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
\qquad c_1=1,\quad c_2=\frac12.
$$

对任意有限经典存储，两个加权判别量的和满足精确界

$$
\sup_{\Phi\ \mathrm{classical}}
\left[L_\Phi(1)+L_\Phi(1/2)\right]=\frac52.
$$

一个二元投影测量已经达到该上界，而量子比特恒等存储给出

$$
L(1)+L(1/2)=\sqrt2+\frac{\sqrt5}{2}>\frac52.
$$

所以两问之和的经典损失至少为

$$
\frac{2\sqrt2+\sqrt5-5}{2}>0.
$$

这里比较的是陈述中两个加权迹范数的和，不把它称为两个不同先验成功概率的未加权和。

证明。用计算基写出

$$
D_1=\begin{pmatrix}1/2&-1/2\\-1/2&-1/2\end{pmatrix},
\qquad
D_{1/2}=\begin{pmatrix}0&-1/2\\-1/2&-1/2\end{pmatrix}.
$$

令

$$
B=D_1+D_{1/2}
=\begin{pmatrix}1/2&-1\\-1&-1\end{pmatrix},
\qquad
D_1-D_{1/2}=\frac12 A,
$$

并取

$$
Y=\begin{pmatrix}11/10&1/5\\1/5&7/5\end{pmatrix}.
$$

$B$ 的特征值为 $1,-3/2$。直接相乘有 $Y^2=B^2$，且 $Y$ 正定，因此 $Y=|B|$，特别地 $Y\ge B$、$Y\ge-B$。此外

$$
Y-\frac12A
=\begin{pmatrix}3/5&1/5\\1/5&7/5\end{pmatrix}>0,
$$

因为两个对角元为正、行列式为 $4/5>0$。由此也有 $Y\ge-\frac12A$。四种符号组合因此统一满足

$$
Y\ge sD_1+tD_{1/2},\qquad s,t\in\{-1,1\}.
$$

固定任意经典存储的 POVM $\{E_k\}$，对每个结果按两个实数 $\operatorname{tr}(E_kD_1)$、$\operatorname{tr}(E_kD_{1/2})$ 的符号选择 $s_k,t_k$；零值任取符号。正性给出

$$
\begin{aligned}
L_\Phi(1)+L_\Phi(1/2)
&=\sum_k\operatorname{tr}\bigl[E_k(s_kD_1+t_kD_{1/2})\bigr]\\
&\le\sum_k\operatorname{tr}(E_kY)
=\operatorname{tr}Y=\frac52.
\end{aligned}
$$

这个上界与经典结果的数量无关。取二元测量

$$
E_+=\frac15\begin{pmatrix}4&-2\\-2&1\end{pmatrix},
\qquad E_-=I-E_+.
$$

$E_+$ 是向量 $(2|0\rangle-|1\rangle)/\sqrt5$ 的秩一投影。四个输出差为

$$
\begin{aligned}
\operatorname{tr}(E_+D_1)&=\frac7{10},&
\operatorname{tr}(E_-D_1)&=-\frac7{10},\\
\operatorname{tr}(E_+D_{1/2})&=\frac3{10},&
\operatorname{tr}(E_-D_{1/2})&=-\frac45.
\end{aligned}
$$

故该测量分别得到 $7/5$ 与 $11/10$，两者之和正是 $5/2$，证明经典界的达到性。

两个加权秩一差的迹范数公式给出

$$
L(c)=\sqrt{(1+c)^2-2c}=\sqrt{1+c^2},
$$

于是量子恒等存储的两问之和为 $\sqrt2+\sqrt5/2$。为验证严格比较，$2\sqrt2>14/5$ 来自 $2>49/25$，而 $\sqrt5>11/5$ 来自 $5>121/25$；两式相加得 $2\sqrt2+\sqrt5>5$。这同时证明正损失的陈述。证毕。

## 追加锚（新终端）

## 35. 两种后揭权重的全参数经典最优值与三结果测量

**定理 35.1（两个后揭权重的有限候选精确公式）。** 沿用定义 34.1 的固定存储任务，设两个候选是不同且非正交的纯量子比特态。记

$$
r=|\langle u,v\rangle|^2\in(0,1),
\qquad c_1,c_2>0,\quad c_1\ne c_2,
$$

$$
C=c_1+c_2,\qquad t=|c_1-c_2|,\qquad 0<t<C,
\qquad \nu=1-r.
$$

共同酉变换和向量代表相位允许取

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},
\qquad
J=\begin{pmatrix}r&\sqrt{r\nu}\\\sqrt{r\nu}&\nu\end{pmatrix}.
$$

定义

$$
B=CA-2J,
\qquad q=\|B\|_1=\sqrt{(C+2)^2-8Cr},
$$

并记所有有限经典存储上的最优和为

$$
V(C,t,r)=\sup_{\Phi\ \mathrm{classical}}
\bigl[L_\Phi(c_1)+L_\Phi(c_2)\bigr].
$$

第一参数域有简单精确公式：

$$
t\le\frac{Cq}{C+2}
\quad\Longrightarrow\quad V(C,t,r)=q.
$$

此时测量 $B$ 的正负谱投影即可达到。对其余参数域，以下三个显式矩阵给出完整精确公式。令

$$
Y_+=\frac{B+tA+|B-tA|}{2},
\qquad
Y_-=\frac{-B+tA+|B+tA|}{2}.
$$

再令

$$
k=\sqrt{\frac r\nu},
\qquad h=\sqrt{\frac{C^2-t^2}{2C\nu}},
\qquad w=k-h,
\qquad y=\frac{2C\nu}{t},
$$

$$
Y_3=\begin{pmatrix}t+yw^2&yw\\yw&y\end{pmatrix},
\qquad
R_3=\operatorname{tr}Y_3
=\frac{C(C+2)-2\sqrt{2Cr(C^2-t^2)}}{t}.
$$

定义候选值

$$
R_+=\begin{cases}
\operatorname{tr}Y_+,&Y_++B\ge0,\\
+\infty,&\text{否则},
\end{cases}
\qquad
R_-=\begin{cases}
\operatorname{tr}Y_-,&Y_--B\ge0,\\
+\infty,&\text{否则}.
\end{cases}
$$

则在 $t>Cq/(C+2)$ 时，

$$
\boxed{V(C,t,r)=\min\{R_+,R_-,R_3\}.}
$$

这里的可行性检验只是两个显式二阶 Hermitian 矩阵的半正定检验，等价于其迹与行列式均非负，不含连续优化。全部矩阵绝对值也可直接写成根式：对 $\lambda>0$，

$$
Q_\lambda=\sqrt{(\lambda+2)^2-8\lambda r},
$$

$$
|\lambda A-2J|
=\frac{(\lambda-2)(\lambda A-2J)+4\lambda\nu I}{Q_\lambda}.
$$

特别地，若 $c_{\rm hi}=(C+t)/2$、$c_{\rm lo}=(C-t)/2$，两个二结果候选矩阵的迹为（是否保留仍由上述可行性检验决定）

$$
\operatorname{tr}Y_+=c_{\rm hi}-1+L(c_{\rm lo}),
\qquad
\operatorname{tr}Y_-=1-c_{\rm lo}+L(c_{\rm hi}),
$$

$$
L(c)=\sqrt{(1+c)^2-4cr}.
$$

证明。不妨交换权重使 $c_1>c_2$。对任一 POVM 结果，两个带符号的迹之差是 $t\operatorname{tr}(E A)\ge0$。把原来的四种符号组合归并后，目标可以等价写成三结果优化

$$
\max_{E_+,E_-,E_0\ge0\,,\ E_++E_-+E_0=I}
\operatorname{tr}(E_+B)-\operatorname{tr}(E_-B)
+t\operatorname{tr}(E_0A).
$$

其理由也可不依赖零迹的符号约定：对每个原结果，两个绝对值之和等于对 $B,-B,tA,-tA$ 四种系数矩阵取最大迹；$tA\ge-tA$ 使第四项冗余。选择一个达到最大值的标签并合并同标签结果，得到三结果 POVM。反过来，对任一三结果 POVM，原绝对值目标至少为所示线性目标，故两个最优值相等。结果为零时任取一个达到最大值的标签即可。

这个三结果优化的对偶为

$$
\min\operatorname{tr}Y,
\qquad Y\ge B,\quad Y\ge-B,\quad Y\ge tA.
$$

原问题的可行集紧，且 $E_+=E_-=E_0=I/3$ 严格可行；对偶取足够大的正数乘 $I$ 也严格可行。因此 Slater 强对偶成立，两边最优值都达到。所有系数矩阵都为实矩阵，对任一可行矩阵及其复共轭取平均，保持可行性和目标，所以原、对偶最优解都可取实对称。对最优解有互补松弛

$$
(Y-B)E_+=0,
\qquad (Y+B)E_-=0,
\qquad (Y-tA)E_0=0.
$$

先考虑仅有前两项约束时的唯一最小迹解 $Y_0=|B|$，其迹为 $q$。$B$ 的行列式是 $-2C\nu<0$，故 $|B|$ 正定。由二阶矩阵绝对值公式，

$$
\langle u,|B|^{-1}u\rangle=\frac{C+2}{Cq}.
$$

令 $z_0=|B|^{-1/2}u$。对正定矩阵作合同变换，$|B|\ge tA$ 等价于

$$
I\ge t|z_0\rangle\langle z_0|,
$$

也就是 $t(C+2)/(Cq)\le1$。这证明 $Y_0$ 的可行域恰为所列第一参数域。测量 $B$ 的谱投影使两个结果上的 $B$ 迹绝对值之和为 $q$；原目标逐结果不小于该和，而可行 $Y_0$ 又给出上界 $q$，所以这一测量达到原目标 $q$。

以下证明剩余候选穷尽最优值。对任意可行 $Y$，三个差矩阵 $Y-B,Y+B,Y-tA$ 都不可能为零：前两种会要求不定矩阵 $B$ 或 $-B$ 半正定；第三种会要求 $tA\ge-B$，但在 $u^\perp$ 上左端为零、右端二次型为 $2\nu>0$。因此，每个奇异差矩阵都恰为秩一。

一个最优 POVM 不可能只有一个非零效应，否则该效应为 $I$，互补松弛会迫使对应差矩阵为零。若它恰有两个非零效应，互补松弛使它们的秩均至多为一；两个非零正秩一矩阵相加为 $I$，必为一对互补正交投影。它们于是达到相应两个系数矩阵的二元最优值。

对任意这里出现的二矩阵 $X_i,X_j$，差 $X_i-X_j$ 均可逆不定。二元最优效应是该差的唯一正谱投影，相应唯一最小迹上界是

$$
Y_{ij}=\frac{X_i+X_j+|X_i-X_j|}{2}.
$$

唯一性也由互补松弛直接得到：两个互补谱投影已固定，等式 $Y E_i=X_iE_i$、$Y E_j=X_jE_j$ 唯一确定 $Y$。所以两结果情形只能产生 $Y_0,Y_+,Y_-$ 中的一个；它还必须满足第三项约束。$Y_+$ 和 $Y_-$ 的剩余约束正是陈述中的两个可行性检验。

若最优 POVM 的三个效应均非零，则三个差矩阵都必须奇异。写

$$
Y=\begin{pmatrix}x&z\\z&y\end{pmatrix}.
$$

对 $\det(Y-B)=\det(Y+B)=\det(Y-tA)=0$ 展开，有

$$
\det Y=2C\nu,
\qquad y=\frac{2C\nu}{t},
\qquad x=t+\frac{z^2}{y}.
$$

剩下的线性混合项等式是

$$
y(C-2r)-2\nu x+4\sqrt{r\nu}\,z=0.
$$

令 $w=z/y$，化简得到

$$
(w-k)^2=h^2.
$$

所以两个三重接触候选分别为 $w=k-h$ 和 $w=k+h$。它们都可行：$Y-tA=y(w,1)^{\mathsf T}(w,1)$ 半正定，而 $Y-B,Y+B$ 的行列式均为零，右下角分别为

$$
2\nu\left(\frac Ct+1\right)>0,
\qquad
2\nu\left(\frac Ct-1\right)>0.
$$

二者因此都是半正定矩阵。由于 $k,h>0$，$w=k-h$ 的迹严格小于 $w=k+h$ 的迹，故高迹候选不可能最优；低迹候选就是 $Y_3$。

这样，至少一个最优解属于所列有限候选集合，而集合中的每个保留候选都可行。在第二参数域 $Y_0$ 已不可行，故精确最优值就是三个剩余候选迹的最小值。矩阵绝对值公式来自两个异号特征值上的线性插值；代入 $\lambda=C,C-t,C+t$ 即得陈述中的全部根式。证毕。

**命题 35.2（达到测量及三结果必要的参数例）。** 定理 35.1 中，若最小值由可行的 $Y_+$ 达到，测量 $B-tA=2(c_{\rm lo}A-J)$ 的正负谱投影即可达到；若由 $Y_-$ 达到，测量 $B+tA=2(c_{\rm hi}A-J)$ 的正负谱投影即可达到。

若 $Y_3$ 最优，其三结果达到测量可以显式写出。对二阶矩阵记 $\operatorname{adj}$ 为伴随矩阵，令

$$
S_\alpha=\frac{k}{yh},
\qquad d_\alpha=\frac{w}{2\nu h},
\qquad
\alpha_0=\frac{2Ck-h(C+2)}{2\nu ht},
$$

$$
\alpha_+=\frac{S_\alpha-\alpha_0-d_\alpha}{2},
\qquad
\alpha_-=\frac{S_\alpha-\alpha_0+d_\alpha}{2}.
$$

则

$$
E_+=\alpha_+\operatorname{adj}(Y_3-B),
\quad
E_-=\alpha_-\operatorname{adj}(Y_3+B),
\quad
E_0=\alpha_0\operatorname{adj}(Y_3-tA)
$$

是达到测量。当 $Y_3$ 最优时，这三个系数必非负；若只把 $Y_3$ 当作可行上界，不能省略这项非负性要求。特别地，$\alpha_0\ge0$ 恰好对应 $t\ge Cq/(C+2)$，但这一个条件本身不保证其余两个系数非负。

取

$$
C=2,\qquad t=1,\qquad r=\frac9{10},
$$

即权重为 $3/2,1/2$，则精确最优值是

$$
V=8-\frac{6\sqrt{30}}5.
$$

三个系数恰为

$$
\alpha_0=4\sqrt{30}-20,
\qquad
\alpha_+=\frac{25}{2}-\frac{9\sqrt{30}}4,
\qquad
\alpha_-=\frac{15}{2}-\frac{5\sqrt{30}}4,
$$

均严格为正。这个例子的最优经典测量需要至少三个非零结果；两个结果不能达到最优值。

证明。二结果候选的测量达到对应两项线性目标；第三项对偶约束已经验证可行，所以原绝对值目标也必须等于该候选迹。

对三结果式，三个伴随矩阵都是非零正秩一矩阵，分别支撑于对应差矩阵的核。把 $E_++E_-+E_0=I$ 的三个实矩阵坐标展开，得到唯一解

$$
\alpha_++\alpha_-+\alpha_0=\frac{k}{yh},
\qquad
\alpha_--\alpha_+=\frac{w}{2\nu h},
\qquad
\alpha_0=\frac{2Ck-h(C+2)}{2\nu ht}.
$$

这里 $k,y,h,\nu,t$ 全部为正。更明确地，把三个伴随矩阵依次按 $(11,12,22)$ 坐标写成三列，其行列式为

$$
-4t\nu yh=-8C\nu^2h\ne0,
$$

所以解确实唯一。若系数非负，这些效应组成 POVM 并逐项满足互补松弛，直接给出目标 $\operatorname{tr}Y_3$。反过来，若 $Y_3$ 最优，强对偶保证存在最优 POVM；其每项都支撑于相应一维核，只能是所写伴随矩阵的非负倍数。唯一性迫使其系数正是上述公式。这证明最优时的非负性与达到构造。

$\alpha_0$ 的阈值关系通过对 $h\le2Ck/(C+2)$ 平方并代入定义得到。具体例中，$5<\sqrt{30}<50/9<6$，所以三个系数都严格为正；代入 $R_3$ 得到所示精确值。该正系数 POVM 已达到可行对偶值，因而最优。任何其他最优 POVM 按三种系数矩阵分组后，都必须满足同一组互补松弛与完整性方程，因此三个组的系数也都是上述严格正数。只有两个非零原结果的测量至多产生两个非空组，不能满足这一要求。这证明三结果的必要性。

所用任意 Hermitian 测量奖励的 POVM 优化及其对偶，见 Watrous，*The Theory of Quantum Information*，[§3.1.2，式 (3.33)–(3.42)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)；同书定理 1.18 与命题 1.19 给出本证明所用的严格可行性、强对偶及互补松弛。这里的有限候选公式针对两种已知可能权重、存储后才揭示实际选择的任务，不把最终采用的权重在存储前已知时的单个 Helstrom 测量等同于对两问同时最优。

同一任务也可写成测量后揭示信息的二态辨别。令子系综标签为 $i=1,2$，其概率为 $\pi_i=(1+c_i)/(C+2)$，标签内部的 $A,J$ 先验分别为 $c_i/(1+c_i)$ 与 $1/(1+c_i)$。只在经典存储结束后揭示 $i$，则该存储及随后最优猜测的平均成功概率恰为

$$
p_{\rm guess}^{\Phi}
=\frac12+\frac{L_\Phi(c_1)+L_\Phi(c_2)}{2(C+2)}.
$$

因此本节优化与这个系综的后信息辨别只差固定正仿射变换。该一般框架见 Carmeli、Heinosaari、Toigo，[*State discrimination with post-measurement information and incompatibility of quantum measurements*（2018），§II.1、定理 1–2](https://arxiv.org/abs/1804.09693)。其定理 1 将事前与事后揭示信息时的最优值相同，刻画为存在兼容的各子系综最优测量；两个候选密度算子可以在不同子系综中重复出现，子系综标签仍互不混淆。这里的权重归一化与该映射明确保留了信息揭示的时点。证毕。

## 追加锚（新终端）

## 36. 任意有限个后揭权重的三标签经典最优存储

**定理 36.1（有限权重表的三结果达到界）。** 沿用定义 34.1 的固定存储任务。允许 $A,J$ 为任意两个量子比特密度矩阵，即

$$
A,J\in\mathbb C^{2\times2},\qquad A,J\ge0,
\qquad \operatorname{tr}A=\operatorname{tr}J=1,
$$

并预先给定任意有限个正权重

$$
m\ge1,\qquad 0<c_1<c_2<\cdots<c_m.
$$

共同存储通道可以依赖 $A,J$ 和整个权重表，但必须在实际权重揭示前固定。对任意有限经典输出通道 $\Phi$，记

$$
L_\Phi(c)=\|c\Phi(A)-\Phi(J)\|_1,
\qquad
V_m=\sup_{\Phi\ \mathrm{classical}}\sum_{j=1}^m L_\Phi(c_j).
$$

这里优化的是所写范数之和；把某个权重的读数换算为定义 34.1 的判别成功率时，仍须使用该权重对应的 $1+c_j$ 分母。

对 $k=0,\ldots,m$ 定义 Hermitian 奖励矩阵

$$
G_k=
\left(\sum_{j=k+1}^m c_j-\sum_{j=1}^k c_j\right)A
+(2k-m)J,
$$

其中空和为零。则

$$
\boxed{
V_m=
\max_{\substack{E_0,\ldots,E_m\ge0\\\sum_{k=0}^m E_k=I}}
\sum_{k=0}^m\operatorname{tr}(E_kG_k)
=\min_{\substack{Y=Y^\dagger\\Y\ge G_k\ (0\le k\le m)}}
\operatorname{tr}Y.
}
$$

两个最优值均达到，并且存在一组达到原范数总分 $V_m$ 的 POVM，其非零效应数至多为

$$
\boxed{\min\{m+1,3\}.}
$$

因此，无论这张有限权重表有多少项，最优经典存储总能只保留至多三个输出标签。权重揭示后再根据存储标签作相应的二元决策。

证明。先核对从任意结果数到有限奖励表的归约。对一个任意 POVM 效应 $E\ge0$，令

$$
a=\operatorname{tr}(EA)\ge0,\qquad
b=\operatorname{tr}(EJ)\ge0.
$$

序列 $c_ja-b$ 随 $j$ 不减。因此可以选择一个 $k\in\{0,\ldots,m\}$，使 $j\le k$ 时 $c_ja-b\le0$，$j>k$ 时 $c_ja-b\ge0$。零值可以置于分界的任一侧；若 $a=0$，取 $k=m$ 即可，不需除以 $a$。于是

$$
\sum_{j=1}^m|c_ja-b|
=-\sum_{j=1}^k(c_ja-b)+\sum_{j=k+1}^m(c_ja-b)
=\operatorname{tr}(EG_k).
$$

任何其他分界给出的带符号和都不超过绝对值之和，所以逐效应恒有

$$
\sum_{j=1}^m\bigl|\operatorname{tr}(E(c_jA-J))\bigr|
=\max_{0\le k\le m}\operatorname{tr}(EG_k).
$$

给定任意有限 POVM $(M_\ell)_\ell$，为每个结果选择一个达到上述最大值的标签 $k(\ell)$，然后令

$$
E_k=\sum_{\ell:\,k(\ell)=k}M_\ell.
$$

这些效应组成 $m+1$ 标签的 POVM，其线性奖励恰等于原 POVM 的范数总分。因此，原问题在任意有限结果数上的上确界不超过所列线性奖励最大值。反过来，对任一这样的 $(E_k)$，逐效应的绝对值之和都不小于所选择的第 $k$ 项奖励，故其原范数总分不小于线性奖励。这给出反向不等式，两个最优值相等。

线性奖励的可行集是有限维紧集：各 $E_k$ 满足 $0\le E_k\le I$，完整性与正性条件均闭。连续目标因而达到最大值。其半正定对偶就是陈述中的 $Y\ge G_k$；原问题取 $E_k=I/(m+1)$ 严格可行，对偶取足够大的正数乘 $I$ 也严格可行。Slater 强对偶给出两者值相等及对偶最优值达到。

现在证明三个非零效应足够。先用共同酉变换将 $A$ 对角化，再施加保持 $A$ 对角的对角相位变换，使 $J$ 的非对角元变为实数；若该元为零，则无需第二步。即使 $A$ 简并，这个操作也成立。因此 $A,J$ 及全部 $G_k$ 都可取实对称矩阵。对一个最优 POVM 的每项作

$$
E_k\longmapsto\frac{E_k+\overline{E_k}}2,
$$

正性与完整性保持。由于 $G_k$ 实对称，$\operatorname{tr}(E_kG_k)$ 也保持，所以存在实对称最优 POVM。

记其非零效应的指标集为 $\mathcal I$。实对称二阶矩阵构成三维实向量空间。若 $|\mathcal I|>3$，则存在不全为零的实数 $(a_k)_{k\in\mathcal I}$，使

$$
\sum_{k\in\mathcal I}a_kE_k=0.
$$

每个非零正效应的迹严格为正。对该等式取迹可知，系数 $a_k$ 必须既有正数也有负数。把系数在 $\mathcal I$ 外延拓为零，并选择

$$
0<\varepsilon<\frac1{\max_{k\in\mathcal I}|a_k|}.
$$

则两组

$$
E_k^{\pm}=(1\pm\varepsilon a_k)E_k
$$

都为合法 POVM。令

$$
\Delta=\sum_{k\in\mathcal I}a_k\operatorname{tr}(E_kG_k).
$$

两组线性奖励分别为 $V_m+\varepsilon\Delta$ 与 $V_m-\varepsilon\Delta$。最优性要求两者都不超过 $V_m$，故 $\Delta=0$。

沿同一方向走到

$$
s_* =\min_{k:\,a_k<0}\frac{-1}{a_k}>0,
\qquad
\widetilde E_k=(1+s_*a_k)E_k.
$$

此时全部系数 $1+s_*a_k$ 非负，至少一个原非零效应变为零；矩阵和仍为 $I$，奖励仍为 $V_m+s_*\Delta=V_m$。这一步不要求效应为秩一。每次至少消去一个非零效应，有限次重复后便得到至多三个非零效应的最优奖励 POVM。

最后把这组 POVM 用作经典存储。其原范数总分不小于 $V_m$，又由 $V_m$ 的定义不大于 $V_m$，所以原目标也达到。删去零效应后，通道可写为

$$
\Phi_*(\rho)=\sum_{\ell=1}^{n_*}
\operatorname{tr}(E_\ell^*\rho)|\ell\rangle\langle\ell|,
\qquad n_*\le\min\{m+1,3\}.
$$

所用线性依赖扰动是标准 POVM 极点方法，见 D'Ariano、Lo Presti 与 Perinotti，*Classical randomness in quantum measurements*，[推论 7 及其证明](https://arxiv.org/abs/quant-ph/0408115)。实对称空间的 $d(d+1)/2$ 维数界也用于实态系综的可访问信息优化，见 Sasaki 等，*Accessible information and optimal strategies for real symmetrical quantum sources*，[引理 5](https://arxiv.org/abs/quant-ph/9812062)；该文研究的是 Shannon 互信息，上面的奖励归约与保值消去步骤直接处理本节的范数总分。证毕。

**推论 36.2（三标签统一界的锐性与纯态量子差距）。** 对定理 36.1 的全部候选对与有限权重表，统一的三标签上界不能改成两个。进一步，若

$$
A=|u\rangle\langle u|,\qquad J=|v\rangle\langle v|,
\qquad \|u\|=\|v\|=1,
\qquad 0<|\langle u,v\rangle|^2<1,
$$

且 $m\ge2$，则仍有严格差距

$$
V_m<\sum_{j=1}^m\|c_jA-J\|_1.
$$

证明。命题 35.2 中

$$
m=2,\qquad c_1=\frac12,\quad c_2=\frac32,
\qquad |\langle u,v\rangle|^2=\frac9{10}
$$

的最优经典总分为 $8-6\sqrt{30}/5$，且任一达到测量都至少有三个非零结果。它属于本节任务，故排除了对全部有限权重表适用的二标签上界。

对于所述纯态候选的严格差距，经典测量的迹范数收缩性逐项给出

$$
L_\Phi(c_j)\le\|c_jA-J\|_1.
$$

若总和取等，定理 36.1 保证存在达到该总和的有限经典存储，且每一项都必须取等。任选两个不同权重即与定理 34.2 矛盾。因此总和严格小于量子原值。恒等量子存储则同时保留右端各项。

这里的三标签计数只针对这一次固定存储后留下的经典输出，保证给定权重表上的最佳经典总分。所用测量可以随权重表改变；结论既不要求保留各个权重的量子最优值，也不给此前多阶段仪器、控制器运行存储或完整历史档案设定三标签上界。证毕。

## 追加锚（新终端）

## 37. 混合量子比特后揭权重的同时无损分类

**定理 37.1（有限权重表的逐项无损条件）。** 沿用第 36 节的固定存储任务，设 $A,J$ 为任意两个量子比特密度矩阵，且

$$
m\ge1,\qquad 0<c_1<\cdots<c_m.
$$

记

$$
D_c=cA-J,\qquad
L(c)=\|D_c\|_1,\qquad
L_\Phi(c)=\|\Phi(D_c)\|_1,
$$

并定义不定权重集合及其大小

$$
\mathcal I=\{c_j:\det D_{c_j}<0\},\qquad n=|\mathcal I|.
$$

这里“不定”表示 $D_c$ 有一个严格正特征值和一个严格负特征值。行列式为零的权重不计入 $\mathcal I$。

存在同一个有限经典存储 $\Phi$，使

$$
L_\Phi(c_j)=L(c_j)\qquad(j=1,\ldots,m),
$$

当且仅当

$$
\boxed{[A,J]=0\quad\text{或}\quad n\le1.}
$$

证明。先处理不在 $\mathcal I$ 中的权重。二阶 Hermitian 矩阵的特征值为实数，行列式非负意味着它们同号或至少一个为零。因此 $D_c$ 半正定或半负定，且

$$
\|D_c\|_1=|\operatorname{tr}D_c|=|c-1|.
$$

任意 CPTP 映射都保持半定性与迹，故对这样的权重，任意存储自动满足

$$
\|\Phi(D_c)\|_1=|c-1|=\|D_c\|_1.
$$

特别地，$\det D_c=0$ 的端点不产生额外限制。若 $n=0$，只有一个效应 $I$ 的测量已经逐项无损；若 $n=1$，测量唯一不定矩阵的正、负谱投影即可，其他权重的等号自动保持。若 $[A,J]=0$，则共同本征基上的二元投影测量保持所有 $D_c$ 的谱读数，因而同时保持任意正权重的迹范数。这证明充分性。

下面证明必要性。设 $D_c$ 不定，写为

$$
D_c=\lambda_+P_c-\lambda_-(I-P_c),\qquad
\lambda_+,\lambda_->0,
$$

其中 $P_c$ 是秩一正谱投影。对任意效应 $E\ge0$，令

$$
x_E=\lambda_+\operatorname{tr}(EP_c),\qquad
y_E=\lambda_-\operatorname{tr}(E(I-P_c)).
$$

两者非负，所以 $|x_E-y_E|\le x_E+y_E$，等号当且仅当至少一项为零。若一个有限 POVM $(E_\ell)_\ell$ 保持 $\|D_c\|_1$，则

$$
\sum_\ell|x_{E_\ell}-y_{E_\ell}|
=\lambda_++\lambda_-
=\sum_\ell(x_{E_\ell}+y_{E_\ell}).
$$

每项的损失非负，总损失为零强制逐项取等。由正性，$\operatorname{tr}(EP)=0$ 对秩一投影 $P$ 意味着 $E$ 消去 $\operatorname{ran}P$：若 $P=|v\rangle\langle v|$，则 $\langle v,Ev\rangle=\|E^{1/2}v\|^2=0$。因此每个非零效应必为下列两种形式之一：

$$
E_\ell=\alpha_\ell P_c\quad\text{或}\quad
E_\ell=\beta_\ell(I-P_c),\qquad
\alpha_\ell,\beta_\ell>0.
$$

也就是说，不定权重的范数等号要求存储测量细分其唯一的二元谱测量。

若同一个 POVM 也对另一个不定权重 $d\ne c$ 保持等号，那么每个非零效应还必须为 $P_d$ 或 $I-P_d$ 的正倍数。取任意一个非零效应，比较其一维值域可知

$$
P_d=P_c\quad\text{或}\quad P_d=I-P_c.
$$

两个谱投影可交换，故 $D_c,D_d$ 可交换。但直接展开有

$$
[D_c,D_d]=(d-c)[A,J].
$$

由于 $d\ne c$，这要求 $[A,J]=0$。所以非对易候选对只要有两个不同的不定权重，就不存在逐项无损的有限经典存储。证毕。

**推论 37.2（最少输出资源及经典总分的等号条件）。** 对定理 37.1 的任务，最少非零经典输出标签数为

$$
\begin{cases}
1,&n=0,\\
2,&n\ge1\ \text{且}\ ([A,J]=0\ \text{或}\ n=1),\\
\text{不存在有限经典实现},&n\ge2\ \text{且}\ [A,J]\ne0.
\end{cases}
$$

若允许一般量子存储，逐项无损所需的最小输出 Hilbert 空间维数为

$$
\boxed{
 d_{\min}^{\mathrm{quantum}}=
 \begin{cases}
 1,&n=0,\\
 2,&n\ge1.
 \end{cases}
}
$$

第 36 节的最佳经典总分还满足

$$
\boxed{
V_m=\sum_{j=1}^mL(c_j)
\quad\Longleftrightarrow\quad
[A,J]=0\ \text{或}\ n\le1.
}
$$

因此，对非对易候选对及至少两个不定权重，有严格差距

$$
V_m<\sum_{j=1}^mL(c_j).
$$

证明。定理 37.1 已给出所有可行情形的一标签或二标签构造。若存在不定权重 $c$，其正、负谱均非零，因此

$$
\|D_c\|_1=\lambda_++\lambda_-
>|\lambda_+-\lambda_-|
=|c-1|.
$$

一标签经典通道对每个输入只输出概率一；更一般地，输出维数为一的 CPTP 映射只能输出唯一的密度矩阵。两者在权重 $c$ 上都只能留下 $|c-1|$，所以有不定权重时，一标签或一维量子输出均不足。二元测量达到经典可行情形的下界；量子比特恒等通道则保持 $A,J$ 本身，达到所有情形的二维量子上界。

最后，迹范数收缩性逐项给出 $L_\Phi(c_j)\le L(c_j)$。若定理 37.1 的条件成立，无损通道使总和取等。反过来，若 $V_m$ 等于量子总分，定理 36.1 保证该经典最大值由一个有限 POVM 达到。各项的非负损失之和为零，故同一个通道逐项无损，定理 37.1 的条件必须成立。它的补集因而给出所述严格不等式；这里没有声称一个与候选对及权重表无关的正差距常数。证毕。

**命题 37.3（同一个混合态对的三种权重表）。** 取

$$
A=\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix},\qquad
J=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix}.
$$

两者均为满秩密度矩阵且不对易。对这个固定候选对，三种权重表的逐项无损资源如下：

| 预先给定的权重表 | 不定权重数 $n$ | 逐项无损的最少经典标签数 | 逐项无损的最小量子输出维数 |
| --- | ---: | --- | ---: |
| $(1/4,4)$ | $0$ | $1$ | $1$ |
| $(1/4,1,4)$ | $1$ | $2$ | $2$ |
| $(1,2)$ | $2$ | 不存在有限经典实现 | $2$ |

证明。$A,J$ 的特征值均为 $3/4,1/4$，所以都是满秩密度矩阵。直接相乘及计算行列式得到

$$
[A,J]=\begin{pmatrix}0&1/8\\-1/8&0\end{pmatrix}\ne0,
\qquad
\det(cA-J)=\frac{3c^2-8c+3}{16}.
$$

所以不定权重恰好位于开区间

$$
\left(\frac{4-\sqrt7}{3},\frac{4+\sqrt7}{3}\right).
$$

端点行列式为零，仍属半定情形。权重 $1/4,4$ 位于该区间外，$1,2$ 位于该区间内。三张表中的不定权重数因而分别为零、一、二；定理 37.1 与推论 37.2 给出所列资源结论。

这个例子说明，权重表的长度本身不决定同时无损的可行性。对不定区间之外的权重，先验已经使恒定决策达到最优；这些任务不要求存储保留候选态之间的区别。进入不定区间后，最优决策必须利用测量结果；同一个非对易候选对在两个不同的不定权重下要求不同且不兼容的二元谱测量。

上述结构是已知后测量信息判别与测量兼容性原理的量子比特特化。Carmeli、Heinosaari 与 Toigo 的 [Theorem 1](https://arxiv.org/html/1804.09693) 说明，有限个子系综的测量前、测量后信息判别最优值相等，当且仅当存在一组彼此兼容的各子系综最优测量；该结果允许一般混合态。对本节可明确取

$$
Z=m+\sum_{j=1}^m c_j,\qquad
q_j=\frac{1+c_j}{Z}>0,
$$

第 $j$ 个子系综的两个先验分别为 $c_j/(1+c_j)$ 与 $1/(1+c_j)$。用不同的标签 $(j,A)$、$(j,J)$ 区分子系综，即使密度矩阵在不同标签下重复，也符合该文的系综定义。由此

$$
p_{\mathrm{guess}}^{\mathrm{post}}
=\frac12+\frac{V_m}{2Z},\qquad
p_{\mathrm{guess}}^{\mathrm{prior}}
=\frac12+\frac{\sum_{j=1}^mL(c_j)}{2Z}.
$$

定理 37.1 将这项兼容性条件化为本任务可直接检查的行列式与对易子条件。这里的标签数和维数均只计算固定存储通道的输出；结论没有把一个量子比特等同于一位经典记录，也不对此前的控制器历史或多阶段协议总资源作相同计数。证毕。

## 追加锚（新终端）

## 38. 高维无损存储的谱投影判据与输出维数

**定理 38.1（可逆加权差的相容性与最少输出资源）。** 把第 36 节的固定存储任务推广到任意有限维 Hilbert 空间 $\mathcal H$，记 $\dim\mathcal H=d\ge1$。设 $A,J$ 为该空间上的密度矩阵，预先给定

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,
\qquad D_j=c_jA-J.
$$

假设每个 $D_j$ 都可逆，记 $P_j$ 为其正谱投影；允许 $P_j=0$ 或 $P_j=I$。所有候选输入使用同一个 CPTP 存储映射 $\Phi$，且该映射必须在实际权重揭示前固定。

存在有限经典输出存储使

$$
\|\Phi(D_j)\|_1=\|D_j\|_1\qquad(j=1,\ldots,m)
$$

当且仅当正谱投影族两两对易：

$$
\boxed{P_iP_j=P_jP_i\qquad(1\le i,j\le m).}
$$

在此相容条件成立时，对 $s=(s_1,\ldots,s_m)\in\{0,1\}^m$ 定义联合符号投影

$$
R_s=\prod_{j=1}^m\bigl[s_jP_j+(1-s_j)(I-P_j)\bigr],
\qquad
\mathcal S=\{s:R_s\ne0\},\qquad N=|\mathcal S|.
$$

这些乘积与排列次序无关。逐项无损所需的最少非零经典输出标签数，以及允许一般量子存储时的最小输出 Hilbert 空间维数，均恰为

$$
\boxed{n_{\min}^{\mathrm{classical}}=d_{\min}^{\mathrm{quantum}}=N.}
$$

这里的维数结论只针对上述相容情形。此外，在本节递增的正权重表下，相容投影必满足

$$
P_1\le P_2\le\cdots\le P_m,
\qquad 1\le N\le\min\{d,m+1\}.
$$

证明。先说明可逆性给出的等号刚性。对任意可逆 Hermitian 矩阵 $D$，写

$$
D=D_+-D_-,\qquad D_+,D_-\ge0,
$$

其中正、负部分支撑正交，正谱投影为 $P$。对 $0\le E\le I$ 有

$$
\operatorname{tr}(D_+)-\operatorname{tr}(ED)
=\operatorname{tr}((I-E)D_+)+\operatorname{tr}(ED_-)\ge0.
$$

右端为零当且仅当 $E$ 在 $D_+$ 的支撑上等于恒等、在 $D_-$ 的支撑上等于零。事实上，对正矩阵 $B,C$，$\operatorname{tr}(BC)=0$ 强制 $B^{1/2}C^{1/2}=0$；把它分别应用于两项即可。可逆性使这两个支撑的直和等于整个输入空间，故最优效应唯一，恰为 $P$。特别地，

$$
\max_{0\le E\le I}\operatorname{tr}(ED)
=\operatorname{tr}(D_+)
=\frac{\|D\|_1+\operatorname{tr}D}{2}.
$$

现在设 $\Phi$ 为任意逐项无损的有限维输出 CPTP 映射。对每个 $j$，在输出空间选择一个达到 $\Phi(D_j)$ 的上述最大值的效应 $F_j$。输出加权差可以有零特征值，这里只需选择一个最优效应，不要求它唯一。伴随映射 $\Phi^*$ 保单位且完全正，故 $\Phi^*(F_j)$ 是输入空间上的合法效应。迹保持与范数等号给出

$$
\operatorname{tr}(\Phi^*(F_j)D_j)
=\operatorname{tr}(F_j\Phi(D_j))
=\frac{\|D_j\|_1+\operatorname{tr}D_j}{2}.
$$

由输入最优效应的唯一性，得到关键算子等式

$$
\boxed{\Phi^*(F_j)=P_j\qquad(j=1,\ldots,m).}
$$

若输出是有限经典标签，设对应输入 POVM 为 $(E_\ell)_\ell$。输出加权差是对角矩阵，可以选择其严格正对角元集合的指示效应作为 $F_j$。因此每个 $P_j$ 都是同一 POVM 的结果合并：

$$
P_j=\sum_{\ell\in B_j}E_\ell.
$$

对任意两个指标 $i,j$，把标签按是否属于 $B_i,B_j$ 分成四组，所得效应记作 $G_{ab}$，$a,b\in\{0,1\}$。它们满足

$$
P_i=G_{11}+G_{10},\qquad
P_j=G_{11}+G_{01},\qquad
0\le G_{ab}\le P_i^{(a)},P_j^{(b)},
$$

其中 $P^{(1)}=P$、$P^{(0)}=I-P$。正效应被投影 $P$ 支配时，其支撑包含在 $\operatorname{ran}P$ 中，因而 $PE=EP=E$。据此

$$
P_iP_j=P_i(G_{11}+G_{01})=G_{11}
=P_jP_i.
$$

这证明经典逐项无损要求投影两两对易。

反过来，设全部 $P_j$ 两两对易。其联合投影 $(R_s)_{s\in\mathcal S}$ 两两正交，且和为 $I$。对每个 $j$，$R_s$ 的值域完全落在 $D_j$ 的正谱子空间或负谱子空间内，取决于 $s_j$。因此

$$
\bigl|\operatorname{tr}(R_sD_j)\bigr|
=(2s_j-1)\operatorname{tr}(R_sD_j).
$$

求和并使用 $\sum_s(2s_j-1)R_s=2P_j-I$，有

$$
\sum_{s\in\mathcal S}\bigl|\operatorname{tr}(R_sD_j)\bigr|
=\operatorname{tr}((2P_j-I)D_j)=\|D_j\|_1.
$$

于是通道

$$
\Phi_{\rm sign}(\rho)
=\sum_{s\in\mathcal S}\operatorname{tr}(R_s\rho)|s\rangle\langle s|
$$

同时保持所有加权差的迹范数。它有 $N$ 个非零经典标签，也给出输出维数为 $N$ 的一般量子存储上界。

为证明任意量子存储都不能使用更小的输出维数，对每个 $s\in\mathcal S$ 选择单位向量 $v_s\in\operatorname{ran}R_s$，并对任意逐项无损 CPTP 映射定义

$$
\rho_s=\Phi(|v_s\rangle\langle v_s|).
$$

由前面已证的拉回等式，

$$
\operatorname{tr}(F_j\rho_s)
=\langle v_s,P_jv_s\rangle=s_j.
$$

若密度矩阵 $\rho$ 对效应 $0\le F\le I$ 的期望为零，正性使 $\operatorname{supp}\rho\subseteq\ker F$；若期望为一，则对 $I-F$ 应用同一论证，得到 $\operatorname{supp}\rho\subseteq\ker(I-F)$。当 $s\ne t$ 时，至少存在一个 $j$ 使 $s_j\ne t_j$，故 $\rho_s$ 与 $\rho_t$ 分别支撑在 $F_j$ 的零和一本征空间内，二者正交。

这样，输出空间包含 $N$ 个两两正交且非零的支撑，因为每个 $\rho_s$ 的迹都为一。输出维数至少为 $N$。这里不要求输出效应族 $(F_j)$ 彼此对易；每对不同输出状态只需由其中一个效应确定地区分。向量 $v_s$ 是检验同一 CPTP 映射的数学测试输入，并未给原判别任务增添候选态。任意有限经典输出也属于一般量子输出，故同一下界适用于其标签数。结合构造，两种最少资源都等于 $N$。

最后核对投影嵌套。若 $i<j$，则

$$
D_j-D_i=(c_j-c_i)A\ge0.
$$

由于 $P_i,P_j$ 对易，若 $P_i(I-P_j)\ne0$，可在其值域中取单位向量 $v$。可逆性给出 $\langle v,D_iv\rangle>0$ 而 $\langle v,D_jv\rangle<0$，与上式矛盾。所以 $P_i\le P_j$。非零联合符号串只能由一段零接一段一组成，至多有 $m+1$ 种；两两正交的非零联合子空间数也不超过 $d$。这给出所列 $N$ 的上下界。

兼容最优测量与后揭信息判别的联系沿用 Carmeli、Heinosaari 与 Toigo 的 [Theorem 1](https://arxiv.org/html/1804.09693)，第 37 节给出的归一化映射同样适用于本节任意有限维候选。锐测量可共同测量时必须对易及其联合投影形式，见 Heinosaari、Reitzner 与 Stano，*Notes on Joint Measurability of Quantum Observables*，[附录 Proposition 8](https://arxiv.org/abs/0811.0783)。本节给出了这些标准兼容性原则在指定加权差任务上的直接证明，并用输出正交支撑计算最少资源。输入可逆性用于保证最优效应唯一；带有零特征值的加权差不在本定理范围内。证毕。

**命题 38.2（严格正定三维候选的非对易无损反例）。** 在 $\mathbb C^3$ 上取

$$
A=\frac1{12}\begin{pmatrix}
4&1&0\\
1&4&-1\\
0&-1&4
\end{pmatrix},
\qquad
J=\frac1{48}\begin{pmatrix}
8&3&0\\
3&16&-5\\
0&-5&24
\end{pmatrix},
$$

以及两个后揭权重

$$
c_1=\frac34,\qquad c_2=\frac54.
$$

这两个候选都是严格正定密度矩阵且 $[A,J]\ne0$。两个加权差 $D_1=c_1A-J$、$D_2=c_2A-J$ 均可逆不定，其正谱投影分别为

$$
P_1=\operatorname{diag}(1,0,0),\qquad
P_2=\operatorname{diag}(1,1,0).
$$

它们不同且严格嵌套。因此存在共同经典存储逐项无损，且其最少非零标签数与一般量子存储的最小输出维数都恰为三。两项被保持的量子范数均为

$$
\|D_1\|_1=\|D_2\|_1=\frac5{12}.
$$

证明。两个矩阵的迹都为一。它们的顺序主子式分别为

$$
A:\quad\frac13,\ \frac5{48},\ \frac7{216};
\qquad
J:\quad\frac16,\ \frac{119}{2304},\ \frac{83}{3456}.
$$

这些数均严格为正，Sylvester 判据给出严格正定性。直接相乘得到

$$
[A,J]=\frac1{288}
\begin{pmatrix}
0&4&-1\\
-4&0&-4\\
1&4&0
\end{pmatrix}\ne0.
$$

加权差为

$$
D_1=\frac1{24}
\begin{pmatrix}
2&0&0\\
0&-2&1\\
0&1&-6
\end{pmatrix},
\qquad
D_2=\frac1{24}
\begin{pmatrix}
6&1&0\\
1&2&0\\
0&0&-2
\end{pmatrix}.
$$

两个谱分别为

$$
\operatorname{spec}(D_1)
=\left\{\frac1{12},\frac{-4+\sqrt5}{24},\frac{-4-\sqrt5}{24}\right\},
$$

$$
\operatorname{spec}(D_2)
=\left\{-\frac1{12},\frac{4+\sqrt5}{24},\frac{4-\sqrt5}{24}\right\}.
$$

因 $0<\sqrt5<4$，它们都无零特征值，且分别有一个与两个正特征值。上述分块形式同时确定了陈述中的 $P_1,P_2$；按符号求特征值绝对值之和得到两项范数 $5/12$。

非零联合符号投影恰为

$$
R_{(1,1)}=|e_1\rangle\langle e_1|,\qquad
R_{(0,1)}=|e_2\rangle\langle e_2|,\qquad
R_{(0,0)}=|e_3\rangle\langle e_3|,
$$

而 $R_{(1,0)}=0$。定理 38.1 因而给出两种最少输出资源都为三。具体达到测量就是标准基上的三元投影测量；它在两个权重上的读数分别为

$$
\left(\frac1{12},-\frac1{12},-\frac14\right),
\qquad
\left(\frac14,\frac1{12},-\frac1{12}\right),
$$

各自的绝对值之和均为 $5/12$。

这个反例说明定理 37.1 的候选态对易判据具有二维限制。在二维不定情形，每个加权差都是恒等矩阵与其正谱投影的线性组合，正谱投影对易便迫使加权差对易。在三维，一个正谱或负谱子空间可以有二维；不同加权差在这些子空间内部仍能不对易，而选定判别任务的正负谱投影已经相容。这里三个经典标签保存的是两问所需的联合符号信息，定理并未要求保存候选态的全部量子结构。证毕。

## 追加锚（新终端）

## 39. 两项不定判别量无损强制整个量子比特可恢复

**定理 39.1（两权重等号与全输入可恢复性）。** 设 $A,J$ 为量子比特密度矩阵，且

$$
[A,J]\ne0,\qquad c,d>0,\qquad c\ne d.
$$

记 $D_t=tA-J$，并要求两个加权差都严格不定：

$$
\det D_c<0,\qquad \det D_d<0.
$$

令 $\Phi:\mathcal L(\mathbb C^2)\to\mathcal L(\mathcal H_B)$ 为 CPTP 映射，其中输出空间 $\mathcal H_B$ 有限维。则

$$
\boxed{
\|\Phi(D_c)\|_1=\|D_c\|_1
\quad\text{且}\quad
\|\Phi(D_d)\|_1=\|D_d\|_1
\quad\Longleftrightarrow\quad
\exists\ \mathcal R\ \mathrm{CPTP},\quad
\mathcal R\circ\Phi=\operatorname{id}_{\mathcal L(\mathbb C^2)}.
}
$$

右端的恢复通道定义在整个 $\mathcal L(\mathcal H_B)$ 上，恢复所有量子比特输入；它是 $\Phi$ 的 CPTP 左逆，不要求 $\Phi$ 映满全部输出状态。

这些条件还等价于下面的正交等距正规形：存在整数 $r\ge1$、正数 $\lambda_1,\ldots,\lambda_r$ 及等距映射 $V_a:\mathbb C^2\to\mathcal H_B$，满足

$$
\sum_{a=1}^r\lambda_a=1,\qquad
V_a^\dagger V_b=\delta_{ab}I_2,
\qquad
\Phi(X)=\sum_{a=1}^r\lambda_aV_aXV_a^\dagger
\quad\text{对全部 }X\in\mathcal L(\mathbb C^2).
$$

特别地，$2r\le\dim\mathcal H_B$。定义

$$
\omega=\sum_{a=1}^r\lambda_a|a\rangle\langle a|,\qquad
W(|\psi\rangle\otimes|a\rangle)=V_a|\psi\rangle,
$$

则 $W:\mathbb C^2\otimes\mathbb C^r\to\mathcal H_B$ 是等距映射，且

$$
\boxed{\Phi(\rho)=W(\rho\otimes\omega)W^\dagger.}
$$

辅助态 $\omega$ 固定且与输入无关，可以是混合态。上述表达只占用输出空间中的一个子空间，不要求输出维数为偶数。

证明。先由两个范数等号推出正规形。对 $t\in\{c,d\}$，将输入加权差写成

$$
D_t=\mu_{t,+}P_t-\mu_{t,-}(I_2-P_t),\qquad
\mu_{t,+},\mu_{t,-}>0,
$$

其中 $P_t$ 为秩一正谱投影。令

$$
\rho_{t,+}=\Phi(P_t),\qquad
\rho_{t,-}=\Phi(I_2-P_t).
$$

两者均为输出密度矩阵。有限维输出上存在最优二元判别效应 $0\le F_t\le I_B$。对任意 Hermitian 矩阵 $H$，有

$$
\|H\|_1=2\max_{0\le F\le I}\operatorname{tr}(FH)-\operatorname{tr}H.
$$

应用于 $H=\Phi(D_t)$，再用范数等号和迹保持性，得到

$$
\operatorname{tr}\!\left[F_t
(\mu_{t,+}\rho_{t,+}-\mu_{t,-}\rho_{t,-})\right]
=\mu_{t,+}.
$$

等价地，

$$
\mu_{t,+}\bigl(1-\operatorname{tr}(F_t\rho_{t,+})\bigr)
+\mu_{t,-}\operatorname{tr}(F_t\rho_{t,-})=0.
$$

两项非负且两个系数严格为正，故

$$
\operatorname{tr}(F_t\rho_{t,+})=1,\qquad
\operatorname{tr}(F_t\rho_{t,-})=0.
$$

正性将这两个条件分别化为

$$
\operatorname{supp}\rho_{t,+}\subseteq\ker(I_B-F_t),\qquad
\operatorname{supp}\rho_{t,-}\subseteq\ker F_t.
$$

因此，$D_t$ 的两个纯本征输入经 $\Phi$ 后仍有正交支撑。

取 $\Phi$ 的任意有限 Kraus 表示

$$
\Phi(X)=\sum_{a=1}^N K_aXK_a^\dagger,\qquad
\sum_{a=1}^N K_a^\dagger K_a=I_2.
$$

若 $|t,+\rangle,|t,-\rangle$ 是 $P_t,I_2-P_t$ 的单位本征向量，则 $K_a|t,+\rangle$ 与 $K_b|t,-\rangle$ 分别落在上述正交支撑内。对任意 $a,b$，于是

$$
\langle t,+|K_a^\dagger K_b|t,-\rangle=0,\qquad
\langle t,-|K_a^\dagger K_b|t,+\rangle=0.
$$

所以 $K_a^\dagger K_b$ 在 $P_t$ 的本征基中对角；这个矩阵不必自伴，但两个非对角元都为零。

另一方面，

$$
[D_c,D_d]=(d-c)[A,J]\ne0.
$$

由于每个 $D_t$ 都是 $P_t$ 的非退化仿射函数，可知 $[P_c,P_d]\ne0$。一个二阶矩阵若在 $P_c$ 的本征基中对角，就可写为 $xI_2+yP_c$；若还与 $P_d$ 对易，则 $y[P_c,P_d]=0$，从而 $y=0$。因此存在复数 $\alpha_{ab}$，使

$$
\boxed{K_a^\dagger K_b=\alpha_{ab}I_2\qquad(1\le a,b\le N).}
$$

矩阵 $\alpha=(\alpha_{ab})$ 自伴且半正定。事实上，对任意 $z\in\mathbb C^N$，

$$
\left(\sum_a z_aK_a\right)^\dagger
\left(\sum_b z_bK_b\right)
=(z^\dagger\alpha z)I_2\ge0.
$$

迹保持性又给出 $\sum_a\alpha_{aa}=1$。选取酉矩阵 $U$ 使 $U^\dagger\alpha U$ 对角，并置 $L_b=\sum_aU_{ab}K_a$。这些算子仍表示同一个通道，且

$$
L_a^\dagger L_b=\delta_{ab}\lambda_aI_2,
\qquad \lambda_a\ge0,\qquad \sum_a\lambda_a=1.
$$

删去 $\lambda_a=0$ 的零算子，对剩余算子定义 $V_a=L_a/\sqrt{\lambda_a}$，即得到所述正交等距正规形。各 $V_a$ 的像空间两两正交且均为二维，故 $2r\le\dim\mathcal H_B$。由 $V_a^\dagger V_b=\delta_{ab}I_2$ 可直接核对 $W^\dagger W=I_2\otimes I_r$，以及固定辅助态表达。

现在由正规形构造恢复通道。令

$$
Q=\sum_{a=1}^rV_aV_a^\dagger,
$$

它是 $\Phi$ 所占用输出子空间的正交投影。任选一个量子比特密度矩阵 $\tau$，定义

$$
\boxed{
\mathcal R(X)=\sum_{a=1}^rV_a^\dagger XV_a
+\operatorname{tr}\bigl[(I_B-Q)X\bigr]\tau.
}
$$

第一项为 Kraus 形式的完全正映射，第二项为一个测量后制备固定态的完全正映射。两项的迹分别为 $\operatorname{tr}(QX)$ 与 $\operatorname{tr}((I_B-Q)X)$，故 $\mathcal R$ 保持迹，且定义覆盖整个输出空间。对任意量子比特输入矩阵 $X$，正交等距关系给出

$$
\mathcal R(\Phi(X))
=\sum_{a=1}^r\lambda_aX=X.
$$

最后，若已有 CPTP 左逆 $\mathcal R$，对任意 Hermitian 输入 $H$，迹范数收缩性给出

$$
\|H\|_1=\|\mathcal R(\Phi(H))\|_1
\le\|\Phi(H)\|_1\le\|H\|_1.
$$

所以 $\Phi$ 保持全部 Hermitian 输入的迹范数，特别地保持 $D_c,D_d$。这完成全部等价关系。由于恢复的是整个输入空间上的恒等通道，张量一个任意有限维参考系统后仍有恒等关系；恢复也保留输入与该参考系统的纠缠，不要求访问参考系统。

上面的 $K_a^\dagger K_b=\alpha_{ab}I_2$ 是以整个量子比特作为编码空间的标准 Knill–Laflamme 条件，见 Knill 与 Laflamme，*Theory of quantum error-correcting codes*，[Theorem 3.2 的式 (19)、(20) 及 Theorem 3.3](https://arxiv.org/html/quant-ph/9604034)。可恢复通道的正交等距及固定辅助态正规形也已有一般维数的结果，见 Nayak 与 Sen，*Invertible Quantum Operations and Perfect Encryption of Quantum States*，[Theorem 2.1 及其证明中的式 (2)、(3)](https://arxiv.org/html/quant-ph/0605041)。本节的两权重判据通过两个不兼容谱基的范数等号达到这些已有条件；它不把一般纠错条件或可恢复通道正规形另作新理论。证毕。

**推论 39.2（二维输出时必须是酉通道）。** 在定理 39.1 的非对易、两个不同严格不定权重假设下，若还要求 $\mathcal H_B=\mathbb C^2$，则

$$
\|\Phi(D_c)\|_1=\|D_c\|_1
\quad\text{且}\quad
\|\Phi(D_d)\|_1=\|D_d\|_1
\quad\Longleftrightarrow\quad
\exists\ U\ \mathrm{unitary},\quad
\Phi(X)=UXU^\dagger\ \text{对全部 }X.
$$

证明。定理 39.1 给出 $r\ge1$ 与 $2r\le2$，故 $r=1$、$\lambda_1=1$。唯一的等距映射 $V_1:\mathbb C^2\to\mathbb C^2$ 是酉矩阵，取 $U=V_1$ 即得结论。反向由酉共轭保持迹范数成立。

这里不是用两个标量读数重建一个未知量子态，而是要求同一个 CPTP 通道在两个指定判别任务上都保持量子最优值。严格不定性使每个等号要求保留一整组正交本征输入的可区分性；非对易性使这两组谱基不兼容，进而约束整个通道。结论中的有限输出、非对易、不同权重及两个严格不定条件均保留，不由第 37 节中半定权重的自动无损情形代替。证毕。

## 追加锚（新终端）

## 40. 后揭两权重的经典损失底线与可达上界

**定理 40.1（两项严格不定任务的显式损失界）。** 设 $A,J$ 为量子比特密度矩阵，且

$$
[A,J]\ne0,\qquad c,d>0,\qquad c\ne d,
\qquad \det(cA-J)<0,\quad\det(dA-J)<0.
$$

对 $t\in\{c,d\}$，记

$$
D_t=tA-J,\qquad P_t=\mathbf 1_{(0,\infty)}(D_t),
\qquad S_t=2P_t-I_2,
$$

$$
a_t=\frac{t-1}{2},\qquad
b_t=\frac{\|D_t\|_1}{2},\qquad
\mu_t=b_t-|a_t|>0.
$$

于是 $D_t=a_tI_2+b_tS_t$，且 $\mu_t$ 是正、负特征值绝对值中的较小者。再记

$$
\kappa=2\operatorname{tr}(P_cP_d)-1,
\qquad \eta=|\kappa|\in[0,1),
$$

$$
M=\sqrt{\mu_c^2+\mu_d^2+2\mu_c\mu_d\eta},
$$

$$
\mathsf L=2(\mu_c+\mu_d-M),
\qquad
\mathsf U=2\min\{\mu_c,\mu_d,b_c(1-\eta),b_d(1-\eta)\}.
$$

令 $V$ 为在同一个有限经典存储上优化的范数总分，允许任意有限结果数：

$$
V=\max_{\Phi\ \mathrm{classical}}
\bigl(\|\Phi(D_c)\|_1+\|\Phi(D_d)\|_1\bigr),
\qquad
\Delta=\|D_c\|_1+\|D_d\|_1-V.
$$

最大值的存在性由定理 36.1 保证。则

$$
\boxed{0<\mathsf L\le\Delta\le\mathsf U.}
$$

上界 $\mathsf U$ 由两个明确的存储测量之一达到其所述损失：在 $P_c,I_2-P_c$ 与 $P_d,I_2-P_d$ 之间，预先选择总损失较小的一组，然后固定使用它。该选择依赖已知候选及完整权重表，不依赖后来才揭示的实际权重。

证明。首先，由 $[D_c,D_d]=(d-c)[A,J]\ne0$ 及量子比特的非退化谱分解，可知 $P_c,P_d$ 不对易。两个秩一投影对易当且仅当其值域相同或正交，所以 $0<\operatorname{tr}(P_cP_d)<1$，即 $\eta<1$。

固定任意有限 POVM $(E_\ell)_\ell$ 及其经典输出通道 $\Phi$。记它在权重 $t$ 上的损失为

$$
\delta_t=\|D_t\|_1-\|\Phi(D_t)\|_1.
$$

写 $\lambda_{t,+}=b_t+a_t>0$、$\lambda_{t,-}=b_t-a_t>0$。对固定 $t$，令

$$
p_\ell=\operatorname{tr}(E_\ell P_t),\qquad
q_\ell=\operatorname{tr}(E_\ell(I_2-P_t)).
$$

两组数非负且各自之和为一。经典输出的对角元为 $\lambda_{t,+}p_\ell-\lambda_{t,-}q_\ell$，所以

$$
\begin{aligned}
\delta_t
&=2\sum_\ell\min\{\lambda_{t,+}p_\ell,\lambda_{t,-}q_\ell\}\\
&\ge2\mu_t\sum_\ell\min\{p_\ell,q_\ell\}\\
&=\mu_t\left(2-\sum_\ell|p_\ell-q_\ell|\right)\\
&=\mu_t\bigl(2-\|\Phi(S_t)\|_1\bigr).
\end{aligned}
$$

剩下的辅助测量优化有一个精确值：

$$
\max_{\Phi\ \mathrm{classical}}
\bigl(\mu_c\|\Phi(S_c)\|_1+\mu_d\|\Phi(S_d)\|_1\bigr)=2M.
$$

为直接证明它，对 $\varepsilon,\zeta\in\{-1,1\}$ 定义四个奖励矩阵

$$
X_{\varepsilon,\zeta}
=\varepsilon\mu_cS_c+\zeta\mu_dS_d.
$$

两个无迹二阶矩阵满足

$$
S_c^2=S_d^2=I_2,
\qquad S_cS_d+S_dS_c=2\kappa I_2.
$$

第二式可将无迹二阶矩阵的恒等式 $X^2=\tfrac12\operatorname{tr}(X^2)I_2$ 应用于 $S_c+S_d$ 后得到，其中 $\operatorname{tr}(S_cS_d)=2\kappa$。

因此

$$
X_{\varepsilon,\zeta}^2
=\bigl(\mu_c^2+\mu_d^2+2\varepsilon\zeta\mu_c\mu_d\kappa\bigr)I_2,
\qquad MI_2\ge X_{\varepsilon,\zeta}.
$$

逐效应选择两个迹的符号，便有

$$
\begin{aligned}
&\mu_c\|\Phi(S_c)\|_1+\mu_d\|\Phi(S_d)\|_1\\
&=\sum_\ell\max_{\varepsilon,\zeta}
\operatorname{tr}(E_\ell X_{\varepsilon,\zeta})
\le\sum_\ell\operatorname{tr}(E_\ell MI_2)=2M.
\end{aligned}
$$

选择 $\varepsilon\zeta\kappa=|\kappa|$；若 $\kappa=0$，任选一个符号组合即可。对应矩阵 $X$ 无迹且有特征值 $M,-M$。测量它的正、负谱投影，并在两结果上分别采用奖励 $X,-X$，线性奖励之和恰为 $2M$。原绝对值目标不小于这组奖励，又受上面的 $2M$ 约束，故达到 $2M$。这证明辅助最优值，且二元谱测量足够。

将辅助上界代入两个单项损失估计，得到对每个有限经典存储都成立的

$$
\delta_c+\delta_d\ge2(\mu_c+\mu_d)-2M=\mathsf L.
$$

而

$$
(\mu_c+\mu_d)^2-M^2=2\mu_c\mu_d(1-\eta)>0,
$$

所以 $\mathsf L>0$；也可写成

$$
\mathsf L=
\frac{4\mu_c\mu_d(1-\eta)}{\mu_c+\mu_d+M}.
$$

现在给出实际测量的上界。选择 $P_c,I_2-P_c$ 时，权重 $c$ 的范数完全保持，而 $D_d$ 的两个输出对角元为

$$
a_d+b_d\kappa,\qquad a_d-b_d\kappa.
$$

利用 $|x+y|+|x-y|=2\max\{|x|,|y|\}$，这组测量在 $d$ 上的范数和损失分别为

$$
2\max\{|a_d|,b_d\eta\},
\qquad
2b_d-2\max\{|a_d|,b_d\eta\}
=2\min\{\mu_d,b_d(1-\eta)\}.
$$

交换 $c,d$，另一组谱测量的总损失为 $2\min\{\mu_c,b_c(1-\eta)\}$。选择其中较小者，所得实际总损失正好为 $\mathsf U$，因此最佳经典存储的损失 $\Delta\le\mathsf U$。结合此前对任意存储的下界，完成所列夹逼。

这两个界可以直接解释为容差限制。给定 $\epsilon_c,\epsilon_d\ge0$，若要求同一个经典存储满足 $\delta_c\le\epsilon_c$、$\delta_d\le\epsilon_d$，必要条件是

$$
\epsilon_c+\epsilon_d\ge\mathsf L.
$$

若只要求总损失不超过 $\epsilon$，则 $\epsilon<\mathsf L$ 不可行，而 $\epsilon\ge\mathsf U$ 由上述二元谱测量保证可行。中间区间的判定仍需实际最优值 $\Delta$。

按第 37 节的归一化，令

$$
Z=2+c+d,\qquad q_c=\frac{1+c}{Z},\qquad q_d=\frac{1+d}{Z},
$$

并在权重 $t$ 下使用条件先验 $t/(1+t),1/(1+t)$。权重揭示前保留量子输入的最佳平均成功率，与先作经典存储后再揭示权重的最佳平均成功率，分别为

$$
p_{\rm quantum}=\frac12+\frac{\|D_c\|_1+\|D_d\|_1}{2Z},
\qquad
p_{\rm classical}=\frac12+\frac{V}{2Z}.
$$

因此

$$
\frac{\mathsf L}{2Z}
\le p_{\rm quantum}-p_{\rm classical}
=\frac{\Delta}{2Z}
\le\frac{\mathsf U}{2Z}.
$$

沿满足本定理假设的参数序列，若 $\min\{\mu_c,\mu_d\}\to0$，或 $\min\{b_c,b_d\}(1-\eta)\to0$，上界立即给出 $\Delta\to0$。特别地，在 $\min\{b_c,b_d\}$ 有界时，$\eta\to1$ 足以使损失趋零。这些界依赖给定候选与权重，未给出跨参数的统一正损失常数。

辅助优化在 $\mu_c=\mu_d$ 时，对应 Carmeli、Heinosaari 与 Toigo，[§V.2，式 (27)](https://arxiv.org/html/1804.09693) 的两个等概率量子比特本征基：其后测量信息成功率为 $\tfrac12(1+\sqrt{(1+\eta)/2})$。一般正系数的辅助最优值由上面的四奖励证书直接证明。辅助值的精确性不使原损失下界自动精确，因为将两本征值绝对值同时替换为 $\mu_t$ 的步骤可以产生严格不等式。证毕。

**命题 40.2（混态例中的精确最优值与两个严格界）。** 取命题 37.3 的满秩候选

$$
A=\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix},\qquad
J=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},
\qquad c=1,\quad d=2.
$$

最佳经典范数总分及其相对量子总分的损失为

$$
\boxed{V=\frac{\sqrt{13}}2,\qquad
\Delta=\frac{\sqrt2+\sqrt5-\sqrt{13}}2.}
$$

定理 40.1 的两个界在此化为

$$
\mathsf L=
\frac{\sqrt2+\sqrt5-2-\sqrt{17-32/\sqrt5}}2,
\qquad
\mathsf U=\frac{\sqrt2-3/\sqrt5}{2},
$$

并满足严格关系

$$
\boxed{0<\mathsf L<\Delta<\mathsf U.}
$$

证明。命题 37.3 已核对候选不对易及两个权重都在严格不定区间。这里直接写出

$$
D_1=\frac14\begin{pmatrix}1&-1\\-1&-1\end{pmatrix},
\qquad
D_2=\begin{pmatrix}1&-1/4\\-1/4&0\end{pmatrix}.
$$

它们的迹范数分别为 $\sqrt2/2$ 与 $\sqrt5/2$；由 $S_t=(D_t-a_tI_2)/b_t$ 计算得到 $\operatorname{tr}(S_cS_d)=6/\sqrt{10}$。因此

$$
b_c=\mu_c=\frac{\sqrt2}{4},\qquad
b_d=\frac{\sqrt5}{4},\qquad
\mu_d=\frac{\sqrt5-2}{4},\qquad
\eta=\frac3{\sqrt{10}}.
$$

先计算最佳经典值。两个差矩阵之和与差为

$$
B=D_1+D_2=3A-2J
=\begin{pmatrix}5/4&-1/2\\-1/2&-1/4\end{pmatrix},
\qquad D_2-D_1=A\ge0.
$$

对任一效应 $E\ge0$，两个绝对迹之和等于在 $B,-B,A$ 三个奖励矩阵上取最大迹；第四种符号对应的 $-A$ 被 $A$ 支配。令

$$
Y=|B|=\frac1{4\sqrt{13}}
\begin{pmatrix}19&-4\\-4&7\end{pmatrix}.
$$

$B$ 的特征值为 $(2+\sqrt{13})/4$ 与 $(2-\sqrt{13})/4$；在这两个异号特征值上线性插值得 $|B|=(2B+9I_2/4)/\sqrt{13}$，即上面的矩阵。因此 $Y\ge B,-B$ 且 $\operatorname{tr}Y=\sqrt{13}/2$。另外

$$
Y-A=\frac1{4\sqrt{13}}
\begin{pmatrix}19-3\sqrt{13}&-4\\-4&7-\sqrt{13}\end{pmatrix}>0.
$$

其左上元为正，行列式的分子为 $156-40\sqrt{13}>0$；后一个严格不等式由 $39^2>100\cdot13$ 得到。因此 $Y$ 支配全部三个奖励，对任意有限 POVM 都给出

$$
\|\Phi(D_1)\|_1+\|\Phi(D_2)\|_1\le\operatorname{tr}Y=\frac{\sqrt{13}}2.
$$

达到这个界的测量是 $B$ 的二元谱测量。具体令

$$
T=\frac1{\sqrt{13}}\begin{pmatrix}3&-2\\-2&-3\end{pmatrix},
\qquad E_+=\frac{I_2+T}{2},\quad E_-=\frac{I_2-T}{2}.
$$

$T^2=I_2$，所以 $E_+,E_-$ 是互补投影。直接计算四个迹，得到

$$
\operatorname{tr}(E_\pm D_1)=\pm\frac5{4\sqrt{13}},
\qquad
\operatorname{tr}(E_\pm D_2)=\frac12\pm\frac2{\sqrt{13}}.
$$

因为 $4>\sqrt{13}$，第二组也一正一负。两个范数之和于是为

$$
\frac5{2\sqrt{13}}+\frac4{\sqrt{13}}=\frac{\sqrt{13}}2.
$$

这证明所列精确 $V$，从量子总分 $(\sqrt2+\sqrt5)/2$ 减去它即得 $\Delta$。

代入前面的 $\mu_c,\mu_d,\eta$，有

$$
M^2=\frac{17-32/\sqrt5}{16},
$$

因而得到陈述中的 $\mathsf L$。由于 $b_c<b_d$ 且

$$
b_d\eta=\frac3{4\sqrt2}>\frac12=|a_d|,
$$

上界四项中的最小者为 $b_c(1-\eta)$，所以 $\mathsf U=2b_c(1-\eta)=(\sqrt2-3/\sqrt5)/2$。

定理 40.1 已给出 $\mathsf L>0$。最后，$\Delta<\mathsf U$ 等价于

$$
\frac8{\sqrt5}<\sqrt{13},
$$

它由 $64<65$ 成立。另一方面，因为 $\sqrt{13}-2>0$，$\mathsf L<\Delta$ 等价于

$$
\sqrt{17-32/\sqrt5}>\sqrt{13}-2.
$$

两边平方后恰好得到同一个 $8/\sqrt5<\sqrt{13}$。这证明全部严格关系。此例的最佳二元测量采用 $D_1+D_2$ 的谱基，严格优于只在两个单项谱测量之间选择；同时原损失严格高于由辅助优化得到的下界。证毕。

## 追加锚（新终端）

## 41. 判别谱投影生成的代数与最小存储维数

**定理 41.1（完整输出与免费经典标签的两种精确维数）。** 沿用定理 38.1 的有限维任务。设 $\dim\mathcal H=D\ge1$，$A,J$ 为输入密度矩阵，且

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,\qquad
D_j=c_jA-J\ \text{均可逆}.
$$

令 $P_j=\mathbf 1_{(0,\infty)}(D_j)$ 为正谱投影，允许 $P_j=0$ 或 $I$。记它们生成的含单位有限维 $C^*$ 代数为

$$
\mathfrak A=C^*(I,P_1,\ldots,P_m)\subseteq\mathcal L(\mathcal H).
$$

选择该代数的标准分块表示

$$
\mathcal H\cong\bigoplus_{k=1}^s
\left(\mathbb C^{d_k}\otimes\mathbb C^{m_k}\right),\qquad
\mathfrak A\cong\bigoplus_{k=1}^s
\left(M_{d_k}(\mathbb C)\otimes I_{m_k}\right),
$$

其中 $s,d_k,m_k\ge1$，$\sum_kd_km_k=D$。这里 $d_k$ 是第 $k$ 个简单矩阵块所作用的 Hilbert 空间维数，$m_k$ 是它在输入空间中的重复次数。

所有存储都必须在实际权重揭示前固定，并逐项满足

$$
\|\Phi(D_j)\|_1=\|D_j\|_1\qquad(j=1,\ldots,m).
$$

区分以下两种资源：

- $d_{\rm all}$：在所有有限维输出 CPTP 通道 $\Phi:\mathcal L(\mathcal H)\to\mathcal L(\mathcal K)$ 中，最小化整个输出空间的维数 $\dim\mathcal K$。若输出包含可读的经典分区标签，它们也计入这个空间。
- $q_{\rm free}$：允许任意有限个免费经典标签，输出为 $M_q(\mathbb C)\otimes\mathbb C^L\cong\bigoplus_{\ell=1}^L M_q(\mathbb C)$，只最小化共享量子寄存器的维数 $q$，$L$ 不计成本。直和上的迹与迹范数均取各块之和。

则两种最小值都达到，并且

$$
\boxed{
 d_{\rm all}=\sum_{k=1}^s d_k,\qquad
 q_{\rm free}=\max_{1\le k\le s}d_k.
}
$$

有限经典存储逐项无损，当且仅当全部 $d_k=1$，也即 $\mathfrak A$ 为交换代数。

证明。首先从范数等号得到输出上的投影表示。取任意逐项无损的有限维输出通道，写出一个有限 Kraus 表示

$$
\Phi(X)=\sum_{a=1}^N K_aXK_a^\dagger,\qquad
\sum_{a=1}^N K_a^\dagger K_a=I.
$$

在输出上取 $F_j$ 为 $\Phi(D_j)$ 的正谱投影。即使输出加权差有零特征值，这仍是一个合法的最优效应。由第 38 节证明中的可逆输入最优效应唯一性，范数等号强制

$$
\Phi^*(F_j)=P_j.
$$

由于 $F_j^2=F_j$，直接展开得

$$
\sum_a(F_jK_a-K_aP_j)^\dagger(F_jK_a-K_aP_j)
=P_j-P_j^2=0.
$$

每项半正定，故

$$
\boxed{F_jK_a=K_aP_j\qquad\text{对全部 }j,a.}
$$

令

$$
\mathcal Q=\operatorname{span}\{\operatorname{ran}K_a:1\le a\le N\}
=\operatorname{supp}\Phi(I)\subseteq\mathcal K.
$$

这里将正算子的支撑视为子空间。交织等式说明每个 $F_j$ 都保持 $\mathcal Q$；自伴性使 $\mathcal Q$ 为约化子空间。因此 $G_j=F_j|_{\mathcal Q}$ 是 $\mathcal Q$ 上的正交投影。

对任何非交换多项式 $p$，逐次使用交织等式可得

$$
p(G_1,\ldots,G_m)K_a
=K_ap(P_1,\ldots,P_m).
$$

若 $p(P_1,\ldots,P_m)=0$，左端就在每个 $K_a$ 的值域上为零，故在它们张成的 $\mathcal Q$ 上为零。反过来，若 $p(G_1,\ldots,G_m)=0$，则所有 $K_ap(P_1,\ldots,P_m)=0$；再用 $\sum_aK_a^\dagger K_a=I$，得到

$$
p(P_1,\ldots,P_m)
=\sum_aK_a^\dagger K_ap(P_1,\ldots,P_m)=0.
$$

输入、输出投影因而满足完全相同的多项式关系。有限维中，含单位的 $*$ 代数生成已经闭合，无需再加入极限。于是

$$
\pi_\Phi:\mathfrak A\longrightarrow\mathcal L(\mathcal Q),
\qquad \pi_\Phi(P_j)=G_j
$$

定义了一个忠实的含单位 $*$ 表示。这里“忠实”指 $\pi_\Phi$ 单射。

在每个简单块 $M_{d_k}(\mathbb C)$ 中选择标准矩阵单位 $e_{ab}^{(k)}$。全部 $e_{aa}^{(k)}$ 是非零、两两正交的投影，且总和为代数单位。忠实表示把它们送到 $\mathcal Q$ 上同样非零且两两正交的投影。它们共有 $\sum_kd_k$ 个，故

$$
\dim\mathcal K\ge\dim\mathcal Q\ge\sum_{k=1}^s d_k.
$$

这给出完整输出的下界。

接着构造达到通道。令 $U$ 实现陈述中的输入分块，对输入矩阵 $X$，将 $UXU^\dagger$ 的第 $k$ 个对角块记为 $X_{kk}$。在输出空间

$$
\mathcal K_0=\bigoplus_{k=1}^s\mathbb C^{d_k}
$$

上定义

$$
\mathcal C_0(X)
=\bigoplus_{k=1}^s\operatorname{tr}_{\mathbb C^{m_k}}(X_{kk}).
$$

该通道先取中央分块，再对重复因子取偏迹。每一步完全正，且输出各块的迹之和为 $\sum_k\operatorname{tr}X_{kk}=\operatorname{tr}X$，所以它是 CPTP 映射。

由于每个 $P_j\in\mathfrak A$，可写

$$
UP_jU^\dagger=\bigoplus_{k=1}^s(P_{j,k}\otimes I_{m_k}),
\qquad P_{j,k}^2=P_{j,k}=P_{j,k}^\dagger.
$$

取输出投影 $\widehat P_j=\bigoplus_kP_{j,k}$，便有 $\mathcal C_0^*(\widehat P_j)=P_j$。因此

$$
\begin{aligned}
\|\mathcal C_0(D_j)\|_1
&\ge2\operatorname{tr}(\widehat P_j\mathcal C_0(D_j))
-\operatorname{tr}\mathcal C_0(D_j)\\
&=2\operatorname{tr}(P_jD_j)-\operatorname{tr}D_j
=\|D_j\|_1.
\end{aligned}
$$

迹范数收缩性给出反向不等式，故所有项都无损。这里不要求 $D_j$ 本身属于 $\mathfrak A$；所保留的正谱投影已足以实现该项判别最优值。通道的输出维数为 $\sum_kd_k$，从而达到 $d_{\rm all}$。

现在计算免费经典标签下的量子寄存器维数。对任意输出于 $\bigoplus_{\ell=1}^L M_q(\mathbb C)$ 的逐项无损通道，上述最优谱投影 $F_j$ 都可取为按经典标签分块的矩阵。于是

$$
\mathcal Q=\bigoplus_{\ell=1}^L\mathcal Q_\ell,
\qquad \dim\mathcal Q_\ell\le q,
\qquad \pi_\Phi=\bigoplus_\ell\pi_\ell.
$$

零支撑的标签可以删去。对第 $k$ 个简单块的中央单位 $z_k=\sum_ae_{aa}^{(k)}$，忠实性保证 $\pi_\Phi(z_k)\ne0$，所以至少有一个标签 $\ell$ 满足 $\pi_\ell(z_k)\ne0$。在该标签内，矩阵单位关系使各 $\pi_\ell(e_{aa}^{(k)})$ 具有相同的秩：$\pi_\ell(e_{ab}^{(k)})$ 给出它们值域间的部分等距。它们的和非零，因而全部非零且两两正交。故

$$
q\ge\dim\mathcal Q_\ell\ge d_k.
$$

对每个 $k$ 应用这个论证，得到 $q\ge\max_kd_k$。这里不同简单块可以在不同的经典标签中出现，因此这个口径给出最大块维数。

为达到该下界，取 $q=\max_kd_k$，并选取等距嵌入 $W_k:\mathbb C^{d_k}\to\mathbb C^q$。用 $s$ 个经典标签定义

$$
\mathcal C_{\rm flag}(X)
=\bigoplus_{k=1}^s
W_k\operatorname{tr}_{\mathbb C^{m_k}}(X_{kk})W_k^\dagger
\in\bigoplus_{k=1}^s M_q(\mathbb C).
$$

此映射 CPTP；第 $k$ 个标签下只使用 $\operatorname{ran}W_k$。输出投影 $\bigoplus_kW_kP_{j,k}W_k^\dagger$ 仍拉回 $P_j$，所以同样逐项保范数。由此 $q_{\rm free}=\max_kd_k$，并且有限个标签已经足够。

纯经典输出就是 $q=1$ 的情形，因此它可行当且仅当全部 $d_k=1$。在交换情形，简单块对应第 38 节的非零联合符号子空间，$s=N$，故完整输出维数仍为 $N$；若经典标签免费，量子寄存器维数为一。在第 39 节的非对易量子比特情形，两个正谱投影生成 $M_2(\mathbb C)$，两种维数都为二，完整量子比特的可恢复性由该节的 Kraus 条件给出。

交织关系还说明，对全部 $X\in\mathfrak A$ 都有

$$
[K_a^\dagger K_b,X]=0.
$$

这是标准算子代数纠错条件在整个输入空间上的形式，见 Bény、Kempf 与 Kribs，*Quantum Error Correction of Observables*，[Theorem 9 及其证明](https://arxiv.org/html/0705.1574)；较早的陈述见同作者 *Generalization of Quantum Error Correction via the Heisenberg Picture*，[Theorem 2，式 (5)](https://arxiv.org/html/quant-ph/0608071)。

免费经典记录下的最大块维数公式已有直接先例：Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[第 5 节、Lemma 5.1 与式 (8)–(11)](https://arxiv.org/html/quant-ph/0608014)。该文研究先受量子存储限制、后获子系综标签时的完美判别，并以支持投影生成代数的最大简单块维数给出精确量子存储门槛。其原文的 $2^q$ 是存储空间维数，对应本节按维数计数的资源。

与本节的对应可逐项写出。对正负部分均非零的 $D_j$，记 $D_j=D_{j,+}-D_{j,-}$，令

$$
t_{j,\pm}=\operatorname{tr}D_{j,\pm}>0,\qquad
\rho_{\pm|j}=\frac{D_{j,\pm}}{t_{j,\pm}},\qquad
p_{\pm|j}=\frac{t_{j,\pm}}{t_{j,+}+t_{j,-}}.
$$

这给出两个正交态组成的二元子系综；各标签 $j$ 可取任意严格正先验。固定通道 $\Phi$ 后，揭示 $j$ 的条件最优成功概率为

$$
p_{\rm succ}(j|\Phi)
=\frac12\left(1+\frac{\|\Phi(D_j)\|_1}{\|D_j\|_1}\right).
$$

所以 $\|\Phi(D_j)\|_1=\|D_j\|_1$ 恰好等价于该子系综的完美判别。可逆性使两态的支持投影正好是 $P_j$ 和 $I-P_j$，因而它们生成的含单位代数就是 $\mathfrak A$。定号的 $D_j$ 在任意 CPTP 通道下都保范数，且只加入 $0$ 或 $I$，可以略去；若全部定号，则 $\mathfrak A=\mathbb C I$、$q_{\rm free}=1$。因此这里的 $q_{\rm free}=\max_kd_k$ 是上述既有判据在加权差任务上的应用。把全部经典分区也计入的 $d_{\rm all}=\sum_kd_k$ 则由本节前面的完整输出下界与达到构造证明。

精确测量压缩及去除重复块的构造另见 Bluhm、Rauber 与 Wolf，*Quantum Compression Relative to a Set of Measurements*，[Definition 4.1、Proposition 6.4 与 Theorem 7.1](https://arxiv.org/html/1708.04898)。该文允许免费经典侧信息，其压缩维数对应这里的 $q$；Theorem 7.1 给出最大矩阵块维数的上界。对于一般非投影效应，不能直接使用这里的 $0/1$ 刚性或宣称生成代数就决定精确压缩维数；该文的一般问题保留了这一区别。输入加权差的可逆性、输出的有限维性以及两种资源的计数口径均属于本定理条件。证毕。

**命题 41.2（五维输入的三维输出与二维量子寄存器）。** 令

$$
\mathcal H=(\mathbb C^2\otimes\mathbb C^2)\oplus\mathbb C,
\qquad P_0=|0\rangle\langle0|,
\qquad P_+=|+\rangle\langle+|,
\qquad |+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
$$

并取密度矩阵

$$
A=\left(\frac34P_0\otimes\frac{I_2}{2}\right)\oplus\frac14,
\qquad
J=\left(\frac12P_+\otimes\frac{I_2}{2}\right)\oplus\frac12,
$$

以及权重 $c_1=1/2$、$c_2=1$。两个加权差均可逆，正谱投影生成的代数为

$$
\mathfrak A=(M_2(\mathbb C)\otimes I_2)\oplus\mathbb C.
$$

因此

$$
\boxed{d_{\rm all}=3,\qquad q_{\rm free}=2.}
$$

两项量子范数分别为

$$
\|D_{1/2}\|_1=1,\qquad
\|D_1\|_1=\frac{\sqrt{13}+1}{4}.
$$

达到完整输出维数三的通道可以丢弃第二个量子比特的状态，因而无需恢复全部五维输入状态。

证明。$A,J$ 均半正定，且迹分别为 $3/4+1/4=1$、$1/2+1/2=1$。直接分块可得

$$
D_t=E_t\otimes\frac{I_2}{2}\ \oplus\left(\frac t4-\frac12\right),
\qquad
E_t=\begin{pmatrix}
3t/4-1/4&-1/4\\
-1/4&-1/4
\end{pmatrix}.
$$

由于 $\det E_t=-3t/16<0$，$E_t$ 有一正一负两个特征值。在 $t=1/2,1$ 时，末尾标量也严格为负，所以两项 $D_t$ 均可逆。$E_t$ 的迹为 $(3t-2)/4$，因而

$$
\|E_t\|_1=\frac{\sqrt{9t^2+4}}4,
\qquad
\|D_t\|_1=\frac{\sqrt{9t^2+4}+2-t}{4}
\quad(t=1/2,1).
$$

这里使用了 $\|I_2/2\|_1=1$。代入两个权重即得到所列范数。

记 $P_t^{(2)}$ 为 $E_t$ 的正谱投影，则

$$
P_t=P_t^{(2)}\otimes I_2\oplus0.
$$

两个二阶投影具体为

$$
P_{1/2}^{(2)}=\frac15\begin{pmatrix}4&-2\\-2&1\end{pmatrix},
\qquad
P_1^{(2)}=\frac12\left[
I_2+\frac1{\sqrt{13}}\begin{pmatrix}3&-2\\-2&-3\end{pmatrix}
\right].
$$

直接相乘有

$$
[P_{1/2}^{(2)},P_1^{(2)}]
=\frac3{5\sqrt{13}}\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\qquad
[P_{1/2},P_1]^2=-\frac9{325}(I_4\oplus0).
$$

因此中央投影 $I_4\oplus0$ 及其补投影都属于 $\mathfrak A$。两个二阶投影不对易，故生成 $M_2(\mathbb C)$：在其中一个投影的本征基内，另一个投影有非零非对角元，用左右谱投影夹取便得到两个非对角矩阵单位，再加上两个对角投影即可。这说明四维中央块上的生成代数是 $M_2(\mathbb C)\otimes I_2$，末尾中央块是 $\mathbb C$；反向包含关系由两个生成元的分块形式直接成立。故所列代数精确，定理 41.1 给出 $3$ 与 $2$ 两种资源值。

具体的三维达到通道为

$$
\mathcal C_0(X)=\operatorname{tr}_2(X_{11})\oplus X_{22},
$$

其中 $X_{11}$ 是输入的四维对角块，$X_{22}$ 是末尾标量块。它将重复因子取偏迹，并保留中央分区标签。对两个不同纯输入

$$
\rho_r=(P_0\otimes|r\rangle\langle r|)\oplus0,
\qquad r=0,1,
$$

有

$$
\mathcal C_0(\rho_0)=\mathcal C_0(\rho_1)=P_0\oplus0.
$$

所以这个达到压缩没有恢复全部五维输入的左逆。它精确保留的是所列判别任务要求的谱投影代数；第二个量子比特的区别不属于这些观测量。若经典标签免费，同一个中央分块构造使用一个二维量子寄存器及两个经典标签即可，符合 $q_{\rm free}=2$。证毕。

## 追加锚（新终端）

## 42. 有限量子存储下的最优值达到与严格资源差距

**定理 42.1（免费经典标签的有限达到界）。** 设输入空间为 $\mathbb C^D$，$D\ge1$，$A,J$ 为该空间上的密度矩阵。给定有限正权重表

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,
\qquad D_j=c_jA-J,
$$

以及一个整数 $1\le q\le D$。存储阶段可以使用任意有限个免费经典标签，每个标签携带一个至多 $q$ 维的量子系统；不足 $q$ 维的分支可以补零嵌入 $\mathbb C^q$。通道预先固定，不能依赖后来揭示的实际权重。

具体地，允许任意有限 $n\ge1$ 及完全正映射

$$
\Phi_\ell:\mathbb C^{D\times D}\longrightarrow
\mathbb C^{q\times q},\qquad 1\le\ell\le n,
$$

满足

$$
\sum_{\ell=1}^n\operatorname{tr}\Phi_\ell(X)
=\operatorname{tr}X,
$$

于是总体 CPTP 存储为

$$
\Phi(X)=\bigoplus_{\ell=1}^n\Phi_\ell(X).
$$

各分支保留其未归一化输出，所有标签均计入最终分数，不允许后选择。定义

$$
V_q=\sup_{\substack{n<\infty\\\Phi\ \mathrm{as\ above}}}
\sum_{j=1}^m\|\Phi(D_j)\|_1
=\sup_{\substack{n<\infty\\\Phi\ \mathrm{as\ above}}}
\sum_{\ell=1}^n\sum_{j=1}^m
\|\Phi_\ell(D_j)\|_1.
$$

则这个上确界由至多 $D^2$ 个非零经典分支达到，并有有限变分公式

$$
\boxed{
V_q=
\max_{\substack{E_1,\ldots,E_{D^2}\ge0\\
\operatorname{rank}E_\ell\le q\ (1\le\ell\le D^2)\\
\sum_{\ell=1}^{D^2}E_\ell=I_D}}
\sum_{\ell=1}^{D^2}\sum_{j=1}^m
\bigl\|\sqrt{E_\ell}\,D_j\sqrt{E_\ell}\bigr\|_1.
}
$$

这里允许零效应。公式中的平方根取正平方根，优化变量均为输入空间上的效应；输出量子维数仍是 $q$，并未扩大到 $D$。

进一步，若所有 $D_j$ 均可逆，令

$$
P_j=\mathbf1_{(0,\infty)}(D_j),\qquad
\mathfrak A=C^*(I_D,P_1,\ldots,P_m)
\cong\bigoplus_{k=1}^s
\left(M_{d_k}(\mathbb C)\otimes I_{r_k}\right),
\qquad q_*=\max_k d_k,
$$

其中 $r_k\ge1$ 为输入表示的重数。则

$$
\boxed{
V_q=\sum_{j=1}^m\|D_j\|_1
\quad\Longleftrightarrow\quad q\ge q_*.
}
$$

因此，对每个固定的候选对、权重表与整数 $q<q_*$，存在严格正的最优总损失

$$
\Delta_q:=\sum_{j=1}^m\|D_j\|_1-V_q>0.
$$

增加有限经典标签数不能使这个损失趋于零。

证明。先把每个分支的完全正映射写成有限 Kraus 和

$$
\Phi_\ell(X)=\sum_a K_{\ell a}XK_{\ell a}^\dagger,
\qquad K_{\ell a}:\mathbb C^D\longrightarrow\mathbb C^q,
\qquad
\sum_{\ell,a}K_{\ell a}^\dagger K_{\ell a}=I_D.
$$

改用新的存储仪器，将 $(\ell,a)$ 作为经典标签，每个分支只使用一个 Kraus 算子：

$$
\widetilde\Phi(X)
=\bigoplus_{\ell,a}K_{\ell a}XK_{\ell a}^\dagger.
$$

这是优化域内另一个合法 CPTP 通道。对每个 $j$，三角不等式给出

$$
\sum_\ell\|\Phi_\ell(D_j)\|_1
\le\sum_{\ell,a}\|K_{\ell a}D_jK_{\ell a}^\dagger\|_1.
$$

故这个替换不降低目标值。它使用的是优化时重新选择仪器的自由；没有假定一个已经实现且丢弃环境的通道，还能事后取回其 Kraus 标签。全部新增标签仍保留在输出中，没有删去不利分支。

对一个这样的算子 $K$，置

$$
E=K^\dagger K\ge0,\qquad \operatorname{rank}E\le q.
$$

极分解 $K=U\sqrt E$ 中，$U$ 在 $\operatorname{supp}E$ 上为等距映射。矩阵 $\sqrt E D_j\sqrt E$ 的支撑包含于该子空间，因此等距嵌入只增添零特征值，并有

$$
\|KD_jK^\dagger\|_1
=\|U\sqrt E D_j\sqrt E U^\dagger\|_1
=\|\sqrt E D_j\sqrt E\|_1.
$$

反过来，对任意有限效应表

$$
E_\ell\ge0,\qquad \operatorname{rank}E_\ell\le q,
\qquad \sum_\ell E_\ell=I_D,
$$

为每个非零效应选择等距映射

$$
U_\ell:\operatorname{supp}E_\ell\longrightarrow\mathbb C^q,
\qquad K_\ell=U_\ell\sqrt{E_\ell}.
$$

把 $U_\ell$ 在支撑外延拓为零，并对零效应取 $K_\ell=0$。于是 $K_\ell^\dagger K_\ell=E_\ell$，通道

$$
\Phi_E(X)=\bigoplus_\ell K_\ell X K_\ell^\dagger
$$

为 CPTP，且逐项达到效应表的范数目标。故原上确界精确等于所有有限秩受限效应表上

$$
\sum_\ell f(E_\ell),\qquad
f(E)=\sum_{j=1}^m\|\sqrt E D_j\sqrt E\|_1
$$

的上确界。

现在证明效应数可以统一限制为 $D^2$。函数 $f$ 在正半定矩阵上连续，且对每个 $t\ge0$ 有

$$
f(tE)=t f(E).
$$

从任意有限可行效应表出发，先删去零效应。若非零效应数大于 $D^2$，由于 $D$ 阶 Hermitian 矩阵构成 $D^2$ 维实向量空间，存在不全为零的实数 $a_\ell$，满足

$$
\sum_\ell a_\ell E_\ell=0.
$$

每个非零效应的迹严格为正。对该等式取迹可知，$a_\ell$ 必须同时含有正数和负数。把整组系数变号也保持该关系，故可以选择方向使

$$
b:=\sum_\ell a_\ell f(E_\ell)\ge0.
$$

沿该方向取

$$
t_*:=\min_{\ell:\,a_\ell<0}\frac{-1}{a_\ell}>0,
\qquad
E'_\ell=(1+t_*a_\ell)E_\ell.
$$

所有缩放系数非负，至少一个原非零效应变为零。正性、秩上界以及总和为 $I_D$ 的条件均保持；齐次性给出

$$
\sum_\ell f(E'_\ell)
=\sum_\ell f(E_\ell)+t_*b
\ge\sum_\ell f(E_\ell).
$$

每次至少删去一个非零效应，有限次重复后得到至多 $D^2$ 个效应，且目标不降。这一消去从任意有限方案开始，不预先假设上确界已经达到。

把效应表补零至 $D^2$ 项。所列固定槽位可行集非空：选一个输入正交基的 $D$ 个秩一投影，再补零即可，因为 $q\ge1$。每个效应自动满足 $0\le E_\ell\le I_D$。正性、总和以及 $\operatorname{rank}E_\ell\le q$ 都是闭条件，后者可由所有 $(q+1)$ 阶子式为零表述。因此可行集在有限维实向量空间中闭且有界，故紧。正矩阵平方根与迹范数连续，所以目标达到最大值。结合前面的消去与物理实现，得到有限变分公式和至多 $D^2$ 个非零经典分支的达到结论。秩约束通常不凸；这个紧集公式不自动给出一般闭式或半正定规划。

最后假设全部 $D_j$ 可逆。任意 CPTP 通道逐项满足

$$
\|\Phi(D_j)\|_1\le\|D_j\|_1.
$$

若 $q\ge q_*$，第 41 节的中心分支与重数偏迹构造使用免费经典标签和至多 $q_*$ 维量子分支，同时保留全部范数。将其分支嵌入 $\mathbb C^q$，得到 $V_q=\sum_j\|D_j\|_1$。

若 $q<q_*$ 而两者相等，前面已经证明最大值由一个有限分支通道达到。各项损失均非负而总和为零，故这个通道对每项都有

$$
\|\Phi(D_j)\|_1=\|D_j\|_1.
$$

这与第 41 节的必要条件 $q\ge\max_k d_k$ 矛盾。因此 $\Delta_q>0$。严格差距来自达到性和精确无损障碍共同作用；只知道没有无损通道，还不足以排除一列损失趋于零的通道。

上面的有限达到证明本身不要求任何 $D_j$ 可逆，也适用于任意固定有限组 Hermitian 输入差。可逆性只用于最后调用第 41 节的符号投影代数判据。这里没有给出跨候选对或权重表统一的正损失常数，也没有从小损失推出一般恢复误差界。

所用标量依赖扰动与 D'Ariano、Lo Presti、Perinotti，*Classical randomness in quantum measurements*，[推论 7 及其证明](https://arxiv.org/abs/quant-ph/0408115) 中的标准 POVM 方法一致；本节利用目标的正齐次性选择不降方向，同时保持各效应的秩上界。Bluhm、Rauber、Wolf，*Quantum compression relative to a set of measurements*，[引理 5.2、引理 5.3 与定理 5.1](https://arxiv.org/abs/1708.04898) 也通过限制经典辅助规模与紧性证明压缩维数的稳定性，但其 $D^4$ 标签界用于在保持给定复合通道不变的条件下重构压缩与解压缩映射。本节只优化所列有限范数总分，允许更换存储仪器并在权重揭示后分别选择最终判别；$D^2$ 界不承担保持原复合通道或共同解压缩映射的要求。证毕。

## 追加锚（新终端）

## 43. 奇异加权差的交叉支撑判据与经典无损存储

**定理 43.1（有序权重的正负支撑判据）。** 设 $A,J$ 为 $\mathbb C^D$ 上的密度矩阵，$D\ge1$，预先给定有限权重表

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,\qquad D_j=c_jA-J.
$$

允许 $D_j$ 奇异、定号或为零。分别记正谱、负谱及零谱投影为

$$
P_j^+=\mathbf1_{(0,\infty)}(D_j),\qquad
P_j^-=\mathbf1_{(-\infty,0)}(D_j),\qquad
Z_j=I_D-P_j^+-P_j^-.
$$

存在一个有限经典输出 CPTP 通道，在实际权重揭示前固定，并满足

$$
\|\Phi(D_j)\|_1=\|D_j\|_1
\qquad(1\le j\le m),
$$

当且仅当

$$
\boxed{
P_i^+P_j^-=0\qquad\text{对全部 }1\le i<j\le m.
}
$$

条件成立时，令

$$
\mathcal S_j=\operatorname{span}
\{\operatorname{ran}P_i^+:1\le i\le j\},
\qquad Q_j=\operatorname{proj}_{\mathcal S_j},
\qquad Q_0=0,\quad Q_{m+1}=I_D.
$$

这些投影满足

$$
Q_0\le Q_1\le\cdots\le Q_m\le Q_{m+1},
\qquad P_j^+\le Q_j\le I_D-P_j^-.
$$

因此

$$
M_k=Q_{k+1}-Q_k,\qquad 0\le k\le m,
$$

是一组共同投影测量；删去零效应后，至多 $\min\{D,m+1\}$ 个经典标签足以同时无损。这里给出的是达到该任务的标签上界，没有断言每个输入都需要这么多标签。

证明。先确定奇异加权差的全部最优效应。对任意 Hermitian 矩阵 $H$，写其 Jordan 分解为

$$
H=H_+-H_-,\qquad H_+,H_-\ge0,\qquad H_+H_-=0.
$$

令 $P^+,P^-,Z$ 为相应的正、负、零谱投影。对效应 $0\le F\le I_D$，有

$$
\operatorname{tr}H_+-\operatorname{tr}(FH)
=\operatorname{tr}((I_D-F)H_+)+\operatorname{tr}(FH_-)
\ge0.
$$

两项均非负。正矩阵乘积的迹为零，等价于它们的正平方根乘积为零。因此等号成立，当且仅当 $F$ 在 $\operatorname{ran}P^+$ 上为恒等、在 $\operatorname{ran}P^-$ 上为零。由于 $F$ 自伴，这两个子空间与其正交补之间的非对角块也为零；于是全部最优效应精确写成

$$
\boxed{
F=P^++R,\qquad 0\le R\le Z,
}
$$

等价地，$P^+\le F\le I_D-P^-$。它们都满足二元判别的变分等式

$$
2\operatorname{tr}(FH)-\operatorname{tr}H=\|H\|_1.
$$

这里 $0\le R\le Z$ 已保证 $R$ 支撑在零特征子空间。若 $H$ 可逆，该自由消失，最优效应唯一；若 $H=0$，整个效应区间都最优。

对加权密度矩阵差，这个完整最优效应区间是量子 Neyman–Pearson 引理的标准形式，见 Jenčová，*Reversibility conditions for quantum operations*，[引理 7](https://arxiv.org/abs/1107.0453)。在该引理中取 $\sigma=A$、$\rho=J$、$t=1/c_j$，则 $\sigma-t\rho=D_j/c_j$；因为 $c_j>0$，正、负、零谱子空间以及最优效应集合均不改变。

现设存在逐项无损的有限经典存储。它由某个有限 POVM $(E_\ell)_\ell$ 给出，输出第 $\ell$ 个标签的概率为 $\operatorname{tr}(E_\ell\rho)$。定义

$$
a_\ell=\operatorname{tr}(E_\ell A)\ge0,\qquad
b_\ell=\operatorname{tr}(E_\ell J)\ge0,
$$

以及输入效应

$$
F_j=\sum_{\ell:\,c_ja_\ell-b_\ell>0}E_\ell.
$$

由经典范数的逐标签绝对值表达，

$$
2\operatorname{tr}(F_jD_j)-\operatorname{tr}D_j
=\sum_\ell|c_ja_\ell-b_\ell|
=\|\Phi(D_j)\|_1
=\|D_j\|_1.
$$

因此每个 $F_j$ 都是对应加权差的最优效应。因为 $a_\ell\ge0$，每个 $c_ja_\ell-b_\ell$ 随 $j$ 不减，正号标签集合随之嵌套，所以

$$
F_i\le F_j\qquad(i<j).
$$

定义直接使用严格正号，不需要除以 $a_\ell$。当 $a_\ell=0$ 时，由 $b_\ell\ge0$，该标签永不入选；读数恰为零时也排除，不影响上述等式与嵌套性。

固定 $i<j$。最优效应条件给出

$$
P_i^+\le F_i\le F_j\le I_D-P_j^-.
$$

对任意 $v\in\operatorname{ran}P_j^-$，夹取此不等式得到 $\langle v,P_i^+v\rangle=0$，故 $P_i^+v=0$。于是 $P_i^+P_j^-=0$，证明必要性。这里没有将一般 $F_j$ 假定为投影，也没有从两效应的共同来源直接断言它们对易。

反过来，设所有交叉支撑条件成立。对 $i\le j$，$\operatorname{ran}P_i^+$ 与 $\operatorname{ran}P_j^-$ 正交；$i=j$ 的情形由谱分解自动成立。因此陈述中的 $\mathcal S_j$ 包含 $\operatorname{ran}P_j^+$，并且与 $\operatorname{ran}P_j^-$ 正交，给出

$$
P_j^+\le Q_j\le I_D-P_j^-.
$$

子空间 $\mathcal S_j$ 递增，所以 $Q_j$ 是嵌套的最优投影扩展。相邻投影差 $M_k=Q_{k+1}-Q_k$ 均为正交投影，彼此正交，且总和为 $I_D$。用这组 PVM 作经典存储，并在权重 $c_j$ 揭示后把 $k<j$ 的标签归为第一种判别结果，则其输入效应为

$$
\sum_{k=0}^{j-1}M_k=Q_j.
$$

这个效应达到 $D_j$ 的二元最优值。存储后范数至少为该决策给出的 $\|D_j\|_1$，迹范数收缩性又给出反向不等式，因而逐项无损。投影总数为 $m+1$，非零项又是两两正交的非零子空间投影，所以非零数不超过 $D$。全部标签均保留，没有后选择。

一般有限组判别问题的正确条件，是能够从各自的最优效应集合中选出彼此兼容的二元测量；兼容指它们都是某一共同 POVM 的经典后处理。对任意 Hermitian 差，上述计算把每个最优集合具体写成 $P_j^++[0,Z_j]$。兼容的一组选取产生共同经典存储，反向则由存储后的最优决策得到这样的选取。最优效应不唯一时，只需存在一组兼容选取；这一一般原则见 Carmeli、Heinosaari、Toigo，*State discrimination with post-measurement information and incompatibility of quantum measurements*，[定理 1 及其后的说明](https://arxiv.org/html/1804.09693)。对本节的 $D_j=c_jA-J$，第 37 节的系综归一化同样适用。

本节在同一候选对与递增正权重的条件下，利用逐标签读数的单调性，把兼容性进一步化为所列交叉支撑判据，并明确构造嵌套的投影扩展。若所有 $D_j$ 可逆，则 $I_D-P_j^-=P_j^+$，交叉条件退化为 $P_i^+\le P_j^+$，与第 38 节在有序权重下得到的嵌套判据一致。奇异情形保留了零特征子空间的选择自由，不能直接要求原始正谱投影彼此对易。证毕。

**命题 43.2（严格正定候选的奇异不定反例）。** 在 $\mathbb C^3$ 的标准基 $e_1,e_2,e_3$ 下取

$$
A=\frac18\begin{pmatrix}
2&3&0\\3&5&0\\0&0&1
\end{pmatrix},\qquad
J=\frac1{27}\begin{pmatrix}
5&9&0\\9&17&0\\0&0&5
\end{pmatrix},
\qquad c=\frac89,\quad d=\frac{32}{27}.
$$

这两个候选都是严格正定密度矩阵，$c<d$。令 $D_t=tA-J$，则

$$
D_c=\frac1{27}\begin{pmatrix}
1&0&0\\0&-2&0\\0&0&-2
\end{pmatrix},\qquad
D_d=\frac1{27}\begin{pmatrix}
3&3&0\\3&3&0\\0&0&-1
\end{pmatrix}.
$$

两个差都不定，$D_c$ 可逆而 $D_d$ 奇异。它们的正谱投影不对易，但标准三结果 PVM 同时保留

$$
\|D_c\|_1=\frac5{27},\qquad
\|D_d\|_1=\frac7{27}.
$$

对这两个任务，最少经典标签数和最小完整量子输出维数均为三；若经典标签免费，所需量子寄存器维数为一。

证明。$A,J$ 的迹均为一。它们的顺序主子式分别为

$$
\left(\frac14,\frac1{64},\frac1{512}\right),\qquad
\left(\frac5{27},\frac4{729},\frac{20}{19683}\right),
$$

全部严格为正，故二者严格正定。代入两个权重得到陈述中的加权差。$D_c$ 的特征值为 $1/27,-2/27,-2/27$；$D_d$ 的特征值为 $6/27,0,-1/27$，因此二者均含有严格正、负特征值，范数也是所列值。

令

$$
u=\frac{e_1+e_2}{\sqrt2},\qquad
w=\frac{e_1-e_2}{\sqrt2}.
$$

相应投影为

$$
P_c^+=|e_1\rangle\langle e_1|,\qquad
P_d^+=|u\rangle\langle u|,\qquad
P_d^-=|e_3\rangle\langle e_3|,\qquad
Z_d=|w\rangle\langle w|.
$$

直接计算得

$$
[P_c^+,P_d^+]
=\frac12\begin{pmatrix}0&1&0\\-1&0&0\\0&0&0\end{pmatrix}\ne0.
$$

但 $P_c^+P_d^-=0$，所以满足定理 43.1 的交叉支撑条件。其嵌套最优投影是

$$
Q_c=|e_1\rangle\langle e_1|,\qquad
Q_d=|e_1\rangle\langle e_1|+|e_2\rangle\langle e_2|
=P_d^++Z_d.
$$

对应 PVM 恰为三个标准基投影。测量两个差得到的未归一化对角读数分别为

$$
\frac1{27}(1,-2,-2),\qquad
\frac1{27}(3,3,-1).
$$

绝对值之和分别为 $5/27$ 与 $7/27$，直接验证共同经典测量无损。

现在证明整个输出至少需要三维。设任意有限维 CPTP 通道 $\Phi(X)=\sum_a K_aXK_a^\dagger$ 对这两项无损，并令

$$
\mathcal R_r=\operatorname{span}_a\{K_ae_r\},
\qquad r=1,2,3.
$$

由迹保持，$\sum_a\|K_ae_r\|^2=1$，所以每个 $\mathcal R_r$ 都非零。对正矩阵 $B,C$，$\|B-C\|_1=\operatorname{tr}B+\operatorname{tr}C$ 当且仅当其支撑正交：取 $B-C$ 的最优正谱投影 $F$，等号要求 $\operatorname{tr}((I-F)B)=\operatorname{tr}(FC)=0$，分别将两个支撑置于 $F$ 的值域与核中；反向由正交分块成立。

将这一条件用于 $D_c$ 的正负部分，无损性给出

$$
\mathcal R_1\perp\mathcal R_2,\qquad
\mathcal R_1\perp\mathcal R_3.
$$

再用于 $D_d=(6|u\rangle\langle u|-|e_3\rangle\langle e_3|)/27$，得到对所有 $a,b$ 都有

$$
\langle K_a(e_1+e_2),K_be_3\rangle=0.
$$

其中 $\langle K_ae_1,K_be_3\rangle=0$ 已由第一项确定，相减可得 $\langle K_ae_2,K_be_3\rangle=0$。所以三个非零子空间 $\mathcal R_1,\mathcal R_2,\mathcal R_3$ 两两正交，整个输出空间至少三维。标准三标签通道达到该下界，也证明两个经典标签不够。免费标签的口径下，同一实现为纯经典输出，故最小量子寄存器维数为一。

最后核对第 41 节公式的适用边界。此例的标准正谱投影生成

$$
C^*(I_3,P_c^+,P_d^+)=M_2(\mathbb C)\oplus\mathbb C.
$$

事实上，上面对易子的平方为 $-(I_2\oplus0)/4$，故两个中央分区投影都在生成代数中；在前二维内，两个不对易秩一投影生成全部 $M_2(\mathbb C)$，末尾为标量块。因此若删去第 41 节的可逆性前提而直接使用其最大块公式，会给出量子寄存器维数二，与这里已达到且最小的维数一矛盾。其完整输出公式在此恰好仍给出三，不能据这个例子声称该数值也失效。

此例的经典无损并不来自某一项半正定而自动保范数：两项都不定，保留它们的最优判别仍需要三个输出维数。改变判据的是 $D_d$ 的零特征子空间；把它加入正谱投影后，最优效应成为能与第一项共同读取的 $Q_d$。证毕。

## 追加锚（新终端）

## 44. 交叉支撑的定量损失界

**定理 44.1（有序权重的显式经典损失下界）。** 沿用第 43 节的有限维任务：$A,J$ 为 $\mathbb C^D$ 上的密度矩阵，$D\ge1$，且

$$
m\ge2,\qquad 0<c_1<\cdots<c_m,\qquad D_k=c_kA-J.
$$

允许这些加权差奇异。固定 $i<j$，假设相关的正、负谱投影

$$
P=P_i^+=\mathbf1_{(0,\infty)}(D_i)\ne0,\qquad
Q=P_j^-=\mathbf1_{(-\infty,0)}(D_j)\ne0.
$$

在这两个非零支撑上定义严格正的谱间隙

$$
\alpha=\min\{\lambda>0:\lambda\in\operatorname{spec}D_i\},
\qquad
\beta=\min\{-\lambda:\lambda<0,\ \lambda\in\operatorname{spec}D_j\}.
$$

令 $r_P=\operatorname{rank}P$、$r_Q=\operatorname{rank}Q$，并记

$$
\boxed{
\mathsf B_{ij}=\alpha r_P+\beta r_Q-\|\alpha P-\beta Q\|_1.
}
$$

对任意预先固定的有限经典输出 CPTP 通道 $\Phi$，令

$$
\delta_k(\Phi)=\|D_k\|_1-\|\Phi(D_k)\|_1.
$$

则

$$
\boxed{
\delta_i(\Phi)+\delta_j(\Phi)\ge\mathsf B_{ij}\ge0,
\qquad
\mathsf B_{ij}>0\ \Longleftrightarrow\ PQ\ne0.
}
$$

特别地，一对违反第 43 节交叉支撑条件的权重，就给出对所有有限经典存储统一有效的严格正总损失下界。它针对固定的候选对与权重表，不是跨任务的统一常数。

若 $P,Q$ 都为秩一投影，记 $\chi=\operatorname{tr}(PQ)\in[0,1]$，则

$$
\boxed{
\mathsf B_{ij}
=\alpha+\beta-\sqrt{(\alpha+\beta)^2-4\alpha\beta\chi}.
}
$$

若相关支撑之一为零，则不使用上述谱间隙定义；这一对权重的下界可直接记为零。$\mathsf B_{ij}$ 是整体判别损失的下界，未断言它等于最优总损失。

证明。固定经典存储对应的有限 POVM $(E_\ell)_\ell$。对每个权重，选取它在经典输出上的正号决策并拉回输入：

$$
F_k=\sum_{\ell:\,c_k\operatorname{tr}(E_\ell A)-\operatorname{tr}(E_\ell J)>0}E_\ell.
$$

与第 43 节相同，各输出读数随 $c_k$ 不减，所以

$$
0\le F_i\le F_j\le I_D.
$$

这里的 $F_k$ 实现存储后的最优二元决策；不要求它在原输入上已经无损，也不要求它是投影。

写 $D_k=D_{k,+}-D_{k,-}$。利用 $F_k$ 的经典最优性，单项损失有精确表达

$$
\begin{aligned}
\delta_k(\Phi)
&=\|D_k\|_1-2\operatorname{tr}(F_kD_k)+\operatorname{tr}D_k\\
&=2\operatorname{tr}((I_D-F_k)D_{k,+})
+2\operatorname{tr}(F_kD_{k,-}).
\end{aligned}
$$

右端两项都非负。谱间隙定义给出 $D_{i,+}\ge\alpha P$ 和 $D_{j,-}\ge\beta Q$，所以

$$
\delta_i(\Phi)+\delta_j(\Phi)
\ge2\alpha\operatorname{tr}((I_D-F_i)P)
+2\beta\operatorname{tr}(F_jQ).
$$

再由 $F_i\le F_j$ 得到

$$
\begin{aligned}
\delta_i(\Phi)+\delta_j(\Phi)
&\ge2\left[\alpha\operatorname{tr}((I_D-F_i)P)
+\beta\operatorname{tr}(F_iQ)\right]\\
&\ge2\min_{0\le F\le I_D}
\left[\alpha\operatorname{tr}((I_D-F)P)
+\beta\operatorname{tr}(FQ)\right].
\end{aligned}
$$

这个辅助最小值可以精确求出。令 $T=\alpha P-\beta Q$，由正谱投影达到的变分公式，有

$$
\max_{0\le F\le I_D}\operatorname{tr}(FT)
=\operatorname{tr}T_+
=\frac{\|T\|_1+\operatorname{tr}T}{2}.
$$

因而

$$
\begin{aligned}
&2\min_{0\le F\le I_D}
\left[\alpha\operatorname{tr}((I_D-F)P)
+\beta\operatorname{tr}(FQ)\right]\\
&=2\alpha r_P-2\operatorname{tr}T_+
=\alpha r_P+\beta r_Q-\|\alpha P-\beta Q\|_1
=\mathsf B_{ij}.
\end{aligned}
$$

这证明下界。辅助二元优化的精确性不使前面的谱间隙替换、丢去非负项及 $F_i\le F_j$ 的估计自动成为等号。

接着判断何时严格为正。三角不等式给出

$$
\|\alpha P-\beta Q\|_1\le\alpha r_P+\beta r_Q.
$$

第 43 节已证明，对两个正矩阵，差的迹范数等于两迹之和，当且仅当它们的支撑正交。这里 $\alpha,\beta>0$，两个支撑正好是 $\operatorname{ran}P$ 与 $\operatorname{ran}Q$，所以

$$
\mathsf B_{ij}=0\ \Longleftrightarrow\ PQ=0.
$$

如果整组任务中存在 $P_i^+P_j^-\ne0$，这两个投影自动非零，可以使用本定理。其余单项损失也非负，因此整组总损失至少为该对权重的 $\mathsf B_{ij}>0$。这个显式结论直接排除了通过增加有限经典标签数而把总损失逼近零的方案。

最后计算秩一情形。写 $P=|p\rangle\langle p|$、$Q=|q\rangle\langle q|$，其中 $p,q$ 为单位向量，则 $\chi=|\langle p,q\rangle|^2$。若 $\chi<1$，在二维空间 $\operatorname{span}\{p,q\}$ 上，$T$ 的迹与行列式分别为

$$
\operatorname{tr}T=\alpha-\beta,\qquad
\det T=-\alpha\beta(1-\chi)<0.
$$

其两个非零特征值异号，故

$$
\|T\|_1
=\sqrt{(\alpha-\beta)^2+4\alpha\beta(1-\chi)}
=\sqrt{(\alpha+\beta)^2-4\alpha\beta\chi}.
$$

在正交补上只有零特征值。若 $\chi=1$，则 $P=Q$，有 $\|T\|_1=|\alpha-\beta|$，同一个根式仍成立，此时 $\mathsf B_{ij}=2\min\{\alpha,\beta\}$。这给出完整的秩一公式，包括 $\chi=0$ 时下界为零的情形。

上述辅助优化是标准 Helstrom 二元判别公式的直接应用。具体令 $C=\alpha r_P+\beta r_Q$，把 $P/r_P$ 与 $Q/r_Q$ 视为两个密度矩阵，先验分别取 $\alpha r_P/C$ 与 $\beta r_Q/C$；其最小错误概率乘以 $2C$ 就是 $\mathsf B_{ij}$。该公式及正谱投影达到策略见 Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[Theorem 2.1](https://arxiv.org/html/quant-ph/0608014)，其中明确归于 Helstrom。本节把第 43 节的有序决策效应与这个标准二元公式结合；不将辅助公式本身作为新结果。证毕。

**命题 44.2（交叉支撑界与第 40 节下界互不支配）。** 在两者共同适用的量子比特任务中，定理 44.1 的 $\mathsf B_{ij}$ 与定理 40.1 的 $\mathsf L$ 没有普遍的大小顺序。

具体地，取

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
J=\frac1{10}\begin{pmatrix}9&3\\3&1\end{pmatrix},
\qquad c=\frac14,\quad d=4,
\qquad \mu=\frac{\sqrt{265}-15}{40}>0.
$$

两候选不对易，两个加权差都严格不定。此时两个下界为

$$
\mathsf B_{cd}=\mu\left(5-\sqrt{\frac{677}{53}}\right),
\qquad
\mathsf L=2\mu\left(5-\sqrt{\frac{1125}{53}}\right),
$$

并且

$$
\boxed{0<\mathsf L<\mu<\mathsf B_{cd}.}
$$

另一方面，在命题 40.2 的混态例中，$\mathsf B_{12}=\mathsf L/2>0$，因此第 40 节的下界严格更强。

证明。这里 $A$ 是秩一投影，$J=vv^\dagger/10$，其中 $v=(3,1)^{\mathsf T}$ 且 $v^\dagger v=10$，所以两者都是纯态密度矩阵。由于 $J$ 的非对角元非零，$[A,J]\ne0$。两个加权差为

$$
D_c=\frac1{20}\begin{pmatrix}-13&-6\\-6&-2\end{pmatrix},
\qquad
D_d=\frac1{10}\begin{pmatrix}31&-3\\-3&-1\end{pmatrix}.
$$

它们的行列式分别为 $-1/40$ 与 $-2/5$，因此都严格不定。迹分别为 $-3/4$ 与 $3$，迹范数分别为

$$
\|D_c\|_1=\frac{\sqrt{265}}{20},\qquad
\|D_d\|_1=\frac{\sqrt{265}}5.
$$

按第 40 节的记号，正、负本征值绝对值中的较小者为 $\mu_c=\mu$、$\mu_d=4\mu$。由于 $c<1<d$，$D_c$ 的正本征值较小、$D_d$ 的负本征值绝对值较小，所以定理 44.1 中的两个谱间隙恰为

$$
\alpha=\mu,\qquad\beta=4\mu.
$$

再令 $S_t=2P_t^+-I_2$。直接去迹并除以相应的 $\|D_t\|_1/2$ 得到

$$
S_c=\frac1{\sqrt{265}}\begin{pmatrix}-11&-12\\-12&11\end{pmatrix},
\qquad
S_d=\frac1{\sqrt{265}}\begin{pmatrix}16&-3\\-3&-16\end{pmatrix}.
$$

因此

$$
\kappa=\frac12\operatorname{tr}(S_cS_d)=-\frac{28}{53},
\qquad \eta=|\kappa|=\frac{28}{53},
\qquad
\chi=\operatorname{tr}(P_c^+P_d^-)=\frac{1-\kappa}{2}=\frac{81}{106}.
$$

代入两个定理，根式中的量分别化为

$$
(\alpha+\beta)^2-4\alpha\beta\chi
=\mu^2\frac{677}{53},
$$

$$
\mu_c^2+\mu_d^2+2\mu_c\mu_d\eta
=\mu^2\frac{1125}{53}.
$$

这给出所列两个下界。它们的严格比较只需要有理数平方比较：

$$
\frac{1125}{53}<25,
\qquad
\frac{1125}{53}>\frac{81}{4},
\qquad
\frac{677}{53}<16.
$$

第一式给出 $\mathsf L>0$；第二式给出 $\mathsf L<2\mu(5-9/2)=\mu$；第三式给出 $\mathsf B_{cd}>\mu(5-4)=\mu$。又因 $265>15^2$，$\mu>0$，所有不等号方向确定。

为得到反向的严格比较，取命题 40.2 的

$$
A=\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix},\qquad
J=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},
\qquad c=1,\quad d=2.
$$

该节已经算得

$$
\mu_c=\frac{\sqrt2}{4},\qquad
\mu_d=\frac{\sqrt5-2}{4},\qquad
\kappa=\eta=\frac3{\sqrt{10}}>0.
$$

此时同样有 $\alpha=\mu_c$、$\beta=\mu_d$。把 $\chi=(1-\kappa)/2$ 代入秩一公式，得到

$$
\mathsf B_{12}
=\mu_c+\mu_d-\sqrt{\mu_c^2+\mu_d^2+2\mu_c\mu_d\kappa}
=\frac{\mathsf L}{2}.
$$

由第 40 节的 $\mathsf L>0$，这是严格较小的下界。两个精确例子共同排除了任一方的普遍数值支配关系。

第 44 节的界适用于任意有限输入维数及奇异加权差，第 40 节则同时给出两项量子比特任务的经典损失上下界。在共同适用处可以取两个下界的较大者；这里保留第 40 节的结论，没有用新界替代它，也未把上述纯态例中的任一下界宣称为实际最优损失。证毕。

## 追加锚（新终端）

## 45. 最优分数的连续性与精确存储维数的跳变

**定理 45.1（固定存储预算下的迹范数扰动界）。** 固定整数 $D,m\ge1$ 与 $1\le q\le D$。对 $\mathbb C^D$ 上的任意有限 Hermitian 矩阵表

$$
\mathbf H=(H_1,\ldots,H_m),
$$

沿用第 42 节的存储域：通道输出至任意有限个免费经典标签，每个标签携带至多 $q$ 维量子系统，各分支输出不归一化且不作后选择。定义

$$
V_q(\mathbf H)=\sup_\Phi\sum_{j=1}^m\|\Phi(H_j)\|_1,
\qquad
B(\mathbf H)=\sum_{j=1}^m\|H_j\|_1,
\qquad
\Delta_q(\mathbf H)=B(\mathbf H)-V_q(\mathbf H).
$$

这里不同矩阵表上的最优通道可以不同，但允许的通道集合由同一组 $D,m,q$ 固定。对另一组同维同长矩阵表 $\mathbf H'=(H'_1,\ldots,H'_m)$，令

$$
d_1(\mathbf H,\mathbf H')=
\sum_{j=1}^m\|H_j-H'_j\|_1.
$$

则

$$
\boxed{
|V_q(\mathbf H)-V_q(\mathbf H')|
\le d_1(\mathbf H,\mathbf H'),
\qquad
|\Delta_q(\mathbf H)-\Delta_q(\mathbf H')|
\le2d_1(\mathbf H,\mathbf H').
}
$$

不要求任何输入差可逆。若仅改变同一密度矩阵对 $A,J$ 的权重，令 $H_j=c_jA-J$、$H'_j=c'_jA-J$，则距离精确为

$$
d_1(\mathbf H,\mathbf H')=\sum_{j=1}^m|c_j-c'_j|.
$$

定义最小无损量子寄存器维数

$$
q_{\min}(\mathbf H)=
\min\{q\in\{1,\ldots,D\}:\Delta_q(\mathbf H)=0\}.
$$

第 42 节的达到性使 $\Delta_q=0$ 等价于存在有限标签的逐项无损通道。对每个固定 $q$，集合 $\{\mathbf H:q_{\min}(\mathbf H)\le q\}$ 是闭集。因此 $q_{\min}$ 是下半连续的：在任意固定矩阵表处，足够小的扰动不能降低该处的最小无损量子维数，但可以使它升高。

证明。首先，对 Hermitian 矩阵 $X=X_+-X_-$，正性与迹保持给出

$$
\|\Phi(X)\|_1
\le\|\Phi(X_+)\|_1+\|\Phi(X_-)\|_1
=\operatorname{tr}X_++\operatorname{tr}X_-
=\|X\|_1.
$$

所以 $0\le V_q(\mathbf H)\le B(\mathbf H)$。对任一共同允许通道，反三角不等式与上述收缩性给出

$$
\begin{aligned}
\left|\sum_j\|\Phi(H_j)\|_1
-\sum_j\|\Phi(H'_j)\|_1\right|
&\le\sum_j\|\Phi(H_j-H'_j)\|_1\\
&\le d_1(\mathbf H,\mathbf H').
\end{aligned}
$$

该界对整个允许通道集合一致。先取一侧上确界，再交换两组矩阵表，便得到 $V_q$ 的扰动界；这一步不要求两组最优通道相同，也不预先使用最大值达到性。对 $B$ 直接用反三角不等式同样得到

$$
|B(\mathbf H)-B(\mathbf H')|
\le d_1(\mathbf H,\mathbf H').
$$

将两式相加即得 $\Delta_q$ 的系数二界。仅改变权重时，$H_j-H'_j=(c_j-c'_j)A$，而 $A\ge0$、$\operatorname{tr}A=1$，所以 $\|H_j-H'_j\|_1=|c_j-c'_j|$。

预算从 $q$ 增大时，可以把原输出量子系统等距嵌入较大空间，故 $V_q$ 不减而 $\Delta_q$ 不增。恒等存储使用 $q=D$ 即可无损，所以 $q_{\min}$ 的定义集合非空。第 42 节的有限达到论证对任意有限 Hermitian 表都成立；各项范数损失非负，故达到的总损失为零，当且仅当每项损失为零。由此

$$
\{\mathbf H:q_{\min}(\mathbf H)\le q\}
=\{\mathbf H:\Delta_q(\mathbf H)=0\}.
$$

右端是连续函数的零点集，因此闭，给出下半连续性。更具体地，若 $q_0=q_{\min}(\mathbf H)>1$，则 $\Delta_{q_0-1}(\mathbf H)>0$。只要

$$
d_1(\mathbf H,\mathbf H')
<\frac12\Delta_{q_0-1}(\mathbf H),
$$

扰动界就保证 $\Delta_{q_0-1}(\mathbf H')>0$，从而 $q_{\min}(\mathbf H')\ge q_0$。若 $q_0=1$，同一结论由维数至少为一自动成立。

这里的连续性控制最优分数与最优损失，没有把整数值的精确资源函数断言为连续。所用范数性质是 Schatten 迹范数的标准三角不等式与正算子迹公式；正且保迹映射的迹范数收缩性见 Watrous，*The Theory of Quantum Information*，[推论 3.40 及式 (3.241)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。免费经典标签上的有限达到性由第 42 节承担。证毕。

**命题 45.2（奇异权重处的维数跳变与消失损失）。** 固定命题 43.2 中的严格正定密度矩阵

$$
A=\frac18\begin{pmatrix}2&3&0\\3&5&0\\0&0&1\end{pmatrix},
\qquad
J=\frac1{27}\begin{pmatrix}5&9&0\\9&17&0\\0&0&5\end{pmatrix},
\qquad c=\frac89.
$$

对参数 $-1/2<s<1/2$，令

$$
d_s=\frac{8(4+s)}{27}>c,\qquad
H_1=D_c=cA-J,\qquad H_2(s)=D_{d_s}=d_sA-J.
$$

对每个固定 $s$，存储可以依赖 $A,J,c,d_s$，但实际采用 $c$ 还是 $d_s$ 只在存储结束后揭示。按第 41 节的两种资源口径，最小逐项无损资源为

$$
\boxed{
d_{\rm all}(s)=3\quad(-1/2<s<1/2),
\qquad
q_{\rm free}(s)=
\begin{cases}
2,&-1/2<s<0,\\
1,&0\le s<1/2.
\end{cases}
}
$$

记 $V_1(s)$ 为最优经典存储的范数总分，$\Delta(s)=\|D_c\|_1+\|D_{d_s}\|_1-V_1(s)$。则

$$
\boxed{
\begin{aligned}
&\Delta(s)=0&& (0\le s<1/2),\\
&0<\Delta(s)\le
\frac{\sqrt{36+72s+45s^2}-6-7s}{27}
&&(-1/2<s<0),
\end{aligned}
}
$$

从而 $\lim_{s\to0}\Delta(s)=0$，尽管精确无损的量子维数在 $s=0$ 发生跳变。更一般地，对任意 $q\in\{1,2,3\}$ 和同一区间中的 $s,t$，都有

$$
|V_q(s)-V_q(t)|\le\frac8{27}|s-t|,
\qquad
|\Delta_q(s)-\Delta_q(t)|\le\frac{16}{27}|s-t|.
$$

证明。候选矩阵的正定性与归一化已在命题 43.2 验证。代入得到

$$
27D_c=\operatorname{diag}(1,-2,-2),\qquad
27D_{d_s}=G_s\oplus(s-1),
$$

其中

$$
G_s=\begin{pmatrix}
3+2s&3+3s\\3+3s&3+5s
\end{pmatrix},
\qquad
\det G_s=s(s+3),\qquad
\operatorname{tr}G_s=6+7s>0.
$$

其特征值为

$$
\lambda_\pm(s)=
\frac{6+7s\pm\sqrt{36+72s+45s^2}}2.
$$

当 $s<0$ 时，$\det G_s<0$，所以前二维含一正一负两个特征值，第三个标量 $s-1$ 也严格为负。两项加权差均可逆。令 $R_s$ 为 $G_s$ 的正谱投影；其非对角元为

$$
(R_s)_{12}=\frac{3+3s}{\sqrt{36+72s+45s^2}}\ne0.
$$

故 $P_c^+=|e_1\rangle\langle e_1|$ 与 $P_{d_s}^+=R_s\oplus0$ 不对易。它们的对易子平方在前二维是某个非零负数乘 $I_2$，在第三维为零；因此生成代数包含两个中央分区，并精确为 $M_2(\mathbb C)\oplus\mathbb C$。定理 41.1 给出 $q_{\rm free}=2$ 与 $d_{\rm all}=3$。

当 $s>0$ 时，$G_s$ 的左上元与行列式都严格为正，因此 $G_s>0$，而 $s-1<0$。此时正谱投影为 $P_c^+=|e_1\rangle\langle e_1|$ 与 $P_{d_s}^+=I_2\oplus0$，生成三个一维简单块的交换代数。定理 41.1 因而给出 $q_{\rm free}=1$ 与 $d_{\rm all}=3$。$s=0$ 正是命题 43.2，其结论同样为 $q_{\rm free}=1$、$d_{\rm all}=3$，无需在奇异点使用第 41 节。

在整个参数区间，$3+2s>0$、$3+5s>0$、$s-1<0$。因此固定的标准基测量对 $D_{d_s}$ 给出的范数为

$$
\frac{(3+2s)+(3+5s)+(1-s)}{27}
=\frac{7+6s}{27},
$$

并始终保留 $\|D_c\|_1=5/27$。当 $s\ge0$ 时，$G_s$ 半正定，这个读数已经等于 $\|D_{d_s}\|_1$，故 $\Delta(s)=0$。

当 $s<0$ 时，正负特征值的绝对值之和为

$$
\|D_{d_s}\|_1
=\frac{\sqrt{36+72s+45s^2}+1-s}{27}.
$$

使用同一个标准基测量，得到其实际总损失为

$$
\frac{\sqrt{36+72s+45s^2}-6-7s}{27}.
$$

最优经典损失不大于该值。另一方面，这时精确无损要求 $q\ge2$，第 42 节的达到性排除了经典通道的最优损失为零，所以 $\Delta(s)>0$。所列上界严格为正，因为 $6+7s>0$ 且

$$
(36+72s+45s^2)-(6+7s)^2=-4s(s+3)>0.
$$

也可将它写成

$$
\frac{-4s(s+3)}
{27\left(\sqrt{36+72s+45s^2}+6+7s\right)},
$$

其分母在 $s\to0^-$ 时趋于 $324$，分子趋于零。因此最优损失从负侧也趋于零。这个上界来自一个明确可行测量，没有声称该测量在 $s<0$ 时达到最佳经典总分。

最后，对两个参数只有第二项加权差改变，并且

$$
H_2(s)-H_2(t)=\frac8{27}(s-t)A,
\qquad
d_1(\mathbf H(s),\mathbf H(t))=\frac8{27}|s-t|.
$$

定理 45.1 直接给出两条全区间扰动界。所有严格正损失均针对固定负参数；当参数接近奇异点时，这些损失没有共同的严格正下界。精确资源的整数跳变因而与最优分数的连续性相容。证毕。

## 追加锚（新终端）
