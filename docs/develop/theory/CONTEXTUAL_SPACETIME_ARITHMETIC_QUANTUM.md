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
