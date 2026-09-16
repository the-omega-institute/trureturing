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

## 46. 两步参考放宽上界的完整等号域

**定理 46.1（内部严格损失、放宽最优纯输入与全部边界）。** 沿用第 29 节的两步加权任务、惰性参考、共同历史依赖系统 CPTP 控制及最终保留 $H_2R$ 的约定，限定参数域为

$$
0\le c,e\le1,\qquad 0\le g\le\frac12.
$$

记

$$
B(c;e,g)
=cg+\sqrt{\bigl[1-c(1-g)(1-2e)\bigr]^2
+4c^2(1-2g)^2e(1-e)}.
$$

则第 29 节的上界有如下完整等号判据：

$$
\boxed{
W_2(c;e,g)<B(c;e,g)
\quad\Longleftrightarrow\quad
c>0,\quad0<e<1,\quad0<g<\frac12.
}
$$

其余参数点全部取等，具体为

| 参数条件 | $W_2(c;e,g)=B(c;e,g)$ |
| --- | --- |
| $c=0$ | $1$ |
| $e=0$ | $1-c+2cg$ |
| $e=1$ | $1+c$ |
| $g=0$ | $\sqrt{(1-c)^2+4ce}$ |
| $g=1/2$ | $1+ce$ |

表中条件可以相交，交点上的表达一致。

进一步，在严格不等式的参数域中，第 29 节保留活动系统的放宽目标 $\mathcal B=B$，其最优纯输入恰为系统边缘等于 $I_2/2$ 的纯态，即系统与参考的某个二维子空间之间的最大纠缠态。任意这样的纯输入在允许的末次局部系统秩一投影测量后，都会严格损失迹范数，即使完整保留惰性参考也不例外。

原任务 $W_2$ 的最优值可以由一个参考量子比特、纯输入及两个依赖第一历史的系统幺正控制达到。本定理确定的是放宽上界的等号域，仍未给出内部参数下 $W_2$ 的一般闭式。

证明。先确定原任务优化的达到性。第 29 节已证明，第一共同系统 CPTP 控制可以吸收进自由共同输入；在 $g\le1/2$ 时，固定输入后的末次共同系统 CPTP 控制，可逐第一历史替换为使加权目标不减的系统幺正。该归约对未归一化实际分支 $c\rho$ 成立，所以覆盖本定理的全部 $c\in[0,1]$。

固定两个末次幺正 $U_0,U_1\in U(2)$。最终加权差关于输入线性，迹范数凸。对任意有限参考上的混合输入，取其有限纯态分解，至少有一个纯分量的目标值不小于混合态。因此在同时优化输入与控制时，纯输入已经足够。系统为二维，每个纯输入的 Schmidt 秩至多为二；参考等距与全部系统操作相交换，并保持最终迹范数，所以该纯输入可在一个二维参考中实现。秩一情形补零嵌入即可。

由此，$W_2$ 等于归一化纯输入 $\psi\in\mathbb C^2\otimes\mathbb C^2$ 与 $U_0,U_1\in U(2)$ 上的最大化。单位球面与两个酉群的乘积紧，最终矩阵及其迹范数对这些变量连续，因此最大值达到。这一步把任意有限参考及任意允许 CPTP 控制的上确界，化为原访问权限下的紧集优化；没有增加可操作量子记忆。

现在假设

$$
0<c\le1,\qquad0<e<1,\qquad0<g<\frac12,
\qquad a=1-g,\quad z=1-2g.
$$

在一个参考量子比特上取 Bell 态 $|\Phi\rangle=(|00\rangle+|11\rangle)/\sqrt2$。令 $T_i$ 为第 29 节放宽映射 $\mathcal F_c$ 作用于这个输入后，第一个历史 $i\in\{0,1\}$ 的差块。具体地，

$$
x_i=\frac{\sqrt{1-e}|ii\rangle+\sqrt e|1-i,1-i\rangle}{\sqrt2},
\qquad y_i=\frac{|ii\rangle}{\sqrt2},
$$

$$
T_i=cz|x_i\rangle\langle x_i|
+cgI_S\otimes\operatorname{tr}_S|x_i\rangle\langle x_i|
-|y_i\rangle\langle y_i|.
$$

在 $\operatorname{span}\{|ii\rangle,|1-i,1-i\rangle\}$ 上，其矩阵为

$$
M=\frac12\begin{pmatrix}
ca(1-e)-1&cz\sqrt{e(1-e)}\\
cz\sqrt{e(1-e)}&cae
\end{pmatrix}.
$$

另外两个正交方向 $|1-i,i\rangle$ 与 $|i,1-i\rangle$ 的特征值分别是 $cg(1-e)/2$ 与 $cge/2$，均严格为正。另一方面，

$$
\det M=\frac{ce}{4}
\left[cg(2-3g)(1-e)-(1-g)\right]<0,
$$

因为

$$
(1-g)-cg(2-3g)(1-e)
\ge1-3g+3g^2
=3\left(g-\frac12\right)^2+\frac14>0.
$$

这里使用了 $c\le1$；没有把本定理延伸到任意 $c>1$。每个 $T_i$ 因而可逆，并且有三个正特征值和一个负特征值。记其正、负谱投影为 $\Pi_i^+$、$\Pi_i^-$，则

$$
\Pi_i^++\Pi_i^-=I_4,\qquad
\Pi_i^-=|v_i\rangle\langle v_i|.
$$

矩阵 $M$ 的非对角元严格非零，故其负特征向量的两个坐标都非零。因此可以写

$$
v_i=r_i|ii\rangle+s_i|1-i,1-i\rangle,
\qquad r_is_i\ne0,
\qquad |r_i|^2+|s_i|^2=1.
$$

这说明 $v_i$ 的 Schmidt 秩为二。

接着核对放宽上界中的归一化。第 29 节给出 $\|T_0\|_1=\|T_1\|_1=B/2$。每个 $|T_i|$ 保持上述二维块与两个一维块的分解，所以 $\operatorname{tr}_S|T_i|$ 在参考的计算基中对角。又有

$$
T_1=(X\otimes X)T_0(X\otimes X),
$$

其中 $X$ 是 Pauli 交换矩阵。因此两个参考偏迹的对角元互换，得到

$$
\boxed{
\sum_{i=0}^1\operatorname{tr}_S|T_i|=\frac B2 I_R.
}
$$

这也与第 29 节的 Pauli 协变性一致。

取任意归一化纯输入，其系统边缘为 $\rho$。必要时先将参考等距嵌入维数至少二的空间。由纯化的参考等距关系及 Bell 向量恒等式，该输入在一个参考等距之前可写成

$$
|\psi_\rho\rangle
=(\sqrt{2\rho}\otimes I_R)|\Phi\rangle
=(I_S\otimes\sqrt{2\rho^{\mathsf T}})|\Phi\rangle.
$$

转置取相对于定义 Bell 态的计算基。把参考等距从最终迹范数中消去，令

$$
K_\rho=I_S\otimes\sqrt{2\rho^{\mathsf T}},
\qquad K_\rho^2=2I_S\otimes\rho^{\mathsf T}.
$$

该纯输入的第 $i$ 个放宽差块便是 $K_\rho T_iK_\rho$。将 $T_i=T_{i,+}-T_{i,-}$ 作 Jordan 分解，三角不等式与正矩阵的迹公式给出

$$
\|K_\rho T_iK_\rho\|_1
\le\operatorname{tr}(K_\rho T_{i,+}K_\rho)
+\operatorname{tr}(K_\rho T_{i,-}K_\rho)
=2\operatorname{tr}((I_S\otimes\rho^{\mathsf T})|T_i|).
$$

两历史相加，并使用偏迹恒等式，右端精确等于

$$
2\operatorname{tr}\left(\rho^{\mathsf T}\frac B2 I_R\right)=B.
$$

如果纯输入达到放宽值 $B$，两个非负的三角不等式亏差都必须为零。第 43 节关于正矩阵迹范数取等的判据说明，$K_\rho T_{i,+}K_\rho$ 与 $K_\rho T_{i,-}K_\rho$ 的支撑正交。等价地，

$$
\left\|T_{i,+}^{1/2}K_\rho^2T_{i,-}^{1/2}\right\|_2^2
=\operatorname{tr}\left(
K_\rho T_{i,+}K_\rho\,K_\rho T_{i,-}K_\rho\right)=0.
$$

由于 $T_{i,+}$ 与 $T_{i,-}$ 在各自谱支撑上严格为正，可得

$$
\Pi_i^+K_\rho^2\Pi_i^-=0.
$$

这个推论不要求 $K_\rho$ 可逆。又因 $\Pi_i^+=I_4-\Pi_i^-$，负特征向量满足

$$
(I_S\otimes\rho^{\mathsf T})v_i=\lambda v_i
$$

而成为 $I_S\otimes\rho^{\mathsf T}$ 的特征向量。对其两个系统坐标分别取分量，再用 $r_is_i\ne0$，得到

$$
\rho^{\mathsf T}|i\rangle=\lambda|i\rangle,
\qquad
\rho^{\mathsf T}|1-i\rangle=\lambda|1-i\rangle.
$$

所以 $\rho^{\mathsf T}=\lambda I_2$；由 $\operatorname{tr}\rho=1$，必有 $\rho=I_2/2$。反过来，这个边缘使 $K_\rho=I_4$，直接达到 Bell 值 $B$。因此在纯输入范围内，放宽最优输入恰好是所述最大纠缠态。这里未把一般混合态的最优性等同于它具有最大混合边缘。

再证明这些纯输入无法在原任务中保留 $B$。参考等距不改变问题，所以只需考察 Bell 输入。对第一历史 $i$，任何允许的末次系统幺正及完美指针读取，都等价于一个系统秩一 PVM $Q_i,I_S-Q_i$，随后丢弃系统而保留两结果及参考。记该 CPTP 映射为 $\mathcal C_i$。对于输出上的任意效应 $F_0\oplus F_1$，其对偶满足

$$
\mathcal C_i^*(F_0\oplus F_1)
=Q_i\otimes F_0+(I_S-Q_i)\otimes F_1.
$$

因此对偶像中的每个效应都与 $Q_i\otimes I_R$ 对易。

假设该读取保留 $T_i$ 的迹范数。取 $\mathcal C_i(T_i)$ 的最优正谱效应，并由 $\mathcal C_i^*$ 拉回。迹保持及范数等号使其成为 $T_i$ 的最优效应；$T_i$ 可逆，故由第 43 节完整最优效应区间可知，这个效应只能是 $\Pi_i^+$。于是

$$
[\Pi_i^+,Q_i\otimes I_R]=0,
\qquad
[\Pi_i^-,Q_i\otimes I_R]=0.
$$

秩一投影 $\Pi_i^-=|v_i\rangle\langle v_i|$ 与另一投影对易，意味着 $v_i$ 属于后者的值域或核。这里两者分别为

$$
\operatorname{ran}Q_i\otimes\mathbb C^2,
\qquad
\operatorname{ran}(I_S-Q_i)\otimes\mathbb C^2.
$$

系统因子在任一子空间内都为一维，所以其中每个向量的 Schmidt 秩至多为一。这与 $v_i$ 的 Schmidt 秩为二矛盾。因此每个第一历史上的局部读取都严格损失迹范数。

原任务的最大值已经由某个纯输入及两个末次幺正达到。如果其值等于 $B$，则第 29 节共同后处理的收缩链强制该纯输入先达到放宽值 $B$，从而必须是上述最大纠缠态。但刚证明这种输入经过末次局部读取后严格损失，矛盾。故在所列内部参数域有 $W_2<B$。紧集达到性在这里是必要的一环：只证明每个固定协议不取等，尚不足以排除一列协议趋近 $B$。

最后验证其余所有参数点的达到构造。以下协议均符合原系统控制权限，且不使用参考。由于第 29 节始终给出 $W_2\le B$，逐项达到相应 $B$ 就足以确定精确值。

当 $c=0$ 时，加权差仅为归一化理想输出的负值，迹范数恒为一，等于 $B=1$。

当 $e=0$ 时，取指针输入 $|0\rangle$，所有控制恒等。第一历史必为 $0$，理想完整历史为 $00$；实际末次两个结果概率为 $1-g$、$g$。因为 $c(1-g)\le1$，加权绝对值之和为

$$
|c(1-g)-1|+cg=1-c+2cg=B(c;0,g).
$$

当 $e=1$ 时，同样取指针输入及恒等控制。理想第一历史为 $0$，实际第一历史为 $1$，完整输出支持已经分离，后续读取不改变这一点。因此加权差的迹范数为 $1+c=B(c;1,g)$。

当 $g=1/2$ 时，继续使用指针输入及恒等控制。理想完整历史为 $00$；实际四个历史 $00,01,10,11$ 的概率依次为

$$
\frac{1-e}{2},\quad\frac{1-e}{2},\quad
\frac e2,\quad\frac e2.
$$

由 $c(1-e)/2\le1$，加权范数为

$$
\left|\frac{c(1-e)}2-1\right|
+\frac{c(1-e)}2+ce=1+ce=B(c;e,1/2).
$$

当 $g=0$ 时，取无参考输入 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$，第一控制恒等。记

$$
x_i=K_i|+\rangle,
\qquad y_i=P_i|+\rangle,
\qquad H_i=c|x_i\rangle\langle x_i|-|y_i\rangle\langle y_i|,
$$

其中 $K_i$ 与指针投影 $P_i$ 沿用第 29 节。对每个第一历史选择共同系统幺正，使 $H_i$ 在末次指针基中对角。因为末次读取无错误，这个合法协议得到的加权范数恰为 $\sum_i\|H_i\|_1$。两个矩阵酉等价，其中一个为

$$
H_0=\frac12\begin{pmatrix}
c(1-e)-1&c\sqrt{e(1-e)}\\
c\sqrt{e(1-e)}&ce
\end{pmatrix}.
$$

它的迹为 $(c-1)/2$，行列式为 $-ce/4$，故

$$
\|H_0\|_1=\frac12\sqrt{(1-c)^2+4ce}.
$$

当 $ce=0$ 时，同一式由直接计算成立。两历史相加就达到

$$
\sqrt{(1-c)^2+4ce}=B(c;e,0).
$$

这些边界穷尽闭参数域中不满足严格条件的点，并证明表中全部表达。各边界均存在取等点，因此没有从上述内部严格性得到跨整个参数域的统一正差距。

所用 Choi 与纯输入变换属于标准表示理论。Watrous，*Simpler semidefinite programs for completely bounded norms*，[§3.1，式 (10) 与 Theorem 6](https://arxiv.org/html/1207.5726) 给出向量化、转置及 Choi 夹乘公式；该文使用未归一化 Choi 算子，而本节 $\bigoplus_iT_i$ 来自归一化 Bell 态，因此两者相差输入维数因子二。可逆差的最优效应唯一性是量子 Neyman–Pearson 引理的特例，见 Jenčová，*Reversibility conditions for quantum operations*，[Lemma 7](https://arxiv.org/abs/1107.0453)，其完整效应区间已在第 43 节使用。本节结合第 29 节的具体差块，分析放宽取等强制的输入结构与末次局部读取的障碍；原目标内部的一般精确值仍未求出。证毕。

## 追加锚（新终端）

## 47. 第一次读取前固定 Bell 有效输入的两步精确值

**定义 47.1（固定 Bell 有效输入的加权任务）。** 沿用定义 29.1 的两步加权任务、惰性参考和末端丢弃活动系统的约定。将第一共同控制吸收进有效输入后，额外要求第一次仪器作用前的共同输入直接固定为

$$
|\Phi\rangle_{SR}=\frac{|00\rangle+|11\rangle}{\sqrt2}.
$$

在两次读取之间，仍允许依赖第一历史 $i$ 的任意共同系统 CPTP 控制，控制环境丢弃后不可再次访问；参考 $R$ 不受控制。记这一受限任务的值为

$$
W_2^{\Phi}(c;e,g)
=\sup_{\{\mathcal C_i\}_{i=0}^1}
\sum_{i,j=0}^1\|cX_{ij}^{\Phi}-Q_{ij}^{\Phi}\|_1.
$$

这里 $X_{ij}^{\Phi}$、$Q_{ij}^{\Phi}$ 分别是实际与理想协议在相同控制表下产生的未归一化参考块。固定有效输入意味着在 $|\Phi\rangle$ 与第一次仪器之间没有额外可优化的共同 CPTP 控制；它与“先提供 Bell 态、再允许任意前置 CPTP 控制”的任务不同。

**定理 47.2（固定 Bell 有效输入的精确值与最优控制）。** 对

$$
c=\frac7{20},\qquad e=\frac3{10},\qquad g=\frac1{10},
$$

定义 47.1 的最优值为

$$
W_2^{\Phi}\left(\frac7{20};\frac3{10},\frac1{10}\right)
=\frac{909}{1000}.
$$

两条第一历史均取恒等的中间系统控制即可达到该值。将固定有效输入换成任意纯最大纠缠系统—参考态，最优值仍相同。

证明。定理 29.2 对末次共同 CPTP 控制的逐历史归约适用于固定输入：因 $g\le1/2$，可将每个中间控制换成一个共同系统幺正而使当前加权目标不减。因此只需对两条历史各自优化一个系统秩一投影测量，并在读出第二结果后丢弃系统。

先处理第一历史 $i=0$。设第二次完美读取所对应的系统效应为

$$
E_0=
\begin{pmatrix}
q&\xi\sqrt{q(1-q)}\\
\overline\xi\sqrt{q(1-q)}&1-q
\end{pmatrix},
\qquad E_1=I-E_0,
\qquad 0\le q\le1,\quad |\xi|=1.
$$

端点 $q=0,1$ 的相位可任取。令 $z=1-2g$。定理 29.2 的共同后处理表达表明，加权参考差块为

$$
cX_{0j}^{\Phi}-Q_{0j}^{\Phi}
=\frac12\left[cK_0(gI+zE_j)K_0-P_0E_jP_0\right]^{\mathsf T}.
$$

转置不改变迹范数。代入指定参数，对 $j=0$，括号中的矩阵可写为

$$
M(q,\xi)=
\begin{pmatrix}
\displaystyle\frac{49}{2000}-\frac{201}{250}q
&\displaystyle\xi\sqrt{\frac{1029}{62500}q(1-q)}\\
\displaystyle\overline\xi\sqrt{\frac{1029}{62500}q(1-q)}
&\displaystyle\frac{189}{2000}-\frac{21}{250}q
\end{pmatrix}.
$$

对 $j=1$，矩阵是 $M(1-q,-\xi)$。Hermitian 二阶矩阵的特征值只依赖对角元及非对角元的模，所以

$$
h(q):=\|M(q,\xi)\|_1
$$

与 $\xi$ 无关。第一历史 $i=0$ 的目标贡献为 $[h(q)+h(1-q)]/2$。第一历史 $i=1$ 由同时交换系统与参考的两个基向量得到，具有相同的可取贡献集合。两个历史的控制可独立选择，故

$$
W_2^{\Phi}\left(\frac7{20};\frac3{10},\frac1{10}\right)
=\max_{0\le q\le1}\bigl[h(q)+h(1-q)\bigr].
$$

下面求这个一变量最大值。直接展开得

$$
\operatorname{tr}M(q,\xi)
=t(q):=\frac{119}{1000}-\frac{111}{125}q,
$$

$$
\det M(q,\xi)
=\frac{21}{4000000}\bigl(16000q^2-18000q+441\bigr).
$$

行列式的两个零点为

$$
q_* =\frac9{16}-\frac{3\sqrt{5135}}{400},
\qquad
q^* =\frac9{16}+\frac{3\sqrt{5135}}{400}.
$$

由 $71<\sqrt{5135}<72$，可知

$$
0<q_*<\frac12<1<q^*.
$$

矩阵右下对角元在 $0\le q\le1$ 上至少为 $21/2000>0$。因此，当 $0\le q\le q_*$ 时，$M(q,\xi)$ 半正定，迹范数等于 $t(q)$；当 $q_*<q\le1$ 时，行列式为负，两特征值异号，迹范数等于其间距。令

$$
R(q)=\frac{113136q^2+41664q+1225}{250000},
\qquad f(q)=\sqrt{R(q)}.
$$

则

$$
h(q)=
\begin{cases}
t(q),&0\le q\le q_*,\\
f(q),&q_*\le q\le1.
\end{cases}
$$

在 $q=q_*$ 两式相等。$R$ 的常数项为正，其一次、二次系数亦为正，因此 $f$ 在 $[0,1]$ 上严格递增。若将 $R(q)$ 写成 $a_2q^2+a_1q+a_0$，则

$$
4a_2a_0-a_1^2
=-\frac{18461289}{976562500}<0,
$$

而

$$
f''(q)=\frac{4a_2a_0-a_1^2}{4R(q)^{3/2}}<0.
$$

故 $f$ 在整个区间上严格凹。

目标关于 $q\leftrightarrow1-q$ 对称，只需考虑 $0\le q\le1/2$。若 $0\le q\le q_*$，则

$$
h(q)+h(1-q)=t(q)+f(1-q).
$$

$t(q)$ 严格递减，$f(1-q)$ 也严格递减，所以该区间的最大值在 $q=0$，等于

$$
h(0)+h(1)=\frac{119}{1000}+\frac{79}{100}
=\frac{909}{1000}.
$$

若 $q_*\le q\le1/2$，则 $q$ 与 $1-q$ 都位于根式分支。由 $f$ 的凹性，

$$
h(q)+h(1-q)
=f(q)+f(1-q)
\le2f\left(\frac12\right)
=\frac{\sqrt{50341}}{250}.
$$

两个比较量都为正，且

$$
\left(\frac{909}{1000}\right)^2
-\left(\frac{\sqrt{50341}}{250}\right)^2
=\frac{833}{40000}>0.
$$

因此全局最大值为 $909/1000$，在 $q=0,1$ 达到。恒等中间控制在每条第一历史都给出这类端点投影，故达到所述值。

最后，任意纯最大纠缠系统—参考态都可写成

$$
(I_S\otimes V_R)|\Phi\rangle,
$$

其中 $V_R$ 是从一个参考量子比特到实际参考空间的等距映射。全部允许操作只作用于系统，因此其输出参考块与 Bell 输入的输出块相差同一个参考等距嵌入，迹范数不变。故最优值相同。

本证明的模型归约与共同后处理直接使用定理 29.2；二阶谱计算随后给出固定有效输入的精确最大值。迹范数判别的标准背景可见 Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[Theorem 2.1](https://arxiv.org/abs/quant-ph/0608014)；末段所用纯化的参考酉等价见 Watrous，*The Theory of Quantum Information*，[Theorem 2.12](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。不同参考维数先限制到 Schmidt 支撑并等距嵌入同维空间即可应用该等价。上述标准结果提供迹范数与纯化工具，本节的 $909/1000$ 则由已列的一变量最大化直接求得。证毕。

**命题 47.3（原两步任务的 Bell 有效输入并非最优）。** 在定理 47.2 的参数点，原任务满足

$$
W_2^{\Phi}\left(\frac7{20};\frac3{10},\frac1{10}\right)
=\frac{909}{1000}
<\frac{\sqrt{534}}{25}
\le W_2\left(\frac7{20};\frac3{10},\frac1{10}\right)
<\frac7{200}+\frac{\sqrt{207433}}{500}.
$$

因此，第 29 章放宽任务的 Bell 达到性不能推出原任务存在最大纠缠的最优有效输入。这一严格比较不确定原任务 $W_2$ 的完整最优值。

证明。定理 29.2 的无参考输入 $|+\rangle$ 及按历史选择的共同幺正控制达到 $\sqrt{534}/25$，因而给出原任务的下界。定理 47.2 给出受限 Bell 任务的精确值。指定参数位于定理 46.1 的严格域，故原任务严格小于第 29 节的放宽上界，得到链的最后一个不等式。Bell 值与无参考下界均为正，且

$$
\left(\frac{\sqrt{534}}{25}\right)^2
-\left(\frac{909}{1000}\right)^2
=\frac{28119}{1000000}>0.
$$

所以每个纯最大纠缠有效输入的最佳值都严格小于一个允许的无参考协议值，不能达到原任务的最优值。上述论证没有给出 $W_2$ 等于该下界的上界证明，故不确定其完整值。证毕。

## 追加锚（新终端）
## 48. 半错误首步下的一族精确参考优势区域

**定义 48.1（Hadamard 与指针控制的 Schmidt 输入族）。** 沿用第 29 节的加权两步任务，固定第一步参数 $e=1/2$，并取

$$
0<c\le1,\qquad0<g<\frac12,\qquad0\le p\le1.
$$

准备一个活动系统量子比特及一个惰性参考量子比特，其共同有效输入为

$$
|\psi_p\rangle_{SR}
=\sqrt p\,|00\rangle+\sqrt{1-p}\,|11\rangle.
$$

第一共同控制恒等；第一次结果为 $0$ 时，第二共同系统控制取 Hadamard 矩阵 $H$；第一次结果为 $1$ 时取恒等矩阵 $I_2$。后者也可换成 Pauli 矩阵 $X$，这只交换该历史的两个末次结果。两种候选使用同一控制表，参考从制备后到最终观察前始终不受操作，末端丢弃活动系统，保留全部经典历史与参考。记这个指定协议的加权迹范数分数为 $F(c,g,p)$。

**定理 48.2（协议精确值与相对无参考最优值的完整优势判据）。** 在定义 48.1 的参数域内，令

$$
a=1-g,\qquad z=1-2g,\qquad b=1-ca>0,
$$

$$
L(p)=1-\frac{cz}{2}-bp,
\qquad
R(p)=\left(\frac c2-p\right)^2
+p(1-p)\left[2c-c^2(1-z^2)\right].
$$

则协议分数精确为

$$
\boxed{F(c,g,p)=L(p)+\sqrt{R(p)}.}
$$

第 30 节的全部无参考输入及共同系统 CPTP 控制最优值在本切片化为

$$
\boxed{
C(c,g):=W_2^{\mathrm{cl}}(c;1/2,g)
=\max\{P,S\},
\qquad
P=1+cg,\quad S=\sqrt{1+c^2z^2}.
}
$$

为比较两者，定义

$$
J=2g+ca(1-5g)>0,\qquad u=a(1-4g),
\qquad h=\max\{0,S-P\},
$$

$$
D=c^2u-2bh,\qquad
\mathcal D=D^2-4cJh(c+h).
$$

对任意给定 $p\in[0,1]$，有精确等价

$$
\boxed{
F(c,g,p)>C(c,g)
\quad\Longleftrightarrow\quad
-cJp^2+Dp-h(c+h)>0.
}
$$

因此，存在严格优于全部无参考协议的输入参数 $p$，当且仅当

$$
\boxed{D>0\quad\text{且}\quad\mathcal D>0.}
$$

这两个条件成立时，全部严格优势参数恰为

$$
\boxed{
p\in(p_-,p_+),\qquad
p_\pm=\frac{D\pm\sqrt{\mathcal D}}{2cJ},
\qquad0\le p_-<p_+<1.
}
$$

若 $P\ge S$，判据进一步简化为

$$
\boxed{
F(c,g,p)>C(c,g)
\quad\Longleftrightarrow\quad
0<g<\frac14,\qquad
0<p<\frac{ca(1-4g)}{2g+ca(1-5g)}.
}
$$

其中 $P\ge S$ 本身等价于

$$
2g\ge c(1-g)(1-3g).
$$

若 $g\ge1/4$，本协议族对任何 $c,p$ 都不能超过无参考最优值。这个结论只限制定义 48.1 的输入与控制族，不排除其他参考协议的优势，也未求出一般 $W_2(c;1/2,g)$ 的最优值。

证明。因为 $e=1/2$，实际第一步的两个 Kraus 算子均为 $I_2/\sqrt2$，理想第一步的算子为指针投影 $P_i=|i\rangle\langle i|$。末次实际效应为 $gI_2+zP_j$。对给定系统控制 $U_i$，相应的初始系统差效应为

$$
M_{ij}=\frac c2U_i^\dagger(gI_2+zP_j)U_i
-P_iU_i^\dagger P_jU_iP_i.
$$

记 $\rho_p=\operatorname{diag}(p,1-p)$。由 Schmidt 输入的直接展开，最终历史 $ij$ 的未归一化参考差块是

$$
N_{ij}=\sqrt{\rho_p}\,M_{ij}^{\mathsf T}\sqrt{\rho_p}.
$$

这里没有对任何分支重新归一化。不同经典历史的块正交，故 $F=\sum_{i,j}\|N_{ij}\|_1$。

当第一结果为 $0$ 时，$U_0=H$ 给出

$$
N_{00}=\frac14\begin{pmatrix}
(c-2)p&cz\sqrt{p(1-p)}\\
cz\sqrt{p(1-p)}&c(1-p)
\end{pmatrix},
$$

$$
N_{01}=\frac14\begin{pmatrix}
(c-2)p&-cz\sqrt{p(1-p)}\\
-cz\sqrt{p(1-p)}&c(1-p)
\end{pmatrix}.
$$

它们的行列式同为

$$
\frac{cp(1-p)}{16}\left[c(1-z^2)-2\right].
$$

由于 $0<c\le1$ 和 $0<z<1$，括号严格为负。对 $0<p<1$，两个矩阵都严格不定，迹范数等于特征值间距，因此

$$
\|N_{00}\|_1+\|N_{01}\|_1
=\frac12\sqrt{\left[c+2(1-c)p\right]^2
+4c^2z^2p(1-p)}
=\sqrt{R(p)}.
$$

最后一式由展开得到。在 $p=0,1$ 时，直接计算两个对角矩阵也给出同一公式。

当第一结果为 $1$ 时，$U_1=I_2$ 给出

$$
N_{10}=\operatorname{diag}\left(\frac{cap}{2},\frac{cg(1-p)}2\right),
$$

$$
N_{11}=\operatorname{diag}\left(\frac{cgp}{2},
\left(\frac{ca}{2}-1\right)(1-p)\right).
$$

第一块半正定，第二块的两个对角元分别非负、非正。相加得到

$$
\|N_{10}\|_1+\|N_{11}\|_1
=\frac{cp}{2}+\left(1-\frac{cz}{2}\right)(1-p)
=L(p).
$$

若取 $U_1=X$，两个块只交换，迹范数之和不变。这证明协议的精确分数。四块的总迹为 $c-1$，与实际及理想完整输出的归一化一致；整个计算保留全部历史，没有后选择。

接着计算无参考比较值。将 $e=1/2$ 代入定理 30.2，令该节的 $d=cz$，则 $0<d<1$，而 $r=0$、$v=1$，从而

$$
\eta=\frac{4(1-d)}{2-d}>0.
$$

因此该节的第三个内部候选不出现，无参考最优值就是其端点候选 $P=1+cg$ 与对称候选 $S=\sqrt{1+c^2z^2}$ 的最大值。两者都严格为正，直接平方得

$$
P^2-S^2
=c\left[2g-c(1-g)(1-3g)\right].
$$

由 $c>0$，这给出陈述中的 $P\ge S$ 判据。

为了安全地比较根式，注意

$$
C=P+h,\qquad
C-L(p)=\frac c2+bp+h>0.
$$

因此 $F>C$ 等价于 $R(p)>(C-L(p))^2$，平方没有引入额外解。展开协议根式与端点比较值，得到

$$
R(p)-(P-L(p))^2
=cp\left[ca(1-4g)-Jp\right].
$$

再把比较值从 $P$ 改为 $P+h$，便有

$$
\begin{aligned}
R(p)-(C-L(p))^2
&=cp\left[ca(1-4g)-Jp\right]
-2h\left(\frac c2+bp\right)-h^2\\
&=-cJp^2+Dp-h(c+h).
\end{aligned}
$$

这证明逐 $p$ 的精确等价。

还需证明二次不等式的参数条件确实与 $p\in[0,1]$ 相容。首先，

$$
J=2g(1-c)+c(1-4g+5g^2),\qquad
1-4g+5g^2=5\left(g-\frac25\right)^2+\frac15>0,
$$

所以 $J>0$。相应二次函数严格凹，常数项为 $-h(c+h)\le0$。若 $D\le0$，它在 $p\ge0$ 上不可能为正；若 $D>0$ 而 $\mathcal D\le0$，其全实轴最大值也不为正。因而存在优势参数必须有 $D>0$、$\mathcal D>0$。

反过来，假设这两个条件成立。由 $D=c^2u-2bh>0$、$b>0$、$h\ge0$，必有 $u>0$，即 $g<1/4$。定义

$$
p_P=\frac{cu}{J}=\frac{ca(1-4g)}{J}.
$$

它满足

$$
0<p_P<1,
\qquad
J-cu=g(2-ca)>0.
$$

二次函数的顶点在

$$
p_{\rm v}=\frac D{2cJ}\in\left(0,\frac{p_P}{2}\right].
$$

$\mathcal D>0$ 使顶点值严格为正，因此它已在 $(0,1)$ 内取得正值。两个实根为陈述中的 $p_-,p_+$。根的和为正、积为 $h(c+h)/(cJ)\ge0$，故 $p_-\ge0$。若 $h=0$，两根直接是 $0,p_P$；若 $h>0$，二次函数在 $p=p_P$ 处的值为

$$
-h(c+2bp_P+h)<0.
$$

结合顶点位于 $p_P/2$ 之前，可知 $0<p_-<p_+<p_P<1$。所以在所有情形下，严格优势参数精确为 $(p_-,p_+)$，并且无需与 $[0,1]$ 再作未知的截取。

若 $P\ge S$，则 $h=0$。优势二次式退化为 $cp(cu-Jp)$，立即得到 $g<1/4$ 及 $0<p<p_P$ 的简化条件。若 $g\ge1/4$，则 $u\le0$、$D\le0$，故本协议不可能严格超过 $C$；这没有对优化域中其他参考控制作断言。

也可核对几个退化边界。$p=0$ 时 $F=P\le C$，$p=1$ 时 $F=1<C$。连续延拓到 $c=0$ 时，$F=C=1$；此时不使用根区间中的除法。延拓到 $g=1/2$ 时，有 $F=1+c/2-cp/2\le C=1+c/2$。在 $g=0$ 时，第 29 节放宽上界与第 30 节无参考值同为 $\sqrt{1+c^2}$；已有无参考协议达到该值，所以本协议也不可能产生严格参考优势。这些边界核对没有把上述开参数域的根公式用于零分母。

协议差块的构造沿用第 21 节的参考输出公式及第 23 节的二阶 Hermitian 迹范数计算；全部无参考优化由定理 30.2 承担。二元判别中迹范数与最优成功概率的标准关系见 Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[Theorem 2.1](https://arxiv.org/html/quant-ph/0608014)，其中归于 Helstrom。本节精确比较的是一个明确参考协议族与已经优化的无参考任务，不把协议族的存在优势判据当作一般参考任务的完整分类。证毕。

**推论 48.3（整段参数上的严格参考增益及三步应用）。** 令

$$
g_0=1-\frac{\sqrt6}{3}.
$$

对任意

$$
g_0\le g<\frac14,\qquad0<c\le1,
$$

都有 $C(c,g)=1+cg$，并且非空区间

$$
0<p<\frac{c(1-g)(1-4g)}
{2g+c(1-g)(1-5g)}
$$

中的每个参数都给出

$$
W_2(c;1/2,g)\ge F(c,g,p)
>W_2^{\mathrm{cl}}(c;1/2,g).
$$

特别地，$g=1/5$ 时，这个区间精确化为 $0<p<2c/5$。

进一步，对任意 $g\in[g_0,1/4)$ 与末次参数 $f\in[1/2,1)$，三步系统 CPTP 任务满足

$$
\boxed{
T_3^{\mathrm{ref,CPTP}}(1/2,g,f)
>T_3^{\mathrm{cl,CPTP}}(1/2,g,f).
}
$$

这里的参考仍然是惰性的，没有额外可操作量子记忆。对每个选定的参数，可以用上述一个参考量子比特的输入与控制族，再接第 28 节的共同尾段构造，得到严格优于全部无参考系统 CPTP 协议的三步值。

证明。首先 $0<g_0<1/4$：前一式由 $\sqrt6<3$ 得到，后一式等价于 $\sqrt6>9/4$，平方后为 $6>81/16$。在所列区间内，$1-3g>0$。由于 $c\le1$，有

$$
\begin{aligned}
2g-c(1-g)(1-3g)
&\ge2g-(1-g)(1-3g)\\
&=-1+6g-3g^2\ge0.
\end{aligned}
$$

最后一步来自该二次式的较小根 $g_0$，且整个当前区间在较大根 $1+\sqrt6/3$ 之前。因此 $P\ge S$，即 $C=1+cg$。又因 $g<1/4$，定理 48.2 的 $p_P$ 严格为正且小于一，所列区间非空，并且每个其中的 $p$ 都产生严格优势。这个协议属于原参考优化域，所以 $W_2\ge F$。

在 $g=1/5$ 时，$a=4/5$、$1-4g=1/5$、$1-5g=0$，因而 $p_P=2c/5$；相应的平方比较是

$$
R(p)-(P-L(p))^2=\frac{2cp(2c-5p)}{25}.
$$

这说明第 21 节的孤立优势构造位于一个连续参数族中。

现在取 $f\in[1/2,1)$，令 $c=1-f\in(0,1/2]$。第 28 节的加权尾段归约与第 30 节的无参考版本分别给出

$$
T_3^{\mathrm{ref,CPTP}}(1/2,g,f)
=\frac f2+\frac12W_2(1-f;1/2,g),
$$

$$
T_3^{\mathrm{cl,CPTP}}(1/2,g,f)
=\frac f2+\frac12C(1-f,g).
$$

对上面非空区间中的任意 $p$，将严格两步优势代入得到

$$
\begin{aligned}
T_3^{\mathrm{ref,CPTP}}(1/2,g,f)
&\ge\frac f2+\frac12F(1-f,g,p)\\
&>\frac f2+\frac12C(1-f,g)
=T_3^{\mathrm{cl,CPTP}}(1/2,g,f).
\end{aligned}
$$

第 28 节的达到方向把这个指定两步协议接成允许的共同系统 CPTP 尾段，因此严格不等式对应可实现的参考协议。端点 $f=1$ 会使 $c=0$，已在前一定理的边界讨论中排除严格优势，故本推论不包含它。这里仍未求出三步参考任务的完整精确值。证毕。
## 49. 两步惰性参考任务中两个固定读取轴不足的精确反例

**定义 49.1（固定读取轴菜单）。** 沿用第 29 节的两步加权任务，取

$$
c=\frac45,\qquad e=\frac12,\qquad g=\frac1{20}.
$$

第一共同控制吸收进有效输入，允许任意有限惰性参考及任意归一化共同输入。末次共同系统控制限制为幺正，并要求每个第一历史 $i$ 对应的末次完美读取效应，只能选以下两种互补秩一 PVM 之一：

$$
\mathsf Z=\{P_0,P_1\},
\qquad
\mathsf X=\{|+\rangle\langle+|,|-\rangle\langle-|\}.
$$

每条第一历史独立选轴，末次结果可以重标记。完美读取效应指第 29 节将最后一次有误仪器改写成退极化后处理之后的效应；有误参数 $g=1/20$ 保留不变。活动系统最后丢弃，保留完整两次历史及参考。将这一菜单下的最优加权迹范数记为 $W_{\{\mathsf X,\mathsf Z\}}$。由于 $g\le1/2$，第 29 节的逐历史归约说明，在同一菜单效应约束下允许末次 CPTP 控制所得的值与允许共同系统幺正所得的值相同；以下直接使用幺正实现。

**引理 49.2（固定控制表的纯化目标对系统边缘凹）。** 固定一个允许的历史控制表，并将对应实际与理想输出映射的加权差记为 Hermitian 保持映射 $\mathcal F$。对系统密度矩阵 $\rho$，令

$$
f_{\mathcal F}(\rho)
=\| (\mathcal F\otimes\operatorname{id})(|\psi_\rho\rangle\langle\psi_\rho|)\|_1,
$$

其中 $|\psi_\rho\rangle$ 为任意纯化，纯化参考始终不受控制。则 $f_{\mathcal F}$ 良定义，并且为凹函数。

证明。同一系统边缘的纯化之间可通过参考等距联系。所有协议映射只作用于系统，参考等距保留输出迹范数，因此选择纯化不影响数值。

设 $\rho=\lambda\rho_0+(1-\lambda)\rho_1$，其中 $0\le\lambda\le1$。把两种纯化嵌入同一个有限参考空间，并引入一个仅用于纯化的二标签参考因子 $F$，取

$$
|\Omega\rangle
=\sqrt\lambda\,|\psi_{\rho_0}\rangle|0\rangle_F
+\sqrt{1-\lambda}\,|\psi_{\rho_1}\rangle|1\rangle_F.
$$

它是 $\rho$ 的归一化纯化。在输出参考因子 $F$ 上去相干，产生两个权重分别为 $\lambda$、$1-\lambda$ 的直和块，故去相干后的迹范数为

$$
\lambda f_{\mathcal F}(\rho_0)+(1-\lambda)f_{\mathcal F}(\rho_1).
$$

去相干是 CPTP 映射，在 Hermitian 算子上收缩迹范数。因此

$$
f_{\mathcal F}(\rho)
\ge\lambda f_{\mathcal F}(\rho_0)+(1-\lambda)f_{\mathcal F}(\rho_1).
$$

这里的参考去相干只用于比较两个输出范数，并未作为控制操作加入原协议。证毕。

**定理 49.3（菜单的精确值与菜单外的严格增益）。** 在上述定义中，

$$
W_{\{\mathsf X,\mathsf Z\}}=\frac{\sqrt{949}}{25}.
$$

另有一个只用参考量子比特、纯有效输入及两个实幺正系统控制的允许协议，其值为

$$
\frac{\sqrt{479942241}+\sqrt{910376791}}{42250}
>\frac{\sqrt{949}}{25}.
$$

因此，将两个末次系统读取轴限制为 $\mathsf X$、$\mathsf Z$ 会严格降低原任务的最优值，即使菜单内允许任意输入和任意有限惰性参考。这一结论不确定原任务的完整最优值，也不声称排除所有系统边缘对角的输入。

证明。固定菜单内的一个控制表。最终加权差关于共同输入线性，迹范数凸，所以某个纯态分量的值不低于混合输入。纯输入的 Schmidt 秩至多二，可将参考等距压缩至量子比特，并用其系统边缘 $\rho$ 参数化。

因为 $e=1/2$，第一次实际 Kraus 算子均为 $K_i=I/\sqrt2$。令 $z=1-2g=9/10$。对第一历史 $i$ 和末次效应 $E_{ij}$，定义初始系统差效应

$$
M_{ij}=\frac c2(gI+zE_{ij})-P_iE_{ij}P_i.
$$

选取规范纯化后，第 23 节的参考部分迹公式给出目标

$$
f(\rho)=\sum_{i,j}\|\sqrt\rho\,M_{ij}\sqrt\rho\|_1.
$$

参考输出中的转置不改变迹范数。这个 $f$ 正是引理中固定整个控制表的函数，因此对 $\rho$ 凹。

令 $Z=\operatorname{diag}(1,-1)$。若第一历史 $i$ 选择 $\mathsf Z$，则 $ZM_{ij}Z=M_{ij}$。若它选择 $\mathsf X$，则 $ZE_{ij}Z=E_{i,1-j}$，且 $P_iE_{ij}P_i=P_i/2$，从而

$$
ZM_{ij}Z=M_{i,1-j}.
$$

所以对每个固定表都有 $f(Z\rho Z)=f(\rho)$：第一历史保持不变，仅在选择 $\mathsf X$ 的分支内互换末次结果。凹性给出

$$
f\left(\frac{\rho+Z\rho Z}{2}\right)\ge f(\rho).
$$

因此，每个固定菜单表的最优值都可用

$$
\rho_p=\operatorname{diag}(p,1-p),\qquad0\le p\le1
$$

达到。以下枚举的是全部四张菜单表及其连续输入优化。

两条第一历史均选择 $\mathsf Z$ 时，全部参考差块对角，直接求绝对值之和得到

$$
f_{\mathsf Z\mathsf Z}(\rho_p)=1+cg=\frac{26}{25}.
$$

两条第一历史均选择 $\mathsf X$ 时，同时交换系统两个计算基向量只会交换第一历史，故

$$
f_{\mathsf X\mathsf X}(\rho_p)
=f_{\mathsf X\mathsf X}(\rho_{1-p}).
$$

再用引理的凹性，其最大值在 $p=1/2$。在此输入上直接计算两阶块的两特征值间距，得到

$$
f_{\mathsf X\mathsf X}(I/2)
=\sqrt{1+c^2z^2}=\frac{\sqrt{949}}{25}.
$$

如果第一历史 $0$ 选择 $\mathsf X$、第一历史 $1$ 选择 $\mathsf Z$，用二阶矩阵公式

$$
\|\sqrt\rho M\sqrt\rho\|_1
=\sqrt{[\operatorname{tr}(\rho M)]^2-4\det\rho\det M}
\quad\text{当 }\det M<0
$$

及半定块的绝对迹公式，得到

$$
f_{\mathsf X\mathsf Z}(\rho_p)
=\frac{16-6p+\sqrt{-299p^2+424p+100}}{25}.
$$

具体地，$\mathsf X$ 分支的两个块各有相同的迹范数，其和为式中的根式除以 $25$；$\mathsf Z$ 分支的范数为 $(16-6p)/25$。交换两条第一历史对应 $p\leftrightarrow1-p$，所以另一张混合表具有同一最优值。

对全部 $p\in[0,1]$，$14+6p>0$，并且

$$
\begin{aligned}
(14+6p)^2-(-299p^2+424p+100)
&=335p^2-256p+96\\
&=335\left(p-\frac{128}{335}\right)^2
+\frac{15776}{335}>0.
\end{aligned}
$$

故混合表的目标严格小于 $30/25$。由于

$$
26<30<\sqrt{949},
$$

四张表中最大值由 $\mathsf X\mathsf X$ 和 Bell 输入达到，为 $\sqrt{949}/25$。输入、参考和菜单控制的上界均已覆盖。 这里的凹性与 $Z$ 共轭只对每一张固定菜单表成立；先对控制表取上确界后所得函数不必仍然凹，因此该论证不外推到原任务的连续控制全体。

现在构造菜单外的协议。取系统边缘

$$
\rho=\begin{pmatrix}\frac12&\frac7{20}\\\frac7{20}&\frac12\end{pmatrix},
\qquad\det\rho=\frac{51}{400},
$$

并取其纯化

$$
|\psi\rangle
=\sqrt{\frac{17}{20}}\,|++\rangle
+\sqrt{\frac3{20}}\,|--\rangle.
$$

这个态归一化，参考保持惰性。对第一历史 $0$，选择末次第零结果效应

$$
Q=\frac1{169}\begin{pmatrix}144&-60\\-60&25\end{pmatrix},
$$

另一效应为 $I-Q$。$Q$ 是实秩一投影，因为它投影到归一化向量 $(12,-5)^{\mathsf T}/13$。对第一历史 $1$ 选择效应 $XQX$、$I-XQX$，其中 $X$ 是 Pauli 交换矩阵。这些实秩一 PVM 均由允许的实幺正中间控制实现。

第一历史 $0$ 的两个初始系统差效应为

$$
M_{00}=\frac1{8450}\begin{pmatrix}-4439&-1080\\-1080&619\end{pmatrix},
\qquad
M_{01}=\frac1{8450}\begin{pmatrix}-631&1080\\1080&2761\end{pmatrix}.
$$

它们的行列式分别是

$$
\det M_{00}=-\frac{3914141}{71402500},
\qquad
\det M_{01}=-\frac{2908591}{71402500},
$$

并且

$$
\operatorname{tr}(\rho M_{00})=-\frac{1333}{4225},
\qquad
\operatorname{tr}(\rho M_{01})=\frac{1821}{8450}.
$$

故二阶谱公式给出

$$
\|\sqrt\rho M_{00}\sqrt\rho\|_1
=\frac{\sqrt{910376791}}{84500},
\qquad
\|\sqrt\rho M_{01}\sqrt\rho\|_1
=\frac{\sqrt{479942241}}{84500}.
$$

$X\rho X=\rho$，而第一历史 $1$ 的两效应是第一历史 $0$ 的效应经过 $X$ 共轭的结果，所以两个第一历史的范数贡献相同。相加得到陈述的协议值。

最后验证严格比较。所有根式均为正，将该协议值与 $\sqrt{949}/25$ 比较，平方并移项后等价于

$$
\sqrt{479942241\cdot910376791}>660059934.
$$

右端为正，再平方可用整数恒等式验证：

$$
479942241\cdot910376791-660059934^2
=1249160754844275>0.
$$

因此这个菜单外的合法协议严格超过菜单内全体协议。原任务的一般连续控制优化仍未完成；本章只排除固定 $\mathsf X/\mathsf Z$ 两轴菜单已经达到原任务最优值这一简化命题。

所用纯化等价与迹范数收缩见 Watrous，*The Theory of Quantum Information*，[Theorem 2.12 与 Corollary 3.40，式 (3.241)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。引理将这两个标准工具应用到同一个固定历史控制表；菜单上界与菜单外的严格比较由本证明的具体矩阵计算给出。证毕。
## 50. 记录选择与后续预测闭合

**定义 50.1（经典观察的后续闭合）。** 设 $X$ 为有限历史集合，$q:X\to Y$ 为当前读数，$F:X\to X$ 为允许的下一步操作。称 $q$ 对 $F$ 后续闭合，如果存在唯一的映射 $\bar F:q(X)\to q(X)$ 使

$$
q\circ F=\bar F\circ q.
$$

**定理 50.2（有限经典读数的闭合判据）。** 上述 $\bar F$ 存在，当且仅当

$$
q(x)=q(y)\Longrightarrow q(F(x))=q(F(y))
\qquad(x,y\in X).
$$

在存在时，$\bar F(q(x)):=q(F(x))$ 给出唯一的闭合更新。

证明。若 $\bar F$ 存在，对 $q(x)=q(y)$ 代入即可。反之，按右端公式定义 $\bar F$；条件保证它不依赖于代表元，且立即满足 $q\circ F=\bar F\circ q$。证毕。

**定义 50.3（量子记录与一步闭合误差）。** 在同一有限维算符空间上，令 $\mathcal E$ 为幂等的量子记录通道，$\mathcal E^2=\mathcal E$，令 $\Phi$ 为一步量子通道。对密度算符定义迹距离

$$
D(\rho,\sigma)=\frac12\lVert\rho-\sigma\rVert_1,
$$

并定义

$$
\delta(\mathcal E,\Phi)
=\sup_{\rho}D\bigl(\mathcal E\Phi(\rho),\nobreak\mathcal E\Phi\mathcal E(\rho)\bigr),
$$

其中上确界遍历全部密度算符。称记录对一步演化严格闭合，如果

$$
\mathcal E\Phi=\mathcal E\Phi\mathcal E,
$$

等价地，$\mathcal E\Phi(I-\mathcal E)=0$。

**定理 50.4（量子记录的累计预测界）。** 假设记录的像空间由有限个经典记录 $\{P_i\}$ 张成，并且存在经典随机矩阵 $K$ 使

$$
\mathcal E\Phi\mathcal E(\rho)=\iota\!\left(K\,\pi(\rho)\right),
$$

其中 $\pi(\rho)$ 是 $\mathcal E(\rho)$ 在经典记录基下的权重向量，$\iota$ 将权重向量嵌回对角密度算符。令 $A=\mathcal E\Phi$、$B=\mathcal E\Phi\mathcal E$。则对每个密度算符 $\rho$ 及整数 $n\ge0$，

$$
D\bigl(A^n(\rho),B^n(\rho)\bigr)\le n\,\delta(\mathcal E,\Phi).
$$

因此以 $K^n\pi(\rho)$ 预测第 $n$ 步记录时，逐步粗读数分布的误差至多为 $n\delta$。

证明。$A$ 与 $B$ 都是量子通道。望远镜分解与迹距离在量子通道下的收缩性给出

$$
D(A^n\rho,B^n\rho)
\le\sum_{k=0}^{n-1}D\bigl(A(B^k\rho),B(B^k\rho)\bigr)
\le n\delta.
$$

第二个不等式使用 $B^k\rho$ 仍为密度算符。对角记录上的 $B$ 正是 $K$ 的作用，所以其记录权重为 $K^n\pi(\rho)$。证毕。

**定理 50.5（有限维生成元的闭合方向）。** 设 $\Phi_t=e^{t\mathcal L}$ 是有限维、时齐次量子半群，且 $\mathcal E^2=\mathcal E$。则全时严格闭合

$$
\mathcal E\Phi_t=\mathcal E\Phi_t\mathcal E\quad(t\ge0)
$$

当且仅当

$$
\mathcal E\mathcal L(I-\mathcal E)=0.
$$

在 $t\to0$ 时，闭合缺陷满足

$$
\mathcal E\Phi_t(I-\mathcal E)
=t\,\mathcal E\mathcal L(I-\mathcal E)+O(t^2).
$$

条件 $(I-\mathcal E)\mathcal L\mathcal E=0$ 则是 $\mathcal L$ 保持 $\operatorname{Fix}(\mathcal E)$ 的另一方向，不能与前一条件混同。

证明。矩阵指数展开给出后一式。若 $\mathcal E\mathcal L(I-\mathcal E)=0$，则对每个 $m\ge1$ 有 $\mathcal E\mathcal L^m(I-\mathcal E)=0$，因为 $\mathcal E\mathcal L=\mathcal E\mathcal L\mathcal E$，从而指数展开的全部项均为零。反向由对 $t=0$ 的导数得到该条件。对后一方向，若 $X=\mathcal E(Y)$，则 $\mathcal L X\in\operatorname{Fix}(\mathcal E)$ 正是 $(I-\mathcal E)\mathcal L\mathcal E=0$；这描述的是记录像空间的不变性，而不是隐藏部分对未来记录的不可见性。证毕。

**命题 50.6（两种互补记录的共同固定点）。** 对量子比特，令 $\mathcal E_Z$ 与 $\mathcal E_X$ 分别为计算基和 Hadamard 基去相干通道。则

$$
\operatorname{Fix}(\mathcal E_Z)\cap\operatorname{Fix}(\mathcal E_X)=\mathbb C I.
$$

限制到密度算符后，交集只有 $I/2$。

证明。$\mathcal E_Z$ 的固定矩阵为对角矩阵 $\operatorname{diag}(a,b)$。Hadamard 共轭后为

$$
\frac12\begin{pmatrix}a+b&a-b\\a-b&a+b\end{pmatrix}.
$$

它再次对角化当且仅当 $a=b$。归一化迹为一时即得 $I/2$。证毕。

**命题 50.7（受约束编码的动力学检查）。** 设 $P_Z$ 投影到长度 $L$ 的无相邻 $1$ 合法字串空间

$$
\mathcal H_{Z,L}=\operatorname{span}\{|w\rangle:w_jw_{j+1}=0\}.
$$

若 $H$ 是 Hermitian Hamiltonian，则该空间在 $e^{-itH}$ 下无泄漏，当且仅当

$$
[H,P_Z]=0.
$$

因此，仅写出合法 Zeckendorf 叠加并不能保证编码与动力学相容；还须检查这个不变性条件。对一般非 Hermitian 生成元或 Lindblad 通道，必须改用相应的子空间不变性条件，不能直接以该对易式代替。

证明。Hermitian 性使 $P_ZH(I-P_Z)=0$ 与其伴随 $(I-P_Z)HP_Z=0$ 等价；这正是 $H$ 与 $P_Z$ 对易。它又等价于 $e^{-itH}$ 保持 $\operatorname{ran}P_Z$。其余警示是定义域不同的动力学条件。证毕。

**本批来源与边界。** 定理 50.2 是有限集合上的直接因子化证明。量子通道的迹距离收缩、有限维纯化与去相干固定点分别使用本卷既有的通道论证和仓库中的记录模型；其具体闭合判据、累计界、生成元方向区分及 Zeckendorf 子空间检验是本批在这些模型上的推导。本文不把这些命题写成 Lean 已验证结果，也不声称它们给出一般开放系统、无界生成元或全部量子测量的统一定理。对 Lindblad 情形，本批只保留“须另行检查子空间不变性”的边界，不替代该检查。

证毕。

## 追加锚（新终端）
## 51. 退相干、冗余记录与经典稳定性阈值

**定义 51.1（历史记录模型）。** 设系统 $S$ 的候选经典标签为 $a$，环境分解为

$$
E=E_1\otimes\cdots\otimes E_N,
$$

并取退相干型相互作用

$$
H_{\mathrm{int}}=\sum_a \Pi_a\otimes B_a,
$$

其中 $\{\Pi_a\}$ 是候选指针分解。若初态含有两个标签的相干项 $|a\rangle\langle b|$，在环境演化后其系统系数写成

$$
\rho_{ab}(t)=\rho_{ab}(0)\,\Gamma_{ab}(t).
$$

当环境片段独立耦合时，退相干因子分解为

$$
\Gamma_{ab}(t)=\prod_{k=1}^{N}\gamma_{ab}^{(k)}(t).
$$

**命题 51.2（经典稳定性的候选操作化条件）。** 给定误差容差 $\varepsilon>0$、信息亏损容差 $\delta>0$、形成后时间窗 $[t_{\mathrm{start}},T]$（$0<t_{\mathrm{start}}\le T$）和目标冗余度整数 $R_\ast\ge1$，以下三项构成候选指针记录的操作化条件：

$$
\sup_{t\in[t_{\mathrm{start}},T]}|\Gamma_{ab}(t)|\le\varepsilon
\qquad(a\ne b),
$$

把指针标签 $A$ 视为经典变量，令 $p_a=\operatorname{tr}(\Pi_a\rho)$，并以联合态

$$
\rho_{AF}=\sum_a p_a\,|a\rangle\langle a|\otimes\rho_F^{(a)}
$$

定义互信息；要求存在 $R_\ast$ 个两两不交的环境片段 $F_1,\ldots,F_{R_\ast}\subseteq E$，使得对每个 $j$ 都有

$$
I(A:F_j)\ge(1-\delta)H(A),
$$

以及系统自身 Hamiltonian 满足附加稳定性条件

$$
\|[H_S,\Pi_a]\|\le\eta.
$$

这里最后一个条件只控制系统自身动力学；完整开放动力学还须另行检验相应 Lindblad 生成元对指针代数的近似不变性。因此，本命题把三项作为给定模型和误差阈值下的候选操作化条件，不声称它们是所有量子模型中的普适必要定理。只有再加上完整开放生成元对指针代数的近似不变性，并完成相应动力学验证时，才可在该具体模型内把这些条件作为充分判据。

证明。第一式在形成后窗口内使不同标签之间的局部干涉项低于观测容差；不把 $t=0$ 的初始相干误称为已退相干。第二式表示每个选定环境片段都获得几乎全部指针标签信息；$R_\ast$ 个互不重叠片段同时满足它们，标签便可被独立读取，形成目标冗余记录。第三式限制系统自身动力学在形成后窗口内旋转指针代数的速率；开放系统还需要对其生成元作所述不变性检验。由此，三项分别约束相干性、可复制性和系统内禀稳定性，给出了可执行的候选经典记录判据。该推导只是在指定模型中的条件性结论，并未把“稳定经典现实”提升为无模型的本体定理。证毕。

**定义 51.3（历史冗余度）。** 固定 $\delta$，定义

$$
R_\delta
=
\max\left\{r:\exists\ F_1,\ldots,F_r\ \text{两两不交},\ I(A:F_j)\ge(1-\delta)H(A)\right\}.
$$

在此定义下，“需要多少约束”应改写成：在给定 $\varepsilon,\delta,T$ 和允许的环境分解后，达到

$$
|\Gamma_{ab}|\le\varepsilon,
\qquad
R_\delta\ge R_\ast
$$

所需的最小有效耦合或记录通道数。$R_\ast$ 由任务要求决定，不是量子理论给出的普适常数。

**推论 51.4（历史保留与经典化的条件性关系）。** 若环境保留了区分历史 $a,b$ 的可复制记录，并且命题 51.2 的阈值条件成立，则对只访问系统局部的观测者，相关相干项按 $\Gamma_{ab}$ 衰减，历史差异可作为稳定的经典标签读取；若所有记录都被擦除且系统与环境重新相干，局部干涉在相应可逆操作下原则上可以恢复。

推导。前半句直接由定义 51.1 的退相干因子和命题 51.2 的冗余互信息条件得到：局部观测同时看见小相干项和多个可替代记录。后半句附带“在相应可逆操作下”的条件，因为只有当环境记录及其动力学均可控时，擦除才会恢复相干；单纯忽略环境并不会自动恢复干涉。故这里给出的是操作层面的可检验关系，不是关于单一经典世界的本体断言。来源：退相干与指针稳定性沿用 Zurek，*Rev. Mod. Phys.* **75**, 715 (2003)；互信息与冗余记录沿用 Ollivier、Poulin 与 Zurek，*Phys. Rev. Lett.* **93**, 220401 (2004)。阈值 $\varepsilon,\delta,T,R_\ast$ 是本章的操作化参数，不是上述文献中的普适常数。证毕。

## 追加锚（新终端）
## 53. 第 51 节候选条件的适用域更正

**命题 53.1（退相干因子分解的假设）。** 第 51.1 节的乘积式

$$
\Gamma_{ab}(t)=\prod_k\gamma_{ab}^{(k)}(t)
$$

需要至少假设初态在所选环境分解下为

$$
\rho_{SE}(0)=\rho_S(0)\otimes\bigotimes_k\tau_k
$$

并且条件环境演化在每个标签 $a$ 下因子化为 $U_a(t)=\bigotimes_kU_{a,k}(t)$。在这些假设下，环境重叠给出

$$
\Gamma_{ab}(t)=\prod_k\operatorname{tr}\!\left(U_{a,k}(t)\tau_kU_{b,k}(t)^\dagger\right).
$$

若系统自身 Hamiltonian 混合不同的 $\Pi_a$ 子空间，则 $\rho_{ab}(t)=\rho_{ab}(0)\Gamma_{ab}(t)$ 一般只是相互作用表象或附加条件下的表达，不能直接当作完整动力学的恒等式。

证明。因子化初态与条件演化使环境条件态分别为 $\bigotimes_kU_{a,k}\tau_kU_{a,k}^\dagger$。两个条件态的重叠是各片段重叠的乘积，得到第一式。若系统自身演化不保持指针分解，它会在不同 $a$ 之间产生额外转移项，故单一乘法因子不能代表完整演化。证毕。

**命题 53.2（互信息条件的可读性边界）。** 第 51.2 节的条件

$$
I(A:F)\ge(1-\delta)H(A)
$$

只说明经典标签 $A$ 与片段 $F$ 的互信息接近标签熵。要把它解释为某个实际测量能够以小猜测误差读出 $A$，还须指定测量类并加入相应的可访问信息或猜测概率界；互信息条件单独不提供该测量界。

证明。互信息是对允许测量前的量子—经典相关量的函数，而可读性还包含从 $F$ 到标签估计器的优化。二者只有在给定编码、测量类及相应信息—误差不等式后才能连接。因此本命题把第 51.2 节的第二项保留为冗余相关性指标，不把它冒充为单次读出定理。证毕。

**推论 53.3（第 51 节结论的正确状态）。** 第 51 节的三项只能作为指定模型、形成后时间窗和误差阈值下的候选筛选条件。要在具体开放系统中把它们升级为充分判据，还须同时验证完整生成元对指针代数的时间窗内近似不变性，并给出该近似与目标读出误差之间的定量界。

因此，“需要多少约束”仍由 $\varepsilon,\delta,T,R_\ast$、环境分解、可执行测量类和生成元参数共同决定；本批不赋予它一个普适整数。

证明。命题 53.1 限定退相干分解的动力学假设，命题 53.2 限定冗余互信息的操作解释，完整生成元检验补足系统自身 Hamiltonian 条件未覆盖的开放动力学。三项边界合并后，所得只是可检验的模型内筛选标准。证毕。



## 追加锚（新终端）
## 52. 末端读取与无中间干预的累计预测界

**定义 52.1（真实演化的末端读取与逐步记录模型）。** 设 $\mathcal H$ 为有限维 Hilbert 空间，$\Phi:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H)$ 为 CPTP 映射，$\mathcal E$ 为同一算符空间上的幂等 CPTP 映射，$\mathcal E^2=\mathcal E$。记全部密度算符为 $\mathsf D(\mathcal H)$，记录态集为

$$
\mathcal R=\mathcal E\bigl(\mathsf D(\mathcal H)\bigr),
\qquad
T=\mathcal E\Phi\mathcal E,
\qquad
K=T|_{\mathcal R}.
$$

幂等性使 $\mathcal E(\sigma)=\sigma$ 对每个 $\sigma\in\mathcal R$ 成立，故 $K(\sigma)=\mathcal E\Phi(\sigma)$，且 $K$ 将记录态集映入自身。

对任意共同初态 $\rho$，在不插入中间记录通道的演化中，真实状态与其第 $n$ 步末端读数分别为

$$
\sigma_n=\Phi^n(\rho),
\qquad
r_n=\mathcal E\Phi^n(\rho).
$$

仅用初始记录建立的闭合预测则是

$$
s_0=\mathcal E(\rho),
\qquad
s_{n+1}=K(s_n),
\qquad
s_n=T^n\mathcal E(\rho).
$$

这里同时写出各个 $r_n$ 是计算不同演化时刻的粗观察量，不要求在同一次实际运行中每一步都施加 $\mathcal E$。若在每一步 $\Phi$ 后实际施加记录通道，则相应状态为 $(\mathcal E\Phi)^n(\rho)$；它与 $\mathcal E\Phi^n(\rho)$ 是两种不同的通道复合。

**定理 52.2（末端记录的累计闭合误差）。** 在定义 52.1 的模型中，令

$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
$$

$$
\delta
=\max_{\omega\in\mathsf D(\mathcal H)}
D\bigl(\mathcal E\Phi(\omega),\mathcal E\Phi\mathcal E(\omega)\bigr).
$$

该最大值存在，且 $0\le\delta\le1$。对每个密度算符 $\rho$ 与整数 $n\ge0$，有

$$
\boxed{
D\bigl(\mathcal E\Phi^n(\rho),T^n\mathcal E(\rho)\bigr)
\le n\delta.
}
$$

特别地，若 $\mathcal E\Phi=\mathcal E\Phi\mathcal E$，则末端记录由初始记录严格决定：

$$
\mathcal E\Phi^n(\rho)=K^n\mathcal E(\rho)
\qquad(n\ge0).
$$

若另有 $0\le\kappa\le1$，使记录更新满足

$$
D(K\sigma,K\tau)\le\kappa D(\sigma,\tau)
\qquad(\sigma,\tau\in\mathcal R),
$$

则有更强的界

$$
D\bigl(\mathcal E\Phi^n(\rho),T^n\mathcal E(\rho)\bigr)
\le\delta\sum_{j=0}^{n-1}\kappa^j.
$$

当 $n=0$ 时空和为零；当 $\kappa<1$ 时，右端可写成 $\delta(1-\kappa^n)/(1-\kappa)$。上述结论不要求 $\Phi$ 保持 $\mathcal R$，也不要求 $\Phi\mathcal E=\mathcal E\Phi$。

证明。有限维密度算符集合紧，两个通道及迹范数连续，所以定义中的上确界达到。两候选均为密度算符，其迹距离属于 $[0,1]$。

采用定义 52.1 的 $\sigma_n,r_n,s_n$，并令 $e_n=D(r_n,s_n)$。初始时 $r_0=s_0=\mathcal E(\rho)$，故 $e_0=0$。幂等性给出

$$
T(r_n)
=\mathcal E\Phi\mathcal E\bigl(\mathcal E(\sigma_n)\bigr)
=\mathcal E\Phi\mathcal E(\sigma_n).
$$

又有 $r_{n+1}=\mathcal E\Phi(\sigma_n)$，其中 $\sigma_n$ 仍为密度算符，故一步缺陷的定义逐步适用：

$$
D\bigl(r_{n+1},T(r_n)\bigr)\le\delta.
$$

$r_n$ 与 $s_n$ 都位于 $\mathcal R$，而 $s_{n+1}=T(s_n)$。三角不等式和记录更新的收缩性给出

$$
\begin{aligned}
e_{n+1}
&\le D\bigl(r_{n+1},T(r_n)\bigr)
+D\bigl(T(r_n),T(s_n)\bigr)\\
&\le\delta+\kappa e_n.
\end{aligned}
$$

对这个标量递推归纳，由 $e_0=0$ 得

$$
e_n\le\delta\sum_{j=0}^{n-1}\kappa^j.
$$

$T$ 是 CPTP 映射，其限制 $K$ 总可取收缩上界 $\kappa=1$，于是得到 $n\delta$。严格闭合使 $\delta=0$，故全部 $e_n=0$。证明中的 $T(r_n)$ 只是把真实第 $n$ 步读数输入预测规则作比较，没有对真实状态 $\sigma_n$ 施加中间干预。

与此区别，令 $A=\mathcal E\Phi$。对第 50.4 条比较的逐步记录通道，$A$ 与 $T$ 在 $\mathcal R$ 上相同，且 $A(\rho),T(\rho)$ 都在 $\mathcal R$。因此对每个 $n\ge1$，

$$
A^n(\rho)=K^{n-1}A(\rho),
\qquad
T^n(\rho)=K^{n-1}T(\rho),
$$

从而

$$
D\bigl(A^n(\rho),T^n(\rho)\bigr)
\le\kappa^{n-1}\delta\le\delta.
$$

这里 $n=1$ 时空次迭代的系数为一。这一更强界适用于逐步记录的两种初始处理；它不把 $A^n$ 改写成 $\mathcal E\Phi^n$。证毕。

**命题 52.3（中间去相干会改变后续记录）。** 对一个量子比特，取计算基去相干通道

$$
\mathcal E_Z(X)=P_0XP_0+P_1XP_1,
\qquad P_j=|j\rangle\langle j|,
$$

以及 Hadamard 幺正通道

$$
\Phi(X)=H X H,\qquad
H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
$$

对初态 $\rho=P_0$ 和两步演化，

$$
\mathcal E_Z\Phi^2(P_0)=P_0,
\qquad
(\mathcal E_Z\Phi)^2(P_0)=\frac I2.
$$

因此末端读取与逐步记录的通道一般不同。在这个模型中，定义 52.2 的一步缺陷为 $\delta=1/2$，而末端记录与闭合预测的两步误差恰为 $1/2$。

证明。$H^2=I$，所以第一式成立。另一方面，$\Phi(P_0)=|+\rangle\langle+|$，去相干后为 $I/2$；后者在 $\Phi$ 和 $\mathcal E_Z$ 下都不变，得到第二式。

为计算一步缺陷，把任意态写成 Bloch 形式

$$
\omega=\frac12(I+xX+yY+zZ),
\qquad x^2+y^2+z^2\le1.
$$

Hadamard 共轭将 $X$ 与 $Z$ 互换。于是

$$
\mathcal E_Z\Phi(\omega)=\frac12(I+xZ),
\qquad
\mathcal E_Z\Phi\mathcal E_Z(\omega)=\frac I2.
$$

两者迹距离为 $|x|/2$，其最大值 $1/2$ 由 $|+\rangle$ 达到。记录更新 $K$ 把所有计算基对角态映为 $I/2$，所以 $T^2\mathcal E_Z(P_0)=I/2$。末端误差为 $D(P_0,I/2)=1/2$；它符合定理 52.2，却不等同于逐步通道之间的误差。证毕。

**定理 52.4（时变记录与逐步收缩系数）。** 设 $\mathcal H_0,\ldots,\mathcal H_n$ 均为有限维空间。对每个 $k=0,\ldots,n-1$，令

$$
\Phi_k:\mathcal L(\mathcal H_k)\to\mathcal L(\mathcal H_{k+1})
$$

为 CPTP 映射，并对每个 $k=0,\ldots,n$ 取幂等 CPTP 记录通道 $\mathcal E_k$。定义记录态集

$$
\mathcal R_k=\mathcal E_k\bigl(\mathsf D(\mathcal H_k)\bigr),
$$

一步记录更新

$$
K_k:\mathcal R_k\to\mathcal R_{k+1},
\qquad
K_k(\sigma)=\mathcal E_{k+1}\Phi_k(\sigma),
$$

以及一步缺陷

$$
\delta_k
=\max_{\omega\in\mathsf D(\mathcal H_k)}
D\bigl(\mathcal E_{k+1}\Phi_k(\omega),
\mathcal E_{k+1}\Phi_k\mathcal E_k(\omega)\bigr).
$$

取任意满足

$$
D(K_k\sigma,K_k\tau)\le\kappa_k D(\sigma,\tau)
\qquad(\sigma,\tau\in\mathcal R_k)
$$

的 $\kappa_k\in[0,1]$。令 $\sigma_0=\rho$、$\sigma_{k+1}=\Phi_k(\sigma_k)$，真实末端读数为 $r_k=\mathcal E_k(\sigma_k)$；闭合预测从 $s_0=\mathcal E_0(\rho)$ 出发，按 $s_{k+1}=K_k(s_k)$ 更新。则

$$
\boxed{
D(r_n,s_n)
\le\sum_{j=0}^{n-1}\delta_j
\prod_{k=j+1}^{n-1}\kappa_k.
}
$$

空积取一，$n=0$ 时空和取零。每个记录更新都可以选择 $\kappa_k=1$，从而始终有 $D(r_n,s_n)\le\sum_{j=0}^{n-1}\delta_j$。

证明。$K_k$ 是 CPTP 映射 $\mathcal E_{k+1}\Phi_k$ 在记录态集上的限制，所以记录态集保持及收缩上界成立。真实状态 $\sigma_k$ 仍归一化；由 $r_k=\mathcal E_k(\sigma_k)$，可直接得到

$$
D\bigl(r_{k+1},K_k(r_k)\bigr)
=D\bigl(\mathcal E_{k+1}\Phi_k(\sigma_k),
\mathcal E_{k+1}\Phi_k\mathcal E_k(\sigma_k)\bigr)
\le\delta_k.
$$

令 $e_k=D(r_k,s_k)$，三角不等式给出

$$
e_{k+1}\le\delta_k+\kappa_k e_k,
\qquad e_0=0.
$$

归纳展开：$e_1\le\delta_0$；若第 $m$ 步已满足乘积和，则

$$
\begin{aligned}
e_{m+1}
&\le\delta_m+\kappa_m
\sum_{j=0}^{m-1}\delta_j\prod_{k=j+1}^{m-1}\kappa_k\\
&=\sum_{j=0}^{m}\delta_j\prod_{k=j+1}^{m}\kappa_k.
\end{aligned}
$$

这正是陈述的第 $m+1$ 步形式。整个比较针对未经中间记录干预的真实通道序列 $\Phi_{n-1}\cdots\Phi_0$；变化的是各时刻的观察映射与预测规则，未把观察计算替换成物理测量。证毕。

**推论 52.5（经典记录的原始预测式）。** 若记录通道为有限正交指针基中的完全去相干，

$$
\mathcal E(\rho)=\sum_i\operatorname{tr}(P_i\rho)P_i,
\qquad P_i=|i\rangle\langle i|,
$$

令 $\pi(\rho)_i=\operatorname{tr}(P_i\rho)$，$\iota(p)=\sum_i p_iP_i$，以及列随机矩阵

$$
K_{ij}=\operatorname{tr}\bigl(P_i\Phi(P_j)\bigr).
$$

则

$$
D\bigl(\mathcal E\Phi^n(\rho),\iota(K^n\pi(\rho))\bigr)
\le n\delta.
$$

等价地，真实末端读数分布与仅从初始读数预测出的 $K^n\pi(\rho)$ 之间，总变差距离不超过 $n\delta$。

证明。每个 $K_{ij}\ge0$，且迹保持给出 $\sum_iK_{ij}=1$。直接代入得 $T\iota(p)=\iota(Kp)$，而 $\mathcal E(\rho)=\iota\pi(\rho)$，故 $T^n\mathcal E(\rho)=\iota(K^n\pi(\rho))$。两个对角密度算符的迹距离恰为其权重向量的总变差距离，应用定理 52.2 即得。证毕。

所用迹范数收缩见 Watrous，*The Theory of Quantum Information*，[Corollary 3.40，式 (3.241)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。本章在有限维 CPTP 模型中用这一标准工具证明末端观察的递推界；一步缺陷的最大值遍历所声明系统的全部密度算符。若要对额外惰性参考上的任意纠缠输入给出统一保证，需要把缺陷改为扩展通道上的最大迹距离，或使用相应 diamond 范数界，不能由未扩展的 $\delta$ 自动推出。界中的 $n\delta$ 可以大于一，此时只有平凡的迹距离上界一更强。量子通道收缩和预测误差界均不指定某一次观测的唯一结果，也不要求把证明中的各次粗观察实现为实际中间测量。



## 追加锚（新终端）

## 54. 有限实验族的预测等价与最小充分记录

前面的闭合条件研究的是一个已经选定的记录通道能否独立推进。这里把问题换成静态的有限任务：在只允许一组有限实验、且每个实验最多运行有限步时，哪些历史必须被区分，哪些历史可以合法地合并？这个问题不要求给不相容测量预先填写一张共同答案表；每个实验协议都有自己的结果分布。

**定义 54.1（有限实验族）。** 设 $X$ 是非空有限的候选历史集合，且 $m\ge1$。固定一个有限实验族

$$
\mathfrak T_H=\{\tau_1,\ldots,\tau_m\},
$$

其中每个协议 $\tau_i$ 的运行长度不超过 $H$，可以包含基于先前结果选择后续操作的有限自适应分支，终端结果集合 $Y_i$ 有限。对 $x\in X$，记该协议的结果分布为

$$
p_i(\,\cdot\mid x)=p_{\tau_i}(\,\cdot\mid x)\in\Delta(Y_i).
$$

记录值只需取在 $r(X)$ 中；对每个 $u\in r(X)$，相应的预测器取值于 $\Delta(Y_i)$。

在量子模型中，$x$ 可以代表一个候选密度算符或带有历史标签的状态，$p_{\tau_i}(y\mid x)$ 由该协议的通道复合与末端 POVM 按 Born 规则给出。实验族中的每个 $\tau_i$ 是一个固定的可执行协议（必要时含有限分支）；不同 $\tau_i$ 之间不要求、也不默认存在联合结果分布。

**定义 54.2（$H$ 步预测等价）。** 定义

$$
x\mathrel{\sim_H}x'
\quad\Longleftrightarrow\quad
p_i(\,\cdot\mid x)=p_i(\,\cdot\mid x')
\quad\text{对所有 }i=1,\ldots,m.
$$

把

$$
S_H(x)=\bigl(p_1(\,\cdot\mid x),\ldots,p_m(\,\cdot\mid x)\bigr)
$$

称为预测响应签名，并令 $Q_H=X/{\sim_H}$。因为 $X$ 有限，$\sim_H$ 是有限个等价类。

**定理 54.3（有限实验族的最小充分记录）。** 令 $r:X\to R$ 是一个记录。以下两件事等价：

1. 对每个实验 $\tau_i$，存在只依赖记录值的分布 $\widehat p_i(\,\cdot\mid r)$，使

   $$
   p_i(\,\cdot\mid x)=\widehat p_i(\,\cdot\mid r(x))
   \qquad(x\in X).
   $$

2. $r$ 的每个纤维都包含在一个 $\sim_H$ 等价类中，即

   $$
   r(x)=r(x')\Longrightarrow x\sim_H x'.
   $$

因此 $S_H$（等价地，商映射 $q_H:X\to Q_H$）是这组实验的最小充分记录：任意充分记录都能区分 $\sim_H$ 的不同类，而 $q_H$ 本身保留恰好足以重建全部 $p_i$ 的信息。达到 $|Q_H|$ 个有效记录值的充分记录，其每个非空纤维恰为一个 $\sim_H$ 类，因而在把记录值作双射重标记的意义下唯一；允许多余记录值时，充分记录可以严格细化这些类。并且

$$
|Q_H|=\bigl|\{S_H(x):x\in X\}\bigr|.
$$

证明。若第 1 条成立且 $r(x)=r(x')$，则对每个 $i$ 都有

$$
p_i(\,\cdot\mid x)=\widehat p_i(\,\cdot\mid r(x))
=\widehat p_i(\,\cdot\mid r(x'))=p_i(\,\cdot\mid x'),
$$

故 $x\sim_Hx'$。反过来，若第 2 条成立，对每个非空记录纤维的记录值 $u$ 选一个代表元 $x_u$，定义

$$
\widehat p_i(\,\cdot\mid u):=p_i(\,\cdot\mid x_u).
$$

第 2 条保证同一纤维中的任意 $x$ 与 $x_u$ 预测等价，所以该定义与代表元选择无关，并满足第 1 条。取 $r=q_H$ 即得到充分记录。若另有充分记录 $r$，已证其纤维不能跨越 $\sim_H$ 类，因此它至少有 $|Q_H|$ 个有效值；$q_H$ 达到该下界。若有效值数也等于 $|Q_H|$，每个类只能对应一个纤维，纤维对应遂给出记录值与 $Q_H$ 之间的双射。证毕。

这个定理给出一个可直接检查的“对象”判据：在指定实验族和 $H$ 步上限后，对象不是当前数值相同的所有历史，而是响应签名相同的历史类。改变实验族会改变等价关系；增加实验只能细化记录，不能把两个已经可区分的响应重新合并。

**推论 54.4（有限协议组合的因子化）。** 若先以固定概率 $\lambda_i\ge0$ 选择协议 $\tau_i$，满足 $\sum_i\lambda_i=1$，并对其终端结果施加随机核 $K_i:Y_i\to\Delta(Y)$，其中 $Y$ 是共同有限结果集，则组合实验的结果分布为

$$
p(y\mid x)=\sum_{i=1}^{m}\lambda_i
\sum_{z\in Y_i}K_i(y\mid z)p_i(z\mid x).
$$

它只依赖于 $S_H(x)$，因而也只依赖于 $q_H(x)$。这给出有限实验族对随机菜单和经典读出的封闭性；它没有把不同不相容协议的结果拼成一个联合样本。

证明。右端只含各个 $p_i(\cdot\mid x)$，而这些分布由 $S_H(x)$ 确定。证毕。

**推论 54.5（实验族扩张的单调性与有限稳定化）。** 若

$$
\mathfrak T_H\subseteq\mathfrak T_{H+1}
$$

（例如加入长度为 $H+1$ 的协议），则

$$
x\sim_{H+1}x'\Longrightarrow x\sim_Hx',
\qquad
|Q_H|\le |Q_{H+1}|.
$$

对有限 $X$，每次严格细化至少使等价类数增加一；所以这条链至多发生 $|X|-1$ 次严格细化。达到某个 $H_0$ 后若 $Q_{H_0}=Q_{H_0+1}$，这只说明在所声明的有限扩张中没有新区别；它不推出未列入实验族的协议也无法区分这些类。

证明。第一式是实验条件包含关系的直接应用；第二式由商集细化得到。严格细化会把至少一个类拆成两个，故有限性给出次数上界。证毕。

**定义 54.6（有限实验族的预测伪距离）。** 在不要求 $X$ 有限时，令

$$
d_H(x,x')
=\max_{1\le i\le m}
\operatorname{TV}\!\left(p_i(\,\cdot\mid x),p_i(\,\cdot\mid x')\right),
$$

其中

$$
\operatorname{TV}(p,q)=\frac12\sum_{y}|p(y)-q(y)|.
$$

在任意 $X$ 上仍用“所有 $p_i(\cdot\mid x)$ 相等”定义 $\sim_H$；当 $X$ 有限时，这与定义 54.2 完全一致。

则 $d_H$ 是伪度量：它非负、对称，满足三角不等式，但不同状态可能有 $d_H=0$。零距离关系正好是 $\sim_H$；并令 $Q_H:=X/{\sim_H}$，于是 $Q_H$ 是把有限任务下不可区分状态取商得到的预测空间。

对每个 $i$ 再施加一个随机后处理 $K_i$ 时，数据处理不等式给出

$$
\operatorname{TV}(K_ip_i^x,K_ip_i^{x'})
\le \operatorname{TV}(p_i^x,p_i^{x'}),
$$

故后处理后的预测伪距离不超过 $d_H$。三角不等式则逐个 $i$ 应用总变差距离的三角不等式，再取最大值。这些收缩性只涉及已列出的协议结果，不涉及不相容测量的联合赋值。

具体地，对任意 $x,y,z$ 有

$$
\begin{aligned}
d_H(x,z)
&=\max_i\operatorname{TV}(p_i^x,p_i^z)\\
&\le\max_i\bigl[\operatorname{TV}(p_i^x,p_i^y)+\operatorname{TV}(p_i^y,p_i^z)\bigr]\\
&\le d_H(x,y)+d_H(y,z),
\end{aligned}
$$

其中 $p_i^x$ 简写为 $p_i(\cdot\mid x)$。这同时说明 $d_H$ 的三角不等式不依赖于任何跨协议联合赋值。

**命题 54.7（近似充分记录的纤维判据）。** 若记录 $r:X\to R$ 满足每个纤维的 $d_H$ 直径不超过 $\varepsilon$，选定每个非空纤维的代表元 $x_u$ 并令

$$
\widehat p_i(\,\cdot\mid u)=p_i(\,\cdot\mid x_u),
$$

则对所有 $x$ 和 $i$，都有

$$
\operatorname{TV}\!\left(p_i(\,\cdot\mid x),
\widehat p_i(\,\cdot\mid r(x))\right)\le\varepsilon.
$$

反过来，若某个预测器对每个 $x$ 的误差均不超过 $\alpha$，即

$$
\operatorname{TV}\!\left(p_i(\,\cdot\mid x),
\widehat p_i(\,\cdot\mid r(x))\right)\le\alpha
$$

对所有 $i,x$ 成立，则每个记录纤维的 $d_H$ 直径不超过 $2\alpha$。

证明。第一部分把 $x$ 与同一纤维代表元的总变差距离直接代入 $d_H$ 的定义。第二部分对同一纤维中的 $x,x'$ 使用三角不等式：

$$
\operatorname{TV}(p_i^x,p_i^{x'})
\le\operatorname{TV}(p_i^x,\widehat p_i^{r(x)})
+\operatorname{TV}(\widehat p_i^{r(x')},p_i^{x'})
\le2\alpha,
$$

其中 $r(x)=r(x')$。对 $i$ 取最大值得证。证毕。

该命题是静态的有限任务压缩条件，和第 50、52 节的动态闭合误差不同：这里不假定存在一步记录通道，也不把误差按时间步累积；它只回答“在预先列出的实验族上，一个记录纤维内最多允许多大预测差异”。如果实验族以包含原实验族的方式扩张，$d_H$ 只能增大，原来的 $\varepsilon$-充分性可能失效。

**例 54.8（增加一个实验会拆分对象）。** 取四个候选历史 $X=\{a,b,c,d\}$。第一实验 $\tau_1$ 和第二实验 $\tau_2$ 都是二结果协议，令结果 $1$ 的概率表为

$$
\begin{array}{c|cccc}
 &a&b&c&d\\ \hline
\tau_1&0&0&1&1\\
\tau_2&0&1&0&1
\end{array}
$$

只允许 $\tau_1$ 时，最小充分记录有两个类：$\{a,b\}$ 与 $\{c,d\}$。加入 $\tau_2$ 后，四个响应签名分别为 $(0,0),(0,1),(1,0),(1,1)$，所以 $Q_H$ 变成四个单点类。一个具体实现是在 $\mathbb C^4$ 的基 $|00\rangle,|01\rangle,|10\rangle,|11\rangle$ 上分别读取第一和第二个经典比特；两行在这个实现中相容。该表的作用是展示商结构，而不是声称任意量子实验都能同时实现不相容读数。

**量子相容性边界。** 在量子应用中，$\mathfrak T_H$ 应理解为一组具体协议，每个协议内部的测量顺序和控制已经固定。定义 $S_H$ 只收集各协议的边缘结果分布，不产生跨不相容协议的联合概率。因而“$x\sim_Hx'$”的含义是：在这组可执行协议上统计不可区分；它不等价于存在一张同时写好所有测量答案的经典表。若实验族包含连续控制参数，有限的 $H$ 步上限本身仍不使 $\mathfrak T_H$ 有限；此时应改用上确界型伪距离，或先给控制菜单和精度预算，再使用本节的有限版本。

**本节边界。** 定理 54.3 处理有限候选历史和有限实验族，证明的是响应分布的因子化与最小性；命题 54.7 给出有限任务下的近似压缩误差。它们不声称记录一定能由一个物理仪器无损实现，也不替代第 50、52 节关于实际通道闭合和时间累计误差的检验。若要把 $Q_H$ 实现为物理记录，还需另外给出仪器、扰动和后续实验的动力学模型，并检查它是否保持所需的响应精度。

本节是 repo-derived/open 的理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 55. 有限记录的 Gram 谱、相位回流与复用协议

前面已经分别给出了预测等价、去相干固定点以及末端预测误差。本节把“记录怎样参与后续演化”压缩成一个有限维可计算对象：条件记录向量的 Gram 矩阵。它同时给出相干模式的衰减因子和相位因子，但不能单独决定记录是否真的被读取，也不能把带记忆的复用协议当成每步独立的无记忆通道。

本节所有结论都是有限维模型中的 `repo-derived/open` 推导；没有新增 Lean 声明、形式覆盖或冻结状态。

### 定义 55.1（条件记录与 Gram 记录通道）

设构型标签集 $I$ 有限，系统空间为

$$
\mathcal H_S=\operatorname{span}\{|i\rangle:i\in I\},
$$

记录空间为 $\mathcal H_R$。固定记录初态 $|m_\ast\rangle$，并假设内部耦合在这些输入上满足

$$
|i\rangle|m_\ast\rangle\longmapsto |i\rangle|r_i\rangle,
\qquad \langle r_i|r_i\rangle=1.
$$

定义 Gram 矩阵

$$
R_{ij}:=\langle r_j|r_i\rangle.
$$

对系统算符定义记录后的局部通道

$$
\mathcal C_R(\rho)=R\circ\rho,
\qquad
(R\circ\rho)_{ij}=R_{ij}\rho_{ij}.
$$

这里的 $\circ$ 是逐项乘积。因为 $R$ 是单位对角的半正定矩阵，Schur 乘积定理给出 $\mathcal C_R$ 完全正且保持迹；它正是上述联合幺正演化后对记录空间取偏迹得到的通道。

### 命题 55.2（Gram 谱就是相干模式的响应谱）

令 $E_{ij}=|i\rangle\langle j|$。则

$$
\mathcal C_R(E_{ij})=R_{ij}E_{ij}.
$$

因此在矩阵单位基下，记录通道的特征值（按代数重数计）就是 $\{R_{ij}:i,j\in I\}$。对 $R_{ij}\neq0$，给定记录间隔 $\tau>0$ 可写成

$$
R_{ij}=e^{-\Gamma_{ij}\tau+i\omega_{ij}\tau},
$$

其中

$$
\Gamma_{ij}=-\frac{\log|R_{ij}|}{\tau},
\qquad
\omega_{ij}=\frac{\arg R_{ij}}{\tau}\pmod{\frac{2\pi}{\tau}}.
$$

故模长描述该相干模式的单次衰减，辐角描述相对相位旋转。这个“谱”属于记录耦合与选定标签的组合，不是孤立构型预先携带的普适频率。

证明。第一式由逐项乘积直接得到；矩阵单位构成全体矩阵空间的基，故特征值列表如上。指数参数化只是对非零复数的模长和辐角作定义。证毕。

### 推论 55.3（趋于经典与仅有经典固定点是两件事）

设 $|I|\ge2$，并令

$$
q:=\max_{i\neq j}|R_{ij}|.
$$

则对任意 $N\ge1$，

$$
(\mathcal C_R^N\rho)_{ij}=R_{ij}^{N}\rho_{ij}.
$$

若 $q<1$，则所有非对角元趋于零，且 $\mathcal C_R^N(\rho)$ 收敛到 $\rho$ 的指针基对角部分。若存在 $i\neq j$ 使 $|R_{ij}|=1$，则该模式不会衰减；它可以周期旋转，也可以保持不变。一般地，固定点空间由满足 $R_{ij}=1$ 的矩阵单位张成；条件 $|R_{ij}|=1$ 本身只说明记录向量同射线，不能说明它们携带可区分记录。对纯记录态，二者的迹距离为 $\sqrt{1-|R_{ij}|^2}$。

若所有 $i\ne j$ 都满足 $R_{ij}=1$ 或 $|R_{ij}|<1$，则逐项极限存在，并等于保留 $R_{ij}=1$ 的矩阵单位的投影；若存在 $|R_{ij}|=1$ 且 $R_{ij}\ne1$，则通常只有 Cesàro 平均才会消除该周期相位，而单次迭代不收敛。

特别地，取

$$
|r_0\rangle=|0\rangle,
\qquad |r_1\rangle=-|0\rangle,
$$

则

$$
R=\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
\qquad
\mathcal C_R(\rho)=Z\rho Z.
$$

其固定点满足 $\rho_{01}=0$，因而固定点全是对角的；但是

$$
\mathcal C_R^2=\operatorname{id}.
$$

所以“固定点代数是经典的”不推出“动力学趋向经典”。趋近经典需要严格的谱隙条件 $q<1$，而不是仅仅要求 $R_{ij}\neq1$。

证明。逐次应用第一式即可。$q<1$ 时有限维任意矩阵范数中的非对角部分都趋于零；反例直接代入 Schur 乘积公式。证毕。

### 定义 55.4（独立新记录与相干复用）

设每次记录都使用一个与系统和旧记录无关的空白单元，则 $N$ 次局部通道为 $\mathcal C_R^N$，其模式 $E_{ij}$ 的可见度为

$$
V_N^{\mathrm{fresh}}(i,j)=|R_{ij}|^N.
$$

若同一个记录单元保留相干并再次参与联合演化，则不能直接把每次作用替换成 $\mathcal C_R$；需要从联合幺正演化重新计算当前记录向量的 Gram 矩阵。

### 命题 55.5（同一记录复用的有限模型）

令

$$
A=\sum_{i\in I}a_i|i\rangle\langle i|,
\qquad
U_\theta=e^{-i\theta A\otimes Y},
$$

记录比特从 $|0\rangle$ 开始。连续作用 $m$ 次而不测量、不重置该比特后，系统边缘通道仍为 Schur 通道，并且

$$
R^{(m)}_{ij}
=\langle0|e^{im\theta a_jY}e^{-im\theta a_iY}|0\rangle
=\cos\!\bigl(m\theta(a_i-a_j)\bigr).
$$

因此

$$
V_m^{\mathrm{reuse}}(i,j)
=\left|\cos\!\bigl(m\theta(a_i-a_j)\bigr)\right|,
$$

而一般不满足

$$
\mathcal C_{R^{(m+n)}}
=\mathcal C_{R^{(m)}}\mathcal C_{R^{(n)}}.
$$

例如 $a_0=0,a_1=1,\theta=\pi/4$ 时，

$$
V_2^{\mathrm{fresh}}=\frac12,
\quad V_2^{\mathrm{reuse}}=0,
\qquad
V_4^{\mathrm{fresh}}=\frac14,
\quad V_4^{\mathrm{reuse}}=1.
$$

同样四次作用可以给出衰减到四分之一的独立记录，也可以给出完整回归的相干复用。差异来自旧记录仍在联合系统中携带相位，而不是来自“作用次数”这个整数本身。

证明。由于 $A$ 在构型基底对角化，$U_\theta^m$ 对 $|i\rangle$ 条件地作用为 $e^{-im\theta a_iY}$。对记录比特取内积得到 $R^{(m)}_{ij}$；$e^{-isY}=\cos s\,I-i\sin s\,Y$ 且 $\langle0|Y|0\rangle=0$，故得到余弦式。数值等式由 $\cos(\pi/2)=0$、$\cos(\pi)=-1$ 以及独立通道的幂次直接得出。证毕。

### 记忆回流的有限表达

为了把“旧历史重新回来”与上述复用例子分开，考虑任意有限维线性演化的可见—隐藏分块：

$$
x_{n+1}=Ax_n+By_n,
\qquad
y_{n+1}=Cx_n+Dy_n.
$$

这里 $x_n$ 是当前记录保留的坐标，$y_n$ 是被省略但仍在整体中演化的坐标；不假定 $y_n$ 自身是量子态。

### 命题 55.6（隐藏块诱导的历史回流核）

对 $n\ge0$，消去 $y_n$ 得

$$
x_{n+1}
=Ax_n+BD^ny_0
+\sum_{k=0}^{n-1}BD^{n-1-k}Cx_k.
$$

其中 $BD^ny_0$ 是初始隐藏差异的后效，$BD^{n-1-k}C$ 是从时刻 $k$ 的可见变化进入隐藏块、再返回当前读数的回流核。

若在某个次乘范数下 $\|D^r\|\le\eta_r$，则相距 $r$ 步以上的回流项范数至多按

$$
\|B\|\,\eta_r\,\|C\|\,\|x_k\|
$$

控制。只有在给定预测窗口和误差容限下这些尾项足够小，才可以把 $x_n$ 近似当作无记忆状态。该条件是对隐藏动力学的谱或范数假设，不由“当前读数已经稳定”自动推出。

证明。由第二式递归展开

$$
y_n=D^ny_0+\sum_{k=0}^{n-1}D^{n-1-k}Cx_k,
$$

代回第一式即得。尾项界由次乘范数和三角不等式给出。证毕。

### Zeckendorf 约束窗口中的记录混叠

取长度 $L$ 的合法字串集合

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

并令 $a(w)$ 是其 Zeckendorf 权重读数。以三位窗口为例，合法构型为

$$
000,001,010,100,101,
$$

对应 $a(w)=0,1,2,3,4$。在该有限集合上使用命题 55.5 的记录耦合，得到

$$
R_{wv}=\cos\!\bigl(\theta(a(w)-a(v))\bigr).
$$

于是

$$
R_{wv}=0
\iff
\theta(a(w)-a(v))\in\frac\pi2+\pi\mathbb Z,
$$

表示两条条件记录正交；而

$$
|R_{wv}|=1
\iff
\theta(a(w)-a(v))\in\pi\mathbb Z,
$$

表示它们至多相差一个相位符号，局部记录不能稳定地区分二者。故 Zeckendorf 刻度差大并不自动意味着可读信息增加；还必须检查实际耦合角度造成的 Gram 谱是否混叠。

这个构造只规定了合法构型和一个明确记录模型。它没有把 Fibonacci 权重解释为物理能量，也没有声称仓库现有 `WindowRegister` 已经实现该受约束量子空间。

### 与前面章节的边界

命题 55.2–55.3 研究一次固定记录通道的谱和渐近行为；它们不替代第 50 节的粗变量闭合条件。命题 55.5 比较两种联合协议，说明第 52 节的逐步无记忆界不能直接套用于相干复用；命题 55.6 给出有限线性模型中的回流核，但不自动保证某个开放量子系统的生成元具有该分块形式。第 54 节的预测等价仍然按预先声明的实验族定义对象；本节只说明同一记录值在不同记录协议下可能拥有不同 Gram 谱和历史后效。项目已有的跨记录类指数衰减结果要求相应重叠统一小于一；本节的周期反例属于同一记录射线只差相位的情形，因此不满足那个收缩假设。

因此，“保留多少历史”在这个有限模型中至少由三项共同决定：记录 Gram 谱中模长小于一的谱隙、相位复用产生的回流、以及任务允许的预测窗口。不存在脱离协议、读出和误差容限的普适整数答案。

## 追加锚（新终端）

## 56. 任务依赖的记忆视界与有效阶数

第 54 节把对象定义为指定实验族上的预测响应类，第 55 节说明记录复用会把旧关联重新带回可见演化。本节把“还要保留多少历史”写成一个可计算的任务量。关键区别是：记忆视界由输入—隐藏—输出的通道共同决定，而不是由隐藏空间的维数或某个全局谱单独决定。

### 定义 56.1（有限线性记忆实现与任务核）

考虑有限维线性实现

$$
x_{n+1}=Ax_n+By_n,
\qquad
y_{n+1}=Cx_n+Dy_n,
$$

其中 $x_n$ 是当前记录保留的坐标，$y_n$ 是未写入记录但仍在整体中演化的坐标。给定线性任务读出 $G$，实际比较的量为 $z_n=Gx_n$。取次乘范数，并令

$$
K_r:=GBD^{r-1}C\quad(r\ge1),
\qquad
b_n:=GBD^ny_0.
$$

由第 55.6 节的消元式，输出满足

$$
z_{n+1}
=GAx_n+b_n+
\sum_{r=1}^{n}K_r x_{n-r}.
$$

$K_r$ 是相隔 $r$ 步的任务记忆核；它只记录能够从可见端口进入隐藏块、再由读出端口返回的部分。隐藏方向若被 $G B$ 消掉，即使在整体中长时间存在，也不属于这个任务的可见记忆。

### 定义 56.2（$\varepsilon$-记忆视界）

固定任务时间窗 $T$、可见轨道界 $\|x_k\|\le X$ 和初始隐藏界 $\|y_0\|\le Y$。整数 $h$ 满足 $0\le h<T$ 时，称其为 $(T,\varepsilon)$-记忆视界，如果对每个 $n$ 满足 $h\le n<T$，都有

$$
\|b_n\|
+X\sum_{r=h+1}^{n}\|K_r\|
\le\varepsilon.
$$

最小这样的 $h$ 记为 $h_{\varepsilon,T}$；若没有这样的整数，则记为 $\infty$。它给出一个直接的任务判据：把 $n-h$ 步以前的可见历史以及尚未释放的初始隐藏差异删去时，下一次任务读出的误差至多为 $\varepsilon$。这里的误差是任务读出所选的范数；若 $G$ 最后产生概率分布，则可再用相应的数据处理收缩把它换成总变差界。

这个定义不同于第 52 节的逐步闭合误差。第 52 节把每一步粗粒化误差沿无记忆迭代累积；这里直接计算被隐藏动力学传播后的尾核，允许同一记录被相干复用，也允许不同延迟的记忆项发生抵消。它因此是“任务需要保留多长历史”的视界，而不是每步误差的重新命名。

### 命题 56.3（几何隐藏衰减给出可计算视界）

设存在 $M\ge1$ 和 $0\le\alpha<1$，使得

$$
\|D^r\|\le M\alpha^r\qquad(r\ge0).
$$

令 $g=\|G\|$、$b=\|B\|$、$c=\|C\|$。则任意 $h$ 都满足

$$
\|b_n\|+X\sum_{r=h+1}^{n}\|K_r\|
\le
gbM\alpha^h\left(Y+\frac{cX}{1-\alpha}\right)
\qquad(n\ge h).
$$

因此，只要 $0<\varepsilon<gbM(Y+cX/(1-\alpha))$，取

$$
h\ge
\left\lceil
\frac{\log\!\left(\varepsilon/[gbM(Y+cX/(1-\alpha))]\right)}{\log\alpha}
\right\rceil
$$

就得到一个 $(T,\varepsilon)$-记忆视界；当右端常数为零时，视界为 $0$。若 $\alpha=0$，则 $D^r=0$（$r\ge1$），记忆核在有限步内严格截断。

证明。由次乘性，$\|b_n\|\le gbM\alpha^nY\le gbM\alpha^hY$。并且

$$
\|K_r\|\le gbcM\alpha^{r-1},
$$

所以

$$
X\sum_{r=h+1}^{n}\|K_r\|
\le gbcMX\sum_{r=h+1}^{\infty}\alpha^{r-1}
=\frac{gbcM X\alpha^h}{1-\alpha}.
$$

两式相加即得。对 $0<\alpha<1$ 取对数并注意 $\log\alpha<0$，得到给出的整数条件。证毕。

### 推论 56.4（有效阶数与精确有限记忆）

在上述条件下，$h_{\varepsilon,T}$ 随 $\varepsilon$ 只按对数增长：其上界为

$$
O\!\left(\frac{\log(1/\varepsilon)}{-\log\alpha}\right).
$$

当存在 $q$ 使

$$
GBD^rC=0\quad(r>q),
\qquad
GBD^ny_0=0\quad(n>q)\quad\text{（对当前给定的初始隐藏态 $y_0$）},
$$

则 $q$ 是该任务的记忆阶数上界；若第 $q$ 延迟项实际非零，它就是精确阶数。所有超过 $q$ 的历史对任务输出都没有作用。特别地，$D^q=0$ 是一个与任务无关的充分条件，但不是必要条件，因为端口 $GB$ 或 $C$ 可能消灭长寿命隐藏方向。

在有限任务窗 $T$ 内，只有 $r<T$ 的核会出现；因此即使 $h_{\varepsilon,\infty}=\infty$，有限实验族仍可能有有限的 $h_{\varepsilon,T}$。这与第 54 节的有限实验族一致：有限视界上的对象只需对声明过的实验和长度负责。

### 反例 56.5（没有谱隙就没有普适有限视界）

若 $D$ 在某个可见端口方向上是单位模旋转，例如 $D=-I$ 且 $GB\ne0$、$C\ne0$，则

$$
K_r=GB(-I)^{r-1}C
$$

的范数不衰减。对适当的有界轨道，任意固定 $h$ 的尾和都不能由几何级数压到任意小；于是 $h_{\varepsilon,\infty}=\infty$（除非端口耦合恰好相消）。这正是第 55 节相干复用的周期回流在记忆核语言中的表现：同一记录被再次访问时，单次 Gram 因子 $|R_{ij}|<1$ 的“新记录”结论不能直接套用。

反过来，$D$ 的谱半径小于一也不足以给出一个仅由谱半径决定的短视界。非正规矩阵

$$
D=\begin{pmatrix}\alpha&L\\0&\alpha\end{pmatrix},
\qquad 0<\alpha<1,
$$

有

$$
D^r=\begin{pmatrix}\alpha^r&rL\alpha^{r-1}\\0&\alpha^r\end{pmatrix}.
$$

当 $L$ 很大时，短期回流可先放大再衰减。故需要的是可验证的范数包络（或带条件数的 Jordan 估计），不能只报告渐近谱半径。

### 命题 56.6（任务端口决定记忆，而非隐藏维数）

设隐藏空间分解为 $Y=Y_{\mathrm{seen}}\oplus Y_{\mathrm{dark}}$，且 $C$ 的像和 $GB$ 的行空间都落在 $Y_{\mathrm{seen}}$ 的相应端口闭包中。若 $D$ 在 $Y_{\mathrm{dark}}$ 上任意（甚至是幺正），则所有 $K_r=GBD^{r-1}C$ 对 $Y_{\mathrm{dark}}$ 的分量均为零；该暗子空间不增加 $h_{\varepsilon,T}$。

相反，隐藏空间可以只有一个维度而取 $D=\alpha$、$\alpha$ 任意接近一，从而使

$$
K_r=GB\,\alpha^{r-1}C
$$

保持很长的有效尾。于是“保留多少历史”既不由隐藏自由度数量决定，也不由当前记录值的数量决定，而由任务允许的输入端口、输出端口、误差和时间窗共同决定。

证明。若 $C$ 不把可见扰动送入 $Y_{\mathrm{dark}}$，且 $GB$ 不从该子空间读出，则每个乘积 $GBD^{r-1}C$ 在该分量上为零。后一断言直接取一维 $D=\alpha$ 代入定义。证毕。

### 与第 54、55 节的连接和边界

第 54 节的 $H$ 步预测等价检验“在已列实验族上能否区分历史”；本节的 $h_{\varepsilon,T}$ 检验“删去多早以前的历史后，指定读出在 $T$ 步内还差多少”。增加实验协议可能使静态商细化，即使原来的记忆视界不变；改变端口或记录复用协议也可能使同一静态商获得不同的回流核。

第 55 节的 Gram 谱给出一次记录对相干模式的模长和相位。只有在每次记录使用独立空白单元并满足相应因子化假设时，$|R_{ij}|^N$ 才能直接作为衰减律；相干复用必须通过联合实现的 $D$ 和端口核重新计算。因而 Gram 谱的谱隙、隐藏块的范数衰减与任务端口的可见性是三个相关但不等同的量。

本节也不声称任何开放量子系统都具有给定的 $(A,B,C,D)$ 分块，或把一般非马尔可夫过程自动压成有限阶经典递推。量子应用必须先给出联合通道、记录初始化和任务 POVM，再证明这些线性界适用于所选算子空间。若环境有初始相关、控制依赖历史或任务读出本身变化，应把相应记录并入状态；否则有限视界结论没有适用依据。

因此，“稳定经典现实”在这个模型中的可计算版本是：对给定实验族、端口和误差容限，存在有限 $h_{\varepsilon,T}$，使更早历史通过回流核对后续记录的影响低于 $\varepsilon$。它是任务依赖的有效阶数，而不是脱离观测协议的宇宙常数。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 57. 无限未来统计、预测商与最小动力学修复

第 54 节把对象定义在有限实验族上，第 55–56 节把记录复用和隐藏回流写成有限记忆模型。若允许继续进行同一类后续操作，还需要回答一个更强的问题：**当前记录是否足以决定所有有限次未来读数？** 这一节用 Heisenberg 迭代生成的可观测空间回答它。

本节使用仓库中已冻结的 `AllFutureStatisticsSufficiency`、`FutureStatisticsEquivalence`、`MinimalPredictiveSummary`、`OperationalReadoutQuotientRepresentation` 与 `PredictionClosureDynamicalRepair` 结果。这里的“所有未来”指给定有限初始 effect 家族、给定离散 Heisenberg 演化下的所有有限迭代；它不表示任意连续控制或任意物理实验都已包含。

### 定义 57.1（未来可见空间与预测投影）

令 $\mathcal V_0$ 是当前选定的有限 effect 家族在 traceless-Hermitian 载体中的实线性 span，令 $H$ 是 Heisenberg 迭代的实线性作用。定义

$$
\mathcal V_{\infty}
=
\operatorname{span}_{\mathbb R}
\{H^n E_i:n\in\mathbb N,\ i\in I\}.
$$

记 $P_{\infty}$ 为到 $\mathcal V_{\infty}$ 的正交投影。它只保留会在某个有限未来时刻进入所选 effect 读数的方向。

### 定理 57.2（全部未来统计的充要预测表示）

对两个 traceless-Hermitian 状态坐标 $\rho,\sigma$，有

$$
P_{\infty}\rho=P_{\infty}\sigma
\iff
\forall n\in\mathbb N,\ \forall i\in I,
\quad
\langle\rho,H^nE_i\rangle
=
\langle\sigma,H^nE_i\rangle.
$$

证明思路是把投影差为零转化为 $\rho-\sigma\in\mathcal V_{\infty}^{\perp}$，再用 span induction 将生成元上的内积相等推广到整个空间；反向则把每个 $H^nE_i$ 看作生成元。形式化定理为 `all_future_statistics_sufficiency`。

这一定义比单次读数严格：两个状态可以有相同当前概率，却在某个未来 Heisenberg 迭代的 effect 上分开。相反，若投影相同，则在这套实验协议允许的任意有限延迟下都不能分开。

### 定理 57.3（Schrödinger 读数与无限 Heisenberg span）

设 $\Phi$ 是有限维量子通道，$H$ 是其 Heisenberg 对偶，$\mathcal A_0$ 是当前 operator system。令

$$
\mathcal V_{\infty}
=\operatorname{span}_{\mathbb R}
\{H^k A:A\in\mathcal A_0,\ k\in\mathbb N\}.
$$

则两个密度态的所有未来 operator-system readout 相等，当且仅当

$$
\rho-\sigma\in\mathcal V_{\infty}^{\perp_{\operatorname{tr}}},
$$

即

$$
\left[\forall k,\quad
R_{\mathcal A_0}(\Phi^k\rho)
=
R_{\mathcal A_0}(\Phi^k\sigma)\right]
\iff
\left[\forall A\in\mathcal V_{\infty},\quad
\operatorname{Tr}\bigl((\rho-\sigma)A\bigr)=0\right].
$$

形式化定理为 `future_statistics_iff_annihilates_infinite_system`。它把“历史被丢掉”精确改写为：历史差异是否落入全部未来读数的正交核。这个核依赖初始 effect 家族和 channel 对偶，不能被称为绝对不可观测部分。

### 定理 57.4（预测充分 summary 的唯一因子化和维数下界）

令 $S$ 是当前状态的线性 summary，并假设

$$
S(x)=S(y)
\Longrightarrow
\langle x,H^nE_i\rangle
=
\langle y,H^nE_i\rangle
$$

对所有 $n,i$ 成立。则存在唯一线性映射 $L$，使

$$
P_{\infty}=L\circ S_{\rm range},
$$

并且

$$
\operatorname{finrank}(\mathcal V_{\infty})
\le
\operatorname{finrank}(\operatorname{range}S).
$$

形式化定理为 `minimal_predictive_summary`。因此“保留多少历史”在该线性模型中有一条必要条件：summary 的可达维数不能小于未来预测空间的维数。summary 可以包含额外不可见坐标，但这些坐标对当前声明的未来任务不是必要的。

### 定理 57.5（操作读数商的规范代表）

定义

$$
\rho\sim_{\mathcal A_0}\sigma
\iff
R_{\mathcal A_0}(\rho)=R_{\mathcal A_0}(\sigma).
$$

则商空间 $\mathrm{States}/\!\sim_{\mathcal A_0}$ 规范等价于实际 readout 的 range。该等价把每个状态类送到它的 readout，并保持二元密度混合：

$$
R(t\rho+(1-t)\sigma)
=tR(\rho)+(1-t)R(\sigma),
\qquad 0\le t\le1.
$$

这是 `operational_readout_quotient_representation` 的内容。故当前尺度上的“对象”可以取为操作商中的一个类；它不是脱离指定 readout 的本体标签。

### 定理 57.6（最小动力学修复）

仅有当前 visible space $\mathcal V$ 时，$\mathcal V^{\perp}$ 未必对后续演化保持不变；于是两个当前不可区分状态的差异可能在未来重新出现。令

$$
\overline{\mathcal V}
=\operatorname{span}\{(H^*)^n v:v\in\mathcal V,\ n\in\mathbb N\},
\qquad
\mathcal R=\overline{\mathcal V}^{\perp}.
$$

则 $\overline{\mathcal V}$ 是包含 $\mathcal V$ 且对 observable evolution 不变的最小扩张，$\mathcal R$ 对 adjoint evolution 不变，并且存在商上的线性演化 $\overline H$ 满足

$$
\overline H\circ\pi
=
\pi\circ H^*.
$$

形式化定理为 `prediction_closure_minimal_dynamical_repair`。这给第 50 节的经典闭合判据一个线性算子版本：若当前记录没有形成演化同余，就把可见空间闭包到最小不变空间，再在残差商上定义演化。

### Zeckendorf 前缀作为一个有误差界的预测摘要

Zeckendorf 卷定理 459.2 给出一个可直接接入本节的有限精度例子。设 $q_L(n)$ 读取自然数 $n$ 的低 $L$ 位合法 Zeckendorf 字串，设 $\alpha$ 为该卷相位定义中的黄金共轭数。若

$$
q_L(n)=q_L(m),
$$

则

$$
\left\|\alpha(n-m)\right\|\le\alpha^L,
$$

其中左侧是到最近整数的圆周距离。于是可以定义一个明确的相位记录模型

$$
|\psi_n\rangle
=\frac{|0\rangle+e^{2\pi i\alpha n}|1\rangle}{\sqrt2}.
$$

两条同前缀历史对应的纯态迹距离满足

$$
D\bigl(|\psi_n\rangle\langle\psi_n|,
|\psi_m\rangle\langle\psi_m|\bigr)
=\left|\sin\bigl(\pi\alpha(n-m)\bigr)\right|
\le\min\{1,\pi\alpha^L\}.
$$

因此，对这个特定的相位读出和任意后续 POVM，低 $L$ 位可以作为误差为 $\pi\alpha^L$ 的近似预测摘要；要让单次读出误差不超过 $\varepsilon$，一个充分条件是

$$
L\ge
\left\lceil\frac{\log(\pi/\varepsilon)}{-\log\alpha}\right\rceil.
$$

这只是一个指定记录模型中的任务界。Zeckendorf 卷定理 469.5 同时指出，同前缀相位的 Wasserstein 或 Lipschitz 误差界不自动给出总变差收敛；某些端点读出仍可把两个同前缀历史完全分开。故“前缀足够”必须连同读出类别和误差度量一起声明，不能从相位逼近直接推出完整历史已经被压缩。

### 与第 54–56 节的边界

第 54 节的有限实验族只要求在已声明的协议上响应相同；本节的 $\mathcal V_{\infty}$ 把协议固定后允许任意有限迭代，因此条件更强。第 56 节的 $h_{\varepsilon,T}$ 是给定时间窗与误差的近似记忆视界；本节给出的是精确的线性预测商，未引入范数误差或有限时间截断。实际应用中可以先取后续章节的有限稳定深度，再用第 56 节的尾核界控制截断误差。

这些定理不声称任意开放量子系统都有给定的有限维 Heisenberg 对偶，也不声称所有连续控制已被枚举；它们只在文件中明确的有限维、线性、指定 effect/channel 假设下成立。本节新增理论叙述应标记为 `repo-derived/open`；不新增 Lean 声明，也不把解释层的“客体”表述升级为普适物理定律。

## 追加锚（新终端）
## 58. Zeckendorf 黄金读数的误差预算与预测响应接口

第 54--56 节已经把对象、响应和记忆视界分开：第 54 节按指定实验族取预测等价类，第 55 节区分独立新记录与相干复用，第 56 节用输入端口、隐藏演化和输出端口定义记忆尾项。本节补上 Zeckendorf 刻度与这三个量之间的一个有限、可检验接口。

关键限制先写明。Zeckendorf 规范化给出离散整数的唯一表示；黄金读数给出一个实数嵌入。它的误差界只适用于已经规范的有限 Zeckendorf 行。对含有重复槽位的原始行，不能把同一个界直接套到未规范的字面系数上。规范化也不自动保留历史：不同原始表可能有同一个规范整数，而第 54 节的后续实验仍能将它们分开。

### 定义 58.1（规范黄金读数与刻度残差）

令

$$
\phi=\frac{1+\sqrt5}{2},\qquad
G_j=F_{j+2},
$$

并令 $s(n)$ 是低位到高位的规范 Zeckendorf 行。置

$$
\Lambda_Z(s(n))
=
\sum_{j\ge0}\phi^{j+2}s(n)_j,
\qquad
\gamma_Z(n)
=
\frac{\Lambda_Z(s(n))}{\sqrt5},
$$

其中和因 $s(n)$ 有限支撑而有限；这正是 Z 卷定义 19 的黄金值 $\beta$ 在单行规范数字上的限制。定义刻度残差

$$
\eta_Z(n)=\gamma_Z(n)-n.
$$

这里的 $\gamma_Z$ 是一个读数坐标，不是新的整数运算，也不是物理能量或 Hamiltonian 的定义。

### 命题 58.2（黄金读数的统一误差界）

对所有 $n\in\mathbb N$，

$$
\left|\eta_Z(n)\right|<\frac1{\sqrt5}.
$$

因而在任意有限窗口 $0\le n<G_L$ 上，误差上界相同；窗口长度只限制可出现的规范构型数，不会把这个读数误差自动改成零。

证明。Binet 恒等式在本索引约定下为

$$
\phi^{j+2}
=
\sqrt5\,G_j+(-\phi^{-1})^{j+2}.
$$

将 $s(n)$ 代入并除以 $\sqrt5$，得到

$$
\eta_Z(n)
=
\frac1{\sqrt5}
\sum_{j\ge0}s(n)_j(-\phi^{-1})^{j+2}.
$$

规范行只有有限个非零位，所以

$$
\left|\sum_{j\ge0}s(n)_j(-\phi^{-1})^{j+2}\right|
<
\sum_{j\ge0}\phi^{-(j+2)}
=1.
$$

最后一个严格不等式来自有限支撑；故得到所列界。这个证明只使用规范行和有限支撑，未把原始重复槽位当作规范数字。证毕。

### 定义 58.3（任务响应的刻度 Lipschitz 条件）

固定有限历史集合 $R$、规范化后的整数读数

$$
N:R\longrightarrow\mathbb N
$$

以及有限实验族 $\mathfrak T=\{\tau_i:1\le i\le m\}$。对每个实验，设输出分布为 $p_i(\,\cdot\mid r)$。若存在定义在包含所有 $N(r)$ 与 $\gamma_Z(N(r))$ 的实区间上的映射

$$
\kappa_i:\mathbb R\longrightarrow\Delta(Y_i)
$$

满足

$$
p_i(\,\cdot\mid r)=\kappa_i(N(r))
$$

以及某个 $L_i<\infty$ 使

$$
\operatorname{TV}\!\left(\kappa_i(x),\kappa_i(y)\right)
\le L_i|x-y|,
$$

则称该实验在这组历史上满足 $L_i$-刻度 Lipschitz 条件。它要求响应确实经由 $N$ 因子化；若不同原始历史具有同一个 $N$ 却有不同后续响应，该条件不成立。

用黄金坐标构造预测器

$$
\widehat p_i(\,\cdot\mid r)
=
\kappa_i\!\left(\gamma_Z(N(r))\right).
$$

### 定理 58.4（刻度误差到有限预测误差的传输）

在定义 58.3 的条件下，对所有 $r\in R$ 和 $i$，

$$
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
\widehat p_i(\,\cdot\mid r)
\right)
<
\frac{L_i}{\sqrt5}.
$$

令 $L_{\mathfrak T}=\max_iL_i$，则全部实验输出的最坏总变差误差满足

$$
\max_{r\in R,\,i\le m}
\operatorname{TV}\left(
p_i(\,\cdot\mid r),\widehat p_i(\,\cdot\mid r)
\right)
<
\frac{L_{\mathfrak T}}{\sqrt5}.
$$

证明。对每个 $i,r$ 使用 Lipschitz 条件和命题 58.2：

$$
\operatorname{TV}\!\left(
\kappa_i(N(r)),
\kappa_i(\gamma_Z(N(r)))
\right)
\le
L_i\left|N(r)-\gamma_Z(N(r))\right|
<
\frac{L_i}{\sqrt5}.
$$

对 $i$ 取最大值即得。证毕。

这个定理只控制“同一个规范整数的实数刻度近似”。它不控制规范化纤维内部的历史差异，也不证明 $\gamma_Z$ 是一个足够状态。

### 定义 58.5（规范化纤维缺陷）

不假设响应经由 $N$ 因子化。对每个实验定义规范化纤维缺陷

$$
\varepsilon_{\mathrm{fib},i}
=
\sup_{\substack{r,r'\in R\\N(r)=N(r')}}
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
p_i(\,\cdot\mid r')
\right),
$$

并令

$$
\varepsilon_{\mathrm{fib}}
=
\max_i\varepsilon_{\mathrm{fib},i}.
$$

它是第 54 节预测伪距离在规范化纤维上的直径；当纤维中没有两个不同元素时，其上确界取 $0$。$\varepsilon_{\mathrm{fib}}=0$ 才表示在所列实验族上，规范化整数已经足以代表历史。

对每个 $i$，从每个非空纤维选一个代表 $r_u$，置

$$
\bar\kappa_i(u)=p_i(\,\cdot\mid r_u).
$$

若 $\bar\kappa_i$ 在同一实区间上有 $L_i$-刻度 Lipschitz 延拓，定义代表黄金预测器

$$
\widehat p_i(\,\cdot\mid r)
=
\bar\kappa_i\!\left(\gamma_Z(N(r))\right).
$$

### 定理 58.6（历史纤维、黄金刻度与任务误差的三项分解）

在上述有限条件下，对所有 $r$ 和 $i$，

$$
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
\widehat p_i(\,\cdot\mid r)
\right)
<
\varepsilon_{\mathrm{fib},i}
+
\frac{L_i}{\sqrt5}.
$$

因此全部实验输出的最坏总变差误差满足

$$
\max_{r\in R,\,i\le m}
\operatorname{TV}\left(
p_i(\,\cdot\mid r),\widehat p_i(\,\cdot\mid r)
\right)
<
\varepsilon_{\mathrm{fib}}
+
\frac{L_{\mathfrak T}}{\sqrt5}.
$$

证明。令 $u=N(r)$，取该纤维代表 $r_u$。三角不等式给出

$$
\operatorname{TV}\!\left(
p_i(\,\cdot\mid r),
\bar\kappa_i(u)
\right)
\le
\varepsilon_{\mathrm{fib},i}.
$$

另一方面，命题 58.2 和 $\bar\kappa_i$ 的 Lipschitz 条件给出

$$
\operatorname{TV}\!\left(
\bar\kappa_i(u),
\bar\kappa_i(\gamma_Z(u))
\right)
<
\frac{L_i}{\sqrt5}.
$$

两式相加即得；再对 $i$ 和 $r$ 取最大值。证毕。

该分解把两个常被混淆的损失分开：

$$
\underbrace{\varepsilon_{\mathrm{fib}}}_{\text{规范化抹去的历史仍可被实验看见}}
\quad+\quad
\underbrace{\frac{L_{\mathfrak T}}{\sqrt5}}_{\text{黄金实数刻度的近似误差}}.
$$

第一项即使整数读数完全精确也可能存在；第二项即使历史恰好经由整数闭合也仍可能存在。更换实验族会改变第一项和各 $L_i$，所以没有脱离任务的单一“黄金现实精度”。

### 命题 58.7（与记忆视界的合并预算）

设第 56 节的 $(T,h)$ 截断在同一任务输出度量下有尾误差 $\tau_{h,T}$；也就是说，把 $n-h$ 步以前的历史和初始隐藏差异删除后，对所有 $n<T$ 的输出改变至多为 $\tau_{h,T}$。若定理 58.6 的黄金代表预测器再用于该截断模型，则总误差满足

$$
\varepsilon_{\mathrm{total}}(h,T)
<
\varepsilon_{\mathrm{fib},T}
+
\frac{L_T}{\sqrt5}
+
\tau_{h,T},
$$

其中 $\varepsilon_{\mathrm{fib},T}$ 和 $L_T$ 分别取长度不超过 $T$ 的全部实验与读出中的最大值。

若第 56 节的线性输出先经过一个以 $c_{\mathrm{out}}$ 为收缩常数的概率读出，则应取

$$
\tau_{h,T}
=
c_{\mathrm{out}}
\max_{n<T}
\left(
\|b_n\|+
X\sum_{r=h+1}^{n}\|K_r\|
\right).
$$

证明。先以真实历史与其规范化纤维代表比较，误差至多 $\varepsilon_{\mathrm{fib},T}$；再以代表的精确整数坐标与黄金坐标比较，误差至多 $L_T/\sqrt5$；最后以完整隐藏演化与 $h$-截断演化比较，误差至多 $\tau_{h,T}$。三次使用总变差的三角不等式即可。若线性尾项先在另一范数中给出，应用读出收缩性得到所列 $c_{\mathrm{out}}$ 因子。证毕。

这条合并预算的解释是：

$$
\text{总任务误差}
\le
\text{规范化纤维缺陷}
+
\text{黄金刻度误差}
+
\text{记忆尾项}.
$$

若给定目标 $\varepsilon$，只有在

$$
\varepsilon_{\mathrm{fib},T}
+
\frac{L_T}{\sqrt5}
+
\tau_{h,T}
\le\varepsilon
$$

时，才可把当前 Zeckendorf 读数、$h$-步历史截断和指定实验族一起当作一个满足该预算的有效对象。此判据仍是充分的预算检验，不是必要条件，也不是无条件的物理定律。

### 推论 58.8（响应分离的安全裕量）

设有限标签集 $U$ 的代表响应满足

$$
\Delta_T
=
\min_{\substack{u\ne v\\u,v\in U}}
\max_{i\le m}
\operatorname{TV}\!\left(
\bar\kappa_i(u),\bar\kappa_i(v)
\right)>0.
$$

若

$$
2\left(
\frac{L_T}{\sqrt5}
+
\tau_{h,T}
\right)
+
2\varepsilon_{\mathrm{fib},T}
<
\Delta_T,
$$

则任意两个不同代表在实际完整任务响应中的分离仍为正；黄金刻度与记忆截断不会在该预算内把它们保证可分的响应合并成同一个预测分布。

证明。对每个代表的近似误差用定理 58.6 和命题 58.7 控制，再对两个代表应用总变差三角不等式的反向形式：

$$
\operatorname{TV}(p_u,p_v)
\ge
\operatorname{TV}(\bar\kappa(u),\bar\kappa(v))
-
\operatorname{TV}(p_u,\bar p_u)
-
\operatorname{TV}(p_v,\bar p_v).
$$

由假设右端为正。证毕。

这里“分离仍为正”只表示在所选实验族和预算下不会被这个近似模型保证为同一分布；它不保证一次有限样本实验必然正确判别，也不产生不相容量子测量的全局答案表。

### 命题 58.9（规范化电荷的相位商）

沿用 Z 卷定理 21。若一条有限实际进位路径把原始行 $r$ 送到 $r'$，记其总电荷为 $z$，则

$$
\beta(r)-\beta(r')=z\in\mathbb Z.
$$

因此相位读出

$$
\chi(r)=\exp\!\left(2\pi i\,\beta(r)\right)
$$

满足

$$
\chi(r)=\chi(r').
$$

更一般地，若记录使用相位尺度 $\vartheta$，置 $\chi_{\vartheta}(r)=e^{i\vartheta\beta(r)}$，则

$$
\frac{\chi_{\vartheta}(r)}{\chi_{\vartheta}(r')}
=e^{i\vartheta z}.
$$

当 $\vartheta/(2\pi)\in\mathbb Z$ 时，所有规范化电荷都被该相位商抹去；当 $\vartheta/(2\pi)=a/b$ 为既约有理数时，只能看到 $z$ 模 $b$ 的信息；当 $\vartheta/(2\pi)$ 无理时，$e^{i\vartheta z}=1$ 当且仅当 $z=0$，所以不同整数电荷不会因这个相位因子相等。

证明。第一式是 Z 卷定理 21 的黄金值差公式。将其代入指数函数即得三种情形；有理情形使用 $e^{i2\pi az/b}=1$ 当且仅当 $b\mid z$，无理情形则由 $\vartheta z\in2\pi\mathbb Z$ 推出 $z=0$。证毕。

这说明“规范化前后相位相同”不是无条件事实，而是读出尺度的选择。相位只记录 $\beta$ 的某个商；若选取把整数电荷识别为零的尺度，规范化历史在该读数中严格不可见，但连续黄金值或另一相位尺度仍可能看见它。这个相位商应作为第 55 节 Gram 相位的一个明确输入参数，而不能从 Zeckendorf 唯一性自动推出。

### 与现有章节的关系和边界

第 54 节的 $d_H$ 衡量指定实验族上的预测差异；本节给出一个由 Zeckendorf 规范行到该伪距离的充分上界。第 55 节的 Gram 特征值决定记录相干的衰减与相位回流；本节的 $\eta_Z$ 是数值坐标读数误差，两者不属于同一谱，也不能用黄金误差替代 Gram 谱隙。第 56 节的 $K_r$ 和 $\tau_{h,T}$ 衡量隐藏历史回流；本节只把其尾项与规范化纤维缺陷、刻度误差用三角不等式合并，未重新假设隐藏动力学是无记忆的。

若原始表尚未规范，必须先使用 $\nu$ 或明确给出其输入行的系数界；否则 $\Lambda_Z$ 的有限误差界不适用。若环境有初始关联、实验控制依赖完整历史、或代表响应不存在 Lipschitz 延拓，则定理 58.6--58.7 的相应项只能标为未验证，不能把 $1/\sqrt5$ 冒称为总误差。若 $\varepsilon_{\mathrm{fib},T}>0$，增加数值刻度精度也不能消除被规范化抹去的历史；应扩展记录或缩小实验族。

因此，Zeckendorf 在这条主线中的作用可以精确表述为：

$$
\boxed{
\text{规范行提供离散状态，}
\quad
\gamma_Z\text{ 提供有界误差的实数坐标，}
\quad
\varepsilon_{\mathrm{fib}}\text{ 测量规范化的历史损失，}
\quad
\tau_{h,T}\text{ 测量有限记忆截断的损失。}
}
$$

稳定的经典对象只有在这三项共同落入任务误差预算时才获得操作性支持。它不要求保留全部历史，也不允许仅凭一个漂亮的黄金刻度宣称历史已经消失。

本节为 repo-derived/open 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 59. 局部读出不能凭空恢复关联方向

第 54 节把有限实验族上的响应相同定义成一个预测商，第 57 节把所有有限 Heisenberg 迭代生成的统计放进无限 operator system，第 58 节再把观察深度和有限顺序词联系起来。本节补上一条不同的边界：

> **如果读出端口只接触局部扇区，且 Heisenberg 动力学保持该局部扇区不变，那么增加局部读出次数不会凭空产生关联扇区的信息。**

这不是“局部观察永远不能做 tomography”的普遍断言，而是一个带有明确扇区保持假设的条件定理。对应的现有 Lean 模块是 D5/S3/Quantum/PredictionDepth/LocalDynamicsNoTomography.lean，其冻结声明为 local_dynamics_no_tomography。本节所有解释仍标记为 repo-derived/open；没有新增 Lean 声明、形式覆盖或冻结状态。

### 59.1 双系统的三种方向

令两个有限维系统的局部维数分别为 $$m$$ 和 $$n$$。在双系统 traceless-Hermitian 算子空间中，仓库模块 BipartiteSectorDecomposition.lean 定义了：

$$
\mathcal L_A
=
\operatorname{traceZeroHermitian}(m)
\otimes
\operatorname{scalarHermitian}(n),
$$

$$
\mathcal L_B
=
\operatorname{scalarHermitian}(m)
\otimes
\operatorname{traceZeroHermitian}(n),
$$

以及真正同时依赖两边的关联扇区：

$$
\mathcal C
=
\operatorname{traceZeroHermitian}(m)
\otimes
\operatorname{traceZeroHermitian}(n).
$$

在 Hilbert--Schmidt 实内积下，模块中的 bipartite_sector_decomposition 给出这些扇区的正交分解。相应维数为：

$$
\dim\mathcal L_A=m^2-1,
\qquad
\dim\mathcal L_B=n^2-1,
$$

$$
\dim\mathcal C=(m^2-1)(n^2-1).
$$

因此无关联局部方向的维数与真正关联方向的维数是两笔不同的账。把局部边缘读数做得更精细，只是在前两笔账内增加可见方向；它不会自动把第三笔账转移到前两笔账。

记局部可见扇区为：

$$
\mathcal V_{\mathrm{loc}}
=
\mathcal L_A+\mathcal L_B.
$$

由正交分解：

$$
\mathcal V_{\mathrm{loc}}\perp\mathcal C,
\qquad
\mathcal V_{\mathrm{loc}}\cap\mathcal C=\{0\}.
$$

这里的“方向”是算子空间中的方向，不是物理空间中的额外坐标轴。

### 59.2 扇区保持给出严格的无生成结论

设 $$H$$ 是作用在上述算子空间上的 Heisenberg 线性演化，并假设：

$$
H(\mathcal V_{\mathrm{loc}})
\subseteq
\mathcal V_{\mathrm{loc}}.
$$

那么对任意自然数 $$t$$：

$$
H^t(\mathcal V_{\mathrm{loc}})
\subseteq
\mathcal V_{\mathrm{loc}}.
$$

再因为局部扇区与关联扇区正交，有：

$$
H^t(\mathcal V_{\mathrm{loc}})\cap\mathcal C
=
\{0\}.
$$

这正是 local_dynamics_no_tomography 的两部分结论。证明只使用两步：先对 $$t$$ 做迭代归纳，得到局部扇区保持；再用正交性说明其与 $$\mathcal C$$ 的交只能是零。它没有使用“观察者在系统外部”或“意识选择结果”的假设。

若状态差方向 $$D$$ 属于关联扇区，局部初始 effect $$x$$ 属于 $$\mathcal V_{\mathrm{loc}}$$，则所有局部未来读出都满足：

$$
\left\langle D,H^t x\right\rangle=0
\qquad
\text{对所有 }t\in\mathbb N.
$$

所以同一关联方向即使在整体状态中真实存在，也不会因为重复施加同一类局部 Heisenberg 读出而进入该读数。这里的“不能恢复”是相对于指定的局部 effect 族和指定的动力学而言的。

### 59.3 一个两比特反例：局部边缘相同，关联读数相反

取两个 qubit，令 $$Z$$ 为 Pauli 矩阵。对 $$0\le\varepsilon\le1$$ 定义：

$$
\rho_{\pm}
=
\frac14
\left(
I\otimes I
\pm
\varepsilon\,Z\otimes Z
\right).
$$

这两个矩阵都是合法密度态。对任意 traceless 的局部 effect $$A\otimes I$$ 或 $$I\otimes B$$，有：

$$
\operatorname{Tr}\!\left(\rho_+(A\otimes I)\right)
=
\operatorname{Tr}\!\left(\rho_-(A\otimes I)\right),
$$

$$
\operatorname{Tr}\!\left(\rho_+(I\otimes B)\right)
=
\operatorname{Tr}\!\left(\rho_-(I\otimes B)\right).
$$

但关联 effect $$Z\otimes Z$$ 给出：

$$
\operatorname{Tr}\!\left(\rho_+(Z\otimes Z)\right)=\varepsilon,
\qquad
\operatorname{Tr}\!\left(\rho_-(Z\otimes Z)\right)=-\varepsilon.
$$

因此，局部边缘读数不能区分 $$\rho_+$$ 与 $$\rho_-$$，而联合读数可以区分。这个例子是有限矩阵计算，不是对仓库中新建定理的声明；它具体展示了 $$\mathcal C$$ 中的方向如何落在局部签名的核内。

仓库的 IncompleteObserverPhysicalCounterexample.lean 给出更一般的物理版本。冻结声明 incomplete_observer_physical_counterexample 表明：只要 identity 加上已选 centered effects 的可见空间存在非零正交残差，就能构造两个不同的 density states，它们对全部已选 effect 的读数相同。因而“当前签名相同”不能推出“整体状态相同”。

### 59.4 目标在可见扇区内，才有签名充分性

对给定 centered effects，令可见空间为：

$$
\mathcal V
=
\operatorname{span}
\left(
\{I\}\cup\{E_i\}
\right).
$$

仓库的 TargetPredictionSufficiency.lean 中，冻结声明 target_prediction_sufficiency 将两件事放在同一命题中：

$$
A\in\mathcal V
\Longrightarrow
\text{所有 }E_i\text{ 的共同读数决定 }A\text{ 的期望值};
$$

而：

$$
A\notin\mathcal V
\Longrightarrow
\text{存在读数完全相同、但 }A\text{ 期望不同的两个物理态}.
$$

因此，局部读出是否足够，不能只问“测了多少次”，还要问目标 effect 是否落在局部可见空间及其动力学闭包中。若目标关联 effect 位于 $$\mathcal C$$，而 $$H$$ 满足局部扇区保持条件，那么所有迭代后的局部读出仍在 $$\mathcal V_{\mathrm{loc}}$$ 内，目标仍然位于该读出族的不可见残差。

这也说明第 57 节的最小预测摘要必须带有任务索引。对局部任务，$$\rho_+$$ 与 $$\rho_-$$ 可以属于同一预测类；加入联合目标后，它们被拆分为不同类。对象的等价性随允许的 effect 和动力学改变，而不是由一个脱离任务的标签决定。

### 59.5 何时可以恢复关联方向？

要使关联方向进入可见响应，至少需要改变下列一项：

1. 增加一个具有关联分量的 effect，例如 $$Z\otimes Z$$；
2. 让 Heisenberg 演化违反局部扇区保持条件，使某个局部 effect 的迭代获得 $$\mathcal C$$ 分量；
3. 引入与两边共同耦合的 ancilla、联合记录或其他可执行的非局部协议。

第二种情形可写成：

$$
H(\mathcal V_{\mathrm{loc}})
\not\subseteq
\mathcal V_{\mathrm{loc}},
$$

但这只说明“有可能进入新的方向”，不自动保证已经完成 tomography。还必须计算由允许迭代生成的 visible span，并检查目标 effect 是否真的落入其中。第 57 节引用的 PredictionClosureDynamicalRepair.lean 提供了相应的最小动力学闭包框架：把初始 visible space 扩张到对演化不变的 observer closure，再在其正交残差上定义商。该框架使用有限维线性空间与伴随不变性；它不自动推广到任意开放量子系统。

### 59.6 对“保留多少历史”的含义

局部记录保留的是边缘方向；关联扇区中的差异属于当前任务的历史残差。若动力学把局部空间封闭，那么这部分残差不会通过未来局部读出回流：

$$
\mathcal R_{\mathrm{corr}}
\subseteq
\mathcal V_{\mathrm{loc}}^{\perp},
\qquad
\left\langle
\mathcal R_{\mathrm{corr}},
H^t\mathcal V_{\mathrm{loc}}
\right\rangle=0.
$$

在这种条件下，继续增加同类局部记录不会减少关联残差；需要的是扩大端口或改变动力学。反之，若存在从关联扇区到局部扇区的耦合，则历史是否必须保留取决于该耦合在指定时间窗内产生的响应大小，不能仅由隐藏空间的维数决定。

这把“稳定经典现实”的一个边界写成了可检验条件：

$$
\boxed{
\text{局部读出足够}
\iff
\text{目标与允许未来统计都落在局部可见动力学闭包内};
}
$$

$$
\boxed{
\text{局部读出不足}
\iff
\text{存在非零关联残差在全部允许局部统计中保持不可见}.
}
$$

第二个判据是相对于指定读出族的判据，不是关于所有可能实验的本体论结论。加入联合测量、改变交互作用或扩大记录端口后，等价类和所需历史预算都可能改变。

本节是 repo-derived/open 的理论追加；引用的 Lean 模块已有冻结状态，但本节没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 60. 记录作用量、相干衰减与不可逆恢复下界

> **状态：repo-derived/open。** 本节整理并连接已有 Lean 结果，没有新增声明、证明覆盖或冻结状态。引用的冻结模块包括 D5/S3/Quantum/Decoherence/RecordActionCoherenceSurvival.lean、D5/S3/Quantum/PureState/RecordCoherenceComplementarity.lean、D5/S3/Quantum/Decoherence/FiniteShiftedRecordChannel.lean 与 D5/S3/Quantum/Decoherence/FiniteRecordRecoveryError.lean。这里的“作用量”是有限记录模型中的数学量，不是一个已从项目推出的普适物理作用量。

第 55 节已经给出单步记录的 Gram 系数。本节把它累积为记录作用量，再连接到有限移位记录模型中的恢复误差下界：

$$
\text{条件记录重叠}
\longrightarrow
\text{累计相干}
\longrightarrow
\text{记录作用量}
\longrightarrow
\text{恢复误差下界}.
$$

“不可逆”首先是操作意义上的：指定记录被丢弃以后，任何只作用于剩余系统的恢复通道，都不能把最坏情形误差压到下界以下。这不等于说包括环境在内的联合幺正演化不可逆。

### 60.1 记录重叠的乘积与作用量

设有限标签集为 $$
I
$$，第 $$
r
$$ 次记录给标签 $$
i
$$ 留下归一化环境向量 $$
e_{r,i}
$$。定义单步 Gram 系数

$$
g_r(i,j)=\langle e_{r,j},e_{r,i}\rangle .
$$

归一化与 Cauchy--Schwarz 不等式给出

$$
|g_r(i,j)|\le 1.
$$

若某个相干矩阵元在每一步都乘上这个系数，则 $$
N
$$ 次记录后的累计系数为

$$
C_N(i,j)=\prod_{r<N}g_r(i,j),
$$

从而

$$
|C_N(i,j)|=\prod_{r<N}|g_r(i,j)|.
$$

在非负扩展实数中定义记录作用量

$$
\mathsf A_N(i,j)=-\log |C_N(i,j)|.
$$

当某个因子为零时，右侧按扩展值解释为无穷；这正是一次完全正交记录把该相干坐标压到零的情形。冻结定理 RecordActionCoherenceSurvival.record_action_controls_coherence_survival 给出：

$$
\mathsf A_{N+1}(i,j)\ge \mathsf A_N(i,j),
$$

以及精确的相干存活关系

$$
|\rho_N(i,j)|
=
\exp\!\bigl(-\mathsf A_N(i,j)\bigr)
|\rho_0(i,j)|.
$$

若记录作用量的平均率存在，即

$$
\lim_{N\to\infty}\frac{\mathsf A_N(i,j)}{N}=\lambda,
$$

并且初始相干非零，则相对相干的负对数率也是 $$
\lambda
$$：

$$
\lim_{N\to\infty}
\frac{-\log\!\left(|\rho_N(i,j)|/|\rho_0(i,j)|\right)}{N}
=
\lambda.
$$

若每一步满足统一严格收缩界

$$
|g_r(i,j)|\le q<1,
$$

则

$$
|C_N(i,j)|\le q^N,
\qquad
\mathsf A_N(i,j)\ge -N\log q.
$$

这给出一个可计算的记录预算。相反，若某些步满足 $$
|g_r(i,j)|=1
$$，则该方向可能只发生相位旋转而没有模长衰减，甚至周期性返回。因此，固定点呈经典形式不能单独推出所有初态都会趋向经典；还必须检查非对角 Gram 系数的模长。

把单步系数写成

$$
g_r(i,j)=|g_r(i,j)|\exp\!\bigl(\mathrm i\varphi_r(i,j)\bigr),
$$

则

$$
C_N(i,j)
=
\exp\!\left(
-\mathsf A_N(i,j)
+
\mathrm i\sum_{r<N}\varphi_r(i,j)
\right).
$$

作用量只记账模长衰减；累计相位是另一项动力学数据。不能把作用量、Zeckendorf 坐标误差或 Fibonacci 权重直接解释为物理能量或 Hamiltonian 频率。

### 60.2 记录重叠同时限制可区分性与可见相干

对两个归一化纯记录 $$
e_L,e_R
$$，令

$$
c=\langle e_L,e_R\rangle,
\qquad
\mathsf V=|c|,
\qquad
\mathsf D=\sqrt{1-|c|^2}.
$$

冻结定理 PureState.RecordCoherenceComplementarity.pure_record_distinguishability_coherence_complementarity 证明

$$
\mathsf D^2+\mathsf V^2=1.
$$

于是正交记录满足

$$
c=0
\quad\Longrightarrow\quad
\mathsf D=1,\quad \mathsf V=0,
$$

而同一量子态射线上的记录满足

$$
|c|=1
\quad\Longrightarrow\quad
\mathsf D=0,\quad \mathsf V=1.
$$

这项等式只适用于声明中的归一化纯记录，不能无条件推广到混合记录或任意开放系统。对有限记录链，可把每一步的可见度相乘：

$$
\mathsf V_N(i,j)=|C_N(i,j)|=\exp\!\bigl(-\mathsf A_N(i,j)\bigr).
$$

因此，标签差异本身不决定可区分性。两个 Zeckendorf 合法构型即使数值不同，也可能留下同一条记录射线；反过来，是否正交取决于实际记录向量，而不取决于标签名称。

### 60.3 有限移位记录通道

FiniteShiftedRecordChannel.lean 给出一个具体有限实现。令

$$
c:\mathbb Z\to\mathbb C
$$

在区间 $$
0,\ldots,N
$$ 外为零，并满足

$$
\sum_{n=0}^{N}|c(n)|^2=1.
$$

给每个系统标签 $$
i
$$ 一个整数位置 $$
q_i
$$。平移后的系数产生有限环境记录，其自相关函数为

$$
\gamma(\ell)
=
\sum_{n=0}^{N}c(n+\ell)\,\overline{c(n)}.
$$

相应通道在矩阵元上的作用为

$$
\Lambda(A)_{kl}
=
\gamma(q_k-q_l)A_{kl}.
$$

所以对角元不变，非对角元按标签位移的自相关系数缩放。该模块证明此构造来自有限维等距嵌入并实现量子通道；它没有额外证明空间局域性、指定 Hamiltonian 的守恒律、零操作成本或任意设备上的普适性。

若

$$
|\gamma(q_i-q_j)|<1,
$$

该相干方向经过一次记录即收缩；若模长等于一，则它可能只获得相位。相同的 Zeckendorf 数值差在不同记录波形下也可以对应不同的自相关值，因此离散刻度不决定记录强度。

### 60.4 恢复误差的不可绕过下界

考虑任意候选恢复通道 $$
R
$$。冻结定理 FiniteRecordRecoveryError.finite_record_recovery_error_lower_bound 假设有限支持、系数归一化，以及选定的非零位移

$$
q_i-q_j\ne0.
$$

对所有密度态取最坏情形迹距离误差，得到

$$
\boxed{
\sup_{\rho}
D\!\left(R\circ\Lambda(\rho),\rho\right)
\ge
\frac{1-|\gamma(q_i-q_j)|}{2}.
}
$$

定理源码把左侧表示为误差集合的上确界，并使用迹距离的收缩性证明该不等式。

见证态是 $$
i,j
$$ 两个标签上的对称与反对称叠加：

$$
|+\rangle=\frac{|i\rangle+|j\rangle}{\sqrt2},
\qquad
|-\rangle=\frac{|i\rangle-|j\rangle}{\sqrt2}.
$$

记录前两态的距离为

$$
D(|+\rangle\langle+|,\ |-\rangle\langle-|)=1,
$$

记录后距离变为

$$
D\!\left(
\Lambda(|+\rangle\langle+|),
\Lambda(|-\rangle\langle-|)\right)
=
|\gamma(q_i-q_j)|.
$$

任何量子通道都不会增加迹距离；将收缩性与三角不等式用于恢复后的两态，就得到上述下界。记录已经降低的这部分区分度，不能由只访问记录后系统的统一恢复无条件补回。

特别地，

$$
\gamma(q_i-q_j)=0
\quad\Longrightarrow\quad
\sup_{\rho}D(R\circ\Lambda(\rho),\rho)\ge\frac12.
$$

而

$$
|\gamma(q_i-q_j)|\approx1
$$

只表示这个下界接近零，并不保证存在零误差恢复。若恢复端还可以访问未丢弃的环境记录，问题已经变成联合系统上的恢复任务，不能继续套用只在系统端恢复的同一结论。

### 60.5 作用量、恢复下界与 Zeckendorf 接口

设有限合法 Zeckendorf 构型集合为

$$
\mathcal W_L
=
\left\{
w\in\{0,1\}^{L}:w_rw_{r+1}=0
\right\},
$$

并给每个构型一个整数标签 $$
q(w)
$$。为每个构型选择条件记录 $$
e_{r,w}
$$，便得到

$$
g_r(w,v)=\langle e_{r,v},e_{r,w}\rangle,
\qquad
C_N(w,v)=\prod_{r<N}g_r(w,v).
$$

这一步只把合法构型接入记录模型；它没有指定记录向量的制备，也没有把 Fibonacci 权重自动变成能量。若采用移位记录接口，还必须给出整数标签 $$
q(w)
$$、有限波形 $$
c
$$ 及其支持条件，才能使用 $$
\gamma(q(w)-q(v))
$$ 的恢复定理。

在该接口上，可以分别记录两种损失：

$$
\mathsf A_N(w,v)=-\log|C_N(w,v)|,
$$

以及有限移位模型中的恢复下界

$$
\varepsilon_{\mathrm{rec}}^{\mathrm{lb}}(w,v)
=
\frac{1-|\gamma(q(w)-q(v))|}{2}.
$$

前者是多步相干存活的对数记账，后者是特定一次通道的恢复障碍。两者不是同一个量，不能相加，也不能互相替代。

若每一步都有

$$
|g_r(w,v)|\le q<1,
$$

则

$$
\mathsf A_N(w,v)\ge-N\log q
$$

给出长期收缩的充分条件；若存在单位模重叠，则该方向可能持续回流。因此，判断一个记录是否足以支持稳定的经典预测，必须同时指定：

$$
\text{记录波形}
\;+\;
\text{可访问的环境范围}
\;+\;
\text{允许的恢复操作}
\;+\;
\text{预测时间窗}.
$$

仅知道 Zeckendorf 标签数量或记录次数，不足以确定这些量。

### 60.6 与前面章节的衔接和边界

第 55 节的 Gram 谱给出单步模长收缩与相位信息；本节把模长收缩累积为作用量，并用有限移位实例给出恢复下界。第 56 节的记忆视界描述隐藏变量怎样回流到读出；本节的乘积公式只适用于记录向量和相干坐标已按给定协议组成的有限链，不能替代有记忆联合演化。第 57 节的无限未来预测商决定全部指定未来统计下的不可区分类；本节只针对特定记录通道给出相干与恢复量，不等同于无限实验族的操作商。

适用边界可写成：

$$
\begin{aligned}
&\text{记录作用量：归一化记录与有限步乘积；非零初始相干用于速率商；}\\
&\text{互补关系：归一化纯记录，不自动推广到混合记录；}\\
&\text{恢复下界：有限移位记录、有限支持、非零标签位移；}\\
&\text{物理解释：不推出 Hamiltonian、空间局域性或普适恢复定理。}
\end{aligned}
$$

因此，本节支持的研究命题是：

$$
\boxed{
\text{记录作用量量化相干被削弱的累计程度，}
\quad
\text{记录自相关给出有限模型中不可逆恢复的下界。}
}
$$

它把“保留多少历史才能得到稳定现实”改写成可检验的问题：在给定 Zeckendorf 合法构型、记录协议和预测视界下，哪些相干方向的作用量已经足够大，哪些方向仍可由可访问关联恢复，以及恢复误差是否超过任务容限。

本节为 repo-derived/open 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 61. 观察精炼、商空间度量与容量守恒

第 57 节把对象定义为全部指定未来统计下的预测等价类，第 59 节说明局部端口若不接触关联扇区，就不能凭空恢复关联信息，第 60 节则给出记录作用量和恢复误差的下界。本节把“增加约束或增加读出究竟保留了什么”写成一个有限维账本：观察精炼增加可见方向，同时减少不可见残差；在固定载体上，两者的总维数保持不变。

本节使用以下冻结 Lean 结果：`ObserverRefinementVisibleResidualEquivalence.lean` 中的 `observer_refinement_visible_residual_equivalence`，`OperationalObservationKernel.lean` 中的 `operational_observation_kernel_and_metric`，以及 `ObserverCapacityConservation.lean` 中的 `observer_capacity_conservation`。正文仍是 `repo-derived/open` 解释，不新增 Lean 声明，也不把有限维结论提升为任意物理系统的普遍定律。

### 61.1 可见空间与残差空间

令系统维数为

$$
d\in\mathbb N,
$$

并在实 Hermitian 算子空间中给定一族 effect。对一个 effect 集合

$$
E\subseteq\operatorname{Herm}(d),
$$

定义包含单位方向的可见空间

$$
\mathcal V(E)
=
\operatorname{span}_{\mathbb R}
\bigl(\{I_d\}\cup E\bigr),
$$

以及其 Hilbert--Schmidt 正交残差

$$
\mathcal R(E)=\mathcal V(E)^{\perp}.
$$

单位方向单独列出，是因为密度态的归一化已经固定了迹；真正增加区分能力的是去掉单位方向以后新增的可见维数。这里的残差是相对于这组 effect 的算子空间残差，不是一个额外物理介质，也不是尚未证明存在的隐藏变量。

若两个密度态在所有选定 effect 上读数相同，它们的状态差落在相应残差中。反过来，残差方向在这些线性读数中不可见；是否能在未来出现，还要再结合第 57 节的动力学闭包条件。

### 定理 61.1（观察精炼的三重等价）

设 `one` 和 `two` 是两组有限维 Hermitian effect，`two` 至少包含 `one` 所提供的可见信息。仓库中的 `observer_refinement_visible_residual_equivalence` 给出以下等价关系：

$$
\begin{aligned}
&\text{精细签名相同}\Rightarrow\text{粗签名相同}\\
&\qquad\Longleftrightarrow\qquad
\mathcal R_{\mathrm{two}}
\subseteq
\mathcal R_{\mathrm{one}}\\
&\qquad\Longleftrightarrow\qquad
\mathcal V_{\mathrm{one}}
\subseteq
\mathcal V_{\mathrm{two}}.
\end{aligned}
$$

第一行的量词是对所有密度态对：如果两态的精细签名相等，则它们的粗签名也相等。第二行是残差包含关系；第三行是可见空间包含关系。形式化定理在有限维 Hermitian 载体上同时保留了这三个方向，因而不能把“更细”只理解成标签数量增加。

这条等价解释了为什么残差方向是反变的：读出越丰富，可见空间越大，残差越小。若只改变标签名称而没有改变 effect span，三种关系都不变，也就没有获得新的预测能力。

### 定理 61.2（观察半范数的核与商空间度量）

给定有限 effect 索引集、严格正的权重和 centered effects，定义一个加权观察半范数。冻结结果 `operational_observation_kernel_and_metric` 的第一部分把它的核识别为 effect span 的正交补：

$$
\operatorname{ker}\|D\|_{\mathrm{obs}}
=
\operatorname{span}_{\mathbb R}
\{E_i\}^{\perp}.
$$

因此，对密度态差

$$
D=\rho-\sigma,
$$

半范数为零，恰好表示当前 effect 家族无法区分这两个状态。它在状态空间上只给出伪距离；把零距离状态取商以后，诱导的 `operationalQuotientDistance` 满足非负性、对称性和三角不等式，并且

$$
\bar d([\rho],[\sigma])=0
\iff
[\rho]=[\sigma].
$$

这使“对象是一个读数等价类”获得了一个内部几何：距离不是预先附加的物理空间距离，而是由允许的 effect、权重和读出范数共同定义的操作距离。

冻结结果还给出分离条件：若原状态空间上的伪距离已经是严格距离，则这组 effect 对密度态是 informationally complete。反之，存在非零残差就意味着至少有两个不同状态落入同一个操作类。这里的 `informationally complete` 只针对指定的密度态与 effect 集合，不能推出对任意序列仪器或任意开放系统都完备。

### 定理 61.3（可见容量与残差容量守恒）

对任意 effect 集合 $E$，令

$$
C(E)
=
\dim_{\mathbb R}\mathcal V(E)-1,
\qquad
Q(E)
=
\dim_{\mathbb R}\mathcal R(E).
$$

`observer_capacity_conservation` 证明，在固定的实 Hermitian 载体上：

$$
\boxed{
C(E)+Q(E)=d^2-1.
}
$$

其中 $d^2$ 是完整 Hermitian 载体的实维数，减去一维单位方向后得到 traceless 方向总数。若粗 effect 集合包含于细 effect 集合，则

$$
C(E_{\mathrm{coarse}})
\le
C(E_{\mathrm{fine}}),
$$

并且

$$
Q(E_{\mathrm{fine}})
\le
Q(E_{\mathrm{coarse}}).
$$

所以每增加一个真正独立的可见方向，残差容量至少相应减少；如果新增 effect 落在原有 span 中，两个容量都不改变。这个守恒式给出的是维数账本，不是信息熵守恒，也不是说每个新增 effect 都携带一个独立可读取的经典 bit。

### 61.4 接到 Zeckendorf 合法构型

令

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

并把合法构型映到第 58 节的黄金坐标或某个指定的 effect 家族。若窗口扩大、记录端口增加，得到的不是自动的“更多历史”，而是一组新的 effect。应分别计算

$$
\mathcal V_L=\operatorname{span}_{\mathbb R}\bigl(\{I\}\cup E_L\bigr),
\qquad
\mathcal R_L=\mathcal V_L^{\perp},
$$

再比较

$$
C_L=\dim_{\mathbb R}\mathcal V_L-1,
\qquad
Q_L=\dim_{\mathbb R}\mathcal R_L.
$$

Zeckendorf 约束只规定合法构型集合及其离散坐标；它不自动规定 effect 的线性独立性，也不自动把窗口长度 $L$ 转成可见容量 $C_L$。若新增构型只改变编号、不改变读出 span，容量不变；若新增构型引入了新的可区分 effect，容量才增加。相应的相干与历史影响仍须用第 55、56 和 60 节的 Gram、回流和作用量计算。

### 61.5 观察距离的任务依赖

设实验族改变了 effect 集合或权重，则半范数、商空间和容量账本都会改变。于是两个状态可能满足

$$
\bar d_{\mathfrak T_1}([\rho],[\sigma])=0,
$$

而在更细任务上满足

$$
\bar d_{\mathfrak T_2}([\rho],[\sigma])>0.
$$

这不是逻辑矛盾，而是两个观察商不同。第 54 节的有限响应商、第 57 节的无限未来商和本节的线性 effect 商，只有在明确给出 effect、channel 与时间范围后才能比较。把它们不加条件地合并成一个“最终对象空间”，会丢掉它们各自的操作边界。

因此，“用多少约束保留历史”可以拆成三个可测量问题：

$$
\begin{aligned}
&\text{当前读出保留了多少可见维数？}\\
&\text{剩余残差在指定未来动力学下是否闭合？}\\
&\text{记录作用量和任务误差是否允许忽略该残差？}
\end{aligned}
$$

第一问由 $C(E)$ 和 $Q(E)$ 结算，第二问由第 57 节的 observer closure 与第 59 节的扇区保持条件结算，第三问由第 56、58、60 节的误差预算结算。三者共同决定当前尺度上是否可以把某个操作等价类当作稳定对象。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 62. 有限观察深度、稳定塔与顺序词完备性

第 61 节给出了静态观察精炼的容量守恒，但“增加一次后续操作”还需要一个时间方向的版本。本节把初始 effect 在 Heisenberg 作用下的前 $n$ 次迭代组成观察塔，证明可见空间随深度单调增加、残差反向减少，并在有限维条件下得到稳定深度。随后把同一思想推广到 sequential instrument words。

使用的冻结模块是 `FiniteTimeObserverMonotonicity.lean` 的 `finite_time_observer_monotonicity`、`CenteredEffectStabilityDepthBound.lean` 的 `centered_effect_stability_depth_bound`、`FiniteSequentialCompletenessDepth.lean` 的 `finite_sequential_completeness_depth`，以及 `UnifiedSequentialKernel.lean` 的 `unified_sequential_kernel`。本节仍为 `repo-derived/open` 理论解释，没有新增 Lean 声明。

### 定义 62.1（有限 Heisenberg 观察塔）

令 $H$ 是 Hermitian 载体上的 Heisenberg 线性作用，初始 effect 家族为

$$
E_0=\{E_i: i\in I\}.
$$

定义 horizon 为 $n$ 的可见空间

$$
\mathcal V_n
=
\operatorname{span}_{\mathbb R}
\left(
\{I\}\cup
\{H^tE_i:t<n,\ i\in I\}
\right),
$$

以及有限深度残差

$$
\mathcal R_n=\mathcal V_n^{\perp}.
$$

这里的 $n$ 是允许的后续迭代次数，不是物理时间单位；是否存在连续时间生成元需要另外的动力学假设。

### 定理 62.2（观察深度的单调性）

冻结结果 `finite_time_observer_monotonicity` 证明对每个 $n$：

$$
\mathcal V_n\subseteq\mathcal V_{n+1},
$$

并且正交残差满足反向包含

$$
\mathcal R_{n+1}subseteq\mathcal R_n.
$$

证明只使用 $t<n$ 蕴含 $t<n+1$，以及正交补对包含关系的反变性。它给出一个可计算的观察偏序：增加允许的后续操作不会让已经可见的线性方向消失，但会缩小当前任务仍无法区分的残差。

对两个状态坐标差 $D$，若

$$
D\in\mathcal R_n,
$$

则所有深度小于 $n$ 的 effect 读数都相同。若在某个更大深度首次有

$$
D\notin\mathcal R_{n+1},
$$

这说明新加入的一步确实把该历史差异带入了可见响应。这个结论是线性读数的结论，不等于一次有限样本实验必然识别出该差异。

### 定理 62.3（有限维稳定深度）

在 trace-zero Hermitian 载体上，令 `towerSpace` 表示由初始 centered effects 和前面各层的 Heisenberg 像递归生成的空间，令 `predictiveSpace` 是所有有限迭代的 span。冻结结果 `centered_effect_stability_depth_bound` 定义最小一步稳定深度

$$
\operatorname{sd}(H,E)
=\min\{m:\mathcal T_m=\mathcal T_{m+1}\}.
$$

它给出

$$
\operatorname{sd}(H,E)
\le
\dim(\mathcal V_{\infty})-\dim(\mathcal T_0),
$$

以及

$$
\dim(\mathcal V_{\infty})-\dim(\mathcal T_0)
\le
 d^2-1-\dim(\mathcal T_0).
$$

更强的是，一旦某一步满足

$$
\mathcal T_m=\mathcal T_{m+1},
$$

以后所有层都保持相同；并且

$$
\mathcal V_{\infty}
=\bigcup_{n\ge0}\mathcal T_n
=\mathcal T_{\operatorname{sd}(H,E)}.
$$

因此，在固定有限维载体与固定线性 Heisenberg 作用下，“所有有限未来 effect”虽然以无限并集定义，却有一个有限深度的线性证书。这个证书的上界来自 traceless-Hermitian 载体维数，而不是来自 Zeckendorf 窗口长度本身。

### 62.4 顺序词不是单时刻标签的重复

令 `Alphabet` 是允许的仪器字母，令

$$
\mathsf E_w
$$

表示由字 $w$ 经过指定 instrument-dual 顺序折叠得到的 sequential word effect。对一个允许词集合

$$
\mathcal A\subseteq\operatorname{List}(\mathrm{Alphabet}),
$$

定义顺序可见空间

$$
\mathcal V_{\mathcal A}
=\operatorname{span}_{\mathbb R}
\{\mathsf E_w:w\in\mathcal A\}.
$$

顺序词记录了操作次序；它不应被替换成只保存每个单步标签的无序集合。不同词可能拥有相同的最终经典标签，却对应不同的 effect 和不同的后续响应。

### 定理 62.5（统一顺序核）

冻结结果 `unified_sequential_kernel` 给出：对任意状态表示 $s$、$s'$，所有允许顺序词的统计相等，当且仅当状态差落在顺序可见空间的正交残差中：

$$
\begin{aligned}
&\forall w\in\mathcal A,
\quad
\langle s,\mathsf E_w\rangle
=
\langle s',\mathsf E_w\rangle\\
&\qquad\Longleftrightarrow\\
&s-s'\in\mathcal V_{\mathcal A}^{\perp}.
\end{aligned}
$$

因此，历史压缩的安全条件不是“最终标签相同”，而是所有允许顺序词对这两个历史给出相同统计。若再加入一个新词，空间变为

$$
\mathcal V_{\mathcal A\cup\{w_0\}},
$$

残差只会缩小或保持不变；新词是否真正增加信息，要看 $\mathsf E_{w_0}$ 是否已经落在旧 span 中。

### 定理 62.6（顺序词的有限完备深度）

若所有有限 sequential word effects 在完整实 Hermitian 载体中张成单位空间，即

$$
\operatorname{span}_{\mathbb R}
\{\mathsf E_w:w\text{ 为任意有限词}\}
=\operatorname{Herm}(d),
$$

则 `finite_sequential_completeness_depth` 保证存在某个

$$
N\le d^2-1
$$

使长度不超过 $N$ 的 sequential words 已经张成完整 Hermitian 可见空间：

$$
\operatorname{span}_{\mathbb R}
\{\mathsf E_w:\lvert w\rvert\le N\}
=\operatorname{Herm}(d).
$$

这里的完备性是假设了所有有限词的总 span 已经完整；定理只把这个无界假设压缩成一个有限深度证书，不声称任意给定仪器族自动满足它。它也不说单个时间片的 POVM 必然 informationally complete。

### 62.7 接到 Zeckendorf 窗口和记忆视界

对合法 Zeckendorf 构型集合

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

可以把窗口内每个构型映射成初始 effect，或映射成允许的 sequential word。此时有三种彼此不同的深度参数：

$$
\begin{aligned}
&L: \text{合法离散构型窗口长度},\\
&N: \text{观察词的最大操作长度},\\
&h: \text{第 56 节隐藏历史的截断深度}.
\end{aligned}
$$

$L$ 增大可能增加构型数，但不保证 $\mathcal V_L$ 增维；$N$ 增大只在新增 effect 不在旧 span 时增加可见方向；$h$ 增大控制的是隐藏回流尾，而不是线性 effect span 的稳定深度。将三者混成一个“观察深度”会把离散编码、操作次序和环境记忆混为一谈。

因此，在任务误差 $\varepsilon$ 下，一个可检查的停止判据可以写成：先找到 $N$ 使线性观察塔稳定，再估计第 56 节的记忆尾和第 58、60 节的刻度与记录误差，要求合并预算不超过 $\varepsilon$。只有在这个复合条件下，才可以把有限深度摘要作为当前任务的有效对象。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 63. 约化不可见、整体可逆与恢复误差下界

第 60 节已经把记录作用量与恢复下界分开。本节进一步区分两种常被混称为“不可逆”的现象：一是只访问约化态时无法从同一个输入恢复不同的联合记录；二是包括记录自由度在内的整体演化是否真的不可逆。仓库中的可逆复制模型给出一个明确反例：前者可以成立，而后者仍然完全可逆。

本节引用 `ReducedRecordAccessDefect.lean` 的 `reduced_irreversibility_is_access_defect`、`CanonicalRecordAccessRecovery.lean` 的 canonical-record 包装，以及 `FiniteRecordRecoveryError.lean` 的 `finite_record_recovery_error_lower_bound`。这些结果都是有限矩阵和有限通道命题，正文继续标记为 `repo-derived/open`。

### 63.1 受控复制的联合演化

令系统是一个 qubit，环境记录也是一个两态自由度。对系统矩阵 $\rho$，先把环境置于空白态，记为

$$
B(\rho).
$$

受控复制幺正 $U_{\mathrm{copy}}$ 把系统地址写入记录，得到

$$
U_{\mathrm{copy}}B(\rho)U_{\mathrm{copy}}^{\dagger}
=
J(\rho),
$$

其中 $J(\rho)$ 是带有 copied-address record 的联合态。`ReducedRecordAccessDefect` 明确构造了这个 permutation unitary，并证明其满足

$$
U_{\mathrm{copy}}^{\dagger}U_{\mathrm{copy}}=I.
$$

因此，联合系统的演化有显式逆

$$
U_{\mathrm{copy}}^{\dagger}J(\rho)=B(\rho).
$$

这一步只使用整体记录仍然可访问的假设；它没有说任何局部观察者都能访问环境。

### 定理 63.1（约化访问缺陷）

设两个系统态 $\rho,\sigma$ 满足相同的对角元

$$
\forall i,\qquad \rho_{ii}=\sigma_{ii},
$$

但存在非对角位置 $i\ne j$ 使

$$
\rho_{ij}\ne\sigma_{ij}.
$$

冻结定理 `reduced_irreversibility_is_access_defect` 给出以下同时成立的事实：

$$
\operatorname{Tr}_{E}J(\rho)
=
\operatorname{Tr}_{E}J(\sigma),
$$

但

$$
J(\rho)\ne J(\sigma),
$$

并且不存在只依赖约化态的函数 $F$，同时满足

$$
F(\operatorname{Tr}_{E}J(\rho))=J(\rho),
\qquad
F(\operatorname{Tr}_{E}J(\sigma))=J(\sigma).
$$

另一方面，访问完整记录并施加逆耦合时，分别有

$$
U_{\mathrm{copy}}^{\dagger}J(\rho)=B(\rho),
\qquad
U_{\mathrm{copy}}^{\dagger}J(\sigma)=B(\sigma).
$$

所以这里真正失败的是访问范围：相同的约化输入被要求映到两个不同联合输出，任何约化态函数都无法完成；整体联合演化仍保留了区分，并且有明确的逆。

### 63.2 与经典记录的关系

对角元相同的条件意味着，受控复制后对环境做偏迹会抹掉该模型中的非对角相干。若把环境记录也纳入整体，非对角差异并没有从联合态中消失；它只是被转移到系统—记录关联中。因而必须区分：

$$
\begin{aligned}
&\text{局部约化不可见},\\
&\text{联合态仍然不同},\\
&\text{访问联合记录后可逆恢复}.
\end{aligned}
$$

`CanonicalRecordAccessRecovery` 把同一个结论接到项目的 canonical `copiedAddressRecord`，说明这不是两个定义方向造成的记号差异。它仍然是特定 qubit 复制模型的结果，不是任意偏迹通道都可逆的断言。

这个例子也修正了“去相干就是历史删除”的说法。若记录被丢弃，历史对该局部读出不可见；若记录保留并可控，历史差异仍可能恢复。是否称为“消失”，必须先指定访问的代数和允许的恢复操作。

### 63.3 有限移位记录的通道系数

令有限记录振幅为

$$
c:\mathbb Z\longrightarrow\mathbb C,
$$

其支撑位于有限区间并满足归一化

$$
\sum_{k\in\mathbb Z}|c(k)|^2=1.
$$

定义记录自相关

$$
\gamma(\ell)
=
\sum_{k\in\mathbb Z}c(k+\ell)\,\overline{c(k)}.
$$

给每个系统标签 $i$ 一个整数位置 $q(i)$，则 `FiniteShiftedRecordChannel` 产生的 Heisenberg 作用按逐项乘法写成

$$
\Lambda(A)_{ij}
=
\gamma\bigl(q(i)-q(j)\bigr)A_{ij}.
$$

因此，对角元保持不变，非对角元由记录自相关调节。这里的 $\gamma$ 是有限移位模型的输入，不是任意记录通道都必须具有的普适函数。

`finite_record_pair_witnesses` 构造两个只在 $i,j$ 位置有相反相干符号的纯态，使其初始迹距离为

$$
D(\rho,\sigma)=1,
$$

而经过 $\Lambda$ 后的距离恰为

$$
D(\Lambda\rho,\Lambda\sigma)
=|\gamma(q(i)-q(j))|.
$$

这个见证把 Gram 或自相关系数直接连接到一个可测的最坏方向：不是所有初态都按同一个相干速率衰减，至少有一对相位方向实现该系数。

### 定理 63.2（有限记录恢复的误差下界）

对任意候选量子通道 $R$ 作为恢复操作，冻结定理 `finite_record_recovery_error_lower_bound` 给出

$$
\sup_{\tau}
D\bigl(R\Lambda(\tau),\tau\bigr)
\ge
\frac{1-|\gamma(q(i)-q(j))|}{2},
$$

其中 $q(i)-q(j)\ne0$，上确界遍历该有限标签空间的密度态。若记录完全区分这两个位置，使

$$
\gamma(q(i)-q(j))=0,
$$

则这个模型中的任何恢复都存在至少 $1/2$ 的最坏迹距离误差；若

$$
|\gamma(q(i)-q(j))|=1,
$$

该下界变为零，但这只表示该见证方向没有给出正的恢复障碍，不表示任意通道都可被完美恢复。

这个下界和第 60 节的记录作用量承担不同工作：作用量描述相干模长的累计损失；这里的下界描述在指定有限通道族中，丢弃记录后恢复误差至少有多大。二者不能互相替代。

### 63.4 接到 Zeckendorf 历史与访问预算

若把合法 Zeckendorf 构型 $w$ 映到整数位置 $q(w)$，则记录自相关只看位置差

$$
q(w)-q(v),
$$

而不自动保留完整的规范化来源。两个不同历史可以有相同位置差，因而拥有相同的该通道系数；这并不说明它们在第 54 节的全部实验族上等价。要把它们合并，仍须检查所有允许读出和后续操作。

恢复能力可以用三项预算描述：

$$
\begin{aligned}
&\text{局部可访问记录的范围},\\
&\text{记录自相关的模长 }|\gamma(\ell)|,\\
&\text{允许恢复通道的类别}.
\end{aligned}
$$

扩大访问范围可能把约化不可见变成联合可见；改变记录分布会改变 $\gamma$ 和第 60 节的作用量；限制恢复通道则会提高可达到的最坏误差。单独知道 Zeckendorf 标签的数量或记录次数，不能决定这三项。

因此，对“多少约束足以形成稳定经典现实”的一个更精确表述是：在指定访问代数和恢复通道类下，约化不可见的历史残差是否已经低于任务误差；若未低于，则需要保留记录关联或扩大可访问端口，而不是仅仅增加数值刻度精度。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 64. 记录类、指数去相干与经典块的形成

第 63 节说明偏迹后的不可见可以来自访问缺陷，而不是整体信息消灭。本节处理另一种更强的情形：当不同记录类的 Gram 重叠统一严格小于一时，重复记录会使跨类相干按明确速率收缩；同一记录类内部的矩阵元则被保留下来，极限是块对角的记录类结构。

引用的冻结模块是 `RepeatedRecordExponentialDecay.lean` 的 `repeated_record_exponential_decay`，以及 `CoherenceDecay.lean` 的 `equal_superposition_coherence_tendsto_zero`。本节只解释这些有限矩阵结论，不新增 Lean 声明，也不把指数收缩推广到未满足 Gram 假设的任意开放系统。

### 64.1 记录 Gram 系数与重复通道

设有限系统标签为 $i\in\operatorname{Fin}(d)$，每个标签对应一个归一化环境记录向量

$$
r_i=\bigl(r_{i,a}\bigr)_{a\in\operatorname{Fin}(e)},
$$

满足

$$
\sum_a|r_{i,a}|^2=1.
$$

定义记录 Gram 系数

$$
G_{ij}=\langle r_j,r_i\rangle.
$$

一次记录通道逐项作用于系统矩阵：

$$
\mathcal C(\rho)_{ij}=G_{ij}\rho_{ij}.
$$

重复 $N$ 次后，冻结定理给出精确式

$$
\bigl(\mathcal C^N(\rho)\bigr)_{ij}
=G_{ij}^{,N}\rho_{ij}.
$$

当 $i=j$ 时，归一化保证

$$
G_{ii}=1.
$$

因此对角概率不受这一记录通道改变；变化集中在非对角关系方向。

### 定理 64.1（跨记录类的指数收缩）

假设存在

$$
q\in[0,1)
$$

使得只要 $r_i\ne r_j$，就有

$$
|G_{ij}|\le q.
$$

对每个记录值 $\lambda$ 定义记录类投影 $P_\lambda$，并令 pinching 映射为

$$
\Pi(\rho)
=\sum_{\lambda}P_\lambda\rho P_\lambda.
$$

`repeated_record_exponential_decay` 同时证明三件事：

$$
\bigl(\mathcal C^N(\rho)\bigr)_{ij}
=G_{ij}^{,N}\rho_{ij},
$$

$$
\Pi(\rho)_{ij}
=
\begin{cases}
\rho_{ij},&r_i=r_j,\\
0,&r_i\ne r_j,
\end{cases}
$$

以及 Frobenius 范数界

$$
\left\|
\mathcal C^N(\rho)-\Pi(\rho)
\right\|_F
\le
q^N
\left\|
\rho-\Pi(\rho)
\right\|_F.
$$

所以极限保留的是每个记录类内部的矩阵块，而跨类相干以 $q^N$ 收缩。若记录向量两两正交，则 $q=0$，一次作用就完成跨类 pinching；若只知道 $|G_{ij}|<1$ 但没有统一有限维上界，仍需另行建立统一 $q$ 才能使用上述范数界。

### 64.2 “经典化”是块结构，不一定是完全对角化

若每个标签都有不同记录向量，记录类都是单点，$Pi(\rho)$ 是对角矩阵，此时

$$
\mathcal C^N(\rho)\longrightarrow\operatorname{diag}(\rho).
$$

但若存在 $i\ne j$ 满足

$$
r_i=r_j,
$$

则 $i,j$ 位于同一记录类，$\Pi(\rho)_{ij}=\rho_{ij}$。这些类内相干不会由该通道衰减。于是“固定点是经典的”只有在记录类全为单点时才意味着对角经典代数；一般极限是记录类块代数。

这与第 55 节的相位反例相容：若条件记录只相差一个相位，物理记录射线可能相同，跨类收缩条件并不成立；不能用固定点的形式描述替代 Gram 模长的严格假设。

`CoherenceDecay` 的 qubit 特例给出同一逻辑的极限版本：若相位阻尼系数 $c$ 满足

$$
0\le c<1,
$$

则等权叠加态的非对角矩阵元满足

$$
\bigl(\mathcal C^N(\rho)\bigr)_{01}
=\frac12c^N
\longrightarrow0.
$$

这里的严格不等式 $c<1$ 是收敛所需的条件；若 $|c|=1$，只能得到相位旋转或周期行为，不能推出衰减。

### 64.3 与 Zeckendorf 合法构型的接口

在合法窗口

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\}
$$

上，可以选择一个记录映射

$$
r:\mathcal W_L\longrightarrow\mathcal R.
$$

映射的纤维

$$
[w]_r=\{v\in\mathcal W_L:r(v)=r(w)\}
$$

决定极限块的边界。Zeckendorf 数值、激发数和局部模式都可以作为 $r$ 的候选，但它们的 Gram 重叠并不由编码本身决定。

若 $r$ 把所有合法构型分开，并且记录向量满足统一 $q<1$，则

$$
\|\mathcal C^N(\rho)-\operatorname{diag}(\rho)\|_F
\le
q^N\|\rho-\operatorname{diag}(\rho)\|_F.
$$

若 $r$ 只记录 Zeckendorf 数值的某个粗粒化，例如多个来源历史共享同一数值，则极限保留这些历史对应的块内相干；要进一步把块内结构当作经典噪声，必须增加记录 effect 或引入另一个会区分块内方向的动力学。

这给出一个比“编码有唯一表示”更严格的判据：唯一表示只说明离散标签层的规范性；经典化速度还需要记录 Gram 模长的统一谱隙

$$
1-q>0.
$$

### 64.4 作用量、误差与停止条件

指数界可转写为达到目标 Frobenius 误差 $\varepsilon$ 的充分步数：若初始跨类残差满足

$$
\|\rho-\Pi(\rho)\|_F\le M,
$$

则只要

$$
q^N M\le\varepsilon,
$$

就有

$$
\|\mathcal C^N(\rho)-\Pi(\rho)\|_F\le\varepsilon.
$$

当 $0<q<1$ 且 $M>0$ 时，一个充分的整数条件是

$$
N\ge
\left\lceil
\frac{\log(M/\varepsilon)}{-\log q}
\right\rceil.
$$

这个 $N$ 只控制跨记录类的 Frobenius 范数尾项；它不自动控制第 56 节隐藏回流、第 58 节 Zeckendorf 刻度误差、第 61 节观察残差或第 63 节访问受限的恢复误差。完整任务预算仍需把这些项按各自适用的距离和通道假设合并。

因此，本节得到的“稳定经典现实”是一个带条件的操作性结论：在记录类固定、Gram 跨类重叠统一小于一、重复通道确实按同一有限模型作用的范围内，跨类相干以指数速度进入块对角结构；块内是否继续保留历史，则由更细的记录和后续动力学决定。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 65. 多上下文读出的独立预算下界

第 61 节给出了单一观察族的可见容量守恒，第 62 节给出了顺序观测的有限稳定深度。本节问一个不同的问题：如果把读出分成多个上下文，每个上下文内部有一组归一化 outcome，那么为了让联合读出区分所有密度态，最少需要保留多少独立 outcome？

冻结模块 `D5/S3/Quantum/PredictionDepth/MultiContextBudgetLowerBound.lean` 中的 `multi_context_budget_lower_bound` 给出一个一般下界。它只使用有限维 traceless-Hermitian 载体和 informational completeness 假设；本节的 Zeckendorf 解释是接口层推导，不是该 Lean 定理的额外前提。

### 65.1 上下文、归一化与独立 outcome

令系统 Hilbert 空间维数为

$$
d\in\mathbb N,
$$

每个上下文属于有限集合

$$
X\in\mathcal X.
$$

上下文 $x$ 有 $m_x+1$ 个 outcome effect，记为

$$
E_{x,0},E_{x,1},\ldots,E_{x,m_x}.
$$

归一化条件是 centered effect 的和为零：

$$
\sum_{j=0}^{m_x}E_{x,j}=0.
$$

因此最后一个 outcome 由前 $m_x$ 个决定：

$$
E_{x,m_x}
=-\sum_{j=0}^{m_x-1}E_{x,j}.
$$

真正计入预算的是每个上下文的独立数量 $m_x$，而不是把归一化约束后的全部 outcome 数量重复相加。

### 定理 65.1（多上下文 informational completeness 下界）

若联合读出对密度态是单射，即

$$
\rho\ne\sigma
\Longrightarrow
\exists x,j,
\quad
\operatorname{Tr}(\rho E_{x,j})
e
\operatorname{Tr}(\sigma E_{x,j}),
$$

则冻结定理 `multi_context_budget_lower_bound` 证明

$$
\boxed{
 d^2-1
\le
\sum_{x\in\mathcal X}m_x.
}
$$

证明的线性核心是：所有上下文 outcome 的 span 必须覆盖完整的 traceless-Hermitian 载体，其实维数为

$$
\dim_{\mathbb R}\operatorname{Herm}_0(d)=d^2-1.
$$

每个上下文删去一个由归一化关系决定的 outcome 后，剩余独立 outcome 总数为

$$
\sum_xm_x.
$$

一个有限 spanning family 的基数不可能小于载体维数，于是得到下界。该结论不要求上下文彼此正交，也不要求它们来自同一个物理装置；只要求联合读出确实 informationally complete。

### 65.2 对 qubit 与受约束构型的含义

当 $d=2$ 时，

$$
d^2-1=3.
$$

因此，任何 informationally complete 的多上下文 qubit 读出至少需要三项独立的 traceless 方向。把它们写成三个 Pauli 方向只是一个常见实现；下界本身不依赖具体坐标选择。

对 Zeckendorf 合法窗口

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

可以把构型集合分成上下文

$$
\mathcal W_L=\bigsqcup_{x\in\mathcal X}\mathcal W_{L,x},
$$

并为每个上下文指定一组 effect。合法构型数量

$$
|\mathcal W_L|=F_{L+2}
$$

本身不是 informational completeness 的预算；它只告诉我们有多少离散基底候选。要判断这些候选是否真的提供独立读出，必须计算对应 effect 的 span，并检查是否覆盖任务所需的 traceless 方向。

因此，增加 Zeckendorf 窗口长度可能增加标签，却不一定满足

$$
\sum_xm_x\ge d^2-1.
$$

反过来，较短窗口若配备线性独立的多个上下文，也可能达到指定有限维载体的完备性。编码容量和观测容量是两笔不同的账。

### 65.3 与观察精炼和顺序深度的关系

第 61 节中的容量守恒对单个 effect span 给出

$$
C+Q=d^2-1.
$$

本节给出的多上下文下界则说明，若目标是把残差降到零，跨上下文累积的独立方向至少要填满同一个 $d^2-1$ 维 traceless 载体。第 62 节的顺序词可以提供这些方向，但每一个顺序词是否增加新维数仍要由 effect span 检验；重复一个已在 span 内的词不会增加预算。

若只要求某个目标 observable $A$ 的预测，而不是完整 informational completeness，则不必支付整个 $d^2-1$ 的预算。只要

$$
A\in\mathcal V_{\mathrm{task}},
$$

目标就由任务可见空间决定；这正是第 59 节 `TargetPredictionSufficiency` 的边界。因而本下界是完整 tomography 的必要条件，不是所有预测任务的普遍最小成本。

### 65.4 上下文预算与历史保留

把“历史保留多少”改写成上下文预算时，需要区分三层：

$$
\begin{aligned}
&\text{离散层：保留哪些 Zeckendorf 合法构型；}\\
&\text{上下文层：允许哪些读出方式和操作顺序；}\\
&\text{线性层：这些读出在 traceless 载体中提供多少独立方向。}
\end{aligned}
$$

若联合读出不是 informationally complete，剩余方向仍可能在第 57 节的未来动力学或第 63 节的完整记录访问中重新出现；不能仅因当前上下文预算不足就宣称这些方向不存在。若联合读出达到完整性，则在该有限维、指定 effect 模型内，当前密度态被唯一确定，但这仍不等于所有环境历史或所有不相容未来实验都已被编码。

所以一个可检验的预算流程是：先列出上下文及其 outcome 归一化关系，再计算独立 outcome 总数和 effect span，最后根据任务是完整 tomography 还是目标预测选择下界。Zeckendorf 只提供合法构型组织，不替代这三步线性核验。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）

## 66. 信息完备读出的有限证书

第 65 节给出了多上下文完整读出的独立预算下界，但下界本身没有说明一个已经完备的无限或任意索引 effect 家族能否压缩成有限清单。本节使用 `FiniteInformationalEffectCertificate.lean` 的 `finite_informational_effect_certificate`，把这个压缩问题写成有限证书。

本节仍限定在有限维 Hermitian 算子和密度态读出；“有限证书”表示存在一个有限子族，不表示任意实验都能自动找到该子族，也不把证书搜索过程当作物理动力学。正文为 `repo-derived/open`，没有新增 Lean 声明。

### 定理 66.1（信息完备家族的有限子证书）

令系统维数为

$$
d\in\mathbb N,
$$

并给定任意索引集上的 effect 家族

$$
\{F_i:i\in I\},
$$

其中每个 $F_i$ 是合法 effect。假设原始读出对密度态单射：

$$
\Bigl[
\forall i,
\quad
\operatorname{Tr}(\rho F_i)
=\operatorname{Tr}(\sigma F_i)
\Bigr]
\Longrightarrow
\rho=\sigma.
$$

冻结定理 `finite_informational_effect_certificate` 保证存在有限子集

$$
S\subseteq I
$$

满足

$$
|S|\le d^2-1,
$$

并且 centered effect 张成完整 trace-zero Hermitian 载体：

$$
\operatorname{span}_{\mathbb R}
\left\{
F_i-\frac{\operatorname{Tr}(F_i)}{d}I_d:i\in S
\right\}
=\operatorname{Herm}_0(d).
$$

同一个子族的原始概率读出仍然单射：

$$
\Bigl[
\forall i\in S,
\quad
\operatorname{Tr}(\rho F_i)
=\operatorname{Tr}(\sigma F_i)
\Bigr]
\Longrightarrow
\rho=\sigma.
$$

### 66.2 为什么 centered 化不丢失密度态信息

对两个密度态，迹差为零：

$$
\operatorname{Tr}(\rho-\sigma)=0.
$$

因此对任意 effect $F$，有

$$
\operatorname{Tr}\left((\rho-\sigma)
\left(F-\frac{\operatorname{Tr}(F)}{d}I_d\right)\right)
=
\operatorname{Tr}\bigl((\rho-\sigma)F\bigr).
$$

单位方向在状态差上没有贡献，centered effect 保留了区分密度态所需的全部线性信息。定理先把原始完备性转成 centered span 的完整性，再从有限维 span 中抽取至多 $d^2-1$ 个生成元；最后用上式把 centered 读数的单射性转回原始 effect 的单射性。

这说明“保留全部历史”并不等于“保留全部原始记录条目”。若任务只是区分有限维密度态，可以删除所有落在已有 centered span 中的冗余 effect，而不改变该任务的预测能力。

### 66.3 与第 65 节预算下界的夹逼

第 65 节说明，任意完整的独立 outcome 家族必须满足

$$
\text{独立 outcome 总数}\ge d^2-1.
$$

本节说明，若已经存在一个信息完备 effect 家族，则总能找到一个规模不超过同一数量的有限子证书：

$$
\boxed{
\text{完整读出的最小规模}
\le d^2-1
\le\text{任意完整读出的独立预算}.
}
$$

当某个选出的子族恰好有 $d^2-1$ 个线性独立 centered effect 时，它同时达到维数下界。若原始 effect 含有额外归一化关系或重复方向，实际可用条目数可能更多，但多出的条目不增加 centered span。

这里的“最小规模”应理解为存在性夹逼：定理保证一个不超过 $d^2-1$ 的证书，但没有声称任意给定索引排序的前 $d^2-1$ 项就构成证书，也没有提供一个通用实验搜索算法。

### 66.4 Zeckendorf 构型中的压缩准则

对合法窗口

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_rw_{r+1}=0\},
$$

若每个构型或历史来源产生一个 effect $F_w$，可以先计算 centered 家族

$$
\widetilde F_w
=F_w-\frac{\operatorname{Tr}(F_w)}{d}I_d.
$$

只有当某个新构型的 $\widetilde F_w$ 不在已有 span 中时，它才增加信息完备性证书的线性容量。Zeckendorf 的唯一规范表示保证离散标签没有字面重复，但不保证对应 effect 在线性上独立；相反，不同历史也可能产生相同 centered effect，从而在该任务中可被压缩为同一个读出方向。

因此，对 Zeckendorf 编码的一个可执行压缩检查是：

$$
\widetilde F_{w_1},\ldots,\widetilde F_{w_k}
$$

逐步加入时，记录每次 span 的维数增量，直到达到任务所需维数。完整 tomography 的终点是

$$
\dim\operatorname{span}\{\widetilde F_w\}=d^2-1;
$$

目标预测的终点则只需包含目标 observable 所在的子空间。这个判据比按构型数或 Fibonacci 维数直接估计信息量更严格。

### 66.5 与历史保留问题的边界

有限证书只保证当前指定密度态读出的完备性。它不保证：

$$
\begin{aligned}
&\text{环境记录已经被保留；}\\
&\text{所有未来 Heisenberg 迭代都在该子族 span 内；}\\
&\text{不相容测量可以同时赋予一份经典答案表；}\\
&\text{第 63 节中约化不可见的联合相干已经可恢复。}
\end{aligned}
$$

若后续动力学把目标带入新的 effect 方向，需要回到第 57、62 节扩张预测空间；若记录通道保留了同一块内相干，需要回到第 63、64 节分析访问范围和 Gram 收缩。有限证书因此是任务索引的：它压缩一个已声明读出任务的冗余，而不是宣布所有历史都已被安全删除。

本节为 `repo-derived/open` 理论追加；没有新增 Lean 声明、形式覆盖或冻结状态。

## 追加锚（新终端）


## 67. 有限读出的条件数、稳定重建与噪声预算

第 66 节的有限证书回答哪些读出足以唯一确定指定有限维密度态读出任务中的每个状态。本节再问：读数有误差、耦合的标定也有误差时，这种唯一性是否仍能支持稳定预测？本节把帧下界、最小二乘误差与标定扰动接到同一预算中。新增连接为 `repo-derived/open` 理论推导，不增加 Lean 声明或冻结状态。

### 67.1 读出方向的数目与最弱可见方向

取 $d>1$，令实内积空间

$$
\mathsf H_0=\operatorname{Herm}_0(d)
$$

由无迹 Hermitian 矩阵组成，使用 Hilbert–Schmidt 内积与范数。给定有限指标集 $I$、权重 $w_i\ge0$ 和 Hermitian 读出方向 $E_i$，定义

$$
A:\mathsf H_0\longrightarrow\mathbb R^I,
\qquad
A(D)_i=\sqrt{w_i}\,\langle D,E_i\rangle_{\mathrm{HS}}.
$$

这里的 $E_i$ 首先是线性读出方向。只有另行满足 $0\le E_i\le I$、适当归一化以及物理测量实现条件时，才能赋予其概率 effect 的解释。若 $D=\rho-\rho_\ast$，$A(D)$ 表示扣除已知参考读数后的加权差值，而非未经中心化的一份概率分布。

令 $G=A^\ast A$，并记

$$
\alpha=\lambda_{\min}(G),
\qquad
\beta=\lambda_{\max}(G).
$$

源码 `D5/S3/Observer/Linear/RobustFrameBounds.lean` 的 `robust_observer_frame_bounds` 给出这一载体上的谱帧界及单射性条件：

$$
\alpha\|D\|_{\mathrm{HS}}^2
\le\|A(D)\|_2^2
\le\beta\|D\|_{\mathrm{HS}}^2,
\qquad
A\text{ 单射}\iff\alpha>0.
$$

在 $\alpha>0$ 的范围，奇异值条件数为

$$
\kappa(A)=\sqrt{\frac{\beta}{\alpha}}.
$$

源码排除 $d=1$，因为这时无迹载体为零维，其构造没有最小特征值。源码使用 Lean 的总定义除法；$\alpha=0$ 时写出的形式商不能解释为通常数值分析中有限的可逆条件数。本节所有可逆条件数与除以 $\sqrt\alpha$ 的公式都明确要求 $\alpha>0$。

同一个有限维读出一旦单射就有正的 $\alpha$；但对一族不同读出而言，单射性不提供共同的正下界。稳定预算需要的是

$$
\alpha\ge\alpha_0>0,
$$

并且需要说明使用的坐标尺度、权重和噪声范数。

### 67.2 完备读出可以任意病态

**命题 67.1（线性完备不提供统一抗噪裕量）。** 在二维实内积载体上，取 $\varepsilon>0$ 和

$$
A_\varepsilon=
\begin{pmatrix}
1&0\\
1&\varepsilon
\end{pmatrix}.
$$

每个 $A_\varepsilon$ 都单射，但其 Gram 特征值为

$$
\lambda_\pm(\varepsilon)
=\frac{2+\varepsilon^2\pm\sqrt{4+\varepsilon^4}}{2},
$$

且 $\lambda_-(\varepsilon)\to0$、$\kappa(A_\varepsilon)\to\infty$ 当 $\varepsilon\to0^+$。不存在对这整个族统一有效的正下帧界。

证明。行列式为 $\varepsilon$，故单射；直接计算

$$
A_\varepsilon^\ast A_\varepsilon
=\begin{pmatrix}2&\varepsilon\\\varepsilon&\varepsilon^2\end{pmatrix},
$$

其特征多项式为 $\lambda^2-(2+\varepsilon^2)\lambda+\varepsilon^2$，得到所列特征值。为避免把两个接近数相减，用等价形式

$$
\lambda_-(\varepsilon)
=\frac{2\varepsilon^2}
{2+\varepsilon^2+\sqrt{4+\varepsilon^4}}.
$$

于是 $\lambda_-/\varepsilon^2\to1/2$、$\lambda_+\to2$，推出结论。更直接地，对真实向量零施加观测噪声 $(0,\nu)$，精确求解得到重建向量 $(0,\nu/\varepsilon)$；其误差为 $|\nu|/\varepsilon$。证毕。

这是一般线性读出的反例，也可以作用在 qubit 无迹空间中任意指定的二维子空间上；它本身不是一个完整 qubit POVM。两项读出接近同一方向，虽然仍线性独立，却不能稳定地区分垂直于该方向的差异。

条件数和绝对灵敏度还必须分别记账。若 $s>0$，把 $A$ 换成 $sA$，则

$$
\alpha\longmapsto s^2\alpha,
\qquad
\beta\longmapsto s^2\beta,
\qquad
\kappa(sA)=\kappa(A).
$$

同一绝对读数噪声下，重建放大因子却变成 $1/(s\sqrt\alpha)$。若只是改写单位，噪声也须同步乘以 $s$，物理预算不因此改善；若真的改变耦合，则必须重新标定噪声，不能仅凭形式缩放声称获取了更多信息。

### 67.3 最小二乘中的噪声如何进入重建

**命题 67.2（有参考读数的重建预算）。** 设 $A$ 满足下帧界 $\alpha>0$，数据模型为

$$
b=A(D)+\xi,
$$

且重建 $\widehat D$ 满足正规方程

$$
A^\ast(A\widehat D-b)=0.
$$

则

$$
\boxed{
\|\widehat D-D\|_{\mathrm{HS}}
\le\frac{\|\xi\|_2}{\sqrt\alpha}.
}
$$

证明。令 $e=\widehat D-D$。正规方程给出 $A^\ast(Ae-\xi)=0$，从而

$$
\|Ae\|_2^2=\langle Ae,\xi\rangle
\le\|Ae\|_2\|\xi\|_2.
$$

若 $Ae=0$，下帧界推出 $e=0$；否则约去 $\|Ae\|_2$。两种情形均有 $\sqrt\alpha\|e\|_{\mathrm{HS}}\le\|\xi\|_2$。这一推导的抽象有限维内积空间版本由 `D5/S3/Observer/Linear/LeastSquaresReconstructionNoiseBound.lean` 的 `least_squares_reconstruction_noise_bound` 承担。证毕。

这个命题不自行给出 $\xi$ 的统计分布或有限采样置信度。若采样、刻度近似和其他建模误差已在同一个加权数据范数中分别有界，才能用三角不等式合并。第 58 节的黄金刻度误差只有经过该节要求的响应正则性或另行证明的范数转换，才能作为这里的输入噪声界。

### 67.4 耦合标定误差与噪声共用一个预算

**定理 67.3（扰动读出的稳定裕量）。** 设 $A$ 满足帧界 $0<\alpha\le\beta$，实际用于重建的标定映射为

$$
\widehat A=A+\Delta,
\qquad
\|\Delta\|_{\mathrm{op}}\le\eta<\sqrt\alpha.
$$

则对全部 $D\in\mathsf H_0$，

$$
(\sqrt\alpha-\eta)\|D\|_{\mathrm{HS}}
\le\|\widehat A D\|_2
\le(\sqrt\beta+\eta)\|D\|_{\mathrm{HS}}.
$$

所以 $\widehat A$ 单射，且

$$
\kappa(\widehat A)
\le\frac{\sqrt\beta+\eta}{\sqrt\alpha-\eta}.
$$

若真实数据仍为 $b=AD+\xi$，而 $\widehat D$ 满足

$$
\widehat A^\ast(\widehat A\widehat D-b)=0,
$$

则

$$
\boxed{
\|\widehat D-D\|_{\mathrm{HS}}
\le
\frac{\|\xi\|_2+\eta\|D\|_{\mathrm{HS}}}
{\sqrt\alpha-\eta}.
}
$$

证明。上下界分别来自反三角不等式和三角不等式：$\|AD\|-\|\Delta D\|\le\|\widehat AD\|\le\|AD\|+\|\Delta D\|$。正的下界保证单射，极端奇异值之比给出条件数估计。再把数据改写为

$$
b=\widehat A D+(\xi-\Delta D).
$$

以 $\widehat A$ 的下帧界 $(\sqrt\alpha-\eta)^2$ 应用命题 67.2，并用 $\|\xi-\Delta D\|_2\le\|\xi\|_2+\eta\|D\|_{\mathrm{HS}}$，即得结论。证毕。

这里 $A$ 是数据真实遵循的读出，$\widehat A$ 是重建采用的标定模型；两者的角色不能在误差公式中静默互换。严格条件 $\eta<\sqrt\alpha$ 也有内容：在最弱奇异方向上，大小恰为 $\sqrt\alpha$ 的扰动就能把该方向完全消掉。

若真实状态为密度矩阵，选择参考 $\rho_\ast=I/d$，则

$$
D=\rho-I/d,
\qquad
\|D\|_{\mathrm{HS}}^2
=\operatorname{Tr}(\rho^2)-\frac1d
\le1-\frac1d.
$$

在参考读数的误差也已计入 $\xi$ 的条件下，$\|\xi\|_2\le\nu$ 给出统一预算

$$
\boxed{
\|\widehat D-D\|_{\mathrm{HS}}
\le
\frac{\nu+\eta\sqrt{1-1/d}}{\sqrt\alpha-\eta}.
}
$$

这是有限维、指定读出、确定性范数误差下的结论；$\nu$ 和 $\eta$ 必须由实际采样与标定程序提供。

### 67.5 从线性重建到合法状态与可见预测

无约束最小二乘只保证 $\rho_{\mathrm{raw}}=I/d+\widehat D$ 是迹为一的 Hermitian 矩阵，不保证正半定。可在 Hilbert–Schmidt 距离下把它投影到密度矩阵的闭凸集，得到 $\widehat\rho$。这一步与求解正规方程是两个不同操作。

**命题 67.4（凸投影与后续概率的误差）。** 设 $\rho$ 是真实密度矩阵，$\widehat\rho$ 是上述 Hilbert–Schmidt 最近点投影。若 $\|\rho_{\mathrm{raw}}-\rho\|_{\mathrm{HS}}\le r$，则

$$
\|\widehat\rho-\rho\|_{\mathrm{HS}}\le r.
$$

若此后施加同一个量子通道 $\Phi$ 和同一个有限 POVM，输出分布分别为 $p,\widehat p$，则

$$
\boxed{
\operatorname{TV}(p,\widehat p)
\le\frac12\|\Phi(\widehat\rho)-\Phi(\rho)\|_1
\le\frac12\|\widehat\rho-\rho\|_1
\le\frac{\sqrt d}{2}\,r.
}
$$

证明。记 $u=\rho_{\mathrm{raw}}$、$v=\widehat\rho$。闭凸集的最近点条件给出 $\langle u-v,\rho-v\rangle_{\mathrm{HS}}\le0$。展开 $\|u-\rho\|_{\mathrm{HS}}^2$，得到它不小于 $\|v-\rho\|_{\mathrm{HS}}^2$。后续测量和通道的迹距离收缩分别给出前两条不等式；最后一条是对至多 $d$ 个奇异值应用 Cauchy–Schwarz。证毕。

投影后的 $\widehat\rho-I/d$ 不必满足原正规方程；误差不增来自凸几何。上述后续通道必须是作用于该状态的同一个已指定通道。若真正后续还依赖未纳入状态的旧环境记录，就不能直接套用；应先扩大联合状态，或另计历史回流误差。

### 67.6 这给历史保留问题增加了哪一个约束

Zeckendorf 合法窗口确定候选构型载体，实际耦合与读出标定确定 $E_i$；权重还包含统计加权等分析选择。两者共同确定最弱可见方向及 $\alpha$。对基底作纯标签重排会给出等距的坐标变换，奇异值不变；把 Fibonacci 数值直接改当物理耦合强度，则是在改变 $A$，必须重新计算谱界。

有限证书解决的是“保留的读出是否足够”；$\alpha$ 解决的是“这些读出是否足够敏感”；$\eta$ 和 $\nu$ 解决的是“标定及采样是否准确到可以使用这种敏感度”。在完整状态重建的任务中，给定重建误差容限 $r_\ast$，一个充分条件为

$$
\eta<\sqrt\alpha,
\qquad
\nu+\eta\sqrt{1-1/d}
\le r_\ast(\sqrt\alpha-\eta).
$$

稳定预测还需后续演化对所选状态描述闭合，或者另有已校准的回流误差界。若只预测少数目标读数，则不必要求完整状态重建，所需的稳定常数应只针对那些目标；完整 tomography 的最弱方向不能自动成为所有任务的成本下界。

本节的谱帧界与最小二乘基础按上述两份项目源码定位；扰动、凸投影及任务解释属于本节的有限维连接推导。所用线性代数、最小二乘和迹距离收缩为标准数学结构，`repo-derived` 表示本卷中的组合与适用域，不声称发明这些结构。本节没有从编码推导物理耦合、采样置信度、唯一测量结果或宇宙的经典性，也没有新增 Lean 形式化或覆盖。

## 追加锚（新终端）

## 68. 适用域校准与读出约束

第 61–66 节的有限维结论可以继续使用，但需要把矩阵记号、读出类型和任务范围校准到源码实际证明的假设。本节只修正适用域，不新增 Lean 声明；正文状态为 `repo-derived/open`。

### 68.1 受控复制的恢复必须是左右共轭

第 63.1 节原先写成

$$
U_{\mathrm{copy}}^{\dagger}J(\rho)=B(\rho).
$$

这条写法应撤回。源码 `D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.lean` 的 `unitaryEvolution` 是左右乘法；定理 `reduced_irreversibility_is_access_defect` 的恢复分支实际断言

$$
\operatorname{unitaryEvolution}
\bigl(U_{\mathrm{copy}}^{\dagger},J(\rho)\bigr)
=B(\rho),
$$

亦即

$$
\boxed{
U_{\mathrm{copy}}^{\dagger}J(\rho)U_{\mathrm{copy}}=B(\rho)
}.
$$

对 $\sigma$ 同样有

$$
U_{\mathrm{copy}}^{\dagger}J(\sigma)U_{\mathrm{copy}}=B(\sigma).
$$

保留的结论是：包括记录自由度的受控复制仍由显式幺正控制，访问联合记录并施加逆耦合可以恢复；只访问偏迹后的系统矩阵，则不能由同一个函数恢复两个不同联合矩阵。这里的左右共轭是矩阵演化的必要部分，不能删去。

### 68.2 正权重改变的是度量尺度，不自动改变观察商

第 61.5 节原先说“改变 effect 集合或权重，则半范数、商空间和容量账本都会改变”。其中关于权重的部分需要撤回并加条件。

在固定 centered effect 家族、且所有权重仍满足

$$
\forall i,\qquad w_i>0,
$$

时，`D5/S3/Quantum/Measurement/OperationalObservationKernel.lean` 中的 私有引理 `operational_seminorm_kernel` 表明

$$
\ker\|D\|_{\mathrm{obs}}
=
\operatorname{span}_{\mathbb R}\{E_i\}^{\perp}
$$

与正权重的具体数值无关。加权读出只是对每个坐标乘以非零因子 $\sqrt{w_i}$；因此状态的零距离关系、`OperationalStateQuotient` 的商以及由 effect span 定义的

$$
C(E)=\dim\operatorname{span}(\{I\}\cup E)-1,
\qquad
Q(E)=\dim\operatorname{span}(\{I\}\cup E)^{\perp}
$$

保持不变。`ObserverCapacityConservation.lean` 的 `observer_capacity_conservation` 没有权重参数，正是这一点的源码边界。

应保留的校准说法是：改变严格正权重通常改变半范数和距离的数值尺度；改变 effect 集合可能改变 kernel、商和容量。若允许某些权重降为零，kernel 与商应对有效家族

$$
E_{\mathrm{eff}}=\{E_i:w_i>0\}
$$

重新计算；此时由有效家族定义的容量才可能改变，而把全部未加权 effect 仍计入 $C(E),Q(E)$ 的名义账本则不会自动改变。若权重不再严格为正，`operational_observation_kernel_and_metric` 的正权重假设不再适用。

### 68.3 多上下文预算使用的是 centered 方向

第 65.1 节中单射条件的显示式有一个排版错误：理论正文中的孤立字符 `e` 应改为数学关系符号 $\ne$。

$$
\rho\ne\sigma
\Longrightarrow
\exists x,j,
\quad
\operatorname{Tr}(\rho E_{x,j})
\ne
\operatorname{Tr}(\sigma E_{x,j}).
$$

此外，第 65 节不能把源码中的 `effect` 自动称为物理 POVM outcome。`multi_context_budget_lower_bound` 的参数类型是

$$
\operatorname{effect}(x,j):\operatorname{traceZeroHermitian}(d),
$$

并且只假设

$$
\sum_j\operatorname{effect}(x,j)=0.
$$

这表达的是 centered effect 方向的线性归一化关系；源码没有为这些项加入正半定性、$0\le E\le I$ 或原始 POVM 的

$$
\sum_jE_{x,j}=I
$$

条件。因此需撤回“这些项本身就是概率 outcome”的表述。

若从合法 POVM $(E_{x,j})_j$ 出发，应先定义

$$
\widetilde E_{x,j}
=E_{x,j}-\frac{\operatorname{Tr}(E_{x,j})}{d}I_d.
$$

原 POVM 的归一化会给出

$$
\sum_j\widetilde E_{x,j}=0,
$$

而状态差上的读数满足

$$
\operatorname{Tr}\bigl((\rho-\sigma)\widetilde E_{x,j}\bigr)
=
\operatorname{Tr}\bigl((\rho-\sigma)E_{x,j}\bigr).
$$

所以第 65.1 节的下界应保留为 centered 线性读出预算：

$$
d^2-1\le\sum_xm_x,
$$

其中 $m_x$ 是每个上下文删去一个由零和关系决定的项后，剩余 centered 方向的项数。源码虽把参数命名为 `independentCount`，却未假设这些剩余方向线性独立；它们的 span 维数只保证不超过 $m_x$。要把它解释为物理概率测量，还必须另外提供原始 POVM 的正性和单位和条件。

### 68.4 第 63 节的裸矩阵定理与密度态见证分开

`reduced_irreversibility_is_access_defect` 及其 canonical bridge 的输入是

$$
\rho,\sigma:\operatorname{QubitMatrix},
$$

源码假设只有对角元相等和某个非对角元不同；没有在该定理的参数中要求 Hermitian、正半定或迹为 $1$。因此第 63.1 节把任意参数直接称为“两个密度态”的说法应撤回，改为“两个 qubit 矩阵的线性见证”。

文件末尾的具体例子取 $\rho=|+\rangle\langle+|$、$\sigma=|-\rangle\langle-|$。从这两个归一化向量的外积可直接检验正性和迹为一；该 Lean `example` 的结论本身只记录对角相等及非对角不同。因此可以在上述合法性检验后保留如下物理实例：在这个例子中，偏迹相同、联合矩阵不同，并且联合逆耦合可恢复。一般的密度态版本需要显式加入

$$
\rho\succeq0,\quad \sigma\succeq0,
\qquad
\operatorname{Tr}\rho=\operatorname{Tr}\sigma=1,
$$

或直接引用该具体见证。

同样，第 63.3 节的恢复误差下界不是任意记录通道的定理。`FiniteRecordRecoveryError.lean` 的 `finite_record_recovery_error_lower_bound` 固定了有限支撑振幅 $c:\mathbb Z\to\mathbb C$、归一化、整数标签 $q$、非零位移 $q(i)-q(j)$，并对由 `FiniteShiftedRecordChannel` 构造的具体通道 $\Lambda$ 以及任意恢复通道 $R$ 给出

$$
\sup_{\tau}D\bigl(R\Lambda(\tau),\tau\bigr)
\ge
\frac{1-|\gamma(q(i)-q(j))|}{2}.
$$

因此应保留“该有限移位记录模型中的恢复下界”，撤回任何对任意记录通道、任意环境或普适物理恢复的外推。

### 68.5 稳定深度的维数必须区分 identity 与 centered predictive space

第 62.3 节前面定义的 $\mathcal V_n$ 包含单位方向 $I$，而源码 `CenteredEffectStabilityDepthBound.lean` 的 `towerSpace` 与 `predictiveSpace` 都位于 trace-zero Hermitian 载体。源码定理 `centered_effect_stability_depth_bound` 的精确上界是

$$
\operatorname{sd}(H,E)
\le
\dim\mathcal P_{\infty}-\dim\mathcal T_0,
$$

其中

$$
\mathcal P_{\infty}=\operatorname{predictiveSpace}(H,E),
\qquad
\mathcal T_0=\operatorname{towerSpace}(H,E,0).
$$

它还给出

$$
\dim\mathcal P_{\infty}-\dim\mathcal T_0
\le
d^2-1-\dim\mathcal T_0.
$$

因此原先写成 $\dim(\mathcal V_{\infty})-\dim(\mathcal T_0)$ 的公式应撤回，除非明确重新定义 $\mathcal V_{\infty}$ 为 centered predictive space。若保留第 62.1 节含单位的全 Hermitian 观察塔，在另行假定单位方向被单列且动力学保持相应 trace-zero 子空间时，可写

$$
\mathcal V_{\infty}=\mathbb RI\oplus\mathcal P_{\infty};
$$

此时单位方向不计入 trace-zero 稳定深度。保留的结论是：固定有限维载体和固定线性 Heisenberg 作用下，某一步 tower 稳定后以后永久稳定，并存在有限深度证书。

### 68.6 有限 effect 证书分离全部密度态

第 66.5 节把有限证书说成“当前指定密度态读出的完备性”，范围过窄。`FiniteInformationalEffectCertificate.lean` 的 `finite_informational_effect_certificate` 假设的是整个映射

$$
\rho\longmapsto
\bigl(\operatorname{Tr}(\rho F_i)\bigr)_{i\in I}
$$

在全部 $\operatorname{DensityState}(\operatorname{Fin}d)$ 上 injective。它抽取有限 $S\subseteq I$，满足

$$
|S|\le d^2-1
$$

以及

$$
\operatorname{span}_{\mathbb R}
\left\{
F_i-\frac{\operatorname{Tr}(F_i)}{d}I_d:i\in S
\right\}
=\operatorname{Herm}_0(d),
$$

并且同一子族仍分离全部密度态：

$$
\left[
\forall i\in S,
\quad
\operatorname{Tr}(\rho F_i)=\operatorname{Tr}(\sigma F_i)
\right]
\Longrightarrow
\rho=\sigma.
$$

所以应把旧说法改为“指定有限维密度态读出任务的全体状态完备性”。它仍然是任务索引的：不保证环境记录已保留，不保证未来 Heisenberg 方向仍在该子族 span 内，也不保证约化不可见的联合相干可以恢复。

### 68.7 校准后的使用规则

六项边界合并后，当前可安全使用的推理链是

$$
\begin{aligned}
&\text{centered effect span}
\longrightarrow
\text{当前读出商与残差},\\
&\text{trace-zero predictive tower}
\longrightarrow
\text{有限观察深度},\\
&\text{具体记录通道}
\longrightarrow
\text{具体相干衰减与恢复下界},\\
&\text{联合幺正}
\longrightarrow
\text{左右共轭的整体恢复}.
\end{aligned}
$$

因此，Zeckendorf 合法构型仍可作为离散索引和约束窗口；它不自动提供 POVM 正性、Hamiltonian、记录通道、全体未来完备性或环境恢复。所谓“保留多少历史”必须同时标明：使用的是哪一类 effect、是否已经 centered、动力学位于哪个 trace-zero 载体、记录通道的具体假设是什么，以及完备性是针对全部有限维密度态还是仅针对一个目标预测任务。

## 追加锚（新终端）

## 69. 面向未来任务的稳定记录与最小噪声放大

第 67 节对全部状态方向给出重建预算。但“足以预测后续相互作用”并不总是完整 tomography：有些状态差异与指定后续实验无关。对这些任务，要求全部方向都有统一正下帧界，会把无需恢复的隐藏信息也计入成本。本节把精确可见性收紧为带噪声的任务判据；新增连接为 `repo-derived/open`，不新增 Lean 声明或冻结状态。

### 69.1 当前读出与未来任务必须分别指定

令 $X,Y,Z$ 为有限维实 Hilbert 空间，当前读出为 $A:X\to Y$，未来任务为 $F:X\to Z$。它们都是线性映射。量子应用可取 $X=\operatorname{Herm}_0(d)$；任务的每个坐标是扣除已知参考后的未来期望值。若未来由已指定的通道 $\Phi$ 和读出方向 $E_j$ 构成，则

$$
F(D)_j=\operatorname{Tr}(E_j\Phi(D))
=\operatorname{Tr}(\Phi^\ast(E_j)D).
$$

因此，“未来”通过实际操作的 Heisenberg 拉回进入 $F$。如果选择多个互不相容的实验，$F(D)$ 记录的是这些不同实验各自的统计响应，不是给单次系统同时指定所有实验的预存答案。

`D5/S3/Observer/VisibleDescent/TargetObservabilityFourWayEquivalence.lean` 的 `target_observability_four_way_equivalence` 给出标量目标的纤维常值、核包含与 adjoint 像等价；`D5/S3/Quantum/PredictionDepth/TargetPredictionSufficiency.lean` 的 `target_prediction_sufficiency` 给出密度态上的可见 span 条件及其失败见证。这些判据解决精确可见性，尚需为数据误差指定数值代价。

### 69.2 任务稳定常数与一个可检验的算子不等式

**定理 69.1（任务读出的有限噪声放大判据）。** 对上述有限维线性映射，以下条件等价：

$$
\ker A\subseteq\ker F;
$$

$$
\exists L_0:\operatorname{ran}A\to Z\text{ 线性},
\qquad F=L_0A;
$$

$$
\exists c\ge0,\quad
\forall x\in X,\qquad\|Fx\|\le c\|Ax\|.
$$

第二式将 $A$ 的值视为 $\operatorname{ran}A$ 的元素，且 $L_0$ 唯一。把满足第三式的最小常数记为 $c_{\mathrm{task}}$，则

$$
\boxed{
 c_{\mathrm{task}}=\|L_0\|
 =\|FA^+\|_{\mathrm{op}}.
}
$$

这里 $A^+$ 是 Moore–Penrose 逆。$A=0,F=0$ 时约定 $c_{\mathrm{task}}=0$。核包含不成立时，记任务代价为 $+\infty$，不把零分母按总定义除法解释为零代价。对给定 $c\ge0$，上述范数不等式又等价于

$$
\boxed{
F^\ast F\preceq c^2A^\ast A,
}
$$

其中 $\preceq$ 表示自伴算子的二次型偏序。

证明。若核包含成立，定义 $L_0(Ax)=Fx$。相同读出的两个原像之差属于 $\ker A$，因此定义与代表无关；线性和唯一性随之成立。有限维使 $L_0$ 有有限算子范数，从而得到范数界。反之，把 $x\in\ker A$ 代入范数界立即得到 $Fx=0$。

由 Penrose 恒等式 $AA^+A=A$，有 $A(A^+Ax-x)=0$，核包含推出

$$
F=FA^+A.
$$

令 $P=AA^+$。Penrose 恒等式还给出 $P^2=P=P^\ast$、$\operatorname{ran}P=\operatorname{ran}A$，因此 $P$ 是到读出像空间的正交投影；由 $A^+AA^+=A^+$ 得 $A^+P=A^+$。于是

$$
FA^+=L_0P.
$$

$P$ 不扩张范数，且在像空间上为恒等，故 $\|FA^+\|=\|L_0\|$。所有可用 $c$ 的最小值正是该范数。最后，平方范数界等价于对全部 $x$ 有

$$
\langle x,(c^2A^\ast A-F^\ast F)x\rangle\ge0,
$$

即所列半正定条件。证毕。

`D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.lean` 的 `isMoorePenroseInverse_moorePenroseInverse` 及 `comp_moorePenroseInverse_comp` 提供所用的有限维 Penrose 基础。这里的任务因子化、最小算子范数及半正定判据是本节组合推导，不称为该模块已有的同名结果。

### 69.3 这个常数直接控制预测误差

**定理 69.2（任务预测与最坏有界噪声）。** 假设定理 69.1 的核包含成立，数据为 $b=Ax+\xi$，且 $\|\xi\|\le\nu$，$\nu\ge0$。定义预测

$$
\widehat f=FA^+b.
$$

则

$$
\boxed{
\|\widehat f-Fx\|\le c_{\mathrm{task}}\nu.
}
$$

对任意预测函数 $\Psi:Y\to Z$，定义确定性风险

$$
R_\nu(\Psi)
=\sup_{x\in X,\,\|\xi\|\le\nu}
\|\Psi(Ax+\xi)-Fx\|.
$$

在允许全部 $x\in X$ 和全部该范数球内噪声的线性问题中，

$$
\inf_{\Psi:Y\to Z}R_\nu(\Psi)=c_{\mathrm{task}}\nu.
$$

证明。因子化给出 $FA^+b-Fx=FA^+\xi$，得到上界。若 $c_{\mathrm{task}}\nu=0$，上界已经为零。否则，有限维单位球的紧性使像空间中存在单位向量 $y$，满足 $\|L_0y\|=c_{\mathrm{task}}$。取 $x_\ast$ 使 $Ax_\ast=\nu y$。输入 $x_\ast$ 配噪声 $-\nu y$，与输入 $-x_\ast$ 配噪声 $\nu y$，都产生 $b=0$。两者目标为 $\pm Fx_\ast$，相距 $2c_{\mathrm{task}}\nu$。任意同一预测值至少对其中一者误差不小于其半距。证毕。

这一最小最坏结论针对整个线性载体，不自动是受限密度态集合上的全局下界。若采用 $\rho_\pm=I/d\pm x_\ast$ 的物理见证，必须另外满足 $x_\ast$ Hermitian、无迹及

$$
\|x_\ast\|_{\mathrm{op}}\le1/d.
$$

即使这两个状态合法，所用噪声 $\pm\nu y$ 还必须符合允许的数据域与采样模型；若读数被解释为概率，须检验相应概率约束。因此不能仅凭状态合法就声称达到了物理实验的最小最坏下界。上界则对允许状态的任何子集继续成立。无论是否达到线性最坏下界，$c_{\mathrm{task}}$ 都是一个可计算的充分误差系数。

标量目标 $Fx=\langle f,x\rangle$ 还有直接的源码支点：`D5/S3/Observer/Conditioning/TargetVisibilityConditionCost.lean` 的 `target_visibility_condition_cost` 给出 $A^\ast a=f$ 的最小范数读出系数证书，并证明其二次条件成本。对这个 $a$，

$$
|\langle a,b\rangle-\langle f,x\rangle|
\le\|a\|\,\|\xi\|.
$$

系数范数描述绝对误差放大；称它为通常的无量纲“条件数”还需要另行指定输入输出归一化。

### 69.4 丢掉某个方向是否可接受，取决于未来操作

**命题 69.3（同一记录对不同目标有不同成本）。** 取 $0<\varepsilon\le1$，在三维实坐标上定义

$$
A_\varepsilon(x,y,z)=(x,\varepsilon y,\varepsilon z).
$$

对目标 $F_x(x,y,z)=x$ 和 $F_y(x,y,z)=y$，分别有

$$
c_x=1,
\qquad
c_y=1/\varepsilon.
$$

当 $\varepsilon=0$ 时，$F_x$ 仍可精确预测，而 $F_y$ 的核包含条件失败。

证明。$A_\varepsilon$ 可逆时，两个目标的系数行分别为 $(1,0,0)$ 和 $(0,1/\varepsilon,0)$，其 Euclidean 范数就是定理 69.1 的代价。$\varepsilon=0$ 时 $(0,1,0)\in\ker A_0$，却不在 $\ker F_y$ 中；$F_x$ 则直接是当前第一项读数。证毕。

这个例子可以实现为三个不同 qubit 测量上下文。设 $(x,y,z)$ 为 Bloch 坐标，分别使用

$$
E_{k,\pm}=\frac{I\pm s_k\sigma_k}{2},
\qquad
(s_x,s_y,s_z)=(1,\varepsilon,\varepsilon).
$$

它们均满足正性与单位和条件；每个上下文的两个概率之差为 $s_k$ 乘以相应 Bloch 分量。按这三个差值组织数据，就得到 $A_\varepsilon$。这里使用 Euclidean Bloch 范数，与第 67 节的无迹 Hilbert–Schmidt 范数相差固定因子 $\sqrt2$；跨节转换时必须同步校准。三个上下文是在分别制备的同态样本上统计，不表示同时测得单个 qubit 的三个确定值。

若未来只再读 $X$，第一项已经够用。若允许一个满足 $U^\ast XU=Y$ 的校准幺正操作，随后同样读取 $X$，则未来目标变成当前的 $Y$ 分量；例如可取 $U=e^{i\pi Z/4}$。原来没有进入第一项记录的相位方向，现在进入可见预测。因此，扩大允许操作族会改变所需记录及其稳定成本。

### 69.5 近似任务与历史尾项应在相同输出尺度上记账

精确核包含有时过强。对已指定的任务 $F$，可以选择当前读出可实现的近似任务 $F_0=L_0A$；令 $P$ 为到 $\operatorname{ran}A$ 的正交投影，取 $L=L_0P$。

**命题 69.4（近似闭合与数据噪声的任务预算）。** 若

$$
\|F-F_0\|_{\mathrm{op}}\le\delta,
\qquad
\|x\|\le M,
\qquad
b=Ax+\xi,\quad\|\xi\|\le\nu,
$$

则预测 $Lb$ 满足

$$
\boxed{
\|Lb-Fx\|\le\delta M+\|L\|\nu.
}
$$

若实际后续读数 $f_{\mathrm{actual}}$ 还满足 $\|f_{\mathrm{actual}}-Fx\|\le\mu$，则总误差不超过

$$
\delta M+\|L\|\nu+\mu.
$$

证明。恒等式 $LA=F_0$ 给出 $Lb-Fx=(F_0-F)x+L\xi$；分别应用算子范数界和三角不等式，再加上实际输出的偏差即可。证毕。

$\delta M$ 是任务不完全落在当前可见空间内的代价，$\|L\|\nu$ 是把读数噪声转换为预测误差的代价，$\mu$ 则容纳已单独证明的历史尾项或动力学失配。第 56、58 节的记忆尾界或刻度界，只有在转换成这里同一个任务输出范数后才能代入 $\mu$ 或 $\nu$。本式没有证明这些误差天然小，也没有赋予三个符号相互独立的概率意义。

### 69.6 可预测对象的候选记录应怎样比较

给定未来任务 $F$、误差容限 $\epsilon_\ast$ 和候选记录 $A_J$，可以先用

$$
\ker A_J\subseteq\ker F
$$

筛出精确足够的记录，再用

$$
F^\ast F\preceq c_J^2A_J^\ast A_J,
\qquad
c_J\nu_J\le\epsilon_\ast
$$

检验其数值稳定性。若只要求近似足够，则使用命题 69.4 的三项预算。$\nu_J$ 必须随记录方案一同标定；单纯增加权重或重复同一项，并不在固定资源下自动减少误差。

因此，记录数、采样量、可访问环境范围、预测时间和误差容限共同约束可选方案。Zeckendorf 标签可以索引 $J$，但标签数量或整数差不能替代 $A_J$ 的线性作用与噪声标定。

相对于这组任务，能够被删除的是那些不影响目标，或只在容许预算内影响目标的关系；需要保留的是会进入未来响应、且必须被稳定读取的方向。这是“保留哪些历史”的有限维任务版本。它仍需物理记录稳定性、实际环境访问条件与后续闭合共同支持，不能单凭线性预测界宣称选出了唯一经典结果。

本节的精确可见性、最小范数标量证书及 Penrose 基础分别由所引项目模块定位；多输出任务范数、最坏有界噪声、物理上下文实例与近似任务预算为本节的连接推导。它们使用标准有限维线性代数和估计论结构，不主张文献新颖性；本节未新增 Lean 形式覆盖。

## 追加锚（新终端）

## 70. 有限视界内的稳定记录、闭合缺陷与记忆容量

第 69 节把“当前记录能否预测指定目标”写成了任务级核包含和噪声常数。本节再加入记录通道的动力学条件：记录是否在每一步被重新建立，隐藏关联是否会回流，以及完全区分历史需要多大的内部记忆。新增组合为 `repo-derived/open` 理论；所引 Lean 模块是现有冻结结果，本节没有新增 Lean 声明。

### 70.1 固定点、吸引子与记录闭合是三件事

设 $\mathcal E$ 是一个有限维量子记录通道，$\Phi$ 是下一步系统演化。若记录是完整正交 pinching，则已有 `FiniteRecordPinchingIdempotence.finite_record_pinching_idempotent` 给出

$$
\mathcal E^2=\mathcal E.
$$

因此 $\operatorname{im}\mathcal E$ 是重复记录后不再改变的子空间。这个事实只说明记录结构是幂等的，不说明任意态会趋近它。

在条件记录向量 $|r_i\rangle$ 的模型中，`EnvironmentMarginalChannel.environment_marginal_channel` 给出

$$
\mathcal E(\rho)_{ij}=R_{ij}\rho_{ij},
\qquad
R_{ij}=\langle r_j,r_i\rangle.
$$

`SingletonRecordClassicality.singleton_record_classicality` 在 $i\ne j$ 时只要求 $R_{ij}\ne1$，即可推出固定点中的相应非对角项为零。若进一步存在统一的

$$
|R_{ij}|\le q<1
$$

跨记录类界，`RepeatedRecordExponentialDecay.repeated_record_exponential_decay` 才给出到记录类 pinching 的收缩，例如

$$
\|\mathcal E^N(\rho)-\mathcal P(\rho)\|_F
\le
q^N\|\rho-\mathcal P(\rho)\|_F.
$$

所以应区分：

$$
\text{幂等固定结构}
\quad\ne\quad
\text{对它的吸引性}
\quad\ne\quad
\text{与下一步动力学的预测闭合}.
$$

当 $|R_{ij}|=1$ 而 $R_{ij}\ne1$ 时，非对角项可以只发生相位旋转；固定点可能是经典的，单次迭代却不收敛。这个边界不能用“已经发生记录”替代。

### 70.2 逐步记录时的精确闭合缺陷

假设每一步都执行同一个记录通道。定义两个从当前完整状态到下一次记录的通道：

$$
A=\mathcal E\Phi,
\qquad
B=\mathcal E\Phi\mathcal E.
$$

$A$ 先让完整状态演化再记录；$B$ 先丢弃当前记录看不见的部分，再演化和记录。若存在记录层通道 $\overline\Phi:\operatorname{im}\mathcal E\to\operatorname{im}\mathcal E$ 使

$$
A=\overline\Phi\mathcal E,
$$

则当前记录是这一步的封闭状态描述。由于 $\mathcal E^2=\mathcal E$，这等价于

$$
\boxed{
\mathcal E\Phi=\mathcal E\Phi\mathcal E.
}
$$

如果只要求有限精度，定义

$$
\delta
=
\sup_{\rho\in\mathsf D}
D\!\left(\mathcal E\Phi(\rho),
\mathcal E\Phi\mathcal E(\rho)\right),
$$

其中 $\mathsf D$ 是指定密度态集合，$D$ 是迹距离。这里的 $\delta$ 衡量当前删去的部分在下一次记录中重新显现的最大幅度。

**命题 70.1（逐步记录的有限视界误差）。** 令 $A=\mathcal E\Phi$、$B=\mathcal E\Phi\mathcal E$，两者均为量子通道，并假设每一步都在记录之后继续演化。若

$$
\sup_{\rho\in\mathsf D}D(A\rho,B\rho)\le\delta,
$$

则对任意初态 $\rho$ 和整数 $n\ge1$，

$$
D(A^n\rho,B^n\rho)\le n\delta.
$$

证明。通道的迹距离收缩性给出

$$
D(A\sigma,A\tau)\le D(\sigma,\tau),
\qquad
D(B\sigma,B\tau)\le D(\sigma,\tau).
$$

插入望远镜分解

$$
A^n-B^n
=
\sum_{k=0}^{n-1}A^{n-1-k}(A-B)B^k
$$

的逐步态版本。第 $k$ 项的距离贡献不超过 $\delta$，已有贡献不会被后续通道放大，故归纳得到

$$
e_{n+1}\le e_n+\delta,
\qquad e_0=0.
$$

因此 $e_n\le n\delta$。证毕。

当要求视界 $n$ 内的记录分布误差不超过 $\varepsilon$ 时，一个充分条件是

$$
\boxed{n\delta\le\varepsilon.}
$$

这个命题只适用于“每一步重新建立记录”的无记忆协议。若同一个记录单元被相干复用，旧关联会留在联合系统中，过程不再由固定的 $B$ 描述；第 55 节的相位回流模型已经给出相同单步作用可以周期性恢复相干的反例。此时必须把记录单元并入状态，或建立带记忆的多时误差界。

### 70.3 完全区分历史的容量下界

设记忆系统维数为 $d_M$，用一个 POVM $(E_j)_j$ 读取它。若有 $N$ 个历史被编码为密度矩阵 $\rho_1,\ldots,\rho_N$，并且满足

$$
\operatorname{Tr}(E_j\rho_i)=\mathbf 1_{i=j},
$$

则 `FiniteMemoryHistoryCapacity.finite_memory_history_capacity` 给出

$$
\boxed{N\le d_M.}
$$

证明的线性核心是：每个 $\rho_i$ 的支撑落在 $E_i$ 的值域，每个不同历史的支撑彼此正交；$d_M$ 维空间至多容纳 $d_M$ 个非零两两正交向量。

若记忆由 $b$ 个量子比特构成，$d_M=2^b$，则完全区分 $N$ 个历史要求

$$
\boxed{b\ge\lceil\log_2N\rceil.}
$$

对长度 $L$、禁止相邻 $1$ 的 Zeckendorf 合法窗口，候选构型数为

$$
|\mathcal W_L|=F_{L+2}.
$$

若每个合法构型都必须在一次读取中被完全区分，记忆维数至少为 $F_{L+2}$。若实验族只区分这些构型的 $N$ 个未来响应类，则容量下界只对 $N$ 生效，而不是对全部 $F_{L+2}$ 个标签生效。

这是编码容量和预测容量的区别：增加 Zeckendorf 合法字串会增加候选标签，但只有当它们落入不同的任务响应类时，才增加必须保留的记录数。近似区分时，$N\le d_M$ 不再是充分描述；需要改用记录态的迹距离、Gram 重叠或本节的闭合缺陷 $\delta$。

### 70.4 投影动力学何时可以写成经典转移

`ProjectedUnistochasticDynamics.projected_dynamics_is_unistochastic` 对每一步执行构型投影的协议给出

$$
K_{ij}=|U_{ij}|^2,
$$

以及

$$
\mathbf p_{n+1}=K\mathbf p_n.
$$

$K$ 是双随机矩阵。这个结论的前提是每一步确实插入了投影；未测量的连续幺正演化不自动服从同一个 $K$。源码中的 `initialWeights` 也没有自动假设非负和归一，所以只有另外加入概率向量条件时，$\mathbf p_n$ 才能直接称为概率分布。

因此，经典转移矩阵不是从“有一个量子基底”自动得到的，而是从

$$
\text{指定投影协议}
+
\text{幺正演化}
+
\text{概率初始条件}
$$

共同得到的。更换为相干复用协议，或者把投影记录留在可访问环境中，都会改变有效过程。

### 70.5 稳定经典对象的有限视界定义

给定实验族 $\mathfrak T$、视界 $H$ 和容许误差 $\varepsilon$，对两个历史 $h,h'$ 定义

$$
 h\sim_{\mathfrak T,H,\varepsilon}h'
$$

当且仅当任意 $T\in\mathfrak T$、任意长度不超过 $H$ 的记录序列，其输出概率分布的总变差距离不超过 $\varepsilon$。

这个关系把三种条件放在同一个对象定义中：

$$
\begin{aligned}
&\text{当前读出足以区分哪些历史；}\\
&\text{记录通道是否在视界内近似闭合；}\\
&\text{隐藏历史是否通过回流在视界内重新可见。}
\end{aligned}
$$

若固定记录通道满足 $|R_{ij}|\le q<1$，则第 70.1 节提供指数项 $q^H$；若逐步闭合缺陷为 $\delta$，则第 70.2 节提供 $H\delta$；若读数存在任务噪声，则第 69 节提供 $c_{\mathrm{task}}\nu$。在这些项都被转换到同一个输出距离后，可以使用

$$
\boxed{
\text{总预测误差}
\le
\text{记录收缩尾项}
+
\text{闭合缺陷项}
+
\text{读出噪声项}
+
\text{其余已标定的历史回流项}.
}
$$

因此当前尺度上的“经典对象”是一个有限预测等价类，而不是脱离实验协议的绝对实体。更换允许的实验族、视界、记录访问范围或误差容限，可能细化或合并这些类。

本节组合了现有记录通道、pinching 幂等性、有限记忆容量与投影动力学的边界；`StaticLossVersusReturnFlow` 仍只提供一般实线性回流反例，不能被当作量子通道定理。Zeckendorf 在这里提供合法构型的离散索引，尚未由本仓量子模块自动生成 Fibonacci 约束 Hilbert 空间或其 Hamiltonian。不从这些有限模型推出唯一测量结果、宇宙经典性或物理耦合常数。

## 71. 幂等记录的有限视界强化与近似记忆容量

第 70 节给出的逐步误差界

$$
D(A^n\rho,B^n\rho)\le n\delta
$$

适用于一般的逐步通道比较，但在本卷当前采用的 pinching 协议中，还可以利用记录映射的幂等性得到更强的结论。令

重复施加记录映射本身满足 $\mathcal E^n=\mathcal E$（$n\ge1$），所以它在一次作用后就到达自己的固定像空间。这里需要区分的是：幂等性不保证一个另行指定的未记录演化 $\Phi$ 会把完整状态吸引到这个像空间，也不保证记录对 $\Phi$ 之后的预测闭合。

$$
A=\mathcal E\Phi,
\qquad
B=\mathcal E\Phi\mathcal E,
\qquad
\mathcal E^2=\mathcal E.
$$

由于 $\mathcal E$ 是记录后的 pinching，$A\rho$ 和 $B\rho$ 都属于 $\operatorname{im}\mathcal E$。若 $\sigma\in\operatorname{im}\mathcal E$，则 $\mathcal E\sigma=\sigma$，从而

$$
A\sigma
=\mathcal E\Phi\sigma
=\mathcal E\Phi\mathcal E\sigma
=B\sigma.
$$

也就是说，$A$ 与 $B$ 在第一次记录之后限制为同一个像空间内的通道。设

$$
\delta
=
\sup_{\rho\in\mathsf D}
D(A\rho,B\rho),
$$

其中现在明确取 $\mathsf D$ 为全部有限维密度态，且假设 $\mathcal E$ 与 $\Phi$ 都是保持密度态域的 CPTP 通道，$\mathcal E$ 还满足幂等性。若只在一个真子集上取上确界，则还必须另加条件 $B^k(\rho)\in\mathsf D$，才能把同一上界用于后续轨道。

则对任意 $n\ge1$，迹距离收缩性给出

$$
\boxed{
D(A^n\rho,B^n\rho)
\le
D(A\rho,B\rho)
\le
\delta.
}
$$

证明可以写成一行递归。令 $C$ 为 $A$ 与 $B$ 在 $\operatorname{im}\mathcal E$ 上共同的限制，则

$$
A^n\rho=C^{n-1}A\rho,
\qquad
B^n\rho=C^{n-1}B\rho.
$$

于是

$$
D(A^n\rho,B^n\rho)
=D(C^{n-1}A\rho,C^{n-1}B\rho)
\le D(A\rho,B\rho).
$$

因此，在固定、无记忆、每步都重新 pinching 的协议中，$n\delta$ 是通用的累积上界，而

$$
\boxed{
D(A^n\rho,B^n\rho)\le\delta\quad(n\ge1)
}
$$

是利用幂等记录结构得到的强化。这个强化不适用于相干复用同一个记录单元的协议：那时完整联合态未必在每一步落入同一个无记忆像空间，旧关联可以沿联合动力学返回可见部分。故“误差是否随视界线性累积”本身也是协议相关的性质。

### 71.1 完全容量与近似容量必须分开

第 70 节的

$$
N\le d_M
$$

有一个不可省略的前提：同一个记忆 POVM 必须**完美区分**所编码的 $N$ 个状态，即存在结果标签 $j$ 满足

$$
\operatorname{Tr}(E_j\rho_i)=\mathbf 1_{i=j}.
$$

这个条件推出不同记忆态支撑两两正交，所以 $N$ 不得超过记忆 Hilbert 空间维数 $d_M$。若记忆由 $b$ 个 qubit 构成，才可进一步得到

$$
b\ge\lceil\log_2N\rceil.
$$

因此，Zeckendorf 合法窗口的数量

$$
|\mathcal W_L|=F_{L+2}
$$

只有在**每一个合法构型都必须由一次读取完全区分**时，才给出

$$
d_M\ge F_{L+2}.
$$

若实验只要求区分 $N$ 个未来响应类，容量下界只在**同一个记忆 POVM 能完美恢复这 $N$ 个类的标签**时作用于这 $N$ 类。仅仅有不同的未来概率律，并不推出一次读取就能完美区分它们。如果若干合法字串在允许实验族中产生相同响应，它们可以共享同一条记录，不需要为每个 Zeckendorf 标签配置独立记忆。

完全区分之外，还有两个不同的近似问题。

第一，可以要求不同记忆态的迹距离至少为某个阈值：

$$
D(\rho_i^M,\rho_j^M)\ge 1-\varepsilon.
$$

这给出有限误差下的可区分性问题，容量不再由一个整数 $N\le d_M$ 单独刻画，而要同时依赖 $d_M$、$\varepsilon$ 和允许的测量族。

第二，可以直接控制记录态的 Gram 矩阵

$$
G_{ij}=\langle r_j|r_i\rangle.
$$

其中 $|G_{ij}|$ 小表示两条记录的相干重叠小，$G_{ij}$ 接近单位模则表示它们即使带有不同相位，也没有形成稳定的可区分记录。对于条件记录通道，非对角系统项按

$$
\rho_{ij}\longmapsto G_{ij}\rho_{ij}
$$

变化。因此，近似记录应同时报告：

$$
\text{状态可区分度 }D(\rho_i^M,\rho_j^M),
\qquad
\text{相干重叠 }|G_{ij}|,
\qquad
\text{视界内闭合缺陷 }\delta.
$$

它们分别回答“能否读出”“相干还剩多少”和“被省略的部分会不会回来”。把这三个量压成单一的历史条数，会丢掉协议与时间尺度的信息。

### 71.2 对稳定经典对象的修正定义

给定实验族 $\mathfrak T$、预测视界 $H$、误差容限 $\varepsilon$ 和记录访问范围 $\mathfrak R$，可以定义当前对象的有限响应**容差关系**：

$$
h\sim_{\mathfrak T,H,\varepsilon,\mathfrak R}h'
$$

当且仅当对所有 $T\in\mathfrak T$，所有长度不超过 $H$ 的记录序列，以及所有允许的记录访问操作 $R\in\mathfrak R$，两段历史给出的输出分布总变差距离不超过 $\varepsilon$。当 $\varepsilon=0$ 时它才是严格的输出等价关系；当 $\varepsilon>0$ 时一般不传递，不能直接把它称为等价类。若需要有限误差下的类，必须另行指定聚类规则或先取精确等价商再定义近似邻域。

在这个定义下，“需要保留多少历史”不是一个脱离协议的常数，而是以下数据的函数：

$$
\boxed{
\text{所需记忆}
=
\text{响应类数量}
+
\text{记录态的近似区分成本}
+
\text{视界内的回流与闭合误差}.
}
$$

若实验族缩小、访问范围减少或视界变短，原先不同的历史可能落入同一个容差邻域；若允许更强的联合操作或更长的视界，它们又可能被重新区分。这种相对性有明确的操作索引，并不等于任意描述都同样有效。闭合缺陷 $\delta$ 也不是独立的近似判别误差；要谈近似容量，还需指定要判别的标签、允许的 POVM 和错误准则。

因此，本卷目前能够支持的最严格表述是：

$$
\boxed{
\text{稳定的经典现实}
=
\text{在指定实验族、记录访问范围和有限视界内，}
\text{对后续响应近似闭合的有限记录类}.
}
$$

这一定义保留了三条边界。记录通道的固定点可以是经典的，但不保证具有吸引性；完全记忆容量只在完美区分前提下给出维数下界；Zeckendorf 的 Fibonacci 计数只统计候选合法构型，不自动等于必须保留的物理记忆数。第 70 节的收缩尾项、闭合缺陷项和噪声项只有在它们分别比较同一协议中的相应端点、所有需要的前缀以及联合历史寄存器（必要时还包括参考系统）时，才能合成为一个输出误差界；当前写法应读作带这些条件的三角不等式模板，而不是已经证明的多时自适应记录定理。后续若要把这条主线推进为新的 Lean 内容，最小的可复用目标是分别形式化幂等像空间上的一次性误差界，以及带 Gram/迹距离阈值和明确判别任务的近似记忆容量，而不是把它们合并成一个无条件的“经典化定理”。

## 72. 仪器级历史误差、参考系统与自适应读出

第 70–71 节的 $\delta$ 比较的是系统末态：它可以说明一次记录后系统态相差多少，却不能自动说明完整的多时记录分布相差多少。要把“历史是否被保留”放到可检验的对象上，需要把记录仪器和它写下的经典寄存器一起纳入通道。

设 $\{\mathcal I_y\}_{y\in Y}$ 是一个有限结果的量子仪器。每个 $\mathcal I_y$ 是完全正的无迹非增映射，非选择通道为

$$
\mathcal N=\sum_{y\in Y}\mathcal I_y.
$$

以下假设 $\mathcal N$ 是 CPTP；因此 $\mathcal I_y$ 是一组合法的仪器分支。若实际模型只给出一个未归一化的 CP 分支，必须另外保留其发生概率，不能直接把条件化后的态代入下面的无条件距离界。

用经典寄存器 $C$ 保存结果，定义仪器的非选择抬升：

$$
\widehat{\mathcal I}(\rho)
=
\sum_{y\in Y}
|y\rangle\langle y|_C\otimes\mathcal I_y(\rho).
$$

若 $R$ 是没有被仪器直接读取的参考系统，则抬升到联合系统的通道为

$$
\widehat{\mathcal I}_R
=
\operatorname{id}_R\otimes\widehat{\mathcal I}.
$$

这一步不是给系统添加一个外部观察者。$C$ 是整体内部的一部分，$R$ 则表示我们允许在检验时保留的关联自由度。只对系统取边缘，或者只看单步的 $\mathcal N(\rho)$，都会忘掉这两个寄存器中的可用区别。

### 72.1 完整历史的通道距离

设 $\Phi_k$ 是第 $k$ 个时间槽的物理演化，$\widehat A_k$ 和 $\widehat B_k$ 是同一记录协议下的两种候选槽通道。例如，未先丢弃当前不可见部分的候选可以写成

$$
\widehat A_k
=
\widehat{\mathcal I}_k\Phi_k,
$$

而先执行当前粗粒化的候选写成

$$
\widehat B_k
=
\widehat{\mathcal I}_k\Phi_k\mathcal E_k.
$$

这里的帽号表示：槽通道同时更新系统和历史寄存器；它不是只对系统矩阵取一个偏迹。令

严格地说，$\widehat A_k$、$\widehat B_k$ 应是同一累计协议中的完整轮次通道：它们把

$$
X_k=H_{k-1}\otimes S_k\otimes M_k
$$

映到共同的

$$
X_{k+1}=H_k\otimes S_{k+1}\otimes M_{k+1},
$$

旧历史由恒等或共同控制保留，必要时对 codomain 做 padding。$\eta_k$ 是这两个完整映射的半 diamond 距离；这样 $\widehat A_{1:n}=\widehat A_n\circ\cdots\circ\widehat A_1$ 的复合才有类型。只定义 $S\to C\otimes S$ 的单槽映射还不足以直接写望远镜复合。

$$
\eta_k
=
\frac12
\left\|
\widehat A_k-\widehat B_k
\right\|_\diamond,
$$

其中 diamond 范数已经对任意有限维参考系统取上确界。设 $\widehat A_{1:n}$ 与 $\widehat B_{1:n}$ 是由这些槽按同一历史寄存器协议组成的 $n$ 步过程通道，则通道范数的望远镜展开给出

$$
\boxed{
\frac12
\left\|
\widehat A_{1:n}-\widehat B_{1:n}
\right\|_\diamond
\le
\min\!\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
}
$$

在均匀界 $\eta_k\le\eta$ 下，这给出 $\min\{1,n\eta\}$。证明只使用每个槽的三角不等式、其余槽通道的 diamond 收缩性，以及望远镜分解；因此它比较的是完整抬升过程，而不是把系统末态距离误称为历史分布距离。

对任意初始联合态 $\rho_{RS}$，有

$$
\frac12
\left\|
\bigl(\operatorname{id}_R\otimes\widehat A_{1:n}\bigr)(\rho_{RS})
-
\bigl(\operatorname{id}_R\otimes\widehat B_{1:n}\bigr)(\rho_{RS})
\right\|_1
\le
\min\!\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
$$

再对系统、参考或量子寄存器取偏迹，并对 $C$ 做任意经典读出，距离只能下降。因此，对完整记录序列的概率分布 $p_{1:n}$、$q_{1:n}$，总变差距离满足

$$
\boxed{
\operatorname{TV}(p_{1:n},q_{1:n})
\le
\min\!\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
}
$$

这个结论给出了“保留的历史是否足以区分两种过程”的直接判据：必须先指定记录寄存器和参考系统，再计算抬升过程的通道距离。

### 72.2 幂等记录的强化范围

一次性界只有在固定的累计空间上才可使用。令 $X$ 是包含系统、历史寄存器和活动工作记忆的固定有限维空间，另以 $R$ 表示未被过程直接操作的惰性参考系统；$P:X\to X$ 是 CPTP 且满足

$$
P^2=P.
$$

令 $A,B:X\to X$ 是 CPTP，并假设

$$
P\circ A=A,
\qquad
P\circ B=B,
\qquad
A\circ P=B\circ P
$$

最后一个等式要作为完全有界映射理解，即对任意参考系统 $R$ 都有

$$
(A\otimes\operatorname{id}_R)\circ(P\otimes\operatorname{id}_R)
=
(B\otimes\operatorname{id}_R)\circ(P\otimes\operatorname{id}_R).
$$

在这些条件下，归纳得到 $A^mP=B^mP$，并且对 $n\ge1$ 有

$$
A^n-B^n=A^{n-1}P(A-B).
$$

因此

$$
\boxed{
\frac12\lVert A^n-B^n\rVert_\diamond
\le
\frac12\lVert A-B\rVert_\diamond.
}
$$

这里的 $P$ 必须是固定累计空间上的 endomap。新鲜记录的抬升通常是 $S\to C\otimes S$，第二次作用已经改变了空间，不能直接写成 $P^2$；若每轮都追加新历史，应该使用 72.1 的完整轮次通道和式。若旧记录被相干地重新写入，也必须把它放进 $X$ 后重新检查完全有界的 $A\circ P=B\circ P$，不能只用系统态上的相等。

这一区分解释了两个看似矛盾的事实：一次系统记录可以已经落在经典像空间，而完整历史过程仍然保留跨时关联；一次系统态的误差可以不随 $n$ 累积，而自适应控制器对整段记录的可区分误差仍然需要逐槽预算。

### 72.3 自适应协议与参考系统不能被省略

若第 $k+1$ 个操作根据前面记录 $y_{1:k}$ 选择不同的 $\Phi_{k+1,y_{1:k}}$，则过程不再是一个与历史无关的固定幂。可以把经典控制器并入 $C$，把每个分支的控制动作写进一条抬升通道；对所有分支统一取 diamond 范数后，72.1 的望远镜界仍可使用。这里要求实际协议和理想协议使用同一个控制器；若控制器本身也随协议改变，其差异必须计入相应的 $\eta_k$。若控制器还保有会在后续操作中参与的量子记忆，则必须把该记忆并入活动系统和通道；只有从整个过程中始终不被操作的辅助系统，才可作为惰性参考 $R$。否则只比较系统边缘会漏掉可重新参与的相位。对经典历史寄存器逐分支取最大误差，只能在每一步先去相干、输入确实是经典块对角时替代整合通道的 diamond 范数。

因此，对任意长度不超过 $H$ 的前缀都要分别检查

$$
\operatorname{TV}(p_{1:k},q_{1:k})
\le
\sum_{j=1}^{k}\eta_j,
\qquad
1\le k\le H,
$$

不能用终点 $k=H$ 的界替代所有前缀，也不能把只对 $\mathcal E^H$ 成立的 $q^H$ 衰减直接套到交错的 $\mathcal E\Phi$ 过程。若研究的是联合历史、参考系统和自适应策略的最坏情况，所需对象是过程或 comb 的距离；系统态的单步闭合缺陷只是其中一个输入量。

### 72.4 与 Zeckendorf 合法构型的连接

对长度 $L$ 的无相邻 $1$ 合法窗口

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
|\mathcal W_L|=F_{L+2},
$$

可以把 $w$ 作为仪器输入标签，把记录结果 $y_w$ 作为内部历史寄存器的一个槽，并假设这些标签两两不同、来自同一个 POVM。只有在同一个槽的 POVM 对所需的构型或未来响应类满足

$$
\Pr(y=y_w\mid w')
=
\mathbf 1_{w=w'}
$$

时，才可以把 $F_{L+2}$ 直接代入完美记忆容量下界。若仪器只保留 Zeckendorf 数值的某个函数，或只需预测后续任务 $F(w)$，则应先按仪器级响应分组，再对真正需要区分的标签数使用容量定理。

在近似情形，给定容许错误 $\epsilon$，应报告

$$
\operatorname{TV}(p_{1:H},q_{1:H}),
\qquad
D(\rho_w^M,\rho_{w'}^M),
\qquad
\left|\langle r_{w'}\mid r_w\rangle\right|,
$$

并说明它们对应的是完整历史、记忆态还是单步相干。最后一个 Gram 重叠只适用于条件记录是纯态 $|r_w\rangle$ 的情形；若记录态是混态，应改报迹距离、保真度或明确选定的广义 Gram 量。三者不能互相替代。于是，Zeckendorf 提供的是合法输入的递归索引；仪器抬升决定哪些索引进入历史；diamond 或过程距离决定这些历史在允许参考系统和控制器下是否仍可被区分。

若记忆态或参考系统本身可被后续操作访问，它们必须计入活动系统的维数与通道；若它们被声明为不可访问环境，则只能在明确取迹后使用收缩性。对后选择分支，归一化会除以分支概率，可能放大条件误差，所以必须使用未归一化 CP 分支的距离，或另给出统一的分支概率下界。

本节还需要一个编码层面的限定。`FiniteMemoryHistoryCapacity` 的有限索引结论适用于同一个 POVM 完美区分 $N$ 个密度态；把 $|\mathcal W_L|=F_{L+2}$ 代入它，还需要给出合法窗口与 $\operatorname{Fin}(F_{L+2})$ 的明确枚举或双射。若只知道构型计数而没有这条重索引，不能直接把 Fibonacci 数写成定理中的 $N$。若记忆可访问的是联合 $M\otimes R$，容量维数也应取联合空间；多轮自适应协议可以使用较小的瞬时记忆，不能从单轮的 $F_{L+2}$ 计数推出每一轮都需要同样大小的记忆。

上述 diamond 望远镜、过程抬升和自适应控制边界是本卷在已有记录、偏迹和容量结果上的新组合；它们不是当前仓库已经冻结的单一 Lean 定理。涉及具体仪器时，仍需在选定的有限维通道、Kraus 数据、记录空间和 axiom 闭包下单独形式化与构建。

本节把“历史回流”从系统末态的比喻改写成了一个可计算的过程级问题：先固定仪器、记录寄存器、参考系统和控制策略，再对完整过程取距离。没有这些对象，单个 $\delta$、单个 $q^H$ 或单个历史条数都不足以证明稳定的经典预测。

## 73. 预测尾空间的最小维数与 Zeckendorf 记录压缩

第 71 节的记忆容量回答的是“要一次完全区分多少个记录态”，第 72 节的过程距离回答的是“两个完整仪器协议相差多少”。两者之间还缺一个更贴近预测的问题：如果我们只要求重现允许实验的全部未来响应，当前状态描述的最小线性维数是多少？

设 $K$ 是一个域，$U$ 是输入方向空间，$Y$ 是读出方向空间，给定一列线性响应

$$
 m=(m_n)_{n\ge0},
 \qquad
 m_n:U\to Y.
$$

这里的 $m_n$ 可以是第 $n$ 步的记录期望、中心化 effect 的坐标，或固定实验族下的线性概率响应。它不是自动等于完整密度矩阵；若原始概率带有归一化约束，应先明确选取线性坐标和剩余的归一化条件。

定义所有未来尾的线性空间：

$$
\mathcal T(m)
=
\operatorname{span}_K
\left\{
 i\longmapsto m_{i+j}(u):
 j\in\mathbb N,\ u\in U
\right\}
\subseteq(\mathbb N\to Y).
$$

它保留的不是历史词的身份，而是历史在所有未来时刻和允许输入方向下能够产生的响应形状。相同的当前读数但不同的未来尾，会在这个空间中留下不同方向。

### 73.1 有限尾空间恰好等价于有限线性预测实现

仓库的 `D5.S3.Observer.Hankel.SequenceHankelRealization` 已给出以下等价关系：

$$
\boxed{
\mathcal T(m)\text{ 有限维}
\iff
\text{存在有限维线性系统完整重现 }m.
}
$$

更具体地，若系统为

$$
(V,A,B,C),
\qquad
A:V\to V,\quad B:U\to V,\quad C:V\to Y,
$$

其 Markov 响应为

$$
 m_n=C A^n B,
$$

则每个未来尾都来自 $V$ 的像，所以

$$
\dim\mathcal T(m)\le\dim V.
$$

反向地，把尾空间本身作为状态空间，令左移成为动力学，当前坐标成为输出，就得到一个重现全部 $m_n$ 的有限实现。因此最小状态维数不是凭经验选出的记忆长度，而是

$$
\boxed{
 d_{\mathrm{pred}}(m)
=\operatorname{finrank}_K\mathcal T(m).
}
$$

这个等式的适用范围是线性响应实现。它不声称任意非线性控制器、任意量子通道或任意带后选择的条件概率都能被同一个线性载体代表。

### 73.2 低于尾空间维数的压缩必然留下未来见证

若 $\mathcal T(m)$ 有限维，取一个线性压缩

$$
Q:\mathcal T(m)\to W
$$

并假设

$$
\operatorname{finrank}W
<
\operatorname{finrank}\mathcal T(m),
$$

则仓库定理 `smaller_compression_has_future_witness` 给出某个非零尾方向 $x$，满足

$$
Qx=0,
$$

但存在有限时刻 $n$ 使

$$
\operatorname{out}(A^n x)\ne0.
$$

因此，压缩器当前看不到的方向，会在某个有限未来实验中重新出现。这个结论把“历史回流”改成了有限见证：不需要假定无限复杂的过去，只要压缩低于尾空间秩，就存在一个可定位的未来读出将其分开。

它也给出了与第 71 节不同的容量概念：

$$
\text{完美记录容量}
\quad\ne\quad
\text{线性预测维数}.
$$

前者要求一次 POVM 区分记录态；后者只要求对指定响应族重现未来输出。很多原始历史可以共享一个预测状态，只要它们在全部允许的未来尾上相同。

### 73.3 有限 Hankel 窗口与可执行校准

对行数 $r$、列数 $c$ 定义有限数据 Hankel 映射

$$
H_{r,c}(u_0,\ldots,u_{c-1})
=
\left(
\sum_{j=0}^{c-1}m_{i+j}(u_j)
\right)_{0\le i<r}.
$$

当 $r,c$ 都不小于 $\operatorname{finrank}\mathcal T(m)$ 时，已有定理 `dataHankel_rank_eq_tailSpace` 给出

$$
\operatorname{rank}H_{r,c}
=
\operatorname{finrank}\mathcal T(m).
$$

这把“需要观察多深”变成了可校准的有限窗口条件。若实际数据带误差，不能直接把观测矩阵的数值秩当成精确秩；应使用第 67 节的条件数和最小二乘噪声界，并声明截断阈值、误差模型与任务容限。

第 72 节的 diamond 距离控制的是完整仪器过程；Hankel 尾空间控制的是选定线性响应坐标。两者的连接需要一个明确的读出映射：先由过程产生记录分布或 effect 期望，再把它们送入 $Y$。没有这个映射，不能用一个状态空间秩替代过程级历史距离。

### 73.4 Zeckendorf 合法构型只给输入索引，不直接给预测维数

令

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
|\mathcal W_L|=F_{L+2}.
$$

可以把每个 $w\in\mathcal W_L$ 作为一个输入标签，构造一个输入空间 $U$。但从标签集合到线性空间还需要指定编码：例如选择基向量 $e_w$，再给出每个未来实验对 $e_w$ 的响应 $m_n(e_w)$。只有在这些响应方向线性独立、并且全部时间移位都落在这组方向所张成的同一个预测载体中时，才会得到

$$
\operatorname{finrank}\mathcal T(m)=F_{L+2}.
$$

合法标签本身并不给出无条件的 $\operatorname{finrank}\mathcal T(m)\le F_{L+2}$：时间移位可能产生额外的动力学方向，使尾空间维数大于瞬时输入标签数。只有在另有一个维数至多为 $F_{L+2}$ 的预测载体，并且所有移位尾都通过它因子化时，才能推出这个上界。反过来，在指定任务的全部未来响应中，不同 Zeckendorf 字串也可能落入同一个尾方向，使实际预测维数严格小于标签数；如果允许的响应还包含未编码的相位、参考关联或历史寄存器，预测空间则可能大于单个 Zeckendorf 数值的像。

所以，Fibonacci 数量、完美记忆维数和预测 Hankel 秩分别回答三个问题：

$$
\begin{aligned}
&F_{L+2}: &&\text{有多少个合法输入构型？}\\
&d_M: &&\text{一次读取能完美区分多少个记忆态？}\\
&d_{\mathrm{pred}}: &&\text{指定未来响应需要多少个线性预测方向？}
\end{aligned}
$$

把三者直接相等，必须额外给出编码双射、同一 POVM 的完美区分以及未来响应方向的独立性。否则 Zeckendorf 只是适配约束的坐标尺，不是自动生成的物理记忆大小。

本节复用的是仓库已冻结的 Hankel 尾空间与最小实现结果；将其解释为量子过程的预测维数仍需明确线性读出、状态域和仪器协议。具体量子模型若要得到新的 Lean 结论，应先固定有限维通道和 effect 坐标，再分别证明过程到 $m_n$ 的映射、尾空间有限性及其噪声稳定性。

## 74. 投影残差、有限视界误差与可接受的历史压缩

第 73 节给出了预测尾空间的最小维数，但实际记录通常还要压缩。压缩是否可接受，不能只看状态维数下降了多少；需要计算压缩动力学与完整动力学在指定视界内产生的输出差异。

取实赋范线性空间

$$
V,W,U,Y
$$

完整线性实现为

$$
 x_{n+1}=Ax_n+Bu_n,
 \qquad
 y_n=Cx_n.
$$

选择一个压缩映射和一个提升映射

$$
P:V\to W,
\qquad
J:W\to V,
$$

并用实际压缩动力学

$$
\widetilde A=PAJ,
\qquad
\widetilde B=PB,
\qquad
\widetilde C=CJ
$$

生成近似输出。这里不要求

$$
PJ=I_W.
$$

如果它不是回缩投影，下面的残差仍然有定义，但不能把这两个映射自动称为同一个子空间的正交投影。

定义动力学和输入残差：

$$
R_A=AJ-J\widetilde A,
\qquad
R_B=B-J\widetilde B.
$$

它们分别测量提升后的压缩一步与完整一步的差，以及输入没有被压缩提升完整保留的差。令完整状态和压缩状态从零初值出发，定义

$$
e_n=x_n-J\widetilde x_n.
$$

由实际递推直接得到

$$
 e_{n+1}
=
Ae_n+R_A\widetilde x_n+R_Bu_n.
$$

### 74.1 有限视界的残差和界

仓库的 `D5.S3.Observer.Hankel.ProjectedRealizationError` 已证明，在任意有限步

$$
n
$$

有

$$
\boxed{
\|e_n\|
\le
\sum_{k=0}^{n-1}
\|A\|^{n-1-k}
\left(
\|R_A\|\,\|\widetilde x_k\|
+
\|R_B\|\,\|u_k\|
\right).
}
$$

再由输出映射得到

$$
\boxed{
\|y_n-\widetilde y_n\|
\le
\|C\|
\sum_{k=0}^{n-1}
\|A\|^{n-1-k}
\left(
\|R_A\|\,\|\widetilde x_k\|
+
\|R_B\|\,\|u_k\|
\right).
}
$$

这条界说明“删除历史”造成的误差具有时间方向：较早的残差会被后续完整动力学反复传播，传播权重是

$$
\|A\|^{n-1-k}.
$$

因此，相同的静态压缩维数在不同的预测视界和动力学下可以有完全不同的可靠性。

如果输入满足

$$
\|u_k\|\le M,
$$

且压缩动力学和完整动力学分别满足

$$
\|\widetilde A\|<1,
\qquad
\|A\|<1,
$$

则已有的 uniform 结果给出一个与

$$
n
$$

无关的充分界：

$$
\boxed{
\|y_n-\widetilde y_n\|
\le
\|C\|
\frac{
\|R_A\|
\dfrac{\|\widetilde B\|M}{1-\|\widetilde A\|}
+
\|R_B\|M
}{1-\|A\|}.
}
$$

这个结论的稳定性假设是范数收缩，而不是仅仅谱半径小于一。若只有谱半径信息，还需要另一个范数转换或暂态增长界；不能直接把上式套用。

### 74.2 任务误差与历史压缩的停止条件

给定预测视界

$$
H
$$

、任务输出容限

$$
\varepsilon_{\mathrm{task}}
$$

和输入界

$$
M\ge0
$$

，可以把压缩接受条件写成

$$
\max_{0\le n\le H}
\|y_n-\widetilde y_n\|
\le
\varepsilon_{\mathrm{task}}.
$$

有限视界时，直接使用 74.1 的残差和界即可；若需要所有未来时刻的统一保证，则需使用 74.1 的收缩条件或独立的尾项可和性证明。这个停止条件保留的是任务所需的响应精度，而不是任意恢复完整原始历史。

第 73 节的低维压缩见证与这里的残差界互补：

$$
\begin{aligned}
&\text{若压缩载体维数小于 }d_{\mathrm{pred}}(m)\text{，且对同一完整响应族的全部允许输入与时刻残差为零}
&&\Longrightarrow\text{违反第 73 节的最小实现性；}\\
&\text{压缩载体维数下降但残差有界}
&&\Longrightarrow\text{只在给定 }H,M,\varepsilon_{\mathrm{task}}\text{ 内可接受；}\\
&\text{残差上界无界或任务容限趋于零}
&&\Longrightarrow\text{该上界本身不能证成预测等价。}
\end{aligned}
$$

这里的第一行要求零残差覆盖整个指定响应族；若只对一个输入序列或一个时刻为零，最多得到该任务实例的精确复现，不能推出尾空间维数矛盾。

因此，“稳定经典对象”可以采用一个带误差的预测接口：接口不保留所有历史方向，但对指定输入界和视界给出可核验的输出误差。

### 74.3 量子读出与 Zeckendorf 编码的适用边界

若量子过程先经过一个明确的线性读出映射

$$
L:\rho\longmapsto x(\rho)\in V,
$$

再用

$$
C
$$

读取目标响应，那么 74.1 可以用于这组坐标。要把坐标误差转成量子态的迹距离或概率误差，还必须给出

$$
L,
$$

和

$$
C
$$

与所选距离之间的范数转换；第 67 节的帧下界和第 72 节的 diamond 距离分别承担不同层面的稳定性，不能互相替代。

对 Zeckendorf 合法构型

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

若合法字串的基向量

$$
e_w\in U
$$

作为输入坐标送入动力学，则压缩输入是

$$
\widetilde B e_w=PB e_w,
$$

而不是在没有给定类型识别时直接写成 $$P e_w$$。只有另有注入

$$
I:U\to V
$$

时，才可以把状态空间中的压缩写成 $$P I(e_w)$$。若两个合法字串在压缩后相同，并且在同一后续输入协议、同一初态约定下的未来响应差异超过

$$
2\varepsilon_{\mathrm{task}},
$$

则不存在一个同时使两者误差不超过 $$\varepsilon_{\mathrm{task}}$$ 的共同近似接口；仅超过 $$\varepsilon_{\mathrm{task}}$$ 还不足以推出这一点。若它们的全部指定响应差异被残差界覆盖，则可以在该有限任务中共享一个预测接口。

这里不把

$$
|\mathcal W_L|=F_{L+2}
$$

直接当作压缩后的维数。Fibonacci 计数只给合法输入构型数；实际可接受的预测维数由

$$
P, A, B, C
$$

、输入界、视界和误差容限共同决定。若压缩还要保留纯态相位或可访问参考关联，则这些方向必须进入

$$
V
$$

，否则实线性残差界没有覆盖它们。

本节直接复用 `ProjectedRealizationError` 的有限残差和、输出误差和收缩统一界；这些声明针对实赋范线性系统。将它们提升为量子通道的 trace/diamond 界，需要另外证明读出嵌入、完全正性、参考系统和距离转换，不能由线性公式自动推出。

## 75. 精确下降的选择性：投影态先精确，读出还需因子化

第 74 节的残差界允许完整状态和压缩状态之间存在误差，并用有限视界控制这种误差。仓库还给出了一个更强、但适用范围更窄的结果：如果动力学先在选定投影下精确下降，且目标读出只依赖这个投影，那么目标输出可以逐步完全相同，即使提升回完整空间的状态仍有残差。

令完整系统、压缩系统和读出分别由

$$
A:V\to V,
\qquad
B:U\to V,
\qquad
C:V\to Y,
$$

以及

$$
P:V\to W,
\qquad
J:W\to V
$$

给出，并定义

$$
\widetilde A=PAJ,
\qquad
\widetilde B=PB,
\qquad
\widetilde C=CJ.
$$

对零初态和任意输入序列，完整状态与压缩状态满足

$$
 x_{n+1}=Ax_n+Bu_n,
 \qquad
 \widetilde x_{n+1}=\widetilde A\widetilde x_n+\widetilde B u_n.
$$

`D5.S3.Observer.Hankel.ProjectedExactDescent` 的第一条条件是

$$
PA=(PAJ)P.
$$

它表示下一步的投影状态只依赖当前投影状态。对任意输入序列和每个有限时刻，源码证明

$$
\boxed{
Px_n=\widetilde x_n.
}
$$

这是一条精确的投影态结论。它不需要输入有界，也不需要

$$
\|A\|<1
\qquad\text{或}\qquad
\|\widetilde A\|<1.
$$

不过它还没有说明任意读出都相同。要让目标读出也完全下降，还必须增加因子化条件

$$
C=(CJ)P.
$$

在这个附加条件下，源码的 `outputs_eq_of_descent` 给出

$$
\boxed{
Cx_n=\widetilde C\widetilde x_n
}
$$

对同一输入序列和每个时刻都成立。这里是充分条件；该声明没有把因子化判据说成必要条件。

### 75.1 可见输出精确，不等于完整状态精确

第 74 节的两个残差在这里写成

$$
R_A=AJ-JPAJ,
\qquad
R_B=B-JPB.
$$

它们可以非零。因子化条件直接推出

$$
CR_A=0,
\qquad
CR_B=0.
$$

因此，提升后的完整状态可以沿着压缩状态没有表示的方向变化，但这些变化被当前选定的读出湮灭。这里应说“对该输出不可见”，不能在没有附加投影假设时把它称为正交投影遗漏。

源码没有要求

$$
PJ=I_W.
$$

如果另行加入这个回缩条件，则可以进一步得到

$$
PR_A=0,
\qquad
PR_B=0,
$$

从而把残差放入投影核；但这仍然不等于残差在某个给定内积下正交。没有回缩条件时，连这个投影核解释也不能直接使用。

一个两坐标例子把区别写得很清楚。取

$$
V=\mathbb R^2,
\qquad
W=U=Y=\mathbb R,
$$

并令

$$
P(x,h)=x,
\qquad
J(w)=(w,0),
\qquad
C(x,h)=x,
$$

$$
A=
\begin{pmatrix}
 a&0\\
 c&d
\end{pmatrix},
\qquad
B u=
\begin{pmatrix}
 b_1u\\
 b_2u
\end{pmatrix}.
$$

此时

$$
PA=(PAJ)P,
\qquad
C=(CJ)P.
$$

所以第一坐标的压缩递推和完整递推完全一致。但只要

$$
 c\ne0
 \qquad\text{或}\qquad
 b_2\ne0,
$$

就有

$$
R_A(w)=(0,cw),
\qquad
R_B(u)=(0,b_2u),
$$

它们不是零。可见输出仍然精确，而隐藏坐标可以持续接收来自可见坐标或外部输入的变化。

这也说明“没有隐藏到可见回流”与“没有可见到隐藏泄漏”是两个方向。仓库的 `VisibleAutonomyCriterion` 对幂等投影把可见下降等价于

$$
P T(1-P)=0
$$

等条件，同时保留一个反例：可见到隐藏的反向块仍可非零。稳定对象所需的是前一个方向不回流到任务读出，而不是完整联合状态永远停留在提升像中。

### 75.2 与有限视界残差界的关系

第 74 节回答的是：当压缩不精确时，完整状态和目标输出的误差上界怎样随视界增长。第 75 节回答的是一个更窄的情形：当选定投影满足全局下降、且读出因子化时，目标输出误差直接为零。

因此，两节的逻辑关系是

$$
\begin{aligned}
&\text{全局下降}+\text{读出因子化}
&&\Longrightarrow
\text{指定输出的逐步精确闭合};\\
&\text{残差有界但不满足因子化}
&&\Longrightarrow
\text{使用第 74 节的有限视界误差界};\\
&\text{没有输出因子化}
&&\Longrightarrow
\text{投影态精确不保证目标读出精确}.
\end{aligned}
$$

精确输出不等于完整状态可恢复，也不等于参考系统或环境中的关联已经消失。若后续任务改变读出，或允许访问此前未读的记录，原先的因子化条件可能不再适用。对非零初态，源码中的零初态归纳还需要把压缩初态明确设为

$$
\widetilde x_0=Px_0
$$

并重新检查零时刻的输出因子化；不能把源码的零初态结论无条件推广到任意初态。

### 75.3 对量子记录与 Zeckendorf 的边界

若量子过程先被送入一个明确的线性坐标空间，再选定一个任务读出，上述精确下降可以作为该坐标任务的模型。但它仍然是实线性算子结论，不自动给出量子态的迹距离、参考系统上的完全有界距离或 diamond 距离界；这些量需要另行指定算子空间、通道结构和范数转换。

同样，若把 Zeckendorf 合法字串映为输入坐标，两个字串被同一个 $$P$$ 或相应的 $$PB$$ 输入映射合并，只能说明它们在当前投影坐标中相同。只有当目标任务的读出满足因子化，并且后续动力学满足下降条件时，这种合并才是该任务中的精确压缩。Fibonacci 数

$$
F_{L+2}
$$

仍然只是合法标签数，不是自动的完整记忆维数，也不证明任何物理 Hamiltonian 保持该合法子空间。

所以，对“多少约束足以形成稳定经典现实”的更细回答是：首先要求当前记录对指定动力学形成可见下降；然后要求真正关心的读出因子化；只有在这两条失败时，才需要用第 74 节的残差、视界和误差容限计算还要保留多少历史。

本节复用 `ProjectedExactDescent` 与 `VisibleAutonomyCriterion` 的精确下降结果，并把它们与第 74 节的残差界连接起来。它没有把可见任务的精确闭合提升为全态恢复、量子通道等价或唯一的经典现实。

## 76. 有限未来关系塔的终止、类预算与 Zeckendorf 标签边界

第 75 节说明了一个选定读出何时可以由压缩状态精确产生。下一步要问的是：需要观察多少个未来时刻，才足以确定这个任务的全部未来响应？对有限状态载体，仓库已有一个不依赖收缩率的答案。

设 $$X$$ 是有限状态载体，

$$
\tau:X\to X,
\qquad
q:X\to O
$$

分别是更新和当前读出。对每个有限深度 $$m$$，定义

$$
x\sim_m x'
\quad\Longleftrightarrow\quad
\forall k\le m,
\ q\bigl(\tau^{[k]}x\bigr)=q\bigl(\tau^{[k]}x'\bigr),
$$

并定义完全未来关系

$$
 x\sim_\infty x'
 \quad\Longleftrightarrow\quad
 \forall k,
 \ q\bigl(\tau^{[k]}x\bigr)=q\bigl(\tau^{[k]}x'\bigr).
$$

这里的 $$\tau^{[k]}$$ 表示迭代 $$k$$ 次。源码中的 `finiteFutureRelation` 和 `infiniteFutureRelation` 正是这两种关系。记

$$
R_m=\sim_m,
\qquad
R_\infty=\sim_\infty,
$$

并记相应商类数为

$$
C_m=\lvert X/R_m\rvert,
\qquad
C_\infty=\lvert X/R_\infty\rvert.
$$

### 76.1 相邻稳定已经足够确定全部未来

`FiniteEquivalenceDescent` 给出有限未来关系的递归

$$
R_0=\ker q,
$$

$$
R_{m+1}
=
\left\{(x,x')\in R_0:
(\tau x,\tau x')\in R_m\right\},
$$

以及有限交表示

$$
R_m
=
\bigcap_{0\le k\le m}
\left\{(x,x'):
q\bigl(\tau^{[k]}x\bigr)=q\bigl(\tau^{[k]}x'\bigr)
\right\}.
$$

因此关系塔只能变细，商类数只能增加：

$$
C_m\le C_{m+1}.
$$

`FiniteStabilityClassBound` 定义最小相邻稳定深度

$$
 d=\min\left\{m:R_m=R_{m+1}\right\}.
$$

它证明

$$
\boxed{
R_d=R_{d+1}=R_\infty.
}
$$

并且对任意满足

$$
R_n=R_{n+1}
$$

的 $$n$$，都有

$$
 d\le n.
$$

所以在有限载体上，“再看一个时刻没有产生新区分”已经足以推出全部未来读出相同。这个结论不需要范数收缩、谱隙、输入振幅界或量子通道结构；它是有限关系塔的组合稳定性。它也不是说任意系统都有一个与任务无关的稳定深度：$$d$$ 依赖更新 $$\tau$$ 和读出 $$q$$。

### 76.2 稳定深度消耗的是商类预算

初始类数不是状态数本身，而是当前读出能够区分的商类数：

$$
C_0
=
\left\lvert X/\ker q\right\rvert
=
\left\lvert\operatorname{range}q\right\rvert.
$$

完全未来类数为 $$C_\infty$$。在源码的自然数减法语境下，`finite_stability_class_bound` 给出两段类预算

$$
\boxed{
 d\le C_\infty-C_0,
}
$$

以及

$$
\boxed{
 C_\infty-C_0
 \le
 \lvert X\rvert-C_0.
}
$$

这表示每次关系塔严格细化，都必须消耗至少一个新的商类；它不是说每一步一定恰好增加一个类，也不是最小线性预测维数定理。若 $$q$$ 满射到有限字母表 $$O$$，则

$$
C_0=\lvert O\rvert,
$$

从而得到

$$
 d\le C_\infty-\lvert O\rvert
 \le
 \lvert X\rvert-\lvert O\rvert.
$$

更一般地，若初始关系不是当前读出的核，而是任意有限载体上的 Setoid $$R$$，`finite_equivalence_descent_and_stability_bound` 给出相应的形式

$$
 d\le C_\infty-\lvert Y/R\rvert
 \le
 \lvert Y\rvert-\lvert Y/R\rvert.
$$

所以“需要保留多少历史”在这个有限确定性模型中首先表现为一个商类预算：不是保存每条历史词，而是继续细分那些仍会在未来读出中分开的类。

### 76.3 Zeckendorf 标签只提供载体大小

取长度为 $$L$$、禁止相邻两个 $$1$$ 的合法字串集合

$$
\mathcal W_L
=
\left\{w\in\{0,1\}^L:
 w_jw_{j+1}=0\right\}.
$$

其合法构型数为

$$
\lvert\mathcal W_L\rvert=F_{L+2}.
$$

只有在更新和读出真的定义在同一个有限载体

$$
\tau:\mathcal W_L\to\mathcal W_L,
\qquad
q:\mathcal W_L\to O
$$

上时，才可以把上一节的类预算代入为

$$
 d\le C_\infty-C_0
 \le
 F_{L+2}-C_0.
$$

若 $$q$$ 满射到 $$O$$，则右侧可写成

$$
 d\le C_\infty-\lvert O\rvert
 \le
 F_{L+2}-\lvert O\rvert.
$$

这只是把有限载体大小代入稳定深度上界。它不把 Fibonacci 数自动变成预测维数。反例很直接：若 $$q$$ 在 $$\mathcal W_L$$ 上单射，则

$$
C_0=F_{L+2},
\qquad
 d=0,
$$

但载体仍有 $$F_{L+2}$$ 个状态。相反，若所有未来读出都相同，则

$$
C_\infty=C_0=1,
\qquad
 d=0,
$$

即使合法标签很多，也不需要更深的未来窗口来区分任务响应。

因此应分开报告三种量：

$$
\boxed{
\text{合法标签载体大小 }F_{L+2},
\qquad
\text{完全未来商类数 }C_\infty,
\qquad
\text{稳定深度 }d.
}
$$

Hankel 预测维数还取决于未来响应的线性秩，量子模型则可能需要算符空间、相位方向、可访问记录和参考系统。它们都不能仅由 $$F_{L+2}$$ 的离散计数推出。即使有限未来商已经稳定，也只说明指定经典更新和读出上的确定性响应已经闭合；它不自动证明密度算符相等、迹距离为零、diamond 距离为零或某个物理 Hamiltonian 保持合法 Zeckendorf 子空间。

第 76 节把“稳定经典接口”进一步拆成了三个可测层次：载体允许哪些合法构型，完全未来还能区分多少类，以及需要看到多深才达到全部未来等价。只有在额外证明编码、更新、读出和预测实现之间的同构时，才可以把其中两个量合并；一般情况下，Fibonacci 标签数只是适用载体的大小，而不是世界必须保留的历史长度。

本节复用 `FiniteEquivalenceDescent`、`FiniteStabilityClassBound` 和 `StableDepthCardinalityBounds` 的既有声明；它们适用于有限确定性更新与读出关系。将这套关系塔解释为量子通道的过程记忆，需要另行给出量子状态空间、仪器协议和距离转换。

## 77. 量子任务的可见商、序列核与不可见物理状态

第 62 节已经给出顺序词效果的正交残差，第 59 节已经给出目标可见性的充分性与失败见证。第 75 节则把状态坐标上的投影下降接到输出因子化，第 76 节把有限确定性载体上的未来关系塔接到稳定深度。本节只做它们之间的接口：说明量子任务中的“同一个对象”应当由允许词的统计签名定义，并列出把这个签名接成动力学商时必须补上的条件。

### 77.1 允许词的量子签名

固定有限矩阵维数 $$d$$、字母表 $$\mathsf A$$、允许词族

$$
\mathcal A\subseteq \operatorname{List}(\mathsf A),
$$

以及每个字母对应的 Heisenberg 线性作用

$$
\mathsf I_a:
\operatorname{Herm}_d
\longrightarrow
\operatorname{Herm}_d.
$$

令 $$E_w$$ 表示仓库 `sequentialWordEffect` 对词 $$w$$ 产生的 Hermitian effect。定义允许词的可见空间、不可见残差和统计签名：

$$
V_{\mathcal A}
=
\operatorname{span}_{\mathbb R}
\{E_w:w\in\mathcal A\},
$$

$$
K_{\mathcal A}=V_{\mathcal A}^{\perp},
$$

$$
\Sigma_{\mathcal A}(s)
=
\bigl(
\langle s,E_w\rangle_{\mathbb R}
\bigr)_{w\in\mathcal A}.
$$

这里的内积是 Hermitian 空间上的实内积；它只记录所选词效果的实线性响应。它不是完整密度矩阵，也不是自动包含参考系统或环境的联合状态。

`unified_sequential_kernel` 给出精确等价：

$$
\boxed{
\Sigma_{\mathcal A}(s)
=
\Sigma_{\mathcal A}(s')
\quad\Longleftrightarrow\quad
s-s'\in K_{\mathcal A}.
}
$$

因此，量子任务中的当前对象应先定义为签名的纤维，而不是把所有物理态直接认作同一个点。若增加允许词族

$$
\mathcal A_H\subseteq\mathcal A_{H+1},
$$

则

$$
V_{\mathcal A_H}
\subseteq
V_{\mathcal A_{H+1}},
\qquad
K_{\mathcal A_{H+1}}
\subseteq
K_{\mathcal A_H}.
$$

这是第 76 节未来关系塔

$$
R_{H+1}\subseteq R_H
$$

的线性量子对应：观察视界扩大时，允许区分的方向增加，不可见残差减少。这里得到的是子空间包含关系，不能直接改写成有限商类数；全体密度态是连续集合，不能套用有限载体的基数界。

### 77.2 目标预测的充分性与不可见见证

对一族实际效应 $$E_i$$，定义含单位方向的可见空间

$$
V
=
\operatorname{span}_{\mathbb R}
\bigl(\{I\}\cup\{E_i\}_i\bigr).
$$

单位方向必须显式加入，因为密度态的迹已经固定；没有它，效应签名不能自动控制标量部分。

这里的 $$E_i$$ 必须先满足源码中的物理效应条件：它们是 Hermitian、正半定，且 $$I-E_i$$ 也正半定。`target_prediction_sufficiency` 的第一半可表述为：若目标算子子空间 $$T$$ 满足

$$
T\subseteq V,
$$

那么两个密度态对全部 $$E_i$$ 的 trace 读数相同，就对每个 $$A\in T$$ 给出相同的目标期望。对 Hermitian 矩阵，仓库中的实内积与 trace 公式通过实部对应；该对应需要在具体有限维载体中明确，不能把两种配对无条件混写。

第二半给出相反方向的物理见证。若

$$
A\notin V,
$$

则存在非零 Hermitian 方向 $$D\in V^{\perp}$$、某个 $$\varepsilon>0$$ 以及两个合法密度态

$$
\rho_{\pm}
=
\frac{I}{d}\pm\varepsilon D
$$

使得对每个已选效应 $$E_i$$，

$$
\operatorname{tr}(\rho_+E_i)
=
\operatorname{tr}(\rho_-E_i),
$$

但目标读数满足

$$
\operatorname{tr}(\rho_+A)
-
\operatorname{tr}(\rho_-A)
=
2\varepsilon\operatorname{tr}(DA)
\ne0.
$$

这说明当前签名对该目标并不充分。它是一个存在性见证：源码只保证某个正 $$\varepsilon$$ 存在，不给出统一的数值下界；结论也不是迹距离或 diamond 距离下界。

若目标是第 $$n$$ 步的效应 $$B$$，应先把 Heisenberg 回拉

$$
A=(\Phi^*)^n(B)
$$

放入目标空间，再检查 $$A\in V$$。当前读出空间只含 $$B$$ 而不含其回拉，并不能推出当前签名足以预测未来的 $$B$$ 读数。

### 77.3 从可见空间到动力学下降的附加条件

不能把 effect 空间 $$V$$ 与状态空间上的投影自动视为同一个算子。前者在 Heisenberg 的 Hermitian 算子空间，后者在 Schrödinger 状态坐标；需要有限维 Hilbert--Schmidt 对偶识别、明确的 adjoint，以及一个真正幂等的状态投影 $$P_H$$。

在这些额外结构已经给定后，若 Schrödinger 作用为 $$T_a$$，并且其 Hilbert--Schmidt 对偶满足

$$
T_a^*=\mathsf I_a,
$$

再假设允许所有长度不超过 $$H$$ 的词，并且该词空间已经稳定：

$$
V_H=V_{H+1},
$$

则对任意 $$k\in V_H^{\perp}$$ 和 $$v\in V_H$$，

$$
\langle T_a k,v\rangle
=
\langle k,T_a^*v\rangle
=0.
$$

所以

$$
T_a(V_H^{\perp})
\subseteq
V_H^{\perp},
$$

等价地，若 $$P_H$$ 是 $$V_H$$ 的正交投影，则

$$
P_HT_a(I-P_H)=0.
$$

这是 `VisibleAutonomyCriterion` 所需的 hidden-to-visible 不泄漏条件。由它可得到可见递推的因子化；再加上第 75 节 `ProjectedExactDescent` 的投影动力学条件，才可对任意输入历时推出

$$
P_Hx_n=\widetilde x_n
$$

以及在输出因子化条件下的

$$
Cx_n=\widetilde C\widetilde x_n.
$$

这里必须保留三条限制：没有 $$P_H^2=P_H$$，不能称为投影下降；没有 state/effect 对偶与 adjoint，不能从 effect span 推出状态不变性；没有量子正性、迹保持和通道假设，这些等式仍只是线性系统结论。

若 $$V_H=V_{H+1}$$ 只是在任意集合中偶然相等，而允许词族没有前缀闭合性，则不能推出更长词仍在 $$V_H$$。永久稳定需要词族对前缀扩展闭合，或另行证明全部后续 Heisenberg 效果仍落在该空间。

### 77.4 何时能接回第 76 节的有限商预算

若选定一个有限物理状态样本

$$
X\subseteq\operatorname{DensityState},
$$

有确定更新 $$\tau:X\to X$$，并且第 $$k$$ 步的输出正好等于指定签名坐标，那么可定义

$$
x\sim_Hx'
\quad\Longleftrightarrow\quad
\Sigma_H(x)=\Sigma_H(x').
$$

这时才能把 $$x\sim_Hx'$$ 与第 76 节的 $$R_H$$ 对齐，并使用有限商类数和稳定深度界。对于包含多条分支或多字母选择的词族，不能直接把它写成单一的 $$q(\tau^{[k]}x)$$；必须固定字母调度，或把分支与历史并入扩大的确定状态。若状态空间是全部密度态，集合通常是连续的，应该报告

$$
\dim V_H,
\qquad
\dim K_H,
$$

或 centered trace-zero 塔，而不是报告 $$|X/R_H|$$ 的有限数值。

同样，Zeckendorf 合法字串的数量

$$
|\mathcal W_L|=F_{L+2}
$$

只在明确指定

$$
w\longmapsto s_w,
\qquad
\tau:\mathcal W_L\to\mathcal W_L,
\qquad
q:\mathcal W_L\to O
$$

以及实际的序列仪器后，才是一个合法的有限载体大小。它不能自动等于

$$
\dim V_H,
\qquad
d^2-1,
$$

也不能自动等于量子记忆维数、Hankel 秩或 Hamiltonian 不变子空间的维数。Zeckendorf 负责组织合法标签；effect、仪器和更新负责决定哪些标签差异进入可见响应。

### 77.5 本节对“稳定经典现实”的精确含义

在这条接口上，“稳定的经典现实”可以写成三个同时满足的任务条件：

$$
\boxed{
\text{签名商定义当前可区分对象}
\;+
\text{可见空间对目标足够}
\;+
\text{隐藏方向在指定动力学下不回流}
}
$$

第一项由 $$\Sigma_H$$ 和 $$K_H$$ 给出；第二项由目标是否落在含单位方向的 effect span 决定；第三项需要真正的投影、对偶和下降条件。三项中任何一项缺失，当前读数都不能单独承担“以后仍然如此”的含义。

因此，“要保留多少历史”没有一个脱离任务的整数答案。对有限 Zeckendorf 载体，先报告合法构型数量；对给定词族，再报告可见 span 与正交残差；对给定更新，最后检验目标回拉是否留在该 span，以及隐藏到可见的耦合是否为零。只有这些对象、操作和误差范围都被指定后，才可以说某一层记录已经足以支撑稳定的经典预测。

本节复用 `unified_sequential_kernel`、`target_prediction_sufficiency`、`finite_time_observer_monotonicity` 和 `incomplete_observer_physical_counterexample` 的现有冻结声明，并把它们接到第 75、76 节的下降与有限关系塔。上述声明均在标准项目公理闭包下通过定向构建；本节没有新增 Lean 定理，也没有把线性 effect 结果提升为 CPTP、trace-distance 或 diamond 等价。

## 追加锚（新终端）

## 78. 精确预测闭合与后揭测量的共同经典存储障碍

### 78.1 序列统计、目标充分性与下降的适用条件

**定义 78.1（按设置归一化的序列任务）。** 设 $d\ge1$，$\operatorname{Herm}_d$ 为 $d$ 阶 Hermitian 矩阵的实向量空间，内积为 $\langle A,B\rangle=\operatorname{tr}(AB)$。物理输入取密度矩阵 $\rho\ge0$、$\operatorname{tr}\rho=1$。对每个可选设置 $b$，分别给定有限个复线性、完全正且迹不增的分支 $\mathcal J_{b,s}$，并要求

$$
\sum_s\mathcal J_{b,s}\quad\text{对每个固定的 }b\text{ 都迹保持。}
$$

令 $\mathcal J_{b,s}^*$ 为 Hilbert--Schmidt 伴随。按时间顺序记录词 $w=((b_1,s_1),\ldots,(b_n,s_n))$，定义

$$
E_\varnothing=I_d,\qquad
E_w=\mathcal J_{b_1,s_1}^*\cdots\mathcal J_{b_n,s_n}^*(I_d),
\qquad
p_\rho(w)=\operatorname{tr}(\rho E_w).
$$

设置是外部选择；若设置也随机化，其概率由另行指定的归一化策略给出，不把不同设置的全部分支直接合成一个仪器。

**命题 78.2（第 77 节线性接口的物理限定）。** 第 77.1 节的签名核等价只需实 Hermitian 线性作用；把其中的响应解释为物理序列概率，须另加定义 78.1 的输入和仪器假设。第 77.2 节的目标充分性适用于 $d\ge1$ 及含单位方向的空间

$$
V=\operatorname{span}_{\mathbb R}\bigl(\{I_d\}\cup\{E_i\}_i\bigr),
\qquad 0\le E_i\le I_d.
$$

其中加入 $I_d$ 是利用已知的迹一约束，不要求额外测量单位算子；对任何标量目标 $aI_d$，期望已经恒等于 $a$。若 $A\notin V$，则有对所有 $E_i$ 同读数、对 $A$ 异读数的两个密度矩阵。

证明。Hermitian 矩阵满足

$$
\overline{\operatorname{tr}(AB)}
=\operatorname{tr}((AB)^\dagger)
=\operatorname{tr}(BA)=\operatorname{tr}(AB),
$$

故所写内积为实数。对任何实线性词效果族，所有配对相等当且仅当状态差正交于这些效果的实张成空间；这就是第 77.1 节 `unified_sequential_kernel` 的线性内容，它不包含密度输入、完全正性或归一化假设。在定义 78.1 下，分支复合把正输入送到正矩阵，其迹给出非负分支概率；对每个已经选定的设置，将该步的结果求和保持输入迹。逐步求和即得每个有限策略树的概率归一化。一般实线性作用没有这些保证，例如作用 $A\mapsto2A$ 从单位效果产生 $2I_d$，对迹一输入的响应为二。

若 $A=aI_d+\sum_i a_iE_i$，其中只有有限个 $a_i$ 非零，则

$$
\operatorname{tr}(\rho A)=a+\sum_i a_i\operatorname{tr}(\rho E_i),
$$

直接给出充分性。反向令 $D=A-\operatorname{proj}_V A$。于是 $D\ne0$、$D\perp V$、$\operatorname{tr}D=0$，且

$$
\operatorname{tr}(DA)=\operatorname{tr}(D^2)>0.
$$

取 $0<\varepsilon<1/(d\|D\|_{\rm op})$，则 $\rho_\pm=I_d/d\pm\varepsilon D$ 的最小特征值至少为 $1/d-\varepsilon\|D\|_{\rm op}>0$，迹为一。正交性给出相同的 $E_i$ 读数，而两态的 $A$ 读数相差 $2\varepsilon\operatorname{tr}(D^2)>0$。这也是第 77.2 节 `target_prediction_sufficiency` 中正维数假设和单位方向的作用；原节关于标量部分的说明应以迹一约束所给的上述公式为准。证毕。

**命题 78.3（全自由词稳定性与确定下降的限定）。** 对任意实线性生成作用 $(L_a)_a$，令 $E_\varnothing=I_d$、$E_{aw}=L_aE_w$，并用全部长度不超过 $H$ 的词定义 $V_H=\operatorname{span}_{\mathbb R}\{E_w:|w|\le H\}$。若 $V_H=V_{H+1}$，则每个生成作用都保持 $V_H$，且 $V_m=V_H$ 对所有 $m\ge H$ 成立。任意前缀闭合的允许子集，或把词族固定截断后得到的相邻相等，不具有这一推论。

第 77.3 节引用的受驱下降等式具有如下精确形式。给定线性映射 $A,B,P,J,C$，令

$$
\widetilde A=PAJ,\quad\widetilde B=PB,\quad\widetilde C=CJ,
\qquad PA=\widetilde A P,
$$

$$
x_0=0,\quad x_{n+1}=Ax_n+Bu_n,
\qquad
\widetilde x_0=0,\quad\widetilde x_{n+1}=\widetilde A\widetilde x_n+\widetilde B u_n.
$$

则 $Px_n=\widetilde x_n$；若另有 $C=\widetilde C P$，则 $Cx_n=\widetilde C\widetilde x_n$。这些是零初态的受驱响应等式；任意密度制备并非它们的初态假设。

证明。对 $|w|\le H$，有 $L_aE_w=E_{aw}\in V_{H+1}=V_H$。线性性把这个包含推广到整个 $V_H$，再对词长归纳，所有词效果都在 $V_H$ 中。与 $V_H\subseteq V_m$ 合用即得永久稳定。这是第 77.3 节所涉及的 `sequential_visible_space_once_stable_permanently` 的生成元不变性论证；不需要在全自由词假设之外再加一条前缀条件。若 $T_a^*=L_a$，同一论证还给出

$$
\langle T_ak,v\rangle=\langle k,L_av\rangle=0
\quad(k\in V_H^\perp,\ v\in V_H),
$$

故 $T_a(V_H^\perp)\subseteq V_H^\perp$。对于删去某些扩展的允许子集，上述 $aw$ 未必被允许，不能作这一步推导；命题 78.5 给出一个物理分支反例。

受驱响应在 $n=0$ 时满足 $Px_0=0=\widetilde x_0$。若第 $n$ 步等式成立，则

$$
Px_{n+1}=PAx_n+PBu_n
=\widetilde A\widetilde x_n+\widetilde B u_n
=\widetilde x_{n+1}.
$$

输出等式由 $C=\widetilde C P$ 代入。这正是 `ProjectedExactDescent` 中 `projectedState_eq_of_descent` 与 `outputs_eq_of_descent` 所用的零初态 `drivenState` 和全局下降条件。对另行指定的非零初态，相同归纳还需要 $\widetilde x_0=Px_0$；它不是任意两个初态之间的结论。证毕。

第 77.4 节接用第 76 节的有限商预算时，增广后的载体必须实际为有限集，更新必须是该集上的同一个时间齐次确定映射。把任意长历史、无界时钟或随机结果添作坐标，本身不满足这一假设：前两者可以产生无限多坐标值，后者仍需给定确定的更新规则。只有明确构造出有限且封闭的确定增广系统，才可使用第 76 节的有限类数和稳定深度界。第 77.5 节的三项条件在这些限定内给出所选任务的精确预测接口；它们不能作为“稳定经典现实”或一个可物理取得的共同经典记录的充分条件。以下同一模型同时满足预测闭合与共同经典存储不可能性。

### 78.2 两个 Lüders 设置的精确可见闭合

**定义 78.4（量子比特任务及未归一化坐标）。** 在计算基 $|0\rangle=(1,0)^T$、$|1\rangle=(0,1)^T$ 中取

$$
I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

对 $b\in\{X,Z\}$、$s\in\{+1,-1\}$，定义

$$
P_s^b=\frac{I+sb}{2},\qquad
\mathcal J_{b,s}(A)=P_s^bAP_s^b.
$$

任意 Hermitian $A$ 唯一写为

$$
A=\frac{tI+xX+yY+zZ}{2},
\qquad (t,x,y,z)\in\mathbb R^4,
\qquad t=\operatorname{tr}A.
$$

允许的操作只有这些分支；有限策略可以依赖已记录的设置和结果选择下一设置或停止，并可使用与输入独立的经典随机数。策略不插入任意旋转、不补充新的量子输入，也不测量外部参考系统。

**命题 78.5（分支递推与所有有限词的闭合）。** 每个固定 $b$ 的二分支族是 Lüders 仪器。分支在可见坐标 $(t,x,z)$ 上的作用恰为

$$
\mathcal J_{X,s}:\ (t,x,z)\longmapsto
\left(\frac{t+sx}{2},\frac{st+x}{2},0\right),
$$

$$
\mathcal J_{Z,s}:\ (t,x,z)\longmapsto
\left(\frac{t+sz}{2},0,\frac{st+z}{2}\right).
$$

密度输入恰满足 $t=1$、$x^2+y^2+z^2\le1$。对全部长度不超过 $H$ 的词效果，其实可见空间与稳定正交残差为

$$
V_0=\operatorname{span}_{\mathbb R}\{I\},\qquad
V_H=V=\operatorname{span}_{\mathbb R}\{I,X,Z\}\quad(H\ge1),
\qquad K=V^\perp=\operatorname{span}_{\mathbb R}\{Y\}.
$$

这些递推精确决定定义 78.4 内全部有限策略的记录概率。

证明。矩阵相乘给出 $X^2=Y^2=Z^2=I$，不同 Pauli 矩阵反对易，且 $I,X,Y,Z$ 两两 Hilbert--Schmidt 正交、平方范数均为二。这证明坐标表示的唯一性。无迹部分满足

$$
(xX+yY+zZ)^2=(x^2+y^2+z^2)I,
$$

故 $A$ 的特征值为 $(t\pm\sqrt{x^2+y^2+z^2})/2$，得到所述密度条件。

每个 $P_s^b$ 都是迹一的正交投影，且 $P_+^b+P_-^b=I$。若 $P=|v\rangle\langle v|$、$\|v\|=1$，则对任意矩阵 $A$，

$$
PAP=\langle v,Av\rangle P=\operatorname{tr}(AP)P.
$$

因此

$$
\mathcal J_{X,s}(A)=\frac{t+sx}{2}P_s^X,
\qquad
\mathcal J_{Z,s}(A)=\frac{t+sz}{2}P_s^Z,
$$

展开投影即得坐标递推，并且分支后的 $y$ 坐标为零。对任意辅助空间和任意正矩阵 $B$，

$$
(\mathcal J_{b,s}\otimes\mathrm{id})(B)
=(P_s^b\otimes I)B(P_s^b\otimes I)\ge0,
$$

所以分支完全正。对 $A\ge0$，其迹为 $\operatorname{tr}(AP_s^b)\in[0,\operatorname{tr}A]$；固定 $b$ 后对 $s$ 求和等于 $\operatorname{tr}A$。这证明每个设置的仪器性质。反之，将两个设置的四个分支不加权相加，输出迹为 $2\operatorname{tr}A$，并非归一化仪器。

这些分支关于 Hilbert--Schmidt 配对自伴随。对非空词 $w=(a_1,\ldots,a_n)$，写 $P_j=P_{s_j}^{b_j}$。秩一压缩逐次给出

$$
E_w=
\left(\prod_{j=1}^{n-1}\operatorname{tr}(P_jP_{j+1})\right)P_1,
$$

其中空积为一。事实上 $E_{(a_n)}=P_n$；若后缀效果为 $cP_{j+1}$，则 $P_j(cP_{j+1})P_j=c\operatorname{tr}(P_jP_{j+1})P_j$，倒序归纳即得公式。同一设置的相邻投影重叠为 $\delta_{s_j,s_{j+1}}$，不同设置的重叠为 $1/2$，因为

$$
\operatorname{tr}(P_s^bP_u^c)
=\frac{1+su\,\delta_{b,c}}2.
$$

故所有词效果在 $V$ 内，长度一的效果已通过 $P_+^X-P_-^X=X$、$P_+^Z-P_-^Z=Z$ 张成 $V$，空词给出 $I$。Pauli 正交性给出 $K$。特别地，每个分支都消去 $Y$，所以隐藏方向不会回流到可见坐标。

这也提供命题 78.3 所需的子集反例：只允许全部 $X$ 设置的词，是整个 $X,Z$ 字母表中的前缀闭合子集；其长度一及长度二的可见空间均为 $\operatorname{span}_{\mathbb R}\{I,X\}$，但 $\mathcal J_{Z,+}^*(I)=(I+Z)/2$ 不在其中。只保留这些词的长度一截断，仍有同样的相邻相等和失败。

最后，对一条终止记录 $h$，令 $q_h$ 是沿记录各次设置选择及终止决定的策略概率的乘积；确定策略时它等于零或一。因策略只依赖已有记录，$q_h$ 不依赖隐藏的输入坐标。该记录的概率是 $q_h\operatorname{tr}(\rho E_h)$，而各节点的分支迹按已证的递推求出。有限树上的求和及停止记录均因此精确确定。全程保存未归一化的 $t$；零迹的正分支必为零矩阵，继续递推仍为零，不在零概率记录上除以 $t$。证毕。

这里的精确经典数值预测以输入的精确 $x,z$ 已作为数值资料给定为前提；它没有提供从一份未知量子态中取得这两个数值的测量方法。

### 78.3 可见正投影的完全正性障碍

**命题 78.6（正而非完全正的预测投影）。** 在全复矩阵空间 $M_2(\mathbb C)$ 上，以计算基转置定义复线性映射

$$
\Pi(A)=\frac{A+A^T}{2}.
$$

它正、迹保持、保单位且幂等。在实 Hermitian 空间上，它是到 $V$ 的 Hilbert--Schmidt 正交投影；在全复矩阵空间上的像则为 $\operatorname{span}_{\mathbb C}\{I,X,Z\}$。它保持定义 78.4 的全部有限策略统计，却不是完全正映射。

证明。$I^T=I$、$X^T=X$、$Y^T=-Y$、$Z^T=Z$，故 $\Pi$ 恰好删去 $Y$ 坐标。实 Hermitian 限制上的正交性由 Pauli 正交基给出；一般复矩阵也有唯一的复 Pauli 展开，因此其复像是所写复张成空间，不能与实空间 $V$ 等同。

若 $A\ge0$，则 $A^T=\overline A$，且对任意复向量 $v$，

$$
v^\dagger A^T v
=\overline{\overline v^{\,\dagger}A\overline v}\ge0.
$$

右边被共轭的数本来就是非负实数，所以转置保持正性，平均映射 $\Pi$ 也正。记转置作用为 $T(A)=A^T$；它保持迹和单位，且 $T^2=\mathrm{id}$，因此

$$
\operatorname{tr}\Pi(A)=\operatorname{tr}A,\qquad
\Pi(I)=I,\qquad
\Pi^2=\tfrac14(\mathrm{id}+2T+T^2)=\Pi.
$$

又因 $A-\Pi(A)$ 在 Hermitian 空间上属于 $K$，命题 78.5 的所有词效果对该差配对为零，所有允许策略统计都被保持。

令

$$
|\Phi\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\quad
\rho_\Phi=|\Phi\rangle\langle\Phi|,\quad
F=\sum_{i,j=0}^1|ij\rangle\langle ji|.
$$

由 $\rho_\Phi=\tfrac12\sum_{i,j}|i\rangle\langle j|\otimes|i\rangle\langle j|$ 得到

$$
(T\otimes\mathrm{id})(\rho_\Phi)=\frac F2,\qquad
(\Pi\otimes\mathrm{id})(\rho_\Phi)=\frac{\rho_\Phi}{2}+\frac F4.
$$

归一化反对称向量 $|\Psi^-\rangle=(|01\rangle-|10\rangle)/\sqrt2$ 与 $|\Phi\rangle$ 正交，并满足 $F|\Psi^-\rangle=-|\Psi^-\rangle$，所以

$$
\langle\Psi^-|(\Pi\otimes\mathrm{id})(\rho_\Phi)|\Psi^-\rangle=-\frac14.
$$

因此 $\Pi\otimes\mathrm{id}$ 不保持正性，$\Pi$ 非完全正。完全正性、Choi 正性及 Kraus 表示的标准等价见 John Watrous，*The Theory of Quantum Information*，Cambridge University Press，2018，[Theorem 2.22](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf)；这里的归一化 Bell 见证直接算出了负期望。证毕。

这个见证排除的是把 $\Pi$ 本身当作量子通道；它没有排除其他编码。参考系统在这里用于检验完全正性，并未成为定义 78.4 的可查询对象。任意共同经典编码的障碍由下一命题单独证明。

### 78.4 后揭设置前不存在精确共同经典存储

**定义 78.7（单份输入的后揭二元查询）。** 存储者收到一份未知量子比特密度矩阵 $\rho$，在请求的设置 $b\in\{X,Z\}$ 揭示之前，固定使用任意有限父 POVM

$$
M_\lambda\ge0,\qquad\sum_{\lambda\in\Lambda}M_\lambda=I,
$$

只保留经典结果 $\lambda$。设置揭示后只允许归一化随机译码

$$
k_b(s\mid\lambda)\ge0,\qquad\sum_{s=\pm1}k_b(s\mid\lambda)=1.
$$

其有效效应与输出概率为

$$
E_s^b=\sum_\lambda k_b(s\mid\lambda)M_\lambda,
\qquad p_{M,k}(s\mid\rho,b)=\operatorname{tr}(\rho E_s^b).
$$

同一 $M,k$ 必须对所有密度输入和两个设置适用。任务只有一个后揭查询，不允许保留量子输出、再次取得输入副本或依输入改变存储方案。

**命题 78.8（任意有限父 POVM 的精确存储不可能性）。** 定义 78.7 中不存在满足

$$
\operatorname{tr}(\rho E_s^b)=\operatorname{tr}(\rho P_s^b)
\quad\text{对全部 }\rho,b,s
$$

的存储和译码方案。

证明。对任意这样的方案，定义四个正效应

$$
G_{su}=\sum_\lambda k_X(s\mid\lambda)k_Z(u\mid\lambda)M_\lambda.
$$

由两个译码核的归一化，

$$
\sum_{s,u}G_{su}=I,\qquad
\sum_uG_{su}=E_s^X,\qquad
\sum_sG_{su}=E_u^Z.
$$

这是构造联合边缘的数学乘积耦合，不要求同时运行两次实际查询。若假设中的全部密度态读数相等，则 $E_s^b=P_s^b$：Hermitian 差若非零，其某个非零特征值的单位本征向量所定义的纯态就给出非零读数，矛盾。因此

$$
0\le G_{su}\le P_s^X,\qquad0\le G_{su}\le P_u^Z.
$$

沿用第 38 节的正效应支撑论证：若 $0\le G\le P$ 且 $P$ 是正交投影，对 $v\in\ker P$ 有

$$
0\le\langle v,Gv\rangle\le\langle v,Pv\rangle=0.
$$

因 $\langle v,Gv\rangle=\|G^{1/2}v\|^2$，有 $Gv=0$。再由自伴随性，$\operatorname{ran}G\subseteq(\ker P)^\perp=\operatorname{ran}P$。这里 $P_s^X$ 的值域由 $(|0\rangle+s|1\rangle)/\sqrt2$ 张成，而 $P_u^Z$ 的值域由 $|0\rangle$ 或 $|1\rangle$ 张成；它们的交为零。故每个 $G_{su}=0$，与 $\sum_{s,u}G_{su}=I$ 矛盾。

这一支撑原则也是 Heinosaari、Reitzner、Stano，*Notes on Joint Measurability of Quantum Observables*，[arXiv:0811.0783，附录 Proposition 8](https://arxiv.org/abs/0811.0783) 中处理任意联合 POVM 的关键：一个锐边缘已强制相容性。此处直接使用值域交为零的量子比特特例，不以“联合测量本身也是锐测量”为前提。证毕。

**命题 78.9（首次实际查询后的有限标签模拟）。** 若第一次设置已经揭示并实际执行其 Lüders 测量，则每个正概率结果 $(b,s)$ 后的归一化状态恰为 $P_s^b$。此后定义 78.4 的任意有限策略，可把量子状态替换为四个标签 $(X,+1),(X,-1),(Z,+1),(Z,-1)$ 并作经典随机更新，精确模拟后续记录。策略控制仍可使用已记录的完整经典历史；四个标签只替代量子状态，不声称压缩策略自身的记忆。

证明。秩一压缩给出 $\mathcal J_{b,s}(\rho)=\operatorname{tr}(\rho P_s^b)P_s^b$；只在该系数为正时归一化。若当前标签为 $(b,s)$，下一设置为 $c$，结果 $u$ 的概率为

$$
\operatorname{tr}(P_s^bP_u^c)=\frac{1+su\,\delta_{b,c}}2,
$$

发生后把标签改为 $(c,u)$。与已记录历史所决定的策略选择结合，对步骤数归纳即得整个后续记录分布。标签是在首次实际查询之后取得，不是定义 78.7 要求的设置揭示之前的共同存储。证毕。

### 78.5 共同经典存储的精确极小极大代价

**定理 78.10（后揭 $X,Z$ 查询的二元总变差最优值）。** 对定义 78.7 的任意有限父 POVM 和随机译码，定义

$$
e(M,k)=\sup_{\rho,\,b\in\{X,Z\}}
\frac12\sum_{s=\pm1}
\left|\operatorname{tr}(\rho P_s^b)-\operatorname{tr}(\rho E_s^b)\right|.
$$

则在所有这类方案上，

$$
\inf_{M,k}e(M,k)=e_*=
\frac{1-1/\sqrt2}{2},
$$

且下确界由一个四结果 POVM 达到。下界不要求边缘无偏，也不预设父 POVM 的结果数。

证明。固定任意方案，记 $e=e(M,k)$，并使用命题 78.8 的乘积耦合 $G_{su}$。取四个等概率测试输入 $P_s^X,P_u^Z$，在存储后揭示其所属设置。在输入 $P_s^b$ 上，理想二元输出确定为 $s$，故总变差恰为 $1-\operatorname{tr}(P_s^bE_s^b)$。因此每个正确标签概率至少为 $1-e$，平均成功率满足

$$
\begin{aligned}
1-e\le S
&=\frac14\sum_s\operatorname{tr}(P_s^XE_s^X)
+\frac14\sum_u\operatorname{tr}(P_u^ZE_u^Z)\\
&=\sum_{s,u}\operatorname{tr}(G_{su}R_{su}),
\qquad R_{su}=\frac{P_s^X+P_u^Z}{4}.
\end{aligned}
$$

采用第 40 节的谱奖励上界方法。因为 $XZ+ZX=0$，

$$
(sX+uZ)^2=2I,\qquad
R_{su}=\frac I4+\frac{sX+uZ}{8}.
$$

$sX+uZ$ 无迹、Hermitian，故特征值为 $\pm\sqrt2$，从而

$$
R_{su}\le cI,\qquad
c=\frac{1+1/\sqrt2}{4}.
$$

正性给出 $\operatorname{tr}(G_{su}(cI-R_{su}))\ge0$；这也可写成正矩阵 $G_{su}^{1/2}(cI-R_{su})G_{su}^{1/2}$ 的迹。因此，对所有有限父 POVM 与随机译码，

$$
S\le c\sum_{s,u}\operatorname{tr}G_{su}
=c\operatorname{tr}I=2c,
\qquad
 e\ge1-2c=e_*.
$$

为证明达到该界，取父 POVM

$$
G_{su}^{\rm opt}=\frac14\left(I+\frac{sX+uZ}{\sqrt2}\right),
\qquad s,u\in\{+1,-1\}.
$$

由同一平方恒等式，其特征值为零和 $1/2$，故各项正；对四个符号求和，非单位项相消，得到 $\sum_{s,u}G_{su}^{\rm opt}=I$。请求 $X$ 时输出 $s$，请求 $Z$ 时输出 $u$，其边缘恰为

$$
E_s^b=\frac{I+sb/\sqrt2}{2}.
$$

对任意密度输入，两个结果的概率差符号相反，故实际二元总变差为

$$
\frac12\sum_{s=\pm1}
\left|\operatorname{tr}\!\left(\rho\frac{s(1-1/\sqrt2)b}{2}\right)\right|
=e_*|\operatorname{tr}(\rho b)|\le e_*.
$$

最后一个不等式来自 $b$ 的谱为 $\{+1,-1\}$；在 $b$ 的任一本征态上取等号。因此该方案的上确界为 $e_*$，与下界相同。误差是对所有态统一有界，并非每个态都等于 $e_*$；例如 $\rho=I/2$ 时为零。证毕。

Heinosaari、Reitzner、Stano 的上述论文 Proposition 1、式 (5) 给出无偏二元量子比特效应的判据 $\|a+b\|+\|a-b\|\le2$；取两个正交方向及共同收缩系数 $\eta\ge0$，它化为 $2\sqrt2\eta\le2$，与构造中的 $\eta=1/\sqrt2$ 一致。该无偏判据并不代替上面对任意有偏译码的下界。Carmeli、Heinosaari、Toigo，*State discrimination with post-measurement information and incompatibility of quantum measurements*，[arXiv:1804.09693，§V.2，式 (27)](https://arxiv.org/abs/1804.09693) 给出两个等概率量子比特本征基的平均后测量信息成功率

$$
\frac12\left(1+\sqrt{\frac{1+|\cos\theta|}{2}}\right).
$$

在 $\theta=\pi/2$ 时，该值为 $2c=1-e_*$。本定理从四态测试得到极小极大下界，再用构造的逐态误差得到一致上界，补足平均成功率与最坏态代价之间的桥接。$e_*$ 只是在定义 78.7 资源约束下的一次后揭查询最优值，不是可见闭合缺陷、退相干速率或跨任务的普适阈值。

### 78.6 三个 Zeckendorf 标签中的等距嵌入

**命题 78.11（合法窗口内的支撑转移及全载体可见空间）。** 沿用本卷定义 1.1 及 Zeckendorf 扩展的开放窗口约定，

$$
\mathcal W_2=\{00,01,10\},\qquad
\mathcal H_{\mathcal W_2}=\operatorname{span}_{\mathbb C}\{|00\rangle,|01\rangle,|10\rangle\}.
$$

定义等距嵌入 $U:\mathbb C^2\to\mathcal H_{\mathcal W_2}$ 为 $U|0\rangle=|00\rangle$、$U|1\rangle=|01\rangle$，并令

$$
Q=UU^\dagger=|00\rangle\langle00|+|01\rangle\langle01|,
\quad R=I_3-Q=|10\rangle\langle10|,
\quad\widehat X=UXU^\dagger,\quad\widehat Z=UZU^\dagger.
$$

每个设置 $b\in\{X,Z\}$ 使用三个投影

$$
\widehat P_s^b=\frac{Q+s\widehat b}{2}\quad(s=\pm1),
\qquad R,
$$

及相应的压缩分支 $A\mapsto\widehat P_s^b A\widehat P_s^b$、$A\mapsto RAR$。对支撑在 $Q$ 的输入，命题 78.5 的序列统计、命题 78.8 的精确存储不可能性及定理 78.10 的二元代价 $e_*$ 全部原值转移。对整个三维载体和含补空间结果的全部词族，长度至少一的实可见空间为

$$
\widehat V_H=\operatorname{span}_{\mathbb R}\{Q,R,\widehat X,\widehat Z\}
\quad(H\ge1),
$$

而长度零的空间为 $\operatorname{span}_{\mathbb R}\{I_3\}$。

证明。两位二进制词中，开放相邻约束只排除 $11$，故合法词恰为上述三个。所选基向量正交，给出 $U^\dagger U=I$、$UU^\dagger=Q$、$RU=0$。因此

$$
\widehat X^2=\widehat Z^2=Q,\qquad
\widehat X\widehat Z+\widehat Z\widehat X=0,\qquad
\widehat P_s^b=UP_s^bU^\dagger.
$$

于是 $\widehat P_+^b,\widehat P_-^b,R$ 两两正交、各自幂等、自伴随，且和为 $I_3$。命题 78.5 的单 Kraus 正性与迹求和论证逐项适用，证明每个设置分别归一化。

支撑在 $Q$ 的密度矩阵唯一为 $\widehat\rho=U\rho U^\dagger$，其中 $\rho=U^\dagger\widehat\rho U$ 是量子比特密度矩阵。直接计算

$$
\widehat P_s^b\widehat\rho\widehat P_s^b
=U(P_s^b\rho P_s^b)U^\dagger,
\qquad R\widehat\rho R=0,
\qquad
\operatorname{tr}(\widehat\rho\widehat P_s^b)
=\operatorname{tr}(\rho P_s^b).
$$

因此全部支撑内序列递推相同。若三维父 POVM 为 $(M_\lambda)_\lambda$，则 $(U^\dagger M_\lambda U)_\lambda$ 是量子比特父 POVM，保留同一译码后，在所有支撑内输入上的二元概率完全相同；故精确不可能性和 $e_*$ 下界都转移。反向把最优量子比特父 POVM 扩为 $(UG_{su}^{\rm opt}U^\dagger)_{s,u}$ 加上 $R$，并在结果 $R$ 上任选归一化二元译码。支撑内输入对 $R$ 的概率为零，故上界也原值转移。这一二元比较的输入域严格限定在 $Q$ 上。

在整个载体上，长度一的效果含 $\widehat P_\pm^X,\widehat P_\pm^Z,R$；它们的和与差给出 $Q,\widehat X,\widehat Z,R$。四者实线性独立：限制到 $Q$ 后由 $I,X,Z$ 独立性得前三个系数为零，限制到 $R$ 得最后系数为零。所有这些投影均秩一，命题 78.5 的压缩归纳仍使每个非空词效果为首个投影的标量倍数，故更长词不增加方向。空词效果 $I_3=Q+R$ 也在该空间内。这证明完整可见空间的等式，不能把它写成只有三个实方向的量子比特空间。证毕。

这里的 Zeckendorf 结构提供合法标签及一个明确的等距嵌入。仪器由所写投影指定；没有从 Fibonacci 权重推导自然能谱、实验耦合、普适几何或经典性，也没有改变支撑内的一次查询存储界。

## 79. 可见算子系统、可编码子系统与 Zeckendorf 记忆成本

### 79.1 预测闭合不等于代数闭合

第 78 节中的 $X/Z$ 任务给出一个最小反例。其所有有限词效果都落在

$$
V_{XZ}=\operatorname{span}_{\mathbb R}\{I,X,Z\},
$$

并且 $Y$ 方向不会回流到这些读数。因而 $V_{XZ}$ 对这组仪器是预测闭合的。然而

$$
XZ=iY\notin V_{XZ}.
$$

所以 $V_{XZ}$ 不是复矩阵代数，也不是一个可以直接当作独立量子系统的乘法闭子空间。

这一区分可以写成两个不同的要求。先取一个已经固定的、单一的 Heisenberg 更新 $H$ 和初始效果族 $S$，令

$$
V_0=\operatorname{span}_{\mathbb R}(\{I\}\cup S),
\qquad
V_{n+1}=V_n+H(V_n).
$$

**预测闭合**是在某个 $N$ 后满足

$$
V_N=V_{N+1},
$$

这时已有的 `operator_system_tower_once_stable_permanently`（其前提是一个明确给定的保单位完全正 Heisenberg 映射）保证后续塔保持不变。多个设置或自适应协议需要先给出打包后的单一通道，或另证族版本；不能由该定理直接推出。**代数闭合**则要求在复化后还满足

$$
V_{\mathbb C}V_{\mathbb C}\subseteq V_{\mathbb C},
\qquad
V_{\mathbb C}^{\ast}=V_{\mathbb C}.
$$

前者保证指定实验的未来统计可由当前坐标预测；后者只说明存在一个有限维含单位的 $*$-子代数候选载体。要把它解释成独立的 $C^*$ 子系统，仍需另给编码、恢复和动力学交换图。前者不推出后者。

证明 $V_{XZ}$ 的失败只需计算 $XZ=iY$。这也解释了第 78 节正投影 $\Pi$ 的地位：它可以在实 Hermitian 读数上保持全部指定统计，却不能直接当作完全正的量子通道。若要求一个物理编码，必须额外提供完全正的嵌入、压缩和其相容的动力学；仅有线性正投影不足以完成这一步。

### 79.2 物理编码的最小接口

设 $\mathcal H_S$ 是完整系统，$\mathcal H_R$ 是候选记忆空间。下面把一个“可独立访问的量子记忆”作为额外的强假设，定义为一对映射

$$
\iota:\mathcal B(\mathcal H_R)\longrightarrow\mathcal B(\mathcal H_S),
\qquad
\mathcal R:\mathcal B(\mathcal H_S)\longrightarrow\mathcal B(\mathcal H_R),
$$

其中 $\iota$ 要求为 Heisenberg 意义下的保单位 $*$-单同态（若只给 UCP 映射，则还须另加 complete-order embedding 假设），$\mathcal R$ 是保单位完全正映射，并满足

$$
\mathcal R\circ\iota=\operatorname{id}_{\mathcal B(\mathcal H_R)}.
$$

若只要求把完整演化商到记忆上，要求某个记忆演化 $H_R$ 满足

$$
\mathcal R\circ H=H_R\circ\mathcal R.
$$

这三条分别保证代数嵌入、Heisenberg 商的可定义性和预测闭合；它们是定义中的额外条件，不是由 operator system 自动得到的。若要求记忆内部作为完整子系统演化，还要加强为

$$
H\circ\iota=\iota\circ H_R.
$$

在 Schrödinger 对偶方向，这些 UCP 条件对应相应的 CPTP 编码与解码条件。它们比“$V$ 是一个稳定实向量空间”严格得多。

在有限维情形，若只要求任务效果而非整个矩阵代数，则可以把 $\mathcal R$ 的像限制为一个含单位的 Hermitian operator system；这正是第 77--78 节可见空间的适用范围。若要求任意后续量子操作都能在记忆内实现，则必须进一步验证乘法闭合或给出一个更大的代数载体。因而“对象”至少有两层：

$$
\text{任务对象}=\text{对指定实验闭合的 operator system},
$$

$$
\text{量子子系统}=\text{带完全正编码与回收的代数对象}.
$$

把第一层直接称为第二层，会把预测充分性误报成物理可实现性。

### 79.3 共享经典存储的成本不是只数当前标签

设 $N$ 个历史在目标实验族中要求精确区分，并且它们必须被一次性写入一个 $d$ 维量子记忆。仓库的 `finite_memory_history_capacity` 在明确假设“$N$ 个密度态由同一个 POVM 一次性完美区分”时给出

$$
N\le d.
$$

若记忆由 $b$ 个量子比特组成，则 $d=2^b$，因此

$$
 b\ge \lceil\log_2N\rceil.
$$

对长度为 $L$、禁止相邻两个 $1$ 的 Zeckendorf 合法构型，

$$
|\mathcal W_L|=F_{L+2}.
$$

若每个合法构型先被编码成记忆 Hilbert 空间中的一个密度态，且任务要求同一个 POVM 一次性完美区分所有这些态，便得到必要条件

$$
 b\ge \left\lceil\log_2 F_{L+2}\right\rceil.
$$

这只是完美区分的下界。若只需预测一个目标族，历史可以按未来响应合并，所需维数由响应等价类数量决定，而不由原始构型总数决定。反过来，若两个当前标签在当前测量下相同、但在后续实验中可分开，则把它们合并会破坏闭合，即使当前标签数已经很小。

因此记忆预算应写成三元组，而不是一个整数：

$$
(\text{响应类数},\ \text{闭合误差},\ \text{可回收关联}).
$$

第一项控制需要多少可区分记录，第二项控制有限预测视界内的近似程度，第三项控制暂时不可见的相干是否可能重新出现。

### 79.4 Zeckendorf 约束改变的是载体维数，不是动力学

令

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
\mathcal H_{Z,L}=\operatorname{span}\{|w\rangle:w\in\mathcal W_L\}.
$$

对 $L\ge2$，并取 $\mathcal W_0=\{\epsilon\}$、$\mathcal W_1=\{0,1\}$，分解首位可得

$$
\mathcal W_L=0\mathcal W_{L-1}\sqcup10\mathcal W_{L-2},
$$

从而

$$
\dim\mathcal H_{Z,L}=F_{L+2}.
$$

这一步只决定允许的基态数量。若 $P_Z$ 是投影到该空间的投影，实际 Hamiltonian $H$ 还必须满足

$$
[H,P_Z]=0
$$

才能保证合法构型空间在连续演化下保持不变；离散更新则需要

$$
UP_Z=P_ZUP_Z.
$$

否则，Zeckendorf 只是对初始构型的编号，演化会产生不在该刻度内的状态。仓库已有的 `prime_diagonal_saturation` 说明了相近但不同的边界：当可见观测属于素数占据生成的对角代数时，完全对角 pinching 不改变这些观测的迹配对；该结论没有把对角代数之外的相干宣称为不存在，也没有给出任意 Hamiltonian 的不变性。

对 $L=2$，合法字串为 $00,01,10$。可把 $|01\rangle,|10\rangle$ 嵌入一个量子比特的两个基态，并把 $|00\rangle$ 作为剩余结果 $R$。这是一种任务特定的编码；它不等于把三维合法空间整体识别成二维量子比特。若后续操作能区分 $|00\rangle$ 与其余两态，$R$ 必须继续保留，否则该信息会在下一步回流中丢失。

### 79.5 可检验的“稳定经典现实”条件

结合前面各节，可以把一个有限任务上的稳定对象**提议**定义为四元组

$$
\mathfrak O=(V,\mathfrak T,H,\varepsilon),
$$

其中 $V$ 是含单位的可见 operator system，$\mathfrak T$ 是允许的实验族，$H$ 是预测视界，$\varepsilon$ 是允许误差。其候选精度条件应写成：对所有密度矩阵 $\rho,\sigma$，若

$$
\forall A\in V,\quad \operatorname{tr}(\rho A)=\operatorname{tr}(\sigma A),
$$

则要求

$$
\sup_{T\in\mathfrak T,\,|w|\le H}
\operatorname{TV}\bigl(p_T(w\mid\rho),p_T(w\mid\sigma)\bigr)
\le\varepsilon.
$$

实验族 $\mathfrak T$ 应包含所允许的设置选择、记录和自适应停止规则。记录通道与动力学的闭合缺陷还须另行定义并纳入同一预算；这里的条件是研究接口，不是仓库现有的一个单独 Lean 判据。若再要求一个真正的量子子系统，则追加完全正的 $\iota,\mathcal R$ 及交换图条件。

因此问题“保留多少历史才得到经典现实”没有独立于任务的答案。精确形式是：寻找最小的 $V$，使其在给定 $\mathfrak T$、$H$ 和 $\varepsilon$ 下闭合，同时满足所需的物理编码条件。在明确给出成本函数和闭合缺陷定义后，才可把它写成如下研究中的受约束优化问题：

$$
\min_V\ \operatorname{cost}(V)
\quad\text{subject to}\quad
\operatorname{closure\_defect}(V;\mathfrak T,H)\le\varepsilon,
$$

这里的 $\operatorname{cost}$ 和 $\operatorname{closure\_defect}$ 都是待定义的研究量；物理版本还须追加“存在完全正编码、恢复和交换图”的约束，不能把它替换成尚未定义的标量等式。

这把“相对性”限制在明确的实验族、时间范围和误差预算内：换实验族会改变最小 $V$，增加预测视界会暴露原先隐藏的方向，要求物理可编码又会排除只有线性闭合而没有完全正回收的候选空间。

本节使用的永久稳定、可见维数、有限记忆容量和对角饱和均来自现有 Lean 模块；`FutureStatisticsEquivalence` 还把“所有未来读数相同”精确连接到差态对无限 Heisenberg 生成 operator system 的湮灭。$X/Z$ 的非代数例子、完全正编码接口和 Zeckendorf 投影不变条件是对这些结果的组合解释。它们给出可形式化的后续目标，但不宣称仓库已经证明任意 operator system 都有物理回收映射，也不把任务特定的二维嵌入提升为普遍量子存储定理。

## 追加锚（新终端）

## 80. 中心标签、块内自由度与可组合历史

### 80.1 预测算子系统与代数闭包

第 79 节的 $X/Z$ 例子说明，预测闭合和乘法闭合是不同要求。设一个固定的 Heisenberg 映射为 $H$，初始效果族为 $S$，定义

$$
V_0=\operatorname{span}_{\mathbb R}(\{I\}\cup S),
\qquad
V_{n+1}=V_n+H(V_n).
$$

全体有限回拉的实线性空间为

$$
V_\infty
=\operatorname{span}_{\mathbb R}
\{H^k(A):A\in V_0, k\in\mathbb N\}.
$$

`operator_system_tower_once_stable_permanently` 说明，在单一保单位完全正 Heisenberg 映射的前提下，一层相邻稳定就会永久稳定；`future_statistics_iff_annihilates_infinite_system` 则在其密度态、Schrödinger 通道、保单位 Heisenberg 对偶和迹配对前提下，把所有未来统计相同精确连接到差态对 $V_\infty$ 的迹配对全部为零。因此，$V_\infty$ 是相对于这组初始效果和这一个通道的预测载体。

但令

$$
\mathcal A_\infty
=\operatorname{Alg}^{\ast}_{\mathbb C}(V_\infty)
$$

表示包含 $V_\infty$ 的最小含单位复 $\ast$-子代数。一般只有

$$
V_\infty\subseteq (\mathcal A_\infty)_{\mathrm{sa}},
$$

而没有等号。两个可见效果的乘积、交换子或条件组合，可能产生原始未来词中没有出现的新方向。特别地，$V_{XZ}=\operatorname{span}_{\mathbb R}\{I,X,Z\}$ 对第 78 节指定仪器足以预测，却因为 $XZ=iY$ 而不是代数。

因此必须区分：

$$
V_\infty=\text{对指定未来统计最小的线性预测载体},
$$

$$
\mathcal A_\infty=\text{对指定可组合操作最小的代数载体}.
$$

若后续实验只查询原先的效果，加入所有乘积可能是过度保留；若实际协议的组合观测明确包含某个乘积（例如把 $AB$ 作为新的效应或关联观测），该乘积才会进入新的响应，不能只依靠 $V_\infty$ 上的读数。一般序列仪器的响应仍由具体 instrument 和 Heisenberg 共轭决定。`prediction_closure_minimal_dynamical_repair` 给出相应的线性最小不变闭包，但没有把该闭包提升为乘法代数。

### 80.2 固定代数的中心与块内量子自由度

设 $\Lambda$ 有限、每个 $n_\lambda$ 有限，并先选定一个代数同构，使有限维固定代数具有块分解

$$
\mathcal A
\cong
\prod_{\lambda\in\Lambda}M_{n_\lambda}(\mathbb C).
$$

仓库的 `record_fixed_center_eq_block_scalars` 精确给出规范乘积代数的中心；经上述同构输运后得到这里的中心公式：

$$
Z(\mathcal A)
=
\left\{(c_\lambda I_{n_\lambda})_{\lambda\in\Lambda}:c_\lambda\in\mathbb C\right\}.
$$

因此（维数公式使用有限直积的标准线性代数维数计算）

$$
\dim_{\mathbb C}Z(\mathcal A)=|\Lambda|,
\qquad
\dim_{\mathbb C}\mathcal A=\sum_{\lambda\in\Lambda}n_\lambda^2.
$$

只有当所有 $n_\lambda=1$ 时，代数才交换，中心才等于整个代数。若某个 $n_\lambda>1$，同一个中心标签仍允许一个非平凡的块内量子系统；把标签 $\lambda$ 当成完整经典对象，会把这部分可由后续操作恢复的关系一并丢掉。

这给“经典记录”的含义加上一个边界：在给定记录通道确实固定这些中心投影、且允许观测族只读取它们时，中心投影才可作为稳定的经典标签；抽象代数的中心本身不自动给出物理记录通道。中心标签的数量不等于完整联合系统的 Hilbert 维数，也不等于可组合算子的维数。`FiniteMemoryHistoryCapacity.finite_memory_history_capacity` 的 $N\le d$ 也只在 $N$ 个密度态被同一个 POVM 一次性完美区分时成立，不能把中心标签数自动解释成所有物理记忆的维数。

### 80.3 Zeckendorf 标签只决定中心数量的特殊情形

取禁止相邻 $11$ 的合法集合

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
|\mathcal W_L|=F_{L+2}.
$$

若每个合法字串只对应一个一维块，则得到纯经典代数

$$
\mathcal A_Z
=\bigoplus_{w\in\mathcal W_L}\mathbb C,
$$

其中心维数、代数维数和标签数都等于 $F_{L+2}$。这正是 Zeckendorf 刻度与经典记录完全吻合的特殊情况。

若每个标签后面仍保留大小为 $n_w$ 的块，则

$$
\mathcal A_Z^{\mathrm{block}}
=\bigoplus_{w\in\mathcal W_L}M_{n_w}(\mathbb C),
$$

并且

$$
\dim_{\mathbb C}Z(\mathcal A_Z^{\mathrm{block}})=F_{L+2},
\qquad
\dim_{\mathbb C}\mathcal A_Z^{\mathrm{block}}
=\sum_{w\in\mathcal W_L}n_w^2.
$$

若物理 Hilbert 空间是一个有限维表示，并在第 $w$ 个块上含有重数 $m_w$（且这些重数满足所选表示的忠实性要求），其载体维数则为

$$
\dim\mathcal H=\sum_{w\in\mathcal W_L}m_wn_w.
$$

这三个数分别回答三个问题：合法标签有多少，可组合的算子有多少，实际联合载体有多少。因此不能从 $F_{L+2}$ 单独推出量子记忆维数、可见算子维数或未来统计的 Hankel 秩。

第 78 节的三构型嵌入已经展示了同一组合法字串在加入补空间后会出现额外记录方向；这里的块分解把“标签之外仍有内部状态”写成了统一公式。若后续实验只访问中心，块内状态可以暂时隐藏；若允许块内操作，隐藏部分必须继续保留在模型中。

### 80.4 近似乘法闭包与历史预算

对一个有限维预测截断 $V\subseteq V_\infty$，先选定矩阵范数，并令距离取该范数到子空间的距离；定义乘法缺陷

$$
\eta(V)
=
\sup_{\substack{A,B\in V\\\|A\|,\|B\|\le1}}
\operatorname{dist}(AB,V+iV).
$$

这里 $V+iV$ 是 $V$ 的复化；有限维保证该子空间闭合。若 $\eta(V)=0$，则所有单位范数以内的可见乘积都落在复化空间中，因而该截断对这些乘积精确闭合。若 $\eta(V)>0$，至少有一对当前可见关系的组合产生了新的方向。这个量是研究定义，不是已冻结的物理误差；研究上有两种不同处理：

$$
\begin{aligned}
&\text{扩大记录，加入产生该乘积的历史关系；}\\
&\text{固定允许误差，把 }\eta(V)\text{ 纳入预测误差预算。}
\end{aligned}
$$

$\eta(V)$ 只量化一步的乘法缺口，不自动给出任意多步实验的误差界。多步控制、参考系统和有记忆环境仍需使用联合通道距离或相应的序列误差界；本节没有把 $\eta$ 宣称为一个已冻结的物理误差定理。

因此，对“保留多少历史才能得到稳定经典现实”的问题，三层结构可以写成

$$
\boxed{
\begin{gathered}
\text{只预测指定未来读数：保留 }V_\infty;\\
\text{允许可组合后续操作：保留 }\mathcal A_\infty;\\
\text{只读取稳定经典标签：保留 }Z(\mathcal A_\infty);\\
\text{存在量子块时：还要保留每个中心块的内部自由度。}
\end{gathered}}
$$

Zeckendorf 约束可以决定中心标签的自然组织和数量 $F_{L+2}$，但不能替代 Heisenberg 演化、乘法闭包或块内量子动力学。所谓稳定经典现实不是一个脱离任务的单独刻度，而是相对于实验族和后续操作选择的三层对象：预测算子系统、可组合代数以及其中心记录。只有明确当前实验使用哪一层，才知道哪些历史可以安全丢弃，哪些历史会在下一次组合操作中重新显现。

本节复用 `operator_system_tower_once_stable_permanently`、`future_statistics_iff_annihilates_infinite_system`、`prediction_closure_minimal_dynamical_repair`、`record_fixed_center_eq_block_scalars` 和 `finite_memory_history_capacity` 的现有结果。中心维数、块内自由度、乘法缺陷 $\eta(V)$ 与 Zeckendorf 分块的组合是本节的开放研究桥接，不冒充已有 Lean 定理。

## 追加锚（新终端）

## 81. 记录重叠、恢复误差与可访问历史

### 81.1 记录不是标签数，而是条件记录的重叠

第 80 节把中心标签与块内自由度分开，但还缺少一个量化问题：当记录被压缩后，剩余的相干究竟还能被恢复多少？仓库的 `FiniteRecordRecoveryError` 给出一个直接的有限模型。

取有限支持的复系数序列 $c_k$，满足

$$
\sum_{k\in\mathbb Z}\lVert c_k\rVert^2=1,
$$

并令记录的平移重叠为

$$
\gamma(\ell)
=
\sum_{k\in\mathbb Z}c_{k+\ell}\,\overline{c_k}.
$$

若系统构型 $i$ 被放置在整数位置 $q(i)$，记录通道对矩阵元的作用为

$$
\Lambda(A)_{ij}
=
\gamma\bigl(q(i)-q(j)\bigr)A_{ij}.
$$

因此对角项保持不变，而构型 $i,j$ 之间的相干按记录重叠 $gamma(q(i)-q(j))$ 缩放。这个量同时保留模长和相位；它不是“记录了几次”的计数。

`coefficient_gamma_neg` 保证

$$
\gamma(-\ell)=\overline{\gamma(\ell)},
$$

所以成对的非对角矩阵元仍满足 Hermitian 对称。对于有限支持记录，$gamma$ 是记录波形与其平移的自相关；记录形状、位置差和相位约定共同决定可见相干，而不是 Zeckendorf 标签本身单独决定。

### 81.2 任意恢复都有一个由记录重叠决定的下界

设 $q(i)-q(j)\ne0$。`finite_record_recovery_error_lower_bound` 对任意量子通道 $R$ 都给出

$$
\frac{1-\lVert\gamma(q(i)-q(j))\rVert}{2}
\le
\sup_{\rho}
\frac12
\left\|
R\!\left(\Lambda(\rho)\right)-\rho
\right\|_1.
$$

更准确地说，右侧是该误差集合的上确界；定理还构造了两个输入态，它们在记录通道前的迹距离为 $1$，经过记录后变为 $\lVert\gamma(q(i)-q(j))\rVert$。迹距离的收缩性说明，任何恢复通道都必须支付上述损失。

这给出两个极端：

$$
\lVert\gamma(q(i)-q(j))\rVert=1
\quad\Longrightarrow\quad
\text{该下界为 }0,
$$

说明相干可能只是旋转或保留相位，不能从下界推出已经经典化；而

$$
\gamma(q(i)-q(j))=0
\quad\Longrightarrow\quad
\text{任意恢复的最坏误差至少为 }\frac12.
$$

所以“记录已经抹掉历史”必须附带记录模型和误差指标。相同的标签数量可以对应完全不同的 $\gamma$，相同的单步去相干也可以对应不同的多步恢复能力。

### 81.3 Zeckendorf 位置与重叠谱

若把合法 Zeckendorf 构型 $w\in\mathcal W_L$ 映射到整数坐标 $q(w)$，例如使用权重 $(F_2,F_3,\ldots,F_{L+1})$ 的规范读数，则记录通道的相干矩阵为

$$
R_{wv}=\gamma\bigl(q(w)-q(v)\bigr).
$$

这说明 Zeckendorf 的作用是提供一组离散位置差；真正决定哪两条历史仍能相干汇聚的，是这些位置差落在记录自相关 $\gamma$ 的什么位置。

即使 $q(w)$ 唯一，仍可能出现

$$
q(w)-q(v)\ne q(w')-q(v')
\quad\text{但}\quad
\gamma(q(w)-q(v))=\gamma(q(w')-q(v')),
$$

也可能出现不同的位置差产生同一相位。于是“编码唯一”与“物理记录可区分”是两件事：前者是整数表示性质，后者是记录波形和相互作用的性质。

若记录设计满足对所有不同合法构型

$$
\left|\gamma(q(w)-q(v))\right|\le q_0<1,
$$

则重复使用独立同形记录时，相应的非对角系数至多按 $q_0^N$ 衰减；若记录是同一联合自由度的相干复用，则必须保留联合系统，不能把每轮都替换成无记忆的乘法通道。第 78 节的 fresh/reuse 对照正是这两个模型的差别。

### 81.4 局部读数丢失不等于联合历史消失

`reduced_irreversibility_is_access_defect` 给出另一个边界。存在两个整体输入 $\rho,\sigma$，满足它们的对角读数相同而某个相干元不同。受控记录耦合后，联合态仍不同，但环境偏迹相同：

$$
\operatorname{Tr}_E(\Omega_\rho)
=
\operatorname{Tr}_E(\Omega_\sigma),
\qquad
\Omega_\rho\ne\Omega_\sigma.
$$

因此不存在只依赖这个局部边缘态的统一恢复函数

$$
D\!\left(\operatorname{Tr}_E\Omega\right)=\Omega
$$

来恢复这两个联合记录。可是访问完整记录并施加受控耦合的逆操作后，二者都能恢复到各自的空记录输入：

$$
U^\dagger\Omega_\rho U=\rho\otimes|0\rangle\langle0|,
\qquad
U^\dagger\Omega_\sigma U=\sigma\otimes|0\rangle\langle0|.
$$

这把“历史是否存在”改写成一个可操作的问题：历史关系是否仍在允许访问的联合自由度中，而不是是否已经出现在某个局部数值上。局部边缘的经典化可以与整体可逆性同时成立。

### 81.5 对稳定经典现实的修正

结合第 79、80 节，稳定经典现实至少需要三个独立条件：

$$
\boxed{
\begin{aligned}
&\text{记录重叠谱在目标视界内足够收缩；}\\
&\text{可见 operator system 对指定实验闭合；}\\
&\text{被省略的联合记录在允许操作族中不会重新回流，或其回流误差有界。}
\end{aligned}}
$$

第一条由 $\gamma$ 的模长和恢复误差下界约束，第二条由 $V_\infty$ 或其有限稳定阶段约束，第三条由可访问环境范围和联合通道决定。Zeckendorf 可以为第一条提供规范位置差，为第二条提供合法构型索引，但不能单独证明任一条的物理前提。

因此，问题“要保留多少历史”现在可以写成一个带任务参数的优化：在给定实验族 $\mathfrak T$、预测视界 $H$、允许误差 $\varepsilon$ 和允许访问的记录代数 $\mathcal R$ 下，寻找最小保留结构，使

$$
\sup_{T\in\mathfrak T,\,n\le H}
\operatorname{TV}\bigl(p_T^{\mathrm{full}}(n),p_T^{\mathrm{retained}}(n)\bigr)
\le\varepsilon,
$$

同时满足记录重叠诱导的恢复下界、operator-system 闭合和联合访问约束。这个优化问题仍是开放的研究接口；本节只把已有的重叠谱、恢复下界和局部访问反例接到同一条可检验主线上。

本节复用 `coefficient_gamma_neg`、`finite_record_recovery_error_lower_bound` 和 `reduced_irreversibility_is_access_defect` 的现有 Lean 结果。Zeckendorf 位置映射、重复记录的多步误差和最后的保留结构优化是组合推导，不冒充仓库已有的统一恢复定理。

## 追加锚（新终端）

## 82. 有限预测深度、完整证书与 Zeckendorf 载体

### 82.1 深度不是时间长度，而是可见空间的秩增量

第 80 节中的 $V_\infty$ 是所有有限 Heisenberg 回拉的线性闭包。对一个有限维载体，真正需要观察多深，不等于实验运行了多少物理时间，而取决于这条回拉链还能增加多少个线性独立方向。

设 $d\ge1$，固定一个字母表和一个单一的 instrumentDual，并令 $V_n$ 为长度不超过 $n$ 的 sequential word effects 的实线性张成。若所有有限词效果最终张成整个 Hermitian 载体，则 `finite_sequential_completeness_depth` 给出某个

$$
N\le d^2-1
$$

使得长度不超过 $N$ 的词已经张成全部 Hermitian 效果空间。

这个上界来自实 Hermitian 维数的有限性：去掉由迹固定的单位方向后，trace-zero Hermitian 方向至多有 $d^2-1$ 个独立维度。每一步若还没有稳定，中心化空间至少增加一个维度；因此不可能在超过这个维数增量后继续严格增加。它不是任意效果标签数或物理时间长度的普遍上界。

这里的 $N$ 是一个最坏情形证书深度，不是任意系统的实际最小深度。若初始效果已经包含很多方向，实际深度可能远小于 $d^2-1$；若词族不能张成完整 Hermitian 空间，则该完整性定理的前提不成立，不能从维数直接宣称所有状态都可区分。多设置、自适应协议或参考系统必须先并入同一个有限载体和固定协议，不能直接套用这个单一 instrumentDual 的结论。

### 82.2 稳定深度与终端预测空间

对 trace-zero Hermitian 载体上的一个固定线性 Heisenberg 更新，`centered_effect_stability_depth_bound` 给出更精细的形式：若 $T_n$ 是该固定更新下的中心化效果塔，$T_0$ 的维数为 $r_0$，终端预测空间的维数为 $r_\infty$，则最小一步稳定深度满足

$$
\operatorname{depth}_{\mathrm{stable}}
\le r_\infty-r_0
\le d^2-1-r_0.
$$

一旦某一层满足

$$
T_N=T_{N+1},
$$

该层就等于所有后续层的并空间：

$$
T_N=\bigvee_{n\ge0}T_n.
$$

这把“递归观察最终会不会停”变成了一个可检查的秩条件。它不要求先找到一个无限历史的终点；只要在有限维空间中检测到相邻层维数不再增加，就可以把当前层作为永久稳定候选。这里的深度是固定线性更新的词层数，不是任意物理时间，也不直接适用于未中心化的原始效果塔。

但这条结论仍然相对于一个固定线性更新和一个固定效果族。改变允许设置、引入自适应仪器、增加参考系统，都会改变 $T_n$ 的载体和相应的稳定深度；不能把一个任务的 $d^2-1$ 上界当作所有观察协议的普遍历史长度。

### 82.3 信息完整性也有有限证书

若一个由正 effect 组成、且每个 $1-E$ 也为正的效果族，对所有密度态的原始概率读数是单射的，`finite_informational_effect_certificate` 进一步给出有限子族 $S$，满足

$$
|S|\le d^2-1,
$$

并且其中心化效果已经张成全部 trace-zero Hermitian 空间。原始效果在这个有限子族上的概率读数仍然可以区分所有密度态。

因此“保留多少个历史读数”与“保留多少个线性方向”不是同一个问题。一个无限的候选效果族可能只需要至多 $d^2-1$ 个精心选择的效果作为信息完整证书；但这不意味着任意抽取的 $d^2-1$ 个标签都足够，也不意味着这些效果在物理实验中可以同时、无噪声地获得。

对纯经典的 $D$ 个状态，信息完整记录通常只需区分 $D$ 个中心标签；对完整量子载体，状态空间的实参数维数为 $D^2-1$。这正是第 80 节必须区分中心标签数与块内自由度的原因：Zeckendorf 合法构型数 $F_{L+2}$ 可以是中心标签数，但若每个标签仍带量子块，完整预测证书的规模按块结构而非只按标签数计算。

### 82.4 对 Zeckendorf 合法空间的条件上界

令

$$
D_L=|\mathcal W_L|=F_{L+2},
\qquad
\mathcal H_{Z,L}=\operatorname{span}\{|w\rangle:w\in\mathcal W_L\}.
$$

若明确把 $\mathcal H_{Z,L}$ 作为一个 $D_L$ 维物理 Hilbert 空间，并且所选仪器的 Heisenberg 效果在这个空间上满足完整性前提，那么把 $d=D_L$ 代入上述定理得到条件上界

$$
N_Z\le D_L^2-1
=(F_{L+2})^2-1.
$$

同样，信息完整效果族存在一个至多

$$
(F_{L+2})^2-1
$$

个效果的有限证书。

这只是一个载体维数上界。它没有从 Zeckendorf 递推自动推出实际 Hamiltonian、仪器完备性或实验可达性。若系统只允许某个受限 operator system，或存在块分解

$$
\mathcal A_Z^{\mathrm{block}}
=\bigoplus_w M_{n_w}(\mathbb C),
$$

则可见深度取决于实际 Heisenberg 作用在该空间上的秩增长；不能只把 $F_{L+2}$ 代入 $d$ 而跳过物理载体的构造。

### 82.5 这给“保留多少历史”增加了一个可检验预算

对于给定载体、仪器和目标实验族，可以把历史保留预算拆为

$$
\boxed{
\begin{aligned}
&\text{结构预算：}\quad d^2-1\text{ 个 trace-zero 方向的最坏上界；}\\
&\text{深度预算：}\quad r_\infty-r_0\text{ 个实际秩增量；}\\
&\text{证书预算：}\quad \le d^2-1\text{ 个信息完整效果；}\\
&\text{恢复预算：}\quad \gamma\text{ 谱给出的不可恢复误差下界。}
\end{aligned}}
$$

第一项只由载体维数控制，第二项由具体动力学控制，第三项由任务的读出选择控制，第四项在第 81 节的具体记录模型和迹距离误差定义下由记录耦合与可访问环境控制。它们互相不能替代：较小的中心标签数不会消除块内维数，有限证书也不会保证记录通道可逆，深度稳定更不会自动产生经典吸引子。

所以，对用户最初的命题，一个更严格的有限版本是：在给定 Zeckendorf 合法载体、仪器族、预测视界和恢复访问范围后，保留的历史必须至少支撑任务所需的可见秩、有限证书和恢复误差预算；只有在这些条件同时满足时，才可以把当前层称为稳定的有效经典记录。

本节复用 `finite_sequential_completeness_depth`、`centered_effect_stability_depth_bound` 和 `finite_informational_effect_certificate` 的现有 Lean 结果。将 $d=F_{L+2}$ 代入 Zeckendorf 载体是条件性组合推导，不是仓库已经证明的受约束量子系统构造。

## 追加锚（新终端）

## 83. 多上下文记录的独立预算

### 83.1 一个上下文只能暴露一个有限切面

第 82 节给出了完整量子载体的维数界，但实际记录通常被分成多个上下文：同一系统可以在不同设置、不同基底或不同局部协议下留下不同结果。设上下文集合为有限集 $X$，上下文 $x$ 有 $m_x$ 个结果。去掉单位方向并把结果写成中心化效果后，每个上下文最多提供

$$
\operatorname{independentCount}(x)=m_x-1
$$

个独立结果方向。

这不是说一个上下文的所有结果都没有物理意义；被去掉的最后一个中心化效果由其余效果的和决定。这里计数的是能独立增加状态区分能力的实线性方向，不是 $m_x-1$ 个经典 bit，也不是一个可执行仪器的自动成本。仓库的 `SingleContextVisibleRemainderDimension` 在秩一基底上下文满足 `IsRecordMeasurement` 的条件下给出了相同的几何边界：单个完整基底的概率方向只有 $d-1$ 个独立中心化方向，剩余的 trace-zero Hermitian 方向仍需其他上下文或其他效应补足。

### 83.2 联合信息完整性的下界

`multi_context_budget_lower_bound` 的假设是：每个上下文的中心化效果满足

$$
\sum_{j=1}^{m_x}E_{x,j}=0
$$

（单位方向已剥离；这些 $E_{x,j}$ 不是定理中自动带有正性的 POVM outcome），并且所有上下文的联合读数对密度态是单射的。若输入 Hilbert 空间维数为 $d\ge1$，则定理给出

$$
\boxed{
 d^2-1
 \le
 \sum_{x\in X}(m_x-1).
}
$$

证明的结构很直接：每个上下文删去一个由归一化决定的结果，剩余效果仍必须张成整个 trace-zero Hermitian 空间；该空间的实维数是 $d^2-1$，所以独立效果总数不能更少。这里是必要条件，不是充分条件；达到这个计数并不保证效果彼此独立、正性成立或存在一个可执行的仪器。

对第 78 节的三构型合法空间，如果明确把 $00,01,10$ 构造成一个三维正交 Hilbert 基，并要求多个上下文联合地完整区分任意密度态，则

$$
 d=3,qquad
\sum_x(m_x-1)\ge 8.
$$

若每个上下文只有两个结果，这个必要条件变成至少八个独立二元上下文方向。它不能被误读成“八次测量一定足够”：上下文之间的线性关系、完全正性和实际序列仪器仍需单独验证。

### 83.3 Zeckendorf 长度下的条件预算

若长度为 $L$ 的合法字串空间被明确实现为一个完整物理载体，并且

$$
D_L=|\mathcal W_L|=F_{L+2},
$$

并且所选中心化效果满足逐上下文求和为零、联合读数对该载体上的全部密度态是单射，则联合信息完整的多上下文记录必须满足

$$
\boxed{
(F_{L+2})^2-1
\le
\sum_{x\in X}(m_x-1).
}
$$

这个式子把两种“尺度”接起来：Zeckendorf 递推给出合法构型的载体维数，量子上下文预算则给出分辨其全部密度态所需的独立中心化方向数。它只在合法构型确实成为正交物理基、上下文效果满足归一化、联合读数对所有密度态单射时成立。

若每个 Zeckendorf 标签后面带有量子块，则应将 $D_L$ 替换为实际联合 Hilbert 维数，或改用第 80 节的块代数和所选 operator system 的真实维数。只把 $F_{L+2}$ 当成总维数，会漏掉块内自由度；只把上下文结果数相加，又可能重复计算线性相关的效果。

### 83.4 父记录、上下文专用记录与量子保留

这个下界还揭示三种存储方案的差别。

第一，**上下文专用记录**可以在设置 $x$ 已知后，只保存该上下文的 $m_x-1$ 个独立线性读出方向；这不是说需要 $m_x-1$ 个经典 bit，实际编码成本还取决于读数精度和物理实现。

第二，**共同经典记录**必须在设置尚未揭示时同时支持所有上下文的联合读数。这是额外的 parent-record 问题，不能由本节的线性计数下界单独推出父 POVM 不可能；第 78 节的 $X/Z$ 二元模型才给出了一个具体的完全精确父 POVM no-go。计数下界只说明联合完整读数所需的独立中心化方向不能凭空消失。

第三，**保留量子载体**不必预先把所有上下文结果写成经典标签，而是保留足够的量子自由度，在设置揭示后再选择测量。这样可以避免把不相容结果同时写入一个经典表格，但其物理成本转移为保存 Hilbert 空间、控制相互作用和限制环境回流。

因此，“保留多少历史”必须先说明设置何时揭示：

$$
\begin{aligned}
&\text{设置先揭示：}\quad\text{可以使用上下文专用记录；}\\
&\text{设置后揭示：}\quad\text{需要共同父记录，或保留量子载体；}\\
&\text{允许有限误差：}\quad\text{需要把上下文缺陷和读出距离纳入预算。}
\end{aligned}
$$

多上下文预算不推翻第 80 节关于中心和块的区分，也不替代第 81 节的恢复误差下界。它补充的是另一项必要条件：即使没有任何隐藏回流，联合完整记录本身也需要足够多的独立中心化方向。若任务只预测一个受限 observable system，而不是区分全部密度态，则应改用该任务空间的维数，不能直接套用 $d^2-1$ 的全 tomography 下界。

本节复用 `multi_context_budget_lower_bound` 和 `single_context_visible_remainder_dimension` 的现有结果。将 $d=F_{L+2}$ 代入得到的 Zeckendorf 预算是条件性组合推导；共同父 POVM 的精确不可能性仍由第 78 节的具体二元模型承担，不把计数下界冒充为一般 no-go 定理。

## 84. 互补上下文怎样补齐剩余方向

### 84.1 从预算下界到正交补齐

第 83 节只给出了联合记录必须拥有多少个独立中心化方向的必要条件。现有的 `CompleteContextTomography` 与 `MutuallyUnbiasedDiagonalPlanes` 还给出一个更有结构的条件性实现：如果一个 $d$ 维物理载体存在 $d+1$ 个秩一上下文，并且任意两个不同上下文满足

$$
\operatorname{Tr}(P_{x,j}P_{y,k})=\frac1d
\qquad(x\ne y),
$$

并且再加上一个载体识别条件：每个上下文的中心化对角平面确实等同于其 $d$ 维 trace-zero 对角载体。记第 $x$ 个平面为 $\mathsf P_x$，则在这个附加条件下，每个平面有 $d-1$ 个独立方向，而且不同上下文的这些平面彼此正交：

$$
\dim \mathsf P_x=d-1,
$$

$$
\mathsf P_x\perp\mathsf P_y\quad(x\ne y),
$$

从而

$$
\dim\Bigl(\bigoplus_{x=0}^{d}\mathsf P_x\Bigr)
=(d+1)(d-1)=d^2-1.
$$

右端正好是 trace-zero Hermitian 方向的维数。因此，在这些重叠条件和完整物理载体假设下，第 83 节的必要预算被恰好填满：单位方向由归一化提供，$d^2-1$ 个中心化方向由 $d+1$ 个互补上下文提供。

这里的逻辑方向必须保持清楚。仓库定理证明的是：**给定**这些上下文和重叠假设，就能得到唯一分解、无共同不可见 trace-zero 残差，以及由所有上下文概率确定 Hermitian trace-one 矩阵。它没有证明任意维数都存在这样的物理仪器，也没有把一组形式上的 `RankOneContext` 自动解释成实验室中可实现的 POVM。

### 84.2 互补不是额外标签，而是剩余空间的几何补偿

一个上下文的去相位通道可以写成

$$
\mathcal D_x(X)=\sum_j\operatorname{Tr}(P_{x,j}X)P_{x,j}.
$$

它把 $X$ 保留在第 $x$ 个对角平面和单位方向上，而把与该平面正交的方向压到当前读数不可见。若 $x\ne y$ 的两个上下文互补，则现有定理给出，对 Hermitian $X$：

$$
\mathcal D_x\mathcal D_y(X)
=\frac{\operatorname{Tr}(X)}{d}I,
$$

以及交换次序后的同样等式。特别地，对 trace-zero 部分 $X_0$ 有

$$
\mathcal D_x\mathcal D_y(X_0)=0.
$$

这不是说第二次观测把整体量子信息从宇宙中删除；它说的是：在只保留第一次和第二次去相位之后的系统边缘记录时，两个互补切面连续作用会把 trace-zero 方向都压到单位方向，当前这组经典记录看不到原来的方向。若环境或记录寄存器仍可访问，联合系统可以保留更多信息；因此“消失”必须带有访问范围的下标。

这也说明为什么“上下文数量”不能直接等同于“历史长度”。两个上下文可以提供互相正交的新方向，也可以在连续去相位协议中抹掉此前可见的方向。真正的资源是记录代数中保留下来的独立方向和仍可访问的联合关联。

### 84.3 三种协议的区别

设设置变量为 $x$，系统状态为 $\rho$。

**上下文先揭示。** 若 $x$ 在相互作用前已知，可以只实施 $\mathcal D_x$，并保存该上下文的 $d-1$ 个独立中心化读数。对于只预测该上下文后续响应的任务，这可以是足够的有效记录；它不承诺对未选择的上下文仍然可回答。

**设置后揭示。** 若 $x$ 在记录之后才揭示，则一份共同的经典记录必须同时支撑各个 $\mathcal D_x$ 的统计预测。这是共同父记录问题。第 84.1 节的正交分解说明在完整量子载体上怎样用多上下文效果补齐信息，但它不构造一个预先写好所有不相容答案的经典表，也不由维数等式单独推出共同父 POVM 的存在或不存在。

**延迟测量。** 若设置尚未揭示而又不要求立即产生经典标签，可以保留 $\rho$ 或一个足够大的联合量子载体，待 $x$ 确定后再实施相应测量。代价转移为保存载体、抑制环境回流并控制联合演化；收益是没有把不相容上下文强行压缩成同一份经典记录。

因此，“保留多少历史”的答案依赖设置揭示顺序：

$$
\begin{array}{c|c|c}
\text{设置时序}&\text{可保留结构}&\text{主要约束}\\
\hline
\text{先揭示}&\text{上下文专用经典记录}&d-1\text{ 个中心化方向}\\
\text{后揭示}&\text{共同父记录或量子载体}&\text{上下文兼容性与联合访问}\\
\text{允许延迟}&\text{未去相位的量子关联}&\text{载体保存与环境回流}
\end{array}
$$

### 84.4 Zeckendorf 合法空间的两个小模型

取禁止相邻 `11` 的合法空间 $\mathcal H_{Z,L}$，并明确假设每个合法字串对应一个正交物理基态。

当 $L=2$ 时，合法构型为

$$
\mathcal W_2=\{00,01,10\},
\qquad d=|\mathcal W_2|=F_4=3.
$$

若要在这个三维载体上做完整态层析，$d+1=4$ 个互补三结果上下文每个提供 $d-1=2$ 个中心化方向，总数为

$$
4\times2=8=3^2-1.
$$

这与第 78 节的三构型模型相容：一个上下文只能看到二维的概率差，另外六个 trace-zero 方向必须由其他设置补足。这里的“四个上下文”是满足互补重叠假设时的条件性层析设计，不是声称仓库已经为该 Zeckendorf 模型构造了具体实验 Hamiltonian。

当 $L=3$ 时，合法构型为

$$
\mathcal W_3=\{000,001,010,100,101\},
\qquad d=|\mathcal W_3|=F_5=5.
$$

相应的完整互补上下文条件需要 $d+1=6$ 个五结果上下文，每个有 $4$ 个独立中心化方向，总预算为

$$
6\times4=24=5^2-1.
$$

Zeckendorf 在这里提供的是合法载体和离散索引；它没有决定这六个上下文的投影矩阵、相互作用角度或记录噪声。若实际系统只允许其中一部分局部效果，预算应改用可达 operator system 的真实维数，不能继续套用 $d^2-1$。

### 84.5 对“稳定经典现实”的进一步限制

互补上下文的正交补齐给出的是**信息完整性**，不是**经典吸引性**。即使

$$
\bigoplus_x\mathsf P_x
=\operatorname{Herm}_0,
$$

仍需另外检查记录通道的非对角 Gram 系数是否满足严格收缩、隐藏关联是否会回流，以及当前保留结构是否对目标演化近似闭合。信息完整意味着“有一组上下文能够区分载体上的状态”；它不意味着一次记录后所有相干都会衰减，也不意味着不同记录会自动形成共同的经典父变量。

因此当前研究对象可以写成三层条件的交集：

$$
\boxed{
\begin{aligned}
&\text{几何完整：}&\quad&\sum_x\mathsf P_x=\operatorname{Herm}_0,\\
&\text{动力学闭合：}&\quad&\mathcal E\Phi\approx\mathcal E\Phi\mathcal E,\\
&\text{记录吸引：}&\quad&|R_{ij}|<1\text{（对需要经典化的关系）}.
\end{aligned}}
$$

第一条回答“哪些上下文合起来足以测量”；第二条回答“丢掉的差异会不会在未来返回”；第三条回答“被记录的相干是否真的衰减”。只有把三条分别验证，才有资格把某个有限层次称为稳定的有效经典现实。

本节直接复用 `complete_context_tomography` 与 `mutually_unbiased_diagonal_planes` 的现有条件性结果。$L=2,3$ 的 Zeckendorf 计数、正交平面维数相加以及三种协议的区分是组合推导；共同父 POVM 的一般存在性、具体 Zeckendorf Hamiltonian 和实验噪声模型仍保持开放。

## 85. 完备上下文的纯度证书与经典化边界

### 85.1 互补记录可以测出纯度，但纯度不是状态本身

在第 84 节的完整互补上下文假设下，仓库已有 `complete_context_purity_identities`。令

$$
p_{l,j}=\operatorname{Tr}(\rho P_{l,j}),
\qquad d=\dim\mathcal H,
$$

并假设 $\rho$ 是正半定且迹为一。该恒等式给出

$$
\boxed{
\sum_{l=0}^{d}\sum_{j=0}^{d-1}
\left(p_{l,j}-\frac1d\right)^2
=\operatorname{Tr}(\rho^2)-\frac1d.
}
$$

等价地，所有上下文概率平方和满足

$$
\boxed{
\sum_{l=0}^{d}\sum_{j=0}^{d-1}p_{l,j}^2
=1+\operatorname{Tr}(\rho^2).
}
$$

因此，完备互补记录不仅能在原则上重建状态，还能把纯度写成一个直接的记录能量。最大混合态的中心化能量为零；纯态的中心化能量为 $1-1/d$。

但纯度只是一个标量不变量。不同的密度态可以拥有相同的 $\operatorname{Tr}(\rho^2)$，所以这两条恒等式本身不能替代第 84 节的全状态层析，也不能把“纯度已经测出”说成“历史已经唯一恢复”。它们提供的是一个低成本的完整性检查：若重建的概率不满足该恒等式，记录、归一化、正性或上下文重叠假设至少有一项不相容。

### 85.2 Zeckendorf 小载体上的数值刻度

在 $L=2$ 的三构型载体中，$d=F_4=3$。若状态为纯态，则

$$
\sum_{l,j}\left(p_{l,j}-\frac13\right)^2=\frac23;
$$

若状态为最大混合态，则该和为零。在 $L=3$ 的五构型载体中，$d=F_5=5$，相应的纯态值为

$$
\sum_{l,j}\left(p_{l,j}-\frac15\right)^2=\frac45.
$$

这些数值只使用合法构型数作为明确的 Hilbert 维数，并把互补上下文假设作为输入。Zeckendorf 权重本身不决定纯度；它只决定被记录的离散基态如何编号。

若实际系统只实现受限的 observable system，平方和应改成该系统内的投影能量，并重新证明相应恒等式。不能把全空间公式直接套到缺失上下文或带量子块的模型。

### 85.3 纯度证书不能替代动力学闭合

纯度证书回答的是“当前记录是否携带了足够的二次信息来检验一个状态不变量”。它不回答：

$$
\mathcal E\Phi=\mathcal E\Phi\mathcal E
$$

是否成立，也不回答非对角 Gram 系数是否严格小于一。一个过程可以保持纯度而在不同上下文之间相干旋转；也可以在记录后纯度下降，却因隐藏记录仍可访问而保持整体可逆。

因此，在当前研究主线上，至少要分开三种证书：

$$
\begin{aligned}
&\text{层析证书：}&\quad&\{p_{l,j}\}\text{ 是否唯一确定目标载体上的状态；}\\
&\text{纯度证书：}&\quad&\sum_{l,j}(p_{l,j}-1/d)^2\text{ 是否与 }\operatorname{Tr}(\rho^2)-1/d\text{ 一致；}\\
&\text{动力学证书：}&\quad&\mathcal E\Phi\approx\mathcal E\Phi\mathcal E\text{ 且隐藏回流误差是否受控。}
\end{aligned}
$$

只有第一项和第二项成立时，我们得到的是“可测且可校验的当前状态”；加入第三项后，才得到“在指定预测视界内可作为有效对象使用的记录”。这正是“稳定经典现实”不能由单一观测次数或单一纯度数值定义的原因。

本节复用 `complete_context_purity_identities` 的现有条件性结果。$L=2,3$ 的数值代入和三类证书的区分是组合解释；有限精度下的统计置信区间、缺失上下文时的残差界以及带量子块载体的纯度分解仍是开放接口。

## 86. 目标相对的记录充分性与未来残差

### 86.1 记录预算应按目标算，而不是按全部状态算

设当前记录效果为 $E_i$，把单位方向一并保留，定义可见算子空间

$$
\mathcal V
=\operatorname{span}_{\mathbb R}\{I,E_i:i\in\mathcal I\}.
$$

冻结定理 `target_prediction_sufficiency` 给出一个严格的二分。

若目标 observable $A$ 满足

$$
A\in\mathcal V,
$$

那么任何两个当前记录相同的物理态，对 $A$ 的期望值也相同。换言之，若任务只要求预测 $\mathcal V$ 内的目标，当前记录已经对该目标充分；不需要为了一个目标自动保存完整 $d^2-1$ 个 trace-zero 方向。

若

$$
A\notin\mathcal V,
$$

定理构造一个非零的 trace-zero Hermitian 残差 $D\in\mathcal V^\perp$，以及足够小的 $\varepsilon>0$，使

$$
\rho_\pm=\frac1dI\pm\varepsilon D
$$

仍是物理密度态。它们满足所有当前效果的读数相同，但

$$
\operatorname{Tr}(D A)\ne0,
$$

因而对目标 $A$ 的期望不同。当前记录对该目标不充分，不是因为缺少更精细的标签，而是因为目标方向落在可见算子空间之外。

这把第 83 节的全 tomography 预算收紧成任务相对的版本：

$$
\boxed{
\text{所需历史}\\
\text{由目标族在可见算子空间中的覆盖决定。}
}
$$

若目标族是所有 Hermitian observable，才需要把 $\mathcal V$ 扩展到完整载体；若目标族只包含 Zeckendorf 数值和若干局部模式，则可以只扩展到这些目标生成的子空间。

### 86.2 Zeckendorf 数值是一个目标，不是完整状态

在 $L=2$ 的合法基底

$$
\{00,01,10\}
$$

上，按权重 $(2,1)$ 定义 Zeckendorf 数值 observable

$$
A_Z=0|00\rangle\langle00|
 +1|01\rangle\langle01|
 +2|10\rangle\langle10|.
$$

如果当前记录效果的实线性张成包含 $I$ 与 $A_Z$，那么记录相同的两个态必然拥有相同的 Zeckendorf 数值期望。这个结论只涉及一个目标方向；它不推出两态对非对角相位、其他上下文或未来 Hamiltonian 的响应相同。

若后续动力学把 $A_Z$ 的 Heisenberg 回拉带到新的方向 $U^\dagger A_ZU$，则记录预算必须扩大到这些回拉方向的张成空间。于是“保留一个 Zeckendorf 数”只对当前目标成立；要预测一族后续实验，必须把该实验族的目标闭包纳入 $\mathcal V$。

### 86.3 未来误差是两个残差的相关

对一个有限效果塔，令 $\mathcal V_m$ 为当前深度可见的 trace-zero 空间，$\mathcal R_m=\mathcal V_m^\perp$ 为隐藏残差空间。对密度态 $\rho$，记其中心化 trace-zero 坐标为 $s_\rho$；未来效果 $F$ 也指 Heisenberg 回拉得到的中心化 Hermitian 方向。`future_probability_residual_correlation` 给出：以可见投影构造线性预测代表后，预测误差满足

$$
\boxed{
\operatorname{error}
=\left\langle
\Pi_{\mathcal R_m}(s_\rho),
\Pi_{\mathcal R_m}(F)
\right\rangle,
}
$$

并有 Cauchy--Schwarz 界

$$
|\operatorname{error}|
\le
\sqrt{\operatorname{residualMass}(\mathcal V_m,s_\rho)}
\,\left\|\Pi_{\mathcal R_m}(F)\right\|.
$$

因此未来误差不是一个只由“隐藏维数”决定的常数。它同时取决于两件事：当前状态在隐藏方向上有多少分量，以及未来目标本身有多少分量会探测这些方向。隐藏空间很大但目标完全正交时，误差仍可为零；隐藏空间很小但未来目标正好对准它时，误差可以达到该界的量级。

同一个隐藏残差还控制压缩动力学本身的不自然性。若环境动力学在 trace-zero 载体上是 $L$-Lipschitz，`residual_controls_naturality` 给出

$$
\Delta_m(X)
\le L\,\left\|\Pi_{\mathcal R_m}X\right\|,
$$

其中 $\Delta_m$ 是“先完整演化再投影”和“先投影再演化”的距离差。在密度态的中心化坐标上，进一步有

$$
\Delta_m(s_\rho)\le L\sqrt{\operatorname{residualMass}(\mathcal V_m,s_\rho)}.
$$

所以同一个 $\sqrt{M_m}$ 同时出现在未来观测误差和动力学压缩缺陷的上界中；前者还乘以未来目标的残差敏感度，后者还乘以动力学的 Lipschitz 常数。两者是共同受残差控制的两个不同量，不是同一个误差的恒等改写。

这个定理还包含一个必要警告：把状态的可见投影加回单位部分得到的线性预测代表，未必是正半定矩阵。因此“用当前记录预测未来”首先是一个 observable 期望的线性近似，不能自动解释成一个新的物理密度态。若需要物理态级别的预测，必须另加正性、完全正性或误差通道的证明。

### 86.4 历史保留的目标闭包判据

设目标族为 $\mathfrak A$，允许的 Heisenberg 更新为 $\mathfrak U$。一个有限记录空间 $\mathcal V$ 对任务足够的必要条件是

$$
\operatorname{span}\{U^\dagger A U:
A\in\mathfrak A,\ U\in\langle\mathfrak U\rangle\}
\subseteq\mathcal V,
$$

其中右侧也应包含单位方向。若该包含关系成立，目标闭包中的每个未来期望都由当前签名决定；若失败，`target_prediction_sufficiency` 的残差构造给出一对当前不可区分、未来可区分的物理态。

这提供了一个比“保留多少历史”更精确的工作流程：先列出任务目标和允许的后续操作，再计算它们的有限线性闭包，最后只保留能覆盖该闭包的记录方向。Zeckendorf 合法构型给出初始离散坐标；真正决定历史成本的是目标闭包的秩和隐藏残差与未来目标的相关。

本节复用 `target_prediction_sufficiency`、`future_probability_residual_correlation` 和 `residual_controls_naturality` 的现有结果。$A_Z$ 的有限 Zeckendorf 构造、目标闭包的物理可达性，以及把线性误差界提升为完整通道距离，仍是条件性组合推导或开放接口。

## 87. 一次经典记录能保存多少个可完美区分的历史

### 87.1 完美区分数受载体维数限制

第 86 节讨论的是目标 observable 的线性覆盖；现在考虑更强的任务：用同一个 POVM 一次性、无误差地识别一组历史状态。设记忆 Hilbert 空间维数为 $d$，候选密度态为 $\rho_i$，记录效果为 $E_j$，满足

$$
E_j\succeq0,
\qquad
\sum_jE_j=I,
$$

并要求完美配对

$$
\operatorname{Tr}(E_j\rho_i)=\delta_{ij}.
$$

冻结定理 `finite_memory_history_capacity` 证明：若这些条件成立，候选历史数 $N$ 必须满足

$$
\boxed{N\le d.}
$$

证明的几何核心是：每个 $\rho_i$ 的支撑落在 $E_i$ 的单位特征子空间中，并与其他效果的支撑正交；因此从每个非零密度态中选出的向量构成一组两两正交的记忆向量，数量不能超过 Hilbert 维数。

这条界与第 82、83 节的 $d^2-1$ 方向预算承担不同任务：

$$
\begin{aligned}
&d^2-1 &&\text{控制连续量子状态的 trace-zero 参数方向；}\\
&d &&\text{控制同一 POVM 一次可完美区分的经典历史标签数。}
\end{aligned}
$$

一个 $d$ 维系统可以有 $d^2-1$ 个连续可观测方向，却不能用一次固定经典读出去完美区分超过 $d$ 个任意历史状态。把这两个数字混为同一个“记忆容量”会错误估算所需约束。

### 87.2 Zeckendorf 合法载体的容量读法

若长度为 $L$ 的禁止相邻 `11` 合法空间确实实现为一个完整正交载体，则

$$
d=D_L=F_{L+2}.
$$

在同一个一次性 POVM 下，完美可区分历史数满足

$$
\boxed{N\le F_{L+2}.}
$$

所以：

$$
L=2\Rightarrow N\le F_4=3,
\qquad
L=3\Rightarrow N\le F_5=5.
$$

这里的 $N$ 是可完美区分的密度态或记录历史数，不是合法字符串总数以外的额外物理自由度；它也不是可重建任意密度态所需的 $d^2-1$ 个概率方向。若每个 Zeckendorf 标签后面带有量子块，必须将 $d$ 换成实际联合 Hilbert 维数；仅用标签数量代入会低估一次性记录容量的需求。

### 87.3 超过容量时，历史必须改变形态

当候选历史数满足

$$
N>d,
$$

同一个记忆载体和同一个 POVM 不可能同时实现上述 Kronecker 配对。要继续区分这些历史，至少需要改变一个条件：

$$
\begin{aligned}
&\text{增加载体维数；}\\
&\text{使用多个设置或多轮记录；}\\
&\text{保留联合量子关联而延迟最终读出；}\\
&\text{放宽为近似区分，并给出统计误差界。}
\end{aligned}
$$

这不是说超过 $d$ 个历史就不能被任何实验区分。多轮协议可以把历史编码到更大的联合载体，多个上下文可以在可重复制备上完成层析，延迟测量可以保留不相容设置所需的相位。定理只限制“同一个有限记忆、同一个一次性完美 POVM”的协议。

因此，稳定经典记录的历史成本至少有两种不同读法：若目标只是当前一次的无误标签，容量受 $d$ 限制；若目标是未来任意上下文的连续预测，成本由第 86 节的目标闭包和残差半径决定。增加标签数量不能替代增加可访问的量子载体或保留历史关联。

本节复用 `finite_memory_history_capacity` 的现有结果。将 $d=F_{L+2}$ 代入是条件性 Zeckendorf 载体解释；近似区分、重复实验的总容量、带记忆环境的联合编码和块结构载体仍需分别建模。


## 88. 观测细化中的容量—残差守恒

### 88.1 可见容量与不可见残差

设记忆载体为 $d$ 维 Hilbert 空间，当前效果集合为 $\mathcal E$。把单位效果也纳入后，定义

$$
\mathcal V(\mathcal E)
=
\operatorname{span}_{\mathbb R}
\bigl(\{I\}\cup\mathcal E\bigr),
$$

并令

$$
C(\mathcal E)
=
\dim_{\mathbb R}\mathcal V(\mathcal E)-1,
\qquad
R(\mathcal E)
=
\dim_{\mathbb R}\mathcal V(\mathcal E)^\perp.
$$

现有定理 observer_capacity_conservation 给出

$$
\boxed{
C(\mathcal E)+R(\mathcal E)=d^2-1.
}
$$

这里的 $d^2-1$ 是完整 trace-zero Hermitian 载体的总方向数，不是历史条数或 POVM outcome 数。若粗效果集满足

$$
\mathcal E_{\mathrm{coarse}}
\subseteq
\mathcal E_{\mathrm{fine}},
$$

则

$$
C(\mathcal E_{\mathrm{coarse}})
\le
C(\mathcal E_{\mathrm{fine}}),
\qquad
R(\mathcal E_{\mathrm{fine}})
\le
R(\mathcal E_{\mathrm{coarse}}).
$$

因此细化记录只把原先不可见的方向转移到当前可见空间；线性相关的新增标签不会增加容量。

### 88.2 Zeckendorf 载体上的预算

若长度为 $L$ 的禁止相邻 11 合法空间明确实现为完整正交载体，则

$$
d=F_{L+2},
\qquad
C(\mathcal E)+R(\mathcal E)
=
(F_{L+2})^2-1.
$$

所以

$$
L=2:\quad C+R=8,
\qquad
L=3:\quad C+R=24.
$$

这与第 87 节的

$$
N\le F_{L+2}
$$

是不同容量：前者计算连续 Hermitian 方向，后者计算一次固定 POVM 可完美区分的离散历史态数。若合法构型后面带有量子块，或仪器只作用在受限 operator system 上，必须使用实际载体或任务空间的维数，不能只按 Zeckendorf 标签数代入。

### 88.3 细化不制造总信息

若某个差异仍位于

$$
\mathcal V(\mathcal E_{\mathrm{fine}})^\perp,
$$

则当前效果族仍无法区分它。要让它进入后续预测，必须加入能与之配对的效果，或让动力学把它旋转进可见空间。这把“保留更多历史”改写成一个线性选择问题：寻找能降低 $R(\mathcal E)$、并覆盖目标闭包的独立效果，而不是盲目保存更多原始词。

精确维数守恒不等于近似预测误差已经足够小。残差维数为零时才得到完整线性可见性；残差非零时，误差仍由第 86 节的状态残差与未来目标残差相关界控制：

$$
|\operatorname{error}|
\le
\sqrt{\operatorname{residualMass}}
\,
\|\text{未来目标的残差分量}\|.
$$

反过来，残差维数很大也不必然造成当前任务误差，因为当前状态或目标可能在这些方向上的投影为零。因此稳定经典记录至少需要同时报告可见容量、残差容量和目标敏感度。

本节复用 observer_capacity_conservation 的现有结果。将 $d=F_{L+2}$ 代入以及与第 86 节误差界的组合是条件性理论桥；近似容量、噪声成本和具体 Zeckendorf 物理仪器仍保持开放。

## 追加锚（新终端）

## 89. 记录关联、熵增与可恢复历史

### 89.1 预测量把相干搬到联合系统，而不是把它直接抹掉

设系统的密度态为 $\rho$，记录自由度起初为空白。项目中的 `coherentCopyState` 给出一个有限维的理想预测量模型：输入矩阵的每个条目被放置在相关基底向量之间，特别是

$$
\bigl(\operatorname{coherentCopyState}(\rho)\bigr)_{(i,i),(j,j)}
=
\rho_{ij}.
$$

因此，联合态仍然保留原来的非对角条目。若只看其中一边，另一边被偏迹掉，则两个边缘态都变成同一个基底去相位态：

$$
\rho_S
=
\rho_E
=
\operatorname{basisPinchingState}(\rho).
$$

这给“历史消失”一个更严格的解释：

> 对局部访问而言，非对角历史不再出现在边缘矩阵中；对整体联合态而言，它仍可能保存在系统—记录关联的相关条目里。

项目还证明相干复制是等距扩张，联合态的 von Neumann 熵保持不变：

$$
S\!\left(\operatorname{coherentCopyState}(\rho)\right)=S(\rho).
$$

所以这里没有把一个可逆的整体过程直接等同为无条件的热力学熵增。增加的是局部可见的经典记录以及系统与记录之间的相关，而不是由这条等距复制定理单独推出的总熵增加。

### 89.2 关联的“成本”由记录熵和相干删除项共同组成

对同一个联合态，项目中的 `coherent_copy_correlation_tax` 给出精确分解：

$$
\boxed{
I(S:E)
=
S\!\left(\operatorname{basisPinchingState}(\rho)\right)
+D\!\left(
\rho\middle\|\operatorname{basisPinchingState}(\rho)
\right).
}
$$

右侧第一项是去相位后保留下来的记录熵；第二项是原态相对于去相位态的量子相对熵。对本节这个基底去相位特例，若采用相对熵非负这一有限维性质，则系统—记录互信息至少包含记录边缘的熵，并且还包含一项由原始相干与局部经典化之间的差异贡献的项。这里的非负性不是 `coherent_copy_correlation_tax` 等式本身额外返回的独立结论；重复协议的公开定理在第 89.4 节明确给出相应每步项的非负性。

这里的“成本”是信息论分解中的成本，不能直接改写成实验室中的热量、功或不可逆熵产生。要作热力学解释，还需要指定温度、能量、环境初态和实际耗散通道。当前定理只处理有限维密度矩阵、偏迹、基底去相位和相对熵。

这一区分也修正了一个容易混淆的说法：

$$
\text{局部读数变得经典}
\not\Rightarrow
\text{整体信息已经销毁}.
$$

在联合描述中，关联承担了原先由局部非对角项承担的部分信息；只有当记录自由度不可访问、被进一步偏迹，或者动力学把这些关联真正带出允许的联合操作范围时，才可以在给定任务上把它视为不可恢复。

### 89.3 可恢复性取决于访问范围，而不是只取决于边缘读数

`CanonicalRecordAccessRecovery` 提供了一个二能级的具体边界。取两个状态 $\rho$ 和 $\sigma$，假设它们在选定基底上的对角元完全相同，但存在某个非对角元不同：

$$
\forall i,\ \rho_{ii}=\sigma_{ii},
\qquad
\exists i\ne j,\ \rho_{ij}\ne\sigma_{ij}.
$$

一个可逆受控耦合可以把两者写成不同的联合记录态；对记录做偏迹后，两者得到相同的局部约化态，因此不存在一个只接受该约化态、就能同时恢复两个联合记录的函数。可是，如果仍能访问记录，并施加该耦合的伴随操作，则两个联合态都可以恢复到各自的空白记录输入。

这说明“不可恢复”必须带有访问限定：

$$
\text{不可由当前边缘恢复}
\ne
\text{在整个联合系统中不可逆}.
$$

对稳定经典现实的研究，因而不能只问“相干是否变成零”，还必须问：允许的后续操作是否包括记录寄存器、环境的某个子系统或联合控制？改变可访问范围，会改变哪些历史仍然能够影响未来。

### 89.4 反复记录时，熵增是每一步相对熵的和

考虑一个固定的幺正矩阵 $U$，以及满足

$$
\rho_{k+1}
=
\operatorname{basisPinchingState}
\left(U\rho_kU^\dagger\right)
$$

的离散协议。项目中的 `entropy_production_coherence_deletion_identity` 证明每一步的熵差为

$$
\boxed{
S(\rho_{k+1})-S(\rho_k)
=
D\!\left(
U\rho_kU^\dagger
\middle\|
\operatorname{basisPinchingState}(U\rho_kU^\dagger)
\right)
\ge 0.
}
$$

并且对任意 $N$ 有望远镜求和：

$$
\boxed{
S(\rho_N)-S(\rho_0)
=
\sum_{k=0}^{N-1}
D\!\left(
U\rho_kU^\dagger
\middle\|
\operatorname{basisPinchingState}(U\rho_kU^\dagger)
\right).
}
$$

这里的非负性来自每一步去相位相对于幺正演化后状态的量子相对熵；幺正共轭本身保持 von Neumann 熵。于是，重复记录协议中的可见熵增加可以逐步结算为“本轮被删除的相干”之和。

这条公式同时给出一个停止条件：如果某一步的相对熵项为零，则该步的幺正后状态已经位于所选基底的去相位固定点；若所有后续步骤都保持这一条件，记录熵不再增加。反过来，固定点集合是经典对角态并不保证任意初态都会到达它；还需检查实际动力学是否持续把非对角分量送入被去相位的方向。

### 89.5 Zeckendorf 只提供合法索引，不决定关联与熵

若把长度为 $L$ 的禁止相邻 `11` 合法串作为构型标签，并令

$$
d=F_{L+2},
$$

则可以把这些标签映射到一个 $d$ 维正交载体，再在其上定义 $\rho$、$U$、基底去相位和记录寄存器。此时第 88 节的容量守恒给出

$$
C(\mathcal E)+R(\mathcal E)=d^2-1=(F_{L+2})^2-1.
$$

但本节的互信息、相对熵和熵产生公式还需要额外指定：

$$
\text{构型到 Hilbert 基底的映射},
\quad
\text{记录耦合},
\quad
\text{幺正动力学},
\quad
\text{去相位基底}.
$$

Zeckendorf 权重本身不决定 $U$，也不决定记录 Gram 矩阵、互信息或相对熵。它只说明哪些有限构型作为离散载体是合法的，以及如何给这些构型提供规范编号。若更换局部约束，合法载体维数和适合的索引递推也会改变；若保留同一标签而更换记录耦合，关联谱和熵变化同样会改变。

因此，对“保留多少历史才能得到稳定经典现实”的当前回答应写成：

$$
\boxed{
\begin{aligned}
&\text{整体层：保留联合态中的记录关联；}\\
&\text{局部层：只保留给定任务可访问的边缘记录；}\\
&\text{动力学层：结算每一步相对熵和未来回流；}\\
&\text{编码层：用 Zeckendorf 组织合法构型，但不把编码当作动力学。}
\end{aligned}}
$$

“历史消失”于是被拆成三个可检验问题：边缘是否已经去相位、联合关联是否仍可访问、以及允许的后续操作是否能把关联重新转回目标读数。只有在指定实验族、访问范围和误差容限下，这三个问题都给出稳定答案时，才可以把该层记录称为有效的经典现实。

本节复用 `coherentCopyState_correlated_entry`、`marginalRight_coherentCopyState`、`marginalLeft_coherentCopyState`、`vonNeumannEntropy_coherentCopyState`、`coherent_copy_correlation_tax` 和 `entropy_production_coherence_deletion_identity`。关于“相对熵就是实际热力学熵产生”、任意 Zeckendorf 物理实现、无限环境中的恢复能力，以及对所有未来实验的经典闭合，仍需额外模型与证明；本节不把这些条件性组合推导冒充为仓库已有结论。

## 追加锚（新终端）

## 90. 记录重叠、可区分性与复制边界

### 90.1 记录重叠给出一条精确的可见性预算

设两个归一化纯记录为 $|r_0\rangle$ 和 $|r_1\rangle$，令

$$
c=\langle r_0|r_1\rangle,
\qquad
V=|c|,
\qquad
D=\sqrt{1-V^2}.
$$

项目中的 `pure_record_distinguishability_coherence_complementarity` 证明：

$$
\boxed{D^2+V^2=1.}
$$

这里的 $V$ 是两条记录之间仍保留的相干可见度；$D$ 是由这两个记录向量的重叠所定义的几何区分度。它们不是两个可以独立增加的预算：在记录向量已经归一化的条件下，提高一个就必然降低另一个。

两个端点尤其清楚：

$$
\begin{aligned}
&c=0
&&\Longrightarrow
&&D=1,\quad V=0;\\
&V=1
&&\Longrightarrow
&&D=0.
\end{aligned}
$$

第一种情形是正交记录；在允许相应投影测量时，它们可以完全区分。第二种情形在归一化向量的标准 Hilbert 空间几何中对应同一条量子态射线，只留下整体相位约定，不能提供区分信息。这里形式化结果直接保证的是 $V=1$ 时几何区分度为零。若 $D=1$，则 $c=0$，任何后续振幅乘上 $c$ 都被消除；若 $V=1$，几何区分度为零。

这把第 89 节的关联公式进一步具体化：记录 Gram 矩阵中的非对角元就是这种重叠。对每一对候选历史，$|R_{ij}|$ 越接近零，局部记录越能把它们分开；$|R_{ij}|$ 越接近一，越多相干仍可在联合演化中保留。不能只报告记录的数量，还要报告记录向量之间的重叠谱。

### 90.2 完美复制只适用于正交或相同的历史

设 $U$ 是同一 Hilbert 空间张量平方上的复线性等距等价，并设三个向量都归一化：输入历史为 $\psi,\phi$，空白记录为 $b$。若同一个 $U$ 满足

$$
U(\psi\otimes b)=\psi\otimes\psi,
\qquad
U(\phi\otimes b)=\phi\otimes\phi,
$$

则 `no_cloning_inner_product_criterion` 给出

$$
\langle\phi|\psi\rangle
=
\langle\phi|\psi\rangle^2.
$$

因此

$$
\boxed{
\phi=\psi
\quad\text{或}\quad
\langle\phi|\psi\rangle=0.
}
$$

证明的核心只是等距映射保持内积，而张量积把重叠相乘。这个结果的适用范围必须保留：它针对同一个线性等距复制过程、同一个归一化空白记录和两个精确复制方程。它不是说任何形式的近似记录、带噪声记录或任务相关压缩都不可能。

对历史档案而言，结论是：任意两个非正交量子历史不能被一个固定的可逆过程无损复制成两份独立副本。若试图把每个历史都写入新的独立记录，就必须满足记录态之间的正交条件，或接受近似误差、改变任务、保留联合关联而不宣称已经产生两份副本。

### 90.3 Zeckendorf 标签可以复制，标签上的任意叠加不能任意复制

若长度为 $L$ 的合法 Zeckendorf 字符串被实现为一组正交计算基态

$$
\{|w\rangle:w\in\mathcal W_L\},
$$

则对不同 $w\ne v$ 有

$$
\langle w|v\rangle=0.
$$

在这个离散基底上，受控复制可以把经典标签写入空白寄存器；这与第 90.2 节并不冲突，因为被复制的是一组彼此正交的基态。可是，对叠加态

$$
|\Psi\rangle=\sum_{w\in\mathcal W_L}a_w|w\rangle
$$

不能把同一个过程解释为对任意未知 $|\Psi\rangle$ 都实现

$$
|\Psi\rangle|0\rangle\longmapsto|\Psi\rangle|\Psi\rangle.
$$

线性演化会把基态复制协议延伸为纠缠的相干复制态，而不是右侧所写的非线性平方。于是，Zeckendorf 的合法性约束只决定可用的正交标签集合；它不能绕过量子态重叠的复制边界，也不能把标签复制自动升级为历史的独立物理副本。

### 90.4 稳定经典记录需要区分“复制标签”和“保留关联”

由前两节可以把记录协议分成三种情形：

$$
\begin{aligned}
&|R_{ij}|=0
&&\Rightarrow&&
\text{该对历史可被当前记录完全区分；}\\
&0<|R_{ij}|<1
&&\Rightarrow&&
\text{记录获得部分区分，同时保留部分相干；}\\
&|R_{ij}|=1
&&\Rightarrow&&
\text{当前记录没有区分这对历史的能力。}
\end{aligned}
$$

第一种情形适合形成可复制的经典标签；第二种情形必须把后续相位、访问范围和恢复操作纳入模型；第三种情形若仍要预测两条历史的差异，就不能把当前记录当作充分状态。

因此，“稳定经典现实”不能定义为把所有历史都复制到无限多个寄存器。更精确的条件是：对指定目标实验族，相关历史已经落入可区分的记录扇区，且被省略的联合关联在预测视界内不会重新进入目标读数。正交复制解决的是一次无误标签任务；它不自动解决未来动力学闭合。

### 90.5 与 Zeckendorf 刻度的组合边界

对合法构型集合 $\mathcal W_L$，Zeckendorf 数值只提供一个离散坐标

$$
\nu(w)=\sum_j F_{j+2}w_j.
$$

若记录耦合另行定义为 $|w\rangle\mapsto|r_w\rangle$，真正进入局部预测的是

$$
R_{wv}=\langle r_w|r_v\rangle,
$$

而不是 $\nu(w)-\nu(v)$ 本身。两个 Zeckendorf 数值相差很大，记录向量仍可能重合；两个数值相邻，也可能被特定耦合映射到正交记录。必须同时给出编码、记录态和允许操作，才能判断历史是否已经成为稳定的经典标签。

本节复用 `pure_record_distinguishability_coherence_complementarity` 与 `no_cloning_inner_product_criterion`。由它们得到的等式和正交/相同二分是 Lean 已证明的有限 Hilbert 空间结果；把它们推广到近似复制、带噪声环境、无限记录链或具体 Zeckendorf 里德伯动力学，仍需额外的通道模型和误差界。

## 追加锚（新终端）

## 91. 局部边缘的相关盲区与历史容量

### 91.1 双系统的无读相关扇区

设两个有限 Hilbert 因子的维数分别为 $m,n$，并在双系统的 trace-zero Hermitian 空间中区分三个子空间：第一因子的局部扇区 $L_A$、第二因子的局部扇区 $L_B$，以及相关扇区 $C$。`local_marginal_correlation_blind_spot` 给出它们的正交分解：

$$
\boxed{
L_A\oplus^{\perp}L_B\oplus^{\perp}C
=
\operatorname{bipartiteTraceZero}(m,n).
}
$$

完整局部边缘能够看到的方向数为

$$
\dim(L_A\oplus L_B)
=(m^2-1)+(n^2-1),
$$

而相关扇区的维数为

$$
\boxed{
\dim C=(m^2-1)(n^2-1).
}
$$

总的 trace-zero 方向数是 $(mn)^2-1$，所以相关盲区占比为

$$
\boxed{
\frac{\dim C}{\dim\operatorname{bipartiteTraceZero}(m,n)}
=
\frac{(m^2-1)(n^2-1)}{m^2n^2-1}.
}
$$

这里的“盲”有严格范围：$C$ 与两个局部扇区在 Hilbert—Schmidt 配对下正交，因此只使用完整的两个局部边缘时，$C$ 中的差异不会改变这些局部线性读数。它不表示相关差异在联合系统中不存在，也不表示任何允许联合操作的实验都无法恢复它。

### 91.2 两个量子态可以有相同边缘而不同整体

项目同时构造两个二能级双系统状态。一个是 Bell 纯态密度矩阵 $\rho_{\mathrm{Bell}}$，另一个是只在 $00$ 与 $11$ 上各占一半的经典相关混合 $\rho_{\mathrm{cl}}$。它们满足

$$
\operatorname{Tr}_A(\rho_{\mathrm{Bell}})
=
\operatorname{Tr}_A(\rho_{\mathrm{cl}}),
\qquad
\operatorname{Tr}_B(\rho_{\mathrm{Bell}})
=
\operatorname{Tr}_B(\rho_{\mathrm{cl}}),
$$

但

$$
\rho_{\mathrm{Bell}}\ne\rho_{\mathrm{cl}}.
$$

Lean 还保留了两者的结构差异：Bell 密度矩阵的秩为 $1$，而经典相关混合不是幂等矩阵。因此，完整边缘读数相同并不意味着联合态相同；被局部观察删去的正是相关扇区中的信息。

这给第 89 节的“访问范围”提供了一个有限维反例：若只访问两个边缘，无法从边缘函数恢复这两种联合记录；若允许联合测量，则可以选择与相关扇区有非零配对的效果来区分它们。后半句是由正交分解得到的操作性组合解释，不是该定理额外证明了某个特定 POVM 的实现。

### 91.3 两个量子比特的数值预算

取 $m=n=2$，则

$$
\dim\operatorname{bipartiteTraceZero}(2,2)=2^4-1=15,
$$

局部可见方向为

$$
(2^2-1)+(2^2-1)=6,
$$

相关盲区为

$$
(2^2-1)(2^2-1)=9,
$$

占比为

$$
\frac{9}{15}=\frac35.
$$

这说明“两个局部系统各自都被完整读出”仍只覆盖 $6$ 个独立的 trace-zero 方向；剩下的 $9$ 个方向不是两个边缘容量的简单相加可以得到的。它们需要联合效果、联合动力学，或保留跨系统记录。

### 91.4 与 Zeckendorf 载体的边界

若要把本节代入 Zeckendorf 合法载体，必须先给出双系统分解。例如可以额外假设

$$
 m=F_{L_A+2},
\qquad
 n=F_{L_B+2},
$$

并把两组合法构型分别实现为两个正交载体。此时才可形式上写出

$$
\dim C
=
\bigl(F_{L_A+2}^2-1\bigr)
\bigl(F_{L_B+2}^2-1\bigr).
$$

单独知道一个长度为 $L$ 的合法空间有 $F_{L+2}$ 个标签，并不能自动把它分解成维数为 $m$ 与 $n$ 的两个物理子系统；更不能从单一 Fibonacci 标签数直接推出相关扇区的维数。编码、张量分解和局部读出必须分别指定。

因此，本节把“历史保留多少”再收紧一层：如果任务只访问局部边缘，相关扇区可以暂时留在不可见残差中；如果未来任务允许联合操作，相关扇区必须进入目标闭包，或者给出忽略它所造成的误差界。

本节复用 `local_marginal_correlation_blind_spot`。其正交分解、维数公式和 Bell/经典相关混合的等边缘反例是 Lean 已证明的有限维结果；把相关盲区解释为具体实验中的不可恢复信息、把 Zeckendorf 标签实现为双系统载体，以及把联合效果提升为物理仪器，仍需额外模型与验证。

## 追加锚（新终端）

## 92. 完备互补上下文中的碰撞统计与纯度

### 92.1 互补记录把算子信息压缩成碰撞和

设系统维数为 $n+1$，有 $n+2$ 个秩一记录上下文。每个上下文都满足记录测量条件，并假设同一上下文内的投影正交、不同上下文之间满足

$$
\operatorname{Tr}(P_{l,j}P_{k,r})
=
\begin{cases}
\delta_{jr},&l=k,\\[2pt]
\dfrac{1}{n+1},&l\ne k.
\end{cases}
$$

这是一组有限维的完备互补上下文条件。`complete_context_collision_conservation` 在这些假设下证明算子恒等式

$$
\boxed{
\sum_{l,j}P_{l,j}\otimes P_{l,j}
=I+\operatorname{Swap}.
}
$$

右侧的交换算子说明：这些上下文的联合记录不只是把每个结果标签分别列出来，而是在二次张量层面覆盖了交换对称的方向。它因此能够把状态的二次信息投影到一个可计算的碰撞统计量。

### 92.2 碰撞概率直接读出纯度

对满足正半定和单位迹条件的密度矩阵 $\rho$，令

$$
 p_{l,j}=\operatorname{basisProbability}(\rho,\text{context }l,j).
$$

同一定理给出

$$
\boxed{
\sum_{l,j}p_{l,j}^{\,2}
=
1+\operatorname{Re}\operatorname{Tr}(\rho^2).
}
$$

因此，在这组完备互补上下文中，所有结果概率的平方和不是任意的“记录总量”，而是状态平方迹的一个平移。若另有条件使 $\operatorname{Tr}(\rho^2)=1$，则碰撞和等于 $2$；一般情况下仍应保留右侧的平方迹，而不能仅凭上下文数量把状态称为纯态。

这条关系把第 89 节的关联记录和第 91 节的相关盲区连接起来：单个局部边缘只能看到局部扇区，而完备互补上下文的整体碰撞和可以对全局二次结构敏感。它仍然不是说一次实验同时读取了所有不相容上下文；这些概率来自在可重复制备上分别执行各上下文，再把统计结果组合起来。

### 92.3 记录细化的代价与收益

完备上下文增加了可访问的读出方向，但它并没有免费消除历史成本。每个上下文仍有自己的结果标签和实验设置；要估计碰撞和，需要在相应设置下积累统计数据。若只保留一个上下文的结果，通常不能从该单一切面恢复右侧的完整平方迹；若保留全部上下文的概率表，才可以使用上式形成纯度证书。

所以“保留多少历史”在这里有两个不同层次：

$$
\begin{aligned}
&\text{状态方向预算：}&d^2-1&\text{ 个连续 trace-zero 方向；}\\
&\text{碰撞证书预算：}&\sum_{l,j}p_{l,j}^2&\text{ 所需的多上下文统计记录。}
\end{aligned}
$$

第二项是一个任务特定的标量证书，不等于保存了完整密度矩阵，也不等于已经构造出一个无记忆的经典状态。不同状态可以共享某个单一统计量；若任务还要求预测未来效果，仍需检查第 86 节的目标闭包和残差条件。

### 92.4 Zeckendorf 载体只能作为附加实现假设

如果要把这条碰撞守恒放到 Zeckendorf 合法空间上，必须先选择一个 $L$，令合法构型数满足

$$
 d=F_{L+2},
$$

再额外构造一族作用在该 $d$ 维空间上的 $d+1$ 个互补秩一上下文，并验证每对投影的重叠条件。Zeckendorf 递推本身只提供 $d$ 个离散标签；它不自动产生完备上下文、交换算子恒等式或碰撞统计。

相应地，若系统被分成两个载体，必须同时满足张量维数分解 $d=mn$，并分别说明局部上下文和联合上下文。第 91 节的相关扇区不会因为给每个构型附上 Fibonacci 编号就自动消失。

本节复用 `complete_context_collision_conservation`。算子恒等式和碰撞—平方迹关系是在明确的有限维互补上下文假设下由 Lean 证明的；上下文在物理实验中的可实现性、有限样本误差、与热力学熵的关系，以及 Zeckendorf 载体上具体构造这些上下文，仍需额外模型与误差分析。

## 追加锚（新终端）

## 93. 算术权重、对角固定点与有效热记录

### 93.1 固定点先由记录基底决定

设 $B$ 是 $d$ 维 Hilbert 空间上的秩一记录上下文，并假设其投影族满足 `IsRecordMeasurement`。项目中的 `basis_measurement_eq_self_iff` 给出固定点刻画：

$$
\boxed{
\operatorname{basisMeasurement}_B(A)=A
\iff
A\in\operatorname{diagonalSubspace}(B).
}
$$

这条等价式的重点不是某个特殊权重，而是记录机制先选定了一个对角子空间。被保留下来的信息是该上下文中的经典对角方向；其余非对角方向不会成为这个记录通道的固定信息。

因此，“经典现实”在这个有限模型中的第一层含义可以写成：

$$
\text{稳定记录}
=
\text{被指定记录通道固定的算子子空间中的元素}.
$$

它仍然是相对于上下文 $B$ 的定义。更换记录基底，会更换 diagonalSubspace，也会更换哪些差异被视为稳定记录。

### 93.2 有限 zeta 权重自动落入这个固定点

对有限索引集 $S\subseteq\operatorname{Fin}(d)$，项目定义

$$
Z_s(S)=\sum_{n\in S}(n+1)^{-s},
$$

并构造加权算子

$$
\tau_{B,s,S}
=
\sum_{n\in S}
\frac{(n+1)^{-s}}{Z_s(S)}P_{B,n}.
$$

`zeta_thermal_state_mem_diagonal` 证明

$$
\tau_{B,s,S}\in\operatorname{diagonalSubspace}(B),
$$

所以 `zeta_thermal_state_pinching_fixed` 给出

$$
\boxed{
\operatorname{basisMeasurement}_B(\tau_{B,s,S})
=\tau_{B,s,S}.
}
$$

这里的“thermal”只表示一种有限 zeta 权重的构造命名。当前定理证明的是它属于指定上下文的对角子空间并被该测量固定；它没有单独证明 $Z_s(S)\ne0$、正迹归一化、某个 Hamiltonian 的 Gibbs 形式，或与实验温度的对应关系。若要把 $\tau_{B,s,S}$ 当作物理密度态，还必须另加这些条件。

### 93.3 固定不等于由动力学达到

第 89 节已经区分了去相位后的固定点与实际熵产生；本节提供一个算术权重的具体固定点例子，但不改变这个边界：

$$
\operatorname{basisMeasurement}_B(\tau)=\tau
\quad\not\Rightarrow\quad
\rho_k\longrightarrow\tau.
$$

要得到趋近结论，必须指定动力学 $\Phi$，并证明 $\tau$ 是 $\Phi$ 的吸引子，或者至少证明从给定初态出发的迭代误差界。固定点等式只说明“如果已经在这个记录子空间中，当前记录不会再改变它”。

同样，两个不同的权重参数 $s$ 或两个不同的有限集 $S$ 可以给出不同的稳定对角状态；记录通道本身不会从固定点等价式中选出唯一的 $s$。选择参数属于模型或实验标定，而不是 Zeckendorf 编码的逻辑后果。

### 93.4 与 Zeckendorf 刻度的关系

若把有限合法 Zeckendorf 构型 $w\in\mathcal W_L$ 映射到上下文 $B$ 的正交基向量，并令索引集 $S$ 对应这些构型，则可以在 $	au_{B,s,S}$ 中使用 Fibonacci 标签、素数指数或其他离散坐标作为权重输入。可是，当前 zeta 固定点定理只使用有限索引 $n$、秩一投影和对角子空间；它没有证明

$$
(n+1)^{-s}
$$

必须等于某个 Fibonacci 能量，也没有证明 Zeckendorf 数值就是热力学能量。两者的安全连接是：Zeckendorf 提供合法离散索引，zeta 权重提供一种可计算的对角加权，记录测量负责规定这些加权态是否稳定可读。

因此可以把三种角色分开：

$$
\boxed{
\begin{aligned}
&\text{编码：}&w&\longmapsto\text{合法离散标签};\\
&\text{加权：}&n&\longmapsto (n+1)^{-s};\\
&\text{记录：}&B&\longmapsto\operatorname{diagonalSubspace}(B)\text{ 与其固定点}.
\end{aligned}}
$$

只有在额外给出载体映射、归一化和动力学之后，才能讨论这些层是否共同形成一个可预测的有效热记录。

本节复用 `basis_measurement_eq_self_iff`、`zeta_thermal_state_mem_diagonal` 和 `zeta_thermal_state_pinching_fixed`。Lean 已证明的是有限秩一记录上下文中的对角固定性；物理 Gibbs 态、热平衡、唯一吸引子、Zeckendorf 能量解释和无限 zeta 极限仍需额外假设与证明。

## 追加锚（新终端）

## 94. 局部动力学不能自动填补相关盲区

### 94.1 局部扇区在迭代下保持封闭

继续使用第 91 节的双系统分解。令

$$
L=L_A\oplus L_B
$$

表示两个局部扇区的和，令 $C$ 表示相关扇区。设 Heisenberg 演化是一个实线性映射

$$
\mathsf H:
\operatorname{BipartiteHermitian}(m,n)
\longrightarrow
\operatorname{BipartiteHermitian}(m,n),
$$

并假设

$$
\mathsf H(L)\subseteq L.
$$

`local_dynamics_no_tomography` 证明对任意离散时间 $t$，

$$
\boxed{
\mathsf H^{t}(L)\subseteq L.
}
$$

这是一个纯粹的迭代闭合结论：如果一步演化不离开局部可见空间，那么重复应用它也不会从局部方向产生新的相关方向。

### 94.2 局部读数不能靠自身迭代完成联合层析

同一定理还给出更强的交集结论：若 $x\in L$ 且某次迭代同时落入相关扇区，

$$
\mathsf H^t x\in C,
$$

则

$$
\boxed{
\mathsf H^t x=0.
}
$$

原因是 $L$ 与 $C$ 在 Hilbert—Schmidt 几何下正交；保持局部扇区的迭代结果既属于 $L$，又属于 $C$，只能落在零交集。这把“局部边缘看不见相关历史”改成了一个动力学判据：只使用保持 $L$ 的局部 Heisenberg 操作，不能把相关扇区拉回局部坐标，也不能用局部数据完成联合层析。

这里的条件非常具体。定理没有说任何物理动力学都保持 $L$，也没有说相关扇区对所有联合操作都不可见；它只约束满足上述线性不变性假设的演化族。只要加入一个把局部方向送入相关方向的联合相互作用，或者允许直接测量 $C$ 中的效果，结论的适用范围就改变。

### 94.3 对“保留多少历史”的影响

第 91 节给出相关扇区的维数

$$
\dim C=(m^2-1)(n^2-1).
$$

第 94 节说明：若未来实验族的 Heisenberg 闭包仍满足 $\mathsf H(L)\subseteq L$，那么这些相关方向不会被局部动力学主动暴露。对只回答局部目标的问题，可以把 $C$ 留在残差空间；对需要联合目标的任务，则必须在实验族中加入能够离开 $L$ 的操作，或直接保留联合记录。

因此，历史预算不只由静态维数决定，还由动力学的扇区不变性决定：

$$
\boxed{
\text{局部预算足够}
\iff
\text{目标闭包仍在 }L\text{ 中};
\qquad
\text{联合目标需要 }C\text{ 的访问或生成机制}.
}
$$

这个判据与第 86 节的目标闭包条件相容，但不能替代对具体目标族和误差容限的计算。若演化只近似保持 $L$，则需要额外的 Lipschitz 或泄漏范数来给出近似版本；当前定理只给出精确离散不变性。

### 94.4 Zeckendorf 双载体的边界

若两个局部载体分别由 Zeckendorf 合法空间实现，必须先给出

$$
 m=F_{L_A+2},
\qquad
 n=F_{L_B+2},
$$

以及一个实际作用在 $m\times n$ 联合空间上的 Heisenberg 映射。只有在验证该映射保持 $L_A\oplus L_B$ 后，才能应用上述闭合结论。Fibonacci 计数本身既不保证局部扇区不变，也不保证相关扇区一定能被某个物理相互作用访问。

本节复用 `local_dynamics_no_tomography`。Lean 已证明的是实线性、精确扇区保持下的迭代闭合和零交集结论；近似局部动力学、开放系统通道、有限样本误差和具体 Zeckendorf Hamiltonian 仍需额外模型。

## 追加锚（新终端）

## 95. 有限移位记录的余弦误差地板

第 81 节已经给出有限移位记录中以 $|\gamma(\ell)|$ 表示的恢复下界。本节的新增内容是对同一个特定通道证明有限窗口的余弦估计，从而把未知的自相关系数替换成显式的标签间距和窗口长度界。

### 95.1 一个可计算的有限记录通道

设 $c:\mathbb Z\to\mathbb C$ 只支撑在有限窗口 $0,1,\ldots,N$，并满足

$$
\sum_{k\in\mathbb Z}|c_k|^2=1.
$$

给每个系统标签 $i$ 一个整数位置 $q_i$，定义移位相关函数

$$
\gamma(t)
=
\sum_{k\in\mathbb Z}c_{k+t}\,\overline{c_k}.
$$

`finite_record_cosine_obstruction` 构造了一个具体的有限记录通道 $C$。在它的系统边缘作用上，矩阵元按标签差异衰减为

$$
\boxed{
\Lambda(A)_{ij}
=
\gamma(q_i-q_j)A_{ij}.
}
$$

这把记录重叠写成了一个离散自相关函数：对角元不变，标签间距为 $t$ 的相干项乘上 $\gamma(t)$。这里的 $C$ 是定理在给定有限窗口、整数标签和记录向量后构造出的特定通道；不能把这个存在性结论改写成任意有限记录装置都具有同一形式。

### 95.2 任意系统端恢复都有一个最坏误差下界

若存在一对标签满足

$$
q_i-q_j=\ell\ne0,
$$

对任意只作用在系统端的恢复通道 $R$，定理对所有输入密度态取最坏误差上确界，得到

$$
\boxed{
\frac{1-|\gamma(\ell)|}{2}
\le
\sup_{\rho\in\mathrm{DensityState}}
D\!\left(R(C(\rho)),\rho\right).
}
$$

更精确地，Lean 结论把左侧误差集合写成一个非空有界集合的上确界，并同时证明它与对应的矩阵迹范数误差集合相等。这个量是“对所有输入状态的最坏误差”，不是说每个输入态都达到该下界，也不是说该下界在所有通道中都是最佳常数。

下界的来源是一个成对的相干见证：可以选取只在 $i,j$ 两个标签上有相反相位的两个纯态，它们输入时迹距离为 $1$，记录通道后只剩下由 $\gamma(q_i-q_j)$ 缩放的非对角差异；迹距离收缩和三角不等式迫使任意恢复保留这项误差。

### 95.3 有限窗口给出严格的余弦地板

令

$$
 d=|\ell|,
\qquad
 m=\left\lfloor\frac{N}{d}\right\rfloor.
$$

`coefficient_gamma_le_cosine` 对有限支撑的每个非零整数移位给出

$$
|\gamma(\ell)|
\le
\cos\!\left(\frac{\pi}{m+2}\right).
$$

因此 `finite_record_cosine_obstruction` 进一步得到

$$
\boxed{
\frac{1-\cos\!\left(\frac{\pi}{m+2}\right)}{2}
\le
\sup_{\rho}
D\!\left(R(C(\rho)),\rho\right),
\qquad
\frac{1-\cos\!\left(\frac{\pi}{m+2}\right)}{2}>0.
}
$$

余弦上界来自把整数索引按模 $d$ 分成 residue blocks；每个长度为 $m+1$ 的实非负范数序列满足最近邻二次型的有限路径上界，再把各块的质量相加。它是统一上界，由此产生严格正的误差地板；当前定理没有为每个 $c$ 提供达到该上界的等号见证，因此不把这个恢复下界称为普适 sharp 常数。

两个边界值得保留：如果所有 $q_i$ 都相同，则不存在非零标签差，定理的量化条件为空；如果 $d>N$ 或 $N=0$，则 $m=0$，地板为

$$
\frac{1-\cos(\pi/2)}{2}=\frac12.
$$

当 $m$ 增大时，地板可以变小；这只说明更长的有限窗口可以降低该特定模型的下界，不表示已经得到无限记录极限或任意通道的无误恢复。

### 95.4 与 Zeckendorf 历史预算的关系

若把合法 Zeckendorf 构型映射为整数标签 $q_i$，则本节告诉我们：标签间距、记录窗口长度 $N$ 和自相关 $\gamma$ 共同决定系统端恢复成本。仅增加合法标签的数量并不能保证历史可恢复；还必须指定这些标签如何嵌入有限记录序列，以及记录寄存器是否仍可被联合访问。

因此，对一个给定的非零间距 $\ell$，可以把

$$
\varepsilon_{N,\ell}
=
\frac{1-\cos\!\left(\frac{\pi}{\lfloor N/|\ell|\rfloor+2}\right)}{2}
$$

作为该有限移位记录模型中的保守恢复预算。它是标签族和记录协议的函数，不是 Zeckendorf 数值本身的普适误差，也不是对所有环境或恢复操作的定律。

本节复用 `finite_record_cosine_obstruction`、`coefficient_gamma_le_cosine` 和 `finite_record_recovery_error_lower_bound`。Lean 已证明的是有限支撑、归一化记录序列、整数标签和系统端恢复通道下的具体下界；联合访问记录环境、近似无限窗口、其他编码和物理 Hamiltonian 仍需分别建模。

## 追加锚（新终端）

## 96. 静态效果相同，仪器历史仍可不同

前面的不完整观察者结果已经说明：当前效果族存在正交残差时，不同密度态可以拥有完全相同的单次读数。本节补上一个更具体的物理桥：即使当前 POVM 的每个效果都完全相同，**仪器在分支后怎样更新状态**仍会改变下一次读数。

### 96.1 同一个 POVM 不决定同一个仪器

在一个量子比特上，令

$$
P_0=|0\rangle\langle0|,
\qquad
P_1=I-P_0,
\qquad
X=|0\rangle\langle1|+|1\rangle\langle0|.
$$

考虑两组单 Kraus 分支：

$$
K_b=P_b,
\qquad
L_b=XP_b,
\qquad b\in\{0,1\}.
$$

它们的静态效果完全相同，因为

$$
K_b^\dagger K_b=P_b,
$$

而

$$
L_b^\dagger L_b
=P_bX^\dagger XP_b
=P_b.
$$

两组效果都满足

$$
\sum_{b=0}^1P_b=I.
$$

因此，只看当前一次测量的 outcome 概率，无法区分这两台仪器。

### 96.2 下一步联合统计却相反

取共同初态 $$\rho=P_0$$，并比较第一步得到 $$b=0$$ 后、第二步读取效果 $$P_1$$ 的概率。

对于第一台仪器，分支态为

$$
K_0\rho K_0^\dagger=P_0,
$$

所以第二步的未归一化权重为

$$
\operatorname{Tr}(P_1P_0)=0.
$$

对于第二台仪器，分支态为

$$
L_0\rho L_0^\dagger
=XP_0X^\dagger
=P_1,
$$

所以第二步权重为

$$
\operatorname{Tr}(P_1P_1)=1.
$$

项目定理 `same_effects_different_two_step_joint_law` 已在有限矩阵中同时证明了四件事：两组分支效果逐 outcome 相等、两组效果都归一化，以及上述第二步概率分别为 $$0$$ 和 $$1$$。

于是得到一个比“当前边缘读数不完整”更强的结论：

$$
\boxed{
\text{相同 POVM 效果}
\not\Rightarrow
\text{相同后续过程}.
}
$$

静态效果只记录 $$K_b^\dagger K_b$$；它没有记录 Kraus 分支留下的状态变换。后续实验访问的正是这部分历史。

### 96.3 需要保留的不是全部过去，而是分支更新

设当前记录只保存 outcome $$b$$，却丢弃分支后的更新算子。上面的两台仪器在当前记录层完全相同，但它们的下一步响应不同。因此，把对象压成

$$
\text{当前 outcome 分布}
$$

不足以支撑未来预测；至少要保留下面三者之一：

$$
\boxed{
\text{分支更新 }\mathcal J_b,
\quad
\text{足以模拟未来的预测摘要},
\quad或
\quad
\text{可访问的联合记录}.
}
$$

这正是“保留多少历史”的操作性版本：历史预算由未来实验能否重建分支后的状态决定，而不是由已经读出的标签数量决定。若允许的未来目标只属于当前效果的线性张成，已有的 `target_prediction_sufficiency` 可以给出签名充分性；若目标包含分支更新产生的新方向，则必须扩大到相应的序列效果或 Heisenberg 闭包。

### 96.4 与 Zeckendorf 构型的接法

把 Zeckendorf 合法字串 $$w$$ 当作系统标签时，静态读出可以先定义为

$$
P_w=|w\rangle\langle w|,
$$

但这只指定了“读到哪个构型”。若构型读出后还允许执行条件更新 $$\mathcal J_w$$，则未来统计由

$$
E_{w_1\cdots w_n}
=
\mathcal J_{w_1}^*\cdots
\mathcal J_{w_n}^*(I)
$$

决定，而不由 Zeckendorf 数值 $$a(w)$$ 单独决定。不同的 $$\mathcal J_w$$ 可以共享相同的单步效果，却产生不同的多步响应。

因此，Zeckendorf 继续承担离散构型的合法编号；仪器分支和后续动力学承担历史如何回流。要声称某个合法字串的当前标签已经足够，必须先证明所有允许的未来词效果都由该标签因子化，或给出未因子化部分的误差界。

本节复用 `same_effects_different_two_step_joint_law`，并与已有的 `target_prediction_sufficiency`、`unified_sequential_kernel` 和 `all_future_statistics_sufficiency` 相接。Lean 已证明的是明确二能级单 Kraus 仪器的有限矩阵反例；它没有证明任意 POVM 都具有该差异，也没有替具体 Zeckendorf Hamiltonian 选择唯一的分支更新。

## 97. 用反向搜索计算最早未来分离深度

第 76 节给出了有限未来关系塔的稳定深度，但没有指定怎样从一个具体的有限更新表中计算每一对状态的首次分离时刻。项目的 `reverse_bfs_correct_and_quadratic` 提供了一个直接算法。

### 97.1 定义成对的未来分离距离

设 $$Y$$ 是有限状态集，

$$
\tau:Y\to Y,
\qquad
q:Y\to O
$$

分别是确定性更新和当前读出。对有序状态对 $$(x,y)$$，定义

$$
\delta(x,y)
=
\min\left\{n\in\mathbb N:
q(\tau^n x)\ne q(\tau^n y)\right\},
$$

若不存在这样的时刻则记为 $$\delta(x,y)=\infty$$。这正是源码中的 `exactSeparationDepth`：它返回 `some n` 或 `none`，而不是把永远不可分的状态强行赋予一个有限距离。

$$
\boxed{
\delta(x,y)=\infty
\iff
x,y\text{ 对全部未来读数保持等价}.
}
$$

因此，稳定对象的边界可以按对区分：有限距离表示还需要保留一个有限未来窗口，$$\infty$$ 表示在指定更新和读出下无需再区分。

### 97.2 反向 BFS 的正确性

把状态对写成一个成对节点

$$
(x,y)\longmapsto(\tau x,\tau y).
$$

先把当前读数不同的节点放入源集合：

$$
M_0
=\{(x,y):q(x)\ne q(y)\}.
$$

再沿成对更新边反向扩张：

$$
M_{k+1}
=
M_k
\cup
\left\{(x,y):(\tau x,\tau y)\in M_k\right\}.
$$

第 $$k$$ 层恰好包含那些在不超过 $$k$$ 步的未来某个时刻会分离的状态对。因而反向搜索首次访问层数满足

$$
\operatorname{reverseBfsDistance}(x,y)
=
\delta(x,y).
$$

这不是启发式搜索；Lean 定理逐对证明了它与源语义 `exactSeparationDepth` 的相等。

### 97.3 历史预算的可计算上界

显式保存每个有序状态对的一条反向边，边数恰为

$$
|Y|^2.
$$

项目定理给出

$$
\boxed{
T\le 2|Y|^2,
\qquad
S\le 3|Y|^2,
}
$$

其中 $$T$$ 是该显式表和逐对访问的单位成本上界，$$S$$ 是边表、距离表和队列的存储上界。这个界没有使用收缩率或概率近似；它只依赖有限状态和确定性更新。

若所有有限的 $$\delta(x,y)$$ 中取最大值

$$
H_*=
\max\{\delta(x,y):\delta(x,y)<\infty\},
$$

那么观察到 $$H_*$$ 的未来窗口后，所有本来会被分开的状态对都已经分开；剩下的对在整个未来中保持同一读数。若不存在任何分离对，可约定 $$H_*=0$$。

这给出“需要保留多少历史”的一个可执行版本：在这个经典有限模型里，保留到 $$H_*$$ 就足够完成指定读出族的未来分类；不需要保留每一条更长历史。

### 97.4 Zeckendorf 窗口与量子边界

若合法 Zeckendorf 构型集 $$\mathcal W_L$$ 被明确赋予

$$
\tau:\mathcal W_L\to\mathcal W_L,
\qquad
q:\mathcal W_L\to O,
$$

则

$$
|Y|=|\mathcal W_L|=F_{L+2}
$$

代入上面的算法预算，得到二次于合法构型数量的校准成本。这里的 $$F_{L+2}$$ 只是载体大小；$$H_*$$ 仍由实际更新和读出表决定。

这条反向 BFS 结论属于有限确定性模型。对量子通道，状态空间通常是连续的，且未来区分可能是概率差异而非精确标签不等式；此时应使用前面的效果闭包、预测投影或误差距离，而不能把 $$|Y|^2$$ 的枚举界直接宣称为量子记忆复杂度。

本节复用 `reverse_bfs_correct_and_quadratic`。Lean 已证明的是有限状态、确定性更新、有限读出字母表下的精确分离深度与预算；Zeckendorf 映射、量子概率阈值和噪声鲁棒版本仍需另行指定。

## 追加锚（新终端）

## 98. 占据历史链的精确振幅与最小记忆债务

第 97 节处理有限确定性状态表的未来分离。另一条更接近“历史怎样被压缩”的项目结果来自 `SequentialOccupationHistory`：它把一个有限占据多重集的逐步生成写成量子等距链，并直接计算每个切口必须保留的记忆维数。

### 98.1 边界不是标签，而是部分历史

给定有限多重集 $$a$$，令 $$\operatorname{Boundary}(a,t)$$ 表示从 $$a$$ 中取出恰好 $$t$$ 个占据的部分历史。若当前边界为 $$b$$，下一步加入符号 $$i$$ 的合法条件是

$$
\operatorname{count}_b(i)<\operatorname{count}_a(i).
$$

项目定义转移矩阵

$$
N_t(i,c;b)
=
\begin{cases}
\sqrt{\dfrac{\operatorname{count}_{a-b}(i)}{|a|-t}},
&c=b+\{i\},\\[6pt]
0,&\text{否则}.
\end{cases}
$$

它保留了“哪些前缀历史仍可继续”以及“剩余占据给每个后继多少振幅”两种信息。对 $$t<|a|$$，Lean 定理 `next_step_gram` 给出

$$
\boxed{
N_t^\dagger N_t=I.
}
$$

所以每个合法一步都是等距的；`next_step_quantum_channel` 进一步构造了相应的有限维量子通道。这里的等距性不是说记忆已经被压成一个标量，而是说这一步在保留的边界载体上不丢失内积。

### 98.2 多步收缩精确等于占据扇区振幅

对一个词 $$w$$，把所有合法边界路径的局部转移振幅相乘并求和，得到 `contraction`。项目定理 `contraction_eq_sector` 证明：当剩余长度与切口满足

$$
|a|=t+n,
$$

时，逐步收缩恰好等于占据扇区向量的分量：

$$
\boxed{
\operatorname{contraction}(a,n,t,w,b)
=
\operatorname{sectorVector}_n(a-b,w).
}
$$

从初始空边界出发，`history_sequential_preparation` 因而给出整个合法占据历史的精确制备振幅。这个等式把“历史求和”落实为有限矩阵乘法；中间边界是被保留的历史接口，末端扇区向量是完整输出。

### 98.3 每个切口都有一个不可绕开的秩下界

把长度 $$t+s$$ 的完整振幅按切口拆成前缀和后缀，定义系数矩阵 $$C_a^{t,s}$$。任意一个有限链若能精确产生同一个扇区振幅，`sequential_coefficient_factorization` 给出

$$
C_a^{t,s}=P_tQ_s,
$$

其中中间指标空间就是该切口的 bond carrier。因此

$$
\operatorname{rank}(C_a^{t,s})
\le
\dim(\text{bond at }t).
$$

项目进一步把扇区系数矩阵的秩写成边界数量，得到 `sequential_memory_necessity`：

$$
\boxed{
|\operatorname{Boundary}(a,t)|
\le
\dim(\text{任何精确链在切口 }t\text{ 的记忆} ) .
}
$$

这是一条比“历史越长，内存越多”更精确的说法。真正的债务由前缀与后缀振幅的线性秩决定；大量字面不同的历史如果在系数矩阵中线性相关，可以共享记忆，而线性独立的边界不能被同一个更小的切口载体精确表示。

### 98.4 5040 的精确实例

项目中的 `occupation5040` 与算术卷中的 5040 具有同一数值对象，但两者承担的编码角色不同。算术卷给出

$$
5040=2^4\cdot3^2\cdot5\cdot7
$$

及其 Zeckendorf 指数行；量子占据链把一个具体多重集的逐步历史写成振幅链。对这个占据多重集，源码证明

$$
|a|=8,
$$

并且所有精确制备链的最大 bond 都满足

$$
\boxed{
\max_t\dim(\text{bond at }t)\ge12.
}
$$

`history_5040_minimum_maximum_bond` 证明下界可达；`history_5040_occupation_chain_attainment` 同时给出链长为 $$8$$、最大 bond 为 $$12$$，并且每个长度八的词振幅都精确等于对应扇区向量。

因此，这个实例给出一个完整的“约束—历史—量子记忆”数值链：

$$
\text{固定占据约束}
\longrightarrow
\text{合法边界族}
\longrightarrow
\text{切口秩}
\longrightarrow
\text{最小记忆 }12.
$$

但必须保留编码边界：源码没有证明 Zeckendorf 合法字串空间与这个 occupation boundary 空间同构，也没有证明 12 是所有能完成同一物理任务的任意量子协议的普适记忆维数。它是该多重集、该精确振幅目标和该有限链模型下的最小最大 bond。

### 98.5 对“稳定经典现实”的补充

这条结果把前面的预测闭合条件再细化了一层。若只要求当前概率标签，可能只需保存一个粗读数；若要求保留完整后续振幅，则每个切口必须保存足以承载系数矩阵秩的边界信息。两者对应不同任务：

$$
\text{标签预测任务}
\not\equiv
\text{完整相干历史制备任务}.
$$

Zeckendorf 可以继续提供合法构型的离散坐标，occupation chain 则给出在一个具体相干任务中这些历史怎样组合、怎样跨切口传输。只有把两者之间的编码映射、目标振幅和允许误差明确写出，才能把 Fibonacci 构型数量转换成实际量子记忆预算。

本节复用 `next_step_gram`、`next_step_quantum_channel`、`contraction_eq_sector`、`sequential_memory_necessity`、`minimum_maximum_bond_characterization` 和 `history_5040_minimum_maximum_bond`。Lean 已证明的是有限多重集占据链的等距性、精确收缩和切口下界；Zeckendorf—occupation 同构、噪声容错记忆以及任意开放系统中的最优压缩仍是未完成接口。

## 追加锚（新终端）

## 99. 单素数轴读数与多素数相关残差

算术卷中的 $$K(n)(p,j)$$ 把每个素数轴上的指数写成一行 Zeckendorf 字串。若把这些轴进一步放进一个有限张量模型，项目的 `single_prime_visible_space` 给出一个精确边界：所有逐轴 Hermitian 读数只能看到空支撑和单轴支撑，不能自动看到两个或更多素数轴之间的相关方向。

### 99.1 扇区分解

设有限索引集为 $$\iota$$，第 $$i$$ 个局部因子维数为 $$d_i$$。对每个有限支撑集 $$S\subseteq\iota$$，定义一个扇区：在 $$S$$ 上取局部 trace-zero Hermitian 方向，在 $$S$$ 外取标量恒等方向。记该扇区为 $$\mathcal V_S$$。

于是全局 Hermitian 张量空间按支撑集合分解为

$$
\mathsf{Herm}_{\mathrm{global}}
=\bigoplus_{S\subseteq\iota}\mathcal V_S.
$$

空支撑 $$S=\varnothing$$ 是整体恒等方向；单点支撑 $$S=\{i\}$$ 是第 $$i$$ 条局部轴的中心化读数；$$|S|\ge2$$ 则表示跨轴相关方向。

### 99.2 逐轴读数的完整像

令 `singlePrimeVisibleSpace` 表示由常数和所有完整单因子 Hermitian effect 生成的可见空间。Lean 定理 `single_prime_visible_space` 证明

$$
\boxed{
\mathsf V_{\mathrm{single}}
=\mathcal V_{\varnothing}
\oplus
\bigoplus_{i\in\iota}\mathcal V_{\{i\}}.
}
$$

如果每个扇区维数满足

$$
\dim_{\mathbb R}\mathcal V_S
=\prod_{j\in S}(d_j^2-1),
$$

则逐轴可见空间的维数为

$$
\boxed{
\dim_{\mathbb R}\mathsf V_{\mathrm{single}}
=1+\sum_{i\in\iota}(d_i^2-1).
}
$$

它是逐轴读数的完整线性容量；不是全部全局 Hermitian 空间的维数。

### 99.3 多轴相关方向的精确盲区

同一定理给出可见空间正交残差

$$
\mathsf R_{\mathrm{multi}}
=\bigoplus_{\substack{S\subseteq\iota\\|S|\ge2}}\mathcal V_S,
$$

以及

$$
\boxed{
\dim_{\mathbb R}\mathsf R_{\mathrm{multi}}
=\left(\prod_{i\in\iota}d_i\right)^2
-1
-\sum_{i\in\iota}(d_i^2-1).
}
$$

因此，只要这个数非零，就存在全局 Hermitian 差异，它对每条单轴读数都为零，却可能在联合 effect 上有非零响应。两因子情形退化为

$$
(d_1^2-1)(d_2^2-1),
$$

与前面二分系统的相关扇区维数一致。

这说明“逐素数轴都读过了”仍不等于“整体历史已经被读出”。逐轴记录保存的是一阶轴向信息；多素数耦合、联合进位或跨轴相位可以落在 $$\mathsf R_{\mathrm{multi}}$$ 中。

### 99.4 与 $$K(n)$$ 的准确接口

把 $$\iota$$ 取作一个有限素数集合时，可以把算术记录的每条 $$K(n)(p,\cdot)$$ 视为第 $$p$$ 轴的离散标签。但要把上面的维数公式用于量子模型，必须额外指定一个映射

$$
K(n)(p,\cdot)
\longmapsto
\text{第 }p\text{ 个局部 Hilbert 空间中的状态或 effect}.
$$

仓库当前定理只处理给定局部维数、给定扇区分解和给定单因子 Hermitian 读数；它没有从 Zeckendorf 行自动构造这些 Hilbert 空间，也没有把算术乘法的进位自动变成跨因子 Hamiltonian。

所以，若当前任务只询问每个素数轴的指数，单轴可见空间可能足够；若任务询问乘积、规范化进位、跨素数联合概率或联合相位，就必须加入至少一个 $$|S|\ge2$$ 的扇区，或者给出该相关残差对目标读数的误差界。

### 99.5 对稳定经典接口的后果

本节把“保留多少约束”改写成一个可量化选择：

$$
\boxed{
\text{逐轴经典接口}
\quad\text{vs.}\quad
\text{包含多轴相关的联合接口}.
}
$$

前者的容量是 $$1+\sum_i(d_i^2-1)$$；后者还要承担 $$\mathsf R_{\mathrm{multi}}$$ 中的方向。若后续动力学始终保持单轴可见空间不变，相关残差可以对该任务保持隐藏；若动力学或目标 effect 进入多轴扇区，当前逐轴记录就不再预测闭合。

这与两份算术卷的边界一致：Zeckendorf 唯一表示保证每条轴上的规范坐标，但不保证跨轴联合记录的唯一性、可见性或物理可逆性。稳定的经典现实因此不能由“每条轴都有合法刻度”单独推出，还必须说明哪些跨轴相关是任务允许继续访问的。

本节复用 `single_prime_visible_space`。Lean 已证明的是有限张量族、Hermitian 扇区和完整单因子读数下的可见空间及残差维数；素数轴到物理局部系统的编码、算术进位的联合动力学以及具体 Zeckendorf Hamiltonian 仍是待建接口。

## 追加锚（新终端）

## 100. 记录份额的阈值：一份隐藏，两份恢复

前面的章节主要按可见算子空间或历史秩计量信息。本节补上一个离散而完整的访问阈值实例：`QutritThresholdSharing` 构造三份 qutrit 记录，使任意单份边缘完全没有输入信息，而任意两份联合访问可以恢复输入振幅。

### 100.1 三份编码

输入标签取 $$s\in\mathbb Z/3\mathbb Z$$。对每个 $$s$$，编码支持在三元组

$$
(j,\,j+s,\,j+2s),
\qquad j\in\mathbb Z/3\mathbb Z,
$$

上，并以 $$1/\sqrt3$$ 归一化。对任意输入振幅函数 $$\psi(s)$$，这给出一个三 qutrit 联合态。

编码的关键是：单个坐标只保留一个线性组合后的 qutrit，而两坐标的差值携带 $$s$$。这不是把每个记录份额单独写成完整输入副本。

### 100.2 任意单份边缘完全混合

项目定理 `qutrit_single_share_maximally_mixed` 证明，对任意输入密度态 $$\rho$$ 和任意份额索引 $$i\in\{0,1,2\}$$，取其余两坐标的偏迹后都有

$$
\boxed{
\rho_i
=\frac13 I_3.
}
$$

因此单份记录对输入标签、输入相位和输入混合权重都不携带可读信息。这个结论是完整密度矩阵等式，而不是只比较某一个统计量。

它给出了“当前局部读数相同但整体不同”的一个编码实例：不同 $$\rho$$ 的每个单份边缘都相同，但三份联合态仍然可以不同。

### 100.3 任意两份的显式恢复

对任意循环相邻的两份，项目定义置换解码

$$
(a,b)\longmapsto(b-a,\,2b-a).
$$

`qutrit_two_share_reconstruction` 证明，应用该置换后，两份联合振幅可写成

$$
\psi(a)
\times
\left[
\frac1{\sqrt3}
\sum_j
\mathbf 1_{(b,r)=(j,j)}
\right],
$$

其中第二因子是与输入无关的固定纠缠因子。于是输入振幅 $$\psi$$ 被恢复到第一解码坐标，剩余坐标只保留固定辅助态。

因此该具体编码满足

$$
\boxed{
\text{任意一份：完全隐藏};
\qquad
\text{任意两份：可逆恢复}.
}
$$

### 100.4 对历史预算的含义

这个实例说明，“保留几份记录”不能脱离访问协议回答。若未来任务只允许访问一份，所需的经典接口只能报告一个与输入无关的最大混合态；若允许访问两份，联合差分结构立即恢复输入。记录数相同但访问集合不同，也会产生不同的可预测性。

它还区分了三种资源：

$$
\text{份额数量}
\not\equiv
\text{单份边缘信息量}
\not\equiv
\text{联合恢复能力}.
$$

三 qutrit 代码中每份边缘的信息量为零，但两份的联合恢复能力是完整的。故不能用“每份都看不见”推出“整体没有历史”，也不能用“总 Hilbert 维数”直接代替任务所需的最小访问份额。

### 100.5 与 Zeckendorf 记录的接口

若把有限 Zeckendorf 合法构型分配到多个记录份额，必须先指定编码映射与可访问集合。Fibonacci 合法性只约束哪些构型标签存在；它不自动决定一份记录是否隐藏、两份是否恢复，也不自动产生阈值共享的线性解码器。

可以把三 qutrit 结果作为一个设计模板：选择份额映射，使单份效果落入当前可见空间的核，而联合份额的效果进入目标闭包。随后再用前面的 `all_future_statistics_sufficiency` 或 `future_statistics_iff_annihilates_infinite_system` 检验联合访问是否足以覆盖所需未来统计。

本节复用 `qutrit_single_share_maximally_mixed`、`qutrit_two_share_reconstruction` 和 `qutrit_matrix_unit_marginal`。Lean 已证明的是该三 qutrit 编码的精确偏迹与两份解码；它没有证明任意 Zeckendorf 编码都存在同样的阈值，也没有给出噪声下的最优份额数。

## 追加锚（新终端）

## 101. Zeckendorf 频率相位与顺序遗失

前面的记录模型说明历史差异可以藏在相位或相关中。本节把算术卷的 Zeckendorf 位直接接到仓库已有的素数频率相位模块，得到一个明确的边界：刻度位可以选择相位频率，但单一标量相位会忘掉步骤顺序。

### 101.1 Zeckendorf 位选择两种黄金步长

对素数 $$p$$ 和层数 $$\ell$$，项目定义一步频率增量

$$
\omega_{p,\ell}
=
\operatorname{primeLayerFrequency}(p,\ell+1)
-
\operatorname{primeLayerFrequency}(p,\ell).
$$

`prime_step_frequency_zeckendorf` 证明，最低 Zeckendorf 位决定两种频率之一：

$$
\boxed{
\begin{aligned}
2\notin\operatorname{wdigits}(\ell)
&\Longrightarrow
\omega_{p,\ell}=\varphi^2\log p,\\
2\in\operatorname{wdigits}(\ell)
&\Longrightarrow
\omega_{p,\ell}=\varphi\log p.
\end{aligned}
}
$$

相应的单位圆相位为

$$
\Phi_{p,\ell}(t)
=
\exp\!\left(i\,t\,\omega_{p,\ell}\right).
$$

`prime_step_phase_euler` 和 `prime_step_phase_norm` 给出

$$
\Phi_{p,\ell}(t)
=\cos(t\omega_{p,\ell})+i\sin(t\omega_{p,\ell}),
\qquad
|\Phi_{p,\ell}(t)|=1.
$$

所以在这个明确模型中，Zeckendorf 位改变的是旋转速度；它本身不产生衰减。长步还满足

$$
\exp(i t\varphi^2\log p)
=
\exp(i t\varphi\log p)\,
\exp(i t\log p),
$$

因为 $$\varphi^2=\varphi+1$$。这是一条频率分解，不是说物理系统必然存在两个独立的记录寄存器。

### 101.2 标量相位的交换律会抹掉顺序

对任意有限频率列表 $$(\omega_1,\ldots,\omega_m)$$，定义标量相位积

$$
\Pi(t)
=\prod_{r=1}^{m}\exp(-i t\omega_r).
$$

`ordered_phase_product_collapse` 证明

$$
\boxed{
\Pi(t)
=\exp\!\left(-i t\sum_{r=1}^{m}\omega_r\right).
}
$$

因此任意排列都给出同一个标量结果：

$$
\Pi_{(\omega_1,\ldots,\omega_m)}(t)
=
\Pi_{(\omega_{\pi(1)},\ldots,\omega_{\pi(m)})}(t).
$$

`adjacent_step_order_invisible` 将这个边界写成相邻两步的交换律。它不是说原始历史不存在，而是说**在只保留一个复标量相位的读出中，顺序没有可见坐标**。

这与第 96 节的仪器反例相互补：第 96 节中，静态 POVM 丢掉了分支后的更新；本节中，标量相位读出丢掉了频率序列的排列信息。两者都说明当前读数相同不等于后续过程相同。

### 101.3 “共振”必须区分相位与振幅

`PrimeGoldenComplexMode` 将一个素数模式写成

$$
M_p(\sigma,t)
=
\exp\!\left(-\sigma\,\lambda_p\right)
\exp\!\left(i t\lambda_p\right),
$$

其中 $$\lambda_p$$ 是指定的黄金素数谱值。于是

$$
|M_p(\sigma,t)|=\exp(-\sigma\lambda_p).
$$

当 $$\sigma>0$$ 时，源码定理 `first_golden_complex_mode_injective_of_pos` 证明模长读出对素数保持单射；当 $$\sigma=0$$ 时，所有模式模长都等于一，而 `finite_zero_sigma_complex_mode_recurrence` 证明有限素数集的相位可以在任意晚时间重新接近完全相干：

$$
\forall\varepsilon>0,\ \forall B>0,
\quad
\exists t>B,
\quad
|M_p(0,t)-1|<\varepsilon
\quad\text{对有限个 }p.
$$

因此“出现振荡”不等于“出现可区分记录”：

$$
\boxed{
\text{振幅衰减提供可校准的大小差异；}
\quad
\text{纯相位运动可以长期回归而不留下单调记录。}
}
$$

### 101.4 需要什么才能保留历史顺序

若任务只关心总频率 $$\sum_r\omega_r$$，标量相位足够；若任务关心 Zeckendorf 步骤的先后、素数轴切换或进位路径，则至少需要下列一种扩展：

$$
\boxed{
\text{时间分辨的连续读出},
\quad
\text{非交换算子乘积},
\quad
\text{或可再次访问的记忆寄存器}.
}
$$

在非交换升格中，两个步骤一般是

$$
U_2U_1\ne U_1U_2,
$$

顺序才会进入可观测量；在标量 $$U(1)$$ 层，交换律会把这部分信息全部压掉。这个区别与第 97 节的未来分离深度、第 98 节的切口 bond、第 100 节的联合份额访问共同说明：历史预算取决于允许的读出代数，而不是只取决于合法 Zeckendorf 标签的数量。

本节复用 `prime_step_frequency_zeckendorf`、`prime_step_phase_euler`、`long_step_phase_factorization`、`ordered_phase_product_collapse`、`adjacent_step_order_invisible` 和 `complex_mode_amplitude_phase_dichotomy`。Lean 已证明的是这些显式频率—相位模型中的代数关系；它没有证明物理系统必然采用该频率定义，也没有把标量相位自动升级为量子 Hamiltonian 或实验共振谱。

## 102. 时间有序记忆曲率：顺序何时重新进入观测

第 101 节给出一个严格边界：如果每一步只留下一个复标量相位，那么不同频率的乘积落入交换的 $$U(1)$$，步骤排列会被压成总频率。仓库中另一个更强的构造说明，顺序信息并不必然消失；它可以转移到一个被保留、并再次参与演化的记忆坐标。

### 102.1 同一个完整寄存器上的逐槽演化

`SequentialRegisterCircuit` 把寄存器写成

$$
\operatorname{Register}(A,K,n)=(\operatorname{Fin}(n)\to A)\times K.
$$

第一因子保存已经访问过的物理槽，第二因子是共享记忆。`firstGate` 和 `tailGate` 都是同一个完整 Hilbert 空间上的幺正等距同构；`partial_circuit_succ_gate` 进一步给出：第 $$m+1$$ 步是在保留全部槽的空间上，追加一个明确的局部门

$$
\operatorname{partialCircuit}(U,n,m+1,t)
=
\operatorname{partialCircuit}(U,n,m,t)\circ
\operatorname{slotGate}(U(t+m),n,m).
$$

因此，未被当前读出的槽并没有从整体动力学中删除。它们仍可在以后门中参与作用。对空白初态，`circuit_blank_succ` 与 `circuit_basis_coefficients` 将最终振幅递归为有限链的系数；这正是“历史被保留为可再次访问的寄存器”而不是“历史已经被重新命名为一个当前数值”的形式化版本。

这一区别很重要：若每一步都把旧寄存器替换成新的无记忆环境，可以得到逐步通道的乘法衰减；若同一寄存器继续参与，后续门会看到旧的相关性，顺序效应就可能返回。

### 102.2 时间有序事件的仿射记忆律

在 `TimeOrderedPrimeMemoryCocycle` 中，一个带时间的事件包含局部标量因子 $$\lambda$$、基准注入 $$b$$、频率 $$\omega$$ 和时间 $$t$$。实际注入为

$$
\widetilde b
=
\exp(-i t\omega)b.
$$

给定稳定因子 $$a$$，它作用在二元状态 $$ (x,m) $$ 上的更新为

$$
(x,m)
\longmapsto
\bigl(a x+\widetilde b\,m,\;\lambda m\bigr).
$$

对事件列表 $$W=(e_1,\ldots,e_n)$$，源码定理 `time_ordered_evolution_affine` 证明整体作用仍是上三角仿射形式：

$$
(x,m)
\longmapsto
\left(
 a^n x+M_a(W)m,
 \Lambda(W)m
\right),
$$

其中 $$\Lambda(W)=\prod_r\lambda_r$$ 是标量词，而 $$M_a(W)$$ 是记忆坐标的有序累积。

对前后两段事件词，`time_ordered_cocycle_append_laws` 给出精确拼接律

$$
\Lambda(W_1W_2)=\Lambda(W_1)\Lambda(W_2),
$$

以及

$$
M_a(W_1W_2)
=
 a^{|W_2|}M_a(W_1)+M_a(W_2)\Lambda(W_1).
$$

第二式不是普通的交换乘法。后发生的词会把先发生的记忆注入乘上稳定传播因子；先发生的标量又会调制后续记忆。顺序因此进入一个半直积样的仿射结构，即使标量坐标本身仍然满足交换乘法。

### 102.3 两步交换曲率是顺序的最小见证

对两个事件 $$P,Q$$，`time_ordered_two_event_swap_curvature` 证明：交换次序时，标量输出完全相同，而记忆坐标的差为

$$
\Delta_{P,Q}
=
(a-\lambda_Q)\widetilde b_P
-
(a-\lambda_P)\widetilde b_Q.
$$

也就是

$$
\boxed{
M_a(PQ)-M_a(QP)=\Delta_{P,Q}.
}
$$

如果初始记忆为 $$m$$，完整状态的第一坐标差为 $$\Delta_{P,Q}m$$；第二坐标相同。于是：

$$
\text{标量读出相同}
\quad\not\Rightarrow\quad
\text{联合状态相同}.
$$

`PrimeSwapCurvature.prime_swap_curvature_spec` 还证明三件事：

$$
\Delta_{Q,P}=-\Delta_{P,Q},
$$

记忆原点变换

$$
\widetilde b_r\mapsto
\widetilde b_r+(a-\lambda_r)c
$$

不改变 $$\Delta_{P,Q}$$，并且在两个共振间隙非零时，

$$
\Delta_{P,Q}
=
(a-\lambda_P)(a-\lambda_Q)
\left(
\frac{\widetilde b_P}{a-\lambda_P}
-
\frac{\widetilde b_Q}{a-\lambda_Q}
\right).
$$

因此交换曲率不是任意坐标选择造成的假象。它是一个对记忆原点平移不变的顺序缺陷；曲率为零，当且仅当两个事件给出的局部观测者原点估计相同（在非共振条件下）。

### 102.4 Zeckendorf 频率进入记忆，而不仅是标量相位

把第 101 节的 Zeckendorf 频率选择接入事件频率：

$$
\omega_{p,\ell}
=
\begin{cases}
\varphi^2\log p,&2\notin\operatorname{wdigits}(\ell),\\
\varphi\log p,&2\in\operatorname{wdigits}(\ell).
\end{cases}
$$

则两个事件的有效注入为

$$
\widetilde b_{p,\ell}
=
\exp(-it\omega_{p,\ell})b_{p,\ell}.
$$

Zeckendorf 位仍只决定局部旋转速度；顺序是否可见，取决于这些旋转后的注入是否进入共享记忆，以及稳定因子与局部因子是否产生非零曲率：

$$
\Delta_{P,Q}
=
(a-\lambda_Q)e^{-it_P\omega_P}b_P
-
(a-\lambda_P)e^{-it_Q\omega_Q}b_Q.
$$

所以同一组 Zeckendorf 标签可以有两种完全不同的接口：

$$
\Delta_{P,Q}=0
\quad\Longrightarrow\quad
\text{该记忆读出对这次交换不可见},
$$

而

$$
\Delta_{P,Q}\ne0
\quad\Longrightarrow\quad
\text{在访问记忆坐标的后续实验中，顺序可被区分}.
$$

这把“历史是否存在”改写成了可计算问题：不是问标签是否记录了先后，而是问允许的读出是否包含一个对交换曲率敏感的记忆坐标。

### 102.5 对“需要保留多少历史”的新结论

现在至少可以区分三个层次：

$$
\boxed{
\begin{aligned}
\text{只保留标量相位}
&\Rightarrow\text{顺序按交换律折叠};\\
\text{保留共享记忆的一维坐标}
&\Rightarrow\text{两步顺序由 }\Delta_{P,Q}\text{ 检验};\\
\text{保留完整寄存器与访问协议}
&\Rightarrow\text{可继续检验更长词的历史回流}.
\end{aligned}
}
$$

因此，“稳定经典现实”所需的历史预算不能只按记录次数或 Zeckendorf 合法字串数量计数。对一个给定实验族，最小预算至少要保留所有会在预测窗口内产生非零交换曲率、回流核或联合恢复效应的坐标。若任务只问总频率，标量接口可能已经闭合；若任务问路径顺序、素数轴切换或可逆恢复，就必须保留共享记忆，或保留足以重建它的寄存器子空间。

本节直接复用 `SequentialRegisterCircuit` 的逐槽幺正组合、`time_ordered_evolution_affine` 的仿射演化、`time_ordered_cocycle_append_laws` 的时间有序拼接律、`time_ordered_two_event_swap_curvature` 的交换缺陷，以及 `prime_swap_curvature_spec` 的反对称性与规范不变性。Lean 已证明这些有限列表和有限寄存器模型中的精确代数关系；它没有证明所有物理系统都具有该记忆坐标，也没有把非零曲率自动等同于实验上已经完成的测量。后者仍取决于实际可访问的读出、噪声模型和预测时间窗。

## 103. 连续可见流与离散隐藏扇区

时间有序记忆说明了“已有记忆怎样让顺序返回”。Solenoid 模块补上另一个边界：有些隐藏差异不是被连续动力学慢慢抹平，而是根本不属于同一个连续路径扇区。

### 103.1 每条连续历史的唯一分解

`universal_solenoid_visible_hidden_motion_classification` 证明，任意连续历史 $$\gamma:\mathbb R\to\operatorname{UniversalSolenoid}$$ 都有唯一数据

$$
(a,h)\in C(\mathbb R,\mathbb R)\times\operatorname{projection.ker}
$$

使得

$$
\boxed{
\gamma(t)=\operatorname{realFlow}(a(t))+h.
}
$$

其中 $$a(t)$$ 是可见的实流坐标，而 $$h$$ 是恒定的隐藏偏移；`frozen_streamline_throat_component_constant` 进一步把对应隐藏地址写成恒定的 $$\operatorname{hiddenKernelAddEquiv}^{-1}(h)$$。于是，在只允许连续实流操作的实验族中，状态自然分解为

$$
\text{可见相位流}\times\text{隐藏扇区标签}.
$$

这给出了一个比“历史可能存在”更严格的闭合候选：如果任务只允许沿 $$\operatorname{realFlow}(t)$$ 演化，那么隐藏扇区可以作为守恒的块索引；若只看投影，则它是一个潜变量。

### 103.2 同投影不等于同一连续可达类

同一投影纤维中的两个点不一定能由连续路径连接。`visible_path_hidden_address_dichotomy` 给出

$$
\operatorname{Joined}(x,y)
\iff
\exists t\in\mathbb R,
\quad
 y=\operatorname{realFlow}(t)+x.
$$

更精确地说，底层 `same_fiber_path_orbit_criterion` 将同投影时的可达时间收缩到整数轨道；若两个点的隐藏坐标不同，分类定理构造出非零整数作用

$$
\operatorname{jump}:\mathbb Z\to\operatorname{HiddenAddress}
$$

并证明不存在连续加法流把整数嵌入延拓为该跳跃：

$$
\neg\exists\,\operatorname{flow}:\mathbb R\to\operatorname{HiddenAddress},
\quad
\operatorname{flow}|_{\mathbb Z}=\operatorname{jump}.
$$

因此跨扇区变化若要发生，必须由离散操作、显式记忆寄存器或改变实验协议来承担。它不能被悄悄解释成同一连续相位的更细刻度。

这里有一个必须保留的拓扑限制：该结果说的是连续路径可达性与隐藏地址的刚性，不是说整个空间不连通。源码同时证明 UniversalSolenoid 连通而非道路连通；拓扑连通与连续路径可达是两种不同性质。

### 103.3 对经典接口的影响

设粗观察只保留投影 $$\pi(x)$$，而不保留隐藏商坐标

$$
 c(x)=\operatorname{QuotientAddGroup.mk'}(\operatorname{range}(\operatorname{realFlowHom}))(x).
$$

对仅由连续实流组成的操作族，有

$$
 c(\gamma(t))=c(\gamma(0)).
$$

所以这类操作下，丢掉 $$c$$ 不会在同一连续扇区内立即造成预测分裂；它只是把不同扇区压进同一个粗标签。可是，一旦实验族加入离散 jump、可访问的隐藏寄存器，或第 102 节中的共享记忆回流，两个原先相同的粗读数就可能在后续被分开。

因此预测闭合必须带有操作族下标：

$$
\text{closure}\bigl(\pi,\mathfrak T_{\mathrm{continuous}}\bigr)
\ne
\text{closure}\bigl(\pi,\mathfrak T_{\mathrm{continuous}}\cup
\mathfrak T_{\mathrm{jump}}\bigr).
$$

这把“保留多少历史”具体化为：先规定允许的时间操作，再判断隐藏扇区是否可以安全商掉。若未来协议允许跨扇区访问，当前的经典接口必须补回 $$c$$，或保留一个能恢复它的记忆寄存器。

本节使用 `visible_path_hidden_address_dichotomy` 与 `universal_solenoid_visible_hidden_motion_classification` 的现成结论。Lean 已证明的是 UniversalSolenoid、连续路径和 HiddenAddress 之间的这些结构关系；它没有证明现实物理系统必然采用该拓扑模型，也没有把“隐藏扇区”自动识别成实验中的某个具体粒子或场。

## 104. 切口 Schmidt 谱：记忆维数之外还要保留哪些历史权重

第 98 节给出了精确相干制备的切口秩下界。`CoherentHistorySchmidt` 进一步计算这个切口中每个边界扇区的权重，因此可以区分“必须保留多少个正交方向”和“哪些方向对当前任务贡献最大”。

### 104.1 完整历史矩阵按边界因子化

取一个有限占据多重集 $$a$$，把总长度写成

$$
|a|=t+s.
$$

令 $$u$$ 是长度 $$t$$ 的前缀，$$v$$ 是长度 $$s$$ 的后缀。源码定义完整合法词的系数矩阵

$$
C_a^{t,s}(u,v)
=
\\begin{cases}
\\operatorname{multiplicity}(|a|,a)^{-1/2},
&\\operatorname{occupation}(u\\mathbin{+!!+}v)=a,\\\\
0,&\\text{否则}.
\\end{cases}
$$

`coefficient_factorization` 证明它可以经过边界集合分解：

$$
C_a^{t,s}=P_{a,t}Q_{a,t,s},
$$

其中中间指标 $$b\\in\\operatorname{Boundary}(a,t)$$ 记录前缀占据，后缀占据被确定为 $$a-b$$。这说明切口记忆不是任意压缩标签，而是前缀与后缀仍然能够匹配的边界扇区。

选取每个边界的代表词后，`coefficient_diagonal_restriction` 给出一个对角子矩阵：

$$
C_a^{t,s}(u_b,v_c)
=
\\begin{cases}
\\operatorname{multiplicity}(|a|,a)^{-1/2},&b=c,\\\\
0,&b\\ne c.
\\end{cases}
$$

所以 `coefficient_rank` 得到精确等式

$$
\\boxed{
\\operatorname{rank}(C_a^{t,s})
=
|\\operatorname{Boundary}(a,t)|.
}
$$

第 98 节的 bond 下界因此可以被理解为 Schmidt 秩下界：任何精确实现同一纯历史振幅的切口，都必须至少携带这么多彼此独立的边界方向。

### 104.2 每个边界方向的 Schmidt 权重

源码进一步定义边界 $$b$$ 的 Schmidt 系数

$$
\\lambda_b
=
\\frac{
\\sqrt{\\operatorname{multiplicity}(t,b)}
\\sqrt{\\operatorname{multiplicity}(s,a-b)}
}{
\\sqrt{\\operatorname{multiplicity}(t+s,a)}
}.
$$

`schmidt_coefficient_sq` 和 `schmidt_coefficient_sq_binomial` 证明

$$
\\boxed{
\\lambda_b^2
=
\\frac{
\\operatorname{multiplicity}(t,b)\\,\\operatorname{multiplicity}(s,a-b)
}{
\\operatorname{multiplicity}(t+s,a)
}
=
\\frac{
\\displaystyle\\prod_z
\\binom{a(z)}{b(z)}
}{
\\binom{t+s}{t}
}.
}
$$

这些权重之和为一，因为它们来自完整均匀合法词的边界分解。于是一个切口有两个不同的复杂度量：

$$
\\begin{aligned}
\\text{精确记忆维数}&=|\\operatorname{Boundary}(a,t)|,\\\\
\\text{历史权重分布}&=(\\lambda_b^2)_b.
\\end{aligned}
$$

前者回答“零误差地保留全部相干需要多少维”；后者回答“若只允许近似预测，哪些边界方向承载主要概率质量”。不能从第二个量的集中性直接推出第一个量可以在精确任务中减少。

### 104.3 精确压缩与近似压缩的边界

若任务要求保留完整纯态的所有振幅，任何丢弃一个 $$\\lambda_b\\ne0$$ 的边界方向都会降低切口 Schmidt 秩，因此不可能由同一较小 bond 精确实现。若任务只要求某个有限观测族的近似预测，可以按权重排序选取一个子集 $$S$$，并定义被丢弃的质量

$$
\\varepsilon_S^2
=
\\sum_{b\\notin S}\\lambda_b^2.
$$

在标准纯态 Schmidt 截断解释下，$$\\varepsilon_S$$ 是态向量级别的尾部范数；但把它转成具体测量概率、迹距离或多步预测误差，还需要指定归一化、测量族和后续动力学。仓库当前定理证明了 $$\\lambda_b$$ 的精确公式，没有自动证明任意截断协议的统一实验误差界。

因此可以把“历史保留多少”拆成两个问题：

$$
\\boxed{
\\begin{aligned}
\\text{精确相干任务:}&\\quad
\\text{保留全部非零边界方向};\\\\
\\text{有限精度任务:}&\\quad
\\text{给定预测族后控制被丢弃 Schmidt 尾部及其回流}.
\\end{aligned}
}
$$

第二行仍要与第 79、86 节的未来 observable 闭包结合。一个很大的 Schmidt 尾部如果完全落在实验不可见方向，未必造成可见误差；一个很小的尾部若被后续操作放大或回流，也不能仅凭当前质量安全丢弃。

### 104.4 与 Zeckendorf 合法空间的严格接口

对禁止相邻两个 $$1$$ 的 Zeckendorf 合法集合 $$\\mathcal W_L$$，可以把每个合法字串按切口分成前缀和后缀，并令边界集合只保留满足跨切口相邻约束的占据模式。若能证明该受限系数矩阵具有与某个 occupation sector 相同的因子化，则可以把上面的边界秩和 Schmidt 权重转移到 Zeckendorf 模型。

但这一步目前不能直接从 `CoherentHistorySchmidt` 得出。现有定理的词空间是由有限多重集占据约束定义的；它没有证明“禁止相邻 $$11$$”与某个固定多重集 sector 的系数矩阵同构，也没有给出受限边界的闭式 Schmidt 谱。因此目前只能保留如下条件性桥：

$$
\\text{若给定 Zeckendorf 振幅能因子化为边界扇区，}
\\quad
\\text{则其精确切口记忆下界等于该边界矩阵的秩。}
$$

这正是下一步可形式化的具体目标：构造一个带相邻约束的系数矩阵，证明其切口因子化，再比较其秩与 Fibonacci 合法构型数 $$F_{L+2}$$。不能把一般 occupation 的 Schmidt 权重直接冒充 Zeckendorf 量子模型的实验谱。

本节复用 `coefficient_factorization`、`coefficient_rank`、`schmidt_coefficient_sq`、`schmidt_coefficient_sq_binomial` 和 `normalized_coefficient_factorization`。Lean 已证明的是有限占据 sector 的精确切口分解、秩和权重；Zeckendorf 相邻约束的 Schmidt 理论、近似截断的多步误差以及对应的物理编码仍保持为条件性或开放问题。

## 105. 预测商：稳定对象是未来响应的最大不变商

前几节分别给出了切口记忆、共享寄存器和隐藏扇区的例子。它们可以被一个更一般的有限状态构造统一：不是先猜一个“真正对象”的内部标签，而是从当前读出和更新规则反复检查哪些历史在未来仍会分开。

### 105.1 有限未来关系逐步细化

设状态空间为 $$Y$$，更新为 $$\tau:Y\to Y$$，当前读出为 $$q:Y\to O$$。定义长度 $$m$$ 的未来关系

$$
R_m(y,y')
\iff
q(\tau^k y)=q(\tau^k y')
\quad\text{对所有 }0\le k\le m.
$$

`finite_horizon_kernel_succ_iff` 精确给出

$$
R_{m+1}(y,y')
\iff
R_m(y,y')
\land
q(\tau^{m+1}y)=q(\tau^{m+1}y').
$$

所以每增加一个未来坐标，关系只会细化，不会重新合并：

$$
m\le n\quad\Longrightarrow\quad R_n\subseteq R_m.
$$

若某一对状态在前 $$m$$ 步相同、在第 $$m+1$$ 步第一次不同，`finite_horizon_first_new_coordinate_strict` 证明

$$
R_{m+1}\subsetneq R_m.
$$

这把“隐藏历史何时重新出现”变成一个可枚举的首次分离深度，而不是一句关于无限历史的直觉。

### 105.2 完整未来核与最大的前向不变关系

把所有未来读出合并为完整 itinerary：

$$
\operatorname{Itin}(y)
=
\bigl(q(y),q(\tau y),q(\tau^2y),\ldots\bigr).
$$

完整未来核为

$$
R_\infty(y,y')
\iff
\operatorname{Itin}(y)=\operatorname{Itin}(y').
$$

`complete_kernel_eq_iInf_finite_horizon` 证明它是有限未来核的无穷交：

$$
R_\infty=\bigcap_{m\ge0}R_m.
$$

更强的 `predictive_completion_maximal_invariant_quotient` 把它刻画为当前读出核中的最大前向不变关系：

$$
R_\infty
=
\operatorname{gfp}(\mathcal R),
$$

其中 $$\mathcal R$$ 保留当前读出相同，并要求关系在 $$\tau$$ 下继续保持。于是 canonical quotient

$$
Y_{\mathrm{pred}}=Y/R_\infty
$$

携带唯一下降的读出与更新。它正是“相对于这组更新和读出，未来响应完全相同”的最粗状态空间。

这里的“最粗”有明确方向：若两个状态在 $$Y_{\mathrm{pred}}$$ 中被识别，它们所有未来读出都相同；若一个摘要仍能精确预测全部未来读出，则它必须细于或等价于这个商。

### 105.3 任何精确历史接口都因子化到预测商

设另一个记忆摘要为 $$r:Y\to M$$，并且当前读出与更新都通过它因子化：

$$
q=\bar q\circ r,
\qquad
r\circ\tau=\bar\tau\circ r.
$$

`predictive_memory_minimal_quotient` 证明存在唯一映射

$$
\theta:\operatorname{range}(r)\to Y_{\mathrm{pred}}
$$

使得 canonical projection 满足

$$
\operatorname{completionProjection}
=
\theta\circ\operatorname{rangeFactorization}(r).
$$

因此，任何能够精确预测所有未来读出的记忆接口，都会唯一映射到 canonical predictive state。这个结论比“某个编码看起来够用”更严格：它给出所有 exact predictive memories 的共同目标，而不要求先指定哪一个内部标签才是真实对象。

`prediction_completion_universality` 还说明，若当前读出和一步更新已经通过某个粗状态半共轭因子化，那么完整未来 itinerary 自动通过同一个粗状态因子化。换句话说，真正的闭合条件一旦成立，不需要为每个未来时刻重新发明一个独立记录。

### 105.4 有限状态何时可以停止继续保留历史

若 $$Y$$ 有限，`finite_horizon_stabilizes_at_completionDepth` 给出某个有限深度 $$H_*$$，使

$$
R_{H_*}=R_\infty.
$$

`FiniteHistoryPermanentStability` 的对应结论更局部：如果某一步的相等关系已经不再细化，即

$$
R_m=R_{m+1},
$$

则对所有 $$r\ge0$$ 都有

$$
R_{m+r}=R_m.
$$

所以“现在没有新分离”只有在这个等式对全部状态成立时才是停止证据；一条样本轨迹暂时没有分开，不能推出全局闭合。

在线性有限维模型中，`FutureReadoutQuotient` 给出同一结构的商版本。对状态空间 $$V$$、线性更新 $$T$$ 和读出 $$C$$，隐藏子空间为

$$
\mathcal N_\infty
=
\bigcap_{k\ge0}\ker(C\circ T^k).
$$

商空间 $$V/\mathcal N_\infty$$ 携带唯一诱导动力学，并恢复所有未来读出。`MaximalUnobservableSubspace.future_kernel_is_maximal_invariant` 进一步说明 $$\mathcal N_\infty$$ 是当前不可见空间中最大的 $$T$$-不变部分；这正是“不会在未来回流到可见读出”的隐藏方向，而不是所有当前看不见方向的简单集合。

### 105.5 与 Zeckendorf 和量子记忆的接口

若把长度 $$L$$ 的 Zeckendorf 合法构型作为初始状态集 $$Y=\mathcal W_L$$，并把一个具体量子或经典更新协议投影成 $$\tau$$ 与 $$q$$，则历史预算应按以下顺序计算：

$$
\boxed{
\begin{aligned}
\text{合法构型数}&=F_{L+2},\\
\text{未来预测商大小}&=|\mathcal W_L/R_\infty|,\\
\text{有限停止深度}&=\min\{m:R_m=R_\infty\},\\
\text{量子精确载体}&\text{还需满足相应切口秩、POVM 或完全正编码约束}.
\end{aligned}
}
$$

第一行是 Zeckendorf 的组合计数；第二、三行依赖实际更新和读出，不能由 Fibonacci 数自动给出；第四行又把预测商与量子可实现性区分开来。若记录通道留下共享相干，经典商可能过早合并状态；若所有未来读出都已在商上闭合，则继续保留更细的历史只增加成本，不增加该任务的预测力。

因此，对“用多少约束保留历史才能得到稳定经典现实”的最精确回答是：先计算允许实验族的完整未来核，再取其最大前向不变商；只有在这个商还能由物理记忆、测量和动力学实现时，它才是一个可交付的经典接口。

本节复用 `finite_horizon_kernel_succ_iff`、`finite_horizon_kernel_antitone`、`complete_kernel_eq_iInf_finite_horizon`、`finite_horizon_stabilizes_at_completionDepth`、`predictive_completion_maximal_invariant_quotient`、`predictive_memory_minimal_quotient`、`prediction_completion_universality` 与 `future_readout_quotient_is_coarsest_with_unique_dynamics`。Lean 已证明的是这些有限状态和有限维线性模型中的核、商与唯一因子关系；将其具体实例化到 Zeckendorf 受限量子通道、噪声环境和实验成本函数，仍是后续形式化目标。

## 106. 操作族扩大后的历史预算：从单一路径到受控闭合

第 105 节固定了一个更新 $$\tau$$。真实的实验协议通常还允许选择输入、脉冲或局部门；此时只检查自然时间序列会低估历史债务。`ControlledFiniteStability` 把未来关系改为对所有有限控制词同时检查。

### 106.1 控制词关系

令有限状态为 $$Y$$，输入字母为 $$U$$，读出为 $$q:Y\to O$$，每个输入 $$u$$ 给出更新

$$
F_u:Y\to Y.
$$

对输入词 $$w=(u_1,\ldots,u_k)$$，记

$$
F_w=F_{u_k}\circ\cdots\circ F_{u_1}.
$$

深度 $$m$$ 的受控关系定义为

$$
R_m^{\mathrm{ctrl}}(y,y')
\iff
q(F_w(y))=q(F_w(y'))
\quad\text{对所有 }|w|\le m.
$$

空词包含当前读出，所以每个 $$R_m^{\mathrm{ctrl}}$$ 都细于当前读出核。完整关系为

$$
R_\infty^{\mathrm{ctrl}}(y,y')
\iff
q(F_w(y))=q(F_w(y'))
\quad\text{对所有有限控制词 }w.
$$

这比单一 $$\tau$$ 的 itinerary 更强：两个历史可能沿默认路径永远相同，但只要存在一个可执行输入词把它们分开，它们就不能在受控预测商中合并。

### 106.2 一步稳定即对所有控制词永久稳定

`controlled_finite_stability` 证明，在 $$Y,U,O$$ 都有限、读出满射且非空的条件下，如果某个深度满足

$$
R_m^{\mathrm{ctrl}}=R_{m+1}^{\mathrm{ctrl}},
$$

那么对所有 $$r\ge0$$ 都有

$$
R_{m+r}^{\mathrm{ctrl}}=R_m^{\mathrm{ctrl}}.
$$

原因是一步稳定等价于关系对每一个输入更新都不变；之后任意控制词都只能在这个不变关系内部演化。

完整受控关系还满足最大不动点刻画：

$$
R_\infty^{\mathrm{ctrl}}
=
\operatorname{gfp}(\mathcal R_{\mathrm{ctrl}}),
$$

其中 $$\mathcal R_{\mathrm{ctrl}}$$ 同时要求当前读出相同，并且对每个 $$u\in U$$ 将关系保持在自身中。它也是所有“细于当前读出且对每个控制更新不变的等价关系”中的最大者。

因此，扩大操作族只会细化预测商：

$$
\mathfrak U_1\subseteq\mathfrak U_2
\quad\Longrightarrow\quad
R_\infty(\mathfrak U_2)\subseteq R_\infty(\mathfrak U_1).
$$

一个在单一动力学下看似经典的对象，可能在加入第二种脉冲或局部重排后被分裂。这正是“相对某个操作族稳定”的精确定义。

### 106.3 深度预算由商类增长支付

定义深度商类数

$$
C_m=|Y/R_m^{\mathrm{ctrl}}|,
\qquad
C_\infty=|Y/R_\infty^{\mathrm{ctrl}}|.
$$

源码证明 $$C_m$$ 单调不减，并给出最小稳定深度 $$H_{\mathrm{ctrl}}$$ 的界：

$$
\boxed{
H_{\mathrm{ctrl}}
\le
C_\infty-|O|
\le
|Y|-|O|.
}
$$

这里使用了读出满射，因此深度零的商类数正好是 $$|O|$$；每一个尚未稳定的深度至少增加一个商类。这个界不是量子 Hilbert 维数界，也不是时间步数的物理定律，而是有限确定性控制模型中的结构预算。

若把长度 $$L$$ 的 Zeckendorf 合法集合作为有限状态集，则

$$
|Y|=|\mathcal W_L|=F_{L+2}.
$$

在一个具体受控更新族上，能够得到的只是

$$
H_{\mathrm{ctrl}}
\le
F_{L+2}-|O|,
$$

以及更精确的 $$C_\infty-|O|$$ 界。不能把 $$F_{L+2}$$ 直接解释成所需历史深度；如果许多合法构型对所有允许控制词都具有相同响应，预测商会远小于原始构型集。

### 106.4 对经典现实的操作性结论

现在“稳定”必须带有操作族标记：

$$
\boxed{
\text{稳定对象}
=
\text{受控完整响应的最大不变等价类}.
}
$$

如果只允许连续实流，103 节的隐藏扇区可以作为不被跨越的块索引；如果加入离散 jump，它们必须在受控关系中重新测试；如果加入共享量子记忆，控制词还要作用在联合寄存器上，而不能只作用在局部粗读数上。

所以增加约束并不自动产生更稳定的经典现实。约束减少初始合法构型数，操作族却可能增加未来可区分的方向。真正的历史预算是二者的交点：

$$
\text{可行历史接口}
=
\text{合法构型空间}
\big/\text{对全部允许控制词的响应等价}.
$$

本节复用 `controlled_finite_stability` 的最大不变关系、永久稳定和商类深度界。Lean 已证明的是有限状态、有限输入字母和满射读出下的受控闭合；将控制输入提升为连续脉冲、量子仪器序列或含噪声的完全正通道，需要另外定义相应的控制关系和误差度量。

## 107. 黄金禁词相位：局部约束保留，标量端点仍会遗失顺序

第 101 节只说明 Zeckendorf 位可以选择两种相位频率。`GoldenEulerGapWordConstraints` 进一步证明，这些频率并非任意二字母串：Zeckendorf 的局部结构把它们组织成一个带禁词的时间序列。

### 107.1 两种频率字母

对素数 $$p$$ 和层数 $$\ell$$，定义短、长两种步长

$$
S_p=\varphi\log p,
\qquad
L_p=\varphi^2\log p.
$$

`golden_true_selects_long_frequency` 与 `golden_false_selects_short_frequency` 证明

$$
\operatorname{goldenWord}(\ell)=\mathrm{true}
\Longrightarrow
\omega_{p,\ell}=L_p,
$$

$$
\operatorname{goldenWord}(\ell)=\mathrm{false}
\Longrightarrow
\omega_{p,\ell}=S_p.
$$

因此 Zeckendorf 位不是被动标签，而是频率字母的选择器。

### 107.2 禁词从位约束传递到相位约束

项目已有的黄金词性质给出两条局部规则：

$$
S_pS_p\quad\text{不会出现},
$$

$$
L_pL_pL_p\quad\text{不会出现}.
$$

`short_frequency_forces_next_long` 证明每个短步之后必为长步；`two_long_frequencies_force_next_short` 证明连续两个长步之后下一步必为短步。通过 `short_phase_forces_next_long` 和 `two_long_phases_force_next_short`，同样的规则传递到

$$
\Phi_{p,\ell}(t)=\exp(i t\omega_{p,\ell})
$$

构成的相位字母：

$$
S\text{-phase}\,\Longrightarrow\,L\text{-phase},
\qquad
LL\text{-phase}\,\Longrightarrow\,S\text{-phase}.
$$

这给出一个比“黄金比例出现了”更严格的结构：合法时间序列属于一个局部受限语言。它与第 102、106 节的历史预算直接相连，因为预测下一步至少需要知道当前的局部禁词上下文。

### 107.3 局部禁词不等于标量端点可恢复

尽管相位字母满足禁词，若只保留所有步的标量乘积，则

$$
\prod_{r=1}^{m}\exp(i t\omega_r)
=
\exp\left(i t\sum_{r=1}^{m}\omega_r\right).
$$

由交换律，所有满足相同字母计数的排列给出同一端点相位。于是存在这样的情形：两个序列都满足

$$
SS\text{ 不出现},
\qquad
LLL\text{ 不出现},
$$

并且包含相同数量的 $$S$$ 与 $$L$$，但其局部先后不同；它们的标量端点读出仍然相同。

所以局部约束保存了“哪些序列合法”，却没有自动保存“合法序列究竟按什么顺序发生”。要让顺序进入结果，至少要加入一种非交换或有记忆的读出：

$$
\boxed{
\text{时间分辨相位序列}
\quad\text{或}\quad
\text{共享记忆中的有序注入}
\quad\text{或}\quad
\text{非交换事件算子}.
}
$$

第 102 节的交换曲率正是第二种机制；它把相位旋转后的注入带入共享记忆坐标，使两个排列的差异不再被标量交换律抹掉。

### 107.4 与禁止相邻 $$11$$ 的 Zeckendorf 空间不要混同

本节的黄金相位字母满足的是

$$
SS\text{ 禁止},
\qquad
LLL\text{ 禁止},
$$

而第 79、98、104 节使用的有限 Zeckendorf 构型空间满足的是二进制约束

$$
11\text{ 禁止}.
$$

两者都来自 Fibonacci 型递归，但字母表、状态含义和可实现动力学不同。不能因为它们都出现 Fibonacci 数，就把黄金频率时间序列直接识别成一个禁止相邻激发的量子 Hilbert 空间。

可以建立一个条件性桥：若给定实验把 $$S/L$$ 相位字母编码为合法构型，并且联合更新保持该编码空间，那么第 105、106 节的预测商和受控稳定深度可以应用于这个有限语言。现有 Lean 结果只证明了相位字母的频率选择和禁词继承；它没有证明该相位语言存在唯一的物理寄存器编码，也没有证明其商类数等于某个 Fibonacci Hilbert 维数。

本节复用 `zeckendorf_selects_layer_gap_phase`、`golden_true_selects_long_frequency`、`golden_false_selects_short_frequency`、`short_frequency_forces_next_long`、`two_long_frequencies_force_next_short`、`short_phase_forces_next_long` 和 `two_long_phases_force_next_short`。Lean 已证明的是黄金词约束到频率与相位的精确传递；标量端点的顺序不可见性来自交换乘法，顺序恢复、物理编码和量子噪声下的稳定深度仍需另建模型。

## 108. 合法性记忆不等于历史记忆

前面已经区分了合法构型数、预测商和量子载体维数。`GoldenZeckendorfLanguage` 给出一个最小的反例：判断一个输入是否属于 Zeckendorf 合法语言，只需要记住前一个符号是否为一；但这远远不够回答该输入代表哪个整数、产生哪种相位或怎样参与后续干涉。

### 108.1 两状态自动机只负责检查局部约束

源码中的状态为

$$
Q=\{\mathrm{clear},\mathrm{previousOne}\}.
$$

转移规则是

$$
\begin{aligned}
\mathrm{clear}\xrightarrow{0}&\mathrm{clear},
&\mathrm{clear}\xrightarrow{1}&\mathrm{previousOne},\\
\mathrm{previousOne}\xrightarrow{0}&\mathrm{clear},
&\mathrm{previousOne}\xrightarrow{1}&\text{非法}.
\end{aligned}
$$

`zeckendorfMSDWord_noAdjacentOnes` 证明任意自然数的规范密集 Zeckendorf 字都满足这个语言约束；`zeckendorfMSDWord_base_success` 则证明这些字都能在该部分自动机中成功执行。

因此，对任务

$$
\text{“当前前缀后面还能不能接一个一？”}
$$

两状态确实是一个充分的有限接口。它保存的是局部合法性所需的最小上下文，而不是完整输入的数值。

### 108.2 三种不同的“记忆维数”

同一个 Zeckendorf 字可以对应至少三种不同的资源量：

$$
\boxed{
\begin{aligned}
\text{合法性记忆}&=|Q|=2,\\
\text{有限窗口构型载体}&=|\mathcal W_L|=F_{L+2},\\
\text{任务预测或相干记忆}&=\text{由未来商、切口秩和物理编码决定}.
\end{aligned}
}
$$

第一项只回答语言接受问题；第二项列出窗口中可能出现的合法基态；第三项还要考虑允许的更新、测量、相位和恢复操作。把第一项当成第二项，或者把第二项当成第三项，都会低估历史债务。

例如，两个前缀都处于 $$\mathrm{clear}$$ 状态时，它们都允许下一位为一；但它们已经累积的 Fibonacci 权重可能不同，之后的数值读数、素数频率或共享记忆注入也可能不同。自动机状态把这些前缀合并，只在“合法性”这个观察族下闭合。

### 108.3 合法性商何时可以成为经典对象

设 $$q_{\mathrm{legal}}$$ 只读出自动机状态，$$q_{\mathrm{value}}$$ 读出完整 Fibonacci 数值，$$q_{\mathrm{phase}}$$ 读出后续相位响应。一般有

$$
\ker q_{\mathrm{value}}
\subseteq
\ker q_{\mathrm{legal}},
\qquad
\ker q_{\mathrm{phase}}
\subseteq
\ker q_{\mathrm{legal}},
$$

因为数值和相位任务会区分更多前缀。只有当允许的后续实验族确实只查询合法性，并且更新不把被合并的前缀重新分开时，二状态商才满足第 105、106 节的预测闭合条件。

若加入算术读数、黄金 Euler 相位或量子干涉，必须重新计算完整未来核：

$$
R_\infty^{\mathrm{legal}}
\supseteq
R_\infty^{\mathrm{value}},
\qquad
R_\infty^{\mathrm{legal}}
\supseteq
R_\infty^{\mathrm{phase}}.
$$

商关系越小，所需历史接口越细。于是“约束减少了状态”只对指定观察任务成立；换一个任务，原先被约掉的历史可能重新成为可见差异。

### 108.4 对量子实现的边界

两状态自动机可以作为一个经典控制器，决定某个量子门是否允许施加；它本身不构成把所有合法字编码为两个正交量子态的物理实现。若要求保留合法构型的相干叠加，至少还要给出

$$
\mathcal H_{Z,L}
=
\operatorname{span}\{|w\rangle:w\in\mathcal W_L\}
$$

的编码、在该空间上保持合法性的联合演化，以及测量和恢复的完全正映射。自动机状态可以附加在寄存器上，但不能替代第 98、104 节中由切口秩决定的相干 bond。

所以一个更准确的分工是：

$$
\text{自动机}
\longrightarrow
\text{约束可执行性},
\qquad
\text{预测商}
\longrightarrow
\text{未来响应闭合},
\qquad
\text{量子寄存器}
\longrightarrow
\text{相干历史与可恢复关联}.
$$

本节复用 `ZeckendorfBaseState`、`zeckendorfBaseStep`、`zeckendorfMSDWord_noAdjacentOnes` 和 `zeckendorfMSDWord_base_success`。Lean 已证明的是规范 Zeckendorf 字的局部合法性和两状态部分自动机的成功执行；它没有证明两状态自动机足以承载数值、相位或任意量子预测任务。

## 109. 禁止相邻 `11` 的均匀态：Fibonacci 标签与 bond 维数分离

现在可以对第 104 节留下的受限 Schmidt 问题做一个完全有限的计算模型。令

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
\qquad
D_L=|\mathcal W_L|=F_{L+2},
$$

并取均匀纯态

$$
|\Psi_L\rangle
=
\frac1{\sqrt{D_L}}
\sum_{w\in\mathcal W_L}|w\rangle.
$$

这一步是一个明确指定的有限量子模型；它不是声称仓库已有的 occupation sector 定理已经覆盖了相邻约束。

### 109.1 切口只看到两种边界状态

把字串切成长度 $$t$$ 与 $$s$$ 的前后两段，其中 $$t+s=L$$ 且 $$t,s\ge1$$。定义

$$
a_0=\#\{u\in\mathcal W_t:u\text{ 以 }0\text{ 结尾}\},
\qquad
a_1=\#\{u\in\mathcal W_t:u\text{ 以 }1\text{ 结尾}\},
$$

以及

$$
b_0=\#\{v\in\mathcal W_s:v\text{ 以 }0\text{ 开头}\},
\qquad
b_1=\#\{v\in\mathcal W_s:v\text{ 以 }1\text{ 开头}\}.
$$

每个前缀和后缀的内部约束已经在 $$\mathcal W_t$$、$$\mathcal W_s$$ 中满足；跨切口唯一新增的条件是

$$
u\text{ 以 }1\text{ 结尾}
\quad\text{且}\quad
v\text{ 以 }1\text{ 开头}
\quad\Longrightarrow\quad
uv\text{ 非法}.
$$

因此，把所有相同边界类型的前缀、后缀分别归一化后，完整系数矩阵等价于

$$
M_{t,s}
=
\frac1{\sqrt{D_L}}
\begin{pmatrix}
\sqrt{a_0b_0}&\sqrt{a_0b_1}\\
\sqrt{a_1b_0}&0
\end{pmatrix}.
$$

这不是把所有合法字串粗暴合并成一个标签；它是把矩阵中真正相同的行、列向量正交化后得到的精确边界表示。

### 109.2 精确 Schmidt 秩恒为二

只要 $$t,s\ge1$$，四个边界计数都为正，且

$$
\det M_{t,s}
=
-\frac{\sqrt{a_0a_1b_0b_1}}{D_L}
\ne0.
$$

所以

$$
\boxed{
\operatorname{SchmidtRank}(|\Psi_L\rangle;t|s)=2
\qquad(1\le t,s<L).
}
$$

这给出一个很强的容量分离：合法构型总数随长度按

$$
D_L=F_{L+2}\sim\frac{\varphi^{L+2}}{\sqrt5}
$$

增长，但均匀态跨任意内部切口只需一个两维 bond。Fibonacci 数量描述的是全局标签空间大小；局部相干历史只需记录切口的两个边界状态。

### 109.3 两个 Schmidt 权重的闭式表达

由于 $M_{t,s}$ 的 Frobenius 范数为一，其两个 Schmidt 权重的平方是 $M_{t,s}M_{t,s}^{\ast}$ 的两个特征值。令

$$
\Delta_{t,s}
=
\frac{a_0a_1b_0b_1}{D_L^2}.
$$

则

$$
\boxed{
\lambda_\pm^2
=
\frac{1\pm\sqrt{1-4\Delta_{t,s}}}{2}.
}
$$

例如，中心切口的直接计算给出：

$$
\begin{array}{c|c|c|c}
L&D_L&\text{切口}&(\lambda_+^2,\lambda_-^2)\\
\hline
2&3&1|1&(0.872677996,\ 0.127322004)\\
3&5&1|2&(0.912310563,\ 0.087689437)\\
4&8&2|2&(0.933012702,\ 0.066987298)\\
5&13&2|3&(0.923076923,\ 0.076923077)\\
6&21&3|3&(0.910325903,\ 0.089674097)\\
8&55&4|4&(0.919070203,\ 0.080929797)\\
10&144&5|5&(0.915739710,\ 0.084260290)
\end{array}
$$

数值表只用于展示这个明确矩阵模型的谱；它不是对真实实验参数的测量，也不是当前 Lean 中的认证数值定理。

### 109.4 这对历史预算意味着什么

若任务是精确制备均匀合法态并允许任意切口上的相干恢复，则两维 bond 已经足够承载这个特定态族的全部跨切口相关；不需要为每个 $$F_{L+2}$$ 个合法字串分配一个独立的切口记忆槽。

若任务改为区分每个合法字串、读取完整 Fibonacci 数值，或允许能访问字串内部位置的控制操作，则预测商会变细，所需接口可能重新随 $$L$$ 增长。于是必须区分

$$
\text{均匀态的相干 bond}
\quad\ne\quad
\text{所有构型的可区分记录容量}.
$$

这也解释了第 108 节的两状态自动机为何不矛盾：自动机和两维 bond 都只是在特定任务中保留边界信息；它们都没有声称能完成所有数值和量子任务。

### 109.5 形式化边界

本节的矩阵 $M_{t,s}$、秩为二和谱公式是从有限集合的直接计数与 $2\times2$ 线性代数得到的组合推导，目前没有冒充为仓库已有 Lean 声明。下一步若要把它纳入唯一真源，需要在 D5 中定义相邻约束词空间、前后缀边界计数和对应系数矩阵，再证明其行列因子化与行列式非零。

一旦完成这一步，才能把

$$
F_{L+2}\quad\text{与}\quad 2
$$

的分离从一个可复算模型升级为形式化定理；在此之前，它只承担研究报告中的明确、可检验桥接。

## 110. 同一 Zeckendorf 语言的任务依赖状态复杂度

第 108 节的两状态自动机只检查“是否出现相邻两个一”。仓库还给出一个任务复杂度完全不同的对照：对同一类规范 Zeckendorf 输入，若任务是计算黄金比例的稀疏 radix-4 输出，则状态下界可以大得多。

### 110.1 合法性任务只需两状态

`ZeckendorfBaseState` 只有

$$
\{\mathrm{clear},\mathrm{previousOne}\},
$$

因此验证局部合法性只需保存一个比特级上下文：前一位是否为一。`zeckendorfMSDWord_base_success` 证明每个规范 Zeckendorf 输入都能在这个部分自动机中成功运行。

这个自动机并不输出输入代表的整数，也不计算黄金比例的 radix-4 数字。它的闭合任务只有语言成员关系。

### 110.2 算术输出任务需要保存更多可区分前缀

`GoldenBase4AutomataOracle` 定义了另一项任务：输入是

$$
\operatorname{zeckendorfMSDWord}(4^i),
$$

输出是

$$
\left\lfloor 4^{i+1}\varphi\right\rfloor
-4\left\lfloor4^i\varphi\right\rfloor,
$$

的 radix-4 数字。此时前缀不仅要保持合法性，还要保留足以决定未来输出的算术信息。

源码中的 `phi_base4_twenty_two_state_minimality` 给出条件性最小性结论：若存在一个 22 状态全局模型，并且对 21 状态模型的指定有限前缀反驳已经由 LRAT 证书提供，则

$$
\operatorname{IsMinimalStateCount}(\operatorname{base4Problem},22).
$$

对应的 M16 定理直接排除至多 21 状态的模型，但它的使用条件仍是显式的有限反驳证书。这里不能把“22”脱离这些前提写成无条件的现实物理常数。

### 110.3 这与量子历史预算是同一类区别

两种任务的状态数对照为

$$
\begin{array}{c|c|c}
\text{任务}&\text{必须保留的关系}&\text{现有状态规模}\\
\hline
\text{检查 Zeckendorf 合法性}&\text{最近一位的局部约束}&2\\
\text{计算稀疏黄金 radix-4 输出}&\text{未来算术输出等价类}&\text{条件性至少 }22\\
\text{均匀禁止相邻态的局部相干}&\text{切口边界}&2\\
\text{完整量子预测}&\text{未来 effect/仪器词闭包}&\text{由商空间与载体决定}
\end{array}
$$

因此“约束只产生两个状态”和“这个系统只需要两个状态”是不同命题。前者只关于一个局部语言；后者必须对指定的所有后续操作和输出任务成立。

### 110.4 对稳定经典现实的修正

如果观察者只问一个局部约束问题，二状态摘要可以是稳定经典对象。若观察者随后要求数值解码、黄金相位预测、不同控制词下的输出，二状态摘要通常不再满足第 105、106 节的预测闭合条件。对应的最小对象应改为

$$
\text{当前前缀}/\text{未来任务响应等价},
$$

而不是

$$
\text{当前前缀}/\text{局部合法性等价}.
$$

量子模型中完全相同：一个两维边界 bond 可以精确承载第 109 节的均匀相干态，但不能因此承载所有合法构型的任意数值、相位和恢复协议。任务一旦扩大，预测商会细化，必须重新计算历史预算。

本节复用 `zeckendorfMSDWord_base_success`、`m16_phi_base4_exclude_at_most_twenty_one` 和 `phi_base4_twenty_two_state_minimality`。Lean 已证明的是两状态合法性执行以及带上界模型和 LRAT 反驳前提的状态最小性接口；它没有把 22 状态结论无条件推广到所有 Zeckendorf 任务，也没有把自动机状态数等同于量子 Hilbert 维数。

## 111. 预测商的条件熵下界：标签、bond 与信息成本

前几节已经区分了三种容易混淆的数量：合法构型的总数、一个特定量子态跨切口所需的 Schmidt bond，以及为未来预测而必须保留的状态数。仓库中的 `PredictiveMemoryEntropyLowerBound.lean` 再增加一个可以直接比较的量：**在当前读出已经给定以后，记忆还必须携带多少条件熵。**

### 111.1 精确预测记忆的定义

设有限状态集合为

$$
X
$$

当前读出为

$$
q:X\to O,
$$

一步更新为

$$
F:X\to X,
$$

候选记忆接口为

$$
r:X\to M.
$$

源码中的 `IsExactPredictiveMemory q F r` 要求存在两个因子化：当前读出可以由记忆恢复，且更新后的记忆仍只依赖旧记忆。用普通数学语言写成，就是存在

$$
\bar q:M\to O,
\qquad
\bar F:M\to M
$$

使得

$$
q=\bar q\circ r,
\qquad
r\circ F=\bar F\circ r.
$$

第一条保证当前观测不会被记忆丢掉；第二条保证记忆接口对下一步操作闭合。它把前面讨论的预测闭合落实为记忆接口条件：

$$
r\circ F=\bar F\circ r.
$$

这里还显式保留当前读出因子化条件。

### 111.2 canonical predictive quotient 是所有 exact memory 的共同下界

由更新和当前读出共同决定的 canonical predictive projection 记作

$$
\pi_{F,q}:X\to Q_{F,q}.
$$

它把两个状态归并，当且仅当它们在当前读出下相同，并且在所有后续迭代中都保持相同的可预测响应。`MinimalPredictiveCompletionQuotient.lean` 以最大 forward congruence 的商实现了这一构造：它保持当前读出，承载更新，并且其投影能够因子化通过任意满足相同闭合条件的商。

因此，对于任意 `IsExactPredictiveMemory q F r`，canonical projection 在每个记忆纤维上都是常值的。于是它在实现的记忆像

$$
r(X)\subseteq M
$$

上因子化为

$$
g:r(X)\to Q_{F,q},
\qquad
\pi_{F,q}=g\circ r.
$$

若另加非空状态假设，或只讨论非零质量分支，可以选择一个延拓到整个记忆类型的函数；零状态情形不应无条件声称存在这样的全域函数。这句话的方向很重要：canonical predictive state 是候选记忆中必然包含的预测信息，而不是任意标签都能替代它。若两个历史在

$$
\pi_{F,q}
$$

中不同，任何 exact memory 都必须把它们放在可区分的记忆纤维中；否则某个后续读出会把它们分开。

### 111.3 条件熵下界

给定一个非负质量函数

$$
\mu:X\to\mathbb R,
\qquad
0\le\mu(x),
$$

定义当前读出与记忆状态的联合质量

$$
J_{q,s}(o,z)
=
\sum_{x:(q(x),s(x))=(o,z)}\mu(x).
$$

那么仓库定理 `predictive_memory_entropy_lower_bound` 精确证明：

$$
\boxed{
H\bigl(\pi_{F,q}\mid q\bigr)
\le
H\bigl(r\mid q\bigr).
}
$$

这里的熵是由上述联合质量计算的条件 Shannon 熵；定理允许质量函数只是非负而未预先归一化。总质量为零时两边都退化为零；总质量为正时，证明把该质量函数归一化，应用条件熵的数据处理不等式，再乘回总质量。因而这不是把“概率”偷偷扩展成任意带符号的线性权重。

定理中的数学关系可以压缩成：

$$
\pi_{F,q}=g\circ r
\quad\Longrightarrow\quad
H(\pi_{F,q}\mid q)\le H(r\mid q).
$$

右侧记忆可能包含额外的、对预测无用的历史；左侧只保留在未来实验中不可省略的部分。于是 canonical quotient 不只是商类最粗，还在这个有限质量模型中给出条件熵意义下的最低记忆成本。

### 111.4 与 Fibonacci 构型数和 Schmidt bond 的三重分离

对禁止相邻两个一的长度

$$
L
$$

合法语言，构型总数是

$$
|\mathcal W_L|=F_{L+2}.
$$

第 109 节的均匀态在任意非平凡切口上只有二维有效边界矩阵，所以其 Schmidt rank 为

$$
\operatorname{SchmidtRank}=2.
$$

而第 111 节的预测商条件熵是另一种量：它取决于选定的当前读出、更新、允许的未来操作族，以及质量函数。即使把质量函数归一化为概率，使指数熵具有无量纲解释，也一般不存在等式

$$
F_{L+2}
=
2
=
\exp H(\pi_{F,q}\mid q).
$$

这三个量分别回答不同问题：

$$
\begin{array}{c|c}
\text{量}&\text{回答的问题}\\
\hline
F_{L+2}&\text{有多少个合法构型}\\
2&\text{这个特定均匀态跨切口需要多少相干边界维度}\\
H(\pi_{F,q}\mid q)&\text{当前读出已知后，为预测未来还需保留多少平均信息}
\end{array}
$$

例如，若当前读出已经把所有合法字串区分开，则

$$
H(\pi_{F,q}\mid q)=0,
$$

即使合法构型数仍为

$$
F_{L+2}
$$

因为当前读出已经携带了全部预测商信息。反过来，若当前质量所支持的历史都落在同一个当前读出纤维中，而更新把它们送到当前读出可以区分的后续状态，则预测商可以在该支持上分成

$$
k
$$

个等质量的未来响应类。质量归一化为概率后，条件熵可以达到

$$
H(\pi_{F,q}\mid q)=\log k.
$$

这时任何 exact memory 的条件熵都至少为

$$
\log k.
$$

这里的

$$
k
$$

与 Fibonacci 构型总数没有必然相等关系。

### 111.5 非负质量不是装饰性条件

同一 Lean 文件中的 `nonnegative_mass_is_necessary` 给出带符号质量的反例：在两点状态上取质量

$$
2
$$

与

$$
-1,
$$

identity memory 仍然是 exact predictive memory，但条件熵下界会失败。原因不是 canonical quotient 失去共轭性，而是 Shannon 熵的数据处理不等式需要非负、可归一化的质量。

因此，以下三句话必须分开：

$$
\text{线性振幅可以是复数，}
$$

$$
\text{形式上的 signed weight 可以用于代数恒等式，}
$$

$$
\text{条件 Shannon 熵的输入必须是非负质量。}
$$

量子振幅的相位不能直接当作熵的概率权重。若要把第 111 节用于量子模型，必须先指定正的 Born 概率、密度矩阵对角分布，或其它明确的正测度。

### 111.6 对“需要保留多少历史”的精确回答

结合前面的 Zeckendorf 约束、Schmidt 分解和预测闭合，当前问题可以写成四步：

$$
\text{合法构型空间}
\longrightarrow
\text{选定读出 }q
\longrightarrow
\text{计算未来响应商 }\pi_{F,q}
\longrightarrow
\text{比较 }H(\pi_{F,q}\mid q)\text{ 与候选记忆成本}.
$$

若候选接口

$$
r
$$

达到 exact predictive memory 条件，并且其条件熵等于 canonical 下界，则在这个质量与任务下，它没有产生额外的条件熵成本；这不单独排除零质量纤维上的冗余标签。若严格大于下界，说明在这个质量和任务下存在额外的平均记忆成本；若小于下界，则它不可能仍然精确预测全部指定未来读出。

这给“稳定经典现实”一个可计算的有限版本：不是要求记忆保存全部历史，也不是只保存当前整数标签，而是保存足以使

$$
\pi_{F,q}=g\circ r
$$

成立的那部分关系，并在给定误差预算下使剩余回流可以忽略。Zeckendorf 的

$$
F_{L+2}
$$

只规定合法构型的组合规模；Schmidt bond 只规定某个态族的跨切口相干规模；条件熵下界才开始回答当前观察已经给定以后，未来预测还必须保留多少历史信息。

### 111.7 形式化边界与下一步

本节直接复用仓库已有的 `minimal_predictive_completion_quotient`、`predictive_memory_entropy_lower_bound` 与 `nonnegative_mass_is_necessary`。Lean 已证明的是有限类型、确定性更新、非负有限质量和精确记忆接口下的条件熵下界，以及带符号质量会破坏该不等式。它没有证明任意无限链、任意量子通道或任意实验噪声下都存在同一个有限熵预算。

要把它接到前面的 Zeckendorf 量子模型，还需额外指定并分别验证：

$$
\text{合法字串状态 }X,
\qquad
\text{实际更新 }F\text{ 或量子通道的有效状态更新},
$$

$$
\text{当前读出 }q,
\qquad
\text{非负的 Born 质量（总质量可为零） }\mu,
$$

以及未来操作族是否比单一步更新更丰富。若未来允许的控制词不止迭代更新，就必须把它们加入预测商的定义；不能把单一步闭合误报成对所有仪器和所有历史协议的闭合。上面的熵例子也只是在指定质量支持和后续读出结构下的条件性组合，不是对全局常数读出的断言。

所以，当前最稳固的研究命题是：

$$
\boxed{
\text{在固定读出、更新和非负有限质量之后，}
\text{canonical predictive quotient 给出 exact memory 的条件熵下界。}
}
$$

它把“保留多少历史才能得到稳定现实”从一个总量问题，改写成了一个可逐任务计算的问题：先确定未来响应等价，再测量任何候选记忆相对于当前读出的剩余信息成本。


## 112. 保留模数的乘积容量：算术记录何时足以恢复历史

第 111 节给出了预测任务下的条件熵下界。另一个更离散的问题是：如果记录接口只保留若干个模数余数，什么时候这些记录足以把一个有限状态集合完全恢复出来？仓库中的 RetainedResidueRecoveryCriterion.lean 给出一个精确的双向判据。

### 112.1 联合余数记录

设有限索引集合为

$$
\iota,
$$

每个索引携带一个正模数

$$
m:\iota\to\mathbb N,
\qquad
0<m(i),
$$

并假设这些模数两两互素：

$$
\operatorname{Pairwise}\bigl(\operatorname{Nat.Coprime}\;\mathrm{on}\;m\bigr).
$$

对状态区间

$$
\operatorname{Fin}(K)=\{0,1,\ldots,K-1\},
$$

保留的记录是联合余数读出

$$
R(x)
=
\bigl(x\bmod m(i)\bigr)_{i\in\iota}.
$$

在 Lean 中，这个读出由 jointReadout 组织，余数坐标以

$$
\mathbb Z/m(i)\mathbb Z
$$

表示。它不是把原始历史直接写回，而是把历史压缩到一组可组合的局部记录中。

### 112.2 精确恢复的充要条件

retained_residue_recovery_iff_product_capacity 证明：

$$
\boxed{
R\text{ 在 }\operatorname{Fin}(K)\text{ 上单射}
\quad\Longleftrightarrow\quad
K\le\prod_{i\in\iota}m(i).
}
$$

正向部分只是有限单射导致的基数不超过目标基数。反向部分使用有限模数的乘积同构：两两互素使联合余数同构于乘积模数，若

$$
0\le x,y<K\le\prod_i m(i)
$$

且所有保留余数相同，那么

$$
x\equiv y\pmod{\prod_i m(i)}.
$$

由于 x 和 y 都落在一个完整模周期内，只能有

$$
x=y.
$$

这里的“容量”是乘积，而不是模数个数。增加一个与已有模数互素的新记录通道，会把可无歧义恢复的状态范围按该模数倍增；但若新通道与已有通道不互素，不能直接使用同一个乘积公式。

### 112.3 与 Zeckendorf 合法构型的连接

长度参数为 L 的禁止相邻两个一语言有

$$
|\mathcal W_L|=F_{L+2}
$$

个合法构型。若先给这些构型一个双射标签

$$
e:\mathcal W_L\to\operatorname{Fin}(K),
\qquad
K=F_{L+2},
$$

再用保留模数记录标签，那么由第 112 节的判据，完整恢复所有合法构型的充分且必要条件是

$$
F_{L+2}
\le
\prod_{i\in\iota}m(i).
$$

这只是一个条件性组合桥：它要求先固定一个有限编码

$$
e
$$

以及实际使用的余数记录。Lean 定理本身证明的是任意有限区间

$$
\operatorname{Fin}(K)
$$

上的恢复，不自动构造 Zeckendorf 语言到区间的双射，也不说明物理系统真的读取这些模数。

在最小例子中，

$$
\mathcal W_3=\{000,001,010,100,101\},
\qquad
|\mathcal W_3|=5.
$$

保留模数

$$
2,\quad3
$$

时乘积为

$$
6,
$$

因此任何先编码为

$$
\operatorname{Fin}(K),
\qquad
K\le6,
$$

的有限状态都可以由这两个余数联合恢复。若只保留模数

$$
2,
$$

容量只有

$$
2,
$$

最多只能无歧义表示两个状态；五个合法构型不能全部由单个二模余数区分。

### 112.4 这不是 Hilbert 维数，也不是预测熵

乘积容量回答的是一个严格的可逆编码问题：

$$
\text{给定记录，能否唯一恢复有限标签？}
$$

它不等同于以下数量：

$$
F_{L+2},
\qquad
\operatorname{SchmidtRank},
\qquad
H(\pi_{F,q}\mid q).
$$

前者统计合法构型；Schmidt rank 描述特定量子态跨切口的线性相关维度；条件熵下界描述给定当前读出后未来预测所需的平均信息。模数乘积则描述一套离散记录接口的最坏情形无歧义容量。

例如，若当前任务只需判断一个局部约束是否合法，二状态自动机可能已经闭合；若任务要求恢复所有

$$
F_{L+2}
$$

个合法构型，就必须检查记录容量是否达到该数值。若任务只要求预测后续动力学，完整恢复甚至可能过度，因为不同构型可能属于同一个未来响应类。于是：

$$
\text{完整历史恢复容量}
\quad\ge\quad
\text{任务预测所需容量}
$$

一般只是任务依赖的比较关系，不是普适的数值等式。

### 112.5 与素数指数档案的边界

项目中的

$$
K(n)(p,j)=s\bigl(v_p(n)\bigr)_j
$$

把每个素数轴上的指数写成 Zeckendorf 行。第 112 节的余数读出可以作为另一种有限记录协议，例如对选定的状态标签保留若干互素模数；但它没有把素数指数轴自动变成余数轴，也没有证明某个具体的

$$
K(n)
$$

在余数记录下可逆。

要建立这样的桥，至少还需指定：

$$
\text{原始档案空间},
\qquad
\text{有限截断范围},
\qquad
\text{余数记录作用在哪个数值或标签上}.
$$

只有在这些数据固定后，才能把

$$
K\le\prod_i m(i)
$$

解释为该档案截断的恢复条件。否则把“素数轴很多”直接等同于“历史记录容量很大”，会把坐标数量误当成可逆信息量。

### 112.6 对稳定经典现实的补充判据

第 111 节说，稳定对象应当保留未来预测所需的 canonical quotient。第 112 节补充了一个更强、也更昂贵的选择：如果要求对象保留全部有限标签，而不是只保留预测等价类，那么必须提供一个对该标签集单射的记录接口。

因此可以区分两种预算：

$$
\text{预测预算}
=
\text{使未来响应可闭合的最小记忆},
$$

$$
\text{恢复预算}
=
\text{使目标历史标签可逆的最小记录容量}.
$$

对余数协议，恢复预算由

$$
\prod_i m(i)
$$

控制；对预测协议，预算由

$$
H(\pi_{F,q}\mid q)
$$

及其误差版本控制。恢复预算通常更高，因为它拒绝把未来行为相同的历史合并。

这使“用多少约束才能得到稳定经典现实”有了两层可检验答案：

$$
\boxed{
\begin{aligned}
&\text{若只要求稳定预测：计算 canonical predictive quotient；}\\
&\text{若要求完整历史可恢复：检查记录容量是否覆盖目标标签集。}
\end{aligned}
}
$$

两者都不自动给出物理 Hamiltonian 或量子测量定律；它们分别刻画关系结构的预测闭合和离散记录的可逆性。

### 112.7 形式化边界

Lean 已证明的是正的两两互素模数、有限索引族和有限状态区间上的精确单射充要条件。它没有证明 Zeckendorf 合法语言的某个具体物理实现会采用这些模数，也没有把乘积容量转译成 Hilbert 空间维数、实验信道容量或量子纠错阈值。

因此第 112 节当前最强的可复用结论是：

$$
\boxed{
\text{在两两互素的保留余数协议中，}
\operatorname{Fin}(K)\text{ 可被精确恢复}
\iff
K\le\prod_i m(i).
}
$$

把它应用于 Fibonacci 合法构型、素数指数档案或量子记录，都必须另外给出编码、读出和物理实现的桥接假设。


## 113. 粗粒化不能凭空增加经典互信息

第 112 节讨论的是保留记录是否仍然可逆。第 113 节处理另一种更弱的要求：即使不要求恢复全部历史，确定性的粗粒化也不应凭空制造原始记录中没有的经典相关。仓库中的 CoarseGrainingCannotAddInformation.lean 对有限、归一化的联合律给出了这个方向的不等式。

### 113.1 从微观联合律到粗记录

设微观状态为有限集合

$$
X,
$$

两次相邻记录的联合质量为

$$
p:X\times X\to\mathbb R,
$$

并满足

$$
p(z)\ge0,
\qquad
\sum_z p(z)=1.
$$

设确定性的记录压缩为

$$
c:X\to C.
$$

粗粒化后的联合律把所有具有相同粗标签的微观对相加：

$$
p_c(a,b)
=
\sum_{\substack{x,y\in X\\c(x)=a,\ c(y)=b}}p(x,y).
$$

在项目定义中，这个对象叫作 coarseGrainedJoint。它描述的是同一份经典联合记录经过确定性标签压缩后的统计，而不是一次新的物理相互作用。

### 113.2 互信息数据处理不等式

Lean 定理 coarse_graining_cannot_add_information 精确证明：

$$
\boxed{
I_{p_c}(C_{\mathrm{past}};C_{\mathrm{future}})
\le
I_p(X_{\mathrm{past}};X_{\mathrm{future}}).
}
$$

证明把右坐标的确定性映射写成一个 Markov channel，先应用一次互信息数据处理，再交换左右坐标并应用第二次。非负性与总质量为一是定理的必要输入，因为仓库中的 mutualInformation 是有限 Shannon 量。

因此，若只是把历史标签重新命名、合并或忘掉部分坐标，就不会让过去与未来的经典互信息增加。粗粒化可能保留一部分相关，也可能把相关抹掉，但它不能从零生成新的经典相关。

### 113.3 与“观测改变现实”的边界

这条不等式不能推出“任何观测都没有物理影响”。它只描述一个特定操作：

$$
\text{同一份经典联合律}
\longrightarrow
\text{确定性标签映射}
\longrightarrow
\text{新的边缘化联合律}.
$$

如果中间步骤实际施加了量子通道、写入环境记录、重置仪器，或改变了后续 Hamiltonian，那么后续联合律已经不是原来的

$$
p
$$

经过单纯标签函数得到的

$$
p_c.
$$

此时应把相互作用本身纳入新的通道模型，再分别计算输入和输出的互信息。第 113 节只阻止把“压缩标签”误报成“凭空增加信息”，不阻止物理操作改变系统的相关结构。

### 113.4 与预测商和余数容量的关系

第 111 节的 canonical predictive quotient 追问：

$$
\text{为了预测未来，最少要保留哪些区别？}
$$

第 112 节的乘积容量追问：

$$
\text{为了可逆恢复目标标签，记录接口能承载多少状态？}
$$

第 113 节追问：

$$
\text{把这些标签粗粒化以后，还剩多少过去—未来相关？}
$$

三者作用不同。一个粗标签映射可能满足

$$
I(p_c)<I(p),
$$

但仍然保留完整的预测商；也可能因为把预测上必需的纤维合并而破坏后续闭合。反过来，一个足容量的余数接口可以保持标签可逆，却携带远超当前预测任务所需的冗余信息。

因此不能从互信息单调性单独推出最小记忆，也不能从记录容量单独推出预测充分性。需要同时检查：

$$
\text{可逆性},
\qquad
\text{预测闭合},
\qquad
\text{相关信息损失}.
$$

### 113.5 一个零相关的边界例子

若微观联合律是独立律

$$
p(x,y)=p_1(x)p_2(y),
$$

则

$$
I_p(X_{\mathrm{past}};X_{\mathrm{future}})=0.
$$

确定性粗粒化后仍有

$$
I_{p_c}(C_{\mathrm{past}};C_{\mathrm{future}})=0.
$$

这说明粗粒化不能把没有的经典相关变出来。它不表示粗粒化后的变量没有意义；它们仍可能对某个单时刻任务有用，只是不能被解释成过去对未来的额外共享信息。

### 113.6 形式化边界

Lean 已证明的是有限类型、非负归一化联合律和同一个确定性粗粒化映射作用于两个坐标时的互信息不增。它没有证明量子互信息在任意测量协议下的完整演化，也没有把经典互信息直接等同于第 111 节的条件熵成本或第 112 节的可逆容量。

所以，第 113 节当前可复用的结论是：

$$
\boxed{
\text{确定性经典粗粒化不能增加有限联合律的互信息；}
}
$$

而“观测是否改变现实”仍需另外指定观测通道、环境记录和后续动力学。把标签压缩、物理测量和量子退相干写成同一个动作，会丢掉它们之间最关键的区别。


## 114. 记录细化的创新能量：从条件熵到预测风险

第 111 节的条件熵比较的是记忆接口平均携带多少离散信息。第 114 节换一个问题：对于一个具体的实值目标，加入更多记录后，最小平方预测误差到底减少了多少？仓库中的条件期望模块给出了一个正交分解。

### 114.1 两层记录生成两个预测空间

设底层状态空间为

$$
X,
$$

带有测度

$$
\mu,
$$

并设当前记录生成的 sigma 代数为

$$
\mathcal G_c,
$$

加入更多历史或未来记录后得到更细的 sigma 代数

$$
\mathcal G_f.
$$

它们满足

$$
\mathcal G_c\le\mathcal G_f\le\mathcal A,
$$

其中

$$
\mathcal A
$$

是环境的 ambient measurable space。给定一个实值平方可积目标

$$
Y\in L^2(\mu),
$$

定义两种条件期望预测：

$$
\widehat Y_c=\mathbb E[Y\mid\mathcal G_c],
\qquad
\widehat Y_f=\mathbb E[Y\mid\mathcal G_f].
$$

在 Zeckendorf 模型中，可以把

$$
\mathcal G_c
$$

理解为当前合法构型读出生成的记录，而把

$$
\mathcal G_f
$$

理解为加入若干历史位、余数记录或后续可访问接口后的记录。这里的 sigma 代数是一个抽象的可测结构；它没有自动等同于量子 Hilbert 子空间。

### 114.2 Pythagoras 分解

conditional_expectation_refinement_pythagoras 精确证明：

$$
\boxed{
\|Y-\widehat Y_c\|_2^2
=
\|Y-\widehat Y_f\|_2^2
+
\|\widehat Y_f-\widehat Y_c\|_2^2.
}
$$

同时有

$$
\|Y-\widehat Y_f\|_2^2
\le
\|Y-\widehat Y_c\|_2^2.
$$

最后一项

$$
\Delta_{\mathrm{refine}}
=
\|\widehat Y_f-\widehat Y_c\|_2^2
$$

可以称作记录细化的创新能量。它不是一个新的 Lean 定义，而是上述分解中已经出现的平方范数项。它的解释是：

$$
\text{细化后新增的可预测部分}
=
\text{细化前后预测器之间的距离}.
$$

如果

$$
\Delta_{\mathrm{refine}}=0,
$$

则两层记录给出的 L^2 预测器相同；这说明新增记录对这个目标和这个测度没有带来平方风险上的改进。这个等价解释只针对该目标、该测度和该二次损失，不能推广成新增记录在所有任务中都无用。

### 114.3 与第 111 节的条件熵成本互补

第 111 节给出的是

$$
H(\pi_{F,q}\mid q)
\le
H(r\mid q),
$$

它回答候选记忆还携带多少平均离散信息。第 114 节给出的是

$$
\|Y-\widehat Y_f\|_2^2
\le
\|Y-\widehat Y_c\|_2^2,
$$

它回答加入记录后一个指定目标的预测误差减少多少。

两者可能朝不同方向变化：

$$
\text{记忆条件熵增加}
\quad\not\Rightarrow\quad
\text{指定目标风险一定下降},
$$

因为新增记录可能只包含与该目标无关的历史；同样，

$$
\text{指定目标风险下降}
\quad\not\Rightarrow\quad
\text{全部未来响应都已闭合}.
$$

因此，稳定对象的记忆预算至少有两个坐标：

$$
\begin{array}{c|c}
\text{坐标}&\text{测量内容}\\
\hline
\text{预测记忆熵}&\text{当前读出已知后还保留多少离散预测信息}\\
\text{创新能量}&\text{细化记录对指定平方损失目标减少多少误差}
\end{array}
$$

这也是为什么不能用单一的“历史长度”替代所有任务的成本描述。

### 114.4 零风险的可测性判据

zero_prediction_risk_iff_ae_observation_measurable 给出一个更强的边界。设

$$
\operatorname{obs}:X\to O
$$

是可测观测，且

$$
Y:X\to\mathbb R
$$

属于

$$
L^2(\mu).
$$

在概率测度条件下，定理证明：

$$
\boxed{
\int
\left(
Y-
\mathbb E[Y\mid\sigma(\operatorname{obs})]
\right)^2
\,d\mu
=0
\quad\Longleftrightarrow\quad
Y\text{ 在 }\sigma(\operatorname{obs})\text{ 上几乎处处可测}.
}
$$

这里的

$$
\sigma(\operatorname{obs})
$$

由观测映射的 comap 构造。左侧是零平方预测风险，右侧表示观测已经保留了足以重建该目标的全部信息，允许测度零集合上的差异。

因此，如果当前 Zeckendorf 读出生成的 sigma 代数已经使目标可测，那么继续保存更多历史不会降低这个目标的平方误差。反之，只要目标还含有当前记录不可测的部分，零风险就不可能由该记录单独达到。

### 114.5 一个有限离散化的解释

在有限状态且均匀概率的模型中，可以把 sigma 代数看成状态划分。当前记录把状态分成若干纤维，条件期望在每个纤维上取目标平均值。加入更细记录就是把纤维进一步拆分：

$$
\text{粗纤维}
\longrightarrow
\text{细纤维}
\longrightarrow
\text{更准确的纤维内平均}.
$$

Pythagoras 分解说明，粗预测误差中有一部分正好等于“细平均”与“粗平均”的平方差。若新增历史只是在每个粗纤维内部加入与目标无关的标签，那么

$$
\widehat Y_f=\widehat Y_c,
$$

创新能量为零；只有当细化后的纤维条件均值确实偏离对应的粗纤维均值时，创新能量才为正。仅仅把目标值不同的状态拆开，并不保证这一点，因为正负偏差可能在纤维平均中抵消。

这个解释与第 113 节的互信息不增并不冲突。粗粒化的互信息定理比较的是过去—未来联合相关；条件期望定理比较的是一个指定目标的平方风险。它们对不同函数和不同损失进行测量。

### 114.6 与量子模型的边界

第 114 节使用的是：

$$
\mathbb R\text{-值目标},
\qquad
L^2\text{ 范数},
\qquad
\text{条件期望},
\qquad
\text{概率测度}.
$$

它没有直接处理复振幅、密度矩阵的 von Neumann 熵、非交换观测或量子通道。要把创新能量接到前面的量子记录模型，必须额外选择一个正的经典输出或 POVM 统计量，把它作为实值目标

$$
Y
$$

再指定观测生成的 sigma 代数。未经这一步，不能把

$$
\|\widehat Y_f-\widehat Y_c\|_2^2
$$

解释成普适的量子相干衰减量。

因此，当前可以安全使用的桥是：

$$
\boxed{
\text{记录细化的预测收益}
=
\text{条件期望的正交创新能量};
}
$$

而量子物理解释仍需另外证明记录通道如何产生这些经典统计和测度。

### 114.7 对稳定现实的进一步约束

把第 111–114 节合起来，历史保留问题可以写成一个三重约束：

$$
\begin{aligned}
&\text{预测闭合：}&
\pi_{F,q}&=g\circ r,\\
&\text{信息成本：}&
H(\pi_{F,q}\mid q)&\le H(r\mid q),\\
&\text{目标风险：}&
\|Y-\widehat Y_f\|_2^2&\le\|Y-\widehat Y_c\|_2^2.
\end{aligned}
$$

若要求某个目标达到零风险，还必须满足

$$
Y
$$

在当前记录生成的 sigma 代数上几乎处处可测。若要求完整历史可恢复，还要另行满足第 112 节的乘积容量判据。于是“稳定经典现实”不是由一项单独的状态数决定，而是由任务、观测和误差准则共同决定。

### 114.8 形式化边界

Lean 已证明的是有限或测度论的实值

$$
L^2
$$

条件期望分解、细化不增加平方预测风险，以及概率测度下零风险与观测可测性的等价。它没有证明这些对象自动来自 Zeckendorf Hamiltonian，也没有把二次预测风险与量子互信息或退相干率等同。

下一步若要继续形式化桥接，应先固定一个有限合法字串空间、一个实际读出函数和一个正的目标统计量，再把其离散划分映射到 sigma 代数或有限条件期望模型。只有这样，创新能量才会成为该具体量子记录协议的可计算量。

## 115. 行动闭合：公开状态相同但所需动作不同的硬反例

第 111 节把稳定对象定义为对未来预测足够的记忆商；第 114 节把记录细化带来的预测收益写成条件期望的创新能量。但“能预测一个目标”还不是“能作为一个行动状态”。如果系统下一步必须选择动作，那么当前记录还必须足以决定在允许的情境下应采取什么行动。

仓库中的 `D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.lean` 给出了这个要求的最小形式化。设

$$
q:T\to S
$$

是时间或历史到公开状态的读出，设

$$
\alpha:T\to A
$$

是实际要求的动作。如果存在两个时刻 $$t,u$$ 满足

$$
q(t)=q(u),
\qquad
\alpha(t)\ne\alpha(u),
$$

则不存在一个只看公开状态的策略

$$
\pi:S\to A
$$

使得对所有时刻都有

$$
\pi(q(v))=\alpha(v).
$$

证明只有一行内积式的等式传递：若这样的策略存在，则

$$
\alpha(t)
=\pi(q(t))
=\pi(q(u))
=\alpha(u),
$$

与动作不同矛盾。Lean 已经在任意类型 $$T,S,A$$ 上编译并证明了这个命题；它没有引入量子假设，因此是一个比具体物理模型更基础的行动闭合障碍。

### 115.1 从预测闭合到控制闭合

第 111 节的预测商只要求：在指定未来操作族中，当前记忆能决定未来读数。行动闭合增加了一个不同的要求：同一个公开状态必须允许同一个策略动作。可以把两者写成两个因子化条件。

令 $$r$$ 是保留的记忆接口，令 $$q$$ 是当前公开读出。预测闭合要求

$$
q=\overline q\circ r,
\qquad
r\circ F=\overline F\circ r,
$$

其中 $$F$$ 是状态更新；控制闭合要求实际行动 $$\alpha$$ 满足

$$
\alpha=\pi\circ r.
$$

前两式说“先演化再压缩”和“先压缩再用有效更新”一致，并且当前读出可以由记忆接口恢复；后一式说“所需行动”本身能够由压缩后的状态决定。当前状态分类即使满足预测闭合，也可能不满足控制闭合，因为行动可能依赖没有进入 $$r$$ 的历史变量。

因此，稳定经典对象至少要通过两道检查：

$$
\boxed{
\text{预测闭合} + \text{控制闭合}.
}
$$

如果研究目标只有被动预测，控制闭合可以暂不要求；如果对象要参与反馈、干预或实验设计，控制闭合就是必要条件。

### 115.2 与第 111 节 canonical quotient 的关系

令 $$r:T\to M$$ 是某个保留的记忆接口。若所有允许的预测和动作都只依赖 $$r$$，则存在函数 $$g_F$$ 与 $$\pi$$ 使得

$$
q(F(t))=g_F(r(t)),
\qquad
\alpha(t)=\pi(r(t)).
$$

第 111 节的 canonical predictive quotient 只对第一类函数取共同商；第 115 节说明，若要得到可执行对象，商必须再细化到能够因子化所有相关动作的程度。换句话说，预测等价关系

$$
 t\sim_{\mathrm{pred}}u
$$

只在所有未来读数相同的历史之间合并；控制等价关系还要求

$$
\alpha(t)=\alpha(u)
$$

对所有被合并的历史成立。若动作不同，两个历史必须继续分开，即使它们当前所有公开读数都相同。

这给出“需要保留多少历史”的一个更强答案：

$$
\boxed{
\text{所需记忆至少要区分所有会导致不同未来动作的历史。}
}
$$

条件熵下界仍然适用，但现在的任务族扩大了。若 $$\Pi$$ 表示允许的策略动作集合，应该以同时支配预测读出与动作的最小商来定义记忆，而不能只根据一个目标变量计算成本。

### 115.3 一个有限反例：同一个 Zeckendorf 粗读数（奇偶）对应不同动作

取长度为三、禁止相邻两个一的合法构型

$$
000,\quad001,\quad010,\quad100,\quad101,
$$

并用权重 $$3,2,1$$ 读出 Zeckendorf 数值。这个读出把五个构型标成 $$0,1,2,3,4$$。现在假定公开接口只保留奇偶性

$$
q(w)=a(w)\bmod 2,
$$

其中 $$a(w)$$ 是上述数值；于是 $$001$$ 与 $$100$$ 都读成公开状态 $$1$$。

如果控制任务规定：数值为 $$1$$ 时执行动作 $$A_1$$，数值为 $$3$$ 时执行动作 $$A_3$$，且 $$A_1\ne A_3$$，那么公开奇偶状态无法支持正确策略。两个历史具有相同的公开值，却要求不同动作。要恢复控制闭合，至少必须保留一个能区分这两个构型的额外记录，例如完整数值、最高位位置，或直接保留它们所属的预测—动作等价类。

这个例子不说明奇偶记录“错误”。它只说明记录的适用范围：它可以足以回答某些二元问题，却不足以承担这个控制任务。Zeckendorf 刻度提供合法构型的组织方式；究竟要保留多少位，则由预测目标、动作集合和允许误差共同决定。

### 115.4 量子边界：策略依赖记录，不等于预先填写所有测量答案

在量子模型中，行动闭合必须相对于一个实际可访问的记录系统来表述。若记录通道为

$$
\mathcal C(\rho)_{ij}=R_{ij}\rho_{ij},
$$

则一个控制器可以依赖当前记录寄存器、系统的允许操作和已建立的相关，而不能自动依赖被环境保留但控制器无法访问的完整历史。

这不意味着为所有不相容测量预先填写一张经典答案表。控制闭合只要求：在明确给定的实验协议和可访问记录下，存在一个实现动作的映射。更换可访问记录、测量上下文或联合操作，可能改变可实现的策略集合。`WindowCharacter` 所表达的非交换障碍仍然保留：不能把所有相容性关系压成一个保乘法的复数读数，再把该读数当成万能控制状态。

一个最小的相位反例来自合法基态 $$|01\rangle,|10\rangle$$。令

$$
|B\rangle=\frac{|01\rangle+|10\rangle}{\sqrt 2},\qquad
|D\rangle=\frac{|01\rangle-|10\rangle}{\sqrt 2}.
$$

计算基底读出对二者给出相同分布，但若允许的后续耦合在该子空间中满足

$$
H|01\rangle=g|00\rangle,\qquad H|10\rangle=g|00\rangle,\qquad
H|00\rangle=g(|01\rangle+|10\rangle),
$$

则

$$
H|B\rangle=\sqrt 2g|00\rangle,\qquad H|D\rangle=0.
$$

因此，相同当前读数不能保证相同控制响应；把这个耦合加入任务族后，动作完备的记录必须保留相对相位所区分的历史。

同样，局部读数相同也不代表联合状态相同。若控制器能够访问记录自由度并执行允许的联合操作，`CanonicalRecordAccessRecovery` 所刻画的恢复机制可能重新暴露被局部读出隐藏的区别；若记录不可访问，则该区别对当前控制器仍然是隐藏变量，并可能通过历史回流影响后续行动。

### 115.5 与第 114 节预测风险的合并

把目标预测误差和行动错误分别记为

$$
\mathcal R_Y(q)=\mathbb E\left[(Y-\widehat Y_q)^2\right],
$$

以及一个动作损失

$$
\mathcal R_A(q)=\mathbb E\left[\ell(\alpha,\widehat\alpha_q)\right].
$$

第 114 节的 Pythagoras 分解说明，记录细化带来的目标风险下降等于新增条件均值的平方能量。第 115 节补充一个离散的零风险边界：若同一公开状态上存在不同必需动作，则任何确定性无记忆策略的动作风险都不可能为零。即使目标 $$Y$$ 已经可以被当前读出无误预测，动作风险仍可能保持正值。

因此，一个面向行动的稳定现实应同时满足

$$
\mathcal R_Y(q)\le\varepsilon_Y,
\qquad
\mathcal R_A(q)\le\varepsilon_A,
$$

并且在零误差的确定性情形满足

$$
\alpha=\pi\circ q.
$$

若允许随机策略，确定性障碍会转化为条件动作分布必须在同一公开状态上相同；不同历史诱导不同的最优动作分布时，仍需保留能区分它们的记录。这个推广需要额外的概率化 Lean 定理，当前仓库只冻结了确定性命题。

### 115.6 对“稳定经典现实”的更新定义

到这里，“稳定”不能只理解为某个记录通道的固定点是对角的，也不能只理解为某个目标的预测误差很小。更完整的有限任务定义是：给定允许的读出、演化和行动族，一个记录接口 $$q$$ 满足

$$
\begin{aligned}
& q\circ F=g_F\circ q &&\text{对相关预测操作成立},\\
& \alpha=\pi\circ q &&\text{对相关控制任务成立},\\
& \mathcal R_Y(q)\le\varepsilon_Y,\\
& \mathcal R_A(q)\le\varepsilon_A.
\end{aligned}
$$

若量子记录还会被重复复用，则必须把记录的可访问性和历史回流一并放进允许操作族；不能只按“观测次数”估算记忆成本。若进一步展开内部结构不会改变这些预测与行动，或改变量低于给定误差界，当前接口才可以作为该尺度上的有效对象。

所以第 115 节把此前的问题推进了一步：

$$
\boxed{
\text{稳定现实不仅要能回答“接下来会看到什么”，还要能决定“接下来能做什么”。}
}
$$

公开状态相同而所需动作不同，是一个可机器验证的反例，说明任何声称“当前读数已经构成完整对象”的理论，都必须说明它保留了哪些行动相关历史，以及这些历史在什么操作族中可以被忽略。

### 115.7 形式化边界

Lean 已证明的是任意类型上的确定性记忆无关策略障碍：重复公开状态若对应不同动作，则不存在只依赖公开状态的全局策略。它没有证明某个具体 Zeckendorf 读出在物理实验中必须承担哪一种控制任务，也没有把确定性策略自动推广为随机、量子反馈或有记忆环境中的最优控制。

当前可复用的桥是：

$$
\boxed{
\text{预测闭合控制未来读数，行动闭合控制未来干预；两者必须按同一任务族分别检验。}
}
$$

下一步若继续形式化，应固定一个有限合法构型空间、一个可访问记录映射和一个有限动作集合，再证明该记录对指定动作族的因子化条件，最后把动作风险与第 114 节的预测风险放在同一个有限概率模型中比较。

## 116. 干预闭包的最小修复：把可执行历史组织成响应轨迹

第 115 节给出了行动闭合失败的最小障碍：相同公开状态可能要求不同动作。下一步不是无条件恢复全部历史，而是问：给定一族允许干预，怎样构造一个刚好足以保持闭合的细化接口？仓库中的 `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean` 给出了一个一般答案。

设原始概念读出为

$$
 c:X\to A,
$$

允许的干预族为

$$
 I:U\to X\to X.
$$

若两个状态被当前概念归为同一类，即

$$
 c(x)=c(y),
$$

那么概念对干预族闭合，是指对每个干预 $$u$$ 都有

$$
 c(I(u,x))=c(I(u,y)).
$$

这正是“当前合并掉的历史，不会在下一次允许操作后重新显现”的形式化条件。

### 116.1 动态闭包记录什么

对一个有限干预词

$$
 w=[u_1,\ldots,u_k]\in U^*,
$$

令 $$I_w(x)$$ 表示从 $$x$$ 出发依次执行这些干预。动态闭包读出为

$$
 \operatorname{Dyn}_I(c)(x)(w)=c(I_w(x)).
$$

因此

$$
\operatorname{Dyn}_I(c):X\to(U^*\to A)
$$

不是只保存当前标签，而是保存“在所有有限干预词之后会看到什么”的响应轨迹。空词给出原始读出：

$$
\operatorname{Dyn}_I(c)(x)([]) = c(x).
$$

这立即说明动态闭包细化了原始概念。若两个状态在动态闭包下相同，它们在空词下当然相同；反方向一般不成立。

### 116.2 它确实对每个允许干预闭合

若 $$x,y$$ 的动态轨迹相同，则对任意干预 $$u$$ 和任意后续词 $$w$$，有

$$
\operatorname{Dyn}_I(c)(I(u,x))(w)
=
\operatorname{Dyn}_I(c)(x)(u::w)
=
\operatorname{Dyn}_I(c)(y)(u::w)
=
\operatorname{Dyn}_I(c)(I(u,y))(w).
$$

所以

$$
\boxed{
\operatorname{Dyn}_I(c)\text{ 对 }I\text{ 的每一个干预都闭合}.
}
$$

这里的关键不是把状态变成一个更长的静态标签，而是把干预前缀加入响应坐标。任何可能使两个状态分开的下一步，都已经成为轨迹中的一个坐标。

### 116.3 最小性：所有闭合细化都必须包含它

设另一个接口

$$
 d:X\to B
$$

满足两个条件：

$$
 c=\bar c\circ d,
$$

即 $$d$$ 至少保留原始概念；并且 $$d$$ 对所有干预闭合，即

$$
 d(x)=d(y)
\Longrightarrow
 d(I(u,x))=d(I(u,y)).
$$

那么仓库中的 `dynamic_closure_is_least` 证明：存在一个从 $$d$$ 到动态闭包的因子，使得动态闭包不会保留任何一个所有闭合细化都可以安全丢掉的坐标。按项目中的 `Refines` 方向写成：

$$
\boxed{
 d\text{ 闭合且细化 }c
\Longrightarrow
 d\text{ 细化 }\operatorname{Dyn}_I(c).
}
$$

等价地说，动态闭包是所有干预闭合细化的最小公共要求。证明沿干预词归纳：闭合性把单步等价逐步传播到任意有限词；原始概念因子化则把每一条轨迹坐标从候选接口恢复出来。

这一步把第 115 节的“必须保留额外历史”变成了一个可构造的最小方案：只保留那些会在允许干预轨迹中显现的差异。

### 116.4 与预测商的精确关系

第 111 节的 predictive quotient 由指定未来读出族决定；第 116 节把未来族具体化为所有有限干预词。若未来任务只允许观测而不允许干预，动态闭包退化为相应的观测响应商。若加入一个新的可执行干预 $$u_*$$，任务族变为

$$
\mathfrak T' = \mathfrak T\cup\{u_*\},
$$

动态闭包会加入以 $$u_*$$ 开头的响应坐标。于是原先可以合并的两个状态，可能因为

$$
 c(I(u_*,x))\ne c(I(u_*,y))
$$

而被分开。

因此，记忆需求不是只由当前读出决定，而是由三元组共同决定：

$$
\boxed{
(\text{当前读出},\ \text{允许干预族},\ \text{预测任务族}).
}
$$

扩大实验能力会细化等价类；缩小实验能力可能允许更粗的有效对象。这里的“相对性”具有明确的单调方向，而不是任意描述都同样有效。

### 116.5 Zeckendorf 合法空间中的有限截断

在长度 $$L$$、禁止相邻两个一的合法空间中，令

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

并令 $$c(w)$$ 是 Zeckendorf 数值或某个局部记录。若干预是保持合法性的局部翻转族

$$
 I_u:\mathcal W_L\to\mathcal W_L,
$$

则动态闭包可以在有限干预深度 $$N$$ 截断为

$$
\operatorname{Dyn}_{I,N}(c)(w)
=
\bigl(c(I_v(w))\bigr)_{|v|\le N}.
$$

对于固定 $$L,N$$，这仍然是有限记录接口，可以直接枚举和比较。它回答的是有限实验范围内的闭合问题：两个合法构型若在所有长度不超过 $$N$$ 的允许干预下都有相同读出，就可以在该实验预算内合并；若某条长度至多 $$N$$ 的词把它们分开，则当前接口不闭合。

但有限截断不等于无限闭包。若只证明

$$
\operatorname{Dyn}_{I,N}(c)(x)=\operatorname{Dyn}_{I,N}(c)(y),
$$

不能推出对所有更长干预词都相同。这个边界正是“有限预测范围”和“全局可恢复历史”的区别。第 112 节的完整恢复容量条件也因此不能由一个有限截断自动替代。

### 116.6 量子版本的边界

在量子系统中，不能直接把 $$I_u$$ 当作任意函数；它应由允许的量子通道、幺正演化或测量—反馈协议给出，并且当前读出应由一个明确的 POVM 或记录通道产生。若用 $$\mathcal C$$ 表示记录，$$\Phi_u$$ 表示干预后的通道，那么有限响应轨迹的坐标可以写成

$$
\mathcal C\circ\Phi_{u_k}\circ\cdots\circ\Phi_{u_1}(\rho).
$$

这只是把动态闭包的结构翻译到量子通道语言；它没有自动证明这些坐标彼此可同时读取，也没有把量子态压成一张预先填写所有不相容测量答案的经典表。不同轨迹坐标可能依赖不同上下文，必须保留测量机制和允许的联合操作。

对于前文的 Zeckendorf 受约束 Hilbert 空间，若投影到合法子空间的投影为 $$P_Z$$，还要分别检查：

$$
[H,P_Z]=0
$$

是否保证连续演化保持合法空间，以及每个测量或反馈通道是否把合法密度矩阵送回合法状态集合。动态闭包只描述“哪些响应需要保留”，不替代物理实现条件。

### 116.7 对稳定经典现实的进一步定义

结合第 115 节，稳定接口不再只是满足一个静态固定点，而应满足：

$$
\begin{aligned}
&\text{当前读出可由接口恢复},\\
&\text{接口对允许更新和干预闭合},\\
&\text{指定预测与动作在接口上因子化},\\
&\text{截断或近似时给出明确误差界}.
\end{aligned}
$$

动态闭包提供了一个极端但清楚的上界：保留全部有限响应轨迹，必然不会遗漏允许干预能暴露的差异。其最小性定理又说明，在同一任务族中，任何安全的闭合接口都必须至少保留这些响应信息。

实际研究通常会在动态闭包与更便宜的近似接口之间选择。第 111 节的条件熵、第 114 节的创新能量和第 115 节的动作风险，可以用来衡量删去哪些轨迹坐标后仍满足给定精度；删去后若出现新的干预分离，则由动态闭合条件给出精确反例。

因此，“保留多少历史”现在有一个可执行的答案：

$$
\boxed{
\text{保留到允许干预族下的响应轨迹闭合；若只做有限实验，就保留到指定深度并报告截断误差。}
}
$$

### 116.8 形式化边界

Lean 已证明的是纯确定性概念动力学中的三件事：原始概念被动态闭包细化；动态闭包对每个干预闭合；任何闭合且细化原概念的候选接口都细化动态闭包。证明使用任意类型和有限列表干预词，不依赖概率、Hilbert 空间或量子公理。

它没有证明无限干预族的有限表示一定存在，也没有证明某个具体 Zeckendorf 翻转规则对应真实物理 Hamiltonian，更没有证明量子通道的非交换响应可以无损地嵌入一个经典轨迹函数。那些桥接仍然开放，必须在固定有限构型、通道、测量和误差指标后分别验证。

当前可复用的最强桥是：

$$
\boxed{
\text{动态闭包是指定干预族下保持预测与行动闭合的最小响应细化。}
}
$$

这使“对象”获得了一个更严格的操作性判据：它不是当前读数的名字，而是对允许实验族足够闭合的响应接口。

## 117. 有限时域控制的下沉：预测闭合还必须保留价值递归

第 116 节说明，若只要求响应对干预闭合，可以用动态闭包构造最小细化。但行动任务通常还有一个更强的问题：不是只问“允许什么动作”，而是问“在有限未来时域内，哪个动作最优”。这要求记录接口不仅保持状态更新，还要保持奖励和终值的结构。

仓库中的 `D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean` 形式化了这个桥。设微观状态、宏观状态和动作分别为

$$
S_{\mathrm{micro}},\qquad S_{\mathrm{macro}},\qquad A,
$$

有一个抽象映射

$$
\alpha:S_{\mathrm{micro}}\to S_{\mathrm{macro}}.
$$

微观转移和宏观转移为

$$
T_m:A\times S_{\mathrm{micro}}\to S_{\mathrm{micro}},
\qquad
T_M:A\times S_{\mathrm{macro}}\to S_{\mathrm{macro}}.
$$

若对每个动作和微观状态都有

$$
\alpha(T_m(a,s))=T_M(a,\alpha(s)),
$$

则抽象与受控动力学相容。

### 117.1 奖励和终值也必须因子化

仅有状态转移相容还不够。有限时域最优控制还使用阶段奖励和终端价值。设

$$
r_m:S_{\mathrm{micro}}\times A\to\mathbb R,
\qquad
r_M:S_{\mathrm{macro}}\times A\to\mathbb R,
$$

以及终端价值

$$
V^0_m:S_{\mathrm{micro}}\to\mathbb R,
\qquad
V^0_M:S_{\mathrm{macro}}\to\mathbb R.
$$

需要同时满足

$$
 r_m(s,a)=r_M(\alpha(s),a),
$$

以及

$$
 V^0_m(s)=V^0_M(\alpha(s)).
$$

这三个条件分别保证：执行同一个动作后的状态一致、即时收益一致、停止时的价值一致。缺少任意一个条件，宏观读出都可能无法承担控制价值。

### 117.2 Bellman 值逐时域因子化

对有限动作集，定义 Bellman 值

$$
V_0(s)=V^0(s),
$$

并递归为

$$
V_{n+1}(s)
=
\max_{a\in A}
\left(r(s,a)+V_n(T(a,s))\right).
$$

Lean 定理 `finite_horizon_value_factorization` 证明：在上一节的三项相容条件下，对每个有限时域 $$n$$ 都有

$$
\boxed{
V^{\mathrm{micro}}_n(s)
=
V^{\mathrm{macro}}_n(\alpha(s)).
}
$$

证明对 $$n$$ 做归纳。零时域就是终值因子化；后继时域中，每个动作的即时奖励和递归续值逐项相等，因此有限动作集合上的最大值也相等。

这比“一步更新可预测”更强：它说明相同宏观状态的微观历史，在整个指定有限时域内拥有相同的最优价值。

### 117.3 最优动作集合也下沉

令有限时域 $$n$$ 下的最优动作集合为

$$
\operatorname{Opt}_n(s)
=
\left\{
 a:\ r(s,a)+V_n(T(a,s))
 \text{达到所有动作中的最大值}
\right\}.
$$

仓库中的 `finite_horizon_optimal_actions_descend` 进一步证明

$$
\boxed{
\operatorname{Opt}^{\mathrm{micro}}_n(s)
=
\operatorname{Opt}^{\mathrm{macro}}_n(\alpha(s)).
}
$$

因此，抽象接口不仅能计算宏观价值，还能准确给出所有最优动作。若微观状态 $$s,t$$ 满足

$$
\alpha(s)=\alpha(t),
$$

那么在这些假设下，它们的有限时域最优动作集合完全相同。这里的“行动闭合”不再只是存在某个动作函数，而是整个有限时域 Bellman 递归在接口上闭合。

### 117.4 对第 115 节障碍的精确修复条件

第 115 节的障碍是：

$$
q(s)=q(t),
\qquad
\text{但所需动作不同}.
$$

第 117 节给出一个可验证的充分条件，保证这种分离不会发生在有限时域最优控制中：抽象 $$\alpha$$ 必须同时保持转移、奖励和终值。此时不是把动作差异强行抹去，而是证明它们在任务定义下本来就不构成差异：

$$
\alpha(s)=\alpha(t)
\Longrightarrow
\operatorname{Opt}_n(s)=\operatorname{Opt}_n(t).
$$

如果实际系统出现两个同一抽象类中的状态，却有不同的最优动作集合，那么至少有一项因子化假设失败。具体可能是：转移没有闭合，奖励读出了隐藏历史，或终端目标依赖被丢弃的变量。此时应增加记录，或者缩小允许任务族，不能继续声称当前抽象是控制完备的。

### 117.5 Zeckendorf 约束空间中的解释

取合法构型空间

$$
\mathcal W_L=\{w\in\{0,1\}^L:w_jw_{j+1}=0\},
$$

把 $$w$$ 作为微观状态，把某个 Zeckendorf 粗读出作为宏观状态。若局部更新保持合法空间，并且满足

$$
\alpha(T_m(a,w))=T_M(a,\alpha(w)),
$$

那么还必须检查阶段奖励和终端目标是否只依赖 $$\alpha(w)$$。例如，若奖励是完整 Zeckendorf 数值的函数，而宏观接口只保留最后一位或奇偶性，则通常不能直接使用值函数下沉定理；需要证明该奖励在每个宏观纤维上相同，或扩展宏观状态。

反过来，若任务只奖励“是否仍为合法构型”，局部有限状态接口可能已经足够。由此可见，合法语言的最小自动机状态数、数值读出所需记忆、有限时域控制所需状态数和量子 Hilbert 空间维数仍然是不同的量。

### 117.6 与量子记录模型的边界

Bellman 因子化定理是有限动作、确定性转移和实值奖励的经典定理。它可以用于量子实验的经典输出层：先固定一个 POVM 或记录通道，把每次实验的输出和代价定义成实值函数，再检查这些输出是否在选定记录接口上因子化。

但它没有直接证明量子通道的密度矩阵、复振幅或非交换观测满足 Bellman 递归。若动作本身是量子通道，或者状态只以概率分布给出，必须另外选择随机控制、部分可观测控制或量子控制的数学模型。不能把有限经典 $$\max$$ 自动解释成量子测量中的普适优化规则。

同样，值函数相等不等于完整历史相等。两个微观状态可以在指定有限时域和奖励下具有相同价值，却在加入新的测量、不同终值或更长时域后被区分。值函数因子化是任务相对的闭合结果，不是本体论上的全局同一。

### 117.7 对稳定经典现实的更新

目前“稳定”的条件可以按强度分层：

$$
\begin{aligned}
&\text{读出闭合}: && q=\bar q\circ r,\\
&\text{状态闭合}: && r\circ T=\bar T\circ r,\\
&\text{行动闭合}: && \operatorname{Opt}_n=\overline{\operatorname{Opt}}_n\circ r,\\
&\text{价值闭合}: && V_n=\bar V_n\circ r.
\end{aligned}
$$

第 116 节给出对指定干预族的最小响应细化；第 117 节说明，当任务还带有奖励和终值时，真正需要的是 Bellman 价值与最优动作的共同下沉。于是“保留多少历史”可按任务逐层增加，而不是一开始就保留全部微观状态。

如果只要求一步读出，读出闭合可能足够；如果要求有限时域行动，就必须验证值函数闭合；如果新增动作、奖励或终值使因子化失败，就必须细化接口或明确任务边界。

### 117.8 形式化边界

Lean 已证明的是有限动作集、非空动作类型、确定性转移、实值阶段奖励和实值终端函数下的有限时域 Bellman 值因子化，以及最优动作集合的精确相等。定向构建确认 `finite_horizon_value_factorization` 使用标准公理闭包

$$
[\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}].
$$

这些定理没有证明无限时域极限、随机策略、部分可观测控制或量子通道的最优性。它们提供的可复用桥是：

$$
\boxed{
\text{若转移、奖励和终值都尊重同一抽象，有限时域价值和最优动作就完全下沉到该抽象。}
}
$$

这把第 115 节的行动闭合从一步逻辑障碍推进到有限未来的控制递归，并给出了一个可以直接检验的历史保留准则。
## 118. 响应闭合的适用条件：支持集、有限视野与动作选择

**定义 118.1（原档案载体与两种数位索引）。** 沿用[《情境时空算术》定义 1–6](CONTEXTUAL_SPACETIME_ARITHMETIC.md)，完整表示为

$$
\mathbf x=(C,A_{\rm sel}),\qquad
C=(E,\prec,t,x,\sigma,\rho,\Omega),\qquad
A_{\rm sel}\subseteq\Omega\subseteq E.
$$

其中 $E$ 是有限事件出现集，$\prec$ 是严格偏序，整数时刻沿偏序严格增加，位置取值于 $\mathbb Z^3$，符号取值于 $\{+1,-1\}$，来源取值于有限来源树。档案、当前区域和当前选择是不同数据；本节的状态集 $X$ 可取这些完整表示的指定集合，或另行明确的状态描述集合。一个表示的档案有限不意味着全部表示组成有限集合。原数值读数为

$$
q_{\rm CSA}(\mathbf x)=\sum_{e\in A_{\rm sel}}\sigma(e).
$$

[《情境时空算术的 Zeckendorf 观察》定义 3、4、9、11](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)中的权重与两种索引分别为

$$
G_0=1,\quad G_1=2,\quad G_{j+2}=G_{j+1}+G_j,
\qquad a(c)=\sum_jG_jc_j,
$$

$$
a_p(r)=\sum_jG_jr(p,j),\qquad N(r)=\prod_p p^{a_p(r)}.
$$

单个自然数的规范行 $c=(c_0,c_1,\ldots)$ 与正整数的素数指数表 $r=(r(p,j))$ 不同；$a(c)$、$a_p(r)$、$N(r)$ 也不与 $q_{\rm CSA}$ 混同。源卷的字串按低位到高位书写。第 115.3 节的三位字串采用反向书写约定：其字串为 $c_2c_1c_0$，从左到右的权重恰为

$$
(G_2,G_1,G_0)=(3,2,1).
$$

因此该节的 $001$ 与 $100$ 分别是数值一与三；若按源卷低位到高位书写，同两行分别写为 $100$ 与 $001$。这里只交换书写方向，不交换素数标签与数位索引。概率分布是额外数据，重复来源标签本身不规定概率或独立性。

**假设 118.2（部分操作的定义域与失败观察）。** 第 116、117 节使用总更新时，须固定当前读出 $c:X\to O$ 及如下操作解释。每个字母 $u\in U$ 指定一个原操作的确定部分映射

$$
I_u:D_u\subseteq X\longrightarrow X.
$$

多元原操作通过固定其他参数及孔的位置给出这样的映射；$D_u$ 保留原定义域。例如原时间复合的守卫仍为

$$
\forall e\in E_{\mathbf x}\ \forall f\in E_{\mathbf y},
\qquad t_{\mathbf x}(e)<t_{\mathbf y}(f).
$$

应用总更新结论时，或者限制到一个非空不变域 $X_0$，使每个允许字母在全部 $X_0$ 上合法且 $I_u(X_0)\subseteq X_0$；或者使用带不交失败标签的扩张

$$
X_\bot=X\sqcup\{\bot\},\qquad
\widehat I_u(z)=
\begin{cases}
I_u(z),&z\in D_u,\\
\bot,&z\in X\setminus D_u\text{ 或 }z=\bot,
\end{cases}
$$

$$
\widehat c(z)=
\begin{cases}
\operatorname{ok}(c(z)),&z\in X,\\
\operatorname{fail},&z=\bot,
\end{cases}
\qquad \operatorname{fail}\notin\operatorname{ok}(c[X]).
$$

成功后继须仍在所选 $X$ 内；失败严格传播。此扩张与[原卷定义 16 的严格观察](CONTEXTUAL_SPACETIME_ARITHMETIC.md)及[Zeckendorf 卷定义 446.1](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)一致。若还要优化控制，须对失败规定终止、奖励和终值，或只使用在全域合法的共同动作集；不能以固定动作集上的最大值代替未说明的状态依赖合法动作域。

**命题 118.3（第 115 节开篇的等式论证）。** 设 $q:T\to S$，$b:T\to A$，且有

$$
q(t)=q(u),\qquad b(t)\ne b(u).
$$

则不存在满足下式的全局确定性策略：

$$
\pi:S\to A,\qquad \forall v\in T,\quad \pi(q(v))=b(v).
$$

第 115 节开篇“内积式的等式传递”应理解为函数对相等的保持及等式传递；该命题不要求内积、概率或量子结构。这里 $b(v)$ 是任务规定必须实现的标签，不是从多个最优标签中任意挑出的一个标签。

证明。若 $\pi$ 存在，对 $q(t)=q(u)$ 应用 $\pi$，得到

$$
b(t)=\pi(q(t))=\pi(q(u))=b(u),
$$

与假设矛盾。这正是[无记忆动作障碍](../../../D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction.lean)的等式论证。

**定义 118.4（有限任务的期望动作风险）。** 取有限非空集合 $T,A$、函数 $q:T\to S$ 与必须实现的标签 $b:T\to A$，并令 $S=q[T]$。给定概率质量

$$
\mu:T\to[0,1],\qquad \sum_{v\in T}\mu(v)=1,
\qquad T_+=\{v\in T:\mu(v)>0\}.
$$

随机策略是 $K:S\to\Delta(A)$，其中 $\Delta(A)$ 是 $A$ 上概率向量的集合；确定性策略 $\pi$ 对应 $K_s=\delta_{\pi(s)}$。零一损失及其风险定义为

$$
\ell_{01}(v,a)=\mathbf 1_{\{a\ne b(v)\}},
\qquad
\mathcal R_{01}(K)=
\sum_{v\in T}\mu(v)\sum_{a\in A}K_{q(v)}(a)\ell_{01}(v,a).
$$

所有策略只能依赖 $q(v)$；这里的随机化不包含额外获知 $v$ 的旁信息。

**命题 118.5（第 115.5 节的支持集修正）。** 在定义 118.4 下，若 $q(t)=q(u)$ 且 $b(t)\ne b(u)$，则每个确定性或随机策略满足

$$
\mathcal R_{01}(K)\ge\min\{\mu(t),\mu(u)\}.
$$

因此这对碰撞给出严格正的下界，须有 $\mu(t)>0$ 且 $\mu(u)>0$。存在零风险策略当且仅当 $b$ 在每个 $q$ 纤维与 $T_+$ 的交上恒定；存在处处正确的确定性策略当且仅当 $b$ 在每个完整 $q$ 纤维上恒定。第 115.5 节“存在不同必需动作，则任何确定性无记忆策略的动作风险都不可能为零”须以上述支持集与损失条件代替。

证明。记共同记录为 $s$，$m=\min\{\mu(t),\mu(u)\}$。损失非负，且不同标签的概率之和至多一，故

$$
\begin{aligned}
\mathcal R_{01}(K)
&\ge\mu(t)(1-K_s(b(t)))+\mu(u)(1-K_s(b(u)))\\
&\ge m\bigl(2-K_s(b(t))-K_s(b(u))\bigr)\ge m.
\end{aligned}
$$

风险为零时，每个正质量点的非负项都为零，因此 $K_{q(v)}(b(v))=1$。同一纤维不能以概率一输出两个不同标签。反之，若每个正质量纤维的标签相同，令策略输出该标签；无正质量点的纤维任选 $A$ 中一个标签，风险即为零。把 $T_+$ 换成 $T$，同一逐纤维构造与命题 118.3 给出处处正确的充要条件。

零质量反例为

$$
T=A=\{0,1\},\quad S=\{*\},\quad q(0)=q(1)=*,
\quad b(v)=v,\quad \mu(0)=1,\quad\mu(1)=0.
$$

常策略 $\pi(*)=0$ 的期望风险为零，却在点一错误；全局正确策略不存在。由此，几乎处处零风险与全局可实现性不能互换。

**命题 118.6（一般损失所需的分离）。** 保持定义 118.4 的有限集合与概率，改取有限实值损失 $\ell:T\times A\to[0,\infty)$，并按同一公式定义 $\mathcal R_\ell$。若 $t\ne u$、$q(t)=q(u)$，且存在 $\eta>0$ 使

$$
\forall a\in A,\qquad \ell(t,a)+\ell(u,a)\ge\eta,
$$

则所有只依赖 $q$ 的随机策略满足

$$
\mathcal R_\ell(K)\ge\eta\min\{\mu(t),\mu(u)\}.
$$

仅有不同标签而没有损失分离不蕴含此结论。

证明。非负性允许删去其余状态的风险项，再将两质量分别降低到其最小值。共同动作分布的总质量为一，所以

$$
\mathcal R_\ell(K)
\ge\min\{\mu(t),\mu(u)\}
\sum_{a\in A}K_{q(t)}(a)\bigl(\ell(t,a)+\ell(u,a)\bigr)
\ge\eta\min\{\mu(t),\mu(u)\}.
$$

若 $\ell$ 恒零，即使 $t,u$ 都有正质量且指定标签不同，每个策略仍有零风险。若损失可取负值，其余状态的负贡献又能抵消碰撞代价，因此非负性也不能无条件删除。

**命题 118.7（第 116.3 节最小性的准确方向）。** 对总更新 $I_u:X\to X$ 及读出 $c:X\to O$，令空词作用为恒等，非空词先执行首字母，再执行尾词，并定义

$$
\operatorname{Dyn}_I(c)(x)(w)=c(I_w(x)),\qquad w\in U^*.
$$

细化关系的方向固定为

$$
\operatorname{Refines}(c,d)
\quad\Longleftrightarrow\quad
\exists f:D\to O,\quad c=f\circ d,
\qquad d:X\to D.
$$

若 $d$ 保留 $c$ 且每个 $I_u$ 保持 $d$ 的纤维，则

$$
\operatorname{Refines}(\operatorname{Dyn}_I(c),d),
\quad\text{即}\quad
\exists g:D\to(U^*\to O),\quad \operatorname{Dyn}_I(c)=g\circ d.
$$

这保留当前 $c$ 及全部未来 $c$，不包含任何未进入读出的独立动作要求。

证明。直接应用[动态闭包最小性定理](../../../D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.lean)，其前提正是 $c=f\circ d$ 与纤维保持，结论正是所列 $g$。空词求值给出 $c(x)=\operatorname{Dyn}_I(c)(x)([])$。该结论中的全部响应坐标均为 $c\circ I_w$，没有未指定的动作读出。

**命题 118.8（行动完备所需的联合读出）。** 第 115.2 节把预测商用于行动时，以及第 116.3 节末段和第 116.8 节“保持预测与行动闭合的最小响应细化”的表述，须相对于指定的必须动作读出 $b:X\to A$ 使用

$$
\widetilde c(x)=(c(x),b(x)).
$$

$\operatorname{Dyn}_I(\widetilde c)$ 是同时保留 $c,b$ 的干预闭合细化中的最小者；其空词坐标恢复当前必须动作。若仍使用 $\operatorname{Dyn}_I(c)$，则当前行动完备需要另外假设存在

$$
\beta:\operatorname{Dyn}_I(c)[X]\to A,
\qquad b=\beta\circ\operatorname{Dyn}_I(c),
$$

其中复合使用动态闭包到其实际像的映射。

证明。干预后任意词的响应等于干预前加上该首字母的词响应，故动态闭包的纤维被每次干预保持。联合读出的两投影恢复 $c,b$；任何同时保留两者的接口 $d$ 都通过配对因子保留 $\widetilde c$，再应用命题 118.7 的最小性。原读出单独不足的反例是

$$
X=A=\{0,1\},\quad O=\{*\},\quad U=\{e\},
\quad I_e=\operatorname{id},\quad c(x)=*,\quad b(x)=x.
$$

此时 $\operatorname{Dyn}_I(c)$ 恒定，不能恢复 $b$；而 $\operatorname{Dyn}_I(\widetilde c)$ 的空词已经区分两个状态。故独立动作要求不能由原动态闭包自动获得。若有多个必须动作或其他任务读出，应将它们的乘积一起纳入初始读出，结论按同一投影与配对适用。

**命题 118.9（第 116.4 节的整个操作语言与被动演化）。** 若 $u_*\notin U$ 是新增字母，旧字母的更新保持原样，则响应坐标的指标集由 $U^*$ 扩为

$$
(U')^*=(U\cup\{u_*\})^*,
\qquad
(U')^*\setminus U^*=\{w\in (U')^*:w\text{ 至少含一次 }u_*\}.
$$

新增字母可在词的任意位置出现，也可重复出现；不只增加以 $u_*$ 开头的词。因此完整响应等价满足

$$
\ker\operatorname{Dyn}_{I'}(c)
\subseteq\ker\operatorname{Dyn}_I(c).
$$

若没有输入字母，或所有允许更新均为恒等，则动态闭包与当前 $c$ 有相同纤维。若“没有干预”仍包含被动演化 $F$，则须把 $F$ 明确纳入更新或任务族，才会要求保留 $c(F^n(x))$。

证明。有限词属于 $(U')^*$ 而不属于 $U^*$，恰当其中出现了新字母。将扩充响应函数限制到旧词，即恢复旧响应，给出核的包含。空字母表只有空词；恒等更新的任意复合也是恒等，所以这两个情形均只比较当前 $c$。被动 $F$ 未列入时，所定义的词作用中没有 $F$，因而不能从该定义推出其未来读数相同。

**命题 118.10（第 116.5 节的剩余视野与稳定条件）。** 在固定的总更新模型上定义

$$
E_N(x,y)\quad\Longleftrightarrow\quad
\forall w\in U^*,\ |w|\le N\Longrightarrow c(I_w(x))=c(I_w(y)).
$$

有限深度接口恰保留被查询的这些响应；其正确递归为

$$
E_0(x,y)\Longleftrightarrow c(x)=c(y),
$$

$$
E_{N+1}(x,y)
\Longleftrightarrow
c(x)=c(y)\ \land\ \forall u\in U,\ E_N(I_u(x),I_u(y)).
$$

所以

$$
E_{N+1}\subseteq E_N,\qquad
E_{N+1}(x,y)\Longrightarrow E_N(I_u(x),I_u(y)),
$$

$$
N\ge1,\ E_N(x,y)\Longrightarrow E_{N-1}(I_u(x),I_u(y)).
$$

这些式子不宣称 $E_N$ 被一步更新保持在同一深度。若整个二元关系满足 $E_N=E_{N+1}$，则该层对全部更新稳定，并永久等于全部有限词的响应关系。这里需要关系在所有状态对上的相等，不能以一个状态对在相邻两层都成立来代替。

证明。将非空词唯一分成首字母与尾词，尾词长度减少一，得到递归；缩小查询词集得到包含。由全关系相等和递归，$E_N$ 的每对后继仍在 $E_N$ 中；沿词归纳，得到任意长度响应相等。这是第 106.2 节所用的永久稳定原理。在 $X,U,O$ 固定有限非空、更新为总函数且 $c:X\to O$ 满射时，直接使用第 106.3 节及[ControlledFiniteStability](../../../D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability.lean)的已有结论：存在最小稳定深度 $H$，并有

$$
H\le |X/E_\infty|-|O|\le |X|-|O|,
\qquad E_\infty=\bigcap_{n\ge0}E_n.
$$

应用该界时可把 $O$ 限制为实际像 $c[X]$，以满足满射条件；该有限性条件不能由只固定一个查询深度代替。递减视野的部分操作版本亦见[Zeckendorf 卷定理 446.2](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)。

同层闭合与逐对稳定的反例可同时取

$$
X=\{0,1,2,3,4\},\quad U=\{e\},\quad
I_e(i)=\min\{i+1,4\},\quad c(i)=\mathbf 1_{\{i=4\}}.
$$

状态零与一在深度一及二的响应都相同，但三次更新后的读数分别为零与一。因此 $E_1(0,1)$ 与 $E_2(0,1)$ 都成立，不蕴含完整等价；同时 $E_2(0,1)$ 成立而 $E_2(I_e(0),I_e(1))=E_2(1,2)$ 不成立。

若某个记录 $q$ 合并 $x,y$，而某词 $w$ 使 $c(I_w(x))\ne c(I_w(y))$，该词证明任务 $c\circ I_w$ 不能经 $q$ 因子化。第 116.5 节“某条长度至多 $N$ 的词把它们分开，则当前接口不闭合”应按这一任务不足解释；它本身不证明深度 $N$ 接口违反同层更新不变性，后者须另检验上面的后继关系。

**命题 118.11（第 117.3、117.4 节的时域及共同选择）。** 固定共同的有限非空动作集 $A$、确定性总转移 $T$、实值奖励 $r$ 与终值 $V^0$，令

$$
V_0=V^0,\qquad
Q_n(s,a)=r(s,a)+V_n(T(a,s)),
\qquad V_{n+1}(s)=\max_{a\in A}Q_n(s,a),
$$

$$
\operatorname{Opt}_n(s)=\operatorname*{arg\,max}_{a\in A}Q_n(s,a).
$$

第 117.3 节的下标 $n$ 计续接的 $n$ 个阶段；再加当前动作，所优化的总阶段数是 $n+1$。若微观与宏观模型通过 $\alpha$ 同时满足第 117.1 节的转移、奖励和终值三项因子化，则对同一个 $n$ 有

$$
Q_n^{m}(s,a)=Q_n^{M}(\alpha(s),a),\qquad
\operatorname{Opt}_n^{m}(s)=\operatorname{Opt}_n^{M}(\alpha(s)).
$$

这些集合非空。固定 $A$ 上一个全序，取每个集合的最小元素，就得到只依赖 $\alpha(s)$ 与剩余阶段数的共同确定性最优选择。它不要求不同历史任意挑出的最优标签相等。

证明。由[有限时域值因子化](../../../D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization.lean)恢复续值，再用奖励与转移相容，得到各动作分数相同；[最优动作下沉](../../../D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent.lean)给出集合相等。有限非空实值集合有最大值，其最大化动作集合因此非空；相同非空集合在固定全序下有同一最小元素。

更一般地，对任意记录 $q$ 和同一时域的最优集合，只要求存在共同最优策略的准确条件是

$$
\forall z\in q[X],\qquad
\bigcap_{s\in q^{-1}(z)}\operatorname{Opt}_n(s)\ne\varnothing.
$$

策略的共同输出给出交集中的元素；反向在每个交集中按固定全序取最小元素即可。故集合相等是足够条件，单纯两个选择标签不同不是障碍判据。若在共同动作、同一时域和同一任务下，确有同一抽象纤维的最优集合不同，才可据前述因子化定理断定三项相容条件不能全部成立。第 117.7 节“如果要求有限时域行动，就必须验证值函数闭合”仅适用于任务还要求恢复最优价值的情形；仅选择一个最优动作时，上述非空交集已是准确判据。例如两状态使用恒等转移、单一动作、零终值，阶段奖励分别为零与一，常记录仍支持唯一动作，但正时域 $n$ 的值分别为零与 $n$。

**命题 118.12（并列最优及跨时域选择的两个反例）。** 第 117.4 节“保证这种分离不会发生”仅排除在其假设下最优集合的分离，不排除任意最优标签选择的分离；第 115.5 节末段所说“不同的最优动作分布”也不能仅凭分布不同排除共同最优策略。各时域最优集合在抽象纤维上相同，还不保证存在对所有时域都最优的、与剩余阶段数无关的平稳策略。

证明。第一个例子取微观状态 $\{0,1\}$、宏观状态 $\{*\}$、常抽象、动作 $A=\{L,R\}$。两层每个动作的转移均为恒等，全部奖励与终值均为零。三项因子化全部成立，且

$$
\forall n,s,\qquad V_n(s)=0,\qquad\operatorname{Opt}_n(s)=\{L,R\}.
$$

在状态零选择 $L$、在状态一选择 $R$，两者都是最优动作；对应的两个点质量分布也都最优。固定选 $L$ 仍是共同最优策略。若另把这两个不同标签规定成必须实现的 $b(0),b(1)$，那是命题 118.3 的另一个任务，不能与只要求最优混同。

第二个例子取状态 $\{s,g\}$、动作 $\{W,H\}$、恒等抽象与零终值。规定

$$
T(W,s)=s,\quad r(s,W)=1,\qquad
T(H,s)=g,\quad r(s,H)=0,
$$

$$
T(a,g)=g,\quad r(g,a)=2\qquad(a\in\{W,H\}).
$$

恒等抽象满足全部因子化。一步时在 $s$ 的分数为一与零，故 $\operatorname{Opt}_0(s)=\{W\}$；两步值为 $V_2(s)=2,V_2(g)=4$，三步的当前分数为三与四，故 $\operatorname{Opt}_2(s)=\{H\}$。同一平稳选择不能同时满足这两个单点要求。

**命题 118.13（值相等不能反推全部控制因子）。** 第 117.6 节的值相等只给指定任务的数值结论。即使所有有限时域的值都在同一纤维上相等，也不蕴含最优动作集合、转移或奖励因子化；只给一个正时域的值相等，还不能推出终值因子化。若相等的时域包含零，则终值因子化由 $V_0=V^0$ 直接成立，但仍不推出另外两项。

证明。先取两个状态 $x,y$、常记录、动作 $\{L,R\}$、恒等转移和零终值，令

$$
r(x,L)=r(y,R)=1,\qquad r(x,R)=r(y,L)=0.
$$

于是 $V_n(x)=V_n(y)=n$，而对每个 $n\ge0$，最优集合分别为 $\{L\}$ 与 $\{R\}$；奖励也不经常记录因子化。

再取三个状态 $x,y,z$，$\alpha(x)=\alpha(y)=0,\alpha(z)=1$，一个动作 $a$，零奖励与零终值，令

$$
T(a,x)=x,\qquad T(a,y)=z,\qquad T(a,z)=z.
$$

全部值恒零，但同一抽象初值零有抽象后继零与一，不存在相容的宏观转移。

最后取两个状态、常记录、一个动作与恒等转移，令

$$
r(x,a)=0,\quad V^0(x)=0,\qquad
r(y,a)=-1,\quad V^0(y)=1.
$$

一步值均为零，终值却不同。三个例子分别排除所述逆推；关于零时域的限定直接来自递归初值。

**命题 118.14（有限构型与密度矩阵的不同载体）。** 第 115.4、116.6、117.6 节的量子解释不由经典构型有限性自动成立。即使合法构型集 $\mathcal W_L$ 有限，若

$$
\mathcal H_Z=\operatorname{span}\{|w\rangle:w\in\mathcal W_L\},
\qquad \dim\mathcal H_Z\ge2,
$$

其全部密度矩阵集合 $\mathcal D(\mathcal H_Z)$ 仍为无限集。对指定通道词 $\Phi_w$ 与 POVM $\{M_o\}_o$，可以定义抽象响应函数

$$
\rho\longmapsto
\left(\operatorname{tr}(M_o\Phi_w(\rho))\right)_{w,o},
\qquad M_o\ge0,\quad\sum_oM_o=\mathbf 1.
$$

这是每个指定实验的概率函数族。第 116.8 节关于“经典轨迹函数”的量子边界须区分此集合论函数与物理编码：前者可以如此定义，后者不由定义给出。该函数不自动给出一个物理 CPTP 编码，也不自动给出从同一次制备中同时读出这些概率精确值的经典寄存器。

证明。取两个正交合法基态 $|e_0\rangle,|e_1\rangle$，则

$$
\rho_p=p|e_0\rangle\langle e_0|+(1-p)|e_1\rangle\langle e_1|,
\qquad 0\le p\le1
$$

彼此不同，已构成连续一族密度矩阵。故有限 Hilbert 维数并非有限状态集合的基数。

抽象函数与物理精确标签编码的区别甚至在此对角族上存在。若某通道 $\mathcal E$ 能把 $p=0,\tfrac12,1$ 的精确概率标签输出为三个互相正交的确定经典旗标，则既要求

$$
\mathcal E(\rho_{1/2})=|f_{1/2}\rangle\langle f_{1/2}|,
$$

又由通道的仿射性要求

$$
\mathcal E(\rho_{1/2})
=\tfrac12|f_0\rangle\langle f_0|+\tfrac12|f_1\rangle\langle f_1|.
$$

两式的支持子空间不同，矛盾。抽象地写出各响应概率不受此限制，因为它没有宣称存在这种确定标签通道。抽样获得一个结果、在重复制备下估计概率、以及一次制备输出概率的精确标签，是不同的输出任务。

**命题 118.15（第 115.4 节相位响应的物理假设与行动边界）。** 在指定的有限维正交基下，若使用该节的 Schur 形式作为记录通道，须要求同阶记录矩阵 $R$ 半正定且 $R_{ii}=1$；此时

$$
\mathcal C(\rho)_{ij}=R_{ij}\rho_{ij}
$$

确为 CPTP 映射。若使用该节的三态耦合，取 $g\in\mathbb R\setminus\{0\}$，在合法子空间 $\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}$ 上规定

$$
H=g\bigl(|00\rangle\langle01|+|00\rangle\langle10|
+|01\rangle\langle00|+|10\rangle\langle00|\bigr).
$$

取 $\hbar=1$；若嵌入更大的空间，要求自伴扩张满足 $[H,P_Z]=0$，其他允许通道也须保持合法态域。则对该节的 $|B\rangle,|D\rangle$，时间 $\tau$ 后测量 $|00\rangle\langle00|$ 的概率分别为

$$
p_B(\tau)=\sin^2(\sqrt2g\tau),\qquad p_D(\tau)=0.
$$

当 $\sin^2(\sqrt2g\tau)>0$ 时，这是不同实验响应的见证；要进一步推出必须动作或最优动作不同，还须指定相应任务或奖励，不能只用耦合差异推出行动标签差异。

证明。半正定矩阵分解给出系数 $v_{i\lambda}$ 满足

$$
R_{ij}=\sum_\lambda v_{i\lambda}\overline{v_{j\lambda}},
\qquad \sum_\lambda|v_{i\lambda}|^2=1.
$$

对角 Kraus 算子 $K_\lambda=\operatorname{diag}(v_{i\lambda})$ 实现 $\mathcal C$，且 $\sum_\lambda K_\lambda^\dagger K_\lambda=\mathbf1$。相位耦合的 $H$ 自伴，并满足

$$
H|B\rangle=\sqrt2g|00\rangle,\quad
H|00\rangle=\sqrt2g|B\rangle,\quad H|D\rangle=0.
$$

因此

$$
e^{-i\tau H}|B\rangle
=\cos(\sqrt2g\tau)|B\rangle-i\sin(\sqrt2g\tau)|00\rangle,
\qquad e^{-i\tau H}|D\rangle=|D\rangle.
$$

Born 规则给出所列概率。另一方面，若所有动作奖励和终值均为零，任何允许动作均最优，故响应不同并不强制最优标签不同。

**命题 118.16（重复测量与反馈的条件性经典描述）。** 第 117.6 节“先固定一个 POVM 或记录通道”不足以直接得到确定性 Bellman 模型。设动作集 $A$ 与结果集 $O$ 有限非空，对每个动作给定量子仪器

$$
\{\mathcal J_{a,o}:o\in O\},
\qquad \mathcal J_{a,o}\text{ 完全正且不增迹},
\qquad \sum_o\mathcal J_{a,o}\text{ 保迹}.
$$

每个分支须保持指定合法子空间；若有可回流的环境记忆，态描述须包含它或足以预测其影响的信息。仪器给出

$$
p(o\mid\rho,a)=\operatorname{tr}\mathcal J_{a,o}(\rho),
\qquad
\rho'_{a,o}=\frac{\mathcal J_{a,o}(\rho)}{p(o\mid\rho,a)}
\quad\text{仅在 }p(o\mid\rho,a)>0\text{ 时定义}.
$$

若另有一个非空有限经典状态描述集 $Z$，控制器在决策前能由实际可访问记录确定 $z$，每个动作在每个可达描述处均允许，且在同一当前描述 $z$ 下的所有可达历史，对每个动作均有相同的后继描述与结果联合分布

$$
P_a(z',o\mid z),\qquad
\sum_{z',o}P_a(z',o\mid z)=1,
$$

并且阶段奖励和终值分别由实值函数 $r(z,a,z',o)$ 与 $V^0(z)$ 给出，则有限时域的期望价值递归为

$$
V_0(z)=V^0(z),\qquad
V_{n+1}(z)=\max_{a\in A}
\sum_{z',o}P_a(z',o\mid z)
\bigl(r(z,a,z',o)+V_n(z')\bigr).
$$

此结论以所列受控 Markov 充分性为假设；当前输出字母有限、记录寄存器维数有限或给定一个 POVM，都不单独蕴含该假设。若每个 $(z,a)$ 的后继描述边缘集中在一个 $T(a,z)$，并定义

$$
\bar r(z,a)=\sum_{z',o}P_a(z',o\mid z)r(z,a,z',o),
$$

则在这一确定后继描述下，上式化为

$$
V_{n+1}(z)=\max_{a\in A}\bigl(\bar r(z,a)+V_n(T(a,z))\bigr).
$$

使用第 117 节的确定性因子化结论时，还须对这个 $T,\bar r,V^0$ 验证同一抽象的三项条件。

证明。完全正与迹条件使各分支概率非负且总和为一；正概率分支的归一化输出为密度矩阵，零概率分支不要求定义后验。给定受控 Markov 充分性，先条件于当前动作，再条件于下一描述与结果，有限期望的全概率分解及剩余时域归纳给出递归。有限非空动作集保证最大值可达，随机化当前动作只形成动作价值的凸组合，不能超过其最大值。若后继描述边缘为点质量，续值项从求和中提出，即得最后一式。

随机后继的直接例子是对 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ 作计算基底投影测量。两结果各有概率 $1/2$；记录结果的两个后继历史不同，条件态也分别为 $|0\rangle\langle0|$ 与 $|1\rangle\langle1|$。因此重复或反馈测量一般产生随机受控核。将结果平均后的通道作为密度矩阵上的确定函数，是另一个明确的状态描述；它不自动保留可按结果分支的反馈策略。经典核的风险与价值结论由所指定实验及其经典描述承担，不把该核认同为全部相干量子动力学。

## 追加锚（本行以下为增补区）
## 119. 记录模拟的缺陷与决策风险：从保留历史到可执行误差界

**定义 119.1（原历史载体与有限观察的取域）。** 原情境仍取[《情境时空算术》定义 1–6](CONTEXTUAL_SPACETIME_ARITHMETIC.md)的

$$
C=(E_C,\prec,t,x,\sigma,\rho,\Omega),\qquad
\eta=(C,A_{\rm sel}),\qquad A_{\rm sel}\subseteq\Omega\subseteq E_C,
$$

其中 $E_C$ 是有限事件出现集，$\prec$ 是严格偏序，$t:E_C\to\mathbb Z$、$x:E_C\to\mathbb Z^3$、$\sigma:E_C\to\{+1,-1\}$ 及来源树映射 $\rho$ 保留原类型，且 $e\prec f$ 蕴含 $t(e)<t(f)$。算术载体仍要求 $\sum_{e\in\Omega}\sigma(e)=0$，读数为 $q_{\rm CSA}(\eta)=\sum_{e\in A_{\rm sel}}\sigma(e)$。选择是当前区域的任意子集；若任务还使用各阶段的选择或区域快照，就将这些快照另列为历史数据。时间复合的原定义域仍为

$$
\forall e\in E_{C_1}\ \forall f\in E_{C_2},\qquad t_1(e)<t_2(f).
$$

用于下述有限观察比较的历史族，是预先指定的原合法对象或合法执行历史的有限非空族；每条执行路径分别满足其操作守卫。有限标签及其概率律是这个族的观察数据，不替换档案、来源、绝对时间、偏序、当前区域或选择。若只讨论抽象统计实验，则直接使用定义 119.2，不预设其标签已实现为原历史。

**定义 119.2（有限实验、共同决策与单向缺陷）。** 设隐藏参数集 $\Theta$、目标观察集 $Y$、保留观察集 $Z$、共同动作集 $A$ 均有限非空。参数 $\theta\in\Theta$ 固定而对决策者未知。实验由实值行概率给出：

$$
F(y\mid\theta)\ge0,\quad \sum_{y\in Y}F(y\mid\theta)=1,
\qquad
E(z\mid\theta)\ge0,\quad \sum_{z\in Z}E(z\mid\theta)=1.
$$

记相应概率行为 $F_\theta,E_\theta$。模拟器 $S:Z\to\mathcal P(Y)$ 表示从 $Z$ 到 $Y$ 的随机核，其中 $\mathcal P(Y)$ 是 $Y$ 上的概率单纯形，即 $S(y\mid z)\ge0$ 且 $\sum_yS(y\mid z)=1$；同一个 $S$ 用于所有 $\theta$，不能读取隐藏参数。复合律与全变差约定为

$$
(SE)_\theta(y)=\sum_z E(z\mid\theta)S(y\mid z),\qquad
\operatorname{TV}(p,q)=\frac12\sum_i|p(i)-q(i)|.
$$

定义模拟误差及单向缺陷

$$
\varepsilon(S)=\max_{\theta\in\Theta}\operatorname{TV}(F_\theta,(SE)_\theta),
\qquad
\delta(F\mid E)=\inf_{S:Z\to\mathcal P(Y)}\varepsilon(S),
$$

方向是从保留实验 $E$ 模拟目标实验 $F$；“目标”与“保留”本身不预设信息次序。给定先验 $\mu(\theta)\ge0$、$\sum_\theta\mu(\theta)=1$ 及损失 $0\le\ell(\theta,a)\le1$，观察集为 $O$ 的实验 $G$ 上的随机决策为 $d:O\to\mathcal P(A)$，其代价及最优 Bayes 风险为

$$
\mathcal C_{\mu,\ell}(G,d)
=\sum_{\theta\in\Theta}\mu(\theta)
  \sum_{o\in O}\sum_{a\in A}G(o\mid\theta)d(a\mid o)\ell(\theta,a),
\qquad
R_{\mu,\ell}(G)=\inf_d\mathcal C_{\mu,\ell}(G,d).
$$

比较中始终使用同一 $\mu,\ell,A$，简记风险为 $R(G)$。这里 $E,F,S,d$ 均为非负归一的概率核，不能以任意带符号矩阵替代。

**命题 119.3（有限实值极值与扩展非负实数的对应）。** 在定义 119.2 下，$R(E),R(F),\delta(F\mid E)$ 都是 $[0,1]$ 中的实数，其下确界均可取到。把非负实数嵌入 $[0,\infty]$ 后，这些值分别等于同一随机核族上的扩展非负实数下确界。此对应适用于[有限实验风险与缺陷的定义及定理 `deficiency_risk_bound`](../../../D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.lean)所采用的下确界约定。

证明。概率行的全变差在 $[0,1]$ 内，且每个代价是 $[0,1]$ 中损失值的概率加权和。非空输出集提供常值确定性核，所以各优化域非空。有限个概率单纯形的乘积是非空紧集；代价是连续函数，模拟误差是有限个连续全变差函数的最大值，亦连续。因此三种下确界均为取得的有限最小值。非负实数的嵌入保持这些值的次序及最小元，故在 $[0,\infty]$ 中取下确界得到同一个嵌入值。证毕。

**定理 119.4（缺陷控制有界决策风险）。** 在定义 119.2 的全部假设下，

$$
R(E)\le R(F)+\delta(F\mid E).
$$

这是[定理 `deficiency_risk_bound`](../../../D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.lean)在上述有限实值约定下的风险转移结论；固定模拟器的风险比较见[定理 `bounded_loss_risk_stability_of_simulator`](../../../D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport.lean)。

证明。先给出两个有限概率不等式。若 $p,q$ 是同一有限集上的概率，$h_i=p(i)-q(i)$，则 $\sum_i h_i=0$，从而

$$
\sum_{h_i>0}h_i=\sum_{h_i<0}(-h_i)=\frac12\sum_i|h_i|.
$$

对 $0\le f(i)\le1$，丢掉非正项并以一控制正项，得到 $\sum_i h_i f(i)\le\operatorname{TV}(p,q)$；交换 $p,q$ 得

$$
\left|\sum_i p(i)f(i)-\sum_i q(i)f(i)\right|
\le\operatorname{TV}(p,q).
$$

因此 $[0,1]$ 损失对应的系数是一。其次，任一共同随机核 $K$ 满足

$$
\begin{aligned}
\operatorname{TV}(Kp,Kq)
&=\frac12\sum_j\left|\sum_i(p(i)-q(i))K(j\mid i)\right|\\
&\le\frac12\sum_i|p(i)-q(i)|\sum_jK(j\mid i)
=\operatorname{TV}(p,q).
\end{aligned}
$$

现在固定模拟器 $S$ 和基于 $F$ 的任意决策 $d_F$，在 $E$ 上执行

$$
d_E(a\mid z)=\sum_y S(y\mid z)d_F(a\mid y).
$$

各项非负，且 $\sum_a d_E(a\mid z)=\sum_yS(y\mid z)=1$，所以 $d_E$ 是合法决策。有限和交换给出 $d_EE_\theta=d_F(SE)_\theta$。对每个 $\theta$，随机后处理的全变差收缩及上述损失不等式给

$$
\begin{aligned}
\sum_a(d_EE)_\theta(a)\ell(\theta,a)
&\le\sum_a(d_FF)_\theta(a)\ell(\theta,a)
   +\operatorname{TV}(d_F(SE)_\theta,d_FF_\theta)\\
&\le\sum_a(d_FF)_\theta(a)\ell(\theta,a)+\varepsilon(S).
\end{aligned}
$$

以非负的 $\mu(\theta)$ 加权求和，并使用 $\sum_\theta\mu(\theta)=1$，得到

$$
R(E)\le\mathcal C_{\mu,\ell}(E,d_E)
\le\mathcal C_{\mu,\ell}(F,d_F)+\varepsilon(S).
$$

任取 $\eta>0$，分别选取代价小于 $R(F)+\eta/2$ 的决策和误差小于 $\delta(F\mid E)+\eta/2$ 的模拟器。两者的优化域独立，故 $R(E)<R(F)+\delta(F\mid E)+\eta$。对所有 $\eta>0$ 成立即得结论；此步只需下确界逼近，不依赖选择最优核。证毕。

**命题 119.5（真实经典粗化的双边风险界与必要方向）。** 若另有一个与 $\theta$ 无关的随机核 $C:Y\to\mathcal P(Z)$ 满足

$$
E_\theta(z)=(CF)_\theta(z)=\sum_yF_\theta(y)C(z\mid y)
\qquad(\theta\in\Theta),
$$

则

$$
0\le R(E)-R(F)\le\delta(F\mid E).
$$

若只给定义 119.2 的两个实验，则 $R(F)\le R(E)$ 不必成立，定理 119.4 的单向风险界仍成立。

证明。任取 $E$ 上的决策 $d_E$，令 $d_F(a\mid y)=\sum_z C(z\mid y)d_E(a\mid z)$。它是随机核，且 $d_FF=d_EE$，所以两代价相等。对所有 $d_E$ 取下确界给出 $R(F)\le R(E)$，再用定理 119.4 得到双边界。

为证明没有粗化关系时左界可以失败，取 $\Theta=Z=A=\{0,1\}$、$Y=\{*\}$、均匀先验和 $\ell(\theta,a)=\mathbf1_{\{a\ne\theta\}}$，令 $E_\theta=\delta_\theta$、$F_\theta=\delta_*$。观察 $E$ 后选 $a=\theta$ 给 $R(E)=0$。只观察 $*$ 的任意决策成功率均为 $\tfrac12(d(0\mid*)+d(1\mid*))=1/2$，故 $R(F)=1/2$。丢弃 $E$ 的输出能精确模拟 $F$，所以 $\delta(F\mid E)=0$；单向不等式为 $0\le1/2$，而左界失败。证毕。

**定理 119.6（确定性标签压缩的精确缺陷）。** 设 $X$ 为有限非空标签集，$q:X\to B$ 满射到其实际像 $B$。取 $\Theta=Y=X$、$Z=B$，并令

$$
F_x=\delta_x,\qquad E_x=\delta_{q(x)},\qquad
X_b=q^{-1}(b),\qquad m_b=|X_b|,\qquad m_{\max}=\max_{b\in B}m_b.
$$

则 $m_b\ge1$，且

$$
\delta(F\mid E)=1-\frac1{m_{\max}}.
$$

证明。对任意模拟器 $S:B\to\mathcal P(X)$，记 $S_b(x)=S(x\mid b)$。概率归一性给

$$
\operatorname{TV}(\delta_x,S_{q(x)})
=\frac12\left(1-S_{q(x)}(x)+\sum_{u\ne x}S_{q(x)}(u)\right)
=1-S_{q(x)}(x).
$$

取最大纤维 $X_{b_*}$。由于 $\sum_{x\in X_{b_*}}S_{b_*}(x)\le1$，其中至少一个 $x$ 满足 $S_{b_*}(x)\le1/m_{\max}$，所以每个模拟器的最坏参数误差至少为 $1-1/m_{\max}$。反向定义只依赖保留标签的模拟器

$$
S(x\mid b)=
\begin{cases}
1/m_b,&q(x)=b,\\
0,&q(x)\ne b.
\end{cases}
$$

每行在非空纤维上均匀且总和为一。参数 $x\in X_b$ 的误差恰为 $1-1/m_b$，其最大值为 $1-1/m_{\max}$。上下界相合，得精确公式。这个模拟器只读取 $b$，并未读取真正的 $x$。证毕。

**定理 119.7（任意先验下的完整标签重建风险）。** 沿用定理 119.6，另取动作 $A=X$、损失 $\ell(x,a)=\mathbf1_{\{a\ne x\}}$ 及任意概率先验 $\mu$，允许任意标签的先验质量为零。则

$$
R(F)=0,\qquad
R(E)=1-\sum_{b\in B}\max_{x\in X_b}\mu(x).
$$

证明。细观察直接给出 $x$，选 $a=x$ 即得零代价，非负性给 $R(F)=0$。粗观察决策 $d$ 的总成功率为

$$
\operatorname{Succ}(d)=\sum_{b\in B}\sum_{x\in X_b}\mu(x)d(x\mid b).
$$

令 $M_b=\max_{x\in X_b}\mu(x)$。每个纤维对成功率的贡献是动作概率对系数 $\mu(a)\mathbf1_{\{a\in X_b\}}$ 的凸组合，故

$$
\sum_{x\in X_b}\mu(x)d(x\mid b)
\le M_b\sum_{x\in X_b}d(x\mid b)\le M_b.
$$

在每个非空有限纤维中选择一个达到 $M_b$ 的代表 $x_b$，并令 $d(x_b\mid b)=1$，则同时达到所有上界。失败风险等于一减成功率，得到所述公式。即使 $M_b=0$，任一代表仍达到上界，证明无需按该纤维质量做条件归一化。证毕。

**命题 119.8（三位合法行的奇偶压缩）。** 取[Zeckendorf 源卷定义 3、9、11](CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的权重 $G_0=1,G_1=2,G_2=3$。本条显示字 $w=w_2w_1w_0$ 按高位到低位书写，是该源定义 9 中低位到高位次序 $(c_0,c_1,c_2)$ 的反转。令

$$
X=\{000,001,010,100,101\},\qquad
V(w)=3w_2+2w_1+w_0,\qquad q(w)=V(w)\bmod2.
$$

这是单行数值观察：源中的 $s(n)$ 是整数 $n$ 自身的规范行，而 $K(n)(p,j)=s(v_p(n))_j$ 是正整数的逐素数指数表；本条的 $V$ 与 $q$ 不把这两个编码认作同一对象。对 $F_w=\delta_w$、$E_w=\delta_{q(w)}$，有

$$
\delta(F\mid E)=\frac23.
$$

在 $X$ 上取均匀先验、完整标签重建动作及零一损失，则

$$
R(F)=0,\qquad R(E)=\frac35.
$$

证明。三个位置没有相邻两个一的全部合法字恰为所列五字，其 $V$ 值依次为 $0,1,2,3,4$。因此

$$
X_0=\{000,010,101\},\qquad X_1=\{001,100\},
\qquad m_0=3,\quad m_1=2.
$$

定理 119.6 给出 $1-1/3=2/3$。均匀先验使两个纤维的最大单点质量都为 $1/5$，定理 119.7 给出 $1-1/5-1/5=3/5$。这些公式已对全部随机决策取最优值；$3/5$ 是该先验和重建任务的平均风险，$2/3$ 是不依赖先验的最坏参数模拟缺陷。证毕。

**命题 119.9（任务相对性与资源量的独立性）。** 若存在共同动作 $a_*\in A$，满足

$$
\ell(\theta,a_*)=\min_{a\in A}\ell(\theta,a)
\qquad(\theta\in\Theta),
$$

则对定义 119.2 的任意实验 $G$，

$$
R(G)=\sum_\theta\mu(\theta)\ell(\theta,a_*).
$$

因而即使 $\delta(F\mid E)>0$，也可以有 $R(E)-R(F)=0$；完整标签重建的缺陷不强制等于某个指定预测或动作任务的风险损失。另给每个核任意正实数值的执行时间或资源费用函数，在保持 $E,F,\mu,\ell$ 不变时，定义 119.2 的缺陷与风险均不变。

证明。对固定 $\theta$，任意随机动作的期望损失至少为 $\ell(\theta,a_*)$。加权求和给出风险下界；不看观察而总选 $a_*$ 达到它。取命题 119.8 的实验，并取具有恒零损失的共同动作，得到缺陷为 $2/3$ 而风险差为零的实例。最后，缺陷和风险的定义只用实验概率、先验、损失及随机核族；所附执行时间和费用不出现在这些表达式中，改变它们不改变表达式的值。因此仅凭纤维基数和这些风险公式，不能推出物理时间、存储或耗散的数值关系。证毕。

**假设 119.10（固定量子制备、实际测量与记录层）。** 取有限维非零复 Hilbert 空间 $\mathcal H$ 和有限非空制备标签集 $\Theta$。每个 $\theta$ 指定密度算子 $\varrho_\theta\ge0$、$\operatorname{tr}\varrho_\theta=1$。给定实际采用的固定有限 POVM

$$
H_y\ge0,\quad\sum_{y\in Y}H_y=I_{\mathcal H},
\qquad
G_z\ge0,\quad\sum_{z\in Z}G_z=I_{\mathcal H},
$$

其中 $Y,Z$ 非空，且两族效应不依赖未知 $\theta$。采用 Born 律定义

$$
F_\theta(y)=\operatorname{tr}(\varrho_\theta H_y),\qquad
E_\theta(z)=\operatorname{tr}(\varrho_\theta G_z).
$$

这里 $\theta$ 是制备标签，不预设为未知计算基底标签；允许 $\varrho_\theta$ 在合法 Zeckendorf 子空间内具有相干非对角项。若要把 $E$ 称为已形成细记录的实际经典压缩，另假设先形成 $y$，随后仅用与 $\theta$ 无关的随机核 $C(z\mid y)$ 产生 $z$。此时该压缩的效应为 $G_z=\sum_yC(z\mid y)H_y$。单独的效应等式只规定当前概率，不规定输出的量子后态或测量仪器。

**命题 119.11（固定 Born 实验的风险界及联合样本的非唯一性）。** 在假设 119.10 下，$E,F$ 满足定义 119.2 的行概率条件。故对同一有限非空动作集、概率先验及 $[0,1]$ 损失，定理 119.4 适用；若另有该假设中的实际经典压缩，则命题 119.5 的双边风险界适用。给定这两个当前实验的概率行，并不唯一确定它们之间的联合样本律，更不提供不相容测量在同一次运行中的反事实样本值。

证明。$\operatorname{tr}(\varrho_\theta H_y)=\operatorname{tr}(\varrho_\theta^{1/2}H_y\varrho_\theta^{1/2})\ge0$，对 $y$ 求和为 $\operatorname{tr}\varrho_\theta=1$；$G$ 同理。实际经典压缩时由全概率公式得到 $E=CF$，所以直接应用对应的风险界。上述论证不要求密度算子在某一基底对角。

联合律的非唯一性已在一个制备标签、两个均匀二元边缘上出现：令 $J_1(0,0)=J_1(1,1)=1/2$、其余为零，或令四个 $J_2(y,z)=1/4$，两者边缘相同而联合律不同。这只是概率律之间两种数学耦合，不断言任一耦合是两个不相容量子测量的共同物理实现。模拟器同样只构造目标概率律，不能由此识别为另一测量在同次运行中本会产生的结果。证毕。

**命题 119.12（同奇偶效应、零当前缺陷与不同的两阶段辨识风险）。** 取命题 119.8 的高位到低位合法三位集合 $X$，令

$$
\mathcal H_Z=\operatorname{span}\{|w\rangle:w\in X\},\qquad
P_w=|w\rangle\langle w|,\qquad
Q_b=\sum_{w\in X_b}P_w\quad(b\in\{0,1\}),
$$

其中所列基正交归一，$I$ 表示 $\mathcal H_Z$ 上的恒等算子。考虑两种理想投影测量仪器的未归一分支：粗奇偶 Lüders 仪器

$$
\mathcal L_b(\varrho)=Q_b\varrho Q_b
$$

与完整基底测量后只在经典层忘记细标签的仪器

$$
\mathcal M_b(\varrho)=\sum_{w\in X_b}P_w\varrho P_w.
$$

它们的每个分支均完全正且不增迹，全部分支之和保迹，并有相同的奇偶效应 $Q_b$，所以对每个密度算子给出相同的即时奇偶概率。令隐藏制备标签为 $\theta\in\{+,-\}$，取

$$
|\psi_+\rangle=\frac{|000\rangle+|010\rangle}{\sqrt2},\qquad
|\psi_-\rangle=\frac{|000\rangle-|010\rangle}{\sqrt2},\qquad
\varrho_\theta=|\psi_\theta\rangle\langle\psi_\theta|.
$$

记第一阶段粗 Lüders 奇偶记录的实验为 $E$，完整基底记录的实验为 $F$。则

$$
E_+=E_-=\delta_0,\qquad
F_+=F_-=\tfrac12\delta_{000}+\tfrac12\delta_{010},\qquad
\delta(F\mid E)=\delta(E\mid F)=0.
$$

这里的参数是制备标签 $\{+,-\}$，不同于命题 119.8 中待完整重建的基底标签 $X$；两个缺陷公式属于不同的实验族。令 $P_+=|\psi_+\rangle\langle\psi_+|$，在上述两种仪器之后都对残余系统实际执行第二次测量 $\{P_+,I-P_+\}$，以 $r=1$ 记 $P_+$ 结果，则

$$
\Pr_{\mathcal L}(r=1\mid+) =1,\qquad
\Pr_{\mathcal L}(r=1\mid-) =0,\qquad
\Pr_{\mathcal M}(r=1\mid\theta)=\frac12\quad(\theta=+,-).
$$

因此在均匀先验、动作 $\{+,-\}$ 和零一辨识损失下，以完整两阶段经典记录作决策的风险分别为

$$
R(\mathcal L\hbox{ 的两阶段记录})=0,\qquad
R(\mathcal M\hbox{ 的两阶段记录})=\frac12.
$$

此命题是“相同即时效应不决定两步联合律”的一个合法三位实例；另一明确的二维仪器分离结论见[定理 `same_effects_different_two_step_joint_law`](../../../D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation.lean)。

证明。$Q_0,Q_1$ 是互相正交且和为 $I$ 的投影。$\mathcal L$ 的 Kraus 算子为 $Q_b$，$\mathcal M$ 的分支 Kraus 算子为 $\{P_w:w\in X_b\}$；分别有 $Q_b^*Q_b=Q_b$ 与 $\sum_{w\in X_b}P_w^*P_w=Q_b$。故两仪器完全正，分支不增迹，全部分支之和保迹，且

$$
\operatorname{tr}\mathcal L_b(\varrho)
=\operatorname{tr}(\varrho Q_b)
=\operatorname{tr}\mathcal M_b(\varrho)
$$

对全部 $\varrho$ 成立。$000,010$ 都在偶纤维中，故 $Q_0\psi_\theta=\psi_\theta$、$Q_1\psi_\theta=0$，而两个非零基底振幅的模平方均为 $1/2$，得到所述第一阶段行概率。由 $S(\cdot\mid b)=\tfrac12\delta_{000}+\tfrac12\delta_{010}$（对两个 $b$ 都取此行）可从 $E$ 精确模拟 $F$；由确定性奇偶核可从 $F$ 精确模拟 $E$。这些核与 $\theta$ 无关，故两个单向缺陷均为零。

两种仪器的第一阶段实际后态则为

$$
\mathcal L_0(\varrho_\theta)=\varrho_\theta,\qquad
\mathcal M_0(\varrho_\theta)=\tau:=\frac{P_{000}+P_{010}}2,
\qquad
\mathcal L_1(\varrho_\theta)=\mathcal M_1(\varrho_\theta)=0.
$$

由于偶结果概率为一，零分支以外不需要再归一。正交关系 $\langle\psi_+,\psi_-\rangle=0$ 给出 $\operatorname{tr}(P_+\varrho_+)=1$、$\operatorname{tr}(P_+\varrho_-)=0$，而

$$
\operatorname{tr}(P_+\tau)
=\frac12\bigl(|\langle\psi_+,000\rangle|^2+|\langle\psi_+,010\rangle|^2\bigr)=\frac12.
$$

因此 $\mathcal L$ 的两阶段记录 $(b,r)$ 完全区分两种制备，按 $r=1$ 选 $+$、$r=0$ 选 $-$ 得零风险。$\mathcal M$ 的两阶段记录在两种制备下具有同一律 $J$；任意决策的均匀先验成功率为

$$
\frac12\sum_{b,r}J(b,r)\bigl(d(+\mid b,r)+d(-\mid b,r)\bigr)=\frac12,
$$

所以其风险恰为 $1/2$。即使保留完整基底的第一阶段标签 $w$，第二协议的联合概率也为 $\Pr(w,r\mid\theta)=1/4$，其中 $w\in\{000,010\}$、$r\in\{0,1\}$，仍与 $\theta$ 无关；该额外经典标签不能恢复已消去的相干项。

第一阶段的 $E,F$ 只含当前经典记录，未包含测量后的量子载体与相位敏感未来，故两个当前缺陷为零与两阶段风险不同并不冲突。将第二次实际测量结果纳入观察后，两阶段行律已有上述区别，应对这些完整记录律重新计算缺陷；若还允许选择后续反馈操作，则需给定相应的路径核或量子过程及可访问载体。单步律的模拟关系并不是经典结果与量子后态联合对象的模拟关系，也不把这里的理想仪器假设推成不可逆坍缩、观察者客观性或唯一结果的结论。证毕。

## 追加锚（本行以下为增补区）

## 120. 量子仪器缺陷与后续决策风险

第 119 节把“保留多少历史”写成有限经典实验的缺陷与风险界。本节把同一问题提升到完整量子仪器：被丢弃的部分可以包含活动记忆、参考系和尚未读取的历史寄存器，因此只比较一次测量的边缘分布是不够的。需要比较整个过程在任意输入和任意保留参考上的可区分性。

### 120.1 完整过程与保留过程

设参数集为有限集合 $\Theta$，先验为 $\mu$。令 $X,Y,\widetilde Y$ 为有限维算子空间；对每个 $\theta\in\Theta$，令

$$
I_\theta:X\longrightarrow Y
$$

是共同输入空间 $X$ 与共同输出空间 $Y$ 上、各参数同型的完整 $n$ 槽量子过程（固定槽接线后视为一个 CPTP 通道）。输出空间 $Y$ 包含全部仍可访问的历史寄存器与活动记忆；惰性的外部参考系统记为任意有限维 $R$，在比较时以 $I_\theta\otimes\operatorname{id}_R$ 处理。压缩后的过程为

$$
\widetilde I_\theta:X\longrightarrow \widetilde Y.
$$

压缩不是把 $Y$ 的坐标重新命名，而是实际丢弃了一部分过程输出。设 $S:\widetilde Y\to Y$ 是与 $\theta$、输入以及后续决策均无关的 CPTP 模拟器。定义过程缺陷

$$
\boxed{
\delta_\diamond(I\mid\widetilde I)
=
\inf_S\;\sup_{\theta\in\Theta}
\frac12\left\|I_\theta-S\circ\widetilde I_\theta\right\|_\diamond .
}
$$

diamond 范数的辅助系统量化了最坏情形下保留参考的影响；因此这里的缺陷不是某个选定初态上的迹距离。允许实验者选择共同输入 $\rho_{XR}$ 和读出 $D:Y\otimes R\to A$，其中 $D$ 是量子到经典的 CPTP 映射；模拟器在参考上作用为 $S\otimes\operatorname{id}_R$。若模型固定无参考输入，则取一维 $R$ 即可。

对损失函数

$$
0\le \ell(\theta,a)\le 1
$$

定义完整过程的最优 Bayes 风险

$$
R^*(I)
=
\inf_{R,\rho_{XR},D}
\sum_{\theta\in\Theta}
\mu(\theta)\,
\mathbb E_{a\sim D((I_\theta\otimes\operatorname{id}_R)(\rho_{XR}))}
[\ell(\theta,a)],
$$

并以同样方式定义 $R^*(\widetilde I)$。这里的后处理可以包含任意对输出记忆的量子控制，但模拟器 $S$ 必须在所有参数之间共用。

### 120.2 缺陷支配后续决策风险

在上述有限参数、共同输入空间、CPTP 后处理和单位区间损失的条件下，有

$$
\boxed{
R^*(\widetilde I)
\le
R^*(I)+\delta_\diamond(I\mid\widetilde I).
}
$$

证明只使用通道范数的定义和测量的收缩性。固定任意模拟器 $S$、输入 $\rho_{XR}$ 与完整过程读出 $D$，把 $D\circ(S\otimes\operatorname{id}_R)$ 作为压缩过程上的决策。若

$$
\frac12\left\|I_\theta-S\circ\widetilde I_\theta\right\|_\diamond
\le\varepsilon
$$

对所有 $\theta$ 成立，则对该输入及任意参考系统，输出态的迹距离至多为 $\varepsilon$；再经 $D$ 后，经典总变差距离仍至多为 $\varepsilon$。单位区间损失的期望差至多为同一数值，对 $\mu$ 加权后仍至多为 $\varepsilon$。先对策略取下确界，再对 $S$ 取下确界，得到所示不等式。

若反向缺陷也有定义，则同时应用两次上界，得到

$$
\boxed{
\left|R^*(I)-R^*(\widetilde I)\right|
\le
\max\left\{
\delta_\diamond(I\mid\widetilde I),
\delta_\diamond(\widetilde I\mid I)
\right\}.
}
$$

该结论的量词顺序很重要：模拟器不能依赖于未知参数，且缺陷控制的是所有输入、所有参考和所有允许后处理。只比较某一次实验的输出概率，不能推出这个统一风险界。

### 120.3 逐槽误差与历史保留

若完整过程由固定接线后的 $n$ 个槽组成，并且第 $k$ 槽存在与输入、记忆和参考兼容的抬升模拟误差 $\eta_k$，且各槽模拟器可以复合为同一输出空间上的全局模拟器 $S$（共同余域时可取相应的恒等填充），则第 72.1 节的望远镜不等式给出

$$
\boxed{
\delta_\diamond(I\mid\widetilde I)
\le
\min\left\{1,\sum_{k=1}^{n}\eta_k\right\}.
}
$$

与第 72.1 节相同，这要求逐槽抬升在同一复合空间上比较，并把中间记忆保留下来。若后续干预可以在各槽之间交错，完整对象应视为 comb 或 strategy；此时不能把 comb 无条件当作一个普通末态通道，而应改用相应的 strategy 范数，或先完成逐槽抬升再应用本节界。

这给出一个可操作的历史预算：在预测时域 $n$ 内，若允许总风险误差为 $\varepsilon$，则满足

$$
\sum_{k=1}^{n}\eta_k\le\varepsilon
$$

足以保证任何单位区间损失的后续决策风险增加不超过 $\varepsilon$。该预算只对所声明的过程族、参考系统和后处理有效，不是对所有未来实验的宇宙级保证。

### 120.4 即时统计相同仍可能有后续风险

Zeckendorf 合法构型空间可取为

$$
\mathcal W_L
=
\{w\in\{0,1\}^L:w_jw_{j+1}=0\}.
$$

令 $P_w=|w\rangle\langle w|$，并按某个粗读出 $q:\mathcal W_L\to Q$ 定义两种过程。第一种是粗 Lüders 过程

$$
L_q(\rho)
=
\sum_{r\in Q}Q_r\rho Q_r,
\qquad
Q_r=\sum_{q(w)=r}P_w;
$$

第二种是先精确记录构型再忘记标签

$$
M_q(\rho)
=
\sum_{r\in Q}\sum_{q(w)=r}P_w\rho P_w.
$$

二者在当前粗标签的经典概率上相同，但保留的后态不同。若把标签写入经典寄存器，两个仪器对结果 $r$ 的概率都为 $\operatorname{Tr}(Q_r\rho)$；差异出现在条件后态及其可供后续操作访问的相干。取三位合法构型中的 $000$ 与 $010$，并令

$$
|\psi_\pm\rangle
=
\frac{|000\rangle\pm|010\rangle}{\sqrt2}.
$$

若粗读出把这两个构型归入同一类，则在过程缺陷定义中取参数集为单元素，并令完整通道为 $L_q$、压缩通道为 $M_q$；diamond 范数的上确界对输入取值，下面的两个态只是其中的测试输入：

$$
M_q(|\psi_+\rangle\langle\psi_+|)
=
M_q(|\psi_-\rangle\langle\psi_-|)
=\tau,
$$

而 $L_q$ 保留两个相反相位的纯态。两者满足

$$
D\!\left(L_q(|\psi_+\rangle\langle\psi_+|),L_q(|\psi_-\rangle\langle\psi_-|)\right)=1,
\qquad
D\!\left(M_q(|\psi_+\rangle\langle\psi_+|),M_q(|\psi_-\rangle\langle\psi_-|)\right)=0.
$$

因此对任意不依赖参数的模拟器 $S$，若其半 diamond 误差至多为 $\varepsilon$，则特别地，对两个制备输入有 $D\!\left(L_q(|\psi_\pm\rangle\langle\psi_\pm|),S\tau\right)\le\varepsilon$，三角不等式给出

$$
1
\le
D\!\left(L_q(|\psi_+\rangle\langle\psi_+|),S\tau\right)
+
D\!\left(S\tau,L_q(|\psi_-\rangle\langle\psi_-|)\right)
\le2\varepsilon,
$$

从而

$$
\boxed{
\delta_\diamond(L_q\mid M_q)\ge\frac12.
}
$$

这说明“即时经典统计完全相同”并不意味着过程缺陷为零。被遗忘的相位在后续联合操作中仍可转回可见读数；风险界必须针对完整过程，而不是单步标签分布。这里的例子把第 96 节和第 119 节的边界现象放进同一个过程缺陷框架。

### 120.5 Zeckendorf 刻度的正确位置

Zeckendorf 编码在本节中承担的是参数与输入构型的离散组织。它决定合法窗口的索引、粗读出纤维 $q^{-1}(r)$ 以及可能被丢弃的历史分支；它不决定通道的 Hamiltonian、CPTP 结构、记录强度或 diamond 范数。

例如，三位合法构型

$$
000,\quad001,\quad010,\quad100,\quad101
$$

按权重 $3,2,1$ 读为 $0,1,2,3,4$。若只保留奇偶性，构型会被分成两个纤维；但过程缺陷仍需比较这些纤维在后态、活动记忆和参考上的可模拟程度。不能用合法构型数 $F_{L+2}$、单步 Gram 系数或一个整数标签，替代完整过程的缺陷计算。

因此，历史保留量不是一个只由编码长度决定的数字，而是相对于三项共同确定的预算：允许的过程族、可执行的后续策略和容许风险误差。改变其中任一项，最小充分记录都可能改变。

### 120.6 研究命题与形式化边界

本节提出的可检验命题是：对于给定过程族和后续策略类，存在一个过程缺陷 $\delta$，它统一上界任何单位区间损失的 Bayes 风险增量；若缺陷按逐槽误差累积，则历史预算可由望远镜界给出。该命题是有限维 CPTP 数学推导，与仓库已有的有限 Kraus 通道、迹距离收缩、过程望远镜和投影动力学结果相容。

指定版本尚无一个直接给出“diamond 缺陷蕴含后续 Bayes 风险界”的单一 Lean 定理；本节的组合证明因此保留为普通数学推导，不能冒充新增 kernel 证明。可继续的形式化任务是：先在有限维矩阵上定义带辅助系统的过程缺陷，再分别形式化风险函数、测量收缩和下确界传递；最后把 Zeckendorf 合法窗口作为参数族接入，而不是把编码本身当作物理动力学。

由此，对“用多少约束和历史才能得到稳定经典现实”的回答获得一个强度受控的版本：在给定实验与误差预算内，只需保留使 $\delta_\diamond\le\varepsilon$ 的过程信息；若更换后续操作、允许访问旧记忆或扩大参考系统，原有预算必须重新计算。稳定性是过程相对于任务的近似闭合，而不是所有未来关系都已被证明消失。

### 120.7 追加锚

本节新增的边界固定为：

$$
\boxed{
\text{即时读数的相同性只约束当前统计；}
\quad
\text{过程 diamond 缺陷才统一约束任意后续决策风险。}
}
$$

后续章节可以在这一锚上研究三类问题：不同记忆结构下的缺陷复合律、comb/strategy 范数的逐槽推广，以及 Zeckendorf 粗读出在给定实验族中的最小充分记录。若没有这些额外假设，不得把“记录看起来经典”升级为“整体过程已经经典”。
## 121. 记录接口的 Blackwell 偏序与缺陷复合

第 120 节用过程 diamond 缺陷控制任意后续量子决策风险。本节固定一个历史参数集，研究不同记录接口之间的可模拟关系：若较粗记录可以由较细记录通过与历史无关的退化得到，则较细记录对所有固定任务都不劣；若只能近似退化，则缺陷沿记录链次可加。这给“保留多少历史”提供一个偏序，而不是单一标量。

### 121.1 经典记录的 Blackwell 预序

设有限历史集为 $H$，有限记录集为 $Y,Z$。记录接口是条件概率核

$$
E(y\mid h),
\qquad
F(z\mid h),
$$

其中对每个 $h$ 有 $\sum_yE(y\mid h)=\sum_zF(z\mid h)=1$。随机退化核 $K(z\mid y)$ 作用为

$$
(K E)(z\mid h)=\sum_yK(z\mid y)E(y\mid h).
$$

定义 Blackwell 预序

$$
E\succeq_B F
\quad\Longleftrightarrow\quad
\exists K\;F=K\circ E.
$$

它是自反且传递的预序：自反性取恒等核；若 $F=K_1E$ 且 $G=K_2F$，则 $G=(K_2K_1)E$。互相可以退化的接口应视为同一个等价类；一般情况下预序不反对称，因此不能把所有记录接口排成一条全序链。

对有限动作集 $A$、先验 $\pi$ 和损失 $0\le\ell(a,h)\le L$，记录 $E$ 的最优风险为

$$
R_E
=
\inf_\delta
\sum_{h\in H}\pi(h)
\sum_{y\in Y}E(y\mid h)
\sum_{a\in A}\delta(a\mid y)\ell(a,h),
$$

其中 $\delta(a\mid y)$ 是从记录到动作的随机决策规则。若 $E\succeq_BF$，固定一个实现 $F=K E$。任意使用 $F$ 的决策规则都可在 $E$ 上先施加 $K$ 再执行，因此

$$
\boxed{R_E\le R_F.}
$$

该不等式对每个固定先验、动作集和有界损失分别成立；它不构成跨任务的单一风险全序，也不说明某条记录在未声明的动力学或自适应实验中仍然充分。

### 121.2 经典近似缺陷的复合律

定义从 $E$ 模拟 $F$ 的最坏行总变差缺陷

$$
\delta_B(F\mid E)
=
\inf_K\max_{h\in H}
\operatorname{TV}\bigl(F_h,(K E)_h\bigr),
$$

其中 $E_h$、$F_h$ 表示固定历史 $h$ 的记录分布。设有第三个接口 $G$，且记录空间允许复合相应随机核。对任意 $K_1,K_2$，由三角不等式和随机核对总变差距离的收缩性，得到

$$
\operatorname{TV}\bigl(G_h,(K_2K_1E)_h\bigr)
\le
\operatorname{TV}\bigl(G_h,(K_2F)_h\bigr)
+
\operatorname{TV}\bigl((K_2F)_h,(K_2K_1E)_h\bigr)
\le
\operatorname{TV}\bigl(G_h,(K_2F)_h\bigr)
+
\operatorname{TV}\bigl(F_h,(K_1E)_h\bigr).
$$

取历史最坏值和两个核的下确界，得到

$$
\boxed{
\delta_B(G\mid E)
\le
\delta_B(F\mid E)+\delta_B(G\mid F).
}
$$

因此沿接口链 $E_0\succeq_B E_1\succeq_B\cdots\succeq_B E_m$，若第 $i$ 步近似缺陷为 $\varepsilon_i$，则端点缺陷至多为 $\sum_i\varepsilon_i$。对单位区间损失，记录风险的相应偏差至多为同一数值；对上界为 $L$ 的损失，乘以 $L$。

### 121.3 量子记录接口

经典核的退化对应量子记录态族之间的 CPTP 模拟。设每个历史 $h$ 在接口 $E$、$F$ 下分别产生密度算子 $\rho_h^E$、$\rho_h^F$。定义

$$
E\succeq_QF
\quad\Longleftrightarrow\quad
\exists\Lambda\ \text{CPTP},
\quad
\rho_h^F=\Lambda(\rho_h^E)\quad(\forall h).
$$

量子接口的状态族模拟缺陷为

$$
\delta_Q(F\mid E)
=
\inf_{\Lambda\ \mathrm{CPTP}}
\max_{h\in H}
\frac12\left\|\rho_h^F-\Lambda(\rho_h^E)\right\|_1.
$$

CPTP 映射保持迹距离收缩，因此 $E\succeq_QF$ 时，对任意 POVM 决策和有界损失都有 $R_E\le R_F$；近似情形下，被模拟方向满足 $R_E\le R_F+L\,\delta_Q(F\mid E)$。近似缺陷还满足复合律

$$
\boxed{
\delta_Q(G\mid E)
\le
\delta_Q(F\mid E)+\delta_Q(G\mid F).
}
$$

证明与经典情形相同：对近似模拟器 $\Lambda_1:E\to F$、$\Lambda_2:F\to G$ 复合，并使用

$$
\frac12\left\|\Lambda_2(\sigma)-\Lambda_2(\tau)\right\|_1
\le
\frac12\left\|\sigma-\tau\right\|_1.
$$

这里的量子预序只比较一组状态族和一次 CPTP 读出。若后续实验可以访问多槽活动记忆、插入自适应控制或保留参考，应回到第 120 节的过程缺陷；单次状态族的 $\delta_Q$ 不自动支配 comb 或 strategy 的风险。

### 121.4 历史保留的操作判据

令 $E_k$ 表示保留深度为 $k$ 的记录接口，且忘却核满足

$$
E_{k+1}\succeq_BE_k
$$

或其量子对应 $E_{k+1}\succeq_QE_k$。给定目标未来接口 $T$、损失上界 $L$ 和容许风险误差 $\varepsilon$，若存在满足条件的 $k$，则可以选择最小的 $k$ 使

$$
L\,\delta(T\mid E_k)\le\varepsilon,
$$

其中 $\delta$ 取与任务匹配的 $\delta_B$、$\delta_Q$ 或第 120 节的过程 diamond 缺陷。这个 $k$ 是相对于历史参数集、后续决策类和误差预算的最小充分记录深度；改变任一项都可能改变它。

该判据不声称存在跨所有任务的唯一“客观历史长度”。Blackwell 预序提供的是可比较性：一条记录若能无损模拟另一条，就对所有固定任务支配；两条记录若互不可退化，则需要指定先验、损失或后续实验才能比较。

### 121.5 与 Zeckendorf 构型的连接

在合法语言

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\}
$$

上，可把 $h=w$ 作为历史参数，把 Zeckendorf 数值、奇偶性或局部模式作为不同记录接口。当 $E_k$ 是 $E_{k+1}$ 的历史无关粗粒化（由函数或随机核给出）时，存在忘却核，因而 $E_{k+1}\succeq_BE_k$。但若记录接口还包含相位、活动记忆或参考，粗粒度函数未必能由经典核模拟；必须把这些量纳入量子状态族并计算 $\delta_Q$，或回到第 120 节的过程缺陷。

这解释了为什么同一组合法构型可以有不同的“现实稳定度”：稳定度不是由 Fibonacci 维数 $F_{L+2}$ 单独决定，而是由所选记录接口在 Blackwell 预序中的位置及其对目标未来的缺陷共同决定。

### 121.6 形式化边界与追加锚

本节的经典预序、总变差复合律、量子 CPTP 预序和状态族迹距离复合律是有限集合与有限维量子态上的普通数学推导。指定版本的 Lean 库已有随机核、有限 Kraus 通道和迹距离收缩等支点；其中 `FiniteDeficiencyTriangle.lean` 与 `FiniteDeficiencyRiskTransfer.lean` 分别提供有限缺陷三角和有界损失风险传递。Blackwell 命名、接口预序与量子状态族的统一组合尚无一个单一冻结定理；本节不冒充新增 kernel 证明。多槽自适应过程仍应使用第 120 节的过程级范数。

新增锚为

$$
\boxed{
\text{记录的充分性形成 Blackwell 预序；缺陷沿可复合的退化链次可加；在模拟方向上，风险增加至多为损失上界乘以缺陷。}
}
$$

因此，“需要保留多少历史”可以先问三个可计算问题：哪些记录可以无损退化，近似退化的缺陷如何沿链累加，以及给定未来任务的风险预算允许多大的端点缺陷。只有在这三个量都被指定后，稳定经典现实才有可检验的记录深度。

## 122. 双向缺陷、操作等价与历史深度

第 121 节给出了有向的 Blackwell 缺陷：较细接口能否模拟较粗接口，以及模拟误差如何沿链累加。本节补上两个边界。第一，若要称两个接口“同一现实接口”，需要同时控制两个方向；第二，嵌套历史接口只有在忘却核与任务缺陷相容时，才会产生可证明的最小保留深度。

### 122.1 双向缺陷不是标签相等

对经典接口定义

$$
\Delta_B(E,F)
=
\max\left\{\delta_B(F\mid E),\delta_B(E\mid F)\right\},
$$

对量子状态族定义

$$
\Delta_Q(E,F)
=
\max\left\{\delta_Q(F\mid E),\delta_Q(E\mid F)\right\}.
$$

第 121 节的有向次可加律立即给出三角不等式

$$
\Delta_B(E,G)
\le
\Delta_B(E,F)+\Delta_B(F,G),
$$

以及量子对应式

$$
\Delta_Q(E,G)
\le
\Delta_Q(E,F)+\Delta_Q(F,G).
$$

两者都满足自反性，但一般不满足严格的同一性判别：若两个接口可以在所有历史上互相近似退化，可能仍然不是字节相等、标签相等或通道同构。它们只是在指定历史实验族下操作等价。因此 $\Delta_B$ 与 $\Delta_Q$ 更准确地说是伪度量；在互相零缺陷的接口等价类上，才得到真正的度量结构。 在有限接口且模拟器集合紧的条件下，定义 $E\sim F\iff\Delta(E,F)=0$ 得到等价关系，商空间上的诱导距离才是度量；若只给定部分任务族，只能称为任务相对等价。

若 $\Delta(E,F)\le\varepsilon$ 且 $\Delta(F,G)\le\varepsilon$，只能推出 $\Delta(E,G)\le2\varepsilon$。所以“误差不超过 $\varepsilon$ 的等价”本身不是传递等价关系；跨多层接口时必须把预算累加，或提高允许阈值。

### 122.2 双向缺陷与任务风险

若损失上界为 $L$，第 121 节的单向结论分别给出

$$
R_E\le R_F+L\,\delta(F\mid E),
\qquad
R_F\le R_E+L\,\delta(E\mid F).
$$

因此

$$
\boxed{
\left|R_E-R_F\right|
\le
L\,\Delta(E,F).
}
$$

这里的风险必须针对同一个先验、动作集和损失函数；改变任务后，$\Delta$ 仍可作为接口距离，但这条风险界需要重新代入新的 $L$ 与决策类。量子状态族的 POVM 决策同样满足该双向界，迹距离收缩是唯一使用的量子性质。

### 122.3 嵌套历史接口的单调性

设 $E_k$ 是保留前 $k$ 层历史的接口。若存在与历史无关的忘却核 $W_k$，满足

$$
E_k=W_k\circ E_{k+1},
$$

则有精确 Blackwell 关系

$$
E_{k+1}\succeq_BE_k.
$$

对任意目标接口 $T$，把从 $E_k$ 到 $T$ 的近似模拟器与 $W_k$ 复合，得到

$$
\boxed{
\delta_B(T\mid E_{k+1})
\le
\delta_B(T\mid E_k).
}
$$

量子状态族在存在 CPTP 忘却映射时满足完全相同的单调性：若 $\rho_h^{E_k}=\Lambda_k(\rho_h^{E_{k+1}})$，则

$$
\delta_Q(T\mid E_{k+1})
\le
\delta_Q(T\mid E_k).
$$

单调性只说明增加可模拟的历史不会变差；它不保证缺陷严格下降，也不保证任意“看起来更长”的记录都存在这样的忘却核。嵌套性必须由接口的实际构造给出。

### 122.4 有限历史深度与开放边界

给定目标未来接口 $T$、容许接口缺陷 $\varepsilon$ 和损失上界 $L$，定义

$$
k_\varepsilon(T)
=
\min\left\{k:\ L\,\delta(T\mid E_k)\le\varepsilon\right\},
$$

但只有集合非空时该最小值才存在。若对所有可用 $k$ 都不满足条件，应保留“无有限深度”的开放状态，不能以增加计算预算代替缺失的历史信息。

当 $E_k$ 嵌套且存在忘却核时，上一节单调性保证可行深度集合是向上的：一旦某个 $k$ 满足预算，所有更深层接口也满足。于是 $k_\varepsilon(T)$ 的含义是明确的最小充分记录深度，而不是任意截断点。 若令 $e_k=\delta(T\mid E_k)$、$e_\infty=\inf_k e_k$，则严格满足 $\varepsilon>L e_\infty$ 时可由单调收敛得到某个有限可行 $k$；$\varepsilon<L e_\infty$ 时不存在可行深度；等号情形只有在某个有限 $k$ 达到极限时才可行，否则仍是开放边界。

第 120 节的过程 diamond 缺陷可直接替换这里的 $\delta$，但需要把 $E_k$ 视为完整过程接口并保留参考与活动记忆。若只用单次状态族的 $\delta_Q$，则所得深度只对一阶段 POVM 任务有效。

### 122.5 Zeckendorf 合法空间中的实例化

在

$$
\mathcal W_L
=\{w\in\{0,1\}^L:w_jw_{j+1}=0\}
$$

中，令 $E_k$ 保留 Zeckendorf 合法字串的前 $k$ 个坐标，令 $W_k$ 忘却其余坐标。只要粗读出确实是这些坐标的函数，$E_k=W_k\circ E_{k+1}$ 成立，因而形成 Blackwell 链。

若目标任务读取完整数值、相位或跨坐标历史，坐标前缀未必足够；此时应把目标接口 $T$ 的后态与记忆纳入缺陷计算。合法构型总数 $F_{L+2}$ 只给出状态空间规模，不决定 $k_\varepsilon(T)$。

因此，同一个 Zeckendorf 刻度可以在一个任务上很快达到小缺陷，在另一个任务上始终有非零缺陷。差异来自目标实验族和可访问关联，而不是编码是否唯一。

### 122.6 形式化边界与追加锚

本节的双向伪度量、风险绝对差界和嵌套接口单调性，均由第 121 节的有向缺陷复合与 CPTP/随机核收缩推出。指定版本的 Lean 支点仍是有限缺陷三角、风险传递和通道收缩；本节未新增 Lean 声明，也没有把这些普通数学组合冒充 kernel 已证结果。

新增锚为

$$
\boxed{
\text{“同一现实接口”只能表示指定实验族下的双向小缺陷；历史深度只有在忘却核、任务和误差预算同时给定时才可计算。}
}
$$

这使“保留多少历史”获得两个可审计的失败模式：没有双向模拟时，接口不能称为操作等价；没有满足预算的有限 $k$ 时，结论必须保持开放，而不是把更长的 Zeckendorf 标签自动当作充分历史。
## 123. 逆极限中的幽灵历史与载体完备化

第 122 节把记录深度写成相对于目标任务的缺陷预算。本节补上一个不同的边界：即使每个有限层都可实现，且层与层之间完全相容，也不保证这些有限记录来自原先的对象载体。逆极限会把所有有限层一致的塔组织起来；原载体能否覆盖这些塔，是一个独立的满射与完备化问题。

### 123.1 有限接口塔与自然嵌入

设有有限层接口 $q_n:X\to Q_n$，以及忘却映射 $\pi_n:Q_{n+1}\to Q_n$，满足

$$
\pi_n\circ q_{n+1}=q_n.
$$

定义兼容塔

$$
\varprojlim Q_n
=
\left\{(z_n)_n:\ \pi_n(z_{n+1})=z_n\ \text{对所有 }n\right\}.
$$

每个 $x\in X$ 给出一个塔

$$
\iota(x)=(q_n(x))_n.
$$

令

$$
R_\infty=\bigcap_n\ker(q_n),
\qquad
x\mathrel{R_\infty}y
\Longleftrightarrow
q_n(x)=q_n(y)\ \text{对所有 }n.
$$

则 $\iota$ 唯一因子化为

$$
\bar\iota:X/R_\infty\longrightarrow\varprojlim Q_n,
$$

并且 $\bar\iota$ 是单射。这里的单射只使用所有层读数同时相等才定义的商关系；它不要求原载体已经完备。

### 123.2 满射缺陷不是逐层一致性能够消除的

嵌入 $\bar\iota$ 满射，当且仅当每一个兼容塔 $(z_n)_n$ 都存在单个 $x\in X$，使

$$
q_n(x)=z_n
\qquad\text{对所有 }n.
$$

因此，“每个有限层都有实现”只说明塔属于逆极限，不说明塔属于原像。定义载体的完备化缺陷为

$$
\operatorname{Ghost}(X;Q_\bullet)
=
\left(\varprojlim Q_n\right)\setminus\operatorname{im}(\bar\iota).
$$

这个集合为空，才可以说当前载体对这组有限接口是完备的；非空时，逆极限引入了原类型中没有的理想记录。这里的“幽灵”是表示边界的数学名称，不是额外物理实体。

### 123.3 Zeckendorf 前缀的具体幽灵

令 $X_{\mathrm{fs}}$ 为所有只有有限多个 $1$ 的无限合法串：

$$
X_{\mathrm{fs}}
=
\left\{x\in\{0,1\}^{\mathbb N}:x_ix_{i+1}=0,\ \exists N\ \forall i\ge N,\ x_i=0\right\}.
$$

令 $Q_n=\mathcal W_n$ 为长度 $n$ 的无相邻 $1$ 字串，$\pi_n$ 删除最后一位，$q_n$ 取前缀。兼容性给出

$$
\varprojlim Q_n
\cong
\left\{z\in\{0,1\}^{\mathbb N}:z_i z_{i+1}=0\right\},
$$

即所有无限合法串，而不仅是有限支持串。

交替串

$$
z=1010101010\cdots
$$

的每个有限前缀都属于某个 $Q_n$，并且每个前缀都可由一个有限 Zeckendorf 整数实现；但不存在 $x\in X_{\mathrm{fs}}$ 同时实现全部前缀，因为 $x$ 最终必须全为 $0$。所以 $z$ 是逆极限中的元素，却不在 $\bar\iota$ 的像中。

若把对象类型扩张为所有无限合法串

$$
\widehat X
=
\left\{x\in\{0,1\}^{\mathbb N}:x_ix_{i+1}=0\right\},
$$

则前缀映射对该逆系统满射。扩张载体解决了满射缺陷，但也改变了对象类型：它加入了有限整数模型没有的无限历史。不能把这一步描述成在原对象中发现了一个普通整数。

### 123.4 动力学必须保持原像

若每层有操作 $T_n:Q_n\to Q_n$，并满足

$$
\pi_n\circ T_{n+1}=T_n\circ\pi_n,
$$

则得到逆极限上的操作

$$
\widehat T((z_n)_n)=(T_n z_n)_n.
$$

若原载体上存在 $T:X\to X$，且

$$
q_n\circ T=T_n\circ q_n,
$$

则

$$
\widehat T\circ\iota=\iota\circ T.
$$

但层间相容本身不保证 $\widehat T$ 保持有限支持像。对 Hilbert 型有界线程，还需要统一的算子界

$$
\sup_n\|T_n\|\le M<\infty
$$

来保证逐层作用仍给出有界线程；没有这个界，层操作可能把可实现的线程推出载体。要让完备化后的动力学仍然代表原模型，必须另行证明

$$
\widehat T\bigl(\operatorname{im}(\bar\iota)\bigr)
\subseteq
\operatorname{im}(\bar\iota),
$$

或给出离开该像集的泄漏指标。否则，一个只在无限完备化中存在的幽灵历史，可能被层操作激活并进入后续读数；这不是原有限对象动力学的结论。

### 123.5 与历史深度和量子接口的边界

本节的逆极限问题与第 122 节的缺陷预算正交。缺陷衡量某个接口对目标实验的预测损失；逆极限满射衡量所有兼容有限记录是否能由同一原对象实现。一个载体可以在任务意义下具有很小缺陷，却仍有非空的完备化缺陷；反过来，载体完备也不保证记录足以闭合未来动力学。

指定版本已经有两个直接相关的 Lean 支点。`D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.lean` 中的 `bounded_inverse_limit_reconstruction` 证明：单调子空间序列的有界、正交投影相容族，与累积闭子空间之间存在规范的线性等距双射；因此在 Hilbert 载体中，“逆极限线程”还必须带有统一有界性。`D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.lean` 中的 `compatible_unbounded_coordinates` 给出反例：`partialOnes n` 满足每个有限层的投影相容性，但

$$
\|\mathrm{partialOnes}(n)\|^2=n,
$$

故范数无界；它既不是某个 $\ell^2$ 向量的投影族，也不属于有界逆极限。这个例子把“逐层一致”与“存在一个实际状态”之间缺失的有界性条件具体化了。

对量子接口，$Q_n$ 应替换为带态、相位和活动记忆的有限接口，忘却映射应替换为保持合法性的量子通道。逐层状态族的一致性仍不自动给出完整过程的可实现性；若后续实验能访问参考或旧记录，必须回到第 120 节的过程 diamond 缺陷。Gram 矩阵的正定性、通道的完全正性和像集不变性，都是额外的整体相容条件。

本节的因子化、Zeckendorf 前缀反例和动力学像集条件是逆系统与有限字串上的普通数学推导；Hilbert 载体中的有界重建与无界线程反例则由上述两个已有 Lean 声明直接支撑。本节没有新增 Lean 声明，也不声称重建了物理时空的完备性。指定版本的项目已有上下文等价、有限接口和记录通道支点，但没有一个冻结定理把这些支点自动组合成 Zeckendorf 逆极限的满射定理。

新增锚为

$$
\boxed{
\text{逆极限组织所有有限层一致记录；原载体的可实现性还要求满射、完备性或有界性，动力学则必须额外保持该像集。}
}
$$

因此，“无限递归”应当分成两个可检验问题：有限层是否相容，以及相容塔是否仍由当前对象类型承载。前者失败时要拒绝该关系网络；后者失败时要明确报告完备化新增的理想历史，并重新指定允许的动力学与测量范围。
## 追加锚（本行以下为增补区）

## 124. 有限前缀量子模拟与连续延拓

本节固定一个经典数字载体和一个有限维量子输出空间，把第 122 节的前缀缺陷与第 123 节的完备化联系起来。目标是刻画何时有限前缀能一致逼近一个态制备任务；载体加入无限合法串，并不自动使任意任务连续。以下定义与证明均在通常数学中进行。

**定义 124.1（合法串、有限核心与实际前缀像）。** 所有下标从 $0$ 开始，令
$$
\widehat X=\{x\in\{0,1\}^{\mathbb N}:\ \forall j\ge0,\ x_jx_{j+1}=0\},\qquad
X_{\rm fs}=\{x\in\widehat X:\ \exists N\ \forall j\ge N,\ x_j=0\}.
$$
对 $k\in\mathbb N$，以同一符号 $q_k$ 表示两个域上的前缀限制，置
$$
q_kx=(x_0,\ldots,x_{k-1}),\qquad
W_k=q_k[X_{\rm fs}]=q_k[\widehat X],\qquad
F_{k,w}=\{x\in X_{\rm fs}:q_kx=w\}.
$$
$W_k$ 恰是全部长度 $k$ 的无相邻 $1$ 字串；任一这种字串补零即给两个域中的原像。因此每个 $F_{k,w}$ 非空，$W_k$ 有限非空，$W_0=\{\varnothing\}$。记 $\tau_kz$ 为 $z$ 保留前 $k$ 位后补零的串。
取前缀距离
$$
p(x,y)=
\begin{cases}
0,&x=y,\\
2^{-m},&x\ne y,\ m=\min\{j:x_j\ne y_j\}.
\end{cases}
$$
这是 Z 卷定理 477.3 的 $d_{1/2}$。Z 卷定义 371.1 的距离另为 $d_K(x,y)=\sum_{j\ge0}2^{-j-1}|x_j-y_j|$，二者满足 $p/2\le d_K\le p$，并非同一数值公式。上述数字核心也不是 CSA 定义 1–3 的带事件、偏序、区域与选择的档案载体；CSA §§14–16 中的读数与语言仍保留各自的类型。

**命题 124.2（紧完备载体与逐柱稠密性）。** $p$ 是给出二元离散乘积之子空间拓扑的超度量，$\widehat X$ 紧且完备，$X_{\rm fs}$ 在其中稠密。更精确地，对每个 $k,w$，$F_{k,w}$ 在柱集 $\widehat F_{k,w}=\{z\in\widehat X:q_kz=w\}$ 中稠密，且
$$
q_kx=q_ky\ \Longleftrightarrow\ p(x,y)\le2^{-k},\qquad
p(\tau_kz,z)\le2^{-k}.
$$
证明。两对串共享的前缀长度取较小者，仍是第三对共享的前缀长度，故
$p(x,z)\le\max\{p(x,y),p(y,z)\}$；分离性和对称性由定义得到。
前缀柱集是有限个离散坐标条件的交；任意有限坐标条件又包含一个足够长的前缀条件。距离球与前缀柱集因而给出同一拓扑，所列等价含 $k=0$。

违反合法性的串在某对相邻坐标上取值 $11$，这是一项开柱条件；所以 $\widehat X$ 在二元乘积中闭。为具体证明紧性，对任意序列依次选第 $0,1,2,\ldots$ 位恒定的无限子序列，再取对角子序列。各坐标最终恒定所得的极限仍无相邻 $1$，前缀距离保证收敛。度量空间的序列紧性给紧性。
若序列是 Cauchy，对每个 $j$，距离最终小于 $2^{-j}$，故第 $j$ 位最终恒定；同一构造给合法极限并证明原序列收敛，故完备。

补零不制造相邻 $1$，故 $\tau_mz\in X_{\rm fs}$ 且趋于 $z$。若 $z\in\widehat F_{k,w}$，则所有 $m\ge k$ 的截断都在 $F_{k,w}$，得到逐柱稠密性。若首差在 $j$，加权距离的首项为 $2^{-j-1}$、尾和至多 $2^{-j}$，也直接验证定义 124.1 的距离比较。这给 Z371.1–2、Z477.3 的载体在所选前缀距离下的具体实现。

**定义 124.3（固定有限维的静态态制备任务）。** 固定整数 $d\ge1$，输出态空间与距离为
$$
\mathcal D_d=\{\rho\in M_d(\mathbb C):\rho=\rho^*,\ \rho\succeq0,\ \operatorname{tr}\rho=1\},\qquad
D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1.
$$
这里 $\|A\|_1=\operatorname{tr}\sqrt{A^*A}$，允许任意混态，不限于纯态。
任务是任意总函数 $T:X_{\rm fs}\to\mathcal D_d$，起初不假定连续。

深度 $k$ 的输入寄存器为 $\mathcal H_k=\mathbb C^{W_k}$，取以 $w\in W_k$ 标记的正交标准基，并置
$$
E_{k,x}=|q_kx\rangle\langle q_kx|.
$$
模拟器遍历所有 CPTP 映射 $\Lambda:M_{|W_k|}(\mathbb C)\to M_d(\mathbb C)$；它须对所有 $x$ 共用，只能从给定寄存器获得前缀。这里 $x$ 是经典制备标签，未给不相容量子可观测量预先指定共同测量结果。

**命题 124.4（CPTP 模拟器与混态表的精确等价）。** 上述输入族上的全部可实现输出恰为任意混态表 $(\sigma_w)_{w\in W_k}\in\mathcal D_d^{W_k}$。每张表都可由
$$
\Lambda_\sigma(A)=\sum_{w\in W_k}\langle w|A|w\rangle\sigma_w
$$
实现，因此只对 $E_{k,x}$ 计算的最坏误差，在所有 CPTP 映射与所有混态表上取下确界相同。
证明。任一 CPTP 映射给出密度态 $\sigma_w=\Lambda(|w\rangle\langle w|)$，于是输入 $x$ 的输出只依赖 $q_kx$。
反向对每个 $w$ 作谱分解 $\sigma_w=\sum_{a=1}^d\lambda_{wa}|v_{wa}\rangle\langle v_{wa}|$，其中 $\lambda_{wa}\ge0$、$\sum_a\lambda_{wa}=1$。取 Kraus 算子
$$
K_{wa}=\sqrt{\lambda_{wa}}\,|v_{wa}\rangle\langle w|.
$$
则 $\sum_{w,a}K_{wa}^*K_{wa}=I_{\mathcal H_k}$，且 $\sum_{w,a}K_{wa}AK_{wa}^*=\Lambda_\sigma(A)$。Kraus 形式给完全正性，前一等式给保迹性，代入基态即得指定表。这个等价只规定输入族上的行为，不规定一般相干叠加输入上的通道行为。

**定义 124.5（前缀缺陷、纤维振幅与半径）。** 对定义 124.3 的固定任务，令
$$
e_k(T)=\inf_{\Lambda\ {\rm CPTP}}\ \sup_{x\in X_{\rm fs}}
D\bigl(T(x),\Lambda(E_{k,x})\bigr)
=\inf_{\sigma\in\mathcal D_d^{W_k}}\ \sup_{x\in X_{\rm fs}}D\bigl(T(x),\sigma_{q_kx}\bigr),
$$
$$
\omega_{k,w}(T)=\sup_{x,y\in F_{k,w}}D(T(x),T(y)),\qquad
\omega_k(T)=\max_{w\in W_k}\omega_{k,w}(T),
$$
$$
f_{k,w}(\sigma)=\sup_{x\in F_{k,w}}D(T(x),\sigma),\qquad
r_{k,w}(T)=\inf_{\sigma\in\mathcal D_d}f_{k,w}(\sigma).
$$
所有上确界都在非空集上且取值于 $[0,1]$。纤维可以无限且不紧，$T$ 也可以不连续，所以这里没有把无限纤维上的上确界写成最大值。只有有限集合 $W_k$ 上使用最大值。

**定理 124.6（精确纤维半径公式与最优表存在）。** $\mathcal D_d$ 在 $D$ 下紧且完备，任意两态间的距离属于 $[0,1]$。对任意 $T:X_{\rm fs}\to\mathcal D_d$ 及任意 $k$，每个纤维都有最优中心，且
$$
e_k(T)=\max_{w\in W_k}\ \min_{\sigma\in\mathcal D_d}
\sup_{x\in F_{k,w}}D(T(x),\sigma)
=\max_{w\in W_k}r_{k,w}(T).
$$
存在一张表达到 $e_k(T)$，并由命题 124.4 实现为 CPTP 模拟器。
证明。Hermitian 矩阵组成有限维实向量空间，迹范数在该空间上给完备的度量。
若一列密度矩阵趋于 $\rho$，则对每个 $v\in\mathbb C^d$，
$$
v^*\rho v=\lim_n v^*\rho_n v\ge0,\qquad
\rho^*=\rho,\qquad \operatorname{tr}\rho=\lim_n\operatorname{tr}\rho_n=1.
$$
所以态空间闭。半正定矩阵的特征值非负，迹等于特征值之和，因此
$$
\|\rho\|_1=\operatorname{tr}\rho=1,\qquad
\tfrac12\|\rho-\sigma\|_1\le\tfrac12(\|\rho\|_1+\|\sigma\|_1)=1.
$$
闭有界性在有限维给紧性，闭子集又继承完备性；迹范数的一半仍是度量。

对任何 $\sigma,\eta\in\mathcal D_d$，逐点三角不等式及取上确界给
$$
f_{k,w}(\sigma)\le f_{k,w}(\eta)+D(\sigma,\eta),\qquad
|f_{k,w}(\sigma)-f_{k,w}(\eta)|\le D(\sigma,\eta).
$$
故纤维目标函数对中心是 $1$-Lipschitz，尽管它对 $x$ 不要求连续。紧集 $\mathcal D_d$ 上的连续实函数达到最小值，取一个中心 $\sigma_w^*$。
任意表的全局目标恰为 $\max_w f_{k,w}(\sigma_w)$，因为非空纤维有限个且分割 $X_{\rm fs}$。每一项至少为 $r_{k,w}$，故任何表的目标至少为 $\max_w r_{k,w}$；对有限个 $w$ 分别选取上述中心，便同时达到这个下界。
证明不要求中心来自 $T[F_{k,w}]$，也不给中心唯一性或不同深度最优表之间的相容性。

**命题 124.7（直径界、单调性与有限层精确性）。** 对所有 $k\ge0$，
$$
\tfrac12\omega_k(T)\le e_k(T)\le\omega_k(T),\qquad
e_{k+1}(T)\le e_k(T),\qquad
\omega_{k+1}(T)\le\omega_k(T).
$$
而且
$$
e_k(T)=0\quad\Longleftrightarrow\quad
\exists t_k:W_k\to\mathcal D_d\ \forall x\in X_{\rm fs},\ T(x)=t_k(q_kx).
$$
证明。对同纤维的 $x,y$ 和任一中心 $\sigma$，有
$D(T(x),T(y))\le D(T(x),\sigma)+D(T(y),\sigma)\le2f_{k,w}(\sigma)$。
先对 $x,y$ 取上确界，再对中心取下确界，得 $\omega_{k,w}\le2r_{k,w}$。
从非空纤维选一个 $x_w$，用 $T(x_w)$ 作中心，得 $r_{k,w}\le\omega_{k,w}$；定理 124.6 给全局两界。

将深度 $k$ 的最优中心复制给每个具有相同父前缀的长度 $k+1$ 字串，新表逐点输出与旧表相同。因此新最优误差不增；新纤维包含于父纤维，也使 $\omega_k$ 不增。这个复制表不必是新层最优表。
若 $e_k=0$，则 $\omega_k=0$，每个非空纤维上的 $T$ 恒定，按此值定义 $t_k$；反向因子化表逐点误差为零。所有结论也覆盖 $d=1$，此时态空间只有一个元素，全部缺陷恒为零。

**定理 124.8（误差趋零与唯一连续延拓的等价）。** 对固定有限 $d\ge1$ 和任意 $T:X_{\rm fs}\to\mathcal D_d$，以下四项等价：

1. $\lim_{k\to\infty}e_k(T)=0$。
2. $\lim_{k\to\infty}\omega_k(T)=0$。
3. $T:(X_{\rm fs},p)\to(\mathcal D_d,D)$ 一致连续，即
$$
\forall\varepsilon>0\ \exists\delta>0\ \forall x,y\in X_{\rm fs},\quad
p(x,y)<\delta\ \Longrightarrow\ D(T(x),T(y))<\varepsilon.
$$
4. 存在唯一连续函数 $\widehat T:(\widehat X,p)\to(\mathcal D_d,D)$，使 $\widehat T|_{X_{\rm fs}}=T$。

该延拓实际上是一致连续的。这里第三项的定义域是有限支持核心，第四项的定义域是全部无限合法串；不能把第三项降为核心上的逐点连续，也不能把第一项换成逐输入的误差极限。

证明。命题 124.7 的两侧界直接给第一、二项等价。
若第二项成立，给定 $\varepsilon>0$ 选 $K$ 使 $\omega_K<\varepsilon$。当 $p(x,y)<2^{-K}$ 时两点共享前 $K$ 位，故 $D(T(x),T(y))\le\omega_K<\varepsilon$，得到第三项。
若第三项成立，先对 $\varepsilon/2$ 选一致连续性的 $\delta$，再选 $K$ 使 $2^{-K}<\delta$。对每个 $k\ge K$ 的同纤维两点，距离不超过 $2^{-k}<\delta$，故目标距离小于 $\varepsilon/2$。取上确界后 $\omega_k\le\varepsilon/2<\varepsilon$，得到第二项。

现由第二项构造第四项。固定 $z\in\widehat X$，对 $m,n\ge K$，截断 $\tau_mz,\tau_nz$ 共享前 $K$ 位，故
$$
D\bigl(T(\tau_mz),T(\tau_nz)\bigr)\le\omega_K(T).
$$
因此这是一列 Cauchy 态；由 $\mathcal D_d$ 的完备性定义
$$
\widehat T(z)=\lim_{n\to\infty}T(\tau_nz)\in\mathcal D_d.
$$
它不依赖截断以外的近似选择：若 $x_n\in X_{\rm fs}$ 且 $p(x_n,z)\to0$，则对固定 $K$，充分大的 $n$ 有 $q_Kx_n=q_Kz$。同样对 $m\ge K$ 有 $q_K\tau_mz=q_Kz$，于是 $D(T(x_n),T(\tau_mz))\le\omega_K$。令 $m\to\infty$ 后仍有 $D(T(x_n),\widehat T(z))\le\omega_K$；再让 $K$ 增大，得到 $T(x_n)\to\widehat T(z)$。有限支持的 $z$ 最终等于自身截断，故延拓确实等于 $T$。

若 $q_Kz=q_Kz'$，则 $n\ge K$ 时的两截断也共享该前缀，令 $n\to\infty$ 得
$$
D(\widehat T(z),\widehat T(z'))\le\omega_K(T).
$$
选 $\omega_K<\varepsilon$ 并取输入距离阈值 $2^{-K}$，这证明延拓一致连续，特别连续。
任一连续延拓 $U$ 都满足 $U(z)=\lim_n U(\tau_nz)=\lim_n T(\tau_nz)=\widehat T(z)$，所以唯一。

最后若第四项成立，命题 124.2 给紧域，Heine–Cantor 定理使连续的 $\widehat T$ 一致连续。
这里也可直接证明所需的紧性步骤：若不一致连续，存在 $\varepsilon_0>0$ 和两列 $z_n,z_n'\in\widehat X$，满足
$$
p(z_n,z_n')<1/(n+1),\qquad
D(\widehat T(z_n),\widehat T(z_n'))\ge\varepsilon_0.
$$
由紧性取 $z_n$ 的收敛子序列，沿同一下标的 $z_n'$ 也趋于同一点。连续性和目标距离三角不等式迫使输出距离趋零，矛盾。
故限制到 $X_{\rm fs}$ 也一致连续，得到第三项。完备性在构造目标极限时使用，紧性在这个反向推导时使用；它们承担不同义务。

**命题 124.9（连续延拓保持每个有限缺陷）。** 若存在连续延拓 $\widehat T:\widehat X\to\mathcal D_d$，把定义 124.5 中的定义域换成 $\widehat X$，而保持 $W_k$ 与模拟器类不变，则对每个 $k$ 有
$$
e_k(\widehat T)=e_k(T),\qquad \omega_k(\widehat T)=\omega_k(T).
$$
更强地，对每个 $w\in W_k$ 与每个中心 $\sigma\in\mathcal D_d$，
$$
\sup_{z\in\widehat F_{k,w}}D(\widehat T(z),\sigma)
=\sup_{x\in F_{k,w}}D(T(x),\sigma).
$$
证明。核心包含于完备载体给右边不大于左边。任一 $z\in\widehat F_{k,w}$ 的截断 $\tau_nz$ 在 $n\ge k$ 时属于 $F_{k,w}$；连续性使其到中心的距离趋于 $D(\widehat T(z),\sigma)$，每项又不超过右侧上确界，故反向不等式成立。
逐对截断同样证明每个柱上的直径上确界不变；对中心取下确界、对有限个柱取最大值便给两个结论。无限串可以使某个上确界真正达到，但不会在连续延拓下增大任何有限层最坏误差。

**命题 124.10（连续而永无精确有限深度的量子比特任务）。** 本命题取 $d=2$，复用 Z477.3 的函数
$$
S(z)=\sum_{j\ge0}4^{-j-1}z_j,\qquad
T_S(x)=\operatorname{diag}(1-S(x),S(x)),\qquad
c_k=\tfrac4{15}4^{-k}.
$$
则 $0\le S(z)\le4/15$，$T_S$ 连续延拓到 $\widehat X$，且对每个 $k\ge0$，
$$
\omega_k(T_S)=c_k,\qquad e_k(T_S)=\tfrac12c_k=\tfrac2{15}4^{-k}>0.
$$
证明。若从位置 $k$ 开始的尾部首位不受前一位限制，每对位置 $k+2r,k+2r+1$ 至多一个 $1$，所以该对的加权贡献至多为 $4^{-(k+2r)-1}$。求几何级数得
$$
\sum_{j\ge k}4^{-j-1}z_j
\le\sum_{r\ge0}4^{-(k+2r)-1}
=\frac{4^{-k-1}}{1-4^{-2}}=c_k.
$$
交替尾 $1010\cdots$ 达到此值；其任意长的有限截断都合法，尾和趋于 $c_k$。取 $k=0$ 得全局范围，因此所写矩阵确为密度态。

固定前缀 $w$，置 $s_w=\sum_{j<k}4^{-j-1}w_j$。当 $k=0$ 或 $w_{k-1}=0$ 时，尾部范围的下确界为 $0$、上确界为 $b_w=c_k$。当 $k\ge1$ 且 $w_{k-1}=1$ 时，第 $k$ 位被迫为零，位置 $k+1$ 起可自由接交替尾，故 $b_w=c_{k+1}$。下端用全零尾达到；上端由对应交替尾的有限截断逼近。
有限支持串无法达到正的上端：达到成对求和界需要无限多对各自达到最大贡献。完备载体上的交替尾则达到上端。

两对角态的迹距离等于第二个对角元之差的绝对值，因此纤维直径的上确界为 $b_w$。合法态
$$
\sigma_w=\operatorname{diag}\bigl(1-s_w-b_w/2,\ s_w+b_w/2\bigr)
$$
是两端态的中点，对整个纤维的误差至多 $b_w/2$；两端态合法，因为对应无限合法串的 $S$ 仍在 $[0,4/15]$。命题 124.7 的逐纤维下界又迫使任何中心，包括非对角中心，半径至少为 $b_w/2$。
全零前缀（含空前缀）给 $b_w=c_k$，其余 $b_w\le c_k$，定理 124.6 因而给出精确缺陷。

同前缀的 $S$ 差不超过 $c_k\to0$，所以无穷级数给出的对角态函数在 $\widehat X$ 连续，并由定理 124.8 唯一延拓核心任务。每个有限 $k$ 的缺陷仍严格为正；“任意小误差都有有限深度”不蕴含“某个有限深度误差为零”。

**命题 124.11（逐输入最终正确仍有固定最坏缺陷）。** 本命题取 $d=2$，记 $P_a=|a\rangle\langle a|$，$a\in\{0,1\}$，以 $0^\infty$ 表示总零串。定义
$$
T_0(x)=\begin{cases}P_0,&x=0^\infty,\\P_1,&x\ne0^\infty.\end{cases}
$$
则对每个有限 $k$，$\omega_k(T_0)=1$、$e_k(T_0)=1/2$。但存在一列确定性前缀预测器，对每个固定输入最终完全正确。
证明。全零前缀纤维同时包含 $0^\infty$ 和仅在某个 $j\ge k$ 取 $1$ 的合法串；它们的目标态距离为 $D(P_0,P_1)=1$。其余纤维若含已见 $1$，目标态恒为 $P_1$。故最大纤维直径为 $1$，一般下界给 $e_k\ge1/2$。
对全零前缀输出 $(P_0+P_1)/2$，对已见 $1$ 的前缀输出 $P_1$，便把最坏误差控制在 $1/2$，证明等式。

另取确定性表 $A_k(w)$：已经见到 $1$ 时输出 $P_1$，否则输出 $P_0$。总零输入在所有深度都正确；任一非零输入有首个 $1$ 的下标 $j$，从 $k=j+1$ 起永远正确。因此
$$
\forall x\in X_{\rm fs},\quad
\lim_{k\to\infty}D(T_0(x),A_k(q_kx))=0,
\qquad
\forall k,\quad\sup_{x\in X_{\rm fs}}D(T_0(x),A_k(q_kx))=1.
$$
后式由每层尚未出现的单个 $1$ 实现。这个确定性表并非最优混态表，不能将其误差 $1$ 与最优缺陷 $1/2$ 混用；同样不能把纤维直径误写成 $1/2$。
远处的单个 $1$ 趋于总零串，目标态却恒为 $P_1$，所以 $T_0$ 在核心的总零点不连续，更无连续延拓。

**命题 124.12（任务逐个有限与整个任务族一致有限的区别）。** 本命题取 $d=2$，对每个 $j\ge0$ 定义坐标任务 $T_j(x)=P_{x_j}$，则
$$
e_k(T_j)=\begin{cases}0,&j<k,\\1/2,&j\ge k.\end{cases}
$$
若先提供前缀、再揭示任务 $j$，允许模拟器按 $(j,w)$ 选择态，但在所有 $j,x$ 上评价最坏误差，则
$$
E_k=\inf_{(\sigma_{j,w})\in\mathcal D_2^{\mathbb N\times W_k}}
\sup_{j\in\mathbb N,\ x\in X_{\rm fs}}D(T_j(x),\sigma_{j,q_kx})=1/2
$$
对每个有限 $k$ 成立。这不是一次同时制备所有任务的联合量子态的要求。
证明。$j<k$ 时该位已被记录，直接输出 $P_{w_j}$ 即精确。$j\ge k$ 时，总零串与仅第 $j$ 位为 $1$ 的串同属全零前缀纤维，迫使误差至少为 $1/2$；常值中点态表给上界。
对任务族，任意表固定取 $j=k$，同一对串仍迫使最坏误差至少为 $1/2$。同时给所有已记录任务输出对应纯态、所有未记录任务输出中点态，达到该界。

每个 $T_j$ 都连续延拓且在深度 $j+1$ 精确；有限非空任务集 $J$ 有共同精确深度 $1+\max J$，空任务集没有约束。然而对无限任务族，以下两个量词序列不同：
$$
\forall j\ \exists K\ \forall k\ge K,\ e_k(T_j)=0,
\qquad
\exists K\ \forall j\ \forall k\ge K,\ e_k(T_j)=0.
$$
本例满足前者而否定后者，甚至对任意小于 $1/2$ 的共同误差预算也否定后者的近似版本。
一般固定有限维、由非空集合 $J$ 标记的任务族 $\{T_j:X_{\rm fs}\to\mathcal D_d\}_{j\in J}$，将上式的 $\mathbb N$ 换成 $J$ 定义共同缺陷。其趋零须由共同的一致连续性条件控制：
$$
\forall\varepsilon>0\ \exists\delta>0\ \forall j\in J\ \forall x,y\in X_{\rm fs},\quad
p(x,y)<\delta\ \Longrightarrow\ D(T_j(x),T_j(y))<\varepsilon.
$$
在通常集合选择下，这也是充要条件：逐任务、逐纤维选择最优中心使共同缺陷等于 $\sup_j e_k(T_j)$；两侧直径界将其趋零化为 $\sup_j\omega_k(T_j)\to0$，再用定理 124.8 中相同的前缀阈值证明。仅有每个任务各自的一致连续性不提供这个共同模量。

**命题 124.13（第 123 节逐层条件与线程完备性的勘注）。** 对第 123 节的逆系统，以下条件必须分开：$z_n\in q_n[X]$ 对每个 $n$ 成立；以及 $\pi_n(z_{n+1})=z_n$ 对每个 $n$ 成立。第 123.2 节“每个有限层都有实现”若被单独用来推出逆极限成员身份，须替换为这两项的合取。
证明与精确定义。取 $X=\{0,1\}$，各层 $Q_n=X$，$q_n$ 和 $\pi_n$ 都是恒等映射。令 $z_n$ 依奇偶交替为 $0,1$；每一层都有实现，但相邻两层不相容，故不在逆极限。

对非空 $X$，若使用实际像 $Q_n=q_n[X]$，每个 $Q_n$ 有限且取离散拓扑，连接映射由兼容读数限制而来，则自然像 $\iota[X]$ 在 $\varprojlim Q_n$ 中稠密。事实上，取线程 $z$ 的任一基本邻域，它只限制有限多个坐标；令 $m$ 为受限坐标的最大值，选 $x$ 使 $q_mx=z_m$。反复使用相容性，便有所有 $n\le m$ 的 $q_nx=z_n$，所以该像点在邻域中。没有坐标限制时任取 $x\in X$ 即可。
因此这里定义
$$
\operatorname{Ghost}(X)=\left(\varprojlim q_n[X]\right)\setminus\iota[X]
$$
才能只计实际有限读数相容后仍无法实现的线程。若改用较大陪域，$X=\{0\}$、各层 $Q_n=\{0,1\}$、$q_n(0)=0$、$\pi_n={\rm id}$ 已给反例：常值 $1$ 线程从未在任何层命中，也不在自然像的闭包中。

代数术语 $\operatorname{ThreadComplete}$ 的定义是 $\iota:X\to\varprojlim Q_n$ 满射；若各层不分离对象，也可等价说商嵌入 $\bar\iota$ 满射。它不是对任意给定拓扑或度量的完备性结论。例如在 $X_{\rm fs}$ 上改取离散距离，空间完备，但前缀线程仍含不属于核心的交替无限串。第 123.3 节与本节命题 124.2 指定前缀拓扑、稠密嵌入和完备载体，才把该具体线程空间识别为度量完备化。

**命题 124.14（第 123.4 节 Hilbert 动力学界的充分条件）。** 设 $H$ 为 Hilbert 空间，$S_n\subseteq H$ 为递增闭子空间，$P_n:H\to S_n$ 为正交投影。每个 $T_n:S_n\to S_n$ 是有界线性算子，并满足对所有 $n\le m$ 和 $u\in S_m$，
$$
P_n(T_mu)=T_n(P_nu).
$$
若有有限 $M\ge0$ 使 $\sup_n\|T_n\|\le M$，则逐层作用保持有界相容线程，并有
$$
\sup_n\|T_nz_n\|\le M\sup_n\|z_n\|.
$$
证明。令 $B=\sup_n\|z_n\|<\infty$，则 $\|T_nz_n\|\le\|T_n\|\|z_n\|\le MB$。而线程相容性给
$P_n(T_mz_m)=T_n(P_nz_m)=T_nz_n$，两项条件俱全。
这将第 123.4 节的算子界明确为上述类型中的充分条件；本命题不把它断言为无条件必要条件，也不从它推出有限支持像保持。

后一个限制可具体检验。取 $H=\ell^2(\mathbb N)$、$S_n$ 为前 $n$ 个坐标子空间，$v_j=2^{-j-1}$，则 $\|v\|^2=1/3$。令 $T_0=0$，$n\ge1$ 时置 $T_nu=u_0P_nv$。它们投影相容且 $\|T_n\|\le\|v\|$，但由有限支持向量 $e_0$ 所给的线程，经逐层作用后重建为无限支持的 $v$。故保持 Hilbert 有界线程与保持原有限支持载体是两项不同要求。

**命题 124.15（第 123.5 节归一化记录 Gram 条件的勘注）。** 有限复矩阵 $G$ 能表示某个有限维 Hilbert 空间内一族归一化记录向量的 Gram 矩阵，当且仅当它是 Hermitian、半正定且对角元全为 $1$。若预先固定记录空间维数为 $r$，还须且只须 $\operatorname{rank}G\le r$；严格正定不是必要条件。
证明。若 $G_{ab}=\langle v_a,v_b\rangle$，则 $c^*Gc=\|\sum_a c_av_a\|^2\ge0$，共轭对称性给 Hermitian 性，归一化给单位对角；秩不超过记录空间维数。
反向由有限维谱分解取 $B$ 使 $G=B^*B$，$B$ 的各列即所需向量，对角条件使各列范数为 $1$。只保留非零特征值可在维数 $\operatorname{rank}G$ 中实现，再嵌入给定的 $r$ 维空间。
至少两个记录全取同一单位向量时，Gram 矩阵全为 $1$，秩为 $1$，合法而奇异。因此第 123.5 节的“Gram 矩阵的正定性”在归一化记录意义下应读作上述半正定条件；它与通道完全正性、动力学像集不变性仍是不同类型的要求。

**约定 124.16（来源、证明范围与后续问题）。** 本节所引 CSA、Z 与 Q 分别指 `CONTEXTUAL_SPACETIME_ARITHMETIC.md`、`CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md` 与本量子卷。CSA 定义 1–3、§§14–16，Z371.1–2、Z477.3，以及 Q54.7、Q57、Q120–122 的引用版本均为仓库提交 `58d94fb6c3b75e5f0fc33f184e510f46949efdca`；Q123 的引用版本为 `71d892f05c219488670b0a10ca6b9bf11b975cfe`。Q54.7 给纤维直径与近似预测的两侧界，Q57 固定特定未来实验族；Q120 使用含参考的过程 diamond 缺陷，Q121–122 的态族缺陷和 Q123 的线程问题各保留原类型。本节将历史参数集明确换成 $X_{\rm fs}$ 并使用上确界，所需证明已逐项给出。

同一基线版本的 `D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction.lean` 中，`bounded_inverse_limit_reconstruction` 在完备内积空间、单调且具有正交投影的子空间序列上，给累积闭子空间与有界相容线程的规范线性等距双射，并给最终残余商的同类表示。`D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.lean` 的 `compatible_unbounded_coordinates` 给实际 $\ell^2$ 坐标截断线程、范数平方为 $n$、无界及无法由单个 $\ell^2$ 向量投影实现等结论。`D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion.lean` 的 `ThreadComplete` 定义为 `stateThread` 满射，`stateThread_bijective_iff_complete_and_separates` 对应线程完备与各层联合分离的合取，不带拓扑完备性的假设或结论。这些声明分别支持所写类型中的既有结果，不承载本节的新前缀缺陷桥。

一般完备延拓与 Heine–Cantor 原理可见钉版 Mathlib（`lake-manifest.json` 的 mathlib 修订 `db584cd6d46c92f209a44c0f1c829460d327499d`，`v4.33.0`）：`Mathlib/Topology/UniformSpace/Completion.lean` 的 `UniformSpace.Completion.extension`、`extension_coe`、`uniformContinuous_extension`、`extension_unique`，以及 `Mathlib/Topology/UniformSpace/HeineCantor.lean` 的 `CompactSpace.uniformContinuous_of_continuous`。延拓的正确限制要求原映射一致连续；目标完备且分离时具有相应唯一性，不能仅凭对任意函数可写下 extension 定义就声称得到延拓。本节是结合这些通常原理与所引仓内模型的 `repo-derived` 普通证明，不提出新颖性或新增 Lean 认证主张。

本节的静态制备模型只比较指定经典输入族的输出态，不保证隐藏参考关联、相干输入行为或自适应过程的模拟；这些要求须另指定联合态或完整过程。定理 124.8 的存在性不提供有效连续模量或高效求最优中心的算法，有限维紧性所得中心存在性也未推广到无限维态空间。下一项研究问题因此是：在增加参考或过程结构后，哪些可检验的连续性与紧性条件仍能给出相应缺陷的精确延拓判据。

## 追加锚（本行以下为增补区）

## 125. 均匀相干态的局部极限与表示边界

本节复用 Q109 的有限均匀态及定义 124.1 的零下标合法串 $W_L$、紧载体 $\widehat X$ 和有限支持核心 $X_{\rm fs}$。固定左端第 $0$ 位而向右增加长度，取 $\varphi=(1+\sqrt5)/2$、$\alpha=\varphi^{-1}$，于是 $0<\alpha<1$ 且 $\alpha+\alpha^2=1$。记 $D_L=|W_L|=F_{L+2}$，其中 $F_0=0,F_1=1$，特别地 $D_0=1$。在完整 qubit 空间 $\mathcal K_L=(\mathbb C^2)^{\otimes L}$ 中沿用
$$
|\Omega_L\rangle=|\Psi_L\rangle
=D_L^{-1/2}\sum_{w\in W_L}|w\rangle.
$$
所讨论的是这一个指定态族的局部极限及其柱读数的表示条件；数字载体仍区别于 CSA 定义 1–3 的事件档案。以下均为普通数学定义与证明。

**命题 125.1（固定左窗口的约化极限）。** 固定整数 $n\ge1$，令 $L=n+m$，$m\ge1$，并在完整张量积上定义
$$
\rho_n^{(L)}=\operatorname{Tr}_{\{n,\ldots,L-1\}}
|\Omega_L\rangle\langle\Omega_L|.
$$
对 $u,v\in W_n$，有
$$
(\rho_n^{(L)})_{uv}=
\begin{cases}
D_m/D_L,&u_{n-1}=v_{n-1}=0,\\
D_{m-1}/D_L,&\text{其余合法前缀对}.
\end{cases}
$$
含非法前缀的行或列全为零。置
$$
s_n=\sum_{u\in W_n}|u\rangle,\qquad
t_n=\sum_{\substack{u\in W_n\\u_{n-1}=0}}|u\rangle.
$$
当 $L\to\infty$ 且 $n$ 固定时，$\rho_n^{(L)}$ 在迹范数下收敛到
$$
\rho_n=\alpha^{n+1}|s_n\rangle\langle s_n|
       +\alpha^{n+2}|t_n\rangle\langle t_n|.
$$
每个 $\rho_n$ 都正、迹为 $1$、秩恰为 $2$，且在完整 qubit 空间之间满足
$$
\operatorname{Tr}_{\{n\}}\rho_{n+1}=\rho_n.
$$

证明。偏迹的矩阵元是使 $uz$ 与 $vz$ 同时合法的长度 $m$ 尾字 $z$ 的数量除以 $D_L$。若两个前缀末位均为 $0$，任意 $z\in W_m$ 均可；否则 $z$ 的首位必须为 $0$，余下 $m-1$ 位任意合法，数量为 $D_{m-1}$。这个计数也含 $m=1$ 的情形。非法前缀不可能被延长为合法字，故相应行列为零。

由 Binet 公式 $F_k=(\varphi^k-(-\varphi^{-1})^k)/\sqrt5$，固定 $n$ 时有
$$
\lim_{m\to\infty}\frac{D_m}{D_{m+n}}=\alpha^n,
\qquad
\lim_{m\to\infty}\frac{D_{m-1}}{D_{m+n}}=\alpha^{n+1}.
$$
两前缀末位均为 $0$ 时，所列 $\rho_n$ 的矩阵元为 $\alpha^{n+1}+\alpha^{n+2}=\alpha^n$；其余合法对为 $\alpha^{n+1}$，所以它正是逐元极限。固定维数 $2^n$ 下，矩阵元收敛给 Hilbert–Schmidt 范数收敛，再由 $\|B\|_1\le\sqrt{2^n}\|B\|_{\rm HS}$ 给迹范数收敛。

两个系数严格为正，故 $\rho_n$ 正且其核为 $s_n^\perp\cap t_n^\perp$。向量 $t_n$ 非零；合法词 $0^{n-1}1$ 在 $s_n$ 中的系数为 $1$，在 $t_n$ 中为 $0$，而 $0^n$ 在两者中的系数都为 $1$，故两向量线性独立，秩恰为 $2$。这里直接计算极限的秩，并未假定取极限保持有限态的秩。

为核对偏迹，对任意长度 $n$ 的前缀对求
$$
(\operatorname{Tr}_{\{n\}}\rho_{n+1})_{uv}
=\sum_{a\in\{0,1\}}(\rho_{n+1})_{ua,va}.
$$
若 $u,v$ 合法且末位均为 $0$，附 $0$ 与附 $1$ 两项分别是 $\alpha^{n+1}$、$\alpha^{n+2}$，和为 $\alpha^n$。其余合法对只有共同附 $0$ 的项非零，为 $\alpha^{n+1}$。含非法前缀的两项均为零。这证明全矩阵偏迹相容。最后
$$
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},
\qquad \operatorname{Tr}\rho_1=\alpha+\alpha^2=1;
$$
偏迹保持迹，逐层得到全部归一化。Q109 的有限 Schmidt 秩与谱公式在此只作为既有有限态背景。

**命题 125.2（完整局部代数上的态及局部弱星极限）。** 令 $\mathcal A_n=M_{2^n}(\mathbb C)$，嵌入为 $A\mapsto A\otimes I_2$，以 $\mathcal A_{\rm loc}$ 表示按这些嵌入识别后的代数并，$\mathcal A$ 为其算子范数完备化，即单侧 qubit UHF 代数。存在唯一态 $\omega:\mathcal A\to\mathbb C$ 满足
$$
\omega(A)=\operatorname{Tr}(\rho_n A)\qquad(A\in\mathcal A_n).
$$
将每个有限态 $|\Omega_L\rangle\langle\Omega_L|$ 接上全零乘积尾态，得到 $\mathcal A$ 上的态 $\widetilde\omega_L$，则
$$
\widetilde\omega_L(A)\longrightarrow\omega(A)\qquad(A\in\mathcal A).
$$
这里弱星收敛指 $\sigma(\mathcal A^*,\mathcal A)$ 下逐可观测量收敛。任意其它态延拓，只要在前 $L$ 位与该有限密度一致，也有同一极限。上述代数嵌入不由合法空间上的压缩自动给出。

证明。令 $\omega_n(A)=\operatorname{Tr}(\rho_n A)$。命题 125.1 给
$$
\omega_{n+1}(A\otimes I_2)=\omega_n(A),\qquad
|\omega_n(A)|\le\|A\|,\qquad \omega_n(I)=1.
$$
所以这些泛函在 $\mathcal A_{\rm loc}$ 上定义一个良定、范数为 $1$ 的线性泛函，并唯一连续延拓到 $\mathcal A$。为核对延拓的正性，给定 $B\in\mathcal A$，取局部 $B_j\to B$，则 $B_j^*B_j\to B^*B$ 且 $\omega(B_j^*B_j)\ge0$，故 $\omega(B^*B)\ge0$。$\mathcal A$ 是 $C^*$ 代数，每个正元都是其正平方根的平方，故延拓为正；其单位值仍为 $1$，即为态。稠密性也给唯一性。

全零尾延拓可具体按有限层定义：前 $k\le L$ 位取 $|\Omega_L\rangle\langle\Omega_L|$ 的约化密度，前 $k>L$ 位取
$$
|\Omega_L\rangle\langle\Omega_L|
\otimes|0^{k-L}\rangle\langle0^{k-L}|.
$$
这组密度正、归一且偏迹相容，故由刚才的延拓论证给 $\widetilde\omega_L$。固定 $A\in\mathcal A_n$，当 $L\ge n+1$ 时，
$$
|\widetilde\omega_L(A)-\omega(A)|
\le\|\rho_n^{(L)}-\rho_n\|_1\|A\|\longrightarrow0.
$$
对一般 $A\in\mathcal A$ 及 $\varepsilon>0$，取局部 $B$ 使 $\|A-B\|<\varepsilon$。两态范数均为 $1$，故差值不超过 $2\varepsilon+|\widetilde\omega_L(B)-\omega(B)|$，得到逐点收敛。同一论证只用前 $L$ 位的密度和态范数为 $1$，因而适用于所说的任何延拓。固定窗口的迹范数收敛与这里的弱星收敛，不给出全局密度的迹范数收敛结论。

压缩的区别已有两位反例。令 $Q$ 为 $\mathcal K_2$ 到 $\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}$ 的正交投影，$X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$，定义 $\kappa(A)=Q(A\otimes I_2)Q$，视为合法子空间上的算子。因为 $(X\otimes I_2)|01\rangle=|11\rangle$，有
$$
\kappa(X)^2|01\rangle=0,
\qquad
\kappa(X^2)|01\rangle=|01\rangle.
$$
所以这条压缩不是乘法同态，不能用它把 $M_{|W_n|}(\mathbb C)$ 自动组成通常张量嵌入塔。这只否定所写压缩方案，不排除其它受约束代数的构造，也不规定完整局部代数的所有动力学保持无相邻 $1$ 的约束。

**命题 125.3（固定左边界柱律与 Z 圆周概率）。** 对 $u\in\{0,1\}^n$，$n\ge1$，记 $[u]=\{x\in\widehat X:q_nx=u\}$，并约定 $[\varnothing]=\widehat X$。存在唯一 Borel 概率 $\mu$ 满足
$$
\mu([u])=\omega(|u\rangle\langle u|)=
\begin{cases}
\alpha^{n+u_{n-1}},&u\in W_n,\\
0,&u\notin W_n.
\end{cases}
$$
在 Q124.1 对 Z 卷载体 $K$ 与 $\widehat X$ 的相同数字及 Borel 结构的识别下，$\mu=(s_Z)_*\lambda$，其中 $\lambda$ 是 Z396.1 的圆周长度概率，$s_Z:\mathbb T\to K$ 是 Z400.1 的 Borel 截面。此柱律的初始分布与行随机转移矩阵为
$$
q=(\alpha,\alpha^2),\qquad
P=\begin{pmatrix}\alpha&\alpha^2\\1&0\end{pmatrix}.
$$
它等同于虚拟左邻位固定 $x_{-1}=0$ 后由 $P$ 生成的边界律，而非以
$$
\pi=\frac{(\varphi^2,1)}{\varphi^2+1}
$$
为初始分布的平稳 Parry 律。

证明。命题 125.1 的对角元给显示的柱读数。为建立其 Borel 概率实现而不只保留一组有限分布，记 Z 卷相位映射为 $H_Z$，则 $H_Zs_Z=\operatorname{id}_{\mathbb T}$。$s_Z$ 为 Borel，故 $\nu=(s_Z)_*\lambda$ 是 $K$ 上的 Borel 概率。

将 Z381.2 对应于合法词 $u$ 的柱集和定向开弧分别记作 $C_u^Z$、$A_u^Z$；其两个端点为 $E_i,E_j$，该条定向弧的长度为 $\alpha^{n+u_{n-1}}$。那里的完整端点公式给
$$
C_u^Z=H_Z^{-1}(A_u^Z)\cup\{e_i^+,e_j^-\}.
$$
由于截面逐点落在相应相位纤维中，这个等式蕴含
$$
s_Z^{-1}(C_u^Z)\mathbin{\triangle}A_u^Z
\subseteq\{E_i,E_j\}.
$$
Z396.1 给两个端点的质量均为零，开弧的质量等于其长度，因而
$$
\nu(C_u^Z)=\lambda(s_Z^{-1}(C_u^Z))
=\lambda(A_u^Z)=\alpha^{n+u_{n-1}}.
$$
非法柱为空，空前缀柱为整个载体，故可取 $\mu=\nu$。前缀柱集连同空集构成生成 Borel 集的 $\pi$ 系统：交集或为空、或为其中更深的柱集，且这些柱集是可数拓扑基。概率测度的唯一性定理遂使任意具有全部相同柱读数的 Borel 概率都等于 $\nu$。这里不需要 $H_Z$ 或 $s_Z$ 为双射，也不忽略开弧内部可能存在的分裂纤维。

每个合法柱都具有正质量，可以逐柱计算条件概率。若 $u_{n-1}=0$，则
$$
\frac{\mu([u0])}{\mu([u])}=\alpha,
\qquad
\frac{\mu([u1])}{\mu([u])}=\alpha^2.
$$
若 $u_{n-1}=1$，则 $u1$ 非法，而
$$
\frac{\mu([u0])}{\mu([u])}
=\frac{\alpha^{n+1}}{\alpha^{n+1}}=1,
\qquad
\frac{\mu([u1])}{\mu([u])}=0.
$$
初始一位柱质量给 $q$，上述比值只依赖末位，证明 Markov 性及所列 $P$；$q$ 正好是 $P$ 的第 $0$ 行。由 $\pi_1=\pi_0\alpha^2$ 与 $\pi_0+\pi_1=1$，得到所列唯一平稳分布，亦即 `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md` 第1594部的分布。

明确地，对数字左移 $\sigma(x)_j=x_{j+1}$，有
$$
\mu(\sigma^{-1}[1])=(qP)_1=\alpha^3
\ne\alpha^2=\mu([1]).
$$
所以非平稳性是相对于数字左移而言；它不把数字左移与 Z 卷的算术后继或圆周旋转认作同一变换。与 Z 概率相同的只是对角柱数据，不能据此认定整个量子态相同：例如 $\langle0|\rho_1|1\rangle=\alpha^2>0$，是柱概率本身未指定的相干读数。

**命题 125.4（有限支持基上的 normal 密度障碍及其表示边界）。** 在 $H_{\rm fs}=\ell^2(X_{\rm fs})$ 中取标准基 $(e_x)_{x\in X_{\rm fs}}$，对每个有限词 $u$ 定义柱投影
$$
C_ue_x=\mathbf1_{\{q_{|u|}x=u\}}e_x.
$$
不存在正迹类算子 $R$ 满足 $\operatorname{Tr}R=1$ 且同时对所有有限词有 $\operatorname{Tr}(RC_u)=\mu([u])$。尽管每个有限深度的全部柱读数都可由该空间上的有限秩密度精确实现，这些实现不能由一个这样的 $R$ 统一承担。此外，$\mu$ 的每个单点质量均为零，$\mu(X_{\rm fs})=0$。局部态 $\omega$ 仍有 GNS 表示及其中的秩一密度实现。

证明。有限支持核心可写为
$$
X_{\rm fs}=\bigcup_{N\ge0}\{u0^\infty:u\in W_N\},
$$
故它可数；补零保持合法性。对任意 $x\in\widehat X$，递减的柱集 $[q_nx]$ 的交恰为 $\{x\}$，由概率测度的从上连续性有
$$
\mu(\{x\})=\lim_{n\to\infty}\mu([q_nx])
\le\lim_{n\to\infty}\alpha^n=0.
$$
单点为闭集，可数个这样的单点给 $X_{\rm fs}$ 为 Borel 零测集。

假设所说的 $R$ 存在。对每个 $x\in X_{\rm fs}$ 及 $n\ge1$，秩一投影满足 $|e_x\rangle\langle e_x|\le C_{q_nx}$。正迹类算子定义正迹泛函；具体地，对正有界 $B$ 有 $\operatorname{Tr}(RB)=\operatorname{Tr}(R^{1/2}BR^{1/2})\ge0$。所以
$$
0\le\langle e_x,Re_x\rangle
\le\operatorname{Tr}(RC_{q_nx})
=\mu([q_nx])\le\alpha^n\longrightarrow0.
$$
每个基对角元均为零，而正迹类算子的迹等于任意可数正交标准基上的对角元之和，得到
$$
1=\operatorname{Tr}R
=\sum_{x\in X_{\rm fs}}\langle e_x,Re_x\rangle=0,
$$
矛盾。证明没有要求 $R$ 对角化或与柱投影对易，也没有假定整个 UHF 代数在 $H_{\rm fs}$ 上具有某个自然表示。

为给出有限深度的准确对照，对固定 $N\ge1$ 定义
$$
R_N=\sum_{u\in W_N}\mu([u])
|e_{u0^\infty}\rangle\langle e_{u0^\infty}|.
$$
这些不同的补零串是正交基标记，系数非负且和为 $1$，故 $R_N$ 为正归一有限秩密度。对 $|v|\le N$，深度 $N$ 的细柱分割 $[v]$，从而
$$
\operatorname{Tr}(R_NC_v)
=\sum_{\substack{u\in W_N\\u|_{|v|}=v}}\mu([u])
=\mu([v]).
$$
这里仅匹配对角柱读数，没有把 $R_N$ 与 Q109 的相干纯态或其约化矩阵认作同一密度。

最后直接给 $\omega$ 的通常 GNS 构造。取
$$
\mathcal N_\omega=\{B\in\mathcal A:\omega(B^*B)=0\},
\qquad
\langle[B],[C]\rangle=\omega(B^*C)
$$
并以第二变量线性的内积约定使用此式。正性作用于 $(B+zC)^*(B+zC)$ 给 Cauchy–Schwarz 不等式，故零半范数元与所有元正交，商 $\mathcal A/\mathcal N_\omega$ 上的内积良定。由 $A^*A\le\|A\|^2I$ 得
$$
\omega(B^*A^*AB)\le\|A\|^2\omega(B^*B).
$$
因此 $\mathcal N_\omega$ 是左理想，左乘 $[B]\mapsto[AB]$ 良定且范数至多 $\|A\|$；它延拓到商内积空间的完备化 $H_\omega$，记作 $\pi_\omega(A)$。左乘保持乘法和单位，且由内积公式其伴随为 $\pi_\omega(A^*)$，所以 $\pi_\omega$ 是幺星表示。向量 $\xi=[I]$ 的范数为 $1$，$\pi_\omega(A)\xi=[A]$ 的线性张成稠密，故 $\xi$ 循环，且
$$
\omega(A)=\langle\xi,\pi_\omega(A)\xi\rangle
=\operatorname{Tr}_{H_\omega}
\bigl(|\xi\rangle\langle\xi|\,\pi_\omega(A)\bigr).
$$
秩一密度位于 $B(H_\omega)$，其向量态限制到 $\pi_\omega(\mathcal A)$ 不因此必为纯态。normal 实现依赖指定的可观测量与表示，不能只由抽象 Hilbert 空间的基数判断。因而本命题给的是有限支持基及上述柱投影的实现障碍，同时保留了全局代数态及其它 Hilbert 表示的实现。

**约定 125.5（引用与证明范围）。** Q、Z、CSA 分别指本量子卷、`CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md`、`CONTEXTUAL_SPACETIME_ARITHMETIC.md`。本节所引 Q109、Q123–124、Z381.2、Z396.1、Z400.1、CSA 定义 1–3 及 `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY.md` 第1594部，均取仓库提交 `c225a37b44971d289ae51b8b324f5cef78e31b82` 的版本。Q123–124 的载体与相容性问题在这里落实为有限相干态、局部代数态和指定表示中的柱读数问题；所用局部极限不另申报 Q109 的有限 Schmidt 结论。

同一版本 `D5/S1/Digit/Infinite/WindowCylinderPartition.lean` 的 `window_cylinder_partition` 给合法窗口的区间几何、准确弧长及定向端点纤维，其结论不含本节的量子态构造。`D5/S3/Quantum/Measurements/OrthogonalAdditivity.lean` 的 `orthogonal_additivity` 在 `SequentiallyNormal` 与 `strong_complete` 等假设下给正交投影族的可数可加性；命题 125.4 使用直接的正迹类论证，不把这些假设省略后援引该声明。

钉版 Mathlib 修订 `db584cd6d46c92f209a44c0f1c829460d327499d` 的 `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` 提供 `PositiveLinearMap.gnsStarAlgHom`，该文件明确将单位循环向量的构造列为 TODO，故它不作为上文完整循环向量结论的现成证明；上文已独立给出通常 GNS 构造。本节为结合所引模型与标准概率、算子代数方法的 `repo-derived` 普通推导，不提出新颖性或新增 Lean 认证主张。

## 追加锚（本行以下为增补区）

## 126. 固定尾零载体上的事件组合预算与精确最优误差

固定非负整数 $K,N$ 与正整数 $M$，令 $\alpha=(\sqrt5-1)/2$，$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。沿用 Q123–125 的前缀方向，以
$$
X=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\ \text{对所有 }j\ge0\},
\qquad W_n=q_n[X],\qquad W_0=\{\varnothing\}
$$
表示完整合法流及其长度 $n$ 前缀，$q_nx=(x_0,\ldots,x_{n-1})$。记 $[u]=\{x\in X:q_nx=u\}$，$[\varnothing]=X$，并固定尾零载体
$$
S_K=\{w0^\infty:w\in W_K\},\qquad
D_K=|S_K|=|W_K|=F_{K+2}.
$$
$\operatorname{Prob}(S_K)$ 指集中在这个指定集合上的全部概率，允许个别原子质量为零；$U_K$ 为每点质量 $1/D_K$ 的均匀概率，即 Q109 有限均匀态的基测量分布补零后的概率。

目标取 Q125.3 的固定虚拟左邻位为零的边界律，其全部柱读数在此明确为
$$
\mu([\varnothing])=1,\qquad
\mu([u])=
\begin{cases}
\alpha^{n+u_{n-1}},&u\in W_n,\ n\ge1,\\
0,&u\notin W_n.
\end{cases}
$$
这些权重由 $\alpha+\alpha^2=1$ 相容：末位为零的柱分成权重比为 $\alpha,\alpha^2$ 的两柱，末位为一的柱只能接零且质量不变；初层质量之和为一。因此通常的相容有限分布延拓与柱集唯一性给出 $X$ 上的唯一 Borel 概率。该律不对数字左移平稳，因为 $\mu(x_1=1)=\alpha^3\ne\alpha^2=\mu(x_0=1)$。这里的数字流与概率事件保留各自类型，不与 CSA 定义 1–3 的情境档案混同。

**命题 126.1（同层柱集组合预算的精确极小极大值）。** 对 $\nu\in\operatorname{Prob}(S_K)$ 定义
$$
d_M(\nu,\mu)=\sup_{n\ge1}\,
\max_{\substack{J\subseteq W_n\\|J|\le M}}
\left|\nu\left(\bigcup_{u\in J}[u]\right)
      -\mu\left(\bigcup_{u\in J}[u]\right)\right|.
$$
每个 $J$ 中的柱集必须有同一个深度 $n$，空 $J$ 允许。则
$$
\min_{\nu\in\operatorname{Prob}(S_K)}d_M(\nu,\mu)
=\min\left(1,\frac{M}{D_K}\right).
$$
若 $M<D_K$，唯一经典最优分布是 $U_K$；若 $M\ge D_K$，全部 $\nu$ 的误差均为 $1$。后一情形在 $K\ge1$ 时不唯一，在 $K=0$ 时定义域本身只有 $\delta_{0^\infty}=U_0$。对 $U_K$，任一有限深度的上述事件差都严格小于所列上确界，故不能把对深度的 $\sup$ 换成 $\max$。

证明。将 $D=D_K$ 个原子质量排序为 $p_1\ge\cdots\ge p_D\ge0$，令 $m=\min(M,D)$、$T_m=\sum_{i=1}^mp_i$。在每个 $n>K$，前 $m$ 个原子的深度 $n$ 前缀给两两不交的隔离柱，每柱在 $\mu$ 下均有质量 $\alpha^n$，故
$$
d_M(\nu,\mu)\ge |T_m-m\alpha^n|.
$$
令 $n\to\infty$，得到 $d_M(\nu,\mu)\ge T_m\ge m/D$，最后一步是最大 $m$ 个质量的平均值不小于全部质量的平均值。

下面证明 $U_K$ 的上界。若 $1\le n\le K$、$u\in W_n$ 且 $b=u_{n-1}$，合法延长计数给
$$
U_K([u])=\frac{F_{K-n+2-b}}{D_K}.
$$
末位零时可接任意长度 $K-n$ 的合法尾字；末位一且仍需延长时，下一位被迫为零。这两种计数也包含 $n=K$ 时的空延长，分别为 $F_2=F_1=1$。置 $r=K-n+2-b$、$s=K+2$，则 $1\le r<s$、$s-r=n+b$。Binet 公式给
$$
F_r-\alpha^{s-r}F_s
=\frac{-(-\alpha)^r+\alpha^{s-r}(-\alpha)^s}{\sqrt5},
\qquad
\left|F_r-\alpha^{s-r}F_s\right|
\le\frac{2\alpha}{\sqrt5}<1.
$$
因此每个这样的柱误差严格小于 $1/D_K$。

若 $n>K$，每个柱在 $U_K$ 下的质量为零或 $1/D_K$，而
$$
0<\mu([u])\le\alpha^n\le\alpha^{K+1}<\frac1{D_K}
\qquad(u\in W_n).
$$
最后一个严格不等式在 $K=0$ 时是 $\alpha<1$；在 $K\ge1$ 时，深度 $K$ 的柱权重 $\alpha^K$ 与 $\alpha^{K+1}$ 均出现且总和为一，故其平均值满足
$$
\alpha^{K+1}<\frac1{D_K}<\alpha^K.
$$
这也使每个深柱误差严格小于 $1/D_K$。同层柱集互不相交，对至多 $M$ 项求和并用三角不等式，得到事件差至多 $M/D_K$；概率差又至多为一。结合下界即得最优值。$M<D_K$ 时，有限深度事件差严格小于 $M/D_K$；$M\ge D_K$ 时，有限层的 $\mu_n$ 对每个合法词赋正质量，所以不存在两概率相差为一的事件，仍严格小于上确界一。

当 $M<D$ 且 $\nu$ 最优时，下界迫使 $T_M=M/D$。于是
$$
\sum_{i\le M<j}(p_i-p_j)=D T_M-M=0.
$$
每项非负，故所有跨越分界的差均为零；两侧均非空，遂使全部质量相等，证明唯一性。若 $M\ge D$，下界已为一，概率上界给每个 $\nu$ 都取一，包括 $K=0$ 的单点定义域。

**命题 126.2（有限窗口总变差及截断的最优者）。** 记 $\nu_n=(q_n)_*\nu$、$\mu_n=(q_n)_*\mu$，在有限集 $W_n$ 上取
$$
\operatorname{TV}(p,q)=\frac12\sum_{u\in W_n}|p(u)-q(u)|.
$$
则
$$
\min_{\nu\in\operatorname{Prob}(S_K)}
\max_{0\le n\le N}\operatorname{TV}(\nu_n,\mu_n)
=\begin{cases}
0,&N\le K,\\
1-D_K\alpha^N,&N>K.
\end{cases}
$$
$N\le K$ 时最优者恰为满足 $\nu_N=\mu_N$ 的分布；$N>K$ 时最优者恰为原子质量
$$
p_w=\nu(\{w0^\infty\})\ge\alpha^N
\qquad(w\in W_K)
$$
的分布。令 $\tau_Kx=(q_Kx)0^\infty$、$\nu^{\rm cut}=(\tau_K)_*\mu$，则 $\nu^{\rm cut}$ 是唯一同时对所有非负整数 $N$ 最优的分布。$U_K$ 与 $\nu^{\rm cut}$ 都对每个固定 $N>K$ 最优，但
$$
d_1(\nu^{\rm cut},\mu)=\alpha^K,
\qquad
\alpha^K>\frac1{D_K}\quad(K\ge1).
$$
$K=0$ 时两分布相同，$N=0$ 的误差为零，$N>0$ 的最优误差为 $1-\alpha^N$，而 $d_1=1$。

证明。前缀投影收缩总变差，故对每个固定 $\nu$ 有
$$
\max_{0\le n\le N}\operatorname{TV}(\nu_n,\mu_n)
=\operatorname{TV}(\nu_N,\mu_N).
$$
当 $N\le K$ 时，$q_N:S_K\to W_N$ 满射，任意目标前缀都可补零至长度 $K$，因此可以给这些原像分配质量以精确实现 $\mu_N$；总变差为零当且仅当两有限分布相同。这也包括 $N=0$，此时所有概率的空前缀分布相同。

当 $N>K$ 时，$\nu_N$ 集中在
$$
A_{K,N}=\{w0^{N-K}:w\in W_K\}\subseteq W_N,
\qquad |A_{K,N}|=D_K
$$
上，其中每个词在 $\mu_N$ 下的质量都是 $a=\alpha^N$。有限概率的重叠质量公式遂给出精确式
$$
\operatorname{TV}(\nu_N,\mu_N)
=1-\sum_{w\in W_K}\min(p_w,a)
\ge1-D_Ka.
$$
逐项 $\min(p_w,a)\le a$，等号成立当且仅当每项 $p_w\ge a$。命题 126.1 证明中的 $a\le\alpha^{K+1}<1/D_K$ 说明这些条件可由 $U_K$ 同时满足，故下界可达。

截断概率在所有 $n\le K$ 精确保持柱读数，且其原子质量为
$$
\nu^{\rm cut}(\{w0^\infty\})=
\begin{cases}
\alpha^{K+w_{K-1}},&K\ge1,\\
1,&K=0.
\end{cases}
$$
$K\ge1$ 时每项至少为 $\alpha^{K+1}$，$K=0$ 时唯一质量为一，所以它也满足每个 $N>K$ 的等号条件。反过来，同时最优必在 $N=K$ 精确实现 $\mu_K$；$q_K:S_K\to W_K$ 是双射，故原子质量被唯一确定为截断概率。这证明全部窗口同时最优的唯一性，并不把固定深窗口的两类最优者分开。

为计算截断概率的 $d_1$，$n\le K$ 的柱误差为零。$K\ge1$ 且 $n>K$ 时，含有支撑原子的柱误差为 $p_w-\alpha^n$，其中 $\alpha^{K+1}\le p_w\le\alpha^K$；不含支撑原子的柱误差至多为 $\alpha^n\le\alpha^{K+1}$。故 $d_1\le\alpha^K$，而 $[0^n]$ 上的差为 $\alpha^K-\alpha^n$，趋于 $\alpha^K$，证明等号。$K=0$ 时同一柱上的差为 $1-\alpha^n$，上确界为一。命题 126.1 中的严格平均值界给 $K\ge1$ 时与 $1/D_K$ 的严格差异。因此，精确保留截至 $K$ 的读数与优化全深度的受限事件误差是不同任务，虽然后者的均匀最优者与截断概率都优化每个 $N>K$ 的固定窗口。

由命题 126.1，固定 $M$ 时最优误差随 $K\to\infty$ 趋于零；若正整数预算 $M_K$ 随 $K$ 变化，则该误差趋零当且仅当 $M_K/D_K\to0$。$M$ 只计一次事件表达允许使用的同深度柱集数，不是运行时间、能量或物理存储量。若完全取消这个数目的限制，有限层事件变分式给全层事件差的最大值为 $\operatorname{TV}(\nu_n,\mu_n)$；对任意固定 $K$ 与 $\nu\in\operatorname{Prob}(S_K)$，事件 $A_{K,n}$ 的差为 $1-D_K\alpha^n$，故全部深度上的上确界为一。这是 Z458.5 的有限或可数支撑对无原子概率的既有分离机制在前缀事件中的体现，不另作为新增结论。

量子读数只给如下带条件的下界。固定 $n>K$，在 $\mathcal K_n=(\mathbb C^2)^{\otimes n}$ 的计算基上，令 $P_{K,n}$ 为投到 $\operatorname{span}\{|u\rangle:u\in A_{K,n}\}$ 的正交投影。设 $\sigma_n,\rho_n$ 为密度算子，且
$$
\sigma_n=P_{K,n}\sigma_nP_{K,n},\qquad
\langle u|\rho_n|u\rangle=\mu_n(u)
\quad(u\in\{0,1\}^n),
$$
其中非法词的目标对角质量为零。以 $D(\sigma,\rho)=\tfrac12\|\sigma-\rho\|_1$ 记迹距，则
$$
D(\sigma_n,\rho_n)
\ge\left|\operatorname{Tr}\bigl(P_{K,n}(\sigma_n-\rho_n)\bigr)\right|
=1-D_K\alpha^n.
$$
证明此测量界只需将迹零 Hermitian 算子 $H=\sigma_n-\rho_n$ 写成正负谱部分 $H_+-H_-$：两部分的迹均为 $\|H\|_1/2$，而 $0\le P_{K,n}\le I$ 使 $\operatorname{Tr}(P_{K,n}H)$ 位于这两个相反界之间。支撑条件使 $\operatorname{Tr}(P_{K,n}\sigma_n)=1$，指定对角律使另一迹为 $D_K\alpha^n$。若每个 $n>K$ 的前缀都满足所列条件，则由迹距至多为一得到全深度上确界一。仅有秩或 Hilbert 空间维数不能推出这里的支撑条件；经典最优等式也不直接给量子迹距的等号或相干态最优者唯一性。

本节引用的 Q109、Q123–124、Z381.2（柱弧）、Z396.1（长度概率）、Z400.1（Borel 截面）、Z458.5 及 CSA 定义 1–3，取仓库提交 `ca874c0d5f5c42b3546795595814b36df13d1013`；Q125.3 的正文版本为 `7af72f9910546ca2aa0bfa3a6bbaed4d8a393efb`。前一提交的 `D5/S3/TotalVariation/Metric.lean` 中 `total_variation_eq_sup_event_gap` 给等质量有限函数的事件变分式，`D5/S3/TotalVariation/DataProcessing.lean` 中 `total_variation_channel_le` 给随机通道收缩，`D5/S1/Scale/FibonacciErrorRatio.lean` 中 `fibonacci_golden_residual` 给相邻 Fibonacci 数的黄金残差。这些是所用既有输入；本节的两条最优性命题及条件量子界为 `repo-derived` 普通数学推导，不据此提出外部新颖性、Lean 准入或完整 Lean 认证主张。

## 追加锚（本行以下为增补区）

## 127. 固定尾零支撑下相干局部态的精确迹距离

固定整数 $n>K\ge0$，令 $\alpha=(\sqrt5-1)/2$、$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，并沿用从第 $0$ 位向右的前缀方向。记
$$
W_j=\{w\in\{0,1\}^j:w_iw_{i+1}=0\ \text{对所有 }0\le i<j-1\},
\qquad W_0=\{\varnothing\},
\qquad \mathcal K_n=(\mathbb C^2)^{\otimes n}.
$$
在完整 $n$ qubit 空间的计算基上，取未归一化向量及指定目标
$$
s_n=\sum_{u\in W_n}|u\rangle,
\qquad
t_n=\sum_{\substack{u\in W_n\\u_{n-1}=0}}|u\rangle,
\qquad
\rho_n=\alpha^{n+1}|s_n\rangle\langle s_n|
       +\alpha^{n+2}|t_n\rangle\langle t_n|.
$$
这正是 Q125.1 的相干局部极限；非法词方向上的行、列均为零。预算固定的是具体计算基支撑
$$
A=A_{K,n}=\{w0^{n-K}:w\in W_K\},
\qquad
P=P_{K,n}=\sum_{u\in A}|u\rangle\langle u|,
\qquad
\mathcal F_{K,n}=\{\sigma\ge0:\operatorname{Tr}\sigma=1,\ \sigma=P\sigma P\}.
$$
可行态允许混合及支撑内的任意相干。以
$$
d_{\rm tr}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^*X}
$$
采用半迹范数约定，字母 $D$ 只用于计数。以下简记
$$
D=F_{K+2},\qquad B=F_{n+1},\qquad C=F_n,\qquad b=B-D,
$$
$$
m=D\alpha^n,\qquad
\delta=\alpha^{2n+3}BC,\qquad
\eta=\alpha^{2n+3}bC,\qquad
c=1-m-\delta,
$$
并置
$$
|a\rangle=D^{-1/2}\sum_{u\in A}|u\rangle,
\qquad \tau_{K,n}=|a\rangle\langle a|.
$$

**命题 127.1（指定相干目标的尾零最优误差）。** 对所有整数 $n>K\ge0$，$\tau_{K,n}$ 达到
$$
e_{K,n}=\min_{\sigma\in\mathcal F_{K,n}}d_{\rm tr}(\rho_n,\sigma).
$$
精确值 $e_{K,n}$ 是三次方程
$$
x^3-cx-\eta=0
$$
的唯一严格正实根。边界为
$$
e_{K,K+1}=\alpha^{K+2}\sqrt{F_{K+1}F_{K+3}},
\qquad e_{0,1}=\sqrt2\,\alpha^2.
$$
若 $\mu_n(u)=\langle u|\rho_n|u\rangle$ 为计算基读数，在全部集中于 $A$ 的经典概率 $\nu$ 上取
$$
\operatorname{TV}(\nu,\mu_n)
=\frac12\sum_{u\in\{0,1\}^n}|\nu(u)-\mu_n(u)|,
$$
则有严格比较
$$
e_{K,n}>1-m
=\min_{\nu:\,\nu(A)=1}\operatorname{TV}(\nu,\mu_n).
$$
其中经典最小值由 $\tau_{K,n}$ 的对角分布达到。固定 $K$ 后，同一个有限均匀态
$$
|\Psi_K\rangle=D^{-1/2}\sum_{w\in W_K}|w\rangle
$$
接上全零尾部，给出所有 $n>K$ 的上述量子最优者，因为
$$
\tau_{K,n}=|\Psi_K\rangle\langle\Psi_K|
\otimes|0^{n-K}\rangle\langle0^{n-K}|.
$$
$K=0$ 时 $|\Psi_0\rangle$ 按空张量积的单位向量理解。

证明。先核对计数与归一化。长度 $n\ge1$ 的合法词中，末位零、末位一的数量分别是 $B=F_{n+1}$、$C=F_n$：末位零可由任意长度 $n-1$ 合法词接零得到；末位一在 $n\ge2$ 时由长度 $n-2$ 合法词接 $01$ 得到，$n=1$ 时两类各有一词。连同 $|W_0|=1,|W_1|=2$，这给 $|W_j|=F_{j+2}$。补零把 $W_K$ 单射到末位零的一类，故 $|A|=D\le B$、$b\ge0$，且 $C,D>0$。Fibonacci 数从下标 $2$ 起严格递增，所以在本参数域内 $b=0$ 当且仅当 $n=K+1$。

由 $\alpha+\alpha^2=1$，$\rho_n$ 的合法对角元为
$$
\mu_n(u)=
\begin{cases}
\alpha^n,&u_{n-1}=0,\\
\alpha^{n+1},&u_{n-1}=1.
\end{cases}
$$
非法词的对角元为零。恒等式
$$
\alpha^n(F_{n+1}+\alpha F_n)=1
$$
在 $n=1$ 时是 $\alpha(1+\alpha)=1$；若它在 $n$ 成立，则
$$
\alpha^{n+1}(F_{n+2}+\alpha F_{n+1})
=\alpha^n\bigl(\alpha(1+\alpha)F_{n+1}+\alpha F_n\bigr)
=\alpha^n(F_{n+1}+\alpha F_n)=1.
$$
因此所列正算子 $\rho_n$ 的迹为一，而且
$$
\operatorname{Tr}(P\rho_n)=m,
\qquad 0<m\le B\alpha^n=1-C\alpha^{n+1}<1.
$$

现在证明最优性。在本证明内简写 $\tau=\tau_{K,n}$。由于 $A$ 的全部词都以零结尾，
$$
Ps_n=Pt_n=\sqrt D\,|a\rangle.
$$
$Q=P-\tau$ 是正交投影，$R=I-Q$ 也是正交投影，且 $Qs_n=Qt_n=0$。取 $\operatorname{ran}Q$ 的正交标准基 $(q_j)_{j=1}^{D-1}$，以 $R$ 及 $|a\rangle\langle q_j|$ 为 Kraus 算子。它们满足
$$
R^*R+\sum_{j=1}^{D-1}
\bigl(|a\rangle\langle q_j|\bigr)^*
\bigl(|a\rangle\langle q_j|\bigr)
=R+Q=I,
$$
故
$$
\Phi(X)=RXR+\operatorname{Tr}(QX)\tau
$$
是完全正保迹通道。$Q\rho_n=\rho_nQ=0$ 使 $\Phi(\rho_n)=\rho_n$。另一方面，$RP=PR=\tau$，所以每个 $\sigma\in\mathcal F_{K,n}$ 都满足
$$
R\sigma R=\langle a|\sigma|a\rangle\tau,
\qquad
\operatorname{Tr}(Q\sigma)=1-\langle a|\sigma|a\rangle,
\qquad \Phi(\sigma)=\tau.
$$
这里 $D=1$ 时 $Q=0$，Kraus 求和为空，等式仍成立。由迹距离在通道下的收缩性，
$$
d_{\rm tr}(\rho_n,\tau)
=d_{\rm tr}(\Phi(\rho_n),\Phi(\sigma))
\le d_{\rm tr}(\rho_n,\sigma).
$$
收缩性也可直接从正负谱部分核对：对 Hermitian 算子 $Y=Y_+-Y_-$，正性、保迹性与三角不等式给
$$
\|\Phi(Y)\|_1
\le\operatorname{Tr}\Phi(Y_+)+\operatorname{Tr}\Phi(Y_-)
=\operatorname{Tr}Y_++\operatorname{Tr}Y_-=\|Y\|_1.
$$
$\tau$ 本身可行，故最小值确由它达到。$\Phi$ 在这里是比较态的数学通道，不以它属于某个物理可实现的制备资源集为前提。

为求这个最小值，置 $H=\rho_n-\tau$。将合法词分成三个互不相交的词组：$A$、末位零但不在 $A$ 的词、末位一的词。$H$ 在各非空词组的均匀向量张成空间之外为零。由于 $C>0$，始终定义
$$
|v\rangle=C^{-1/2}\sum_{\substack{u\in W_n\\u_{n-1}=1}}|u\rangle.
$$
当 $b>0$ 时再定义
$$
|z\rangle=b^{-1/2}\sum_{\substack{u\in W_n\setminus A\\u_{n-1}=0}}|u\rangle.
$$
此时 $(a,z,v)$ 是正交标准组，其上的实际三维压缩为
$$
H_3=\alpha^n
\begin{pmatrix}
D&\sqrt{Db}&\alpha\sqrt{DC}\\
\sqrt{Db}&b&\alpha\sqrt{bC}\\
\alpha\sqrt{DC}&\alpha\sqrt{bC}&\alpha C
\end{pmatrix}
-\operatorname{diag}(1,0,0).
$$
当 $b=0$ 时不定义空词组的归一化向量 $z$，只用 $(a,v)$，实际二维压缩为
$$
H_2=\alpha^n
\begin{pmatrix}
D&\alpha\sqrt{DC}\\
\alpha\sqrt{DC}&\alpha C
\end{pmatrix}
-\operatorname{diag}(1,0).
$$
在两种情形下都有 $\operatorname{Tr}H=0$。对 $y\perp a$，
$$
\langle y|H|y\rangle=\langle y|\rho_n|y\rangle\ge0,
\qquad
\langle a|H|a\rangle=m-1<0.
$$
若负谱子空间至少二维，它与 $a^\perp$ 有非零交，便同时给出严格负和非负的二次型值，矛盾。因此 $H$ 恰有一个负特征值，记为 $-e$，其中 $e>0$。迹为零使正特征值之和为 $e$，从而 $\|H\|_1/2=e=e_{K,n}$。

接着计算不变量。$\rho_n$ 在整个末位零类与末位一类的两个归一化均匀向量上具有矩阵
$$
\alpha^n
\begin{pmatrix}
B&\alpha\sqrt{BC}\\
\alpha\sqrt{BC}&\alpha C
\end{pmatrix}.
$$
其行列式为
$$
\alpha^{2n}(\alpha-\alpha^2)BC
=\alpha^{2n+3}BC=\delta>0,
$$
其中 $\alpha-\alpha^2=\alpha^3$。这个二维矩阵之外 $\rho_n$ 为零，且其迹为一，所以
$$
\operatorname{Tr}\rho_n^2=1-2\delta,
\qquad
\operatorname{Tr}H^2
=\operatorname{Tr}\rho_n^2-2\langle a|\rho_n|a\rangle+1
=2(1-m-\delta)=2c.
$$
$H\ne0$ 为 Hermitian 算子，故 $c>0$。

当 $b>0$ 时，$\rho_n$ 的三维压缩秩为二、行列式为零。将它的第一对角元减去一，行列式恰减去对应的余子式，得到
$$
\det H_3
=-\alpha^{2n}(\alpha-\alpha^2)bC
=-\eta.
$$
迹零三维矩阵的二次基本对称式为 $-\operatorname{Tr}H_3^2/2=-c$，于是
$$
\det(\lambda I_3-H_3)=\lambda^3-c\lambda+\eta.
$$
代入唯一负特征值 $\lambda=-e$ 得 $e^3-ce-\eta=0$。反过来，每个严格正实根 $x$ 都使 $-x$ 成为 $H_3$ 的负特征值，故严格正实根唯一。

当 $b=0$ 时使用实际的 $H_2$：它的迹为零、平方迹为 $2c$，所以
$$
\det H_2=-c,\qquad
\operatorname{spec}(H_2)=\{-\sqrt c,\sqrt c\}.
$$
此时 $\eta=0$，三次方程是 $x(x^2-c)=0$，唯一严格正实根仍是 $e=\sqrt c$；二维行列式是 $-c$，不是三维补零矩阵的零行列式。

在边界 $n=K+1$，有 $D=B$，归一化恒等式进一步把实际二维矩阵写成
$$
H_2=\alpha^{n+1}
\begin{pmatrix}
-C&\sqrt{DC}\\
\sqrt{DC}&C
\end{pmatrix}.
$$
因此
$$
e_{K,K+1}^2=\alpha^{2n+2}C(C+D)
=\alpha^{2K+4}F_{K+1}F_{K+3},
$$
由 $e_{K,K+1}>0$ 即得所列平方根。$K=0$ 时 $D=1$，可行支撑为 $|0^n\rangle$ 张成的一维空间，上述通道与谱论证对每个 $n>0$ 仍适用；其中 $n=1$ 给 $C=D=1$，故 $e_{0,1}=\sqrt2\,\alpha^2$。

最后核对经典最优值与严格差距。显式对角律在 $A$ 上每词赋质量 $\alpha^n$，总质量为 $m$。对任意 $\nu(A)=1$，总变差的事件界给
$$
\operatorname{TV}(\nu,\mu_n)\ge|\nu(A)-\mu_n(A)|=1-m.
$$
该事件界直接来自差函数总和为零，其正部、负部之和各等于总变差。令 $\nu$ 在 $A$ 上均匀，则 $m<1$ 给 $1/D>\alpha^n$，从而 $A$ 内外的绝对差之和分别为
$$
\sum_{u\in A}\left(\frac1D-\alpha^n\right)=1-m,
\qquad
\sum_{u\notin A}\mu_n(u)=1-m.
$$
半和恰为 $1-m$，这既证明经典最优值，也说明 $\tau$ 的对角分布达到它。

量子严格性则来自 $H$ 的非对角作用。无论 $b$ 是否为零，末位一类的均匀向量 $v$ 都已定义且与 $a$ 正交，并满足
$$
\langle v|H|a\rangle=\alpha^{n+1}\sqrt{DC}>0.
$$
因此 $a$ 不是 $H$ 的特征向量。Rayleigh 商达到最小特征值当且仅当向量属于相应特征空间，故
$$
-e_{K,n}=\lambda_{\min}(H)
<\langle a|H|a\rangle=m-1,
$$
即 $e_{K,n}>1-m$。张量积公式直接由 $A$ 的定义得到，证明固定的 $|\Psi_K\rangle$ 接全零尾部同时给出每个 $n>K$ 的最优者。证毕。

这里的差距比较完整 POVM 所能取得的态区分总变差与只读计算基的总变差。它依赖所列相干目标及固定尾零支撑，不是对所有目标或每种受限测量的结论，也不是过程的 diamond 范数界。它不表示最优值依赖计算基的相位角：任意计算基对角酉算子 $U$ 都与 $P$ 对易，共轭使 $\mathcal F_{K,n}$ 双射到自身，迹范数的酉不变性便给
$$
\min_{\sigma\in\mathcal F_{K,n}}d_{\rm tr}(U\rho_nU^*,\sigma)=e_{K,n}.
$$
固定支撑也不能换成仅有维数的预算；若 $K\ge1$，则 $D\ge2$，而上面的正二维行列式给 $\operatorname{rank}\rho_n=2$，允许任选 $D$ 维子空间就能令其包含 $\operatorname{ran}\rho_n$，以 $\sigma=\rho_n$ 达到零误差。

本节的 Q109、Q125.1、Q125.3 取仓库提交 `7af72f9910546ca2aa0bfa3a6bbaed4d8a393efb`；Q126.2 的固定尾零载体及经典窗口比较取提交 `dc4af5d3b06e66c8be5fe63ffd5fc1ace63e2c7e`，这里已从显式对角律独立证明所需经典最优值。迹距离的数据处理是既有标准结论，前一提交的 `D5/S3/Quantum/Foundation/FiniteTraceDistance.lean` 中 `traceDistance_contract` 对应所用收缩性，其范围不包含本节完整最优化。命题 127.1 为 `repo-derived` 普通数学推导，不提出外部新颖性或完整 Lean 认证主张。

## 追加锚（本行以下为增补区）

## 128. 尾零量子最优者的唯一性与短窗口保真的代价

固定整数 $n>K\ge0$，取 $\alpha=(\sqrt5-1)/2$、$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$。窗口从第 $0$ 位向右延伸，记
$$
W_j=\{w\in\{0,1\}^j:w_iw_{i+1}=0\ \text{对所有 }0\le i<j-1\},
\qquad W_0=\{\varnothing\},
\qquad D_K=|W_K|=F_{K+2}.
$$
完整载体与其中的合法词子空间分别为
$$
\mathcal K_j=(\mathbb C^2)^{\otimes j},
\qquad
\mathcal L_j=\operatorname{span}\{|w\rangle:w\in W_j\}\subseteq\mathcal K_j,
\qquad \mathcal K_0=\mathcal L_0=\mathbb C.
$$
目标是 Q125.1、Q127.1 所指定的相干态族：$\rho_0=(1)$，而对 $j\ge1$，
$$
s_j=\sum_{w\in W_j}|w\rangle,
\qquad
t_j=\sum_{\substack{w\in W_j\\w_{j-1}=0}}|w\rangle,
\qquad
\rho_j=\alpha^{j+1}|s_j\rangle\langle s_j|
       +\alpha^{j+2}|t_j\rangle\langle t_j|.
$$
这里 $s_j,t_j$ 未归一化，$\rho_j$ 是完整 $\mathcal K_j$ 上的密度算子，非法词方向上的行、列为零。补零等距映射及可行域为
$$
V=V_{K,n}:\mathcal L_K\longrightarrow\mathcal K_n,
\qquad V|w\rangle=|w0^{n-K}\rangle,
\qquad P=VV^*,
$$
$$
\mathcal F_{K,n}
=\{\sigma\text{ 为 }\mathcal K_n\text{ 上的密度算子}:\sigma=P\sigma P\}.
$$
因此固定的是 $\{w0^{n-K}:w\in W_K\}$ 的具体尾零支撑，允许该支撑内的混合及任意相干。置
$$
|\Psi_K\rangle=D_K^{-1/2}\sum_{w\in W_K}|w\rangle,
\qquad |a\rangle=V|\Psi_K\rangle,
\qquad \tau=\tau_{K,n}=|a\rangle\langle a|,
\qquad Q=P-\tau.
$$
采用半迹范数 $d_{\rm tr}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$。Q127.1 的普通证明给出
$$
e=e_{K,n}=d_{\rm tr}(\rho_n,\tau)
=\min_{\sigma\in\mathcal F_{K,n}}d_{\rm tr}(\rho_n,\sigma)
>1-D_K\alpha^n>0,
$$
并给出 $H=\rho_n-\tau$ 的负谱子空间恰为一维。取其中单位向量 $\zeta$，使 $H\zeta=-e\zeta$，定义
$$
r=r_{K,n}=\|P\zeta\|^2.
$$
谱投影 $|\zeta\rangle\langle\zeta|$ 及 $r$ 均与 $\zeta$ 的相位选择无关。对 $K\ge1$ 再记
$$
B_K=F_{K+1},\qquad C_K=F_K,\qquad D_K=B_K+C_K,
\qquad \kappa_K=\alpha^{K+2}\frac{B_KC_K}{D_K},
$$
并单独定义 $\kappa_0=0$；空词不使用末位分类。

**命题 128.1（投影余量、唯一最优者与短窗口保真冲突）。** 对所有上述整数 $n>K\ge0$，有 $0<r_{K,n}<1$。每个 $\sigma\in\mathcal F_{K,n}$ 若记 $p=\langle a|\sigma|a\rangle$，则
$$
d_{\rm tr}(\rho_n,\sigma)
\ge e_{K,n}+(1-r_{K,n})(1-p).
$$
因而 $\tau_{K,n}$ 是该可行域内唯一的迹距离最优者。

每个可行态唯一写成 $\sigma=V\theta V^*$，其中 $\theta$ 是 $\mathcal L_K$ 上的密度算子；把 $\theta$ 在非法词方向延零，视为完整 $\mathcal K_K$ 上的算子，则其完整张量积偏迹为
$$
\operatorname{Tr}_{\{K,\ldots,n-1\}}\sigma=\theta.
$$
所以精确保留前 $K$ 位目标 $\rho_K$ 的唯一可行延拓是
$$
\sigma^{\rm cut}_{K,n}=V\rho_KV^*
=\rho_K\otimes|0^{n-K}\rangle\langle0^{n-K}|.
$$
乘积 $V\rho_KV^*$ 中的 $\rho_K$ 取其在 $\mathcal L_K$ 上的限制，右端及偏迹仍在完整 qubit 空间中解释。此延拓也精确保留所有 $0\le j\le K$ 的目标前缀 $\rho_j$。令
$$
p_K=\langle\Psi_K|\rho_K|\Psi_K\rangle.
$$
对 $K\ge1$，有
$$
p_K=\alpha^{K+1}D_K+\alpha^{K+2}\frac{B_K^2}{D_K},
\qquad 1-p_K=\kappa_K>0,
$$
以及严格的长窗口额外误差
$$
g_{K,n}:=d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})-e_{K,n}
\ge(1-r_{K,n})\kappa_K>0.
$$
对 $K=0$，$p_0=1$，唯一可行态就是 $\tau_{0,n}=\sigma^{\rm cut}_{0,n}$，没有这种冲突。

更一般地，任取非负容差 $\varepsilon_{\rm short},\varepsilon_{\rm large}$。若某个可行态及其短窗口 $\theta$ 同时满足
$$
d_{\rm tr}(\theta,\rho_K)\le\varepsilon_{\rm short},
\qquad
d_{\rm tr}(\rho_n,\sigma)\le e_{K,n}+\varepsilon_{\rm large},
$$
则必有
$$
\varepsilon_{\rm large}
\ge(1-r_{K,n})\max\{\kappa_K-\varepsilon_{\rm short},0\}.
$$
这只是必要条件，一般并不充分，也不是可达误差对的精确 Pareto 边界。

对每个固定的 $K\ge1$，各有限 $n>K$ 的冲突严格为正，但实际差距满足
$$
0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n\longrightarrow0
\qquad(n\to\infty).
$$
因而不存在对所有 $n>K$ 统一成立的正差距下界。投影余量的系数也退化：
$$
e_{K,n}\le r_{K,n}<1,
\qquad
0<1-r_{K,n}\le1-e_{K,n}<D_K\alpha^n\longrightarrow0.
$$

证明。先构造实际用于余量界的测量。由于支撑中的每个词均以零结尾，
$$
Ps_n=Pt_n=\sqrt{D_K}\,|a\rangle.
$$
$Q=P-\tau$ 是正交投影，且 $Qs_n=Qt_n=0$，故 $Q\rho_n=\rho_nQ=0$ 及 $QH=HQ=0$。由
$$
0=QH\zeta=-eQ\zeta
$$
和 $e>0$ 得 $Q\zeta=0$。于是
$$
P\zeta=\tau\zeta=\langle a|\zeta\rangle a,
\qquad r=|\langle a|\zeta\rangle|^2.
$$
若 $r=0$，则
$$
-e=\langle\zeta|H|\zeta\rangle
=\langle\zeta|\rho_n|\zeta\rangle\ge0,
$$
矛盾。若 $r=1$，则单位向量 $\zeta$ 属于 $\operatorname{ran}P$，结合 $Q\zeta=0$ 可知它与 $a$ 平行，故 $a$ 必为 $H$ 的特征向量。然而 Q127.1 中始终非空的末位一词组给单位向量
$$
|v\rangle=F_n^{-1/2}\sum_{\substack{u\in W_n\\u_{n-1}=1}}|u\rangle,
\qquad v\perp\operatorname{ran}P,
$$
并且由显式目标直接有
$$
\langle v|H|a\rangle
=\alpha^{n+1}\sqrt{D_KF_n}>0.
$$
这与 $a$ 为特征向量矛盾，故 $0<r<1$。这里 $F_n>0$ 对每个 $n>K\ge0$ 成立，$n=K+1$ 也无需引入任何空词组的归一化向量。

由 $Q\zeta=0$，两个正交投影 $|\zeta\rangle\langle\zeta|$ 与 $Q$ 的乘积在两个方向上均为零，因此
$$
E=|\zeta\rangle\langle\zeta|+Q,
\qquad E^*=E,\qquad E^2=E,\qquad 0\le E\le I.
$$
它与 $I-E$ 构成二元投影测量。对任意可行 $\sigma$，支撑条件和 $P\zeta=\langle a|\zeta\rangle a$ 给
$$
\operatorname{Tr}(E\sigma)
=\langle\zeta|\sigma|\zeta\rangle+\operatorname{Tr}(Q\sigma)
=rp+1-p.
$$
另一方面，$Q\rho_n=0$ 及 $H\zeta=-e\zeta$ 给
$$
\operatorname{Tr}(E\rho_n)
=\langle\zeta|\rho_n|\zeta\rangle
=\langle\zeta|(H+\tau)|\zeta\rangle=r-e.
$$
在本次应用中，将迹零 Hermitian 算子 $Y=\sigma-\rho_n$ 写成正负谱部分 $Y_+-Y_-$；两部分的迹都是 $\|Y\|_1/2$，且 $0\le\operatorname{Tr}(EY_\pm)\le\operatorname{Tr}Y_\pm$，所以
$$
|\operatorname{Tr}(EY)|\le\tfrac12\|Y\|_1=d_{\rm tr}(\rho_n,\sigma).
$$
两个期望相减恰为 $e+(1-r)(1-p)>0$，这便证明投影余量界。

Q127.1 已给 $\tau$ 达到最小值 $e$。若 $\sigma$ 也达到该值，$1-r>0$ 与 $0\le p\le1$ 迫使 $p=1$。此时
$$
\operatorname{Tr}\bigl((I-\tau)\sigma(I-\tau)\bigr)=1-p=0.
$$
括号中的算子为正，迹零使它为零，消去了 $a^\perp$ 内的全部方向。对任意 $x\perp a$，正算子的 Cauchy–Schwarz 不等式又给
$$
|\langle x|\sigma|a\rangle|^2
\le\langle x|\sigma|x\rangle\langle a|\sigma|a\rangle=0,
$$
其共轭交叉项也为零。因此 $\sigma=p\tau=\tau$，唯一性成立；这里并未使用迹范数的严格凸性。

下面核对短窗口及其唯一延拓。$V^*V=I_{\mathcal L_K}$，故可行态给出密度算子 $\theta=V^*\sigma V$，且 $V\theta V^*=P\sigma P=\sigma$；反向乘以 $V^*,V$ 也证明 $\theta$ 唯一。按合法词基展开，
$$
V\theta V^*
=\sum_{w,u\in W_K}\theta_{wu}
  |w\rangle\langle u|\otimes|0^{n-K}\rangle\langle0^{n-K}|.
$$
尾部秩一投影的迹为一，故在完整张量积上取尾部偏迹正好得到延零后的 $\theta$，并非在较小的合法空间上另定义偏迹。特别地，短窗口等于 $\rho_K$ 当且仅当 $\theta=\rho_K$，得到所列唯一的 $\sigma^{\rm cut}_{K,n}$。Q125.1 的完整偏迹相容性逐层迭代，使该态的前 $j$ 位等于 $\rho_j$，$1\le j\le K$；空窗口为标量迹一，即 $\rho_0$。

对 $K\ge1$，末位零、末位一的词数分别为 $B_K,C_K$，两者均正。由未归一化向量的定义，
$$
\langle\Psi_K|s_K\rangle=\sqrt{D_K},
\qquad
\langle\Psi_K|t_K\rangle=\frac{B_K}{\sqrt{D_K}},
$$
从而得到陈述中的 $p_K$。归一化在同一记号下为
$$
1=\operatorname{Tr}\rho_K
=\alpha^{K+1}D_K+\alpha^{K+2}B_K.
$$
两式相减，利用 $D_K-B_K=C_K$，即得
$$
1-p_K
=\alpha^{K+2}\left(B_K-\frac{B_K^2}{D_K}\right)
=\alpha^{K+2}\frac{B_KC_K}{D_K}=\kappa_K>0.
$$
$\sigma^{\rm cut}_{K,n}$ 的 $p$ 正是 $p_K$，代入余量界给严格额外误差。$K=0$ 时 $\mathcal L_0$ 一维，唯一密度为 $\rho_0=(1)$，$\Psi_0$ 是单位空张量；因此 $p_0=1$、$\kappa_0=0$ 及全部无冲突结论直接成立。

对容差结论，$\sigma=V\theta V^*$ 给 $p=\langle\Psi_K|\theta|\Psi_K\rangle$。对完整 $\mathcal K_K$ 上的迹零算子 $\theta-\rho_K$ 应用刚才的正负部分论证，并取投影 $|\Psi_K\rangle\langle\Psi_K|$，得到
$$
|p-p_K|\le d_{\rm tr}(\theta,\rho_K)\le\varepsilon_{\rm short}.
$$
由于 $p\le1$，这蕴含
$$
1-p\ge\max\{\kappa_K-\varepsilon_{\rm short},0\}.
$$
与长窗口余量界和假设的长窗口上界合并，便是所列必要条件，$K=0$ 时右端为零。

为验证它一般不充分，取 $K=1$、任意 $n>1$，以及 $\varepsilon_{\rm large}=0$、$\varepsilon_{\rm short}=\kappa_1$。这对预算满足所列必要不等式。若有可行态满足两项预算，长窗口预算及唯一性却迫使它为 $\tau_{1,n}$，短窗口只能是 $|\Psi_1\rangle\langle\Psi_1|$。此时 $\kappa_1=\alpha^3/2=\alpha-1/2>0$，由 Q125.1 的一位矩阵得到
$$
|\Psi_1\rangle\langle\Psi_1|-\rho_1
=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}
 -\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}
=\kappa_1\begin{pmatrix}-1&1\\1&1\end{pmatrix}.
$$
这个迹零矩阵的特征值为 $\pm\sqrt2\,\kappa_1$，故短窗口迹距离是 $\sqrt2\,\kappa_1>\varepsilon_{\rm short}$，矛盾。这给出了必要条件与可达性的严格区别。

最后，任意两个密度算子的迹距离至多为一，所以对 $K\ge1$，已证的严格性与 Q127.1 的 $e_{K,n}>1-D_K\alpha^n$ 共同给
$$
0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n.
$$
固定 $K$ 时右端趋零，夹逼的是实际差距本身。又因 $E$ 与 $\rho_n$ 均为正算子，
$$
0\le\operatorname{Tr}(E\rho_n)=r_{K,n}-e_{K,n},
$$
故 $r_{K,n}\ge e_{K,n}$，同时 $r_{K,n}<1$，得到所列系数退化界。证毕。

本命题刻画指定相干目标与准确尾零支撑下的静态窗口相容性。Q126.2 中经典截断概率与均匀概率均优化每个固定深窗口的总变差；这里的唯一量子最优者则在 $K\ge1$ 时不能同时精确保留 $\rho_K$。投影 $E$ 是完整 $n$ 窗口上允许任意联合测量时的数学效应，未附加局域性、实施成本或可访问性条件。所证范围不包含时间演化、动态预测、任意维数预算、一般目标态或形而上必然性。

本节的 Q125.1、Q126.2、Q127.1 均取[仓库不可变提交 `ac40238901406b5bba4518e306d5bb2da9fe8ba1` 的量子卷](https://github.com/the-omega-institute/trureturing/blob/ac40238901406b5bba4518e306d5bb2da9fe8ba1/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md)，依其显式普通证明使用。测量期望受迹距离控制属于 Helstrom 变分框架；Q127.1 所引同仓 `D5/S3/Quantum/Foundation/FiniteTraceDistance.lean` 提供既有有限迹距离数据处理，其覆盖范围不是本节的完整唯一性与保真冲突。命题 128.1 是 `repo-derived` 普通数学推导，不主张外部新颖性或 Lean 认证。

## 追加锚（本行以下为增补区）

## 129. 移动边界下的非消失尾零代价

取 $\alpha=(\sqrt5-1)/2$、$F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，在完整 qubit 载体中记
$$
\mathcal K_j=(\mathbb C^2)^{\otimes j},
\qquad
W_j=\{w\in\{0,1\}^j:w_iw_{i+1}=0\ \text{对所有 }0\le i<j-1\},
\qquad W_0=\{\varnothing\},
$$
$$
\mathcal L_j=\operatorname{span}\{|w\rangle:w\in W_j\}\subseteq\mathcal K_j,
\qquad \mathcal K_0=\mathcal L_0=\mathbb C.
$$
目标取命题 125.1 的指定密度算子 $\rho_0=(1)$ 及
$$
\rho_j=\alpha^{j+1}|s_j\rangle\langle s_j|
       +\alpha^{j+2}|t_j\rangle\langle t_j|\quad(j\ge1),
\qquad
|s_j\rangle=\sum_{w\in W_j}|w\rangle,
\qquad
|t_j\rangle=\sum_{\substack{w\in W_j\\w_{j-1}=0}}|w\rangle.
$$
对每个整数 $K\ge0$ 取 $n=K+1$，置
$$
C=F_{K+1},\qquad D=F_{K+2},\qquad s=\alpha^{K+2},
$$
$$
A=\{w0:w\in W_K\},
\qquad P=\sum_{u\in A}|u\rangle\langle u|,
\qquad
\mathcal F_{K,K+1}=\{\sigma\ge0:\operatorname{Tr}\sigma=1,\ \sigma=P\sigma P\},
$$
其中 $\sigma$ 作用于完整 $\mathcal K_{K+1}$。定义精确尾零等距映射与向量
$$
V:\mathcal L_K\longrightarrow\mathcal K_{K+1},
\qquad V|w\rangle=|w0\rangle,
\qquad
|\Psi_K\rangle=D^{-1/2}\sum_{w\in W_K}|w\rangle,
$$
$$
|a\rangle=V|\Psi_K\rangle,
\qquad \tau=|a\rangle\langle a|,
\qquad
|v\rangle=C^{-1/2}\sum_{\substack{u\in W_{K+1}\\u_K=1}}|u\rangle,
\qquad \mathcal M=\operatorname{span}\{a,v\}.
$$
采用半迹范数约定，并以命题 127.1 的可行域定义最优误差：
$$
d_{\rm tr}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
\qquad \|X\|_1=\operatorname{Tr}\sqrt{X^*X},
\qquad
e_{K,K+1}=\min_{\sigma\in\mathcal F_{K,K+1}}d_{\rm tr}(\rho_{K+1},\sigma).
$$
记 $H=\rho_{K+1}-\tau$，令 $\Pi_-$ 为 $H$ 在完整载体上的负谱投影，定义
$$
r_{K,K+1}=\langle a|\Pi_-|a\rangle,
\qquad
\sigma^{\rm cut}_{K,K+1}=V(\rho_K|_{\mathcal L_K})V^*,
\qquad
g_K=d_{\rm tr}(\rho_{K+1},\sigma^{\rm cut}_{K,K+1})-e_{K,K+1}.
$$
这里乘积中的 $\rho_K$ 识别为它在合法支撑 $\mathcal L_K$ 上的限制；$\rho_K$ 本身仍指完整 $\mathcal K_K$ 上、在非法词方向延零的算子。对 $K\ge1$ 沿用命题 128.1 的记号
$$
\kappa_K=\alpha^{K+2}\frac{F_{K+1}F_K}{F_{K+2}}.
$$

**命题 129.1（移动边界的非消失尾零代价）。** 对上述指定目标与具体尾零支撑，对所有整数 $K\ge0$，在完整载体上有
$$
\sigma^{\rm cut}_{K,K+1}=\rho_K\otimes|0\rangle\langle0|,
\qquad
e_{K,K+1}=d_{\rm tr}(\rho_{K+1},\tau)=s\sqrt{C(C+D)}>0.
$$
$H$ 在正交标准基 $(a,v)$ 上的矩阵及其平方为
$$
H_2=s\begin{pmatrix}-C&\sqrt{CD}\\\sqrt{CD}&C\end{pmatrix},
\qquad H_2^2=e_{K,K+1}^2I_2.
$$
$H$ 在 $\mathcal M^\perp$ 上为零，其完整负谱投影为二维负谱投影的延零：
$$
\Pi_{-,2}=\frac{I_2-H_2/e_{K,K+1}}2,
\qquad \Pi_-=\Pi_{-,2}\oplus0_{\mathcal M^\perp}.
$$
当 $K\ge1$ 时，$\dim\ker H=2^{K+1}-2>0$，而 $(I_{\rm full}-H/e_{K,K+1})/2$ 在此核上作用为单位算子的一半，故不是负谱投影。当 $K=0$ 时，$\mathcal K_1=\mathcal M$，该完整单位算子表达式成立。对所有 $K\ge0$，重叠量为
$$
r_{K,K+1}=\frac{1+\sqrt{F_{K+1}/F_{K+3}}}{2}.
$$
取 $\kappa_0=0$，则 $g_0=0$；对 $K\ge1$ 有
$$
g_K\ge(1-r_{K,K+1})\kappa_K>0.
$$
沿 $n=K+1$ 令 $K\to\infty$，有三个极限
$$
e_{K,K+1}\longrightarrow\frac1{\sqrt5},
\qquad
1-r_{K,K+1}\longrightarrow\frac{1-\alpha}{2}=\frac{\alpha^2}{2},
\qquad
\kappa_K\longrightarrow\frac{\alpha^3}{\sqrt5},
$$
以及
$$
\liminf_{K\to\infty}g_K\ge L:=\frac{\alpha^5}{2\sqrt5}>0.
$$
另一方面，固定任意整数 $K\ge1$，令 $n>K$ 增大，并沿用命题 127.1、128.1 在具体支撑 $A_{K,n}=\{w0^{n-K}:w\in W_K\}$ 上的最优误差 $e_{K,n}$，记
$$
D_K=F_{K+2},
\qquad
\sigma^{\rm cut}_{K,n}=\rho_K\otimes|0^{n-K}\rangle\langle0^{n-K}|,
\qquad
g_{K,n}=d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})-e_{K,n}.
$$
则
$$
0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n,
\qquad
g_{K,n}\longrightarrow0,
\qquad
e_{K,n}\longrightarrow1,
\qquad
d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})\longrightarrow1.
$$

证明。按合法词基展开 $\rho_K|_{\mathcal L_K}$，每个矩阵单位 $|w\rangle\langle u|$ 经 $V$ 变为 $|w0\rangle\langle u0|$，即 $|w\rangle\langle u|\otimes|0\rangle\langle0|$。在非法词方向延零，得到陈述中的完整载体等式。

命题 127.1 的计数给 $|A|=D$、末位一合法词数为 $C$，且 $C,D>0$。当 $n=K+1$ 时，$A$ 恰为全部末位零合法词，故 $(a,v)$ 正交归一，且
$$
|s_{K+1}\rangle=\sqrt D\,|a\rangle+\sqrt C\,|v\rangle,
\qquad |t_{K+1}\rangle=\sqrt D\,|a\rangle.
$$
因此 $H$ 在 $\mathcal M^\perp$ 上为零。将这两式代入目标公式，并用命题 127.1 的归一化恒等式 $\alpha^{K+1}(D+\alpha C)=1$，即得所列 $H_2$。直接相乘，
$$
H_2^2=s^2
\begin{pmatrix}C^2+CD&0\\0&CD+C^2\end{pmatrix}
=s^2C(C+D)I_2.
$$
$H_2$ 的迹为零，其特征值为 $\pm s\sqrt{C(C+D)}$。命题 127.1 给 $\tau$ 达到可行域上的最小值，半迹范数遂给 $e_{K,K+1}=s\sqrt{C(C+D)}>0$。两特征值非零，故 $\ker H=\mathcal M^\perp$。有限维谱分解给 $\Pi_{-,2}=(I_2-H_2/e_{K,K+1})/2$，在正交补上延零才是完整负谱投影。$K\ge1$ 时正交补维数 $2^{K+1}-2>0$，完整单位算子表达式在该补空间上为一半；$K=0$ 时完整空间只有两维、正交补为零，因而该表达式有效。

负谱为一维，取其单位向量 $\zeta$。由于 $Pa=a$、$Pv=0$ 且 $\zeta\in\mathcal M$，这里的 $r_{K,K+1}$ 与命题 128.1 的 $\|P\zeta\|^2=|\langle a|\zeta\rangle|^2$ 相同。二维投影的第一个对角元为
$$
r_{K,K+1}=\langle a|\Pi_-|a\rangle
=\frac12\left(1+\frac{sC}{e_{K,K+1}}\right)
=\frac12\left(1+\sqrt{\frac{C}{C+D}}\right).
$$
用 $C+D=F_{K+3}$ 即得对所有 $K\ge0$ 的重叠公式，且 $0<r_{K,K+1}<1$。

令 $h_j=\alpha^jF_j$。命题 125.1 所用 Binet 公式在本参数下给精确残差
$$
h_j=\frac{1-(-\alpha^2)^j}{\sqrt5},
\qquad h_j\longrightarrow\frac1{\sqrt5},
$$
因为 $0<\alpha<1$。边界误差、重叠比值和 $\kappa_K$ 满足三个缩放恒等式：
$$
e_{K,K+1}^2=\alpha^{2K+4}F_{K+1}F_{K+3}=h_{K+1}h_{K+3},
$$
$$
\frac{F_{K+1}}{F_{K+3}}=\alpha^2\frac{h_{K+1}}{h_{K+3}},
$$
$$
\kappa_K=\alpha^{K+2}\frac{F_{K+1}F_K}{F_{K+2}}
=\alpha^3\frac{h_{K+1}h_K}{h_{K+2}}.
$$
最后一式的指数抵消为 $K+2-(K+1)-K+(K+2)=3$；它在 $K=0$ 时也因 $F_0=h_0=0$ 与定义 $\kappa_0=0$ 一致。各分母的极限严格为正，取正平方根、商及乘积的极限，结合 $1-\alpha=\alpha^2$，得到陈述中的三个极限。

命题 128.1 对此 cut 态给 $1-\langle a|\sigma^{\rm cut}_{K,K+1}|a\rangle=\kappa_K$，并由其投影余量界得到
$$
g_K\ge(1-r_{K,K+1})\kappa_K>0\qquad(K\ge1).
$$
因此
$$
\liminf_{K\to\infty}g_K
\ge\lim_{K\to\infty}(1-r_{K,K+1})\kappa_K
=\frac{\alpha^2}{2}\frac{\alpha^3}{\sqrt5}
=\frac{\alpha^5}{2\sqrt5}>0.
$$
$K=0$ 时，$\rho_0=(1)$ 且 $\sigma^{\rm cut}_{0,1}=\tau=|0\rangle\langle0|$，故 $g_0=0$；改变这一有限项不影响下极限。

最后，对每个固定 $K\ge1$，命题 128.1 的实际上界是 $0<g_{K,n}\le1-e_{K,n}<D_K\alpha^n$。右端随 $n\to\infty$ 趋零，故 $g_{K,n}\to0$；再用 $e_{K,n}\le1$ 得 $e_{K,n}\to1$，从而 $d_{\rm tr}(\rho_n,\sigma^{\rm cut}_{K,n})=e_{K,n}+g_{K,n}\to1$。这是固定 $K$ 的窗口序列；沿 $n=K+1$ 的窗口序列则有 $e_{K,K+1}\to1/\sqrt5<1$ 及上述正的下极限界。证毕。

## 追加锚（本行以下为增补区）
## 130. 固定二维活动记忆的相干前缀生成与容量下界

**命题 130.1（同一等距的逐位生成与受限最小容量）。** 取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
$$
并令 $B=M=\mathbb C^2$，两者均以 $|0\rangle,|1\rangle$ 为正交标准基。输出空间为完整张量积 $H_n=B^{\otimes n}$，$H_0=\mathbb C$。记 $W_n\subseteq\{0,1\}^n$ 为不含相邻 $11$ 的词集，$W_0=\{\varnothing\}$；对 $n\ge1$，令 $\ell(w)=w_{n-1}$ 为末位，并置
$$
s_n=\sum_{w\in W_n}|w\rangle,\qquad
t_n=\sum_{\substack{w\in W_n\\\ell(w)=0}}|w\rangle,
$$
$$
\rho_n=\alpha^{n+1}|s_n\rangle\langle s_n|
       +\alpha^{n+2}|t_n\rangle\langle t_n|,\qquad \rho_0=(1).
$$
这里的 $\rho_n$ 是命题 125.1 的固定左边界相干局部态，作为 $H_n$ 上的算子取值。

在活动记忆中定义
$$
m_1=|0\rangle,\qquad m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,
$$
并以基像定义线性映射 $T:M\to B\otimes M$：
$$
T|0\rangle=|0\rangle\otimes m_0,\qquad
T|1\rangle=|1\rangle\otimes m_1.
$$
它是等距。令 $\Xi_0=m_0$，始终按输出在前、记忆在后的次序递推
$$
\Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n\in H_{n+1}\otimes M
\qquad(n\ge0).
$$
则所有 $\Xi_n$ 均为单位向量，且对每个 $n\ge1$，
$$
\Xi_n=\sum_{w\in W_n}\alpha^{(n+\ell(w))/2}|w\rangle\otimes m_{\ell(w)}
=\alpha^{(n+1)/2}s_n\otimes|0\rangle
 +\alpha^{(n+2)/2}t_n\otimes|1\rangle.
$$
因而在完整输出空间上，对所有 $n\ge0$ 有
$$
\operatorname{Tr}_M|\Xi_n\rangle\langle\Xi_n|=\rho_n.
$$
非法词对应的行、列均为零，等式包含全部非对角相干项。后续只作用于记忆与新输出的等距保持已发出前缀的约化态，所以同一递推同时给出全部有限前缀。

这个 $T$ 可由同一个二比特幺正实现。令
$$
R=\begin{pmatrix}\sqrt\alpha&-\alpha\\\alpha&\sqrt\alpha\end{pmatrix},\qquad
C_0(R)=|0\rangle\langle0|\otimes R+|1\rangle\langle1|\otimes I_M,
\qquad W=C_0(R)\operatorname{SWAP}
$$
作用于 $B_{\rm new}\otimes M$，其中 $\operatorname{SWAP}(|b\rangle\otimes|c\rangle)=|c\rangle\otimes|b\rangle$，乘积中先作用 $\operatorname{SWAP}$。每次新输出取与已有系统独立的纯空白 $|0\rangle$，初始记忆为 $R|0\rangle=m_0$，则
$$
W(|0\rangle\otimes\psi)=T\psi\qquad(\psi\in M).
$$

最小活动记忆容量取 Hilbert 空间维数，且仅在如下类别中比较：记忆空间 $K$ 的维数固定为 $d$，初始记忆为纯态，每次引入独立纯空白；每步为顺序等距，已经发出的寄存器不再受作用；不存在未计入 $K$ 的环境、纯化参考、共享随机性或其它记忆。吸收纯空白的插入后，竞争映射可写作 $V_j:K\to B\otimes K$，允许随 $j$ 改变。若这种生成器精确实现全部 $\rho_n$，则 $d\ge2$；上述固定 $T$ 达到 $d=2$。该最小性只比较指定输出态族在此类别中的精确生成，等式所确定的是已发出前缀上的全部联合测量概率，不是任意记忆干预的过程等价或普适最小预测器。

证明。首先 $\|m_1\|^2=1$、$\|m_0\|^2=\alpha+\alpha^2=1$，而
$$
\langle m_1,m_0\rangle=\sqrt\alpha.
$$
$T$ 的两列具有单位范数，其内积为
$$
\langle |0\rangle\otimes m_0,|1\rangle\otimes m_1\rangle
=\langle0|1\rangle\langle m_0,m_1\rangle=0.
$$
因此 $T^*T=I_M$；这里使两列正交的是输出基，而非两个记忆标签。由线性性，
$$
Tm_0=\sqrt\alpha\,|0\rangle\otimes m_0+\alpha|1\rangle\otimes m_1,
\qquad Tm_1=|0\rangle\otimes m_0.
$$
初态为单位向量，各步等距，故 $\|\Xi_n\|=1$，包括 $n=0$。

对所列词展开从 $n=1$ 开始归纳，不为空词定义末位。$W_1=\{0,1\}$，$\Xi_1=Tm_0$ 的两个系数分别为 $\alpha^{1/2}$ 与 $\alpha$，正是公式。设公式对某个 $n\ge1$ 成立。若 $w\in W_n$ 末位为 $0$，它的项在下一步变为
$$
\alpha^{n/2}|w\rangle\otimes Tm_0
=\alpha^{(n+1)/2}|w0\rangle\otimes m_0
 +\alpha^{(n+2)/2}|w1\rangle\otimes m_1.
$$
这两个延长都合法，系数分别等于 $\alpha^{(n+1+\ell(w0))/2}$ 与 $\alpha^{(n+1+\ell(w1))/2}$。若 $w$ 末位为 $1$，只有附加 $0$ 合法，且
$$
\alpha^{(n+1)/2}|w\rangle\otimes Tm_1
=\alpha^{(n+1)/2}|w0\rangle\otimes m_0.
$$
其系数同样是所需的 $\alpha^{(n+1+\ell(w0))/2}$，而附加 $1$ 的振幅为零。每个长度 $n+1$ 的合法词具有唯一长度 $n$ 前缀，故这些项无遗漏、无重复，归纳成立。

将每项的记忆向量改写到正交计算基上。末位为 $0$ 的词给出的两个记忆列系数为
$$
\alpha^{n/2}\sqrt\alpha=\alpha^{(n+1)/2},\qquad
\alpha^{n/2}\alpha=\alpha^{(n+2)/2};
$$
末位为 $1$ 的词只给记忆 $|0\rangle$ 列，系数也为 $\alpha^{(n+1)/2}$。因此得到陈述中的 $s_n,t_n$ 两列展开。对这两个正交记忆列取偏迹，交叉项为零，立即给
$$
\operatorname{Tr}_M|\Xi_n\rangle\langle\Xi_n|
=\alpha^{n+1}|s_n\rangle\langle s_n|
 +\alpha^{n+2}|t_n\rangle\langle t_n|=\rho_n\qquad(n\ge1).
$$
具体地，对所有 $u,v\in\{0,1\}^n$，完整矩阵元为
$$
\langle u|\rho_n|v\rangle=
\begin{cases}
\alpha^n,&u,v\in W_n,\ \ell(u)=\ell(v)=0,\\
\alpha^{n+1},&u,v\in W_n,\ \text{至少一个末位为 }1,\\
0,&u\notin W_n\ \text{或 }v\notin W_n.
\end{cases}
$$
第一种情形使用 $\alpha^{n+1}+\alpha^{n+2}=\alpha^n$。这也直接核对了命题 125.1 的全部相干项。$n=0$ 时，对整个记忆取迹给 $\|m_0\|^2=1=\rho_0$，无需使用词展开。

为核对已经发出的边际，取任意 $A\in\mathcal L(H_n)$。由 $T^*T=I_M$，
$$
\langle\Xi_{n+1},(A\otimes I_B\otimes I_M)\Xi_{n+1}\rangle
=\langle\Xi_n,(A\otimes T^*T)\Xi_n\rangle
=\operatorname{Tr}(\rho_nA).
$$
这对所有 $A$ 成立，所以再发出一位后前 $n$ 位的密度仍是 $\rho_n$。迭代即得对每个 $0\le k\le n$，
$$
\operatorname{Tr}_{B^{\otimes(n-k)}\otimes M}
|\Xi_n\rangle\langle\Xi_n|=\rho_k.
$$
特别地，任意前缀上的联合 POVM $(E_a)_a$ 满足 $\Pr(a)=\operatorname{Tr}(\rho_kE_a)$。偏迹在此描述停止时的输出态；继续生成使用的是仍与旧输出相关联的同一记忆。

两个条件记忆标签不能被当作可完美读取的经典标志。事实上，若效应 $0\le E\le I_M$ 满足 $\langle m_0,Em_0\rangle=1$、$\langle m_1,Em_1\rangle=0$，正性给 $(I_M-E)^{1/2}m_0=0$ 及 $E^{1/2}m_1=0$，于是 $Em_0=m_0$、$Em_1=0$。自伴性将给
$$
\sqrt\alpha=\langle m_1,m_0\rangle
=\langle m_1,Em_0\rangle=\langle Em_1,m_0\rangle=0,
$$
矛盾。

现核对显式幺正。由 $\alpha+\alpha^2=1$，直接相乘得 $R^*R=RR^*=I_M$。两个控制投影正交且和为 $I_B$，故
$$
C_0(R)^*C_0(R)=C_0(R)C_0(R)^*=I_{B\otimes M}.
$$
$\operatorname{SWAP}$ 置换正交标准基且平方为恒等，亦为幺正，因此 $W$ 在整个四维空间上幺正。任取 $\psi=a|0\rangle+b|1\rangle$，先交换、再施加零控制的 $R$，得到
$$
\begin{aligned}
W(|0\rangle\otimes\psi)
&=C_0(R)(\psi\otimes|0\rangle)\\
&=a|0\rangle\otimes R|0\rangle+b|1\rangle\otimes|0\rangle\\
&=a|0\rangle\otimes m_0+b|1\rangle\otimes m_1=T\psi.
\end{aligned}
$$
这是整个输入记忆空间上的线性等式，与旧输出张量恒等后也成立，所以每次插入独立空白并作用同一 $W$ 就给上述递推。在固定纯空白上逐槽作用幺正，其有限链振幅由逐槽矩阵元收缩给出，单位初态的范数保持为一（[SequentialRegisterCircuit，circuit_initialized_coefficients 与 initialized_norm](../../../D5/S3/Quantum/Entanglement/SequentialRegisterCircuit.lean)）；这里所需的特殊基像由刚才的直接计算确定。

最后证明限定类别中的下界。对任意竞争生成器，第一位输出后，输出与全部活动记忆的联合态为纯态 $\eta\in B\otimes K$，因为输入记忆与独立空白均纯，且第一步为等距。在 $K$ 的正交标准基 $e_1,\ldots,e_d$ 下写
$$
\eta=\sum_{j=1}^d x_j\otimes e_j,\qquad x_j\in B.
$$
其输出密度为 $\sum_{j=1}^d|x_j\rangle\langle x_j|$，像包含于 $\operatorname{span}\{x_1,\ldots,x_d\}$，所以若精确匹配第一位，必有 $\operatorname{rank}\rho_1\le d$。由目标公式，
$$
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},\qquad
\det\rho_1=\alpha^3-\alpha^4=\alpha^3(1-\alpha)=\alpha^5>0.
$$
故 $\operatorname{rank}\rho_1=2$，从而 $d\ge2$。上面的构造使用纯初始记忆、独立纯空白及固定幺正，没有其它环境，并达到 $d=2$。下界只用第一步，对时间依赖的竞争等距同样成立。

固定活动容量与固定总档案是不同的资源条件：第 $n$ 步后保留的是 $n$ 个输出 qubit 加一个活动 qubit，联合空间为 $H_n\otimes M$，维数 $2^{n+1}$。输出寄存器随 $n$ 增加；有限个输出并未容纳一个无限词。若把这些有限前缀统一为命题 125.4 指定的 $\ell^2(X_{\rm fs})$ 上的单个正迹类密度，并沿用其柱投影 $C_u$，则全部柱读数须为 $\alpha^{|u|+\ell(u)}$（非空合法 $u$）。命题 125.4 排除了这样的密度；这里变化的输出空间并不提供该固定表示。

同一 $T$ 也不使边界态移位平稳。由已证对角元，第一位与第二位为 $1$ 的概率分别为
$$
\Pr(w_0=1)=\alpha^2,\qquad
\Pr(w_1=1)=\langle01|\rho_2|01\rangle+\langle11|\rho_2|11\rangle
=\alpha^3\ne\alpha^2.
$$
这与命题 125.3 的固定左边界律一致。若第一步后丢弃记忆并独立重置，第二步后两位输出为乘积态；若还要保持上述两个单点概率，便会给 $\Pr(11)=\alpha^5>0$，而目标值为零。因此停止时取偏迹不能替代生成途中保留记忆关联。当 $n\ge1$ 时，命题 125.3 的经典 Markov 抽样在计算基中给 $\sum_{w\in W_n}\alpha^{n+\ell(w)}|w\rangle\langle w|$，只匹配对角元；例如目标的 $\langle0|\rho_1|1\rangle=\alpha^2>0$。这一比较限于抽样所得的对角态，不排除另带相干制备的经典控制协议，也不把本命题的容量下界推广到其假设以外的模型。证毕。

## 追加锚（本行以下为增补区）

## 131. 活动记忆的边界遗忘与平稳窗口的构型相干

**命题 131.1（精确记忆衰减、统一未来窗口界与保留首记录的正下界）。** 沿用命题 130.1 的固定等距，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
\qquad B=M=\mathbb C^2,\qquad H_\ell=B^{\otimes\ell},\qquad H_0=\mathbb C.
$$
$B$ 与 $M$ 均取正交标准基 $|0\rangle,|1\rangle$。令
$$
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad
m_1=|0\rangle,\qquad P_j=|m_j\rangle\langle m_j|\quad(j=0,1),
$$
$$
T:M\longrightarrow B\otimes M,\qquad T|j\rangle=|j\rangle\otimes m_j.
$$
每步对已发出输出张量恒等，始终按输出在前、活动记忆在后的次序定义
$$
T_0=I_M,\qquad T_{\ell+1}=(I_{H_\ell}\otimes T)T_\ell:
M\longrightarrow H_{\ell+1}\otimes M.
$$
对 $X\in\mathcal L(M)$ 定义记忆通道与输出通道
$$
\mathcal M(X)=\operatorname{Tr}_B(TXT^*),\qquad
\Gamma_\ell(X)=\operatorname{Tr}_M(T_\ell XT_\ell^*),\qquad
\Gamma_0(X)=\operatorname{Tr}X.
$$
原初记忆为纯态 $\sigma_0=P_0$，记
$$
\sigma_n=\mathcal M^n(P_0),\qquad
\Omega_n=T_nP_0T_n^*,\qquad
\rho_n=\Gamma_n(P_0)\quad(n\ge0).
$$
这里 $\rho_n$ 是命题 125.1 的完整相干密度，由命题 130.1 的等式识别；$\rho_0=1$。任意同一有限维空间上的两个密度采用半迹范数距离
$$
D(\theta,\vartheta)=\frac12\|\theta-\vartheta\|_1,
\qquad \|A\|_1=\operatorname{Tr}\sqrt{A^*A}.
$$
令
$$
\mathrm{den}=1+\alpha^2,\qquad
\pi_0=\frac1{\mathrm{den}},\qquad
\pi_1=\frac{\alpha^2}{\mathrm{den}},\qquad
\sigma_*=\pi_0P_0+\pi_1P_1.
$$
则记忆通道的显式形式、唯一不动密度及从指定初态出发的轨道满足
$$
\mathcal M(X)=X_{00}P_0+X_{11}P_1,\qquad
\mathcal M(\sigma_*)=\sigma_*,
$$
$$
\sigma_n=(1-p_n)P_0+p_nP_1,\qquad
p_0=0,\qquad p_{n+1}=\alpha^2(1-p_n),\qquad
p_n=\pi_1\bigl(1-(-\alpha^2)^n\bigr).
$$
带符号的系数偏差 $p_n-\pi_1=-\pi_1(-\alpha^2)^n$ 在偶数 $n$ 时严格为负，在奇数 $n$ 时严格为正；它是两个非正交密度的混合系数偏差，不是可完美读取的记忆标志概率。对所有整数 $n\ge0$，精确记忆距离为
$$
D(\sigma_n,\sigma_*)=
\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}.
$$

对整数 $n\ge0,\ell\ge1$，在 $H_\ell$ 上定义无条件未来窗口和比较密度
$$
\beta_{n,\ell}=\operatorname{Tr}_{\text{前 }n\text{ 位}}\rho_{n+\ell},
\qquad \eta_\ell=\Gamma_\ell(\sigma_*),\qquad \eta_0=1.
$$
此前 $n$ 位输出及最终记忆均被忽略；允许的未来窗口效应在联合空间上形如 $I_{H_n}\otimes E\otimes I_M$，其中 $0\le E\le I_{H_\ell}$。此范围不含读取旧记录、按旧记录条件化、访问纯化参考、反馈或任意记忆干预。则
$$
\beta_{n,\ell}=\Gamma_\ell(\sigma_n),\qquad
D(\beta_{n,\ell},\eta_\ell)
\le\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}
\quad(n\ge0,\ \ell\ge1),
$$
其中同一个上界适用于每个有限 $\ell$。对所有整数 $\ell\ge0$，比较族左右边缘均相容：
$$
\operatorname{Tr}_{\text{末位}}\eta_{\ell+1}=\eta_\ell,
\qquad
\operatorname{Tr}_{\text{首位}}\eta_{\ell+1}=\eta_\ell.
$$
特别地，对所有整数 $r,s,\ell\ge0$，将剩余输出依序识别为 $H_\ell$ 后，
$$
\operatorname{Tr}_{\text{前 }r\text{ 位与后 }s\text{ 位}}
\eta_{r+\ell+s}=\eta_\ell.
$$

在所指定的记忆基与输出构型基中，矩阵分别为
$$
\Gamma_1(X)=
\begin{pmatrix}X_{00}&\sqrt\alpha\,X_{01}\\
\sqrt\alpha\,X_{10}&X_{11}\end{pmatrix},
\qquad
\sigma_*=
\frac1{\mathrm{den}}
\begin{pmatrix}1&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix},
$$
$$
\eta_1=\frac1{\mathrm{den}}
\begin{pmatrix}1&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},
\qquad
\langle0|\eta_1|1\rangle=\frac{\alpha^2}{\mathrm{den}}>0,
\qquad
\det\sigma_*=\frac{\alpha^4}{\mathrm{den}^2}>0.
$$
若以 $\Delta_B(Y)=\sum_{j=0}^1|j\rangle\langle j|Y|j\rangle\langle j|$ 表示该输出基中的完全去相干，则 $\Delta_B(\eta_1)\ne\eta_1$。此单位置结论只判定给定基中的去相干，不给出纠缠、情境性或 Bell 非局域性的判据。比较族的此项构造使用秩二的混合初始记忆 $\sigma_*$，不属于命题 130.1 比较最小容量时限定的纯初态类别；这里不对 $\eta_\ell$ 在该类别中的可达性或最小容量作断言。

最后，若比较保留首记录的完整窗口，则对每个整数 $\ell\ge1$ 有
$$
D(\rho_\ell,\eta_\ell)\ge
\frac{\sqrt2\,\alpha^4}{\mathrm{den}}>0.
$$
上述未来窗口上界与完整窗口下界均是在各自有限空间 $H_\ell$ 内的距离不等式，不是把增长中的窗口视为同一空间中的范数极限；$n$ 表示略去的输出位数，不是物理时间。

证明。命题 130.1 给 $T^*T=I_M$，故由递推 $T_\ell^*T_\ell=I_M$。各 $\Gamma_\ell$ 将密度映为密度，包括 $\ell=0$ 的标量密度。对矩阵单位直接展开，
$$
TXT^*=\sum_{i,j=0}^1X_{ij}|i\rangle\langle j|\otimes|m_i\rangle\langle m_j|.
$$
对输出基取偏迹，只保留 $i=j$ 项，得到
$$
\mathcal M(X)=X_{00}P_0+X_{11}P_1.
$$
密度 $X$ 的两个对角元非负且和为 $1$，故任何不动密度都必须落在 $P_0,P_1$ 的凸混合像中。这两密度不同，因而其混合系数唯一。设 $X=(1-p)P_0+pP_1$、$0\le p\le1$，则
$$
X_{11}=\alpha^2(1-p),\qquad
X_{00}=\alpha(1-p)+p=1-\alpha^2(1-p).
$$
因此 $\mathcal M(X)$ 的 $P_1$ 系数是 $\alpha^2(1-p)$。不动点方程为
$$
p=\alpha^2(1-p),\qquad
p=\frac{\alpha^2}{1+\alpha^2}=\pi_1,
$$
所以 $\sigma_*$ 存在且是不动密度中的唯一者。从 $p_0=0$ 归纳，递推保持 $p_n\in[0,1]$；减去不动点方程得
$$
p_{n+1}-\pi_1=-\alpha^2(p_n-\pi_1),\qquad
p_n-\pi_1=-\pi_1(-\alpha^2)^n.
$$
这证明轨道公式及奇偶符号。又 $\langle m_1,m_0\rangle=\sqrt\alpha\ne0$。若效应 $E$ 能以概率 $1$ 区分这两个纯态，则交换标签后可设 $Em_0=m_0$、$Em_1=0$：这些等式由 $E$ 与 $I_M-E$ 的正性推出。自伴性却会给
$$
\sqrt\alpha=\langle m_1,m_0\rangle
=\langle m_1,Em_0\rangle=\langle Em_1,m_0\rangle=0,
$$
矛盾，故混合分量不是可完美读取的标志。

为计算精确距离，在记忆基中有
$$
P_1-P_0=
\begin{pmatrix}\alpha^2&-\alpha\sqrt\alpha\\
-\alpha\sqrt\alpha&-\alpha^2\end{pmatrix},
\qquad \operatorname{Tr}(P_1-P_0)=0,
$$
$$
(P_1-P_0)^2=(\alpha^4+\alpha^3)I_M=\alpha^2I_M.
$$
末式使用 $\alpha+\alpha^2=1$。此自伴矩阵的两个特征值为 $\alpha,-\alpha$，故 $D(P_0,P_1)=\alpha$。于是对 $n\ge0$，
$$
\sigma_n-\sigma_*=(p_n-\pi_1)(P_1-P_0),\qquad
D(\sigma_n,\sigma_*)=|p_n-\pi_1|\alpha
=\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}.
$$
特别地，$n=0$ 给 $D(P_0,\sigma_*)=\pi_1\alpha=\alpha^3/\mathrm{den}$。

现从实际联合态求未来窗口。递推并保留张量次序，归纳得到
$$
T_{n+\ell}=(I_{H_n}\otimes T_\ell)T_n
\qquad(n,\ell\ge0).
$$
对任意 $A\in\mathcal L(H_n\otimes M)$，在 $H_n$ 的正交标准基中写 $A=\sum_{u,v}|u\rangle\langle v|\otimes A_{uv}$，便有
$$
\operatorname{Tr}_{H_n}
\bigl[(I_{H_n}\otimes T_\ell)A(I_{H_n}\otimes T_\ell^*)\bigr]
=\sum_uT_\ell A_{uu}T_\ell^*
=T_\ell(\operatorname{Tr}_{H_n}A)T_\ell^*.
$$
这个恒等式适用于相关联合态。取 $\ell=1$，再对新输出取偏迹，并从 $\Omega_0=P_0$ 归纳，得到
$$
\operatorname{Tr}_{H_n}\Omega_n=\mathcal M^n(P_0)=\sigma_n.
$$
现在取 $A=\Omega_n$，再对最终记忆取偏迹，结合命题 130.1 对完整相干输出的识别，得到
$$
\begin{aligned}
\beta_{n,\ell}
&=\operatorname{Tr}_{H_n\otimes M}
\bigl[(I_{H_n}\otimes T_\ell)\Omega_n(I_{H_n}\otimes T_\ell^*)\bigr]\\
&=\operatorname{Tr}_M(T_\ell\sigma_nT_\ell^*)
=\Gamma_\ell(\sigma_n).
\end{aligned}
$$
这里没有把 $\Omega_n$ 分解成旧输出与记忆的乘积；被忽略的旧输出是通过偏迹消去的。

以下使用有限维迹距离的效应变分式（参见 John Watrous，[The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/)，Cambridge University Press，2018，量子态判别部分）。为同时处理不同输入、输出维数，直接给出所需推导。任意有限维空间 $K$ 上的两个密度 $\theta,\vartheta$ 之差 $A=\theta-\vartheta$ 自伴且迹零。取正、负谱部分 $A_+,A_-$，则
$$
A=A_+-A_-,\qquad A_+A_-=0,\qquad
\operatorname{Tr}A_+=\operatorname{Tr}A_-=\tfrac12\|A\|_1.
$$
对 $0\le E\le I_K$，正性给 $0\le\operatorname{Tr}(EA_\pm)\le\operatorname{Tr}A_\pm$，所以
$$
|\operatorname{Tr}(EA)|\le\tfrac12\|A\|_1.
$$
取 $E$ 为 $A$ 的正谱投影即达到右端，因而
$$
D(\theta,\vartheta)=\sup_{0\le E\le I_K}
|\operatorname{Tr}(E(\theta-\vartheta))|.
$$
对输出空间 $H_\ell$ 上任意效应 $E$，回拉为记忆空间上的
$$
F=T_\ell^*(E\otimes I_M)T_\ell.
$$
由于 $T_\ell$ 等距，
$$
F\ge0,\qquad
I_M-F=T_\ell^*((I_{H_\ell}-E)\otimes I_M)T_\ell\ge0.
$$
故对 $M$ 上的两个密度 $\theta,\vartheta$，偏迹的定义与迹的循环性给
$$
\begin{aligned}
|\operatorname{Tr}(E(\Gamma_\ell(\theta)-\Gamma_\ell(\vartheta)))|
&=|\operatorname{Tr}(F(\theta-\vartheta))|\\
&\le D(\theta,\vartheta).
\end{aligned}
$$
在 $H_\ell$ 上对 $E$ 取上确界，得到
$$
D(\Gamma_\ell(\theta),\Gamma_\ell(\vartheta))
\le D(\theta,\vartheta).
$$
这一步不要求 $\dim H_\ell=\dim M$。取 $\theta=\sigma_n,\vartheta=\sigma_*$，便得所述未来窗口界，右端与 $\ell$ 无关。

为证明边缘相容，先取任意记忆密度 $X$ 与 $A\in\mathcal L(H_\ell)$。由最后一步 $T_{\ell+1}=(I_{H_\ell}\otimes T)T_\ell$，
$$
\begin{aligned}
\operatorname{Tr}\bigl[(A\otimes I_B)\Gamma_{\ell+1}(X)\bigr]
&=\operatorname{Tr}\bigl[T_\ell XT_\ell^*(A\otimes T^*T)\bigr]\\
&=\operatorname{Tr}\bigl[A\Gamma_\ell(X)\bigr].
\end{aligned}
$$
因这对所有 $A$ 成立，$\operatorname{Tr}_{\text{末位}}\Gamma_{\ell+1}(X)=\Gamma_\ell(X)$。另一方面，按第一步分组为 $T_{\ell+1}=(I_B\otimes T_\ell)T$，利用刚才的偏迹交换恒等式得
$$
\operatorname{Tr}_{\text{首位}}\Gamma_{\ell+1}(X)
=\operatorname{Tr}_M\bigl[T_\ell\operatorname{Tr}_B(TXT^*)T_\ell^*\bigr]
=\Gamma_\ell(\mathcal M(X)).
$$
两式在 $\ell=0$ 时均为取整个单点密度的迹，值为 $1$。取 $X=\sigma_*$ 并用 $\mathcal M(\sigma_*)=\sigma_*$，即得左右相容；反复略去末位与首位给所有平移窗口的同一密度 $\eta_\ell$。

对 $TXT^*$ 的展开改为取记忆偏迹，矩阵元变为 $X_{ij}\langle m_j,m_i\rangle$。两记忆向量均为单位向量，交叉内积为 $\sqrt\alpha$，所以得到所列 $\Gamma_1(X)$。再将 $\pi_0,\pi_1$ 代入 $\sigma_*$：
$$
\sigma_*=
\frac1{\mathrm{den}}
\begin{pmatrix}\alpha+\alpha^2&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix}
=\frac1{\mathrm{den}}
\begin{pmatrix}1&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix}.
$$
应用 $\Gamma_1$ 得 $\eta_1$ 的非对角元 $\sqrt\alpha\,\alpha\sqrt\alpha/\mathrm{den}=\alpha^2/\mathrm{den}$，严格为正，故 $\eta_1\ne\Delta_B(\eta_1)$。同时
$$
\det\sigma_*=
\frac{\alpha^2-\alpha^3}{\mathrm{den}^2}
=\frac{\alpha^2(1-\alpha)}{\mathrm{den}^2}
=\frac{\alpha^4}{\mathrm{den}^2}>0.
$$
$\sigma_*$ 为密度且秩二，故此比较族确实使用混合初态。

最后，由命题 125.1 的单点矩阵，令 $c=\alpha^4/\mathrm{den}>0$，则
$$
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix},\qquad
\rho_1-\eta_1=c\begin{pmatrix}-1&1\\1&1\end{pmatrix}.
$$
右边矩阵的平方为 $2c^2I_B$ 且迹零，特征值为 $\sqrt2c,-\sqrt2c$，所以 $D(\rho_1,\eta_1)=\sqrt2c$。命题 130.1 的前缀相容与已证 $\eta$ 的末位相容给
$$
\operatorname{Tr}_{\text{后 }\ell-1\text{ 位}}\rho_\ell=\rho_1,
\qquad
\operatorname{Tr}_{\text{后 }\ell-1\text{ 位}}\eta_\ell=\eta_1.
$$
在效应变分式中将单点效应 $E$ 提升为 $E\otimes I_{H_{\ell-1}}$，即得偏迹收缩；因此
$$
D(\rho_\ell,\eta_\ell)\ge D(\rho_1,\eta_1)
=\frac{\sqrt2\,\alpha^4}{\mathrm{den}}>0
\qquad(\ell\ge1).
$$
故略去左端记录后，所有有限未来窗口的距离都受随 $n$ 趋零的同一上界控制；保留旧首记录的窗口则始终具有上述正的可区分度下界。证毕。

## 追加锚（本行以下为增补区）
## 132. 边界遗忘下的相邻输出纠缠与统一有限位置见证

**命题 132.1（平稳双位置纠缠及同一轨道的严格负见证界）。** 沿用命题 130.1 的固定等距及命题 131.1 的记号：
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
\qquad \mathrm{den}=1+\alpha^2,\qquad
\pi_0=\frac1{\mathrm{den}},\qquad \pi_1=\frac{\alpha^2}{\mathrm{den}}.
$$
取 $B=M=\mathbb C^2$，均以 $|0\rangle,|1\rangle$ 为正交标准基，并令
$$
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad
m_1=|0\rangle,\qquad P_j=|m_j\rangle\langle m_j|,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
顺序始终为输出在前、记忆在后；$T_0=I_M$，$T_{\ell+1}=(I_{B^{\otimes\ell}}\otimes T)T_\ell$，且
$$
\Gamma_\ell(X)=\operatorname{Tr}_M(T_\ell XT_\ell^*),\qquad
\sigma_*=\pi_0P_0+\pi_1P_1,\qquad
\eta_\ell=\Gamma_\ell(\sigma_*),\qquad
\rho_\ell=\Gamma_\ell(P_0).
$$
命题 131.1 给出的 $\sigma_*$ 是秩二混合不动密度，$\eta_\ell$ 为平稳比较族；原族 $\rho_\ell$ 仍从纯记忆 $P_0$ 出发。此混合比较初态不改变命题 130.1 的纯初态容量定理及其适用类别。

以下张量分割为两个实际发出位置的完整空间 $B_1\otimes B_2=\mathbb C^2\otimes\mathbb C^2$。称其上的密度 $\theta$ 可分，是指存在有限分解
$$
\theta=\sum_{r=1}^N q_r A_r\otimes C_r,\qquad
q_r\ge0,\qquad \sum_{r=1}^N q_r=1,
$$
其中 $A_r,C_r$ 分别为 $B_1,B_2$ 上的密度，即正半定且迹为一的算子。不满足此定义者称为纠缠态。合法支撑 $\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}$ 只是完整空间的子空间，不另赋予它一个张量分割。

在字典序 $00,01,10,11$ 下，平稳双位置密度为
$$
\eta_2=\pi_0
\begin{pmatrix}
\alpha&\alpha^2&\alpha^2&0\\
\alpha^2&\alpha^2&\alpha^3&0\\
\alpha^2&\alpha^3&\alpha^2&0\\
0&0&0&0
\end{pmatrix}.
$$
定义 Hermitian 算子
$$
W_{\rm ent}=\alpha^4|00\rangle\langle00|+|11\rangle\langle11|
-\alpha^2\bigl(|01\rangle\langle10|+|10\rangle\langle01|\bigr).
$$
则对每个可分密度 $\theta$ 有 $\operatorname{Tr}(W_{\rm ent}\theta)\ge0$，而
$$
\operatorname{Tr}(W_{\rm ent}\eta_2)=-\pi_0\alpha^5<0.
$$
因此 $\eta_2$ 在两个发出位置之间纠缠。$W_{\rm ent}$ 有负特征值，因而不是正的 POVM 效应；这里使用的是其期望值作为纠缠见证。

同一命题还适用于原纯初态轨道的每个有限位置。对整数 $n\ge0$，令
$$
\beta_{n,2}=\operatorname{Tr}_{\text{前 }n\text{ 位}}\rho_{n+2}.
$$
这些窗口均忽略前 $n$ 位及最终记忆，不作条件化、反馈或其它干预。命题 131.1 的实际相关前缀恒等式与递推给
$$
\beta_{n,2}=\Gamma_2(\sigma_n),\qquad
\sigma_n=(1-p_n)P_0+p_nP_1,\qquad
p_0=0,\qquad p_{n+1}=\alpha^2(1-p_n).
$$
同一个 $W_{\rm ent}$ 满足
$$
\operatorname{Tr}(W_{\rm ent}\beta_{n,2})
=\alpha^5\bigl((\alpha-2)+(3-\alpha)p_n\bigr)
\le-2\alpha^8<0\qquad(n\ge0),
$$
且 $n=1$ 时等号成立。故原族的每个平移相邻窗口也纠缠；$-2\alpha^8$ 是此固定见证沿指定轨道的期望最大值，不是对所有态或见证优化的纠缠量。

证明。由 $T$ 的基像及顺序递推，
$$
T_2|0\rangle=\sqrt\alpha\,|00\rangle\otimes m_0
+\alpha|01\rangle\otimes m_1,\qquad
T_2|1\rangle=|10\rangle\otimes m_0.
$$
为核对全部矩阵元，对 $u\in\{00,01,10,11\}$ 定义记忆系数映射
$$
L_u=(\langle u|\otimes I_M)T_2,\qquad
L_{00}=\sqrt\alpha\,|m_0\rangle\langle0|,\quad
L_{01}=\alpha|m_1\rangle\langle0|,\quad
L_{10}=|m_0\rangle\langle1|,\quad L_{11}=0.
$$
于是对任意 $X\in\mathcal L(M)$ 及任意 $u,v$，
$$
\langle u|\Gamma_2(X)|v\rangle=\operatorname{Tr}(L_uXL_v^*).
$$
两个记忆向量的实际内积为
$$
\langle m_0,m_0\rangle=\langle m_1,m_1\rangle=1,\qquad
\langle m_0,m_1\rangle=\langle m_1,m_0\rangle=\sqrt\alpha.
$$
具体地，对非零的三个 $L_u=c_u|m_{k_u}\rangle\langle j_u|$，上式等于
$$
c_uc_vX_{j_uj_v}\langle m_{k_v},m_{k_u}\rangle,
\qquad
(c_u,j_u,k_u)=
\begin{cases}
(\sqrt\alpha,0,0),&u=00,\\
(\alpha,0,1),&u=01,\\
(1,1,0),&u=10.
\end{cases}
$$
任一指标为 $11$ 时则为零。三个对角元依次是 $\alpha X_{00},\alpha^2X_{00},X_{11}$；三个上三角非对角元依次是
$$
\sqrt\alpha\,\alpha X_{00}\langle m_1,m_0\rangle=\alpha^2X_{00},\qquad
\sqrt\alpha\,X_{01}\langle m_0,m_0\rangle=\sqrt\alpha\,X_{01},\qquad
\alpha X_{01}\langle m_0,m_1\rangle=\alpha\sqrt\alpha\,X_{01}.
$$
反向指标仍由同一公式给出，无需假设 $X$ 自伴。因此全部十六个矩阵元为
$$
\Gamma_2(X)=
\begin{pmatrix}
\alpha X_{00}&\alpha^2X_{00}&\sqrt\alpha\,X_{01}&0\\
\alpha^2X_{00}&\alpha^2X_{00}&\alpha\sqrt\alpha\,X_{01}&0\\
\sqrt\alpha\,X_{10}&\alpha\sqrt\alpha\,X_{10}&X_{11}&0\\
0&0&0&0
\end{pmatrix}.
$$
这里的相干项来自记忆向量的内积，非法扇区的整行整列由 $L_{11}=0$ 消失，并非只计算经典转移概率。

将命题 131.1 的矩阵
$$
\sigma_*=\pi_0
\begin{pmatrix}1&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix}
$$
代入，便得到陈述中的完整 $\eta_2$。它由密度 $\sigma_*$ 经等距及偏迹得到，故为正半定；同时
$$
\operatorname{Tr}\eta_2=\pi_0(\alpha+2\alpha^2)
=\pi_0(1+\alpha^2)=1.
$$
命题 131.1 的左右边缘相容性已保证，这也是该平稳比较族中任意两个相邻位置的密度。

现证明见证对全部可分态非负。任取复向量
$$
a=a_0|0\rangle+a_1|1\rangle\in B_1,\qquad
b=b_0|0\rangle+b_1|1\rangle\in B_2,
$$
不要求归一化，也不限制其乘积向量的支撑。直接展开给
$$
\begin{aligned}
\langle a\otimes b,W_{\rm ent}(a\otimes b)\rangle
&=\alpha^4|a_0b_0|^2+|a_1b_1|^2
-2\alpha^2\operatorname{Re}\bigl(\overline{a_0b_1}\,a_1b_0\bigr)\\
&=\left|a_1\overline{b_1}-\alpha^2a_0\overline{b_0}\right|^2\ge0.
\end{aligned}
$$
第二个因子的共轭不可省略：该等式使用任意复坐标，而非实向量的限制。若 $A,C$ 为两个因子上的密度，有限维谱分解给
$$
A=\sum_r\lambda_r|a^{(r)}\rangle\langle a^{(r)}|,\qquad
C=\sum_s\mu_s|b^{(s)}\rangle\langle b^{(s)}|,\qquad
\lambda_r,\mu_s\ge0,
$$
其中谱向量为单位向量，两组特征值各自和为一。按张量积及迹的线性性，
$$
\operatorname{Tr}\bigl(W_{\rm ent}(A\otimes C)\bigr)
=\sum_{r,s}\lambda_r\mu_s
\left|a^{(r)}_1\overline{b^{(s)}_1}
-\alpha^2a^{(r)}_0\overline{b^{(s)}_0}\right|^2\ge0.
$$
再对可分密度的有限凸组合应用线性性，即得 $\operatorname{Tr}(W_{\rm ent}\theta)\ge0$。这正是块正算子在可分锥上配对非负的成熟可分性数学（[CompositeConeDuality，blockPositive_iff_forall_separable_pairing_nonneg](../../../D5/S3/Resource/CompositeConeDuality.lean)）。

此见证的偏转置来源也可直接表示为
$$
W_{\rm ent}=\operatorname{PT}_2\bigl(|v\rangle\langle v|\bigr),\qquad
v=|11\rangle-\alpha^2|00\rangle,\qquad
\operatorname{PT}_2(|ij\rangle\langle kl|)=|il\rangle\langle kj|,
$$
其中 $\operatorname{PT}_2$ 按此基公式线性延伸。偏转置的可分性判据见 Asher Peres，Separability Criterion for Density Matrices，Physical Review Letters 77，1413–1415（1996），[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)，[arXiv:quant-ph/9604005](https://arxiv.org/abs/quant-ph/9604005)。这里仅使用其数学含义，不把偏转置当作物理操作；所需非负性已由平方模及谱分解直接证明。

$W_{\rm ent}$ 的两个交叉项互为伴随，故它自伴。而
$$
W_{\rm ent}(|01\rangle+|10\rangle)
=-\alpha^2(|01\rangle+|10\rangle),
$$
所以它不是正半定算子，也不满足 POVM 效应所需的 $0\le E\le I$。由 $\eta_2$ 的上述矩阵元，
$$
\begin{aligned}
\operatorname{Tr}(W_{\rm ent}\eta_2)
&=\alpha^4\langle00|\eta_2|00\rangle
+\langle11|\eta_2|11\rangle
-\alpha^2\bigl(\langle10|\eta_2|01\rangle+\langle01|\eta_2|10\rangle\bigr)\\
&=\pi_0\alpha^5-2\pi_0\alpha^5=-\pi_0\alpha^5<0.
\end{aligned}
$$
这与可分密度的非负性矛盾，证明平稳双位置态纠缠。

最后处理同一纯初态轨道的有限位置。将
$$
P_0=\begin{pmatrix}\alpha&\alpha\sqrt\alpha\\
\alpha\sqrt\alpha&\alpha^2\end{pmatrix},\qquad
P_1=\begin{pmatrix}1&0\\0&0\end{pmatrix}
$$
代入已求出的 $\Gamma_2$，得到
$$
G_0:=\Gamma_2(P_0)=
\begin{pmatrix}
\alpha^2&\alpha^3&\alpha^2&0\\
\alpha^3&\alpha^3&\alpha^3&0\\
\alpha^2&\alpha^3&\alpha^2&0\\
0&0&0&0
\end{pmatrix},
$$
$$
G_1:=\Gamma_2(P_1)=|0\rangle\langle0|\otimes\rho_1
=\begin{pmatrix}
\alpha&\alpha^2&0&0\\
\alpha^2&\alpha^2&0&0\\
0&0&0&0\\
0&0&0&0
\end{pmatrix},\qquad
\rho_1=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}.
$$
由命题 131.1 已在相关联合态上证明的窗口恒等式与 $\Gamma_2$ 的线性性，
$$
\beta_{n,2}=(1-p_n)G_0+p_nG_1.
$$
因而
$$
\operatorname{Tr}(W_{\rm ent}G_0)=\alpha^6-2\alpha^5
=\alpha^5(\alpha-2),\qquad
\operatorname{Tr}(W_{\rm ent}G_1)=\alpha^5,
$$
$$
\operatorname{Tr}(W_{\rm ent}\beta_{n,2})
=\alpha^5\bigl((\alpha-2)+(3-\alpha)p_n\bigr).
$$
递推映射 $p\mapsto\alpha^2(1-p)$ 将闭区间 $[0,\alpha^2]$ 映到
$$
[\alpha^2(1-\alpha^2),\alpha^2]=[\alpha^3,\alpha^2]
\subseteq[0,\alpha^2].
$$
从 $p_0=0$ 归纳得 $0\le p_n\le\alpha^2$ 对所有 $n\ge0$ 成立，且 $p_1=\alpha^2$。用 $\alpha+\alpha^2=1$ 化简，有
$$
(\alpha-2)+(3-\alpha)\alpha^2=-2\alpha^3,
$$
$$
\operatorname{Tr}(W_{\rm ent}\beta_{n,2})+2\alpha^8
=\alpha^5(3-\alpha)(p_n-\alpha^2)\le0.
$$
由于 $\alpha>0$、$3-\alpha>0$，这给出陈述中的统一严格负界，并在 $n=1$ 达到等号。每个 $\beta_{n,2}$ 因此均不可分。命题 130.1 的已发出前缀不变性还保证，继续生成任意有限个后续输出再忽略它们，不改变这一对已发出位置的边际。

同时，直接引用命题 131.1 在同一无条件窗口上的结论，
$$
D(\beta_{n,2},\eta_2)\le\frac{\alpha^3}{\mathrm{den}}\alpha^{2n}
\longrightarrow0\qquad(n\longrightarrow\infty).
$$
因此此固定生成器的边界遗忘与相邻输出纠缠同时成立。这里在单位置的指定基相干之外，进一步判定了跨两个输出因子的不可分性；此结论不蕴含 Bell 非局域性或情境性，不量化所有平稳态，也不构成物理空间的推导、最优负性或距离的断言。证毕。

## 追加锚（本行以下为增补区）
## 133. 忽略间隔后的分块可分性与平稳占据关联的非零尾

**命题 133.1（相关输入的间隔分解与交替衰减的平稳协方差）。** 沿用命题 130.1 的同一个固定等距及命题 131.1 的记忆通道。取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad 0<\alpha<1,\qquad \alpha+\alpha^2=1,
\qquad B=M=\mathbb C^2,\qquad H_n=B^{\otimes n},\qquad H_0=\mathbb C,
$$
$$
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\qquad
m_1=|0\rangle,\qquad P_j=|m_j\rangle\langle m_j|,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
两份二维空间均取正交标准基 $|0\rangle,|1\rangle$。以 $\dagger$ 表示伴随，$I_K$ 表示空间 $K$ 上的恒等算子，$\operatorname{Id}_K$ 表示算子空间 $\mathcal L(K)$ 上的恒等超算子。输出在前、记忆在后的顺序固定为
$$
T_0=I_M,\qquad T_{n+1}=(I_{H_n}\otimes T)T_n,
\qquad T^\dagger T=I_M,
$$
$$
\mathcal M(X)=\operatorname{Tr}_B(TXT^\dagger)=X_{00}P_0+X_{11}P_1,
\qquad \Gamma_n(X)=\operatorname{Tr}_M(T_nXT_n^\dagger),
\qquad \mathcal M^0=\operatorname{Id}_M.
$$
这里 $M$ 是 Hilbert 空间，$\mathcal M$ 是记忆通道。再记
$$
\pi_0=\frac1{1+\alpha^2},\qquad \pi_1=\frac{\alpha^2}{1+\alpha^2},\qquad
\sigma_*=\pi_0P_0+\pi_1P_1,\qquad
\eta_n=\Gamma_n(\sigma_*),\qquad \rho_n=\Gamma_n(P_0).
$$
命题 131.1 给出 $\mathcal M(\sigma_*)=\sigma_*$ 及 $\eta$ 的平稳边缘相容性。

第一，设 $L$ 为任意有限维复 Hilbert 空间，$\Omega$ 为 $L\otimes M$ 上任意密度，允许两因子相关或纠缠。旧因子 $L$ 始终不受作用。对整数 $g,b\ge1$，依序发出 $g$ 个被忽略的中间输出及 $b$ 个保留的右侧输出；完整次序为 $L\otimes H_g\otimes H_b\otimes M$。保留态定义为实际联合态的偏迹
$$
\omega_{LR}
=\operatorname{Tr}_{H_g,M}\bigl[
(I_L\otimes T_{g+b})\Omega(I_L\otimes T_{g+b}^\dagger)
\bigr]\in\mathcal L(L\otimes H_b).
$$
令
$$
A_j=(I_L\otimes\langle j|)\Omega(I_L\otimes|j\rangle),
\qquad w_j=\operatorname{Tr}A_j\quad(j=0,1).
$$
则 $A_j\ge0$、$w_j\ge0$、$w_0+w_1=1$，并且
$$
\begin{aligned}
\omega_{LR}
&=\bigl(\operatorname{Id}_L\otimes(\Gamma_b\circ\mathcal M^g)\bigr)(\Omega)\\
&=\sum_{j=0}^1 A_j\otimes\Gamma_b\bigl(\mathcal M^{g-1}(P_j)\bigr)\\
&=\sum_{\substack{j=0,1\\w_j>0}}
w_j\,\frac{A_j}{w_j}\otimes\Gamma_b\bigl(\mathcal M^{g-1}(P_j)\bigr).
\end{aligned}
$$
复合中先作用 $\mathcal M^g$，再作用 $\Gamma_b$。每个右因子均为 $H_b$ 上的密度；$w_j=0$ 时 $A_j=0$，不对此项归一化。最后一式是在完整 $L\mid H_b$ 张量分割上的有限凸乘积态分解，因而 $\omega_{LR}$ 可分。$g=1$ 时右因子就是 $\Gamma_b(P_j)$，此结论不包含 $g=0$ 的可分性断言。任意有限维且不受作用的参考系统均可并入 $L$；假设只允许所写的固定顺序等距及无条件偏迹，不包含联合控制、读取间隔记录、条件化或恢复间隔的操作。

特别地，对 $X=\sigma_*$ 或 $X=P_0$、整数 $r\ge0$ 及 $a,g,b\ge1$，按 $H_r\otimes H_a\otimes H_g\otimes H_b$ 分组的
$$
\theta^X_{r;a,g,b}
=\operatorname{Tr}_{H_r,H_g}\Gamma_{r+a+g+b}(X)
$$
在完整 $H_a\mid H_b$ 分割上可分。这里左块之前恰有 $r$ 个被忽略输出，两块之间恰有 $g$ 个被忽略输出；再生成任意有限个右侧输出并忽略它们，也不改变此保留态。

第二，仅对平稳族 $\eta$，将输出从 $0$ 编号。在 $H_{d+1}$ 上令
$$
N_i=I_{H_i}\otimes|1\rangle\langle1|\otimes I_{H_{d-i}}
\qquad(0\le i\le d).
$$
对每个整数 $d\ge1$，两处占据均值均为 $\pi_1$，且
$$
\operatorname{Cov}_d
:=\operatorname{Tr}(\eta_{d+1}N_0N_d)-\pi_1^2
=\pi_0\pi_1(-\alpha^2)^d.
$$
此值在每个有限 $d$ 均非零，奇数距离为负、偶数距离为正，绝对值 $\pi_0\pi_1\alpha^{2d}$ 趋于零。对 $d\ge2$，忽略中间 $g=d-1\ge1$ 个位置后的双位置态可分，却不是乘积态；更一般地，任何相隔 $g\ge1$ 个被忽略位置的非空平稳有限块也不是乘积态。

证明。先在相关联合态上识别被忽略输出的作用。按记忆标准基展开
$$
\Omega=\sum_{i,k=0}^1\Omega_{ik}\otimes|i\rangle\langle k|,
\qquad
\Omega_{ik}=(I_L\otimes\langle i|)\Omega(I_L\otimes|k\rangle).
$$
真实的一步等距给出 $L\otimes B\otimes M$ 上的算子
$$
(I_L\otimes T)\Omega(I_L\otimes T^\dagger)
=\sum_{i,k=0}^1\Omega_{ik}\otimes|i\rangle\langle k|
\otimes|m_i\rangle\langle m_k|.
$$
新输出因子的 $|i\rangle\langle k|$ 的迹是 $\delta_{ik}$，故取该输出的偏迹恰好消去 $i\ne k$ 项，得到
$$
\operatorname{Tr}_B\bigl[(I_L\otimes T)\Omega(I_L\otimes T^\dagger)\bigr]
=\sum_{j=0}^1A_j\otimes P_j
=(\operatorname{Id}_L\otimes\mathcal M)(\Omega).
$$
这保留了 $\Omega$ 的两个对角算子块，并未以两边的边缘态替换 $\Omega$。

为在以后各步沿用此等式，直接使用命题 131.1 的相关偏迹恒等式并保留旁观因子 $L$。具体地，设 $E$ 为已发出而待忽略的因子，$Z$ 为 $L\otimes E\otimes M$ 上的算子，取 $E$ 的正交基 $(e_u)$ 并写
$$
D_{uv}=(I_L\otimes\langle e_u|\otimes I_M)
Z(I_L\otimes|e_v\rangle\otimes I_M)
\in\mathcal L(L\otimes M).
$$
在 $L\otimes E\otimes H_\ell\otimes M$ 的顺序下，取 $E$ 的对角块后求和给
$$
\begin{aligned}
&\operatorname{Tr}_E\bigl[
(I_L\otimes I_E\otimes T_\ell)Z
(I_L\otimes I_E\otimes T_\ell^\dagger)\bigr]\\
&\quad=\sum_u(I_L\otimes T_\ell)D_{uu}(I_L\otimes T_\ell^\dagger)\\
&\quad=(I_L\otimes T_\ell)(\operatorname{Tr}_E Z)
(I_L\otimes T_\ell^\dagger).
\end{aligned}
$$
所以先取旧因子的偏迹与继续只作用记忆的等距可交换。由一步公式归纳，
$$
\operatorname{Tr}_{H_g}\bigl[
(I_L\otimes T_g)\Omega(I_L\otimes T_g^\dagger)\bigr]
=(\operatorname{Id}_L\otimes\mathcal M^g)(\Omega)
=\sum_{j=0}^1A_j\otimes\mathcal M^{g-1}(P_j)
\qquad(g\ge1).
$$
再按顺序分组
$$
T_{g+b}=(I_{H_g}\otimes T_b)T_g,
$$
应用刚才的偏迹交换式，最后取记忆偏迹，便得到陈述中的 $\omega_{LR}$ 两个线性表达式。

对任意 $v\in L$，
$$
\langle v,A_jv\rangle
=(\langle v|\otimes\langle j|)\Omega(|v\rangle\otimes|j\rangle)\ge0,
\qquad \sum_j\operatorname{Tr}A_j=\operatorname{Tr}\Omega=1.
$$
因此 $A_j$ 正半定；若其迹为零，所有非负特征值之和为零，故 $A_j=0$。正权重项的 $A_j/w_j$ 是密度。命题 131.1 的记忆通道及输出通道均由等距共轭与偏迹给出，保持正性与迹；$P_j$ 是密度，故 $\Gamma_b(\mathcal M^{g-1}(P_j))$ 也是密度。由此得到所述有限凸分解，包括仅一个权重为正的情形。

这一步所用的测量后制备可分性是成熟的纠缠破坏通道数学：Michael Horodecki、Peter W. Shor、Mary Beth Ruskai，[General Entanglement Breaking Channels，arXiv:quant-ph/0302031v2](https://arxiv.org/abs/quant-ph/0302031v2)（该版本 PDF 的题头为 Entanglement Breaking Channels），定理 4 的 (A)、(B)、(D) 分别给出测量后制备表示、纠缠破坏性质及秩一 Kraus 表示的等价性。其保迹资格在这里由测量效应 $|j\rangle\langle j|$ 构成 POVM 以及
$$
C_j=|m_j\rangle\langle j|,\qquad
\mathcal M(X)=\sum_{j=0}^1 C_jXC_j^\dagger,\qquad
\sum_{j=0}^1 C_j^\dagger C_j=I_M
$$
落实；制备态为单位迹的 $P_j$。上面的相关算子块计算是该等价性在此固定生成器中的直接应用。

现在取 $L=H_a$、$\Omega=T_aXT_a^\dagger$。在 $H_a\otimes H_g\otimes H_b\otimes M$ 上，迭代的分组恒等式把此后的联合态识别为 $T_{a+g+b}XT_{a+g+b}^\dagger$，故前述 $\omega_{LR}$ 正是 $\Gamma_{a+g+b}(X)$ 忽略中间 $g$ 位后的首 $a$ 位、末 $b$ 位约化态。若还有被忽略的前缀 $r\ge0$，先按 $H_r\otimes H_a\otimes M$ 分组；命题 131.1 的同一偏迹恒等式给
$$
\Omega^{(r,a)}
:=\operatorname{Tr}_{H_r}(T_{r+a}XT_{r+a}^\dagger)
=T_a\mathcal M^r(X)T_a^\dagger.
$$
于是保留左块之前的实际记忆输入是 $\mathcal M^r(X)$，而左块发出后的实际输入是相关密度 $\Omega^{(r,a)}$。将其代入第一部分即得 $\theta^X_{r;a,g,b}$ 的可分性。$r=0$ 时 $H_0=\mathbb C$，式子同样成立。最后，命题 130.1 的已发出前缀不变性，或命题 131.1 的末位边缘相容恒等式，说明继续生成再忽略任意有限后缀保持所有这些约化态。这同时适用于纯边界族与平稳族。

下面计算平稳占据关联。令 $Y_i\in\{0,1\}$ 表示第 $i$ 个输出在计算基中的测量值，并用未归一化分支映射
$$
\mathcal J_j(X)=C_jXC_j^\dagger=X_{jj}P_j.
$$
它确实来自实际发出输出的投影，因为 $(\langle j|\otimes I_M)T=C_j$。旧输出上的投影可与以后仅作用记忆及新输出的步骤交换；依次收缩各个输出因子，对任意词 $w=(j_0,\ldots,j_{n-1})$ 有
$$
(\langle w|\otimes I_M)T_n=C_{j_{n-1}}\cdots C_{j_0},
$$
$$
\langle w|\eta_n|w\rangle
=\operatorname{Tr}\bigl[
(\mathcal J_{j_{n-1}}\circ\cdots\circ\mathcal J_{j_0})(\sigma_*)
\bigr].
$$
故这些分支的迹是完整相干态 $\eta_n$ 的实际对角概率，而非以去相干态代替原联合态所得的假设。

$\sigma_*$ 的两个对角元为
$$
(\sigma_*)_{00}=\pi_0\alpha+\pi_1=\pi_0,
\qquad (\sigma_*)_{11}=\pi_0\alpha^2=\pi_1.
$$
因此首次概率为 $(\pi_0,\pi_1)$；任一正概率分支发出 $j$ 后，归一化记忆为 $P_j$。由
$$
\operatorname{diag}P_0=(\alpha,\alpha^2),\qquad
\operatorname{diag}P_1=(1,0)
$$
得到以旧值标行、新值标列的转移矩阵
$$
K=\begin{pmatrix}\alpha&\alpha^2\\1&0\end{pmatrix},
\qquad \pi=(\pi_0,\pi_1),\qquad \pi K=\pi.
$$
更明确地，$\mathcal J_k(P_j)=K_{jk}P_k$，所以对所有词，包括概率为零的词，都有
$$
(\mathcal J_{j_{n-1}}\circ\cdots\circ\mathcal J_{j_0})(\sigma_*)
=\pi_{j_0}\left(\prod_{t=1}^{n-1}K_{j_{t-1}j_t}\right)P_{j_{n-1}},
$$
$$
\Pr(Y_0=j_0,\ldots,Y_{n-1}=j_{n-1})
=\pi_{j_0}\prod_{t=1}^{n-1}K_{j_{t-1}j_t}\qquad(n\ge1).
$$
空乘积取一。这一未归一化恒等式处理零分支而无需除以零，且给出实际计算基词律的平稳 Markov 递推。

由于 $\pi_1>0$，可定义
$$
q_d=\Pr(Y_d=1\mid Y_0=1),\qquad q_0=1.
$$
转移到 $1$ 的概率从 $0$ 出发为 $\alpha^2$，从 $1$ 出发为零，故
$$
q_{d+1}=\alpha^2(1-q_d),\qquad
\pi_1=\alpha^2(1-\pi_1),\qquad
q_{d+1}-\pi_1=-\alpha^2(q_d-\pi_1).
$$
从 $q_0-\pi_1=\pi_0$ 归纳得到
$$
q_d=\pi_1+\pi_0(-\alpha^2)^d\qquad(d\ge0).
$$
每个位置的占据均值由 $\pi K=\pi$ 等于 $\pi_1$；$N_0N_d$ 的联合均值则为
$$
\operatorname{Tr}(\eta_{d+1}N_0N_d)
=\Pr(Y_0=1,Y_d=1)=\pi_1q_d.
$$
减去 $\pi_1^2$ 即得协方差公式。特别地，$q_1=0$，且
$$
\operatorname{Cov}_1=-\pi_0\pi_1\alpha^2=-\pi_1^2,
$$
与相邻词 $11$ 的概率为零一致。$0<\alpha<1$ 及 $\pi_0\pi_1>0$ 给出所有有限距离的非零性、符号交替与衰减极限。

若 $d\ge2$，第一部分取 $a=b=1$、$g=d-1$、$X=\sigma_*$ 即得端点态可分；乘积态上两个局部占据算子的期望乘法分解，协方差必为零，故这里的端点态不是乘积态。对两个非空平稳块，取左块末位与右块首位，距离为 $g+1$；平稳边缘相容性给出同一个非零协方差，因而两块也不是乘积态。

这里 $\langle m_0,m_1\rangle=\sqrt\alpha\ne0$，分解指标 $j$ 不构成可完美读取的记忆标志。上述可分性不蕴含零量子失协、固定乘积基中的对角性或量子条件独立性，也不判定整个多位置态的多体纠缠；占据协方差的非零尾不等于纠缠，亦不给出所有关联的有限支撑。$d$ 只计输出位置间距，不表示物理长度或时间。结合命题 132.1 的 $\eta_2$ 及每个 $\beta_{n,2}$ 的相邻纠缠，同一生成器中相邻输出纠缠、平稳族在每个有限距离的非零衰减占据关联，与无条件忽略任意含 $g\ge1$ 个输出的间隔后两侧有限块的可分性同时成立。证毕。

## 追加锚（本行以下为增补区）

## 134. 选择性局部测量下的有限间隔端点纠缠

**命题 134.1（纯边界的指定纠缠分支与无条件可分平均）。** 沿用命题 130.1 的固定生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
两份二维空间均取正交标准基 $|0\rangle,|1\rangle$，$\dagger$ 表示伴随。记
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
T_0=I_M,\qquad T_{n+1}=(I_{H_n}\otimes T)T_n,\qquad
\Xi_n=T_nm_0.
$$
对整数 $g\ge0$，从纯初始记忆 $m_0$ 恰好生成 $n=g+2$ 个输出，按
$$
B_L\otimes H_g\otimes B_R\otimes M
$$
分组：$L$、$R$ 分别是第一个、最后一个已发出的输出 qubit，$M$ 是生成结束后的活动记忆。左端点之前没有被忽略的输出前缀。假设生成结束后可以分别测量每个内部输出及最终活动记忆，并可访问这些测量的经典结果记录以选择分支；两个端点均保留。

在内部输出上使用正交基
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
在最终活动记忆上使用计算基。对全部 $\varepsilon\in\{+,-\}^g$、$k\in\{0,1\}$，令 $|\varepsilon\rangle=|\varepsilon_1\rangle\otimes\cdots\otimes|\varepsilon_g\rangle$，定义实际联合向量的收缩
$$
v_{\varepsilon,k}
=(I_{B_L}\otimes\langle\varepsilon|\otimes I_{B_R}\otimes\langle k|)\Xi_{g+2}
\in B_L\otimes B_R.
$$
$g=0$ 时内部字符串为空，$|\varepsilon\rangle=1\in H_0$，其 bra 为恒等收缩。各个被测因子上的物理投影彼此交换，其联合投影为
$$
Q_{\varepsilon,k}
=I_{B_L}\otimes|\varepsilon\rangle\langle\varepsilon|
 \otimes I_{B_R}\otimes|k\rangle\langle k|.
$$

选择全部内部结果为 $+$ 且最终记忆结果为 $0$，记 $v_g=v_{(+,\ldots,+),0}$。令
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
v_g=\sum_{i,j=0}^1 C_g(i,j)|i\rangle_L\otimes|j\rangle_R,
$$
其中系数矩阵以左端点位值为行、右端点位值为列。则
$$
C_g=\frac{s^{g+3}}{(\sqrt2)^g}J^{g+1},\qquad
C_0=\alpha sJ,\qquad
\det C_g=-\alpha^3\left(-\frac\alpha2\right)^g\ne0.
$$
该联合事件的 Born 概率及条件密度为
$$
p_g=\|v_g\|^2=\operatorname{Tr}(C_gC_g^\dagger),\qquad
0<p_g<1,\qquad
\theta_g=\frac{|v_g\rangle\langle v_g|}{p_g}.
$$
这里可分性始终指完整 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$ 上的有限凸可分性：密度 $\omega$ 可分，当且仅当存在有限个权重 $\lambda_a\ge0$、$\sum_a\lambda_a=1$ 及各自二维空间上的密度 $\sigma_a,\tau_a$，使
$$
\omega=\sum_a\lambda_a\,\sigma_a\otimes\tau_a.
$$
对每个有限 $g\ge0$，$\theta_g$ 均不可分；它的密度算子秩为 $1$，而其系数矩阵秩、亦即 Schmidt 秩为 $2$。

对完整测量的每个结果令 $p_{\varepsilon,k}=\|v_{\varepsilon,k}\|^2$，仅在 $p_{\varepsilon,k}>0$ 时定义 $\theta_{\varepsilon,k}=|v_{\varepsilon,k}\rangle\langle v_{\varepsilon,k}|/p_{\varepsilon,k}$。则
$$
\begin{aligned}
\Theta_g
&:=\operatorname{Tr}_{H_g,M}|\Xi_{g+2}\rangle\langle\Xi_{g+2}|\\
&=\sum_{\varepsilon\in\{+,-\}^g}\sum_{k=0}^1
 |v_{\varepsilon,k}\rangle\langle v_{\varepsilon,k}|\\
&=\sum_{\substack{\varepsilon\in\{+,-\}^g,\ k\in\{0,1\}\\p_{\varepsilon,k}>0}}
 p_{\varepsilon,k}\theta_{\varepsilon,k},\qquad
\sum_{\varepsilon,k}p_{\varepsilon,k}=1.
\end{aligned}
$$
零概率项在未归一化求和中为零。对 $g\ge1$，此无条件端点密度 $\Theta_g$ 可分；这一可分性结论不包含 $g=0$。

证明。记 $W_n$ 为长度 $n$ 的不含相邻 $11$ 的二进制词集，$W_n^0$ 为其中末位为 $0$ 的词集。命题 130.1 在完整输出与最终记忆空间上给出
$$
\Xi_n
=s^{n+1}\sum_{w\in W_n}|w\rangle\otimes|0\rangle
 +s^{n+2}\sum_{w\in W_n^0}|w\rangle\otimes|1\rangle
\qquad(n\ge1).
$$
取 $n=g+2$。最终记忆的 $\langle0|$ 选出第一列；每个内部计算基位值与 $\langle+|$ 的内积均为 $1/\sqrt2$，所以
$$
C_g(i,j)=\frac{s^{g+3}}{(\sqrt2)^g}
\#\{u\in\{0,1\}^g:(i,u,j)\in W_{g+2}\}.
$$
这是对完整联合向量的线性收缩。这里的 $1/\sqrt2$ 是基向量的内积，不是单次结果具有概率 $1/2$ 或结果相互独立的假设。

$J_{ab}$ 恰为相邻位值 $a,b$ 的相容性指示数。展开矩阵乘法，固定 $x_0=i$、$x_{g+1}=j$，有
$$
(J^{g+1})_{ij}
=\sum_{(x_1,\ldots,x_g)\in\{0,1\}^g}
 \prod_{t=0}^{g}J_{x_tx_{t+1}}.
$$
每个乘积在对应整词合法时为 $1$，否则为 $0$，故此式正好计数上面的内部词。$g=0$ 时求和只有空内部词这一项，乘积为 $J_{ij}$，从而同样得到 $C_0=s^3J=\alpha sJ$。于是所有 $g\ge0$ 的系数矩阵公式成立。由于 $\det J=-1$，行列式的乘法性给
$$
\det C_g
=\frac{s^{2g+6}}{2^g}(\det J)^{g+1}
=\frac{\alpha^{g+3}}{2^g}(-1)^{g+1}
=-\alpha^3\left(-\frac\alpha2\right)^g.
$$
$\alpha>0$，故任意有限 $g$ 下该行列式均不为零，特别地 $v_g\ne0$。

命题 130.1 给 $\|\Xi_{g+2}\|=1$。正交投影是压缩，且所选测量因子均为单位向量，故
$$
p_g=\langle\Xi_{g+2},Q_{(+,\ldots,+),0}\Xi_{g+2}\rangle
=\|v_g\|^2\le1.
$$
按端点正交基展开范数，得到 $\|v_g\|^2=\sum_{i,j}|C_g(i,j)|^2=\operatorname{Tr}(C_gC_g^\dagger)$；$v_g\ne0$ 给 $p_g>0$。为证严格上界，在上面的第二记忆列中，全零输出词的系数为 $s^{g+4}$。因此最终记忆为 $1$ 的边缘概率至少为 $s^{2g+8}>0$，而所选事件要求记忆为 $0$，所以
$$
p_g\le\Pr(M=0)=1-\Pr(M=1)\le1-s^{2g+8}<1.
$$
这个边缘概率下界来自联合向量的正交基展开，无需测量保留的端点。归一化后，$\theta_g$ 为正、迹为 $1$，其像恰为 $\mathbb Cv_g$，所以密度秩为 $1$。

现证明这种纯密度不可能具有有限凸乘积分解。设 $\psi=v_g/\sqrt{p_g}$，并反设 $|\psi\rangle\langle\psi|=\sum_a\lambda_a\sigma_a\otimes\tau_a$。对每个二维密度作有限谱分解，再展开张量积并删去零权重项，便得到
$$
|\psi\rangle\langle\psi|
=\sum_{b=1}^{N}q_b|a_b\otimes b_b\rangle\langle a_b\otimes b_b|,
\qquad q_b>0,\qquad\sum_{b=1}^{N}q_b=1,
$$
其中 $a_b,b_b$ 为各自空间中的单位向量，$N$ 有限。对任意 $z\perp\psi$ 测试二次型，
$$
0=\sum_{b=1}^{N}q_b\,|\langle z,a_b\otimes b_b\rangle|^2.
$$
每项非负，故每个正权重乘积向量都与全部 $\psi^\perp$ 正交，从而属于同一条射线 $\mathbb C\psi$。由于至少有一个正权重项，$\psi$ 本身必为乘积向量。非零乘积向量的系数矩阵为两个非零列向量的外积 $ab^{\mathsf T}$，秩为 $1$；但 $\psi$ 的系数矩阵为 $C_g/\sqrt{p_g}$，其行列式不为零，秩为 $2$，矛盾。因此 $\theta_g$ 不可分。上述论证使用的是两个完整输出因子的张量分割；合法词集只规定联合向量的支撑，不另给合法支撑赋予张量分解。

最后，$\{|\varepsilon\rangle\otimes|k\rangle\}_{\varepsilon,k}$ 是全部被测因子 $H_g\otimes M$ 的正交标准基。各局部投影作用于互不相同的因子，故彼此交换，并满足 $\sum_{\varepsilon,k}Q_{\varepsilon,k}=I$。按此基展开实际 $\Xi_{g+2}$，其每个端点系数向量就是 $v_{\varepsilon,k}$；在 $H_g,M$ 上取偏迹时，不同基指标的交叉项消失，遂得
$$
\operatorname{Tr}_{H_g,M}|\Xi_{g+2}\rangle\langle\Xi_{g+2}|
=\sum_{\varepsilon,k}|v_{\varepsilon,k}\rangle\langle v_{\varepsilon,k}|.
$$
取迹给全部联合 Born 概率之和为 $1$，对正概率项再归一化即得陈述中的加权平均。这个恒等式对所有结果求和；归一化分支的均匀平均或仅对所选成功结果作平均，均不是此偏迹恒等式。

令 $P_0=|m_0\rangle\langle m_0|$。由命题 130.1，$\operatorname{Tr}_M|\Xi_{g+2}\rangle\langle\Xi_{g+2}|=\rho_{g+2}=\Gamma_{g+2}(P_0)$。因而在相同的输出分组下，$\Theta_g=\operatorname{Tr}_{H_g}\rho_{g+2}$ 正是命题 133.1 中取 $X=P_0$、$r=0$、$a=b=1$ 的 $\theta^{P_0}_{0;1,g,1}$。该命题对 $g\ge1$ 给出完整 $B_L\mid B_R$ 分割上的有限凸乘积态分解，故这里同一纯边界族的 $\Theta_g$ 可分。

可分性的量词是存在一个有限凸乘积态分解，并不要求一个密度的每个纯态系综都由乘积向量组成。因此，对 $g\ge1$，可依据完整经典测量记录选择正概率的纠缠分支 $\theta_g$，与忘却全部记录后得到可分的 Born 平均 $\Theta_g$ 相容。证毕。

## 追加锚（本行以下为增补区）

## 135. 指定纠缠分支的联合概率与固定乘积态极限

**命题 135.1（有限间隔纠缠、消失的联合概率与固定端点极限）。** 沿用命题 134.1 的纯边界与生成器：
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
对每个整数 $g\ge0$，从初始活动记忆 $m_0$ 恰好生成 $g+2$ 个输出，保留第一个及最后一个已发出的 qubit $L,R$；左端点之前没有被丢弃的输出前缀。假设可访问全部内部输出的测量记录及最终活动记忆：在每个内部输出的正交基 $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$ 中选择结果 $+$，在最终活动记忆的计算基中选择结果 $0$。此处选中的记忆向量是 $|0\rangle$，不是非正交记忆标签 $m_0$；两个端点始终都是已发出的输出。所有 $B_L\otimes B_R$ 通过各自带标签的计算基识别为同一个固定空间 $\mathbb C^2\otimes\mathbb C^2$。

以命题 134.1 的完整联合向量 $\Xi_{g+2}$ 定义
$$
v_g=(I_{B_L}\otimes\langle+|^{\otimes g}\otimes I_{B_R}\otimes\langle0|)\Xi_{g+2}
=\operatorname{vec}_{LR}(C_g),\qquad
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C(i,j)|i\rangle_L\otimes|j\rangle_R.
$$
$g=0$ 时内部 bra 是空张量积的恒等收缩。矩阵的行指标为 $L$ 位值，列指标为 $R$ 位值。记 $\operatorname{adj}(A)$ 为共轭转置，$\operatorname{outer}(x)=|x\rangle\langle x|$，并在本命题内令
$$
p_g=\|v_g\|^2=\operatorname{Tr}(C_g\operatorname{adj}(C_g)),\qquad
\psi_g=\frac{v_g}{\sqrt{p_g}},\qquad
\theta_g=\operatorname{outer}(\psi_g).
$$
这里 $p_g$ 是上述整个记录的联合 Born 概率，包含最终记忆结果 $0$ 的概率，不是预先条件于记忆成功后的概率，也不是命题 131.1 的记忆混合参数；$\theta_g$ 只表示固定端点空间上的选中密度。命题 134.1 已给出
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
\kappa_g=\frac{s^{g+3}}{(\sqrt2)^g},\qquad
C_g=\kappa_gJ^{g+1},\qquad \det C_g\ne0,\qquad 0<p_g<1.
$$

令
$$
\mathrm{den}=1+\alpha^2,\qquad
u_+=\frac{|0\rangle+\alpha|1\rangle}{\sqrt{\mathrm{den}}},\qquad
u_-=\frac{-\alpha|0\rangle+|1\rangle}{\sqrt{\mathrm{den}}},\qquad
e_+=u_+\otimes u_+,\qquad e_-=u_-\otimes u_-,
$$
$$
\varepsilon_g=(-1)^{g+1},\qquad t_g=\alpha^{2g+2},\qquad
b=\frac1{2\alpha},\qquad r_g=\kappa_g\alpha^{-g-1}>0.
$$
则 $u_+,u_-$ 是实正交单位向量，且有固定基展开
$$
C_g=r_g\bigl(\operatorname{outer}(u_+)+\varepsilon_gt_g\operatorname{outer}(u_-)\bigr),\qquad
\psi_g=\frac{e_++\varepsilon_gt_ge_-}{\sqrt{1+t_g^2}},\qquad
r_g^2=\alpha b^g.
$$
相对符号在偶数 $g$ 时为负，在奇数 $g$ 时为正。联合概率的精确式为
$$
p_g=\frac{\alpha^{g+3}}{2^g}
\bigl(\alpha^{-2g-2}+\alpha^{2g+2}\bigr)
=\alpha b^g\bigl(1+\alpha^{4g+4}\bigr).
$$
两端约化密度 $\operatorname{Tr}_{B_R}\theta_g$、$\operatorname{Tr}_{B_L}\theta_g$ 在各自的 $u_+,u_-$ 基下具有相同的两个特征值
$$
w_+=\frac1{1+t_g^2},\qquad w_-=\frac{t_g^2}{1+t_g^2}.
$$
每个有限 $g$ 下二者均为正；非负 Schmidt 系数是 $\sqrt{w_+},\sqrt{w_-}$。因此 $\theta_g$ 的密度算子秩为 $1$，而系数矩阵及两端约化密度的秩均为 $2$，$\theta_g$ 对完整 $B_L\mid B_R$ 分割不可分。

对有限维矩阵采用迹范数及密度间迹距离
$$
\operatorname{traceNorm}(A)=\operatorname{Tr}\sqrt{\operatorname{adj}(A)A},\qquad
D(\rho,\sigma)=\frac12\operatorname{traceNorm}(\rho-\sigma),
$$
其中平方根取唯一正半定平方根，故其迹为实数。这与 [FiniteTraceDistance 的 traceNorm、traceDistance](../../../D5/S3/Quantum/Foundation/FiniteTraceDistance.lean) 的约定一致。令与 $g$ 无关的纯乘积密度为
$$
\Pi_+=\operatorname{outer}(e_+)
=\operatorname{outer}(u_+)\otimes\operatorname{outer}(u_+).
$$
则
$$
D(\theta_g,\Pi_+)=\frac{t_g}{\sqrt{1+t_g^2}},\qquad
0<D(\theta_g,\Pi_+)\le\alpha^{2g+2},
$$
并且沿全部非负整数指标有
$$
0<p_g\le3\alpha^3b^g\longrightarrow0,\qquad
w_-\longrightarrow0,\qquad
D(\theta_g,\Pi_+)\longrightarrow0.
$$
故这个指定分支在每个有限间隔仍纠缠，同时联合成功概率趋零，密度在固定四维端点空间的迹距离下趋于一个固定纯乘积态。上述距离针对指定的 $\Pi_+$，不是对可分密度的最小化，也不是对所有可分密度的距离下界。

证明。由 $\alpha+\alpha^2=1$，有 $1/2<\alpha<1$ 及 $1+\alpha=\alpha^{-1}$。向量 $u_+,u_-$ 的范数平方均为 $1$，内积为 $(-\alpha+\alpha)/\mathrm{den}=0$。直接矩阵乘法给出
$$
J\begin{pmatrix}1\\\alpha\end{pmatrix}
=\begin{pmatrix}1+\alpha\\1\end{pmatrix}
=\alpha^{-1}\begin{pmatrix}1\\\alpha\end{pmatrix},\qquad
J\begin{pmatrix}-\alpha\\1\end{pmatrix}
=\begin{pmatrix}1-\alpha\\-\alpha\end{pmatrix}
=-\alpha\begin{pmatrix}-\alpha\\1\end{pmatrix}.
$$
这两个特征对亦见 [FibonacciEigen 的 fibonacci_substitution_spec](../../../D5/S1/Scale/FibonacciEigen.lean)：其中扩张向量为 $(\alpha^{-1},1)$，收缩向量为 $(-\alpha,1)$，分别乘以 $\alpha/\sqrt{\mathrm{den}}$、$1/\sqrt{\mathrm{den}}$ 即为这里的 $u_+,u_-$。因它们构成二维空间的正交单位基，谱分解给
$$
J^{g+1}=\alpha^{-g-1}\operatorname{outer}(u_+)
+(-\alpha)^{g+1}\operatorname{outer}(u_-).
$$
将此式代入命题 134.1 的 $C_g=\kappa_gJ^{g+1}$，提出正因子 $r_g$，即得所述 $C_g$ 展开。

按上述行列指标约定，对一般复向量 $u$，
$$
\operatorname{vec}_{LR}(\operatorname{outer}(u))
=u\otimes\overline u,
$$
其中横线表示计算基中的逐坐标共轭。这里 $u_+,u_-$ 的坐标全为实数，才有 $\operatorname{vec}_{LR}(\operatorname{outer}(u_\pm))=e_\pm$。由局部正交性，$e_+,e_-$ 也是正交单位向量，故
$$
v_g=r_g(e_++\varepsilon_gt_ge_-),\qquad
p_g=r_g^2(1+t_g^2),\qquad
\psi_g=\frac{e_++\varepsilon_gt_ge_-}{\sqrt{1+t_g^2}}.
$$
因 $s^2=\alpha$，
$$
r_g^2=\frac{s^{2g+6}}{2^g}\alpha^{-2g-2}
=\frac{\alpha^{1-g}}{2^g}=\alpha b^g,
$$
代入 $p_g$ 即得两个概率闭式。归一化因子 $(\sqrt2)^{-g}$ 来自每个内部投影 bra；最终记忆的 $\langle0|$ 已在 $C_g$ 中，未作任何记忆成功条件化。此计算只使用联合向量的 Born 范数，不假设各结果等概率或相互独立。

将纯密度展开为
$$
\theta_g=\frac{
\operatorname{outer}(e_+)+t_g^2\operatorname{outer}(e_-)
+\varepsilon_gt_g\bigl(|e_+\rangle\langle e_-|+|e_-\rangle\langle e_+|\bigr)
}{1+t_g^2}.
$$
在右端取偏迹时，交叉项分别乘以 $\langle u_-,u_+\rangle$、$\langle u_+,u_-\rangle$，均为零；对角项乘以相应单位向量的范数平方。因此
$$
\operatorname{Tr}_{B_R}\theta_g
=w_+\operatorname{outer}(u_+)_L+w_-\operatorname{outer}(u_-)_L.
$$
在左端取偏迹同理得到
$$
\operatorname{Tr}_{B_L}\theta_g
=w_+\operatorname{outer}(u_+)_R+w_-\operatorname{outer}(u_-)_R.
$$
$t_g>0$ 给两个正特征值。带符号的固定基展开中，把 $\varepsilon_g$ 吸收到右端第二个局部向量，得到真正的非负 Schmidt 展开
$$
\psi_g=\sqrt{w_+}\,u_+\otimes u_+
+\sqrt{w_-}\,u_-\otimes(\varepsilon_gu_-).
$$
每侧两个局部向量仍正交归一，故 Schmidt 秩为 $2$；不可分性亦与命题 134.1 的非零行列式结论一致。整个密度仍是一个单位向量的外积，故秩为 $1$。相对符号虽在两端约化谱中消失，却仍保留在 $\theta_g$ 的交叉项中。

在有序正交基 $(e_+,e_-)$ 所张成的子空间上，差 $\theta_g-\Pi_+$ 的矩阵为
$$
\frac1{1+t_g^2}
\begin{pmatrix}
-t_g^2&\varepsilon_gt_g\\
\varepsilon_gt_g&t_g^2
\end{pmatrix},
$$
并在其正交补上为零。这个实对称块的迹为零，行列式为 $-t_g^2/(1+t_g^2)$，故两个特征值恰为
$$
\lambda_+=\frac{t_g}{\sqrt{1+t_g^2}},\qquad
\lambda_-=-\frac{t_g}{\sqrt{1+t_g^2}}.
$$
对 Hermitian 矩阵，$\operatorname{adj}(A)A=A^2$；在正交特征基中，其正半定平方根的特征值为原特征值的绝对值。因此取以上两个绝对值之和的一半，便得到
$$
D(\theta_g,\Pi_+)=\frac{t_g}{\sqrt{1+t_g^2}}\le t_g.
$$
这直接计算了两个已归一化密度的差，不使用保迹映射的压缩性去处理非线性的分支归一化。

边界 $g=0$ 的内部测量为空，最终记忆测量仍在。由 $J$ 的三个非零矩阵元，
$$
C_0=s^3J,\qquad p_0=3\alpha^3,\qquad
\psi_0=\frac{|00\rangle+|01\rangle+|10\rangle}{\sqrt3}.
$$
又因 $J^2=\begin{pmatrix}2&1\\1&1\end{pmatrix}$，
$$
C_1=\frac{s^4}{\sqrt2}\begin{pmatrix}2&1\\1&1\end{pmatrix},\qquad
p_1=\frac{7\alpha^4}{2},\qquad
\psi_1=\frac{2|00\rangle+|01\rangle+|10\rangle+|11\rangle}{\sqrt7}.
$$
两式中的概率都保留了最终记忆结果 $0$ 的概率因子。

最后，由 $1/2<\alpha<1$ 得 $0<b<1$。又由 $\alpha^2=1-\alpha$，可得 $\alpha^4=2-3\alpha$，从而
$$
\alpha(1+\alpha^4)=3\alpha(1-\alpha)=3\alpha^3.
$$
对所有 $g\ge0$，$\alpha^{4g+4}\le\alpha^4$，所以
$$
0<p_g=\alpha b^g(1+\alpha^{4g+4})\le3\alpha^3b^g,\qquad
0<w_-\le t_g^2=\alpha^{4g+4},\qquad
0<D(\theta_g,\Pi_+)\le\alpha^{2g+2}.
$$
由于 $b$、$\alpha^2$、$\alpha^4$ 均严格介于 $0$ 与 $1$，三个右端是趋零的几何序列；夹逼即给沿全部整数指标的三个极限，而非只沿某个奇偶子列的极限。尤其不存在对所有 $g$ 都成立的联合成功概率正下界，也不存在到这个固定 $\Pi_+$ 的距离正下界；这不改变任何有限 $g$ 下的精确非零性及纠缠性。

这里比较的是每个有限 $g$ 的正概率条件态在同一端点空间内的极限，不是增长的完整输出空间中的极限，也没有对一个概率为零的无限测量事件定义条件态。命题 134.1 的 $\Theta_g$ 仍是对完整结果集按联合 Born 概率求和的无条件端点密度，与选中的 $\theta_g$ 为不同对象。证毕。

## 追加锚（本行以下为增补区）

## 136. 最终记忆未读时的内部选择与有限间隔端点纠缠

**命题 136.1（只选择内部全加结果的秩二纠缠态）。** 沿用命题 130.1、134.1、135.1 的同一个纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1).
$$
两份二维空间均取正交标准基。记 $\operatorname{adj}(A)$ 为共轭转置，$\operatorname{outer}(x)=|x\rangle\langle x|$，并令
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad T_0=I_M,\qquad
T_{n+1}=(I_{H_n}\otimes T)T_n,\qquad \Xi_n=T_nm_0.
$$
对每个整数 $g\ge0$，恰好生成 $g+2$ 个输出，按输出在前、活动记忆在后的次序分组为
$$
B_L\otimes H_g\otimes B_R\otimes M.
$$
$L,R$ 分别为第一个、最后一个已发出的 qubit，左端点之前没有被忽略的前缀，初始记忆始终为纯向量 $m_0$。假设可以在每个内部输出上测量正交基
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
访问这些内部结果并选择全部为 $+$ 的记录。最终活动记忆完全以偏迹忽略，不测量它，也不选择其计算基结果 $0$ 或记忆向量 $m_0$。两个端点均保留，可分性取完整 $B_L\mid B_R$ 分割：密度可分是指它有有限凸乘积密度分解。

内部全加记录收缩后的未归一化向量为
$$
\chi_g=(I_{B_L}\otimes\langle+|^{\otimes g}\otimes I_{B_R}\otimes I_M)\Xi_{g+2}
\in B_L\otimes B_R\otimes M,
$$
其中 $g=0$ 的内部 bra 是空张量积上的恒等收缩。沿用命题 134.1、135.1 的系数矩阵，定义
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
\kappa_g=\frac{s^{g+3}}{(\sqrt2)^g},\qquad C_g=\kappa_gJ^{g+1},\qquad
E_0=\begin{pmatrix}1&0\\0&0\end{pmatrix},
$$
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C(i,j)|i\rangle_L\otimes|j\rangle_R,
\qquad \|C\|_F^2=\operatorname{Tr}(C\operatorname{adj}(C)).
$$
行指标为 $L$ 位值，列指标为 $R$ 位值，故右乘 $E_0$ 选择最后一个已发出位值为 $0$ 的列。则
$$
\chi_g=\operatorname{vec}_{LR}(C_g)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_gE_0)\otimes|1\rangle,
$$
$$
Q_g:=\operatorname{Tr}_M\operatorname{outer}(\chi_g)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_g))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_gE_0)),
$$
$$
q_g:=\operatorname{Tr}Q_g
=\|C_g\|_F^2+\alpha\|C_gE_0\|_F^2,\qquad
0<q_g\le1,\qquad \theta_g^{\mathrm{unread}}:=\frac{Q_g}{q_g}.
$$
这里 $q_g$ 是只含内部全加记录的 Born 概率，$\theta_g^{\mathrm{unread}}$ 是最终记忆未读的实际条件密度；它们分别不同于命题 134.1、135.1 中额外选择最终记忆结果 $0$ 的 $p_g$ 与纯条件密度 $\theta_g$。对每个有限 $g\ge0$，$\theta_g^{\mathrm{unread}}$ 的算子秩为 $2$，且在完整 $\mathbb C^2\otimes\mathbb C^2$ 上纠缠。空内部记录满足
$$
q_0=1,\qquad \alpha^3(3+2\alpha)=1,\qquad
Q_0=\theta_0^{\mathrm{unread}}=\Gamma_2(P_0)=G_0,
\qquad P_0=\operatorname{outer}(m_0),
$$
其中 $\Gamma_2$ 与 $G_0$ 是命题 132.1 的同名对象。

对全部内部记录 $e\in\{+,-\}^g$，令 $|e\rangle=|e_1\rangle\otimes\cdots\otimes|e_g\rangle$，并在同一个相关联合向量上定义
$$
\chi_e=(I_{B_L}\otimes\langle e|\otimes I_{B_R}\otimes I_M)\Xi_{g+2},\qquad
Q_e=\operatorname{Tr}_M\operatorname{outer}(\chi_e),\qquad q_e=\operatorname{Tr}Q_e.
$$
则完整结果的 Born 平均满足
$$
\overline\Theta_g:=\sum_{e\in\{+,-\}^g}Q_e
=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
=\sum_{\substack{e\in\{+,-\}^g\\q_e>0}}q_e\frac{Q_e}{q_e},
\qquad \sum_e q_e=1.
$$
未归一化求和包含全部记录，零概率项只从归一化表达式中省去。对 $g\ge1$，$\overline\Theta_g$ 可分；$g=0$ 时它等于上述纠缠密度 $G_0$。

证明。令 $W_n$ 为不含相邻 $11$ 的长度 $n$ 二进制词集，$W_n^0$ 为其中末位为 $0$ 的词集。命题 130.1 的实际联合态两列展开给
$$
\Xi_n=s^{n+1}\sum_{w\in W_n}|w\rangle\otimes|0\rangle
+s^{n+2}\sum_{w\in W_n^0}|w\rangle\otimes|1\rangle
\qquad(n\ge1),\qquad \|\Xi_n\|=1.
$$
取 $n=g+2$，在两列上施加同一组归一化内部 bra。对每个内部计算基词 $u$，有 $\langle+|^{\otimes g}|u\rangle=(\sqrt2)^{-g}$。因此第一列的端点系数为
$$
\kappa_g\#\{u\in\{0,1\}^g:(i,u,j)\in W_{g+2}\}
=C_g(i,j),
$$
这里最后一个等号正是命题 134.1 的相容矩阵计数 $(J^{g+1})_{ij}$。第二列仍只对末位为 $0$ 的合法词求和，故其系数为
$$
\frac{s^{g+4}}{(\sqrt2)^g}
\#\{u\in\{0,1\}^g:(i,u,j)\in W_{g+2},\ j=0\}
=sC_g(i,j)\,\mathbf1_{\{j=0\}}
=s(C_gE_0)(i,j).
$$
这同时给出所述 $\chi_g$，包括只有空内部词的 $g=0$。此处把最终记忆写在计算基中只是同一向量的坐标展开，不是额外实施一次记忆测量；两列均保留原振幅，未分别归一化。正交记忆基的交叉项在偏迹中消失，而第二列的平方系数为 $s^2=\alpha$，遂得 $Q_g$ 与 $q_g$ 的公式。内部 bra 的因子 $1/\sqrt2$ 是内积，不假设各结果等概率或独立。

由 $\det J=-1$、$\kappa_g>0$，
$$
\det C_g=\kappa_g^2(-1)^{g+1}\ne0.
$$
故 $C_g$ 可逆且非零，$q_g\ge\|C_g\|_F^2>0$。内部全加事件在完整联合空间上的正交投影是
$$
\mathsf P_g=I_{B_L}\otimes\operatorname{outer}(|+\rangle^{\otimes g})
\otimes I_{B_R}\otimes I_M.
$$
于是
$$
q_g=\|\chi_g\|^2=\langle\Xi_{g+2},\mathsf P_g\Xi_{g+2}\rangle\le1,
$$
因为 $\Xi_{g+2}$ 为单位向量。$Q_g$ 为正半定，除以其正迹得到密度。$g=0$ 时 $\mathsf P_0=I$，故 $q_0=1$。直接由 $C_0=s^3J$，在字典序 $00,01,10,11$ 下有
$$
Q_0=\alpha^3
\begin{pmatrix}
1+\alpha&1&1+\alpha&0\\
1&1&1&0\\
1+\alpha&1&1+\alpha&0\\
0&0&0&0
\end{pmatrix}
=\begin{pmatrix}
\alpha^2&\alpha^3&\alpha^2&0\\
\alpha^3&\alpha^3&\alpha^3&0\\
\alpha^2&\alpha^3&\alpha^2&0\\
0&0&0&0
\end{pmatrix}=G_0.
$$
此处 $\alpha^3(1+\alpha)=\alpha^2$；取迹给 $\alpha^3(3+2\alpha)=2\alpha^2+\alpha^3=1$，最后一步用 $\alpha^3=2\alpha-1$。这与命题 132.1 的无条件首两位密度 $\Gamma_2(P_0)$ 完全一致。

现以一个局部合同变换检验混合态可分性。设
$$
A_g=C_g^{-1},\qquad F_g=A_g\otimes I_{B_R},\qquad
\phi=|00\rangle+|11\rangle.
$$
按行优先的向量化约定，对任意两个二阶矩阵 $A,C$，逐坐标展开有
$$
(A\otimes I_{B_R})\operatorname{vec}_{LR}(C)
=\sum_{k,j}\left(\sum_i A(k,i)C(i,j)\right)|k\rangle_L\otimes|j\rangle_R
=\operatorname{vec}_{LR}(AC).
$$
故 $A_gC_g=I$、$A_gC_gE_0=E_0$ 给出
$$
F_gQ_g\operatorname{adj}(F_g)=S,\qquad
S:=\operatorname{outer}(\phi)+\alpha\operatorname{outer}(|00\rangle),
$$
$$
F_g\theta_g^{\mathrm{unread}}\operatorname{adj}(F_g)=\frac{S}{q_g},\qquad
\operatorname{Tr}\left(\frac{S}{q_g}\right)=\frac{2+\alpha}{q_g}>1.
$$
这里 $S/q_g$ 是未归一化正算子，不将分母换成 $2+\alpha$。$F_g$ 只用于代数合同变换；本命题没有实施此滤波，也不赋予未缩放的逆矩阵任何确定性或迹不增操作的资格。

沿用命题 132.1 的偏转置约定，在右端计算基上定义并线性延伸
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
在相同字典序下直接得到
$$
\operatorname{PT}_R(S)=
\begin{pmatrix}
1+\alpha&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix}.
$$
单位向量 $v=(|01\rangle-|10\rangle)/\sqrt2$ 满足
$$
\langle v,\operatorname{PT}_R(S)v\rangle=-1,\qquad
\left\langle v,\operatorname{PT}_R\left(\frac{S}{q_g}\right)v\right\rangle=-\frac1{q_g}<0.
$$

反设实际密度可分，即存在有限分解
$$
\theta_g^{\mathrm{unread}}=\sum_{a=1}^N\lambda_a D_a\otimes E_a,
\qquad \lambda_a\ge0,\qquad \sum_{a=1}^N\lambda_a=1,
$$
其中 $D_a,E_a$ 为各自端点上的密度。局部合同变换及偏转置的线性性给
$$
\operatorname{PT}_R\bigl(F_g\theta_g^{\mathrm{unread}}\operatorname{adj}(F_g)\bigr)
=\sum_{a=1}^N\lambda_a
\bigl(A_gD_a\operatorname{adj}(A_g)\bigr)\otimes E_a^{\mathsf T}.
$$
第一因子正半定，因为在任意 $x$ 上的二次型等于 $\langle\operatorname{adj}(A_g)x,D_a\operatorname{adj}(A_g)x\rangle\ge0$。若 $E_a=\sum_b\mu_b\operatorname{outer}(z_b)$ 是谱分解，$\mu_b\ge0$，则
$$
E_a^{\mathsf T}=\sum_b\mu_b\operatorname{outer}(\overline{z_b})\ge0,
$$
其中共轭逐计算基坐标取值。正半定因子的张量积及其非负有限和仍正半定，因此上式必须正半定，与 $v$ 上严格负的二次型矛盾。此论证只用可分态偏转置为正的必要性，且在未归一化的可分正半定锥中成立；不调用其逆命题，不把偏转置视为物理通道。由此对每个有限 $g$ 证明实际密度纠缠。

向量 $\phi$ 与 $|00\rangle$ 线性无关且 $\alpha>0$，所以 $S$ 的像是它们张成的二维空间。可逆合同变换及除以 $q_g>0$ 均保持秩，故 $\operatorname{rank}\theta_g^{\mathrm{unread}}=2$。系数矩阵的可逆性在此用来构造合同变换，没有对混合态使用纯态的 Schmidt 判据。

最后，$\{|e\rangle:e\in\{+,-\}^g\}$ 是 $H_g$ 的正交标准基，其投影之和为 $I_{H_g}$。对同一个 $\Xi_{g+2}$ 在此基中展开，再取内部空间的偏迹，得到 $\sum_e\operatorname{outer}(\chi_e)$；继续取 $M$ 的偏迹即得
$$
\sum_e Q_e=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})=\overline\Theta_g.
$$
取迹给 $\sum_eq_e=1$。各 $Q_e$ 正半定，故 $q_e=0$ 蕴含 $Q_e=0$；仅对正概率项归一化即得陈述中的加权平均，不能用归一化分支的等权平均替代。

由命题 130.1 的 $\operatorname{Tr}_M\operatorname{outer}(\Xi_{g+2})=\Gamma_{g+2}(P_0)$，此平均正是命题 133.1 中 $X=P_0$、$r=0$、$a=b=1$ 的 $\theta^{P_0}_{0;1,g,1}$。因此对 $g\ge1$ 直接应用该命题得到完整端点分割上的可分性；其假设明确要求非空间隔。$g=0$ 时平均只有空记录一项，等于 $G_0$，并已证纠缠。可分性要求存在一个有限凸乘积密度分解，不要求同一密度的每个系综都由可分分量组成，故可分平均与所选的纠缠分量相容。

本命题给出的是上述纯边界、内部测量及全加记录选择下，对每个有限间隔都纠缠的一种指定协议；最终记忆访问不是该协议的假设。它不对所有测量记录、任意混合初态或所有协议量化，不给出普遍最小访问条件、最优纠缠、确定性交付、信号传递、物理距离或时间的结论，也不给出关于 $g$ 的统一纠缠量正下界。证毕。

## 追加锚（本行以下为增补区）

## 137. 未读最终记忆时任意局部秩一内部记录的端点分类

**命题 137.1（正概率记录的乘积与秩二纠缠二分）。** 取命题 130.1 的纯边界生成器及命题 136.1 的向量化约定：
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对任意整数 $g\ge0$，恰好生成 $g+2$ 个输出，按发出次序分组为
$$
B_L\otimes H_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个和最后一个已发出的 qubit，左端点之前没有被忽略的前缀。对第 $k$ 个内部输出，选取单位复向量
$$
|\eta_k\rangle=\eta_{k,0}|0\rangle+\eta_{k,1}|1\rangle,
\qquad |\eta_{k,0}|^2+|\eta_{k,1}|^2=1\quad(1\le k\le g),
$$
其秩一投影为该位置某个固定局部正交基测量的一个结果。记记录为 $\eta=(\eta_1,\ldots,\eta_g)$；只对内部输出作这些测量及结果选择，生成过程没有反馈、记忆测量或重置，最终活动记忆以偏迹忽略。两个端点保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$；可分密度指此分割上的有限凸乘积密度和，非可分密度称为纠缠态。

令 $\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(v)=v\operatorname{adj}(v)$，并定义
$$
D_k=\operatorname{diag}(\overline{\eta_{k,0}},\overline{\eta_{k,1}}),\qquad
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
E_0=\operatorname{diag}(1,0),
$$
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad \|C\|_F^2=\sum_{i,j=0}^1|C_{ij}|^2,
$$
$$
C_\eta=s^{g+3}JD_1JD_2\cdots JD_gJ,\qquad C_\varnothing=s^3J.
$$
其中矩阵因子从左到右按内部位置 $1,\ldots,g$ 排列，所有空乘积取一。实际记录收缩及其最终记忆偏迹满足
$$
\begin{aligned}
\chi_\eta
&=(I_{B_L}\otimes\langle\eta_1|\otimes\cdots\otimes\langle\eta_g|
\otimes I_{B_R}\otimes I_M)\Xi_{g+2}\\
&=\operatorname{vec}_{LR}(C_\eta)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_\eta E_0)\otimes|1\rangle,\\
Q_\eta&:=\operatorname{Tr}_M\operatorname{outer}(\chi_\eta)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_\eta))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_\eta E_0)),\\
q_\eta&:=\operatorname{Tr}Q_\eta
=\|C_\eta\|_F^2+\alpha\|C_\eta E_0\|_F^2\in[0,1].
\end{aligned}
$$
$q_\eta$ 是实际内部投影的 Born 概率，且 $q_\eta=0$ 当且仅当 $C_\eta=0$；只在 $q_\eta>0$ 时定义条件密度 $\theta_\eta=Q_\eta/q_\eta$。有
$$
\det C_\eta=(-1)^{g+1}\alpha^{g+3}
\prod_{k=1}^g\overline{\eta_{k,0}\eta_{k,1}}.
$$
每个正概率记录恰属于以下一类。

第一，若至少一个内部向量有零计算基分量，则 $C_\eta$ 非零且秩为一。存在非零复系数列向量 $a,b\in\mathbb C^2$，使 $C_\eta=ab^{\mathsf T}$，其中 $\mathsf T$ 是普通转置。此时
$$
\theta_\eta=
\frac{\operatorname{outer}(a)}{\|a\|^2}\otimes
\frac{\operatorname{outer}(b)+\alpha\operatorname{outer}(E_0b)}
{\|b\|^2+\alpha|b_0|^2}.
$$
这是左因子为纯态的乘积密度，右因子不必为纯态。

第二，若所有内部向量的两个计算基分量均非零，则 $C_\eta$ 可逆，记录必有正概率，且 $\theta_\eta$ 是秩为二的纠缠密度。这包含 $g=0$ 的空记录；此时
$$
q_\varnothing=1,\qquad Q_\varnothing=\theta_\varnothing=G_0=\Gamma_2(P_0),
\qquad P_0=\operatorname{outer}(m_0),
$$
其中 $G_0$ 是命题 132.1 的纯边界相邻双位置密度。

对每个内部位置固定一个正交标准基 $\{|\eta_{k,0}^{\rm bas}\rangle,|\eta_{k,1}^{\rm bas}\rangle\}$，对全部记录 $e\in\{0,1\}^g$ 以上述定义取 $\eta_k=\eta_{k,e_k}^{\rm bas}$，并把所得算子及概率记为 $Q_e,q_e$。这个完整测量的平均为
$$
\overline\Theta_g:=\sum_{e\in\{0,1\}^g}Q_e
=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
=\sum_{\substack{e\in\{0,1\}^g\\q_e>0}}q_e\theta_e,
\qquad \sum_{e\in\{0,1\}^g}q_e=1.
$$
对 $g\ge1$，此平均由命题 133.1 可分；$g=0$ 时它等于纠缠密度 $G_0$。特别地，$g\ge1$ 时在所有内部位置测计算基，正概率记录恰为不含相邻 $11$ 的内部词，每个这样的记录均给乘积密度。若每个内部位置均测
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
则对每个 $g\ge0$，全部 $2^g$ 个记录均有正概率，均给秩二纠缠密度；这些概率和条件密度不要求彼此相等。

在混合选基记录中，任何含零分量的正概率记录仍给上述乘积密度。若恰有一个 $D_k$ 奇异，其余 $D_k$ 均可逆，则 $C_\eta$ 必为非零秩一矩阵，因而 $q_\eta>0$；两个或更多奇异因子则可以使整个矩阵为零。具体地，$g=2$ 的计算基内部记录 $(|1\rangle,|1\rangle)$ 概率为零，$g=3$ 的记录 $(|0\rangle,|-\rangle,|0\rangle)$ 也恰有零概率，后者即使存在合法计算基路径仍相消。

证明。令 $W_n$ 为不含相邻 $11$ 的长度 $n$ 二进制词集。命题 130.1 从实际 $T$ 递推所得的两个记忆列为
$$
\Xi_n=s^{n+1}\sum_{w\in W_n}|w\rangle\otimes|0\rangle
+s^{n+2}\sum_{\substack{w\in W_n\\w_{n-1}=0}}|w\rangle\otimes|1\rangle
\quad(n\ge1),\qquad \|\Xi_n\|=1.
$$
取 $n=g+2$。对任意内部计算基词 $u=(u_1,\ldots,u_g)$，复 bra 收缩的权重是
$$
(\langle\eta_1|\otimes\cdots\otimes\langle\eta_g|)|u\rangle
=\prod_{k=1}^g\overline{\eta_{k,u_k}}.
$$
置 $x_0=i$、$x_k=u_k$（$1\le k\le g$）、$x_{g+1}=j$。由 $J_{ab}=0$ 恰当 $a=b=1$，第一记忆列在端点 $i,j$ 上的系数为
$$
\begin{aligned}
s^{g+3}\sum_{u\in\{0,1\}^g}
\left(\prod_{t=0}^g J_{x_t,x_{t+1}}\right)
\left(\prod_{k=1}^g\overline{\eta_{k,u_k}}\right)
&=s^{g+3}(JD_1JD_2\cdots JD_gJ)_{ij}\\
&=(C_\eta)_{ij}.
\end{aligned}
$$
这是矩阵乘法对所有内部指标的求和：$D_k$ 的对角元在第 $k$ 个内部指标处插入，故次序是从左端点沿发出位置到右端点的 $D_1,\ldots,D_g$。$g=0$ 时求和只有空词，唯一边因子为 $J_{ij}$，仍给 $C_\varnothing=s^3J$。第二记忆列只允许末位 $j=0$，并多出一个 $s$，所以对全部 $i,j$，其系数为
$$
s(C_\eta)_{ij}\mathbf1_{\{j=0\}}=s(C_\eta E_0)_{ij}.
$$
因此得到所述 $\chi_\eta$。两个记忆列保留其原振幅；在正交记忆基中取偏迹消掉交叉项，以 $s^2=\alpha$ 得到 $Q_\eta$。它是正半定，取迹给 $q_\eta$ 的两个平方范数之和。该和为零当且仅当 $C_\eta=0$，此时 $\chi_\eta=0$、$Q_\eta=0$。

写 $|\eta\rangle=\bigotimes_{k=1}^g|\eta_k\rangle$，空张量积为 $H_0$ 的单位向量。实际内部事件的投影为
$$
\mathsf P_\eta=I_{B_L}\otimes\operatorname{outer}(|\eta\rangle)
\otimes I_{B_R}\otimes I_M.
$$
各局部向量单位化，故 $0\le\mathsf P_\eta\le I$，于是
$$
q_\eta=\|\chi_\eta\|^2
=\langle\Xi_{g+2},\mathsf P_\eta\Xi_{g+2}\rangle\in[0,1].
$$
这既证明概率的 Born 含义，也说明只可对正概率记录归一化，不能分别归一化两列再混合。$g=0$ 时 $\mathsf P_\varnothing=I$，所以 $q_\varnothing=1$；此时偏迹就是 $\Gamma_2(P_0)=G_0$，与命题 132.1、136.1 的相邻密度一致。

二阶矩阵的标量倍数在行列式中贡献标量的平方。由乘法性、$g+1$ 个 $J$ 因子及 $s^2=\alpha$，
$$
\begin{aligned}
\det C_\eta
&=(s^{g+3})^2(\det J)^{g+1}\prod_{k=1}^g\det D_k\\
&=\alpha^{g+3}(-1)^{g+1}
\prod_{k=1}^g\overline{\eta_{k,0}\eta_{k,1}}.
\end{aligned}
$$
由于 $\alpha>0$，这恰在至少一个计算基分量为零时消失。若 $q_\eta>0$ 且有这样的零分量，$C=C_\eta$ 非零且行列式为零，所以秩为一。选一个非零主元 $C_{i_*j_*}$，逐坐标定义
$$
a_i=C_{ij_*},\qquad b_j=\frac{C_{i_*j}}{C_{i_*j_*}}\quad(i,j\in\{0,1\}).
$$
秩一给出所有二阶子式关系
$$
C_{ij}C_{i_*j_*}=C_{ij_*}C_{i_*j}.
$$
故 $C_{ij}=a_ib_j$，且 $a_{i_*}\ne0$、$b_{j_*}=1$。这里是复系数的双线性分解 $C=ab^{\mathsf T}$，不对 $b$ 取共轭。由向量化定义及 $E_0^{\mathsf T}=E_0$，
$$
\operatorname{vec}_{LR}(C)=a\otimes b,\qquad
\operatorname{vec}_{LR}(CE_0)=a\otimes E_0b,
$$
$$
Q_\eta=\operatorname{outer}(a)\otimes
\bigl(\operatorname{outer}(b)+\alpha\operatorname{outer}(E_0b)\bigr),
\qquad q_\eta=\|a\|^2(\|b\|^2+\alpha|b_0|^2)>0.
$$
两个因子均为非零正半定算子；按其迹归一化得到陈述中的乘积密度，左因子的秩为一。右因子确实可以混合：取 $g=1$、$\eta_1=|0\rangle$，则
$$
C_\eta=s^4JE_0J=s^4\begin{pmatrix}1&1\\1&1\end{pmatrix}.
$$
可取 $a=s^4(1,1)^{\mathsf T}$、$b=(1,1)^{\mathsf T}$；右因子归一化前的矩阵为
$$
\begin{pmatrix}1+\alpha&1\\1&1\end{pmatrix},
$$
其行列式为 $\alpha>0$，所以归一化后仍秩二。

若每个分量均非零，则行列式非零，$C=C_\eta$ 可逆，且 $q_\eta\ge\|C\|_F^2>0$。直接应用命题 136.1 的局部合同论证：其中逐坐标恒等式
$$
(A\otimes I_{B_R})\operatorname{vec}_{LR}(C)=\operatorname{vec}_{LR}(AC)
$$
对任意复矩阵 $A,C$ 成立，并不要求矩阵为实。取
$$
F=C^{-1}\otimes I_{B_R},\qquad \phi=|00\rangle+|11\rangle,
\qquad S=\operatorname{outer}(\phi)+\alpha\operatorname{outer}(|00\rangle),
$$
便有
$$
FQ_\eta\operatorname{adj}(F)=S,\qquad
F\theta_\eta\operatorname{adj}(F)=\frac{S}{q_\eta},\qquad
\operatorname{Tr}\left(\frac{S}{q_\eta}\right)=\frac{2+\alpha}{q_\eta}.
$$
这是代数合同变换，不是本命题允许实施的操作；其归一化输入的像也不是单位迹密度。

命题 136.1 的可分正半定锥论证同样允许复系数：若 $X=\sum_r A_r\otimes B_r$ 且 $A_r,B_r\ge0$，则
$$
FX\operatorname{adj}(F)
=\sum_r(C^{-1}A_r\operatorname{adj}(C^{-1}))\otimes B_r
$$
仍是有限个正半定乘积之和。第一因子的非负性来自二次型；若 $B_r=\sum_t\mu_t\operatorname{outer}(z_t)$、$\mu_t\ge0$ 是谱分解，则
$$
B_r^{\mathsf T}=\sum_t\mu_t\operatorname{outer}(\overline{z_t})\ge0.
$$
所以在右计算基上取偏转置后，上述每个张量因子及有限和仍正半定。采用命题 132.1、136.1 的约定
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|,
$$
在字典序 $00,01,10,11$ 下已有
$$
\operatorname{PT}_R(S)=
\begin{pmatrix}
1+\alpha&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix},\qquad
v=\frac{|01\rangle-|10\rangle}{\sqrt2},\qquad
\langle v,\operatorname{PT}_R(S)v\rangle=-1.
$$
若 $\theta_\eta$ 可分，则 $Q_\eta=q_\eta\theta_\eta$ 也在该锥中，合同后的 $S$ 必有正半定偏转置，与此负二次型矛盾。因此 $\theta_\eta$ 纠缠。所用的仅是可分性的偏转置正性必要条件（Asher Peres，Separability Criterion for Density Matrices，Physical Review Letters 77，1413–1415，1996，[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)），其复数情形已由上述谱分解落实。

若 $\lambda\operatorname{vec}_{LR}(C)+\mu\operatorname{vec}_{LR}(CE_0)=0$，向量化的单射性给 $C(\lambda I+\mu E_0)=0$。左乘 $C^{-1}$，比较两个对角元，得到 $\lambda=0$、$\lambda+\mu=0$，故 $\mu=0$。两向量线性无关，$\alpha>0$，于是 $Q_\eta$ 这两个正权重外积之和的像恰为它们张成的二维空间：其核是两向量的共同正交补。这证明 $\operatorname{rank}\theta_\eta=2$，并未对混合密度使用纯态的 Schmidt 判据。行列式的两种情形穷尽所有正概率记录，故分类成立。

现在证明完整测量的平均。各个局部基的正交完备性给
$$
\sum_{e_k=0}^1\operatorname{outer}(|\eta_{k,e_k}^{\rm bas}\rangle)=I_B,
\qquad
\sum_{e\in\{0,1\}^g}\operatorname{outer}(|\eta_e^{\rm bas}\rangle)=I_{H_g},
\qquad
|\eta_e^{\rm bas}\rangle=\bigotimes_{k=1}^g|\eta_{k,e_k}^{\rm bas}\rangle.
$$
将同一个 $\Xi_{g+2}$ 在这个内部正交基上展开，每个系数正是 $\chi_e$；取内部偏迹时，正交性消掉不同记录间的交叉项，因此
$$
\operatorname{Tr}_{H_g}\operatorname{outer}(\Xi_{g+2})
=\sum_e\operatorname{outer}(\chi_e).
$$
再取 $M$ 的偏迹即得 $\sum_eQ_e=\overline\Theta_g$，取迹得 $\sum_eq_e=\|\Xi_{g+2}\|^2=1$。零概率项已经证明为零算子，只在写成 $q_e\theta_e$ 时省去。由命题 130.1 的实际输出偏迹，这个平均恰为命题 133.1 的
$$
\overline\Theta_g=\theta^{P_0}_{0;1,g,1}\qquad(g\ge1),
$$
即纯边界 $X=P_0$、无前缀 $r=0$、左右块长 $a=b=1$、忽略 $g$ 个内部输出的态；其可分性直接由该命题得出。$g=0$ 的完整基只有空记录，平均为上面已识别的纠缠密度 $G_0$。

在计算基测量中，记录 $u\in\{0,1\}^g$ 的权重只选中该内部词。若 $u$ 含相邻 $11$，没有合法完整词含此内部片段，路径式处处为零；若 $u$ 不含相邻 $11$，完整词 $(0,u,0)$ 合法，因此 $(C_u)_{00}=s^{g+3}\ne0$。这证明正概率记录恰为合法内部词；当 $g\ge1$ 时，每个此类记录含零分量，故分类的第一项给出乘积密度。该论证的全乘积结论不含 $g=0$。在加减基中，每个局部向量的两分量均非零，故每条记录的行列式非零，分类的第二项适用于全部 $2^g$ 条记录，包括空记录。完整测量的权重始终是各自的 $q_e$；正交完备性只给它们的和为一，不给等概率或相同条件密度。

最后，单位向量有零分量时另一个分量非零，所以奇异的 $D_k$ 本身秩为一。若这样的因子恰有一个，把整个乘积写作 $U D_k V$，其中包含非零标量及所有其余因子的 $U,V$ 均可逆；左右乘可逆矩阵保持秩，故 $C_\eta$ 秩一且非零。对多个奇异因子，令 $E_1=\operatorname{diag}(0,1)$，则
$$
E_1JE_1=0,\qquad
C_{(|1\rangle,|1\rangle)}=s^5JE_1JE_1J=0.
$$
另令 $Z=\operatorname{diag}(1,-1)$，则
$$
JZJ=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
E_0JZJE_0=0,
$$
$$
C_{(|0\rangle,|-\rangle,|0\rangle)}
=\frac{s^6}{\sqrt2}JE_0JZJE_0J=0.
$$
第二个记录在每对端点 $i,j$ 上都有两个合法词 $(i,0,0,0,j)$ 与 $(i,0,1,0,j)$，其内部 bra 权重分别为 $1/\sqrt2$ 与 $-1/\sqrt2$，故等幅相消；最终记忆的两列同时为零。两例均由 $C_\eta=0$ 得到 $q_\eta=0$，不定义其条件密度。证毕。

## 追加锚（本行以下为增补区）

## 138. 固定局部正交测量的平均端点 concurrence 与精确衰减界

**命题 138.1（未读最终记忆的分支凸顶与固定选基最优值）。** 沿用命题 130.1、137.1 的纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对每个整数 $g\ge0$，恰好发出 $g+2$ 个输出，次序为 $B_L\otimes H_g\otimes B_R\otimes M$。端点是第一个与最后一个已发出的 qubit，保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$，左端点之前没有被忽略的前缀。最终记忆不可访问，只取偏迹；生成途中无记忆读取、重置或反馈。

对每个内部位置 $1\le k\le g$，事先固定一个局部正交标准基
$$
\mathcal B_k=(|\eta_{k,0}\rangle,|\eta_{k,1}\rangle),\qquad
|\eta_{k,r}\rangle=\eta_{k,r,0}|0\rangle+\eta_{k,r,1}|1\rangle,
\qquad \langle\eta_{k,r}|\eta_{k,t}\rangle=\delta_{rt}.
$$
允许的测量恰为这些内部位置上的局部正交秩一投影，选基不依赖任何结果，保留完整记录 $\mathbf r=(r_1,\ldots,r_g)\in\{0,1\}^g$。以下最大值只在这个固定非自适应选基族中取；不包含 POVM、一般仪器、端点滤波、Bell 转换或记忆操作，初始记忆始终是上述纯 $m_0$。

记 $\operatorname{adj}$ 为共轭转置，$\operatorname{outer}(z)=z\operatorname{adj}(z)$，并按左端点为行、右端点为列定义
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad E_0=\operatorname{diag}(1,0).
$$
对一条记录，令 $|\eta_k\rangle=|\eta_{k,r_k}\rangle$，其分量简记为 $\eta_{k,j}=\eta_{k,r_k,j}$。直接采用命题 137.1 的实际分支公式：
$$
D_k=\operatorname{diag}(\overline{\eta_{k,0}},\overline{\eta_{k,1}}),\qquad
C_{\mathbf r}=s^{g+3}JD_1JD_2\cdots JD_gJ,\qquad C_\varnothing=s^3J,
$$
$$
v_{\mathbf r}=\operatorname{vec}_{LR}(C_{\mathbf r}),\qquad
w_{\mathbf r}=s\operatorname{vec}_{LR}(C_{\mathbf r}E_0),\qquad
Q_{\mathbf r}=\operatorname{outer}(v_{\mathbf r})+\operatorname{outer}(w_{\mathbf r}),
$$
$$
q_{\mathbf r}=\operatorname{Tr}Q_{\mathbf r}
=\|C_{\mathbf r}\|_F^2+\alpha\|C_{\mathbf r}E_0\|_F^2,\qquad
\det C_{\mathbf r}=(-1)^{g+1}\alpha^{g+3}
\prod_{k=1}^g\overline{\eta_{k,0}\eta_{k,1}}.
$$
这里 $\|C\|_F^2=\operatorname{Tr}(C\operatorname{adj}(C))$，$Q_{\mathbf r}$ 是实际内部复 bra 收缩后对最终记忆取偏迹的未归一化端点算子，$q_{\mathbf r}$ 是该记录的 Born 概率。命题 137.1 给出 $q_{\mathbf r}=0$ 当且仅当 $C_{\mathbf r}=0$；仅在 $q_{\mathbf r}>0$ 时定义 $\theta_{\mathbf r}=Q_{\mathbf r}/q_{\mathbf r}$。特别地，$q_\varnothing=1$；计算基记录 $(1,1)$ 及混合记录 $(|0\rangle,|-\rangle,|0\rangle)$ 的精确零事件均不定义条件密度，其中 $|-\rangle=(|0\rangle-|1\rangle)/\sqrt2$。

对单位向量 $z=\operatorname{vec}_{LR}(Z)$ 定义纯态 concurrence 为 $c(z)=2|\det Z|$。对完整双 qubit 空间上的密度 $\theta$，定义其凸顶 concurrence 为
$$
\mathcal C(\theta)=\inf\left\{
\sum_{\ell=1}^Np_\ell c(\psi_\ell):
\begin{array}{l}
N\ge1\text{ 为有限整数},\quad p_\ell\ge0,\quad \sum_{\ell=1}^Np_\ell=1,\\
\|\psi_\ell\|=1,\quad
\theta=\sum_{\ell=1}^Np_\ell\operatorname{outer}(\psi_\ell)
\end{array}\right\}.
$$
下确界遍历所有有限复单位纯态系综，不限制于实际记忆列给出的分解；它是密度的数学定义，与对物理测量基的最大化是两个不同的取值域。谱分解保证上述集合非空。术语及纯态 concurrence 的约定见 William K. Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，[arXiv:quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (7) 及式 (19)–(22) 的系综平均讨论；期刊版为 *Physical Review Letters* **80**，2245–2248（1998），[DOI:10.1103/PhysRevLett.80.2245](https://doi.org/10.1103/PhysRevLett.80.2245)。

则 $0\le c(z)\le1$、$0\le\mathcal C(\theta)\le1$，且每条正概率记录满足精确公式
$$
\mathcal C(\theta_{\mathbf r})=\frac{2|\det C_{\mathbf r}|}{q_{\mathbf r}}.
$$
令
$$
B_k=\sum_{r=0}^1|\eta_{k,r,0}\eta_{k,r,1}|,\qquad
A_g(\mathcal B_1,\ldots,\mathcal B_g)
=\sum_{\substack{\mathbf r\in\{0,1\}^g\\q_{\mathbf r}>0}}
q_{\mathbf r}\mathcal C(\theta_{\mathbf r}).
$$
则
$$
A_g=2\alpha^{g+3}\prod_{k=1}^gB_k,\qquad
\max_{\mathcal B_1,\ldots,\mathcal B_g}A_g=2\alpha^{g+3}.
$$
当 $g\ge1$ 时取到最大值当且仅当每个局部基均平衡，即其两个基向量的两个计算基分量的模均为 $1/\sqrt2$。所有赤道基
$$
\left(\frac{|0\rangle+e^{i\varphi_k}|1\rangle}{\sqrt2},
\frac{|0\rangle-e^{i\varphi_k}|1\rangle}{\sqrt2}\right),\qquad \varphi_k\in\mathbb R,
$$
以及它们逐向量改相位或互换次序后的基均取等，包括加减基。任一内部位置采用计算基（允许相位及次序改变）即有 $A_g=0$。$g=0$ 时空乘积为一，只有空记录及恒等仪器，$A_0=2\alpha^3$，无选基条件。最大值随 $g$ 以比值 $\alpha$ 几何衰减至零。

对每个有限 $g\ge0$，全加减基的每条记录均有非零行列式、正概率和正 concurrence，因而其条件密度不可写成有限凸乘积密度和。不过对 $g\ge1$，命题 133.1、137.1 的无条件端点平均
$$
\overline\Theta_g=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
$$
可分，故 $\mathcal C(\overline\Theta_g)=0$，而全加减基的条件 concurrence 的 Born 加权平均为 $2\alpha^{g+3}>0$。

证明。若 $Z=(Z_{ij})_{i,j=0}^1$，三角不等式与 $2uv\le u^2+v^2$ 给出
$$
\begin{aligned}
2|\det Z|&\le2|Z_{00}Z_{11}|+2|Z_{01}Z_{10}|\\
&\le |Z_{00}|^2+|Z_{11}|^2+|Z_{01}|^2+|Z_{10}|^2
=\operatorname{Tr}(Z\operatorname{adj}(Z)).
\end{aligned}
$$
当 $\operatorname{vec}_{LR}(Z)$ 为单位向量时右侧为一。每个有限系综的平均也在 $[0,1]$ 内，结合谱分解的存在便得所述凸顶取值范围。

固定一条 $q=q_{\mathbf r}>0$ 的记录，简写 $C,v,w,Q,\theta$。先设 $C$ 奇异。由 $q>0$ 可知 $C\ne0$，故 $C$ 秩一。按命题 137.1 的复秩一分解，存在非零复列向量 $a,b$ 使 $C=ab^{\mathsf T}$，其中 $\mathsf T$ 是普通转置。由行列约定，
$$
v=a\otimes b,\qquad w=s\,a\otimes E_0b.
$$
把 $v,w$ 中每个非零列 $h$ 化成单位向量 $h/\|h\|$，赋权 $\|h\|^2/q$；这些权重和为一，且所得外积加权和为 $\theta$。每个单位向量均为乘积向量，系数矩阵行列式为零；若 $w=0$ 就省去该列。因此这给出平均 concurrence 为零的有限系综，由非负性得 $\mathcal C(\theta)=0=2|\det C|/q$。

再设 $C$ 可逆。若 $xv+yw=0$，向量化的单射性给出
$$
C(xI+s yE_0)=0.
$$
左乘 $C^{-1}$ 并比较两个对角元得 $x=0$、$x+s y=0$，而 $s>0$，所以 $y=0$。于是矩阵 $H=[\,v\ \ w\,]$ 满列秩，$Q=H\operatorname{adj}(H)$，且
$$
F=(\operatorname{adj}(H)H)^{-1}\operatorname{adj}(H),\qquad FH=I_2
$$
是其左逆。

任取定义中一个有限单位纯态系综 $\theta=\sum_\ell p_\ell\operatorname{outer}(\psi_\ell)$，删去零权重，置 $z_\ell=\sqrt{q p_\ell}\,\psi_\ell$，于是
$$
Q=\sum_\ell\operatorname{outer}(z_\ell)=H\operatorname{adj}(H).
$$
对任意 $u\perp\operatorname{range}H$，
$$
0=\operatorname{adj}(u)Qu=\sum_\ell|\operatorname{adj}(u)z_\ell|^2.
$$
各项非负，故每个 $z_\ell$ 都正交于 $(\operatorname{range}H)^\perp$，即属于 $\operatorname{range}H$。满列秩保证唯一表示 $z_\ell=x_\ell v+y_\ell w$。记 $t_\ell=(x_\ell,y_\ell)^{\mathsf T}=Fz_\ell$，则
$$
\sum_\ell\operatorname{outer}(t_\ell)
=FQ\operatorname{adj}(F)
=FH\operatorname{adj}(H)\operatorname{adj}(F)=I_2.
$$
逐矩阵元读取此式，得到
$$
\sum_\ell|x_\ell|^2=\sum_\ell|y_\ell|^2=1,\qquad
\sum_\ell\overline{x_\ell}y_\ell=0,\qquad
\sum_\ell x_\ell\overline{y_\ell}=0.
$$
若 $z_\ell=\operatorname{vec}_{LR}(Z_\ell)$，线性性给
$$
Z_\ell=C(x_\ell I+s y_\ell E_0),\qquad
\det Z_\ell=\det C\,x_\ell(x_\ell+s y_\ell).
$$
不必改变任何系综相位。由于 $|x_\ell|=|\overline{x_\ell}|$，包括 $x_\ell=0$，有
$$
\begin{aligned}
\sum_\ell|\det Z_\ell|
&=|\det C|\sum_\ell|x_\ell(x_\ell+s y_\ell)|\\
&=|\det C|\sum_\ell|\overline{x_\ell}(x_\ell+s y_\ell)|\\
&\ge |\det C|\left|\sum_\ell
\bigl(|x_\ell|^2+s\overline{x_\ell}y_\ell\bigr)\right|
=|\det C|.
\end{aligned}
$$
二阶行列式的齐次性及 $z_\ell=\sqrt{q p_\ell}\,\psi_\ell$ 又给
$$
\sum_\ell p_\ell c(\psi_\ell)
=\frac2q\sum_\ell|\det Z_\ell|
\ge\frac{2|\det C|}{q}.
$$
所取系综任意，故这是全部有限复纯态系综的共同下界。另一方面，实际两列 $v,w$ 按范数平方除以 $q$ 赋权的单位纯态分解满足
$$
\det(sCE_0)=0,\qquad
\frac{\|v\|^2}{q}c\left(\frac{v}{\|v\|}\right)
+\frac{\|w\|^2}{q}c\left(\frac{w}{\|w\|}\right)
=\frac{2|\det C|}{q}.
$$
可逆情形两列均非零，所以此式无零除。它达到下界，证明 $\mathcal C(\theta)=2|\det C|/q$。这里的两列系综是已取记忆偏迹之密度的数学分解，不引入记忆测量；其最优性来自刚证的共同下界，不是对任意混合分解的最优性断言。整个分支公式由以上有限维论证得到。

现在对固定的完整局部测量求平均。命题 137.1 的正交完备性恒等式为
$$
\sum_{\mathbf r\in\{0,1\}^g}Q_{\mathbf r}
=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2})
=\overline\Theta_g,\qquad
\sum_{\mathbf r\in\{0,1\}^g}q_{\mathbf r}=1.
$$
它由 $\sum_{r=0}^1\operatorname{outer}(|\eta_{k,r}\rangle)=I_B$ 的有限张量积及 $\|\Xi_{g+2}\|=1$ 给出，亦适用于 $g=0$。先用已证分支凸顶公式，得到每条正概率记录的 $q_{\mathbf r}\mathcal C(\theta_{\mathbf r})=2|\det C_{\mathbf r}|$。零概率记录有 $C_{\mathbf r}=0$，其行列式为零，故只在行列式之和中补入这些零项，而不定义它们的条件密度。命题 137.1 的行列式公式及有限乘积展开遂给
$$
\begin{aligned}
A_g
&=2\sum_{\mathbf r\in\{0,1\}^g}|\det C_{\mathbf r}|\\
&=2\alpha^{g+3}\sum_{r_1=0}^1\cdots\sum_{r_g=0}^1
\prod_{k=1}^g|\eta_{k,r_k,0}\eta_{k,r_k,1}|\\
&=2\alpha^{g+3}\prod_{k=1}^g
\left(\sum_{r=0}^1|\eta_{k,r,0}\eta_{k,r,1}|\right).
\end{aligned}
$$
这里分解的是行列式权重之和；正交完备性不要求 Born 概率彼此相等，也不要求这些概率按位置分解。

任意二维复正交标准基可写成
$$
\bigl((a,b)^{\mathsf T},\ e^{i\chi}(-\overline b,\overline a)^{\mathsf T}\bigr),
\qquad |a|^2+|b|^2=1,\qquad \chi\in\mathbb R,
$$
因为第一向量的正交补是一维，所列第二向量是其中的单位向量。因此对应的局部因子及其精确差额为
$$
B=2|ab|,\qquad 1-B=(|a|-|b|)^2\ge0.
$$
故 $0\le B\le1$；$B=1$ 当且仅当 $|a|=|b|=1/\sqrt2$，而 $B=0$ 当且仅当 $a=0$ 或 $b=0$，也就是计算基相差相位及排列的情形。对 $g\ge1$，有限个 $[0,1]$ 因子的乘积为一当且仅当每个因子为一：若有 $B_k<1$，则乘积不大于该因子，严格小于一。平衡基同时实现所有因子为一，于是最大值存在，且等号条件恰如陈述。逐向量去整体相位可将任意平衡基写成所列赤道基；加减基是 $\varphi_k=0$ 的情形。任一计算基因子为零就使整个平均为零。

当 $g=0$，由 $C_\varnothing=s^3J$ 得 $|\det C_\varnothing|=\alpha^3$，由 $q_\varnothing=1$ 得 $A_0=2\alpha^3$，与空乘积公式一致，不附加任何不存在的内部位置条件。若记上述最大值为 $M_g$，则
$$
M_{g+1}=\alpha M_g,\qquad M_g=2\alpha^{g+3}\longrightarrow0,
$$
因为 $0<\alpha<1$。这是一列有限协议的平均值极限，不对无限记录事件作条件化。

最后，全加减基的每个选中向量都有两非零分量，故对每个有限 $g$ 及每条记录，命题 137.1 的行列式非零，进而 $q_{\mathbf r}>0$，已证分支公式给 $\mathcal C(\theta_{\mathbf r})>0$。若双 qubit 密度可分，即为有限凸乘积密度和，则分别谱分解每个乘积因子的两个局部密度，再分配有限求和，得到一个有限单位乘积纯态系综。每个乘积纯态的系数矩阵秩一，故 $c=0$，该密度的凸顶也为零。因此正凸顶排除了上述可分性。对 $g\ge1$，命题 133.1 取纯输入 $P_0=\operatorname{outer}(m_0)$、无前缀 $r=0$、左右块长均为一，正给出 $\overline\Theta_g$ 的有限凸乘积密度分解，故同一谱细化论证给 $\mathcal C(\overline\Theta_g)=0$；全加减基的 $A_g=2\alpha^{g+3}>0$ 则由平均公式得出。两者分别是平均密度的凸顶和保留完整结果记录时各条件密度凸顶的平均，取值顺序不同。证毕。

## 追加锚（本行以下为增补区）

## 139. 经典记录反馈下逐分支相同的最优端点 concurrence

**命题 139.1（固定次序自适应正交测量的平均最优值与最坏记录保证）。** 沿用命题 130.1 的纯边界生成器，令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha+\alpha^2=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对每个整数 $g\ge0$，在任何测量之前恰好生成 $g+2$ 个输出，次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个与最后一个已发出的 qubit，左端点之前没有被忽略的前缀，端点保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。最终记忆只以偏迹忽略，生成及测量均不读取、测量或重置记忆，也不对端点施加操作。

定义策略类 $\mathfrak P_g$ 如下：每个内部位置只测量一次，次序固定为 $1,\ldots,g$；在已观察到历史 $h=(r_1,\ldots,r_t)\in\{0,1\}^t$、$0\le t<g$ 时，策略 $\mathcal P$ 为下一个位置 $t+1$ 指定一个正交标准基
$$
\mathcal B_h=(|\eta_{h,0}\rangle,|\eta_{h,1}\rangle),\qquad
\langle\eta_{h,b}|\eta_{h,d}\rangle=\delta_{bd}\quad(b,d\in\{0,1\}).
$$
此选择只能依赖已知模型、$g$ 和历史 $h$，测量为该基的两个秩一正交投影，保留全部结果记录。零概率历史处可任意补齐正交标准基，使策略定义于整棵有限二叉树，但不为这些历史定义归一化条件态。以下两个最大值仅在 $\mathfrak P_g$ 中取；任意 LOCC、POVM、滤波、可变测量次序、重复测量同一位置及记忆访问均不属于此取值域。

记 $\operatorname{adj}$ 为共轭转置，$\operatorname{outer}(z)=z\operatorname{adj}(z)$，并以左端点为行、右端点为列定义
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad E_0=\operatorname{diag}(1,0).
$$
对每个形式完整记录 $r=(r_1,\ldots,r_g)$，置 $r_{<k}=(r_1,\ldots,r_{k-1})$，并记该路径上实际选中的向量及其分量为
$$
|\eta_{r,k}\rangle:=|\eta_{r_{<k},r_k}\rangle
=\eta_{r,k,0}|0\rangle+\eta_{r,k,1}|1\rangle,\qquad
|\eta_r\rangle=\bigotimes_{k=1}^g|\eta_{r,k}\rangle.
$$
当 $g=0$ 时只有空记录 $\varnothing$，其空张量积是 $H_0$ 的单位向量。逐路径采用命题 137.1 的收缩约定，定义
$$
D_{r,k}=\operatorname{diag}(\overline{\eta_{r,k,0}},\overline{\eta_{r,k,1}}),\qquad
C_r=s^{g+3}JD_{r,1}JD_{r,2}\cdots JD_{r,g}J,\qquad C_\varnothing=s^3J.
$$
实际分支、未归一化端点算子及其 Born 权重为
$$
\begin{aligned}
\chi_r
&=(I_{B_L}\otimes\langle\eta_r|\otimes I_{B_R}\otimes I_M)\Xi_{g+2}\\
&=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle,\\
Q_r&=\operatorname{Tr}_M\operatorname{outer}(\chi_r)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),\\
q_r&=\operatorname{Tr}Q_r
=\|C_r\|_F^2+\alpha\|C_rE_0\|_F^2,
\qquad \|C\|_F^2=\sum_{i,j=0}^1|C_{ij}|^2.
\end{aligned}
$$
有 $q_r=0$ 当且仅当 $C_r=0$，仅对 $q_r>0$ 定义 $\theta_r=Q_r/q_r$，且
$$
\det C_r=(-1)^{g+1}\alpha^{g+3}
\prod_{k=1}^g\overline{\eta_{r,k,0}\eta_{r,k,1}}.
$$
这里的两个记忆列及其权重是实际振幅与偏迹所得，不分别归一化；路径公式不将自适应策略等同于一组固定局部基的笛卡尔积。

采用命题 138.1 的 concurrence 定义，记作 $\mathcal C_{\rm conc}=\mathcal C$：单位向量 $z=\operatorname{vec}_{LR}(Z)$ 的纯态值为 $c(z)=2|\det Z|$，密度 $\theta$ 的值为
$$
\mathcal C_{\rm conc}(\theta)
=\inf\left\{\sum_{\ell=1}^Np_\ell c(\psi_\ell):
\begin{array}{l}
N\ge1\text{ 为有限整数},\quad p_\ell\ge0,\quad\sum_{\ell=1}^Np_\ell=1,\\
\|\psi_\ell\|=1,\quad
\theta=\sum_{\ell=1}^Np_\ell\operatorname{outer}(\psi_\ell)
\end{array}\right\}.
$$
下确界遍历全部有限复单位纯态系综。该定义及其本族恒等式 $\mathcal C_{\rm conc}(Q_r/q_r)=2|\det C_r|/q_r$ 均取自命题 138.1；该命题对全部系综的证明不以实际两记忆列限制取值域。纯态术语的文献约定亦见该命题所引 Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，Physical Review Letters 80，2245–2248（1998），[DOI:10.1103/PhysRevLett.80.2245](https://doi.org/10.1103/PhysRevLett.80.2245)。

定义平均值与最坏正概率记录保证为
$$
A_g(\mathcal P)=\sum_{\substack{r\in\{0,1\}^g\\q_r>0}}
q_r\mathcal C_{\rm conc}(\theta_r),\qquad
G_g(\mathcal P)=\min_{\substack{r\in\{0,1\}^g\\q_r>0}}
\mathcal C_{\rm conc}(\theta_r).
$$
则对任意 $\mathcal P\in\mathfrak P_g$，形式记录向量 $|\eta_r\rangle$ 构成 $H_g$ 的正交标准基，并有
$$
\sum_rQ_r=\overline\Theta_g
:=\operatorname{Tr}_{H_g,M}\operatorname{outer}(\Xi_{g+2}),\qquad
\sum_rq_r=1.
$$
所以定义 $G_g$ 的有限集合非空，而且
$$
G_g(\mathcal P)\le A_g(\mathcal P)
=2\sum_{r\in\{0,1\}^g}|\det C_r|
\le2\alpha^{g+3}.
$$
存在仅使用既有经典记录的策略 $\mathcal P_*$，使每条完整记录都满足
$$
q_r=2^{-g},\qquad
\mathcal C_{\rm conc}(\theta_r)=2\alpha^{g+3}.
$$
因此两个最大值均达到，且恰为命题 138.1 的固定选基平均最优值：
$$
\max_{\mathcal P\in\mathfrak P_g}G_g(\mathcal P)
=\max_{\mathcal P\in\mathfrak P_g}A_g(\mathcal P)
=2\alpha^{g+3}.
$$
在 $g=0$ 时唯一记录满足 $C_\varnothing=s^3J$、$q_\varnothing=1$、$\mathcal C_{\rm conc}(\theta_\varnothing)=2\alpha^3$，没有选基步骤。两个最优值随 $g$ 以比值 $\alpha$ 几何衰减至零，故不存在对所有 $g$ 一致严格为正的此类保证下界。$g$ 仅是内部输出数，不赋予物理距离或时间含义。

这里逐记录相同的结论仅指这个纠缠量，不附加端点密度相同、谱相同、局部幺正等价、纯 Bell 对或同一校正操作的结论，也不定义 Bell 产率。遗忘全部记录时，对 $g\ge1$ 仍得到命题 133.1 的可分无条件端点密度，故其 concurrence 为零；此陈述只涉及指定态族与指定取值域，不是普适经典性结论。

证明。固定任意策略及一条完整记录。在这条路径上，每个已选局部向量已确定，顺序投影作用在不同内部因子上，其乘积就是这些局部投影的张量积。去掉投影后保留的单位内部向量，端点及记忆的系数向量恰为 $\chi_r$；这一步不需要预先固定其他路径的基。命题 137.1 的复 bra 收缩公式逐路径适用，给出上述 $C_r$ 和两记忆列；取记忆偏迹给 $Q_r$ 及 $q_r$。两个平方范数之和为零当且仅当 $C_r=0$。又因 $\det J=-1$、$s^2=\alpha$，行列式的乘法性给出所列 $\det C_r$，包含空记录。这样保留了左行右列及所有 bra 的复共轭，概率也是整条分支的未归一化范数平方。

任取两条不同形式记录 $r,r'$，令 $k$ 为首次分歧位置。它们在此之前的历史相同，因此第 $k$ 个位置采用同一个正交标准基，而两个结果标签不同，故
$$
\langle\eta_{r,k}|\eta_{r',k}\rangle=0,\qquad
\langle\eta_r|\eta_{r'}\rangle
=\prod_{j=1}^g\langle\eta_{r,j}|\eta_{r',j}\rangle=0.
$$
每个张量向量范数为一，共有 $2^g=\dim H_g$ 个，所以它们是正交标准基，$\sum_r\operatorname{outer}(|\eta_r\rangle)=I_{H_g}$。不可达历史处的任意正交补齐同样满足这一论证。把 $\Xi_{g+2}$ 在此内部基上展开后取内部偏迹，再取记忆偏迹，得到 $\sum_rQ_r=\overline\Theta_g$；由命题 130.1 的 $\|\Xi_{g+2}\|=1$，取迹得 $\sum_rq_r=1$。当 $g=0$ 时基仅含空张量积，两个等式仍成立。因此至少有一条正概率记录，且归一化条件密度只在这个非空有限子集上使用。

由命题 138.1 已对全部有限系综证明的本族公式，每条正概率记录有 $q_r\mathcal C_{\rm conc}(\theta_r)=2|\det C_r|$。零概率记录有 $C_r=0$，只向行列式求和补入零项，便得
$$
A_g(\mathcal P)
=2\alpha^{g+3}\sum_{r\in\{0,1\}^g}
\prod_{k=1}^g|\eta_{r,k,0}\eta_{r,k,1}|.
$$
任一单位 qubit 向量满足
$$
2|\eta_{r,k,0}\eta_{r,k,1}|
\le |\eta_{r,k,0}|^2+|\eta_{r,k,1}|^2=1.
$$
故每条形式记录的乘积不超过 $2^{-g}$，共有 $2^g$ 条，直接得到 $A_g(\mathcal P)\le2\alpha^{g+3}$。这个估计逐记录成立，不对含历史依赖的求和作逐位置因子分解。正概率权重之和为一，每个对应的 concurrence 均不小于其最小值，故 $G_g(\mathcal P)\le A_g(\mathcal P)$。

现在构造达到这两个上界的策略。先定义仅由已知输出密度和已观察到的历史确定的条件密度。令
$$
\Omega_{\rm out}=\operatorname{Tr}_M\operatorname{outer}(\Xi_{g+2}).
$$
对于长度 $t<g$ 的历史 $h$，沿其已选路径置
$$
K_h=I_{B_L}\otimes
\left(\bigotimes_{k=1}^t\langle\eta_{h_{<k},h_k}|\right)
\otimes I_{B_{t+1}\otimes\cdots\otimes B_g\otimes B_R},
\qquad X_h=K_h\Omega_{\rm out}\operatorname{adj}(K_h),\qquad q_h=\operatorname{Tr}X_h.
$$
这里 $q_h$ 是前缀事件的 Born 概率，空历史有 $K_\varnothing=I$、$q_\varnothing=1$。同一定义在 $t=g$ 时保留的末因子仅为 $B_R$，此时 $X_r=Q_r$。在 $q_h>0$ 且 $t<g$ 时，下一内部位置的归一化条件密度为
$$
\rho_h=\frac1{q_h}
\operatorname{Tr}_{B_L,B_{t+2},\ldots,B_g,B_R}X_h
=\begin{pmatrix}a&c\\\overline c&1-a\end{pmatrix},
\qquad a\in[0,1],\quad c\in\mathbb C.
$$
$t=g-1$ 时上式只迹去 $B_L,B_R$。这一定义对已知 $\Omega_{\rm out}$ 收缩过去的投影，除以实际前缀权重，再迹去其余输出；没有读取隐藏记忆值、测定未知态、使用未来结果或访问最终记忆。由于此前投影仅在输出上，先对记忆取偏迹与这些收缩可交换，故它正是该事件下下一位置的 Born 密度。

在每个已到达历史 $h$ 上，精确地定义
$$
\kappa_h=
\begin{cases}
i\,\overline c/|c|,&c\ne0,\\
1,&c=0,
\end{cases}
\qquad
|\eta_{h,0}\rangle=\frac{|0\rangle+\kappa_h|1\rangle}{\sqrt2},\qquad
|\eta_{h,1}\rangle=\frac{|0\rangle-\kappa_h|1\rangle}{\sqrt2}.
$$
两种情形均有 $|\kappa_h|=1$，所以两向量范数为一，内积为 $(1-|\kappa_h|^2)/2=0$；它们构成平衡正交标准基。按照所写的非对角元约定 $\rho_{h,01}=c$，对两个标签直接计算得
$$
\begin{aligned}
\Pr(0\mid h)&=\langle\eta_{h,0}|\rho_h|\eta_{h,0}\rangle
=\frac12+\operatorname{Re}(\kappa_hc),\\
\Pr(1\mid h)&=\langle\eta_{h,1}|\rho_h|\eta_{h,1}\rangle
=\frac12-\operatorname{Re}(\kappa_hc).
\end{aligned}
$$
若 $c\ne0$，则 $\kappa_hc=i|c|$，实部为零；若 $c=0$，则 $\kappa_hc=0$，实部也为零。故两个条件概率严格等于 $1/2$。这里 $c=0$ 是精确分支；任意非零复数 $c$，无论其模多小，均采用第一行公式。

从 $q_\varnothing=1$ 开始按历史长度归纳。若长度 $t<g$ 的每个历史已满足 $q_h=2^{-t}>0$，则它们的 $\rho_h$ 全部存在，上述两个基向量也均已定义；对 $b=0,1$ 有
$$
q_{hb}=q_h\Pr(b\mid h)=2^{-(t+1)}>0.
$$
这同时证明下一层全部可达，并允许继续定义该策略，没有用尚未证明为正的权重归一化。有限归纳给出整棵树及其全部完整记录，且 $q_r=2^{-g}$。每个被选向量的两个计算基分量的模都为 $1/\sqrt2$，故路径行列式满足
$$
|\det C_r|=\alpha^{g+3}2^{-g}>0,\qquad
\mathcal C_{\rm conc}(\theta_r)
=\frac{2\alpha^{g+3}2^{-g}}{2^{-g}}=2\alpha^{g+3}.
$$
于是 $\mathcal P_*$ 同时达到 $A_g$ 和 $G_g$ 的上界。这一存在性构造不包含自适应性为必要条件的断言。平衡性本身也不蕴含等概率：$g=1$ 的固定实加减基由同一 $Q_r$ 公式给出 $q_+=1/2+\alpha^3$、$q_-=1/2-\alpha^3$，两者不同；上面的等概率来自所选相位与条件非对角元的关系。

在 $g=0$ 时无内部测量，完备性给 $q_\varnothing=1$，而 $|\det(s^3J)|=\alpha^3$，命题 138.1 的本族公式给唯一 concurrence 为 $2\alpha^3$。令任一最优值为 $M_g=2\alpha^{g+3}$，则 $M_{g+1}=\alpha M_g$ 且 $M_g\to0$。因此对任意 $\varepsilon>0$，存在有限 $g$ 使每个允许策略都满足 $G_g(\mathcal P)\le M_g<\varepsilon$，排除跨全部 $g$ 的一致正下界。

最后，任意策略遗忘记录后的密度都等于已证的 $\overline\Theta_g$。当 $g\ge1$，命题 133.1 取纯输入 $P_0=\operatorname{outer}(m_0)$、被忽略前缀长为零、左右块长均为一，给出该密度的有限凸乘积密度分解。将两个局部密度各自谱分解，可细化为有限单位乘积纯态系综，各项行列式为零，故 $\mathcal C_{\rm conc}(\overline\Theta_g)=0$。相反，上述策略保留记录时的条件 concurrence 平均为 $2\alpha^{g+3}>0$；这里分别是平均密度的 concurrence 与条件 concurrence 的平均。又因构造中每个 $C_r$ 可逆，命题 137.1 给每个条件密度秩二，故这些分支并非纯 Bell 对；同一 concurrence 等式没有比较端点密度、谱或局部幺正轨道，也未增加任何端点校正或转换操作。证毕。

## 追加锚（本行以下为增补区）

## 140. 原始结果坐标的删除与联合奇偶记录的条件纠缠

**命题 140.1（固定选基下的坐标遗忘、独立擦除与两内部位奇偶反例）。** 取命题 130.1 的纯边界生成器，令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
H_n=B^{\otimes n},\qquad H_0=\mathbb C,\qquad
\Xi_0=m_0,\qquad \Xi_{n+1}=(I_{H_n}\otimes T)\Xi_n.
$$
两份二维空间均取正交标准基。对每个整数 $g\ge0$，在任何测量之前恰好生成 $g+2$ 个输出，完整次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个和最后一个已发出的 qubit，左端点之前没有被忽略的前缀，端点保留完整空间 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。生成途中不读取、测量或重置记忆；最终记忆不可访问并取偏迹。

测量族取命题 138.1 的固定非自适应族：对每个内部位置，事先选定局部正交标准基
$$
\mathcal B_k=(|\eta_{k,0}\rangle,|\eta_{k,1}\rangle),\qquad
|\eta_{k,r}\rangle=\eta_{k,r,0}|0\rangle+\eta_{k,r,1}|1\rangle,
\qquad \langle\eta_{k,r}|\eta_{k,t}\rangle=\delta_{rt}.
$$
每个内部位置仅在此基测量一次，全部基在任何结果出现之前确定。以命题 139.1 的历史记号表示，这里要求 $\mathcal B_h=\mathcal B_{|h|+1}$ 对全部历史成立；不取该命题的一般历史依赖选基族。端点不施加操作，结果不用于后续选基或其他反馈控制；下文仅允许对已完成测量的经典记录作所指定的处理，该处理不耦合到端点或记忆。测后的内部输出及结果的其他物理副本均不可访问，所声明的经典接口是唯一可访问记录。因而一个结果此前是否被用于物理控制，与它此后是否仍可访问，是分别受限的两个假设；事后删除记录不撤销既往控制。

写 $[g]=\{1,\ldots,g\}$，$[0]=\varnothing$。沿用命题 137.1 的分支及左行右列向量化记号，$\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(z)=z\operatorname{adj}(z)$，并令
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad E_0=\operatorname{diag}(1,0).
$$
对完整原始记录 $r=(r_1,\ldots,r_g)\in\{0,1\}^g$，置
$$
D_{k,r_k}=\operatorname{diag}(\overline{\eta_{k,r_k,0}},\overline{\eta_{k,r_k,1}}),\qquad
C_r=s^{g+3}JD_{1,r_1}JD_{2,r_2}\cdots JD_{g,r_g}J,
\qquad C_\varnothing=s^3J.
$$
命题 137.1 的实际收缩公式为
$$
\begin{aligned}
\chi_r
&=(I_{B_L}\otimes\langle\eta_{1,r_1}|\otimes\cdots\otimes
\langle\eta_{g,r_g}|\otimes I_{B_R}\otimes I_M)\Xi_{g+2}\\
&=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle,\\
Q_r&=\operatorname{Tr}_M\operatorname{outer}(\chi_r)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),\\
q_r&=\operatorname{Tr}Q_r=\|C_r\|_F^2+\alpha\|C_rE_0\|_F^2,
\qquad \|C\|_F^2=\sum_{i,j=0}^1|C_{ij}|^2.
\end{aligned}
$$
其中 $q_r$ 是 Born 概率，$q_r=0$ 当且仅当 $C_r=0$；仅在 $q_r>0$ 时定义 $\theta_r=Q_r/q_r$，且 $\sum_rq_r=1$。两记忆列保留实际振幅，不分别归一化。

采用命题 138.1 的 concurrence，记 $\mathcal C_{\rm conc}=\mathcal C$。单位向量 $z=\operatorname{vec}_{LR}(Z)$ 的纯态值为 $c(z)=2|\det Z|$，密度 $\theta$ 的值定义为
$$
\mathcal C_{\rm conc}(\theta)=\inf\left\{
\sum_{\ell=1}^Np_\ell c(\psi_\ell):
\begin{array}{l}
N\ge1\text{ 为有限整数},\quad p_\ell\ge0,\quad\sum_{\ell=1}^Np_\ell=1,\\
\|\psi_\ell\|=1,\quad\theta=\sum_{\ell=1}^Np_\ell\operatorname{outer}(\psi_\ell)
\end{array}\right\}.
$$
下确界遍历全部有限复单位纯态系综。直接采用命题 138.1 已证恒等式
$$
\mathcal C_{\rm conc}(\theta_r)=\frac{2|\det C_r|}{q_r}\quad(q_r>0),\qquad
B_k=\sum_{r=0}^1|\eta_{k,r,0}\eta_{k,r,1}|\le1,
$$
$$
A_g(\mathrm{full})
:=\sum_{r:q_r>0}q_r\mathcal C_{\rm conc}(\theta_r)
=2\alpha^{g+3}\prod_{k=1}^gB_k.
$$
可分密度采用命题 132.1 的有限凸乘积密度和定义；相应的可分正锥为
$$
\operatorname{Sep}_+(L:R)=\left\{\sum_{\nu=1}^N U_\nu\otimes V_\nu:
N\ge1\text{ 为有限整数},\quad U_\nu\ge0,\quad V_\nu\ge0\right\},
$$
它包含零算子。则以下三项成立。

（A）对每个有限 $g\ge1$、固定真子集 $S\subsetneq[g]$ 及保留值 $y\in\{0,1\}^S$，定义
$$
Q_{S,y}=\sum_{r:r_S=y}Q_r,\qquad q_{S,y}=\operatorname{Tr}Q_{S,y}.
$$
有 $Q_{S,y}\in\operatorname{Sep}_+(L:R)$，包括 $Q_{S,y}=0$。当 $q_{S,y}>0$ 时，$Q_{S,y}/q_{S,y}$ 是可分密度且 concurrence 为零。这里遗忘的是一组固定的原始结果坐标，不量化记录的任意非单射函数。

（B）对所有 $g\ge0$ 及 $S\subseteq[g]$，沿用同一求和式定义 $Q_{S,y}$、$q_{S,y}$，故完整掩码满足 $Q_{[g],r}=Q_r$、$q_{[g],r}=q_r$。完成全部局部测量后，将每个原始标志独立通过经典擦除：第 $k$ 个标志以固定概率 $t_k\in[0,1]$ 保留，擦除随机性独立于全部结果值，且各位置相互独立。接口同时揭示保留掩码 $S$ 和保留值 $y$，不留其他可访问副本。令
$$
w_S=\prod_{k\in S}t_k\prod_{k\notin S}(1-t_k).
$$
事件 $(S,y)$ 的未归一化端点算子及概率分别为 $w_SQ_{S,y}$ 和 $w_Sq_{S,y}$；仅在 $w_Sq_{S,y}>0$ 时，其条件密度定义为
$$
\theta^{\rm erased}_{S,y}=\frac{w_SQ_{S,y}}{w_Sq_{S,y}}
=\frac{Q_{S,y}}{q_{S,y}}.
$$
按这一掩码与值接口求平均，则
$$
\begin{aligned}
A_g(\mathrm{erased})
&:=\sum_{\substack{S\subseteq[g],\ y\in\{0,1\}^S\\w_Sq_{S,y}>0}}
w_Sq_{S,y}\mathcal C_{\rm conc}(\theta^{\rm erased}_{S,y})\\
&=\left(\prod_{k=1}^gt_k\right)A_g(\mathrm{full})
=2\alpha^{g+3}\prod_{k=1}^g(t_kB_k).
\end{aligned}
$$
当 $g=0$ 时只有空记录、空掩码，所有空乘积为一，平均值为 $2\alpha^3$。若存在 $t_k=0$，则对任意上述固定基族，平均值均为零。这里取的是条件密度 concurrence 的平均，不是平均密度的 concurrence。值无关性是必要的适用假设：若掩码选择依赖结果，揭示掩码本身可以揭示联合关系，事件算子不自动等于 $w_SQ_{S,y}$。

（C）取 $g=2$，两个内部位置均测加减基
$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\qquad
|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2},
$$
标签分别为 $0,1$。在完成全部测量后，仅保留经典位 $b=r_1\mathbin{\oplus}r_2$，不独立保留任何原始值。两个事件算子为
$$
Q_{\rm even}=Q_{00}+Q_{11},\qquad Q_{\rm odd}=Q_{01}+Q_{10}.
$$
两事件概率均严格为正，其条件端点密度均纠缠；而仅保留任一原始位的条件端点密度均由（A）可分。因此一个联合奇偶位与一个原始坐标位具有不同的条件纠缠性质。此反例的参数限定为 $g=2$，所保留的性质是纠缠，不是完整记录对所有端点实验的预测：同属偶事件的正概率记录 $00,11$ 满足
$$
\Pr(01\mid00)=\frac4{18+13\alpha}>0,\qquad
\Pr(01\mid11)=0.
$$
故奇偶位不是完整端点密度的充分统计量。

证明。先证（A）。置 $\Omega_{\rm out}=\operatorname{Tr}_M\operatorname{outer}(\Xi_{g+2})$，任取 $k\notin S$。对第 $k$ 个输出因子，固定正交标准基的完备性给出对任意联合算子 $X$ 的恒等式
$$
\sum_{r_k=0}^1
(I\otimes\langle\eta_{k,r_k}|\otimes I)X
(I\otimes|\eta_{k,r_k}\rangle\otimes I)
=\operatorname{Tr}_{B_k}X.
$$
两个恒等因子各表示该位置前、后的全部旁观因子。这是偏迹在任意正交标准基下的表达。其余位置上的选择都是固定的，作用在不相交张量因子上，所以其 bra 收缩及隐藏结果求和均与此求和、偏迹交换；对最终记忆取偏迹也同样交换。这一步无需假设各测量结果独立。

先不施加任何其余位置的投影，将第 $k$ 个输出两侧取为完整非空块
$$
K_-=B_L\otimes B_1\otimes\cdots\otimes B_{k-1},\qquad
K_+=B_{k+1}\otimes\cdots\otimes B_g\otimes B_R.
$$
这两块的长度分别为 $k\ge1$ 和 $g+1-k\ge1$。命题 133.1 的纯边界分块公式取输入 $P_0=\operatorname{outer}(m_0)$、忽略前缀长度 $0$、左块长度 $k$、间隔长度 $1$、右块长度 $g+1-k$，即给
$$
\operatorname{Tr}_{B_k}\Omega_{\rm out}
=\theta^{P_0}_{0;k,1,g+1-k}
=\sum_{\nu=1}^N U_\nu\otimes V_\nu,
\qquad U_\nu\ge0,\quad V_\nu\ge0.
$$
其中凸权重已吸收入正因子，分解是在 $K_-\mid K_+$ 上进行的；命题 133.1 允许发出左块后左块与活动记忆相关，并未以独立边缘替换该相关输入。

在 $K_-$ 上，对 $S\cap\{1,\ldots,k-1\}$ 的位置作指定 $y$ 的 bra 收缩，对其余内部位置取偏迹，记所得局部线性映射为 $\Phi_-:\mathcal L(K_-)\to\mathcal L(B_L)$。同样定义 $\Phi_+:\mathcal L(K_+)\to\mathcal L(B_R)$。每一步 $X\mapsto KX\operatorname{adj}(K)$ 与偏迹均保持正性，所以两映射把各正因子送到正因子；它们可以不保迹。由刚才的交换恒等式与有限求和的分配律，
$$
\begin{aligned}
Q_{S,y}
&=(\Phi_-\otimes\Phi_+)(\operatorname{Tr}_{B_k}\Omega_{\rm out})\\
&=\sum_{\nu=1}^N\Phi_-(U_\nu)\otimes\Phi_+(V_\nu)
\in\operatorname{Sep}_+(L:R).
\end{aligned}
$$
这恰是所有相容完整分支的未归一化和，因此保留实际 Born 权重，而不是先归一化每条分支再等权混合。上述等式也包含零事件。

若 $q=q_{S,y}>0$，写 $A_\nu=\Phi_-(U_\nu)$、$F_\nu=\Phi_+(V_\nu)$ 及 $a_\nu=\operatorname{Tr}A_\nu$、$f_\nu=\operatorname{Tr}F_\nu$。正算子迹为零则算子为零；删去 $a_\nu f_\nu=0$ 的零乘积项后，
$$
\frac{Q_{S,y}}q
=\sum_{\nu:a_\nu f_\nu>0}
\frac{a_\nu f_\nu}{q}\,
\frac{A_\nu}{a_\nu}\otimes\frac{F_\nu}{f_\nu},\qquad
\sum_\nu\frac{a_\nu f_\nu}{q}=1.
$$
这就是有限凸乘积密度分解。按命题 138.1 证明中的谱细化，将每个局部密度各自谱分解再分配求和，得到有限单位乘积纯态系综。每个乘积纯态的系数矩阵秩一，故纯态 concurrence 为零；凸顶非负且不超过这个零平均值，所以也为零。（A）成立。

对（B），完整测量后的经典记录与端点联合态可写成
$$
\sum_{r\in\{0,1\}^g}|r\rangle\langle r|\otimes Q_r.
$$
值无关且相互独立的擦除使任一给定记录 $r$ 产生掩码 $S$ 的概率恰为 $w_S$，与 $r$ 无关；它产生接口值 $(S,y)$ 当且仅当 $r_S=y$。经典通道的线性性于是给出事件算子
$$
\sum_{r:r_S=y}w_SQ_r=w_SQ_{S,y},
$$
其迹为 $w_Sq_{S,y}$。只有该迹为正时才归一化，此时 $w_S>0$、$q_{S,y}>0$，约去 $w_S$ 即得所列条件密度。所有事件的概率之和为
$$
\sum_{S\subseteq[g]}w_S\sum_yq_{S,y}
=\sum_{S\subseteq[g]}w_S
=\prod_{k=1}^g(t_k+(1-t_k))=1.
$$
这里对每个固定掩码有 $\sum_yq_{S,y}=\sum_rq_r=1$，不对 Born 权重作逐位置分解。

当 $g\ge1$，所有真子掩码的正概率分支由（A）贡献零 concurrence；完整掩码 $S=[g]$ 的权重是 $w_{[g]}=\prod_kt_k$，其保留值就是完整记录。因此正概率项的求和给
$$
A_g(\mathrm{erased})=w_{[g]}
\sum_{r:q_r>0}q_r\mathcal C_{\rm conc}(\theta_r)
=\left(\prod_kt_k\right)2\alpha^{g+3}\prod_kB_k.
$$
若 $w_{[g]}=0$，完整掩码没有正概率事件，上式两侧均为零，未对这些事件定义条件态。若 $g=0$，唯一的空掩码同时是完整掩码，$C_\varnothing=s^3J$、$q_\varnothing=1$；命题 138.1 给唯一 concurrence 为 $2\alpha^3$，也与命题 132.1 的纯边界相邻密度 $G_0$ 相符。故空乘积公式同样成立。任一 $t_k=0$ 的结论随之得到。若改成结果相关的掩码律 $p(S\mid r)$，对应算子应为 $\sum_{r:r_S=y}p(S\mid r)Q_r$；不能把这个因子移出求和。这说明值无关性在证明中的确切作用。

最后证（C）。令 $Z=\operatorname{diag}(1,-1)$。两局部 bra 给 $D_{k,0}=I/\sqrt2$、$D_{k,1}=Z/\sqrt2$，故直接在命题 137.1 的转移乘积中相乘得
$$
C_r=\frac{s^5}{2}M_r,\qquad M_r=JZ^{r_1}JZ^{r_2}J,
$$
$$
M_{00}=\begin{pmatrix}3&2\\2&1\end{pmatrix},\quad
M_{01}=\begin{pmatrix}1&2\\0&1\end{pmatrix},\quad
M_{10}=\begin{pmatrix}1&0\\2&1\end{pmatrix},\quad
M_{11}=\begin{pmatrix}-1&0\\0&1\end{pmatrix}.
$$
每个 $M_r$ 非零，故四个完整记录均有正概率。若 $v_r=\operatorname{vec}_{LR}(M_r)$、$e_r=\operatorname{vec}_{LR}(M_rE_0)$，则
$$
Q_r=\frac{\alpha^5}{4}\bigl(v_rv_r^{\mathsf T}+\alpha e_re_r^{\mathsf T}\bigr).
$$
此处向量均实，所以普通转置就是伴随。记录已经经典化，按奇偶合并只对 $Q_r$ 相加，不产生不同记录振幅的交叉项；不把这个经典处理替换成内部量子系统上的相干奇偶投影或 $C_{00}+C_{11}$ 的分支振幅。

置 $u=1+\alpha$。在 $00,01,10,11$ 次序下，逐项外积给出显式未归一化矩阵
$$
Q_{\rm even}=\frac{\alpha^5}{4}
\begin{pmatrix}
10u&6&6u&2\\
6&4&4&2\\
6u&4&4u&2\\
2&2&2&2
\end{pmatrix},\qquad
Q_{\rm odd}=\frac{\alpha^5}{4}
\begin{pmatrix}
2u&2&2u&2\\
2&4&0&2\\
2u&0&4u&2\\
2&2&2&2
\end{pmatrix}.
$$
取迹并用 $\alpha^5=5\alpha-3$、$\alpha^2=1-\alpha$，有
$$
\begin{aligned}
q_{\rm even}
&=\frac{\alpha^5}{4}(20+14\alpha)
=\frac{(5\alpha-3)(20+14\alpha)}4
=\frac52-3\alpha,\\
q_{\rm odd}
&=\frac{\alpha^5}{4}(12+6\alpha)
=\frac{(5\alpha-3)(12+6\alpha)}4
=3\alpha-\frac32.
\end{aligned}
$$
两式的首个表达式直接为正，末个表达式相加为一。

采用命题 132.1、137.1 的右偏转置约定
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
记 $P_b=(4/\alpha^5)\operatorname{PT}_R(Q_b)$，则
$$
P_{\rm even}=\begin{pmatrix}
10u&6&6u&4\\
6&4&2&2\\
6u&2&4u&2\\
4&2&2&2
\end{pmatrix},\qquad
P_{\rm odd}=\begin{pmatrix}
2u&2&2u&0\\
2&4&2&2\\
2u&2&4u&2\\
0&2&2&2
\end{pmatrix}.
$$
为展开行列式，偶矩阵第一行四个不带符号的三阶余子式依次为
$$
8(2\alpha+1),\quad 8(2\alpha+1),\quad-8(3\alpha+1),\quad-8\alpha;
$$
奇矩阵第一行前三个相应余子式为 $8(2\alpha+1)$、$8(2\alpha+1)$、$-8u$，第四项的系数为零。因此沿第一行展开给
$$
\begin{aligned}
\frac{\det P_{\rm even}}{16}
&=5u(2\alpha+1)-3(2\alpha+1)-3u(3\alpha+1)+2\alpha
=\alpha^2-\alpha-1,\\
\frac{\det P_{\rm odd}}{16}
&=u(2\alpha+1)-(2\alpha+1)-u^2
=\alpha^2-\alpha-1.
\end{aligned}
$$
由 $\alpha^2+\alpha=1$，两者均等于 $-2\alpha$。恢复四维矩阵的标量因子，便得两个精确恒等式
$$
\det\operatorname{PT}_R(Q_{\rm even})
=\det\operatorname{PT}_R(Q_{\rm odd})
=\left(\frac{\alpha^5}{4}\right)^4(-32\alpha)
=-\frac{\alpha^{21}}8<0.
$$
两偏转置矩阵均为 Hermitian；正半定 Hermitian 矩阵的特征值非负，其行列式作为特征值之积亦非负，所以此负行列式排除正半定性。另一方面，若 $Q=\sum_\nu A_\nu\otimes F_\nu$ 且各因子正半定，则
$$
\operatorname{PT}_R(Q)=\sum_\nu A_\nu\otimes F_\nu^{\mathsf T}\ge0,
$$
因为正矩阵的转置仍正。这是可分性之偏转置正性的必要条件，亦见命题 132.1 所引 Asher Peres，*Separability Criterion for Density Matrices*，Physical Review Letters 77，1413–1415（1996），[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)。由于 $q_b>0$，归一化只将对应行列式除以自己的 $q_b^4$：
$$
\det\operatorname{PT}_R(Q_b/q_b)=-\frac{\alpha^{21}}{8q_b^4}<0
\quad(b=\mathrm{even},\mathrm{odd}).
$$
故两个条件端点密度均纠缠。仅保留 $r_1$ 或仅保留 $r_2$，则分别取（A）的 $S=\{1\}$ 或 $S=\{2\}$，均为真子集，得到可分条件态；这并不适用于联合标签 $r_1\mathbin{\oplus}r_2$。

同一例也落实了（B）的值无关性边界：若规定偶记录揭示 $S=\varnothing$，奇记录揭示 $S=\{1\}$ 及其保留值，则所有揭示的掩码都是真子集，但空掩码事件的算子是 $Q_{\rm even}$，其正概率条件态纠缠。该掩码选择依赖联合结果，并非（B）的独立擦除。

最后，由所列 $M$ 矩阵及两记忆列的实际权重，
$$
q_{00}=\frac{\alpha^5}{4}(18+13\alpha)>0,\qquad
q_{11}=\frac{\alpha^5}{4}(2+\alpha)>0,
$$
$$
\langle01|Q_{00}|01\rangle=\frac{\alpha^5}{4}\,4,
\qquad \langle01|Q_{11}|01\rangle=0.
$$
分别除以各自的正概率即得陈述中的两个条件预测，它们不同而奇偶值相同。因而这里保留纠缠的单比特反例不保留完整记录的全部端点预测，也不给出任意 $g$ 的奇偶结论或一般压缩最优性、比特或熵下界。全部结论的量词限于所写的固定生成、固定选基及无反馈记录接口，不附加物理擦除代价、Bell 产率、任意局部操作与经典通信的结论，亦不赋予 $g$ 时空度量含义。证毕。

## 追加锚（本行以下为增补区）

## 141. 两内部位经典奇偶记录的独立翻转与精确可分阈值

**命题 141.1（带噪奇偶报告的条件端点可分性）。** 沿用命题 140.1（C）的完整加减基仪器与命题 130.1 的纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n\quad(0\le n<4).
$$
各空间均取正交标准基，恰好发出四位，完整次序为
$$
B_L\otimes B_1\otimes B_2\otimes B_R\otimes M.
$$
左右端点分别是第一位和第四位，左端点之前没有被忽略的前缀。生成过程中不读取、测量或重置记忆，最终记忆取偏迹且不可访问。两个内部输出分别在事先固定的局部正交基
$$
|\eta_r\rangle=\frac{|0\rangle+(-1)^r|1\rangle}{\sqrt2}
\quad(r=0,1),\qquad |\eta_0\rangle=|+\rangle,\quad |\eta_1\rangle=|-\rangle
$$
中测量一次。测量全部完成且结果已为经典记录后，形成
$$
b=r_1\mathbin{\oplus}r_2\in\{0,1\}.
$$
结果不用于反馈、后续选基或端点操作；测后的内部系统及原始记录、奇偶记录的其他副本均不可访问，不允许环境重新耦合或记录的相干重组。端点的张量分割始终是完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。

记 $Q_0=Q_{\rm even}$、$Q_1=Q_{\rm odd}$ 为命题 140.1（C）的实际未归一化端点算子，$\operatorname{adj}$ 表示共轭转置。在 $00,01,10,11$ 次序下，令
$$
Q_b=\frac{\alpha^5}{4}N_b,\qquad
N_0=\begin{pmatrix}
10(1+\alpha)&6&6(1+\alpha)&2\\
6&4&4&2\\
6(1+\alpha)&4&4(1+\alpha)&2\\
2&2&2&2
\end{pmatrix},\qquad
N_1=\begin{pmatrix}
2(1+\alpha)&2&2(1+\alpha)&2\\
2&4&0&2\\
2(1+\alpha)&0&4(1+\alpha)&2\\
2&2&2&2
\end{pmatrix}.
$$
其实际先验概率为
$$
\begin{aligned}
q_0=\operatorname{Tr}Q_0
&=\frac{\alpha^5}{4}(20+14\alpha)=\frac52-3\alpha>0,\\
q_1=\operatorname{Tr}Q_1
&=\frac{\alpha^5}{4}(12+6\alpha)=3\alpha-\frac32>0,
\end{aligned}
\qquad q_0+q_1=1,\qquad q_0\ne q_1.
$$
在此经典奇偶位上施加独立二元对称通道：翻转位 $e$ 独立于测量记录及其端点系综，满足
$$
\Pr(e=1)=\epsilon\in[0,1],\qquad y=b\mathbin{\oplus}e.
$$
唯一保留的接口是 $y$；不保留 $b$ 或原始记录的隐藏副本，翻转位 $e$ 不可访问。这一通道只处理已经经典化的记录。相应事件算子、概率及条件密度定义为
$$
\widetilde Q_0=(1-\epsilon)Q_0+\epsilon Q_1,\qquad
\widetilde Q_1=\epsilon Q_0+(1-\epsilon)Q_1,
$$
$$
\widetilde q_y=\operatorname{Tr}\widetilde Q_y>0,\qquad
\rho_y=\frac{\widetilde Q_y}{\widetilde q_y}\quad(y=0,1).
$$
特别地，实际归一化混合权重是贝叶斯后验
$$
\Pr(b\mid y)=\frac{\Pr(y\mid b)q_b}{\widetilde q_y},\qquad
\Pr(y\mid b)=
\begin{cases}1-\epsilon,&y=b,\\ \epsilon,&y\ne b,\end{cases}
\qquad
\rho_y=\sum_{b=0}^1\Pr(b\mid y)\frac{Q_b}{q_b}.
$$
先验不等，故直接以原通道权重混合两个归一化密度一般得到不同的态。

可分性采用命题 132.1 的有限凸乘积密度和定义，纠缠指不可分。沿用右偏转置约定
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
称密度为 PPT，是指其右偏转置正半定；NPT 指其右偏转置不是正半定。则对每个 $\epsilon\in[0,1]$ 和每个 $y\in\{0,1\}$，
$$
\rho_y\text{ 为 NPT}
\quad\Longleftrightarrow\quad
\rho_y\text{ 纠缠}
\quad\Longleftrightarrow\quad
\epsilon(1-\epsilon)<\frac{\alpha^3}{2},
$$
$$
\rho_y\text{ 为 PPT}
\quad\Longleftrightarrow\quad
\rho_y\text{ 可分}
\quad\Longleftrightarrow\quad
\epsilon(1-\epsilon)\ge\frac{\alpha^3}{2}.
$$
置
$$
\epsilon_*=\frac{1-\sqrt{1-2\alpha^3}}2\in(0,1/2).
$$
两种报告的条件态均在 $[0,\epsilon_*)\cup(1-\epsilon_*,1]$ 上纠缠，在闭区间 $[\epsilon_*,1-\epsilon_*]$ 上可分；两个边界均为 PPT，且
$$
\operatorname{rank}\operatorname{PT}_R(\rho_y)=3
\qquad(\epsilon=\epsilon_*\text{ 或 }1-\epsilon_*).
$$
等价的纠缠条件为 $|1-2\epsilon|>\sqrt{1-2\alpha^3}$。同时令 $Q_+=Q_0+Q_1$、$Q_-=Q_0-Q_1$，则
$$
\widetilde Q_0+\widetilde Q_1=Q_+,\qquad
\widetilde Q_0-\widetilde Q_1=(1-2\epsilon)Q_-.
$$
其中 $Q_+$ 是迹为一的可分端点密度。$\epsilon=0$ 给出完整奇偶报告，$\epsilon=1$ 交换两个报告标签，而 $\epsilon=1/2$ 时两个归一化分支均恰为 $Q_+$。

证明。命题 140.1（C）的完整仪器在两条最终记忆列上取偏迹，给出上述 $Q_b\ge0$、正迹 $q_b$ 及其和为一。测量后的奇偶记录与端点联合态为
$$
\sum_{b=0}^1|b\rangle\langle b|\otimes Q_b.
$$
独立经典通道将报告为 $y$ 的项合并为 $\sum_b\Pr(y\mid b)Q_b$，正是所列 $\widetilde Q_y$，没有不同原始记录间的振幅交叉项。其迹是两个严格正数 $q_0,q_1$ 的凸组合，所以对整个闭参数区间均严格为正；除以该迹即得贝叶斯公式。由于 $N_0,N_1$ 的同一非零矩阵元 $01,01$ 均为 $4$，而迹不同，$Q_0/q_0\ne Q_1/q_1$。例如 $\epsilon=1/2$ 时后验仍为 $q_b$，以 $1/2,1/2$ 混合这两个不同密度便与实际后验混合不同。

取任意 $t\in[0,1]$，令 $N(t)=(1-t)N_0+tN_1$。按右偏转置定义逐块转置，得到
$$
A(t):=\operatorname{PT}_R(N(t))
=\begin{pmatrix}d&\operatorname{adj}(v)\\v&B\end{pmatrix},\qquad
d=(10-8t)(1+\alpha),\qquad
v=\begin{pmatrix}6-4t\\(6-4t)(1+\alpha)\\4-4t\end{pmatrix},
$$
$$
B=\begin{pmatrix}4&2&2\\2&4+4\alpha&2\\2&2&2\end{pmatrix}.
$$
对任意 $z=(z_0,z_1,z_2)^{\mathsf T}\in\mathbb C^3$，直接展开有
$$
\operatorname{adj}(z)Bz
=2|z_0|^2+(2+4\alpha)|z_1|^2+2|z_0+z_1+z_2|^2.
$$
三个系数均严格为正；右边为零先迫使 $z_0=z_1=0$，继而 $z_2=0$，故 $B>0$。其分解及行列式为
$$
B=\operatorname{adj}(L)DL,\qquad
L=\begin{pmatrix}1&0&0\\0&1&0\\1&1&1\end{pmatrix},\qquad
D=\operatorname{diag}(2,2+4\alpha,2),\qquad
\det B=8+16\alpha>0.
$$
令 $S(t)=d-\operatorname{adj}(v)B^{-1}v$。对任意 $x\in\mathbb C$ 及 $z\in\mathbb C^3$，完整二次型配方为
$$
\operatorname{adj}\begin{pmatrix}x\\z\end{pmatrix}
A(t)\begin{pmatrix}x\\z\end{pmatrix}
=S(t)|x|^2+
\operatorname{adj}(z+B^{-1}vx)B(z+B^{-1}vx).
$$
变量变换 $(x,z)\mapsto(x,z+B^{-1}vx)$ 可逆且行列式为一。因此 $A(t)$ 与 $\operatorname{diag}(S(t),B)$ 合同，并有
$$
A(t)\ge0\quad\Longleftrightarrow\quad S(t)\ge0,
\qquad \det A(t)=(\det B)S(t).
$$
在这一矩阵族内，$B>0$ 因而使正半定性等价于行列式非负；这一步依赖所证的正定块。

为显式计算标量补量，记 $h=6-4t$、$w=4-4t$，则 $h-w=2$，且由上面的三角分解，
$$
\begin{aligned}
\operatorname{adj}(v)B^{-1}v
&=\frac{(v_0-v_2)^2}{2}
+\frac{(v_1-v_2)^2}{2+4\alpha}+\frac{v_2^2}{2}\\
&=2+\frac{(2+\alpha h)^2}{2+4\alpha}+\frac{w^2}{2}.
\end{aligned}
$$
这里 $v$ 为实向量，故这些平方也等于平方模。乘以 $\det B$ 后逐项展开给
$$
\begin{aligned}
\det A(t)
&=(8+16\alpha)\left((10-8t)(1+\alpha)-2-\frac{(4-4t)^2}{2}\right)
-4\bigl(2+\alpha(6-4t)\bigr)^2\\
&=-32\alpha+64(2+\alpha)t(1-t)
+16(\alpha^2+\alpha-1)\bigl(1+4t(1-t)\bigr)\\
&=-32\alpha+64(2+\alpha)t(1-t).
\end{aligned}
$$
第二行是尚未施加 $\alpha^2+\alpha=1$ 的多项式恒等式，第三行才用该关系。再由 $\alpha^3=2\alpha-1$ 及 $(2+\alpha)\alpha^3=\alpha$，得到
$$
\det A(t)=64(2+\alpha)\left(t(1-t)-\frac{\alpha^3}{2}\right).
$$
由于 $2+\alpha>0$，结合配方即得 $A(t)$ 正半定当且仅当 $t(1-t)\ge\alpha^3/2$；严格反向不等式时 $S(t)<0$，取 $x=1$、$z=-B^{-1}v$ 就给出严格负二次型。

对报告 $y$ 分别取
$$
t_0=\epsilon,\qquad t_1=1-\epsilon.
$$
于是 $t_y(1-t_y)=\epsilon(1-\epsilon)$，且
$$
\operatorname{PT}_R(\widetilde Q_y)=\frac{\alpha^5}{4}A(t_y),\qquad
\operatorname{PT}_R(\rho_y)=\frac{\alpha^5}{4\widetilde q_y}A(t_y),
$$
$$
\det\operatorname{PT}_R(\widetilde Q_y)
=\left(\frac{\alpha^5}{4}\right)^4
\bigl[-32\alpha+64(2+\alpha)\epsilon(1-\epsilon)\bigr],
$$
$$
\det\operatorname{PT}_R(\rho_y)
=\frac{(\alpha^5/4)^4}{\widetilde q_y^4}
\bigl[-32\alpha+64(2+\alpha)\epsilon(1-\epsilon)\bigr].
$$
所有缩放因子均为正，故两报告具有同一个 PPT/NPT 判定。归一化行列式各除以自己的 $\widetilde q_y^4$，不要求两值相等。在等号边界 $S(t_y)=0$ 而 $B>0$，合同式给出右偏转置秩恰为 $3$，同时为正半定。

当偏转置不是正半定时，命题 136.1 证明中使用的 Peres 必要条件排除可分性：若 $\rho=\sum_\nu p_\nu U_\nu\otimes V_\nu$ 是有限凸乘积密度和，则
$$
\operatorname{PT}_R(\rho)=\sum_\nu p_\nu U_\nu\otimes V_\nu^{\mathsf T}\ge0,
$$
因为正矩阵的转置仍正。该必要条件见 Asher Peres，*Separability Criterion for Density Matrices*，Physical Review Letters 77，1413–1415（1996），[DOI:10.1103/PhysRevLett.77.1413](https://doi.org/10.1103/PhysRevLett.77.1413)。

当偏转置正半定时，使用 M. Horodecki、P. Horodecki、R. Horodecki，*Separability of Mixed States: Necessary and Sufficient Conditions*，[arXiv:quant-ph/9605038](https://arxiv.org/abs/quant-ph/9605038)，[第二版定理 3，PDF 第 8 页](https://arxiv.org/pdf/quant-ph/9605038v2)，Physics Letters A 223，1–8（1996），[DOI:10.1016/S0375-9601(96)00706-2](https://doi.org/10.1016/S0375-9601(96)00706-2) 的 $\mathbb C^2\otimes\mathbb C^2$ 充分性：此空间上的密度若 PPT，则可分。这里的 $\rho_y$ 已是该完整空间上的密度，故符合该定理的维数与正性、迹条件。

该文第 3 页以有限凸乘积密度和在迹范数中的闭包定义可分态；它与这里的有限和定义一致。事实上，两个局部密度集合均为有限维紧集，故乘积密度集合
$$
\mathcal P=\{U\otimes V:U,V\ge0,\ \operatorname{Tr}U=\operatorname{Tr}V=1\}
$$
亦紧，且包含在实仿射维数为 $15$ 的四阶迹一 Hermitian 空间中。若一个凸组合含超过 $16$ 个正权重项 $\sum_i p_i R_i$，仿射相关性给出不全为零的实数 $c_i$，满足
$$
\sum_i c_i=0,\qquad \sum_i c_iR_i=0.
$$
其中有正的 $c_i$。取 $\lambda=\min_{c_i>0}p_i/c_i$，将权重改为 $p_i-\lambda c_i$，保持非负性、总和与所表示的态，并至少消去一项。有限次消元将项数降至至多 $16$。因此 $\operatorname{conv}(\mathcal P)$ 是紧集 $\Delta_{15}\times\mathcal P^{16}$ 在连续映射 $((p_i),(R_i))\mapsto\sum_i p_iR_i$ 下的像；这里 $\Delta_{15}=\{p\in\mathbb R^{16}:p_i\ge0,\sum_i p_i=1\}$，不足的项补零权重。这个凸包紧而闭，在有限维迹范数中也闭，故上述闭包没有加入新的态。这便使所引充分性恰好给出本命题所用的有限凸分解意义下的可分性，并与必要条件共同完成两个等价式。

最后，$\alpha^3=\sqrt5-2$ 给
$$
1-2\alpha^3=5-2\sqrt5\in(0,1),\qquad
\epsilon(1-\epsilon)=\frac{1-(1-2\epsilon)^2}{4}.
$$
前一个区间由 $2<\sqrt5<5/2$ 得到。因此两个根为 $\epsilon_*$ 和 $1-\epsilon_*$，分别严格位于 $0$ 与 $1/2$、$1/2$ 与 $1$ 之间；二次式在两根之间达到或超过阈值，外侧严格低于阈值。这证明所列闭中间区间、两外侧区间及记录对比的等价不等式。

经典通道的两条线性式直接相加、相减，便得 $Q_+$ 不变与 $Q_-$ 乘以 $1-2\epsilon$。完整仪器的结果求和等于忽略内部输出，故
$$
Q_+=\operatorname{Tr}_{B_1,B_2,M}\operatorname{outer}(\Xi_4)
=\theta^{P_0}_{0;1,2,1},\qquad P_0=\operatorname{outer}(m_0).
$$
命题 133.1 在纯输入 $P_0$、忽略前缀长度 $0$、两端块长度各为 $1$、忽略间隔长度 $2$ 时给出此密度的可分性。$\epsilon=0,1$ 的两式分别保留、交换 $Q_0,Q_1$。$\epsilon=1/2$ 时 $\widetilde Q_0=\widetilde Q_1=Q_+/2$、$\widetilde q_0=\widetilde q_1=1/2$，故两个条件密度均为 $Q_+$，与阈值判定一致。证毕。

## 追加锚（本行以下为增补区）

## 142. 任意有限内部长度的总奇偶一位与条件端点纠缠的精确范围

**命题 142.1（固定加减基总奇偶记录的全长度分类）。** 取命题 130.1 的纯边界生成器，令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n.
$$
各空间均取正交标准基。对任意有限整数 $g\ge1$，在任何测量之前恰好发出 $g+2$ 个输出，次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 分别是第一位和最后一位已发出的 qubit，左端点之前没有被忽略的前缀；端点空间始终是完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$。生成过程中不读取、测量或重置记忆，最终记忆取偏迹且不可访问。每个内部输出在同一事先固定的局部正交基
$$
|\eta_r\rangle=\frac{|0\rangle+(-1)^r|1\rangle}{\sqrt2}
\quad(r=0,1)
$$
中测量一次。全部测量完成、结果已成为经典记录后，仅保留总奇偶位
$$
b=\bigoplus_{k=1}^g r_k\in\{0,1\}.
$$
这一位没有附加翻转通道。结果不用于反馈、后续选基或端点操作；测后的内部系统、原始记录及奇偶记录的其他副本均不可访问，不允许环境重新耦合或记录的相干重组。

以 $\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(u,v)=u\operatorname{adj}(v)$，$\operatorname{outer}(u)=\operatorname{outer}(u,u)$。对 $r=(r_1,\ldots,r_g)$，定义实际分支
$$
\chi_r=(I_{B_L}\otimes\langle\eta_{r_1}|\otimes\cdots\otimes
\langle\eta_{r_g}|\otimes I_{B_R}\otimes I_M)\Xi_{g+2},
\qquad Q_r=\operatorname{Tr}_M\operatorname{outer}(\chi_r),
$$
$$
Q_{g,b}=\sum_{r:\,\bigoplus_k r_k=b}Q_r,\qquad
q_{g,b}=\operatorname{Tr}Q_{g,b}.
$$
可分密度采用命题 132.1 的有限凸乘积密度和定义，纠缠指不可分；右偏转置约定为
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
则对所有有限整数 $g\ge1$ 及 $b\in\{0,1\}$，
$$
q_{g,b}=\frac12+(-1)^b\alpha^{g+2},\qquad 0<q_{g,b}<1.
$$
因此 $\rho_{g,b}=Q_{g,b}/q_{g,b}$ 总有定义，且
$$
\rho_{g,b}\text{ 纠缠}
\quad\Longleftrightarrow\quad
\operatorname{PT}_R(\rho_{g,b})\not\ge0
\quad\Longleftrightarrow\quad g\in\{1,2\},
$$
$$
\rho_{g,b}\text{ 可分}
\quad\Longleftrightarrow\quad
\operatorname{PT}_R(\rho_{g,b})>0
\quad\Longleftrightarrow\quad g\ge3.
$$
这里 $>0$ 指严格正定。两个事件之和满足
$$
Q_{g,0}+Q_{g,1}
=\operatorname{Tr}_{B_1,\ldots,B_g,M}\operatorname{outer}(\Xi_{g+2})
=\theta^{P_0}_{0;1,g,1},\qquad P_0=\operatorname{outer}(m_0),
$$
是命题 133.1 的可分无条件端点密度；各 $\rho_{g,b}$ 则是按总奇偶位条件化的密度。本命题的量词仅涉及上述固定基与总奇偶函数。

证明。写 $P_j=\operatorname{outer}(m_j)$、$E_{ij}=|i\rangle\langle j|$。命题 131.1 的矩阵单位展开及两个通道为
$$
T A\operatorname{adj}(T)
=\sum_{i,j=0}^1 A_{ij}E_{ij}\otimes\operatorname{outer}(m_i,m_j),
\qquad
\mathcal M(A)=A_{00}P_0+A_{11}P_1,
$$
$$
\Gamma_1(A)=\operatorname{Tr}_M(T A\operatorname{adj}(T))
=\begin{pmatrix}A_{00}&sA_{01}\\sA_{10}&A_{11}\end{pmatrix}.
$$
令
$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\mathcal L(A)=\operatorname{Tr}_B\bigl[(X\otimes I_M)T A\operatorname{adj}(T)\bigr],
$$
$$
U=\operatorname{outer}(m_0,m_1)=\begin{pmatrix}s&0\\\alpha&0\end{pmatrix},
\qquad V=\operatorname{adj}(U).
$$
上面的展开给出复线性映射
$$
\mathcal L(A)=A_{01}U+A_{10}V,
\qquad
\mathcal L(E_{00})=\mathcal L(E_{11})=0,\quad
\mathcal L(E_{01})=U,\quad\mathcal L(E_{10})=V,
$$
$$
\mathcal L(U)=\alpha V,\qquad \mathcal L(V)=\alpha U.
$$
从 $g=1$ 起逐次作用便得，对任意复矩阵 $A$，
$$
\mathcal L^g(A)=
\begin{cases}
\alpha^{g-1}(A_{01}U+A_{10}V),&g\text{ 为奇数},\\
\alpha^{g-1}(A_{01}V+A_{10}U),&g\text{ 为偶数}.
\end{cases}
$$
特别地，$\mathcal L^{g+2}=\alpha^2\mathcal L^g$ 对 $g\ge1$ 成立。

单个实际测量结果对记忆的 Kraus 算子及分支映射为
$$
K_r=(\langle\eta_r|\otimes I_M)T
=\frac{m_0\langle0|+(-1)^r m_1\langle1|}{\sqrt2},
\qquad
\Phi_r(A)=K_rA\operatorname{adj}(K_r)
=\frac{\mathcal M(A)+(-1)^r\mathcal L(A)}2.
$$
已发出因子上的测量与其后只作用于记忆及新输出的等距交换，故先发出全部输出再测量的协议，仍可按位置次序计算为 $\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}$。保持这个复合次序并分配有限和，得到
$$
\sum_{r\in\{0,1\}^g}\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}
=(\Phi_0+\Phi_1)^g=\mathcal M^g,
$$
$$
\sum_{r\in\{0,1\}^g}(-1)^{\sum_k r_k}
\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}
=(\Phi_0-\Phi_1)^g=\mathcal L^g.
$$
这里没有交换 $\mathcal M$ 与 $\mathcal L$。因而奇偶事件的实际记忆映射为
$$
\mathcal S_{g,b}
:=\sum_{r:\,\bigoplus_k r_k=b}\Phi_{r_g}\circ\cdots\circ\Phi_{r_1}
=\frac{\mathcal M^g+(-1)^b\mathcal L^g}{2}.
$$
相应的内部事件效应是
$$
\sum_{r:\,\bigoplus_k r_k=b}\bigotimes_{k=1}^g\operatorname{outer}(\eta_{r_k})
=\frac{I_{B^{\otimes g}}+(-1)^bX^{\otimes g}}2.
$$
此效应来自完整局部仪器结果的经典合并，事件算子中没有不同原始记录之间的振幅交叉项。

令 $\Omega=T P_0\operatorname{adj}(T)$ 为首个已发出端点与记忆的联合密度。再发出右端点并忽略最终记忆给出
$$
Q_{g,b}
=\bigl(\operatorname{Id}_{B_L}\otimes(\Gamma_1\circ\mathcal S_{g,b})\bigr)(\Omega)\ge0.
$$
这里最后的 $\Gamma_1$ 将活动记忆转为已发出的右端点。与命题 137.1 的系数公式对照，置
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
D_r=\frac1{\sqrt2}\operatorname{diag}(1,(-1)^r),\qquad
C_r=s^{g+3}JD_{r_1}J\cdots D_{r_g}J,
$$
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L\otimes|j\rangle_R.
$$
该命题的两记忆列公式恰给
$$
Q_r=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_{00})).
$$
因此上述通道式就是陈述中的 $\sum_{r:\,\bigoplus_k r_k=b}Q_r$，保留了两条最终记忆列及其实际 Born 权重。其正性来自这些实际分支的正算子和。

对左端点取迹，有 $\operatorname{Tr}_{B_L}\Omega=\mathcal M(P_0)$；该矩阵的两个非对角元均为 $\alpha^2s$。由 $\operatorname{Tr}U=\operatorname{Tr}V=s$，
$$
\operatorname{Tr}\mathcal L^g(\mathcal M(P_0))
=2\alpha^{g-1}\alpha^2s^2=2\alpha^{g+2}.
$$
$\mathcal M$ 与 $\Gamma_1$ 保迹，故
$$
q_{g,b}=\frac12\left(1+(-1)^b\,2\alpha^{g+2}\right).
$$
由 $\alpha^3=\sqrt5-2<1/2$ 及 $0<\alpha^{g+2}\le\alpha^3$，两个概率均严格位于 $0$ 与 $1$ 之间。求和消去带符号项，所得 $\theta^{P_0}_{0;1,g,1}$ 由命题 133.1 可分。这一步求得的是无条件密度。

下面求条件态的偏转置。定义
$$
z_n=\frac{1-(-\alpha^2)^n}{1+\alpha^2}\quad(n\ge0),\qquad
z_0=0,\quad z_1=1,\quad z_{n+1}=1-\alpha^2z_n.
$$
命题 131.1 写 $\sigma_n=\mathcal M^n(P_0)=(1-p_n)P_0+p_nP_1$，其中 $p_n=\alpha^2z_n$，所以 $1-p_n=z_{n+1}$。由于 $\mathcal M(E_{00})=P_0$，对 $g\ge1$ 有
$$
\mathcal M^g(E_{00})=\sigma_{g-1}=z_gP_0+(1-z_g)P_1.
$$
又 $\mathcal M(E_{11})=P_1$、$\mathcal M(P_1)=P_0$，故 $g=1$ 时直接用 $z_0=0$，$g\ge2$ 时用 $\sigma_{g-2}$，统一得到
$$
\mathcal M^g(E_{11})=z_{g-1}P_0+(1-z_{g-1})P_1.
$$
置
$$
H(z)=\begin{pmatrix}1-\alpha^2z&\alpha^2z\\\alpha^2z&\alpha^2z\end{pmatrix},\qquad
h=\begin{pmatrix}1\\\alpha\end{pmatrix},\quad e=\begin{pmatrix}1\\0\end{pmatrix},
\qquad c_g=s\alpha^{g-1},
$$
$$
D=\alpha\begin{pmatrix}1&s\\1&0\end{pmatrix},\qquad
\phi=|00\rangle+|11\rangle.
$$
实际首步满足 $Tm_0=\operatorname{vec}_{LM}(D)=(D\otimes I_M)\phi$，且 $\det D=-\alpha^2s\ne0$。对四个矩阵单位逐一应用刚才的公式，得到
$$
\begin{aligned}
\Gamma_1\mathcal M^g(E_{00})&=H(z_g),&
\Gamma_1\mathcal M^g(E_{11})&=H(z_{g-1}),\\
\Gamma_1\mathcal M^g(E_{01})&=0,&
\Gamma_1\mathcal M^g(E_{10})&=0,\\
\Gamma_1\mathcal L^g(E_{00})&=0,&
\Gamma_1\mathcal L^g(E_{11})&=0,\\
\Gamma_1\mathcal L^g(E_{01})&=c_gW_g,&
\Gamma_1\mathcal L^g(E_{10})&=c_g\operatorname{adj}(W_g),
\end{aligned}
\qquad
W_g=\begin{cases}he^{\mathsf T},&g\text{ 为奇数},\\eh^{\mathsf T},&g\text{ 为偶数}.
\end{cases}
$$
这里 $\Gamma_1(U)=s he^{\mathsf T}$、$\Gamma_1(V)=s eh^{\mathsf T}$。将 $\operatorname{outer}(\phi)=\sum_{i,j}E_{ij}\otimes E_{ij}$ 展开，便得
$$
2Q_{g,b}=(D\otimes I_{B_R})\mathcal K_{g,b}\operatorname{adj}(D\otimes I_{B_R}),
$$
$$
\mathcal K_{g,b}=
\begin{pmatrix}
H(z_g)&(-1)^b c_gW_g\\
(-1)^b c_g\operatorname{adj}(W_g)&H(z_{g-1})
\end{pmatrix}.
$$
此合同只是矩阵恒等式，协议中没有执行 $D$ 或其逆作为局部操作。

右偏转置将每个二阶块转置，故保持两个实对称对角块，并反转非对角秩一块的方向。令 $Z=\operatorname{diag}(1,-1)$，则
$$
\mathcal K_{g,1}=(Z\otimes I)\mathcal K_{g,0}(Z\otimes I),\qquad
\operatorname{PT}_R(\mathcal K_{g,1})
=(Z\otimes I)\operatorname{PT}_R(\mathcal K_{g,0})(Z\otimes I).
$$
此外，偏转置与左因子合同交换，因而
$$
\operatorname{PT}_R(\rho_{g,b})
=\frac1{2q_{g,b}}(D\otimes I)
\operatorname{PT}_R(\mathcal K_{g,b})\operatorname{adj}(D\otimes I).
$$
可逆合同及正数缩放保持 Hermitian 矩阵的正、负、零惯性指数，所以两种 $b$ 有相同的 PPT 或 NPT 分类；这一论证不要求两个实际归一化密度有相同的谱。

当 $g=1$ 时，$z_1=1$、$z_0=0$，$\operatorname{PT}_R(\mathcal K_{1,b})$ 在 $00,11$ 指标上的主子式为
$$
\det\begin{pmatrix}\alpha&(-1)^b s\alpha\\(-1)^b s\alpha&0\end{pmatrix}
=-\alpha^3<0.
$$
所以两个分支均为 NPT。

当 $g\ge2$ 时，递推使所用的两个 $z$ 均在 $(0,1]$ 内。令
$$
d(z)=1-2\alpha^2z.
$$
由 $2\alpha^2<1$ 得 $d(z)>0$，且
$$
\det H(z)=\alpha^2z\,d(z)>0,\qquad H(z)>0.
$$
二阶逆矩阵给出
$$
H(z)^{-1}=\frac1{\alpha^2z\,d(z)}
\begin{pmatrix}\alpha^2z&-\alpha^2z\\-\alpha^2z&1-\alpha^2z\end{pmatrix},
$$
$$
e^{\mathsf T}H(z)^{-1}e=\frac1{d(z)},\qquad
h^{\mathsf T}H(z)^{-1}h=\frac{1-\alpha z}{z\,d(z)}.
$$
后一式的分子在约去 $\alpha^2$ 前为
$$
\alpha^2z-2\alpha^3z+\alpha^2(1-\alpha^2z)
=\alpha^2(1-\alpha z).
$$

为判定整个偏转置，写 $A=H(z_g)$、$B=H(z_{g-1})$，其右上块在奇数 $g$ 时为 $(-1)^b c_g e h^{\mathsf T}$，在偶数 $g$ 时为 $(-1)^b c_g h e^{\mathsf T}$。一般地，$A>0$ 时有可逆合同
$$
\begin{pmatrix}I&0\\-R^\dagger A^{-1}&I\end{pmatrix}
\begin{pmatrix}A&R\\R^\dagger&B\end{pmatrix}
\begin{pmatrix}I&-A^{-1}R\\0&I\end{pmatrix}
=\begin{pmatrix}A&0\\0&B-R^\dagger A^{-1}R\end{pmatrix}.
$$
若 $R=\lambda uv^\dagger$ 且 $B>0$，下块再经 $B^{-1/2}$ 合同成为
$$
I-ww^\dagger,\qquad
w=|\lambda|\sqrt{u^\dagger A^{-1}u}\,B^{-1/2}v.
$$
在 $w$ 的正交补上此矩阵为恒等，在其方向上的特征值为 $1-\|w\|^2$；$w=0$ 时它就是恒等。因此整个分块矩阵正半定当且仅当
$$
|\lambda|^2(u^\dagger A^{-1}u)(v^\dagger B^{-1}v)\le1,
$$
严格小于时整个矩阵正定，严格大于时存在负二次型。代入上述两个方向及逆二次型，定义
$$
z_*=
\begin{cases}z_{g-1},&g\text{ 为奇数},\\z_g,&g\text{ 为偶数},\end{cases}
\qquad
F_g=z_*d(z_g)d(z_{g-1})-c_g^2(1-\alpha z_*),
$$
便得
$$
\operatorname{PT}_R(\mathcal K_{g,b})\ge0\quad\Longleftrightarrow\quad F_g\ge0,
\qquad
\operatorname{PT}_R(\mathcal K_{g,b})>0\quad\Longleftrightarrow\quad F_g>0.
$$
这使用了两个正定对角块及秩一 Schur 补，而非一般矩阵的行列式符号判据。特别地，$g=2$ 时 $z_2=\alpha$、$z_1=1$、$c_2^2=\alpha^3$、$d(1)=\alpha^3$，故
$$
F_2=\alpha^4(1-2\alpha^3)-\alpha^3(1-\alpha^2)
=-2\alpha^7<0.
$$
这与命题 140.1（C）的两内部位 NPT 结论一致。

最后给出对所有 $g\ge3$ 的统一严格界。对每个 $n\ge2$，有
$$
\alpha\le z_n\le2\alpha^2.
$$
事实上 $z_2=\alpha$，且 $\alpha\le2\alpha^2$ 由 $\alpha>1/2$ 得到。递减映射 $z\mapsto1-\alpha^2z$ 在该区间的最大值为
$$
1-\alpha^3=2\alpha^2,
$$
最小值满足
$$
1-2\alpha^4-\alpha=\alpha^2(1-2\alpha^2)>0.
$$
它因此将该区间映入自身，归纳即得所述全 $n$ 界。又由 $\alpha^2+\alpha=1$ 化简可得精确恒等式
$$
1-4\alpha^4=\alpha^2+\alpha^7.
$$
所以对 $g\ge3$，两个 $z_g,z_{g-1}$ 均满足
$$
d(z)\ge1-4\alpha^4=\alpha^2+\alpha^7>\alpha^2.
$$
同时
$$
z_*\ge\alpha,\qquad
c_g^2=\alpha^{2g-1}\le\alpha^5,\qquad
0<1-\alpha z_*\le1-\alpha^2=\alpha.
$$
代入 Schur 标量得到
$$
F_g>\alpha\cdot\alpha^2\cdot\alpha^2-\alpha^5\cdot\alpha
=\alpha^5-\alpha^6=\alpha^7>0
\qquad(g\ge3).
$$
这直接涵盖每个有限整数 $g\ge3$，从而两个实际条件密度的整个右偏转置均严格正定。

可分密度的右偏转置必为正半定，因为有限凸乘积和逐项变为正矩阵与其正转置的张量积。因此 $g=1,2$ 的 NPT 排除可分性。对 $g\ge3$，$\rho_{g,b}$ 已由实际分支和及正概率归一化为完整 $\mathbb C^2\otimes\mathbb C^2$ 上的密度，适用命题 141.1 所引并使用的二维 PPT 充分性：M. Horodecki、P. Horodecki、R. Horodecki，*Separability of Mixed States: Necessary and Sufficient Conditions*，[arXiv:quant-ph/9605038v2，定理 3，PDF 第 8 页](https://arxiv.org/pdf/quant-ph/9605038v2)，Physics Letters A 223，1–8（1996），[DOI:10.1016/S0375-9601(96)00706-2](https://doi.org/10.1016/S0375-9601(96)00706-2)。该文可分态闭包定义与本卷有限凸和定义的一致性已在命题 141.1 证明，故这里得到的正是陈述中的可分性。命题 137.1 对所有完整加减基记录给出的纠缠性，并不使同一奇偶事件内的经典混合仍然纠缠；以上实际事件算子与统一 Schur 界给出了该混合的精确范围。证毕。

## 追加锚（本行以下为增补区）

## 143. 确定性一位记录的两内部位唯一性与三内部位全划分障碍

**命题 143.1（全部布尔二分下的条件端点纠缠）。** 沿用命题 130.1、137.1 的纯边界生成器，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
t=1+\alpha,\qquad t^2=t+1,\qquad 1<t<2,
$$
$$
B=M=\mathbb C^2,\qquad
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,
\qquad T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n.
$$
各空间取正交标准基。对有限整数 $g\ge1$，先恰好发出 $g+2$ 个输出，次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 分别为第一个和最后一个已发出的单量子比特因子，端点的联合空间始终是完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$；左端点之前没有被忽略的前缀。生成过程中不读取、测量或重置记忆，最终记忆取偏迹且不可访问。每个内部输出在事先固定的加减基
$$
|\eta_{r_k}\rangle=\frac{|0\rangle+(-1)^{r_k}|1\rangle}{\sqrt2}
\quad(r_k\in\{0,1\})
$$
中测量一次。全部测量完成、结果成为经典记录 $r=(r_1,\ldots,r_g)$ 后，仅保留事先指定的确定性满射
$$
f:\{0,1\}^g\longrightarrow\{0,1\}
$$
的值，不附加随机通道。测后的内部系统、原始记录及报告的其他副本均不可访问；结果不用于反馈、后续选基或端点操作，不允许环境重新耦合或记录的相干重组。

以 $\operatorname{adj}$ 表示共轭转置，$\operatorname{outer}(v)=v\operatorname{adj}(v)$，并取命题 137.1 的逐行向量化约定
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
记
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad
\kappa_g=s^{g+3}2^{-g/2}>0,
$$
$$
C_r=\kappa_g JZ^{r_1}J\cdots Z^{r_g}J,
\qquad
Q_r=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),
\qquad q_r=\operatorname{Tr}Q_r.
$$
这里 $Q_r$ 正是实际测量分支对最终记忆取偏迹所得的算子，两个外积保留两条未读记忆列及其原权重。对非空记录集 $S\subseteq\{0,1\}^g$，先定义
$$
Q_S=\sum_{r\in S}Q_r,\qquad q_S=\operatorname{Tr}Q_S=\sum_{r\in S}q_r,
$$
再在 $q_S>0$ 时定义 $\theta_S=Q_S/q_S$。可分性采用命题 132.1 的有限凸乘积密度和定义，纠缠指不可分；右偏转置为
$$
\operatorname{PT}_R(|ij\rangle\langle kl|)=|il\rangle\langle kj|.
$$
右偏转置正半定称为 PPT，否则称为 NPT。两个报告的记录集为 $S_b=f^{-1}(b)$。将 $f$ 与 $1-f$ 视为同一个无标号二分，则有以下结论。

对所有有限 $g\ge1$，每个非空 $S$ 都有 $q_S>0$，且
$$
\theta_S=\sum_{r\in S}\frac{q_r}{q_S}\theta_{\{r\}},\qquad
q_{S_0}+q_{S_1}=1.
$$
集合的基数不作为其概率。当 $g=1$ 时，唯一二分 $\{0\}\mid\{1\}$ 的两个报告均 NPT。当 $g=2$ 时，全部七个二分中恰有一个使两个报告均纠缠，即
$$
\{00,11\}\mid\{01,10\};
$$
等价地，成功的满射恰为 $f(r)=r_1\mathbin{\oplus}r_2$ 及其补。其余六个二分中，四个 $1\mid3$ 二分恰有一个纠缠报告，两个非奇偶 $2\mid2$ 二分的两个报告均可分。当 $g=3$ 时，任意至少含四条记录的 $S$ 均给可分密度 $\theta_S$；因此全部 $127$ 个二分均不能使两个报告同时纠缠，其中 $35$ 个 $4\mid4$ 二分的两个报告均可分。特别地，断言
$$
\forall g\ge1\ \exists\text{满射 }f:\{0,1\}^g\to\{0,1\},\quad
\theta_{f^{-1}(0)}\text{ 与 }\theta_{f^{-1}(1)}\text{ 均纠缠}
$$
被 $g=3$ 反驳。本命题不判定各个 $g\ge4$ 是否存在这样的满射；命题 142.1 在这些长度对总奇偶函数的结论仍限于该函数。

证明。命题 137.1 的实际分支公式在上述加减基上给出
$$
\chi_r=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle_M
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle_M.
$$
对两条正交记忆列取偏迹正是所定义的 $Q_r$。$J,Z$ 均可逆且 $\kappa_g>0$，故每个 $C_r$ 可逆，从而
$$
q_r=\|C_r\|_F^2+\alpha\|C_rE_0\|_F^2>0,
\qquad \sum_{r\in\{0,1\}^g}q_r=1.
$$
后一式由该完整测量的正交完备性及 $\|\Xi_{g+2}\|=1$ 得到。记录已成为经典数据，合并事件只求 $Q_r$ 之和，没有不同记录间的振幅交叉项。于是每个非空事件的概率为正，满射的两报告均有正概率，归一化权重恰为陈述中的 $q_r/q_S$。

为处理整个记录集，使用同一个代数合同
$$
F=J^{-1}\otimes I_{B_R},\qquad
N_r=\kappa_g^{-1}J^{-1}C_r=Z^{r_1}J\cdots Z^{r_g}J.
$$
若
$$
v_r=\operatorname{vec}_{LR}(N_r)=(a,b,c,d)^{\mathsf T},\qquad
w_r=(a,0,c,0)^{\mathsf T},\qquad
P_r=\operatorname{outer}(v_r)+\alpha\operatorname{outer}(w_r),
$$
则
$$
P(S):=\sum_{r\in S}P_r
=\kappa_g^{-2}FQ_S\operatorname{adj}(F),\qquad
R(S):=\operatorname{PT}_R(P(S)).
$$
这是对整个事件的共同正数缩放与可逆左局部合同，没有分别归一化记录。其迹不替代实际概率 $q_S$。可逆局部合同及其逆均保持有限个正乘积算子之和，而右偏转置与左局部合同交换。因此 $Q_S$ 与 $P(S)$ 及各自的正迹归一化具有相同的可分性与 PPT 分类。$F$ 仅用于代数论证，协议没有增加端点操作。

所有 $N_r$ 都是实矩阵。直接对单条记录取右偏转置得
$$
R(\{r\})=
\begin{pmatrix}
ta^2&ab&tac&bc\\
ab&b^2&ad&bd\\
tac&ad&tc^2&cd\\
bc&bd&cd&d^2
\end{pmatrix}.
$$
记
$$
H=\begin{pmatrix}
0&0&0&-1\\
0&0&1&0\\
0&1&0&0\\
-1&0&0&0
\end{pmatrix}.
$$
偏转置只把 $\operatorname{outer}(v_r)$ 的 $00,11$ 与 $01,10$ 位置及其对称位置互换，变化分别为 $-\det N_r$ 和 $\det N_r$。另一方面，$w_r=(a,c)^{\mathsf T}\otimes|0\rangle$，故记忆项 $\alpha\operatorname{outer}(w_r)$ 在右偏转置下不变。由 $\det J=\det Z=-1$，得到适用于任意记录集的恒等式
$$
R(S)=P(S)+\left(\sum_{r\in S}\det N_r\right)H,
\qquad \det N_r=(-1)^{g+r_1+\cdots+r_g}.
$$
因此，只要 $S$ 中 $r_1+\cdots+r_g$ 为偶数与奇数的记录数相等，就有 $R(S)=P(S)\ge0$。这里平衡的是行列式的计数，并不要求原始 Born 概率相等。该正半定结论允许奇异矩阵。

翻转第一条记录位，记作 $\tau(r)=(1-r_1,r_2,\ldots,r_g)$，给出
$$
N_{\tau(r)}=ZN_r,\qquad
P(\tau S)=(Z\otimes I)P(S)(Z\otimes I),\qquad
R(\tau S)=(Z\otimes I)R(S)(Z\otimes I).
$$
故这对记录集保持分类。对 $g=3$，若以二进制整数表示记录，$\tau$ 就是与 $4$ 作异或。

每个原始记录的 NPT 可直接使用命题 137.1 的可逆分支论证。具体地，令 $G_r=C_r^{-1}\otimes I$、$z=(|01\rangle-|10\rangle)/\sqrt2$，则
$$
\operatorname{PT}_R\bigl(G_rQ_r\operatorname{adj}(G_r)\bigr)
=\begin{pmatrix}
t&0&0&0\\
0&0&1&0\\
0&1&0&0\\
0&0&0&1
\end{pmatrix},\qquad
\operatorname{adj}(z)\operatorname{PT}_R\bigl(G_rQ_r\operatorname{adj}(G_r)\bigr)z=-1.
$$
因左局部合同与右偏转置交换，$x_r=\operatorname{adj}(G_r)z$ 满足
$$
\operatorname{adj}(x_r)\operatorname{PT}_R(Q_r)x_r=-1,
\qquad
\operatorname{adj}(x_r)\operatorname{PT}_R(\theta_{\{r\}})x_r=-\frac1{q_r}<0.
$$
这证明所有单点事件 NPT，特别是 $g=1$ 的唯一二分成功。

现完整处理 $g=2$。由 $N_r=Z^{r_1}JZ^{r_2}J$ 得
$$
\begin{array}{c|rrrr}
r&a&b&c&d\\\hline
00&2&1&1&1\\
01&0&1&1&1\\
10&2&1&-1&-1\\
11&0&1&-1&-1
\end{array}.
$$
对偶事件 $E_2=\{00,11\}$，上述公共矩阵公式给出
$$
R(E_2)=\begin{pmatrix}
4t&2&2t&0\\
2&2&2&0\\
2t&2&2t&2\\
0&0&2&2
\end{pmatrix},\qquad
\det R(E_2)=-32(t-1)=-32\alpha<0.
$$
负的全阶主子式排除正半定性，奇事件 $\{01,10\}=\tau E_2$ 亦然。这与命题 140.1（C）的奇偶 NPT 结论一致。由于 $\det F=(\det J^{-1})^2=1$，对两个实际归一化报告分别有
$$
\det\operatorname{PT}_R(\theta_S)
=\frac{\kappa_2^8}{q_S^4}(-32\alpha)<0.
$$
另两个 $2\mid2$ 二分恰为
$$
\{00,01\}\mid\{10,11\},\qquad
\{00,10\}\mid\{01,11\}.
$$
其每个块都有一条偶记录与一条奇记录，故由平衡恒等式均 PPT；这也符合命题 140.1（A）的固定原始坐标删除结论。

四个 $1\mid3$ 二分的单点侧已证 NPT。将三元块按其缺失记录标识，第一位翻转把缺失 $10$、$11$ 分别化为缺失 $00$、$01$。两代表的矩阵为
$$
R(\{01,10,11\})=\begin{pmatrix}
4t&2&-2t&-1\\
2&3&-2&-1\\
-2t&-2&3t&3\\
-1&-1&3&3
\end{pmatrix},\qquad
R(\{00,10,11\})=\begin{pmatrix}
8t&4&0&-1\\
4&3&0&-1\\
0&0&3t&3\\
-1&-1&3&3
\end{pmatrix}.
$$
以 $\Delta_k(M)$ 表示按固定次序取 $M$ 左上角 $k\times k$ 主子矩阵的行列式，两行完整顺序主子式为
$$
\begin{array}{c|rrrr}
\text{缺失记录}&\Delta_1&\Delta_2&\Delta_3&\Delta_4\\\hline
00&4t&12t-4&12t+24&80-25t\\
01&8t&24t-16&24t+72&336-153t
\end{array}.
$$
这些值由行列式展开及 $t^2=t+1$ 得到。$1<t<2$ 使每项严格为正，故两矩阵均由 Sylvester 判据正定，第一位翻转覆盖另两组三元块。

下面处理 $g=3$ 的全部四元块。把四条偶记录记为 $e_A,e_B,e_C,e_D$，并按第一位翻转的对应次序记四条奇记录为 $o_A,o_B,o_C,o_D$。直接乘 $Z^{r_1}JZ^{r_2}JZ^{r_3}J$ 所得八个整数向量为
$$
\begin{array}{c|c|rrrr}
\text{标记}&r&a&b&c&d\\\hline
e_A&000&3&2&2&1\\
e_B&101&1&2&0&-1\\
e_C&110&1&0&-2&-1\\
e_D&011&-1&0&0&1\\\hline
o_A&100&3&2&-2&-1\\
o_B&001&1&2&0&1\\
o_C&010&1&0&2&1\\
o_D&111&-1&0&0&-1
\end{array}.
$$
置 $E=\{e_A,e_B,e_C,e_D\}$、$O=\{o_A,o_B,o_C,o_D\}$。全部四元子集按所含偶记录数分成
$$
\binom84=70
=\underbrace{\binom42\binom42}_{36}
+\underbrace{2}_{E,O}
+\underbrace{\binom43\binom41}_{16}
+\underbrace{\binom41\binom43}_{16}.
$$
其中 $36$ 个平衡块已经由 $R(S)=P(S)\ge0$ 处理，无需其主子式严格为正。第一位翻转交换 $E,O$，并交换最后两类。故剩余只需处理 $E$ 及全部十六个
$$
S_{ij}=(E\setminus\{e_i\})\cup\{o_j\},\qquad i,j\in\{A,B,C,D\}.
$$
令 $M_E=R(E)/2$、$M_{ij}=R(S_{ij})/2$。公共矩阵项已由 $R(\{r\})$ 给出，具体说，对这些四元块 $S$，
$$
M_S=\frac12\sum_{r\in S}
\begin{pmatrix}
ta_r^2&a_rb_r&ta_rc_r&b_rc_r\\
a_rb_r&b_r^2&a_rd_r&b_rd_r\\
ta_rc_r&a_rd_r&tc_r^2&c_rd_r\\
b_rc_r&b_rd_r&c_rd_r&d_r^2
\end{pmatrix},\qquad
M_E=\begin{pmatrix}
6t&4&2t&2\\
4&4&0&0\\
2t&0&4t&2\\
2&0&2&2
\end{pmatrix}.
$$
下列十七行逐一标明矩阵，并列出其全部四个顺序主子式：
$$
\begin{array}{c|rrrr}
M&\Delta_1&\Delta_2&\Delta_3&\Delta_4\\\hline
M_E&6t&24t-16&16t+80&224-64t\\
M_{AA}&6t&24t-16&10t+32&4t+36\\
M_{AB}&2t&8t-4&6t+12&4t+28\\
M_{AC}&2t&4t-1&10t+16&4t+28\\
M_{AD}&2t&4t-1&4t+6&3t+10\\
M_{BA}&10t&40t-36&22t+236&796-316t\\
M_{BB}&6t&24t-16&26t+80&116-28t\\
M_{BC}&6t&12t-9&12t+54&130-45t\\
M_{BD}&6t&12t-9&10t+40&76-8t\\
M_{CA}&10t&60t-49&34t+240&636-172t\\
M_{CB}&6t&36t-25&18-8t&42-21t\\
M_{CC}&6t&24t-16&32-6t&100-44t\\
M_{CD}&6t&24t-16&12-2t&28-12t\\
M_{DA}&10t&60t-49&64t+354&1090-453t\\
M_{DB}&6t&36t-25&34t+120&284-40t\\
M_{DC}&6t&24t-16&30t+108&316-108t\\
M_{DD}&6t&24t-16&26t+80&196-44t
\end{array}.
$$
为给出各行的统一展开式，写
$$
M=\begin{pmatrix}
tx&y&tp&h\\
y&z&k&u\\
tp&k&tv&w\\
h&u&w&2
\end{pmatrix},\qquad
A=xv-p^2,\qquad D=2z-u^2,
$$
$$
C=v(2y^2-2uyh+zh^2)+x(2k^2-2ukw+zw^2)
-2p\bigl(2yk-u(yw+hk)+zhw\bigr).
$$
这里各 $M$ 的右下角为 $2$，因为八个向量都满足 $d_r^2=1$。逐阶展开得到
$$
\begin{aligned}
\Delta_1&=tx,\\
\Delta_2&=txz-y^2,\\
\Delta_3&=t^2zA-t(xk^2+vy^2-2pyk),\\
\Delta_4&=t^2AD-tC+(yw-hk)^2.
\end{aligned}
$$
将八个向量按相应 $S$ 代入公共矩阵项，再用 $t^2=t+1$ 约化，即逐行得到上表。两组三元块及此十七行中的每个主子式都是一次式 $L(t)$；所列系数均满足 $L(1)\ge0$、$L(2)\ge0$ 且两者不同时为零。因此
$$
L(t)=(2-t)L(1)+(t-1)L(2)>0\qquad(1<t<2).
$$
例如 $42-21t=21(2-t)>0$，其在 $t=2$ 的零值不属于参数范围。故这十七个实对称矩阵全由 Sylvester 判据正定，翻转合同覆盖其余十七个非平衡块；加上 $36$ 个平衡块，全部 $70$ 个四元块都 PPT。

这里的实矩阵判据确实作用于所需的复 Hermitian 正性：对实对称 $A$ 与任意复向量 $x+iy$，有
$$
(x+iy)^*A(x+iy)=x^{\mathsf T}Ax+y^{\mathsf T}Ay.
$$
因而实二次型的非负性等价于复二次型的非负性，实正定也给出复正定。平衡块的正半定性则直接来自正外积之和。可分复密度的偏转置必正半定，因为正乘积项 $U\otimes V$ 变为 $U\otimes V^{\mathsf T}\ge0$，故前面的 NPT 均排除可分性。对所有已证 PPT 的块，$\theta_S$ 是完整 $\mathbb C^2\otimes\mathbb C^2$ 上的正迹一密度，可使用命题 141.1 已采用的二维 PPT 充分性，得到可分性。所用结果为 M. Horodecki、P. Horodecki、R. Horodecki，*Separability of Mixed States: Necessary and Sufficient Conditions*，[arXiv:quant-ph/9605038v2，定理 3，PDF 第 8 页](https://arxiv.org/pdf/quant-ph/9605038v2)，Physics Letters A 223，1–8（1996），[DOI:10.1016/S0375-9601(96)00706-2](https://doi.org/10.1016/S0375-9601(96)00706-2)。该文的闭包定义与此处有限凸和定义的一致性已由命题 141.1 的有限维紧性论证给出。因此上述三元块、平衡块与全部四元块得到的都是本命题所定义的可分性。

最后，把 $g=3$ 的四元块结论推广到较大记录集。若 $S\subseteq\{0,1\}^3$ 且 $n=|S|\ge4$，则未归一化算子有恒等式
$$
Q_S=\binom{n-1}{3}^{-1}
\sum_{\substack{A\subseteq S\\|A|=4}}Q_A.
$$
事实上，固定 $r\in S$ 后，包含 $r$ 的四元子集由其余 $n-1$ 条记录中任选三条唯一确定，恰有 $\binom{n-1}{3}$ 个。将右边每个 $Q_A$ 展开为原始 $Q_r$ 之和，每个 $Q_r$ 的系数因而恰为一。已证每个 $Q_A$ 属于有限正乘积和组成的可分正锥，该锥对有限求和与非负数乘法封闭，所以 $Q_S$ 也在该锥内。由 $q_S>0$，$\theta_S$ 可分。这一步使用已可分四元块的正组合；它不以向一个 PPT 算子添加任意原始正算子为封闭性依据。

每个八记录二分必有一块的基数至少为四，故至少一个报告可分。为明确穷尽范围，把含 $000$ 的块作为第一块，并要求其补非空，恰有 $2^7-1=127$ 个无标号非平凡二分；按较小块的基数计数为
$$
\begin{array}{c|rrrr}
\text{块大小}&1\mid7&2\mid6&3\mid5&4\mid4\\\hline
\text{二分数}&8&28&56&35
\end{array},\qquad 8+28+56+35=127.
$$
全部 $127$ 个二分都由上述至少四元块的结论排除两个报告同时纠缠，$4\mid4$ 的两块则均可分。同理，四记录的无标号二分共有 $2^3-1=7$ 个，前面列出的三个 $2\mid2$ 与四个 $1\mid3$ 已穷尽它们，得到恰一个成功、四个单侧纠缠、两个双侧可分的分类。$g=3$ 的全二分障碍即给陈述中的全有限长度存在断言的反例。证毕。

## 追加锚（本行以下为增补区）

## 144. 全端点预测的射影历史商与共同前后缀下的记录合并

**命题 144.1（两记忆列的标量射线判据与精确充分记录）。** 沿用命题 130.1、137.1 的纯边界过程，取
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
0<\alpha<1,\qquad \alpha^2+\alpha=1,\qquad B=M=\mathbb C^2,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle\otimes m_j\quad(j=0,1),
$$
$$
\Xi_0=m_0,\qquad
\Xi_{n+1}=(I_{B^{\otimes n}}\otimes T)\Xi_n.
$$
各空间取正交标准基。对任意有限整数 $g\ge0$，从这个纯初态恰好发出 $g+2$ 个输出，在全部生成之后测量内部位置；完整次序为
$$
B_L\otimes B_1\otimes\cdots\otimes B_g\otimes B_R\otimes M.
$$
$L,R$ 是第一个和最后一个已发出的 qubit，端点空间始终为完整的 $B_L\otimes B_R=\mathbb C^2\otimes\mathbb C^2$，左端点之前没有被忽略的前缀。最终记忆取偏迹且不可访问，生成途中不读取、测量或重置记忆。每个内部位置仅在事先固定的加减基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2}
\quad(b=0,1)
$$
中测量一次，全部结果成为原始经典记录 $r=(r_1,\ldots,r_g)\in\{0,1\}^g$。生成及内部测量没有反馈、端点操作或记录的相干重组。测后的内部系统与最终记忆均不可再访问；对已完成记录作确定性经典处理后，除所声明的保留标签外，不访问原始记录及其他副本。以下端点预测指这一制备完成后的实验，不要求重建旧的经典词或被测位置的仪器。

以 $\dagger$ 表示伴随，$\operatorname{outer}(x)=xx^\dagger$，并按左行右列约定
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L\otimes|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
记
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad
\kappa_g=s^{g+3}2^{-g/2},
$$
$$
N_r=Z^{r_1}J\cdots Z^{r_g}J,\qquad N_\varnothing=I_2,
\qquad C_r=\kappa_g JN_r.
$$
直接采用命题 137.1 的实际分支公式：
$$
\chi_r=\operatorname{vec}_{LR}(C_r)\otimes|0\rangle_M
+s\operatorname{vec}_{LR}(C_rE_0)\otimes|1\rangle_M,
$$
$$
Q_r=\operatorname{Tr}_M\operatorname{outer}(\chi_r)
=\operatorname{outer}(\operatorname{vec}_{LR}(C_r))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(C_rE_0)),
\qquad q_r=\operatorname{Tr}Q_r>0,\qquad \theta_r=Q_r/q_r.
$$
两个记忆列及其相对系数 $\alpha$ 都保留，$q_r$ 是该完整记录的实际 Born 概率，$\sum_rq_r=1$。对任意非零复二阶矩阵 $C$，也用同一代数式定义
$$
Q(C)=\operatorname{outer}(\operatorname{vec}_{LR}(C))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(CE_0)),\qquad
\operatorname{Tr}Q(C)=\|C\|_F^2+\alpha\|CE_0\|_F^2>0.
$$
称两个非零矩阵射影相同，是指它们相差一个非零复标量。对每个 $N_r$，选取 $N_r,-N_r$ 中按逐行次序遇到的第一个非零元素为正的那个，记为整数矩阵签名 $\sigma(r)$。

固定 $g$，定义完整记录的精确端点预测等价为
$$
r\sim_g v
\quad\Longleftrightarrow\quad
\operatorname{Tr}(E\theta_r)=\operatorname{Tr}(E\theta_v)
\quad\text{对每个 }E\in\mathcal L(B_L\otimes B_R),\ 0\le E\le I.
$$
这也就是每个有限端点 POVM 的全部结果分布相同。对确定性函数 $f:\{0,1\}^g\to\mathcal B$，仅考虑其有限像中的标签 $b$，定义实际事件及条件密度
$$
Q_b=\sum_{r:f(r)=b}Q_r,\qquad
q_b=\operatorname{Tr}Q_b=\sum_{r:f(r)=b}q_r>0,\qquad
\theta_b=Q_b/q_b.
$$
称 $f$ 逐记录精确充分，是指对每个端点效应 $E$，存在仅依赖保留标签的预测值 $\widehat p_E(b)\in[0,1]$，满足
$$
\widehat p_E(f(r))=\operatorname{Tr}(E\theta_r)
\qquad\text{对每条完整记录 }r.
$$
这一要求保留每条原始记录所条件化的概率，而不只是给出合并事件的平均概率。

则对任意非零 $C,D\in\mathbb C^{2\times2}$，包括奇异矩阵，均有标量射线判据
$$
\frac{Q(D)}{\operatorname{Tr}Q(D)}=\frac{Q(C)}{\operatorname{Tr}Q(C)}
\quad\Longleftrightarrow\quad
D=zC\quad\text{存在 }z\in\mathbb C\setminus\{0\}.
$$
因此，对每个固定 $g\ge0$ 及 $r,v\in\{0,1\}^g$，
$$
r\sim_g v
\quad\Longleftrightarrow\quad \theta_r=\theta_v
\quad\Longleftrightarrow\quad N_v=\pm N_r
\quad\Longleftrightarrow\quad \sigma(v)=\sigma(r).
$$
这些条件成立时还满足 $C_v=\pm C_r$、$Q_v=Q_r$、$q_v=q_r$。$f$ 逐记录精确充分当且仅当每个非空纤维中的 $\theta_r$ 全部相同；此时实际 Born 加权的 $\theta_b$ 就是该共同密度。签名 $\sigma$ 因而是此任务的最粗充分有限标签，在有效标签双射重命名的意义下唯一，其标签数恰为
$$
K_g=\bigl|\{\sigma(r):r\in\{0,1\}^g\}\bigr|,
$$
即不同射影整数矩阵的个数。两个相同端点密度也保持对同一后续端点 CPTP 操作及测量的预测相同，所用协议只能访问端点和已保留标签。

进一步有
$$
(ZJ)^3=-I_2,\qquad N_{0111}=N_{1110}=-J.
$$
固定长度 $g=0,1,2,3$ 时没有不同记录的射影碰撞，首次碰撞发生于 $g=4$。任意有限二进制词 $u,r,v$ 满足
$$
N_{urv}=N_uN_rN_v.
$$
故中间词的射影相同在任意共同前缀 $u$ 与共同后缀 $v$ 下保持。特别地，若中间词 $r,w$ 等长且 $N_w=\pm N_r$，则在内部长度同为 $G=|u|+|r|+|v|$ 的两个完整协议中，
$$
Q_{uwv}=Q_{urv},\qquad q_{uwv}=q_{urv},\qquad
\theta_{uwv}=\theta_{urv}.
$$
因此每个 $g\ge4$ 都有不同完整记录可无损合并，$K_g<2^g$。这里的上下文是完整协议内的共同测量标签词；结论没有给出仅作用于已保留端点态的逐步闭合动力学，也不授予访问已丢弃记忆或内部系统的能力。

证明。加减基在命题 137.1 中给 $D_k=2^{-1/2}Z^{r_k}$，代入该命题即得所列 $C_r$、$\chi_r$ 及 $Q_r$。由 $\det J=\det Z=-1$，
$$
N_r\in\operatorname{GL}_2(\mathbb Z),\qquad
\det N_r=(-1)^{g+\sum_k r_k},\qquad \kappa_g>0.
$$
所以所有 $C_r$ 非零且可逆，命题 137.1 的迹公式给 $q_r>0$，完整测量的完备性给 $\sum_rq_r=1$，包括 $g=0$ 的空记录。这里没有把第二记忆列并入第一列或各自重新归一化。

先证一般的标量射线判据。令 $P=I_{B_L}\otimes E_0$，则 $P=P^\dagger=P^2$，且
$$
P\operatorname{vec}_{LR}(C)=\operatorname{vec}_{LR}(CE_0).
$$
在全部四阶复矩阵的线性空间上定义
$$
\mathcal L(X)=X+\alpha PXP,\qquad
\mathcal R(Y)=Y-\frac{\alpha}{1+\alpha}PYP.
$$
利用 $P^2=P$ 展开两种复合，均有
$$
\begin{aligned}
\mathcal R(\mathcal L(X))
&=X+\left(\alpha-\frac{\alpha}{1+\alpha}
-\frac{\alpha^2}{1+\alpha}\right)PXP=X,\\
\mathcal L(\mathcal R(Y))
&=Y+\left(\alpha-\frac{\alpha}{1+\alpha}
-\frac{\alpha^2}{1+\alpha}\right)PYP=Y.
\end{aligned}
$$
故 $\mathcal L$ 代数可逆，$\mathcal L^{-1}=\mathcal R$。置 $c=\operatorname{vec}_{LR}(C)$、$d=\operatorname{vec}_{LR}(D)$，便有 $Q(C)=\mathcal L(cc^\dagger)$、$Q(D)=\mathcal L(dd^\dagger)$。若两个归一化密度相同，取正数
$$
\lambda=\frac{\operatorname{Tr}Q(D)}{\operatorname{Tr}Q(C)}>0,
$$
则 $Q(D)=\lambda Q(C)$。施加线性的 $\mathcal R$ 得 $dd^\dagger=\lambda cc^\dagger$。对任意非零向量 $h$，$hh^\dagger$ 的像恰为 $\mathbb C h$：它的每个像向量是 $h$ 的倍数，而 $hh^\dagger h=\|h\|^2h\ne0$。于是 $d=zc$，其中 $z\ne0$，再比较外积得 $|z|^2=\lambda$。向量化单射，故 $D=zC$。反之，$D=zC$ 直接给 $Q(D)=|z|^2Q(C)$ 及相同的归一化密度。证明只用 $c,d$ 非零，没有要求 $C,D$ 可逆。

这个逆仅用于代数比较。事实上，取标准基 $e_0=|00\rangle$、$e_1=|01\rangle$ 及正迹一算子
$$
Y=\operatorname{outer}\left(\frac{e_0+e_1}{\sqrt2}\right).
$$
由于 $Pe_0=e_0$、$Pe_1=0$，$\mathcal R(Y)$ 在这两个坐标上的主子矩阵及其行列式为
$$
\frac12\begin{pmatrix}(1+\alpha)^{-1}&1\\1&1\end{pmatrix},\qquad
-\frac{\alpha}{4(1+\alpha)}<0,
\qquad \operatorname{Tr}\mathcal R(Y)=1-\frac{\alpha}{2(1+\alpha)}\ne1.
$$
因此 $\mathcal R$ 不是正映射，也不是完全正或保迹映射，不能作为任意输入态的物理恢复通道。

对固定长度的两条记录，刚证的判据及 $J$ 可逆、$\kappa_g>0$ 给
$$
\theta_v=\theta_r\quad\Longleftrightarrow\quad
N_v=zN_r\quad(z\ne0).
$$
$N_r$ 至少有一个非零实元素，比较该处元素说明 $z$ 为实数。再取行列式，
$$
z^2=\frac{\det N_v}{\det N_r}\in\{1,-1\}.
$$
实非零 $z$ 的平方为正，故 $z^2=1$、$z=\pm1$。反向蕴含直接成立。两个 $C$ 的尺度 $\kappa_g$ 相同，所以连未归一化 $Q$ 及其迹也相同。选首个非零元素为正恰好消去这个符号歧义，得到签名等价式。

现在识别预测任务。密度相同显然给所有效应的 Born 概率相同。若 $\Delta=\theta_r-\theta_v$ 为非零 Hermitian 矩阵，则 $\operatorname{Tr}\Delta=0$。其非零实特征值不可能全同号，所以至少有一个正特征值。令 $E_+$ 为全部正特征空间的正交投影，就有
$$
0\le E_+\le I,\qquad
\operatorname{Tr}(E_+\theta_r)-\operatorname{Tr}(E_+\theta_v)
=\operatorname{Tr}(E_+\Delta)
=\sum_{\lambda_j(\Delta)>0}\lambda_j(\Delta)>0.
$$
这给出区分效应，故所有效应相同当且仅当密度相同。每个效应属于二结果 POVM $(E,I-E)$，每个有限 POVM 又由效应组成，因而两种预测表述等价。

为逐字适用定理 54.3 的有限实验族，取 $X=\{0,1\}^g$、实验长度上限 $H=1$，在端点的四个标准基向量 $e_0,e_1,e_2,e_3$ 上选取下列 $16$ 个秩一投影作为二元测量的第一个效应：
$$
\begin{gathered}
F_j=\operatorname{outer}(e_j)\quad(0\le j\le3),\\
F_{jk}^{+}=\operatorname{outer}\left(\frac{e_j+e_k}{\sqrt2}\right),\qquad
F_{jk}^{i}=\operatorname{outer}\left(\frac{e_j+i e_k}{\sqrt2}\right)
\quad(0\le j<k\le3).
\end{gathered}
$$
每个协议是 $(F,I-F)$，共 $4+2\binom42=16$ 个协议。若 $\theta_{jk}=\langle e_j|\theta|e_k\rangle$，则其第一个结果概率满足
$$
\begin{aligned}
p_j&=\theta_{jj},\\
p_{jk}^{+}&=\frac{\theta_{jj}+\theta_{kk}}2+\operatorname{Re}\theta_{jk},\\
p_{jk}^{i}&=\frac{\theta_{jj}+\theta_{kk}}2-\operatorname{Im}\theta_{jk}.
\end{aligned}
$$
所以这 $16$ 个数确定全部对角元和全部非对角元的实、虚部，下三角由 Hermitian 性确定。该有限菜单的响应签名相同恰等价于密度相同，因而恰等价于全部端点效应的预测相同。这里的信息完备性是这些显式公式的结论；信息完备测量的一般术语参见 G. M. D'Ariano、P. Perinotti、M. F. Sacchi，*Informationally Complete Measurements and Group Representation*，Journal of Optics B: Quantum and Semiclassical Optics 6，S487–S491（2004），[DOI:10.1088/1464-4266/6/6/005](https://doi.org/10.1088/1464-4266/6/6/005)。菜单收集各个二元实验的分布，不要求不同实验存在联合结果分布。

定理 54.3 现在直接适用于这个有限菜单：$f$ 充分当且仅当其纤维不跨越响应签名类，而这里的类已被识别为 $\theta_r$ 相同的类，亦即 $\sigma(r)$ 相同的类。对实际事件，经典结果合并的线性性给 $Q_b=\sum_{f(r)=b}Q_r$，且没有不同 $r$ 的振幅交叉项；因此
$$
\theta_b=\sum_{r:f(r)=b}\frac{q_r}{q_b}\theta_r,\qquad
\sum_{r:f(r)=b}\frac{q_r}{q_b}=1.
$$
若纤维中的密度共同等于 $\theta$，这个实际 Born 加权和就等于 $\theta$，取 $\widehat p_E(b)=\operatorname{Tr}(E\theta_b)$ 即满足每条记录的要求。若同一纤维包含不同密度，刚才的区分效应给出两个不同概率，一个共同预测值不可能同时等于它们。合并后的平均概率仍存在，但不满足逐记录要求。故由定理 54.3 的最小性结论，任意充分标签都必须细化 $\sigma$ 的纤维，$\sigma$ 本身充分且恰有 $K_g$ 个有效值；达到这个数的充分标签恰与 $\sigma$ 双射重命名。这没有以纤维大小代替其 Born 权重。

若 $\theta_r=\theta_v$，对同一个端点 CPTP 映射 $\Phi$ 及其输出上的任意效应 $F$，有
$$
\operatorname{Tr}(F\Phi(\theta_r))=\operatorname{Tr}(F\Phi(\theta_v)).
$$
有限次端点操作与测量也逐分支保持这个结论：每条指定结果路径的未归一化算子由同一串线性测量分支映射和通道得到，相同输入给相同算子及其迹。协议若根据先前端点结果或共同保留标签选取后续操作，逐路径仍用同一个映射。此论证的输入只是所保留的端点密度与标签，不包括已丢弃记录、被测内部系统或最终记忆。

为了明确严格于只保留纠缠这一性质，取 $g=2$ 的记录 $00$ 与 $11$。由上面的矩阵乘积，亦即命题 140.1（C）的同一分支，
$$
\kappa_2^{-1}C_{00}=\begin{pmatrix}3&2\\2&1\end{pmatrix},\qquad
\kappa_2^{-1}C_{11}=\begin{pmatrix}-1&0\\0&1\end{pmatrix}.
$$
两条记忆列的迹分别给 $q_{00}=\kappa_2^2(18+13\alpha)$、$q_{11}=\kappa_2^2(2+\alpha)$。效应 $E=|01\rangle\langle01|$ 因而满足
$$
\operatorname{Tr}(E\theta_{00})=\frac4{18+13\alpha}>0,
\qquad \operatorname{Tr}(E\theta_{11})=0.
$$
两条分支均由命题 137.1 纠缠，却能由端点实验区分。命题 140.1（C）已经证明合并为奇偶报告仍保留条件纠缠，但这两个同为偶记录的概率不同，所以该报告不满足此处的精确预测充分性。

最后处理词关系。直接相乘得
$$
ZJ=\begin{pmatrix}1&1\\-1&0\end{pmatrix},\qquad
(ZJ)^2=\begin{pmatrix}0&1\\-1&-1\end{pmatrix},\qquad
(ZJ)^3=\begin{pmatrix}-1&0\\0&-1\end{pmatrix}=-I_2.
$$
于是
$$
N_{0111}=J(ZJ)^3=-J=(ZJ)^3J=N_{1110}.
$$
对较短长度，把 $N_r$ 的四个元素按逐行次序记为 $(a,b,c,d)$。从空词的 $I_2$ 出发，附加一位的整数乘法为
$$
N_{r0}=\begin{pmatrix}a+b&a\\c+d&c\end{pmatrix},\qquad
N_{r1}=\begin{pmatrix}a-b&a\\c-d&c\end{pmatrix}.
$$
这给出长度不超过三的全部值：
$$
\begin{array}{c|c|rrrr}
g&r&a&b&c&d\\\hline
0&\varnothing&1&0&0&1\\\hline
1&0&1&1&1&0\\
1&1&1&1&-1&0\\\hline
2&00&2&1&1&1\\
2&01&0&1&1&1\\
2&10&2&1&-1&-1\\
2&11&0&1&-1&-1\\\hline
3&000&3&2&2&1\\
3&001&1&2&0&1\\
3&010&1&0&2&1\\
3&011&-1&0&0&1\\
3&100&3&2&-2&-1\\
3&101&1&2&0&-1\\
3&110&1&0&-2&-1\\
3&111&-1&0&0&-1
\end{array}.
$$
各长度的 $2^g$ 条记录均已列出；在每个固定长度内，选首个非零元素为正后，四元组两两不同。因此 $g\le3$ 没有射影碰撞，而所列两条长度四的不同记录给出首次碰撞。

按定义连接有限乘积，结合律立即给 $N_{urv}=N_uN_rN_v$，空词情形也成立。若 $N_w=zN_r$，则
$$
N_{uwv}=N_u(zN_r)N_v=zN_{urv}.
$$
故射影关系在任意共同上下文中保持。若 $|r|=|w|$，前面已证 $z=\pm1$，两条完整记录的内部长度同为 $G$，于是
$$
C_{uwv}=\kappa_G JN_{uwv}=\pm\kappa_G JN_{urv}=\pm C_{urv}.
$$
分别对两记忆列取外积，符号同时消去，便得到相同的实际 $Q$、$q$ 及 $\theta$。这些式子比较的是从 $m_0$ 开始、各自恰好发出 $G+2$ 位的完整协议；共同前缀是其中已测内部位置的标签，并非左端点之前被忽略的输出，共同后缀也不是作用于旧右端点的通道。因而该乘法恒等式不提供在擦除最终记忆后继续生成的状态更新律。

对每个 $g\ge4$，在 $0111$ 与 $1110$ 前面同加 $0^{g-4}$，就得到两条不同的长度 $g$ 记录及相同的实际条件端点密度，故 $K_g<2^g$。所证的是该关系及其所有共同上下文中的保持性；没有断言这一条改写生成全部词关系，也没有由它确定一般正规形或 $K_g$ 的增长律。证毕。

## 追加锚（本行以下为增补区）
## 145. 丢弃相关记忆后的逐结果延长与非选择物理闭合

**命题 145.1（未知左滤波制备族的唯一代数延长、仪器障碍与非选择通道）。** 取命题 130.1、137.1 的纯边界生成器，在各个二维空间的正交标准基中令
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad 0<\alpha<1,
$$
$$
m_0=s|0\rangle+\alpha|1\rangle,\qquad m_1=|0\rangle,\qquad
T|j\rangle=|j\rangle_{\rm out}\otimes m_j\quad(j=0,1).
$$
从纯记忆 $m_0$ 恰好发出两个输出 $L,R$，记
$$
\Xi_2=(I_L\otimes T)Tm_0\in B_L\otimes B_R\otimes M,
\qquad B_L=B_R=M=\mathbb C^2.
$$
本命题另行允许如下制备族：对任意复二阶矩阵 $F$，只要 $F^\dagger F\le I_2$，就在 $L$ 上施加单 Kraus 成功分支 $F$，保留未归一化联合向量
$$
\chi_F=(F\otimes I_R\otimes I_M)\Xi_2.
$$
成功旗标相同，滤波设置 $F$ 不作为后续仪器的可用标签。这里允许全部这样的复收缩，包括奇异矩阵与零矩阵；这是新增的制备假设，并非命题 138.1、139.1 的内部测量策略所已允许的端点操作。

以 $\dagger$ 表示伴随，$\mathsf T$ 表示普通转置，沿用命题 137.1 的左行右列约定
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
定义
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=|0\rangle\langle0|,
\qquad C_0=s^3J,\qquad C=FC_0,
$$
$$
Q(C)=|\operatorname{vec}_{LR}(C)\rangle\langle\operatorname{vec}_{LR}(C)|
+\alpha|\operatorname{vec}_{LR}(CE_0)\rangle
\langle\operatorname{vec}_{LR}(CE_0)|.
$$
此式对包括零在内的全部复矩阵 $C$ 定义。实际端点输入是 $\operatorname{Tr}_M|\chi_F\rangle\langle\chi_F|$；一旦取偏迹，端点仪器不得访问该记忆或其副本。

比较协议则保留同一个 $\chi_F$ 中的原始相关记忆，对它施加 $T$ 再发出一个输出 $R'$，在旧 $R$ 上测量固定正交基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},
\qquad b\in\{0,1\},\qquad A_b=Z^bJ,
$$
保留结果 $b$、$L,R'$，对最终记忆 $M'$ 取偏迹。其未归一化向量和端点算子定义为
$$
\chi_{F,b}=(I_L\otimes\langle\eta_b|_R\otimes I_{R'}\otimes I_{M'})
(I_{LR}\otimes T)\chi_F,
\qquad Q_{F,b}=\operatorname{Tr}_{M'}|\chi_{F,b}\rangle\langle\chi_{F,b}|.
$$
$F$ 始终只作用于 $L$。将输入 $L,R$ 与输出 $L,R'$ 按标准基识别为 $\mathbb C^4$。端点二结果量子仪器在这里指一对定义于全部 $M_4(\mathbb C)$ 的复线性完全正映射 $\mathcal I_0,\mathcal I_1$，其和保迹；两映射固定而不依赖 $F$。

则实际制备及比较分支满足
$$
\chi_F=\operatorname{vec}_{LR}(C)\otimes|0\rangle_M
+s\operatorname{vec}_{LR}(CE_0)\otimes|1\rangle_M,
\qquad \operatorname{Tr}_M|\chi_F\rangle\langle\chi_F|=Q(C),
$$
$$
C_b=\frac{s}{\sqrt2}CA_b,\qquad
\chi_{F,b}=\operatorname{vec}_{LR'}(C_b)\otimes|0\rangle_{M'}
+s\operatorname{vec}_{LR'}(C_bE_0)\otimes|1\rangle_{M'},
\qquad Q_{F,b}=\frac{\alpha}{2}Q(CA_b).
$$
两记忆列及其相对系数 $\alpha$ 均不可省略。设
$$
q_F=\operatorname{Tr}Q(C)=\|C\|_F^2+\alpha\|CE_0\|_F^2,\qquad
q_{F,b}=\operatorname{Tr}Q_{F,b}
=\frac{\alpha}{2}\bigl(\|CA_b\|_F^2+\alpha\|CA_bE_0\|_F^2\bigr).
$$
这里 $q_F\in[0,1]$ 是滤波成功概率，$q_{F,b}$ 是成功且报告 $b$ 的联合概率，$q_{F,0}+q_{F,1}=q_F$。若 $F\ne0$，则 $q_F,q_{F,0},q_{F,1}>0$，报告条件概率为 $q_{F,b}/q_F$，报告后的密度为 $Q_{F,b}/q_{F,b}$。若 $F=0$，全部算子和概率均为零，不定义条件密度。

不存在上述端点仪器使
$$
\mathcal I_b(Q(FC_0))=Q_{F,b}
\quad\text{对每个 }F\in M_2(\mathbb C),\ F^\dagger F\le I_2,
\quad b=0,1
$$
同时成立。不过，去掉完全正性要求后，每个分支有唯一的复线性延拓。令
$$
P=I_L\otimes E_0,\qquad
\mathcal L(X)=X+\alpha PXP,\qquad
\mathcal L^{-1}(Y)=Y-\frac{\alpha}{1+\alpha}PYP,
\qquad \operatorname{Ad}_B(X)=BXB^\dagger,
$$
则该延拓为
$$
\widehat{\mathcal I}_b
=\frac{\alpha}{2}\mathcal L\circ
\operatorname{Ad}_{I_L\otimes A_b^{\mathsf T}}\circ\mathcal L^{-1}
=\operatorname{Id}_L\otimes\phi_b.
$$
其中对任意彼此独立的复数 $x,y,z,w$，令 $e=(-1)^b$，有
$$
\phi_b\!\begin{pmatrix}x&y\\z&w\end{pmatrix}
=\frac12\begin{pmatrix}
\alpha x+e(y+z)+w&\alpha^2x+e\alpha z\\
\alpha^2x+e\alpha y&\alpha^2x
\end{pmatrix},
\qquad
\operatorname{Tr}\phi_b(X)=\operatorname{Tr}(|\eta_b\rangle\langle\eta_b|X).
$$
所以只要求下一报告的概率时，端点测量 $I_L\otimes|\eta_b\rangle\langle\eta_b|$ 已能实现它；障碍在于同时保留正确报告及其条件输出。

另一方面，忘掉报告后的唯一延拓是完全正保迹通道
$$
\widehat{\mathcal I}_0+\widehat{\mathcal I}_1
=\operatorname{Id}_L\otimes\mathcal T,\qquad
\mathcal T(X)=X_{00}\tau_0+X_{11}E_0,
\qquad
\tau_0=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}.
$$
它在右端点测量计算基，随后分别制备 $\tau_0$ 或 $E_0$，消除 $L:R'$ 间的纠缠。它的有效 Kraus 分解不实现上面指定的两个逐结果分支。

证明。由 $\|m_0\|^2=\alpha+\alpha^2=1$、$\|m_1\|^2=1$ 及输出标准基的正交性，$T^\dagger T=I_2$。直接应用两次等距得
$$
Tm_0=s|0\rangle m_0+\alpha|1\rangle m_1,
\qquad
\Xi_2=\alpha|00\rangle m_0+s\alpha|01\rangle m_1
+\alpha|10\rangle m_0.
$$
在正交记忆基上展开，利用 $s\alpha=s^3$、$\alpha^2=s^4$，得到
$$
\Xi_2=s^3(|00\rangle+|01\rangle+|10\rangle)|0\rangle_M
+s^4(|00\rangle+|10\rangle)|1\rangle_M
=\operatorname{vec}_{LR}(C_0)|0\rangle_M
+s\operatorname{vec}_{LR}(C_0E_0)|1\rangle_M.
$$
对任意复矩阵 $F,C_0$，逐坐标有
$$
(F\otimes I_R)\operatorname{vec}_{LR}(C_0)=\operatorname{vec}_{LR}(FC_0).
$$
这给出 $\chi_F$ 的两列；对 $M$ 取偏迹时只消去正交记忆列之间的交叉项，第二列的外积系数是 $s^2=\alpha$，从而得到实际的 $Q(FC_0)$。这一步没有先把任意 $C$ 的代数定义当成物理制备。$F^\dagger F\le I_2$ 保证 $F$ 与 $\sqrt{I_2-F^\dagger F}$ 可组成完整制备操作，且
$$
q_F=\|\chi_F\|^2
=\langle\Xi_2|(F^\dagger F\otimes I_R\otimes I_M)|\Xi_2\rangle\le1.
$$

为推导比较分支，把 $C$ 的两列记为 $u,v\in\mathbb C^2$，故
$$
\chi_F=(u|0\rangle_R+v|1\rangle_R)|0\rangle_M
+s u|0\rangle_R|1\rangle_M.
$$
这里 $u,v$ 属于 $L$，其系数可以为任意复数。对原始记忆应用 $T$，再用 $\langle\eta_b|$ 收缩旧 $R$，逐项得到
$$
\chi_{F,b}
=\frac{s}{\sqrt2}\bigl((u+ev)|0\rangle_{R'}+u|1\rangle_{R'}\bigr)|0\rangle_{M'}
+\frac{\alpha}{\sqrt2}(u+ev)|0\rangle_{R'}|1\rangle_{M'}.
$$
由于
$$
A_b=\begin{pmatrix}1&1\\e&0\end{pmatrix},\qquad
CA_b=(u+ev,\ u),\qquad s^2=\alpha,
$$
这恰是所列 $C_b$ 的两记忆列。$\eta_b$ 的分量为实数，bra 系数为 $1/\sqrt2,e/\sqrt2$；它不对 $u,v$ 取共轭。取最终记忆偏迹，外积才带复共轭，且两个分支都保留同一个因子 $s^2/2=\alpha/2$。$L$ 上的 $F$ 与这次发出和旧 $R$ 测量作用于不同张量因子，故也可在这些操作之后施加同一个 $F$。全过程没有更换或重置原始记忆。

迹等于两列范数平方之和，给出全部概率式。比较协议中的等距保范数，两个 $\eta_b$ 完备，所以 $\sum_bq_{F,b}=\|\chi_F\|^2=q_F$。$C_0$ 与两个 $A_b$ 都可逆，因而 $F\ne0$ 时 $C\ne0$、$CA_b\ne0$，每个范数和严格为正。$F=0$ 时全部向量为零。这证明了包括奇异与零滤波在内的实际分支和归一化边界。

现在才讨论端点线性延拓。$P^2=P$，展开两种复合时 $PXP$ 的额外系数均为
$$
\alpha-\frac{\alpha}{1+\alpha}-\frac{\alpha^2}{1+\alpha}=0,
$$
故所列 $\mathcal L^{-1}$ 确为代数逆。又有
$$
P\operatorname{vec}_{LR}(C)=\operatorname{vec}_{LR}(CE_0),\qquad
\mathcal L(|\operatorname{vec}_{LR}(C)\rangle\langle\operatorname{vec}_{LR}(C)|)=Q(C).
$$
$\det C_0=-s^6\ne0$。对任意 $D\in M_2(\mathbb C)$，取实数
$$
t=\max\{1,\|DC_0^{-1}\|_{\rm op}\}>0,\qquad
F=t^{-1}DC_0^{-1}.
$$
则 $F^\dagger F\le I_2$ 且 $D=tFC_0$。两个实际分支的公式都是二次齐次的：
$$
Q(tFC_0)=t^2Q(FC_0),\qquad
Q(tFC_0A_b)=t^2Q(FC_0A_b).
$$
因此，一个线性映射若在全部允许的收缩 $F$ 上满足要求，就在全部 $D$ 上被迫满足
$$
\mathcal I_b(Q(D))=\frac{\alpha}{2}Q(DA_b).
$$
$D=0$ 对应 $F=0$，两边都为零，不需除以概率。

为说明这一约束确定全部算子，令 $h_0,\ldots,h_3$ 为 $\mathbb C^4$ 标准基，$E_{jk}=|h_j\rangle\langle h_k|$。取下列 $16$ 个未归一化秩一外积：
$$
D_j=|h_j\rangle\langle h_j|\quad(0\le j\le3),\qquad
D_{jk}^{+}=|h_j+h_k\rangle\langle h_j+h_k|,\qquad
D_{jk}^{i}=|h_j+i h_k\rangle\langle h_j+i h_k|
\quad(0\le j<k\le3).
$$
它们给出
$$
D_{jk}^{+}-D_j-D_k=E_{jk}+E_{kj},\qquad
D_{jk}^{i}-D_j-D_k=-iE_{jk}+iE_{kj}.
$$
右边连同四个对角矩阵构成 Hermitian 矩阵空间的实基，所以这 $4+2\binom42=16$ 个外积在实数上张成全部 Hermitian 矩阵。每个向量都可唯一写成某个复二阶矩阵的 $\operatorname{vec}_{LR}$；上一段的正数缩放把它对应的 $Q$ 化为允许的实际输入的正倍数。可逆且保持 Hermitian 性的 $\mathcal L$ 因而把它们送到另一组实张成族。最后每个复矩阵 $X$ 都有分解
$$
X=\frac{X+X^\dagger}{2}
+i\frac{X-X^\dagger}{2i},
$$
两项中的矩阵均为 Hermitian，故复线性性确定全部 $M_4(\mathbb C)$ 上的值。这里用到的是全部未知复左收缩产生的张成族，而不是任意固定有限原始记录集的张成性。

逐坐标的向量化恒等式为
$$
\operatorname{vec}_{LR'}(DA_b)
=(I_L\otimes A_b^{\mathsf T})\operatorname{vec}_{LR}(D).
$$
因此 $\widehat{\mathcal I}_b$ 的所列复合确实把 $Q(D)$ 送到 $\alpha Q(DA_b)/2$，由刚证的唯一性，任何候选仪器都必须等于它。普通转置来自右乘的指标次序；伴随只出现在 $\operatorname{Ad}$ 中。特别地，$A_b$ 是实矩阵，但 $F,D$ 无须为实。

写 $\mathcal L=\operatorname{Id}_L\otimes\lambda$，其中 $\lambda(X)=X+\alpha E_0XE_0$。由 $(1+\alpha)^{-1}=\alpha$，对独立复矩阵元有
$$
\lambda^{-1}\!\begin{pmatrix}x&y\\z&w\end{pmatrix}
=\begin{pmatrix}\alpha x&y\\z&w\end{pmatrix},\qquad
A_b^{\mathsf T}=\begin{pmatrix}1&e\\1&0\end{pmatrix}.
$$
两侧相乘，再施加 $\alpha\lambda/2$，就得到陈述中的 $\phi_b$，这里没有施加 $z=\overline y$ 的限制。利用 $\alpha+\alpha^2=1$ 取迹得
$$
\operatorname{Tr}\phi_b(X)=\frac{x+w+e(y+z)}2
=\operatorname{Tr}(|\eta_b\rangle\langle\eta_b|X).
$$
在左端点各矩阵块上应用此式，得到对全部 $Y\in M_4(\mathbb C)$ 的迹恒等式
$$
\operatorname{Tr}\widehat{\mathcal I}_b(Y)
=\operatorname{Tr}\bigl((I_L\otimes|\eta_b\rangle\langle\eta_b|)Y\bigr).
$$
两效应为正且和为恒等，因此实际 $Q(C)$ 上的报告概率确有端点测量实现。

然而取合法端点密度
$$
Y=|0\rangle_L\langle0|\otimes|+\rangle_R\langle+|,
\qquad |+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2}.
$$
在 $L=0$ 的右端点块上将 $x=y=z=w=1/2$、$b=1$ 代入，利用 $1-\alpha=\alpha^2$ 及 $\alpha-\alpha^2=\alpha^3$，得到
$$
\widehat{\mathcal I}_1(Y)
=|0\rangle_L\langle0|\otimes
\frac{\alpha^2}{4}\begin{pmatrix}-1&-\alpha\\-\alpha&1\end{pmatrix},
\qquad
\langle00|\widehat{\mathcal I}_1(Y)|00\rangle=-\frac{\alpha^2}{4}<0.
$$
因此这个唯一延拓连正映射都不是，更不可能完全正，所要求的端点仪器不存在。

这个 $Y$ 不在实际制备域内，甚至不在该域所生成的正锥内。事实上，$\mathcal L^{-1}(Y)$ 在同一块上为
$$
\frac12\begin{pmatrix}\alpha&1\\1&1\end{pmatrix},\qquad
\det\left(\frac12\begin{pmatrix}\alpha&1\\1&1\end{pmatrix}\right)
=\frac{\alpha-1}{4}=-\frac{\alpha^2}{4}<0.
$$
若 $Y=\sum_k t_kQ(F_kC_0)$ 且 $t_k\ge0$，施加 $\mathcal L^{-1}$ 后右边是非负系数的秩一外积和，必为正半定，与此行列式矛盾；归一化兼容密度的有限正混合亦归入同一正锥。收敛的正混合或概率积分也不能给出 $Y$，因为施加连续线性映射 $\mathcal L^{-1}$ 后，每个向量上的二次型仍是非负数的极限或积分。该计算同时说明代数逆 $\mathcal L^{-1}$ 不是正的物理恢复映射。虽然 $Y$ 不是某个 $F$ 产生的输入，定义在全部端点算子上的量子仪器必须在它上面保持正性；制备族已把该仪器的线性取值唯一固定，所以这个域外密度是有效的否定依据。对每个实际制备，$Q_{F,b}$ 始终是两个正外积之和，没有物理联合过程把实际合法制备送成负算子。

最后相加两个分支公式，含 $e$ 的项消去，得到
$$
(\phi_0+\phi_1)(X)
=\begin{pmatrix}\alpha x+w&\alpha^2x\\\alpha^2x&\alpha^2x\end{pmatrix}
=x\tau_0+wE_0.
$$
为明确在全部算子上的等式，令 $e_{ij}=|i\rangle\langle j|$ 为右端点四个矩阵单位。刚才的相加及以下 Kraus 和在这四个输入上的像分别均为
$$
e_{00}\longmapsto\tau_0,\qquad e_{11}\longmapsto E_0,\qquad
 e_{01}\longmapsto0,\qquad e_{10}\longmapsto0.
$$
左因子保持不变，所以对 $|i\rangle_L\langle k|\otimes e_{jl}$ 的全部 $16$ 个矩阵单位等式成立，进而对每个复四阶矩阵成立。具体地，取
$$
K_0=\alpha(|0\rangle+|1\rangle)\langle0|,\qquad
K_1=s^3|0\rangle\langle0|,\qquad K_2=|0\rangle\langle1|.
$$
直接乘法给
$$
\sum_{j=0}^2 K_jXK_j^\dagger
=X_{00}\bigl(\alpha^2(|0\rangle+|1\rangle)(\langle0|+\langle1|)
+\alpha^3E_0\bigr)+X_{11}E_0=\mathcal T(X),
$$
因为 $\alpha^2+\alpha^3=\alpha$。而
$$
\tau_0=2\alpha^2|+\rangle\langle+|+\alpha^3E_0,
\qquad 2\alpha^2+\alpha^3=1,
\qquad \operatorname{Tr}\tau_0=1,\qquad \det\tau_0=\alpha^5>0,
$$
$$
\sum_{j=0}^2K_j^\dagger K_j
=(2\alpha^2+\alpha^3)E_0+|1\rangle\langle1|=I_2.
$$
Kraus 和在任意附加恒等因子后仍把正算子送到正算子，故完全正；最后一个等式给出保迹性。端点 Kraus 算子恰为 $I_L\otimes K_j$。对任意密度 $\rho_{LR}$，记其两个右对角块为
$$
\rho_L^{jj}=(I_L\otimes\langle j|)\rho_{LR}(I_L\otimes|j\rangle)\ge0.
$$
则
$$
(\operatorname{Id}_L\otimes\mathcal T)(\rho_{LR})
=\rho_L^{00}\otimes\tau_0+\rho_L^{11}\otimes E_0,
\qquad \operatorname{Tr}\rho_L^{00}+\operatorname{Tr}\rho_L^{11}=1.
$$
将非零左块按迹归一化，即为有限凸乘积密度和，证明 $L:R'$ 可分。这只消除该分割上的纠缠；若 $L$ 与另一个外部系统纠缠，这个结论不要求它们的纠缠消失。

每个 $F$ 已有由原始相关记忆给出的正分支，且端点输入通过上述代数延拓确定它们。若只给定一个已知 $F\ne0$，还可定义依赖该设置的替换仪器
$$
\mathcal R_b^{F}(X)=\operatorname{Tr}(X)\,\frac{Q_{F,b}}{q_F}.
$$
若 $Q_{F,b}/q_F=\sum_j\lambda_j|v_j\rangle\langle v_j|$ 是谱分解，则 $\sqrt{\lambda_j}|v_j\rangle\langle h_k|$（$0\le k\le3$）给出该映射的 Kraus 算子，所以它完全正。由 $\sum_b\operatorname{Tr}(Q_{F,b}/q_F)=1$，两映射之和保迹，并在 $Q(FC_0)$ 上给 $Q_{F,b}$；但它随 $F$ 改变，故不满足同一未知设置族上的要求。同样，报告概率的端点测量、忘记报告后的 Kraus 通道以及任何该通道的其他有效 Kraus 分解，都不等于指定的 $\widehat{\mathcal I}_b$：若某个有效二结果分解在全部允许输入上给出这些分支，唯一性又会迫使其负的 $b=1$ 分支成立。保留原始相关记忆足以实施这个下一实验；只保留端点且不提供 $F$ 标签，不能对该整个制备族实施带报告的正确延长。关于已完成端点实验的预测等价和代数状态更新，因而不蕴含这种物理仪器闭合。证明不对固定有限原始记录族单独断言同样障碍，也不确定其他辅助资源的最小容量或任意环境干预的动力学。证毕。

本命题所用仪器概念的成熟参考为 E. B. Davies、J. T. Lewis，*An operational approach to quantum probability*，Communications in Mathematical Physics 17，239–260（1970），[DOI:10.1007/BF01647093](https://doi.org/10.1007/BF01647093)。初始系统与环境相关、约化动力学的兼容域以及全空间正性要求之间的区分，参见 P. Pechukas，*Reduced Dynamics Need Not Be Completely Positive*，Physical Review Letters 73，1060–1062（1994），[DOI:10.1103/PhysRevLett.73.1060](https://doi.org/10.1103/PhysRevLett.73.1060)。测量后制备与破坏纠缠通道的术语参见 M. Horodecki、P. W. Shor、M. B. Ruskai，*Entanglement Breaking Channels*，Reviews in Mathematical Physics 15，629–641（2003），[DOI:10.1142/S0129055X03001709](https://doi.org/10.1142/S0129055X03001709)。这些引文提供概念背景；本命题的具体结论由所给 $T$、制备族、矩阵恒等式及负二次型推出。

## 追加锚（本行以下为增补区）

## 146. 独立报告翻转下端点延长仪器的精确噪声阈值

**命题 146.1（未知复左收缩族的一步带噪延长、闭阈值与 Kraus 实现）。** 沿用命题 145.1 的制备族及命题 130.1、137.1 的纯边界生成器。所有矩阵均在复数域上，$\dagger$ 表示共轭转置，$\mathsf T$ 表示普通转置，$\operatorname{outer}(v)=vv^\dagger$。置
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad 1+\alpha=\alpha^{-1},\qquad 1-\alpha=\alpha^2,
$$
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad
E_1=\operatorname{diag}(0,1),\qquad C_0=s^3J.
$$
各二维空间取正交标准基，向量化仍为
$$
\operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1 C_{ij}|i\rangle_L|j\rangle_R,
\qquad 00,01,10,11\text{ 为坐标次序}.
$$
从初始记忆 $m_0=s|0\rangle+\alpha|1\rangle$ 出发，以
$$
m_1=|0\rangle,\qquad T|j\rangle=|j\rangle_{\rm out}\otimes m_j
$$
恰好发出 $L,R$ 两个输出，再在 $L$ 上施加任意单 Kraus 成功分支 $F\in M_2(\mathbb C)$，$F^\dagger F\le I_2$，不归一化。成功旗标相同，后续端点仪器只接收成功制备的端点，不取得设置 $F$ 或原始相关记忆及其副本。全部复收缩，包括奇异矩阵和 $F=0$，都在量词范围内；这个端点滤波假设来自命题 145.1 的另行扩大的制备族，并非命题 138.1、139.1 的内部测量策略所授权的操作。令 $C=FC_0$，由该实际制备所得的未归一化输入为
$$
Q(C)=\operatorname{outer}(\operatorname{vec}_{LR}(C))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(CE_0)).
$$

比较协议保留这个成功制备中的同一个原始相关记忆，再用 $T$ 发出 $R'$，在旧 $R$ 上测量
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},\qquad b\in\{0,1\},
$$
并对最终记忆取偏迹。随后引入与制备及该测量独立的经典位 $e$，满足 $\Pr(e=1)=\varepsilon$，$0\le\varepsilon\le1$；只保留报告 $y=b\mathbin\oplus e$，丢弃 $b,e$ 的全部其他副本。以命题 145.1 的实际尖锐分支记号写成
$$
Q_b(C):=Q_{F,b}=\frac{\alpha}{2}Q(CZ^bJ),
$$
其中输出向量化在 $L,R'$ 上。带噪报告的实际未归一化分支是
$$
R_0(C)=(1-\varepsilon)Q_0(C)+\varepsilon Q_1(C),\qquad
R_1(C)=\varepsilon Q_0(C)+(1-\varepsilon)Q_1(C).
$$
这里混合的是带各自 Born 权重的算子，不是分别归一化的两个密度。

按标准基识别输入 $L,R$ 与输出 $L,R'$ 的四维空间。存在不依赖 $F$ 的复线性完全正映射 $\mathcal J_0,\mathcal J_1:M_4(\mathbb C)\to M_4(\mathbb C)$，使 $\mathcal J_0+\mathcal J_1$ 保迹并满足
$$
\mathcal J_y(Q(FC_0))=R_y(FC_0)
\quad\text{对全部 }F^\dagger F\le I_2\text{ 及 }y\in\{0,1\},
$$
当且仅当
$$
(1-2\varepsilon)^2\le\alpha,
\qquad\text{即}\qquad
\frac{1-\sqrt\alpha}{2}\le\varepsilon\le\frac{1+\sqrt\alpha}{2}.
$$
更精确地，令 $\lambda=1-2\varepsilon$、$\nu_y=(-1)^y\lambda$。对每个 $\varepsilon\in[0,1]$，在整个所声明制备族上的兼容性已经迫使唯一的复线性延拓
$$
\widehat{\mathcal J}_y=\operatorname{Id}_L\otimes\psi_{\nu_y},\qquad
\psi_\nu\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=\frac12\begin{pmatrix}
\alpha x+w+\nu(u+v)&\alpha^2x+\nu\alpha v\\
\alpha^2x+\nu\alpha u&\alpha^2x
\end{pmatrix},
$$
其中 $x,u,v,w$ 是相互独立的复数。这两个延拓恰在上述闭区间内完全正。

在允许区间内，置 $\delta_\nu=\alpha-\nu^2\ge0$，可取右端点 Kraus 算子
$$
K_1(\nu)=\frac1{\sqrt2}\begin{pmatrix}\nu&1\\\nu\alpha&0\end{pmatrix},\qquad
K_2(\nu)=\frac{\sqrt{\delta_\nu}}{\sqrt2}\begin{pmatrix}1&0\\\alpha&0\end{pmatrix},\qquad
K_3(\nu)=\frac{\alpha^2}{\sqrt2}\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$
带报告标签 $y$ 的六个算子 $I_L\otimes K_j(\nu_y)$ 组成一个固定端点仪器。对任意 $\varepsilon\in[0,1]$，其强制代数延拓的报告效应和非选择和分别为
$$
H_y=\frac{I_2+\nu_y X_{\rm P}}2,\qquad
X_{\rm P}=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\operatorname{Tr}\widehat{\mathcal J}_y(Y)=\operatorname{Tr}((I_L\otimes H_y)Y),
$$
$$
\widehat{\mathcal J}_0+\widehat{\mathcal J}_1
=\operatorname{Id}_L\otimes\mathcal T,\qquad
\mathcal T\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=x\tau_0+wE_0,\qquad
\tau_0=\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}.
$$
所有这些报告效应构成有效 POVM，且 $\mathcal T$ 始终是同一个完全正保迹通道；这两个事实各自均不蕴含指定带报告分支的完全正性。结论只涉及上述固定制备族、独立经典翻转和一次延长。

证明。命题 130.1 的等距以及命题 145.1 对命题 137.1 空内部记录的实际展开给出
$$
\Xi_2=s^3(|00\rangle+|01\rangle+|10\rangle)|0\rangle_M
+s^4(|00\rangle+|10\rangle)|1\rangle_M,
$$
$$
\chi_F=\operatorname{vec}_{LR}(C)|0\rangle_M
+s\operatorname{vec}_{LR}(CE_0)|1\rangle_M.
$$
这保留了两个记忆列；命题 145.1 的计算直接适用于全部复 $F$，不需要 $F^{-1}$。记 $C=(c_0,c_1)$，则
$$
q(C):=\operatorname{Tr}Q(C)=(1+\alpha)\|c_0\|^2+\|c_1\|^2,
\qquad 0\le q(C)\le1,\qquad q(C_0)=\alpha^3(3+2\alpha)=1.
$$
$C_0$ 可逆，故 $q(C)=0$ 恰当 $F=0$。比较协议在同一个 $\chi_F$ 上继续；命题 145.1 已从 $T$ 与旧 $R$ 的 bra 收缩得到其最终记忆两列的系数矩阵
$$
D_b=\frac{s}{\sqrt2}(c_0+\sigma c_1,\ c_0)
=\frac{s}{\sqrt2}CZ^bJ,\qquad sD_bE_0,\qquad \sigma=(-1)^b.
$$
取最终记忆偏迹即为 $Q(D_b)=Q_b(C)$。这直接引用同一相关动力学的分支，不把偏迹后的端点重新与独立记忆拼接。

置 $h(C)=\operatorname{Re}(c_0^\dagger c_1)$。利用 $\alpha(1+\alpha)=1$，展开范数得
$$
\begin{aligned}
q_b(C):=\operatorname{Tr}Q_b(C)
&=\frac{\alpha}{2}\bigl((1+\alpha)\|c_0+\sigma c_1\|^2+\|c_0\|^2\bigr)\\
&=\frac{q(C)}2+\sigma h(C),\qquad q_0(C)+q_1(C)=q(C).
\end{aligned}
$$
若 $F\ne0$，两个 $Z^bJ$ 均可逆，故 $q_b(C)>0$。独立翻转并忘记旧经典标签时，对同一报告的未归一化分支求和，正是所述 $R_y$，且
$$
r_y(C):=\operatorname{Tr}R_y(C)=\frac{q(C)}2+\nu_yh(C),\qquad
r_0(C)+r_1(C)=q(C).
$$
非零 $F$ 时 $r_y(C)>0$；成功条件下报告概率为 $r_y(C)/q(C)$，报告后的端点密度为 $R_y(C)/r_y(C)$。例如令 $\theta_b=Q_b(C)/q_b(C)$，则
$$
\frac{R_0(C)}{r_0(C)}
=\frac{(1-\varepsilon)q_0(C)}{r_0(C)}\theta_0
+\frac{\varepsilon q_1(C)}{r_0(C)}\theta_1.
$$
这两个条件权重一般不同于 $1-\varepsilon,\varepsilon$。当 $F=0$ 时所有未归一化算子及概率均为零，以上任何条件密度都不作定义。

现用命题 145.1 已证的兼容输入张成性。具体地，令 $P=I_L\otimes E_0$，则
$$
\mathcal L(Y)=Y+\alpha PYP,\qquad
\mathcal L^{-1}(Y)=Y-\alpha^2PYP,
\qquad Q(C)=\mathcal L(\operatorname{outer}(\operatorname{vec}_{LR}(C))).
$$
其中 $\alpha/(1+\alpha)=\alpha^2$。对任意复矩阵 $D$，命题 145.1 的正数缩放
$$
t=\max\{1,\|DC_0^{-1}\|_{\rm op}\},\qquad F=t^{-1}DC_0^{-1}
$$
满足 $F^\dagger F\le I_2$ 且 $D=tFC_0$。$Q$ 和每个 $R_y$ 都按 $t^2$ 缩放，因此线性兼容性从实际收缩族延至全部 $D$。该命题用四维标准基 $h_j$ 以及 $h_j+h_k,h_j+i h_k$ 的 $16$ 个外积证明 Hermitian 实张成；可逆的 $\mathcal L$ 及上述逐项正缩放给出实际兼容输入的同样张成性。每个复矩阵都是两个 Hermitian 矩阵的复线性组合，所以这也确定全部 $M_4(\mathbb C)$ 上的作用。这里的带符号线性组合只用于唯一性证明，不增加物理制备假设。

命题 145.1 的唯一尖锐延拓为 $\widehat{\mathcal I}_b=\operatorname{Id}_L\otimes\phi_b$。其右因子方向由
$$
\operatorname{vec}(CZ^bJ)=(I_L\otimes (Z^bJ)^{\mathsf T})\operatorname{vec}(C),
\qquad (Z^bJ)^{\mathsf T}=JZ^b=\begin{pmatrix}1&\sigma\\1&0\end{pmatrix}
$$
固定。该命题对四个独立复矩阵元给出的 $\phi_b$ 正是本命题 $\psi_\sigma$ 的公式。将两个尖锐延拓按实际经典翻转作线性组合，$\sigma$ 项变为 $\nu_y$，常数项不变，遂得到 $\widehat{\mathcal J}_y=\operatorname{Id}_L\otimes\psi_{\nu_y}$；它满足全部兼容性等式，由张成性也是唯一延拓。这个等式不施加 $v=\overline u$ 的限制，亦不把 $\mathcal L^{-1}$ 当作可实施的恢复映射。

为判定完全正性，记右端点矩阵单位 $e_{ij}=|i\rangle\langle j|$。取未归一化向量 $\Omega=|00\rangle+|11\rangle$，第一因子是输入参考，第二因子是通道输出。直接代入四个矩阵单位，得到
$$
\begin{aligned}
\mathsf C_\nu
&:=(\operatorname{Id}_{\rm ref}\otimes\psi_\nu)(\operatorname{outer}(\Omega))
=\sum_{i,j=0}^1e_{ij}\otimes\psi_\nu(e_{ij})\\
&=\frac12\begin{pmatrix}
\alpha&\alpha^2&\nu&0\\
\alpha^2&\alpha^2&\nu\alpha&0\\
\nu&\nu\alpha&1&0\\
0&0&0&0
\end{pmatrix}.
\end{aligned}
$$
对实数 $\nu$ 置 $\delta=\alpha-\nu^2$、$v_0=(1,\alpha)^{\mathsf T}$。$2\mathsf C_\nu$ 的前三维块以第三个对角元 $1$ 为 Schur 主元，其余二阶 Schur 补为
$$
\begin{pmatrix}
\alpha-\nu^2&\alpha^2-\alpha\nu^2\\
\alpha^2-\alpha\nu^2&\alpha^2-\alpha^2\nu^2
\end{pmatrix}
=\delta v_0v_0^{\mathsf T}+\alpha^4E_1.
$$
更直接地，对任意 $r,t,u,k\in\mathbb C$ 有精确恒等式
$$
2\begin{pmatrix}r\\t\\u\\k\end{pmatrix}^{\!\dagger}
\mathsf C_\nu\begin{pmatrix}r\\t\\u\\k\end{pmatrix}
=|u+\nu r+\nu\alpha t|^2
+\delta|r+\alpha t|^2+\alpha^4|t|^2.
$$
这里使用 $\alpha^3+\alpha^4=\alpha^2$。若 $\delta\ge0$，右边非负；若 $\delta<0$，取
$$
z_\nu=(1,0,-\nu,0)^{\mathsf T},\qquad
z_\nu^\dagger\mathsf C_\nu z_\nu=\frac{\alpha-\nu^2}{2}<0.
$$
因此 $\mathsf C_\nu\ge0$ 恰当 $\nu^2\le\alpha$。前三维主块的行列式为 $\alpha^4(\alpha-\nu^2)/8$，全四阶行列式则恒为零，不能用后者判定阈值。

若 $\psi_\nu$ 完全正，依定义 $\operatorname{Id}_{\rm ref}\otimes\psi_\nu$ 必将正算子 $\operatorname{outer}(\Omega)$ 送到正算子，所以负二次型已经排除 $\nu^2>\alpha$。若某个兼容端点分支 $\mathcal J_y$ 完全正，则唯一性迫使其等于 $\operatorname{Id}_L\otimes\psi_{\nu_y}$。将它与完全正的嵌入 $X\mapsto E_0\otimes X$ 及对 $L$ 的偏迹复合，所得恰为 $\psi_{\nu_y}$，故后者也必须完全正。两份 $\nu_y^2$ 都等于 $\lambda^2$，于是 $\lambda^2\le\alpha$ 是端点仪器存在的必要条件。$z_\nu$ 只是强制映射的 Choi 二次型测试向量，不是原始制备产生的负态；对任意允许的 $F$ 和 $\varepsilon\in[0,1]$，实际 $Q_b(C)$ 是正外积之和，$R_y(C)$ 是其非负混合，始终正半定。区间外所排除的是全空间完全正延拓，本论证不对 $\psi_\nu$ 的普通正性另作分类。

反之，设 $\delta=\alpha-\nu^2\ge0$，取陈述中的 $K_j(\nu)$。这三个矩阵的第一列依次为 $\nu v_0/\sqrt2$、$\sqrt\delta v_0/\sqrt2$、$\alpha^2|1\rangle/\sqrt2$，第二列依次为 $|0\rangle/\sqrt2,0,0$。因此在四个独立矩阵单位上逐项有
$$
\begin{aligned}
\sum_{j=1}^3 K_j e_{00}K_j^\dagger
&=\frac12(\alpha v_0v_0^\dagger+\alpha^4E_1)
=\frac12\begin{pmatrix}\alpha&\alpha^2\\\alpha^2&\alpha^2\end{pmatrix}
=\psi_\nu(e_{00}),\\
\sum_{j=1}^3 K_j e_{01}K_j^\dagger
&=\frac\nu2\begin{pmatrix}1&0\\\alpha&0\end{pmatrix}
=\psi_\nu(e_{01}),\\
\sum_{j=1}^3 K_j e_{10}K_j^\dagger
&=\frac\nu2\begin{pmatrix}1&\alpha\\0&0\end{pmatrix}
=\psi_\nu(e_{10}),\\
\sum_{j=1}^3 K_j e_{11}K_j^\dagger
&=\frac12 E_0=\psi_\nu(e_{11}).
\end{aligned}
$$
复线性性遂给出全部 $X\in M_2(\mathbb C)$ 上的 Kraus 恒等式。每个 Kraus 项在任意辅助空间上扩张后都是由 $I_{\rm anc}\otimes K_j$ 作合同，因而保持正半定；有限和完全正。张量上左端点恒等即给出所需端点分支的完全正性。这个充分性直接来自所列算子，不需要从 Choi 正性反推完全正性的定理。

还须证明这两分支组成同一个保迹仪器。直接乘法以及
$$
\alpha(1+\alpha^2)+\alpha^4=\alpha+\alpha^3+\alpha^4=1
$$
给出
$$
\sum_{j=1}^3 K_j(\nu)^\dagger K_j(\nu)
=\frac12\begin{pmatrix}1&\nu\\\nu&1\end{pmatrix}
=\frac{I_2+\nu X_{\rm P}}2.
$$
取 $\nu_0=\lambda$、$\nu_1=-\lambda$，两个效应相加为 $I_2$，从而
$$
\sum_{y=0}^1\sum_{j=1}^3
(I_L\otimes K_j(\nu_y))^\dagger(I_L\otimes K_j(\nu_y))=I_4.
$$
所以总映射保迹；每个分支效应介于零与恒等之间，分支不增迹。这一个仪器只依赖给定的 $\varepsilon$，其右 Kraus 算子从旧 $R$ 映到新 $R'$，保持 $L$ 不变，不访问 $F,b,e$ 或已丢弃的记忆。结合已证的兼容性，它对全部复收缩都给出正确未归一化输出。两个边界 $\lambda=\pm\sqrt\alpha$ 均使 $K_2=0$，其余公式仍成立，没有除以 $\delta$ 的步骤，故两个等号边界都允许。由 $\lambda=1-2\varepsilon$ 解不等式即得陈述中的闭区间。

最后，对全部实数 $\nu\in[-1,1]$，直接从 $\psi_\nu$ 的公式取迹，得到
$$
\operatorname{Tr}\psi_\nu(X)=\frac{x+w+\nu(u+v)}2
=\operatorname{Tr}\left(\frac{I_2+\nu X_{\rm P}}2 X\right).
$$
效应的特征值为 $(1+\nu)/2,(1-\nu)/2$。故即使不满足完全正阈值，两个报告概率仍可由端点 POVM 实现，但这不提供指定条件输出。又有
$$
(\psi_\lambda+\psi_{-\lambda})(X)=x\tau_0+wE_0=\mathcal T(X),
\qquad \operatorname{Tr}\tau_0=1,\qquad \det\tau_0=\alpha^5>0.
$$
这正是命题 145.1 已证明的计算基测量后制备通道，故对每个噪声参数均完全正保迹。在 $\varepsilon=1/2$ 时，$\lambda=0$，两个分支都等于 $(\operatorname{Id}_L\otimes\mathcal T)/2$；在 $\varepsilon=0$ 或 $1$ 时，$\lambda^2=1>\alpha$，负 Choi 期望恰为 $(\alpha-1)/2=-\alpha^2/2$，尽管报告 POVM 和非选择通道仍有效。交换报告标签使 $\lambda$ 变号，所以允许区间关于 $1/2$ 对称。对 $0<|\lambda|\le\sqrt\alpha$，效应差 $H_0-H_1=\lambda X_{\rm P}$ 非零，仪器保留非零报告对比度；完全抹去报告并非必要。上述存在性与障碍只比较这一制备族的一步延长，不推及其他制备、其他噪声或多步闭合。证毕。

本命题的 Choi 矩阵与完全正映射术语参见 Man-Duen Choi，*Completely positive linear maps on complex matrices*，Linear Algebra and its Applications 10（3），285–290（1975），[DOI:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0)。此引文提供成熟背景；所述固定制备族的阈值、闭边界及 Kraus 算子由本命题的矩阵恒等式给出。

## 追加锚（本行以下为增补区）
## 147. 任意有限报告的端点复现、最大二元因子与精确饱和

**命题 147.1（有限报告的逐行完全正判据、唯一随机分解与饱和恢复）。** 沿用命题 145.1、146.1 的全部复左收缩制备族和向量化约定。具体地，各二维空间取正交标准基，$\dagger$ 表示共轭转置，$\mathsf T$ 表示普通转置，$\operatorname{outer}(v)=vv^\dagger$，并置
$$
\alpha=\frac{\sqrt5-1}{2},\qquad s=\sqrt\alpha,\qquad
\alpha+\alpha^2=1,\qquad 0<s<1,
$$
$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
Z=\operatorname{diag}(1,-1),\qquad E_0=\operatorname{diag}(1,0),\qquad C_0=s^3J,
\qquad \operatorname{vec}_{LR}(C)=\sum_{i,j=0}^1C_{ij}|i\rangle_L|j\rangle_R.
$$
从纯初始记忆 $m_0=s|0\rangle+\alpha|1\rangle$ 出发，以 $m_1=|0\rangle$、$T|j\rangle=|j\rangle_{\rm out}\otimes m_j$ 恰好发出 $L,R$，随后在 $L$ 上施加任意单 Kraus 成功分支 $F\in M_2(\mathbb C)$，$F^\dagger F\le I_2$。包括奇异 $F$ 与 $F=0$，不对成功分支归一化；保留共同成功旗标，而不向后续端点仪器提供 $F$。这是命题 145.1 明定的扩大的制备族，不由命题 138.1、139.1 的有限内部记录策略推出。记 $C=FC_0$，端点仪器只取得约化输入
$$
Q(C)=\operatorname{outer}(\operatorname{vec}_{LR}(C))
+\alpha\operatorname{outer}(\operatorname{vec}_{LR}(CE_0)).
$$
比较协议则保留该制备的同一个原始相关记忆，用 $T$ 再发出一次 $R'$，在旧 $R$ 上测量固定基
$$
|\eta_b\rangle=\frac{|0\rangle+(-1)^b|1\rangle}{\sqrt2},\qquad b\in\{0,1\},
$$
再对最终记忆取偏迹，实际尖锐分支为命题 146.1 的
$$
Q_b(C)=\frac\alpha2 Q(CZ^bJ),
$$
其中输出向量化在 $L,R'$ 上。所有步骤无反馈；端点仪器不能访问原始记忆及其副本。

任取非空有限集合 $Y$ 和列随机矩阵 $W:Y\leftarrow\{0,1\}$，即 $W(y\mid b)\ge0$、$\sum_yW(y\mid b)=1$。在实际尖锐记录完成后，给定 $b$ 按 $W(\cdot\mid b)$ 独立于其余系统及制备设置抽取报告，只保留 $y$ 与量子输出 $L,R'$，不保留 $b$、处理随机性或已丢弃记忆的可访问副本。定义
$$
R_y(C)=\sum_{b=0}^1W(y\mid b)Q_b(C),\qquad
c_y=W(y\mid0)+W(y\mid1),\qquad d_y=W(y\mid0)-W(y\mid1).
$$
称 $W$ 对此制备族可由端点仪器复现，是指存在一个不依赖 $F$ 的仪器 $(\mathcal J_y)_{y\in Y}$：每个 $\mathcal J_y:M_4(\mathbb C)\to M_4(\mathbb C)$ 复线性且完全正，$\sum_y\mathcal J_y$ 保迹，并且
$$
\mathcal J_y(Q(FC_0))=R_y(FC_0)
\qquad(F^\dagger F\le I_2,\ y\in Y).
$$
这里按标准基识别输入 $L,R$ 与输出 $L,R'$。要求是每个未归一化分支相等，等价于完整报告与量子输出的联合算子 $\sum_y|y\rangle\langle y|\otimes R_y(C)$ 相等。每个上述 $W$ 都能处理原实验已完成的记录；本定义限制的是只从约化端点输入复现这个联合算子，不是对经典处理本身的物理许可分类。

令
$$
B_s(t\mid b)=\frac{1+(-1)^{t+b}s}{2},\qquad t,b\in\{0,1\}.
$$
则以下三项等价：$W$ 可由端点仪器复现；对每个 $y$ 有 $d_y^2\le\alpha c_y^2$；存在列随机矩阵 $V:Y\leftarrow\{0,1\}$ 使 $W=VB_s$。该随机因子唯一，且
$$
V(y\mid t)=\frac{c_y+(-1)^t d_y/s}{2}.
$$
不论 $W$ 是否满足完全正判据，制备族上的分支匹配都迫使唯一的全空间复线性延拓。以命题 146.1 的
$$
\psi_\nu\!\begin{pmatrix}x&u\\v&w\end{pmatrix}
=\frac12\begin{pmatrix}
\alpha x+w+\nu(u+v)&\alpha^2x+\nu\alpha v\\
\alpha^2x+\nu\alpha u&\alpha^2x
\end{pmatrix}
\qquad(x,u,v,w\in\mathbb C)
$$
表示，该延拓恰为
$$
\widehat{\mathcal J}_y=
\begin{cases}
c_y(\operatorname{Id}_L\otimes\psi_{d_y/c_y}),&c_y>0,\\
0,&c_y=0.
\end{cases}
$$
对于具有相同二元输入的报告矩阵，定义 $A\preceq B$ 表示 $A=SB$，其中 $S$ 为列随机的输出处理矩阵；互相满足此关系称为随机后处理等价。$B_s$ 是全部可由端点仪器复现的有限报告在此关系下的最大元，最大性按随机后处理等价理解，不要求字面报告字母表唯一。

进一步，对每个可由端点仪器复现的 $W$，两条件列的总变差满足
$$
\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))
:=\frac12\sum_{y\in Y}|d_y|\le s.
$$
等号成立当且仅当每个非零行满足 $|d_y|=sc_y$，也当且仅当 $W$ 与 $B_s$ 随机后处理等价。等号时，按 $d_y$ 的正负作确定性分组即恢复 $B_s$，零行可任意分组；所恢复的是这个极端带噪报告，不是原始尖锐记录 $b$。总变差比较的是 $W$ 的条件列，不假定实际尖锐 Born 先验均匀，也不表示量子迹距离。仅有此总变差上界不足以推出端点复现：例如
$$
W_* =\begin{pmatrix}1/10&0\\9/10&1\end{pmatrix}
$$
的总变差为 $1/10<s$，却不满足逐行判据。结论只涉及所声明制备族的一次延长和这个报告与量子输出联合算子，不要求恢复与已丢弃记忆、不可访问制备标签或任意未来干预的关联，亦不附加熵、容量、最小记忆、多步闭合或普适经典性结论。

证明。命题 145.1、146.1 从命题 130.1 的字面生成器及命题 137.1 的空内部记录得到
$$
\chi_F=\operatorname{vec}_{LR}(C)|0\rangle_M
+s\operatorname{vec}_{LR}(CE_0)|1\rangle_M.
$$
继续使用同一个相关记忆时，固定 $b$ 的最终记忆两列系数矩阵是 $D_b=(s/\sqrt2)CZ^bJ$ 与 $sD_bE_0$，故其偏迹正是上述 $Q_b(C)$；这两个记忆列始终保持原振幅。写 $C=(r,t)$，引用命题 146.1 已由这些列证明的 Born 权重等式，得
$$
q(C):=\operatorname{Tr}Q(C)=(1+\alpha)\|r\|^2+\|t\|^2,
\qquad h(C)=\operatorname{Re}(r^\dagger t),
$$
$$
q_b(C):=\operatorname{Tr}Q_b(C)
=\frac{\|r+(-1)^bt\|^2+\alpha\|r\|^2}{2}
=\frac{q(C)}2+(-1)^bh(C),\qquad q_0(C)+q_1(C)=q(C).
$$
收缩条件给 $0\le q(C)\le1$，$C_0$ 可逆给 $q(C)=0$ 当且仅当 $F=0$；若 $F\ne0$，上式两个平方范数不可能同时为零，故两个 $q_b(C)$ 都严格为正。经典处理的条件独立性因此给
$$
p_y(C):=\operatorname{Tr}R_y(C)=\frac{c_yq(C)}2+d_yh(C),\qquad
\sum_yp_y(C)=q(C).
$$
当 $F\ne0$ 时，$p_y(C)=0$ 恰当该报告行全零。对 $p_y(C)>0$，成功条件下的报告概率为 $p_y(C)/q(C)$，报告态为
$$
\frac{R_y(C)}{p_y(C)}
=\sum_{b=0}^1\frac{W(y\mid b)q_b(C)}{p_y(C)}\,
\frac{Q_b(C)}{q_b(C)}.
$$
故归一化尖锐态的混合权重含有实际 Born 权重，不能直接以原始 $W(y\mid b)$ 代替。当 $F=0$ 时所有分支及概率为零，不定义任何条件态；零行亦不定义报告态。

现直接使用命题 145.1、146.1 对同一个全部复收缩族证明的张成性和唯一尖锐延拓。其适用性依赖于 $C_0$ 可逆、任意复 $D$ 可正缩放为 $FC_0$，以及可逆线性算子
$$
\mathcal L(A)=A+\alpha PAP,\qquad
\mathcal L^{-1}(A)=A-\alpha^2PAP,\qquad P=I_L\otimes E_0
$$
把四维秩一外积的 Hermitian 实张成族送到兼容输入的张成族。因此兼容等式确定整个 $M_4(\mathbb C)$ 上的复线性映射，不只确定兼容的正算子。该族包括全部复 $F$，无需任何 $F^{-1}$；固定原始有限记录集本身没有在这里承担张成性。由前述命题，尖锐分支的延拓是 $\operatorname{Id}_L\otimes\psi_{(-1)^b}$；其中右乘 $Z^bJ$ 对应右 Hilbert 因子的 $(Z^bJ)^{\mathsf T}=JZ^b$，所以独立复矩阵元 $u,v$ 的方向正是陈述中的方向。

将这两个尖锐延拓按一行 $W$ 线性相加，利用 $\psi_\nu$ 对实参数 $\nu$ 的仿射性，若 $c_y>0$ 就得
$$
\sum_bW(y\mid b)(\operatorname{Id}_L\otimes\psi_{(-1)^b})
=c_y(\operatorname{Id}_L\otimes\psi_{\nu_y}),\qquad \nu_y=d_y/c_y.
$$
它已匹配该行的所有实际未归一化分支，张成性保证唯一。若 $c_y=0$，非负性迫使整行及 $d_y$ 为零，张成性迫使延拓为零，无需定义 $\nu_y$。

命题 146.1 已对相互独立的复矩阵元证明 $\psi_\nu$ 完全正当且仅当 $\nu^2\le\alpha$，并在此闭区间给出 $K_j(\nu)$ 的 Kraus 分解，包括 $\nu=\pm s$ 时 $K_2=0$ 的边界。对 $c_y>0$，若全端点映射 $\widehat{\mathcal J}_y$ 完全正，将它依次与 $A\mapsto E_0\otimes A$、对 $L$ 的偏迹复合并除以 $c_y$，便得到完全正的 $\psi_{\nu_y}$。故 $d_y^2\le\alpha c_y^2$ 必要。反之，该不等式使
$$
\sqrt{c_y}\,I_L\otimes K_j(\nu_y)\qquad(j=1,2,3)
$$
给出所需分支的 Kraus 算子，零行取零映射。命题 146.1 的效应恒等式给
$$
\mathsf E_y=I_L\otimes\frac{c_yI_2+d_yX_{\rm P}}2,\qquad
X_{\rm P}=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$
列随机性给 $\sum_yc_y=2$、$\sum_yd_y=0$，故 $\sum_y\mathsf E_y=I_4$。这些完全正分支之和保迹，组成同一个与 $F$ 无关的仪器。这证明端点复现与逐行不等式的等价，包含全部零行和阈值边界。

为求随机因子，写
$$
B_s=\frac12\begin{pmatrix}1+s&1-s\\1-s&1+s\end{pmatrix},\qquad
\det B_s=s>0.
$$
若 $W=VB_s$，逐行比较和与差，必有
$$
V(y\mid0)+V(y\mid1)=c_y,\qquad
s\bigl(V(y\mid0)-V(y\mid1)\bigr)=d_y.
$$
解这两个等式即得唯一的所列 $V$。由于 $s>0$，其非负性恰等价于 $|d_y|\le sc_y$，也就是逐行完全正判据；两个列和分别为
$$
\sum_yV(y\mid t)=\frac{\sum_yc_y+(-1)^t\sum_yd_y/s}{2}=1.
$$
反过来，在该判据下这样定义 $V$，它列随机，且直接相乘给
$$
(VB_s)(y\mid b)=\frac{c_y+(-1)^bd_y}{2}=W(y\mid b).
$$
零行给出 $V$ 的零行，乘积方向为从 $b$ 经 $B_s$ 到 $t$ 再经 $V$ 到 $y$。

这一分解也在量子输出上实现所要求的等式。先做 $B_s$ 对应的边界仪器
$$
\mathcal I_t=\operatorname{Id}_L\otimes\psi_{(-1)^ts},\qquad t=0,1,
$$
再以 $V(y\mid t)$ 处理其报告并丢弃 $t$。它的第 $y$ 个分支在整个 $M_4(\mathbb C)$ 上满足
$$
\sum_tV(y\mid t)\mathcal I_t=\widehat{\mathcal J}_y,
$$
因为两系数的和为 $c_y$、乘上 $s$ 的差为 $d_y$；零行情形两边同为零。因此复现的是每个量子分支以及完整联合算子，非仅报告概率。$B_s$ 本身满足判据，而每个可复现 $W$ 都有 $W\preceq B_s$，所以它是所述最大元；同一等价类可有分裂后的更多标签，不是唯一字母表。另由 $d_y=s(V(y\mid0)-V(y\mid1))$ 可见
$$
\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))
=s\operatorname{TV}(V(\cdot\mid0),V(\cdot\mid1)).
$$
$V$ 的两列总变差可以达到 $1$，例如 $W=B_s$ 时 $V=I_2$；上界 $s$ 针对的是 $W$。

最后逐行求和得到
$$
\frac12\sum_y|d_y|\le\frac s2\sum_yc_y=s,\qquad
s-\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))
=\frac12\sum_y(sc_y-|d_y|).
$$
右边为有限个非负数的和，故等号恰当每个亏量为零。零行自动满足，非零行则有 $d_y=\pm sc_y\ne0$。将正号行放入 $Y_+$、负号行放入 $Y_-$，零行任意分入两者，记 $C_\pm=\sum_{y\in Y_\pm}c_y$。饱和及列和给
$$
C_++C_-=2,\qquad sC_+-sC_-=\sum_yd_y=0,
\qquad C_+=C_-=1.
$$
于是
$$
\sum_{y\in Y_+}W(y\mid b)=\frac{1+(-1)^bs}{2},\qquad
\sum_{y\in Y_-}W(y\mid b)=\frac{1-(-1)^bs}{2}.
$$
定义确定性列随机矩阵 $U$，在 $Y_+$ 上输出 $0$、在 $Y_-$ 上输出 $1$，便有 $UW=B_s$。同一分组还给 $\sum_{y\in Y_+}\widehat{\mathcal J}_y=\mathcal I_0$、$\sum_{y\in Y_-}\widehat{\mathcal J}_y=\mathcal I_1$，故极端报告的对应量子分支亦被恢复。

反之，任意列随机 $U$ 都满足有限和三角不等式
$$
\sum_t\left|\sum_yU(t\mid y)d_y\right|
\le\sum_{t,y}U(t\mid y)|d_y|=\sum_y|d_y|.
$$
若 $UW=B_s$，便有 $s=\operatorname{TV}(B_s(\cdot\mid0),B_s(\cdot\mid1))\le\operatorname{TV}(W(\cdot\mid0),W(\cdot\mid1))\le s$，所以必须饱和。结合总有的 $W=VB_s$，即得饱和与随机后处理等价的双向结论。全论证对任意非空有限 $Y$ 逐行成立，不需要字母表大小的上界。

为区分逐行判据与总体总变差，$W_*$ 的两行有
$$
(c_0,d_0)=(1/10,1/10),\qquad
(c_1,d_1)=(19/10,-1/10),\qquad
(\nu_0,\nu_1)=(1,-1/19).
$$
第一行违反 $\nu_0^2\le\alpha$，第二行满足该式，而 $\sum_yc_y\nu_y=0$ 且总变差仅为 $1/10$。由 $\alpha^2+\alpha=1$ 和 $0<\alpha<1$ 可得 $\alpha>1/2$，故 $1/10<s$ 及 $1/19^2<\alpha$。对每个非零 $F$，第一行的实际概率为 $q_0(C)/10>0$，不能作为不可能事件略去。

事实上，对任意列随机 $W$，即使违反完全正判据，也有 $|d_y|\le c_y$，故上述 $\mathsf E_y$ 的两个右因子特征值为 $(c_y\pm d_y)/2=W(y\mid0),W(y\mid1)\ge0$，且 $\sum_y\mathsf E_y=I_4$。从 $\psi_\nu$ 的迹式得到 $\operatorname{Tr}\widehat{\mathcal J}_y(A)=\operatorname{Tr}(\mathsf E_yA)$；对任意固定输出密度 $\tau$，映射 $A\mapsto\operatorname{Tr}(\mathsf E_yA)\tau$ 组成一个可实现这些概率的仪器。其完全正性可直接看出：若 $\mathsf E_y=\sum_j e_j|u_j\rangle\langle u_j|$、$\tau=\sum_k t_k|v_k\rangle\langle v_k|$ 为谱分解，则 $\sqrt{e_jt_k}|v_k\rangle\langle u_j|$ 是 Kraus 算子。但这不保证输出为所需的 $R_y(C)$。

此外，对所有 $W$，强制延拓的非选择和总为
$$
\sum_y\widehat{\mathcal J}_y
=\operatorname{Id}_L\otimes(2\psi_0)
=\operatorname{Id}_L\otimes\mathcal T,
$$
其中 $\mathcal T$ 是命题 146.1 已证明的完全正保迹通道。因而有效 POVM 和有效非选择和各自都不足以保证指定分支完全正；$W_*$ 与尖锐恒等报告 $W=I_2$ 都体现这个区别。命题 146.1 的负 Choi 二次型排除的是兼容族所迫使的全空间完全正延拓，实际 $Q_b(C)$ 与 $R_y(C)$ 始终是正算子，并无实际分支产生负态的结论。证毕。

## 追加锚（本行以下为增补区）
