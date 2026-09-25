# 递归关系观察：共同相位谱与精确接收边界

## 1. 同一相位来源与完整联合接收

**定义 1.1（带已知权重的共同相位发射）。** 取
\[
\alpha=(\sqrt5-1)/2,\qquad B=M=\mathbb C^2,\qquad
m_0=\sqrt\alpha\,|0\rangle+\alpha|1\rangle,\quad m_1=|0\rangle,
\qquad T|i\rangle=|i\rangle\otimes m_i.
\tag{1.1}
\]
两个记忆向量均为单位向量且线性独立，\(T:M\to B\otimes M\) 为等距。此处使用[上下文几何卷定义42.1](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#421-同一装置上的联合任务与纯根任务)的同一个发射装置与输出在前的因子次序。

令 \(\Theta\subseteq\mathbb R/(2\pi\mathbb Z)\) 非空，\(c=(c_t)_{t\ge1}\) 是已知整数序列，定义
\[
R_\gamma=\operatorname{diag}(1,e^{i\gamma}),\qquad
T_{\vartheta,t}^{\rm step}=(R_{c_t\vartheta}\otimes I_M)T,\qquad
T_{\vartheta,0}=I_M,
\]
\[
H_n=B^{\otimes n},\quad H_0=\mathbb C,\qquad
T_{\vartheta,n+1}=(I_{H_n}\otimes T_{\vartheta,n+1}^{\rm step})T_{\vartheta,n}.
\tag{1.2}
\]
上标 \({\rm step}\) 标识一步等距，\(T_{\vartheta,n}\) 则是累计等距。同一运行从头到尾使用同一个实际 \(\vartheta\)，各步不重新选择相位。每个新发出位可由与此前整个系统独立的纯空白及该步等距的酉延拓生成；没有向活动记忆的反馈、复位或中间干预。

固定有限维参考 \(J\) 及一次联合输入 \(\rho\in\mathcal D(J\otimes M)\)，令
\[
\Omega_{\vartheta,n}(\rho)
=(I_J\otimes T_{\vartheta,n})\rho(I_J\otimes T_{\vartheta,n}^*).
\tag{1.3}
\]
来源类允许全部这样的输入，特别允许 \(J=\mathbb C^2\) 与一个 \(JM\) Bell 对。\(\vartheta\) 是相对于固定已知基的实际作用参数；读出权限包括该基下的相干终端检验，不将不同 \(\vartheta\) 直接认作不可观察的整体相位。

**定义 1.2（同一物理接收边界）。** 对固定 \(n,\Theta,c\)，允许编码和解码通道
\[
\mathcal E_n:\mathcal L(H_n)\to\mathcal L(K),\qquad
\mathcal D_n:\mathcal L(K)\to\mathcal L(H_n)
\]
依赖 \(n,\Theta,c\) 和已知装置，但不能依赖实际 \(\vartheta\)、未知输入或不可访问的参考。要求
\[
(\operatorname{id}_J\otimes(\mathcal D_n\mathcal E_n)
 \otimes\operatorname{id}_M)\Omega_{\vartheta,n}(\rho)
=\Omega_{\vartheta,n}(\rho)
\quad(\vartheta\in\Theta,\ \rho\in\mathcal D(J\otimes M)).
\tag{1.4}
\]
两个通道均在整个声明载体上完全正且保迹。最小化的资源 \(k_n(\Theta,c)\) 是 \(\dim K\)；所有跨越编码、解码间隔而保留输入相关信息的接收系统都包含在 \(K\) 中，包括经典标签。\(J\) 和活动 \(M\) 原样保留，接收器无权访问它们。量词是每个允许相位下的完整联合态恢复，不只恢复相位平均后的档案边缘。

被动顺序接收允许每步仅操作接收寄存器与最新发出位，把该发出位清回独立纯空白后丢弃；在每个事先指定的有限终端提供式（1.4）的解码。发射计数、已知权重表、门描述、空白、路由、实际历时和输出端口另行计量，\(k_n\) 不计它们为免费取得的来源信息。原已获记录保持不变。

**定义 1.3（合法词与相位作用谱）。** 对 \(n\ge1\)，令 \(\mathcal W_n\) 为不含相邻 \(11\) 的二元词，\(\mathcal W_n^{ij}\) 为首位 \(i\)、末位 \(j\) 的子集。置
\[
A(w)=\prod_{t=1}^{n-1}(m_{w_t})_{w_{t+1}}>0,
\qquad Q_c(w)=\sum_{t=1}^n c_tw_t,
\qquad \mathcal Q_n^{ij}=\{Q_c(w):w\in\mathcal W_n^{ij}\}.
\tag{1.5}
\]
约定 \(\mathcal W_0=\{\varepsilon\}\)，其中 \(\varepsilon\) 是空词，\(A(\varepsilon)=1,Q_c(\varepsilon)=0\)；首末扇区只在 \(n\ge1\) 定义。空乘积为一；不存在的首末扇区给空集。对每个整数 \(q\)，记 \(f_q(\vartheta)=e^{iq\vartheta}\)，并定义有限维字符空间
\[
\mathcal U_n^{ij}
=\operatorname{span}_{\mathbb C}\{f_q|_\Theta:q\in\mathcal Q_n^{ij}\}
\subseteq\mathbb C^\Theta,
\qquad d_n(\Theta,c)=\sum_{i,j=0}^1\dim\mathcal U_n^{ij}.
\tag{1.6}
\]
当 \(\Theta\) 有限时，各维数就是矩阵 \((e^{iq\vartheta})_{\vartheta\in\Theta,q\in\mathcal Q_n^{ij}}\) 的复秩。不同相位按模 \(2\pi\) 区分。

## 2. 共同作用谱决定精确物理容量

**定理 2.1（同源相位族的精确接收容量）。** 在定义1.1—1.3的同一来源与权限下，
\[
\boxed{k_0=1,\qquad k_n(\Theta,c)=d_n(\Theta,c)\quad(n\ge1).}
\tag{2.1}
\]
特别地，若 \(\Theta\) 是无限集合，则
\[
\boxed{k_n(\Theta,c)=\sum_{i,j=0}^1|\mathcal Q_n^{ij}|.}
\tag{2.2}
\]
来源不必允许不同相位之间的相干叠加。式（2.1）的下界适用于全部满足（1.4）的 CPTP 编解码。

证明。定义实际档案列
\[
\chi_{ij}^{n}(\vartheta)
=\sum_{w\in\mathcal W_n^{ij}}A(w)e^{i\vartheta Q_c(w)}|w\rangle.
\tag{2.3}
\]
逐步展开等距，得到
\[
T_{\vartheta,n}|i\rangle
=\sum_{j=0}^1\chi_{ij}^{n}(\vartheta)\otimes m_j.
\tag{2.4}
\]
因为 \(m_0,m_1\) 线性独立，所有来源块的档案支撑恰为
\[
S_n(\vartheta)=\operatorname{span}\{\chi_{ij}^{n}(\vartheta):i,j\in\{0,1\}\}.
\]
对每个首末扇区及实际出现的荷，置
\[
g_{ijq}=\sum_{\substack{w\in\mathcal W_n^{ij}\\Q_c(w)=q}}A(w)|w\rangle.
\tag{2.5}
\]
这些向量非零，不同 \((i,j,q)\) 的支撑不交，因而线性独立。式（2.3）变成 \(\chi_{ij}^{n}(\vartheta)=\sum_qe^{iq\vartheta}g_{ijq}\)。于是共同线性包
\[
W_n=\operatorname{span}_{\vartheta\in\Theta}S_n(\vartheta)
\tag{2.6}
\]
的维数正是（1.6）。即使 \(\Theta\) 无限，这也只是有限个字符的线性代数：若评价行张成不是全秩，其消去向量恰给字符的线性依赖。

接着证明单个实际编解码必须在整个 \(W_n\) 上可逆，而非仅在各个相位下分别可逆。对任意 \(\vartheta,\varphi\in\Theta\)，取
\[
z_t=e^{ic_t(\varphi-\vartheta)},\qquad D(z)=\operatorname{diag}(1,z),
\qquad P=\begin{pmatrix}\alpha&\alpha^2\\1&0\end{pmatrix}.
\]
内积第一变量共轭线性时，四个同首末扇区内积组成的 \(2\times2\) 矩阵为
\[
F_n(\vartheta,\varphi)_{ij}
=\langle\chi_{ij}^{n}(\vartheta),\chi_{ij}^{n}(\varphi)\rangle,
\qquad
F_n=D(z_1)P D(z_2)\cdots P D(z_n).
\tag{2.7}
\]
每个词的首位给第一项 \(D(z_1)\)，之后的转移振幅平方给 \(P\)，新位的相位给相应 \(D(z_t)\)，逐词求和即得。故
\[
\det F_n=(-\alpha^2)^{n-1}\prod_{t=1}^n z_t\ne0.
\tag{2.8}
\]
至少一个扇区内积非零，所以任意两份 \(S_n(\vartheta),S_n(\varphi)\) 都不正交。

令 \(\mathcal L=\mathcal D_n\mathcal E_n\)，并在 \(JM\) 准备 Bell 态。其实际输出是纯态
\[
|\Psi_\vartheta\rangle
=\frac1{\sqrt2}\sum_{i,j}\chi_{ij}^{n}(\vartheta)
 \otimes|i\rangle_J\otimes m_j,
\tag{2.9}
\]
这里只为书写把档案置于左侧。由于 \(|i\rangle\otimes m_j\) 线性独立，\(H_n\mid JM\) 的左 Schmidt 支撑就是 \(S_n(\vartheta)\)。式（1.4）保留这份联合纯态；对其 Schmidt 展开逐个夹取右侧矩阵单位，得到
\[
\mathcal L(X)=X\qquad(X\in\mathcal L(S_n(\vartheta))).
\tag{2.10}
\]

取同一个通道 \(\mathcal L\) 的 Stinespring 等距 \(V:H_n\to H_n\otimes E\)。式（2.10）意味着存在单位向量 \(e_\vartheta\in E\)，使
\[
Vx=x\otimes e_\vartheta\qquad(x\in S_n(\vartheta)).
\tag{2.11}
\]
具体地，纯态输出先使每个单位向量的像为该向量与环境的乘积；再对同一子空间中的两个基向量及其叠加使用（2.10），环境向量就必须相同。这是精确不扰动与参考保持的标准机制，亦见 Koashi—Imoto 的不扰动态族分解。[^phase_ki]

若 \(x\in S_n(\vartheta),y\in S_n(\varphi)\) 的内积非零，等距性给
\[
\langle x,y\rangle
=\langle Vx,Vy\rangle
=\langle x,y\rangle\langle e_\vartheta,e_\varphi\rangle.
\]
所以 \(\langle e_\vartheta,e_\varphi\rangle=1\)，即两环境向量相同。（2.8）对任意相位对均成立，故所有 \(e_\vartheta\) 是同一向量。线性性于是强迫
\[
Vw=w\otimes e\quad(w\in W_n),\qquad
\mathcal L|_{\mathcal L(W_n)}=\operatorname{id}.
\tag{2.12}
\]
这没有增设可制备相位叠加的假设；共同线性包上的恒等性是同一物理通道与实际支撑非正交关系的后果。

因此 \(\mathcal E_n\) 在 \(\mathcal L(W_n)\) 上单射。比较复线性维数，\((\dim W_n)^2\le(\dim K)^2\)，得到所需下界。反向取 \(W_n\) 到 \(\mathbb C^{\dim W_n}\) 的等距，把补空间用固定态替换；解码在编码像上用逆等距，在补空间同样用固定态替换。与[上下文几何卷命题42.5](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md#424-全域通道延拓与原权限内的终端运输)相同的 Kraus 完成使两映射在全域 CPTP，复合在 \(\mathcal L(W_n)\) 上恒等，故达到下界。\(n=0\) 的档案一维。

若 \(\Theta\) 无限，不同整数指数的有限线性组合在其上为零时，乘以足够高的 \(e^{i\vartheta}\) 次幂即得到在无限多个不同点为零的普通多项式，故全部系数为零。各字符线性独立，得到（2.2）。证明完毕。

## 3. 前缀接收与相位不确定性的容量增长

**定理 3.1（谱交叠与逐步容量）。** 对定义1.1中的固定权重序列和同一 \(\Theta\)，\(d_0=1,d_1=2\)，且对 \(n\ge1\)，
\[
\boxed{d_{n+1}-d_n
=\sum_{i=0}^1\bigl(\dim\mathcal U_n^{i0}
-\dim(\mathcal U_n^{i0}\cap\mathcal U_n^{i1})\bigr)\ge0.}
\tag{3.1}
\]
对每个固定有限 \(N\)，同一个 \(d_N\) 维被动接收寄存器能在每个前缀 \(n\le N\) 精确保留定义1.2的联合来源；\(d_N\) 也是服务这些前缀所需的最小维数。

证明。合法词延长给
\[
\mathcal Q_{n+1}^{i0}=\mathcal Q_n^{i0}\cup\mathcal Q_n^{i1},\qquad
\mathcal Q_{n+1}^{i1}=c_{n+1}+\mathcal Q_n^{i0}.
\tag{3.2}
\]
故 \(\mathcal U_{n+1}^{i0}=\mathcal U_n^{i0}+\mathcal U_n^{i1}\)，而 \(\mathcal U_{n+1}^{i1}=f_{c_{n+1}}\mathcal U_n^{i0}\)。字符处处非零，乘以它为可逆线性操作；维数加法公式立即给（3.1）。长度一的两个非空扇区各一维，故 \(d_1=2\)。

累计来源的档案列递推还给
\[
S_{n+1}(\vartheta)\subseteq S_n(\vartheta)\otimes B,
\qquad W_{n+1}\subseteq W_n\otimes B.
\tag{3.3}
\]
约定 \(S_0(\vartheta)=W_0=H_0=\mathbb C\)，则（3.3）也适用于 \(n=0\)。相位因子仅是该递推的标量，不改变此包含。由（3.1），对每个 \(n\le N\) 可取等距 \(F_n:W_n\to K\)，其中 \(\dim K=d_N\)。在子空间 \((F_n\otimes I_B)W_{n+1}\) 上规定
\[
U_n[(F_n\otimes I_B)w]=F_{n+1}w\otimes|0\rangle.
\tag{3.4}
\]
两侧保持相同内积，这个部分等距可扩充为 \(K\otimes B\) 上的酉。由空档案起逐步执行，消耗位每次均清回与全部其余系统乘积的纯空白；编码态与 \(J,M\) 的关联完整保留。每个终端用定理2.1的全域 CPTP 逆完成。此顺序收卷步骤使用已有相干接收方法，[^phase_bcz] 新的容量来自（2.7）—（2.12）的共同相位刚性和（1.6）的实际谱。终端 \(N\) 的下界由定理2.1给出，故前缀共同实现也达到最小值。证明完毕。

**定理 3.2（共同等权相位的精确分类）。** 设 \(c_t=1\) 对所有 \(t\) 成立。若 \(\Theta\) 有 \(m\) 个不同相位，允许 \(m=\infty\) 并约定 \(\min(\infty,r)=r\)，则对 \(n\ge2\)，
\[
\boxed{k_n=
\min\!\left(m,\left\lceil\frac n2\right\rceil\right)
+2\min\!\left(m,\left\lfloor\frac n2\right\rfloor\right)
+\min\!\left(m,\left\lfloor\frac{n-1}2\right\rfloor\right).}
\tag{3.5}
\]
有限 \(m\) 时，从 \(n\ge2m+1\) 起 \(k_n=4m\)；存在一个固定 \(4m\) 维寄存器的门序列服务所有有限前缀。无限 \(\Theta\) 时，\(k_n=2n-1\)，不存在维数统一有界的精确接收寄存器。这里的无限集合无需包含开弧。

证明。此时荷为一的个数，四个非空荷区间恰为
\[
\begin{aligned}
\mathcal Q_n^{00}&=\{0,\ldots,\lfloor(n-1)/2\rfloor\},\\
\mathcal Q_n^{01}=\mathcal Q_n^{10}&=\{1,\ldots,\lfloor n/2\rfloor\},\\
\mathcal Q_n^{11}&=\{2,\ldots,\lfloor(n+1)/2\rfloor\}.
\end{aligned}
\tag{3.6}
\]
最后一个集合在 \(n=2\) 时为空。上界由无相邻一及端点限制得到；将所需个数的一隔位放置并填零，可取得每个列出的整数。对长度 \(r\) 的连续指数区间，\(m\) 个不同单位复数上的评价矩阵在乘去非零行尺度后为 Vandermonde 矩阵，秩为 \(\min(m,r)\)。无限集合可选任意所需数目的不同相位，故秩为 \(r\)。代入（2.1）得到（3.5），并推出两个容量结论。有限 \(m\) 时取同一个 \(K=\mathbb C^{4m}\)，对全部 \(n\) 按（3.4）构造门，门序列无须依赖未来终端。其已知计数与门控制成本仍按定义1.2另计。证明完毕。

**定理 3.3（三次发射时的首个严格容量差）。** 等权情形在 \(n=2\) 对任何非空 \(\Theta\) 都有 \(k_2=3\)。在 \(n=3\)，已知单一相位只需四维，而任意两个不同候选相位已经需要五维。

证明。记 \(a=\sqrt\alpha,b=\alpha\)。长度二的共同支撑恒为 \(\operatorname{span}\{|00\rangle,|01\rangle,|10\rangle\}\)。长度三的四列为
\[
\begin{aligned}
\chi_{00}^{3}(\vartheta)&=a^2|000\rangle+b e^{i\vartheta}|010\rangle,\\
\chi_{01}^{3}(\vartheta)&=ab e^{i\vartheta}|001\rangle,\\
\chi_{10}^{3}(\vartheta)&=a e^{i\vartheta}|100\rangle,\\
\chi_{11}^{3}(\vartheta)&=b e^{2i\vartheta}|101\rangle.
\end{aligned}
\tag{3.7}
\]
单相位给四条独立列；任意两个不同相位使第一行的两份向量独立，另三条射线位于不交支撑，总维数五。物理下界与达到性由定理2.1承担。证明完毕。

## 4. 同一个未知参数的线性与指数边界

**定理 4.1（Zeckendorf 权重使全部合法历史进入接收边界）。** 令 \(F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r\)，取已知权重
\[
c_t=F_{t+1}=1,2,3,5,\ldots.
\tag{4.1}
\]
若同一未知相位的候选集合 \(\Theta\) 无限，则
\[
\boxed{k_n(\Theta,c)=F_{n+2}\quad(n\ge0).}
\tag{4.2}
\]
达到该值的共同可逆支撑就是全部合法词的线性空间 \(\operatorname{span}\{|w\rangle:w\in\mathcal W_n\}\)。即使尚未实际测量任何词，任何满足完整联合恢复合同的接收器，也必须能在这整个子空间上被同一解码器精确反演。

证明。无相邻一的权重和 \(Q_c(w)\) 在长度 \(n\) 的合法词上单射；更精确地，它们恰取每个整数 \(0,\ldots,F_{n+2}-1\) 一次。这是 Zeckendorf 权重的标准唯一表示机制：按最后一位分开，末位零的和由归纳取 \([0,F_{n+1}-1]\)；末位一迫使倒数第二位零，其余和加上 \(F_{n+1}\)，取 \([F_{n+1},F_{n+2}-1]\)。两个区间不交且相邻，初值 \(n=0,1\) 直接成立。此处只将这一既有算术编码用于定义1.1的相位作用，不重建其一般表示理论。

所以每个固定首末扇区内的荷也不重复，（2.5）的每个非零向量仅为单个 \(|w\rangle\) 的正倍数。无限相位集合上的字符独立使 \(W_n\) 等于完整合法词空间。（2.2）给其维数 \(|\mathcal W_n|=F_{n+2}\)，定理2.1给一般 CPTP 下界与达到性。\(n=0\) 的空档案给一维。证明完毕。

**定理 4.2（局部生成维数与参数个数不决定统一接收容量）。** 固定定义1.1的二维活动记忆、二维发出端口及完整联合恢复任务。对 \(n\ge3\)，存在以下三个精确容量：
\[
\begin{array}{c|c}
\text{相位及其已知作用方式}&k_n\\\hline
\text{实际相位已知，任意固定整数权重}&4\\
\text{一个未知相位贯穿全部历史，等权，候选含开弧}&2n-1\\
\text{一个未知相位贯穿全部历史，Zeckendorf 权重，候选含开弧}&F_{n+2}.
\end{array}
\tag{4.3}
\]
后两种来源各只有一个共同未知参数。把候选开弧缩得任意小但保持非退化，仍保留各自的精确容量；把候选限制成一个已知相位则回到第一行。

证明。单相位时，每个非空首末扇区的字符空间一维；\(n\ge3\) 的四个扇区均非空，由（2.1）得到四维。后两行分别来自定理3.2和4.1。不同整数字符在任意非空开弧上都线性独立，故缩小开弧不改变（2.2）。这些均使用同一基础发射等距 \(T\) 与无干预联合来源；附加的相位作用方式及接收器必须同时适用的候选相位族不同。

因此，在这个具体关系过程中，切口需要保留的是实际历史对共同相位的独立作用字符，而不是参数标签的数量。四维已校准接收合同没有同时恢复全部候选相位的量词，故其容量与后两行相容。此结论属于精确恢复；不从秩的跳变推出固定正误差容限下相同的容量下界。不同权重的物理实施费用、持续时间和校准精度亦未由（4.3）比较。证明完毕。

[^phase_ki]: Masato Koashi and Nobuyuki Imoto, *What is Possible Without Disturbing Partially Known Quantum States?*, Physical Review A **66**, 022318 (2002), [arXiv:quant-ph/0101144](https://arxiv.org/abs/quant-ph/0101144), [doi:10.1103/PhysRevA.66.022318](https://doi.org/10.1103/PhysRevA.66.022318)。不扰动态族的结构是标准前置；定理2.1另外计算了本发射装置的首末扇区、跨相位转移行列式及受参考约束的共同可逆支撑。

[^phase_bcz]: Robin Blume-Kohout, Sarah Croke and Michael Zwolak, *Ideal state discrimination with an O(1)-qubit quantum computer*, [arXiv:1201.6625](https://arxiv.org/abs/1201.6625), Section II。相干逐步接收复用其前缀支撑与等距延拓机制；此处的未知相位族及式（2.7）、（3.5）、（4.2）须由对应计算给出。

## 4.99 追加锚
