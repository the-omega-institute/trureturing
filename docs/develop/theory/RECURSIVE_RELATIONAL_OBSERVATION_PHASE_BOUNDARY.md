# 递归关系观察：共同相位谱与接收边界

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

## 5. 正误差下的共同相位容量与荷涨落

**定义 5.1（统一联合近似接收）。** 保留定义1.1—1.2的来源、权限及全部接收资源计数，固定等权 \(c_t=1\) 和全部候选相位 \(\Theta=\mathbb R/(2\pi\mathbb Z)\)。对 \(0<\epsilon<1\)，以 \(k_n^{(\epsilon)}\) 表示满足
\[
\sup_{\vartheta,J,\rho}
\frac12\left\|
(\operatorname{id}_J\otimes\mathcal D_n\mathcal E_n\otimes\operatorname{id}_M)
\Omega_{\vartheta,n}(\rho)-\Omega_{\vartheta,n}(\rho)
\right\|_1\le\epsilon
\tag{5.1}
\]
的最小 \(\dim K\)。上确界取所有有限参考及其允许联合输入，编解码不依赖其中任何未知量。本节优化一个已指定终端的接收；没有要求近似编码同时实现逐位清空或无界前缀服务。

记
\[
p=\alpha^2,\quad \mu=\frac p{1+p},\quad
h_r=\frac{1-(-p)^r}{1+p},\quad
V_n=\sum_{r=1}^{n-1}h_r^2,\quad
b_n=n\mu+\left(\frac12-\mu\right)h_n.
\tag{5.2}
\]
有 \(0<h_r\le1\) 及 \(V_n\le n-1\)。定义
\[
t_{n,\epsilon}=\sqrt{\frac{V_n}{2}\log\frac4{\epsilon^2}},\qquad
\mathcal A_{n,\epsilon}
=\left\{q\in\mathbb Z:
|q-b_n|\le\frac{h_n}{2}+t_{n,\epsilon}\right\},\qquad
r_{n,\epsilon}=\sum_{i,j}|\mathcal Q_n^{ij}\cap\mathcal A_{n,\epsilon}|.
\tag{5.3}
\]
对数取自然底。\(r_{n,\epsilon}\) 计算实际保留的首末扇区与荷，不计算全部具有该荷的词数。

**定理 5.2（保留总荷窗口的联合接收上界）。** 对 \(n\ge2\)，
\[
\boxed{k_n^{(\epsilon)}\le
\min\{2n-1,r_{n,\epsilon}+1\}
\le\min\{2n-1,8t_{n,\epsilon}+9\}.}
\tag{5.4}
\]
达到第一项中的近似上界时，保留每个 \((i,j,q)\) 的完整相干向量 \(g_{ijq}\)，另用一维记录失败分支。这里没有把实际相干词测量成经典词档案。

证明。对固定首位 \(i\)，在计算基中读取档案词时，其概率是 \(A(w)^2\)。由（1.1），后续位 \(X_t\) 是转移矩阵
\[
P=\begin{pmatrix}\alpha&p\\1&0\end{pmatrix}
\tag{5.5}
\]
的二态 Markov 链，\(X_1=i\)。相位只改变振幅的相位，不改变这些概率。设 \(S_n=\sum_{t=1}^nX_t\)。条件期望递推给
\[
\mathbb E_iX_t=\mu+(i-\mu)(-p)^{t-1},\qquad
\mathbb E_iS_n=n\mu+(i-\mu)h_n.
\tag{5.6}
\]
所以两个初态均值与 \(b_n\) 的距离都是 \(h_n/2\)。

逐位揭示 \(X_2,\ldots,X_n\)，取终值 \(S_n\) 的 Doob 鞅。在已知到第 \(t-1\) 位的同一历史下，若 \(X_t\) 的两个取值均可达，它们所给条件期望之差为
\[
1-p+p^2-\cdots+(-p)^{n-t}=h_{n-t+1}.
\tag{5.7}
\]
若只有一个取值可达，差为零。因此第 \(t\) 个鞅增量的条件取值区间宽度至多 \(h_{n-t+1}\)。标准条件 Hoeffding 指数估计逐步相乘并优化指数参数，给出 Azuma—Hoeffding 双尾界[^phase_azuma]
\[
\Pr_i\{|S_n-\mathbb E_iS_n|\ge u\}
\le2\exp(-2u^2/V_n).
\tag{5.8}
\]
由（5.3）、（5.6）和（5.8），对两个 \(i\) 都有
\[
\Pr_i\{S_n\notin\mathcal A_{n,\epsilon}\}
\le\delta:=\epsilon^2/2.
\tag{5.9}
\]

令 \(P_{\mathcal A}\) 投影到所保留的 \(g_{ijq}\) 的线性包，其秩是 \(r_{n,\epsilon}\)。由于不同首位扇区正交，
\[
T_{\vartheta,n}^*[(I-P_{\mathcal A})\otimes I_M]T_{\vartheta,n}
=\operatorname{diag}\bigl(
\Pr_0\{S_n\notin\mathcal A_{n,\epsilon}\},
\Pr_1\{S_n\notin\mathcal A_{n,\epsilon}\}\bigr)
\preceq\delta I_M.
\tag{5.10}
\]
这里相同首位内的不同末位及荷扇区也正交，且 \(\|m_j\|=1\)，故对角项正是所列概率。式（5.10）对任意初始相干、混合及外部参考同时控制失败质量，未把初始联合态替换为独立或对角来源。

取保留子空间到 \(\mathbb C^{r_{n,\epsilon}}\) 的等距 \(F\)，另添正交旗标 \(|\bot\rangle\)，定义全域通道
\[
\mathcal E(X)=FP_{\mathcal A}XP_{\mathcal A}F^*
+\operatorname{Tr}[(I-P_{\mathcal A})X]|\bot\rangle\langle\bot|.
\tag{5.11}
\]
解码在成功块使用逆等距，在失败块输出任意固定档案密度矩阵；成功、失败块之间的非对角项置零。这些映射完全正且保迹，旗标包含在 \(K\) 内。

先把初始联合态纯化，并把纯化空间归入参考。对实际纯目标 \(|\psi\rangle\)，若失败质量为 \(d\le\delta\)，恢复态的成功项是
\((P_{\mathcal A}\otimes I)|\psi\rangle\langle\psi|(P_{\mathcal A}\otimes I)\)，其与目标的重叠为 \((1-d)^2\)，失败项再贡献非负重叠。纯目标的迹距离—保真度不等式[^phase_fvg]因而给
\[
\frac12\|\rho_{\rm recovered}-|\psi\rangle\langle\psi|\|_1
\le\sqrt{1-(1-d)^2}\le\sqrt{2\delta}=\epsilon.
\tag{5.12}
\]
丢弃额外纯化参考不会增加迹距离，于是（5.1）成立。

窗口半宽为 \(h_n/2+t_{n,\epsilon}\)，其中的整数个数至多 \(h_n+2t_{n,\epsilon}+1\le2t_{n,\epsilon}+2\)。四扇区加旗标遂给 \(r_{n,\epsilon}+1\le8t_{n,\epsilon}+9\)。也可直接用定理3.2的 \(2n-1\) 维精确编码，取两者较小得到（5.4）。证明完毕。

**定理 5.3（任意物理编码的相位区分下界）。** 对 \(n\ge4\)，
\[
\boxed{k_n^{(\epsilon)}\ge
\frac{1-\epsilon}{2\sqrt\pi}
\sqrt{\alpha^3\left\lfloor\frac{n-1}{3}\right\rfloor}.}
\tag{5.13}
\]
下界允许任意满足定义5.1的 CPTP 编解码，不限制为投影、荷窗口或相位协变通道。

证明。只取合法 Bell 输入，其实际联合纯态为（2.9）。把不可访问的 \(JM\) 合记为四维 \(R\)。按总荷分组有
\[
|\Psi_\vartheta\rangle=\sum_qe^{iq\vartheta}|v_q\rangle,
\qquad \langle v_q,v_{q'}\rangle=0\quad(q\ne q').
\tag{5.14}
\]
对全圆相位取数学平均，得到
\[
\overline\Omega=\frac1{2\pi}\int_{-\pi}^{\pi}
|\Psi_\vartheta\rangle\langle\Psi_\vartheta|\,d\vartheta
=\sum_q|v_q\rangle\langle v_q|,
\qquad
\|\overline\Omega\|_\infty=\max_q\Pr\{S_n=q\}.
\tag{5.15}
\]
右侧是（5.5）中初位均匀的链；这是实际 Bell 来源的荷分布，不是给接收器增加相位读数或准备权限。

先估计此分布的最大点质量。置 \(z=e^{it}\)、\(A(t)=P\operatorname{diag}(1,z)\)，并用最大绝对行和范数。直接相乘得
\[
A(t)^2=
\begin{pmatrix}
\alpha^2(1+z)&\alpha^3z\\
\alpha&\alpha^2z
\end{pmatrix}.
\tag{5.16}
\]
令 \(c=|\cos(t/2)|\)。两行绝对和分别为 \(1-2\alpha^2(1-c)\) 和一；再左乘 \(A(t)\)，逐行三角不等式给
\[
\|A(t)^3\|_\infty
\le1-2\alpha^3(1-c)
\le1-\alpha^3\sin^2(t/2),\qquad
\|A(t)\|_\infty=1.
\tag{5.17}
\]
取 \(m=\lfloor(n-1)/3\rfloor\ge1\)。荷的特征函数是
\(\frac12(1,e^{it})A(t)^{n-1}(1,1)^{\mathsf T}\)，故其绝对值至多
\(\exp[-m\alpha^3\sin^2(t/2)]\)。整数 Fourier 反演和 \(\sin(|t|/2)\ge|t|/\pi\) 对 \(|t|\le\pi\) 给
\[
\max_q\Pr\{S_n=q\}
\le\frac1{2\pi}\int_{-\pi}^{\pi}
 e^{-m\alpha^3\sin^2(t/2)}\,dt
\le\frac{\sqrt\pi}{2\sqrt{m\alpha^3}}=:\beta_n.
\tag{5.18}
\]

现取任何 \(k\) 维接收器，令其编码后的 \(KR\) 态为 \(\tau_\vartheta\)，恢复态为 \((\mathcal D\otimes\operatorname{id}_R)(\tau_\vartheta)\)。由 \(0\preceq\tau_\vartheta\preceq I_{KR}\)，以及解码对偶的正性，其目标重叠满足
\[
f_\vartheta
\le\operatorname{Tr}\bigl[(\mathcal D^*\otimes\operatorname{id}_R)
(|\Psi_\vartheta\rangle\langle\Psi_\vartheta|)\bigr].
\tag{5.19}
\]
（5.1）对目标纯态投影这个效果给 \(f_\vartheta\ge1-\epsilon\)。积分（5.19），再用（5.15）、（5.18）及 \(\mathcal D^*(I)=I_K\)，得到
\[
1-\epsilon\le
\operatorname{Tr}[(\mathcal D^*\otimes\operatorname{id}_R)(\overline\Omega)]
\le\beta_n\operatorname{Tr}I_{KR}=4k\beta_n.
\tag{5.20}
\]
代入 \(\beta_n\) 即得（5.13）。保留的四维参考已明确计入此下界估计，没有把它当成可访问的编码寄存器。证明完毕。

**定理 5.4（同一来源的精确容量与正误差容量分离）。** 对定义5.1的同一来源及任意固定 \(0<\epsilon<1\)，存在只依赖 \(\epsilon\) 的正常数 \(a_\epsilon,b_\epsilon\)，使全部 \(n\ge4\) 满足
\[
\boxed{a_\epsilon\sqrt n\le k_n^{(\epsilon)}\le b_\epsilon\sqrt n,
\qquad k_n^{(0)}=2n-1.}
\tag{5.21}
\]

证明。上界由（5.4）及 \(V_n\le n-1\) 得到；下界由（5.13）及 \(\lfloor(n-1)/3\rfloor\ge n/6\) 对 \(n\ge4\) 成立得到；精确值是定理3.2。以 qubit 数 \(\lceil\log_2 k\rceil\) 计量时，前者为 \(\frac12\log_2n+O_\epsilon(1)\)，后者为 \(\log_2n+O(1)\)。未知量子时钟的频率投影与近似压缩已有先例；[^phase_clock] 此处由相关合法词的（5.6）—（5.10）和三步转移消去（5.16）—（5.18），在同一不可访问参考与活动记忆的联合合同中取得两侧界。

因此，精确容量计算的是全部独立相位字符，固定正误差容量则可只保留承载主要概率质量的相干荷方向。式（5.21）不改变第2—4节的零误差结算，也不推出无限深度顺序接收的同一误差保证；窗口在各终端的截断误差尚未证明可在同一在线接收过程中无积累地拼接。证明完毕。

[^phase_azuma]: Kazuoki Azuma, *Weighted sums of certain dependent random variables*, Tohoku Mathematical Journal **19** (1967), 357–367，[doi:10.2748/tmj/1178243286](https://doi.org/10.2748/tmj/1178243286)。式（5.8）使用条件取值区间宽度版本的标准鞅指数估计；本源的均值、区间宽度及量子联合失败算子由（5.6）、（5.7）、（5.10）给出。

[^phase_fvg]: Christopher A. Fuchs and Jeroen van de Graaf, *Cryptographic Distinguishability Measures for Quantum-Mechanical States*, IEEE Transactions on Information Theory **45** (1999), 1216–1227，[doi:10.1109/18.761271](https://doi.org/10.1109/18.761271)，[arXiv:quant-ph/9712042](https://arxiv.org/abs/quant-ph/9712042)。式（5.12）使用其中的迹距离与保真度关系，并将目标取为联合纯态。

[^phase_clock]: Yuxiang Yang, Giulio Chiribella and Masahito Hayashi, *Compression for Qubit Clocks*, [arXiv:2209.06519](https://arxiv.org/abs/2209.06519)。该文的频率投影用于独立同分布 qubit 时钟的渐近近似压缩；本节的来源为（1.1）的相关发射，误差合同为（5.1），上下界均按该来源重新计算。

## 5.99 追加锚

## 6. 共同存活事件下的全部前缀接收

**定义 6.1（固定时域的同一被动接收器）。** 保留定义5.1的等权、全圆相位和全部初始联合来源，预先给定有限时域 $N\ge2$ 。接收器从固定纯态开始，每步只以一个已知 CPTP 映射作用于同一寄存器 $K$ 与最新发出位，之后把该位置成与其余系统独立的纯空白并丢弃；无持久辅助标签留在 $K$ 之外。源的活动记忆与参考均不可访问，也没有向源反馈。门可依赖 $N,\epsilon$ 和当前步数，不能依赖未知相位或输入。若在任一事先指定的 $n\le N$ 选择停止，均有解码器满足（5.1）。最小 $\dim K$ 记为 $k_{\le N}^{(\epsilon)}$ 。

此合同只在所选终端解码，不要求解码后保留一份档案副本并原样继续，也不要求保持任意中途干预下的过程距离。计数、门控制、瞬时空白及丢弃环境的成本按定义1.2另计。允许的是固定相干基下的普通 CPTP 操作；未知 $\vartheta$ 不附加所有门必须相位协变的超选择限制。保持不可访问环境关联的局部压缩是既有任务；[^phase_tensor] 本节进一步要求同一逐步接收实现与共同误差预算。

置

$$
s_{N,\epsilon}=\sqrt{\frac{N-1}{2}\log\frac4{\epsilon^2}},\qquad
R_{N,\epsilon}=\frac{s_{N,\epsilon}+1}{1+p}.
\tag{6.1}
$$

称合法词 $w\in\mathcal W_n$ 存活，若其每个前缀都满足

$$
\left|\sum_{t=1}^kw_t-k\mu\right|\le R_{N,\epsilon}
\quad(1\le k\le n).
\tag{6.2}
$$

令 $\mathcal W_n^{\rm s}$ 为存活词集；空词存活。对非空首末荷扇区定义

$$
g_{ijq}^{n,\rm s}
=\sum_{\substack{w\in\mathcal W_n^{\rm s}\cap\mathcal W_n^{ij}\\
\sum_tw_t=q}}A(w)|w\rangle,
\qquad W_n^{\rm s}=\operatorname{span}\{g_{ijq}^{n,\rm s}\},
\qquad W_0^{\rm s}=\mathbb C.
\tag{6.3}
$$

空扇区不计入生成集， $d_n^{\rm s}=\dim W_n^{\rm s}$ 。这是保留全部过去未越界条件的子空间，不是各终端独立选择的荷窗口。

**定理 6.2（单个接收器的平方根容量与共同误差）。** 对定义6.1的合同，

$$
\boxed{k_{\le N}^{(\epsilon)}
\le\min\left\{2N-1,1+\max_{0\le n\le N}d_n^{\rm s}\right\}
\le\min\{2N-1,8R_{N,\epsilon}+5\}.}
\tag{6.4}
$$

同一个接收器在每个可选终端 $n\le N$ 的完整联合半迹距离均至多 $\epsilon$ ，误差预算不乘以 $N$ 。对每个固定 $0<\epsilon<1$ ，有

$$
k_{\le N}^{(\epsilon)}\asymp_\epsilon\sqrt N\qquad(N\ge4).
\tag{6.5}
$$

证明。先在（5.5）的实际词链上固定任一初位，令

$$
Y_t=X_t-\mu,\qquad
\eta_t=Y_t+pY_{t-1}\quad(t\ge2),\qquad
M_k=\sum_{t=2}^k\eta_t,\quad M_1=0.
\tag{6.6}
$$

由 $\mathbb E[Y_t\mid X_1,\ldots,X_{t-1}]=-pY_{t-1}$ ， $M_k$ 是鞅，每个增量的条件取值区间宽度至多一。直接求和得

$$
(1+p)(S_k-k\mu)=M_k+Y_1+pY_k,
\qquad -p\le Y_1+pY_k\le1.
\tag{6.7}
$$

条件 Hoeffding 估计使
 $\exp[\lambda M_k-(k-1)\lambda^2/8]$
为非负超鞅。若 $M_k$ 在 $k\le N$ 首次达到 $s>0$ ，该时刻超鞅至少为 $\exp[\lambda s-(N-1)\lambda^2/8]$ 。对首次到达时刻截停并取期望，得上尾概率至多 $\exp[-\lambda s+(N-1)\lambda^2/8]$ ；负尾同理。取 $\lambda=4s/(N-1)$ ，得到

$$
\Pr_i\left\{\max_{1\le k\le N}|M_k|\ge s\right\}
\le2e^{-2s^2/(N-1)}.
\tag{6.8}
$$

这是标准非负超鞅最大估计在本链上的应用。由（6.1）、（6.7），只要（6.2）曾经失败，必有 $|M_k|>s_{N,\epsilon}$ 。因此对两个初位同时有

$$
\Pr_i\{\text{时域内至少一次不存活}\}\le\epsilon^2/2.
\tag{6.9}
$$

这里估计的是同一个实际路径事件，没有把各终端失败概率相加。

现构造物理接收。每条存活历史的前缀仍存活。记 $a_{bj}=(m_b)_j$ ，把带外或空扇区向量视为零，则

$$
g_{ijq}^{n+1,\rm s}
=\mathbf1_{\{|q-(n+1)\mu|\le R_{N,\epsilon}\}}
\sum_{b=0}^1a_{bj}\,g_{ib,q-j}^{n,\rm s}\otimes|j\rangle
\quad(n\ge1).
\tag{6.10}
$$

故 $W_{n+1}^{\rm s}\subseteq W_n^{\rm s}\otimes B$ ， $n=0$ 也由一维空档案成立。等权相位在每个此类向量上仅给标量 $e^{iq\vartheta}$ ，所有 $W_n^{\rm s}$ 均不依赖实际相位。

取
 $K=K_{\rm g}\oplus\mathbb C|\bot\rangle$ ，其中
 $\dim K_{\rm g}=\max_{n\le N}d_n^{\rm s}$ ，并选等距
 $F_n:W_n^{\rm s}\to K_{\rm g}$ 。将 $`F_n^*`$ 在其编码像的正交补上置零，寄存器初态取 $F_0(1)$ 。令 $P_{n+1}^{\rm s}$ 是到 $W_{n+1}^{\rm s}$ 的投影。在 $K\otimes B$ 上定义成功算子

$$
A_n=F_{n+1}P_{n+1}^{\rm s}(F_n^*\otimes I_B),
\qquad
\mathcal C_n(X)=A_nXA_n^*
+\operatorname{Tr}[(I-A_n^*A_n)X]|\bot\rangle\langle\bot|.
\tag{6.11}
$$

包含关系使 $A_n$ 是两个相同维数子空间之间的部分等距，故 $`A_n^*A_n`$ 是投影， $\mathcal C_n$ 为全域 CPTP 映射。把其输出张量 $|0\rangle\langle0|_B$ 就将已消费位置为独立纯空白。旧失败旗标满足 $`F_n^*|\bot\rangle=0`$ ，所以失败分支吸收。整个操作只需要当前 $K$ 与新位；被丢弃环境未作为隐含接收记忆保留。

令 $Q_n^{\rm s}$ 是档案空间中选取全部存活计算基词的投影。原来源的存活部分满足

$$
(Q_n^{\rm s}\otimes I_M)T_{\vartheta,n}|i\rangle
=\sum_{j,q}e^{iq\vartheta}g_{ijq}^{n,\rm s}\otimes m_j.
\tag{6.12}
$$

据此归纳（6.11）：连续成功的未归一化联合分支恰为原来源经 $Q_n^{\rm s}$ 投影，再由 $F_n$ 编码的状态。其余分支落在 $|\bot\rangle$ ；没有将某次失败后重新进入带内的历史当作成功。尤其 $P_{n+1}^{\rm s}$ 在实际成功来源上所做的操作，与追加位后检查（6.2）一致，而非另一次不相关的状态估计。

与（5.10）相同的首位正交性给

$$
T_{\vartheta,n}^*[(I-Q_n^{\rm s})\otimes I_M]T_{\vartheta,n}
=\operatorname{diag}(\delta_{0,n},\delta_{1,n})
\preceq(\epsilon^2/2)I_M,
\tag{6.13}
$$

其中 $\delta_{i,n}$ 是截至第 $n$ 步曾越界的概率，由（6.9）统一控制。这覆盖全部相位、初始相干及有限参考。终端解码对好块用 $`F_n^*`$ ，对失败及未使用编码空间输出固定态。纯化后，成功项与目标的重叠至少为 $(1-\epsilon^2/2)^2$ ，其余项为正；（5.12）的证明给联合半迹距离至多 $\epsilon$ 。

在任一时刻，存活荷只落在长度 $2R_{N,\epsilon}$ 的区间，四首末扇区故给 $d_n^{\rm s}\le4(2R_{N,\epsilon}+1)$ ； $n=0$ 的一维也满足此界。加一维失败旗标得（6.4）的第二项。也可使用定理3.1—3.2的 $2N-1$ 维精确接收器，得到较小值。

最后，无反馈的接收操作与其后的源发射作用在不交系统上，可以交换次序。因此整个时域接收在终端等价于只作用于完整档案的一个 CPTP 编码，必须满足定理5.3在 $n=N$ 的下界。结合（6.1）、（6.4）得（6.5）。门序列依赖预定 $N$ ；这些量词没有给出一个与终端时域无关的无限门序列。证明完毕。

[^phase_tensor]: Ge Bai, Yuxiang Yang and Giulio Chiribella, *Quantum Compression of Tensor Network States*, New Journal of Physics **22**, 043015 (2020)，[arXiv:1904.06772](https://arxiv.org/abs/1904.06772)。§II.A给出参数无关精确压缩；§V式（35）—（36）及命题4处理不可访问环境关联；附录B命题6处理未知共同变换。这些是第1—4节任务与支撑压缩的一般先例；本卷的字符秩及显式容量来自对应来源计算。第2节行列式还保证整个共同支撑代数被同一通道固定，这比单独得到最小维数更强；它不是一般局部压缩容量下界的必要方法。

## 6.99 追加锚


## 7. 固定接收门与必须计入的控制记忆

**定义 7.1（同一固定门的精确空白接收）。** 本节把相位固定为已知零值，保持定义1.1的同一发射源、全部初始参考—记忆联合态及被动接收权限。预先给定整数 $`N\ge1`$，接收寄存器 $`K`$ 从独立纯态 $`|k_0\rangle`$ 开始。每一步在 $`K`$ 与最新发出的 $`B`$ 上施加同一个酉 $`U`$，随后 $`B`$ 必须精确成为与全部其余系统乘积的固定纯空白 $`|0\rangle`$。此要求对全部初态及每个 $`n\le N`$ 成立。所有持久量子记忆、钟和控制标签均计入 $`K`$；没有额外丢弃环境，没有按发射次数另选门，也不访问活动 $`M`$。允许在所选终端以依赖终端编号的解码器恢复档案。记最小 $`\dim K`$ 为 $`a_N`$。

这里固定的是接收门，仍由源提供有序的新端口。本节不声称实现了没有外部供能或事件供给的连续时间自主机器。它比较的是相同来源与精确联合任务下，两种门控制合同的存储成本。每步纯空白允许反向运行接收酉，将空白依次恢复为原档案；因而上述合同确实保留全部联合态，而不只是源的边缘。

**引理 7.2（有限酉期望不能非恒定地收敛）。** 若 $`V`$ 是有限维空间上的酉，$`\xi`$ 是向量，$`A`$ 是算子，且 $`\langle V^n\xi,AV^n\xi\rangle`$ 在 $`n\to\infty`$ 时收敛，则这个序列恒定。

证明。酉的有限谱分解把该序列写成 $`\sum_{z\in Z}c_z z^n`$，其中 $`Z`$ 是有限个不同单位复数。设极限为 $`L`$，对任意 $`z\ne1`$，序列减去 $`L`$ 后乘 $`z^{-n}`$ 的 Cesàro 平均趋于零；有限几何和同时给该平均趋于 $`c_z`$。因此所有非一频率的系数为零，原序列只剩常数项。该论证是有限酉演化的标准谱机制。

**定理 7.3（精确无限接收不存在有限固定门记忆）。** 不存在有限维 $`K`$ 与同一个 $`U`$，使定义7.1的空白要求对所有有限 $`n`$ 同时成立。

证明。按固定因子置换，将发射加接收的一步写为等距

$$
A=\Sigma_{\rm out}(I_M\otimes U)\Sigma_{\rm in}(T\otimes I_K):M\otimes K\longrightarrow B\otimes M\otimes K,
\qquad
W=(\langle0|_B\otimes I)A,\quad
Z=(\langle1|_B\otimes I)A.
\tag{7.1}
$$

这里 $`\Sigma_{\rm in}`$ 把发射后的 $`B,M,K`$ 次序换为 $`M,K,B`$，$`\Sigma_{\rm out}`$ 再把接收后的 $`M,K,B`$ 换为 $`B,M,K`$。于是

$$
W^*W+Z^*Z=I_{M\otimes K}.
\tag{7.2}
$$

置 $`L=M\otimes\mathbb C|k_0\rangle`$。每步精确纯空白给 $`ZW^jL=0`$。令 $`\mathcal R=\operatorname{span}_{j\ge0}W^jL`$；这是有限维、前向不变的子空间，$`Z`$ 在其上恒零。由（7.2），$`W`$ 在 $`\mathcal R`$ 上等距；有限维及前向不变性使其限制成为 $`\mathcal R`$ 上的酉。

另一方面，接收酉只作用于已发出的位与 $`K`$，所以活动 $`M`$ 的边缘仍严格按原通道 $`E`$ 演化。取实际允许初态 $`|0\rangle\langle0|_M`$，定义

$$
q_n=\operatorname{Tr}\!\left[|1\rangle\langle1|\,E^n(|0\rangle\langle0|)\right],
\qquad p=\alpha^2,\quad \mu=\frac{p}{1+p}.
\tag{7.3}
$$

由 $`E(X)=X_{00}|m_0\rangle\langle m_0|+X_{11}|m_1\rangle\langle m_1|`$ 得

$$
q_0=0,\qquad q_{n+1}=p(1-q_n),\qquad
q_n=\mu\bigl(1-(-p)^n\bigr).
\tag{7.4}
$$

该序列收敛且不恒定。但在 $`\mathcal R`$ 上，它又是初向量 $`|0\rangle_M|k_0\rangle_K`$ 对可观测量 $`|1\rangle\langle1|_M\otimes I_K`$ 的有限酉期望，与引理7.2矛盾。证明完毕。

**定理 7.4（有限时域的线性记忆代价）。** 令 $`d_N=\dim S_N`$，其中 $`S_N`$ 是已知相位的实际档案支撑，故 $`d_1=2,d_2=3,d_N=4`$（$`N\ge3`$）。则对 $`N\ge2`$，

$$
\boxed{
\max\left\{d_N,\left\lceil\frac{N+2}{2}\right\rceil\right\}
\le a_N\le4N-2.
}
\tag{7.5}
$$

特别地，$`a_N=\Theta(N)`$，而允许接收门按已知步数改变时，同一个四维寄存器足以覆盖全部有限终端。

证明。先证新的下界。对任一定义7.1的装置使用（7.1），置

$$
\mathcal R_t=\operatorname{span}\{W^jL:0\le j\le t\},\qquad
\dim L=2.
\tag{7.6}
$$

前 $`N`$ 步纯空白给 $`Z\mathcal R_{N-1}=0`$，故 $`W`$ 在 $`\mathcal R_{N-1}`$ 上等距。若某个 $`0\le t\le N-1`$ 满足 $`\mathcal R_t=\mathcal R_{t+1}`$，则 $`W\mathcal R_t\subseteq\mathcal R_t`$，其限制因有限维而为酉，并且 $`Z\mathcal R_t=0`$。于是这个装置从 $`L`$ 开始的全部后续步骤自动仍为纯空白，违背定理7.3。这里未来空白由已保证步内的平台推出，没有把有限合同擅自延长。

所以 $`\mathcal R_0\subsetneq\cdots\subsetneq\mathcal R_N`$，每次至少增加一维，从而

$$
2\dim K=\dim(M\otimes K)\ge\dim\mathcal R_N\ge N+2.
\tag{7.7}
$$

另一项 $`a_N\ge d_N`$ 是既有参考完整档案恢复的切口下界：整个接收装置是作用于档案一侧的编码，反向门序列为解码，故可直接应用本卷已知相位容量结果。

现证上界。取互相正交的时刻扇区

$$
K=\bigoplus_{n=0}^{N}K_n,\qquad
\dim K_n=d_n,\qquad F_n:S_n\longrightarrow K_n\text{ 为等距同构}.
\tag{7.8}
$$

初态取 $`F_0(1)`$。由于 $`S_{n+1}\subseteq S_n\otimes B`$，在 $`K\otimes B`$ 的子空间 $`(F_n\otimes I_B)S_{n+1}`$ 上规定

$$
U\bigl((F_n\otimes I_B)s\bigr)=F_{n+1}s\otimes|0\rangle,
\qquad 0\le n<N.
\tag{7.9}
$$

对不同 $`n`$，输入分别位于正交的 $`K_n\otimes B`$，输出分别位于正交的 $`K_{n+1}\otimes\mathbb C|0\rangle`$；每一块本身也等距。因此这些规定共同组成一个子空间等距，可以延拓为整个 $`K\otimes B`$ 上的同一个酉。归纳即得每个前缀的联合编码与纯空白，所有控制扇区已计入 $`K`$。最后

$$
\dim K=\sum_{n=0}^{N}d_n=1+2+3+4(N-2)=4N-2
\tag{7.10}
$$

给出上界。证明完毕。

本节将有限酉谱、可达子空间平台及原来源的严格收缩组合到同一个接收合同；有限封闭系统不能精确承载非平凡无限耗散的机制属于成熟原理，不在这里宣称原创。经典有限幂酉扩张已有线性维数及无限全幂障碍；[^phase_dilation] 其合同是算子幂的角压缩，本节则额外要求固定局部门接收、纯空白与全部来源联合态，不能直接把那一维数公式当作这里的 $`a_N`$。线性上下界没有确定 $`a_N`$ 的精确值。一般 CPTP 接收可以向新环境丢弃信息，近似纯空白允许每步误差；二者都破坏（7.2）中从实际空白得到精确等距的关键条件，需另行求界。上述维数不是物理面积、能量、计时精度或实际历时。

[^phase_dilation]: Eli Levy and Orr Moshe Shalit, *Dilation theory in finite dimensions: the possible, the impossible and the unknown*, Rocky Mountain Journal of Mathematics **44**(1), 203–221 (2014)，[arXiv:1012.4514v2](https://arxiv.org/html/1012.4514v2)，[DOI:10.1216/rmj-2014-44-1-203](https://doi.org/10.1216/rmj-2014-44-1-203)。定理1.1后的全幂无限维说明、定理1.3及推论2.2分别给有限幂构造与最小维数；其角压缩合同与本节不同。

四维已知相位预测边界与这里的线性固定门记忆并不矛盾。前者允许按步数供应不同接收门，后者把选择门所需的持久控制也纳入同一固定关系实现。把时间写进静态结构时，可以不外加一个演化参数；要由同一装置持续执行这些关系，控制信息仍须有明确归属。

## 追加锚（本行以下为增补区）
