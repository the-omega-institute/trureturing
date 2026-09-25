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


## 8. 精确固定门容量与共同初始化的分界

本节保持定义7.1的全部资源与来源条件，把定理7.4的线性界收紧为精确值。随后单独改变初始化条件，检验哪些联合关系承担了这份容量。

**约定 8.1（实际系数域与空白行块）。** 写 $`a=\sqrt\alpha`$、$`b=\alpha`$，故 $`a,b>0`$。接收寄存器初态记为单位向量 $`e`$。对两个初始记忆基态，记前 $`j`$ 步接收后的纯联合向量为

$$
\Psi_j^i=|0\rangle_M u_j^i+|1\rangle_M v_j^i,
\qquad
(u_0^0,v_0^0)=(e,0),\quad
(u_0^1,v_0^1)=(0,e).
\tag{8.1}
$$

这里 $`u_j^i,v_j^i\in K`$。定义实际系数子空间

$$
H_t=\operatorname{span}\{u_j^i:0\le j\le t,\ i=0,1\},\qquad
G_t=\operatorname{span}\{v_j^i:0\le j\le t,\ i=0,1\}.
\tag{8.2}
$$

它们由同一实际装置和全部已声明输入生成，允许彼此相交。对 $`K\otimes\mathcal B`$ 上的同一个接收酉 $`U`$，定义其空白与非空白行块

$$
A=(I_K\otimes\langle0|)U(I_K\otimes|0\rangle),\qquad
B=(I_K\otimes\langle0|)U(I_K\otimes|1\rangle),
\tag{8.3}
$$

以及将左侧 $`\langle0|`$ 换成 $`\langle1|`$ 所得的 $`Z_0,Z_1`$。本节把新发出位的二维空间记为 $`\mathcal B`$，以区别接收算子 $`B:K\to K`$。

**引理 8.2（实际纯空白强制正交等距域）。** 若前 $`N`$ 步满足定义7.1，令 $`t=N-1`$，则 $`A|_{H_t}`$、$`B|_{G_t}`$ 分别等距，且

$$
A H_t\perp B G_t.
\tag{8.4}
$$

实际轨道的系数更新为

$$
u_j^i=aAu_{j-1}^i+Bv_{j-1}^i,\qquad
v_j^i=bAu_{j-1}^i\qquad(1\le j\le N).
\tag{8.5}
$$

证明。对任一实际向量 $`|0\rangle u+|1\rangle v`$，发射给出 $`|0\rangle_B m_0\otimes u+|1\rangle_B m_1\otimes v`$。接收后非空白部分的系数是 $`m_0\otimes Z_0u+m_1\otimes Z_1v`$。两个记忆向量 $`m_0,m_1`$ 线性独立，所以实际纯空白要求分别强制 $`Z_0u=0`$、$`Z_1v=0`$。对所有来源基态与 $`j<N`$ 取线性张成，得到 $`Z_0H_t=0`$、$`Z_1G_t=0`$。

于是 $`U(x\otimes|0\rangle)=Ax\otimes|0\rangle`$ 对 $`x\in H_t`$ 成立，另一块对 $`y\in G_t`$ 同理。酉性分别保持范数，并把原来正交的两个输入块送到正交输出块，给（8.4）。展开 $`m_0=a|0\rangle+b|1\rangle`$、$`m_1=|0\rangle`$ 得（8.5）。证明完毕。

该推导没有把所有 $`M\otimes H_t`$ 当作可自由准备的来源。是记忆输出向量的线性独立性，把同一实际联合态上的空白要求分解成了两个系数域上的约束。

**定理 8.3（精确最小固定门容量）。** 对定义7.1的同一已知相位来源、独立纯接收初态及全部参考完整输入，

$$
\boxed{a_1=2,\qquad a_N=2N-1\quad(N\ge2).}
\tag{8.6}
$$

证明。先证下界。固定 $`t=N-1\ge1`$，将等距 $`A|_{H_t}:H_t\to K`$ 的伴随拉回到 $`H_t`$，定义

$$
J_t=(A|_{H_t})^*\,\iota_{H_t}:H_t\longrightarrow H_t,
\tag{8.7}
$$

其中 $`\iota_{H_t}`$ 是到 $`K`$ 的包含映射。由（8.4）、（8.5），

$$
J_tu_j^i=a\,u_{j-1}^i\qquad(1\le j\le t).
\tag{8.8}
$$

写 $`y_j=u_j^1`$、$`x_j=u_j^0`$。有 $`y_0=0`$、$`y_1=Be\ne0`$，因此

$$
J_ty_1=0,\qquad J_ty_j=ay_{j-1}\ (2\le j\le t),\qquad
J_t^t x_t=a^t e\ne0.
\tag{8.9}
$$

向量 $`y_1,\ldots,y_t`$ 线性独立：若有线性关系，对其中最高非零指标 $`r`$ 施加 $`J_t^{r-1}`$，只留下非零倍数的 $`y_1`$，矛盾。$`J_t^t`$ 又消灭这整条链，却不消灭 $`x_t`$，所以 $`x_t`$ 不在其张成内。因此

$$
\dim H_t\ge t+1.
\tag{8.10}
$$

同样论证用于 $`t-1`$ 给 $`\dim H_{t-1}\ge t`$；$`t=1`$ 时直接用 $`H_0=\mathbb Ce`$。因 $`b\ne0`$，（8.5）还给 $`G_t\supseteq A H_{t-1}`$，从而 $`\dim G_t\ge t`$。两像正交且各自等距，故

$$
\dim K\ge\dim H_t+\dim G_t\ge2t+1=2N-1.
\tag{8.11}
$$

$`N=1`$ 时两个实际域均为 $`\mathbb Ce`$，两个等距像必须正交，直接得到 $`\dim K\ge2`$。

再构造达到者。对 $`N\ge2`$ 取固定空间 $`K=\mathbb C^{2N-1}`$，选正交单位向量 $`e,f`$。先在两个域 $`H_0=G_0=\mathbb Ce`$ 上规定部分映射 $`Ae=e`$、$`Be=f`$。保持两个部分映射各自等距且像正交，随后按以下有限递推延拓；构造中不要求它们在整个 $`K`$ 上等距。

每一轮先用已经定义的映射和（8.5）计算下一对轨道。首步满足 $`\Psi_1^0=a\Psi_0^0+b\Psi_0^1`$；每轮延拓保持旧域上的作用，所以逐步归纳得到

$$
\Psi_j^0=a\Psi_{j-1}^0+b\Psi_{j-1}^1\qquad(j\ge1)
\tag{8.12}
$$

在构造到的所有层成立。这一步不预设尚未构成的全域酉。于是，对 $`t\ge1`$，

$$
H_t=\operatorname{span}\{e,u_1^1,\ldots,u_t^1\},\qquad
G_t=\operatorname{span}(e,A H_{t-1})=A H_{t-1},
\tag{8.13}
$$

后一等式用了 $`Ae=e`$，并且 $`b\ne0`$。故 $`\dim H_t\le t+1`$、$`\dim G_t\le t`$。这些域先由已经算出的向量确定，再延拓部分映射，不存在用未来映射定义其自身当前域的循环。

具体地，若两个旧域维数分别为 $`r_0,r_1`$，本轮新增正交方向数为 $`\Delta_0,\Delta_1`$，则在 $`t\le N-1`$ 时

$$
r_0+r_1+\Delta_0+\Delta_1\le2t+1\le2N-1.
\tag{8.14}
$$

两旧像共同正交补的维数足以安放全部新增像，可将这些新增方向等距送入互相正交的新像。初始 $`t=0`$ 的两域合计维数是二，单独处理且也不超过 $`2N-1`$。域与像在 $`K`$ 内可以相交，不额外要求这种相交消失。

延拓到 $`H_{N-1},G_{N-1}`$ 后，在 $`K\otimes\mathcal B`$ 的子空间上规定

$$
U(x\otimes|0\rangle+y\otimes|1\rangle)
=(Ax+By)\otimes|0\rangle,
\qquad x\in H_{N-1},\ y\in G_{N-1}.
\tag{8.15}
$$

输入两块正交，输出由构造也正交，各块保持内积，因此这是子空间等距，可补为同一全域酉。最终这个固定 $`U`$ 完全重现构造时的全部轨道，并计算第 $`N`$ 步；无需再把部分映射扩到 $`H_N,G_N`$。对初始基态成立，经线性性即覆盖任意相干输入及参考。所有选择在运行前完成，运行中没有更换门。纯空白与可逆性保证终端联合恢复。$`N=1`$ 取两个 qubit 间的 SWAP 即达到二维。证明完毕。

**推论 8.4（控制计费与共同初始化的精确分离）。** 从第三步起，已知相位的实际档案每个终端均有四维接收边界；要求一个固定门持续接收至 $`N`$，并将全部持久控制计入同一寄存器，则精确最小维数为 $`2N-1`$。其初期序列为 $`2,3,5,7,9,\ldots`$。若把独立纯初始化及全部输入的要求改为一份指定的共同平稳纯化，则二维接收器可用一个固定门永久返回纯空白。因此这三个容量对应不同的控制与来源条件。这是总接收维数，不是额外钟必须独立张量分解后的维数，也不是把发射步数解释为物理历时。

证明。前两项分别由定理2.1及8.3给出。第三项使用 Godley–Guţă 的既有相干吸收构造（Lemma 4.1），在本来源上作如下特化；该成熟构造的适用条件与初始化要求见[文献说明](../../../Library/Dynamics/godley2023absorber.md)。令

$$
\rho_*=(1-\mu)|m_0\rangle\langle m_0|+\mu|m_1\rangle\langle m_1|,
\qquad \mu=\frac{\alpha^2}{1+\alpha^2},
\tag{8.16}
$$

并将 $`M,K`$ 初始共同准备为 $`\rho_*`$ 的一个固定纯化 $`|\Xi\rangle_{MK}`$。每轮发射前及该轮接收完成后，$`MK`$ 共同态均为这个 $`|\Xi\rangle`$。

$`E(\rho_*)=\rho_*`$，且 $`\det\rho_*=\alpha^2\mu(1-\mu)>0`$，所以它是秩二密度矩阵。取谱分解 $`\rho_*=\sum_{j=0}^1\lambda_j|r_j\rangle\langle r_j|`$，其中 $`\lambda_j>0`$，并置 $`|\Xi\rangle=\sum_j\sqrt{\lambda_j}|r_j\rangle_M|j\rangle_K`$。

发射后的纯态 $`(T\otimes I_K)|\Xi\rangle`$ 在活动 $`M`$ 上的边缘仍为 $`\rho_*`$，故可写为

$$
\Sigma_{\rm in}(T\otimes I_K)|\Xi\rangle
=\sum_{j=0}^1\sqrt{\lambda_j}|r_j\rangle_M|\chi_j\rangle_{K\mathcal B},
\qquad \langle\chi_i|\chi_j\rangle=\delta_{ij},
\tag{8.17}
$$

这里 $`\Sigma_{\rm in}`$ 是（7.1）中把发射输出换至 $`M,K,\mathcal B`$ 次序的置换。规定 $`U|\chi_j\rangle=|j\rangle_K|0\rangle_{\mathcal B}`$，再作有限维酉延拓，即得到

$$
(I_M\otimes U)\Sigma_{\rm in}(T\otimes I_K)|\Xi\rangle
=|\Xi\rangle_{MK}\otimes|0\rangle_{\mathcal B}
\tag{8.18}
$$

在同一固定因子次序下成立。共同态每步被恢复，故同一个 $`U`$ 可永久重复。这个构造是相同边缘的纯化之间等距对应的直接应用。证明完毕。

此处 $`MK`$ 已预先相关且来源被固定；若还附加参考 $`J`$，由于 $`MK`$ 共同态纯，初始联合态只能是它与 $`J`$ 的乘积。它不满足定义7.1的独立接收初态及任意 $`JM`$ 来源要求，因而不反驳定理7.3或8.3，也不能作为在原权限下免费取得的准备。

这给出一个可检验的统一关系：相同的局部发射规则与相同的几何切口，并不单独决定实现成本。允许的来源联合态、控制是否在切口内计费，以及重新拼接时要保留哪些参考关系，共同决定最小边界。固定门将前缀关系的独立链转化为 $`2N-1`$ 维容量；预先供应特定共同平稳关系则能消去这里的独立初始化瞬态。两种结论对应的来源不同，不能用其中一个替代另一个。

本节沿用第7节所引有限酉扩张背景；部分等距延拓、线性链独立性与共同平稳纯化的相干吸收均是成熟机制。新增结果是定理8.3在同一局部接收合同下的精确最小容量；推论8.4用既有吸收构造检验这一定理的初始化边界，不将该构造另报为新定理。没有从这些维数公式推出物理面积律、Lorentz 度量或 Born 规则；误差允许下的最小固定门容量仍须另证。

## 追加锚（本行以下为增补区）


## 9. 振幅退化处的精确容量跳变

**定义 9.1（已知复振幅的同一固定门任务）。** 将定义7.1中的已知来源替换为

$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,
\qquad a,b\in\mathbb C,\quad |a|^2+|b|^2=1,
\qquad T_{a,b}|i\rangle=|i\rangle_{\mathcal B}\otimes m_i.
\tag{9.1}
$$

振幅在运行前已知。保留独立纯接收初态、任意参考—记忆输入、同一个接收酉、每步精确纯空白、无额外丢弃环境及全部持久控制计入 $`K`$ 的条件。记覆盖每个终端 $`1\le n\le N`$ 的最小接收维数为 $`d_N(a,b)`$。发射等距对所有这些参数成立，包括两个记忆输出向量线性相关的 $`b=0`$ 情形。

**定理 9.2（非零振幅与两类退化来源的完整容量）。** 定义9.1给出

$$
\boxed{
d_1(a,b)=2,\qquad
d_N(a,b)=
\begin{cases}
2N-1,&ab\ne0,\\
N+1,&ab=0
\end{cases}
\quad(N\ge2).
}
\tag{9.2}
$$

因而对每个固定 $`N\ge3`$，从非零振幅来源趋近任一退化端点时，精确容量在端点下降 $`N-2`$。两个端点在给定初始记忆基态后，发射词不再分支，固定纯空白接收的容量仍随时域线性增长。

证明。记接收初态为 $`e`$，继续使用（8.1）—（8.3）的系数空间和行块。本证明中的 $`B`$ 为接收行块，发出位的空间记为 $`\mathcal B`$。

当 $`ab\ne0`$ 时，$`m_0,m_1`$ 线性独立，引理8.2的正交等距域及递推（8.5）仍成立。定理8.3的下界只用 $`a\ne0`$ 保证压缩伴随链不消失，以及 $`b\ne0`$ 保证 $`G_t\supseteq AH_{t-1}`$；不使用两振幅为正实数。其上界的部分等距延拓也只用这两个非零条件和归一化；（8.12）保留复系数 $`a,b`$，不需要取共轭。因此原证明给 $`2N-1`$。以下分别补足原证明不能直接代入的两个退化情形。

先令 $`a=0`$，于是 $`|b|=1`$。两个记忆输出仍线性独立，引理8.2可用，而实际递推变成

$$
u_j^i=Bv_{j-1}^i,\qquad v_j^i=bAu_{j-1}^i.
\tag{9.3}
$$

令 $`t=N-1`$。对 $`1\le r\le t`$，由全部初始系数及（9.3）得到精确的子空间等式

$$
H_r=\mathbb Ce+BG_{r-1},\qquad
G_r=\mathbb Ce+AH_{r-1}.
\tag{9.4}
$$

在这些域上，$`A,B`$ 各自等距，且两个像正交。非零向量 $`e`$ 不可能同时属于 $`BG_{r-1}`$ 和 $`AH_{r-1}`$，所以至少一项加上 $`\mathbb Ce`$ 时增加一维。写 $`h_r=\dim H_r`$、$`g_r=\dim G_r`$，就有

$$
h_r+g_r\ge h_{r-1}+g_{r-1}+1,
\qquad h_0+g_0=2.
\tag{9.5}
$$

故 $`h_t+g_t\ge t+2=N+1`$。最终两个等距像 $`AH_t,BG_t`$ 正交地位于同一个 $`K`$，给 $`\dim K\ge N+1`$。

再令 $`b=0`$，于是 $`|a|=1`$。此时 $`m_0,m_1`$ 线性相关，不能援用引理8.2对一般联合系数分别消去非空白行块。改为直接检查实际来源：初始输入 $`|0\rangle_M`$ 与 $`|1\rangle_M`$ 分别要求 $`Z_0e=Z_1e=0`$；首次发射后活动记忆恒在 $`\mathbb C|0\rangle_M`$，以后每一步实际到达的接收向量只配新位 $`|0\rangle_{\mathcal B}`$。记两条来源的 $`M=0`$ 系数为 $`x_j=u_j^0,y_j=u_j^1`$；第二条来源在初始时刻的其余系数仍为 $`v_0^1=e`$。保留来源产生的复相位，则

$$
x_0=e,\quad y_0=0,\qquad
x_j=aAx_{j-1}\ (j\ge1),\qquad
y_1=Be,\quad y_j=aAy_{j-1}\ (j\ge2).
\tag{9.6}
$$

因此在

$$
H_t=\operatorname{span}\{x_0,\ldots,x_t,y_1,\ldots,y_t\},
\qquad G_t=\mathbb Ce
\tag{9.7}
$$

上，实际空白要求仍给 $`Z_0H_t=0`$、$`Z_1G_t=0`$。由接收酉性，$`A|_{H_t}`$ 等距、$`Be`$ 为单位向量且 $`AH_t\perp\mathbb CBe`$。

对 $`t\ge1`$ 令 $`J_t=(A|_{H_t})^*\iota_{H_t}`$。式（9.6）及上述正交性给

$$
J_ty_1=0,\qquad J_ty_j=ay_{j-1}\ (2\le j\le t),
\qquad J_t^t x_t=a^te\ne0.
\tag{9.8}
$$

与（8.9）的链独立性论证相同，$`y_1,\ldots,y_t`$ 线性独立，且 $`x_t`$ 不在其张成内。因此 $`\dim H_t\ge t+1`$。再计入与 $`AH_t`$ 正交的 $`\mathbb CBe`$，得到 $`\dim K\ge t+2=N+1`$。当 $`N=1`$ 时，两个实际首步输入分别给两个正交空白输出，直接得到二维下界；这也适用于其余全部参数。

两个退化情形都有一个达到下界的同一固定门。取 $`K=\mathbb C^{N+1}`$，正交基 $`e_0,\ldots,e_N`$，初态 $`e=e_0`$，先规定

$$
U(e_0\otimes|0\rangle)=e_0\otimes|0\rangle,\qquad
U(e_0\otimes|1\rangle)=e_1\otimes|0\rangle.
\tag{9.9}
$$

若 $`b=0`$，再对 $`1\le j<N`$ 规定

$$
U(e_j\otimes|0\rangle)=e_{j+1}\otimes|0\rangle.
\tag{9.10}
$$

若 $`a=0`$，则改为对同一指标范围规定

$$
U(e_j\otimes|\beta_j\rangle)=e_{j+1}\otimes|0\rangle,
\qquad
\beta_j=
\begin{cases}0,&j\text{ 为奇数},\\1,&j\text{ 为偶数}.
\end{cases}
\tag{9.11}
$$

每一种规定中的输入基向量互异，输出恰为 $`e_0,\ldots,e_N`$ 各张量纯空白，也互异。因此可在剩余基向量之间任选双射，补成整个 $`K\otimes\mathcal B`$ 上的一个置换酉。

当 $`b=0`$ 时，两条基态来源发射的位词分别是全零词与首位一、其余全零的词；（9.9）—（9.10）使第 $`n`$ 步后的寄存器基标签分别为 $`e_0,e_n`$。当 $`a=0`$ 时，两条位词分别为 $`0101\cdots`$ 与 $`1010\cdots`$；（9.9）、（9.11）使第 $`n`$ 步后的基标签分别为 $`e_{n-1},e_n`$。这些陈述只描述基标签，来源积累的 $`a,b`$ 相位仍保留在线性振幅中，没有被测量或删除。故所有 $`n\le N`$ 的输出均为纯空白，线性性覆盖任意输入相干及参考。逆序运行接收酉即恢复完整档案联合态，给所需上界。首步对一般参数使用 SWAP 达到二维。

最后，$`ab\ne0`$ 的归一化参数可任意接近 $`a=0`$ 或 $`b=0`$，但其容量恒为 $`2N-1`$；端点值为 $`N+1`$，两者之差为 $`N-2`$。该跳变针对零误差、逐步纯空白和同一固定酉的合同；仅把终端恢复条件放宽而仍要求每步精确纯空白，不会降低这里的最小维数，因为反向酉已经给精确恢复。允许非空白泄漏或新丢弃环境时，实际域不再被上述论证强制为正交等距域，（9.2）不声称给出那些合同的容量。证明完毕。

## 追加锚（本行以下为增补区）


## 10. 允许丢弃新环境后的固定通道容量

**定义 10.1（固定 CPTP 接收与全部终端的精确恢复）。** 对定义9.1的同一已知来源，接收寄存器 $`K`$ 从独立纯态 $`e`$ 开始，每步施加同一个全域 CPTP 映射

$$
\mathcal C:\mathcal L(K\otimes\mathcal B)\longrightarrow\mathcal L(K).
\tag{10.1}
$$

实现（10.1）时允许每步引入并丢弃新的环境；所有持久接收记忆仍全部计入 $`K`$，不访问活动记忆 $`M`$ 或参考 $`J`$，不反馈来源，不按步数改变 $`\mathcal C`$。若保留已消费位作为输出端口，可以另外准备固定纯空白；它不承担任何档案信息。

令 $`\sigma_n(\rho)`$ 为接收后的 $`JMK`$ 联合态，$`\Omega_n(\rho)`$ 为不作接收时同一来源的 $`JM\mathcal B^{\otimes n}`$ 联合态。要求对每个 $`n\ge1`$，存在仅作用于 $`K`$、可依赖终端编号的 CPTP 解码器 $`\mathcal D_n`$，使

$$
(\operatorname{id}_{JM}\otimes\mathcal D_n)\sigma_n(\rho)
=\Omega_n(\rho)
\qquad\text{对全部有限参考 }J\text{ 及输入 }\rho.
\tag{10.2}
$$

定义 $`d_{\mathrm{CPTP},\infty}(a,b)`$ 为满足这一合同的最小有限 $`\dim K`$；不存在有限实现时取值 $`\infty`$。这里一个 $`K,e,\mathcal C`$ 同时服务全部终端；每个有限终端另选一台机器是不同量词。

**定理 10.2（固定 CPTP 接收器的无限时域分类）。** 在定义10.1的条件下，

$$
\boxed{
d_{\mathrm{CPTP},\infty}(a,b)=
\begin{cases}
2,&a=0,\\
3,&b=0,\\
\infty,&ab\ne0.
\end{cases}}
\tag{10.3}
$$

非退化情形的不能性甚至只需要：从一个指定纯初态 $`|0\rangle_M`$ 出发，每个终端局部恢复全部档案与活动记忆的纯联合态。它不要求接收后的联合态为纯态，也不要求被丢弃环境保持空白。

证明。先建立非退化情形的障碍。固定 $`p=|b|^2\in(0,1)`$，令

$$
R_0=|m_0\rangle\langle m_0|,\quad R_1=|0\rangle\langle0|,
\quad F=R_0-R_1,\quad
\rho_*={R_0+pR_1\over1+p},\quad D={p\over1+p}F.
\tag{10.4}
$$

源边缘通道为 $`E(X)=X_{00}R_0+X_{11}R_1`$。直接计算给 $`E(\rho_*)=\rho_*`$、$`E(F)=-pF`$ 和 $`\operatorname{Tr}F^2=2p`$。因此从 $`|0\rangle_M`$ 出发，对 $`n\ge1`$ 有

$$
\rho_{M,n}=\rho_*+(-p)^{n-1}D,\qquad
q_n:=\operatorname{Tr}\rho_{M,n}^2
=q_*+2\operatorname{Tr}(\rho_*D)(-p)^{n-1}
+\operatorname{Tr}D^2\,p^{2n-2},
\quad \operatorname{Tr}D^2={2p^3\over(1+p)^2}>0.
\tag{10.5}
$$

这里 $`q_*:=\operatorname{Tr}\rho_*^2`$。此纯度序列的指数基底属于 $`\{1,-p,p^2\}`$，最低模基底为唯一的正实数 $`p^2`$，其系数严格正。

假设存在有限接收器。将一次发射与固定接收合成 $`MK`$ 上的固定 CPTP 映射 $`\mathcal R`$，记上述初态的接收结果为

$$
\sigma_n=\mathcal R^n
\bigl(|0\rangle\langle0|_M\otimes|e\rangle\langle e|_K\bigr).
\tag{10.6}
$$

局部保迹接收不改变 $`M`$ 边缘，所以 $`\operatorname{Tr}_K\sigma_n=\rho_{M,n}`$。原始目标 $`\Omega_n=|\Psi_n\rangle\langle\Psi_n|_{M\mathcal B^{\otimes n}}`$ 是纯态。对（10.2）的解码器取 Kraus 算子，按环境基排列为 Stinespring 等距
 $`V_n:K\to\mathcal B^{\otimes n}\otimes E_n`$。
解码后的目标边缘纯，故整个延拓态必为

$$
(I_M\otimes V_n)\sigma_n(I_M\otimes V_n^*)
=|\Psi_n\rangle\langle\Psi_n|\otimes\tau_n.
\tag{10.7}
$$

这里纯边缘强制乘积可直接由正性看出：目标纯态正交补上的投影期望为零，整个态的支撑只能落在该一维子空间张量 $`E_n`$ 中。等距保持非零谱，而纯态的两侧边缘具有相同非零谱，因此（10.7）给

$$
\boxed{
\operatorname{Tr}\sigma_{K,n}^2
=q_n\operatorname{Tr}\sigma_n^2,
\qquad \sigma_{K,n}=\operatorname{Tr}_M\sigma_n.
}
\tag{10.8}
$$

这个恒等式完整允许 $`\tau_n`$ 为随 $`n`$ 改变的混合态。

在有限维矩阵空间上对 $`\mathcal R`$ 作 Jordan 分解。丢掉零特征值对应的有限幂零前缀后，其实际轨道可以写成

$$
\sigma_n=\sum_{\lambda\in\Lambda}\lambda^nP_\lambda(n),
\qquad r=\min_{\lambda\in\Lambda}|\lambda|>0.
\tag{10.9}
$$

$`\Lambda`$ 只收录该轨道实际出现的不同非零特征值，各 $`P_\lambda`$ 为非零矩阵多项式；不要求通道正规或可对角化。由于态的迹为一，$`\Lambda`$ 非空。

不同非零基底的指数多项式在整数尾部线性独立。为见这一点，对一份假设的零线性组合，逐一施加差分算子 $`f(n)\mapsto f(n+1)-zf(n)`$，对每个待消去基底 $`z`$ 使用高于其多项式次数的幂。它消去该基底，对任一不同基底只乘非零的最高次系数。保留一个基底后不可能得到恒零的非零多项式，故原组合的每项均必须为零。

利用 $`\sigma_n`$ Hermitian，以 Hilbert–Schmidt 内积展开其纯度：

$$
\operatorname{Tr}\sigma_n^2
=\|\sigma_n\|_{\rm HS}^2
=\sum_{\lambda,\mu\in\Lambda}
(\overline\lambda\mu)^n
\langle P_\lambda(n),P_\mu(n)\rangle_{\rm HS}.
\tag{10.10}
$$

所有基底模至少为 $`r^2`$。正实基底 $`r^2`$ 的多项式系数恰为

$$
A_r(n)=\sum_{|\lambda|=r}\|P_\lambda(n)\|_{\rm HS}^2.
\tag{10.11}
$$

因为 $`\overline\lambda\mu=r^2`$ 强制 $`|\lambda|=|\mu|=r`$ 且 $`\lambda=\mu`$，这里没有其他交叉项。该多项式最高次系数是若干非零矩阵系数的平方范数之和，严格正；所以这一最低模项确实存在。

偏迹仅把（10.9）中的 $`P_\lambda`$ 替换为 $`\operatorname{Tr}_M P_\lambda`$，不引入新基底。因此（10.8）左边的指数多项式没有模小于 $`r^2`$ 的项。右边却必含正实基底 $`p^2r^2<r^2`$，系数为

$$
{\operatorname{Tr}D^2\over p^2}\,A_r(n)\ne0.
\tag{10.12}
$$

源纯度的另外两种基底只可能产生模至少 $`r^2`$、$`pr^2`$ 的项，不能抵消（10.12）；源的 $`p^2`$ 项也只有乘上（10.11）才能产生这个正实基底。指数多项式唯一性遂与（10.8）矛盾。这证明 $`ab\ne0`$ 时的不能性，且没有限制终端解码器随 $`n`$ 变化。

现在构造 $`a=0`$ 的二维接收器。取 $`K=\mathbb C^2`$，初态 $`|+\rangle`$，定义从 $`K\otimes\mathcal B`$ 到 $`K\otimes E`$ 的固定酉

$$
V|k\rangle_K|s\rangle_{\mathcal B}
=|s\rangle_K|k\mathbin{\oplus}s\rangle_E,
\qquad k,s\in\{0,1\},\qquad
\mathcal C(X)=\operatorname{Tr}_E(VXV^*).
\tag{10.13}
$$

首步满足 $`V(|+\rangle\otimes|s\rangle)=|s\rangle\otimes|+\rangle`$，故环境与数据独立，寄存器保存首位。此后来源逐位交替，接收输入仅支撑于 $`|0\rangle_K|1\rangle_{\mathcal B}`$ 与 $`|1\rangle_K|0\rangle_{\mathcal B}`$ 的张成。两者都使环境成为 $`|1\rangle_E`$，寄存器保存最新位；相干组合的相对相位不变。给定终端 $`n`$，最新位唯一确定整条交替词，故把两份正交寄存器基态等距送到对应词，就恢复全部参考—记忆—档案联合态。来源产生的 $`b`$ 相位始终留在实际振幅中。

首步选最大纠缠输入时，档案与其余系统的 Schmidt 秩为二；一维 $`K`$ 的局部解码不能产生这种跨切口纠缠。因此二维达到最小值。

最后令 $`b=0`$。取三维 $`K`$，正交基为 $`|e\rangle,|d_0\rangle,|d_1\rangle`$，初态 $`|e\rangle`$。定义固定通道的 Kraus 算子

$$
L_{\rm first}=\sum_{s=0}^1|d_s\rangle\langle e,s|,
\qquad L_{\rm run}=\sum_{s=0}^1|d_s\rangle\langle d_s,0|,
\qquad L_s=|e\rangle\langle d_s,1|\quad(s=0,1).
\tag{10.14}
$$

四项 $`L^*L`$ 之和为输入空间恒等算子，因此定义全域 CPTP 通道。首步只有 $`L_{\rm first}`$ 起作用，存下首位的整个 qubit；以后活动记忆在 $`|0\rangle_M`$，来源恒发零，只有 $`L_{\rm run}`$ 起作用并保持数据。环境只记录确定的首次或后续阶段，取得不了来源位。终端解码把 $`|d_s\rangle`$ 送到 $`|s0\cdots0\rangle`$，在未使用的 $`|e\rangle`$ 上任意补为通道，即满足（10.2）。来源的单位模振幅 $`a`$ 所产生的相位保留，不要求 $`a=1`$。

还须排除二维 $`K`$。若它存在，首步在实际输入域 $`S_0=\mathbb Ce\otimes\mathcal B`$ 上必须无损传输任意 qubit，因为 $`b=0`$ 时源把初始 qubit 完整发到首位，活动记忆已经复位。二维输入、二维输出且具有 CPTP 左逆的通道必为酉通道：对满 Schmidt 秩 Bell 输入使用（10.7），二维输出限制迫使噪声因子秩为一，于是编码的 Choi 态纯，编码是单个等距算子，等维时即酉。

所以首步后任意 $`K`$ 态及其参考相干均是实际可达的。第二步的新位固定为零，（10.2）又要求同一个 $`\mathcal C`$ 在 $`S_1=K\otimes\mathbb C|0\rangle`$ 上无损传输任意 qubit，也必须为酉编码。固定一个 $`\mathcal C`$ 的 Stinespring 等距 $`W:K\otimes\mathcal B\to K\otimes E`$。在每个 $`S_i`$ 上，它的环境因子都是一个固定纯向量；这是相应限制通道为酉的结果。两域交于一维 $`\mathbb C(e\otimes|0\rangle)`$，同一个 $`W`$ 在这份非零交向量上的像强制两个环境向量共线。

由线性性，$`W`$ 因而把三维 $`S_0+S_1`$ 等距送入同一个二维 $`K\otimes\mathbb C\eta`$，矛盾。因此二维不可能，三维构造最小。证明完毕。

## 追加锚（本行以下为增补区）


## 11. 每个正精度的有限固定接收与零误差极限

**定义 11.1（同一装置在全部终端的近似联合任务）。** 固定定义10.1中的已知 $`a,b\ne0`$，令 $`p=|b|^2\in(0,1)`$。将（10.2）放宽为

$$
\sup_{n\ge1}\ \sup_{J,\rho}
\frac12\left\|
(\operatorname{id}_{JM}\otimes\mathcal D_n)\sigma_n(\rho)
-\Omega_n(\rho)\right\|_1\le\epsilon,
\qquad 0<\epsilon<1.
\tag{11.1}
$$

仍要求一个独立纯接收初态和一个固定全域 CPTP 接收通道服务全部 $`n`$，新环境可以丢弃，所有持久控制计入 $`K`$；仅终端解码器可以依赖 $`n`$。记最小有限接收维数为 $`d_\infty^{(\epsilon)}(a,b)`$。设计可以使用已知振幅，未放入未知共同相位族。

**定理 11.2（全时域对数容量上界与零误差发散）。** 令

$$
\rho_*={|m_0\rangle\langle m_0|+p|0\rangle\langle0|\over1+p},
\qquad \lambda_*:=\lambda_{\min}(\rho_*)>0,
\qquad C_p={\sqrt{2p}\over(1+p)\sqrt{\lambda_*}},
\tag{11.2}
$$

以及

$$
T=\max\left\{3,\,
1+\left\lceil{\log(2C_p/\epsilon)\over\log(1/p)}\right\rceil\right\}.
\tag{11.3}
$$

则

$$
\boxed{
d_\infty^{(\epsilon)}(a,b)\le4T-2
=O_p\!\left(\log{1\over\epsilon}\right),
\qquad
\lim_{\epsilon\downarrow0}d_\infty^{(\epsilon)}(a,b)=\infty.
}
\tag{11.4}
$$

更具体地，对每个固定维数 $`D`$，可取显式时域 $`N_D=6D^2(4D^2+1)`$，并存在 $`\eta_D>0`$，使任一维数不超过 $`D`$ 的固定接收器，至少在一个 $`n\le N_D`$ 上具有不小于 $`\eta_D`$ 的最坏参考完整半迹误差。特别地，若一个 $`D`$ 维固定接收器精确服务前 $`N`$ 步，则必有 $`N<6D^2(4D^2+1)`$，因而 $`D>(N/30)^{1/4}`$。这个精确时域下界不主张最优；$`\eta_D`$ 仍只是存在性结论。

证明。先在有限启动时刻建立一份共同编码。沿用（10.4）的 $`F=R_0-R_1`$。对两个初始记忆基态，$`T`$ 步后的活动记忆边缘为

$$
\rho_{i,T}=\rho_*+c_i(-p)^{T-1}F,
\qquad c_0={p\over1+p},\quad c_1=-{1\over1+p}.
\tag{11.5}
$$

$`T\ge3`$ 时，两份边缘均秩二。实际档案按首发位 $`i`$ 分成两个正交扇区；每个扇区在该初始基态下的 Schmidt 支撑维数为二。因此实际总支撑 $`S_T`$ 为四维，纯化之间的等距对应给

$$
F_T:S_T\xrightarrow{\ \cong\ }Q\otimes R,
\qquad \dim Q=\dim R=2,
\qquad
(I_M\otimes F_T)T_T|i\rangle
=|i\rangle_Q\otimes|\operatorname{vec}\sqrt{\rho_{i,T}}\rangle_{MR}.
\tag{11.6}
$$

因子置换按所标系统理解。这里 $`T_T`$ 是来源的累计等距，$`\operatorname{vec}A=\sum_{j,k}A_{jk}|j\rangle_M|k\rangle_R`$ 使用固定基。式（11.6）分别在两份正交档案扇区上定义，故合起来是同一个仅作用于档案的等距同构；未操作活动 $`M`$。

定义比较等距

$$
W_\infty|i\rangle=|i\rangle_Q|\Xi\rangle_{MR},
\qquad |\Xi\rangle=|\operatorname{vec}\sqrt{\rho_*}\rangle.
\tag{11.7}
$$

两份 $`Q`$ 标签正交，因而

$$
\left\|(I_M\otimes F_T)T_T-W_\infty\right\|
=\max_{i=0,1}\left\|\sqrt{\rho_{i,T}}-\sqrt{\rho_*}\right\|_{\rm HS}.
\tag{11.8}
$$

这个算子范数控制相干输入，并在张量任意参考后保持，不能只解释为两份经典基态的比较。

直接计算有 $`\det\rho_*=p^2/(1+p)^2>0`$ 和 $`\|F\|_{\rm HS}=\sqrt{2p}`$。取 $`A=\sqrt{\rho_{i,T}}`$、$`B=\sqrt{\rho_*}`$、$`Z=A-B`$，则

$$
AZ+ZB=\rho_{i,T}-\rho_*.
\tag{11.9}
$$

在两边正算子的各自本征基组成的矩阵基中，Sylvester 算子 $`Z\mapsto AZ+ZB`$ 的本征值为两本征值之和，均至少为 $`\sqrt{\lambda_*}`$。所以

$$
\left\|\sqrt{\rho_{i,T}}-\sqrt{\rho_*}\right\|_{\rm HS}
\le{\|\rho_{i,T}-\rho_*\|_{\rm HS}\over\sqrt{\lambda_*}}
\le C_pp^{T-1}=:\delta.
\tag{11.10}
$$

于是对全部参考完整输入，真实 $`T`$ 步编码态 $`\alpha_T`$ 与比较态

$$
\beta_T=\rho_{JQ}\otimes|\Xi\rangle\langle\Xi|_{MR}
\tag{11.11}
$$

的半迹距离至多 $`\delta`$。这里 $`\rho_{JQ}`$ 是把原输入的记忆因子同构为 $`Q`$ 所得的同一输入态。纯态半迹距离不超过相应单位向量之差的范数，对任意混合态取纯化后偏迹即可得到该界。$`\beta_T`$ 只用于比较；装置实际生成的是 $`\alpha_T`$，没有免费供应共同平稳初始化。

由 $`E(\rho_*)=\rho_*`$，采用推论8.4所引 Godley–Guţă 相干吸收构造：[^phase_burnin_absorber] 存在 $`R\otimes\mathcal B`$ 上的同一个酉 $`U_*`$，使

$$
(I_M\otimes U_*)(T_{a,b}\otimes I_R)|\Xi\rangle
=|\Xi\rangle\otimes|0\rangle_{\mathcal B}.
\tag{11.12}
$$

这也可直接将发射后同一 $`\rho_*`$ 的两份正交 Schmidt 纯化向量，送回 $`R`$ 的对应基向量张量空白，再延拓为酉。启动后的运行通道为

$$
\mathcal C_{\rm run}(X)
=\operatorname{Tr}_{\mathcal B}
\bigl[(I_Q\otimes U_*)X(I_Q\otimes U_*^*)\bigr].
\tag{11.13}
$$

比较态（11.11）经每轮“源发射＋运行接收”完全不变。实际态执行同一个 CPTP 演化，半迹距离收缩，故对全部 $`n\ge T`$，其运行态 $`\sigma_n`$ 满足

$$
D(\sigma_n,\beta_T)\le\delta,
\qquad D(X,Y):=\tfrac12\|X-Y\|_1.
\tag{11.14}
$$

这个比较保留 $`J,M,Q,R`$ 全部系统，后续误差没有按步相加。

终端解码只访问接收器。对 $`n=T+\ell`$，在 $`R`$ 旁加入 $`\ell`$ 个纯空白位，按逆时间顺序运行 $`U_*^*`$，再对 $`QR`$ 执行 $`F_T^*`$，得到前 $`T`$ 位和后续 $`\ell`$ 位档案。为验证它，把每个接收门与其后的源发射交换次序：前者作用于接收器及已经发出的位，后者只作用于活动 $`M`$ 及未来新位。因此全部接收门可推到源发射之后，逆接收电路确实不操作 $`M`$。

令 $`G_n`$ 表示先用 $`F_T^*`$ 展开前缀，再让源执行 $`\ell`$ 步的联合等距；它可以作用于 $`M`$，仅用于下面的数学比较。记上述实际局部解码器为 $`\mathcal D_n`$，则

$$
\Omega_n=G_n\alpha_TG_n^*,
\qquad
(\operatorname{id}_{JM}\otimes\mathcal D_n)\beta_T
=G_n\beta_TG_n^*.
\tag{11.15}
$$

第二式只在平稳比较态上使用（11.12），没有断言局部解码器将任意 $`\alpha_T`$ 直接变成未来目标。结合（11.14）、等距保持距离及通道收缩性，得到

$$
\begin{aligned}
D\bigl((\operatorname{id}_{JM}\otimes\mathcal D_n)\sigma_n,\Omega_n\bigr)
&\le D(\sigma_n,\beta_T)+D(\beta_T,\alpha_T)\\
&\le2\delta\le\epsilon.
\end{aligned}
\tag{11.16}
$$

还需将启动门与运行门合成一台固定装置。对 $`0\le t<T`$，取精确前缀编码扇区 $`K_t`$；其维数依次为 $`1,2,3,4,\ldots,4`$，运行扇区为 $`K_{\rm run}=Q\otimes R`$。置

$$
K=\bigoplus_{t=0}^{T-1}K_t\ \oplus\ K_{\rm run},
\qquad \dim K=1+2+3+4(T-2)=4T-2.
\tag{11.17}
$$

在启动扇区上，使用实际包含关系 $`S_{t+1}\subseteq S_t\otimes\mathcal B`$ 给出的精确压缩部分等距；最后一步的目标编码选为（11.6）。每块在实际支撑正交补上补以输出固定态的 Kraus 算子，使其全域保迹。运行扇区采用（11.13）。先按输入扇区投影、再用相应 Kraus 算子，便构成一个全域固定 CPTP 通道。

实际运行每时刻只处于一个确定扇区，故没有源数据的扇区间相干被此投影删除。初态在 $`K_0`$，到第 $`T`$ 步进入运行扇区，此后永久留在其中。全部启动控制已计入（11.17）；运行中不调用外部步数来换门。$`n\le T`$ 的前缀均精确编码，解码误差为零；$`n>T`$ 用（11.16）。未使用扇区上的终端解码可任意 CPTP 完成。因此（11.1）的两个上确界同时满足，得到容量上界。

先给固定维数的显式精确障碍。取 $`\dim K=D`$，仅选定理10.2证明中的纯初态 $`|0\rangle_M`$。令 $`V=\operatorname{Herm}(M\otimes K)`$，其实维数为 $`q=4D^2`$。固定接收器与发射合成实线性映射 $`\mathcal R:V\to V`$，保留实际轨道 $`\sigma_n=\mathcal R^n\sigma_0`$。在实对称张量子空间 $`W=\operatorname{Sym}^2V`$ 上，$`\mathcal R\otimes\mathcal R`$ 限制为线性映射 $`L`$，且

$$
s:=\dim W={q(q+1)\over2},\qquad
\tau_n=\sigma_n\otimes\sigma_n,\qquad \tau_{n+1}=L\tau_n.
\tag{11.18}
$$

把两个实对称双线性型
 $`(X,Y)\mapsto\operatorname{Tr}[(\operatorname{Tr}_M X)(\operatorname{Tr}_M Y)]`$
及 $`(X,Y)\mapsto\operatorname{Tr}(XY)`$
线性化并限制到 $`W`$，分别记为 $`u,v`$。于是 $`u(\tau_n)=\operatorname{Tr}\sigma_{K,n}^2`$、$`v(\tau_n)=\operatorname{Tr}\sigma_n^2`$。按（10.5）写 $`q_n=q_*+\beta(-p)^{n-1}+\gamma p^{2n-2}`$，并置

$$
\begin{aligned}
z_n&=(\tau_n,(-p)^{n-1}\tau_n,p^{2n-2}\tau_n),\\
z_1&=(\tau_1,\tau_1,\tau_1),\qquad
z_{n+1}=\operatorname{diag}(L,-pL,p^2L)z_n,\\
f_n&=u(\tau_n)-q_nv(\tau_n)
=(u-q_*v)(z_n^{(1)})-\beta v(z_n^{(2)})-\gamma v(z_n^{(3)}).
\end{aligned}
\tag{11.19}
$$

这是一份维数 $`3s=6D^2(4D^2+1)=N_D`$ 的固定线性递推及线性读出。Cayley–Hamilton 恒等式给首项系数为一的 $`N_D`$ 阶标量递推，所以 $`f_1,\ldots,f_{N_D}`$ 全为零就强制所有 $`f_n`$ 为零；不需要 $`f_0`$，也不要求 $`L`$ 可逆。

定理10.2证明中（10.9）—（10.12）的最低模代数论证直接排除了这一恒零序列。因此任何固定接收器都不可能精确服务前 $`N_D`$ 步：精确恢复会由（10.8）使这些 $`f_n`$ 全为零。这里没有从纯度恒等式反推出未来解码器，只在有限合同之外继续迭代同一个全域通道以应用线性递推。若精确服务前 $`N`$ 步，必有 $`N<N_D\le30D^4`$，即得陈述中的四次根下界。

最后证明正误差障碍和发散。固定 $`D`$ 后，纯接收初态、固定接收通道以及前 $`N_D`$ 个终端解码器构成紧参数集：纯态集合闭且有界，各有限维通道的 Choi 集合也闭且有界。目标函数取前 $`N_D`$ 个终端的最大参考完整半迹误差。输入维数为二，通道差的钻石范数可以用二维参考取得，故这是有限维参数的连续函数。它在紧集上取得最小值；前述显式精确障碍排除零点，故其最小值 $`\eta_D`$ 严格正。维数较小的装置可补到 $`D`$ 维并在未使用空间任意完成通道，所以同一障碍覆盖全部维数不超过 $`D`$ 的装置。

所以 $`\epsilon<\eta_D`$ 时必有 $`d_\infty^{(\epsilon)}(a,b)>D`$。这对每个 $`D`$ 成立，即得（11.4）的发散结论。紧性论证没有提供 $`\eta_D`$ 的数值或有效求法，上界的常数也只针对固定 $`p\in(0,1)`$；不主张在振幅退化极限上一致，更没有证明对数上界最优。证明完毕。

[^phase_burnin_absorber]: 平稳纯化的固定相干吸收使用 Godley–Guţă (2023), Lemma 4.1，来源及初始化条件见[既有文献说明](../../../Library/Dynamics/godley2023absorber.md)。该已知构造在本证明中作为有限启动后的运行步骤；有限启动编码、所有终端共用误差界及固定通道容量的零误差极限在同一合同下组合。

## 追加锚（本行以下为增补区）


## 12. 环境交叉关系给出的平方根精确容量下界

**定义 12.1（有限时域的固定 CPTP 接收容量）。** 固定定义10.1中的已知非退化来源 $`a,b\ne0`$。对整数 $`N\ge1`$，记 $`d_{\mathrm{CPTP},N}(a,b)`$ 为一个独立纯初态、一个固定全域 CPTP 接收通道及仅依赖终端编号的解码器，精确满足（10.2）对全部 $`1\le n\le N`$ 所需的最小持久接收维数。装置可以依赖预定 $`N`$，所有持久控制均计入容量；每轮新环境可立即丢弃，活动记忆与参考不可访问。

**定理 12.2（保留环境相干约束的有限时域障碍）。** 对定义12.1的任务，

$$
\boxed{
N<8\,d_{\mathrm{CPTP},N}(a,b)^2,
\qquad
d_{\mathrm{CPTP},N}(a,b)>\sqrt{N/8}.
}
\tag{12.1}
$$

对 $`N\ge2`$，已有固定纯空白酉构造同时给

$$
\sqrt{N/8}<d_{\mathrm{CPTP},N}(a,b)\le2N-1.
\tag{12.2}
$$

此外，对每个固定正整数 $`D`$，存在 $`\widehat\eta_D>0`$，使任一维数不超过 $`D`$ 的固定接收器，至少在一个 $`n\le8D^2`$ 上具有不小于 $`\widehat\eta_D`$ 的最坏参考完整半迹恢复误差。这里 $`\widehat\eta_D`$ 可以依赖已固定的 $`a,b`$，未给其数值，也不主张在振幅退化极限上一致。式（12.1）加强定理11.2的精确时域下界，不改动其正误差容量上界，也不主张平方根下界最优。

证明。只取任务允许的纯源初态 $`|0\rangle_M`$，接收初态为 $`|e\rangle_K`$，令

$$
H=M\otimes K,\quad \dim K=D,\quad
|\psi_0\rangle=|0\rangle_M|e\rangle_K,\qquad
\mathcal R(X)=\sum_{u\in\mathsf A}K_uXK_u^*.
\tag{12.3}
$$

这里 $`\mathcal R`$ 是一次源发射与固定接收合成的 $`H`$ 上通道，$`\mathsf A`$ 为一份固定有限 Kraus 表的指标集。$`K_u`$ 是算子，寄存器仍记为 $`K`$。对词 $`w=u_1\cdots u_n`$，置 $`K_w=K_{u_n}\cdots K_{u_1}`$，空词取恒等算子。连续使用这份 Kraus 表的一份全局纯化为

$$
|\chi_n\rangle
=\sum_{w\in\mathsf A^n}K_w|\psi_0\rangle\otimes|w\rangle_{E_n}.
\tag{12.4}
$$

$`E_n`$ 只在数学纯化中保留已丢弃的环境，并不供接收器使用。记 $`\sigma_n=\operatorname{Tr}_{E_n}|\chi_n\rangle\langle\chi_n|`$。

若终端 $`n`$ 的局部解码恢复全部档案与活动记忆的目标纯态，则对解码器取 Stinespring 等距，解码后的全局纯态必分解为目标纯态与其余系统纯态的张量积。因此，解码前后的 $`ME_n`$ 边缘相同，并满足

$$
\rho_{ME_n}=\rho_{M,n}\otimes\rho_{E_n}.
\tag{12.5}
$$

逐环境矩阵元读取（12.5），得到对任意 $`w,v\in\mathsf A^n`$ 及 $`A\in\operatorname{End}(M)`$，

$$
\langle\psi_0|K_w^*(A\otimes I_K)K_v|\psi_0\rangle
=\operatorname{Tr}(\rho_{M,n}A)
\langle\psi_0|K_w^*K_v|\psi_0\rangle.
\tag{12.6}
$$

反过来，（12.6）对全部 $`A,w,v`$ 成立也足以逐矩阵元恢复（12.5）。这里包含 $`w\ne v`$ 的环境相干矩阵元，不能只检查各分支概率。由纯目标恢复得到（12.5）的步骤是标准的环境解耦必要条件，本证明将它用于同一固定接收器的全部有限续接。

置 $`p=|b|^2\in(0,1)`$、$`\lambda=-p`$，并沿用（10.4）的平稳态 $`\rho_*`$。令

$$
\Delta=|0\rangle\langle0|-\rho_*.
\tag{12.7}
$$

本来源的边缘通道满足 $`E(\rho_*)=\rho_*`$、$`E(\Delta)=\lambda\Delta`$，所以

$$
\rho_{M,n}=\rho_*+\lambda^n\Delta\qquad(n\ge0).
\tag{12.8}
$$

该式在 $`n=0`$ 也成立；它与（10.5）在 $`n\ge1`$ 的表达相同。

现在把（12.6）的整族关系放进一个有限维线性空间。取

$$
\mathcal V=\operatorname{End}(H)\oplus\operatorname{End}(H),
\qquad \dim_{\mathbb C}\mathcal V=8D^2,
\tag{12.9}
$$

并定义

$$
\begin{aligned}
g_A&=\left(
(A-\operatorname{Tr}(\rho_*A)I_M)\otimes I_K,
\operatorname{Tr}(\Delta A)I_H
\right),\\
\ell(X,Y)&=\langle\psi_0|(X-Y)|\psi_0\rangle,\\
\mathcal L_{uv}(X,Y)&=
(K_u^*XK_v,\ \lambda K_u^*YK_v)
\qquad(u,v\in\mathsf A).
\end{aligned}
\tag{12.10}
$$

对 $`g_A`$ 作长度 $`n`$ 的字母对复合，所得向量遍历

$$
\left(
K_w^*[(A-\operatorname{Tr}(\rho_*A)I_M)\otimes I_K]K_v,
\lambda^n\operatorname{Tr}(\Delta A)K_w^*K_v
\right)
\quad(w,v\in\mathsf A^n).
\tag{12.11}
$$

因此（12.6）恰为 $`\ell`$ 在这些向量上等于零。第二坐标携带 $`\lambda^n`$，故把不同长度的等式放在同一线性空间中，没有删去它们各自的时间因子。

定义累计词空间

$$
W_0=\operatorname{span}_{\mathbb C}\{g_A:A\in\operatorname{End}(M)\},
\qquad
W_{t+1}=W_t+\sum_{u,v\in\mathsf A}\mathcal L_{uv}(W_t).
\tag{12.12}
$$

归纳可见，$`W_t`$ 正是长度至多 $`t`$ 的全部（12.11）的张成。若 $`W_t=W_{t+1}`$，它就对全部 $`\mathcal L_{uv}`$ 不变，此后永久稳定。每次严格增长至少增加一维，故

$$
W_{8D^2}=\bigcup_{t\ge0}W_t.
\tag{12.13}
$$

这只是有限维可达空间的标准稳定机制；本处的两个算子坐标把随时间变化的边缘目标与全部环境交叉关系一并纳入该机制。

假设同一 $`D`$ 维接收器精确服务前 $`8D^2`$ 个终端。每个这些终端的（12.6）都成立，长度零的等式则由（12.7）自动成立。因此 $`\ell`$ 在 $`W_{8D^2}`$ 上恒零。由（12.13），（12.6）便对所有 $`n\ge0`$ 成立，从而（12.5）也对所有这些 $`n`$ 成立。

这里只对各个时刻已经成立的同长度交叉等式作线性组合，没有要求不同时间之间存在物理相干，也没有假设有限合同之外仍有解码器。被继续迭代的只是同一个已定义于全域的通道。

由（12.4）的全局纯性以及（12.5），有

$$
\operatorname{Tr}\sigma_{K,n}^2
=\operatorname{Tr}\rho_{ME_n}^2
=\operatorname{Tr}\rho_{M,n}^2\operatorname{Tr}\rho_{E_n}^2
=\operatorname{Tr}\rho_{M,n}^2\operatorname{Tr}\sigma_n^2
\qquad(n\ge0).
\tag{12.14}
$$

定理10.2证明中的（10.9）—（10.12）已排除这条全时域纯度乘积恒等式：源纯度的唯一最低模正实基底为 $`p^2`$ 且系数严格正，与有限维固定通道轨道的最低纯度谱模相乘，会产生偏迹侧不可能具有的更低模项。因此假设矛盾，得到 $`N<8D^2`$ 及（12.1）。定理9.2的固定酉属于这里允许的 CPTP 接收器，给出（12.2）的上界。

最后固定 $`D`$ 和 $`8D^2`$ 个终端。独立纯初态、固定接收通道及这有限多个局部解码器的参数集紧。前 $`8D^2`$ 个终端的最大参考完整半迹误差是连续函数：输入维数为二，可把通道差的参考维数限制为二。上面已排除最小值为零，故该函数的最小值 $`\widehat\eta_D`$ 严格正。较小维数的装置可补到 $`D`$ 维，因而同一结论也覆盖全部不超过 $`D`$ 的容量。证明完毕。

## 追加锚（本行以下为增补区）


## 13. 未知共同相位的无终端接收与吸收截断边界

**定义 13.1（与未来终端无关的门序列）。** 回到定义1.1的来源，取 $`\Theta=\mathbb R/(2\pi\mathbb Z)`$、$`c_t=1`$、$`p=\alpha^2`$ 和 $`\mu=p/(1+p)`$。对固定 $`0<\epsilon<1`$，允许预先给定一列有限维寄存器及全域 CPTP 映射

$$
K_0=\mathbb C,\qquad
\mathcal C_n:\mathcal L(K_{n-1}\otimes B)\longrightarrow\mathcal L(K_n)
\quad(n\ge1),
\qquad
\mathcal D_n:\mathcal L(K_n)\longrightarrow\mathcal L(H_n).
\tag{13.1}
$$

门可以依赖当前编号、已知来源和误差要求，但不能依赖实际相位、输入、参考或未来选择的终端。全部持久且与来源有关的接收系统计入 $`K_n`$；每轮新环境可立即丢弃。不访问活动 $`M`$ 与参考 $`J`$，也不反馈来源。要求每个确定终端的全部参考完整联合态满足（5.1）的半迹误差界。这里不要求固定维数或同一个门，也不增加可依赖未知状态的停止策略合同。

**定理 13.2（无预定终端的近平方根接收）。** 对定义13.1，存在同一门序列满足全部终端误差至多 $`\epsilon`$，且

$$
\dim K_n
=O\!\left(\sqrt{n\left[\log\log(en)+\log(1/\epsilon)\right]}+1\right).
\tag{13.2}
$$

具体地，置

$$
\delta={\epsilon^2\over2},\quad
\delta_r={6\delta\over\pi^2r^2},\quad
s_r=\sqrt{{2^r-1\over2}\log{2\over\delta_r}},\quad
r(n)=\max\{1,\lceil\log_2n\rceil\},\quad
b_n={1+s_{r(n)}\over1+p}.
\tag{13.3}
$$

可取

$$
\dim K_n\le4\bigl(\lfloor2b_n\rfloor+1\bigr)+1
\le8b_n+5.
\tag{13.4}
$$

证明。使用（6.6）的同一实际词链与鞅 $`M_k`$。由（6.8），对两个初位及每个整数 $`r\ge1`$，

$$
\Pr_i\left\{\max_{1\le k\le2^r}|M_k|\ge s_r\right\}
\le\delta_r.
\tag{13.5}
$$

因 $`\sum_r\delta_r=\delta`$，可数并集界表明：至少以 $`1-\delta`$ 的概率，全部这些 dyadic 时域界同时成立。结合（6.7），在该同一个事件上，所有 $`n\ge1`$ 同时满足

$$
|S_n-n\mu|\le b_n.
\tag{13.6}
$$

按几何时域分配可求和错误预算是标准的时间一致浓缩方法；Howard 等的 stitched boundary 给出同类迭代对数尺度。[^phase_anytime_stitching] 此处直接由已得（6.8）完成所需概率估计。

称词存活，当且仅当它的每个前缀均满足（13.6）。沿用（6.3）的首末荷扇区，但将固定带宽换为每个时刻各自的 $`b_t`$，得到 $`g_{ijq}^{n,\rm s}`$ 及 $`W_n^{\rm s}`$。式（6.10）的末端指示函数相应成为 $`\mathbf1_{\{|q-(n+1)\mu|\le b_{n+1}\}}`$，仍严格给出

$$
W_{n+1}^{\rm s}\subseteq W_n^{\rm s}\otimes B.
\tag{13.7}
$$

全部这些空间只由已知来源和事先固定的带宽序列确定，与实际相位及未来终端无关。

对 $`n\ge1`$，取 $`K_n=W_n^{\rm s}\oplus\mathbb C|\bot\rangle`$，并保持 $`K_0=\mathbb C`$ 及空档案恒等编码 $`F_0`$；用（6.11）的成功部分等距和补空间送到旗标的 Kraus 完成，逐步定义（13.1）。不同步的载体维数可以不同；部分等距的实际输入域与输出像仍等维，补空间处理使每个门全域保迹。初始标量按空档案编码，旧旗标保持吸收。

任一终端的连续成功分支，正是原来源投影到全部前缀存活词后精确编码的分支。由（13.5）的共同事件，两种初位的累计失败概率均至多 $`\delta`$。首位正交性使完整失败效果不超过 $`\delta I_M`$；因此对全部相位、初始相干与任意参考成立。终端在成功块反向展开、在旗标块输出任意固定态，纯化后的目标重叠至少为 $`(1-\delta)^2`$。半迹误差至多 $`\sqrt{2\delta}=\epsilon`$，与终端深度无关。

长度为 $`2b_n`$ 的荷区间最多含 $`\lfloor2b_n\rfloor+1`$ 个整数，四个首末扇区加一维旗标给（13.4）。对 $`n\ge2`$，$`2^{r(n)}\le2n`$ 且 $`\log(2/\delta_{r(n)})=\log(2\pi^2r(n)^2/(3\epsilon^2))`$，故（13.2）成立；$`n=1`$ 可由常数项涵盖。证明完毕。

**定义 13.3（硬区间与一维不可恢复失败旗标）。** 给定非负确定带宽序列 $`b=(b_n)`$。取上一证明的全前缀存活空间和部分等距编码；每次失败把全部输入补空间送入同一个一维旗标，随后旗标永久吸收，且没有其他持久失败档案。终端解码任意，但不得依赖实际相位。令

$$
s_n={1\over2}\sum_{i=0}^1
\Pr_i\{|S_t-t\mu|\le b_t\text{ 对所有 }1\le t\le n\}.
\tag{13.8}
$$

这是本卷 Bell 初始输入的连续成功质量。

**定理 13.4（存活消失时，联合恢复误差趋于一）。** 对定义13.3中的接收器，在 Bell 初始输入上，任意允许解码器的最坏相位半迹误差满足

$$
\sup_\vartheta
D\bigl(\widehat\Omega_{\vartheta,n},\Omega_{\vartheta,n}\bigr)
\ge(1-s_n)(1-\beta_n),
\qquad
\beta_n={\sqrt\pi\over2\sqrt{\alpha^3\lfloor(n-1)/3\rfloor}}
\quad(n\ge4).
\tag{13.9}
$$

特别地，若 $`s_n\to0`$，最坏误差趋于一。令

$$
\sigma^2={p(1-p)\over(1+p)^3}>0.
\tag{13.10}
$$

若

$$
\limsup_{n\to\infty}{b_n\over\sqrt{2\sigma^2 n\log\log n}}<1,
\tag{13.11}
$$

则 $`s_n\to0`$，上述恢复失败成立。因此任意固定 $`C<\infty`$ 的 $`b_n=C\sqrt n`$ 均不能使这个装置类保持小于一的统一误差。

式（13.9）的对象是定义13.3指定的吸收截断码；一般 CPTP 接收器可保留其他失败信息或使用混合的中间表示，本定理不对它们给出迭代对数容量下界。定理13.2提供一个无终端构造，定理5.3只对任意此类构造给逐终端平方根下界，两者之间的迭代对数差距未由这里的证明消除。

证明。记 $`Q_n`$ 为完整档案中选取全部存活计算基词的投影。对 Bell 来源，目标为 $`\Omega_{\vartheta,n}=|\Psi_\vartheta\rangle\langle\Psi_\vartheta|`$。其共同相位作用只在档案一侧，且与 $`Q_n`$ 对易。因此原始 $`JM`$ 边缘和成功分支的 $`JM`$ 边缘均不依赖相位。局部保迹接收不改变总 $`JM`$ 边缘，所以失败分支的未归一化 $`JM`$ 态也不依赖相位：它是这两个边缘之差。

定义13.3的实际输出按成功块与旗标块分块对角，且旗标仅一维。于是解码后的失败项是同一个相位无关的正算子 $`\Gamma_n`$，其迹为 $`1-s_n`$；成功项的迹为 $`s_n`$。这不要求丢弃环境独立于相位，只要求它不再进入接收器和解码器。

以目标纯态投影配对，成功项贡献不超过 $`s_n`$。由（5.15）、（5.18），相位平均目标的谱范数至多 $`\beta_n`$，故

$$
\begin{aligned}
{1\over2\pi}\int_{-\pi}^{\pi}
\langle\Psi_\vartheta|\widehat\Omega_{\vartheta,n}|\Psi_\vartheta\rangle
\,d\vartheta
&\le s_n+\operatorname{Tr}(\overline\Omega_n\Gamma_n)\\
&\le s_n+(1-s_n)\beta_n.
\end{aligned}
\tag{13.12}
$$

半迹距离至少为目标纯态检验的概率差。取相位上确界不小于相位平均，得到（13.9）。半迹距离至多一；$`s_n\to0`$ 与 $`\beta_n\to0`$ 因而给趋于一。

余下验证（13.11）确实使存活消失。实际二状态链有严格正的平稳分布
 $`\pi=(1/(1+p),p/(1+p))`$，不可约且有自环。对 $`g(x)=x-\mu`$，有 $`Pg=-pg`$。因此 $`g`$ 有零平稳均值且有界，$`\sum_{k=0}^{n-1}P^kg`$ 的 $`L^2(\pi)`$ 范数一致有界，满足 Miao–Yang 的 Markov 加性泛函迭代对数律条件。[^phase_anytime_lil]

更明确地，Poisson 方程的解为 $`h=g/(1+p)`$，其鞅增量为
 $`H(x,y)=h(y)-Ph(x)=(g(y)+pg(x))/(1+p)`$。
当 $`x=1`$ 时增量为零；当 $`x=0`$ 时分子分别以概率 $`1-p,p`$ 取 $`-p,1-p`$。故平稳二阶矩为

$$
\mathbb E_\pi H(X_0,X_1)^2
={1\over1+p}\,{p(1-p)\over(1+p)^2}
=\sigma^2.
\tag{13.13}
$$

该标准迭代对数律对 $`g`$ 与 $`-g`$ 分别给

$$
\limsup_{n\to\infty}{S_n-n\mu\over\sqrt{2\sigma^2 n\log\log n}}=1,
\qquad
\liminf_{n\to\infty}{S_n-n\mu\over\sqrt{2\sigma^2 n\log\log n}}=-1
\quad\text{几乎必然}.
\tag{13.14}
$$

改变求和起点只差有界端项。由于两个初位的平稳权重均严格正，平稳律下的概率一结论在分别固定每个初位后也为概率一。（13.11）于是保证几乎每条路径最终越界，乃至无穷次越界。全前缀存活事件随 $`n`$ 递减，连续性给两个初位的存活概率均趋零，即 $`s_n\to0`$。证明完毕。

[^phase_anytime_stitching]: Steven R. Howard、Aaditya Ramdas、Jon McAuliffe、Jasjeet Sekhon，*Time-uniform, nonparametric, nonasymptotic confidence sequences*，[arXiv:1810.08240v9，Theorem 1、§3.1](https://arxiv.org/html/1810.08240v9#S3.SS1)。几何时域分配与 stitched boundary 是既有概率方法；本节通过来源的首末荷空间递推，把同一个无限时域事件实现为保持参考联合态的接收门序列。

[^phase_anytime_lil]: Yu Miao and Guangyu Yang，*The law of the iterated logarithm for additive functionals of Markov chains*，Statistics & Probability Letters **78** (2008)，[doi:10.1016/j.spl.2007.05.032](https://doi.org/10.1016/j.spl.2007.05.032)，[arXiv:math/0701167v2，Theorem 2.4](https://arxiv.org/pdf/math/0701167v2#page=3)。该定理的条件为平稳遍历链、$`g\in L_0^2(\pi)`$ 以及 $`\|\sum_{k<n}P^kg\|_2=O(n^a)`$ 对某个 $`a<1/2`$ 成立；本文通过 $`Pg=-pg`$ 和（13.13）核对条件及方差，只将已知迭代对数律作为接收失败证明的中间步骤。

## 追加锚（本行以下为增补区）


## 14. 一般有限维来源的收缩谱障碍

**定义 14.1（固定等距来源及实际谱分量）。** 取有限维非零空间 $`M,B`$ 和固定等距

$$
T:M\longrightarrow M\otimes B,
\qquad E(X)=\operatorname{Tr}_B(TXT^*),
\qquad m=\dim M.
\tag{14.1}
$$

每次只对活动 $`M`$ 重复同一个发射，已有档案不再作用于来源。固定纯初态 $`\rho_0=|\psi\rangle\langle\psi|`$，记 $`\rho_n=E^n(\rho_0)`$，其未接收的完整记忆—档案目标为纯态。对复线性映射 $`E`$ 的广义特征空间分解，记谱投影为 $`P_\lambda`$，称 $`\lambda`$ 在此来源轨道上实际出现，若 $`P_\lambda\rho_0\ne0`$。

接收器为有限维 $`K`$、独立纯初态及同一个全域 CPTP 通道 $`\mathcal C:\mathcal L(K\otimes B)\to\mathcal L(K)`$。每轮新环境可以丢弃，全部持久接收系统计入 $`K`$，不访问活动 $`M`$；终端局部解码器可依赖编号。只要求恢复这一个指定纯来源的完整联合目标，已经构成下面的必要条件。

**定理 14.2（非零收缩谱阻止有限固定精确接收）。** 若存在实际出现的谱值满足

$$
0<|\lambda|<1,
\tag{14.2}
$$

则定义14.1的任务不存在服务全部终端的有限固定接收器。令 $`c_\rho=\dim_{\mathbb C}\operatorname{span}\{E^n(\rho_0):n\ge0\}\le m^2`$。若一个 $`D`$ 维固定接收器精确服务前 $`N`$ 个终端，则

$$
\boxed{
N<m^2D^2c_\rho\le m^4D^2,
\qquad D>\sqrt{\frac{N}{m^2c_\rho}}\ge\frac{\sqrt N}{m^2}.
}
\tag{14.3}
$$

因此，若同一接收器还须对全部初始态精确服务全部终端，则源边缘通道必须满足

$$
\operatorname{spec}(E)\subseteq\{0\}\cup\{z\in\mathbb C:|z|=1\}.
\tag{14.4}
$$

这是必要条件，不在本定理中宣称充分。零特征值对应的有限幂零暂态不受（14.2）排除；非平凡单位圆谱也没有被当作收缩模式。

证明。先说明所需的谱性质。设有限维线性轨道 $`x_n=L^nx_0`$ 去掉零特征值的有限幂零前缀后写为

$$
x_n=\sum_{\lambda\in\Lambda}\lambda^n A_\lambda(n),
\qquad r_x=\min_{\lambda\in\Lambda}|\lambda|>0,
\tag{14.5}
$$

其中各 $`A_\lambda`$ 为非零向量多项式，$`\Lambda`$ 只收录实际非零谱。对任意正定内积，平方范数是基底 $`\overline\lambda\mu`$ 的指数多项式；其所有基底模至少为 $`r_x^2`$，而正实基底 $`r_x^2`$ 的系数恰为

$$
\sum_{|\lambda|=r_x}\|A_\lambda(n)\|^2\ne0.
\tag{14.6}
$$

这是（10.10）—（10.11）的同一有限谱事实，不要求正规性、对角化或最低模谱值唯一。

另取自主轨道 $`y_n=L'^ny_0`$，实际最低非零谱模为 $`r_y`$。其张量轨道由 $`L\otimes L'`$ 生成，实际最低非零谱模严格等于 $`r_xr_y`$。为核对可能的谱乘积碰撞，把两个空间分别分解为广义特征空间 $`G_\lambda,H_\mu`$。各
 $`G_\lambda\otimes H_\mu`$
仍构成直和，并对 $`L\otimes L'`$ 不变；当 $`\lambda\mu\ne0`$ 时，这一块可逆且只有谱值 $`\lambda\mu`$。初始分量为两个实际谱投影之张量，二者非零就给非零张量。即使不同谱对具有同一个乘积，它们也处于不同直和块，不能相消。因此

$$
r_{x\otimes y}=r_xr_y.
\tag{14.7}
$$

这一步使用完整算子轨道的直和分量，不把任意标量指数级数的乘积误认作无抵消。

现在假设有限固定精确接收存在。把一次发射与接收合成 $`H=M\otimes K`$ 上的固定通道 $`\mathcal R`$，得到 $`\sigma_n=\mathcal R^n\sigma_0`$。局部保迹接收不改变活动边缘，所以 $`\operatorname{Tr}_K\sigma_n=\rho_n`$。记两个完整轨道的实际最低非零谱模为 $`r_E,r_{\mathcal R}`$。迹为一使两者的实际非零谱集非空；有限维通道的谱位于闭单位盘，条件（14.2）故给 $`0<r_E<1`$。

对每个终端的解码作纯化，目标纯态强制与其余环境成乘积，正如（10.7）。由纯化两侧非零谱相同，精确接收必须满足

$$
\|\operatorname{Tr}_M\sigma_n\|_{\rm HS}^2
=\|\rho_n\|_{\rm HS}^2\|\sigma_n\|_{\rm HS}^2
=\|\rho_n\otimes\sigma_n\|_{\rm HS}^2.
\tag{14.8}
$$

左侧由对 $`\sigma_n`$ 施加线性偏迹后再取平方范数得到，因此没有模小于 $`r_{\mathcal R}^2`$ 的指数基底。右侧由（14.7）、（14.6），必有非零的正实基底

$$
(r_Er_{\mathcal R})^2<r_{\mathcal R}^2.
\tag{14.9}
$$

不同非零基底的指数多项式在整数尾部线性独立，矛盾。这里的 $`\rho_n\otimes\sigma_n`$ 是证明中的数学张量轨道，没有要求接收器复制未知量子态。

再证明显式有限时域界。取一份固定 Kraus 表 $`\mathcal R(X)=\sum_u L_uXL_u^*`$，并按（12.4）保留其词环境。精确终端恢复强制对全部同长度词 $`w,v`$ 及 $`A\in\operatorname{End}(M)`$ 有

$$
\langle\xi_0|L_w^*(A\otimes I_K)L_v|\xi_0\rangle
=\operatorname{Tr}[\rho_0(E^*)^n(A)]
\langle\xi_0|L_w^*L_v|\xi_0\rangle,
\quad |w|=|v|=n,
\tag{14.10}
$$

其中 $`|\xi_0\rangle=|\psi\rangle_M|e\rangle_K`$、$`\sigma_0=|\xi_0\rangle\langle\xi_0|`$。该式与记忆及累计环境的乘积分解逐矩阵元等价。

用实际来源轨道的线性空间
 $`C_\rho=\operatorname{span}_{\mathbb C}\{\rho_n:n\ge0\}`$
及其限制映射 $`F=E|_{C_\rho}`$ 表示右侧的时间因子。记 $`t(x)=\operatorname{Tr}x`$、$`a_A(x)=\operatorname{Tr}(xA)`$ 为 $`C_\rho`$ 上的线性泛函；有 $`t(\rho_0)=1`$ 及 $`F^\vee t=t`$，其中 $`F^\vee f=f\circ F`$。取

$$
\mathcal V=\operatorname{End}(H)\otimes C_\rho^*,
\qquad v:=\dim\mathcal V=m^2D^2c_\rho,
\tag{14.11}
$$

并在线性延拓意义下定义

$$
\begin{aligned}
g_A&=(A\otimes I_K)\otimes t-I_H\otimes a_A,\\
\ell(X\otimes f)&=\operatorname{Tr}(\sigma_0X)f(\rho_0),\\
\mathcal L_{uv}(X\otimes f)&=L_u^*XL_v\otimes F^\vee f.
\end{aligned}
\tag{14.12}
$$

长度 $`n`$ 的字母对复合把 $`g_A`$ 送到

$$
L_w^*(A\otimes I_K)L_v\otimes t
-L_w^*L_v\otimes(F^\vee)^n a_A.
\tag{14.13}
$$

用 $`\ell`$ 读取该式，恰得到（14.10）两侧之差；迹泛函的固定性使第一项不增加时间因子。与（12.12）相同，累计生成空间在至多 $`v`$ 层后稳定；长度零的等式由 $`\operatorname{Tr}_K\sigma_0=\rho_0`$ 自动成立。若前 $`v`$ 个终端均精确，$`\ell`$ 就在整个稳定空间上恒零，使（14.10）在全部长度成立。环境乘积分解随之对全部终端成立，并直接给出已被（14.9）排除的（14.8）。不需要假设合同之外存在解码器。因此 $`N<v`$，即得（14.3）。这里 $`c_\rho`$ 计数实际来源轨道的独立线性方向；定义9.1的非退化两态来源在第12节所选初态 $`\rho_0=|0\rangle\langle0|`$ 上有 $`c_\rho=2`$，因而本界恢复（12.1）的 $`8D^2`$ 时域。
最后，假如 $`E`$ 具有任意非零收缩谱值，其非零谱投影不可能消去全部纯态投影，因为纯态投影复线性张成 $`\operatorname{End}(M)`$。故总能选择一个纯初态使该谱值实际出现；对全部初始态的任务必须包含这个初态，前述不能性适用。于是（14.4）必要。证明完毕。

## 追加锚（本行以下为增补区）


## 15. 固定物理接收器存在的外围谱判据

本节固定一个已知的有限维等距来源

$$
T:M\longrightarrow M\otimes\mathcal B,\qquad m=\dim M\ge1,
\qquad E(X)=\operatorname{Tr}_{\mathcal B}(TXT^\dagger).
\tag{15.1}
$$

全部发出系统都属于待恢复档案，来源没有另外丢弃、却不计入档案的环境。接收合同沿用定义10.1：一个有限寄存器 $`K`$ 从与来源独立的固定纯态开始；每步使用同一个全域 CPTP 映射 $`\mathcal C:\mathcal L(K\otimes\mathcal B)\to\mathcal L(K)`$；不访问参考或活动来源、不反馈来源；所有持久控制计入 $`K`$。每个终端可以使用依赖终端编号、只作用于 $`K`$ 的解码器，必须对全部有限参考 $`J`$ 和全部输入 $`\rho_{JM}`$ 精确恢复参考、活动来源与完整档案的联合态。

**定理 15.1（固定 CPTP 精确接收的谱充要条件）。** 上述合同存在有限维实现，当且仅当

$$
\operatorname{spec}_{\mathbb C}(E)
\subseteq\{0\}\cup\{z\in\mathbb C:|z|=1\}.
\tag{15.2}
$$

成立时可取

$$
\dim K\le m^4+m^3.
\tag{15.3}
$$

此界只给统一有限上界，不主张最优。装置可以依赖已知的 $`T`$，但不依赖实际输入、参考或未来终端。

证明。必要性由定理14.2末段：任一非零严格收缩谱投影都在某个纯初始态上非零，而全部输入合同必须包含该初态；该定理因而排除有限固定接收。以下证明充分性。

**有限启动后精确进入外围空间。** 有限维 CPTP 映射的幂一致有界，因此单位模特征值的 Jordan 块均为一阶。在（15.2）下，其余 Jordan 块全部属于零特征值。令 $`L\ge1`$ 为零 Jordan 块的最大长度；无零块时取 $`L=1`$。于是

$$
1\le L\le m^2,\qquad
\operatorname{ran}E^L=X_E,
\tag{15.4}
$$

其中 $`X_E`$ 是全部单位模特征空间的复线性张成。这是有限步的精确等式，不是渐近近似。

Wolf–Pérez-García 的外围空间结构定理给出原 Hilbert 空间的正交分解与正定密度矩阵：[^phase_peripheral_structure]

$$
M=M_0\oplus\bigoplus_{k=1}^{s}(A_k\otimes B_k),
\qquad
X_E=0\oplus\bigoplus_{k=1}^{s}\mathcal L(A_k)\otimes\tau_k.
\tag{15.5}
$$

存在块置换 $`p`$ 及酉识别 $`U_k:A_k\to A_{p(k)}`$，使

$$
E\bigl(\iota_k(X\otimes\tau_k)\bigr)
=\iota_{p(k)}\bigl(U_kXU_k^\dagger\otimes\tau_{p(k)}\bigr).
\tag{15.6}
$$

这里 $`\iota_k`$ 表示嵌入第 $`k`$ 个来源块。只有 $`\dim A_k=\dim A_{p(k)}`$ 是必需条件；不要求 $`r_k:=\dim B_k`$ 沿置换循环保持相同。

**一次共同的启动编码。** 记 $`P_k`$ 为来源块投影，定义

$$
F_k(X)=\operatorname{Tr}_{B_k}\bigl(P_kE^L(X)P_k\bigr).
\tag{15.7}
$$

这是完全正映射，且由（15.4）—（15.5），

$$
E^L(X)=\bigoplus_k F_k(X)\otimes\tau_k,
\qquad
\sum_k\operatorname{Tr}F_k(X)=\operatorname{Tr}X.
\tag{15.8}
$$

为每个 $`F_k`$ 取最小 Kraus 实现

$$
V_k:M\longrightarrow A_k\otimes Q_k,
\qquad
F_k(X)=\operatorname{Tr}_{Q_k}(V_kXV_k^\dagger),
\qquad q_k:=\dim Q_k\le m\dim A_k.
\tag{15.9}
$$

各 $`V_k`$ 不必分别等距，但 $`\sum_kV_k^\dagger V_k=I_M`$。取 $`q=\max_kq_k`$ 维公共空间 $`Q`$，固定等距 $`j_k:Q_k\to Q`$，并令 $`\widetilde V_k=(I\otimes j_k)V_k`$。

取 $`\tau_k`$ 的最小纯化

$$
|\Xi_k\rangle\in B_k\otimes R_k,
\qquad \dim R_k=r_k,
\qquad K_{\rm run}=Q\otimes\bigoplus_kR_k.
\tag{15.10}
$$

按固定张量因子次序，将

$$
W_{\rm can}|\psi\rangle
=\sum_k\widetilde V_k|\psi\rangle\otimes|\Xi_k\rangle
\in M\otimes K_{\rm run}
\tag{15.11}
$$

解释为等距：其中 $`A_kB_k`$ 属于来源，第 $`k`$ 个 $`QR_k`$ 属于接收器。不同 $`R_k`$ 正交，故迹掉接收器所得通道正是 $`E^L`$。式（15.11）是相干求和，不是测量块标签后选择分支。

令 $`W_t:M\to M\otimes\mathcal B^{\otimes t}`$ 为真实来源的 $`t`$ 步发射等距，只将活动来源写在张量积前方。定义统一实际档案支撑

$$
S_t=\operatorname{span}\{
(\langle u|_M\otimes I)W_t|v\rangle:
u,v\in M\}
\subseteq\mathcal B^{\otimes t}.
\tag{15.12}
$$

于是

$$
S_0=\mathbb C,\qquad
\dim S_t\le m^2,\qquad
S_{t+1}\subseteq S_t\otimes\mathcal B.
\tag{15.13}
$$

维数界来自输入和活动来源各有 $`m`$ 个基向量；包含关系来自下一次发射只作用于活动来源。这一支撑同时容纳全部输入及全部参考，未依实际态选择。

由于 $`W_L`$ 与 $`W_{\rm can}`$ 给出同一个来源通道，存在一个等距

$$
C_L:S_L\longrightarrow K_{\rm run},
\qquad
(I_M\otimes C_L)W_L=W_{\rm can}.
\tag{15.14}
$$

这是最小实际环境上的 Stinespring 唯一性，也可直接由 Gram 矩阵证明：在输入和来源输出基下，两份等距的档案系数向量具有相同的全部内积，因为这些内积就是 $`E^L(|i\rangle\langle j|)`$ 的矩阵元。因此把真实系数送到规范系数的线性映射良定且等距。这里比较的是整个通道的一份共同编码，已经固定不同块的相对相位。

**一个保持块相干的固定运行吸收器。** 对每个 $`k`$，在 $`B_kR_k`$ 上准备 $`\Xi_k`$，让实际来源 $`T`$ 作用于 $`A_kB_k`$。这给出一个等距

$$
W_k:A_k\longrightarrow M\otimes\mathcal B\otimes R_k.
\tag{15.15}
$$

它的来源边缘通道由（15.6）给出。该通道的另一份最小 Stinespring 等距为

$$
Z_k|v\rangle
=\iota_{p(k)}\bigl(U_k|v\rangle\otimes|\Xi_{p(k)}\rangle\bigr)
\in M\otimes R_{p(k)}.
\tag{15.16}
$$

由于 $`\tau_{p(k)}`$ 正定，这份环境的支撑是整个 $`R_{p(k)}`$。Stinespring 唯一性因而给一个等距

$$
J_k:R_{p(k)}\longrightarrow\mathcal B\otimes R_k,
\qquad
W_k=(I_M\otimes J_k)Z_k.
\tag{15.17}
$$

这是对整个输入空间 $`A_k`$ 的线性等式，因此即使 $`A_k`$ 与任意参考及 $`Q`$ 纠缠也成立。它也直接蕴含 $`r_{p(k)}\le(\dim\mathcal B)r_k`$，无需另加相同噪声秩的假设。

在 $`K_{\rm run}\otimes\mathcal B`$ 上定义单个部分等距 $`A`$：将第 $`k`$ 块按固定张量次序写成 $`Q\otimes\mathcal B\otimes R_k`$ 后，在 $`Q\otimes\operatorname{ran}J_k`$ 上施加 $`I_Q\otimes J_k^\dagger`$，输出放入第 $`p(k)`$ 块；在这些成功子空间的正交补上取零。

输入块彼此正交，输出块也因 $`p`$ 是置换而彼此正交。因此

$$
AA^\dagger=I_{K_{\rm run}},\qquad
P:=A^\dagger A\text{ 是成功支撑投影}.
\tag{15.18}
$$

取任意固定运行态 $`\omega`$，定义

$$
\mathcal C_{\rm run}(X)
=AXA^\dagger+\operatorname{Tr}[(I-P)X]\,\omega.
\tag{15.19}
$$

这是一份全域 CPTP 映射。成功部分必须是单个 Kraus 算子 $`A`$；若将每个块分别作为一个成功 Kraus 算子，就会测量并消除块间相干，不能用于本合同。

为验证实际运行永不离开成功支撑，考虑以下共同纯化子空间：

$$
\Gamma((\xi_k)_k)
=\sum_k\xi_k^{A_kQ}\otimes\Xi_k^{B_kR_k},
\qquad
\xi_k\in A_k\otimes Q.
\tag{15.20}
$$

它包含（15.11）的全部像。由（15.17），一次真实发射加（15.19）把（15.20）精确送到同一形式，其中

$$
\xi'_{p(k)}=(U_k\otimes I_Q)\xi_k.
\tag{15.21}
$$

发射后的接收输入全部位于 $`P`$；补空间重置项的概率为零。式（15.21）是一份块置换加酉的线性等式，既保持块内参考纠缠，也保持不同块之间的相干。因而此性质可以无限迭代，且不用外部时钟切换运行门。

**把有限启动和运行装成同一台机器。** 对 $`0\le t<L`$，令 $`K_t`$ 为 $`S_t`$ 的一份等距副本，取固定编码 $`C_t:S_t\to K_t`$，其中 $`K_0=\mathbb C|e\rangle`$。最后一步编码使用（15.14）。由（15.13），每个启动转移可以在实际输入子空间

$$
(C_t\otimes I_{\mathcal B})S_{t+1}
\subseteq K_t\otimes\mathcal B
\tag{15.22}
$$

上实现规定的等距编码；在其正交补上输出任意固定态，就得到全域 CPTP 映射。目标扇区在 $`t+1<L`$ 时为 $`K_{t+1}`$，在 $`t+1=L`$ 时为 $`K_{\rm run}`$。

取总寄存器

$$
K=\bigoplus_{t=0}^{L-1}K_t\oplus K_{\rm run}.
\tag{15.23}
$$

按输入阶段扇区投影，随后施加对应启动通道或运行通道，构成一份固定全域 CPTP 映射 $`\mathcal C`$。实际时刻的阶段标签确定：前 $`L`$ 步顺次经过启动扇区，此后永久处于运行扇区。因此阶段投影不删除任何实际来源与参考的相干；它没有测量运行扇区内部的 $`k`$ 标签。接收初态为固定独立纯态 $`|e\rangle`$，全部阶段控制已纳入 $`K`$。

**全部终端的本地精确解码。** 还须证明运行编码在完整档案支撑上等距，而不只在各个单独输入上保持概率。对 $`n\ge L`$ 递归定义

$$
C_{n+1}
=A(C_n\otimes I_{\mathcal B})\big|_{S_{n+1}}.
\tag{15.24}
$$

假设 $`C_n`$ 是等距，且实际接收后的等距为 $`(I_M\otimes C_n)W_n`$。由（15.20）—（15.21），对每个源输入 $`v`$，下一次发射后的向量属于 $`M\otimes\operatorname{ran}P`$。对其活动来源系数逐个取内积，并用（15.12）张成定义，得到

$$
(C_n\otimes I_{\mathcal B})S_{n+1}
\subseteq\operatorname{ran}P.
\tag{15.25}
$$

在这个子空间上 $`A`$ 等距，所以（15.24）是整个 $`S_{n+1}`$ 上的等距，且继续给出相同的实际编码恒等式。由（15.14）开始归纳，每个 $`n`$ 都得到一个与输入、参考无关的共同等距 $`C_n:S_n\to K`$。将 $`C_n`$ 在 $`S_n`$ 的正交补上延零；目标 $`\Omega_n`$ 本来支撑于 $`JM\otimes S_n`$。于是

$$
\sigma_n(\rho)
=(I_{JM}\otimes C_n)\Omega_n(\rho)(I_{JM}\otimes C_n^\dagger)
\quad\text{对全部 }J,\rho_{JM}.
\tag{15.26}
$$

将 $`C_n^\dagger`$ 的值域 $`S_n`$ 嵌回完整档案空间，记所得算子为 $`R_n:K\to\mathcal B^{\otimes n}`$。取任意固定档案态 $`\zeta_n`$，则

$$
\mathcal D_n(X)
=R_nXR_n^\dagger
+\operatorname{Tr}[(I_K-C_nC_n^\dagger)X]\,\zeta_n
\tag{15.27}
$$

是只作用于接收器的全域 CPTP 解码器，并由（15.26）恢复完整 $`JM\mathcal B^{\otimes n}`$ 联合态。参考完整性来自统一线性等距恒等式，不需要逐输入选择恢复映射。

等价地，对 $`n>L`$ 可反复施加 $`A^\dagger`$ 恢复后续发出系统，再逆启动编码；$`AA^\dagger=I`$ 保证反向运行本身等距，且在实际像上回到正确的历史支撑。早期接收操作与后续只作用于活动来源的发射可交换位置，因此整个解码电路不访问活动来源。

**容量账。** 由（15.5），

$$
\sum_kr_k\le\sum_k(\dim A_k)r_k\le m,
\qquad q\le m\max_k\dim A_k\le m^2.
\tag{15.28}
$$

于是

$$
\begin{aligned}
\dim K
&=\sum_{t=0}^{L-1}\dim S_t+q\sum_kr_k\\
&\le1+(L-1)m^2+m^3\\
&\le m^4+m^3,
\end{aligned}
\tag{15.29}
$$

最后一步使用 $`L\le m^2`$ 和 $`m\ge1`$。所有持久启动、块标签、纯化与 Kraus 记忆均已计入。证明完毕。

本判据区分两种量词：每个固定终端的实际档案支撑始终不超过 $`m^2`$，但要让一个独立初始化、固定 CPTP 的有限物理装置连续维护精确边界，还必须排除全部非零严格收缩谱模。单位模部分可以永久可逆地运行，零谱部分可以在有限启动内消去。结论不要求外围相位是单位根，也没有声称同维固定酉、无丢弃环境的接收合同成立。

[^phase_peripheral_structure]: Michael M. Wolf and David Pérez-García, *The Inverse Eigenvalue Problem for Quantum Channels*, [arXiv:1005.4545v1, Theorem 8, pp.10–11, equations (22)–(24)](https://arxiv.org/pdf/1005.4545v1#page=10). 原定理适用于保迹 Schwarz 映射，文中定义为其对偶满足 Schwarz 不等式；CPTP 映射属于此类。定理给原 Hilbert 空间在某个正交基下的分解，允许瞬态空间及不同噪声块维数。原文输出第 $`k`$ 块读取输入第 $`\pi(k)`$ 块，本节用 $`p=\pi^{-1}`$ 写成输入块到输出块的方向。原定理只描述外围空间；有限步进入该空间由本节的额外谱假设（15.2）和 Jordan 分解提供。固定接收器及容量上界是本节在该结构上的组合推导，不是原定理的原有结论。

## 追加锚（本行以下为增补区）


## 16. 一般有限维来源的统一近似接收

本节保留（15.1）的已知等距来源、独立纯初始化、固定全域 CPTP 接收器、局部访问权限及全部持久控制计费，但不再假设（15.2）。误差仍比较任意参考、活动来源与完整档案的联合态。记半迹距离为 $`d(\rho,\sigma)=\frac12\|\rho-\sigma\|_1`$；在每个指定终端 $`n`$，仅对接收器实施可依赖 $`n`$ 的解码。解码后继续运行、由未知态决定停止、或中途干预来源，不属于本节合同。

**定义 16.1（外围投影与启动偏差）。** 令 $`\Pi`$ 为 $`E`$ 的全部单位模特征空间之和上的谱投影，沿其余广义特征空间投影。置

$$
\delta_L=\|E^L-E^L\Pi\|_\diamond,
\qquad L\ge1.
\tag{16.1}
$$

这里使用通道的完整 diamond 范数，没有额外除以二。

**定理 16.2（任意固定正精度下的有限固定接收）。** 对任意（15.1）的有限维等距来源及任意 $`0<\epsilon<1`$，存在一台有限维、独立初始化、固定 CPTP 接收器，及一族只作用于接收器的终端解码器，使

$$
\sup_{n\ge1}\ \sup_{J,\rho_{JM}}
d\left((\operatorname{id}_{JM}\otimes\mathcal D_n)\sigma_n(\rho),
\Omega_n(\rho)\right)\le\epsilon.
\tag{16.2}
$$

更具体地，$`\Pi`$ 是 CPTP，且 $`\delta_L\to0`$。任取满足 $`2\sqrt{\delta_L}\le\epsilon`$ 的 $`L\ge1`$，可取

$$
\boxed{
\dim K\le 1+(L-1)m^2+2m^3.
}
\tag{16.3}
$$

对固定已知来源，故有容量上界 $`O_E(1+\log(1/\epsilon))`$。其中常数可以依赖来源通道的衰减谱及维数；不主张对所有通道给出相同的混合速率或最优容量。若（15.2）成立，前节已经给出精确有限接收，无需使用本节误差容限。

证明。分开建立外围近似、共同启动编码和全时域误差比较。

**外围投影本身是合法通道。** 有限维 CPTP 映射的幂一致有界，所以单位模特征值没有非平凡 Jordan 块。对有限个外围相位，取一列趋于无穷的整数 $`n_j`$，使所有相位的 $`n_j`$ 次幂同时趋于一；有限周期情形取共同周期的倍数，一般情形由有限维环面上的同时逼近得到。其余广义特征空间上的幂趋于零。因此

$$
E^{n_j}\longrightarrow\Pi,
\qquad E\Pi=\Pi E,
\qquad \operatorname{ran}\Pi=X_E.
\tag{16.4}
$$

在有限维空间中，CPTP 映射集合闭，故 $`\Pi`$ 是 CPTP。来源具有固定态，所以外围空间非零。这一取极限构造也出现在前节所引外围结构定理的证明中。

于是 $`\widetilde E_L:=E^L\Pi`$ 是 CPTP，并且其像等于 $`X_E`$。差映射 $`E^L(I-\Pi)`$ 只含模小于一的谱。零谱部分在有限步消失，其余 Jordan 项为指数乘多项式，所以在 diamond 范数下也有 $`\delta_L\to0`$。

**一个对全部输入共同有效的启动编码。** 使用（15.5）—（15.6）的外围分解。这份结构对一般 $`E`$ 同样成立；本节仅将前节的 $`E^L`$ 换成 $`\widetilde E_L`$ 来定义各 CP 分支及其 Kraus 算子。取

$$
\dim Q=2m^2,
\qquad K_{\rm run}=Q\otimes\bigoplus_kR_k,
\qquad \dim R_k=\dim B_k=r_k.
\tag{16.5}
$$

各分支的最小 Kraus 空间维数至多 $`m\dim A_k\le m^2`$，因而都能嵌入此公共 $`Q`$。按（15.11）构造 $`\widetilde E_L`$ 的规范 Stinespring 等距

$$
\widetilde W_L:M\longrightarrow M\otimes K_{\rm run}.
\tag{16.6}
$$

其像处于（15.20）的共同纯化子空间。它同时保存输入与参考关联，以及不同外围块之间的相干。

对 $`E^L`$ 与 $`\widetilde E_L`$ 应用 Stinespring 连续性定理。[^phase_stinespring_continuity] 该定理对 Heisenberg 对偶的 cb 范数给出共同膨胀的算子范数界；有限维对偶关系将其改写为本节的 diamond 范数。两份最小环境维数各至多 $`m^2`$，共同环境可取它们的直和，故维数至多 $`2m^2`$。于是存在同环境上的等距 $`V,\widetilde V`$，分别表示这两个通道，并满足

$$
\|V-\widetilde V\|_{\rm op}\le\sqrt{\delta_L}.
\tag{16.7}
$$

由于 $`\sum_kr_k\ge1`$，（16.5）的环境维数至少为 $`2m^2`$。把上述共同环境嵌入 $`K_{\rm run}`$；$`\widetilde V`$ 与固定的规范等距 $`\widetilde W_L`$ 表示同一通道，其实际环境支撑之间的等距可在同维的整个环境上扩展成一个酉。将这个共同酉同时作用于两份膨胀，就能保持（16.7），并使理想膨胀恰为 $`\widetilde W_L`$。

真实 $`L`$ 步等距 $`W_L`$ 的实际档案支撑为（15.12）的 $`S_L`$。Stinespring 唯一性给出一个共同等距

$$
C_L:S_L\longrightarrow K_{\rm run},
\qquad
\|(I_M\otimes C_L)W_L-\widetilde W_L\|_{\rm op}
\le\sqrt{\delta_L}.
\tag{16.8}
$$

它不依赖实际输入或参考。对任意参考纠缠纯输入，两个输出向量的范数差仍至多 $`\sqrt{\delta_L}`$；归一化纯态的半迹距离不超过相应向量范数差。再对混态取纯化并偏迹，得到统一比较

$$
d(\alpha_L(\rho),\widetilde\alpha_L(\rho))
\le\eta_L:=\sqrt{\delta_L},
\tag{16.9}
$$

其中 $`\alpha_L`$ 是真实档案经 $`C_L`$ 编码后的 $`JMK_{\rm run}`$ 态，$`\widetilde\alpha_L`$ 是规范膨胀（16.6）的输出态。

**固定运行且不累积误差。** 前 $`L`$ 步完全使用真实档案支撑 $`S_t`$ 作精确启动压缩，最后编码为（16.8）。因此启动期间没有近似损失；（16.9）只是对实际启动状态与理想比较状态的距离估计。

运行通道使用（15.17）—（15.19）的同一个部分等距 $`A`$，只将公共 $`Q`$ 扩大到（16.5）的维数。它仍满足

$$
AA^\dagger=I_{K_{\rm run}},
\qquad
\mathcal C_{\rm run}(X)
=AXA^\dagger+\operatorname{Tr}[(I-A^\dagger A)X]\omega.
\tag{16.10}
$$

理想比较态位于共同纯化子空间；真实发射加运行接收使该子空间按（15.21）内的置换和酉演化，成功概率始终为一。这里无需理想态静止，也无需外围相位为单位根。

真实启动态可以含有成功子空间外的分量，仍按同一个全域 CPTP 通道合法演化。把一次来源发射加运行接收记为 $`\mathcal R`$。对 $`n=L+\ell`$，定义

$$
\sigma_n=(\operatorname{id}_J\otimes\mathcal R^\ell)(\alpha_L),
\qquad
\widetilde\sigma_n=(\operatorname{id}_J\otimes\mathcal R^\ell)(\widetilde\alpha_L).
\tag{16.11}
$$

通道的半迹距离收缩性给

$$
d(\sigma_n,\widetilde\sigma_n)\le\eta_L
\qquad\text{对全部 }n\ge L.
\tag{16.12}
$$

没有逐步添加新的近似通道，因而这里没有 $`\ell\eta_L`$ 型累积项。

**只在接收器上解码完整档案。** 由 $`AA^\dagger=I`$，$`A^\dagger:K_{\rm run}\to K_{\rm run}\otimes\mathcal B`$ 是全域等距。对终端 $`n=L+\ell`$，反复施加它，按逆顺序恢复后 $`\ell`$ 个发出系统；最后在剩余运行寄存器上施加 $`C_L`$ 的全域 CPTP 左逆 $`\mathcal D_L`$，并把其值域嵌回前 $`L`$ 位档案。这定义只访问接收器的 $`\mathcal D_n`$。

令 $`\mathcal S_\ell`$ 表示不接收时的后 $`\ell`$ 次来源发射，并保留全部新档案。在整个共同纯化子空间上，一步发射满足

$$
(I_M\otimes A^\dagger)(I_M\otimes A)(T\otimes I_{K_{\rm run}})
=(T\otimes I_{K_{\rm run}}),
\tag{16.12a}
$$

其中接收输入按固定次序重排为 $`K_{\rm run}\otimes\mathcal B`$。该式来自发射像处于成功投影 $`A^\dagger A`$ 的范围。因此逆运行在整个理想编码子空间上确实撤销接收；较早的接收操作只作用于接收器及已发出系统，与较后的来源发射作用于不同系统。归纳作逆序撤销给

$$
(\operatorname{id}_{JM}\otimes\mathcal D_n)(\widetilde\sigma_n)
=\mathcal S_\ell\bigl((\operatorname{id}_{JM}\otimes\mathcal D_L)
(\widetilde\alpha_L)\bigr),
\tag{16.13}
$$

按固定次序重排档案张量因子。另一方面，真实启动编码可被精确逆转，故

$$
\Omega_n
=\mathcal S_\ell\bigl((\operatorname{id}_{JM}\otimes\mathcal D_L)
(\alpha_L)\bigr).
\tag{16.14}
$$

这里没有把理想比较态的解码冒认为原目标。对（16.13）与（16.14）再次使用（16.9）及通道收缩性，它们的距离至多 $`\eta_L`$。再加上（16.12）的解码后距离，得到

$$
\begin{aligned}
d\bigl((\operatorname{id}_{JM}\otimes\mathcal D_n)(\sigma_n),\Omega_n\bigr)
&\le d(\sigma_n,\widetilde\sigma_n)+\eta_L\\
&\le2\sqrt{\delta_L}.
\end{aligned}
\tag{16.15}
$$

所有比较使用同一个任意输入 $`\rho_{JM}`$，并且界与参考和终端编号无关。对 $`n<L`$，直接逆启动编码，误差为零。每个解码器在总寄存器 $`K`$ 的预期阶段扇区上按上述方式定义，在其他阶段扇区输出任意固定档案态，因而是整个 $`K`$ 上的 CPTP 通道；实际终端处在该预期扇区内。

**统一装置与容量。** 取（15.23）的有限启动扇区和本节运行扇区；按输入阶段选用已固定的启动通道或（16.10），得到一个独立纯初始化的固定全域 CPTP 接收器。实际阶段始终确定，运行阶段的块标签保持相干。由 $`\dim S_0=1`$、$`\dim S_t\le m^2`$ 和 $`\sum_kr_k\le m`$，其总维数至多

$$
1+(L-1)m^2+(2m^2)\sum_kr_k
\le1+(L-1)m^2+2m^3.
\tag{16.16}
$$

最后说明精度依赖。若存在非零严格收缩谱，令其最大模为 $`r<1`$。任取 $`r<\gamma<1`$，有限维 Jordan 估计并吸收有限幂零前缀，给常数 $`C_{E,\gamma}>0`$，使

$$
\delta_L\le C_{E,\gamma}\gamma^L
\qquad(L\ge1).
\tag{16.17}
$$

取 $`L=O_E(1+\log(1/\epsilon))`$ 即可使（16.15）至多 $`\epsilon`$。若没有非零严格收缩谱，$`\delta_L`$ 在有限步后为零，亦符合所述上界。证明完毕。

定理15.1与本节给出精确和近似任务的不同结论：非零收缩谱可以排除任意有限容量的全时域精确接收；对每个固定正误差容限，同一已知有限维来源仍有有限固定接收器。两者不矛盾，容量可以随着误差趋零而发散。其几何内容是把来源的外围共同关系保存为可持续维护的纯化接口，并把剩余衰减部分的影响限制在一次启动比较中；并非每步舍弃一小块历史，再假定误差自行抵消。

[^phase_stinespring_continuity]: Dennis Kretschmann, Dirk Schlingemann and Reinhard F. Werner, *A Continuity Theorem for Stinespring's Dilation*, [arXiv:0710.2495v1, Theorem 1 and equations (6)–(7)](https://arxiv.org/pdf/0710.2495v1). 定理给 $`\beta(T_1,T_2)\le\sqrt{\|T_1-T_2\|_{\rm cb}}`$、达到该 Bures 距离的共同 Stinespring 表示，以及两份最小表示的直和可作为共同表示。本文在有限矩阵代数上对通道的 Heisenberg 对偶应用该结论；其 cb 距离等于 Schrödinger 通道的 diamond 距离。原定理没有给出本文的固定在线接收、全终端误差或容量账，这些由本节的外围吸收器和两次距离比较建立。

## 追加锚（本行以下为增补区）


## 17. 同一内部通道与不同校准边界的容量差

前节的装置可以依赖已知来源。本节说明，这个量词不能仅凭内部通道相同而改成“同一装置适用于全部尚未校准的发射接口”。采用定义1.1的两态来源、等权 $`c_t=1`$ 和同一个贯穿全程的相位。按该定义的输出在前约定，一步发射为

$$
T_\vartheta=(R_\vartheta\otimes I_M)T,
\qquad R_\vartheta=\operatorname{diag}(1,e^{i\vartheta}).
\tag{17.1}
$$

**命题 17.1（相同记忆动力学不供相位校准）。** 全部（17.1）的内部记忆通道严格相同：

$$
E_\vartheta(X)
=\operatorname{Tr}_B(T_\vartheta XT_\vartheta^\dagger)
=\operatorname{Tr}_B(TXT^\dagger)=E(X).
\tag{17.2}
$$

因此它们有相同的外围投影、衰减谱及（16.1）的 $`\delta_L`$。对任意固定 $`0<\epsilon<1`$，每个已经校准的 $`\vartheta`$ 都有一台满足定理16.2的有限固定接收器，并且数值容量上界可取相同；接收通道及解码器本身仍可依赖这个已知 $`\vartheta`$。

证明。对被偏迹系统施加酉不改变偏迹，逐矩阵元或由偏迹的定义即得（17.2）。其余谱数据只取决于 $`E`$，故相同。每个已知 $`T_\vartheta`$ 都是固定等距来源，将张量因子作一次固定重排后应用定理16.2。也可在接收每个新位时先施加已知 $`R_\vartheta^\dagger`$，接上零相位的固定接收器，并在终端解码后对每个档案位恢复 $`R_\vartheta`$。这两种构造均使用已知校准，不取得未知相位的免费读数。证明完毕。

**定理 17.2（任意正长度相位区间的统一容量障碍）。** 令 $`I`$ 为相位圆上的可测集合，归一 Haar 测度为

$$
a:=\mu(I)>0,
\qquad d\mu(\vartheta)=\frac{d\vartheta}{2\pi}.
\tag{17.3}
$$

特别允许任意短的非退化相位弧。取 $`n\ge4`$，记本卷估计（5.18）为

$$
\beta_n=\frac{\sqrt\pi}
{2\sqrt{\alpha^3\lfloor(n-1)/3\rfloor}},
\qquad \alpha=\frac{\sqrt5-1}{2}.
\tag{17.4}
$$

若同一个编码—解码方案不能依赖实际 $`\vartheta\in I`$，接收系统维数为 $`D`$，则在指定 Bell 初始参考输入上，它的最坏联合半迹恢复误差 $`e_n`$ 满足

$$
\boxed{
e_n\ge\max\left\{0,\ 1-\frac{4D\beta_n}{a}\right\}.
}
\tag{17.5}
$$

所以，若要求全部相位及全部参考输入的误差至多 $`\epsilon<1`$，必有

$$
D\ge\frac{a(1-\epsilon)}{4\beta_n}
=\Omega_{a,\epsilon}(\sqrt n).
\tag{17.6}
$$

允许每个终端重新设计编码、接收门或解码器仍受此界。特别地，任何固定有限 $`D`$ 的同一装置，其最坏误差随终端编号趋于一，不可能满足全部终端的统一正精度合同。

证明。沿用（5.15）的纯联合 Bell 目标
 $`P_\vartheta=|\Psi_\vartheta\rangle\langle\Psi_\vartheta|`$，并把不可访问的参考与活动记忆合记为四维系统 $`R=JM`$。定义全圆与局部平均

$$
\overline P=\int P_\vartheta\,d\mu(\vartheta),
\qquad
\overline P_I=\frac1a\int_I P_\vartheta\,d\mu(\vartheta).
\tag{17.7}
$$

正算子积分给 $`0\preceq\overline P_I\preceq\overline P/a`$。由（5.15）—（5.18），$`\overline P\preceq\beta_n I`$，因此

$$
\overline P_I\preceq\frac{\beta_n}{a}I.
\tag{17.8}
$$

对任意允许编码所得 $`KR`$ 联合态 $`\tau_\vartheta`$，有 $`0\preceq\tau_\vartheta\preceq I_{KR}`$。令 $`\mathcal D_n`$ 为这个终端的同一 CPTP 解码器。目标重叠满足

$$
\begin{aligned}
f_\vartheta
&=\operatorname{Tr}\left[P_\vartheta
(\mathcal D_n\otimes\operatorname{id}_R)(\tau_\vartheta)\right]\\
&\le\operatorname{Tr}
\left[(\mathcal D_n^*\otimes\operatorname{id}_R)(P_\vartheta)\right].
\end{aligned}
\tag{17.9}
$$

对 $`I`$ 平均，利用解码对偶的正性和幺性，得到

$$
\frac1a\int_I f_\vartheta\,d\mu(\vartheta)
\le\operatorname{Tr}
\left[(\mathcal D_n^*\otimes\operatorname{id}_R)(\overline P_I)\right]
\le\frac{4D\beta_n}{a}.
\tag{17.10}
$$

以纯目标投影作为一个效果，半迹距离至少为 $`1-f_\vartheta`$。最坏误差不小于平均误差，故（17.10）给（17.5）；再移项得到（17.6）。$`\beta_n\to0`$，而半迹距离不超过一，所以固定 $`D`$ 时 $`e_n\to1`$。证明只用了终端接收系统的容量及同一解码器，不假定来源在不同相位之间可作相干叠加，也没有把未知相位认作逐步独立噪声。证明完毕。

本节是定理16.2与既有共同相位平均界的综合应用，不另立新的谱结构原理。它给出一个明确的关系边界：内部记忆边缘、谱和混合速率完全相同，仍不保证这些发射接口具有同一有限维的全时域近似接收实现。装置需要保存哪些关系，还取决于允许来源族及输出相干检验所使用的校准。

这不是对所有有限参数不确定性的结论；定理17.2使用 $`a>0`$，不处理零测度候选族。误差下界也允许终端的最坏相位随 $`n`$ 改变；它没有额外证明同一个固定相位的误差必然趋于一。对每个固定区间，容量发散已经足以排除统一装置。

## 追加锚（本行以下为增补区）


## 18. 校准分辨率与有限终端容量的统一尺度

**定义 18.1（已知候选弧与完整联合压缩）。** 固定定义1.1的等权来源。令 $`I`$ 为相位圆上一条已知闭弧，弧长 $`0\le\ell\le2\pi`$；$`\ell=0`$ 表示一个已知相位，$`\ell=2\pi`$ 表示全圆。给定 $`n\ge4`$ 及 $`0<\epsilon<1`$，记 $`k_n^{(\epsilon)}(I)`$ 为满足定义1.2权限、对全部 $`\vartheta\in I`$ 及全部参考完整输入具有半迹恢复误差至多 $`\epsilon`$ 的最小接收维数。编码与解码可以依赖已知的 $`I,n,\epsilon`$，不能依赖实际相位或输入。此处的资源只跨越一个指定终端的编码—解码间隔，不要求不同 $`n`$ 的装置由同一接收通道实现。

沿用（5.2）的 $`h_r,b_n`$，定义

$$
g_n^2:=\sum_{r=1}^n h_r^2\le n,
\qquad
N_{n,I,\epsilon}:=
\max\left\{1,\left\lceil
\frac{\ell g_n}{2\sqrt2\,\epsilon}
\right\rceil\right\}.
\tag{18.1}
$$

**定理 18.2（弧宽与涨落尺度的双边容量律）。** 对定义18.1中的全部参数，

$$
\boxed{
\max\left\{1,
\frac{\ell(1-\epsilon)}{4\pi^{3/2}}
\sqrt{\alpha^3\left\lfloor\frac{n-1}{3}\right\rfloor}
\right\}
\le k_n^{(\epsilon)}(I)
\le \min\{2n-1,\ 4N_{n,I,\epsilon}\}
\le4+\frac{\sqrt2\,\ell\sqrt n}{\epsilon}.
}
\tag{18.2}
$$

因此，对每个固定 $`0<\epsilon<1`$，存在只依赖 $`\epsilon`$ 的正常数 $`c_\epsilon,C_\epsilon`$，使

$$
\boxed{
c_\epsilon(1+\ell\sqrt n)
\le k_n^{(\epsilon)}(I)
\le C_\epsilon(1+\ell\sqrt n).
}
\tag{18.3}
$$

常数统一于终端编号、弧长和弧的位置，因而允许弧长随 $`n`$ 改变。这里的平方根尺度与量子时钟压缩及量子 Markov 输出的局部统计尺度相联系；[^phase_calibration_lan] 以下证明直接保留本来源的参考与活动记忆，给出有限 $`n`$ 的共同物理编码。

证明。下界在 $`\ell>0`$ 时由定理17.2取 $`a=\ell/(2\pi)`$ 得到，其论证逐终端成立，不要求本处的 $`I`$ 在不同终端相同。$`\ell=0`$ 时只使用任何非零接收系统的维数至少为一。

为构造上界，先控制邻近相位在整个输入空间上的变化。（5.7）的 Doob 鞅增量具有条件均值零及条件取值区间宽度至多 $`h_{n-t+1}`$。区间宽度为 $`h`$ 的实随机变量方差至多 $`h^2/4`$：减去区间中点后，其平方不超过 $`h^2/4`$，再减均值只使二阶矩下降。鞅增量彼此正交，所以

$$
\operatorname{Var}_i(S_n)
\le\frac14\sum_{r=1}^{n-1}h_r^2.
\tag{18.4}
$$

由（5.6），$`\mathbb E_iS_n-b_n=(i-\tfrac12)h_n`$，从而对两个初位均有

$$
\mathbb E_i(S_n-b_n)^2\le\frac{g_n^2}{4}.
\tag{18.5}
$$

把弧提升为实轴上的长度 $`\ell`$ 区间。对区间内的两个相位 $`\vartheta,\varphi`$，置 $`\delta=\vartheta-\varphi`$，并以同一个标量相位比较两份累计等距：

$$
Q_{\vartheta,\varphi}
:=T_{\vartheta,n}-e^{ib_n\delta}T_{\varphi,n}.
\tag{18.6}
$$

两个输入基向量的输出档案首位不同，故 $`Q_{\vartheta,\varphi}|0\rangle`$ 与 $`Q_{\vartheta,\varphi}|1\rangle`$ 正交。在各自首位扇区逐词展开，利用 $`|e^{ix}-1|\le|x|`$ 及（18.5），得到

$$
\begin{aligned}
\|Q_{\vartheta,\varphi}|i\rangle\|^2
&=\mathbb E_i\left|
e^{i\delta S_n}-e^{i\delta b_n}
\right|^2\\
&\le\delta^2\mathbb E_i(S_n-b_n)^2
\le\frac{\delta^2g_n^2}{4}.
\end{aligned}
\tag{18.7}
$$

因此

$$
Q_{\vartheta,\varphi}^*Q_{\vartheta,\varphi}
\preceq\frac{\delta^2g_n^2}{4}I_M.
\tag{18.8}
$$

式（18.8）没有分别调整两个输入分量的相位；同一算子界在张量任意参考后仍然成立。

将提升区间等分为 $`N=N_{n,I,\epsilon}`$ 段，取各段中点 $`\varphi_1,\ldots,\varphi_N`$；退化弧只取其唯一点。每个相位距某个网格点不超过

$$
\frac{\ell}{2N}\le
h:=\frac{\sqrt2\,\epsilon}{g_n}.
\tag{18.9}
$$

对已知相位 $`\varphi_j`$，令 $`S_n(\varphi_j)`$ 为全部实际档案的共同支撑。定理3.2给 $`\dim S_n(\varphi_j)=4`$。令 $`P`$ 为这些支撑之和上的正交投影，记 $`r=\operatorname{rank}P`$，则

$$
r\le4N,
\qquad
(P\otimes I_M)T_{\varphi_j,n}=T_{\varphi_j,n}.
\tag{18.10}
$$

对实际相位选取（18.9）的网格点，将（18.8）投影到 $`P`$ 的补空间，得到

$$
T_{\vartheta,n}^*[(I-P)\otimes I_M]T_{\vartheta,n}
\preceq\frac{h^2g_n^2}{4}I_M
=\frac{\epsilon^2}{2}I_M.
\tag{18.11}
$$

取等距满射 $`F:PH_n\to\mathbb C^r`$ 和一份固定编码态 $`\kappa`$。定义全域 CPTP 编解码

$$
\mathcal E(X)=FPXP F^*
+\operatorname{Tr}[(I-P)X]\kappa,
\qquad
\mathcal D(Y)=F^*YF.
\tag{18.12}
$$

$`F^*`$ 的值域按原支撑嵌入 $`H_n`$。失败结果直接重置到同一编码空间，不额外保留可读旗标；该合同不要求报告是否失败。对任意纯化输入，记真实纯联合目标为 $`|\psi\rangle`$。式（18.11）保证失败质量 $`d\le\epsilon^2/2`$。恢复态含有正的成功项

$$
(P\otimes I_R)|\psi\rangle\langle\psi|(P\otimes I_R),
\tag{18.13}
$$

其中 $`R`$ 包含参考与活动记忆；其余失败项也为正。因此恢复态与目标的重叠至少为 $`(1-d)^2`$。应用（5.12）中的纯目标迹距离界，并对混合输入丢弃额外纯化参考，统一恢复误差至多

$$
\sqrt{1-(1-d)^2}\le\sqrt{2d}\le\epsilon.
\tag{18.14}
$$

网格、投影和通道仅使用声明的候选弧；（18.6）中的实际相位差只用于证明误差界，不是装置取得的额外读数。这给 $`k_n^{(\epsilon)}(I)\le4N`$。定理3.2的全圆精确编码另给 $`2n-1`$；由（18.1）的取整界及 $`g_n\le\sqrt n`$，得到（18.2）的全部上界。

最后，$`\lfloor(n-1)/3\rfloor\ge n/6`$ 对 $`n\ge4`$ 成立。令

$$
A_\epsilon=\frac{(1-\epsilon)\alpha^{3/2}}
{4\pi^{3/2}\sqrt6}>0.
\tag{18.15}
$$

则（18.2）下界至少为 $`\max\{1,A_\epsilon\ell\sqrt n\}`$，进而至少为 $`\tfrac12\min\{1,A_\epsilon\}(1+\ell\sqrt n)`$。上界可取 $`C_\epsilon=\max\{4,\sqrt2/\epsilon\}`$。这证明（18.3）。证明完毕。

**推论 18.3（有界终端容量的校准阈值）。** 固定 $`0<\epsilon<1`$，给定一列已知候选弧 $`I_n`$，弧长为 $`\ell_n`$。则

$$
\boxed{
\sup_{n\ge4}k_n^{(\epsilon)}(I_n)<\infty
\quad\Longleftrightarrow\quad
\ell_n\sqrt n=O(1).
}
\tag{18.16}
$$

若 $`\ell_n=n^{-\gamma}`$，其中 $`\gamma\ge0`$，则

$$
k_n^{(\epsilon)}(I_n)
=\Theta_\epsilon\!\left(1+n^{1/2-\gamma}\right).
\tag{18.17}
$$

证明。直接使用（18.3）的统一常数；有限个起始终端不影响有界性。证明完毕。

上述容量律不提供候选弧本身的取得程序。若候选弧来自额外观察，取得这些读数的资源仍是另一个任务。式（18.12）也不声明不同终端的支撑投影具有合法续接关系；将这些编码组成同一个固定接收器，还需要相应的动态闭合及共同误差证明。

[^phase_calibration_lan]: Mădălin Guţă and Jukka Kiukas，*Equivalence classes and local asymptotic normality in system identification for quantum Markov chains*，[arXiv:1402.3535](https://arxiv.org/abs/1402.3535)。该文研究可识别参数的 $`n^{-1/2}`$ 局部尺度与 Gaussian 极限；本节不将该渐近统计结论当作有限终端、全参考恢复的容量定理。量子时钟压缩的相关先例见本卷 [^phase_clock]。本节的有限网格编码及相位弧双边容量式由（5.7）、定理17.2及实际档案支撑共同推出。

## 追加锚（本行以下为增补区）


## 19. 有限候选与无限候选的全时域接收分界

**定义 19.1（同一候选族的固定近似接收）。** 固定定义1.1的等权两态来源，令 $`\Theta`$ 为相位圆的非空子集，不要求其具有正测度或可测性。对固定 $`0<\epsilon<1`$，接收器仍从独立纯态启动，只作用于持久寄存器与最新发出位；每步使用同一个全域 CPTP 接收通道，所有持久控制均计入寄存器。来源活动记忆与参考不可访问。接收器与终端解码器可以依赖已知的候选集合，不能依赖实际 $`\vartheta\in\Theta`$。要求每个有限终端、每个候选相位和每份参考完整输入的联合半迹恢复误差均至多 $`\epsilon`$。

**定理 19.2（候选相位基数的精确存在性判据）。** 定义19.1中的任务存在有限维固定接收器，当且仅当 $`\Theta`$ 是有限集。

若 $`\Theta`$ 无限，则更强地，对任意固定容量 $`D<\infty`$ 的方案，即使允许接收门随终端或步数改变，在本卷指定 Bell 输入上的逐终端最坏误差也满足

$$
\boxed{
\lim_{n\to\infty}\sup_{\vartheta\in\Theta}
d\bigl(\widehat\Omega_{\vartheta,n},\Omega_{\vartheta,n}\bigr)=1.
}
\tag{19.1}
$$

这里允许每个终端的最坏相位不同；结论不声称某一个固定相位的误差必然趋于一。

证明。先设 $`\Theta=\{\vartheta_1,\ldots,\vartheta_q\}`$ 有限。引入只供数学构造使用的标签空间 $`L=\mathbb C^q`$，把扩展来源记忆取为 $`\widetilde M=L\otimes M`$。按来源记忆在前的因子约定，定义固定等距

$$
\widetilde T(|j\rangle_L\otimes|\psi\rangle_M)
=|j\rangle_L\otimes
\operatorname{swap}_{B,M}T_{\vartheta_j}|\psi\rangle_M.
\tag{19.2}
$$

不同标签的像正交，每个 $`T_{\vartheta_j}`$ 等距，因此 $`\widetilde T`$ 是一份已知有限维等距来源，$`\dim\widetilde M=2q`$。应用定理16.2，得到一个从独立纯态启动的有限固定接收器，对扩展来源的全部参考完整输入、全部终端都保持误差至多 $`\epsilon`$。

将输入限制为

$$
|j\rangle\langle j|_L\otimes\rho_{JM},
\tag{19.3}
$$

并丢弃不可访问标签，恰得到原候选 $`\vartheta_j`$ 的发射与恢复合同。所构造接收通道只作用于其自身寄存器及每个发出位，不读取 $`L`$；没有向接收器免费交付实际相位。扩展来源上更强的相干输入合同只是充分性证明的工具，原模型不需要允许不同实际相位相干叠加。维数的一个有限上界由定理16.2取 $`m=2q`$ 给出，其中启动长度由整份已知扩展来源及所需误差决定。

现设 $`\Theta`$ 无限。任取 $`q\ge2`$ 个不同候选 $`\vartheta_1,\ldots,\vartheta_q`$。对相同 Bell 初态，令长度 $`n`$ 的纯目标向量为 $`|\Psi_{j,n}\rangle`$。由（5.14），两份目标的重叠是实际总荷的特征函数：

$$
\langle\Psi_{j,n}|\Psi_{k,n}\rangle
=\mathbb E\,e^{i(\vartheta_k-\vartheta_j)S_n}.
\tag{19.4}
$$

令

$$
m_n=\left\lfloor\frac{n-1}{3}\right\rfloor,
\qquad
c_q=\alpha^3\min_{j\ne k}
\sin^2\frac{\vartheta_k-\vartheta_j}{2}>0.
\tag{19.5}
$$

这些相位彼此不同模 $`2\pi`$，且取的是有限个数，故最小值严格正。由（5.17）的三步转移估计，对 $`j\ne k`$ 有

$$
|\langle\Psi_{j,n}|\Psi_{k,n}\rangle|
\le e^{-c_qm_n}.
\tag{19.6}
$$

记平均目标

$$
Q_{q,n}=\frac1q\sum_{j=1}^q
|\Psi_{j,n}\rangle\langle\Psi_{j,n}|.
\tag{19.7}
$$

令 $`V:\mathbb C^q\to H_n\otimes R`$ 的第 $`j`$ 列为 $`|\Psi_{j,n}\rangle`$，其中 $`R=JM`$ 为不可访问的四维系统。$`VV^*`$ 与 Gram 矩阵 $`V^*V`$ 具有相同的非零特征值。后者对角为一，各非对角项由（19.6）控制；以最大绝对行和界其谱半径，得到

$$
\|Q_{q,n}\|_\infty
\le\frac{1+(q-1)e^{-c_qm_n}}q.
\tag{19.8}
$$

对任意 $`D`$ 维接收器产生的终端态 $`\tau_{j,n}`$，以及同一个 CPTP 解码器 $`\mathcal D_n`$，采用（17.9）的正性估计，平均目标重叠至多

$$
\begin{aligned}
\frac1q\sum_{j=1}^q
\operatorname{Tr}\!\left[
|\Psi_{j,n}\rangle\langle\Psi_{j,n}|
(\mathcal D_n\otimes\operatorname{id}_R)(\tau_{j,n})
\right]
&\le\operatorname{Tr}
\left[(\mathcal D_n^*\otimes\operatorname{id}_R)(Q_{q,n})\right]\\
&\le\frac{4D}{q}\left[1+(q-1)e^{-c_qm_n}\right].
\end{aligned}
\tag{19.9}
$$

因此以 $`e_n`$ 记全候选集合上的最坏半迹误差，便有

$$
e_n\ge
\max\left\{0,
1-\frac{4D}{q}\left[1+(q-1)e^{-c_qm_n}\right]
\right\}.
\tag{19.10}
$$

先固定这 $`q`$ 个候选，让 $`n\to\infty`$，得 $`\liminf_ne_n\ge1-4D/q`$。无限集合允许任意大的有限 $`q`$，故 $`\liminf_ne_n\ge1`$。半迹距离至多为一，得到（19.1），并排除任何固定 $`\epsilon<1`$ 的有限容量实现。这里先取时间极限、再取任意大的有限候选子集，不假定 $`c_q`$ 随 $`q`$ 有统一正下界。证明完毕。

**推论 19.3（零测度校准残余仍可阻止有限固定接收）。** 候选集

$$
\Theta=\{0\}\cup\{1/j:j\ge1\}
\tag{19.11}
$$

是紧、可数、Haar 零测度集合，却不允许定义19.1中的有限固定接收器；每个有限子集均允许这种接收器。

证明。该集合在相位圆上只以零为聚点，因而紧；可数性给零测度。分别应用定理19.2的无限与有限方向。证明完毕。

本节将定理17.2的固定容量发散结论延伸到任意无限候选相位集，未改变其正测度情形的显式平方根速率。对一般无限集合，（19.10）的衰减常数依赖所选有限子集，因而本证明不给统一的平方根容量增长率。不同的长期容量结论仍以相同的完整档案及参考恢复任务为前提。

## 追加锚（本行以下为增补区）

## 20. 固定容量正误差隙的显式实代数下界

本节保留第10—12节的已知两态来源、独立纯初始化、同一个全域 CPTP 接收通道以及仅依赖终端编号的局部解码器。所有持久控制均计入接收寄存器；允许每轮引入并立即丢弃新的环境。来源振幅可以是复数，满足 $`|a|^2+|b|^2=1`$。误差仍比较参考、活动记忆与完整档案的联合态。

**定义 20.1（离退化端点的整数参数及显式常数）。** 固定整数 $`D\ge1`$、$`k\ge2`$，并限制来源为

$$
|a|^2\ge\frac1k,\qquad |b|^2\ge\frac1k.
\tag{20.1}
$$

每个已知非退化来源都满足某个这样的整数条件，例如可取
 $`k=\lceil1/\min\{|a|^2,|b|^2\}\rceil`$。
定义

$$
\begin{aligned}
N&=8D^2,& v&=8D^4+4,& s&=4D^2+3,\\
d&=16N,& B_D&=128D^4,\\
H&=\max\{k,\ 36ND^4B_D^{4N}\},&
\widehat H&=\max\{H,\ 2v+2s\},\\
\kappa_{D,k}&=(16\widehat H d^v)^{-v(2d)^v},&
\eta_{D,k}&=\frac{\kappa_{D,k}}{16N}.
\end{aligned}
\tag{20.2}
$$

其中 $`v`$ 是下文使用的实变量数，$`s`$ 是约束多项式总数，$`d`$ 是偶数次数上界；它们不是额外物理寄存器的维数。

**定理 20.2（统一于端点距离的显式有限时域误差隙）。** 对满足（20.1）的任一来源、任一维数不超过 $`D`$ 的固定接收器及任意一族终端解码器，有

$$
\boxed{
\max_{1\le n\le8D^2}\ \sup_{J,\rho_{JM}}
\frac12\left\|
(\operatorname{id}_{JM}\otimes\mathcal D_n)\sigma_n(\rho)
-\Omega_n(\rho)
\right\|_1
\ge\eta_{D,k}>0.
}
\tag{20.3}
$$

事实上，仅取指定初态 $`|0\rangle_M`$、不附加参考，已经足以得到此下界。因此，定义11.1中的全终端误差若严格小于 $`\eta_{D,k}`$，所需接收维数必大于 $`D`$。本节给出第12节正误差隙的一份显式下界，不主张该数值或其容量依赖最优。

证明。把接收初态的固定单位向量用一个固定基变换送到 $`e_0`$，并同时共轭接收通道及各解码器，不改变容量、固定性或恢复误差。因此先令 $`\dim K=D`$，并取初态

$$
\sigma_0=|0,e_0\rangle\langle0,e_0|_{MK}.
\tag{20.4}
$$

以下全过程只使用这一指定纯来源。记一次发射与固定接收的合成通道为 $`\mathcal R`$，并置 $`\sigma_n=\mathcal R^n(\sigma_0)`$、$`\rho_n=\operatorname{Tr}_K\sigma_n`$、$`\sigma_{K,n}=\operatorname{Tr}_M\sigma_n`$。

**环境解耦的有限矩阵表达。** 定义

$$
h_n=
\operatorname{Tr}\sigma_{K,n}^2
+\operatorname{Tr}\rho_n^2\operatorname{Tr}\sigma_n^2
-2\operatorname{Tr}\bigl[(\rho_n\otimes I_K)\sigma_n^2\bigr].
\tag{20.5}
$$

取 $`\sigma_n`$ 的任意纯化 $`|\chi_n\rangle_{MKE}`$，则

$$
h_n=
\|\rho_{ME,n}-\rho_n\otimes\rho_{E,n}\|_{\rm HS}^2\ge0.
\tag{20.6}
$$

为核对交叉项，暂时略去 $`n`$，写

$$
|\chi\rangle
=\sum_{i,\alpha,e}c_{i\alpha,e}|i,\alpha,e\rangle,
\quad
\sigma_{i\alpha,j\beta}
=\sum_e c_{i\alpha,e}\overline{c_{j\beta,e}},
\quad
(\rho_E)_{ef}
=\sum_{r,\beta}c_{r\beta,e}\overline{c_{r\beta,f}}.
\tag{20.7}
$$

这里 $`i,j,r`$ 是来源指标，$`\alpha,\beta`$ 是接收指标，$`e,f`$ 是纯化环境指标。于是

$$
\begin{aligned}
\operatorname{Tr}[\rho_{ME}(\rho_M\otimes\rho_E)]
&=\langle\chi|\rho_M\otimes I_K\otimes\rho_E|\chi\rangle\\
&=\sum_{i,j,\alpha,e,f}
\overline{c_{i\alpha,e}}(\rho_M)_{ij}
(\rho_E)_{ef}c_{j\alpha,f}\\
&=\sum_{i,j,\alpha,r,\beta}
(\rho_M)_{ij}\sigma_{r\beta,i\alpha}
\sigma_{j\alpha,r\beta}\\
&=\operatorname{Tr}[(\rho_M\otimes I_K)\sigma^2].
\end{aligned}
\tag{20.8}
$$

纯化两侧边缘具有相同非零谱，另外给出
 $`\operatorname{Tr}\rho_{ME}^2=\operatorname{Tr}\sigma_K^2`$
及 $`\operatorname{Tr}\rho_E^2=\operatorname{Tr}\sigma^2`$。
展开（20.6）的平方范数即得（20.5）。因而（20.5）仅需 $`2D`$ 维联合接收态，虽然其零点检验的是与全部累计环境的解耦。

**终端恢复误差控制解耦缺陷。** 令 $`\epsilon_n`$ 是指定纯来源在终端 $`n`$ 的恢复半迹误差。对解码器取 Stinespring 等距，将 $`\chi_n`$ 送到全局纯态 $`\zeta`$；其档案与活动记忆边缘记为 $`\tau`$，纯目标记为 $`|\Psi_n\rangle`$。由目标纯态投影这一效果，

$$
f:=\langle\Psi_n|\tau|\Psi_n\rangle\ge1-\epsilon_n.
\tag{20.9}
$$

当 $`f>0`$ 时，将 $`\zeta`$ 在目标方向上的分量归一化，得到其余系统上的纯态 $`|\xi\rangle`$，使
 $`|\langle\zeta|\Psi_n\otimes\xi\rangle|^2=f`$。
当 $`f=0`$ 时任取 $`\xi`$；此时（20.9）迫使 $`\epsilon_n=1`$，下述界仍成立。纯态距离公式给

$$
d\bigl(|\zeta\rangle\langle\zeta|,
|\Psi_n\rangle\langle\Psi_n|\otimes|\xi\rangle\langle\xi|\bigr)
\le\sqrt{\epsilon_n},
\qquad d(X,Y)=\tfrac12\|X-Y\|_1.
\tag{20.10}
$$

解码只作用于 $`K`$，所以它不改变 $`ME`$ 边缘；真实来源目标的活动记忆边缘也恰为 $`\rho_n`$。对（20.10）偏迹，先得到
 $`d(\rho_{ME,n},\rho_n\otimes\xi_E)\le\sqrt{\epsilon_n}`$，
再得到 $`d(\rho_{E,n},\xi_E)\le\sqrt{\epsilon_n}`$。
由三角不等式以及 $`\|X\|_{\rm HS}\le\|X\|_1`$，

$$
d(\rho_{ME,n},\rho_n\otimes\rho_{E,n})\le2\sqrt{\epsilon_n},
\qquad h_n\le16\epsilon_n.
\tag{20.11}
$$

因此，若

$$
G=\sum_{n=1}^{N}h_n,
\qquad N=8D^2,
\tag{20.12}
$$

则 $`G\le16N\max_{1\le n\le N}\epsilon_n`$。

**排除多项式的零点。** 对任何合法接收器及满足（20.1）的来源，都有 $`G>0`$。否则非负性使前 $`N`$ 个 $`h_n`$ 全部为零；由（20.6），记忆与累计环境在这些终端均成乘积。对固定 Kraus 词环境逐矩阵元读取，便得到（12.6）的全部同长度环境交叉等式。第12节的累计词空间在 $`8D^2`$ 层以内稳定，因此这些**精确零等式**延拓到全部字长，并推出（12.14）的全时域纯度恒等式，与非退化来源的谱障碍矛盾。

这里调用的是第12节证明中的环境交叉延拓，不是把单个纯度差当作充分恢复条件，也没有把有限个近似等式延拓到无限时间。下一步将直接对有限多项式 $`G`$ 使用正最小值估计。

**整数半代数参数集。** 任意从 $`2D`$ 维输入到 $`D`$ 维输出的 CPTP 接收通道，其 Kraus 秩至多 $`2D^2`$。补零 Kraus 算子后，可统一写为 Stinespring 等距

$$
W:\mathbb C^{2D}\longrightarrow
\mathbb C^D\otimes\mathbb C^{2D^2},
\qquad W^\dagger W=I_{2D}.
\tag{20.13}
$$

$`W`$ 是 $`2D^3\times2D`$ 的复矩阵，共有 $`8D^4`$ 个实参数。再把 $`a,b`$ 的四个实分量也作为变量，共得到（20.2）的 $`v=8D^4+4`$ 个实变量；没有把给定的任意实振幅分量用作不受控制的系数。

等式 $`W^\dagger W=I_{2D}`$ 用对角实方程和非对角项的实部、虚部表示，恰有 $`4D^2`$ 条实二次方程，整数系数高度至多一。另加

$$
|a|^2+|b|^2-1=0,
\qquad k|a|^2-1\ge0,
\qquad k|b|^2-1\ge0.
\tag{20.14}
$$

总计 $`s=4D^2+3`$ 条整数二次约束，系数绝对值至多 $`k`$。它们定义一个非空基本闭半代数集 $`\mathscr T_{D,k}\subset\mathbb R^v`$：可取 $`a=b=1/\sqrt2`$ 及任意（20.13）的等距。每个 $`W`$ 列向量的范数为一，来源也归一化，故所有实变量有界；约束闭，因而该集合紧。

每个点都定义一台合法固定接收器和一个非退化来源；前面的零点排除遂给 $`G>0`$ 在整个 $`\mathscr T_{D,k}`$ 上成立。

**次数与系数高度。** 对实变量上的复多项式 $`P=\sum_\alpha c_\alpha x^\alpha`$，使用系数范数

$$
\|P\|_{\mathrm{coef},1}=\sum_\alpha|c_\alpha|.
\tag{20.15}
$$

该范数次可乘，复共轭不改变其值。一个复矩阵元写成 $`x+iy`$ 时范数为二；$`a,b`$ 同样如此。所有计算起于整数及 $`i`$，故中间系数属于 $`\mathbb Z[i]`$。最后取实部是逐系数操作，并满足
 $`\|\operatorname{Re}P\|_{\mathrm{coef},1}\le\|P\|_{\mathrm{coef},1}`$；
因此实化不会另增一个二因子。

令 $`t_{ji}=(m_i)_j`$，即 $`t_{00}=a,t_{10}=b,t_{01}=1,t_{11}=0`$。按来源在前的固定因子次序，发射与接收合成的 Kraus 算子为

$$
(L_u)_{(j,\alpha),(i,\beta)}
=t_{ji}\,W_{(\alpha,u),(\beta,i)},
\quad
1\le u\le2D^2,\quad 1\le\alpha,\beta\le D.
\tag{20.16}
$$

每个矩阵元的次数至多二，系数范数至多四。递推
 $`\sigma_{n+1}=\sum_uL_u\sigma_nL_u^\dagger`$
的每个矩阵元，至多含 $`(2D^2)(2D)^2`$ 个被加项；左右两个 Kraus 元贡献范数因子至多十六。因此，由（20.4）起归纳，有

$$
\deg(\sigma_n)_{xy}\le4n,
\qquad
\| (\sigma_n)_{xy}\|_{\mathrm{coef},1}
\le(128D^4)^n=B_D^n.
\tag{20.17}
$$

记 $`z=B_D^n`$。接收边缘的每个矩阵元至多是两个 $`\sigma_n`$ 元之和，来源边缘的每个矩阵元至多是 $`D`$ 个之和。逐项求和遂给

$$
\begin{aligned}
\|\operatorname{Tr}\sigma_{K,n}^2\|_{\mathrm{coef},1}
&\le4D^2z^2,\\
\|\operatorname{Tr}\rho_n^2\|_{\mathrm{coef},1}
&\le4D^2z^2,\\
\|\operatorname{Tr}\sigma_n^2\|_{\mathrm{coef},1}
&\le4D^2z^2,\\
\|\operatorname{Tr}[(\rho_n\otimes I_K)\sigma_n^2]\|_{\mathrm{coef},1}
&\le8D^3z^3.
\end{aligned}
\tag{20.18}
$$

最后一项可具体按来源的两个行列指标及一个接收指标求和，共 $`4D`$ 项；其中 $`\rho_n`$ 元的范数至多 $`Dz`$，$`\sigma_n^2`$ 元的范数至多 $`2Dz^2`$，乘积即给上述界。结合（20.5），

$$
\begin{aligned}
\|h_n\|_{\mathrm{coef},1}
&\le4D^2B_D^{2n}
+16D^4B_D^{4n}
+16D^3B_D^{3n}\\
&\le36D^4B_D^{4n},\\
\deg G&\le16N=d,
\qquad
\|G\|_{\mathrm{coef},1}\le36ND^4B_D^{4N}.
\end{aligned}
\tag{20.19}
$$

式（20.5）对所有实参数均为实数：递推产生 Hermitian 矩阵，而其中的迹表达为实数。也可在定义目标多项式时直接取该表达的实部；它保持全部实参数上的值。由（20.15），得到的 $`G`$ 属于 $`\mathbb Z[x_1,\ldots,x_v]`$，且（20.19）保持原常数。因此约束与目标的整数系数高度统一不超过（20.2）的 $`H`$。

**紧连通分量上的显式正最小值。** Jeronimo–Perrucci–Tsigaridas 的正最小值界指出：[^phase_positive_polynomial_minimum] 若 $`v`$ 个实变量上的基本闭半代数集由 $`s`$ 个整数多项式的等式及非严格不等式定义，其次数不超过偶数 $`d`$、系数绝对值不超过 $`H`$；整数目标多项式也满足这两个界，则它在任一紧连通分量上的非零最小值，其绝对值至少为

$$
\left(2^{4-v/2}\widehat H d^v\right)^{-v2^vd^v},
\qquad \widehat H=\max\{H,2v+2s\}.
\tag{20.20}
$$

本处 $`v\ge12`$，$`d=16N`$ 是正偶数，全部条件已经满足。由于 $`\mathscr T_{D,k}`$ 紧且 $`G>0`$，其全局最小值在某点取得且严格正。取包含该点的连通分量；连通分量是紧集中的闭子集，因此紧，而且其最小值就是全局最小值。无需额外假定整个参数集连通。

应用（20.20），再用 $`2^{4-v/2}\le16`$ 及 $`2^vd^v=(2d)^v`$，得到

$$
\min_{\mathscr T_{D,k}}G
\ge\left(2^{4-v/2}\widehat H d^v\right)^{-v2^vd^v}
\ge(16\widehat H d^v)^{-v(2d)^v}
=\kappa_{D,k}.
\tag{20.21}
$$

这里增大底数会减小带负指数的表达，故最后替换是保守的下界。结合（20.11）—（20.12），

$$
\max_{1\le n\le N}\epsilon_n
\ge\frac{G}{16N}
\ge\frac{\kappa_{D,k}}{16N}
=\eta_{D,k}.
\tag{20.22}
$$

全部参考和输入的上确界至少包含这份指定纯来源误差。容量小于 $`D`$ 的装置可嵌入 $`D`$ 维寄存器，并在未使用空间任意完成通道；嵌入不改变实际运行。故（20.3）也覆盖全部容量不超过 $`D`$ 的装置。证明完毕。

对固定 $`k`$，上述显式数值的大小可以直接估计。由（20.2），

$$
-\log\eta_{D,k}
=\log(16N)+v(2d)^v\log(16\widehat H d^v).
\tag{20.23}
$$

当 $`D\to\infty`$ 时，$`v=O(D^4)`$、$`d=O(D^2)`$、$`\log\widehat H=O_k(D^2\log(D+1))`$，因而存在仅依赖 $`k`$ 的常数 $`C_k`$，使

$$
-\log\eta_{D,k}
\le\exp\bigl(C_kD^4\log(D+1)\bigr)
\qquad(D\ge1).
\tag{20.24}
$$

这只描述本节所给显式下界的保守尺度；它没有证明第11节对数容量上界最优。其来源依赖通过整数 $`k`$ 明确进入，未声称在退化端点上一致。本节使用既有环境交叉零点排除与标准实代数最小值定理的组合，不把实代数分离定理本身作为新结论。

**推论 20.3（精度要求给出的显式容量发散）。** 固定一个满足（20.1）的来源及整数 $`k`$。当 $`\epsilon\downarrow0`$ 时，定义11.1的全时域容量满足

$$
d_{\infty}^{(\epsilon)}(a,b)
=\Omega_k\!\left(
\left[
\frac{\log\log(1/\epsilon)}
{\log\log\log(1/\epsilon)}
\right]^{1/4}
\right).
\tag{20.25}
$$

式（20.25）只在误差充分小、全部对数有定义且分母为正时使用；常数及该阈值可以仅依赖 $`k`$。它与定理11.2的 $`O_{a,b}(\log(1/\epsilon))`$ 上界之间仍有缺口。

证明。设容量 $`D`$ 实现误差 $`\epsilon`$，则由（20.3）、（20.24），

$$
\epsilon\ge\eta_{D,k}
\ge\exp\{-\exp(C_kD^4\log(D+1))\}.
\tag{20.26}
$$

置 $`L=\log\log(1/\epsilon)`$，对充分小的误差取对数得
 $`L\le C_kD^4\log(D+1)`$。若 $`D\ge L^{1/4}`$，所需下界直接成立；否则对充分大的 $`L`$ 有 $`\log(D+1)\le\log L`$，从而

$$
D\ge C_k^{-1/4}(L/\log L)^{1/4}.
\tag{20.27}
$$

取这两个情形的共同正常数，再对允许的容量取最小值，即得结论。证明完毕。

[^phase_positive_polynomial_minimum]: Gabriela Jeronimo, Daniel Perrucci and Elias Tsigaridas, *On the minimum of a polynomial function on a basic closed semialgebraic set and applications*, [arXiv:1112.0544v1, Theorem 1, equation (1)](https://arxiv.org/html/1112.0544v1), [doi:10.1137/110857751](https://doi.org/10.1137/110857751). 原文的变量数 $`n`$、约束数 $`m`$ 在本节分别记为 $`v,s`$；定理要求偶数次数上界，并允许等式和非严格不等式、奇异可行集及紧连通分量。本节使用其非零最小值下界，不需要原定理同时给出的代数次数上界。原定理不涉及量子接收；环境缺陷多项式、有限时域零点排除及误差转换由本节与第12节给出。

## 追加锚（本行以下为增补区）

## 21. 三步精确接收中丢弃环境的首个严格容量收益

本节固定定义9.1的已知非退化复振幅来源
 $`m_0=a|0\rangle+b|1\rangle`$、$`m_1=|0\rangle`$，其中
 $`ab\ne0`$、$`|a|^2+|b|^2=1`$。
接收合同取定义12.1：独立纯初始化、同一个全域 CPTP 接收通道、全部持久系统计入接收容量，并在每个指定终端恢复任意参考、活动记忆及完整档案的联合态。每轮新环境可立即丢弃；环境不在后续轮次复用。

**定理 21.1（三步的精确最小固定 CPTP 容量）。** 对上述任意已知非退化来源，

$$
\boxed{
d_{\mathrm{CPTP},1}(a,b)=2,\qquad
d_{\mathrm{CPTP},2}(a,b)=3,\qquad
d_{\mathrm{CPTP},3}(a,b)=4.
}
\tag{21.1}
$$

因此，第三步是固定 CPTP 合同与同一固定酉、逐步同一纯空白、无额外丢弃环境合同的首个严格容量差：后者由定理9.2需要五维，前者只需四维。以下构造使用同一个固定接收门，其丢弃端口在前三轮依次为确定纯态 $`|0\rangle,|1\rangle,|0\rangle`$；这些端口不携带来源数据，但并非每轮都为同一个纯空白。

证明。先给三步四维构造。取 $`K=\mathbb C^4`$ 的正交单位基
 $`u,v,w,t`$，接收初态为 $`w`$。置

$$
c=\sqrt{|a|^4+|b|^2},\qquad
z=\frac{a^2u+bv}{c},\qquad
y=\frac{-\overline b\,u+\overline{a}^{2}v}{c}.
\tag{21.2}
$$

有 $`c>0`$，且 $`z,y`$ 是 $`\operatorname{span}\{u,v\}`$ 的一组正交单位基。具体地，两者范数均为一，而
 $`\langle z,y\rangle=(-\overline{a}^{2}\overline b+\overline b\,\overline{a}^{2})/c^2=0`$。
这里保留全部复振幅，没有把 $`a,b`$ 假定为正实数。

取每轮新环境 $`E=\mathbb C^2`$，定义
 $`V:K\otimes\mathcal B\to K\otimes E`$
在下列八个输入基向量上的作用：

$$
\begin{aligned}
V(t\otimes|0\rangle)&=u\otimes|1\rangle,
&V(z\otimes|0\rangle)&=z\otimes|0\rangle,\\
V(t\otimes|1\rangle)&=v\otimes|1\rangle,
&V(u\otimes|1\rangle)&=w\otimes|0\rangle,\\
V(y\otimes|0\rangle)&=w\otimes|1\rangle,
&V(w\otimes|0\rangle)&=t\otimes|0\rangle,\\
V(v\otimes|1\rangle)&=t\otimes|1\rangle,
&V(w\otimes|1\rangle)&=y\otimes|0\rangle.
\end{aligned}
\tag{21.3}
$$

输入中，新位为零时的四个接收向量是 $`t,y,z,w`$，新位为一时的四个接收向量是 $`t,v,u,w`$；两组分别正交归一。输出中，环境为一时的接收向量是 $`u,v,w,t`$，环境为零时是 $`z,w,t,y`$，也分别正交归一。因此（21.3）把一组八维正交单位基送到另一组，唯一确定一个全域酉。定义同一个接收通道

$$
\mathcal C(X)=\operatorname{Tr}_E(VXV^\dagger).
\tag{21.4}
$$

它在整个 $`K\otimes\mathcal B`$ 上 CPTP，运行时不调用步数来更换门。

**三步的实际联合态。** 将活动记忆写在接收器前方。对初始记忆基态 $`|i\rangle_M`$，记接收后的纯联合向量为 $`\Psi_n^i\in M\otimes K`$。前三轮满足

$$
\begin{aligned}
\Psi_1^0&=m_0\otimes t,
&\Psi_1^1&=m_1\otimes y,\\
\Psi_2^0&=a\,m_0\otimes u+b\,m_1\otimes v,
&\Psi_2^1&=m_0\otimes w,\\
\Psi_3^0&=c\,m_0\otimes z+ab\,m_1\otimes w,
&\Psi_3^1&=a\,m_0\otimes t+b\,m_1\otimes y.
\end{aligned}
\tag{21.5}
$$

同时，各轮环境的纯向量分别为

$$
\eta_1=|0\rangle,
\qquad \eta_2=|1\rangle,
\qquad \eta_3=|0\rangle,
\tag{21.6}
$$

且与其余全部系统成乘积。

逐步验证如下。首轮只使用（21.3）中的 $`w\otimes|0\rangle`$ 与 $`w\otimes|1\rangle`$，两者都输出环境零，给（21.5）第一行。第二轮的两个发射后向量为

$$
a\,m_0\otimes t\otimes|0\rangle
+b\,m_1\otimes t\otimes|1\rangle,
\qquad
m_0\otimes y\otimes|0\rangle.
\tag{21.7}
$$

其中全部接收输入都由（21.3）送到环境一，得到第二行。第三轮的两个发射后向量为

$$
\begin{aligned}
&m_0\otimes(a^2u+bv)\otimes|0\rangle
+ab\,m_1\otimes u\otimes|1\rangle\\
&\hspace{2em}=c\,m_0\otimes z\otimes|0\rangle
+ab\,m_1\otimes u\otimes|1\rangle,\\
&a\,m_0\otimes w\otimes|0\rangle
+b\,m_1\otimes w\otimes|1\rangle.
\end{aligned}
\tag{21.8}
$$

全部接收输入都输出环境零，给第三行。以上每轮对两个初始基态使用相同的环境向量；线性性因而同时覆盖任意初始相干及任意参考纠缠。对混态可取纯化再偏迹。若仅为数学验证保留所有环境，则前三个终端的累计环境分别为 $`|0\rangle`$、$`|01\rangle`$、$`|010\rangle`$；实际运行立即丢弃各轮环境，并不将它们作为额外接收记忆。

**完整参考下的本地逆解码。** 对终端 $`n\in\{1,2,3\}`$，在接收器旁准备（21.6）的前 $`n`$ 个已知环境纯态，按逆时间顺序使用同一个 $`V^\dagger`$。每次只作用于当前接收器和该轮重新准备的环境，恢复对应发出位；最后丢弃回到初态的接收寄存器。这是一份只访问接收器的合法解码。

更明确地，令 $`\mathsf V_n`$ 是按正时间顺序把同一个 $`V`$ 依次作用于 $`K`$ 和档案中第 $`1,\ldots,n`$ 个位置的酉，已处理位置随后视为环境，记
 $`\boldsymbol\eta_n=\eta_1\otimes\cdots\otimes\eta_n`$。
定义整个 $`K`$ 上的通道

$$
\mathcal D_n(X)=
\operatorname{Tr}_K\!\left[
\mathsf V_n^\dagger
\bigl(X\otimes|\boldsymbol\eta_n\rangle
\langle\boldsymbol\eta_n|\bigr)
\mathsf V_n
\right].
\tag{21.9}
$$

其输出为完整 $`\mathcal B^{\otimes n}`$ 档案，因而（21.9）在全域 CPTP，无需依实际输入另选延拓。

每个较早的接收门只作用于 $`K`$ 和已发出的位置，与后续只作用于活动记忆及新位置的来源发射可交换。因此可以先完成全部来源发射，再运行 $`\mathsf V_n`$；这只是重排作用于不同系统的门，不给接收器访问活动记忆的权限。由（21.5）—（21.6），对全部 $`J,\rho_{JM}`$ 有

$$
(\operatorname{id}_{JM}\otimes\operatorname{Ad}_{\mathsf V_n})
\bigl(\Omega_n(\rho)\otimes|w\rangle\langle w|_K\bigr)
=\sigma_n(\rho)\otimes
|\boldsymbol\eta_n\rangle\langle\boldsymbol\eta_n|,
\qquad 1\le n\le3,
\tag{21.10}
$$

其中按标记系统作固定张量因子置换。代入（21.9）并逆转酉，就精确恢复 $`\Omega_n(\rho)`$。终端新准备的环境只含已知的确定纯态，不是取回运行中丢弃的系统。

**四维下界及首个严格差。** 为证明一般非退化振幅下的下界，取允许的 Bell 输入
 $`(|0\rangle_J|0\rangle_M+|1\rangle_J|1\rangle_M)/\sqrt2`$。
不作接收时，三步目标在档案与 $`JM`$ 的切口可写为

$$
\begin{aligned}
|\Omega_3\rangle=\frac1{\sqrt2}\bigl[
&|0\rangle_Jm_0\otimes(a^2|000\rangle+b|010\rangle)
+ab\,|0\rangle_Jm_1\otimes|001\rangle\\
&+a\,|1\rangle_Jm_0\otimes|100\rangle
+b\,|1\rangle_Jm_1\otimes|101\rangle
\bigr].
\end{aligned}
\tag{21.11}
$$

四个档案向量非零且有互不相交的计算基支撑，故线性独立。由于 $`b\ne0`$，$`m_0,m_1`$ 线性独立，四个对应的 $`JM`$ 向量也线性独立。因此此纯目标的 Schmidt 秩为四。

任何 $`D`$ 维接收器的联合 $`JMK`$ 态可分解为纯态之和，每个纯态在 $`JM:K`$ 切口的 Schmidt 秩至多 $`D`$。仅在 $`K`$ 上施加解码 Kraus 算子不会增加这些秩；若最终输出恰为一个纯态，所有非零分支必须与该纯态共线。因此能够恢复（21.11）就必须有 $`D\ge4`$。这里使用的是 Bell 参考与活动记忆的联合四维切口，没有把单个二维活动记忆误当成可承载 Schmidt 秩四的系统。四维构造达到此界。

同样的 Bell 输入在首步给 Schmidt 秩二，第二步的三项展开为

$$
\frac1{\sqrt2}\bigl[
a\,|0\rangle_Jm_0\otimes|00\rangle
+b\,|0\rangle_Jm_1\otimes|01\rangle
+|1\rangle_Jm_0\otimes|10\rangle
\bigr],
\tag{21.12}
$$

其 Schmidt 秩为三。故前两步容量至少分别为二、三；定理9.2的同一纯空白固定酉构造分别达到这两个数值，也属于允许的 CPTP 接收合同。结合三步构造，得到（21.1）。定理9.2给三步固定纯空白酉容量为五，遂得到所述首个严格分离。证明完毕。

这份具体通道不能继续精确服务第四个终端。由（21.5），初始来源为一时，第四次发射后的接收输入只含 $`t\otimes|0\rangle`$、$`t\otimes|1\rangle`$ 和 $`y\otimes|0\rangle`$，全部输出环境一。初始来源为零时，第四轮环境一的唯一分量来自 $`cb\,m_1\otimes z\otimes|1\rangle`$ 中的 $`b^2m_1\otimes v\otimes|1\rangle`$，输出为 $`b^2m_1\otimes t\otimes|1\rangle_E`$。因此

$$
\Pr\{E_4=1\mid i=0\}=|b|^4<1,
\qquad
\Pr\{E_4=1\mid i=1\}=1.
\tag{21.13}
$$

对 Bell 输入，这给参考的计算基标签与第四轮环境之间的相关性。若能仅由接收器恢复完整纯目标，则解码后的纯目标必须与剩余环境成乘积；局部解码不改变参考—环境边缘，与（21.13）矛盾。此失败只针对（21.3）的具体通道，没有判定四步固定 CPTP 的最小容量。

前三步的容量收益不依赖丢弃来源信息：这三轮环境均与数据及参考独立，承担的是可丢弃的确定阶段输出。将这些输出都强制成同一纯空白且禁止额外丢弃环境，会回到第9节的另一份合同。

## 追加锚（本行以下为增补区）

## 22. 任意校准候选集的尺度容量与稀疏增长律

**定义 22.1（相位集合的分离数及终端任务）。** 沿用定义1.1的等权两态来源及其未知共同相位。相位圆记为 $`\mathbb T=\mathbb R/(2\pi\mathbb Z)`$，其测地距离为

$$
d_{\mathbb T}(\vartheta,\varphi)
=\min_{j\in\mathbb Z}|\vartheta-\varphi+2\pi j|.
\tag{22.1}
$$

对任意非空集合 $`\Theta\subseteq\mathbb T`$ 和 $`\delta>0`$，定义

$$
P(\Theta,\delta)
=\max\bigl\{|A|:A\subseteq\Theta,\
d_{\mathbb T}(\vartheta,\varphi)\ge\delta
\text{ 对全部不同的 }\vartheta,\varphi\in A\bigr\}.
\tag{22.2}
$$

圆周有限且距离分离，故上述集合的基数有有限整数上界；非空性保证最大值至少为一，并有一份有限集合取得该整数。这里不要求 $`\Theta`$ 闭、可测或具有正长度。

将定义18.1的弧 $`I`$ 换为 $`\Theta`$，记完整参考、活动记忆及档案恢复的最小单终端接收维数为 $`k_n^{(\epsilon)}(\Theta)`$。编码和解码可以依赖 $`\Theta,n,\epsilon`$，不能依赖实际相位或来源输入；参考与活动记忆不可访问。本节不要求这些终端编码之间具有共同在线更新。

置

$$
a_*:=\frac{\alpha^3}{6\pi^2},\qquad
C_*:=1+2\sum_{r=1}^{\infty}e^{-a_*r^2}<\infty,
\qquad
J_\epsilon:=\left\lceil\frac1{\sqrt2\epsilon}\right\rceil,
\quad \alpha=\frac{\sqrt5-1}{2}.
\tag{22.3}
$$

**定理 22.2（任意候选集的统一尺度容量）。** 对任意非空 $`\Theta\subseteq\mathbb T`$、$`n\ge4`$ 及 $`0<\epsilon<1`$，有

$$
\boxed{
\max\left\{1,\frac{1-\epsilon}{4C_*}
P(\Theta,n^{-1/2})\right\}
\le k_n^{(\epsilon)}(\Theta)
\le\min\left\{2n-1,\
4J_\epsilon P(\Theta,n^{-1/2})\right\}.
}
\tag{22.4}
$$

特别地，固定 $`\epsilon`$ 后，

$$
k_n^{(\epsilon)}(\Theta)
=\Theta_\epsilon\bigl(P(\Theta,n^{-1/2})\bigr),
\tag{22.5}
$$

其中上下常数统一于候选集和终端编号，因而也允许候选集随 $`n`$ 改变。参数分辨率、可区分网与压缩记忆的联系已有文献先例；[^phase_metric_population] 本节针对上述关联来源及任意候选集合证明有限终端双边界。式（22.5）右侧的 $`\Theta_\epsilon(\cdot)`$ 表示双边阶估计，与候选集合符号相区别。

证明。令 $`\delta=n^{-1/2}`$，取一份取得最大分离数的集合
 $`A=\{\vartheta_1,\ldots,\vartheta_q\}`$，其中
 $`q=P(\Theta,\delta)`$。

**分离目标的共同解码下界。** 对相同 Bell 初始参考输入，记相位 $`\vartheta_j`$ 的纯联合目标为 $`|\Psi_{j,n}\rangle`$。式（19.4）及（5.17）给

$$
|\langle\Psi_{j,n}|\Psi_{k,n}\rangle|
\le\exp\left\{-\alpha^3
\left\lfloor\frac{n-1}{3}\right\rfloor
\sin^2\frac{d_{\mathbb T}(\vartheta_j,\vartheta_k)}2\right\}.
\tag{22.6}
$$

对 $`0\le d\le\pi`$，有 $`\sin(d/2)\ge d/\pi`$；对 $`n\ge4`$，有 $`\lfloor(n-1)/3\rfloor\ge n/6`$。故

$$
|\langle\Psi_{j,n}|\Psi_{k,n}\rangle|
\le e^{-a_*n d_{\mathbb T}(\vartheta_j,\vartheta_k)^2}.
\tag{22.7}
$$

固定 $`j`$，从 $`\vartheta_j`$ 分别沿顺时针及逆时针方向排列距离不超过 $`\pi`$ 的其余点；若有对径点，只归入一侧。同一侧第 $`r`$ 个点的距离至少为 $`r\delta`$：首个距离至少为 $`\delta`$，相邻点之间的弧长不超过 $`\pi`$，因而等于它们的测地距离，也至少为 $`\delta`$。因此 Gram 矩阵 $`G_{jk}=\langle\Psi_{j,n}|\Psi_{k,n}\rangle`$ 的每个绝对行和满足

$$
\sum_k|G_{jk}|
\le1+2\sum_{r=1}^{\infty}e^{-a_*n(r\delta)^2}
=C_*.
\tag{22.8}
$$

令 $`Q=q^{-1}\sum_j|\Psi_{j,n}\rangle\langle\Psi_{j,n}|`$。令 $`V`$ 为以这些目标向量为列的矩阵，则 $`VV^*`$ 与 Gram 矩阵 $`G=V^*V`$ 具有相同非零特征值。式（22.8）的最大绝对行和控制 Hermitian 矩阵 $`G`$ 的谱范数；以下 $`\|\cdot\|_\infty`$ 均表示算子谱范数。因此

$$
\|Q\|_\infty=\frac{\|G\|_\infty}{q}
\le\frac{C_*}{q}.
\tag{22.9}
$$

任取维数 $`D`$ 的合法编码及同一个解码器。不可访问系统 $`R=JM`$ 的维数为四。对编码所得各 $`KR`$ 态使用 $`0\preceq\tau_j\preceq I_{KR}`$，与（19.9）同样的正性及幺性计算给

$$
\frac1q\sum_j
\operatorname{Tr}\bigl[
|\Psi_{j,n}\rangle\langle\Psi_{j,n}|
(\mathcal D\otimes\operatorname{id}_R)(\tau_j)
\bigr]
\le\frac{4DC_*}{q}.
\tag{22.10}
$$

半迹误差不小于一减去目标重叠。因此任何同一解码器的最坏误差 $`e_n`$ 满足

$$
e_n\ge\max\{0,1-4DC_*/q\}.
\tag{22.11}
$$

若要求 $`e_n\le\epsilon`$，即得（22.4）的下界。这里只对有限候选子集取平均，不需要在 $`\Theta`$ 上定义概率测度。

**相位网覆盖与物理编码上界。** 最大分离集同时给一份 $`\delta`$ 网：若存在 $`\vartheta\in\Theta`$ 与全部 $`\vartheta_j`$ 的距离均至少为 $`\delta`$，将它加入就得到更大的分离集，矛盾。因此 $`\Theta`$ 被以这些点为中心、半径 $`\delta`$ 的弧覆盖。因 $`n\ge4`$，每条弧长 $`2\delta\le1<2\pi`$，可分别提升为实区间。

把每条弧等分为 $`J_\epsilon`$ 段，取中点作为已知参考相位。至多得到 $`qJ_\epsilon`$ 个参考点，每个实际候选距某个参考点不超过

$$
h=\frac{\delta}{J_\epsilon}
\le\frac{\sqrt2\epsilon}{\sqrt n}.
\tag{22.12}
$$

参考点可以位于候选集之外；它们只用于定义一个已知子空间，并不声称实际来源具有这些相位。取所有参考相位的共同档案支撑之和，令其投影为 $`P_0`$、秩为 $`r`$。由定理3.2，各参考相位的支撑维数至多四，故

$$
r\le4qJ_\epsilon.
\tag{22.13}
$$

在实际相位与对应参考相位之间，选取实现测地距离的实提升差。式（18.6）—（18.8）使用同一个标量相位控制整个来源输入空间，且 $`g_n^2\le n`$。因为参考输出全部落在 $`P_0`$ 内，实际输出在补空间的质量算子满足

$$
T_{\vartheta,n}^*[(I-P_0)\otimes I_M]T_{\vartheta,n}
\preceq\frac{h^2g_n^2}{4}I_M
\preceq\frac{\epsilon^2}{2}I_M.
\tag{22.14}
$$

将（18.12）的投影编码及失败重置应用于 $`P_0`$，就得到维数 $`r`$ 的全域 CPTP 编码和解码。由（18.13）—（18.14），对任意参考纯化及任意实际候选，相同通道的联合恢复半迹误差至多 $`\epsilon`$。丢弃额外纯化参考后仍保持此界。网和通道不使用未知实际相位；只在误差证明中为每个候选选择一个临近参考点。结合（22.13）得到第二个上界；全圆精确编码另给 $`2n-1`$。证明完毕。

**推论 22.3（可数零测度候选集的不同容量增长）。** 固定 $`0<\epsilon<1`$。对任意 $`\beta>0`$，令

$$
\Theta_\beta=\{0\}\cup\{j^{-\beta}:j\ge1\},
\qquad
\Theta_{\exp}=\{0\}\cup\{2^{-j}:j\ge0\},
\tag{22.15}
$$

均视为相位圆上 $`[0,1]`$ 内的集合。它们都紧、可数、Haar 零测度，但单终端容量分别满足

$$
\boxed{
k_n^{(\epsilon)}(\Theta_\beta)
=\Theta_{\beta,\epsilon}\bigl(n^{1/[2(\beta+1)]}\bigr),
\qquad
k_n^{(\epsilon)}(\Theta_{\exp})
=\Theta_\epsilon(\log n).
}
\tag{22.16}
$$

证明。先计算 $`\Theta_\beta`$ 的小尺度分离数。取
 $`J=\lceil\delta^{-1/(\beta+1)}\rceil`$。前 $`J`$ 项至多贡献 $`J`$ 个分离点，剩余全部位于长度 $`J^{-\beta}`$ 的区间中；该区间至多容纳 $`1+J^{-\beta}/\delta`$ 个距离至少为 $`\delta`$ 的点。于是

$$
P(\Theta_\beta,\delta)
\le J+1+\frac{J^{-\beta}}\delta
=O_\beta(\delta^{-1/(\beta+1)}).
\tag{22.17}
$$

反向，对充分小的 $`\delta`$ 取
 $`J'=\lfloor(\beta/\delta)^{1/(\beta+1)}\rfloor-1`$。
均值定理给

$$
j^{-\beta}-(j+1)^{-\beta}
\ge\beta(j+1)^{-(\beta+1)}
\ge\delta\qquad(1\le j\le J').
\tag{22.18}
$$

故前 $`J'+1`$ 项组成分离集，得到匹配下界。这些点处于长度一的实区间内，实距离就是测地距离。

对 $`\Theta_{\exp}`$，令 $`J=\lceil\log_2(1/\delta)\rceil`$。前 $`J`$ 项至多贡献 $`J`$ 点，其余全部处于长度 $`2^{-J}\le\delta`$ 的区间，至多再贡献两点。反向，令 $`L=\lfloor\log_2(1/\delta)\rfloor`$，前 $`L+1`$ 项的最小相邻差为 $`2^{-L}\ge\delta`$，给匹配下界。因此

$$
P(\Theta_\beta,\delta)
=\Theta_\beta(\delta^{-1/(\beta+1)}),
\qquad
P(\Theta_{\exp},\delta)=\Theta(\log(1/\delta)).
\tag{22.19}
$$

代入定理22.2的 $`\delta=n^{-1/2}`$ 即得。两组序列都只在零处聚集，故其连同零的集合紧；可数性给零测度。证明完毕。

特别地，第19节的 $`\{0\}\cup\{1/j:j\ge1\}`$ 具有 $`n^{1/4}`$ 单终端容量阶；零测度不将其容量降为常数。几何收敛的候选序列则给对数阶，仍由定理19.2排除任意固定有限容量的全时域实现。这些区别全部发生在同一内部记忆通道及同一完整恢复任务下。

**推论 22.4（校准集合的箱维数与容量指数）。** 对固定非空 $`\Theta\subseteq\mathbb T`$，以分离数定义下、上箱维数

$$
\underline s=\liminf_{\delta\downarrow0}
\frac{\log P(\Theta,\delta)}{\log(1/\delta)},
\qquad
\overline s=\limsup_{\delta\downarrow0}
\frac{\log P(\Theta,\delta)}{\log(1/\delta)}.
\tag{22.20}
$$

则对每个固定 $`0<\epsilon<1`$，

$$
\boxed{
\liminf_{n\to\infty}\frac{\log k_n^{(\epsilon)}(\Theta)}{\log n}
=\frac{\underline s}{2},
\qquad
\limsup_{n\to\infty}\frac{\log k_n^{(\epsilon)}(\Theta)}{\log n}
=\frac{\overline s}{2}.
}
\tag{22.21}
$$

证明。定理22.2给
 $`\log k_n^{(\epsilon)}(\Theta)=\log P(\Theta,n^{-1/2})+O_\epsilon(1)`$。
令 $`\delta_n=n^{-1/2}`$，则 $`\log(1/\delta_n)=\tfrac12\log n`$。若 $`\delta_{n+1}<\delta\le\delta_n`$，分离数的单调性给

$$
P(\Theta,\delta_n)\le P(\Theta,\delta)
\le P(\Theta,\delta_{n+1}).
\tag{22.22}
$$

两端的对数尺度之比趋于一；夹逼表明沿 $`\delta_n`$ 取极限下、上限与沿全部 $`\delta\downarrow0`$ 相同。再除以 $`\log n`$ 即得（22.21）。证明完毕。

箱维数只记录幂次指数，并不替代（22.4）的完整尺度函数。例如有限集合与 $`\Theta_{\exp}`$ 均有零箱维数，但前者的终端容量有界，后者按对数发散。式（22.4）保留了这种区别；其上界仍是一族单终端编码，没有据此得到同一接收器的在线更新或同阶在线容量。

[^phase_metric_population]: Yuxiang Yang, Ge Bai, Giulio Chiribella and Masahito Hayashi, *Compression for quantum population coding*, [arXiv:1701.03372v8, §II Theorem 1 and §VI equations (93)–(106)](https://arxiv.org/html/1701.03372v8), [doi:10.1109/TIT.2017.2788407](https://doi.org/10.1109/TIT.2017.2788407). 该文研究独立同分布的规则参数族，以可区分网证明渐近总记忆的参数维数主阶；其有限维量子态族部分具有满秩、非简并谱以及参数连续变化或固定等明确条件。本文不把该结论直接套于任意稀疏相位集合。式（22.4）使用本卷来源的有限长度重叠估计与保参考编码，处理固定误差、关联档案及任意非空候选集；上述文献作为参数网与压缩关系的先例。

## 追加锚（本行以下为增补区）

## 23. 四步精确固定 CPTP 的最小容量为五

本节沿用第21节的已知非退化来源
$`m_0=a|0\rangle+b|1\rangle`$、$`m_1=|0\rangle`$，其中
$`ab\ne0`$、$`|a|^2+|b|^2=1`$。接收合同仍为定义12.1：接收器独立纯初始化，逐轮使用同一个全域 CPTP 通道，新环境丢弃后不再复用，全部持久系统计入接收容量；每个终端均须仅凭接收器恢复任意参考、活动记忆和完整档案的联合态。

**定理 23.1（四步的精确最小固定 CPTP 容量）。** 对上述任意已知非退化复振幅来源，

$$
\boxed{d_{\mathrm{CPTP},4}(a,b)=5.}
\tag{23.1}
$$

因此，四维接收器无法同时服务前四个精确终端，而五维已经足够。第9节同一纯空白固定酉合同在四步需要七维。以下给出一般 CPTP 合同的五维全域固定门，并证明它同时服务全部四个终端。

**证明中的标准可逆编码事实。** 以下回顾精确纠错的 Kraus 正交分解，并给出所需的证明，以明确处理第一步接收态可能混合的情形。这是 Knill–Laflamme 精确纠错条件及其张量因子结构的应用，参见 [Knill–Laflamme, *Theory of Quantum Error-Correcting Codes*, Theorems 3.2、3.5，式（19）—（20）](https://arxiv.org/abs/quant-ph/9604034)，不作为本节新结论。设纯态
$`|\Omega\rangle\in R\otimes S`$ 在 $`S`$ 上满 Schmidt 秩
$`s=\dim S`$。设编码通道
$`\mathcal E:\mathcal L(S)\to\mathcal L(K)`$ 有本地解码通道
$`\mathcal D`$，满足

$$
(\operatorname{id}_R\otimes\mathcal D\mathcal E)
(|\Omega\rangle\langle\Omega|)
=|\Omega\rangle\langle\Omega|.
\tag{23.2}
$$

则存在正数 $`p_1,\ldots,p_r`$ 和等距映射
$`W_\alpha:S\to K`$，使

$$
\mathcal E(X)=\sum_{\alpha=1}^r p_\alpha
W_\alpha XW_\alpha^\dagger,
\qquad
\sum_\alpha p_\alpha=1,
\qquad
W_\alpha^\dagger W_\beta=\delta_{\alpha\beta}I_S.
\tag{23.3}
$$

特别地，$`sr\le\dim K`$。若 $`\dim K<2s`$，则 $`r=1`$，编码在此支撑上是单个等距映射，编码后的联合态为纯态。

为验证这一标准事实，将（23.2）按 Schmidt 基展开。各 Schmidt 系数均非零，逐矩阵块比较即得
$`\mathcal D\mathcal E=\operatorname{id}`$ 在
$`\mathcal L(S)`$ 上成立。取编码 Kraus 算子 $`A_\alpha`$ 和解码 Kraus 算子 $`B_\beta`$。恒等通道的 Choi 矩阵秩为一，因此它的每个 Kraus 算子均为恒等嵌入的标量倍数，即
$`B_\beta A_\alpha=\lambda_{\beta\alpha}I_S`$；若解码输出含更大的档案空间，这里的 $`I_S`$ 解释为该支撑的自然嵌入。由解码的保迹性，

$$
A_\alpha^\dagger A_\gamma
=\sum_\beta (B_\beta A_\alpha)^\dagger
(B_\beta A_\gamma)
=c_{\alpha\gamma}I_S,
\qquad
c_{\alpha\gamma}=\sum_\beta
\overline{\lambda_{\beta\alpha}}\lambda_{\beta\gamma}.
\tag{23.4}
$$

对半正定矩阵 $`c`$ 作酉对角化，相应酉混合 Kraus 算子，再删去零算子，得到
$`F_\alpha^\dagger F_\beta=p_\alpha\delta_{\alpha\beta}I_S`$，其中 $`p_\alpha>0`$。置
$`W_\alpha=F_\alpha/\sqrt{p_\alpha}`$，便得（23.3）。各等距映射有两两正交的 $`s`$ 维像空间，因此 $`sr\le\dim K`$。

**四维不可能性的证明。** 反设存在四维接收器服务全部
$`n\le4`$。只需考虑 Bell 输入
$`(|0\rangle_J|0\rangle_M+|1\rangle_J|1\rangle_M)/\sqrt2`$。
未接收时，档案相对 $`JM`$ 的 Schmidt 秩在
$`n=2,3,4`$ 分别为 $`3,4,4`$。前两项由（21.11）—（21.12）给出。第三项也可不另作档案枚举：三步的 $`JM`$ 边缘正定，而来源的活动记忆通道为

$$
\mathcal T(X)=\langle0|X|0\rangle|m_0\rangle\langle m_0|
+\langle1|X|1\rangle|m_1\rangle\langle m_1|.
\tag{23.5}
$$

由于 $`m_0,m_1`$ 线性独立，$`\mathcal T(I)>0`$。若
$`\rho_{JM}\ge\lambda I_{JM}`$ 且 $`\lambda>0`$，则
$`(\operatorname{id}_J\otimes\mathcal T)(\rho_{JM})
\ge\lambda I_J\otimes\mathcal T(I)>0`$。故第四步仍有 Schmidt 秩四。

把前 $`n`$ 个接收门视为从完整档案到 $`K`$ 的累计编码通道是合法的：较早接收门与后续来源发射作用于不同系统，因而可交换。精确本地解码与上述标准事实遂表明：第二、三、四步的实际 $`JMK`$ 联合态均为纯态，接收器支撑秩分别为三、四、四。此处**没有**断言第一步为纯态；第一步可以具有秩二的可逆附加因子，以下论证允许这种情形。

对 $`j=2,3`$，将纯联合态写为

$$
|\Psi_j\rangle=\frac1{\sqrt2}\sum_{i=0}^1
|i\rangle_J\bigl(|0\rangle_Mu_j^i+|1\rangle_Mv_j^i\bigr),
\quad
H_j=\operatorname{span}\{u_j^0,u_j^1\},
\quad
G_j=\operatorname{span}\{v_j^0,v_j^1\}.
\tag{23.6}
$$

这些向量由对应未接收档案向量经同一等距编码得到。由第二步展开，编码前的两组系数为

$$
\begin{array}{ll}
\widetilde u_2^0=a^2|00\rangle+b|01\rangle,
&\widetilde u_2^1=a|10\rangle,\\
\widetilde v_2^0=ab|00\rangle,
&\widetilde v_2^1=b|10\rangle;
\end{array}
\tag{23.7}
$$

这里波浪号表示等距编码前的档案坐标，即 $`u_j^i=W_j\widetilde u_j^i`$、$`v_j^i=W_j\widetilde v_j^i`$，其中 $`W_j`$ 是该终端的等距编码。同理，第三步的档案坐标为

$$
\begin{array}{ll}
\widetilde u_3^0=a^3|000\rangle+ab|010\rangle+ab|001\rangle,
&\widetilde u_3^1=a^2|100\rangle+b|101\rangle,\\
\widetilde v_3^0=a^2b|000\rangle+b^2|010\rangle,
&\widetilde v_3^1=ab|100\rangle.
\end{array}
\tag{23.8}
$$

非退化性及这些向量的计算基支撑给出

$$
\dim H_2=\dim G_2=\dim H_3=\dim G_3=2,
\qquad
\dim(H_2+G_2)=3,
\qquad
H_3+G_3=K.
\tag{23.9}
$$

固定一次接收通道的任意 Stinespring 等距映射
$`V:K\otimes\mathcal B\to K\otimes E`$。第三、四轮发射后、接收前，接收输入的支撑分别为

$$
L_3=(H_2\otimes|0\rangle)\oplus(G_2\otimes|1\rangle),
\qquad
L_4=(H_3\otimes|0\rangle)\oplus(G_3\otimes|1\rangle).
\tag{23.10}
$$

二者均为四维：来源发射把（23.6）中的系数分别配到
$`|i\rangle_Jm_0`$ 和 $`|i\rangle_Jm_1`$，这四个
$`JM`$ 向量线性独立。第二、三、四步联合态均为纯态，故第三、四轮的新环境各为固定纯向量，且

$$
V|_{L_3}=U_3\otimes\eta_3,
\qquad
V|_{L_4}=U_4\otimes\eta_4,
\tag{23.11}
$$

其中 $`U_3:L_3\to K`$、$`U_4:L_4\to K`$ 都是满射等距映射。确切地说，纯输入经等距映射后仍纯，而其 $`JMK`$ 边缘纯，故与新环境成乘积；比较满 Schmidt 支撑的系数即可得到（23.11）。这一步也不要求先前已丢弃的各环境分别为纯态。

置 $`q=\langle\eta_3,\eta_4\rangle`$、$`\gamma=|q|`$。
等距性给
$`\langle x,y\rangle=q\langle U_3x,U_4y\rangle`$
（$`x\in L_3,y\in L_4`$），因而

$$
P_{L_3}P_{L_4}P_{L_3}=\gamma^2P_{L_3}.
\tag{23.12}
$$

若 $`\gamma=1`$，则 $`L_3=L_4`$；按输入位分块得到
$`H_2=H_3`$、$`G_2=G_3`$，与（23.9）的三维和四维矛盾。

若 $`\gamma=0`$，则 $`L_3\perp L_4`$，于是
$`H_3=H_2^\perp`$、$`G_3=G_2^\perp`$。因此

$$
\dim(H_3\cap G_3)
=\dim(H_2+G_2)^\perp=1,
\tag{23.13}
$$

仍与 $`H_3+G_3=K`$ 矛盾。

最后设 $`0<\gamma<1`$。定义第三轮两种输入位的接收像空间

$$
P=U_3(H_2\otimes|0\rangle),
\qquad
Q=U_3(G_2\otimes|1\rangle)=P^\perp,
\tag{23.14}
$$

并用 $`P',Q'`$ 表示第四轮的对应像空间。四者均二维。不同输入位在接收前正交，且 $`q\ne0`$，故
$`P\perp Q'`$、$`Q\perp P'`$。比较维数可得
$`P'=P`$、$`Q'=Q`$。

式（23.12）且 $`\gamma<1`$ 又给
$`L_3\cap L_4=\{0\}`$，从而
$`H_2\cap H_3=G_2\cap G_3=\{0\}`$。这些均为四维
$`K`$ 中的二维空间，故
$`H_2+H_3=G_2+G_3=K`$。利用线性性，令
$`F=\operatorname{span}\{\eta_3,\eta_4\}`$，便得到固定接收门的**全域**约束

$$
V(K\otimes|0\rangle)\subset P\otimes F,
\qquad
V(K\otimes|1\rangle)\subset Q\otimes F.
\tag{23.15}
$$

现在把（23.15）用回第二轮，允许第一轮联合态为任意混态。来源等距发射
$`\mathsf S|0\rangle=m_0\otimes|0\rangle`$、
$`\mathsf S|1\rangle=m_1\otimes|1\rangle`$ 满足

$$
(\langle1|_M\otimes I_{\mathcal B})\mathsf S
=b|0\rangle_{\mathcal B}\langle0|_M.
\tag{23.16}
$$

所以任何一轮中，新活动记忆的 $`|1\rangle\langle1|`$
对角块只经过输入位零。由（23.15），接收并丢弃新环境后，这个对角块的接收器支撑必包含于 $`P`$。第二步实际联合态为（23.6）的纯态，偏迹参考后，该对角块为
$`\frac12\sum_i|v_2^i\rangle\langle v_2^i|`$，故
$`G_2\subset P`$。两者维数均为二，得到 $`G_2=P`$。同理第三步给 $`G_3=P`$。这与
$`G_2\cap G_3=\{0\}`$ 矛盾。

全部 $`\gamma`$ 情形都已排除，四维不可能。维数更小已由第三步 Schmidt 秩下界排除，因此得到（23.1）的下界。

**五维接收向量。** 取五维接收器的正交单位基
$`u,v,w,t,e`$，接收初态为 $`w`$。定义正实数及两层正交旋转

$$
c=\sqrt{|a|^4+|b|^2},\qquad
d=\sqrt{c^2+|b|^2},
\qquad
z=\frac{a^2u+bv}{c},\qquad
y=\frac{-\overline b\,u+\overline{a}^{2}v}{c},
\tag{23.17}
$$

$$
q=\frac{\overline b\,y+\overline{a}^{2}e}{c},
\qquad
f=\frac{-a^2y+be}{c}.
\tag{23.18}
$$

因此 $`z,y`$ 是 $`\operatorname{span}\{u,v\}`$ 的正交单位基，
$`q,f`$ 是 $`\operatorname{span}\{y,e\}`$ 的正交单位基，
$`z,q,f`$ 是 $`\operatorname{span}\{u,v,e\}`$ 的正交单位基。
再定义

$$
s=\frac{-cv+be}{d},
\qquad
g=\frac{\overline b\,v+ce}{d},
\qquad
r=\frac{df-cs}{b}.
\tag{23.19}
$$

$`s,g`$ 是 $`\operatorname{span}\{v,e\}`$ 的正交单位基，所以
$`s\perp u`$。展开（23.17）—（23.18）给出关键恒等式

$$
s=\frac{-\overline b\,z+cf}{d}.
\tag{23.20}
$$

其验证为

$$
-\overline b\,z+cf
=-\frac{a^2\overline b}{c}u
-\frac{|b|^2}{c}v-a^2y+be
=-cv+be.
\tag{23.21}
$$

由（23.20）有 $`\langle s,f\rangle=c/d`$，于是

$$
\langle s,r\rangle=0,
\qquad
\|r\|^2=\frac{d^2+c^2-2c^2}{|b|^2}=1,
\qquad
cs+br=df.
\tag{23.22}
$$

所以 $`s,r`$ 是 $`\operatorname{span}\{z,f\}`$ 的正交单位基，
$`q,s,r`$ 是 $`\operatorname{span}\{u,v,e\}`$ 的正交单位基。
以上等式对一般复数 $`a,b`$ 成立；除以 $`b`$ 合法来自非退化假设。

**同一个全域酉。** 每轮取新环境 $`E=\mathbb C^2`$。定义
$`V:K\otimes\mathcal B\to K\otimes E`$ 如下，表中后一位为输入位或输出环境：

$$
\begin{aligned}
V(w\otimes0)&=t\otimes0,
&V(t\otimes0)&=u\otimes1,\\
V(w\otimes1)&=q\otimes0,
&V(t\otimes1)&=v\otimes1,\\
V(z\otimes0)&=s\otimes0,
&V(q\otimes0)&=w\otimes1,\\
V(u\otimes1)&=r\otimes0,
&V(f\otimes0)&=t\otimes1,\\
V(g\otimes1)&=w\otimes0,
&V(s\otimes1)&=e\otimes1.
\end{aligned}
\tag{23.23}
$$

输入位零时的五个接收向量为 $`w,z,t,q,f`$，是正交单位基；输入位一时为 $`w,u,g,t,s`$，也是正交单位基。输出环境零时的接收向量为
$`t,q,s,r,w`$，环境一时为 $`u,v,w,t,e`$，两组仍分别为正交单位基。因此（23.23）将一个十维正交单位基映到另一个，确定全域酉。运行中固定使用

$$
\mathcal C(X)=\operatorname{Tr}_E(VXV^\dagger).
\tag{23.24}
$$

**四步实际联合态。** 对初始活动记忆基态 $`|i\rangle`$，前三步及第四步接收后的联合向量为

$$
\begin{aligned}
\Psi_1^0&=m_0\otimes t,
&\Psi_1^1&=m_1\otimes q,\\
\Psi_2^0&=a m_0\otimes u+b m_1\otimes v,
&\Psi_2^1&=m_0\otimes w,\\
\Psi_3^0&=c m_0\otimes s+ab m_1\otimes r,
&\Psi_3^1&=a m_0\otimes t+b m_1\otimes q,\\
\Psi_4^0&=ad m_0\otimes t+cb m_1\otimes e,
&\Psi_4^1&=m_0\otimes(a^2u+bw)+ab m_1\otimes v.
\end{aligned}
\tag{23.25}
$$

两种初始基态在每一步输出相同的环境纯向量，环境序列为

$$
\eta_1=|0\rangle,\qquad
\eta_2=|1\rangle,\qquad
\eta_3=|0\rangle,\qquad
\eta_4=|1\rangle.
\tag{23.26}
$$

首步使用 $`w0,w1`$ 两条映射。第二步的接收输入为
$`a m_0\otimes t0+b m_1\otimes t1`$ 和
$`m_0\otimes q0`$，故得到（23.25）第二行且环境为一。第三步的接收输入为

$$
c m_0\otimes z0+ab m_1\otimes u1,
\qquad
a m_0\otimes w0+b m_1\otimes w1,
\tag{23.27}
$$

给（23.25）第三行且环境为零。第四步的接收输入为

$$
\begin{aligned}
&a m_0\otimes(cs+br)0+cb m_1\otimes s1
=ad m_0\otimes f0+cb m_1\otimes s1,\\
&m_0\otimes(a^2t+bq)0+ab m_1\otimes t1.
\end{aligned}
\tag{23.28}
$$

由（23.23）均输出环境一，给（23.25）第四行。环境序列（23.26）对两个初始基态相同，故线性性覆盖任意输入相干和任意参考纠缠；混合输入可取纯化。

**终端解码。** 在每个 $`n\le4`$ 的指定终端，本地重新准备（23.26）的前 $`n`$ 个确定环境纯态，逆序使用同一个 $`V^\dagger`$，恢复全部发出位，最后丢弃回到初态 $`w`$ 的接收器。若 $`\mathsf V_n`$ 表示把固定 $`V`$ 逐位置作用于接收器与完整档案的酉，则解码通道为

$$
\mathcal D_n(X)=\operatorname{Tr}_K\left[
\mathsf V_n^\dagger
\bigl(X\otimes|\eta_1\cdots\eta_n\rangle
\langle\eta_1\cdots\eta_n|\bigr)
\mathsf V_n\right].
\tag{23.29}
$$

这是全域 CPTP 通道。较早接收门与后续来源发射作用于不同系统，可交换次序。因此（23.25）—（23.26）保证（23.29）对所有 $`J,\rho_{JM}`$ 恢复完整参考—活动记忆—档案联合态。运行时环境即时丢弃且不复用；终端新准备的纯态仅依赖终端步数和已知固定构造，不携带输入信息。全部持久系统即为五维 $`K`$，运行门不随步数更换。

由此五维构造与已证四维不可能性，得到 $`d_{\mathrm{CPTP},4}(a,b)=5`$，定理得证。四步的固定 CPTP 接收容量比同一纯空白固定酉合同的七维小两维；这里的精确恢复仍覆盖全部输入、全部参考及完整档案。

## 追加锚（本行以下为增补区）

## 24. 局部相位导数支撑与恢复精度的阶乘上界

本节仍取定义22.1的单终端、完整参考恢复合同。沿用（5.2）的 $`V_n,h_n,b_n`$ 及（18.1）的

$$
g_n^2=V_n+h_n^2\le n.
\tag{24.1}
$$

以下构造使用标准指数函数的 Taylor 余项及条件 Hoeffding 估计。需要核对的是同一个移心相位能否覆盖全部来源输入，以及这些向量能否放入只在档案一侧作用的有限维支撑；不赋予接收器读取实际相位的权限。

**定理 24.1（网半径、导数阶数与完整恢复误差）。** 给定非空 $`\Theta\subseteq\mathbb T`$、$`n\ge4`$、$`h>0`$ 及整数 $`k\ge1`$，存在一份维数至多

$$
4kP(\Theta,h)
\tag{24.2}
$$

的全域 CPTP 编解码，对全部候选相位及全部参考完整输入，其联合半迹恢复误差至多

$$
\boxed{
\min\left\{1,\;
2\sqrt{\frac{(g_n^2h^2/2)^k}{k!}}\right\}
\le
\min\left\{1,\;
2\sqrt{\frac{(nh^2/2)^k}{k!}}\right\}.
}
\tag{24.3}
$$

特别地，只要右侧的第二项不超过 $`\epsilon`$，就有

$$
\boxed{
k_n^{(\epsilon)}(\Theta)
\le\min\{2n-1,\;4kP(\Theta,h)\}.
}
\tag{24.4}
$$

常数统一于 $`\Theta,n,h,k`$。本定理允许集合不可测、非闭，也允许 $`h>\pi`$；此时分离数为一。

证明。先建立两个初始来源基态都适用的共同移心矩估计。令

$$
Y_i=S_n-\mathbb E_iS_n,
\qquad
X=S_n-b_n,
\qquad
c_i=\mathbb E_iS_n-b_n=(i-\tfrac12)h_n.
\tag{24.5}
$$

（5.7）的条件取值区间宽度及 Hoeffding 指数估计给，对全部实数 $`t`$，

$$
\mathbb E_i e^{tY_i}\le e^{V_nt^2/8}.
\tag{24.6}
$$

同时使用 $`t`$ 与 $`-t`$，并用 $`|c_i|=h_n/2`$ 及 $`\cosh u\le e^{u^2/2}`$，得到

$$
\begin{aligned}
\mathbb E_i(e^{tX}+e^{-tX})
&\le2e^{V_nt^2/8}\cosh(tc_i)\\
&\le2e^{g_n^2t^2/8}.
\end{aligned}
\tag{24.7}
$$

这里没有声称 $`X`$ 在每个初态下均值为零。对 $`t>0`$，事件 $`|X|\ge u`$ 上有 $`e^{tX}+e^{-tX}\ge e^{tu}`$。优化 $`t`$ 给

$$
\Pr_i\{|S_n-b_n|\ge u\}
\le2e^{-2u^2/g_n^2}.
\tag{24.8}
$$

由尾积分公式，对每个整数 $`k\ge1`$，

$$
\begin{aligned}
\mathbb E_i|S_n-b_n|^{2k}
&=2k\int_0^\infty u^{2k-1}
\Pr_i\{|S_n-b_n|\ge u\}\,du\\
&\le2k!\left(\frac{g_n^2}{2}\right)^k.
\end{aligned}
\tag{24.9}
$$

**每个参考相位的导数支撑。** 在档案 $`H_n`$ 上定义自伴总荷算子

$$
\widehat Q_n|w\rangle
=\left(\sum_{t=1}^nw_t\right)|w\rangle.
\tag{24.10}
$$

它在整个计算基上定义；实际来源只占其中的合法词。对参考相位 $`\varphi`$，令 $`S_n(\varphi)`$ 为定理3.2中的四维档案支撑，定义

$$
S_{n,k}(\varphi)
=\sum_{r=0}^{k-1}
(\widehat Q_n-b_nI)^rS_n(\varphi).
\tag{24.11}
$$

每个线性像的维数至多四，故 $`\dim S_{n,k}(\varphi)\le4k`$。这些子空间由已知来源、参考相位及终端编号确定。

对实提升差 $`t=\vartheta-\varphi`$，共同相位的实际作用给

$$
T_{\vartheta,n}
=(e^{it\widehat Q_n}\otimes I_M)T_{\varphi,n}.
\tag{24.12}
$$

以同一个标量 $`e^{ib_nt}`$ 定义近似算子

$$
A_{\varphi,k}(t)
=e^{ib_nt}\sum_{r=0}^{k-1}\frac{(it)^r}{r!}
[(\widehat Q_n-b_nI)^r\otimes I_M]T_{\varphi,n}.
\tag{24.13}
$$

它的档案分量全部落在 $`S_{n,k}(\varphi)`$ 内，不要求近似算子本身等距。对实数 $`x`$，积分形式的 Taylor 余项给

$$
\left|e^{ix}-\sum_{r=0}^{k-1}\frac{(ix)^r}{r!}\right|
\le\frac{|x|^k}{k!}.
\tag{24.14}
$$

这是沿实轴对 $`e^{ix}`$ 的估计，不额外产生 $`e^{|x|}`$ 因子。逐档案词展开并使用（24.9），对两个输入基向量都有

$$
\|(T_{\vartheta,n}-A_{\varphi,k}(t))|i\rangle\|^2
\le\frac{|t|^{2k}}{(k!)^2}
\mathbb E_i|S_n-b_n|^{2k}
\le2\frac{(g_n^2t^2/2)^k}{k!}.
\tag{24.15}
$$

两个误差列仍处于不同档案首位扇区，因而正交。于是同一个算子界成立：

$$
(T_{\vartheta,n}-A_{\varphi,k}(t))^*
(T_{\vartheta,n}-A_{\varphi,k}(t))
\preceq2\frac{(g_n^2t^2/2)^k}{k!}I_M.
\tag{24.16}
$$

特别地，张量任意参考后仍保留该界；没有分别替换两个来源输入的相位。

**合并参考点并进行物理压缩。** 取取得 $`q=P(\Theta,h)`$ 的最大分离集。与第22节相同，极大性保证每个实际候选都与某个中心的距离小于 $`h`$。若 $`h>\pi`$，只需任取一个中心，圆周上全部点与它的测地距离均小于 $`h`$。对每个候选与相应中心，取实现测地距离的实提升差 $`t`$。

令 $`P_0`$ 投影到全部 $`q`$ 个中心的 $`S_{n,k}(\varphi)`$ 之和，记其秩为 $`r`$，则 $`r\le4kq`$。由（24.13）与（24.16），

$$
T_{\vartheta,n}^*[(I-P_0)\otimes I_M]T_{\vartheta,n}
\preceq d_*I_M,
\qquad
d_*:=2\frac{(g_n^2h^2/2)^k}{k!}.
\tag{24.17}
$$

对这个子空间使用（18.12）的投影编码与同一空间内的失败重置。任意纯化输入的实际失败质量 $`d`$ 满足 $`d\le\min\{1,d_*\}`$；恢复态的目标重叠至少为 $`(1-d)^2`$。因此（18.14）给统一半迹误差

$$
\sqrt{1-(1-d)^2}\le\sqrt{2d}
\le2\sqrt{\frac{(g_n^2h^2/2)^k}{k!}}.
\tag{24.18}
$$

半迹距离本身至多为一，故得到（24.3）。对混态丢弃额外纯化参考即可。网点及通道均预先固定，候选依赖的临近点选择仅用于误差证明。再与全圆精确编码比较，得到（24.4）。证明完毕。

**推论 24.2（固定涨落网的阶乘精度界）。** 定义

$$
K_\epsilon
=\min\{k\in\mathbb N:k\ge1,\;2^kk!\ge4/\epsilon^2\}.
\tag{24.19}
$$

则

$$
\boxed{
k_n^{(\epsilon)}(\Theta)
\le\min\{2n-1,\;4K_\epsilon P(\Theta,n^{-1/2})\}.
}
\tag{24.20}
$$

而且当 $`\epsilon\downarrow0`$ 时，

$$
K_\epsilon\sim
\frac{2\log(1/\epsilon)}{\log\log(1/\epsilon)}.
\tag{24.21}
$$

证明。在定理24.1中取 $`h=n^{-1/2}`$，误差上界为 $`2/\sqrt{2^kk!}`$。（24.19）保证其不超过 $`\epsilon`$。最后使用 $`\log(k!)=k\log k-k+O(\log k)`$，对（24.19）的最小整数条件取对数即得（24.21）。证明完毕。

**推论 24.3（随精度扩大的局部相位网）。** 令

$$
L_\epsilon
=\left\lceil\frac{\log(4/\epsilon^2)}{\log8}\right\rceil,
\qquad
H_{n,\epsilon}
=\sqrt{\frac{L_\epsilon}{4en}}.
\tag{24.22}
$$

则对全部 $`n\ge4`$、$`0<\epsilon<1`$，

$$
\boxed{
k_n^{(\epsilon)}(\Theta)
\le\min\{2n-1,\;4L_\epsilon
P(\Theta,H_{n,\epsilon})\}.
}
\tag{24.23}
$$

证明。由 $`k!\ge(k/e)^k`$，在定理24.1中取 $`h=\sqrt{k/(4en)}`$ 后，其误差至多

$$
2\sqrt{\frac{(k/(8e))^k}{k!}}
\le2\cdot8^{-k/2}.
\tag{24.24}
$$

取 $`k=L_\epsilon`$ 即满足目标误差。若 $`H_{n,\epsilon}>\pi`$，定理24.1仍适用；同时保留 $`2n-1`$ 的精确容量上限。证明完毕。

若某个候选集满足定量小尺度估计

$$
P(\Theta,h)\le C h^{-s}
\quad(0<h\le h_0),\qquad 0\le s\le1,
\tag{24.25}
$$

则在 $`H_{n,\epsilon}\le h_0`$ 的范围内，（24.23）进一步给

$$
k_n^{(\epsilon)}(\Theta)
\le\min\left\{2n-1,\;
4C(4e)^{s/2}n^{s/2}L_\epsilon^{1-s/2}\right\}.
\tag{24.26}
$$

所以误差趋零时有 $`O(n^{s/2}[\log(1/\epsilon)]^{1-s/2})`$ 的联合上界；这里只在明确的小尺度条件内使用该式。仅知道箱维数为 $`s`$，不能自动替代（24.25）的常数统一估计。

对弧长为 $`\ell`$ 的候选弧，总有 $`P(I,h)\le1+\ell/h`$，所以（24.23）给

$$
k_n^{(\epsilon)}(I)
\le\min\left\{2n-1,\;
4L_\epsilon+8\ell\sqrt{enL_\epsilon}\right\}.
\tag{24.27}
$$

它保留了弧长与精度的共同作用；若是单一已知相位，仍可直接使用四维精确编码。全圆还可以结合第5节的总荷窗口上界，其他候选集也可以同时使用第22节的网格上界与（24.20），取其中最小者。

本节证明的是可实施的单终端精度上界，没有给出相同精度依赖的下界，也没有建立不同终端之间的共同在线更新。来源的共同移心矩、档案侧导数支撑和全参考误差转换构成这里的具体推导；一般 Taylor 近似、阶乘估计及 Hoeffding 工具作为既有前置使用。

## 追加锚（本行以下为增补区）


## 25. 五终端的确定正交交替环境恰好需要七维

本节仍取已知非退化来源
$`m_0=a|0\rangle+b|1\rangle,\ m_1=|0\rangle`$，
$`ab\ne0,\ |a|^2+|b|^2=1`$。固定接收通道取一份固定 Stinespring 等距映射
$`V:K\otimes B\to K\otimes E`$，接收器独立纯初始化。
**定义 25.1（确定正交交替环境合同）。** 在定义12.1的接收合同上额外要求：对全部初始输入及参考，在前五轮新环境依次为与全部其余系统独立的确定纯态
$$
\eta_0,\eta_1,\eta_0,\eta_1,\eta_0,
\qquad \langle\eta_0,\eta_1\rangle=0.
\tag{25.1}
$$
同一射线允许任意轮次的全局相位，均吸收进联合态向量的选择。

**定理 25.2（五步正交交替环境的精确容量）。** 满足定义25.1的精确接收器所需最小维数恰为七。因而一般固定 CPTP 五终端容量满足

$$
5\le d_{\mathrm{CPTP},5}(a,b)\le7.
\tag{25.1a}
$$

这里七维下界只适用于确定正交交替环境合同；一般 CPTP 的下界五来自定理23.1及终端集合的包含。下面不排除一般五终端五维或六维通道，也不要求一般通道具有非混合的早期累计环境。

**证明：前三步的固定记号。**

记 $`D=\dim K`$。若 $`D<6`$，可把 $`K`$ 等距嵌入六维空间，并将固定 Stinespring 等距映射在额外输入子空间上等距延拓；必要时扩大未使用的环境空间。初态和实际轨迹均保留，因此反证只需设 $`D=6`$。以下也直接保留 $`D\le6`$ 的维数计数。

初态为单位向量 $`k`$。确定纯环境使每个初始基态的实际 $`MK`$ 态为纯向量，且同轮两列具有同一个环境向量。第一轮定义
$$
V(k0)=p\eta_0,\qquad V(k1)=q\eta_0,
\tag{25.2}
$$
故 $`p,q`$ 正交归一，第一轮两列为 $`m_0p,m_1q`$。第二轮定义
$$
V(p0)=u\eta_1,\quad V(p1)=v\eta_1,\quad
V(q0)=w\eta_1.
\tag{25.3}
$$
由于 $`p0,p1,q0`$ 正交，$`u,v,w`$ 正交归一，第二轮两列为
$$
a m_0u+b m_1v,\qquad m_0w.
\tag{25.4}
$$
上述逐向量映射由 $`m_0,m_1`$ 线性独立及非零系数逐项抽出，并不额外假设输入位可以任意独立制备。

置
$$
c=\sqrt{|a|^4+|b|^2},\quad
z=\frac{a^2u+bv}{c},\quad
y_0=\frac{-\overline b\,u+\overline{a}^{2}v}{c},
\tag{25.5}
$$
并记
$$
H=\operatorname{span}\{z,w\},\quad
G=\operatorname{span}\{u,w\},\quad
L=\operatorname{span}\{u,v,w\}=H+G.
\tag{25.6}
$$
$`H,G`$ 均二维，$`H\cap G=\operatorname{span}\{w\}`$。第三轮定义
$$
V(z0)=s\eta_0,\quad V(u1)=r\eta_0,\quad
V(w0)=t\eta_0,\quad V(w1)=j\eta_0.
\tag{25.7}
$$
四个输入正交，故 $`s,r,t,j`$ 正交归一。第三轮两列为
$$
c m_0s+ab m_1r,\qquad a m_0t+b m_1j.
\tag{25.8}
$$
记
$$
S=\operatorname{span}\{s,t\},\quad
R=\operatorname{span}\{r,j\},\quad
L_3=S\oplus R.
\tag{25.9}
$$
四轮所需的零位和一位接收输入空间分别为
$$
H_3=\operatorname{span}\{cs+br,\ a^2t+bj\},\qquad G_3=S.
\tag{25.10}
$$
（25.10）的零位首向量略去非零公因子 $`a`$，不改变支撑。

**前四步强制初态与第二步一列平行。**

所有环境为 $`\eta_0`$ 的已指定接收输入，其零位和一位接收向量合并为
$$
A_0=\operatorname{span}(k,H),\qquad B_0=\operatorname{span}(k,G).
\tag{25.11}
$$
所有环境为 $`\eta_1`$ 的第二、四轮输入合并为
$$
A_1=\operatorname{span}(p,q,cs+br,a^2t+bj),\qquad
B_1=\operatorname{span}(p,s,t).
\tag{25.12}
$$
固定 $`V`$ 等距且两个环境正交，因此
$$
A_0\perp A_1,\qquad B_0\perp B_1.
\tag{25.13}
$$

等距映射在环境零支撑上的接收像空间为
$`\operatorname{span}(p,q,L_3)`$，故
$$
\dim\operatorname{span}(p,q,L_3)
=\dim A_0+\dim B_0.
\tag{25.14}
$$
另外，由（25.2）、（25.7）同为环境零以及不同输入位正交，
$$
p\perp R,\qquad q\perp S.
\tag{25.15}
$$

分四种实际的子空间位置，不作坐标上的额外假定：

1. 若 $`k\notin H`$ 且 $`k\notin G`$，则（25.14）右侧为六。
   因为 $`\dim L_3=4`$，$`p,q`$ 在商空间 $`K/L_3`$ 中线性独立。
   两个向量 $`cs+br,a^2t+bj`$ 在 $`L_3`$ 内线性独立，故
   $`\dim A_1=4`$。但 $`\dim A_0=3`$，与（25.13）及 $`D\le6`$ 矛盾。

2. 若 $`k\in G\setminus H`$，由 $`k1\in G\otimes1`$ 和（25.7）可得 $`q\in R`$。
   此时（25.14）为五，故 $`p\notin L_3`$。两个向量
   $`cs+br,a^2t+bj`$ 在 $`S`$ 上的投影分别为 $`cs,a^2t`$，线性独立；
   因此加上非零的 $`q\in R`$ 后仍线性独立。
   再加 $`p\notin L_3`$ 得 $`\dim A_1=4`$，而 $`\dim A_0=3`$，仍矛盾。

3. 若 $`k\in H\setminus G`$，同理有 $`p\in S`$，且由（25.14）得 $`q\notin L_3`$。
   这时 $`A_0=H`$、$`B_0=L`$，而 $`B_1=S`$，所以（25.13）给 $`S\perp L`$。
   特别地 $`s,t\perp H`$。又因 $`cs+br,a^2t+bj\in A_1\perp H`$，
   且 $`a,b\ne0`$，有 $`r,j\perp H`$，从而 $`L_3\subset H^\perp`$。
   同时 $`q\in A_1\subset H^\perp`$ 且 $`q\notin L_3`$，于是
   $`\dim H^\perp\ge5`$，即 $`D\ge7`$，矛盾。

4. 唯一剩余是 $`k\in H\cap G=\operatorname{span}\{w\}`$。

故 $`k\parallel w`$。两者都是单位向量，写 $`w=\zeta k`$，$`|\zeta|=1`$。
可在整个环境 $`\eta_1`$ 方向上把 $`V`$ 的输出乘 $`\overline\zeta`$，
即在 Stinespring 输出环境上施加固定相位酉。这不改变 CPTP 接收通道，也不改变（25.1）的环境射线。
在这份等价 Stinespring 表示中，第二轮的三个输出向量整体乘 $`\overline\zeta`$，于是新的 $`w=k`$。
此后重新按（25.5）—（25.8）定义 $`z,s,r,t,j`$ 即可。固定同一个 $`V`$ 的（25.2）、（25.7）随即给
$$
t=p,\qquad j=q.
\tag{25.16}
$$
这正是所用相位规范，未改变来源的 $`a,b`$，也未给运行门增加轮次控制。

**第五轮的二维夹角矛盾。**

此后取 $`D=6`$、$`k=w`$。由第二轮与第三轮输入环境正交，
$$
p\perp z,w,u,\qquad q\perp z,w.
\tag{25.17}
$$
因为 $`z,u`$ 张成 $`u,v`$ 平面，故 $`p\perp L`$。定义二维空间
$$
L_0=(L\oplus\operatorname{span}\{p\})^\perp.
\tag{25.18}
$$
于是 $`q\in\operatorname{span}\{y_0\}\oplus L_0`$，且 $`q`$ 为单位向量。

置
$$
d=\sqrt{c^2+|b|^2},\qquad f=\frac{cs+br}{d}.
\tag{25.19}
$$
因 $`s,r,p,q`$ 正交归一，$`f`$ 是单位向量且 $`f\perp p,q`$。
第四轮环境为一而第三轮零位输入空间为 $`H`$，给 $`f\perp z,w`$。
故 $`q,f`$ 是三维空间
$$
T=\operatorname{span}\{y_0\}\oplus L_0
\tag{25.20}
$$
中的一组正交单位向量。由第四轮一位输入与第三轮一位输入环境正交，还得到
$`s\perp u,w`$。

第四轮新出现的正交输入 $`f0,s1`$ 均与第二轮输入 $`p0,p1,q0`$ 正交。
因此可写
$$
V(f0)=A\eta_1,\qquad V(s1)=B\eta_1,
\tag{25.21}
$$
其中 $`A,B`$ 正交归一，且 $`A,B\perp u,v,w`$。第四轮两列为
$$
ad\,m_0A+cb\,m_1B,\qquad
m_0(a^2u+bw)+ab\,m_1v.
\tag{25.22}
$$

第五轮环境为零，必须与第二、四轮环境一的全部输入正交。
（25.22）第一列的一位输入向量是非零倍数的 $`A`$，所以
$$
A\perp p,s.
\tag{25.23}
$$
其零位输入向量为
$$
h_5=a^2d A+cb B,
\tag{25.24}
$$
故
$$
h_5\perp p,q,f.
\tag{25.25}
$$
由 $`A\perp p`$、$`cb\ne0`$ 及（25.25），有 $`B\perp p`$。结合
$`A,B\perp L`$，可知 $`A,B`$ 是二维 $`L_0`$ 的正交单位基。

令
$$
X=|a|^2,\qquad Y=|b|^2,\qquad
\kappa^2=X^2d^2+Yc^2,
\qquad \ell=h_5/\kappa.
\tag{25.26}
$$
$`\ell`$ 是 $`L_0`$ 中的单位向量。由（25.25），$`q,f`$ 张成
$`T\cap\ell^\perp`$。取 $`L_0\cap\ell^\perp`$ 的单位向量 $`e`$，则
$$
\operatorname{span}\{q,f\}=\operatorname{span}\{y_0,e\}.
\tag{25.27}
$$
所以存在 $`\alpha,\beta\in\mathbb C`$、$`\theta\in\mathbb R`$，使
$$
q=\alpha y_0+\beta e,\qquad
f=e^{i\theta}(-\overline\beta\,y_0+\overline\alpha\,e),
\qquad |\alpha|^2+|\beta|^2=1.
\tag{25.28}
$$
这里保留了伴随向量的全部相位 $`e^{i\theta}`$，没有假定复振幅为正实数。

因为 $`s\perp p,q,w`$，可在正交基 $`z,f,\ell`$ 中写
$$
s=\sigma z+\frac{c}{d}f+\tau\ell.
\tag{25.29}
$$
其中 $`f`$ 的系数是正实数 $`c/d`$，由（25.19）及 $`s\perp r`$ 得到。
另一方面，由（25.5）、（25.28）有
$$
\langle u,z\rangle=\frac{a^2}{c},\qquad
|\langle u,f\rangle|^2=\frac{Y|\beta|^2}{c^2}.
\tag{25.30}
$$
利用 $`s\perp u`$ 和 $`\|s\|=1`$，令 $`T_\beta=|\beta|^2`$，得到
$$
|\sigma|^2=\frac{Yc^2T_\beta}{X^2d^2},
\qquad
|\tau|^2=\frac{Y}{d^2}
\left(1-\frac{c^2T_\beta}{X^2}\right).
\tag{25.31}
$$
特别地 $`T_\beta\le X^2/c^2<1`$，所以 $`\alpha\ne0`$。
$`s`$ 在 $`L_0=\operatorname{span}\{e,\ell\}`$ 上的投影为
$$
s_{L_0}=\frac{c}{d}e^{i\theta}\overline\alpha\,e+\tau\ell,
\qquad
\|s_{L_0}\|^2=
\frac{d^2-c^4T_\beta/X^2}{d^2}>0.
\tag{25.32}
$$
由 $`A\in L_0`$、$`\|A\|=1`$、$`A\perp s`$，二维正交补的坐标给出
$$
|\langle\ell,A\rangle|^2
=\frac{c^2(1-T_\beta)}{d^2-c^4T_\beta/X^2}.
\tag{25.33}
$$
但（25.24）、（25.26）以及 $`A,B`$ 正交归一又给
$$
|\langle\ell,A\rangle|^2
=\frac{X^2d^2}{X^2d^2+Yc^2}.
\tag{25.34}
$$
比较（25.33）—（25.34），乘正分母，并用
$`c^2=X^2+Y`$、$`d^2=X^2+2Y`$，得到
$$
\begin{aligned}
0
&=c^2(1-T_\beta)(X^2d^2+Yc^2)
-X^2d^2(d^2-c^4T_\beta/X^2)\\
&=Y^3+Y^2c^2T_\beta.
\end{aligned}
\tag{25.35}
$$
右侧严格为正，因为 $`Y>0`$、$`T_\beta\ge0`$。矛盾。等价地，这一合同会强制
$`T_\beta=-Y/c^2<0`$。

故六维及以下无法以确定、正交、交替的环境序列01010服务五个精确终端。

**七维上界的构造。** 现在重新定义本段向量。取 $`K`$ 的正交单位基

$$
u,v,w,p,e,g,h,
\qquad k_0=w,
\qquad E=\mathbb C^2,
\qquad \eta_0=|0\rangle,\quad\eta_1=|1\rangle.
\tag{25.36}
$$

沿用正数 $`c=\sqrt{|a|^4+|b|^2}`$、$`d=\sqrt{c^2+|b|^2}`$，定义

$$
\begin{aligned}
z&=\frac{a^2u+bv}{c},
&y&=\frac{-\overline b\,u+\overline{a}^{2}v}{c},\\
q&=\frac{\overline b\,y+\overline{a}^{2}e}{c},
&f&=\frac{-a^2y+be}{c},\\
s&=\frac{-cv+be}{d},
&r&=\frac{df-cs}{b},\\
\kappa&=\sqrt{|a|^4d^2+|b|^2c^2},
&x&=\frac{a^2d\,g+cb\,h}{\kappa}.
\end{aligned}
\tag{25.37}
$$

这些分母均非零。前六个向量使用定理23.1的五维构造，其中原来的基向量 $`t`$ 在本段记为 $`p`$；$`g,h`$ 是新增的两个正交方向。直接核对该构造中已经证明的内积关系，有

$$
\begin{gathered}
z,y\text{ 正交归一},\qquad q,f\text{ 正交归一},
\qquad p,q,s,r\text{ 正交归一},\\
q,f\in\operatorname{span}\{y,e\},\qquad
s\perp u,w,p,\qquad
cs+br=df.
\end{gathered}
\tag{25.38}
$$

特别地，$`q,f\perp z,w,p`$；$`g,h,x`$ 均垂直于原来的五维空间。定义以下十一行部分酉表；输入的第二指标是最新发出位，输出的第二指标是新环境：

$$
\begin{array}{c|c@{\qquad}c|c}
\text{输入}&\text{输出}&\text{输入}&\text{输出}\\ \hline
w0&p0&p0&u1\\
w1&q0&p1&v1\\
z0&s0&q0&w1\\
u1&r0&f0&g1\\
x0&g0&s1&h1\\
g1&h0&&
\end{array}
\tag{25.39}
$$

左半表的输入是六个正交单位向量：零位上的 $`w,z,x`$ 互相正交，一位上的 $`w,u,g`$ 互相正交。右半表的输入是五个正交单位向量：零位上的 $`p,q,f`$ 互相正交，一位上的 $`p,s`$ 互相正交。两半表的零位子空间互相正交，由（25.38）和 $`x\perp\operatorname{span}\{u,v,w,p,e\}`$ 得到；一位子空间的交叉正交性则由 $`s,p\perp u,w,g`$ 得到。

输出的环境零块为正交单位族 $`p,q,s,r,g,h`$，环境一块为正交单位族 $`u,v,w,g,h`$。所以全表两侧各为十一元正交单位族。将两侧各补成十四维空间的正交单位基，便得到全域酉
$`U:K\otimes B\to K\otimes E`$。每轮接收使用同一个通道 $`\mathcal C(X)=\operatorname{Tr}_E UXU^*`$。

前两轮两列分别为 $`m_0p,m_1q`$ 和（25.4）；第三轮两列为
$`c m_0s+ab m_1r`$、$`a m_0p+b m_1q`$。由（25.39）及 $`cs+br=df`$，第四、五轮两列为

$$
\begin{aligned}
\Psi_4^0&=ad\,m_0g+cb\,m_1h,\\
\Psi_4^1&=m_0(a^2u+bw)+ab\,m_1v,\\
\Psi_5^0&=\kappa m_0g+abd\,m_1h,\\
\Psi_5^1&=a m_0(cs+bp)+b m_1(a^2r+bq).
\end{aligned}
\tag{25.40}
$$

例如第五轮第一列的零位输入为 $`a^2d\,g+cb\,h=\kappa x`$，一位输入为 $`abd\,g`$；第二列的零位输入为 $`a(cz+bw)`$，一位输入为 $`b(a^2u+bw)`$。表中六条环境零映射遂给出（25.40）。同一轮两列都具有相同的环境因子，因此任意相干初态及任意参考也依次产生与其余系统乘积的环境字01010。

固定一个终端 $`n\le5`$，在解码端制备已知环境字的前 $`n`$ 位，逆序施加相应的 $`U^*`$，即可恢复各个发出位与初始接收态。整个逆运算只作用于接收器及解码端新制备的系统：早先的接收门与后续源发射作用于不同系统，故可将全部接收门视为完整档案上的累计酉；恢复不需要访问活动记忆或参考。最终丢弃复原的固定接收初态，即给出所需全域本地解码通道。这样七维确实服务全部五个终端。

七维构造与下界合并，得到受限合同的精确值。它也属于定义12.1的一般接收类，从而给出（25.1a）的上界；其下界由四终端最小值五得到。一般五终端是否能进一步压到五维或六维，本定理不作判定。证明完毕。

## 追加锚（本行以下为增补区）

## 26. 一般五终端固定 CPTP 接收需要至少六维

来源为 $`m_0=a|0\rangle+b|1\rangle`$、$`m_1=|0\rangle`$，
$`ab\ne0`$、$`|a|^2+|b|^2=1`$。合同为定义12.1：独立纯接收初始化、同一个全域 CPTP 接收通道、所有持久系统计入接收器，且每个指定终端恢复全部参考—活动记忆—档案联合态。这里不预先限制新环境的纯度、维数、相互重叠或累计纠缠。

**定理 26.1（五终端的一般下界）。** 对任意上述已知非退化复振幅来源，

$$
6\le d_{\mathrm{CPTP},5}(a,b)\le7.
\tag{26.1}
$$

上界是第25节的七维构造。本节证明一般五维接收器不可能；四维及以下已由第23节排除。本节不判定一般六维是否可达。

**证明：纯终端与早期混合附加因子。**

反设 $`\dim K=5`$。固定一次接收通道的 Stinespring 等距映射
$`V:K\otimes B\to K\otimes E`$，写
$`V_0x=V(x\otimes|0\rangle)`$、$`V_1x=V(x\otimes|1\rangle)`$。
只需使用允许的 Bell 输入。终端档案相对 $`JM`$ 的 Schmidt 秩在第一步为二、第二步为三、第三步及以后为四。由第23节证明中的标准可逆编码分解，支撑秩 $`s`$ 与可逆附加因子的秩 $`r`$ 满足 $`sr\le5`$。
因此第二至第五步的实际 $`JMK`$ 联合态均为纯态；第一步的附加因子秩
$`r\in\{1,2\}`$，暂不假定为一。

对 $`n=2,3,4,5`$ 写纯联合态为

$$
\Psi_n=\frac1{\sqrt2}\sum_{i=0}^1|i\rangle_J
\bigl(|0\rangle_Mu_n^i+|1\rangle_Mv_n^i\bigr),
\qquad
H_n=\operatorname{span}\{u_n^0,u_n^1\},\quad
G_n=\operatorname{span}\{v_n^0,v_n^1\}.
\tag{26.2}
$$

这些空间满足

$$
\dim H_n=\dim G_n=2,
\qquad
\dim(H_2+G_2)=3,
\qquad
\dim(H_n+G_n)=4\quad(n=3,4,5).
\tag{26.3}
$$

例如第二步可选择正交单位向量 $`u,v,w\in K`$，使两列为

$$
\Psi_2^0=a m_0u+b m_1v,
\qquad \Psi_2^1=m_0w.
\tag{26.4}
$$

从而 $`H_2=\operatorname{span}\{a^2u+bv,w\}`$，
$`G_2=\operatorname{span}\{u,w\}`$。第三步的四维秩由第21节给出；往后 $`JM`$ 边缘仍正定，因为来源通道 $`\mathcal T`$ 满足 $`\mathcal T(I)>0`$。各活动记忆对角块在参考的两个计算基标签上都有正权，给出（26.3）中各二维空间。

第二至第五步纯度还给出第三、四、五轮各自的新环境纯向量
$`\eta_3,\eta_4,\eta_5`$。记这些轮次的实际输入支撑

$$
D_j=(H_{j-1}\otimes|0\rangle)\oplus
(G_{j-1}\otimes|1\rangle),\qquad j=3,4,5.
\tag{26.5}
$$

均有维数四，且 $`V(D_j)=(H_j+G_j)\otimes\eta_j`$。
存在二维空间 $`Q_j`$，满足

$$
V_0(H_{j-1})=G_j\otimes\eta_j,
\qquad
V_1(G_{j-1})=Q_j\otimes\eta_j,
\qquad
G_j\perp Q_j.
\tag{26.6}
$$

这里 $`G_j`$ 作为零位像空间，来自活动记忆 $`|1\rangle`$ 系数仅等于零位接收系数的非零倍数 $`b`$。还可写

$$
H_j\subset G_j\oplus Q_j,
\qquad \operatorname{rank}(P_{G_j}|_{H_j})=2.
\tag{26.7}
$$

后一秩来自 $`u_j^i=a A_ju_{j-1}^i+B_jv_{j-1}^i`$ 中
$`A_j:H_{j-1}\to G_j`$ 等距、$`a\ne0`$，且 $`B_jv_{j-1}^i\in Q_j\perp G_j`$。

**第二轮零位输入的关键结构。** 第一轮的标准可逆编码分解可写为

$$
V(k0)=\sum_{\alpha=1}^r\sqrt{\lambda_\alpha}\,p_\alpha e_\alpha,
\qquad
V(k1)=\sum_{\alpha=1}^r\sqrt{\lambda_\alpha}\,q_\alpha e_\alpha,
\tag{26.8}
$$

其中 $`\lambda_\alpha>0`$、$`\sum\lambda_\alpha=1`$，
$`p_1,q_1,\ldots,p_r,q_r`$ 是接收器中的正交单位向量，
$`e_\alpha`$ 是第一轮环境的正交单位向量。第二步联合 $`JMK`$ 为纯态，故累计环境 $`E_1E_2`$ 为独立的纯态。第一轮环境的边缘不变，所以该累计环境可写为
$`\sum_\alpha\sqrt{\lambda_\alpha}e_\alpha f_\alpha`$，其中
$`f_\alpha`$ 在第二轮环境中正交归一。

把两步全局纯向量按 $`e_\alpha`$、参考标签和线性独立的
$`m_0,m_1`$ 比较，得到

$$
V_0p_\alpha=u f_\alpha,
\qquad V_1p_\alpha=v f_\alpha,
\qquad V_0q_\alpha=w f_\alpha.
\tag{26.9}
$$

因此存在

$$
X=\operatorname{span}\{p_\alpha,q_\alpha:1\le\alpha\le r\},
\qquad F=\operatorname{span}\{f_\alpha:1\le\alpha\le r\},
\tag{26.10}
$$

满足

$$
\boxed{\dim X=2r\ge2,\qquad \dim F=r,\qquad V_0(X)=G_2\otimes F.}
\tag{26.11}
$$

这一步保留了早期混合附加因子，也允许 $`E_1,E_2`$ 彼此纠缠；没有把第二步纯度误用为第一步纯度。

**最后三轮环境只有两类。**

以下仅比较环境射线，写 $`\eta\parallel\xi`$ 表示同一射线。
若 $`\eta_i\not\parallel\eta_j`$，则 $`D_i\cap D_j=\{0\}`$；
若 $`\eta_i\perp\eta_j`$，则 $`D_i\perp D_j`$。两者均由固定
$`V`$ 等距及相应输出张量子空间直接得到。
若 $`\langle\eta_i,\eta_j\rangle\ne0`$，不同输入位的正交性给

$$
G_i\perp Q_j,\qquad Q_i\perp G_j.
\tag{26.12}
$$

如果 $`\langle\eta_3,\eta_4\rangle\ne0`$，则
$`Q_4\perp G_3+G_4`$。五维 $`K`$ 中 $`\dim Q_4=2`$，因此
$`\dim(G_3+G_4)\le3`$，所以 $`G_3\cap G_4\ne\{0\}`$。
该非零交空间在第四、五轮均作为一位输入，固定 $`V_1`$ 强制
$`\eta_4\parallel\eta_5`$。

余下设 $`\eta_3\perp\eta_4`$。若 $`\eta_5`$ 与两者均不同射线，且与两者内积均非零，则由（26.12）仍有
$`Q_5\perp G_3+G_4`$，继而同样得到
$`\eta_4\parallel\eta_5`$，矛盾。所以 $`\eta_5`$ 必正交于
$`\eta_3`$ 或 $`\eta_4`$ 中至少一个。
若正交于 $`\eta_3`$，则 $`D_3`$ 同时正交于 $`D_4,D_5`$，
而不同环境射线又给 $`D_4\cap D_5=\{0\}`$。于是三者总维数为十二，超过 $`\dim(K\otimes B)=10`$。正交于 $`\eta_4`$ 的情形相同。

因此只剩

$$
\boxed{\eta_4\parallel\eta_5\quad\text{或}\quad
\eta_3\parallel\eta_5\perp\eta_4.}
\tag{26.13}
$$

**排除末两轮同射线。**

先设 $`\eta_4\parallel\eta_5`$。固定 $`V`$ 把
$`D_4+D_5`$ 等距送入五维 $`K\otimes\eta_4`$，故

$$
\dim(H_3+H_4)+\dim(G_3+G_4)\le5.
\tag{26.14}
$$

各单项子空间均二维，因此 $`H_3=H_4`$ 或 $`G_3=G_4`$。

**先处理 $`\eta_3\not\parallel\eta_4`$。** 如果 $`G_3=G_4`$，
不同环境射线给 $`H_2\cap H_3=G_2\cap G_3=\{0\}`$。
由（26.6），$`V_0(H_2+H_3)`$ 包含于
$`G_3\otimes E`$，而（26.11）的 $`V_0(X)`$ 包含于
$`G_2\otimes E`$。两者交为零，故
$`X\cap(H_2+H_3)=\{0\}`$，与
$`\dim X\ge2`$、$`\dim(H_2+H_3)=4`$、$`\dim K=5`$ 矛盾。

所以仅需 $`H_3=H_4`$ 且 $`G_3\ne G_4`$；由（26.14），
$`\dim(G_3+G_4)=3`$。
若 $`\eta_3\perp\eta_4`$，则 $`D_3`$ 同时正交于
$`D_4,D_5`$，所以

$$
H_2\perp H_3,
\qquad G_2\perp G_3+G_4.
\tag{26.15}
$$

于是 $`H_2+H_3`$ 是四维，而 $`V_0(H_2+H_3)`$ 的接收器分量包含于
$`G_3+G_4\subset G_2^\perp`$，与 $`V_0(X)=G_2\otimes F`$ 正交。
故 $`X\perp H_2+H_3`$，又需至少六维，矛盾。

若 $`\eta_3`$ 与 $`\eta_4`$ 不同射线且内积非零，（26.12）使
$`Q_3,Q_4\subset(G_3+G_4)^\perp`$；两者二维，故都等于同一个二维空间 $`Q`$。由（26.7），共同空间 $`H=H_3=H_4`$ 满足

$$
H\subset (G_3\oplus Q)\cap(G_4\oplus Q)
=(G_3\cap G_4)\oplus Q.
\tag{26.16}
$$

但 $`G_3\cap G_4`$ 仅一维，故 $`P_{G_3}|_H`$ 的秩至多一，
与（26.7）的秩二矛盾。所有不同射线的情况均被排除。

**再处理三个环境全为同一射线。** 此时令
$`H_\Sigma=H_2+H_3+H_4`$、$`G_\Sigma=G_2+G_3+G_4`$，
固定接收等距性给

$$
\dim H_\Sigma+\dim G_\Sigma\le5.
\tag{26.17}
$$

各自至少二维，因此至少一个恰为二维。
若 $`\dim G_\Sigma=2`$，则 $`G_2=G_3=G_4`$。同一环境下
$`V_0(H_2)=G_3\otimes\eta_3`$ 与
$`V_0(H_3)=G_4\otimes\eta_3`$ 相等，等距性给
$`H_2=H_3`$。这与（26.3）的三维、四维支撑秩矛盾。

若 $`\dim H_\Sigma=2`$，则 $`H_2=H_3=H_4`$，同理得
$`G_3=G_4`$。还需排除这一对共同子空间；不能只沿用前面的不同射线条件。
置 $`x=|a|^2`$、$`y=|b|^2`$，定义

$$
t_1=x,\qquad t_2=x^2+y,\qquad
t_3=1-yt_2,\qquad t_4=1-yt_3.
\tag{26.18}
$$

来源的两列满足 $`\|u_n^0\|^2=t_n`$、
$`\|u_n^1\|^2=t_{n-1}`$（此处 $`n=2,3,4`$）。不同参考标签的档案支撑正交，故各组 $`u_n^0,u_n^1`$ 正交。
在 $`n=3,4`$ 时，由（26.7）的系数更新，$`P_{H_n}P_{G_n}|_{H_n}`$ 的两个特征值为

$$
x\frac{\|u_{n-1}^i\|^2}{\|u_n^i\|^2},\qquad i=0,1.
\tag{26.19}
$$

因此其第三、第四步行列式分别为

$$
\delta_3=\frac{x^3}{t_3},\qquad
\delta_4=\frac{x^2t_2}{t_4},
\qquad
\delta_4-\delta_3
=\frac{x^3y^2}{t_3t_4}>0.
\tag{26.20}
$$

最后等式用了 $`t_2+xy=1`$ 和 $`t_3-x=xy^2`$。
但 $`H_3=H_4`$、$`G_3=G_4`$ 会使两个投影压缩相同，矛盾。
至此三个环境同射线也被排除，故（26.13）的第一类完全不可能。

**交替尾强制完整的正交交替五字。**

剩余情况为 $`\eta_3\parallel\eta_5\perp\eta_4`$。固定单位代表
$`A,B`$，使第三至第五轮的环境射线为 $`A,B,A`$。
由 $`D_3\perp D_4`$ 得

$$
H_2\perp H_3,\qquad G_2\perp G_3.
\tag{26.21}
$$

（26.11）及 $`V_0(H_2)=G_3\otimes A`$ 的接收器分量正交，故
$`X\perp H_2`$。于是 $`2r=\dim X\le\dim H_2^\perp=3`$，
强制 $`r=1`$。
第一步实际联合态因而为纯态，第一轮新环境为纯向量 $`\eta_1`$；
第二轮新环境也为纯向量 $`\eta_2`$，且 $`F=\mathbb C\eta_2`$。

现在 $`X,H_3`$ 均为三维 $`H_2^\perp`$ 中的二维子空间，故
$`X\cap H_3\ne\{0\}`$。它们的 $`V_0`$ 像分别为
$`G_2\otimes\eta_2`$、$`G_4\otimes B`$，非零交强制

$$
\eta_2\parallel B.
\tag{26.22}
$$

令纯第一步两列为 $`m_0p,m_1q`$，其中 $`p,q`$ 正交归一，
初态为 $`k`$。于是 $`V_0k=p\otimes\eta_1`$、
$`V_1k=q\otimes\eta_1`$，且第一步系数空间为
$`H_1=\operatorname{span}\{p,q\}`$、$`G_1=\mathbb Cp`$。

合并第三、第五轮（环境 $`A`$）的输入，记

$$
H_A=H_2+H_4,\qquad G_A=G_2+G_4.
\tag{26.23}
$$

固定 $`V`$ 把这两个输入位的直和等距送入 $`K\otimes A`$，故
$`\dim H_A+\dim G_A\le5`$。若和为四，则两项各二维，意味着
$`H_2=H_4`$、$`G_2=G_4`$，与（26.3）第二、第四步总支撑维数不同矛盾。
所以

$$
\dim H_A+\dim G_A=5.
\tag{26.24}
$$

第二、第四轮（环境 $`B`$）的零位输入合并为
$`H_B=H_1+H_3`$。其像空间精确为

$$
V_0(H_B)=(G_2+G_4)\otimes B=G_A\otimes B,
\qquad \dim H_B=\dim G_A.
\tag{26.25}
$$

又因 $`A\perp B`$，有 $`H_A\perp H_B`$；结合（26.24），两者张成整个五维 $`K`$。因此固定 $`V_0`$ 的全域像包含于

$$
V_0(K)\subset K\otimes\operatorname{span}\{A,B\},
\qquad
(I_K\otimes\langle B|)V_0(K)\subset G_A.
\tag{26.26}
$$

第一步向量 $`p`$ 作为第二轮环境 $`B`$ 的一位输入，与第三、第五轮环境 $`A`$ 的全部一位输入正交，所以

$$
p\perp G_A.
\tag{26.27}
$$

而 $`V_0k=p\otimes\eta_1`$。由（26.26），$`\eta_1`$ 只能属于
$`\operatorname{span}\{A,B\}`$；若它的 $`B`$ 分量非零，同式又强制
$`p\in G_A`$，与（26.27）矛盾。故

$$
\eta_1\parallel A.
\tag{26.28}
$$

全部五轮的新环境现在均为确定独立纯态，射线序列为
$`A,B,A,B,A`$，且 $`A\perp B`$。第一步及后续步骤的环境向量对初始两个基态共用，故线性性同时给全部输入与参考这一环境合同。
第25节已经证明该额外合同至少需要七维，与假设 $`\dim K=5`$ 矛盾。

一般五维实现的所有环境分支均已排除。结合第23节对四维及以下的排除，以及第25节的一般七维上界，得到（26.1）。本证明允许最初的混合附加因子，并且仅在实际推导出 $`r=1`$ 后才使用前两轮新环境纯度；未将累计环境纯度误当成逐轮纯度。

## 追加锚（本行以下为增补区）

## 27. 六维接收中秩二附加态对后续环境的约束

本节只研究以下分支：已知非退化来源
$`m_0=a|0\rangle+b|1\rangle`$、$`m_1=|0\rangle`$，
$`ab\ne0`$、$`|a|^2+|b|^2=1`$；一个六维寄存器从独立纯态启动，使用同一个全域 CPTP 通道，精确服务前五个完整参考终端；第二终端可逆编码中的固定附加态秩为二。第一终端的附加态允许秩一、二或三。

按第23节的标准可逆编码结构，第二终端的三维档案支撑与二维附加因子已占满六维寄存器，可取

$$
K=Q\otimes\Gamma,
\qquad Q=\operatorname{span}\{u,v,w\},\quad
\dim\Gamma=2,
\tag{27.1}
$$

其中 $`u,v,w`$ 正交归一，第二终端的固定附加态在 $`\Gamma`$ 上正定。这里的张量分解只描述可逆编码，并不声称附加态纯，也不把它免费移出接收器。

记

$$
c=\sqrt{|a|^4+|b|^2},\qquad
z=\frac{a^2u+bv}{c},\qquad
H=\operatorname{span}\{z,w\},\quad
G=\operatorname{span}\{u,w\}.
\tag{27.2}
$$

有 $`H+G=Q`$、$`H\cap G=\mathbb Cw`$。第三轮接收前的实际输入支撑为

$$
L_3=(H\otimes\Gamma\otimes|0\rangle)
\oplus(G\otimes\Gamma\otimes|1\rangle),
\qquad \dim L_3=8.
\tag{27.3}
$$

后续三个终端的 Bell 档案秩均为四，而 $`6<2\cdot4`$，所以其可逆编码均为单个等距，接收后的 $`JMK`$ 联合态纯。固定每轮的 Stinespring 等距
$`V:K\otimes B\to K\otimes E`$。精确可逆编码的相邻纯化结构给一份等距 $`R:\Gamma\to E`$ 及 $`K`$ 中四个正交单位向量 $`s,r,t,j`$，使

$$
\begin{aligned}
V(z\otimes\xi\otimes|0\rangle)&=s\otimes R\xi,&
V(u\otimes\xi\otimes|1\rangle)&=r\otimes R\xi,\\
V(w\otimes\xi\otimes|0\rangle)&=t\otimes R\xi,&
V(w\otimes\xi\otimes|1\rangle)&=j\otimes R\xi
\end{aligned}
\quad(\xi\in\Gamma).
\tag{27.4}
$$

为说明这里未额外假定第三轮环境纯，取第二终端附加态与旧环境的一份 Schmidt 展开

$$
\chi_2=\sum_{j=1}^2\sqrt{\lambda_j}\,\xi_j\otimes e_j,
\qquad \lambda_j>0,
\tag{27.4a}
$$

其中两侧各自正交归一。第三终端的 $`JMK`$ 边缘纯，故与累计环境成乘积。旧环境边缘未被后续局部操作改变，所以第三终端的固定环境纯态必可写为
$`\sum_j\sqrt{\lambda_j}\,e_j\otimes R\xi_j`$，其中 $`R\xi_1,R\xi_2`$ 正交归一。对旧环境的 $`e_j`$ 系数以及四个线性独立的 $`JM`$ 系数分别比较，即得（27.4）在整个 $`\Gamma`$ 上成立；接收向量的正交归一性也由第三终端的等距编码给出。

因此第三轮把附加因子等距排入新环境，前三轮累计环境仍可是一份内部纠缠的固定纯态。这里没有把 $`\xi`$ 固定成单一向量，也没有把旧环境的某个分支当成可访问的控制。

置

$$
C_3=\operatorname{span}\{s,r,t,j\},\qquad
F=R\Gamma\subseteq E.
\tag{27.5}
$$

于是 $`\dim C_3=4`$、$`\dim F=2`$ 且

$$
V(L_3)=C_3\otimes F.
\tag{27.6}
$$

记第四、第五终端的四维接收器支撑为 $`C_4,C_5`$。因为第三至第五终端的联合态纯，第四、第五轮新环境分别为来源无关的单位纯向量 $`\eta_4,\eta_5`$。记相应四维接收输入支撑为 $`L_4,L_5`$，则

$$
V(L_4)=C_4\otimes\mathbb C\eta_4,
\qquad
V(L_5)=C_5\otimes\mathbb C\eta_5.
\tag{27.7}
$$

**命题 27.1（秩二附加态的后续环境限制）。** 在上述分支中，若精确服务全部五个终端，则

$$
\boxed{\eta_4,\eta_5\in F,
\qquad C_4\ne C_3,
\qquad C_5\ne C_3.}
\tag{27.8}
$$

因此第四、第五轮的纯环境都必须落在第三轮排出附加因子的同一个二维环境空间内。两者仍可非正交，也可共线；本结论没有排除这两种剩余情形。

证明。使用实际来源的记忆系数，写第三、第四终端的纯联合态为

$$
|\Psi_m\rangle
=\frac1{\sqrt2}\sum_{i=0}^1|i\rangle_J
\bigl(|0\rangle_Mx_m^i+|1\rangle_My_m^i\bigr),
\quad
H_m=\operatorname{span}\{x_m^0,x_m^1\},\quad
G_m=\operatorname{span}\{y_m^0,y_m^1\},
\qquad m=3,4.
\tag{27.9}
$$

已知来源的实际档案列及等距编码给

$$
\dim H_m=\dim G_m=2,
\qquad H_m+G_m=C_m,
\qquad \dim C_m=4.
\tag{27.10}
$$

下一次发射后的接收输入因此为

$$
L_{m+1}=(H_m\otimes|0\rangle)
\oplus(G_m\otimes|1\rangle).
\tag{27.11}
$$

这里同时使用参考与活动记忆的独立系数；未把活动记忆当成可访问的控制。

**先排除一种支撑回返。** 若 $`\eta\in F`$ 为单位向量，取唯一单位 $`\xi\in\Gamma`$ 使 $`R\xi=\eta`$。由（27.4），

$$
V^{-1}(C_3\otimes\mathbb C\eta)
=(H\otimes\mathbb C\xi\otimes|0\rangle)
\oplus(G\otimes\mathbb C\xi\otimes|1\rangle).
\tag{27.12}
$$

这里逆像在 $`V`$ 的像上理解；等距的单射性保证没有其它输入向量映到同一子空间。右边的零位、一位接收系数合起来只张成
$`(H+G)\otimes\mathbb C\xi=Q\otimes\mathbb C\xi`$，维数为三。
因此，当 $`n=4`$ 或 $`5`$ 时，不可能同时有

$$
C_n=C_3,\qquad \eta_n\in F:
\tag{27.13}
$$

否则（27.7）、（27.11）及（27.12）会使前一终端的接收支撑 $`C_{n-1}`$ 只有三维，与（27.10）矛盾。

**第四轮环境不能在 $`F`$ 外。** 反设 $`\eta_4\notin F`$。式（27.6）、（27.7）的两个像交为零，所以 $`L_3\cap L_4=0`$。两者维数和为 $`8+4=12=\dim(K\otimes B)`$，故同一个全域等距的整个像恰为

$$
\mathcal R:=V(K\otimes B)
=C_3\otimes F+C_4\otimes\mathbb C\eta_4.
\tag{27.14}
$$

若 $`C_4=C_3`$，则（27.14）使每次接收后的接收器支撑都包含于同一四维 $`C_3`$。但第二终端的接收器边缘支撑维数为
$`3\cdot2=6`$，矛盾。因此此时 $`C_4\ne C_3`$，且
$`\dim(C_3\cap C_4)\le3`$。

第五轮像 $`C_5\otimes\mathbb C\eta_5`$ 必须包含于（27.14）。在环境商空间 $`E/F`$ 上投影，分三种情形：

- 若 $`\eta_5\in F`$，则
  $`\mathcal R\cap(K\otimes F)=C_3\otimes F`$，从而 $`C_5\subseteq C_3`$。两者均四维，所以 $`C_5=C_3`$，违反（27.13）。
- 若 $`\eta_5\notin F`$，商空间投影强制
  $`\eta_5=c\eta_4+f`$，其中 $`c\ne0`$、$`f\in F`$，并且 $`C_5\subseteq C_4`$，故 $`C_5=C_4`$。
  若 $`f\ne0`$，减去 $`c(C_4\otimes\eta_4)`$ 又给
  $`C_4\otimes f\subseteq C_3\otimes F`$，从而 $`C_4=C_3`$，矛盾。
- 余下 $`f=0`$ 时，$`\eta_5\parallel\eta_4`$ 且 $`C_5=C_4`$。两轮像相同，固定等距单射性给 $`L_5=L_4`$。分别取新位零与一的系数空间，得到 $`H_4=H_3`$、$`G_4=G_3`$，故 $`C_4=C_3`$，仍矛盾。

所有情形均不成立，故 $`\eta_4\in F`$。结合（27.13）得到 $`C_4\ne C_3`$。

**第五轮环境也不能离开 $`F`$。** 现在（27.6）、（27.7）的交空间为

$$
V(L_3)\cap V(L_4)
=(C_3\cap C_4)\otimes\mathbb C\eta_4.
\tag{27.15}
$$

其维数至多三，所以

$$
\dim(L_3+L_4)
=8+4-\dim(C_3\cap C_4)\ge9.
\tag{27.16}
$$

同时 $`V(L_3+L_4)\subseteq K\otimes F`$。若 $`\eta_5\notin F`$，则
$`V(L_5)=C_5\otimes\mathbb C\eta_5`$ 与该像交零。因此
$`L_5\cap(L_3+L_4)=0`$，要求十二维输入空间中容纳至少 $`9+4=13`$ 维，矛盾。故 $`\eta_5\in F`$；再由（27.13）得 $`C_5\ne C_3`$。证明完毕。

本命题保留第二终端的秩二附加态及其与过去环境的纠缠，也没有限制第一终端附加态的秩。它把此分支的后续纯环境限定到同一二维空间，没有给出剩余交叉 Gram 方程的可行解或矛盾，因而不能据此排除一般五终端六维接收器。

## 追加锚（本行以下为增补区）

## 28. 相位历史的多尺度无终端接收

本节取定义1.1的等权来源 $`c_t=1`$，实际未知相位 $`\vartheta\in\Theta`$ 在一次运行中始终相同。固定非空候选集 $`\Theta\subseteq\mathbb T`$，不要求其闭或可测。接收合同采用定义13.1，但将全圆替换为这个固定候选集：预先给定同一列寄存器与门，在每个确定终端恢复参考、活动记忆及整个档案的联合态。门可依赖当前编号、已知候选集和精度，不能依赖未来终端、实际相位或输入；不增加适应性停止或解码后继续运行的要求。分离数 $`P(\Theta,r)`$ 沿用（22.2）的距离至少为 $`r`$ 的约定。

置

$$
p=\alpha^2,\qquad \mu=\frac p{1+p},\qquad
C_{\rm hist}=\frac14\left(\frac{1+p}{1-p}+\frac1{1-p^2}\right),
\qquad
c_{\rm hist}=\frac{1-2^{-1/2}}{\sqrt{2C_{\rm hist}}}.
\tag{28.1}
$$

**引理28.1（相位历史的共同移心比较）。** 给定任意已知相位历史 $`\boldsymbol\varphi=(\varphi_1,\ldots,\varphi_n)`$，以第 $`t`$ 步相位 $`\varphi_t`$ 定义虚拟累计等距 $`T_{\boldsymbol\varphi,n}`$。这些虚拟等距仅用于构造已知子空间，不改变实际来源或接收权限。选择实数

$$
\delta_t\equiv\vartheta-\varphi_t\pmod{2\pi},\qquad
|\delta_t|=d_{\mathbb T}(\vartheta,\varphi_t),
$$

并置

$$
H=\sum_{t=1}^n\delta_t(-p)^{t-1},\qquad
b=\mu\sum_{t=1}^n\delta_t+\left(\frac12-\mu\right)H.
\tag{28.2}
$$

则同一个标量相位 $`e^{ib}`$ 对整个来源输入空间满足

$$
\boxed{
(T_{\vartheta,n}-e^{ib}T_{\boldsymbol\varphi,n})^*
(T_{\vartheta,n}-e^{ib}T_{\boldsymbol\varphi,n})
\preceq C_{\rm hist}\left(\sum_{t=1}^n\delta_t^2\right)I_M.
}
\tag{28.3}
$$

证明。来源词的振幅平方给转移矩阵

$$
\begin{pmatrix}1-p&p\\1&0\end{pmatrix}
$$

的二态链 $`X_t`$，初位 $`X_1=i\in\{0,1\}`$。它满足

$$
\mathbb E[X_t\mid X_s]
=\mu+(X_s-\mu)(-p)^{t-s},\qquad
\operatorname{Cov}_i(X_s,X_t)
=(-p)^{t-s}\operatorname{Var}_i(X_s)\quad(s\le t).
\tag{28.4}
$$

取 $`Z=\sum_t\delta_tX_t`$。由 $`\operatorname{Var}_i(X_s)\le1/4`$、几何级数及 $`2|xy|\le x^2+y^2`$，

$$
\begin{aligned}
\operatorname{Var}_iZ
&\le\frac14\sum_{s,t=1}^n|\delta_s\delta_t|p^{|s-t|}\\
&\le\frac14\frac{1+p}{1-p}\sum_{t=1}^n\delta_t^2.
\end{aligned}
\tag{28.5}
$$

另一方面，$`\mathbb E_iZ-b=(i-\tfrac12)H`$，且 Cauchy–Schwarz 不等式给

$$
H^2\le\frac1{1-p^2}\sum_{t=1}^n\delta_t^2.
$$

因而两种初位均满足

$$
\mathbb E_i(Z-b)^2
=\operatorname{Var}_iZ+\frac14H^2
\le C_{\rm hist}\sum_{t=1}^n\delta_t^2.
\tag{28.6}
$$

逐词展开两个等距，使用 $`|e^{ix}-1|\le|x|`$ 及末端记忆向量的单位范数，得

$$
\|(T_{\vartheta,n}-e^{ib}T_{\boldsymbol\varphi,n})|i\rangle\|^2
\le\mathbb E_i(Z-b)^2.
$$

两个误差列分别位于首档案位为零和一的正交扇区，故无交叉项，（28.6）即给（28.3）。同一标量 $`b`$ 同时控制两个输入列，因此（28.3）可张量任意参考，包含输入的相干叠加。证明完毕。

**定理28.2（固定候选集的一套多尺度因果接收器）。** 给定 $`0<\epsilon<1`$ 及正的非增序列 $`(u_j)_{j\ge0}`$，满足

$$
\sum_{j=0}^{\infty}u_j^2\le1.
\tag{28.7}
$$

存在同一列寄存器和全域 CPTP 映射

$$
K_0=\mathbb C,\qquad
\mathcal C_n:\mathcal L(K_{n-1}\otimes B)\to\mathcal L(K_n),
\qquad
\mathcal D_n:\mathcal L(K_n)\to\mathcal L(H_n),
\tag{28.8}
$$

在每个确定终端、全部 $`\vartheta\in\Theta`$ 及任意初始参考输入上，完整联合恢复的半迹误差至多 $`\epsilon`$。对 $`n\ge1`$，令 $`k=\lfloor\log_2n\rfloor`$，则可取

$$
\boxed{
\dim K_n
\le4P(\Theta,c_{\rm hist}\epsilon u_k2^{-k/2})+1
\le4P\left(\Theta,\frac{c_{\rm hist}\epsilon u_k}{\sqrt n}\right)+1.
}
\tag{28.9}
$$

这里一维失败旗标计入 $`K_n`$。计数、已知门描述、纯空白和路由仍按定义1.2及13.1另行计量；（28.9）不声称这些资源的界。

证明分四步。

**嵌套网与相位祖先。** 置

$$
B_j=\{2^j,\ldots,2^{j+1}-1\},\qquad
\rho_j=c_{\rm hist}\epsilon u_j2^{-j/2}.
\tag{28.10}
$$

非增性给 $`\rho_{j+1}\le2^{-1/2}\rho_j`$。先选一个有限的、包含意义下极大的 $`\rho_0`$ 分离集 $`A_0\subseteq\Theta`$；递归地将 $`A_{j-1}`$ 扩张为极大的 $`\rho_j`$ 分离集 $`A_j`$。圆上的有限分离数保证扩张在有限步后停止。因此

$$
A_0\subseteq A_1\subseteq\cdots,\qquad
|A_j|\le P(\Theta,\rho_j),\qquad
\forall\vartheta\in\Theta\ \exists a\in A_j:
\ d_{\mathbb T}(\vartheta,a)<\rho_j.
\tag{28.11}
$$

最后一个严格网性质来自极大性：若某点与所有网点的距离均至少为 $`\rho_j`$，就还可将其加入。这个构造不使用 $`\Theta`$ 上的概率测度或紧性。

对每个 $`j\ge1`$ 固定父映射 $`\pi_j:A_j\to A_{j-1}`$，满足

$$
d_{\mathbb T}(a,\pi_j(a))<\rho_{j-1},
\qquad \pi_j(a)=a\quad(a\in A_{j-1}).
\tag{28.12}
$$

若 $`a\in A_k`$，以反复取父节点得到 $`a_j\in A_j`$，其中 $`a_k=a`$。在整个区块 $`B_j`$ 使用相位 $`a_j`$，再截到终端 $`n`$，得到一条已知相位历史 $`\boldsymbol\varphi^{,a,n}`$。全部网与父映射预先固定，与未来终端无关。

给定实际相位 $`\vartheta`$ 和当前 $`n`$，在误差证明中选 $`a_k\in A_k`$ 使 $`d_{\mathbb T}(\vartheta,a_k)<\rho_k`$。对其任意祖先，三角不等式及几何递减给

$$
d_{\mathbb T}(\vartheta,a_j)
<\rho_k+\sum_{\ell=j}^{k-1}\rho_\ell
\le\frac{\rho_j}{1-2^{-1/2}}.
\tag{28.13}
$$

每个 $`B_j`$ 的长度是 $`2^j`$，最后一块截断只会减少平方和。因此所选历史满足

$$
\begin{aligned}
\sum_{t=1}^n d_{\mathbb T}(\vartheta,\varphi_t^{,a_k,n})^2
&\le\frac1{(1-2^{-1/2})^2}\sum_{j=0}^k2^j\rho_j^2\\
&\le\frac{c_{\rm hist}^2\epsilon^2}{(1-2^{-1/2})^2}
=\frac{\epsilon^2}{2C_{\rm hist}}.
\end{aligned}
\tag{28.14}
$$

**历史支撑与因果闭合。** 对任意固定相位历史定义

$$
\chi_{ij}^{n,\boldsymbol\varphi}
=\sum_{w\in\mathcal W_n^{ij}}
A(w)e^{i\sum_{t=1}^n\varphi_tw_t}|w\rangle,
\qquad
S_n(\boldsymbol\varphi)
=\operatorname{span}\{\chi_{ij}^{n,\boldsymbol\varphi}:i,j=0,1\}.
\tag{28.15}
$$

逐词展开给

$$
T_{\boldsymbol\varphi,n}|i\rangle
=\sum_{j=0}^1\chi_{ij}^{n,\boldsymbol\varphi}\otimes m_j,
\qquad \dim S_n(\boldsymbol\varphi)\le4.
\tag{28.16}
$$

令 $`W_0=H_0=\mathbb C`$，并对 $`n\in B_k`$ 取普通线性和

$$
W_n=\sum_{a\in A_k}S_n(\boldsymbol\varphi^{,a,n})
\subseteq H_n.
\tag{28.17}
$$

这里不假设不同历史的支撑正交。立即有 $`\dim W_n\le4|A_k|`$。若 $`\boldsymbol\varphi'`$ 延长 $`\boldsymbol\varphi`$ 一步，则

$$
\chi_{ij}^{n+1,\boldsymbol\varphi'}
=e^{i\varphi'_{n+1}j}
\sum_{b=0}^1(m_b)_j\,
\chi_{ib}^{n,\boldsymbol\varphi}\otimes|j\rangle.
\tag{28.18}
$$

故延长历史的支撑包含于其前缀支撑张量 $`B`$。区块内部，每个叶节点只延长自己的历史；在 $`n+1=2^{k+1}`$ 的边界，新叶节点的长度 $`n`$ 前缀恰为其父节点在旧层的历史。因此对所有 $`n\ge0`$，

$$
W_{n+1}\subseteq W_n\otimes B.
\tag{28.19}
$$

**全域通道及累计成功分支。** 记 $`P_n`$ 为 $`W_n`$ 的正交投影、$`r_n=\dim W_n`$。对 $`n\ge1`$，取

$$
K_n=\mathbb C^{r_n}\oplus\mathbb C|\bot_n\rangle,
$$

并选等距编码 $`F_n:W_n\to\mathbb C^{r_n}\subseteq K_n`$。将 $`F_n`$ 在 $`W_n^\perp`$ 上以零延拓，故 $`F_n^*F_n=P_n`$、$`F_nF_n^*=I_{K_n}-|\bot_n\rangle\langle\bot_n|`$；取 $`F_0=P_0=I_{\mathbb C}`$。定义

$$
L_n=F_nP_n(F_{n-1}^*\otimes I_B),
\qquad
\mathcal C_n(X)=L_nXL_n^*
+\operatorname{Tr}[(I-L_n^*L_n)X]
|\bot_n\rangle\langle\bot_n|.
\tag{28.20}
$$

由（28.19），$`L_n^*L_n`$ 是输入空间上的正交投影，故（28.20）在整个输入载体上完全正且保迹。旧旗标被 $`F_{n-1}^*`$ 消去，因而其后始终留在失败块。各轮可采用立即丢弃的新环境实现此通道，并附加独立纯空白作为清除后的发出位；无其他持久接收系统。

这些通道仅作用于已发档案与接收器，和之后作用于活动记忆的来源等距可交换。将全部发射先展开后，连续成功 Kraus 算子的乘积由

$$
P_n(P_{n-1}\otimes I_B)=P_n
$$

逐步化为

$$
L_n(L_{n-1}\otimes I_B)\cdots
(L_1\otimes I_{B^{\otimes(n-1)}})=F_nP_n,
\tag{28.21}
$$

其中各因子的恒等延拓按其所剩档案位解释。因而某终端此前全部步骤成功的分支，恰为原档案在 $`W_n`$ 上的投影后编码；失败总质量恰是这个终端投影的漏出质量。

**完整联合误差。** 对给定的实际 $`\vartheta`$，由（28.14）选出的比较历史输出完全位于 $`W_n\otimes M`$。引理28.1遂给

$$
T_{\vartheta,n}^*[(I_{H_n}-P_n)\otimes I_M]T_{\vartheta,n}
\preceq\frac{\epsilon^2}{2}I_M.
\tag{28.22}
$$

固定任意档案态 $`\tau_n`$，定义全域终端解码

$$
\mathcal D_n(Y)=F_n^*YF_n
+\langle\bot_n|Y|\bot_n\rangle\tau_n.
\tag{28.23}
$$

对任意初始参考输入再取纯化，令纯联合目标为 $`|\Psi\rangle`$，并令 $`d_n`$ 为其在（28.22）投影补空间的质量；则 $`d_n\le\epsilon^2/2`$。由（28.21），解码后的成功分支是 $`P_n|\Psi\rangle\langle\Psi|P_n`$，其与目标的重叠为 $`(1-d_n)^2`$；这里省略了参考与活动记忆上的恒等算子。全部失败项均为正，所以总重叠至少为该值。纯目标的迹距离界给

$$
D(\widehat\Omega,|\Psi\rangle\langle\Psi|)
\le\sqrt{1-(1-d_n)^2}
\le\sqrt{2d_n}\le\epsilon.
\tag{28.24}
$$

丢弃额外纯化参考后此界仍成立。通道本身始终独立于实际相位和输入；为每个相位选叶节点只发生在证明中。最后，由 $`r_n\le4|A_k|`$ 及 $`2^k\le n`$，得到（28.9）。所有 $`W_n,F_n,\mathcal C_n,\mathcal D_n`$ 一次预定，因此同一门序列共同实现每个终端的结论。证明完毕。

**推论28.3（统一的缓变细化界）。** 任取 $`\eta>0`$，令

$$
u_j=\frac{C_\eta}{\sqrt{(j+2)[\log(j+2)]^{1+2\eta}}},
\qquad
C_\eta=\left(\sum_{j=0}^{\infty}
\frac1{(j+2)[\log(j+2)]^{1+2\eta}}\right)^{-1/2}.
\tag{28.25}
$$

该序列正、非增且平方和为一。令 $`k=\lfloor\log_2n\rfloor`$ 及

$$
L_{\epsilon,\eta}(n)=\frac1{c_{\rm hist}\epsilon u_k}\ge1.
\tag{28.26}
$$

则定理28.2的一套接收器满足

$$
\dim K_n\le
4P\left(\Theta,\frac{n^{-1/2}}{L_{\epsilon,\eta}(n)}\right)+1,
\qquad
L_{\epsilon,\eta}(n)
=\Theta_{\epsilon,\eta}\!\left(
\sqrt{\log n}\,(\log\log n)^{1/2+\eta}\right)
\quad(n\to\infty).
\tag{28.27}
$$

对 $`0<r\le1`$ 和 $`L\ge1`$，圆上的分离数满足

$$
P(\Theta,r/L)\le(\lfloor2L\rfloor+1)P(\Theta,r).
\tag{28.28}
$$

事实上，极大的 $`r`$ 分离集的半径 $`r`$ 弧覆盖 $`\Theta`$；把一份 $`r/L`$ 分离集的点逐一分配到这些弧，每条弧长 $`2r\le2<\pi`$，至多容纳 $`\lfloor2L\rfloor+1`$ 个这样的点。因此同一接收器还有统一于候选集的界

$$
\dim K_n
=O_{\epsilon,\eta}\!\left(
P(\Theta,n^{-1/2})\sqrt{\log n}\,
(\log\log n)^{1/2+\eta}+1\right).
\tag{28.29}
$$

式（28.25）—（28.28）适用于全部 $`n\ge1`$；（28.29）以 $`n\to\infty`$ 理解。

**推论28.4（几何候选集的最优对数阶）。** 对 $`0<q<1`$，置

$$
\Theta_q=\{0\}\cup\{q^j:j\ge0\}\subseteq[0,1]\subseteq\mathbb T.
\tag{28.30}
$$

固定 $`0<\epsilon<1`$，存在一套与未来终端无关的接收门序列，在全部确定终端满足完整联合误差界，且

$$
\dim K_n=\Theta_{q,\epsilon}(\log n)\qquad(n\to\infty).
\tag{28.31}
$$

每一套满足相同合同的门序列均须满足相应的 $`\Omega_{q,\epsilon}(\log n)`$ 下界。

证明。相邻候选间距为 $`(1-q)q^j`$。保留间距至少为 $`r`$ 的初段给 $`\Omega_q(1+\log(1/r))`$ 个分离点；反向将初段与位于长度 $`O_q(r)`$ 区间中的尾段分开，给

$$
P(\Theta_q,r)=\Theta_q(1+\log(1/r))\qquad(r\downarrow0).
\tag{28.32}
$$

在（28.25）中固定例如 $`\eta=1/2`$，则 $`\log L_{\epsilon,\eta}(n)=O_\epsilon(\log\log n)`$，（28.27）给 $`O_{q,\epsilon}(\log n)`$。任意因果门序列在某个确定终端构成一个合法单终端编码，定理22.2遂给反向下界。证明完毕。

**推论28.5（上下盒维指数与幂律累积）。** 定义

$$
\underline d=\liminf_{r\downarrow0}\frac{\log P(\Theta,r)}{\log(1/r)},
\qquad
\overline d=\limsup_{r\downarrow0}\frac{\log P(\Theta,r)}{\log(1/r)}.
\tag{28.33}
$$

不要求两者相等。取（28.25）的任意固定 $`\eta>0`$，定理28.2给出的同一套接收门序列满足

$$
\boxed{
\liminf_{n\to\infty}\frac{\log\dim K_n}{\log n}
=\frac{\underline d}{2},
\qquad
\limsup_{n\to\infty}\frac{\log\dim K_n}{\log n}
=\frac{\overline d}{2}.
}
\tag{28.34}
$$

每一套满足相同合同的门序列，其相应下极限至少为 $`\underline d/2`$，上极限至少为 $`\overline d/2`$。特别地，若盒维数 $`d=\underline d=\overline d`$ 存在，本构造的对数维数比收敛到 $`d/2`$；结论也包含维数为零和有限候选集。

证明。令

$$
r_n^{\rm coarse}=n^{-1/2},\qquad
r_n^{\rm fine}=\frac{n^{-1/2}}{L_{\epsilon,\eta}(n)}.
$$

两列尺度都严格递减到零，相邻项之比趋于一，且

$$
\frac{\log(1/r_n^{\rm coarse})}{\log n}=\frac12,
\qquad
\frac{\log(1/r_n^{\rm fine})}{\log n}\longrightarrow\frac12.
$$

对细尺度，在 dyadic 边界还须使用（28.25）的 $`u_{j+1}/u_j\to1`$；在区块内部只剩平方根因子。若 $`r_{n+1}\le r\le r_n`$，分离数的单调性给

$$
\frac{\log P(\Theta,r_n)}{\log(1/r_{n+1})}
\le\frac{\log P(\Theta,r)}{\log(1/r)}
\le\frac{\log P(\Theta,r_{n+1})}{\log(1/r_n)}
$$

（只取分母为正的充分大编号）。因此对上述任一列尺度，沿该序列取盒维数比的下、上极限，分别仍为全尺度的 $`\underline d,\overline d`$。定理22.2与（28.27）对本构造逐终端给

$$
\frac{1-\epsilon}{4C_*}P(\Theta,r_n^{\rm coarse})
\le\dim K_n
\le4P(\Theta,r_n^{\rm fine})+1\qquad(n\ge4).
$$

取对数、除以 $`\log n`$，两侧具有相同的下极限 $`\underline d/2`$ 与相同的上极限 $`\overline d/2`$，得到（28.34）。左侧对任意合法门序列仍成立，给出所述必要下界。证明完毕。

特别地，对（22.15）的 $`\Theta_\beta=\{0\}\cup\{j^{-\beta}:j\ge1\}`$，令 $`d=1/(\beta+1)`$。对任意 $`\eta>0`$，有一套接收门序列满足

$$
\dim K_n
=O_{\beta,\epsilon,\eta}\!\left(
 n^{d/2}(\log n)^{d/2}
 (\log\log n)^{d(1/2+\eta)}\right),
\tag{28.35}
$$

而每套合法门序列均须满足 $`\dim K_n=\Omega_{\beta,\epsilon}(n^{d/2})`$。因此指数相合，额外的对数因子仍未消去。

本节没有建立对所有候选集都成立的 $`O_\epsilon(P(\Theta,n^{-1/2}))`$ 无终端接收界。即使全圆，定理22.2与13.2目前仍分别给出 $`\Omega_\epsilon(\sqrt n)`$ 下界和另一套门序列的 $`O_\epsilon(\sqrt{n\log\log n})`$ 上界；定理13.4的限制只针对其规定的吸收截断接收器。两种上界各由一套完整门序列实现，不能仅因它们分别成立，就声称存在一套门序列在每个终端自动取得两者的较小值。

前缀支撑的相干逐步接收与等距延拓已有一般先例，[^phase_bcz] 联合纯目标的误差转换使用既有迹距离与保真度不等式。[^phase_fvg] 参数网与压缩指数的联系也有独立同分布规则族的先例。[^phase_metric_population] 本节的具体推导是（28.3）的共同移心历史比较、（28.11）—（28.19）的祖先历史支撑和（28.21）的累计投影关系；这些关系共同给出任意固定候选集的一套完整联合恢复门序列，不由上述文献的合同直接代入而得。

## 追加锚（本行以下为增补区）
