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
