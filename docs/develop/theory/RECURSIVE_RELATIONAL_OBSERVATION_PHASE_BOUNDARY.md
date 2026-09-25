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

## 29. 六维五终端接收的纯环境必要归约

本节沿用第26节的已知非退化来源
$`m_0=a|0\rangle+b|1\rangle`$、$`m_1=|0\rangle`$，其中
$`ab\ne0`$、$`|a|^2+|b|^2=1`$。假设一个六维接收器从独立纯态启动，使用同一个全域 CPTP 接收通道，精确服务前五个参考完整终端；所有持久系统计入接收器，活动记忆及参考均不可访问。

令 $`r_n`$ 为第 $`n`$ 终端可逆编码中固定附加态的秩。第23节的标准可逆编码结构及来源档案秩给

$$
r_1\in\{1,2,3\},\qquad r_2\in\{1,2\},\qquad
r_3=r_4=r_5=1.
\tag{29.1}
$$

本节先排除第二终端附加态秩二的整个分支，不限制第一终端原本允许的附加态秩；在余下的 $`r_2=1`$ 分支中，再排除 $`r_1=3`$ 和 $`r_1=2`$。因此任何六维候选都必须有 $`r_1=r_2=1`$：对任意纯的参考—记忆联合输入，五个终端的联合接收态全部为纯态，每轮新环境也为输入无关的纯态。这个归约保留环境之间任意的非正交 Gram 参数，尚未决定纯环境六维候选是否存在；第26节的总体界仍为 $`6\le d_{\mathrm{CPTP},5}(a,b)\le7`$。

固定每轮共用的 Stinespring 等距
$`V:K\otimes B\to K\otimes E`$，写
$`V_i x=V(x\otimes|i\rangle)`$。下文的环境等式若写作平行，均指同一射线，不暗含不同射线正交。

在联合态为纯态的终端，按活动记忆基写 Bell 输入的两列为

$$
\Psi_n^i=|0\rangle_Mx_n^i+|1\rangle_My_n^i,
\qquad
H_n=\operatorname{span}\{x_n^0,x_n^1\},\quad
G_n=\operatorname{span}\{y_n^0,y_n^1\},\quad
C_n=H_n+G_n.
$$

第三至第五终端均有 $`\dim H_n=\dim G_n=2`$、$`\dim C_n=4`$；在 $`r_2=1`$ 分支中，第二终端亦有两个二维系数空间，但 $`\dim C_2=3`$。这些是第26节已计算的来源支撑，下面只使用其维数和固定门递推。

**秩二第二终端的坐标。** 先取 $`r_2=2`$。沿用第27节的六维分解及记号：

$$
\begin{gathered}
K=Q\otimes\Gamma,\qquad
Q=\operatorname{span}\{u,v,w\},\qquad \dim\Gamma=2,\\
c=\sqrt{|a|^4+|b|^2},\qquad
z=\frac{a^2u+bv}{c},\qquad
H=\operatorname{span}\{z,w\},\quad
G=\operatorname{span}\{u,w\}.
\end{gathered}
\tag{29.2}
$$

其中 $`u,v,w`$ 正交归一，$`H+G=Q`$、$`H\cap G=\mathbb Cw`$。第二终端附加态在 $`\Gamma`$ 上正定。式（27.4）给等距 $`R:\Gamma\to E`$ 以及接收器中正交单位向量 $`s,r,t,j`$，使对全部 $`\xi\in\Gamma`$ 有

$$
\begin{aligned}
V_0(z\otimes\xi)&=s\otimes R\xi,&
V_1(u\otimes\xi)&=r\otimes R\xi,\\
V_0(w\otimes\xi)&=t\otimes R\xi,&
V_1(w\otimes\xi)&=j\otimes R\xi.
\end{aligned}
$$

记 $`F=R\Gamma`$。命题27.1已经给出第四、第五轮新环境
$`\eta_4,\eta_5\in F`$，并有 $`C_4,C_5\ne C_3`$。这里完整保留第二终端的混合附加态和前三轮累计环境的纠缠，不把（29.2）的某个纯切片当作实际第二终端态。

记
$$
A=\operatorname{span}\{s,t\}=G_3,\quad
B_3=\operatorname{span}\{r,j\},\quad Z=C_3^\perp,
$$
故 $`C_3=A\oplus B_3`$、$`\dim A=\dim B_3=\dim Z=2`$。
对第 $`n=4,5`$ 轮令 $`Q_n`$ 为一位输入的接收器像，即
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n.
$$
各 $`G_n,Q_n`$ 正交且二维，$`C_n=G_n\oplus Q_n`$。来源非退化还保证
$$
P_{G_n}H_n=G_n,\qquad P_{Q_n}H_n=Q_n.
\tag{29.3}
$$
这里两个投影限制在二维 $`H_n`$ 上均为同构。对 $`n=3`$，同样有
$`P_AH_3=A`$、$`P_{B_3}H_3=B_3`$。这些事实来自来源递推的两个非零系数，而非任意四维支撑的性质。

**命题29.1（排除秩二第二终端）。** 六维固定 CPTP 接收器若精确服务前五个完整参考终端，则必有 $`r_2=1`$。

反设 $`r_2=2`$。先证明此分支强制下列几何关系，再与来源系数递推比较导出矛盾。首先必须有
$$
\eta_4\parallel\eta_5.
\tag{29.4}
$$
吸收射线相位，写 $`\eta_4=\eta_5=\eta=R\xi`$，其中 $`\xi\in\Gamma`$ 单位。则还必须有
$$
G_4=G_3=A,\qquad H_3=H\otimes\mathbb C\xi,
\tag{29.5}
$$
以及
$$
\begin{aligned}
S_0&=(H\otimes\mathbb C\xi)+H_3+H_4,\\
S_1&=(G\otimes\mathbb C\xi)+A+G_4,
\end{aligned}
\qquad \dim S_0=\dim S_1=3.
\tag{29.6}
$$
令 $`\xi^\perp`$ 为任一单位正交补，则
$$
C_3=(Q\otimes\mathbb C\xi)\oplus
\mathbb C(v\otimes\xi^\perp).
\tag{29.7}
$$
在 （29.6） 中，$`H_4\ne H_3`$、$`G\otimes\mathbb C\xi\ne A`$。

**证明：排除两条不同射线。** 由第27节，$`\eta_4,\eta_5\in F`$。固定等距的两个位像正交，且
$`V_0(H\otimes\Gamma)=A\otimes F`$、
$`V_1(G\otimes\Gamma)=B_3\otimes F`$。所以
$$
G_4,G_5\subseteq B_3^\perp=A\oplus Z,\qquad
Q_4,Q_5\subseteq A^\perp=B_3\oplus Z.
\tag{29.8}
$$
反设 $`\eta_4,\eta_5`$ 是不同射线。固定 $`V_1`$ 在 $`A=G_3`$ 与 $`G_4`$ 上产生不同的纯环境，故 $`A\cap G_4=0`$。因此 $`P_ZG_4=Z`$。由 $`G_4\perp Q_4`$ 与 （29.8），可得 $`P_ZQ_4=0`$，从而 $`Q_4=B_3`$。取 $`R\xi_4=\eta_4`$。等距单射性和
$$
V_1A=B_3\otimes\eta_4=V_1(G\otimes\mathbb C\xi_4)
$$
给出 $`A=G\otimes\mathbb C\xi_4`$。

若 $`\eta_4\perp\eta_5`$，输入正交性给 $`A\perp G_4`$、$`H_3\perp H_4`$。结合 （29.8），$`G_4=Z`$。此时 $`H_3\subset A\oplus B_3`$，$`H_4\subset Z\oplus B_3`$，并且两者投影到 $`B_3=Q_4`$ 都是同构。故两空间不可能正交：取其任意基，交叉 Gram 矩阵是两个可逆 $`B_3`$ 系数矩阵的乘积，必可逆。矛盾。

若 $`\langle\eta_4,\eta_5\rangle\ne0`$，跨位输入正交性给 $`Q_5\perp G_4`$，而 （29.8） 给 $`Q_5\perp A`$。由于 $`A+G_4=B_3^\perp`$，得到 $`Q_5=B_3`$。取 $`R\xi_5=\eta_5`$，再次用单射性得 $`G_4=G\otimes\mathbb C\xi_5`$。两 $`\xi`$ 不共线，因此
$$
B_3\perp A+G_4=G\otimes\Gamma,
\qquad B_3=\mathbb Cv\otimes\Gamma.
\tag{29.9}
$$
另一方面，$`V_0H_3\subset K\otimes\eta_4`$，而
$`V_0(H\otimes\xi_4^\perp)=A\otimes R\xi_4^\perp`$，所以
$$
H_3\perp H\otimes\xi_4^\perp.
\tag{29.10}
$$
但 $`A=G\otimes\xi_4`$，而 $`P_{B_3}H_3=B_3`$ 由 （29.3） 成立。由 （29.9），$`H_3`$ 在 $`\xi_4^\perp`$ 切片的像为整个 $`\mathbb Cv`$；这不可能正交于 $`H`$，因为 $`\langle z,v\rangle\ne0`$。与 （29.10） 矛盾，证得 （29.4）。

**共同射线下的六维饱和。** 置 $`H_\xi=H\otimes\mathbb C\xi`$、$`G_\xi=G\otimes\mathbb C\xi`$。在 $`S_0,S_1`$ 上分别写
$$
V_0x=f(x)\otimes\eta,\qquad V_1y=g(y)\otimes\eta.
$$
$`f,g`$ 各为等距，其像正交，故 $`\dim S_0+\dim S_1\le6`$。它们满足
$$
\begin{array}{lll}
fH_\xi=A,& fH_3=G_4,&fH_4=G_5,\\
gG_\xi=B_3,&gA=Q_4,&gG_4=Q_5.
\end{array}
\tag{29.11}
$$
若 $`\dim S_1=2`$，则 $`G_\xi=A=G_4`$；（29.11） 的单射性又给 $`H_\xi=H_3`$，从而
$`\dim C_3=\dim(H_\xi+G_\xi)=3`$，矛盾。
若 $`\dim S_0=2`$，则 $`H_\xi=H_3=H_4`$，故 $`A=G_4`$、$`C_4=C_3`$、$`Q_4=B_3`$。再由 （29.11） 得 $`G_\xi=A`$，产生相同矛盾。因此两个维数都至少三，且总和至多六，即 （29.6）。

记
$$
U=fS_0=A+G_4+G_5,\qquad
W=gS_1=B_3+Q_4+Q_5.
\tag{29.12}
$$
则 $`K=U\oplus W`$，二者维数均为三。

**排除 $`G_4\ne A`$。** 反设二者不同。由它们都是 $`U`$ 中二维空间，$`A+G_4=U`$。它们又包含于三维 $`S_1`$，故 $`S_1=U`$。因此 $`G_\xi\subset U`$，且 $`g:U\to W`$ 为满等距。
由 （29.3），$`P_UH_3=A`$、$`P_UH_4=G_4`$，所以 $`P_US_0=U`$。三维空间 $`S_0`$ 必是某个线性映射 $`T:U\to W`$ 的图：
$$
S_0=\{u+Tu:u\in U\}.
\tag{29.13}
$$
又由 （29.3），$`T(A)=B_3`$、$`T(G_4)=Q_4`$，且 $`T|_A`$ 单射。因此
$$
\operatorname{im}T=B_3+Q_4=g(G_\xi+A).
\tag{29.14}
$$
然而 $`0\ne w\otimes\xi\in H_\xi\cap G_\xi\subset S_0\cap U`$，故 $`\ker T\ne0`$、$`\operatorname{rank}T\le2`$。式 （29.14） 迫使两个二维空间 $`G_\xi,A`$ 相等。于是 $`w\otimes\xi\in A\cap\ker T`$，与 $`T|_A`$ 单射矛盾。证得 $`G_4=A`$；（29.11） 随即给 $`H_3=H_\xi`$，即 （29.5）。

**第三终端支撑的形状。** 由 （29.5）、（29.6），
$`S_1=G_\xi+A`$ 为三维，所以 $`\dim(G_\xi\cap A)=1`$。而
$`H_\xi\cap A=H_3\cap G_3=0`$，且
$`H_\xi\cap G_\xi=\mathbb C(w\otimes\xi)`$。这两条不同的交线张成 $`G_\xi`$，故
$$
Q\otimes\mathbb C\xi=H_\xi+G_\xi
\subseteq H_\xi+A=C_3.
\tag{29.15}
$$
由 $`V_1A\subset K\otimes\eta`$，输入 $`A`$ 必正交于 $`G\otimes\xi^\perp`$。故
$`A\subset(Q\otimes\xi)\oplus\mathbb C(v\otimes\xi^\perp)`$。结合 （29.15） 和 $`\dim C_3=4`$，得到 （29.7）。

**共同射线下的系数条件。** 余下的（29.5）情形还须同时满足：
$$
\begin{gathered}
H_3=H_\xi,\quad G_3=G_4=A,\quad
\dim(H_\xi+H_4)=\dim(G_\xi+A)=3,\\
f:H_\xi+H_4\overset{\cong}{\longrightarrow}A+G_5,
\quad g:G_\xi+A\overset{\cong}{\longrightarrow}B_3+Q_4,\\
(A+G_5)\perp(B_3+Q_4),\quad Q_5=Q_4,
\end{gathered}
\tag{29.16}
$$
以下 $`n=2`$ 的系数是固定附加因子向量 $`\xi`$ 的纯切片系数，并非把实际混合第二终端态改称纯态。由第27节的式 (27.4)，此切片经第三轮产生同一个实际纯第三终端。因此这些切片与后续实际纯终端必须满足来源系数递推
$$
x_{n+1}^i=a f(x_n^i)+g(y_n^i),\qquad
y_{n+1}^i=b f(x_n^i),\qquad n=2,3,4,
\tag{29.17}
$$
其中 $`x_2^0=c(z\otimes\xi)`$、$`x_2^1=a(w\otimes\xi)`$、
$`y_2^0=ab(u\otimes\xi)`$、$`y_2^1=b(w\otimes\xi)`$。
前两轮还必须确实产生第27节假设的满秩二维附加态。下面只用已经得到的后续必要条件导出矛盾，因此无需再对前两轮的实现附加限制。

**排除共同射线下的剩余系数。** 沿用（29.12）的正交分解 $`K=U\oplus W`$，由（29.3）有 $`P_UH_3=A`$，且此投影在 $`H_3`$ 上单射，因此 $`H_3\cap W=0`$。对 $`q\in Q`$ 简记 $`q_\xi=q\otimes\xi`$。由（27.4）及共同环境定义，

$$
fz_\xi=s,\qquad fw_\xi=t,\qquad
gu_\xi=r,\qquad gw_\xi=j.
$$

**系数矩阵的一个秩一差。** 写 $`X_n=[x_n^0\ x_n^1]`$、$`Y_n=[y_n^0\ y_n^1]`$。第二步使用固定 $`\xi`$ 的纯切片，非实际混合第二终端的纯态假设；第27节式 (27.4) 保证该切片生成同一实际纯第三终端。因此
$$
X_2=[c z_\xi\quad a w_\xi],\qquad
Y_2=[ab u_\xi\quad b w_\xi],
\quad c=\sqrt{|a|^4+|b|^2},
\tag{29.18}
$$
并且对 $`n=2,3,4`$ 有
$$
X_{n+1}=a fX_n+gY_n,\qquad Y_{n+1}=b fX_n.
\tag{29.19}
$$
由 $`H_3=H_\xi=\operatorname{ran}X_2`$，存在可逆二阶矩阵 $`T`$ 使
$$
X_3=X_2T,\qquad Y_4=Y_3T.
\tag{29.20}
$$
置 $`M=Y_3-Y_2T`$。来源递推给
$$
X_4-X_3T=gM.
\tag{29.21}
$$
左侧两组列合起来张成三维 $`H_3+H_4`$，而 $`\operatorname{ran}(gM)\subset W`$、$`H_3\cap W=0`$。故
$$
\operatorname{rank}M=1.
\tag{29.22}
$$

**零行列式强制列交换。** 设
$$
x=|a|^2,\quad y=|b|^2,\quad
d=c^2=x^2+y,\quad \tau=x(d+y),
$$
所以 $`x,y>0`$、$`x+y=1`$，且 $`d^2-x\tau=y^2`$。直接从来源的正交输出列得到
$$
D_0=\begin{pmatrix}x&0\\0&1\end{pmatrix},\quad
D_2=X_2^*X_2=\begin{pmatrix}d&0\\0&x\end{pmatrix},\quad
D_3=X_3^*X_3=\begin{pmatrix}\tau&0\\0&d\end{pmatrix},
\tag{29.23}
$$
及
$$
X_2^*Y_2=\bar a b D_0,\quad
X_3^*Y_3=\bar a b D_2,\quad
T^*D_2T=D_3.
\tag{29.24}
$$
取任意非零 $`h\in\ker M`$。由 $`Y_3h=Y_2Th`$，式 （29.24） 给
$$
(D_2-T^*D_0T)h=0.
\tag{29.25}
$$
令 $`L=D_2^{1/2}TD_3^{-1/2}`$，则 $`L`$ 酉。置 $`p=|L_{00}|^2`$，二阶酉性还给 $`|L_{11}|^2=p`$、$`|L_{01}|^2=|L_{10}|^2=1-p`$。对 $`N=T^*D_0T`$，有
$$
N_{00}=\tau\left(p\frac{x}{d}+(1-p)\frac1x\right),\quad
N_{11}=(1-p)x+p\frac d x,\quad \det N=\tau.
\tag{29.26}
$$
因此
$$
\begin{aligned}
\det(D_2-T^*D_0T)
&=dx+\tau-xN_{00}-dN_{11}\\
&=p\left(xd+\frac{\tau y}{d}-\frac{d^2}{x}\right)
=-p\frac{y^3}{xd}.
\end{aligned}
\tag{29.27}
$$
式 （29.25） 使左侧为零，故 $`p=0`$。于是存在单位复数 $`\omega,\nu`$ 满足
$$
T=\begin{pmatrix}
0&\omega\\
\nu\sqrt{\tau/x}&0
\end{pmatrix},\qquad
D_2-T^*D_0T=\begin{pmatrix}-y&0\\0&0\end{pmatrix}.
\tag{29.28}
$$
由 （29.22）、（29.25），$`\ker M`$ 恰是第二坐标轴，故
$$
Y_3^1=\omega Y_2^0.
\tag{29.29}
$$

**列交换与下一轮纯环境不相容。** 由（27.4）、（29.18）—（29.19），
$$
Y_3^1=ab t,\qquad Y_2^0=ab u_\xi,
$$
所以 $`t=\omega u_\xi`$。又由
$$
X_3^1=a^2t+bj=\omega X_2^0
=\omega(a^2u_\xi+bv_\xi),
$$
得到 $`j=\omega v_\xi`$。四个向量 $`s,r,t,j`$ 正交归一；结合 （29.7），$`s,r`$ 必为
$`\operatorname{span}\{w_\xi,v\otimes\xi^\perp\}`$ 的一组正交基。
另一方面，（29.28） 给
$$
X_3^0=\kappa w_\xi,
\qquad \kappa=\nu a\sqrt{\tau/x}\ne0.
\tag{29.30}
$$
写
$$
s=\alpha w_\xi+\beta(v\otimes\xi^\perp).
\tag{29.31}
$$
必须有 $`\beta\ne0`$：否则 $`s`$ 沿 $`w_\xi`$，$`r`$ 沿 $`v\otimes\xi^\perp`$，而
$`X_3^0=ac s+ab r`$ 含非零的后一个分量，违反 （29.30）。

此时 $`S_1=G_\xi+A=\operatorname{span}\{u_\xi,w_\xi,v\otimes\xi^\perp\}`$。所以
$$
e=g(v\otimes\xi^\perp)
\tag{29.32}
$$
是单位向量。它正交于 $`gG_\xi=B_3`$，也正交于 $`fH_\xi=A`$，故由 （29.7）
$$
e\in C_3^\perp=G\otimes\mathbb C\xi^\perp.
\tag{29.33}
$$
由 （29.11）、（29.19）、（29.30）、（29.31），
$$
X_4^0=a\kappa t+bc\,g s
=a\kappa t+bc\alpha j+bc\beta e.
\tag{29.34}
$$
前两项位于 $`Q\otimes\xi`$，最后一项为 $`e`$ 的非零倍数。

但是 $`V_0H_4\subset K\otimes\eta`$，而第27节的全附加因子等式给
$$
V_0(H\otimes\xi^\perp)=A\otimes R\xi^\perp,
\qquad R\xi^\perp\perp\eta.
$$
故等距性要求 $`H_4\perp H\otimes\xi^\perp`$。将 （29.34） 代入，得到
$`e\perp H\otimes\xi^\perp`$。这与 （29.33） 不相容：$`P_H|_G`$ 单射，因为
$`G=\operatorname{span}\{u,w\}`$、$`H=\operatorname{span}\{z,w\}`$，且
$`\langle z,u\rangle=\bar a^2/c\ne0`$。因此 $`e=0`$，违反其单位范数。矛盾，证明完毕。

**纯第二终端的早期支撑。** 现在取 $`r_2=1`$。第二至第五终端的参考—活动记忆—接收器联合态均为纯态，第三至第五轮的新环境分别记为 $`\eta_3,\eta_4,\eta_5`$。

沿用第26节的 $`H_n,G_n`$，置 $`C_n=H_n+G_n`$、$`U=G_2`$。有

$$
\dim H_n=\dim G_n=2,\qquad
\dim C_2=3,\qquad \dim C_3=\dim C_4=\dim C_5=4.
\tag{29.35}
$$

写 $`V_i x=V(x\otimes|i\rangle)`$。对 $`n=3,4,5`$，存在二维 $`Q_n`$，使

$$
V_0(H_{n-1})=G_n\otimes\eta_n,\qquad
V_1(G_{n-1})=Q_n\otimes\eta_n,\qquad
G_n\perp Q_n.
\tag{29.36}
$$

第一终端附加态秩 $`r_1\in\{1,2,3\}`$。第26节的两轮系数比较适用于当前 $`r_2=1`$ 合同，给正交单位向量 $`p_\alpha,q_\alpha`$、$`u,v,w`$ 与正交单位环境向量 $`f_\alpha`$，使

$$
V_0p_\alpha=u\otimes f_\alpha,\qquad
V_1p_\alpha=v\otimes f_\alpha,\qquad
V_0q_\alpha=w\otimes f_\alpha.
\tag{29.37}
$$

因此，令

$$
X=\operatorname{span}\{p_\alpha,q_\alpha:1\le\alpha\le r_1\},
\quad F=\operatorname{span}\{f_\alpha:1\le\alpha\le r_1\},
$$

便有

$$
U=\operatorname{span}\{u,w\},\qquad
\dim X=2r_1,\quad\dim F=r_1,\qquad V_0(X)=U\otimes F.
\tag{29.38}
$$

第一轮的混合附加因子仍保留；$`F`$ 是第二轮环境子空间，不预先等同于第一轮环境支撑。

**命题29.2（纯第二终端强制纯第一终端）。** 在 $`r_2=1`$ 分支中，必有 $`r_1=1`$。证明先排除 $`r_1=3`$，再在 $`r_1=2`$ 时导出二维环境限制及三个射线分支，最后将它们逐一排除。

**证明：排除第一终端秩三。**

若 $`r_1=3`$，则 $`X=K`$，从而 $`V_0(K)=U\otimes F`$。由（29.36），$`G_3,G_4\subseteq U`$，两者均二维，所以 $`G_3=G_4=U`$。固定 $`V_1`$ 对相同输入子空间 $`G_2=G_3=U`$ 的像相同，强制 $`\eta_3\parallel\eta_4`$。于是

$$
V_0(H_2)=U\otimes\eta_3
=U\otimes\eta_4=V_0(H_3).
$$

$`V_0`$ 单射给 $`H_2=H_3`$，继而 $`C_3=H_3+G_3=H_2+U=C_2`$，违反（29.35）。此排除只需服务至第四终端。

**第一终端秩二：后续环境的二维限制。**

以下取 $`r_1=2`$，故 $`\dim X=4`$、$`\dim F=2`$。令 $`\mathcal R_0=V_0(K)`$，维数为六。

反设至少一个 $`\eta_t\notin F`$（$`t\in\{3,4,5\}`$）。由（29.36）、（29.38），两个相交为零的空间 $`U\otimes F`$ 与 $`G_t\otimes\eta_t`$ 的维数和为六，故

$$
\mathcal R_0=U\otimes F+G_t\otimes\eta_t.
\tag{29.39}
$$

若 $`G_t=U`$，则 $`\mathcal R_0`$ 的全部接收器分量均在 $`U`$ 中，因而 $`G_3=G_4=G_5=U`$。固定 $`V_1`$ 再使 $`\eta_3\parallel\eta_4`$，固定 $`V_0`$ 使 $`H_2=H_3`$，仍与（29.35）矛盾。因此只需考虑 $`Z:=G_t\ne U`$。

任意二维矩形子空间 $`G\otimes\eta\subseteq\mathcal R_0`$ 只有下列两种形式：

$$
\mathrm A:\quad G=U,\ \eta\in F;
\qquad
\mathrm B:\quad G=Z,\ \eta\parallel\eta_t.
\tag{29.40}
$$

证明：若 $`\eta\in F`$，由 $`\mathcal R_0\cap(K\otimes F)=U\otimes F`$ 得 $`G=U`$。若 $`\eta\notin F`$，投影环境到 $`E/F`$ 后，（29.39）强制 $`G=Z`$、$`\eta=c\eta_t+f`$，其中 $`c\ne0`$、$`f\in F`$。减去 $`cZ\otimes\eta_t`$ 得 $`Z\otimes f\subseteq U\otimes F`$；如果 $`f\ne0`$，则 $`Z\subseteq U`$，与 $`Z\ne U`$ 矛盾。因此 $`f=0`$，证明（29.40）。这里的两项是普通子空间之和，不假设 $`Z\perp U`$ 或 $`\eta_t\perp F`$。

对第三至第五轮的 $`(G_n,\eta_n)`$ 应用（29.40）。

- 若第三轮为A，则 $`G_3=U`$。固定 $`V_1`$ 在 $`G_2=G_3`$ 上给 $`\eta_4\parallel\eta_3\in F`$，故第四轮仍为A，$`G_4=U`$。于是 $`H_2=H_3`$，违反第二、第三终端的支撑秩差。
- 若第三、第四轮均为B，则 $`G_3=G_4=Z`$。固定 $`V_1`$ 强制 $`\eta_5\parallel\eta_4\parallel\eta_t`$，第五轮也为B。因此 $`G_3=G_4=G_5=Z`$，由固定 $`V_0`$ 又有 $`H_2=H_3=H_4`$。这使 $`(H_3,G_3)`$ 与 $`(H_4,G_4)`$ 为同一对空间，违反式（26.20）的主角度行列式严格变化：若 $`x=|a|^2`$、$`y=|b|^2`$，则 $`\delta_4-\delta_3=x^3y^2/(t_3t_4)>0`$。
- 唯一余下为第三轮B、第四轮A。因 $`G_4=U=G_2`$，固定 $`V_1`$ 给 $`\eta_5\parallel\eta_3`$，所以第五轮B。固定 $`V_0`$ 对第三、第五轮的相同像给 $`H_2=H_4`$；于是 $`C_4=H_4+G_4=H_2+U=C_2`$，违反（29.35）。

所有分支均矛盾，因此

$$
\boxed{\eta_3,\eta_4,\eta_5\in F.}
\tag{29.41}
$$

这不是提前假设独立或纯的前两轮环境；第一轮与第二轮环境仍可以纠缠。

**第一终端秩二：三种尾环境射线排列。**

令 $`\pi:K\to K/U`$ 为线性商映射。因为 $`(\pi\otimes I_E)V_0`$ 在四维 $`X`$ 上为零，其像

$$
\mathcal Z:=(\pi\otimes I_E)V_0(K)
$$

至多二维。对全部 $`n=3,4,5`$ 有

$$
\pi(G_n)\otimes\eta_n\subseteq\mathcal Z,
\qquad
\dim\pi(G_n)=2-\dim(G_n\cap U).
\tag{29.42}
$$

不同环境射线产生的这类张量子空间相交为零；若其环境向量线性无关，维数可相加。

**分支一：$`\eta_3\not\parallel\eta_4`$。** 若 $`x\in U\cap G_3`$，固定 $`V_1x`$ 同时属于 $`Q_3\otimes\eta_3`$ 和 $`Q_4\otimes\eta_4`$，只能为零，所以 $`U\cap G_3=0`$，$`\dim\pi(G_3)=2`$。由（29.41），两条不同射线在 $`F`$ 中线性无关；（29.42）的二维上限强制 $`\pi(G_4)=0`$，即 $`G_4=U`$。再在 $`V_1(G_4)=V_1(G_2)`$ 上比较第五、第三轮，得到 $`\eta_5\parallel\eta_3`$。因此

$$
\boxed{
\eta_3\parallel\eta_5\not\parallel\eta_4,
\qquad G_4=U,\qquad G_3\cap U=0.
}
\tag{29.43}
$$

并有更精确的零位全像

$$
\mathcal R_0=U\otimes F+G_3\otimes\eta_3.
\tag{29.44}
$$

（29.44）中两项相交为零，维数和为六；不同于（29.39），此时 $`\eta_3\in F`$，没有环境外方向。又因为 $`\eta_5\parallel\eta_3`$，可从（29.44）取该环境方向的截面，得到

$$
G_5\subseteq U+G_3.
\tag{29.45}
$$

如果定义 $`X_\eta:=V_0^{-1}(U\otimes\eta)`$（非零 $`\eta\in F`$），它是 $`X`$ 内的二维空间，则本分支还有

$$
H_3=X_{\eta_4},\qquad H_2\cap X=0,\qquad H_4\cap U=0.
\tag{29.46}
$$

最后一式是 $`G_4=U`$ 与 $`\dim C_4=4`$ 的直接要求。

**分支二：$`\eta_3\parallel\eta_4`$ 而 $`\eta_5\not\parallel\eta_3`$。** 固定 $`V_1`$ 把 $`U+G_3`$ 送入 $`(Q_3+Q_4)\otimes\eta_3`$，把 $`G_4`$ 送入 $`Q_5\otimes\eta_5`$。两条环境射线不同，单射性给

$$
G_4\cap(U+G_3)=0.
\tag{29.47}
$$

因此

$$
\dim\pi(G_3+G_4)=\dim\pi(G_3)+2.
$$

（29.42）同时包含 $`\pi(G_3+G_4)\otimes\eta_3`$ 与 $`\pi(G_5)\otimes\eta_5`$，所以二维上限强制 $`\pi(G_3)=\pi(G_5)=0`$。得到

$$
\boxed{
\eta_3\parallel\eta_4\not\parallel\eta_5,
\qquad G_3=G_5=U,\qquad G_4\cap U=0.
}
\tag{29.48}
$$

相应有

$$
\mathcal R_0=U\otimes F+G_4\otimes\eta_3,
\qquad
H_2=X_{\eta_3},\quad H_4=X_{\eta_5},\quad
H_2+H_4=X,\quad H_3\cap X=0.
\tag{29.49}
$$

因为 $`\eta_3,\eta_5`$ 为 $`F`$ 的一组基，两个 $`X_\eta`$ 的和确实是整个 $`X`$。

**分支三：三个环境同射线。** 即

$$
\eta_3\parallel\eta_4\parallel\eta_5.
\tag{29.50}
$$

第26节同射线分析中与五维上限无关的部分仍可用：若

$$
H_\Sigma=H_2+H_3+H_4,\qquad
G_\Sigma=G_2+G_3+G_4,
$$

则固定 $`V`$ 在同一环境方向上等距给 $`\dim H_\Sigma+\dim G_\Sigma\le6`$。任何一项等于二均不可能：$`\dim G_\Sigma=2`$ 会给 $`G_2=G_3=G_4`$ 与 $`H_2=H_3`$，违反第二、第三终端秩差；$`\dim H_\Sigma=2`$ 会给 $`H_2=H_3=H_4`$、$`G_3=G_4`$，违反（26.20）。故必要条件是

$$
\boxed{\dim H_\Sigma=\dim G_\Sigma=3.}
\tag{29.51}
$$

（29.43）、（29.48）、（29.50）穷尽所有射线排列；特别排除了三条互异射线及 $`\eta_4\parallel\eta_5\not\parallel\eta_3`$。以下将同射线、首末同射线、前两轮同射线分别记为 AAA、ABA、AAB；不同字母只表示不同射线，不预设正交。下面逐一排除这三个分支。

**三个射线分支均与早期接收矛盾。** 仍反设 $`r_1=2`$。定义二维空间 $`P=\operatorname{span}\{p_\alpha:\alpha=1,2\}`$。由（29.37）—（29.38）及第二终端来源系数，

$$
V_0P=\mathbb Cu\otimes F,\qquad
V_1P=\mathbb Cv\otimes F,\qquad
H_2=\operatorname{span}\{a^2u+bv,w\}.
\tag{29.52}
$$

**早期两个位像给出的共同正交约束。** 由 （29.52）、$`V_0K\perp V_1K`$ 和 （29.41），
$$
G_n\perp v,\qquad Q_n\perp U,
\qquad n=3,4,5.
\tag{29.53}
$$
环境属于 $`F`$ 是这一步的必要前提；例如可用同一个 $`\eta_n\in F`$ 将 $`G_n\otimes\eta_n\perp v\otimes F`$ 化为 $`G_n\perp v`$。

**排除 AAA。** 选三个环境的共同单位代表 $`\eta`$，置
$$
S_0=H_2+H_3+H_4,\qquad S_1=U+G_3+G_4.
$$
它们均为三维。在这两个空间上写 $`V_0x=f(x)\otimes\eta`$、$`V_1y=g(y)\otimes\eta`$。其正交像
$$
R=fS_0=G_3+G_4+G_5,\qquad
W=gS_1=Q_3+Q_4+Q_5
\tag{29.54}
$$
各三维，所以 $`K=R\oplus W`$。由 （29.53），$`v\in W`$、$`U\subset R`$。因此 $`S_1=R`$，$`g:R\to W`$ 为满等距。

式 （29.52） 给 $`P_RH_2=U`$、$`P_WH_2=\mathbb Cv`$，而来源给
$`P_RH_3=G_3`$、$`P_RH_4=G_4`$。于是 $`P_RS_0=U+G_3+G_4=R`$。三维 $`S_0`$ 为某个线性映射 $`T:R\to W`$ 的图，且
$$
T(U)=\mathbb Cv,\qquad T(w)=0,\qquad
T(G_3)=Q_3=gU,\qquad T(G_4)=Q_4=gG_3.
\tag{29.55}
$$
其中 $`T|_{G_3}`$ 单射。因 $`w\ne0`$，$`\operatorname{rank}T\le2`$。但
$`g(U+G_3)\subset\operatorname{im}T`$，所以 $`G_3=U`$。这使同一限制 $`T|_U`$ 同时具有秩一和秩二，矛盾。

**排除 ABA。** 选不同环境射线的单位代表 $`\alpha=\eta_3=\eta_5`$、$`\beta=\eta_4`$。由于 $`G_4=U=G_2`$，固定 $`V_1`$ 给 $`Q_5=Q_3`$。由 （29.53） 和 $`G_3\perp Q_3`$，
$$
Q_3=(U+G_3)^\perp=:Q,
\qquad v\in Q,
\tag{29.56}
$$
因为 $`\dim(U+G_3)=4`$、$`v\perp U+G_3`$。

若 $`\alpha\perp\beta`$，固定 $`V_1`$ 对输入 $`U,G_3`$ 的像给 $`U\perp G_3`$，固定 $`V_0`$ 对输入 $`H_2,H_3`$ 的像给 $`H_2\perp H_3`$。此时 $`H_3\subset G_3\oplus Q\subset U^\perp`$，且 $`P_QH_3=Q`$。由 $`v\in Q`$，存在 $`h\in H_3`$ 使 $`\langle v,h\rangle\ne0`$。因 $`u\perp H_3`$，有
$`\langle a^2u+bv,h\rangle=\bar b\langle v,h\rangle\ne0`$，违反 $`H_2\perp H_3`$。

若 $`\langle\alpha,\beta\rangle\ne0`$，两个不同位的像
$`G_3\otimes\alpha`$、$`Q_4\otimes\beta`$ 正交，故 $`G_3\perp Q_4`$。结合 $`Q_4\perp U`$ 和 （29.56），得到 $`Q_4=Q_3=Q_5=Q`$。因此
$$
V_1(U+G_3)=Q\otimes\operatorname{span}\{\alpha,\beta\}=Q\otimes F.
\tag{29.57}
$$
由 $`v\in Q`$ 和 （29.52），$`V_1P\subset V_1(U+G_3)`$，单射性给 $`P\subset U+G_3=Q^\perp`$。但是 $`H_3\subset G_3\oplus Q`$，且 $`P_Q|_{H_3}`$ 单射，所以 $`H_3\cap Q^\perp=0`$，进而 $`P\cap H_3=0`$。另一方面，
$$
V_0P=u\otimes F,\qquad V_0H_3=U\otimes\beta
$$
的交恰为一维 $`u\otimes\beta`$。固定等距的单射性要求 $`\dim(P\cap H_3)=1`$，矛盾。

**排除 AAB。** 选单位代表 $`\alpha=\eta_3=\eta_4`$、$`\beta=\eta_5`$，射线不同。因为 $`G_3=U=G_2`$，固定 $`V_1`$ 给 $`Q_3=Q_4=:Q`$。由 （29.53）、$`G_4\perp Q_4`$ 和 $`G_4\cap U=0`$，
$$
Q=(U+G_4)^\perp,\qquad v\in Q.
\tag{29.58}
$$

若 $`\alpha\perp\beta`$，固定 $`V_1`$ 对输入 $`U,G_4`$ 的像给 $`U\perp G_4`$，固定 $`V_0`$ 对输入 $`H_2,H_4`$ 的像给 $`H_2\perp H_4`$。此时 $`H_4\subset G_4\oplus Q\subset U^\perp`$，并且 $`P_QH_4=Q`$。如上一分支，$`v\in Q`$ 与 $`b\ne0`$ 使 $`a^2u+bv`$ 不可能正交于整个 $`H_4`$，矛盾。

若 $`\langle\alpha,\beta\rangle\ne0`$，跨位正交性给 $`G_4\perp Q_5`$。结合 $`Q_5\perp U`$ 与 （29.58），得到 $`Q_5=Q`$。从而
$$
V_1(U+G_4)=Q\otimes F.
\tag{29.59}
$$
式 （29.52） 和 $`v\in Q`$ 再给 $`P\subset U+G_4=Q^\perp`$。由于 $`P_Q|_{H_4}`$ 单射，$`P\cap H_4=0`$。但
$`V_0P=u\otimes F`$、$`V_0H_4=G_5\otimes\beta=U\otimes\beta`$ 有一维交，单射性要求 $`\dim(P\cap H_4)=1`$，矛盾。

三个分支均已排除，故 $`r_1=2`$ 不可能。结合 $`r_1=3`$ 的排除，得 $`r_1=1`$，命题得证。


命题29.1和29.2合并，得到任何一般六维五终端精确接收器都必须满足 $`r_1=r_2=1`$。第三至第五终端本来就因 $`4r_n\le6`$ 具有 $`r_n=1`$，所以对任意纯的参考—记忆联合输入，五个终端的参考—活动记忆—接收器联合态全部为纯态。由独立纯初始化和固定 Stinespring 延拓，每一轮新环境也都是输入无关的纯向量；混合输入可先纯化，仍使用同一环境向量。这里只作必要归约，不限制环境射线的相互重叠。

纯环境候选仍须满足同一个全域接收等距、独立初始接收态和全部跨轮 Gram 等式。本节没有证明这样的六维候选存在或不存在，也不能将任意纯环境词换成第25节的正交交替词。一般容量界仍为 $`6\le d_{\mathrm{CPTP},5}(a,b)\le7`$。

本节复用第23节所述的可逆编码固定附加态结构与 Stinespring 等距工具。具体的六维像空间饱和、共同射线下的图空间与秩一差矛盾，以及纯第二终端的二维商空间和早期像空间交限制，均由上述来源关系推出；这些结论给出纯环境必要归约，尚未决定一般六维的存在性。

## 追加锚（本行以下为增补区）

## 30. 六维纯终端接收的后续环境维数

接续第29节的纯终端必要归约，取第26节的非退化来源 $`m_0=a|0\rangle+b|1\rangle`$、$`m_1=|0\rangle`$，其中 $`ab\ne0`$、$`|a|^2+|b|^2=1`$。假设六维固定 CPTP 接收器精确服务前五个完整参考终端，并且前两终端的可逆附加态秩均为一。后面三个终端的档案秩为四，所以其附加态也纯。固定每轮共用的 Stinespring 等距 $`V:K\otimes B\to K\otimes E`$，其每轮实际输出环境是来源无关的纯向量 $`\eta_n`$，$`n=1,\ldots,5`$。

结论保留环境向量之间完整的非正交 Gram 参数，仍只是六维候选的必要条件，没有给出接收器构造。

**共同坐标。**

令 $`k\in K`$ 为独立纯接收初态，$`V_i x=V(x\otimes|i\rangle)`$。前两轮可取接收器正交单位向量 $`p,q`$ 及正交单位向量 $`u,v,w`$，使

$$
V_0k=p\otimes\eta_1,\qquad
V_1k=q\otimes\eta_1,
\tag{30.1}
$$

$$
V_0p=u\otimes\eta_2,\qquad
V_1p=v\otimes\eta_2,\qquad
V_0q=w\otimes\eta_2.
\tag{30.2}
$$

接收后的来源两列及系数支撑满足

$$
\Psi_1^0=m_0p,\quad\Psi_1^1=m_1q,
\qquad
H_1=\operatorname{span}\{p,q\},\quad G_1=\mathbb Cp,
\tag{30.3}
$$

$$
\Psi_2^0=a m_0u+b m_1v,\quad\Psi_2^1=m_0w,
\quad
H_2=\operatorname{span}\{a^2u+bv,w\},\quad
G_2=\operatorname{span}\{u,w\}.
\tag{30.4}
$$

对纯终端 $`n`$ 写 $`\Psi_n^i=|0\rangle_Mx_n^i+|1\rangle_My_n^i`$，定义 $`H_n=\operatorname{span}\{x_n^0,x_n^1\}`$、$`G_n=\operatorname{span}\{y_n^0,y_n^1\}`$、$`C_n=H_n+G_n`$。则

$$
\dim H_n=\dim G_n=2\quad(n=2,3,4,5),\qquad
\dim C_2=3,\quad\dim C_3=\dim C_4=\dim C_5=4.
\tag{30.5}
$$

对第三至第五轮，存在二维 $`Q_n`$ 满足

$$
V_0(H_{n-1})=G_n\otimes\eta_n,\qquad
V_1(G_{n-1})=Q_n\otimes\eta_n,
\qquad G_n\perp Q_n,
\tag{30.6}
$$

$$
C_n=G_n\oplus Q_n,\qquad
P_{G_n}H_n=G_n,\qquad P_{Q_n}H_n=Q_n.
\tag{30.7}
$$

两个投影在二维 $`H_n`$ 上均为同构，这是来源的两个非零系数及两个输入系数对独立性给出的事实。对应实际输入支撑为

$$
D_n=(H_{n-1}\otimes|0\rangle)\oplus
(G_{n-1}\otimes|1\rangle),\qquad
V(D_n)=C_n\otimes\eta_n\quad(n=3,4,5).
\tag{30.8}
$$

**命题30.1（后三轮环境的张成恰为二维）。** 在上述合同中，

$$
\boxed{\dim\operatorname{span}\{\eta_3,\eta_4,\eta_5\}=2.}
\tag{30.9}
$$

等价地，后三轮环境 Gram 矩阵的秩恰为二；其中可以有两条或三条不同射线，结论不将它们强制正交。

**证明：排除三维环境张成。**

反设 $`\eta_3,\eta_4,\eta_5`$ 线性无关。由（30.6），它们分别给 $`V_0`$ 与 $`V_1`$ 像中三个各二维的代数直和项。每个全域像的维数也恰为六，所以

$$
\begin{aligned}
V_0(K)&=(G_3\otimes\eta_3)\dotplus
(G_4\otimes\eta_4)\dotplus(G_5\otimes\eta_5),\\
V_1(K)&=(Q_3\otimes\eta_3)\dotplus
(Q_4\otimes\eta_4)\dotplus(Q_5\otimes\eta_5).
\end{aligned}
\tag{30.10}
$$

这里的直和不要求正交。取单射逆像，还得

$$
K=H_2\dotplus H_3\dotplus H_4
=G_2\dotplus G_3\dotplus G_4.
\tag{30.11}
$$

由（30.2），$`G_2\otimes\eta_2=V_0(H_1)\subseteq V_0(K)`$。先在环境上投影到 $`E/\operatorname{span}\{\eta_3,\eta_4,\eta_5\}`$，得到 $`\eta_2`$ 属于这三个向量的张成。若 $`\eta_2`$ 的 $`\eta_3`$ 系数非零，按独立环境坐标比较，必须有 $`G_2\subseteq G_3`$，与（30.11）矛盾；其 $`\eta_4`$ 系数也同理必须为零。因此

$$
\eta_2\parallel\eta_5,\qquad
G_5=G_2,\qquad H_1=H_4.
\tag{30.12}
$$

最后一个等式来自 $`V_0(H_1)=G_2\otimes\eta_2=G_5\otimes\eta_5=V_0(H_4)`$ 的子空间等式及单射性。

再由（30.1）、（30.10）比较 $`p\otimes\eta_1`$。同样先得 $`\eta_1`$ 属于后三轮环境张成。因为（30.11）、（30.12）使 $`G_3,G_4,G_5`$ 成为三个代数直和空间，非零 $`p`$ 不可能同时属于其中两个；故 $`\eta_1`$ 必与某一个 $`\eta_j`$ 共线，$`j\in\{3,4,5\}`$。同时比较（30.10）的零位和一位像，可得

$$
k\in H_{j-1}\cap G_{j-1}.
\tag{30.13}
$$

第三、第四终端各有四维总支撑，所以 $`H_3\cap G_3=H_4\cap G_4=0`$。因此只能 $`j=3`$，并由（30.4）得到

$$
\eta_1\parallel\eta_3,\qquad k\parallel w.
\tag{30.14}
$$

吸收环境射线相位后，（30.1）、（30.14）使 $`V_0w`$、$`V_1w`$ 分别等于 $`p\otimes\eta_3`$、$`q\otimes\eta_3`$ 的同一个非零标量倍数。第二来源列在第二终端的系数为 $`x_2^1=aw`$、$`y_2^1=bw`$，所以其第三终端零记忆系数为

$$
0\ne x_3^1\in\mathbb C(a^2p+bq)\subseteq H_1=H_4.
\tag{30.15}
$$

它按定义也属于 $`H_3`$，违反（30.11）的 $`H_3\cap H_4=0`$。故后三轮环境不可能张成三维。

**排除共同环境射线。**

现在反设 $`\eta_3\parallel\eta_4\parallel\eta_5`$，吸收相位后写为共同单位向量 $`\eta`$。令

$$
H_\Sigma=H_2+H_3+H_4,\qquad
G_\Sigma=G_2+G_3+G_4.
\tag{30.16}
$$

固定等距在同一环境方向上给 $`\dim H_\Sigma+\dim G_\Sigma\le6`$。两项均至少为三：若 $`\dim G_\Sigma=2`$，则 $`G_2=G_3=G_4`$，由（30.6）得 $`H_2=H_3`$，违反 $`\dim C_2=3`$、$`\dim C_3=4`$；若 $`\dim H_\Sigma=2`$，则 $`H_2=H_3=H_4`$、$`G_3=G_4`$，违反第26节式（26.20）的主角度行列式严格变化。因此

$$
\dim H_\Sigma=\dim G_\Sigma=3.
\tag{30.17}
$$

去掉共同环境因子，写

$$
V_0x=f(x)\otimes\eta\quad(x\in H_\Sigma),\qquad
V_1y=g(y)\otimes\eta\quad(y\in G_\Sigma).
$$

$`f,g`$ 为等距，其像 $`U=fH_\Sigma`$、$`W=gG_\Sigma`$ 正交且均三维，故

$$
K=U\oplus W,\qquad
fH_2=G_3,\quad fH_3=G_4,\quad fH_4=G_5,
\quad gG_2=Q_3,\quad gG_3=Q_4,\quad gG_4=Q_5.
\tag{30.18}
$$

**第二轮环境必须正交于共同尾环境。** 反设 $`\langle\eta_2,\eta\rangle\ne0`$。$`V_0(K)\perp V_1(K)`$，结合（30.2）、（30.18）给

$$
G_2\perp W,\qquad v\perp U,
\quad\text{所以}\quad G_2\subset U,\ v\in W.
\tag{30.19}
$$

而 $`G_3,G_4\subset U`$，所以 $`G_\Sigma=U`$，$`g:U\to W`$ 为满等距。

若 $`G_3\ne G_4`$，两个二维子空间张成三维 $`U`$。由（30.7），$`P_UH_3=G_3`$、$`P_UH_4=G_4`$，故 $`P_UH_\Sigma=U`$。于是三维 $`H_\Sigma`$ 是线性映射 $`T:U\to W`$ 的图，并有

$$
T(G_3)=Q_3=gG_2,\qquad T(G_4)=Q_4=gG_3,
\qquad\operatorname{im}T=g(G_2+G_3).
\tag{30.20}
$$

因 $`0\ne w\in H_2\cap G_2\subset H_\Sigma\cap U`$，有 $`\ker T\ne0`$，故 $`\operatorname{rank}T\le2`$。（30.20）及 $`g`$ 单射迫使 $`G_2=G_3`$，从而 $`w\in G_3\cap\ker T`$；但（30.7）使 $`T|_{G_3}`$ 单射，矛盾。

若 $`G_3=G_4`$，固定 $`V_0`$ 与共同环境直接给 $`H_2=H_3`$。由（30.4）、（30.19），$`P_UH_2=G_2`$，而（30.7）给 $`P_UH_3=G_3`$，所以 $`G_2=G_3`$，再次违反第二、第三终端支撑秩差。因此

$$
\eta_2\perp\eta,\qquad H_1\perp H_\Sigma,\qquad p\perp G_\Sigma.
\tag{30.21}
$$

后两个正交性由（30.2）、（30.6）及固定等距直接得到。

**第一轮环境也必须正交于共同尾环境。** 反设 $`\langle\eta_1,\eta\rangle\ne0`$。用（30.1）的两个输入位与（30.18）交叉比较，得 $`p\in U`$、$`q\in W`$。二者又都属于 $`H_1`$，故由（30.21）正交于 $`H_\Sigma`$。

若 $`G_3\ne G_4`$，则 $`P_UH_\Sigma`$ 包含 $`G_3+G_4=U`$，从而 $`p\in U`$ 且 $`p\perp U`$，矛盾。若 $`G_3=G_4`$，则 $`G_\Sigma=G_2+G_3`$，并由（30.7）、（30.18）得到

$$
P_WH_\Sigma\supseteq Q_3+Q_4
=g(G_2+G_3)=W.
$$

于是 $`q\in W`$ 且 $`q\perp W`$，也矛盾。因此

$$
\eta_1\perp\eta.
\tag{30.22}
$$

由（30.1）、（30.18）、（30.22），初态 $`k`$ 同时正交于 $`H_\Sigma`$ 与 $`G_\Sigma`$；而（30.21）及 $`p\in H_1`$ 给 $`p`$ 也同时正交于这两个空间。

**最后的支撑秩矛盾。** $`k,p`$ 必线性无关。否则令 $`p=\lambda k`$，由（30.1）、（30.2）的非零纯张量等式可得 $`\eta_1\parallel\eta_2`$、$`u\parallel p`$、$`v\parallel q`$，从而

$$
H_1=\operatorname{span}\{u,v\}.
$$

非零向量 $`a^2u+bv`$ 又属于 $`H_2`$，违反（30.21）的 $`H_1\perp H_\Sigma`$。

因此 $`(H_\Sigma+G_\Sigma)^\perp`$ 至少二维，$`\dim(H_\Sigma+G_\Sigma)\le4`$。但是四维 $`C_3=H_3+G_3`$ 和 $`C_4=H_4+G_4`$ 均包含于这个和空间，故

$$
C_3=C_4=H_\Sigma+G_\Sigma.
\tag{30.23}
$$

（30.8）的共同环境现在给 $`V(D_3)=C_3\otimes\eta=C_4\otimes\eta=V(D_4)`$。单射性强制 $`D_3=D_4`$，分别比较两个输入位得到 $`H_2=H_3`$、$`G_2=G_3`$，继而 $`C_2=C_3`$，与（30.5）的三维、四维秩矛盾。

共同尾射线也被排除。三条非零环境向量的张成只能有维数一、二、三；前后两项均不可能，故得到（30.9）。证明完毕。



（30.9）没有把二维环境中的三个射线限制为两个，也没有将不同射线正交化。它只控制后三轮环境；前两轮是否属于同一个二维环境空间尚未由此证明。一般六维纯终端实现仍须满足（30.1）—（30.8）及全部跨轮 Gram 等式。标准可逆编码和共同 Stinespring工具沿第23节已读来源；本节没有以这些来源替代具体的支撑与射线推导。

## 追加锚（本行以下为增补区）

## 31. 多相位边发射的商空间容量与因果接收

本节研究有限状态 Markov 转移、整数边荷与完整边标签发射。实际相位在一次运行中保持不变。来源与前面的两态量子发射器不同；本节允许接收门随当前编号变化，不用于判定第29—30节的同一固定接收通道容量。

**定义31.1（来源、商空间与完整联合合同）。** 取状态集 $\mathcal V=\{1,\ldots,m\}$、primitive 行随机矩阵 $P$，即某个正整数幂的全部矩阵元严格为正。记非空支持边集
$\mathcal E=\{(i,j):P_{ij}>0\}$、$s=|\mathcal E|$。每条支持边给定整数荷 $g_{ij}\in\mathbb Z^q$。活动记忆为 $M=\mathbb C^m$，发出位为 $B=\mathbb C^{\mathcal E}$，其已知正交基保留完整边标签。对 $\theta\in\mathbb T^q=(\mathbb R/2\pi\mathbb Z)^q$，一步等距为

$$
V_\theta|i\rangle
=\sum_{j:P_{ij}>0}\sqrt{P_{ij}}\,
e^{i\theta\cdot g_{ij}}|i,j\rangle_B\otimes|j\rangle_M.
\tag{31.1}
$$

不同初始状态由边标签中的起点区分，行随机性保证范数为一。置 $H_n=B^{\otimes n}$、$H_0=\mathbb C$，并递归定义

$$
T_{\theta,0}=I_M,\qquad
T_{\theta,n+1}=(I_{H_n}\otimes V_\theta)T_{\theta,n},\qquad
\Omega_{\theta,n}(\rho)
=(I_J\otimes T_{\theta,n})\rho(I_J\otimes T_{\theta,n}^*).
\tag{31.2}
$$

这里 $J$ 是任意有限参考，$\rho\in\mathcal D(J\otimes M)$ 是任意初始联合态。固定非空候选集 $\Theta\subseteq\mathbb T^q$，不要求闭或可测。允许全域 CPTP 编解码
$\mathcal E_n:\mathcal L(H_n)\to\mathcal L(K)$、
$\mathcal D_n:\mathcal L(K)\to\mathcal L(H_n)$，依赖已知模型、$\Theta,n,\epsilon$，但不能依赖实际相位、输入或参考，也不能访问 $J,M$。半迹距离记为 $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$。要求

$$
\sup_{\theta\in\Theta,\ J,\ \rho}
D\!\left(
(\operatorname{id}_J\otimes\mathcal D_n\mathcal E_n
 \otimes\operatorname{id}_M)\Omega_{\theta,n}(\rho),
\Omega_{\theta,n}(\rho)\right)\le\epsilon.
\tag{31.3}
$$

最小 $\dim K$ 记为 $k_n^{(\epsilon)}(\Theta)$；$\epsilon=0$ 表示精确恢复，$k_0^{(\epsilon)}=1$。全部持久且携带输入信息的接收系统计入 $K$，包括经典标签和失败旗标。已知门描述、时间编号、网的取得、路由和新空白另行计量；本节不提供任意候选集的有效描述或门复杂度界。

与未来终端无关的在线合同要求预先给定同一列

$$
K_0=\mathbb C,\qquad
\mathcal C_t:\mathcal L(K_{t-1}\otimes B)\to\mathcal L(K_t),
\qquad
\mathcal D_t:\mathcal L(K_t)\to\mathcal L(H_t),
\tag{31.4}
$$

在每个确定终端满足（31.3）。门可依赖当前编号，不能依赖未来终端；新环境可立即丢弃。不增加适应性停止或解码后继续运行的要求。

定义标量相位加端点势差的子群

$$
\mathcal H=\left\{h\in\mathbb T^q:
\begin{array}{l}
\exists\,\omega\in\mathbb R,\ |z_1|=\cdots=|z_m|=1,\\
e^{ih\cdot g_{ij}}=e^{i\omega}z_i\overline{z_j}
\quad((i,j)\in\mathcal E)
\end{array}\right\}.
\tag{31.5}
$$

原环面取平坦测地距离。下文证明 $\mathcal H$ 闭；商
$\mathcal Q=\mathbb T^q/\mathcal H$ 配距离

$$
d_{\mathcal Q}([\theta],[\varphi])
=\min_{h\in\mathcal H}d_{\mathbb T^q}(\theta-\varphi,h).
\tag{31.6}
$$

相位乘子、内部酉规范和量子 Markov 参数识别已有一般理论，局部参数的 $n^{-1/2}$ 高斯尺度也已有先例。[^phase_multiphase_gk] 本节另外证明此边标签模型的全局有限步估计、任意参考历史界与完整联合接收容量。

**引理31.2（路径荷差与全部退化相位）。** 对支持路径
$\gamma=(i_0,\ldots,i_n)$，记 $|\gamma|=n$、
$g(\gamma)=\sum_{t=1}^n g_{i_{t-1}i_t}$。令 $\Lambda\le\mathbb Z^q$ 为全部同长度、同起点、同终点路径的荷差生成的整数子群，则

$$
\mathcal H=\Lambda^\perp
=\{h:e^{ih\cdot\lambda}=1\text{ 对全部 }\lambda\in\Lambda\}.
\tag{31.7}
$$

所以 $\mathcal H$ 闭，允许有有限多个连通分支；$\mathcal Q$ 是维数
$r=\operatorname{rank}\Lambda$ 的连通紧环面。$r=0$ 时商为单点，不存在额外的有限非平凡离散商。

证明。（31.5）沿路径相乘为 $e^{in\omega}z_{i_0}\overline{z_{i_n}}$，正向成立。反向令

$$
M_h(i,j)=P_{ij}e^{ih\cdot g_{ij}}.
\tag{31.8}
$$

若 $h\in\Lambda^\perp$，同一 $n,i,j$ 的所有路径相位一致，故
$|M_h^n(i,j)|=P^n(i,j)$，不存在路径时两侧均零。因此
$\|M_h^n\|_{\infty\to\infty}=1$，其中该范数是最大绝对行和。有限维谱半径公式给 $\rho(M_h)=1$。取模一特征值
$M_hz=e^{i\omega}z$，从最大模分量所在行的三角不等式取等号，再沿不可约支持图传播，得到所有 $|z_i|$ 相等且非零。逐行取等号于是给
$e^{ih\cdot g_{ij}}z_j=e^{i\omega}z_i$；归一化共同模即得（31.5）。闭子群及商维数结论是有限生成整数子群的标准环面对偶结构。证明完毕。

**引理31.3（统一有限步高斯衰减）。** 存在只依赖 $P,g$ 的
$C_{\mathrm G}\ge1$、$c_{\mathrm G}>0$，使对全部 $\delta\in\mathbb T^q$、$n\ge0$，

$$
\boxed{
\|M_\delta^n\|_{\infty\to\infty}
\le C_{\mathrm G}
e^{-c_{\mathrm G}n\,d_{\mathcal Q}([\delta],0)^2}.
}
\tag{31.9}
$$

同一右侧也控制 $|m^{-1}\mathbf1^{\mathsf T}M_\delta^n\mathbf1|$。

证明。$\Lambda=0$ 时商距离恒零，取 $C_{\mathrm G}=1$ 即可。否则可从实际路径对中选有限多个荷差 $\lambda_1,\ldots,\lambda_\ell$ 生成 $\Lambda$：有限生成元各由有限个实际差的整数线性组合表示，收集所用差即可。

固定顶点 $`i_*,j_*`$。primitive 性给 $N$，使任意两顶点间每个长度至少 $N$ 都有支持路径。为每对见证接同一条从 $`i_*`$ 出发的 $N$ 步前缀，再接同一条到 $`j_*`$ 的后缀。选足够大的共同总长度 $L$，使每对所需后缀长度 $L-N-|\gamma|$ 均至少为 $N$。见证的荷差不变，现在全为 $L$ 步的 $`i_*\to j_*`$ 路径对。

对全部这种桥路径令 $w_\gamma=\prod_tP_{i_{t-1}i_t}>0$，置

$$
a_0=P^L(i_*,j_*)=\sum_\gamma w_\gamma>0,\qquad
S(\delta)=M_\delta^L(i_*,j_*)
=\sum_\gamma w_\gamma e^{i\delta\cdot g(\gamma)}.
\tag{31.10}
$$

有精确恒等式

$$
a_0^2-|S(\delta)|^2
=\sum_{\gamma,\gamma'}w_\gamma w_{\gamma'}
[1-\cos(\delta\cdot(g(\gamma)-g(\gamma')))].
\tag{31.11}
$$

各项非负。保留有限见证的项，合并重复项或减小正常数，得

$$
a_0^2-|S(\delta)|^2
\ge c_0\sum_{a=1}^{\ell}[1-\cos(\delta\cdot\lambda_a)]
\ge c_0c_1d_{\mathcal Q}([\delta],0)^2
\tag{31.12}
$$

其中 $c_0,c_1>0$。第二个不等式的理由如下：三角多项式的零集恰为
$\mathcal H$；在其统一小邻域内，取到最近群点的短实提升
$v\perp\operatorname{Lie}(\mathcal H)$。行向量 $\lambda_a$ 在该法空间上单射，故 $\sum_a(\lambda_a\cdot v)^2$ 控制 $\|v\|^2$，而
$1-\cos t$ 在小邻域内控制 $t^2$。邻域外由紧性及无零点取得正下界。这个论证统一处理 $\mathcal H$ 的所有连通分支。

因 $a_0+|S|\le2a_0$，第 $`i_*`$ 行的绝对行和至多
$1-a\,d_{\mathcal Q}^2$，其中 $a=c_0c_1/(2a_0)>0$；其余行至多一。取整数 $K$ 使 $P^K>0$，令
$`b=\min_iP^K(i,i_*)>0`$、$\kappa=ab$、$T=K+L$。逐项不等式
$|M_\delta^{K+L}|\le P^K|M_\delta^L|$ 将该亏损传播到全部起点：

$$
\|M_\delta^T\|_{\infty\to\infty}
\le1-\kappa d_{\mathcal Q}([\delta],0)^2.
\tag{31.13}
$$

按 $T$ 步分块，余下块的范数至多一。设
$\Delta=\operatorname{diam}\mathcal Q$，可取
$C_{\mathrm G}=e^{\kappa\Delta^2}$、$c_{\mathrm G}=\kappa/T$，得到（31.9）。这里直接控制有限步矩阵幂，没有略去非正规矩阵的幂常数或引入随 $n$ 增长的多项式损失。证明完毕。

**引理31.4（共同标量历史比较与任意参考界）。** 令 $\pi$ 为 $P$ 的平稳分布，定义

$$
\begin{gathered}
\beta_k=\max_i\sum_j|P^k(i,j)-\pi_j|,\quad
B_1=\sum_{k\ge0}\beta_k,\quad B_2=\sum_{k\ge0}\beta_k^2,\\
G_*=\max_{(i,j)\in\mathcal E}\|g_{ij}\|,\quad
\mu=\sum_{i,j}\pi_iP_{ij}g_{ij},\quad
C_{\mathrm{hist}}=1+G_*^2(1+4B_1+B_2).
\end{gathered}
\tag{31.14}
$$

primitive 性保证两个级数有限。给定已知相位历史
$\boldsymbol\varphi=(\varphi_1,\ldots,\varphi_n)$，以每步
$V_{\varphi_t}$ 定义虚拟等距 $T_{\boldsymbol\varphi,n}$。对实际常相位
$\theta$，取 $\delta_t\in\mathbb R^q$ 为 $\theta-\varphi_t$ 的最短实提升，并置
$b=\sum_t\delta_t\cdot\mu$。则

$$
\boxed{
(T_{\theta,n}-e^{ib}T_{\boldsymbol\varphi,n})^*
(T_{\theta,n}-e^{ib}T_{\boldsymbol\varphi,n})
\preceq C_{\mathrm{hist}}
\left(\sum_t\|\delta_t\|^2\right)I_M.
}
\tag{31.15}
$$

证明。对初态 $X_0=i$ 的 Markov 链，令
$Y_t=\delta_t\cdot g_{X_{t-1}X_t}$、$Z=\sum_tY_t$。平稳均值与混合界给

$$
|\mathbb E_iZ-b|
\le G_*\sum_t\beta_{t-1}\|\delta_t\|,
\qquad
\operatorname{Var}_iY_t\le G_*^2\|\delta_t\|^2.
\tag{31.16}
$$

若 $s<t$，对截至第 $s$ 条边的历史 $\mathcal F_s$ 条件化，从 $X_s$ 到第 $t$ 条边的起点还需 $t-s-1$ 次转移，故

$$
|\mathbb E[Y_t\mid\mathcal F_s]-\delta_t\cdot\mu|
\le G_*\beta_{t-s-1}\|\delta_t\|,
\qquad
|\operatorname{Cov}_i(Y_s,Y_t)|
\le2G_*^2\beta_{t-s-1}\|\delta_s\|\,\|\delta_t\|.
\tag{31.17}
$$

后一式使用 $`\mathbb E|Y_s-\mathbb E Y_s|\le2G_*\|\delta_s\|`$。方差展开中用 $2uv\le u^2+v^2$，均值偏移平方用 Cauchy–Schwarz，得到全部初态共用的

$$
\mathbb E_i(Z-b)^2
\le G_*^2(1+4B_1+B_2)\sum_t\|\delta_t\|^2
\le C_{\mathrm{hist}}\sum_t\|\delta_t\|^2.
\tag{31.18}
$$

整数荷保证逐路径相位差正是 $e^{iZ}$。展开各输入列并使用
$|e^{ix}-1|\le|x|$，其误差范数平方受（31.18）控制。不同初始 $i$ 被首条完整边标签分入正交档案扇区，因此列界提升为（31.15）的整个输入算子界。同一个 $b$ 用于所有初态，故可以张量任意参考，保留全部输入相干。证明完毕。

**引理31.5（单个常量群移位保持投影漏出）。** 对已知历史定义

$$
\chi_{ij}^{n,\boldsymbol\varphi}
=\sum_{\substack{\gamma:i\to j\\|\gamma|=n}}
\sqrt{w_\gamma}\,
e^{i\sum_{t=1}^n\varphi_t\cdot g_{i_{t-1}i_t}}|\gamma\rangle,\qquad
S_n(\boldsymbol\varphi)=
\operatorname{span}\{\chi_{ij}^{n,\boldsymbol\varphi}:i,j\in\mathcal V\}.
\tag{31.19}
$$

不存在的路径扇区给零向量。其支撑维数至多 $m^2$，且
$T_{\boldsymbol\varphi,n}|i\rangle=\sum_j\chi_{ij}^{n,\boldsymbol\varphi}\otimes|j\rangle$。
若 $W_n$ 是任意这些历史支撑的线性和，$\Pi_n$ 为投影，则对每个
$h\in\mathcal H$，

$$
T_{\theta+h,n}^*[(I-\Pi_n)\otimes I_M]T_{\theta+h,n}
=T_{\theta,n}^*[(I-\Pi_n)\otimes I_M]T_{\theta,n}.
\tag{31.20}
$$

证明。选（31.5）的 $\omega,z$。常量相移在每个端点扇区只乘
$e^{in\omega}z_i\overline{z_j}$，因而定义一个档案端点对角酉
$D_{h,n}$；在不合法档案基向量上可任意作对角酉延拓。它保持每个
$S_n(\boldsymbol\varphi)$ 及其任意和 $W_n$，并与 $\Pi_n$ 交换。又有
$T_{\theta+h,n}=(D_{h,n}\otimes I_M)T_{\theta,n}$，即得（31.20）。这里完整保留端点相干，未把不同初态分别移相。证明完毕。

**定理31.6（任意候选集的单终端商空间容量）。** 令
$\Gamma=\{[\theta]:\theta\in\Theta\}\subseteq\mathcal Q$，以商距离定义

$$
\operatorname{Pack}(\Gamma,r)=
\max\{|A|:A\subseteq\Gamma,\ d_{\mathcal Q}(x,y)\ge r
\text{ 对全部不同的 }x,y\in A\}.
\tag{31.21}
$$

固定 $0<\epsilon<1$。对全部充分大的 $n$，统一于非空候选集，

$$
\boxed{
k_n^{(\epsilon)}(\Theta)
\asymp_{P,g,\epsilon}\operatorname{Pack}(\Gamma,n^{-1/2}).
}
\tag{31.22}
$$

具体上界对所有 $n\ge1$ 为

$$
k_n^{(\epsilon)}(\Theta)\le
m^2\operatorname{Pack}\!\left(
\Gamma,\frac{\epsilon}{\sqrt{2C_{\mathrm{hist}}n}}\right)+1.
\tag{31.23}
$$

这个上界可由门依赖预定终端 $n$ 的因果接收实现。

证明。紧商环面的分离集基数有有限整数上界，故最大基数由某个实际有限子集取得；包含意义下极大的分离集同时为严格同半径网。这不要求 $\Gamma$ 闭或可测。

上界取尺度 $h=\epsilon/\sqrt{2C_{\mathrm{hist}}n}$ 的极大网，点数
$N\le\operatorname{Pack}(\Gamma,h)$。为各网点任取相位代表，以其常相位支撑之和定义 $W_n$，则 $\dim W_n\le m^2N$。对实际 $\theta$，选临近网点及一个常量 $h_0\in\mathcal H$，使 $\theta+h_0$ 与该代表的原环面距离小于 $h$。由（31.15）、（31.20），

$$
T_{\theta,n}^*[(I-\Pi_n)\otimes I_M]T_{\theta,n}
\preceq C_{\mathrm{hist}}nh^2I_M
=\frac{\epsilon^2}{2}I_M.
\tag{31.24}
$$

因果实现时，在每个前缀 $t\le n$ 都用这个同一终端网的全部常相位支撑之和。其维数始终至多 $m^2N$，并满足
$W_{t+1}\subseteq W_t\otimes B$。以
$W_0=K_0=\mathbb C$ 启动，用下一定理（31.31）—（31.33）的部分等距、吸收旗标与全域完成，累计成功恰等于终端投影。式（31.24）给所需完整联合误差；无须预先保存完整档案。

下界取 $n^{-1/2}$ 分离的最大集合，点数为 $N$，并从实际 $\Theta$ 选各点代表。输入取 $m$ 维 Bell 参考态，完整纯目标记为
$|\Psi_{\theta,n}\rangle$。路径正交性精确给

$$
\langle\Psi_{\theta,n},\Psi_{\varphi,n}\rangle
=\frac1m\mathbf1^{\mathsf T}M_{\varphi-\theta}^n\mathbf1.
\tag{31.25}
$$

若商维数为 $r_{\mathcal Q}$，固定紧平坦环面的局部体积比较给常数
$C_{\mathrm{pack}}$，使距某分离点在
$[\ell n^{-1/2},(\ell+1)n^{-1/2})$ 内的点数至多
$C_{\mathrm{pack}}(\ell+2)^{r_{\mathcal Q}}$，对充分大 $n$ 统一成立。由（31.9），Gram 绝对行和统一有界：

$$
B_{\mathrm G}
=C_{\mathrm G}C_{\mathrm{pack}}
\sum_{\ell\ge0}(\ell+2)^{r_{\mathcal Q}}e^{-c_{\mathrm G}\ell^2}
<\infty.
\tag{31.26}
$$

商为单点时直接取 $B_{\mathrm G}=1$。平均目标态
$\bar\rho=N^{-1}\sum_j|\Psi_{\theta_j,n}\rangle\langle\Psi_{\theta_j,n}|$
与 Gram 矩阵具有相同非零谱，差一个 $1/N$ 因子，所以
$\|\bar\rho\|_{\mathrm{op}}\le B_{\mathrm G}/N$。

任取维数 $D$ 的合法编码及共同解码，置
$\tau=\mathcal D_n(I_D)$，则 $\tau\succeq0$、$\operatorname{Tr}\tau=D$。
编码后的联合密度矩阵不超过 $I_{JM}\otimes I_D$；解码正性使恢复态不超过 $I_{JM}\otimes\tau$。半迹误差至多 $\epsilon$ 给每个目标重叠至少
$1-\epsilon$，取平均得

$$
1-\epsilon\le
\operatorname{Tr}[\bar\rho(I_{JM}\otimes\tau)]
\le\frac{B_{\mathrm G}m^2D}{N}.
\tag{31.27}
$$

故 $D\ge(1-\epsilon)N/(B_{\mathrm G}m^2)$；这里 $m^2$ 正是参考与活动记忆的乘积维数。最后，固定商环面的局部打包比较将（31.23）的细尺度分离数控制为粗尺度 $n^{-1/2}$ 分离数的常数倍，常数只依赖模型及固定 $\epsilon$。上下界统一于候选集，得（31.22）。证明完毕。

**定理31.7（同一套无未来终端信息的接收门）。** 给定正的非增序列
$(u_j)_{j\ge0}$，满足 $\sum_j u_j^2\le1$。置

$$
c_*=\frac{1-2^{-1/2}}{\sqrt{2C_{\mathrm{hist}}}},
\qquad \rho_j=c_*\epsilon u_j2^{-j/2}.
\tag{31.28}
$$

存在同一列满足（31.4）的全域接收门，在所有确定终端、全部实际相位和任意参考输入上误差至多 $\epsilon$。令
$k=\lfloor\log_2n\rfloor$，则

$$
\boxed{
\dim K_n\le m^2\operatorname{Pack}(\Gamma,\rho_k)+1
\le m^2\operatorname{Pack}\!\left(
\Gamma,\frac{c_*\epsilon u_k}{\sqrt n}\right)+1.
}
\tag{31.29}
$$

证明。取嵌套有限极大 $\rho_j$ 分离集
$A_0\subseteq A_1\subseteq\cdots\subseteq\Gamma$。因
$\rho_{j+1}\le2^{-1/2}\rho_j$，旧网可扩张成新网。每个新节点选距小于
$\rho_{j-1}$ 的父节点，旧节点取恒等父映射。初层任取相位代表；递归沿
$\mathcal H$ 调整每个新节点代表，使其与已固定父节点代表的原环面距离等于商距离。紧性保证最小值取得，旧节点保留原代表。

在区块 $\{2^j,\ldots,2^{j+1}-1\}$，每个第 $k$ 层叶节点使用其第 $j$ 层祖先代表为虚拟相位，再截到当前终端 $n$。这些历史全部预先固定。对实际 $\theta$，只在误差证明中选距其商点小于 $\rho_k$ 的叶，再选单个
$h\in\mathcal H$，使 $\theta+h$ 与叶代表的原环面距离小于 $\rho_k$。沿父链的三角不等式给每个第 $j$ 块的误差至多
$\rho_j/(1-2^{-1/2})$，故

$$
\sum_{t\le n}d_{\mathbb T^q}(\theta+h,\varphi_t)^2
\le\frac1{(1-2^{-1/2})^2}\sum_{j\le k}2^j\rho_j^2
\le\frac{\epsilon^2}{2C_{\mathrm{hist}}}.
\tag{31.30}
$$

每个终端只有一个固定的 $h$，没有逐块更换群移位或修改预定历史。由（31.15）、（31.20），实际 $\theta$ 的投影漏出也受
$\epsilon^2I_M/2$ 控制。

令 $W_n$ 为当前层全部叶历史支撑之和。其维数至多 $m^2|A_k|$。若历史延长一步，

$$
\chi_{ij}^{n+1,\boldsymbol\varphi'}
=\sum_{\ell:(\ell,j)\in\mathcal E}\sqrt{P_{\ell j}}\,
e^{i\varphi'_{n+1}\cdot g_{\ell j}}\,
\chi_{i\ell}^{n,\boldsymbol\varphi}\otimes|\ell,j\rangle.
\tag{31.31}
$$

区块内部沿同一叶延长；区块边界的新叶旧前缀恰为父节点历史。因此始终
$W_{n+1}\subseteq W_n\otimes B$。

记 $\Pi_n$ 为投影。取 $W_0=K_0=\mathbb C$、$F_0=\Pi_0=I$；对
$n\ge1$，取
$K_n=\mathbb C^{\dim W_n}\oplus\mathbb C|\bot_n\rangle$，以 $F_n$ 将
$W_n$ 等距编码到成功块。将 $F_n$ 在 $W_n^\perp$ 上以零延拓，所以其伴随在失败旗标上为零。定义

$$
\begin{aligned}
L_n&=F_n\Pi_n(F_{n-1}^*\otimes I_B),\\
\mathcal C_n(X)&=L_nXL_n^*
+\operatorname{Tr}[(I-L_n^*L_n)X]|\bot_n\rangle\langle\bot_n|.
\end{aligned}
\tag{31.32}
$$

前缀包含使 $`L_n^*L_n`$ 为投影，故此式全域完全正且保迹，旧旗标保持吸收。接收门和之后的来源发射作用于不同系统，可以交换。又因
$\Pi_n(\Pi_{n-1}\otimes I_B)=\Pi_n$，连续成功 Kraus 的乘积恰为
$F_n\Pi_n$。不存在对不同终端失败的额外并集误差。

取任意固定档案态 $\tau_n$，终端解码为

$$
\mathcal D_n(Y)=F_n^*YF_n+
\langle\bot_n|Y|\bot_n\rangle\tau_n.
\tag{31.33}
$$

对任意初始参考输入先纯化。令纯目标漏出质量为 $d_n\le\epsilon^2/2$。成功分支与目标重叠为 $(1-d_n)^2$，所有失败项为正，因此

$$
D(\widehat\Omega,\Omega)
\le\sqrt{1-(1-d_n)^2}\le\sqrt{2d_n}\le\epsilon.
\tag{31.34}
$$

丢弃额外纯化参考后仍成立。全域通道可用立即丢弃的新环境实现，并按需要附加独立纯空白，不保留未计入寄存器的输入相关系统。维数计数给（31.29）。证明完毕。

**推论31.8（商候选集的上下盒维与几何稀疏增长）。** 取任意固定 $\eta>0$，例如选择

$$
u_j=\frac{C_\eta}{\sqrt{(j+2)[\log(j+2)]^{1+2\eta}}},
\qquad
C_\eta=\left(\sum_{j\ge0}
\frac1{(j+2)[\log(j+2)]^{1+2\eta}}\right)^{-1/2}.
\tag{31.35}
$$

令 $\underline d,\overline d$ 分别为
$\log\operatorname{Pack}(\Gamma,r)/\log(1/r)$ 在 $r\downarrow0$ 的下、上极限。定理31.7的同一门序列满足

$$
\liminf_{n\to\infty}\frac{\log\dim K_n}{\log n}
=\frac{\underline d}{2},\qquad
\limsup_{n\to\infty}\frac{\log\dim K_n}{\log n}
=\frac{\overline d}{2}.
\tag{31.36}
$$

任意合法门序列的相应下、上极限分别至少为这两个数。

证明。细化尺度
$`r_n=c_*\epsilon u_{\lfloor\log_2n\rfloor}/\sqrt n`$
递减到零，相邻项之比趋于一，且 $\log(1/r_n)/\log n\to1/2$。dyadic 跳点还使用 $u_{j+1}/u_j\to1$。分离数的单调性在相邻尺度间夹逼，给出与全尺度相同的上下盒维极限。再用（31.22）的逐终端下界及（31.29）的上界即可。这需要所选预算的缓变性质，不适用于任意平方可和预算。证明完毕。

若商候选集满足
$\operatorname{Pack}(\Gamma,r)\asymp1+\log(1/r)$，则同一在线构造给
$\dim K_n=\Theta_{P,g,\Gamma,\epsilon,\eta}(\log n)$，任意合法门序列也受相应对数下界。例如，在商环面的局部等距坐标片内取足够短的非零向量 $v$，
$\Gamma=\{0\}\cup\{a^jv:j\ge0\}$、$0<a<1$，就满足此条件。条件必须落在商空间；原参数集沿 $\mathcal H$ 的几何序列可以投影为单点。

例如，两态 $P_{ij}=1/2$、$q=2$、$g_{ij}=(i-j,\mathbf1_{\{i=j=0\}})$，状态编号为 $0,1$。第一坐标为端点势差，而路径
$0\to0\to1$ 与 $0\to1\to1$ 的荷差为 $(0,1)$，所以
$\Lambda=\mathbb Z(0,1)$、$\mathcal H=\mathbb T\times\{0\}$。
原参数集 $\{(0,0)\}\cup\{(a^j,0):j\ge0\}$ 虽为几何序列，其商像却为单点，整个族有同一份至多 $m^2$ 维档案支撑，能精确常数维接收。只给原参数距离的几何上界也不足以推出对数增长。

[^phase_multiphase_gk]: Mădălin Guţă and Jukka Kiukas, *Equivalence classes and local asymptotic normality in system identification for quantum Markov chains*, [arXiv:1402.3535v1](https://arxiv.org/abs/1402.3535v1)。Theorem 2 将 primitive 量子 Markov 等距的平稳输出等价刻画为相位乘子与内部酉共轭；Lemma 2 给相应模一外围谱判据。Theorem 4 对解析单参数族的有界局部参数 $\theta=\theta_0+u/\sqrt n$ 给联合系统—输出纯态的高斯极限及统计模型强收敛。§5.3 Corollary 1 说明等价规范方向的渐近每步 Fisher 信息为零，初态或端点仍可携带非广延信息。这些结论不直接给出本节任意候选集、全局有限步、任意参考和完整联合恢复的容量定理；（31.9）、（31.15）、（31.20）及前缀支撑构造承担这些额外义务。

本节的前缀支撑相干接收和纯目标迹距离转换分别复用既有机制。[^phase_bcz][^phase_fvg] 商空间尺度及完整联合容量由本节的具体有限源关系推出；这里不作这些容量结论的外部原创优先权主张。

## 追加锚（本行以下为增补区）

## 32. 循环荷格、精确字符容量与一维候选弧

本节继续第31节的边标签来源与完整联合恢复合同。先用有限整数矩阵计算商维数，再确定全相位候选集的精确容量，并比较精确恢复与固定正误差恢复。接收门仍可依当前编号变化。以下不改判第29—30节的固定接收通道问题。

**引理32.1（实际路径差格的有限矩阵表示）。** 令支持图有 $m$ 个顶点、$s$ 条边，非空且强连通；本引理暂不要求非周期。取有符号关联矩阵
$\mathsf D\in\mathbb Z^{m\times s}$，边 $e:i\to j$ 的列为
$\mathbf e_j-\mathbf e_i$，自环列为零。令

$$
A=\begin{pmatrix}\mathsf D\\\mathbf1^{\mathsf T}\end{pmatrix},
\qquad
G=(g_e)_{e\in\mathcal E}\in\mathbb Z^{q\times s}.
\tag{32.1}
$$

若 $L_{\mathrm{path}}$ 为全部等长、同起终点支持路径的边计数差生成的整数群，则

$$
\boxed{
L_{\mathrm{path}}=\ker_{\mathbb Z}A,\qquad
\Lambda=G(\ker_{\mathbb Z}A).
}
\tag{32.2}
$$

而且 $\ker_{\mathbb Z}A$ 的每个元素本身就是一对实际等长、同起终点路径的计数差。商维数可计算为

$$
\boxed{
r=\operatorname{rank}\Lambda
=\operatorname{rank}_{\mathbb R}
 \begin{pmatrix}\mathsf D\\\mathbf1^{\mathsf T}\\G\end{pmatrix}-m.
}
\tag{32.3}
$$

证明。若 $x(\gamma)\in\mathbb Z_{\ge0}^s$ 为路径边计数，则
$\mathsf D x(\gamma)=\mathbf e_j-\mathbf e_i$、
$\mathbf1^{\mathsf T}x(\gamma)=|\gamma|$。等长同端点路径的差在
$\ker_{\mathbb Z}A$ 中。

反向取 $z\in\ker_{\mathbb Z}A$。强连通性使每条边都位于一个有向闭走法中；将每条边所选闭走法的计数相加，得到
$c\in\mathbb Z_{>0}^s$，满足 $\mathsf Dc=0$。取整数 $k$ 充分大，使
$kc$ 和 $kc+z$ 每个坐标均严格为正。两份边重数都在每个顶点入出平衡，且包含全部原图边，因而各自有从同一指定顶点开始的有向 Euler 回路。其总长度相等，计数差恰为 $z$，证明第一式；施以 $G$ 即得第二式。

强连通图的关联矩阵秩为 $m-1$。向量 $\mathbf1^{\mathsf T}$ 不在
$\mathsf D$ 的行空间中：它在正循环计数 $c$ 上取正值，而
$\mathsf D$ 的每行在 $c$ 上均为零。所以 $\operatorname{rank}A=m$。
整数矩阵的有理核实张成其全部实核，给有理基清分母可得
$\operatorname{span}_{\mathbb R}\ker_{\mathbb Z}A=\ker_{\mathbb R}A$。于是

$$
\operatorname{rank}\Lambda
=\operatorname{rank}_{\mathbb R}(G|_{\ker_{\mathbb R}A})
=\operatorname{rank}_{\mathbb R}\begin{pmatrix}A\\G\end{pmatrix}
-\operatorname{rank}_{\mathbb R}A,
\tag{32.4}
$$

得到（32.3）。证明完毕。

这一表示既保留整数格，也消去了遍历全部路径的定义。实秩只给商维数；
$\Lambda$ 的完整整数结构还决定 $\mathcal H=\Lambda^\perp$ 的有限连通分支，不能以未校验的浮点核代替整数格。

**推论32.2（每条边各有独立相位）。** 若 $q=s$、$G=I_s$，则

$$
r=s-m,\qquad
\mathcal H=
\{h_e=\omega+\phi_{\mathrm s(e)}-\phi_{\mathrm t(e)}
       \pmod{2\pi}\}.
\tag{32.5}
$$

此时 $\mathcal H$ 是连通环面的连续像，因而连通。若进一步 $P$ primitive，取
$\Theta=\mathbb T^s$，则每个固定 $0<\epsilon<1$ 有

$$
k_n^{(\epsilon)}(\mathbb T^s)
\asymp_{P,\epsilon} n^{(s-m)/2}.
\tag{32.6}
$$

取第31节的缓变平方可和预算，同一套与未来终端无关的在线门也有增长指数
$(s-m)/2$；此处保留该预算的慢变开销，不对任意平方可和预算断言同一指数。

证明。格秩由（32.3）给出。规范群的表达式就是（31.5），是
$(\omega,\phi_1,\ldots,\phi_m)\in\mathbb T^{m+1}$ 的连续群像。维数
$s-m$ 的固定紧平坦环面在小尺度 $\delta$ 的分离数为
$\Theta(\delta^{-(s-m)})$；将其用于定理31.6和推论31.8即可。证明完毕。

两态四边均正、边顺序为 $00,01,10,11$ 时，循环差格的一组整数基是

$$
(1,0,0,-1),\qquad(-2,1,1,0).
\tag{32.7}
$$

所以 $r=2$，可取商相位坐标

$$
\theta_{00}-\theta_{11},\qquad
\theta_{01}+\theta_{10}-2\theta_{00}.
\tag{32.8}
$$

固定误差容量是 $\Theta(n)$。若两态图只有 $00,01,10$ 三边且转移
primitive，则 $r=1$，格基为 $(-2,1,1)$，有效相位为
$\theta_{01}+\theta_{10}-2\theta_{00}$。这些都是完整边标签模型的实例，不能凭相同指数与前文另一来源等同。

**定理32.3（全相位精确容量及其在线实现）。** 对 $n\ge1$ 和端点 $i,j$，记
$C_n(i,j)\subseteq\mathbb Z^q$ 为所有 $n$ 步支持路径 $i\to j$ 的总荷集合，并置

$$
N_n=\sum_{i,j}|C_n(i,j)|,\qquad N_0=1.
\tag{32.9}
$$

在定义31.1的任意参考、任意初始活动记忆与完整联合恢复合同下，

$$
\boxed{k_n^{(0)}(\mathbb T^q)=N_n.}
\tag{32.10}
$$

同一列与未来终端无关的时变在线接收门，在每个时刻 $n$ 精确使用
$N_n$ 维记忆即可实现，不需要另加失败旗标。

证明。先写共同档案支撑，再证明任意共同编解码都受此支撑的维数下界。
对路径 $\gamma=(i_0,\ldots,i_n)$，记

$$
p(\gamma)=\prod_{t=1}^nP_{i_{t-1}i_t},\qquad
|\gamma\rangle=
|i_0,i_1\rangle\otimes\cdots\otimes|i_{n-1},i_n\rangle.
\tag{32.11}
$$

对每个可达三元组 $(i,j,c)$ 定义

$$
b_{ijc}=
\sum_{\substack{\gamma:i\to j,\ |\gamma|=n\\g(\gamma)=c}}
\sqrt{p(\gamma)}\,|\gamma\rangle,
\qquad
\chi_{ij}^{(n)}(\theta)
=\sum_{c\in C_n(i,j)}e^{i\theta\cdot c}b_{ijc}.
\tag{32.12}
$$

所有 $b_{ijc}$ 非零，不同三元组的路径集合不交，所以它们两两正交。
$n\ge1$ 时，完整边标签同时记录初始及终止顶点；不同端点扇区也正交。
对每个固定相位，全部初始输入在档案侧的支撑是

$$
S_n(\theta)=
\operatorname{span}\{\chi_{ij}^{(n)}(\theta):C_n(i,j)\ne\varnothing\}.
\tag{32.13}
$$

不同整数荷给出的环面字符线性无关。等价地，对固定 $i,j,c$，

$$
b_{ijc}=\frac1{(2\pi)^q}
\int_{\mathbb T^q}e^{-i\theta\cdot c}\chi_{ij}^{(n)}(\theta)\,d\theta.
\tag{32.14}
$$

有限维子空间对积分封闭，因此

$$
W_n:=\operatorname{span}_{\theta\in\mathbb T^q}S_n(\theta)
=\operatorname{span}\{b_{ijc}\},\qquad \dim W_n=N_n.
\tag{32.15}
$$

支撑计数尚不足以单独证明最小物理维数。设共同编码、解码通过
$D$ 维寄存器，恢复通道为 $\mathcal R=\mathcal D_n\mathcal E_n$。
以 $m$ 维参考 $J$ 和归一化 Bell 初态
$m^{-1/2}\sum_i|i\rangle_J|i\rangle_M$ 测试合同，得到纯联合态

$$
|\Psi_{\theta,n}\rangle
=\frac1{\sqrt m}\sum_{i,j}|i\rangle_J
 \otimes\chi_{ij}^{(n)}(\theta)\otimes|j\rangle_M.
\tag{32.16}
$$

它在档案侧的 Schmidt 支撑正是 $S_n(\theta)$。精确保持这个完整纯态，逐项比较参考—活动记忆的矩阵元，即得
$\mathcal R(X)=X$ 对每个 $X\in\mathcal L(S_n(\theta))$ 成立。

取恢复通道的一个固定 Stinespring 等距
$U:H_n\to H_n\otimes E$。纯态不扰动使它在每个
$S_n(\theta)$ 上形为

$$
Ux=x\otimes e_\theta\quad(x\in S_n(\theta)),\qquad
\|e_\theta\|=1.
\tag{32.17}
$$

这里同一支撑内的环境向量相同：先对一组正交基的纯态使用纯输出，再对任意两基向量的叠加或其非对角矩阵元使用
$\mathcal R=\operatorname{id}$，就强制环境向量一致。

固定 $\theta$，选任意非空端点扇区 $(i,j)$。向量
$\chi_{ij}^{(n)}(\theta)$ 非零且连续，所以当 $\varphi$ 位于 $\theta$ 的某邻域时

$$
\langle\chi_{ij}^{(n)}(\theta),\chi_{ij}^{(n)}(\varphi)\rangle\ne0.
\tag{32.18}
$$

由 $U$ 保持内积和（32.17），该内积等于其自身乘上
$\langle e_\theta,e_\varphi\rangle$，故
$\langle e_\theta,e_\varphi\rangle=1$，即 $e_\theta=e_\varphi$。
环境向量在连通环面上局部常值，因而全局相同。这里仅使用邻近相位的交叠，不要求任意远隔相位的支撑非正交。

线性性于是给 $Uw=w\otimes e$ 对全部 $w\in W_n$ 成立。因此
$\mathcal R$ 在整个 $\mathcal L(W_n)$ 上恒等，编码
$\mathcal E_n$ 在这个算子空间上单射。比较复线性维数得到

$$
N_n^2=\dim_{\mathbb C}\mathcal L(W_n)
\le \dim_{\mathbb C}\mathcal L(\mathbb C^D)=D^2,
\quad\text{故 }D\ge N_n.
\tag{32.19}
$$

上界可将 $W_n$ 等距编码，并在正交补上作任意 CPTP 完成。下面的在线实现同时给出各终端的上界。

令 $W_0=K_0=\mathbb C$。由（31.31）的端点递推，对每个相位都有
$S_{n+1}(\theta)\subseteq S_n(\theta)\otimes B$，因此

$$
W_{n+1}\subseteq W_n\otimes B.
\tag{32.20}
$$

取 $K_n=\mathbb C^{N_n}$、$F_n:W_n\to K_n$ 为满射等距，将
$F_n$ 在 $W_n^\perp$ 上以零延拓。设 $\Pi_n$ 为 $W_n$ 的正交投影，
$F_0=\Pi_0=I$，则
$`F_n^*F_n=\Pi_n`$、$`F_nF_n^*=I_{K_n}`$。在整个输入载体上定义

$$
\begin{aligned}
L_n&=F_n\Pi_n(F_{n-1}^*\otimes I_B),\\
\mathcal C_n(X)
&=L_nXL_n^*
+\operatorname{Tr}[(I-L_n^*L_n)X]\,\tau_n,
\end{aligned}
\tag{32.21}
$$

其中 $\tau_n$ 是 $K_n$ 内任一预定密度矩阵。前缀包含（32.20）保证
$`L_n^*L_n`$ 为投影，所以（32.21）是全域 CPTP 映射；$L_n$ 在可达支撑上等距，在其正交补上为零。实际来源对全部相位和参考输入都落在可达支撑内，补分支概率恒为零。故解码

$$
\mathcal D_n(Y)=F_n^*YF_n
\tag{32.22}
$$

保迹并精确恢复。所有门只依赖当前编号，无需知道未来终端。它们没有要求从整个
$K_{n-1}\otimes B$ 到 $K_n$ 存在无环境等距；所需的是可达支撑上的部分等距及全域通道完成。证明完毕。

上述必要性还适用于其他连通候选参数空间：只要档案支撑向量随参数连续、始终至少有一个非零向量，共同 Stinespring 环境同样由局部非零交叠强制为全局常量。因此，精确容量等于该连通族的共同档案支撑维数。下文的闭区间候选弧直接使用这一步，不预设能够制备不同参数值的叠加输入。

**定理32.4（精确与固定正误差的全环面增长阶）。** 对 primitive
$P$，令 $r=\operatorname{rank}G(\ker_{\mathbb Z}A)$。当 $n\to\infty$ 时，

$$
N_n\asymp_{P,g}n^r.
\tag{32.23}
$$

所以对每个固定 $0<\epsilon<1$，

$$
\boxed{
k_n^{(0)}(\mathbb T^q)\asymp_{P,g}n^r,\qquad
k_n^{(\epsilon)}(\mathbb T^q)
\asymp_{P,g,\epsilon}n^{r/2}.
}
\tag{32.24}
$$

证明。先作上界。固定端点 $i,j$ 后，任意两个 $n$ 步路径的计数差在
$\ker_{\mathbb Z}A$，所以相应荷差落在维数 $r$ 的实空间
$G(\ker_{\mathbb R}A)$。每个荷的范数不超过
$n\max_e\|g_e\|$，不同整数荷的欧氏距离至少为一。因此
$C_n(i,j)$ 是一个 $r$ 维仿射子空间内、半径 $O(n)$ 球中的一分离集。
以半径 $1/3$ 的互不交小球比较该仿射空间的体积，得到
$|C_n(i,j)|=O(n^r)$。再对最多 $m^2$ 个端点对求和。若 $r=0$，每个非空扇区只有一个荷，结论同样成立。

下界须产生实际可实现的荷，不能只数实仿射切片。取引理32.1中的严格正整数循环计数 $c$，置 $L=\mathbf1^{\mathsf T}c>0$。固定顶点
$i$。primitive 性给整数 $N$，使每个长度 $t\ge N$ 都有
$i\to i$ 支持闭走法。对 $t=N,\ldots,N+L-1$ 各选一份闭走法计数
$r_t$。当 $n\ge N$ 时，令

$$
k=\left\lfloor\frac{n-N}{L}\right\rfloor,\qquad
t=n-kL\in\{N,\ldots,N+L-1\},\qquad
q_n=kc+r_t.
\tag{32.25}
$$

它满足 $\mathsf Dq_n=0$、$\mathbf1^{\mathsf T}q_n=n$，且对所有充分大的
$n$，每条边都有 $(q_n)_e\ge\kappa n$，其中 $\kappa>0$ 是固定常数。

从整数核中选 $z_1,\ldots,z_r$，使
$Gz_1,\ldots,Gz_r$ 实线性无关；（32.4）保证可选。取足够小的固定
$\delta>0$，则对所有整数系数 $|\ell_a|\le\delta n$，向量

$$
q_n+\sum_{a=1}^r\ell_a z_a
\tag{32.26}
$$

每个坐标均严格为正，仍平衡且总长为 $n$。其支持包含原图全部边，故由
Euler 回路实现为从 $i$ 开始的 $n$ 步闭走法。线性无关性使不同
$(\ell_1,\ldots,\ell_r)$ 给不同总荷，于是

$$
|C_n(i,i)|\ge(2\lfloor\delta n\rfloor+1)^r
=\Omega(n^r).
\tag{32.27}
$$

$r=0$ 时用一条实际路径即可。上下界给（32.23）。精确容量由定理32.3给出；固定正误差容量由商环面的 $r$ 维分离数与定理31.6给出。证明完毕。

零误差侧区分全部相干字符，固定正误差侧的有效分辨尺度为
$n^{-1/2}$；同一商维数控制两侧，但增长指数相差一倍。这是对具体边标签模型及完整联合合同的结论。

**命题32.5（两态四边独立相位的精确有限值）。** 取两态四边转移全部正，
$g_{00},g_{01},g_{10},g_{11}$ 为 $\mathbb Z^4$ 标准基。则对每个
$n\ge1$，

$$
\boxed{
N_n=n^2+n+2,\qquad
k_n^{(0)}(\mathbb T^4)=n^2+n+2.
}
\tag{32.28}
$$

固定 $0<\epsilon<1$ 时仍有
$k_n^{(\epsilon)}(\mathbb T^4)\asymp_{P,\epsilon}n$。

证明。路径计数写作 $(a,b,c,d)$，分别对应 $00,01,10,11$。
$01$ 端点扇区满足 $b=c+1$。置 $c=t\ge0$ 后，
$a+d=n-2t-1$；每个这样的非负计数都能通过交替跨边、在访问顶点插入自环实现。因此

$$
|C_n(0,1)|
=\sum_{t=0}^{\lfloor(n-1)/2\rfloor}(n-2t),
\qquad |C_n(1,0)|=|C_n(0,1)|.
\tag{32.29}
$$

$00$ 端点扇区满足 $b=c=t$。若 $t=0$，路径只能是全部 $00$ 自环，贡献一个计数；若 $t\ge1$，两态均已访问，任意
$a,d\ge0$、$a+d=n-2t$ 都可实现。所以

$$
|C_n(0,0)|
=1+\sum_{t=1}^{\lfloor n/2\rfloor}(n-2t+1),
\qquad |C_n(1,1)|=|C_n(0,0)|.
\tag{32.30}
$$

分别代入 $n=2k$ 和 $n=2k+1$ 求和，均得
$2|C_n(0,1)|+2|C_n(0,0)|=n^2+n+2$。
精确值由定理32.3给出，正误差阶由 $r=2$ 的定理32.4给出。证明完毕。

**命题32.6（相同一维商几何，不同精确容量指数）。** 在命题32.5的同一来源中，固定
$\alpha\in\mathbb R$，取足够小的固定 $L>0$，令候选相位仅为

$$
\Theta_\alpha=
\{(\theta_{00},\theta_{01},\theta_{10},\theta_{11})
=(0,0,\alpha t,t):0\le t\le L\}.
\tag{32.31}
$$

若 $\alpha$ 无理，则

$$
k_n^{(0)}(\Theta_\alpha)=n^2+n+2
\quad(n\ge1).
\tag{32.32}
$$

若 $\alpha=p/q$、$p\in\mathbb Z$、$q\in\mathbb Z_{>0}$，则

$$
k_n^{(0)}(\Theta_{p/q})\asymp_{p,q}n.
\tag{32.33}
$$

两种情形下，商候选弧的盒维数都是一；对每个固定 $0<\epsilon<1$，

$$
\boxed{
k_n^{(\epsilon)}(\Theta_\alpha)
\asymp_{P,\alpha,L,\epsilon}\sqrt n.
}
\tag{32.34}
$$

证明。固定端点 $i,j\in\{0,1\}$ 和长度 $n$，路径计数满足
$b-c=j-i$、$a+b+c+d=n$，故 $(c,d)$ 唯一决定全部计数。沿候选弧，相位字符成为

$$
e^{i(\alpha c+d)t}.
\tag{32.35}
$$

无理性使不同整数对 $(c,d)$ 的频率 $\alpha c+d$ 不同。有限个不同实频率的指数函数在任意非退化实区间上线性无关：若其线性组合恒为零，于区间内一点取从零到频率总数减一阶的导数，所得矩阵是乘以非零对角因子的 Vandermonde 矩阵，其行列式是非零频率差的乘积。因此，每个端点扇区按完整四边计数合成的全部向量
$b_{ij,(a,b,c,d)}$ 仍被这条候选弧张满，共同档案支撑与完整四相位环面相同。

候选闭区间连通，支撑向量连续；定理32.3的局部交叠论证强制共同恢复通道在整个共同支撑上恒等。命题32.5给其维数
$n^2+n+2$，故得到（32.32）。这个必要性来自逐参数的精确恢复合同，不增加相位叠加输入要求。

若 $\alpha=p/q$，频率变成 $(pc+qd)/q$。由于 $0\le c,d\le n$，每个端点扇区至多有 $O_{p,q}(n)$ 个不同频率。将同频率的全部路径振幅合成一个非零向量后，不同频率组仍有不交的路径支撑；上面的指数独立性及连通交叠证明使精确容量等于各端点扇区不同频率数之和。下界在
$01$ 扇区取

$$
c=0,\quad b=1,\quad d=0,\ldots,n-1,\quad a=n-1-d.
\tag{32.36}
$$

这些计数分别由先走 $00$ 自环、再过 $01$、最后走 $11$ 自环实现，给出
$n$ 个不同频率 $d$。这证明（32.33）。

最后，（32.8）的商坐标将整条候选弧映成 $(-t,\alpha t)$。
这些整数坐标来自循环差格的完整基，诱导商环面与 $\mathbb T^2$ 的同构。在足够小的固定坐标片中，商的平坦距离与这些坐标的欧氏距离双侧等价；方向
$(-1,\alpha)$ 非零，所以存在 $0<c_\alpha\le C_\alpha<\infty$，使

$$
c_\alpha|t-t'|
\le d_{\mathcal Q}([\theta(t)],[\theta(t')])
\le C_\alpha|t-t'|\quad(0\le t,t'\le L).
\tag{32.37}
$$

由此
$\operatorname{Pack}(\Gamma_\alpha,\delta)
\asymp_{\alpha,L}\delta^{-1}$，定理31.6即给（32.34）。证明完毕。

这个对照表明，精确容量指数不由候选集的商盒维数单独决定。无理性仅用于有限频率集合的严格单射；证明没有使用任何丢番图逼近速率。Vandermonde 论证只确定代数秩，不给稳定数值反演或门描述复杂度，也不声称可以通过有限测量精确认定某参数无理。

本节的 Euler 回路、整数循环格、字符独立性与共同 Stinespring 机制是所用的标准中间工具。新增推导给出第31节具体来源的可达荷容量、精确在线实现及有理／无理候选弧对照；这些是普通数学结果，未在 Lean 中形式化，也不作外部原创优先权主张。

## 追加锚（本行以下为增补区）

## 33. 相干长度把整体相位变成边界必须保留的关系

固定终端的整体相位不改变目标密度矩阵；把不同长度保持为同一档案中的相干分量后，这些相位可以产生可见的相对关系。本节在第31—32节的完整边标签来源上证明这一改变的容量代价。新来源明确固定各长度间的相对相位；它不能仅由各固定长度通道的等价类唯一指定。

本节采用单终端块编码合同。它没有把不同终端的独立协议自动拼成相干协议，也不提供该来源的在线生成、固定接收门或物理钟标定成本。其结论不改判第29—30节的六维固定接收器问题。

**定义33.1（相干长度来源与完整联合恢复）。**

固定有限 $m$ 态 primitive 行随机矩阵 $P$，其支持图有 $s$ 条边。每条支持边有独立相位，$\theta\in\mathbb T^s$。将第31节的完整边标签累计等距作固定张量因子重排，把活动记忆写在前方，记为
$$
T_{\theta,n}:M\longrightarrow M\otimes B^{\otimes n}.
$$
取整数 $N\ge1$、$1\le W\le N+1$，置
$$
\mathcal I_{N,W}=\{N,\ldots,N+W-1\},\qquad
\mathcal A_{N,W}=\bigoplus_{n\in\mathcal I_{N,W}}B^{\otimes n}.
$$
令 $\iota_n$ 为长度层的等距嵌入，定义新的相干来源
$$
\mathcal T_{\theta;N,W}
=\frac1{\sqrt W}\sum_{n\in\mathcal I_{N,W}}
(I_M\otimes\iota_n)T_{\theta,n}.
\tag{33.1}
$$
各长度层正交，所以 $\mathcal T_{\theta;N,W}^*\mathcal T_{\theta;N,W}=I_M$。式 （33.1） 是等距叠加，输出保留不同长度之间的相干项。长度标签属于待恢复档案 $\mathcal A_{N,W}$，不是免费经典旁信息。

初始 $M$ 输入任意，允许与任意不可访问参考纠缠。编码 $\mathcal E:\mathcal L(\mathcal A_{N,W})\to\mathcal L(K)$ 和解码 $\mathcal D:\mathcal L(K)\to\mathcal L(\mathcal A_{N,W})$ 只作用于档案或接收寄存器，不访问参考、活动记忆。它们共同固定，不能依赖实际 $\theta$，但可依赖已知 $P,N,W,\epsilon$。记完整联合恢复半迹误差至多 $\epsilon$ 所需的最小 $\dim K$ 为 $k_{N,W}^{\epsilon,\mathrm{coh}}$。

令 $D$ 为支持图关联矩阵、$A=[D;\mathbf1^T]$，并置
$$
r=s-m=\dim\ker_{\mathbb R}A.
$$
这里支持图来自行随机矩阵，非空；primitive 性保证所用的强连通与统一长度结论。

**定理33.2（相干长度窗口的精确与近似容量）。** 设 $N_n=\sum_{i,j}|\mathcal C_n(i,j)|$，其中 $\mathcal C_n(i,j)$ 为长度 $n$、端点 $i,j$ 的可达完整边计数集合。则对全部 $N\ge1$、$1\le W\le N+1$，
$$
k_{N,W}^{0,\mathrm{coh}}
=\sum_{n=N}^{N+W-1}N_n.
\tag{33.2}
$$
对每个固定 $0<\epsilon<1$，有统一于全部 $1\le W\le N+1$ 的渐近界
$$
\boxed{
k_{N,W}^{0,\mathrm{coh}}\asymp_P WN^r,
\qquad
k_{N,W}^{\epsilon,\mathrm{coh}}\asymp_{P,\epsilon} WN^{r/2}.
}
\tag{33.3}
$$
即存在只依赖所列固定参数的正上下常数和阈值 $N_0$，对全部 $N\ge N_0$ 及该范围内每个 $W$ 同时成立。

**精确共同支撑与最小物理维数。**

对可达计数 $c\in\mathbb Z_{\ge0}^s$，将同一长度、端点和计数的所有路径振幅合为
$$
b_{n,ij,c}
=\sum_{\substack{\gamma:i\to j,\ |\gamma|=n\\c(\gamma)=c}}
\sqrt{\prod_{e\in\gamma}P_e}\,|n,\gamma\rangle.
\tag{33.4}
$$
每个向量非零，且不同 $(n,i,j,c)$ 的向量正交。独立边相位使其字符为 $e^{i\theta\cdot c}$。因为 $\mathbf1^Tc=n$，不同长度也不可能产生相同完整计数。

已知 $\theta$ 时，档案 Schmidt 支撑由各端点向量
$$
\chi_{ij}(\theta)=\frac1{\sqrt W}
\sum_{n\in\mathcal I_{N,W}}\sum_{c\in\mathcal C_n(i,j)}
e^{i\theta\cdot c}b_{n,ij,c}
\tag{33.5}
$$
张成。这里每个 $\chi_{ij}$ 本身包含跨长度相干。完整边标签与 $N\ge1$ 使不同端点扇区正交；对 $m$ 维 Bell 参考输入，这些非零向量正是档案侧的 Schmidt 支撑。

不同整数计数给出不同环面字符，故 $\theta$ 遍历整个 $\mathbb T^s$ 时，（33.5） 在每个端点扇区张满全部 $b_{n,ij,c}$。共同支撑 $\mathcal W$ 的维数因而为 $\sum_nN_n$。

还必须证明共同物理编码不能低于这个维数。若同一恢复通道 $\mathcal D\circ\mathcal E$ 精确恢复全部完整纯目标，固定其 Stinespring 等距 $U_L$，则在每个已知相位 Schmidt 支撑上有 $U_Lx=x\otimes e_\theta$。任选非零端点向量，连续性使邻近相位的相应向量具有非零交叠；等距内积保持遂给 $e_\theta=e_\phi$。连通环面使这些环境向量全相同。线性性于是给 $U_Lw=w\otimes e$ 于整个 $\mathcal W$，所以恢复通道在 $\mathcal L(\mathcal W)$ 上恒等。

编码在这个 $(\dim\mathcal W)^2$ 维算子空间上必须单射，故 $\dim K\ge\dim\mathcal W$。反向对 $\mathcal W$ 作一个整体等距编码，并在正交补完成全域 CPTP 映射，即实现精确上界，证明 （33.2）。

定理32.4给出的完整边计数增长律 $N_n\asymp_P n^r$ 对每个充分大 $n$ 成立。由于窗口内 $N\le n\le2N$，其求和给 （33.3） 的精确侧，常数与 $W$ 无关。

**单个计数的统一概率上界。**

记
$$
p_{n,i,j}(c)=\|b_{n,ij,c}\|^2.
$$
这是以状态 $i$ 启动、长度 $n$ 后到 $j$ 并具有计数 $c$ 的经典路径概率。对独立边相位的矩阵
$M_\theta(i,j)=P_{ij}e^{i\theta_{ij}}$，有有限 Fourier 展开
$$
M_\theta^n(i,j)=\sum_c p_{n,i,j}(c)e^{i\theta\cdot c}.
$$
归一化 Haar 积分反演及引理31.3的全局有限步 Gaussian 界给
$$
\begin{aligned}
p_{n,i,j}(c)
&\le\int_{\mathbb T^s}|M_\theta^n(i,j)|\,d\theta\\
&\le C\int_{\mathbb T^s}e^{-c_0n d_H([\theta],0)^2}\,d\theta
\le C_0 n^{-r/2}.
\end{aligned}
\tag{33.6}
$$
最后一步将 Haar 测度推到维数 $r$ 的固定商环面；局部体积界控制 Gaussian 积分，远处由指数衰减控制。$r=0$ 时该积分为常数，仍是同一式。$C_0$ 统一于 $i,j,c,n$；取充分大 $n$ 已足够，也可增大常数覆盖全部 $n\ge1$。

**保留长度相干的近似下界。**

对 Bell 参考输入，完整纯目标可写为
$$
|\Psi_\theta\rangle=\sum_c e^{i\theta\cdot c}|\beta_c\rangle,
\qquad
|\beta_c\rangle=\frac1{\sqrt{mW}}
\sum_{i,j}|i\rangle_J|j\rangle_M\otimes b_{n,ij,c},
\quad n=\mathbf1^Tc\in\mathcal I_{N,W}.
\tag{33.7}
$$
不存在的端点计数项取零。不同 $c$ 的 $\beta_c$ 正交；同一计数允许把多个端点扇区相干地合在同一个 $\beta_c$ 中，不能把这些相同字符重复当成不同特征值。

对完整相位环面取 Haar 平均，得到
$$
\overline\rho=\int |\Psi_\theta\rangle\langle\Psi_\theta|\,d\theta
=\sum_c|\beta_c\rangle\langle\beta_c|.
$$
由 （33.6）、$n\ge N$，
$$
\|\overline\rho\|
=\max_c\frac1{mW}\sum_{i,j}p_{n,i,j}(c)
\le\frac{C_1}{WN^{r/2}}.
\tag{33.8}
$$
例如取 $C_1=mC_0$ 即可。

设共同编码维数为 $D_K$，共同解码为 $\mathcal D$，令 $\tau=\mathcal D(I_K)$，则 $\operatorname{Tr}\tau=D_K$。每个编码后的联合密度矩阵不超过 $I_{JM}\otimes I_K$，所以恢复态不超过 $I_{JM}\otimes\tau$。半迹误差至多 $\epsilon$ 给每个纯目标的恢复重叠至少 $1-\epsilon$。取 Haar 平均并用 （33.8），
$$
1-\epsilon
\le\operatorname{Tr}[\overline\rho(I_{JM}\otimes\tau)]
\le\frac{C_1m^2D_K}{WN^{r/2}}.
\tag{33.9}
$$
这证明 $D_K\ge(1-\epsilon)WN^{r/2}/(C_1m^2)$。这里从未测量长度；Haar 平均只用于对未知参数族作必要性证明。

**一个整体成功算子的近似上界。**

令 $\pi$ 为平稳分布，$\mu_e=\pi_iP_{ij}$ 为边 $e=(i,j)$ 的平稳频率。Markov 混合的二阶矩估计给某个只依赖 $P$ 的 $C_2>0$，使全部初始状态 $i$ 都满足
$$
\mathbb E_i\|c(X_0,\ldots,X_n)-n\mu\|^2\le C_2n.
\tag{33.10}
$$
例如可对引理31.4的历史扰动估计的每个边坐标取常量实测试向量，再把 $s$ 个平方界相加，取 $C_2=sC_{\rm hist}$。该二阶矩界包含非平稳初始状态的均值偏移。

取 $R=2\sqrt{C_2}/\epsilon$。在每个长度层只保留满足
$$
\|c-n\mu\|\le R\sqrt N
\tag{33.11}
$$
的可达向量 $b_{n,ij,c}$，令 $\mathcal W_{\rm good}$ 为所有长度、端点和这些计数向量的**整体线性张成**，$P_{\rm good}$ 为其正交投影。由 （33.10）、$n\le2N$ 和 Markov 不等式，每个初始状态在每个长度层的漏出概率至多
$2C_2/R^2=\epsilon^2/2$。对相干来源，各长度层正交，故总漏出概率是这些数的等权平均；没有为了计算该范数而实施长度测量。

不同初始状态的档案位于不同首边标签扇区，$P_{\rm good}$ 保持这些扇区。因此误差输入算子没有交叉项，严格有
$$
\mathcal T_{\theta;N,W}^*
[I_M\otimes(I-P_{\rm good})]
\mathcal T_{\theta;N,W}
\preceq\frac{\epsilon^2}{2}I_M.
\tag{33.12}
$$
该界对全部相位相同，并可张量任意参考。

对固定 $n,i,j$，所有可达计数满足
$$
Dc=e_j-e_i,\qquad\mathbf1^Tc=n.
$$
它们处于一个 $r$ 维仿射空间中，且相异整数计数的间距至少一。将半径 $R\sqrt N$ 的球与该仿射空间相交，再用半径 $1/3$ 的不交球比较，可得该层保留的计数个数至多
$(3R\sqrt N+1)^r$；空交集贡献零，$r=0$ 时最多一个。于是
$$
\dim\mathcal W_{\rm good}
\le m^2W(3R+1)^rN^{r/2}.
\tag{33.13}
$$

取等距 $F:\mathcal W_{\rm good}\to K_{\rm good}$，并加一维旗标。用**一个**成功 Kraus 算子 $FP_{\rm good}$ 定义全域通道
$$
\mathcal E(X)=FP_{\rm good}XP_{\rm good}F^*
+\operatorname{Tr}[(I-P_{\rm good})X]|\perp\rangle\langle\perp|.
\tag{33.14}
$$
将 $F$ 在所选子空间的正交补上以零延拓。对任意固定档案态 $\tau$，解码明确取为

$$
\mathcal D(Y)=F^*YF+\langle\perp|Y|\perp\rangle\tau.
$$

它在整个接收寄存器上完全正且保迹。特别地，若 $P_n$ 表示选中子空间在长度 $n$ 层的投影，（33.14） 的成功项包含全部
$FP_nXP_{n'}F^*$，包括 $n\ne n'$；所以成功分支保留跨长度相干。

对任意参考输入取纯化，令完整纯目标为 $|\Psi\rangle$、漏出质量为 $d\le\epsilon^2/2$。解码后的成功分支恰为
$P_{\rm good}|\Psi\rangle\langle\Psi|P_{\rm good}$，其目标重叠为 $(1-d)^2$；失败项为正。因此完整联合半迹误差至多
$$
\sqrt{1-(1-d)^2}\le\sqrt{2d}\le\epsilon.
$$
额外纯化参考可再偏迹丢弃。编码维数至多 （33.13） 加一，证明 （33.3） 的近似侧上界。所有常数与 $W$ 无关。

**跨长度相位及范围。**

固定长度时，边相位的 scalar-plus-coboundary 方向
$h_{ij}=\omega+\phi_i-\phi_j$ 沿路径只留下
$e^{in\omega}e^{i\phi_i-i\phi_j}$。在 （33.1） 中，$e^{in\omega}$ 随长度层变化；当 $W\ge2$ 时，它一般改变档案不同长度分量之间的相对相位，不能再作为整个目标的一个共同标量删去。

容量中的因子 $W$ 来自这个明确保留长度相干的合同：精确侧不同长度具有不同完整计数字符，近似侧平均态的特征值带 $1/W$，上界则整体编码全部选中长度扇区。$W=1$ 恢复固定长度结果；$W=N+1$ 给
$$
k_{N,N+1}^{0,\mathrm{coh}}\asymp_P N^{r+1},\qquad
k_{N,N+1}^{\epsilon,\mathrm{coh}}\asymp_{P,\epsilon}N^{1+r/2}.
$$
这只证明新相干来源的单终端块编码容量；没有给出一套固定门、未知未来终端协议、长度测量协议或额外时钟实现成本的结论。本节复用第31—32节已注明来源的字符独立、Markov 混合和 Fourier 反演等标准工具；相干窗口容量由此处的完整联合恢复推导给出，不作外部原创优先权或 Lean 验证主张。


**推论33.3（一个纯相位钟与去相干目标的容量差别）。** 取单状态单边来源 $P=[1]$，故 $m=s=1$、$r=0$。每个长度层只含一条路径，记为 $|n\rangle$。完整相干来源成为

$$
|c_\theta\rangle=\frac1{\sqrt W}
\sum_{n=N}^{N+W-1}e^{in\theta}|n\rangle,
\qquad\theta\in\mathbb T.
\tag{33.15}
$$

对 $0\le\epsilon<1$，在相同的未知相位共同编解码合同下，

$$
\boxed{
k_{N,W}^{0,\mathrm{coh}}=W,\qquad
(1-\epsilon)W\le k_{N,W}^{\epsilon,\mathrm{coh}}\le W.
}
\tag{33.16}
$$

如果将来源替换为在长度分解上完全去相干后的族，则输出为

$$
\rho^{\mathrm{deph}}_\theta
=\frac1W\sum_{n=N}^{N+W-1}|n\rangle\langle n|,
\tag{33.17}
$$

与 $\theta$ 无关，其精确最小接收维数是一。

证明。取 $\theta_j=2\pi j/W$、$j=0,\ldots,W-1$。有限等比和给
$\langle c_{\theta_j}|c_{\theta_k}\rangle=\delta_{jk}$，故这 $W$ 个态构成 $W$ 维档案空间的正交基。

设共同解码为 $\mathcal D$、接收维数为 $D$，置 $\tau=\mathcal D(I_D)$，则 $\operatorname{Tr}\tau=D$。每个编码密度矩阵不超过 $I_D$，恢复态因而不超过 $\tau$。误差不超过 $\epsilon$ 使每个目标投影的恢复概率至少为 $1-\epsilon$；对这组正交目标求和，得到

$$
W(1-\epsilon)
\le\sum_{j=0}^{W-1}\langle c_{\theta_j}|\tau|c_{\theta_j}\rangle
=\operatorname{Tr}\tau=D.
$$

整个档案空间的恒等编码给 $D=W$ 上界，$\epsilon=0$ 时两者相等。去相干后全族只有一份已知态，编码可以输出固定的一维态，解码重新准备（33.17），从而精确恢复。任何非空接收空间至少一维，故一维最优。证明完毕。

这里去相干是更换来源及恢复目标；在原合同中测量长度会破坏需要恢复的相干项，不能据此获得一维方案。也没有把未知相位称为已校准物理时间。这个例子确定的是：同一组长度标签，是否保留它们之间的相位关系，会改变必要的边界容量。

## 追加锚（本行以下为增补区）


## 34. 六维五终端接收排除三条互异尾环境射线

本节回到第29—30节的固定接收通道问题。来源仍为
$m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，其中
$ab\ne0$、$|a|^2+|b|^2=1$。接收器从独立纯态启动，所有持久系统都计入六维
$K$，每轮使用同一个全域 CPTP 通道，新环境随即丢弃且不再访问；接收器不能访问活动记忆或参考，须精确恢复前五个完整参考终端。

命题29.1和29.2已将任何这样的候选归约到五个终端全部为纯的联合编码，每轮新环境为输入无关的单位向量
$\eta_n$。命题30.1又给
$\dim\operatorname{span}\{\eta_3,\eta_4,\eta_5\}=2$。
本节证明，这三个尾环境不能占据三条互异射线。因此只保留两条不同尾射线的
AAB、ABA、ABB 三种模式；字母相同表示射线相同，字母不同不预设正交。本节不决定这些两射线模式的可行性。

固定共同 Stinespring 等距
$V:K\otimes B\to K\otimes E$，令
$V_i x=V(x\otimes|i\rangle)$。原始环境 $E$ 的维数不受预先限制，也不假定
$V_1(K)$ 已落在二维环境中。沿用（30.1）—（30.4）的正交单位向量
$p,q$ 和正交单位向量 $u,v,w$，以及初态 $k$：

$$
\begin{gathered}
V_0k=p\otimes\eta_1,\qquad V_1k=q\otimes\eta_1,\\
V_0p=u\otimes\eta_2,\qquad V_1p=v\otimes\eta_2,
\qquad V_0q=w\otimes\eta_2,\\
H_1=\operatorname{span}\{p,q\},\qquad
G_2=\operatorname{span}\{u,w\},\qquad
H_2=\operatorname{span}\{a^2u+bv,w\}.
\end{gathered}
\tag{34.1}
$$

对于 $n=3,4,5$，（30.5）—（30.7）给出二维空间
$H_n,G_n,Q_n$，满足

$$
\begin{gathered}
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n,\\
G_n\perp Q_n,\qquad H_n\subseteq G_n\oplus Q_n,\qquad
P_{G_n}H_n=G_n,\quad P_{Q_n}H_n=Q_n.
\end{gathered}
\tag{34.2}
$$

最后两个投影在 $H_n$ 上都是同构。这是实际来源的非零系数及支撑秩所强制的关系，后文不会将
$H_n$ 换成任意二维空间。全节的内积对第一变量共轭线性、对第二变量线性。

**引理34.1（三条互异尾射线强制共同四加二维分解）。** 反设
$\eta_3,\eta_4,\eta_5$ 的射线两两不同，令
$F=\operatorname{span}\{\eta_3,\eta_4,\eta_5\}$，则 $\dim F=2$。
所有五个环境向量均属于 $F$，且存在正交分解
$K=S\oplus Q$，$\dim S=4$、$\dim Q=2$，满足

$$
\begin{gathered}
Q_3=Q_4=Q_5=Q,\qquad
S=G_3+G_4=G_2+G_3=G_2+G_4,\\
G_5\subseteq S,\qquad p\in S,\quad v\in Q,\qquad
V_0K\subseteq S\otimes F.
\end{gathered}
\tag{34.3}
$$

映射 $U:=V_1|_S:S\to Q\otimes F$ 为满等距，且

$$
U(G_2)=Q\otimes\eta_3,\qquad
U(G_3)=Q\otimes\eta_4,\qquad
U(G_4)=Q\otimes\eta_5.
\tag{34.4}
$$

三个尾环境还必须两两非正交：

$$
0<|\langle\eta_i,\eta_j\rangle|<1
\qquad(3\le i<j\le5).
\tag{34.5}
$$

证明。若 $x\in G_3\cap G_4$，固定 $V_1x$ 同时属于
$Q_4\otimes\eta_4$ 与 $Q_5\otimes\eta_5$。不同环境射线使这两个张量子空间相交为零；等距的单射性给
$G_3\cap G_4=0$。

以 $\eta_3,\eta_4$ 为 $F$ 的代数基，写
$\eta_5=\alpha\eta_3+\beta\eta_4$，其中 $\alpha\beta\ne0$。若

$$
x_3\otimes\eta_3+x_4\otimes\eta_4+x_5\otimes\eta_5=0,
\qquad x_j\in G_j,
$$

则环境坐标给 $x_3=-\alpha x_5$、$x_4=-\beta x_5$。所以
$x_5\in G_3\cap G_4=0$，三个向量均为零。由（34.2），这些像子空间全部包含于
$V_0K$，其维数和已达六，故

$$
V_0K=(G_3\otimes\eta_3)\dotplus
(G_4\otimes\eta_4)\dotplus(G_5\otimes\eta_5)
\subseteq K\otimes F.
\tag{34.6}
$$

此处 $\dotplus$ 是代数直和，不断言正交。又由（34.1），
$V_0H_1=G_2\otimes\eta_2$、$V_0k=p\otimes\eta_1$，其中接收器因子非零。
将环境投影到 $F^\perp$ 就得 $\eta_1,\eta_2\in F$。这一步只使用零位像的全域饱和。

二维复空间中的每条射线只有一条正交补射线；在三条不同射线中，至少有一条与另两条都非正交。选其编号
$j\in\{3,4,5\}$。固定 $V$ 的两个输入位像正交，故比较
$G_i\otimes\eta_i\subset V_0K$ 与 $Q_j\otimes\eta_j\subset V_1K$，得到
$Q_j\perp G_i$，对 $i=3,4,5$ 均成立。因此

$$
S:=G_3+G_4=Q_j^\perp,\qquad \dim S=4,
\qquad G_5\subseteq S.
\tag{34.7}
$$

由（34.6）有 $V_0K\subseteq S\otimes F$；再用早期纯张量像，得到
$G_2\subseteq S$、$p\in S$。

现在 $V_1(G_2+G_3+G_4)$ 等于

$$
(Q_3\otimes\eta_3)+(Q_4\otimes\eta_4)+(Q_5\otimes\eta_5).
$$

其维数恰为

$$
6-\dim(Q_3\cap Q_4\cap Q_5).
\tag{34.8}
$$

确切地说，从 $Q_3\oplus Q_4\oplus Q_5$ 到上述和空间的自然映射，其核是
$\{(-\alpha x,-\beta x,x):x\in Q_3\cap Q_4\cap Q_5\}$。
另一方面，输入包含于四维 $S$，所以（34.8）至多为四。这迫使三个二维
$Q_i$ 全部相等，记为 $Q$；（34.7）给 $K=S\oplus Q$。同时

$$
V_1S=V_1(G_3+G_4)
=Q\otimes\eta_4+Q\otimes\eta_5=Q\otimes F.
\tag{34.9}
$$

所以 $U=V_1|_S$ 为满等距，（34.4）成立，任意两个不同环境纤维的逆像张成
$S$。又因 $p\in S$、$V_1p=v\otimes\eta_2$，得到 $v\in Q$。

还须排除尾环境的正交对。若 $\eta_3\perp\eta_4$，由固定
$V_0,V_1$ 分别得 $H_2\perp H_3$、$G_2\perp G_3$。
此时 $H_3\subseteq G_3\oplus Q$，且 $P_QH_3=Q$，可取
$h\in H_3$ 使 $\langle v,h\rangle\ne0$。因为
$u\in G_2\subset S$，有 $u\perp H_3$，于是

$$
\langle a^2u+bv,h\rangle
=\bar b\langle v,h\rangle\ne0,
$$

违反 $H_2\perp H_3$。若 $\eta_3\perp\eta_5$，改用
$H_4\subseteq G_4\oplus Q$、$P_QH_4=Q$，同理违反 $H_2\perp H_4$。

若 $\eta_4\perp\eta_5$，则 $H_3\perp H_4$、$G_3\perp G_4$。
任取单位 $z\in Q$，用两个满投影选取 $h_3\in H_3$、$h_4\in H_4$，使
$P_Qh_3=P_Qh_4=z$。由 $S\perp Q$、$G_3\perp G_4$，

$$
\langle h_3,h_4\rangle=\langle z,z\rangle=1,
$$

又与 $H_3\perp H_4$ 矛盾。三个内积都非零；单位向量不共线给其绝对值严格小于一，证明完毕。

对任意单位 $\xi\in F$，下文记

$$
W_\xi:Q\to S,\qquad W_\xi z=U^{-1}(z\otimes\xi).
\qquad
W_\xi^*W_\zeta=\langle\xi,\zeta\rangle I_Q.
\tag{34.10}
$$

于是 $G_2,G_3,G_4$ 分别是 $W_{\eta_3},W_{\eta_4},W_{\eta_5}$ 的像，
$p=W_{\eta_2}v$。式（34.10）给出了这些二维子空间的完整交叠矩阵。

**引理34.2（早期矩形强制第四纤维和双线性约束）。** 在引理34.1的假设下，取代数基
$e_0=\eta_3$、$e_1=\eta_4$，写

$$
\eta_5=\alpha e_0+\beta e_1,\qquad
\eta_2=ce_0+de_1,\qquad
\alpha\beta\ne0,\quad(c,d)\ne(0,0).
\tag{34.11}
$$

定义辅助非零向量

$$
\eta_6=\alpha c e_0+(\beta c-\alpha d)e_1.
\tag{34.12}
$$

则

$$
U(G_5)=Q\otimes\mathbb C\eta_6,\qquad
(U\otimes I_F)V_0K=Q\otimes J,
\tag{34.13}
$$

其中

$$
J=\operatorname{span}\{
\eta_4\otimes\eta_3,\eta_5\otimes\eta_4,
\eta_6\otimes\eta_5\}\subset F\otimes F,
\qquad \dim J=3.
\tag{34.14}
$$

令 $\mathcal B:F\times F\to\mathbb C$ 为复双线性形式，其在
$e_0,e_1$ 基中的矩阵为

$$
[\mathcal B]=
\begin{pmatrix}d&-c\\0&\alpha c/\beta\end{pmatrix}.
\tag{34.15}
$$

它的线性延拓满足 $J=\ker\mathcal B$，并有

$$
\mathcal B(\eta_{j+1},\eta_j)=0,\qquad j=1,\ldots,5.
\tag{34.16}
$$

$\eta_6$ 只标记一个辅助纤维，不声称第六轮存在或具有这一环境。
$\mathcal B$ 是双线性形式，不是 Hilbert 内积；其消失值不表示环境正交。

证明。在零位像的接收器因子上作用 $U$，由（34.6）得到

$$
\begin{aligned}
(U\otimes I)V_0K
={}&Q\otimes(e_1\otimes e_0)
+Q\otimes((\alpha e_0+\beta e_1)\otimes e_1)\\
&+U(G_5)\otimes(\alpha e_0+\beta e_1).
\end{aligned}
\tag{34.17}
$$

前两个标量张量独立，张成二维空间 $L\subset F\otimes F$。定义满射
$\pi:F\otimes F\to\mathbb C^2$：

$$
\begin{aligned}
\pi(e_0\otimes e_0)&=(1,0),&
\pi(e_0\otimes e_1)&=(0,1),\\
\pi(e_1\otimes e_0)&=0,&
\pi(e_1\otimes e_1)&=(0,-\alpha/\beta).
\end{aligned}
\tag{34.18}
$$

其核恰为 $L$。对 $x=x_0\otimes e_0+x_1\otimes e_1\in Q\otimes F$，有

$$
(I_Q\otimes\pi)(x\otimes\eta_5)
=(\alpha x_0,\beta x_0-\alpha x_1).
\tag{34.19}
$$

右侧定义了 $Q\oplus Q$ 上的可逆线性变换 $T$，因为 $\alpha\ne0$。
故（34.17）在这个商中的像恰为二维空间 $T(U(G_5))$。

早期矩形 $V_0H_1=G_2\otimes\eta_2$ 也包含于 $V_0K$；在
$U$ 坐标下，它是 $Q\otimes e_0\otimes(ce_0+de_1)$，商像为
$\{(cz,dz):z\in Q\}$。此空间二维，故它与 $T(U(G_5))$ 相等。
解

$$
\alpha x_0=cz,\qquad \beta x_0-\alpha x_1=dz
$$

得
$x_0=(c/\alpha)z$、$x_1=((\beta c-\alpha d)/\alpha^2)z$，即（34.12）—（34.13）的第一式。
该辅助向量非零：$c\ne0$ 时其 $e_0$ 系数非零；$c=0$ 时
$d\ne0$，其 $e_1$ 系数为 $-\alpha d\ne0$。

代回（34.17）得像空间等式（34.13）。左侧维数六，$\dim Q=2$，所以
$\dim J=3$。早期矩形包含进一步给
$\eta_3\otimes\eta_2\in J$。而由（34.1）、（34.10），

$$
(U\otimes I)V_0k=v\otimes\eta_2\otimes\eta_1\in Q\otimes J,
$$

由于 $v\ne0$，还得 $\eta_2\otimes\eta_1\in J$。

直接代入（34.15），$\mathcal B$ 在（34.14）的三个生成张量上均为零。
它非零且核为三维，故 $J=\ker\mathcal B$，连同两个早期包含即得（34.16）。证明完毕。

两种退化的后果将用于下一步。若 $d=0$，则
$\eta_2\parallel\eta_3$、$\eta_6\parallel\eta_5$，从而 $G_5=G_4$；
由 $\mathcal B(\eta_2,\eta_1)=0$ 还得 $\eta_1\parallel\eta_3$。
若 $c=0$，则 $\eta_2\parallel\eta_4$、$\eta_6\parallel\eta_4$，
从而 $G_5=G_3$。这两个分支的双线性形式都为秩一，不能提前使用非退化性。

**引理34.3（双线性非退化与早期正交刚性）。** 三条互异尾射线的候选必须进一步满足

$$
c\ne0,\qquad d\ne0,\qquad
k\in S,\quad q\in Q,\qquad
\eta_2\perp\eta_3,\quad q\perp v.
\tag{34.20}
$$

证明。先分别排除两个退化分支，再处理非退化双线性形式。

若 $d=0$，前述后果使前三个环境射线相同。逐轮将共同相位吸收入该轮全部接收向量，可以取
$\eta_1=\eta_2=\eta_3=\eta$；同轮的共同调整保留来源系数的相对值。
由 $Up=v\otimes\eta$ 和（34.4），$p\in G_2$。
又因 $V_1k=q\otimes\eta$ 与 $V_0H_1=G_2\otimes\eta$ 正交，
$q\perp G_2$。而 $V_0k=p\otimes\eta\in V_0H_1$，单射性给 $k\in H_1$。

写 $p=\lambda u+\mu w$，其中 $|\lambda|^2+|\mu|^2=1$。
$V_0$ 等距给
$\langle k,p\rangle=\langle p,u\rangle=\bar\lambda$、
$\langle k,q\rangle=\langle p,w\rangle=\bar\mu$，所以
$k=\lambda p+\mu q$。再由 $V_1$ 等距，
$\langle q,v\rangle=\langle k,p\rangle=\bar\lambda$。
置

$$
c_0=\sqrt{|a|^4+|b|^2}>0.
\tag{34.21}
$$

在 $H_1$ 的正交单位基 $p,q$ 与 $H_2$ 的正交单位基
$(a^2u+bv)/c_0,w$ 之间，交叠矩阵为

$$
M=\begin{pmatrix}
a^2\bar\lambda/c_0&\bar\mu\\
b\bar\lambda/c_0&0
\end{pmatrix}.
\tag{34.22}
$$

另一方面，$V_0H_1=G_2\otimes\eta$、$V_0H_2=G_3\otimes\eta$，
而（34.10）使 $G_2,G_3$ 的两个主角余弦均为
$r=|\langle\eta_3,\eta_4\rangle|\in(0,1)$。故
$MM^*=r^2I$。其非对角元为
$a^2\bar b|\lambda|^2/c_0^2$；$ab\ne0$ 迫使 $\lambda=0$，
但这使 $M$ 的第二行全零，与 $r>0$ 矛盾。因此 $d\ne0$。

若 $c=0$，则 $G_5=G_3$。由
$V_0H_2=G_3\otimes\eta_3$、$V_0H_4=G_3\otimes\eta_5$，
$H_2,H_4$ 的两个主角余弦均为
$r=|\langle\eta_3,\eta_5\rangle|\in(0,1)$。单位向量
$w\in H_2$ 因而满足 $\|P_{H_4}w\|=r$。
另一方面，$w\in G_2=\operatorname{im}W_{\eta_3}$，
$G_4=\operatorname{im}W_{\eta_5}$，所以（34.10）也给
$\|P_{G_4}w\|=r$。

实际来源的（34.2）使 $H_4$ 是某个可逆映射 $T:G_4\to Q$ 的图。
对任意 $z\in S$，置 $z_4=P_{G_4}z$，由图空间的正交投影公式得

$$
\|P_{H_4}z\|^2
=\langle z_4,(I+T^*T)^{-1}z_4\rangle.
\tag{34.23}
$$

$T$ 可逆使 $(I+T^*T)^{-1}<I$ 严格成立。取 $z=w$，因
$z_4\ne0$，便有 $\|P_{H_4}w\|<\|P_{G_4}w\|=r$，矛盾。
因此 $c\ne0$。

现在 $cd\ne0$，（34.15）的行列式为 $\alpha cd/\beta\ne0$。
取非零 $\omega\in J^\perp\subset F\otimes F$。在 $F$ 的任意正交单位基中，
双线性泛函 $\mathcal B$ 的系数矩阵仍为秩二，而其 Hilbert 表示向量
$\omega$ 的系数矩阵是该矩阵的复共轭，差一个非零标量。
所以 $\omega$ 的 Schmidt 秩为二。原代数基不正交只引入可逆基变换，不改变这个秩。

令 $k_Q=P_Qk$、$q_S=P_Sq$。$V_1$ 等距及（34.9）给
$V_1k_Q\perp Q\otimes F$；同时

$$
V_1k_Q=V_1k-V_1(P_Sk)\in K\otimes F,
\tag{34.24}
$$

因为两项分别是 $q\otimes\eta_1$ 和 $Q\otimes F$ 中的向量。
所以 $V_1k_Q\in S\otimes F$。再由 $V_0K\perp V_1K$，

$$
V_1k_Q\in R:=(S\otimes F)\cap(V_0K)^\perp,
\qquad (U\otimes I)R=Q\otimes J^\perp=Q\otimes\mathbb C\omega.
\tag{34.25}
$$

对 $V_1k=q\otimes\eta_1$ 取接收器的 $S$ 投影，得到
$V_1k_Q=q_S\otimes\eta_1$。若 $k_Q\ne0$，等距性使其非零；
在 $U$ 坐标下，它既是某个 $z\ne0$ 所给的 $z\otimes\omega$，
又是 $(Uq_S)\otimes\eta_1$。对于 $(Q\otimes F)\mid F$ 切分，
前者 Schmidt 秩二、后者至多一，矛盾。故 $k_Q=0$，上述等式再给 $q_S=0$，即
$k\in S$、$q\in Q$。这个论证只限制实际初态的 $Q$ 分量，没有假定整个
$V_1(Q)$ 都属于 $K\otimes F$。

最后证明早期正交。由 $p=W_{\eta_2}v$、$u,w\in G_2$，可取
$Q$ 的正交单位基 $r,s$，使

$$
u=W_{\eta_3}r,\qquad w=W_{\eta_3}s.
\tag{34.26}
$$

记 $z=\langle\eta_2,\eta_3\rangle$、
$t=|\langle\eta_3,\eta_4\rangle|\in(0,1)$，反设 $z\ne0$。
在上述 $H_1,H_2$ 正交单位基之间，交叠矩阵现为

$$
M=\begin{pmatrix}
a^2z\langle v,r\rangle/c_0&z\langle v,s\rangle\\
b\langle q,v\rangle/c_0&0
\end{pmatrix}.
\tag{34.27}
$$

这里用到 $p,u,w\in S$、$q,v\in Q$、$S\perp Q$。
固定等距将两空间送到 $G_2\otimes\eta_2$、$G_3\otimes\eta_3$，所以
$MM^*=|z|^2t^2I$，且 $M$ 满秩。第二行唯一可能非零项必非零；
两行正交迫使 $\langle v,r\rangle=0$，继而
$|\langle v,s\rangle|=1$。这使第一行的平方范数为 $|z|^2$，
却又必须等于 $|z|^2t^2$，违反 $t<1$。因此
$\eta_2\perp\eta_3$。

此时 $V_0H_1$、$V_0H_2$ 正交，等距性给 $H_1\perp H_2$。
特别地，$0=\langle q,a^2u+bv\rangle=b\langle q,v\rangle$，
故 $q\perp v$，证明完毕。

**定理34.4（排除三条互异尾环境射线）。** 第29—30节合同中的六维五终端精确接收器，
其 $\eta_3,\eta_4,\eta_5$ 不可能是三条互异射线。结合命题30.1，
后三轮若有六维实现，其环境必须恰好占据两条不同射线。

证明。反设三条射线互异，使用引理34.1—34.3的全部结论。
记 $g_{ij}=\langle\eta_i,\eta_j\rangle$。首先有

$$
g_{13}\ne0,\qquad g_{24}\ne0,\qquad g_{35}\ne0.
\tag{34.28}
$$

最后一项已由（34.5）给出。若 $g_{13}=0$，二维 $F$ 和
$\eta_2\perp\eta_3$ 给 $\eta_1\parallel\eta_2$。
于是（34.16）的 $\mathcal B(\eta_2,\eta_1)=0$ 给
$\mathcal B(\eta_2,\eta_2)=0$；再加上
$\mathcal B(\eta_3,\eta_2)=0$，因 $\eta_2,\eta_3$ 为一组基，
便得 $\mathcal B(x,\eta_2)=0$ 对所有 $x\in F$ 成立，违反非退化性。
若 $g_{24}=0$，同一二维正交补关系给 $\eta_4\parallel\eta_3$，
违反尾射线不同。因此（34.28）全部成立。

由 $k\in S$、$V_1k=q\otimes\eta_1$，以及（34.10），

$$
k=W_{\eta_1}q,\qquad p=W_{\eta_2}v,\qquad q,v\in Q.
\tag{34.29}
$$

取（34.26）的正交单位基 $r,s$。因为
$(a^2u+bv)/c_0,w$ 是 $H_2$ 的正交单位基，固定
$V_0H_2=G_3\otimes\eta_3$ 给 $Q$ 的另一组正交单位基 $r_3,s_3$，使

$$
\begin{aligned}
V_0(a^2u+bv)&=c_0W_{\eta_4}r_3\otimes\eta_3,\\
V_0w&=W_{\eta_4}s_3\otimes\eta_3.
\end{aligned}
\tag{34.30}
$$

分别将 $V_0k=p\otimes\eta_1$ 与这两式取内积。由（34.29）、
$S\perp Q$ 和（34.10），等距关系给

$$
\begin{aligned}
a^2g_{13}\langle q,r\rangle
&=c_0g_{13}g_{24}\langle v,r_3\rangle,\\
g_{13}\langle q,s\rangle
&=g_{13}g_{24}\langle v,s_3\rangle.
\end{aligned}
$$

消去非零的 $g_{13}$，得到

$$
a^2\langle q,r\rangle=c_0g_{24}\langle v,r_3\rangle,\qquad
\langle q,s\rangle=g_{24}\langle v,s_3\rangle.
\tag{34.31}
$$

现在使用实际第三轮来源，而不只使用其支撑维数。由（30.4），第二终端的系数为

$$
x_2^0=a^2u+bv,\quad y_2^0=ab u,\qquad
x_2^1=aw,\quad y_2^1=bw.
\tag{34.32}
$$

来源将旧的零、一记忆系数 $x,y$ 变成新零记忆系数
$aV_0x+V_1y$。结合（34.30）以及
$V_1u=r\otimes\eta_3$、$V_1w=s\otimes\eta_3$，
在同一个实际环境 $\eta_3$ 中得到两个第三轮零记忆系数

$$
\begin{aligned}
h_{30}&=a c_0W_{\eta_4}r_3+ab r,\\
h_{31}&=a^2W_{\eta_4}s_3+b s.
\end{aligned}
\tag{34.33}
$$

它们张成 $H_3$。分别取与 $p,q$ 的内积，用（34.31）得到

$$
\begin{aligned}
\langle p,h_{30}\rangle
&=a c_0g_{24}\langle v,r_3\rangle
=a^3\langle q,r\rangle,&
\langle q,h_{30}\rangle&=ab\langle q,r\rangle,\\
\langle p,h_{31}\rangle
&=a^2g_{24}\langle v,s_3\rangle
=a^2\langle q,s\rangle,&
\langle q,h_{31}\rangle&=b\langle q,s\rangle.
\end{aligned}
\tag{34.34}
$$

$b\ne0$，因此在整个 $H_3$ 上有同一线性关系

$$
\langle p,h\rangle=\frac{a^2}{b}\langle q,h\rangle
\qquad(h\in H_3).
\tag{34.35}
$$

所以正交投影 $P_{H_1}|_{H_3}:H_3\to H_1$ 的秩至多一。

另一方面，固定等距又给

$$
V_0H_1=G_2\otimes\eta_2,\qquad
V_0H_3=G_4\otimes\eta_4.
\tag{34.36}
$$

在 $G_2=\operatorname{im}W_{\eta_3}$ 与
$G_4=\operatorname{im}W_{\eta_5}$ 上，用同一个 $Q$ 正交单位基传来的两组基，
其交叠矩阵由（34.10）为 $g_{35}I_Q$。再乘上环境内积，
（34.36）两空间的交叠矩阵便为

$$
g_{24}g_{35}I_Q.
\tag{34.37}
$$

由（34.28），它的秩为二。交叠矩阵的秩不受两侧各自换正交基影响；
等距 $V_0$ 又保持该秩，所以 $P_{H_1}|_{H_3}$ 的秩必须为二。
这与（34.35）的秩至多一矛盾，三条互异尾射线分支被排除。证明完毕。

定理34.4将命题30.1的二维尾环境必要条件进一步收紧为两条不同射线，仍允许它们非正交。
剩余模式是

$$
\begin{array}{ll}
\mathrm{AAB}:&\eta_3\parallel\eta_4\not\parallel\eta_5,\\
\mathrm{ABA}:&\eta_3\parallel\eta_5\not\parallel\eta_4,\\
\mathrm{ABB}:&\eta_4\parallel\eta_5\not\parallel\eta_3.
\end{array}
\tag{34.38}
$$

本节没有构造或排除这三种模式。因此在本节结论范围内，一般容量仍保持
$6\le d_{\mathrm{CPTP},5}(a,b)\le7$。

## 追加锚（本行以下为增补区）

## 35. 展开有限轨道得到固定次数的显式精度下界

本节保留理论卷第10—12、20节的已知两态来源与固定 CPTP 接收合同。其内容是第20节实代数参数化的加强：将前 $8D^2$ 步联合态作为额外变量，用低次递推方程约束，而不把全部迭代代入成高次多项式。原第20节的下界仍成立；新公式改善其容量渐近尺度，不断言对每个小 $D$ 都数值优于旧公式。

**定义35.1（来源、合同与展开参数）。**

来源记忆 $M=\mathbb C^2$，每步发出 $\mathcal B=\mathbb C^2$。已知复振幅满足

$$
|a|^2+|b|^2=1,\qquad
m_0=a|0\rangle+b|1\rangle,\quad m_1=|0\rangle,\qquad
T_{a,b}|i\rangle=|i\rangle_{\mathcal B}\otimes m_i.
\tag{35.1}
$$

接收器有一个独立于来源输入的纯初态，并在每一步使用同一个全域 CPTP 通道
$\mathcal C:\mathcal L(K\otimes\mathcal B)\to\mathcal L(K)$。
每轮新环境可立即丢弃，全部持久控制计入 $K$；来源记忆和任意外部参考均不可访问。终端解码器只作用于 $K$，可以依赖终端编号。误差是参考、活动记忆与全部原档案联合态的半迹距离。

固定整数 $D\ge1$、$k\ge2$，并限制振幅为

$$
|a|^2\ge1/k,\qquad |b|^2\ge1/k.
\tag{35.2}
$$

定义完全显式的常数

$$
\begin{aligned}
N&=8D^2,\\
v'&=40D^4+4,\\
s'&=96D^4+4D^2+3,\\
H'&=\max\{k,400ND^4\}=\max\{k,3200D^6\},\\
\widehat H'&=\max\{H',2v'+2s'\},\\
\kappa'_{D,k}
&=(16\widehat H'6^{v'})^{-v'12^{v'}},\\
\eta'_{D,k}&=\frac{\kappa'_{D,k}}{16N}.
\end{aligned}
\tag{35.3}
$$

**定理35.2（展开递推的显式有限时域误差隙）。** 对满足（35.2）的每个来源，任意维数不超过 $D$ 的固定接收器及任意终端解码器族，至少有一个 $1\le n\le N$，使完整联合最坏半迹恢复误差不小于 $\eta'_{D,k}>0$。事实上，只取来源初态 $|0\rangle_M$，不加参考，已经足够：

$$
\boxed{
\max_{1\le n\le8D^2}\epsilon_n(|0\rangle)
\ge\eta'_{D,k}.
}
\tag{35.4}
$$

其中 $\epsilon_n(|0\rangle)$ 比较接收后的 $M$ 与解码档案和真实纯目标的联合态。

对固定 $k$，存在只依赖 $k$ 的 $C_k>0$，使全部 $D\ge1$ 满足

$$
-\log\eta'_{D,k}\le\exp(C_kD^4).
\tag{35.5}
$$

因此第11节的全时域容量在 $\epsilon\downarrow0$ 时满足

$$
\boxed{
d_\infty^{(\epsilon)}(a,b)
=\Omega_k\!\left([\log\log(1/\epsilon)]^{1/4}\right).
}
\tag{35.6}
$$

此处的常数和充分小误差阈值可统一于（35.2）的整个来源类。它加强第20节
$[\log\log(1/\epsilon)/\log\log\log(1/\epsilon)]^{1/4}$ 的已证下界，仍与既有 $O_{a,b}(\log(1/\epsilon))$ 上界相距很远。

**有限轨道、环境缺陷与已有零点排除。**

先说明第20节已建立、在这里保留的误差转换。固定接收基变换可把独立纯接收初态取为 $e_0$，同时共轭固定通道及解码器，不改变合同。令

$$
\sigma_0=|0,e_0\rangle\langle0,e_0|,\qquad
\sigma_n=\mathcal R^n(\sigma_0),\quad
\rho_n=\operatorname{Tr}_K\sigma_n,\quad
q_n=\operatorname{Tr}_M\sigma_n,
\tag{35.7}
$$

其中 $\mathcal R$ 是一次来源发射与同一接收通道合成的 $M\otimes K$ 上通道。

定义

$$
h(S)=
\operatorname{Tr}[(\operatorname{Tr}_M S)^2]+
\operatorname{Tr}[(\operatorname{Tr}_K S)^2]\operatorname{Tr}(S^2)
-2\operatorname{Tr}[((\operatorname{Tr}_K S)\otimes I_K)S^2],
\quad
G=\sum_{n=1}^N h(\sigma_n).
\tag{35.8}
$$

若 $|\chi_n\rangle_{MKE}$ 是 $\sigma_n$ 的任意纯化，记其边缘为
$\omega_{ME,n}$、$\omega_{E,n}$，则第20节的有限矩阵恒等式给

$$
h(\sigma_n)=
\|\omega_{ME,n}-\rho_n\otimes\omega_{E,n}\|_{\rm HS}^2\ge0.
\tag{35.9}
$$

纯化两侧边缘具有相同非零谱，给出（35.8）的前两项；交叉项为
$\operatorname{Tr}[((\operatorname{Tr}_K\sigma_n)\otimes I_K)\sigma_n^2]$。
故只需 $2D$ 维联合态即可计算与全部累计环境的解耦缺陷。

若一个终端解码的完整纯目标误差为 $\epsilon_n$，则纯目标投影的恢复概率至少为 $1-\epsilon_n$。对解码取 Stinespring 等距，将其全局输出在纯目标方向上的分量归一化，可得目标与某环境纯态的乘积近似，纯态半迹距离至多 $\sqrt{\epsilon_n}$。若目标投影概率为零，则 $\epsilon_n=1$，下述缺陷界直接由两个密度矩阵的迹范数距离至多二得到，无需归一化零向量。偏迹到 $ME$ 及 $E$，再用三角不等式，得到

$$
\frac12\|\omega_{ME,n}-\rho_n\otimes\omega_{E,n}\|_1
\le2\sqrt{\epsilon_n}.
$$

结合 Hilbert–Schmidt 范数不超过迹范数，

$$
h(\sigma_n)\le16\epsilon_n,\qquad
G\le16N\max_{1\le n\le N}\epsilon_n.
\tag{35.10}
$$

另一前置是第12节证明给出的零点排除，而非有限近似误差的无限时间延拓。对非退化来源和同一固定通道，

$$
G>0\qquad(N=8D^2).
\tag{35.11}
$$

理由是：若 $G=0$，（35.9）的非负性使前 $N$ 个终端的记忆与累计环境全都精确成乘积。取同一固定 Kraus 表的词环境，读取全部同长度交叉矩阵元，得到第12节的环境交叉等式。该等式族在 $8D^2$ 维可达空间中于 $N$ 步以内稳定，故精确零等式延拓到全部词长，并推出已被源纯度谱障碍排除的全时域乘积恒等式。这个论证只使用指定纯来源输入 $|0\rangle$，没有要求全部初态解码才成立。

以下参数化只改变对同一个 $G>0$ 的数值分离方式。

**用独立 Hermitian 变量展开所有状态。**

任意 $2D$ 维输入到 $D$ 维输出的 CPTP 通道的 Kraus 秩至多 $2D^2$。补零 Kraus 后，可统一用等距

$$
W:\mathbb C^{2D}\longrightarrow
\mathbb C^D\otimes\mathbb C^{2D^2},
\qquad W^*W=I_{2D}
\tag{35.12}
$$

表示。它是 $2D^3\times2D$ 复矩阵，含 $8D^4$ 个实坐标。

写 $t_{ji}=(m_i)_j$，即
$t_{00}=a,t_{10}=b,t_{01}=1,t_{11}=0$。合成通道的 Kraus 矩阵为

$$
(L_u)_{(j,\alpha),(i,\beta)}
=t_{ji}W_{(\alpha,u),(\beta,i)},\qquad
1\le u\le2D^2.
\tag{35.13}
$$

各矩阵元是来源和 $W$ 实坐标的次数至多二的复多项式。

对每个 $1\le n\le N$，另外引入一个 $2D\times2D$ Hermitian 矩阵变量 $S_n$。对角项用实变量，严格上三角项用一对实部／虚部变量，下三角取其共轭；每个 $S_n$ 恰有 $4D^2$ 个实变量。令 $S_0=\sigma_0$ 为固定矩阵，并要求

$$
S_{n+1}=\sum_{u=1}^{2D^2}L_uS_nL_u^*,
\qquad 0\le n<N.
\tag{35.14}
$$

每个 Hermitian 矩阵等式给 $4D^2$ 条实等式，次数至多五；首步因 $S_0$ 固定，次数至多四。

这些等式没有引入虚假的状态轨道：给定合法 $W,a,b$，（35.14）从固定 $S_0$ 逐步唯一决定
$S_n=\mathcal R^n(\sigma_0)$。因此 $S_n\succeq0$、$\operatorname{Tr}S_n=1$ 自动成立。不需要另加随 $D$ 增长的主子式正性约束，这是将次数上界固定为常数的关键。

为直接显式保证有界，对所有 $S_n$ 的独立实坐标 $x$ 另加冗余约束

$$
1-x\ge0,\qquad1+x\ge0.
\tag{35.15}
$$

实际密度矩阵的各实、虚分量都在此区间，故这些约束不排除任何合法装置。

全部变量为 $W$ 的 $8D^4$ 个坐标、$a,b$ 的四个坐标，以及 $N$ 个状态的 $4ND^2$ 个坐标：

$$
v'=8D^4+4+4ND^2=40D^4+4.
\tag{35.16}
$$

约束包括 $`W^*W=I`$ 的 $4D^2$ 条实等式、来源归一化一条等式、（35.2）两条不等式、递推的 $4ND^2$ 条等式、状态坐标盒的 $8ND^2$ 条不等式。因此总数为

$$
s'=4D^2+3+12ND^2=96D^4+4D^2+3.
\tag{35.17}
$$

这是整数多项式的基本闭半代数集。$W$ 的列范数和来源归一化使其相应坐标有界，状态坐标由（35.15）有界，故可行集紧。它非空：取
$a=b=1/\sqrt2$、任一（35.12）等距，并取其真实有限轨道即可。所有可行点都是满足（35.2）的合法来源和装置，并且 $G=\sum_nh(S_n)>0$。

**次数、整数系数高度与正最小值。**

继续使用第20节的复多项式系数范数
$\|P\|_{\mathrm{coef},1}=\sum_\alpha|c_\alpha|$，它次可乘，实部／虚部提取不增加这个范数。所有符号运算起于整数及 $i$，所以实化后的约束和目标属于实变量上的整数多项式环。

Hermitian 状态矩阵的每个条目系数范数至多二；（35.13）的每个条目次数至多二，系数范数至多四。一个递推矩阵元的右侧至多含
$(2D^2)(2D)^2=8D^4$ 个被加项，每项的范数至多 $4\cdot2\cdot4=32$。
连同左侧矩阵元，实或虚递推约束的系数范数不超过

$$
256D^4+2\le258D^4.
\tag{35.18}
$$

等距约束、来源约束及盒约束的系数高度也不超过
$\max\{k,258D^4\}$。

现在 $G$ 是独立状态变量上的多项式，其次数至多四，没有将迭代代入提升次数。直接按矩阵条目求和，得到每个 $n$：

$$
\begin{aligned}
\|\operatorname{Tr}[(\operatorname{Tr}_M S_n)^2]\|_{\mathrm{coef},1}
&\le16D^2,\\
\|\operatorname{Tr}[(\operatorname{Tr}_K S_n)^2]\|_{\mathrm{coef},1}
&\le16D^2,\\
\|\operatorname{Tr}S_n^2\|_{\mathrm{coef},1}
&\le16D^2,\\
2\|\operatorname{Tr}[((\operatorname{Tr}_K S_n)\otimes I_K)S_n^2]\|_{\mathrm{coef},1}
&\le128D^3.
\end{aligned}
$$

因而

$$
\|h(S_n)\|_{\mathrm{coef},1}
\le16D^2+256D^4+128D^3\le400D^4,
\qquad
\|G\|_{\mathrm{coef},1}\le400ND^4.
\tag{35.19}
$$

这些表达式对任意 Hermitian $S_n$ 都实值；也可逐系数取实部，保持可行集上的值、整数性及同一范数界。

因此，全部约束及目标的次数统一不超过固定偶数

$$
d'=6,
$$

系数高度统一不超过（35.3）的
$H'=\max\{k,400ND^4\}$。

应用第20节已引用的 Jeronimo–Perrucci–Tsigaridas 正最小值定理：在 $v'$ 个实变量、$s'$ 个基本闭整数多项式约束的紧连通分量上，次数不超过偶数 $d'$、系数高度不超过 $H'$ 的整数目标的非零最小值，绝对值至少为

$$
\left(2^{4-v'/2}\widehat H'(d')^{v'}\right)^{-v'2^{v'}(d')^{v'}}.
\tag{35.20}
$$

全局最小值在紧可行集上取得，且由（35.11）严格为正；取包含其最小点的紧连通分量即可，不要求整个可行集连通。

代入 $d'=6$，并保守增大底数中的 $2^{4-v'/2}$ 为 $16$，得到

$$
\min G\ge
(16\widehat H'6^{v'})^{-v'12^{v'}}
=\kappa'_{D,k}.
\tag{35.21}
$$

最后由（35.10）得（35.4）。维数小于 $D$ 的装置可嵌入 $D$ 维寄存器，并在未使用输入空间完成一个固定通道；实际轨道与误差保持。因此该结论覆盖全部预算不超过 $D$ 的装置。证明完毕。

**容量渐近式及与旧结果的关系。**

由（35.3）直接有

$$
-\log\eta'_{D,k}
=\log(16N)+v'12^{v'}\log(16\widehat H'6^{v'}).
\tag{35.22}
$$

这里 $v'\le44D^4$，并且

$$
2v'+2s'=272D^4+8D^2+14\le3200D^6,
$$

故 $\widehat H'=H'\le(k+3200)D^6$。于是次数固定后的增长满足（35.5）。

如需一份显式的可用常数，可取

$$
A_k=\log(16(k+3200))+6+44\log6,\qquad
C_k=44\log12+8+\log(128+44A_k).
\tag{35.23}
$$

事实上 $\log(16\widehat H'6^{v'})\le A_kD^4$，从（35.22）得

$$
-\log\eta'_{D,k}
\le(128+44A_k)D^8
 \exp(44(\log12)D^4)
\le\exp(C_kD^4).
$$

这对全部 $D\ge1$ 成立。

若容量 $D$ 实现全时域误差至多 $\epsilon$，则

$$
\epsilon\ge\eta'_{D,k}
\ge\exp\{-\exp(C_kD^4)\}.
\tag{35.24}
$$

对充分小的正误差取两次对数即得

$$
D\ge C_k^{-1/4}[\log\log(1/\epsilon)]^{1/4},
$$

从而证明（35.6）。

新旧两个显式常数都有效，可按具体 $D,k$ 使用
$\max\{\eta_{D,k},\eta'_{D,k}\}$。本节的加强是消去原保守渐近估计
$D^4\log(D+1)$ 中的 $\log D$ 因子；额外状态变量增大了常数，因此没有逐 $D$ 比较两个数值的先验单调主张。仍未得到
$\exp(-C D^2)$ 或 $\exp(-CD)$ 级的误差下界。

本节复用第12节有限环境交叉零点排除、第20节的环境缺陷／误差转换，以及标准实代数正最小值定理。来源与任意参考合同未弱化；指定 $|0\rangle$ 仅用于必要性。

本节使用与第20节相同的实代数正最小值定理及适用范围。[^phase_positive_polynomial_minimum] 新增参数化以额外的有限轨道状态坐标换取固定次数约束；零点排除和误差转换保持原有依据。

## 追加锚（本行以下为增补区）

## 36. 已知非退化来源的五终端固定接收容量恰为七

本节继续固定第26节的已知来源

$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,
\qquad ab\ne0,\qquad |a|^2+|b|^2=1.
$$

接收器从独立纯态启动，每轮使用同一个全域 CPTP 通道；所有持久系统均计入接收器，活动记忆和任意外部参考不可访问。前五个终端各自要求精确恢复完整参考—活动记忆—原始档案联合态，终端解码器允许依终端而异。来源参数已知，接收通道可以针对这份来源校准。

第29节已把六维候选归约到五个终端均为纯编码，第30节证明后三轮纯环境的张成恰为二维，第34节排除其中三条射线互异的情形。本节处理余下的全部两射线模式。

**定理 36.1（五终端的一般精确容量）。** 在上述合同下，

$$
\boxed{d_{\mathrm{CPTP},5}(a,b)=7.}
\tag{36.1}
$$

证明的七维上界直接复用第25节的显式构造；以下排除一般六维候选，不预设其早期环境正交或来自同一个二维空间。

**共同资料。** 反设有六维接收空间 $K$ 和固定 Stinespring 等距 $V$。记 $V_i x=V(x\otimes|i\rangle)$，则 $V_0K\perp V_1K$。纯终端归约给单位环境向量 $\eta_1,\ldots,\eta_5$、正交单位向量 $p,q$ 及正交单位向量 $u,v,w$，满足

$$
\begin{aligned}
V_0k&=p\otimes\eta_1,&V_1k&=q\otimes\eta_1,\\
V_0p&=u\otimes\eta_2,&V_1p&=v\otimes\eta_2,&V_0q&=w\otimes\eta_2.
\end{aligned}
\tag{36.2}
$$

早期系数空间为

$$
H_1=\operatorname{span}\{p,q\},\qquad
G_2=\operatorname{span}\{u,w\},\qquad
H_2=\operatorname{span}\{a^2u+bv,w\}.
\tag{36.3}
$$

对 $n=3,4,5$，已有二维空间 $H_n,G_n,Q_n$，满足

$$
\begin{aligned}
V_0H_{n-1}&=G_n\otimes\eta_n,&
V_1G_{n-1}&=Q_n\otimes\eta_n,\\
G_n&\perp Q_n,&
H_n&\subset G_n\oplus Q_n,
\end{aligned}
\tag{36.4}
$$

且 $H_n$ 到 $G_n,Q_n$ 的两个正交投影均为同构。这里的满投影来自实际来源的非零系数，不是对任意二维子空间的额外假设。

第30、34节使后三轮射线只可能为 $AAB$、$ABA$ 或 $ABB$，其中不同字母表示不同射线。各段可以一致吸收环境射线相位；这不改变 $a,b$，也不增加轮次控制。下文的 $S,Q,F$ 等辅助符号均在各段局部使用。

**两个线性代数事实。** 若 $U:S\to Q\otimes F$ 为满等距，对单位 $\xi\in F$ 定义

$$
W_\xi z=U^{-1}(z\otimes\xi),\qquad
W_\xi^*W_\zeta=\langle\xi,\zeta\rangle I_Q.
\tag{36.5}
$$

因此两个对应平面的主角余弦均为 $|\langle\xi,\zeta\rangle|$。固定等距保持子空间交叠矩阵的奇异值。

另若 $H\subset G\oplus Q$ 到两个二维因子的投影均为同构，则 $H$ 是可逆映射 $T:G\to Q$ 的图。对 $z\perp Q$，置 $z_G=P_Gz$，有

$$
\|P_Hz\|^2
=\langle z_G,(I+T^*T)^{-1}z_G\rangle
<\|P_Gz\|^2\quad(z_G\ne0).
\tag{36.6}
$$

严格性来自 $T$ 可逆。这一恒等式将用于同一个单位向量的两份投影读数；不会把不同过程的最优值拼在一起。

### 36.1 AAB 尾环境不可能

取 $A=\eta_3=\eta_4$、$B=\eta_5$，两射线不同。

若 $A\perp B$，由 $V_1G_3=Q_4\otimes A$、$V_1G_4=Q_5\otimes B$ 得 $G_3\perp G_4$。同一环境 $A$ 下的跨位正交给

$$
Q_3,Q_4\perp G_3+G_4.
$$

维数迫使

$$
K=G_3\oplus G_4\oplus Q_4.
\tag{36.7}
$$

$H_4\subset G_4\oplus Q_4$，故 $G_3\perp H_4$。又 $V_0H_3=G_4\otimes A$ 与 $V_0H_4=G_5\otimes B$ 正交，故 $H_3\perp H_4$。利用 $H_3$ 到 $Q_3$ 的满投影，得到 $Q_3\perp H_4$；再用 $Q_3\perp G_4$ 和 $H_4$ 到 $Q_4$ 的满投影，得到 $Q_3\perp Q_4$。于是 $Q_3$ 正交于(36.7)的全部三个因子，矛盾。

现在设 $0<|\langle A,B\rangle|<1$。所有尾环境两两非正交，跨位正交给

$$
(G_3+G_4+G_5)\perp(Q_3+Q_4+Q_5).
$$

$V_1G_3$、$V_1G_4$ 的环境射线不同，所以 $G_3\cap G_4=0$。维数只能为四加二。因此存在

$$
S=G_3+G_4,\qquad Q=S^\perp,
\qquad Q_3=Q_4=Q_5=Q,\qquad G_5\subset S.
$$

令 $F=\operatorname{span}\{A,B\}$，则 $U=V_1|_S:S\to Q\otimes F$ 为满等距。由 $V_1G_2=Q\otimes A=V_1G_3$ 得

$$
G_2=G_3=\operatorname{im}W_A,\qquad
G_4=\operatorname{im}W_B.
\tag{36.8}
$$

零位的四维像 $V_0(H_2+H_3)=S\otimes A$，与二维像 $V_0H_4=G_5\otimes B$ 作代数直和，饱和整个零位像：

$$
V_0K=(S\otimes A)\dotplus(G_5\otimes B)\subset S\otimes F.
\tag{36.9}
$$

早期等式给 $\eta_1,\eta_2\in F$、$p\in S$，再由 $V_1p=v\otimes\eta_2\in Q\otimes F$ 得 $v\in Q$。

若 $\eta_2$ 不平行 $A$，早期矩形 $G_2\otimes\eta_2\subset V_0K$ 的 $B$ 坐标迫使 $G_5=G_2$。于是 $H_2,H_4$ 的两个主角余弦均为 $r=|\langle A,B\rangle|>0$，而(36.8)使 $G_2,G_4$ 的主角余弦也是 $r$。单位 $w\in H_2\cap G_2$ 因而满足

$$
\|P_{H_4}w\|=r=\|P_{G_4}w\|,
$$

违反(36.6)，因为 $H_4$ 是 $G_4\to Q$ 的可逆图、$w\perp Q$。

若 $\eta_2\parallel A$，则 $V_0H_1=V_0H_2$，故 $H_1=H_2$。由于 $p\in S$ 而 $H_2\cap S=\mathbb Cw$，有 $p\parallel w$，继而 $q\parallel a^2u+bv$。所以 $q_S=P_Sq\ne0$。

令 $k_Q=P_Qk$。由实际初轮等式、$V_1S=Q\otimes F$ 和固定等距性，

$$
V_1k_Q=q_S\otimes\eta_1
\in R:=(S\otimes F)\cap(V_0K)^\perp.
$$

(36.9)给

$$
R=(S\cap G_5^\perp)\otimes A^\perp,
\tag{36.10}
$$

其中 $A^\perp$ 是二维 $F$ 中的环境线。因 $q_S\ne0$，必须 $k_Q\ne0$、$\eta_1\perp A$。于是 $V_0k=p\otimes\eta_1$ 正交于 $V_0(H_2+H_3)=S\otimes A$，故 $k\perp H_2+H_3$。但 $H_2,H_3\subset G_2\oplus Q$，它们的和四维，故 $H_2+H_3=G_2\oplus Q$。这给 $k_Q=0$，矛盾。AAB 的两个分支均被排除。

### 36.2 非正交 ABA 尾环境不可能

取 $\eta_3=\eta_5=A$、$\eta_4=B$，且 $0<|\langle A,B\rangle|<1$。$V_1G_3$、$V_1G_4$ 的环境射线不同，故 $G_3\cap G_4=0$。全部尾跨位正交再次迫使

$$
K=S\oplus Q,\quad S=G_3+G_4,\quad
Q_3=Q_4=Q_5=Q,\quad G_5\subset S,
$$

其中维数为四加二。取 $F=\operatorname{span}\{A,B\}$、$U=V_1|_S:S\to Q\otimes F$。$V_1G_2=V_1G_4$ 使

$$
G_2=G_4=\operatorname{im}W_A,\qquad
G_3=\operatorname{im}W_B.
\tag{36.11}
$$

先证明 $\eta_2\in F$。若不成立，零位像包含独立环境方向上的

$$
((G_3+G_5)\otimes A)\dotplus(G_2\otimes B)
\dotplus(G_2\otimes\eta_2).
$$

维数至多六使 $G_5=G_3$，且该和饱和 $V_0K$。其全部 receiver 因子属于 $S$，所以 $p\in S$。但 $V_1p=v\otimes\eta_2\in Q\otimes F$，矛盾。

若 $\eta_2\parallel B$，早期 $v\otimes B$ 与 $G_3\otimes A$、$G_2\otimes B$ 跨位正交，使 $v\in Q$，继而 $V_1p\in Q\otimes B=V_1G_3$，故 $p\in G_3$。同时 $V_0H_1=G_2\otimes B=V_0H_3$，给 $p\in H_1=H_3$，违反 $H_3\cap G_3=0$。

因此 $\eta_2$ 的 $A$ 坐标非零。早期矩形与 $G_2\otimes B$ 联合给 $G_2\otimes A$，再加 $G_3\otimes A$ 得六维饱和：

$$
V_0K=(S\otimes A)\dotplus(G_2\otimes B).
\tag{36.12}
$$

所以 $\eta_1\in F$、$p\in S$、$v\in Q$，并有 $p=W_{\eta_2}v$。如(36.10)，实际初轮等式给

$$
V_1k_Q=q_S\otimes\eta_1
\in(S\cap G_2^\perp)\otimes A^\perp,
\qquad q\perp G_2.
\tag{36.13}
$$

对 $V_0k=p\otimes\eta_1$ 的 receiver 因子作用 $U$，由(36.12)得到

$$
\eta_2\otimes\eta_1\in F\otimes A+A\otimes F.
$$

在两个 $F/\mathbb CA$ 因子上取商，得到二择一

$$
\eta_2\parallel A\quad\hbox{或}\quad\eta_1\parallel A.
\tag{36.14}
$$

若 $\eta_2\parallel A$，取 $Q$ 的正交单位基 $r,s$ 使 $u=W_A r,w=W_A s$。令 $c_0=\sqrt{|a|^4+|b|^2}$。在 $H_1$ 的基 $p,q$ 与 $H_2$ 的基 $(a^2u+bv)/c_0,w$ 中，交叠矩阵为

$$
M=\begin{pmatrix}
a^2\langle v,r\rangle/c_0&\langle v,s\rangle\\
b\langle q,v\rangle/c_0&0
\end{pmatrix}.
\tag{36.15}
$$

(36.11)及固定 $V_0$ 使 $MM^*=t^2I$，其中 $t=|\langle A,B\rangle|\in(0,1)$。满秩与两行正交迫使 $\langle v,r\rangle=0$，从而 $|\langle v,s\rangle|=1$。第一行范数为一，与 $t<1$ 矛盾。

若 $\eta_2$ 不平行 $A$，(36.14)迫使 $\eta_1\parallel A$。由(36.13)得 $k_Q=0$、$q_S=0$，即 $k\in S$、$q\in Q$，且 $k\in\operatorname{im}W_A=G_2$。记 $z=\langle\eta_2,A\rangle$。若 $z\ne0$，(36.15)第一行两项各乘 $z$，而固定 $V_0$ 要求 $MM^*=|z|^2t^2I$。同样的满秩与正交行论证使第一行范数为 $|z|$，仍与 $t<1$ 矛盾。因此 $\eta_2\perp A$，从而 $p\perp G_2$。

现在 $V_0k=p\otimes\eta_1$ 正交于 $V_0H_3=G_2\otimes B$，故 $k\perp H_3$。但 $k\in G_2\subset Q^\perp$，$H_3$ 到 $G_3$ 的投影满射，所以 $k\perp G_3$；(36.11)的非零等角关系又使 $G_2$ 到 $G_3$ 的投影单射，只能 $k=0$，矛盾。

### 36.3 正交 ABA 强制已被排除的完整交替环境

取 $\eta_3=\eta_5=A\perp B=\eta_4$。置

$$
L=G_2+G_4,\quad l=\dim L,\qquad
M=H_2+H_4,\quad m=\dim M.
$$

共同环境 $A$ 下的跨位正交给

$$
m+l\le6,
\qquad G_3\perp L,\qquad H_3\perp M.
\tag{36.16}
$$

若 $\eta_2\notin F=\operatorname{span}\{A,B\}$，零位像包含

$$
((G_3+G_5)\otimes A)\dotplus(G_4\otimes B)
\dotplus(G_2\otimes\eta_2),
$$

维数为 $m+4\le6$。故 $m=2$、$G_5=G_3$，且零位像饱和，所有 receiver 因子属于 $G_3+L$。这迫使 $p\in G_3+L$，而 $V_1(G_3+L)\subset K\otimes F$ 与 $V_1p=v\otimes\eta_2$ 矛盾。因此 $\eta_2\in F$。

若 $\langle\eta_2,A\rangle\ne0$，早期与第三轮的跨位正交给 $G_2\perp Q_3$、$v\perp G_3$。再用(36.16)，$H_2\perp G_3$、$H_2\perp H_3$；$H_3$ 到 $Q_3$ 满投影使 $H_2\perp Q_3$，从而 $v\perp Q_3$。于是三维 $C_2=G_2\oplus\mathbb Cv$ 正交于四维 $C_3=G_3\oplus Q_3$，矛盾。所以

$$
\eta_2\parallel B.
\tag{36.17}
$$

由(36.17)，$V_1p$ 与 $V_1L$ 的环境正交，给 $p\perp L$。同 $B$ 跨位正交还给 $v,Q_4\perp L$。因此 $H_2+H_4$ 到 $L$ 的正交投影满射，$m\ge l$；结合(36.16)，只有 $l=2,3$。

若 $l=3$，则 $m=3$，已有零位像

$$
((G_3+G_5)\otimes A)\dotplus(L\otimes B)
$$

维数六，饱和 $V_0K$。由 $V_0k=p\otimes\eta_1$ 得 $\eta_1\in F$；其 $B$ 系数若非零，就有 $p\in L$，与 $p\perp L$ 矛盾。因此 $\eta_1\parallel A$。

若 $l=2$，则 $G_4=G_2$，同 $B$ 零位像使 $H_1=H_3$，特别地 $p\in H_3$。$m=2$ 会使 $H_2=H_4$，与 $0\ne w\in H_2\cap G_2=H_4\cap G_4=0$ 矛盾。$m=4$ 再次饱和上述零位像，同理迫使 $\eta_1\parallel A$。

只剩 $m=3$。此时 $H_2,H_4$ 分别是同一 $G_2$ 上两个映射的图：

$$
T_2u=(b/a^2)v,\quad T_2w=0,\qquad
T_4:G_2\longrightarrow Q_4\ \hbox{可逆}.
$$

图的维数公式给

$$
3=\dim(H_2+H_4)=2+\operatorname{rank}(T_4-T_2).
$$

若 $v\notin Q_4$，$(T_4-T_2)x=0$ 会使 $T_4x=T_2x\in Q_4\cap\mathbb Cv=0$，故 $x=0$，与差映射秩一矛盾。因此 $v\in Q_4$。于是 $V_1p=v\otimes B\in V_1G_3$，故 $p\in G_3$，与 $p\in H_3$、$H_3\cap G_3=0$ 矛盾。

所有余下情形都给 $\eta_1\parallel A$，五轮环境必为 $A,B,A,B,A$。这满足第25节确定、正交、交替环境的合同；定理25.2已经证明该合同需要至少七维。因此正交 ABA 也不可能。

### 36.4 非正交 ABB 尾环境不可能

取 $\eta_3=A$、$\eta_4=\eta_5=B$，且 $0<|\langle A,B\rangle|<1$。令 $F=\operatorname{span}\{A,B\}$。置

$$
\begin{aligned}
M&=H_3+H_4,&m&=\dim M,&L&=G_3+G_4,&l&=\dim L,\\
R&=G_4+G_5,&W&=Q_4+Q_5,&S&=G_3+G_4+G_5,&T&=Q_3+Q_4+Q_5.
\end{aligned}
$$

共同环境 $B$ 给 $\dim R=m$、$\dim W=l$、$R\perp W$，故 $m+l\le6$。全部尾环境非正交又给 $S\perp T$；$M$ 到 $S$ 的投影像恰为 $L$，所以 $m\ge l$。因此 $2\le l\le3$。

若 $l=3$，则 $m=3$，维数使 $S=R=L$、$T=W$，各三维。$V_1S=W\otimes B$ 与 $V_1G_2=Q_3\otimes A$ 的环境不同，故 $G_2\cap S=0$。尾零位像 $(G_3\otimes A)\dotplus(S\otimes B)$ 五维，全部 receiver 因子在 $S$；早期 $G_2\otimes\eta_2$ 与其交为零，另加两维，矛盾。

故 $l=2$，即 $G_3=G_4$、$Q_4=Q_5=:Q$。$m=2$ 会使 $H_3=H_4$，这与第26节式(26.20)的来源主角行列式严格变化矛盾：置 $x=|a|^2$、$y=|b|^2$、$t_2=x^2+y$、$t_3=1-yt_2$、$t_4=1-yt_3$，则

$$
\delta_3=\frac{x^3}{t_3},\qquad
\delta_4=\frac{x^2t_2}{t_4},\qquad
\delta_4-\delta_3=\frac{x^3y^2}{t_3t_4}>0.
\tag{36.18}
$$

同一对 $H,G$ 的投影压缩不可能有两个不同的行列式。因此只剩 $m=3,4$，此时 $S=G_3+G_5=R$。

若 $m=4$，$S^\perp$ 二维，故 $Q_3=Q_4=Q_5=Q=S^\perp$。尾零位像

$$
V_0K=(G_3\otimes A)\dotplus(S\otimes B)
\tag{36.19}
$$

六维饱和，使早期 $G_2\subset S$。$V_1G_2=Q\otimes A$、$V_1G_3=Q\otimes B$ 给 $G_2\cap G_3=0$，故 $G_2+G_3=S$，$U=V_1|_S:S\to Q\otimes F$ 为满等距。$G_2,G_3$ 是 $A,B$ 对应的平面，两个主角余弦为 $r=|\langle A,B\rangle|>0$。

另一方面，$V_0H_2=G_3\otimes A$、$V_0H_3=G_4\otimes B=G_3\otimes B$，使 $H_2,H_3$ 的两个主角余弦也为 $r$。单位 $w\in H_2\cap G_2$ 的投影应满足

$$
\|P_{H_3}w\|=r=\|P_{G_3}w\|,
$$

而 $H_3$ 是 $G_3\to Q$ 的可逆图、$w\perp Q$，违反(36.6)。

若 $m=3$，尾零位像

$$
Z=(G_3\otimes A)\dotplus(S\otimes B)
$$

五维。早期矩形 $E_0=G_2\otimes\eta_2$ 二维，$E_0+Z\subset V_0K$ 使 $\dim(E_0\cap Z)\ge1$。又 $G_2\cap G_3=0$，而 $G_3\subset S$ 的维数为二、三，故 $\dim(G_2\cap S)\le1$。从交集中的非零 $x\otimes\eta_2$ 得

$$
\dim(G_2\cap S)=1,\qquad\eta_2\in F.
$$

若 $\eta_2$ 的 $A$ 系数非零，逐环境坐标比较 $Z$ 会给 $x\in G_3$，与 $x\in G_2\setminus\{0\}$ 矛盾。因此 $\eta_2\parallel B$。令 $S'=S+G_2$，维数四，早期和尾像联合饱和为

$$
V_0K=(G_3\otimes A)\dotplus(S'\otimes B).
\tag{36.20}
$$

$G_2\otimes B$ 与 $Q_3\otimes A$、$Q\otimes B$ 跨位正交，使 $G_2\perp Q_3+Q$；原有 $S\perp Q_3+Q$，所以 $Q_3=Q=(S')^\perp$。于是 $G_2+G_3=S'$，$V_1|_{S'}$ 给相同的 $A,B$ 张量平面。再对单位 $w$ 使用与上一段完全相同的两个主角读数和(36.6)，得到矛盾。非正交 ABB 被排除。

### 36.5 正交 ABB 尾环境不可能

最后取 $\eta_3=A\perp B=\eta_4=\eta_5$。尾正交给

$$
G_2\perp G_3+G_4,\qquad H_2\perp H_3+H_4.
\tag{36.21}
$$

先证明 $\eta_2\in F=\operatorname{span}\{A,B\}$。否则零位像包含

$$
(G_3\otimes A)\dotplus((G_4+G_5)\otimes B)
\dotplus(G_2\otimes\eta_2).
$$

六维限制迫使 $G_4=G_5$，且此和饱和 $V_0K$。所有 receiver 因子属于 $G_2+G_3+G_4$，故 $p$ 属于此和；但 $V_1$ 在该和上只产生 $F$ 中环境，与 $V_1p=v\otimes\eta_2$ 矛盾。

若 $\langle\eta_2,A\rangle\ne0$，跨位正交给 $G_2\perp Q_3$、$v\perp G_3$。结合(36.21)，$H_2\perp G_3$ 且 $H_2\perp H_3$；满 $Q_3$ 投影使 $H_2\perp Q_3$，继而 $v\perp Q_3$。又得到三维 $C_2$ 正交于四维 $C_3$ 的矛盾。因此

$$
\eta_2\parallel B.
\tag{36.22}
$$

第二、第四、第五轮现在共用环境射线 $B$。其零位接收像包含 $R'\otimes B$、一位接收像包含 $W'\otimes B$，其中

$$
R'=G_2+G_4+G_5,\qquad
W'=\mathbb Cv+Q_4+Q_5,\qquad R'\perp W'.
$$

由(36.21)，$G_2\perp G_4$，故 $\dim R'\ge4$。$W'$ 至少二维，所以六维限制使 $\dim W'=2$。固定 $V_1$ 在 $\operatorname{span}\{p\}+G_3+G_4$ 上的像恰为 $W'\otimes B$，等距性迫使

$$
G_3=G_4,\qquad p\in G_3.
\tag{36.23}
$$

另一方面，$V_0H_1=G_2\otimes B$ 与 $V_0H_3=G_4\otimes B$ 正交，故 $H_1\perp H_3$。非零 $p\in H_1$ 因而正交于 $H_3$，但(36.23)使 $p\in G_3$，而 $H_3$ 到 $G_3$ 投影满射。这只能给 $p=0$，矛盾。

### 36.6 完整容量结算及适用边界

第29节排除六维候选的全部混合附加态分支，将其归约为五个纯终端。第30节把后三轮环境张成限制为恰二维，第34节排除三条互异射线。本节逐项排除剩余的 AAB、ABA、ABB，每个模式均包含正交与非正交两类，因而没有留下环境 Gram 参数分支。

所以一般六维固定接收器不可能。第26节已排除五维及以下，第25节为每份已知非退化复振幅来源给出了七维固定 CPTP 构造。因此得到(36.1)。证明完毕。

这个数值对应五个精确、参考完整终端及同一个固定接收通道；它不等同于单个终端的档案秩，也不覆盖未知来源共用通道、无限终端、近似恢复或额外持久资源。第23节的四终端精确值五与本节的五终端精确值七属于不同终端合同，没有改写旧结论。环境射线只是固定通道的 Stinespring 表示资料；证明没有向接收器免费提供轮次标记或外部控制。

## 追加锚（本行以下为增补区）

## 37. 消去终端解码器的有限维保真度不变量

本文保留第10—12节的两态来源、独立纯接收初态、同一个全域 CPTP 接收通道和全部持久控制计入容量的合同。对象是一个有限维可优化工具，不替代第20节及第35节已经取得的显式误差下界，也不把一个尚未估计的新不变量写成新的显式渐近率。

来源为

$$
T_{a,b}|i\rangle=|i\rangle_{\mathcal B}\otimes m_i,\qquad
m_0=a|0\rangle+b|1\rangle,\quad m_1=|0\rangle,\quad
|a|^2+|b|^2=1,\quad ab\ne0.
\tag{37.1}
$$

记容量为 $D$，接收空间 $K=\mathbb C^D$。固定基变换可将任意独立纯接收初态送至同一个 $e_0$，同时共轭接收通道及解码器；故以下固定初态，不损失任何允许的装置。

**定理37.1（有限共同接收器的保真度优化）。** 对（37.1）的任一非退化来源，下文（37.8）的共同接收器最大值取得，且 $\Delta_D>0$。其操作误差界为（37.10）；针对指定初态的有限子任务还满足（37.11）的双侧比较。同一个优化可消去全部终端解码器和指数大小档案，以（37.14）的 $388D^4+1$ 个实变量表示为紧半代数问题。代数振幅允许原则上的认证计算；对任意实振幅，不作无有效参数表示的算法声明。这些结论共同由下文的连续纯化、单终端消元、固定接收器有限期限与全局参数化证明。

**连续的规范纯化与单终端恒等式。**

对固定接收通道 $\mathcal C$，令 $\mathcal R_{\mathcal C}$ 为一次来源发射和接收合成的 $M\otimes K$ 上通道。只取允许的指定来源输入 $|0\rangle_M$，置

$$
\sigma_0=|0,e_0\rangle\langle0,e_0|,\qquad
\sigma_n=\mathcal R_{\mathcal C}^{\,n}(\sigma_0),\qquad
\rho_n=\operatorname{Tr}_K\sigma_n.
\tag{37.2}
$$

局部接收不改变来源记忆边缘，所以 $\rho_n$ 也是未接收的真实纯目标
$|\Psi_n\rangle_{M\mathcal B^{\otimes n}}$ 的 $M$ 边缘。

始终使用同一个辅助空间 $E=\mathbb C^{2D}$，并在 $M\otimes K$ 选定基
$\{|z\rangle\}_{z=1}^{2D}$。定义

$$
|\Omega\rangle=\sum_{z=1}^{2D}|z\rangle_{MK}|z\rangle_E,\qquad
|\Gamma_n\rangle=(\sqrt{\sigma_n}\otimes I_E)|\Omega\rangle,\qquad
\omega_n=\operatorname{Tr}_K|\Gamma_n\rangle\langle\Gamma_n|.
\tag{37.3}
$$

$|\Omega\rangle$ 未归一化，$|\Gamma_n\rangle$ 则因
$\operatorname{Tr}\sigma_n=1$ 归一化。它是 $\sigma_n$ 的纯化，且
$\omega_n$ 是 $M\otimes E$ 上的密度矩阵。

正半定矩阵平方根在整个正半定锥上连续，包括秩发生变化的边界。因而
$\mathcal C\mapsto\sigma_n\mapsto|\Gamma_n\rangle\mapsto\omega_n$ 连续。
这里不能仅说“任选一个纯化”就推出所选纯化连续；（37.3）提供了所需的全局规范。

本文使用根保真度

$$
F(A,B)=\operatorname{Tr}\sqrt{\sqrt A B\sqrt A}.
$$

对每个终端定义

$$
f_n(\mathcal C)=
\max_{\tau\in\mathcal D(E)}
F(\omega_n,\rho_n\otimes\tau).
\tag{37.4}
$$

**单终端恒等式。** 对每个 $n\ge1$，

$$
\boxed{
f_n(\mathcal C)=
\max_{\mathcal D_n:K\to\mathcal B^{\otimes n}\ {\rm CPTP}}
F\!\left((\operatorname{id}_M\otimes\mathcal D_n)(\sigma_n),
|\Psi_n\rangle\langle\Psi_n|\right).
}
\tag{37.5}
$$

两侧均取得最大值，且

$$
f_n(\mathcal C)=1
\quad\Longleftrightarrow\quad
\text{该指定初态在终端 $n$ 有精确的 $K$-局部解码。}
\tag{37.6}
$$

证明。记目标档案空间为 $A=\mathcal B^{\otimes n}$。对一个解码器取 Stinespring 等距
$V:K\to A\otimes F$，并把环境维数按需补大。输出的全局纯化为

$$
|\zeta_V\rangle=(I_{ME}\otimes V)|\Gamma_n\rangle
$$

（这里只作固定的张量因子重排）。它在 $MA$ 上与纯目标的根保真度等于

$$
\max_{\|\xi\|=1,\ \xi\in E\otimes F}
|\langle\Psi_n\otimes\xi\,|\,\zeta_V\rangle|.
\tag{37.7}
$$

这是把 $\zeta_V$ 投影到目标纯态后所得环境向量的范数。

对固定 $\xi$，令 $\tau=\operatorname{Tr}_F|\xi\rangle\langle\xi|$。
$|\Psi_n\rangle\otimes|\xi\rangle$ 是
$\rho_n\otimes\tau$ 在 $ME$ 上的一份纯化，而 $\Gamma_n$ 是
$\omega_n$ 的纯化，所余纯化腿为 $K$。
有限维 Uhlmann 变分恒等式于是给[^phase_uhlmann_transition]

$$
\max_{V:K\hookrightarrow A\otimes F}
|\langle\Psi_n\otimes\xi|(I_{ME}\otimes V)|\Gamma_n\rangle|
=F(\omega_n,\rho_n\otimes\tau).
$$

可取足够大的 $F$，使 Uhlmann 在纯化支撑上的等距延拓到整个 $K$；该等距因而定义全域 CPTP 解码器，而不是只定义于可达支撑的操作。这个变分恒等式也可由纯化振幅矩阵的极分解直接得到：最大重叠为相应乘积的迹范数。

任意 $\tau$ 都有 $\xi$ 纯化，任意解码器和 $\xi$ 也都给这样一个 $\tau$。交换对这两个独立选择的最大化，得到（37.5）。有限维通道集和密度矩阵集紧，目标连续；上述等距构造也直接给最大值实现。根保真度等于一当且仅当两个密度矩阵相同，故（37.6）成立。证明完毕。

（37.5）表明 $f_n$ 与纯化规范无关。固定 $\sigma_n$ 的两份同维纯化只差 $E$ 上酉变换，$\tau$ 的完整优化集随之双射；非最小辅助空间只需补零。这也是后面可用任意矩阵因子代替平方根而不改变优化值的原因。

**有限期限、正性与操作误差。**

置

$$
N_D=8D^2,\qquad
\gamma_D(a,b)=\max_{\mathcal C}\min_{1\le n\le N_D}f_n(\mathcal C),
\qquad
\Delta_D(a,b)=1-\gamma_D(a,b).
\tag{37.8}
$$

通道 $\mathcal C:\mathcal L(K\otimes\mathcal B)\to\mathcal L(K)$ 全域且固定，不允许随 $n$ 更换。终端的 $\tau_n$ 和解码器则可分别依赖 $n$，与原合同一致。

由（37.3）的连续性、根保真度的连续性和固定紧集
$\mathcal D(E)$ 上最大值的连续性，所有 $f_n$ 都是 $\mathcal C$ 的连续函数。Choi 表示中的 CPTP 通道集紧，有限个 $f_n$ 的最小值也连续，所以（37.8）的最大值取得。

若 $\Delta_D=0$，同一个最大点通道使前 $8D^2$ 个 $f_n$ 全为一。由（37.5）分别选择终端解码器，就能对指定输入 $|0\rangle$ 精确服务这些终端。

这里需要核对第12节障碍的实际量词。第12节证明从开头即只取 $|0\rangle_M$，由其每个精确终端推出记忆—累计环境乘积分解，再延拓环境交叉等式；整个矛盾没有使用其他来源初态或参考。因此它已经排除了上述只针对 $|0\rangle$ 的接收器，给出

$$
\boxed{\Delta_D(a,b)>0.}
\tag{37.9}
$$

这一步不是仅凭一个“全输入任务无解”定理就推断子任务无解，而是复用其针对该指定输入的证明范围。

令 $\epsilon_D^\star(a,b)$ 为维数不超过 $D$ 的允许装置在全部终端、全部初始来源和参考上的最优半迹误差下确界。则

$$
\boxed{
\epsilon_D^\star(a,b)\ge
1-\gamma_D(a,b)^2
=2\Delta_D(a,b)-\Delta_D(a,b)^2
\ge\Delta_D(a,b)>0.
}
\tag{37.10}
$$

证明。若某装置的全合同误差至多 $\epsilon$，限制到指定初态和前 $N_D$ 个终端。纯目标投影是一个效果，因此其恢复概率至少为 $1-\epsilon$。其根保真度至少为 $\sqrt{1-\epsilon}$，所以

$$
f_n(\mathcal C)\ge\sqrt{1-\epsilon}
\quad(1\le n\le N_D),\qquad
\gamma_D\ge\sqrt{1-\epsilon}.
$$

平方即得（37.10），再对所有装置取下确界。维数较小的装置可嵌入 $D$ 维，并在未访问部分全域完成固定通道。证明完毕。

这比只使用 $F\ge1-\epsilon$ 的 $\epsilon\ge\Delta_D$ 转换稍强，但仍没有估计 $\Delta_D$ 随 $D$ 的衰减率。

也可精确标定这个工具对应的任务。令 $\varepsilon^0_{D,N_D}$ 为只要求指定初态 $|0\rangle$、只要求前 $N_D$ 个终端的最佳最坏半迹误差，接收通道仍须同一固定通道。定义

$$
Q_D=1-\gamma_D^2.
$$

由（37.5）与纯目标的迹距离／保真度关系，

$$
\boxed{
Q_D\le\varepsilon^0_{D,N_D}\le\sqrt{Q_D}.
}
\tag{37.11}
$$

下界是上面的纯目标投影论证。上界取（37.8）的最大点通道，并分别取实现（37.5）的各终端解码器；它们的误差都不超过
$\sqrt{1-f_n^2}\le\sqrt{Q_D}$。
（37.11）的上界只属于这个指定初态的有限子任务，不是全部来源／参考、全部终端合同的上界。

**每个固定接收器的 SDP 与全局有限变量优化。**

对固定的正半定矩阵 $A,B$，根保真度有变分形式。[^phase_watrous_fidelity_sdp]

$$
F(A,B)=
\max_X\left\{\operatorname{Re}\operatorname{Tr}X:
\begin{pmatrix}A&X\\X^*&B\end{pmatrix}\succeq0\right\}.
\tag{37.12}
$$

该式可由块正性给出的
$X=\sqrt A\,C\,\sqrt B$、$\|C\|_{\rm op}\le1$ 及极分解验证，奇异情形按支撑限制或连续性处理。

所以当 $\mathcal C$ 固定时，（37.4）是以下 SDP：

$$
\begin{aligned}
\text{最大化}\quad&\operatorname{Re}\operatorname{Tr}X_n,\\
\text{满足}\quad&
\tau_n\succeq0,\quad\operatorname{Tr}\tau_n=1,\\
&
\begin{pmatrix}
\omega_n&X_n\\X_n^*&\rho_n\otimes\tau_n
\end{pmatrix}\succeq0.
\end{aligned}
\tag{37.13}
$$

$\omega_n,\rho_n$ 此时固定，故右下块对 $\tau_n$ 仿射。
$E$ 的维数为 $2D$，$\omega_n$ 和 $X_n$ 的矩阵大小是 $4D$，整个保真度块大小为 $8D$。这些状态矩阵的大小只随 $D$ 线性增长。

全局优化接收器时，可以完全不引入大小为 $2^n$ 的档案或终端解码器。采用以下实坐标：

- 接收 Choi 矩阵 $J_{\mathcal C}$ 的大小为 $2D^2\times2D^2$，Hermitian 坐标共 $4D^4$ 个，满足 $J_{\mathcal C}\succeq0$ 及对输出偏迹等于 $I_{2D}$。
- 每个终端 $n=1,\ldots,N_D$ 有一个 $2D\times2D$ Hermitian 状态变量 $S_n$，坐标数 $4D^2$，满足从固定 $S_0=\sigma_0$ 出发的同一一步递推
  $S_{n+1}=\mathcal R_{\mathcal C}(S_n)$。
- 每个终端有一个复矩阵 $Y_n\in\mathbb C^{2D\times2D}$，共 $8D^2$ 个实坐标，满足 $`Y_nY_n^*=S_n`$。令 $\Gamma(Y_n)=\operatorname{vec}(Y_n)$，$\omega(Y_n)=\operatorname{Tr}_K|\Gamma(Y_n)\rangle\langle\Gamma(Y_n)|$。
- 每个终端有一个 $2D\times2D$ Hermitian 密度变量 $\tau_n$，坐标数 $4D^2$，及 $4D\times4D$ 复矩阵 $X_n$，坐标数 $32D^2$。
- 一个共同实标量 $s\in[0,1]$，要求 $s\le\operatorname{Re}\operatorname{Tr}X_n$ 对全部终端成立，并加入（37.13）的块正性，使用 $\omega(Y_n)$ 和 $\rho_n=\operatorname{Tr}_K S_n$。

不同 $n$ 的 $Y_n$ 只是在各终端表示同一真实状态的辅助纯化；它们不需要是一个物理累计环境的前缀。由（37.5）的纯化不变性，这种自由度既不改变单终端值，也不放松同一接收通道的要求。同一通道要求完整保留在 $S_n$ 的共同递推中。

最大化 $s$ 得到的值恰为 $\gamma_D$。对于固定接收器，每个终端的 $\tau_n,X_n$ 独立优化，故共同下界的最大值就是各 $f_n$ 的最小值；反向，任何可行点都定义一台合法接收器和这些终端的可行保真度见证。

按上述坐标选择，总实变量数恰为

$$
4D^4+N_D(4+8+4+32)D^2+1
=388D^4+1.
\tag{37.14}
$$

若把纯初态也当变量优化，会再增加 $O(D)$ 坐标；固定初态的基变换已经消去了这项。Choi 矩阵本身大小为 $O(D^2)$，不能与其余 $O(D)$ 大小的状态矩阵混为一谈。

该可行集紧。Choi 正性和固定偏迹使 Choi 坐标有界；一步递推从密度矩阵出发始终保持密度矩阵；$`Y_nY_n^*=S_n`$ 给 $\|Y_n\|_{\rm HS}=1$；$\tau_n$ 为密度矩阵；保真度块正性给

$$
|(X_n)_{uv}|^2
\le(\omega_n)_{uu}(\rho_n\otimes\tau_n)_{vv}\le1.
$$

全部等式和非严格正性约束闭，所以可行集紧。

对固定 $a,b$，递推对 Choi 和状态变量是双线性的，$`Y_nY_n^*=S_n`$ 是二次等式，块矩阵条目也是次数至多二的多项式。将有限大小的 Hermitian 正性用主子式非负表述，就得到一个有限基本闭半代数优化；它在全局上并非凸优化，尽管固定接收器后的每个终端是 SDP。主子式展开的个数和次数随 $D$ 增长，式（37.14）的变量计数不等于多项式时间算法或固定次数标量约束。

**可计算性范围和可复用边界。**

若 $a,b$ 的实、虚分量是明确给定的实代数数，则上述紧半代数优化使用代数系数。实闭域量词消去和代数数隔离可在原则上确定 $\gamma_D$，并为每个固定 $D$ 输出经过认证的有理数

$$
0<q_D\le\Delta_D
\quad\text{或}\quad
0<q'_D\le Q_D.
\tag{37.15}
$$

严格正性（37.9）保证存在这样的正有理下界；没有实用运行时间、条件数或精度复杂度声明。“全局多项式优化”只有带有效的全局证书或已证明收敛的认证算法时才能承担此结论，未经认证的局部数值最大值不能作下界证书。

对未提供有效表示的任意实振幅，不声称能从其符号值运行算法得到逐来源的 $\Delta_D(a,b)$。如果只要求统一于
$|a|^2,|b|^2\ge1/k$ 的下界，可以把 $a,b$ 的四个实坐标也加入优化，并加入第20节的整数系数归一化及端点距离约束。所得紧集依然没有 $\gamma=1$ 的点，故统一 $\Delta_{D,k}>0$；其优化系数是整数，原则上的有理证书计算只需输入 $D,k$。这扩大了证书的参数范围，但不自动给出足够强的数值界或实用算法。

第20节和第35节的显式下界也给出此优化量的定量界。对一个终端取达到 $f_n$ 的 $\tau_n$，由

$$
D(\omega_n,\rho_n\otimes\tau_n)\le\sqrt{1-f_n^2}
$$

及边缘收缩、三角不等式，

$$
h(\sigma_n)\le16(1-f_n^2).
\tag{37.16}
$$

在取得 $\gamma_D$ 的接收器上，全部 $f_n\ge\gamma_D$，于是

$$
G\le16N_DQ_D.
$$

若第35节给 $G\ge\kappa'_{D,k}$，则

$$
Q_D\ge\eta'_{D,k},\qquad
\Delta_D\ge1-\sqrt{1-\eta'_{D,k}}.
\tag{37.17}
$$

因此这一工具至少重现既有显式下界；进一步改进必须来自对全局保真度优化的更强估计或认证结果，不能仅凭重新定义不变量宣布新速率。

一个可直接核对的低维边界是 $D=1$。此时接收通道唯一，只能丢弃输入，$\sigma_n=\rho_n$。对任意纯化，极分解或 Schmidt 展开给

$$
f_n=\lambda_{\max}(\rho_n),\qquad
\Delta_1=1-\min_{1\le n\le8}\lambda_{\max}(\rho_n).
\tag{37.18}
$$

确切地，根保真度平方的优化为
$\max_{\tau}\operatorname{Tr}(\rho_n^2\tau^{\mathsf T})
=\lambda_{\max}(\rho_n)^2$；平方根才给上式。它检验了根保真度与平方保真度的区别。一般 $D$ 的全局优化仍保留真实接收器自由度，不能由这一例子外推速率。

本工具给出的新接口是：全部终端解码器和指数大小档案被消去，留下固定通道、前 $8D^2$ 个 $2D$ 维联合态及 $O(D)$ 大小的保真度块。下一步可研究某个可认证的全局上界
$\gamma_D\le1-\zeta_D$，或等价的 $Q_D$ 下界。若目标为
$\exp(-CD^2)$ 或 $\exp(-CD)$ 级误差下界，仍须提供相应的 $\zeta_D$ 定量估计；本文没有完成这一部分。

[^phase_uhlmann_transition]: Armin Uhlmann, “The ‘transition probability’ in the state space of a *-algebra,” *Reports on Mathematical Physics* **9** (1976), 273–279, [doi:10.1016/0034-4877(76)90060-4](https://doi.org/10.1016/0034-4877(76)90060-4), [作者原文 PDF](https://www.physik.uni-leipzig.de/~uhlmann/PDF/Uh76a.pdf)。§2 式（4）定义所有共同表示中向量重叠模平方的上确界，§5 式（23）计算密度矩阵情形为平方保真度；本文的根保真度为其平方根。固定一份有限维纯化、对另一纯化腿取等距的形式使用纯化唯一性；把支撑等距完成到全输入的义务由（37.5）的证明给出。

[^phase_watrous_fidelity_sdp]: John Watrous, “Simpler semidefinite programs for completely bounded norms,” [arXiv:1207.5726v2](https://arxiv.org/abs/1207.5726v2), 2 August 2012。式（3）明确采用根保真度；§2.1（原文第5—6页）的 primal problem 正是最大化 Re Tr X、约束 [[P,X],[X*,Q]]≥0，并由 Lemma 2 的收缩算子分解证明最优值等于根保真度，适用于奇异正半定矩阵。本文仅引用这一固定矩阵 SDP 工具，不将其计算复杂度结论扩展到共同接收器的非凸全局优化。

## 追加锚（本行以下为增补区）

## 38. 指定纯输入前三终端的二维障碍与精确容量

本节研究与保真度不变量 $\Delta_D$ 相同的指定来源输入 $|0\rangle_M$。同一个二维全域 CPTP 接收器不能同时精确恢复第二、第三终端，而一个明确的三维固定接收器可以恢复前三个终端，所以这个指定输入任务的精确最小容量是三。二维障碍还把原来用于排除零点的 $32=8D^2$ 步缩短到三步，并给出相应的显式全局有理证书。这里的容量结算只要求指定输入，不等同于完整参考输入族的合同。

**模型与纯输出必要性。**

取来源

$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,\qquad
|a|^2+|b|^2=1,\quad ab\ne0,\qquad
T|i\rangle=m_i\otimes|i\rangle_{\mathcal B}.
\tag{38.1}
$$

这里只将来源记忆排在张量因子前面。接收器 $K=\mathbb C^2$ 从独立纯态 $e$ 启动，重复使用同一个全域 CPTP 通道
$\mathcal C:\mathcal L(K\otimes\mathcal B)\to\mathcal L(K)$。
固定其一份 Stinespring 等距

$$
V:K\otimes\mathcal B\longrightarrow K\otimes E.
\tag{38.2}
$$

环境每步可立即丢弃，不要求环境空白，不限制 Choi 秩。来源初态固定为 $|0\rangle_M$。接收后的联合态记为 $\sigma_n$。

置 $p=|b|^2\in(0,1)$。真实来源边缘通道为

$$
\mathcal E(\rho)=\rho_{00}|m_0\rangle\langle m_0|
+\rho_{11}|0\rangle\langle0|.
$$

所以

$$
\rho_2=(1-p)|m_0\rangle\langle m_0|
+p|0\rangle\langle0|,\qquad
\det\rho_2=p^2(1-p)>0.
\tag{38.3}
$$

又有 $(\rho_2)_{11}=p(1-p)\in(0,1)$，故 $\rho_3$ 也是正定矩阵。

**定理38.1（指定初态的最短二维障碍）。** 对（38.1）的任一非退化复振幅来源，从指定初态 $|0\rangle_M$ 和独立纯接收初态出发，同一个二维全域 CPTP 接收器不能同时精确恢复第二、第三终端的活动记忆与全部档案。前两个终端则可由同一个二维通道精确恢复，因此第三终端是这一指定输入任务的首个障碍。由此得到（38.23）—（38.24）的短期限显式正误差证书。证明保留任意丢弃环境和任意 Choi 秩，不借用完整参考输入族的较强要求。

**纯输出必要性。** 若某终端的真实记忆边缘 $\rho_n$ 正定，且仅作用于二维 $K$ 的通道精确恢复原来的 $M$—档案纯目标，则 $\sigma_n$ 必为纯态。

证明。取实际累计环境给出的 $\sigma_n$ 纯化。精确恢复纯目标迫使记忆与累计环境的边缘为
$\rho_n\otimes\omega_E$。其秩又等于接收器边缘的秩，不超过二。因此

$$
2\operatorname{rank}\omega_E
=\operatorname{rank}(\rho_n\otimes\omega_E)
\le2.
$$

环境为纯态，原来的 $\sigma_n$ 也纯。反过来，若 $\sigma_n$ 纯且具有正确的 $\rho_n$，它与真实目标是同一 $\rho_n$ 的两份纯化；可将 $K$ 等距映入目标的档案 Schmidt 支撑，得到全域局部解码。证明完毕。

因此，第二、第三终端均可精确解码，当且仅当 $\sigma_2,\sigma_3$ 均为纯态。以下直接排除后一个条件。

**第二终端纯性强制第一接收态纯。**

首次来源发射的档案恒为 $|0\rangle_{\mathcal B}$，所以

$$
\sigma_1=|m_0\rangle\langle m_0|\otimes\tau,\qquad
\tau=\mathcal C(|e,0\rangle\langle e,0|).
\tag{38.4}
$$

假设 $\sigma_2$ 纯。若 $\tau$ 秩二，取其谱分解
$\tau=\lambda_0|q_0\rangle\langle q_0|+\lambda_1|q_1\rangle\langle q_1|$，
其中 $\lambda_0,\lambda_1>0$，$q_0,q_1$ 正交归一。

第二次发射前后的 $M\mathcal B$ 纯态为

$$
|\Theta\rangle
=a|m_0\rangle|0\rangle_{\mathcal B}
+b|0\rangle|1\rangle_{\mathcal B},
\tag{38.5}
$$

它的记忆边缘为正定的 $\rho_2$，故在 $\mathcal B$ 上具有满 Schmidt 支撑。接收第二步时，这个纯态与 $\tau$ 张量相乘。

两个正权谱分支接收后的混合态等于同一个纯态 $\sigma_2$，所以每个分支的 $MK$ 输出都等于这份纯态。两份关于正定 $\rho_2$ 的纯化只差 $K$ 上酉变换，因此存在一个共同酉 $U:\mathcal B\to K$ 和单位环境向量 $\zeta_0,\zeta_1$，满足

$$
V(q_j\otimes|b\rangle)
=U|b\rangle\otimes\zeta_j
\quad(j,b\in\{0,1\}).
\tag{38.6}
$$

这里对全部 $b$ 的结论来自（38.5）的满 Schmidt 支撑，不能只比较一条输入向量。

等距 $V$ 保持 $q_0\otimes|b\rangle$ 与 $q_1\otimes|b\rangle$ 的正交性，故 $\zeta_0\perp\zeta_1$。由于 $\{q_j\otimes|b\rangle\}$ 已是整个四维输入空间的基，（38.6）给出全域通道

$$
\mathcal C(X)=U(\operatorname{Tr}_K X)U^*.
\tag{38.7}
$$

将它用于首步，得到 $\tau=U|0\rangle\langle0|U^*$ 为纯态，矛盾。

所以 $\tau$ 必为纯态。取单位向量 $k\in K$，使 $\tau=|k\rangle\langle k|$。首步和第二步的固定等距因而可写为

$$
V(e\otimes|0\rangle)=k\otimes\eta_1,\qquad
V(k\otimes|b\rangle)=u_b\otimes\eta_2
\quad(b=0,1),
\tag{38.8}
$$

其中 $\eta_1,\eta_2$ 单位，$u_0,u_1$ 是 $K$ 的一组正交归一基。

**第三终端与固定等距的交叉 Gram 矛盾。**

由（38.5）、（38.8），第二终端的联合纯态是

$$
|\psi_2\rangle
=a|m_0\rangle\otimes u_0+b|0\rangle\otimes u_1
=|0\rangle\otimes(a^2u_0+bu_1)
+|1\rangle\otimes ab\,u_0.
\tag{38.9}
$$

定义

$$
r=\sqrt{|a|^4+|b|^2}>0,\qquad
q=(a^2u_0+bu_1)/r.
\tag{38.10}
$$

$q$ 单位，且因 $b\ne0$，$q$ 与 $u_0$ 不共线。

第三次发射后，实际的 $K\mathcal B$ Schmidt 支撑为

$$
S_3=\operatorname{span}\{q\otimes|0\rangle,\ u_0\otimes|1\rangle\}.
\tag{38.11}
$$

理由是其两个记忆系数为线性无关的 $m_0,|0\rangle$，两个接收输入系数分别为非零的
$r q\otimes|0\rangle$、$ab\,u_0\otimes|1\rangle$。

若 $\sigma_3$ 也纯，则这整个二维支撑经 $V$ 后位于
$K\otimes\mathbb C\eta_3$，并因两边维数都是二而占满该空间。所以存在正交归一基 $v_0,v_1$ 和单位 $\eta_3$，使

$$
V(q\otimes|0\rangle)=v_0\otimes\eta_3,\qquad
V(u_0\otimes|1\rangle)=v_1\otimes\eta_3.
\tag{38.12}
$$

令 $c_{23}=\langle\eta_2,\eta_3\rangle$。把（38.8）的两个第二步输入与（38.12）的两个第三步输入交叉取内积，得到

$$
\begin{pmatrix}
\langle k,q\rangle&0\\
0&\langle k,u_0\rangle
\end{pmatrix}
=
c_{23}
\begin{pmatrix}
\langle u_0,v_0\rangle&\langle u_0,v_1\rangle\\
\langle u_1,v_0\rangle&\langle u_1,v_1\rangle
\end{pmatrix}.
\tag{38.13}
$$

右边第二个矩阵是酉矩阵。若 $c_{23}=0$，则 $k$ 同时正交于张满 $K$ 的 $q,u_0$，矛盾。故 $c_{23}\ne0$，两项非对角元必须为零，于是

$$
v_0\parallel u_0,\qquad v_1\parallel u_1,\qquad
|\langle k,q\rangle|=|\langle k,u_0\rangle|.
\tag{38.14}
$$

特别地，$k$ 不可能平行于 $u_0$：否则（38.14）使 $q\parallel u_0$，与（38.10）矛盾。因此

$$
\langle k,u_1\rangle\ne0.
\tag{38.15}
$$

现在把首次输入 $e\otimes|0\rangle$ 与第二步的
$k\otimes|1\rangle$ 比较。输入正交，而输出内积为
$\langle k,u_1\rangle\langle\eta_1,\eta_2\rangle$。
由（38.15），$\langle\eta_1,\eta_2\rangle=0$。
再与 $k\otimes|0\rangle$ 比较，得到

$$
\langle e,k\rangle
=\langle k,u_0\rangle\langle\eta_1,\eta_2\rangle=0.
\tag{38.16}
$$

同理，把首次输入与第三步的 $u_0\otimes|1\rangle$ 比较，利用
$v_1\parallel u_1$ 及（38.15），得到
$\langle\eta_1,\eta_3\rangle=0$。
再与 $q\otimes|0\rangle$ 比较，得到

$$
\langle e,q\rangle
=\langle k,v_0\rangle\langle\eta_1,\eta_3\rangle=0.
\tag{38.17}
$$

二维空间中，非零 $e$ 的正交补是一条直线。（38.16）、（38.17）迫使
$q\parallel k$，再由（38.14）得到 $k\parallel u_0$，最终又给
$q\parallel u_0$，矛盾。

**结论。** 对任意非退化复振幅 $a,b$，同一个二维固定 CPTP 接收器从指定输入 $|0\rangle$ 出发，不能使第二、第三终端同时精确可恢复。证明没有假设第一接收态纯，也没有假设各轮环境相同、正交或空白；所需纯性和两个环境正交关系均由实际合同推出。

这个期限是该指定输入任务的首个障碍：取
$\mathcal C(X)=\operatorname{Tr}_K X$，把每个新发出位存入二维接收器，前两个终端可精确恢复。终端一输出固定 $|0\rangle$；终端二将接收位前面附上首位 $|0\rangle$，就恢复完整档案。首步后继续使用同一个通道即可，不需免费控制或终端知识。

**对 $\Delta_2$ 的短期限与显式全局证书。**

令 $f_n(\mathcal C)$ 为指定来源输入下终端 $n$ 最优局部解码的根保真度，等价于消去解码器后的
$\max_\tau F(\omega_n,\rho_n\otimes\tau)$。定义

$$
\gamma_2^{[3]}=\max_{\mathcal C}\min\{f_2(\mathcal C),f_3(\mathcal C)\},
\quad
\Delta_2^{[3]}=1-\gamma_2^{[3]},
\quad
Q_2^{[3]}=1-(\gamma_2^{[3]})^2.
\tag{38.18}
$$

首终端对所有 $\mathcal C$ 都有 $f_1=1$，因为其真实档案恒为已知纯态
$|0\rangle$。所以省略 $f_1$ 不改变前三终端的值。

有限维 CPTP 集紧、$f_n$ 连续；上述精确障碍使最大值严格小于一。因此
$\Delta_2^{[3]}>0$。原来使用前32终端的 $\Delta_2$ 满足

$$
\Delta_2\ge\Delta_2^{[3]}.
\tag{38.19}
$$

还可将这个短期限零点排除代入既有的环境缺陷／实代数方法，给出无需数值搜索的有理证书。取整数 $k\ge2$，假设
$|a|^2,|b|^2\ge1/k$，并令

$$
G_3=h(\sigma_2)+h(\sigma_3),
\tag{38.20}
$$

其中 $h$ 是第20节的完整环境解耦缺陷多项式。若 $G_3=0$，则两个终端的记忆与累计环境均成乘积；由（38.3）及其第三步版本，秩论证迫使
$\sigma_2,\sigma_3$ 都纯，已被上面的几何证明排除。所以整个合法参数集上
$G_3>0$。

使用第35节的固定次数展开，但只保留三个轨道变量
$S_1,S_2,S_3$。二维接收通道的一份通用等距为
$W:\mathbb C^4\to\mathbb C^2\otimes\mathbb C^8$，含128个实变量。
保留复 $a,b$ 的四个实变量，再加三个 $4\times4$ Hermitian 状态的48个变量，总数为

$$
v_3=180.
$$

等距约束16条、来源归一化及端点约束3条、三个递推48条、状态实坐标的双侧盒约束96条，总数为

$$
s_3=163.
$$

递推次数至多五、目标次数至多四，取固定偶数 $d_3=6$。
每个 $h(S_n)$ 的整数系数范数不超过
$400\cdot2^4=6400$，两项之和不超过12800；递推约束的系数界不超过4128。因此可取

$$
H_3=\max\{k,12800\},\qquad
\widehat H_3=\max\{H_3,2v_3+2s_3\}=H_3.
\tag{38.21}
$$

状态正性和迹一仍由合法递推保证，没有添加高次主子式约束。

与第35节相同的正最小值定理于是给出完全显式的正有理数

$$
\kappa_{2,k}^{[3]}
=(16H_3\,6^{180})^{-180\,12^{180}},
\qquad
\min G_3\ge\kappa_{2,k}^{[3]}.
\tag{38.22}
$$

对任何达到 $f_n$ 的产品环境态，
$h(\sigma_n)\le16(1-f_n^2)$。在达到
$\gamma_2^{[3]}$ 的接收器上，因此有
$G_3\le32Q_2^{[3]}$。得到

$$
\boxed{
Q_2^{[3]}\ge\frac{\kappa_{2,k}^{[3]}}{32},
\qquad
\Delta_2\ge\Delta_2^{[3]}
\ge1-\sqrt{1-\kappa_{2,k}^{[3]}/32}.
}
\tag{38.23}
$$

若只要有理数形式，也有

$$
\Delta_2\ge\frac{\kappa_{2,k}^{[3]}}{64},
\tag{38.24}
$$

因为 $1-\sqrt{1-x}\ge x/2$ 对 $0\le x\le1$ 成立。完整合同的最坏误差也至少为
$\kappa_{2,k}^{[3]}/32$，指定输入的第二、第三终端已经见证此下界。

这里使用了既有实代数最小值定理，但新增的零点排除是只用第二、第三终端的二维几何矛盾。对 $D=2$，展开所需变量从第35节通用构造的644个减到180个。证书仍极保守；它只证明一个明确正有理下界，没有计算真正的 $\Delta_2$、宣称数值最优或给出一般 $D$ 的新渐近率。全部结论均针对固定的全域 CPTP 接收器，不是假设接收酉或预设纯环境的受限模型。

**源相位的固定换基。** 对已知的非零复振幅，令

$$
D_M=\operatorname{diag}(1,e^{i(\arg a-\arg b)}),\qquad
U_{\mathcal B}=\operatorname{diag}
(e^{-i\arg a},e^{i(\arg a-\arg b)}).
\tag{38.25}
$$

逐列计算得到

$$
(D_M\otimes U_{\mathcal B})T_{a,b}D_M^*
=T_{|a|,|b|}.
\tag{38.26}
$$

在正实振幅来源上，把每个新发出位先作用 $U_{\mathcal B}^*$，再使用原来的固定接收通道；终端解码档案再作用 $U_{\mathcal B}^{\otimes n}$。该预处理每轮相同，可直接并入一个全域 CPTP 接收门，不增加持久控制。指定初态 $|0\rangle$ 被 $D_M$ 保持；完整参考合同则同时对来源初态作固定酉换基，而其全输入上确界不变。因此本节的指定输入误差、相应保真度不变量以及完整参考容量都只依赖 $p=|b|^2$，后续可在 $a=\sqrt{1-p},b=\sqrt p$ 上研究。

这一等价没有把接收通道限制为实矩阵，也没有通过平均通道来选取对称接收器；被改变的是固定的物理基和每轮相同的新位预处理。

**三维达到构造与精确容量。**

**定理38.2（指定输入前三终端的精确容量三）。** 对（38.1）的任一非退化复振幅来源，以 $|0\rangle_M$ 为指定来源初态，要求同一个全域 CPTP 接收器从独立纯态启动，并在每个 $n=1,2,3$ 终端由仅作用于接收器的解码恢复活动记忆与完整档案，则接收空间的最小维数为三。达到下界的接收门及各终端解码门都可以与 $a,b$ 无关。

证明。二维不可能性已由定理38.1给出；一维装置可嵌入二维并将通道全域扩展，因此更小维数也不可能。下面构造三维装置。

取 $K=\operatorname{span}\{e_0,e_1,e_2\}$，接收初态为 $e_0$，单轮丢弃环境为
$E=\operatorname{span}\{A,B\}$。定义固定酉
$V:K\otimes\mathcal B\to K\otimes E$ 为以下基向量置换：

$$
\begin{array}{lll}
V(e_0\otimes|0\rangle)=e_2\otimes A,&
V(e_1\otimes|0\rangle)=e_0\otimes A,&
V(e_2\otimes|0\rangle)=e_0\otimes B,\\
V(e_0\otimes|1\rangle)=e_1\otimes A,&
V(e_2\otimes|1\rangle)=e_1\otimes B,&
V(e_1\otimes|1\rangle)=e_2\otimes B.
\end{array}
\tag{38.27}
$$

输入六个基向量和输出六个基向量分别构成整个六维空间的正交归一基，故此表定义了全域酉。每轮都使用

$$
\mathcal C(X)=\operatorname{Tr}_E(VXV^*).
\tag{38.28}
$$

从 $|0\rangle_M\otimes e_0$ 逐轮作用真实来源等距及（38.27），得到接收后的纯联合态

$$
\begin{aligned}
|\Phi_1\rangle_{MK}&=m_0\otimes e_2,\\
|\Phi_2\rangle_{MK}&=a\,m_0\otimes e_0+b\,m_1\otimes e_1,\\
|\Phi_3\rangle_{MK}&=m_0\otimes(a^2e_2+be_0)+ab\,m_1\otimes e_1.
\end{aligned}
\tag{38.29}
$$

相应累计环境恰为 $A$、$A\otimes B$、$A\otimes B\otimes A$，每个终端都与 $MK$ 解耦。这些等式保留复振幅本身，未对来源作相位换基。

终端 $n\le3$ 的解码器在本地附加这个已知的环境前缀，然后按逆序对接收器和第 $n,n-1,\ldots,1$ 个环境作用 $V^*$，每次保留复原的档案位。最后丢弃复原的初始接收寄存器。这个过程是定义在整个 $\mathcal L(K)$ 上的 CPTP 通道；实际输入上最终寄存器恢复为 $e_0$，所有档案位均恢复为原来的次序。早期接收操作与其后的来源发射作用于不交系统，故可把累计接收视为全部发射后仅作用于档案和接收器的酉；其逆不访问活动记忆，因此同时保留活动记忆与档案的完整联合态。

门表和附加的环境前缀均不含 $a,b$；接收过程中只持久保存三维 $K$，终端解码可按已知的 $n$ 选择。记这一指定输入任务的最小维数为 $D_{\min}^{0,[3]}$，便有

$$
\boxed{D_{\min}^{0,[3]}=3.}
\tag{38.30}
$$

证明完毕。该达到构造只保证指定初态 $|0\rangle_M$ 的前三终端，完整参考输入族的三终端最小容量四属于不同合同；也没有由（38.30）推出四步以后或所有终端的精确恢复。

## 追加锚（本行以下为增补区）

## 39. 六终端的八维固定接收器与指定核心延拓的精确容量

本节固定已知非退化来源

$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,
\qquad ab\ne0,\qquad |a|^2+|b|^2=1.
\tag{39.1}
$$

源的一步等距为 $|i\rangle_M\mapsto m_i\otimes|i\rangle_B$。接收器从独立纯态启动，每轮对接收器与最新发出位使用同一个全域 CPTP 通道；所有持久系统均计入接收器，活动记忆和任意外部参考不可访问。要求前六个终端各自精确恢复完整参考—活动记忆—原始档案联合态，终端解码器允许依终端而异。

**定理 39.1（六终端的八维上界）。** 对每份满足（39.1）的已知来源，存在一个八维固定接收通道，精确服务上述六个终端。因此，结合第36节的五终端精确容量，

$$
\boxed{7\le d_{\mathrm{CPTP},6}(a,b)\le8.}
\tag{39.2}
$$

以下给出完整构造。接收通道可以针对已知 $a,b$ 校准，但实际执行不依赖轮次控制。

### 39.1 五维向量核心与三个新增方向

取接收空间 $K$ 的八元正交单位基

$$
u,v,w,p,e,g,h,t,
\tag{39.3}
$$

初始接收态为 $w$。环境 $E$ 二维，正交单位基为 $A,B$。沿用第23节的五维向量核心，令

$$
\begin{aligned}
c&=\sqrt{|a|^4+|b|^2},&
d&=\sqrt{c^2+|b|^2},\\
z&=\frac{a^2u+bv}{c},&
y&=\frac{-\overline b\,u+\overline a^{\,2}v}{c},\\
q&=\frac{\overline b\,y+\overline a^{\,2}e}{c},&
f&=\frac{-a^2y+be}{c},\\
s&=\frac{-cv+be}{d},&
r&=\frac{df-cs}{b}.
\end{aligned}
\tag{39.4}
$$

这些向量满足

$$
\begin{gathered}
(z,y),\quad(q,f),\quad(p,q,s,r)
\quad\text{分别是正交单位族},\\
q,f\in\operatorname{span}\{y,e\},\qquad
q,f\perp z,w,p,\qquad s\perp u,w,p,\\
cs+br=df,\qquad
\operatorname{span}\{p,q,s,r\}
=\operatorname{span}\{u,v,p,e\}.
\end{gathered}
\tag{39.5}
$$

最后一个空间等式也可直接核对：由 $r=(df-cs)/b$ 可在左侧得到 $f$，由 $(q,f)$ 得到 $\operatorname{span}\{y,e\}$，由 $s=(-cv+be)/d$ 得到 $v$，最后由 $y$ 的非零 $u$ 系数得到 $u$。

在新增平面 $\operatorname{span}\{g,h\}$ 中置

$$
\begin{aligned}
\kappa&=\sqrt{|a|^4d^2+|b|^2c^2},\\
x&=\frac{a^2dg+cbh}{\kappa},&
y_4&=\frac{-c\overline b\,g+\overline a^{\,2}dh}{\kappa}.
\end{aligned}
\tag{39.6}
$$

直接取内积得 $\|x\|=\|y_4\|=1$、$\langle x,y_4\rangle=0$。再定义

$$
\lambda=\sqrt{\kappa^2+|b|^2d^2},\qquad
z_6=\frac{\kappa t+bd\,y_4}{\lambda}.
\tag{39.7}
$$

于是 $z_6$ 单位，且正交于 $x$ 及整个五维核心。$c,d,\kappa,\lambda$ 均严格正，且 $b\ne0$，所以所有分母均非零。

### 39.2 同一个部分酉的十三行作用

记输入 $v0=v\otimes|0\rangle$、$v1=v\otimes|1\rangle$；输出 $vA=v\otimes A$、$vB=v\otimes B$。规定

$$
\begin{array}{c|c@{\qquad}c|c}
\text{输入}&\text{输出}&\text{输入}&\text{输出}\\ \hline
w0&pA&p0&uB\\
w1&qA&p1&vB\\
z0&sA&q0&wB\\
u1&rA&f0&gB\\
x0&tA&s1&hB\\
g1&y_4A&z_6 0&pB\\
&&t1&eB
\end{array}
\tag{39.8}
$$

左半表的零位输入族为 $(w,z,x)$，一位输入族为 $(w,u,g)$；右半表分别为 $(p,q,f,z_6)$ 和 $(p,s,t)$。四族各自正交归一。

两半表的零位族彼此正交：原核心给 $w,z\perp p,q,f$，新增 $x$ 正交于核心，$z_6$ 正交于核心及 $x$。两半表的一位族也彼此正交：原核心给 $w,u\perp p,s$，新增 $g,t$ 正交于核心且相互正交。不同输入位之间自动正交，所以十三个输入构成正交单位族。

环境 $A$ 块中的接收输出为 $(p,q,s,r,t,y_4)$，是六个正交单位向量；环境 $B$ 块为 $(u,v,w,g,h,p,e)$，是七个正交单位向量。两个环境正交，所以十三个输出也构成正交单位族。

把两侧各自补成十六维空间的正交单位基，得到全域酉

$$
V:K\otimes\mathbb C^2\longrightarrow K\otimes E.
\tag{39.9}
$$

每轮固定使用同一个通道

$$
\mathcal C(X)=\operatorname{Tr}_E(VXV^*).
\tag{39.10}
$$

环境逐轮丢弃，没有任何环境系统作为额外持久接收记忆保留。

### 39.3 两个初始列的全部六轮轨迹

以 $\Psi_n^i\in M\otimes K$ 表示初始活动记忆为 $|i\rangle$ 时，第 $n$ 轮之后的联合列；记 $m_jv=m_j\otimes v$，省略共同环境字。前两轮为

$$
\begin{array}{ll}
\Psi_1^0=m_0p,&\Psi_1^1=m_1q,\\[2pt]
\Psi_2^0=a\,m_0u+b\,m_1v,&\Psi_2^1=m_0w.
\end{array}
\tag{39.11}
$$

第三轮给

$$
\Psi_3^0=c\,m_0s+ab\,m_1r,\qquad
\Psi_3^1=a\,m_0p+b\,m_1q.
\tag{39.12}
$$

利用 $cs+br=df$，第四轮为

$$
\begin{aligned}
\Psi_4^0&=ad\,m_0g+cb\,m_1h,\\
\Psi_4^1&=m_0(a^2u+bw)+ab\,m_1v.
\end{aligned}
\tag{39.13}
$$

第五轮第一列的零位输入系数为 $a^2dg+cbh=\kappa x$，一位输入系数为 $abd\,g$，故

$$
\begin{aligned}
\Psi_5^0&=\kappa m_0t+abd\,m_1y_4,\\
\Psi_5^1&=a\,m_0(cs+bp)+b\,m_1(a^2r+bq).
\end{aligned}
\tag{39.14}
$$

第六轮第一列的两个输入系数为

$$
a\kappa t+abd\,y_4=a\lambda z_6,\qquad b\kappa t.
\tag{39.15}
$$

第二列的两个输入系数为

$$
\begin{aligned}
a^2(cs+bp)+b(a^2r+bq)
&=a^2df+a^2bp+b^2q,\\
ab(cs+bp)&=abc\,s+ab^2p.
\end{aligned}
\tag{39.16}
$$

表（39.8）于是给出最后一轮

$$
\begin{aligned}
\Psi_6^0&=a\lambda\,m_0p+b\kappa\,m_1e,\\
\Psi_6^1&=m_0(a^2dg+a^2bu+b^2w)
          +m_1(abc\,h+ab^2v).
\end{aligned}
\tag{39.17}
$$

每一轮的两个初始列都具有同一个纯输出环境，六轮依次为 $A,B,A,B,A,B$。因此这些等式通过线性性保持任意初始叠加，并保持与任意不可访问参考的相干关联。

### 39.4 只在接收端运行的完整解码

固定终端 $n\le6$，记 $\eta_1\cdots\eta_n$ 为 $ABABAB$ 的前 $n$ 位。解码端准备这份已知纯环境字，从 $\eta_n$ 开始逆序施加 $V^*$，每次恢复一个发出位，最后恢复独立接收初态 $w$。将发出位排列回原有档案次序并丢弃 $w$，得到一个定义在整个接收空间上的 CPTP 解码器。

早期接收门与其后的源发射分别作用于接收器—既有档案和活动记忆—新发出位，因此可以交换次序。全部接收门在终端等价于只作用于完整档案及初态 $w$ 的累计酉。上述逆运算正是该累计酉在实际输入像上的逆，始终只访问接收器、解码端准备的环境以及已恢复的档案位。

于是对任意参考 $R$、任意初始联合态 $\rho_{RM}$，都有

$$
(\operatorname{id}_{RM}\otimes\mathcal D_n)
\bigl(\rho^{\mathrm{received}}_{RMK,n}\bigr)
=\rho^{\mathrm{source}}_{RM B_1\cdots B_n}.
\tag{39.18}
$$

这证明八维上界。六终端合同包含前五个终端要求，而第36节给 $d_{\mathrm{CPTP},5}(a,b)=7$，所以得到（39.2）。定理39.1证明完毕。

### 39.5 固定第25节前四轮九行部分表的延拓下界

以下另外限制实现类。固定第25节构造（25.39）的前四轮九行部分表

$$
\begin{array}{c|c@{\qquad}c|c}
\text{输入}&\text{输出}&\text{输入}&\text{输出}\\ \hline
w0&pA&p0&uB\\
w1&qA&p1&vB\\
z0&sA&q0&wB\\
u1&rA&f0&gB\\
&&s1&hB
\end{array}
\tag{39.19}
$$

其中五维向量核心仍为（39.4），$g,h$ 是与核心正交的单位方向。只允许在尚未指定的输入上选择等距完成，要求前六轮的新环境为同一对正交单位向量构成的 $ABABAB$。

**定理 39.2（指定九行核心的六终端最优容量）。** 在（39.19）及确定正交交替环境的附加限制下，六终端最小接收维数恰为八。

证明：表（39.8）已给八维上界。反设七维完成存在，则 $K$ 的正交单位基为 $u,v,w,p,e,g,h$。第五轮第一来源列的两个新输入为 $x0$ 和 $g1$，其中 $x$ 由（39.6）定义。由于第五轮要求环境 $A$，而 $m_0,m_1$ 线性无关且两个系数均非零，必有

$$
V(x0)=j\otimes A,\qquad V(g1)=k\otimes A,
\tag{39.20}
$$

其中 $j,k$ 正交归一。它们与已有环境 $A$ 输出 $p,q,s,r$ 正交，所以（39.5）给

$$
j,k\in\operatorname{span}\{w,g,h\}.
\tag{39.21}
$$

这里保留了该三维正交补中全部第五轮自由。第五轮第一列必为

$$
\Psi_5^0=\kappa m_0j+abd\,m_1k.
\tag{39.22}
$$

第六轮的一位输入系数为非零倍数 $b\kappa j$。该方向必须输出环境 $B$，所以固定等距使 $j1$ 正交于旧环境 $A$ 的一位输入 $w1,u1,g1$。结合（39.21）得到

$$
j=\zeta h,\qquad |\zeta|=1,\qquad
k\in\operatorname{span}\{w,g\}.
\tag{39.23}
$$

第六轮零位输入系数是 $a(\kappa j+bdk)$。它同样必须输出环境 $B$，故

$$
\kappa j+bdk\perp\operatorname{span}\{w,z,x\}.
\tag{39.24}
$$

先与 $w$ 取内积，由 $bd\ne0$ 得 $k\perp w$。于是

$$
k=\xi g,\qquad |\xi|=1.
\tag{39.25}
$$

再与 $x$ 取内积，得到

$$
\begin{aligned}
0
&=\langle x,\kappa\zeta h+bd\,\xi g\rangle\\
&=c\overline b\,\zeta+
\frac{b\overline a^{\,2}d^2}{\kappa}\,\xi.
\end{aligned}
\tag{39.26}
$$

因此取绝对值必须满足

$$
c\kappa=|a|^2d^2.
\tag{39.27}
$$

但令 $X=|a|^2$、$Y=|b|^2>0$，由 $c^2=X^2+Y$、$d^2=X^2+2Y$、$\kappa^2=X^2d^2+Yc^2$，有

$$
\begin{aligned}
c^2\kappa^2-X^2d^4
&=c^2(X^2d^2+Yc^2)-X^2d^4\\
&=Y(c^4-X^2d^2)\\
&=Y^3>0,
\end{aligned}
\tag{39.28}
$$

与（39.27）矛盾。七维完成不可能；更低维数本来不能容纳（39.19）要求的七个正交单位核心方向。结合八维构造，受限最优值恰为八。证明完毕。

定理39.2固定的是第25节的前四轮九行实现，不能将任意七维接收器归约到该表。一般七维候选可以改变早期实现或采用尚未排除的早期混合附加态，因此一般六终端问题在本节仍只有（39.2）：最优值为七或八。八维构造也没有给出一个统一服务任意多终端的八维固定通道。

## 追加锚（本行以下为增补区）

## 40. 二维固定接收器的初等误差隙与三终端校准

本节对第38节指定输入 $|0\rangle_M$ 的三终端障碍作定量化。来源、独立纯接收初态、同一个全域 CPTP 接收通道以及任意丢弃环境均保持不变。结论仅使用第二、第三终端，不使用实代数正最小值界。

**显式结论与保真度约定。**

来源为

$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,\qquad
T|i\rangle=m_i\otimes|i\rangle_{\mathcal B},\qquad
|a|^2+|b|^2=1,\quad ab\ne0.
\tag{40.1}
$$

接收器 $K=\mathbb C^2$ 从纯态 $e$ 启动，每轮重复同一个全域 CPTP 通道
$\mathcal C:\mathcal L(K\otimes\mathcal B)\to\mathcal L(K)$。固定一份全域 Stinespring 等距
$V:K\otimes\mathcal B\to K\otimes E$。
只取来源初态 $|0\rangle_M$，接收联合态记为 $\sigma_n$，未接收的完整纯目标记为
$|\Psi_n\rangle_{M\mathcal B^{\otimes n}}$。

令 $f_n(\mathcal C)$ 为终端 $n$ 的最佳局部解码根保真度；所以
$f_n^2$ 是最佳解码后对纯目标投影的概率。置

$$
\gamma_2^{[3]}=\max_{\mathcal C}\min\{f_2(\mathcal C),f_3(\mathcal C)\},
\qquad Q_2^{[3]}=1-(\gamma_2^{[3]})^2.
\tag{40.2}
$$

最大值取得，但下面的逐装置论证不依赖寻找这个最大点。

记

$$
p=|b|^2,\qquad
r=\sqrt{(1-p)^2+p},\qquad
g=1-\frac{1-p}{r}\in(0,1).
\tag{40.3}
$$

真实记忆边缘满足

$$
\begin{aligned}
\rho_2&=(1-p)|m_0\rangle\langle m_0|
+p|0\rangle\langle0|,\\
\rho_3&=(1-p(1-p))|m_0\rangle\langle m_0|
+p(1-p)|0\rangle\langle0|.
\end{aligned}
$$

令

$$
\mu=\min\{\lambda_{\min}(\rho_2),\lambda_{\min}(\rho_3)\}
=\frac{1-\sqrt{1-4p^2(1-p)(1-p+p^2)}}2>0.
\tag{40.4}
$$

后一等号使用 $\det\rho_3=(1-p+p^2)\det\rho_2\le\det\rho_2$ 和迹一二阶矩阵的最小特征值公式。

**定理40.1（二维初等显式误差隙）。** 定义

$$
\epsilon_{\rm el}(p)=2^{-96}\mu^4g^{16}.
\tag{40.5}
$$

则

$$
\boxed{Q_2^{[3]}\ge\epsilon_{\rm el}(p).}
\tag{40.6}
$$

因此任意二维固定接收器及第二、第三终端解码器中，至少一个终端的指定输入完整半迹恢复误差不小于 $\epsilon_{\rm el}(p)$。
原来使用前32终端的指定输入不变量还满足

$$
\Delta_2\ge1-\sqrt{1-\epsilon_{\rm el}(p)}
\ge\epsilon_{\rm el}(p)/2.
\tag{40.7}
$$

完整参考合同包含这个指定输入，所以受相同必要下界约束；本定理没有把指定输入任务当成完整合同的充分条件。

若 $|a|^2,|b|^2\ge1/k$，$k\ge2$ 为整数，则有简洁的统一有理证书

$$
\boxed{
Q_2^{[3]}\ge\frac1{2^{116}k^{24}},
\qquad
\Delta_2\ge\frac1{2^{117}k^{24}}.
}
\tag{40.8}
$$

这些常数为保守值，不声称最优。

证明分为近纯性、同一门的首步约束和二维 Gram 稳定性三部分。

**维数二与满秩记忆把近恢复转为近纯化。**

先证明一个使用维数饱和的估计。设 $|\Gamma\rangle_{MKE}$ 是接收联合态
$\sigma_{MK}$ 的实际纯化，$\dim M=\dim K=2$，且
$\rho_M\succeq\mu I_M$。
若存在环境态 $\tau_E$ 满足

$$
D(\omega_{ME},\rho_M\otimes\tau_E)\le\delta,
\qquad
\omega_{ME}=\operatorname{Tr}_K|\Gamma\rangle\langle\Gamma|,
\tag{40.9}
$$

则

$$
\lambda_{\max}(\sigma_{MK})\ge1-\frac{2\delta}{\mu}.
\tag{40.10}
$$

为证此式，记 $\rho_M$ 的特征值为 $\alpha\ge\beta\ge\mu$，
$\tau_E$ 的特征值为 $t_1\ge t_2\ge\cdots$，不足两项时补零。
$\rho_M\otimes\tau_E$ 的最大特征值是 $\alpha t_1$，次大值是
$\max\{\beta t_1,\alpha t_2\}$。
若次大值为 $\beta t_1$，最大的两个特征值之和为 $t_1$；
否则其和至多 $\alpha(t_1+t_2)\le\alpha$，所以余下谱质量至少为
$\beta\ge\mu$。两种情况均给

$$
1-\|\rho_M\otimes\tau_E\|_{(2)}
\ge\mu(1-t_1),
\tag{40.11}
$$

其中 $\|\cdot\|_{(2)}$ 是最大的两个特征值之和。

$\omega_{ME}$ 的秩不超过 $\dim K=2$。用其支撑投影作为（40.9）的测量效果，
得到 $\|\rho_M\otimes\tau_E\|_{(2)}\ge1-\delta$，故
$1-t_1\le\delta/\mu$。再偏迹到 $E$，对 $\tau_E$ 的最大特征向量作投影，得
$\lambda_{\max}(\omega_E)\ge t_1-\delta$。
$\omega_E$ 与 $\sigma_{MK}$ 非零谱相同，因此

$$
\lambda_{\max}(\sigma_{MK})
\ge1-\delta/\mu-\delta\ge1-2\delta/\mu.
$$

这证明（40.10），不限制环境维数或其秩。

现在假设某终端最佳目标投影概率 $f_n^2\ge1-\epsilon$。
选择达到最优值的解码器，并对其取 Stinespring 等距。
将解码后全局纯态在真实目标方向上的分量归一化，就得到某环境态
$\tau_E$，使（40.9）以 $\delta=\sqrt\epsilon$ 成立。
这一过程只用目标投影概率，不要求预先有半迹误差上界。
于是对于 $n=2,3$，令

$$
t=\frac{2\sqrt\epsilon}{\mu},
$$

便有 $\lambda_{\max}(\sigma_n)\ge1-t$。

取最大特征向量 $\psi_n$。在实际纯化中，其对应环境向量可选为单位
$\zeta_n$，满足

$$
\|\Gamma_n-\psi_n\otimes\zeta_n\|
\le\sqrt{2t}.
$$

另一方面，$|\psi_n\rangle\langle\psi_n|$ 与 $\sigma_n$ 的半迹距离不超过
$t$，其记忆边缘与真实 $\rho_n$ 的距离也不超过 $t$。
由 Uhlmann 及 $F\ge1-D$，存在同一个二维 $K$ 上的纯化
$\phi_n$，满足 $\operatorname{Tr}_K|\phi_n\rangle\langle\phi_n|=\rho_n$ 且
$\|\psi_n-\phi_n\|\le\sqrt{2t}$。
因此

$$
\boxed{
\|\Gamma_n-\phi_n\otimes\zeta_n\|\le
\zeta:=\frac{4\epsilon^{1/4}}{\sqrt\mu},
\qquad n=2,3.
}
\tag{40.12}
$$

各纯态相位已选择使相关重叠为非负实数。稍后的反证阈值保证 $t<1$，所以全部近纯化选择都合法。

**第二步的近等距结构及首态混合程度。**

首步后记

$$
\Gamma_1=|m_0\rangle_M\otimes|\alpha\rangle_{KE_1},
\qquad
|\alpha\rangle=V(e\otimes|0\rangle),\qquad
\tau=\operatorname{Tr}_{E_1}|\alpha\rangle\langle\alpha|.
\tag{40.13}
$$

第二次发射的记忆—新位纯态为

$$
|\Theta\rangle=a|m_0\rangle|0\rangle_{\mathcal B}
+b|0\rangle|1\rangle_{\mathcal B}.
$$

它的记忆边缘为 $\rho_2\succeq\mu I$。定义等距

$$
A:\mathcal B\longrightarrow K\otimes E_2\otimes E_1,
\qquad
A|b\rangle=(V\otimes I_{E_1})(\alpha\otimes|b\rangle).
$$

（40.12）的 $\phi_2$ 和 $\Theta$ 是同一正定 $\rho_2$ 在二维纯化空间上的纯化，
所以存在酉 $U:\mathcal B\to K$，使
$\phi_2=(I_M\otimes U)\Theta$。把（40.12）应用于第二步，并使用
$\Theta$ 在新位上的最小 Schmidt 权重至少为 $\mu$，得到

$$
\boxed{
\|A-U\otimes\zeta_2\|_{\rm op}
\le\eta:=\frac{\zeta}{\sqrt\mu}
=\frac{4\epsilon^{1/4}}{\mu}.
}
\tag{40.14}
$$

具体地，对差算子 $B$，
$\|(I_M\otimes B)\Theta\|^2
=\operatorname{Tr}(\rho_{\mathcal B}B^*B)\ge\mu\|B\|_{\rm op}^2$。

记 $\lambda=\lambda_{\min}(\tau)$。
下面利用首步与第二步确实使用同一个 $V$，证明

$$
\boxed{\lambda\le\eta.}
\tag{40.15}
$$

若 $\lambda=0$ 无须证明。否则取 Schmidt 分解

$$
\alpha=\sum_{j=0}^1\sqrt{\lambda_j}\,q_j\otimes r_j,
\qquad
\lambda_0=1-\lambda,\quad\lambda_1=\lambda,
$$

并将 $\zeta_2$ 在 $E_1$ 的 $r_j$ 方向上的分量记为
$\xi_j\in E_2$。由（40.14），对 $b=0$，误差向量

$$
z_j=\sqrt{\lambda_j}\,V(q_j\otimes|0\rangle)
-U|0\rangle\otimes\xi_j
$$

满足 $\sum_j\|z_j\|^2\le\eta^2$；$\zeta_2$ 在其余 $E_1$ 方向的分量只会增加总误差。

写 $e=\sum_j c_jq_j$，并令 $P=|U0\rangle\langle U0|$ 为输出 $K$ 上投影。
由于 $P^\perp$ 消去各 $U0\otimes\xi_j$，Cauchy–Schwarz 给

$$
\begin{aligned}
\|(P^\perp\otimes I)V(e\otimes|0\rangle)\|
&=\left\|\sum_j\frac{c_j}{\sqrt{\lambda_j}}
(P^\perp\otimes I)z_j\right\|\\
&\le\left(\sum_j\frac{|c_j|^2}{\lambda_j}\right)^{1/2}
\left(\sum_j\|z_j\|^2\right)^{1/2}
\le\frac{\eta}{\sqrt\lambda}.
\end{aligned}
\tag{40.16}
$$

左侧平方恰为 $1-\langle U0|\tau|U0\rangle$，至少为 $\lambda$。
所以 $\lambda^2\le\eta^2$，得到（40.15）。

取 $k=q_0$ 为首态的最大特征向量，令 $\eta_1=r_0$。由（40.15），

$$
\|V(e\otimes|0\rangle)-k\otimes\eta_1\|
\le\sqrt{2\eta}.
\tag{40.17}
$$

若 $\tau$ 纯，按其唯一 Schmidt 项定义同样的 $k,\eta_1$。

将（40.14）投影到 $r_0$ 后，置 $w=\xi_0/\sqrt{\lambda_0}$，得

$$
\|V(k\otimes\cdot)-U(\cdot)\otimes w\|_{\rm op}
\le\eta/\sqrt{1-\eta}\le\sqrt2\,\eta
$$

（取 $\eta\le1/2$）。
$|\|w\|-1|\le\sqrt2\,\eta$；取 $\eta\le1/4$ 可将 $w$ 归一化为单位
$\eta_2$，并得到

$$
\boxed{
\|V(k\otimes|b\rangle)-u_b\otimes\eta_2\|
\le3\eta,\quad u_b=U|b\rangle,\quad b=0,1.
}
\tag{40.18}
$$

$u_0,u_1$ 是正交归一基。

**第三步作用在正确的理想前缀上。**

（40.12）中的 $\phi_2$ 具有正确的记忆边缘，且由 $U$ 写为

$$
\phi_2=a\,m_0\otimes u_0+b\,|0\rangle\otimes u_1.
$$

定义

$$
q=(a^2u_0+bu_1)/r.
$$

它单位，且 $|\langle q,u_0\rangle|=(1-p)/r=1-g$。

对理想前缀 $\phi_2$ 再作一次真实来源发射和真实接收 $V$，得到纯态
$\chi_3\in M\otimes K\otimes E_3$。实际第三步纯化 $\Gamma_3$ 与
$\chi_3\otimes\zeta_2$ 的向量距离至多 $\zeta$，因为实际第二步与
$\phi_2\otimes\zeta_2$ 的距离至多 $\zeta$，之后使用同一个等距。

又由（40.12），$\Gamma_3$ 与 $\phi_3\otimes\zeta_3$ 的距离至多 $\zeta$。
所以

$$
\|\chi_3\otimes\zeta_2-\phi_3\otimes\zeta_3\|\le2\zeta.
$$

对旧环境施以 $\langle\zeta_2|$，得到
$\|\chi_3-\phi_3\otimes w_3\|\le2\zeta$。
当 $2\zeta<1$ 时，归一化 $w_3$ 为单位 $\eta_3$，给

$$
\|\chi_3-\phi_3\otimes\eta_3\|\le4\zeta.
\tag{40.19}
$$

这一步保留旧环境整体相干，没有按环境分支选择不同接收门。

理想第三步的 $K\mathcal B$ Schmidt 支撑为

$$
S_3=\operatorname{span}\{q\otimes|0\rangle,u_0\otimes|1\rangle\}.
$$

它的记忆边缘是正确的 $\rho_3\succeq\mu I$，而 $\phi_3$ 也是该边缘的二维纯化。
再次用最小 Schmidt 权重除去源侧振幅，可得一组正交归一 $v_0,v_1$，使

$$
\boxed{
\|V(q\otimes|0\rangle)-v_0\otimes\eta_3\|\le4\eta,\qquad
\|V(u_0\otimes|1\rangle)-v_1\otimes\eta_3\|\le4\eta.
}
\tag{40.20}
$$

（40.17）、（40.18）、（40.20）涉及的所有实际输入和理想乘积输出均为单位向量。
因此不同块间每个内积的误差至多相应两项向量误差之和。
当 $\eta\le1$ 时，所有这些交叉 Gram 误差统一不超过

$$
\delta_G=8\sqrt\eta
=\frac{16\epsilon^{1/8}}{\sqrt\mu}.
\tag{40.21}
$$

**二维交叉 Gram 关系的显式稳定矛盾。**

下面只使用二维几何。将 $\delta_G$ 暂记为 $\delta$，假设

$$
\delta\le g^2/256.
\tag{40.22}
$$

令

$$
x=\langle k,q\rangle,\qquad y=\langle k,u_0\rangle,\qquad
c_{23}=\langle\eta_2,\eta_3\rangle.
$$

两个后续输入块的交叉 Gram 矩阵为 $\operatorname{diag}(x,y)$，相应理想输出的矩阵为 $c_{23}(\langle u_i,v_j\rangle)_{i,j=0}^1$。因此

$$
\max_{i,j\in\{0,1\}}
\left|\operatorname{diag}(x,y)_{ij}
-c_{23}\langle u_i,v_j\rangle\right|\le\delta,
$$

故矩阵算子范数误差至多 $2\delta$。
矩阵 $(\langle u_i,v_j\rangle)_{i,j=0}^1$ 是酉矩阵，奇异值扰动界给

$$
\big||x|-|y|\big|\le4\delta.
\tag{40.23}
$$

而

$$
|x|^2+|y|^2
=\langle k,(|q\rangle\langle q|+|u_0\rangle\langle u_0|)k\rangle
\ge1-|\langle q,u_0\rangle|=g.
$$

因此

$$
|c_{23}|\ge\sqrt{g/2}-2\delta\ge\sqrt g/4.
$$

非对角 Gram 项遂给

$$
|\langle u_0,v_1\rangle|,\ |\langle u_1,v_0\rangle|
\le4\delta/\sqrt g.
$$

适当选择 $v_i$ 相对于 $u_i$ 的比较相位，得到

$$
\min_{\theta}\|v_i-e^{i\theta}u_i\|
\le8\delta/\sqrt g,\qquad i=0,1.
\tag{40.24}
$$

令 $\beta=|\langle k,u_1\rangle|$，于是 $|y|=\sqrt{1-\beta^2}$。
由 $q$ 在 $u$ 基中的系数模为 $1-g,\sqrt{1-(1-g)^2}$，

$$
|x|\le(1-g)|y|+\beta.
$$

结合（40.23），有 $g|y|\le\beta+4\delta$。
若 $\beta\le g/4$，则 $|y|\ge1/2$，而（40.22）蕴含
$\delta\le g/32$，于是右侧至多 $3g/8$，左侧至少 $g/2$，矛盾。
所以

$$
\beta\ge g/4.
\tag{40.25}
$$

（40.22）还保证 $8\delta/\sqrt g\le g/8$，因此（40.24）给

$$
|\langle k,v_1\rangle|\ge g/8.
$$

首次输入与第二块的一位输入正交。其近似输出内积给

$$
|\langle\eta_1,\eta_2\rangle|\le4\delta/g.
$$

再比较首次输入与第二块的零位输入，得到

$$
|\langle e,k\rangle|\le5\delta/g.
$$

同理，首次输入与第三块的一位输入正交，得到
$|\langle\eta_1,\eta_3\rangle|\le8\delta/g$，
继而与第三块零位输入比较，得

$$
|\langle e,q\rangle|\le9\delta/g.
\tag{40.26}
$$

置 $h=9\delta/g<1$。二维空间中，$k,q$ 沿同一个 $e$ 的分量均不超过
$h$，故沿 $e^\perp$ 的分量模均至少为 $\sqrt{1-h^2}$。于是

$$
|x|=|\langle k,q\rangle|\ge1-2h^2.
$$

由（40.23），$|y|\ge1-2h^2-4\delta$，所以

$$
\beta^2=1-|y|^2
\le4h^2+8\delta
=\frac{324\delta^2}{g^2}+8\delta
\le\left(\frac{324}{256^2}+\frac8{256}\right)g^2
<g^2/16.
\tag{40.27}
$$

这与（40.25）矛盾。由此，只要（40.22）成立，就不存在这些近似块数据。

**常数闭合、统一来源界与适用边界。**

反设某个固定接收器有
$f_2^2,f_3^2\ge1-\epsilon_{\rm el}(p)$，在以上推导中取
$\epsilon=\epsilon_{\rm el}(p)$。
则

$$
\eta=4\epsilon^{1/4}/\mu=2^{-22}g^4<1/4,\qquad
\zeta=\eta\sqrt\mu<1/2,
$$

所有归一化条件成立；并且

$$
\delta_G=8\sqrt\eta=g^2/256.
$$

这恰落入二维几何矛盾范围。因此每个接收器至少有一个终端的最佳目标投影概率小于
$1-\epsilon_{\rm el}(p)$，取共同接收器最优值即得（40.6）。
对任意实际解码，半迹距离至少为目标投影概率的损失，因此得到操作误差下界。原来的前32终端目标更强，且
$1-\sqrt{1-x}\ge x/2$，于是（40.7）成立。

最后说明（40.8）。对归一化 $2\times2$ 正矩阵有
$\lambda_{\min}\ge\det$。写 $x=1-p$，则

$$
\mu=\lambda_{\min}(\rho_3)\ge\det\rho_3=p^2xr^2,
\qquad
g=\frac{p}{r(r+x)}.
$$

保留同一来源的归一化关系，便有

$$
\mu^4g^{16}
\ge\frac{p^{24}x^4}{r^8(r+x)^{16}}
\ge2^{-16}p^{24}(1-p)^4,
$$

其中用了 $r\le1$、$r+x\le2$。函数
$24\log p+4\log(1-p)$ 在 $[1/k,1-1/k]$ 上凹，
故最小值取在端点；当 $k\ge2$ 时左端值不大于右端值。因此

$$
p^{24}(1-p)^4
\ge\frac{(k-1)^4}{k^{28}}
\ge\frac1{16k^{24}}.
$$

代回（40.5），得到更细的统一估计及其简化式

$$
\epsilon_{\rm el}(p)
\ge\frac{(k-1)^4}{2^{112}k^{28}}
\ge\frac1{2^{116}k^{24}}.
$$

再用（40.7）即得（40.8）。
证明完毕。

本定理的必要性只取指定来源输入，完整参考任务因包含这一输入而继承下界。其证明没有假设实际接收态、首态或环境原本为纯态；（40.10）、（40.15）及三个近乘积块均由恢复精度、二维容量和同一固定通道推出。结论是 $D=2$ 的初等定量结果，不给一般 $D$ 的 $\exp(-CD)$ 或 $\exp(-CD^2)$ 下界。常数选择重在闭合全部误差传播，未作数值最优声明。

**校准例：同一存新位通道的三终端上界。**

用第38节的固定相位换基取 $a,b>0$，仍令 $r=\sqrt{a^4+b^2}$。
选择全域固定通道

$$
\mathcal C_{\rm store}(X)=\operatorname{Tr}_{K_{\rm old}}X,
\tag{40.28}
$$

把新发出位的二维空间固定识别为新的 $K$。首终端输出固定首位零，第二终端在当前接收位前附上首位零，因此这两个终端精确；接收门本身始终不变。

第三终端省去恒定首位零后，真实目标是

$$
a^2m_0\otimes|00\rangle
+ab\,m_1\otimes|01\rangle
+b\,m_0\otimes|10\rangle.
$$

定义正交归一档案向量

$$
\chi_0=(a^2|00\rangle+b|10\rangle)/r,\qquad
\chi_1=|01\rangle.
$$

第三终端解码取全域等距
$|0\rangle_K\mapsto|0\rangle\otimes\chi_0$、
$|1\rangle_K\mapsto|0\rangle\otimes\chi_1$。
在正交归一联合向量 $m_0\otimes\chi_0,m_1\otimes\chi_1$ 上，
目标和解码输出的矩阵分别为

$$
\begin{pmatrix}r^2&rab\\rab&a^2b^2\end{pmatrix},
\qquad
\begin{pmatrix}r^2&a^3b\\a^3b&a^2b^2\end{pmatrix}.
\tag{40.29}
$$

两矩阵迹均为一；区别只在这组联合正交向量上的两个非对角元。
因此这份完整联合恢复的半迹误差及目标投影损失分别为

$$
\delta_{\rm store}=ab(r-a^2),\qquad
q_{\rm store}=2a^2b^2r(r-a^2).
\tag{40.30}
$$

这给出

$$
\boxed{
\epsilon_{\rm el}(p)\le Q_2^{[3]}\le q_{\rm store},\qquad
\epsilon_{\rm el}(p)\le
\varepsilon^0_{2,[3]}\le\delta_{\rm store},
}
\tag{40.31}
$$

其中 $\varepsilon^0_{2,[3]}$ 是指定输入 $|0\rangle$、只要求前三终端的最佳最坏半迹误差。上界只用这份明确装置及解码器，不声称它们最优。

平衡来源 $a=b=1/\sqrt2$ 时，

$$
q_{\rm store}=\frac{3-\sqrt3}{8},\qquad
\delta_{\rm store}=\frac{\sqrt3-1}{4},
$$

而（40.8）给 $Q_2^{[3]}\ge2^{-140}$。
这一校准仅覆盖指定输入的前三终端；它既不是完整参考合同的上界，也不是前32终端 $\Delta_2$ 的上界。

## 追加锚（本行以下为增补区）

## 41. 任意有限终端固定接收的线性上界

本节继续固定已知来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，其中 $ab\ne0$、$|a|^2+|b|^2=1$。一步发射为 $|i\rangle_M\mapsto m_i\otimes|i\rangle_B$。接收器独立纯启动，每轮使用同一个全域 CPTP 通道，全部持久资源计入接收器；参考和活动记忆不可访问。每个终端 $n\le N$ 都须精确恢复完整参考—活动记忆—档案联合态。

**定理 41.1（共同固定通道的有限终端上界）。** 对任意整数 $N\ge6$，

$$
\boxed{d_{\mathrm{CPTP},N}(a,b)\le
\left\lceil\frac{3N}{2}\right\rceil-1.}
\tag{41.1}
$$

与第9节非退化来源的 $2N-1$ 维精确空白接收容量相比，本节利用允许丢弃环境的固定 CPTP 合同改进线性上界的系数。两者仍为线性阶；本节不声称容量最优，也不提供与 $N$ 无关的固定有限维接收器。

### 41.1 前五轮核心和二步递推

使用第39节的八维空间 $K_5=\operatorname{span}\{u,v,w,p,e,g,h,t\}$、（39.4）—（39.7）的向量及前五轮十一行

$$
\begin{array}{c|c@{\qquad}c|c}
w0&pA&p0&uB\\
w1&qA&p1&vB\\
z0&sA&q0&wB\\
u1&rA&f0&gB\\
x0&tA&s1&hB\\
g1&y_4A&&
\end{array}
\tag{41.2}
$$

其中 $A,B$ 为正交单位环境。前五轮的两个初始列为第39节（39.11）—（39.14）。特别地，

$$
\Psi_2^1=m_0w,\qquad
\Psi_5^0=\kappa m_0t+abd\,m_1y_4.
\tag{41.3}
$$

第六轮第一列两个输入为 $z_6 0,t1$，对应系数为 $a\lambda,b\kappa$；这两个输入与十一行核心全部输入正交。

记 $\eta_n=A$（$n$ 奇数）、$\eta_n=B$（$n$ 偶数），$F$ 为一次源发射和固定接收等距的联合映射。所有已经构造的轮次满足

$$
\Psi_n^1=a\Psi_{n-2}^0+b\Psi_{n-2}^1\qquad(n\ge2).
\tag{41.4}
$$

证明从 $\Psi_0^i=|i\rangle w$ 和 $\Psi_2^1=m_0w$ 开始。若第 $n$ 轮关系成立，则

$$
F\Psi_n^1
=(a\Psi_{n-1}^0+b\Psi_{n-1}^1)\otimes\eta_{n-1}
=(a\Psi_{n-1}^0+b\Psi_{n-1}^1)\otimes\eta_{n+1}.
\tag{41.5}
$$

右侧只调用第 $n-1$ 轮已经定义的作用，故同时给出下一轮第二列和共同环境；没有要求额外的新表行。因此后面只需构造第一列。

### 41.2 不同轮次使用的新增方向

若 $N=6$，第39节已经给维数八的结论。下文设 $N\ge7$。

对每个偶数 $n$，$6\le n<N$，增加一对正交单位向量 $P_n,Q_n$；对每个奇数 $n$，$7\le n<N$，只增加一个正交单位向量 $P_n$。所有这些新增向量彼此正交，且正交于 $K_5$。奇数轮的 $Q_n$ 将定义为上一偶数轮平面内的向量，不再增加维数。

中间轮数为 $N-6$，从偶数六开始交替增加二、一维。因此

$$
\begin{aligned}
\dim K
&=8+3\left\lfloor\frac{N-6}{2}\right\rfloor
  +2\bigl((N-6)\bmod2\bigr)\\
&=\left\lceil\frac{3N}{2}\right\rceil-1.
\end{aligned}
\tag{41.6}
$$

第六轮规定

$$
V(z_6 0)=P_6\otimes B,\qquad V(t1)=Q_6\otimes B.
\tag{41.7}
$$

于是

$$
\Psi_6^0=A_6m_0P_6+B_6m_1Q_6,\qquad
A_6=a\lambda,\quad B_6=b\kappa.
\tag{41.8}
$$

### 41.3 偶数中间轮用新平面，奇数中间轮复用正交补

已给第 $n-1$ 轮第一列

$$
\Psi_{n-1}^0=A_{n-1}m_0P_{n-1}+B_{n-1}m_1Q_{n-1}
\tag{41.9}
$$

后，对 $7\le n<N$ 置

$$
\begin{aligned}
s_{n-1}&=\sqrt{|aA_{n-1}|^2+|B_{n-1}|^2},\\
Z_n&=\frac{aA_{n-1}P_{n-1}+B_{n-1}Q_{n-1}}{s_{n-1}},\\
Y_n&=\frac{-\overline{B_{n-1}}P_{n-1}
       +\overline{aA_{n-1}}Q_{n-1}}{s_{n-1}},\\
A_n&=s_{n-1},\qquad B_n=bA_{n-1}.
\end{aligned}
\tag{41.10}
$$

$(Z_n,Y_n)$ 是上一对 $(P_{n-1},Q_{n-1})$ 平面的正交单位基。所有 $A_n,B_n$ 非零，所以各分母正。

若 $n$ 为偶数，使用第二部分已经新增的正交对 $(P_n,Q_n)$。若 $n$ 为奇数，定义

$$
Q_n=Y_n.
\tag{41.11}
$$

两种情况均规定

$$
V(Z_n0)=P_n\otimes\eta_n,\qquad
V(P_{n-1}1)=Q_n\otimes\eta_n.
\tag{41.12}
$$

于是第一列递推为

$$
\Psi_n^0=A_nm_0P_n+B_nm_1Q_n.
\tag{41.13}
$$

每个奇数中间轮只把上一新平面中与刚用零位输入正交的方向作为输出，另一个输出使用一维新方向。下一偶数轮再使用全新平面。

### 41.4 终端使用核心中尚未占用的环境输出方向

最后仍定义

$$
s_{N-1}=\sqrt{|aA_{N-1}|^2+|B_{N-1}|^2},\qquad
Z_N=\frac{aA_{N-1}P_{N-1}+B_{N-1}Q_{N-1}}{s_{N-1}}.
\tag{41.14}
$$

终端输出不再增加方向。若 $N$ 为偶数，规定

$$
V(Z_N0)=p\otimes B,\qquad V(P_{N-1}1)=e\otimes B.
\tag{41.15}
$$

若 $N$ 为奇数，规定

$$
V(Z_N0)=w\otimes A,\qquad V(P_{N-1}1)=x\otimes A.
\tag{41.16}
$$

前五轮环境 $B$ 的接收输出为 $u,v,w,g,h$，正交于 $p,e$；环境 $A$ 的接收输出为 $p,q,s,r,t,y_4$，正交于 $w,x$。所有中间轮输出都属于新增方向张成的空间。因此这两个终端选择均正交于全部同环境的既有输出，且各自为正交单位对。

最终第一列为

$$
\Psi_N^0=
\begin{cases}
s_{N-1}m_0p+bA_{N-1}m_1e,&N\text{ 偶},\\
s_{N-1}m_0w+bA_{N-1}m_1x,&N\text{ 奇}.
\end{cases}
\tag{41.17}
$$

### 41.5 整张表的输入和输出正交

每步增加一个零位输入和一个一位输入，不同位自动正交。

第六轮两个输入与核心正交。对后续零位输入分两类：

- 若其前一轮为偶数，$(P_{n-1},Q_{n-1})$ 是前一轮首次引入的全新平面，此前只用作输出，尚未出现于任何输入，所以 $Z_n0$ 正交于所有旧零位输入。
- 若其前一轮为奇数，则 $P_{n-1}$ 是新方向，$Q_{n-1}=Y_{n-1}$ 位于再前一轮的全新平面内。那个平面此前唯一的零位输入是 $Z_{n-1}$，而 $Y_{n-1}\perp Z_{n-1}$；更早的零位输入正交于整个新平面。因此 $Z_n0$ 仍正交于所有旧零位输入。

一位输入总为 $P_{n-1}1$；每个 $P_{n-1}$ 在前一轮首次加入，在该步首次作为一位输入，故正交于全部旧一位输入。这个论证同样覆盖最后一轮。

再看输出。偶数中间轮使用全新平面，因此正交于全部旧输出。奇数中间轮的 $P_n$ 是新方向，$Q_n=Y_n$ 位于上一偶数轮首次加入的平面中；该平面此前仅在环境 $B$ 下出现，而当前环境为 $A$，故两个新输出正交于全部旧输出。终端输出的正交性已在第四部分验证。

因此全部输入、输出各自构成正交单位族。总行数为 $11+2(N-5)=2N+1$，且

$$
2N+1\le2\left(\left\lceil\frac{3N}{2}\right\rceil-1\right)
\qquad(N\ge6).
\tag{41.18}
$$

可将两侧补为正交单位基，得到同一个全域酉 $V:K\otimes\mathbb C^2\to K\otimes\mathbb C^2$。逐轮第一列由表给出，第二列由第一部分的二步关系给出，所以两列每轮均输出同一纯环境 $\eta_n$。

### 41.6 参考完整的终端逆运算

令 $\mathcal C(X)=\operatorname{Tr}_E(VXV^*)$。任意终端 $n\le N$ 的解码器准备已知纯环境字 $\eta_1\cdots\eta_n$，逆序施加 $V^*$，恢复完整原始档案和独立接收初态 $w$，再丢弃 $w$。接收门与后续源发射作用于不交系统，故逆运算只在接收端运行。两个来源列保持同一环境，通过线性性保持任意参考及活动记忆关联，得到全部规定终端的精确联合恢复。

上述维数即为所述上界。它对每个预先给定有限 $N$ 构造一个固定通道，不把不同 $N$ 的终端独立最优值当成同一个无限时域实现。


## 追加锚（本行以下为增补区）

## 42. 一般整数边荷的相干窗口：字符合并、相位商与同轴增长

第33节每条边各有独立相位，不同长度必有不同字符，因而容量含乘法因子 $W$。一般整数边荷不具备这一性质：不同长度可以具有相同总荷，其振幅必须合成同一个相干向量。本节先给准确的精确容量与相位商，再证明一个长度窗口只沿已有荷方向拉长的实例。

仍取第31节的有限状态 primitive 行随机矩阵 $P$，支持边集为 $\mathcal E$，每条边保留完整正交标签，并赋整数荷 $g_{ij}\in\mathbb Z^q$。一步等距仍为（31.1）。取 $N\ge1$、$1\le W\le N+1$，记

$$
M_*=N+W-1,\qquad \mathcal I=\{N,\ldots,M_*\},\qquad
\mathcal A=\bigoplus_{n\in\mathcal I}B^{\otimes n}.
\tag{42.1}
$$

活动记忆写在前面，定义具有已固定跨长度相位的来源

$$
\mathcal T_{\theta;N,W}
=\frac1{\sqrt W}\sum_{n\in\mathcal I}(I_M\otimes\iota_n)T_{\theta,n},
\qquad\theta\in\mathbb T^q.
\tag{42.2}
$$

接收合同与第33节相同：共同全域 CPTP 编解码仅访问档案或接收器，对全部相位、任意初始活动记忆和任意外部参考恢复完整联合态。长度属于档案的一部分，不能作为免费旁信息测量。本节只给单终端块编码，不给在线生成、固定接收门或物理钟成本。以 $k_{N,W}^{\epsilon,\mathrm{coh}}(P,g)$ 表示最小接收维数。

### 42.1 同字符跨长度合并后的精确容量

对端点 $i,j$ 和长度 $n$，令 $C_n(i,j)$ 为可达总荷集合，并置

$$
C_{\mathcal I}(i,j)=\bigcup_{n\in\mathcal I}C_n(i,j).
\tag{42.3}
$$

对 $c\in C_{\mathcal I}(i,j)$，定义一个跨长度向量

$$
b_{ij,c}^{\mathcal I}
=\frac1{\sqrt W}
\sum_{n\in\mathcal I}
\sum_{\substack{\gamma:i\to j,\ |\gamma|=n\\g(\gamma)=c}}
\sqrt{p(\gamma)}\,|n,\gamma\rangle,
\qquad p(\gamma)=\prod_{e\in\gamma}P_e.
\tag{42.4}
$$

**定理42.1（一般标签的精确相干窗口容量）。** 对全部上述 $N,W$，

$$
\boxed{
k_{N,W}^{0,\mathrm{coh}}(P,g)
=\sum_{i,j}|C_{\mathcal I}(i,j)|.
}
\tag{42.5}
$$

证明。不同 $(i,j,c)$ 的向量（42.4）非零且正交。对固定相位，档案侧的端点支撑向量是

$$
\chi_{ij}^{\mathcal I}(\theta)
=\sum_{c\in C_{\mathcal I}(i,j)}
e^{i\theta\cdot c}b_{ij,c}^{\mathcal I}.
\tag{42.6}
$$

$N\ge1$ 和完整边标签使不同端点扇区正交。整数荷对应的环面字符线性无关，因此共同档案支撑恰为全部（42.4）的张成，维数等于（42.5）右侧。

为得到物理容量下界，对初始 $M$ 使用 $m$ 维 Bell 参考。精确保持其完整纯目标，强制共同恢复通道在每个 $\operatorname{span}\{\chi_{ij}^{\mathcal I}(\theta)\}$ 的全部算子上恒等。固定一份恢复通道的 Stinespring 等距；在这个支撑上，它必为 $x\mapsto x\otimes e_\theta$。端点向量连续且非零，所以邻近相位的同一端点向量内积非零，等距内积保持强制相应 $e_\theta$ 相等。连通环面使环境向量全局相同。线性性于是使恢复通道在整个共同档案支撑上恒等，编码必须在其算子空间上单射，故接收维数不小于该支撑维数。这正是定理32.3的共同 Stinespring 论证，所有条件在（42.6）中仍成立。

反向将整个共同支撑作一次等距编码，并在正交补上完成全域 CPTP 通道，得到精确上界。证明完毕。

式（42.5）使用荷集合的并集，不是各长度基数之和。一个 $b_{ij,c}^{\mathcal I}$ 保留同荷的全部长度相干，并没有识别或测量实际长度。独立边荷时，总荷的所有坐标之和就是长度，各长度集合不交，才恢复（33.2）。

### 42.2 纯势差子群、有限别名与连续维数

沿用（32.1）的关联矩阵 $\mathsf D$、边荷矩阵 $G$，记

$$
\begin{aligned}
\Lambda&=G\ker_{\mathbb Z}
\begin{pmatrix}\mathsf D\\\mathbf1^{\mathsf T}\end{pmatrix},
&L&=\operatorname{span}_{\mathbb R}\Lambda,\qquad r=\operatorname{rank}\Lambda,\\
\Lambda_0&=G\ker_{\mathbb Z}\mathsf D,
&r_0&=\operatorname{rank}\Lambda_0.
\end{aligned}
\tag{42.7}
$$

第31节固定长度子群为 $\mathcal H=\Lambda^\perp$。纯端点势差子群定义为

$$
\mathcal H_0=
\{h\in\mathbb T^q:\exists |z_i|=1,
e^{ih\cdot g_{ij}}=z_i\overline{z_j}\text{ 对全部支持边}\}.
\tag{42.8}
$$

这里的商仍指端点支撑的退化方向，含义与第31节相同。端点势差可能改变完整目标中的端点相干；它们被已有有限个端点支撑保存，并不是断言这些完整目标密度矩阵全都相同。

**命题42.2（相干窗口的格与商）。** 有

$$
\mathcal H_0=\Lambda_0^\perp,\qquad
\Lambda\subseteq\Lambda_0,\qquad r_0-r\in\{0,1\}.
\tag{42.9}
$$

更具体地，存在 $v\in\ker_{\mathbb Z}\mathsf D$ 满足 $\mathbf1^{\mathsf T}v=1$。令 $\gamma=Gv$，则

$$
\Lambda_0=\Lambda+\mathbb Z\gamma.
\tag{42.10}
$$

若 $\gamma\notin L$，则 $r_0=r+1$，且 $\mathcal H/\mathcal H_0$ 为一个圆群。若 $\gamma\in L$，则 $r_0=r$，但 $\mathcal H/\mathcal H_0$ 可以是非平凡有限循环群，其阶为满足 $d\gamma\in\Lambda$ 的最小正整数 $d$。特别地，商维数不增加不等于两个子群相同。

证明。强连通支持图中的整数循环满足：每个 $z\in\ker_{\mathbb Z}\mathsf D$ 都能写成两条同起终点实际路径的计数差。具体取严格正的整数循环计数 $c$，对充分大的整数 $k$，$kc$ 与 $kc+z$ 都有从同一顶点开始的 Euler 回路；这里不要求它们等长。因此 $\Lambda_0$ 正是所有同端点、允许不同长度的路径荷差生成的格。

纯势差沿同端点路径相消，所以 $\mathcal H_0\subseteq\Lambda_0^\perp$。反向，若所有整数循环荷的相位都为一，从固定根顶点沿路径定义顶点相位，闭走法相位为一保证定义与路径选择无关；每条边相位于是为端点相位比。因此 $\mathcal H_0=\Lambda_0^\perp$。

primitive 性使所有有向闭走法长度的最大公因子为一。对有限条长度作 Bézout 整数组合，得到长度一的有符号整数循环 $v$。任意 $z\in\ker_{\mathbb Z}\mathsf D$ 满足
$z-(\mathbf1^{\mathsf T}z)v\in\ker_{\mathbb Z}[\mathsf D;\mathbf1^{\mathsf T}]$，从而（42.10）成立。

对 $h\in\mathcal H$，其 scalar-plus-coboundary 表达中的标量相位唯一：两个表达之比沿任意闭走法给 $e^{i\Delta\omega |\gamma'|}=1$，长度最大公因子一迫使 $e^{i\Delta\omega}=1$。将表达乘在长度一循环 $v$ 上，得到

$$
\chi(h):=e^{ih\cdot\gamma}=e^{i\omega(h)},\qquad
\ker\chi=\mathcal H_0.
\tag{42.11}
$$

（42.10）使 $\Lambda_0/\Lambda$ 为由 $\gamma+\Lambda$ 生成的循环群。若 $\gamma\notin L$，此群为无限循环群，其对偶为圆群；若 $\gamma\in L$，整数格的有理结构保证存在上述最小正整数 $d$，商群及其对偶都是阶 $d$ 的循环群。这也给秩结论。证明完毕。

**有限窗口的准确条件。** 定义

$$
\Lambda_{N,W}
=\left\langle c-c':
 c,c'\in C_{\mathcal I}(i,j)\text{，某个共同端点 }i,j\right\rangle_{\mathbb Z}.
\tag{42.12}
$$

对于有限 $N,W$，端点支撑的准确相位子群是 $\Lambda_{N,W}^\perp$：同一端点向量（42.6）在相移后只乘一个标量，当且仅当所有所含字符获得同一相位。始终有 $\Lambda_{N,W}\subseteq\Lambda_0$。

存在仅依赖支持图与标签的整数 $N_0$，使

$$
\Lambda_{N,1}=\Lambda\quad(N\ge N_0),\qquad
\Lambda_{N,W}=\Lambda_0\quad(N\ge N_0,\ W\ge2).
\tag{42.13}
$$

证明。先取有限个实际等长同端点路径对，其荷差生成 $\Lambda$。如引理31.3的共同桥处理，把这些路径对加上共同前后缀，统一到一个起终点和一个长度。primitive 性允许继续加共同后缀，将它们放入每个充分大的指定长度 $N$；因此该长度的差格包含 $\Lambda$，反向包含本来成立。

再取同一对端点的 $N$ 步和 $N+1$ 步路径；充分大的 $N$ 保证两者都存在。其计数差 $z$ 是长度一整数循环，所以 $Gz-\gamma\in\Lambda$。只要窗口含这两个相邻长度，窗口差格便包含 $\Lambda$ 和 $\gamma$，由（42.10）得到 $\Lambda_0$。证明完毕。

这一区分保留有限长度的偶然退化；并未把 $W\ge2$ 单独当作全部小 $N$ 的充分条件。即使（42.13）使连续商增加一维，一个有界宽度的窗口也只在新方向给有限分辨率，不能仅凭商维数断言新增一个 $N$ 的幂次。

平稳边频率 $f_{ij}=\pi_iP_{ij}$ 满足 $\mathsf Df=0$、$\mathbf1^{\mathsf T}f=1$。令平稳漂移

$$
\mu=\sum_{i,j}\pi_iP_{ij}g_{ij}=Gf.
\tag{42.14}
$$

因为 $f-v\in\ker_{\mathbb R}[\mathsf D;\mathbf1^{\mathsf T}]$，有 $\mu-\gamma\in L$，所以

$$
\boxed{r_0=r+1\ \Longleftrightarrow\ \mu\notin L.}
\tag{42.15}
$$

若漂移已经在固定长度荷差空间中，相干长度无需增加连续商维数；它仍可以沿该空间中已有方向改变分辨尺度。

例如，在两态全正图上取 $g_{ij}=1+2j$，其中 $i,j\in\{0,1\}$，则（32.7）给 $\Lambda=2\mathbb Z$，而自环荷一给 $\Lambda_0=\mathbb Z$。故 $\mathcal H=\{0,\pi\}$、$\mathcal H_0=\{0\}$，两商都是一维。相移 $\pi$ 给每条边乘 $-1$：固定长度只有整体符号，相邻长度相干则使这个符号可见。这是消除有限别名，未增加连续维数。

### 42.3 伯努利标签：精确 $4M_*$，近似 $\sqrt N+W$

现在取

$$
m=2,\qquad P_{ij}=\frac12\quad(i,j\in\{0,1\}),\qquad g_{ij}=j\in\mathbb Z.
\tag{42.16}
$$

经典路径中的 $X_1,\ldots,X_n$ 是独立均匀位，总荷 $S_n=\sum_{t=1}^nX_t$ 为二项变量，初态 $X_0=i$ 不改变这一定律。完整边标签仍保留初始和终止状态，不能把来源替换成只保留成功数的经典装置。

**定理42.3（同一荷轴上的相干窗口容量）。** 对（42.16），全部 $N\ge1$、$1\le W\le N+1$ 满足

$$
\boxed{k_{N,W}^{0,\mathrm{coh}}=4(N+W-1).}
\tag{42.17}
$$

对每个 $0<\epsilon<1$，有显式界

$$
\boxed{
\frac{1-\epsilon}{12}(\sqrt N+W)
\le k_{N,W}^{\epsilon,\mathrm{coh}}
\le 2W+\frac8\epsilon\sqrt N+3.
}
\tag{42.18}
$$

因此固定正误差容量为 $\Theta_\epsilon(\sqrt N+W)$，常数统一于所列全部 $N,W$。这一模型的 $\mathcal H=\mathcal H_0=\{0\}$；长度相干没有增加相位商维数。

证明。对每个起点 $i$，终态 $j$ 决定最后一位，而此前 $n-1$ 位可以任意选择，所以

$$
C_n(i,0)=\{0,\ldots,n-1\},\qquad
C_n(i,1)=\{1,\ldots,n\}.
\tag{42.19}
$$

相同终态的荷集随 $n$ 嵌套，窗口并集分别为 $\{0,\ldots,M_*-1\}$ 和 $\{1,\ldots,M_*\}$。两种初态各有这两份集合，定理42.1立即给精确值 $4M_*$。此外，（32.7）的两个格基在 $G$ 下分别变为 $-1,1$，故 $\Lambda=\mathbb Z$，并且 $\Lambda_0=\mathbb Z$，得到两个平凡子群。

近似下界用 Bell 参考输入。按总荷合成完整联合向量后，目标及其 Haar 平均为

$$
|\Psi_\theta\rangle=\sum_k e^{ik\theta}|\beta_k\rangle,
\qquad
\overline\rho=\int_{\mathbb T}|\Psi_\theta\rangle\langle\Psi_\theta|\,d\theta
=\sum_k|\beta_k\rangle\langle\beta_k|.
\tag{42.20}
$$

这里 $\beta_k=2^{-1/2}\sum_{i,j}|i\rangle_J|j\rangle_M\otimes b_{ij,k}^{\mathcal I}$，不同 $k$ 正交。求和包括全部端点与同荷长度分量。准确的非零特征值是

$$
\nu(k)=\|\beta_k\|^2
=\frac1W\sum_{n=N}^{M_*}\binom nk2^{-n},
\tag{42.21}
$$

约定不可达的二项系数为零。其等式可直接从
$\Pr_i(S_n=k,X_n=j)=2^{-n}\binom{n-1}{k-j}$ 求和得到；初态数二与 Bell 归一化因子相消。

对每个 $n\ge1$，Fourier 反演及 $\cos u\le e^{-u^2/2}$（$0\le u\le\pi/2$）给

$$
\begin{aligned}
\max_k\binom nk2^{-n}
&\le\frac1{2\pi}\int_{-\pi}^{\pi}|\cos(t/2)|^n\,dt\\
&\le\sqrt{\frac2{\pi n}}\le n^{-1/2}.
\end{aligned}
\tag{42.22}
$$

另一方面，二项生成函数给每个 $k\ge0$ 的恒等式
$\sum_{n=k}^{\infty}\binom nk2^{-n}=2$。所以

$$
\|\overline\rho\|=\max_k\nu(k)
\le\min\{N^{-1/2},2/W\}
\le\frac3{\sqrt N+W}.
\tag{42.23}
$$

最后一步来自：若一个非负数同时不超过 $a/x$ 和 $b/y$，则不超过 $(a+b)/(x+y)$。

设共同编码维数为 $D_K$、共同解码为 $\mathcal D$，置 $\tau=\mathcal D(I_K)$，故 $\operatorname{Tr}\tau=D_K$。编码后的联合态不超过 $I_{JM}\otimes I_K$，解码正性使恢复态不超过 $I_{JM}\otimes\tau$。完整半迹误差至多 $\epsilon$ 给每个纯目标的投影概率至少 $1-\epsilon$。Haar 平均后，用 $\dim(JM)=4$ 得

$$
1-\epsilon
\le\operatorname{Tr}[\overline\rho(I_{JM}\otimes\tau)]
\le\frac{12D_K}{\sqrt N+W}.
\tag{42.24}
$$

这证明下界，没有测量长度或相位。

上界只保留整数荷带

$$
\mathcal B_{\rm good}
=\mathbb Z\cap
\left[\frac N2-\frac{\sqrt N}{\epsilon},\,
\frac{M_*}2+\frac{\sqrt N}{\epsilon}\right].
\tag{42.25}
$$

令 $\mathcal W_{\rm good}$ 是所有 $i,j$ 及 $k\in\mathcal B_{\rm good}$ 的完整跨长度向量 $b_{ij,k}^{\mathcal I}$ 的张成，$\Pi$ 为其投影。对窗口中任一长度，$\mathbb E_iS_n=n/2$ 位于荷带的中心区间，而
$\operatorname{Var}_i S_n=n/4\le N/2$。荷落在带外必有 $|S_n-n/2|>\sqrt N/\epsilon$，故 Chebyshev 不等式给每个初态、每个长度的漏出概率至多 $\epsilon^2/2$。

投影在实际来源支撑上保留或删去整个总荷分量，所以跨长度的总漏出是这些概率的等权平均。投影还保持初态首边标签扇区，因此严格有

$$
\mathcal T_{\theta;N,W}^*[I_M\otimes(I-\Pi)]
\mathcal T_{\theta;N,W}
\preceq\frac{\epsilon^2}{2}I_M
\tag{42.26}
$$

对全部相位成立，并可张量任意参考。

荷带内整数个数至多 $(W-1)/2+2\sqrt N/\epsilon+1$。每个荷至多有四个端点向量，所以将 $\mathcal W_{\rm good}$ 等距编码、再加一维失败旗标，所需维数不超过
$2W+8\sqrt N/\epsilon+3$。明确地，取等距 $F:\mathcal W_{\rm good}\to K_{\rm good}$ 并在正交补以零延拓，定义

$$
\begin{aligned}
\mathcal E(X)&=F\Pi X\Pi F^*
+\operatorname{Tr}[(I-\Pi)X]|\perp\rangle\langle\perp|,\\
\mathcal D(Y)&=F^*YF+\langle\perp|Y|\perp\rangle\tau_0,
\end{aligned}
\tag{42.27}
$$

其中 $\tau_0$ 是任一预定档案态。两者全域 CPTP；成功项是一个整体 Kraus 算子，保留所有选中向量之间的相干，包括不同长度与不同荷。对任意参考纯化，令纯目标的漏出为 $d\le\epsilon^2/2$，解码后的目标重叠至少 $(1-d)^2$，故半迹误差至多 $\sqrt{2d}\le\epsilon$。这证明上界和定理。证明完毕。

在此实例中，窗口均值由 $N/2$ 移到 $M_*/2$，仍在同一条总荷轴上。宽度 $W\ll\sqrt N$ 时，已有 $\sqrt N$ 波动尺度控制近似容量；宽度 $W\gg\sqrt N$ 时，均值区间长度控制容量。精确容量则始终计数合并后的荷值，不能把每个长度分别编码的维数相加作为必要下界。

### 42.4 协方差结构与尚未推出的结论

一般模型也具有与上述两种尺度相符的局部协方差结构。先令 Markov 链平稳启动，令 $L_{N,W}$ 独立地均匀取窗口长度，总荷为 $S_{L_{N,W}}$。有限 primitive 链的混合使平稳边荷的协方差级数绝对可和，并使其带一个滞后因子的级数也可和。因此存在渐近协方差矩阵 $\Sigma\succeq0$，满足
$\operatorname{Cov}(S_n)=n\Sigma+O_{P,g}(1)$，余项在算子范数中一致有界。全协方差公式给

$$
\operatorname{Cov}(S_{L_{N,W}})
=\left(N+\frac{W-1}{2}\right)\Sigma
+\frac{W^2-1}{12}\mu\mu^{\mathsf T}
+O_{P,g}(1).
\tag{42.28}
$$

这里 $O(1)$ 不依赖 $N,W$；平稳启动使各条件均值严格等于 $n\mu$。

而且

$$
\ker\Sigma=L^\perp,\qquad \operatorname{im}\Sigma=L.
\tag{42.29}
$$

一个直接证明使用有限链 Poisson 方程。令 $m_i=\sum_jP_{ij}g_{ij}$，取向量值解
$(I-P)u=m-\mu$；其存在来自 $\sum_i\pi_i(m_i-\mu)=0$。边增量
$\xi_{ij}=g_{ij}-\mu+u_j-u_i$ 条件均值为零，所以累积为 martingale，且
$S_n-n\mu=\sum_{t=1}^n\xi_{X_{t-1}X_t}+u_{X_0}-u_{X_n}$。边界项有界，除以 $n$ 后其方差及交叉项消失，从而
$\Sigma=\sum_{i,j}\pi_iP_{ij}\xi_{ij}\xi_{ij}^{\mathsf T}$。
方向 $h$ 位于其核，当且仅当
$h\cdot g_{ij}=h\cdot\mu+h\cdot u_i-h\cdot u_j$ 对全部支持边成立；这等价于 $h$ 消去全部等长同端点荷差，即 $h\in L^\perp$。等价性的反向也可从（32.3）的实线性核得到：消去 $G\ker_{\mathbb R}[\mathsf D;\mathbf1^{\mathsf T}]$ 的边函数位于该矩阵行空间中。由对称性即得像空间结论。

这些等式把固定长度的 $N\Sigma$ 波动与长度随机性的秩一项分开，但它们是局部二阶结构，不单独确定全局相位别名或一般容量。一个准确对照是：取各行相同的转移矩阵，使目的状态独立抽样。第一份来源的整数荷为 $-1,1$，概率各 $1/2$；第二份来源的整数荷为 $-2,0,2$，概率分别为 $1/8,3/4,1/8$。两者每步都具有 $\mu=0$、$\Sigma=1$，且任意窗口的总荷协方差都严格等于 $\mathbb E L_{N,W}$。但第一份有 $\Lambda=2\mathbb Z$、$\Lambda_0=\mathbb Z$，第二份有 $\Lambda=\Lambda_0=2\mathbb Z$。相干相邻长度只在第一份中消除相移 $\pi$ 的别名。相同协方差因而不能替代整数格条件。

本节确定一般标签的精确字符并集公式、相位商条件及伯努利实例的完整容量界。协方差公式提供二阶结构；一般容量估计还须结合最大荷概率与实际整数格。上面的反例证明，不能仅凭协方差恢复全局别名。

## 追加锚（本行以下为增补区）

## 43. 周期纯环境的线性下界与固定核心的精确容量

本节固定已知非退化来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，其中 $ab\ne0$、$|a|^2+|b|^2=1$。接收器从独立纯态启动，活动记忆和参考不可访问，每轮使用同一个全域 CPTP 通道，所有持久资源计入接收器；每个规定终端都要求完整参考—活动记忆—原始档案联合态的精确恢复。

第一项结果只要求同一 Stinespring 表示下的实际新环境为输入无关纯态，且按有限周期重复，不要求不同相位的环境正交，也不固定早期接收作用。第二项另外固定第25节的九行核心和正交交替环境，并求出这一较小实现类的精确容量。两项都不改变一般 CPTP 接收容量尚未收紧的下界。

### 43.1 周期纯环境的循环钟归约

**定理 43.1（周期纯环境的容量下界）。** 假设维数 $D$ 的接收器使用同一个 CPTP 通道，并且有一份固定 Stinespring 等距 $V:K\otimes\mathbb C^2\to K\otimes E$，其每轮实际新环境均是输入无关的单位纯向量 $\eta_n$。若存在整数 $k\ge1$ 使前 $N\ge2$ 轮满足 $\eta_{n+k}=\eta_n$（有定义时），则

$$
\boxed{kD\ge2N-1.}
\tag{43.1}
$$

因此 $D\ge\lceil(2N-1)/k\rceil$。特别地，任何纯 $ABAB\cdots$ 实现都满足 $D\ge N$，不要求固定第25节九行核心，也不要求 $A\perp B$。

证明：对任意输入纯态可将参考包括在内。初始接收态纯，且每轮丢弃环境为输入无关纯态，所以每轮接收后的参考—活动记忆—接收器仍纯，保留原输入相干。写第 $n-1$ 轮每个来源基态列为

$$
\Psi_{n-1}^i=|0\rangle x_{n-1}^i+|1\rangle y_{n-1}^i.
\tag{43.2}
$$

下一轮源发射后，$V$ 作用给

$$
m_0\otimes V(x_{n-1}^i0)+m_1\otimes V(y_{n-1}^i1).
\tag{43.3}
$$

因为 $m_0,m_1$ 线性无关、实际新环境属于 $\mathbb C\eta_n$，向该环境线的正交补投影可知

$$
V(x_{n-1}^i0),\ V(y_{n-1}^i1)\in K\otimes\mathbb C\eta_n.
\tag{43.4}
$$

对每个钟相位 $j=0,\ldots,k-1$，令 $D_j\subseteq K\otimes\mathbb C^2$ 是所有 $n-1\equiv j\pmod k$、$n\le N$ 的这些实际输入系数方向的线性张成。对有实际轮次的相位，周期性给

$$
V(D_j)\subseteq K\otimes\mathbb C\eta_{j+1},
\tag{43.5}
$$

对没有实际轮次的相位取 $D_j=0$。在非空相位上定义

$$
W_j=(I_K\otimes\langle\eta_{j+1}|)\,V|_{D_j}:D_j\to K.
\tag{43.6}
$$

空相位的 $W_j$ 取零维映射。$V$ 等距且其像在同一单位环境线上，所以每个 $W_j$ 都等距；特别地 $\dim D_j\le D$。

新增一个 $k$ 维持久循环钟 $C$，正交基为 $|j\rangle$。在 $(K\otimes C)\otimes\mathbb C^2$ 上定义部分作用

$$
U(\xi\otimes|j\rangle)
=W_j\xi\otimes|j+1\bmod k\rangle\otimes|0\rangle,
\qquad \xi\in D_j,
\tag{43.7}
$$

输入因子按固定次序重排。各输入钟相位正交，各输出下一钟相位也正交，每个块又等距。因此这是同一输入输出维数空间中的部分等距，可补全为全域酉。

初态为原接收初态乘 $|0\rangle_C$。逐轮应用同一个 $U$，在实际来源上复制原来的接收状态，钟相位循环推进，每个发出位都成为独立纯空白。全部持久容量是 $kD$，没有免费外部时变门。各终端可逆运行 $U$ 恢复完整档案及参考—活动记忆关联，故它满足第9节的非退化、独立纯初始化、同一固定酉、逐轮纯空白合同。

该合同精确最小维数为 $2N-1$，于是 $kD\ge2N-1$。证明完毕。

这里要求的是同一 Stinespring 表示下的实际输入无关纯环境周期。仅有有限维环境张成或有限种环境射线，不足以保证该周期前提；混合附加态也未由本定理处理。因此不从此推导一般 CPTP 接收容量的线性下界。

### 43.2 固定九行核心的受限合同

本节再固定第25节（25.39）的前四轮九行 Stinespring 作用，并要求各轮实际新环境为正交单位向量 $A,B$ 构成的确定交替字。允许环境空间更大、允许任意未指定输入上的等距完成；不把通道限制为置换矩阵，不预设后续接收方向正交或全新。

**定理 43.2（固定九行核心的精确容量）。** 在上述受限合同下，对每个 $N\ge5$，最小接收维数恰为

$$
\boxed{d^{\mathrm{core},AB}_N(a,b)
=\left\lceil\frac{3N}{2}\right\rceil-1.}
\tag{43.8}
$$

该下界只适用于固定九行核心和纯正交交替环境；它不是一般 CPTP 容量下界。

### 43.3 固定核心和输入—输出空间包含

沿用第39节（39.4）的 $c,d,z,q,f,s,r$，固定接收器中七个正交单位方向 $u,v,w,p,e,g,h$、初态 $w$，以及

$$
\begin{array}{c|c@{\qquad}c|c}
w0&pA&p0&uB\\
w1&qA&p1&vB\\
z0&sA&q0&wB\\
u1&rA&f0&gB\\
&&s1&hB
\end{array}
\tag{43.9}
$$

这里 $cs+br=df$，$z\in\operatorname{span}\{u,v\}$，且全部九个输入、九个输出各为正交单位族。

对任意已规定部分表及 $\eta\in\{A,B\}$，记：
- $D_\eta$ 是输出环境为 $\eta$ 的所有行的**接收器输入方向**张成空间，遗忘输入位；
- $O_\eta$ 是这些行的接收器输出方向张成空间。

本核心满足

$$
\begin{aligned}
D_A&=\operatorname{span}\{w,z,u\}
\subseteq \operatorname{span}\{u,v,w,g,h\}=O_B,\\
D_B&=\operatorname{span}\{p,q,f,s\}
\subseteq \operatorname{span}\{p,q,s,r\}=O_A.
\end{aligned}
\tag{43.10}
$$

这里 $D_A,D_B$ 未声明彼此正交；原输入位已经被遗忘。关键是交叉包含

$$
D_A\subseteq O_B,\qquad D_B\subseteq O_A.
\tag{43.11}
$$

### 43.4 实际第一列产生的两条新行

记第 $n$ 轮第一来源列为

$$
\Psi_n^0=A_nm_0P_n+B_nm_1Q_n.
\tag{43.12}
$$

已知前四轮可取

$$
\begin{array}{c|c|c|c|c}
n&A_n&B_n&P_n&Q_n\\ \hline
2&a&b&u&v\\
3&c&ab&s&r\\
4&ad&cb&g&h
\end{array}
\tag{43.13}
$$

其中每个 $(P_n,Q_n)$ 正交归一，且两系数非零。另取 $A_1=1$、$P_1=p$。

对 $n\ge4$，如果第 $n$ 轮第一列已为这种形式，下一轮发射的两个接收输入系数为

$$
aA_nP_n+B_nQ_n,\qquad bA_nP_n.
\tag{43.14}
$$

置

$$
A_{n+1}=\sqrt{|aA_n|^2+|B_n|^2}>0,\qquad
B_{n+1}=bA_n,\qquad
Z_{n+1}=\frac{aA_nP_n+B_nQ_n}{A_{n+1}}.
\tag{43.15}
$$

若下一轮要求共同纯环境 $\eta_{n+1}$，因为 $m_0,m_1$ 线性无关，向环境正交补投影实际发射—接收等式，分别得到

$$
V(Z_{n+1}0)=P_{n+1}\otimes\eta_{n+1},\qquad
V(P_n1)=Q_{n+1}\otimes\eta_{n+1}
\tag{43.16}
$$

的一对单位输出向量。等距性及输入位不同给 $P_{n+1}\perp Q_{n+1}$，故第一列继续具有同样形式。这是任何满足受限合同的实际装置都必须满足的两行，不是为了构造而另加的输入假设。

第5轮的两条输入具体为

$$
Z_5=x=\frac{a^2dg+cbh}{\kappa},\qquad P_4=g.
\tag{43.17}
$$

$x0,g1$ 正交于九行核心的全部输入。因此其两个新输出正交于旧的同环境 $A$ 输出。这给下面强制归纳的起点。

### 43.5 全表正交由固定等距强制

断言：把每轮第一列强制产生的两行依次加入核心后，全部已加入输入、输出各为正交单位族，并且交叉包含 $D_A\subseteq O_B,D_B\subseteq O_A$ 始终成立。

核心以及第5轮已经核对。假设结论已到第 $n$ 轮。其最新接收输出 $P_n,Q_n$ 正交于**加入这两行前**的同环境输出空间 $O_{\eta_n}^{\mathrm{old}}$。下一轮输入 $Z_{n+1},P_n$ 属于 $\operatorname{span}\{P_n,Q_n\}$。

对下一轮同环境 $\eta_{n+1}\ne\eta_n$ 的任一旧输入行，其接收方向属于

$$
D_{\eta_{n+1}}^{\mathrm{old}}
\subseteq O_{\eta_n}^{\mathrm{old}},
\tag{43.18}
$$

所以两个新接收输入方向均与之正交，因而同输入位的完整输入正交。

对环境 $\eta_n$ 的任一旧行，新的实际输出处在 $K\otimes\eta_{n+1}$，旧输出处在 $K\otimes\eta_n$，两环境正交。固定 $V$ 等距，故相应完整输入也正交。不同输入位之间本来就正交；两个新行之间亦然。

所以新输入与全部旧输入正交，固定等距使新输出与全部旧输出正交。最后，两个新输入接收方向位于上一轮输出空间 $O_{\eta_n}$，因此新扩大的 $D_{\eta_{n+1}}$ 仍包含于 $O_{\eta_n}$；另一项包含未改变。归纳完成。

特别地，所有零位接收输入

$$
w,p,q,Z_3,Z_4,\ldots,Z_N
\tag{43.19}
$$

构成正交单位族，其中 $Z_3=z$、$Z_4=f$。所有一位接收输入

$$
w,p,P_2,P_3,\ldots,P_{N-1}
\tag{43.20}
$$

也构成正交单位族。这两族之间可以有非零交叠；没有将它们合并为一个正交族。

### 43.6 来源决定两族交叠的严格奇偶分离

置

$$
\alpha_n=|A_n|^2,\qquad x_0=|a|^2,\qquad y_0=|b|^2.
\tag{43.21}
$$

由于第一列单位且 $P_n\perp Q_n$，

$$
|A_n|^2+|B_n|^2=1.
\tag{43.22}
$$

因此 $|B_n|^2=y_0\alpha_{n-1}$，并有

$$
\alpha_1=1,\qquad
\alpha_n=1-y_0\alpha_{n-1}
=\frac{1-(-y_0)^n}{1+y_0}.
\tag{43.23}
$$

故

$$
\alpha_n-\alpha_{n+1}=(-1)^{n+1}y_0^n.
\tag{43.24}
$$

对于 $2\le n\le N-1$，记

$$
r_n=\frac{aA_n}{A_{n+1}}.
\tag{43.25}
$$

前四轮的既有系数相位按表保留；例如 $r_3=c/d$。所有这些系数都满足

$$
|r_n|^2
=x_0\frac{\alpha_n}{\alpha_{n+1}}
\begin{cases}
<x_0,&n\text{ 偶},\\
>x_0,&n\text{ 奇}.
\end{cases}
\tag{43.26}
$$

如果 $m,n$ 同奇偶，输出环境相同。$P_m$ 来自零位输入，$Q_n$ 来自一位输入，因此固定等距给 $P_m\perp Q_n$。结合第43.5节的 $P_n$ 正交族和 $Z_{n+1}$ 公式（$n=2,3$ 分别由 $Z_3=z,Z_4=f$ 直接核对），得到

$$
\langle P_m,Z_{n+1}\rangle
=r_n\delta_{mn}
\qquad(m\equiv n\pmod2).
\tag{43.27}
$$

不同奇偶的交叠不预设为零。

### 43.7 收缩矩阵的秩缺陷下界

取两个长度 $L=N-2$ 的正交单位族

$$
(P_n)_{n=2}^{N-1},\qquad (Z_{n+1})_{n=2}^{N-1},
\tag{43.28}
$$

令其交叠矩阵为

$$
M_{mn}=\langle P_m,Z_{n+1}\rangle.
\tag{43.29}
$$

它是两个等距嵌入的交叠矩阵，所以 $\|M\|\le1$。按偶、奇指标排序，

$$
M=
\begin{pmatrix}
D_{\mathrm e}&U\\
W&D_{\mathrm o}
\end{pmatrix},
\tag{43.30}
$$

其中 $D_{\mathrm e},D_{\mathrm o}$ 分别是相应 $r_n$ 组成的对角矩阵，偶指标数

$$
e_N=\left\lfloor\frac{N-1}{2}\right\rfloor.
\tag{43.31}
$$

由 $M^*M\preceq I$ 的奇列主块，

$$
U^*U+D_{\mathrm o}^*D_{\mathrm o}\preceq I.
\tag{43.32}
$$

第43.6节使 $D_{\mathrm o}^*D_{\mathrm o}\succ x_0 I$。指标有限，所以

$$
\|U\|^2<1-x_0.
\tag{43.33}
$$

同时 $D_{\mathrm e}D_{\mathrm e}^*\prec x_0I$。因此 $I-MM^*$ 的偶行主块满足

$$
I-D_{\mathrm e}D_{\mathrm e}^*-UU^*\succ0.
\tag{43.34}
$$

这个主块维数为 $e_N$，故

$$
\operatorname{rank}(I-MM^*)\ge e_N.
\tag{43.35}
$$

两个正交族的联合 Gram 矩阵为

$$
\begin{pmatrix}I&M\\M^*&I\end{pmatrix}.
\tag{43.36}
$$

可逆分块消元给其秩为

$$
L+\operatorname{rank}(I-M^*M)
=L+\operatorname{rank}(I-MM^*).
\tag{43.37}
$$

因此两个族共同张成的接收子空间至少有 $L+e_N$ 维。

第43.5节又给 $w,p$ 彼此正交，且同时正交于上述两个族。所以

$$
\begin{aligned}
\dim K
&\ge L+e_N+2\\
&=N+\left\lfloor\frac{N-1}{2}\right\rfloor\\
&=\left\lceil\frac{3N}{2}\right\rceil-1.
\end{aligned}
\tag{43.38}
$$

### 43.8 达到与范围

当 $N=5$ 时，第25节十一行表在固定九行后追加 $x0\mapsto gA$、$g1\mapsto hA$，给七维达到。当 $N\ge6$ 时，第41节构造保留同一九行核心及确定正交交替环境，给 $\lceil3N/2\rceil-1$ 维达到。因此受限精确值成立。

特别地，该实现类在 $N=5,6,7,8,9,10$ 的精确容量为

$$
7,\ 8,\ 10,\ 11,\ 13,\ 14.
\tag{43.39}
$$

这里的必要正交由固定九行核心和交替环境共同推出。去掉其中任一条件，第43.5节的强制归纳没有建立；所以该结论没有排除一般七维六终端或一般九维七终端 CPTP 接收器，也不升级为一般线性容量下界。

## 追加锚（本行以下为增补区）

## 44. 一般整数边荷相干长度窗口的容量三分律

沿用第42节有限 primitive 行随机矩阵 $P$、完整边标签、整数边荷 $g$ 和相干均匀长度窗口的来源与完整参考块编码合同。所有相位遍历整个 $\mathbb T^q$。写 $M_*=N+W-1$，其中 $1\le W\le N+1$。以下常数允许依赖固定的 $P,g$，误差常数另依赖固定 $0<\epsilon<1$，但不依赖 $N,W$。

记
$$
\Lambda=G\ker_{\mathbb Z}[\mathsf D;\mathbf1^{\mathsf T}],\qquad
L=\operatorname{span}_{\mathbb R}\Lambda,\qquad r=\dim L,
\qquad \mu=\sum_{i,j}\pi_iP_{ij}g_{ij}.
$$
第42节已给 $\Lambda_0=G\ker_{\mathbb Z}\mathsf D=\Lambda+\mathbb Z\gamma$，且 $\mu-\gamma\in L$。整数格及其有限别名保留为实际模型数据。

**定理44.1（相干窗口的三个统一容量尺度）。** 对所有充分大的 $N$ 和全部 $1\le W\le N+1$，
$$
k_{N,W}^{\epsilon,\mathrm{coh}}(P,g)\asymp_{P,g,\epsilon}
\begin{cases}
W N^{r/2},&\mu\notin L,\\
N^{(r-1)/2}(\sqrt N+W),&0\ne\mu\in L,\\
N^{r/2},&\mu=0.
\end{cases}
\tag{44.1}
$$
第二种情形自动有 $r\ge1$。第一种允许 $r=0$，此时尺度为 $W$；第三种允许 $r=0$，此时容量保持有界。本定理只要求每个给定窗口的一次共同块编解码，不提供一个固定接收门、因果在线实现或适应性停止保证。

### 44.1 固定长度最大原子的统一上界

从初始状态 $i$ 出发，记经典边路径总荷为 $S_n$，末状态为 $X_n$，并定义
$$
p_n(i,j,c)=\Pr_i(X_n=j,S_n=c),\qquad c\in\mathbb Z^q.
$$

引理31.3的有限矩阵谱幂估计（31.9）给
$$
\|P(\theta)^n\|_{\infty\to\infty}\le C\exp\{-c_0n\,d(\theta,\mathcal H)^2\},\qquad
P(\theta)_{ij}=P_{ij}e^{i\theta\cdot g_{ij}},\qquad
\mathcal H=\Lambda^\perp.
\tag{44.2}
$$
所有模一外围点已经包含在完整闭子群 $\mathcal H$ 中，包括其有限连通分支；不能只使用其切空间。Fourier 反演给
$$
p_n(i,j,c)=\int_{\mathbb T^q}
e^{-i\theta\cdot c}(P(\theta)^n)_{ij}\,d\theta.
$$
这里 Haar 测度归一化。商环面 $\mathbb T^q/\mathcal H$ 的维数为 $r$，其固定平坦度量的小球体积为 $O(t^r)$；积分（44.2）于是给
$$
\boxed{\sup_{i,j,c}p_n(i,j,c)\le C_1 n^{-r/2}\qquad(n\ge1).}
\tag{44.3}
$$
$r=0$ 时积分只给常数，正是所需的退化情形。这一步仅复用固定长度谱估计，并未假设无算术周期或标签格饱和。

### 44.2 非平稳初态下的指数尾与路径二分

给向量值状态函数 $u$ 解有限链 Poisson 方程
$$
(I-P)u=\bar g-\mu,\qquad
\bar g(i)=\sum_jP_{ij}g_{ij}.
$$
因为右侧在平稳律下均值为零，且 $P$ primitive，解存在。置
$$
\xi(i,j)=g_{ij}-\mu+u(j)-u(i).
$$
这些向量条件均值为零、范数一致有界，并且对任意初态都有
$$
S_n-n\mu=\sum_{t=1}^n\xi(X_{t-1},X_t)+u(X_0)-u(X_n).
\tag{44.4}
$$
对任意一个坐标，若对应第 $t$ 步增量 $\xi_t$ 的绝对值至多 $B$，条件均值为零及凸性给条件指数矩界
$\mathbb E(e^{\lambda\xi_t}\mid\mathcal F_{t-1})\le e^{\lambda^2B^2/2}$。逐步取条件期望，再优化 Chernoff 参数 $\lambda$，得该坐标的双侧尾界 $2e^{-s^2/(2nB^2)}$。对有限个坐标并合，并吸收（44.4）的有界端点项，得到常数 $C_2,c_2>0$，使
$$
\boxed{\Pr_i(\|S_n-n\mu\|\ge t)
\le C_2e^{-c_2t^2/n}\qquad(n\ge1,t\ge0).}
\tag{44.5}
$$
若所有 martingale 增量为零，左侧仅由有界端点项产生，同样通过增大 $C_2$ 取得（44.5）。因此不要求协方差正定，也不要求初态平稳。

结合（44.3）和（44.5）可得包含前置因子的荷点上界。将 $n\ge2$ 分成 $n_1=\lfloor n/2\rfloor$、$n_2=n-n_1$。Markov 性给
$$
p_n(i,j,c)=\sum_\ell\sum_y
p_{n_1}(i,\ell,y)p_{n_2}(\ell,j,c-y).
\tag{44.6}
$$
若 $t=\|c-n\mu\|$，每个被加项至少满足
$$
\|y-n_1\mu\|\ge t/2
\quad\text{或}\quad
\|c-y-n_2\mu\|\ge t/2.
$$
在第一类项中，用（44.3）上界第二因子，再将第一因子求和，使用（44.5）；第二类交换两因子的角色。有限个中间状态只增加固定常数。因 $n_1,n_2\asymp n$，得到
$$
\boxed{p_n(i,j,c)\le C_3 n^{-r/2}
\exp\{-c_3\|c-n\mu\|^2/n\}.}
\tag{44.7}
$$
调整常数即可包括 $n=1$ 的有限支持。此处指数点界由最大原子与尾界共同推出，不引用未经核对的全局局部极限定理。

### 44.3 不同长度在荷空间中的位置

若 $\mu\notin L$，由 $\mu-\gamma\in L$，可取实线性泛函 $\ell$ 满足
$$
\ell|_L=0,\qquad \ell(\gamma)=\ell(\mu)=1.
$$
对同端点两条路径 $\alpha,\beta$，其计数差 $z$ 满足 $\mathsf Dz=0$，且
$Gz-(\mathbf1^{\mathsf T}z)\gamma\in\Lambda$。所以
$$
\ell(g(\alpha)-g(\beta))=|\alpha|-|\beta|.
\tag{44.8}
$$
因此，在固定端点 $i,j$ 后，一个总荷 $c$ 至多属于一个长度。固定长度 $n$ 的全部总荷又处在某个 $\Lambda$ 的陪集中；这个陪集的实方向空间为 $L$。

若 $\mu\in L$，则 $\gamma\in L$，故 $\Lambda_0$ 是 $L$ 中的一个满秩格。对同端点的全部长度，总荷都落在一个共同的 $\Lambda_0$ 陪集中。该陪集可以依赖端点，但无需依赖窗口。若 $\Lambda_0/\Lambda$ 是非平凡有限群，不同长度可以落在不同 $\Lambda$ 陪集，以下计数始终在较大的实际格 $\Lambda_0$ 内进行，保留这项有限别名差别。

### 44.4 Haar 平均目标与容量下界

取活动记忆与 $m$ 维参考的 Bell 输入。按第42节的同荷跨长度向量合成完整联合目标
$$
|\Psi_\theta\rangle=\sum_c e^{i\theta\cdot c}|\beta_c\rangle.
$$
不同 $c$ 的向量正交；Haar 平均目标的非零特征值为
$$
\nu(c)=\|\beta_c\|^2
=\frac1{mW}\sum_{n=N}^{M_*}\sum_{i,j}p_n(i,j,c).
\tag{44.9}
$$
此等式已经将同一个字符的不同长度相干合成，没有对长度作经典测量。

在 $\mu\notin L$ 情形，（44.8）说明每个端点对在（44.9）中至多有一个非零长度项；（44.3）给
$$
\max_c\nu(c)\le \frac{C}{W N^{r/2}}.
\tag{44.10}
$$

在 $0\ne\mu\in L$ 情形，先由（44.3）得 $\max_c\nu(c)\le C N^{-r/2}$。另一方面，对任意 $c$，令 $a_c=\langle c,\mu\rangle/\|\mu\|^2$。由于 $N\le n\le2N$，
$$
\sum_{n=N}^{M_*}e^{-c_3\|c-n\mu\|^2/n}
\le\sum_{n\in\mathbb Z}
e^{-(c_3\|\mu\|^2/(2N))(n-a_c)^2}
\le C\sqrt N.
$$
最后的格点高斯和界对任意中心 $a_c$ 一致，可按与中心的整数距离分组后比较积分。由（44.7）、（44.9）得
$$
\max_c\nu(c)\le C N^{-r/2}
\min\{1,\sqrt N/W\}
\le\frac{C'}{N^{(r-1)/2}(\sqrt N+W)}.
\tag{44.11}
$$
在 $\mu=0$ 情形，直接由（44.3）得到
$$
\max_c\nu(c)\le C N^{-r/2}.
\tag{44.12}
$$

以下同一个解码正性论证将三式转为容量下界。设共同接收维数为 $D_K$，解码为 $\mathcal D$，置 $\tau=\mathcal D(I_K)$，则 $\operatorname{Tr}\tau=D_K$。编码后的联合密度矩阵不超过 $I_{JM}\otimes I_K$，所以恢复态不超过 $I_{JM}\otimes\tau$。每个纯目标的投影概率至少为 $1-\epsilon$，Haar 平均后得到
$$
1-\epsilon\le
\operatorname{Tr}[\overline\rho(I_{JM}\otimes\tau)]
\le m^2D_K\|\overline\rho\|
=m^2D_K\max_c\nu(c).
\tag{44.13}
$$
代入（44.10）—（44.12），即得（44.1）的全部必要下界。

### 44.5 保持相干的荷管道上界

取只依赖 $P,g,\epsilon$ 的常数 $R\ge1$，并令半径 $a=R\sqrt N$。定义荷管道
$$
\mathcal T_{\rm good}
=\{c\in\mathbb Z^q:
\operatorname{dist}(c,[N\mu,M_*\mu])\le a\}.
\tag{44.14}
$$
对每个端点，只保留（42.4）中 $c\in\mathcal T_{\rm good}$ 的整个跨长度向量 $b_{ij,c}^{\mathcal I}$，其张成记为 $\mathcal W$，投影为 $\Pi$。

任意窗口长度的中心点 $n\mu$ 位于管道轴上；非平稳初态的实际均值不必严格等于该中心，（44.5）已经包括这个差别。一个荷未被保留，必有 $\|S_n-n\mu\|>a$。由（44.5）及 $n\le2N$，其概率至多 $C_2e^{-c_2R^2/2}$。选 $R$ 使此数不超过 $\epsilon^2/2$。首边起点扇区使漏出算子在初态基中对角，因而对全部相位和任意参考，
$$
\mathcal T_{\theta;N,W}^*
[I_M\otimes(I-\Pi)]\mathcal T_{\theta;N,W}
\preceq (\epsilon^2/2)I_M.
\tag{44.15}
$$
与（42.27）相同，对 $\mathcal W$ 作一次等距编码，增加一维失败旗标，在失败时输出固定档案态。成功项只有一个 Kraus 算子，保留所有选中荷和长度之间的相干。对任意参考纯化，若漏出为 $d\le\epsilon^2/2$，解码后与纯目标的重叠至少为 $(1-d)^2$，故半迹误差至多 $\sqrt{2d}\le\epsilon$。所需维数不超过 $\dim\mathcal W+1$。

剩下只需估计每个端点扇区中选中荷的数量。固定的秩 $r$ 格在任意半径 $a\ge1$ 的球内有 $O(a^r)$ 个点，常数对陪集和平移中心一致。可由格的固定基本域或最小点距的球打包得到；$r=0$ 时每个陪集至多一个点。

若 $\mu\notin L$，对每个固定长度分别使用其 $\Lambda$ 陪集。荷满足（44.8），所以固定长度的支持超平面与管道轴只在该长度附近相交；更直接地，可以把保留条件改为：对每个长度 $n$，保留 $\|c-n\mu\|\le a$ 的荷。端点和总荷唯一确定长度，故此条件仍选择整个 $b_{ij,c}^{\mathcal I}$，不分割同荷向量；（44.15）和原证明不变。每个长度有 $O(a^r)$ 个保留荷，总数 $O(Wa^r)$。

若 $0\ne\mu\in L$，全部荷处于一个 $\Lambda_0$ 陪集，且轴方向 $\mu$ 位于 $L$。将轴分成至多 $C(1+W/a)$ 段，每段长度不超过 $a$；管道被同样数量的半径 $3a$ 球覆盖。每球与该陪集至多相交 $O(a^r)$ 个格点，故所选荷数为
$$
O(a^r+Wa^{r-1})=O(N^{r/2}+WN^{(r-1)/2}).
\tag{44.16}
$$
陪集可位于 $L$ 的平移中，正交投影到其仿射支撑或直接使用最小格距，均给同一计数界。

若 $\mu=0$，管道退化为半径 $a$ 的球，每个端点陪集内至多有 $O(a^r)=O(N^{r/2})$ 个荷。

总端点数至多 $m^2$，失败旗标只加一维。以上三种上界与（44.13）的下界一致，证明（44.1）。

### 44.6 精确容量的二分律

**推论44.2（相同窗口的精确容量）。** 在同一模型与窗口范围内，
$$
k_{N,W}^{0,\mathrm{coh}}(P,g)\asymp_{P,g}
\begin{cases}
W N^r,&\mu\notin L,\\
N^r,&\mu\in L.
\end{cases}
\tag{44.17}
$$

证明。第32节的固定长度荷计数给
$\sum_{i,j}|C_n(i,j)|\asymp_{P,g}n^r$。
若 $\mu\notin L$，（44.8）使每个端点的不同长度荷集互不相交。第42节精确并集公式因而变成固定长度基数之和，在 $N\le n\le2N$ 上为 $\Theta(WN^r)$。

若 $\mu\in L$，每个端点的全部窗口荷位于一个秩 $r$ 的 $\Lambda_0$ 陪集中。边荷有界、路径长度至多 $2N$，故这些荷全部位于半径 $2N\max_e\|g_e\|$ 的球中；格点计数给每个端点 $O(N^r)$ 个荷。窗口又包含长度 $N$ 的全部荷，固定长度下界给 $\Omega(N^r)$。端点数固定，第42节精确并集公式完成证明。$r=0$ 时每个陪集至多一个点，论证仍然成立。

### 44.7 几何含义与合同边界

如果平均荷不在固定长度的波动空间 $L$ 中，改变长度沿一个新的方向移动支持，窗口贡献乘法因子 $W$。如果平均荷已经位于 $L$ 且非零，长度只把原波动空间中的一条轴由 $\sqrt N$ 拉长到 $\sqrt N+W$，其余 $r-1$ 条轴仍为 $\sqrt N$。如果平均荷为零，长度窗口不产生均值轴的额外拉长。

整数格决定精确字符与全部全局别名；最大原子和尾界决定固定正误差尺度。有限格指数可以改变常数与精确容量，以上推导未将其抹去，也没有仅由协方差矩阵猜测下界。结论统一于 $1\le W\le N+1$，不推及任意长窗口、任意相位候选子集、非 primitive 来源、经典去相干长度或同一个固定在线接收器。

## 追加锚（本行以下为增补区）

## 45. 无周期假设的纯轨道延拓与接收容量线性下界

### 45.1 有限维通道的纯轨道延拓

**引理45.1（有限纯前缀强制全时域纯轨道）。** 设 $\mathcal R$ 是 $d$ 维复 Hilbert 空间 $H$ 上的 CPTP 通道，$\sigma_0$ 是纯态，且 $\sigma_n=\mathcal R^n(\sigma_0)$。如果 $\sigma_0,\ldots,\sigma_{2d-1}$ 全为纯态，则所有 $\sigma_n$ 均为纯态。

这里不要求通道单酉、不要求不同时间的纯态正交，也不预设 Stinespring 环境周期。

证明。取有限 Kraus 表 $\mathcal R(X)=\sum_u K_uXK_u^*$。记 $N=2d-1$，为已知纯态选单位向量 $\psi_n$。正项之和秩一迫使

$$
K_u\psi_n=\kappa_{u,n}\psi_{n+1},\qquad
\sum_u|\kappa_{u,n}|^2=1,
\qquad 0\le n<N.
\tag{45.1}
$$

选取复数 $h_u$，避开有限个真超平面，使

$$
c_n:=\sum_u h_u\kappa_{u,n}\ne0\qquad(0\le n<N).
$$

令 $A=\sum_u h_uK_u$。于是 $A\psi_n=c_n\psi_{n+1}$，且 $A^n\psi_0$ 与 $\psi_n$ 共线，对 $0\le n\le N$ 均非零。

考虑循环空间 $H_c=\operatorname{span}\{A^n\psi_0:n\ge0\}$，维数为 $m\le d$。循环向量的最小多项式写为 $z^tq(z)$，其中 $q(0)\ne0$、$\deg q=r$、$t+r=m$。由于 $A^N\psi_0\ne0$ 且 $N\ge d$，该多项式不可能是纯幂，故 $r\ge1$。稳定循环空间

$$
R=A^tH_c
=\operatorname{span}\{A^{t+j}\psi_0:j\ge0\}
\tag{45.2}
$$

维数为 $r$，$A_R=A|_R$ 可逆，而 $y_j=A^{t+j}\psi_0$，$0\le j<r$，是 $R$ 的一组基。

因为 $t+r=m\le d\le N$，（45.1）覆盖这组基及其后继，故每个 $K_u$ 都保持 $R$。限制通道仍在 $R$ 上保迹。定义

$$
B_u=A_R^{-1}K_u|_R.
$$

每个 $y_j$ 是所有 $B_u$ 的共同本征向量，所以这些算子同时可对角化。将相同共同本征值元组的空间合并，得到代数直和

$$
R=S_1\oplus\cdots\oplus S_s,
\qquad s\ge1.
\tag{45.3}
$$

这些空间不要求正交。$\sum_u h_uB_u=I_R$。

对非零 $x\in R$，$\mathcal R(|x\rangle\langle x|)$ 秩一，当且仅当 $x$ 属于某个 $S_\alpha$。确实，秩一等价于所有 $K_ux$ 共线；$A_R$ 可逆，故等价于所有 $B_ux$ 共线。它们的线性组合为 $x$，所以每个 $B_ux$ 都是 $x$ 的标量倍数，即 $x$ 为共同本征向量。反向直接成立。在这些纯输入上，下一纯态方向为 $Ax$。

若 $s=1$，则整个 $R$ 都是纯输入空间，而且 $AR=R$，所以从时刻 $t$ 开始立即得到无限纯轨道。以下设 $s\ge2$。

对每个长度 $L\ge1$ 的环境类型词 $\alpha_0\cdots\alpha_{L-1}$，取非零线性空间

$$
C_{\alpha_0\cdots\alpha_{L-1}}
=\bigcap_{j=0}^{L-1}A_R^{-j}S_{\alpha_j},
\tag{45.4}
$$

将全部非零者组成族 $\mathscr C_L$。其并集恰为前 $L$ 个迭代方向全部属于纯输入集合的非零向量。每个 $\mathscr C_L$ 的成员构成代数直和族：$L=1$ 由（45.3）成立；延长一个符号时，每个旧成员被它与直和族 $A_R^{-L}S_\alpha$ 的交空间细分，因此各子空间仍为直和，不同旧成员之间也保持直和。

定义非负整数势

$$
\Phi_L=\sum_{C\in\mathscr C_L}(2\dim C-1).
\tag{45.5}
$$

一个 $q$ 维旧成员若产生 $k$ 个非零子空间，维数为 $q_1,\ldots,q_k$，则 $\sum_iq_i\le q$。如果 $k=0$，势下降 $2q-1\ge1$；如果 $k=1$ 且子空间真小，势至少下降二；如果 $k\ge2$，势至少下降 $k-1\ge1$。所以只要 $\mathscr C_{L+1}$ 与 $\mathscr C_L$ 不是完全相同的子空间族，就有 $\Phi_{L+1}<\Phi_L$。

一旦两族相同，每个旧成员恰有一个与自身相同的延长子空间。对该成员中的任意非零 $x$，向前作用 $A_R$ 后，其长度 $L$ 的后缀又落在 $\mathscr C_L$ 的一个成员内。因此该子空间并集前向不变，其中每个方向都产生无限纯轨道。

初始势满足

$$
\Phi_1=2r-s\le2r-2.
$$

已知纯轨道在时刻 $t$ 以后至少还有

$$
N-t=2d-1-t\ge2r-1
\tag{45.6}
$$

次纯输出，故 $y_0$ 属于 $\mathscr C_{2r-1}$ 的一个成员，特别地 $\Phi_{2r-1}\ge1$。如果前 $2r-2$ 次细分全严格，势将降到零，矛盾。所以在这之前已经稳定；$y_0$ 在相应稳定并集中，从而以后永远产生纯态。时刻 $t$ 之前也已知纯，证明完毕。

**命题45.1a（每个维数的精确纯轨道阈值）。** 对每个 $d\ge2$，存在一个 $d$ 维 CPTP 通道及纯初态，使时刻 $0,\ldots,2d-2$ 的态全部纯，而时刻 $2d-1$ 的态混合。因此引理45.1的阈值 $2d-1$ 对每个维数均为最小可能值。

证明：取正交单位基 $e_0,\ldots,e_{d-1}$，置

$$
v=\frac{e_0+e_1}{\sqrt2},\qquad
K_0=\sum_{i=0}^{d-2}|e_{i+1}\rangle\langle e_i|,
\qquad K_1=|v\rangle\langle e_{d-1}|.
$$

有

$$
K_0^*K_0=\sum_{i=0}^{d-2}|e_i\rangle\langle e_i|,
\qquad K_1^*K_1=|e_{d-1}\rangle\langle e_{d-1}|,
$$

所以 $\mathcal R(X)=K_0XK_0^*+K_1XK_1^*$ 是 CPTP。以 $e_0$ 为初始纯态方向，前 $d$ 个时刻依次为

$$
\psi_t=e_t\quad(0\le t\le d-1).
$$

下一步由 $K_1$ 复位到 $v$。其后，只要两个分量均未跨过最后一维，$K_0$ 将它们共同右移而 $K_1$ 为零。因此

$$
\psi_{d+j}=\frac{e_j+e_{j+1}}{\sqrt2},
\qquad 0\le j\le d-2.
$$

最后纯时刻恰为 $2d-2$；下一次分别由两份 Kraus 输出 $e_{d-1}/\sqrt2$ 与 $v/\sqrt2$，得到

$$
\sigma_{2d-1}
=\frac12|e_{d-1}\rangle\langle e_{d-1}|
+\frac12|v\rangle\langle v|.
$$

这两个方向在每个 $d\ge2$ 都线性独立，所以该态秩为二。$d=2$ 时两方向虽然不正交，仍线性独立，证明同样成立。结合引理45.1，得到每个维数上的精确阈值。$d=1$ 的轨道恒纯，另行平凡处理。证明完毕。

该例满足 $\mathcal R(I)=I-|e_0\rangle\langle e_0|+|v\rangle\langle v|\ne I$，所以不保单位；它与第45.4节更强的保单位特例并不冲突。

### 45.2 对固定来源接收的线性必要维数

仍取本卷非退化来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，$ab\ne0$，来源初态为 $|0\rangle_M$。接收器维数为 $D$，独立纯启动，使用同一个全域 CPTP 通道。

**推论45.2（任意纯终端接收类的线性必要维数）。** 如果接收后的实际 $MK$ 态在每个 $0\le n\le N$ 都纯，则

$$
\boxed{N\le4D-2,\qquad D\ge\left\lceil\frac{N+2}{4}\right\rceil.}
\tag{45.7}
$$

特别地，若要求一份固定 Stinespring 表示在这些轮次的实际新环境都是输入无关纯态，则该下界成立；这些纯环境可以任意非正交、无周期，也无需固定早期核心。

证明。一次来源发射与固定接收合成 $MK$ 上的固定 CPTP 通道 $\mathcal R$，其 Hilbert 空间维数为 $d=2D$。若 $N\ge4D-1$，引理使全部实际 $\sigma_n$ 均纯。每个 $\sigma_n$ 的来源边缘仍为真实的 $\rho_{M,n}$。记 $q_n=\operatorname{Tr}\rho_{M,n}^2$；纯双体态的两侧边缘具有相同非零谱，所以对全部 $n$ 有

$$
\operatorname{Tr}\sigma_{K,n}^2=q_n,\qquad
\operatorname{Tr}\sigma_n^2=1,
$$

从而直接满足第10节（10.8）的全时域纯度乘积恒等式。该节针对指定来源输入 $|0\rangle_M$ 的最低谱模矛盾排除了这种轨道，不需要引入未来解码器。故 $N<4D-1$，即（45.7）。

推论只需指定输入的实际联合态纯，不把它当作一般 CPTP 合同的自动后果。对一般完整参考合同，第23节的可逆编码结构在 $n\ge3$ 只给 $4r_n\le D$，其中 $r_n$ 是附加态秩；当 $D\ge8$ 时允许 $r_n\ge2$。因此（45.7）尚不能替代第12节的一般平方根下界。要取得一般线性下界，仍需把上述纯轨道有限延拓机制扩展到同一固定通道的混合可逆子系统轨道，或证明最小容量装置可保持纯终端而不增加维数。

### 45.3 一般小容量接收器的纯尾与有限终端障碍

完整参考合同可以在小容量下自动产生纯尾，不要求最早两个终端的接收态纯。

**推论45.3（七维以下的一般固定 CPTP 终端界）。** 对本卷已知非退化来源，设一个 $D\le7$ 维接收器从独立纯态启动，逐轮使用同一个全域 CPTP 通道，并精确服务全部 $1\le n\le N$ 的完整参考、活动记忆与档案恢复合同。则

$$
\boxed{N\le4D+1.}
\tag{45.8}
$$

特别地，一般七维固定 CPTP 接收器不能服务前三十个精确终端；因此 $N\ge30$ 时有 $d_{\mathrm{CPTP},N}(a,b)\ge8$。这里允许早期混合附加态，未对 Stinespring 环境的纯度、正交性、周期或维数另加限制。

证明。只需反设 $N\ge4D+2$，此时 $N\ge3$。取第23节的 Bell 参考输入；从第三轮开始，其真实档案的 Schmidt 秩为四，并在以后每轮保持为四。该节的可逆编码分解因而给每个 $3\le n\le N$ 的附加态秩 $r_n$ 满足

$$
4r_n\le D\le7.
\tag{45.9}
$$

若 $D<4$，第三终端本身已不可能；其余情形强制 $r_n=1$。于是累计编码在该终端的整个实际档案支撑上为单个等距，特别地，对指定初始来源 $|0\rangle_M$，实际 $MK$ 态 $\sigma_n$ 在所有 $3\le n\le N$ 均纯。此推断没有限制 $\sigma_1,\sigma_2$。

一次来源发射与固定接收仍为同一个 $2D$ 维空间上的通道 $\mathcal R$。从纯态 $\sigma_3$ 开始，已知的纯输出次数为 $N-3\ge4D-1$。引理45.1因此使实际轨道在每个 $n\ge3$ 均纯。沿用原来从 $|0\rangle_M$ 启动的真实来源纯度 $q_n$，得到

$$
\operatorname{Tr}\sigma_{K,n}^2=q_n,
\qquad\operatorname{Tr}\sigma_n^2=1,
\qquad n\ge3.
\tag{45.10}
$$

第10节的最低谱模反证只需要其（10.8）在一个整数尾部成立。具体地，（10.9）的 Jordan 轨道表达本来就先丢弃零特征值的有限幂零前缀；不同非零基底的指数多项式在整数尾部仍线性独立。若实际非零轨道基底的最小模为 $s>0$，联合纯度的正实基底 $s^2$ 具有非零正最高次系数，而 $q_n$ 中的正实基底 $p^2$ 具有严格正系数。乘积右侧因此出现 $p^2s^2<s^2$，偏迹侧却没有这样小的基底。删除任何有限前缀都不改变这一矛盾。所以（45.10）所给的尾部纯度恒等式已经不可能。

反设被排除，得到（45.8）。容量界对 $D\le7$ 统一成立，故 $N\ge30$ 必须 $D\ge8$。证明完毕。

这里的纯尾是四维档案支撑和 $D<8$ 共同强制的结果。当 $D\ge8$ 时，（45.9）允许混合附加态秩至少为二，上述归约不再成立；本推论没有将一般有限时域 CPTP 容量的平方根下界改为所有 $D$ 上的线性下界。

### 45.4 乘法域文献、保单位特例及非保单位桥梁

本节的细分势有明确的方法先例。Rahaman 在 [《Multiplicative properties of quantum channels》](https://doi.org/10.1088/1751-8121/aa7b57)（2017，Remark 2.7）引入乘法指数；Jaques–Rahaman 的 [《Spectral properties of tensor products of channels》](https://doi.org/10.1016/j.jmaa.2018.05.052)（2018，Lemma 3.5、Theorem 3.6）以势

$$
\chi(\mathcal A)=\sum_j(2n_j-1)
$$

控制有限维含幺 $*$-子代数链，并证明保单位、保迹的完全正通道在 $d\ge2$ 时满足

$$
\kappa(\Phi)\le2d-2.
\tag{45.11}
$$

这里的保单位意为 $\Phi(I)=I$，不意为通道由单个酉算子实现。上述标签对应 [arXiv:1710.00427v3](https://arxiv.org/pdf/1710.00427v3) 的 Lemma 3.5（第15—16页）及 Theorem 3.6（第16—17页）。Rahaman 的 [arXiv:1701.06205v4](https://arxiv.org/pdf/1701.06205v4) 给出较早的 $\kappa<d^2$ 讨论，不能作为（45.11）的出处。

这些既有结果还直接给出一个更强的保单位特例。设 $P$ 是秩一投影，$\Phi$ 保单位且 CPTP。如果 $\Phi^{2d-2}(P)$ 是纯态，则全部 $\Phi^n(P)$ 都是纯态，无须另行假设中间时刻纯。

证明：令 $k=2d-2$。纯输出是投影，而 $P^*P=PP^*=P$，故

$$
\Phi^k(P^*P)=\Phi^k(P)^*\Phi^k(P),\qquad
\Phi^k(PP^*)=\Phi^k(P)\Phi^k(P)^*.
$$

乘法域的 Schwarz 等号判据给 $P\in\mathcal M_{\Phi^k}$。乘法指数上界使该代数已稳定为 $\bigcap_{n\ge1}\mathcal M_{\Phi^n}$，所以每个 $\Phi^n(P)$ 均为投影。保迹使其迹为一，因此秩为一。$d=1$ 的情形直接成立。

引理45.1允许不保单位的 CPTP 通道，使用不要求正交的共同本征子空间及其细分。这些子空间尚未被等同于通道各次幂的乘法 $*$-代数；匹配的势函数不能替代该对应。取伴随也不自动补齐条件：任意 CPTP 通道的伴随保单位，但一般不保迹，而上述乘法域链结论使用了保迹性。Rahaman 的 [《A New Bound on Quantum Wielandt Inequality》](https://doi.org/10.1109/TIT.2019.2945776)（2020，Proposition 3.11）又明确证明，其保迹 Schwarz 映射自动保单位，因此该表述同样不能直接越过这里的非保单位边界。

命题45.1a给每个 $d\ge2$ 一份不保单位通道：它在 $2d-2$ 时仍纯，却在下一时刻混合，阻止了将保单位阈值原样推广。本节承认代数链势的方法先例，并给出自身所需的非保单位推导；对上述三篇原文的核对不等于穷尽相关文献，也不据此宣称本节结论的文献原创性。

## 追加锚（本行以下为增补区）

## 46. 伯努利相干窗口的有限误差证书

第42节确定伯努利标签来源的精确容量与固定正误差增长阶，第44节给一般标签的窗口三分律。本节保留误差参数，给每个有限窗口的可计算双界。上界来自一份明确的共同 CPTP 编解码，下界来自对任意编解码都有效的相位探针；只在该探针族内部优化下界，不把它称为全 CPTP 容量的最优值。

继续取两态来源 $P_{ij}=1/2$、$g_{ij}=j$，其中 $i,j\in\{0,1\}$，保留完整边标签。窗口为 $\{N,\ldots,M_*\}$，$M_*=N+W-1$，$N\ge1$、$1\le W\le N+1$；不同长度按（42.2）等幅相干叠加。所有相位遍历 $\mathbb T$，编解码共同固定且只作用于档案或接收器。记原来的任意参考、任意来源初态、全相位最坏半迹误差容量为 $k_{\rm mm}(\epsilon)$。

另定义较弱的 $k_{\rm av,Bell}(\epsilon)$：只取初始来源记忆与二态参考的 Bell 纯态，要求对相位 Haar 平均的半迹恢复误差不超过 $\epsilon$。它仍使用同一份与实际相位无关的全域 CPTP 编解码，但不要求其他来源输入或每个相位分别达到误差预算。因此

$$
k_{\rm av,Bell}(\epsilon)\le k_{\rm mm}(\epsilon).
\tag{46.1}
$$

下面的必要下界连这个较弱的平均合同也适用；构造上界则满足较强的全相位完整参考合同。两者没有被认作同一个最优化问题。

### 46.1 档案的端点与相位态分解

定义 $M_*$ 个严格正的有理权重

$$
a_\ell=\frac1W\sum_{n=N}^{M_*}
2^{-(n-1)}\binom{n-1}{\ell},
\qquad 0\le\ell\le M_*-1,
\qquad \sum_\ell a_\ell=1,
\tag{46.2}
$$

其中不可达二项系数取零。令

$$
|\psi_\theta\rangle_C
=\sum_{\ell=0}^{M_*-1}\sqrt{a_\ell}\,e^{i\ell\theta}|\ell\rangle_C,
\qquad
|\Phi_\theta\rangle_{MJ}
=\frac{|0,0\rangle+e^{i\theta}|1,1\rangle}{\sqrt2}.
\tag{46.3}
$$

这里 $J$ 是下文档案中的末态寄存器，外部参考另记为 $R$。

第42节的同荷跨长度向量满足

$$
\|b_{ij,k}^{\mathcal I}\|^2
=\frac1W\sum_{n=N}^{M_*}2^{-n}\binom{n-1}{k-j}
=\frac12a_{k-j}.
\tag{46.4}
$$

因此，全部共同档案支撑上存在一份已知的满射等距 $U_{\rm ar}$，把归一化向量 $b_{ij,k}^{\mathcal I}/\|b_{ij,k}^{\mathcal I}\|$ 送到
$|i\rangle_I\otimes|j\rangle_J\otimes|k-j\rangle_C$。其像为
$\mathbb C^2_I\otimes\mathbb C^2_J\otimes\mathbb C^{M_*}_C$，维数 $4M_*$。

由（42.6）逐项代入，任意初始联合态 $\rho_{RM_0}$ 的完整来源输出经这份档案换坐标后恰为

$$
\boxed{
\rho_{RI}\otimes
|\Phi_\theta\rangle\langle\Phi_\theta|_{MJ}
\otimes|\psi_\theta\rangle\langle\psi_\theta|_C.
}
\tag{46.5}
$$

这里 $M_0$ 的基被同名搬到 $I$，$M$ 是最终活动记忆。证明对初始基态 $|i\rangle$ 给
$|i\rangle_I\otimes|\Phi_\theta\rangle_{MJ}\otimes|\psi_\theta\rangle_C$，线性性保持任意输入叠加及参考，再延拓到混合态。$U_{\rm ar}$ 不依赖实际相位，不是长度测量；每个 $b_{ij,k}^{\mathcal I}$ 中的长度相干保持完整。

式（46.5）用于构造编码，并不是把原容量问题改成没有端点与参考的单个相位态任务。任意编码器仍可在三个档案因子之间联合操作；后面的下界不限制它采用上述张量分解式编码。

### 46.2 一份无额外旗标的截断复位码

将权重递减排序为 $a_{(1)}\ge\cdots\ge a_{(M_*)}>0$，只排序已知权重，保留每个所选项原来的整数相位频率。对 $1\le s\le M_*$，令 $S_s$ 为最大的 $s$ 项对应的频率集合，置

$$
p_s=\sum_{\ell\in S_s}a_\ell,
\qquad d_s=1-p_s,
\qquad a_*=a_{(1)}.
\tag{46.6}
$$

取 $\ell_*\in S_s$ 使 $a_{\ell_*}=a_*$。在 $C$ 上保留投影 $P_s$，将失败直接复位到 $|\ell_*\rangle$。编码到 $s$ 维空间并按原频率等距解码后的通道为

$$
\mathcal R_s(X)=P_sXP_s+
\operatorname{Tr}[(I-P_s)X]|\ell_*\rangle\langle\ell_*|.
\tag{46.7}
$$

这确实通过 $s$ 维系统分解：成功 Kraus 是从 $P_sC$ 到代码空间的等距，其他 Kraus 分别将每个未选频率送到同一个代码基态。保留整个 $I\otimes J$，故实际接收维数为 $4s$，不需再加失败旗标。将 $U_{\rm ar}$ 的定义在共同支撑外完成为任意 CPTP 编码，解码用其逆等距，得到整个原档案空间上的全域编解码。

对相位态，解码结果是

$$
\sigma_{s,\theta}
=P_s|\psi_\theta\rangle\langle\psi_\theta|P_s
+d_s|\ell_*\rangle\langle\ell_*|.
\tag{46.8}
$$

该通道与相位对角作用协变，故误差与 $\theta$ 无关；（46.5）及半迹距离对张量一个共同密度矩阵的不变性，使同一个数也是全部参考和全部初态的最坏误差。

**命题46.1（截断复位码的准确误差）。** 若 $d_s=0$，误差 $E_s=0$。若 $d_s>0$，其完整联合半迹误差 $E_s$ 是方程

$$
\boxed{E_s^3-d_sE_s-d_s^2(p_s-a_*)=0}
\tag{46.9}
$$

的唯一正根。因此，对 $0<\epsilon<1$，这份 $4s$ 维装置满足合同，当且仅当

$$
\boxed{\epsilon^3\ge d_s\epsilon+d_s^2(p_s-a_*).}
\tag{46.10}
$$

证明。只需在 $\theta=0$ 下计算，记 $p=p_s$、$d=d_s$，$|v\rangle=P_s|\psi_0\rangle$。差算子

$$
A=|\psi_0\rangle\langle\psi_0|
-|v\rangle\langle v|-d|\ell_*\rangle\langle\ell_*|
\tag{46.11}
$$

迹为零，且是一个秩一正算子减去正算子，所以至多有一个正特征值。其支撑至多由保留方向、保留方向内的 $|\ell_*\rangle$ 分量以及丢弃方向张成，维数至多三。

具体取单位 $|s_0\rangle=|v\rangle/\sqrt p$、单位丢弃方向 $|o\rangle$，并在保留空间中把
$|\ell_*\rangle=\sqrt t\,|s_0\rangle+\sqrt{1-t}\,|u\rangle$，其中相位可吸收且 $t=a_*/p$。在这组至多三维基中，$A$ 的矩阵为

$$
\begin{pmatrix}
-dt&-d\sqrt{t(1-t)}&\sqrt{pd}\\
-d\sqrt{t(1-t)}&-d(1-t)&0\\
\sqrt{pd}&0&d
\end{pmatrix}.
\tag{46.12}
$$

若 $t=1$，第二方向无须存在，可补一个零行列来计算同一特征多项式。直接计算得
$\operatorname{Tr}A^2=2d$、$\det A=d^2(p-a_*)$。故特征多项式是
$z^3-dz-d^2(p-a_*)$。$d>0$ 时 $A$ 非零，唯一正特征值等于半迹距离；多项式在正半轴上只有一个正根，得到（46.9）。对正的 $\epsilon$，多项式值非负当且仅当 $\epsilon$ 不小于这个根，得到（46.10）。证明完毕。

$\epsilon=0$ 不能不加区分地使用（46.10）：当 $s=1$ 时三次式还有零根，而真正误差是 $\sqrt{d_s}$。零误差统一由 $s=M_*$ 以及第42节精确容量处理。

### 46.3 对任意编码器有效的有限相位探针

给任意概率向量 $w=(w_0,\ldots,w_{M_*-1})$，定义探针相位态

$$
|\psi^w_\theta\rangle
=\sum_\ell\sqrt{w_\ell}e^{i\ell\theta}|\ell\rangle.
\tag{46.13}
$$

对固定 Bell 初始输入，在（46.5）的完整目标中只把 $|\psi_\theta\rangle$ 替换为 $|\psi^w_\theta\rangle$，得到单位探针 $|\Xi^w_\theta\rangle$。真实目标与探针的投影重叠恰为

$$
|\langle\Xi^w_\theta,\Psi_\theta\rangle|^2
=\left(\sum_\ell\sqrt{a_\ell w_\ell}\right)^2.
\tag{46.14}
$$

若 Bell 输入的 Haar 平均半迹误差不超过 $\epsilon$，测量这个依相位定义的探针投影并积分，恢复输出的平均投影概率至少为（46.14）减去 $\epsilon$。探针只用于下界证明，不要求编码器知道实际相位或实施这个测量。

设接收维数为 $D_K$、共同解码为 $\mathcal D$，记 $\tau=\mathcal D(I_K)$，故 $\operatorname{Tr}\tau=D_K$。每个编码联合态不超过 $I_{RM}\otimes I_K$，解码正性给恢复态不超过 $I_{RM}\otimes\tau$。将探针投影先对外部参考和活动记忆偏迹，再作相位 Haar 平均，在规范档案坐标中恰得

$$
\int\operatorname{Tr}_{RM}
|\Xi^w_\theta\rangle\langle\Xi^w_\theta|\,d\theta
=\frac{I_{IJ}}4\otimes
\sum_\ell w_\ell|\ell\rangle\langle\ell|.
\tag{46.15}
$$

其中最大特征值为 $\max_\ell w_\ell/4$。返回原档案支撑的等距不改变该谱，支撑外只有零特征值。因此

$$
\boxed{
D_K\ge
4\frac{\left(\sum_\ell\sqrt{a_\ell w_\ell}\right)^2-\epsilon}
{\max_\ell w_\ell}.
}
\tag{46.16}
$$

该必要界对任意共同 CPTP 编解码成立，包括联合操作端点与相位寄存器的编码器。它也适用于较弱的 Haar 平均 Bell 合同，所以当然适用于全相位最坏误差。这里精确使用探针平均态的档案边缘谱，没有把源 Haar 平均谱的最佳低秩截断当成全相位最优压缩，也没有把某个 Schmidt 切面的尾质量当成压缩合同的充分必要条件。

### 46.4 探针下界的有限排序解

令 $v_\ell=\sqrt{a_\ell}$。对 $0<\epsilon<1$ 定义

$$
\mathfrak L_a(\epsilon)
=\max_{0\le x_\ell\le1}
\left\{\left(\sum_\ell v_\ell x_\ell\right)^2
-\epsilon\sum_\ell x_\ell^2\right\}.
\tag{46.17}
$$

它恰为（46.16）右侧除以四后，对全部概率探针 $w$ 的最优值。因为由 $w$ 置 $x_\ell=\sqrt{w_\ell/\max w}$ 就得到同一目标；反向取 $w_\ell=x_\ell^2/\sum x_j^2$ 即可。该最大值为正，例如 $x=v/\max v$ 给 $(1-\epsilon)/a_*$；正值的最大点必有一个坐标达到一，否则可整体放大。

**命题46.2（探针优化的唯一阈值）。** 存在唯一正数 $c$ 满足

$$
\sum_\ell\min\left\{a_\ell,\frac{\sqrt{a_\ell}}c\right\}
=\epsilon.
\tag{46.18}
$$

（46.17）的一个最大点为 $x_\ell=\min\{1,c\sqrt{a_\ell}\}$。置
$H=\{\ell:c\sqrt{a_\ell}\ge1\}$、$h=|H|$、
$d_H=\sum_{\ell\notin H}a_\ell$、$S_H=\sum_{\ell\in H}\sqrt{a_\ell}$，则

$$
c=\frac{S_H}{\epsilon-d_H},\qquad
\boxed{\mathfrak L_a(\epsilon)
=\frac{\epsilon S_H^2}{\epsilon-d_H}-\epsilon h.}
\tag{46.19}
$$

证明。对非负数 $A$ 有 $A^2=\max_{t\ge0}(2tA-t^2)$。对 $x$ 和 $t$ 的两个最大值可以交换次序，因此（46.17）等于

$$
\max_{t\ge0}\left[
-t^2+\sum_\ell
\max_{0\le x\le1}(2t v_\ell x-\epsilon x^2)
\right].
\tag{46.20}
$$

内层最大点为 $x=\min\{1,tv_\ell/\epsilon\}$。所得外层函数连续可微；置 $t=\epsilon c>0$ 后，其导数的符号与
$\sum_\ell\min\{a_\ell,v_\ell/c\}-\epsilon$ 相同。该和从一开始，越过初始常值区后严格下降到零，所以对 $0<\epsilon<1$ 有唯一根。导数先正后负，该根给全局最大。集合 $H$ 非空，且（46.18）等价于
$\epsilon=d_H+S_H/c$，故 $d_H<\epsilon$。代回目标，得到（46.19）。证明完毕。

这个计算只需有限排序：对 $h=1,\ldots,M_*$ 依次取最大的 $h$ 个权重，计算相应 $d_h,S_h$。当 $\epsilon>d_h$ 且
$c_h=S_h/(\epsilon-d_h)$ 满足
$c_h\sqrt{a_{(h)}}\ge1\ge c_h\sqrt{a_{(h+1)}}$ 时，即得到所需值；约定 $a_{(M_*+1)}=0$。阈值处的并列权重不改变答案。这里只精确优化探针证书，没有证明其等于实际容量。

### 46.5 对全部有限误差的容量双界

对 $0<\epsilon<1$，定义

$$
s_a(\epsilon)=
\min\left\{1\le s\le M_*:
\epsilon^3\ge d_s\epsilon+d_s^2(p_s-a_*)\right\}.
\tag{46.21}
$$

全集 $s=M_*$ 总满足条件，所以这个整数必存在。

**定理46.3（有限窗口的平均下界与最坏误差上界）。** 对每个上述有限窗口和每个 $0<\epsilon<1$，

$$
\boxed{
\left\lceil4\mathfrak L_a(\epsilon)\right\rceil
\le k_{\rm av,Bell}(\epsilon)
\le k_{\rm mm}(\epsilon)
\le4s_a(\epsilon).
}
\tag{46.22}
$$

证明。必要下界是（46.16）对全部探针的优化，并使用维数为整数；中间不等式是合同包含。充分上界由命题46.1给出的明确 $4s_a(\epsilon)$ 维编解码达到，其误差对所有相位和任意参考输入均等于相应 $E_s$。证明完毕。

例如，仅取探针 $w=a$ 或在最大的 $h$ 个权重上取均匀分布，就分别给可直接使用的弱化证书

$$
D_K\ge\frac{4(1-\epsilon)}{a_*},\qquad
D_K\ge4\left[
\left(\sum_{j=1}^h\sqrt{a_{(j)}}\right)^2-h\epsilon
\right].
\tag{46.23}
$$

前者完全由有理权重与误差给出；优化式（46.19）可以进一步加强它们。

端点误差也可明确处理。$\epsilon=0$ 时，平均误差为零使连续且非负的相位误差处处为零；Bell 输入上的精确恢复是来源输入通道的 Choi 等式，因而保持全部初始输入。第42节于是给
$k_{\rm av,Bell}(0)=k_{\rm mm}(0)=4M_*$。$\epsilon=1$ 时任何两个态的半迹距离至多一，一维固定输出已经满足两个合同，故两容量都是一。

式（46.22）对 $N,W,\epsilon$ 是逐实例的有限证书，不要求 $\epsilon$ 随 $N$ 保持常数。对于有理 $\epsilon>0$，（46.21）的可行性只需比较有理数，不必数值求解三次根。下界则由有限个平方根、排序和（46.19）确定。

### 46.6 分位数形式与误差依赖

命题46.1还给

$$
\sqrt{d_s}\le E_s\le
\delta(d_s):=\frac{d_s+\sqrt{4d_s-3d_s^2}}2.
\tag{46.24}
$$

左侧由三次方程及 $p_s-a_*\ge0$ 得到。右侧可直接用（46.11）：删去负项 $-d_s|\ell_*\rangle\langle\ell_*|$ 只会增大最大特征值，而剩余秩二算子的正特征值正是 $\delta(d_s)$。

对 $0<\epsilon<1$，置

$$
\eta(\epsilon)
=\frac{1+\epsilon-\sqrt{(1-\epsilon)(1+3\epsilon)}}2
=\frac{2\epsilon^2}
{1+\epsilon+\sqrt{(1-\epsilon)(1+3\epsilon)}}.
\tag{46.25}
$$

$\delta(d)\le\epsilon$ 当且仅当 $d\le\eta(\epsilon)$。若
$Q_a(t)=\min\{s:d_s\le t\}$ 是有限权重的保留分位数，则

$$
Q_a(\epsilon^2)\le s_a(\epsilon)
\le Q_a(\eta(\epsilon)),\qquad
k_{\rm mm}(\epsilon)\le4Q_a(\eta(\epsilon)).
\tag{46.26}
$$

第一项只描述这一截断复位码族所需的最小保留数，不是对任意编码器的新下界。因为 $\eta(\epsilon)\sim\epsilon^2$，相比分别保留每个长度或只用二阶矩球，这个分位数直接使用实际有限荷权重及其尾部。

还可给一个无需排序的上界。权重（46.2）是窗口内 $\operatorname{Bin}(n-1,1/2)$ 的平均。对 $M_*>1$，置

$$
t_\epsilon=
\sqrt{\frac{M_*-1}{2}
\log\frac2{\eta(\epsilon)}}.
\tag{46.27}
$$

二项变量的 Hoeffding 界说明：区间
$[(N-1)/2-t_\epsilon,(M_*-1)/2+t_\epsilon]$ 外的总权重至多 $\eta(\epsilon)$。$n=1$ 的退化变量恒零，也满足这个保留条件。因此

$$
k_{\rm mm}(\epsilon)\le
4\min\left\{M_*,\,
\left\lfloor\frac{W-1}{2}+2t_\epsilon\right\rfloor+1\right\}.
\tag{46.28}
$$

$M_*=1$ 时直接取上界四。由于 $M_*\le2N$ 且 $\eta(\epsilon)\ge\epsilon^2/2$，这给统一的
$O(\min\{M_*,W+\sqrt{N\log(2/\epsilon)}\})$ 上界；（46.21）的实际分位数证书可以更小。

作为一个无需数值近似的校准，$N=2,W=1$ 时 $M_*=2$、$a=(1/2,1/2)$，探针最优值为 $2(1-\epsilon)$。由（46.22）及精确八维上界，得到
$k_{\rm mm}(\epsilon)=8$ 对全部 $0\le\epsilon<1/8$ 成立。这个区间结论来自两个实际容量界相合；一般权重下（46.22）可以存在间隙，仍不能宣称确定了全部误差下的最优压缩。

本节没有把 Haar 平均误差等同于全相位最坏误差。下界对前者有效，上界装置达到后者；探针族的最优性、截断复位码的准确误差与全部 CPTP 编解码的最优容量是三个不同陈述。

## 追加锚（本行以下为增补区）

## 47. 二步回归刚性与正交交替环境的六终端容量

固定已知非退化来源

$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,\qquad
ab\ne0,\qquad |a|^2+|b|^2=1.
\tag{47.1}
$$

接收器独立纯启动，全部持久系统计入 $K$，活动记忆和参考不可访问，每轮使用同一个全域 CPTP 通道，全部规定终端精确恢复完整参考—活动记忆—档案联合态。

本节只研究同一 Stinespring 等距 $V$ 在实际前缀上输出确定纯环境 $A,B,A,B,\ldots$ 的合同，其中 $A\perp B$。同一环境射线上的全局相位可以统一选择；不预设任何接收器基、不固定第25节九行坐标。

以下两个结论分开：
1. 如果第二轮第二来源列的接收方向回到初态，则任意维数下都有三比二容量下界，并由既有构造达到。
2. 只有在 $D=\dim K\le7$ 且已服务前五个终端时，才证明这种回归被强制；不将它推广到全部 $D$。

### 47.1 一般前三轮资料

设初始接收向量为单位 $k$。定义

$$
\begin{aligned}
V(k0)&=pA,&V(k1)&=qA,\\
V(p0)&=uB,&V(p1)&=vB,&V(q0)&=wB.
\end{aligned}
\tag{47.2}
$$

其中 $p,q$ 正交归一，$u,v,w$ 正交归一，但 $w$ 暂不等于 $k$。第二轮两列为

$$
\Psi_2^0=a m_0u+b m_1v,\qquad
\Psi_2^1=m_0w.
\tag{47.3}
$$

置

$$
c=\sqrt{|a|^4+|b|^2},\qquad
z=\frac{a^2u+bv}{c},\qquad
H=\operatorname{span}\{z,w\},\qquad
G=\operatorname{span}\{u,w\},\qquad
L=H+G=\operatorname{span}\{u,v,w\}.
\tag{47.4}
$$

则 $H,G$ 二维、$H\cap G=\mathbb Cw$。第三轮的实际纯环境给

$$
V(z0)=sA,\qquad V(u1)=rA,\qquad
V(w0)=tA,\qquad V(w1)=jA.
\tag{47.5}
$$

四个输入正交，故 $s,r,t,j$ 正交归一。记

$$
S=\operatorname{span}\{s,t\},\qquad
R=\operatorname{span}\{r,j\},\qquad
L_3=S\oplus R.
\tag{47.6}
$$

第三轮两列及第四轮所需系数空间为

$$
\begin{aligned}
\Psi_3^0&=c m_0s+ab m_1r,&
\Psi_3^1&=a m_0t+b m_1j,\\
H_3&=\operatorname{span}\{cs+br,\ a^2t+bj\},&
G_3&=S.
\end{aligned}
\tag{47.7}
$$

$H_3$ 到 $S,R$ 的两个投影均为同构，因此 $H_3\cap S=H_3\cap R=0$。

固定等距的跨位正交给 $p\perp R$、$q\perp S$。第三轮与第二轮的环境不同，还给 $p\perp H+G=L$，因为 $p$ 同时正交于 $z,u,w$。

对截至第五轮的实际输入，按环境及输入位定义累计接收方向空间

$$
\begin{aligned}
H_A^0&=\operatorname{span}(k,H),&
G_A^0&=\operatorname{span}(k,G),\\
H_B&=\operatorname{span}(p,q,H_3),&
G_B&=\operatorname{span}(p,S),\\
H_A&=H_A^0+H_4,&G_A&=G_A^0+G_4.
\end{aligned}
\tag{47.8}
$$

这里 $H_4,G_4$ 是第四轮两列的零、一位接收系数空间。两个环境正交给

$$
H_A\perp H_B,\qquad G_A\perp G_B.
\tag{47.9}
$$

令 $U_\eta,W_\eta$ 分别为固定 $V$ 在 $H_\eta0,G_\eta1$ 上去掉共同环境后的接收像；则

$$
U_\eta\perp W_\eta,\qquad
\dim U_\eta=\dim H_\eta,\qquad
\dim W_\eta=\dim G_\eta.
\tag{47.10}
$$

特别地每个环境有 $\dim H_\eta+\dim G_\eta\le D$。只看前一、三轮还有

$$
\dim\operatorname{span}(p,q,L_3)=\dim H_A^0+\dim G_A^0.
\tag{47.11}
$$

第四轮的零位像为

$$
U_B=G+G_4.
\tag{47.12}
$$

这是因为 $H_B=\operatorname{span}(p,q,H_3)$，其前三类零位像分别张成 $G$ 和 $G_4$。第四轮实际零系数空间 $H_4$ 的另一投影满到 $V_1S$；具体地，第三轮的两个一位系数为非零倍数的 $s,t$，所以投影满秩没有额外假设。

### 47.2 七维以下的前五轮强制二步回归

**定理 47.1（七维以下的二步回归刚性）。** 若 $D\le7$ 且上述正交交替环境合同服务前五个终端，则 $k\parallel w$。

证明：第25节定理25.2已经排除同一确定正交交替环境合同下的 $D\le6$，所以只需处理 $D=7$。分 $k$ 相对 $H,G$ 的位置。

#### 47.2.1 情形甲：$k\notin H$ 且 $k\notin G$

此时 $\dim H_A^0=\dim G_A^0=3$。初始环境 $A$ 的接收像维数为六，所以 $p,q$ 在 $K/L_3$ 中线性独立。于是

$$
\dim H_B=4,\qquad \dim G_B=3.
\tag{47.13}
$$

$H_A\perp H_B$ 及 $H_A\supset H_A^0$ 强制 $H_A=H_A^0$，维数三。环境 $B$ 的两类像饱和七维：

$$
K=U_B\oplus W_B,\qquad \dim U_B=4,\quad\dim W_B=3.
\tag{47.14}
$$

第五轮一位输入使 $G_A\supset G+G_4=U_B$。又 $G_A\perp G_B$，故

$$
G_A=U_B=G_B^\perp,\qquad \dim G_A=4.
\tag{47.15}
$$

环境 $A$ 的零位像为

$$
U_A=\operatorname{span}(p,S)=G_B.
\tag{47.16}
$$

所以 $W_A=G_A$。固定 $V_1$ 在 $G_A$ 上去掉环境 $A$ 后，给 $G_A$ 到自身的酉 $T$。有

$$
Tk=q,\qquad T(G)=R.
\tag{47.17}
$$

$k,w$ 是 $G_A$ 中两个线性独立向量。因 $H_3\subset H_B=(H_A^0)^\perp$，且 $s,t\in S\subset G_B\perp G_A$，对 $cs+br,a^2t+bj$ 分别取与 $k,w$ 的内积，得到

$$
R\perp\operatorname{span}\{k,w\}.
\tag{47.18}
$$

两边余维恰好给

$$
R=G_A\cap\operatorname{span}\{k,w\}^\perp.
\tag{47.19}
$$

但 $q=Tk\in G_A$，且 $q\in H_B$，所以 $q\perp k,w$，即 $q\in R=T(G)$。$T$ 单射于是强制 $k\in G$，矛盾。

#### 47.2.2 情形乙：$k\in G\setminus H$

此时 $\dim H_A^0=3,\dim G_A^0=2$，且 $q\in R$。环境 $A$ 的初始像维数五，所以 $p\notin L_3$。由于 $H_3\cap R=0$，

$$
\dim H_B=4,\qquad \dim G_B=3.
\tag{47.20}
$$

与情形甲相同的饱和论证给

$$
H_A=H_A^0=L,\quad H_B=L^\perp,\quad
G_A=U_B=G_B^\perp,\quad W_B=G_B,\quad W_A=G_A.
\tag{47.21}
$$

特别地 $v\in W_B=G_B$。$H_3\perp v$，其中 $r,j\in R\subset G_A\perp v$，所以 $s,t\perp v$。因 $S$ 二维、$G_B$ 三维，

$$
S=G_B\cap v^\perp.
\tag{47.22}
$$

而 $p\in G_B$ 且 $p\perp L$，所以 $p\perp v$，从而 $p\in S\subset L_3$，与 $p\notin L_3$ 矛盾。

#### 47.2.3 情形丙：$k\in H\setminus G$

这时 $H_A^0=H$、$G_A^0=L$，且 $p\in S$。初始环境 $A$ 像维数五，所以 $q\notin L_3$。由于 $H_3\cap S=0$，

$$
\dim H_B=4,\qquad G_B=S,\qquad\dim G_B=2.
\tag{47.23}
$$

于是 $\dim U_B=4,\dim W_B=2$，且 $v\in W_B$，从而 $U_B\perp v$。利用 $U_B=G+G_4$，

$$
G_A=L+G_4=U_B\oplus\mathbb Cv,\qquad \dim G_A=5.
\tag{47.24}
$$

环境 $A$ 的接收像维数不超过七，而 $H_A\supset H$ 二维，所以

$$
H_A=H.
\tag{47.25}
$$

因此第四轮零系数空间 $H_4\subset H\subset L\subset G_A$。

另一方面，在相应环境 $B$ 的输入域上记 $\widehat V_i x=(I_K\otimes\langle B|)V(xi)$。第四轮两个零系数明确为

$$
\begin{aligned}
X_4^0&=a^2\widehat V_0(cs+br)+bc\widehat V_1s,\\
X_4^1&=a\widehat V_0(a^2t+bj)+ab\widehat V_1t.
\end{aligned}
\tag{47.26}
$$

左侧均在 $H_4\subset G_A$，右侧第一项均在 $G_4\subset U_B\subset G_A$。分别相减并用 $bc,ab\ne0$，得到 $\widehat V_1s,\widehat V_1t\in G_A$，即 $W_B=\widehat V_1S\subset G_A$。这要求正交和 $U_B\oplus W_B$ 的六维空间包含在五维 $G_A$ 中，矛盾。

#### 47.2.4 唯一余下位置

只能 $k\in H\cap G=\mathbb Cw$。两者单位，所以 $k\parallel w$。证明完毕。

本证明只在 $D=7$ 的维数饱和处排除三类自由度。不能将这一步结论推广到 $D\ge8$。

### 47.3 二步回归足以推出全表正交，无需固定九行坐标

现在允许任意维数 $D$，另假设 $k\parallel w$。写 $w=\zeta k$、$|\zeta|=1$，在 Stinespring 输出环境上施加固定相位酉 $A\mapsto A$、$B\mapsto\overline\zeta B$。第二轮三个接收向量整体乘 $\overline\zeta$，于是新 $w=k$；后续按同一个等距重新定义 $z,s,r,t,j$。这不改变来源 $a,b$ 或物理 CPTP 通道，也没有增加依赖轮次的操作。固定 $V$ 立即给 $t=p,j=q$。于是第三轮四个接收输出 $p,q,s,r$ 正交归一。

置

$$
d=\sqrt{c^2+|b|^2},\qquad f=\frac{cs+br}{d}.
\tag{47.27}
$$

$f$ 单位且正交于 $p,q$，而 $s\perp p$。第四轮的新实际输入是 $f0,s1$，它们与旧的同环境 $B$ 输入 $p0,p1,q0$ 正交；与环境 $A$ 的旧输入正交则由实际新环境为 $B$ 和固定等距性强制。故可记

$$
V(f0)=gB,\qquad V(s1)=hB,
\tag{47.28}
$$

其中 $u,v,w,g,h$ 正交归一。这里没有规定 $g,h$ 必须正交于全部其余接收向量。

前四轮九行的接收方向仍满足

$$
\begin{aligned}
D_A&=\operatorname{span}\{w,z,u\}
\subseteq\operatorname{span}\{u,v,w,g,h\}=O_B,\\
D_B&=\operatorname{span}\{p,q,f,s\}
\subseteq\operatorname{span}\{p,q,s,r\}=O_A.
\end{aligned}
\tag{47.29}
$$

这些包含只用 $z\in\operatorname{span}\{u,v\}$、$df=cs+br$，没有使用第25节构造的特殊坐标。

第五轮的两条新输入为

$$
x0,\quad g1,\qquad
x=\frac{a^2dg+cbh}{\sqrt{|a|^4d^2+|b|^2c^2}}.
\tag{47.30}
$$

由于 $g,h\perp u,v,w$，它们正交于所有旧的同环境 $A$ 输入；与旧环境 $B$ 输入的正交则由环境正交及固定等距性强制。因此全部十一行完整输入在 $K\otimes\mathbb C^2$ 中正交归一，完整输出在 $K\otimes E$ 中正交归一；没有要求不同环境的接收向量在 $K$ 内相互正交。

此后完全采用第43节的交叉包含归纳：上一轮新增输出正交旧同环境像，下一轮同环境旧输入又包含在这些旧像里，所以新输入正交同环境旧输入；异环境正交由 $A\perp B$ 和固定 $V$ 强制。两条新输入均在上一轮输出空间中，故交叉包含继续保持。

所以各轮第一列写为

$$
\Psi_n^0=A_nm_0P_n+B_nm_1Q_n
\tag{47.31}
$$

时，零位输入族 $w,p,q,Z_3,\ldots,Z_N$ 与一位输入族 $w,p,P_2,\ldots,P_{N-1}$ 各自正交归一。两族彼此之间不要求正交。

### 47.4 二步回归合同的精确容量

**定理 47.2（二步回归合同的精确容量）。** 对任意 $N\ge5$，在纯正交交替环境及二步回归 $k\parallel w$ 的合同下，最小接收维数恰为

$$
\boxed{d_N^{\mathrm{return},AB}(a,b)
=\left\lceil\frac{3N}{2}\right\rceil-1.}
\tag{47.32}
$$

不需要固定第25节的九行向量坐标。

证明：第47.3节已得到第43节 Gram 缺陷证明所需的全部正交族。为明确对应，令 $\alpha_n=|A_n|^2$，则

$$
\alpha_1=1,\qquad
\alpha_n=1-|b|^2\alpha_{n-1}
=\frac{1-(-|b|^2)^n}{1+|b|^2}.
\tag{47.33}
$$

取 $n=2,\ldots,N-1$ 的两个正交族 $(P_n)$、$(Z_{n+1})$，令 $M$ 为其交叠矩阵，$\|M\|\le1$。同环境跨位正交使其按奇偶排序的对角块为 $\operatorname{diag}(r_n)$，其中

$$
r_n=\frac{aA_n}{A_{n+1}},\qquad
|r_n|^2=|a|^2\frac{\alpha_n}{\alpha_{n+1}}
\begin{cases}
<|a|^2,&n\text{ 偶},\\
>|a|^2,&n\text{ 奇}.
\end{cases}
\tag{47.34}
$$

所以第43节的块收缩论证给

$$
\operatorname{rank}(I-MM^*)\ge
\left\lfloor\frac{N-1}{2}\right\rfloor.
\tag{47.35}
$$

两个族联合张成的维数至少为 $N-2$ 加这个缺秩；共同正交的 $w,p$ 再给两维，于是

$$
D\ge N+\left\lfloor\frac{N-1}{2}\right\rfloor
=\left\lceil\frac{3N}{2}\right\rceil-1.
\tag{47.36}
$$

第25节的五终端七维构造和第41节的 $N\ge6$ 构造都满足二步回归与正交交替环境，因此达到。证明完毕。

### 47.5 一般正交交替环境的六终端精确值

**推论 47.3（一般正交交替环境的六终端精确容量）。** 不固定任何早期向量坐标，仅要求纯正交交替环境时，六终端最小接收维数恰为八。

证明：第39节给八维达到。若存在七维以下实现，其前五轮由第47.2节强制二步回归。第47.4节在 $N=6$ 给

$$
D\ge\left\lceil9\right\rceil-1=8,
\tag{47.37}
$$

矛盾。因此该环境合同的六终端精确值为八。

一般固定 CPTP 六终端容量仍只有 $7\le d_{\mathrm{CPTP},6}(a,b)\le8$；七维候选若存在，必须离开纯正交交替环境合同。对七终端九维的正交交替环境候选，第47.2节的低维回归刚性不适用，但第47.4节表明它必须满足 $k\not\parallel w$。这是必要自由度，尚未给出九维构造或排除定理。


## 追加锚（本行以下为增补区）

## 48. 一般低秩轨道的有限判据与多周期同步障碍

第45节证明：任意 $d$ 维 CPTP 通道的纯态轨道，只要时刻 $0,\ldots,2d-1$ 全纯，就永久保持纯态。该阈值对每个 $d\ge2$ 都锐。本节说明，把“纯”直接替换成“秩不超过 $r$”，不能得到适用于全部 CPTP 通道和全部 $r$ 的多项式维数阈值。即使初态纯、通道仅作经典测量与制备，互不相交的周期组件在同一时刻分支，也能把首次越过秩界的时刻推到超多项式尺度。

这个反例只处理低秩轨道判据。它没有实现本卷给定非退化来源的完整参考—活动记忆—档案恢复合同，不反驳一般精确接收容量的线性下界猜想。

### 48.1 待检验的统一低秩延拓命题

对通道 $\Phi:\mathcal L(\mathbb C^d)\to\mathcal L(\mathbb C^d)$ 和初态 $\sigma_0$，记 $\sigma_t=\Phi^t(\sigma_0)$。所考察的是如下统一命题：存在仅依赖 $d,r$ 的阈值 $L(d,r)$，使

$$
\operatorname{rank}\sigma_t\le r\quad(0\le t\le L(d,r))
\quad\Longrightarrow\quad
\operatorname{rank}\sigma_t\le r\quad(t\ge0).
\tag{48.1}
$$

**定理48.1（一般低秩延拓没有统一多项式阈值）。** 不存在固定常数 $C_0,C>0$，使对全部 $d$、$1\le r<d$ 及全部 $d$ 维 CPTP 通道，检查时刻 $0,\ldots,\lfloor C_0d^C\rfloor$ 的秩界就足以推出（48.1）的全时域结论。该否定在只允许纯初态时仍成立。因此一般情形不存在统一的 $O(dr)$、$O(d^2)$，或任何固定次数的 $d,r$ 多项式阈值。

最后一项使用 $r<d$：任意固定的 $d,r$ 多项式都被某个 $C_0d^C$ 控制。本定理不否定任一固定 $d,r$ 下存在更大的有限阈值，也不否定附加结构所允许的较短阈值。

### 48.2 具有单、双节点周期类的经典通道

取整数 $k\ge2$ 和两两互素的整数周期 $p_1,\ldots,p_k\ge2$。在通道的 Hilbert 空间中取正交基，由一个根向量 $o$ 及以下 $k$ 个互不相交的组件组成：组件 $i$ 有单节点

$$
x_{i,0},\ldots,x_{i,p_i-2}
$$

和双节点 $y_{i,0},y_{i,1}$。因此总维数为

$$
d=1+\sum_{i=1}^k(p_i+1).
\tag{48.2}
$$

组件 $i$ 的周期类 $0,\ldots,p_i-2$ 各有一个节点，周期类 $p_i-1$ 有两个节点。转移规则为：根以概率 $1/k$ 进入每个组件的类零；单节点沿类次序确定前进；进入最后的双节点类时等概率分支；两个末节点随后都确定回到类零。

将这些转移明确写成 Kraus 算子：

$$
\begin{aligned}
R_i&=\frac1{\sqrt k}|x_{i,0}\rangle\langle o|,
&&1\le i\le k,\\
T_{i,j}&=|x_{i,j+1}\rangle\langle x_{i,j}|,
&&0\le j\le p_i-3,\\
B_{i,\alpha}&=\frac1{\sqrt2}|y_{i,\alpha}\rangle
  \langle x_{i,p_i-2}|,
&&\alpha\in\{0,1\},\\
C_{i,\alpha}&=|x_{i,0}\rangle\langle y_{i,\alpha}|,
&&\alpha\in\{0,1\}.
\end{aligned}
\tag{48.3}
$$

当 $p_i=2$ 时，$T_{i,j}$ 的指标集合为空；分支与合并仍按同一公式定义。令 $\Phi$ 为对（48.3）全部 Kraus 项求和的映射。每个输入节点的出边概率之和为一，具体有

$$
\begin{aligned}
\sum_iR_i^*R_i&=|o\rangle\langle o|,\\
\sum_jT_{i,j}^*T_{i,j}
+\sum_{\alpha}B_{i,\alpha}^*B_{i,\alpha}
+\sum_{\alpha}C_{i,\alpha}^*C_{i,\alpha}
&=\sum_{j=0}^{p_i-2}|x_{i,j}\rangle\langle x_{i,j}|
+\sum_{\alpha=0}^1|y_{i,\alpha}\rangle\langle y_{i,\alpha}|.
\end{aligned}
\tag{48.4}
$$

所以全部 Kraus 平方和为 $I$，$\Phi$ 是同一个全域 CPTP 通道。它在所列基上先测量、再依照转移概率制备，后续论证只涉及对角态。其新环境可以携带被丢弃的经典信息；这里没有施加第45节的纯轨道或其他接收恢复条件。

### 48.3 精确轨道及首次越界时刻

从纯态 $\sigma_0=|o\rangle\langle o|$ 启动。在组件 $i$ 内定义类态

$$
\omega_{i,j}=
\begin{cases}
|x_{i,j}\rangle\langle x_{i,j}|,&0\le j\le p_i-2,\\[2pt]
\dfrac12\bigl(|y_{i,0}\rangle\langle y_{i,0}|
+|y_{i,1}\rangle\langle y_{i,1}|\bigr),&j=p_i-1.
\end{cases}
\tag{48.5}
$$

由转移规则，每个类态确定变成下一个类态，类号模 $p_i$ 计算。根一步后的每个组件质量为 $1/k$，以后不再改变。因此，对所有整数 $t\ge1$，

$$
\sigma_t=\frac1k\sum_{i=1}^k
\omega_{i,(t-1)\bmod p_i}.
\tag{48.6}
$$

不同组件正交，而且每个非零对角权重均严格为正。一个组件通常贡献秩一，恰在 $(t-1)\bmod p_i=p_i-1$，即 $p_i\mid t$ 时贡献秩二。故

$$
\boxed{\operatorname{rank}\sigma_t
=k+\#\{i:p_i\mid t\}\qquad(t\ge1).}
\tag{48.7}
$$

置

$$
r=2k-1,\qquad P=\prod_{i=1}^kp_i.
\tag{48.8}
$$

有 $1\le r<d$。两两互素使 $P$ 为所有周期的最小公倍数，因而第一次同时满足全部整除条件的正时刻正是 $P$。结合根初态秩一，得到

$$
\operatorname{rank}\sigma_t\le r\quad(0\le t<P),
\qquad
\operatorname{rank}\sigma_P=2k=r+1.
\tag{48.9}
$$

在 $t=P+1$ 时，所有组件又回到单节点类零，所以秩降回 $k$。一般非保单位通道的秩无需单调；这里的首次越界来自多个周期同时处于双节点类，而非单个支撑持续扩张。

例如取 $k=2$、$p_1=3$、$p_2=5$，则 $d=11$、$r=3$，且

$$
\operatorname{rank}\sigma_t
=2+\mathbf1_{3\mid t}+\mathbf1_{5\mid t}\quad(t\ge1).
\tag{48.10}
$$

时刻 $0,\ldots,14$ 的秩全部不超过三，时刻十五首次达到四；时刻十六又降到二。

### 48.4 只用 Bertrand 定理的超多项式估计

令 $p_i$ 为第 $i$ 个素数。由 Bertrand 定理相邻素数满足 $p_{i+1}<2p_i$，配合 $p_1=2$，有 $p_i\le2^i$。另一方面，第 $i$ 个素数满足 $p_i\ge i+1$。因此

$$
d_k=1+k+\sum_{i=1}^kp_i
\le2^{k+1}+k-1\le2^{k+2},
\qquad
P_k=\prod_{i=1}^kp_i\ge(k+1)!.
\tag{48.11}
$$

对任意固定实数 $C>0$，

$$
\frac{P_k}{d_k^C}
\ge\frac{(k+1)!}{2^{C(k+2)}}\longrightarrow\infty.
\tag{48.12}
$$

右侧相邻项之比为 $(k+2)/2^C$，故该发散不需要素数定理。给定任意固定 $C_0,C>0$，取足够大的 $k$，便有 $P_k>C_0d_k^C$。相应通道在全部被要求检查的时刻仍满足秩界，却在时刻 $P_k$ 越界，证明定理48.1。

### 48.5 反对称检测给出的通用有限上界

没有统一多项式阈值，不等于没有有限判据。以下上界与定理48.1相容：其指数依赖允许的秩。

**定理48.2（一般低秩轨道的有限延拓上界）。** 对任意 $d$ 维 CPTP 通道、任意初态及 $1\le r<d$，若

$$
\operatorname{rank}\sigma_n\le r
\qquad(0\le n\le d^{r+1}-1),
\tag{48.13}
$$

则全部以后时刻也满足该秩界。

证明。置 $\ell=r+1\le d$，在 $\widetilde H=(\mathbb C^d)^{\otimes\ell}$ 上取反对称投影 $P_{\mathrm{alt}}$。对半正定态 $\sigma$，按其谱分解直接计算可得

$$
\operatorname{Tr}(P_{\mathrm{alt}}\sigma^{\otimes\ell})
=\sum_{1\le i_1<\cdots<i_\ell\le d}
\lambda_{i_1}(\sigma)\cdots\lambda_{i_\ell}(\sigma).
\tag{48.14}
$$

各特征值非负，所以该式为零当且仅当 $\operatorname{rank}\sigma\le r$。又因 $P_{\mathrm{alt}}$ 是正交投影、$\sigma^{\otimes\ell}$ 半正定，迹为零当且仅当后者的支撑包含于 $\ker P_{\mathrm{alt}}$。

令 $\widetilde\Phi=\Phi^{\otimes\ell}$，则 $\sigma_n^{\otimes\ell}=\widetilde\Phi^n(\sigma_0^{\otimes\ell})$。记 $\mathcal A$ 为其有限张量 Kraus 表，定义

$$
S_n=\operatorname{supp}(\sigma_n^{\otimes\ell}),\qquad
W_n=\sum_{j=0}^nS_j.
\tag{48.15}
$$

正项之和的支撑为各正项支撑之和，因此

$$
S_{n+1}=\sum_{A\in\mathcal A}AS_n,
\qquad
W_{n+1}=W_0+\sum_{A\in\mathcal A}AW_n.
\tag{48.16}
$$

特别地，若 $W_{n+1}=W_n$，则每个 $A$ 都保持 $W_n$，所以之后的全部支撑均留在 $W_n$。

置 $\widetilde d=d^\ell$。由（48.13）—（48.14），$W_0,\ldots,W_{\widetilde d-1}$ 全部包含于 $\ker P_{\mathrm{alt}}$。由于 $\ell\le d$，反对称子空间非零，故这个核是真子空间，维数至多 $\widetilde d-1$。另一方面，$W_0$ 至少一维。如果这 $\widetilde d-1$ 次相邻包含全部严格，则 $W_{\widetilde d-1}$ 至少 $\widetilde d$ 维，矛盾。因此某次相邻包含相等，此后的支撑永久留在同一个 $\ker P_{\mathrm{alt}}$ 内。再用（48.14），得到所有未来时刻的秩界。证明完毕。

这个上界只用于区分“没有统一多项式界”与“没有有限界”。它未声称最优；特别在 $r=1$ 时，第45节已将这里的平方级界 $d^2-1$ 收紧到逐维精确的线性阈值 $2d-1$。

### 48.6 对接收容量研究的含义与边界

该构造由多个封闭的周期组件组成，且根是暂态；它没有不可约性或本原性。低秩轨道的读数可以只记录有多少周期组件当前分支，不能据此控制这些组件何时同时分支。因此，第45节的纯轨道线性延拓不能仅靠把秩一换成一般秩界，就升级为适用于全部 CPTP 的多项式有限检验。

这里的长周期存于混合态的不同周期分量；秩是状态的数学属性，不是一份单次测量可精确读出的钟值。不同时间的密度矩阵也不自动成为可完美区分的时间标签。例如 $\sigma_1$ 与 $\sigma_{1+p_1}$ 在第一个组件都对 $x_{1,0}$ 赋予权重 $1/k$，支撑相交，所以不能被单次测量完美区分。因此不能把长同步周期当作免费外部控制器来驱动接收门；它在这里提供的是低秩判据本身的反例。

在本卷的实际接收问题中，第23节的可逆编码结构给出同一终端上档案支撑、接收等距与附加态之间的联合关系。把这组关系只投影成 $4r_n\le D$ 或实际联合态的秩上界，会丢失它们来自同一个来源递推和同一个固定接收通道的约束。本节的经典轨道没有提供这一组来源与恢复对应，故不能据（48.9）构造精确接收器，也不能据此否定一般接收容量的线性增长。

后续要取得容量下界，必须保留足以排除这种任意周期附加动力学的共同来源与恢复结构，或利用该结构推出新的支撑、交叠或相容性约束。仅延长对单条轨道低秩性的观察，在一般通道类中无法完成这一步。

## 追加锚（本行以下为增补区）

## 49. 固定 Bell 边缘态与小维数接收器的准确误差

第46节把伯努利相干窗口化为端点与相位钟的张量积，并给出有限探针证书。本节使用 Bell 初始输入留下的固定边缘态，改进接收维数小于四时的必要界，再构造达到该界的装置。所得最优性分别针对维数一、二、四；维数三及一般较大维数不由这些结论插值得到。

沿用（46.2）的严格正权重 $a=(a_0,\ldots,a_{M_*-1})$，记 $v_\ell=\sqrt{a_\ell}$，$E=I\otimes J$，$A=R\otimes M$。档案换坐标后的来源输出仍为

$$
\rho_{RI}\otimes|\Phi_\theta\rangle\langle\Phi_\theta|_{MJ}
\otimes|\psi^a_\theta\rangle\langle\psi^a_\theta|_C.
\tag{49.1}
$$

初始 $RI$ 取 Bell 态时，$AE$ 是四维最大纠缠纯态，$A$ 的边缘态对全部相位恒为 $I_A/4$。编码只作用于档案 $EC$，所以编码后 $AK$ 的边缘态也恒为 $I_A/4$。

本节记接收维数至多为 $D$ 时，最优全相位、全初态、完整参考半迹误差为 $e_{\rm mm}(D)$；只要求初始 Bell 输入并取相位 Haar 平均的最优误差为 $e_{\rm av,Bell}(D)$。二者分别对所有共同 CPTP 编解码取下确界，且

$$
e_{\rm av,Bell}(D)\le e_{\rm mm}(D).
\tag{49.2}
$$

### 49.1 固定最大混合边缘态的谱上界

**引理49.1。** 若密度矩阵 $\omega_{AK}$ 满足 $\dim A=r$、$\dim K=D$ 及 $\operatorname{Tr}_K\omega=I_A/r$，则

$$
\boxed{\omega_{AK}\preceq\min\{1,D/r\}\,I_{AK}.}
\tag{49.3}
$$

证明。取任一正特征值 $\lambda$ 及相应单位特征向量 $|\chi\rangle$。由
$\lambda|\chi\rangle\langle\chi|\preceq\omega$，偏迹得
$\lambda\chi_A\preceq I_A/r$。令 $Q$ 是 $\chi_A$ 的支撑投影；Schmidt 分解给 $\operatorname{rank}Q\le\min\{r,D\}$。两边乘 $Q$ 后取迹，得

$$
\lambda=\lambda\operatorname{Tr}(Q\chi_A)
\le\frac{\operatorname{rank}Q}{r}
\le\min\{1,D/r\}.
$$

每个特征值都满足此界，证明完毕。

取共同解码器 $\mathcal D$，置 $\tau=\mathcal D(I_K)$，于是 $\tau\succeq0$、$\operatorname{Tr}\tau=D$。由（49.3）及解码正性，Bell 输入的每个恢复态满足

$$
\sigma_\theta\preceq
\min\{1,D/4\}\,I_A\otimes\tau.
\tag{49.4}
$$

对第46节任意概率向量探针 $|\Xi^w_\theta\rangle$，（46.15）的准确平均边缘谱给

$$
\int\langle\Xi^w_\theta|\sigma_\theta|\Xi^w_\theta\rangle\,d\theta
\le\frac D4\min\{1,D/4\}\max_\ell w_\ell.
\tag{49.5}
$$

因此，若 Bell 输入的平均半迹误差不超过 $\epsilon$，则

$$
\left(\sum_\ell\sqrt{a_\ell w_\ell}\right)^2-\epsilon
\le\frac D4\min\{1,D/4\}\max_\ell w_\ell.
\tag{49.6}
$$

继续使用（46.17）的有限优化，并把端点定义为

$$
\mathfrak L_a(0)=\left(\sum_\ell\sqrt{a_\ell}\right)^2,
\qquad \mathfrak L_a(1)=0.
\tag{49.7}
$$

对全部探针优化（49.6）得到

$$
\boxed{\mathfrak L_a(\epsilon)
\le\frac D4\min\{1,D/4\}.}
\tag{49.8}
$$

等价地，对 $0\le\epsilon<1$，

$$
\boxed{
\left\lceil4\max\left\{\mathfrak L_a(\epsilon),
\sqrt{\mathfrak L_a(\epsilon)}\right\}\right\rceil
\le k_{\rm av,Bell}(\epsilon)
\le k_{\rm mm}(\epsilon).
}
\tag{49.9}
$$

当 $\mathfrak L_a(\epsilon)<1$ 时，连续下界严格强于第46节的 $4\mathfrak L_a(\epsilon)$；取整后的整数下界不必每次都严格增大。对 $D\ge4$，式（49.8）回到第46节的必要界。

### 49.2 投影概率上界的可达性及其范围

式（49.5）在每个 $1\le D\le4$、每个固定探针 $w$ 下都有一份真正的共同编码达到等号。其构造也适用于一般端点维数 $r$ 和 $D\le r$。

选端点空间 $E$ 的 $D$ 个坐标基向量，记它们的支撑投影为 $P$，并选其中一个单位基向量 $|e_0\rangle$。编码丢弃钟 $C$，把 $PE$ 等距送入 $D$ 维接收器；每个未选端点基向量均复位为 $|e_0\rangle$ 对应的代码态。解码等距嵌回 $PE$，并准备钟基态 $|\ell_*\rangle$，其中 $w_{\ell_*}=\max w$。恢复后的端点通道具有 Kraus 算子

$$
K_0=P,\qquad K_j=|e_0\rangle\langle e_j|\quad(e_j\perp PE),
\qquad \sum_jK_j^*K_j=I_E.
\tag{49.10}
$$

对任一 $r$ 维最大纠缠态 $|\Phi_U\rangle=(I\otimes U)|\Phi_r\rangle$，其端点恢复投影概率是

$$
\sum_j\left|\langle\Phi_U|(I\otimes K_j)|\Phi_U\rangle\right|^2
=\frac1{r^2}\sum_j|\operatorname{Tr}(U^*K_jU)|^2
=\frac{D^2}{r^2}.
\tag{49.11}
$$

这里 $\operatorname{Tr}K_0=D$，其余 Kraus 的迹为零。钟探针的投影概率是 $w_{\ell_*}$，故完整投影概率对每个相位都等于

$$
\frac{D^2}{r^2}\max_\ell w_\ell.
\tag{49.12}
$$

特别地，$r=4$ 时达到（49.5）的上界。编码和解码只用固定坐标与已选 $\ell_*$，完全不依赖实际相位。这个结论只说明投影概率不等式本身准确；一般情形中，某个探针投影差达到下界，并不等于该装置的完整半迹误差达到下界。

### 49.3 由有限探针优化构造最优的钟准备态

下面先给出同时用于三个维数的矩阵构造。函数 $\mathfrak L_a$ 在 $[0,1]$ 上连续并严格递减。连续性来自紧盒上连续目标的最大值；当 $\epsilon<1$ 时最大值为正，且任一最大点都有 $\max_\ell x_\ell=1$。因此对 $0\le\epsilon_1<\epsilon_2<1$，取第二个参数的最大点即得

$$
\mathfrak L_a(\epsilon_1)
\ge\mathfrak L_a(\epsilon_2)+
(\epsilon_2-\epsilon_1)\|x\|^2
\ge\mathfrak L_a(\epsilon_2)+\epsilon_2-\epsilon_1.
\tag{49.13}
$$

与 $\epsilon_2=1$ 的严格比较由 $\mathfrak L_a(\epsilon_1)>0$ 得到。又因所有权重严格正，$\mathfrak L_a(0)\ge1$，且等号恰在 $M_*=1$ 时成立。

**引理49.2（钟准备态）。** 给定 $0<\kappa<\mathfrak L_a(0)$，令 $e\in(0,1)$ 是唯一满足

$$
\mathfrak L_a(e)=\kappa
\tag{49.14}
$$

的数。存在一个可由（46.18）有限求出的概率向量 $b$，使矩阵

$$
B_\kappa=vv^* -\kappa\operatorname{diag}b
\tag{49.15}
$$

只有一个正特征值，且该特征值恰为 $e$。同时

$$
\sum_\ell\frac{a_\ell}{e+\kappa b_\ell}=1.
\tag{49.16}
$$

证明。取（46.18）的最大点 $x_\ell=\min\{1,c v_\ell\}$，记 $S=v^*x>0$ 及 $H=\{\ell:x_\ell=1\}$。每个坐标都严格正。内部坐标的一阶条件和上端点的一阶条件分别是

$$
S v_\ell=e x_\ell\quad(\ell\notin H),
\qquad S v_\ell\ge e\quad(\ell\in H).
\tag{49.17}
$$

定义

$$
b_\ell=
\begin{cases}
(Sv_\ell-e)/\kappa,&\ell\in H,\\
0,&\ell\notin H.
\end{cases}
\tag{49.18}
$$

式（49.17）给非负性，而且

$$
\kappa=S^2-e\|x\|^2
=\sum_\ell x_\ell(Sv_\ell-e x_\ell)
=\sum_{\ell\in H}(Sv_\ell-e),
\tag{49.19}
$$

所以 $\sum_\ell b_\ell=1$。逐坐标计算得

$$
B_\kappa x=e x,
\qquad (e+\kappa b_\ell)x_\ell=S v_\ell.
\tag{49.20}
$$

秩一正算子减去正算子至多有一个正特征值：在 $v^\perp$ 上二次型非正，故不可能存在二维正谱子空间。由于 $e>0$ 是其特征值，它就是唯一正特征值。将（49.20）除以正分母，乘 $v_\ell$ 后求和并约去 $S$，得到（49.16）。证明完毕。

相位对角酉只共轭 $vv^*$，并保持 $\operatorname{diag}b$ 不变，所以同一特征值结论对全部相位成立。边界情形 $M_*=1$、$\kappa=1$ 另取 $b=(1)$、$e=0$。

### 49.4 维数一、二、四的准确最优误差

置

$$
\kappa_1=\frac1{16},\qquad
\kappa_2=\frac14,\qquad
\kappa_4=1.
\tag{49.21}
$$

对 $D\in\{1,2,4\}$，令 $e_D\in[0,1)$ 为唯一满足

$$
\mathfrak L_a(e_D)=\kappa_D
\tag{49.22}
$$

的解。其中 $e_D=0$ 恰发生在 $D=4$、$M_*=1$；其余情形使用引理49.2取相应的 $b$。

**定理49.3（三个维数的共同最优值）。** 对每个第46节的伯努利相干窗口，

$$
\boxed{
e_{\rm av,Bell}(D)=e_{\rm mm}(D)=e_D,
\qquad D\in\{1,2,4\}.
}
\tag{49.23}
$$

证明分为构造与必要性。

**维数一。** 编码丢弃整个档案，解码准备

$$
\tau_{EC}=\frac{I_E}{r}\otimes\operatorname{diag}b,
\qquad r=4,\quad\kappa=1/r^2.
\tag{49.24}
$$

先看初始 Bell 输入。恢复态是
$I_{AE}/r^2\otimes\operatorname{diag}b$。在目标端点最大纠缠向量张成的一维空间上，目标减恢复的矩阵是

$$
|\psi^a_\theta\rangle\langle\psi^a_\theta|
-\frac1{r^2}\operatorname{diag}b;
\tag{49.25}
$$

端点正交补上的所有块都非正。引理49.2给完整差算子唯一正特征值 $e_1$。完整差算子迹为零，故半迹误差恰为 $e_1$，与相位无关。

还须证明这个实际擦除码对任意来源输入和参考的误差都不超过 $e_1$。可以证明更强的陈述：固定 $\dim E=r$，对任意参考系统 $A$、任意纯态 $|\zeta\rangle_{AE}$，其钟仍为独立的 $|\psi^a_\theta\rangle$ 时，（49.24）的误差不超过最大纠缠输入的误差。

取 Schmidt 概率 $\lambda_1,\ldots,\lambda_r$，缺项补零。目标减恢复为

$$
|\zeta\rangle\langle\zeta|\otimes
|\psi^a_\theta\rangle\langle\psi^a_\theta|
-\zeta_A\otimes\frac{I_E}{r}\otimes\operatorname{diag}b.
\tag{49.26}
$$

这是迹零的秩一正算子减去正算子，且 $r=4$ 时不为零，因而有且只有一个正特征值 $t$；它就是半迹误差。在 Schmidt 基与钟坐标中，正特征值方程由秩一扰动直接给出：若 $u$ 是目标单位向量、$T$ 是被减去的正算子，则正特征向量必须正比于 $(tI+T)^{-1}u$，并满足 $\langle u,(tI+T)^{-1}u\rangle=1$。因此这里有

$$
\sum_{i=1}^r\sum_\ell
\frac{\lambda_i a_\ell}{t+\lambda_i b_\ell/r}=1.
\tag{49.27}
$$

对任意固定 $t>0$、$c\ge0$，函数 $z\mapsto z/(t+cz)$ 在非负半轴上凹。由 $\sum_i\lambda_i=1$，Jensen 不等式给

$$
\sum_{i=1}^r\frac{\lambda_i}{t+\lambda_i b_\ell/r}
\le\frac1{t+b_\ell/r^2}.
\tag{49.28}
$$

把 $t=e_1$ 代入（49.27）的左侧，再用（49.28）与（49.16），所得值不超过一。该左侧随 $t>0$ 严格下降，所以其根不大于 $e_1$。混合态由半迹范数凸性得到同一上界。实际来源（49.1）是上述输入集合的子集，且包含最大纠缠 $AE$ 输入；故该码的完整最坏误差正好为 $e_1$。

**维数二。** 编码完整保留二态寄存器 $I$，丢弃 $J,C$；解码准备
$I_J/2\otimes\operatorname{diag}b$。任意 $\rho_{RI}$ 都原样保留，目标与恢复态分别是

$$
\rho_{RI}\otimes|\Phi_\theta\rangle\langle\Phi_\theta|_{MJ}
\otimes|\psi^a_\theta\rangle\langle\psi^a_\theta|_C,
\qquad
\rho_{RI}\otimes\frac{I_{MJ}}4\otimes\operatorname{diag}b.
\tag{49.29}
$$

张量相同的密度矩阵 $\rho_{RI}$ 不改变半迹距离。在 $MJ$ 的目标 Bell 方向上，差算子为
$|\psi^a_\theta\rangle\langle\psi^a_\theta|-(1/4)\operatorname{diag}b$；其余三个端点方向均给非正块。因此引理49.2给误差恰为 $e_2$，对每个相位、每个来源初态和参考都成立。

**维数四。** 编码完整保留 $I,J$，丢弃 $C$；解码准备 $\operatorname{diag}b$。误差就是钟的半迹距离

$$
\frac12\left\||\psi^a_\theta\rangle\langle\psi^a_\theta|
-\operatorname{diag}b\right\|_1=e_4.
\tag{49.30}
$$

对 $M_*>1$，等号由引理49.2及差算子迹零得到；$M_*=1$ 时钟是已知固定纯态，误差为零。端点和参考均完整保留。

以上三个构造通过 $U_{\rm ar}$ 返回原档案，并在共同支撑外任意完成为全域 CPTP 编码；它们均与实际相位无关。因此 $e_{\rm mm}(D)\le e_D$。反向，对任意维数至多为 $D$ 的装置，（49.8）给
$\mathfrak L_a(\epsilon)\le\kappa_D$；严格单调性迫使 $\epsilon\ge e_D$。这一必要界已经适用于较弱的 Bell 平均合同，故与（49.2）合并得到（49.23）。证明完毕。

维数三只得到

$$
\underline e_3\le e_{\rm av,Bell}(3)
\le e_{\rm mm}(3)\le e_2,
\qquad \mathfrak L_a(\underline e_3)=\frac9{16}.
\tag{49.31}
$$

下界来自（49.8），上界由把维数二的代码嵌入三维空间得到。第49.2节虽然在 $D=3$ 也使投影概率上界达到等号，但没有证明该码的半迹误差达到 $\underline e_3$；本节不把两种可达性混同。

### 49.5 平坦相位钟的准确校准

若权重平坦，即 $a_\ell=1/M_*$，Cauchy–Schwarz 不等式给

$$
\frac1{M_*}\left(\sum_\ell x_\ell\right)^2
-\epsilon\sum_\ell x_\ell^2
\le(1-\epsilon)\sum_\ell x_\ell^2
\le M_*(1-\epsilon),
$$

而 $x_\ell=1$ 达到等号。因此

$$
\mathfrak L_a(\epsilon)=M_*(1-\epsilon),
\qquad
\boxed{
e_1=1-\frac1{16M_*},\quad
 e_2=1-\frac1{4M_*},\quad
 e_4=1-\frac1{M_*}.
}
\tag{49.32}
$$

对应准备态可以统一取 $b_\ell=1/M_*$。伯努利窗口中，$N=W=1$ 给 $M_*=1$，三个准确误差依次为 $15/16,3/4,0$；$N=2,W=1$ 给 $a=(1/2,1/2)$，三个准确误差依次为 $31/32,7/8,1/2$。一般伯努利窗口的权重不是平坦的，其误差由（49.22）和第46节的有限排序公式计算。

平坦钟还给较大接收维数的准确族。考虑同样端点分解（49.1），但将钟取为任意给定长度 $M_*$ 的平坦相位态；这定义一个辅助来源，不声称每个平坦权重都来自伯努利长度窗口。若 $M_*=st$，按频率 $\ell=j+sk$ 重排钟基，便有与实际相位无关的分解

$$
\frac1{\sqrt{M_*}}\sum_{\ell=0}^{M_*-1}e^{i\ell\theta}|\ell\rangle
\longmapsto
\left(\frac1{\sqrt s}\sum_{j=0}^{s-1}e^{ij\theta}|j\rangle\right)
\otimes
\left(\frac1{\sqrt t}\sum_{k=0}^{t-1}e^{iks\theta}|k\rangle\right).
\tag{49.33}
$$

保留端点 $IJ$ 与第一个钟因子，所需维数 $D=4s$；丢弃第二个因子并在解码时准备 $I_t/t$。纯态与 $I_t/t$ 的差具有特征值 $1-1/t$ 以及 $t-1$ 个 $-1/t$，故对全部来源输入、参考和相位，误差恰为 $1-1/t$。另一方面（49.8）在 $D=4s$ 时给
$M_*(1-\epsilon)\le s$。两边匹配，得到

$$
\boxed{
e_{\rm av,Bell}(4s)=e_{\rm mm}(4s)
=1-\frac{s}{M_*},\qquad s\mid M_*.
}
\tag{49.34}
$$

因此，在固定 Bell 边缘态的这一来源类中，$D\ge4$ 的原探针界已经有实际共同 CPTP 编码达到等号，不能在整个该区间对所有此类来源统一作严格加强。非平坦权重、非整除关系和其他维数仍须使用各自的联合编码条件分析；（49.34）没有给这些情形作最优性结算。

## 追加锚（本行以下为增补区）

## 50. 非正交二周期环境的支撑增长与六终端容量

固定非退化已知来源
$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,
\qquad ab\ne0,\qquad |a|^2+|b|^2=1.
$$
接收器独立纯启动，活动记忆和参考不可访问，每轮使用同一个全域 CPTP 通道，全部持久系统计入 $K$，记 $D=\dim K$。要求前 $N\ge2$ 个终端精确恢复完整参考—活动记忆—原档案联合态。

本节先假设同一固定 Stinespring 表示的实际新环境为输入无关的纯向量 $A,B,A,B,\ldots$，且
$$
0<|\langle A,B\rangle|<1.
$$

**定理50.1（非正交二周期环境的累计支撑下界）。** 对 $N\ge3$，任意这种接收器满足
$$
\boxed{D\ge\left\lceil\frac{3N}{2}\right\rceil.}
\tag{50.1}
$$

证明。对两份来源列写
$$
\Psi_n^i=m_0A_n^i+m_1B_n^i,
$$
并令
$$
P=\operatorname{span}\{A_n^i:1\le n\le N\},\qquad
Q=\operatorname{span}\{B_n^i:1\le n\le N\}.
$$
令 $V_i x=V(x\otimes|i\rangle)$。每个 $A_n^i\otimes\eta_n$ 属于 $V_0K$，每个 $B_m^j\otimes\eta_m$ 属于 $V_1K$。两个全域像正交，而每对实际环境内积非零，因此
$$
P\perp Q.
$$

记单轮子空间
$$
G_n=\operatorname{span}\{A_n^0,A_n^1\},\qquad
H_n=\operatorname{span}\{aA_n^0+B_n^0,aA_n^1+B_n^1\},\qquad
Q_n=\operatorname{span}\{B_n^0,B_n^1\}.
$$
首步 $G_1=\mathbb Cp$、$H_1=\operatorname{span}(p,q)$，其中 $p\in P,q\in Q$ 是正交单位向量；$\dim G_n=\dim H_n=2$ 对 $n\ge2$ 成立。逐步有
$$
V_0H_n=G_{n+1}\otimes\eta_{n+1},\qquad
V_1G_n=Q_{n+1}\otimes\eta_{n+1}.
$$
第一式在 $P$ 上的输入投影满足 $P_PH_n=G_n$，因为 $a\ne0$。这些维数可从 $\dim H_1=2$ 直接归纳：$V_0$ 单射给 $\dim G_{n+1}=\dim H_n$，而 $H_n$ 到 $G_n$ 的投影满秩且两者均由两个向量生成，故 $n\ge2$ 时都恰为二维。进一步，$n\ge3$ 时 $\dim Q_n=2$，所以四个 $A_n^i,B_n^i$ 线性独立；这也与完整参考 Bell 档案的 Schmidt 秩四在纯可逆编码下保持一致。

定义累计奇偶空间
$$
E_m=G_2+G_4+\cdots+G_{2m},\qquad
O_m=G_1+G_3+\cdots+G_{2m-1},
$$
及 $e_m=\dim E_m,o_m=\dim O_m$，只使用指标不超过 $N$ 的项。

同一偶数轮环境给
$$
\dim(H_1+H_3+\cdots+H_{2m-1})=e_m.
$$
该输入空间在 $P$ 上的投影是 $O_m$，且包含非零 $q\in H_1\cap Q$。因此其投影核至少一维，得到
$$
e_m\ge o_m+1.\tag{50.2}
$$
同一奇数轮环境又给
$$
\dim(H_2+H_4+\cdots+H_{2m})
=\dim(G_3+G_5+\cdots+G_{2m+1})\le o_{m+1}.
$$
其 $P$ 投影是 $E_m$，故
$$
o_{m+1}\ge e_m.\tag{50.3}
$$
由 $o_1=1$、$e_1=2$ 归纳可得
$$
e_m\ge m+1,\qquad o_m\ge m.\tag{50.4}
$$

只要累计空间中的最大终端指标不超过 $N-1$，$V_1$ 将 $E_m$ 送入 $Q\otimes A$，将 $O_l$ 送入 $Q\otimes B$。不同环境射线给
$$
E_m\cap O_l=0.\tag{50.5}
$$
同一等距还给
$$
\dim Q\ge\max(e_m,o_l).\tag{50.6}
$$

若 $N=2m+1$，取截至 $N-1$ 的 $E_m,O_m$。式（50.4）—（50.6）给
$$
\dim P\ge2m+1,\qquad \dim Q\ge m+1,
$$
故 $D\ge3m+2=\lceil3N/2\rceil$。

若 $N=2m\ge4$，取截至 $N-1$ 的 $E_{m-1},O_m$。此时 $e_{m-1}\ge m,o_m\ge m$，故
$$
\dim P\ge2m,\qquad \dim Q\ge m,
$$
得到 $D\ge3m=\lceil3N/2\rceil$。证明完毕。

定理50.1在五终端给出 $D\ge8$。对 $N\ge6$，它比第41节正交交替构造的 $\lceil3N/2\rceil-1$ 上界高一维，因此非正交二周期纯环境不能改善该既有构造的容量。下面对二步回归子类给出精确值，并进一步排除六终端的九维等号情形。

记 $V_i x=V(x\otimes|i\rangle)$，初态为 $k$。前两轮资料为
$$
V_0k=pA,\quad V_1k=qA,
\qquad V_0p=uB,\quad V_1p=vB,\quad V_0q=wB.
$$
$p,q$ 正交归一，$u,v,w$ 正交归一。两步回归指 $w\parallel k$。若 $w=\zeta k$，则重选同一环境射线的单位代表 $B'=\zeta B$，并将所有偶数轮对应的接收系数按该坐标选择重标，首个 $w$ 便成为 $k$。这是同一个 $V$ 的坐标变化，不是在非正交环境上实施独立相位的环境酉；物理接收通道保持相同。以下使用这一共同相位约定，写 $w=k$。

**定理50.2（非正交交替环境的回归精确容量）。** 对 $N\ge2$，非正交交替纯环境且两步回归的精确容量为
$$
\boxed{d_N^{\mathrm{return},\mathrm{nonorth}\,AB}=2N+1.}
\tag{50.7}
$$

证明。先证下界。因环境内积非零，$V_0q=kB$ 与 $V_1k=qA$ 的正交给 $k\perp q$。再比较同一个 $V_0$ 在 $k,q$ 上的像，得到 $p\perp k$；比较它在 $k,p$ 上的像得到 $p\perp u$。比较 $V_1$ 在 $k,p$ 上的像得到 $q\perp v$。不同输入位的像还给 $p\perp v$、$q\perp u$。结合两轮内部的正交性，得到
$$
p,q,u,v,k\quad\text{正交归一}.\tag{50.8}
$$
因此前五行输入也正交归一。

对第一来源列，取非零标量 $\lambda_n,\mu_n$ 和正交单位向量 $P_n,Q_n$，使
$$
\Psi_n^0=\lambda_nm_0P_n+\mu_nm_1Q_n\qquad(n\ge2),
$$
初值为 $(\lambda_2,\mu_2,P_2,Q_2)=(a,b,u,v)$。递归令
$$
\lambda_{n+1}=\sqrt{|a\lambda_n|^2+|\mu_n|^2},\qquad
\mu_{n+1}=b\lambda_n,\qquad
Z_{n+1}=\frac{a\lambda_nP_n+\mu_nQ_n}{\lambda_{n+1}}.
$$
每轮第一列的实际纯环境要求
$$
V_0Z_{n+1}=P_{n+1}\eta_{n+1},\qquad
V_1P_n=Q_{n+1}\eta_{n+1}.\tag{50.9}
$$

归纳证明（50.9）每轮添加两个新的正交接收输出。假设截至第 $n\ge2$ 轮，已经得到
$$
p,q,u,v,k,P_3,Q_3,\ldots,P_n,Q_n
$$
两两正交归一。下一轮零位输入 $Z_{n+1}$ 位于最后两个新方向 $P_n,Q_n$ 的张成内，因而正交于全部旧零位输入 $k,p,q,Z_3,\ldots,Z_n$；下一轮一位输入 $P_n$ 正交于全部旧一位输入 $k,p,P_2,\ldots,P_{n-1}$。两类输入位又彼此正交。因此两个新增输入行与全部已列输入行正交归一。固定 $V$ 保持这些内积，且任意两轮环境内积非零，所以新增接收向量 $P_{n+1},Q_{n+1}$ 与全部旧接收输出正交归一。初始的 $n=2$ 用（50.8）成立。于是总共有 $5+2(N-2)=2N+1$ 个正交接收向量。

为达到下界，直接选取上述 $2N+1$ 个正交单位向量，将前五行与（50.9）作为部分作用规定。所列输入正交归一，所列输出接收向量也正交归一，因此无论 $A,B$ 的非零交叠是多少，全部带环境输出仍正交归一。把部分作用补成 $K\otimes\mathbb C^2\to K\otimes\operatorname{span}(A,B)$ 的全域酉。

第一来源列按构造逐步成立。第二来源列满足
$$
\Psi_2^1=m_0k=a\Psi_0^0+b\Psi_0^1,
$$
令 $\mathcal L$ 为一次来源发射接上固定 $V$ 的联合等距。实际前缀满足 $\mathcal L\Psi_{j-1}^i=\Psi_j^i\otimes\eta_j$。若上一步已有 $\Psi_{n-1}^1=a\Psi_{n-3}^0+b\Psi_{n-3}^1$，对其施加同一个 $\mathcal L$，右侧只使用两步前已规定的行表，并且 $\eta_n=\eta_{n-2}$。消去共同环境因子便得到
$$
\Psi_n^1=a\Psi_{n-2}^0+b\Psi_{n-2}^1\qquad(n\ge2).
$$
初值是前述 $n=2$ 等式。
这说明第二列的每一步也落在上述部分作用的已规定域内，不另外增加行。固定单位环境前缀与来源输入解耦，逐终端可附加已知环境前缀并逆序运行 $V^*$，恢复全部原档案且保持参考与活动记忆。全部持久资源恰为 $2N+1$ 维。证明完毕。

**定理50.3（非正交交替环境的六终端强化下界）。** 非正交交替纯环境的六终端接收器必须满足 $D\ge10$。

证明。定理50.1的一般增长下界先给 $D\ge9$。反设 $D=9$。沿用该节的全局正交空间 $P\perp Q$、单轮 $G_n,H_n,Q_n$，以及累计
$$
E=G_2+G_4,\qquad O=G_1+G_3+G_5.
$$
增长下界的等号条件给
$$
\dim P=6,\quad \dim Q=3,\quad
\dim E=\dim O=3,\quad P=E\dotplus O.
\tag{50.10}
$$
固定 $V_1$ 分别将 $E,O$ 送入 $Q\otimes A,Q\otimes B$；维数饱和使
$$
V_1E=Q\otimes A,\qquad V_1O=Q\otimes B.
\tag{50.11}
$$
由于 $V_1k=qA$，单射性和（50.11）迫使 $k\in E\subset P$。

置 $L=H_2+H_4$。同一奇数轮环境给
$$
V_0L=(G_3+G_5)\otimes A\subset O\otimes A.
$$
故 $\dim L\le3$。另一方面，$L$ 到 $P$ 的投影为 $E$，所以恰有 $\dim L=3$，且 $L$ 是某个线性映射 $T:E\to Q$ 的图。

由
$$
H_2=\operatorname{span}(a^2u+bv,w),
$$
得到 $Tw=0$、$Tu=(b/a^2)v$。因此 $T(G_2)=\mathbb Cv$。又因 $H_4$ 到 $G_4$ 和 $Q_4$ 的投影都是同构，
$$
T(G_4)=Q_4,\qquad \dim Q_4=2.
$$
$E$ 三维且 $w\ne0$ 在核中，所以 $\operatorname{rank}T=2$，继而
$$
\operatorname{im}T=Q_4\quad\text{且}\quad v\in Q_4.
$$
现在比较 $V_1p=vB$ 与 $V_1G_3=Q_4\otimes B$。单射性给 $p\in G_3$。再比较 $V_0k=pA$ 与 $V_0H_2=G_3\otimes A$，得到 $k\in H_2$。

但 $k\in P$，且 $P\perp Q$、$b\ne0$ 使
$$
H_2\cap P=\mathbb Cw.
$$
故 $k\parallel w$。定理50.2在六终端要求 $D\ge13$，与 $D=9$ 矛盾。因此 $D\ge10$。证明完毕。

**推论50.4（任意二周期纯环境的六终端精确容量）。** 在同一固定 Stinespring 表示的实际新环境输入无关且具有周期至多二的接收器类中，服务前六个完整参考终端的精确最小接收维数为
$$
\boxed{d_{6}^{\mathrm{pure},\,\mathrm{period}\le2}=8.}
\tag{50.12}
$$

证明。共同环境射线的情形，在每轮实际输入空间的和上去掉这个共同环境，就得到单个部分等距；将其补成逐轮纯空白的固定接收酉，第9节给出 $D\ge2\cdot6-1=11$。不同的两个环境射线若非正交，定理50.3给出更强的 $D\ge10$；若正交，第47节的五终端低维回归刚性及回归容量界排除 $D\le7$ 的六终端实现。第39节的八维正交交替构造达到下界。证明完毕。

周期条件指同一 Stinespring 表示下的实际纯环境射线；可将同射线向量的相位吸入相应轮次的全部接收系数，统一选取周期代表。这个坐标选择不改变物理接收通道，不提供额外轮次控制。

本节没有将任意七维纯环境序列归约为两周期，也未排除早期混合附加态。定理50.1、50.3没有证明非正交子类的下界可达；定理50.2的精确值另有二步回归前提。一般六终端问题仍只有 $7\le d_{\mathrm{CPTP},6}\le8$；式（50.12）只结算上述二周期纯环境子类。

## 追加锚（本行以下为增补区）

## 51. 二维本原指数与一项 Wielandt 界的版本核对

第45节的二维纯轨道例子同时给出一个本原 CPTP 通道，其严格正性指数恰为三。它的伴随是保单位完全正映射，严格正性指数也恰为三。本节逐项计算这两个指数，并与一份明确版本的文献陈述比较。

核对对象为 Owen Ekblad 的 *A note on the quantum Wielandt inequality*，arXiv:2504.21638v3，PDF 首页日期为2025年12月11日。以下关于原文的定位均指这份七页版本，不把未核对的其他版本或出版文本视为相同陈述。[^ekblad_v3]

### 51.1 本原性与待核对的数值界

记 $M_d$ 为复 $d\times d$ 矩阵。一个正映射 $\Lambda:M_d\to M_d$ 称为严格正，如果它把每个非零半正定矩阵送到正定矩阵；如果某个正整数次迭代严格正，则称其本原。对本原映射定义

$$
q(\Lambda)=\min\{n\ge1:
\Lambda^n(X)>0\text{ 对全部 }0\ne X\succeq0\text{ 成立}\}.
\tag{51.1}
$$

所核对版本的第1页 Theorem A 声称：对保单位本原 Schwarz 映射，

$$
q(\Lambda)\le2(d-1)^2.
\tag{51.2}
$$

第2页 Theorem B 对全部本原 2-positive 映射声称同一界，并紧接着明确说明既不要求保单位，也不要求保迹。这里的 $d$ 是矩阵的阶数；原文将 $M_D$ 定义为 $D\times D$ 矩阵，而不是把 $D$ 用作矩阵空间的维数 $d^2$。

下面给出的二维映射分别满足这两条陈述的假设，但都有 $q=3$；（51.2）在 $d=2$ 时的右侧为二。

### 51.2 一个严格正性指数为三的 CPTP 通道

在 $\mathbb C^2$ 的正交基 $|0\rangle,|1\rangle$ 上置

$$
|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
\qquad
L_0=|1\rangle\langle0|,
\qquad
L_1=|+\rangle\langle1|.
\tag{51.3}
$$

由 $L_0^*L_0+L_1^*L_1=I$，映射

$$
\Theta(X)=L_0XL_0^*+L_1XL_1^*
=X_{00}|1\rangle\langle1|+X_{11}|+\rangle\langle+|
\tag{51.4}
$$

是 CPTP，特别也是 2-positive。

**命题51.1。** 通道 $\Theta$ 本原，且 $q(\Theta)=3$。

证明。直接迭代（51.4）给

$$
\Theta^2(X)=\frac{X_{11}}2|1\rangle\langle1|
+\left(X_{00}+\frac{X_{11}}2\right)|+\rangle\langle+|,
\tag{51.5}
$$

$$
\Theta^3(X)=
\left(\frac{X_{00}}2+\frac{X_{11}}4\right)|1\rangle\langle1|
+\left(\frac{X_{00}}2+\frac{3X_{11}}4\right)|+\rangle\langle+|.
\tag{51.6}
$$

对任意 $0\ne X\succeq0$，两个对角元非负，且 $X_{00}+X_{11}=\operatorname{Tr}X>0$。所以（51.6）的两个系数均严格正。$|1\rangle,|+\rangle$ 线性独立，两个秩一正算子的正权和因此正定。故 $\Theta^3$ 严格正。

另一方面，

$$
\Theta(|0\rangle\langle0|)=|1\rangle\langle1|,
\qquad
\Theta^2(|0\rangle\langle0|)=|+\rangle\langle+|,
\tag{51.7}
$$

均为秩一，前两次迭代都非严格正。这就证明 $q(\Theta)=3$。证明完毕。

该通道正是第45节二维锐性例子。这里不仅追踪其中一条轨道，还用（51.6）对全部非零半正定输入验证本原性，因此它满足所核对 Theorem B 的全部假设。

### 51.3 保单位伴随仍具有指数三

取 Hilbert–Schmidt 伴随 $\Phi=\Theta^*$。由（51.3），

$$
\Phi(X)=L_0^*XL_0+L_1^*XL_1
=\operatorname{diag}\bigl(\langle1|X|1\rangle,
\langle+|X|+\rangle\bigr).
\tag{51.8}
$$

这是完全正映射，且 $\Phi(I)=I$。保单位完全正映射满足 Schwarz 不等式，所以它属于所核对 Theorem A 的映射类。

**命题51.2。** 映射 $\Phi$ 本原，且 $q(\Phi)=3$。

证明。对任意 $X$，记

$$
\beta=\langle1|X|1\rangle,\qquad
\gamma=\langle+|X|+\rangle.
$$

逐次应用（51.8）得到

$$
\Phi^2(X)=\operatorname{diag}\left(
\gamma,\frac{\beta+\gamma}{2}\right),
\qquad
\Phi^3(X)=\operatorname{diag}\left(
\frac{\beta+\gamma}{2},\frac{\beta+3\gamma}{4}\right).
\tag{51.9}
$$

当 $0\ne X\succeq0$ 时，$\beta,\gamma\ge0$。若两者均为零，则 $X^{1/2}$ 同时消灭 $|1\rangle$ 和 $|+\rangle$；这两个向量张成整个空间，迫使 $X=0$，矛盾。所以 $\beta+\gamma>0$，（51.9）的两个末态对角元均严格正。

取 $|-\rangle=(|0\rangle-|1\rangle)/\sqrt2$，则

$$
\Phi(|-\rangle\langle-|)=\operatorname{diag}(1/2,0),
\qquad
\Phi^2(|-\rangle\langle-|)=\operatorname{diag}(0,1/4).
\tag{51.10}
$$

前两次均非正定，而第三次对全部非零半正定输入正定。因此 $q(\Phi)=3$。证明完毕。

命题51.1、51.2是分别对两类映射的直接核验。它们排除了该精确版本 Theorem B、Theorem A 在二维所写的上界二；这个结论不以某个证明步骤有缺口为推断依据。

### 51.4 加权迹不能直接替代普通秩

原文还有一处可单独定位的机制问题。其第2页把投影关系 $p\sim q$ 定义为普通迹相等 $\operatorname{Tr}p=\operatorname{Tr}q$。第4页 Corollary 3.4 的证明在得到

$$
0\preceq\varrho^{1/2}\Lambda^\kappa(p)\varrho^{1/2}
\preceq\varrho^{1/2}q\varrho^{1/2},
\qquad \Lambda^*(\varrho)=\varrho>0
\tag{51.11}
$$

后，声称取迹即可推出 $\Lambda^\kappa(p)=q$。但普通迹相等并不保证 $\operatorname{Tr}(\varrho p)=\operatorname{Tr}(\varrho q)$。下面的三维例子把这两个量明确分开。

在 $M_3$ 上定义

$$
\mathcal F(X)=\operatorname{diag}\left(
X_{33},X_{33},\frac{\operatorname{Tr}X}{3}\right).
\tag{51.12}
$$

它的 Kraus 算子为

$$
|1\rangle\langle3|,\quad |2\rangle\langle3|,
\quad \frac1{\sqrt3}|3\rangle\langle j|\quad(j=1,2,3).
\tag{51.13}
$$

所以 $\mathcal F$ 完全正且保单位，但不保迹：
$\mathcal F^*(I)=\operatorname{diag}(1/3,1/3,7/3)$。直接计算得

$$
\mathcal F^2(X)=\operatorname{diag}\left(
\frac{\operatorname{Tr}X}{3},\frac{\operatorname{Tr}X}{3},
\frac{2X_{33}}3+\frac{\operatorname{Tr}X}{9}\right).
\tag{51.14}
$$

该式对全部非零半正定输入正定；$\mathcal F$ 自身并非严格正。因此 $\mathcal F$ 本原且 $q(\mathcal F)=2$。归一化正定不动密度为

$$
\varrho=\operatorname{diag}(1/5,1/5,3/5),
\qquad \mathcal F^*(\varrho)=\varrho.
\tag{51.15}
$$

它的乘法域恰为标量矩阵。确实，若 $X$ 在乘法域中，则第三个对角元的 Schwarz 等号要求

$$
\frac{\operatorname{Tr}(X^*X)}3
=\left|\frac{\operatorname{Tr}X}{3}\right|^2,
\tag{51.16}
$$

Hilbert–Schmidt Cauchy–Schwarz 的等号条件迫使 $X$ 为标量矩阵。

这一结论对全部迭代也成立，可直接核验而不依赖有争议的秩增长步骤。$\mathcal F^n$ 对角输出的权重来自随机矩阵

$$
T=\begin{pmatrix}
0&0&1\\
0&0&1\\
1/3&1/3&1/3
\end{pmatrix}^{\!n}.
\tag{51.17}
$$

当 $n=1$ 时第三行全正；当 $n\ge2$ 时全部行全正。任取一行正权重 $t_j$，令 $m=\sum_jt_jX_{jj}$。相应的单侧 Schwarz 缺陷是

$$
\sum_jt_j\sum_{i\ne j}|X_{ij}|^2
+\sum_jt_j|X_{jj}-m|^2.
\tag{51.18}
$$

它为零即迫使非对角项全部为零、对角项全部相等。因此所有迭代的乘法域都是 $\mathbb CI$，乘法指数 $\kappa(\mathcal F)=1$。

现在取两个等普通秩投影

$$
p=\operatorname{diag}(1,1,0),\qquad
q=\operatorname{diag}(1,0,1).
\tag{51.19}
$$

则

$$
\mathcal F^\kappa(p)=\operatorname{diag}(0,0,2/3)\preceq q,
\qquad \mathcal F^\kappa(p)\ne q,
\tag{51.20}
$$

而

$$
\operatorname{Tr}(\varrho p)=2/5,\qquad
\operatorname{Tr}(\varrho q)=4/5.
\tag{51.21}
$$

该映射满足原文所列的保单位、本原、Schwarz 假设，乘法域也已经稳定，却把投影 $p$ 的普通秩从二降到一。因此原文 Corollary 3.4 的相应结论及第5页 Corollary 3.5 的普通秩严格增长结论均不成立。这个三维例子本身没有违反（51.2），因为其指数二小于右侧八；它只定位从忠实加权迹到普通秩的错误迁移。

原文 Lemma 3.1 的式（3.3）明确要求 $X$ 和 $X^*$ 的两条加权范数等号。只满足单侧 Schwarz 等号的矩阵不能反驳这条双侧判据，本节也不把它列为额外缺口。

### 51.5 结论的适用范围

二维计算直接针对 arXiv:2504.21638v3 所写的具体常数及假设，三维计算解释其普通秩增长论证中缺失的等式。它们不否定保留保单位与保迹条件的既有结果，也没有判定替代常数、其他正确的二次阶界或其他版本的状态。本节不据这些核对作文献原创性断言。

第48节的低秩长延迟反例由多个周期组件构成，并非本原；其超多项式结论和一般有限上界均不依赖这份文献。这里的本原指数反例则满足本原性，解决的是不同的、已写出具体常数的原文陈述。

[^ekblad_v3]: Owen Ekblad, *A note on the quantum Wielandt inequality*, [arXiv:2504.21638v3](https://arxiv.org/pdf/2504.21638v3)，2025年12月11日版本。第1页：$M_D$、本原性、严格正性指数及 Theorem A；第2页：Theorem B、无保单位或保迹要求的说明，以及 $p\sim q$ 的普通迹定义；第4页：Corollary 3.4 的加权迹步骤；第5页：Corollary 3.5 的秩增长陈述。

## 追加锚（本行以下为增补区）

## 52. 三个线性无关循环纯环境的六终端下界

固定非退化来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，$ab\ne0$、$|a|^2+|b|^2=1$。接收器独立纯启动，每轮使用同一个全域 CPTP 通道，全部持久系统计入接收空间 $K$，活动记忆和参考不可访问，前六个终端恢复完整参考—活动记忆—原档案联合态。

**定理52.1（三周期独立环境的六终端容量下界）。** 如果同一固定 Stinespring 表示的前六轮实际新环境依次为输入无关纯向量
$$
A,B,C,A,B,C,
$$
且 $A,B,C$ 线性无关，则
$$
\boxed{D:=\dim K\ge8.}
\tag{52.1}
$$
不要求三条环境方向正交。

证明。记 $V_i x=V(x\otimes|i\rangle)$、初始接收态为单位 $k$。每个终端的来源两列写成
$$
\Psi_n^i=|0\rangle x_n^i+|1\rangle y_n^i,
$$
令 $H_n=\operatorname{span}\{x_n^0,x_n^1\}$、$G_n=\operatorname{span}\{y_n^0,y_n^1\}$。首步有正交单位向量 $p,q$，第二步有正交单位向量 $u,v,w$，使
$$
H_1=\operatorname{span}(p,q),\quad G_1=\mathbb Cp,
$$
$$
H_2=\operatorname{span}(a^2u+bv,w),\quad G_2=\operatorname{span}(u,w),
\quad H_2\cap G_2=\mathbb Cw.
$$
对 $n\ge2$，$H_n,G_n$ 均二维。对 $n\ge3$，来源按初始位与最后发射位给出四个非零、支撑互不相交的档案向量；$m_0,m_1$ 线性独立，故 Bell 输入的参考—活动记忆边缘秩为四。实际环境纯且与来源输入无关，使接收后的参考—活动记忆—接收器联合态纯，并保持这个不可访问边缘。因此四个接收系数向量线性独立，得到
$$
H_n\cap G_n=0.
\tag{52.2}
$$

依第1/4、第2/5、第3/6轮分组，定义两类输入位的累计接收域
$$
\begin{array}{lll}
H_A=\mathbb Ck+H_3,&H_B=H_1+H_4,&H_C=H_2+H_5,\\
G_A=\mathbb Ck+G_3,&G_B=G_1+G_4,&G_C=G_2+G_5.
\end{array}
\tag{52.3}
$$
$V_0H_A,V_0H_B,V_0H_C$ 分别落在 $K\otimes A,K\otimes B,K\otimes C$，三个环境向量线性无关，故这些像为代数直和。$V_0$ 单射，于是
$$
\dim H_A+\dim H_B+\dim H_C\le D.
\tag{52.4}
$$
同理，
$$
\dim G_A+\dim G_B+\dim G_C\le D.
\tag{52.5}
$$

逐个环境块都需要至少五维的两位输入总量：

- $H_3,G_3$ 各二维且交零，非零 $k$ 不可能同时属于它们。因此 $\dim H_A+\dim G_A\ge5$。
- 若 $\dim H_B+\dim G_B=4$，两项必都为二，故 $H_1=H_4$ 且 $p\in G_4$。这使非零 $p\in H_4\cap G_4$，矛盾。因此该和至少五。
- 若 $\dim H_C+\dim G_C=4$，则 $H_2=H_5$、$G_2=G_5$，从而非零 $w\in H_5\cap G_5$，矛盾。因此该和也至少五。

三式相加给
$$
2D\ge15,
\tag{52.6}
$$
故整数 $D\ge8$。证明完毕。

本命题不覆盖三个不同环境射线只张成二维的情况，也不将任意六轮纯环境预设为三周期；初始混合附加态同样不在这个子类内。

一般六终端固定 CPTP 接收的容量仍保留 $7\le d_{\mathrm{CPTP},6}\le8$；本节只排除上述三周期、线性无关纯环境子类中的七维候选。

## 追加锚（本行以下为增补区）

## 53. 七维混合分支的环境交叠约束

固定非退化已知来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，$ab\ne0$、$|a|^2+|b|^2=1$。接收器独立纯启动，全部持久系统计入七维 $K$，每轮使用同一个全域 CPTP 接收通道，活动记忆和参考不可访问，前六个终端精确恢复完整参考—活动记忆—原档案联合态。

记可逆编码固定附加态的秩为 $r_n$。档案支撑秩为 $2,3,4,4,4,4$，因此
$$
r_1\le3,\quad r_2\le2,\quad r_3=r_4=r_5=r_6=1.
$$
前面各款先讨论 $r_2=2$ 分支；最后一款处理 $r_2=1$ 时第一终端附加态的秩。第三终端纯不表示第三轮新环境纯：该轮会把第二终端的混合附加因子排入新环境，并可与旧环境纠缠。第四、第五、第六轮的新环境才由相邻纯终端保证是输入无关纯向量 $\eta_4,\eta_5,\eta_6$。

### 53.1 第二终端秩二与第三轮固定等距块

第二终端的六维编码支撑可写成 $Q\otimes\Gamma\subset K$，其中 $\dim Q=3$、$\dim\Gamma=2$，余下的 $Z=(Q\otimes\Gamma)^\perp$ 一维。取 $Q$ 中正交单位 $u,v,w$，置
$$
c=\sqrt{|a|^4+|b|^2},\quad
z=\frac{a^2u+bv}{c},\quad
H=\operatorname{span}(z,w),\quad G=\operatorname{span}(u,w).
$$
固定 $V_i x=V(x\otimes|i\rangle)$。沿第27节的纯化系数比较，存在等距 $R:\Gamma\to E$、二维环境 $F=R\Gamma$，以及正交单位接收向量 $s,t,r,j$，使对全部 $\xi\in\Gamma$ 有
$$
V_0(z\otimes\xi)=s\otimes R\xi,\quad
V_0(w\otimes\xi)=t\otimes R\xi,
$$
$$
V_1(u\otimes\xi)=r\otimes R\xi,\quad
V_1(w\otimes\xi)=j\otimes R\xi.
$$
令 $A=\operatorname{span}(s,t)=G_3$、$B=\operatorname{span}(r,j)$，则
$$
V_0(H\otimes\Gamma)=A\otimes F,\qquad
V_1(G\otimes\Gamma)=B\otimes F.
\tag{53.1}
$$
两像各四维，$A\perp B$。实际第三终端支撑为 $C_3=A\oplus B$。

对 $n=3,4,5,6$，在标准活动记忆基下明确写实际来源两列为
$$
\Psi_n^i=|0\rangle_Mu_n^i+|1\rangle_Mv_n^i,
\qquad
H_n=\operatorname{span}\{u_n^0,u_n^1\},\quad
G_n=\operatorname{span}\{v_n^0,v_n^1\}.
$$
它们均二维、交零，$C_n=H_n+G_n$ 四维。第三轮等距块具体产生
$$
\Psi_3^0=c\,m_0s+ab\,m_1r,\qquad
\Psi_3^1=a\,m_0t+b\,m_1j.
$$
因为 $m_0=a|0\rangle+b|1\rangle$ 且 $ab\ne0$，这里 $A=G_3$，另一实际输出空间为 $B=Q_3=\operatorname{span}(r,j)$。这使下文 $V_1A$ 使用第四轮环境 $\eta_4$ 的对应明确成立。

对 $n=4,5,6$，有二维 $Q_n$，满足
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n.
\tag{53.2}
$$

### 53.2 环境商维数

**定理53.1（环境商维数约束）。** 第二终端秩二的七维候选必须满足
$$
\dim\operatorname{span}(F,\eta_4,\eta_5,\eta_6)\le3.
\tag{53.3}
$$

证明。若在 $E/F$ 中存在两个独立的尾环境类，选对应 $\eta_n,\eta_m$。则
$$
(A\otimes F)+(G_n\otimes\eta_n)+(G_m\otimes\eta_m)
$$
为维数 $4+2+2=8$ 的代数直和。它包含于七维 $V_0K$，矛盾。证明完毕。

更精确地，任意这种候选都满足两个有限维商空间秩约束
$$
\dim\frac{A\otimes F+\sum_{n=4}^6G_n\otimes\eta_n}{A\otimes F}\le3,
\qquad
\dim\frac{B\otimes F+\sum_{n=4}^6Q_n\otimes\eta_n}{B\otimes F}\le3.
\tag{53.4}
$$
这是两份七维全域位像扣除各自已占四维后的精确剩余容量。各项必须在同一实际向量空间中合计，不把分别的商维数直接相加。

### 53.3 尾环境的三种必要模式

**定理53.2（尾环境模式限制）。** 该七维、第二终端秩二分支的三个纯尾环境，只能有以下三种相对于 $F$ 的模式：
$$
(F,F,F),\qquad(O,F,O),\qquad(O,O,O).
\tag{53.5}
$$
这里每个 $F$ 表示该向量属于二维空间 $F$，不同位置可以是不同射线；每个 $O$ 表示同一条不包含于 $F$ 的环境射线。声明的是必要模式，不宣称这三类均可实现。

证明。先设 $\eta_4\in F$。若 $\eta_5\notin F$，则 $V_1G_3=Q_4\otimes\eta_4$ 与 $V_1G_4=Q_5\otimes\eta_5$ 的不同环境射线迫使 $A\cap G_4=0$。于是 $V_0K$ 中的
$$
(A\otimes F)+(G_4\otimes\eta_4)+(G_5\otimes\eta_5)
$$
是 $4+2+2=8$ 维直和，矛盾。因此 $\eta_5\in F$。

若进一步有 $\eta_6\notin F$，则 $V_0K$ 中位于 $K\otimes F$ 的子空间
$$
R=(A\otimes F)+(G_4\otimes\eta_4)+(G_5\otimes\eta_5)
$$
必须至多五维，以容纳与它交零的二维 $G_6\otimes\eta_6$。令 $\pi_A:K\to K/A$。于是 $\dim (\pi_A\otimes I)R\le1$。若 $\eta_4,\eta_5$ 不共线，固定 $V_1$ 又使 $A\cap G_4=0$，给二维的 $\pi_A(G_4)\otimes\eta_4$，矛盾。因此 $\eta_4\parallel\eta_5$。此时商维数至多一意味着
$$
\dim(A+G_4+G_5)\le3.
$$
但 $\eta_5\in F$、$\eta_6\notin F$，固定 $V_1$ 迫使 $G_4\cap G_5=0$，两个二维空间不能同时位于上述三维空间中。矛盾。因此 $\eta_6\in F$，得到第一种模式。

现在设 $\eta_4\notin F$。先记一个交空间约束：若另有 $\eta_j\notin F$，且 $\eta_j\not\parallel\eta_4$，定理53.1使
$$
\eta_j=c\eta_4+f,\qquad c\ne0,\quad 0\ne f\in F.
$$
逐个独立环境分量比较可知
$$
\bigl((A\otimes F)+(G_4\otimes\eta_4)\bigr)
\cap(G_j\otimes\eta_j)
=(A\cap G_4\cap G_j)\otimes\eta_j.
\tag{53.6}
$$
前一个空间六维，后一个二维，联合包含于七维 $V_0K$，故（53.6）的交至少一维。特别地 $A\cap G_4\ne0$。

若 $\eta_5\notin F$，则它必须与 $\eta_4$ 共线：否则（53.6）给 $A\cap G_4\ne0$，而 $V_1A\subset K\otimes\eta_4$、$V_1G_4\subset K\otimes\eta_5$ 强制这个交为零。共同外部射线又使
$$
\dim(G_4+G_5)\le3,
$$
因为其张量该射线与四维 $A\otimes F$ 交零。故 $G_4\cap G_5\ne0$，固定 $V_1$ 进一步强制 $\eta_6\parallel\eta_5$。得到第三种模式。

最后取 $\eta_5\in F$。如果 $\eta_6\notin F$，它必须与 $\eta_4$ 共线：否则（53.6）再次给 $A\cap G_4\ne0$，但 $V_1$ 在 $A,G_4$ 上分别使用 $\eta_4\notin F$、$\eta_5\in F$，迫使交为零。若反而 $\eta_6\in F$，则
$$
R_F=(A\otimes F)+(G_5\otimes\eta_5)+(G_6\otimes\eta_6)
$$
与 $G_4\otimes\eta_4$ 交零，且两者都包含于七维 $V_0K$，所以 $\dim R_F\le5$。对 $A$ 取接收商，四维 $A\otimes F$ 是商映射在 $R_F$ 上的核，故
$$
\dim(\pi_A\otimes I)R_F\le1.
$$
特别有 $\dim\pi_A(G_5)\le1$，因此 $A\cap G_5\ne0$。但固定 $V_1$ 在 $A=G_3$ 上使用 $\eta_4\notin F$，在 $G_5$ 上使用 $\eta_6\in F$；不同射线迫使 $A\cap G_5=0$，矛盾。因此 $\eta_6$ 必须位于与 $\eta_4$ 相同的外部射线，得到第二种模式。证明完毕。

### 53.4 定量环境交叠

置
$$
x=|a|^2,\quad y=|b|^2,\quad d=x^2+y,
\qquad \kappa=\frac{x}{\sqrt d}.
$$
令 $t_j$ 为来源初态 $|0\rangle$ 在第 $j$ 终端的零记忆概率，则
$$
t_0=1,\qquad t_j=1-y t_{j-1},\qquad
t_j=x+y^2t_{j-2}\quad(j\ge2).
\tag{53.7}
$$
定义
$$
\sigma_m=\sqrt{\min\left\{
 x\frac{t_{m-1}}{t_m},\ x\frac{t_{m-2}}{t_{m-1}}
\right\}}\quad(m\ge3).
\tag{53.8}
$$
这是实际两个记忆系数空间 $H_m,G_m$ 的最小主角奇异值。

**定理53.3（环境交叠的显式正下界）。** 对 $n=5,6$，上述七维、第二终端秩二分支必须满足
$$
\boxed{
\|P_F\eta_n\|^2
\ge\frac{(\sigma_{n-1}-\kappa)^2}{4}>0.
}
\tag{53.9}
$$
所以第五、第六轮新环境都不能正交于第三轮排出附加因子的环境 $F$。

证明。记 $m=n-1\ge4$、$s_n=\|P_F\eta_n\|^2$。由（53.1）、（53.2）及 $V_0$ 等距，对任意单位 $\xi\in H_m$ 有
$$
\|P_{H\otimes\Gamma}\xi\|^2
=\|P_{A\otimes F}V_0\xi\|^2
=s_n\|P_A\widehat V_0\xi\|^2\le s_n.
\tag{53.10}
$$
这里 $\widehat V_0$ 是 $V_0$ 在该实际域上去掉共同单位环境 $\eta_n$ 后的等距。同理，对任意单位 $\gamma\in G_m$，
$$
\|P_{G\otimes\Gamma}\gamma\|\le\sqrt{s_n}.
\tag{53.11}
$$

取
$$
h=\frac{\overline b\,u-\overline a^{\,2}v}{c}.
$$
则 $H^\perp\cap Q=\mathbb Ch$、$G^\perp\cap Q=\mathbb Cv$，且 $|\langle h,v\rangle|=\kappa$。$H_m$ 二维而 $Z$ 一维，故可选单位向量 $\zeta\in H_m\cap Z^\perp$。将它正交分解为
$$
\zeta=\zeta_H+\zeta_h,
\qquad \zeta_H\in H\otimes\Gamma,
\quad \zeta_h\in\mathbb Ch\otimes\Gamma.
$$
式（53.10）给 $\|\zeta_H\|\le\sqrt{s_n}$，而 $\|\zeta_h\|\le1$。记 $W=(G\otimes\Gamma)^\perp=(\mathbb Cv\otimes\Gamma)\oplus Z$，则
$$
\|P_W\zeta\|
\le\|P_W\zeta_h\|+\|\zeta_H\|
\le\kappa+\sqrt{s_n}.
\tag{53.12}
$$
对任意单位 $\gamma\in G_m$，沿 $W\oplus(G\otimes\Gamma)$ 分解内积，并用（53.11），得到
$$
|\langle\gamma,\zeta\rangle|
\le\|P_W\zeta\|
+\|P_{G\otimes\Gamma}\gamma\|\,
 \|P_{G\otimes\Gamma}\zeta\|
\le\kappa+2\sqrt{s_n}.
$$
取单位 $\gamma$ 的上确界，便有
$$
\|P_{G_m}\zeta\|\le\kappa+2\sqrt{s_n}.
\tag{53.13}
$$

实际来源的内积给出反向下界。对两个来源初始标签，零记忆系数范数平方分别为 $t_m,t_{m-1}$。不同标签的档案支撑正交，精确可逆编码保持这些内积。沿第26节的同轮零、一输入像正交计算，$P_{H_m}P_{G_m}|_{H_m}$ 的两个特征值恰为
$$
\lambda_m=x\frac{t_{m-1}}{t_m},\qquad
\lambda_{m-1}=x\frac{t_{m-2}}{t_{m-1}}.
\tag{53.14}
$$
因此每个单位 $\zeta\in H_m$ 都满足 $\|P_{G_m}\zeta\|\ge\sigma_m$。与（53.13）合并给
$$
\sigma_m\le\kappa+2\sqrt{s_n}.
$$

最后证明严格正间隙。由（53.7），$t_j>x$ 对全部 $j\ge2$ 成立。对任意 $j\ge3$，利用 $d+xy=1$，有
$$
\lambda_j>\kappa^2
\iff d t_{j-1}>x(1-y t_{j-1})
\iff t_{j-1}>x.
\tag{53.15}
$$
$m\ge4$ 使（53.14）的两个指标都至少三，所以 $\sigma_m>\kappa$。移项、平方即得（53.9）。证明完毕。

这两个终端可以使用同一个显式正界。式（53.7）的闭式为
$$
t_j=\frac{1+y(-y)^j}{1+y},\qquad
\lambda_j-x=\frac{xy(-y)^{j-1}}{t_j}.
$$
故 $\lambda_3,\lambda_5>x>\lambda_4$，从而
$$
\sigma_4=\sigma_5=\sqrt{x\frac{t_3}{t_4}},
\qquad
\|P_F\eta_5\|^2,\ \|P_F\eta_6\|^2
\ge\frac14\left(\sqrt{x\frac{t_3}{t_4}}-
\frac{x}{\sqrt{x^2+y}}\right)^2>0.
\tag{53.16}
$$

第四轮的前一终端是 $m=3$，其较小特征值恰为 $\lambda_2=x^2/d=\kappa^2$，所以上述主角估计在该轮本身只给零下界。不过，六终端完整合同下的模式限制（53.5）给出额外推论：$FFF$ 中 $\|P_F\eta_4\|^2=1$；$OFO$、$OOO$ 中 $\eta_4\parallel\eta_6$，单位向量的投影范数相同。式（53.16）的右端至多 $1/4$，因为 $0\le\kappa<\sigma_4\le1$。故三个纯尾环境共同满足
$$
\boxed{
\|P_F\eta_n\|^2
\ge\frac14\left(\sqrt{x\frac{t_3}{t_4}}-
\frac{x}{\sqrt{x^2+y}}\right)^2>0,
\qquad n=4,5,6.
}
$$
第四轮的正界是结合环境模式继承的结果，没有把 $m=3$ 本身的主角间隙改称严格正。外部射线虽然不包含于 $F$，却不能正交于 $F$。这些条件都是必要条件，未被宣称为充分条件。

### 53.5 纯第二终端的早期秩限制

**定理53.4（纯第二终端排除秩三第一终端）。** 在同一七维合同中，若 $r_2=1$，则 $r_1=3$ 不可能。证明只需前五个完整参考终端，因而该分支只余 $r_1=1$ 或 $2$。

证明。反设 $r_1=3$。第一终端附加态的纯化与第二终端纯性，沿第29节式（29.37）给出六个正交单位接收向量 $p_\alpha,q_\alpha$、三个正交单位 $u,v,w$ 和三个正交单位环境向量 $f_\alpha$，使对 $\alpha=1,2,3$ 有
$$
V_0p_\alpha=u\otimes f_\alpha,\qquad
V_1p_\alpha=v\otimes f_\alpha,\qquad
V_0q_\alpha=w\otimes f_\alpha.
$$
这里 $V_i x=V(x\otimes|i\rangle)$，同一个 $V$ 是固定通道的 Stinespring 等距。记
$$
X=\operatorname{span}\{p_\alpha,q_\alpha\},\quad
F=\operatorname{span}\{f_\alpha\},\quad
U=\operatorname{span}(u,w)=G_2.
$$
则
$$
\dim X=6,\quad\dim F=3,\quad V_0X=U\otimes F.
\tag{53.17}
$$
第二终端的实际系数空间为
$$
H_2=\operatorname{span}(a^2u+bv,w),\qquad G_2=U,
\qquad \dim(H_2+G_2)=3.
\tag{53.18}
$$
第三至第五轮的新环境 $\eta_3,\eta_4,\eta_5$ 为输入无关纯向量，并有
$$
V_0H_{n-1}=G_n\otimes\eta_n,\quad
V_1G_{n-1}=Q_n\otimes\eta_n\qquad(n=3,4,5).
\tag{53.19}
$$
各 $H_n,G_n,Q_n$ 均二维；$n\ge3$ 时 $C_n=H_n+G_n=G_n\oplus Q_n$ 四维，且 $H_n$ 到 $G_n,Q_n$ 的两个投影都是同构。

**尾环境共线。**

首先，各 $\eta_n$ 都属于 $F$。否则（53.17）与 $G_n\otimes\eta_n$ 形成 $6+2=8$ 维直和，不能包含在七维 $V_0K$ 中。

令 $\pi:K\to K/U$ 为商映射。因为 $(\pi\otimes I_E)V_0$ 在六维 $X$ 上为零，
$$
\mathcal Z:=(\pi\otimes I_E)V_0K,
\qquad \dim\mathcal Z\le1.
\tag{53.20}
$$
对每个尾终端，$\pi(G_n)\otimes\eta_n\subseteq\mathcal Z$。

若 $\eta_3,\eta_4$ 不共线，固定 $V_1$ 在 $U=G_2$、$G_3$ 上的像分别属于两条不同环境线，因此 $U\cap G_3=0$。于是 $\dim\pi(G_3)=2$，违反（53.20）。故可统一选取 $\eta_3=\eta_4=\eta$。

$G_3,G_4$ 不可能都等于 $U$：否则（53.19）和 $V_0$ 单射性使 $H_2=H_3$，继而 $C_3=C_2$，与三维、四维支撑秩差矛盾。因此（53.20）恰为一维，其接收商方向由 $\pi(G_3)$ 或 $\pi(G_4)$ 确定，且
$$
W:=U+G_3+G_4,\qquad \dim W=3.
\tag{53.21}
$$
若 $\eta_5$ 不共线于 $\eta$，固定 $V_1$ 在 $G_3,G_4$ 上的不同环境像会迫使 $G_3\cap G_4=0$。但这两个二维空间都在三维 $W$ 中，矛盾。故 $\eta_5=\eta$ 也可统一选取，且（53.20）使 $G_5\subseteq W$。

**三维图空间的秩冲突。**

因为 $\eta\in F$，取单位系数向量 $\xi=(\xi_1,\xi_2,\xi_3)$ 使 $\eta=\sum_\alpha\xi_\alpha f_\alpha$，并令
$$
p_\xi=\sum_\alpha\xi_\alpha p_\alpha,\qquad
q_\xi=\sum_\alpha\xi_\alpha q_\alpha.
$$
则
$$
V_0p_\xi=u\eta,\quad V_0q_\xi=w\eta,\quad
V_1p_\xi=v\eta.
\tag{53.22}
$$
（53.17）、（53.19）、（53.21）使整个 $W\otimes\eta$ 包含在 $V_0K$ 中。令
$$
S_0=V_0^{-1}(W\otimes\eta),\qquad S_1=\mathbb Cp_\xi+W.
$$
$S_0$ 恰三维，包含 $p_\xi,q_\xi,H_2,H_3,H_4$。$S_1$ 包含 $p_\xi,G_2,G_3,G_4$，所以共同环境上可写
$$
V_0x=f(x)\otimes\eta\quad(x\in S_0),\qquad
V_1y=g(y)\otimes\eta\quad(y\in S_1),
$$
其中 $f,g$ 等距，$fS_0=W$，且不同输入位正交给
$$
gS_1\perp W.
\tag{53.23}
$$

由（53.18）、（53.22）、（53.23），$H_2$ 到 $W$ 的投影为 $U$。来源同轮系数递推又给 $H_3,H_4$ 到 $W$ 的投影分别为 $G_3,G_4$：其另一个分量分别在 $Q_3=gU$、$Q_4=gG_3$ 中，由（53.23）正交于 $W$。因此
$$
P_WS_0\supseteq U+G_3+G_4=W.
$$
两空间同为三维，所以该投影为同构；存在唯一线性映射 $T:W\to W^\perp$，使 $S_0$ 为其图。

从（53.18）得到
$$
Tw=0,\qquad T(U)=\mathbb Cv.
\tag{53.24}
$$
从 $H_3,H_4$ 到同轮两个接收输出空间的满投影，又得到
$$
T(G_3)=Q_3=gU,\qquad T(G_4)=Q_4=gG_3.
\tag{53.25}
$$
由于 $w\ne0$ 在三维域 $W$ 的核中，$\operatorname{rank}T\le2$；（53.25）的第一项已有秩二，所以 $\operatorname{im}T=gU$。再用（53.25）的第二项，得到 $gG_3\subseteq gU$。$g$ 单射给 $G_3\subseteq U$，两者均二维，故 $G_3=U$。

然而（53.24）称 $T(U)$ 一维，（53.25）称 $T(G_3)$ 二维，矛盾。证明完毕。

本节没有排除全部七维接收器。第二终端秩二的候选须满足上述三种尾模式及环境交叠下界；第二终端纯而第一终端秩二的候选仍未结算。全部早期终端纯的非周期环境也未在此归约。一般六终端固定 CPTP 接收容量仍为 $7\le d_{\mathrm{CPTP},6}\le8$。

## 追加锚（本行以下为增补区）

## 54. 七维第一终端秩二时的尾环境封闭性

### 54.1 实际来源、早期等距块与主结论

固定非退化来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，$ab\ne0$、$|a|^2+|b|^2=1$。七维接收器 $K$ 独立纯启动，同一个全域 CPTP 通道逐轮作用，前六个终端恢复完整参考—活动记忆—原档案联合态。记可逆编码固定附加态的秩为 $r_n$，本节取 $r_2=1$、$r_1=2$。

固定该通道同一份 Stinespring 等距，记 $V_i x=V(x\otimes|i\rangle)$。第一步与第二步纯化比较给两个正数 $\lambda_1,\lambda_2$，四个正交单位接收向量 $p_1,q_1,p_2,q_2$，以及两组正交单位环境向量 $e_1,e_2$ 和 $f_1,f_2$，满足
$$
V_0k=\sum_{\alpha=1}^2\sqrt{\lambda_\alpha}\,p_\alpha\otimes e_\alpha,
\qquad
V_1k=\sum_{\alpha=1}^2\sqrt{\lambda_\alpha}\,q_\alpha\otimes e_\alpha,
\tag{54.1}
$$
$$
V_0p_\alpha=u\otimes f_\alpha,\qquad
V_1p_\alpha=v\otimes f_\alpha,\qquad
V_0q_\alpha=w\otimes f_\alpha.
\tag{54.2}
$$
这里 $k$ 是单位初态，$u,v,w$ 正交归一，$\lambda_1+\lambda_2=1$。令
$$
P_0=\operatorname{span}(p_1,p_2),\quad
X=\operatorname{span}(p_1,q_1,p_2,q_2),\quad
F=\operatorname{span}(f_1,f_2),\quad
U=\operatorname{span}(u,w).
$$
所以 $\dim P_0=2$、$\dim X=4$、$\dim F=2$，且
$$
V_0X=U\otimes F,\qquad V_1P_0=\mathbb Cv\otimes F.
\tag{54.3}
$$
第二至第六终端均纯；第三至第六轮新环境是输入无关单位向量 $\eta_3,\eta_4,\eta_5,\eta_6$。写实际来源两列
$$
\Psi_n^i=|0\rangle_Mu_n^i+|1\rangle_Mv_n^i,\qquad
H_n=\operatorname{span}(u_n^0,u_n^1),\quad
G_n=\operatorname{span}(v_n^0,v_n^1),\quad C_n=H_n+G_n.
$$
各 $H_n,G_n$ 二维，$C_2$ 三维、$C_n$ 在 $n\ge3$ 时四维；第二终端有
$$
H_2=\operatorname{span}(a^2u+bv,w),\qquad G_2=U.
\tag{54.4}
$$
对 $3\le n\le6$，有二维 $Q_n$ 使
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n,\qquad G_n\perp Q_n.
\tag{54.5}
$$
同轮来源递推使 $H_n$ 到 $G_n$ 和 $Q_n$ 的两个正交投影均为同构，且 $C_n=G_n\oplus Q_n$。

**定理54.1（秩二第一终端的二维尾环境封闭性）。** 在上述七维六终端合同中，若第一终端可逆附加态秩为二、第二终端纯，则
$$
\boxed{
\operatorname{span}(\eta_3,\eta_4,\eta_5,\eta_6)=F,
\qquad \dim F=2.
}
$$
因此四个纯尾环境都属于第二轮排出附加因子的同一二维环境空间，并且不能全部沿一条射线。结论不要求这些射线彼此正交，也不排除二维空间内的其余候选。

下面先给矩形像约束下的一般环境模式，再证明共同纯尾的交叠限制，并排除两种外部模式，最后合并得到主结论。

### 54.2 矩形像后的环境模式

设 $K$ 七维，$E$ 为环境 Hilbert 空间，$V_0,V_1:K\to K\otimes E$ 为固定等距。给二维子空间 $A\subset K$、$F\subset E$，满足
$$
A\otimes F\subset V_0K.
\tag{54.6}
$$
给有限尾长 $L\ge2$、二维接收子空间 $G_0=A,G_1,\ldots,G_L$，二维 $Q_1,\ldots,Q_L$，以及单位环境向量 $\eta_1,\ldots,\eta_L$，满足
$$
G_j\otimes\eta_j\subset V_0K,\qquad
V_1G_{j-1}=Q_j\otimes\eta_j\quad(1\le j\le L).
\tag{54.7}
$$
该抽象引理不要求 $V_0K\perp V_1K$；实际 CPTP 接收器还满足这个额外正交条件。

**引理54.2（矩形像后的环境模式）。** 尾环境只有以下三种可能形式：

1. 全部 $\eta_j\in F$；此项不限制它们在 $F$ 内的射线。
2. 存在一条不包含于 $F$ 的射线 $O$，全部 $\eta_j\in O$。
3. 存在一条不包含于 $F$ 的射线 $O$ 和一条包含于 $F$ 的射线 $B$，尾环境严格按 $O,B,O,B,\ldots$ 交替。

这只是必要模式，不主张每种模式均可实现。

**证明。** 两个简单的张量维数事实先单独说明。

第一，所有 $\eta_j$ 在 $E/F$ 中的像至多张成一维。若两个像独立，则 $A\otimes F$ 与这两个对应的 $G_j\otimes\eta_j$ 为 $4+2+2=8$ 维代数直和，不能同处七维 $V_0K$。

第二，若 $J$ 是一组环境在 $F$ 内的指标，且
$$
R_F=(A\otimes F)+\sum_{j\in J}G_j\otimes\eta_j,
\qquad \dim R_F\le5,
\tag{54.8}
$$
则
$$
\dim\left(A+\sum_{j\in J}G_j\right)\le3.
\tag{54.9}
$$
令 $\pi_A:K\to K/A$。$(\pi_A\otimes I_E)|_{R_F}$ 的核恰为四维 $A\otimes F$，所以其像至多一维。如果像为零，（54.9）立即成立。否则该像含有某个非零纯张量 $u\otimes f$，且全部 $\pi_A(G_j)\otimes\eta_j$ 都在此单线内；因此所有非零 $\pi_A(G_j)$ 都在共同接收商线 $\mathbb Cu$ 内，仍给（54.9）。

**首环境在 $F$ 内时不会离开。** 若 $\eta_1\in F$，反设 $t\ge2$ 是第一个 $\eta_t\notin F$ 的指标。式（54.8）对 $J=\{1,\ldots,t-1\}$ 的 $R_F$ 与 $G_t\otimes\eta_t$ 交零，故 $\dim R_F\le5$。由（54.9），二维 $G_{t-2}$ 和 $G_{t-1}$（当 $t=2$ 时前者是 $G_0=A$）都在同一至多三维空间中，交非零。固定 $V_1$ 将它们分别送到环境 $\eta_{t-1}\in F$ 和 $\eta_t\notin F$，不同环境线迫使输入交为零，矛盾。因此全部环境在 $F$ 内。

**首环境在 $F$ 外时，全部外部环境同射线。** 现在取 $\eta_1\notin F$。若 $\eta_j\notin F$、$\eta_j\not\parallel\eta_1$，第一条维数事实给
$$
\eta_j=c\eta_1+f,\qquad c\ne0,\quad0\ne f\in F.
$$
逐个环境分量比较得到
$$
\bigl(A\otimes F+G_1\otimes\eta_1\bigr)
\cap(G_j\otimes\eta_j)
=(A\cap G_1\cap G_j)\otimes\eta_j.
\tag{54.10}
$$
左侧两个空间分别六维和二维，同处七维 $V_0K$，故交非零，特别有 $A\cap G_1\ne0$。固定 $V_1$ 因而强制 $\eta_2\parallel\eta_1$。

若 $\eta_2\parallel\eta_1$，当 $L=2$ 时已得到全部尾环境共线；当 $L\ge3$ 时，$G_1+G_2$ 至多三维，因为其张量共同外部环境的像与 $A\otimes F$ 交零。因此 $G_1\cap G_2\ne0$，固定 $V_1$ 给 $\eta_3\parallel\eta_2$。对每个仍有后继的指标重复该论证，全部后续环境都与 $\eta_1$ 共线。这与上面选取的 $\eta_j$ 矛盾。

所以全部外部环境均属于同一射线 $O=\mathbb C\eta_1$。若 $\eta_2\in O$，已经得到全 $O$ 模式；只需讨论 $\eta_2\in F$。

**外部与内部的后继被固定。** 令
$$
R_O=\sum_{\eta_j\in O}G_j,
\qquad
R_F=(A\otimes F)+\sum_{\eta_j\in F}G_j\otimes\eta_j.
$$
两份零位像 $R_O\otimes\eta_1$ 和 $R_F$ 交零。$\dim R_F\ge4$、$\dim R_O\ge2$，故
$$
\dim R_O\le3,\qquad \dim R_F\le5.
\tag{54.11}
$$
于是（54.9）给 $A+\sum_{\eta_j\in F}G_j$ 至多三维。

每个内部指标 $j<L$ 都有 $A\cap G_j\ne0$；固定 $V_1$ 在 $A=G_0$ 上产生环境 $\eta_1\in O$，在 $G_j$ 上产生 $\eta_{j+1}$，所以
$$
\eta_j\in F\Longrightarrow\eta_{j+1}\in O.
\tag{54.12}
$$
另一方面，每个外部指标 $j<L$ 都有 $G_1\cap G_j\ne0$，因为它们均二维且都位于至多三维 $R_O$。固定 $V_1$ 在 $G_1$ 上产生 $\eta_2$，故
$$
\eta_j\in O\Longrightarrow\eta_{j+1}\parallel\eta_2.
\tag{54.13}
$$
式（54.12）、（54.13）给严格交替模式，内部环境的射线固定为 $B=\mathbb C\eta_2\subset F$。证明完毕。

### 54.3 共同纯尾的环境交叠限制

考虑七维固定 CPTP 接收器服务前六个完整参考终端的非退化来源，且第二终端纯。沿标准早期可逆编码，记第二终端接收向量 $u,v,w$ 正交单位，
$$
U=G_2=\operatorname{span}(u,w),\qquad
H_2=\operatorname{span}(a^2u+bv,w),\qquad ab\ne0.
\tag{54.14}
$$
第二轮排出第一终端附加因子的环境空间记为 $F$。它维数等于第一终端附加态秩 $r_1\ge1$，且固定 Stinespring 等距的两个位块满足
$$
U\otimes F\subseteq V_0K,\qquad
\mathbb Cv\otimes F\subseteq V_1K.
\tag{54.15}
$$
假设第三至第六轮的新环境为同一条纯射线；统一选取单位代表 $\eta$。实际系数空间满足
$$
V_0H_{n-1}=G_n\otimes\eta,\qquad
V_1G_{n-1}=Q_n\otimes\eta\quad(3\le n\le6),
\tag{54.16}
$$
其中各 $H_n,G_n,Q_n$ 二维，$C_2=H_2+G_2$ 三维，$C_n=H_n+G_n=G_n\oplus Q_n$ 在 $n\ge3$ 时四维。实际 $H_n$ 到 $G_n$、$Q_n$ 的两个正交投影均为同构。

**引理54.3（共同纯尾的环境交叠限制）。** 上述共同纯尾环境必须满足
$$
\boxed{\eta\perp F.}
\tag{54.17}
$$

**证明。** 反设 $\eta$ 与 $F$ 有非零交叠。令
$$
S_0=H_2+H_3+H_4+H_5,\qquad
S_1=U+G_3+G_4+G_5.
$$
去掉共同环境得到等距 $f:S_0\to K$、$g:S_1\to K$。置
$$
R=fS_0=G_3+G_4+G_5+G_6,\qquad W=gS_1.
\tag{54.18}
$$
不同输入位正交给 $R\perp W$，所以
$$
\dim S_0+\dim S_1\le7.
\tag{54.19}
$$
式（54.15）与非零环境交叠又给
$$
U\perp W,\qquad v\perp R.
\tag{54.20}
$$

两个输入和的维数都至少三。若 $\dim S_1=2$，则 $U=G_3=G_4$，进而 $fH_2=fH_3$，与 $C_2$ 三维、$C_3$ 四维矛盾。若 $\dim S_0=2$，则 $H_2=H_3=H_4$、$G_3=G_4$；这使 $(H_3,G_3)=(H_4,G_4)$，但第53节式（53.14）的两个来源主角特征值相乘给
$$
\delta_n=x^2\frac{t_{n-2}}{t_n},\qquad
\delta_4-\delta_3=\frac{x^3y^2}{t_3t_4}>0,
\quad x=|a|^2,\ y=|b|^2,\ t_j=1-y t_{j-1},\ t_0=1.
\tag{54.21}
$$
因此只需处理 $\dim S_0=3$ 或 $4$。

**若 $\dim S_0=3$。** 此时 $R$ 三维，并且 $G_3+G_4+G_5=R$：否则三个二维空间相等，由 $f$ 单射得 $H_2=H_3=H_4$，仍与（54.21）矛盾。因此 $S_1=U+R$。式（54.20）及 $R\perp W$ 使 $S_1\perp W$，于是 $2\dim S_1\le7$。故 $\dim S_1=3$、$S_1=R$、$U\subset R$。

对 $n=3,4,5$，来源递推给 $P_RH_n=G_n$，所以 $P_RS_0=R$。因此三维 $S_0$ 是一个线性映射 $T:R\to R^\perp$ 的图。由（54.14）、（54.20）及同轮满投影，
$$
Tw=0,\quad T(U)=\mathbb Cv,\quad
T(G_3)=gU,\quad T(G_4)=gG_3.
\tag{54.22}
$$
$w\ne0$ 使 $\operatorname{rank}T\le2$，而后两个像各二维，因此 $gU=gG_3$。$g$ 单射给 $U=G_3$；（54.22）却使同一限制 $T|_U$ 的秩同时是一和二，矛盾。

**若 $\dim S_0=4$。** 式（54.19）使 $\dim S_1=3$，$R$ 四维、$W$ 三维，故 $K=R\oplus W$。由（54.20）得 $U\subset R$，从而 $S_1\subset R$。定义
$$
D=f^{-1}(S_1)\subset S_0.
$$
$f:S_0\to R$ 是满等距，所以 $D$ 三维；它包含 $H_2,H_3,H_4$，因为这三个空间的像分别为 $G_3,G_4,G_5\subset S_1$。

若 $U+G_3+G_4$ 只有二维，则 $U=G_3=G_4$，与 $C_2,C_3$ 的秩差矛盾。因此
$$
U+G_3+G_4=S_1.
\tag{54.23}
$$
由（54.14）、（54.20）、$Q_3,Q_4\subset W\perp S_1$ 得
$$
P_{S_1}H_2=U,\qquad P_{S_1}H_3=G_3,\qquad
P_{S_1}H_4=G_4.
$$
式（54.23）给 $P_{S_1}D=S_1$。三维 $D$ 因而是某个 $T:S_1\to S_1^\perp$ 的图。同样有
$$
Tw=0,\quad T(U)=\mathbb Cv,\quad
T(G_3)=gU,\quad T(G_4)=gG_3.
$$
完全相同的秩一／秩二矛盾排除此情形。

两个可能维数均已排除，故共同尾环境与 $F$ 正交。证明完毕。

### 54.4 共同外部尾环境的排除

**引理54.4（排除共同外部尾环境）。** 回到54.1节的 $r_1=2,r_2=1$ 合同，不可能有
$$
\eta_3\parallel\eta_4\parallel\eta_5\parallel\eta_6,
\qquad \eta_3\notin F.
\tag{54.24}
$$
该结论没有要求外部射线事先正交于 $F$。

**证明。** 选择共同单位代表 $\eta$，相应重标各终端纯向量的整体相位。令
$$
S_0=H_2+H_3+H_4+H_5,\qquad
S_1=U+G_3+G_4+G_5.
$$
去掉共同环境，在这些域上写
$$
V_0x=f(x)\otimes\eta\quad(x\in S_0),\qquad
V_1y=g(y)\otimes\eta\quad(y\in S_1),
$$
其中 $f,g$ 等距。置
$$
R=fS_0=G_3+G_4+G_5+G_6,\qquad W=gS_1.
\tag{54.25}
$$
不同输入位正交给 $R\perp W$。

因为 $\eta\notin F$，$U\otimes F$ 与 $R\otimes\eta$ 的交为零；两者都包含于七维 $V_0K$。因此
$$
\dim S_0=\dim R\le3.
\tag{54.26}
$$
实际上
$$
\dim S_0=\dim R=3,\qquad G_3+G_4+G_5=R.
\tag{54.27}
$$
为核对这一点，若 $\dim S_0=2$，则 $H_2=H_3=H_4$，并由 $f$ 单射得 $G_3=G_4$。若 $\dim(G_3+G_4+G_5)=2$，则 $G_3=G_4=G_5$，再由 $f$ 单射同样得 $H_2=H_3=H_4$。两种情形均使 $(H_3,G_3)=(H_4,G_4)$，但实际来源的主角乘积在这两个终端不同。具体地，置 $x=|a|^2$、$y=|b|^2$、$t_0=1$、$t_j=1-y t_{j-1}$。第53节式（53.14）的两个来源主角特征值相乘给
$$
\delta_n=\det\bigl(P_{H_n}P_{G_n}|_{H_n}\bigr)
=x^2\frac{t_{n-2}}{t_n},\qquad
\delta_4-\delta_3=\frac{x^3y^2}{t_3t_4}>0.
\tag{54.28}
$$
故上述两种情形均不成立，证明（54.27）。

于是 $S_1=U+R$，其维数至少三。由 $R\perp W$、$\dim W=\dim S_1$ 得
$$
\dim S_1\in\{3,4\}.
\tag{54.29}
$$
对 $n=3,4,5$，因为 $Q_n\subset W\perp R$，来源递推给
$$
P_RH_n=G_n.
$$
式（54.27）因此给 $P_RS_0=R$。三维 $S_0$ 是一个线性映射 $T:R\to R^\perp$ 的图，并且
$$
T(G_3)=Q_3=gU,\qquad
T(G_4)=Q_4=gG_3,\qquad
T(G_5)=Q_5=gG_4.
\tag{54.30}
$$

先排除 $\dim S_1=3$。这时 $U\subset R$，而 $0\ne w\in H_2\cap U\subset S_0\cap R$，故 $Tw=0$、$\operatorname{rank}T\le2$。式（54.30）的三个像都是二维，必相等。$g$ 单射给
$$
U=G_3=G_4.
$$
由 $fH_2=G_3$、$fH_3=G_4$ 再得 $H_2=H_3$，从而 $C_2=C_3$，违反三维、四维秩差。因此
$$
\dim S_1=\dim W=4,\qquad K=R\oplus W.
\tag{54.31}
$$

若 $\eta$ 与 $F$ 有非零交叠，$V_0X=U\otimes F$ 与 $V_1S_1=W\otimes\eta$ 的正交性会给 $U\perp W$，进而 $U\subset R$，与 $\dim S_1=4$ 矛盾。因此
$$
\eta\perp F.
\tag{54.32}
$$
由（54.3）和等距性，这迫使
$$
S_0\perp X,\qquad S_1\perp P_0,
\quad\text{故}\quad P_0\perp S_0+S_1.
\tag{54.33}
$$

接着证明 $\eta$ 也正交于第一轮环境支撑。对（54.1）的零位像取环境 $\eta$ 分量，置
$$
p_\eta=(I_K\otimes\langle\eta|)V_0k
=\sum_{\alpha=1}^2\sqrt{\lambda_\alpha}\,
\langle\eta,e_\alpha\rangle p_\alpha.
$$
$V_0k\perp V_1S_1=W\otimes\eta$ 给 $p_\eta\perp W$，式（54.31）给 $p_\eta\in R$。但 $p_\eta\in P_0$，且（54.33）使它正交于包含 $R$ 的 $S_1$。所以 $p_\eta=0$。$p_1,p_2$ 正交且两个 $\lambda_\alpha$ 严格正，故
$$
\eta\perp e_1,e_2.
\tag{54.34}
$$
结合（54.1）和两个尾像，等距性再给
$$
k\perp S_0+S_1.
\tag{54.35}
$$

最后，$k\notin P_0$。否则（54.3）使 $V_1k\in\mathbb Cv\otimes F$ 为非零纯张量；但（54.1）的 Schmidt 秩为二，矛盾。因此 $P_0+\mathbb Ck$ 三维，并由（54.33）、（54.35）正交于 $S_0+S_1$。七维性给
$$
\dim(S_0+S_1)\le4.
\tag{54.36}
$$
两个四维终端支撑 $C_3,C_4$ 都包含于 $S_0+S_1$，故 $C_3=C_4=S_0+S_1$。固定等距 $V$ 将
$$
(H_2\otimes|0\rangle)\oplus(U\otimes|1\rangle)
\quad\text{和}\quad
(H_3\otimes|0\rangle)\oplus(G_3\otimes|1\rangle)
$$
分别映到相同的 $C_3\otimes\eta=C_4\otimes\eta$。单射性使两域相同，按输入位比较得 $H_2=H_3$、$U=G_3$。于是 $C_2=C_3$，再次违反秩差。证明完毕。

### 54.5 外部交替尾环境的排除

仍采用54.1节第一终端秩二、第二终端纯的七维六终端精确接收合同。特别地，
$$
U=G_2=\operatorname{span}(u,w),\quad
H_2=\operatorname{span}(a^2u+bv,w),\quad
V_0X=U\otimes F,
\quad\dim U=\dim F=2.
\tag{54.37}
$$
$u,v,w$ 正交单位，$ab\ne0$。各纯尾满足
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n,\qquad
G_n\perp Q_n\quad(3\le n\le6).
\tag{54.38}
$$
各 $H_n,G_n,Q_n$ 二维，$C_n=H_n+G_n=G_n\oplus Q_n$ 在 $n\ge3$ 时四维。$H_n$ 到同轮 $G_n,Q_n$ 的正交投影均为同构。

**引理54.5（排除外部交替尾环境）。** 不可能存在单位环境向量 $O\notin F$、$B\in F$，使
$$
\eta_3=\eta_5=O,\qquad\eta_4=\eta_6=B.
\tag{54.39}
$$
这里同射线的整体相位已统一选取；未假设 $O$ 和 $F$ 的任何正交关系。

**证明。** 令
$$
R=G_3+G_5,\qquad
L=U+G_4+G_6,\qquad r=\dim R,\quad d=\dim L-2.
$$
全部零位像包含
$$
R\otimes O
\quad\text{和}\quad
(U\otimes F)+(G_4+G_6)\otimes B.
$$
前后两项交为零，因为 $O\notin F$。后一项的维数是 $4+d$：对 $U$ 取接收商，其核恰为 $U\otimes F$，像为 $\pi_U(G_4+G_6)\otimes B$。七维性给
$$
r+d\le3,\qquad r\ge2,\quad d\ge0.
\tag{54.40}
$$

若 $r=3$，则 $d=0$，从而 $G_4=G_6=U$。固定 $V_0$ 及（54.39）给 $H_3=H_5$；固定 $V_1$ 在 $G_2=G_4=U$ 上给 $Q_3=Q_5=:Q$。共同外部环境上的不同输入位正交给
$$
R\perp Q.
$$
因此 $P_RH_3=G_3$、$P_RH_5=G_5$。$H_3=H_5$ 便迫使 $G_3=G_5$，使 $r=2$，矛盾。

所以 $r=2$，即 $G_3=G_5$。固定 $V_0$ 及共同环境 $O$ 立刻给
$$
H_2=H_4.
\tag{54.41}
$$
由于 $B\in F$，早期零位块 $U\otimes F$ 与第四轮一位像 $Q_4\otimes B$ 的正交性给 $Q_4\perp U$。同时同轮零、一位像给 $Q_4\perp G_4$。因此
$$
U+G_4\subseteq Q_4^\perp.
\tag{54.42}
$$
但 $0\ne w\in H_2\cap U=H_4\cap U$，所以（54.42）使 $P_{Q_4}w=0$。这与 $P_{Q_4}|_{H_4}$ 单射矛盾。证明完毕。

### 54.6 主结论与保留范围

将引理54.2用于54.1节的 $A=U=G_2$、二维 $F$ 与四轮纯尾，抽象指标 $1,2,3,4$ 对应实际轮次 $3,4,5,6$。它只允许全部尾环境在 $F$ 内、共同外部射线 $OOOO$，或一条外部射线与一条内部射线严格交替 $OBOB$。引理54.4和54.5排除后两项，所以
$$
\eta_3,\eta_4,\eta_5,\eta_6\in F.
$$
若它们只张成一维，选择共同单位代表 $\eta\in F$；引理54.3却给 $\eta\perp F$，与单位范数矛盾。因此四份尾环境张成整个二维 $F$，定理54.1得证。

本节没有排除这个二维环境内的全部非共线序列。第一终端的混合附加因子始终计入接收器，前两轮环境仍可彼此纠缠。第二终端秩二的分支仍由第53节约束，早期全部纯的非周期环境也未在此结算。一般六终端固定 CPTP 接收容量仍为
$$
7\le d_{\mathrm{CPTP},6}\le8.
$$

## 追加锚（本行以下为增补区）

## 55. 七维秩二第一终端的两射线尾模式

### 55.1 实际合同、共同接口与主结论

固定非退化来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，$ab\ne0$、$|a|^2+|b|^2=1$。七维接收器独立纯启动，同一全域 CPTP 接收通道服务前六个完整参考终端，第一终端可逆附加态秩二、第二终端纯。

沿第54节记号，$V_0,V_1:K\to K\otimes E$ 是同一 Stinespring 等距的两个正交位像，早期空间为
$$
U=G_2=\operatorname{span}(u,w),\qquad
H_2=\operatorname{span}(a^2u+bv,w),\qquad
u,v,w\text{ 正交单位}.
\tag{55.1}
$$
存在二维 $P_0=\operatorname{span}(p_1,p_2)$、四维 $X=\operatorname{span}(p_1,q_1,p_2,q_2)$ 及二维环境 $F=\operatorname{span}(f_1,f_2)$，满足
$$
V_0X=U\otimes F,\qquad V_1P_0=\mathbb Cv\otimes F.
\tag{55.2}
$$
对单位 $\xi=\xi_1f_1+\xi_2f_2\in F$，置
$$
p_\xi=\xi_1p_1+\xi_2p_2,\qquad
q_\xi=\xi_1q_1+\xi_2q_2,\qquad
X_\xi=\operatorname{span}(p_\xi,q_\xi).
$$
则 $p_\xi,q_\xi$ 正交单位，且
$$
V_0p_\xi=u\otimes\xi,\quad
V_0q_\xi=w\otimes\xi,\quad
V_1p_\xi=v\otimes\xi,\quad V_0X_\xi=U\otimes\xi.
\tag{55.3}
$$
其中 $p_1,q_1,p_2,q_2$ 以及 $f_1,f_2$ 分别正交归一。两条不同射线 $\xi,\zeta\in F$ 满足 $X_\xi+X_\zeta=X$。

第一轮的实际零位像还有 Schmidt 分解
$$
V_0k=\sqrt{\lambda_1}p_1\otimes e_1+
\sqrt{\lambda_2}p_2\otimes e_2,\qquad
\lambda_1,\lambda_2>0,
\tag{55.4}
$$
其中 $e_1,e_2$ 正交单位。这份实际第一轮资料会在一个饱和分支中使用。

对纯尾 $n=3,4,5,6$，各 $H_n,G_n,Q_n$ 二维，满足
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n,
\tag{55.5}
$$
并记 $C_n=H_n+G_n$；$C_2$ 三维，$C_n$ 在 $n=3,4,5,6$ 时四维。且 $G_n\perp Q_n$，$H_n\subset G_n\oplus Q_n$ 到两个同轮因子的投影均为同构。全部尾环境在 $F$ 内时，旧块和位像正交给
$$
v\perp U+G_3+G_4+G_5+G_6,
\qquad Q_n\perp U.
\tag{55.6}
$$

第54节已经给出 $\operatorname{span}(\eta_3,\eta_4,\eta_5,\eta_6)=F$，以下保留这个实际来源合同，不将 $F$ 内的不同射线预设为正交。

**定理55.1（两射线尾模式的必要限制）。** 四个纯尾环境的射线模式只能为
$$
\boxed{AABA,\qquad ABAA,\qquad ABAB.}
$$
其中 $A,B$ 是二维 $F$ 中的两条不同射线。该结论不宣称这三个剩余模式均可实现，也未排除其中任一模式的全部非正交参数。

### 55.2 四轮尾射线模式的穷尽

**引理55.2（四轮尾射线的六种候选模式）。** 用相同字母表示同一环境射线、不同字母表示不同射线，则四轮尾 $(\eta_3,\eta_4,\eta_5,\eta_6)$ 必为下列六种模式之一：
$$
AAAA,\quad AAAB,\quad AABA,\quad ABAA,\quad ABAB,\quad ABAC.
\tag{55.7}
$$
最后一种中的 $A,B,C$ 三条射线互异。列表只声明必要模式，不声称逐个可实现；不同字母没有正交含义。

**证明。** 令 $\pi_U:K\to K/U$，置
$$
Z=(\pi_U\otimes I_E)V_0K.
$$
$U\otimes F$ 是四维核子空间，而 $V_0K$ 七维，所以 $\dim Z\le3$。

令 $A=\mathbb C\eta_3$。若 $n\in\{3,4,5\}$ 满足 $\eta_{n+1}\notin A$，固定 $V_1$ 在 $U$ 与 $G_n$ 上的环境射线不同，故 $U\cap G_n=0$。因此
$$
\dim\pi_U(G_n)=2,\qquad
\pi_U(G_n)\otimes\eta_n\subseteq Z.
\tag{55.8}
$$
若两个这样的指标 $n,m$ 还满足 $\eta_n\not\parallel\eta_m$，两个二维张量子空间的交为零，其和四维，违反 $\dim Z\le3$。所以
$$
\eta_{n+1},\eta_{m+1}\notin A
\quad\Longrightarrow\quad
\eta_n\parallel\eta_m
\qquad(n,m\in\{3,4,5\}).
\tag{55.9}
$$

现在逐项处理射线位置。

- 若 $\eta_4\notin A$，取其射线为 $B$。若 $\eta_5\notin A$，则（55.9）对 $n=3,m=4$ 会给 $\eta_3\parallel\eta_4$，矛盾。因此 $\eta_5\in A$。最后的 $\eta_6$ 或属于 $A$、或属于 $B$、或属于第三条射线 $C$，分别得到 $ABAA,ABAB,ABAC$。
- 若 $\eta_4\in A$ 而 $\eta_5\notin A$，取后者射线为 $B$。若 $\eta_6\notin A$，则（55.9）对 $n=4,m=5$ 会给 $\eta_4\parallel\eta_5$，矛盾。因此 $\eta_6\in A$，得到 $AABA$。
- 若 $\eta_4,\eta_5\in A$，则 $\eta_6\in A$ 给 $AAAA$，其余情况给 $AAAB$。

三类情形互斥并穷尽全部环境位置，得到（55.7）。证明完毕。

### 55.3 延迟到最后一轮才换射线的排除

**引理55.3（排除 AAAB）。** 不可能存在单位向量 $A\in F$、$B\not\parallel A$，使
$$
\eta_3=\eta_4=\eta_5=A,\qquad\eta_6=B.
$$
这一排除只使用 $A\in F$ 及 $B\not\parallel A$，不使用 $A\perp B$。

**证明。** 令 $L=U+G_3+G_4$。若 $\dim L=2$，则 $U=G_3=G_4$。因第三、第四轮环境相同，$V_0H_2=G_3\otimes A=G_4\otimes A=V_0H_3$；单射性给 $H_2=H_3$，于是 $C_2=C_3$，违反三维与四维的秩差。因此 $\dim L\ge3$。

固定 $V_1$ 将 $L$ 送入 $K\otimes A$，将 $G_5$ 送入 $K\otimes B$。两环境射线不同，所以 $G_5\cap L=0$。因此
$$
R:=U+G_3+G_4+G_5=L+G_5,
\qquad \dim R=\dim L+2\ge5.
$$

因 $A\in F$，旧块包含 $U\otimes A$；第三至第五轮零位像又包含 $G_3\otimes A,G_4\otimes A,G_5\otimes A$，所以 $R\otimes A\subset V_0K$。同时 $V_1L=Q\otimes A$，其中 $\dim Q=\dim L\ge3$。两个位像正交且环境相同，故 $R\perp Q$。于是
$$
7=\dim K\ge\dim R+\dim Q=2\dim L+2\ge8,
$$
矛盾。证明完毕。

### 55.4 三条互异射线的 ABAC 排除

**引理55.4（排除三条互异射线的 ABAC）。** 不可能存在 $F$ 中三条互异环境射线的单位代表 $A,B,C$，使
$$
\eta_3=\eta_5=A,\qquad \eta_4=B,\qquad\eta_6=C.
\tag{55.10}
$$
三条射线互异不表示两两正交；证明分别保留所有非零与零交叠。

**证明。** 对 $U$ 取商 $\pi:K\to K/U$。由（55.2），
$$
Z=(\pi\otimes I_E)V_0K,\qquad\dim Z\le3.
\tag{55.11}
$$
$V_1$ 在 $U,G_3,G_5$ 上分别使用 $A,B,C$，所以 $U\cap G_3=U\cap G_5=0$。因此
$$
M=\pi(G_3+G_5),\qquad m=\dim M\in\{2,3\},
\quad M\otimes A\subset Z.
\tag{55.12}
$$

**商像三维。**

若 $m=3$，则 $Z=M\otimes A$。由 $B,C$ 均不平行 $A$，$\pi(G_4)\otimes B$、$\pi(G_6)\otimes C$ 只能为零，故
$$
G_4=G_6=U.
\tag{55.13}
$$
令 $S=U+G_3+G_5$，它五维，且 $S\otimes A\subset V_0K$。因 $V_1U=Q_3\otimes A$，有 $S\perp Q_3$，于是
$$
K=S\oplus Q_3,\qquad v\in Q_3.
\tag{55.14}
$$
$B,C$ 张成 $F$，所以它们不能同时正交于非零 $A\in F$。若 $\langle A,B\rangle\ne0$，跨位正交给 $Q_4\perp S$，因而 $Q_4=Q_3$；故
$$
V_1(U+G_3)=Q_3\otimes F.
$$
由 $V_1P_0=v\otimes F$ 及 $v\in Q_3$，单射性给 $P_0\subset U+G_3\subset S$。若改为 $\langle A,C\rangle\ne0$，则以 $Q_6=Q_3$ 和 $U+G_5$ 得到同样的 $P_0\subset S$。

但（55.13）使 $V_0H_3=U\otimes B=V_0X_B$，故 $H_3=X_B$，非零 $p_B\in P_0\cap H_3$。另一方面，$H_3\subset G_3\oplus Q_3$ 到 $Q_3$ 的投影单射，而 $G_3\subset S\perp Q_3$，所以 $H_3\cap S=0$。与 $P_0\subset S$ 矛盾。

**商像二维与共同的一位张量块。**

以下 $m=2$。令
$$
S=U+G_3+G_5,\qquad\dim S=4.
$$
由于 $U\cap G_3=U\cap G_5=0$，有
$$
S=U+G_3=U+G_5.
\tag{55.15}
$$
固定 $V_1$ 给
$$
V_1S=(Q_3\otimes A)+(Q_4\otimes B).
$$
将 $C$ 写成 $C=\alpha A+\beta B$，三射线互异使 $\alpha\beta\ne0$。由 $G_5\subset S$ 及 $V_1G_5=Q_6\otimes C$，逐个 $A,B$ 分量比较给 $Q_6\subset Q_3\cap Q_4$。三者均二维，因此
$$
Q_3=Q_4=Q_6=:Q,\qquad
V_1S=Q\otimes F.
\tag{55.16}
$$
跨位正交于是使
$$
U,G_3,G_4,G_5,G_6\subset Q^\perp.
\tag{55.17}
$$
特别地 $S\perp Q$。

此外，$V_1G_4=Q_5\otimes A$，其与 $V_1S=Q\otimes F$ 的交落在 $Q\otimes A=V_1U$。固定等距单射性给
$$
G_4\cap S=G_4\cap U.
\tag{55.18}
$$

**二维商像中的 $G_4\ne U$ 分支。**

由（55.11）、（55.12）及 $B\not\parallel A$，$\dim\pi G_4\le1$。当前不等于 $U$，故 $N=\pi G_4$ 恰一维。式（55.18）使 $N\cap M=0$：否则 $G_4$ 中一个不在 $U$ 的向量会属于 $S$。因此
$$
Z=(M\otimes A)\oplus(N\otimes B).
$$
对 $\pi(G_6)\otimes C\subset Z$ 比较两个非零环境分量，得 $\pi G_6\subset M\cap N=0$，所以
$$
G_6=U.
\tag{55.19}
$$
式（55.18）还给 $\dim(S+G_4)=5$；结合（55.17）和 $\dim Q=2$，
$$
K=(S+G_4)\oplus Q.
$$
由（55.6）得 $v\in Q$。于是（55.3）、（55.16）给
$$
V_1p_C=v\otimes C\in Q\otimes C=V_1G_5,
\quad\text{故 }p_C\in G_5.
$$
而（55.19）使 $H_5=X_C$，所以 $p_C\in H_5\cap G_5=0$，与 $p_C$ 单位矛盾。

**二维商像中的 $G_4=U$ 分支。**

现在 $H_3=X_B$。只需证明 $v\in Q$：一旦成立，（55.3）、（55.16）给 $p_B\in G_3$，而 $p_B\in H_3$，违反 $H_3\cap G_3=0$。

若 $G_6\not\subset S$，由（55.11）、（55.12）及 $C\not\parallel A$，$\dim\pi G_6\le1$。故 $\dim(S+G_6)=5$。式（55.17）及（55.6）立即给 $K=(S+G_6)\oplus Q$、$v\in Q$。

若 $G_6\subset S$ 而 $G_6\ne U$，则 $\dim\pi G_6=1$。已知零位像
$$
(U\otimes F)+(S\otimes A)+(G_6\otimes C)
\tag{55.20}
$$
恰七维：商掉四维 $U\otimes F$ 后，前两个零位块留下二维 $M\otimes A$，最后一个留下不同环境线上的一维 $\pi(G_6)\otimes C$。因此（55.20）饱和 $V_0K$，并全部包含于 $S\otimes F$。式（55.4）两个严格正 Schmidt 权重迫使 $p_1,p_2\in S$，即 $P_0\subset S$。结合（55.2）、（55.16）得到 $v\in Q$。

最后，若 $G_6=U$，则
$$
H_3=X_B,\qquad H_5=X_C,\qquad X=H_3+H_5.
\tag{55.21}
$$
因为 $G_4=U$，固定 $V_1$ 又给 $Q_5=Q_3=Q$。于是 $H_3,H_4,H_5\subset S\oplus Q$，从而 $X\subset S\oplus Q$。$V_0X=U\otimes F$ 与 $V_0H_4=G_5\otimes A$ 交零，因为 $G_5\cap U=0$。所以
$$
X+H_4=S\oplus Q,\qquad \dim(X+H_4)=6.
\tag{55.22}
$$
由（55.15），$G_3\subset U+G_5$，故
$$
V_0H_2=G_3\otimes A
\subset (U\otimes F)+(G_5\otimes A)=V_0(X+H_4).
$$
单射性给 $H_2\subset X+H_4=S\oplus Q$。式（55.1）及 $u\in S$、$b\ne0$ 因而给 $v\in S\oplus Q$；而（55.6）使 $v\perp S$，所以仍有 $v\in Q$。

最后一个分支的全部子情形都得到所需矛盾。$m=2$、$m=3$ 两个分支均已排除，定理得证。

### 55.5 主结论与剩余范围

引理55.2穷尽六种候选模式。第54节的张满二维结论排除 $AAAA$；引理55.3排除 $AAAB$；引理55.4排除三条互异射线的 $ABAC$。因此恰只留下 $AABA,ABAA,ABAB$ 三种必要模式，定理55.1得证。

本节没有把三个必要模式判为可实现，也没有排除两条不同射线的全部正交或非正交参数。第二终端秩二及早期全部纯的分支仍按各自合同保留；一般六终端固定 CPTP 接收容量仍为
$$
7\le d_{\mathrm{CPTP},6}\le8.
$$

## 追加锚（本行以下为增补区）

## 56. 七维秩二第一终端只余两种非正交尾模式

### 56.1 实际合同与主结论

固定第54、55节的实际合同：非退化来源 $ab\ne0$，七维接收器独立纯启动，同一个全域 CPTP 接收通道服务前六个完整参考终端，$r_1=2,r_2=1$。沿用二维 $U=G_2=\operatorname{span}(u,w)$、二维环境 $F$、四维早期输入 $X$，以及
$$
H_2=\operatorname{span}(a^2u+bv,w),\qquad
V_0X=U\otimes F,\qquad V_1P_0=\mathbb Cv\otimes F.
\tag{56.1}
$$
$u,v,w$ 正交单位。对单位 $\xi\in F$，有单位 $p_\xi\in X_\xi$，满足
$$
V_0X_\xi=U\otimes\xi,\qquad V_1p_\xi=v\otimes\xi.
\tag{56.2}
$$
各纯尾系数空间满足
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n\quad(3\le n\le6),
\tag{56.3}
$$
各 $H_n,G_n,Q_n$ 二维，$H_n\subset G_n\oplus Q_n$ 到 $G_n,Q_n$ 的正交投影均为同构。第54节给全部尾环境在 $F$ 内，故旧块与不同输入位正交使
$$
v\perp U+G_3+G_4+G_5+G_6,\qquad Q_n\perp U.
\tag{56.4}
$$
同一个 $V$ 的两位像正交；同环境方向中的两份接收像因而正交。

**定理56.1（两种非正交尾模式的必要限制）。** 在上述七维六终端合同中，若 $r_1=2,r_2=1$，则第3至第6轮的纯环境射线只能为
$$
\boxed{ABAA\quad\text{或}\quad ABAB,\qquad 0<|\langle A,B\rangle|<1.}
$$
其中 $A,B$ 是二维排出环境 $F$ 内的单位代表。两个模式仍只是必要形态，本定理不提供可行接收器，也没有排除全部非正交参数。

### 56.2 三种尾模式的正交参数排除

**引理56.2（三种尾模式的正交参数排除）。** 若四轮尾环境的模式是第55节留下的 $AABA$、$ABAA$ 或 $ABAB$，则两条不同射线不能正交。对单位代表必有
$$
\boxed{0<|\langle A,B\rangle|<1.}
\tag{56.5}
$$

**证明。** 上界严格小于一只用两条射线不同。以下反设 $A\perp B$，逐项排除三个模式。

**AABA。**

现在 $\eta_3=\eta_4=\eta_6=A$、$\eta_5=B$。令 $L=U+G_3$、$l=\dim L$。固定 $V_1$ 将 $L$ 送入环境 $A$，将 $G_4$ 送入环境 $B$，所以 $L\cap G_4=0$。零位像在环境 $A$ 中包含
$$
R\otimes A,\qquad R=U+G_3+G_4+G_6,\qquad\dim R\ge l+2.
$$
其中 $U\otimes A$ 来自早期块。一位像在同一环境中包含 $V_1L=Q\otimes A$，$\dim Q=l$。不同输入位正交给
$$
7\ge\dim R+\dim Q\ge2l+2.
$$
$l\ge2$，故只能 $l=2$，即
$$
G_3=U.
\tag{56.6}
$$
又因 $A\perp B$，固定 $V_1$ 给 $U\perp G_4$。第三、第四轮的零位像分别为 $U\otimes A$ 与 $G_4\otimes A$，所以 $H_2\perp H_3$。但 $0\ne w\in H_2\cap U$，而（56.6）及同轮满投影给 $P_UH_3=U$，因此 $w$ 不可能正交于整个 $H_3$。矛盾。

**ABAA。**

现在 $\eta_3=\eta_5=\eta_6=A$、$\eta_4=B$。令
$$
L=U+G_4+G_5,\quad l=\dim L,\qquad
R=U+G_3+G_5+G_6,\quad r=\dim R,\qquad
T=U+G_5,\quad t=\dim T.
$$
$V_1L$ 使用 $A$，$V_1G_3$ 使用 $B$，不同射线给 $G_3\cap L=0$。于是 $r\ge t+2$、$l\ge t$。同一环境 $A$ 上，零位像包含 $R\otimes A$，一位像 $V_1L$ 的接收因子维数为 $l$，故
$$
7\ge r+l\ge2t+2.
$$
$t\ge2$，所以 $t=2$，即
$$
G_5=U,\qquad L=U+G_4,\qquad l\in\{2,3\}.
\tag{56.7}
$$
这里 $l\le3$ 因为 $r\ge4$。

若 $l=3$，则 $r=4$。写 $V_1L=Q_A\otimes A$；同一环境的正交性使 $K=R\oplus Q_A$，$\dim Q_A=3$。式（56.4）给 $v\in Q_A$，所以（56.2）及单射性给 $p_A\in L$。同时（56.7）和（56.3）给 $H_4=X_A$，故 $p_A\in H_4$。

但是 $B$ 环境中的零位像包含 $(U+G_4)\otimes B=L\otimes B$，一位像包含 $Q_4\otimes B$，所以 $Q_4\perp L$。$H_4\subset G_4\oplus Q_4$、$G_4\subset L$，且到 $Q_4$ 的投影单射，因而 $H_4\cap L=0$。这与非零 $p_A\in H_4\cap L$ 矛盾。因此 $l=2$，即
$$
G_4=G_5=U.
\tag{56.8}
$$
这一步的结构归约只使用 $A,B$ 不同，尚未使用二者正交。

由 $A\perp B$，固定 $V_1$ 给 $U\perp G_3$。而 $V_0H_2=G_3\otimes A$、$V_0H_4=U\otimes A$，故 $H_2\perp H_4$。式（56.8）使 $P_UH_4=U$，再次与 $0\ne w\in H_2\cap U$ 矛盾。

**ABAB。**

现在 $\eta_3=\eta_5=A$、$\eta_4=\eta_6=B$。令 $\pi:K\to K/U$，由四维旧块得到
$$
Z=(\pi\otimes I_E)V_0K,\qquad\dim Z\le3.
$$
$V_1$ 在 $U,G_3,G_5$ 上分别使用 $A,B,B$，故 $U\cap G_3=U\cap G_5=0$。因此
$$
M=\pi(G_3+G_5),\qquad m=\dim M\in\{2,3\},\qquad M\otimes A\subset Z.
\tag{56.9}
$$
若 $m=3$，则 $Z=M\otimes A$；不同环境 $B$ 的零位商像必须为零，故 $G_4=G_6=U$。固定 $V_0$ 给 $H_3=H_5$，固定 $V_1$ 又给 $Q_3=Q_5=:Q$。共同环境 $A$ 的位像正交使 $G_3+G_5\perp Q$。于是同一空间 $H_3=H_5$ 到 $G_3+G_5$ 的投影像既为 $G_3$、又为 $G_5$，故 $G_3=G_5$，与 $m=3$ 矛盾。

所以 $m=2$。正交环境 $A\perp B$ 使 $U\perp G_3+G_5$，$\pi$ 在 $G_3+G_5$ 上单射；因此 $\dim(G_3+G_5)=2$，即 $G_3=G_5$。固定零位像在共同环境 $A$ 中相同，便有
$$
H_2=H_4.
\tag{56.10}
$$
但 $0\ne w\in H_2\cap U=H_4\cap U$，而式（56.4）给 $Q_4\perp U$，所以 $P_{Q_4}w=0$。这违反 $P_{Q_4}|_{H_4}$ 的单射性。矛盾。

三个模式的正交参数均被排除，得到（56.5）。证明完毕。

### 56.3 非正交 AABA 的排除

采用第55节的七维、$r_1=2,r_2=1$、前六个完整参考终端的实际合同。来源 $ab\ne0$，记 $U=G_2$、$H_2=\operatorname{span}(a^2u+bv,w)$，$u,v,w$ 正交单位。第二轮排出空间 $F$ 二维，且
$$
U\otimes F\subset V_0K,\qquad
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n.
\tag{56.11}
$$
$H_n\subset G_n\oplus Q_n$ 到两个同轮二维因子的投影均为同构，$V_0K\perp V_1K$。全部尾环境属于 $F$，所以 $Q_n\perp U$。

**引理56.3（非正交 AABA 的排除）。** 不可能有
$$
\eta_3=\eta_4=\eta_6=A,\qquad\eta_5=B,\qquad
0<r:=|\langle A,B\rangle|<1,\qquad A,B\in F.
\tag{56.12}
$$

**证明。** 先复核不需要环境正交的归约 $G_3=U$。令 $L=U+G_3$、$l=\dim L$。固定 $V_1$ 将 $L$ 送入环境 $A$，将 $G_4$ 送入环境 $B$，所以 $G_4\cap L=0$。环境 $A$ 中的零位接收像包含 $U+G_3+G_4$，维数至少 $l+2$；一位接收像 $V_1L$ 的因子维数为 $l$。两者正交，因此 $7\ge2l+2$。$l\ge2$ 使 $l=2$，故 $G_3=U$。

再令
$$
L_A=U+G_5,\quad l=\dim L_A,\qquad
R_A=U+G_4+G_6,\quad s=\dim R_A.
$$
$V_1L_A$ 使用环境 $A$，$V_1G_4$ 使用环境 $B$，所以 $G_4\cap L_A=0$。因 $U\cap G_4=0$，有 $s\ge4$；环境 $A$ 的零、一位像正交给 $s+l\le7$，因此 $l\in\{2,3\}$。

若 $l=3$，则 $s=4$，所以 $R_A=U+G_4$。$R_A\cap L_A=U$，故
$$
\dim(R_A+L_A)=4+3-2=5.
$$
写 $V_1L_A=W_A\otimes A$，$\dim W_A=3$。同一环境给 $R_A\perp W_A$。另一零位像包含 $L_A\otimes B$：其中 $U\otimes B$ 来自旧块，$G_5\otimes B$ 来自第五轮。因为 $\langle A,B\rangle\ne0$，跨位正交还给 $L_A\perp W_A$。因此 $R_A+L_A$ 的五维空间正交于三维 $W_A$，七维中不可能。故 $l=2$，得到
$$
G_3=G_5=U.
\tag{56.13}
$$

式（56.13）使
$$
V_0H_2=U\otimes A,\qquad V_0H_4=U\otimes B.
$$
这两份完整二维像的两个主角余弦都等于 $r$；等距保持主角。因此任意单位 $h\in H_2$ 满足 $\|P_{H_4}h\|=r$。特别取同一个实际单位向量 $w\in H_2\cap U$，得
$$
\|P_{H_4}w\|=r.
\tag{56.14}
$$
另一方面，写 $V_1w=q\otimes A$，其中 $q\in Q_3$ 单位。由 $V_1G_4=Q_5\otimes B$，等距投影公式给
$$
\|P_{G_4}w\|
=\|P_{Q_5\otimes B}(q\otimes A)\|
=r\|P_{Q_5}q\|\le r.
\tag{56.15}
$$

但 $H_4$ 是一个可逆线性映射 $T:G_4\to Q_4$ 的图，而 $w\in U\perp Q_4$。记 $w_G=P_{G_4}w$。图投影公式给
$$
\|P_{H_4}w\|^2
=\langle w_G,(I+T^*T)^{-1}w_G\rangle
<\|w_G\|^2=\|P_{G_4}w\|^2
\tag{56.16}
$$
只要 $w_G\ne0$。这里（56.14）及 $r>0$ 确保 $w_G\ne0$；$T$ 可逆确保严格性。联立（56.14）—（56.16）得到 $r<r$，矛盾。证明完毕。

### 56.4 ABAA 环境交叠的定量下界

采用第55节七维、$r_1=2,r_2=1$、前六个完整参考终端的实际合同，来源 $ab\ne0$。尾环境为
$$
\eta_3=\eta_5=\eta_6=A,\qquad\eta_4=B,\qquad A\not\parallel B.
$$
$A,B$ 是二维排出环境 $F$ 中的单位向量。ABAA 的无正交结构归约给
$$
G_4=G_5=U=G_2,\qquad
H_2=\operatorname{span}(a^2u+bv,w),\qquad\|w\|=1,\quad w\in U,
\tag{56.17}
$$
其中 $u,v,w$ 正交单位。这里引用该归约时不假设 $A\perp B$。

置
$$
x=|a|^2,\qquad y=|b|^2,\qquad
t_0=1,\quad t_j=1-y t_{j-1}.
$$

**命题56.4（ABAA 环境交叠的来源相关下界）。** 环境交叠必须满足
$$
\boxed{
|\langle A,B\rangle|^2\ge x\frac{t_3}{t_4}.
}
\tag{56.18}
$$
这比仅要求非正交更强；当 $x=y=1/2$ 时，右端为 $5/11$。

**证明。** 对同一个实际单位向量 $w$ 比较三份投影读数。由（56.17）及固定零位等距，
$$
V_0H_2=G_3\otimes A,\qquad
V_0H_4=U\otimes A.
$$
因此可写 $V_0w=t\otimes A$，其中 $t\in G_3$ 单位，并有准确等式
$$
\|P_{H_4}w\|=\|P_Ut\|.
\tag{56.19}
$$
固定一位等距满足 $V_1G_3=Q_4\otimes B$、$V_1U=Q_3\otimes A$。写 $V_1t=q\otimes B$，其中 $q\in Q_4$ 单位，得到
$$
\|P_Ut\|
=|\langle A,B\rangle|\,\|P_{Q_3}q\|
\le|\langle A,B\rangle|.
\tag{56.20}
$$

另一方面，$w\in U=G_4$，实际来源的第四终端主角给反向下界。第53节式（53.14）中 $H_4,G_4$ 的两个主角余弦平方为
$$
\lambda_4=x\frac{t_3}{t_4},\qquad
\lambda_3=x\frac{t_2}{t_3}.
$$
同节的递推计算给 $\lambda_3>x>\lambda_4>0$。所以每个 $G_4$ 中的单位向量都满足
$$
\|P_{H_4}w\|\ge\sqrt{\lambda_4}.
\tag{56.21}
$$
联立（56.19）—（56.21）并平方，得到（56.18）。证明完毕。

该下界还满足
$$
\sqrt{x\frac{t_3}{t_4}}
>\frac{x}{\sqrt{x^2+y}},
$$
严格间隙由第53节式（53.15）给出。这里的环境交叠始终是同一实际 ABAA 候选的两个单位环境向量的交叠；没有将不同装置的可达最优值组合。

本命题只排除小于来源相关阈值的环境交叠。大交叠参数仍未由此结算，非正交 ABAB 也不在此界的范围内。

### 56.5 主结论与保留范围

第55节已把 $r_1=2,r_2=1$ 分支的四轮尾限制到 $AABA,ABAA,ABAB$。引理56.2排除这三个模式的所有正交参数；引理56.3再排除非正交 $AABA$。两条环境射线不同，单位代表的交叠模严格小于一，因此只余定理56.1所列的两种非正交模式。

$ABAA$ 的证明还给出不要求环境正交的结构约束 $G_4=G_5=U$；$ABAB$ 则必须满足零位商空间中的 $\dim\pi_U(G_3+G_5)=2$。这些都是同一实际候选的必要关系，不能替代其余共同 Gram 等式、初态实现或终端恢复义务。

本节没有排除 $ABAA,ABAB$ 的全部非正交参数，也没有处理第二终端秩二和早期全部纯的其余分支。一般六终端固定 CPTP 接收容量仍为
$$
7\le d_{\mathrm{CPTP},6}\le8.
$$

## 追加锚（本行以下为增补区）

## 57. 七维纯第二终端强制纯第一终端

### 57.1 实际来源、早期编码与主结论

固定非退化来源 $m_0=a|0\rangle+b|1\rangle$、$m_1=|0\rangle$，$ab\ne0$、$|a|^2+|b|^2=1$。七维接收器 $K$ 从独立单位初态 $k$ 启动，每轮使用同一个全域 CPTP 通道，前六个终端要求完整参考—活动记忆—原档案的精确恢复。本节研究第二终端可逆附加态纯的合同。为排除第一终端附加态秩二的分支，以下编码资料先在 $r_1=2,r_2=1$ 的反设下引入。

固定一次 Stinespring 等距的两个位块 $V_0,V_1:K\to K\otimes E$，两像正交。早期标准编码给四个正交单位接收向量 $p_1,q_1,p_2,q_2$、两个正交单位环境 $f_1,f_2$ 及正交单位 $u,v,w$，满足
$$
V_0p_i=u\otimes f_i,\quad V_0q_i=w\otimes f_i,\quad
V_1p_i=v\otimes f_i\qquad(i=1,2).
\tag{57.1}
$$
置
$$
U=\operatorname{span}(u,w)=G_2,\quad
P_0=\operatorname{span}(p_1,p_2),\quad
X=\operatorname{span}(p_1,q_1,p_2,q_2),\quad
F=\operatorname{span}(f_1,f_2).
$$
第二终端的零记忆系数空间为
$$
H_2=\operatorname{span}(a^2u+bv,w).
\tag{57.2}
$$
第一轮真实输出仍有两个严格正的 Schmidt 权重：存在正交单位 $e_1,e_2$ 和 $\lambda_1,\lambda_2>0$，使
$$
V_0k=\sum_{i=1}^2\sqrt{\lambda_i}\,p_i\otimes e_i,
\qquad
V_1k=\sum_{i=1}^2\sqrt{\lambda_i}\,q_i\otimes e_i.
\tag{57.3}
$$
两个环境组 $e_i$、$f_i$ 未预设相互正交或相同。

对 $\xi=\xi_1f_1+\xi_2f_2\in F$，定义 $p_\xi=\xi_1p_1+\xi_2p_2$、$q_\xi=\xi_1q_1+\xi_2q_2$ 及 $X_\xi=\operatorname{span}(p_\xi,q_\xi)$。单位 $\xi$ 对应单位 $p_\xi$，且
$$
V_0X_\xi=U\otimes\xi,\qquad V_1p_\xi=v\otimes\xi.
\tag{57.4}
$$
对纯尾 $3\le n\le6$，有二维 $H_n,G_n,Q_n$，满足
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n,\qquad G_n\perp Q_n.
\tag{57.5}
$$
实际 $H_n\subset G_n\oplus Q_n$ 到两个同轮因子的投影均为同构；特别 $H_n\cap G_n=0$。第54节给尾环境均在 $F$ 中，故（57.1）及位像正交使
$$
v\perp U+G_3+G_4+G_5+G_6,\qquad Q_n\perp U.
\tag{57.6}
$$

**定理57.1（纯第二终端强制纯第一终端）。** 对上述非退化来源、独立纯启动及全部持久资源计费的合同，七维固定 CPTP 接收器若精确服务前六个完整参考终端，且第二终端的可逆附加态纯，则第一终端的可逆附加态也纯：
$$
\boxed{r_2=1\Longrightarrow r_1=1.}
$$
证明将先排除 $r_1=2,r_2=1$ 的剩余两个尾模式，再结合第53节对 $r_1=3,r_2=1$ 的排除。该结论没有排除 $r_2=2$ 的分支，也没有结算早期全部纯的七维候选。

### 57.2 非正交 ABAA 的排除

**引理57.2（非正交 ABAA 的排除）。** 不可能有
$$
\eta_3=\eta_5=\eta_6=A,\qquad\eta_4=B,\qquad
0<|\langle A,B\rangle|<1,\qquad A,B\in F.
\tag{57.7}
$$

**证明。** 先使用 ABAA 的无正交结构归约
$$
G_4=G_5=U.
\tag{57.8}
$$
为使来源依赖完整，简要复核：令 $L=U+G_4+G_5$、$R=U+G_3+G_5+G_6$、$T=U+G_5$。固定 $V_1$ 在 $L$ 上使用 $A$、在 $G_3$ 上使用 $B$，故 $G_3\cap L=0$。环境 $A$ 的零、一位正交像给
$$
7\ge\dim R+\dim L\ge2\dim T+2,
$$
所以 $T=U$、$G_5=U$。此时 $\dim L\in\{2,3\}$。若 $\dim L=3$，则 $\dim R=4$，环境 $A$ 的两个位像饱和为接收正交分解 $K=R\oplus Q_A$，$V_1L=Q_A\otimes A$。式（57.6）给 $v\in Q_A$，故（57.4）和单射性使 $p_A\in L$。另一方面 $G_5=U$ 使 $H_4=X_A$，故 $p_A\in H_4$。环境 $B$ 的零位像包含 $L\otimes B$，一位像包含 $Q_4\otimes B$，所以 $Q_4\perp L$。$H_4\subset G_4\oplus Q_4$ 到 $Q_4$ 的投影单射，且 $G_4\subset L$，因而 $H_4\cap L=0$，矛盾。故 $L=U$，得到（57.8）。该归约未使用 $A,B$ 正交。

由（57.8）及固定零位映射，
$$
H_3=X_B,\qquad H_4=X_A,\qquad X=H_3+H_4.
\tag{57.9}
$$
最后一个等式使用 $A,B$ 张成二维 $F$。固定一位映射还给
$$
Q_3=Q_5=Q_6.
\tag{57.10}
$$

令
$$
S=U+G_3,\qquad W=Q_3+Q_4.
\tag{57.11}
$$
$V_1U$ 与 $V_1G_3$ 分属不同射线，所以 $U\cap G_3=0$、$\dim S=4$。所有尾环境都在两条非正交射线中，跨位正交和（57.6）给
$$
S\perp W,\qquad v\perp S,\qquad\dim W\in\{2,3\}.
\tag{57.12}
$$
若 $v\in Q_3$，由 $V_1p_A=v\otimes A\in Q_3\otimes A=V_1U$ 得 $p_A\in U$，但（57.9）使 $p_A\in H_4$，违反 $H_4\cap U=0$。同理，$v\in Q_4$ 会使 $p_B\in G_3\cap H_3=0$。因此
$$
v\notin Q_3\cup Q_4.
\tag{57.13}
$$

**三维 $W$：同一内积给出的投影约束。**

假设 $\dim W=3$。式（57.12）使 $K=S\oplus W$，所以 $v\in W$。

定义等距 $f:U\to Q_3$、$g:G_3\to Q_4$，使
$$
V_1u'=f(u')\otimes A,\qquad
V_1z=g(z)\otimes B.
$$
由 $p_A\in H_4\subset U\oplus Q_4$，写 $p_A=u_A+q_A$。式（57.12）给 $q_A\perp S$，所以 $u_A=P_Up_A$。等距投影和（57.4）给
$$
f(u_A)=P_{Q_3}v.
\tag{57.14}
$$
对任意 $z\in G_3$，一方面
$$
\langle p_A,z\rangle
=\langle u_A,z\rangle
=\langle A,B\rangle\,\langle P_{Q_3}v,g(z)\rangle,
$$
另一方面，直接使用 $V_1p_A=v\otimes A$ 得
$$
\langle p_A,z\rangle
=\langle A,B\rangle\,\langle v,g(z)\rangle.
$$
非零 $\langle A,B\rangle$ 可消去，$g$ 满射到 $Q_4$，所以
$$
P_{Q_4}v=P_{Q_4}P_{Q_3}v.
\tag{57.15}
$$
于是 $v-P_{Q_3}v$ 同时正交于 $Q_3$、$Q_4$，也即正交于 $W$。但 $v,P_{Q_3}v\in W$，故 $v=P_{Q_3}v\in Q_3$，违反（57.13）。

**二维 $W$：第一轮环境与独立初态的冲突。**

只剩 $W=Q_3=Q_4=:Q$。式（57.10）使全部 $Q_n=Q$，且
$$
V_1S=Q\otimes F.
\tag{57.16}
$$
令 $T=S\oplus Q$，它六维，$Z=T^\perp$ 一维。由（57.9），$X=H_3+H_4\subset T$，所以 $P_0\subset T$。式（57.12）、（57.13）给正交分解
$$
v=v_Q+v_Z,\qquad v_Q=P_Qv,\quad 0\ne v_Z\in Z.
\tag{57.17}
$$

对任意 $\xi\in F$，（57.4）、（57.16）及等距性给
$$
V_1(P_Sp_\xi)=v_Q\otimes\xi.
$$
因为 $p_\xi\in T$，余下分量是 $P_Qp_\xi$，故
$$
V_1(P_Qp_\xi)=v_Z\otimes\xi.
\tag{57.18}
$$
$\xi\mapsto P_Qp_\xi$ 的范数等于 $\|v_Z\|\,\|\xi\|$，因此它是 $F$ 到二维 $Q$ 的线性同构。特别 $P_Qp_1,P_Qp_2$ 线性无关，并且
$$
V_1Q=\mathbb Cv_Z\otimes F,\qquad
V_1T=(Q\oplus\mathbb Cv_Z)\otimes F.
\tag{57.19}
$$

第一轮零位像 $V_0k$ 必正交于 $V_1S=Q\otimes F$。用真实 Schmidt 分解（57.3），投影到 $Q\otimes F$ 得
$$
\sum_{i=1}^2\sqrt{\lambda_i}\,(P_Qp_i)\otimes(P_Fe_i)=0.
$$
两个接收向量 $P_Qp_i$ 线性无关、两个权重严格正，故
$$
e_1,e_2\perp F.
\tag{57.20}
$$

由（57.3）、（57.20），$V_0k$ 正交于 $V_0H_2=G_3\otimes A$，所以 $k\perp H_2$。同样 $V_1k$ 正交于（57.19）中的整个 $V_1T$，所以
$$
k\in T^\perp=Z.
\tag{57.21}
$$
$u\in S\subset T$，而 $a^2u+bv\in H_2$，结合 $b\ne0$、$k\perp H_2$ 得 $\langle k,v\rangle=0$。但 $k$ 是一维 $Z$ 中的单位向量，式（57.17）给 $v$ 在 $Z$ 中的分量非零，因此不可能 $k\perp v$。矛盾。

两个可能的 $W$ 维数都被排除，定理得证。

### 57.3 整个 ABAB 的排除

**引理57.3（整个 ABAB 的排除）。** 不可能存在不同环境射线的单位代表 $A,B\in F$，使
$$
\eta_3=\eta_5=A,\qquad\eta_4=\eta_6=B.
\tag{57.22}
$$
该结论不要求 $A,B$ 正交，也不要求二者非正交。

**证明。** 令 $\pi:K\to K/U$。四维旧块使
$$
Z=(\pi\otimes I_E)V_0K,\qquad\dim Z\le3.
\tag{57.23}
$$
$V_1$ 在 $U,G_3,G_5$ 上分别使用 $A,B,B$，所以 $U\cap G_3=U\cap G_5=0$。于是
$$
M=\pi(G_3+G_5),\qquad m=\dim M\in\{2,3\},\qquad M\otimes A\subset Z.
\tag{57.24}
$$

若 $m=3$，则 $Z=M\otimes A$。不同环境 $B$ 的零位商像 $\pi(G_4)\otimes B$、$\pi(G_6)\otimes B$ 必为零，故
$$
G_4=G_6=U.
$$
固定零位等距给 $H_3=H_5$；固定一位等距在 $G_2=G_4=U$ 上给 $Q_3=Q_5=:Q$。共同环境 $A$ 的位像正交使 $G_3+G_5\perp Q$。于是同一空间 $H_3=H_5$ 到 $G_3+G_5$ 的投影像既等于 $G_3$、又等于 $G_5$，强制 $G_3=G_5$，与 $m=3$ 矛盾。

因此 $m=2$。置
$$
S=U+G_3+G_5,\qquad\dim S=4.
$$
因 $U\cap G_3=U\cap G_5=0$，
$$
S=U+G_3=U+G_5.
\tag{57.25}
$$
固定一位等距使
$$
V_1S=(Q_3\otimes A)+(Q_4\otimes B),\qquad
Q_6\otimes B=V_1G_5\subseteq V_1S.
\tag{57.26}
$$
$A,B$ 线性无关。逐个环境分量比较（57.26），任意 $q\otimes B\in Q_6\otimes B$ 的 $A$ 分量为零，所以 $q\in Q_4$。因此 $Q_6\subseteq Q_4$；两者二维，故 $Q_6=Q_4$。于是
$$
V_1G_5=Q_4\otimes B=V_1G_3.
$$
$V_1$ 单射给 $G_5=G_3$。再由两个零位像共用环境 $A$，
$$
V_0H_2=G_3\otimes A=G_5\otimes A=V_0H_4,\qquad H_2=H_4.
\tag{57.27}
$$
但非零 $w\in H_2\cap U=H_4\cap U$，式（57.6）使 $P_{Q_4}w=0$，违反 $P_{Q_4}|_{H_4}$ 单射。矛盾。

两种商维数均已排除，定理得证。

### 57.4 早期秩结论及保留范围

若 $r_2=1$，七维性与第一终端档案秩二给 $r_1\in\{1,2,3\}$。第53节已排除 $r_1=3$。若 $r_1=2$，第56节将全部候选压到非正交 $ABAA$ 或非正交 $ABAB$；引理57.2和57.3分别排除这两个模式。因此只余 $r_1=1$，定理57.1得证。

此结算使用同一实际来源、同一固定 Stinespring 等距和第一轮真实 Schmidt 分解；第一轮环境与第二轮排出空间的正交关系是在证明内部推出，没有被当作预设资源。全部论证只使用前六个终端。

一般七维候选仍可能落在第53节约束的 $r_2=2$ 分支，或 $r_1=r_2=1$ 的全部早期纯分支。这里没有排除这些剩余情况，故一般六终端固定 CPTP 接收容量仍为
$$
7\le d_{\mathrm{CPTP},6}\le8.
$$

## 追加锚（本行以下为增补区）

## 58. 七维第二终端秩二排除共同外部尾环境

固定非退化来源
$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,\qquad
ab\ne0,\quad |a|^2+|b|^2=1.
$$
七维接收器 $K$ 独立纯启动，全部持久系统计费，同一个全域 CPTP 接收通道精确服务前六个完整参考终端。第二终端可逆附加态秩为二，第三至第六终端纯。固定同一 Stinespring 等距的两个位块 $V_0,V_1:K\to K\otimes E$，两像正交。

### 58.1 实际第二终端与第三轮排出块

沿第53节，第二终端编码支撑为 $Q\otimes\Gamma\subset K$，$\dim Q=3$、$\dim\Gamma=2$；$u,v,w$ 为 $Q$ 中正交单位向量。附加态 $\tau_\Gamma$ 在 $\Gamma$ 上正定。置
$$
G=\operatorname{span}(u,w),\quad
H=\operatorname{span}(z,w),\quad
z=(a^2u+bv)/\sqrt{|a|^4+|b|^2}.
$$
第三轮将整个附加因子排到二维环境 $F\subset E$，给二维正交接收子空间
$$
A_0=G_3,\qquad B_0=Q_3,\qquad A_0\perp B_0,
$$
使
$$
V_0(H\otimes\Gamma)=A_0\otimes F,\qquad
V_1(G\otimes\Gamma)=B_0\otimes F.
\tag{58.1}
$$
两个旧位像均四维。这里第三轮新环境可以与旧环境纠缠，未被改称纯向量。

对 $n=4,5,6$，实际纯终端空间满足
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n,\qquad G_n\perp Q_n.
\tag{58.2}
$$
各 $H_n,G_n,Q_n$ 二维；$H_n\subset G_n\oplus Q_n$ 到两个同轮因子的投影均为同构。

**定理58.1（共同外部纯尾环境不可能）。** 不可能有
$$
\eta_4\parallel\eta_5\parallel\eta_6,\qquad \eta_4\notin F.
\tag{58.3}
$$
因此第53节的 $OOO$ 必要模式实际上不能由该接收器实现。

**证明。** 选择共同单位代表 $\eta$。第53节的严格环境交叠下界给
$$
0<\|P_F\eta\|<1.
\tag{58.4}
$$
右侧只用 $\eta\notin F$；左侧是完整六终端合同下已证必要条件，没有额外假设环境非正交。

置
$$
S_0=H_3+H_4+H_5,\qquad
S_1=G_3+G_4+G_5,
$$
并去掉共同环境，写等距 $f:S_0\to K$、$g:S_1\to K$。令
$$
R=fS_0=G_4+G_5+G_6,\qquad
W=gS_1=Q_4+Q_5+Q_6.
\tag{58.5}
$$
由于 $\eta\notin F$，$A_0\otimes F$ 与 $R\otimes\eta$ 交零；同理 $B_0\otimes F$ 与 $W\otimes\eta$ 交零。这些空间分别包含于七维 $V_0K,V_1K$，所以
$$
\dim S_0=\dim R\le3,\qquad
\dim S_1=\dim W\le3.
\tag{58.6}
$$

两项实际都等于三。若 $\dim S_0=2$，则 $H_3=H_4=H_5$，固定 $f$ 使 $G_4=G_5$，因而 $(H_4,G_4)=(H_5,G_5)$。若 $\dim S_1=2$，则 $G_3=G_4=G_5$，固定 $f$ 给 $H_3=H_4$，因而 $(H_3,G_3)=(H_4,G_4)$。这些都违反实际来源的主角谱变化。具体地，第53节式（53.14）的两个特征值之积给
$$
\delta_n=\det(P_{H_n}P_{G_n}|_{H_n})
=x^2\frac{t_{n-2}}{t_n},\quad
x=|a|^2,\quad y=|b|^2,\quad t_0=1,\quad t_j=1-y t_{j-1},
$$
并有
$$
\delta_{n+1}-\delta_n
=\frac{x^3(-y)^{n-1}}{t_nt_{n+1}}\ne0
\qquad(n=3,4).
\tag{58.7}
$$
故
$$
\dim S_0=\dim S_1=\dim R=\dim W=3.
\tag{58.8}
$$

### 58.2 两个全域位像同时饱和

式（58.1）、（58.5）、（58.8）现在饱和两个七维位像：
$$
V_0K=(A_0\otimes F)+(R\otimes\eta),\qquad
V_1K=(B_0\otimes F)+(W\otimes\eta).
\tag{58.9}
$$
两项都是代数直和；未声称它们在同一个位像内正交。

由于 $V_0K\perp V_1K$，有 $A_0\perp B_0$、$R\perp W$。式（58.4）的非零环境交叠还给
$$
A_0\perp W,\qquad R\perp B_0.
$$
所以接收子空间
$$
L_0=A_0+R,\qquad L_1=B_0+W
$$
满足
$$
L_0\perp L_1,\qquad
V_0K\subseteq L_0\otimes E,\qquad
V_1K\subseteq L_1\otimes E.
\tag{58.10}
$$
$W$ 三维使 $\dim L_1\ge3$，故
$$
\dim L_0\le4.
\tag{58.11}
$$
这些已经是整个固定通道的位像约束，不只对后面三个纯终端成立。

### 58.3 同一来源的早期支撑约束

来源每次发射后，活动记忆的 $|1\rangle$ 分量只来自 $m_0$ 中的 $b|1\rangle$；$m_1=|0\rangle$ 不贡献该分量。因此，任何一步接收后的记忆 $|1\rangle$ 条件接收态，都由 $V_0$ 的像产生。式（58.10）使其接收支撑包含于 $L_0$。这对实际第二终端同样成立，因为每轮使用的是同一个全域通道。

第二终端的标准可逆编码对两个来源基态给
$$
\Psi_2^0=a\,m_0\otimes u+b\,m_1\otimes v,\qquad
\Psi_2^1=m_0\otimes w,
$$
再张量固定混合附加态 $\tau_\Gamma$。对 Bell 参考输入，投影活动记忆为 $|1\rangle$、迹掉参考后，未归一化接收态为
$$
\frac{|b|^2}{2}
\bigl(|a|^2|u\rangle\langle u|+|w\rangle\langle w|\bigr)
\otimes\tau_\Gamma.
\tag{58.12}
$$
$ab\ne0$ 且 $\tau_\Gamma$ 正定，所以（58.12）的支撑恰为四维 $G\otimes\Gamma$。由上一段以及（58.11），
$$
G\otimes\Gamma\subseteq L_0,\qquad
L_0=G\otimes\Gamma.
\tag{58.13}
$$
这一步使用完整混合附加态，没有把其某个纯切片当作实际第二终端。

### 58.4 固定一位像的矛盾

$S_1=G_3+G_4+G_5$，其中 $G_3=A_0$、$G_4,G_5\subset R$。因此（58.13）给
$$
S_1\subseteq A_0+R=L_0=G\otimes\Gamma.
$$
固定一位映射一方面由旧块（58.1）使
$$
V_1S_1\subseteq B_0\otimes F,
$$
另一方面由纯尾定义使 $V_1S_1=W\otimes\eta$。因为 $\eta\notin F$，这两份张量子空间交为零，所以 $V_1S_1=0$。但 $V_1$ 等距且 $\dim S_1=3$，矛盾。证明完毕。

本定理仅排除 $r_2=2$ 分支的 $OOO$ 模式；第53节的 $FFF$ 与 $OFO$ 尚未由此结算。第57节的结论仍只适用于纯第二终端。一般六终端容量仍为 $7\le d_{\mathrm{CPTP},6}\le8$。

## 追加锚（本行以下为增补区）

## 59. 七维第二终端秩二的尾环境二维封闭性

固定非退化来源
$$
m_0=a|0\rangle+b|1\rangle,\qquad m_1=|0\rangle,\qquad
ab\ne0,\quad |a|^2+|b|^2=1.
$$
七维接收器 $K$ 独立纯启动，全部持久系统计费，同一个全域 CPTP 接收通道精确服务前六个完整参考终端。第二终端可逆附加态秩为二，第三至第六终端纯。固定同一 Stinespring 等距的两个位块 $V_0,V_1:K\to K\otimes E$，二者均等距且两像正交。

沿第53节，实际第二终端编码支撑为 $Q\otimes\Gamma\subset K$，$\dim Q=3$、$\dim\Gamma=2$；$u,v,w$ 为 $Q$ 中正交单位向量，附加态 $\tau_\Gamma$ 在 $\Gamma$ 上正定。置
$$
G=\operatorname{span}(u,w),\qquad
H=\operatorname{span}(z,w),\qquad
z=(a^2u+bv)/\sqrt{|a|^4+|b|^2}.
$$
第三轮给等距 $R_\Gamma:\Gamma\to E$、二维环境 $F=R_\Gamma\Gamma$，以及正交单位接收向量 $s,t,r,j$，使
$$
V_0(z\otimes\xi)=s\otimes R_\Gamma\xi,\qquad
V_0(w\otimes\xi)=t\otimes R_\Gamma\xi,
$$
$$
V_1(u\otimes\xi)=r\otimes R_\Gamma\xi,\qquad
V_1(w\otimes\xi)=j\otimes R_\Gamma\xi.
\tag{59.1}
$$
写
$$
A_0=\operatorname{span}(s,t)=G_3,\qquad
B_0=\operatorname{span}(r,j)=Q_3.
$$
于是 $A_0\perp B_0$，并有两个四维旧块
$$
V_0(H\otimes\Gamma)=A_0\otimes F,\qquad
V_1(G\otimes\Gamma)=B_0\otimes F.
\tag{59.2}
$$
第三轮新环境可以与旧环境纠缠，未被假设为纯向量。

对 $n=4,5,6$，纯尾环境和实际来源空间满足
$$
V_0H_{n-1}=G_n\otimes\eta_n,\qquad
V_1G_{n-1}=Q_n\otimes\eta_n.
\tag{59.3}
$$
各 $H_n,G_n,Q_n$ 二维；$C_n=G_n\oplus Q_n$ 四维，$H_n\subset C_n$ 到两个正交因子的投影均为同构，特别地 $H_n\cap G_n=0$。

**定理59.1（交替外部尾环境不可能）。** 在上述合同下，不可能有第53节的 $OFO$ 模式：
$$
\eta_4\parallel\eta_6,\qquad
\eta_4\notin F,\qquad \eta_5\in F.
\tag{59.4}
$$

**证明。** 选单位环境代表
$$
\eta_4=\eta_6=o\notin F,\qquad \eta_5=\beta\in F.
$$
这里等式只统一射线代表；（59.3）是子空间等式，不受整体相位影响。第53节的六终端环境交叠下界给
$$
P_Fo\ne0.
\tag{59.5}
$$
不预设 $o$ 与 $\beta$ 是否正交。

### 59.1 两个全域位像的维数饱和

令
$$
R=G_4+G_6,\qquad W=Q_4+Q_6,\qquad
r=\dim R,\quad k=\dim W,
$$
$$
d_0=\dim(A_0+G_5)-2,\qquad
d_1=\dim(B_0+Q_5)-2.
\tag{59.6}
$$
因为 $\beta\in F$，
$$
\dim\bigl((A_0\otimes F)+(G_5\otimes\beta)\bigr)=4+d_0.
$$
因为 $o\notin F$，$R\otimes o$ 与上述空间交零。两者都包含于七维 $V_0K$，所以
$$
r+d_0\le3.
\tag{59.7}
$$
$r\ge2$，因此 $d_0\in\{0,1\}$。同理对一位像有
$$
k+d_1\le3.
\tag{59.8}
$$
另一方面，固定 $V_1$ 在 $A_0=G_3$ 和 $G_5$ 上都使用同一射线 $o$，由（59.3）及等距性，
$$
V_1(A_0+G_5)=(Q_4+Q_6)\otimes o=W\otimes o,
\qquad k=2+d_0.
\tag{59.9}
$$
合并（59.8）得 $d_0+d_1\le1$。故只有
$$
(d_0,d_1)=(0,0),\ (1,0),\ (0,1).
\tag{59.10}
$$

**排除 $(0,0)$。** 此时 $G_5=A_0$、$Q_5=B_0$。取单位 $\xi\in\Gamma$ 使 $R_\Gamma\xi=\beta$。由（59.1）、（59.3），
$$
V_0(H\otimes\mathbb C\xi)=A_0\otimes\beta=V_0H_4,
$$
$$
V_1(G\otimes\mathbb C\xi)=B_0\otimes\beta=V_1G_4.
$$
两个固定等距均单射，因而
$$
H_4=H\otimes\mathbb C\xi,\qquad
G_4=G\otimes\mathbb C\xi.
$$
这两者包含同一非零向量 $w\otimes\xi$，违反 $H_4\cap G_4=0$。

**情形 $(1,0)$。** 式（59.9）给 $k=3$，式（59.7）给 $r=2$。两个已知位像的维数分别为 $4+1+2=7$ 和 $4+0+3=7$。

**情形 $(0,1)$。** 此时 $G_5=A_0=G_3$、$k=2$。若 $r=2$，则 $G_4=G_6$。固定 $V_0$ 和共同环境 $o$ 给 $H_3=H_5$，故 $(H_3,G_3)=(H_5,G_5)$。这违反实际来源的主角谱。具体地，令
$$
x=|a|^2,\quad y=|b|^2,\quad t_0=1,\quad t_j=1-y t_{j-1}.
$$
第53节式（53.14）的两个主角特征值之积为
$$
\delta_n=\det(P_{H_n}P_{G_n}|_{H_n})
=x^2\frac{t_{n-2}}{t_n},
$$
且
$$
\delta_5-\delta_3
=\frac{x^4y^2}{t_3t_5}>0.
\tag{59.11}
$$
因此 $r=3$，两个已知位像的维数分别为 $4+0+3=7$ 和 $4+1+2=7$。

综上，任意尚存候选均使两个全域位像恰好饱和：
$$
V_0K=(A_0\otimes F)+(G_5\otimes\beta)+(R\otimes o),
$$
$$
V_1K=(B_0\otimes F)+(Q_5\otimes\beta)+(W\otimes o).
\tag{59.12}
$$
这些和空间未被默认视为正交和。

### 59.2 非正交尾环境与实际第二终端矛盾

先设 $\langle o,\beta\rangle\ne0$。由 $V_0K\perp V_1K$，环境因子的非零交叠给全部跨位接收因子正交：
$$
A_0\perp B_0,Q_5,W,\qquad
G_5\perp B_0,Q_5,W,\qquad
R\perp B_0,Q_5,W.
\tag{59.13}
$$
其中跨 $F,o$ 的两项使用（59.5），跨 $\beta,o$ 的两项使用当前非零交叠；其余使用相同环境，或 $\beta\in F$。

因此
$$
L_0=A_0+G_5+R,\qquad L_1=B_0+Q_5+W
$$
满足
$$
L_0\perp L_1,\qquad
V_iK\subseteq L_i\otimes E\quad(i=0,1).
\tag{59.14}
$$
$(d_0,d_1)=(1,0)$ 时 $\dim W=3$；$(d_0,d_1)=(0,1)$ 时 $\dim(B_0+Q_5)=3$。所以总有
$$
\dim L_1\ge3,\qquad \dim L_0\le4.
\tag{59.15}
$$

现在使用同一固定通道的实际早期来源。来源每次发射后，活动记忆的 $|1\rangle$ 分量仅来自 $m_0$ 中的 $b|1\rangle$，因此任何轮次的记忆 $|1\rangle$ 条件接收态均由 $V_0$ 的像产生。（59.14）使其接收支撑位于 $L_0$。该断言同样适用于第二终端，没有假设第二终端纯。

第二终端的标准可逆编码为
$$
\Psi_2^0=a\,m_0\otimes u+b\,m_1\otimes v,\qquad
\Psi_2^1=m_0\otimes w,
$$
并张量固定正定附加态 $\tau_\Gamma$。对 Bell 参考输入，投影活动记忆为 $|1\rangle$ 后再迹掉参考，所得未归一化接收态为
$$
\frac{|b|^2}{2}
\bigl(|a|^2|u\rangle\langle u|+|w\rangle\langle w|\bigr)
\otimes\tau_\Gamma.
\tag{59.16}
$$
其支撑恰好是四维 $G\otimes\Gamma$。由（59.14）、（59.15），
$$
L_0=G\otimes\Gamma.
\tag{59.17}
$$
特别地 $A_0\subseteq G\otimes\Gamma$。旧一位块（59.2）遂使
$$
V_1A_0\subseteq B_0\otimes F.
$$
然而实际第四轮又给
$$
V_1A_0=Q_4\otimes o.
$$
由于 $o\notin F$，这两个张量子空间交零，违反 $V_1$ 单射及 $\dim A_0=2$。非正交情形不可能。

### 59.3 正交尾环境迫使两个四维终端支撑正交

余下设 $o\perp\beta$。由（59.3），固定等距保持内积，给
$$
A_0\perp G_4,\qquad H_3\perp H_4.
\tag{59.18}
$$
第一项来自 $V_1A_0=Q_4\otimes o$ 和 $V_1G_4=Q_5\otimes\beta$；第二项来自 $V_0H_3=G_4\otimes o$ 和 $V_0H_4=G_5\otimes\beta$。

跨位正交连同（59.2）、（59.5）另给
$$
A_0\perp Q_4,\qquad B_0\perp G_4.
\tag{59.19}
$$
现在 $H_3\subset A_0\oplus B_0$、$H_4\subset G_4\oplus Q_4$。对任意 $h\in H_3$、$h'\in H_4$，用（59.18）、（59.19）消去其余三种交叉配对，得到
$$
0=\langle h,h'\rangle
=\langle P_{B_0}h,P_{Q_4}h'\rangle.
$$
实际来源给 $P_{B_0}H_3=B_0$、$P_{Q_4}H_4=Q_4$，故
$$
B_0\perp Q_4.
\tag{59.20}
$$
合并（59.18）—（59.20），
$$
C_3=A_0\oplus B_0\ \perp\ C_4=G_4\oplus Q_4.
$$
这要求七维 $K$ 包含两个正交的四维子空间，矛盾。正交情形亦不可能。证明完毕。

### 59.4 第二终端秩二的必要环境封闭性

**推论59.2（全部纯尾环境留在同一二维空间）。** 结合第53节的 $FFF/OFO/OOO$ 必要模式、第58节的共同外部尾环境排除与定理59.1，第二终端秩二的任意七维六终端候选必须满足
$$
\eta_4,\eta_5,\eta_6\in F.
$$
这一结论尚未排除 $FFF$，也未处理早期终端全部纯的其余候选。一般六终端容量仍为 $7\le d_{\mathrm{CPTP},6}\le8$。

## 追加锚（本行以下为增补区）
