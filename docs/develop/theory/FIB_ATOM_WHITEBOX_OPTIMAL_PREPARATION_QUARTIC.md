# FIB 完整张量符号源：四阶最优准备与充分优化解码后的严格分离

## 1. 固定来源、准备类与整条服务合同

**数学引文 1.1（来源与证明范围）。** 本卷以共同科学快照 [`f833660337ac6264fc6f742d4b2114f25b4df6c8`](https://github.com/the-omega-institute/trureturing/tree/f833660337ac6264fc6f742d4b2114f25b4df6c8) 中的 [Correlated Word Recovery][Recovery] 定义 1.2–1.4 和 [Legal Edge Minimax][Minimax] 定义 1.2–1.6 为固定合同。前者供应均匀 Bayes 最优错误首项、平方根测量构造及完整服务对应；后者供应 minimax 首项及其与 Bayes 首项的目标不相容性。本卷在同一完整来源上给出全准备类的 Bayes 四阶优化、乘积准备类在任意联合解码之后的四阶损失及相应整数调用展开。以下是普通数学定理与证明，作为理论参考输入，未经 Lean kernel 验证；理想源、公开校准、准备和任意末端测量均是明确假设。

**定义 1.2（完整合法词与同一未知源）。** 固定整数 $N,L\ge1$，令 $n=3N$、$\theta=\pi/(4L)$。系统为 $\mathcal K=(\mathbb C^2)^{\otimes n}$，因子标签、带符号的计算基及 $X,Y,Z$ 标准已知。置

$$
\begin{aligned}
B_n&=\{b\in\{0,1\}^n:b_i b_{i+1}=0\quad(1\le i<n)\},\\
s_i(b)&=(-1)^{b_i},\\
U_b&=\bigotimes_{i=1}^n\exp(i s_i(b)\theta Z),\\
\Lambda_b(\rho)&=U_b\rho U_b^\dagger.
\end{aligned}
$$

未知 $b$ 选定一次，实验始终使用这个理想、无噪声、无记忆、已校准的源。一次普通调用对整个 $n$ 量子位系统施加 $\Lambda_b$，对参考及工作空间施加恒等。来源域包括全零词、尾部 null 窗和每一个跨窗接缝；没有额外标签建议，没有 canonical $\mathrm{End}$。

**定义 1.3（完整一块式协议类）。** $q$ 是满足 $0\le q\le L$ 的整数。协议准备与 $b$ 无关的任意输入密度态和任意有限维参考，随后在同一系统上连续作恰好 $q$ 次普通完整系统调用，调用间不操作系统，最后作一次任意联合末端 POVM，经有限末端计算输出 $\widehat b\in B_n$。允许与源无关的随机化和工作空间初值。仅作用于参考的中间操作与源调用交换，可推迟到末端。不允许未知 controlled-$U$、逆源、源复位、重新抽取来源标签、调用间系统控制或源相关建议。

以下全类最优值取遍这整个协议类。输入、有限参考维数、随机化和末端 POVM 均可随公开整数合同变化。源、参考和准备必须在同一次实验内共同实现，不能分别为不同合法词更换输入。

**定义 1.4（先验、损失与整数重叠参数）。** 令 $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$，$M=M_n=|B_n|=F_{n+2}$。采用完整 $B_n$ 上的均匀先验和整词零一损失。协议 $\Pi$ 的逐源成功概率为 $p_\Pi(b)=\Pr_b(\widehat b=b)$，定义

$$
\begin{aligned}
\beta_n(L,q)&=\sup_\Pi\frac1M\sum_{b\in B_n}p_\Pi(b),\\
\varepsilon_n^\star(L,q)&=1-\beta_n(L,q),\\
\beta_n^{\mathrm{mm}}(L,q)&=\sup_\Pi\min_{b\in B_n}p_\Pi(b),\\
x&=\cos(2q\theta)=\cos\left(\frac{\pi q}{2L}\right),\qquad 0\le x\le1.
\end{aligned}
$$

非法答案可归给一个固定合法词，因而末端不必另设失败标签。错误指整词错误，不是平均单个位错误。$x$ 是一次准备后连续酉迭代的重叠，不是 $q$ 份新样本的重叠，也不是 $(\cos(2\theta))^q$。以 $x$ 表示有限矩阵不授予固定设备内自由改角度的操作。Bayes、minimax、指定策略分数及逐源分数分别按其定义解释。

**定义 1.5（合法图与四阶系数）。** 以 $B_n$ 为顶点，Hamming 距离一时连边，记邻接矩阵为 $A=A_n$、无向边数为 $e=e_n$、顶点度数为 $d_b$。复用 [Recovery][Recovery] 的计数

$$
e_n=\sum_{b\in B_n}|b|
=\frac{nF_{n+1}+2(n+1)F_n}{5},\qquad |b|=\sum_i b_i.
$$

计数辅助约定 $B_0=\{\text{空词}\}$、$e_0=0$；实际源仍为 $n=3N\ge3$。令

$$
\begin{aligned}
s_n&=\sum_{b\in B_n}\binom{|b|}{2}
=\frac{(5n^2+3n-2)F_n-6nF_{n+1}}{50},\\
C_n&=\frac{e_n}{2M},\\
Q_n&=\frac{e_n-2s_n}{8M}
=\frac{11nF_{n+1}-(5n^2-7n-12)F_n}{200F_{n+2}},\\
\Delta_n&=\frac{e_{n-1}}{32M}>0.
\end{aligned}
$$

$s_n$ 计数合法图的二维立方体面，其表达式在 §3.7 证明；$C_n$ 是既有全类 Bayes 首项。本卷的优化增量是 $Q_n$、$\Delta_n$ 及其准备实现，不将立方体计数作为独立新结论。范数采用 $\|T\|_{\mathrm{HS}}^2=\operatorname{Tr}(T^\dagger T)$；$O_n$ 的常数和邻域只须对固定 $n$ 成立。

**定义 1.6（完整乘积及局部参考准备类）。** 记 $\mathcal P_{\mathrm{prod}}$ 为以下受限准备类：给定一个与源无关的经典随机种子，准备态是各位点 $S_i\otimes R_i$ 上状态的张量积，再附一个与这些因子独立的有限辅助态。每个局部参考 $R_i$ 可任意且有限，每个局部状态可为混态；随机种子可保留给末端解码。末端 POVM 仍任意，允许跨全部寄存器的联合测量。仅在这个具名准备类中排除不同 $S_i\otimes R_i$ 因子之间的初始相干关联；共同经典种子的随机混合仍在类内。令

$$
\beta_n^{\mathrm{prod}}(L,q)
=\sup_{\Pi\in\mathcal P_{\mathrm{prod}}}\frac1M\sum_b p_\Pi(b),
\qquad
\varepsilon_n^{\mathrm{prod}}(L,q)=1-\beta_n^{\mathrm{prod}}(L,q).
$$

该类的限制在准备，不在解码；它不能替代定义 1.3 的完整准备类。

**定义 1.7（计算基分布及矩坐标）。** 对 $Z$ 的计算基本征值 $z=(z_1,\ldots,z_n)\in\{-1,+1\}^n$，令 $z_S=\prod_{i\in S}z_i$。概率分布 $\pi$ 的矩为

$$
m_S=\sum_z\pi(z)z_S,\qquad m_\varnothing=1.
$$

以非负计算基振幅表示的系统态为

$$
|\chi_\pi\rangle=\sum_z\sqrt{\pi(z)}\,|z\rangle.
$$

分布 $\pi$ 的唯一性与全部物理准备态的唯一性不同；与源交换的相位或等价参考实现不由这个表示区分。

**定义 1.8（完整五窗索引与指针服务）。** 按 [Recovery][Recovery] 定义 4.2 的有限终止及全部有限历史合同，置

$$
W_j(b)=(b_{3j-2},b_{3j-1},b_{3j}),\qquad 1\le j\le N.
$$

五种窗口 $000,100,010,101,001$ 分别读作 $\mathrm{null},2,3,2\ 5,5$；每个接缝仍须满足 $b_{3j}b_{3j+1}=0$。安装输出为闭合、确定性服务，安装及每个合法回复均有限终止，安装后不再访问源或源相关建议。随机化只用于安装。整条成功要求每条有限合法查询历史的回复均正确，包含重复索引及依先前回复自适应选择的查询，并保持读出、合法域和更新。

索引 $j$ 返回 $W_j$。指针版本另有初值 $a=1$，取值在 $\{1,\ldots,N+1\}$；索引读不改 $a$，$\mathrm{Next}$ 恰在 $a\le N$ 时合法，返回 $W_a$ 后递增 $a$。没有 $\mathrm{End}$，尾部 null 窗仍占三位。

## 2. 全准备类的四阶定理

**定理 2.1（四阶最优准备、乘积类分离与整数实现）。** 在定义 1.2–1.8 的不变合同下，以下六项成立。

(A) 对每个固定 $n=3N$，存在 $\rho_n>0$ 和 $K_n<\infty$，使每个满足 $0\le x\le\rho_n$ 的原整数合同都有

$$
\left|\varepsilon_n^\star(L,q)-C_nx^2-Q_nx^4\right|
\le K_nx^6.
\tag{2.1}
$$

因此，每个允许的准备、有限参考、随机化协议和末端 POVM 的平均错误至少为

$$
C_nx^2+Q_nx^4-K_nx^6.
$$

常数与协议及参考维数无关，但可依赖固定 $n$。

(B) 对每个整数合同，$\mathcal P_{\mathrm{prod}}$ 的优化分数等于单个平衡准备 $|+\rangle^{\otimes n}$ 在任意末端 POVM 下的优化分数。对固定 $n$ 和充分小的 $x$，

$$
\begin{aligned}
\varepsilon_n^{\mathrm{prod}}(L,q)
&=C_nx^2+(Q_n+\Delta_n)x^4+O_n(x^6),\\
\beta_n(L,q)-\beta_n^{\mathrm{prod}}(L,q)
&=\Delta_nx^4+O_n(x^6)>0.
\end{aligned}
\tag{2.2}
$$

严格正号用于充分小的正 $x$。这是两个已优化取得类的分离，两类都已充分优化联合解码器，不是两个固定接收器的比较。

(C) 压缩到非负计算基振幅后，完整 Bayes 问题对充分小的 $x$ 有唯一最优概率分布 $\pi_\star(z,x)$。它实解析、关于 $x$ 为偶函数，满足 $\pi_\star(z,x)=\pi_\star(-z,x)$，并有对所有 $z$ 一致的展开

$$
\pi_\star(z,x)
=2^{-n}\left[1-\frac{x^2}{4}\sum_{i=1}^{n-1}z_i z_{i+1}
+O_n(x^4)\right].
\tag{2.3}
$$

唯一性仅指该压缩分布，不是模去交换相位或等价参考之后的物理态唯一性。显式分布

$$
\pi_{\mathrm{trial}}(z,x)
=2^{-n}\left[1-\frac{x^2}{4}\sum_{i=1}^{n-1}z_i z_{i+1}\right]
\tag{2.4}
$$

在 $(n-1)x^2<4$ 时严格为正。准备

$$
|\chi_x\rangle=\sum_z\sqrt{\pi_{\mathrm{trial}}(z,x)}\,|z\rangle,
$$

作规定的 $q$ 次调用，对完整输出态族使用 SRM，即得到平均错误

$$
C_nx^2+Q_nx^4+O_n(x^6).
\tag{2.5}
$$

该实现不使用输入参考，仅用一个共同末端测量。式（2.4）没有被断言在有限正 $x$ 精确最优。

(D) 完整五标签域

$$
B_3=\{000,100,010,101,001\}
\longleftrightarrow\{\mathrm{null},2,3,2\ 5,5\}
$$

有 $M=e=5$、$s_3=1$、$e_2=2$，所以

$$
\begin{aligned}
\varepsilon_3^\star&=\frac{x^2}{2}+\frac{3x^4}{40}+O(x^6),\\
\varepsilon_3^{\mathrm{prod}}&=\frac{x^2}{2}+\frac{7x^4}{80}+O(x^6),\\
\beta_3-\beta_3^{\mathrm{prod}}&=\frac{x^4}{80}+O(x^6).
\end{aligned}
\tag{2.6}
$$

五个原标签全部保留；这些是优化错误和成功优势的系数，不是数值样本。

(E) 对每个固定 $n=3N$ 和固定整数 $r\ge1$，沿 $q=L-r$、$L\to\infty$，

$$
\begin{aligned}
\varepsilon_n^\star(L,L-r)
&=\frac{\pi^2r^2e_n}{8ML^2}
-\frac{\pi^4r^4(e_n+6s_n)}{384ML^4}
+O_{n,r}(L^{-6}),\\
\beta_n(L,L-r)-\beta_n^{\mathrm{prod}}(L,L-r)
&=\frac{\pi^4r^4e_{n-1}}{512ML^4}
+O_{n,r}(L^{-6}).
\end{aligned}
\tag{2.7}
$$

对充分大 $L$，这些是 $0<q<L$ 的真正内部整数合同。第一式的 $L^{-4}$ 修正严格负且非零，不使用自由调节的物理角度。

(F) $q=0$ 时两个 Bayes 准备类的成功率均为 $1/M$，$q=L$ 时均为 $1$。在定义 1.8 的有限终止和全部有限历史合同下，完整五窗索引服务及其指针版本具有相同的优化 Bayes 分数及四阶分离。本定理不推出 minimax 四阶结论或逐来源支配。

## 3. 定理 2.1 的完整普通证明

### 3.1 准备与有限参考的精确压缩

先固定一个无经典随机化的协议。利用额外有限参考将输入纯化，写成

$$
|\psi\rangle=\sum_z|z\rangle|r_z\rangle,
\qquad \pi(z)=\langle r_z,r_z\rangle.
$$

所有 $U_b$ 在 $z$ 基中对角，故来源输出的 Gram 矩阵只通过 $\pi$ 依赖输入，恰等于系统输入 $|\chi_\pi\rangle$ 所给的 Gram 矩阵。原混态测量可忽略附加纯化参考，从而保持原概率。

相同的 Gram 矩阵给出两个带标签输出族张成空间之间的等距映射：将

$$
\sum_b c_b|\psi_b\rangle
\quad\text{映到}\quad
\sum_b c_b|\chi_{\pi,b}\rangle.
$$

Gram 相等同时证明映射良定义并保持内积。经这个等距映射转移原 POVM，在正交补上任意补全，就同时保持每个真实 $b$ 下的全部条件答案概率。映射与转移测量只依赖所选准备及公开候选模型，不依赖未知真实源。

因此，优化任意输入和有限参考，精确归约为优化概率分布 $\pi$ 与 $|\chi_\pi\rangle$ 输出族的末端 POVM。经典随机化不能提高 Bayes 上确界，因为随机化的 Bayes 分数是各条件协议分数的平均。这一归约允许参考维数和准备随整数合同变化。

置 $t=\sqrt{1-x^2}$。令 $D=\{i:b_i\ne c_i\}$、$s_S(b)=\prod_{i\in S}s_i(b)$，则规范化 Gram 矩阵精确为

$$
\begin{aligned}
G_{bc}(\pi,x)
&=\sum_z\pi(z)\prod_{i\in D}\bigl(x-it s_i(b)z_i\bigr)\\
&=\sum_{S\subseteq D}x^{|D|-|S|}(-it)^{|S|}s_S(b)m_S,
\qquad G_{bb}=1.
\end{aligned}
\tag{3.1}
$$

Walsh 特征的正交恒等式为

$$
\sum_z z_Sz_T=
\begin{cases}2^n,&S=T,\\0,&S\ne T.\end{cases}
$$

由此得到反演

$$
\pi(z)=2^{-n}\sum_{S\subseteq\{1,\ldots,n\}}m_Sz_S.
\tag{3.2}
$$

非空矩是概率单纯形的实坐标，零矩向量的一个邻域位于其内部。

### 3.2 充分优化解码的局部一致估计

此处需要最小错误辨识解析理论的一个定量局部后果，而不假设 SRM 精确最优。正定加权 Gram 矩阵的最优检测器解析依赖已有供应，见 [Singal–Ghosh][SG] 定理 3.2、4.1–4.2 及 §4.2 末尾；在这里的等先验规范化中，对应其加权 Gram 矩阵的是 $G/M$。以下局部推导给出本定理所需的特定余项。

设 $G=I+H$ 是正定的 $M\times M$ Gram 矩阵，$H$ Hermitian、$\operatorname{diag}(H)=0$，范数充分小。令 $S=\sqrt G$，以 $\mathbb C^M$ 中的列 $v_i=Se_i$ 表示规范化状态。其等先验优化成功率记为 $P_{\mathrm{opt}}(G)$，SRM 成功率为

$$
P_{\mathrm{SRM}}(G)=\frac1M\sum_iS_{ii}^2.
$$

坐标测量附近的带标签正交测量用局部坐标 $V=\exp(K)$ 表示，其中 $K$ 反 Hermitian 且对角为零；测量向量为 $\mu_i=V^\dagger e_i$。成功函数为

$$
F(K,G)=\frac1M\sum_i|(VS)_{ii}|^2.
$$

在 $G=I$ 时，

$$
F(K,I)=1-\frac{\|K\|_{\mathrm{HS}}^2}{M}+O(\|K\|^3).
$$

因而在这些实局部坐标中的 Hessian 负定。实解析隐函数定理给出唯一的邻近平稳测量 $K(G)$，并使其解析依赖 $G$。

这一平稳测量对所有 POVM 最优，不仅在正交测量类中最优。置

$$
\rho_i=|v_i\rangle\langle v_i|,
\qquad Q_i=|\mu_i\rangle\langle\mu_i|,
\qquad \Gamma=\frac1M\sum_i\rho_iQ_i.
$$

对测量旋转的平稳性给出 $\Gamma=\Gamma^\dagger$；另有

$$
\left(\Gamma-\frac{\rho_i}{M}\right)\mu_i=0.
$$

在 $G=I$ 时，$\Gamma-\rho_i/M$ 在 $\mu_i^\perp$ 上的限制为 $I/M$。由连续性，缩小邻域后，这些限制对有限多个 $i$ 一致正定，故

$$
\Gamma-\frac{\rho_i}{M}\succeq0.
$$

对任意 POVM $(R_i)$，其成功率为

$$
\operatorname{Tr}\Gamma-
\sum_i\operatorname{Tr}\left[\left(\Gamma-\frac{\rho_i}{M}\right)R_i\right]
\le\operatorname{Tr}\Gamma.
$$

每个被减去的迹均因两因子半正定而非负，$(Q_i)$ 达到 $\operatorname{Tr}\Gamma$。这证明解析局部检测器在完整 POVM 类中的最优性；所用是普通半正定对偶证书。

$H$ 的零对角给出 $S_{ii}=1+O(\|H\|^2)$，而非对角 $S_{ij}=O(\|H\|)$。在 $K=0$ 微分有

$$
dF(0,G)[K]
=\frac2M\sum_{i<j}(S_{ii}-S_{jj})
\operatorname{Re}(K_{ij}S_{ji}).
\tag{3.3}
$$

故零点梯度为 $O(\|H\|^3)$。可逆 Hessian 在局部一致远离奇异，因而 $K(G)=O(\|H\|^3)$，Taylor 公式给出邻域内一致估计

$$
0\le P_{\mathrm{opt}}(G)-P_{\mathrm{SRM}}(G)=O(\|H\|^6).
\tag{3.4}
$$

展开

$$
S=I+\frac H2-\frac{H^2}{8}+\frac{H^3}{16}
-\frac{5H^4}{128}+O(\|H\|^5),
$$

再将对角项平方，得到优化错误

$$
\begin{aligned}
E(G)=1-P_{\mathrm{opt}}(G)
&=\frac{\operatorname{Tr}(H^2)}{4M}
-\frac{\operatorname{Tr}(H^3)}{8M}\\
&\quad+\frac{5\operatorname{Tr}(H^4)
-\sum_i((H^2)_{ii})^2}{64M}
+O(\|H\|^5).
\end{aligned}
\tag{3.5}
$$

此处全部范数和常数均在固定维数 $M$ 中解释。式（3.4）允许六阶或更高阶的测量改善，没有把 SRM 当作有限正 $x$ 的精确最优测量。

### 3.3 局部分析如何控制全局准备最优值

在 $x=0$，式（3.1）的非对角项成为

$$
G_{bc}=(-i)^{|D|}s_D(b)m_D.
$$

每个非空 $D\subseteq\{1,\ldots,n\}$ 都是两个合法词的对称差：把 $D$ 中物理奇数位置置入 $b$，偶数位置置入 $c$。两个词各自没有相邻的 $1$，其对称差恰为 $D$。此步骤使用完整合法域。

正先验下，规范化纯态能被完美辨识必彼此正交。事实上，成功一迫使 $Q_iv_i=v_i$，并对 $j\ne i$ 迫使 $Q_iv_j=0$，所以 $\langle v_i,v_j\rangle=0$。因此在 $x=0$ 完美辨识强制每个非空矩 $m_D$ 为零。Walsh 反演随即强制 $\pi(z)=2^{-n}$，均匀分布是该端点唯一零错误压缩准备。

固定 $n$ 时，$\pi$ 的概率单纯形紧，固定 $2^n$ 维系统上具有 $M$ 个结果的 POVM 集亦紧。以非负振幅 $\sqrt{\pi(z)}$ 表示输入，成功率对 $\pi,x$ 连续。因此优化错误 $E(\pi,x)$ 连续且全局最小值存在。

均匀分布任一邻域的补集上，$E(\pi,0)$ 有严格正的最小值。一致连续性使小 $x$ 时该补集仍与零错误分开，而均匀准备的错误趋于零。因此 $x\to0$ 时，每个全局最优准备都必须进入均匀分布的任意给定小邻域。

在这个邻域中 Gram 矩阵正定，§3.2 使 $E(m,x)$ 实解析。对非空 $D$，令 $N_D$ 为满足 $b\oplus c=D$ 的有序合法词对数；上述对称差构造证明 $N_D>0$。§3.2 的二次项在 $x=0$ 给出

$$
E(m,0)=\frac1{4M}\sum_{D\ne\varnothing}N_Dm_D^2
+O(\|m\|^3).
\tag{3.6}
$$

其 Hessian 正定。解析隐函数定理因此给出零附近唯一平稳准备 $m_\star(x)$。缩小邻域后，准备 Hessian 在其中保持正定。结合此前的全局局部化，得到充分小 $x$ 时该平稳准备就是唯一全局压缩最小化分布。最优准备的解析性由此被证明，而不是对任意优化族预先假设。

### 3.4 对称性排除低阶准备方向

将 $\pi(z)$ 换成 $\pi(-z)$ 会把 $G$ 换成其复共轭，保持每个可达辨识分数。矩坐标变为 $m_S\mapsto(-1)^{|S|}m_S$。压缩最优分布的唯一性因此给出

$$
m_{\star,S}(x)=0\qquad(|S|\text{ 为奇数}).
\tag{3.7}
$$

令对角矩阵 $J$ 满足 $J_{bb}=(-1)^{|b|}$。精确 Gram 公式还给出

$$
G(m,-x)=J\,\overline{G(m,x)}\,J.
$$

复共轭及各状态代表的重新定相不改变辨识概率，故 $E(m,-x)=E(m,x)$。解析平稳分支的唯一性推出 $m_\star(-x)=m_\star(x)$。

负 $x$ 仅用于这些有限矩阵的解析延拓，不授予负重叠参数、额外源操作或任意可调物理角度。对每个非空偶数大小的 $S$，因此有

$$
m_{\star,S}(x)=a_Sx^2+O_n(x^4),
\tag{3.8}
$$

全部奇数矩精确为零。原问题中未预先限制为近乘积形态的准备，也已由 §3.3 控制；完整优化问题的四阶部分遂归为确定这些有限系数 $a_S$。

### 3.5 四阶准备泛函

对非空偶数大小的 $S$，取任意固定实系数集合 $a_S$，并考虑 $m_S=a_Sx^2+O(x^4)$、奇数矩全零的准备。Gram 公式给出

$$
H=xA+x^2B+x^3C+O(x^4).
\tag{3.9}
$$

$B$ 实对称、对角为零，只支撑在偶数 Hamming 距离；$C$ 只支撑在至少为三的奇数 Hamming 距离。因此 $\operatorname{Tr}(AB)=\operatorname{Tr}(AC)=0$。合法图为二部图，故 $\operatorname{Tr}(A^3)=0$。

对 $b\ne c$、$D=b\oplus c$，二阶矩阵精确为

$$
B_{bc}=
\begin{cases}
\mathbf1_{\{|D|=2\}}+(-1)^{|D|/2}s_D(b)a_D,
&|D|\text{ 为偶数},\\
0,&|D|\text{ 为奇数}.
\end{cases}
\tag{3.10}
$$

代入式（3.5）得到

$$
\begin{aligned}
E&=C_nx^2+Q(B)x^4+O(x^5),\\
Q(B)&=\frac{\operatorname{Tr}(B^2)}{4M}
-\frac{3\operatorname{Tr}(A^2B)}{8M}
+\frac{5\operatorname{Tr}(A^4)-\sum_b d_b^2}{64M}.
\end{aligned}
\tag{3.11}
$$

对解析偶最优分支，余项提高为 $O_n(x^6)$。Walsh 反演说明任意固定集合 $a_S$ 在充分小 $x$ 时都可行。把精确全局最优值与每个这样的试验准备比较，最优分支的系数集合必须在全部这些实 $a_S$ 上最小化 $Q(B)$。这一比较没有限制原协议类，因为 §3.3 已将每个全局最优准备局部化。

由于 $\operatorname{diag}(B)=0$，$Q(B)$ 中依赖准备的部分在相差一个常数后为

$$
\frac1{4M}\left\|B-\frac34
\bigl(A^2-\operatorname{diag}(d)\bigr)\right\|_{\mathrm{HS}}^2.
\tag{3.12}
$$

因此可按对称差集合分别最小化，随后还须检查这些系数能否由一个准备同时实现。

### 3.6 精确最小化及同一次准备的实现

先取相邻物理位置 $D=\{i,i+1\}$。在这两位都不同的两个合法词只能分别为 $10$ 和 $01$，所以 $s_D(b)=-1$，$B_{bc}=1+a_D$。两个词恰有一个共同合法邻点，其这两位为 $00$，因此 $(A^2)_{bc}=1$。每个这样的条目在 $B_{bc}=3/4$ 时最小，给出

$$
a_{\{i,i+1\}}=-\frac14.
\tag{3.13}
$$

再取不相邻位置 $D=\{i,j\}$、$|i-j|>1$。只要有两个合法词在这两位不同，保持其共同外部位串，在 $i,j$ 上的四个组合就都合法，形成一个正方形。两条无序对角线的 $B$ 条目分别是 $1-a_D$ 和 $1+a_D$，各有两个共同邻点，故目标条目都是 $3/2$。两条对角线的平方距离之和为

$$
\left(1-a_D-\frac32\right)^2
+\left(1+a_D-\frac32\right)^2
=\frac12+2a_D^2.
$$

唯一最小值在 $a_D=0$。这一配对分别适用于每个允许的外部上下文。

对偶数 $|D|\ge4$，$A^2$ 在该距离上没有非对角条目，$B_{bc}$ 是一个符号乘 $a_D$。因为 $N_D>0$，其贡献是严格正倍数的 $a_D^2$，唯一最小点仍为 $a_D=0$。

所以唯一的最小化系数集合是全部 $n-1$ 个相邻物理位置对取 $-1/4$，其他每个非空偶数集合取零。结合式（3.2）、（3.7）–（3.8），得到定理 (C) 的最优准备展开。

这些分开求得的系数由同一个分布同时实现，而不是独立探针或不相容二元接收器的拼接。取式（2.4）的 $\pi_{\mathrm{trial}}$。每个非恒定 Walsh 特征的总和为零，所以该分布总质量为一；且

$$
\pi_{\mathrm{trial}}(z,x)
\ge2^{-n}\left[1-\frac{(n-1)x^2}{4}\right]>0
\qquad\bigl((n-1)x^2<4\bigr).
$$

它的全部相邻对矩正是 $-x^2/4$，其余非空矩为零。这 $n-1$ 个对包括所有跨窗口接缝。一个准备和一个完整输出态族的测量因此共同实现全部所需系数。

### 3.7 系数的组合求值

令 $J_n$ 为相邻物理位置发生 $10\leftrightarrow01$ 交换的无序合法词对数。把交换位置对收缩为一个标记的 $1$，即得到长度 $n-1$ 的合法词及其中一个指定占位。反向将该标记 $1$ 展开为 $10$ 与 $01$，恢复原无序词对。这是双射，故

$$
J_n=\sum_{v\in B_{n-1}}|v|=e_{n-1}.
\tag{3.14}
$$

一个正方形由其上方合法顶点以及该顶点两个待变化占位唯一确定，故正方形数为 $s_n$。每个不相邻位置的 Hamming 距离二词对，恰为一个这样的正方形的两条对角线之一。相邻交换词对有一个共同邻点，正方形对角线各有两个共同邻点。

计数有序长度二行走，以及将 $A^2$ 各条目平方，得到

$$
\begin{aligned}
\sum_b d_b^2&=2e+2J_n+8s_n,\\
\operatorname{Tr}(A^4)&=2e+4J_n+24s_n.
\end{aligned}
\tag{3.15}
$$

令 $A_2$ 指示 Hamming 距离恰为二，则

$$
\operatorname{Tr}(A_2^2)=2J_n+4s_n,
\qquad
\operatorname{Tr}(A^2A_2)=2J_n+8s_n.
\tag{3.16}
$$

均匀准备有 $B=A_2$。代入式（3.11），

$$
Q(A_2)=\frac{e-2s_n}{8M}+\frac{J_n}{32M}.
\tag{3.17}
$$

将一个相邻交换条目从 $1$ 改为 $3/4$，在式（3.12）中每个无序词对恰降低 $1/(32M)$，其两个有序条目均已计入。全部 $J_n$ 个相邻交换同时改变，其他二阶条目保持原值，所以全局最小系数为

$$
Q_n=\frac{e-2s_n}{8M},
\qquad
\Delta_n=\frac{J_n}{32M}=\frac{e_{n-1}}{32M}.
\tag{3.18}
$$

为证明 $s_n$ 的显式式，含 $k$ 个 $1$ 的合法词数为 $\binom{n-k+1}{k}$：对第 $j$ 个 $1$ 的位置减去 $j-1$，即与从 $n-k+1$ 个位置选 $k$ 个的集合双射。因此

$$
s_n=\sum_k\binom{k}{2}\binom{n-k+1}{k}.
$$

首段分解 $B_n=0B_{n-1}\mathbin{\dot\cup}10B_{n-2}$ 还给出

$$
s_0=s_1=0,
\qquad
s_n=s_{n-1}+s_{n-2}+e_{n-2}\quad(n\ge2).
\tag{3.19}
$$

将既有 $e_n$ 的表达式直接代入，可验证定义 1.5 中的 Fibonacci 表达式满足这些初值和递推，故它等于 $s_n$；再代入式（3.18）得到所列 $Q_n$ 的等价闭式。

这些恒等式是支撑优化系数的 Fibonacci cube 计数；立方体计数多项式与顶点占位的联系已有经典背景，见 [Klavžar–Mollard][KM]。它们不作为独立的量子取得新定理。

### 3.8 乘积准备类中的精确实验支配

用局部有限参考将 $\mathcal P_{\mathrm{prod}}$ 的每个局部输入纯化。其两个局部来源输出是规范化纯向量 $\chi_0,\chi_1$，内积为

$$
g=x-itm,
\qquad m=\langle Z\rangle,
\qquad |g|=\sqrt{x^2+(1-x^2)m^2}\ge x.
$$

平衡局部准备的两个输出 $\phi_0,\phi_1$ 的内积为 $x$。若 $g\ne0$，选规范化环境向量 $e_0,e_1$ 满足

$$
\langle e_0,e_1\rangle=\frac{x}{g}.
$$

因 $|x/g|\le1$，这些向量存在。赋值

$$
\phi_a\longmapsto\chi_a\otimes e_a\qquad(a=0,1)
$$

保持两态 Gram 矩阵，因此延为其张成空间上的等距映射。迹掉环境就得到一个与未知源无关的量子通道，将平衡输出逐一映到对应局部候选输出。若 $g=0$，必有 $x=0$，可将正交平衡对直接映到目标对。

将这些已知通道取张量积，便从平衡乘积输出族模拟任意乘积准备的整个输出族，同时适用于每个二进制词，因而适用于每个合法词。通过该通道拉回任意联合末端 POVM，就得到平衡准备上的一个合法联合 POVM。局部混态、被丢弃的局部纯化及独立辅助态均由此构造包含。

对随机准备，按每个种子作同样的拉回，再平均所得 POVM 效果。这仍是同一个平衡准备上的 POVM，并保持条件决策概率。所以 $\mathcal P_{\mathrm{prod}}$ 中每个协议都可由平衡准备加某个联合解码器模拟；反向包含显然，因为平衡准备属于该类。

这对每个整数合同证明了 (B) 的精确优化等式。它的小 $x$ 优化错误即固定 Gram 族

$$
G_{bc}=x^{h(b,c)}
$$

的充分优化错误。§3.2 说明它与 SRM 分数之差仅为 $O_n(x^6)$，§3.7 给出四阶系数 $Q_n+\Delta_n$。由 $\Delta_n>0$ 得到严格优化分离。

此模拟只用已知末端处理比较两个实验，没有增加未知源调用、逆源、复位或 controlled-$U$，也没有假定原合法态族是群轨道。

### 3.9 一致余项及显式可达分数

§§3.2–3.4 已证明，全局优化错误是零的固定邻域上的实解析偶函数。对乘积优化错误，§3.2 应用于其固定解析 Gram 族同样给出解析性，重新定相对称性给出偶性。试验分布实解析且为偶函数，在充分小的固定邻域严格为正，其 SRM 错误也实解析且为偶函数。

对试验准备，§3.6 给出最小化的 $B$；§3.7 因此给出与全类最优值相同的二阶和四阶错误系数。解析偶性排除五阶余项，证明式（2.5）的 $O_n(x^6)$ 可达错误。

具体 SRM 采用 [Eldar–Forney][EF] 定理 3 的正交化：令 $\Phi$ 的列为全部试验输出态，测量 $\Phi G^{-1/2}$ 的正交归一列，将正交补归给任一固定合法标签。这是一个共同接收器。正定性在充分小邻域内保持。它的精确可达成功率为

$$
P_{\mathrm{trial,SRM}}=\frac1M\sum_b\bigl((\sqrt G)_{bb}\bigr)^2.
$$

这一指定策略分数与全类优化值分别解释；它不等于有限正 $x$ 精确最优值的断言。

将邻域缩成解析区域内部的一个闭区间，全类优化错误、乘积优化错误和试验 SRM 错误的六阶导数在其上均有界。取一个大于这些界除以 $6!$ 的有限常数，由 Taylor 定理得到全部所述 $O_n(x^6)$ 不等式。这证明了有限 $\rho_n,K_n$ 的存在及其一致性。

这些常数界定的是在精确参考归约和紧性局部化之后的已全局优化值。任意原协议的错误都不小于全局最优值，所以相同下界与其准备、参考维数或随机化如何随合同变化无关。这里没有假设任意协议族都具有一致 Taylor 展开。由此证明 (A)，并完成 (B)、(C) 的余项要求。

本定理没有计算这些常数或数值邻域端点。严格分离仍是有限邻域上的严格结论：将 $K_n$ 增大到同时控制两类错误且取 $K_n>0$，则

$$
0<x\le\rho_n,\qquad x^2\le\frac{\Delta_n}{4K_n}
\quad\Longrightarrow\quad
\beta_n-\beta_n^{\mathrm{prod}}\ge\frac{\Delta_n}{2}x^4.
\tag{3.20}
$$

### 3.10 完整五标签、整数调用及端点

$n=3$ 的完整合法图有五个顶点、五条边、一个正方形和两个相邻交换词对。代入 $M=e=5$、$s_3=1$、$J_3=2$，得到 $Q_3=3/40$、$\Delta_3=1/80$，证明 (D)。这两个错误系数属于各自已优化类，五个原标签无一删去。

固定整数 $r\ge1$，沿 $q=L-r$，令 $a=\pi r/2$。原合同给出

$$
\begin{aligned}
x&=\sin(a/L),\\
x^2&=\frac{a^2}{L^2}-\frac{a^4}{3L^4}+O_r(L^{-6}),\\
x^4&=\frac{a^4}{L^4}+O_r(L^{-6}).
\end{aligned}
$$

代入 (A)，

$$
\varepsilon_n^\star
=\frac{C_na^2}{L^2}
+\left(Q_n-\frac{C_n}{3}\right)\frac{a^4}{L^4}
+O_{n,r}(L^{-6}).
$$

因为

$$
Q_n-\frac{C_n}{3}=-\frac{e_n+6s_n}{24M},
$$

得到 (E) 第一式；将 $x$ 代入 $\Delta_nx^4+O_n(x^6)$ 得到第二式。$e_n>0$、$s_n\ge0$ 说明第一式的 $L^{-4}$ 系数对每个 $n=3N$ 严格负且非零，是所述固定 $r$ 整数族上 $L^{-2}$ 后的下一非零项。充分大 $L$ 有 $0<q<L$，整个族分别满足原设备合同。

$q=0$ 时输出与来源无关，均匀 Bayes 成功率为 $1/M$，猜词达到该值。$q=L$ 时平衡输出族正交，两个准备类均可成功一。这两个端点不使用奇异 Gram 矩阵的逆。渐近定理用于 $q=L$ 的邻域，不断言整个 $0<q<L$ 都有同一公式。由此证明 (F) 的端点部分。

### 3.11 整条服务对应及任务相对的白盒质量

由解码合法词 $\widehat b$ 安装确定索引表 $j\mapsto W_j(\widehat b)$。指针版本保留初始 $a=1$，索引读不改 $a$；$\mathrm{Next}$ 恰在 $a\le N$ 时合法，返回 $W_a$ 后递增 $a$。全部五标签、尾部 null 和每个接缝均保留，没有 $\mathrm{End}$。

若 $\widehat b=b$，对每条有限混合查询历史作长度归纳，始终保持回复、合法域和指针更新一致：初始词及指针相同；索引读给相同窗口且不改指针；$\mathrm{Next}$ 在两边有同一合法域，合法时给相同窗口并同步递增。该归纳包括重复索引及依此前回复自适应的查询。若 $\widehat b\ne b$，至少一个窗口不同，一次对应索引查询见证服务失败。因此这种安装精确保持整词成功事件。

反向，取任意满足定义 1.8 有限终止合同的安装协议。安装后执行固定有限索引扫描 $1,\ldots,N$ 并解码回复，将非法回复串归给一个固定合法词。全部有限历史上的整条服务正确必推出该扫描恢复 $b$。扫描无源调用、有限终止，属于末端后处理，故诱导一个原协议类允许的有限标签末端 POVM。对每个真实来源，其成功率至少为原整条服务成功率。

这两个构造保持准备类。正向逐源保分，反向逐源不减分，取 Bayes 上确界，就得到完整类和 $\mathcal P_{\mathrm{prod}}$ 各自的优化整词分数与服务分数相等。指针接口有同一索引扫描，正向归纳又保持其全部混合历史更新，因而同样成立。这是 [Recovery][Recovery] 推论 4.3 的服务归约应用于所确定的新优化系数；扫描不构成任意服务全部历史正确性的有限认证。完成 (F)。

因此，对同一指定的完整五窗服务质量任务，限制准备会造成严格的四阶平均整条服务损失，即使解码器已经充分优化。这个解释不推出逐来源支配、minimax 结论或实际训练网络的收益。原生 FIB 树、KBonacci 来源及真实机器学习系统仍各需单独证明对象、来源、读出、合法操作和更新的对应。定理 2.1 证毕。

## 4. 资源假设与适用边界

**假设 4.1（准备、参考与共同实现）。** 式（2.4）的准备仅依赖公开的 $n,L,q$，不以未知真实标签为条件；其关联覆盖跨窗物理相邻对。显式可达协议采用系统态 $|\chi_x\rangle$，恰好作 $q$ 次不中断普通完整系统调用，再用一个任意联合末端正交测量。可达构造无需输入参考，而全类下界仍覆盖全部允许的有限参考。

该准备在正 $x$ 时一般不是乘积纯态：单位置矩为零，物理相邻对矩为 $-x^2/4$。定理给出具名限制类的分离，不是对每种可能的纠缠资源定义都给出普适下界。最优压缩分布的唯一性也不排除交换相位及等价参考实现。

**假设 4.2（公开知识、校准、综合与读出价格）。** 已知因子标签、带符号基准、理想校准、无噪声和无记忆承诺仍是必要假设。准备综合、参考、校准、集体测量、控制和读出的价格均未求出；新准备的价格不能认作平衡准备原有的 $n$ 个 Hadamard 门。公开模型上的矩阵平方根及逆平方根是测量描述，不是未知逆源调用。显式协议未取得其他标签样本，未使用未知 controlled-$U$、复位、重新抽样或附加建议。

**假设 4.3（存储与复杂度）。** 显式服务安装保留 $n$ 个经典位，指针版本再保留一个有限指针。这些是充分保留资源，不是最小存储定理。没有高效准备综合、多项式时间算法、LOCC 实现或净硬件成本优势的结论。若另限局部测量或 LOCC，任意联合测量类的可达性不能自动传递。

**假设 4.4（规模、目标和来源限制）。** 全部余项常数针对固定 $n$，虽独立于协议和有限参考维数，却不保证对增长的 $n$ 一致。一般内部整数 $q$ 的精确全类 Bayes 值、精确 minimax 值、minimax 下一阶项、优化 $x^6$ 系数及远离正交端点的精确最优准备不由本定理确定。平衡准备类的每合同精确优化等式不替代全准备类的有限参数目标。

## 5. 数学供应、增量归属与未解问题

**数学引文 5.1（既有供应的精确边界）。** 下表仅标示相关步骤的已有来源，不将固定态族检测、通用优化工具或组合计数另列为新增定理。

| 来源 | 使用范围与供应边界 |
| --- | --- |
| [Recovery][Recovery] 定义 1.2–1.4、定理 2.1(C)、§3.4、定义 4.2 和推论 4.3；[Minimax][Minimax] 定义 1.2–1.6、定理 2.1 和开放问题 5.3–5.4 | 不变源、一块式协议、均匀完整合法域、既有 Bayes 首项、minimax 首项结算、SRM 及服务合同。两卷的高阶准备缺口仍明确；其结论不供应本卷的四阶全准备优化。 |
| [Yonina C. Eldar、G. David Forney, Jr.，*On Quantum Detection and the Square-Root Measurement*][EF]，定理 3 | `literature-attested`：成熟正交化 $\Phi G^{-1/2}$。几何均匀态族的特殊最小错误最优性不应用到完整合法词族。SRM、平方根演算和正交化不作为本卷新内容。 |
| [Tanmay Singal、Sibasish Ghosh，*Minimum Error Discrimination for an Ensemble of Linearly Independent Pure States*][SG]，定理 3.2、4.1–4.2 及 §4.2 末尾 | `literature-attested`：线性无关纯态族的最小错误检测及解析机器；其加权 Gram 矩阵对应本卷 $G/M$。它供应固定态族工具，不供应张量符号输入优化；端点唯一性、全单纯形局部化、矩最小化和源特定系数由本卷证明承担。 |
| [Jon Tyson，*Error rates of Belavkin weighted quantum measurements and a converse to Holevo’s asymptotic optimality theorem*][Tyson]，版本 v1、§§1.2–1.4、2.3 | `literature-attested`：带权测量及固定态族、固定先验的近正交渐近边界。它不替代全准备类的四阶最优值。 |
| [Sandi Klavžar、Michel Mollard，*Daisy cubes and distance cube polynomial*][KM] | `literature-attested`：Fibonacci 合法词图的立方体计数背景。正方形数及组合账目属于支撑计算，该文不供应量子取得分数。 |
| [EquiprobablePgmActiveSetRefutation][ActiveSet] | 不同的三个混态 active-set 反例及半正定对偶证书；不供应完整合法纯态族的准备优化。该源码引用不构成本卷的 Lean 编译或 kernel 核验。 |
| mathlib 固定提交 [`db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d) 的 [HermitianFunctionalCalculus][MathCFC]、[PosDef][MathPosDef]、[Calculus.Implicit][MathImplicit] | 通用谱演算、正定性和隐函数抽象；不是本卷定理的现有形式化。尤其不将该隐函数文件视为整个解析优化论证的已编译实现。 |
| [StageScalarAddressCertificate][Stage]；[金字塔基础公式卷][Pyramid] §§二、六、十一、十四及其 [Wainwright–Jordan][WJ]、[Drton–Sullivant][Drton]、[Shannon][Shannon]、[Sullivant][Sullivant] 文献条目 | 前者处理原生有序树、地址观察及已知标量阶段的共同证书；后者处理五模式概率律、同源原生接续以及另需明确附件的量子表示。它们不提供本卷张量符号普通调用的来源对应、准备优化值或资源价格。原生树认证、经典概率拼接、受控源资源及本卷一块式量子实验保持各自合同。 |

**数学引文 5.2（本卷综合推导的归属）。** 定理 2.1 的全准备四阶系数、压缩最优分布的局部唯一性、同时实现的相邻对矩、充分优化解码后的乘积准备类分离及原整数族的非零下一阶修正为 `repo-derived` 普通综合推导。其增量相对于所列固定来源的明确缺口，覆盖每个固定 $B_{3N}$，完整 $B_3$ 保留全部五标签。已有 SRM、固定态族解析方法、通用紧性、隐函数理论、组合恒等式及服务归约不独立主张新知识。所列定向供应不是全世界文献的穷尽检索，不证明世界优先性；普通证明也不等于物理实现、实际网络增益或持续研究目标的整体认证。

**开放问题 5.3（完整有限参数与更高阶优化）。** 一般内部整数 $0<q<L$ 上完整 $B_{3N}$ 的精确全类 Bayes 和 minimax 值仍未确定，远离正交端点的完整 $B_3$ 也未由本定理求解。全类四阶优化不确定 minimax 四阶项；显式试验分布只达到二阶及四阶系数，不确定精确正 $x$ 最优准备或优化 $x^6$ 系数。需要进一步的全局有限参数分析或相应高阶优化，不能以指定接收器分数替代。

**开放问题 5.4（增长规模与实际任务对应）。** 本定理未给出 $\rho_n,K_n$ 的数值，也未控制增长 $n$ 的一致余项、全部局部或 LOCC 类最优值、校准误差、噪声、记忆源及完整物理资源成本。原生 FIB 树、KBonacci 来源和训练网络与本量子承诺族的对象、来源、读出、合法域、更新及成本对应仍需独立证明；同名五标签或相同数值不是这种对应。

[Recovery]: https://github.com/the-omega-institute/trureturing/blob/f833660337ac6264fc6f742d4b2114f25b4df6c8/docs/develop/theory/FIB_ATOM_WHITEBOX_CORRELATED_WORD_RECOVERY.md
[Minimax]: https://github.com/the-omega-institute/trureturing/blob/f833660337ac6264fc6f742d4b2114f25b4df6c8/docs/develop/theory/FIB_ATOM_WHITEBOX_LEGAL_EDGE_MINIMAX.md
[EF]: https://arxiv.org/abs/quant-ph/0005132
[SG]: https://arxiv.org/abs/1407.5389
[Tyson]: https://arxiv.org/abs/0907.1884v1
[KM]: https://arxiv.org/abs/1705.08674
[ActiveSet]: https://github.com/the-omega-institute/trureturing/blob/499d30d2085d31ecc46eee400f490c70e2434603/D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.lean
[MathCFC]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean
[MathPosDef]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Matrix/PosDef.lean
[MathImplicit]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Implicit.lean
[Stage]: https://github.com/the-omega-institute/trureturing/blob/db2dc3b9bd2ef965f2b91635b81e9e1f4fac9e1b/D5/S3/Arith/FibonacciAtomic/StageScalarAddressCertificate.lean
[Pyramid]: https://github.com/the-omega-institute/trureturing/blob/499d30d2085d31ecc46eee400f490c70e2434603/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md
[WJ]: https://github.com/the-omega-institute/trureturing/blob/499d30d2085d31ecc46eee400f490c70e2434603/Library/Estimation/wainwrightjordan2008graphical.md
[Drton]: https://github.com/the-omega-institute/trureturing/blob/499d30d2085d31ecc46eee400f490c70e2434603/Library/Estimation/drtonsullivant2007algebraic.md
[Shannon]: https://github.com/the-omega-institute/trureturing/blob/499d30d2085d31ecc46eee400f490c70e2434603/Library/Estimation/shannon1948communication.md
[Sullivant]: https://github.com/the-omega-institute/trureturing/blob/499d30d2085d31ecc46eee400f490c70e2434603/Library/Estimation/sullivant2006toricfiber.md

## 追加锚（本行以下为增补区）
