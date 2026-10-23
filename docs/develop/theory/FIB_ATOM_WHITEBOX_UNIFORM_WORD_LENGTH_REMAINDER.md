# FIB 完整张量符号源：词长一致的 minimax 余项与联合端点极限

## 1. 完整来源、损失与既有数学供应

**定义 1.1（完整合法词与固定源）。** 固定整数 $N,L\ge1$，令 $n=3N$、$\theta=\pi/(4L)$，系统为 $\mathcal K=(\mathbb C^2)^{\otimes n}$。因子标签、带符号的计算基及 Pauli 标准均已知。置

$$
\begin{aligned}
B_n&=\{b\in\{0,1\}^n:b_i b_{i+1}=0\quad(1\le i<n)\},\\
s_i(b)&=(-1)^{b_i},\qquad
U_b=\bigotimes_{i=1}^n e^{i s_i(b)\theta Z},\\
\Lambda_b(\rho)&=U_b\rho U_b^\dagger.
\end{aligned}
$$

一个未知 $b\in B_n$ 选定一次，整个实验始终使用这个理想、无噪声、无记忆、已校准的源。一次普通调用作用于整个系统，对参考和工作空间作用为恒等。全零词、尾部 $000$ 窗及所有接缝条件全部保留；尤其 $b_{3j}b_{3j+1}=0$ 不因分窗而省去。没有额外标签建议，也没有 $\mathrm{End}$ 标签。

**定义 1.2（一块式协议与两个优化目标）。** 整数 $q$ 满足 $0\le q\le L$。协议 $\Pi$ 准备任意与 $b$ 无关的输入密度态和任意有限维参考，在同一系统上连续作恰好 $q$ 次普通完整系统调用，最后作一次共同联合 POVM，经有限末端处理输出 $\widehat b\in B_n$。允许与源无关的随机化及工作空间初值。仅作用于参考的中间操作与源调用交换，可推迟到末端。调用间不操作系统，不允许逆源、源复位、重新抽取标签、未知 controlled-$U$ 或源相关建议。

记最终条件概率为 $P_\Pi(c\mid b)$，整词错误为 $\eta_b(\Pi)=1-P_\Pi(b\mid b)$。令 $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$，$M_n=|B_n|=F_{n+2}$，并定义

$$
\begin{aligned}
\varepsilon_n^\star(L,q)
 &=\inf_\Pi\frac1{M_n}\sum_{b\in B_n}\eta_b(\Pi),
&\beta_n(L,q)&=1-\varepsilon_n^\star(L,q),\\
\delta_n(L,q)&=\inf_\Pi\max_{b\in B_n}\eta_b(\Pi),
&\beta_n^{\mathrm{mm}}(L,q)&=1-\delta_n(L,q),\\
x&=\cos\frac{\pi q}{2L}=\cos(2q\theta).
\end{aligned}
\tag{1.1}
$$

Bayes 目标采用完整 $B_n$ 上的均匀先验；minimax 目标取完整来源域上的最大整词错误。所有下确界均取遍上述整个协议类，准备、参考维数、随机化及测量可随公开整数合同变化。非法答案可归给一个固定合法词。$x$ 描述一次准备后的连续酉迭代，不描述重新准备的 $q$ 份样本。

**定义 1.3（合法边负载）。** $h(b,c)$ 为 Hamming 距离。完整合法词图 $\Gamma_n$ 的顶点为 $B_n$，当且仅当 $h(b,c)=1$ 时有边。记邻接矩阵为 $A$、无向边数为 $e_n$、度数为 $d_b$。每条边选取份额

$$
0\le a_{c\leftarrow b}\le1,\qquad
a_{c\leftarrow b}+a_{b\leftarrow c}=1.
$$

置

$$
L_b(a)=\sum_{c\sim b}a_{c\leftarrow b}^2,
\qquad \kappa_n=\min_a\max_b L_b(a),
\qquad C_n=\frac{e_n}{2M_n}.
\tag{1.2}
$$

有限闭区间乘积的紧性给出最小化分配的存在。零份额与份额一均合法。半份额分配给出 $\kappa_n\le n/4$；度数求和给出 $C_n\le n/4$。这些公开图变量不随未知真实标签另行选择。对一般整数 $n\ge0$ 使用同一合法词图定义，仅作为图论辅助；实际来源一直满足 $n=3N\ge3$。

**数学引文 1.4（所用有限公式与增长律）。** [Minimax][Minimax] 定义 1.2–1.5、定理 2.1(A) 及 §§3.2–3.4 供应同一来源、全协议类下界和旋转接收器；[Recovery][Recovery] 定理 2.1(A)–(C)、§§3.2–3.5 供应全协议类 Bayes 下界、SRM 及有限上界。具体为

$$
\begin{aligned}
\delta_n&\ge v_n(x)
 :=\frac{4\kappa_nx^2}{(1+\sqrt{1+4\kappa_nx})^2},\\
\varepsilon_n^\star&\ge\ell_n(x)
 :=\frac{4C_nx^2}{(1+\sqrt{1+nx})^2},\\
\varepsilon_n^\star&\le1-P_{\mathrm{SRM}}\le u_n(x)
 :=\frac{4C_nx^2+(1+x^2)^n-1-nx^2}
 {[1+\sqrt{2-(1+x)^n}]^2}\quad\bigl((1+x)^n<2\bigr),\\
C_n&=\frac{nF_{n+1}+2(n+1)F_n}{10F_{n+2}}.
\end{aligned}
\tag{1.3}
$$

[Growth][Growth] 定理 5.2、式（5.3）、定理 7.3 及推论 7.4 供应

$$
\begin{aligned}
c_\star&:=\lim_{n\to\infty}\frac{\kappa_n}{n},
&c_\star n&\le\kappa_n\le c_\star(n+1),\\
c_\star&\ge\frac{1800}{12559},
&\frac{C_n}{n}&\longrightarrow c_B:=\frac{5-\sqrt5}{20},\\
c_\star-c_B&>\frac{51}{10000}.
\end{aligned}
\tag{1.4}
$$

这些图系数、Fibonacci 计数、增长常数及有限辨识界均沿用所引结论。所需新估计是旋转接收器对词长一致的逐列余项，以及由它得到的源误差联合极限；Bayes 一致界直接由式（1.3）的既有有限夹逼推出。

**假设 1.5（能力与价格参数）。** 可达性使用理想共同准备和任意联合末端测量。整数调用数 $q$ 与准备、源取得及校准、测量综合、经典计算、保留存储和物理实现的价格分别计量；这些价格之间不预设等式或支配关系。式（1.1）只优化错误概率，不优化价格，也不对这些价格赋值或给出增长阶。有限公开矩阵的存在不附带高效综合或高效计算假设。

## 2. 词长一致的整词误差界

**定理 2.1（一致 minimax 余项与 Bayes 比较）。** 对每个定义 1.1–1.2 的原整数合同，若 $0\le nx\le1/4$，则

$$
\boxed{
\kappa_nx^2-\frac18n^2x^3
\le\delta_n(L,q)
\le\kappa_nx^2+\frac{21}{4}n^2x^3,
\qquad
|\delta_n(L,q)-\kappa_nx^2|\le6n^2x^3.
}
\tag{2.1}
$$

下界对任意共同准备、任意有限参考、源无关随机化和共同联合 POVM 成立。上界由一次 $|+\rangle^{\otimes n}$ 准备、恰好 $q$ 次普通调用及一个服务全部原标签的共同末端接收器达到；不要求输入参考，不对图份额加严格正性条件。

同一范围内，既有 Bayes 有限夹逼给出

$$
\boxed{
C_nx^2-\frac18n^2x^3
\le\varepsilon_n^\star(L,q)
\le C_nx^2+\frac34n^2x^3.
}
\tag{2.2}
$$

令 $g_n=\beta_n-\beta_n^{\mathrm{mm}}=\delta_n-\varepsilon_n^\star$，则

$$
-\frac78n^2x^3
\le g_n-(\kappa_n-C_n)x^2
\le\frac{43}{8}n^2x^3.
\tag{2.3}
$$

因而 Bayes 绝对余项至多 $\frac34n^2x^3$，分离绝对余项至多 $6n^2x^3$；特别也满足较宽的常数 $3$ 与 $9$。Bayes 上界由未旋转 SRM 达到，minimax 上界由图最小化分配的旋转接收器达到。这里的“达到上界”是接收器错误不超过该界，不断言有限参数精确最优，也不把两个不同目标的策略视为同一优化器。

在 $x=0$，即 $q=L$ 时，两种最优错误和 $g_n$ 恰为零。

## 3. 定理 2.1 的逐列证明

### 3.1 合法词壳层与 Gram 矩阵

**证明（逐列计数）。** 取一个公开的最小化分配 $a^{\mathrm{opt}}$。以下 $\mathbf e_b$ 表示以 $B_n$ 为坐标集的单位向量，矩阵行对应输出标签，列对应真实标签。范数为 Euclidean 范数及其诱导算子范数。置

$$
D_{cb}=a^{\mathrm{opt}}_{c\leftarrow b}\,\mathbf1_{\{c\sim b\}},
\qquad K=D-\frac A2.
\tag{3.1}
$$

于是 $D+D^T=A$、$K^T=-K$，而且

$$
\|D\mathbf e_b\|^2=L_b(a^{\mathrm{opt}})\le\kappa_n\le\frac n4,
\quad \|K\|\le\frac n2,
\quad \|K\mathbf e_b\|\le\frac{\sqrt n}{2},
\quad \|A\mathbf e_b\|\le\sqrt n.
\tag{3.2}
$$

后面三个界来自 $|K_{cb}|\le1/2$、各度数至多为 $n$，以及绝对行和、列和的算子范数界。零份额不影响这些估计。

令 $\phi_b=U_b^q|+\rangle^{\otimes n}$，$\Phi$ 以 $\phi_b$ 为列。[Recovery][Recovery] §3.4 的乘积内积公式给出

$$
G=\Phi^\dagger\Phi,\qquad G_{bc}=x^{h(b,c)},\qquad G_{bb}=1.
\tag{3.3}
$$

在 $x=0$ 时仍按对角值一解释。置

$$
y=nx\le\frac14,\qquad z=nx^2\le\frac1{16},\qquad
H=G-I,\qquad E=H-xA.
$$

从任一固定合法词出发，距离 $j$ 的合法词至多有 $\binom nj$ 个。以完整二元立方体作计数上界不改变实际合法来源域。由 $\binom nj\le n^j/j!$ 及 $j!\ge2$（$j\ge2$），同时得到

$$
\begin{aligned}
\|H\|&\le(1+x)^n-1
 \le\frac y{1-y}\le2nx\le\frac12,\\
\|H\mathbf e_b\|^2&\le(1+x^2)^n-1
 \le\frac z{1-z}\le2nx^2,\\
\|E\mathbf e_b\|^2&\le\sum_{j=2}^n\binom njx^{2j}
 \le\frac{z^2}{2(1-z)}\le n^2x^4.
\end{aligned}
\tag{3.4}
$$

这里 $\|H\|$ 的第一步使用实对称矩阵的绝对行和界。因此 $G\ge I/2$，逆平方根在整个所述范围内存在。实际 $n\ge3$，故此范围也排除了 $q=0$。

### 3.2 平方根的精确列余项

令 $S=\sqrt G$。对 $t>-1$ 的精确恒等式为

$$
\sqrt{1+t}-1-\frac t2
=-\frac{t^2}{2(1+\sqrt{1+t})^2}.
$$

在 Hermitian 谱演算中，它给出

$$
R_S:=S-I-\frac x2A
=\frac E2-\frac12H^2(I+S)^{-2}.
\tag{3.5}
$$

后项各因子交换，且 $\|(I+S)^{-2}\|\le1$。因此式（3.4）逐列给出

$$
\begin{aligned}
\|R_S\mathbf e_b\|
&\le\frac12\|E\mathbf e_b\|
 +\frac12\|H\|\,\|H\mathbf e_b\|\\
&\le\frac n2x^2+\sqrt2\,n^{3/2}x^2
\le2n^{3/2}x^2.
\end{aligned}
\tag{3.6}
$$

最后一步只用 $n\ge1$ 与 $\sqrt2+1/2<2$。关键量是 $\|H\|\,\|H\mathbf e_b\|$；把它替换成 $\|H\|^2$ 会失去所需的列尺度。

### 3.3 正交旋转的列余项与共同测量

令 $Q=e^{xK}$。因 $K^T=-K$，所有 $e^{uK}$ 都正交。积分余项精确满足

$$
\begin{aligned}
Q-I&=\int_0^x e^{uK}K\,du,\\
Q-I-xK&=\int_0^x(x-u)e^{uK}K^2\,du.
\end{aligned}
$$

结合式（3.2），有

$$
\|Q-I\|\le x\|K\|,\qquad
\|(Q-I-xK)\mathbf e_b\|
\le\frac{x^2}{2}\|K\|\,\|K\mathbf e_b\|
\le\frac18n^{3/2}x^2.
\tag{3.7}
$$

置 $T=QS$，利用 $D=K+A/2$ 作精确分解

$$
R_T:=T-I-xD
=QR_S+(Q-I-xK)+\frac x2(Q-I)A.
$$

于是对全部 $b$ 同时成立

$$
\boxed{
\|R_T\mathbf e_b\|
\le\left(2+\frac18+\frac14\right)n^{3/2}x^2
=\frac{19}{8}n^{3/2}x^2
\le3n^{3/2}x^2.
}
\tag{3.8}
$$

此处末项使用 $\frac x2\|(Q-I)A\mathbf e_b\|\le n^{3/2}x^2/4$。

现在沿用 [Minimax][Minimax] §3.4、式（3.8）–（3.9）的共同测量列

$$
W=\Phi G^{-1/2}e^{-xK},\qquad W^\dagger W=I,
\qquad W^\dagger\Phi=e^{xK}\sqrt G=T.
\tag{3.9}
$$

对 $W$ 各列作一维正交投影，将其共同正交补并入一个固定合法标签，即得一个完整 POVM。所有候选输出均在这些列的张成空间，补全不影响任何来源的概率。$G^{-1/2}$ 是公开候选矩阵的函数；测量定义不使用未知源的逆调用或额外候选样本。相同准备和相同末端测量同时适用于全部原标签。

### 3.4 从列振幅到每个来源的错误

由 $T^\dagger T=G$、$G_{bb}=1$，列 $b$ 的总概率为一。令 $P_b^\perp=I-\mathbf e_b\mathbf e_b^\dagger$，$r_b=R_T\mathbf e_b$，则该旋转接收器的错误精确为

$$
\eta_b^{\mathrm{rot}}
=\|P_b^\perp T\mathbf e_b\|^2
=\|xD\mathbf e_b+P_b^\perp r_b\|^2.
$$

所以式（3.2）、（3.8）给出

$$
\begin{aligned}
|\eta_b^{\mathrm{rot}}-L_b(a^{\mathrm{opt}})x^2|
&\le2x\|D\mathbf e_b\|\,\|r_b\|+\|r_b\|^2\\
&\le3n^2x^3+9n^3x^4
\le\frac{21}{4}n^2x^3.
\end{aligned}
\tag{3.10}
$$

平方余项也由 $nx\le1/4$ 吸收；仅控制交叉项不足以推出该界。最大负载为 $\kappa_n$，取全部来源的最大值便证明式（2.1）的可达上界。

同一平方根列估计还控制未旋转 SRM。取 $D=A/2$、$K=0$，则

$$
\begin{aligned}
\eta_b^{\mathrm{SRM}}
 &=\left\|\frac x2A\mathbf e_b+P_b^\perp R_S\mathbf e_b\right\|^2,\\
\left|\eta_b^{\mathrm{SRM}}-\frac{d_b}{4}x^2\right|
 &\le2n^2x^3+4n^3x^4\le3n^2x^3.
\end{aligned}
\tag{3.11}
$$

这是逐来源界。其平均界可改用既有有限夹逼取得更小常数，见 §3.6；两种界分别用于平均误差和最坏来源比较。

### 3.5 全协议类下界的统一余项

式（1.3）的 minimax 下界已包含所有允许的准备、有限参考和随机化。其量词来自 [Minimax][Minimax] §§3.2–3.3 的同时决策约束：共同混态输入可在有限参考上纯化，POVM 可等距嵌入正交结果空间；对每条合法边，固定源的相对酉给出 $\operatorname{Re}\langle\psi_b,\psi_c\rangle=x$，从而同一决策律满足

$$
x\le\sqrt{P(c\mid b)}+\sqrt{P(b\mid c)}+\sqrt{\eta_b\eta_c}.
\tag{3.12}
$$

源无关随机种子的平均保持此式，因为 $\mathbb E\sqrt P\le\sqrt{\mathbb EP}$，且 $\mathbb E\sqrt{\eta_b\eta_c}\le\sqrt{\mathbb E\eta_b\,\mathbb E\eta_c}$。此后使用最终平均条件概率，不交换种子平均与逐源最大值。若最大错误 $m<x$，则每条边的两向错误振幅之和至少为 $x-m>0$；按这个正和归一得到可行图份额，故 $m\ge\kappa_n(x-m)^2$。零振幅的分子允许为零，没有除以个别份额、准备权重或对偶质量。$m\ge x$ 的情形也满足 $m\ge v_n(x)$。这正是所引全协议下界的适用范围。

只需对这个既有有限表达式作统一估计。令 $v=v_n(x)$。对 $x>0$，其较小根满足

$$
v=\kappa_n(x-v)^2,\qquad
0\le v\le\kappa_nx^2.
$$

因而

$$
0\le\kappa_nx^2-v
=2\kappa_nxv-\kappa_nv^2
\le2\kappa_n^2x^3
\le\frac18n^2x^3.
\tag{3.13}
$$

对所有协议取下确界得式（2.1）的下界。不假定最优准备或最优 POVM 存在或连续，也不要求参考维数有统一上限。

### 3.6 既有 Bayes 夹逼的统一推论与零端点

[Recovery][Recovery] §§3.2–3.3 的纯化与正交结果迹估计给出 $2e_nx\le2\sqrt{2e_nE_0}+nE_0$，其中 $E_0=\sum_b\eta_b$。其结果即式（1.3）的 $\ell_n$；对每个源无关种子该下界相同，平均后仍成立。故它优化的是整个原协议类。

对 $y=nx\ge0$，$\sqrt{1+y}\le1+y/2$，故 $(1+\sqrt{1+y})^2=2+y+2\sqrt{1+y}\le4+2y$，所以

$$
\ell_n(x)\ge\frac{C_nx^2}{1+y/2}
\ge C_nx^2\left(1-\frac y2\right)
\ge C_nx^2-\frac18n^2x^3.
\tag{3.14}
$$

为使用既有 SRM 上界，置 $\rho=(1+x)^n-1$、$\zeta=(1+x^2)^n-1-nx^2$。式（3.4）的计数给出

$$
0\le\rho\le\frac y{1-y}\le\frac13,
\qquad 0\le\zeta\le n^2x^4.
$$

因而式（1.3）的适用条件成立，而且

$$
\frac4{(1+\sqrt{1-\rho})^2}
\le\frac1{1-\rho}
\le\frac{1-y}{1-2y}
\le1+2y.
$$

最后一步使用 $y\le1/4$。分母 $(1+\sqrt{1-\rho})^2\ge1$，故

$$
\begin{aligned}
u_n(x)&\le C_nx^2(1+2y)+n^2x^4\\
&\le C_nx^2+\left(\frac12+x\right)n^2x^3
\le C_nx^2+\frac34n^2x^3.
\end{aligned}
\tag{3.15}
$$

这里仅用 $C_n\le n/4$ 与 $x\le1/4$。式（3.14）–（3.15）是 [Recovery][Recovery] 定理 2.1(A),(B) 有限公式的直接推论，不依赖固定词长的高阶最优准备展开。它们证明式（2.2）；将其与式（2.1）的两侧界相减，证明式（2.3）。

若 $x=0$，则 $q=L$、$G=I$、$S=Q=I$。上述两个共同接收器精确辨识全部标签，两种最优错误都为零，所有不含除以 $x$ 的界仍成立。定理 2.1 得证。

## 4. 同一合法参数列上的联合极限

**定理 4.1（增长词长的端点联合极限）。** 设 $(N_j,L_j,q_j)$ 是任意原整数合同列，令 $n_j=3N_j$、$x_j=\cos(\pi q_j/(2L_j))$。若

$$
n_j\longrightarrow\infty,\qquad x_j>0,\qquad n_jx_j\longrightarrow0,
\tag{4.1}
$$

则沿这同一参数列，

$$
\begin{aligned}
\frac{\delta_n(L,q)}{nx^2}&\longrightarrow c_\star,\\
\frac{\varepsilon_n^\star(L,q)}{nx^2}&\longrightarrow c_B,\\
\frac{\beta_n(L,q)-\beta_n^{\mathrm{mm}}(L,q)}{nx^2}
 &\longrightarrow c_\star-c_B>\frac{51}{10000},\\
\frac{\delta_n(L,q)}{\varepsilon_n^\star(L,q)}
 &\longrightarrow\frac{c_\star}{c_B}
 =\frac{20c_\star}{5-\sqrt5}>1.
\end{aligned}
\tag{4.2}
$$

**证明。** 所述列最终满足 $nx\le1/4$。由定理 2.1 与既有式（1.4），逐项有

$$
\begin{aligned}
\left|\frac{\delta_n}{nx^2}-c_\star\right|
 &\le6nx+\frac{c_\star}{n},\\
\left|\frac{\varepsilon_n^\star}{nx^2}-c_B\right|
 &\le\frac34nx+\left|\frac{C_n}{n}-c_B\right|,\\
\left|\frac{\beta_n-\beta_n^{\mathrm{mm}}}{nx^2}-(c_\star-c_B)\right|
 &\le6nx+\frac{c_\star}{n}+\left|\frac{C_n}{n}-c_B\right|.
\end{aligned}
\tag{4.3}
$$

每个右侧沿同一列趋于零，没有交换固定词长极限与词长极限。$c_B>0$，且 $x>0$ 时式（1.3）的 Bayes 下界严格为正，故最后一个比值有定义并趋于所示值。正间隔使用 [Growth][Growth] 定理 7.3、推论 7.4 的解析界：$1800/12559>1433/10000$，而 $\sqrt5>559/250$ 给出 $c_B<1382/10000$。

另有 $nx^2=(nx)^2/n\to0$，所以两个最优成功率都趋于一，绝对成功率差趋于零；式（4.2）的正间隔位于错误尺度。这里分离的是两个优化值，未要求一个协议同时优化两种损失。若 $nx\to\lambda>0$，式（4.3）的余项不再趋于零，因而该证明不决定此尺度的极限。证毕。

**推论 4.2（两个共同接收器的实际误差尺度）。** 在定理 4.1 的同一参数列上，令

$$
m_{\mathrm{rot}}=\max_b\eta_b^{\mathrm{rot}},\qquad
m_{\mathrm{SRM}}=\max_b\eta_b^{\mathrm{SRM}},\qquad
\bar\eta_{\mathrm{SRM}}=\frac1{M_n}\sum_b\eta_b^{\mathrm{SRM}}.
$$

则

$$
\begin{aligned}
\frac{m_{\mathrm{rot}}}{nx^2}&\longrightarrow c_\star,
&\frac{m_{\mathrm{rot}}}{\delta_n}&\longrightarrow1,\\
\frac{m_{\mathrm{SRM}}}{nx^2}&\longrightarrow\frac14,
&\frac{\bar\eta_{\mathrm{SRM}}}{\varepsilon_n^\star}&\longrightarrow1,\\
\frac{\delta_n}{m_{\mathrm{SRM}}}&\longrightarrow4c_\star.
\end{aligned}
\tag{4.4}
$$

**证明。** 式（3.10）逐列成立且最大图负载等于 $\kappa_n$，故 $|m_{\mathrm{rot}}-\kappa_nx^2|\le(21/4)n^2x^3$。式（3.11）逐列成立，最大度数为全零词的 $n$，故 $|m_{\mathrm{SRM}}-(n/4)x^2|\le3n^2x^3$。对 SRM 平均错误，既有夹逼 $\ell_n\le\varepsilon_n^\star\le\bar\eta_{\mathrm{SRM}}\le u_n$ 与式（3.14）–（3.15）给出 $\bar\eta_{\mathrm{SRM}}/(nx^2)\to c_B$。再用定理 4.1 及 $c_\star,c_B>0$ 即得全部比值。证毕。

此推论只比较两个明确构造的共同接收器。[Minimax][Minimax] 定理 2.1(D) 关于每个 Bayes 首项最优族的逐源刚性以固定 $n$ 为前提；上述优化值与指定接收器的联合界没有把它推广到任意增长词长的协议族。

**命题 4.3（原整数合同的等价尺度与非空实例）。** 置 $r=L-q$。对任意原整数合同，

$$
\frac rL\le x=\sin\frac{\pi r}{2L}\le\frac{\pi r}{2L}.
\tag{4.5}
$$

因此在 $n=3N\to\infty$、$x>0$ 的列上，$nx\to0$ 等价于 $nr/L\to0$，且必有 $L/n\to\infty$。在该区域内，

$$
\begin{aligned}
\delta_n(L,q)&=\left(\frac{\pi^2c_\star}{4}+o(1)\right)\frac{nr^2}{L^2},\\
\varepsilon_n^\star(L,q)&=\left(\frac{\pi^2c_B}{4}+o(1)\right)\frac{nr^2}{L^2},\\
\beta_n-\beta_n^{\mathrm{mm}}
 &=\left(\frac{\pi^2(c_\star-c_B)}4+o(1)\right)\frac{nr^2}{L^2}.
\end{aligned}
\tag{4.6}
$$

具体合法参数列为 $n=3N$、$L=n^2$、$q=L-1$。它满足

$$
0<nx=n\sin\frac\pi{2n^2}\le\frac\pi{2n}\longrightarrow0,
$$

式（4.6）在此列分别为 $(\pi^2c_\star/4+o(1))n^{-3}$、$(\pi^2c_B/4+o(1))n^{-3}$ 和 $(\pi^2(c_\star-c_B)/4+o(1))n^{-3}$。

**证明。** $2u/\pi\le\sin u\le u$ 对 $0\le u\le\pi/2$ 成立，代入 $u=\pi r/(2L)$ 得式（4.5）。$x>0$ 等价于整数 $r\ge1$；$nr/L\to0$ 蕴含 $n/L\to0$。同时 $r/L\to0$，故 $x/(r/L)\to\pi/2$。把这个比值与定理 4.1 的同列极限相乘，得到式（4.6）。所示实例满足全部整数限制并有 $nr/L=1/n\to0$。每次实验内的校准和来源仍固定；这里比较不同的合法合同。$r=0$ 的精确零端点不参加这些归一化比值。证毕。

## 5. 完整五窗函数及引用的适用范围

**定义 5.1（全部有限历史的五窗函数）。** 沿用 [Recovery][Recovery] 定义 4.2，令 $W_j(b)=(b_{3j-2},b_{3j-1},b_{3j})$。窗口 $000,100,010,101,001$ 分别记作 $\mathrm{null},2,3,2\ 5,5$，接缝条件仍为 $b_{3j}b_{3j+1}=0$。索引函数在 $j\in\{1,\ldots,N\}$ 时返回 $W_j$。指针版本的状态为 $a\in\{1,\ldots,N+1\}$，初值一；索引读不改 $a$，$\mathrm{Next}$ 恰在 $a\le N$ 时合法，返回 $W_a$ 并把 $a$ 加一。没有 $\mathrm{End}$ 操作，尾部 null 仍是窗口。

一次取得后的输出是确定性函数及相应更新，之后不再访问源或源相关建议；取得和每个合法回复均有限终止。整条成功要求全部有限合法历史的回复、合法域与后继均正确，包含重复和依据先前回复作的自适应索引选择。

**数学引文 5.2（逐源归约的应用）。** [Recovery][Recovery] 推论 4.3 和 [Minimax][Minimax] 定理 2.1(G)、§3.8 给出此合同下整词取得与上述两种完整五窗函数的最优 Bayes、minimax 分数相同。正向从估计词构成函数，整条成功事件恰为词正确事件；反向有限索引扫描不增加源调用，逐来源恢复概率至少为整条成功概率。因此定理 2.1、4.1 和命题 4.3 的优化值直接适用于这些完整函数。所用归约不把有限扫描当成任意输出函数对所有历史正确的认证，不改变来源或操作合同。

**数学引文 5.3（数学公式的归属与文献边界）。** 本卷的各步依赖以下具体结论。

| 来源与精确条目 | 使用的数学结论及条件 |
| --- | --- |
| [Minimax][Minimax] 定义 1.5，定理 2.1(A)，§§3.2–3.4、式（3.8）–（3.10） | 图份额系数 $\kappa_n$、全部共同准备和有限参考的有限下界、同一共同旋转接收器及其精确振幅。对该接收器的词长一致余项由本卷式（3.8）、（3.10）给出。 |
| [Recovery][Recovery] 定理 2.1(A)–(C)，§§3.4–3.5 | Gram 距离公式、SRM、$C_n$、有限 Bayes 夹逼。常数 $3/4$ 的平均余项是该夹逼的直接定量推论。 |
| [Growth][Growth] 定理 5.2、定理 7.3、推论 7.4 | $c_\star$ 的存在、$c_\star n\le\kappa_n\le c_\star(n+1)$、解析有理下界、Fibonacci 比值极限及正系数差；Cartesian 可加性和 Fekete 步骤仍使用该卷的结论。 |
| [Eldar–Forney][EF]，版本 v2、定理 3 | SRM 正交化 $\Phi G^{-1/2}$；不将其特殊对称态族的精确最优性套用于本来源。 |
| [Tyson][Tyson]，版本 v1、§§1.3–1.4、定义 6、定理 7 | 等先验时幂权平方根测量一致；近正交测量渐近最优性固定有限先验与态数，不提供增长标签数或本源输入优化的一致界。 |
| [Montanaro][Montanaro]，版本 v2、§2.2、式（8） | Gram 平方根的逐来源平方重叠界；其直接应用不确定图份额最优系数。 |
| [Quartic][Quartic] 定理 2.1(A) 与 [Sixth][Sixth] 定理 2.1 | 同一源的固定词长四阶、六阶最优 Bayes 展开；常数和邻域依赖 $n$，不替代本卷的联合估计。 |

这里使用的文献范围限于表中具名条目的结论与假设。平方根谱演算和反对称矩阵指数作为这些推导的标准工具；所述源特定一致估计不作为一般近正交态族、一般图到量子源的对应、局部或 LOCC 类的最优性、价格优势或实际学习收益的结论。精确 $c_\star$、内部有限参数精确最优值、较大 $nx$ 区域及词长一致的更高阶最优余项不由这些估计确定。

[Minimax]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_ATOM_WHITEBOX_LEGAL_EDGE_MINIMAX.md
[Recovery]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_ATOM_WHITEBOX_CORRELATED_WORD_RECOVERY.md
[Growth]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[Quartic]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_ATOM_WHITEBOX_OPTIMAL_PREPARATION_QUARTIC.md
[Sixth]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_ATOM_WHITEBOX_OPTIMAL_BAYES_SIXTH_ORDER.md
[EF]: https://arxiv.org/abs/quant-ph/0005132v2
[Tyson]: https://arxiv.org/abs/0907.1884v1
[Montanaro]: https://arxiv.org/abs/quant-ph/0607011v2

## 追加锚（本行以下为增补区）
