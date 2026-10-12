# FIB 合法边负载的唯一满支撑最优测度

## 1. 完整合法词域与调和目标

**定义 1.1（合法词与完整图）。** 对整数 $n\ge1$，令

$$
B_n=\{b\in\{0,1\}^n:b_ib_{i+1}=0\text{ 对 }1\le i<n\},
\qquad M_n=|B_n|.
$$

图 $\Gamma_n=(B_n,E_n)$ 包含全部 Hamming 距离为一的合法词对。记 $b\sim c$ 表示 $\{b,c\}\in E_n$，$k(b)=\sum_i b_i$，$0^n$ 为全零词。若 $b_i=0$ 且把该位改为 $1$ 后仍合法，所得词记为 $b+e_i$。每条边唯一地写成 $\{b,b+e_i\}$，称 $b$ 为下端。端点外约定 $b_0=b_{n+1}=0$；合法插入的条件是 $b_{i-1}=b_i=b_{i+1}=0$。

合法词也就是路径 $P_n$ 的独立集；取子集保持合法，单点增删给出上述完整边集。这是 Fibonacci 立方的经典描述，见 [Codara–D'Antona][CD] 的定义 1–2 与第 1、3 节。其计数为 $M_n=F_{n+2}$，其中 $F_0=0$、$F_1=1$、$F_{j+2}=F_{j+1}+F_j$。这一计数也可由末位分类得到：$M_0=1$、$M_1=2$，而 $M_n=M_{n-1}+M_{n-2}$。任意合法词逐个删去其 $1$ 都能沿原图边走到 $0^n$，所以 $\Gamma_n$ 连通。

**定义 1.2（原单纯形与目标）。** 对 $s,t\ge0$，置

$$
\mathcal P(B_n)=\left\{\mu\in[0,\infty)^{B_n}:\sum_{b\in B_n}\mu_b=1\right\},
\qquad
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
$$

以及

$$
\Phi_n(\mu)=\sum_{\{b,c\}\in E_n}h(\mu_b,\mu_c).
\tag{1.1}
$$

这里的优化域允许任意零坐标。所有合法词，包括 $0^n$，以及所有原图边都参与定义。

[增长常数卷][Growth] 的引理 3.1 给出 $h$ 的连续性、凹性、一次齐次性及变分恒等式

$$
s\alpha^2+t(1-\alpha)^2-h(s,t)
=(s+t)\left(\alpha-\frac{t}{s+t}\right)^2
\quad(s+t>0).
\tag{1.2}
$$

当 $s=t=0$ 时，左边恒为零。该卷定理 3.2 给出有限调和对偶、最大值存在性及精确鞍点等号；其中一般 minimax 步骤使用 [Sion][Sion] 的经典定理。

**定义 1.3（位置常数）。** 对 $1\le i\le n$，令

$$
N_i=\{i-1,i+1\}\cap\{1,\ldots,n\},\qquad
d_i=|N_i|,\qquad q_i=\frac{4-d_i}{4+d_i}.
\tag{1.3}
$$

$d_i$ 是位置 $i$ 在路径中的度数，区别于合法词在 $\Gamma_n$ 中的度数。$n=1$ 时 $q_1=1$；$n\ge2$ 时两个端点的 $q_i=3/5$，内部位置的 $q_i=1/3$。

## 2. 合法插入的完整邻域比较

**引理 2.1（配对翻转与被阻插入）。** 设 $p_b>0$ 对全部 $b\in B_n$ 成立，定义

$$
g_b(p)=\frac{\partial\Phi_n}{\partial p_b}
=\sum_{c\sim b}\left(\frac{p_c}{p_b+p_c}\right)^2,
\qquad f(t)=\frac{t^2}{(1+t)^2}\quad(t>0).
\tag{2.1}
$$

对任一原图边 $y=x+e_i$，置 $r=p_y/p_x$。令

$$
T_i(x)=\{w\sim x:w\text{ 由翻转位置 }j\text{ 得到，}|j-i|\ge2\},
$$

$$
U_i(x)=\{x+e_j:j\in N_i,\ x+e_j\in B_n\}.
$$

则 $x$ 的邻点恰为 $\{y\}\sqcup T_i(x)\sqcup U_i(x)$，$y$ 的邻点恰为 $\{x\}\sqcup\{w+e_i:w\in T_i(x)\}$，且 $|U_i(x)|\le d_i$。特别地，

$$
\begin{aligned}
g_y(p)-g_x(p)
&=\frac{1-r}{1+r}
 +\sum_{w\in T_i(x)}\left[
 f\left(\frac{p_{w+e_i}}{p_y}\right)
 -f\left(\frac{p_w}{p_x}\right)\right]
 -\sum_{v\in U_i(x)}f\left(\frac{p_v}{p_x}\right).
\end{aligned}
\tag{2.2}
$$

**证明。** $x_i=0$，$y_i=1$，且两词在 $N_i$ 上都为零。翻转 $i$ 给出彼此。翻转满足 $|j-i|\ge2$ 的位置，其合法性只取决于该位及相邻位，因而在 $x$ 与 $y$ 中相同。对每个这样的下层邻点 $w$，$w+e_i$ 合法，且为 $y$ 的邻点；这给出所述一一配对。

剩余位置恰为 $N_i$。这些位置在 $x$ 中只能由零插入 $1$，满足合法条件的结果就是 $U_i(x)$；它们在 $y$ 中都被第 $i$ 位的 $1$ 阻止。没有其他翻转位置，故邻域分解完整。

式（2.1）由 $\partial_s h(s,t)=t^2/(s+t)^2$ 得到。边 $xy$ 对 $g_y-g_x$ 的贡献为

$$
\frac{1}{(1+r)^2}-\frac{r^2}{(1+r)^2}
=\frac{1-r}{1+r}.
$$

将配对邻点和剩余邻点分别相加即得（2.2）。此外 $f'(t)=2t/(1+t)^3>0$，故 $f$ 严格递增。以上导数计算是初等微积分；本引理的图结构内容是完整邻域配对及至多 $d_i\le2$ 个被阻插入。

## 3. 唯一性与全部原坐标的正性

**定理 3.1（完整 Fibonacci 图的唯一满支撑最大点）。** 对每个整数 $n\ge1$，$\Phi_n$ 在整个 $\mathcal P(B_n)$ 上有且仅有一个最大点，记为 $\pi^{(n)}$。它在每个原合法词上都严格为正，并且对每个合法插入 $b\mapsto b+e_i$ 有

$$
q_i\,\pi^{(n)}_b\le\pi^{(n)}_{b+e_i}\le\pi^{(n)}_b.
\tag{3.1}
$$

进一步，对每个 $b\in B_n$，

$$
\pi^{(n)}_b
\ge\frac{1}{F_{n+2}}\prod_{i:b_i=1}q_i
\ge\frac{3^{-k(b)}}{F_{n+2}}
\ge\frac{3^{-\lceil n/2\rceil}}{F_{n+2}}>0.
\tag{3.2}
$$

空乘积取 $1$，故此式也包含全零词。$n=1$ 时 $\pi^{(1)}_0=\pi^{(1)}_1=1/2$。各结论同样适用于全部 $n=3N$、$N\ge1$。

**证明。** 固定 $n$，缩写 $M=M_n$、$\Phi=\Phi_n$。取辅助常数

$$
0<\varepsilon<\frac{3^{-n}}{M},\qquad
\mathcal P_\varepsilon=
\left\{p\in\mathcal P(B_n):p_b\ge\varepsilon\text{ 对全部 }b\right\}.
\tag{3.3}
$$

均匀向量属于这个非空紧集。由 $\Phi$ 连续，存在其在 $\mathcal P_\varepsilon$ 上的最大点 $p$。本段的导数只在这个正向量处使用。随后将证明所有辅助下界都不活跃，并对原单纯形上的每个向量给出最优性等号。

先令 $R$ 为全部合法插入比 $p_{x+e_i}/p_x$ 的最大值；这些边非空且有限。假设 $R>1$，取实现它的边 $y=x+e_i$。对引理 2.1 中的每个 $w\in T_i(x)$，边 $w\mapsto w+e_i$ 也是原合法插入，故

$$
\frac{p_{w+e_i}}{p_w}\le R=\frac{p_y}{p_x},
\qquad
\frac{p_{w+e_i}}{p_y}\le\frac{p_w}{p_x}.
$$

由于 $f$ 递增，（2.2）的每个配对差都非正；最后一项也非正。因此

$$
g_y(p)-g_x(p)\le\frac{1-R}{1+R}<0.
$$

但 $p_y>p_x\ge\varepsilon$，所以可以从 $y$ 向 $x$ 转移充分小的正质量，仍留在 $\mathcal P_\varepsilon$，其目标导数为 $g_x-g_y>0$。这与辅助最大性矛盾。于是全部合法插入都满足

$$
p_{x+e_i}\le p_x.
\tag{3.4}
$$

接着固定任意位置 $i$，令 $r_i$ 为该方向全部合法插入比的最小值。该方向至少含 $0^n\mapsto e_i$，所以最小值存在且 $0<r_i\le1$。取实现它的边 $y=x+e_i$。对每个 $w\in T_i(x)$，

$$
\frac{p_{w+e_i}}{p_w}\ge r_i=\frac{p_y}{p_x},
\qquad
\frac{p_{w+e_i}}{p_y}\ge\frac{p_w}{p_x},
$$

故（2.2）的配对差都非负。每个 $v\in U_i(x)$ 是在另一个位置的合法插入；（3.4）给出 $p_v\le p_x$，从而 $f(p_v/p_x)\le f(1)=1/4$。因此

$$
g_y(p)-g_x(p)\ge\frac{1-r_i}{1+r_i}-\frac{d_i}{4}.
\tag{3.5}
$$

若 $r_i<q_i$，则 $r_i<1$，且（3.5）的右边严格为正，因为

$$
\frac{1-r_i}{1+r_i}>\frac{d_i}{4}
\quad\Longleftrightarrow\quad
r_i<\frac{4-d_i}{4+d_i}=q_i.
$$

此时 $p_x>p_y\ge\varepsilon$，可以从 $x$ 向 $y$ 转移充分小的正质量，其导数为 $g_y-g_x>0$，再次矛盾。于是对每个原合法插入都有

$$
q_i\le\frac{p_{b+e_i}}{p_b}\le1.
\tag{3.6}
$$

逐个删去任意合法词的 $1$，由（3.4）可知 $p_{0^n}$ 是最大坐标，故 $p_{0^n}\ge1/M$。反过来，从 $0^n$ 按任意顺序插入 $b$ 的各个 $1$，所有中间词均为 $b$ 的子集而合法。（3.6）沿此路径给出

$$
p_b\ge p_{0^n}\prod_{i:b_i=1}q_i
\ge\frac{3^{-k(b)}}{M}
\ge\frac{3^{-n}}{M}>\varepsilon.
\tag{3.7}
$$

所以辅助最大点的每个下界约束都严格不活跃。任意两个坐标之间都可作双向小质量转移；一阶必要条件遂给出一个实数 $\lambda$，使

$$
g_b(p)=\lambda\qquad(b\in B_n).
\tag{3.8}
$$

逐边求和可得初等齐次恒等式

$$
\begin{aligned}
\sum_b p_b g_b(p)
&=\sum_{\{b,c\}\in E_n}
\frac{p_bp_c^2+p_cp_b^2}{(p_b+p_c)^2}\\
&=\sum_{\{b,c\}\in E_n}\frac{p_bp_c}{p_b+p_c}
=\Phi(p).
\end{aligned}
$$

由（3.8）与 $\sum_b p_b=1$，得到 $\Phi(p)=\lambda$。

现在定义原图每条有向边的份额

$$
a_{c\leftarrow b}=\frac{p_c}{p_b+p_c},\qquad
a_{b\leftarrow c}=\frac{p_b}{p_b+p_c}.
\tag{3.9}
$$

两份额相加为一，各顶点平方份额负载为 $L_b(a)=g_b(p)=\lambda$。对原单纯形上的任意 $\nu$，包括任意零质量及零零边，（1.2）给出

$$
\Phi(\nu)\le\sum_b\nu_bL_b(a)=\lambda=\Phi(p).
\tag{3.10}
$$

这将 $p$ 认证为原问题的最大点，而非仅为辅助紧集的最大点。更精确地，仍由（1.2），

$$
\lambda-\Phi(\nu)
=\sum_{\substack{\{b,c\}\in E_n\\\nu_b+\nu_c>0}}
\frac{(\nu_bp_c-\nu_cp_b)^2}
{(\nu_b+\nu_c)(p_b+p_c)^2}.
\tag{3.11}
$$

若 $\nu_b=\nu_c=0$，该边的原变分差严格等于零；（3.11）以省去零项表示这个情形，并未删除原边。

设 $\nu$ 为任意原最大点。左边为零，各非负项必须为零。因此在每条边上都有 $\nu_bp_c=\nu_cp_b$；零零边上同一等式也成立。由于全部 $p_b>0$，这等价于

$$
\frac{\nu_b}{p_b}=\frac{\nu_c}{p_c}\qquad(b\sim c).
$$

原图连通，故所有这些比值是同一常数。两向量的原归一化条件迫使该常数为一，即 $\nu=p$。这同时排除了所有边界最大点、正支撑不连通的最大点及不同归一化比例的最大点。于是可记 $p=\pi^{(n)}$。

式（3.6）、（3.7）给出（3.1）及（3.2）的前两个下界。将位置分成相邻对 $\{1,2\},\{3,4\},\ldots$，奇数长度时加上最后的单点，每组至多含一个 $1$，所以 $k(b)\le\lceil n/2\rceil$，给出最后一个下界。$n=1$ 时 $q_1=1$，（3.1）迫使两个质量相等，因而各为 $1/2$。证明对全部 $n\ge1$ 成立，故也覆盖 $n=3N$。

（3.2）的质量下界依赖 $n$，可以随词长衰减；它不声称一个对全部词长统一的正质量下界。端点和内部位置分别由 $d_i=1$、$d_i=2$ 处理，$n=1$ 则由 $d_i=0$ 处理。对 $n=3N$ 按三位分组书写词时，组间相邻位置仍是同一路径上的相邻位置，所有跨组合法翻转边仍在引理 2.1 的完整邻域中。

## 4. 原负载问题的直接接口

**推论 4.1（唯一分配与全顶点等负载）。** 在 $\Gamma_n$ 上，令 $\mathcal A(\Gamma_n)$ 为满足 $a_{c\leftarrow b}\in[0,1]$、$a_{c\leftarrow b}+a_{b\leftarrow c}=1$ 的全部原边分配，并令

$$
L_b(a)=\sum_{c\sim b}a_{c\leftarrow b}^2,\qquad
\kappa_n=\min_{a\in\mathcal A(\Gamma_n)}\max_bL_b(a).
$$

该最小化问题也有唯一解，且在全部原边和全部原顶点上分别满足

$$
a_{c\leftarrow b}=\frac{\pi^{(n)}_c}{\pi^{(n)}_b+\pi^{(n)}_c},
\qquad L_b(a)=\kappa_n=\Phi_n(\pi^{(n)}).
\tag{4.1}
$$

在每条合法插入边 $y=x+e_i$ 上还有

$$
\frac{4-d_i}{8}\le a_{y\leftarrow x}\le\frac12,
\qquad
\frac12\le a_{x\leftarrow y}\le\frac{4+d_i}{8}.
\tag{4.2}
$$

**证明。** 有限分配集紧，最小点存在。[增长常数卷][Growth] 定理 3.2 的鞍点等号适用于任意最小分配和定理 3.1 的最大测度。因后者在每个原坐标严格为正，鞍点份额公式在每条边都适用，且每个顶点负载都必须等于 $\kappa_n$。这唯一地指定全部分配份额。它也与（3.8）–（3.10）给出的分配一致。

若 $r=\pi^{(n)}_y/\pi^{(n)}_x$，则 $a_{y\leftarrow x}=r/(1+r)$，而（3.1）给出 $q_i\le r\le1$。由于 $r/(1+r)$ 递增，且 $q_i/(1+q_i)=(4-d_i)/8$，得到第一组界；取互补份额得到第二组。特别地，全部原份额都在 $[1/4,3/4]$ 内；端点插入的范围分别为 $[3/8,1/2]$ 与 $[1/2,5/8]$，$n=1$ 时两份额都是 $1/2$。

这是定理 3.1 经既有有限调和对偶得到的原模型接口后果；它不引入新的 minimax 原理。

**推论 4.2（反转与包含关系）。** 唯一最大测度在 $\Gamma_n$ 的每个图自同构下不变，特别地对反转 $\rho(b)_i=b_{n+1-i}$ 有 $\pi^{(n)}_{\rho(b)}=\pi^{(n)}_b$。若 $b,c\in B_n$ 且 $b_i\le c_i$ 对全部位置成立，则

$$
\left(\prod_{i:b_i=0,\ c_i=1}q_i\right)\pi^{(n)}_b
\le\pi^{(n)}_c\le\pi^{(n)}_b.
\tag{4.3}
$$

**证明。** 图自同构置换原边集，因而保持 $\Phi_n$；它将最大点送到最大点，唯一性迫使其不变。反转保持合法性和 Hamming 邻接，故为自同构。包含情形中，从 $b$ 逐个加入 $c$ 中新增的 $1$，每个中间词都是合法词 $c$ 的子集；沿这条原图路径应用（3.1）即得（4.3）。

反转不变最大点的存在原已由增长常数卷推论 3.3 给出；这里唯一性使所有最大点归于该单一测度。（4.3）比较的是包含关系，不能据此把不互相包含的词仅按 $k(b)$ 排序。

**推论 4.3（每个真面严格次优）。** 对任意非空真子集 $S\subsetneq B_n$，

$$
\max_{\substack{\nu\in\mathcal P(B_n)\\\nu_b=0\ (b\notin S)}}\Phi_n(\nu)<\kappa_n.
\tag{4.4}
$$

**证明。** 所示原单纯形的闭面非空且紧，故限制目标取到最大值。若它达到 $\kappa_n$，便是原问题的一个最大点；定理 3.1 迫使它等于满支撑的 $\pi^{(n)}$，与面外零坐标矛盾。式（3.11）同时给出了每个具体面内向量的精确非负差。这一结论仍在完整原目标中计算，保留面内、跨面及面外的全部原边。

## 5. 数学归属与未解问题

完整合法词图、调和变分式、有限对偶、最大值存在性及反转平均归于 [增长常数卷][Growth] 定义 2.1–2.5、引理 3.1、定理 3.2 与推论 3.3。该卷开放问题 9.5 中的唯一性和满支撑两项由本卷定理 3.1 回答。Fibonacci 立方及路径独立集描述是既有组合数学；[Hsu][Hsu] 是该图的经典来源，[Codara–D'Antona][CD] 给出本卷使用的独立集描述和计数。调和变分式、紧集取极值、可行方向的一阶条件及比例等号均为既有数学工具。

相对于这些前置，本卷的新增结论是实际完整 $\Gamma_n$ 上的两个全称结构命题。证明使用引理 2.1 的邻域对应、定理 3.1 中最大与最小插入比的比较、以及在原单纯形上成立的（3.11）。插入比界、正质量界、唯一均衡分配与真面严格次优是同一证明的后果及接口，区别于新的经典分析原理。

P. Codara 与 O. M. D'Antona 的 [*Independent subsets of powers of paths, and Fibonacci cubes*][CD]，arXiv:1211.2251v1，提供路径独立集背景。W.-J. Hsu 的 [*Fibonacci cubes—a new interconnection topology*][Hsu]，IEEE Transactions on Parallel and Distributed Systems 4（1993），3–12，是 Fibonacci 立方的经典文献。M. Sion 的 [*On general minimax theorems*][Sion]，Pacific Journal of Mathematics 8（1958），171–176，供应增长常数卷有限对偶中的一般 minimax 定理。这些背景和工具分别具有其自身来源。

**开放问题 5.1（不互相包含的词）。** 对不互相包含的合法词 $b,c$，仅有 $k(b)<k(c)$ 时，是否必有 $\pi^{(n)}_b\ge\pi^{(n)}_c$？式（4.3）只提供包含路径上的比较，未提供这类词间的比较。

**开放问题 5.2（增长与常数项）。** 增长常数卷定理 5.2 给出 $c_\star=\lim_n\kappa_n/n$ 和 $\theta_n=\kappa_n-c_\star n\in[0,c_\star]$。$c_\star$ 的精确值、$\kappa_n$ 的闭式、$\theta_n$ 的收敛或奇偶子列收敛仍未由本卷确定。各有限长度最大点的唯一性与正性不提供这些渐近结论。

[Growth]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[CD]: https://arxiv.org/html/1211.2251v1
[Hsu]: https://doi.org/10.1109/71.205649
[Sion]: https://doi.org/10.2140/pjm.1958.8.171

## 追加锚（本行以下为增补区）
