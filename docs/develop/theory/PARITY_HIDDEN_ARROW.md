# 有限奇偶马尔可夫核的隐藏时间箭头与信息阈值

## 1. 奇偶核与路径方向

**定义 1.1（奇偶核族）。** 固定整数 $d\ge2$，记 $n=2^d$、$M=2^{d-1}$、
$X=\{-1,+1\}^d$、$\chi(x)=\prod_{j=1}^d x_j$ 及
$C_\pm=\{x:\chi(x)=\pm1\}$。$\mathbb E$ 表示 $X$ 上的均匀平均，
$\mathbb E_\pm$ 表示 $C_\pm$ 上的均匀平均。取 $a:X\to(-1,1)$ 满足
$\mathbb E a=0$，定义

$$
P_a(x,y)=\frac{1+a(x)\chi(y)}n,\qquad
b(x)=\chi(x)a(x),\qquad m=\mathbb E b.
$$

每行之和为 $1$，每列之和也为 $1$，故均匀分布 $\pi(x)=1/n$ 平稳；
所有转移概率严格为正。条件 $\mathbb E a=0$ 等价于
$\mathbb E_+b=\mathbb E_-b=m$。记 $\mathcal K_d^0$ 为额外满足 $m=0$ 的核族，
并以均匀分布启动相应平稳马尔可夫链 $(X_t)_{t\ge0}$。

**定义 1.2（一步信息与路径不可逆率）。** 全文用自然对数，置

$$
\phi(u)=\frac{(1+u)\log(1+u)+(1-u)\log(1-u)}2,\qquad -1\le u\le1,
$$

端点按 $0\log0=0$ 延拓；置 $h(u)=\operatorname{artanh}u$、
$g(u)=u h(u)$，后两者的定义域为 $(-1,1)$。定义

$$
I(P)=I(X_0;X_1)=\frac1n\sum_{x,y}P(x,y)\log\bigl(nP(x,y)\bigr),
$$

$$
\sigma(P)=D\bigl(\mathcal L(X_0,X_1)\,\Vert\,\mathcal L(X_1,X_0)\bigr)
=\frac1n\sum_{x,y}P(x,y)\log\frac{P(x,y)}{P(y,x)}.
$$

这是有限平稳马尔可夫链的标准路径相对熵率；链式展开给出长度 $T$ 的正向路径律
与倒序路径律的相对熵为 $T\sigma(P)$。这里不附加热浴或局部详细平衡假设。

## 2. 固定状态数的尖锐发散阈值

**定理 2.1（真子坐标全白、两步独立时的信息阈值）。** 令

$$
F_M(r)=\frac{\phi(r)+(M-1)\phi(r/(M-1))}{2M}\quad(0\le r\le1),
\qquad
c_d=F_M(1)
=\frac{\log2+(M-1)\phi(1/(M-1))}{2M}.
$$

在核族 $\mathcal K_d^0$ 中有以下结论。

(i) 对任意固定真子集 $S\subsetneq\{1,\ldots,d\}$，
整个过程 $((X_t)_S)_{t\ge0}$ 是均匀独立同分布过程；完整链满足
$P^2=\Pi$，其中 $\Pi(x,y)=1/n$。特别地，所有这些核的特征多项式均为
$(z-1)z^{n-1}$。

(ii) 对任意 $c\in[0,\log2)$，定义信息预算下的不可逆率上确界

$$
\Sigma_d(c)=\sup\{\sigma(P):P\in\mathcal K_d^0,\ I(P)\le c\}.
$$

则

$$
\boxed{\quad \Sigma_d(c)<\infty\ \Longleftrightarrow\ c<c_d.\quad}
$$

在 $0<c<c_d$ 时，存在唯一 $r_c\in(0,1)$ 使 $F_M(r_c)=c$，并有显式界

$$
\sigma(P)\le g(r_c)\qquad
\bigl(P\in\mathcal K_d^0,\ I(P)\le c\bigr).
$$

在 $c=0$ 时唯一的核是 $\Pi$，其不可逆率为零。

(iii) 临界值自身可由严格正核实现为发散序列的恒定信息：
存在 $P_k\in\mathcal K_d^0$ 满足

$$
I(P_k)=c_d\quad\text{对每个 }k,\qquad
\sigma(P_k)\longrightarrow+\infty.
$$

(iv) 当 $d\to\infty$ 时，

$$
c_d=\frac{\log2}{2^d}
+\frac{1}{2^d(2^d-2)}+O(2^{-4d}).
$$

**证明。** 先求本族的精确表达式。若 $S$ 是真子集，固定 $y_S=z$ 后，
在至少一个未观测坐标上翻转符号使 $\chi(y)$ 相消，所以对每个完整状态 $x$，

$$
\sum_{y:y_S=z}P_a(x,y)=2^{-|S|}.
$$

因此下一时刻的子坐标向量条件于全部过去仍为均匀分布。
由平稳初始分布归纳得到任意长度的独立乘积分布。这一论证针对每个固定 $S$；
它不把不同 $S$ 的联合记录当成同一个受限观察。

将核视为作用于实函数的算子，有

$$
Pf=\mathbb E f+\ a\,\mathbb E(\chi f).
$$

写 $A=P-\Pi$，则 $\Pi A=A\Pi=0$，且 $A^2=mA$。
在 $m=0$ 时 $A^2=0$，所以 $P^2=\Pi$；常数方向上的特征值为 $1$，
均值零子空间上的算子平方为零，给出 (i) 的特征多项式。
这里不要求 $P$ 可对角化。

为计算 $I$ 与 $\sigma$，记

$$
\ell(u)=\frac12\log(1-u^2),\qquad
\log(1+a(x)\chi(y))=\ell(a(x))+\chi(y)h(a(x)).
$$

在均匀乘积测度上，

$$
I(P)=\mathbb E\phi(a)=\mathbb E\phi(b).
$$

又

$$
\sigma(P)=
\mathbb E_{x,y}\!\left[(1+a(x)\chi(y))
  \bigl(\log(1+a(x)\chi(y))-\log(1+a(y)\chi(x))\bigr)\right].
$$

第一个对数的贡献是 $\mathbb E\ell(a)+\mathbb E[a h(a)]$；
第二个对数的贡献是
$\mathbb E\ell(a)+\mathbb E[a\chi]\,\mathbb E[\chi h(a)]$。
因为 $h$ 为奇函数、$a=\chi b$ 且 $\mathbb E[a\chi]=m$，得到

$$
\boxed{\quad
I(P)=\mathbb E\phi(b),\qquad
\sigma(P)=\mathbb E[(b-m)h(b)]
=\operatorname{Cov}(b,h(b)).
\quad} \tag{2.1}
$$

尤其在 $\mathcal K_d^0$ 内，

$$
\sigma(P)=\mathbb E g(b). \tag{2.2}
$$

这些计算也说明：在更大的定义 1.1 核族内，
$\sigma=0$ 当且仅当 $b$ 为常数，因为对独立均匀状态 $x,y$，

$$
2\operatorname{Cov}(b,h(b))
=\mathbb E_{x,y}\bigl[(b(x)-b(y))(h(b(x))-h(b(y)))\bigr],
$$

右边逐项非负，且 $h$ 严格递增。

下面证明临界界。对任意坐标 $x_*$，设 $|b(x_*)|=r$。
同一奇偶类的其余 $M-1$ 个数的和为 $-b(x_*)$。
由 $\phi''(u)=1/(1-u^2)>0$、偶性及 Jensen 不等式，

$$
I(P)\ge
\frac{\phi(r)+(M-1)\phi(r/(M-1))}{2M}
=F_M(r). \tag{2.3}
$$

另一奇偶类的贡献非负。$F_M$ 在 $[0,1]$ 上连续，在 $(0,1)$ 上严格递增，
且 $F_M(0)=0$。若 $I(P)\le c<c_d$，式 (2.3) 对每个坐标都给出
$|b(x)|\le r_c<1$。$g$ 是偶函数并在 $[0,1)$ 上递增，
故 (2.2) 给出 $\sigma(P)\le g(r_c)$。
若 $c=0$，$\phi$ 的唯一零点为零，所以 $b=0$、$P=\Pi$。

为证明临界发散，令 $r\uparrow1$，在 $C_+$ 上取

$$
b_1=r,\qquad b_2=\cdots=b_M=-\frac{r}{M-1}.
$$

该类均值为零，其对总信息的贡献恰为 $F_M(r)$。
由于 $c_d-F_M(r)\downarrow0$，对足够靠近 $1$ 的 $r$，
存在唯一 $s_r\in(0,1)$ 满足

$$
\phi(s_r)=2\bigl(c_d-F_M(r)\bigr).
$$

$M$ 为偶数，因此可在 $C_-$ 上放置 $M/2$ 个 $s_r$ 与 $M/2$ 个 $-s_r$。
此类也均值为零，总信息严格等于 $c_d$，且所有 $|b|<1$。
但

$$
\sigma(P_r)\ge \frac{g(r)}{2M}\longrightarrow+\infty.
$$

这证明 (iii)，也给出 (ii) 中所有 $c\ge c_d$ 的发散。
最后，用 $\phi(u)=u^2/2+O(u^4)$ 展开 $F_M(1)$，得到

$$
c_d=\frac{\log2}{2M}+\frac1{4M(M-1)}
+O\!\left(\frac1{M(M-1)^3}\right),
$$

代入 $M=2^{d-1}$ 即为 (iv)。$\square$

## 3. 下边界与四状态的完整上边界

**定义 3.1（信息坐标中的代价函数）。** $\phi$ 在 $[0,1)$ 上严格递增，
将它在该区间的反函数记为 $\phi_+^{-1}:[0,\log2)\to[0,1)$，并置

$$
H(t)=g\bigl(\phi_+^{-1}(t)\bigr),\qquad 0\le t<\log2.
$$

**定理 3.2（固定一步信息的尖锐上下界）。** 对 $d\ge2$ 及 $0\le I_0<\log2$，
在 $\{P\in\mathcal K_d^0:I(P)=I_0\}$ 上，最小不可逆率恰为

$$
\boxed{\quad \min\sigma(P)=H(I_0).\quad}
$$

等号成立当且仅当所有 $|b(x)|$ 都等于 $\phi_+^{-1}(I_0)$。
当 $d=2$ 时，还可求得完整的上边界：

$$
\boxed{
\sup_{P\in\mathcal K_2^0,\ I(P)=I_0}\sigma(P)=
\begin{cases}
\frac12 H(2I_0),&0\le I_0<\frac12\log2,\\
+\infty,&\frac12\log2\le I_0<\log2.
\end{cases}}
$$

第一行的上界可达；在 $I_0>0$ 时，达到上界恰好要求一奇偶类上的 $b$ 为零，
另一奇偶类上的两个值为
$\pm\phi_+^{-1}(2I_0)$，两类的角色可互换。

**证明。** 置 $t=\phi(u)$、$0<u<1$。直接求导得

$$
H'(t)=1+\frac{u}{(1-u^2)h(u)},\qquad
H''(t)=\frac{(1+u^2)h(u)-u}{(1-u^2)^2h(u)^3}>0,
$$

其中正性由 $h(u)>u$ 给出。
在零点，$H(t)=2t+\frac23t^2+O(t^3)$，故 $H$ 在整个 $[0,\log2)$ 上严格凸。
将 (2.2) 写成 $\sigma=\mathbb E H(\phi(b))$，Jensen 不等式给出
$\sigma\ge H(\mathbb E\phi(b))=H(I_0)$。
等号当且仅当所有 $\phi(b(x))$ 相等，亦即所有 $|b(x)|$ 相等。
因每个奇偶类含偶数个状态，将该类一半取正、一半取负，
即可在任何 $I_0$ 上满足零均值并达到下界。

当 $d=2$ 时，每个奇偶类恰有两个状态；零均值强制其取值分别为
$(u,-u)$ 和 $(v,-v)$，其中 $|u|,|v|<1$。写
$\alpha=\phi(u)$、$\beta=\phi(v)$，则

$$
I_0=\frac{\alpha+\beta}{2},\qquad
\sigma=\frac{H(\alpha)+H(\beta)}2.
$$

若 $2I_0<\log2$，可行线段为
$0\le\alpha\le2I_0$、$\beta=2I_0-\alpha$。
严格凸函数在该线段上的最大值位于端点，给出
$\sigma\le H(2I_0)/2$ 及等号刻画。

若 $2I_0\ge\log2$，取 $\alpha_k\uparrow\log2$ 并令
$\beta_k=2I_0-\alpha_k$。
对足够大的 $k$，二者均在 $[0,\log2)$ 内；
$H(\alpha_k)\to\infty$，而 $H(\beta_k)\ge0$。
由对应的 $u_k,v_k$ 构造严格正核，给出信息精确固定的发散序列。$\square$

## 4. 来源、文献状态与边界

**文献表态。** 本卷的有限奇偶核、所有真子坐标的全路径白噪声、临界值
$c_d$、临界恒信息发散构造，以及 $d=2$ 的完整上边界，均标为
`suspected-novel`；这是在下列检索范围内未找到逐字相同结果的工作性标记，不是原创性证明。
检索命中而只承担背景的结果包括：

| 来源 | 精确范围与使用边界 |
| --- | --- |
| Qian Zeng and Jin Wang, *Information Landscape and Flux, Mutual Information Rate Decomposition and Entropy Production*, arXiv:1707.01940 | `literature-attested`：互信息率与熵产生的分解背景；不含本卷的奇偶秩一核或 $c_d$ 阈值 |
| Sheng-Wen Li, *The production rate of the system-bath mutual information*, arXiv:1612.03884；Takahiro Sagawa and Masahito Ueda, *Role of Mutual Information in Entropy Production under Information Exchanges*, arXiv:1307.6092 | `literature-attested`：信息交换与熵产生的热力学关系；不提供本卷的有限观察纤维构造 |
| Krzysztof Ptaszynski and Massimiliano Esposito, *Ensemble dependence of information-theoretic contributions to the entropy production*, arXiv:2301.13061 | `literature-attested`：熵产生的分解依赖选定系综；不提供本卷的尖锐有限维界 |
| — | `repo-derived`：本卷定理 2.1、3.2 及定义 3.1 中的阈值、渐近式和严格正发散族 |

**边界声明。** $\sigma$ 是平稳相邻状态联合律与其交换律之间的 KL 相对熵率；没有给出热浴、能量函数或局部详细平衡时，不把它等同于物理热。真子坐标分别观察时完全白，但在 $\mathcal K_d^0$ 内，只有 $P\ne\Pi$（等价于 $I(P)>0$）时，联合读取全部坐标才能恢复一步方向；在更大的定义 1.1 核族内，这要求 $b$ 非常数。$a=0$、$P=\Pi$ 的端点可逆，不具有时间方向；“边缘白噪声”不等于“联合过程可逆”。证明均在普通实分析和有限维线性代数内，尚未由 Lean kernel 验证。

## 追加锚（本行以下为增补区）
