# 全点对电阻固定的路径 Fiedler 优化

## 1. 图、归一化与系数

**约定 1.1（正电导路径）。** 对每个整数 $n\ge2$，令 $P_n$ 的顶点为
$1,\ldots,n$，边为 $\{i,i+1\}$，其中 $1\le i<n$。电导向量
$c=(c_1,\ldots,c_{n-1})$ 遍历 $(0,\infty)^{n-1}$，不附加任何对称条件。
令 $B\in\mathbb R^{n\times(n-1)}$ 的第 $i$ 列为 $e_i-e_{i+1}$，并令

$$
D=\operatorname{diag}(c_1,\ldots,c_{n-1}),\qquad L(c)=BDB^{\mathsf T}.
$$

这里使用普通未归一化 Laplacian，按重数排列特征值为
$0=\lambda_1<\lambda_2\le\cdots\le\lambda_n$。有效电阻与总电阻约定为

$$
R_{\mathrm{eff}}(a,b)=(e_a-e_b)^{\mathsf T}L(c)^+(e_a-e_b),\qquad
R(c)=\sum_{1\le a<b\le n}R_{\mathrm{eff}}(a,b).
$$

每个无序不同点对只计一次，包括不相邻的点对；因此
$R(c)=n\operatorname{tr}(L(c)^+)$，而非 $\operatorname{tr}(L(c)^+)$。
这里 $L(c)^+$ 是 Moore–Penrose 逆。上述 Laplacian、有效电阻及全点对求和
分别采用 Cruz Ortega–Menéndez-Conde，
[*Maximal Algebraic Connectivity for Paths with Fixed Effective Resistance*,
arXiv:2306.08187v1](https://arxiv.org/pdf/2306.08187v1)，§§2–4 的约定；
全点对求和与迹的系数也见 Ghosh–Boyd–Saberi，
[*Minimizing Effective Resistance of a Graph*, SIAM Review 50(1), 37–66](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf)，
[DOI:10.1137/050645452](https://doi.org/10.1137/050645452)，§§2.4–2.5，式 (8)、(13)–(15)。

**定义 1.2（路径系数）。** 固定 $n\ge2$，置

$$
\begin{aligned}
s_0=s_n&=0,& s_i&=\sqrt{i(n-i)}\quad(1\le i<n),\\
d_i&=2s_i-s_{i-1}-s_{i+1}\quad(1\le i<n),&
v_j&=s_j-s_{j-1}\quad(1\le j\le n),\\
C_n&=\sum_{j=1}^{n}v_j^2.
\end{aligned}
$$

记 $s=(s_1,\ldots,s_{n-1})^{\mathsf T}$、
$d=(d_1,\ldots,d_{n-1})^{\mathsf T}$、$v=(v_1,\ldots,v_n)^{\mathsf T}$。
空指标集上的和为零，特别包括 $n=2$ 时下文的内部边求和。

## 2. 全路径的尖锐乘积界

**定理 2.1（任意正电导的乘积界与全部等号情形）。** 对每个整数 $n\ge2$，
定义 1.2 的每个 $d_i$ 均严格为正，且

$$
C_n=\sum_{i=1}^{n-1}s_i d_i>0.
$$

对每个 $c\in(0,\infty)^{n-1}$，有

$$
R(c)=\sum_{i=1}^{n-1}\frac{i(n-i)}{c_i},\qquad
\lambda_2(L(c))R(c)\le C_n.
$$

等号成立当且仅当存在同一个实数 $k>0$，使

$$
c_i=k\frac{s_i}{d_i}\qquad(1\le i<n).
$$

在这个等号情形，$v$ 是对应于 $k=\lambda_2(L(c))$ 的非零特征向量。

**证明。** 首先证明所有分母的严格正性。函数
$f(x)=\sqrt{x(n-x)}$ 在 $(0,n)$ 上满足

$$
f''(x)=-\frac{n^2}{4[x(n-x)]^{3/2}}<0.
$$

故当 $2\le i\le n-2$ 时，严格中点凹性给出
$2s_i>s_{i-1}+s_{i+1}$。在端点指标 $i=1$，

$$
2s_1=2\sqrt{n-1}>\sqrt{2(n-2)}=s_2,
$$

因为 $4(n-1)-2(n-2)=2n>0$；该式对 $n=2$ 也成立，其中 $s_2=s_n=0$。
由 $s_{n-i}=s_i$ 得到另一端点 $i=n-1$ 的同一结论。
这些情形包含了 $n=2,3$，所以始终有 $d_i>0$。

令 $T=B^{\mathsf T}B$，则 $T$ 的主对角为 $2$，相邻副对角为 $-1$，
并且 $Ts=d$、$Bs=v$。因此

$$
C_n=\|Bs\|^2=s^{\mathsf T}Ts=\sum_{i=1}^{n-1}s_i d_i>0.
$$

同时 $\sum_{j=1}^n v_j=s_n-s_0=0$。这里 $s_i>0$，且 $v\ne0$。

路径电阻的串联公式给出

$$
R_{\mathrm{eff}}(a,b)=\sum_{i=a}^{b-1}\frac1{c_i}\qquad(a<b).
$$

这是 Cruz Ortega–Menéndez-Conde，§4，推论 4.4 的公式，
也是 Ghosh–Boyd–Saberi，§2.3 的树电阻公式。
边 $\{i,i+1\}$ 位于恰好 $i(n-i)$ 个无序点对的唯一路径上，故交换有限求和即得

$$
R(c)=\sum_{1\le a<b\le n}\sum_{i=a}^{b-1}\frac1{c_i}
=\sum_{i=1}^{n-1}\frac{i(n-i)}{c_i}
=\sum_{i=1}^{n-1}\frac{s_i^2}{c_i}.
$$

以下把经典的矩阵谱对应和 Rayleigh 原理作为中间步骤使用。
置 $A=BD^{1/2}$ 及

$$
H=A^{\mathsf T}A=D^{1/2}TD^{1/2},\qquad L=AA^{\mathsf T}.
$$

$Bz=0$ 的第一坐标给 $z_1=0$，逐个坐标递推给出 $z_i=0$，所以 $B$ 满列秩。
因而 $H$ 正定，而 $L$ 的核恰为常数向量空间。
对任一 $\mu>0$，若 $Hz=\mu z$ 且 $z\ne0$，则
$Az\ne0$ 且 $L(Az)=\mu Az$；反之若 $Lx=\mu x$ 且 $x\ne0$，
则 $A^{\mathsf T}x\ne0$ 且 $H(A^{\mathsf T}x)=\mu A^{\mathsf T}x$。
这两个映射在相应特征空间上互逆至因子 $\mu$，故保留重数，得到

$$
\lambda_2(L)=\lambda_{\min}(H).
$$

现在取严格正向量 $y=D^{-1/2}s$。由上述电阻恒等式及 $Ts=d$，有

$$
y^{\mathsf T}y=R(c),\qquad y^{\mathsf T}Hy=C_n.
$$

对 $H$ 使用 Rayleigh 最小值原理即得

$$
\lambda_2(L)=\lambda_{\min}(H)
\le\frac{y^{\mathsf T}Hy}{y^{\mathsf T}y}=\frac{C_n}{R(c)}.
$$

这里的 Rayleigh 原理是与 Cruz Ortega–Menéndez-Conde，§3 相同的有限维变分原理；
试探向量是在边空间中构造的，不以电导的反射对称性为前提。

若乘积界取等号，则 $y$ 的 Rayleigh 商等于 $H$ 的最小特征值。
在 $H$ 的正交特征基中，将 $y$ 展为 $\sum_\ell\alpha_\ell u_\ell$，有

$$
0=y^{\mathsf T}(H-\lambda_{\min}(H)I)y
=\sum_\ell(\mu_\ell-\lambda_{\min}(H))\alpha_\ell^2.
$$

各项非负，故所有非零分量都属于最小特征空间，
$Hy=ky$，其中 $k=\lambda_2(L)>0$。逐坐标写出这个等式为

$$
\sqrt{c_i}\,d_i=k\frac{s_i}{\sqrt{c_i}},
\qquad\text{即}\qquad c_i=k\frac{s_i}{d_i}.
$$

反过来，设 $c_i=ks_i/d_i$ 对同一个 $k>0$ 成立。
则仍有 $Hy=ky$，但还须证明 $k$ 为最小特征值。
为此使用经典的正基态平方和恒等式；参见 Keller–Pinchover–Pogorzelski，
[*From Hardy to Rellich inequalities on graphs*, arXiv:1909.02286v1](https://arxiv.org/pdf/1909.02286v1)，
§6，定理 6.1 证明中引用的 ground state transform。
在这里图的顶点是边指标 $1,\ldots,n-1$，相邻耦合为
$a_i=\sqrt{c_i c_{i+1}}$，顶点测度为 $1$，
Schrödinger 算子为 $H-kI$，其严格正零解为 $y$。
不需要该文的无穷图或 Rellich 不等式假设；所用的有限恒等式如下，对每个
$z\in\mathbb R^{n-1}$ 都有

$$
z^{\mathsf T}(H-kI)z
=\sum_{i=1}^{n-2}a_i y_i y_{i+1}
\left(\frac{z_i}{y_i}-\frac{z_{i+1}}{y_{i+1}}\right)^2\ge0.
$$

为核对恒等式，$Hy=ky$ 的第 $i$ 个坐标给出

$$
(H_{ii}-k)y_i=a_{i-1}y_{i-1}+a_i y_{i+1},
$$

其中越出指标范围的项取零。展开平方，$z_i^2$ 的系数即为 $H_{ii}-k$，
相邻交叉项为 $-2a_i z_i z_{i+1}$，与左边一致。
所有 $y_i$ 严格为正，因此这些除法合法。
这证明 $H-kI$ 半正定；又 $Hy=ky$ 且 $y\ne0$，故
$\lambda_{\min}(H)=k$，从而 $\lambda_2(L)=k$。
当 $n=2$ 时右边为空和，上述等式直接给出 $H-kI=0$，没有遗漏低阶情形。

最后，由 $D d=k s$ 得

$$
Lv=BDB^{\mathsf T}Bs=BDTs=BDd=kBs=kv.
$$

且 $R(c)=\sum_i s_i d_i/k=C_n/k$。因此乘积等号确实成立，
$k$ 是实际的最小正特征值，等号条件也已双向证明。证毕。

本定理的文献对应是 Cruz Ortega–Menéndez-Conde，§1 的一般路径问题及 §5 的
固定总电阻目标；其中 $P_3,P_4$ 的小阶结论在该文给出。
这里 $n\ge5$ 的结论是同一全点对约束下的完整路径族推导。
树电阻公式、Rayleigh 原理与正基态恒等式仅为上述证明的经典中间步骤。

## 3. 固定电阻的唯一最大值与约束边界

**推论 3.1（任意电阻水平的唯一优化权重）。** 对每个整数 $n\ge2$ 和每个实数
$R_0>0$，在所有满足 $R(c)=R_0$ 的 $c\in(0,\infty)^{n-1}$ 中，
$\lambda_2(L(c))$ 的最大值为 $C_n/R_0$，且恰在一个电导向量处取得：

$$
c_i^\star=\frac{C_n}{R_0}\frac{s_i}{d_i}\qquad(1\le i<n).
$$

该向量的最小正特征值就是 $C_n/R_0$，并满足
$c_i^\star=c_{n-i}^\star$。特别地，取

$$
R_0=R(P_n)=\frac{n(n^2-1)}6,
$$

则最大值为 $6C_n/[n(n^2-1)]$。

**证明。** 定理 2.1 给出对所有可行正电导的上界 $C_n/R_0$。
令 $k=C_n/R_0>0$，由于每个 $s_i,d_i$ 都严格为正，
$c_i^\star=ks_i/d_i$ 的每个坐标均为有限正实数，且

$$
R(c^\star)=\frac1k\sum_{i=1}^{n-1}s_i d_i
=\frac{C_n}{k}=R_0.
$$

定理 2.1 的充分性部分给出 $\lambda_2(L(c^\star))=k$，所以这是实际达到的最大值。
若另一个可行向量达到同一最大值，定理 2.1 的必要性部分迫使
$c_i=k's_i/d_i$ 对某个 $k'>0$ 成立；其电阻为 $C_n/k'$，故
$k'=C_n/R_0=k$，于是该向量就是 $c^\star$。这同时证明唯一性，
不依赖可行集合的紧性或极限边界。

由 $s_{n-i}=s_i$ 和 $d_{n-i}=d_i$，立得 $c_i^\star=c_{n-i}^\star$。
路径的自同构由一个端点的像决定，因而只有恒等与次序反射；
所以唯一最大值权重在全部自同构下不变。这个对称性是结论，
可行竞争者仍遍历全部严格正电导。

在无权路径上，每个 $c_i=1$，利用定理 2.1 中引用的路径电阻公式得

$$
R(P_n)=\sum_{i=1}^{n-1}i(n-i)
=n\frac{n(n-1)}2-\frac{n(n-1)(2n-1)}6
=\frac{n(n^2-1)}6.
$$

代入 $R_0$ 即得所述无权参考水平的最大值。

与已有小阶公式的对应如下，均是上述同一公式的归一化检验。
$n=2$ 时 $s_1=1,d_1=2,C_2=2$，给出
$c_1^\star=1/R_0$ 和 $\lambda_2=2/R_0$。
$n=3$ 时 $s_1=s_2=\sqrt2$、$d_1=d_2=\sqrt2$、$C_3=4$，
故 $R_0=4$ 时两边电导均为 $1$，最优值为 $1$。
Cruz Ortega–Menéndez-Conde，定理 5.1 使用的边电阻条件
$1/c_1+1/c_2=2$，在全点对约定下正是 $R_0=4$，
因为 $R(c)=2/c_1+2/c_2$；其推论 5.2 的乘积常数为 $4$。

$n=4$ 时

$$
s=(\sqrt3,2,\sqrt3),\qquad
 d=(2\sqrt3-2,4-2\sqrt3,2\sqrt3-2),\qquad C_4=20-8\sqrt3.
$$

因此在 $R_0=10$ 时有

$$
(c_1^\star,c_2^\star,c_3^\star)
=\left(\frac{9-\sqrt3}{10},\frac{8+2\sqrt3}{5},\frac{9-\sqrt3}{10}\right),
\qquad \lambda_2=2-\frac{4\sqrt3}{5}.
$$

这些电导对应 Cruz Ortega–Menéndez-Conde，§5 的标量参数
$r_0=\frac5{13}(3+1/\sqrt3)$、端边电导 $1/r_0$ 与中边电导
$2/(5-3r_0)$。直接代入亦给出

$$
\frac6{(9-\sqrt3)/10}+\frac4{(8+2\sqrt3)/5}
=\frac{10(9+\sqrt3)}{13}+\frac{10(4-\sqrt3)}{13}=10.
$$

这说明所用参数满足全点对电阻条件；小阶值及此参数化均来自上述文献对应。证毕。

推论 3.1 的图类限制不能删去：在 $K_{2,3}$ 上，一侧枢纽关联边电导为 $32/23$、
另一侧为 $16/23$ 时，全点对电阻为 $23/3$，Fiedler 值为 $48/23$；
同一电阻水平下，自同构不变的电导只能全部为 $1$，其 Fiedler 值为 $2$。
这些既有反例数值及推导见
[固定电阻的非不变权重反例](../../../Blueprint/D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.md)。
因此路径结论不推出一般图上的不变最大值，也不提供 $K_{2,m}$ 全部正电导的
最优值、全局上界或达到性结论。

固定全点对电阻、固定电导和与固定相邻点对电阻和是不同的约束。
Ghosh–Boyd–Saberi，§1，式 (2) 和 §5.1 在 $\sum_i c_i=1$ 下最小化总电阻，
路径上的解为 $c_i=s_i/\sum_j s_j$，并非推论 3.1 的目标。
Menéndez-Conde，
[*Isoperimetric inequalities for eigenvalues of the Laplacian on cycles with fixed resistance metric*,
arXiv:1808.07976v2](https://arxiv.org/pdf/1808.07976v2)，摘要及 §3 定义 2，
固定的是相邻点对的有效电阻之和。Rosa–Harman，
[*Laplacian Network Optimization via Information Functions*,
arXiv:2512.19279v1](https://arxiv.org/pdf/2512.19279v1)，§1.1，
讨论增加给定数量的边的网络设计问题。
这些预算约束不能直接替换 $R(c)=R_0$；本推论不作这种替换。

## 追加锚（本行以下为增补区）
