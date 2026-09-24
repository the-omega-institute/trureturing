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

## 5. 临界点下方的尖锐增长与极值形状

**定义 5.1（单峰族与临界距离）。** 沿用定义 1.1、1.2 与定理 2.1，
固定 $z\in C_+$。对 $0<r<1$，令 $q_r=r/(M-1)$，并定义

$$
b^{(r)}(z)=r,\qquad
b^{(r)}(x)=-q_r\ (x\in C_+\setminus\{z\}),\qquad
b^{(r)}(x)=0\ (x\in C_-).
\tag{5.1}
$$

相应核记作 $P_{d,r}$。它属于 $\mathcal K_d^0$，且
$I(P_{d,r})=F_M(r)$。对 $0<c<c_d$ 记
$\delta=c_d-c$、$L_\delta=\log(1/\delta)$、$r_c=F_M^{-1}(c)$。

**定理 5.2（尖锐双对数修正及临界极值形状）。** 固定 $d\ge3$，
令 $n=2^d$、$M=n/2$、$q=1/(M-1)$。当 $c\uparrow c_d$ 时，

$$
\Sigma_d(c)
=\frac{g(r_c)+(M-1)g(r_c/(M-1))}{n}+o(1)
=\frac{L_\delta+\log L_\delta-\log n}{2n}
 +\frac{M-1}{n}g(q)+o(1).
\tag{5.2}
$$

第一式中的 $o(1)$ 非负。每个 $c<c_d$ 的上确界均可达；
当 $c\uparrow c_d$ 时，任何极大化向量 $b_c$ 到下列有限集合的距离趋于零：
在一个奇偶类上取 $s,-s/(M-1),\ldots,-s/(M-1)$，
另一奇偶类全零，其中 $s\in\{-1,1\}$，单峰位置任取。
距离可取 $\mathbb R^n$ 的任意范数。

固定 $d=2$ 时，两个同类坐标必须同时趋向端点，增长式改为

$$
\Sigma_2(c)=\frac14\bigl(L_\delta+\log L_\delta-\log2\bigr)+o(1),
\qquad c\uparrow c_2=\frac{\log2}{2}.
\tag{5.3}
$$

证明。式 (2.3) 使 $I\le c<c_d$ 的所有坐标落在
$[-r_c,r_c]$；两个零和约束与信息约束给出紧可行集，$\sigma$ 在其上连续。
因此存在极大化向量。单峰族给出下界

$$
\Sigma_d(c)\ge
\frac{g(r_c)+(M-1)g(r_c/(M-1))}{n}\longrightarrow\infty.
\tag{5.4}
$$

考虑任意 $c_k\uparrow c_d$ 及相应极大化向量。
在 $[-1,1]^n$ 中取收敛子列，极限记为 $b_*$。
若全部极限坐标均在 $(-1,1)$ 内，则该子列的 $\sigma$ 有界，与 (5.4) 矛盾。
故某一坐标绝对值为一。将 (2.3) 的 Jensen 论证用于此端点，
该奇偶类的信息贡献至少为 $c_d$，另一类非负；
连续性又给出总信息至多为 $c_d$。
严格凸性的等号条件强制同类其余坐标全等于该端点的负值除以 $M-1$，
另一类全零。这既证明极值形状的断言，也说明 $M\ge4$ 时恰有一个端点坐标。

沿该子列将端点坐标记为 $x_*$。式 (2.3) 给出
$g(b_{c_k}(x_*))\le g(r_{c_k})$；其余坐标处 $g$ 连续，故

$$
\limsup_k\left(\Sigma_d(c_k)-\frac{g(r_{c_k})}{n}\right)
\le\frac{M-1}{n}g(q).
\tag{5.5}
$$

若 (5.5) 对整体极限不成立，可取违反它的子列，再按上述紧性论证取子列，
产生矛盾。结合 (5.4) 得到 (5.2) 第一式。
这没有断言单峰族在每个亚临界 $c$ 上都是精确极大化者。

为求第二式，置 $\varepsilon=1-r_c$、$s=\log(1/\varepsilon)$。
由 $\phi'(u)=\operatorname{artanh}u$，直接展开端点和内部点 $q<1$ 得

$$
\delta=\frac{\varepsilon}{2n}
 \left(s+1+\log2+2\operatorname{artanh}q+O(\varepsilon)\right).
\tag{5.6}
$$

取对数先得 $s/L_\delta\to1$，再代回得
$s=L_\delta+\log L_\delta-\log(2n)+o(1)$。
同时 $g(1-\varepsilon)=(s+\log2)/2+o(1)$，
其余有限项趋于 $(M-1)g(q)/n$，给出 (5.2)。
若 $d=2$，定理 3.2 给出精确上界 $g(r_c)/2$，且
$\delta=(\log2-\phi(r_c))/2$
$=\varepsilon(s+1+\log2+O(\varepsilon))/4$。
同样反演便得到 (5.3)。$\square$

## 6. 完整轨迹的方向判别与稀有边

**定义 6.1（等先验方向误差）。** 对单峰核 $P_{d,r}$，以均匀分布启动，
记 $\mathsf Q_{d,r,T}$ 为 $(X_0,\ldots,X_T)$ 的正向律，
$\mathsf Q^{\leftarrow}_{d,r,T}$ 为其倒序律。
两方向各以概率 $1/2$ 选取，观察完整的 $T+1$ 个状态。
最小平均判别错误率为

$$
e_{d,r}(T)=\frac12\sum_{\boldsymbol x}
 \min\{\mathsf Q_{d,r,T}(\boldsymbol x),
        \mathsf Q^{\leftarrow}_{d,r,T}(\boldsymbol x)\}
=\frac{1-\operatorname{TV}(\mathsf Q_{d,r,T},
                          \mathsf Q^{\leftarrow}_{d,r,T})}{2}.
\tag{6.1}
$$

这里 $T$ 计转移数，且判别器知道 $d,r,z$ 及核。置
$H=\{z\}$、$B=C_+\setminus\{z\}$、$Z=C_-$，
用 $Y_t\in\{H,B,Z\}$ 标记 $X_t$ 所在集合。
记 $N_{UV}=\#\{0\le t<T:Y_t=U,Y_{t+1}=V\}$、
$J=N_{ZH}-N_{HZ}$、
$\Delta_U=\mathbf1_{Y_0=U}-\mathbf1_{Y_T=U}$。

**定理 6.2（路径似然的单电流表达）。** 令 $q=q_r$，并置

$$
A=\log\frac{1+r}{1-q},\qquad B_0=\log(1+q),\qquad
C=-\log(1-r),\qquad \mathcal A=A+B_0+C.
\tag{6.2}
$$

每条完整轨迹的方向对数似然比恰为

$$
\log\frac{\mathsf Q_{d,r,T}(\boldsymbol x)}
              {\mathsf Q^{\leftarrow}_{d,r,T}(\boldsymbol x)}
=\mathcal A J+A\Delta_H-B_0\Delta_Z.
\tag{6.3}
$$

特别地，$(J,Y_0,Y_T)$ 保留完整轨迹对这两个方向假设的全部似然信息。
此外有有限参数误差界

$$
\left|2e_{d,r}(T)-\mathsf Q_{d,r,T}(N_{ZH}=0)\right|
\le\frac2n+\frac{T(1-r)}{2n}+B_0+
       \frac{(1-r)(1-q)}{1+r}.
\tag{6.4}
$$

证明。均匀初始质量在路径比中相消。
同一集合内两状态间的正反转移比为一；三个有向跨集合边
$H\to B$、$B\to Z$、$Z\to H$ 的对数比分别为 $A,B_0,C$。
记对应净计数为 $J_{HB},J_{BZ},J$。
一条有限路径在每个集合上的流量平衡给出

$$
J_{HB}-J=\Delta_H,\qquad
J_{BZ}-J_{HB}=\Delta_B,
\qquad \Delta_H+\Delta_B=-\Delta_Z.
\tag{6.5}
$$

将它们代入 $AJ_{HB}+B_0J_{BZ}+CJ$ 即得 (6.3)。
这里使用的是有限马尔可夫网络的标准循环分解思想；
本族的精确系数与下面的误差界由上述转移概率直接确定。

以正向律取期望，若以 $S$ 记 (6.3) 的左边，则
$2e=\mathbb E\min(1,e^{-S})$。
平稳性给出端点命中 $H$ 的概率至多为 $2/n$，而

$$
\mathbb E N_{HZ}=\frac{T(1-r)}{2n}.
\tag{6.6}
$$

排除端点命中 $H$ 及 $N_{HZ}>0$ 这两个事件后，
$S=\mathcal A N_{ZH}-B_0\Delta_Z$。
若 $N_{ZH}=0$，$\min(1,e^{-S})$ 与一相差至多 $B_0$；
若 $N_{ZH}\ge1$，该量至多为
$e^{-\mathcal A+B_0}=(1-r)(1-q)/(1+r)$。
在排除事件上两被比较量均在 $[0,1]$ 中。
由并集界及 Markov 不等式得到 (6.4)。$\square$

**定理 6.3（方向误差的泊松尺度与无界不可逆率）。** 令
$d\to\infty$、$n=2^d$，对每个 $d$ 任选 $r_d\in(0,1)$ 满足 $r_d\to1$。
若整数 $T_d\ge0$ 满足 $T_d/n\to\lambda\in[0,\infty)$，则在正向律下

$$
N_{ZH}\ \xrightarrow{\mathrm d}\ \operatorname{Poisson}(\lambda/2),
\qquad
\boxed{\ \lim_{d\to\infty}e_{d,r_d}(T_d)=\frac12e^{-\lambda/2}.\ }
\tag{6.7}
$$

若 $T_d/n\to\infty$，则 $e_{d,r_d}(T_d)\to0$。
对任意固定 $0<\eta<1/2$，定义达到误差 $\eta$ 所需的最小完整轨迹长度

$$
T_\eta(d,r_d)=\min\{T\ge0:e_{d,r_d}(T)\le\eta\}.
$$

则有精确尺度

$$
\frac{T_\eta(d,r_d)}{n}\longrightarrow2\log\frac1{2\eta}.
\tag{6.8}
$$

这些结论与不可逆率的发散速度无关。例如取
$r_d=1-e^{-n^2}$，则全部核严格为正，所有真子坐标过程仍为均匀独立过程，且

$$
nI(P_{d,r_d})\longrightarrow\log2,\qquad
\frac{\sigma(P_{d,r_d})}{n}\longrightarrow\frac12,
\qquad
T_d=o(n)\ \Longrightarrow\ e_{d,r_d}(T_d)\longrightarrow\frac12.
\tag{6.9}
$$

证明。记 $E_t=\{Y_t=Z,Y_{t+1}=H\}$。
$Z$ 的平稳质量为 $1/2$，每个 $Z$ 中的状态下一步到 $z$ 的概率为 $1/n$，
所以 $\Pr(E_t)=1/(2n)$，与 $r$ 无关。
定理 2.1 的 $P^2=\Pi$ 还给出如下精确独立性：
若相邻选定时刻相距至少三，则相应的 $E_t$ 联合独立。
因为前一对状态的末端到后一对的起端至少有两步，
条件分布已恢复均匀，递归条件化即可。

对任何 $k$ 个不同的指定时刻，无论是否相近，它们的共同发生概率至多为 $n^{-k}$。
这是因为按时间先后条件化时，每个事件均须从 $Z$ 作一次概率恰为 $1/n$ 的跃迁到 $z$；
不能共同发生的事件组合概率为零。
固定 $k\ge2$，$T$ 个时刻中包含间距一或二的 $k$ 元集合只有 $O_k(T^{k-1})$ 个。
因而对 $N=N_{ZH}$，当 $T/n\to\lambda>0$ 时，

$$
\mathbb E\binom Nk
=\binom Tk(2n)^{-k}+O_k(T^{k-1}n^{-k})
\longrightarrow\frac{(\lambda/2)^k}{k!}.
\tag{6.10}
$$

$k=0,1$ 的公式直接成立，且对所有 $k$ 有
$\mathbb E\binom Nk\le(T/n)^k/k!$。
对 $u\in[0,1]$ 展开 $u^N=(1+(u-1))^N$，
此界允许逐项取极限，给出
$\mathbb E u^N\to\exp((\lambda/2)(u-1))$。
这是泊松分布的概率生成函数；在 $u=0$ 处同时得到
$\Pr(N=0)\to e^{-\lambda/2}$。
若 $\lambda=0$，$\Pr(N>0)\le T/(2n)\to0$，结论相同。

由于 $q_{r_d}\to0$、$1-r_d\to0$，(6.4) 的右边在 $T_d/n$ 有界时趋于零，
故得 (6.7)。当 $T_d/n\to\infty$ 时，对每个固定 $K>0$，
只观察前 $\lfloor Kn\rfloor$ 步便得
$\limsup e_{d,r_d}(T_d)\le e^{-K/2}/2$；再令 $K\to\infty$。
同样，由误差随 $T$ 单调不增，将 (6.7) 分别用于
$\lambda$ 略小于及略大于 $2\log(1/(2\eta))$ 的情形，夹逼出 (6.8)。
对于每个固定的 $d,r>0$，此最小值确实存在：
间隔两步抽取的相邻状态对独立同律，正反联合律不同，
对一个概率不同的事件使用样本频率即可将判错率降到零。

最后，(5.1) 与 (2.2) 给出

$$
nI(P_{d,r_d})=\phi(r_d)+(M-1)\phi(r_d/(M-1)),
$$

$$
\sigma(P_{d,r_d})
=\frac{g(r_d)+(M-1)g(r_d/(M-1))}{n}.
\tag{6.11}
$$

因 $\phi(u)=u^2/2+O(u^4)$、$g(u)=u^2+O(u^4)$，
两个式子的非单峰部分均为 $O(1/n)$。
$r_d=1-e^{-n^2}$ 时，$\phi(r_d)\to\log2$，
$g(r_d)=(n^2+\log2)/2+o(1)$。
这证明 (6.9) 的两个数值极限；方向误差则由 (6.7) 的 $\lambda=0$ 得到。
完整路径的方向相对熵虽为 $T\sigma$，它不决定等先验的有限轨迹判错率。
式 (6.3) 将这种差异定位于同一轨迹上的稀有 $Z\to H$ 边及其逆边。$\square$

## 追加锚（本行以下为增补区）
