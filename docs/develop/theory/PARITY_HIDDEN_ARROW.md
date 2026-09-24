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

这里 $T$ 是预先确定的转移数，且判别器知道 $d,r,z$ 及核。
固定时域的式 (6.1) 与序贯似然阈值的平均停时是不同统计量；
后者与路径相对熵的关系见
[Roldán 等（2015），式 (1)–(6)](../../../Library/Dynamics/roldan2015arrow.md)，
其中式 (4) 的平均停时等式要求似然过程连续，并含超额项。
本章允许随 $d$ 增大的对数似然跳幅。置
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
这里使用的是有限马尔可夫网络的标准循环分解思想，参见
[Schnakenberg（1976），第 VIII–IX 节](../../../Library/Dynamics/schnakenberg1976network.md)；
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

证明。局部依赖稀有事件的泊松近似已有一般定理，见
[Arratia–Goldstein–Gordon（1990），定理 1](../../../Library/Dynamics/arratia1990poisson.md)。
这里直接以因子矩证明所需的计数极限，再由 (6.4) 得到本族的最优判错曲线。
记 $E_t=\{Y_t=Z,Y_{t+1}=H\}$。
$Z$ 的平稳质量为 $1/2$，每个 $Z$ 中的状态下一步到 $z$ 的概率为 $1/n$，
所以 $\Pr(E_t)=1/(2n)$，与 $r$ 无关。
定理 2.1 的 $P^2=\Pi$ 还给出如下精确独立性：
若相邻选定时刻相距至少三，则相应的 $E_t$ 联合独立。
因为前一对状态的末端到后一对的起端至少有两步，
条件分布已恢复均匀，递归条件化即可。

对任何 $k$ 个不同的指定时刻，无论是否相近，它们的共同发生概率至多为 $n^{-k}$。
这是因为对完整自然滤过 $\mathcal F_t$，
$\Pr(E_t\mid\mathcal F_t)=\mathbf1_{Y_t=Z}/n\le1/n$；
按时间先后条件化即可，不能共同发生的事件组合概率为零。
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
抽取 $(X_{3j},X_{3j+1})$，这些相邻状态对独立同律，正反联合律不同，
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
稀有高耗散轨迹使平均耗散大而整体时间不对称性小的机制，已有
[Feng–Crooks（2008），式 (14)–(16)](../../../Library/Dynamics/fengcrooks2008arrow.md)
的先例；这里的 (6.7)–(6.8) 求出了本核族在 $T/n$ 尺度上的完整误差曲线和常数。
式 (6.3) 将这种差异定位于同一轨迹上的稀有 $Z\to H$ 边及其逆边。$\square$

**定理 6.4（稀有边等待的精确生成函数）。** 固定 $d\ge2$、$0<r<1$，
在定义 6.1 的平稳正向链中，令
$\tau=\min\{t+1:Y_t=Z,Y_{t+1}=H\}$，并记
$s_T=\Pr(\tau>T)$、$p=1/(2n)$、$\varepsilon=1-r$。
则 $\tau$ 几乎必然有限，且

$$
s_0=1,\quad s_1=1-p,\quad s_2=1-2p,\qquad
s_{T+3}=s_{T+2}-p\varepsilon s_{T+1}-pr s_T\quad(T\ge0).
\tag{6.12}
$$

因此对 $0\le u\le1$，

$$
\sum_{T\ge0}s_Tu^T
=\frac{1-pu-pru^2}{1-u+p\varepsilon u^2+pru^3},
\qquad
\boxed{\ \mathbb E\tau=2n-1-r.\ }
\tag{6.13}
$$

证明。$Y_t$ 本身为马尔可夫链，因为每个集合中 $a(x)=\chi(x)b(x)$ 恒定。
按 $H,B,Z$ 的次序排列状态，从其转移矩阵中删去 $Z\to H$ 转移得到

$$
K=\begin{pmatrix}
 (1+r)/n &(M-1)(1+r)/n &\varepsilon/2\\
 (1-q_r)/n &(M-1)(1-q_r)/n &(1+q_r)/2\\
 0 &(M-1)/n &1/2
\end{pmatrix},\qquad
w=\left(1/n,(M-1)/n,1/2\right).
\tag{6.14}
$$

于是 $s_T=wK^T\mathbf1$，此处 $K^T$ 表示 $T$ 次幂。
从任意当前集合出发，下一步进入 $Z$ 的概率至少为 $\varepsilon/2$，
再下一步从 $Z$ 进入 $H$ 的概率为 $1/n$。
故每两步条件于尚未出现目标边，其出现概率至少为 $\varepsilon/(2n)>0$，
从而 $s_{2k}\le(1-\varepsilon/(2n))^k$。
这同时证明 $\tau$ 几乎必然有限及尾和可求和。

直接展开 (6.14) 的行列式，利用 $q_r(M-1)=r$ 与 $n=2M$，得到

$$
\det(vI-K)=v^3-v^2+p\varepsilon v+pr.
\tag{6.15}
$$

由 Cayley–Hamilton 恒等式，左乘 $wK^T$、右乘 $\mathbf1$ 即得 (6.12) 的递推。
初值来自单步目标边概率 $p$，以及连续两步不可能都为 $Z\to H$。
对递推求生成函数，分子依次为
$s_0=1$、$s_1-s_0=-p$、$s_2-s_1+p\varepsilon=-pr$，
得到 (6.13) 的有理函数。可求和性允许令 $u=1$，分母为 $p$，
由正整数随机变量的尾和公式，
$\mathbb E\tau=(1-p-pr)/p=2n-1-r$。
该等待时间计到目标边第一次出现；目标边出现前亦可使用端点等信息，
所以它不被等同于定义 6.1 的最优固定时域判别长度。$\square$

## 追加锚（本行以下为增补区）

## 7. 临界邻域的精确单峰极值

**定义 7.1（单峰不可逆率）。** 对 $k=M-1$ 及 $0\le r<1$，记

$$
G_M(r)=\frac{g(r)+k g(r/k)}n.
\tag{7.1}
$$

约定 $P_{d,0}=\Pi$，即将定义 5.1 的单峰族连续延拓到 $r=0$。
本章仍在固定 $d\ge3$ 的 $\mathcal K_d^0$ 内取极值。
其约束可表成固定中点的散度问题：令 $\mu_\pm(x)=(1\pm b(x))/n$，则

$$
\operatorname{JS}(\mu_+,\mu_-)=I(P),\qquad
D(\mu_+\Vert\mu_-)+D(\mu_-\Vert\mu_+)=4\sigma(P).
\tag{7.2}
$$

这里 $\operatorname{JS}$ 取等权混合，每个原子的中点质量固定为 $1/n$，
且两测度在每个奇偶类上的质量均为 $1/2$。
[Harremoës–Vajda 的散度联合值域定理（定理 8）](../../../Library/Dynamics/harremoes2010divergences.md)
允许改变支撑权重；其二点分布凸组合约化不保持这里的固定中点与奇偶类约束。

**定理 7.2（临界邻域的精确极值及全部等号情形）。** 对每个固定 $d\ge3$，
存在 $c_*(d)\in(0,c_d)$，使对所有 $c_*(d)<c<c_d$，

$$
\boxed{\quad \Sigma_d(c)=G_M(r_c),\qquad r_c=F_M^{-1}(c).\quad}
\tag{7.3}
$$

全部极大化向量恰为：选择一个奇偶类和其中一个位置，在该位置取 $s r_c$，
同类其余位置取 $-s r_c/(M-1)$，另一类全零，其中 $s\in\{-1,1\}$。
此结论加强定理 5.2 的渐近式；这里只断言一个临界左邻域，不指定其最大长度。

证明。紧性与可达性已由定理 5.2 给出。对任意可行 $b$，置
$r=\max_x|b(x)|\le r_c$。信息与不可逆率均不随整体变号、类内置换或交换两类而变，
故可令 $x_*\in C_+$ 且 $b(x_*)=r$。以 $b^*(r)$ 表示同一位置的正单峰向量，置
$D=I(b)-F_M(r)\ge0$。在非峰值坐标处展开 $\phi$，由 $\phi''\ge1$ 得

$$
D\ge\frac1{2n}\sum_{x\ne x_*}\bigl(b(x)-b^*(r)(x)\bigr)^2.
\tag{7.4}
$$

线性项在 $C_+\setminus\{x_*\}$ 和 $C_-$ 上分别相消，因为各组参考值恒定，
且各组偏差之和均为零。又因 $I(b)\le c<c_d$，

$$
D\le c_d-F_M(r),\qquad
\max_{x\ne x_*}|b(x)|
\le\frac1k+\sqrt{2n\bigl(c_d-F_M(r)\bigr)}.
\tag{7.5}
$$

固定 $R\in(1/k,1)$。当 $r$ 足够接近 $1$ 时，(7.5) 使全部非峰值坐标及其参考值
都落在 $[-R,R]$。在此区间 $g''(u)=2/(1-u^2)^2\le K$，其中
$K=2/(1-R^2)^2$。再次用线性项相消、Taylor 余项界及 (7.4)，有

$$
\sigma(b)-G_M(r)
\le\frac K{2n}\sum_{x\ne x_*}\bigl(b(x)-b^*(r)(x)\bigr)^2
\le K D.
\tag{7.6}
$$

另一方面，

$$
\frac{G_M'(r)}{F_M'(r)}
=\frac{g'(r)+g'(r/k)}{h(r)+h(r/k)}\longrightarrow\infty,
\qquad g'(r)=h(r)+\frac r{1-r^2}.
\tag{7.7}
$$

因此可固定 $r_0<1$，使 (7.5)–(7.6) 对 $r\ge r_0$ 均适用，且
$G_M'/F_M'>K$ 在 $[r_0,1)$ 上成立。
再取 $c_*\in(F_M(r_0),c_d)$，使 $G_M(F_M^{-1}(c_*))>g(r_0)$；
这是可能的，因为 $G_M(r)\to\infty$。

若 $c>c_*$ 而 $r\le r_0$，则 $\sigma(b)\le g(r_0)<G_M(r_c)$。
若 $r_0<r<r_c$，积分 (7.7) 得

$$
G_M(r_c)-G_M(r)>K\bigl(F_M(r_c)-F_M(r)\bigr)
=K\bigl(c-F_M(r)\bigr)\ge K D.
\tag{7.8}
$$

与 (7.6) 合用仍得严格劣于单峰。
最后，若 $r=r_c$，可行性强迫 $D=0$，由 (7.4) 得 $b=b^*(r_c)$。
恢复三种对称操作即得全部等号情形。$\square$

## 8. 全核族的两标量方向判别谱

**定义 8.1（路径亲和矩阵与误差指数）。** 固定 $P\in\mathcal K_d^0$，
令 $\mathsf W_{P,T}$ 为均匀启动的 $T$ 步路径律，$\mathsf W_{P,T}^{\leftarrow}$ 为倒序律。
记等先验最小错误率为 $e_P(T)$，定义

$$
R_{xy}=\sqrt{P(x,y)P(y,x)},\qquad
\mathcal H_P(T)=\sum_{\boldsymbol x}
 \sqrt{\mathsf W_{P,T}(\boldsymbol x)\mathsf W_{P,T}^{\leftarrow}(\boldsymbol x)},
\qquad
\eta_p=\frac1M\sum_{x\in C_p}\sqrt{1-b(x)^2}\quad(p\in\{+,-\}).
\tag{8.1}
$$

路径亲和度的矩阵表达式是经典马尔可夫 Bhattacharyya 递推，见
[Daskalakis–Dikkala–Gravin，引理 5、式 (5)](../../../Library/Dynamics/daskalakis2018testing.md)，
该处将此递推归于 Kazakos；引理本身不要求转移矩阵对称。

**定理 8.2（秩四约化、四次方程与精确错误指数）。** 对定义 8.1 的任意核，
令 $\mathbf1$ 为全一列向量，并置

$$
u_p(x)=\mathbf1_{C_p}(x)\sqrt{1+b(x)},\qquad
v_p(x)=\mathbf1_{C_p}(x)\sqrt{1-b(x)}.
$$

则

$$
R=\frac1n\bigl(u_+u_+^\top+u_-u_-^\top+v_+v_-^\top+v_-v_+^\top\bigr),
\qquad \operatorname{rank}R\le4,\qquad
\mathcal H_P(T)=\frac1n\mathbf1^\top R^T\mathbf1.
\tag{8.2}
$$

$R$ 的 Perron 特征值为 $\lambda=(1+z)/2$，其中 $z\in(0,1]$ 是方程

$$
\boxed{\quad z^2(1+z)^2=(z+\eta_+^2)(z+\eta_-^2)\quad}
\tag{8.3}
$$

的唯一正根。固定 $d$ 与核 $P$ 后，错误指数存在，且

$$
C_{\rm path}(P):=\lim_{T\to\infty}-\frac1T\log e_P(T)
=-\log\lambda.
\tag{8.4}
$$

所以长期指数只依赖两个标量 $(\eta_+,\eta_-)$；有限时域的 $\mathcal H_P(T)$
仍由 (8.2) 中的向量决定。$C_{\rm path}=0$ 当且仅当 $b\equiv0$。

证明。同类边给出 $\sqrt{(1+b(x))(1+b(y))}/n$，异类边给出
$\sqrt{(1-b(x))(1-b(y))}/n$，逐块得到 (8.2) 的矩阵分解。
路径概率相乘再求和得到其中的亲和度公式。
零和约束还给出

$$
\|u_p\|^2=\|v_p\|^2=M,\qquad u_p^\top v_p=M\eta_p.
\tag{8.5}
$$

试取正系数的向量 $h=a_+u_++a_-u_-+c_+v_++c_-v_-$。
下列系数等式足以保证 $Rh=((1+z)/2)h$：

$$
z a_+=\eta_+c_+,\qquad z a_-=\eta_-c_-,\qquad
(1+z)c_+=\eta_-a_-+c_-,\qquad
(1+z)c_-=\eta_+a_++c_+.
\tag{8.6}
$$

消去 $a_\pm$ 后，两式的相容条件正是 (8.3)。
由于 $0<\eta_\pm\le1$，函数

$$
f(z)=\frac{z^2(1+z)^2}{(z+\eta_+^2)(z+\eta_-^2)}\quad(z>0)
$$

严格递增：其对数导数为
$2/z+2/(1+z)-1/(z+\eta_+^2)-1/(z+\eta_-^2)>0$。
又 $f(0+)=0$ 且 $f(1)\ge1$，故正根唯一且至多为 $1$。
对该根，(8.6) 可选全部系数为正，从而 $h>0$。
$R$ 逐项正，故此特征值即 Perron 值。
这个构造不要求四个生成向量线性独立，也包括某个 $\eta_p=1$ 的退化情形。

为从亲和度得到精确错误指数，将 $h$ 归一化为 $\sum_xh_x^2=1$，并定义

$$
\widehat P(x,y)=\frac{R_{xy}h_y}{\lambda h_x},\qquad \widehat\pi(x)=h_x^2.
\tag{8.7}
$$

此 Perron 归一化是可逆核族的已知 $e$ 投影构造，见
[Wolfer–Watanabe，定理 7](../../../Library/Dynamics/wolfer2021reversible.md)；
严格正性满足其共同支持强连通的假设。这里 $\widehat P$ 逐项正，且
$\widehat\pi(x)\widehat P(x,y)=h_xR_{xy}h_y/\lambda$
关于 $x,y$ 对称。因此它平稳且可逆。
在该平稳路径律 $\widehat{\mathbb P}$ 下，置

$$
S_T=\sum_{t=0}^{T-1}\log\frac{P(X_t,X_{t+1})}{P(X_{t+1},X_t)}.
$$

边增量反对称而平稳边律对称，故均值为零；有限正链的遍历定理给出
$S_T/T\to0$ 几乎处处。直接比较路径质量得到精确恒等式

$$
e_P(T)=\frac{\lambda^T}{2n}
\widehat{\mathbb E}\!\left[
\frac{\exp(-|S_T|/2)}{h_{X_0}h_{X_T}}\right].
\tag{8.8}
$$

固定 $P$ 时，端点因子有正的上下界。期望的上界为常数；
对任意 $\epsilon>0$，其下界为某个正的常数乘以
$e^{-\epsilon T/2}\widehat{\mathbb P}(|S_T|\le\epsilon T)$。
后者概率趋于 $1$，因此期望不贡献指数率，证明 (8.4)。
最后 $\lambda=1$ 等价于 $z=1$，由 (8.3) 等价于 $\eta_+=\eta_-=1$，
又等价于每个 $b(x)=0$。$\square$

**定理 8.3（单峰的三次谱与维数尺度）。** 对正单峰核 $P_{d,r}$，

$$
\eta_- =1,\qquad
\eta_+=\frac{\sqrt{1-r^2}+(M-1)\sqrt{1-r^2/(M-1)^2}}M.
\tag{8.9}
$$

其 Perron 值为 $(1+z)/2$，其中 $z>0$ 唯一满足

$$
z^3+z^2-z-\eta_+^2=0.
\tag{8.10}
$$

当 $n=2^d\to\infty$ 时，一致地对 $0\le r<1$ 有

$$
C_{\rm path}(P_{d,r})
=\frac{1-\sqrt{1-r^2}}{2n}+O(n^{-2}).
\tag{8.11}
$$

特别地，对任意 $r_d\to1$，有 $nC_{\rm path}(P_{d,r_d})\to1/2$。

证明。在 (8.3) 中代入 $\eta_-=1$ 并除以 $1+z$，得到 (8.10)。
置 $a=1-\sqrt{1-r^2}\in[0,1]$。对 (8.9) 中的第二个平方根一致展开得

$$
\eta_+=1-\frac{2a}n+O(n^{-2}),\qquad
\eta_+^2=1-\frac{4a}n+O(n^{-2}).
$$

三次式在 $(z,\eta_+^2)=(1,1)$ 处对 $z$ 的导数为 $4$，
故 $z=1-a/n+O(n^{-2})$，从而
$-\log((1+z)/2)=a/(2n)+O(n^{-2})$。各余项均与 $r$ 无关。$\square$

## 9. 独立状态对与连续轨迹的不同判别曲线

**定义 9.1（独立状态对实验）。** 对已知核 $P\in\mathcal K_d^0$，记
$Q_P(x,y)=P(x,y)/n$、$Q_P^\top(x,y)=Q_P(y,x)$。
观察 $m$ 个独立状态对，两假设分别为 $Q_P^{\otimes m}$ 和
$(Q_P^\top)^{\otimes m}$，等先验错误率记为 $e_P^{\rm pair}(m)$。
置

$$
U_p=\sum_{x\in C_p}\sqrt{1+b(x)},\qquad
V_p=\sum_{x\in C_p}\sqrt{1-b(x)},\qquad
\rho_P=\sum_{x,y}\sqrt{Q_P(x,y)Q_P(y,x)}.
\tag{9.1}
$$

**定理 9.2（独立对的精确亲和度与临界窗口）。** 对定义 9.1 的核，

$$
\operatorname{TV}(Q_P,Q_P^\top)=\frac1{2n^2}\sum_{x,y}|b(x)-b(y)|,
\qquad
\rho_P=\frac{U_+^2+U_-^2+2V_+V_-}{n^2},
\tag{9.2}
$$

且固定核的错误指数为

$$
C_{\rm pair}(P):=\lim_{m\to\infty}-\frac1m\log e_P^{\rm pair}(m)
=-\log\rho_P.
\tag{9.3}
$$

对正单峰，置 $k=M-1$、
$A_r=\sqrt{1+r}+k\sqrt{1-r/k}$、
$B_r=\sqrt{1-r}+k\sqrt{1+r/k}$，则

$$
\operatorname{TV}(Q_{P_{d,r}},Q_{P_{d,r}}^\top)=\frac{3r}{2n},\qquad
\rho_{P_{d,r}}=\frac{A_r^2+M^2+2MB_r}{n^2},
\tag{9.4}
$$

并且一致地对 $0\le r<1$，

$$
C_{\rm pair}(P_{d,r})
=\frac{2-\sqrt{1+r}-\sqrt{1-r}}n+O(n^{-2}).
\tag{9.5}
$$

令 $d\to\infty$、$r_d\to1$、$m_d/n\to\tau\in[0,\infty)$。
若 $N_1,N_2$ 为独立的 Poisson 随机变量，均值分别为 $\tau,\tau/2$，则

$$
\boxed{\quad
 e_{P_{d,r_d}}^{\rm pair}(m_d)
 \longrightarrow e^{-\tau/2}
 \left(\Pr(N_1<N_2)+\tfrac12\Pr(N_1=N_2)\right).
\quad}
\tag{9.6}
$$

当 $\tau>0$ 时，(9.6) 严格小于定理 6.3 的连续轨迹极限
$\tfrac12e^{-\tau/2}$。两个固定核指数的大维数极限也不同：
$nC_{\rm pair}\to2-\sqrt2$，而 $nC_{\rm path}\to1/2$。
两种指数极限均先在固定核下取样本数趋于无穷；(9.6) 则直接处理联合极限。

证明。$Q_P(x,y)-Q_P(y,x)=\chi(x)\chi(y)(b(x)-b(y))/n^2$，
给出全变差公式。亲和度按同类与异类边分块即得 (9.2)。
为证明 (9.3)，令
$\widetilde Q(x,y)=\sqrt{Q_P(x,y)Q_P(y,x)}/\rho_P$。
该概率律在交换坐标下不变，故单对对数似然比在其下均值为零。
对 $m$ 个独立的 $\widetilde Q$ 样本，以 $L_m$ 记总对数似然比，直接得到

$$
e_P^{\rm pair}(m)=\frac{\rho_P^m}2
\widetilde{\mathbb E}\bigl[e^{-|L_m|/2}\bigr].
\tag{9.7}
$$

由大数律 $L_m/m\to0$，如同 (8.8) 的上下界论证得到 (9.3)。
这是对转置假设的标准 Chernoff 中点倾斜论证。

在单峰族中，$b$ 的三组取值为 $r,-r/k,0$，组大小为 $1,k,M$。
不同组间绝对差的无序加权和为
$k(r+r/k)+Mr+kM(r/k)=3Mr$；计入两个顺序后得到 (9.4) 的全变差。
代入四个平方根和得到其亲和度。又一致地有

$$
A_r=M+\sqrt{1+r}-1-r/2+O(n^{-1}),\qquad
B_r=M+\sqrt{1-r}-1+r/2+O(n^{-1}).
$$

因此 $1-\rho_{P_{d,r}}=(2-\sqrt{1+r}-\sqrt{1-r})/n+O(n^{-2})$，
取负对数即为 (9.5)。

下面直接证明联合极限。以 $H,B,Z$ 记定义 6.1 的三个状态类，
但现在 $N_{UV}$ 计数的是独立样本对。置 $q=r/k$，仍用

$$
A=\log\frac{1+r}{1-q},\qquad B_0=\log(1+q),\qquad C=-\log(1-r).
$$

总对数似然比精确等于

$$
L_m=A(N_{HB}-N_{BH})+C(N_{ZH}-N_{HZ})
       +B_0(N_{BZ}-N_{ZB}).
\tag{9.8}
$$

在正向律下，四种稀有类别 $(HB,BH,HZ,ZH)$ 的单次概率分别为

$$
\frac{k(1+r)}{n^2},\quad \frac{k(1-q)}{n^2},\quad
\frac{1-r}{2n},\quad \frac1{2n}.
\tag{9.9}
$$

多项分布的概率母函数为
$\bigl(1+\sum_jp_j(t_j-1)\bigr)^m$。
沿给定序列它趋向
$\exp(\tau(t_1-1)+\frac\tau2(t_2-1)+\frac\tau2(t_4-1))$。
故四个计数联合趋于独立 Poisson 变量，均值分别为
$(\tau,\tau/2,0,\tau/2)$；特别地 $\Pr(N_{HZ}>0)\to0$。

背景类别满足
$p_{BZ}-p_{ZB}=kMq/n^2=r/(2n)$。
独立性给出 $\operatorname{Var}(N_{BZ}-N_{ZB})\le m$，故当 $m=O(n)$ 时，

$$
\mathbb E[B_0(N_{BZ}-N_{ZB})]=O(n^{-1}),\qquad
\operatorname{Var}[B_0(N_{BZ}-N_{ZB})]=O(n^{-1}).
\tag{9.10}
$$

所以背景对数似然趋零。又 $A\to\log2$、$C\to\infty$。
在 $N_{HZ}=0,N_{ZH}>0$ 上，稀有计数的紧性与 (9.10) 使
$\min(1,e^{-L_m})$ 依概率趋零；在 $N_{HZ}=N_{ZH}=0$ 上，
其极限为 $\min(1,2^{N_2-N_1})$。
函数有界，计数联合收敛及极限独立性遂给出

$$
\lim e_{P_{d,r_d}}^{\rm pair}(m_d)
=\frac{e^{-\tau/2}}2\mathbb E\min(1,2^{N_2-N_1}).
\tag{9.11}
$$

交换 Poisson 计数 $i,j$ 时，其概率质量之比为 $2^{i-j}$，
所以 (9.11) 等于 (9.6)。当 $\tau>0$，对每个 $i>j$，
$\Pr(N_1=i,N_2=j)>\Pr(N_1=j,N_2=i)$。
求和得到 $\Pr(N_1>N_2)>\Pr(N_1<N_2)$，证明严格比较。$\square$

## 追加锚（本行以下为增补区）

## 10. 两种观察实验的精确似然内积

**定义 10.1（相对于均匀参考律的似然）。** 对 $P_b\in\mathcal K_d^0$，
区分两种实验。路径实验观察均匀启动的 $s$ 步轨迹；状态对实验观察 $s$ 个独立的
$Q_b(x,y)=P_b(x,y)/n$ 样本。两者的正向律分别记为
$\mathsf P^{+,\mathrm{path}}_{b,s}$ 与 $\mathsf P^{+,\mathrm{pair}}_{b,s}$，
反向律由整条路径倒序、或交换每个状态对的两坐标得到。
相应均匀参考律为
$\mathsf U^{\mathrm{path}}_s=\operatorname{Unif}(X)^{\otimes(s+1)}$ 和
$\mathsf U^{\mathrm{pair}}_s=\operatorname{Unif}(X^2)^{\otimes s}$。
对 $E\in\{\mathrm{path},\mathrm{pair}\}$、$\epsilon\in\{+,-\}$，置

$$
L^{\epsilon,E}_{b,s}
=\frac{d\mathsf P^{\epsilon,E}_{b,s}}{d\mathsf U^E_s}.
\tag{10.1}
$$

路径上的两个似然分别为 $\prod_{t<s}nP_b(X_t,X_{t+1})$ 与
$\prod_{t<s}nP_b(X_{t+1},X_t)$；独立状态对上取相应单对因子的乘积。
$s=0$ 时似然恒为 $1$。不致混淆时略去上标 $E$。

**定理 10.2（全核族的交叉乘积与似然正交）。** 对任意
$P_b,P_c\in\mathcal K_d^0$，有

$$
P_bP_c=\Pi.
\tag{10.2}
$$

在定义 10.1 的两种实验中，对每个 $s\ge0$ 都有相同的内积公式

$$
\mathbb E_{\mathsf U^E_s}[L^{\epsilon,E}_{b,s}L^{\epsilon,E}_{c,s}]
=(1+\mathbb E[bc])^s\quad(\epsilon\in\{+,-\}),\qquad
\mathbb E_{\mathsf U^E_s}[L^{+,E}_{b,s}L^{-,E}_{c,s}]=1.
\tag{10.3}
$$

因此，正向与反向的中心化似然所张成的子空间在 $L^2(\mathsf U^E_s)$ 中正交。

对同一 $r\in(0,1)$，以 $b_z$ 表示峰位为 $z\in C_+$ 的正单峰，置
$k=M-1$、$\alpha=r^2/(2k)$、
$\overline L_s^\epsilon=M^{-1}\sum_{z\in C_+}L_{b_z,s}^\epsilon$。则

$$
\mathbb E[L_{b_z,s}^\epsilon L_{b_w,s}^\epsilon]
=\begin{cases}(1+\alpha)^s,&z=w,\\
(1-\alpha/k)^s,&z\ne w,
\end{cases}
\qquad
V_s:=\mathbb E(\overline L_s^\epsilon-1)^2
=\frac{(1+\alpha)^s+k(1-\alpha/k)^s}{M}-1,
\tag{10.4}
$$

且 $\mathbb E(\overline L_s^+-\overline L_s^-)^2=2V_s$。
这里各期望都在各自实验的均匀参考律下取。

证明。令 $A_b=P_b-\Pi$。作为函数算子，
$A_bf=\chi b\,\mathbb E(\chi f)$。
两个奇偶类上的零和约束给出 $\mathbb E b=\mathbb E(\chi b)=0$，
故 $\Pi A_c=A_b\Pi=A_bA_c=0$，证明 (10.2)。

对于路径的同向内积，逐边乘积给出转移矩阵

$$
K_{bc}(x,y)=nP_b(x,y)P_c(x,y)
=\frac{f(x)+g(x)\chi(y)}n,
\qquad f=1+bc,\quad g=\chi(b+c).
\tag{10.5}
$$

由于 $\mathbb E g=0$，每列之和都是 $1+\mathbb E(bc)$。
以 $\pi^\top=n^{-1}\mathbf1^\top$ 记均匀行向量，得到

$$
\mathbb E_{\mathsf U^{\mathrm{path}}_s}[L_{b,s}^+L_{c,s}^+]
=\pi^\top K_{bc}^{,s}\mathbf1=(1+\mathbb E[bc])^s.
$$

反向与反向的情形由参考律在路径倒序下不变得到。
异向内积的矩阵为 $H_{bc}(x,y)=nP_b(x,y)P_c(y,x)$。
由 (10.2)，其每行之和为 $n(P_bP_c)(x,x)=1$，
所以 $\pi^\top H_{bc}^{,s}\mathbf1=1$。
这类逐边乘积的矩阵求和与
[马尔可夫亲和递推](../../../Library/Dynamics/daskalakis2018testing.md)
采用相同的路径求和步骤；这里的列和、行和恒等式来自共同奇偶结构。

对于独立状态对，直接积分单对乘积分别得到
$1+\mathbb E(bc)$ 和 $1+\mathbb E b\,\mathbb E c=1$，再用独立性取 $s$ 次幂。
每个似然的参考期望为一，故中心化后的异向内积为零。
最后，单峰向量满足
$\mathbb E b_z^2=\alpha$、$\mathbb E(b_zb_w)=-\alpha/k$（$z\ne w$）。
代入并展开均值的平方即得 (10.4) 及最后一式。$\square$

**定理 10.3（二步混合与二阶重合的边界）。** 正的双随机矩阵各自满足
$P^2=Q^2=\Pi$，不足以推出路径异向似然的内积为一。
另一方面，即使在本卷的单峰族内，(10.3) 的两种实验内积完全相同，
它们的似然三阶矩仍可不同：当 $d\ge3$、$0<r<1$、$s=2$ 时，置

$$
\beta_3=\mathbb E b_z^3=\frac{r^3(1-k^{-2})}{n}>0,
$$

则

$$
\mathbb E_{\mathsf U^{\mathrm{pair}}_2}[(L^{+,\mathrm{pair}}_{b_z,2})^3]
=(1+3\alpha)^2,
\qquad
\mathbb E_{\mathsf U^{\mathrm{path}}_2}[(L^{+,\mathrm{path}}_{b_z,2})^3]
=(1+3\alpha)^2+3\alpha\beta_3.
\tag{10.6}
$$

证明。第一项反例取 $X=\{-1,1\}^2$、
$P(x,y)=(1+r x_1y_2)/4$、$Q=P^\top$，其中 $0<r<1$。
均匀求和时 $\mathbb E(x_1x_2)=0$，故 $P^2=Q^2=\Pi$。
但 $Q(y,x)=P(x,y)$，因此一步的异向内积为
$\mathbb E_{x,y}(1+r x_1y_2)^2=1+r^2$。
这里不具有 (10.2) 的共同奇偶因子结构。

为证明 (10.6)，将单条边的似然因子立方展开为
$f_3(x)+g_3(x)\chi(y)$，其中
$f_3=1+3b_z^2$、$g_3=\chi(3b_z+b_z^3)$。
因为 $b_z$ 只在 $C_+$ 上非零，

$$
\mathbb E f_3=1+3\alpha,\qquad
\mathbb E g_3=\beta_3,\qquad
\mathbb E(\chi f_3)=3\alpha.
$$

两条独立边给出 $(\mathbb E f_3)^2$。
两条相邻边先对末状态积分，再对前两状态积分，给出
$(\mathbb E f_3)^2+\mathbb E g_3\,\mathbb E(\chi f_3)$。
因此二阶重合并不延伸为全部似然矩相同。$\square$

## 11. 未知峰位的尖锐信息门槛

**定义 11.1（固定未知峰位与最坏方向风险）。** 已知 $d$、$r\in(0,1)$、
正峰符号及其所在的 $C_+$，未知位置 $z\in C_+$ 在整个样本期间保持不变。
对实验 $E\in\{\mathrm{path},\mathrm{pair}\}$，定义允许随机化判别器的风险

$$
\mathcal R^E_{d,r}(s)
=\inf_\delta\ \max_{z\in C_+,\,\epsilon\in\{+,-\}}
\mathsf P^{\epsilon,E}_{b_z,s}\{\delta\ne\epsilon\}.
\tag{11.1}
$$

置 $I=F_M(r)$、$\mu=sI$，并引入偶函数 $\psi$ 与奇函数 $\xi$：

$$
\psi(u)=\frac{(1+u)\log^2(1+u)+(1-u)\log^2(1-u)}2,
\qquad
\xi(u)=\frac{(1+u)\log(1+u)-(1-u)\log(1-u)}2.
\tag{11.2}
$$

以下只在 $|u|<1$ 使用对数。相关的稀疏分布检测文献采用截断似然二阶矩，见
[Bhattacharya–Mukherjee，§5.2.2](../../../Library/Dynamics/bhattacharya2024sparse.md)。
其固定稀疏指数模型不包含这里恰好一个固定峰位及其弥散补偿的约束。

**定理 11.2（单峰似然的精确协方差及一致方差界）。** 在各个似然自身的概率律下，
对任意 $d\ge2$、$0<r<1$、$s\ge0$，有

$$
\mathbb E_{\mathsf P^{\epsilon,E}_{b_z,s}}\log L^{\epsilon,E}_{b_z,s}=sI,
\qquad
\operatorname{Var}_{\mathsf P^{\epsilon,E}_{b_z,s}}
       (\log L^{\epsilon,E}_{b_z,s})\le2sI.
\tag{11.3}
$$

更精确地，在正向平稳路径下置
$\ell_t=\log(nP_{b_z}(X_t,X_{t+1}))$，以及

$$
J=\frac{\xi(r)-k\xi(r/k)}n\le0,
\qquad
v=\frac{\psi(r)+k\psi(r/k)}n-I^2.
\tag{11.4}
$$

则

$$
\operatorname{Cov}(\ell_t,\ell_{t+1})=IJ,\qquad
\operatorname{Cov}(\ell_t,\ell_{t+j})=0\quad(j\ge2),
\tag{11.5}
$$

故 $s\ge1$ 时，路径总对数似然的方差为 $sv+2(s-1)IJ$；
独立状态对实验的方差为 $sv$。

证明。条件于出发状态 $x$ 的对数似然均值为 $F(x)=\phi(b_z(x))$，
二阶矩为 $\psi(b_z(x))$，故每条边的均值是 $I$，方差是 $v$。
对 $u\in[0,1)$，有

$$
(2\phi-\psi)'(u)=-h(u)\log(1-u^2)\ge0.
\tag{11.6}
$$

由零点取值及偶性得到 $\psi(u)\le2\phi(u)$，从而 $v\le2I$。
又 $\xi(0)=0$ 且 $\xi''(u)=-u/(1-u^2)\le0$，
凹性给出 $\xi(r)\le k\xi(r/k)$，所以 $J\le0$。

由于平稳分布均匀，条件于到达状态 $y$ 的上一条边均值为

$$
R(y):=\mathbb E[\ell_{t-1}\mid X_t=y]=I+J\chi(y).
\tag{11.7}
$$

确实，$(1+u)\log(1+u)=\phi(u)+\xi(u)$；在此处以
$u=\chi(x)\chi(y)b_z(x)$ 代入并对 $x$ 均匀求和，
利用单峰支撑在 $C_+$，即得 (11.7)。
函数 $F$ 也只在 $C_+$ 上非零，故
$\mathbb E(\chi F)=I$，以及

$$
P_{b_z}F=I(1+b_z).
\tag{11.8}
$$

马尔可夫性与条件期望于是给出

$$
\mathbb E[\ell_t\ell_{t+1}]=\mathbb E(RF)=I^2+IJ,
\qquad
\mathbb E[\ell_t\ell_{t+2}]
=\mathbb E(RP_{b_z}F)=I^2.
$$

第二式使用 $\mathbb E b_z=\mathbb E(\chi b_z)=\mathbb E\chi=0$。
对 $j\ge3$，$P_{b_z}^{j-1}F=\Pi F=I$，同样得到乘积均值 $I^2$。
求和协方差即得路径方差公式及其上界 $sv\le2sI$。
独立状态对的方差直接相加。反向实验通过倒序或交换坐标变回正向实验，
不改变相应对数似然的分布；$s=0$ 的结论直接成立。$\square$

**定理 11.3（未知峰位的共同尖锐门槛与定位跃迁）。** 对每个固定
$\varepsilon\in(0,1)$、任意序列 $r_d\in(0,1)$ 与非负整数 $s_d$，
令 $d\to\infty$。若充分大的 $d$ 均满足

$$
s_dF_M(r_d)\le(1-\varepsilon)\log M,
$$

则两种实验都满足

$$
\mathcal R^E_{d,r_d}(s_d)\longrightarrow\frac12.
\tag{11.9}
$$

在同一条件下，即使预先告知方向，均匀未知峰位的最优精确定位成功率也趋于零。
若充分大的 $d$ 均满足

$$
s_dF_M(r_d)\ge(1+\varepsilon)\log M,
$$

则在全部 $2M$ 个位置与方向假设中作联合最大似然判别，
其位置或方向判错的最坏概率趋于零，因而

$$
\mathcal R^E_{d,r_d}(s_d)\longrightarrow0.
\tag{11.10}
$$

因此两种实验的一阶临界样本尺度同为

$$
s_*(d,r)=\frac{\log M}{F_M(r)}
=\frac{n\log M}{\phi(r)}\bigl(1+O(M^{-1})\bigr),
\tag{11.11}
$$

其中相对余项一致地适用于 $0<r<1$。特别地，
$r_d\to1$ 时 $s_*\sim n\log n/\log2$；
$r_d\to0$ 时 $s_*\sim2n\log M/r_d^2$。
这里不要求 $r_d$ 趋近端点的速度，亦不判定临界窗口中的极限风险。

证明。先说明最坏风险与均匀先验的关系。
$C_+$ 内的置换在峰位上可迁，倒序或交换坐标把两个方向互换。
将任一随机化判别器对这个有限群平均，同时变换其输出方向，
使全部 $2M$ 个风险相等，且不改变均匀平均风险。
因此以 $\overline{\mathsf P}^{\epsilon,E}_s$ 记均匀峰位混合，有

$$
\mathcal R^E_{d,r}(s)
=\frac{1-\operatorname{TV}(\overline{\mathsf P}^{+,E}_s,
                          \overline{\mathsf P}^{-,E}_s)}2.
\tag{11.12}
$$

这一步只是有限群对称化；混合中的峰位只选一次，不随样本重抽。

以下固定任一实验，省略 $E$。在某一方向分别截断每个分量似然：
对 $h>\mu$ 置

$$
\widetilde L_z=L_{b_z,s}^{\epsilon}
   \mathbf1_{\{\log L_{b_z,s}^{\epsilon}\le h\}},\qquad
\widetilde L=\frac1M\sum_z\widetilde L_z,
\qquad
\delta_h=\mathsf P_{b_z,s}^{\epsilon}
          \{\log L_{b_z,s}^{\epsilon}>h\}.
$$

由对称性 $\delta_h$ 与 $z,\epsilon$ 无关；由 (11.3)，
$\delta_h\le2\mu/(h-\mu)^2$。
在参考律下，$\mathbb E\widetilde L=1-\delta_h$。
对角项满足 $\mathbb E\widetilde L_z^2\le e^h\mathbb E L_{b_z,s}^{\epsilon}=e^h$；
异位项由非负性及 (10.4) 满足
$\mathbb E\widetilde L_z\widetilde L_w\le(1-\alpha/k)^s\le1$。
所以

$$
\mathbb E\widetilde L^2\le\frac{e^h}{M}+\frac{M-1}{M},\qquad
\mathbb E|\overline L_s^\epsilon-1|
\le\delta_h+\sqrt{\frac{e^h}{M}+2\delta_h}.
\tag{11.13}
$$

后一式使用截去的总均值为 $\delta_h$，及
$\mathbb E(\widetilde L-1)^2\le e^h/M+2\delta_h$。
这种逐分量截断属于既有的截断二阶矩方法；这里的精确异位内积使交叉项直接有界。

若 $\mu\le(1-\varepsilon)\log M$，取
$h=(1-\varepsilon/2)\log M$。则
$\delta_h=O(1/\log M)$，$e^h/M=M^{-\varepsilon/2}$。
故两个方向混合律分别在全变差下趋于均匀参考律。
由三角不等式及 (11.12) 得到 (11.9)。
若方向已知，令 $a_z$ 为任意随机化定位规则输出 $z$ 的条件概率，
则 $\sum_z a_z=1$，并有

$$
\frac1M\sum_z\mathbb E_{\mathsf P_{b_z,s}^{\epsilon}}a_z
\le\frac{e^h}{M}+\delta_h\longrightarrow0.
\tag{11.14}
$$

这里将每项按真分量似然是否超过 $e^h$ 分开即可，不要求这些事件互斥。

现在考虑上界。若真参数为 $(z,\epsilon)$，每个错误候选 $(w,\epsilon')$ 都满足

$$
\mathbb E_{\mathsf P_{b_z,s}^{\epsilon}}L_{b_w,s}^{\epsilon'}
=\mathbb E_{\mathsf U_s}[L_{b_z,s}^{\epsilon}L_{b_w,s}^{\epsilon'}]\le1,
\tag{11.15}
$$

其中异向时等于一，同向异位时为 $(1-\alpha/k)^s$。
若真似然大于 $e^h$ 且其余 $2M-1$ 个似然全小于 $e^h$，最大似然唯一地选中真参数。
因此对 $h<\mu$，Chebyshev 不等式与逐候选 Markov 不等式给出统一界

$$
\max_{z,\epsilon}\mathsf P_{b_z,s}^{\epsilon}
 \{(\widehat z,\widehat\epsilon)\ne(z,\epsilon)\}
\le\frac{2\mu}{(\mu-h)^2}+(2M-1)e^{-h}.
\tag{11.16}
$$

若 $\mu\ge(1+\varepsilon)\log M$，取 $h=(1+\varepsilon/2)\log M$。
函数 $\mu/(\mu-h)^2$ 在 $\mu>h$ 上递减，故右边至多
$8(1+\varepsilon)/(\varepsilon^2\log M)+2M^{-\varepsilon/2}$，趋于零。
这个论证使用全部路径转移，不作独立边抽稀，且对任意 $r_d\in(0,1)$ 一致成立。

最后，正项级数
$\phi(r)=\sum_{j\ge1}r^{2j}/((2j)(2j-1))$ 给出

$$
0\le k\phi(r/k)\le\frac{\phi(r)}k.
$$

代回 $F_M$ 得到 (11.11)。再用 $\phi(r)\to\log2$（$r\to1$）
及 $\phi(r)\sim r^2/2$（$r\to0$）得到两个端点尺度。$\square$

## 12. 对整个反向族同时有效的似然鞅

**定理 12.1（共同反向鞅与可选停止的方向保证）。** 对任意
$P_b,P_c\in\mathcal K_d^0$，在正向 $P_c$ 路径律下，
$(L^{-,\mathrm{path}}_{b,s})_{s\ge0}$ 是非负、均值为一的鞅；
在反向 $P_c$ 路径律下，$(L^{+,\mathrm{path}}_{b,s})_{s\ge0}$ 具有同一性质。
两项结论也适用于按样本对增长的独立状态对实验。
因此，同一方向中预先固定权重的任意有限似然混合，
都是整个相反方向核族下的均值一非负鞅。

对定义 11.1 的单峰族，取 $\overline L_s^\pm=M^{-1}\sum_z L_{b_z,s}^\pm$。
给定 $\eta\in(0,1)$，定义停止时刻

$$
\tau_\eta=\inf\{s\ge1:\max(\overline L_s^+,\overline L_s^-)\ge1/\eta\},
\tag{12.1}
$$

在停止时输出达到门槛的方向；若两个方向同时达到则任意破同分。
对每个固定 $d,r$，两种实验中的 $\tau_\eta$ 都在每个单峰假设下几乎处处有限，且

$$
\max_{z,\epsilon}
\mathsf P_{b_z}^{\epsilon}\{\widehat\epsilon_{\tau_\eta}\ne\epsilon\}
\le\eta.
\tag{12.2}
$$

不需要另给两个方向分摊错误预算。

证明。在正向 $P_c$ 下，反向候选似然的下一步乘子条件期望为

$$
\mathbb E_c\!\left[
 \frac{L_{b,s+1}^-}{L_{b,s}^-}\,\middle|\,X_0,\ldots,X_s\right]
=n\sum_yP_c(X_s,y)P_b(y,X_s)
=n(P_cP_b)(X_s,X_s)=1.
\tag{12.3}
$$

最后一步使用 (10.2)，而非仅用单个核的平方等于 $\Pi$。
似然严格为正且 $L_{b,0}^-=1$，得到鞅性质与均值一。
交换两个方向时，使用
$P_c^\top P_b^\top=(P_bP_c)^\top=\Pi$。
对独立状态对，下一对的异向乘子均值由 (10.3) 在 $s=1$ 时给出，亦为一。
固定权重的有限和保留鞅性质。

由经典 Ville 不等式，见
[Howard 等，引理 1](../../../Library/Dynamics/howard2020timeuniform.md)，
每个真正向核下都有

$$
\Pr\{\sup_{s\ge0}\overline L_s^-\ge1/\eta\}\le\eta,
$$

真反向核下也有对应的正向越界界。
报告错误方向必导致该错误方向的混合似然曾越界，故直接得到 (12.2)。
对固定真单峰 $(z,\epsilon)$，有限正链的遍历定理或独立样本大数律给出

$$
\frac1s\log L_{b_z,s}^{\epsilon}\longrightarrow F_M(r)>0
\quad\text{几乎处处}.
$$

又 $\overline L_s^\epsilon\ge L_{b_z,s}^\epsilon/M$，故真方向的混合似然最终超过任何固定门槛，
证明停时有限。这里只给出错误率与几乎处处停止，不断言期望停时的最优尺度。$\square$

## 追加锚（本行以下为增补区）
