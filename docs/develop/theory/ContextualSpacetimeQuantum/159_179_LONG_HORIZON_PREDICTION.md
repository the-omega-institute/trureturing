# 情境时空算术的量子扩展：长期预测、校准与辨识

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](142_158_REPORTS_AND_OBSERVERS.md) · [续卷](180_203_PROGRAM_INFORMATION.md)


<a id="entry-666"></a>

## 追加锚（本行以下为增补区）

<a id="section-159"></a>

## 159. 固定证据前缀与全部非平凡精度范围的逆混合率下界

**命题 159.1（低于静态地板的前缀平衡块状态下界，repo-derived）。** 沿用命题153.1、156.1、158.1的二元时间齐次无控制仪器、初态 $I_2/2$ 及观察者记号。固定
$$
0<p<\frac12,\qquad d=1-2p,\qquad
\Delta=\frac d2,\qquad \kappa=\frac{1-p}{p},\qquad
\lambda=\log\kappa,\qquad
h(x)=p+\frac d{1+e^{-x}}.
$$
旧隐藏位先发射报告，再按 $P(r)$ 翻转；每个报告、旧位、新位三元组对应一个独立秩一 Kraus 项。观察者仍为 $\mathcal O=(S,s_0,T_0,T_1,t)$：$S$ 非空有限，更新 $T_0,T_1:S\to S$ 与读出 $t:S\to[0,1]$ 确定且固定，全部可读的演化记忆均计入 $S$。允许依赖 $p,r,\varepsilon$ 的任意精确实数静态表，同一张表须对包括空词和任意稀有历史在内的全部有限报告词满足
$$
\mathcal E_r(\mathcal O)
=\sup_{w\in\{0,1\}^{*}}|t(s_{\mathcal O}(w))-f_r(w)|\le\varepsilon,
\qquad f_r(w)=h(x_w^{(r)}).
$$
$N_{\min}^{(r)}(\varepsilon)$ 为可行观察者的最小有限状态数，不存在时取 $\infty$。函数的复合迭代一律写为 $F^{\circ n}$，其中 $F^{\circ0}=\operatorname{id}$；词的幂仍表示重复拼接。

固定 $0<\varepsilon<\Delta$，选择固定正整数 $a,b$，使
$$
L_{ab}=h(b\lambda)-h\!\left(-\frac{a\lambda}{2}\right)>2\varepsilon.
$$
这样的选择存在。对正整数 $j$ 记 $D_j=\kappa^j-\kappa^{-j}$，并置
$$
\begin{aligned}
D_{ab}&=D_{a+b}=\kappa^{a+b}-\kappa^{-(a+b)},&
C_{ab}&=d\,aD_{ab},\\
M&=L_{ab}-2\varepsilon>0,&
K_{ab}&=\frac d4(2bD_b+aD_a)>0,\\
c&=\frac{M}{2C_{ab}}>0,&
r_0&=\min\!\left\{\frac14,\frac{M}{2K_{ab}}\right\}\in(0,1/2).
\end{aligned}
$$
则
$$
\forall r\in(0,r_0),\qquad
N_{\min}^{(r)}(\varepsilon)\ge\frac c r.
$$
所用历史为 $0^b(0^a1^a)^n$。这里 $p,\varepsilon,a,b$ 先于 $r_0$ 和观察者固定；常数不依赖观察者。命题157.1的显式有限见证与词长界、命题158.1在 $0<\varepsilon<\Delta/2$ 上的陈述各保留原适用范围。

**证明。** 先核对沿用模型的时间顺序与条件化。为避免与前缀长度 $b$ 混淆，将单个报告写作 $\beta\in\{0,1\}$。沿用
$$
c_{00}=c_{11}=p,\qquad c_{01}=c_{10}=1-p,
\qquad P_{ii}(r)=1-r,\qquad P_{1-i,i}(r)=r.
$$
命题153.1、156.1中的独立 Kraus 项给出的复线性分支为
$$
\phi_\beta^{(r)}(X)
=\sum_{i,j=0}^1c_{\beta i}P_{ji}(r)X_{ii}|j\rangle\langle j|
\qquad(X\in M_2(\mathbb C)).
$$
这是逐项共轭作用后相加的结果，不能把 Kraus 振幅先相加。从 $v_\varnothing^{(r)}=(1/2,1/2)^{\mathsf T}$ 出发，故有既有递推
$$
v_{w\beta}^{(r)}=P(r)\operatorname{diag}(c_{\beta0},c_{\beta1})v_w^{(r)},
\qquad Z_w^{(r)}=\mathbf1^{\mathsf T}v_w^{(r)}.
$$
$P(r)$ 的列和为一且 $c_{\beta i}\ge p$，所以 $Z_{w\beta}^{(r)}\ge pZ_w^{(r)}$，从而 $Z_w^{(r)}\ge p^{|w|}>0$。两分量始终严格为正，后验 $q_w^{(r)}=(v_w^{(r)})_1/Z_w^{(r)}$ 及对数赔率 $x_w^{(r)}=\log(q_w^{(r)}/(1-q_w^{(r)}))$ 均有定义。下一零报告概率为 $p+dq_w^{(r)}=h(x_w^{(r)})$，且 $x_\varnothing^{(r)}=0$、$h(0)=1/2$。

旧位发射使对数赔率增加 $(-1)^\beta\lambda$，再由翻转作用更新，因此命题158.1的精确递推为
$$
F_{\beta,r}(x)=G_r(x+(-1)^\beta\lambda),\qquad
G_r(z)=\log\frac{(1-r)e^z+r}{re^z+1-r},
\qquad x_{w\beta}^{(r)}=F_{\beta,r}(x_w^{(r)}).
$$
末次发射后的翻转已包含在 $x_w^{(r)}$ 中。对 $0<r<1/2$，令 $\eta=1-2r$。沿用该证明中的全实轴界
$$
0<G_r'(z)=\frac{1-2r}{1+2r(1-r)(\cosh z-1)}\le\eta<1,
\qquad 0<h'(x)\le\frac d4.
$$
分母至少为一，且 $G_r$ 为奇函数、$G_r(0)=0$，故它保号并将实数移向零；每个包含零的闭区间均被 $G_r$ 保持。各 $F_{\beta,r}$ 为 $\eta$-Lipschitz。

先固定所需的 $a,b$。当正整数 $a=b$ 同时趋于无穷时，$h(b\lambda)\to1-p$、$h(-a\lambda/2)\to p$，所以 $L_{ab}\to d=2\Delta>2\varepsilon$。取一次充分大的 $a=b$ 即证选择存在；以下论证适用于任意已经固定且满足所列严格间隙的正整数 $a,b$。

对这个固定 $a$，直接复用命题158.1证明中在成本半径选择之前建立的反射结论。具体地，置
$$
I=[-a\lambda,0],\qquad A_r=F_{0,r}^{\circ a},\qquad
B_r(x)=-A_r(x),\qquad
H_r=F_{1,r}^{\circ a}\circ F_{0,r}^{\circ a}=B_r^{\circ2}.
$$
对每个 $0<r<1/2$，该证明给出 $B_r:I\to I$ 的收缩常数 $\eta^a$、唯一不动点 $x_r\in(-a\lambda,0)$，以及
$$
A_r(x_r)=-x_r,\qquad H_r(x_r)=x_r,\qquad
\left|x_r+\frac{a\lambda}{2}\right|
\le\frac{arD_a}{2(1-r)}.
$$
这些是固定 $a$ 的反射与中心估计，不使用该命题后段的成本精度限制。若按命题158.1开头的参数约束代入，取
$$
g_a=\Delta\tanh\frac{a\lambda}{4}\in(0,\Delta),\qquad
\varepsilon_*=\frac{g_a}{4}.
$$
便有 $0<\varepsilon_*<\Delta/2$ 及 $g_a>2\varepsilon_*$，故所选任意正整数 $a$ 都满足该处的前提。这里只取其证明在全部 $0<r<1/2$ 上已给出的上述反射子结论；$\varepsilon_*$ 不替换本命题的 $\varepsilon$，也不把命题158.1的成本结论用于其范围之外。特别地 $x_r\to-a\lambda/2$；没有对 $r=0$ 断言严格收缩或不动点唯一性。

现加入从原始先验实际运行的前缀。记
$$
z_r=F_{0,r}^{\circ b}(0)=x_{0^b}^{(r)},\qquad
J=[-a\lambda,b\lambda].
$$
从零出发，每个零报告后的值严格为正，并且
$$
0\le F_{0,r}^{\circ j}(0)\le j\lambda\quad(0\le j\le b),
\qquad 0<z_r\le b\lambda.
$$
归纳中第 $j$ 次送入 $G_r$ 的数在 $[0,j\lambda]$，因为上一步在 $[0,(j-1)\lambda]$，加上 $\lambda$ 后再向零收缩。命题158.1的逐步缺陷估计在任意正整数 $j$ 上同样为
$$
|G_r(u)-u|\le\frac{rD_j}{1-r}\qquad(|u|\le j\lambda).
$$
这里直接用其恒等式 $G_r(u)-u=\log(1-r+re^{-u})-\log(1-r+re^u)$：两个对数自变量均至少为 $1-r$，对数中值界与 $|e^u-e^{-u}|\le D_j$ 给出该式。前缀各步用 $D_j\le D_b$ 并相加，得到
$$
|z_r-b\lambda|\le\frac{brD_b}{1-r}\le2brD_b,
\qquad z_r\longrightarrow b\lambda\quad(r\downarrow0).
$$

须把整块控制域扩大到 $J$，因为前缀终点 $z_r$ 为正。对任意 $x\in J$，零报告段满足
$$
F_{0,r}^{\circ j}(x)\in[-(a-j)\lambda,(b+j)\lambda]
\qquad(0\le j\le a).
$$
$j=0$ 为起点条件；第 $j$ 步之前的值加上 $\lambda$，恰落在此式的第 $j$ 个区间内，而该区间包含零，所以经 $G_r$ 后仍在其中。特别地，$u=F_{0,r}^{\circ a}(x)\in[0,(a+b)\lambda]$。随后的一报告段满足
$$
F_{1,r}^{\circ j}(u)\in[-j\lambda,(a+b-j)\lambda]
\qquad(0\le j\le a).
$$
同样，第 $j$ 步将前一界减去 $\lambda$，其区间仍包含零，故被 $G_r$ 保持。这两次归纳同时给出了每次送入 $G_r$ 的参数界，而不只给出块端点界；所有这些参数均在 $[-(a+b)\lambda,(a+b)\lambda]$ 内。第二段的 $j=a$ 界直接是 $[-a\lambda,b\lambda]=J$，故
$$
H_r(J)\subseteq J.
$$
闭区间 $J$ 非空完备，$H_r$ 在其上为 $\eta^{2a}$-Lipschitz，且 $\eta^{2a}<1$。Banach 不动点定理因而给出从 $J$ 内每个起点的收敛；已有的 $x_r\in I\subset J$ 满足 $H_r(x_r)=x_r$，由唯一性它正是同一个不动点。因此，对每个固定 $r\in(0,1/2)$，
$$
H_r^{\circ n}(z_r)\longrightarrow x_r\qquad(n\to\infty).
$$

整块的 $a$ 个 $+\lambda$ 与 $a$ 个 $-\lambda$ 增量相消。将上述全部中间参数的逐步缺陷相加，得到
$$
\sup_{x\in J}|H_r(x)-x|
\le\frac{2arD_{ab}}{1-r}\le4arD_{ab}
\qquad(0<r<1/2).
$$
现在直接应用[《情境时空算术·机器学习》定义21.1、定理21.2](../CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)：精确状态域取 $J$、精确更新取 $H_r$，摘要为包含映射 $\pi:J\hookrightarrow\mathbb R$，模型更新和实际求值更新均取 $\operatorname{id}_{\mathbb R}$。相应常数为
$$
L=1,\qquad \delta_{\rm close}=4arD_{ab},\qquad
\delta_{\rm eval}=0,\qquad e_0=0,
\qquad L_o=\frac d4,\qquad\varepsilon_o=0,
$$
输出为 $h$，两条轨迹同从 $z_r$ 出发。真实轨迹因 $H_r(J)\subseteq J$ 始终在 $J$，比较轨迹恒为 $z_r\in J$；所有域条件成立。该定理对任意有限块数视界给出
$$
|h(H_r^{\circ n}(z_r))-h(z_r)|
\le\frac d4(4arD_{ab})\sum_{j=0}^{n-1}1^j
=C_{ab}nr\qquad(n\ge0).
$$
$n=0$ 时空和为零。相同代入也直接符合既有 [`output_trajectory_error`](../../../../D5/S3/Observer/MetricGeometry/OutputTrajectoryError.lean)：$Y=J$、$Z=\mathbb R$、$\tau=H_r$、$\sigma=\operatorname{id}_{\mathbb R}$、$\pi$ 为包含映射、$q_{\rm out}=h|_J$、$o=h$，一步缺陷为 $4arD_{ab}$、读出不匹配量为零。这个界随 $n$ 增长，不是对所有时间一致的小误差界；比较用的实数轨迹也不是观察者获准额外读取的记忆。

令实际起点与极限的输出间隙为
$$
L_r=h(z_r)-h(x_r)>0.
$$
由 $r<1/2$ 下的前缀偏差及反射中心界，
$$
|z_r-b\lambda|\le2brD_b,\qquad
\left|x_r+\frac{a\lambda}{2}\right|\le arD_a.
$$
再用 $h$ 的 $d/4$-Lipschitz 性，得到
$$
|L_r-L_{ab}|
\le\frac d4(2bD_b+aD_a)r=K_{ab}r.
$$
因此陈述中的同一个 $r_0=\min\{1/4,M/(2K_{ab})\}$ 满足：对所有 $0<r<r_0$，
$$
L_r-2\varepsilon\ge L_{ab}-K_{ab}r-2\varepsilon
\ge\frac M2>0.
$$
这里的参数选择和间隙估计均在选择观察者之前完成，即使固定容差任意接近 $\Delta$，也只需该严格正的 $M$；未要求对这些容差有共同的正半径。

固定这样的 $r$，再固定任意可行的 $m=|S|$ 状态观察者。对块更新及实际前缀后状态
$$
U=T_1^{\circ a}\circ T_0^{\circ a}:S\to S,
\qquad s_b=T_0^{\circ b}(s_0),
$$
直接应用 [`finite_orbit_and_readout_eventually_periodic`](../../../../D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.lean)，代入有限集 $S$、自映射 $U$、读出 $t$ 和起点 $s_b$。它给出整数 $n\ge0$、$\ell\ge1$，使
$$
n+\ell\le m,\qquad
U^{\circ(j+\ell)}(s_b)=U^{\circ j}(s_b)\quad(j\ge n).
$$
于是对每个整数 $k\ge0$，$U^{\circ(n+k\ell)}(s_b)=U^{\circ n}(s_b)$。记其共同固定读出为 $t_*=t(U^{\circ n}(s_b))$。这些状态对应原先验下的有限词
$$
w_k=0^b(0^a1^a)^{n+k\ell},\qquad
x_{w_k}^{(r)}=H_r^{\circ(n+k\ell)}(z_r),\qquad
Z_{w_k}^{(r)}\ge p^{b+2a(n+k\ell)}>0.
$$
可行性给
$$
|t_*-h(H_r^{\circ(n+k\ell)}(z_r))|\le\varepsilon
\qquad(k\ge0).
$$
现在仅在当前 $r$ 和当前观察者均已固定后令 $k\to\infty$。因 $\ell\ge1$，Banach 收敛和 $h$ 连续性给 $|t_*-h(x_r)|\le\varepsilon$。再取 $k=0$ 的约束，便有
$$
|h(H_r^{\circ n}(z_r))-h(x_r)|\le2\varepsilon.
$$
若 $n=0$，这里使用的第一个词就是实际前缀 $0^b$。起点 $s_b$ 仍是 $S$ 中的一个状态；前缀既未改变允许的初始先验，也未赠送 $b$ 个状态。有限轨道界始终是 $n+\ell\le m$，无需增加 $b$。

结合前面的有限时域误差界与正间隙，有
$$
\begin{aligned}
L_r
&\le |h(z_r)-h(H_r^{\circ n}(z_r))|
 +|h(H_r^{\circ n}(z_r))-h(x_r)|\\
&\le C_{ab}nr+2\varepsilon
\le C_{ab}mr+2\varepsilon,\\
m&\ge\frac{L_r-2\varepsilon}{C_{ab}r}
\ge\frac{M}{2C_{ab}r}=\frac c r.
\end{aligned}
$$
这里 $n$ 计块数，报告词长是 $b+2an$；$2a$ 次更新已计入 $C_{ab}$ 所来自的整块缺陷界，不再额外乘一次 $2a$。对所有可行有限基数取最小值即得陈述；若可行集合为空，$N_{\min}^{(r)}(\varepsilon)=\infty$ 自动满足同一下界。命题153.1已经给出每个正 $r$、正容差下的有限观察者存在性，这与本必要界相容，无须重新构造观察者。

全部取样历史都从 $I_2/2$ 出发且是正质量有限词，包括定义中的空词；证明不要求无限周期报告路径具有正概率。固定 $p,\varepsilon,a,b$ 后的小 $r$ 间隙估计，与固定 $r$、观察者后取 $k\to\infty$ 的步骤各自成立，没有交换极限。若 $\varepsilon\ge\Delta$，命题156.1的恒定读出 $1/2$ 已用一个状态达到要求；本命题排除 $\varepsilon=0$。结论不给匹配上界、优化常数、状态成本单调性，亦不给 $\varepsilon\uparrow\Delta$ 或 $p$ 趋近端点时的一致界。成本是全部演化观察者状态的基数，不是固定表的有限精度位成本、熵或物理比特数；没有外置免费时钟，也没有可读取的隐藏后验寄存器。由命题153.1、156.1，每个非空报告分支即使在 $r=0$ 也是测量制备映射，生成器仍只有两个经典隐藏状态；这里不作量子到经典转变的推断。证毕。

上述通用步骤分别由所引 ML 定理21.2、输出轨迹误差定理及有限轨道定理承担。Banach 步骤使用非空完备度量空间上的收缩映射定理，见钉版 Mathlib 的 [`Contracting.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/MetricSpace/Contracting.lean) 中 `ContractingWith.fixedPoint_isFixedPt`、`ContractingWith.fixedPoint_unique`、`ContractingWith.tendsto_iterate_fixedPoint`；本命题是在所列模型上的普通推导。

相邻文献的量词与损失各有范围。V. Sharan、S. Kakade、P. Liang、G. Valiant，*Prediction with a Short Memory*，[arXiv:1612.02526](https://arxiv.org/abs/1612.02526)，命题1给出有限阶 Markov 预测的平均 KL 或平均 $\ell_1$ 误差界。T. Berg、O. Ordentlich、O. Shayevitz，*Binary Hypothesis Testing with Deterministic Finite-Memory Decision Rules*，[arXiv:2005.07445](https://arxiv.org/abs/2005.07445)，第I节式(4)–(8)及定理1研究两个独立同分布 Bernoulli 假设下有限确定性状态机的渐近分类错误与状态数指数。P. Chigansky，*Stability of the nonlinear filter for slowly switching Markov chains*，[arXiv:math/0411596](https://arxiv.org/abs/math/0411596)，第1节及定理1.1研究不同初始先验滤波器之差的几乎处处渐近遗忘指数；其二元公式(1.5)及例1.2允许慢切换极限下保持非零负指数。这些平均风险或几乎处处结论不替代本命题逐个有限词的误差约束，也不是本下界的前提；此处不作新颖性或文献穷尽断言。

<a id="entry-668"></a>

## 追加锚（本行以下为增补区）

<a id="section-160"></a>

## 160. 局部收缩校准的非均匀对数赔率网格与固定精度状态阶

**命题 160.1（全有限历史的自适应网格上界与固定精度逆混合率阶，repo-derived）。** 沿用命题153.1、156.1、159.1的二元报告仪器、固定先验 $I_2/2$ 与有限确定性观察者。固定
$$
0<p<\frac12,\qquad 0<r<\frac12,\qquad
d=1-2p,\qquad \Delta=\frac d2,\qquad
\kappa=\frac{1-p}{p},\qquad \lambda=\log\kappa.
$$
旧隐藏位先发射报告，再翻转；每个报告、旧位、新位三元组的秩一 Kraus 项分别作用后求和。以隐藏位为一的后验 $q_w$ 定义精确对数赔率 $x_w=\log(q_w/(1-q_w))$，于是
$$
x_\varnothing=0,\qquad q_\varnothing=\frac12,\qquad
x_{wb}=F_b(x_w),\qquad
F_b(x)=G_r(x+(-1)^b\lambda),
$$
$$
G_r(z)=\log\frac{(1-r)e^z+r}{re^z+1-r},\qquad
h(x)=p+\frac d{1+e^{-x}},\qquad f_r(w)=h(x_w).
$$
这里 $f_r(w)$ 是读完有限报告词 $w$ 后的下一零报告概率。观察者的更新和实数读出表可依赖 $p,r,\varepsilon$，但一经选定即固定；全部演化记忆计入有限状态集，误差上确界取遍包括空词在内的每个有限词，沿用命题156.1的 $N_{\min}^{(r)}(\varepsilon)$。

对任意 $\varepsilon>0$，置
$$
E=\min\!\left\{1,\frac{4\varepsilon}{d}\right\},\qquad
B=\log\frac{1-r}{r},\qquad I=[-B,B],\qquad
\eta=1-2r,
$$
并对 $y\in\mathbb R$ 定义局部校准量
$$
L(y)=\frac{\eta}{1+2r(1-r)\bigl(\cosh(\max\{|y|-E,0\})-1\bigr)},
\qquad \delta(y)=E(1-L(y)).
$$
令 $m=\lceil B\rceil$。对 $k=0,\ldots,m-1$，取
$$
\ell_k=\min\{k+1,B\}-k,\qquad
n_k=\left\lceil\frac{\ell_k}{\delta(k)}\right\rceil,
\qquad
Q=\bigcup_{k=0}^{m-1}
\left\{\pm\left(k+\frac{j\ell_k}{n_k}\right):j=0,\ldots,n_k\right\}.
$$
在内部有限网格 $Q\subset I$ 上，定义最近点量化器
$$
R(y)=\min\left\{a\in Q:|y-a|=\min_{u\in Q}|y-u|\right\}
\qquad(y\in I),
$$
即并列最近时取较小的网格值。取状态标签集 $S=Q$，初态 $s_\varnothing=0$，固定更新和读出
$$
T_b(a)=R(F_b(a)),\qquad t(a)=h(a),\qquad
s_{wb}=T_b(s_w).
$$
则这些定义均有意义，且
$$
|S|=1+2\sum_{k=0}^{m-1}n_k\le\frac{14}{Er},\qquad
\forall w\in\{0,1\}^{*},\quad |x_w-s_w|\le E,
\quad |t(s_w)-h(x_w)|\le\varepsilon.
$$
网格只须一次性枚举，令零点标签的编号为零；上述两张更新表及实数读出表随后均为静态表。运行时只演化一个网格编号，不另保存精确 $x_w$ 或演化实数坐标。

因此，对每个固定 $0<p<1/2$ 及固定 $0<\varepsilon<\Delta$，与命题159.1合用可得
$$
N_{\min}^{(r)}(\varepsilon)=\Theta_{p,\varepsilon}(1/r)
\qquad(r\downarrow0).
$$
若 $\varepsilon\ge\Delta$，单状态恒定读出 $1/2$ 可行，故 $N_{\min}^{(r)}(\varepsilon)=1$。网格结论的参数域仅为正容差、正混合率。

**证明。** 先在已有仪器上核对本证明使用的分支与时间顺序。令
$$
c_{00}=c_{11}=p,\qquad c_{01}=c_{10}=1-p,\qquad
P=\begin{pmatrix}1-r&r\\r&1-r\end{pmatrix},\qquad
K_{bji}=\sqrt{c_{bi}P_{ji}}\,|j\rangle\langle i|.
$$
对于任意复矩阵 $A\in M_2(\mathbb C)$，各项分别作共轭作用给
$$
\Phi_b(A)=\sum_{j=0}^1\left(\sum_{i=0}^1c_{bi}P_{ji}A_{ii}\right)|j\rangle\langle j|,
\qquad
\sum_{b,j,i=0}^1K_{bji}^{*}K_{bji}
=\sum_{i=0}^1\left(\sum_b c_{bi}\right)
\left(\sum_j P_{ji}\right)|i\rangle\langle i|=I_2.
$$
因此这是原仪器的复线性分支，总仪器保迹；相干振幅并未先相加。从 $v_\varnothing=(1/2,1/2)^{\mathsf T}$ 出发，沿用的未归一化对角向量和 Born 质量满足
$$
v_{wb}=P\operatorname{diag}(c_{b0},c_{b1})v_w,\qquad
Z_w=\mathbf1^{\mathsf T}v_w,\qquad
q_w=\frac{(v_w)_1}{Z_w}.
$$
列随机矩阵 $P$ 保持总质量，故每个条件报告概率为两个 $c_{bi}$ 的凸组合，落在 $[p,1-p]$。特别地 $Z_w\ge p^{|w|}>0$，空词质量为一，两个分量始终正。下一零报告概率为 $p(1-q_w)+(1-p)q_w=p+dq_w$。旧位发射的 Bayes 乘权把赔率乘以 $\kappa^{(-1)^b}$；随后翻转给
$$
q_{wb}=r+(1-2r)\frac{1}{1+e^{-(x_w+(-1)^b\lambda)}}.
$$
取赔率再取对数，恰得陈述中的 $F_b$。这仅核对命题153.1、156.1、159.1已经使用的同一模型，并未交换发射与翻转。

对 $G_r$ 直接求导，得到
$$
G_r'(z)
=\frac{(1-2r)e^z}{((1-r)e^z+r)(re^z+1-r)}
=\frac{\eta}{1+2r(1-r)(\cosh z-1)}.
$$
分母至少为一，故 $0<G_r'(z)\le\eta<1$。由表达式，$G_r$ 是奇函数、严格递增、固定零点，且在正负无穷的极限分别为 $B$ 和 $-B$，所以值域恰为 $(-B,B)$。中值定理给 $|G_r(z)|\le\eta|z|\le|z|$；每个 $F_b$ 将整个实轴送入 $I$，而初值零也在 $I$。若记 $\sigma(x)=(1+e^{-x})^{-1}$，则
$$
h'(x)=d\sigma(x)(1-\sigma(x)),\qquad 0<h'(x)\le\frac d4.
$$
因而 $h$ 在整个实轴上为 $d/4$-Lipschitz。又因 $0<E\le1$，有 $0<L(y)\le\eta<1$ 及 $\delta(y)>0$；$L$ 是偶函数且随 $|y|$ 不增，$\delta$ 是偶函数且随 $|y|$ 不减。

下面把一步误差界校准在量化前的目标位置。固定 $a,x\in I$、报告 $b\in\{0,1\}$，并假设 $|x-a|\le E$。置
$$
z=a+(-1)^b\lambda,\qquad y=G_r(z)=F_b(a).
$$
从 $z$ 到 $x+(-1)^b\lambda$ 的闭线段中任一点 $u$ 满足 $|u-z|\le E$，从而
$$
|u|\ge\max\{|z|-E,0\}\ge\max\{|y|-E,0\},
$$
其中第二个不等式用了 $|G_r(z)|\le|z|$。双曲余弦为偶函数且在非负轴递增，因此在线段的每一点均有 $G_r'(u)\le L(y)$。在两端重合时差为零，其余情形对按大小排列的两端直接应用导数有界的中值不等式，即得
$$
|F_b(x)-y|\le L(y)|x-a|\le E L(y).
$$
此处所用通用段估计可直接取钉版 Mathlib [`MeanValue.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/MeanValue.lean) 的 `norm_image_sub_le_of_norm_deriv_le_segment'`，代入该闭线段、函数 $G_r$、导数 $G_r'$ 与常数 $L(y)$。若线段跨过零点，则 $|z|\le E$，于是 $|y|\le E$，$L(y)=\eta$；零点处的最大导数仍被包含。这里使用整条线段的导数上界，未用一个端点的导数替代它。

再证内部网格的舍入性质。因为 $B>0$，所以 $m\ge1$，且每个所列 $k$ 都满足 $0<\ell_k\le1$。正数 $\delta(k)$ 使 $n_k\ge1$，每个分箱 $[k,k+\ell_k]$ 被均分成 $n_k$ 段，每段长度
$$
\frac{\ell_k}{n_k}\le\delta(k).
$$
若 $B$ 是正整数，最后一箱是 $[B-1,B]$，长度为一；若 $0<B<1$，只有 $k=0$ 的一箱，长度为 $B$。非整数 $B>1$ 的最后一箱长度为 $B-(m-1)>0$。这些箱覆盖 $[0,B]$，故 $Q$ 包含零及两端点 $\pm B$，完全位于 $I$ 内。

对任意 $y\in[0,B]$，选一个包含它的箱，再选该箱内一个包含它的小段。该小段的一个端点与 $y$ 的距离不超过整段长度，所以存在 $a\in Q$ 使
$$
|y-a|\le\frac{\ell_k}{n_k}\le\delta(k)\le\delta(y).
$$
这也适用于箱的共享边界及 $y=B$；无需把整数端点归入一个不存在的下一箱。对负 $y$ 使用反射网格及 $\delta$ 的偶性，得到同一结论。有限非空 $Q$ 上的全局最近点必不比这个端点更远，因此固定的较小值破同距规则给出单值映射 $R:I\to Q$，并满足
$$
|y-R(y)|\le\delta(y)\qquad(y\in I),\qquad R(0)=0.
$$
这只用整段长度的界，不需要更换为半段常数。

现在在乘积载体 $X=I\times Q$ 上直接使用既有 [`invariant_safety`](../../../../D5/S0/Rewriting/Safety/InvariantSafety.lean)。令转移关系 $\mathcal R$ 由同一个报告驱动两侧：
$$
(x,a)\mathrel{\mathcal R}(x',a')
\quad\Longleftrightarrow\quad
\exists b\in\{0,1\},\quad x'=F_b(x),\quad a'=R(F_b(a)).
$$
该关系的两侧确在 $X$ 中，因为 $F_b(I)\subset I$ 且 $R(I)\subset Q$。取初始集、不变量集及安全集分别为
$$
\mathcal A=\{(0,0)\},\qquad
\mathcal V=\{(x,a)\in X:|x-a|\le E\},\qquad
\mathcal S=\{(x,a)\in X:|h(x)-h(a)|\le\varepsilon\}.
$$
它的三个前提逐项成立：初始差为零，故 $\mathcal A\subseteq\mathcal V$；对 $\mathcal V$ 中任一对及任一报告，上一段的 $y=F_b(a)$ 满足
$$
|F_b(x)-R(y)|\le|F_b(x)-y|+|y-R(y)|
\le E L(y)+\delta(y)=E,
$$
故一步保持 $\mathcal V$；最后 $h$ 的 Lipschitz 界及 $dE/4\le\varepsilon$ 给 $\mathcal V\subseteq\mathcal S$。既有定理于是给出从 $\mathcal A$ 经 $\mathcal R$ 的自反传递闭包可达的每个状态均在 $\mathcal S$。再将该定理的安全集取为 $\mathcal V$、用恒等包含 $\mathcal V\subseteq\mathcal V$，也直接得到每个可达状态在 $\mathcal V$ 中。每个有限报告词恰指定这样一条同报告路径；自反路径包含空词，此时两侧都是零、读出都是 $1/2$。这就同时给出所列全历史对数赔率界与读出界，无需量化后的 $T_b$ 自身收缩。

最后计数。相邻正箱只共享一个端点；从零开始，每箱增加恰好 $n_k$ 个正点，反射后正负部分只共享零。因此
$$
|Q|=1+2\sum_{k=0}^{m-1}n_k
\le1+2m+2\sum_{k=0}^{m-1}\frac1{\delta(k)},
$$
这里用了 $\lceil u\rceil\le u+1$ 及 $\ell_k\le1$。记
$$
C_k=\cosh(\max\{k-E,0\})\ge1.
$$
直接通分给出所需的精确恒等式与上界：
$$
\frac1{1-L(k)}
=1+\frac{\eta}{2r\bigl(r+(1-r)C_k\bigr)}
\le1+\frac1{rC_k}.
$$
最后一步等价于 $\eta C_k\le2r+2(1-r)C_k$，两边之差为 $2r+C_k>0$。于是，以 $\operatorname{sech}u=1/\cosh u$ 记倒双曲余弦，有
$$
\sum_{k=0}^{m-1}\frac1{\delta(k)}
\le\frac mE+\frac1{Er}\sum_{k=0}^{m-1}
\operatorname{sech}(\max\{k-E,0\}).
$$
当 $m=1$ 时只有首项；一般情形前两项至多为二。对 $k\ge2$，$E\le1$ 给 $\max\{k-E,0\}\ge k-1$，而 $\cosh u\ge e^u/2$，故尾项至多 $2e^{-(k-1)}$。由几何级数及 $e>2$，
$$
\sum_{k=0}^{m-1}\operatorname{sech}(\max\{k-E,0\})
\le2+2\sum_{j=1}^{\infty}e^{-j}
=2+\frac2{e-1}<4.
$$
$e>2$ 可直接用钉版 Mathlib [`ExponentialBounds.lean`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Complex/ExponentialBounds.lean) 的 `Real.exp_one_gt_two`。对正数 $u=(1-r)/r$，用 [`Real.log_le_sub_one_of_pos`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean) 的 $\log u\le u-1$，有
$$
m\le B+1\le\frac{1-r}{r}\le\frac1r.
$$
所以
$$
\sum_{k=0}^{m-1}\frac1{\delta(k)}\le\frac mE+\frac4{Er},\qquad
|Q|\le1+2m+\frac{2m}E+\frac8{Er}.
$$
乘以正数 $Er$，再用 $m\le1/r$、$E\le1$ 及 $Er<1/2$，得到
$$
Er|Q|\le Er+2E+10<14.
$$
因而陈述中的非严格界成立，所有向上取整、最后一段箱长与共享端点均已计入，状态数没有剩余的对数因子。

为明确同阶结论的常数与量词，现固定 $p$ 和 $0<\varepsilon<\Delta$。取命题159.1允许的固定正整数 $a_*,b_*$，使
$$
L_*=h(b_*\lambda)-h(-a_*\lambda/2)>2\varepsilon.
$$
沿用该命题的常数，只把整数下标改写以区别网格状态和单次报告：
$$
\begin{aligned}
D_j&=\kappa^j-\kappa^{-j},& M_*&=L_*-2\varepsilon,\\
C_*&=d\,a_*D_{a_*+b_*},&
K_*&=\frac d4(2b_*D_{b_*}+a_*D_{a_*}),\\
c_*&=\frac{M_*}{2C_*}>0,&
r_*&=\min\!\left\{\frac14,\frac{M_*}{2K_*}\right\}>0.
\end{aligned}
$$
命题159.1在完全相同的先验、先发射再翻转顺序、逐有限词下一报告损失以及静态精确实数表约定下，已对每一个有限确定性观察者证明 $|S|\ge c_*/r$（$0<r<r_*$）；其观察者并不限于网格。本命题给出可行网格，因此在同一范围内
$$
\frac{c_*}{r}\le N_{\min}^{(r)}(\varepsilon)\le\frac{14}{Er}.
$$
$c_*,r_*,E$ 在 $p,\varepsilon,a_*,b_*$ 固定后均不随 $r$ 或观察者变化，这正是所述 $\Theta_{p,\varepsilon}(1/r)$。另一方面，$h(x)\in(p,1-p)$ 给 $|h(x)-1/2|\le\Delta$，一个恒定状态即处理 $\varepsilon\ge\Delta$；非空状态集至少有一个状态，故该范围的最小值恰为一。证毕。

不变量距离关系与量化误差共同闭合的成熟背景可见 G. Pola、A. Girard、P. Tabuada，*Approximately bisimilar symbolic models for nonlinear control systems*，[arXiv:0706.0246](https://arxiv.org/abs/0706.0246)，定理4.1：它在连续时间控制系统的增量渐近稳定假设下，以 $\beta(\varepsilon,\tau)+\mu+\eta/2\le\varepsilon$ 构造近似双模拟关系。该文参数及时间假设不同，不承担这里的 $14/(Er)$ 计数。W. Ren、D. V. Dimarogonas，*Logarithmic Quantization based Symbolic Abstractions for Nonlinear Control Systems*，[arXiv:2011.12811](https://arxiv.org/abs/2011.12811)，定理1建立控制系统抽象的反馈精化关系；它不直接给出本命题固定的、仅由报告驱动的确定性逐词观察者保证。G. Pagès、A. Sagna，*Improved error bounds for quantization based numerical schemes for BSDE and nonlinear filtering*，[arXiv:1510.01048](https://arxiv.org/abs/1510.01048)，定理6.3在其局部 Lipschitz、分布与矩条件下给出有限视界滤波量化误差，界依赖视界和观测似然归一化因子；不能把它替换为本命题对任意长度、任意稀有有限词的同一误差界。这里的模型专属上界由上述局部校准、内部舍入和计数普通推导给出，不作优先性或文献穷尽断言。

命题154.1讨论固定 $(p,r)$ 时的 $\varepsilon\downarrow0$；命题159.1与本命题合成的是固定 $(p,\varepsilon)$、$0<\varepsilon<\Delta$ 时的 $r\downarrow0$。这两个分开的极限不推出联合 $\Theta(1/(r\varepsilon))$ 定律、参数一致的下界常数或极限交换。本命题不优化常数，不对 $\varepsilon=0$ 或 $r=0$ 给出网格结论，也不提供随 $p$、$\varepsilon$ 同时变化的一致同阶下界。

所计成本始终是全部演化观察者状态的基数；若使用时钟、档案或种子，其全部演化取值都须计入状态。精确 $x_w$ 只出现在证明中的比较轨迹，不是观察者寄存器；有限网格的实数标签、更新表和输出表静态存在。基数与标记状态所需的位数不同，本结论没有给出有限位表编码、精确指数求值算法、最少位数或总实现成本。保证涵盖每一个正 Born 质量的有限词，无论多稀有；它不是典型、平均或几乎处处保证，也不需要某个无限词具有正概率。原仪器在 $r=0$ 时各非空报告分支已是测量制备操作，生成器始终只有两个经典隐藏状态；这里的状态阶不推出物理熵界、量子优势、相干性边界或关于普遍经典实在的结论。

<a id="entry-670"></a>

## 追加锚（本行以下为增补区）

<a id="section-161"></a>

## 161. 未知循环相位的重复记录预测半径与非一致时间极限

**定义 161.1（已校准两条边的共同记录源）。** 令系统空间为 $\mathcal H_S=\mathbb C^3$，固定有序基 $|0\rangle,|1\rangle,|2\rangle$。设 $0\le r\le1$ 为已知参数，定义 Hermitian 矩阵
$$
C(r,z)=\begin{pmatrix}
1&r&rz\\
r&1&r\\
r\overline z&r&1
\end{pmatrix},\qquad z\in\mathbb C.
\tag{161.1}
$$
允许的未知参数为满足 $C(r,e^{i\phi})\succeq0$ 的 $\phi\in[-\pi,\pi]$。两个端点 $-\pi,\pi$ 表示同一个矩阵。源按第3节的有限 Gram 实现提供单位记录向量 $e_j^{(\phi)}\in\mathbb C^3$，方向固定为
$$
\langle e_k^{(\phi)}\mid e_j^{(\phi)}\rangle
=C(r,e^{i\phi})_{jk}.
\tag{161.2}
$$
例如可以取 $C(r,e^{i\phi})^{\mathsf T}$ 的正半定平方根的各列；其通常方向的 Gram 矩阵即为 $C(r,e^{i\phi})^{\mathsf T}$。三标签也可使用第14.4节的两个位置 Zeckendorf 合法基底，以下只使用这三个正交标签。

初态为固定空白向量的环境单元，实施受控记录等距映射 $|j\rangle|m_*\rangle\mapsto|j\rangle|e_j^{(\phi)}\rangle$。丢弃该单元后，系统通道为
$$
\mathcal M_{r,\phi}(A)=C(r,e^{i\phi})\odot A.
\tag{161.3}
$$
这里 $\odot$ 表示逐项乘积。单位对角与 Gram 实现保证它完全正且保持迹。参数 $\phi$ 在整个重复协议中固定未知；每一步使用同一受控记录规则和一个与系统、参考及既有记录独立的新空白单元。旧记录不再访问，两步之间没有额外控制或中间结果读取。于是 $N$ 步终端通道是同一个 $\mathcal M_{r,\phi}$ 的 $N$ 次复合，不是每步重新抽取独立相位的平均通道。

所有源的逐对记录转移概率均为 $|\langle e_k^{(\phi)}\mid e_j^{(\phi)}\rangle|^2=r^2$（$j\ne k$），而循环乘积为 $r^3e^{-i\phi}$；故本节参数与第14.6节的有向循环相位相差负号。式（161.1）还声明了相对于系统制备和读出基的两条实际校准边 $C_{01}=C_{12}=r$。它们是来源合同的一部分，不能从逐对模资料推出，也不能以没有运输输入和效果的坐标变换免费取得。以下预测半径针对这一已校准源族；任意未校准边相位的更大源族不在等式的范围内。循环相位作为三态不变量及其可行域使用第8.9、14.6节的既有机制。

逐对区分度之外的三态相位具有成熟先例：A. J. Menssen 等，*Distinguishability and many-particle interference*，[arXiv:1609.09804v1](https://arxiv.org/abs/1609.09804v1)，正文第2页式(4)给三光子 tritter 的符合概率，其中含有 $r_{12}r_{23}r_{31}\cos\varphi$；第3页式(10)—(14)给固定逐对模而改变三者相位的准备。本节使用三标签受控记录通道，不将该三光子散射概率改称式（161.3），也不将循环相位本身当作新增机制。

**定义 161.2（参考安全的终端预测半径）。** 对两个系统 CPTP 通道 $\mathcal T,\mathcal U$，令
$$
d_{\rm ref}(\mathcal T,\mathcal U)
=\sup_{\substack{\dim\mathcal H_R<\infty\\
\rho_{SR}\succeq0,\ \operatorname{Tr}\rho_{SR}=1}}
\frac12\left\|\bigl((\mathcal T-\mathcal U)\otimes\operatorname{id}_R\bigr)(\rho_{SR})\right\|_1.
\tag{161.4}
$$
两通道作用于同一份输入和同一个不受操作的参考。它是通常的半 diamond 距离；以下证明直接使用所列态优化，不需要限制参考维数。固定已知 $(r,N)$，预测者选择一个与 $\phi$ 无关的 CPTP 通道 $\mathcal F$。定义
$$
\mathcal R_N(r)=\inf_{\mathcal F\ \mathrm{CPTP}}
\ \sup_{\phi:\ C(r,e^{i\phi})\succeq0}
 d_{\rm ref}(\mathcal M_{r,\phi}^{N},\mathcal F),\qquad N\ge1,
\qquad \mathcal R_0(r)=0.
\tag{161.5}
$$
这是对未知共同源作统一终端预测的误差，不是已知源通道的恢复误差。允许的预测通道不必属于原来的单参数源族；它须在所有输入及参考上物理合法。没有额外校准试次、环境读出、作用间干预或关于 $\phi$ 的概率先验。

**定理 161.3（全部输入和参考下的精确重复预测半径）。** 定义
$$
\alpha(r)=
\begin{cases}
\pi,&0\le r\le1/2,\\
\displaystyle\arccos\!\left(\frac{3r^2-1}{2r^3}\right),&1/2<r<1,\\
0,&r=1.
\end{cases}
\qquad h(t)=\sin\!\bigl(\min\{t,\pi/2\}\bigr)\quad(t\ge0).
\tag{161.6}
$$
则对每个 $N\ge1$，
$$
\boxed{\mathcal R_N(r)=\frac{r^N}{2}\,h(N\alpha(r)).}
\tag{161.7}
$$
当 $0<r<1$ 时，令 $s=r^N$、$\beta=N\alpha(r)$，一个达到下确界的预测通道为
$$
\mathcal F_{r,N}(A)=C(s,z_*)\odot A,
\qquad
z_*=
\begin{cases}
\cos\beta,&0\le\beta\le\pi/2,\\
0,&\beta\ge\pi/2.
\end{cases}
\tag{161.8}
$$
该通道完全正且保持迹，并且最坏源对的区分无需纠缠参考就能达到式（161.7）的下界。

证明。 对 $0<r<1$，任意二阶主块的行列式为 $1-r^2>0$。用一个二阶主块作 Schur 补，三阶矩阵正半定等价于
$$
\det C(r,e^{i\phi})=1-3r^2+2r^3\cos\phi\ge0.
\tag{161.9}
$$
$r\le1/2$ 时，该行列式的最小值为 $(1+r)^2(1-2r)\ge0$，故全部相位允许。对 $1/2<r<1$，阈值 $c(r)=(3r^2-1)/(2r^3)$ 严格递增，因为 $c'(r)=3(1-r^2)/(2r^4)>0$，并从 $-1$ 增至 $1$；允许相位恰为 $[-\alpha(r),\alpha(r)]$。这是第14.6节同一 Schur 补判据在可变 $r$ 上的应用。$r=0$ 时通道不依赖相位；$r=1$ 时正性迫使 $\cos\phi=1$，通道为恒等。后两种情形的预测误差均为零。

由新鲜记录及固定同一参数的合同，逐项复合给出
$$
\mathcal M_{r,\phi}^{N}(A)=C(s,e^{iN\phi})\odot A,
\qquad s=r^N.
\tag{161.10}
$$
对任意两个使 $C(s,z),C(s,w)$ 正半定的复数 $z,w$，对应通道只在 $(0,2),(2,0)$ 两个矩阵元上不同，并满足精确式
$$
d_{\rm ref}(M_{C(s,z)},M_{C(s,w)})=\frac{s}{2}|z-w|,
\qquad M_C(A)=C\odot A.
\tag{161.11}
$$
为证明包括任意参考的上界，将输入态写成系统基下的参考算子块 $X_{jk}$，令 $\delta=s(z-w)$。输出差在 $0,2$ 子块上为
$$
\begin{pmatrix}0&\delta X_{02}\\\overline\delta X_{20}&0\end{pmatrix},
$$
其迹范数为 $2|\delta|\|X_{02}\|_1$。输入正性给出
$$
\|X_{02}\|_1\le\sqrt{\operatorname{Tr}X_{00}\operatorname{Tr}X_{22}}
\le\frac{\operatorname{Tr}X_{00}+\operatorname{Tr}X_{22}}2\le\frac12.
\tag{161.12}
$$
第一步也可直接由输入的纯态分解证明：写各纯向量为 $\sum_j|j\rangle v_j$，对各项 $|v_0\rangle\langle v_2|$ 使用迹范数的三角不等式，再对带混合权重的 $\|v_0\|\|v_2\|$ 使用 Cauchy–Schwarz。因而半迹范数至多为 $|\delta|/2$。取无参考输入 $(|0\rangle+|2\rangle)/\sqrt2$ 时，输出差的两个非零特征值恰为 $\pm|\delta|/2$，达到该上界。对应的正谱投影也给出达到同一概率差的二结果终端测量。此处使用第9.4节已有的参考算子块估计与二标签达到机制；新的优化对象是整个未知共同相位族。

若 $\beta\le\pi/2$，两个实际源 $\phi=\pm\alpha(r)$ 的终端参数为 $e^{\pm i\beta}$。它们的通道距离为 $s\sin\beta$。对任何 CPTP 预测通道，三角不等式表明其到至少一个端点的距离不小于 $s\sin\beta/2$。端点通道的等权混合就是式（161.8）中 $z_*=\cos\beta$ 的通道，因此物理合法。对任意 $|t|\le\beta$，因 $\cos\beta\ge0$，有
$$
|e^{it}-\cos\beta|^2
=1+\cos^2\beta-2\cos\beta\cos t
\le1-\cos^2\beta=\sin^2\beta.
\tag{161.13}
$$
结合式（161.11），该预测通道达到下界。

若 $\beta\ge\pi/2$，实际源 $\phi_\pm=\pm\pi/(2N)$ 均在允许区间内，终端参数分别为 $i,-i$。两通道距离为 $s$，故任意预测通道的最坏误差至少为 $s/2$。这两个通道的等权混合使 $z_*=0$，而任意实际终端参数的模长均为一；式（161.11）因此给出恒为 $s/2$ 的误差。式（161.7）在两种情形都成立。证毕。

上述达到通道由实际源通道的凸混合构成，故无须将任意复坐标插值误当成通道。它通常不等于任何一个 $\mathcal M_{r,\phi}^{N}$，因为 $|z_*|<1$。要求预测通道同时来自原始固定逐对模的单一源，是比定义161.2更严格的优化问题，不能将本定理的达到式直接沿用。

**命题 161.4（固定均匀制备与全通道预测的差别）。** 在定义161.1的合同下，若输入限定为 $|s_3\rangle=(|0\rangle+|1\rangle+|2\rangle)/\sqrt3$，且仍允许全部终端系统测量，则令
$$
\rho_{r,\phi}^{(N)}=\mathcal M_{r,\phi}^{N}(|s_3\rangle\langle s_3|)
=\frac13 C(r^N,e^{iN\phi}).
\tag{161.14}
$$
对全部密度矩阵预测 $\sigma$ 的最坏半迹范数误差恰为
$$
\inf_{\sigma\succeq0,\ \operatorname{Tr}\sigma=1}
\sup_{|\phi|\le\alpha(r)}\frac12\|\rho_{r,\phi}^{(N)}-\sigma\|_1
=\frac{r^N}{3}h(N\alpha(r)).
\tag{161.15}
$$
特别地，固定均匀制备的误差严格小于非退化情形的全通道误差，不能以一个三路出口或一种输入的最优值代替定义161.2。

证明。 两个候选矩阵只在 $(0,2),(2,0)$ 上不同，差矩阵的两个非零特征值为 $\pm r^N|z-w|/3$，故半迹范数为 $r^N|z-w|/3$。定理161.3使用的同一端点对给出对任意密度矩阵预测的下界；同一端点态的平均给出合法达到态。将该证明中的系数 $1/2$ 换成 $1/3$ 即得。$r=0,1$ 时两种误差都为零。证毕。

**命题 161.5（新鲜记录中的预测误差先增长而相干模仍衰减）。** 对每个 $1/\sqrt2<r<1$，有
$$
\frac{\mathcal R_2(r)}{\mathcal R_1(r)}
=3-\frac1{r^2}>1,
\qquad
\lim_{N\to\infty}\mathcal R_N(r)=0.
\tag{161.16}
$$
与此同时，对每个固定实际源 $\phi$ 和每个异标签矩阵元，$N$ 步通道的乘子模长均为 $r^N$，随 $N$ 严格下降。

证明。 在 $r=1/\sqrt2$，式（161.6）给 $\alpha=\pi/4$；$c(r)$ 的严格递增性表明所给范围内 $0<\alpha(r)<\pi/4$。故第一、二步均使用式（161.7）的正弦支，且
$$
\frac{r^2\sin(2\alpha)}{r\sin\alpha}
=2r\cos\alpha
=\frac{3r^2-1}{r^2}.
$$
另一方面，$0\le\mathcal R_N(r)\le r^N/2\to0$。乘子模长的陈述由式（161.10）直接读出。这里不存在与数据处理收缩的矛盾：两个不同未知参数的源在下一步分别作用不同的通道；不能把该比较改写为对两份输出再施加同一个已知通道。环境各步保持新鲜，增长也不要求旧记录回流。证毕。

**定理 161.6（趋于同射线的记录仍有非零统一视界误差）。** 令 $r=1-\varepsilon$，$\varepsilon\downarrow0$。对每个固定 $t\ge0$，有
$$
\lim_{\varepsilon\downarrow0}
\mathcal R_{\lfloor t/\varepsilon\rfloor}(1-\varepsilon)
=f(t):=\frac{e^{-t}}2\sin\!\bigl(\min\{\sqrt3t,\pi/2\}\bigr).
\tag{161.17}
$$
该收敛在每个有限 $t$ 区间上一致，且
$$
\boxed{
\lim_{r\uparrow1}\sup_{N\ge1}\mathcal R_N(r)
=\frac{\sqrt3}{4}\exp\!\left(-\frac{\pi}{3\sqrt3}\right)>0,
\qquad
\forall N<\infty,\quad\lim_{r\uparrow1}\mathcal R_N(r)=0.
}
\tag{161.18}
$$
对每个 $0<r<1$ 选任一达到 $\sup_{N\ge1}\mathcal R_N(r)$ 的整数 $N_*(r)$，则
$$
\lim_{r\uparrow1}(1-r)N_*(r)=\frac{\pi}{3\sqrt3}.
\tag{161.19}
$$

证明。 对 $1/2<r<1$，阈值具有精确恒等式
$$
1-\cos\alpha(r)
=\frac{(1-r)^2(2r+1)}{2r^3}.
\tag{161.20}
$$
结合 $2(1-\cos u)/u^2\to1$，得到 $\alpha(1-\varepsilon)/\varepsilon\to\sqrt3$。同时 $\log(1-\varepsilon)/\varepsilon\to-1$。对 $N=\lfloor t/\varepsilon\rfloor$，有 $|N\varepsilon-t|\le\varepsilon$；因而在任意有限 $t$ 区间上一致地成立
$$
(1-\varepsilon)^N\longrightarrow e^{-t},
\qquad N\alpha(1-\varepsilon)\longrightarrow\sqrt3t.
$$
$h$ 连续且为全局 Lipschitz 函数，所以定理161.3给出式（161.17），包括 $t=0$ 处的约定。

对任意整数 $N$，$1-\varepsilon\le e^{-\varepsilon}$ 给出统一尾界
$$
0\le\mathcal R_N(1-\varepsilon)\le\frac12e^{-\varepsilon N}.
\tag{161.21}
$$
先选择大的 $T$ 控制全部 $\varepsilon N\ge T$ 的尾，再使用 $[0,T]$ 上的一致收敛与网格间距 $\varepsilon\to0$，得到最大值趋于 $\max_{t\ge0}f(t)$。在 $0<t<\pi/(2\sqrt3)$，
$$
f'(t)=\frac{e^{-t}}2\bigl(\sqrt3\cos(\sqrt3t)-\sin(\sqrt3t)\bigr).
$$
其唯一零点为 $t_* =\pi/(3\sqrt3)$，此前为正，此后为负；在 $t\ge\pi/(2\sqrt3)$，$f(t)=e^{-t}/2$ 严格下降。因此全局最大点唯一，且 $f(t_*)=(\sqrt3/4)e^{-\pi/(3\sqrt3)}$。

固定 $0<r<1$ 时，$\mathcal R_1(r)>0$ 且 $\mathcal R_N(r)\to0$，所以最大值由有限整数取得。对任意序列 $r\uparrow1$，尾界使其最大点的缩放参数留在某个有限区间；一致收敛和 $f$ 的唯一最大点表明该参数只能趋于 $t_*$，证明式（161.19）。对固定 $N$，$\alpha(r)\to0$，由式（161.7）直接得到式（161.18）的后一式。证毕。

式（161.18）比较的是先取全部视界上确界与先令 $r\uparrow1$，并不声称两个普通迭代极限 $\lim_{r\uparrow1}\lim_{N\to\infty}\mathcal R_N(r)$ 和 $\lim_{N\to\infty}\lim_{r\uparrow1}\mathcal R_N(r)$ 不同；它们都为零。遗漏相位造成的是预测充分性对视界的不一致性。第14节的已知源恢复问题允许恢复依赖完整 $C$，本节预测者只取得定义161.1的共同校准数据；这两个优化的量词不同。第55节的复用记录回流也不承担本节的新鲜记录结论。

<a id="entry-672"></a>

## 追加锚（本行以下为增补区）

<a id="section-162"></a>

## 162. 单步最优预测的迭代刚性与共同相位代价

**定义 162.1（单步最优通道的重复使用）。** 沿用定义161.1的已校准三标签记录源、固定未知相位、新鲜空白记录单元与无中间控制合同，以及定义161.2的距离 $d_{\rm ref}$ 和逐视界预测半径 $\mathcal R_N(r)$。所有预测通道均作用于同一个系统代数 $B(\mathbb C^3)$，没有额外的持久记忆寄存器。令
$$
\mathfrak F_1(r)=
\left\{\mathcal F\ \mathrm{CPTP}:
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi},\mathcal F)
=\mathcal R_1(r)\right\}.
\tag{162.1}
$$
该集合由定理161.3非空。定义
$$
\mathcal E_N(r)=
\inf_{\mathcal F\in\mathfrak F_1(r)}
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^{N},\mathcal F^{N}),
\qquad N\ge1,\qquad \mathcal E_0(r)=0.
\tag{162.2}
$$
下确界允许 $\mathcal F$ 随 $(r,N)$ 选择，但每次必须达到单步最优，并在这 $N$ 步中重复使用同一通道。真实源也在全部步骤保留同一个 $\phi$。本定义没有给未知参数赋予概率先验。

对 $1/\sqrt3<r<1$，简记
$$
\alpha=\alpha(r)\in(0,\pi/2),\qquad
c=\cos\alpha=\frac{3r^2-1}{2r^3}\in(0,1),\qquad
\mathcal F_*(A)=C(r,c)\odot A.
\tag{162.3}
$$
由式（161.8），$\mathcal F_*\in\mathfrak F_1(r)$。它等于 $\mathcal M_{r,\alpha}$ 与 $\mathcal M_{r,-\alpha}$ 的等权混合。这里的混合给出一个合法预测器，并不把真实未知源改成每步独立抽样的源。

**定理 162.2（全 CPTP 单步最优类的精确迭代误差）。** 对每个 $1/\sqrt3<r<1$ 和每个整数 $N\ge1$，有
$$
\boxed{
\mathcal E_N(r)=
\frac{r^N}{2}
\sqrt{1+c^{2N}-2c^N\cos\!\bigl(\min\{N\alpha,\pi\}\bigr)}.
}
\tag{162.4}
$$
同一个 $\mathcal F_*$ 对所有 $N$ 都达到式（162.2）的下确界。下界适用于全部 $\mathfrak F_1(r)$，不要求其中的通道为 Schur 乘子，也不要求它保持系统基的各个投影。达到下界的输入不需要参考系统。

证明。 令 $P=|0\rangle\langle0|+|2\rangle\langle2|$，并在 $P\mathbb C^3$ 上使用 Pauli 矩阵 $X,Y,Z$。记
$$
u_\theta=(\cos\theta,\sin\theta,0),\qquad
v_\theta=(-\sin\theta,\cos\theta,0),\qquad
\rho_\theta=\frac12(P+u_\theta\cdot\sigma),
\qquad q=r\sin\alpha>0.
\tag{162.5}
$$
两端点源作用于 $\rho_\theta$ 后，所得态均支撑于 $P$，其 Bloch 向量构成无序对
$$
b_\theta+qv_\theta,\quad b_\theta-qv_\theta,
\qquad b_\theta=rc\,u_\theta.
\tag{162.6}
$$
这两个态的半迹范数距离为 $q$，且 $\mathcal R_1(r)=q/2$。

先证它们在全三维态空间中半径 $q/2$ 的共同中心唯一。设密度矩阵 $\tau$ 到两态的距离均不大于 $q/2$。令 $t=\langle1|\tau|1\rangle\ge0$，将压缩块写成
$$
P\tau P=\frac12\bigl((1-t)P+w\cdot\sigma\bigr),
\qquad w\in\mathbb R^3.
\tag{162.7}
$$
对分块 $P\oplus(I-P)$ 做 pinching 不增加迹范数。一个 Hermitian 二维矩阵 $(-tP+a\cdot\sigma)/2$ 的迹范数是 $\max\{t,|a|\}$，因为它的两个特征值为 $(-t\pm|a|)/2$。因此上述两个距离分别至少为
$$
\frac12\left(\max\{t,|w-b_\theta\mp qv_\theta|\}+t\right).
\tag{162.8}
$$
而
$$
\max_{\pm}|w-b_\theta\pm qv_\theta|
\ge \sqrt{|w-b_\theta|^2+q^2}\ge q.
\tag{162.9}
$$
距离上界迫使 $q+t\le q$，故 $t=0$；再由式（162.9）得 $w=b_\theta$。$\tau$ 正性和 $\langle1|\tau|1\rangle=0$ 还迫使所有与 $|1\rangle$ 相连的非对角元为零。故唯一共同中心为
$$
\tau_\theta=\frac12(P+rc\,u_\theta\cdot\sigma).
\tag{162.10}
$$
本步骤使用二维 Bloch 球的 Euclidean 范数公式与 pinching 的迹范数收缩；它不声称任意高维迹范数球的共同中心都唯一。

任取 $\mathcal F\in\mathfrak F_1(r)$。单步全输入距离上界特别适用于每个 $\rho_\theta$，所以前述唯一性给出 $\mathcal F(\rho_\theta)=\tau_\theta$。对 $\theta=0,\pi$ 的等式取和、取差，再用 $\theta=\pi/2,3\pi/2$，由线性性得
$$
\mathcal F(P/2)=P/2,\qquad
\mathcal F(X)=rcX,\qquad
\mathcal F(Y)=rcY.
\tag{162.11}
$$
因此不论 $\mathcal F$ 在其余方向怎样作用，其在整个赤道圆盘上的迭代已被迫满足
$$
\mathcal F^N(\rho_\theta)
=\frac12\bigl(P+(rc)^Nu_\theta\cdot\sigma\bigr).
\tag{162.12}
$$
真实源在同一输入上的 Bloch 向量为 $r^N u_{\theta-N\phi}$；角度的正负来自式（161.1）的矩阵元约定，不影响以下模长。两输出的半迹范数距离恰为
$$
\frac{r^N}{2}|e^{iN\phi}-c^N|.
\tag{162.13}
$$
由于 $c^N>0$，在 $|\phi|\le\alpha$ 上最大化此模长，等价于最小化 $\cos(N\phi)$。当 $N\alpha\le\pi$ 时最小值为 $\cos(N\alpha)$；当 $N\alpha\ge\pi$ 时可取实际源 $\phi=\pi/N$，最小值为 $-1$。这给每个 $\mathcal F\in\mathfrak F_1(r)$ 同一个式（162.4）下界。

另一方面，$\mathcal F_*^N(A)=C(r^N,c^N)\odot A$，且作为 CPTP 通道的复合仍为 CPTP。它与 $\mathcal M_{r,\phi}^N$ 只在 $(0,2),(2,0)$ 两个乘子上不同。式（161.11）的全参考精确距离给出
$$
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal F_*^N)
=\frac{r^N}{2}|e^{iN\phi}-c^N|.
\tag{162.14}
$$
故 $\mathcal F_*$ 达到上述下界，同时证明所有有限参考都不能扩大该达到值。证毕。

**命题 162.3（每个后续视界的严格损失与阈值）。** 对所有 $1/\sqrt3<r<1$ 和所有整数 $N\ge2$，
$$
\boxed{\mathcal E_N(r)>\mathcal R_N(r).}
\tag{162.15}
$$
对 $0\le r\le1/\sqrt3$，存在同一个单步最优预测通道在每个视界均最优，且
$$
\mathcal E_N(r)=\mathcal R_N(r)=\frac{r^N}{2}\qquad(N\ge1).
\tag{162.16}
$$
在 $r=1$，两者对全部 $N$ 均为零。

证明。 先设 $1/\sqrt3<r<1$，令 $\beta=N\alpha$、$a=c^N>0$。若 $\beta<\pi/2$，式（161.7）、（162.4）给出
$$
\left(\frac{2\mathcal E_N}{r^N}\right)^2
-\left(\frac{2\mathcal R_N}{r^N}\right)^2
=(a-\cos\beta)^2.
\tag{162.17}
$$
由 $0<\alpha$ 和 $N\ge2$，在 $1\le k<N$ 时
$$
\cos((k+1)\alpha)
=c\cos(k\alpha)-\sin(k\alpha)\sin\alpha
<c\cos(k\alpha).
$$
本情形各个中间角均小于 $\pi/2$，故迭代该不等式得到 $\cos(N\alpha)<c^N=a$，式（162.17）严格为正。

若 $\beta\ge\pi/2$，则 $\mathcal R_N=r^N/2$ 且 $\cos(\min\{\beta,\pi\})\le0$，于是
$$
\left(\frac{2\mathcal E_N}{r^N}\right)^2-1
=a^2-2a\cos(\min\{\beta,\pi\})>0.
\tag{162.18}
$$
这也包含 $\beta=\pi/2$，从而证明式（162.15）。

对 $0<r\le1/\sqrt3$，有 $\alpha(r)\ge\pi/2$。式（161.8）的单步最优通道可取 $\mathcal F_0(A)=C(r,0)\odot A$；它是两个合法源 $\phi=\pm\pi/2$ 的平均。对每个 $N\ge1$，$\mathcal F_0^N(A)=C(r^N,0)\odot A$ 正是定理161.3的逐视界达到通道。任何重复预测通道在第 $N$ 步仍为一个 CPTP 通道，因此其误差不能低于无单步限制的 $\mathcal R_N$；这个共同达到者证明式（162.16）。$r=0$ 时唯一真实通道是完全去相干通道，选它作预测即可；$r=1$ 时唯一真实通道是恒等通道，也可精确预测。证毕。

**定理 162.4（单步最优限制的弱记录极限）。** 令 $r=1-\varepsilon$，$\varepsilon\downarrow0$。对每个 $t\ge0$，
$$
\lim_{\varepsilon\downarrow0}
\mathcal E_{\lfloor t/\varepsilon\rfloor}(1-\varepsilon)
=g(t):=e^{-t}
\sin\!\left(\min\left\{\frac{\sqrt3\,t}{2},\frac\pi2\right\}\right).
\tag{162.19}
$$
该收敛在每个有限 $t$ 区间上一致。并且
$$
\boxed{
\lim_{r\uparrow1}\sup_{N\ge1}\mathcal E_N(r)
=\sqrt{\frac37}\,
\exp\!\left[-\frac2{\sqrt3}\arctan\!\left(\frac{\sqrt3}{2}\right)\right].
}
\tag{162.20}
$$
若 $N^\dagger(r)$ 为任一达到 $\sup_{N\ge1}\mathcal E_N(r)$ 的整数，则
$$
\lim_{r\uparrow1}(1-r)N^\dagger(r)
=\frac2{\sqrt3}\arctan\!\left(\frac{\sqrt3}{2}\right).
\tag{162.21}
$$
式（162.20）的常数严格大于定理161.6中的 $(\sqrt3/4)e^{-\pi/(3\sqrt3)}$。

证明。 定理161.6已给出 $\alpha(1-\varepsilon)/\varepsilon\to\sqrt3$ 以及 $r^{\lfloor t/\varepsilon\rfloor}\to e^{-t}$，后者在有限 $t$ 区间上一致。由式（161.20），
$$
1-c=\frac{\varepsilon^2(3-2\varepsilon)}
{2(1-\varepsilon)^3}=O(\varepsilon^2).
\tag{162.22}
$$
对 $N=\lfloor t/\varepsilon\rfloor$，在 $0\le t\le T$ 上有
$$
0\le1-c^N\le N(1-c)=O(T\varepsilon),
\tag{162.23}
$$
故 $c^N\to1$ 一致。将式（162.4）写成
$$
\mathcal E_N(r)=
\frac{r^N}{2}
\left|e^{i\min\{N\alpha,\pi\}}-c^N\right|
\tag{162.24}
$$
并使用复数模长的 Lipschitz 性，即得有限区间上一致的极限
$$
\frac{e^{-t}}2|e^{i\min\{\sqrt3t,\pi\}}-1|
=g(t).
$$
$N=0$ 时该式也按定义为零，因而包含 $t=0$。

对所有 $N\ge1$，式（162.24）给出统一尾界
$$
0\le\mathcal E_N(1-\varepsilon)
\le (1-\varepsilon)^N
\le e^{-\varepsilon N}.
\tag{162.25}
$$
和定理161.6一样，有限区间上一致收敛、网格间距趋零及该尾界把最大值问题化为 $\max_{t\ge0}g(t)$。令 $a=\sqrt3/2$；在 $0<t<\pi/(2a)$，
$$
g'(t)=e^{-t}(a\cos(at)-\sin(at)).
$$
其唯一零点为 $t^\dagger=a^{-1}\arctan a$，此前导数为正，此后为负；在剩余区间 $g(t)=e^{-t}$ 严格下降。唯一最大值为
$$
g(t^\dagger)
=\frac{a}{\sqrt{1+a^2}}e^{-t^\dagger}
=\sqrt{\frac37}\,e^{-(2/\sqrt3)\arctan(\sqrt3/2)}.
$$
固定 $1/\sqrt3<r<1$ 时，$\mathcal E_1(r)>0$ 而 $\mathcal E_N(r)\to0$，所以整数最大点存在。统一尾界和极限的唯一最大点给出式（162.21）。

最后比较定理161.6的函数 $f(t)$。当 $0<t\le\pi/(2\sqrt3)$ 时，写 $x=\sqrt3t/2\in(0,\pi/4]$，有 $g(t)=e^{-t}\sin x>e^{-t}\sin x\cos x=f(t)$。当 $t\ge\pi/(2\sqrt3)$ 时，$f(t)=e^{-t}/2$，而 $g(t)\ge e^{-t}/\sqrt2>f(t)$。在 $f$ 的正最大点代入即得两最大值的严格差。证毕。

为解释上述严格代价，使用通道复合对加法的分配律。在定义162.1的非退化区间内，最优预测器满足
$$
\mathcal F_*^N
=2^{-N}\!\!\sum_{\epsilon_1,\ldots,\epsilon_N\in\{-1,1\}}
\mathcal M_{r,\epsilon_N\alpha}\circ\cdots\circ
\mathcal M_{r,\epsilon_1\alpha}.
\tag{162.26}
$$
其 $(0,2)$ 乘子为 $r^Nc^N$；若在开始时仅抽一次等权端点相位，并在所有步骤保持它，所得平均终端通道的该乘子则为 $r^N\cos(N\alpha)$。二者在 $N=2$ 时的通道距离恰为
$$
\frac{r^2}{2}\sin^2\alpha>0.
\tag{162.27}
$$
因此单步上相同的混合预测合同，在独立重抽与保持共同参数两种续接下给出不同的多步通道。

事实上，逐次展开 $\bigl((\mathcal M_{r,\alpha}+\mathcal M_{r,-\alpha})/2\bigr)^N$ 即得式（162.26）。其相位因子的平均是
$$
2^{-N}\!\!\sum_{\epsilon_1,\ldots,\epsilon_N}
e^{i\alpha(\epsilon_1+\cdots+\epsilon_N)}
=\left(\frac{e^{i\alpha}+e^{-i\alpha}}2\right)^N=c^N.
$$
固定共同端点的平均因子为 $(e^{iN\alpha}+e^{-iN\alpha})/2=\cos(N\alpha)$。在 $N=2$，二者之差为 $c^2-\cos(2\alpha)=\sin^2\alpha$，再用式（161.11）即得（162.27）。

这两种混合是比较预测合同的数学构造，不改变定义161.1的实际源：每个实际 $\phi$ 固定，环境单元逐步新鲜。静态随机参数产生特征函数退相干已有明确文献：C. M. Kropf、C. Gneiting、A. Buchleitner，*Effective Dynamics of Disordered Quantum Systems*，[Phys. Rev. X 6, 031023 (2016)](https://doi.org/10.1103/PhysRevX.6.031023)，第II A节式(1)—(3)保持每个实现的 Hamiltonian 不变再作平均，第V节式(24)—(25)给出由参数分布特征函数控制的非对角元。式（162.26）的独立乘积平均与固定共同参数平均使用这一成熟的随机参数区分；该文的 Hamiltonian 系综平均不替代本节无参数先验的 minimax 优化。

定理162.2说明任何单步最优的三维 CPTP 模型在赤道圆盘上都被迫给出同一种迭代，因此严格差距不只是选择 Schur 预测器的偶然结果。定理162.4给出的最坏视界常数约为 $0.2871395757$，而逐视界重新选择预测通道的常数约为 $0.2365518148$；前者仅在“必须先达到单步最优”的约束下最优，不是所有平稳预测模型的无约束最优值。固定 $r<1$ 时，两种误差仍随 $N\to\infty$ 趋零；逐视界严格差距不意味着关于全部视界的一致正差距。允许额外持久记忆、随步数改变通道、取得校准数据或中间控制，会改变优化域。平均与复合不交换也可发生在经典未知参数模型中；本节的量子内容在于该已校准记录源的全输入、全参考距离和全 CPTP 最优类的精确界，不由此推出普遍的量子与经典分界。

<a id="entry-674"></a>

## 追加锚（本行以下为增补区）

<a id="section-163"></a>

## 163. 固定预测通道的全视界最优极限与有限参数间隙

**定义 163.1（一个通道同时服务全部视界）。** 沿用定义161.1的已校准三标签记录源和固定未知共同相位，以及定义161.2的全参考距离。真实过程每步使用一个新鲜空白记录单元，无中间控制、旧记录访问或额外相位校准。固定 $r$ 后，预测者选择一个与 $\phi$、视界 $N$ 均无关的 CPTP 通道 $\mathcal F:B(\mathbb C^3)\to B(\mathbb C^3)$，以后只使用其幂 $\mathcal F^N$；不附加持久记忆寄存器。令
$$
\mathcal J(r)=
\inf_{\mathcal F\ \mathrm{CPTP}}\quad
\sup_{\substack{N\in\mathbb N,\ N\ge1\\|\phi|\le\alpha(r)}}
d_{\rm ref}(\mathcal M_{r,\phi}^{N},\mathcal F^N).
\tag{163.1}
$$
这里不施加单步最优条件。另记第162节的受限全视界问题为
$$
\mathcal J_{\rm one}(r)=
\inf_{\mathcal F\in\mathfrak F_1(r)}
\sup_{\substack{N\ge1\\|\phi|\le\alpha(r)}}
d_{\rm ref}(\mathcal M_{r,\phi}^{N},\mathcal F^N).
\tag{163.2}
$$
两个下确界都在视界上确界之前选定通道。它们不同于允许按 $N$ 重选终端通道的 $\sup_{N\ge1}\mathcal R_N(r)$。

以下使用常数
$$
k_*=\frac{3\sqrt3\log2}{\pi},\qquad
t_*=\frac{\pi}{3\sqrt3},\qquad
L=\frac{\sqrt3}{4}e^{-t_*}.
\tag{163.3}
$$
有 $0<k_*<3$。对 $0<r\le1$ 定义固定预测通道的候选
$$
\mathcal T_r(A)=C(r,r^{k_*})\odot A,
\tag{163.4}
$$
并在 $r=0$ 将 $\mathcal T_0$ 定义为系统基下的完全去相干通道。

**定理 163.2（全 CPTP 固定预测的精确弱记录极限）。** 式（163.4）对所有 $0\le r\le1$ 都是 CPTP 通道。令
$$
D_N(r)=
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^{N},\mathcal T_r^N),
\qquad N\ge1,\qquad D_0(r)=0.
\tag{163.5}
$$
则
$$
\boxed{
\lim_{r\uparrow1}\mathcal J(r)
=\lim_{r\uparrow1}\sup_{N\ge1}D_N(r)
=\lim_{r\uparrow1}\sup_{N\ge1}\mathcal R_N(r)
=L.
}
\tag{163.6}
$$
具体地，若 $r=1-\varepsilon$、$\varepsilon\downarrow0$，则在每个有限 $t$ 区间上一致地有
$$
D_{\lfloor t/\varepsilon\rfloor}(1-\varepsilon)
\longrightarrow
G(t):=\frac{e^{-t}}2
\left|e^{i\min\{\sqrt3t,\pi\}}-e^{-k_*t}\right|.
\tag{163.7}
$$
$G$ 的唯一全局最大点为 $t_*$，最大值为 $L$。对每个 $0<r<1$ 选取任一达到 $\sup_{N\ge1}D_N(r)$ 的整数 $N_T(r)$，都有
$$
(1-r)N_T(r)\longrightarrow t_*.
\tag{163.8}
$$
式（163.6）只给出极限等式，不宣称 $\mathcal T_r$ 在每个固定 $r<1$ 都达到 $\mathcal J(r)$。

证明。 先验证合法性。更一般地，对 $0<r\le1$、$0\le k\le3$，令 $z=r^k$。矩阵 $C(r,z)$ 的对角元为一，二阶主子式分别是 $1-r^2$ 与 $1-r^2z^2$，均非负。其三阶行列式可因式分解为
$$
\det C(r,z)=(1-rz)(1+rz-2r^2).
\tag{163.9}
$$
因 $rz=r^{1+k}\le1$，第一个因子非负；又因 $1+k\le4$，
$$
1+rz-2r^2\ge1+r^4-2r^2=(1-r^2)^2\ge0.
\tag{163.10}
$$
故所有主子式非负，$C(r,r^k)\succeq0$。取 $k=k_*$，再用第3节的 Gram 通道实现，得到完全正且保持迹。$r=0$ 的定义也显然合法；$r=1$ 时 $\mathcal T_1$ 是恒等通道。这里仅使用有限维正性与既有 Gram 实现，不另行假设插值后的系数自动物理合法。

通道复合给出 $\mathcal T_r^N(A)=C(r^N,r^{k_*N})\odot A$。式（161.11）于是给出每个实际源的全参考精确距离
$$
d_{\rm ref}(\mathcal M_{r,\phi}^{N},\mathcal T_r^N)
=\frac{r^N}{2}|e^{iN\phi}-r^{k_*N}|.
$$
实中心 $r^{k_*N}$ 为正，故和定理162.2一样，最坏相位使 $\cos(N\phi)$ 在允许区间上最小，从而
$$
D_N(r)=\frac{r^N}{2}
\left|e^{i\min\{N\alpha(r),\pi\}}-r^{k_*N}\right|.
\tag{163.11}
$$
该式在 $N=0$ 时也给零，在 $r=0$ 时按 $N\ge1$ 给零，在 $r=1$ 时给零。无需参考的平衡两标签输入仍能达到距离。

定理161.6已给出 $\alpha(1-\varepsilon)/\varepsilon\to\sqrt3$ 与 $\log(1-\varepsilon)/\varepsilon\to-1$。当 $N=\lfloor t/\varepsilon\rfloor$ 时，在有限 $t$ 区间上一致地有
$$
r^N\to e^{-t},\qquad
N\alpha(r)\to\sqrt3t,\qquad
r^{k_*N}\to e^{-k_*t}.
\tag{163.12}
$$
由复数模长的 Lipschitz 性，得到式（163.7），包括 $t=0$。同时
$$
0\le D_N(1-\varepsilon)
\le(1-\varepsilon)^N
\le e^{-\varepsilon N}
\tag{163.13}
$$
给出与视界一致的尾界。

现在精确定位 $G$ 的全局峰值。令 $b=\sqrt3$、$k=k_*$。在 $0<t<\pi/b$，
$$
G(t)^2=
\frac14\left(e^{-2t}+e^{-2(1+k)t}
-2e^{-(2+k)t}\cos(bt)\right),
$$
所以
$$
\frac{d}{dt}G(t)^2
=\frac12e^{-(2+k)t}H(t),
\qquad
H(t)=(2+k)\cos(bt)+b\sin(bt)-e^{kt}-(1+k)e^{-kt}.
\tag{163.14}
$$
有 $H(0)=0$、$H'(0)=b^2+k^2>0$。记
$$
A(t)=(2+k)\cos(bt)+b\sin(bt),\qquad
t_0=\frac{\pi/2+\arctan(b/(2+k))}{b}\in(0,\pi/b).
\tag{163.15}
$$
在 $[0,t_0)$ 上 $A>0$，在 $(t_0,\pi/b]$ 上 $A<0$。前一区间满足
$$
H''(t)=-b^2A(t)-k^2\bigl(e^{kt}+(1+k)e^{-kt}\bigr)<0.
\tag{163.16}
$$
因而 $H$ 在 $[0,t_0]$ 严格凹；结合 $H'(0)>0$ 和 $H(t_0)<0$，它在 $(0,t_0)$ 恰有一个零点。唯一性也可由严格凹性推出 $H(t)/t$ 在 $t>0$ 时严格下降。在 $[t_0,\pi/b]$，$H=A-e^{kt}-(1+k)e^{-kt}<0$。因此 $G$ 在 $(0,\pi/b)$ 先严格增后严格减。在 $t\ge\pi/b$，$G(t)=e^{-t}(1+e^{-kt})/2$ 继续严格下降。

由常数选择，$bt_*=\pi/3$、$kt_*=\log2$。代入式（163.14）得
$$
H(t_*)=\frac{2+k}{2}+\frac32-2-\frac{1+k}{2}=0.
$$
故 $t_*$ 正是上述唯一最大点，并且
$$
G(t_*)=
\frac{e^{-t_*}}2
\left|e^{i\pi/3}-\frac12\right|
=\frac{\sqrt3}{4}e^{-t_*}=L.
\tag{163.17}
$$
有限区间上一致收敛、网格间距 $\varepsilon\to0$ 以及式（163.13）的统一尾界，遂给出 $\sup_N D_N(r)\to L$。固定 $0<r<1$ 时 $D_1(r)>0$ 且 $D_N(r)\to0$，所以整数最大点存在；同一尾界排除缩放最大点逃至无穷，$G$ 的唯一最大点再给出式（163.8）。

最后，任意固定 CPTP 通道 $\mathcal F$ 在每个视界的幂仍为一个 CPTP 通道，故定义161.2直接给出
$$
\sup_{N,\phi}d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal F^N)
\ge\sup_{N\ge1}\mathcal R_N(r).
$$
对 $\mathcal F$ 取下确界，再用合法候选 $\mathcal T_r$，得到逐参数夹逼
$$
\sup_{N\ge1}\mathcal R_N(r)
\le\mathcal J(r)\le\sup_{N\ge1}D_N(r).
\tag{163.18}
$$
两端由定理161.6与以上证明趋于同一个 $L$，即得式（163.6）。这里没有交换通道下确界与视界上确界，也没有把任意 CPTP 通道先验限制成 Schur 乘子。证毕。

**命题 163.3（此固定构造的局部代价与全程改进）。** 定义163.1中的固定通道满足
$$
\lim_{r\uparrow1}\frac{D_1(r)}{\mathcal R_1(r)}
=\sqrt{1+\frac{k_*^2}{3}}>1.
\tag{163.19}
$$
另一方面，
$$
\lim_{r\uparrow1}\mathcal J_{\rm one}(r)
=\sqrt{\frac37}\,
\exp\!\left[-\frac2{\sqrt3}\arctan\!\left(\frac{\sqrt3}{2}\right)\right]
>L=\lim_{r\uparrow1}\mathcal J(r).
\tag{163.20}
$$
因此对所有充分接近一的 $r<1$，$\mathcal T_r$ 的全视界最坏误差严格小于每一个单步最优固定预测通道的全视界最坏误差。

证明。 令 $\varepsilon=1-r$。当 $\varepsilon\downarrow0$ 时，
$$
1-r^{k_*}=k_*\varepsilon+O(\varepsilon^2),\qquad
1-\cos\alpha(r)=\frac32\varepsilon^2+O(\varepsilon^3).
$$
由
$$
|e^{i\alpha}-r^{k_*}|^2
=(1-r^{k_*})^2+2r^{k_*}(1-\cos\alpha)
$$
得到
$$
D_1(r)=\frac{\sqrt{k_*^2+3}}2\,\varepsilon+o(\varepsilon),
\qquad
\mathcal R_1(r)=\frac{\sqrt3}{2}\,\varepsilon+o(\varepsilon).
\tag{163.21}
$$
这证明式（163.19）。

对 $1/\sqrt3<r<1$，每个 $\mathcal F\in\mathfrak F_1(r)$ 的第 $N$ 步误差至少为 $\mathcal E_N(r)$。定理162.2还提供同一个 $\mathcal F_*$ 同时达到每个 $N$ 的下界，因此
$$
\mathcal J_{\rm one}(r)=\sup_{N\ge1}\mathcal E_N(r).
\tag{163.22}
$$
应用定理162.4，再用定理163.2，得到式（163.20）及充分接近一时的严格比较。证毕。

式（163.19）的比值约为 $1.1992166662$，是这一显式构造相对于单步最优值的代价，不是所有渐近全视界最优模型必须支付的最小局部代价。式（163.20）消除的是单步最优限制造成的额外常数；残余误差 $L>0$ 仍在，因而没有恢复被遗漏的相位信息，也没有把未知源识别出来。

**命题 163.4（有限参数处仍有严格固定通道间隙）。** 令 $r_0=1/\sqrt2$。则
$$
\sup_{N\ge1}\mathcal R_N(r_0)=\frac14,
\qquad
\boxed{
\frac14<\mathcal J(r_0)
\le \frac1{2\sqrt2}\sqrt{\frac54-\frac1{\sqrt2}}.
}
\tag{163.23}
$$
右端约为 $0.2605026916$。所以式（163.6）的渐近相等不能升级为所有固定参数上的相等；本命题不确定 $\mathcal J(r_0)$ 的精确值。

证明。 此时 $\alpha(r_0)=\pi/4$，定理161.3给出 $\mathcal R_1(r_0)=\mathcal R_2(r_0)=1/4$；对 $N\ge3$，$\mathcal R_N(r_0)=r_0^N/2<1/4$。

先说明式（163.1）的下确界在固定 $r$ 时可取得。由有限维 Choi 表示，全体三维 CPTP 通道对应于正半定且输出偏迹固定为恒等矩阵的 Choi 矩阵，构成非空紧集。对每个固定 $N$，通道复合与 $d_{\rm ref}$ 连续；具体地，CPTP 通道的距离收缩与复合的 telescoping 给出
$$
d_{\rm ref}(\mathcal F^N,\mathcal G^N)
\le N\,d_{\rm ref}(\mathcal F,\mathcal G).
\tag{163.24}
$$
故每个固定 $(N,\phi)$ 的误差是 $\mathcal F$ 的连续函数，所有 $(N,\phi)$ 的上确界是下半连续函数，在该紧集上达到最小值。这只使用有限维通道空间的紧性，不要求对 $N$ 一致的连续模。

如果 $\mathcal J(r_0)=1/4$，取其达到通道 $\mathcal F$。其单步误差不超过 $1/4=\mathcal R_1(r_0)$，所以 $\mathcal F\in\mathfrak F_1(r_0)$。但定理162.2给出
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r_0,\phi}^2,\mathcal F^2)
\ge\mathcal E_2(r_0)=\frac{\sqrt5}{8}>\frac14,
\tag{163.25}
$$
与全视界上界矛盾。结合式（163.18），得到严格下界。

为给上界，取合法通道 $\mathcal Q(A)=C(r_0,1/2)\odot A$。式（163.9）在这里成为 $\det C(r_0,z)=(1-r_0z)r_0z\ge0$，且所有二阶主子式非负，故 $\mathcal Q$ 是 CPTP。其第 $N$ 步最坏误差由式（161.11）等于
$$
\frac{r_0^N}{2}
\left|e^{i\min\{N\pi/4,\pi\}}-2^{-N}\right|.
\tag{163.26}
$$
$N=1$ 时恰为式（163.23）的右端，$N=2$ 时为 $\sqrt{17}/16$；对 $N\ge3$，三角不等式给出不超过
$$
\frac{r_0^N}{2}(1+2^{-N})
\le\frac9{32\sqrt2}<\frac14.
$$
而第一步误差严格大于第二步，因为二者平方之差为
$$
\left(\frac5{32}-\frac1{8\sqrt2}\right)-\frac{17}{256}
=\frac{23-16\sqrt2}{256}>0.
$$
故 $\mathcal Q$ 的全视界最坏误差由第一步取得，证明所述上界。证毕。

定理163.2与命题163.4共同区分了三个量词层次：逐视界重选的最优终端通道、固定通道服务全部视界，以及再要求该固定通道单步最优。它们使用同一个已校准源族和同一个全参考距离。式（163.4）的预测器增加特定非对角方向的衰减来平衡各视界误差，不改变真实记录源、不访问被丢弃的环境，也不根据实际未知相位选择预测。静态随机参数与每步重抽参数的既有区别仍按第162节所引 Kropf、Gneiting、Buchleitner 的文献范围理解；本节比较的是这些固定预测通道的无先验最坏误差，不由此给出量子性的普遍定义或量子对经典的普遍优势。

<a id="entry-676"></a>

## 追加锚（本行以下为增补区）

<a id="section-164"></a>

## 164. 近似单步最优的迭代稳定性与必要局部代价

**定义 164.1（单步超额与固定通道的全视界风险）。** 沿用定义161.1的校准记录源、定义161.2的全参考距离和定义163.1的固定三维 CPTP 预测合同。真实相位在全部步骤固定未知，每步记录单元新鲜；预测者不能访问旧记录、取得额外相位校准、插入中间控制或附加持久记忆。对 $1/\sqrt3<r<1$ 和任意 CPTP 通道 $\mathcal F:B(\mathbb C^3)\to B(\mathbb C^3)$，令
$$
\ell_r(\mathcal F)=
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi},\mathcal F),
\qquad
W_r(\mathcal F)=
\sup_{\substack{N\ge1\\|\phi|\le\alpha(r)}}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal F^N).
\tag{164.1}
$$
定义非负的单步超额及相对超额
$$
\delta_r(\mathcal F)=\ell_r(\mathcal F)-\mathcal R_1(r),
\qquad
\xi_r(\mathcal F)=\frac{\delta_r(\mathcal F)}{\mathcal R_1(r)}.
\tag{164.2}
$$
分母在所给区间内严格为正。记
$$
q=r\sin\alpha(r)=2\mathcal R_1(r),\qquad
\eta_r(\mathcal F)=
\sqrt{\frac43\bigl(q\delta_r(\mathcal F)+\delta_r(\mathcal F)^2\bigr)}
=\frac{2\mathcal R_1(r)}{\sqrt3}
\sqrt{\xi_r(\mathcal F)\bigl(2+\xi_r(\mathcal F)\bigr)}.
\tag{164.3}
$$
仍令 $\mathcal F_*(A)=C(r,\cos\alpha(r))\odot A$ 为定理162.2的共同达到通道。对系统态使用距离 $D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$，对矩阵使用 Hilbert–Schmidt 范数 $\|A\|_2^2=\operatorname{Tr}(A^\dagger A)$。

**定理 164.2（全 CPTP 预测器的近似赤道刚性）。** 令 $P=|0\rangle\langle0|+|2\rangle\langle2|$，$X,Y$ 为 $P\mathbb C^3$ 上的 Pauli 矩阵，定义赤道圆盘
$$
\mathscr D=
\left\{\frac12(P+xX+yY):x,y\in\mathbb R,\ x^2+y^2\le1\right\}.
\tag{164.4}
$$
在定义164.1的条件下，对全部 $\rho\in\mathscr D$ 和全部整数 $N\ge1$，
$$
D\bigl(\mathcal F(\rho),\mathcal F_*(\rho)\bigr)
\le\eta_r(\mathcal F),
\qquad
D\bigl(\mathcal F^N(\rho),\mathcal F_*^N(\rho)\bigr)
\le N\eta_r(\mathcal F).
\tag{164.5}
$$
于是每个视界都满足
$$
\boxed{
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal F^N)
\ge
\bigl[\mathcal E_N(r)-N\eta_r(\mathcal F)\bigr]_+,
}
\qquad [u]_+=\max\{u,0\}.
\tag{164.6}
$$
这里 $\mathcal F$ 不必为 Schur 通道，也不必保持 $\mathscr D$；保持该圆盘的是比较通道 $\mathcal F_*$。

证明。 对无迹 Hermitian 矩阵 $A$，正、负特征值的绝对值之和各为 $\|A\|_1/2$，故
$$
\|A\|_2^2\le2\left(\frac{\|A\|_1}{2}\right)^2.
\tag{164.7}
$$
若 $A$ 是三维矩阵且非零，设其正、负特征值数目为 $p_+,p_-\ge1$，则 $p_++p_-\le3$。Cauchy–Schwarz 给出
$$
\|A\|_2^2
\ge\left(\frac{\|A\|_1}{2}\right)^2
\left(\frac1{p_+}+\frac1{p_-}\right)
\ge\frac32\left(\frac{\|A\|_1}{2}\right)^2.
\tag{164.8}
$$
零矩阵时同样成立。这两步仅使用有限维 Schatten 范数的初等关系，三维常数用于下面的预测误差估计。

先取圆盘边界上的纯态
$$
\rho_\theta=\frac12(P+\cos\theta\,X+\sin\theta\,Y).
$$
令 $\sigma_\pm=\mathcal M_{r,\pm\alpha(r)}(\rho_\theta)$、$\tau=\mathcal F(\rho_\theta)$。由定理162.2中的端点表达式，其中点为 $\tau_*=\mathcal F_*(\rho_\theta)$，且
$$
\sigma_\pm=\tau_*\pm\frac q2 V_\theta,
\qquad
V_\theta^2=P,\quad \operatorname{Tr}(V_\theta)=0.
\tag{164.9}
$$
交换两个端点的标签不影响此式。记 $\delta=\delta_r(\mathcal F)$。单步全输入距离上界特别给出
$$
D(\tau,\sigma_\pm)\le\mathcal R_1(r)+\delta=\frac q2+\delta.
\tag{164.10}
$$
对两个无迹 Hermitian 差矩阵应用式（164.7），再取平均。Hilbert–Schmidt 平行四边形恒等式及 $\operatorname{Tr}P=2$ 给出
$$
\|\tau-\tau_*\|_2^2+\frac{q^2}{2}
=\frac12\bigl(\|\tau-\sigma_+\|_2^2+\|\tau-\sigma_-\|_2^2\bigr)
\le2\left(\frac q2+\delta\right)^2.
\tag{164.11}
$$
因此 $\|\tau-\tau_*\|_2^2\le2q\delta+2\delta^2$。差矩阵 $\tau-\tau_*$ 也是三维无迹 Hermitian 矩阵；式（164.8）遂给出
$$
D(\tau,\tau_*)^2
\le\frac23\|\tau-\tau_*\|_2^2
\le\frac43(q\delta+\delta^2)=\eta_r(\mathcal F)^2.
\tag{164.12}
$$
此估计已包含向第三标签的泄漏与非对角响应，不把 $\tau$ 预先压回二维子空间。$\mathscr D$ 是这些 $\rho_\theta$ 的凸包，通道线性性和迹范数凸性将同一上界延伸至整个圆盘，得到式（164.5）的第一式。

定理162.2给出 $\mathcal F_*(P/2)=P/2$、$\mathcal F_*(X)=r\cos\alpha\,X$ 与 $\mathcal F_*(Y)=r\cos\alpha\,Y$，故 $\mathcal F_*$ 保持 $\mathscr D$。对非交换线性映射仍成立的 telescoping 恒等式为
$$
\mathcal F^N-\mathcal F_*^N
=\sum_{j=0}^{N-1}
\mathcal F^{N-1-j}\circ(\mathcal F-\mathcal F_*)\circ\mathcal F_*^j.
\tag{164.13}
$$
将其作用于 $\rho\in\mathscr D$，每个比较输入 $\mathcal F_*^j(\rho)$ 仍在同一圆盘内。CPTP 通道对态差的迹距离收缩，所以每一项的半迹范数至多为 $\eta_r(\mathcal F)$，求和即得第二式。

最后取无参考平衡输入 $\rho_0=(|0\rangle+|2\rangle)(\langle0|+\langle2|)/2$。式（162.13）和（162.14）表明
$$
\sup_\phi
D\bigl(\mathcal M_{r,\phi}^N(\rho_0),\mathcal F_*^N(\rho_0)\bigr)
=\mathcal E_N(r).
$$
三角不等式与刚证出的迭代估计给出 $\mathcal F$ 在该输入上的最坏误差至少为 $\mathcal E_N(r)-N\eta_r(\mathcal F)$；全输入、全参考距离包含这个实验，且误差非负，故式（164.6）成立。证毕。

式（164.5）约束的是赤道圆盘上的系统态输出，不声称 $d_{\rm ref}(\mathcal F,\mathcal F_*)\le\eta_r(\mathcal F)$。全视界下界由同一个圆盘内的比较轨道承担；实际 $\mathcal F$ 的轨道可以离开该圆盘。

**定理 164.3（局部相对误差约束下的全视界下界）。** 对每个充分接近一的 $r<1$，任取一个三维 CPTP 通道 $\mathcal F_r$，不要求其关于 $r$ 连续。定义
$$
g(t)=e^{-t}\sin\!\left(\min\left\{\frac{\sqrt3t}{2},\frac\pi2\right\}\right),
\qquad
\Phi(\xi)=\sup_{t\ge0}
\left[g(t)-t\sqrt{\xi(2+\xi)}\right]_+,
\quad \xi\ge0.
\tag{164.14}
$$
若 $\limsup_{r\uparrow1}\xi_r(\mathcal F_r)\le\xi<\infty$，则
$$
\boxed{
\liminf_{r\uparrow1}W_r(\mathcal F_r)\ge\max\{L,\Phi(\xi)\}.
}
\tag{164.15}
$$
特别地，若单步风险比 $\ell_r(\mathcal F_r)/\mathcal R_1(r)\to1$，则
$$
\liminf_{r\uparrow1}W_r(\mathcal F_r)
\ge K:=
\sqrt{\frac37}\exp\!\left[-\frac2{\sqrt3}
\arctan\!\left(\frac{\sqrt3}{2}\right)\right]>L.
\tag{164.16}
$$
此类预测族中的下界 $K$ 由 $\mathcal F_r=\mathcal F_*$ 达到。式（164.16）不要求每个有限 $r$ 的单步误差已经精确最优。

证明。 令 $\varepsilon=1-r$。由式（163.21），$2\mathcal R_1(r)/(\sqrt3\varepsilon)\to1$，故式（164.3）和所给相对超额假设推出
$$
\limsup_{r\uparrow1}
\frac{\eta_r(\mathcal F_r)}{\varepsilon}
\le\sqrt{\xi(2+\xi)}.
\tag{164.17}
$$
固定 $t>0$，取 $N=\lfloor t/\varepsilon\rfloor$，则充分小的 $\varepsilon$ 下 $N\ge1$ 且 $\varepsilon N\to t$。定理162.4给出 $\mathcal E_N(r)\to g(t)$，而定理164.2给出
$$
W_r(\mathcal F_r)\ge
\bigl[\mathcal E_N(r)-N\eta_r(\mathcal F_r)\bigr]_+.
$$
取下极限得到对每个固定 $t>0$ 都成立的
$$
\liminf_{r\uparrow1}W_r(\mathcal F_r)
\ge\left[g(t)-t\sqrt{\xi(2+\xi)}\right]_+.
\tag{164.18}
$$
$t=0$ 时右端为零也成立；随后对这些已成立的不等式取 $t$ 的上确界，得到下界 $\Phi(\xi)$。另一方面，式（163.18）的逐视界下界适用于每个 $\mathcal F_r$，定理161.6因此还给出下界 $L$。合并两者即得（164.15），没有交换未知预测器的优化与视界上确界。$\xi=0$ 时 $\Phi(0)=\max_tg(t)=K$，由定理162.4计算；同一节与式（163.22）还给出 $\mathcal F_*$ 的全视界风险趋于 $K$。证毕。

**命题 164.4（达到最优全视界极限的必要正局部代价）。** 令 $a=\sqrt3/2$、$t^\dagger=\arctan(a)/a$。在区间 $[0,t^\dagger]$ 上，式（164.14）的函数为 $g(t)=e^{-t}\sin(at)$。存在唯一 $t_c\in(0,t^\dagger)$ 使
$$
g(t_c)-t_cg'(t_c)=L.
\tag{164.19}
$$
定义
$$
B_c=g'(t_c)>0,\qquad
\xi_c=\sqrt{1+B_c^2}-1>0.
\tag{164.20}
$$
则 $\Phi(\xi_c)=L$，且 $\Phi(\xi)>L$ 当且仅当 $0\le\xi<\xi_c$。若任意固定通道族 $\mathcal F_r$ 满足 $W_r(\mathcal F_r)\to L$，便必须有
$$
\boxed{
\liminf_{r\uparrow1}
\frac{\ell_r(\mathcal F_r)}{\mathcal R_1(r)}
\ge1+\xi_c.
}
\tag{164.21}
$$
数值上，
$$
t_c\approx0.7066490123,\qquad
B_c\approx0.0662831528,\qquad
\xi_c\approx0.002194320652.
\tag{164.22}
$$
这是所证下界 $\Phi$ 的临界参数，并非实际最小局部代价已经达到的断言。

证明。 在 $[0,t^\dagger]$，
$$
g'(t)=e^{-t}(a\cos(at)-\sin(at)),\qquad
g''(t)=e^{-t}\bigl((1-a^2)\sin(at)-2a\cos(at)\bigr)<0.
\tag{164.23}
$$
最后一个严格号可由 $a^2=3/4$、$\tan(at)\le a$ 及 $\cos(at)>0$ 直接得到。因此 $g'$ 从 $g'(0)=a$ 严格下降至 $g'(t^\dagger)=0$。在 $t>t^\dagger$，包括越过相位截断之后，$g$ 仍严格下降。

令 $B=\sqrt{\xi(2+\xi)}$。若 $B\ge a$，因全部 $t\ge0$ 都有 $g(t)\le at$，故 $\Phi(\xi)=0$。若 $0\le B<a$，存在唯一 $t_B\in(0,t^\dagger]$ 使 $g'(t_B)=B$。函数 $g(t)-Bt$ 在该点之前严格增加、之后严格下降，其最大值为正，所以
$$
\Phi(\xi)=g(t_B)-Bt_B.
\tag{164.24}
$$
当 $B<a$ 增大时，这个最优值严格下降：若 $B_1<B_2<a$，在 $B_2$ 的正最大点代入 $B_1$ 的目标，即得严格不等式。

函数 $Q(t)=g(t)-tg'(t)$ 在 $(0,t^\dagger)$ 满足 $Q'(t)=-tg''(t)>0$，且 $Q(0)=0$、$Q(t^\dagger)=K>L$。连续性与严格单调性证明式（164.19）唯一可解，并有 $0<B_c<a$。在 $B=B_c$ 时，式（164.24）的最大点正是 $t_c$，所以 $\Phi(\xi_c)=L$；再由上述严格下降与 $B\ge a$ 时的零值，得到所述阈值性质。

为证明不要求局部误差比收敛的式（164.21），设 $W_r(\mathcal F_r)\to L$，令 $\varepsilon=1-r$、$N=\lfloor t_c/\varepsilon\rfloor$。定理164.2直接给出
$$
N\eta_r(\mathcal F_r)
\ge\mathcal E_N(r)-W_r(\mathcal F_r).
$$
右端趋于 $g(t_c)-L=t_cB_c>0$，且 $\varepsilon N\to t_c$，故
$$
\liminf_{r\uparrow1}\frac{\eta_r(\mathcal F_r)}{\varepsilon}\ge B_c.
\tag{164.25}
$$
再用精确式
$$
\frac{\eta_r(\mathcal F_r)}{\varepsilon}
=\frac{2\mathcal R_1(r)}{\sqrt3\varepsilon}
\sqrt{\xi_r(\mathcal F_r)\bigl(2+\xi_r(\mathcal F_r)\bigr)}
$$
及前因子趋于一，单调连续函数 $x\mapsto\sqrt{x(2+x)}$ 在非负半轴上的反函数为 $y\mapsto\sqrt{1+y^2}-1$，即得 $\liminf\xi_r(\mathcal F_r)\ge\xi_c$。证毕。

因此约 $0.2194\%$ 是达到 $L$ 的必要相对超额下界，而命题163.3的显式构造给出约 $19.9217\%$ 的可行相对超额。两端之间的差距尚未由这些定理闭合；式（164.21）也不声称 $\Phi$ 对每个 $\xi>0$ 都是可达到的最优权衡。

**命题 164.5（有限参数固定预测风险的定量间隙）。** 令 $r_0=1/\sqrt2$、
$$
d=\frac{\sqrt5}{8}-\frac14>0,
$$
并令 $x_0$ 为二次方程
$$
13x^2+(8+6d)x-3d^2=0
\tag{164.26}
$$
的唯一正根，即
$$
x_0=
\frac{\sqrt{(8+6d)^2+156d^2}-(8+6d)}{26}
\approx0.0003192995672.
\tag{164.27}
$$
则定义163.1的全 CPTP 固定预测风险满足
$$
\boxed{
\frac14+x_0\le\mathcal J(r_0)
\le\frac1{2\sqrt2}\sqrt{\frac54-\frac1{\sqrt2}}.
}
\tag{164.28}
$$
这将命题163.4的严格下界定量化，但不确定 $\mathcal J(r_0)$ 的精确值。

证明。 任取固定 CPTP 通道 $\mathcal F$，设 $w=W_{r_0}(\mathcal F)$、$x=w-1/4$。由 $\mathcal R_1(r_0)=1/4$，有 $x\ge0$，且
$$
0\le\delta_{r_0}(\mathcal F)
=\ell_{r_0}(\mathcal F)-\frac14\le x.
$$
此时 $q=1/2$、$\mathcal E_2(r_0)=\sqrt5/8$。定理164.2在 $N=2$ 给出
$$
\frac14+x=w
\ge\frac{\sqrt5}{8}
-\frac4{\sqrt3}\sqrt{\frac x2+x^2},
$$
即
$$
x+\frac4{\sqrt3}\sqrt{\frac x2+x^2}\ge d.
\tag{164.29}
$$
左端是 $x\ge0$ 上连续严格增加的函数，从零开始，且在 $x=d$ 时严格大于 $d$。其与 $d$ 相等的唯一解位于 $(0,d)$；在这一区间中两边移项后均非负，可以等价平方，得到式（164.26）。故此唯一解正是 $x_0$，式（164.29）迫使 $x\ge x_0$。对全部 $\mathcal F$ 取下确界即得所述下界；上界由命题163.4的显式通道给出。证毕。

定理164.2把端点中点的精确约束扩展为近似约束，再沿同一个合法比较轨道传播。定理164.3—命题164.4据此比较单步近优与全视界最优的不同要求；源的未知共同相位并未被重新抽取或估计出来。输入域、通道维数和无持久记忆的假设均沿用定义164.1，允许扩维记忆或自适应校准的模型属于不同的优化问题。

<a id="entry-678"></a>

## 追加锚（本行以下为增补区）

<a id="section-165"></a>

## 165. 全视界最优预测的精确局部代价与有限尺度盲区

**定义 165.1（渐近全视界最优族的局部代价）。** 沿用定义164.1的固定未知相位、新鲜记录与三维 CPTP 预测合同，以及其中的单步风险 $\ell_r$、全视界风险 $W_r$ 和单步最优值 $\mathcal R_1(r)$；本节将 $\ell_r,W_r$ 按式（164.1）的相同公式定义于全部 $0<r<1$，允许相位域仍取定义161.1。预测者在每个 $r$ 选择一个通道，以其幂服务全部视界，不访问环境记录、不插入中间控制、不附加持久辅助记忆。令
$$
\mathscr A=
\left\{(\mathcal F_r)_{r\uparrow1}:
\mathcal F_r\text{ 为三维 CPTP 通道},\quad
W_r(\mathcal F_r)\longrightarrow L\right\},
\qquad
L=\frac{\sqrt3}{4}e^{-t_*},\quad
t_*=\frac\pi{3\sqrt3}.
\tag{165.1}
$$
族只须在某个区间 $r\in(r_0,1)$、$0<r_0<1$ 内定义，不要求连续或可微。记
$$
k_*=\frac{\log2}{t_*}=\frac{3\sqrt3\log2}{\pi},\qquad
h_*=\sqrt{1+\frac{k_*^2}{3}}=\sqrt{1+\frac{9(\log2)^2}{\pi^2}},\qquad
S_*=\frac12\sqrt{3+k_*^2}.
\tag{165.2}
$$

**定理 165.2（任意三维 CPTP 族的精确必要局部代价）。** 每个 $(\mathcal F_r)\in\mathscr A$ 都满足
$$
\boxed{
\liminf_{r\uparrow1}
\frac{\ell_r(\mathcal F_r)}{\mathcal R_1(r)}
\ge h_*.
}
\tag{165.3}
$$
第163节的合法通道 $\mathcal T_r(A)=C(r,r^{k_*})\odot A$ 属于 $\mathscr A$，且其比值收敛至 $h_*$。因此
$$
\inf_{(\mathcal F_r)\in\mathscr A}
\liminf_{r\uparrow1}
\frac{\ell_r(\mathcal F_r)}{\mathcal R_1(r)}
=h_*=1.1992166662\ldots.
\tag{165.4}
$$
这里的下界允许全部三维 CPTP 通道，不预设 Schur 形式、有限 $r$ 的半群嵌入、参数连续性或局部比值的收敛。结论给出的是趋于 $r=1$ 时的精确最小相对局部代价，不是有限参数处 $\mathcal J(r)$ 的精确值。

证明。 若式（165.3）不成立，可取 $r_n\uparrow1$，使
$$
\frac{\ell_{r_n}(\mathcal F_{r_n})}{\mathcal R_1(r_n)}
\longrightarrow h<h_*.
\tag{165.5}
$$
因单步最优值是所有 CPTP 通道的下确界，必有 $h\ge1$。设 $\varepsilon_n=1-r_n$，由式（163.21），
$$
S_n:=\frac{\ell_{r_n}(\mathcal F_{r_n})}{\varepsilon_n}
\longrightarrow S=\frac{\sqrt3}{2}h<S_*.
\tag{165.6}
$$
把通道视为矩阵空间 $M_3(\mathbb C)$ 上的复线性算子，定义
$$
\mathcal G_n=
\frac{\mathcal F_{r_n}-\mathrm{Id}}{\varepsilon_n},\qquad
\|\mathcal G\|_{1\to1}=
\sup_{A\ne0}\frac{\|\mathcal G(A)\|_1}{\|A\|_1}.
\tag{165.7}
$$
令 $\Delta$ 为系统基下的完全去相干通道。允许相位 $\phi=0$ 的真实通道恰为
$$
\mathcal M_{r,0}=r\,\mathrm{Id}+(1-r)\Delta.
$$
故对每个系统密度矩阵 $\rho$，三角不等式与两个态的距离至多为一给出
$$
\|\mathcal G_n(\rho)\|_1
\le 2(S_n+1).
\tag{165.8}
$$
对 Hermitian 输入 $A=A_+-A_-$，分别归一化其正负部分，得到
$$
\|\mathcal G_n(A)\|_1\le2(S_n+1)\|A\|_1.
$$
对任意复矩阵写 $A=H+iK$，其中 $H,K$ Hermitian 且 $\|H\|_1,\|K\|_1\le\|A\|_1$，于是
$$
\|\mathcal G_n\|_{1\to1}\le4(S_n+1).
\tag{165.9}
$$
有限维有界性允许再取子列，使 $\mathcal G_n\to\mathcal G$ 为算子范数收敛。由于 $3\log2<\pi$，有 $k_*<\sqrt3$、$S_*<3/2$，因而
$$
\|\mathcal G\|_{1\to1}
\le4(S+1)<10<6\sqrt3=\frac{2\pi}{t_*}.
\tag{165.10}
$$
特别地，$\mathcal G$ 的每个复特征值 $\mu$ 都满足 $|\operatorname{Im}\mu|<2\pi/t_*$。

对任意固定 $t\ge0$，有限维 Euler 极限给出
$$
\mathcal F_{r_n}^{\lfloor t/\varepsilon_n\rfloor}
=(\mathrm{Id}+\varepsilon_n\mathcal G_n)^{\lfloor t/\varepsilon_n\rfloor}
\longrightarrow e^{t\mathcal G}.
\tag{165.11}
$$
具体地，式（165.9）的统一有界性保证充分大的 $n$ 下可用收敛的矩阵对数级数，且
$$
\log(\mathrm{Id}+\varepsilon_n\mathcal G_n)
=\varepsilon_n\mathcal G_n+O(\varepsilon_n^2)
$$
在算子范数中成立。乘以 $\lfloor t/\varepsilon_n\rfloor$ 后趋于 $t\mathcal G$，再用指数的连续性即得（165.11）。每个左侧通道都 CPTP，有限维 CPTP 集合闭，故 $e^{t\mathcal G}$ 也 CPTP。这一论证没有要求单个 $\mathcal F_{r_n}$ 本身具有 CPTP 的对数生成元，也不对无界 $t$ 声称一致收敛。

取 $P,X,Y$ 如式（164.4）的赤道圆盘，写
$$
\rho_\theta=\frac12(P+\cos\theta\,X+\sin\theta\,Y),\qquad
N_n=\lfloor t_*/\varepsilon_n\rfloor.
$$
真实源的两个允许端点为 $\phi=\pm\alpha(r_n)$。由 $r_n^{N_n}\to e^{-t_*}$ 与 $N_n\alpha(r_n)\to\pi/3$，其在 $\rho_\theta$ 上的输出趋于
$$
\sigma_{\theta,\pm}
=\frac12\left(P+e^{-t_*}
\left[\cos(\theta\pm\pi/3)X+
\sin(\theta\pm\pi/3)Y\right]\right).
\tag{165.12}
$$
端点标签可随 $Y$ 的符号约定互换，不影响下述距离与中点。因为 $W_{r_n}(\mathcal F_{r_n})\to L$，式（165.11）推出
$$
D(e^{t_*\mathcal G}(\rho_\theta),\sigma_{\theta,\pm})\le L.
\tag{165.13}
$$
两个端点的距离为 $2L$，中点是
$$
m_\theta=\frac12\left(P+\lambda
(\cos\theta\,X+\sin\theta\,Y)\right),\qquad
\lambda=\frac{e^{-t_*}}2=e^{-(1+k_*)t_*}.
\tag{165.14}
$$
这个中点在整个三维态空间中也是唯一可满足式（165.13）的态。事实上，写 $\sigma_{\theta,\pm}=m_\theta\pm Q_\theta$，则 $Q_\theta$ Hermitian、无迹，且 $Q_\theta^2=L^2P$。对任一满足（165.13）的态 $\tau$，式（164.7）适用于无迹 Hermitian 差 $\tau-\sigma_{\theta,\pm}$。Hilbert–Schmidt 平行四边形恒等式给出
$$
\|\tau-m_\theta\|_2^2+2L^2
=\frac12\left(\|\tau-\sigma_{\theta,+}\|_2^2+
\|\tau-\sigma_{\theta,-}\|_2^2\right)
\le2L^2.
\tag{165.15}
$$
故 $\tau=m_\theta$。此处只使用实际端点的极限，不把 $e^{-t_*}$ 当作一个新的源参数并调用不同的完整相位族。对全部 $\theta$ 比较（165.14），得到
$$
e^{t_*\mathcal G}(P)=P,\qquad
e^{t_*\mathcal G}(X)=\lambda X,\qquad
e^{t_*\mathcal G}(Y)=\lambda Y.
\tag{165.16}
$$

下面从这一时刻的算子信息返回生成元。对任意 $b>0$，令 $a=(\log b)/t_*$。整函数
$$
e^{t_*z}-b=(z-a)u_b(z),\qquad u_b(a)=t_*b
\tag{165.17}
$$
中的 $u_b$ 只可能在 $a+2\pi i m/t_*$、$m\in\mathbb Z\setminus\{0\}$ 处为零。式（165.10）排除这些点与 $\mathcal G$ 的谱相交，因此 $u_b(\mathcal G)$ 可逆，且与 $\mathcal G-a\mathrm{Id}$ 交换。于是
$$
\ker(e^{t_*\mathcal G}-b\mathrm{Id})
=\ker(\mathcal G-a\mathrm{Id}).
\tag{165.18}
$$
可逆性也可直接在每个 Jordan 块上核对：$u_b$ 作用后的对角元均为非零的 $u_b(\mu)$。因此（165.18）不需要 $\mathcal G$ 可对角化。这里使用的是标准矩阵函数演算及其谱映射性质；相关背景见 Higham、Lin，[*Matrix Functions: A Short Course*](https://eprints.maths.manchester.ac.uk/2067/1/covered/MIMS_ep2013_42.pdf)，§3。谱带界（165.10）承担排除指数不同对数分支的具体义务。

分别取 $b=1$ 和 $b=\lambda$，式（165.16）遂迫使
$$
\mathcal G(P)=0,\qquad
\mathcal G(X)=-(1+k_*)X,\qquad
\mathcal G(Y)=-(1+k_*)Y.
\tag{165.19}
$$
特别地，对 $\rho_0=(P+X)/2$，有 $\mathcal G(\rho_0)=-(1+k_*)X/2$。真实端点通道在同一个输入上的一阶展开为
$$
\frac{\mathcal M_{r_n,\alpha(r_n)}(\rho_0)-\rho_0}{\varepsilon_n}
\longrightarrow\frac12(-X\pm\sqrt3Y),
\tag{165.20}
$$
其中用到了 $\alpha(r_n)/\varepsilon_n\to\sqrt3$。因此全参考单步风险至少包含这个无参考输入的距离，给出
$$
S=\lim_n\frac{\ell_{r_n}(\mathcal F_{r_n})}{\varepsilon_n}
\ge\frac12\left\|\frac12(-k_*X\mp\sqrt3Y)\right\|_1
=\frac12\sqrt{k_*^2+3}=S_*.
\tag{165.21}
$$
最后一步由 $X^2=Y^2=P$、$XY+YX=0$，相应矩阵的两个非零特征值为 $\pm\sqrt{k_*^2+3}/2$。这与（165.6）矛盾，证明（165.3），包括局部比值振荡或无上界的族：若其下极限低于 $h_*$，总能选出（165.5）的有限收敛子列。可达到性由定理163.2及命题163.3直接给出，证明（165.4）。证毕。

式（165.3）将命题164.4的必要下界加强到精确值，并确定第163节构造的最小代价性质；这正是前两节尚未确定的部分。此前的有限参数界与近似圆盘估计仍按各自假设成立。

**命题 165.3（相同局部代价和缩放生成元不能认证全部视界）。** 令 $\mathcal R(A)=\operatorname{Tr}(A)|1\rangle\langle1|$ 为重置通道，并设
$$
p_r=(1-r)^2,\qquad
\widehat{\mathcal T}_r=(1-p_r)\mathcal T_r+p_r\mathcal R,
\qquad 0<r<1.
\tag{165.22}
$$
它是三维 CPTP 通道族，满足
$$
\frac{\ell_r(\widehat{\mathcal T}_r)}{\mathcal R_1(r)}\longrightarrow h_*,\qquad
\left\|\frac{\widehat{\mathcal T}_r-\mathcal T_r}{1-r}\right\|_{1\to1}\longrightarrow0,
\tag{165.23}
$$
并在每个有限缩放视界区间上与 $\mathcal T_r$ 渐近一致：对任意 $T<\infty$，
$$
\sup_{0\le t\le T}
 d_{\rm ref}\left(
\widehat{\mathcal T}_r^{\lfloor t/(1-r)\rfloor},
\mathcal T_r^{\lfloor t/(1-r)\rfloor}\right)
\longrightarrow0.
\tag{165.24}
$$
但它在每个 $0<r<1$ 都有
$$
\boxed{W_r(\widehat{\mathcal T}_r)=1,}
\tag{165.25}
$$
所以不属于 $\mathscr A$。

证明。 通道凸组合保持 CPTP，且 $d_{\rm ref}(\widehat{\mathcal T}_r,\mathcal T_r)\le p_r$。距离的三角不等式使两个单步风险之差的绝对值也至多为 $p_r$。因 $\mathcal R_1(r)\sim\sqrt3(1-r)/2$，命题163.3给出（165.23）的第一式。又 $\mathcal T_r\to\mathrm{Id}$，故 $\mathcal R-\mathcal T_r$ 在有限维算子范数中有界，而
$$
\frac{\widehat{\mathcal T}_r-\mathcal T_r}{1-r}
=(1-r)(\mathcal R-\mathcal T_r),
$$
证明第二式。$\mathcal T_r$ 的各 Schur 系数在 $r=1$ 有单侧导数，所以 $(\mathcal T_r-\mathrm{Id})/(1-r)$ 确有极限；两族因此有同一个缩放生成元。

复合的 telescoping 估计（163.24）给出第 $N$ 步距离至多为 $Np_r$，在 $N=\lfloor t/(1-r)\rfloor$、$0\le t\le T$ 时不超过 $T(1-r)$，即得（165.24）。

另一方面，$\mathcal T_r$ 固定全部计算基态，并保持迹，故 $\mathcal T_r\mathcal R=\mathcal R\mathcal T_r=\mathcal R$、$\mathcal R^2=\mathcal R$。归纳得到
$$
\widehat{\mathcal T}_r^N
=(1-p_r)^N\mathcal T_r^N+
\bigl(1-(1-p_r)^N\bigr)\mathcal R.
\tag{165.26}
$$
取输入 $|0\rangle\langle0|$。全部真实源及 $\mathcal T_r^N$ 都保留该态，重置通道则给出正交态 $|1\rangle\langle1|$。因此实际预测距离为 $1-(1-p_r)^N$，对 $N$ 的上确界是一。任意两通道的全参考距离至多为一，故（165.25）成立。证毕。

定理165.2只用一个有限缩放时刻建立必要条件；其达到性使用第163节的统一尾界。命题165.3显示，这两种义务不可互相替代：每步 $O((1-r)^2)$ 的重置在 $N=O((1-r)^{-1})$ 的任何固定缩放区间上消失，却在更长视界累积成完全可区分的误差。局部最小代价和生成元相同均不足以控制无界视界。本节仍只研究定义165.1的已校准量子记录模型，不由这些预测权衡给出量子性的普遍定义或量子相对经典的普遍优势。

<a id="entry-680"></a>

## 追加锚（本行以下为增补区）

<a id="section-166"></a>

## 166. 全视界误差的半距门槛与稳定记录空间

**定义 166.1（固定模式、周边模式与一阶匹配）。** 沿用定义165.1的已校准三标签记录源、全参考距离和风险 $W_r$，其中 $0<r<1$，每个预测器为在原三维系统上反复使用的 CPTP 通道。令 $\Delta$ 为计算基下的完全去相干通道。对通道 $\mathcal F$，记
$$
\operatorname{Fix}(\mathcal F)=\ker(\mathcal F-\mathrm{Id}),\qquad
m(\mathcal F)=\dim_{\mathbb C}\operatorname{Fix}(\mathcal F).
\tag{166.1}
$$
周边空间指复线性算子 $\mathcal F$ 的全部模长为一的特征值所对应的广义特征空间之和，其维数记为 $p(\mathcal F)$。CPTP 通道的幂有界，因而周边 Jordan 块均为一阶。固定模式是周边模式的一部分，二者不先验等同。

仍以 $\mathcal T_r(A)=C(r,r^{k_*})\odot A$ 表示第163节的达到通道，$k_*=3\sqrt3\log2/\pi$。称通道族 $\mathcal F_r$ 与它一阶匹配，若该族在某个 $(r_0,1)$ 上定义，且
$$
\delta_r:=d_{\rm ref}(\mathcal F_r,\mathcal T_r)=o(1-r).
\tag{166.2}
$$
这里使用整个通道的全参考距离，不只比较一个输入、单步风险值或某个相干分量。

**定理 166.2（小于半距的预测必须保留三个稳定纯态）。** 对固定 $0<r<1$ 和任意三维 CPTP 通道 $\mathcal F$，若
$$
W_r(\mathcal F)<\frac12,
\tag{166.3}
$$
则 $m(\mathcal F)=p(\mathcal F)=3$，且存在一组正交归一基 $u_0,u_1,u_2$ 与相关矩阵 $B\succeq0$、$B_{ii}=1$，使
$$
\mathcal F(|u_i\rangle\langle u_j|)
=B_{ij}|u_i\rangle\langle u_j|,
\qquad |B_{ij}|<1\quad(i\ne j).
\tag{166.4}
$$
因此 $\mathcal F$ 是该基下的严格衰减 Schur 通道，固定三个正交纯态，且 $\mathcal F(I)=I$。设 $\Delta_U$ 为这组基下的完全去相干通道，则
$$
\mathcal F^N\longrightarrow\Delta_U,
\qquad
d_{\rm ref}(\Delta_U,\Delta)\le W_r(\mathcal F).
\tag{166.5}
$$
更一般地，在本模型内只要 $m(\mathcal F)\ne3$ 或 $p(\mathcal F)\ne3$，便有 $W_r(\mathcal F)\ge1/2$。式（166.4）是低风险的必要结构，不是所有此类 Schur 通道都低风险的充分条件；也不要求 $u_i$ 等于原计算基。

证明。 先说明所用的有限维秩障碍。若两个 CPTP 幂等算子 $\mathcal P,\mathcal Q$ 的复秩不同，不妨设 $\operatorname{rank}\mathcal P>\operatorname{rank}\mathcal Q$。二者保 Hermitian，其 Hermitian 像空间的实维数等于复秩，因此存在非零 Hermitian 矩阵
$$
A\in\operatorname{ran}\mathcal P\cap\ker\mathcal Q.
$$
于是 $(\mathcal P-\mathcal Q)A=A$。将 $A$ 的正负部分分别归一化为态，用 $d_{\rm ref}$ 所包含的无参考输入距离，得到
$$
\|A\|_1
=\|(\mathcal P-\mathcal Q)A\|_1
\le2d_{\rm ref}(\mathcal P,\mathcal Q)\|A\|_1.
$$
故
$$
\operatorname{rank}\mathcal P\ne\operatorname{rank}\mathcal Q
\quad\Longrightarrow\quad
d_{\rm ref}(\mathcal P,\mathcal Q)\ge\frac12.
\tag{166.6}
$$
这只是不同秩的投影不能在算子范数一以内相互逼近的标准有限维事实在全参考距离下的归一化。

通道幂的有界性保证 Cesàro 极限存在：
$$
\mathcal E_{\mathcal F}
=\lim_{M\to\infty}\frac1M\sum_{N=1}^{M}\mathcal F^N.
\tag{166.7}
$$
逐个 Jordan 块看，模长小于一的块平均后消失，模长为一但不等于一的特征值平均后也消失，而特征值一的空间保留。因此 $\mathcal E_{\mathcal F}$ 是投影到 $\operatorname{Fix}(\mathcal F)$ 的幂等算子；它是 CPTP 通道的平均之极限，所以也是 CPTP。

相位零属于允许源族，且 $\mathcal M_{r,0}^N\to\Delta$。对平均应用距离的凸性，再取极限，得到
$$
d_{\rm ref}(\mathcal E_{\mathcal F},\Delta)
\le W_r(\mathcal F).
\tag{166.8}
$$
由于 $\operatorname{rank}\Delta=3$，式（166.6）已证明：若 $m(\mathcal F)\ne3$，则风险至少为 $1/2$；在假设（166.3）下，$m(\mathcal F)=3$。

接下来使用任意有限维 CPTP 通道的成熟固定空间结构。Blume-Kohout、Ng、Poulin、Viola，[*Information-preserving structures: A general framework for quantum zero-error information*](https://arxiv.org/abs/1006.1358)，定义10及定理5，给出在固定态共同支撑上的分解
$$
\mathcal H=
\left(\bigoplus_a\mathcal A_a\otimes\mathcal B_a\right)\oplus\mathcal K,
\qquad
\operatorname{Fix}(\mathcal F)=
\left(\bigoplus_a M(\mathcal A_a)\otimes\tau_a\right)\oplus0_{\mathcal K},
\tag{166.9}
$$
其中 $\tau_a$ 为固定的非零正矩阵，可归一化为密度矩阵；$\mathcal K$ 是固定态共同支撑之外的空间。该结构适用于非 unital 通道，不要求预先存在满秩固定态。因而
$$
m(\mathcal F)=\sum_a(\dim\mathcal A_a)^2.
\tag{166.10}
$$
当此和等于三时，只能有三个一维 $\mathcal A_a$。物理 Hilbert 空间本身也只有三维，故每个 $\mathcal B_a$ 都一维、$\mathcal K=0$。于是存在三个正交纯态投影 $|u_i\rangle\langle u_i|$ 被 $\mathcal F$ 固定。这也证明了一个后面要用的事实：仅有 $m(\mathcal F)=3$，已经足以推出某个基下的 Schur 形式，不必先假设（166.3）。

取任意 Kraus 表示 $\mathcal F(A)=\sum_\ell K_\ell A K_\ell^\dagger$。纯态固定条件意味着每个 $K_\ell u_i$ 都在 $\mathbb C u_i$ 中，否则正算子之和会在该直线之外产生非零支撑。写 $K_\ell u_i=a_{\ell i}u_i$，便得到 Schur 系数
$$
B_{ij}=\sum_\ell a_{\ell i}\overline{a_{\ell j}}.
$$
它是 Gram 矩阵，且保持迹给出 $B_{ii}=1$。这证明式（166.4）除严格模长外的部分，同时证明 unital 性。上述外部固定空间定理只承担这个结构步骤；本节的误差门槛由式（166.6）与真实源极限共同给出。

最后处理周边模式。设 $\lambda_1,\ldots,\lambda_s$ 是全部周边特征值。有限个单位圆相位的同时回归给出整数 $N_j\to\infty$，使每个 $\lambda_a^{N_j}\to1$。这可由环面上的同时有理逼近得到；若回归取值有有限公共周期，则取其不断增大的整数倍。幂有界排除了周边非平凡 Jordan 块，其余广义特征空间在这些幂下趋于零。因此
$$
\mathcal F^{N_j}\longrightarrow\mathcal P_{\rm per},
\tag{166.11}
$$
其中 $\mathcal P_{\rm per}$ 为周边空间上的 CPTP 幂等投影，秩为 $p(\mathcal F)$。与同一序列上的 $\mathcal M_{r,0}^{N_j}\to\Delta$ 比较，得到
$$
d_{\rm ref}(\mathcal P_{\rm per},\Delta)\le W_r(\mathcal F).
\tag{166.12}
$$
式（166.6）故也给出 $p(\mathcal F)\ne3$ 时的半距下界；在（166.3）下，周边空间恰好三维。固定空间已经占满这三维，故 Schur 系数 $B_{ij}$ 在 $i\ne j$ 时都必须满足 $|B_{ij}|<1$。其幂于是收敛至 $\Delta_U$，再用式（166.8）得到（166.5）。证毕。

**命题 166.3（半距门槛在每个参数处都精确）。** 令 $P_i=|i\rangle\langle i|$、$Q=P_0+P_1$，并定义块去相干通道
$$
\mathcal B(A)=QAQ+P_2AP_2.
\tag{166.13}
$$
则 $m(\mathcal B)=p(\mathcal B)=5$，但对全部 $0<r<1$，
$$
\boxed{W_r(\mathcal B)=\frac12.}
\tag{166.14}
$$
所以定理166.2中的严格不等号不能改成非严格不等号，也不能将门槛提高。

证明。 $\mathcal B^2=\mathcal B$，其像为一个完整二阶矩阵块及一个标量块，维数为 $2^2+1^2=5$。令 $\operatorname{Ad}_U(A)=UAU^\dagger$。有
$$
\mathcal B=\frac12\left(\mathrm{Id}+
\operatorname{Ad}_{\operatorname{diag}(1,1,-1)}\right),
\qquad
\Delta=\frac12\left(\mathcal B+
\operatorname{Ad}_{\operatorname{diag}(1,-1,1)}\circ\mathcal B\right).
\tag{166.15}
$$
两个通道的 diamond 距离至多为二，故这两个等式给出
$$
\|\mathrm{Id}-\mathcal B\|_\diamond\le1,
\qquad
\|\Delta-\mathcal B\|_\diamond\le1.
$$
第一个范数以 $02$ 两标签的平衡叠加作输入达到半迹距离 $1/2$，第二个范数则由 $01$ 平衡叠加达到同一值，故两个上界都是等式。

对任意 $N\ge1$，写 $s=r^N$、$\theta=N\phi$ 和 $U_\theta=\operatorname{diag}(e^{i\theta},1,1)$。逐矩阵元计算得
$$
\mathcal M_{r,\phi}^{N}-\mathcal B
=(1-s)(\Delta-\mathcal B)
+s\,\operatorname{Ad}_{U_\theta}\circ(\mathrm{Id}-\mathcal B).
\tag{166.16}
$$
右端第一项只改变 $01$ 相干，第二项只含连接 $\{0,1\}$ 与 $\{2\}$ 的相干，并给 $02$ 项正确相位。由 diamond 范数的三角不等式及输出酉共轭不变性，右端范数至多为 $(1-s)+s=1$。结合 $\mathcal B^N=\mathcal B$，得到 $W_r(\mathcal B)\le1/2$。当 $N\to\infty$ 时真实通道趋于 $\Delta$，而 $d_{\rm ref}(\Delta,\mathcal B)=1/2$，故下界也成立。证毕。

**定理 166.4（一阶匹配下，稳定记录维数刻画全视界稳定性）。** 设任意三维 CPTP 族 $\mathcal F_r$ 满足式（166.2），不要求参数连续。以下三项等价：

1. 对所有充分接近一的 $r<1$，$m(\mathcal F_r)=3$。
2. $\sup_{N\ge0}d_{\rm ref}(\mathcal F_r^N,\mathcal T_r^N)\to0$。
3. $W_r(\mathcal F_r)\to L$，其中 $L=(\sqrt3/4)e^{-\pi/(3\sqrt3)}$。

此外，对任意满足式（166.2）的族，$W_r(\mathcal F_r)$ 在 $r\uparrow1$ 时的全部聚点均属于
$$
\boxed{\{L\}\cup[1/2,1].}
\tag{166.17}
$$
故在这类一阶匹配族中，风险不能收敛到严格介于 $L$ 与 $1/2$ 之间的数。

证明。 先由第一项推出第二项。令 $\varepsilon=1-r$，并把通道视为带 Hilbert–Schmidt 内积的九维矩阵空间上的线性算子。有限维范数等价与式（166.2）给出
$$
A_r:=\frac{\mathcal F_r-\mathrm{Id}}{\varepsilon}
\longrightarrow G_*:=
\lim_{r\uparrow1}\frac{\mathcal T_r-\mathrm{Id}}{\varepsilon}.
\tag{166.18}
$$
在原计算基的矩阵单位 $E_{ij}$ 上，$G_*$ 的三个对角方向为零；$01,10,12,21$ 四个方向的特征值为 $-1$；$02,20$ 两个方向的特征值为 $-(1+k_*)$。所以零特征值半单且恰好三重，与其余谱有正间隔。

在零附近取固定的小圆，不包围其余两个特征值。沿该圆定义的 Riesz 谱投影连续依赖于算子，故 $A_r$ 对应的谱投影趋于 $\Delta$，且充分接近一时秩为三。这里使用标准有限维矩阵函数演算；例如见 Higham、Lin，[*Matrix Functions: A Short Course*](https://eprints.maths.manchester.ac.uk/2067/1/covered/MIMS_ep2013_42.pdf)，§3.1的 Jordan、插值与 Cauchy 积分表述。

由第一项，$\ker A_r$ 本身已经三维，因此这个零附近谱簇只能由三个精确零特征值组成，没有从零分裂出来的缓慢模式。定理166.2证明中由式（166.9）—（166.10）推出的结构说明：每个这样的 $\mathcal F_r$ 都是某个正交基下的 Schur 通道。它在该基的矩阵单位上对角化，因而是 Hilbert–Schmidt 内积下的正规算子，$A_r$ 也正规。其零谱投影于是为该基下的去相干投影 $\mathcal E_r$，满足
$$
d_{\rm ref}(\mathcal E_r,\Delta)\longrightarrow0.
\tag{166.19}
$$
虽然此基可以随 $r$ 旋转，投影的收敛仍由（166.18）的谱间隔控制。

其余六个特征值 $\mu$ 只能趋近 $-1$ 或 $-(1+k_*)$，故充分接近一时统一满足 $\operatorname{Re}\mu\le-1/2$ 及 $|\mu|\le C_0$，其中 $C_0$ 与 $r$ 无关。对应的 $\mathcal F_r$ 特征值为 $1+\varepsilon\mu$，于是
$$
|1+\varepsilon\mu|^2
\le1-\varepsilon+C_0^2\varepsilon^2
\le1-\frac\varepsilon2,
\qquad
|1+\varepsilon\mu|\le1-\frac\varepsilon4
\tag{166.20}
$$
对所有充分小的 $\varepsilon$ 成立。正规性消除了 Jordan 多项式因子及随基变坏的条件数，故
$$
\|\mathcal F_r^N-\mathcal E_r\|_{2\to2}
\le e^{-\varepsilon N/4},
\qquad
\|\mathcal T_r^N-\Delta\|_{2\to2}
\le r^N\le e^{-\varepsilon N}.
\tag{166.21}
$$

为明确参考系统不带来隐含维数成本，任意纯系统—参考输入的 Schmidt 秩至多为三，可将参考限制到三维。输出所在空间至多九维，故迹范数至多为三倍 Hilbert–Schmidt 范数；输入纯态的 Hilbert–Schmidt 范数为一，而张量恒等映射不改变 $2\to2$ 算子范数。再由输入的凸分解，对任意三维通道 $\mathcal H,\mathcal K$ 都有
$$
d_{\rm ref}(\mathcal H,\mathcal K)
\le\frac32\|\mathcal H-\mathcal K\|_{2\to2}.
\tag{166.22}
$$
所以式（166.21）给出统一于全部参考系统和整数视界的指数尾界。

固定 $T>0$。当 $\varepsilon N\le T$ 时，通道复合的 telescoping 与式（166.2）给出
$$
d_{\rm ref}(\mathcal F_r^N,\mathcal T_r^N)
\le N\delta_r\le T\frac{\delta_r}{\varepsilon}\longrightarrow0.
\tag{166.23}
$$
当 $\varepsilon N>T$ 时，用（166.19）—（166.22），
$$
d_{\rm ref}(\mathcal F_r^N,\mathcal T_r^N)
\le d_{\rm ref}(\mathcal E_r,\Delta)
+\frac32\left(e^{-T/4}+e^{-T}\right).
\tag{166.24}
$$
先令 $r\uparrow1$，再令 $T\to\infty$，即得第二项。这个顺序同时控制所有整数 $N$，不把逐个有限缩放区间的收敛冒充无界视界收敛。

三角不等式还给出
$$
|W_r(\mathcal F_r)-W_r(\mathcal T_r)|
\le\sup_{N\ge0}d_{\rm ref}(\mathcal F_r^N,\mathcal T_r^N).
\tag{166.25}
$$
定理163.2给出 $W_r(\mathcal T_r)\to L$，故第二项推出第三项。若第三项成立，由 $L<1/2$，最终有 $W_r(\mathcal F_r)<1/2$，定理166.2遂推出第一项。

最后，若沿某个 $r_n\uparrow1$ 有风险收敛到 $w<1/2$，则该序列最终满足 $m(\mathcal F_{r_n})=3$。刚才的谱投影、有限区间及尾估计逐项适用于这条序列，故 $w=L$。风险总在 $[0,1]$ 内，得到式（166.17）。证毕。

**命题 166.5（一阶匹配仍可达到半距分支）。** 令 $V$ 交换计算基的 $0,1$ 标签并固定 $2$，定义 $\mathcal S=\operatorname{Ad}_V\circ\Delta$。对 $1/2<r<1$，令 $\varepsilon=1-r$、$p_r=\varepsilon^2$，并取
$$
\mathcal H_r=(1-p_r)\mathcal T_r+p_r\mathcal S.
\tag{166.26}
$$
则 $\mathcal H_r$ 为 CPTP 通道，满足式（166.2），且 $m(\mathcal H_r)=2$；对所有充分接近一的 $r<1$，恰有
$$
\boxed{W_r(\mathcal H_r)=\frac12.}
\tag{166.27}
$$
因此式（166.17）的上分支可以在其左端点达到，即使单步通道偏差只有 $O((1-r)^2)$。

证明。 通道凸组合保持 CPTP，且 $d_{\rm ref}(\mathcal H_r,\mathcal T_r)\le p_r=o(\varepsilon)$。在对角子空间上，$\mathcal H_r$ 是随机矩阵
$$
K_r=(1-p_r)I+p_r\Pi_{01},
\tag{166.28}
$$
其中 $\Pi_{01}$ 交换前两个坐标。它有两个固定方向与一个特征值 $1-2p_r$；因 $0<p_r<1/4$，后者严格介于零与一。在非对角子空间上，$\mathcal S$ 为零，故 $\mathcal H_r$ 的系数为 $(1-p_r)$ 乘以 $\mathcal T_r$ 的系数，模长都严格小于一。这证明 $m(\mathcal H_r)=2$。

取输入 $P_0$。真实源在全部步骤保持 $P_0$，而预测器的两个前部标签发生对称混合，第 $N$ 步距离为
$$
a_N=\frac{1-(1-2p_r)^N}{2}.
\tag{166.29}
$$
其上确界为 $1/2$，故每个所给 $r$ 的风险都至少为 $1/2$。

为给出渐近上界，把任意输入的对角与非对角响应分开。对全部参考系统，$\Delta-K_r^N\circ\Delta$ 的半 diamond 范数恰为 $a_N\le1/2$：对角输入块是正矩阵，每列经典转移的总变差至多为 $a_N$，三角不等式给出上界；输入 $P_0$ 达到它。真实通道的非对角乘子模长为 $r^N$，预测器的非对角乘子模长至多为 $(1-p_r)^Nr^N$，所以其差的 $2\to2$ 范数至多为 $2r^N$。与式（166.22）相同的 Schmidt 秩及范数估计适用于这个线性差映射，得到
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal H_r^N)
\le\frac12-\frac12(1-2p_r)^N+3r^N.
\tag{166.30}
$$
保留（166.30）的负项可以得到精确上界。令 $q_r=1-2\varepsilon^2$，当 $0<\varepsilon\le1/4$ 时，
$$
\frac r{q_r}=\frac{1-\varepsilon}{1-2\varepsilon^2}
\le1-\frac\varepsilon2\le e^{-\varepsilon/2}.
\tag{166.31}
$$
取固定常数 $T_0=2\log6$。若 $\varepsilon N\ge T_0$，则 $3r^N\le q_r^N/2$，式（166.30）不超过 $1/2$。若 $\varepsilon N<T_0$，有限视界 telescoping 给出 $d_{\rm ref}(\mathcal H_r^N,\mathcal T_r^N)\le Np_r$，因此
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal H_r^N)
\le W_r(\mathcal T_r)+T_0\varepsilon<\frac12
\tag{166.32}
$$
对所有充分接近一的 $r$ 成立，最后一个严格号由定理163.2的 $W_r(\mathcal T_r)\to L<1/2$ 保证。两个视界范围一起给出 $W_r(\mathcal H_r)\le1/2$；（166.29）给出相反方向，证明（166.27）。证毕。

命题165.3的稀有重置只保留一个固定方向；命题166.5的稀有交换保留两个。它们的每步变化都可以比 $1-r$ 更小，却改变了无限续接后仍然存在的记录空间。定理166.4指出，在完整通道一阶匹配的前提下，精确保留三个固定方向正是排除这类长时失准的条件。这个条件约束最终保留下来的关系，而不只是漂移速度；它仍属于所给三维、无持久辅助记忆的预测合同。

<a id="entry-682"></a>

## 追加锚（本行以下为增补区）

<a id="section-167"></a>

## 167. 长期最优反推观察坐标与临界相干律

**定义 167.1（无局部预设的最优族与双标签接口）。** 沿用定义165.1的源族、风险及渐近最优族 $\mathscr A$。以下只假设三维 CPTP 族 $\mathcal F_r$ 在某个 $(r_0,1)$ 上定义，且
$$
W_r(\mathcal F_r)\longrightarrow L,
\qquad
L=\frac{\sqrt3}{4}e^{-t_*},\quad
t_* =\frac\pi{3\sqrt3},\quad
k_* =\frac{\log2}{t_*}.
\tag{167.1}
$$
不附加单步最优、相对局部误差上界、参数连续性或式（166.2）的一阶匹配条件。仍记 $\varepsilon=1-r$、$E_{ij}=|i\rangle\langle j|$、$P_i=E_{ii}$、$P=P_0+P_2$，并取 $X=E_{02}+E_{20}$、$Y=-iE_{02}+iE_{20}$。令 $J:\mathbb C^2\to\mathbb C^3$ 为将标准基送到 $|0\rangle,|2\rangle$ 的等距映射，定义输入通道
$$
\iota_{02}(A)=JAJ^\dagger.
\tag{167.2}
$$
对输入维数为二、输出维数为三的通道，$d_{\rm ref}$ 仍按全部有限参考系统上的半迹距离上确界定义。

**定理 167.2（最优族的弱变化尺度、坐标对齐与生成元约束）。** 在定义167.1的唯一风险假设下，
$$
\|\mathcal F_r-\mathrm{Id}\|_\diamond=O(1-r).
\tag{167.3}
$$
对所有充分接近一的 $r$，定理166.2给出 $\mathcal F_r$ 的稳定去相干投影 $\mathcal E_r$。这些投影必满足
$$
\boxed{d_{\rm ref}(\mathcal E_r,\Delta)\longrightarrow0.}
\tag{167.4}
$$
定义有界的缩放算子族 $G_r=(\mathcal F_r-\mathrm{Id})/(1-r)$。它的每个算子范数聚点 $G$ 都在原计算基下为 Schur 生成元：存在 $\mu_{ij}$，使
$$
G(E_{ii})=0,\qquad
G(E_{ij})=\mu_{ij}E_{ij}\quad(i\ne j),\qquad
\operatorname{Re}\mu_{ij}<0,
\tag{167.5}
$$
并且关键系数被唯一确定为
$$
\boxed{\mu_{02}=\mu_{20}=-(1+k_*).}
\tag{167.6}
$$
特别地，整个族都满足
$$
G_r(P_i)\longrightarrow0\quad(i=0,1,2),\qquad
G_r(E_{02})\longrightarrow-(1+k_*)E_{02},\qquad
G_r(E_{20})\longrightarrow-(1+k_*)E_{20}.
\tag{167.7}
$$
本定理不确定另外四个相干方向的生成元系数，也不声称整个 $G_r$ 必有唯一极限。

证明。 先从低全视界风险得到（167.3）。选固定 $w\in(L,1/2)$，则 $r$ 充分接近一时 $W_r(\mathcal F_r)\le w$。令
$$
c=\frac{1/2-w}{2}>0,\qquad
a=2(w+c)=w+\frac12<1,\qquad
\beta=\arcsin a<\frac\pi2,\qquad
m=\left\lfloor\frac c\varepsilon\right\rfloor.
\tag{167.8}
$$
充分小的 $\varepsilon$ 下 $m\ge1$。由定理166.2，$\mathcal F_r$ 是某个正交基下的严格 Schur 通道，其非对角系数记为 $b_{ij}(r)$。相位零的真实通道满足
$$
\mathcal M_{r,0}^N=r^N\mathrm{Id}+(1-r^N)\Delta,
\qquad
d_{\rm ref}(\mathrm{Id},\mathcal M_{r,0}^N)
\le1-r^N\le N\varepsilon.
$$
故对 $1\le N\le m$，
$$
d_{\rm ref}(\mathrm{Id},\mathcal F_r^N)\le w+c.
\tag{167.9}
$$
在 $\mathcal F_r$ 自己的 Schur 基中取任意两个标签的平衡叠加，便得到对每个非对角系数 $b=b_{ij}(r)$ 都成立的
$$
|1-b^N|\le a\qquad(1\le N\le m).
\tag{167.10}
$$

因 $a<1$，$b\ne0$。写 $b=|b|e^{i\theta}$，其中 $\theta$ 为主辐角。圆盘 $\{z:|1-z|\le a\}$ 不含原点，其辐角绝对值至多为 $\beta$，而模长至少为 $1-a$。因此
$$
|b|^m\ge1-a,
\qquad
|\operatorname{Arg}(b^N)|\le\beta\quad(1\le N\le m).
\tag{167.11}
$$
这些主辐角条件还迫使没有绕圈：$|\theta|\le\beta$；若 $|(N-1)\theta|\le\beta$，则 $|N\theta|\le2\beta<\pi$，此时 $N\theta$ 就是主辐角，再用（167.11）可得 $|N\theta|\le\beta$。归纳给出 $m|\theta|\le\beta$。于是
$$
|1-b|\le1-|b|+|\theta|
\le-\log|b|+|\theta|
\le\frac{-\log(1-a)+\beta}{m}.
\tag{167.12}
$$
Schur 基的矩阵单位是 Hilbert–Schmidt 正交归一的特征基，故 $\|\mathcal F_r-\mathrm{Id}\|_{2\to2}=\max_{i\ne j}|1-b_{ij}(r)|$。当 $\varepsilon\le c/2$ 时 $m\ge c/(2\varepsilon)$，再由式（166.22）的 diamond 与 Hilbert–Schmidt 算子范数比较，得到（167.3）。这里的 $O(\varepsilon)$ 尺度由全视界风险导出，没有从局部假设取得。

现取任意 $r_n\uparrow1$。上述有界性允许取子列，使 $G_{r_n}\to G$。同时可取各预测器的 Schur 基酉矩阵 $U_n$，再由酉群的紧性取子列，使 $U_n\to U$。在这些基中，$G_{r_n}$ 对三个对角方向为零，对其余方向为有界标量乘法。因此 $G$ 在 $U$ 基中也是 Schur 算子，且是 Hilbert–Schmidt 正规算子。

有界生成元的 Euler 极限给出，对每个固定 $t\ge0$，
$$
\mathcal F_{r_n}^{\lfloor t/\varepsilon_n\rfloor}
\longrightarrow e^{tG},\qquad \varepsilon_n=1-r_n.
\tag{167.13}
$$
例如，$\log(\mathrm{Id}+\varepsilon_nG_{r_n})=\varepsilon_nG_{r_n}+O(\varepsilon_n^2)$ 的一致范数估计给出此式；这与定理165.2使用的有限维矩阵函数论证相同。每个左侧都是 CPTP，故 $e^{tG}$ 也 CPTP；其特征值模长至多为一，因而 $G$ 的谱实部非正。

对固定 $u\in[-\sqrt3,\sqrt3]$，选择实际允许的相位
$$
\phi_n=\frac u{\sqrt3}\alpha(r_n).
$$
由定理161.6的 $\alpha(r_n)/\varepsilon_n\to\sqrt3$，相同视界上的真实源趋于
$$
\mathcal R_{t,u}(A)
=C(e^{-t},e^{iut})\odot A.
\tag{167.14}
$$
因此对每个固定的 $t\ge0$ 与上述 $u$，原风险假设给出
$$
d_{\rm ref}(e^{tG},\mathcal R_{t,u})\le L.
\tag{167.15}
$$
$t=0$ 时两侧通道都是恒等通道。对正 $t$，所用离散视界最终至少为一。式（167.14）由合法通道的极限得到，不另行假设任意连续相位族自动完全正。

先排除 $G$ 的额外零衰减模式。对 CPTP 通道 $\mathcal Q=e^G$ 和整数 $N\ge1$，式（167.15）的 $t=N,u=0$ 给出
$$
d_{\rm ref}(\mathcal Q^N,\mathcal M_{e^{-1},0}^N)\le L<\frac12.
\tag{167.16}
$$
定理166.2中式（166.8）与（166.12）的秩论证只用了相位零，故直接适用于（167.16）：$\mathcal Q$ 的固定与周边空间维数均为三。$G$ 在 $U$ 基中的三个对角方向已经为零，若任一非对角特征值的实部为零，就会给 $e^G$ 增加周边维数。因此 $G$ 的其余六个 Schur 系数均有严格负实部，且
$$
\ker G=\operatorname{span}\{|u_i\rangle\langle u_i|:i=0,1,2\}.
\tag{167.17}
$$
这里先对每个有限 $t$ 建立（167.15），随后研究这个已得到的半群本身的全部整数幂；没有交换原参数极限与原视界上确界。

在 $t=t_*$ 时，取实际端点 $u=\pm\sqrt3$，并对赤道输入 $\rho_\theta=(P+\cos\theta X+\sin\theta Y)/2$ 应用（167.15）。两端输出的 Bloch 方向相差 $2\pi/3$，模长为 $e^{-t_*}$，距离为 $2L$。式（165.15）的无迹 Hermitian 平行四边形论证表明，在整个三维态空间中，同时距两个端点至多 $L$ 的态只能是其中点。因此
$$
e^{t_*G}(P)=P,\qquad
e^{t_*G}(X)=\lambda_*X,\qquad
e^{t_*G}(Y)=\lambda_*Y,
\quad
\lambda_* =\frac{e^{-t_*}}2=e^{-(1+k_*)t_*}.
\tag{167.18}
$$
由于 $G$ 的非零特征值均有负实部，$e^{t_*G}$ 的固定空间就是 $\ker G$；所以 $P$ 在 $U$ 基中为对角矩阵。$P$ 是秩二正交投影，故 $U$ 基的两个向量位于 $\operatorname{span}\{|0\rangle,|2\rangle\}$，第三个位于 $\mathbb C|1\rangle$。

另一方面，$e^{t_*G}$ 保留 $U$ 基下的全部对角元，且 $\lambda_*\ne1$。式（167.18）于是要求 $X,Y$ 在这个基中的全部对角元为零。对其中任一位于 $P\mathbb C^3$ 的基向量 $v=a|0\rangle+b|2\rangle$，这意味着
$$
\langle v,Xv\rangle=2\operatorname{Re}(\overline a b)=0,
\qquad
\langle v,Yv\rangle=2\operatorname{Im}(\overline a b)=0.
$$
故 $\overline a b=0$，每个这样的基向量只能是 $|0\rangle$ 或 $|2\rangle$ 的相位倍数。$U$ 因此是计算基的置换及逐向量相位变换；$G$ 已在原计算基下为 Schur 算子。这证明（167.5）。

记其 $02$ 系数为 $\mu$。由（167.18），
$$
e^{t_*\mu}=\lambda_*,
\qquad
\mu=-(1+k_*)+\frac{2\pi i j}{t_*}
\quad\text{某个 }j\in\mathbb Z.
\tag{167.19}
$$
若 $j\ne0$，取 $t_j=t_*/(2|j|)\le t_*/2$。在输入 $(|0\rangle+|2\rangle)(\langle0|+\langle2|)/2$ 上，$e^{t_jG}$ 的相干系数为负实数 $-e^{-(1+k_*)t_j}$，相位零的真实极限通道系数则为正实数 $e^{-t_j}$。于是
$$
d_{\rm ref}(e^{t_jG},\mathcal R_{t_j,0})
\ge\frac{e^{-t_j}+e^{-(1+k_*)t_j}}2
\ge\frac{e^{-t_*/2}}2>L.
\tag{167.20}
$$
最后一个严格号等价于 $2e^{t_*/2}>\sqrt3$。这与（167.15）矛盾，故 $j=0$；保 Hermitian 性给出 $20$ 系数为其共轭，得到（167.6）。排除对数分支所用的是实际中间时刻的误差约束，不是预先给定的生成元小范数界。

上述推导适用于任意生成元聚点。若（167.4）不成立，可以选一条投影始终远离 $\Delta$ 的参数序列，再同时提取 $G_{r_n}$ 与 $U_n$ 的收敛子列。但已经证明其极限基只差计算基的置换和相位，因此 $\mathcal E_{r_n}=\operatorname{Ad}_{U_n}\circ\Delta\circ\operatorname{Ad}_{U_n^\dagger}\to\Delta$，矛盾。最后，有界族 $G_r$ 的每个聚点都在（167.7）指定的输入上取同一个值，再用相同的子列反证法，得到整个族的（167.7）。证毕。

**定理 167.3（关键双标签接口的全视界唯一行为）。** 在定义167.1的条件下，即使不假设完整通道一阶匹配，仍有
$$
\boxed{
\sup_{N\ge0}
d_{\rm ref}\bigl(\mathcal F_r^N\circ\iota_{02},
\mathcal T_r^N\circ\iota_{02}\bigr)
\longrightarrow0.
}
\tag{167.21}
$$
上确界包含所有整数视界，距离包含输入的任意有限参考系统。它只约束 $02$ 双标签输入接口，不宣称所有三标签输入上都有同样的全视界唯一性。

证明。 由（167.4），可以在 $\mathcal F_r$ 的 Schur 基中选择标签与向量相位，使对应酉矩阵满足 $U_r\to I$。说明这种选择为何不需要参数连续性：若无法把基向量逐一对齐到计算基，则可取一条与所有置换、相位对齐均有正距离的序列。酉群紧性给出极限基，而（167.4）要求该极限基的对角代数恰好等于计算基对角代数，其三个最小投影只能是 $P_0,P_1,P_2$ 的置换，与所取正距离矛盾。对齐后逐列选相位，即得 $U_r\to I$。

令
$$
\widetilde{\mathcal F}_r
=\operatorname{Ad}_{U_r^\dagger}\circ\mathcal F_r\circ\operatorname{Ad}_{U_r},
\qquad
\widetilde G_r
=\operatorname{Ad}_{U_r^\dagger}\circ G_r\circ\operatorname{Ad}_{U_r}.
\tag{167.22}
$$
前者在原计算基下为 Schur 通道。由于 $G_r$ 有界且 $U_r\to I$，$\widetilde G_r-G_r\to0$；恒等算子在共轭下不变，所以严格有 $\widetilde{\mathcal F}_r=\mathrm{Id}+\varepsilon\widetilde G_r$。由（167.7），其 $02$ 系数 $b_r$ 满足
$$
b_r=1-(1+k_*)\varepsilon+o(\varepsilon).
\tag{167.23}
$$
这里对齐的是有界生成元，因而不需要 $\|U_r-I\|=o(\varepsilon)$ 一类额外速率假设。

$\mathcal T_r$ 在同一方向的系数为 $s_r=r^{1+k_*}=1-(1+k_*)\varepsilon+O(\varepsilon^2)$。因此
$$
|b_r-s_r|=o(\varepsilon),\qquad
q_r:=\max\{|b_r|,s_r\}\le1-c_0\varepsilon
\tag{167.24}
$$
对某个固定 $c_0>0$ 及全部充分接近一的 $r$ 成立。对任意 $N\ge1$，标量幂的 telescoping 给出
$$
|b_r^N-s_r^N|
\le|b_r-s_r|Nq_r^{N-1}
\le\frac{|b_r-s_r|}{1-q_r}\longrightarrow0,
\tag{167.25}
$$
最后一个上界与 $N$ 无关，其中用到 $Nq^{N-1}\le\sum_{j=0}^{N-1}q^j\le(1-q)^{-1}$。

对 $02$ 输入，这两个 Schur 通道的幂只在该相干系数上不同。式（161.11）的单边块范数论证给出同样的全参考精确距离
$$
d_{\rm ref}\bigl(\widetilde{\mathcal F}_r^N\circ\iota_{02},
\mathcal T_r^N\circ\iota_{02}\bigr)
=\frac12|b_r^N-s_r^N|.
\tag{167.26}
$$
也可直接由二阶正块矩阵的非对角块迹范数至多为 $1/2$ 得到上界，再由无参考的平衡输入达到等号。$N=0$ 时距离为零。

最后，输入与输出的酉共轭差不随迭代次数累积：
$$
\mathcal F_r^N
=\operatorname{Ad}_{U_r}\circ\widetilde{\mathcal F}_r^N\circ
\operatorname{Ad}_{U_r^\dagger}.
$$
通道前后复合对全参考距离收缩，因此对全部 $N\ge0$，
$$
d_{\rm ref}\bigl(\mathcal F_r^N\circ\iota_{02},
\widetilde{\mathcal F}_r^N\circ\iota_{02}\bigr)
\le d_{\rm ref}(\operatorname{Ad}_{U_r},\mathrm{Id})
+d_{\rm ref}(\operatorname{Ad}_{U_r^\dagger},\mathrm{Id})
\longrightarrow0.
\tag{167.27}
$$
此式已包含旋转后输入向第三标签的分量，无需假设原 $02$ 子空间被 $\mathcal F_r$ 精确保持。合并（167.25）—（167.27），得到（167.21）。证毕。

定理167.2—167.3由全视界最优性反推弱变化尺度、稳定坐标及关键输入接口的唯一长期行为。第165节的精确局部代价仍成立；本节移除的是对候选族局部接近程度的预设，并不确定其余相干方向的自由度。这里的坐标对齐始终相对于定义161.1给定的校准基；对整个实验作同一酉共轭，会将校准基、源族、预测器及结论中的投影一同共轭。

<a id="entry-684"></a>

## 追加锚（本行以下为增补区）

<a id="section-168"></a>

## 168. 最优预测器的连续自由度与完整动力学的不唯一性

**定义 168.1（保留关键相干的附加去相干族）。** 沿用定义165.1的源族、全参考距离、风险 $W_r$ 及常数 $L,t_*,k_*$，并沿用定理163.2的预测器 $\mathcal T_r$。所有预测器仍是同一三维系统上的一个固定 CPTP 通道，以其幂服务全部视界，没有持久辅助记忆。令
$$
Z=\operatorname{diag}(1,-1,1),\qquad
\mathcal D_u=\frac{1+u}{2}\mathrm{Id}
+\frac{1-u}{2}\operatorname{Ad}_Z\quad(0\le u\le1),
\qquad
\mathcal F_{h,r}=\mathcal T_r\circ\mathcal D_{r^h}
\quad(h\ge0).
\tag{168.1}
$$
$\mathcal D_u$ 是酉通道的凸组合，故 $\mathcal F_{h,r}$ 对全部 $0<r<1$ 都为 CPTP。它保留三个对角元，且相干系数为
$$
b_{01}=b_{10}=b_{12}=b_{21}=r^{1+h},\qquad
b_{02}=b_{20}=r^{1+k_*}.
\tag{168.2}
$$
再定义与 $r$ 无关的正数
$$
T_0=\log\frac2L,\qquad
h_0=\frac{1-e^{-k_*T_0}}{2T_0}>0.
\tag{168.3}
$$
该区间是下面构造的充分范围，不定义全部最优预测器的最大参数范围。

**定理 168.2（连续多个预测器的精确风险夹界）。** 对任意 $0<r<1$ 及任意 $h\in[0,h_0]$，
$$
\boxed{
W_r(\mathcal T_r)
\le W_r(\mathcal F_{h,r})
\le\max\{W_r(\mathcal T_r),L\}.
}
\tag{168.4}
$$
因此，对任意函数 $h:(r_0,1)\to[0,h_0]$，不要求它连续或收敛，均有
$$
\lim_{r\uparrow1}W_r(\mathcal F_{h(r),r})=L.
\tag{168.5}
$$

证明。 固定视界 $N\ge1$ 及合法实际相位 $\phi$，令
$$
x=-N\log r>0,\qquad s=e^{-x}=r^N,\qquad
d=s(1-e^{-hx}),\qquad
w=s(e^{iN\phi}-e^{-k_*x}),\quad q=|w|.
\tag{168.6}
$$
$\mathcal M_{r,\phi}^N-\mathcal F_{h,r}^N$ 是 Hermitian Schur 乘子，其乘子矩阵为
$$
B=\begin{pmatrix}0&d&w\\d&0&d\\\overline w&d&0\end{pmatrix}.
\tag{168.7}
$$
先在本证明内建立所需的支配估计：若 $2d\le q$，则此差的全参考半迹范数恰为 $q/2$。$q=0$ 时 $d=0$，结论直接成立。否则写 $w=qe^{i\theta}$，取
$$
Y=\begin{pmatrix}
q&de^{i\theta}&0\\
de^{-i\theta}&q&de^{i\theta}\\
0&de^{-i\theta}&q
\end{pmatrix}.
\tag{168.8}
$$
两个矩阵 $Y\pm B$ 都半正定。确实，将 $02$ 块排在前面，该块分别为
$$
\begin{pmatrix}q&\pm qe^{i\theta}\\\pm qe^{-i\theta}&q\end{pmatrix},
$$
其秩为一；连接标签 $1$ 的列向量分别为
$$
v_\pm=d\begin{pmatrix}e^{i\theta}\pm1\\e^{-i\theta}\pm1\end{pmatrix}.
$$
它们位于对应秩一块的像中。该块的非零特征值为 $2q$，所以 Schur 补条件为
$$
q\ge \frac{\|v_\pm\|^2}{2q}
=\frac{d^2|e^{i\theta}\pm1|^2}{q},
$$
这由 $2d\le q$ 保证。正半定乘子给出完全正 Schur 映射，是第161节所用相关矩阵框架的标准正性事实。

记 $S_B,S_Y$ 为对应 Schur 映射。对任意系统与有限参考的联合密度矩阵 $\rho$，令
$$
A=(S_Y\otimes\mathrm{Id})(\rho),\qquad
H=(S_B\otimes\mathrm{Id})(\rho).
$$
因为 $S_Y\pm S_B$ 完全正，故 $A\ge0$ 且 $-A\le H\le A$。$Y$ 的三个对角元均为 $q$，从而 $\operatorname{Tr}A=q$。分别以 $H$ 的正、负谱投影压缩上述两个不等式并取迹，可得
$$
\|H\|_1\le\operatorname{Tr}A=q.
\tag{168.9}
$$
另一方面，无参考的平衡 $02$ 输入使输出差只含系数 $w/2$ 及其共轭，迹范数为 $q$。因此，当 $2d\le q$ 时，精确距离为
$$
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal F_{h,r}^N)=\frac q2.
\tag{168.10}
$$

当 $0<x\le T_0$，函数 $1-e^{-k_*x}$ 的凹性及其在零点的零值给出
$$
2(1-e^{-hx})\le2hx\le2h_0x
=\frac{x}{T_0}(1-e^{-k_*T_0})
\le1-e^{-k_*x}
\le|e^{iN\phi}-e^{-k_*x}|.
\tag{168.11}
$$
乘以 $s$ 得到 $2d\le q$。故在此范围，式（168.10）与式（161.11）共同给出
$$
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal F_{h,r}^N)
=d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal T_r^N).
\tag{168.12}
$$
当 $x\ge T_0$，将（168.7）拆为三个单边乘子，分别使用式（161.11）的正块矩阵估计及三角不等式，得到
$$
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal F_{h,r}^N)
\le d+\frac q2
\le2e^{-x}\le2e^{-T_0}=L.
\tag{168.13}
$$
这两段估计都是实际离散视界上的界，不需要交换参数极限与视界上确界。它们证明（168.4）的上界。对于每个 $N,\phi$，平衡 $02$ 输入也总给出下界 $q/2$，而 $\mathcal T_r$ 的完整距离恰为 $q/2$。取上确界便得到（168.4）的下界。最后由定理163.2的 $W_r(\mathcal T_r)\to L$ 夹逼得到（168.5）；夹界与所选 $h$ 无关，所以也允许任意参数函数 $h(r)$。证毕。

**定理 168.3（接近弱记录极限时的有限参数风险相等）。** 存在 $r_1<1$，使对所有 $r\in(r_1,1)$ 及所有 $h\in[0,h_0]$，
$$
\boxed{W_r(\mathcal F_{h,r})=W_r(\mathcal T_r)>L.}
\tag{168.14}
$$
此式是这组候选预测器之间的精确比较，不断言它们达到有限 $r$ 的无约束 minimax 值 $\mathcal J(r)$。

证明。 令 $a=-\log r\downarrow0$。式（161.20）等价于
$$
\cos\alpha(r)=\frac{3e^a-e^{3a}}2
=1-\frac32a^2-2a^3+O(a^4).
$$
结合 $\alpha(r)/a\to\sqrt3$ 与余弦的 Taylor 展开，得到
$$
\frac{\alpha(r)}a=\sqrt3+\frac2{\sqrt3}a+O(a^2).
\tag{168.15}
$$
在 $(t_*,\sqrt3)$ 邻域定义光滑函数
$$
f(x,b)=\frac{e^{-x}}2
\sqrt{1+e^{-2k_*x}-2e^{-k_*x}\cos(bx)}.
\tag{168.16}
$$
它给出 $\mathcal T_r$ 在实际端点相位 $\phi=\alpha(r)$、缩放视界 $x=Na$ 上的精确距离。由 $k_*t_* =\log2$、$\sqrt3t_* =\pi/3$，直接求导得
$$
f(t_*,\sqrt3)=L,\qquad
\partial_x f(t_*,\sqrt3)=0,\qquad
\partial_b f(t_*,\sqrt3)=\frac{t_*e^{-t_*}}4>0.
\tag{168.17}
$$
取最接近 $t_*/a$ 的正整数 $N_a$，则 $N_aa=t_*+O(a)$。二元 Taylor 展开、（168.15）及（168.17）给出
$$
f\left(N_aa,\frac{\alpha(r)}a\right)
=L+\frac{t_*e^{-t_*}}{2\sqrt3}a+O(a^2)>L
\tag{168.18}
$$
对所有充分小的正 $a$ 成立。此时 $N_a\alpha(r)$ 接近 $\pi/3$，所用端点始终是原合同允许的实际相位。故 $W_r(\mathcal T_r)>L$；代入（168.4），得到对全部 $h\in[0,h_0]$ 同时成立的（168.14）。证毕。

**定理 168.4（相同最优风险不确定完整动力学）。** 对任意不同的 $h_1,h_2\in[0,h_0]$、任意 $0<r<1$ 和整数 $N\ge1$，
$$
d_{\rm ref}(\mathcal F_{h_1,r}^N,\mathcal F_{h_2,r}^N)
=\frac12\left|r^{(1+h_1)N}-r^{(1+h_2)N}\right|.
\tag{168.19}
$$
特别地，虽两族均满足 $W_r\to L$，仍有
$$
\liminf_{r\uparrow1}\sup_{N\ge1}
d_{\rm ref}(\mathcal F_{h_1,r}^N,\mathcal F_{h_2,r}^N)
\ge\frac12\left|e^{-(1+h_1)}-e^{-(1+h_2)}\right|>0.
\tag{168.20}
$$
还存在渐近最优族，其缩放生成元在 $r\uparrow1$ 时不收敛。

证明。 令 $v=r^{(1+h_1)N}-r^{(1+h_2)N}$。两个通道幂的差只在 $01,10,12,21$ 四个方向乘以 $v$，故严格等于
$$
\mathcal F_{h_1,r}^N-\mathcal F_{h_2,r}^N
=\frac v2(\mathrm{Id}-\operatorname{Ad}_Z).
\tag{168.21}
$$
任意联合密度矩阵被两个酉通道送出的态，其差的迹范数至多为二，所以全参考半距离至多为 $|v|/2$。无参考的平衡 $01$ 输入及其 $Z$ 共轭正交，达到该上界，证明（168.19）。取 $N=\lfloor(1-r)^{-1}\rfloor$，即得（168.20）。差异可在固定校准接口上直接读出，不是对同一通道重命名基向量。

最后取
$$
h(r)=\frac{h_0}{2}\left(1+\sin\frac1{1-r}\right),\qquad
\mathcal F_r=\mathcal F_{h(r),r}.
\tag{168.22}
$$
由（168.5），此族仍渐近最优。记 $G_r=(\mathcal F_r-\mathrm{Id})/(1-r)$；对有界的 $h(r)$，一致 Taylor 展开给出
$$
G_r(E_{01})=\bigl(-(1+h(r))+O(1-r)\bigr)E_{01}.
\tag{168.23}
$$
选择 $1/(1-r)=\pi/2+2\pi n$ 与 $1/(1-r)=3\pi/2+2\pi n$ 两条趋于无穷的序列，分别得到系数极限 $-(1+h_0)$ 与 $-1$。故整个生成元族不收敛。其 $02$ 系数和稳定去相干投影仍满足第167节的强制结论。证毕。

第167节确定的关键接口与本节构造的连续自由度可同时存在：全视界最优值限定若干关系，却不唯一规定全部动力学。本节给出的自由度只是一段共同改变 $01,12$ 衰减率的显式充分区间，不是所有最优生成元的分类，也不把风险相等解释成各个输入上的预测等价。

<a id="entry-686"></a>

## 追加锚（本行以下为增补区）

<a id="section-169"></a>

## 169. 一个持久经典比特消除局部最优的长期代价

**定义 169.1（同一个联合通道的有限记忆预测合同）。** 沿用定义161.1的三标签源 $\mathcal M_{r,\phi}$、固定未知相位 $|\phi|\le\alpha(r)$、逐步新鲜的真实记录单元，以及定义161.2的全参考距离。取 $1/\sqrt3<r<1$，故 $0<\alpha(r)<\pi/2$。预测者现在允许选一个有限维辅助空间 $K$、其密度矩阵 $\sigma_r$，以及作用于 $B(\mathbb C^3\otimes K)$ 的同一个 CPTP 通道 $\Lambda_r$。它们可以依赖已知的 $r$，但不依赖未知的 $\phi$、视界 $N$ 或系统与参考的输入态。记忆只在开始时初始化，初态与系统及参考独立；定义
$$
\mathcal P_{r,N}(A)=\operatorname{Tr}_K
\Lambda_r^N(A\otimes\sigma_r),\qquad N\ge0,
\tag{169.1}
$$
以及
$$
W_r^{\rm mem}(\Lambda_r,\sigma_r)
=\sup_{N\ge1}\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}).
\tag{169.2}
$$
系统与记忆之间没有额外的随步数改变的控制。这里仍只比较终端系统通道，不访问真实源的旧记录，也不取得额外相位校准。联合通道及记忆初始化的框架是标准有限记忆通道方法，参见 Dennis Kretschmann、Reinhard F. Werner，*Quantum Channels with Memory*，[arXiv:quant-ph/0502106v2](https://arxiv.org/pdf/quant-ph/0502106v2)，§III A；该处主要讨论消息串的串接，本定义明确采用同一系统的重复演化。

令 $H(r)=\sup_{N\ge1}\mathcal R_N(r)$。分别以 $J_{\rm mem}(r)$ 与 $J_{{\rm mem},1}(r)$ 表示（169.2）在全部有限维上述合同上的下确界，以及进一步要求
$$
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi},\mathcal P_{r,1})
=\mathcal R_1(r)
\tag{169.3}
$$
时的下确界。维数一恰好退化为定义163.1的通道幂合同；一个被持续保留的随机种子同样属于记忆，不能计为维数一。

**定理 169.2（端点比特的合法实现与精确风险）。** 取 $K=\mathbb C^2$，基向量标为 $s=\pm$，并取 $\sigma=(|+\rangle\langle+|+|-\rangle\langle-|)/2$。令
$$
\Lambda_r(X)=\sum_{s=\pm}
\mathcal M_{r,s\alpha(r)}
\bigl((I\otimes\langle s|)X(I\otimes|s\rangle)\bigr)
\otimes|s\rangle\langle s|.
\tag{169.4}
$$
则 $\Lambda_r$ 为 CPTP，其记忆始终可保持为经典比特，且
$$
\mathcal P_{r,N}^{\rm bit}
=\frac12\bigl(\mathcal M_{r,\alpha(r)}^N
+\mathcal M_{r,-\alpha(r)}^N\bigr).
\tag{169.5}
$$
它精确满足单步最优条件（169.3）。若
$$
m(x)=
\begin{cases}
\sin x,&0\le x\le\pi/2,\\
1-\cos x,&\pi/2\le x\le\pi,\\
1+|\cos x|,&x\ge\pi,
\end{cases}
\tag{169.6}
$$
则每个整数视界的精确风险为
$$
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{\rm bit})
=\frac{r^N}{2}m(N\alpha(r)).
\tag{169.7}
$$

证明。 为每个合法端点通道选一组 Kraus 算符 $K_{s,j}$，则（169.4）的 Kraus 算符为 $K_{s,j}\otimes|s\rangle\langle s|$，且其伴随乘积之和为 $I\otimes I_K$。这也在含记忆非对角块的任意联合输入上证明完全正与保迹，未将通道只定义在经典输入上。对初始经典比特逐次应用（169.4），标签 $s$ 不变，条件系统演化为 $\mathcal M_{r,s\alpha}^N$，故得到（169.5）。辅助比特与真实相位独立，它是预测器自行选取的内部标签，不是对真实相位的读取。

第162节已经给出固定端点混合的相干因子 $\cos(N\alpha)$，并区分它与每步重抽后的 $(\cos\alpha)^N$；此处将该既有构造放入（169.1）的联合 CPTP 合同。由（169.5），预测器的 $01,12$ 系数为 $r^N$，$02$ 系数为 $r^N\cos(N\alpha)$。因此式（161.11）给出包含任意参考系统的精确距离
$$
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{\rm bit})
=\frac{r^N}{2}|e^{iN\phi}-\cos(N\alpha)|.
\tag{169.8}
$$
令 $x=N\alpha$。当 $x\le\pi/2$，实中心 $\cos x\ge0$，允许弧上最远点为 $e^{\pm ix}$，距离为 $\sin x$。当 $\pi/2\le x\le\pi$，中心非正，弧包含最远点 $1$，距离为 $1-\cos x$。当 $x\ge\pi$，允许弧覆盖单位圆，最大距离为 $1+|\cos x|$。这证明（169.6）—（169.7）。$N=1$ 时，预测器恰为定义162.1的 $\mathcal F_*$，所以满足（169.3）。证毕。

**定理 169.3（弱记录邻域中的精确有限记忆 minimax 值）。** 存在 $r_2<1$，使对全部 $r\in(r_2,1)$，一个经典比特同时达到
$$
\boxed{
J_{\rm mem}(r)=J_{{\rm mem},1}(r)
=W_r^{\rm mem}(\Lambda_r,\sigma)=H(r).
}
\tag{169.9}
$$
因此它单步无超额风险，且全视界风险趋于
$$
\boxed{L=\frac{\sqrt3}{4}e^{-t_*},\qquad
t_* =\frac\pi{3\sqrt3}.}
\tag{169.10}
$$
式（169.9）是充分接近一时的有限参数精确等式，不指定一个未经求出的数值阈值 $r_2$。

证明。 每个 $\mathcal P_{r,N}$ 都是合法 CPTP 通道，故由逐视界最优值的定义，对任意记忆维数、任意 $\Lambda_r,\sigma_r$ 均有
$$
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N})
\ge\mathcal R_N(r).
\tag{169.11}
$$
取上确界和下确界便得 $J_{{\rm mem},1}(r)\ge J_{\rm mem}(r)\ge H(r)$。这个下界也允许记忆维数随 $r$ 改变，不需要紧性或先假设下确界可达。

考察比特构造。令 $\varepsilon=1-r$。函数 $m$ 连续、有界且全局 Lipschitz，故与定理161.6相同的有限区间一致极限给出
$$
\frac{r^{\lfloor t/\varepsilon\rfloor}}2
m(\lfloor t/\varepsilon\rfloor\alpha(r))
\longrightarrow
b(t):=\frac{e^{-t}}2m(\sqrt3t).
\tag{169.12}
$$
同时，对全部离散视界都有统一尾界
$$
0\le\frac{r^N}{2}m(N\alpha(r))\le e^{-\varepsilon N}.
\tag{169.13}
$$
在第一段 $0\le t\le\pi/(2\sqrt3)$，$b(t)=e^{-t}\sin(\sqrt3t)/2$，其唯一最大点是 $t_*$，值为 $L$。在第二段 $\pi/(2\sqrt3)\le t\le\pi/\sqrt3$，求导可知最大点为 $2t_*$，最大值为
$$
B_2=\frac34e^{-2t_*}<L.
\tag{169.14}
$$
最后一段满足
$$
b(t)\le e^{-t}\le B_3:=e^{-\pi/\sqrt3}<L.
\tag{169.15}
$$
两严格号分别等价于 $t_*>\log\sqrt3$ 和 $2t_*>\log(4/\sqrt3)$。例如 $\sqrt3<7/4$、$\pi>3$ 给出 $t_*>4/7$；由指数级数 $e^{11/10}>3$ 得 $\log\sqrt3<11/20<4/7$。又 $4/\sqrt3<3$，所以 $\log(4/\sqrt3)<\log3<11/10<8/7<2t_*$。因此两处都有严格余量。有限区间一致收敛及（169.13）已证明比特构造的全视界风险趋于 $L$。

为得到有限 $r$ 的精确等式，还需将晚视界与早视界分开。记 $B=\max\{B_2,B_3\}<L$。有
$$
\limsup_{r\uparrow1}
\sup_{N\alpha(r)\ge\pi/2}
\frac{r^N}{2}m(N\alpha(r))\le B.
\tag{169.16}
$$
严格说明移动分界的处理：先用（169.13）排除 $\varepsilon N$ 任意大的尾；若（169.16）失败，可选晚视界序列 $N_j$，使 $\varepsilon_jN_j$ 在有界区间内收敛到 $t$。由 $\alpha(r_j)/\varepsilon_j\to\sqrt3$，晚视界条件给出 $\sqrt3t\ge\pi/2$；一致收敛使风险趋于 $b(t)\le B$，矛盾。

另一方面，取 $N_r=\lfloor t_*/\varepsilon\rfloor$，它最终属于早视界 $N_r\alpha(r)<\pi/2$，且风险趋于 $L$。选任意 $\eta\in(0,(L-B)/3)$；充分接近一时，晚视界全部风险至多 $B+\eta$，上述早视界风险至少 $L-\eta>B+\eta$。所以比特构造的全视界上确界只能在早视界取得。由（169.7）和定理161.3，每个早视界的风险精确等于 $\mathcal R_N(r)$，于是
$$
W_r^{\rm mem}(\Lambda_r,\sigma)
=\sup_{N\alpha(r)<\pi/2}\mathcal R_N(r)\le H(r).
$$
结合（169.11）的反向不等式，得到（169.9）。比特构造已满足单步限制，故两个下确界同时由它达到。证毕。

**定理 169.4（同时局部与长期最优的最小持久维数）。** 在定义169.1的齐次联合通道合同内，对所有充分接近一的 $r$，要同时满足单步最优条件（169.3）及全视界风险等于 $H(r)$，最小记忆 Hilbert 空间维数恰为二；一个经典比特即可达到。若只要求全视界风险趋于 $L$ 并保持精确单步最优，维数一下界仍成立，甚至不允许维数一在某条 $r\uparrow1$ 的子序列上出现。

证明。 维数二的上界由定理169.3给出。维数一时，$\mathcal P_{r,N}=\mathcal F_r^N$。一旦满足单步最优，定理162.2对全部 CPTP 预测器给出
$$
W_r^{\rm mem}\ge\sup_{N\ge1}\mathcal E_N(r).
\tag{169.17}
$$
由定理162.4与定理161.6，两边所需比较量的极限为
$$
\sup_N\mathcal E_N(r)\longrightarrow
G_*:=\sqrt{\frac37}\exp\!\left[-\frac2{\sqrt3}
\arctan\frac{\sqrt3}{2}\right]>L,
\qquad H(r)\longrightarrow L.
\tag{169.18}
$$
严格极限差使（169.17）在充分接近一时排除 $W_r^{\rm mem}=H(r)$，也排除沿任意趋于一的维数一子序列有风险趋于 $L$。这对量子记忆也成立，因为维数一只有平凡状态空间。必要性依赖同一联合通道、一次初始化及所给局部要求；未计入的外部时钟或持续随机种子会改变合同。证毕。

**定理 169.5（终端最优不保证干预历史接近）。** 固定任意 $1/\sqrt3<r<1$，令 $q=r\sin\alpha(r)>0$。若扩展实验合同，允许每一步重新制备系统、测量并保存经典结果，则存在不访问预测器记忆的测试，使实际相位零的源与（169.4）的比特预测器，在 $N$ 步测量历史上的总变差距离至少为
$$
\max\left\{0,1-\frac8{Nq^2}\right\}.
\tag{169.19}
$$
因此这种干预实验的全视界可区分度上确界为一，包括（169.9）成立的参数范围。

证明。 每步输入 $|+_{02}\rangle=(|0\rangle+|2\rangle)/\sqrt2$，在通道作用后测量 $02$ 子空间的 Pauli $Y$，记录 $Y_j\in\{-1,1\}$，然后重新制备相同输入。两个模型都保持该子空间，所以测量可扩展到全三维空间，而第三个标签的结果概率始终为零。相位零的真实源每步给出均值零的结果；逐步新鲜的环境及重新制备使这些结果独立。对比特预测器，条件于起初保留的标签 $s$，每步结果独立，均值为 $q$ 或 $-q$，符号取决于矩阵元约定。测试者不读取标签，其历史分布是这两种独立样本律的等权混合。

令 $\overline Y_N=N^{-1}\sum_{j=1}^NY_j$，考虑事件 $A_N=\{|\overline Y_N|<q/2\}$。每种条件样本律的单次方差至多为一。由 Chebyshev 不等式，
$$
\Pr_{\phi=0}(A_N)\ge1-\frac4{Nq^2},\qquad
\Pr_{\rm bit}(A_N)\le\frac4{Nq^2}.
\tag{169.20}
$$
第二式分别在均值 $q$ 与 $-q$ 的条件律下成立，再作等权平均。总变差距离至少为任何一个事件的概率差，故得到（169.19）。取 $N\to\infty$，并用总变差距离至多为一，证明上确界等于一。这个测试改变了定义169.1的无中间干预条件，所以与终端风险的最优性不矛盾。证毕。

第165节的精确局部代价在无持久记忆的合同内仍然成立。这里通过保留一个预测器自己的经典标签改变了可用续接关系，在同一终端风险目标下消除了该代价；没有从真实相位取得额外信息。第162节所引静态随机参数文献承担固定混合与逐步重抽的标准区别，本节的新增结论是这一校准源上的有限参数 minimax 达到性、同时局部与长期最优所需的精确记忆维数，以及相应终端保证在干预历史上的明确边界。

<a id="entry-688"></a>

## 追加锚（本行以下为增补区）

<a id="section-170"></a>

## 170. 终端趋同与干预历史的统一预测障碍

**定义 170.1（允许中间测试的相位盲预测）。** 沿用定义161.1的源族，取 $1/\sqrt3<r<1$，每个实际 $\phi\in[-\alpha(r),\alpha(r)]$ 在全部使用中保持固定，环境记录单元逐步新鲜。记 $\mathbf M_{r,\phi}^{(N)}$ 为这一源在 $N$ 个系统端口上的过程。现在允许测试者在这些端口之间制备、测量和重置系统，保存经典结果；测试者不访问源的环境或预测器的私有记忆。

过程距离直接采用[上下文几何卷定义11.16](../RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md)的共同 tester 接口：令 $\mathfrak T_N$ 包含所有上述合法顺序测试，$p_T^{\mathbf P}$ 是过程 $\mathbf P$ 在测试 $T$ 下的有限输出律，定义
$$
d_{\mathfrak T_N}(\mathbf P,\mathbf Q)
=\sup_{T\in\mathfrak T_N}
\operatorname{TV}(p_T^{\mathbf P},p_T^{\mathbf Q}).
\tag{170.1}
$$
其中 $\operatorname{TV}(p,q)=\sup_A|p(A)-q(A)|$。每个预测过程 $\mathbf P$ 可有任意有限私有记忆、相关输出和随端口变化的内部通道，并可依赖已知的 $r,N$；但其选择、初始记忆和测试前的资料均与实际 $\phi$ 无关，也不接收另一个真实源的实验结果。所有输入输出端口均与源匹配。定义
$$
\mathcal C_N(r)=\inf_{\mathbf P}
\sup_{|\phi|\le\alpha(r)}
d_{\mathfrak T_N}(\mathbf M_{r,\phi}^{(N)},\mathbf P).
\tag{170.2}
$$
有限视界中，任意确定性量子梳也可纳入此预测域。tester 的标准概率解释见 Chiribella、D'Ariano、Perinotti，*Theoretical framework for quantum networks*，[arXiv:0904.4483](https://arxiv.org/pdf/0904.4483)，定义11、定理11；本节只用下面显式实现的制备与测量测试，不从抽象表示额外取得控制权限。

**定理 170.2（任意预测记忆都满足的有限视界下界）。** 取整数 $1\le k\le N$，记
$$
m=\left\lfloor\frac Nk\right\rfloor,\qquad
\beta=\min\{k\alpha(r),\pi/4\},\qquad
q_k=r^k\sin\beta>0.
\tag{170.3}
$$
则对每个整数 $M\ge2$，
$$
\boxed{
\mathcal C_N(r)\ge
\max\left\{0,1-\frac1M-
\frac{(M-1)^2}{m q_k^2}\right\}.
}
\tag{170.4}
$$
该下界不限制预测器的私有记忆维数，也不要求它的输出独立。特别地，对每个固定的上述 $r$，
$$
\lim_{N\to\infty}\mathcal C_N(r)=1.
\tag{170.5}
$$

证明。 令 $Y=-iE_{02}+iE_{20}$、$P_1=E_{11}$。采用以下固定测试：每段开始制备 $|+_{02}\rangle=(|0\rangle+|2\rangle)/\sqrt2$，连续使用过程 $k$ 次，段内只作恒等连接；段末测量二值可观测量 $Y+P_1$，保存结果，再重新制备下一段的输入。$Y+P_1$ 的谱为 $\{-1,1\}$，所以即使预测器输出泄漏到第三个标签，测量仍完整合法。制备与重置是 CPTP 通道，测量的两个谱投影给归一化仪器；有限次复合及经典记录保存因此构成实际可实现的共同 tester。共作 $m$ 段，剩余不足 $k$ 次使用可忽略其输出，不修改已保存的记录。

对实际源，输入和输出始终支撑于 $02$ 子空间，每段的相干系数为 $r^ke^{ik\phi}$。段末结果 $Y_j\in\{-1,1\}$ 的均值为
$$
\mu(\phi)=-r^k\sin(k\phi).
\tag{170.6}
$$
在固定实际 $\phi$ 后，环境逐步新鲜，段首系统又被重新制备，所以这 $m$ 个结果独立同分布。相位没有在段间重新抽取。将合法相位限制到 $[-\beta/k,\beta/k]$，均值连续且单调地扫过 $[-q_k,q_k]$。

在该均值区间取 $M$ 个等距点
$$
\mu_j=-q_k+\frac{2q_k(j-1)}{M-1},\qquad
\phi_j=-\frac1k\arcsin\frac{\mu_j}{r^k},\qquad
1\le j\le M.
\tag{170.7}
$$
因为 $\beta\le\pi/4$，有 $|\phi_j|\le\beta/k\le\alpha(r)$，故它们都是同一源合同中的实际允许相位。记 $\overline Y_m=m^{-1}\sum_{i=1}^mY_i$，并定义历史事件
$$
A_j=\left\{
|\overline Y_m-\mu_j|<\frac{q_k}{M-1}
\right\}.
\tag{170.8}
$$
这些开区间只可能在未包含的端点相接，故事件两两不交。

任取一个预测过程 $\mathbf P$。上述共同测试固定后，它产生某个历史律 $Q$；该律可以相关，但因测试及预测器均不知道实际相位，它对所有 $\phi_j$ 是同一个 $Q$。于是 $\sum_jQ(A_j)\le1$，至少存在一个 $j$ 使 $Q(A_j)\le1/M$。在实际源 $\phi_j$ 下，样本均值的方差至多为 $1/m$，故由 Chebyshev 不等式，
$$
\Pr_{\phi_j}(A_j)
\ge1-\frac{(M-1)^2}{m q_k^2}.
\tag{170.9}
$$
将该事件的概率差代入总变差距离定义，再对实际相位取上确界，得到（170.4）。$j$ 的选择可依赖候选预测律，但测试本身并未依赖实际相位；这恰是先选预测器、再取最坏实际来源的量词。最后对全部预测器取下确界不会改变这个统一下界。

对固定 $r$ 取 $k=1$，则 $q_1>0$ 不依赖 $N$。再取例如 $M_N=\max\{2,\lfloor(Nq_1^2)^{1/3}\rfloor\}$，（170.4）的两个损失项都趋于零。过程距离至多为一，因此得到（170.5）。这里的样本集中与互斥事件计数是标准概率工具；它们作用于同一个实际相位产生的共同历史，而非分别选择不可联合实现的最优读数。证毕。

**定理 170.3（弱记录下同一使用预算的相反结论）。** 令 $r\uparrow1$、$\varepsilon=1-r$，并取任意整数视界函数 $N(r)$，满足
$$
\varepsilon N(r)\longrightarrow\infty.
\tag{170.10}
$$
则即使预测过程及其记忆维数都随 $r,N(r)$ 改变，仍有
$$
\boxed{\mathcal C_{N(r)}(r)\longrightarrow1.}
\tag{170.11}
$$
另一方面，对定理169.2的同一个比特预测器，在相同使用次数下却有
$$
\boxed{
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^{N(r)},
\mathcal P_{r,N(r)}^{\rm bit})\longrightarrow0.
}
\tag{170.12}
$$
因此这个比特预测器的终端误差趋零，而其包含允许干预与历史的最坏过程距离趋于一。

证明。 取固定
$$
t_0=\frac\pi{6\sqrt3},\qquad
k_r=\left\lfloor\frac{t_0}{\varepsilon}\right\rfloor.
\tag{170.13}
$$
充分接近一时 $k_r\ge1$，且由定理161.6，
$$
\varepsilon k_r\to t_0,\qquad
k_r\alpha(r)\to\pi/6<\pi/4,\qquad
q_{k_r}=r^{k_r}\sin(k_r\alpha(r))
\longrightarrow\frac12e^{-t_0}>0.
\tag{170.14}
$$
式（170.10）还给出 $k_r\le N(r)$ 及
$$
m_r=\left\lfloor\frac{N(r)}{k_r}\right\rfloor\longrightarrow\infty.
\tag{170.15}
$$
在（170.4）中取 $k=k_r$ 和 $M_r=\max\{2,\lfloor(m_rq_{k_r}^2)^{1/3}\rfloor\}$，即可使下界趋于一。它对所有预测过程统一成立，因此不需要交换预测器下确界和参数极限，直接得到（170.11）。

对终端读数，式（169.7）的 $m(x)\le2$ 给出
$$
\sup_{|\phi|\le\alpha(r)}
d_{\rm ref}(\mathcal M_{r,\phi}^{N(r)},
\mathcal P_{r,N(r)}^{\rm bit})
\le r^{N(r)}\le e^{-\varepsilon N(r)}\longrightarrow0.
\tag{170.16}
$$
该界包含任意有限惰性参考系统。比特预测器的过程也是（170.2）中允许的候选之一，所以其干预距离至少为 $\mathcal C_{N(r)}(r)$、至多为一，得到最后的陈述。终端接线与保存分段测量历史的接线使用相同次数的源；新增资源是声明允许的制备、测量和记录，不是源相位信息。证毕。

式（170.14）中，一段内部的相干合成先把未知相位转成非消失的可测均值，再由多段历史提供多个相互排斥的来源证据。若每次使用后立刻重置，实际单次均值幅度仅为 $r\sin\alpha(r)\sim\sqrt3\varepsilon$，同一集中估计需要 $N\varepsilon^2\to\infty$；分段构造把充分条件改为（170.10），但不声称已求出所有测试的最优有限样本速率。结论依赖本节的允许控制和最坏完整历史损失，不否定从实际数据学习相位的任务，也不把经典样本的可识别性当成量子性的普遍判据。

<a id="entry-690"></a>

## 追加锚（本行以下为增补区）

<a id="section-171"></a>

## 171. 终端最优预测的遗忘尺度与有限时刻擦除

**定义 171.1（可遗忘记忆的终端合同）。** 沿用定义169.1的时间齐次联合 CPTP 通道合同、一次初始化及终端距离 $d_{\rm ref}=\frac12\|\cdot\|_\diamond$。真实相位 $\phi$ 在一条运行中固定，真实环境逐步新鲜；预测器的初始私有记忆与真实相位无关。记
$$
\varepsilon=1-r,\qquad \alpha=\alpha(r),\qquad
H(r)=\sup_{N\ge1}\mathcal R_N(r),\qquad
t_* =\frac\pi{3\sqrt3},\qquad L=\frac{\sqrt3}{4}e^{-t_*}.
\tag{171.1}
$$
以下取 $1/\sqrt3<r<1$。记忆的遗忘只指丢弃系统输出之后，最终私有记忆对其初始化的依赖消失；它不要求已经输出的系统或已保存的实验记录丢失初始化信息。对本节的自主记忆更新，还将证明包含任意有限惰性参考 $R$ 的具体迹范数界。有关标准有限记忆通道与遗忘性的定义，见 Kretschmann、Werner，*Quantum Channels with Memory*，[arXiv:quant-ph/0502106v2](https://arxiv.org/pdf/quant-ph/0502106v2)，§III C 的全局经典开关，以及§V定义3、命题9。该文§VI B式(79)还给出有限步后精确消除初始记忆依赖的严格遗忘定义。该文丢弃消息输出后的记忆遗忘与本节所用方向一致；下面另行计算同一系统反复使用时的约化通道，不把不同接线方式等同。

取 $0<p\le1/2$。在记忆基 $s=\pm1$ 上，令 $T_p(s,s)=1-p$、$T_p(s,-s)=p$，并定义
$$
\Lambda_{r,p}^{\rm mix}(X)=
\sum_{s,u=\pm1}T_p(s,u)
\mathcal M_{r,s\alpha}(X_{ss})\otimes|u\rangle\langle u|,
\qquad X_{ss}=(I\otimes\langle s|)X(I\otimes|s\rangle).
\tag{171.2}
$$
初始记忆为 $\sigma=I_2/2$。也就是每一步先使用当前标签的端点通道，再以概率 $p$ 翻转标签；标签不是每步重新读取的真实源参数。以 $\mathcal P_{r,N}^{\rm mix}$ 表示其终端系统通道，$W_r^{\rm mix}$ 表示定义169.1的全视界风险。$p$ 随 $r$ 变化时均指这同一个构造族。

**定理 171.2（自主混合比特的全视界风险与遗忘界）。** 式（171.2）给出合法 CPTP 通道，且对每个 $p$ 精确满足单步最优条件（169.3）。设 $S_1$ 为均匀符号，$S_{j+1}$ 以概率 $p$ 从 $S_j$ 翻转，记
$$
z_{N,p}=\mathbb E\exp\!\left(i\alpha\sum_{j=1}^N S_j\right)
=\mathbb E\cos\!\left(\alpha\sum_{j=1}^N S_j\right).
\tag{171.3}
$$
则 $\mathcal P_{r,N}^{\rm mix}$ 的 $01,12$ 系数为 $r^N$，$02$ 系数为 $r^Nz_{N,p}$，并且对第169节的持续比特有
$$
d_{\rm ref}(\mathcal P_{r,N}^{\rm mix},\mathcal P_{r,N}^{\rm bit})
\le r^N\bigl[1-(1-p)^{N-1}\bigr]
\le r^N(N-1)p.
\tag{171.4}
$$
因而对全部充分接近一的 $r$、全部 $0<p\le1/2$，
$$
\boxed{0<W_r^{\rm mix}-H(r)\le\frac p{1-r}.}
\tag{171.5}
$$
同时，对任意初始联合密度 $\tau_{SKR}$，$N\ge1$ 次无中间干预的运行后，有
$$
\frac12\left\|\tau_{KR}^{(N)}-\sigma\otimes\tau_R\right\|_1
\le\frac{(1-2p)^N}{2}.
\tag{171.6}
$$
特别地，每个固定 $r,p>0$ 都有指数记忆遗忘；该结论没有声称遗忘速率对 $r\uparrow1$ 一致。

证明。 选取端点通道的 Kraus 算符 $K_{s,a}$，则（171.2）的 Kraus 算符为 $\sqrt{T_p(s,u)}K_{s,a}\otimes|u\rangle\langle s|$。其伴随乘积之和为恒等算符，故在任意含记忆相干的联合输入上都是 CPTP。均匀符号为 $T_p$ 的平稳分布，整体符号反转保持路径概率不变，故（171.3）为实数。条件于符号路径，Schur 系数逐步相乘，得到所述终端系数。单步时 $z_{1,p}=\cos\alpha$，所以终端通道正是定理162.2中的 $\mathcal F_*$。

将混合链和持续比特取为相同初始符号；在前 $N-1$ 次更新均未翻转的事件上，两条符号路径一致。其补事件概率为 $1-(1-p)^{N-1}$，而任意两个单位复数相距至多二，因此
$$
|z_{N,p}-\cos(N\alpha)|\le2\bigl[1-(1-p)^{N-1}\bigr].
\tag{171.7}
$$
两终端通道只有 $02,20$ 系数不同，式（161.11）将其距离精确写成 $r^N|z_{N,p}-\cos(N\alpha)|/2$；该公式已经包含任意惰性参考。由并集界得到（171.4）。又有
$$
(N-1)r^N\le\sum_{j=1}^{N-1}r^j\le\frac1{1-r},
\tag{171.8}
$$
故三角不等式及定理169.3给出 $W_r^{\rm mix}\le H(r)+p/(1-r)$。每个终端预测仍为 CPTP，所以逐视界半径下界给出 $W_r^{\rm mix}\ge H(r)$。

为得到严格号，定理169.3的证明表明，充分接近一时 $H(r)$ 在某个早视界 $N_*\alpha<\pi/2$ 取得；因 $\mathcal R_1(r)\to0$ 而 $H(r)\to L>0$，还可保证 $N_*\ge2$。对每条符号路径，$|\sum S_j|\le N_*$，故余弦至少为 $\cos(N_*\alpha)$。恰有一次内部翻转的路径具有正概率，且严格满足 $|\sum S_j|<N_*$，所以
$$
z_{N_*,p}>\cos(N_*\alpha).
\tag{171.9}
$$
在实际允许端点 $\phi=\alpha$ 上，精确距离为
$$
\frac{r^{N_*}}2
\sqrt{\sin^2(N_*\alpha)+
\bigl[z_{N_*,p}-\cos(N_*\alpha)\bigr]^2}
>\frac{r^{N_*}}2\sin(N_*\alpha)=H(r).
\tag{171.10}
$$
这证明（171.5），且所需邻域不依赖于正数 $p$ 的大小。

最后设 $A_s=\operatorname{tr}_S\tau_{ss}$ 为参考上的次归一化正算符，则 $A_++A_-=\tau_R$。每个条件系统通道保迹，故丢弃系统后，每一步仅以 $T_p$ 更新这两个参考算符。记 $\rho=1-2p$，直接对二态转移矩阵求幂，得到
$$
\tau_{KR}^{(N)}=
\sigma\otimes\tau_R+
\frac{\rho^N}{2}
(|+\rangle\langle+|-|-\rangle\langle-|)
\otimes(A_+-A_-).
\tag{171.11}
$$
因为 $\|A_+-A_-\|_1\le\operatorname{tr}(A_++A_-)=1$，即得（171.6）。同一计算在逐次送入不同系统、最终丢弃全部系统输出的接线中仍然成立，对联合输入及惰性参考统一，因而也满足所引标准记忆遗忘条件。已经发出的系统仍可携带初始符号的信息；（171.11）不对保留这些输出的联合历史作遗忘断言。证毕。

**定理 171.3（此混合比特族内的锐遗忘尺度）。** 对任意参数函数 $p_r\in(0,1/2]$，有
$$
\boxed{
W_r^{\rm mix}\longrightarrow L
\quad\Longleftrightarrow\quad
\frac{p_r}{1-r}\longrightarrow0
\qquad(r\uparrow1).
}
\tag{171.12}
$$
这是定义171.1的对称 Markov 比特族内的充要条件，不量化所有有限记忆预测器。

证明。 充分性由（171.5）与 $H(r)\to L$ 直接得到。证明必要性，取
$$
N_r=\left\lfloor\frac{t_*}{\varepsilon}\right\rfloor,
\qquad \theta_r=N_r\alpha\longrightarrow\pi/3.
\tag{171.13}
$$
最终 $N_r\ge2$ 且 $\theta_r<\pi/2$。以下略去下标 $r$。每条符号路径均满足 $\cos(\alpha\sum S_j)\ge\cos\theta$。若恰有一次翻转发生在第 $j$ 次与第 $j+1$ 次通道之间，则该余弦为 $\cos((N-2j)\alpha)$，该事件概率为 $p(1-p)^{N-2}$。这些事件互斥，所以
$$
z_{N,p}-\cos\theta\ge
p(1-p)^{N-2}\sum_{j=1}^{N-1}
\bigl[\cos((N-2j)\alpha)-\cos\theta\bigr].
\tag{171.14}
$$

先考虑某条子序列满足 $p/\varepsilon\to\lambda\in(0,\infty)$。由 $\alpha/\varepsilon\to\sqrt3$、$\varepsilon N\to t_*$，括号和的 Riemann 极限及翻转概率极限分别为
$$
\varepsilon\sum_{j=1}^{N-1}
\bigl[\cos((N-2j)\alpha)-\cos\theta\bigr]
\longrightarrow
\int_0^{t_*}
\bigl[\cos(\sqrt3(t_*-2u))-\cos(\sqrt3t_*)\bigr]\,du
=\frac{1-t_*}{2},
\tag{171.15}
$$
$$
(1-p)^{N-2}\longrightarrow e^{-\lambda t_*}.
\tag{171.16}
$$
式（171.15）中，余弦积分为 $\sin(\sqrt3t_*)/\sqrt3=1/2$，常数项积分为 $t_*/2$。又 $t_*<1$，所以（171.14）的右侧趋于
$$
a_\lambda:=\lambda e^{-\lambda t_*}\frac{1-t_*}{2}>0.
\tag{171.17}
$$
在同一视界取实际端点，使用（171.10）对应的距离公式，得到
$$
\liminf W_r^{\rm mix}\ge
\frac{e^{-t_*}}2\sqrt{\frac34+a_\lambda^2}>L
\tag{171.18}
$$
沿该子序列成立。

再考虑 $p/\varepsilon\to\infty$ 的子序列。平稳符号链有 $\mathbb E S_j=0$ 及 $\mathbb E S_iS_j=(1-2p)^{|i-j|}$。由于 $0\le\rho=1-2p<1$，
$$
\mathbb E\left(\sum_{j=1}^N S_j\right)^2
=N+2\sum_{h=1}^{N-1}(N-h)\rho^h
\le N\frac{1+\rho}{1-\rho}
=N\frac{1-p}{p}\le\frac Np.
\tag{171.19}
$$
利用 $0\le1-\cos x\le x^2/2$，有
$$
0\le1-z_{N,p}\le\frac{\alpha^2N}{2p}
\longrightarrow0,
\tag{171.20}
$$
因为 $\alpha^2N=O(\varepsilon)$。所以 $z_{N,p}\to1$，实际端点距离趋于
$$
\frac{e^{-t_*}}2|e^{i\pi/3}-1|
=\frac{e^{-t_*}}2>L.
\tag{171.21}
$$

若 $p_r/\varepsilon$ 不趋于零，可选一条子序列使该比值始终至少为某个 $\delta>0$，再选扩展实数意义下收敛的子序列，其极限属于 $[\delta,\infty]$。有限正极限由（171.18）排除，无穷极限由（171.21）排除。因此 $W_r^{\rm mix}\to L$ 必须有 $p_r/\varepsilon\to0$。本证明只用互斥的单次翻转事件与二态链协方差，不需要把离散路径先替换成连续随机过程。证毕。

**定理 171.4（有限时刻完全擦除仍可达到精确终端最优）。** 对所有充分接近一的 $r$，令
$$
J(r)=\left\lceil\frac{\log H(r)}{\log r}\right\rceil.
\tag{171.22}
$$
存在维数 $2J(r)+1$ 的经典私有记忆及同一个时间齐次联合 CPTP 通道，使其满足精确单步最优条件（169.3），全视界风险精确等于 $H(r)$，而从任意初始系统—记忆状态出发，私有记忆至多在 $J(r)$ 步后成为同一个纯状态，并与其余系统完全解耦。此构造满足
$$
\varepsilon J(r)\longrightarrow\log\frac1L,
\qquad
\varepsilon\dim K_r\longrightarrow2\log\frac1L.
\tag{171.23}
$$
维数为所给实现的上界，不声称最小维数或最短擦除期限。

证明。 $0<H(r)<1$ 且 $0<r<1$，故 $J\ge1$、$r^J\le H(r)$。取经典记忆基
$$
\{(s,j):s=\pm1,\ 0\le j\le J-1\}\cup\{*\}.
\tag{171.24}
$$
初始记忆均匀分布在 $(+,0)$ 和 $(-,0)$。在 $(s,j)$ 上先应用 $\mathcal M_{r,s\alpha}$，然后当 $j<J-1$ 时将记忆变成 $(s,j+1)$，当 $j=J-1$ 时变成 $*$；在 $*$ 上应用 $\mathcal M_{r,0}$ 并保持 $*$。先在此记忆基上完全退相干，即把定义扩展到任意输入。若 $f(v)$ 表示上述确定性记忆更新、$K_{v,a}$ 为对应系统通道的 Kraus 算符，则联合 Kraus 算符为 $K_{v,a}\otimes|f(v)\rangle\langle v|$，其伴随乘积之和为恒等算符。这既证明 CPTP，也显示时钟已经计入私有记忆；没有外置的随步数改变通道的控制。

对指定初始化，终端 Schur 系数 $01,12$ 始终为 $r^N$，而 $02$ 系数为
$$
c_N=r^N\cos\bigl(\min\{N,J\}\alpha\bigr).
\tag{171.25}
$$
因此当 $N<J$ 时，它与第169节的持续比特完全相同；在 $N=1$，包括 $J=1$ 的情形，都有 $c_1=r\cos\alpha$，故精确单步最优。若 $N\ge J$，由（161.11）及两个单位圆盘元素相距至多二，
$$
\sup_{|\phi|\le\alpha}
d_{\rm ref}(\mathcal M_{r,\phi}^{N},\mathcal P_{r,N}^{\rm erase})
=\frac{r^N}{2}
\sup_{|\phi|\le\alpha}|e^{iN\phi}-\cos(J\alpha)|
\le r^N\le r^J\le H(r).
\tag{171.26}
$$
充分接近一时，早于 $J$ 的所有风险由定理169.3也不超过 $H(r)$；故全视界风险至多为 $H(r)$。逐视界 CPTP 半径下界使其至少为 $H(r)$，于是精确达到相同最优值。

每一个初始记忆基态至多在 $J$ 步后进入吸收态 $*$，最初的记忆相干又已被去除。因此对任意初始联合密度、任意有限惰性参考，最终态均具有
$$
\tau_{SKR}^{(J)}=\omega_{SR}\otimes|*\rangle\langle*|_K
\tag{171.27}
$$
的形式，其中按张量因子次序作自然识别。特别地，丢弃系统后得到 $|*\rangle\langle*|\otimes\tau_R$。这里 $\omega_{SR}$ 仍可依赖初始记忆；擦除的是私有寄存器，未把先前作用于系统的影响倒回，也未擦除已有输出历史。随后每一步都是固定系统通道 $\mathcal M_{r,0}$。

最后由 $\varepsilon/(-\log r)\to1$、$H(r)\to L$，并利用取整误差小于一，得到（171.23）。证毕。

式（171.12）的尺度要求与（171.23）并不矛盾：前者限制只有一个自主对称翻转比特的模型，后者把擦除时刻的计数也存入更大的私有记忆。在第二种实现中，信息先保留到指定阶段，之后完全删除；删除后的所有终端相干已经受到 $r^N\le H(r)$ 的统一抑制。因而“最终会遗忘”“在相关视界内怎样保留”和“用多少内部状态安排删除”是不同的数学条件。标准的全局开关、二态混合与记忆遗忘本身由所引文献承担；本节给出的是当前校准源和终端风险合同下的全视界误差界、混合比特的充要尺度，以及有限期限擦除的精确 minimax 实现。第170节允许中间测试并保留历史时的障碍仍适用，私有记忆擦除不使那个过程距离变成终端距离。

<a id="entry-692"></a>

## 追加锚（本行以下为增补区）

<a id="section-172"></a>

## 172. 精确终端最优与可遗忘经典相位记忆的最小状态数

**定义 172.1（自主经典相位选择器）。** 沿用第171节的源族、终端风险、$\varepsilon=1-r$、$\alpha=\alpha(r)$、$H(r)$、$L$ 和 $t_*$。取非空有限状态集 $V$、相位标记 $\theta_v\in[-\alpha,\alpha]$、时间齐次随机矩阵 $T$ 及初始概率分布 $\pi$。每步在当前状态 $v$ 上应用系统通道 $\mathcal M_{r,\theta_v}$，随后按 $T(v,u)$ 更新私有状态。联合通道明确为
$$
\Lambda(X)=\sum_{v,u\in V}T(v,u)
\mathcal M_{r,\theta_v}(X_{vv})\otimes|u\rangle\langle u|,
\qquad
\sigma=\sum_v\pi(v)|v\rangle\langle v|.
\tag{172.1}
$$
其中 $X_{vv}$ 为记忆基上的系统对角块，故记忆的任意初始相干也在定义域内。$V,T,\pi,\theta$ 可依赖已知的 $r$，不依赖实际未知相位、使用视界或系统输入；记忆更新不读取系统输出，不另给外置时钟。条件通道的 Kraus 算符与 $\sqrt{T(v,u)}|u\rangle\langle v|$ 的张量积直接证明（172.1）为 CPTP。

称此选择器可遗忘，当
$$
\delta_n(T):=\max_{v,w\in V}
\operatorname{TV}\bigl(T^n(v,\cdot),T^n(w,\cdot)\bigr)
\longrightarrow0.
\tag{172.2}
$$
这要求私有记忆对任意初始化的依赖消失，不仅针对指定分布 $\pi$。这是有限经典链的标准遗忘条件，方向与第171节所引记忆通道定义一致；它不要求已经发出的系统遗忘初始化。

令 $d_{\rm fg}(r)$ 为全部满足（172.2）且全视界终端风险精确等于 $H(r)$ 的选择器中，$|V|$ 的最小值；若无这样的选择器，定义其值为 $+\infty$。所有演化状态都计入 $V$，包括计时与吸收状态。以下只研究这个明确限定的经典选择器域，不将其最小值等同于任意量子记忆的最小 Hilbert 空间维数。

记
$$
B_N(r)=\frac{r^N}{2}m(N\alpha),\qquad
n_*(r)=\max\operatorname*{arg\,max}_{N\ge1}B_N(r),
\tag{172.3}
$$
其中 $m$ 为式（169.6）的函数。由 $B_1>0$、$B_N\to0$，最大点集合非空且有限。定理169.3的严格晚视界间隙表明，充分接近一时，$\sup_NB_N=H$，所有最大点都满足 $N\alpha<\pi/2$，且此集合也等于逐视界半径 $\mathcal R_N$ 的最大点集合。定理161.6又给出
$$
\varepsilon n_*(r)\longrightarrow t_*,
\qquad n_*(r)\ge2
\quad\text{最终成立}.
\tag{172.4}
$$
下面统一限于满足这些性质的 $r$ 邻域。

**定理 172.2（最优终端读数强制端点路径保持）。** 设定义172.1的选择器具有全视界风险 $H(r)$，令 $n=n_*(r)$。则由初始分布 $\pi$ 产生的每条正概率的长度 $n$ 状态路径，在这 $n$ 次系统使用中，相位标记必定全为 $+\alpha$ 或全为 $-\alpha$；两类路径的总概率各为 $1/2$。特别地，此精确全视界最优条件已经强制单步终端通道为 $\mathcal F_*$。

证明。 设 $V_1\sim\pi$，随后按 $T$ 更新。条件于整条路径，（172.1）的 Schur 系数相乘，所以终端系数 $01,12$ 为 $r^n$，$02$ 为 $r^nz_n$，其中
$$
z_n=\mathbb E\exp\!\left(i\sum_{j=1}^n\theta_{V_j}\right).
\tag{172.5}
$$
令 $x=n\alpha\in(0,\pi/2)$。在两个实际允许端点 $\phi=\pm\alpha$ 上，式（161.11）及 $H=r^n\sin x/2$ 给出
$$
|z_n-e^{ix}|\le\sin x,\qquad
|z_n-e^{-ix}|\le\sin x.
\tag{172.6}
$$
两个圆盘的圆心距离恰为其半径和 $2\sin x$，故交集只有圆心连线的中点；等价地，三角不等式必须处处取等。因此
$$
z_n=\cos x.
\tag{172.7}
$$

每条路径的累计相位 $a=\sum_j\theta_{V_j}$ 属于 $[-x,x]$，在此区间有 $\cos a\ge\cos x$，且等号只在 $a=\pm x$ 取得。式（172.7）的实部说明这个非负差的期望为零；路径集合有限，所以每条正概率路径都满足 $a=\pm n\alpha$。每一项又属于 $[-\alpha,\alpha]$，故累计取端点只可能由所有项取同一个端点得到。令全正路径的概率为 $q$，则（172.7）的虚部为 $(2q-1)\sin x=0$，得到 $q=1/2$。于是第一步也以相同概率应用两个端点通道，正是 $\mathcal F_*$。证毕。

**定理 172.3（可遗忘选择器的精确最小状态数）。** 对全部充分接近一的 $r$，
$$
\boxed{d_{\rm fg}(r)=n_*(r)+1.}
\tag{172.8}
$$
该最小值可由一个吸收型经典选择器达到，它满足单步最优并在每个固定 $r$ 下遗忘初始记忆。因此
$$
\boxed{\lim_{r\uparrow1}(1-r)d_{\rm fg}(r)=t_*.}
\tag{172.9}
$$
若以能编码全部私有状态的二进制寄存器位数计成本，则最小所需位数满足
$$
\left\lceil\log_2 d_{\rm fg}(r)\right\rceil
=\log_2\frac1{1-r}+O(1).
\tag{172.10}
$$

证明。 先证下界。令 $C_s=\{v:\theta_v=s\alpha\}$，$s=\pm1$。定理172.2说明，初始支持在两个集合中各有正概率，且从任一初始支持状态出发，前 $n-1$ 次更新都不能以正概率离开其符号对应的 $C_s$，其中 $n=n_*(r)$。

至少一个符号必须存在从其初始支持通往 $V\setminus C_s$ 的正概率路径。否则，分别从正、负初始支持中选一个状态 $v_+,v_-$，对所有整数 $k$ 都有 $T^k(v_+,C_+)=1$、$T^k(v_-,C_-)=1$；由于 $C_+\cap C_-=\varnothing$，两分布的总变差距离恒为一，违反（172.2）。

选这样的符号及其初始支持上的起点，并取离开 $C_s$ 的最短正概率路径
$$
v_0,v_1,\ldots,v_\ell,
\qquad v_0,\ldots,v_{\ell-1}\in C_s,
\quad v_\ell\notin C_s.
\tag{172.11}
$$
路径内部不能重复状态，否则删去两次重复之间的环，就得到更短的正概率离开路径。因此 $\ell\le|C_s|$。另一方面，若 $\ell\le n-1$，第 $\ell+1$ 次系统使用就出现不同相位；将路径任意延长到长度 $n$，仍可选到正概率路径，违反定理172.2。所以 $\ell\ge n$，得到 $|C_s|\ge n$。另一符号的初始支持至少还包含一个不在 $C_s$ 的状态，故 $|V|\ge n+1$。这里使用的有限有向图最短路径计数是标准工具；约束最短离开时间的前提来自（172.6）所强制的精确终端几何。

再证可达到性。取 $n$ 个负相位状态 $0,1,\ldots,n-1$，以及一个正相位吸收态 $*$。初始分布在 $0$ 与 $*$ 上各取 $1/2$。负相位状态均应用 $\mathcal M_{r,-\alpha}$；在 $j<n-1$ 时使用后确定性地变成 $j+1$，在 $j=n-1$ 时使用后以概率 $p$ 进入 $*$，以概率 $1-p$ 留在原状态。吸收态始终应用 $\mathcal M_{r,+\alpha}$ 并保持自身。此更新时间齐次，全部 $n+1$ 个状态均计入记忆。

从初始负相位分支出发，前 $n$ 次系统使用必定全部采用负端点；第一次可能的切换只影响第 $n+1$ 次系统使用。所以对 $N\le n$，终端通道精确等于持续比特通道，风险为 $B_N$。令
$$
K=\left\lceil\frac{\log H}{\log r}\right\rceil.
\tag{172.12}
$$
因为 $H=r^n\sin(n\alpha)/2<r^n$，有 $K>n$；而 $r^K\le H$。若 $n<N<K$，将当前选择器与持续比特取相同初始符号，只有负分支在前 $N-1$ 次更新中发生吸收时才会产生差异。至多有 $N-n$ 次相关吸收机会，所以按（171.7）相同的单位圆耦合估计，
$$
d_{\rm ref}(\mathcal P_{r,N}^{(p)},\mathcal P_{r,N}^{\rm bit})
\le r^N(N-n)p.
\tag{172.13}
$$
由 $n$ 是最大的最大点，每个这样的整数 $N$ 都有 $B_N<H$。取
$$
p=\min\left\{\frac12,
\min_{n<N<K}\frac{H-B_N}{2r^N(N-n)}\right\},
\tag{172.14}
$$
其中空集的内层最小值解释为 $+\infty$。这是有限个正数与 $1/2$ 的最小值，故 $0<p\le1/2$。三角不等式给出所有中间视界的严格界
$$
\sup_{|\phi|\le\alpha}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{(p)})
\le B_N+r^N(N-n)p
\le\frac{H+B_N}{2}<H.
\tag{172.15}
$$
对 $N\ge K$，任意路径平均仍满足 $|z_N|\le1$，其余校准系数为 $r^N$，故
$$
\sup_{|\phi|\le\alpha}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{(p)})
\le r^N\le r^K\le H.
\tag{172.16}
$$
在 $N=n$ 则精确达到 $B_n=H$。这证明同一个选择器服务全部视界，风险精确为 $H$；第一步也精确最优。取最大的最大点排除了中间有限视界中尚有相同最优值的情形，故没有把一个零余量错误用于选取正数 $p$。

从任意负相位初态出发，至多 $n-1$ 步后到达末端负相位状态，其后每步都有概率 $p$ 吸收。于是对 $k\ge n$，
$$
\max_{v\in V}\operatorname{TV}(T^k(v,\cdot),\delta_*)
\le(1-p)^{k-n+1}\longrightarrow0.
\tag{172.17}
$$
这蕴含（172.2）。对任意初始联合系统—记忆—惰性参考密度，记忆基上的参考正算符块同样按 $T$ 更新；非吸收块的总迹至多为（172.17）的右侧，故丢弃系统后的记忆—参考密度与 $\delta_*\otimes\tau_R$ 的半迹距离也受这个界控制。这里没有要求在有限步后严格擦除：每个有限 $k$ 仍允许以正概率停留在末端负相位状态。

上下界证明（172.8），式（172.4）随即给出（172.9）。取对数及整数编码的取整误差至多一，得到（172.10）。证毕。

Kretschmann–Werner，*Quantum Channels with Memory*，[arXiv:quant-ph/0502106v2](https://arxiv.org/pdf/quant-ph/0502106v2)，§V定理10已证明可遗忘通道的稠密性，其证明以稀少噪声构造近似。本节的吸收概率选择还保留了全部最大风险视界的精确终端通道，并分别控制剩余有限视界与无限尾部；式（172.8）的等号由这一构造与路径保持下界共同给出。

第169节的两个永久标签具有固定维数二，但违反（172.2）；第171节的混合比特具有固定维数二并可遗忘，却只在所给尺度条件下渐近最优，有限参数处仍有严格超额风险。式（172.8）针对的是同时要求可遗忘与有限参数精确最优的经典选择器。达到它的更新先用内部状态保证一段绝不切换的路径，再利用其他有限视界的严格余量选择正的吸收概率。式（172.17）没有对 $r\uparrow1$ 给出统一遗忘速度；式（172.8）也不解决严格有限期限擦除的最小维数，或一般量子记忆与系统反馈所允许的维数。

<a id="entry-694"></a>

## 追加锚（本行以下为增补区）

<a id="section-173"></a>

## 173. 放宽内部条件通道后的双态精确最优与参数例外集

**定义 173.1（一般可遗忘预测器与唯一最大点参数）。** 沿用定义169.1的时间齐次联合 CPTP 通道 $\Lambda_r$、一次初始化 $\sigma_r$、同一系统的终端通道 $\mathcal P_{r,N}$ 及全视界风险 $W_r^{\rm mem}$。真实源仍为定义161.1的 $\mathcal M_{r,\phi}$，实际相位在全部使用中固定，环境逐步新鲜。预测器可以依赖已知的 $r$，不依赖实际相位、所比较的运行视界或输入态。

对同一个局部处理器，另作标准的逐次新鲜输入接线：令 $\Gamma_{r,N}$ 将初始记忆和 $N$ 个系统输入映到最终记忆及 $N$ 个系统输出，令 $\Phi_{r,N}$ 为丢弃这些输出后的记忆通道。要求存在从系统输入串到最终记忆的 CPTP 通道 $E_{r,N}$，使
$$
\left\|\Phi_{r,N}-E_{r,N}\circ\operatorname{Tr}_{K_r}\right\|_\diamond
\longrightarrow0\qquad(N\to\infty).
\tag{173.1}
$$
这是 Kretschmann–Werner 的标准遗忘条件的 Schrödinger 形式，见第171节所引原文定义3及命题9；范数包含任意惰性参考。它与计算 $\mathcal P_{r,N}$ 的同一系统反复接线分别定义，不要求已经输出的历史被擦除。

记 $D_{\rm fg}(r)$ 为同时满足（173.1）、精确单步最优条件（169.3）及 $W_r^{\rm mem}=H(r)$ 的全部有限量子记忆实现中，$\dim K_r$ 的最小值。预测器的内部条件通道不再要求逐个属于原校准源族。选择充分接近一的区间 $I=(r_0,1)$，使定理169.3—169.4及式（172.4）的全部性质成立，并令
$$
U=\{r\in I:B_N(r)\text{ 在正整数视界上有唯一最大点}\}.
\tag{173.2}
$$
其中 $B_N$ 是持续端点比特风险。对 $r\in U$，记唯一最大点为 $n=n(r)$；因此 $n\ge2$、$n\alpha(r)<\pi/2$ 且 $B_n(r)=H(r)$。

**定理 173.2（唯一最大点参数上的精确双态实现）。** 集合 $U$ 在 $I$ 中开且稠密，其补集至多可数。对每个 $r\in U$，一个自主、对称、可遗忘的经典比特即可实现定义173.1的全部要求，因而
$$
\boxed{D_{\rm fg}(r)=2\quad(r\in U),\qquad
\liminf_{r\uparrow1}D_{\rm fg}(r)=2.}
\tag{173.3}
$$
这里的双态构造使用合法的条件 Schur 通道，但这些通道偏离定义172.1规定的校准源族。结论没有给出 $I\setminus U$ 上的双态实现，也不把经典记忆改称相干量子记忆。

证明。 先固定 $r\in U$，略去参数 $r$ 的下标，记
$$
\alpha=\alpha(r),\qquad c_0=r\cos\alpha,
\qquad q(\theta)=\frac{c_0}{\cos\theta},\qquad
a(\theta)=\sqrt{\frac{1-q(\theta)^2}{2(1-c_0)}}.
\tag{173.4}
$$
当 $\theta=\alpha$ 时有 $q=a=r$；后一等式来自端点相关矩阵的行列式为零。对 $\theta>\alpha$ 充分接近 $\alpha$，有 $r<q<1$、$0<a<r$。定义两个条件相关矩阵
$$
C_s(\theta)=
\begin{pmatrix}
1&a&q e^{is\theta}\\
a&1&a\\
q e^{-is\theta}&a&1
\end{pmatrix},\qquad s=\pm1.
\tag{173.5}
$$
其一阶及二阶主子式非负，而
$$
\det C_s=1-2a^2-q^2+2a^2q\cos\theta=0.
\tag{173.6}
$$
所以两矩阵半正定且对角元为一，对应合法 CPTP Schur 通道 $\mathcal Q_{s,\theta}$。在 $\theta=\alpha$ 时，它们正是原源的两个端点通道。

令私有符号以均匀分布初始化。每步先应用 $\mathcal Q_{s,\theta}$，再以概率 $p$ 翻转符号；在任意联合输入上先去除记忆基间的相干，正如式（171.2）的 Kraus 实现。这样得到同一个时间齐次联合 CPTP 通道，记忆维数为二。令
$$
Z_{N,p}(\theta)=
\mathbb E\cos\!\left(\theta\sum_{j=1}^N S_j\right),
\tag{173.7}
$$
其中 $S_j$ 是平稳对称翻转链。由符号反转对称性，终端系数为
$$
b_{01}=b_{12}=a(\theta)^N,
\qquad b_{02}=q(\theta)^N Z_{N,p}(\theta)\in\mathbb R.
\tag{173.8}
$$

现在只用已知 $r$ 的唯一最大点 $n$ 来设计这一个固定通道。定义
$$
F(p,\theta)=q(\theta)^n Z_{n,p}(\theta)
-r^n\cos(n\alpha).
\tag{173.9}
$$
有限路径和使 $Z_{n,p}$ 在 $p=0$ 附近具有实解析延拓；只在 $p\ge0$ 时将其解释为概率期望。由于 $Z_{n,0}(\theta)=\cos(n\theta)$，有 $F(0,\alpha)=0$，且
$$
\partial_\theta F(0,\alpha)=
nr^n\bigl[\tan\alpha\cos(n\alpha)-\sin(n\alpha)\bigr]
=-\frac{nr^n\sin((n-1)\alpha)}{\cos\alpha}<0.
\tag{173.10}
$$
另一方面，零次与一次翻转路径对 $p$ 的一阶贡献给出
$$
\partial_p F(0,\alpha)
=r^n\sum_{j=1}^{n-1}
\bigl[\cos((n-2j)\alpha)-\cos(n\alpha)\bigr]>0.
\tag{173.11}
$$
每个括号都严格为正，因为 $n\alpha<\pi/2$ 且 $|n-2j|<n$。由通常的实解析隐函数定理，存在 $\theta(p)$，满足
$$
\theta(0)=\alpha,\qquad
F(p,\theta(p))=0,\qquad
\theta'(0)=-\frac{\partial_pF(0,\alpha)}{\partial_\theta F(0,\alpha)}>0.
\tag{173.12}
$$
因此所有充分小的正 $p$ 都落在上述合法条件通道范围，并且同时精确保留
$$
q\cos\theta=r\cos\alpha,
\qquad q^n Z_{n,p}(\theta)=r^n\cos(n\alpha).
\tag{173.13}
$$

还须控制完整三维系统及任意参考，不能只比较 $02$ 输入。定理168.2的证明已经建立以下通用估计：若 Hermitian Schur 差的乘子矩阵为
$$
B=\begin{pmatrix}0&d&w\\d&0&d\\\overline w&d&0\end{pmatrix},
\qquad 0\le2d\le|w|,
\tag{173.14}
$$
则全参考半迹距离精确等于 $|w|/2$。该证明的正半定矩阵 $Y\pm B$ 只用这里所列条件，故直接适用于当前通道差。

在 $N=1,n$ 这两个固定视界，由（173.13）可取
$$
d=r^N-a^N,\qquad
w=r^N\bigl(e^{iN\phi}-\cos(N\alpha)\bigr).
\tag{173.15}
$$
这里 $d\to0$ 当 $p\downarrow0$，而对全部允许的实际相位均有
$$
|w|\ge r^N\bigl(1-\cos(N\alpha)\bigr)>0.
\tag{173.16}
$$
故进一步缩小正 $p$，即可对这两个视界同时保证（173.14）。其完整距离于是精确等于只含 $02$ 差的距离，在 $N=1$ 达到单步最优风险 $\mathcal R_1$，在 $N=n$ 达到全视界下界 $H$。

对其他视界，先控制一个对 $p$ 统一的无限尾。固定任意 $\bar q\in(r,1)$，将 $p$ 限制得足够小，使 $q\le\bar q$。由 $a\le r$、$|Z_{N,p}|\le1$，将通道差拆成三个单边 Schur 乘子，应用第161节的单边估计及三角不等式，得到
$$
\sup_{|\phi|\le\alpha}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{(p)})
\le r^N-a^N+\frac{r^N+q^N}{2}
\le2\bar q^N.
\tag{173.17}
$$
选整数 $K>n$ 使 $2\bar q^K<H$，则 $N\ge K$ 的风险统一严格小于 $H$。对剩下的有限集合 $1\le N<K$、$N\ne n$，在 $p=0$ 时风险为 $B_N<H$，其中严格号使用唯一最大点假设。有限次通道复合连续，实际相位区间紧，因此各个最坏风险都随 $p$ 连续。进一步缩小同一个正 $p$，便可保留全部有限严格不等式，同时保留（173.13）—（173.16）。于是这个固定预测器的全视界风险至多为 $H$，又在 $n$ 精确达到 $H$，故为精确最优。所有参数在运行前由 $r$ 确定；并未按被比较的运行视界 $N$ 重新选择通道。

每个条件系统通道都保迹，所以在标准新鲜输入接线中，丢弃系统输出后只有记忆翻转链作用于初始记忆的参考算符块。与式（171.11）相同的计算给出（173.1），可取 $E_{r,N}(A)=\operatorname{Tr}(A)I_2/2$，误差随 $(1-2p)^N$ 指数消失。这里 $p>0$ 对所选 $r$ 固定，没有声称该遗忘速率对 $r\uparrow1$ 一致。因此这是合法的可遗忘二维实现。定理169.4排除同一区间内维数一同时满足精确单步与全视界最优，故 $D_{\rm fg}(r)=2$。

最后证明参数集合的性质。对任意 $r\in U$，可在一个小邻域中选 $\bar r<1$ 使 $B_N(s)\le\bar r^N$，从而统一排除充分大的 $N$ 成为最大点。剩余有限个连续函数在 $r$ 处具有唯一最大者，其严格差距在一个更小邻域内保留。因此 $U$ 是开集。

若 $s\in I\setminus U$，则至少有两个不同的早视界 $j,k$ 并列最大，从而
$$
s^j\sin(j\alpha(s))=s^k\sin(k\alpha(s)).
\tag{173.18}
$$
对每对固定 $j\ne k$，两边都是 $(1/\sqrt3,1)$ 上的实解析函数，且不恒等：当 $s\uparrow1$，它们的一阶项分别为 $j\sqrt3(1-s)$ 与 $k\sqrt3(1-s)$。故其相等点为离散集，至多可数。对可数对整数取并集，得 $I\setminus U$ 至多可数，因而不含非空开区间。这证明 $U$ 稠密。任意趋近一的区间均包含 $U$ 中的点，结合一般的维数一下界，得到（173.3）的下极限。证毕。

第172节的下界需要每个内部条件通道都具有校准系数 $01=12=r$ 及 $02=re^{i\theta_v}$、$|\theta_v|\le\alpha$。本节明确改变了这些内部条件：$a<r$、$q>r$、$\theta>\alpha$，但实际源、精确单步最优要求与全视界终端风险合同保持原定义。隐函数调整保留唯一最大视界的接触等式，额外相干方向的距离余量与其他视界的严格风险余量允许正的遗忘率。因此状态数下界依赖允许的内部实现，而不仅取决于相同的最优风险值。并列最大点需要同时保持多个接触等式，当前构造未解决这一例外集；这里也没有给出量子相干记忆相对于经典记忆的优势结论。

<a id="entry-696"></a>

## 追加锚（本行以下为增补区）

<a id="section-174"></a>

## 174. 三维相干记忆的精确最优、可遗忘性与相邻接触校准

**定义 174.1（相邻校准视界与启动记忆）。** 沿用定义173.1的一次初始化、时间齐次联合 CPTP 处理器、同一系统终端通道、标准新鲜输入遗忘条件及最小维数 $D_{\rm fg}(r)$。实际源仍为 $\mathcal M_{r,\phi}$，同一次运行的实际相位 $\phi$ 固定，环境逐步新鲜。记
$$
c=r\cos\alpha,\qquad b=r\sin\alpha,\qquad z_*=c+ib,
\qquad \alpha=\alpha(r).
\tag{174.1}
$$
在充分接近一的区间中，令 $n$ 为持续端点比特风险 $B_N(r)$ 的最小最大点，令 $m=n+1$。以下所用记忆为
$$
K=\mathbb C|e\rangle\oplus\mathbb C^2,
\qquad \sigma=|e\rangle\langle e|,
\tag{174.2}
$$
其中 $|e\rangle$ 是启动态，活动子空间的基为 $|+\rangle,|-\rangle$；启动态计入总维数。所有设计参数只依赖已知的 $r$，同一处理器服务全部运行视界 $N$。

**定理 174.2（全部近一参数上的相干三维实现）。** 存在 $r_1<1$，使每个 $r\in(r_1,1)$ 都有定义174.1的三维实现，满足
$$
\sup_{|\phi|\le\alpha}
d_{\rm ref}(\mathcal M_{r,\phi},\mathcal P_{r,1})=\mathcal R_1(r),
\qquad
\sup_{N\ge1,\,|\phi|\le\alpha}
d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N})=H(r),
\tag{174.3}
$$
并满足包含任意惰性参考的遗忘条件（173.1）。活动记忆的某个单步输入通道不是纠缠破坏通道；保持其余参数不动而完全擦除活动记忆的相干，会严格改变实际启动运行的第四步终端读数。因此
$$
2\le D_{\rm fg}(r)\le3\qquad(r_1<r<1).
\tag{174.4}
$$
与定理173.2结合，在唯一最大点集合 $U$ 上仍有 $D_{\rm fg}(r)=2$。式（174.4）包含并列最大点，但不确定这些点上的最小值究竟是二还是三。

证明。 先说明只需校准两个相邻视界。由定理169.3及式（172.4），充分近一时，$\sup_N B_N=H$ 且全部最大点都在 $N\alpha<\pi/2$ 的早段。令 $\beta=-\log r$，早段的连续延拓为
$$
g(t)=\frac12e^{-\beta t}\sin(\alpha t),
\qquad
t_c=\frac1\alpha\arctan\frac\alpha\beta.
\tag{174.5}
$$
其导数在 $t_c$ 前正、其后负，故最大整数只可能为 $\lfloor t_c\rfloor,\lceil t_c\rceil$。由 $\alpha/(1-r)\to\sqrt3$、$\beta/(1-r)\to1$，有 $\alpha t_c\to\pi/3$。进一步缩小区间后，$n\ge2$、$m\alpha<\pi/2$，并且全部最大点都属于 $\{n,m\}$。即使只有一个最大点，以下仍同时校准这两个视界。

取 $0<\kappa<r$，稍后把它选得充分接近 $r$。对 $z=u+iv$ 定义
$$
B(\kappa,z)=
\begin{pmatrix}1&\kappa&z\\\kappa&1&\kappa\\\bar z&\kappa&1\end{pmatrix}.
\tag{174.6}
$$
直接检查主子式可得，其半正定条件恰为
$$
|z-\kappa^2|\le1-\kappa^2.
\tag{174.7}
$$
在 $z=z_*$ 处，原源的端点行列式为零给出
$$
\det B(\kappa,z_*)=2(1-c)(r^2-\kappa^2)>0.
\tag{174.8}
$$
所以固定这样的 $\kappa$ 后，$z_*$ 位于合法圆盘内部。降低另外两条相干系数由此提供完全正性的严格余量。

给出作用于活动子空间的具体相干处理器。取新鲜环境中的实正交单位向量 $f_0,f_1,f_2$，在（174.7）的严格内部定义
$$
\eta=\sqrt{\frac{1-u}{2}}f_1,\qquad
\xi=\kappa f_0+\frac{v}{\sqrt{2(1-u)}}f_1
+\sqrt{\frac{1+u}{2}-\kappa^2-\frac{v^2}{2(1-u)}}f_2.
\tag{174.9}
$$
根号非负正是（174.7）；在当前邻域内 $u<1$。定义单位记录向量
$$
e_0^+=\xi+i\eta,\quad e_2^+=\xi-i\eta,\quad
e_1^+=e_1^-=f_0,\quad
e_0^-=e_2^+,\quad e_2^-=e_0^+.
\tag{174.10}
$$
等距映射 $V_z|j,s\rangle=|j,s\rangle\otimes e_j^s$ 在丢弃环境后定义联合 CPTP 通道 $\mathcal Q_z$。固定活动标签 $s$ 时，其系统条件通道分别是相关矩阵 $B(\kappa,z)$ 与 $B(\kappa,\bar z)$ 的 Schur 通道。

固定 $\chi=1/4$。在 $\mathcal Q_z$ 后依次对记忆施加：将非对角元乘以 $\chi$ 的去相位通道 $\mathcal D_\chi$、旋转 $U_\gamma=e^{-i\gamma X/2}$、以及
$$
\mathcal R_\delta(T)=(1-\delta)T+\delta\operatorname{Tr}(T)I_2/2.
\tag{174.11}
$$
记所得活动处理器为 $\mathcal L_z$。启动块使用通道
$$
\mathcal T(A)=\frac12\sum_{s=\pm}
\operatorname{Schur}(B(\kappa,z_{*,s}))(A)\otimes|s\rangle\langle s|,
\qquad z_{*,+}=z_*,\quad z_{*,-}=\bar z_*.
\tag{174.12}
$$
对任意系统—记忆输入算符 $X$，同一个时间齐次处理器为
$$
\Lambda(X)=\mathcal T(X_{ee})+
\mathcal L_z(X_{\mathrm{act},\mathrm{act}}).
\tag{174.13}
$$
它先丢弃启动与活动子空间间的非对角块，再分别施加 CPTP 通道，故在任意联合输入上 CPTP。每次输出记忆都位于活动子空间；没有外部时钟切换处理器。

计算同一系统反复使用时的终端通道。其 $01,12$ 系数均为 $\kappa^N$。$02$ 记忆块写成 $(x_NI+iy_NZ+ih_NY)/2$，其中 $X,Y,Z$ 为通常的 Pauli 矩阵，终端 $02$ 系数为实数 $x_N$。令 $s=1-\delta$，直接由记录向量内积得到
$$
(x_1,y_1,h_1)=(c,b,0),
\qquad
\begin{aligned}
x_{N+1}&=ux_N-vy_N,\\
y_{N+1}&=s\bigl[\cos\gamma(vx_N+uy_N)+\chi\sin\gamma h_N\bigr],\\
h_{N+1}&=s\bigl[-\sin\gamma(vx_N+uy_N)+\chi\cos\gamma h_N\bigr].
\end{aligned}
\tag{174.14}
$$
具体说，$02$ 块在旋转与重置之前的变换是
$$
T\longmapsto
\begin{pmatrix}zT_{++}&\chi T_{+-}\\\chi T_{-+}&\bar zT_{--}\end{pmatrix};
\tag{174.15}
$$
这也直接验证了递推，没有用正权经典路径分布替代相干处理器。

在 $\delta=\gamma=0$ 时，$x_N=\operatorname{Re}(z_*z^{N-1})$。现在对固定 $r,\kappa$，要求
$$
x_n=r^n\cos(n\alpha),\qquad
x_m=r^m\cos(m\alpha).
\tag{174.16}
$$
在 $(u,v,\delta,\gamma)=(c,b,0,0)$ 处，这两个等式成立。其左侧关于 $(u,v)$ 的 Jacobian 行为
$$
\bigl((N-1)r^{N-1}\cos((N-1)\alpha),
-(N-1)r^{N-1}\sin((N-1)\alpha)\bigr),\qquad N=n,m,
\tag{174.17}
$$
行列式为 $-n(n-1)r^{2n-1}\sin\alpha\ne0$。实解析隐函数定理因此给出 $z=z(\delta,\gamma)$，在零点取值 $z_*$，并精确满足（174.16）。递推式在实参数的零点邻域解析，负 $\delta$ 仅用于解析延拓，不作概率解释。选择充分小的 $\delta=\gamma>0$，利用（174.8）的严格余量，所得 $z$ 仍在合法圆盘内部。

下面验证完整系统及任意参考上的风险。定理168.2证明中的 Schur 支配估计给出：对
$$
D(d,w)=\begin{pmatrix}0&d&w\\d&0&d\\\bar w&d&0\end{pmatrix},
\qquad d\ge0,
\tag{174.18}
$$
当 $2d\le|w|$ 时，$\frac12\|\operatorname{Schur}(D(d,w))\|_\diamond=|w|/2$。固定 $d$，对 $|w|=Q$ 应用该估计，再将圆盘内的 $w$ 写成圆周点的凸组合，得到
$$
2d\le Q,\quad |w|\le Q
\quad\Longrightarrow\quad
\frac12\|\operatorname{Schur}(D(d,w))\|_\diamond\le Q/2.
\tag{174.19}
$$
对 $N\in\{1,n,m\}$，式（174.14）、（174.16）给出
$$
d=r^N-\kappa^N,\qquad
w=r^N\bigl(e^{iN\phi}-\cos(N\alpha)\bigr),\qquad
Q=r^N\sin(N\alpha).
\tag{174.20}
$$
因为 $N\alpha<\pi/2$，允许相位弧上有 $|w|\le Q$。选 $\kappa$ 足够接近 $r$，可对这三个视界同时保证 $2d<Q$。故风险至多 $Q/2$；端点相位与均衡 $02$ 输入又达到 $Q/2$。单步风险精确为 $\mathcal R_1$，视界 $n$ 精确达到 $H$。

还须用同一组正参数控制其他全部视界。先令 $\tau=(3+r)/4<1$，将校准解限制在 $|z|<(1+r)/2$。没有 $\mathcal D_\chi$ 时，$02$ 交叉块变换可写成两个等距映射夹住 $T$ 再偏迹，因而在迹范数上压缩。将 $\mathcal D_\chi=\chi\,\mathrm{id}+(1-\chi)\mathcal D_0$ 分解，完全去相位部分在（174.15）中的范数至多 $|z|$，所以一次交叉块传递的诱导迹范数至多
$$
\chi+(1-\chi)|z|<\tau.
\tag{174.21}
$$
旋转及重置也是迹范数压缩。启动的 $02$ 块迹范数为 $r$，因此
$$
|x_N|\le r\tau^{N-1}\le\tau^N,
\qquad
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N})
\le r^N-\kappa^N+\frac{r^N+|x_N|}{2}
\le2\tau^N.
\tag{174.22}
$$
中间的不等式按三个非对角边拆分，使用第161节包含参考的单边距离估计。

先固定整数 $K_0>m$ 使 $2\tau^{K_0}<H$。对有限集合 $N<K_0$、$N\notin\{1,n,m\}$，有 $B_N<H$。当前风险又至多
$$
B_N+(r^N-\kappa^N)
+\frac12\left|x_N-r^N\cos(N\alpha)\right|.
\tag{174.23}
$$
因此先选足够接近 $r$ 的 $\kappa<r$，使（174.20）的支配条件成立，并让（174.23）的第一项误差小于各有限严格余量的一半；固定该 $\kappa$ 后，再沿校准解选足够小的 $\delta=\gamma>0$，使第二项误差落在其余余量内，同时保持完全正性与（174.21）。这种顺序保留了严格正的选择区间。式（174.22）控制所有 $N\ge K_0$，式（174.20）控制三个保留视界，遂得（174.3）。

遗忘性使用另一种接线：系统输入逐次新鲜，丢弃系统输出，只比较最终记忆。任意初始记忆经过一次使用后都在活动子空间。以后的每次使用都含概率为 $\delta$、独立于输入的重置分支。给定某次重置已发生，在丢弃此前系统输出后，重置记忆为 $I_2/2$，与尚未使用的输入及参考独立。此前处理对被丢弃部分保迹，故不能改变这些未使用输入及参考的边缘态。因而对具有相同完整系统输入—参考边缘态的任意两份初始联合态 $\rho_1,\rho_2$，有
$$
\left\|\operatorname{Tr}_{B^N}
(\Gamma_{r,N}\otimes\mathrm{id}_R)(\rho_1-\rho_2)\right\|_1
\le2(1-\delta)^{N-1}.
\tag{174.24}
$$
这里 $B^N$ 表示所有系统输出。具体取任意固定记忆态 $\sigma_0$，定义 $E_{r,N}(A)=\Phi_{r,N}(\sigma_0\otimes A)$，在上式比较 $\rho$ 与 $\sigma_0\otimes\operatorname{Tr}_K\rho$，即得
$$
\|\Phi_{r,N}-E_{r,N}\circ\operatorname{Tr}_K\|_\diamond
\le2(1-\delta)^{N-1}\longrightarrow0.
\tag{174.25}
$$
态输入与任意参考上的一致界等于这里两 CPTP 通道之差的 diamond 范数界。这正是定义173.1的遗忘条件；它不要求保留在外部的输出历史消失。此框架及稀少重置产生遗忘性的背景见 Kretschmann–Werner，*Quantum Channels with Memory*，[arXiv:quant-ph/0502106v2](https://arxiv.org/pdf/quant-ph/0502106v2)，§V定义3、命题9与定理10；精确保留（174.16）还使用了上述校准与全视界估计。

最后核对相干确实参与该实现。将活动处理器的系统输入固定为 $|1\rangle$，记录向量均为 $f_0$，所以记忆通道恰为 $\mathcal R_\delta\operatorname{Ad}_{U_\gamma}\mathcal D_\chi$。其归一化 Choi 态的部分转置具有特征值
$$
\frac\delta4-\frac{(1-\delta)\chi}{2}<0\qquad(0<\delta<1/3).
\tag{174.26}
$$
旋转是局部酉变换，不改变该部分转置的谱。故此通道能保留与参考的纠缠，不是纠缠破坏通道。另一方面，固定已经选好的 $\kappa,z,\delta,\gamma$，只将保留相干的参数 $\chi$ 改为零，由（174.14）得到
$$
x_4(\chi)-x_4(0)
=(1-\delta)^2v\chi\sin^2\gamma\,(vc+ub)>0.
\tag{174.27}
$$
严格正号来自校准解充分接近 $u=c>0,v=b>0$，以及 $0<\gamma<\pi$。对均衡 $02$ 系统输入，终端相干读数因而严格不同。这一比较不重新校准其他参数，证明的是该实现实际使用了记忆相干。三维上界与定理169.4的维数一下界共同给出（174.4）。证毕。

式（174.27）区分了同一实现中是否保留相干，没有比较所有经典实现与所有量子实现的最小资源。当前上界的成立也没有要求在所有 $r\uparrow1$ 上统一选择正的重置率。允许的内部条件通道依旧是定义173.1的较大 CPTP 类，而非定义172.1的校准源选择器；该区别与实际源、未知固定相位及终端风险的定义分别承担不同假设。

<a id="entry-698"></a>

## 追加锚（本行以下为增补区）

<a id="section-175"></a>

## 175. 平稳经典三态的双视界校准与精确可遗忘预测

**定义 175.1（带去相位状态的平稳选择器）。** 沿用定义173.1的一般 CPTP 预测器合同及定义174.1的 $n,m=n+1$；在充分近一的区间中，全部最大风险视界都属于 $\{n,m\}$，且 $n\ge2$、$m\alpha<\pi/2$。记 $c_0=r\cos\alpha$，并对零点邻域内的参数 $p,w,\theta$ 定义
$$
c=\frac{c_0}{1-w},\qquad q=\frac c{\cos\theta},\qquad
a=\sqrt{\frac{1-q^2}{2(1-c)}}.
\tag{175.1}
$$
物理取值要求 $0<p,w<1$、$0<a,q<1$、$c<1$。三个经典标签为 $+,-,0$，其初始分布和每次条件通道之后的转移为
$$
\pi=\left(\frac{1-w}{2},\frac{1-w}{2},w\right),
\qquad T=(1-p)I+p\mathbf1\pi.
\tag{175.2}
$$
标签 $\pm$ 的条件通道是相关矩阵
$$
C_\pm=
\begin{pmatrix}1&a&qe^{\pm i\theta}\\a&1&a\\qe^{\mp i\theta}&a&1\end{pmatrix}
\tag{175.3}
$$
的 Schur 通道，标签 $0$ 的条件通道为完全去相位。记这些通道为 $\mathcal Q_v$，则在任意系统—记忆联合输入上的处理器及初始化为
$$
\Lambda(X)=\sum_{v,u}T(v,u)\mathcal Q_v(X_{vv})\otimes|u\rangle\langle u|,
\qquad \sigma=\sum_v\pi_v|v\rangle\langle v|.
\tag{175.4}
$$
它在每步丢弃经典标签间的相干。真实源仍为固定未知相位的 $\mathcal M_{r,\phi}$，其环境逐步新鲜；仅预测器的内部条件通道允许离开原校准源族。

**定理 175.2（不使用记忆相干的全参数三态上界）。** 对每个充分接近一的 $r<1$，存在定义175.1的合法正参数，使同一个平稳初始化、时间齐次的经典三态预测器同时满足
$$
\sup_{|\phi|\le\alpha}d_{\rm ref}(\mathcal M_{r,\phi},\mathcal P_{r,1})=\mathcal R_1(r),
\qquad
\sup_{N\ge1,\,|\phi|\le\alpha}d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N})=H(r),
\tag{175.5}
$$
以及标准遗忘条件（173.1）。该结论包含并列最大点，不使用量子记忆相干或单独的启动状态。参数由已知 $r$ 一次选定，不随所比较的运行视界 $N$ 改变。

证明。 在 $(p,w,\theta)=(0,0,\alpha)$，原端点关系
$$
1-r^2=2r^2(1-c_0)
\tag{175.6}
$$
给出 $q=a=r$。此时标签 $0$ 不被初始化，两个端点标签永不切换，故终端预测器正是持续端点比特。

首先计算一般参数的终端系数。由（175.2），转移矩阵限制到两个端点标签的行和为 $1-pw$。因此前 $N$ 次条件通道都避开 $0$ 的概率是 $(1-w)(1-pw)^{N-1}$；最后一次使用后的转移不影响该终端通道。条件于避开 $0$，符号初始均匀，转移为对称翻转链，翻转率
$$
f=\frac{p(1-w)}{2(1-pw)}.
\tag{175.7}
$$
任何访问 $0$ 的路径都使非对角系统矩阵元归零，后续 Schur 通道不能重建它们。因此，写 $Z_{N,f}(\theta)$ 为式（173.7）的符号和余弦期望，终端系数恰为
$$
A_N=(1-w)a^N(1-pw)^{N-1},\qquad
u_N=(1-w)q^N(1-pw)^{N-1}Z_{N,f}(\theta),
\tag{175.8}
$$
其中 $01=12=A_N$、$02=u_N\in\mathbb R$。特别地，$u_1=(1-w)q\cos\theta=c_0$，所以关键的单步系数已被恒等地保留。

用 $w,\theta$ 同时校准 $n,m$ 两个视界。定义 $F_N=u_N-r^N\cos(N\alpha)$，有限路径和使其在基点邻域具有实解析延拓。负的 $p,w$ 只用于此延拓。将基点偏导除以 $r^N$，分别记为
$$
d_N=\frac{\partial_\theta u_N}{r^N}
=-\frac{N\sin((N-1)\alpha)}{\cos\alpha},\qquad
b_N=\frac{\partial_wu_N}{r^N}=(N-1)\cos(N\alpha),
\tag{175.9}
$$
以及
$$
h_N=\frac{\partial_pu_N}{r^N}
=\frac12\bigl[\cot\alpha\sin(N\alpha)-N\cos(N\alpha)\bigr].
\tag{175.10}
$$
前两式直接微分（175.8）；在基点有 $q_w=r$。第三式中生存因子的一阶贡献为零，而 $f_p=1/2$；零次与一次翻转路径给出
$$
2h_N=\sum_{j=1}^{N-1}
\bigl[\cos((N-2j)\alpha)-\cos(N\alpha)\bigr].
\tag{175.11}
$$
三角和恒等式把它化为（175.10）。对当前的早视界 $n,m$，每个括号严格为正，所以 $h_N>0$，同时 $b_N>0,d_N<0$。

令 $x=n\alpha$、$\lambda=d_m/d_n$，消去共同的 $\theta$ 方向，得到两个余项
$$
\begin{aligned}
R_b&=b_m-\lambda b_n
=\frac{\sin x\cos x-n^2\sin\alpha\cos\alpha}
{n\sin(x-\alpha)},\\
R_h&=h_m-\lambda h_n
=\frac{\cos\alpha\,[n^2\sin^2\alpha-\sin^2x]}
{2n\sin\alpha\sin(x-\alpha)}.
\end{aligned}
\tag{175.12}
$$
这两个等式由 $m=n+1$ 及和角公式直接展开得到。其符号无需渐近估计：$\sin t/t$ 在 $(0,\pi)$ 严格递减，而 $0<\alpha<x<\pi/2$、$n\ge2$，所以
$$
\sin x<n\sin\alpha,
\qquad
\sin x\cos x<n\sin\alpha\cos\alpha
<n^2\sin\alpha\cos\alpha.
\tag{175.13}
$$
因此 $R_h>0$、$R_b<0$，而 $(F_n,F_m)$ 对 $(\theta,w)$ 的 Jacobian 行列式为 $r^{n+m}d_nR_b>0$。

隐函数定理给出 $w(p),\theta(p)$，满足 $w(0)=0,\theta(0)=\alpha$，并精确保留
$$
u_n=r^n\cos(n\alpha),\qquad u_m=r^m\cos(m\alpha).
\tag{175.14}
$$
对两等式微分并消元可得
$$
w'(0)=-\frac{R_h}{R_b}>0,\qquad
\theta'(0)=-\frac{h_n+b_nw'(0)}{d_n}>0.
\tag{175.15}
$$
沿此解支，式（175.1）及（175.6）又给出
$$
q'(0)=r\bigl[w'(0)+\tan\alpha\,\theta'(0)\bigr]>0,
\qquad
a'(0)=-\frac r2w'(0)
-\frac{r^3\tan\alpha}{1-r^2}\theta'(0)<0.
\tag{175.16}
$$
例如，对 $a^2$ 分别求偏导，基点值为 $\partial_w(a^2)=-r^2$、$\partial_\theta(a^2)=-2r^4\tan\alpha/(1-r^2)$，即得后一式。故对所选固定 $r$，全部充分小的正 $p$ 都满足 $0<w<1$、$\theta>\alpha$、$r<q<1$、$0<a<r$、$c<1$。

矩阵（175.3）的一阶与二阶主子式为正，且
$$
\det C_\pm=1-2a^2-q^2+2a^2q\cos\theta
=1-q^2-2a^2(1-c)=0.
\tag{175.17}
$$
所以它们为半正定的秩二相关矩阵，条件 Schur 通道合法。若 $K_{v,j}$ 是 $\mathcal Q_v$ 的 Kraus 算符，则（175.4）的 Kraus 算符为 $\sqrt{T(v,u)}K_{v,j}\otimes|u\rangle\langle v|$，其伴随乘积之和为单位算符。这验证了任意联合输入上的完全正性与保迹性。

对三个视界 $S=\{1,n,m\}$，单步恒等式及（175.14）给出 $u_N=r^N\cos(N\alpha)$。又有 $0\le A_N\le r^N$，且 $A_N\to r^N$ 当 $p\downarrow0$。源与预测器的 Schur 差因而为式（174.18）的矩阵，其中
$$
d=r^N-A_N,\qquad
w=r^N\bigl(e^{iN\phi}-\cos(N\alpha)\bigr).
\tag{175.18}
$$
由早段相位弧几何，$|w|\le Q_N:=r^N\sin(N\alpha)$。将正 $p$ 限得充分小，可同时保证 $2(r^N-A_N)<Q_N$。包含任意参考的支配估计（174.19）于是给出风险上界 $Q_N/2$，端点相位与均衡 $02$ 输入达到它。因此单步风险精确为 $\mathcal R_1$，在 $n$ 精确达到 $H$，并在 $m$ 也保留原最优风险 $\mathcal R_m\le H$。

为同时控制其余全部视界，固定 $r<\bar q<1$，缩小正 $p$ 使 $q\le\bar q$。由（175.8）有 $|u_N|\le q^N$，逐边距离估计给出
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N})
\le r^N-A_N+\frac{r^N+|u_N|}{2}
\le2\bar q^N.
\tag{175.19}
$$
选 $K>m$ 使 $2\bar q^K<H$，则所有 $N\ge K$ 都严格低于 $H$。其余有限个 $N<K$、$N\notin S$ 满足 $B_N<H$，而
$$
d_{\rm ref}(\mathcal P_{r,N},\mathcal P_{r,N}^{\rm bit})
\le r^N-A_N+
\frac12|u_N-r^N\cos(N\alpha)|\longrightarrow0.
\tag{175.20}
$$
故这些严格余量在同一个充分小的正 $p$ 下全部保留。有限多个正邻域的交仍含正参数，并列最大点已由（175.14）精确保持。至此得到（175.5）。

最后在新鲜系统输入、丢弃全部系统输出的接线中检验遗忘。记 $\Pi=\mathbf1\pi$，则 $\Pi^2=\Pi$，故
$$
T^N=(1-p)^NI+[1-(1-p)^N]\Pi.
\tag{175.21}
$$
初始记忆可与全部系统输入及惰性参考任意相关。令 $A_v$ 为初始记忆对角块 $v$ 在偏迹全部系统输入后得到的参考正算符，则 $\sum_vA_v=\tau_R$。因为所有条件系统通道保迹，在丢弃输出后这些参考算符块只受 $T$ 作用。因此最终记忆—参考态恰为
$$
\tau_{KR}^{(N)}
=(1-p)^N\sum_v|v\rangle\langle v|\otimes A_v
+[1-(1-p)^N]\sigma\otimes\tau_R.
\tag{175.22}
$$
从而 $\frac12\|\tau_{KR}^{(N)}-\sigma\otimes\tau_R\|_1\le(1-p)^N$。取常值制备通道 $E_{r,N}(A)=\operatorname{Tr}(A)\sigma$，便得到
$$
\|\Phi_{r,N}-E_{r,N}\circ\operatorname{Tr}_K\|_\diamond
\le2(1-p)^N\longrightarrow0,
\tag{175.23}
$$
即定义173.1的标准遗忘条件。证毕。

这里使用的经典开关与遗忘框架见 Kretschmann–Werner，*Quantum Channels with Memory*，[arXiv:quant-ph/0502106v2](https://arxiv.org/pdf/quant-ph/0502106v2)，§III C与§V；该文定理10的稀少噪声近似并不单独给出（175.5）的精确等号。当前构造用第三个去相位标签提供第二个可校准方向，（175.12）的相反符号保证了物理正参数下的同时补偿。第174节相干实现的读数差仍成立，但同样的三态维数上界也能由本节的纯经典实现达到；三态上界本身不能作为量子资源优势的依据。并列最大点处是否存在满足同一合同的双态实现，以及能否对 $r\uparrow1$ 保持统一遗忘率，仍未由这些构造确定。

<a id="entry-700"></a>

## 追加锚（本行以下为增补区）

<a id="section-176"></a>

## 176. 相干相位反转与全部近一参数的双维精确最优

**定义 176.1（活动比特的相位反转校准）。** 沿用定义173.1的一般 CPTP 预测器合同、最小记忆维数 $D_{\rm fg}(r)$ 及定义174.1的 $c=r\cos\alpha$、$b=r\sin\alpha$、$n,m=n+1$。令 $K=\mathbb C^2$，一次初始化为 $I_2/2$。选 $0<\kappa<r$、$z=c+iv$，采用式（174.9）—（174.10）的记录向量及相干通道 $\mathcal Q_z$。在每次 $\mathcal Q_z$ 后，对记忆依次施加 $\mathcal D_\chi$、$U_\gamma=e^{-i\gamma X/2}$ 及重置 $\mathcal R_\delta$。

这里允许 $-1\le\chi<0$：$\mathcal D_\chi$ 将记忆非对角元乘以 $\chi$，仍是 CPTP 通道，因为
$$
\mathcal D_\chi=\frac{1+\chi}{2}\,\mathrm{id}
+\frac{1-\chi}{2}\operatorname{Ad}_Z
=|\chi|\operatorname{Ad}_Z+(1-|\chi|)\mathcal D_0.
\tag{176.1}
$$
负号表示相干的相位反转，不是负概率。此处理器没有启动标志；全部记忆维数为二。

**定理 176.2（并列最大点也允许双维精确最优）。** 存在 $r_2<1$，使对每个 $r\in(r_2,1)$，都能在定义176.1中选择 $-1<\chi<0$、$0<\delta<1$、$0<\gamma<\pi$ 及合法的 $\kappa,v$，使同一个时间齐次处理器满足精确单步最优、全视界风险 $H(r)$ 及标准遗忘条件（173.1）。因此
$$
\boxed{D_{\rm fg}(r)=2\qquad(r_2<r<1).}
\tag{176.2}
$$
这个结论包含两个相邻视界并列最大之处。所得实现实际使用相干；它不单独给出经典双态实现的下界。

证明。 所有最大视界都包含在 $\{n,m\}$，且 $n\ge2$、$m\alpha<\pi/2$，见（174.5）的定位。令
$$
\varepsilon=1-r,\qquad \beta=-\log r,\qquad
t_* =\frac{\pi}{3\sqrt3},\qquad
\varepsilon n\longrightarrow t_*.
\tag{176.3}
$$
以下先核对校准方程具有物理正的重置率，再选择完全正性与全视界风险所需的参数邻域。

令 $q=1-\cos\gamma$、$s=1-\delta$。为在 $q=0$ 处使用解析变量，将式（174.14）的第三个坐标改写成 $j_N=\sin\gamma\,h_N$。由活动比特初始化可得
$$
(x_0,y_0,j_0)=(1,0,0),\qquad
\begin{aligned}
x_{N+1}&=cx_N-vy_N,\\
y_{N+1}&=s\bigl[(1-q)(vx_N+cy_N)+\chi j_N\bigr],\\
j_{N+1}&=s\bigl[-(2q-q^2)(vx_N+cy_N)+\chi(1-q)j_N\bigr].
\end{aligned}
\tag{176.4}
$$
对 $0<q<2$，取 $\gamma=\arccos(1-q)$ 即恢复实际通道；零点附近其余实参数只用于递推的解析延拓。终端系数为 $01=12=\kappa^N$、$02=x_N\in\mathbb R$，且 $x_1=c$ 恒成立。

在 $q=\delta=0,v=b$，有 $x_N=r^N\cos(N\alpha)$。先暂取 $\chi=-1$，记此基点的三个偏导为
$$
V_N=\partial_vx_N=-Nr^{N-1}\sin((N-1)\alpha),\qquad
D_N=\partial_\delta x_N,\qquad G_N=\partial_qx_N.
\tag{176.5}
$$
后两者可从生成函数明确计算。设 $\rho^2=c^2+v^2$、$A=s(1-q)$、$B=s^2$，消去递推中的 $y,j$，得到形式幂级数恒等式
$$
\sum_{N\ge0}x_N\zeta^N
=\frac{1+A(1-c)\zeta-Bc\zeta^2}
{1-[c+A(c-1)]\zeta+[A(\rho^2-c)-Bc]\zeta^2+B\rho^2\zeta^3}.
\tag{176.6}
$$
在基点令 $Q(\zeta)=1-2c\zeta+r^2\zeta^2$，直接求导给出
$$
\sum_{N\ge0}D_N\zeta^N=\frac{b^2\zeta^2}{Q(\zeta)^2},
\qquad
\sum_{N\ge0}G_N\zeta^N
=\frac{1-\zeta}{1+\zeta}\frac{b^2\zeta^2}{Q(\zeta)^2}.
\tag{176.7}
$$
特别地，
$$
D_N=\frac{r^N}{2}
\bigl[\cot\alpha\sin(N\alpha)-N\cos(N\alpha)\bigr].
\tag{176.8}
$$
式（176.7）的额外因子记录相位反转对重置方向的改变。

为确定两个校准方程所需重置率的符号，以下给出统一的近一渐近式。令 $a=\sqrt3$，对实变量 $t$ 定义
$$
\begin{aligned}
d_\varepsilon(t)&=\frac{e^{-(\beta/\varepsilon)t}}2
\left[\varepsilon\cot\alpha\sin\!\left(\frac\alpha\varepsilon t\right)
-t\cos\!\left(\frac\alpha\varepsilon t\right)\right],\\
f_\varepsilon(t)&=-\frac t r e^{-(\beta/\varepsilon)t}
\sin\!\left(\frac\alpha\varepsilon t-\alpha\right).
\end{aligned}
\tag{176.9}
$$
于是 $D_N=\varepsilon^{-1}d_\varepsilon(\varepsilon N)$、$V_N=\varepsilon^{-1}f_\varepsilon(\varepsilon N)$。由 $\alpha/\varepsilon\to a$、$\beta/\varepsilon\to1$，这些函数及其任意固定阶导数在 $t_*$ 的紧邻域上一致收敛，极限为
$$
d(t)=\frac{e^{-t}}2\left[\frac{\sin(at)}a-t\cos(at)\right],
\qquad f(t)=-te^{-t}\sin(at).
\tag{176.10}
$$

还需把 $G_N$ 与 $d_\varepsilon'$ 联系起来，并控制相位反转的交替项。令 $z_*=re^{i\alpha}$、$k=\cot\alpha$、$a_0(z)=(z-1)/(z+1)$。对式（176.7）取系数，或对等比数列及其 $N$ 倍分别求有限和，得到精确恒等式
$$
G_N=-\frac12\operatorname{Re}\!\left[
\left(a_0(z_*)(N+ik)+\frac{2z_*}{(1+z_*)^2}\right)z_*^N\right]
+\frac{2b^2}{|1+z_*|^4}(-1)^N.
\tag{176.11}
$$
例如，乘子 $(1-\zeta)/(1+\zeta)$ 把数列 $z^N$ 变成 $a_0(z)z^N+2(-1)^N/(1+z)$，再对 $z$ 求导即可核对此式。由于 $z_*$ 接近一，可选趋于零的主支 $\log z_*=-\beta+i\alpha$；有
$$
a_0(z_*)=\tfrac12\log z_*+O(\varepsilon^3),
\qquad
\frac{2z_*}{(1+z_*)^2}=\frac12+O(\varepsilon^2).
\tag{176.12}
$$
当 $\varepsilon N$ 在上述紧邻域内，$N+ik=O(\varepsilon^{-1})$，交替项也是 $O(\varepsilon^2)$。把（176.8）延拓到实数 $N$ 并求导，遂得
$$
G_N=\frac12d_\varepsilon'(\varepsilon N)+O(\varepsilon^2),
\tag{176.13}
$$
余项对该邻域内的整数一致。

令 $\lambda=V_m/V_n$，并设
$$
\Delta_D=D_m-\lambda D_n,\qquad
\Delta_G=G_m-\lambda G_n.
\tag{176.14}
$$
因为 $f(t_*)\ne0$，对 $m=n+1$ 作 Taylor 展开，利用（176.9）、（176.13）可得
$$
\Delta_D\longrightarrow
d'(t_*)-\frac{f'(t_*)}{f(t_*)}d(t_*),\qquad
\frac{\Delta_G}{\varepsilon}\longrightarrow
\frac12\left[d''(t_*)-\frac{f'(t_*)}{f(t_*)}d'(t_*)\right].
\tag{176.15}
$$
这里 $at_*=\pi/3$，直接微分（176.10）给出
$$
\frac{f'(t_*)}{f(t_*)}=\frac1{t_*},\quad
d(t_*)=\frac{e^{-t_*}}4(1-t_*),\quad
d'(t_*)=e^{-t_*}(t_*-1/4),\quad
d''(t_*)=e^{-t_*}(1-t_*).
\tag{176.16}
$$
因此记 $A_*=e^{-t_*}(t_*-1/(4t_*))>0$，则
$$
\Delta_D\longrightarrow A_*,\qquad
\frac{\Delta_G}{\varepsilon}\longrightarrow-\frac{A_*}{2}.
\tag{176.17}
$$
严格正号使用 $t_*>1/2$。这些极限只要求 $\varepsilon n\to t_*$，不要求最大点唯一。

现在求解
$$
x_n(v,\delta,q)=r^n\cos(n\alpha),\qquad
x_m(v,\delta,q)=r^m\cos(m\alpha).
\tag{176.18}
$$
在基点，其关于 $(v,\delta)$ 的 Jacobian 行列式为 $V_n\Delta_D\ne0$。隐函数定理给出 $v(q),\delta(q)$，满足 $v(0)=b,\delta(0)=0$，且
$$
\delta'(0)=-\frac{\Delta_G}{\Delta_D},\qquad
\frac{\delta'(0)}{1-r}\longrightarrow\frac12>0
\quad(\chi=-1).
\tag{176.19}
$$
故在充分近一的整个区间，所需重置率的一阶方向为正。基点处 $j_N=0$，所以 $V_N,D_N$ 与 $\chi$ 无关；$G_N$ 对 $\chi$ 连续。对每个这样的固定 $r$，可先选一个 $-1<\chi<0$ 充分接近 $-1$，使同一 Jacobian 仍非零且 $\delta'(0)>0$。随后固定这个 $\chi$，隐函数解对全部充分小的正 $q$ 满足 $0<\delta(q)<1$。这一步把严格相位反转移入带衰减的合法相干通道内部，并保留两个精确接触等式。

接着确定完全正性与全部视界风险。固定 $\bar\rho\in(r,1)$，令
$$
\tau=|\chi|+(1-|\chi|)\bar\rho<1.
\tag{176.20}
$$
对 $z$ 足够接近 $z_*$ 有 $|z|<\bar\rho$。由（176.1），一次 $02$ 交叉块传递的迹范数至多 $|\chi|+(1-|\chi|)|z|\le\tau$：相位反转支与原相干支都是迹范数压缩，完全去相位支的界为 $|z|$；旋转与重置仍压缩。初始 $02$ 记忆块是 $I_2/2$，迹范数为一，故
$$
|x_N|\le\tau^N,\qquad
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N})
\le r^N-\kappa^N+\frac{r^N+|x_N|}{2}\le2\tau^N.
\tag{176.21}
$$
这同时控制任意惰性参考；最后一步使用 $r<\bar\rho\le\tau$。

先选 $K_0>m$ 使 $2\tau^{K_0}<H$，再选 $\kappa<r$ 充分接近 $r$。对 $N\in\{1,n,m\}$，可保证
$$
2(r^N-\kappa^N)<r^N\sin(N\alpha).
\tag{176.22}
$$
对其余有限的 $N<K_0$，$B_N<H$，可同时令 $r^N-\kappa^N$ 小于各严格余量的一半。此 $\kappa$ 又使 $B(\kappa,z_*)$ 严格正定，见（174.8）。固定 $\kappa$ 后，沿（176.18）选足够小的正 $q$，即可保留相关矩阵正性、$|z|<\bar\rho$、正重置率及全部有限余量，因为
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N})
\le B_N+(r^N-\kappa^N)
+\frac12|x_N-r^N\cos(N\alpha)|.
\tag{176.23}
$$
在 $1,n,m$，恒等式 $x_1=c$ 与校准（176.18）使（174.19）的完整 Schur 支配估计适用，风险分别精确为 $\mathcal R_1,H,\mathcal R_m$。其他有限视界由（176.23）控制，无限尾由（176.21）控制。因此同一固定处理器在全部视界的最坏风险恰为 $H$。

在新鲜输入、丢弃所有系统输出的接线中，每次使用都含独立概率 $\delta>0$ 的记忆重置。一旦重置发生，未使用的输入与参考的边缘态由保迹性保持，记忆被制备成 $I_2/2$。沿（174.24）—（174.25）的论证，任取固定记忆态 $\sigma_0$ 并令 $E_{r,N}(A)=\Phi_{r,N}(\sigma_0\otimes A)$，有
$$
\|\Phi_{r,N}-E_{r,N}\circ\operatorname{Tr}_K\|_\diamond
\le2(1-\delta)^N\longrightarrow0.
\tag{176.24}
$$
所以实现满足标准 KW 遗忘合同。这里遗忘接线与计算终端 $x_N$ 的同一系统接线仍分别定义，框架沿用第174节所引 Kretschmann–Werner 原文。

最后，相干确实影响该双维实现。固定其余已选参数，仅将 $\chi$ 改为零，由（176.4）计算前三步可得
$$
x_3(\chi)-x_3(0)=(1-\delta)^2\chi v^2\sin^2\gamma\ne0.
\tag{176.25}
$$
对均衡 $02$ 输入，这直接改变终端读数。在系统输入 $|1\rangle$ 上，活动记忆通道的归一化 Choi 态部分转置有特征值 $\delta/4-(1-\delta)|\chi|/2$；进一步缩小正 $q$，它严格为负，因此记忆通道也不是纠缠破坏通道。二维上界结合定理169.4在相同合同中的维数一下界，得到（176.2）。证毕。

本节确定的是允许一般 CPTP 内部处理器时的最小 Hilbert 空间维数。第175节的经典三态上界仍成立；是否能在并列参数处另造经典双态实现，不能由（176.25）的相干使用事实判定。式（176.19）描述零扰动附近的校准方向，不给出对 $r\uparrow1$ 统一的正遗忘率；最终参数还必须同时满足完全正性、有限风险余量与无限尾界。

<a id="entry-702"></a>

## 追加锚（本行以下为增补区）

<a id="section-177"></a>

## 177. 经典双态的精确最优、选择器障碍与更新耦合

**定义 177.1（自主经典双态 Schur 选择器的局部参数）。** 系统仍为三维，真实源、固定未知相位及全参考终端风险沿用定义173.1。经典记忆有两个标签 $+,-$，初始分布为 $(\pi,1-\pi)$，每次条件系统通道后按矩阵
$$
T=\begin{pmatrix}1-\ell_+&\ell_+\\\ell_-&1-\ell_-\end{pmatrix}
\tag{177.1}
$$
更新，且更新不依赖系统输入。两个条件系统通道可以是任意 CPTP Schur 通道，记其 $02$ 系数为 $z_+,z_-$；不要求它们属于原校准源族，不要求初始分布平稳。其他相干系数只受各条件通道的完全正性约束。

记 $U_N$ 为终端 $02$ 系数。对相应的经典路径 $V_1,\ldots,V_N$，有
$$
U_N=\mathbb E\prod_{j=1}^N z_{V_j},\qquad
U_1=\pi z_++(1-\pi)z_-.
\tag{177.2}
$$
局部比较点是永久端点比特的参数
$$
(\pi,z_+,z_-,\ell_+,\ell_-)
=(1/2,z_*,\bar z_*,0,0),\qquad
z_*=r e^{i\alpha}=c+ib.
\tag{177.3}
$$
以下邻域只指这些参数的通常有限维拓扑，不对条件通道的其他相干系数另设接近要求。

**定理 177.2（双接触零集与正转移锥的局部隔离）。** 存在 $r_3<1$，使对每个 $r\in(r_3,1)$，若持续端点比特在 $n,m=n+1$ 两个视界并列达到 $H(r)$，则存在定义177.1中（177.3）的邻域 $\mathcal U_r$，其中没有同时满足精确单步最优、全视界风险 $H(r)$ 及标准遗忘条件（173.1）的经典双态选择器。更具体地，在该邻域内，只要满足前两个风险等号，就必有
$$
\ell_+=\ell_-=0.
\tag{177.4}
$$
这样的并列参数在每个 $(r_0,1)$ 型的充分近一区间内存在。邻域可以依赖 $r$；结论不排除邻域之外的经典双态实现，也不适用于任意非 Schur 条件通道或依赖系统输入的标签更新。

证明。 先从风险合同推出必须满足的矩条件。在 $N\in\{1,n,m\}$，考虑实际相位 $\phi=\pm\alpha$ 及系统输入 $(|0\rangle+|2\rangle)/\sqrt2$。Schur 通道保持对角元，故输出半迹距离为 $|r^Ne^{\pm iN\alpha}-U_N|/2$。当前三个视界均在早段，$N\alpha<\pi/2$；风险合同因此要求 $U_N$ 同时位于以 $r^Ne^{\pm iN\alpha}$ 为圆心、以 $r^N\sin(N\alpha)$ 为半径的两个闭圆盘内。它们外切于唯一一点，故
$$
U_1=c,\qquad
U_n=r^n\cos(n\alpha),\qquad
U_m=r^m\cos(m\alpha).
\tag{177.5}
$$
这里在 $n,m$ 使用两者都为最坏视界；若只有一个最大点，另一个等式并非风险合同所必需。

在 $\pi$ 接近 $1/2$ 时，第一式可用复参数 $h$ 完整参数化为
$$
z_+=c+(1-\pi)h,\qquad z_-=c-\pi h,
\tag{177.6}
$$
基点为 $h=2ib$。再令
$$
S=\ell_++\ell_-,\qquad D=\ell_+-\ell_-.
\tag{177.7}
$$
物理转移率的非负性要求 $S\ge|D|$。有限路径和使 $U_n,U_m$ 对这些实参数解析；使用隐函数定理时允许负转移率的解析延拓，实际选择器仍必须满足非负性。

将（177.5）的后两式拆成四个实方程。先计算基点的 Jacobian。记
$$
V_N=-Nr^{N-1}\sin((N-1)\alpha),\qquad
E_N=\frac{r^N}{2}
\bigl[\cot\alpha\sin(N\alpha)-N\cos(N\alpha)\bigr],
\tag{177.8}
$$
以及
$$
P_N=2\bigl[r^N\sin(N\alpha)
-Nb r^{N-1}\cos((N-1)\alpha)\bigr].
\tag{177.9}
$$
在零转移率处，$U_N=\pi z_+^N+(1-\pi)z_-^N$。将（177.6）代入微分，得到
$$
\partial_{\operatorname{Im}h}\operatorname{Re}U_N=V_N/2,
\quad
\partial_{\operatorname{Re}h}\operatorname{Im}U_N=-V_N/2,
\quad
\partial_\pi\operatorname{Im}U_N=P_N.
\tag{177.10}
$$
相应的另一实部或虚部偏导为零。沿 $D=0$ 增加 $S$，两个翻转率均为 $S/2$，零次与一次翻转路径的微分给出
$$
\partial_S\operatorname{Re}U_N=E_N,\qquad
\partial_S\operatorname{Im}U_N=0.
\tag{177.11}
$$
因此，四个方程关于 $(\operatorname{Im}h,S,\operatorname{Re}h,\pi)$ 的 Jacobian 分成两个实块，行分别由 $(V_N/2,E_N)$ 与 $(-V_N/2,P_N)$ 构成，$N=n,m$。

验证两块都非奇异。令 $\lambda=V_m/V_n$，其中 $V_n<0$。式（175.12）中相邻视界的消元恒等式给出
$$
\Delta_E:=E_m-\lambda E_n
=\frac{r^{n+1}\cos\alpha\,[n^2\sin^2\alpha-\sin^2(n\alpha)]}
{2n\sin\alpha\sin((n-1)\alpha)}>0.
\tag{177.12}
$$
严格正号由 $n\ge2$、$0<n\alpha<\pi/2$ 及 $\sin(n\alpha)<n\sin\alpha$ 得到。对另一块，展开和角公式，直接从（177.8）—（177.9）可得
$$
P_N=4\tan\alpha\,E_N
+\frac{2r\sin^2\alpha}{\cos\alpha}\,V_N,
\qquad
P_m-\lambda P_n=4\tan\alpha\,\Delta_E>0.
\tag{177.13}
$$
两个实块的行列式分别为 $V_n\Delta_E/2$ 与 $-V_n(P_m-\lambda P_n)/2$，所以均非零。这是有限参数处的精确判据。

对每个这样的固定 $r$，实解析隐函数定理把基点附近的全部四方程解写成一条解析曲线
$$
(\operatorname{Im}h,S,\operatorname{Re}h,\pi)
=(v(D),S(D),u(D),\pi(D)),
\tag{177.14}
$$
并且在 $D=0$ 处取基点值。这个表述覆盖邻域内整个零集，不预设候选实现按某个可微参数族给出。

交换两个标签并对系数取共轭，对上述参数的作用为
$$
(D,S,\pi,h)\longmapsto(-D,S,1-\pi,-\bar h).
\tag{177.15}
$$
它把 $U_N$ 变成 $\bar U_N$，保持实目标（177.5），也保持基点。隐函数解的局部唯一性因此蕴含 $S(-D)=S(D)$。由于 $S(0)=0$，解析性给出常数 $C_r<\infty$，使足够小的 $D$ 满足
$$
|S(D)|\le C_rD^2.
\tag{177.16}
$$
物理非负率又要求 $S(D)\ge|D|$。进一步缩小邻域，则 $0<|D|<1/C_r$ 时两者不相容；若 $C_r=0$，结论直接成立。因此物理解只能有 $D=0$，继而 $S=0$，得到（177.4）。

当两个转移率为零时，标准新鲜输入接线中，丢弃条件系统通道的输出后，两个初始经典标签各自保留，永不混合。两个标签所对应最终记忆之差的迹范数恒为二，故不满足（173.1）。这证明邻域内不存在所要求的可遗忘选择器。

最后说明并列参数并非空条件。若某个 $(r_0,1)$ 型的近一区间内每个 $r$ 都有唯一最大视界，则该视界作为整数值函数局部常数：统一尾界先将最大值比较限制为有限个视界，唯一最大点的严格差距在小邻域内保留。区间连通使它在整个区间内恒定，与 $\varepsilon n\to t_*>0$ 矛盾。因此每个 $(r_0,1)$ 型的近一区间都包含并列点，且这些点可以趋近一。证毕。

第173节的经典双态构造只需保持一个最大视界；定理177.2使用两个同时必需的接触方程，并允许初始权重与条件复系数作非对称调整。该障碍针对的是“先按当前标签施加通道、再独立更新标签”的分解。下面允许系统操作与标签更新共享同一次随机选择，仍只保留一个经典比特。

**定义 177.3（与翻转共同发生的去相位）。** 固定近一参数 $r$，取 $0<\delta<1-r$，记
$$
x=1-\delta,\qquad \rho=\frac r x,\qquad
\kappa^2=\frac{1-\rho^2}{2(1-\rho\cos\alpha)},\qquad
\beta=x\kappa.
\tag{177.17}
$$
令 $\mathcal Q_s$ 是相关矩阵
$$
G_s=\begin{pmatrix}
1&\kappa&\rho e^{is\alpha}\\
\kappa&1&\kappa\\
\rho e^{-is\alpha}&\kappa&1
\end{pmatrix},\qquad s=\pm1,
\tag{177.18}
$$
的 Schur 通道，$\Delta$ 是系统完全去相位通道。记忆为两个经典标签，一次均匀初始化。对任意系统—记忆联合输入定义
$$
\Lambda_\delta(X)=\sum_{s=\pm1}
\left[x\mathcal Q_s(X_{ss})\otimes|s\rangle\langle s|
+\delta\Delta(X_{ss})\otimes|-s\rangle\langle-s|\right].
\tag{177.19}
$$
同一次随机选择同时决定系统通道与标签更新：保持标签时施加 $\mathcal Q_s$，翻转时施加 $\Delta$。记忆基间相干在每步被去除，分支随机性来自新鲜环境，不另存为持久记忆。

**定理 177.4（经典记忆也达到全参数双维最优）。** 对每个充分近一的 $r<1$，定义177.3中存在明确的正 $\delta$，使该经典双态记忆满足精确单步最优、全视界风险 $H(r)$ 及标准遗忘条件（173.1），包括全部并列最大点。其 $02$ 终端系数在每个视界都精确等于持续端点比特的系数，而不只是匹配最大点。结合维数一下界，当前合同中的最小记忆维数二可以由经典记忆达到。

此外，存在与（177.19）具有相同单步系统边缘通道及记忆边缘通道的另一经典双态处理器，其全视界风险严格大于 $H(r)$。这两个边缘相同并不确定联合处理器的续接行为。

证明。 首先核对合法性。由 $r<x<1$ 得 $r<\rho<1$，所以（177.17）中的分母为正，且 $\kappa>0$。不等式
$$
1-\rho^2\le2(1-\rho\cos\alpha)
\tag{177.20}
$$
等价于 $|\rho-e^{i\alpha}|^2\ge0$，故 $\kappa\le1$。矩阵 $G_s$ 的一阶、二阶主子式非负，行列式由（177.17）恰为零，因而它是半正定相关矩阵。若 $K_{s,a}$ 为 $\mathcal Q_s$ 的 Kraus 算符，则（177.19）的 Kraus 算符可取
$$
\sqrt{x}K_{s,a}\otimes|s\rangle\langle s|,
\qquad
\sqrt\delta\,|j\rangle\langle j|\otimes|-s\rangle\langle s|.
\tag{177.21}
$$
其伴随乘积之和是单位算符，故处理器在任意联合输入上 CPTP。

端点关系 $2r^2c=3r^2-1$ 又给出
$$
\beta^2=\frac{x(x^2-r^2)}{2(x-c)},\qquad
r^2-\beta^2
=\frac{\delta(x^2+x+1-3r^2)}{2(x-c)}>0.
\tag{177.22}
$$
严格正号使用 $x>r$ 及 $r^2+r+1-3r^2=(1-r)(2r+1)>0$。因此 $0<\beta<r$，并且 $\beta\to r$ 当 $\delta\downarrow0$。

同一系统重复使用时，一条路径只要有一次翻转，其系统非对角元就被完全去相位，后续 Schur 通道不能重建。只有两条从不翻转的路径贡献相干。长度 $N$ 的保持路径包括 $N$ 次保持事件，因而其 $02$ 权重为
$$
x^N\rho^N e^{isN\alpha}=r^N e^{isN\alpha}.
\tag{177.23}
$$
这里最后一次更新也决定最后一次系统通道，与（177.2）中仅后续更新影响路径系数的时序不同。平均两个初始标签后，终端相关矩阵精确为
$$
F_N=\begin{pmatrix}
1&\beta^N&r^N\cos(N\alpha)\\
\beta^N&1&\beta^N\\
r^N\cos(N\alpha)&\beta^N&1
\end{pmatrix}.
\tag{177.24}
$$

现在给出同时控制全部视界的正参数。记 $\mathcal M_r=\operatorname*{arg\,max}_{N\ge1}B_N(r)$，选择近一区间使 $\sup_NB_N=H$。由于 $B_N\le r^N$、$H>0$，最大点集非空且有限。定义
$$
K_r=\min\{K\in\mathbb N:K\ge2,\ 2r^K<H(r)\},
\tag{177.25}
$$
以及有限正数
$$
g_r=\min\left(\{B_1(r),H(r)\}
\cup\{H(r)-B_N(r):1\le N<K_r,\ N\notin\mathcal M_r,\ N\ne1\}\right).
\tag{177.26}
$$
第二个集合为空时省略它。所有最大视界都小于 $K_r$。取
$$
\delta=\min\left\{\frac{1-r}{4},\frac{g_r r(1-r)}{12K_r}\right\}>0.
\tag{177.27}
$$
由 $\delta\le(1-r)/2$ 得 $2(x-c)\ge1-r$；式（177.22）的分子括号至多为三，故
$$
r-\beta\le\frac{3\delta}{r(1-r)}\le\frac{g_r}{4K_r},
\qquad
d_N:=r^N-\beta^N\le N(r-\beta)<\frac{g_r}{4}\quad(1\le N<K_r).
\tag{177.28}
$$

源与（177.24）的差为式（174.18）的 Schur 乘子，其中 $d=d_N$、$w=r^N(e^{iN\phi}-\cos(N\alpha))$。由持续端点比特的风险公式，允许相位上 $\sup_\phi|w|=2B_N$。若 $d_N\le B_N$，则（174.19）的圆盘估计与均衡 $02$ 输入给出完整参考风险的精确等号
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{\delta})=B_N.
\tag{177.29}
$$
式（177.28）保证它同时适用于 $N=1$ 与全部 $N\in\mathcal M_r$，从而单步风险为 $\mathcal R_1$，每个最大视界的风险都为 $H$。

其他视界可将与持续端点比特的差拆成两条相邻边，得到
$$
d_{\rm ref}(\mathcal P_{r,N}^{\delta},\mathcal P_{r,N}^{\rm bit})\le d_N,
\qquad
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{\delta})\le B_N+d_N.
\tag{177.30}
$$
当 $N<K_r$ 且不是单步或最大视界时，（177.26）、（177.28）使此界严格小于 $H$。当 $N\ge K_r$ 时，它至多 $2r^N\le2r^{K_r}<H$。因此同一个（177.27）精确实现全部风险要求，不需要逐个最大视界求隐函数。

在标准新鲜输入接线中，丢弃系统输出后，保迹性使参考算符块只受对称翻转矩阵作用，其非平稳特征值为 $1-2\delta$。取忽略输入并制备均匀记忆的通道 $E_{r,N}$，对任意初始联合态与惰性参考可得
$$
\|\Phi_{r,N}-E_{r,N}\circ\operatorname{Tr}_K\|_\diamond
\le2(1-2\delta)^N\longrightarrow0.
\tag{177.31}
$$
这里 $0<\delta<1/4$。此计算与第171节的参考算符块证明相同，因为每条更新分支中的系统通道都保迹。故经典比特满足标准 KW 遗忘条件。维数一下界仍由定理169.4给出。

最后构造边缘相同但续接不同的处理器。令
$$
\mathcal A_s=x\mathcal Q_s+\delta\Delta,
\qquad
\widetilde\Lambda_\delta(X)=\sum_s\mathcal A_s(X_{ss})
\otimes\bigl[x|s\rangle\langle s|+\delta|-s\rangle\langle-s|\bigr].
\tag{177.32}
$$
它也是 CPTP，且在全部联合输入上都有
$$
\operatorname{Tr}_K\widetilde\Lambda_\delta
=\operatorname{Tr}_K\Lambda_\delta,
\qquad
\operatorname{Tr}_S\widetilde\Lambda_\delta
=\operatorname{Tr}_S\Lambda_\delta.
\tag{177.33}
$$
第一个等式直接来自 $\mathcal A_s$ 的定义，第二个使用条件通道保迹。两者的单步系统风险、经典记忆转移及标准遗忘率相同。

但是 $\mathcal A_s$ 的 $02$ 系数为 $r e^{is\alpha}$，而（177.32）的标签更新与系统通道独立。因此其第 $N$ 步系数为 $r^NZ_{N,\delta}(\alpha)$，其中 $Z$ 是式（173.7）的对称翻转路径期望。取任何最大视界 $n\ge2$；它满足 $n\alpha<\pi/2$。每条符号路径的余弦至少为 $\cos(n\alpha)$，具有正概率的一次翻转路径则严格大于它，故 $Z_{n,\delta}(\alpha)>\cos(n\alpha)$。端点相位与均衡 $02$ 输入于是给出
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^n,\widetilde{\mathcal P}_{r,n})
\ge\frac{r^n}{2}
\sqrt{\sin^2(n\alpha)+[Z_{n,\delta}(\alpha)-\cos(n\alpha)]^2}
>H(r).
\tag{177.34}
$$
这证明最后的边缘与续接断言。证毕。

经典记忆通道与标准遗忘框架的来源仍为 Kretschmann–Werner，*Quantum Channels with Memory*，[arXiv:quant-ph/0502106v2](https://arxiv.org/pdf/quant-ph/0502106v2)，§III C及§V。当前两个处理器都只保留经典标签；区别在于系统去相位与标签翻转是否属于同一次联合事件。定理177.2的局部障碍要求（177.2）的先按标签施加通道再更新的分解，（177.19）不具有该分解。式（177.33）并不修复这项缺失的联合关系。由此，在当前近一参数合同下，维数二的精确最优不需要相干记忆；第176节的相干实现及其擦除相干后的读数差仍成立。这里没有对参数趋近一给出统一的正遗忘率，也不要求有限时间内严格重置。

<a id="entry-704"></a>

## 追加锚（本行以下为增补区）

<a id="section-178"></a>

## 178. 固定边缘下的联合配对、精确风险与二步辨识

**定义 178.1（固定边缘的配对区间）。** 固定充分近一的 $r$，采用定义177.3及式（177.25）—（177.27）的 $\delta,x,\rho,\kappa,\beta,K_r,g_r$，其中 $\delta$ 必须是（177.27）给出的显式选择。记忆一次均匀初始化。对 $0\le w\le\delta$，定义同一个时间齐次联合处理器
$$
\begin{aligned}
\Lambda_w(X)=\sum_s\Big(&[(x-w)\mathcal Q_s(X_{ss})+w\Delta(X_{ss})]
\otimes|s\rangle\langle s|\\
&+[w\mathcal Q_s(X_{ss})+(\delta-w)\Delta(X_{ss})]
\otimes|-s\rangle\langle-s|\Big).
\end{aligned}
\tag{178.1}
$$
参数 $w$ 同时是“施加 $\mathcal Q_s$ 并翻转”与“完全去相位但保持标签”的概率。四个非负分支的总权重为一。$w=0$ 给出（177.19），$w=x\delta$ 给出独立组合（177.32）。记其同一系统终端通道为 $\mathcal P_{r,N}^{w}$，全视界风险为 $W_r(w)$，并令 $\mathcal M_r=\operatorname*{arg\,max}_NB_N(r)$。

**定理 178.2（整个配对区间的精确风险与唯一最优点）。** 这一族处理器全都 CPTP，使用同一经典双态记忆，具有相同的两个单步边缘通道、相同的精确单步最优风险及相同的标准遗忘界（177.31）。令 $p=w/x$，则终端系数精确为
$$
01=12=\beta^N,\qquad
02=r^N Z_{N,p}(\alpha).
\tag{178.2}
$$
对整个 $0\le w\le\delta$，全参考风险满足
$$
W_r(w)=\max_{N\in\mathcal M_r}
\frac{r^N}{2}
\sqrt{\sin^2(N\alpha)+[Z_{N,w/x}(\alpha)-\cos(N\alpha)]^2}.
\tag{178.3}
$$
因此 $w=0$ 是这一固定边缘配对区间内唯一达到 $H(r)$ 的点；任意 $w>0$ 都有 $W_r(w)>H(r)$。

证明。 因为 $w\le\delta<x$，式（178.1）是非负 CP 分支之和，总权重为一。对系统输出或记忆输出分别偏迹，四个分支合并为固定的系统通道 $x\mathcal Q_s+\delta\Delta$ 及固定的记忆翻转率 $\delta$。这证明两个边缘通道在全部联合输入上不依赖 $w$，保迹分支也使新鲜输入接线中的参考算符块始终只受同一个经典翻转矩阵作用。故标准遗忘界及单步系统通道都与定理177.4相同。

任何包含 $\Delta$ 的路径都不贡献终端非对角元。每个当前标签下施加 $\mathcal Q_s$ 的总概率为 $x$；条件于全部 $N$ 步都使用该通道，其符号链初始均匀，每步翻转率为 $w/x$。权重 $x^N$ 分别抵消 $\rho^N$ 与合并 $\kappa^N$，得到（178.2）。影响符号和的翻转有 $N-1$ 次，最后一次标签更新不改变最后一次 $\mathcal Q_s$ 的相位。

对任何 $N\in\mathcal M_r$，已有 $N\ge2$、$N\alpha<\pi/2$。符号和的绝对值不超过 $N$，所以
$$
\cos(N\alpha)\le Z_{N,p}(\alpha)\le1.
\tag{178.4}
$$
当 $p>0$ 时，$p\le\delta/x<1$，恰有一次翻转的路径具有正概率，故左侧严格。令 $z=Z_{N,p}(\alpha)>0$；实际相位弧上 $|e^{iN\phi}-z|$ 的最大值位于端点，等于 $\sqrt{\sin^2(N\alpha)+(z-\cos(N\alpha))^2}$。该值至少为 $\sin(N\alpha)$。又由（177.28）有 $d_N=r^N-\beta^N<B_N=H$，所以（174.19）的完整参考支配估计适用，端点的均衡 $02$ 输入达到它。故（178.3）右侧每一项都是对应视界的精确风险，且对 $w>0$ 严格大于 $H$。

还须排除其他视界在整个配对区间内超过这些值。对任意 $N$，把有翻转与无翻转的条件符号路径分开，得到
$$
|Z_{N,p}(\alpha)-\cos(N\alpha)|
\le2[1-(1-p)^{N-1}]\le2(N-1)p.
\tag{178.5}
$$
于是三个非对角边的参考距离估计给出
$$
\sup_\phi d_{\rm ref}(\mathcal M_{r,\phi}^N,\mathcal P_{r,N}^{w})
\le B_N+d_N+r^N(N-1)p.
\tag{178.6}
$$
当 $N<K_r$、$N\notin\mathcal M_r$ 且 $N\ne1$ 时，由（177.27）—（177.28）及 $p\le\delta/x$、$x>r$，有
$$
d_N<\frac{g_r}{4},\qquad
r^N(N-1)p<\frac{K_r\delta}{x}
\le\frac{g_r r(1-r)}{12x}<\frac{g_r}{12}.
\tag{178.7}
$$
故（178.6）严格小于 $B_N+g_r/3<H$。单步通道固定，其风险是 $\mathcal R_1<H$。当 $N\ge K_r$，由 $|Z_{N,p}|\le1$ 可将风险统一界为
$$
r^N-\beta^N+\frac{r^N+r^N|Z_{N,p}|}{2}
\le2r^N\le2r^{K_r}<H.
\tag{178.8}
$$
全部非最大视界在整个配对区间内都低于 $H$，而最大视界至少达到 $H$，遂得（178.3）及唯一最优断言。证毕。

**定理 178.3（二步充分读数与风险二次项）。** 在定义178.1的固定族内，一个二步相干读数就能恢复 $w$：
$$
u_2(w):=(\mathcal P_{r,2}^{w})_{02}
=r^2\cos(2\alpha)+\frac{2r^2\sin^2\alpha}{x}w.
\tag{178.9}
$$
因此整个族的全部终端通道都由该读数与已知参数唯一决定。两个二步通道的全参考距离为
$$
d_{\rm ref}(\mathcal P_{r,2}^{w},\mathcal P_{r,2}^{0})=J(r)w,
\qquad J(r)=\frac{r^2\sin^2\alpha}{x}>0.
\tag{178.10}
$$
对固定 $r$，当 $w\downarrow0$，有
$$
W_r(w)-H(r)=C(r)w^2+O_r(w^3),
\tag{178.11}
$$
其中
$$
C(r)=\max_{N\in\mathcal M_r}
\frac{r^NL_N^2}{4x^2\sin(N\alpha)}>0,
\qquad
L_N=\sum_{j=1}^{N-1}
[\cos((N-2j)\alpha)-\cos(N\alpha)].
\tag{178.12}
$$
令 $\varepsilon=1-r$、$t_* =\pi/(3\sqrt3)$，则
$$
\varepsilon^2C(r)\longrightarrow
C_*:=\frac{e^{-t_*}(1-t_*)^2}{8\sqrt3},
\qquad
\frac{J(r)}{\varepsilon^2}\longrightarrow3.
\tag{178.13}
$$
这些式子特别给出有明确取序的极限
$$
\lim_{r\uparrow1}(1-r)^3
\left[\lim_{w\downarrow0}
\frac{\sqrt{W_r(w)-H(r)}}
{d_{\rm ref}(\mathcal P_{r,2}^{w},\mathcal P_{r,2}^{0})}\right]
=\frac{\sqrt{C_*}}3.
\tag{178.14}
$$

证明。 两步的符号和只可能为 $\pm2$ 或零，故 $Z_{2,p}=(1-p)\cos(2\alpha)+p$，得到（178.9）。输入 $(|0\rangle+|2\rangle)/\sqrt2$ 后，测量 $|0\rangle\langle2|+|2\rangle\langle0|$ 的期望就是实系数 $u_2(w)$，因而这是可操作的读数。它对 $w$ 仿射且斜率非零；由（178.2）即可计算所有其他终端系数。这一充分性只针对当前固定的一参数族。

两个二步通道的相邻系数均为 $\beta^2$，只在 $02$ 边相差（178.9）的增量。第161节的单边全参考距离因此为增量模长的一半，得到（178.10）。

对任意固定 $N\in\mathcal M_r$，有限路径和给出
$$
Z_{N,p}(\alpha)-\cos(N\alpha)=L_Np+O_N(p^2).
\tag{178.15}
$$
每个求和项严格为正，因为 $N\alpha<\pi/2$、$|N-2j|<N$，所以 $L_N>0$。对（178.3）中的平方根在零处展开，并使用 $p=w/x$，其对应视界的风险为
$$
H(r)+\frac{r^NL_N^2}{4x^2\sin(N\alpha)}w^2+O_r(w^3).
\tag{178.16}
$$
最大点集只有一个或两个元素；对这些有限个式子取最大，余项仍为 $O_r(w^3)$，二次系数为各二次系数的最大值。这一步不要求最大函数在整个参数区间可微，得到（178.11）。

为计算 $r\uparrow1$ 的极限，三角和给出
$$
L_N=\cot\alpha\sin(N\alpha)-N\cos(N\alpha).
\tag{178.17}
$$
每个最大视界都满足 $\varepsilon N\to t_*$、$N\alpha\to\pi/3$、$r^N\to e^{-t_*}$。又有 $\alpha/\varepsilon\to\sqrt3$，故
$$
\varepsilon L_N\longrightarrow\frac{1-t_*}{2}.
\tag{178.18}
$$
显式选择 $\delta\le\varepsilon/4$ 使 $x\to1$。把这些极限代入（178.12），一个最大点或两个最大点都给出同一个极限 $C_*$；代入（178.10）则得到 $J/\varepsilon^2\to3$。对每个固定 $r$，先由（178.10）—（178.11）求内层极限 $\sqrt{C(r)}/J(r)$，再取 $r\uparrow1$，即得（178.14）。证毕。

式（178.1）的两个单步边缘在整个区间上恒定，因而不能辨识 $w$；二步读数则在这一族内将这些不同的联合实现逐一分开。式（178.14）比较的是规定次序下的局部风险与通道距离，不声称对所有 $r$ 存在统一的有限误差邻域，也不直接给出有限样本复杂度。所有记忆标签仍为经典；被保留和检测的是系统操作与记忆更新的联合配对关系。

<a id="entry-706"></a>

## 追加锚（本行以下为增补区）

<a id="section-179"></a>

## 179. 联合配对的辨识信息量与有限查询成本

**定义 179.1（重置后的二步查询与统计任务）。** 固定定义178.1的一参数族及已知的充分近一参数 $r$，令 $\varepsilon=1-r$。一次查询把隐藏经典记忆重新均匀初始化，对信号连续施加两次同一处理器，只返回最终信号；不同查询使用独立的新记忆。允许任意参考系统，以及完整查询之间不依赖未知 $w$ 的自适应操作；不允许读取隐藏标签或干预一次查询的内部两步。由（178.2）、（178.9），查询通道 $\mathcal T_w:=\mathcal P_{r,2}^{w}$ 是相关矩阵为
$$
F(a,u(w))=
\begin{pmatrix}1&a&u(w)\\a&1&a\\u(w)&a&1\end{pmatrix},
\qquad
a=\beta^2,\quad
u(w)=u_0+2Jw,\quad u_0=r^2\cos(2\alpha)
\tag{179.1}
$$
的实 Schur 通道，其中 $J=r^2\sin^2\alpha/x$、$0\le w\le\delta$。

采用对称对数导数信息量：$\dot\sigma=(L\sigma+\sigma L)/2$ 时 $I(\sigma)=\operatorname{Tr}(\sigma L^2)$。用 $I_1(r,w)$ 表示一次查询在全部信号—参考输入上的最大信息量，用 $I_m(r,w)$ 表示 $m$ 次完整查询的全部允许自适应协议之信息量上确界。参数微分保持 $r$ 固定；端点信息量取连续单侧值。本文使用的参数无关通道下信息量单调性及经典程序模拟界，分别是量子估计与通道模拟的既有工具；经典模拟的具体形式可参见 Demkowicz-Dobrzański、Kołodyński、Guţă，*The elusive Heisenberg limit in quantum enhanced metrology*，arXiv:1201.3940v2，式（18）—（19）。一般可编程通道的自适应归约及其辨识下界见 Pirandola、Lupo，*Ultimate precision of adaptive noise estimation*，arXiv:1609.02160v3，补充材料式（85）；其要求程序界与可达界分开的限制在此保留。

**定理 179.2（这一配对族的精确单次信息量）。** 对全部充分近一的 $r$ 及全部 $w\in[0,\delta(r)]$，有
$$
I_1(r,w)=\frac{4J(r)^2}{1-u(w)^2}.
\tag{179.2}
$$
均衡输入 $(|0\rangle+|2\rangle)/\sqrt2$ 和 $02$ 对称、反对称基测量达到此值，加入参考系统不增加这个单次最优值。并且
$$
\sup_{0\le w\le\delta(r)}
\left|\frac{I_1(r,w)}{(1-r)^3}-9\right|\longrightarrow0
\qquad(r\uparrow1).
\tag{179.3}
$$

证明。 先核对适用区间。由（177.27）—（177.28），$r-\beta\le g_r/(4K_r)$。有 $g_r\le B_1=O(\varepsilon)$，而最大视界 $n$ 满足 $\varepsilon n\to t_*>0$、$K_r>n$，故
$$
\beta=r+O(\varepsilon^2),\qquad
a=1-2\varepsilon+O(\varepsilon^2),\qquad
u(w)=1-2\varepsilon+O(\varepsilon^2)
\tag{179.4}
$$
在整个配对区间上一致成立。最后一个式子使用 $J=O(\varepsilon^2)$、$w\le\delta\le\varepsilon/4$。所以 $0<a<1$ 且 $2a-1<u(w)<1$；上界也可由 $u(w)=r^2Z_{2,w/x}(\alpha)\le r^2<1$ 得到。

以下在保持 $a$ 固定时对 $u$ 微分。任意纯信号—参考输入写成 $\sum_i|i\rangle|v_i\rangle$，令 $p_i=\lVert v_i\rVert^2$。输出与矩阵
$$
R_p(u)=\operatorname{diag}(\sqrt p)F(a,u)
\operatorname{diag}(\sqrt p)
\tag{179.5}
$$
经一个不依赖 $u$ 的等距映射相同，因为不同 $i$ 对应的信号基向量正交。混合输入可先纯化，信息量单调性保证这不会减少信息量。因此优化只需考察概率向量 $p$。

交换信号的 $0,2$ 标签记为 $U$。通道与此交换相容。对给定纯输入 $|\psi\rangle$，考虑保留一个参考标记的纯输入
$$
|\widetilde\psi\rangle=
\frac{|\psi\rangle|0\rangle_F+(U\otimes I)|\psi\rangle|1\rangle_F}{\sqrt2}.
\tag{179.6}
$$
其信号人口满足 $p_0=p_2$。输出后去相位标记，得到两个等权且信息量相同的条件输出，信息量等于原输入所给的值。去相位不增加信息量，故（179.6）的信息量至少与原输入一样大。于是可限制到 $p_0=p_2=t/2$、$p_1=1-t$，而不是仅凭信息量的凸性断言这种限制。

令 $\ell=(1-u)/2$、$h=(1+u)/2$。在 $02$ 反对称、对称及 $1$ 的基下，（179.5）分成特征值 $t\ell$ 和二阶块
$$
\begin{pmatrix}
th&a\sqrt{t(1-t)}\\
a\sqrt{t(1-t)}&1-t
\end{pmatrix}.
\tag{179.7}
$$
对 $0<t<1$ 解对称对数导数方程，得到关于 $u$ 的信息量
$$
\mathcal I_u(t)=\frac t4\left[
\frac1\ell+
\frac{1-t(\ell+a^2)}{(1-t\ell)(h-a^2)}\right],
\qquad
\frac{d\mathcal I_u}{dt}=
\frac{1-a^2/(1-t\ell)^2}{4\ell(h-a^2)}.
\tag{179.8}
$$
第一项来自标量块；二阶块的导数为 $\operatorname{diag}(t/2,0)$，其行列式为 $t(1-t)(h-a^2)$，直接代入方程给出第二项。由于 $h>a$、$1-t\ell\ge h$，导数严格为正。端点由各自支持上的信息量或连续极限得到，故最大值在 $t=1$，等于 $1/(1-u^2)$。均衡 $02$ 输入的输出在固定对称、反对称基下给出概率 $(1\pm u)/2$，这一测量达到该信息量。再使用 $du/dw=2J$，得（179.2）。

由（179.4），$1-u(w)^2=4\varepsilon+O(\varepsilon^2)$ 一致成立；由（178.13），$J/\varepsilon^2\to3$。代入即得（179.3）。$F(a,u)$ 在 $2a-1<u<1$ 内正定，因此各端点附近的通道有光滑延伸，所用连续单侧信息量无额外奇点。证毕。

**定理 179.3（允许查询间自适应的信息量界）。** 定义
$$
q_\pm(w)=\frac{1\pm u(w)}2,\qquad
\pi_+(w)=q_+(w)-a,\quad\pi_-(w)=q_-(w),
\qquad
I_{\rm prog}(r,w)=J^2\left(\frac1{\pi_+(w)}+\frac1{\pi_-(w)}\right).
\tag{179.9}
$$
在定理179.2的区间内，两种程序概率严格为正。对任意正整数 $m$，
$$
m I_1(r,w)\le I_m(r,w)\le m I_{\rm prog}(r,w),
\tag{179.10}
$$
并有一致极限
$$
\sup_{0\le w\le\delta(r)}
\left|\frac{I_{\rm prog}(r,w)}{(1-r)^3}-18\right|
\longrightarrow0.
\tag{179.11}
$$
因此最佳自适应信息量为 $\Theta(m(1-r)^3)$，其中常数可对全部 $m\ge1$ 和允许的 $w$ 统一选择；此界不确定 $9$ 与 $18$ 之间的最佳渐近常数。

证明。 令 $\mathcal Q_\pm$ 为相邻系数为零、$02$ 系数为 $\pm1$ 的固定 Schur 通道。其相关矩阵半正定，故它们 CPTP。逐个比较相关矩阵的系数，得到精确分解
$$
\mathcal T_w=a\,\operatorname{Id}
+\pi_+(w)\mathcal Q_+
+\pi_-(w)\mathcal Q_-.
\tag{179.12}
$$
三个权重非负、总和为一。将它们作为正交经典程序态的概率，固定控制通道读取程序并执行对应通道，就实现（179.12）。把任意协议的每次查询替换为此固定控制操作，并把全部协议操作合并，最终输出为
$$
\sigma_w^{(m)}=\mathcal A\bigl(\tau_w^{\otimes m}\bigr),
\qquad
\tau_w=\operatorname{diag}(a,\pi_+(w),\pi_-(w)),
\tag{179.13}
$$
其中 $\mathcal A$ 不依赖 $w$，包含全部输入、参考和适应操作。程序信息量是（179.9），张量积可加性及参数无关通道下的单调性给出（179.10）的上界。分别使用 $m$ 个均衡 $02$ 输入给出下界。这是经典程序模拟方法在当前通道中的应用，不要求当前三维通道具备传态协变性，也不把可编程上界当作自动可达值。

由（179.4），$\pi_\pm(w)=\varepsilon+O(\varepsilon^2)$ 一致成立。结合 $J/\varepsilon^2\to3$，即得（179.11）。与定理179.2的统一极限合用，得到所述量级。证毕。

**定理 179.4（有限查询的二点辨识成本）。** 取同一允许区间中的 $w_0<w_1$，令 $d=w_1-w_0>0$。未知通道等先验地取为 $\mathcal T_{w_0}$ 或 $\mathcal T_{w_1}$，记 $m$ 次查询的最小平均判错概率下确界为 $P_{e,m}^*$。定义两个根保真度
$$
\begin{aligned}
f_{\rm sig}&=\sqrt{q_+(w_0)q_+(w_1)}+
\sqrt{q_-(w_0)q_-(w_1)},\\
f_{\rm prog}&=a+\sqrt{\pi_+(w_0)\pi_+(w_1)}+
\sqrt{\pi_-(w_0)\pi_-(w_1)}.
\end{aligned}
\tag{179.14}
$$
则有有限次数的界
$$
\frac{1-\sqrt{1-f_{\rm prog}^{\,2m}}}{2}
\le P_{e,m}^*\le\frac{f_{\rm sig}^{\,m}}2.
\tag{179.15}
$$
若 $m_{1/4}$ 是使 $P_{e,m}^*\le1/4$ 的最小正整数，则
$$
\frac{\log(4/3)}{-2\log f_{\rm prog}}
\le m_{1/4}\le
\left\lceil\frac{\log2}{-\log f_{\rm sig}}\right\rceil.
\tag{179.16}
$$
当 $r\uparrow1$ 时，在全部 $0\le w_0<w_1\le\delta(r)$ 上一致有
$$
\frac{1-f_{\rm sig}}{\varepsilon^3d^2}\longrightarrow\frac98,
\qquad
\frac{1-f_{\rm prog}}{\varepsilon^3d^2}\longrightarrow\frac94.
\tag{179.17}
$$
特别地，
$$
m_{1/4}=\Theta\!\left(\frac1{(1-r)^3(w_1-w_0)^2}\right),
\tag{179.18}
$$
常数在该区间上统一。该上界由独立均衡 $02$ 输入和经典似然比判别保证，无须估计量无偏或渐近正态假设。

证明。 由（179.13），任何自适应输出的半迹范数距离不超过两个 $m$ 份程序态的距离。程序态可交换，其根保真度为 $f_{\rm prog}^m$；根保真度 $f$ 与半迹范数距离 $D$ 的既有不等式 $D\le\sqrt{1-f^2}$，结合等先验 Helstrom 公式，给出（179.15）的下界。它也可直接由经典分布的柯西—施瓦茨不等式得到。

独立使用均衡 $02$ 输入并在对称、反对称基测量，得到 $m$ 份概率向量 $q(w_j)$。两种联合分布的最优经典判错率等于逐结果较小概率之和的一半。用 $\min\{p,q\}\le\sqrt{pq}$，即得（179.15）的可达上界。解下界不超过 $1/4$ 的必要条件及上界不超过 $1/4$ 的充分条件，得（179.16）。

为证明一致尺度，注意相应可变概率之间的差恰为 $\pm Jd$。对任意两个概率向量 $b,c$，有
$$
1-\sum_i\sqrt{b_ic_i}
=\frac12\sum_i(\sqrt{b_i}-\sqrt{c_i})^2.
\tag{179.19}
$$
对（179.14）的两个向量应用此式并有理化平方根，分别得到
$$
1-f_{\rm sig}=\frac{J^2d^2}{2}
\left[
\frac1{(\sqrt{q_+(w_0)}+\sqrt{q_+(w_1)})^2}
+\frac1{(\sqrt{q_-(w_0)}+\sqrt{q_-(w_1)})^2}
\right],
\tag{179.20}
$$
$$
1-f_{\rm prog}=\frac{J^2d^2}{2}
\left[
\frac1{(\sqrt{\pi_+(w_0)}+\sqrt{\pi_+(w_1)})^2}
+\frac1{(\sqrt{\pi_-(w_0)}+\sqrt{\pi_-(w_1)})^2}
\right].
\tag{179.21}
$$
在整个参数区间上，$q_+=1-\varepsilon+O(\varepsilon^2)$、$q_-=\varepsilon+O(\varepsilon^2)$、$\pi_\pm=\varepsilon+O(\varepsilon^2)$，且 $J/\varepsilon^2\to3$。逐项代入即得（179.17）；这些精确恒等式不要求 $d$ 与 $\varepsilon$ 之间有额外下界。由于 $d\le\delta(r)\to0$，两个根保真度均一致趋于一，$-\log f\sim1-f$ 也一致成立。（179.16）遂给出（179.18），整数取整不改其统一量级。证毕。

上述成本属于定义179.1规定的重置查询实验。第178节的一个精确期望值能辨识参数，与（179.18）的实验次数下界相容：辨识映射的单射性不提供该映射的统计精度。这里的自适应下界不涵盖可干预二步内部过程或可读取隐藏记忆的另一种实验接口。
