# 全点对电阻约束下十二边形的对称性障碍

## 1. 图、电阻与有限参数

**定义 1.1（带标号的正电导环）。** 令 $V=\mathbb Z/12\mathbb Z$，
$e_i=\{i,i+1\}$，$E=\{e_i:i\in V\}$，所得简单图记为 $C_{12}$。
各边电导 $c_i$ 是独立的严格正实数；可行集合不附加对称性条件。
在顶点函数空间上取计数测度内积，定义普通 Laplacian

$$
(L(c)x)_i=c_i(x_i-x_{i+1})+c_{i-1}(x_i-x_{i-1}).
$$

令 $H=\{x\in\mathbb R^{12}:\sum_i x_i=0\}$，按重数记特征值为
$0=\lambda_1(c)<\lambda_2(c)\le\cdots\le\lambda_{12}(c)$。
以 $L(c)^+$ 表示在 $H$ 上等于 $L(c)|_H$ 的逆、在常数上为零的算子。
有效电阻与总电阻取为

$$
R_{\mathrm{eff},c}(i,j)
=(\delta_i-\delta_j)^{\mathsf T}L(c)^+(\delta_i-\delta_j),
\qquad
R(c)=\sum_{0\le i<j\le11}R_{\mathrm{eff},c}(i,j).
$$

这里 $\delta_i$ 是第 $i$ 个坐标向量，和中共有 $66$ 个无序不同点对。
这些约定对应 Cruz Ortega–Menéndez-Conde，
[*Maximal Algebraic Connectivity for Paths with Fixed Effective Resistance*,
arXiv:2306.08187v1](https://arxiv.org/html/2306.08187v1)，
§2、§4 定义 4.1–4.2 以及 §5 式 (3)。
所用经典电学输入是有效电阻的伪逆表达式、
$R(c)=12\operatorname{tr}L(c)^+$ 与电导缩放律；
其矩阵形式见 Ghosh–Boyd–Saberi，
[*Minimizing Effective Resistance of a Graph*](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf)，
[DOI:10.1137/050645452](https://doi.org/10.1137/050645452)，
§§2.4–2.5，式 (8)、(13)–(15)。

**定义 1.2（固定的有限电导向量）。** 对每个 $R_0>0$，置

$$
\begin{aligned}
t&=\frac1{2000},& a&=2+\sqrt3,& T_0&=\frac{143}{12},\\
r_i&=1+2t\cos\frac{\pi i}{6}+2t^2\cos\frac{\pi i}{3}
\quad(0\le i\le11),\\
T&=T_0-2at^2-2t^4,&
\alpha&=\frac{12T}{R_0},& c_i&=\frac{\alpha}{r_i}.
\end{aligned}
$$

辅助电导记为 $\widetilde c_i=1/r_i$。

## 2. 完整非零谱的有限严格分离

**定理 2.1（十二边形的非不变可行向量）。** 对每个实数 $R_0>0$，
定义 1.2 的十二个 $c_i$ 均为有限严格正实数，且

$$
R(c)=R_0,\qquad
\lambda_j(c)>\frac{143(2-\sqrt3)}{R_0}
\quad\text{对每个 }j\in\{2,\ldots,12\}.
$$

另一方面，对每个 $w\in(0,\infty)^{12}$，若 $R(w)=R_0$，
且 $w$ 在 $C_{12}$ 的全部图自同构下不变，则

$$
w_i=\frac{143}{R_0}\quad(0\le i\le11),\qquad
\lambda_2(w)=\frac{143(2-\sqrt3)}{R_0}.
$$

因此不存在支配全部可行正电导向量的自同构不变可行向量。
这些结论不以全局最大值存在为前提。

**证明。** 首先，$0<t<1/2$，$7/2<a<4$，故

$$
r_i\ge1-2t-2t^2>\frac12,\qquad
T>11-8t^2-2t^4>10.
$$

所以 $\widetilde c_i,\alpha,c_i$ 均为有限正数。
对任意正电导，恒等式

$$
x^{\mathsf T}L(c)x=\sum_i c_i(x_i-x_{i+1})^2
$$

表明核恰是常数空间；在 $H$ 上的逆确实存在并严格正定。
下文在复化空间上作酉变换。实对称矩阵的复化保留全部特征值及重数，
故所得界同时控制原实空间中的全部 $11$ 个非零特征值。

先把 $L(\widetilde c)|_H$ 的逆精确表示出来。
定向关联矩阵取 $B\delta_i=\delta_i-\delta_{i+1}$，即
$(Bq)_i=q_i-q_{i-1}$。此时

$$
L(\widetilde c)=B\operatorname{diag}(1/r_i)B^*,\qquad
\ker B=\mathbb C\mathbf1.
$$

边空间的零均值子空间与顶点空间的零均值子空间同维，
$B$ 在两者之间是双射。对每个顶点零均值向量 $h$，
令 $q$ 是满足 $Bq=h$ 的唯一零均值边向量。
由于有限几何级数给出 $\sum_i r_i=12$，有精确的最小能量式

$$
h^*L(\widetilde c)^+h
=\min_{s\in\mathbb C}\sum_i r_i|q_i+s|^2
=q^*\operatorname{diag}(r_i)q-\frac{|r^*q|^2}{12}.
\tag{1}
$$

为核对第一等号，令 $u=L(\widetilde c)^+h$，
$q_*=\operatorname{diag}(1/r_i)B^*u$。
则 $Bq_*=h$，任何其它可行流与 $q_*$ 相差常数。
而 $\mathbf1^*\operatorname{diag}(r_i)q_*=mathbf1^*B^*u=0$，
所以 $q_*$ 与所有循环流在该能量内积下正交，其能量为
$u^*L(\widetilde c)u=h^*L(\widetilde c)^+h$。
第二等号由对复数 $s$ 配方得到，最小点为 $s=-r^*q/12$。
这也验证了 (1) 用的是这些实际边电导。

令 $\theta=\pi/6$、$z=\exp(i\theta)$，在顶点及边空间均使用正交基

$$
f_k(i)=12^{-1/2}z^{ki}\quad(0\le k\le11).
$$

有 $Bf_k=d_k f_k$，其中 $d_k=1-z^{-k}$。
对 $I=\{1,\ldots,11\}$ 定义

$$
\mu_k=|d_k|^{-2}=\frac1{2-2\cos(k\theta)},\qquad
S=\operatorname{diag}_{k\in I}(\sqrt{\mu_k}).
$$

这些对角元的完整列表为

$$
(\mu_1,\ldots,\mu_{11})
=\left(a,1,\frac12,\frac13,2-\sqrt3,\frac14,
2-\sqrt3,\frac13,\frac12,1,a\right).
\tag{2}
$$

令 $A_\ell$ 为 $I$ 上的实对称矩阵，
当 $k-m\equiv\ell$ 或 $-\ell\pmod {12}$ 时 $(A_\ell)_{km}=1$，
其它情形为零；这里仅使用 $\ell=1,2$。
令 $v\in\mathbb R^{11}$ 由

$$
v_1=v_{11}=t,\qquad v_2=v_{10}=t^2,\qquad
v_k=0\quad(k\notin\{1,2,10,11\})
$$

给出。由
$r_i=1+t(z^i+z^{-i})+t^2(z^{2i}+z^{-2i})$，
有限 Fourier 求和直接给出

$$
\bigl(\langle f_k,\operatorname{diag}(r_i)f_m\rangle\bigr)_{k,m\in I}
=I_{11}+tA_1+t^2A_2,\qquad
\langle f_k,r\rangle=\sqrt{12}\,v_k\quad(k\in I).
$$

因此 (1) 中的逆算子与下列实际 $11\times11$ 实对称矩阵酉等价：

$$
M=S(I_{11}+tA_1+t^2A_2-vv^{\mathsf T})S.
\tag{3}
$$

更明确地，若 $D=\operatorname{diag}(d_k)$，
$N=I_{11}+tA_1+t^2A_2-vv^{\mathsf T}$，
则该逆算子的 Fourier 矩阵为 $D^{-*}ND^{-1}$。
写 $D^{-1}=US$，$U$ 为对角酉矩阵，即得 $D^{-*}ND^{-1}=U^*MU$。
这不是只在某个特征向量上的恒等式。

由 (2)–(3)，两个 $A_\ell$ 的对角线均为零，故

$$
\begin{aligned}
\operatorname{tr}L(\widetilde c)^+
=\operatorname{tr}M
&=\sum_{k=1}^{11}\mu_k-2at^2-2t^4\\
&=\frac{143}{12}-2at^2-2t^4=T.
\end{aligned}
\tag{4}
$$

在全点对电阻的经典迹公式中，系数为 $12$：事实上

$$
\sum_{0\le i<j\le11}(\delta_i-\delta_j)(\delta_i-\delta_j)^{\mathsf T}
=12I_{12}-\mathbf1\mathbf1^{\mathsf T}.
$$

将其与 $L(\widetilde c)^+$ 取迹便得到 $R(\widetilde c)=12T$，
包括所有非相邻点对。由于 $L(\alpha\widetilde c)=\alpha L(\widetilde c)$，
有 $R(c)=R(\widetilde c)/\alpha=R_0$。

现在给出 (3) 的整个谱的严格上界。
将指标分成 $P=\{1,11\}$ 与 $Q=I\setminus P$，写成分块

$$
M=\begin{pmatrix}pI_2&F\\F^{\mathsf T}&C\end{pmatrix},
\qquad p=a(1-t^2).
\tag{5}
$$

这里 $P$ 中非对角项恰为 $a(t^2-t^2)=0$。
按 $Q$ 的列次序 $(2,10,3,9,4,5,6,7,8)$，完整交叉块为

$$
F=\left[\sqrt a\,t(I_2-t^2J_2)\ \middle|\
\sqrt{\frac a2}\,t^2 I_2\ \middle|\ 0_{2\times5}\right],
\qquad J_2=\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\tag{6}
$$

$J_2$ 的特征值为 $0,2$，因而 $FF^{\mathsf T}$ 的两个特征值为

$$
a\left(t^2+\frac{t^4}{2}\right),\qquad
at^2(1-2t^2)^2+\frac a2t^4.
$$

由 $0<t^2<1$ 可知第二个不超过第一个。所以

$$
\|F\|^2=\beta^2:=a\left(t^2+\frac{t^4}{2}\right).
\tag{7}
$$

每个 $A_\ell$ 都是十二维空间上两个酉循环移位之和的压缩，
故 $\|A_\ell\|\le2$。由 (2)，$S$ 在 $Q$ 上的范数至多为 $1$。
舍去负半定项 $-Svv^{\mathsf T}S$，得到二次型上界

$$
C\preceq(1+2t+2t^2)I_9\preceq q_0I_9,
\qquad q_0=1+3t.
\tag{8}
$$

置

$$
d=a-1,\qquad \varepsilon=3t+at^2,\qquad
D_0=p-q_0=d-\varepsilon.
$$

以下都是固定有理数与 $\sqrt3$ 的有限比较：

$$
d>\frac52,\qquad
0<\varepsilon<\frac3{2000}+\frac4{4000000}
=\frac{1501}{1000000}<\frac1{500},\qquad D_0>2.
\tag{9}
$$

对每个分块向量 $(x,y)\in\mathbb C^2\oplus\mathbb C^9$，
由 (5)、(7)、(8) 及配方不等式
$2\beta\|x\|\|y\|\le(\beta^2/D_0)\|x\|^2+D_0\|y\|^2$，有

$$
\begin{aligned}
(x,y)^*M(x,y)
&\le\left(p+\frac{\beta^2}{D_0}\right)\|x\|^2+p\|y\|^2\\
&\le m(\|x\|^2+\|y\|^2),\qquad
m:=a(1-t^2)+\frac{a(t^2+t^4/2)}{D_0}.
\end{aligned}
\tag{10}
$$

因此 $\rho:=\lambda_{\max}(M)\le m$。
为把这个界与 (4) 的迹严格比较，由 (9) 得

$$
\begin{aligned}
\frac{1+t^2/2}{D_0}-\frac1d
&=\frac{\varepsilon}{dD_0}+\frac{t^2}{2D_0}\\
&<\frac1{2500}+\frac1{16000000}<\frac1{2000}.
\end{aligned}
\tag{11}
$$

又因 $1/(a-1)=(\sqrt3-1)/2$，

$$
\kappa:=1-\frac1d-\frac{24a}{143}
=\frac{333-191\sqrt3}{286}
>\frac{29}{4290}>\frac1{200}.
\tag{12}
$$

这里使用严格有理界 $\sqrt3<26/15$，它由 $3<(26/15)^2$ 得到。
此外

$$
\frac1{2000}+\frac{24t^2}{143}
<\frac1{2000}+\frac1{4000000}<\frac1{1000}.
\tag{13}
$$

将 (11)–(13) 代入 (10)，得到明确的严格余量

$$
\begin{aligned}
\frac{aT}{T_0}-m
&>at^2\left(\kappa-\frac1{2000}-\frac{24t^2}{143}\right)\\
&>\frac{at^2}{250}>0.
\end{aligned}
\tag{14}
$$

特别地，$0<\rho\le m<aT/T_0$。
由 (3)，$M$ 的特征值恰为 $L(\widetilde c)$ 的全部非零特征值的倒数。
因而对每个 $j=2,\ldots,12$ 均有

$$
\lambda_j(c)=\alpha\lambda_j(\widetilde c)
\ge\frac{\alpha}{\rho}
>\frac{12T}{R_0}\frac{T_0}{aT}
=\frac{143}{aR_0}
=\frac{143(2-\sqrt3)}{R_0}.
$$

这同时完成全谱控制与实际电导的严格分离。

最后，旋转 $i\mapsto i+1$ 是 $C_{12}$ 的自同构，
并在十二条边上传递。因此任何自同构不变正电导必为常数 $\gamma>0$。
常电导时，上述 Fourier 基给出全部非零特征值
$\gamma(2-2\cos(k\pi/6))$，$1\le k\le11$，
由 (2) 得 $R(\gamma\mathbf1)=12T_0/\gamma=143/\gamma$。
可行性迫使 $\gamma=143/R_0$，最小正特征值就是
$\gamma(2-\sqrt3)$。它严格小于所构造的 $\lambda_2(c)$，
故没有不变可行向量能支配所有可行向量，无需假设最大值存在。

在单位电导 $C_{12}$ 上，相邻两顶点之间的两条串联支路电阻为 $1$ 与 $11$，
其并联电阻为 $11/12$，故相邻无序点对电阻和为 $11$，全点对和则为 $143$。
Menéndez-Conde，
[*Isoperimetric inequalities for eigenvalues of the Laplacian on cycles with fixed resistance metric*,
arXiv:1808.07976v2](https://arxiv.org/html/1808.07976v2)，§3 定义 2，
固定的正是前一种相邻点对之和。该文的约束与本定理的 $R(c)=R_0$ 不同。
Ghosh–Boyd–Saberi，§1 式 (2)，研究的则是固定 $\sum_i c_i=1$ 时最小化总电阻，
也不替代这里的约束。
经典伪逆与电学恒等式在此仅承担中间步骤；
(3)–(14) 给出了所指定十二边形向量的有限谱推导。证毕。

## 3. 尖锐问题的范围

**定义 3.1（任意阶环的尖锐问题）。** 对每个整数 $n\ge5$，
在带标号的 $C_n$ 上沿用计数测度 Laplacian，并令 $R_n$ 为所有
$\binom n2$ 个无序不同顶点对的有效电阻之和。定义

$$
\mathcal M_n=\sup_{c\in(0,\infty)^n}\lambda_2(L(c))R_n(c),\qquad
\mathcal A_n=\{c\in(0,\infty)^n:
\lambda_2(L(c))R_n(c)=\mathcal M_n\}.
$$

由电导缩放律，固定任意 $R_0>0$ 的尖锐上确界等于 $\mathcal M_n/R_0$，
达到性等价于 $\mathcal A_n\ne\varnothing$，全部等号情形由
$\mathcal A_n$ 及缩放描述。
定理 2.1 只给出严格下界 $\mathcal M_{12}>143(2-\sqrt3)$，
以及十二阶环上不变向量不可能达到全局最优的结论；
全部 $n\ge5$ 的 $\mathcal M_n$、达到或不达到，以及 $\mathcal A_n$ 的完整刻画仍待确定，
包括 $n=12$ 的精确最优值与达到性。

路径与一般图的相关结果有各自的图类限制。
[全路径固定电阻优化定理](FIEDLER_RESISTANCE_PATH_OPTIMIZER.md)，
定理 2.1、推论 3.1，处理的是 $P_n$。
[既有 $K_{2,3}$ 反例](../../../Blueprint/D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.md)
给出电阻 $23/3$ 下非不变向量的值 $48/23$ 与全部不变可行向量的值 $2$。
这些结果分别用于路径尖锐问题和一般图不变性命题；
本卷的有限十二阶环结论不重复这些图类的证明，也不把它们当作任意环的尖锐解。

## 追加锚（本行以下为增补区）
