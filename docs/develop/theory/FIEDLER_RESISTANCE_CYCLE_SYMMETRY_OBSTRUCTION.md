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

## 4. 任意阶实际环与电阻单纯形

**定义 4.1（全部独立正电导与边界坐标）。** 固定整数 $n\ge5$，
顶点标为 $1,\ldots,n$，边标为
$e_i=\{i,i+1\}$（$1\le i<n$）及 $e_0=\{n,1\}$。
每条边的电导 $c_i$ 独立遍历 $(0,\infty)$。
令 $L(c)$ 为普通计数测度 Laplacian，$R(c)$ 为全部无序不同顶点对的
有效电阻之和，并置

$$
H=\mathbf1^\perp\subset\mathbb R^n,\qquad
P=I-\frac1n\mathbf1\mathbf1^{\mathsf T},\qquad
r_i=\frac1{c_i},\quad s=\sum_{i=0}^{n-1}r_i,\quad p_i=\frac{r_i}{s}.
$$

这里顶点内积始终是 $\langle x,y\rangle=\sum_{j=1}^n x_jy_j$。
记

$$
\begin{aligned}
\Delta&=\{p\in[0,1]^n:\sum_i p_i=1\},&
\Delta^\circ&=\{p\in\Delta:p_i>0\ \text{对所有 }i\},\\
\mathcal V&=\{\varepsilon_0,\ldots,\varepsilon_{n-1}\},&
a_0&=0,\qquad a_i=P\sum_{j=1}^i\delta_j\quad(1\le i<n),\\
\bar a(p)&=\sum_i p_i a_i,&
M(p)&=\sum_i p_i a_i a_i^{\mathsf T}-\bar a(p)\bar a(p)^{\mathsf T}.
\end{aligned}
$$

$\delta_j$ 是顶点坐标向量，$\varepsilon_i$ 是边坐标向量；
$M(p)$ 作为 $H$ 上的算子。对 $p\in\Delta\setminus\mathcal V$，置

$$
T(p)=\operatorname{tr}_H M(p),\qquad
\rho(p)=\lambda_{\max}(M(p)|_H),\qquad
\Phi(p)=\frac{nT(p)}{\rho(p)}.
\tag{4.1}
$$

下文将证明该定义中的分母严格为正，并在内点证明
$\Phi(p)=\lambda_2(L(c))R(c)$。
令

$$
B_n=\sup_{c\in(0,\infty)^n}\lambda_2(L(c))R(c).
\tag{4.2}
$$

因此 $B_n$ 与定义 3.1 的 $\mathcal M_n$ 是同一个上确界；
记号 (4.2) 不指定它的精确数值。
Laplacian 和全点对电阻采用定义 1.1 所引
[Cruz Ortega–Menéndez-Conde，arXiv:2306.08187v1](https://arxiv.org/html/2306.08187v1)
§§2–4 的约定，顶点数改为 $n$。

**约定 4.2（完整路径定理的参数对应）。** 置

$$
s_0=s_n=0,\qquad s_i=\sqrt{i(n-i)},\qquad
 d_i=2s_i-s_{i-1}-s_{i+1},\qquad
A_n=\sum_{j=1}^n(s_j-s_{j-1})^2=\sum_{i=1}^{n-1}s_id_i.
$$

这里的 $s_i$ 带下标，与定义 4.1 的总边电阻 $s$ 不同。
直接使用[完整路径优化定理](https://github.com/the-omega-institute/trureturing/blob/48474969a064d134fa7bb9c78d5919922d48faf9/docs/develop/theory/FIEDLER_RESISTANCE_PATH_OPTIMIZER.md)
定理 2.1、推论 3.1 的全部结论：$d_i>0$，普通计数测度路径 $P_n$
的任意正电导满足 $\lambda_2R\le A_n$，等号恰为
$c_i=\kappa s_i/d_i$、$\kappa>0$；此时 $\lambda_2=\kappa$，
特征向量为 $(s_j-s_{j-1})_{j=1}^n$；固定 $R_0>0$ 时唯一最优电导为
$(A_n/R_0)s_i/d_i$。被引定理记作 $C_n$ 的常数在这里记作 $A_n$。
删去实际环的 $e_0$ 后，顶点仍为 $1,\ldots,n$，每个顶点质量仍为 $1$，
第 $i$ 条路径边就是 $e_i$，所以这是真正的参数对应。
含零边电阻的边界不直接当作普通单位质量的缩点路径。

## 5. 顶点退化的全部方向

**定理 5.1（顶点附近的一致路径界）。** 对每个 $n\ge5$，
$\Phi$ 在 $\Delta\setminus\mathcal V$ 上连续，在 $\Delta^\circ$ 上等于
实际环的 $\lambda_2R$。固定任一顶点 $\varepsilon_\ell$，
令 $q\in\Delta$、$q_\ell=0$，并定义

$$
K_\ell(q)=\sum_{i\ne\ell}q_i(a_i-a_\ell)(a_i-a_\ell)^{\mathsf T},\qquad
\Psi_\ell(q)=\frac{n\operatorname{tr}K_\ell(q)}{\lambda_{\max}(K_\ell(q))}.
$$

则 $\max_{q_\ell=0}\Psi_\ell(q)=A_n$，且对所有这样的 $q$ 以及
所有 $0<\epsilon<1$，均有

$$
(1-\epsilon)\Psi_\ell(q)
\le\Phi\bigl((1-\epsilon)\varepsilon_\ell+\epsilon q\bigr)
\le\frac{\Psi_\ell(q)}{1-\epsilon},
\tag{5.1}
$$

从而

$$
\left|\Phi\bigl((1-\epsilon)\varepsilon_\ell+\epsilon q\bigr)
-\Psi_\ell(q)\right|\le\frac{A_n\epsilon}{1-\epsilon}.
\tag{5.2}
$$

特别地，顶点逼近的上确界极限恰为

$$
\lim_{\delta\downarrow0}\,
\sup\{\Phi(p):p\in\Delta^\circ,\ 0<1-p_\ell\le\delta\}=A_n.
\tag{5.3}
$$

式 (5.2) 对方向 $q$ 一致，允许 $q$ 随 $\epsilon$ 任意变化、趋于任意面，
以及各坐标具有任意不同的衰减尺度。

证明。先验证 (4.1) 与实际模型的关系。把 $e_i$ 定向为 $i\to i+1$，
$e_0$ 定向为 $n\to1$，令关联矩阵为 $D$。
对 $h\in H$，所有满足 $Dz=h$ 的流都写成

$$
z_i=t+\sum_{j=1}^i h_j=t+\langle a_i,h\rangle\quad(1\le i<n),
\qquad z_0=t.
$$

采用经典的最小耗散原理，或直接令
$u=L(c)^+h$、$z_*=\operatorname{diag}(c_i)D^{\mathsf T}u$：
$Dz_*=h$，且 $\sum_i r_i(z_*)_i=\mathbf1^{\mathsf T}D^{\mathsf T}u=0$。
于是 $z_*$ 与所有常循环流在电阻内积下正交，得到

$$
\begin{aligned}
h^{\mathsf T}L(c)^+h
&=\min_t\sum_i r_i\bigl(t+\langle a_i,h\rangle\bigr)^2\\
&=s\left[\sum_i p_i\langle a_i,h\rangle^2
-\left(\sum_i p_i\langle a_i,h\rangle\right)^2\right]
=s\,h^{\mathsf T}M(p)h.
\end{aligned}
\tag{5.4}
$$

这里最小点为 $t=-\sum_i p_i\langle a_i,h\rangle$。
这也将第 2 节式 (1) 的流计算直接接到任意 $n$ 的实际边上。
全点对恒等式
$\sum_{i<j}(\delta_i-\delta_j)(\delta_i-\delta_j)^{\mathsf T}=nP$
给出 $R(c)=n\operatorname{tr}L(c)^+$。
电学伪逆和迹公式的经典出处仍是
[Ghosh–Boyd–Saberi，DOI:10.1137/050645452](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf)，
§§2.4–2.5，式 (8)、(13)–(15)；这里只使用其电学恒等式。
由 (5.4) 和谱分解，内点上有

$$
L(c)^+|_H=sM(p),\qquad
\lambda_2(L(c))=\frac1{s\rho(p)},\qquad
R(c)=nsT(p),\qquad \lambda_2R=\Phi(p).
\tag{5.5}
$$

向量 $a_1,\ldots,a_{n-1}$ 线性无关：若
$\sum_{i=1}^{n-1}\alpha_i a_i=0$，其未投影的累积向量为常数，
但第 $n$ 坐标为零，故各坐标均为零，依次相减给出所有 $\alpha_i=0$。
因此 $a_0,\ldots,a_{n-1}$ 仿射无关，且

$$
M(p)=\sum_i p_i(a_i-\bar a)(a_i-\bar a)^{\mathsf T}
\tag{5.6}
$$

在支撑大小为 $k$ 的点上秩恰为 $k-1$。
事实上二次型为零当且仅当该向量与全部支撑点之差正交。
非顶点时 $k\ge2$，故 $T,\rho>0$；连续性由矩阵元素和最大特征值的
连续性得到。内点时 $M$ 在 $H$ 上正定。

先取 $\ell=0$。删边后的普通路径若有正边电阻 $q_i$，
其唯一流为 $z_i=\langle a_i,h\rangle$，同一能量计算给出
$L_{P_n}^+|_H=K_0(q)$。
因此约定 4.2 的完整路径定理直接给出 $\Psi_0(q)\le A_n$，
并在 $q_i$ 与 $d_i/s_i$ 成比例时取等号。
若一些 $q_i=0$，以正 $q$ 逼近：由于

$$
\|a_i\|^2=\frac{i(n-i)}n\ge\frac{n-1}n,\qquad
\operatorname{tr}K_0(q)\ge\frac{n-1}n,
$$

分母在整个闭方向单纯形上不为零，连续延拓保持该上界。
这一步没有以单位质量的缩点路径替换原来的 $n$ 个顶点。
对一般 $\ell$，循环重标号给出完全相同的路径、电学恒等式和范数界。

令 $v=\sum_{i\ne\ell}q_i(a_i-a_\ell)$、$K=K_\ell(q)$。
将 (5.6) 在 $p=(1-\epsilon)\varepsilon_\ell+\epsilon q$ 处展开，得到

$$
M(p)=\epsilon(K-\epsilon vv^{\mathsf T}),\qquad
vv^{\mathsf T}\preceq K.
\tag{5.7}
$$

后一不等式是标量 Cauchy–Schwarz 不等式
$(\sum_i q_i\langle a_i-a_\ell,h\rangle)^2
\le\sum_i q_i\langle a_i-a_\ell,h\rangle^2$。
所以

$$
(1-\epsilon)K\preceq K-\epsilon vv^{\mathsf T}\preceq K.
$$

对迹和最大特征值分别使用这些序界，即得 (5.1)，继而得 (5.2)。
上界对全部闭方向一致；下界取上述严格正的路径最优方向，令
$\epsilon\downarrow0$，便证明 (5.3)。∎

## 6. 路径值的严格超越与每个真面的排除

**定理 6.1（实际正环严格超过完整路径常数）。** 对每个整数 $n\ge5$，
存在全部 $n$ 条边电导均有限且严格为正的实际 $C_n$，满足
$\lambda_2R>A_n$。因此 $B_n>A_n$。

证明。仅调用约定 4.2 的完整路径最优点，取
$c_i=s_i/d_i$、$1\le i<n$。
令 $K=L_{P_n}^+|_H$、$T=\operatorname{tr}K$、
$r_i=d_i/s_i$。被引定理给出

$$
\lambda_{\max}(K)=1,\qquad T=\frac{A_n}{n},\qquad
u_j=\frac{s_j-s_{j-1}}{\sqrt{A_n}},\qquad K\nu=\nu,
\quad\|\nu\|=1.
$$

此最大特征值单重：路径 Laplacian 的任一特征向量由其第一个坐标
通过首行及后继行唯一递推确定，若第一个坐标为零便全为零；
实对称性使几何重数与代数重数相同。

令 $b=\delta_1-\delta_n$、$v=Kb$、$\ell=b^{\mathsf T}Kb=\sum_i r_i$。
给缺失的实际边 $e_0$ 添加电导 $h>0$，在 $H$ 上直接相乘验证逆矩阵为

$$
K_h=(L_{P_n}|_H+hbb^{\mathsf T})^{-1}
=K-\tau vv^{\mathsf T},\qquad
\tau=\frac{h}{1+h\ell}>0.
\tag{6.1}
$$

为计算严格增益，$\langle a_i,b\rangle=1$ 给出
$v=\sum_i r_i a_i$，且

$$
\langle\nu,a_i\rangle=\frac{s_i}{\sqrt{A_n}},\qquad
\langle\nu,v\rangle=\frac{\sum_i d_i}{\sqrt{A_n}}
=\frac{2\sqrt{n-1}}{\sqrt{A_n}}.
\tag{6.2}
$$

对 $1\le i\le j<n$，

$$
\langle a_i,a_j\rangle=\frac{i(n-j)}n
\le\frac{s_is_j}{n},
$$

其中 $i<j$ 时严格，因为 $i(n-j)<j(n-i)$。
所有 $r_i>0$，且有至少两个不同的路径边指标，所以

$$
\|v\|^2=\sum_{i,j}r_ir_j\langle a_i,a_j\rangle
<\frac1n\left(\sum_i r_i s_i\right)^2
=\frac{4(n-1)}n.
\tag{6.3}
$$

使用有限维简单特征值的一阶展开，

$$
\lambda_{\max}(K-\tau vv^{\mathsf T})
=1-\tau\langle\nu,v\rangle^2+O(\tau^2).
\tag{6.4}
$$

这里的余项可直接由谱隙得到：在
$\mathbb R\nu\oplus\nu^\perp$ 中，右下块的最大特征值与 $1$ 有严格间隙，
交叉块为 $O(\tau)$。Rayleigh 下界取 $\nu$；上界对交叉项配方，
便与左上标量相差 $O(\tau^2)$。
于是 (5.5)、(6.1)–(6.4) 给出

$$
\begin{aligned}
\lambda_2(L_{P_n}+hbb^{\mathsf T})R
&=\frac{n(T-\tau\|v\|^2)}{\lambda_{\max}(K-\tau vv^{\mathsf T})}\\
&=A_n+\tau\bigl(4(n-1)-n\|v\|^2\bigr)+O(\tau^2)>A_n
\end{aligned}
$$

对所有充分小的 $h>0$ 成立。式 (6.3) 保证一阶系数严格为正，
因此选择的是有限正电导，并非只在删边极限取值。∎

**定理 6.2（任意非顶点真面的严格内点支配）。** 固定 $n\ge5$。
对每个 $p\in\partial\Delta\setminus\mathcal V$，存在
$p'\in\Delta^\circ$ 使 $\Phi(p')>\Phi(p)$。
此结论涵盖每个真面的全部非顶点，包括任意数目的零坐标，
并在原来的 $n$ 个计数质量上成立。

证明。令 $S_p=\{i:p_i>0\}$，$k=|S_p|\ge2$，并置

$$
W=\operatorname{span}\{a_i-a_l:i\in S_p\}\subset H
$$

其中 $l\in S_p$。式 (5.6) 表明 $M(p)$ 的像恰为 $W$，
在 $W^\perp$ 上为零，在 $W$ 上正定。
至少有一个零坐标，故可在循环边指标上选取相邻的两个支撑指标 $l,r$，
它们之间沿选定方向有 $m-1\ge1$ 个零坐标。
因支撑至少有两个，$2\le m\le n-1$。
在该间隙任选距 $l$ 为 $j$ 的指标 $k_0$，$1\le j<m$，置

$$
\theta=\frac jm,\qquad
 d=a_r-a_l,\qquad
 w=a_{k_0}-(1-\theta)a_l-\theta a_r,\qquad
 z=(1-\theta)a_l+\theta a_r-\bar a(p).
\tag{6.5}
$$

跨过循环指标 $0$ 时，用 $a_n=a_0$ 和
$a_i-a_{i-1}=P\delta_i$（顶点指标也按周期解释）计算。
若 $I$ 是间隙对应的 $m$ 个原始顶点，$J$ 是其中前 $j$ 个，则

$$
d=P\mathbf1_I,\qquad
w=\mathbf1_J-\frac jm\mathbf1_I,\qquad
\|w\|^2=\frac{j(m-j)}m=:b_0>0,\qquad
\|d\|^2=\frac{m(n-m)}n.
\tag{6.6}
$$

每个 $a_i-a_l$、$i\in S_p$ 在 $I$ 的全部坐标上取同一数值，
所以 $w\perp W$。同时 $d,z\in W$。
这一步保留了每个原始顶点的内积；若以块常数 $x_i=y_I$ 表示，
范数贡献是 $|I|y_I^2$，不是 $y_I^2$。

取

$$
p(t)=p+t\bigl(\varepsilon_{k_0}-(1-\theta)\varepsilon_l
-\theta\varepsilon_r\bigr).
$$

对充分小的 $t>0$，它仍在 $\Delta$，因为只减去两个严格正的支撑坐标。
其均值变化为 $tw$。逐项展开协方差，得到精确恒等式

$$
M(p(t))=M(p)-t\theta(1-\theta)dd^{\mathsf T}
+t(zw^{\mathsf T}+wz^{\mathsf T})+t(1-t)ww^{\mathsf T}.
\tag{6.7}
$$

因此，无论 $\rho=\rho(p)$ 的重数是多少，$W$ 上的整个压缩都不增加。
另一方面，取迹并使用 $w\perp W$，得到

$$
T(p(t))=T(p)+a_0t-b_0t^2,\qquad
 a_0=b_0-\theta(1-\theta)\|d\|^2=\frac{j(m-j)}n>0.
\tag{6.8}
$$

以下控制整个最大特征空间，而非单独选择一个特征向量。
令 $T=T(p)$，并取 $0<t<1$ 足够小，使 $tb_0\le\rho/2$。
在 $W\oplus W^\perp$ 中，(6.7) 对任意向量 $(x,y)$ 给出

$$
\begin{aligned}
\langle M(p(t))(x,y),(x,y)\rangle
&\le\rho\|x\|^2+2t\|z\|\|w\|\|x\|\|y\|
+\frac\rho2\|y\|^2\\
&\le(\rho+C t^2)\|x\|^2+\rho\|y\|^2,\qquad
 C=\frac{2\|z\|^2b_0}{\rho}.
\end{aligned}
$$

最后一步使用 $2AB\le 2A^2/\rho+\rho B^2/2$。
于是 $\rho(p(t))\le\rho+Ct^2$，并由 (6.8) 得到

$$
\Phi(p(t))\ge\frac{n(T+a_0t-b_0t^2)}{\rho+Ct^2}
>\frac{nT}{\rho}=\Phi(p)
\tag{6.9}
$$

只要再取 $t<\rho a_0/(\rho b_0+TC)$。
所有限制都可与两个支撑坐标的正性限制同时满足。
若 $p(t)$ 还有零坐标，令
$p'=(1-\eta)p(t)+\eta(1/n,\ldots,1/n)$；
定理 5.1 的非顶点连续性保证对充分小的 $\eta>0$ 仍保留 (6.9) 的严格性。
此时 $p'\in\Delta^\circ$，对应同一实际 $n$ 顶点环上的有限正电导
$c_i'=1/p_i'$。由 (5.5)，其乘积恰为 $\Phi(p')$。∎

## 7. 全边界排除后的达到性与定量分离

**定理 7.1（有限正最大点与严格双界）。** 对每个整数 $n\ge5$，
$B_n$ 在实际标号环的有限严格正电导处达到，并且

$$
A_n<B_n<n(n-1).
\tag{7.1}
$$

每个 $R_0>0$ 都满足

$$
\max_{c\in(0,\infty)^n,\ R(c)=R_0}\lambda_2(L(c))=\frac{B_n}{R_0}.
\tag{7.2}
$$

证明。由 (5.5) 和 (4.2)，$B_n=\sup_{p\in\Delta^\circ}\Phi(p)$。
$M(p)$ 在 $H$ 上正定，维数为 $n-1$，所以
$\Phi(p)\le n(n-1)$，从而上确界有限。
定理 6.1 已经给出 $B_n>A_n$。

取 $\Phi(p^{(k)})\to B_n$ 的内点序列，先在闭单纯形内取一个收敛子列，
记其极限为 $p^*$。若 $p^*$ 是顶点，定理 5.1 的一致界给出
$\limsup_k\Phi(p^{(k)})\le A_n<B_n$，矛盾。
若 $p^*\in\partial\Delta\setminus\mathcal V$，连续性给出
$\Phi(p^*)=B_n$，而定理 6.2 给出实际内点 $p'$ 满足
$\Phi(p')>B_n$，也矛盾。
已经排除全部边界，故 $p^*\in\Delta^\circ$，连续性才给出
$\Phi(p^*)=B_n$，这证明达到性。

若某一内点有 $\Phi(p)=n(n-1)$，迹与最大特征值之比取等号迫使
$M(p)=\rho(p)I_H$。式 (5.4) 于是给出

$$
L(c)=\frac1{s\rho(p)}P.
$$

但右边任意两个不同顶点间的矩阵元都是负数，而 $n\ge5$ 的实际环
存在非相邻顶点，它们之间的 Laplacian 矩阵元为零，矛盾。
将这一严格性应用于刚证明存在的最大点，便得 (7.1) 的严格上界。

最后任取内点 $p$，令 $\widehat c_i=1/p_i$。
此时总边电阻为 $1$，由 (5.5) 得
$R(\widehat c)=nT(p)$。定义

$$
c_i^{(R_0)}=\frac{nT(p)}{R_0p_i}.
\tag{7.3}
$$

缩放律给出

$$
R(c^{(R_0)})=R_0,\qquad
\lambda_2(L(c^{(R_0)}))=\frac{\Phi(p)}{R_0}.
$$

取 $p=p^*$ 就达到 (7.2)；任一其它可行电导的乘积不超过 $B_n$，
所以 (7.2) 的上界也对全部独立正电导成立。∎

**定理 7.2（全部近最大点的一致内部分离）。** 对每个固定整数 $n\ge5$，
存在仅依赖于 $n$ 的 $\epsilon_n>0$ 和 $\delta_n>0$，使

$$
p\in\Delta^\circ,\quad \Phi(p)\ge B_n-\epsilon_n
\quad\Longrightarrow\quad \min_i p_i\ge\delta_n.
\tag{7.4}
$$

尤其所有趋于 $B_n$ 的序列最终都落入同一个开单纯形内的紧子集。
任意固定 $R_0>0$ 时，这些点经 (7.3) 对应的电导也落入
$(0,\infty)^n$ 的一个紧子集。

证明。定义实际边界水平

$$
\Gamma_n=\max\left\{A_n,\,
\sup_{p\in\partial\Delta\setminus\mathcal V}\Phi(p)\right\}.
$$

首先证明 $\Gamma_n<B_n$。每个非顶点边界点都被定理 6.2 的内点严格支配，
故其值严格小于 $B_n$。若这些边界值的上确界仍为 $B_n$，
取逼近它的边界序列并在闭单纯形取收敛子列。
极限非顶点时，连续性会给出一个值为 $B_n$ 的边界点，矛盾；
极限为顶点时，(5.1) 对闭方向也成立，给出上极限不超过
$A_n<B_n$，仍矛盾。结合 $A_n<B_n$，得所需严格间隙。

令 $\epsilon_n=(B_n-\Gamma_n)/4>0$。
存在 $\delta_n>0$ 使

$$
p\in\Delta^\circ,\quad\min_i p_i<\delta_n
\quad\Longrightarrow\quad\Phi(p)\le\Gamma_n+\epsilon_n.
\tag{7.5}
$$

否则可选取 $\min_i p_i\to0$ 而
$\Phi(p)>\Gamma_n+\epsilon_n$ 的内点序列。其收敛子列的极限在边界；
非顶点极限由连续性否定这一严格下界，顶点极限由 (5.1) 否定它。
这证明 (7.5)，并因
$\Gamma_n+\epsilon_n=B_n-3\epsilon_n<B_n-\epsilon_n$
得到 (7.4)。必要时减小 $\delta_n$，可使 $\delta_n<1/n$。
该论证证明分离常数存在，没有指定未经推导的数值。

集合 $\{p\in\Delta:p_i\ge\delta_n\ \text{对所有 }i\}$ 是开单纯形内的紧集。
其上 $T(p)$ 连续且严格为正，(7.3) 因而是取值于有限正电导的连续映射，
像亦紧。这同时排除固定总电阻下近最大点的任一电导逃逸。∎

## 8. 内点最大值的必要重数与尚未确定的精确问题

**定理 8.1（任何内点局部最大值的 Fiedler 重数恰为二）。** 固定 $n\ge5$。
若实际正环的电导 $c$ 是尺度不变量 $\lambda_2R$ 的局部最大点，
或是任意固定 $R_0>0$ 水平上 $\lambda_2$ 的局部最大点，则

$$
\lambda_2(L(c))=\lambda_3(L(c))<\lambda_4(L(c)).
\tag{8.1}
$$

因此 (8.1) 适用于定理 7.1 的每一个全局最大点。

证明。先在 $p\in\Delta^\circ$ 上证明 $\rho(p)$ 在 $\Phi$ 的局部最大点
不能单重。暂设它单重，取单位最大特征向量 $u\in H$，并记

$$
v_i=a_i-\bar a(p),\qquad h_i=\langle u,v_i\rangle,\qquad
T=T(p),\quad\rho=\rho(p),\quad\beta=\frac T\rho.
$$

若 $\xi\in\mathbb R^n$ 满足 $\sum_i\xi_i=0$，协方差的一阶变化为
$\sum_i\xi_i v_i v_i^{\mathsf T}$。
简单特征值的 Rayleigh 展开（与 (6.4) 的谱隙配方论证相同）给出

$$
D\Phi(p)[\xi]=\frac n\rho
\sum_i\xi_i\bigl(\|v_i\|^2-\beta h_i^2\bigr).
\tag{8.2}
$$

局部最大点允许所有这样的双向变化，故括号对 $i$ 为常数；
其 $p$ 加权和是 $T-\beta\rho=0$，所以

$$
\|v_i\|^2=\beta h_i^2\qquad\text{对所有 }i.
\tag{8.3}
$$

仿射无关性和 $p_i>0$ 保证 $\bar a(p)\ne a_i$，所以每个 $v_i\ne0$，
继而每个 $h_i\ne0$。定义

$$
S=\sum_i\frac{p_i}{h_i},\qquad
w=\sum_i\frac{p_i v_i}{h_i},\qquad
C=\sum_i\frac{p_i}{h_i}v_i v_i^{\mathsf T}.
$$

由 $\sum_i p_iv_i=0$、$\sum_i p_i h_i=0$ 以及 (8.3)，有

$$
\langle u,w\rangle=1,\qquad Cu=0,\qquad\operatorname{tr}C=0,
\qquad \|w\|^2<\sum_i p_i\left\|\frac{v_i}{h_i}\right\|^2=\beta.
\tag{8.4}
$$

最后的不等式严格：平方范数的加权凸性取等号要求所有 $v_i/h_i$ 相同，
这会使全部 $v_i$ 共线，与 $n$ 个 $a_i$ 在 $n-1\ge2$ 维空间中
仿射无关相矛盾。

对充分小的正负 $t$，令

$$
p_i(t)=\frac{p_i(1+t/h_i)}{1+tS},\qquad d(t)=1+tS.
$$

这些坐标严格为正、总和为 $1$，并在 $t=0$ 回到 $p$。
相对于旧均值，新均值为 $tw/d(t)$，故有精确公式

$$
M(p(t))=\frac{M(p)+tC}{d(t)}
-\frac{t^2}{d(t)^2}ww^{\mathsf T},\qquad
T(p(t))=\frac{T}{d(t)}-\frac{t^2}{d(t)^2}\|w\|^2.
\tag{8.5}
$$

因 $Cu=0$，第一项在 $\mathbb Ru\oplus u^\perp$ 上是块对角的，
$u$ 方向特征值为 $\rho/d(t)$。
单重性保证它与另一块的最大特征值保持一个固定正谱隙。
第二项的交叉块为 $O(t^2)$，且其 $u,u$ 元为 $-t^2/d(t)^2$，
因为 $\langle u,w\rangle=1$。与 (6.4) 相同的配方上界和取 $u$ 的下界给出

$$
\rho(p(t))=\frac{\rho}{d(t)}-\frac{t^2}{d(t)^2}+O(t^4).
$$

代回 (8.5)，得到

$$
\Phi(p(t))=n\beta+
\frac n\rho\bigl(\beta-\|w\|^2\bigr)t^2+O(t^3)>\Phi(p)
$$

对所有充分小的非零 $t$ 成立，违背局部最大性。
这证明最大特征值必须至少二重；整个论证没有假定其它特征值单重。

由 (5.5)，$M(p)$ 的最大特征空间与 $L(c)$ 的 Fiedler 特征空间相同。
而实际正环上任意特征值 $\lambda$ 的特征向量满足

$$
c_i x_{i+1}=(c_{i-1}+c_i-\lambda)x_i-c_{i-1}x_{i-1},
$$

顶点和边指标按周期解释。因 $c_i>0$，两个相邻坐标唯一确定其余坐标，
所以每个特征空间维数至多为 $2$。
实对称性使代数重数也至多为 $2$，故 Fiedler 重数恰为 $2$，即 (8.1)。

最后，$c\mapsto(p,s)$ 是正电导空间到
$\Delta^\circ\times(0,\infty)$ 的光滑双射，逆为 $c_i=1/(sp_i)$。
$\lambda_2R$ 只依赖 $p$。在 $R=R_0$ 水平上，式 (5.5) 将 $s$ 唯一确定为
$R_0/(nT(p))$，式 (7.3) 给出双向连续的参数化，
其目标为 $\Phi(p)/R_0$。因此两种局部最大性都归于刚证明的情形。∎

**定义 8.2（剩余的精确优化问题）。** 对每个 $n\ge5$，令

$$
\mathcal P_n=\{p\in\Delta^\circ:\Phi(p)=B_n\}.
$$

定理 7.1–7.2 确定 $\mathcal P_n$ 非空且在开单纯形内紧，
定理 8.1 给出其每一点必须满足的二重 Fiedler 条件。
待确定的仍是 $B_n$ 的精确值及 $\mathcal P_n$ 的完整刻画；
二重条件不作为局部或全局最优的充分条件。
固定 $R_0$ 的完整等号集合由 (7.3) 作用于 $\mathcal P_n$ 给出，
这一定义不评价该集合或 $B_n$。
对 $n=12$，定理 2.1 的有限向量及严格不变性障碍仍成立，
并与本节最大点存在及必要重数结论同时适用。
[Menéndez-Conde，arXiv:1808.07976v2](https://arxiv.org/html/1808.07976v2)
§3 定义 2 的相邻点对电阻约束，以及 Ghosh–Boyd–Saberi §1 式 (2) 的
固定电导预算，均不同于本节的全点对电阻约束。

## 追加锚（本行以下为增补区）

## 9. Fourier 矩与均匀值的严格比较

**定义 9.1（全部正竞争者的 Fourier 坐标）。** 固定整数 $n\ge5$。
沿用定义 4.1 的实际环、计数内积、开单纯形与全部无序点对电阻，
并直接使用定理 5.1–8.1 的全部结论。置
$\theta=2\pi/n$、$z=e^{\mathrm i\theta}$，所有 Fourier 下标按模 $n$ 解释，并定义

$$
\begin{aligned}
d_k&=1-z^{-k},&
\mu_k&=|d_k|^{-2}=\frac1{4\sin^2(\pi k/n)}
 &&(1\le k<n),\\
q_k(p)&=\sum_{i=0}^{n-1}p_i z^{ki},&
q_0&=1,&q_{n-k}&=\overline q_k,\\
\tau_n&=\frac1n\sum_{k=1}^{n-1}\mu_k=\frac{n^2-1}{12n},&
\rho_n&=\frac{\mu_1}{n},&
T_n&=\tau_n-2\rho_n,\\
E_n(p)&=\frac1n\sum_{k=2}^{n-2}\mu_k|q_k(p)|^2,&
\beta_n&=\frac{\tau_n}{\rho_n},&
U_n&=n\beta_n.
\end{aligned} \tag{9.1}
$$

这里 $E_n$ 排除第一模及其共轭模；$T_n>0$ 是均匀点的互补谱迹。
经典有限三角和可由 $g(X)=(X^n-1)/(X-1)$ 在 $X=1$ 的两次对数微分得到：
对 $\zeta^n=1,\zeta\ne1$，
$\sum(1-\zeta)^{-1}=(n-1)/2$，
$\sum(1-\zeta)^{-2}=(n-1)^2/4-(n-1)(n-2)/3$；
再用 $\mu_k=(1-z^k)^{-1}-(1-z^k)^{-2}$ 即得 (9.1) 的 $\tau_n$。

**定理 9.2（精确矩比较及尖锐均匀值区域）。** 对每个 $p\in\Delta^\circ$，
在顶点 Fourier 基 $f_k(j)=n^{-1/2}z^{kj}$ 的非恒定部分中，有

$$
M(p)_{km}=\frac{q_{m-k}-\overline q_kq_m}
 {n\,\overline d_kd_m}\quad(1\le k,m<n),\qquad
T(p)=\tau_n-2\rho_n|q_1|^2-E_n(p). \tag{9.2}
$$

特别地，令 $a=|q_1|^2$、$b=|q_2-q_1^2|$，则

$$
\rho(p)\ge\rho_n(1-a+b),\qquad
\Phi(p)\le
\frac{n\,[\,\tau_n-2\rho_na-E_n(p)\,]}{\rho_n(1-a+b)}. \tag{9.3}
$$

在完整区域 $E_n(p)\ge T_n|q_1(p)|^2$ 上，

$$
\Phi(p)\le U_n=\frac{n(n^2-1)}3\sin^2\frac{\pi}{n}, \tag{9.4}
$$

且等号当且仅当 $p_i=1/n$ 对每条边成立。

证明。式 (5.4) 的最小流能量在 Fourier 基中给出 (9.2)：
关联矩阵在第 $k$ 模上的乘子是 $d_k$，
$\langle f_k,\operatorname{diag}(p)f_m\rangle=q_{m-k}/n$，
减去循环流均值的秩一项为 $\overline q_kq_m/n$。
取迹即得第二式。对指标 $\{1,n-1\}$ 的二阶主压缩作对角酉共轭后，
其两个特征值为 $\rho_n(1-a\pm b)$，所以 Rayleigh 原理给出 (9.3)。
正性使 $|q_1|<1$，所有分母均为正。

若 $E_n\ge(\tau_n-2\rho_n)a$，则 $T(p)\le\tau_n(1-a)$，
而 $\rho(p)\ge\rho_n(1-a)$，得到 (9.4)。
若取等号且 $q_1=0$，则 $E_n=0$，所有非恒定 Fourier 系数均为零，
Fourier 反演给出均匀 $p$。
若取等号且 $q_1\ne0$，Rayleigh 等号迫使 $f_1$ 为最大特征向量。
(9.2) 的 $(2,1)$ 元为零，给出
$\overline q_1=\overline q_2q_1$，从而 $|q_2|=1$。
严格正的概率对至少两个不同的 $z^{2i}$ 赋正质量，故三角不等式严格，
不可能有 $|q_2|=1$。均匀点直接取等号。∎

**推论 9.3（非恒等旋转与相干矩障碍）。** 对每个 $n\ge5$，
任何具有非恒等旋转对称性的非均匀正电导，在同一总电阻水平上
都被均匀电导严格支配。任何满足 $\Phi(p)>U_n$ 的正竞争者必须满足

$$
q_1\ne0,\qquad
E_n(p)+\tau_n|q_2-q_1^2|<T_n|q_1|^2. \tag{9.5}
$$

此外其全部矩必须共同满足

$$
\left(q_{m-k}-\overline q_kq_m\right)_{1\le k,m<n}\succ0,\qquad
p_i=\frac1n\sum_{k=0}^{n-1}q_kz^{-ki}>0. \tag{9.6}
$$

因此独立指定各模的大小不能替代同一个正概率向量的相干矩条件。

证明。旋转 $i\mapsto i+d$ 不变给出 $q_1=z^{-d}q_1$，
非恒等性使 $q_1=0$；非均匀性使 $E_n>0$。
于是 $T<\tau_n$、$\rho\ge\rho_n$，严格低于 $U_n$。
由 (9.3)，严格改进又要求
$\tau_n-2\rho_na-E_n>\tau_n(1-a+b)$，这恰是 (9.5)。
(9.6) 的矩阵是非恒定 Fourier 函数在 $p$ 下的协方差 Gram 矩阵；
严格正的 $p$ 使其正定：若线性组合的方差为零，它在全部 $n$ 个点为常数，
但其 Fourier 常数系数为零，故组合为零。第二式是 Fourier 反演。
式 (7.3) 保持比较并把它送到任意 $R_0>0$。∎

## 10. 每个正双 Fiedler 点的解析正则性与完整曲率条件

**定义 10.1（压缩、切向量及互补谱）。** 令
$\mathscr D_n=\{p\in\Delta^\circ:\rho(p)\text{ 恰二重}\}$。
在 $p\in\mathscr D_n$ 处，记 $E=\ker(M-\rho I)$、$\Pi=P_E$、
$Q=I_H-\Pi$、$v_i=a_i-\bar a(p)$、$\beta=T/\rho$。
对 $\sum_i\xi_i=0$ 定义

$$
w_\xi=\sum_i\xi_iv_i,\quad C_\xi=\sum_i\xi_iv_iv_i^{\mathsf T},\quad
\mathcal R_p\xi=\operatorname{tf}_E(\Pi C_\xi\Pi),\quad
\operatorname{tf}_E A=A-\tfrac12\operatorname{tr}_E(A)I_E. \tag{10.1}
$$

互补逆 $G=Q(\rho I_Q-QMQ)^{-1}Q$ 只在 $QH$ 上取逆，
在 $E$ 上为零。所有互补特征值都严格小于 $\rho$，所以该定义合法。

**引理 10.2（实际环的秩二横截性）。** 对每个 $p\in\mathscr D_n$，
$\mathcal R_p$ 满射到二维空间 $\operatorname{Sym}_0(E)$。

证明。取 $E$ 的正交基 $u,v$，并置
$F_i=(\langle u,v_i\rangle,\langle v,v_i\rangle)^{\mathsf T}$。
因为 $M=L(1/p)^+|_H$，对任一 $x\in E$，
$\rho\,p_i^{-1}(x_i-x_{i+1})=\langle x,v_i\rangle$，
而 $\langle x,v_i-v_{i-1}\rangle=x_i$。因此

$$
F_{i+1}+F_{i-1}=(2-p_i/\rho)F_i,\qquad
\sum_i p_iF_iF_i^{\mathsf T}=\rho I_2. \tag{10.2}
$$

递推使 $D_i=\det(F_i,F_{i+1})$ 与 $i$ 无关。
若该常数为零，可选非零线性组合同时消去两个相邻的 $F_i$ 分量；
二阶递推使所有分量为零，继而 $u,v$ 的同一组合为零，矛盾。
所以每两个相邻 $F_i$ 线性无关。

若满射失败，存在非零迹零对称 $A$ 使
$F_i^{\mathsf T}AF_i$ 对 $i$ 为常数。按 $p$ 加权和该常数是
$\rho\operatorname{tr}A=0$。非零迹零实对称二阶矩阵的零二次型集合
恰为两条不同直线。相邻 $F_i$ 必交替落在这两条直线上。
(10.2) 左边落在与 $F_i$ 不同的直线上，故 $2-p_i/\rho=0$ 对每个 $i$ 成立。
于是 $p_i=1/n$ 且 $\rho=1/(2n)$；但均匀点的实际最大特征值为
$[4n\sin^2(\pi/n)]^{-1}>1/(2n)$，因为 $n>4$，矛盾。∎

**定理 10.3（完整正双 Fiedler 集的局部维数）。** 在每个正电导环
$\lambda_2=\lambda_3<\lambda_4$ 的附近，实际双 Fiedler 集是实解析子流形：
共同特征值自由时维数为 $n-2$，归一化为 $\lambda_2=\lambda_3=1$ 时维数为 $n-3$。
在 $p$ 坐标中，其切空间恰为 $\ker\mathcal R_p$。

证明。用隔离顶层二阶谱簇的围道 resolvent 定义解析谱投影；
把固定的 $E$ 投影到该谱簇并作 Gram 矩阵的解析逆平方根，得到解析正交框架。
该框架中的二阶对称矩阵 $K(p')$ 解析，
双重条件恰是 $\operatorname{tf}K(p')=0$。
在 $p$ 处其微分为 $\mathcal R_p$，故引理 10.2 与解析隐函数定理
给出开单纯形内维数 $(n-1)-2=n-3$，切空间为所述核。
原电导与 $(p,s)$ 解析双射；自由 $s>0$ 增加一维。
共同 Laplacian 特征值为 $(s\rho(p))^{-1}$，等于 $1$ 时唯一确定
$s=1/\rho(p)$。互补谱隙和全部电导正性在邻域内保持。∎

**定理 10.4（唯一严格正乘子与全部互补谱的必要曲率）。** 在任何内点局部极大值
$p$ 处，定理 8.1 给出 $p\in\mathscr D_n$。存在唯一的 $W\in\operatorname{Sym}(E)$ 满足

$$
W\succ0,\qquad \operatorname{tr}_E W=1,\qquad
\|v_i\|^2=\beta\,(\Pi v_i)^{\mathsf T}W(\Pi v_i)\quad\text{对全部 }i. \tag{10.3}
$$

对每个 $\xi\in\ker\mathcal R_p$，令
$H_\xi=\Pi(-w_\xi w_\xi^{\mathsf T}+C_\xi GC_\xi)\Pi$。
则局部极大值必须满足完整二阶条件

$$
\begin{aligned}
0&\ge-\|w_\xi\|^2-\beta\operatorname{tr}(WH_\xi)\\
&=-\|w_\xi\|^2+\beta\|W^{1/2}\Pi w_\xi\|^2
-\beta\sum_{\nu<\rho}
 \frac{\|W^{1/2}\Pi C_\xi e_\nu\|^2}{\rho-\nu}.
\end{aligned} \tag{10.4}
$$

和对 $QH$ 的任一完整正交特征基 $Me_\nu=\nu e_\nu$ 取，
包括所有重数；不只保留邻近的一个互补特征值。

证明。局部极大性的一阶方向条件是
$\operatorname{tr}C_\xi\le\beta\lambda_{\max}(\Pi C_\xi\Pi)$ 对所有 $\xi$ 成立。
有限维凸分离给出 $W\succeq0$、迹为一，使
$\operatorname{tr}C_\xi=\beta\operatorname{tr}(W\Pi C_\xi\Pi)$：
否则将迹一正半定矩阵的紧凸集合在线性读数映射下与目标读数分离，
得到某个违反上述方向条件的 $\xi$。
于是 $\|v_i\|^2-\beta(\Pi v_i)^{\mathsf T}W(\Pi v_i)$ 对 $i$ 为常数；
其 $p$ 加权和为 $T-\beta\rho=0$，故该常数为零。
两个乘子的差迹为零，并与 $\mathcal R_p$ 的满像正交，
所以乘子唯一。

先允许 $W$ 半正定以推导 (10.4)。
由定理 10.3，每个核向量可延伸为解析双轨迹
$p(t)=p+t\xi+t^2\eta+O(t^3)$。
协方差的二阶展开为

$$
M(p(t))=M+tC_\xi+t^2(C_\eta-w_\xi w_\xi^{\mathsf T})+O(t^3).
$$

顶层一阶压缩为 $\alpha I_E$。对互补块消元，顶层二阶矩阵为
$\Pi C_\eta\Pi+H_\xi$；沿双轨迹它是 $\gamma I_E$。
该 Schur 补计算只用互补逆 $G$：
解互补分量的一阶项为 $tGC_\xi x$，代回顶层即给出 $t^2\Pi C_\xi GC_\xi\Pi$。
一阶乘子恒等式又给出
$\operatorname{tr}C_\xi=\beta\alpha$、
$\operatorname{tr}C_\eta=\beta(\gamma-\operatorname{tr}WH_\xi)$。
代入商，二次系数恰为
$(n/\rho)(-\|w_\xi\|^2-\beta\operatorname{tr}WH_\xi)$。
局部极大性使其非正。展开 $G$ 的完整谱分解得到 (10.4)。

最后排除秩一 $W=uu^{\mathsf T}$。令 $h_i=\langle u,v_i\rangle$；
(10.3) 给出 $\|v_i\|^2=\beta h_i^2$，所以 $h_i\ne0$。
定义

$$
S=\sum_i p_i/h_i,\qquad
w=\sum_i p_iv_i/h_i,\qquad C=\sum_i(p_i/h_i)v_iv_i^{\mathsf T}.
$$

与 (8.4) 同一代数恒等式给出
$Cu=0$、$\operatorname{tr}C=0$、$\langle u,w\rangle=1$、
$\|w\|^2<\beta$。严格性来自 $a_i$ 的仿射无关性。
正解析曲线
$p_i(t)=p_i(1+t/h_i)/(1+tS)$ 满足

$$
M(t)=\frac{M+tC}{1+tS}-\frac{t^2ww^{\mathsf T}}{(1+tS)^2},\quad
T(t)=\frac T{1+tS}-\frac{t^2\|w\|^2}{(1+tS)^2}. \tag{10.5}
$$

取 $E$ 的另一单位向量 $v\perp u$，写 $\delta=v^{\mathsf T}Cv$。
若 $\delta\ne0$，选 $\delta t<0$，则 $u$ 分支成为顶层；
其与另一顶层的间隙为一阶，其余谱隙固定。
二阶秩一项的交叉影响为 $O(|t|^3)$，故
$\rho(t)=\rho/(1+tS)-t^2/(1+tS)^2+O(|t|^3)$。
于是目标增加
$(n/\rho)(\beta-\|w\|^2)t^2+O(|t|^3)>0$，矛盾。

若 $\delta=0$，取 (10.5) 的切向量
$\xi_i=p_i(1/h_i-S)$。有
$w_\xi=w$、$C_\xi=C-SM$，
所以 $\Pi C_\xi\Pi=-S\rho I_E$，即 $\xi\in\ker\mathcal R_p$。
又 $QC_\xi u=0$、$\langle u,w_\xi\rangle=1$，
故 $\operatorname{tr}(WH_\xi)=u^{\mathsf T}H_\xi u=-1$。
(10.4) 的右边等于 $\beta-\|w\|^2>0$，矛盾。
所以唯一乘子严格正定。

这也确定了完整的一阶临界方向集。
令 $A_\xi=\Pi C_\xi\Pi$，则最大特征值的一侧方向导数与乘子恒等式给出

$$
D^+\Phi(p)[\xi]=\frac{n\beta}{\rho}
 [\,\operatorname{tr}(WA_\xi)-\lambda_{\max}(A_\xi)\,]. \tag{10.6}
$$

正定的 $W$ 对 $A_\xi$ 的两个特征方向都赋严格正质量，
所以括号为零当且仅当 $A_\xi$ 为标量矩阵，即
$\xi\in\ker\mathcal R_p$；其余方向一阶严格下降。
因此 (10.4) 在全部一阶临界方向上给出双集的必要曲率，
没有因舍去某个互补特征值或某类临界方向而缩小条件。∎

## 11. 均匀点全部方向的二阶展开与阶数阈值

**定义 11.1（均匀谱与扰动矩阵）。** 令 $p^0_i=1/n$、
$M_0=M(p^0)$、$v_i^0=a_i-\bar a(p^0)$、
$\rho=\rho_n$、$\tau=\tau_n$、$\beta=\beta_n$、
$\rho_k=\mu_k/n$。均匀点的顶空间为
$E_0=\operatorname{span}_{\mathbb C}\{f_1,f_{n-1}\}$，按实结构理解为二维实空间。
记 $\Pi_0$ 为其投影，$Q_0=I_H-\Pi_0$，
$G_0=Q_0(\rho I_{Q_0H}-Q_0M_0Q_0)^{-1}Q_0$。
对每个实切向量 $\sum_i\xi_i=0$，定义
$x_k=\sum_i\xi_i z^{ki}$、$x_0=0$，
$C_\xi=\sum_i\xi_i v_i^0(v_i^0)^{\mathsf T}$、
$w_\xi=\sum_i\xi_i v_i^0$。有

$$
(C_\xi)_{km}=\frac{x_{m-k}}{n\overline d_kd_m},\qquad
\|w_\xi\|^2=\sum_{k=1}^{n-1}\rho_k|x_k|^2,\qquad
H_\xi=\Pi_0(-w_\xi w_\xi^{\mathsf T}+C_\xi G_0C_\xi)\Pi_0. \tag{11.1}
$$

**定理 11.2（含一阶分裂的完整二次式）。** 对每个实切向量 $\xi$，
令 $a=|x_2|$。若 $a>0$，取 $\Pi_0C_\xi\Pi_0$ 对应于
$\pm\rho a$ 的单位向量 $e_\pm$，置
$h_\pm=e_\pm^*H_\xi e_\pm$。
若 $a=0$，置 $h_+=h_-=\lambda_{\max}(H_\xi)$。
则对 $t\to0^\pm$，

$$
\begin{aligned}
\rho(p^0+t\xi)&=\rho+\rho a|t|+h_\pm t^2+o(t^2),\\
\Phi(p^0+t\xi)&=U_n-U_na|t|
+\frac n\rho\left[-\|w_\xi\|^2-\beta h_\pm+\beta\rho a^2\right]t^2
+o(t^2).
\end{aligned} \tag{11.2}
$$

若 $\xi$ 切于实际双集，即 $x_2=0$，则任一实现该切向量的解析双轨迹上
目标的二次系数为

$$
\begin{aligned}
\mathcal Q_n(\xi)&=\frac n\rho\,\mathcal C_n(\xi),\\
\mathcal C_n(\xi)
&=-\sum_{k=1}^{n-1}\rho_k|x_k|^2+\beta\rho|x_1|^2\\
&\quad-\frac{\beta\rho}{2}
 \sum_{j=2}^{n-2}\frac{\rho_j}{\rho-\rho_j}
 (|x_{j-1}|^2+|x_{j+1}|^2).
\end{aligned} \tag{11.3}
$$

这里没有遗漏偶数 $n$ 的自共轭模，也不要求互补特征值单重。

证明。式 (9.2) 在 $q_k=tx_k$ 时给出 (11.1)，并给出精确迹
$T(p^0+t\xi)=\tau-t^2\|w_\xi\|^2$。
顶层一阶压缩的对角元为零，非对角元模为 $\rho|x_2|$，
其特征值为 $\pm\rho a$。
对互补块作与定理 10.4 相同的 Schur 消元，
顶层二次矩阵为 $H_\xi$，故第一式 (11.2) 成立。
把迹除以该展开；分母一阶项的平方贡献
$\beta\rho a^2$，得到第二式。

若 $x_2=0$，在双轨迹 $p^0+t\xi+t^2\eta+O(t^3)$ 上，
共同二次位移是
$\frac12\operatorname{tr}(H_\xi+\Pi_0C_\eta\Pi_0)$。
均匀点对所有 $\eta$ 都有
$\operatorname{tr}C_\eta=0$ 和
$\operatorname{tr}(\Pi_0C_\eta\Pi_0)=0$，
故目标二次系数与 $\eta$ 无关，为
$(n/\rho)(-\|w_\xi\|^2-\frac\beta2\operatorname{tr}H_\xi)$。
在 Fourier 基中，秩一部分的顶迹为 $-2\rho|x_1|^2$，
而互补部分的顶迹为

$$
\operatorname{tr}(\Pi_0C_\xi G_0C_\xi\Pi_0)
=\rho\sum_{j=2}^{n-2}\frac{\rho_j}{\rho-\rho_j}
 (|x_{j-1}|^2+|x_{j+1}|^2).
$$

这就得到 (11.3)。所有分母严格为正；该公式按每个 Fourier 下标求和，
因而自动包括偶数中间模及互补重数。∎

**引理 11.3（完整双切空间的符号）。** 在 $x_2=0$ 的实切空间上，
(11.3) 按 Fourier 对角化。除 $\{1,n-1\}$ 外，
每个允许的非零模的系数严格为负；第一对的贡献为

$$
2\rho|x_1|^2\chi_n,\qquad
\chi_n=-1+\frac{(n^2-1)\sin^2(\pi/n)\cos(2\pi/n)}
 {3[\,4\cos^2(\pi/n)-1\,]}. \tag{11.4}
$$

而且 $\chi_n<0$ 对 $5\le n\le11$ 成立，
$\chi_n>0$ 对所有 $n\ge12$ 成立。

证明。(11.3) 是模的平方和；除第一对之外，其第一项严格负，
其余贡献非正。
对第一对，置
$r=\rho_2/\rho=1/[4\cos^2(\pi/n)]$。
它对 $\frac12\operatorname{tr}H_\xi$ 的贡献为
$\rho|x_1|^2[-1+r/(1-r)]$，所以其 $\mathcal C_n$ 系数为
$2\rho|x_1|^2[-1+\frac\beta2(1-2r)/(1-r)]$，恰为 (11.4)。

为证明阈值而不依赖数值图，令 $x=\pi/n$。
$\chi_n+1$ 等于

$$
\frac13(\pi^2-x^2)
 \left(\frac{\sin x}{x}\right)^2
 \frac{1-2\sin^2x}{3-4\sin^2x}. \tag{11.5}
$$

在 $0<x\le\pi/5$，三个因子都为正且严格递减：
第一个显然；第二个由 $\sin x-x\cos x>0$；
第三个由
$\frac{d}{du}\frac{1-2u}{3-4u}=-2/(3-4u)^2<0$
和 $u=\sin^2x$ 严格递增。
因此 $\chi_n$ 随整数 $n\ge5$ 严格递增。
在 $n=11$，$\pi<22/7$ 给出 $x<2/7$，
交错正弦级数给出
$\sin x<2/7-(2/7)^3/6+(2/7)^5/120=71054/252105$。
函数 $u(1-2u)/(3-4u)$ 在 $0\le u\le1/10$ 严格递增。
取 $u_*=5048670916/63556931025<1/10$，有精确有理比较

$$
\chi_{11}<-1+\frac{40u_*(1-2u_*)}{3-4u_*}
=-\frac{7788680328999988951}{2166987665449056075255}<0.
$$

在 $n=12$，代入 $\sin^2(\pi/12)=(2-\sqrt3)/4$ 得

$$
\chi_{12}=\frac{262\sqrt3-453}{24(1+\sqrt3)}>0,
$$

因为 $3\cdot262^2-453^2=723>0$。单调性完成所有阶数的符号判定。∎

**定理 11.4（对全部邻近竞争者的局部极大值与实际双集上的鞍点）。**
当 $5\le n\le11$ 时，均匀正环在尺度商上是严格局部极大值；
等价地，每个 $R_0>0$ 上的均匀电导
$c_i=n(n^2-1)/(12R_0)$，是固定总电阻问题的严格局部极大值。
当 $n\ge12$ 时，均匀点在实际双 Fiedler 集上具有正负二阶方向，
所以是严格鞍点。

证明。先给出覆盖分裂竞争者的统一论证。
在定理 10.3 的解析框架中，把顶层二阶矩阵写成
$m(p)I+\begin{pmatrix}g_1&g_2\\g_2&-g_1\end{pmatrix}$。
以 $v=(g_1,g_2)$ 为两个法向坐标，以 $u\in\mathbb R^{n-3}$
为其余解析坐标；均匀点为 $(0,0)$，双集恰为 $v=0$。
于是 $\rho(p)=m(p)+|v|$，而
$F(p)=nT(p)/m(p)$ 是解析函数。
在均匀点，$DF=0$；(11.3) 是其双切空间的二次式。
对 $5\le n\le11$，引理 11.3 使该式负定。
Taylor 定理和混合项的配方给出常数 $a,C>0$，使

$$
F(u,v)\le U_n-a|u|^2+C|v|^2
$$

在一个邻域成立（先吸收 $|u||v|$ 项）。
$m$ 与 $F$ 在此有正上下界，故再缩小邻域，

$$
\Phi(u,v)=\frac{F(u,v)}{1+|v|/m(u,v)}
\le U_n-\tfrac a2|u|^2-c|v|
$$

对某个 $c>0$ 成立。这严格控制所有邻近正竞争者，包括任意分裂的两个最小正特征值。

当 $n\ge12$，取第一 Fourier 对的非零实切向量，
(11.4) 给出正二次项；取第三 Fourier 对则给出负二次项。
定理 10.3 把这两类切向量分别实现为实际正解析双轨迹，
(11.3) 给出相应的严格增减。
固定电阻由 (7.3) 与尺度商解析等价，故上述局部类型也适用于固定电阻。
这些结论没有给出 $5\le n\le11$ 的全局最优性。∎

## 12. 每个大阶环上的实际改进分支与无极大值邻域

**定理 12.1（每个 $n\ge12$ 与每个 $R_0>0$ 的正解析分支）。**
存在 $\epsilon>0$ 和实解析 $p:(-\epsilon,\epsilon)\to\Delta^\circ$，使

$$
p(0)=p^0,\qquad p_i'(0)=\cos(2\pi i/n),\qquad
p(t)\in\mathscr D_n.
$$

定义

$$
c_i(t)=\frac{nT(p(t))}{R_0p_i(t)}. \tag{12.1}
$$

则每个 $|t|<\epsilon$ 都是原来 $n$ 个计数质量上的实际正环，
$R(c(t))=R_0$、$\lambda_2(c(t))=\lambda_3(c(t))<\lambda_4(c(t))$，
并且对所有充分小的 $t\ne0$，

$$
\lambda_2(c(t))R_0>U_n. \tag{12.2}
$$

证明。给定的切向量满足 $x_2=0$；
在定理 10.3 的隐函数图中取切坐标的直线，
解析地解出两个法向坐标，便得到上述曲线及规定的一阶导数。
其二次项由 (11.3)–(11.4) 给出，严格为正，
所以在正负两侧的充分小非零 $t$ 都满足 (12.2)。
严格正性与互补谱隙由连续性保持。
(7.3) 的全点对电阻恒等式给出 (12.1) 的精确归一化。∎

**推论 12.2（整个均匀邻域内无局部极大值）。** 对每个 $n\ge12$，
存在 $p^0$ 的一个完整相对邻域 $\mathcal N\subset\Delta^\circ$，
其中没有尺度不变目标 $\Phi$ 的局部极大值。
因此每个固定 $R_0>0$ 上对应的均匀电导邻域也没有局部极大值。

证明。用定理 10.3 的局部坐标把双集限制目标写为解析函数 $f(u)$。
由定理 11.4，存在固定坐标向量 $e$ 使
$D^2f(0)[e,e]>0$；连续性使
$D^2f(u)[e,e]>0$ 在一个完整双集邻域成立。
故该邻域内每点都不能是限制目标的局部极大值：
一阶导数非零时选增加的方向，为零时正二阶导数给出增加。
缩小完整邻域 $\mathcal N$ 以保持顶层二阶谱簇隔离。
由定理 8.1，完整问题的局部极大值必在该双集上，
因而已全部排除。固定电阻的结论由 (7.3) 的双向参数化得到。∎

## 13. 精确有限位移、余谱松弛锥与完整仿射纤维

**定理 13.1（任意有限位移的目标恒等式与谱松弛锥）。**
设 $p$ 是内点局部极大值，用定义 10.1 与定理 10.4 的记号。
对任意 $\sum_i\xi_i=0$、$p+\xi\in\Delta^\circ$，不要求 $\xi$ 小，
置 $w=w_\xi$、$C=C_\xi$、

$$
a=\operatorname{tr}(W\Pi C\Pi),\quad
D=\rho I_H-M,\quad
\delta=\lambda_{\max}(M+C-ww^{\mathsf T})-\rho-a.
$$

则有精确恒等式

$$
\begin{aligned}
M(p+\xi)&=M+C-ww^{\mathsf T},\\
T(p+\xi)&=T+\beta a-\|w\|^2,\\
\Phi(p+\xi)-\Phi(p)
&=-\frac{n(\|w\|^2+\beta\delta)}{\rho+a+\delta}.
\end{aligned} \tag{13.1}
$$

分母是实际正最大特征值。
令标准谱松弛锥为

$$
\mathfrak S_H=\{(Y,b)\in\operatorname{Sym}(H)\times\mathbb R:
 bI_H-Y\succeq0\}. \tag{13.2}
$$

这是闭凸锥，且对每个实数 $d$，余谱松弛具有精确判据

$$
\delta\le d
\ \Longleftrightarrow\
(C-ww^{\mathsf T}-D,\ a+d)\in\mathfrak S_H
\ \Longleftrightarrow\
D+(a+d)I_H-C+ww^{\mathsf T}\succeq0. \tag{13.3}
$$

尤其局部极大性要求
$\delta\ge-\|w\|^2/\beta$ 对全部充分小可行位移成立。
(13.3) 包含整个互补谱，不能只核对顶层压缩。

更具体地，令 $u=\Pi w$、$v=Qw$，并置

$$
\begin{aligned}
A_d&=(a+d)I_E-\Pi C\Pi+uu^{\mathsf T},\\
B&=-\Pi CQ+uv^{\mathsf T},\\
Z_d&=QDQ+(a+d)I_Q-QCQ+vv^{\mathsf T}.
\end{aligned}
$$

则 (13.3) 等价于完整 Schur 条件

$$
Z_d\succeq0,\qquad \operatorname{ran}(B^{\mathsf T})\subseteq\operatorname{ran}Z_d,
\qquad A_d-BZ_d^+B^{\mathsf T}\succeq0. \tag{13.4}
$$

证明。按新均值 $\bar a+w$ 展开协方差，得到第一式 (13.1)。
(10.3) 逐项乘以 $\xi_i$ 再相加给出 $\operatorname{tr}C=\beta a$，
从而得到迹式。令 $\rho'=\rho+a+\delta$，直接通分得最后的目标恒等式。
最大特征值的序定义给出 (13.2)–(13.3)。
将 (13.3) 的矩阵按 $E\oplus QH$ 分块正是
$\begin{pmatrix}A_d&B\\B^{\mathsf T}&Z_d\end{pmatrix}$。
其正半定性先在 $QH$ 给出 $Z_d\succeq0$；
在 $\ker Z_d$ 上用任意倍数测试交叉项，得到 $B\ker Z_d=0$，
等价于范围条件。
余下在 $\operatorname{ran}Z_d$ 上配方，得到 (13.4)，反向展开也成立。
这证明奇异余块也被包括。∎

**定理 13.2（整条非平凡仿射纤维的严格支配）。** 在每个内点局部极大值 $p$ 处，
完整仿射纤维

$$
\mathcal A_p=\{p+\xi\in\Delta^\circ:
 \sum_i\xi_i=0,\quad\operatorname{tf}_E(\Pi C_\xi\Pi)=0\} \tag{13.5}
$$

的维数为 $n-3$，且每个 $p'\in\mathcal A_p\setminus\{p\}$ 都满足
$\Phi(p')<\Phi(p)$。不附加 $\Pi w_\xi=0$、小位移或余谱不变的条件。

证明。引理 10.2 给出两个独立的线性条件，所以纤维维数为 $n-3$。
对其中的位移，有 $\Pi C\Pi=\alpha I_E$，所以 $a=\alpha$。
实际新矩阵的顶层压缩为
$(\rho+\alpha)I_E-uu^{\mathsf T}$。
二维空间内的秩一矩阵有零特征值，故
$\rho'\ge\rho+\alpha$，即 $\delta\ge0$。
又 $\sum_i\xi_i=0$ 时 $w=\sum_i\xi_i a_i$；
$a_1,\ldots,a_{n-1}$ 线性无关，所以 $w=0$ 强迫所有 $\xi_i=0$。
非零位移使 $\|w\|^2>0$，(13.1) 遂给出严格支配。
新矩阵正定，故所有商的分母为正；证明对整条可行纤维有效。∎

**定理 13.3（固定紧顶空间协方差不能给出邻域比值证书）。**
在内点局部极大值 $p$，不存在固定环境矩阵
$X\succeq0$、$\operatorname{tr}_H X=1$、$\operatorname{tr}(XM(p))=\rho(p)$，
使

$$
\operatorname{tr}(XM(q))\ge T(q)/\beta
\quad\text{对 }p\text{ 的某个完整相对邻域内所有 }q\text{ 成立}. \tag{13.6}
$$

因此用一个固定的紧顶空间协方差下界来证明
$\rho(q)\ge T(q)/\beta$ 的路线在完整邻域内失败；
该结论只排除这一类证书。

证明。紧性及正半定性使 $X$ 支持于 $E$：
$\operatorname{tr}(X(\rho I-M))=0$，正半定乘积的零迹使其像落在核内。
若 (13.6) 成立，双向一阶微分给出
$\operatorname{tr}(XC_\xi)=\operatorname{tr}C_\xi/\beta$
对每个 $\xi$ 成立，故由定理 10.4 的唯一性有 $X=\Pi W\Pi$。
对任意有限位移，(13.1) 又给出精确差

$$
\operatorname{tr}(XM(p+\xi))-T(p+\xi)/\beta
=\|w_\xi\|^2/\beta-(\Pi w_\xi)^{\mathsf T}W(\Pi w_\xi). \tag{13.7}
$$

$M$ 在 $n-1\ge4$ 维的 $H$ 上正定，顶层二重，
所以 $\beta=T/\rho>2$。
迹一的二阶 $W$ 有特征值 $\omega\ge1/2>1/\beta$。
映射 $\xi\mapsto w_\xi$ 是单纯形切空间到 $H$ 的线性同构，
故可取 $w_\xi$ 为该特征值的单位特征向量。
对每个充分小非零 $t$，$p+t\xi$ 仍严格正，
(13.7) 为 $t^2(1/\beta-\omega)<0$，违背 (13.6)。∎

## 14. 同一实际环的全部删边路径与闭合边判据

**定理 14.1（原路径第三特征值处的精确正闭合判据）。**
令 $P_n$ 是任意正电导路径，顶点质量全部为一，端点为 $a,b$，
$e=\delta_a-\delta_b\in H$。记
$A=L_P|_H$，其严格递增的特征值为
$0<\lambda_2<\lambda_3<\cdots<\lambda_n$，
正交单位特征向量为 $x_j$。置

$$
\gamma_j=e^{\mathsf T}x_j,\qquad
S_3=\sum_{\substack{2\le j\le n\\j\ne3}}
 \frac{\gamma_j^2}{\lambda_j-\lambda_3}.
$$

给端点间添加实际电导 $h>0$ 后，有
$\lambda_2(L_P+hee^{\mathsf T})=\lambda_3(L_P+hee^{\mathsf T})=\lambda_3$
当且仅当

$$
\gamma_3=0,\qquad S_3<0,\qquad h=-1/S_3. \tag{14.1}
$$

这包括路径的全部正谱与共同端点向量，不以独立路径边际替代。

证明。正路径的特征向量由端点的一个坐标经首行和三对角递推唯一确定，
故每个特征值单重。
对 $\lambda$ 不在路径谱内，直接展开秩一行列式得到经典世俗方程

$$
1+h\,e^{\mathsf T}(A-\lambda I)^{-1}e
=1+h\sum_{j=2}^n\frac{\gamma_j^2}{\lambda_j-\lambda}=0. \tag{14.2}
$$

在 $\lambda=\lambda_3$ 处，若 $\gamma_3\ne0$，
把更新后的特征方程与 $x_3$ 内积可推出 $e^{\mathsf T}y=0$，
进而 $y$ 为 $x_3$ 的倍数，再推出 $y=0$，故此时不是特征值。
若 $\gamma_3=0$，$x_3$ 仍为特征向量。
在 $x_3^\perp$ 上 $A-\lambda_3I$ 可逆；
第二个独立特征向量存在当且仅当
$1+hS_3=0$，且此时其在该补空间中唯一至倍数。
因为 $h>0$，此条件恰为 (14.1)。

正秩一交错给出，若更新后的正谱为 $\mu_2\le\cdots\le\mu_n$，则
$\lambda_j\le\mu_j\le\lambda_{j+1}$ 对 $2\le j<n$ 成立。
$\lambda_3$ 的二重只能出现在 $\mu_2,\mu_3$，
因为 $\mu_4\ge\lambda_4>\lambda_3$。
故 (14.1) 给出的二重确为 Fiedler 二重，反向必要性亦成立。
所用交错也可直接由 Rayleigh 极小极大原理在 $e^\perp$ 上限制得到。∎

**推论 14.2（闭合的全点对电阻和目标）。** 令
$K=A^{-1}$、$v=Ke$、$\ell=e^{\mathsf T}Ke$、
$\tau=h/(1+h\ell)$。对任意 $h>0$，

$$
\begin{aligned}
K_h&=K-\tau vv^{\mathsf T},\\
R_h&=R_P-n\tau\|v\|^2,\qquad
R_{\mathrm{eff},h}(a,b)=\ell/(1+h\ell).
\end{aligned} \tag{14.3}
$$

若 (14.1) 成立，则

$$
\lambda_2(L_h)R_h
=\lambda_3\left[R_P-
 n\,\frac{h}{1+h\ell}\sum_{j=2}^n\frac{\gamma_j^2}{\lambda_j^2}\right]. \tag{14.4}
$$

证明。直接相乘验证秩一逆公式给出第一式，
取迹并用 $R=n\operatorname{tr}_H K$ 得到第二式；
取 $e$ 的二次型得到端点电阻式。
谱分解给出 $\|Ke\|^2=\sum_j\gamma_j^2/\lambda_j^2$，
再由定理 14.1 得 (14.4)。
逆与全点对迹的经典输入仍是
[Ghosh–Boyd–Saberi，DOI:10.1137/050645452](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf)
§§2.4–2.5 的电阻公式。∎

**定理 14.3（每次删除必须属于同一个环）。** 对一个固定的正电导环 $c$，
对每条边 $e_i$ 删边得到路径 $P^{(i)}$，
令 $A_i,\lambda_{i,j},\gamma_{i,j},S_{i,3},K_i,v_i,\ell_i$
为定理 14.1–14.2 在此路径及其原始端点差上的数据。
则以下条件等价：
环是双 Fiedler；某一次删除满足 (14.1) 且 $h=c_i$；
每一次删除都满足 (14.1) 且 $h=c_i$。
在等价条件成立时，所有 $\lambda_{i,3}$ 都等于同一个环 Fiedler 值 $\Lambda$，且

$$
L(c)|_H=A_i+c_i e_ie_i^{\mathsf T},\qquad
L(c)^+|_H=K_i-\tau_i v_iv_i^{\mathsf T},\qquad
R(c)=R(P^{(i)})-n\tau_i\|v_i\|^2,\quad
\tau_i=\frac{c_i}{1+c_i\ell_i}. \tag{14.5}
$$

这里 $e_i$ 在矩阵式中表示原边的端点差向量。
对每个删除路径还须同时保留约定 4.2 引用的完整路径定理：

$$
\lambda_{i,2}R(P^{(i)})\le A_n,
$$

等号当且仅当按该次路径次序
$c_j=\kappa_i\sqrt{j(n-j)}/[\,2\sqrt{j(n-j)}
-\sqrt{(j-1)(n-j+1)}-\sqrt{(j+1)(n-j-1)}\,]$
对同一个 $\kappa_i>0$ 成立。
每条路径的 $n-1$ 条保留边必须采用原环中相同的电导坐标；
不同删除路径的共同边共有 $n-2$ 条，并在这些边上逐一相容。
不能把分别取得的路径最优值同时赋给它们。

证明。若环正谱在最低处二重为 $\Lambda$，
秩一交错在每次删边给出
$\lambda_{i,2}\le\Lambda\le\lambda_{i,3}\le\Lambda$，
故 $\lambda_{i,3}=\Lambda$。
于是定理 14.1 的必要条件对每条边成立，闭合电导恰为 $c_i$。
反向只需任一次删除的充分条件；“每次”蕴含“某次”。
(14.5) 是同一矩阵恢复及 (14.3)，所以它强制全部删除数据相容。
最后直接应用
[完整路径定理及全部等号类](https://github.com/the-omega-institute/trureturing/blob/48474969a064d134fa7bb9c78d5919922d48faf9/docs/develop/theory/FIEDLER_RESISTANCE_PATH_OPTIMIZER.md)
定理 2.1、推论 3.1，其中该文的 $C_n$ 是这里的 $A_n$；
原顶点质量仍全部为一，路径电阻仍为全部 $\binom n2$ 个点对之和。
这使用整个路径定理，不重新推导其特例。∎

## 15. 精确优化问题与所用文献的适用范围

**定义 15.1（尚待确定的尖锐值与充分等号条件）。** 对每个 $n\ge5$，
仍取定义 4.1、8.2 的
$B_n=\sup_{c>0}\lambda_2(L(c))R(c)$、
$\mathcal P_n=\{p\in\Delta^\circ:\Phi(p)=B_n\}$。
定理 7.1–7.2 的正内点达到性、边界排除与紧近最大点，
以及定理 8.1 的必要双重性，均作为完整输入。
第 9–14 节给出比较区域、局部类型、分支、必要曲率、
有限位移支配与兼容闭合条件，没有确定任何尚未求出的 $B_n$，
也没有给出 $\mathcal P_n$ 的充分且必要刻画。
$5\le n\le11$ 的局部结论不替代全局问题；
$n\ge12$ 的改进分支只确定严格超过 $U_n$ 的可行点。
固定 $R_0>0$ 的完整最优类仍是 (7.3) 作用于 $\mathcal P_n$ 的像。

本节的优化约束是
[Cruz Ortega–Menéndez-Conde，arXiv:2306.08187v1](https://arxiv.org/html/2306.08187v1)
§5 的全点对电阻；该文路径小阶结论与约定 4.2 的完整路径供应相区分。
[Ghosh–Boyd–Saberi](https://doi.org/10.1137/050645452) 的伪逆与全点对迹公式
是电学中间输入，其固定电导预算的凸优化问题不替代这里的比值最大化。
[Lin–Shirazi，arXiv:2410.09736v1](https://arxiv.org/html/2410.09736v1)
§4 定义 4.3、4.6 与定理 4.9 刻画周期且平衡的潜在第二或第三特征向量；
这里保留同一电导的联合二重条件并额外比较全点对目标。
[Arroyo–Castro–Fillman，arXiv:2308.12373v1](https://arxiv.org/html/2308.12373v1)
§§1–2 的周期 Jacobi、Schrödinger 和闭谱隙关系提供二阶周期递推的背景；
(10.2) 在本模型的正边电阻系数切片上使用，并给出所需横截性。
[*Laplacian Network Optimization via Information Functions*,
arXiv:2512.19279v1](https://arxiv.org/html/2512.19279v1) 的谱目标与信息函数框架
须按其各自的目标和权重约束解释；
这里的 (9.2)、(10.4)、(11.3) 与 (13.1) 直接针对
$\lambda_2\,n\operatorname{tr}L^+$，全部竞争者始终为独立正电导。
经典 Rayleigh 原理、秩一行列式、Schur 补与解析隐函数定理
只承担上述推导的中间步骤。

## 追加锚（本行以下为增补区）

## 16. 带标号五边形的全局尖锐值

**定义 16.1（五阶 Fourier 数据）。** 令 $p=(p_0,\ldots,p_4)\in\Delta^\circ$，令

$$
z=e^{2\pi\mathrm i/5},qquad q_k=\sum_{j=0}^4p_jz^{kj}\quad(k\in\mathbb Z/5\mathbb Z),qquad
a=|q_1|^2,\quad b=|q_2|^2.
$$

置

$$
\rho_1=\frac{5+\sqrt5}{50},\qquad
\rho_2=\frac{5-\sqrt5}{50},\qquad
\tau=\frac25,qquad
\kappa=\frac{5+\sqrt5}{20},qquad
r=\frac{\rho_2}{\rho_1}=\frac{3-\sqrt5}{2},qquad
h=1-2\kappa=\frac{5-\sqrt5}{10}.
\tag{16.1}
$$

For the covariance operator $M(p)$ of Definition 4.1, write

$$
T=\operatorname{tr}_H M(p)=\tau-2\rho_1a-2\rho_2b,
\qquad \rho=\lambda_{\max}(M(p)|_H).
\tag{16.2}
$$

The relation between this operator and a positive conductance vector is exactly (5.4)–(5.5): if
$r_i=c_i^{-1}$, $s=\sum_i r_i$, and $p_i=r_i/s$, then
$\lambda_2(L(c))R(c)=5T/\rho$.

**引理 16.2（全域二模态证书）。** For every $p\in\Delta^\circ$,

$$
\rho\ge \kappa T.
\tag{16.3}
$$

Equality in (16.3) is possible only when $q_1=q_2=0$, and hence only at
$p_0=\cdots=p_4=1/5$.

**证明。** The $k=1,2$ principal block of the Fourier matrix in (9.2) is the Hermitian matrix

$$
A=
\begin{pmatrix}
\rho_1(1-a)&\displaystyle\frac{q_1-\overline q_1q_2}{5\,\overline d_1d_2}\\[6pt]
\displaystyle\frac{\overline q_1-q_1\overline q_2}{5\,d_1\overline d_2}&\rho_2(1-b)
\end{pmatrix},
\qquad d_k=1-z^{-k}.
\tag{16.4}
$$

Indeed, this is (9.2) with $(k,m)=(1,2)$, and
$|d_k|^{-2}=5\rho_k$. Therefore, with
$\chi=|q_1-\overline q_1q_2|^2$,

$$
\det(\kappa T I_2-A)
=\rho_1^2\bigl[h(a-b)L-r\chi\bigr],
\qquad
L=1-r-2\kappa a+rh\,b.
\tag{16.5}
$$

The identities used here are
$\tau=2\rho_1(1+r)$, $1=2\kappa(1+r)$, and $h=2\kappa r$.
If $a\le b$, then

$$
L\ge 1-r-2\kappa a+rh\,a=(1-r)(1-a)\ge0,
\tag{16.6}
$$

so the right side of (16.5) is nonpositive. Suppose next that $a>b$ and put
$x=\sqrt a$, $y=\sqrt b$. If $L\le0$, (16.5) is again nonpositive. If $L>0$, the reverse triangle inequality gives

$$
\chi\ge x^2(1-y)^2.
\tag{16.7}
$$

The remaining scalar comparison is valid on the entire square-triangle
$0\le y\le x\le1$:

$$
r x^2(1-y)^2-h(x^2-y^2)\bigl(1-r-2\kappa x^2+rh\,y^2\bigr)\ge0.
\tag{16.8}
$$

For completeness, its exact factorization is as follows. Put $y=tx$ with
$0\le t\le1$. The left side of (16.8) equals

$$
\frac{7-3\sqrt5}{10}\,x^2G_t(x),
$$

where

$$
\begin{aligned}
G_t(x)&=A_t x^2-5(3+\sqrt5)tx+C_t,\\
A_t&=t^4+(3+\sqrt5)t^2+\frac{7+3\sqrt5}{2},\\
C_t&=\frac{5+3\sqrt5}{2}t^2+5+\sqrt5.
\end{aligned}
\tag{16.9}
$$

Here $A_t>0$, and the discriminant of this quadratic in $x$ is

$$
\bigl[-10-6\sqrt5\bigr](1-t)^2(1+t)^2(t^2+4+2\sqrt5)\le0.
\tag{16.10}
$$

Thus (16.8) holds. It is strict when $x>y$: in that case $t<1$, so (16.10) is strict. Combining (16.5), (16.7), and (16.8) proves
$\det(\kappa T I_2-A)\le0$ for every $p\in\Delta^\circ$.

The two eigenvalues of $A$ are real. A nonpositive determinant in (16.5) implies
$\lambda_{\max}(A)\ge\kappa T$, and Cauchy interlacing then gives (16.3).
For equality, the case $a>b$ is excluded by the strictness just proved. If
$a<b$, (16.6) makes (16.5) strictly negative. Hence $a=b$ and $\chi=0$.
If $a=b>0$, then
$q_1=\overline q_1q_2$ forces $|q_2|=1$, impossible for a strictly positive
probability on the five distinct points $z^{2j}$. Therefore $a=b=0$.
Fourier inversion gives $p_j=1/5$ for every $j$. Conversely, the uniform vector has
$q_1=q_2=0$ and equality in (16.3). ∎

**定理 16.3（五边形的尖锐全局界与全部等号）。** For every five-tuple of independent finite strictly positive conductances
$c=(c_0,\ldots,c_4)$ on the labelled cycle $C_5$,

$$
\lambda_2(L(c))R(c)\le 25-5\sqrt5.
\tag{16.11}
$$

The constant is attained by every constant conductance vector. Equality in (16.11)
holds if and only if

$$
c=\gamma(1,1,1,1,1)\qquad(\gamma>0).
\tag{16.12}
$$

Thus the equality set is the labelled ray (16.12), with no quotient by rotations or
reflections.

**证明。** By (5.5) and Lemma 16.2,

$$
\lambda_2(L(c))R(c)=5\frac{T}{\rho}\le\frac5\kappa
=\frac{100}{5+\sqrt5}=25-5\sqrt5.
$$

The lemma also says that equality forces $p_i=1/5$. Since $p_i=r_i/s$ with
$r_i=c_i^{-1}$, this is equivalent to $c_0=\cdots=c_4=\gamma$ for some
$\gamma>0$. For the converse, the ordinary unit $C_5$ has nonzero spectrum

$$
2-2\cos\frac{2\pi k}{5}
\quad(k=1,2,3,4),
$$

so $\lambda_2(L(\gamma\mathbf1))=\gamma(5-\sqrt5)/2$. The classical
identity $R(c)=5\operatorname{tr}L(c)^+$ (the all-pairs pseudoinverse identity
of Ghosh–Boyd–Saberi, §§2.4–2.5, equations (8), (13)–(15)) gives
$R(\gamma\mathbf1)=10/\gamma$. Their product is $25-5\sqrt5$. ∎

**推论 16.4（固定总电阻的唯一原始等号向量）。** For every $R_0>0$,

$$
\max_{\substack{c_i>0\text{ finite}\\R(c)=R_0}}
\lambda_2(L(c))=\frac{25-5\sqrt5}{R_0},
\tag{16.13}
$$

and the unique labelled maximizer is

$$
c_0=c_1=c_2=c_3=c_4=\frac{10}{R_0}.
\tag{16.14}
$$

At this vector the attained Fiedler value is $(25-5\sqrt5)/R_0$.

**证明。** The scaling laws $R(\alpha c)=R(c)/\alpha$ and
$\lambda_2(L(\alpha c))=\alpha\lambda_2(L(c))$ give from (16.11)
$\lambda_2\le(25-5\sqrt5)/R_0$ on the level set $R=R_0$. Formula
$R(\gamma\mathbf1)=10/\gamma$ gives (16.14), which attains that bound. The
equality clause of Theorem 16.3 proves uniqueness. ∎

## 17. 适用范围、路径参数与未决阶数

The comparison in Lemma 16.2 is over the complete Fourier moment domain
$0\le|q_1|,|q_2|\le1$, including all three scalar cases $a<b$, $a=b$, and
$a>b$ and the possible sign change of $L$; strict positivity is used only for
the equality assertion $|q_1|,|q_2|<1$. The bridge from conductances to this domain
is the all-pairs cycle identity (5.4)–(5.5), with the same ordinary unit vertex
masses and the same ten unordered original vertex pairs as in Definition 1.1.
The classical Fourier diagonalization and pseudoinverse trace identity are the
only external intermediate inputs; the determinant comparison (16.5)–(16.10) is
the additional five-cycle derivation.

For boundary directions of the resistance simplex, Theorem 5.1 already supplies
the complete path comparison. Its parameter map is the one in Convention 4.2:
for $P_5$, $s=(2,\sqrt6,\sqrt6,2)$,
$d=(4-\sqrt6,2\sqrt6-4,2\sqrt6-4,4-\sqrt6)$, and the path constant is

$$
A_5=\sum_{i=1}^4s_id_i=40-12\sqrt6.
$$

The cited path theorem applies to all positive path conductances and extends to
closed directions by the continuity argument in Theorem 5.1; it retains the five
original unit vertex masses and never replaces a deleted edge by a vertex
contraction. Since $25-5\sqrt5>40-12\sqrt6$, these boundary values lie strictly
below the five-cycle value. Indeed, this is equivalent to $12\sqrt6>15+5\sqrt5$; squaring gives $514>150\sqrt5$, and squaring once more gives $264196>112500$. No separately optimized path is assigned to more than
one deletion of the same labelled cycle.

The result above settles only the unrestricted labelled $C_5$. For every $n\ge6$,
the exact value of $B_n$ and the complete equality set remain unresolved; none of
the statements here supplies a general-$n$ bound, a kernel result, or a resolution
of the original all-$n$ problem.

## 追加锚（本行以下为增补区）

## 18. 带标号六边形的全局尖锐界

**定义 18.1（六阶 Fourier 坐标）。** 令 $p=(p_0,\ldots,p_5)\in\Delta^\circ$，令
$z=\exp(\pi\mathrm i/3)$，并置

$$
q_k=\sum_{j=0}^{5}p_jz^{kj}\quad(k\in\mathbb Z/6\mathbb Z),\qquad
a=|q_1|^2,\quad b=|q_2|^2,\quad c=q_3^2 .
$$

这里 $q_3\in\mathbb R$。由式 (5.5) 及式 (9.2)，若 $M(p)$ 是定义 4.1 的
协方差算子，则

$$
T(p)=\frac{35}{72}-\frac a3-\frac b9-\frac c{24},\qquad
\Phi(p)=\frac{6T(p)}{\lambda_{\max}(M(p)|_H)} .
\tag{18.1}
$$

**引理 18.2（六点矩的二阶主块证书）。** 对每个 $p\in\Delta^\circ$，有

$$
 (11a-8b-3c)(70-72a+11b-9c)
 \le 1225\,|q_1-\overline q_1q_2|^2 .
\tag{18.2}
$$

等号若 $p$ 严格为正则仅在 $p_0=\cdots=p_5=1/6$ 处成立。

**证明。** 对任意 $v\in[0,\infty)^6$，记
$S_v=\sum_jv_j$、$Q_k(v)=\sum_jv_jz^{kj}$、
$A_v=|Q_1(v)|^2$、$B_v=|Q_2(v)|^2$、$C_v=Q_3(v)^2$，并置

$$
\begin{aligned}
D(v)={}&1225|S_vQ_1(v)-\overline{Q_1(v)}Q_2(v)|^2\\
&-(11A_v-8B_v-3C_v)(70S_v^2-72A_v+11B_v-9C_v),\\
J(v)={}&12S_v(455A_v+560B_v+210C_v)
 -14700\operatorname{Re}(\overline{Q_1(v)}^{\,2}Q_2(v)),\\
K(v)={}&36(455A_v+560B_v+210C_v).
\end{aligned} \tag{18.3}
$$

$D,J,K$ 分别齐次四次、三次、二次。$S_p=1$ 时，$D(p)$ 正是
(18.2) 的右边减左边。直接相乘得

$$
\begin{aligned}
D(v)={}&S_v^2(455A_v+560B_v+210C_v)
 -2450S_v\operatorname{Re}(\overline{Q_1(v)}^{\,2}Q_2(v))\\
&+792A_v^2+528A_vB_v-117A_vC_v
 +88B_v^2-39B_vC_v-27C_v^2.
\end{aligned} \tag{18.4}
$$

加上 $m\mathbf1$ 不改变非恒定 Fourier 矩，而总和增加 $6m$，故

$$
D(v+m\mathbf1)=D(v)+mJ(v)+m^2K(v)\qquad(m\ge0).
\tag{18.5}
$$

以下给出 $D(v),J(v)$ 的完整有理系数非负分解。
取 $m=\min_jp_j$、$v=p-m\mathbf1$，将六个坐标按非降次序排列。
$D,J,K$ 在循环移动和反射标签下不变，故排序排列可取为集合

$$
\Sigma=\left\{\sigma\in\mathfrak S_6:
\sigma=\min_{\mathrm{lex}}\{(\epsilon\sigma_j+h\bmod6)_{j=0}^5:
\epsilon\in\{-1,1\},\ 0\le h<6\}\right\}
$$

中的代表。$\Sigma$ 的全部 $60$ 个排列按字典序在系数表中列出。
这枚举所有坐标次序，没有要求原向量具有对称性；相等坐标任选排序。
令 $x_j=v_{\sigma_j}-v_{\sigma_{j-1}}\ge0$（$1\le j\le5$），则
$v_{\sigma_0}=0$、$v_{\sigma_j}=x_1+\cdots+x_j$，记此向量为 $v^\sigma(x)$。

对五位非负整数指标 $\alpha$，记 $x^\alpha=\prod_{j=1}^5x_j^{\alpha_j}$。
表中五位数字表示五个指数，不是十进制数。
$I_d=\{\alpha\in\mathbb N_0^5:|\alpha|=d,\ \alpha_5\le2\}$
按逆字典序列出；$|I_3|=34$、$|I_4|=65$。完整列次序为：

$I_3$: $(30000,21000,20100,20010,20001,12000,11100,11010,11001,10200,10110,10101,10020,10011,10002,03000,02100,02010,02001,01200,01110,01101,01020,01011,01002,00300,00210,00201,00120,00111,00102,00030,00021,00012)$.

$I_4$: $(40000,31000,30100,30010,30001,22000,21100,21010,21001,20200,20110,20101,20020,20011,20002,13000,12100,12010,12001,11200,11110,11101,11020,11011,11002,10300,10210,10201,10120,10111,10102,10030,10021,10012,04000,03100,03010,03001,02200,02110,02101,02020,02011,02002,01300,01210,01201,01120,01111,01102,01030,01021,01012,00400,00310,00301,00220,00211,00202,00130,00121,00112,00040,00031,00022)$.

对 $u,v\in I_4$、$u+v$ 逐坐标为偶数及 $t>0$，定义

$$
\begin{aligned}
B_{u,v,t}(x)&=t x^u+t^{-1}x^v-2x^{(u+v)/2}\\
&=\frac{x^w}{t}\left(t x^{(u-w)/2}-x^{(v-w)/2}\right)^2\ge0,
\qquad w_j=\min(u_j,v_j).
\end{aligned} \tag{18.8}
$$

半指数均为整数。令 $\mathcal B_s$ 为乘数表中编号 $s$ 的所有行，
没有列出的编号取空集。另令 $E_s=0$，但下列四个编号取

$$
E_s(x)=\frac{25}{32}\left[48x_4^2+48x_4x_5+
\sum_{j=1}^3(a_{sj}x_jx_4+b_{sj}x_jx_5)\right]^2.
\tag{18.9}
$$

| $s$ | $(a_{s1},b_{s1},a_{s2},b_{s2},a_{s3},b_{s3})$ |
|---|---|
| 49 | $(-66,15,-160,-80,-32,-28)$ |
| 50 | $(-66,-81,-160,-80,-32,-4)$ |
| 55 | $(-66,15,-160,-80,-32,-4)$ |
| 56 | $(-66,-81,-160,-80,-32,-28)$ |

乘数表的每行贡献 $\kappa B_{u,v,t}$；所有 $t,\kappa$ 均严格为正。

| $s$ | $u$ | $v$ | $t$ | $\kappa$ |
|---|---|---|---|---|
| 1 | 00040 | 20020 | $1$ | $1125$ |
| 1 | 00040 | 20020 | $1/2$ | $1350$ |
| 1 | 00022 | 20020 | $1$ | $1800$ |
| 1 | 00031 | 20011 | $1$ | $225/2$ |
| 2 | 00112 | 20110 | $1$ | $1842$ |
| 2 | 00040 | 20020 | $1$ | $1125$ |
| 2 | 00040 | 20020 | $1/2$ | $1350$ |
| 2 | 00031 | 20011 | $1$ | $3375/2$ |
| 2 | 00031 | 20011 | $1/2$ | $3825$ |
| 2 | 00202 | 20002 | $1$ | $1125/2$ |
| 2 | 00022 | 20002 | $1$ | $375/2$ |
| 2 | 00022 | 20002 | $1/2$ | $2850$ |
| 2 | 00022 | 02002 | $1$ | $375/2$ |
| 5 | 00202 | 20002 | $1$ | $1125/2$ |
| 7 | 00040 | 20020 | $1/2$ | $2325$ |
| 7 | 00040 | 20020 | $1/4$ | $150$ |
| 7 | 00022 | 20020 | $1$ | $750$ |
| 7 | 00031 | 20011 | $1$ | $2325/2$ |
| 7 | 00040 | 00220 | $1/2$ | $1200$ |
| 7 | 00031 | 00211 | $1$ | $2250$ |
| 7 | 00022 | 00202 | $1$ | $1050$ |
| 8 | 00040 | 20020 | $1/2$ | $2325$ |
| 8 | 00040 | 20020 | $1/4$ | $150$ |
| 8 | 00031 | 20011 | $1/2$ | $11025/2$ |
| 8 | 00022 | 20002 | $1/2$ | $6075/2$ |
| 8 | 00022 | 02002 | $1/2$ | $375/2$ |
| 8 | 00040 | 00220 | $1/2$ | $1200$ |
| 8 | 00022 | 00220 | $1/2$ | $75$ |
| 8 | 00031 | 00211 | $1$ | $825/2$ |
| 8 | 00031 | 00211 | $1/2$ | $1725/2$ |
| 8 | 00022 | 00202 | $1$ | $150$ |
| 17 | 00022 | 02002 | $1$ | $375/2$ |
| 17 | 00040 | 00220 | $1$ | $1200$ |
| 17 | 00022 | 00220 | $1$ | $1350$ |
| 17 | 00022 | 00202 | $1$ | $150$ |
| 18 | 00040 | 00220 | $1$ | $1200$ |
| 18 | 00022 | 00220 | $1$ | $750$ |
| 18 | 00031 | 00211 | $1$ | $1500$ |
| 18 | 00022 | 00202 | $1$ | $1050$ |
| 23 | 00022 | 02002 | $1$ | $375/2$ |
| 25 | 00040 | 20020 | $1$ | $1125$ |
| 25 | 00040 | 20020 | $1/2$ | $1350$ |
| 25 | 00022 | 20020 | $1$ | $1800$ |
| 25 | 00031 | 20011 | $1$ | $225/2$ |
| 26 | 00112 | 20110 | $1$ | $1842$ |
| 26 | 00040 | 20020 | $1$ | $1125$ |
| 26 | 00040 | 20020 | $1/2$ | $1350$ |
| 26 | 00031 | 20011 | $1$ | $3375/2$ |
| 26 | 00031 | 20011 | $1/2$ | $3825$ |
| 26 | 00202 | 20002 | $1/8$ | $1125/2$ |
| 26 | 00022 | 20002 | $1/4$ | $588$ |
| 26 | 00022 | 20002 | $1/8$ | $4899/2$ |
| 26 | 01201 | 03001 | $1$ | $588$ |
| 26 | 00202 | 02002 | $1$ | $14325/16$ |
| 26 | 00202 | 02002 | $2$ | $20475/16$ |
| 26 | 00022 | 02002 | $1$ | $13251/16$ |
| 26 | 00022 | 02002 | $2$ | $4149/16$ |
| 29 | 00202 | 20002 | $1$ | $969/2$ |
| 29 | 00202 | 20002 | $1/2$ | $78$ |
| 29 | 01201 | 03001 | $1$ | $588$ |
| 29 | 00202 | 02002 | $1$ | $2697/2$ |
| 29 | 00202 | 02002 | $2$ | $1653/2$ |
| 29 | 00022 | 02002 | $1$ | $375$ |
| 29 | 00022 | 02002 | $2$ | $1425/2$ |
| 31 | 00220 | 20020 | $1$ | $6111/2$ |
| 31 | 00040 | 20020 | $1/2$ | $2325$ |
| 31 | 00040 | 20020 | $1/4$ | $150$ |
| 31 | 00022 | 20020 | $1$ | $300$ |
| 31 | 00031 | 20011 | $1$ | $3225/2$ |
| 31 | 00040 | 00220 | $1/2$ | $1200$ |
| 31 | 00022 | 00220 | $1$ | $1350$ |
| 31 | 00022 | 00202 | $1$ | $150$ |
| 32 | 00220 | 20020 | $1$ | $6111/2$ |
| 32 | 00202 | 20020 | $1$ | $4368$ |
| 32 | 00040 | 20020 | $1/2$ | $2325$ |
| 32 | 00040 | 20020 | $1/4$ | $150$ |
| 32 | 00022 | 20020 | $1/4$ | $93/2$ |
| 32 | 00211 | 20011 | $1$ | $4476$ |
| 32 | 00031 | 20011 | $1/2$ | $4434$ |
| 32 | 00031 | 20011 | $1/4$ | $1032$ |
| 32 | 00022 | 20002 | $1/4$ | $6075/2$ |
| 32 | 00022 | 02002 | $1/2$ | $1857/2$ |
| 32 | 00022 | 02002 | $1/4$ | $159$ |
| 32 | 00040 | 00220 | $1/2$ | $1200$ |
| 32 | 00031 | 00211 | $1/2$ | $2250$ |
| 32 | 00022 | 00202 | $1/2$ | $1050$ |
| 43 | 00022 | 02002 | $1$ | $825/2$ |
| 43 | 00022 | 02002 | $1/2$ | $675$ |
| 43 | 00040 | 00220 | $1$ | $1200$ |
| 43 | 00031 | 00211 | $1$ | $2250$ |
| 43 | 00022 | 00202 | $1$ | $1050$ |
| 44 | 00040 | 00220 | $1$ | $1200$ |
| 44 | 00022 | 00220 | $1$ | $1350$ |
| 44 | 00022 | 00202 | $1$ | $150$ |
| 49 | 00220 | 02020 | $1$ | $376$ |
| 49 | 00202 | 02020 | $1$ | $4872$ |
| 49 | 00211 | 02011 | $1$ | $208$ |
| 50 | 00220 | 02020 | $1$ | $376$ |
| 55 | 00220 | 20020 | $1$ | $9411/2$ |
| 55 | 00220 | 02020 | $1$ | $376$ |
| 56 | 00220 | 20020 | $1$ | $9411/2$ |
| 56 | 00202 | 20020 | $1$ | $11711/2$ |
| 56 | 00211 | 20011 | $1$ | $3228$ |
| 56 | 00220 | 20002 | $1$ | $12917/4$ |
| 56 | 00220 | 02020 | $1$ | $376$ |
| 56 | 00211 | 02011 | $1$ | $5080$ |

系数表每行的 $h_s$ 有 $34$ 项，$r_s$ 有 $65$ 项，分别按 $I_3,I_4$
的完整列次序；$g_s>0$。精确的索引分解为

$$
\begin{aligned}
J(v^\sigma(x))&=210\sum_{\alpha\in I_3}h_{s,\alpha}x^\alpha,\\
D(v^\sigma(x))&=E_s(x)+
\sum_{(u,v,t,\kappa)\in\mathcal B_s}\kappa B_{u,v,t}(x)
+g_s\sum_{\alpha\in I_4}r_{s,\alpha}x^\alpha.
\end{aligned} \tag{18.10}
$$

全部 $h_{s,\alpha},r_{s,\alpha}$ 是下表打印的非负整数。

| $s$ | $\sigma$ | $h_s$ | $g_s$ | $r_s$ |
|---|---|---|---|---|
| 1 | 012345 | $(420,1075,730,530,185,1305,1694,1236,620,668,844,546,468,604,415,650,1374,975,576,1072,1266,932,345,468,274,348,560,484,222,358,146,10,15,5)$ | $3/2$ | $(29400,104300,70280,47320,13300,166400,216450,149930,60670,68158,83484,47870,29968,45435,29900,137500,281110,194610,96430,189986,228704,146024,61610,82276,44810,46376,71060,61666,21384,45224,23090,0,0,750,46000,134940,92000,49060,152178,188330,115744,49100,59510,23358,83536,144026,100180,63590,87584,30844,3100,6450,3350,20298,47696,33496,35698,47746,14398,9500,16650,7150,0,2325,0)$ |
| 2 | 012354 | $(420,1075,730,530,345,1305,1694,1236,616,668,844,298,468,332,279,650,1374,975,399,1072,1266,334,345,222,151,348,560,76,222,86,10,10,15,5)$ | $3/2$ | $(29400,104300,70280,47320,34020,166400,216450,149930,89260,68158,82256,35614,31168,15701,13808,137500,281110,194610,98180,189986,228704,82680,61610,40944,24144,46376,71060,9394,21384,0,0,0,0,0,46000,134940,92000,42940,152178,188330,72586,49100,38690,12823,83536,144026,43846,63590,39596,6850,3100,2850,0,20298,47696,14200,35698,23650,1975,9500,11850,1122,0,0,0)$ |
| 3 | 012435 | $(420,1075,730,385,185,1305,1694,1078,620,668,1038,546,649,772,415,650,1374,975,576,1072,1810,932,889,1012,274,348,968,484,902,902,146,282,423,141)$ | $3$ | $(14700,52150,35140,18130,6650,83200,108225,63595,30335,34079,50351,23935,25326,31080,14950,68750,140555,91465,48215,94993,148646,73012,65725,76684,22405,23188,64867,30833,59795,62144,11545,18116,29286,11170,23000,67470,46000,24530,76089,115885,57872,46270,51475,11679,41768,103381,50090,84883,87232,15422,23270,37017,13747,10149,33496,16748,40769,40769,7199,21646,32469,10823,4224,8448,4224)$ |
| 4 | 012453 | $(420,1075,730,385,200,1305,1694,1078,458,668,1038,492,649,526,292,650,1374,975,399,1072,1810,878,889,766,151,348,968,484,902,902,146,282,423,141)$ | $3$ | $(14700,52150,35140,18130,11480,83200,108225,63595,33260,34079,50351,26416,25326,19572,9196,68750,140555,91465,43250,94993,148646,75634,65725,54766,11446,23188,64867,34034,59795,57446,9196,18116,25062,6946,23000,67470,46000,21470,76089,115885,58013,46270,41065,6474,41768,103381,53291,84883,82534,13073,23270,32793,9523,10149,33496,16748,40769,40769,7199,21646,32469,10823,4224,8448,4224)$ |
| 5 | 012534 | $(420,1075,730,545,345,1305,1694,1074,616,668,790,298,537,524,279,650,1374,798,399,1072,1212,334,414,414,151,348,560,76,222,86,10,10,15,5)$ | $3/2$ | $(29400,104300,70280,56980,34020,166400,216450,155780,89260,68158,88446,35614,50188,49904,17733,137500,281110,184680,98180,189986,233948,82680,88772,90024,24144,46376,77462,9394,38886,19744,0,7800,11100,3300,46000,134940,85880,42940,152178,188612,72586,59792,59792,12948,83536,150428,43846,81092,61796,6850,14200,21300,7100,20298,47696,14200,35698,23650,1975,9500,11850,2350,1200,2400,1200)$ |
| 6 | 012543 | $(420,1075,730,545,200,1305,1694,1074,458,668,790,492,537,550,292,650,1374,798,399,1072,1212,878,414,414,151,348,560,484,222,358,146,10,15,5)$ | $3$ | $(14700,52150,35140,28490,11480,83200,108225,77890,33260,34079,44223,26416,25094,25236,9196,68750,140555,92340,43250,94993,116974,75634,44386,43760,11446,23188,38731,34034,19443,29014,9196,3900,6150,2250,23000,67470,42940,21470,76089,94306,58013,29896,29896,6474,41768,75214,53291,40546,50194,13073,7100,10650,3550,10149,23848,16748,17849,23873,7199,4750,8325,3575,600,1200,600)$ |
| 7 | 013245 | $(420,1075,875,530,185,1305,2152,1236,620,1139,1328,678,468,604,415,650,1551,975,576,1303,1374,688,345,468,274,402,545,253,153,140,133,10,15,5)$ | $3/2$ | $(29400,104300,81340,47320,13300,166400,266280,149930,60670,118272,133882,58310,29718,44735,29900,137500,326000,194610,96430,262392,283736,129112,61610,82276,44810,73892,107518,46574,30326,31952,22470,0,0,750,46000,141060,92000,49060,160128,185870,90946,49100,59510,23358,81076,121886,53758,43910,44336,19222,3100,6450,3350,16008,28016,11872,7608,4972,3612,0,0,0,0,125,0)$ |
| 8 | 013254 | $(420,1075,875,530,345,1305,2152,1236,616,1139,1328,650,468,332,279,650,1551,975,399,1303,1374,686,345,222,151,402,545,292,153,166,146,10,15,5)$ | $3/2$ | $(29400,104300,81340,47320,34020,166400,266280,149930,89260,118272,133882,75572,30218,14576,14058,137500,326000,194610,98180,262392,283736,154624,61610,40944,24144,73892,107518,60944,30326,28700,20844,0,0,0,46000,141060,92000,42940,160128,185870,94924,49100,38690,12698,81076,121886,68128,43910,43484,18796,3100,2850,0,16008,28016,16144,7508,10519,6948,0,0,0,0,0,0)$ |
| 9 | 013425 | $(420,1075,875,530,185,1305,2152,1536,620,1139,1628,678,768,904,415,650,1551,1152,576,1303,1920,688,768,768,274,402,914,253,768,632,133,256,384,128)$ | $3$ | $(14700,52150,40670,23660,6650,83200,133140,88510,30335,59136,80486,29155,30404,36300,14950,68750,163000,113910,48215,131196,185080,64556,65956,68228,22405,36946,80366,23287,60316,53068,11235,16896,27756,10860,23000,70530,49060,24530,80064,112666,45473,39076,39076,11679,40538,87550,26879,62884,50812,9611,15872,23808,7936,8004,23944,5936,27332,18884,2156,14848,19860,5012,3456,6912,3456)$ |
| 10 | 013452 | $(420,1075,875,530,345,1305,2152,1536,916,1139,1628,950,768,632,279,650,1551,1152,576,1303,1920,1232,768,768,274,402,914,661,768,904,269,256,384,128)$ | $3$ | $(14700,52150,40670,23660,17010,83200,133140,88510,58175,59136,80486,51331,30404,24508,9054,68750,163000,113910,65695,131196,185080,120524,65956,63684,20133,36946,80366,57079,60316,67564,18483,16896,22932,6036,23000,70530,49060,24530,80064,112666,67193,39076,39076,11679,40538,87550,60671,62884,74956,21683,15872,23808,7936,8004,23944,18008,27332,35780,10604,14848,24684,9836,3456,6912,3456)$ |
| 11 | 013524 | $(420,1075,875,690,345,1305,2152,1532,616,1139,1600,650,876,876,279,650,1551,975,399,1303,1918,686,889,766,151,402,953,292,833,710,146,282,423,141)$ | $3$ | $(14700,52150,40670,34020,17010,83200,133140,102805,44630,59136,89117,37786,44931,44931,9054,68750,163000,114785,49090,131196,197836,77312,89045,80984,12072,36946,87551,30472,75499,67438,10422,24894,37341,12447,23000,70530,46000,21470,80064,114655,47462,46270,41065,6474,40538,94735,34064,77467,65182,9398,23270,32793,9523,8004,26080,8072,32372,25292,3524,18520,25668,7148,4224,8448,4224)$ |
| 12 | 013542 | $(420,1075,875,690,345,1305,2152,1532,916,1139,1600,950,876,876,279,650,1551,975,576,1303,1918,1232,889,1012,274,402,953,661,833,956,269,282,423,141)$ | $3$ | $(14700,52150,40670,34020,17010,83200,133140,102805,58175,59136,89117,51331,44931,44931,9054,68750,163000,114785,65695,131196,197836,120524,89045,97106,20133,36946,87551,57079,75499,83560,18483,24894,37341,12447,23000,70530,46000,24530,80064,114655,67193,46270,51475,11679,40538,94735,60671,77467,89752,21683,23270,37017,13747,8004,26080,18008,32372,39452,10604,18520,29892,11372,4224,8448,4224)$ |
| 13 | 014235 | $(420,1075,730,385,185,1305,1994,1078,620,968,1338,846,649,772,415,650,1551,975,576,1303,1918,1232,889,1012,274,402,953,661,833,956,269,282,423,141)$ | $3$ | $(14700,52150,35140,18130,6650,83200,121770,63595,30335,47624,63896,37480,25326,31080,14950,68750,157160,91465,48215,120142,165734,100102,65725,76684,22405,31732,73894,49862,60278,73112,22030,18116,29286,11170,23000,70530,46000,24530,80064,114655,67193,46270,51475,11679,40538,94735,60671,77467,89752,21683,23270,37017,13747,8004,26080,18008,32372,39452,10604,18520,29892,11372,4224,8448,4224)$ |
| 14 | 014253 | $(420,1075,730,385,200,1305,1994,1078,458,968,1338,492,649,526,292,650,1551,975,399,1303,1918,686,889,766,151,402,953,292,833,710,146,282,423,141)$ | $3$ | $(14700,52150,35140,18130,11480,83200,121770,63595,33260,47624,63896,26416,25326,19572,9196,68750,157160,91465,43250,120142,165734,65632,65725,54766,11446,31732,73894,24032,60278,47444,9196,18116,25062,6946,23000,70530,46000,21470,80064,114655,47462,46270,41065,6474,40538,94735,34064,77467,65182,9398,23270,32793,9523,8004,26080,8072,32372,25292,3524,18520,25668,7148,4224,8448,4224)$ |
| 15 | 014325 | $(420,1075,730,530,185,1305,1994,1536,620,968,1444,846,768,904,415,650,1551,1152,576,1303,1920,1232,768,768,274,402,914,661,768,904,269,256,384,128)$ | $3$ | $(14700,52150,35140,23660,6650,83200,121770,88510,30335,47624,68832,37480,30404,36300,14950,68750,157160,113910,48215,120142,174652,100102,65956,68228,22405,31732,71164,49862,56328,70672,22030,16896,27756,10860,23000,70530,49060,24530,80064,112666,67193,39076,39076,11679,40538,87550,60671,62884,74956,21683,15872,23808,7936,8004,23944,18008,27332,35780,10604,14848,24684,9836,3456,6912,3456)$ |
| 16 | 014352 | $(420,1075,730,530,345,1305,1994,1536,916,968,1444,598,768,632,279,650,1551,1152,576,1303,1920,688,768,768,274,402,914,253,768,632,133,256,384,128)$ | $3$ | $(14700,52150,35140,23660,17010,83200,121770,88510,58175,47624,68832,31352,30404,24508,9054,68750,157160,113910,65695,120142,174652,74550,65956,63684,20133,31732,71164,21302,56328,41984,7686,16896,22932,6036,23000,70530,49060,24530,80064,112666,45473,39076,39076,11679,40538,87550,26879,62884,50812,9611,15872,23808,7936,8004,23944,5936,27332,18884,2156,14848,19860,5012,3456,6912,3456)$ |
| 17 | 014523 | $(420,1075,730,545,200,1305,1994,1374,458,968,1090,492,537,550,292,650,1551,975,399,1303,1374,686,345,222,151,402,545,292,153,166,146,10,15,5)$ | $3/2$ | $(29400,104300,70280,56980,22960,166400,243540,182870,66520,95248,115536,52832,50188,50472,18392,137500,314320,217890,86500,240284,280364,131264,84890,67516,22892,63464,90668,48064,35004,38024,18392,7800,12300,4500,46000,141060,92000,42940,160128,185870,94924,49100,38690,12823,81076,121886,68128,43910,43484,18796,3100,2850,0,16008,28016,16144,7508,11944,6948,0,0,0,400,2400,75)$ |
| 18 | 014532 | $(420,1075,730,545,345,1305,1994,1374,916,968,1090,598,537,524,279,650,1551,975,576,1303,1374,688,345,468,274,402,545,253,153,140,133,10,15,5)$ | $3$ | $(14700,52150,35140,28490,17010,83200,121770,91435,58175,47624,57768,31352,25094,24952,9054,68750,157160,108945,65695,120142,140182,74550,42445,51132,20133,31732,45334,21302,17502,15992,7686,3900,5550,1650,23000,70530,46000,24530,80064,92935,45473,24550,29755,11679,40538,60943,26879,21955,22168,9611,1550,3225,1675,8004,14008,5936,3954,2736,1806,0,0,0,200,700,0)$ |
| 19 | 015234 | $(420,1075,890,545,345,1305,1990,1074,616,1100,1358,842,537,524,279,650,1374,798,399,1072,1212,878,414,414,151,348,560,484,222,358,146,10,15,5)$ | $3$ | $(14700,52150,45500,28490,17010,83200,136065,77890,44630,67815,83855,51775,25094,24952,9054,68750,158035,92340,49090,132225,156478,101852,44386,45012,12072,42940,75683,53137,36643,46240,14097,3900,5550,1650,23000,67470,42940,21470,76089,94306,58013,29896,29896,6474,41768,75214,53291,40546,50194,13073,7100,10650,3550,10149,23848,16748,17849,23873,7199,4750,8325,3575,600,1200,600)$ |
| 20 | 015243 | $(420,1075,890,545,200,1305,1990,1074,458,1100,1358,516,537,550,292,650,1374,798,399,1072,1212,334,414,414,151,348,560,76,222,86,10,10,15,5)$ | $3$ | $(14700,52150,45500,28490,11480,83200,136065,77890,33260,67815,83855,32080,25094,25236,9196,68750,158035,92340,43250,132225,156478,54626,44386,43760,11446,42940,75683,22546,36643,27046,4500,3900,6150,2250,23000,67470,42940,21470,76089,94306,36293,29896,29896,6474,41768,75214,21923,40546,30898,3425,7100,10650,3550,10149,23848,7100,17849,11825,1175,4750,5925,1175,600,1200,600)$ |
| 21 | 015324 | $(420,1075,890,690,345,1305,1990,1532,616,1100,1684,842,876,876,279,650,1374,975,399,1072,1810,878,889,766,151,348,968,484,902,902,146,282,423,141)$ | $3$ | $(14700,52150,45500,34020,17010,83200,136065,102805,44630,67815,103550,51775,44931,44931,9054,68750,158035,114785,49090,132225,209824,101852,89045,80984,12072,42940,106274,53137,88228,88228,14097,24894,37341,12447,23000,67470,46000,21470,76089,115885,58013,46270,41065,6474,41768,103381,53291,84883,82534,13073,23270,32793,9523,10149,33496,16748,40769,40769,7199,21646,32469,10823,4224,8448,4224)$ |
| 22 | 015342 | $(420,1075,890,690,345,1305,1990,1532,916,1100,1684,842,876,876,279,650,1374,975,576,1072,1810,932,889,1012,274,348,968,484,902,902,146,282,423,141)$ | $3$ | $(14700,52150,45500,34020,17010,83200,136065,102805,58175,67815,103550,51775,44931,44931,9054,68750,158035,114785,65695,132225,209824,107972,89045,97106,20133,42940,106274,53137,88228,88228,14097,24894,37341,12447,23000,67470,46000,24530,76089,115885,57872,46270,51475,11679,41768,103381,50090,84883,87232,15422,23270,37017,13747,10149,33496,16748,40769,40769,7199,21646,32469,10823,4224,8448,4224)$ |
| 23 | 015423 | $(420,1075,890,545,200,1305,1990,1374,458,1100,1358,516,537,550,292,650,1374,975,399,1072,1266,334,345,222,151,348,560,76,222,86,10,10,15,5)$ | $3/2$ | $(29400,104300,91000,56980,22960,166400,272130,182870,66520,135630,167710,64160,50188,50472,18392,137500,316070,217890,86500,264450,325196,109252,84890,67516,22892,85880,151366,45092,73286,54092,9000,7800,12300,4500,46000,134940,92000,42940,152178,188330,72586,49100,38690,12823,83536,144026,43846,63590,39596,6850,3100,2850,0,20298,47696,14200,35698,23650,2350,9500,11850,2350,1200,2400,1075)$ |
| 24 | 015432 | $(420,1075,890,545,345,1305,1990,1374,916,1100,1358,842,537,524,279,650,1374,975,576,1072,1266,932,345,468,274,348,560,484,222,358,146,10,15,5)$ | $3$ | $(14700,52150,45500,28490,17010,83200,136065,91435,58175,67815,83855,51775,25094,24952,9054,68750,158035,108945,65695,132225,162598,107972,42445,51132,20133,42940,75683,53137,36643,46240,14097,3900,5550,1650,23000,67470,46000,24530,76089,94165,57872,24550,29755,11679,41768,72013,50090,31795,43792,15422,1550,3225,1675,10149,23848,16748,17849,23873,7199,4750,8325,3575,600,1200,600)$ |
| 25 | 021345 | $(420,915,730,530,185,849,1102,668,296,668,844,546,468,604,415,354,646,407,239,640,698,582,345,494,287,348,560,484,222,358,146,10,15,5)$ | $3/2$ | $(29400,83580,70280,47320,13300,92448,130706,75514,27100,68158,83484,47870,29968,45435,29900,51756,90838,46034,26372,85458,80384,73048,27210,53968,38080,46376,71060,61666,21384,45224,23090,0,0,750,13488,30412,17840,12572,40658,40266,41050,14700,28130,15092,44032,70122,61974,29190,53132,21042,3100,7650,4550,20298,47696,33496,35698,47746,14398,9500,16650,7150,0,2325,0)$ |
| 26 | 021354 | $(420,915,730,530,345,849,1102,668,372,668,844,298,468,332,279,354,646,407,168,640,698,116,345,196,138,348,560,76,222,86,10,10,15,5)$ | $3/2$ | $(29400,83580,70280,47320,34020,92448,130706,75514,48414,68158,82256,35614,31168,15701,476,51756,90838,46034,19662,85458,80384,7336,27210,452,11322,46376,71060,9394,21384,0,0,0,0,0,13488,30412,17840,4876,40658,40266,0,14700,1270,0,44032,70122,7756,29190,5248,0,3100,1650,0,20298,47696,14200,35698,23650,0,9500,11850,1122,0,0,0)$ |
| 27 | 021435 | $(420,915,730,385,185,849,1102,730,296,668,1038,546,649,772,415,354,646,478,239,640,1164,582,662,662,287,348,968,484,902,902,146,282,423,141)$ | $3$ | $(14700,41790,35140,18130,6650,46224,65353,41146,13550,34079,50351,23935,25326,31080,14950,25878,45419,35588,13186,42729,81790,36524,44722,47620,19040,23188,64867,30833,59795,62144,11545,18116,29286,11170,6744,15206,12572,6286,20329,41050,20525,21552,21552,7546,22016,61974,30987,56450,56450,10521,16492,24738,8246,10149,33496,16748,40769,40769,7199,21646,32469,10823,4224,8448,4224)$ |
| 28 | 021453 | $(420,915,730,385,200,849,1102,730,434,668,1038,492,649,526,292,354,646,478,239,640,1164,582,662,662,287,348,968,484,902,902,146,282,423,141)$ | $3$ | $(14700,41790,35140,18130,11480,46224,65353,41146,27596,34079,50351,26416,25326,19572,9196,25878,45419,35588,22402,42729,81790,45266,44722,41824,16142,23188,64867,34034,59795,57446,9196,18116,25062,6946,6744,15206,12572,6286,20329,41050,20525,21552,21552,7546,22016,61974,30987,56450,56450,10521,16492,24738,8246,10149,33496,16748,40769,40769,7199,21646,32469,10823,4224,8448,4224)$ |
| 29 | 021534 | $(420,915,730,545,345,849,1102,806,372,668,790,298,537,524,279,354,646,407,168,640,698,116,345,196,138,348,560,76,222,86,10,10,15,5)$ | $3/2$ | $(29400,83580,70280,56980,34020,92448,130706,103606,48414,68158,88446,35614,50188,49904,17681,51756,90838,64466,19662,85458,97868,7336,50490,29528,11322,46376,77462,9394,38886,19744,0,7800,11100,3300,13488,30412,17840,4876,40658,40266,0,14700,1270,0,44032,70122,7756,29190,5248,0,3100,1650,0,20298,47696,14200,35698,23650,0,9500,11850,2350,1200,2400,0)$ |
| 30 | 021543 | $(420,915,730,545,200,849,1102,806,434,668,790,492,537,550,292,354,646,407,239,640,698,582,345,494,287,348,560,484,222,358,146,10,15,5)$ | $3$ | $(14700,41790,35140,28490,11480,46224,65353,51803,27596,34079,44223,26416,25094,25236,9196,25878,45419,32233,22402,42729,48934,45266,25245,35726,16142,23188,38731,34034,19443,29014,9196,3900,6150,2250,6744,15206,8920,6286,20329,20133,20525,7350,14065,7546,22016,35061,30987,14595,26566,10521,1550,3825,2275,10149,23848,16748,17849,23873,7199,4750,8325,3575,600,1200,600)$ |
| 31 | 023145 | $(420,915,715,530,185,849,1264,668,296,707,760,354,468,604,415,354,823,407,239,871,806,390,345,494,287,402,545,292,153,166,146,10,15,5)$ | $3/2$ | $(29400,83580,60620,47320,13300,92448,129704,75514,27100,55648,59466,24740,27981,44435,29900,51756,110464,46034,26372,97944,66104,33664,27210,53968,38080,39236,38462,21184,0,3644,15740,0,0,750,13488,41380,17840,12572,58304,42654,24796,14700,28130,15092,46420,52830,28368,9510,18428,13692,3100,7650,4550,16008,28016,16144,4671,11944,6948,0,0,0,0,1325,0)$ |
| 32 | 023154 | $(420,915,715,530,345,849,1264,668,372,707,760,406,468,332,279,354,823,407,168,871,806,416,345,196,138,402,545,253,153,140,133,10,15,5)$ | $3/2$ | $(29400,83580,60620,47320,34020,92448,129704,75514,48414,55648,59466,34726,25145,10278,10008,51756,110464,46034,19662,97944,66104,32440,27210,452,11322,39236,38462,17278,0,0,8022,0,0,0,13488,41380,17840,5268,58304,42654,17858,14700,1270,0,46420,52830,24462,9510,592,4774,3100,1650,0,16008,28016,11872,5571,488,0,0,0,0,0,0,0)$ |
| 33 | 023415 | $(420,915,715,370,185,849,1264,892,296,707,1008,354,580,580,415,354,823,655,239,871,1326,390,593,470,287,402,953,292,833,710,146,282,423,141)$ | $3$ | $(14700,41790,30310,13300,6650,46224,64852,40645,13550,27824,38285,12370,19515,19515,14950,25878,55232,45401,13186,48972,81724,16832,38413,27928,19040,19618,50215,10592,45587,35102,7870,14990,22485,7495,6744,20690,18056,6286,29152,49375,12398,21054,13425,7546,23210,57399,14184,47555,32846,6846,13366,17937,4571,8004,26080,8072,32372,25292,3524,18520,25668,7148,4224,8448,4224)$ |
| 34 | 023451 | $(420,915,715,370,185,849,1264,892,596,707,1008,654,580,580,415,354,823,655,416,871,1326,936,593,716,410,402,953,661,833,956,269,282,423,141)$ | $3$ | $(14700,41790,30310,13300,6650,46224,64852,40645,27095,27824,38285,25915,19515,19515,14950,25878,55232,45401,32215,48972,81724,64892,38413,48898,29525,19618,50215,39623,45587,56072,18355,14990,22485,7495,6744,20690,18056,11770,29152,49375,36977,21054,28683,15175,23210,57399,43215,47555,62264,21555,13366,22161,8795,8004,26080,18008,32372,39452,10604,18520,29892,11372,4224,8448,4224)$ |
| 35 | 023514 | $(420,915,715,530,345,849,1264,968,372,707,1060,406,768,632,279,354,823,584,168,871,1352,416,768,496,138,402,914,253,768,632,133,256,384,128)$ | $3$ | $(14700,41790,30310,23660,17010,46224,64852,51302,24207,27824,43278,17363,30404,24508,9054,25878,55232,42046,9831,48972,81112,16220,51180,27316,5661,19618,48262,8639,45540,31196,4011,16896,22932,6036,6744,20690,14404,2634,29152,45906,8929,24300,9956,831,23210,55446,12231,48108,28940,2387,15872,18984,3112,8004,23944,5936,27332,18884,2156,14848,19860,5012,3456,6912,3456)$ |
| 36 | 023541 | $(420,915,715,530,185,849,1264,968,596,707,1060,654,768,904,415,354,823,584,416,871,1352,936,768,1040,410,402,914,661,768,904,269,256,384,128)$ | $3$ | $(14700,41790,30310,23660,6650,46224,64852,51302,27095,27824,43278,25915,30404,36300,14950,25878,55232,42046,32215,48972,81112,64892,51180,75044,29525,19618,48262,39623,45540,59884,18355,16896,27756,10860,6744,20690,14404,11770,29152,45906,36977,24300,38644,15175,23210,55446,43215,48108,67276,21555,15872,28632,12760,8004,23944,18008,27332,35780,10604,14848,24684,9836,3456,6912,3456)$ |
| 37 | 024135 | $(420,915,570,385,185,849,1326,730,296,756,990,522,649,772,415,354,894,478,239,864,1116,558,662,662,287,324,648,324,606,606,282,282,423,141)$ | $3$ | $(14700,41790,24780,18130,6650,46224,68241,41146,13550,31071,41447,20695,25326,31080,14950,25878,67803,35588,13186,63633,78830,37468,44722,47620,19040,21708,42867,22257,39275,44048,18665,18116,29286,11170,6744,24342,12572,6286,33393,39770,19885,21552,21552,7546,20736,40374,20187,36130,36130,12817,16492,24738,8246,4941,13176,6588,15753,15753,5871,11742,17613,5871,4224,8448,4224)$ |
| 38 | 024153 | $(420,915,570,385,200,849,1326,730,434,756,990,468,649,526,292,354,894,478,239,864,1116,558,662,662,287,324,648,324,606,606,282,282,423,141)$ | $3$ | $(14700,41790,24780,18130,11480,46224,68241,41146,27596,31071,41447,20752,25326,19572,9196,25878,67803,35588,22402,63633,78830,41362,44722,41824,16142,21708,42867,20610,39275,34502,13892,18116,25062,6946,6744,24342,12572,6286,33393,39770,19885,21552,21552,7546,20736,40374,20187,36130,36130,12817,16492,24738,8246,4941,13176,6588,15753,15753,5871,11742,17613,5871,4224,8448,4224)$ |
| 39 | 024315 | $(420,915,570,370,185,849,1326,892,296,756,1044,522,580,580,415,354,894,655,239,864,1170,558,593,470,287,324,648,324,606,606,282,282,423,141)$ | $3$ | $(14700,41790,24780,13300,6650,46224,68241,40645,13550,31071,41390,20695,19515,19515,14950,25878,67803,45401,13186,63633,85904,37468,38413,27928,19040,21708,44514,22257,37796,37796,18665,14990,22485,7495,6744,24342,18056,6286,33393,46901,19885,21054,13425,7546,20736,42021,20187,34651,29878,12817,13366,17937,4571,4941,13176,6588,15753,15753,5871,11742,17613,5871,4224,8448,4224)$ |
| 40 | 024351 | $(420,915,570,370,185,849,1326,892,596,756,1044,522,580,580,415,354,894,655,416,864,1170,612,593,716,410,324,648,324,606,606,282,282,423,141)$ | $3$ | $(14700,41790,24780,13300,6650,46224,68241,40645,27095,31071,41390,20695,19515,19515,14950,25878,67803,45401,32215,63633,85904,48436,38413,48898,29525,21708,44514,22257,37796,37796,18665,14990,22485,7495,6744,24342,18056,11770,33393,46901,27016,21054,28683,15175,20736,42021,21834,34651,39424,17590,13366,22161,8795,4941,13176,6588,15753,15753,5871,11742,17613,5871,4224,8448,4224)$ |
| 41 | 024513 | $(420,915,570,385,200,849,1326,1030,434,756,990,468,649,526,292,354,894,655,239,864,1170,558,593,470,287,324,648,324,606,606,282,282,423,141)$ | $3$ | $(14700,41790,24780,18130,11480,46224,68241,54691,27596,31071,41447,20752,25326,19572,9196,25878,67803,54617,22402,63633,89798,41362,45205,31822,16142,21708,42867,20610,39275,34502,13892,18116,25062,6946,6744,24342,18056,6286,33393,46901,19885,21054,13425,7546,20736,42021,20187,34651,29878,12817,13366,17937,4571,4941,13176,6588,15753,15753,5871,11742,17613,5871,4224,8448,4224)$ |
| 42 | 024531 | $(420,915,570,385,185,849,1326,1030,596,756,990,522,649,772,415,354,894,655,416,864,1170,612,593,716,410,324,648,324,606,606,282,282,423,141)$ | $3$ | $(14700,41790,24780,18130,6650,46224,68241,54691,27095,31071,41447,20695,25326,31080,14950,25878,67803,54617,32215,63633,89798,48436,45205,58588,29525,21708,42867,22257,39275,44048,18665,18116,29286,11170,6744,24342,18056,11770,33393,46901,27016,21054,28683,15175,20736,42021,21834,34651,39424,17590,13366,22161,8795,4941,13176,6588,15753,15753,5871,11742,17613,5871,4224,8448,4224)$ |
| 43 | 025134 | $(420,915,730,545,345,849,1402,806,372,968,1090,598,537,524,279,354,823,407,168,871,806,416,345,196,138,402,545,253,153,140,133,10,15,5)$ | $3/2$ | $(29400,83580,70280,56980,34020,92448,157796,103606,48414,95248,115536,62704,50188,49904,18108,51756,128896,64466,19662,140604,132044,61516,50490,29528,11322,63464,90668,42604,35004,31984,15372,7800,11100,3300,13488,41380,17840,5268,58304,42654,17858,14700,1270,487,46420,52830,24462,9510,592,4774,3100,1650,0,16008,28016,11872,8408,4972,3612,0,0,0,400,900,0)$ |
| 44 | 025143 | $(420,915,730,545,200,849,1402,806,434,968,1090,492,537,550,292,354,823,407,239,871,806,390,345,494,287,402,545,292,153,166,146,10,15,5)$ | $3$ | $(14700,41790,35140,28490,11480,46224,78898,51803,27596,47624,57768,26416,25094,25236,9196,25878,64448,32233,22402,70302,66022,35264,25245,35726,16142,31732,45334,24032,17502,19012,9196,3900,6150,2250,6744,20690,8920,6286,29152,21327,12398,7350,14065,7546,23210,26415,14184,4755,9214,6846,1550,3825,2275,8004,14008,8072,3754,5972,3474,0,0,0,200,1200,100)$ |
| 45 | 025314 | $(420,915,730,530,345,849,1402,968,372,968,1444,598,768,632,279,354,823,584,168,871,1352,416,768,496,138,402,914,253,768,632,133,256,384,128)$ | $3$ | $(14700,41790,35140,23660,17010,46224,78898,51302,24207,47624,68832,31352,30404,24508,9054,25878,64448,42046,9831,70302,105340,30758,51180,27316,5661,31732,71164,21302,56328,41984,7686,16896,22932,6036,6744,20690,14404,2634,29152,45906,8929,24300,9956,831,23210,55446,12231,48108,28940,2387,15872,18984,3112,8004,23944,5936,27332,18884,2156,14848,19860,5012,3456,6912,3456)$ |
| 46 | 025341 | $(420,915,730,530,185,849,1402,968,596,968,1444,846,768,904,415,354,823,584,416,871,1352,936,768,1040,410,402,914,661,768,904,269,256,384,128)$ | $3$ | $(14700,41790,35140,23660,6650,46224,78898,51302,27095,47624,68832,37480,30404,36300,14950,25878,64448,42046,32215,70302,105340,74582,51180,75044,29525,31732,71164,49862,56328,70672,22030,16896,27756,10860,6744,20690,14404,11770,29152,45906,36977,24300,38644,15175,23210,55446,43215,48108,67276,21555,15872,28632,12760,8004,23944,18008,27332,35780,10604,14848,24684,9836,3456,6912,3456)$ |
| 47 | 025413 | $(420,915,730,385,200,849,1402,1030,434,968,1338,492,649,526,292,354,823,655,239,871,1326,390,593,470,287,402,953,292,833,710,146,282,423,141)$ | $3$ | $(14700,41790,35140,18130,11480,46224,78898,54691,27596,47624,63896,26416,25326,19572,9196,25878,64448,54617,22402,70302,109846,35264,45205,31822,16142,31732,73894,24032,60278,47444,9196,18116,25062,6946,6744,20690,18056,6286,29152,49375,12398,21054,13425,7546,23210,57399,14184,47555,32846,6846,13366,17937,4571,8004,26080,8072,32372,25292,3524,18520,25668,7148,4224,8448,4224)$ |
| 48 | 025431 | $(420,915,730,385,185,849,1402,1030,596,968,1338,846,649,772,415,354,823,655,416,871,1326,936,593,716,410,402,953,661,833,956,269,282,423,141)$ | $3$ | $(14700,41790,35140,18130,6650,46224,78898,54691,27095,47624,63896,37480,25326,31080,14950,25878,64448,54617,32215,70302,109846,74582,45205,58588,29525,31732,73894,49862,60278,73112,22030,18116,29286,11170,6744,20690,18056,11770,29152,49375,36977,21054,28683,15175,23210,57399,43215,47555,62264,21555,13366,22161,8795,8004,26080,18008,32372,39452,10604,18520,29892,11372,4224,8448,4224)$ |
| 49 | 031245 | $(420,1060,875,530,185,1152,1876,1152,428,1139,1328,678,468,604,415,512,1152,768,384,1042,1044,496,276,276,274,402,545,253,153,140,133,10,15,5)$ | $1/32$ | $(1411200,4542720,3904320,2271360,638400,6043776,10285632,6043776,1801920,5677056,6426336,2798880,1509564,2233980,1429575,4104192,9957120,6156288,2355456,9399744,9555072,3871488,1207296,1809408,1858080,3546816,5160864,2235552,1350048,1465296,1099560,0,0,0,1191936,3575808,2383872,1191936,4344192,4383744,1986816,0,161280,608384,2728704,3344640,1364736,0,0,457856,0,0,0,768384,1344768,569856,404352,259200,31472,0,0,0,0,0,0)$ |
| 50 | 031254 | $(420,1060,875,530,345,1152,1876,1152,724,1139,1328,650,468,332,279,512,1152,768,384,1042,1044,548,276,276,274,402,545,292,153,166,146,10,15,5)$ | $1/32$ | $(1411200,4542720,3904320,2271360,1632960,6043776,10285632,6043776,4241856,5677056,6426336,3627456,1509564,785148,705159,4104192,9957120,6156288,3800832,9399744,9555072,5683584,1207296,605184,1255968,3546816,5160864,2925312,1350048,1234800,984312,0,0,0,1191936,3575808,2383872,1191936,4344192,4383744,2396928,155904,167936,608384,2728704,3344640,1979904,0,276992,758912,0,0,0,768384,1344768,774912,404352,566912,337904,0,0,0,0,0,0)$ |
| 51 | 031425 | $(420,1060,875,530,185,1152,1876,1152,428,1139,1628,678,768,904,415,512,1152,768,384,1042,1536,496,768,768,274,402,914,253,768,632,133,256,384,128)$ | $3$ | $(14700,47320,40670,23660,6650,62956,107142,62956,18770,59136,80486,29155,30404,36300,14950,42752,103720,64128,24536,97914,136624,40328,55168,57440,18730,36946,80366,23287,60316,53068,11235,16896,27756,10860,12416,37248,24832,12416,45252,65536,20696,28288,28288,8004,28424,64648,14216,52096,40024,5936,15872,23808,7936,8004,23944,5936,27332,18884,2156,14848,19860,5012,3456,6912,3456)$ |
| 52 | 031452 | $(420,1060,875,530,345,1152,1876,1152,724,1139,1628,950,768,632,279,512,1152,768,384,1042,1536,1040,768,768,274,402,914,661,768,904,269,256,384,128)$ | $3$ | $(14700,47320,40670,23660,17010,62956,107142,62956,44186,59136,80486,51331,30404,24508,9054,42752,103720,64128,39592,97914,136624,96296,55168,52896,16458,36946,80366,57079,60316,67564,18483,16896,22932,6036,12416,37248,24832,12416,45252,65536,44840,28288,28288,8004,28424,64648,50432,52096,64168,18008,15872,23808,7936,8004,23944,18008,27332,35780,10604,14848,24684,9836,3456,6912,3456)$ |
| 53 | 031524 | $(420,1060,875,690,345,1152,1876,1448,724,1139,1600,650,876,876,279,512,1152,768,384,1042,1588,548,820,820,274,402,953,292,833,710,146,282,423,141)$ | $3$ | $(14700,47320,40670,34020,17010,62956,107142,88372,44186,59136,89117,37786,44931,44931,9054,42752,103720,79184,39592,97914,155500,59204,76316,76316,16458,36946,87551,30472,75499,67438,10422,24894,37341,12447,12416,37248,24832,12416,45252,69808,24968,32560,32560,8004,28424,71056,20624,62776,52840,8072,20144,30216,10072,8004,26080,8072,32372,25292,3524,18520,25668,7148,4224,8448,4224)$ |
| 54 | 031542 | $(420,1060,875,690,345,1152,1876,1448,724,1139,1600,950,876,876,279,512,1152,768,384,1042,1588,1040,820,820,274,402,953,661,833,956,269,282,423,141)$ | $3$ | $(14700,47320,40670,34020,17010,62956,107142,88372,44186,59136,89117,51331,44931,44931,9054,42752,103720,79184,39592,97914,155500,96296,76316,76316,16458,36946,87551,57079,75499,83560,18483,24894,37341,12447,12416,37248,24832,12416,45252,69808,44840,32560,32560,8004,28424,71056,50432,62776,72712,18008,20144,30216,10072,8004,26080,18008,32372,39452,10604,18520,29892,11372,4224,8448,4224)$ |
| 55 | 032145 | $(420,1060,715,530,185,1152,1580,1152,428,707,760,354,468,604,415,512,1152,768,384,1042,1044,548,276,276,274,402,545,292,153,166,146,10,15,5)$ | $1/32$ | $(1411200,4542720,2909760,2271360,638400,6043776,7845696,6043776,1801920,2671104,2854368,1187520,1358988,2233980,1429575,4104192,8511744,6156288,2355456,6290880,6228096,2792832,1207296,1809408,1858080,1883328,1846176,1016832,0,185712,758520,0,0,0,1191936,3575808,2383872,1191936,4344192,4383744,2396928,155904,167936,608384,2728704,3344640,1979904,0,276992,758912,0,0,0,768384,1344768,774912,253776,566912,337904,0,0,0,0,0,0)$ |
| 56 | 032154 | $(420,1060,715,530,345,1152,1580,1152,724,707,760,406,468,332,279,512,1152,768,384,1042,1044,496,276,276,274,402,545,253,153,140,133,10,15,5)$ | $1/32$ | $(1411200,4542720,2909760,2271360,1632960,6043776,7845696,6043776,4241856,2671104,2854368,1666848,1171612,681852,601823,4104192,8511744,6156288,3800832,6290880,6228096,3435264,1207296,605184,1255968,1883328,1846176,829344,0,0,271656,0,0,0,1191936,3575808,2383872,1191936,4344192,4383744,1986816,155904,5376,608384,2728704,3344640,1364736,0,0,457856,0,0,0,768384,1344768,569856,150440,0,0,0,0,0,0,0,0)$ |
| 57 | 032415 | $(420,1060,715,370,185,1152,1580,856,428,707,1008,354,580,580,415,512,1152,768,384,1042,1588,548,820,820,274,402,953,292,833,710,146,282,423,141)$ | $3$ | $(14700,47320,30310,13300,6650,62956,81726,37540,18770,27824,38285,12370,19515,19515,14950,42752,88664,49072,24536,65530,95276,29092,46204,46204,18730,19618,50215,10592,45587,35102,7870,14990,22485,7495,12416,37248,24832,12416,45252,69808,24968,32560,32560,8004,28424,71056,20624,62776,52840,8072,20144,30216,10072,8004,26080,8072,32372,25292,3524,18520,25668,7148,4224,8448,4224)$ |
| 58 | 032451 | $(420,1060,715,370,185,1152,1580,856,428,707,1008,654,580,580,415,512,1152,768,384,1042,1588,1040,820,820,274,402,953,661,833,956,269,282,423,141)$ | $3$ | $(14700,47320,30310,13300,6650,62956,81726,37540,18770,27824,38285,25915,19515,19515,14950,42752,88664,49072,24536,65530,95276,66184,46204,46204,18730,19618,50215,39623,45587,56072,18355,14990,22485,7495,12416,37248,24832,12416,45252,69808,44840,32560,32560,8004,28424,71056,50432,62776,72712,18008,20144,30216,10072,8004,26080,18008,32372,39452,10604,18520,29892,11372,4224,8448,4224)$ |
| 59 | 032514 | $(420,1060,715,530,345,1152,1580,1152,724,707,1060,406,768,632,279,512,1152,768,384,1042,1536,496,768,768,274,402,914,253,768,632,133,256,384,128)$ | $3$ | $(14700,47320,30310,23660,17010,62956,81726,62956,44186,27824,43278,17363,30404,24508,9054,42752,88664,64128,39592,65530,101968,35784,55168,52896,16458,19618,48262,8639,45540,31196,4011,16896,22932,6036,12416,37248,24832,12416,45252,65536,20696,28288,28288,8004,28424,64648,14216,52096,40024,5936,15872,23808,7936,8004,23944,5936,27332,18884,2156,14848,19860,5012,3456,6912,3456)$ |
| 60 | 032541 | $(420,1060,715,530,185,1152,1580,1152,428,707,1060,654,768,904,415,512,1152,768,384,1042,1536,1040,768,768,274,402,914,661,768,904,269,256,384,128)$ | $3$ | $(14700,47320,30310,23660,6650,62956,81726,62956,18770,27824,43278,25915,30404,36300,14950,42752,88664,64128,24536,65530,101968,66184,55168,57440,18730,19618,48262,39623,45540,59884,18355,16896,27756,10860,12416,37248,24832,12416,45252,65536,44840,28288,28288,8004,28424,64648,50432,52096,64168,18008,15872,23808,7936,8004,23944,18008,27332,35780,10604,14848,24684,9836,3456,6912,3456)$ |

为了直接核对 (18.10) 与原矩多项式的对应，令
$\mathcal O_\alpha(v)=\sum_{\beta\in\operatorname{Orb}(\alpha)}v^\beta$，
其中 $\operatorname{Orb}(\alpha)$ 是循环移动和反射得到的**不同**六位指标集合，
每个单项式只计一次。完整四次式是

$$
\begin{aligned}
D(v)={}&1800\mathcal O_{000022}+7125\mathcal O_{000112}
 -75\mathcal O_{000121}+12672\mathcal O_{000202}\\
&-5700\mathcal O_{001012}-3900\mathcal O_{001021}
 +8772\mathcal O_{001102}+1194\mathcal O_{001111}\\
&+10368\mathcal O_{002002}-7731\mathcal O_{010102}
 -21078\mathcal O_{010111}-9120\mathcal O_{011011}.
\end{aligned} \tag{18.11}
$$

在 (18.11) 代入 $v_{\sigma_j}=\sum_{i=1}^j x_i$，减去乘数表中逐行列出的
(18.8) 以及 (18.9)，所得全部余项系数就是 $g_sr_s$。
$h_s$ 是 (18.3) 的 $J(v^\sigma(x))/210$ 的全部系数；
$I_3,I_4$ 外的系数均为零。因此 (18.3)、(18.8)–(18.11)
打印了恒等式的完整指标、乘数和系数，并给出每个非负项的具体形式。

由 (18.10)，每个 $v\ge0$ 且 $\min_jv_j=0$ 都有 $D(v),J(v)\ge0$。
又 $K(v)\ge0$，故 (18.5) 证明 $D(p)\ge0$，包括闭单纯形的全部边界。
这同时覆盖 $11a-8b-3c$ 的两种符号，没有附加矩区域限制。
非正分支的另一因子还可独立核对：令

$$
U_1=\sum_{j=0}^5p_jp_{j+1},\quad
U_2=\sum_{j=0}^5p_jp_{j+2},\quad
U_3=\sum_{j=0}^2p_jp_{j+3},
$$

下标模六，则对严格正 $p$，

$$
11a-8b-3c=25U_1-9U_2-32U_3,\qquad
70-72a+11b-9c=75U_1+183U_2+324U_3>0.
\tag{18.12}
$$

所以第一因子非正时，乘积确实非正。

最后，若 $p_j>0$，则 $m>0$；(18.5) 的三项非负，
故 $D(p)=0$ 蕴含 $K(v)=0$。由 (18.3) 中三个严格正系数，
$Q_1(v)=Q_2(v)=Q_3(v)=0$。
实向量的另外两个非恒定 Fourier 矩是 $Q_2,Q_1$ 的共轭，
所以 Fourier 反演使 $v$ 为常向量；而 $\min_jv_j=0$，故 $v=0$。
于是 $p=m\mathbf1$，由 $S_p=1$ 得 $p_j=1/6$。
均匀向量的全部非恒定矩为零，反向直接给出 $D(p)=0$。
这证明 (18.2) 及完整的严格正零集。证毕。

**定理 18.3（六边形的尖锐全局界与全部等号）。** 对每个独立有限严格正
电导向量 $c=(c_0,\ldots,c_5)$，有

$$
\lambda_2(L(c))R(c)\le\frac{35}{2}.
\tag{18.6}
$$

等号当且仅当存在 $\gamma>0$ 使

$$
c_0=c_1=c_2=c_3=c_4=c_5=\gamma .
\tag{18.7}
$$

**证明。** 记 $\rho=\lambda_{\max}(M(p)|_H)$，并置
$t=12T(p)/35$。在式 (9.2) 的 Fourier 基中取指标 $1,2$ 的主压缩 $A$。
因为 $|1-z^{-1}|=1$、$|1-z^{-2}|=\sqrt3$，有

$$
A=\begin{pmatrix}
 (1-a)/6 & (q_1-\overline q_1q_2)/(6\,\overline d_1d_2)\\[2mm]
 (\overline q_1-q_1\overline q_2)/(6\,d_1\overline d_2)&(1-b)/18
\end{pmatrix} .
$$

由 (18.1)，直接计算

$$
t-A_{11}=\frac{11a-8b-3c}{210},\qquad
t-A_{22}=\frac{70-72a+11b-9c}{630},\qquad
|A_{12}|^2=\frac{|q_1-\overline q_1q_2|^2}{108}.
$$

因此引理 18.2 等价于
$\det(tI_2-A)\le0$。两个特征值为实数，故
$\lambda_{\max}(A)\ge t$。Cauchy 交错给出
$\rho\ge\lambda_{\max}(A)\ge t$，从而

$$
\Phi(p)=\frac{6T(p)}\rho\le\frac{6T(p)}{12T(p)/35}=\frac{35}{2}.
$$

若等号成立，则每个不等式均为等号，特别是引理 18.2 取等号；严格正性
遂给出 $p_i=1/6$。由 $p_i=c_i^{-1}/\sum_jc_j^{-1}$，这等价于 (18.7)。
反之，单位六边形的非零谱为 $1,1,3,3,4$，故
$\operatorname{tr}L(\mathbf1)^+=35/12$、$R(\mathbf1)=6\cdot35/12=35/2$
且 $\lambda_2(L(\mathbf1))=1$。电导缩放律遂给出每个常向量均取等号。
证毕。

## 19. 归一化序列与固定电阻的完整等号类

**定理 19.1（全部正序列的等号判别）。** 令 $c[k]\in(0,\infty)^6$ 为任意
正电导序列，并记 $\lambda_k=\lambda_2(L(c[k]))$。则

$$
\lambda_kR(c[k])\longrightarrow\frac{35}{2}
$$

当且仅当

$$
\left(\frac{c_0[k]}{\lambda_k},\ldots,
\frac{c_5[k]}{\lambda_k}\right)\longrightarrow(1,1,1,1,1,1).
\tag{19.1}
$$

**证明。** 对每个 $k$ 置 $r_i[k]=c_i[k]^{-1}$、
$s_k=\sum_ir_i[k]$、$p_i[k]=r_i[k]/s_k$。由 (5.5)，

$$
\lambda_kR(c[k])=\Phi(p[k]),\qquad
\frac{c_i[k]}{\lambda_k}=\frac{\rho(p[k])}{p_i[k]} .
\tag{19.2}
$$

若左式趋于 $35/2$，定理 7.2 给出一个只依赖于 $n=6$ 的
$\delta>0$，使充分大的 $k$ 满足 $p_i[k]\ge\delta$。因此这些 $p[k]$
落在紧子集上；取任意收敛子列 $p[k_j]\to p^*$，连续性与定理 18.3
给出 $\Phi(p^*)=35/2$，故 $p^*$ 为均匀向量。每个收敛子列均有同一
极限，所以 $p[k]\to(1/6,\ldots,1/6)$。再由连续性
$\rho(p[k])\to1/6$，式 (19.2) 即得 (19.1)。

反过来，若 (19.1) 成立，则归一化电导
$\widehat c[k]=c[k]/\lambda_k$ 逐坐标趋于单位向量。其 Laplacian
特征值连续，且 $\lambda_2(L(\widehat c[k]))=1$；全点对电阻也是正定
矩阵伪逆的连续函数，故

$$
\lambda_kR(c[k])=R(\widehat c[k])
\longrightarrow R(\mathbf1)=\frac{35}{2}.
$$
证毕。

**推论 19.2（固定全点对电阻的唯一原始等号向量）。** 对每个 $R_0>0$，

$$
\max_{\substack{c_i>0\\ R(c)=R_0}}\lambda_2(L(c))
=\frac{35}{2R_0},
\tag{19.3}
$$

且唯一的带标号最大向量为

$$
c_0=c_1=c_2=c_3=c_4=c_5=\frac{35}{2R_0}.
\tag{19.4}
$$

对每条满足 $R(c[k])=R_0$ 的有限严格正原始电导序列，
$\lambda_2(L(c[k]))\to35/(2R_0)$ 当且仅当
$c[k]\to(35/(2R_0))(1,1,1,1,1,1)$。

**证明。** 由 (18.6) 及 $R(c)=R_0$，有
$\lambda_2(L(c))\le35/(2R_0)$。令每条边电导为
$35/(2R_0)$；由 $R(\mathbf1)=35/2$ 及缩放律，其总电阻为 $R_0$，
并取到右端。等号时 (18.7) 给出唯一性，且保留原始标签。

对任意 $R(c[k])=R_0$ 的有限严格正原始电导序列，置
$\gamma=35/(2R_0)$，则

$$
\lambda_2(L(c[k]))\longrightarrow\gamma
\quad\Longleftrightarrow\quad
c[k]\longrightarrow\gamma(1,1,1,1,1,1).
\tag{19.5}
$$

左向右时，$\lambda_kR(c[k])\to35/2$，定理 19.1 给出
$c[k]/\lambda_k\to\mathbf1$；乘以 $\lambda_k\to\gamma$ 即得右式。
右向左时，Laplacian 特征值的连续性及
$\lambda_2(L(\gamma\mathbf1))=\gamma$ 给出左式。
这是每条可行序列的充要条件，不另加有界性或尺度假设。证毕。

**约定 19.3（来源、边界输入与未决阶数）。**
式 (5.4)–(5.5)、(9.2) 的原始参数对应始终保留：六个顶点的计数质量为一，
六条原边电导独立为有限正数，$R$ 是全部十五个原始无序点对之和。
[Ghosh–Boyd–Saberi，DOI:10.1137/050645452](https://web.stanford.edu/~boyd/papers/pdf/eff_res.pdf)
§§2.4–2.5，尤其式 (13)–(15)，供应伪逆及全点对迹公式；
[Cruz Ortega–Menéndez-Conde，arXiv:2306.08187v1](https://arxiv.org/html/2306.08187v1)
§5 的固定全点对电阻目标与尺度不变量是外部问题对应，区别于固定电导预算。
新增比较是 (18.3)–(18.12) 的六点齐次多项式推导。

正达到性、全边界排除、定量紧性及必要 Fiedler 二重性分别由定理 7.1、
5.1–6.2、7.2、8.1 按原假设供应；完整路径供应仍按约定 4.2，
五边形供应仍是定理 16.3。六点比较对每个正竞争者直接成立，
未预设最大点的对称性、谱秩、矩区域、迹或预算。
定理 19.1 的正向紧性是在确定 $B_6=35/2$ 后应用定理 7.2，
未将任何边界当作缩点后的普通计数测度环。
在单纯形顶点处仅使用 $D$ 的齐次多项式，不给 $T/\rho$ 的 $0/0$ 赋值；
接近顶点的原始正序列由定理 5.1 的一致路径界及定理 7.2 排除。
这里确定六阶值、全部正等号及全部序列判别；$n\ge7$ 的尖锐值、
完整等号与序列分类仍未由这些推导确定。

## 追加锚（本行以下为增补区）
