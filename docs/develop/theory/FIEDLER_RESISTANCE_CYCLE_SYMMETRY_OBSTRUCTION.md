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

## 9. Fourier moments and a sharp uniform comparison

**定义 9.1（循环 Fourier 数据）。** 固定 $n\ge5$，令
$\theta=2\pi/n$、$z=e^{\mathrm i\theta}$，并对 $1\le k\le n-1$ 置

$$
 d_k=1-z^{-k},\qquad \mu_k=|d_k|^{-2}=\frac1{4\sin^2(\pi k/n)}.
$$

对 $p\in\Delta$ 定义

$$
 q_k(p)=\sum_{i=0}^{n-1}p_i z^{ki},\qquad q_0=1,\qquad q_{n-k}=\overline {q_k}.
$$

记

$$
 \tau_n=\frac1n\sum_{k=1}^{n-1}\mu_k=\frac{n^2-1}{12n},\qquad
 \rho_n=\frac{\mu_1}{n},\qquad
 T_n=\tau_n-2\rho_n,\qquad
 E_n(p)=\frac1n\sum_{k=2}^{n-2}\mu_k|q_k(p)|^2.
$$

$\tau_n$ 和 $\rho_n$ 分别是均匀权重的迹和最大特征值；$T_n$ 是去掉第一 Fourier 对后的迹。

**定理 9.2（精确 Fourier 矩阵及均匀值比较）。** 对 $p\in\Delta^\circ$，在顶点 Fourier 基
$f_k=n^{-1/2}(z^{ki})_{i=0}^{n-1}$ 的非恒定部分中，$M(p)$ 的矩阵为

$$
 M(p)_{km}=\frac{q_{m-k}(p)-\overline {q_k(p)}q_m(p)}
 {n\,\overline {d_k}d_m},\qquad 1\le k,m\le n-1. \tag{9.1}
$$

因而

$$
 T(p)=\tau_n-2\rho_n|q_1|^2-E_n(p),\qquad
 M(p)_{11}=\rho_n(1-|q_1|^2),\qquad
 \rho(p)\ge\rho_n(1-|q_1|^2). \tag{9.2}
$$

在区域

$$
 {\cal E}_n=\{p\in\Delta^\circ:E_n(p)\ge T_n|q_1(p)|^2\} \tag{9.3}
$$

有尖锐的比较

$$
 \Phi(p)\le \Phi_{\rm unif}:=\frac{n\tau_n}{\rho_n}
 =\frac{n(n^2-1)}3\sin^2\frac{\pi}{n}. \tag{9.4}
$$

等号当且仅当 $p_i=1/n$ 对全部 $i$ 成立。

证明。将 (5.4) 写在 Fourier 基中。边流的第 $k$ 个系数为
$d_k^{-1}$ 乘以顶点的第 $k$ 个系数，故加权能量的第一项为
$q_{m-k}/(n\overline d_kd_m)$；最小化循环流常数给出第二项
$\overline q_kq_m/(n\overline d_kd_m)$，这就是 (9.1)。取对角和得到第一式 (9.2)，取 $(1,1)$ 元并用 Rayleigh 原理得到其余两式。

若 $E_n(p)\ge T_n|q_1|^2$，则
$T(p)\le\tau_n(1-|q_1|^2)$，再由 (9.2) 得 (9.4)。以下核对等号。
若 $q_1=0$，两次不等式同时取等号会给出 $E_n=0$，所以所有非零 Fourier 矩均为零，$p$ 均匀。若 $q_1\ne0$，等号要求 $f_1$ 是 $M(p)$ 的最大特征向量。对 (9.1) 的 $(m,1)$ 元（取 $m=2$）有
$q_1=\overline q_1q_2$，从而 $|q_2|=1$；严格正的概率向量不可能有非平凡 Fourier 矩的模为一。因此 $q_1=0$，回到前一种情形。∎

**推论 9.3（旋转对称性的严格障碍及改进的必要矩条件）。** 若 $p$ 在非恒等循环旋转下不变，则 $q_1(p)=0$。因此非均匀的此类 $p$ 满足

$$
 \Phi(p)<\Phi_{\rm unif}. \tag{9.5}
$$

任何满足 $\Phi(p)>\Phi_{\rm unif}$ 的正权重必须满足

$$
 q_1(p)\ne0,\qquad E_n(p)<T_n|q_1(p)|^2, \tag{9.6}
$$

以及更强的相干谱条件

$$
 \rho(p)<\rho_n\,\frac{T(p)}{\tau_n}. \tag{9.7}
$$

其 Fourier 矩还必须满足矩阵

$$
 \bigl(q_{m-k}-\overline q_kq_m\bigr)_{1\le k,m\le n-1}\succeq0, \tag{9.8}
$$

并使 (9.1) 的非对角相位共同降低最大特征值；单独改变各个 $|q_k|$ 而破坏 (9.8) 不能产生可行权重。

证明。若 $p_{i+d}=p_i$，则
$q_1=z^{-d}q_1$，而非恒等性给出 $z^{-d}\ne1$。非均匀性又使某个 $q_k\ne0$，故 (9.2) 和 $\rho\ge\rho_n$ 给出严格式 (9.5)。若 (9.6) 不成立，(9.4) 反向给出不超过均匀值。由严格改进的定义直接得到 (9.7)。最后 (9.8) 是
$\sum_i p_i(\zeta_i-\bar\zeta)(\zeta_i-\bar\zeta)^*$ 的 Gram 矩阵，其中
$\zeta_i=(z^{ki})_{k=1}^{n-1}$；它是正半定的必要相干条件。∎


## 10. 正双 Fiedler 轨迹的解析结构

**定义 10.1（双 Fiedler 集）。** 令

$$
 {\cal D}=\{(p,s)\in\Delta^\circ\times(0,\infty):
 \lambda_{\max}(M(p))\text{ 的重数为 }2\},\qquad c_i=(sp_i)^{-1}.
$$

若 $E(p)$ 是 $M(p)$ 的最大特征空间，记 $\Pi(p)$ 为其正交投影，并写
$\operatorname{tf}_E A=A-\frac12\operatorname{tr}_E(A)I_E$。

**引理 10.2（双重条件的秩二横截性）。** 在每个 $(p,s)\in{\cal D}$，线性映射

$$
 {\cal R}_p:\{\xi\in\mathbb R^n:\sum_i\xi_i=0\}\longrightarrow\operatorname{Sym}_0(E(p)),\qquad
 {\cal R}_p(\xi)=\operatorname{tf}_E\!\left(\Pi\sum_i\xi_i v_iv_i^{\mathsf T}\Pi\right), \tag{10.1}
$$

是满射，其中 $v_i=a_i-\bar a(p)$。

证明。设 $u,v$ 是 $E(p)$ 的正交基。若 (10.1) 不满射，则存在非零迹零矩阵
$A\in\operatorname{Sym}_0(\mathbb R^2)$，使

$$
 (u_i,v_i)A(u_i,v_i)^{\mathsf T}\quad\text{与 }i\text{ 无关}, \tag{10.2}
$$

其中 $(u_i,v_i)=(\langle u,v_i\rangle,\langle v,v_i\rangle)$。把 $u,v$ 代入环的特征方程，并连续消去相邻坐标，得到

$$
 \sum_i c_i\bigl(u_iv_{i+1}-u_{i+1}v_i\bigr)^2>0. \tag{10.3}
$$

且 (10.2) 的左边相邻差的加权和等于
$-\operatorname{tr}(A)$ 乘以 (10.3)。由于 $\operatorname{tr}(A)=0$，反向消元给出
$A=0$，矛盾。这里 (10.3) 严格是因为两个独立环特征向量的离散 Wronskian 不可能在一个正系数二阶递推中处处为零；$n\ge5$ 保证消元中至少有三个连续方程。∎

**定理 10.3（双 Fiedler 集的局部解析维数）。** $\mathcal D$ 在每个正双 Fiedler 周期附近是实解析子流形。允许共同特征值自由时，其在 $c$ 空间的局部维数为 $n-2$；加入
$\lambda_2=\lambda_3=1$ 时，局部维数为 $n-3$。

证明。对称矩阵的二重特征值条件等价于最大特征空间上的迹零压缩为零，即两个独立的解析方程。引理 10.2 给出其微分秩恰为二，解析隐函数定理遂给出
$(n-1)-2=n-3$ 维的 $p$ 轨迹。坐标
$c\leftrightarrow(p,s)$ 是正解析双射，共同特征值为
$(s\rho(p))^{-1}$，故自由尺度增加一维，得到 $n-2$。条件共同特征值为 $1$ 唯一确定
$s=\rho(p)^{-1}$，不再增加维数，得到 $n-3$。∎

**定理 10.4（局部极大值的唯一正乘子与互补曲率）。** 设 $(p,s)$ 是 $\Phi$ 的内点局部极大值，$E=E(p)$，$\rho=\lambda_{\max}M(p)$，$T=T(p)$，$\beta=T/\rho$。则存在唯一
$W\in\operatorname{Sym}(E)$ 满足

$$
 W\succ0,\qquad \operatorname{tr}_E W=1,\qquad
 \|v_i\|^2=\beta\,\langle W u_i,u_i\rangle\quad(0\le i<n), \tag{10.4}
$$

其中 $u_i=\Pi v_i\in E$。令 $Q=I-\Pi$，对任一满足
$\operatorname{tf}_E\Pi\dot M[\xi]\Pi=0$ 的切向量 $\xi$，置

$$
 w_\xi=\sum_i\xi_i v_i,\quad A_\xi=\sum_i\xi_i v_iv_i^{\mathsf T},\quad
 {\cal H}_\xi=\Pi\!\left(-w_\xi w_\xi^{\mathsf T}+A_\xi Q(\rho I-M)^{-1}QA_\xi\right)\!\Pi. \tag{10.5}
$$

则必要的互补谱曲率条件为

$$
 \lambda_{\max}({\cal H}_\xi)\ge-\frac{\|w_\xi\|^2}{\beta} \qquad\text{对所有上述 }\xi. \tag{10.6}
$$

证明。最大特征值的次梯度是 $\Pi W\Pi$，其中 $W\succeq0$ 且迹为一。对所有单纯形切向量的第一变分为零，给出
$\|v_i\|^2-\beta\langle Wu_i,u_i\rangle$ 为常数；按 $p$ 加权后常数为零，得到 (10.4)。若 $W$ 有零方向，则 (10.4) 迫使全部 $v_i$ 的投影落在一条直线上；环上 $n\ge5$ 个仿射无关的 $a_i$ 排除该情形，故 $W\succ0$。引理 10.2 又给出线性方程组的唯一性。

沿 $p+t\xi$ 有精确展开
$M(t)=M+tA_\xi-t^2w_\xi w_\xi^{\mathsf T}$。当顶层一阶压缩为标量时，标准对称矩阵二阶分裂公式给出顶层二阶矩阵 (10.5)。同时
$T(t)=T+t\beta\alpha-t^2\|w_\xi\|^2$，其中 $\alpha$ 是顶层共同的一阶位移。代入 $nT(t)/\lambda_{\max}M(t)$，$\alpha^2$ 项相消，局部极大性给出
$-\|w_\xi\|^2-\beta\lambda_{\max}({\cal H}_\xi)\le0$，即 (10.6)。∎


## 11. 均匀双 Fiedler 周期的完整二次式

**定义 11.1（均匀点的扰动数据）。** 令 $p^0_i=1/n$，$M_0=M(p^0)$，其最大特征值为 $\rho_n$，最大空间
$E_0=\operatorname{span}\{f_1,f_{n-1}\}$。对实切向量 $\xi$ 令

$$
 \widehat\xi_k=\sum_{i=0}^{n-1}\xi_i z^{ki},\qquad \sum_i\xi_i=0,
$$

置 $\rho_k=\mu_k/n$（$1\le k\le n-1$），并在 $H$ 上定义

$$
 A_\xi=\sum_i\xi_i v_i^0(v_i^0)^{\mathsf T},\qquad
 w_\xi=\sum_i\xi_i v_i^0,\qquad
 G_0=Q_0(\rho_nI-M_0)^{-1}Q_0,\quad Q_0=I-\Pi_0. \tag{11.1}
$$

在 Fourier 基中

$$
 (A_\xi)_{km}=\frac{\widehat\xi_{m-k}}{n\,\overline d_kd_m},\qquad
 \|w_\xi\|^2=\frac1n\sum_{k=1}^{n-1}\mu_k|\widehat\xi_k|^2. \tag{11.2}
$$

顶层压缩的迹为零，且其两个特征值为
$\pm\rho_n|\widehat\xi_2|$。

**定理 11.2（每个切向量的精确二次展开）。** 对任一实切向量 $\xi$，令

$$
 {\cal H}_\xi^0=\Pi_0\left(-w_\xi w_\xi^{\mathsf T}+A_\xi G_0A_\xi\right)\Pi_0. \tag{11.3}
$$

则对 $t\to0$ 有

$$
 \rho(p^0+t\xi)=\rho_n+\rho_n|\widehat\xi_2|\,|t|
 +h_\xi^{\operatorname{sgn}t}t^2+o(t^2), \tag{11.4}
$$

其中 $h_\xi^\sigma$ 是 (11.3) 加到顶层一阶压缩的 $\sigma$-分支上的二次系数；当 $\widehat\xi_2=0$ 时
$h_\xi^\sigma=\lambda_{\max}({\cal H}_\xi^0)$。同时

$$
 \Phi(p^0+t\xi)=\Phi_{\rm unif}\bigl(1-|\widehat\xi_2||t|\bigr)
 +\frac n{\rho_n}\left[-\|w_\xi\|^2-\beta_n h_\xi^{\operatorname{sgn}t}
 +\beta_n\rho_n|\widehat\xi_2|^2\right]t^2+o(t^2),\quad
 \beta_n=\frac{\tau_n}{\rho_n}. \tag{11.5}
$$

证明。式 (11.2) 是 (9.1) 对 $q_k=t\widehat\xi_k$ 的一阶项和累积流公式。顶层的 $(1,n-1)$ 元模为
$\rho_n|\widehat\xi_2|$，对角元为零，故一阶分裂如 (11.4)。对补空间作 Schur 补，二阶项正是
$-w_\xi w_\xi^{\mathsf T}+A_\xi G_0A_\xi$。迹的精确式为
$T(p^0+t\xi)=\tau_n-t^2\|w_\xi\|^2$。将这两式代入商，线性项和二阶分母项按 (11.5) 合并，得到结论。∎

**推论 11.3（双重轨迹上的二次式及 $12$ 阈值）。** 在 $\widehat\xi_2=0$ 的切空间中，能够由解析双 Fiedler 轨迹实现的共同二次曲率为

$$
 {\cal Q}_{\rm dbl}(\xi)=\frac n{\rho_n}\left[-\|w_\xi\|^2-\frac{\beta_n}{2}\operatorname{tr}{\cal H}_\xi^0\right]. \tag{11.6}
$$

Fourier 模式彼此正交；除第一模式及其共轭外，所有模式在 (11.6) 中的系数严格为负。第一模式的系数为

$$
 2\rho_n|\widehat\xi_1|^2\,\chi_n,\qquad
 \chi_n=-1+\frac{(n^2-1)\sin^2(\pi/n)\cos(2\pi/n)}
 {3\,[\,4\cos^2(\pi/n)-1\,]}. \tag{11.7}
$$

并且

$$
 \chi_n<0\quad(5\le n\le11),\qquad \chi_n>0\quad(n\ge12). \tag{11.8}
$$

证明。若 $\widehat\xi_k$ 只含一对 $k,n-k$，(11.2) 和 (11.3) 中的补谱分母均为
$\rho_n-\rho_j>0$，所以 $k\ge3$ 的贡献为严格负数。对 $k=1$，有
$\|w_\xi\|^2=2\rho_n|\widehat\xi_1|^2$，而

$$
 \frac12\operatorname{tr}{\cal H}_\xi^0
=\rho_n|\widehat\xi_1|^2\left[-1+\frac{\rho_2/\rho_n}{1-\rho_2/\rho_n}\right],\qquad
 \frac{\rho_2}{\rho_n}=\frac1{4\cos^2(\pi/n)}.
$$

代入 $\beta_n=(n^2-1)\sin^2(\pi/n)/3$ 即得 (11.7)。不同 Fourier 对在迹和补谱分母中正交，故不存在交叉项。

为核对符号，令 $x=\pi/n$。把 (11.7) 移项并乘以正数
$3(4\cos^2x-1)$，符号等价于

$$
 (n^2-1)\sin^2x\cos(2x)-3(4\cos^2x-1). \tag{11.9}
$$

将 $n=\pi/x$ 代入并微分，在 $0<x\le\pi/5$ 清除正因子后导数严格为负；因此 (11.9) 随 $n$ 严格递增。交错 Taylor 界给出
$-1/200<\chi_{11}<-1/250$，而
$1/100<\chi_{12}<1/80$。故 (11.8) 成立。

**定理 11.4（均匀点的局部类型）。** 在固定总电阻的尺度商空间中，均匀正环为严格局部极大值当且仅限于
$5\le n\le11$；对 $n\ge12$，它是实际双 Fiedler 集上的严格鞍点。

证明。若 $\widehat\xi_2\ne0$，(11.5) 的绝对值线性项在两个方向均严格降低目标。若 $\widehat\xi_2=0$，解析双 Fiedler 轨迹的二阶系数为 (11.6)；(11.8) 与其余模式的严格负系数给出 $5\le n\le11$ 的严格负性。有限维单位球面的紧性把逐模严格性提升为统一的二次负界，故得到严格局部极大值。

当 $n\ge12$，取 $\xi_i=\cos(2\pi i/n)$。由 (11.7)–(11.8)，双轨迹上的二阶系数严格为正。引理 10.2 和解析隐函数定理允许加入唯一的二阶 $2$-模校正，使顶层二阶迹零且不发生分裂；由 (11.6) 该校正不改变共同二次系数。因此均匀点沿实际双 Fiedler 集有增有减，是严格鞍点。∎


## 12. 大阶正解析分支与均匀邻域

**定理 12.1（固定电阻上的严格改进分支）。** 对每个 $n\ge12$ 和每个 $R_0>0$，存在正解析曲线 $p(t)\in\Delta^\circ$，定义在 $|t|<\varepsilon_n$，满足

$$
 p(0)=p^0,\qquad \lambda_2(L(c(t)))=\lambda_3(L(c(t))),\qquad
 c_i(t)=\frac{nT(p(t))}{R_0p_i(t)},\qquad R(c(t))=R_0, \tag{12.1}
$$

并且对某个符号选择及所有充分小的非零 $t$，有

$$
 \lambda_2(L(c(t)))R_0>\Phi_{\rm unif}. \tag{12.2}
$$

不把曲线上的任何点称为全局最优。

证明。取定理 11.4 的第一 Fourier 切向量。引理 10.2 给出的秩二方程允许唯一解析地解出二阶法向分量，使最大特征值保持二重；正性由 $p^0$ 的正坐标和连续性保持。式 (11.8) 使曲线上目标的二阶系数为正。最后按 (7.3) 缩放，得到 (12.1) 的总电阻与严格不等式 (12.2)。∎

**推论 12.2（均匀邻域无局部极大值）。** 对每个 $n\ge12$，存在均匀点的一个相对邻域，其中没有实际正环的局部极大值。

证明。局部极大值必满足定理 8.1 的双 Fiedler 条件。定理 10.3 把该双集在均匀点附近解析化，而 (11.6) 的正曲率在第一模式方向上对该解析切场保持；缩小邻域后，每个双点都有一条保持双重性的曲线使目标严格增加。因此该邻域内不存在局部极大值。∎

## 13. 内点极大值的有限位移、余谱锥与证书排除

**定理 13.1（有限位移恒等式与余谱松弛锥）。** 设 $p$ 是任意内点局部极大值，记 $M=M(p)$、$T=T(p)$、$\rho=\rho(p)$，$\Pi$ 为其二重 Fiedler 投影，$Q=I-\Pi$。对任意满足 $\sum_i\xi_i=0$ 且 $p+\xi\in\Delta^\circ$ 的有限位移，置

$$
 w_\xi=\sum_i\xi_i v_i,\qquad C_\xi=\sum_i\xi_i v_iv_i^{\mathsf T},\qquad S_\xi=C_\xi-w_\xi w_\xi^{\mathsf T}. \tag{13.1}
$$

则有精确恒等式

$$
 M(p+\xi)=M+S_\xi,\qquad T(p+\xi)=T+\operatorname{tr}S_\xi,\qquad
 \Phi(p+\xi)=\frac{n(T+\operatorname{tr}S_\xi)}{\rho+\sigma(S_\xi)}, \tag{13.2}
$$

其中 $\sigma(S)=\lambda_{\max}(M+S)-\rho$。总有
$\sigma(S)\ge\lambda_{\max}(\Pi S\Pi)$。
定义余谱松弛锥

$$
 {\cal K}_{\Pi}=\left\{S:\ \Pi S\Pi=\alpha\Pi,\quad QS\Pi=0,\quad
 Q(\rho I-M-S)Q\succeq0\ \text{for some }\alpha\in\mathbb R\right\}. \tag{13.3}
$$

在该锥上 $\sigma(S)=\alpha$；若最后的半正定式严格正定，则余谱严格有隙。

证明。把协方差按新均值展开即得 (13.1)–(13.2)。在 $E=\operatorname{ran}\Pi$ 上取 Rayleigh 商给出松弛下界。若 $S\in{\cal K}_\Pi$，$M+S$ 按 $E\oplus E^\perp$ 分块，顶块为
$(\rho+\alpha)I_E$，交叉块为零，余块不超过该值，故最大特征值恰为 $\rho+\alpha$。∎

**推论 13.2（非平凡仿射纤维上的严格支配）。** 定义线性纤维

$$
 {\cal F}_p=\{\xi:\sum_i\xi_i=0,\ \Pi w_\xi=0,\
 \operatorname{tf}_E(\Pi C_\xi\Pi)=0\}. \tag{13.4}
$$

若 $\xi\in{\cal F}_p$、$p+\xi\in\Delta^\circ$、$w_\xi\ne0$，且 $S_\xi\in{\cal K}_\Pi$ 的余谱半正定式严格，则

$$
 \Phi(p+\xi)<\Phi(p). \tag{13.5}
$$

这对整个非平凡纤维同时成立，而不是只对其原点的微分成立。

证明。由 $\Pi w_\xi=0$ 和 (13.4)，$\Pi S_\xi\Pi=\alpha\Pi$。定理 10.4 的乘子恒等式给出

$$
 \operatorname{tr}C_\xi-\beta\,\alpha=0,\qquad \beta=T/\rho.
$$

故
$\operatorname{tr}S_\xi-\beta\alpha=-\|w_\xi\|^2<0$。将 $\sigma(S_\xi)=\alpha$ 代入 (13.2)，即得 (13.5)；若 $w_\xi=0$，同一恒等式给出等值而非严格值。∎

**定理 13.3（固定紧顶空间证书不能在邻域内成立）。** 不存在固定的环境矩阵
$X\succeq0$、$\operatorname{tr}X=1$，使其在某个包含内点局部极大值的完整邻域内同时满足

$$
\operatorname{ran}X\subset E(p),\qquad \operatorname{tr}(XM(p))=\rho(p) \tag{13.6}
$$

并以此给出全邻域的紧顶空间比值证书。

证明。等式 $\operatorname{tr}X(\rho I-M)=0$ 与两矩阵的半正定性等价于
$X$ 支持在 $E(p)$。若同一个 $X$ 在开邻域内满足 (13.6)，对任一切向量微分
$M(p+t\xi)X=\rho(p+t)X$ 的余谱分量，得到
$Q(p)A_\xi X=0$。引理 10.2 的同一 Wronskian 消元表明可选取 $\xi$ 使该分量非零，矛盾。故固定迹一矩阵不可能在完整邻域保持紧性；这只排除该证书路线，不排除其它随 $p$ 变化的证书。∎


## 14. 同一环的删边路径与闭合边判据

**定理 14.1（正路径的闭合边判据）。** 从一个正电导环删去边 $e$，得到端点为 $a,b$ 的正电导路径。令
$A=L_P|_{\mathbf1^\perp}$，其特征对为
$0<\lambda_2<\lambda_3<\cdots$，取单位特征向量 $x_j$，并置
$\gamma_j=\langle b,x_j\rangle$、$\ell=b^{\mathsf T}A^{-1}b$。给路径重新加入电导 $h>0$ 的边后，闭环在原路径第三特征值 $\lambda_3$ 处具有
$\lambda_2=\lambda_3$ 当且仅当

$$
 \gamma_3=0,\qquad
 1+h\sum_{j\ne3}\frac{\gamma_j^2}{\lambda_j-\lambda_3}=0,\qquad
 h=-\left(\sum_{j\ne3}\frac{\gamma_j^2}{\lambda_j-\lambda_3}\right)^{-1}>0. \tag{14.1}
$$

这里的和包含路径的全部正特征值；第二式同时保证 $\lambda_3$ 仍是闭环特征值和另一个根在同一点相交。

证明。Sherman–Morrison 的秩一特征方程为

$$
 1+h\,b^{\mathsf T}(A-\lambda I)^{-1}b=0. \tag{14.2}
$$

原特征值 $\lambda_3$ 在更新后保持不变恰当且仅当 $\gamma_3=0$。在此条件下把 $\lambda=\lambda_3$ 代入 (14.2) 即得 (14.1)；正性正是闭合边电导为正的条件。秩一交错定理保证该根位于第二与第三路径根之间，故相交时它们正是闭环的两个最小正根。∎

**推论 14.2（电阻与目标的精确关系）。** 记
$K=A^{-1}$、$v=Kb$、$\tau=h/(1+h\ell)$。闭环伪逆在 $\mathbf1^\perp$ 上为

$$
 K_h=K-\tau vv^{\mathsf T},\qquad
 R_h=R_P-n\tau\|v\|^2,\qquad
 R_{\rm eff,h}(a,b)=\frac{\ell}{1+h\ell}. \tag{14.3}
$$

若 (14.1) 成立，则

$$
 \lambda_2(L_h)=\lambda_3(A),\qquad
 \lambda_2(L_h)R_h=\lambda_3(A)\,[R_P-n\tau\|v\|^2]. \tag{14.4}
$$

证明。第一式是秩一逆公式，第二式取迹并用全点对恒等式
$R=n\operatorname{tr}L^+$，第三式是端点二支路的并联公式。再用定理 14.1 即得 (14.4)。∎

**定理 14.3（同一环逐边删去的兼容性）。** 一个正电导环若要求对每一条边 $e$ 的删边路径都在原路径第三特征值处满足闭合边判据，则必须且只须对每条 $e$ 同时满足 (14.1)，其中
$A_e,b_e,\lambda_{e,j},\gamma_{e,j}$ 全部由同一个环电导向量删去该边后得到，而闭合边的 $h$ 必须等于原环的同一坐标 $c_e$。此外，各条路径的共同电阻和目标必须由 (14.3) 的同一环伪逆相容；不能把不同删边所得的路径边际最优值分别拼接。

证明。对每一条边独立应用定理 14.1 得必要性。反之，若同一电导向量的每个删边数据都满足 (14.1)，逐边秩一恢复即给出所要求的双 Fiedler 条件；(14.3) 则保证电阻和目标来自同一个闭环。完整路径乘积界及其唯一等号类可直接使用
FIEDLER_RESISTANCE_PATH_OPTIMIZER.md 的定理 2.1 与推论 3.1；它们约束的是每一个共同实现的删边路径，不能替换为相互独立的路径边际量。∎

## 15. 尚未闭合的尖锐常数与等号类

对每个 $n\ge5$，仍令

$$
 B_n=\sup_{c\in(0,\infty)^n}\lambda_2(L(c))R(c),\qquad
 \mathcal P_n=\{p\in\Delta^\circ:\Phi(p)=B_n\}.
$$

定理 7.1 已给出 $A_n<B_n<n(n-1)$ 及正内点达到性；定理 9.2、11.4、12.1、13.1–13.3 和 14.1–14.3 只增加必要条件、局部类型、有限位移恒等式、证书排除与共同删边判据。它们没有给出 $B_n$ 的闭式，也没有给出 $\mathcal P_n$ 的充分且必要刻画；所有原有的全点对、正性、计数质量和竞争者量词保持不变。

原始路径中使用的全路径等号类仍仅作为每次删边的已知中间结果。相关电阻恒等式和迹公式见 Ghosh–Boyd–Saberi，[*Minimizing Effective Resistance of a Graph*](https://doi.org/10.1137/050645452)，§§2.4–2.5；路径优化的完整结论见 [FIEDLER_RESISTANCE_PATH_OPTIMIZER.md](FIEDLER_RESISTANCE_PATH_OPTIMIZER.md)。

## 追加锚（本行以下为增补区）
