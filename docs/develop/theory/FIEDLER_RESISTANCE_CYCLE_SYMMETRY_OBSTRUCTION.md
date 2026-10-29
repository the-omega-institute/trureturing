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
