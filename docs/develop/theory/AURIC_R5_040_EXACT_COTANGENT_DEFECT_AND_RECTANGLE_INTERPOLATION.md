# 原连续幂系数映射的精确外四次缺陷与矩形插值

本卷固定特征零域 $F$、实际可分域扩张 $D/F$，以及整数 $m\ge 5$，其中
$[D:F]=2m$。取任一本原元 $\theta\in D$，其首一最小多项式记为
$f(T)$，并置

$$
C=\operatorname{span}_F(1,\theta,\ldots,\theta^{m-1}).
$$

沿用前卷 [AURIC_R5_039，§§111--117](AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 的原嵌入标签、带符号互补系数、统一商 $X_D$、Gale 对合 $\iota$、正规化环 $B_F$ 和原系数环 $S_F$。前卷已经给出正规化的固定点局部模型、负余切的多项式识别、完整的成对余切映射，以及本节所用的外四次下界；下文只证明把这个下界变成等式所需的原族上界。关于外四次二次关系的经典代数曲率解释，可参见 Bettiol--Kummer--Mendes, *Convex Algebraic Geometry of Curvature Operators*, arXiv:1908.03713v2, §§2.1--2.2；本卷的张成结论直接由下面的有限插值证明。

## 119. 原族余切的固定记号

**定义 119.1（原系数到正规化的余切映射）。** 令 $p=[P_C]$ 为原带标签系数点，令 $y$ 为 $\operatorname{Spec}B_F$ 上方的正规化点，并写

$$
\mathfrak t_S=\mathfrak m_{(S_F)_p}/\mathfrak m_{(S_F)_p}^2,
\qquad
\mathfrak t_Z=\mathfrak m_{(B_F)_y}/\mathfrak m_{(B_F)_y}^2,
\qquad
J:\mathfrak t_S\longrightarrow\mathfrak t_Z.
\tag{119.1}
$$

这里 $Z=\operatorname{Spec}B_F$，所以 $J^\vee$ 是正规化 $Z\to\operatorname{Spec}S_F$ 在 $y$、$p$ 处的切映射。这个切映射属于正规化，而不是光滑乘法商 $X_D\to\Gamma_D$ 的一阶映射。

取 $f$ 的分裂域 $K/F$，令 $\Lambda\subset K$ 为 $f$ 的全部 $2m$ 个互异根，并保持它们的原嵌入标签。置

$$
d=m-2,
\qquad
V_K=K[T]_{\le d},
\qquad
a=\frac{m(m-1)}2,
\qquad
b=\frac{(m-1)(m-2)}2.
\tag{119.2}
$$

前卷的固定点局部模型给出 $K$-线性分解

$$
\mathfrak t_{Z,K}=P^\vee\oplus Q,
\qquad
Q=\operatorname{Sym}^2(N^\vee),
\qquad
N^\vee\simeq\bigwedge^2V_K,
\tag{119.3}
$$

其中 $\dim P=a$、$\dim N=b$。因此 $\dim Q=b(b+1)/2$。记

$$
M_K=\operatorname{im}(J_K)\subset P^\vee\oplus Q.
\tag{119.4}
$$

前卷的负余切识别是由

$$
Q_0(s,t)=(s-t)A(s,t),
\qquad A(t,s)=-A(s,t),
\qquad \deg_sA,\deg_tA\le d,
\tag{119.5}
$$

给出的 $\ker\mu_{C,K}\simeq\bigwedge^2V_K$。在这个识别下，若
$F_A(T)=\prod_{u\in A}(T-u)$，则记

$$
F_A\wedge F_B
   :=F_A(s)F_B(t)-F_B(s)F_A(t)\in\bigwedge^2V_K.
\tag{119.6}
$$

以下对 $\mathfrak t_{Z,K}$ 的二次纯负部分都使用
$Q=\operatorname{Sym}^2(\bigwedge^2V_K)$。

**既有输入 119.2（前卷结果）。** 下列事实作为前卷的已建立结果使用：

1. 带符号互补系数的成对余切类在 (119.3) 中形如
   $(\ell_I,q_I)$，并共同生成 $M_K$；
2. 前卷 (116.2) 的四根点导子给出

   $$
   \dim_K\operatorname{coker}J_K\ge {m-1\choose4};
   \tag{119.7}
   $$

3. 对任一实际矩形比值 $r$，其 $r$、$1-r$ 以及带符号互补范数均为相应局部化环中的单位，并满足前卷 (112.4)--(112.5)。

这些输入保留原始 $D/F$、原嵌入标签和实际连续幂窗口；没有把矩阵换成任意根的泛矩阵。

## 120. 实际矩形的负微分与原系数判别式

**定义 120.1（实际矩形）。** 取互不相交的根子集

$$
\Lambda=A\sqcup B\sqcup\{\alpha,\gamma,\beta,\delta\},
\qquad |A|=|B|=d.
\tag{120.1}
$$

置

$$
I=A\sqcup\{\alpha,\gamma\},
\qquad
J=B\sqcup\{\beta,\delta\},
\qquad
F_A(T)=\prod_{u\in A}(T-u),
\qquad
F_B(T)=\prod_{v\in B}(T-v).
\tag{120.2}
$$

在 $I$ 行的实际评价帧上，令

$$
\ell_i(T)=\frac{F_I(T)}{(T-i)F_I'(i)}\quad(i\in I),
\qquad
 a_{ji}=\ell_i(j)\quad(j\in J),
\tag{120.3}
$$

并取原矩形比值

$$
 r=\frac{a_{\beta\alpha}a_{\delta\gamma}}
 {a_{\beta\gamma}a_{\delta\alpha}}.
\tag{120.4}
$$

连续幂评价帧的每个 $m$ 阶子式都是互异根的 Vandermonde 值；统一开集因而使
$F_I'(i)$、四个矩形条目及下面出现的所有分母都成为单位。

对于不同的实际根 $u,v$，沿用前卷的实际包含帧方向

$$
 H_{uv}(P)=
 \frac{f'(u)P(v)e_u+f'(v)P(u)e_v}{u-v},
 \qquad P\in K[T]_{<m},
\tag{120.5}
$$

其中 $e_s$ 是标签 $s$ 的坐标向量。前卷的负切识别为

$$
[H_{uv}]_-=2\,\operatorname{ev}_u\wedge\operatorname{ev}_v,
\qquad \operatorname{ev}_u(P)=P(u)\quad(P\in V_K).
\tag{120.6}
$$

前卷的双曲切片把这些 $H_{uv}$ 的商切类选成纯负类；矩形比值是商上的函数，
所以其在 $H_{uv}$ 上的微分正是负余切类与 (120.6) 的配对。

**定理 120.2（实际原族矩形梯度）。** 在 (119.5) 的负余切识别和 (120.6) 的符号约定下，矩形对数的负余切类为

$$
\boxed{
 [d\log r]_-=
 -\frac{(\alpha-\gamma)(\beta-\delta)}2\,(F_A\wedge F_B).
}
\tag{120.7}
$$

特别地，这个类非零，并且其系数只由四个实际剩余根的差给出。

证明。把包含帧写成 $E+tH$，用 $I$ 行作基。实际的商矩阵是

$$
 A(t)=(E_J+tH_J)(E_I+tH_I)^{-1},
$$

在 $t=0$ 处求导，记 $A=A(0)$，得到

$$
 \dot A=H_JE_I^{-1}-AH_IE_I^{-1}
 =(H_J-AH_I)E_I^{-1}.
\tag{120.8}
$$

逐项写成拉格朗日基就是

$$
 \dot a_{ji}=H_j(\ell_i)-\sum_{t\in I}\ell_t(j)H_t(\ell_i).
\tag{120.9}
$$

这一步同时包含了行的变化和 $I$ 帧的变化。若 $u,v\in A$，则 $H_J=0$；由 $\ell_i(v)=\delta_{iv}$、$\ell_i(u)=\delta_{iu}$，$H_IE_I^{-1}$ 只在 $u,v$ 两列有支撑，左乘 $A$ 后仍如此。由于 $\alpha,\gamma\notin A$，(120.9) 给出
$\dot a_{\beta\alpha}=\dot a_{\beta\gamma}=\dot a_{\delta\alpha}=\dot a_{\delta\gamma}=0$。若 $u,v\in B$，则 $H_IE_I^{-1}=0$，而 $H_JE_I^{-1}$ 只在 $u,v$ 两行有支撑；由于 $\beta,\delta\notin B$，四个同样的导数也全为零。因此 $[d\log r]_-$ 消去 $\bigwedge^2\operatorname{ev}(A)$ 和 $\bigwedge^2\operatorname{ev}(B)$。

评价映射 $V_K\to K^A$ 的核是一维空间 $KF_A$，所以其外平方映射的核为 $F_A\wedge V_K$；同理得到 $F_B\wedge V_K$。两个不同的一维因子给出

$$
(F_A\wedge V_K)\cap(F_B\wedge V_K)
   =K(F_A\wedge F_B).
\tag{120.10}
$$

故存在标量 $c$ 使 $[d\log r]_- =c(F_A\wedge F_B)$。现在取 $u\in A$、$v\in B$。此时 $H_{uv}$ 的 $I$ 行只有输出 $u$，由 (120.9) 直接得到

$$
\begin{aligned}
(d\log r)(H_{uv})
=-\frac{f'(u)}{u-v}\bigg[&
\ell_u(\beta)\left(
 \frac{\ell_\alpha(v)}{\ell_\alpha(\beta)}-
 \frac{\ell_\gamma(v)}{\ell_\gamma(\beta)}
\right)\\
&+\ell_u(\delta)\left(
 \frac{\ell_\gamma(v)}{\ell_\gamma(\delta)}-
 \frac{\ell_\alpha(v)}{\ell_\alpha(\delta)}
\right)\bigg].
\end{aligned}
\tag{120.11}
$$

对 $j=\beta,\delta$，拉格朗日公式给出

$$
\frac{\ell_\alpha(v)}{\ell_\alpha(j)}-
\frac{\ell_\gamma(v)}{\ell_\gamma(j)}
=
\frac{F_I(v)}{F_I(j)}
\frac{(\alpha-\gamma)(j-v)}{(v-\alpha)(v-\gamma)}.
\tag{120.12}
$$

把 (120.12) 代入 (120.11)，再用

$$
\ell_u(j)=\frac{F_I(j)}{(j-u)F_I'(u)},
\quad
f'(u)=F_I'(u)F_J(u),
\quad
F_I(v)=(v-\alpha)(v-\gamma)F_A(v),
\quad
F_J(u)=(u-\beta)(u-\delta)F_B(u),
\tag{120.13}
$$

并约去 $(u-v)$，得到

$$
(d\log r)(H_{uv})
=(\alpha-\gamma)(\beta-\delta)F_B(u)F_A(v).
\tag{120.14}
$$

根据 (120.6)，左端等于 $2c(F_A\wedge F_B)(u,v)$。这里

$$
(F_A\wedge F_B)(u,v)
=F_A(u)F_B(v)-F_B(u)F_A(v)
=-F_B(u)F_A(v),
\tag{120.15}
$$

而不是零。根集互不相交，所以 $F_B(u)F_A(v)\ne0$。由 (120.14)--(120.15) 得
$c=-(\alpha-\gamma)(\beta-\delta)/2$，即 (120.7)。四个根互异还保证 (120.4) 的值和其补值非零；具体为

$$
 r(C)=\frac{(\beta-\gamma)(\delta-\alpha)}
 {(\beta-\alpha)(\delta-\gamma)},
 \qquad
 1-r(C)=\frac{(\alpha-\gamma)(\beta-\delta)}
 {(\beta-\alpha)(\delta-\gamma)}.
\tag{120.16}
$$
证毕。

**命题 120.3（原系数中的正向与纯负二次类）。** 令 $\iota$ 为前卷的 Gale 对合，并置

$$
 N(r)=r\,\iota(r),
 \qquad
 s_r=1+N(r)-N(1-r)=r+\iota(r),
 \qquad
 D_r=s_r^2-4N(r)=(r-\iota(r))^2.
\tag{120.17}
$$

则 $s_r,D_r\in S_K$。在固定点局部坐标 $\iota(U,V)=(U,-V)$ 下，若
$\gamma_r=[d\log r]_-$，则

$$
 [D_r]=(0,4r(C)^2\gamma_r^2)
 =\left(0,r(C)^2(\alpha-\gamma)^2(\beta-\delta)^2
       (F_A\wedge F_B)^2\right)\in P^\vee\oplus Q.
\tag{120.18}
$$

并且 $\{[ds_r]_P\}$ 张成 $P^\vee$；可从实际矩形中选出 $a$ 个 $s_r$，使其正向微分构成一组基。

证明。前卷 (112.4) 的带符号互补子式给出

$$
 N(r)=\frac{q_{\beta\alpha}q_{\delta\gamma}}
 {q_{\beta\gamma}q_{\delta\alpha}},
 \qquad
 N(1-r)=\frac{q_{\{\beta,\delta\},\{\alpha,\gamma\}}}
 {q_{\beta\gamma}q_{\delta\alpha}},
\tag{120.19}
$$

其中 $q_{\beta\alpha}$ 等记号是前卷 (112.1) 的原带标签符号系数比值
$q_{\{\beta\},\{\alpha\}}$ 的简写；统一性使所有分母为单位。故 (120.17) 确实属于原系数环，而非假定的全不变量环。

在固定点，$r-\iota(r)$ 的常数项为零，正向一次项相消，负向一次项为 $2\,dr|_N=2r(C)\gamma_r$。将其平方并取正规化不变量余切类便得到 (120.18)。另一方面，锚归一化矩形比值是 $X_{D,K}$ 的局部坐标；它们的微分限制到 $P$ 张成 $P^\vee$。由 $d(r+\iota r)|_P=2\,dr|_P$，相应的 $s_r$ 中必有 $a$ 个给出独立正向微分。证毕。

## 121. 实际矩形的插值张成与外四次补空间

**引理 121.1（删两点插值基）。** 令 $T_0=\{t_0,\ldots,t_{d+1}\}\subset\Lambda$ 为 $d+2$ 个互异根，并置

$$
 G_{ij}(T)=\prod_{t\in T_0\setminus\{t_i,t_j\}}(T-t)
 \quad(0\le i<j\le d+1).
\tag{121.1}
$$

则 $\{G_{ij}\odot G_{ij}:i<j\}$ 是 $\operatorname{Sym}^2V_K$ 的一组基。

证明。对每个无序节点对 $\{t_k,t_l\}$（$k<l$）评价二元对称式
$G_{ij}(s)G_{ij}(t)$。若 $\{k,l\}\ne\{i,j\}$，至少有一个节点属于
$T_0\setminus\{t_i,t_j\}$，评价为零；在自己的节点对上，评价为

$$
G_{ij}(t_i)G_{ij}(t_j)
=\prod_{t\in T_0\setminus\{t_i,t_j\}}(t_i-t)(t_j-t)\ne0.
$$

因此评价矩阵是非零对角矩阵。元素数为
$\binom{d+2}{2}=\dim\operatorname{Sym}^2V_K$，故它们构成基。证毕。

**引理 121.2（所有实际矩形平方的精确张成）。** 令

$$
\mathcal H_K=\operatorname{span}_K\left\{
 (F_A\wedge F_B)\odot(F_A\wedge F_B):
 A,B\subset\Lambda,\ |A|=|B|=d,\ A\cap B=\varnothing
\right\}
\subset\operatorname{Sym}^2(\bigwedge^2V_K).
\tag{121.2}
$$

定义外乘映射

$$
 w_K:\operatorname{Sym}^2(\bigwedge^2V_K)\longrightarrow\bigwedge^4V_K,
 \qquad
 w_K((u\wedge v)\odot(s\wedge t))
 =(u\wedge v)\wedge(s\wedge t).
\tag{121.3}
$$

则

$$
\boxed{\mathcal H_K=\ker w_K.}
\tag{121.4}
$$

证明。每个生成元都在 $\ker w_K$，因为
$(F_A\wedge F_B)\wedge(F_A\wedge F_B)=0$。反向取一个对称双线性形式

$$
\mathcal T:\bigwedge^2V_K\times\bigwedge^2V_K\longrightarrow K
$$

消去 $\mathcal H_K$。固定一个 $d$ 元集 $A$。其外部还有 $d+4$ 个根，选其中任意
$d+2$ 个组成 $T_0$。对每个 $i<j$，令
$B=T_0\setminus\{t_i,t_j\}$。剩余四个原标签可分为
$\{\alpha,\gamma\}$ 和 $\{\beta,\delta\}$，所以这个 $A,B$ 确实来自一个实际矩形；由 (120.18)，其平方属于原系数像的纯负部分，因而被 $\mathcal T$ 消去。引理 121.1 遂给出

$$
 v\longmapsto\mathcal T(F_A\wedge v,F_A\wedge v)=0
 \quad\text{对所有 }v\in V_K.
\tag{121.5}
$$

现在固定 $v\in V_K$，再取任意 $d+2$ 个原根 $T_1$，并令
$A=T_1\setminus\{t_i,t_j\}$。对每个这样的 $A$，(121.5) 给出

$$
 u\longmapsto\mathcal T(u\wedge v,u\wedge v)=0
 \quad\text{在所有这些 }F_A\text{ 上成立}.
$$

再次使用引理 121.1，得到

$$
\mathcal T(u\wedge v,u\wedge v)=0
 \quad\text{对所有 }u,v\in V_K.
\tag{121.6}
$$

令

$$
\Omega(u,v,w,z)=\mathcal T(u\wedge v,w\wedge z).
\tag{121.7}
$$

它在 $(u,v)$、$(w,z)$ 中反对称，在两对交换时对称。对 (121.6) 作极化，得到
$\Omega(u,v,u,z)=0$；再对重复的 $u$ 作极化，得到
$\Omega(w,v,u,z)=-\Omega(u,v,w,z)$。于是它也在第 $1,3$ 个位置反对称。由
$(23)=(13)(12)(13)$，它在所有相邻位置反对称，故是四次交错形式。反过来，任意四次交错形式都按 (121.7) 定义一个消去所有 (121.2) 生成元的对称双线性形式。因此

$$
\operatorname{Ann}(\mathcal H_K)=\operatorname{im}(w_K^*).
$$

有限维对偶性给出 $\mathcal H_K=(\operatorname{im}w_K^*)^\perp=\ker w_K$。证毕。

## 122. 精确余切缺陷与完整耦合切核

**定理 122.1（原连续幂族的精确余切缺陷）。** 在定义 119.1 的全部假设下，原系数到正规化的余切映射满足

$$
\boxed{
\operatorname{coker}J\simeq_F\bigwedge^4_FV_F,
\qquad
V_F=F[T]_{\le m-2}.
}
\tag{122.1}
$$

因此

$$
\dim_F\operatorname{coker}J=\binom{m-1}{4},
\qquad
\operatorname{rank}J
 =a+\frac{b(b+1)}2-\binom{m-1}{4}.
\tag{122.2}
$$

这里的秩是原系数到正规化的余切像秩；(122.2) 不是 $S_F$ 的嵌入维数断言。对偶切映射
$J^\vee:T_yZ\to T_p\operatorname{Spec}S_F$ 的核由
$\bigwedge^4_FV_F^\vee$ 的外四次符号唯一参数化：每个符号有且只有一个正向一阶修正。这个核属于正规化 $Z\to\operatorname{Spec}S_F$，不等同于光滑商 $X_D$ 的另一种一阶核。

证明。先在 $K$ 上工作。由命题 120.3，$M_K$ 含有

$$
0\oplus\mathcal H_K=0\oplus\ker w_K.
\tag{122.3}
$$

同时，选取命题 120.3 中 $a$ 个正向独立的 $s_r$，记其余切类为
$e_i=(\ell_i,q_i)$，则 $\ell_1,\ldots,\ell_a$ 是 $P^\vee$ 的一组基。它们与 (122.3) 直和独立：若
$\sum c_ie_i\in0\oplus\ker w_K$，投影到 $P^\vee$ 即得
$\sum c_i\ell_i=0$，所以所有 $c_i=0$。故

$$
\dim_KM_K\ge a+\dim\ker w_K.
\tag{122.4}
$$

当 $m\ge5$ 时 $\dim V_K=m-1\ge4$，外乘映射 $w_K$ 满射，且

$$
\dim\ker w_K=\frac{b(b+1)}2-\binom{m-1}{4}.
\tag{122.5}
$$

由 (119.7)，另一方面

$$
\dim\operatorname{coker}J_K\ge\binom{m-1}{4},
$$

也就是 $\dim M_K$ 不超过右端所对应的补维。与 (122.4)--(122.5) 合并即得等号，并且

$$
M_K\cap Q=\ker w_K,
\qquad
M_K+Q=P^\vee\oplus Q.
\tag{122.6}
$$

因此自然映射

$$
Q/\ker w_K\longrightarrow (P^\vee\oplus Q)/M_K,
\qquad [q]\longmapsto[(0,q)]
\tag{122.7}
$$

既满射又由维数等式知为同构。再用第一同构定理
$Q/\ker w_K\simeq\bigwedge^4V_K$，得到分裂域上的 (122.1)。

所有结构都由原域定义：$V_F=F[T]_{\le m-2}$、$w_F$、正负对合分解和原系数余切像都在 $F$ 上。分裂域扩张后 (122.6) 成立，故忠实平坦性给出

$$
M_F\cap Q_F=\ker w_F,
\qquad
M_F+Q_F=P_F^\vee\oplus Q_F.
\tag{122.8}
$$

于是 (122.7) 和 (122.1) 下降到 $F$，并且秩在扩域前后相同，得到 (122.2)。
这里下降的是这些分裂矩形所张成的 $F$-子空间；不把任何单个带根标签的分裂矩形误称为 $F$-有理函数。

最后说明完整切核。仍令 $Q=\operatorname{Sym}^2(\bigwedge^2V_K)$，其中
$\xi\odot\eta$ 表示对称代数中的乘积；其线性对偶
$Q^\vee=\operatorname{Hom}_K(Q,K)$ 使用求值配对 $\langle\Pi,q\rangle=\Pi(q)$。定义

$$
\kappa:\bigwedge^4V_K^\vee\longrightarrow Q^\vee,
\qquad \kappa=w_K^*.
\tag{122.9}
$$

这里用行列式配对 $\langle x_1\wedge\cdots\wedge x_4,v_1\wedge\cdots\wedge v_4\rangle=\det(x_i(v_j))_{i,j=1}^4$
识别 $\bigwedge^4V_K^\vee=(\bigwedge^4V_K)^\vee$。具体地，归一化由下式完全指定：

$$
\kappa(\omega)(\xi\odot\eta)
 =\langle\omega,\xi\wedge\eta\rangle,
\qquad \xi,\eta\in\bigwedge^2V_K.
\tag{122.10}
$$

两个二次外幂的外乘满足 $\xi\wedge\eta=\eta\wedge\xi$，故右端是对称双线性形式，
在 $Q$ 上给出唯一的线性泛函。由 (121.3)，它恰满足
$\langle\kappa(\omega),q\rangle=\langle\omega,w_K(q)\rangle$；
下文的 $\Pi(q)$ 均指这个泛函的求值。

取上面选出的 $e_i=(\ell_i,q_i)$，令

$$
L:P\longrightarrow K^a,
\qquad
L(u)=(\ell_1(u),\ldots,\ell_a(u)).
\tag{122.11}
$$

它是同构。给定 $\Pi=\kappa(\omega)$，定义

$$
\begin{aligned}
 u_\Pi&=-L^{-1}\bigl(\Pi(q_1),\ldots,\Pi(q_a)\bigr)\\
 &=-L^{-1}\bigl(\langle\omega,w_K(q_1)\rangle,\ldots,
               \langle\omega,w_K(q_a)\rangle\bigr).
\end{aligned}
\tag{122.12}
$$

则 $(u_\Pi,\Pi)$ 消去全部 $M_K$。事实上，(122.6) 表明每个
$(\ell,q)\in M_K$ 都可唯一写为

$$
(\ell,q)=\sum_i c_i(\ell_i,q_i)+(0,h),
\qquad h\in\ker w_K.
\tag{122.13}
$$

由 (122.12) 第一项的配对为零，而 $\Pi(h)=0$。反过来，若 $(u,\Pi)$ 消去 $M_K$，则它消去 $0\oplus\ker w_K$，故
$\Pi\in(\ker w_K)^\perp=\operatorname{im}w_K^*$；一旦 $\Pi$ 固定，消去 $e_i$ 的方程唯一决定 $u$。所以

$$
\ker J_K^\vee\simeq\kappa(\bigwedge^4V_K^\vee).
\tag{122.14}
$$

同一唯一性将 (122.14) 下降到 $F$，得到
$\ker J^\vee\simeq\kappa(\bigwedge^4V_F^\vee)$。这也说明改变根的排序、参考系数、双曲补空间、环面横截面或所选正向枢轴只改变坐标表示，不改变外四次符号和其唯一提升。指定的 $\theta$ 和连续幂识别仍是本定理的一部分。证毕。

**命题 122.2（任意坐标中的完整耦合修正）。** 在定理 122.1 的任一对合相容切片中，写原系数类为 $(\ell_I,q_I)$。取 $a$ 个正向基类 $(\ell_i,q_i)$，并令

$$
 C(\ell)=(L^\vee)^{-1}(\ell)\in (K^a)^\vee\simeq K^a,
\qquad
q_I^{\mathrm{red}}=q_I-\sum_{i=1}^a C(\ell_I)_i q_i.
\tag{122.15}
$$

则

$$
q_I^{\mathrm{red}}\in\ker w_K
\quad\text{对每一个原系数类 }I.
\tag{122.16}
$$

因此对任意外四次符号 $\Pi=\kappa(\omega)$，完整切核向量的正向分量必须是 (122.12)；在任意图坐标中不能把它误写成零正向分量。若选用原系数正向枢轴作为切片坐标，(122.15) 把该修正吸收到正参数中，才表现为纯负符号。

证明。由 (122.6)，从 $(\ell_I,q_I)$ 减去具有相同正向分量的枢轴线性组合，所得向量属于 $M_K\cap Q=\ker w_K$，这正是 (122.15)--(122.16)。对偶化后，消去枢轴的唯一方程就是 (122.12)。证毕。

## 123. 完整中文普通语言表述

**定理 123.1（原连续幂窗口的白话等价表述）。** 设 $F$ 是特征零域，$D/F$ 是次数 $2m$ 的可分域扩张，$m\ge5$；取任一本原元 $\theta$，并使用
$1,\theta,\ldots,\theta^{m-1}$ 的实际连续幂窗口和原来的带标签互补系数。令 $Z$ 是原系数像的正规化。则原系数到 $Z$ 的一阶余切映射恰好漏掉

$$
\binom{m-1}{4}
$$

个方向；这些方向组成 $F[T]_{\le m-2}$ 的四次外幂。等价地，像秩是

$$
\frac{m(m-1)}2
+\frac12\left(\frac{(m-1)(m-2)}2\right)
 \left(\frac{(m-1)(m-2)}2+1\right)
-\binom{m-1}{4}.
\tag{123.1}
$$

这个秩是余切映射的像秩，不是原系数环的嵌入维数。其对偶切核中的每一个四次外幂符号，都有唯一的正向一阶补偿；该切核属于 $Z$ 到原系数像的映射。

证明。把 $f$ 的根全部放进 $K$，但保留它们的原标签。先看一个实际矩形：两组各有 $m-2$ 个根，剩下四个根分成两列和两行。实际评价矩阵的变化式 (120.8)--(120.9) 同时记录了输出行变化和作为基的那组行变化。若变化只发生在第一组根内部，矩形的两列不动；若只发生在第二组根内部，矩形的两行不动。因此矩形对数的负微分同时消去两组根的两两评价，必定是两个根多项式外积的倍数。取第一组中的一个根 $u$ 和第二组中的一个根 $v$ 直接代入，得到

$$
(d\log r)(H_{uv})
=(\alpha-\gamma)(\beta-\delta)F_B(u)F_A(v).
$$

因为
$(F_A\wedge F_B)(u,v)=-F_B(u)F_A(v)$，这个倍数确实是
$-(\alpha-\gamma)(\beta-\delta)/2$，并且永远不为零。

前卷的带符号互补公式说明 $r+\iota(r)$ 和 $(r-\iota(r))^2$ 都是原系数函数。前者在固定点的正向微分是矩形坐标微分的两倍，故可以选出全部 $a=m(m-1)/2$ 个正向枢轴；后者没有正向一次项，只留下

$$
4r(C)^2[d\log r]_-^2,
$$

所以是真正属于原系数环的纯负二次信息。这里用的是实际符号系数和实际单位，未把原系数环扩大成抽象不变量环。

剩下的问题是这些纯二次信息是否覆盖全部可见方向。令 $d=m-2$。固定一组 $d$ 个根 $A$，其外面有 $d+4$ 个根。任取其中 $d+2$ 个，每次删去两个，得到多项式 $G_{ij}$。在所有无序节点对上评价 $G_{ij}(s)G_{ij}(t)$，只有被删去的那一对给出非零值；因此这些平方构成
$\operatorname{Sym}^2V$ 的基。于是固定 $A$ 时，矩形平方让第二个多项式任意变化。再固定第二个多项式，重复一次插值，便得到任意 $u,v\in V$ 的分解平方

$$
\mathcal T(u\wedge v,u\wedge v)=0
$$

只要 $\mathcal T$ 消去所有实际矩形平方。把这个恒等式极化，
$\mathcal T(u\wedge v,w\wedge z)$ 变成四个变量的完全交错形式。换句话说，实际矩形平方的消去空间正好是四次外幂的对偶，实际矩形平方本身正好是外乘映射
$\operatorname{Sym}^2(\bigwedge^2V)\to\bigwedge^4V$ 的核。

因此原系数像同时含有全部正向枢轴和全部 $\ker w$ 的纯负部分。正向枢轴与纯负部分在同一个直和余切空间中独立，故像的余维至多是
$\dim\bigwedge^4V=\binom{m-1}{4}$。前卷已经给出相反方向的下界，所以只能取等号。商
$Q/\ker w$ 由外乘映射直接识别为 $\bigwedge^4V$，这给出 (123.1) 和定理 122.1。

最后，若把四次外幂符号固定下来，枢轴方程唯一解出正向分量；其公式是
$-L^{-1}(\Pi(q_1),\ldots,\Pi(q_a))$。所以完整切核不是随意的纯负二次核，而是每个外四次符号的一次唯一提升。上述等式在分裂域成立，所有空间和映射都来自 $F$；忠实扩域后下降得到原域结论。这个证明只涉及指定连续幂窗口处的正规化余切和切核，不涉及更高阶形式芽、导子理想或全局次数。证毕。

**注记 123.2（几何层次）。** 外四次空间描述的是
$Z=\operatorname{Spec}B_F$ 到原系数像的正规化差异。光滑商 $X_D$ 的负切空间本身仍是前卷识别的
$(\bigwedge^2V_F)^\vee$；不能把它的平滑一阶方向数与 (122.2) 的正规化切核混为同一对象。矩形插值也只对实际根集和指定 $\theta$ 的连续幂表示作出结论。

## 追加锚（本行以下为增补区）
