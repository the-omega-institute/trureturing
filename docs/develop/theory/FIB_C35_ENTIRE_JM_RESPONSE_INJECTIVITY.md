# FIB C35 整个第五纤维的实际 JM 联合响应单射

## 1. 完整世界、固定历史与原恢复问题

**定义 1.1（完整原域与实际读数）。** 沿用《[FIB 双末根平面的完整逆与第四 J 精确对腔室](FIB_TERMINAL_ZERO_PLANE_INVERSE_AND_J_PAIR_CHAMBER.md)》（下称前卷）定义 1.1、9.1 的模型。一个完整世界是三元组 $W=(P,g,d)$，其中

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},
$$

$$
0<r<1,\qquad b,c>0,\qquad bc=r(1-r),\qquad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\qquad d\in\mathbb R.
\tag{1.1}
$$

正非对角元起初无上界。每个世界只有一个整个增益多项式和一个固定常漂移；不同世界之间不要求增益或漂移相同。全部符号、采样零、非采样零、重根与次数下降均属于此域。原读数为

$$
Q_0=I,\qquad Q_i=E_iQ_{i-1},\qquad
y_i(W)=d+g(i)\operatorname{tr}(Q_iP),\qquad E_i\in\{J,M\}.
\tag{1.2}
$$

初读计数，每个单独动作后立即读取，原时钟为 $0,\ldots,7$。一条轨迹不重置、不复制、不跳读、不加空动作、不重编号、不增加端口。互择动作的响应函数比较同一个已经固定的世界，不表示同时取得两种读数。完整目标始终是 $W$。

**定义 1.2（精确 C35 历史与两个实际续行响应）。** 固定

$$
A=24,\quad C=35,\quad z=\frac{26372}{875},\quad
Y=\frac{528}{35},\quad p_\star=-\frac{9596}{525},
$$

$$
H_4^\star=(0,J,A,M,C,J,z,M,Y),\qquad
H_5^\star=(H_4^\star,M,p_\star).
\tag{1.3}
$$

$\mathcal F(H)$ 表示实现全部字面历史 $H$ 的合法完整世界。取

$$
c=\frac{r(1-r)}b,\quad j=b+c,\quad T=1+b,\quad
U=1+2b,\quad n=j+r,\quad L=jTn.
\tag{1.4}
$$

以 $P(r,b)$ 表示由式 (1.1)、(1.4) 确定的源矩阵。在 $H_5^\star$ 后实际选择第六 $J$、第七 $M$，其响应记为

$$
h(W)=d+g(6)(1+2r+2b+c),\qquad
m(W)=d+g(7)(2+5b+c).
\tag{1.5}
$$

这些公式来自下列实际左乘积；时间词的最右矩阵因子最早作用。

| 原时钟 | 时间词 | $Q_i$ | $\operatorname{tr}(Q_iP)$ |
| --- | --- | --- | --- |
| $0$ | 空词 | $I$ | $1$ |
| $1$ | $J$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $j$ |
| $2$ | $JM$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $T$ |
| $3$ | $JMJ$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $n$ |
| $4$ | $JMJM$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $U$ |
| $5$ | $JMJMM$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $n+U$ |
| $6$ | $JMJMMJ$ | $\left(\begin{smallmatrix}3&1\\2&1\end{smallmatrix}\right)$ | $1+2r+2b+c$ |
| $7$ | $JMJMMJM$ | $\left(\begin{smallmatrix}2&1\\5&2\end{smallmatrix}\right)$ | $2+5b+c$ |

**定义 1.3（失败递归与共同父问题）。** 对同一历史下的任意世界集 $K\subseteq\mathcal F(H)$，包括无限集，取前卷式 (1.3) 的原递归

$$
\begin{aligned}
L_0(K,H)&\iff |K|\ge2,\\
L_{s+1}(K,H)&\iff |K|\ge2\ \land
\bigwedge_{E\in\{J,M\}}\exists u\in\mathbb R:\\
&\hspace{16mm}L_s\bigl(K\cap\mathcal F(H,E,u),(H,E,u)\bigr).
\end{aligned}
\tag{1.6}
$$

基数数不同完整三元组。特别空集或单点集不满足任何失败守卫。原恢复问题仍是在式 (1.1) 全域上，以同一个确定性历史依赖策略，用零至七的至多八次总读恢复完整世界；不对策略附加连续、可测或可计算性。原根问题保留 $L_7$、全部祖先、互择动作与每一停止守卫。八次与九次总读的比较及九读上界也是该全域的策略问题。

前卷第 11 节的同父问题使用
$H_4(C,z,Y)=(0,J,24,M,C,J,z,M,Y)$，共享同一 $C,z,Y$，并在每个第五动作 $F$ 下共享同一 $p_F$，在每个第六动作 $E$ 下共享同一 $v_{FE}$。其四个块为

$$
\bigwedge_{F\in\{J,M\}}\ \bigwedge_{E\in\{J,M\}}
\exists v_{FE}\in\mathbb R:\quad
L_1\bigl(\mathcal F(H_4,F,p_F,E,v_{FE}),
(H_4,F,p_F,E,v_{FE})\bigr).
\tag{1.7}
$$

同一第六节点的两个最终动作允许使用不同、交叠或不相交的终端碰撞对，但必须使用该节点已经取得的同一个响应。式 (1.3) 只固定其中一个第五 $M$ 响应，不替代式 (1.7) 的其他参数与共同实现条件。

## 2. 整个兼容纤维的联合单射

**定理 2.1（精确历史上的整个实际 JM 联合响应）。** 在定义 1.1 的完整原域中，映射

$$
\mathcal F(H_5^\star)\longrightarrow\mathbb R^2,\qquad
W\longmapsto(h(W),m(W))
\tag{2.1}
$$

为单射。整个兼容源集恰为下文式 (2.25) 的两条图；每个源对应唯一完整世界，逆由式 (2.18) 给出。此结论不预设源有界、增益精确三次、任一样本非零、根简单、固定漂移或固定增益方向。

证明。前卷定理 9.3、10.2 给任意实历史的固定源唯一性与完整纤维逆。以下使用同一四节点插值，在当前精确历史上写出多项式、全域包含及实际响应的全部对应。

### 2.1. 原方程的兼容多项式

初读及原时钟一至三的正迹迫使

$$
g(0)=-d,\qquad g(1)=\frac{A-d}j,\qquad
g(2)=\frac{C-d}T,\qquad g(3)=\frac{z-d}n.
\tag{2.2}
$$

令 $\ell_i(s)=\prod_{0\le a\le3,\ a\ne i}(s-a)/(i-a)$。四个节点互异，故
$g(s)=\sum_{i=0}^3g(i)\ell_i(s)$；这里不要求任何样本非零。所用普通 Lagrange 插值见 Berrut–Trefethen，《[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)》，§2；前卷式 (10.14) 的四行权重直接为

$$
\begin{pmatrix}g(4)\\g(5)\\g(6)\\g(7)\end{pmatrix}
=
\begin{pmatrix}
-1&4&-6&4\\
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}
\begin{pmatrix}g(0)\\g(1)\\g(2)\\g(3)\end{pmatrix}.
\tag{2.3}
$$

将前两行代入原时钟四、五的读数，得到

$$
\begin{aligned}
a_4&=1+U(1-4/j+6/T-4/n),\\
k_4&=U(4A/j-6C/T+4z/n),\\
a_5&=1+(n+U)(4-15/j+20/T-10/n),\\
k_5&=(n+U)(15A/j-20C/T+10z/n),\\
a_4d&=Y-k_4,\qquad a_5d=p_\star-k_5.
\end{aligned}
\tag{2.4}
$$

定义整数多项式 $S(r,b)=\sum_{a,e}s_{ae}r^ab^e$，其全部非零系数如下，未列项为零。

| $a$ | $e$ | $s_{ae}$ |
| --- | --- | --- |
| 6 | 1 | 446700 |
| 6 | 0 | -259800 |
| 5 | 2 | -893400 |
| 5 | 1 | -820500 |
| 5 | 0 | 779400 |
| 4 | 3 | -1297084 |
| 4 | 2 | 1891444 |
| 4 | 1 | -14092 |
| 4 | 0 | -779400 |
| 3 | 4 | 2127484 |
| 3 | 3 | 2208874 |
| 3 | 2 | -1047871 |
| 3 | 1 | 702884 |
| 3 | 0 | 259800 |
| 2 | 5 | 688376 |
| 2 | 4 | -3711170 |
| 2 | 3 | -1518547 |
| 2 | 2 | -177718 |
| 2 | 1 | -314992 |
| 1 | 6 | -1108084 |
| 1 | 5 | -159582 |
| 1 | 4 | 2127519 |
| 1 | 3 | 668307 |
| 1 | 2 | 227545 |
| 0 | 7 | 225008 |
| 0 | 6 | 1301952 |
| 0 | 5 | -367156 |
| 0 | 4 | -578255 |
| 0 | 3 | -161160 |

代入 $c=r(1-r)/b$ 后，式 (2.4) 的交叉相消给精确恒等式

$$
S=-\frac{2625}{2}b^3L
\bigl[a_5(Y-k_4)-a_4(p_\star-k_5)\bigr].
\tag{2.5}
$$

此式可由式 (2.4) 清正分母后逐项合并取得，也等于前卷式 (10.3) 的 $-(2625/2)R_M$ 在当前参数的取值。因此任意兼容世界必给严格源零点 $S=0$。这里尚未除以 $a_4$ 或任何增益样本。

### 2.2. 有限系数与闭矩形上的符号

对有理多项式 $f(u,v)=\sum a_{ef}u^ev^f$，设其坐标次数为 $(n,m)$。定义

$$
\mathcal B_{ij}(f)=
\sum_{e=0}^i\sum_{f=0}^j a_{ef}
\frac{\binom ie}{\binom ne}\frac{\binom jf}{\binom mf},
\qquad 0\le i\le n,\quad0\le j\le m.
\tag{2.6}
$$

零次方向只取下标零。对有理闭矩形 $R=[a,a']\times[q,q']$，
$\mathcal B^R(f)$ 表示先代入 $b=a+(a'-a)u$、$x=q+(q'-q)v$，再用式 (2.6)；每个多项式使用其自身坐标次数。

所用张量 Bernstein 恒等式与《[FIB 同一第五 M 纤维的整个增益平面穷尽](FIB_V1_ENTIRE_GAIN_PLANE_SATURATION.md)》式 (29.13)–(29.14) 相同。具体地，令
$B_{i,n}(u)=\binom niu^i(1-u)^{n-i}$，则

$$
f(u,v)=\sum_{i=0}^n\sum_{j=0}^m
\mathcal B_{ij}(f) B_{i,n}(u)B_{j,m}(v).
\tag{2.7}
$$

事实上
$\binom ni\binom ie/\binom ne=\binom{n-e}{i-e}$，从而
$\sum_{i=e}^n\binom ie B_{i,n}(u)/\binom ne=u^e$；两个方向相乘并按幂系数求和即得式 (2.7)。基函数在单位闭方形上非负且和为一，所以全体系数严格正或严格负就给整个闭矩形同一严格符号，包括边和顶点。

首先展开 $S(r,1+t)=\sum_{k=0}^7a_k(r)t^k$。各 $a_k$ 在 $r\in[0,1]$ 上的一元 Bernstein 系数的精确范围是

| $k$ | $\deg a_k$ | 最小系数 | 最大系数 |
| --- | --- | --- | --- |
| 0 | 6 | $1242592/3$ | $1426013/2$ |
| 1 | 6 | $18008705/6$ | $32050601/6$ |
| 2 | 5 | $8744206$ | $16629878$ |
| 3 | 4 | $13131722$ | $27768580$ |
| 4 | 3 | $11557068$ | $24990525$ |
| 5 | 2 | $6050014$ | $12169724$ |
| 6 | 1 | $1768924$ | $2877008$ |
| 7 | 0 | $225008$ | $225008$ |

所有最小系数严格正，故 $b\ge1$ 时 $S(r,b)>0$，包括无界的 $b$ 端。再定义精确多项式商

$$
C_0(r,u)=\frac{S(r,r(1-r)u)}{r^3(1-r)^3}.
\tag{2.8}
$$

分子在 $\mathbb Q[r,u]$ 中被分母整除，商的坐标次数为 $(8,7)$；在 $[0,1]^2$ 上，全部 $72$ 个式 (2.6) 系数的最小值为 $11193$、最大值为 $537526$。若严格源有 $c\ge1$，则 $u=1/c=b/[r(1-r)]\in(0,1]$，正因子 $r^3(1-r)^3$ 给 $S>0$。于是 $S=0$ 的严格源必满足

$$
0<b<1,\qquad 0<c<1.
\tag{2.9}
$$

这两个上界由原方程导出，不是增添的源承诺。最后 $S(3/4,b)$ 次数为七，两个区间上的精确 Bernstein 系数范围为

| $b$ 区间 | 最小系数 | 最大系数 |
| --- | --- | --- |
| $[0,1/2]$ | $2377877/7168$ | $22359367/8960$ |
| $[1/2,1]$ | $2980827/2048$ | $458212529/1024$ |

故严格源零点还满足 $r\ne3/4$。本小节每个有限数值均由 $29$ 个整数系数、式 (2.6) 及列出的有理代入唯一指定。

### 2.3. 两张多项式图及完整世界的无零分母逆

按 $r<3/4$ 或 $r>3/4$ 取图 A、B，分别代入

$$
\begin{array}{c|c|c|c|c}
\text{图}&r&c&X_{\max}&\lambda\\ \hline
\mathrm A&bx&x(1-bx)&4&3/4\\
\mathrm B&1-bx&x(1-bx)&4/3&1/4
\end{array}
\tag{2.10}
$$

由式 (2.9)，图 A 的 $x=r/b=c/(1-r)<4$，图 B 的 $x=(1-r)/b=c/r<4/3$。所以所有严格零源恰落在两个互不相交的严格图域内，其闭包含域为

$$
D_\nu=\{(b,x):0\le b\le1,\ 0\le x\le X_{\max,\nu},\ bx\le\lambda_\nu\},
\qquad \nu\in\{\mathrm A,\mathrm B\}.
\tag{2.11}
$$

在每图中先用式 (2.10) 代入 $r,c$，此后 $j,n,T,U,L$ 均是 $b,x$ 的多项式。定义

$$
F_\nu(b,x)=\frac{S(r_\nu(b,x),b)}{b^3}.
\tag{2.12}
$$

这是在多项式环中的精确整除，故也定义 $b=0$ 的延拓，坐标次数为 $(4,6)$。以下各式均按所选图作多项式运算，省略下标 $\nu$：

$$
\begin{aligned}
\Delta&=L+U(L-4Tn+6jn-4jT),\\
B&=YL-U(4ATn-6Cjn+4zjT),\\
V_0&=-B,\\
V_1&=(A-Y)Tn+U\bigl(ATn+6(A-C)n+4(z-A)T\bigr),\\
V_2&=(C-Y)jn+U\bigl(Cjn+4(A-C)n+4(z-C)j\bigr),\\
V_3&=(z-Y)jT+U\bigl(zjT+4(A-z)T+6(z-C)j\bigr).
\end{aligned}
\tag{2.13}
$$

直接合并项有

$$
\Delta=La_4,\quad B=L(Y-k_4),\quad
jV_1=A\Delta-B,\quad TV_2=C\Delta-B,\quad nV_3=z\Delta-B.
\tag{2.14}
$$

为表达实际末两读，定义

$$
\begin{aligned}
G_6&=-10V_0+36V_1-45V_2+20V_3,\\
G_7&=-20V_0+70V_1-84V_2+35V_3,\\
\tau_6&=1+2r+2b+c,\qquad \tau_7=2+5b+c,\\
H&=B+\tau_6G_6,\qquad M_n=B+\tau_7G_7.
\end{aligned}
\tag{2.15}
$$

两条多项式余项恒等式为

$$
\begin{aligned}
B+U(-V_0+4V_1-6V_2+4V_3)-Y\Delta&=0,\\
B+(n+U)(-4V_0+15V_1-20V_2+10V_3)-p_\star\Delta
&=-\frac2{2625}F.
\end{aligned}
\tag{2.16}
$$

式 (2.14) 可逐个展开；例如 $jV_1=A[L+U(L-4Tn+6jn-4jT)]-YL+U(4ATn-6Cjn+4zjT)$，消去相反项即得 $j$ 乘式 (2.13) 的 $V_1$。其余两个同理。式 (2.16) 第一行代入 $V_i$ 消去全部项；第二行由式 (2.5) 和 $L(Y-k_4)=B$、$La_4=\Delta$ 得到，乘开时 $b^3$ 正好由式 (2.12) 消去。这些均为多项式恒等式，不要求 $F=0$ 或 $\Delta\ne0$。

下一小节将先证明每个严格零点的

$$
F_x>0,\qquad \Delta<0.
\tag{2.17}
$$

在此之后才定义完整逆

$$
d=\frac B\Delta,\qquad
g(s)=\frac1\Delta\sum_{i=0}^3V_i\ell_i(s),\qquad
W_\nu(b,x)=(P(r_\nu,b),g,d).
\tag{2.18}
$$

式 (2.14) 给全部前四读，式 (2.16) 给后两读；因此每个严格零源产生一个实现整个 $H_5^\star$ 的世界。它的增益不恒零：否则初读与第一动后读数均等于 $d$，与 $0\ne24$ 矛盾。反向，任一兼容世界由式 (2.5) 落在严格零集，由式 (2.17) 及 $L>0$ 知 $a_4\ne0$，于是式 (2.4) 强迫同一个 $d=B/\Delta$，前四样本再强迫式 (2.18) 的整个 $g$。这证明严格源零集与全部完整世界的双射，也与前卷定理 10.2 的逆相同。在该双射下，式 (2.3)、(2.15) 进一步给

$$
h=\frac H\Delta,\qquad m=\frac{M_n}\Delta.
\tag{2.19}
$$

此推导只在证明 $\Delta<0$ 后除它；从不除以 $g(i)$、最高次系数、根差或判别式。

### 2.4. 两张闭图域的完整有限覆盖证书

图 A 取 $k=6$，图 B 取 $k=7/4$，并定义

$$
\begin{aligned}
N&=M_n-kH,\\
K&=F_x(N_b\Delta-N\Delta_b)-F_b(N_x\Delta-N\Delta_x),\\
\Sigma&=M_n-4H-120\Delta.
\end{aligned}
\tag{2.20}
$$

以下有序多项式列完全由式 (2.10)–(2.15)、(2.20) 指定：

$$
\begin{array}{c|ccccc}
\mathrm A&F&F_x&-\Delta&-K&\Sigma\\
\mathrm B&F&F_x&-\Delta&-K&-\Sigma\\ \hline
\text{坐标次数}&(4,6)&(4,5)&(4,4)&(11,15)&(4,6).
\end{array}
\tag{2.21}
$$

为列出覆盖，在各图的整个矩形 $R_0=[0,1]\times[0,X_{\max}]$ 上定义前序二叉树。根深度为零，遇字符 $X$ 时，在偶深度平分 $b$ 区间、奇深度平分 $x$ 区间；两者均取精确中点。其后先读左子树，再读右子树。三个叶字符的数学条件为：

| 字符 | 所在闭矩形 $R=[b_0,b_1]\times[x_0,x_1]$ 的条件 |
| --- | --- |
| $O$ | $b_0x_0>\lambda$ |
| $Z$ | $\mathcal B^R(F)$ 的全部系数严格正，或全部严格负 |
| $C$ | 式 (2.21) 最后四个多项式各自的 $\mathcal B^R$ 全部系数严格正 |

每个字符串恰消耗一棵完整树；无其他叶字符。下列行的换行仅分组，连接各行就是全部前序字符。

图 A：

```text
XXXXXXZXXZXXZXXZXXZXXXXXXCZXCZZXXXCZXCZZZXXXXXCZXCZZXXXCZCZZXZXXXXCZXCZZXXXCZXCZ
ZXZXXZXXXXCXZXCZXZXXCZXCZZXXXZXXCZXCZCZXZXXCZXCZXZXXZXXZXXCXZXXZXCZZXZXXXXCZCZXC
ZXZXXZXXCZXCZXZXXCZXCZXZXXZXXZXXCZXCZXZCXZXXZCXZCXZXXZXXZXXZXXZCXZCZZZZXXXZXXXXX
XXXZXXXCZXCZZZXXXXXCZXCZZXXXCZCZZZXXXXXCZXCZZXXXCZXCZZZZXXXXXXXCZXXCZXXCZXCZZXXX
ZCXZCZZXXXXXZCXZCZXXXZCXZCZZZZZXXXXXXXXXXXZXCZZXXCZXCZXZXXCZXCZZXXXZXXCZCXZXCXZC
ZZXXXXXZXXZCXZCXZXXZCXZCZXXXZXXZCZZXXXXCZXCZZXXXCZCZZZXXXXXZXXCZXCZXZXXXXZCXZCZX
XXZCXZCXZXCZZXXXZXXZCXZCXZXXZCXZCZZZXZXXXXXXXXZXXZXCZZZXXXXCZXCZZXXXCZCZXZXXCZXC
ZZXXXZXXCXXCZCCXZCXZXXZXCZZZXXXZXXXXCZXCZZXCZXCXXCZXCZXXZXZXZOXZOXXZXZXZXZXXZOXZ
OXXXXZXZXZOXXZXZOOXXXXXZOOOOOXXXXXXZOOOOOOXXXXCXXCXCXXCZZXXXCZZZXXXXCZZXXXZOOOXZ
OXXXXXXCXCZZXXXCZXCZZZZXXZOOO
```

图 B：

```text
XXXXCXXXXXXCZXCZZXXXCZXCZZZXXXXXCZZZZZXXCXZXCXCXXCXCZXXCZZXXXXXZXCZZXCZZZXZXXZXX
ZOOXZOXXXXXXXXZXZXZXXZXXZCCXXXZCCCXXZXXZXZCXXXZCCCXXXXZCCXXCZZXXXCZZZXXXXXXZXZXZ
CXXXZXZCXXZCCCXXXXXXZCCCCZZXXXCZZZZZXXXXXCZZZZZZZZO
```

上述树和式 (2.6) 给以下有限有理不等式：全部 $29$ 个 $O$ 叶满足其严格乘积不等式；全部 $Z$ 叶的 $F$ 系数具有要求的同一严格符号；全部 $C$ 叶的最后四列系数严格正。逐列系数总数如下。

| 图 | $Z$ 叶 | $C$ 叶 | $O$ 叶 | 最大深度 | $Z$ 上 $F$ 系数 | $C$ 上 $F_x$ | $C$ 上 $-\Delta$ | $C$ 上 $-K$ | $C$ 上有号 $\Sigma$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A | 235 | 115 | 25 | 20 | 8225 | 3450 | 2875 | 22080 | 4025 |
| B | 64 | 38 | 4 | 17 | 2240 | 1140 | 950 | 7296 | 1330 |

为使每个系数的有理运算完全显式，若原幂展开为 $f(b,x)=\sum p_{ef}b^ex^f$，则矩形仿射代入后的幂系数是

$$
\widetilde p_{ij}=
(b_1-b_0)^i(x_1-x_0)^j
\sum_{e\ge i,\ f\ge j}p_{ef}\binom ei\binom fj
b_0^{e-i}x_0^{f-j}.
\tag{2.22}
$$

用 $\widetilde p_{ij}$ 代入式 (2.6) 就是上述每个有限不等式，无需根近似或外部系数表。等价的逐层运算是中点 de Casteljau：对一条 Bernstein 系数列，反复取相邻均值；每层首项依次组成左半区列，每层末项逆序组成右半区列。该恒等式由式 (2.7) 在 $u/2$、$(1+u)/2$ 的代入和二项式展开得到，张量情形只在选定坐标方向运算。所有系数均为有理数；共同的严格正有理倍数不改变这些不等式。

现在将有限符号传到整个域。每次二分的两个闭子矩形之并等于父矩形，故完整树的闭叶覆盖 $R_0$。$b,x\ge0$ 使 $O$ 叶全部满足 $bx>\lambda$，不能遇到 $D_\nu$；$Z$ 叶由式 (2.7) 在整个闭矩形上无 $F$ 零点。因此 $D_\nu$ 中的每个 $F$ 零点必落在至少一个 $C$ 叶，其上式 (2.7) 给

$$
\begin{array}{c|cccc}
\mathrm A&F_x>0&\Delta<0&K<0&\Sigma>0\\
\mathrm B&F_x>0&\Delta<0&K<0&\Sigma<0.
\end{array}
\tag{2.23}
$$

叶边界也在覆盖内。因而这不是从有限采样点推断零曲线；每个符号都覆盖整个闭叶，包括两个 $b\to0$ 端及所有叶交界。这证明了式 (2.17)，并给随后的全域方向与跨图分离。

### 2.5. 全部源零点恰为两个连通参数图

固定 $b\in(0,1)$，在 A、B 分别令

$$
u_\nu(b)=\min\{X_{\max,\nu},\lambda_\nu/b\}.
$$

这里 $u_\nu(b)>0$。若上端点取 $\lambda_\nu/b$，则 $r=3/4$，由第 2.2 小节有 $F(b,u_\nu)>0$。若上端点取 $X_{\max,\nu}$，则 A 中 $x=4$、$r\le3/4$、$c=4(1-r)\ge1$，B 中 $x=4/3$、$r\ge3/4$、$c=(4/3)r\ge1$；同一小节仍给 $F(b,u_\nu)>0$。

式 (2.23) 给 $[0,u_\nu(b)]$ 上每个零点的 $F_x>0$，故每个零点均为简单向上穿越。多项式不恒零，因为上端为正；其零点有限。若有两个向上简单穿越，取相邻两零点，则前一个右侧为正、后一个左侧为负，介值定理迫使中间另有零点，矛盾。因此至多一个零点。若 $F(b,0)<0$，介值定理给恰一个内部零点；若 $F(b,0)>0$，任何首次向上穿越之前的负值又会迫使更早的零点，所以无零点。若 $F(b,0)=0$，端点导数为正，只剩这个边界零点，内部无零点。

下端的精确多项式为

$$
\begin{aligned}
F_{\mathrm A}(b,0)=q_A(b)
&=225008b^4+1301952b^3-367156b^2-578255b-161160,\\
F_{\mathrm B}(b,0)=2q_B(b),\qquad
q_B(b)&=112504b^4+96934b^3+80819b^2-17211b-49805.
\end{aligned}
\tag{2.24}
$$

对 $b>0$，

$$
\begin{aligned}
\left(\frac{q_A(b)}{b^2}\right)'&=
450016b+1301952+\frac{578255}{b^2}+\frac{322320}{b^3}>0,\\
\left(\frac{q_B(b)}b\right)'&=
337512b^2+193868b+80819+\frac{49805}{b^2}>0.
\end{aligned}
$$

两比值在 $b\to0^+$ 时趋向负无穷，在 $b\to\infty$ 时趋向正无穷；故各恰有一个正零点 $\beta_A,\beta_B$。又
$q_A(1)=420389>0$、$q_B(1)=223241>0$，两根均小于一。精确符号界为

$$
q_A(17/20)<0<q_A(851/1000),\qquad
q_B(583/1000)<0<q_B(73/125).
$$

于是整个严格零源集恰为

$$
\begin{aligned}
\Gamma_A&=\{(r,b):0<b<\beta_A,\ r=bx_A(b)\},\\
\Gamma_B&=\{(r,b):0<b<\beta_B,\ r=1-bx_B(b)\},\\
\Gamma&=\{(r,b):0<r<1,\ b>0,\ S(r,b)=0\}
=\Gamma_A\ \dot\cup\ \Gamma_B,
\end{aligned}
\tag{2.25}
$$

其中 $x_\nu(b)$ 是 $(0,u_\nu(b))$ 内唯一零点。每个这样的点都有 $0<r<1$、$b,c>0$，且 $bc=r(1-r)$；式 (2.9) 随后保证 $c<1$。在 $b=\beta_\nu$ 唯一零点为 $x=0$，给 $r=0$ 或 $1$，不属于严格域。第 2.2 小节已排除其他 $b$、$c$ 及 $r=3/4$，所以没有额外的分支或遗漏端。

对多项式方程 $F_\nu(b,x)=0$，式 (2.23) 的 $F_x\ne0$ 满足标准隐函数定理的条件；参见 Rudin，《Principles of Mathematical Analysis》，第 9 章的隐函数定理。每个局部函数由同一 $b$ 上的唯一性拼接，得到整个连通区间 $(0,\beta_\nu)$ 上的可微函数，且

$$
x_\nu'(b)=-\frac{F_b}{F_x}.
\tag{2.26}
$$

式 (2.18) 将这两张完整图分别双射到全部兼容世界的两部分。

### 2.6. 连通图上的严格单调与跨图分离

在任一图上，式 (2.19)、(2.20)、(2.26) 的商法则给

$$
\frac{d}{db}(m-kh)
=\frac{(N_b\Delta-N\Delta_b)F_x
-(N_x\Delta-N\Delta_x)F_b}{\Delta^2F_x}
=\frac K{\Delta^2F_x}<0.
\tag{2.27}
$$

所以 $m-6h$ 在 A 的整个 $(0,\beta_A)$ 上严格递减，$m-(7/4)h$ 在 B 的整个 $(0,\beta_B)$ 上严格递减。严格递减由任意两个参数之间的中值定理得到，使用的是显式多项式曲线的可微性，不是任何策略的正则性。

同图两个世界若有同一 $(h,m)$，则有同一严格单调投影，故 $b$ 相同；唯一零点使 $x$ 相同，源相同，式 (2.18) 使整个增益与固定漂移均相同。

跨图时，式 (2.19)、(2.20)、(2.23) 给

$$
m-4h-120=\frac\Sigma\Delta,
\qquad
\begin{cases}
m-4h<120,&\Gamma_A,\\
m-4h>120,&\Gamma_B.
\end{cases}
\tag{2.28}
$$

因此两图不可能共享同一个响应对。合并同图与跨图两种情形，式 (2.1) 在整个完整世界纤维上为单射。所有增益退化均通过式 (2.2)、(2.18) 保留；式 (2.23) 排除的是由当前历史方程决定的源分母零点，而非预先删掉某类世界。∎

## 3. 任意已获第六 J 切片的最终 M 单射

**推论 3.1（统一同响应消费者与精确第五节点的失败排除）。** 对每个实数 $v$，在完整的实际切片

$$
S_v=\mathcal F(H_5^\star,J,v)
\tag{3.1}
$$

上，原时钟七的实际最终 $M$ 响应为单射。因而对任意基数的 $K\subseteq S_v$，

$$
\neg L_1\bigl(K,(H_5^\star,J,v)\bigr).
\tag{3.2}
$$

特别

$$
\neg L_2\bigl(\mathcal F(H_5^\star),H_5^\star\bigr).
\tag{3.3}
$$

同一结论适用于 $\mathcal F(H_5^\star)$ 的任意子集。它允许各最终动作提出不同、交叠或不相交的终端对。

证明。先固定任意实际响应 $v$。$S_v$ 内每个世界都有 $h=v$。若两个世界实际最终 $M$ 同读，则它们有同一 $(h,m)$；定理 2.1 迫使完整世界相同。因此对任意 $K\subseteq S_v$、任意实数 $w$，

$$
\left|K\cap\mathcal F(H_5^\star,J,v,M,w)\right|\le1.
\tag{3.4}
$$

空或单点的 $K$ 已违反停止守卫。其余 $K$ 的最终 $M$ 分句也因式 (3.4) 没有任何 $L_0$ 叶，故式 (1.6) 给式 (3.2)。这直接作用于整个实际切片，不从非终端失败集抽取同深度失败对。

若式 (3.3) 不成立，$L_2$ 的第六 $J$ 分句必给某个实 $v$，使相应实际切片有 $L_1$，与式 (3.2) 矛盾。对子集的同一论证完全相同。最终 $M$ 的每个纤维都至多一元，所以不同、交叠或不相交的候选终端对均被这个统一分句排除。

作为同历史边界，直接复用《FIB 同一第五 M 纤维的整个增益平面穷尽》例 28.4、前卷定义 12.1 和定理 12.2 的 $C=35$ 对：

$$
P_1=\begin{pmatrix}3/5&1/2\\12/25&2/5\end{pmatrix},\qquad
P_2=\begin{pmatrix}9/10&1/2\\9/50&1/10\end{pmatrix},
$$

$$
g(s)=(s-1)(s-7)\left(\frac{103}{105}s-\frac{24}{7}\right),\qquad
W_i=(P_i,g,24).
\tag{3.5}
$$

这两个固定完整世界沿实际第六 $M$ 的原时钟零至六共同响应

$$
\left(0,24,35,\frac{26372}{875},\frac{528}{35},
-\frac{9596}{525},-\frac{7797}{175}\right),
\tag{3.6}
$$

且原最终 $J,M$ 都响应 $24$，所以该第六 $M$ 节点确有既有的二世界 $L_1$。同一世界对改选第六 $J$ 时，响应分别是

$$
h(W_1)=-\frac{3712}{175},\qquad
h(W_2)=-\frac{4357}{175}.
\tag{3.7}
$$

其不同第六响应与定理 2.1 相容；第六 $M$ 的既有碰撞不补足同一第五节点的第六 $J$ 分句。

式 (3.3) 只排除式 (1.3) 的精确 $p_\star$。同一个 $H_4^\star$ 的其他第五 $M$ 响应、第五 $J$ 臂、其他固定或自由 $C,z,Y$ 父，仍分别属于式 (1.7) 的共同实现问题；该问题要求两个第五臂与四个第六块保持各自已经取得的相同响应。更早祖先、其他动作和全部非单点守卫仍属于定义 1.3 的原根合同。本推论不推出原根 $L_7$、原八读恢复或不可能性、八与九的极小极大比较或九读上界。∎

## 追加锚（本行以下为增补区）

## 4. 自由第五响应上的同历史八读碰撞

**定义 4.1（原源坐标中的碰撞多项式）。** 保持定义 1.1 的全部原域以及定义 1.2 的 $A,C,z,Y,H_4^\star$，第五 $M$ 响应在本节不预定为 $p_\star$。在源坐标 $(r,b)$ 中定义下列有理系数多项式，花体符号区别于第 2 节图坐标中的同名量：

$$
\begin{aligned}
X&=b^2+r-r^2,&N&=X+br,&T&=1+b,&U&=1+2b,\\
\mathscr D&=TXN+U(TXN-4bTN+6XN-4bXT),\\
\mathscr B&=YTXN-U(4AbTN-6CXN+4zbXT),\\
\mathscr V_0&=-\mathscr B,\\
\mathscr V_1&=(A-Y)bTN+
 U\bigl(AbTN+6(A-C)bN+4(z-A)b^2T\bigr),\\
\mathscr V_2&=(C-Y)XN+
 U\bigl(CXN+4(A-C)bN+4(z-C)bX\bigr),\\
\mathscr V_3&=(z-Y)bXT+
 U\bigl(zbXT+4(A-z)b^2T+6(z-C)bX\bigr).
\end{aligned}
\tag{4.1}
$$

再定义

$$
\begin{aligned}
R_5&=b(1+r+3b)+r(1-r),\\
R_6&=b(1+2r+2b)+r(1-r),\\
R_7&=b(2+5b)+r(1-r),\\
\mathscr G_5&=-4\mathscr V_0+15\mathscr V_1-20\mathscr V_2+10\mathscr V_3,\\
\mathscr G_6&=-10\mathscr V_0+36\mathscr V_1-45\mathscr V_2+20\mathscr V_3,\\
\mathscr G_7&=-20\mathscr V_0+70\mathscr V_1-84\mathscr V_2+35\mathscr V_3,\\
\mathscr Q_i&=875\bigl(b\mathscr B+R_i\mathscr G_i\bigr),\qquad i=5,6,7.
\end{aligned}
\tag{4.2}
$$

这里 $875\ne0$，且各 $\mathscr Q_i\in\mathbb Z[r,b]$。原实际左乘积仍记为 $Q_i$，不与分子 $\mathscr Q_i$ 混用。取 $a=1/5$，以 $(x,y,t)$ 为有序变量，定义三个字面的有理多项式

$$
\mathscr F_i(x,y,t)=
 t\mathscr D(y,t)\mathscr Q_i(x,a)
 -a\mathscr D(x,a)\mathscr Q_i(y,t),\qquad i=5,6,7,
\qquad
\mathscr F=(\mathscr F_5,\mathscr F_6,\mathscr F_7)^{\mathsf T}.
\tag{4.3}
$$

三个方程均不取本原部、不另乘逐行因子。定义有理中心、半径及闭盒

$$
m=\frac1{10^{20}}
\begin{pmatrix}
89850698363088918156\\
7833997018546596202\\
91970589378655924931
\end{pmatrix},\qquad
\rho=\frac1{10^{12}},\qquad
\mathcal K=\{u\in\mathbb R^3:\|u-m\|_\infty\le\rho\}.
\tag{4.4}
$$

向量范数为最大绝对坐标，矩阵范数为最大绝对行和。所用有理矩阵为

$$
C_{\rm pre}=\frac1{10^{14}}
\begin{pmatrix}
484000580&-391719536&44432068\\
39998670301&-8950431445&-1109212522\\
-29631340564&7452413434&416274491
\end{pmatrix}.
\tag{4.5}
$$

**定理 4.2（整个第四历史纤维中的精确双世界碰撞）。** 式 (4.3) 在式 (4.4) 的 $\mathcal K$ 中恰有一个实零点，记为 $(\xi,\eta,\theta)$。其坐标为实代数数。由这一零点，下文式 (4.15) 的单个整个增益和固定漂移分别给出两个合法完整世界

$$
W_1=(P(\xi,1/5),g_1,d_1),\qquad
W_2=(P(\eta,\theta),g_2,d_2),
\qquad W_1\ne W_2,
\tag{4.6}
$$

且沿同一实际时间词 $J,M,J,M,M,J,M$ 的原时钟零至七，具有完全相同的八行记录

$$
\left(0,24,35,\frac{26372}{875},\frac{528}{35},p_0,h_0,f_0\right),
\qquad
-7<p_0<-6,\quad 11<h_0<12,\quad107<f_0<108.
\tag{4.7}
$$

其中三个末响应由式 (4.18) 精确定义，区间端点不代替响应本身。此唯一性只指 $\mathcal K$ 内的式 (4.3) 零点。

证明。先给局部零点存在性，再把它与完整原方程相接。

### 4.1. 有理系数界与隔离盒内的零点

对 $P\in\mathbb Q[x,y,t]$，令 $\|P\|_{\rm coeff}$ 为合并同类项后所有系数的绝对值之和，并令

$$
H_i=\sum_{j=1}^3\sum_{k=1}^3
\|\partial_j\partial_k\mathscr F_i\|_{\rm coeff},
\qquad (\partial_1,\partial_2,\partial_3)=(\partial_x,\partial_y,\partial_t).
\tag{4.8}
$$

式 (4.1)–(4.5) 的有理运算给下列界；$J_{\mathscr F}$ 的行次序为 $5,6,7$，列次序为 $x,y,t$：

$$
\begin{aligned}
\|C_{\rm pre}\|_\infty
 &=\frac{12514578567}{25000000000000}<\frac1{1000},\\
\|I-C_{\rm pre}J_{\mathscr F}(m)\|_\infty
 &\le\frac{1166992}{10^{14}}<\frac1{10^6},\\
\|\mathscr F(m)\|_\infty
 &\le\frac{47251031}{10^{22}}<\frac1{10^{13}},\\
\|C_{\rm pre}\mathscr F(m)\|_\infty
 &\le\frac{4715}{10^{24}}<\frac1{10^{16}},\\
(H_5,H_6,H_7)
 &=\left(\frac{2596965156059808}{78125},
 \frac{2727311991107856}{78125},
 \frac{699741400200432}{3125}\right),\\
\max_i H_i&<3\cdot10^{11}.
\end{aligned}
\tag{4.9}
$$

这些是有限有理表达式的不等式：第一项直接取式 (4.5) 的最大绝对行和；第二项把式 (4.3) 微分后在有理点 $m$ 代入，计算 $I-C_{\rm pre}J_{\mathscr F}(m)$ 的最大绝对行和；第三、四项分别对 $\mathscr F(m)$、$C_{\rm pre}\mathscr F(m)$ 取最大绝对坐标。式 (4.8) 对九个有序二阶偏导分别合并系数后求和。所有数据均由式 (4.1)–(4.5) 指定，不涉及任何零点近似。

由式 (4.4) 直接有 $\mathcal K\subset(0,1)^3$，而且在整个盒上 $x>89/100$、$y<2/25$。每个单项式在盒上的绝对值至多为一。因此沿 $m$ 到 $u\in\mathcal K$ 的线段，对每个 Jacobian 行先求各列绝对值之和，再用式 (4.8)，得到

$$
\begin{aligned}
\|J_{\mathscr F}(u)-J_{\mathscr F}(m)\|_\infty
 &\le\rho\max_iH_i
 =\frac{43733837512527}{195312500000000}<\frac3{10}.
\end{aligned}
\tag{4.10}
$$

令 $\mathcal T(u)=u-C_{\rm pre}\mathscr F(u)$。式 (4.9)–(4.10) 给整个盒上的

$$
\begin{aligned}
\|D\mathcal T(u)\|_\infty
 &<\frac1{10^6}+\frac1{1000}\frac3{10}
 =\frac{301}{10^6}<\frac1{1000},\\
\|\mathcal T(m)-m\|_\infty&<\frac1{10^{16}},\\
\|\mathcal T(u)-m\|_\infty
 &<\frac1{10^{16}}+\frac{\rho}{1000}
 =\frac{11}{10^{16}}<\rho.
\end{aligned}
\tag{4.11}
$$

$\mathcal K$ 是完备的闭凸盒，故 Banach 压缩映像定理给其中唯一的 $\mathcal T$ 不动点。为从不动点回到原方程，式 (4.9) 的第二行使 $C_{\rm pre}J_{\mathscr F}(m)$ 由 Neumann 级数可逆；两个因子均为方阵，故 $C_{\rm pre}$ 可逆。这个平方近似逆论证参见 Rump，《[Verified bounds for singular values, in particular for the spectral norm of a matrix and its inverse](https://www.tuhh.de/ti3/paper/rump/Ru10a.pdf)》，§2；这里所需的是式 (4.9) 的诱导无穷范数有理界。因此 $\mathcal T(u)=u$ 当且仅当 $\mathscr F(u)=0$。式 (4.11) 还使该零点的 $C_{\rm pre}J_{\mathscr F}$ 可逆，故零点非奇异且孤立。

闭盒由有理不等式定义，其中的零集恰为一个点。由实闭域的投影定理，这个单点的每个坐标投影都是在 $\mathbb Q$ 上半代数的单点，因而是实代数数。这只用标准的实代数消元性质；它不分类盒外的零点。

### 4.2. 非零分母与整个原世界的充要重建

下面的区间计算均为有理区间运算。对源多项式 $P(r,b)=\sum_{j,k}p_{jk}r^jb^k$，以

$$
\mathcal I(P)=\sum_{j,k}[p_{jk},p_{jk}]\,I_r^jI_b^k
\tag{4.12}
$$

定义展开后的自然区间值。加法按端点相加，乘法取四个端点乘积的最小、最大值；非负整数幂为重复区间乘法。第一源取 $I_r=[m_1-\rho,m_1+\rho]$、$I_b=[a,a]$，第二源取 $I_r=[m_2-\rho,m_2+\rho]$、$I_b=[m_3-\rho,m_3+\rho]$。首先用式 (4.12) 得到

$$
\mathcal I(\mathscr D(x,a))\subset
\left(-\frac{134089}{10^6},-\frac{134088}{10^6}\right)
\subset\left(-\frac15,-\frac1{10}\right),\qquad
\mathcal I(\mathscr D(y,t))\subset
\left(-\frac{16078383}{10^6},-\frac{16078382}{10^6}\right)
\subset(-17,-16).
\tag{4.13}
$$

所以两个分母在整个盒上均严格负。$a>0$、$t>0$ 也已由盒界给出。此后才对不含零的区间 $[l,u]$ 用倒数 $[1/u,1/l]$；分子分别按式 (4.12) 展开求值，再乘倒数，给下表。每格 $(L,U)$ 表示严格包含在 $(L/10^6,U/10^6)$ 中；表内表达式分别代入 $(x,a)$ 与 $(y,t)$。

| 表达式 | 第一源 | 第二源 |
| --- | --- | --- |
| $r(1-r)/b$ | $(455960,455961)$ | $(78506,78507)$ |
| $\mathscr B/\mathscr D$ | $(19485381,19485382)$ | $(28798260,28798261)$ |
| $\mathscr Q_5/(875b\mathscr D)$ | $(-6692588,-6692586)$ | $(-6692588,-6692587)$ |
| $\mathscr Q_6/(875b\mathscr D)$ | $(11815176,11815178)$ | $(11815177,11815178)$ |
| $\mathscr Q_7/(875b\mathscr D)$ | $(107058221,107058224)$ | $(107058222,107058223)$ |

在任一严格源上，先由 $b>0$ 定义 $c=r(1-r)/b>0$，于是 $j=b+c=X/b>0$、$n=r+j=N/b>0$、$T>0$，故下列分式的分母均非零。式 (4.1) 与式 (2.4) 的第四行方程之间有精确恒等式

$$
\begin{aligned}
\mathscr D&=b^2jTn\,a_4,&
\mathscr B&=b^2jTn(Y-k_4),\\
j\mathscr V_1&=A\mathscr D-\mathscr B,&
T\mathscr V_2&=C\mathscr D-\mathscr B,&
n\mathscr V_3&=z\mathscr D-\mathscr B,\\
\mathscr B+U(-\mathscr V_0+4\mathscr V_1-6\mathscr V_2+4\mathscr V_3)
 &=Y\mathscr D.
\end{aligned}
\tag{4.14}
$$

后三个乘法恒等式可乘 $b$ 清分母后逐项合并，最后一式本身是多项式恒等式。在满足 $\mathscr D\ne0$ 的严格源上，定义

$$
\begin{aligned}
\ell_0(s)&=-\frac{(s-1)(s-2)(s-3)}6,&
\ell_1(s)&=\frac{s(s-2)(s-3)}2,\\
\ell_2(s)&=-\frac{s(s-1)(s-3)}2,&
\ell_3(s)&=\frac{s(s-1)(s-2)}6,\\
d_{r,b}&=\frac{\mathscr B(r,b)}{\mathscr D(r,b)},&
g_{r,b}(s)&=\frac{\sum_{i=0}^3\mathscr V_i(r,b)\ell_i(s)}{\mathscr D(r,b)}.
\end{aligned}
\tag{4.15}
$$

插值常数 $2,6$ 均非零。式 (4.13) 已保证这两个具体源能使用式 (4.15)。更一般地，在 $\mathscr D(r,b)\ne0$ 的任一严格源上，对于定义 1.1 的整个三元组，有原行的充要关系

$$
(P(r,b),g,d)\in\mathcal F(H_4^\star)
\quad\Longleftrightarrow\quad
(d,g)=(d_{r,b},g_{r,b}).
\tag{4.16}
$$

确实，$\ell_i(k)=\delta_{ik}$ 于 $0\le i,k\le3$，故式 (4.14) 依次给实际读数 $0,A,C,z$；式 (2.3) 的时钟四权重 $(-1,4,-6,4)$ 及式 (4.14) 最后一行给实际第五行 $Y$。反向，任一实现这五行的整个次数至多三多项式，必有式 (2.2) 的四个样本，再由四节点 Lagrange 插值唯一确定。把它代入时钟四给 $a_4d=Y-k_4$。由式 (4.14)、$b^2jTn>0$ 和 $\mathscr D\ne0$，先知 $a_4\ne0$，才除出式 (4.15) 的 $d$，随后得到同一个整个 $g$。插值方法直接使用第 2.1 小节引用的 Berrut–Trefethen §2，不作为另一个新增结论。

式 (4.15) 给一个在全部原时钟不变的实多项式，次数至多三。若它恒零，原时钟零、一的读数均等于固定 $d$，与 $0\ne24$ 矛盾。因此它是整个非零增益。式 (4.16) 仅在已证非零的局部源分母上使用，不断言 $a_4$ 在整个 $\mathcal F(H_4^\star)$ 上非零；其余源层无需为此存在性结论分类或删去。整个定义域仍含增益样本零、任意符号、非采样根、重根与次数下降；这里不除以样本值、最高次系数、根差或判别式。

在零点处置 $(r_1,b_1)=(\xi,a)$、$(r_2,b_2)=(\eta,\theta)$，并取 $g_i=g_{r_i,b_i}$、$d_i=d_{r_i,b_i}$。两个源明确为

$$
P_1=\begin{pmatrix}\xi&1/5\\5\xi(1-\xi)&1-\xi\end{pmatrix},\qquad
P_2=\begin{pmatrix}\eta&\theta\\\eta(1-\eta)/\theta&1-\eta\end{pmatrix}.
\tag{4.17}
$$

两源各项严格正、迹为一、行列式为零，故秩恰为一。$\xi>89/100$ 而 $\eta<2/25$ 使它们不同。表中的漂移界还给 $19<d_1<20$、$28<d_2<29$。这证明式 (4.6) 的完整合法性与不同性。

### 4.3. 三个方程与原始八行的精确对应

沿定义 1.2 表中的实际左乘积，原时钟五、六、七的正迹分别为
$1+r+3b+c$、$1+2r+2b+c$、$2+5b+c$，恰为 $R_5/b,R_6/b,R_7/b$。这些乘积依次是
$Q_5=M Q_4$、$Q_6=JQ_5$、$Q_7=M Q_6$，故没有交换动作或重编号。把同一个式 (4.15) 代入式 (1.2)，式 (2.3) 的三行插值权重给实际响应

$$
q_i(r,b)=\frac{\mathscr Q_i(r,b)}{875b\mathscr D(r,b)},\qquad i=5,6,7,
\qquad
(p_0,h_0,f_0)=\bigl(q_5(\xi,a),q_6(\xi,a),q_7(\xi,a)\bigr).
\tag{4.18}
$$

在盒上 $875ab_2\mathscr D(x,a)\mathscr D(y,t)\ne0$，其中 $b_2=t$。因此式 (4.3) 不仅是共同响应的必要条件，而有逐行恒等式及充要关系

$$
\begin{aligned}
q_i(x,a)-q_i(y,t)
 &=\frac{\mathscr F_i(x,y,t)}
 {875at\mathscr D(x,a)\mathscr D(y,t)},\qquad i=5,6,7,\\
\mathscr F(x,y,t)=0
 &\quad\Longleftrightarrow\quad
(q_5,q_6,q_7)(x,a)=(q_5,q_6,q_7)(y,t).
\end{aligned}
\tag{4.19}
$$

在 $(\xi,\eta,\theta)$ 处三个多项式为零，所以三个末响应完全相等；相等性来自式 (4.19)，并非区间交叠。式 (4.16) 已给共同的前五行，故得到式 (4.7) 的全部八行。式 (4.18) 连同有理方程和隔离盒就是三个代数响应的精确定义。表中的整个盒界给所需的三个开区间，完成证明。∎

**推论 4.3（自由第五响应的固定续行障碍与共享历史边界）。** 对 $W\in\mathcal F(H_4^\star)$，令 $p(W)$ 是第五 $M$ 的实际响应，$h(W)$、$m(W)$ 是随后第六 $J$、最终 $M$ 的实际响应。映射

$$
\Psi:\mathcal F(H_4^\star)\longrightarrow\mathbb R^3,
\qquad W\longmapsto\bigl(p(W),h(W),m(W)\bigr)
\tag{4.20}
$$

不是单射。令

$$
\begin{aligned}
H_5^0&=(H_4^\star,M,p_0),&H_6^0&=(H_5^0,J,h_0),\\
S_0&=\mathcal F(H_6^0),&
\Lambda_0&=\mathcal F(H_6^0,M,f_0).
\end{aligned}
\tag{4.21}
$$

则最终 $M$ 在整个已获切片 $S_0$ 上不是单射，且 $\Lambda_0$ 至少含两个不同完整世界，满足定义 1.3 的 $L_0$。定理 2.1 与推论 3.1 在 $H_5^\star$ 上的结论仍成立。

证明。定理 4.2 的两个世界属于 $\Lambda_0\subseteq S_0\subseteq\mathcal F(H_5^0)$，其式 (4.20) 响应相等，而完整目标不同。这同时证明三项非单射、非单点叶及其停止守卫。又 $p_\star=-9596/525<-7$，而 $p_0\in(-7,-6)$，所以 $H_5^0\ne H_5^\star$；定理 2.1 的量词域是固定的 $\mathcal F(H_5^\star)$。其两图包含、分支符号与单射结论没有被用于式 (4.20) 的自由 $p$ 域。

这正好排除在整个 $\mathcal F(H_4^\star)$ 上统一采用第五 $M$、第六 $J$、最终 $M$ 的完整识别续行。要在同一已获响应 $p_0,h_0$ 上取得 $L_1(S_0,H_6^0)$，式 (1.6) 还要求最终 $J$ 有一个非单点叶；那个叶可用另一对世界，但它们也必须属于同一个 $S_0$，不能把另一第六响应下的对接入。要进一步在 $H_5^0$ 取得 $L_2$，还须在同一个 $p_0$ 下，为第六 $M$ 找一个共同响应 $v_M$，使其已获切片同时有最终 $J$ 和最终 $M$ 的非单点叶。它们各自的父节点也必须满足非单点停止守卫。定理 4.2 只给式 (4.21) 这一最终 $M$ 叶，不给这些其余存在量词的见证。

因此仍待决定：同一第四父的第五 $M$ 臂是否有一个实际响应支持完整的 $L_2$，以及是否反而该臂的每个第五响应都有某个第六动作，使每个已获切片可由一个适当的最终动作单射识别；该最终动作允许依赖已经取得的响应。第五 $J$ 臂、其他父、全部祖先与原根 $L_7$ 仍保留定义 1.3 的量词和共同实现条件。单个固定续行的失败不结算原八读策略的存在或不可能性、八与九的极小极大比较或九读上界。

本节的具体相容世界与同历史碰撞是由上述原方程得出的仓内数学内容；Lagrange 插值、Banach 压缩映像、Neumann 级数与实半代数投影仅为证明中的既有工具，不另立同名新定理，也不据此作任何文献原创性主张。∎

## 追加锚（本行以下为增补区）

## 5. 闭响应窗口内的整个第六子纤维与最终 J 恢复

**定义 5.1（响应窗口、兼容多项式与两个源矩形）。** 保持定义 1.1 的完整原域、定义 1.2 的 $H_4^\star$ 和定义 4.1 的原源多项式。取闭窗口

$$
I_p=\left[-\frac{6692588}{10^6},-\frac{6692586}{10^6}\right],\qquad
I_h=\left[\frac{11815176}{10^6},\frac{11815178}{10^6}\right],\qquad
K(p,h)=\mathcal F(H_4^\star,M,p,J,h).
\tag{5.1}
$$

这里的 $K(p,h)$ 包含全部实现该字面历史的合法完整世界，既不限定为第 4 节的两个世界，也不限定源在其隔离盒内。对式 (4.1)–(4.2) 的量定义

$$
\begin{aligned}
\mathscr N_i&=\mathscr Q_i/875=b\mathscr B+R_i\mathscr G_i,
 &&i=5,6,7,\\
\mathscr N_J&=b\mathscr B+R_5\mathscr G_7,\\
f_5(r,b;p)&=-\frac{875}{2}
  \bigl(\mathscr N_5-pb\mathscr D\bigr),\\
f_6(r,b;h)&=-\frac{875}{2}
  \bigl(\mathscr N_6-hb\mathscr D\bigr).
\end{aligned}
\tag{5.2}
$$

$\mathscr N_i$ 是多项式分子，不是式 (4.18) 的响应 $q_i$。两个 $f_i$ 分别属于 $\mathbb Z[r,b,p]$、$\mathbb Z[r,b,h]$，在源变量中的总次数为七、坐标次数为 $(6,7)$，对响应参数仿射。

采用区别于第 2 节分界的两张图

$$
\begin{aligned}
r_{\mathrm A}(b,x)&=bx,&r_{\mathrm B}(b,x)&=1-bx,\\
c_{\mathrm A}(b,x)&=c_{\mathrm B}(b,x)=x(1-bx),\\
D_{\rm chart}&=\{(b,x):0\le b\le2,\ 0\le x\le4,\ bx\le1/2\},\\
R_{\mathrm A}&=[459/500,461/500]\times[83/1000,11/125],\\
R_{\mathrm B}&=[99/500,101/500]\times[1/2,13/25].
\end{aligned}
\tag{5.3}
$$

全部矩形的坐标次序均为 $(b,x)$。以下各商是多项式环中的精确整除，因而在 $b=0$ 也定义：

$$
\begin{aligned}
P_{5\nu}(b,x;p)&=f_5(r_\nu(b,x),b;p)/b^3,\\
P_{6\nu}(b,x;h)&=f_6(r_\nu(b,x),b;h)/b^3,\\
\delta_\nu(b,x)&=\mathscr D(r_\nu(b,x),b)/b^2,\\
n_{J\nu}(b,x)&=\mathscr N_J(r_\nu(b,x),b)/b^3,
\qquad \nu\in\{\mathrm A,\mathrm B\}.
\end{aligned}
\tag{5.4}
$$

两个 $P_{i\nu}$ 在 $(b,x)$ 中的坐标次数均为 $(4,6)$；$\delta_\nu$ 与 $n_{J\nu}$ 的坐标次数分别为 $(4,4)$、$(4,6)$。这些定义不以分母非零为前提。

**定理 5.2（整个响应窗口的至多二世界及实际最终 J 单射）。** 对每个固定的 $(p,h)\in I_p\times I_h$，整个 $K(p,h)$ 至多含两个完整世界。每个兼容源必在式 (5.3) 的 $R_{\mathrm A}$ 或 $R_{\mathrm B}$ 中，每个矩形至多给一个源，每个源至多给一个完整世界。原时钟七的实际最终 $J$ 响应

$$
j_7(W)=d+g(7)\operatorname{tr}(JQ_6P)
      =d+g(7)(1+r+3b+c)
\tag{5.5}
$$

在整个 $K(p,h)$ 上单射。A 图世界的响应属于 $(71,79)$，B 图世界的响应属于 $(89,104)$。这里的统一至多二结论不声称每个 $(p,h)$ 都有两个世界，空纤维与单点纤维亦包括在内。

证明。先保留分母零层取得全域必要方程，再作全域排除，最后建立充要重建及响应单射。

### 5.1. 不删除分母零层的原世界必要条件

任一 $W\in K(p,h)$ 都有严格源。式 (1.4) 的 $j,T,n$ 均严格正，所以式 (2.2) 和同一个整个次数至多三的增益的式 (2.3) 插值有效。原时钟四给式 (2.4) 的 $a_4d=Y-k_4$；乘上正的 $b^2jTn$，用式 (4.14) 得

$$
\mathscr Dd=\mathscr B,\qquad
\mathscr V_i=\mathscr Dg(i)\quad(0\le i\le3),\qquad
\mathscr G_k=\mathscr Dg(k)\quad(k=5,6,7).
\tag{5.6}
$$

第二式对 $i=0$ 由 $g(0)=-d$ 得到，对 $i=1,2,3$ 分别将式 (4.14) 的三个乘法恒等式与原读数相减，再仅除以正的 $j,T,n$；第三式由式 (2.3) 的固定权重得到。因而这些式子即使在 $\mathscr D=0$ 时仍然成立。原时钟五、六的迹分别为 $R_5/b,R_6/b$，故

$$
\mathscr N_5=pb\mathscr D,\qquad
\mathscr N_6=hb\mathscr D,
\qquad f_5=f_6=0.
\tag{5.7}
$$

至此未除以 $\mathscr D$、$a_4$ 或任何增益样本，也未除以最高次系数、根差或判别式。因此式 (5.7) 是每一个原世界的必要条件，而不只是预先选定的非退化支的条件。

### 5.2. 当前响应范围上的无界源排除

本节所需界由式 (5.2) 重新给出，不使用 $p_\star$ 纤维的式 (2.9)。在较大的 $p\in[-7,-6]$ 上，展开

$$
f_5(r,2+t;-7+v)=\sum_{k=0}^7 a_k(r,v)t^k.
\tag{5.8}
$$

依式 (2.6) 对各 $a_k$ 使用其自身坐标次数，在 $(r,v)\in[0,1]^2$ 上的张量 Bernstein 系数范围如下：

| $k$ | 最小系数 | 最大系数 |
| --- | --- | --- |
| 0 | $14495440$ | $28050480$ |
| 1 | $50579792$ | $97164736$ |
| 2 | $74049576$ | $139187192$ |
| 3 | $59404148$ | $107182400$ |
| 4 | $28306716$ | $47728875$ |
| 5 | $8037462$ | $12202140$ |
| 6 | $1262685$ | $1634428$ |
| 7 | $84871$ | $85746$ |

全体系数严格正，故式 (2.7) 给 $b\ge2$ 时 $f_5>0$。另一方面，精确多项式商

$$
C_*(r,u,v)=
\frac{f_5(r,r(1-r)u/2;-7+v)}{r^3(1-r)^3}
\tag{5.9}
$$

在 $(r,u,v)$ 中的坐标次数为 $(8,7,1)$，其在 $[0,1]^3$ 上的全部 $144$ 个张量 Bernstein 系数的最小值为 $224867/4$、最大值为 $598983/4$。三变量转换是式 (2.6) 的三个二项式比值相乘；式 (2.7) 的证明逐坐标相乘即适用。若严格源有 $c\ge2$，取 $u=2/c\in(0,1]$，则 $b=r(1-r)u/2$，而正的 $r^3(1-r)^3$ 又给 $f_5>0$。因此每个式 (5.7) 的严格源必有

$$
0<b<2,\qquad0<c<2.
\tag{5.10}
$$

当 $r\le1/2$，用 A 图的 $x=r/b=c/(1-r)<4$；当 $r\ge1/2$，用 B 图的 $x=(1-r)/b=c/r<4$。两种情形都有 $bx\le1/2$。故每个原世界的源落在至少一个 $D_{\rm chart}$ 中，且式 (5.7) 等价于其图上的 $P_{5\nu}=P_{6\nu}=0$。这里仅因严格源 $b>0$ 才除去 $b^3$；随后覆盖仍包括其闭延拓 $b=0$。

### 5.3. 两张闭图域的完整排除树

复用式 (2.6)–(2.7)、(2.22) 的标准 Bernstein 转换与中点 de Casteljau 细分。为了直接从原幂系数复算，若 $P(b,x)=\sum a_{ef}b^ex^f$ 的坐标次数为 $(n,m)$，则在 $R=[l,u]\times[q,v]$ 上

$$
\begin{aligned}
M_{i,e}(l,u;n)
 &=\sum_{k=0}^{\min(i,e)}
 \binom ek\frac{\binom ik}{\binom nk}l^{e-k}(u-l)^k,\\
\mathcal B^R_{ij}(P)
 &=\sum_{e,f}a_{ef}M_{i,e}(l,u;n)M_{j,f}(q,v;m).
\end{aligned}
\tag{5.11}
$$

零次坐标仍只有下标零，零次幂取一。式 (5.11) 由二项式仿射展开再用式 (2.6) 得到；不需要零点近似或任何外部系数表。

每张图的根矩形取 $[0,2]\times[0,4]$，根深度为零。字符 $X$ 在偶深度平分 $b$、奇深度平分 $x$，均取精确中点，随后依次读完整左、右子树。取 $k_{\mathrm A}=3$、$k_{\mathrm B}=18/5$。闭叶的条件是：

| 字符 | 闭叶 $R=[b_0,b_1]\times[x_0,x_1]$ 上的条件 |
| --- | --- |
| $0$ | $P_{5\nu}$ 在 $p$ 的两个端点的全部 $\mathcal B^R$ 系数合在一起严格正或合在一起严格负 |
| $1$ | $P_{6\nu}$ 在 $h$ 的两个端点的全部 $\mathcal B^R$ 系数合在一起严格正或合在一起严格负 |
| $2$ | $P_{6\nu}-k_\nu P_{5\nu}$ 在 $(p,h)$ 的四个角点的全部 $\mathcal B^R$ 系数合在一起严格正或合在一起严格负 |
| $O$ | $b_0x_0>1/2$ |
| $C$ | $R\subseteq R_\nu$ |

每个下列字符串恰消耗一棵完整树；没有省略字符，也没有其余叶型。

图 A：

```text
XXXXX20X2XX20X2OXX0XXX22XXXX2XX0X0X02XXX0X0X2XXX0X0X0C2XXX2XC000X2XX200X202XXXXXX022202002X0OXXX0XXXX0OOOOXXX0X0X0OX0XX0OX0OOOXXX0OX0OO
```

图 B：

```text
XXXXXXXX0XX0XX02X02X0XX02X0XXX2X020XXX02X020X0XX0XX0XXXX0202X02X0XX0X2X02X0XX02X02X0XX0XX0XX02000X0XX0XXXXXXXX2X200XXX20XXC0XC200XXXXX0222X0200XXXXX02X0X202X02000X0XXXXXXXX0XX0210X2XX2X020X0XX12X0XX0202X0XXXXXX0202021X0XX0XX20220X0XXX2X0X2X0XX20X2O0XXX0XX2OOX2OOXX0X2X2X0OX0OXXXX0X0X0X0OXXXXXX0OOOOOOXXX0XX0OX0OX0XX0OX0OOOXXX0OX0OO
```

式 (5.11) 给出的全部严格系数不等式及叶包含关系为：

| 图 | 字符数 | $X$ | $0$ | $1$ | $2$ | $O$ | $C$ | 最大深度 | 严格符号系数不等式数 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A | 135 | 67 | 32 | 0 | 20 | 14 | 2 | 22 | 5040 |
| B | 331 | 165 | 90 | 3 | 48 | 23 | 2 | 19 | 13230 |

其中 A 的两个 $C$ 叶分别为

$$
[941/1024,471/512]\times[43/512,11/128],\qquad
[941/1024,471/512]\times[11/128,45/512],
\tag{5.12}
$$

B 的两个 $C$ 叶分别为

$$
[51/256,103/512]\times[1/2,65/128],\qquad
[51/256,103/512]\times[65/128,33/64].
\tag{5.13}
$$

这些闭叶分别包含于 $R_{\mathrm A}$、$R_{\mathrm B}$。表中 $18270$ 个严格系数不等式由式 (4.1)–(4.2)、(5.2)–(5.4)、(5.11) 与上述字面树唯一确定：每个 $0$ 或 $1$ 叶检查两个端点的各 $35$ 个系数，每个 $2$ 叶检查四角的各 $35$ 个系数；全部 $37$ 个 $O$ 叶检查其严格乘积不等式。逐层使用第 2.4 小节的中点均值细分给相同系数。

每次二分的两个闭子矩形之并恰为父矩形，故完整树覆盖整个闭根矩形，包括所有叶边界。$O$ 叶不交 $D_{\rm chart}$；其余符号叶由式 (2.7) 排除共同零点。响应参数仿射，所以端点或四角的同一严格系数符号覆盖整个闭响应窗口。因此每个兼容源必落在式 (5.12) 或 (5.13) 的保留叶，进而落在相应的 $R_\nu$。这同时排除了原隔离盒以外的全部严格源，而不只是某个种子族。

### 5.4. 局部唯一性、分母符号与实际最终响应

令 $F_\nu=(P_{5\nu},P_{6\nu})^{\mathsf T}$，取有理矩阵

$$
C_{\mathrm A}=\frac1{10^9}
 \begin{pmatrix}14151&-4603\\-24812&8877\end{pmatrix},\qquad
C_{\mathrm B}=\frac1{10^9}
 \begin{pmatrix}341431&-95782\\256543&-70000\end{pmatrix},\qquad
M_\nu=I-C_\nu D_{(b,x)}F_\nu.
\tag{5.14}
$$

对每一项 $(M_\nu)_{ij}$，在响应窗口四角用式 (5.11) 计算其在 $R_\nu$ 上的全部系数，取其中最大绝对值 $e_{ij}$。每行的 $e_{i1}+e_{i2}$ 精确为下表；参数仿射与系数凸包使它们给整个 $R_\nu\times I_p\times I_h$ 的绝对行和上界。

| 图、行 | 精确行上界 | 严格较简上界 |
| --- | --- | --- |
| A，1 | $71351751694474689435678992304483/1250000000000000000000000000000000$ | $3/50$ |
| A，2 | $104370834580611560172840798778981/1250000000000000000000000000000000$ | $9/100$ |
| B，1 | $177327651671476966605853/250000000000000000000000$ | $71/100$ |
| B，2 | $242546488204122941305121/500000000000000000000000$ | $49/100$ |

固定 $p,h$。若同一闭凸矩形内 $u,v$ 都为 $F_\nu$ 的零点，则均为 $T_\nu(w)=w-C_\nu F_\nu(w)$ 的不动点。沿连接它们的线段积分导数，得

$$
\|u-v\|_\infty
=\|T_\nu(u)-T_\nu(v)\|_\infty
\le q_\nu\|u-v\|_\infty,\qquad
q_{\mathrm A}=9/100<1,\quad q_{\mathrm B}=71/100<1.
\tag{5.15}
$$

故 $u=v$。此处只用标准导数压缩的线段论证，不要求 $T_\nu$ 将矩形映入自身，也不据此推断零点存在。

对 $\delta_\nu,n_{J\nu}$ 用同一式 (5.11)，其精确系数凸包的端点为：

| 图 | $\delta_\nu$ 的系数凸包 | $n_{J\nu}$ 的系数凸包 |
| --- | --- | --- |
| A | $[-596520146414055502368439/31250000000000000000000,-36122871286469788581/1907348632812500000]$ | $[-38630148696085865978111293/26077032089233398437500,-10729379714311235790780089886403/7812500000000000000000000000]$ |
| B | $[-1718000828797/500000000000,-9833023240326541/3051757812500000]$ | $[-138558673158342009928/417232513427734375,-26804249049432221/87500000000000]$ |

分别以不含零的分母区间作区间除法，得到

$$
\begin{array}{c|cc}
\nu&\delta_\nu(R_\nu)&(n_{J\nu}/\delta_\nu)(R_\nu)\\ \hline
\mathrm A&(-20,-18)&(71,79)\\
\mathrm B&(-7/2,-3)&(89,104).
\end{array}
\tag{5.16}
$$

例如两个响应商的闭区间凸包依次为

$$
\begin{aligned}
&\left[
\frac{10729379714311235790780089886403}{149130036603513875592109750000},
\frac{309041189568686927824890344}{3950939046957633126046875}
\right]\subset(71,79),\\
&\left[
\frac{26804249049432221}{300650145039475},
\frac{4433877541066944317696}{43019476676428616875}
\right]\subset(89,104).
\end{aligned}
\tag{5.17}
$$

所有兼容源已由全域覆盖进入这两个矩形，而严格源有 $b>0$，故此时才得到整个实际切片上的 $\mathscr D=b^2\delta_\nu<0$。于是式 (4.15) 定义同一个固定漂移与同一个整个增益，且式 (4.16)、(5.7) 给精确的充要重建：

$$
\begin{aligned}
W\in K(p,h)
\quad\Longleftrightarrow\quad&
\text{$W$ 的严格源在某个 $R_\nu$，且 }P_{5\nu}=P_{6\nu}=0,\\
&d=\mathscr B/\mathscr D,\qquad
g(s)=\sum_{i=0}^3\mathscr V_i\ell_i(s)/\mathscr D.
\end{aligned}
\tag{5.18}
$$

右向已由必要条件与全域覆盖证明。左向由式 (4.14) 和插值给原时钟零至四，再由式 (5.2) 的两个零方程给五、六；初两读 $0,24$ 排除恒零增益。矩形上均有 $b,x>0$、$bx<1/2$，所以两图确实给合法的严格正、迹一秩一源。每个源只有式 (5.18) 的一个完整增益与漂移，样本零、重根、非采样根、任意符号与次数下降均未删除。

式 (5.15) 给每个矩形至多一个源，式 (5.18) 给每个源至多一个完整世界，故整个 $K(p,h)$ 至多二元。矩阵乘法给 $JQ_6=Q_5$，但最终响应仍使用原时钟七的 $g(7)$；由式 (5.2)、(5.4) 得

$$
j_7(W)=\frac{\mathscr N_J}{b\mathscr D}
       =\frac{n_{J\nu}}{\delta_\nu}.
\tag{5.19}
$$

同一矩形至多一个世界，跨矩形则式 (5.16) 的响应区间不交，所以实际最终 $J$ 在整个切片上单射。这完成定理 5.2。∎

**推论 5.3（精确已获碰撞子纤维的穷尽及失败阶数）。** 取定理 4.2 的根、式 (4.18) 的精确 $p_0,h_0,f_0$ 与式 (4.21) 的 $H_6^0$。则

$$
K_0:=K(p_0,h_0)=S_0=\{W_1,W_2\},\qquad
j_7(W_2)\in(71,79),\quad j_7(W_1)\in(89,104).
\tag{5.20}
$$

实际最终 $M$ 仍在 $f_0$ 碰撞，且

$$
\Lambda_0=\mathcal F(H_6^0,M,f_0)=\{W_1,W_2\},\qquad
L_0(\Lambda_0,(H_6^0,M,f_0)),\qquad
\forall K\subseteq K_0:\ \neg L_1(K,H_6^0).
\tag{5.21}
$$

证明。对式 (4.4) 的第一根坐标区间 $[m_1-\rho,m_1+\rho]$，先把 $\mathscr N_5(r,a)$、$\mathscr N_6(r,a)$、$a\mathscr D(r,a)$ 展开为一元多项式，再用式 (4.12) 的自然区间规则求值。分母区间严格负；取倒数后相乘，给精确有理外包围

$$
\begin{aligned}
p_0&\in\left[
-\frac{6692587197153}{10^{12}},
-\frac{6692586896521}{10^{12}}\right]\subset\operatorname{int}I_p,\\
h_0&\in\left[
\frac{2953794293849}{250000000000},
\frac{11815177289453}{10^{12}}\right]\subset\operatorname{int}I_h.
\end{aligned}
\tag{5.22}
$$

这些是式 (4.18) 的根定义响应的包围，未用区间端点替换真实响应。相同根盒的有理端点运算还给

$$
\begin{aligned}
\theta&\in\left[\frac{183941178757}{200000000000},
                    \frac{229926473447}{250000000000}\right],\\
\eta/\theta&\in\left[\frac{85179371703}{10^{12}},
                    \frac{42589685853}{500000000000}\right],\\
5(1-\xi)&\in\left[\frac{6343313523}{12500000000},
                    \frac{507465081851}{10^{12}}\right].
\end{aligned}
\tag{5.23}
$$

因此 $W_2$ 的 A 图坐标 $(\theta,\eta/\theta)$ 严格在 $R_{\mathrm A}$ 内，$W_1$ 的 B 图坐标 $(1/5,5(1-\xi))$ 严格在 $R_{\mathrm B}$ 内。定理 4.2 与式 (4.16)–(4.19) 已给这两个不同合法世界实现 $H_6^0$，且共享最终 $M$ 的 $f_0$。式 (5.22) 允许应用定理 5.2：全域排除不容许矩形外的其他源，局部唯一性不容许任一矩形内的第二源，式 (5.18) 不容许同源的其他完整增益或漂移。这证明整个 $K_0$ 的式 (5.20) 穷尽，响应界由式 (5.16) 得到。

由于两世界仍有同一最终 $M$ 响应，$\Lambda_0=K_0$ 且其 $L_0$ 停止守卫成立。另一方面，对每个 $K\subseteq K_0$ 和每个实数 $u$，最终 $J$ 单射给

$$
\left|K\cap\mathcal F(H_6^0,J,u)\right|\le1.
\tag{5.24}
$$

故没有最终 $J$ 的 $L_0$ 叶；空集或单点子集本身也不满足非单点守卫。按式 (1.6)，每个这样的 $K$ 都不满足 $L_1$。这是同一个已经取得的 $p_0,h_0$ 子节点的结论，并非将另一第六响应处的世界对事后接入此节点。∎

**命题 5.4（局部恢复的共同历史边界）。** 定理 5.2、推论 5.3 不给 $\mathcal F(H_4^\star,M,p_0)$ 的 $\neg L_2$，也不给该第五 $M$ 臂的完整 $L_2$ 见证。若在这个 $p_0$ 构造 $L_2$，其第六 $J$ 分句所用的共同响应必须在 $I_h$ 外；第六 $M$ 分句及其他原递归义务仍须各自满足。

证明。对于任意 $h\in I_h$，定理 5.2 的整个最终 $J$ 单射都按式 (5.24) 排除该子节点及其子集的 $L_1$。但式 (1.6) 的 $L_2$ 在第六 $J$ 分句中允许选择其他实际响应，窗口外的第六响应未被本节分类。因此不能从 $K_0$ 的 $\neg L_1$ 推出其第五父的 $\neg L_2$。同一个 $p_0$ 的第六 $M$ 分句还需要某个共同响应 $v_M$，使其同一实际子节点内最终 $J,M$ 各有非单点叶；第六 $J$ 分句在所选的同一窗口外响应处也需要两个最终动作的非单点叶。两动作的碰撞对允许不同，但不能改变已获历史。

若改选第五响应，两条第六分句必须共同使用那个同一第五响应。第五 $J$ 臂、其他第四父与更早祖先、原根 $L_7$、所有节点的非单点停止守卫、任意不受正则性限制的自适应八读与九读比较，以及九读充分性，均仍是定义 1.3 的未决义务；本节不增加连续、可测、可计算或有限描述的策略限制。第 2–3 节的 $p_\star$ 结论保持其原域，不向当前自由响应外推。

实际自校准的局部结论是：一个固定终端动作的碰撞，在完全相同的已获历史上换用另一个允许终端动作时，可以不再存在。这里最终 $M$ 在 $K_0$ 上碰撞，而最终 $J$ 识别整个 $K_0$；所选择的最后动作可依据已经取得的 $p_0,h_0$。这比较同一固定完整世界的两个候选响应函数，不声称同时获取两种末读，也不作事后分支拼接。

本节的承重内容是当前响应窗口的整个原域排除、二世界分类与同历史恢复后果。插值直接使用第 2.1 小节所引 Berrut–Trefethen §2，Bernstein 凸包与中点细分使用第 2.2、2.4 小节的恒等式，导数压缩使用第 4.1 小节相同的标准范数工具；这些既有方法不作为新增定理。∎

## 追加锚（本行以下为增补区）

## 6. 自由父上联合实现的原世界接口

本节及第 7–9 节保持定义 1.1、1.3 的全部原域，而将 $C,z,Y$ 作为自由父读数。第 7 节给一个三世界交叠对实现，并证明在其自身精确历史下，所有完整纤维子集中的最小 $L_2$ 支撑为三。第 8 节在另一个父上给四世界实现，两支源差均非奇异，并有局部 $C^1$ 二参数实现族。这两个父互不相同，均不是定义 1.2 的 $H_4^\star$；第 2–5 节的源界、穷尽及恢复结论不向它们外推。

**定义 6.1（共用动作表与完整世界逆）。** 记

$$
H_4(C,z,Y)=(0,J,24,M,C,J,z,M,Y),\qquad
H_5(C,z,Y,p)=(H_4(C,z,Y),M,p).
\tag{6.1}
$$

这里 $H_5$ 已实际读取原时钟 $0,\ldots,5$ 的六行。下表（表 6.1）中的词按时间从左到右排列，矩阵仍按式 (1.2) 左乘；$c=r(1-r)/b$。互择续行不是额外观测。

| 标签 | 原时钟 | 时间词 | 实际左乘积 $Q$ | $\operatorname{tr}(QP)$ |
| --- | --- | --- | --- | --- |
| $0$ | $0$ | 空词 | $I$ | $1$ |
| $1$ | $1$ | $J$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $b+c$ |
| $2$ | $2$ | $JM$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $1+b$ |
| $3$ | $3$ | $JMJ$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $r+b+c$ |
| $4$ | $4$ | $JMJM$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $1+2b$ |
| $5$ | $5$ | $JMJMM$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $1+r+3b+c$ |
| $6J$ | $6$ | $JMJMMJ$ | $\left(\begin{smallmatrix}3&1\\2&1\end{smallmatrix}\right)$ | $1+2r+2b+c$ |
| $7JJ$ | $7$ | $JMJMMJJ$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $1+r+3b+c$ |
| $7JM$ | $7$ | $JMJMMJM$ | $\left(\begin{smallmatrix}2&1\\5&2\end{smallmatrix}\right)$ | $2+5b+c$ |
| $6M$ | $6$ | $JMJMMM$ | $\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$ | $2+r+5b+c$ |
| $7MJ$ | $7$ | $JMJMMMJ$ | $\left(\begin{smallmatrix}5&2\\3&1\end{smallmatrix}\right)$ | $1+4r+3b+2c$ |
| $7MM$ | $7$ | $JMJMMMM$ | $\left(\begin{smallmatrix}5&2\\8&3\end{smallmatrix}\right)$ | $3+2r+8b+2c$ |

在全严格源域 $\Omega=\{(r,b):0<r<1,b>0\}$ 上，置

$$
\begin{gathered}
j=b+c,\quad n=r+j,\quad T=1+b,\quad U=1+2b,\quad V=n+U,\\
a_4=1+U(1-4/j+6/T-4/n),\qquad
k_4=U(96/j-6C/T+4z/n),\\
a_5=1+V(4-15/j+20/T-10/n),\qquad
k_5=V(360/j-20C/T+10z/n),\\
B_4=Y-k_4,\quad B_5=p-k_5,\quad S=a_4^2+a_5^2,\qquad
\Gamma(C,z,Y,p)=\{(r,b)\in\Omega:a_5B_4-a_4B_5=0\}.
\end{gathered}
\tag{6.2}
$$

沿用前卷定理 9.2、10.2 的全严格源结论，$S>0$。对每个 $x\in\Gamma$，定义

$$
\begin{gathered}
d_x=\frac{a_4B_4+a_5B_5}{S},\qquad
(q_0,q_1,q_2,q_3)=\left(-d_x,\frac{24-d_x}{j},
\frac{C-d_x}{T},\frac{z-d_x}{n}\right),\\
\ell_0(s)=-\frac{(s-1)(s-2)(s-3)}6,\quad
\ell_1(s)=\frac{s(s-2)(s-3)}2,\\
\ell_2(s)=-\frac{s(s-1)(s-3)}2,\quad
\ell_3(s)=\frac{s(s-1)(s-2)}6,\qquad
g_x(s)=\sum_{i=0}^3q_i\ell_i(s).
\end{gathered}
\tag{6.3}
$$

这些是既有完整逆的参数接口，不计作新增分类。其双向性也可直接从下列余项核对。若 $R=a_5B_4-a_4B_5$，则

$$
a_4d_x-B_4=-a_5R/S,\qquad a_5d_x-B_5=a_4R/S.
\tag{6.4}
$$

四节点插值给前四行，式 (6.4) 给第四及第五动作行。反之，任意兼容完整世界的前四行迫出式 (6.3) 的四个样本，次数至多三迫出同一个整个多项式；另两行就是 $a_4d=B_4,a_5d=B_5$，遂 $x\in\Gamma$，且漂移必为 $d_x$。取源坐标与此重建互逆。因此式 (6.2)–(6.3) 保留整个 $\mathcal F(H_5)$，包括下文局部图分母 $D=0$ 的所有层。$j,T,n,S$ 均严格正；没有除以增益样本、首项系数、根差或判别式。初读 $0$ 与第一动作读数 $24$ 排除恒零增益。

为明确全源非退化依据，前卷式 (9.7)–(9.14) 使用 $X=bj,N=bn,L=jTn$，其 $N_4=b^2La_4,N_{5,M}=b^3La_5$ 满足

$$
\operatorname{Res}_r(N_4,N_{5,M})=256b^{14}(1+b)^4(1+2b)^2P_M(b).
\tag{6.5}
$$

$P_M$ 的全部十七个系数见前卷式 (9.12)。在 $0<b<4$，最高三项为 $b^{14}(27b^2+198b-24294)$，括号不大于 $-23070$，其余各项严格负；在 $b\ge4$，$j,n>b$ 给 $a_4>1+U(b^2-b-8)/(b(1+b))>0$。故全严格源不存在 $a_4=a_5=0$，不是只在见证盒内假定 $S>0$。

**定义 6.2（有限有理计算的读法）。** 以下所有数组均是精确整数或有理数数据，十进制仅在带明确分母时出现。若 $P(x)=\sum_\alpha c_\alpha x^\alpha$，其中心值与一阶导数按有限和

$$
P(m)=\sum_\alpha c_\alpha\prod_jm_j^{\alpha_j},\qquad
\partial_jP(m)=\sum_{\alpha_j>0}c_\alpha\alpha_j
m_j^{\alpha_j-1}\prod_{h\ne j}m_h^{\alpha_h}
\tag{6.6}
$$

求值。若 $m_j=0$，直接按导数单项式求值，绝不将式 (6.6) 改成除以 $m_j$。向量无穷范数是最大绝对坐标，矩阵诱导无穷范数是最大绝对行和；所有界均可由整数交叉相乘比较。也可用一阶 jet：常数为 $(c,0)$，变量为 $(m_j,e_j)$，乘法为 $(v,d)(w,e)=(vw,wd+ve)$；这给同样的精确导数。

对有理区间，和、负号按端点计算，乘积取四个端点乘积的最小与最大值；仅在 $0\notin[a,b]$ 时使用 $[a,b]^{-1}=[1/b,1/a]$。第 7 节指定展开多项式的系数包含法，第 8 节指定所写因式表达式的端点包含法，两者不混淆。证书中的区间只描述精确根定义的量；共享响应的等式由零多项式方程证明，不由区间重叠证明。

## 7. 同一第五 M 历史的最小三世界交叠实现

**定义 7.1（直线核与第三源方程）。** 本节变量次序固定为 $x=(k,\theta,\psi,r,b)$。使用前卷定义 19.1 的整数多项式

$$
f(k)=2104+1520k-14654k^2+1108k^3+27037k^4
-8977k^5-13559k^6+6408k^7.
\tag{7.1}
$$

以下数组逐字给出 $u_0,u_1,u_2,u_3,v_0,v_1,v_2,v_3$ 的 $k$ 升幂系数，缺省高次系数为零。它们复用前卷式 (19.3) 的核，不复用前卷矩形 (19.5) 的任何界。

```json
[
  [
    12624,
    12528,
    -61716,
    -53004,
    100062,
    63696,
    -70146,
    -23340,
    18918
  ],
  [
    -1664,
    -232,
    8240,
    14792,
    -21500,
    -27295,
    24225,
    12935,
    -9060
  ],
  [
    1248,
    -4560,
    -3240,
    13509,
    1578,
    -14739,
    2238,
    5361,
    -1962
  ],
  [
    -208,
    760,
    484,
    -2699,
    212,
    3400,
    -1089,
    -1370,
    636
  ],
  [
    12624,
    1632,
    -45312,
    20400,
    50046,
    -33378,
    -18486,
    12600
  ],
  [
    -1664,
    -6976,
    -14310,
    11770,
    35638,
    -15028,
    -18364,
    8640
  ],
  [
    1248,
    1200,
    2748,
    -1731,
    -9432,
    3498,
    5241,
    -2394
  ],
  [
    -208,
    16,
    114,
    -253,
    344,
    94,
    -263,
    72
  ]
]
```

置 $U_k(s)=\sum_{a=0}^3u_a(k)s^a$、$V_k(s)=\sum_{a=0}^3v_a(k)s^a$。$s$ 是原时钟，系数多项式的高次不改变增益关于 $s$ 的至多三次条件。令

$$
R_k(q)=\begin{pmatrix}q&kq\\(1-q)/k&1-q\end{pmatrix},\qquad
A_Q=\beta+ek,\quad B_Q=-\beta+(a-e)k+\gamma k^2
\quad\left(Q=\begin{pmatrix}a&\beta\\\gamma&e\end{pmatrix}\right).
\tag{7.2}
$$

于是 $\operatorname{tr}(QR_k(q))=(A_Q+B_Qq)/k$。对表 6.1 的标签 $i\in\{1,2,3,4,5,6J,7JJ,7JM\}$，以该行的原时钟 $t_i$ 定义

$$
N_i=(A_{Q_i}+B_{Q_i}(\theta+\psi))V_k(t_i)
-B_{Q_i}\theta\psi U_k(t_i)-kV_k(0).
\tag{7.3}
$$

对 $i\in\{6M,7MJ,7MM\}$，定义

$$
O_i=k(-V_k(0)+\psi U_k(0))
+(A_{Q_i}+B_{Q_i}\theta)(V_k(t_i)-\psi U_k(t_i)).
\tag{7.4}
$$

这些都是五变量整数多项式。第三源使用 $X=b^2+r-r^2$、$Z=X+br$、$T=1+b$、$U_{\rm tr}=1+2b$，定义

$$
\begin{aligned}
D={}&TXZ+U_{\rm tr}(TXZ-4bTZ+6XZ-4bXT),\\
\widetilde B={}&N_4TXZ-U_{\rm tr}(4N_1bTZ-6N_2XZ+4N_3bXT),\\
\widetilde V_0={}&-\widetilde B,\\
\widetilde V_1={}&(N_1-N_4)bTZ
+U_{\rm tr}(N_1bTZ+6(N_1-N_2)bZ+4(N_3-N_1)b^2T),\\
\widetilde V_2={}&(N_2-N_4)XZ
+U_{\rm tr}(N_2XZ+4(N_1-N_2)bZ+4(N_3-N_2)bX),\\
\widetilde V_3={}&(N_3-N_4)bXT
+U_{\rm tr}(N_3bXT+4(N_1-N_3)b^2T+6(N_3-N_2)bX).
\end{aligned}
\tag{7.5}
$$

再置

$$
\begin{aligned}
G_5&=-4\widetilde V_0+15\widetilde V_1-20\widetilde V_2+10\widetilde V_3,\\
G_6&=-10\widetilde V_0+36\widetilde V_1-45\widetilde V_2+20\widetilde V_3,\\
G_7&=-20\widetilde V_0+70\widetilde V_1-84\widetilde V_2+35\widetilde V_3,\\
R_5&=b(1+r+3b)+r(1-r),\\
R_{6M}&=b(2+r+5b)+r(1-r),\\
R_{7MJ}&=b(1+4r+3b)+2r(1-r),\\
R_{7MM}&=b(3+2r+8b)+2r(1-r).
\end{aligned}
\tag{7.6}
$$

根方程是以下字面整数多项式，不作行缩放、primitive-part 归一或饱和：

$$
\begin{aligned}
E_0&=f(k),\\
E_1&=b\widetilde B+R_5G_5-bDN_5,\\
E_2&=b\widetilde B+R_{6M}G_6-bDO_{6M},\\
E_3&=b\widetilde B+R_{7MJ}G_7-bDO_{7MJ},\\
E_4&=b\widetilde B+R_{7MM}G_7-bDO_{7MM}.
\end{aligned}
\tag{7.7}
$$

**定义 7.2（隔离盒、预条件矩阵与有限证书）。** 以下 JSON 是证书的完整序列化数据。`center_numerators` 除以 $10^{80}$ 得中心 $m$，`preconditioner_numerators` 除以 $10^{40}$ 得矩阵 $C_{\rm pre}$，盒为 $\mathcal K_3=m+[-10^{-30},10^{-30}]^5$。各字符串中的分数与幂均按精确有理数解释。响应区间及漂移区间的分母以各自字段为准。

```json
{
  "variables": [
    "k",
    "theta",
    "psi",
    "r",
    "b"
  ],
  "center_denominator": "10^80",
  "center_numerators": [
    "135170138264509060920941464358507452644106098353769677261980391189333138499781947",
    "49641886755433939432803899789399989623290090240107202861332139864890456872378906",
    "76527529902567100293823315744941596163723301213848744467071215649897199370920751",
    "4743672767087795572707072560047805578116836592351617698327302984128931113863432",
    "19114715504377618515092060155534537515762604796788910695805590877792261569203431"
  ],
  "radius": "10^-30",
  "preconditioner_denominator": "10^40",
  "preconditioner_numerators": [
    [
      "-1208493617823390871946320160558275457",
      "0",
      "0",
      "0",
      "0"
    ],
    [
      "219036921761437997447619587399062937580",
      "732823485150298762485432821779584695986",
      "-452997157561581401933783142767008434471",
      "137368567312266578731886084987327294663",
      "31640738836541638754269982074443190152"
    ],
    [
      "-371170228601987938887919298884730852374",
      "-1139733434612934247305339075183391755691",
      "721751406085086254044973777342490938280",
      "-246098622084638389138492207494224668969",
      "-40475812602606886465357822727465857035"
    ],
    [
      "4527705732675340704213241994399204116",
      "10282946906544081406181599932702283902",
      "-14672926714994020508324102955211647267",
      "2967296245957139121077161862100223476",
      "2335790995032894390764628559867039442"
    ],
    [
      "-16588736578556359533698927798560975305",
      "44344228745140247513675256649529844969",
      "-57200442600393349256657086010717264153",
      "-19265039998042062433976429596888883951",
      "22524553094194242214220178380039946730"
    ]
  ],
  "polynomial_total_degrees": [
    7,
    19,
    19,
    19,
    19
  ],
  "polynomial_monomial_counts": [
    8,
    1082,
    1084,
    1082,
    1084
  ],
  "bounds": {
    "induced_infinity_norm_C": "<=1",
    "induced_infinity_norm_I_minus_C_JE_at_m": "<=10^-25",
    "infinity_norm_E_at_m": "<=10^-60",
    "infinity_norm_C_E_at_m": "<=10^-60",
    "hessian_bound_definition": "For E_i=sum_a c_ia x^a, set H_i=sum_{|a|>=2}|c_ia| |a|(|a|-1) 2^(|a|-2). Since every coordinate on the box has absolute value <=2, this bounds the sum over all ordered second partial derivatives in row i.",
    "H": [
      "17897372",
      "1723011608021760",
      "8244099155326464",
      "16832892743251968",
      "29227217855804928"
    ],
    "H_max": "<3*10^16",
    "contraction_norm": "<=10^-25+3*10^-14<10^-12",
    "self_map_displacement": "<=10^-60+10^-42<10^-30"
  },
  "polynomial_enclosure_rule": "For any expanded integer polynomial P=sum_a c_a x^a, let L(P)=sum_{|a|>=1}|c_a||a|2^(|a|-1). On the closed box, P lies in [P(m)-10^-30 L(P),P(m)+10^-30 L(P)]. Evaluate P(m) exactly as sum_a c_a product_j m_j^(a_j). All sign and response enclosures below use this rational rule, and division only after a denominator interval excludes zero.",
  "raw_integer_enclosures": {
    "N1": [
      "-3294",
      "-3293"
    ],
    "N2": [
      "-9523",
      "-9522"
    ],
    "N3": [
      "-1808",
      "-1807"
    ],
    "N4": [
      "1997",
      "1998"
    ],
    "N5": [
      "8816",
      "8817"
    ],
    "N6J": [
      "10116",
      "10117"
    ],
    "N7JJ": [
      "-7444",
      "-7443"
    ],
    "N7JM": [
      "-16374",
      "-16373"
    ],
    "O6M": [
      "9287",
      "9288"
    ],
    "O7MJ": [
      "-16452",
      "-16451"
    ],
    "O7MM": [
      "-37558",
      "-37557"
    ],
    "D": [
      "-135/1000",
      "-134/1000"
    ]
  },
  "response_enclosures": {
    "convention": "Each pair (L,U) means the exact response lies strictly in (L/10^6,U/10^6); these enclosures are descriptive, not the definitions of the responses.",
    "C": [
      69388395,
      69388396
    ],
    "z": [
      13172131,
      13172132
    ],
    "Y": [
      -14554448,
      -14554447
    ],
    "p": [
      -64246124,
      -64246123
    ],
    "u_J": [
      -73716635,
      -73716634
    ],
    "w_JJ": [
      54240742,
      54240743
    ],
    "w_JM": [
      119307915,
      119307916
    ],
    "u_M": [
      -67672769,
      -67672768
    ],
    "w_MJ": [
      119879363,
      119879364
    ],
    "w_MM": [
      273670352,
      273670353
    ]
  },
  "additional_enclosures": {
    "d_theta": [
      "-82620312/10^6",
      "-82620311/10^6"
    ],
    "d_psi": [
      "-88182216/10^6",
      "-88182215/10^6"
    ],
    "d_3": [
      "-319965/10^6",
      "-319964/10^6"
    ],
    "det_Ptheta_minus_P3": [
      "-266922/10^6",
      "-266921/10^6"
    ]
  }
}
```

**定理 7.3（交叠三世界的同父 $L_2$ 及其最小支撑）。** 式 (7.7) 在闭盒 $\mathcal K_3$ 中恰有一个实零点 $x_\dagger=(k,\theta,\psi,r,b)$。以下全部量均在该零点取值：

$$
\alpha=24/N_1,\qquad\lambda=\alpha k,
\tag{7.8}
$$

$$
\begin{aligned}
P_\theta&=R_k(\theta),&
g_\theta(s)&=\lambda(V_k(s)-\psi U_k(s)),&
d_\theta&=-\lambda(V_k(0)-\psi U_k(0)),\\
P_\psi&=R_k(\psi),&
g_\psi(s)&=\lambda(V_k(s)-\theta U_k(s)),&
d_\psi&=-\lambda(V_k(0)-\theta U_k(0)),\\
P_3&=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},&
g_3(s)&=\frac\alpha D\sum_{i=0}^3\widetilde V_i\ell_i(s),&
d_3&=\alpha\widetilde B/D.
\end{aligned}
\tag{7.9}
$$

记这些完整世界为 $W_\theta,W_\psi,W_3$。定义精确响应

$$
\begin{gathered}
C=\alpha N_2,\quad z=\alpha N_3,\quad Y=\alpha N_4,\quad p=\alpha N_5,\\
u_J=\alpha N_{6J},\quad w_{JJ}=\alpha N_{7JJ},\quad w_{JM}=\alpha N_{7JM},\\
u_M=\alpha O_{6M},\quad w_{MJ}=\alpha O_{7MJ},\quad w_{MM}=\alpha O_{7MM},\\
H_4^{[3]}=H_4(C,z,Y),\quad H_5^{[3]}=(H_4^{[3]},M,p),\quad
K_3=\{W_\theta,W_\psi,W_3\}.
\end{gathered}
\tag{7.10}
$$

三个世界合法且不同，并有

$$
K_3\subseteq\mathcal F(H_5^{[3]}),\qquad
L_2(K_3,H_5^{[3]}),\qquad L_2(\mathcal F(H_5^{[3]}),H_5^{[3]}).
\tag{7.11}
$$

在这一固定精确历史下，所有满足 $K\subseteq\mathcal F(H_5^{[3]})$、$L_2(K,H_5^{[3]})$ 的子集，其最小基数恰为三。此为见证支撑最小性，不是完整纤维的基数断言。父与第五响应满足 $69<C<70$、$13<z<14$、$-15<Y<-14$、$-65<p<-64$。

证明。先证明零点存在唯一性及所有除法的合法性。对展开的 $E_i=\sum_\nu c_{i\nu}x^\nu$，在 $|x_j|\le2$ 上有

$$
\sum_{j,h}|\partial_j\partial_hE_i(x)|
\le H_i:=\sum_{|\nu|\ge2}|c_{i\nu}|\,|\nu|(|\nu|-1)2^{|\nu|-2}.
\tag{7.12}
$$

由式 (7.1)–(7.7) 展开得到证书列出的次数、单项式数及五个 $H_i$；最后四行各有 $1082,1084,1082,1084$ 个单项式。式 (6.6) 给

$$
\|C_{\rm pre}\|_\infty\le1,\quad
\|I-C_{\rm pre}JE(m)\|_\infty\le10^{-25},\quad
\|E(m)\|_\infty\le10^{-60},\quad
\|C_{\rm pre}E(m)\|_\infty\le10^{-60}.
\tag{7.13}
$$

这些有限界的复算只需：以数组的升幂约定乘开式 (7.7)，逐项使用式 (6.6)，作五乘五有理矩阵点积，并取绝对行和。式 (7.12) 的有限和与 JSON 中的五个整数逐项对应，无浮点根作为输入。

$\mathcal K_3$ 内全部坐标绝对值小于二。沿 $m$ 到 $x$ 的线段积分导数，得

$$
\|JE(x)-JE(m)\|_\infty
\le10^{-30}\max_iH_i<3\cdot10^{-14}.
$$

于是 $T_E(x)=x-C_{\rm pre}E(x)$ 在盒内的导数范数小于 $10^{-25}+3\cdot10^{-14}<10^{-12}$，且

$$
\|T_E(x)-m\|_\infty\le10^{-60}+10^{-12}10^{-30}
=10^{-60}+10^{-42}<10^{-30}.
\tag{7.14}
$$

闭盒在无穷范数下完备且凸，Banach 压缩定理给唯一不动点，且它在内部。式 (7.13) 的矩阵缺陷小于一，Neumann 级数给 $C_{\rm pre}JE(m)$ 可逆；两因子均为五阶方阵，故 $C_{\rm pre}$ 可逆。不动点恰为 $E=0$，从而证明所述唯一零点。

其余符号界由明确有限包含法获得。对任一展开整数多项式 $P=\sum c_\nu x^\nu$ 令

$$
\mathcal L(P)=\sum_{|\nu|\ge1}|c_\nu||\nu|2^{|\nu|-1},\qquad
I(P)=[P(m)-10^{-30}\mathcal L(P),P(m)+10^{-30}\mathcal L(P)].
\tag{7.15}
$$

由一阶导数的系数界，$P(\mathcal K_3)\subseteq I(P)$。对 $N_i,O_i,D$ 按式 (7.15) 求值，给 JSON 的全部原多项式区间；对响应使用 $24I(N_i)/I(N_1)$ 或 $24I(O_i)/I(N_1)$，给十个严格的 $10^{-6}$ 响应包围。漂移分别使用

$$
-\frac{24I(k(V_k(0)-\psi U_k(0)))}{I(N_1)},\quad
-\frac{24I(k(V_k(0)-\theta U_k(0)))}{I(N_1)},\quad
\frac{24I(\widetilde B)}{I(N_1)I(D)}.
\tag{7.16}
$$

第三支源差行列式用多项式分子

$$
-kb(\theta-r)^2-(k\theta-b)\bigl(b(1-\theta)-kr(1-r)\bigr)
\tag{7.17}
$$

的 $I$ 区间除以 $I(kb)$，给证书中的严格负界。上述有限公式与所有字面数据完全指定所用每个包含，不需保留数值搜索或实验程序。

由中心与半径直接有

$$
k>1,\quad \frac{49}{100}<\theta<\frac12,\quad
\frac{76}{100}<\psi<\frac{77}{100},\quad
\frac4{100}<r<\frac5{100},\quad\frac{19}{100}<b<\frac{20}{100}.
\tag{7.18}
$$

再由证书 $-3294<N_1<-3293$、$-135/1000<D<-134/1000$，故 $k,b,N_1,D$ 均非零，式 (7.8)–(7.9) 的所有除法合法。三个源逐项正、迹一、行列式零，故秩恰一；式 (7.18) 的三个互不相交的首对角元区间区分三个源。

接着证明实际行等式。由所给八行数组乘开，按标签 $1,2,3,4,5,6J,7JJ,7JM$ 有整数多项式恒等式

$$
K_i:=A_{Q_i}U_k(t_i)+B_{Q_i}V_k(t_i)-kU_k(0)
=(0,0,0,0,0,0,0,6k^2f(k))_i.
\tag{7.19}
$$

这里使用前卷式 (19.11) 的全多项式恒等式，而非其旧参数矩形上的区间估计。由式 (7.2) 直接展开式 (7.9) 的实际读数，得

$$
\begin{aligned}
\alpha^{-1}\bigl(d_\theta+g_\theta(t_i)\operatorname{tr}(Q_iP_\theta)\bigr)-N_i&=-\psi K_i,\\
\alpha^{-1}\bigl(d_\psi+g_\psi(t_i)\operatorname{tr}(Q_iP_\psi)\bigr)-N_i&=-\theta K_i.
\end{aligned}
\tag{7.20}
$$

$E_0=f(k)=0$，故这八行完全相同，初读则由 $d=-g(0)$ 为零。对三个 M 续行，式 (7.4) 正是 $W_\theta$ 的未缩放实际响应。

第三源的完整逆可在除以 $D$ 前验证为多项式恒等式：令 $j=X/b,n=Z/b$，则

$$
\begin{gathered}
\widetilde V_0=-\widetilde B,\qquad
X\widetilde V_1=b(N_1D-\widetilde B),\qquad
T\widetilde V_2=N_2D-\widetilde B,\\
Z\widetilde V_3=b(N_3D-\widetilde B),\qquad
\widetilde B+U_{\rm tr}(-\widetilde V_0+4\widetilde V_1-6\widetilde V_2+4\widetilde V_3)=N_4D.
\end{gathered}
\tag{7.21}
$$

因此未缩放漂移 $\widetilde B/D$ 和整个多项式 $\sum_i\widetilde V_i\ell_i/D$ 给前五行 $(0,N_1,N_2,N_3,N_4)$。反之，对这一固定源，前四行迫出四个样本 $(-d,(N_1-d)/j,(N_2-d)/T,(N_3-d)/n)$；四节点插值唯一确定整个至多三次多项式。第四动作行清除正分母 $TXZ$ 后即 $Dd=\widetilde B$，故此非零 $D$ 图上也是充要逆。将增益与漂移同乘 $\alpha$ 后得到式 (7.9)，与式 (6.3) 的全世界逆一致。这个固定源逆不声称整个父纤维都在 $D\ne0$ 图上。

插值基在时钟 $4,5,6,7$ 的权重分别是

$$
(-1,4,-6,4),\quad(-4,15,-20,10),\quad
(-10,36,-45,20),\quad(-20,70,-84,35).
\tag{7.22}
$$

表 6.1 的相应源迹为 $R_i/b$，故第三世界未缩放续行读数为 $(b\widetilde B+R_iG_{t_i})/(bD)$。减去式 (7.3)–(7.4) 的目标响应得到

$$
(q_5-N_5,q_{6M}-O_{6M},q_{7MJ}-O_{7MJ},q_{7MM}-O_{7MM})
=\frac{(E_1,E_2,E_3,E_4)}{bD}=0.
\tag{7.23}
$$

乘回 $\alpha$ 就是完整实际读数等式。由式 (7.20)–(7.23)，逐行已获历史与见证为

| 已获部分或互择续行 | 同一个精确响应 | 使用的完整世界 |
| --- | --- | --- |
| 原时钟 $0,\ldots,5$ 沿 $JMJMM$ | $(0,24,C,z,Y,p)$ | $W_\theta,W_\psi,W_3$ |
| 第六 $J$ | $u_J$ | $W_\theta,W_\psi$ |
| 其后最终 $J$ | $w_{JJ}$ | 同一对 $W_\theta,W_\psi$ |
| 其后最终 $M$ | $w_{JM}$ | 同一对 $W_\theta,W_\psi$ |
| 第六 $M$ | $u_M$ | $W_\theta,W_3$ |
| 其后最终 $J$ | $w_{MJ}$ | 同一对 $W_\theta,W_3$ |
| 其后最终 $M$ | $w_{MM}$ | 同一对 $W_\theta,W_3$ |

每个 $g$ 是在任何动作前就固定的一个整个实多项式，每个 $d$ 是一个固定常数。各世界已有前两读 $0,24$，所以 $g\not\equiv0$。没有补加精确次数、样本非零、根简单或符号假设，整个原域也未排除零样本、重根或次数下降。式 (7.17) 给第六 M 对的源差严格非奇异，而 $\det(P_\theta-P_\psi)=0$；所以前卷定理 22.2 的“两支源差均奇异”假设不成立。

四个终端叶各含所指定的两个不同完整世界，故满足 $L_0$；各选定第六节点含同一对，且对两个终端动作均有实际共同响应，故满足 $L_1$。第五节点有三个世界，两个第六动作分别用 $u_J,u_M$，故满足 $L_2$。同一第五响应 $p$ 在两支之间不变；没有将不同第六响应处的碰撞拼接。将这些见证包含进完整 $\mathcal F(H_5^{[3]})$，原递归的每个存在分句仍由相同世界见证，证明式 (7.11)，无需穷尽该纤维。

最后证明最小支撑。若任意两元素 $K\subseteq\mathcal F(H_5^{[3]})$ 满足 $L_2$，前卷定义 8.1、定理 8.2 的全合法域分类适用，其中 $a_0=0,A=24,Z=z$，没有 chamber 条件。由其式 (8.3)，必有某 $0<\beta<1$ 使

$$
C=24+\frac{80}{7}(1+\beta)<\frac{328}{7}.
\tag{7.24}
$$

这与证书给出的 $C>69$ 矛盾。空集与单点又不满足停止守卫，而 $K_3$ 是实际三元素见证，所以整个精确历史下的最小支撑恰为三；论证覆盖纤维内任意二元素集，不只检查 $K_3$ 的三个二元素子集。∎

## 8. 两支源差非奇异的四世界实现及局部参数族

**定义 8.1（四源字面方程）。** 本节不沿用第 7 节的父参数、根或世界。变量次序为

$$
u=(r_1,b_1,r_2,b_2,r_3,b_3,\bar c,\bar z,\bar y),\qquad
C=40\bar c,\quad z=40\bar z,\quad Y=40\bar y,
\tag{8.1}
$$

固定第零源 $(r_0,b_0)=(1/3,1/4)$，其余三源取 $u$ 的相应坐标。对任一源 $(r,b)$，以下定义均使用同一组 $C,z,Y$：

$$
\begin{aligned}
X&=b^2+r-r^2,&N&=X+br,&T&=1+b,&U&=1+2b,\\
D&=TXN+U(TXN-4bTN+6XN-4bXT),\\
B&=YTXN-U(96bTN-6CXN+4zbXT),\\
V_0&=-B,\\
V_1&=(24-Y)bTN+U(24bTN+6(24-C)bN+4(z-24)b^2T),\\
V_2&=(C-Y)XN+U(CXN+4(24-C)bN+4(z-C)bX),\\
V_3&=(z-Y)bXT+U(zbXT+4(24-z)b^2T+6(z-C)bX),\\
G_5&=-4V_0+15V_1-20V_2+10V_3,\\
G_6&=-10V_0+36V_1-45V_2+20V_3,\\
G_7&=-20V_0+70V_1-84V_2+35V_3.
\end{aligned}
\tag{8.2}
$$

再定义

$$
\begin{aligned}
R_5&=b(1+r+3b)+r(1-r),\\
R_{6J}&=b(1+2r+2b)+r(1-r),&R_{6M}&=b(2+r+5b)+r(1-r),\\
R_{7JJ}&=R_5,&R_{7JM}&=b(2+5b)+r(1-r),\\
R_{7MJ}&=b(1+4r+3b)+2r(1-r),&R_{7MM}&=b(3+2r+8b)+2r(1-r),\\
\delta&=bD,&\mathsf N_5&=bB+R_5G_5,\\
\mathsf N_{6J}&=bB+R_{6J}G_6,&\mathsf N_{6M}&=bB+R_{6M}G_6,\\
\mathsf N_{7EG}&=bB+R_{7EG}G_7\quad(E,G\in\{J,M\}),\\
\mathbf n&=(\mathsf N_5,\mathsf N_{6J},\mathsf N_{7JJ},\mathsf N_{7JM},
\mathsf N_{6M},\mathsf N_{7MJ},\mathsf N_{7MM}).
\end{aligned}
\tag{8.3}
$$

$\mathbf n$ 的分量下标为 $0,\ldots,6$；上标 $a$ 仅标第 $a$ 个源，不是幂。下列九行依此顺序组成 $F(u)$：

$$
F(u)=\begin{pmatrix}
(\delta^1\mathbf n^0[k]-\delta^0\mathbf n^1[k])_{k=0,1,2,3}\\
(\delta^3\mathbf n^2[k]-\delta^2\mathbf n^3[k])_{k=0,4,5,6}\\
\delta^2\mathbf n^0[0]-\delta^0\mathbf n^2[0]
\end{pmatrix}.
\tag{8.4}
$$

这是有理系数多项式向量，计算前已代入式 (8.1) 的三个因子 $40$；不对行作缩放、取本原部分或隐式约分。

**定义 8.2（九维有限有理证书）。** 以下 JSON 中九个中心分子除以 $10^{40}$，八十一个预条件矩阵元除以 $10^8$，半径 $\rho=10^{-20}$。记闭盒 $\mathcal K_4=m+[-\rho,\rho]^9$。`checked_rational_bounds` 是精确值的向上有理包围，只有矩阵范数的第一项标明为精确值；其余不得当成相等式。所有 `_1e8` 区间均以端点除以 $10^8$，采用闭包含，特别 $b_0=1/4$ 的两端相等。七个 `ordered_responses` 按式 (8.3) 的分量次序排列。

```json
{
  "center_denominator": "10^40",
  "center_numerators": [
    "4557759729073436442796058377390588056011",
    "4190082928615718615189038304394566342756",
    "4067197602021839352406507101850594149930",
    "5355183630854491525141799510058711045852",
    "9404705059346670630750829277365830615728",
    "5772780794779080752176768670668835818951",
    "8669206514298209456447060366965794937823",
    "8412184959908890458278649069574788782168",
    "6070231472042998016520129449168845286458"
  ],
  "rho": "1/10^20",
  "box": "K={u: ||u-m||_infinity<=rho}. The whole box lies in (0,1)^9.",
  "preconditioner_denominator": "10^8",
  "preconditioner_integer_rows": [
    [
      -4906352171,
      208365504,
      -7678230763,
      5849222640,
      -727432,
      225569,
      689094,
      -502128,
      362241405
    ],
    [
      -12710436345,
      4933381344,
      -18049807412,
      12398117539,
      -1349763,
      418547,
      1278626,
      -931708,
      672145469
    ],
    [
      -2614656515,
      -527720431,
      -3524847249,
      2836712986,
      -5614988,
      2062013,
      420367,
      -582591,
      376798007
    ],
    [
      -5261690346,
      -714055163,
      -9734355078,
      7478084709,
      4832185,
      -1851772,
      817315,
      -291301,
      581897357
    ],
    [
      2251173976,
      556918726,
      2256310414,
      -1920735254,
      2891514,
      463605,
      -260728,
      -16390,
      -339112700
    ],
    [
      -5345408227,
      -709625720,
      -10009101297,
      7677378920,
      1801820,
      1458969,
      911140,
      -1100296,
      582339521
    ],
    [
      -1023519349,
      -126440332,
      -1988135321,
      1518029481,
      -223577,
      69329,
      211794,
      -154330,
      111335382
    ],
    [
      -2565317459,
      -318121777,
      -4973773762,
      3798559826,
      -519679,
      161147,
      492291,
      -358722,
      258786307
    ],
    [
      -3812838710,
      -401697543,
      -7932454510,
      6007567887,
      -685169,
      212463,
      649058,
      -472955,
      341195545
    ]
  ],
  "checked_rational_bounds": {
    "Cpre_norm_exact": "48767866753/100000000",
    "I_minus_Cpre_JF_center_upper": "155367273/1000000000000",
    "F_center_upper": "158919398/1000000000000000000000000000000000000000000000",
    "Cpre_F_center_upper": "48672/1000000000000000000000000000000000000000000000"
  },
  "usable_strict_bounds": [
    "||Cpre||_infinity<500",
    "||I-Cpre*JF(m)||_infinity<1/5000",
    "||F(m)||_infinity<1/10^35",
    "||Cpre*F(m)||_infinity<1/10^38"
  ],
  "coefficient_majorants": {
    "convention": "Coefficient 1-norm after substituting C=40*cbar,z=40*zbar,Y=40*ybar. Multiplication is submultiplicative and addition is subadditive. Fixing r0=1/3,b0=1/4 cannot increase this norm.",
    "X": 3,
    "N": 4,
    "T": 2,
    "U": 3,
    "D": 480,
    "B": 14784,
    "V0_V1_V2_V3": [
      14784,
      7232,
      8352,
      7056
    ],
    "G5_G6_G7": [
      405216,
      925152,
      1750448
    ],
    "max_R": 17,
    "max_numerator": 29772400,
    "max_F_row": 28581504000,
    "max_total_degree_F": 15,
    "max_ordered_Hessian_coefficient_sum": 6002115840000,
    "strict_Hessian_bound": "For every i, sum over j,k of ||partial_j partial_k F_i||_coeff <=15*14*28581504000=6002115840000<10^13."
  },
  "finite_reproduction": "Each checked norm is uniquely determined by the displayed rational polynomials, m and Cpre: differentiate F, evaluate at m by rational arithmetic, and take maximum absolute coordinate or maximum absolute row sum. The upper bounds in checked_rational_bounds are upward rational roundings of those exact quantities. No floating root is an input to any inequality.",
  "interval_rule": "For the following box certificates evaluate the displayed factored polynomial expressions with ordinary rational interval addition and endpoint-product multiplication on [m_i-rho,m_i+rho]. Source 0 has the singleton intervals 1/3,1/4. Divide only after D and b*D are proved nonzero. Every pair of integers [L,U] denotes containment in the closed interval [L/10^8,U/10^8].",
  "parent_enclosures_1e8": {
    "C": [
      3467682605,
      3467682606
    ],
    "z": [
      3364873983,
      3364873984
    ],
    "Y": [
      2428092588,
      2428092589
    ]
  },
  "world_enclosures_1e8": [
    {
      "source": 0,
      "r": [
        33333333,
        33333334
      ],
      "b": [
        25000000,
        25000000
      ],
      "c": [
        88888888,
        88888889
      ],
      "D": [
        4666401,
        4666402
      ],
      "d": [
        2913959655,
        2913959656
      ],
      "ordered_responses": [
        [
          208824277,
          208824278
        ],
        [
          118308452,
          118308453
        ],
        [
          3505864388,
          3505864389
        ],
        [
          3738200825,
          3738200826
        ],
        [
          -1177857106,
          -1177857105
        ],
        [
          3882028143,
          3882028144
        ],
        [
          4396487397,
          4396487398
        ]
      ],
      "g6": [
        -914940394,
        -914940393
      ],
      "g7": [
        199145517,
        199145518
      ]
    },
    {
      "source": 1,
      "r": [
        45577597,
        45577598
      ],
      "b": [
        41900829,
        41900830
      ],
      "c": [
        59197929,
        59197930
      ],
      "D": [
        -61876122,
        -61876121
      ],
      "d": [
        2950374382,
        2950374383
      ],
      "ordered_responses": [
        [
          208824277,
          208824278
        ],
        [
          118308452,
          118308453
        ],
        [
          3505864388,
          3505864389
        ],
        [
          3738200825,
          3738200826
        ],
        [
          -1408306135,
          -1408306134
        ],
        [
          3835198119,
          3835198120
        ],
        [
          4370300767,
          4370300768
        ]
      ],
      "g6": [
        -847531167,
        -847531166
      ],
      "g7": [
        168086825,
        168086826
      ]
    },
    {
      "source": 2,
      "r": [
        40671976,
        40671977
      ],
      "b": [
        53551836,
        53551837
      ],
      "c": [
        45058921,
        45058922
      ],
      "D": [
        -192635631,
        -192635630
      ],
      "d": [
        3040797219,
        3040797220
      ],
      "ordered_responses": [
        [
          208824277,
          208824278
        ],
        [
          230858005,
          230858006
        ],
        [
          3453788635,
          3453788636
        ],
        [
          3652222698,
          3652222699
        ],
        [
          -1622599936,
          -1622599935
        ],
        [
          3652989519,
          3652989520
        ],
        [
          4113706712,
          4113706713
        ]
      ],
      "g6": [
        -842543947,
        -842543946
      ],
      "g7": [
        119228528,
        119228529
      ]
    },
    {
      "source": 3,
      "r": [
        94047050,
        94047051
      ],
      "b": [
        57727807,
        57727808
      ],
      "c": [
        9698226,
        9698227
      ],
      "D": [
        -387343472,
        -387343471
      ],
      "d": [
        2627808549,
        2627808550
      ],
      "ordered_responses": [
        [
          208824277,
          208824278
        ],
        [
          -337281031,
          -337281030
        ],
        [
          3205617424,
          3205617425
        ],
        [
          3391729403,
          3391729404
        ],
        [
          -1622599936,
          -1622599935
        ],
        [
          3652989519,
          3652989520
        ],
        [
          4113706712,
          4113706713
        ]
      ],
      "g6": [
        -717508612,
        -717508611
      ],
      "g7": [
        153293945,
        153293946
      ]
    }
  ],
  "source_difference_determinant_enclosures_1e8": {
    "det(P0-P1)": [
      3518798,
      3518799
    ],
    "det(P2-P3)": [
      -27012334,
      -27012333
    ]
  }
}
```

**定理 8.3（四世界同父 $L_2$ 与非奇异双支）。** 字面 $F$ 在 $\mathcal K_4$ 中恰有一个实零点 $u_\ddagger$，它在内部，九个坐标均为实代数数，且 $J_uF(u_\ddagger)$ 非奇异。以下各源均在该根取值，令

$$
\begin{gathered}
c_a=r_a(1-r_a)/b_a,\qquad
P_a=\begin{pmatrix}r_a&b_a\\c_a&1-r_a\end{pmatrix},\\
d_a=B^a/D^a,\qquad
g_a(s)=\frac{\sum_{i=0}^3V_i^a\ell_i(s)}{D^a},\qquad
W_a=(P_a,g_a,d_a),\qquad q^a[k]=\mathbf n^a[k]/\delta^a.
\end{gathered}
\tag{8.5}
$$

这些定义的分母均非零，四个完整世界合法且不同。定义

$$
\begin{gathered}
p=q^0[0],\quad u_J=q^0[1],\quad v_{JJ}=q^0[2],\quad v_{JM}=q^0[3],\\
u_M=q^2[4],\quad v_{MJ}=q^2[5],\quad v_{MM}=q^2[6],\\
H_4^{[4]}=H_4(C,z,Y),\quad H_5^{[4]}=(H_4^{[4]},M,p),\quad
K_4=\{W_0,W_1,W_2,W_3\}.
\end{gathered}
\tag{8.6}
$$

则

$$
K_4\subseteq\mathcal F(H_5^{[4]}),\qquad
L_2(K_4,H_5^{[4]}),\qquad L_2(\mathcal F(H_5^{[4]}),H_5^{[4]}).
\tag{8.7}
$$

第六 J 支用 $(W_0,W_1)$，第六 M 支用 $(W_2,W_3)$。两对分别有不同固定漂移，且

$$
\det(P_0-P_1)>0,\qquad \det(P_2-P_3)<0,\qquad
 g_a(6)<0<g_a(7)\quad(a=0,1,2,3).
\tag{8.8}
$$

父读数包围为 $34.67<C<34.68$、$33.64<z<33.65$、$24.28<Y<24.29$，而 $2.08<p<2.09$。这些仅是同一个根所定义节点的包围，不是笛卡尔响应盒上的统一定理；也不主张四世界最小。

证明。先给证书界的有限依据。在 $C=40\bar c,z=40\bar z,Y=40\bar y$ 后，对多项式取系数一范数 $\|\cdot\|_{\rm coeff}$。加法次可加、乘法次可乘，且固定 $r_0=1/3,b_0=1/4$ 不增加此范数。逐式使用式 (8.2)–(8.3) 给

$$
\begin{gathered}
\|X\|_{\rm coeff}\le3,\quad\|N\|_{\rm coeff}\le4,\quad
\|T\|_{\rm coeff}\le2,\quad\|U\|_{\rm coeff}\le3,\\
\|D\|_{\rm coeff}\le480,\quad\|B\|_{\rm coeff}\le14784,\\
(\|V_0\|_{\rm coeff},\ldots,\|V_3\|_{\rm coeff})
\le(14784,7232,8352,7056),\\
(\|G_5\|_{\rm coeff},\|G_6\|_{\rm coeff},\|G_7\|_{\rm coeff})
\le(405216,925152,1750448),\\
\max_i\|R_i\|_{\rm coeff}\le17,\qquad
\max_k\|\mathbf n[k]\|_{\rm coeff}\le29772400.
\end{gathered}
\tag{8.9}
$$

例如 $\|\delta\|_{\rm coeff}\le480$，故式 (8.4) 每行的范数不超过 $2\cdot480\cdot29772400=28581504000$；由字面乘法次数不超过十五。于是

$$
\sum_{j,h}\|\partial_j\partial_hF_i\|_{\rm coeff}
\le15\cdot14\cdot28581504000=6002115840000<10^{13}.
\tag{8.10}
$$

式 (8.9) 的每项亦可直接展开，以 $\sum_\alpha|c_\alpha|$ 复算。中心矩阵界由式 (6.6) 与九乘九点积给出，四项分别为

$$
\begin{aligned}
\|C_{\rm pre}\|_\infty&=\frac{48767866753}{10^8}<500,\\
\|I-C_{\rm pre}JF(m)\|_\infty&\le\frac{155367273}{10^{12}}<\frac1{5000},\\
\|F(m)\|_\infty&\le\frac{158919398}{10^{45}}<10^{-35},\\
\|C_{\rm pre}F(m)\|_\infty&\le\frac{48672}{10^{45}}<10^{-38}.
\end{aligned}
\tag{8.11}
$$

证书已序列化 $m,C_{\rm pre}$；用式 (6.6) 在有理数域求九个值、八十一个偏导数，作八十一个九项矩阵点积和九项残差点积，再取范数，即完整复算式 (8.11)。它不依赖数值求根。

整个 $\mathcal K_4$ 位于 $(0,1)^9$，故式 (8.10) 及线段积分给

$$
\|JF(u)-JF(m)\|_\infty\le\rho\,10^{13}=10^{-7}.
$$

$T_F(u)=u-C_{\rm pre}F(u)$ 的导数范数小于 $1/5000+500\cdot10^{-7}=1/4000<1/1000$，且

$$
\|T_F(u)-m\|_\infty<10^{-38}+\rho/1000<\rho.
\tag{8.12}
$$

Banach 定理在完备闭盒上给唯一内部不动点。$\|I-C_{\rm pre}JF(m)\|<1$ 给两个方阵因子均可逆，故不动点与零点相同；同一导数估计还给盒内各点 $JF$ 非奇异。集合 $\{u\in\mathcal K_4:F(u)=0\}$ 是由有理系数等式与不等式定义的半代数单点集。实闭域投影保持半代数性，其每个坐标投影仍为有理系数半代数单点，因而坐标是实代数数。

所有剩余不等式使用定义 6.2 的端点运算：令每个 $u_j$ 取 $[m_j-\rho,m_j+\rho]$，第零源取单点 $1/3,1/4$，逐次评价式 (8.1)–(8.3) 所显示的因式表达式。先得四个 $D$ 区间，其符号依次为正、负、负、负；$b_a>0$，因此四个 $\delta$ 也排除零。随后评价

$$
c_a=\frac{r_a(1-r_a)}{b_a},\qquad d_a=\frac{B^a}{D^a},\qquad
q^a[k]=\frac{\mathbf n^a[k]}{b_aD^a},\qquad
g_a(6)=\frac{G_6^a}{D^a},\quad g_a(7)=\frac{G_7^a}{D^a}.
\tag{8.13}
$$

对两支源差，用

$$
\det(P_a-P_b)=-(r_a-r_b)^2-(b_a-b_b)(c_a-c_b)
\tag{8.14}
$$

用同一区间的普通端点乘法评价重复因子 $r_a-r_b$，允许重复变量带来的过估计；所得包含仍给证书中的严格符号。证书列出的六十一个包含由三项父读数、四源各十四项、两项行列式组成，均是上述有限端点规则的直接结果。四个互不相交的 $r$ 区间给六个两两源分离；$d_0,d_1$ 及 $d_2,d_3$ 的区间分别不交，八个增益样本区间均不含零。故式 (8.8) 的所有严格界已经在除法之后逐项得到，而除法前的 $b,D,\delta$ 非零由先行多项式包含保证。

现在核对完整世界及每个原行。记 $j=X/b,n=N/b,L=jTn$，直接展开式 (8.2) 得

$$
\begin{gathered}
D=b^2La_4,\qquad B=b^2L(Y-k_4),\qquad V_0=-B,\\
jV_1=24D-B,\qquad TV_2=CD-B,\qquad nV_3=zD-B,\\
B+U(-V_0+4V_1-6V_2+4V_3)=YD.
\end{gathered}
\tag{8.15}
$$

$\ell_i(h)=\delta_{ih}$（$0\le i,h\le3$），所以式 (8.5) 的一个整个 $g$ 与固定 $d$ 正好给前四行 $(0,24,C,z)$，最后一条式 (8.15) 给 $Y$。反之，这五行在固定源的 $D\ne0$ 图上迫出相同四样本、相同整个多项式及 $d=B/D$；证明与式 (7.21) 后的插值逆相同。这与式 (6.3) 的完整原世界逆一致，未将图外的 $D=0$ 世界从完整纤维删去。前两读 $0,24$ 排除恒零多项式。

式 (7.22) 的时钟 $5,6,7$ 权重给 $Dg(i)=G_i$。表 6.1 的七个续行源迹分别为式 (8.3) 的 $R_i/b$；所以 $q^a[k]$ 正是相应原时钟的 $d_a+g_a(i)\operatorname{tr}(Q_iP_a)$。每个世界的源逐项正、迹一、行列式零，秩恰一；增益次数至多三，漂移任意实常数，符合原域。至此，$F=0$ 的九行都能通过非零 $\delta$ 交叉相乘还原为实际共享响应等式：

$$
\begin{aligned}
q^0[k]&=q^1[k]&&(k=0,1,2,3),\\
q^2[k]&=q^3[k]&&(k=0,4,5,6),\\
q^0[0]&=q^2[0].
\end{aligned}
\tag{8.16}
$$

特别四世界共享完全相同的前六行 $(0,24,C,z,Y,p)$，不是只共享边缘范围。

| 同一个第五历史之后 | 第六已获响应 | 最终 $J$ 的共同响应 | 最终 $M$ 的共同响应 | 固定完整世界对 |
| --- | --- | --- | --- | --- |
| 实际第六 $J$ | $u_J=q^0[1]=q^1[1]$ | $v_{JJ}=q^0[2]=q^1[2]$ | $v_{JM}=q^0[3]=q^1[3]$ | $(W_0,W_1)$ |
| 实际第六 $M$ | $u_M=q^2[4]=q^3[4]$ | $v_{MJ}=q^2[5]=q^3[5]$ | $v_{MM}=q^2[6]=q^3[6]$ | $(W_2,W_3)$ |

两个最终动作在每支都使用已经取得的同一个第六响应；同一对世界在两个互择词中保持原来的整个增益和漂移。每个终端叶含两个不同世界，故 $L_0$；各选定第六节点非单点且满足两个终端分句，故 $L_1$；第五节点非单点且满足两个第六分句，故 $L_2$。相同见证保留于完整纤维，给式 (8.7)。这不是 $K_4=\mathcal F(H_5^{[4]})$ 的断言。∎

**定理 8.4（局部 $C^1$ 二参数联合实现族）。** 在式 (8.2)–(8.4) 中将第零源改为 $(r_0,b_0)=(a,b_0)$，其余未知量仍为式 (8.1) 的 $u$。存在 $(1/3,1/4)$ 的一个开邻域 $\mathcal U\subset\mathbb R^2$ 及 $C^1$ 映射 $u:\mathcal U\to\mathbb R^9$，在基点取值 $u_\ddagger$，使扩展的字面多项式方程 $F(a,b_0,u(a,b_0))=0$。对每个 $(a,b_0)\in\mathcal U$，式 (8.5)–(8.7) 仍给四个不同合法完整世界、同一个第五响应及两支完整双末碰撞。式 (8.8) 的严格符号、两支漂移差非零和四源分母非零均保留。

证明。扩展的 $F$ 是十一实变量的多项式，因而为 $C^1$；定理 8.3 已给基点的九乘九 $u$-Jacobian 可逆。普通隐函数定理给基点附近唯一的 $C^1$ 解图。四源正性、$r<1$、六个 $r$ 差非零、四个 $D$ 非零、四个 $\delta$ 非零、两个漂移差非零、八个增益样本的符号及两个行列式符号，都是连续函数在基点成立的有限个严格不等式。缩小 $\mathcal U$ 后它们同时保留，故所有世界仍合法且不同，全部除法仍合法。方程 $F=0$ 保留式 (8.16) 的精确等式；逐行原世界重建和停止守卫的证明不变，得所述 $L_2$。这里的可微性属于显式实现族，不是对恢复策略施加正则性。没有证明参数到 $(C,z,Y)$ 的映射秩，因此不推出父响应三元组含开集，也不推出任意笛卡尔响应窗口都可实现。∎

## 9. 联合实现的来源、适用域与原目标余项

第 7 节新增的是第三个完整世界与第六 M 块对旧第六 J 核的同时接合，及同一精确历史下的最小支撑消费者；八个整数核恒等式与全域二世界分类分别来自前卷定义 19.1、式 (19.11) 及定理 8.2。第 8 节新增的是两支源差都非奇异的四世界同父实现及其局部隐函数实现族。前卷定理 9.2、10.2 的完整逆作为两节共同接口，定理 22.2 的奇异源差障碍仅在其原假设内使用。这些是仓内既有结构上的综合推导，不主张文献原创性，也不将插值、压缩、隐函数或实闭域投影作为新增数学。

文献对应如下。Li–Lee–Bresler，《[A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems](https://arxiv.org/html/1501.06120)》定理 2.8、推论 3.4 的变换群可识别性与复数泛型子空间结论，有助于区分因子与整体世界；它们不提供本模型的任意实漂移、零增益和固定有限时钟上的共同历史。Ling–Strohmer，《[Self-Calibration and Bilinear Inverse Problems via Linear Least Squares](https://arxiv.org/html/1611.04196)》§2.2 的线性化使用可逆对角校准及相应重复设计或快照条件；这里不能假定 $g(i)\ne0$，也不能取得额外实验。Kech–Krahmer，《[Optimal Injectivity Conditions for Bilinear Inverse Problems](https://arxiv.org/html/1603.07316)》命题 IV.3 的提升差集与测量核关系提供割线类比；其复数泛型和稳定单射范围不替代固定 J/M、正源、漂移与自适应量词。

Villaverde–Tsiantis–Banga，《[Full observability and estimation of unknown inputs, states and parameters of nonlinear biological models](https://pmc.ncbi.nlm.nih.gov/articles/PMC6685009/)》定义 2.1–2.2、定理 2.2 是解析 ODE 与轨迹输入下的局部秩工具；Dong–Goodbrake–Harrington–Pogudin，《[Differential elimination for dynamical models via projections with applications to structural identifiability](https://arxiv.org/html/2111.00991)》区分单实验与多实验及泛型纤维，这些对应提醒不能用额外快照或局部秩替代完整离散历史。Alcázar–Caravantes–Díaz-Toca 的《[A new method to compute the singularities of offsets to rational plane curves](https://arxiv.org/abs/1502.04518v3)》仅提供参数对相等及分母检查的类比；没有将本响应纤维认定为其所研究的有理曲线偏移。这些文章均不作为式 (7.11) 或 (8.7) 的外部直接定理。

承重的一般工具是四节点 Lagrange 插值（本卷 §2.1 所引 Berrut–Trefethen §2）、诱导范数与 Neumann 级数、Banach 压缩定理、普通隐函数定理及实闭域的半代数投影。后两项可分别参见 Rudin《Principles of Mathematical Analysis》第 9 章隐函数定理，以及 Bochnak–Coste–Roy《[Real Algebraic Geometry](https://doi.org/10.1007/978-3-662-03718-8)》的 Tarski–Seidenberg 定理。此处隐函数定理的可逆 Jacobian 和投影的有理半代数单点假设已在定理 8.3–8.4 逐项给出；消元工具的继承出处为前卷式 (9.11)–(9.14)。全部新结论是普通数学证明及有限有理证书，不声称 Lean/kernel 验证或任何构建、覆盖、冻结状态。

两个父必须分别使用。第 7 节 $z<14<144/5$，不在前卷定理 4.1 的第四 J 精确对 chamber；第 8 节 $z>9C/10$，也不在该 chamber。它们既不能彼此拼接，也不能附接旧第四 J 对以构造祖先。第 7 节最小支撑为三的结论不迁移到第 8 节。第 8 节虽由前卷定理 8.2 的必要条件 $C=24+(80/7)(1+\beta)>248/7$ 排除两世界 $L_2$，但尚未决定其父上的三世界可行性，因而没有四世界最小性。两节均只证明完整父纤维包含所给见证，不给完整纤维的穷尽或基数上界。

精确保留的原目标余项为：

1. 对字面 $H_4^\star=(0,J,24,M,35,J,26372/875,M,528/35)$，在所有尚未解决的实际第五响应 $p$ 中，是否存在第五 M 的完整同响应 $L_2$ 仍未决定。第 2–3 节只处理 $p_\star$；第 5 节只处理其明确的闭响应窗口及已获子节点。
2. 对 $H_4^{[3]}$ 与 $H_4^{[4]}$ 各自的第五 J 臂，仍需一个在该父下取得的共同 $p_J$，以及其第六 J、M 两个失败子节点；每个子节点须有一个已获共同第六响应，且在这一响应内同时满足两个最终动作的碰撞与全部非单点停止守卫。两节各只完成式 (1.7) 中 $F=M$ 的两个块，不给任一个 $L_3(H_4)$。
3. 通往这些父的同历史第四动作替代证明、所有更早祖先及互择动作、原根 $L_7$ 的全部响应与停止守卫仍未解决；旧 chamber 的第四 J 证明不满足当前父的参数对应。
4. 无限制自适应八读恢复或不可能性、八读与九读比较，以及原完整域的九读充分性仍未解决。策略仍可为任意确定性历史依赖函数，不附连续、可测、可计算或有限描述条件。

上述两个实际第五 M 节点各自给出完整原世界的联合实现；原根与九读任务的完成判据保持定义 1.3 的原范围。

## 追加锚（本行以下为增补区）

## 10. 自由父读数的第五 J 完整二世界分类

本节将第五动作取为 $J$，并在本节及第 11 节允许 $A>0,C>0$ 自由变化。第 12 节再取 $A=24$，分别应用于第 7、8 节的两个父。定义 1.1 的完整原域、定义 1.3 的失败递归和原恢复目标均保留；这里的参数扩大不改变前文固定历史的含义。

**定义 10.1（第五 J 的字面历史与严格过滤）。** 记

$$
\begin{aligned}
H_4^A(C,z,Y)&=(0,J,A,M,C,J,z,M,Y),\\
H_{5J}^A(C,z,Y,p)&=(H_4^A(C,z,Y),J,p),\qquad j=b+c.
\end{aligned}
\tag{10.1}
$$

除另行声明外，$z,Y,p$ 遍及实数。每个候选世界必须满足

$$
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\quad
0<r<1,\quad b,c>0,\quad bc=r(1-r),\quad
0\ne g\in\mathbb R[v],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{10.2}
$$

一个世界只使用一个整个多项式 $g$ 与一个固定漂移 $d$。正非对角元起初无上界。实际乘积仍为 $Q_0=I,Q_i=E_iQ_{i-1}$，每步读 $d+g(i)\operatorname{tr}(Q_iP)$；初读计数，时钟恰为 $0,\ldots,7$，不重置、不复制、不跳读、不重编号、不增加动作或端口。沿 $JMJMJ$ 的六个已获方程为

$$
\begin{aligned}
0&=d+g(0),&A&=d+jg(1),\\
C&=d+(1+b)g(2),&z&=d+(j+r)g(3),\\
Y&=d+(1+2b)g(4),&p&=d+(j+2r)g(5).
\end{aligned}
\tag{10.3}
$$

用 $n=2,3$ 分别标记第六动作 $J,M$，不以 $n$ 替代时钟。相应原矩阵与响应为

$$
\begin{array}{c|c|c}
\text{位置}&Q&\text{实际响应}\\ \hline
6,n&\left(\begin{smallmatrix}1&0\\n&1\end{smallmatrix}\right)
&h_n=d+(1+nb)g(6)\\
7,nJ&\left(\begin{smallmatrix}n&1\\1&0\end{smallmatrix}\right)
&f_{nJ}=d+(j+nr)g(7)\\
7,nM&\left(\begin{smallmatrix}n&1\\n+1&1\end{smallmatrix}\right)
&f_{nM}=d+(1+nb+j+(n-1)r)g(7).
\end{array}
\tag{10.4}
$$

这是根卷《[FIB 同父历史的采样零层坍缩与失效核心](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md)》式 (21.2) 的同一实际动作表，父响应现在自由。所有源迹严格正。表中互择响应仅比较预先固定世界的函数值；一个实际分支只取得其所选动作的响应。

以下称一个二次式的“两合法根”，意为它有两个不同实根，两个根都满足 $0<r<1$，并且由所给 $b$ 及 $c=r(1-r)/b$ 得严格源。重根只给一个世界。各族所列父读数等式、第五响应等式及式 (10.2) 都是定义的一部分，不允许只满足其中的边缘范围。

**定义 10.2（四种精确合法对）。** 固定式 (10.1) 的 $A,C,z,Y,p$。下列各族均指两个完整世界组成的无序对。

（一）$Z_{67}$。置

$$
\kappa=\frac{\sqrt{17}-1}{4},\qquad
2\kappa^2+\kappa-2=0.
\tag{10.5}
$$

选择 $d\ne0$ 及不同的 $b_1,b_2\in(0,1/\kappa)$，令

$$
\begin{aligned}
r_i&=\kappa b_i,&c_i&=\kappa(1-\kappa b_i),\\
g_1(v)&=-\frac d{84}(v-6)(v-7)(b_2v+2),&
g_2(v)&=-\frac d{84}(v-6)(v-7)(b_1v+2).
\end{aligned}
\tag{10.6}
$$

两世界漂移均为 $d$。写 $t=1+b_1,s=1+b_2$，要求精确等式

$$
\begin{aligned}
A&=d\left(1-\frac{5\kappa(s+1)(t+1)}{28}\right),\\
C&=d\left(1-\frac{10st}{21}\right),\\
z&=d\left(1-\frac{\kappa(3s-1)(3t-1)}{14}\right),\\
Y&=d\left(1-\frac{(2s-1)(2t-1)}7\right),\\
p&=d\left(1-\frac{\kappa(5s-3)(5t-3)}{84}\right).
\end{aligned}
\tag{10.7}
$$

特别，第一等式和 $A>0$ 排除其归一化因子为零，但不预设漂移符号。正源曲线 (10.6) 继承前卷引理 2.3、式 (2.12)–(2.13)，不作为新曲线。

（二）$Z_{137}$。要求

$$
d=A=z,\qquad b=\frac{21C-26A}{5A}>0,\qquad
Y=\frac{176A-126C}{35}.
\tag{10.8}
$$

两世界共用

$$
g(v)=\frac A{21}(v-1)(v-3)(v-7),\qquad
V=\frac{21(A-p)}{16A}.
\tag{10.9}
$$

取二次式

$$
r^2-(1+2b)r+b(V-b)=0
\tag{10.10}
$$

的两合法根，分别取 $c=r(1-r)/b$。两合法根的条件也可精确写为

$$
0<b<\frac12,\qquad
2+b<V<b+\frac{(1+2b)^2}{4b}.
\tag{10.11}
$$

（三）$Z_{157}$。要求

$$
d=A=p,\qquad b=\frac{7C-10A}{3A}>0,\qquad
Y=\frac{42C-16A}{35}.
\tag{10.12}
$$

两世界共用

$$
g(v)=\frac A{35}(v-1)(v-5)(v-7),\qquad
N=\frac{35(z-A)}{16A}.
\tag{10.13}
$$

取二次式

$$
r^2-(1+b)r+b(N-b)=0
\tag{10.14}
$$

的两合法根，分别取 $c=r(1-r)/b$；等价的严格域为

$$
0<b<1,\qquad 1+b<N<b+\frac{(1+b)^2}{4b}.
\tag{10.15}
$$

因此这一族的父平面条件恰为

$$
R_{15}:=35Y-42C+16A=0.
\tag{10.16}
$$

（四）$Z_{357}$。要求

$$
\begin{gathered}
d=z=p\ne0,\qquad b=6-\frac{7C}{d}>0,\\
j=\frac{35(d-A)}{16d},\qquad c=j-b>0,\qquad
Y=\frac{48d-14C}{35},\qquad 0<bc<\frac14.
\end{gathered}
\tag{10.17}
$$

两世界共用

$$
g(v)=\frac d{105}(v-3)(v-5)(v-7),\qquad
r_\pm=\frac{1\pm\sqrt{1-4bc}}2.
\tag{10.18}
$$

这里的 $c$ 已固定，两根均给同一个 $bc$。定义不先给 $d$ 添符号条件；严格源过滤及响应方程决定哪些参数可行。

**定理 10.3（自由 $C$ 的完整两世界充要分类）。** 对每个 $A>0,C>0,z,Y,p\in\mathbb R$，以及每个由两个不同完整世界组成的
$K\subseteq\mathcal F(H_{5J}^A(C,z,Y,p))$，有

$$
L_2(K,H_{5J}^A)
\quad\Longleftrightarrow\quad
K\text{ 是定义 10.2 的一个合法 }Z_{67},Z_{137},Z_{157}\text{ 或 }Z_{357}\text{ 对}.
\tag{10.19}
$$

左侧不假设根、共同漂移、共同增益、精确次数、源差非奇异或样本非零。这些合法对事实上都有非零漂移和真三次增益；它们是结论，不能作为必要性证明的输入。

证明。精确二元素集的非单点子集只能是它自身。因此定义 1.3 逐层等价于：这同一对在每种第六动作后同读，并在该已获第六响应之后的两个最终动作分别同读。不同第六动作的共同响应不必彼此相等。此处只使用精确二元素支持，不对一般支持作两世界抽取。

先写 $G_i=g_i(7)$。四个终端等式由式 (10.4) 给出。跨 $n=2,3$ 相减，最终 $J$ 等式给 $r_1G_1=r_2G_2$，最终 $M$ 等式给
$(b_1+r_1)G_1=(b_2+r_2)G_2$，故 $b_1G_1=b_2G_2$。在 $n=2$ 将最终 $M$ 减最终 $J$，又有

$$
(1-r_1+2b_1)G_1=(1-r_2+2b_2)G_2.
\tag{10.20}
$$

前两个关系代回即得 $G_1=G_2=G$。若 $G\ne0$，则 $r,b$ 相同，秩一给相同 $c$，一个终端等式给相同漂移。前四个已获方程的源迹都正，故增益在 $0,1,2,3$ 的值相同。沿用四节点插值，整个增益相同，两个完整世界相同，矛盾。因此

$$
g_1(7)=g_2(7)=0,\qquad d_1=d_2=d.
\tag{10.21}
$$

这一步也排除同源但不同增益或漂移的伪例外。以上终端消元是根卷定理 21.3 中与父参数无关的既有步骤。

再令 $K_i=g_i(6)$。两个第六等式为

$$
(1+2b_1)K_1=(1+2b_2)K_2,\qquad
(1+3b_1)K_1=(1+3b_2)K_2.
\tag{10.22}
$$

相减后代回，得 $K_1=K_2=K_6$ 及 $K_6(b_1-b_2)=0$，没有除未知样本。

先设 $K_6\ne0$。此时 $b_1=b_2=b$，两个增益在四个互异节点 $0,2,6,7$ 上分别为

$$
-d,\qquad (C-d)/(1+b),\qquad K_6,\qquad0.
\tag{10.23}
$$

次数界与同一插值唯一性给一个共同整个 $g$。三个奇节点的方程为

$$
g(1)j_i=A-d,\qquad
g(3)(j_i+r_i)=z-d,\qquad
g(5)(j_i+2r_i)=p-d.
\tag{10.24}
$$

若其中至少两个样本非零，两个不同斜率的线性方程固定 $j,r$，源与世界均同。若三个样本都零，连同根七得到四个不同根，也不合法。因此恰有两个奇样本为零。因式定理给三种且仅三种根集 $137,157,357$；初值 $g(0)=-d$ 固定相应尺度，$d=0$ 将增添第四个不同根，故此支 $d\ne0$。

同一个整个增益的样本如下；前两行乘 $A$，第三行乘 $d$。

$$
\begin{array}{c|rrrrrrrr}
&0&1&2&3&4&5&6&7\\ \hline
g_{137}/A&-1&0&5/21&0&-3/7&-16/21&-5/7&0\\
g_{157}/A&-1&0&3/7&16/35&9/35&0&-1/7&0\\
g_{357}/d&-1&-16/35&-1/7&0&1/35&0&-1/35&0.
\end{array}
\tag{10.25}
$$

代入式 (10.3)，前两行依次给式 (10.8)–(10.10)、(10.12)–(10.14)。例如第二行给

$$
C=A+\frac{3A}{7}(1+b),\qquad
Y=A+\frac{9A}{35}(1+2b),
\tag{10.26}
$$

消去 $b$ 正好是式 (10.16)。其唯一非零奇行分别固定 $j+2r=V$、$j+r=N$；与 $bc=r(1-r)$ 合用就是所列二次式。对前者，两不同合法根和为 $1+2b<2$，在一处的多项式值为 $b(V-b-2)>0$，判别式严格正，得到式 (10.11)。反向这些不等式使两根乘积正、根和在零与二之间、在一处取正值，故两根都在 $(0,1)$。式 (10.15) 同理由根和 $1+b$ 及在一处的值 $b(N-b-1)$ 得到。

第三行先给 $d=z=p\ne0$，再依次从第二、第一、第四读得到式 (10.17) 的 $b,j,Y$。固定 $b,c$ 后，源条件是 $r^2-r+bc=0$，其两个不同合法根恰要求 $0<bc<1/4$，即式 (10.18)。至此 $K_6\ne0$ 支全部分类完毕。

再设 $K_6=0$。沿用前卷定义 1.2 的双末根表示，在当前初读零下写

$$
g_i(v)=(v-6)(v-7)(a_iv-d/42).
\tag{10.27}
$$

这是包含二次、剩余重根与额外零样本的完整表示。令

$$
X=a_1P_1-a_2P_2=\begin{pmatrix}x_0&x_1\\x_2&x_3\end{pmatrix},\qquad
\mathsf V=d(P_1-P_2)=\begin{pmatrix}v_0&v_1\\v_2&-v_0\end{pmatrix}.
\tag{10.28}
$$

五个前缀响应差直接调用前卷引理 2.1 的第五 $J$ 完整核：

$$
x_0=x_1=0,\quad x_2=(v_1+v_2)/42,\quad
x_3=v_1/84,\quad v_0=2(v_1+v_2),\quad
a_1-a_2=v_1/84.
\tag{10.29}
$$

不重新建立该线性核，也不把核内任意点当成实际源。若 $d=0$，则 $\mathsf V=X=0$；取迹给 $a_1=a_2\ne0$，继而两源相同。故不同世界要求 $d\ne0$。

记 $\delta b=b_1-b_2$，其余差同理。若 $\delta b=0$，核给共同 $a$ 及 $\delta r=2\delta c$。当 $a\ne0$，$x_0=a\delta r=0$ 给所有源差为零；当 $a=0$，$x_2=0=d\delta c/42$ 再给同一结论。所以只剩 $\delta b\ne0$。

这时 $x_1=0$ 与迹关系给

$$
a_1=-db_2/84,\qquad a_2=-db_1/84.
\tag{10.30}
$$

由 $x_0=0$ 得 $r_1/b_1=r_2/b_2=:\kappa>0$。由 $v_0=2(v_1+v_2)$ 得
$\delta c=(\kappa/2-1)\delta b$。令 $h=\kappa/2-1$；把式 (10.30) 代回 $x_2$ 给

$$
c_i-b_ih=2(1+h)=\kappa,\qquad
r_i=\kappa b_i,\qquad c_i=\kappa+hb_i.
\tag{10.31}
$$

实际秩一条件于是成为

$$
bc-r(1-r)=(\kappa^2+\kappa/2-1)b_i^2=0.
\tag{10.32}
$$

严格 $b_i>0$ 与 $\kappa>0$ 给式 (10.5) 的唯一正根。因 $h=-\kappa^2$，式 (10.31) 正好回到继承曲线 (10.6)；$0<r_i<1$ 给 $0<b_i<1/\kappa$。式 (10.27)、(10.30) 给两增益，原五行给对称式 (10.7)。因此这一支恰为 $Z_{67}$，没有遗漏其他核内可实现点。

最后证明四族的反向实际实现及全部守卫。$Z_{67}$ 的源由式 (10.5)–(10.6) 逐项正、迹一且行列式零；不同 $b_i$ 区分源。其余三族的两合法根及 $c$ 定义同样给严格正、迹一、秩恰一源，并区分两个世界。每个增益由非零尺度给一个预先固定的非零三次多项式，漂移固定。式 (10.7) 或样本表 (10.25) 逐行给全部已获历史 (10.3)。其后两世界的共同响应为

$$
\begin{array}{c|c|c|c}
\text{族}&\text{第六 }J&\text{第六 }M&\text{四种最终响应}\\ \hline
Z_{67}&d&d&d\\
Z_{137}&A-5A(1+2b)/7&A-5A(1+3b)/7&A\\
Z_{157}&A-A(1+2b)/7&A-A(1+3b)/7&A\\
Z_{357}&d-d(1+2b)/35&d-d(1+3b)/35&d.
\end{array}
\tag{10.33}
$$

对任一第六动作，选该行的实际共同响应。所得子切片保留同一对不同完整世界；在它的每种最终动作后，再选表中的共同响应，仍保留同一对，故终叶有 $L_0$。两个最终分句与子节点非单点给 $L_1$；两个第六分句与父非单点给 $L_2$。所有子历史都在同一个 $H_{5J}^A$ 下，既不拼接不同父，也不把另一分支的响应当成已获响应。

必要性未除源差行列式、任何局部图分母 $D$、增益首项、根差或判别式。零漂移、低次数、重根、采样零与同源不同扰动均先保留，再由明确分支识别或排除。除法仅用固定节点差、严格正源因子及已证明非零的分支量 $K_6,d,\delta b$、所选奇样本。故旧图的 $D=0$ 层仍在完整量词内。∎

## 11. 根七漂移条带上整个实际 JJ 纤维及显式逆

**定义 11.1（完整条带类与实际 JJ 映射）。** 对每个 $A>0,C>0,z,Y,p\in\mathbb R$，令 $H=H_{5J}^A(C,z,Y,p)$，并定义

$$
\mathcal S_p=\{W\in\mathcal F(H):g(7)=0,\ 0\le d\le21C/11\},\qquad
\Psi_{JJ}(W)=(h_2(W),f_{2J}(W)).
\tag{11.1}
$$

$\Psi_{JJ}$ 是先实际第六 $J$、再实际最终 $J$ 的两个响应；不是同时读取互择动作。条带是条件定理的声明类，原世界域仍是式 (10.2)。其成员的增益可以降次、重根或有额外采样零。

**定理 11.2（整个纤维的二元界、例外与逆）。** 映射 $\Psi_{JJ}$ 在整个 $\mathcal S_p$ 上的每个纤维至多有两个完整世界。每个二元素纤维恰为定义 10.2 中处于该条带的一个合法 $Z_{137},Z_{157}$ 或 $Z_{357}$ 对；反向每个这样的对都是一个完整二元素纤维。

对任何候选实际响应 $(u,a)$，下述公式和严格过滤给恰好整个纤维，包括空纤维及单点纤维；对实际来自 $\mathcal S_p$ 的响应，过滤后必非空。

先取 $d=a$ 并要求 $0\le d\le21C/11$。置

$$
R=Y-\frac{6(C-d)}5+\frac d7-u.
\tag{11.2}
$$

若 $d=0$，要求 $R<0$ 并取

$$
t=-\frac{3C}{5R}.
\tag{11.3}
$$

若 $d>0$，要求根式为实并取较大根

$$
t=\frac{35R+\sqrt{1225R^2+840d(C-d)}}{20d}.
\tag{11.4}
$$

要求 $t>1$，令 $b=t-1$，并置

$$
\xi=\frac{C-d}{t},\qquad \eta=\frac{Y-d}{2t-1},\qquad
g(v)=(v-7)\left[
\frac{d(v-2)(v-4)}{56}
+\frac{\xi v(v-4)}{20}
-\frac{\eta v(v-2)}{24}\right].
\tag{11.5}
$$

最后求下面所有严格合法源，而不是任择一个二次根。记

$$
q_m=g(2m+1),\qquad (a_0,a_1,a_2)=(A,z,p),\qquad m=0,1,2.
\tag{11.6}
$$

这里 $a_m$ 只是三个已获奇读数的局部记号，$a_0=A$ 不是初读。当 $q_m=0$ 时，必须有 $a_m=d$；当 $q_m\ne0$ 时，要求

$$
j+mr=\frac{a_m-d}{q_m}.
\tag{11.7}
$$

若至少两个 $q_m,q_n$ 非零，$m\ne n$，取 $L_h=(a_h-d)/q_h$，显式求
$r=(L_n-L_m)/(n-m),j=L_m-mr$。若恰一个 $q_m$ 非零，取 $L=(a_m-d)/q_m$，候选为

$$
r_\pm=\frac{1+mb\pm\sqrt{(1+mb)^2-4b(L-b)}}2,\qquad
j=L-mr_\pm.
$$

根式非实即无候选；重根只计一次。三个 $q_m$ 全零则无合法候选。对每个候选取 $c=j-b$，保留且只保留式 (10.2)、全部式 (10.3) 及实际响应 $(u,a)$ 成立的世界 $W=(P,g,d)$。增益非零条件也保留在过滤中。不同源产生不同完整世界。

证明。根七使实际最终 $J$ 的响应为 $a=d$，故任何同纤维世界已有同一漂移。置 $t=1+b>1$，则原第二、第四读给 $g(2)=\xi,g(4)=\eta$。沿用既有四节点插值，在互异节点 $0,2,4,7$ 的值为 $-d,\xi,\eta,0$，唯一给式 (11.5)。这是根卷引理 3.1 的插值式在自由 $C$ 上的参数对应，不是另立插值定理。求得

$$
g(6)=\eta-\frac35\xi-\frac d7,\qquad
u(t)=Y-\frac{3(C-d)(2t-1)}{5t}-\frac{d(2t-1)}7.
\tag{11.8}
$$

对不同 $t,s>1$，其精确差商为

$$
\frac{u(t)-u(s)}{t-s}
=-\frac{2d}7-\frac{3(C-d)}{5ts}.
\tag{11.9}
$$

当 $0\le d\le C$ 时右侧严格负，包含 $d=0,C$。当 $C<d\le21C/11$ 时，由 $ts>1$，有

$$
-\frac{2d}7+\frac{3(d-C)}{5ts}
<-\frac{2d}7+\frac{3(d-C)}5
=\frac{11d-21C}{35}\le0.
\tag{11.10}
$$

所以每个实际纤维唯一固定 $t,b$，再由式 (11.5) 固定整个 $g$，无需源界或局部图。

将式 (11.8) 重排，恰为

$$
R=\frac{2d}7t-\frac{3(C-d)}{5t},\qquad
10dt^2-35Rt-21(C-d)=0.
\tag{11.11}
$$

$d=0$ 给式 (11.3)。$d>0$ 时，若 $d\le C$，另一根非正；若 $C<d\le21C/11$，两根乘积为

$$
q=\frac{21(d-C)}{10d}\le1.
\tag{11.12}
$$

一个实际根 $t>1$ 的另一根是 $q/t<1$，因此实际根一定是式 (11.4) 的较大根。实际响应的判别式满足

$$
1225R^2+840d(C-d)
=\left(10dt+\frac{21(C-d)}t\right)^2>0.
\tag{11.13}
$$

最后一个严格性在 $d\le C$ 时直接成立；在 $d>C$ 时，括号为 $10d(t-q/t)>0$。故没有丢掉条带上端点。具体地，$d=C$ 时 $t=7R/(2C)$；$d=21C/11$ 时

$$
R=\frac{6C}{11}(t+t^{-1}),\qquad
u'(t)=\frac{6C}{11}(t^{-2}-1)<0.
\tag{11.14}
$$

这些公式同时包含零漂移、端点和可能的增益次数下降。任意提出的 $(u,a)$ 仍须经过全部过滤；根式为实或 $t>1$ 单独均不保证历史可实现。

现在确定完整源。三个奇样本不可能全零，否则非零至多三次 $g$ 有根 $1,3,5,7$。若至少两个非零，式 (11.7) 的不同斜率固定唯一 $j,r$；例如对 $m\ne n$，先取
$r=((a_n-d)/q_n-(a_m-d)/q_m)/(n-m)$，再取 $j=(a_m-d)/q_m-mr$。其余奇行和严格源条件只作过滤，所以至多一个世界。

若恰一个奇样本非零，另外两个奇根连同根七将 $g$ 强制为式 (10.25) 的一行；两零奇行强制相应的漂移等式。唯一非零奇行和秩一条件给式 (10.10)、(10.14) 或 $r^2-r+bc=0$。每个二次式至多两个不同合法根，且所有合法根均由式 (11.7)、(10.3) 保留。因此整个实际纤维至多二元，非单点时恰为所列合法对。反向每个条带内合法对由式 (10.33) 确实同属一个实际 JJ 纤维；整个纤维已有二元上界，故这对就是整个纤维，不会隐藏第三个世界。

上述重建必要性来自每个实际世界的原行，充分性来自重建候选逐行满足原行及严格过滤。未使用增益首项、重根排除或 $D\ne0$ 图，也没有从精确对分类反推一般纤维。∎

**推论 11.3（条带内任意支持的精确失败条件）。** 对每个有限或无限的 $S\subseteq\mathcal S_p$，有

$$
L_2(S,H_{5J}^A)
\quad\Longleftrightarrow\quad
S\text{ 包含一个条带内合法 }Z_{137},Z_{157}\text{ 或 }Z_{357}\text{ 对}.
\tag{11.15}
$$

证明。若有 $L_2$，第六 $J$ 分句给一个已获响应 $u$ 及其 $L_1$ 子切片；该节点最终 $J$ 分句再给一个响应 $a$ 及含至少两个不同世界的 $L_0$ 叶。这些世界同在一个实际 JJ 纤维。定理 11.2 给整个条带纤维至多二元且其非单点形式精确已知，故所需对确实在 $S$ 内。反向，该对由定理 10.3 已满足全部 $L_2$ 守卫；同历史包含单调性将相同见证保留在 $S$ 中。这里的两世界归结依赖整个支持处于声明条带及已证整个纤维界，不是一般支持的抽取规则。∎

## 12. 两个父盒对所有第五 J 响应的统一排除

**定义 12.1（分别包含两个实际父的闭盒）。** 本节取 $A=24$。以 $(C,z,Y)$ 为坐标，置

$$
\begin{aligned}
\mathcal B_{[3]}&=[69,70]\times[13,14]\times[-15,-14],\\
\mathcal B_{[4]}&=[3467/100,3468/100]
\times[3364/100,3365/100]\times[2428/100,2429/100].
\end{aligned}
\tag{12.1}
$$

第 7 节的精确父 $H_4^{[3]}$ 处于第一个盒内部，第 8 节的精确父 $H_4^{[4]}$ 处于第二个盒内部。盒内排除结论对每一点成立；第五 $M$ 的存在性仍只按第 7、8 节各自的精确父及所述局部实现族使用，不扩张为这两个笛卡尔盒上的统一存在性。

**定理 12.2（全 $p$ 的二世界排除与条带 JJ 单射）。** 对任一 $(C,z,Y)\in\mathcal B_{[3]}\cup\mathcal B_{[4]}$ 和每个 $p\in\mathbb R$，没有两不同世界组成的
$K\subseteq\mathcal F(H_{5J}^{24}(C,z,Y,p))$ 满足 $L_2$。同一历史的实际映射 $\Psi_{JJ}$ 在整个 $\mathcal S_p$ 上为单射；任何完全包含于 $\mathcal S_p$ 的支持均无 $L_2$。

证明。先从 $Z_{67}$ 的父公式取得一个必要平面。定义

$$
\Phi=(652\kappa-560)A+(648\kappa-540)C
+(560-430\kappa)z+(730-1135\kappa)Y.
\tag{12.2}
$$

将式 (10.7) 代入、写回 $b_1,b_2$，有限展开给

$$
\Phi=\frac{10d}7(2\kappa^2+\kappa-2)
\bigl(56b_1b_2-17(b_1+b_2)-120\bigr)=0.
\tag{12.3}
$$

这是对每个合法 $Z_{67}$ 的必要条件，不需要倒置父归一化因子。为给两个完整闭盒上的严格符号，记 $q(x)=2x^2+x-2$。有

$$
q(39/50)=-2/625<0,\qquad
q(781/1000)=461/500000>0,\qquad q'(x)=4x+1>0\quad(x>0),
\tag{12.4}
$$

故 $39/50<\kappa<781/1000$。在这个闭区间及每个闭父盒上，$\Phi$ 对 $\kappa,C,z,Y$ 分别仿射。逐坐标线性插值把每个值写成十六个角值的凸组合。将各坐标端点代入式 (12.2)，得下列有理闭包含；另外两行是其所示仿射式的端点值。

| 必要量 | $\mathcal B_{[3]}$ 上的闭包含 | $\mathcal B_{[4]}$ 上的闭包含 |
| --- | --- | --- |
| $\Phi$ | $[36006/25,385213/200]$ | $[134629249/100000,3385877/2500]$ |
| $R_{15}=35Y-42C+384$ | $[-3081,-3004]$ | $[-5569/25,-22199/100]$ |
| $z-7C/6$ | $[-206/3,-133/2]$ | $[-341/50,-4079/600]$ |

式 (12.4)、两个盒端点及分别仿射的式 (12.2) 唯一指定第一行的全部十六个角值，不需要近似代数根。第一行严格正，与式 (12.3) 冲突，故排除所有 $Z_{67}$。两盒均有 $z>0,z\ne24$，排除要求 $z=A$ 的 $Z_{137}$。第二行严格负，与式 (10.16) 冲突，排除 $Z_{157}$。最后，$Z_{357}$ 需要 $d=z>0$ 及 $b=6-7C/z>0$；第三行给 $z<7C/6$，反而使 $b<0$，故也不合法。四个排除均与 $p$ 无关。

定理 10.3 因而排除所有两世界 $L_2$。定理 11.2 表明条带 JJ 映射的每个非单点纤维都必须是已排除的后三族之一，故该映射在整个条带类上单射。推论 11.3 随即排除任意基数的纯条带支持。∎

**推论 12.3（无限制支持的指定实际叶必须越出条带）。** 在定理 12.2 的任一父及任意 $p$，若
$S\subseteq\mathcal F(H_{5J}^{24})$ 满足 $L_2$，则 $S$ 至少含三个不同完整世界。沿失败递归选择第六 $J$ 的一个实际 $L_1$ 子响应，再选择该节点最终 $J$ 的一个实际 $L_0$ 响应，其叶中至多一个世界属于 $\mathcal S_p$，因而至少一个世界满足

$$
g(7)\ne0\quad\text{或}\quad d<0\quad\text{或}\quad d>21C/11.
\tag{12.5}
$$

证明。空集与单点违反停止守卫；二元素支持由定理 12.2 排除，所以至少三元。所选叶有 $L_0$，含至少两个不同完整世界，并在同一实际 JJ 响应纤维内。该纤维与 $\mathcal S_p$ 的交至多一个，故至少一端在外。此论证也适用于无限支持。∎

式 (12.5) 只约束所指定的实际第六 $J$、最终 $J$ 叶；这里没有为 $JM,MJ,MM$ 证明同样的条带交数界。它也不允许删除混合支持中的条带成员，更不把无限制 $L_2$ 支持缩成一对。

## 13. 固定相同整个增益的纤维界与两种不同增益的必要性

**定理 13.1（相同整个多项式的二世界上界）。** 令 $A>0$，允许 $C,Y,p\in\mathbb R$，但要求 $z\ne A$。对每个固定的非零实多项式 $g$，$\deg g\le3$，有

$$
\left|\{W\in\mathcal F(H_{5J}^A(C,z,Y,p)):
\operatorname{gain}(W)=g\}\right|\le2.
\tag{13.1}
$$

这里等号要求整个多项式完全相同，不只是比例。没有根七或漂移条带假设，源非对角元也未预先有界。

证明。固定 $g$ 后初读给唯一 $d=-g(0)$。若 $g(1),g(3),g(5)$ 全零，则第一、第三读均等于 $d$，即 $z=A$，与假设冲突。所以至少一个奇样本非零。

若 $g(2)$ 或 $g(4)$ 非零，相应偶读唯一固定 $b$。任选一个非零奇样本 $g(2m+1)$，$m\in\{0,1,2\}$，令 $L=(a_m-d)/g(2m+1)$，其中 $(a_0,a_1,a_2)=(A,z,p)$。该行给 $j+mr=L$，与 $c=r(1-r)/b$ 合用得

$$
r^2-(1+mb)r+b(L-b)=0.
\tag{13.2}
$$

首项系数为一，至多两个不同实根。每个合法根固定 $c$，其余所有实际行及严格源条件只删候选。因此此支至多两个完整世界，包含二次式重根时的单世界情形。

若 $g(2)=g(4)=0$，非零且次数至多三使三个奇样本至多一个为零，否则有四个不同根。于是至少两个非零奇样本用式 (11.7) 固定 $j,r$。源条件剩下

$$
b^2-jb+r(1-r)=0,\qquad c=j-b,
\tag{13.3}
$$

故同样至多两个合法 $b$。每个给唯一源和同一个固定 $g,d$。两个分支穷尽所有情况，只在样本已声明非零时才相除，全部剩余原行始终保留。∎

$z\ne A$ 不能无条件删去。例如对任意 $A>0$ 及固定 $b>0$，取

$$
g(v)=\frac A{15}(v-1)(v-3)(v-5),\quad d=A,\quad
C=\frac{A(6+b)}5,\quad Y=\frac{A(4-2b)}5,\quad z=p=A.
\tag{13.4}
$$

对每个 $r\in(0,1)$，令 $c=r(1-r)/b$，都给严格合法源及同一个实际第五 J 历史。奇样本全零，偶样本只固定 $b$，因此这是同一个整个增益下的无限源纤维。此例说明守卫的作用，不主张它在第 12 节的父上实现失败。

**推论 13.2（两个父上的失败必须用不同整个增益）。** 对第 12 节任一父及任意 $p$，若无限制支持
$S\subseteq\mathcal F(H_{5J}^{24})$ 满足 $L_2$，则其中至少有两个不同的整个增益多项式。

证明。两盒均有 $z\ne24$。若 $S$ 的世界全使用一个相同的整个 $g$，定理 13.1 给 $|S|\le2$。停止守卫排除零或一，定理 12.2 排除二，所以无 $L_2$，矛盾。∎

这一必要性区分相同多项式与比例方向：$g_1\ne g_2$ 仍可能有 $g_2=\lambda g_1$，$\lambda\ne1$。固定 $g$ 时初读固定漂移的证明不能用于固定方向而尺度可变的类。因此推论 13.2 不声称两个非比例方向或增益线性跨度至少二。

## 14. 量词增量、文献关系与同父余项

根卷定理 21.3 已在 $A=24,C=48$ 的切片分类第五 J 二世界 $L_2$。前卷引理 2.1 提供自由父的双末根线性核，引理 2.3 提供正源曲线及比例窗口排除；本卷第 2 节和前卷第 9–10 节已提供四节点插值与完整源逆。定理 10.3 复用这些工具，新增的是 $A>0,C>0$ 独立变化时四个合法族的完整充要关系及其严格过滤。把整个增益和漂移同乘一个非零常数会同比缩放 $A,C$，保持 $C/A$；故固定 $C=2A$ 的结果不能仅靠缩放给出自由 $C$。

特别，$Z_{137}$、$Z_{157}$ 的两合法根域分别给

$$
\frac CA=\frac{26+5b}{21}<2\quad(0<b<1/2),\qquad
\frac CA=\frac{10+3b}7<2\quad(0<b<1),
\tag{14.1}
$$

这些合法分支不在旧比例切片内。$Z_{67}$ 所用曲线是既有曲线；其在自由父分类中的位置与必要父平面 (12.2) 承担这里的应用。前卷第 8 节的完整二世界定理是第五 $M$ 分类，与本节第五 $J$ 的实际第五行不同。第 7、8 节两个第五 $M$ 见证仍是各自父上的既有实现。

第 11 节进一步对整个 $\mathcal S_p$ 求实际 JJ 纤维，包含空、单点及两点情况；这不同于只列出两世界失败对。第 12 节把分类与整个纤维界用于两个完整闭父盒，排除每个实第五 J 响应上的二世界失败，并给指定实际 JJ 叶的越界约束。第 13 节的固定相同整个增益界使“至少两种不同多项式”成为无限制支持的必要条件。这些是现有模型中的综合推导及量词扩大，不将标准插值、根数界、二次式或差商判单调另计为独立新定理。

有关文献的数学对应如下。Berrut–Trefethen，《[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)》§2 提供普通节点插值；此处只用互异固定节点的多项式唯一性。Kech–Krahmer，《[Optimal Injectivity Conditions for Bilinear Inverse Problems with Applications to Identifiability of Deconvolution Problems](https://arxiv.org/html/1603.07316)》§II、命题 IV.3 用提升后的测量核与可实现差集讨论单射。其复数域、尺度商和泛型测量结论不能直接给出固定 $J/M$ 产品、实正秩一源及常漂移下的四族分类。

Li–Lee–Bresler，《[A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models](https://arxiv.org/html/1501.06120)》定理 2.8 区分因子识别与固定一因子后的识别，推论 3.4 的结论针对泛型复子空间及快照条件。这里固定整个 $g$ 后仍保留全部源和原行，且实际目标为整个 $(P,g,d)$，不取比例商。Ling–Strohmer，《[Self-Calibration and Bilinear Inverse Problems via Linear Least Squares](https://arxiv.org/html/1611.04196)》§2.2 将校准对角矩阵假设为可逆，其三类设计涉及重复测量、不同输入或多个快照。本卷必须保留增益采样零，也不能取得额外实验，故这些结果不提供这里所需的无零样本假设或额外共同历史。上述论文的这些结论均不是定理 10.3、11.2、12.2 或 13.1 的直接替代。本卷的具体增量是仓内推导，不主张全球原创性、优先权或文献穷尽。

这里的结论具有普通数学证明与所列有限有理证书的证据范围，不声称 Lean/kernel 形式化。所有条件类均保留原非零至多三次整个增益、严格正迹一秩一实源、固定实漂移、原时钟与实际非重置历史；未用局部 $D\ne0$ 图删除任何世界。分类中推出精确三次不缩小其他定理及原恢复问题的域。

对每个精确父 $H_4^{[3]}$、$H_4^{[4]}$，新的必要条件同时要求：任何第五 J 的 $L_2$ 支持至少三世界、至少两种不同整个增益，并在其所需实际第六 J／最终 J 碰撞叶中出现式 (12.5) 的类外世界。因而单个精确失败对、单一相同整个增益，或完全限于根七漂移条带的方案都不能补齐缺失臂。这些限制没有给出符合它们的同父方案，也没有排除全部较大支持。

仍需在同一个父、同一个实际第五 J 响应 $p_J$ 下，同时取得第六 J 与 M 的失败子节点；每个子节点的两个最终动作必须共享该节点已获的同一个第六响应，允许使用不同终端碰撞对，并满足各层非单点停止守卫。精确二世界分类没有把任意支持化为一对。两个父仍不同，不能互相拼接，第五 J 响应也不能用第五 M 的响应替代。第 8 节局部实现族仍未证明父映射满秩，闭盒排除没有补上盒内第五 M 的统一可行性。

所以较大支持的同父第五 J $L_2$、父上的完整 $L_3$、更早互择祖先与原根 $L_7$ 均未决定；无限制自适应八读恢复或不可能性、八读与九读比较及完整原域的九读充分性也未决定。原策略始终可为任意确定性历史依赖函数，不附连续、可测、可计算或有限描述条件。条带结果不向 $g(7)\ne0$、$d<0$ 或 $d>21C/11$ 外推，也不向其他实际终端词外推；固定整个增益界不向比例增益类外推。这些未解范围与定义 1.3 的原完成判据一致。

## 追加锚（本行以下为增补区）

## 15. Exact-gain fifth-J supports and the three-to-four transition

**Definition 15.1 (A width-dependent exact parent).** In the original domain of Definition 1.1, fix $\beta>0$ and put

$$
\begin{gathered}
h(s)=\frac85(s-1)(s-3)(s-5),\qquad
P_\beta(r)=\begin{pmatrix}r&\beta\\r(1-r)/\beta&1-r\end{pmatrix},\\
W_\beta(r)=(P_\beta(r),h,24),\qquad
K_\beta=\{W_\beta(r):0<r<1\},\\
C_\beta=24+\frac{24}{5}(1+\beta),\qquad
Y_\beta=24-\frac{24}{5}(1+2\beta),\\
H_{4,\beta}=(0,J,24,M,C_\beta,J,24,M,Y_\beta),\qquad
H_{5,\beta}^F=(H_{4,\beta},F,24)\quad(F=J,M).
\end{gathered}
\tag{15.1}
$$

For $S\subseteq(0,1)$ write $K_\beta(S)=\{W_\beta(r):r\in S\}$. Equality $g=h$ below means equality of entire polynomials, including scale. It does not mean a gain direction. The coordinates and the gain at $\beta=4$ occur in the root volume, §23, equations (23.4)–(23.6), (23.15)–(23.18). Here each width has its own exact parent; the support question concerns this family of parents.

**Theorem 15.2 (Entire exact-gain slice and sharp support sizes).** The entire slice of $\mathcal F(H_{4,\beta})$ with $g=h$ is $K_\beta$. Both fifth actions have response $24$ throughout this slice; every other fifth-response slice with $g=h$ is empty. For every finite or infinite $S\subseteq(0,1)$,

$$
\begin{aligned}
L_2(K_\beta(S),H_{5,\beta}^J)\quad\Longleftrightarrow\quad
\bigwedge_{m=1}^3\ \exists r,t\in S:
\ r\ne t,\quad r+t=1+m\beta.
\end{aligned}
\tag{15.2}
$$

Consequently $L_2(K_\beta,H_{5,\beta}^J)$ holds exactly when $0<\beta<1/3$. The minimum size of a finite $L_2$ support **inside $K_\beta$** is three for $0<\beta<1/4$ and four for $1/4\le\beta<1/3$. Every three-world support has the parameter set

$$
\left\{\frac12,\frac12+\beta,\frac12+2\beta\right\}.
\tag{15.3}
$$

For $\beta\ge1/3$, no subset of $K_\beta$, of any cardinality, has this $L_2$ property.

Proof. All entries of $P_\beta(r)$ are positive, its trace is one and its determinant is zero. Its nonzero trace makes its rank exactly one. Different $r$ give different sources and complete worlds. The single entire gain has samples

$$
(h(0),\ldots,h(7))=
\left(-24,0,\frac{24}{5},0,-\frac{24}{5},0,24,\frac{384}{5}\right).
\tag{15.4}
$$

The prefix traces in (10.3) are $1,j,1+\beta,j+r,1+2\beta$. Thus these worlds realize exactly $H_{4,\beta}$ and both fifth responses are $24$. Conversely, $g=h$ and the initial response force $d=24$. Clock two then gives
$C_\beta=24+(24/5)(1+b)$, so $b=\beta$. Strict source legality forces $0<r<1$ and $c=r(1-r)/\beta$. This proves the entire-slice identity without a hidden source restriction.

Set

$$
q_m(r)=\beta+\frac{r(1-r)}\beta+mr,\qquad V_k=1+k\beta.
\tag{15.5}
$$

By the actual left products (10.4), $k=2$ denotes sixth $J$, and $k=3$ denotes sixth $M$. The acquired response and the two alternative terminal responses on the same fixed world are

$$
v_k=24+24V_k,\qquad
f_{kJ}(r)=24+\frac{384}{5}q_k(r),\qquad
f_{kM}(r)=24+\frac{384}{5}\bigl(V_k+q_{k-1}(r)\bigr).
\tag{15.6}
$$

Each acquired sixth slice retains all of $K_\beta(S)$. For distinct $r,t$ the exact difference is

$$
q_m(r)-q_m(t)=\frac{(r-t)(1+m\beta-r-t)}\beta.
\tag{15.7}
$$

Call the equation $r+t=1+m\beta$ color $m$. Sixth $J$ requires colors $2,1$ for its final $J,M$ leaves; sixth $M$ requires colors $3,2$. An $L_2$ support must therefore contain a distinct pair of each of colors $1,2,3$. Conversely these pairs supply both $L_0$ leaves inside the single acquired $v_k$ child for each $k$. Each sixth child contains a distinct pair and has both terminal clauses, hence $L_1$; the common fifth node contains them and has $L_2$. All non-singleton guards hold. The color-two pair may serve both sixth blocks. No alternative response has been acquired on an already chosen trajectory. This proves (15.2), including empty and singleton failures.

Color three requires $r+t=1+3\beta<2$, which is impossible for $\beta\ge1/3$. At equality the forbidden boundary $r=t=1$ cannot be made legal. For $0<\beta<1/4$, the three points (15.3) are legal and their three pairs have colors $1,2,3$. A single pair cannot have two colors because $\beta>0$, so two worlds never suffice. If three ordered points $x<y<z$ work, their three strictly ordered sums must satisfy

$$
x+y=1+\beta,\qquad x+z=1+2\beta,\qquad y+z=1+3\beta.
\tag{15.8}
$$

Solving gives (15.3). Its largest point is strictly below one exactly for $\beta<1/4$; at $\beta=1/4$ it is not legal.

For $0<\beta<1/3$ another support is given by the set of the four values

$$
a=\frac{1+5\beta}{4},\quad
b_*=\frac{3-\beta}{4},\quad
c_*=\frac{1+9\beta}{4},\quad
e=\frac{3+3\beta}{4}.
\tag{15.9}
$$

These are source parameters $r$, not matrix entries. All lie in $(0,1)$, and
$a+b_*=1+\beta$, $a+e=1+2\beta$, $c_*+e=1+3\beta$. Each selected pair is distinct: $b_*-a=e-c_*=(1-3\beta)/2>0$ and $e-a=(1-\beta)/2>0$. Thus they give at most four worlds. In $1/4\le\beta<1/3$ all four are distinct, since $c_*-a=e-b_*=\beta$ and $c_*-b_*=(5\beta-1)/2>0$. The impossibility of three proves the four-world minimum. At $\beta=1/4$ this set is $\{9/16,11/16,13/16,15/16\}$. Below that range, the possible coincidence $b_*=c_*$ at $\beta=1/5$ simply gives three worlds. ∎

**Theorem 15.3 (An exact rational actual $L_2$).** Take $\beta=1/8$ and the three complete worlds with the common $g=h,d=24$ and sources

$$
P_0=\begin{pmatrix}1/2&1/8\\2&1/2\end{pmatrix},\quad
P_1=\begin{pmatrix}5/8&1/8\\15/8&3/8\end{pmatrix},\quad
P_2=\begin{pmatrix}3/4&1/8\\3/2&1/4\end{pmatrix}.
\tag{15.10}
$$

Their common fifth-J history is
$H_{5,1/8}^J=(0,J,24,M,147/5,J,24,M,18,J,24)$.
Writing $K=\{W_0,W_1,W_2\}$, one has $L_2(K,H_{5,1/8}^J)$.

Proof. Each displayed source is strictly positive, trace one and determinant zero. Use the one polynomial
$h(s)=-24+(184/5)s-(72/5)s^2+(8/5)s^3$ throughout. The following are exact response functions of these predetermined worlds. The fifth-M continuations are included to distinguish the two actual fifth choices.

| Time word | $y(W_0)$ | $y(W_1)$ | $y(W_2)$ |
| --- | --- | --- | --- |
| empty, clock $0$ | $0$ | $0$ | $0$ |
| $J$ | $24$ | $24$ | $24$ |
| $JM$ | $147/5$ | $147/5$ | $147/5$ |
| $JMJ$ | $24$ | $24$ | $24$ |
| $JMJM$ | $18$ | $18$ | $18$ |
| $JMJMJ$ | $24$ | $24$ | $24$ |
| $JMJMJJ$ | $54$ | $54$ | $54$ |
| $JMJMJM$ | $57$ | $57$ | $57$ |
| $JMJMJJJ$ | $264$ | $1368/5$ | $264$ |
| $JMJMJJM$ | $1608/5$ | $1608/5$ | $1512/5$ |
| $JMJMJMJ$ | $1512/5$ | $1608/5$ | $1608/5$ |
| $JMJMJMM$ | $1848/5$ | $1896/5$ | $1848/5$ |
| $JMJMM$ | $24$ | $24$ | $24$ |
| $JMJMMJ$ | $126$ | $129$ | $126$ |
| $JMJMMM$ | $147$ | $147$ | $141$ |
| $JMJMMJJ$ | $1608/5$ | $1608/5$ | $1512/5$ |
| $JMJMMJM$ | $1896/5$ | $1848/5$ | $1704/5$ |
| $JMJMMMJ$ | $2952/5$ | $3048/5$ | $2952/5$ |
| $JMJMMMM$ | $3576/5$ | $3576/5$ | $3384/5$ |

The fifth-J rows follow from (10.4), equivalently (15.6); the fifth-M rows follow from the literal products in Table 6.1. At the acquired sixth-J response $54$, final $J$ uses $(W_0,W_2)$ at $264$ and final $M$ uses $(W_0,W_1)$ at $1608/5$. At the acquired sixth-M response $57$, final $J$ uses $(W_1,W_2)$ at $1608/5$ and final $M$ uses $(W_0,W_2)$ at $1848/5$. Both sixth slices retain all three worlds. Each terminal leaf retains its displayed distinct pair, so every $L_0$, $L_1$ and $L_2$ guard holds. The initial read is counted and the terminal clock remains seven. ∎

**Theorem 15.4 (Failure of the entire exact-gain M arm).** For every $\beta>0$ and every $S\subseteq(0,1)$,

$$
\neg L_2(K_\beta(S),H_{5,\beta}^M),\qquad
\neg L_3(K_\beta,H_{4,\beta}).
\tag{15.11}
$$

These statements concern the exact-$h$ slice. They impose no nonexistence conclusion on the unrestricted M arm or unrestricted parent.

Proof. After fifth $M$, sixth $J$ has matrix $\left(\begin{smallmatrix}3&1\\2&1\end{smallmatrix}\right)$ and trace $1+\beta+q_2(r)$; the following final $J$ has matrix $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ and trace $1+2\beta+q_1(r)$. If their actual responses are $u,f$, then

$$
u=24+24(1+\beta+q_2(r)),\quad
f=24+\frac{384}{5}(1+2\beta+q_1(r)),\quad
r=\beta+\frac{u-24}{24}-\frac5{384}(f-24).
\tag{15.12}
$$

Here $q_2-q_1=r$. Thus the joint map is injective on the entire $K_\beta$. Once $u$ has been acquired, every final-J leaf is empty or a singleton, even after restricting to a subset. No sixth-J child has $L_1$, and the corresponding conjunct of fifth-M $L_2$ fails. Other fifth responses give empty slices by Theorem 15.2. Hence no M choice can supply the M conjunct of parent $L_3$ in $K_\beta$. ∎

## 16. A zero-safe atlas of complete seven-read children

**Definition 16.1 (Even-node coordinates).** In this section $A,C,z,Y,p,v$ are arbitrary real numbers. The notation

$$
H_4^A=(0,J,A,M,C,J,z,M,Y),\quad H_{5J}^A=(H_4^A,J,p),\quad
H_6^E=(H_{5J}^A,E,v)
\tag{16.1}
$$

extends the same literal histories to arbitrary $A$, without changing the positive-$A$ assumptions of §§10–14. There are seven readings at clocks $0,\ldots,6$. Fix $E\in\{J,M\}$ and $b>0$, and write

$$
\begin{gathered}
T=1+b,\quad U=1+2b,\quad
k=\begin{cases}2&E=J,\\3&E=M,\end{cases}\quad V=1+kb,\quad K=16TUV>0,\\
B_0=-dTUV,\quad B_2=(C-d)UV,\quad
B_4=(Y-d)TV,\quad B_6=(v-d)TU,\\
\begin{pmatrix}G_1\\G_3\\G_5\\G_7\end{pmatrix}
=\begin{pmatrix}
5&15&-5&1\\-1&9&9&-1\\1&-5&15&5\\-5&21&-35&35
\end{pmatrix}
\begin{pmatrix}B_0\\B_2\\B_4\\B_6\end{pmatrix},\\
H_E(b,d)=(A-d)G_3G_5-2(z-d)G_1G_5+(p-d)G_1G_3.
\end{gathered}
\tag{16.2}
$$

Here $K$ is an interpolation denominator, not a world set. The $G_i$ are affine polynomials in $d$ for each fixed $b$ and observations. For $i\in\{0,2,4,6\}$ let
$\ell_i^{\rm ev}(s)=\prod_{a\in\{0,2,4,6\}\setminus\{i\}}(s-a)/(i-a)$.
Define

$$
g_{b,d}(s)=-d\ell_0^{\rm ev}(s)
+\frac{C-d}{T}\ell_2^{\rm ev}(s)
+\frac{Y-d}{U}\ell_4^{\rm ev}(s)
+\frac{v-d}{V}\ell_6^{\rm ev}(s).
\tag{16.3}
$$

**Theorem 16.2 (Complete-world bijection and genuine drift cubics).** For each fixed $E,b$ and all the observations in Definition 16.1, retain exactly the real triples $(d,j,r)$ satisfying

$$
\begin{gathered}
H_E(b,d)=0,\qquad 0<r<1,\qquad j>b,\qquad
b(j-b)=r(1-r),\qquad g_{b,d}\ne0,\\
G_1j=K(A-d),\qquad G_3(j+r)=K(z-d),\qquad
G_5(j+2r)=K(p-d).
\end{gathered}
\tag{16.4}
$$

The map

$$
(d,j,r)\longmapsto
\left(\begin{pmatrix}r&b\\j-b&1-r\end{pmatrix},g_{b,d},d\right)
\tag{16.5}
$$

is a bijection onto all complete worlds at that $b$ in $\mathcal F(H_6^E)$. Its union over **all** $b>0$ is the entire child. The nonzero-polynomial filter is automatic if $A=24$ or if $z\ne A$; it remains part of the statement for arbitrary $A$.

The polynomial $H_E(b,d)$ is exactly cubic in $d$, for every choice of the real observations. Its leading coefficient is

$$
\begin{aligned}
L_J(b)&=16b(1+2b)^2(4b^3+16b^2+5b+8)>0,\\
L_M(b)&=192b^4(3b^2+12b+4)>0.
\end{aligned}
\tag{16.6}
$$

Proof. The actual even traces at clocks $0,2,4,6$ are $1,T,U,V$, and the odd traces at $1,3,5$ are $j,j+r,j+2r$. Four distinct even nodes determine every degree-at-most-three polynomial, including all degree drops. They force (16.3). Evaluating their Lagrange basis at $1,3,5,7$ gives exactly the matrix in (16.2), divided by $16$, and therefore $g(i)=G_i/K$.

With

$$
R_1=G_1j-K(A-d),\quad
R_3=G_3(j+r)-K(z-d),\quad
R_5=G_5(j+2r)-K(p-d),
$$

the polynomial identity

$$
R_1G_3G_5-2R_3G_1G_5+R_5G_1G_3=-KH_E
\tag{16.7}
$$

follows from $j-2(j+r)+(j+2r)=0$. It uses no division by an odd sample. Let $\alpha_i=[d]G_i$. Direct substitution of the four $B_i$ gives

$$
\begin{array}{c|cc}
&E=J&E=M\\ \hline
\alpha_1&-(2b+1)(10b^2+41b+16)&-2(5b+2)(3b^2+12b+4)\\
\alpha_3&(2b+1)(2b^2-23b-16)&2(3b+2)(b^2-12b-4)\\
\alpha_5&-(2b+1)(2b^2+13b+16)&-2(b+2)(3b^2+12b+4)\\
\alpha_7&(2b+1)^2(5b-16)&2(b-2)(15b^2+12b+4).
\end{array}
\tag{16.8}
$$

The coefficient of $d^3$ in $H_E$ is

$$
-\alpha_3\alpha_5+2\alpha_1\alpha_5-\alpha_1\alpha_3=L_E(b).
\tag{16.9}
$$

Expansion and factorization give (16.6); every factor is positive for every $b>0$, with no upper bound on $b$.

Every original world yields (16.4) by its seven rows, (16.7), and source legality. Conversely, a retained triple has $c=j-b>0$, trace-one source, zero determinant, and strictly positive entries, hence rank exactly one. Equation (16.3) gives its four even rows, and (16.4) gives all three odd rows. The entire interpolant is nonzero and has degree at most three. This is exactly one original world, and its $b,d,j,r$ recover the tuple uniquely. If $g=0$, all observed responses equal $d$; the initial response makes $d=0$. Thus $A=24$ or $z\ne A$ excludes it, whereas arbitrary-$A$ reconstruction must keep the filter.

When $G_1=G_3=G_5=0$, the odd equations require exactly $A=z=p=d$. If the other filters hold, every $0<r<1$ with $j=b+r(1-r)/b$ remains admissible. In particular this stratum is retained at $A=24$ when its even data give a nonzero interpolant. If only some $G_i$ vanish, each corresponding response must equal $d$; there is no artificial source equation from that row. No gain sign, repeated root, sampled zero, nonsampled root, degree drop, zero drift, or zero of an earlier local inverse denominator $D$ has been discarded. All divisions in the atlas use only $T,U,V$ and fixed node differences. ∎

**Theorem 16.3 (At most three complete worlds per fixed $b$).** Suppose $z\ne A$. For each $E$, each fixed set of observations, and each fixed $b>0$, the child in Theorem 16.2 contains at most three distinct complete worlds. This is a bound at one $b$, with source multiplicity included; it is not a global bound on the union over $b$.

Proof. The genuine cubic $H_E$ has total real-root multiplicity at most three. At a retained drift root, $G_1,G_3$ cannot both vanish, because their rows would give $d=A=z$. If at least two of $G_1,G_3,G_5$ are nonzero, the corresponding two independent affine traces $j+mr$, with $m=0,1,2$, fix at most one $(j,r)$. The even data have already fixed the entire gain. This drift therefore gives at most one complete world.

If only $G_1$ is nonzero, $d=z=p$ and $j=K(A-d)/G_1$ are fixed; sources solve

$$
r^2-r+b(j-b)=0.
\tag{16.10}
$$

There are at most two distinct legal roots. At this $d_0=z=p$, both $G_3,G_5$ vanish. Writing $x=d-d_0$, each term of $H_E$ contains $x^2$: respectively $G_3G_5$, $(z-d)G_5$, and $(p-d)G_3$ supply the factors. Hence $d_0$ is a drift root of multiplicity at least two.

If only $G_3$ is nonzero, then $d=A=p$, and $n=j+r=K(z-d)/G_3$ is fixed. The source equation is

$$
r^2-(1+b)r+b(n-b)=0.
\tag{16.11}
$$

Again there are at most two legal roots. At $d_0=A=p$, $G_1,G_5$ vanish, and the three terms of $H_E$ contain respectively $(A-d)G_5$, $G_1G_5$, and $(p-d)G_1$, hence each has two factors $x$. A $G_5$-only or all-zero case is impossible under $z\ne A$.

Thus at every retained drift root the number of complete worlds is at most its root multiplicity. Summing gives three. Repeated quadratic roots count once; repeated drift roots, sampled gain zeros and degree drops have been included. Counting only distinct drift roots would not prove this complete-world bound. ∎

**Theorem 16.4 (Necessary filters and a boundary infinite fiber).** The cubic equation alone does not certify a world. Also the restriction $z\ne A$ in Theorem 16.3 cannot simply be removed.

Proof. For either $E$, take $b=1$, $A=24$, $C=z=Y=p=v=0$ and $d=0$. All $B_i,G_i$ and $H_E$ vanish, but the first odd equation reads $0=24K$, which is impossible.

For the second assertion take $b=1$, $A=z=p=24$, $C=168/5$, $Y=48/5$ and $v=96$ for $E=J$ or $v=120$ for $E=M$. For every $0<r<1$ use $P_1(r)$, $g=h$, $d=24$ from Definition 15.1. Equation (15.4) has all three early odd samples zero. Its even rows give exactly these $C,Y,v$. The gain is nonzero and all sources are legal and distinct. Thus this is an infinite complete-world child at fixed $b$ when $z=A$. ∎

**Theorem 16.5 (Same-source injectivity and the guarded common-child interface).** In each actual child $\mathcal F(H_6^E)$, including $z=A$ and arbitrary $A$, equal source matrices imply equal complete worlds. For its atlas world the two terminal response functions are

$$
f_{EJ}=d+\frac{G_7}{K}(j+kr),\qquad
f_{EM}=d+\frac{G_7}{K}\bigl(V+j+(k-1)r\bigr).
\tag{16.12}
$$

Fix one fourth parent, one fifth-J response $p$, and a prescribed finite or infinite $\mathcal K\subseteq\mathcal F(H_4^A)$. Let $\mathcal A_E(p,v)$ denote the atlas union over all $b>0$ at that literal child, restricted to $\mathcal K$. Then

$$
\begin{aligned}
&L_2\bigl(\mathcal K\cap\mathcal F(H_{5J}^A),H_{5J}^A\bigr)\\
&\quad\Longleftrightarrow\quad
\bigwedge_{E\in\{J,M\}}\exists v_E\in\mathbb R\
\bigwedge_{G\in\{J,M\}}\exists W_{EG0},W_{EG1}\in\mathcal A_E(p,v_E):\\
&\hspace{40mm}(r_{EG0}-r_{EG1})^2+(b_{EG0}-b_{EG1})^2>0,\\
&\hspace{40mm}f_{EG}(W_{EG0})=f_{EG}(W_{EG1}).
\end{aligned}
\tag{16.13}
$$

At a parent whose fifth-M arm already has an actual $L_2$ response, existence of a $p$ satisfying (16.13) for the full parent fiber is equivalent to $L_3$ there. In particular this conditional equivalence applies separately to $H_4^{[3]}$ and $H_4^{[4]}$.

Proof. Suppose two worlds in one child have the same $P$, hence the same $b,j,r$. If their drifts coincide, their four even gain samples coincide, so their entire polynomials coincide. Otherwise subtract their three odd equations and divide by their nonzero drift difference. Since the $G_i$ are affine in $d$, this gives

$$
\alpha_1j=-K,\qquad \alpha_3(j+r)=-K,\qquad
\alpha_5(j+2r)=-K.
\tag{16.14}
$$

Multiply these equations respectively by $\alpha_3\alpha_5$, $-2\alpha_1\alpha_5$, $\alpha_1\alpha_3$ and add. The left side is zero; the right side is $KL_E(b)>0$ by (16.6), (16.9), a contradiction. No $\alpha_i$ or gain sample was divided out. Hence complete-world distinction in this child is equivalent to source distinction, which is exactly the strict squared-coordinate condition in (16.13). This equivalence is justified for these actual children, rather than substituted for the complete-world guard at arbitrary histories.

Formula (16.12) follows from (10.4) and $g(7)=G_7/K$. If $G_7=0$, both terminal functions correctly equal $d$. They are alternatives on the same fixed world.

For necessity in (16.13), the recursive definition first selects $v_E$ under the already fixed $p$, then selects a terminal response for each $G$, and only in that actual $L_0$ leaf selects two distinct complete worlds. The atlas contains exactly those worlds. Same-source injectivity supplies the strict source condition.

For sufficiency fix all selected complete worlds first and take their finite union. For each $E,G$ its pair lies in a single terminal leaf. Both pairs for that $E$ share the acquired $v_E$, so they provide the two terminal clauses and the non-singleton guard of $L_1$. The two sixth children share $p$ and give $L_2$ with its guard. Every used ancestor contains a distinct descendant pair. Containment in a larger compatible set preserves $L_s$ by induction on its defining recursion, so extra worlds and infinite $\mathcal K$ cause no problem.

Finally, a realized M arm and the J system at the **same** fourth parent supply the two fifth clauses of $L_3$; the converse follows from the same recursion. Fifth responses for different actions may differ. Different terminal slots may use different $b,g,d$, but every slot is one complete fixed triple satisfying all its acquired and alternative rows. Refitting a world's gain or drift between rows is not allowed. At the two inherited parents $z\ne24$, so Theorem 16.3 also applies at each fixed $b$. Neither the cubic nor the interface proves existence of any missing pair. ∎

## 17. Whole proportional-gain containment of an actual sixth-J child

**Definition 17.1 (An entire gain direction).** For a nonzero real polynomial $h$ of degree at most three, its direction is
$[h]=\{\lambda h:\lambda\in\mathbb R\setminus\{0\}\}$.
Fix a literal $H_{5J}^A$ as in (16.1), and put

$$
\mathcal S_h=\{(P,g,d)\in\mathcal F(H_{5J}^A):g\in[h]\},\qquad
u_J(W)=d+g(6)(1+2b).
\tag{17.1}
$$

For $\mathcal K\subseteq\mathcal S_h$ let $\mathcal K_u=\{W\in\mathcal K:u_J(W)=u\}$. Both signs of the nonzero proportionality factor are initially allowed. The symbol $[g]$ is an external mathematical label, not an acquired observation. Set

$$
F_0=14C+35Y-48z,\qquad F_1=35Y-42C+16A.
\tag{17.2}
$$

The second residual agrees with (10.16); neither residual is the source-chart denominator $D$.

**Theorem 17.2 (All-support containment collapse).** Assume

$$
AzCY\ne0,\qquad z\ne A,\qquad C\ne Y.
\tag{17.3}
$$

For every direction $h$, every finite or infinite $\mathcal K\subseteq\mathcal S_h$ and every $u$, if the actual sixth-J child $\mathcal K_u$ has $L_1$, then

$$
\mathcal S_h=\mathcal K=\mathcal K_u=\{W_-,W_+\},
\tag{17.4}
$$

where the two worlds have the same entire gain and drift and are of one of the following forms:

$$
\begin{array}{c|c|c}
&\text{root family }157&\text{root family }357\\ \hline
g(s)&\dfrac A{35}(s-1)(s-5)(s-7)&
\dfrac z{105}(s-3)(s-5)(s-7)\\
d,\ p&A,\ A&z,\ z\\
C&A(10+3b)/7&z(6-b)/7\\
Y&A(44+18b)/35&z(36+2b)/35\\
\text{fixed odd trace}&n=j+r=35(z-A)/(16A)&j=35(z-A)/(16z)\\
\text{source equation}&r^2-(1+b)r+b(n-b)=0&r^2-r+b(j-b)=0\\
\text{forced residual}&F_1=0&F_0=0.
\end{array}
\tag{17.5}
$$

In each column the two roots must be distinct and satisfy every strict source condition and every prefix row. The resulting pair itself has $L_2$ at the fifth-J history. In particular, if additionally $F_0F_1\ne0$, no direction-contained actual sixth-J child has $L_1$, and no direction-contained fifth-J support has $L_2$.

Proof. First consider the regular odd branch $h(1)h(3)\ne0$. Write $h_i=h(i)$ and $g=h/t$, $t\ne0$. The initial, first and third rows force

$$
d(t)=-h_0/t,\qquad
j(t)=\frac{h_0+At}{h_1},\qquad
r(t)=\frac{h_0+zt}{h_3}-j(t).
\tag{17.6}
$$

At least one of $h_2,h_4$ is nonzero, for otherwise $C=Y=d$. If $h_2\ne0$ use
$b(t)=(h_0+Ct)/h_2-1$; otherwise use
$b(t)=((h_0+Yt)/h_4-1)/2$. Put $c(t)=j(t)-b(t)$. Retain exactly the nonzero real $t$ with

$$
\begin{gathered}
0<r(t)<1,\quad b(t),c(t)>0,\quad
r(t)(1-r(t))=b(t)c(t),\\
h_2(1+b(t))-h_0=Ct,\qquad
h_4(1+2b(t))-h_0=Yt,\\
h_5(j(t)+2r(t))-h_0=pt.
\end{gathered}
\tag{17.7}
$$

One even row was used to define $b$; both are still displayed as filters. These equations give a bijection between retained $t$ and $\mathcal S_h$. Thus they are a converse reconstruction, not just necessary projected equations. The source is affine, $P(t)=P_0+tV_0$, and any fixed continuation matrix $Q$ at clock $a$ has response

$$
h_a\operatorname{tr}(QV_0)
+\frac{h_a\operatorname{tr}(QP_0)-h_0}{t}.
\tag{17.8}
$$

On an arbitrary subset of nonzero real $t$ this function is constant if its reciprocal coefficient is zero, and otherwise injective. If $\mathcal K_u$ had $L_1$, each terminal action would have a collision between distinct $t$. The two collisions may use different pairs, but (17.8) forces each of the two terminal functions to be constant on the entire class. Choosing any distinct pair in $\mathcal K_u$ would then give scale-changing proportional worlds sharing the acquired $u$ and both terminal responses.

Such a pair is impossible, as follows. Suppose $g_2=\mu g_1$, $\mu\ne0,1$, and write $g=g_1$. Initial response gives $d_2=\mu d_1$ and $d_1=-g(0)$. Put $D_*=P_1-\mu P_2$. Every shared row says

$$
g(a)\operatorname{tr}(Q_aD_*)=g(0)(1-\mu).
\tag{17.9}
$$

If $g(0)=0$, both drifts are zero. Since $C,Y\ne0$, the clock-two and clock-four samples are nonzero. Their equations give
$(1-\mu)+(D_*)_{12}=0$ and $(1-\mu)+2(D_*)_{12}=0$, a contradiction. Thus $g(0)\ne0$. Define $Z=D_* /(1-\mu)$ and $q=g/g(0)$. Then $\operatorname{tr}Z=1$ and
$q(a)\operatorname{tr}(Q_aZ)=1$ at every used row, so every divided $q(a)$ is nonzero.

Repeated matrices $Q_4=Q_{6J}$ and $Q_{5J}=Q_{7JJ}$ force $q(4)=q(6)$ and $q(5)=q(7)$. The two constraints on a cubic with $q(0)=1$ give

$$
q(s)=1+a\left(s^3-\frac{33}{2}s^2+89s\right).
\tag{17.10}
$$

Its samples at $1,\ldots,7$ are

$$
\left(1+\frac{147a}{2},1+120a,1+\frac{291a}{2},
1+156a,1+\frac{315a}{2},1+156a,1+\frac{315a}{2}\right).
\tag{17.11}
$$

Writing $B=Z_{12},R=Z_{11}$, the even equations yield
$1+B=1/q(2)$ and $1+2B=1/q(4)$. Equality of both terminal traces gives $R=1+2B$, whereas the early odd rows give $R=1/q(3)-1/q(1)$. Therefore both polynomials

$$
\begin{aligned}
\mathcal G(a)&=2q(4)-q(2)-q(2)q(4)
=-12a(7+1560a),\\
\mathcal H(a)&=q(4)(q(1)-q(3))-q(1)q(3)
=-1-291a-\frac{87705}{4}a^2
\end{aligned}
\tag{17.12}
$$

must vanish. The exhaustive roots of $\mathcal G$ are $0,-7/1560$. Their $\mathcal H$ values are respectively $-1,-29357/216320$, both nonzero. At the second candidate the samples $q(1),q(2),q(3),q(4)$ are $697/1040,6/13,361/1040,3/10$. Thus no zero sample was hidden in taking reciprocals. The auxiliary $Z$ was only a trace-one real matrix, never assumed to be a positive source. This excludes the regular odd branch for $L_1$, for every support cardinality.

It remains to consider $h_1h_3=0$. Both cannot vanish since $z\ne A$. If $h_1=0$, the first row fixes $d=A\ne0$; if $h_3=0$, the third fixes $d=z\ne0$. Hence $h_0\ne0$ and the scale of $g=\lambda h$ is fixed by $d=-\lambda h_0$. All worlds of $\mathcal S_h$ now have the same whole $g,d$. An active even sample fixes $b$ because $C\ne Y$. The remaining nonzero early odd sample fixes $n=j+r$ in the first case and $j$ in the second. The corresponding monic source quadratics are precisely those in (17.5). There are at most two complete worlds in the entire $\mathcal S_h$. The $L_1$ guard supplies two, so the nested sets in (17.4) must all equal that pair.

The two roots have different $r$. With fixed $n$, the fifth-J trace is $n+r$; with fixed $j$, it is $j+2r$. In either case the shared fifth response forces $g(5)=0$, and the final-J collision forces $g(7)=0$. Together with $g(1)=0$ or $g(3)=0$ these are three distinct roots. The initial value fixes exactly the corresponding polynomial in (17.5), with nonzero scale. Substitution in the two even rows gives its $C,Y$ and its vanishing residual. These are the $157$ and $357$ formulas of Definition 10.2; their strict two-root filters remain necessary. The argument here permits all signs consistent with (17.3), rather than invoking the positive-$A,C$ classification outside its domain.

For the resulting pair, both actual sixth traces $1+2b$ and $1+3b$ are common. After each acquired sixth response both terminal actions read the common $d$, since $g(7)=0$. Each terminal leaf contains the pair, each sixth child has $L_1$ with its guard, and their common fifth node has $L_2$ with its guard. If $F_0F_1\ne0$, neither column of (17.5) is possible; the sixth-J conjunct of any direction-contained fifth-J $L_2$ is therefore impossible. ∎

## 18. Gain direction together with the actual JJ responses

**Theorem 18.1 (Direction-tagged actual JJ injectivity).** Suppose

$$
A>0,\qquad C>Y>0,\qquad z\ne A,\qquad F_1\ne0.
\tag{18.1}
$$

For every real $p$, the map on the entire compatible fifth-J fiber

$$
W\longmapsto\bigl([g_W],u_J(W),a_{JJ}(W)\bigr),\qquad
a_{JJ}(W)=d+g(7)(j+2r),
\tag{18.2}
$$

is injective. In particular any distinct pair with the same acquired sixth-J response and the same final-J response has nonproportional entire gains. This is a statement about a tagged map: $[g_W]$ is not supplied by the experiment.

Proof. Suppose two worlds share the history, the direction and $u_J$. Write $g_2=\mu g_1$, $\mu\ne0$. Initial response gives $d_2=\mu d_1$. First suppose $\mu\ne1$. With $T_i=1+b_i>1$, subtraction of the two clock-two rows and the two clock-four rows gives

$$
\mu g_1(2)(T_2-T_1)=C(1-\mu),\qquad
2\mu g_1(4)(T_2-T_1)=Y(1-\mu).
\tag{18.3}
$$

Their nonzero right sides justify the divisions below. These identities yield $2C g_i(4)=Y g_i(2)$. Substitution into each world's even rows gives

$$
d_i\bigl[2(C-Y)T_i+Y\bigr]=CY.
\tag{18.4}
$$

The bracket exceeds $C>0$, hence $0<d_i<Y$. In particular $\mu>0$, the two drifts are distinct, and $\varphi=g_i/d_i$ is the same entire polynomial for both worlds. Put

$$
q=Y/C\in(0,1),\qquad \alpha=\frac{2(1-q)}q,\qquad \eta=1-q.
$$

The even rows give $\varphi(0)=-1$, $\varphi(2)=\alpha$, $\varphi(4)=\eta$. Since
$T_i=(C/d_i-1)/\alpha$, the acquired sixth-J response is

$$
u_J=\frac{2C\varphi(6)}\alpha
+d_i\left[1-\varphi(6)\left(1+\frac2\alpha\right)\right].
\tag{18.5}
$$

Its equality for distinct $d_i$ forces $\varphi(6)=\eta$ and $u_J=Y$. Interpolation at the even nodes, with the same weights as (16.2), now fixes all samples:

$$
\begin{array}{c|c}
i&\varphi(i)\\ \hline
0&-1\\
1&(4q^2-39q+30)/(16q)\\
2&2(1-q)/q\\
3&(18-9q-8q^2)/(16q)\\
4&1-q\\
5&(-20q^2+29q-10)/(16q)\\
6&1-q\\
7&(42-37q)/(16q).
\end{array}
\tag{18.6}
$$

In particular

$$
\varphi(7)-\varphi(5)=\frac{(2-q)(13-10q)}{8q}>0.
\tag{18.7}
$$

If $\varphi(5)=0$, the common fifth response would equal both distinct drifts, which is impossible. The actual fifth-J and final-J matrices are equal, so

$$
a_{JJ}(W_i)=\frac{\varphi(7)}{\varphi(5)}p
+\left(1-\frac{\varphi(7)}{\varphi(5)}\right)d_i.
\tag{18.8}
$$

The coefficient of $d_i$ is nonzero by (18.7). Thus scale-changing proportional worlds have different actual final-J responses.

Now suppose $\mu=1$. The entire gain and drift are common. At least one of $g(2),g(4)$ is nonzero since $C\ne Y$, so $b$ is fixed. If at least two of $g(1),g(3),g(5)$ are nonzero, their independent traces $j,j+r,j+2r$ fix $j,r$, giving the same world. Otherwise exactly one of these samples is nonzero, because $z\ne A$ excludes $g(1)=g(3)=0$.

If only $g(1)$ is active, common $j,b$ and different sources have different $r$. A final-J collision forces $g(7)=0$. Hence
$g(s)=a(s-3)(s-5)(s-7)$, $d=105a$,
$C=a(90-15b)$ and $Y=a(108+6b)$. The condition $Y>0$ forces $a>0$, so $Y-C=a(18+21b)>0$, contradicting $C>Y$.
If only $g(3)$ is active, the same argument gives
$g(s)=a(s-1)(s-5)(s-7)$ and $d=A=35a$.
Its even rows give $F_1=0$ by (17.5), again a contradiction. These cases exhaust equal gains. Thus equal values of all three coordinates in (18.2) force the same complete world. ∎

**Theorem 18.2 (Necessary scale-changing relation and a direction-child bound).** Under $C>Y>0$, any scale-changing proportional pair sharing $H_{5J}^A$ and its acquired sixth-J response must satisfy

$$
\mathcal P(Y/C)=0,\qquad
\mathcal P(q)=18q^3-62q^2+75q-30.
\tag{18.9}
$$

It has $0<d_i<Y$, $u_J=Y$, the normalized samples (18.6), and different final-J responses. This is a necessary relation, not a source-existence certificate.

If also $z\ne A$ and $0<Y/C\le4/5$, every one-direction actual sixth-J child contains at most two complete worlds, for every $p,u$. No global bound on the unrestricted child is asserted.

Proof. The scale-changing branch of Theorem 18.1 used only $C>Y>0$ and the shared rows, so it gives (18.4)–(18.8). All of $\varphi(1),\varphi(3),\varphi(5)$ must be nonzero: otherwise the corresponding common odd response would equal two distinct drifts. The trace identity gives, for each drift,

$$
\frac{p-d_i}{\varphi(5)}
=2\frac{z-d_i}{\varphi(3)}-\frac{A-d_i}{\varphi(1)}.
\tag{18.10}
$$

Subtract for the two distinct drifts and multiply only nonzero samples. The result is

$$
\varphi(5)(2\varphi(1)-\varphi(3))-\varphi(1)\varphi(3)
=\frac{(2-q)\mathcal P(q)}{16q^2}=0,
\tag{18.11}
$$

which proves (18.9). For $q=4/5-t$, $t\ge0$, exact expansion gives

$$
\mathcal P(4/5-t)
=-\frac{58}{125}-\frac{259}{25}t-\frac{94}{5}t^2-18t^3<0.
\tag{18.12}
$$

Thus a one-direction child in the stated ratio range has no two different gain scales. All of its gains and drifts are common, and an active even row fixes $b$. The condition $z\ne A$ guarantees at least one active odd sample. Two active odd samples fix the source; if just one trace $j+mr=\ell$ is fixed, the sources satisfy

$$
r^2-(1+mb)r+b(\ell-b)=0.
\tag{18.13}
$$

This monic quadratic gives at most two complete worlds. Strict legality, all remaining rows and repeated roots are still filtered. Neither (18.9) nor the source quadratic alone supplies two legal worlds. ∎

**Theorem 18.3 (The final-J coordinate cannot be omitted).** There are different legal complete worlds satisfying the strict parent conditions (18.1), with the same entire gain, the same fifth-J history and the same acquired sixth-J response.

Proof. Set

$$
b=\frac14,\quad d=24,\quad
g(s)=\frac65(s-1)(s-4)(s-5),\qquad
P_0=\begin{pmatrix}1/3&1/4\\8/9&2/3\end{pmatrix},\quad
P_1=\begin{pmatrix}11/12&1/4\\11/36&1/12\end{pmatrix}.
\tag{18.14}
$$

Both sources are strictly positive, trace one and determinant zero. Along the literal word $JMJMJJJ$ their response rows are

$$
\begin{aligned}
W_0:&\quad(0,24,33,466/15,24,24,42,102),\\
W_1:&\quad(0,24,33,466/15,24,24,42,636/5).
\end{aligned}
\tag{18.15}
$$

Direct evaluation of this one $g$ and the actual traces gives each entry; in particular the legal sampled zero $g(4)=0$ is retained. Here $A=24$, $C=33>Y=24>0$, $z=466/15\ne A$, $F_1=-162$, and $Y/C=8/11$. The direction and $u_J=42$ coincide, while the final-J responses differ. Thus this pair does not contradict Theorem 18.1, and it disproves dropping its final-J coordinate. ∎

## 19. Separate exact-parent consequences and the remaining common-parent system

**Theorem 19.1 (Direction constraints at the two attained M parents).** At each exact parent $H_4^{[3]}$ of (7.10) and $H_4^{[4]}$ of (8.6), and every real fifth-J response $p$, any actual sixth-J child with $L_1$ contains at least two nonproportional entire gains. Thus its gain span over $\mathbb R$ has dimension at least two. No finite or infinite support contained in one gain direction can supply the fifth-J $L_2$ at either parent.

At $H_4^{[4]}$, every distinct final-J collision pair in any actual sixth-J child itself has nonproportional entire gains. Also each one-direction sixth-J child there contains at most two complete worlds. The individual-pair conclusion is asserted at the positive-$Y$ parent only. At negative-$Y$ $H_4^{[3]}$ the conclusion is the whole-child diversity constraint, which does not identify the directions of every possible final-J pair.

Proof. The parent values are the exact algebraic quantities defined by their respective roots in (7.7)–(7.10) and (8.1)–(8.6). Their defining roots are not replaced by independently chosen points in response intervals. The enclosures in §§7–8 give the following closed bounds. In each row the denominator $D$ applies to all interval endpoints, and $A=24$.

| Exact parent | $D$ | $C$ numerator interval | $z$ numerator interval | $Y$ numerator interval | $F_0$ numerator interval | $F_1$ numerator interval |
| --- | --- | --- | --- | --- | --- | --- |
| $H_4^{[3]}$ | $10^6$ | $[69388395,69388396]$ | $[13172131,13172132]$ | $[-14554448,-14554447]$ | $[-170230486,-170230389]$ | $[-3039718312,-3039718235]$ |
| $H_4^{[4]}$ | $10^8$ | $[3467682605,3467682606]$ | $[3364873983,3364873984]$ | $[2428092588,2428092589]$ | $[-27983154182,-27983154085]$ | $[-22259428872,-22259428795]$ |

For example the lower and upper $F_0$ numerators are
$14C_{\rm lo}+35Y_{\rm lo}-48z_{\rm hi}$ and
$14C_{\rm hi}+35Y_{\rm hi}-48z_{\rm lo}$; those for $F_1$ are
$35Y_{\rm lo}-42C_{\rm hi}+384D$ and
$35Y_{\rm hi}-42C_{\rm lo}+384D$.
These give the displayed exact integer bounds. All four residual upper endpoints are negative.

Each parent satisfies $AzCY\ne0$, $z\ne A$, $C\ne Y$, and $F_0F_1\ne0$. Theorem 17.2 applies separately at each one. If an $L_1$ child's gains spanned one dimension, choosing any of its nonzero gains as $h$ would put the whole child inside $\mathcal S_h$, contradicting that theorem. The sixth-J conjunct is required in every fifth-J $L_2$.

At $H_4^{[4]}$ the enclosures also give $C>Y>0$, $F_1<0$, and $Y/C<4/5$. For the last inequality, already the coarser bounds in (12.1) give $5\cdot2429=12145<13868=4\cdot3467$. Theorem 18.1 gives the individual final-J-pair statement and Theorem 18.2 gives the one-direction child bound. The strict hypotheses persist on the same local continuous realization family of Theorem 8.4 after shrinking its parameter neighborhood. This uses continuity of that family; it does not assert a full-rank parent-response map or M-arm existence on a Cartesian response box. ∎

**Definition 19.2 (The unresolved common-parent system).** For each one of the exact parents $H_4^{[3]}$, $H_4^{[4]}$, retain its inherited actual fifth-M $L_2$ from Theorem 7.3 or 8.3. The missing J arm is the existence of **one** $p_J$ for which (16.13), using all strict filters (16.4), is feasible. It requires one acquired $v_J$ and one acquired $v_M$ under that same $p_J$, and two terminal collision pairs inside each corresponding child. Different pairs may overlap or be disjoint, but their acquired sixth response must agree within each child. Every used world remains a fixed complete triple, including its one entire gain and one drift.

This feasibility problem remains open. The atlas is a bijective interface to its worlds, not a feasibility proof; a real root of one drift cubic is not enough. Its at-most-three bound applies separately at each fixed $b$ and puts no finite bound on the available $b$ values or on global child cardinality. The direction constraints in Theorem 19.1 are necessary conditions, not mixed-gain witnesses. The positive-$Y$ leaf statement does not extend here to the negative-$Y$ parent.

The exact parents of §15 have $z=24$, whereas $H_4^{[3]}$ has $13<z<14$ and $H_4^{[4]}$ has $33.64<z<33.65$. Thus none of these parents coincide. The new $K_\beta$ J supports cannot be joined to either inherited M support to obtain $L_3$. At $H_{4,\beta}$, an unrestricted M arm would require worlds outside the entire $g=h$ slice by Theorems 15.2 and 15.4. Conversely an unrestricted fiber at this parent has not been classified by its exact-$h$ subfamily. The support minima and the cutoff in Theorem 15.2 are only relative to $K_\beta$.

The unresolved statements include the unrestricted same-parent fifth-J $L_2$ and parent $L_3$, the separate fixed-C35 response domain left open in §9, the alternative fourth actions and earlier ancestors, the original guarded root $L_7$, arbitrary deterministic adaptive eight-read recovery or impossibility, the comparison with nine total readings, and full-original-domain nine-read sufficiency. The strategies retain the quantifiers of Definition 1.3, with no continuity, measurability, computability or finite-description restriction. A local arm or a tagged injectivity theorem does not settle these root or strategy questions.

**Definition 19.3 (Mathematical sources and applicability).** The status of the model-specific statements in §§15–19 is ordinary, repository-derived mathematics. Their proofs use the original complete-world domain and literal products of §§1 and 10. Standard interpolation, polynomial root multiplicity, monic quadratic bounds and affine reciprocal functions are intermediate tools, not separate new general results. These statements assert no Lean/kernel formalization.

The repository correspondences are as follows; each citation is used only within its own hypotheses.

| Source | Mathematical overlap and distinction |
| --- | --- |
| Root volume, [§23](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md#23-全实根三根五类的实际-jj-逆与任意支持失败分类), especially (23.4)–(23.6), (23.15)–(23.18) | The actual fifth-J coordinates, the gain $h$ and its continuous $\beta=4$, $C=48$ family are inherited. The variable-width consequences in §15 are the $1/3$ cutoff, the $1/4$ support transition, the rational J realization and the entire exact-gain M obstruction. |
| [Terminal-zero-plane volume](FIB_TERMINAL_ZERO_PLANE_INVERSE_AND_J_PAIR_CHAMBER.md), Theorems 9.3, 10.2, 11.2 | Fixed-source uniqueness, an entire fifth-fiber inverse and guarded terminal-slot extraction already exist. Section 16 gives even-node drift cubics with positive leading coefficients and a multiplicity bound on complete worlds at fixed $b$; the same-source calculation is supplied within that interface. No chamber-specific theorem is applied to a parent outside its chamber. |
| [Promised-fiber volume](FIB_JMJM_PROMISED_FIBERS_AND_JOINT_EXCEPTION_GEOMETRY.md), Theorem 4.1 and §6 | Affine reconstruction in a gain direction, quadratic source bounds and sampled-zero mechanisms are existing tools in the $C=48$, $24<z<48$ sector. That sector does not supply the present separate-parent constraints at the prescribed fifth-J and sixth-J history. |
| Root volume, Theorem 27.1 and Corollary 27.2 | A known direction admits a direction-dependent seven-action recovery word and hence an original-root diversity obstruction. Here the direction constraints concern the already prescribed prefix $JMJMJ$ and its actual sixth-J child; a free choice of an earlier word cannot substitute for that child. |
| This volume, §§10–14 | Exact two-world fifth-J classification, root-seven strip fibers and equality-of-whole-gain bounds are inherited. Section 17 treats arbitrary support in a proportional class, including scale-changing gains; §18 supplies the stronger individual JJ-pair constraint under its additional positive-$Y$ hypotheses. |

The external identifiability framework of Li–Lee–Bresler, *[A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems](https://arxiv.org/html/1501.06120)*, Definition 2.7 and Theorem 2.8, distinguishes factor equivalence classes from ordinary identifiability. It does not turn $[g]$ into acquired data or prove the fixed real positive-source J/M/cubic/drift statements above. Ling–Strohmer, *[Self-Calibration and Bilinear Inverse Problems via Linear Least Squares](https://arxiv.org/html/1611.04196)*, model setup and §2.2, uses invertible calibration and repeated-design or snapshot assumptions. Those assumptions do not remove sampled gain zeros from this single nonresetting trajectory. Ordinary four-node interpolation may be read in Berrut–Trefethen, *[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)*, §2; its use here is the explicit fixed-node matrix in (16.2), with all world filters kept.

These are applicability comparisons with the named results, not an exhaustive literature or repository classification, a priority claim, or a new general inverse-problem method. The exact-gain family is a conditional subfamily of the original domain; the unrestricted atlas retains arbitrary gain signs, zeros and repeated roots, all lower degrees, zero drift, unbounded positive off-diagonals and the $D=0$ strata. Any extra nonzero condition used in §§17–18 is either a displayed theorem hypothesis or a consequence proved from the shared original rows. No gain, drift, clock or source is changed between a world's acquired and alternative responses.

## 追加锚（本行以下为增补区）
