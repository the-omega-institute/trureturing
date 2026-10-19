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
