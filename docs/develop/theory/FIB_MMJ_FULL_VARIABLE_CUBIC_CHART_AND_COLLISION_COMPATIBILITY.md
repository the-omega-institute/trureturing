# FIB MMJ 全变量三次纤维与完整世界恢复

## 1. 完整世界、字面历史与源坐标

**定义 1.1（完整目标与原时钟）。** 置

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

一个合法完整世界是 $W=(P,g,d)$，其中

$$
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),\qquad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{1.1}
$$

因此源逐项严格正、秩恰为一、迹为一，可以不对称；非对角元无上界。令 $A_0=I$、$A_i=E_iA_{i-1}$，原时钟 $i$ 的响应是

$$
z_i(W)=d+g(i)\operatorname{tr}(A_iP).
\tag{1.2}
$$

初读计数，每个单独动作后立即读取。全过程固定同一个源、整个增益和漂移，不重置、不复制轨迹、不跳读、不补空动作、不重编号时钟，也不增加观测端口。目标是整个三元组，不是其某个因子或类别。

本卷固定

$$
H_4=(0,J,24,M,48,J,z,M,Y),\qquad
36<z<\frac{361}{10},\quad33<Y<34,
\tag{1.3}
$$

并固定任意实数 $p,v,a$。所研究的是实际第五个 $M$、第六个 $M$、最终 $J$ 的纤维，其字面七动作词与八个响应为

$$
(E_1,\ldots,E_7)=(J,M,J,M,M,M,J),\qquad
(z_0,\ldots,z_7)=(0,24,48,z,Y,p,v,a).
\tag{1.4}
$$

记实现式 (1.4) 的全部合法世界为 $\mathcal F_{MMJ}(z,Y,p,v,a)$。各个候选世界都可有不同的 $b,d,g$；不假定两个可能端点共享任何隐藏参数。

**命题 1.2（全部实际迹与无根式的源条件）。** 定义

$$
t=1+b>1,\quad u=2t-1=1+2b,\quad
j=b+c,\quad n=r+j,\quad x=\frac n u>0.
\tag{1.5}
$$

式 (1.4) 的矩阵和迹为

| 原时钟 | 实际矩阵 $A_i$ | $\operatorname{tr}(A_iP)$ |
| --- | --- | --- |
| $0$ | $\left(\begin{smallmatrix}1&0\\0&1\end{smallmatrix}\right)$ | $1$ |
| $1$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $j=n-r$ |
| $2$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $t$ |
| $3$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $n$ |
| $4$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $u$ |
| $5$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $n+u$ |
| $6$ | $\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$ | $n+2u$ |
| $7$ | $\left(\begin{smallmatrix}5&2\\3&1\end{smallmatrix}\right)$ | $t+2n+2r$ |

给定 $t,n,r$，令 $b=t-1$、$c=n-r-b$。源合法当且仅当

$$
t>1,\qquad0<r<1,\qquad c>0,\qquad
r^2-tr+bn-b^2=0.
\tag{1.6}
$$

证明。对任意二阶矩阵 $A$，直接乘法给出

$$
\operatorname{tr}(AP)=A_{22}+(A_{11}-A_{22})r+A_{21}b+A_{12}c.
\tag{1.7}
$$

逐次左乘 $J,M,J,M,M,M,J$ 得表中矩阵，代入式 (1.7) 得各迹；末迹也等于 $1+4r+3b+2c$。每个迹在合法源上严格正。代入 $c=n-r-b$ 后，$bc=r(1-r)$ 等价于

$$
bn-br-b^2=r-r^2,
$$

即式 (1.6)。其余严格条件恰保证所有条目为正；行列式为零、迹为一使秩恰为一。还得到 $j=n-r=b+c>0$ 和 $n>b=t-1$。这里保留整个源二次方程，不选择其某个根。∎

## 2. 同一个整个增益与仿射漂移系数

**命题 2.1（四节点插值与全部余下样本）。** 对 $t>1,n>0,d\in\mathbb R$，置

$$
f=\frac{48-d}{t},\qquad e=\frac{z-d}{n},\qquad
h=\frac{Y-d}{u}.
\tag{2.1}
$$

唯一的三次及以下增益候选为

$$
\begin{aligned}
g(s)={}&\frac d{24}(s-2)(s-3)(s-4)
 +\frac f4s(s-3)(s-4)\\
&-\frac e3s(s-2)(s-4)+\frac h8s(s-2)(s-3).
\end{aligned}
\tag{2.2}
$$

定义

$$
L=\frac{6f+h-d}{4},\quad Q=\frac{10f+15h+d}{4},\quad
R=9f+9h+d,\quad S_7=21f+\frac{35}2h+\frac52d.
\tag{2.3}
$$

则同一多项式满足

$$
k:=g(1)=L-e,\quad g(5)=Q-5e,\quad
g(6)=R-16e,\quad\gamma:=g(7)=S_7-35e.
\tag{2.4}
$$

全部尚需满足的非插值节点响应是

$$
\begin{aligned}
k(n-r)&=24-d,\\
p&=d+(Q-5e)(n+u),\\
v&=d+(R-16e)(n+2u),\\
a&=d+\gamma(t+2n+2r).
\end{aligned}
\tag{2.5}
$$

证明。式 (2.2) 的四个基项分别在 $0,2,3,4$ 的自身节点取所需值 $-d,f,e,h$，在其余三个节点为零。两个三次及以下候选的差有四个不同根，只能恒零，故整个增益唯一。将 $1,5,6,7$ 代入这四个基项，所得系数分别为

$$
\begin{pmatrix}
-1/4&3/2&-1&1/4\\
1/4&5/2&-5&15/4\\
1&9&-16&9\\
5/2&21&-35&35/2
\end{pmatrix}
\begin{pmatrix}d\\f\\e\\h\end{pmatrix}.
\tag{2.6}
$$

这就是式 (2.3)–(2.4)。再用命题 1.2 的实际迹得到式 (2.5)。一切低次、重根及采样零都包括在同一个插值式中，未在续行处重新选择增益。∎

**命题 2.2（全变量实际响应的仿射形式）。** 定义只依赖 $t$ 的系数

$$
\begin{aligned}
A&=\frac{t-18+5/t}{2},&B&=2t-28+\frac9t,\\
K&=240-\frac{120}{t}+\frac{15Y}{4},&
N&=864-\frac{432}{t}+9Y,
\end{aligned}
\tag{2.7}
$$

以及依赖 $(t,x)$ 的四个函数

$$
\begin{aligned}
p_0&=(x+1)\left(K-\frac{5z}{x}\right),&
v_0&=(x+2)\left(N-\frac{16z}{x}\right),\\
p_1&=A(x+1)+6+\frac5x,&
v_1&=B(x+2)+17+\frac{32}{x}.
\end{aligned}
\tag{2.8}
$$

则实际第五、第六响应恰是

$$
p=p_0+dp_1,\qquad v=v_0+dv_1.
\tag{2.9}
$$

这些函数是隐藏源坐标的系数，不是额外读数。

证明。由 $u=2t-1$ 和式 (2.1)–(2.3)，

$$
\begin{aligned}
uQ&=\frac{120u}{t}+\frac{15Y}{4}
+d\left(\frac u4-\frac{5u}{2t}-\frac{15}{4}\right)=K+Ad,\\
uR&=\frac{432u}{t}+9Y+d\left(u-\frac{9u}{t}-9\right)=N+Bd.
\end{aligned}
\tag{2.10}
$$

使用 $n=ux$、$e=(z-d)/(ux)$，式 (2.5) 的中间两式分别成为

$$
\begin{aligned}
p&=d+(x+1)\left(K+Ad-\frac{5(z-d)}x\right),\\
v&=d+(x+2)\left(N+Bd-\frac{16(z-d)}x\right).
\end{aligned}
\tag{2.11}
$$

收集 $d$，系数分别为 $A(x+1)+1+5(x+1)/x$ 和 $B(x+2)+1+16(x+2)/x$，即式 (2.8)。每个端点都使用自己的 $t,x,d$。∎

## 3. 全象限漂移分母与精确恢复

**定理 3.1（漂移方向在全象限不消失）。** 对每个 $t>1,x>0$，

$$
D_d:=p_1^2+v_1^2>0.
\tag{3.1}
$$

本结论不需要源秩一条件、$z,Y$ 的窗口或增益根承诺。

证明。若 $p_1=v_1=0$，则

$$
A=-\frac{6x+5}{x(x+1)}=-\frac5x-\frac1{x+1},\qquad
B=-\frac{17x+32}{x(x+2)}.
$$

相减得

$$
B-4A=q(x):=\frac{7x^2+19x+8}{x(x+1)(x+2)}
=\frac4x+\frac4{x+1}-\frac1{x+2}.
\tag{3.2}
$$

另一方面，式 (2.7) 给 $B-4A=8-1/t>7$。在正轴上

$$
q'(x)=-\frac4{x^2}-\frac4{(x+1)^2}+\frac1{(x+2)^2}
<-\frac4{x^2}-\frac3{(x+1)^2}<0,
$$

而 $q(4/5)=865/126<7$，因为 $865<882$。所以 $q(x)>7$ 强迫 $x<4/5$，从而

$$
-A=\frac5x+\frac1{x+1}>\frac{25}4+\frac59
=\frac{245}{36}>\frac{34}{5}.
\tag{3.3}
$$

最后一个比较清正分母后是 $1225>1224$。可是

$$
A+\frac{34}{5}=\frac{(5t-11)^2+4}{50t}>0
\tag{3.4}
$$

对所有 $t>0$ 成立，矛盾。故两个漂移系数不可能同时为零；其中任一个单独为零仍被本定理覆盖。∎

**命题 3.2（漂移恢复及相容行列式）。** 定义

$$
\Xi=p_1(v-v_0)-v_1(p-p_0),\qquad
\widehat d=\frac{p_1(p-p_0)+v_1(v-v_0)}{D_d}.
\tag{3.5}
$$

式 (2.9) 当且仅当 $\Xi=0,d=\widehat d$。精确残差为

$$
p-p_0-p_1\widehat d=-\frac{v_1\Xi}{D_d},\qquad
v-v_0-v_1\widehat d=\frac{p_1\Xi}{D_d}.
\tag{3.6}
$$

证明。以 $D_d=p_1^2+v_1^2$ 展开两个分子即得式 (3.6)。原两式若成立，交叉相减给 $\Xi=0$，与 $(p_1,v_1)$ 作内积给 $d=\widehat d$；反向由残差为零得到。定理 3.1 使除法在整个象限合法，不必选择某个非零分量。∎

## 4. 精确三次投影及全部系数

**定理 4.1（负二次幂相消与完整三次式）。** 置

$$
\begin{aligned}
h_2&=AN-BK,\\
h_1&=(3A+6)N-(3B+17)K+z(5B-16A),\\
h_0&=(2A+17)N-(2B+49)K+z(-48A+15B-11),\\
h_{-1}&=10N-32K+z(10B-32A-27).
\end{aligned}
\tag{4.1}
$$

收集为 $t,Y,z$ 的显式形式是

$$
\begin{aligned}
h_2={}&-(48+3Y)t+24Y-1032+\frac{2112-45Y}{4t},\\
h_1={}&-(144+9Y)t+\frac{249Y}{4}-1992
 +\frac{4128-135Y}{4t}+z\left(2t+4+\frac5t\right),\\
h_0={}&-(96+6Y)t+\frac{69Y}{4}+864
 -\frac{1632+90Y}{4t}+z\left(6t+1+\frac{15}t\right),\\
h_{-1}={}&960-\frac{480}t-30Y+z\left(4t-19+\frac{10}t\right).
\end{aligned}
\tag{4.2}
$$

定义

$$
\begin{aligned}
\mathcal C(t,x;p,v)={}&-h_2x^3+(Av-Bp-h_1)x^2\\
&+\bigl((A+6)v-(2B+17)p-h_0\bigr)x
 +5v-32p-h_{-1}.
\end{aligned}
\tag{4.3}
$$

则 $\mathcal C=x\Xi$。因此在 $x>0$ 上，三次式为零与实际 $p,v$ 的漂移相容性完全等价。

证明。将四个 Laurent 式完整写出：

$$
\begin{aligned}
p_1&=Ax+(A+6)+5/x,&v_1&=Bx+(2B+17)+32/x,\\
p_0&=Kx+(K-5z)-5z/x,&v_0&=Nx+(2N-16z)-32z/x.
\end{aligned}
\tag{4.4}
$$

令 $\mathscr H=p_1v_0-v_1p_0$。乘积最低只能出现 $x^{-2}$；其系数恰是

$$
5(-32z)-32(-5z)=0.
\tag{4.5}
$$

其余四个系数逐项为

$$
\begin{aligned}
[x^2]\mathscr H={}&AN-BK,\\
[x]\mathscr H={}&A(2N-16z)+(A+6)N-B(K-5z)-(2B+17)K,\\
[x^0]\mathscr H={}&-32Az+(A+6)(2N-16z)+5N\\
&+5Bz-(2B+17)(K-5z)-32K,\\
[x^{-1}]\mathscr H={}&-32z(A+6)+5(2N-16z)
 +5z(2B+17)-32(K-5z).
\end{aligned}
\tag{4.6}
$$

收集这些项就是式 (4.1)，故

$$
\mathscr H=h_2x^2+h_1x+h_0+h_{-1}/x.
\tag{4.7}
$$

为核对式 (4.2)，先用

$$
\begin{aligned}
432A-120B&=-24(t+22),\\
9A-\frac{15}4B&=-3t+24-\frac{45}{4t},
\end{aligned}
$$

以及 $K=120u/t+15Y/4$、$N=432u/t+9Y$ 得到所列 $h_2$。再用

$$
\begin{aligned}
h_1&=3h_2+6N-17K+z(5B-16A),\\
h_0&=2h_2+17N-49K+z(-48A+15B-11),\\
5B-16A&=2t+4+5/t,\\
-48A+15B-11&=6t+1+15/t,\\
10B-32A-27&=4t-19+10/t
\end{aligned}
$$

代入式 (2.7)，分别给式 (4.2) 的其余三行。最后
$\Xi=p_1v-v_1p-\mathscr H$；乘以 $x$ 即得式 (4.3) 的全部四个系数及其符号。由于 $x>0$，清除此分母不引入正坐标赘根。∎

**定理 4.2（全无界源域上的真正三次）。** 对每个 $t>1$、$33<Y<34$，

$$
-h_2>\frac{825}{4}.
\tag{4.8}
$$

所以对任意固定 $t$ 和任意实 $p,v$，式 (4.3) 在 $x$ 中次数恰为三，不存在恒零或降次层。

证明。由式 (4.2)，

$$
-(48+3Y)t<-147,\qquad24Y-1032<-216,
$$

且 $582<2112-45Y<627$、$t>1$ 给

$$
\frac{2112-45Y}{4t}<\frac{627}{4}.
$$

相加得 $h_2<-147-216+627/4=-825/4$。这不依赖 $p,v,z$，也不对 $t$ 设上界。此处的三次是源坐标 $x$ 的次数，不是增益实际次数的承诺。∎

## 5. 合法世界的首末分母与全部线性分支

**定理 5.1（首、末样本不可能同时为零）。** 在式 (1.3) 的每个合法世界上，

$$
D_r:=k^2+4\gamma^2>0.
\tag{5.1}
$$

该结论只断言合法世界上的正性，不断言未过滤的整个 $(t,x)$ 象限上 $D_r>0$。

证明。反设 $k=g(1)=0$ 且 $\gamma=g(7)=0$。第一祖先和 $j>0$ 给 $d=24$。令

$$
m=Y-24\in(9,10),\qquad C_0=z-24\in(12,121/10).
$$

同一个增益由节点 $0,1,2,4$ 的值 $-24,0,24/t,m/u$ 唯一插值为

$$
g(s)=3(s-1)(s-2)(s-4)-\frac6t s(s-1)(s-4)
 +\frac{m}{24u}s(s-1)(s-2).
\tag{5.2}
$$

因此

$$
H_3:=g(3)=-6+\frac{36}t+\frac m{4u},\qquad
\gamma=270-\frac{756}t+\frac{35m}{4u}.
\tag{5.3}
$$

第三祖先是 $H_3n=C_0>0$，故 $H_3>0$。在 $1<t\le2$，

$$
\gamma<270-378+\frac{175}{2}=-\frac{41}{2}<0;
$$

这里 $-756/t\le-378$，且 $m<10,u>1$。在 $t\ge3$，最后一项正而 $-756/t\ge-252$，所以 $\gamma>18>0$。端点 $t=2,3$ 也被严格符号排除，$\gamma=0$ 只能有 $2<t<3$。

在此区间，

$$
(t-1)H_3=42-6t-\frac{36}t+\frac m4\frac{t-1}{2t-1},
$$

其中

$$
42-6t-\frac{36}t-12=-\frac{6(t-2)(t-3)}t>0,\qquad
\frac{t-1}{2t-1}>\frac13.
$$

故

$$
(t-1)H_3>12+\frac34=\frac{51}{4}>\frac{121}{10}>C_0.
\tag{5.4}
$$

源严格正给 $n=r+b+c>b=t-1$，与 $H_3>0$ 合用却得到
$C_0=nH_3>(t-1)H_3$，矛盾。故不可能同时为零，式 (5.1) 成立。这一短证明直接使用完整源的必要条件和第三祖先，不依赖其他首根分离多项式或并集单射性。∎

**命题 5.2（首、末响应的有护栏有理恢复）。** 固定 $t,x$，按式 (3.5) 取 $d=\widehat d$，用式 (2.1)–(2.4) 构造同一个增益。置

$$
U=kn-(24-d),\qquad V=a-d-\gamma(t+2n),\qquad
\Delta_r=kV-2\gamma U.
\tag{5.5}
$$

首祖先和最终响应恰为

$$
kr=U,\qquad2\gamma r=V.
\tag{5.6}
$$

当 $D_r>0$ 时，这等价于

$$
\Delta_r=0,\qquad r=\widehat r:=\frac{kU+2\gamma V}{D_r}.
\tag{5.7}
$$

精确残差为

$$
U-k\widehat r=-\frac{2\gamma\Delta_r}{D_r},\qquad
V-2\gamma\widehat r=\frac{k\Delta_r}{D_r}.
\tag{5.8}
$$

证明。式 (2.5) 的首、末两式移项给式 (5.6)。展开式 (5.7) 的分子即得式 (5.8)；原两式与 $(k,2\gamma)$ 作内积又给唯一的 $r$。所以两方向均成立。

若 $k=0$，则 $\gamma\ne0$，相容行列式要求 $U=0$，即保留 $d=24$；随后末式确定 $r$。若 $\gamma=0$，则 $k\ne0$，相容行列式要求 $V=0$，即保留 $a=d$；随后首式确定 $r$。两者同时为零的候选可以拒绝，因为定理 5.1 排除了每个完整合法世界。恢复式没有除以单个样本，也没有删掉任何零偏移条件。∎

## 6. 完整通过处方与坐标世界双射

**定义 6.1（通过坐标）。** 固定式 (1.3) 的 $z,Y$ 和一个实际末三响应候选 $(p,v,a)$。一个实数对 $(t,x)$ 通过，当且仅当以下全部条件同时成立：

1. $t>1,x>0$，置 $u=2t-1,n=ux,b=t-1$。按式 (2.7)–(2.8)、(4.1)–(4.3) 求系数，要求 $\mathcal C(t,x;p,v)=0$；以式 (3.5) 的正分母 $D_d$ 定义 $d=\widehat d$。
2. 用式 (2.1)–(2.4) 定义唯一的整个 $g,k,\gamma$，用式 (5.5) 定义 $U,V$。要求 $D_r>0$ 和 $\Delta_r=0$，再以式 (5.7) 定义 $r=\widehat r$。
3. 置 $c=n-r-b$，要求

$$
0<r<1,\qquad c>0,\qquad r^2-tr+bn-b^2=0.
\tag{6.1}
$$

通过时返回 $P=\left(\begin{smallmatrix}r&b\\c&1-r\end{smallmatrix}\right)$、式 (2.2) 的同一个 $g$ 以及 $d$。这些是纯粹的精确实数条件，未把八个读数复现另设为补充义务。

**定理 6.2（全变量三次纤维的完整世界双射）。** 定义 6.1 的通过坐标与 $\mathcal F_{MMJ}(z,Y,p,v,a)$ 一一对应。对每个固定 $t>1$，该纤维至多有三个具有此 $t$ 的不同完整世界。

证明必要性。取纤维内任一合法世界。其 $t,n,x$ 满足正域，实际时钟 $0,2,3,4$ 给式 (2.1) 的四个增益值；四节点唯一性使原整个 $g$ 就是式 (2.2)。实际第五、第六响应由命题 2.2 给式 (2.9)，命题 3.2 于是给 $\Xi=0,d=\widehat d$，定理 4.1 给 $\mathcal C=0$。定理 3.1 的 $D_d>0$ 在源过滤之前已经成立，定理 5.1 的 $D_r>0$ 则适用于此合法世界。其首、末响应由命题 5.2 给 $\Delta_r=0,r=\widehat r$。原源条件由命题 1.2 恰给式 (6.1)。所以每个原世界都进入处方，包括全部允许次数和采样零层。

证明充分性。取任一通过对。$D_d>0$、$\mathcal C=x\Xi=0$ 和式 (3.6) 先给实际响应 $p,v$ 的两个完整等式。$D_r>0$、$\Delta_r=0$ 和式 (5.8) 再给 $kr=U,2\gamma r=V$，即

$$
d+k(n-r)=24,\qquad d+\gamma(t+2n+2r)=a.
\tag{6.2}
$$

由于 $b=t-1>0$，式 (6.1) 与命题 1.2 给 $bc=r(1-r)$、全部条目严格正、迹一、秩恰一，并给 $j=n-r=b+c>0$。同一个式 (2.2) 在四节点取值 $g(0)=-d,g(2)=f,g(3)=e,g(4)=h$，配合实际迹 $1,t,n,u$，逐项得到

$$
\begin{array}{c|cccccccc}
\text{原时钟}&0&1&2&3&4&5&6&7\\\hline
\text{响应}&0&24&48&z&Y&p&v&a.
\end{array}
\tag{6.3}
$$

其中时钟一、七已经由式 (6.2) 证明，时钟五、六已经由漂移残差及同一增益的式 (2.4) 证明；四个插值节点提供其余四读。因此没有把未证的祖先或末端条件藏进八读过滤。如果 $g$ 恒零，初读零先强迫 $d=0$，时钟二就只能读零，与 $48$ 矛盾，故 $g\ne0$。返回的整个世界合法并实现全部八读。

证明互逆与计数。在固定 $z,Y,p,v,a,t,x$ 后，正 $D_d$ 唯一确定漂移，四节点唯一确定整个增益，正 $D_r$ 和两条线性方程唯一确定 $r$，随后 $b=t-1,c=n-r-b$ 唯一。返回世界的 $n=r+b+c=ux$，所以回取坐标得到原 $(t,x)$。反向从原世界重建也恢复原三元组，故两映射互逆。源二次方程的不同合法分支没有被预先删除；其在一个通过坐标上必须服从同一首末线性恢复，因此不产生第二个世界。

对每个固定 $t$，定理 4.2 给非零三次多项式；若它有四个不同实根，逐个因子定理将强迫次数至少四，矛盾。所以至多三个不同正根 $x$。每根最多一个完整世界，其余条件只能删去候选。重根仍是一个坐标。这证明固定 $t$ 的三世界上界。∎

**推论 6.3（尚未解决的碰撞等价式）。** 不受限实际 MMJ 碰撞存在，当且仅当同一 $z,Y,p,v,a$ 有两个通过坐标 $(t_1,x_1),(t_2,x_2)$ 满足

$$
(t_1-t_2)^2+(x_1-x_2)^2>0.
\tag{6.4}
$$

证明。定理 6.2 的双射把两边的不同性互相转换。两份处方各自携带自己的 $b_i,d_i,g_i,r_i,c_i$，均须通过全部条件。∎

这里 $t$ 是隐藏的源参数，不是取得的标签。每个固定 $t$ 的三根上界不约束连续并集 $t\in(1,\infty)$ 的基数，也不证明存在逆、单射性或某个读数预算。式 (6.4) 的存在与不存在均未在此得到证明。

## 7. 双端点漂移转移的两个完整分支

**命题 7.1（共同实际 $p,v$ 的精确转移接口）。** 对端点 $i=1,2$，令

$$
H_i=(p_{0i},v_{0i}),\qquad D_i=(p_{1i},v_{1i}),\qquad
\delta H=H_2-H_1,\qquad\Omega=\det(D_1,D_2).
\tag{7.1}
$$

所有系数均在自己的 $(t_i,x_i)$ 处取值，且 $D_i\ne0$。两端点的实际 $p,v$ 共同，当且仅当

$$
d_1D_1-d_2D_2=\delta H.
\tag{7.2}
$$

若 $\Omega\ne0$，其等价处方为

$$
d_1=\frac{\det(\delta H,D_2)}\Omega,\qquad
d_2=\frac{\det(\delta H,D_1)}\Omega.
\tag{7.3}
$$

若 $\Omega=0$，其等价处方为

$$
\det(\delta H,D_1)=0,\qquad
d_1\|D_1\|^2-d_2(D_1\cdot D_2)=D_1\cdot\delta H.
\tag{7.4}
$$

证明。共同向量 $(p,v)=H_i+d_iD_i$ 移项即为式 (7.2)，定理 3.1 保证两个 $D_i$ 都非零。非平行情形分别与 $D_2,D_1$ 取行列式，得到式 (7.3) 的两个正号；非零行列式又保证反向代入解唯一。平行情形，$\Omega=0$ 使 $D_2$ 是非零 $D_1$ 的倍数，第一护栏使 $\delta H$ 也是其倍数。于是式 (7.2) 的向量残差平行于 $D_1$，第二护栏使其与 $D_1$ 内积为零，因此残差为零。反向由原向量式直接得到两护栏。∎

两个分支都只解决共同 $p,v$；还须对两端点同时加入首祖先、末响应、源秩一和所有严格条件。平行不意味着碰撞，也不供应一个合法世界族；$\Omega$ 只在明确非零的分支中作分母。

## 8. 同一精确父点的条件性特化

**定义 8.1（继承父点与有限前提）。** 《FIB 实际 JMJM 的承诺纤维与联合例外几何》定义 28.1–28.2 固定十二坐标

$$
\xi=(b_1,D_1,r_2,b_2,D_2,r_3,b_3,D_3,r_4,b_4,D_4,Z),\quad
r_1=3/10,\quad d_i=100D_i,\quad z=100Z.
\tag{8.1}
$$

本节仅指该定义的同一字面有理中心 $\xi_0$、其式 (28.8) 的十二个整数、式 (28.9a–d) 的全部四个十二行三列块所定义的同一方阵 $C$，以及半径 $\varepsilon=10^{-12}$ 的闭盒 $X$。这些数据固定，不作为可调参数。这里的 $\xi$ 与本卷源坐标 $x=n/u$ 不同。

各世界仍以 $c_i=r_i(1-r_i)/b_i,j_i=b_i+c_i$，在原节点 $0,1,2,3$ 上取

$$
-d_i,\qquad\frac{24-d_i}{j_i},\qquad
\frac{48-d_i}{1+b_i},\qquad\frac{100Z-d_i}{r_i+j_i}
\tag{8.2}
$$

插值定义一个整个 $g_i$。该继承构造的响应为

$$
\begin{aligned}
Y_i&=d_i+(1+2b_i)g_i(4),&p_i^J&=d_i+(2r_i+j_i)g_i(5),\\
u_i&=d_i+(1+2b_i)g_i(6),&m_i&=d_i+(1+3b_i)g_i(6),\\
A_i^J&=d_i+(2r_i+j_i)g_i(7),&
B_i^J&=d_i+(1+r_i+c_i+3b_i)g_i(7),\\
A_i^M&=d_i+(3r_i+j_i)g_i(7),&
B_i^M&=d_i+(1+2r_i+c_i+4b_i)g_i(7).
\end{aligned}
\tag{8.3}
$$

继承的同一个联合映射是

$$
F=\frac1{100}\begin{pmatrix}
Y_2-Y_1\\p_2^J-p_1^J\\u_2-u_1\\A_2^J-A_1^J\\B_2^J-B_1^J\\
Y_4-Y_3\\p_4^J-p_3^J\\m_4-m_3\\A_4^M-A_3^M\\B_4^M-B_3^M\\
Y_3-Y_1\\p_3^J-p_1^J
\end{pmatrix}.
\tag{8.4}
$$

本节的有限前提为：来源分母在 $X$ 的一个邻域上严格正，继承的全盒合法性及漂移互异包围成立，并且

$$
\sup_{\xi\in X}\|I-CDF(\xi)\|_\infty\le
q:=\frac{3683112}{10^{12}}<1,\qquad
\|CF(\xi_0)\|_\infty\le10^{-40}.
\tag{8.5}
$$

还以继承包围

$$
z_\star\in\frac{[36008179,36008180]}{10^6},\qquad
Y_\star\in\frac{[33443453,33443454]}{10^6}
\tag{8.6}
$$

为前提。所列有限前提不在本卷内重新计算或认证。

**命题 8.2（条件性的同点特化与第五 J 支臂）。** 在定义 8.1 的全部有限前提下，

$$
\xi^{(0)}=\xi_0,\qquad
\xi^{(k+1)}=\xi^{(k)}-CF(\xi^{(k)}),\qquad
\xi_\star=\lim_{k\to\infty}\xi^{(k)}
\tag{8.7}
$$

精确定义 $X$ 内唯一联合零点。令 $z_\star=100Z_\star$、$Y_\star=Y_1(\xi_\star)$；本卷定理 6.2 特化于这同一精确父历史。继承的四世界在第五 $J$ 的共同响应 $p_\star^J$ 后有 $L_2$；本卷当前的第五 $M$ 响应 $p$ 不与 $p_\star^J$ 认同。

证明。$G(\xi)=\xi-CF(\xi)$ 在闭凸盒内沿线段积分导数，式 (8.5) 给 $q$-Lipschitz 性，且

$$
\|G(\xi)-\xi_0\|_\infty
\le q10^{-12}+10^{-40}<10^{-12}.
\tag{8.8}
$$

所以 $G$ 是完备闭盒上的严格自映射收缩，收缩原理给式 (8.7) 的唯一不动点。在中心，$E_0=I-CDF(\xi_0)$ 的范数小于一；几何级数 $\sum_{k\ge0}E_0^k$ 是 $CDF(\xi_0)$ 的双侧逆。两个因子为同阶方阵，故 $C$ 可逆；于是 $CF(\xi_\star)=0$ 推出全部十二行 $F(\xi_\star)=0$。零点反过来都是不动点，所以唯一。这是条件性符号推论，不把中心当作零点，也不执行该迭代。

式 (8.6) 使这同一 $z_\star,Y_\star$ 位于式 (1.3) 的开矩形，所以均匀的三次图谱直接适用，矩形上的主证明本身不依赖有限盒表。

$F$ 的前五行给第一对在第五 $J$ 后共同 $Y,p^J$、共同第六 $J$ 响应及两个最终响应；第六至十行给第二对在第六 $M$ 后的对应共同响应；最后两行使两对共享同一 $Y,p^J$。源合法性、整个增益以及不交的漂移包围给固定的不同完整目标。每对在其指定第六子节点，最终 $J,M$ 的实际叶都保留这对不同目标，故有 $L_1$。两对的固定并集在同一第五 $J$ 历史上不能停止，又分别供应两种第六动作的 $L_1$，所以有 $L_2$。所有相等来自同一个联合零，不能以包含区间相交替代。

式 (8.3) 的第五迹是 $2r+j$，本卷第五 $M$ 的迹却是 $n+u$；因此此条件性支臂不供应缺少的第五 $M$ 支臂。∎

## 9. 完整递归义务、适用边界与内容定位

**定义 9.1（失败递归和八槽共同实现）。** 对任意基数的合法族 $K\subseteq\mathcal F(H)$，置

$$
\begin{aligned}
L_0(K,H)&\iff |K|\ge2,\\
L_{s+1}(K,H)&\iff |K|\ge2\ \land\
\bigwedge_{E\in\{J,M\}}\exists\alpha\in\mathbb R:
L_s(K\cap\mathcal F(H,E,\alpha),(H,E,\alpha)).
\end{aligned}
\tag{9.1}
$$

所用预算只及剩余原时钟，空集、单点和提前停止均保留其原义。在同一 $H_4$ 之后固定第五 $M$，两个第六动作及其最终迹为

| 第六动作 $E$ | 第六迹 $\tau_E$ | 最终 $J$ 迹 $\tau_{EJ}$ | 最终 $M$ 迹 $\tau_{EM}$ |
| --- | --- | --- | --- |
| $J$ | $1+2r+2b+c$ | $1+r+3b+c$ | $2+5b+c$ |
| $M$ | $n+2u$ | $t+2n+2r$ | $3+2r+8b+2c$ |

各响应始终是同一世界的 $d+g(6)\tau_E$ 或 $d+g(7)\tau_{EG}$，第五响应始终是 $d+g(5)(n+u)$。

**命题 9.2（完整第五 M 支臂的八槽接口）。** 在某个同一 $H_4$ 上存在第五 $M$ 的 $L_2$ 族，当且仅当存在一个共同第五响应 $p$ 和八个预先固定的合法完整世界槽

$$
W_{EGk},\qquad E,G\in\{J,M\},\quad k=1,2,
\tag{9.2}
$$

满足以下同时条件：全部槽实现 $H_4$ 及第五 $M$ 的同一 $p$；对每个 $E$，四槽共享一个实际第六响应 $v_E$；对每个 $E,G$，两槽是不同完整目标并共享其实际最终 $G$ 响应。允许 $v_J\ne v_M$，不同叶可以复用同一个整个世界。

证明。先按式 (9.1) 对每个第六动作选一个实际 $L_1$ 子集，再对其每个最终动作选一个实际 $L_0$ 叶；只在这样的终叶选一对不同世界，得到八槽。这对任意基数原族都成立，不从非终端失败族抽取失败对。

反向取槽的固定并集。对每个 $E$，响应 $v_E$ 子集内两种最终动作各有一对不同目标保持碰撞，因此有 $L_1$；两种第六动作于是供应第五历史的两个递归分句，且并集至少二元，所以有 $L_2$。加入任何兼容世界均不破坏结论：$L_0$ 的基数条件向上保持，归纳时相同响应给对应子集包含，故所有 $L_s$ 对包含向上保持。整个论证保留停止护栏。表中迹由式 (1.7) 和实际左乘给出，不增加观测端口。∎

本卷完整图谱只处理式 (9.2) 中 $E=M,G=J$ 的一个实际终叶。在任何第五 $M$ 的 $L_2$ 见证中，先取第六 $M$ 的实际 $L_1$ 子节点，再取最终 $J$ 的实际 $L_0$ 叶，才能在那里选出两世界；它们必须给式 (6.4) 的两个通过坐标。本卷既未构造也未排除这两个坐标。另一个最终 $M$ 叶、第六 $J$ 子节点及其两个最终叶、全八槽的共同第五响应仍是同时义务，不能分别拟合后拼接。

只有在定义 8.1 的同一精确 $z_\star,Y_\star$ 上完成这整个第五 $M$ 的 $L_2$，才可与条件性的第五 $J$ 支臂按包含单调性合成该父 $H_4$ 的局部 $L_3$。这里没有这样的构造或排除。即使有局部 $L_3$，更早每个祖先仍须补齐相反动作、实际响应和提前停止分句，不能迫使任意原根策略到达这个历史。

**适用域和除法边界。** 插值只除以固定非零节点差和正 $t,u,n$；坐标只除以正 $u,x$。$D_d$ 在整个 $t>1,x>0$ 上严格正；$D_r$ 仅在完整合法世界上被证明严格正，并在候选处方中明确要求。两个首末残差都带确定符号。源秩一条件从未改写成选取某个二次根，也未除以判别式；转移分支只在 $\Omega\ne0$ 时除以它。

所有实漂移都保留，特别是 $d=0,24,48,z,Y$；对应 $g(0),g(1),g(2),g(3),g(4)$ 的零层都以未除法的原响应约束保留。$p=d,v=d,a=d$ 分别允许第五、第六、末样本为零。单独的 $p_1=0$、$v_1=0$、$k=0$、$\gamma=0$ 都覆盖；仅证明不可能的两个同时零层被排除。其他相容的多采样根、增益降次、增益重根、坐标三次式重根、源二次式重根均未删除；某个次数层可由精确条件自然为空。

源域保持全部 $0<r<1,b,c>0$，不加对称性、紧盒、上界、有理坐标或增益符号承诺。$r=0,1$、$b=0$、$c=0$、$t=1$、$x=0$ 均为排除边界，不能靠取极限纳入。$t,b,c,n$ 和漂移没有人为上截断。参数矩形严格为式 (1.3)，不声称闭端点延拓。正分母、三次式、转移关系或秩一条件单独都不是世界存在或碰撞的充分条件；充分性使用定义 6.1 的全部同时条件。

**原目标和证据范围。** 任意初读 $a_0$ 只能通过完整双射 $(P,g,d)\mapsto(P,g,d-a_0)$ 归一化：每个原时钟响应都减去 $a_0$，恢复后将其加回漂移。初读零不是零漂移或根承诺。固定 $t$ 的三世界界是目标个数界，不是读数数目；不受限通过坐标问题在连续 $t$ 上仍未解决。因此原域确定性完整目标在原时钟 $0,\ldots,7$ 内至多八次总读恢复，与 $n_{\rm det}(3,0)\ge9$ 的原二择仍为未决；没有不受限终端逆、原根到达证明、原根共同核证书、九读上界或承诺检测器。

本卷的源相对增量是全象限漂移分母不消失、均匀真正三次、合法世界首末分母不消失及完整坐标世界双射。插值、正交投影残差、行列式、非零多项式根数、收缩原理和包含递归作为标准支持工具；转移接口是同一漂移消元的双端点表达。继承第五 $J$ 的有限联合构造及其条件性消费者不另计新成果。这里没有外部新颖性、优先权或文献穷尽主张。所有推导限于未执行的符号数学；不附内核证明、执行算术、有限表、数值、实验、一般神经网络、物理、噪声、稳定性、效率或资源认证。

## 追加锚（本行以下为增补区）

## 10. 任意第五动作的全局源图

**定义 10.1（任意实数父历史与第五纤维）。** 本节不采用式 (1.3) 的小矩形。固定任意
$z,Y,p\in\mathbb R$，并把前四个动作和五个响应写成

$$
(0,J,24,M,48,J,z,M,Y).
$$

在这段前缀之后接第五动作 $E\in\{J,M\}$，其第五响应为 $p$。对一个源置

$$
0<r<1,\qquad b>0,\qquad c=\frac{r(1-r)}b,\qquad
j=b+c,\quad t=1+b,\quad n=r+j,\quad u=1+2b,
$$

并令

$$
s_J=2r+j,\qquad s_M=n+u.
$$

允许 $b=c$；若另行要求非对称世界，才附加 $b\ne c$。前四个动作在原时钟
$0,1,2,3,4$ 的迹为 $1,j,t,n,u$，第五动作 $E$ 的迹为 $s_E$。

在节点 $0,1,2,3$ 上给出四个增益值

$$
\left(-d,\frac{24-d}{j},\frac{48-d}{t},\frac{z-d}{n}\right).
$$

令 $\ell_0,\ldots,\ell_3$ 为节点 $0,1,2,3$ 的 Lagrange 基：

$$
\begin{aligned}
\ell_0(s)&=-\frac{(s-1)(s-2)(s-3)}6,&
\ell_1(s)&=\frac{s(s-2)(s-3)}2,\\
\ell_2(s)&=-\frac{s(s-1)(s-3)}2,&
\ell_3(s)&=\frac{s(s-1)(s-2)}6,
\end{aligned}
$$

并定义整个三次及以下增益

$$
g_d(s)=-d\,\ell_0(s)+\frac{24-d}{j}\ell_1(s)
+\frac{48-d}{t}\ell_2(s)+\frac{z-d}{n}\ell_3(s).
\tag{10.1}
$$

这是四个节点值的唯一插值；其中任一采样值为零、实际次数下降或出现重根都不改变定义。

**引理 10.2（时钟四、五的紧凑系数）。** 置

$$
\begin{aligned}
a_4&=1-\frac4j+\frac6t-\frac4n,&
b_4&=\frac{96}j-\frac{288}t+\frac{4z}n,\\
a_5&=4-\frac{15}j+\frac{20}t-\frac{10}n,&
b_5&=\frac{360}j-\frac{960}t+\frac{10z}n.
\end{aligned}
\tag{10.2}
$$

则

$$
g_d(4)=a_4d+b_4,\qquad g_d(5)=a_5d+b_5.
\tag{10.3}
$$

**证明。** 直接把 $s=4,5$ 代入式 (10.1)。在 $s=4$ 得到系数
$1,-4/j,6/t,-4/n$，在 $s=5$ 得到系数
$4,-15/j,20/t,-10/n$；将与 $d$ 无关的部分收集即得
式 (10.2)。这一步没有除以任何增益值。∎

**命题 10.3（第五响应的两个仿射方程）。** 定义

$$
\begin{aligned}
A_4&=1+u a_4,&B_4&=Y-u b_4,\\
A_{5,E}&=1+s_Ea_5,&B_{5,E}&=p-s_Eb_5.
\end{aligned}
\tag{10.4}
$$

给定源和 $E$，式 (10.1) 实现时钟四、五的响应 $Y,p$ 当且仅当

$$
A_4d=B_4,\qquad A_{5,E}d=B_{5,E}.
\tag{10.5}
$$

因此 $R_E=0$，其中

$$
R_E=B_4A_{5,E}-B_{5,E}A_4,
\tag{10.6}
$$

是漂移相容性的必要条件。

**证明。** 时钟四为 $d+u g_d(4)=A_4d+u b_4$，时钟五为
$d+s_Eg_d(5)=A_{5,E}d+s_Eb_5$。移项得到式 (10.5)，再交叉相减得到
式 (10.6)。∎

## 11. 两个第五动作的全局非零分母

**定理 11.1（全局漂移系数不同时消失）。** 对每个合法源和
$E\in\{J,M\}$，

$$
S_E=A_4^2+A_{5,E}^2>0.
\tag{11.1}
$$

这个结论对任意实数 $z,Y,p$ 成立；不要求 $b\ne c$，不要求 $z,Y,p$ 落在窗口中，也不要求增益的实际次数或任何采样值非零。

**证明。** 先令 $b\ge4$。因为 $j>b$、$n>j$，且 $u=2t-1$，有

$$
\begin{aligned}
A_4
&=1+u+\frac{6u}{t}-\frac{4u}{j}-\frac{4u}{n}\\
&>2t-4-\frac6t-\frac8b
\ge\frac{14}{5}>0.
\end{aligned}
\tag{11.2}
$$

这里最后一个下界在 $b=4,t=5$ 取到，右端随 $b$ 增大而增加。因此同时为零只可能在
$0<b<4$。

在此区间设

$$
\kappa=2ut,\qquad K=t^2+3u,\qquad H=t^2-18t+5.
\tag{11.3}
$$

若 $A_4=0$，则

$$
\frac1j+\frac1n=\frac K\kappa.
\tag{11.4}
$$

令

$$
D=Kn-\kappa,\qquad N=\kappa n.
\tag{11.5}
$$

由式 (11.4) 得

$$
D=\frac{\kappa n}{j}>0,\qquad j=\frac ND.
\tag{11.6}
$$

源秩一方程 $r^2-tr+bn-b^2=0$，代入 $r=n-j$，等价于

$$
j^2+(t-2n)j+n^2-n-b^2=0.
\tag{11.7}
$$

乘以 $D^2$ 后得到 $C(n,b)=0$，其中按 $n$ 的升幂排列

$$
\begin{aligned}
C(n,b)={}&-b^2\kappa^2
+\bigl(2b^2\kappa K-(t+1)\kappa^2\bigr)n\\
&+\bigl(4\kappa^2+(t+2)\kappa K-b^2K^2\bigr)n^2\\
&-\bigl(K^2+4\kappa K\bigr)n^3+K^2n^4.
\end{aligned}
\tag{11.8}
$$

若同时 $A_{5,M}=0$，将式 (11.4) 和式 (10.2) 代入并乘以
$\kappa n$，得到

$$
Q_M(n,b)=5u\kappa+(Hu+6\kappa)n+Hn^2=0.
\tag{11.9}
$$

若同时 $A_{5,J}=0$，同样消去 $j$，并乘以 $\kappa D$，得到

$$
Q_J(n,b)=-16\kappa^2+\kappa(11K-3H)n+2KHn^2=0.
\tag{11.10}
$$

下面给出不依赖根选择的整系数证书。对两个多项式都按 $n$ 的降幂写入
六阶 Sylvester 矩阵：前两行为 $C$ 的系数向右平移，后四行为 $Q_E$ 的系数向右平移，缺项补零。其行列式就是
$\operatorname{Res}_n(C,Q_E)$。式 (11.8) 的升幂系数向量为

$$
[-b^2\kappa^2,\,
2b^2\kappa K-(t+1)\kappa^2,\,
4\kappa^2+(t+2)\kappa K-b^2K^2,\,
-K^2-4\kappa K,\,
K^2],
\tag{11.11}
$$

式 (11.9) 和式 (11.10) 的升幂系数向量分别为

$$
[5u\kappa,\,Hu+6\kappa,\,H],\qquad
[-16\kappa^2,\,\kappa(11K-3H),\,2KH].
\tag{11.12}
$$

对这个显示的 $6\times6$ 行列式作整数行列式展开并按 $b$ 收集，得到

$$
\operatorname{Res}_n(C,Q_M)
=16(1+b)^2(1+2b)^4\mathcal R_M(b),
\tag{11.13}
$$

$$
\operatorname{Res}_n(C,Q_J)
=256b^2(1+b)^4(1+2b)^4(b^2+8b+4)^2\mathcal R_J(b),
\tag{11.14}
$$

其中所有系数均按 $b$ 的升幂排列：

$$
\begin{aligned}
\mathcal R_M(b)={}&71680+834560b+4266880b^2+13027456b^3\\
&+28167328b^4+49669216b^5+77097576b^6\\
&+103197064b^7+112237206b^8+93879326b^9\\
&+56647044b^{10}+22502243b^{11}+5180250b^{12}\\
&+576939b^{13}+24294b^{14}-198b^{15}-27b^{16},
\end{aligned}
\tag{11.15}
$$

$$
\begin{aligned}
\mathcal R_J(b)={}&57344+778240b+4552704b^2+15120384b^3\\
&+31699968b^4+44357120b^5+42960384b^6\\
&+29398144b^7+13939808b^8+4101632b^9\\
&+543416b^{10}-14256b^{11}-6960b^{12}\\
&-216b^{13}+9b^{14}.
\end{aligned}
\tag{11.16}
$$

Equations (11.13)–(11.16), together with the displayed Sylvester coefficient
vectors, are a finite ordinary determinant certificate: expanding the six rows
gives the left sides, and coefficient comparison with the two displayed
right sides gives the identities. No numerical root assertion enters this
calculation.

For $0<b<4$, the terms of $\mathcal R_M$ below degree $14$ are positive and its
remaining part is

$$
b^{14}(24294-198b-27b^2)
=b^{14}\bigl(23070+(4-b)(306+27b)\bigr)>0.
\tag{11.17}
$$

For $\mathcal R_J$, the terms below degree $10$ are positive,

$$
\begin{aligned}
&b^{10}(543416-14256b-6960b^2-216b^3)\\
&\qquad=b^{10}\bigl(361208+(4-b)(45552+7824b+216b^2)\bigr)>0,
\end{aligned}
\tag{11.18}
$$

and the last term is $9b^{14}>0$. Thus both resultants in
(11.13)–(11.14) are strictly positive on $0<b<4$, so $C$ has no common
root with either $Q_M$ or $Q_J$. A simultaneous zero of $A_4,A_{5,E}$
would produce precisely such a common root through (11.6)–(11.10), a
contradiction. Together with (11.2), this proves $S_E>0$. ∎

**定理 11.2（全局源到纤维的精确逆）。** 对固定的任意 $z,Y,p$、固定
$E\in\{J,M\}$ 和任意合法源，置

$$
d_E=\frac{A_4B_4+A_{5,E}B_{5,E}}{S_E}.
\tag{11.19}
$$

则该源能扩成实现第五响应 $p$ 的完整世界，当且仅当 $R_E=0$。
满足此条件时，漂移唯一为 $d_E$，整个增益唯一为式 (10.1)，第五纤维的源图
完全由 $(r,b)$ 参数化。

**证明。** 由式 (11.1) 和式 (11.19) 直接计算

$$
A_4d_E-B_4=-\frac{A_{5,E}R_E}{S_E},\qquad
A_{5,E}d_E-B_{5,E}=\frac{A_4R_E}{S_E}.
\tag{11.20}
$$

所以 $R_E=0$ 时两式 (10.5) 同时成立；反之，任一共同漂移解交叉相减即给
$R_E=0$，而式 (11.20) 给出同一唯一的 $d_E$。式 (10.1) 随后复现
时钟 $0,1,2,3$，式 (10.3) 与式 (10.5) 复现时钟 $4,5$。增益不可能恒零：
若恒零，四个节点值迫使 $d_E=0$ 和 $24=0$，矛盾。故返回的是合法完整世界。
全过程没有除以一个增益采样值、首末系数、判别式或最高次系数，所有零采样、次数下降和重根均保留。

若两个完整世界属于同一固定 $z,Y,p,E$，则它们相同当且仅当其
$(r,b)$ 相同。确实，相同的 $(r,b)$ 给出唯一 $c,j,t,n,u,s_E$，定理
11.1 给出唯一 $d_E$，式 (10.1) 给出唯一整个 $g$；反向则显然。因此
两世界不同可精确写成

$$
(r_1-r_2)^2+(b_1-b_2)^2>0.
\tag{11.21}
$$

这也是完整世界的源到世界单射和逆向恢复，不是对增益次数或漂移符号的附加假设。∎

## 12. 一个精确父点上的完整第五 M 消费者

**定义 12.1（E(z) 父曲线及其第五 J 支臂）。** 置

$$
b_z=6-\frac{336}{z},\qquad
c_z=\frac{4536-61z}{16z},\qquad
\alpha_\pm=\frac{11928\pm168\sqrt{46}}{185}.
\tag{12.1}
$$

取严格合法区间

$$
z\in(56,\alpha_-)\ \cup\ (\alpha_+,4536/61).
\tag{12.2}
$$

于是

$$
b_z>0,\qquad c_z>0,\qquad0<b_zc_z<\frac14,
$$

并令

$$
r_\pm=\frac{1\pm\sqrt{1-4b_zc_z}}2,\qquad
Y=\frac{48z-672}{35},\qquad p_J=z.
\tag{12.3}
$$

两根严格不同。对第五动作 $J$，取漂移 $d=z$ 和整个增益

$$
g_J(s)=\frac{z(s-3)(s-5)(s-7)}{105}.
\tag{12.4}
$$

其在原时钟 $0,\ldots,7$ 的增益样本为

$$
z\left(-1,-\frac{16}{35},-\frac17,0,\frac1{35},0,-\frac1{35},0\right).
\tag{12.5}
$$

由 $j=35(z-24)/(16z)$ 和 $t=7(z-48)/z$，前缀响应恰为
$0,24,48,z,Y$，第五 J 响应为 $z$。第五 J 之后，第六 J 和第六 M 的响应分别为

$$
z-\frac{(1+2b_z)z}{35},\qquad
z-\frac{(1+3b_z)z}{35},
\tag{12.6}
$$

而两种最终动作的响应都为 $z$。因此两个根分支给出第五 J 后每个第六、最终动作所需的不同世界对；该支臂是既有 E(z) 构造的精确复用。

**定义 12.2（十八变量第五 M 系统）。** 未知量为

$$
z,\ p_M,\quad (r_{EGk},b_{EGk})\quad
(E,G\in\{J,M\},\ k\in\{1,2\}),
\tag{12.7}
$$

共十八个实变量。$z$ 受式 (12.2) 的严格区间约束，$p_M$ 任意实数，并令
$Y=(48z-672)/35$。每个槽 $(E,G,k)$ 由

$$
0<r_{EGk}<1,\quad b_{EGk}>0,\quad
c_{EGk}=\frac{r_{EGk}(1-r_{EGk})}{b_{EGk}}>0
\tag{12.8}
$$

定义 $j,t,n,u,s_J,s_M$。基本系统允许 $b_{EGk}=c_{EGk}$；
若研究者另加非对称筛选，则逐槽附加 $b_{EGk}\ne c_{EGk}$，这不是源图定理的前提。

对每个槽应用定理 11.2 的 $E=M$ 情形，令

$$
R_{M,EGk}=R_M\!\left(z,Y,p_M;r_{EGk},b_{EGk}\right),\qquad
d_{EGk}=d_M\!\left(z,Y,p_M;r_{EGk},b_{EGk}\right),
\tag{12.9}
$$

并以式 (10.1) 记其整个增益为 $g_{EGk}$。系统的前八个方程是

$$
R_{M,EGk}=0\qquad(E,G\in\{J,M\},\ k=1,2).
\tag{12.10}
$$

这里 $R_M$ 是式 (10.6) 中的相容性行列式，而不是 (11.15) 的一元因子多项式 $\mathcal R_M$。

定义每个槽在第六动作后的两个实际响应

$$
\begin{aligned}
h_J(E,G,k)&=d_{EGk}+
\bigl(n_{EGk}+r_{EGk}+t_{EGk}\bigr)g_{EGk}(6),\\
h_M(E,G,k)&=d_{EGk}+
\bigl(n_{EGk}+2u_{EGk}\bigr)g_{EGk}(6).
\end{aligned}
\tag{12.11}
$$

对每个 $E$，四个槽共享同一个 $h_E$。用第一槽作参照，六个方程为

$$
\begin{aligned}
h_E(E,J,2)-h_E(E,J,1)&=0,\\
h_E(E,M,1)-h_E(E,J,1)&=0,\\
h_E(E,M,2)-h_E(E,J,1)&=0,
\end{aligned}
\qquad E\in\{J,M\}.
\tag{12.12}
$$

最后定义

$$
\begin{aligned}
f_{JJ}(E,G,k)&=d_{EGk}+(n_{EGk}+u_{EGk})g_{EGk}(7),\\
f_{JM}(E,G,k)&=d_{EGk}+(n_{EGk}+4t_{EGk}-2-r_{EGk})g_{EGk}(7),\\
f_{MJ}(E,G,k)&=d_{EGk}+(2n_{EGk}+t_{EGk}+2r_{EGk})g_{EGk}(7),\\
f_{MM}(E,G,k)&=d_{EGk}+(2n_{EGk}+3u_{EGk})g_{EGk}(7).
\end{aligned}
\tag{12.13}
$$

For each $(E,G)$, impose one final equality

$$
f_{EG}(E,G,2)-f_{EG}(E,G,1)=0,
\qquad E,G\in\{J,M\},
\tag{12.14}
$$

where $f_{EG}$ means the corresponding line of (12.13). Equations
(12.10), (12.12), and (12.14) total $8+6+4=18$ equations. In addition, every final pair has the strict distinctness guard

$$
(r_{EG1}-r_{EG2})^2+(b_{EG1}-b_{EG2})^2>0.
\tag{12.15}
$$

All guards in (12.2), (12.8), (12.15) are part of the system; no sign restriction is imposed on any $d_{EGk}$, $p_M$, gain sample, or leading coefficient.

**定理 12.3（十八方程消费者的必要性与充分性）。** The guarded system of Definition 12.2 has a solution if and only if, on the exact parent

$$
H_4(z)=\left(0,J,24,M,48,J,z,M,\frac{48z-672}{35}\right)
$$

with $z$ in (12.2), there is an unrestricted fifth M $L_2$ family whose terminal pairs are indexed by
$(E,G)\in\{J,M\}^2$, with a possibly different pair for every final action.

**证明（必要性）。** Assume the stated fifth M $L_2$ family. For each sixth action $E$, choose its actual response $h_E$ witnessing the $L_1$ clause. For each final action $G$, choose two different complete worlds in the corresponding $L_0$ leaf and label them $k=1,2$. Their source coordinates satisfy (12.8), their common fifth response is one $p_M$, and Theorem 11.2 gives (12.9)–(12.10). The actual trace table after the fifth M is

$$
\begin{array}{c|ccc}
E&\text{sixth trace}&\text{final }J\text{ trace}&\text{final }M\text{ trace}\\ \hline
J&n+r+t&n+u&n+4t-2-r\\
M&n+2u&2n+t+2r&2n+3u .
\end{array}
\tag{12.16}
$$

Thus equal sixth responses give (12.12), equal final responses give (12.14), and
distinct complete worlds give (12.15) by (11.21). No pair is forced to equal a pair under another final action; reuse is allowed precisely when the complete world itself is reused.

**证明（充分性）。** Given a solution, (12.9)–(12.10) and Theorem 11.2 construct eight legal complete worlds, all with the same $H_4(z)$ and fifth M response $p_M$. Equations (12.12) make the four worlds under each sixth action share one actual response, and (12.14) makes the two designated worlds for each final action share its actual terminal response. Guard (12.15) and (11.21) make every designated pair different. Hence the two final-action leaves under each sixth action contain an $L_0$ pair, each sixth action supplies an $L_1$ child, and the fifth M arm supplies $L_2$. Different final actions may use different pairs; the union is a set of at most eight worlds because repeated slots can be the same complete world.

The two E(z) worlds from Definition 12.1 supply the fifth J arm's $L_2$ at the same exact $z,Y$. Their union with the eight M worlds therefore supplies an $L_3$ family after the common $H_4$, using at most ten complete worlds. This is a conditional local construction: existence of a solution of the eighteen equations is not asserted. ∎

**命题 12.4（父点与祖先边界）。** The consumer of Theorem 12.3 requires the same exact $z,Y$ in both fifth arms. A fifth-M construction at a different parent cannot be substituted into this system, even when its source coordinates or responses are individually legal. A solution of the system proves only the local $H_4$ $L_3$ statement. It does not supply the earlier opposite-action fibers, their actual-response failure clauses, any original-root termination argument, the eight-versus-nine conclusion, or a nine-read upper bound. The distinctness guards and all shared literal prefixes stated in Theorem 12.3 remain necessary when those ancestor questions are later addressed.

## 13. 来源对应、普通工具与未决存在性

**命题 13.1（来源与范围对应）。** 本增补复用本卷 §§1–3 的完整世界、原时钟、迹表和四节点插值约定，复用 §§6、9 的通过坐标和失败递归语义；它把原来固定
$36<z<361/10,\ 33<Y<34$ 的 MMJ 图扩展为任意实数 $z,Y,p$ 的第五 J、第五 M 两个源图。式 (12.1)–(12.6) 的 E(z) 父曲线和第五 J 支臂对应《FIB_JMJM_PROMISED_FIBERS_AND_JOINT_EXCEPTION_GEOMETRY》中的第五 J 构造，尤其对应其第 24 节的漂移系数接口及第 31–33 节的 E(z)、终端迹和联合例外几何；本卷 §§8、9 已给出的条件性同点特化只作为语义和递归接口，不被改判。Lagrange 插值、秩一源方程、仿射消元、Sylvester 行列式和多项式根计数是标准数学工具。这里没有外部文献的新颖性、优先权或穷尽检索主张。

**证明。** 前四个量迹和增益节点直接由本卷命题 1.2、命题 2.1 的同一左乘和插值计算给出；式 (10.2) 只是把节点改为 $0,1,2,3$ 后对时钟四、五的重新收集。E(z) 的式 (12.1)–(12.6) 直接代入式 (1.2) 的迹公式，且其第五 J 两根仍由同一 $b_z,c_z$ 产生。递归接口则是本卷定义 9.1 和命题 9.2 的同一包含关系。故来源对应只说明所复用的数学对象和适用范围，不把来源文本当作本增补结论的证明。∎

**定理 13.2（本增补的未决边界）。** 定理 11.2 是同时适用于两个第五动作的全局源-only 参数化，包含对称源、任意实漂移和所有增益退化。定理 12.3 是 E(z) 同父路线的精确充分必要十八方程消费者。这里没有断言十八方程有解，没有断言任何其他第五 M 构造位于这条父曲线上，也没有断言所得局部 $L_3$ 延伸为原根结论。

**证明。** 定理 11.1 的结果式正性只排除两个漂移系数同时为零；它不制造一个满足
$R_E=0$ 的源。定理 11.2 的双向证明把存在性精确地留在行列式方程和全部源严格条件中。定理 12.3 只是把这些条件与同一父点的八个槽、六个第六响应相等式、四个最终相等式合并；方程的可解性仍是开放的。命题 12.4 列出的祖先和根层义务没有进入这十八个方程，因此也不能由它们推出。∎

## 追加锚（本行以下为增补区）

## 14. 结果式证书的显式矩阵

**命题 14.1（六阶 Sylvester 展开）。** 若

$$
C(n)=c_4n^4+c_3n^3+c_2n^2+c_1n+c_0,\qquad
Q(n)=q_2n^2+q_1n+q_0,
$$

则本增补所用的结果式是下列显示矩阵的行列式：

$$
\operatorname{Res}_n(C,Q)=
\det\begin{pmatrix}
c_4&c_3&c_2&c_1&c_0&0\\
0&c_4&c_3&c_2&c_1&c_0\\
q_2&q_1&q_0&0&0&0\\
0&q_2&q_1&q_0&0&0\\
0&0&q_2&q_1&q_0&0\\
0&0&0&q_2&q_1&q_0
\end{pmatrix}.
\tag{14.1}
$$

在 $C$ 上取

$$
(c_4,c_3,c_2,c_1,c_0)=
\bigl(K^2,-K^2-4\kappa K,\,
4\kappa^2+(t+2)\kappa K-b^2K^2,\,
2b^2\kappa K-(t+1)\kappa^2,\,-b^2\kappa^2\bigr),
$$

在 $Q_M$ 上取

$$
(q_2,q_1,q_0)=(H,Hu+6\kappa,5u\kappa),
$$

在 $Q_J$ 上取

$$
(q_2,q_1,q_0)=(2KH,\kappa(11K-3H),-16\kappa^2).
$$

把 $t=1+b,u=1+2b,\kappa=2ut,K=t^2+3u,H=t^2-18t+5$
逐项代入式 (14.1)，按 $b$ 的幂次收集，所得系数恰为式
(11.13)–(11.16) 的两个因子分解。因而这些分解是显示矩阵的整系数行列式恒等式；
它们的正性证明只使用式 (11.17)–(11.18)，不使用近似根或额外的可解性假设。∎

## 追加锚（本行以下为增补区）
