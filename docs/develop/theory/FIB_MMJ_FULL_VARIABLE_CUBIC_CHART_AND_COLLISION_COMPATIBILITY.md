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

## 10. 同一实际 MMJ 的整个比例增益分离

**定义 10.1（整个增益的比例关系）。** 两个非零三次及以下实多项式 $g_1,g_2$ 成比例，是指存在实数 $\lambda$ 使 $g_2=\lambda g_1$ 作为整个多项式恒等成立；此时 $\lambda\ne0$。这不是只在若干采样点拟合尺度。两个世界仍各有自己的源与漂移，不附加共同 $b$、共同 $d$ 或同一通过坐标的承诺。

**定理 10.2（实际 MMJ 的整个比例增益分离）。** 固定式 (1.3) 的同一个 $z,Y$。若两个合法完整世界 $W_i=(P_i,g_i,d_i)$ 实现这个同一实际父历史，且 $g_2=\lambda g_1$，则有以下结论：

1. 父历史本身已经排除 $\lambda<0$。
2. 若 $\lambda\ne1$，两世界的实际第五、第六 $M,M$ 响应对 $(p_i,v_i)$ 不同；这一排除不需要最终读数。
3. 若两世界还有相同的实际 $p,v,a$，则 $P_1=P_2,g_1=g_2,d_1=d_2$，即完整世界相同。

以上结论覆盖定义 1.1 的整个合法域及全部允许增益次数，不要求任一样本预先非零，也不对源参数或漂移加上界。

证明。对每个端点沿用命题 1.2 的 $t_i=1+b_i>1$、$u_i=2t_i-1$、$n_i=r_i+b_i+c_i>t_i-1$。全部实际方程为

$$
\begin{aligned}
g_i(0)&=-d_i,&g_i(1)(n_i-r_i)&=24-d_i,\\
g_i(2)t_i&=48-d_i,&g_i(3)n_i&=z-d_i,\\
g_i(4)u_i&=Y-d_i,\\
p_i&=d_i+g_i(5)(n_i+u_i),\\
v_i&=d_i+g_i(6)(n_i+2u_i),\\
a_i&=d_i+g_i(7)(t_i+2n_i+2r_i).
\end{aligned}
\tag{10.1}
$$

这些迹严格正，且各个端点从始至终使用自己的同一个整个增益。初读与比例关系先给

$$
d_2=\lambda d_1.
\tag{10.2}
$$

先处理 $\lambda\ne1$。若 $t_2=t_1$，时钟二的第二端点响应就是第一端点响应的 $\lambda$ 倍，故 $48=48\lambda$，矛盾。因此 $\delta_t=t_2-t_1\ne0$。将第二端点的时钟二、四方程分别减去第一端点的 $\lambda$ 倍，得到

$$
\lambda g_1(2)\delta_t=48(1-\lambda),\qquad
2\lambda g_1(4)\delta_t=Y(1-\lambda).
\tag{10.3}
$$

两右端都非零，所以这两处增益值非零。比较两式并使用整个比例关系，两个端点都必须满足

$$
96g_i(4)=Yg_i(2).
\tag{10.4}
$$

将式 (10.1) 的时钟二、四值代入，清去正的 $t_i,u_i$，给出

$$
\begin{aligned}
96t_i(Y-d_i)&=Y(2t_i-1)(48-d_i),\\
d_i\bigl[2(48-Y)t_i+Y\bigr]&=48Y,\\
d_i&=\frac{48Y}{2(48-Y)t_i+Y}.
\end{aligned}
\tag{10.5}
$$

最后的分母严格大于 $96-Y>48$，且分子正，故

$$
0<d_i<Y,\qquad\lambda=\frac{d_2}{d_1}>0,\qquad d_1\ne d_2.
\tag{10.6}
$$

这是从非单位比例分支的原响应推得的结论；没有先除以可能为零的漂移。负尺度必属此分支，式 (10.6) 已在父历史上将它排除。

现在以已经证明非零的漂移归一化同一个整个多项式：

$$
h=\frac{g_1}{d_1}=\frac{g_2}{d_2},\qquad
h(0)=-1,\qquad
\alpha=h(2)=\frac{2(48-Y)}Y,\quad
q=h(4)=\frac{48-Y}{48},\quad e=h(3).
\tag{10.7}
$$

这里 $\alpha$ 由式 (10.5) 和 $g_i(2)t_i=48-d_i$ 给出，$q=Y\alpha/96$ 由式 (10.4) 给出。窗口及实际第三祖先给

$$
\frac{14}{17}<\alpha<\frac{10}{11},\qquad
\frac45<\alpha<1,\qquad
\frac7{24}<q<\frac5{16},\qquad
e=\frac{z-d_i}{d_in_i}>0.
\tag{10.8}
$$

最后一个严格符号使用 $z>Y>d_i$ 和 $d_in_i>0$。四节点 $0,2,3,4$ 插值是

$$
\begin{aligned}
h(s)={}&\frac{(s-2)(s-3)(s-4)}{24}
 +\frac\alpha4s(s-3)(s-4)\\
&-\frac e3s(s-2)(s-4)+\frac q8s(s-2)(s-3).
\end{aligned}
\tag{10.9}
$$

四个节点取值分别为 $-1,\alpha,e,q$，与 $h$ 之差有四个不同根而次数至多三，故该恒等式对全部允许次数都成立。在节点五、六得到

$$
h(5)=Q-5e,\qquad h(6)=R-16e,\qquad
Q=\frac{10\alpha+15q+1}{4},\quad R=9\alpha+9q+1.
\tag{10.10}
$$

为使用相同的实际响应，先由两个祖先写出
$d_in_i=(z-d_i)/e$、$d_iu_i=(Y-d_i)/q$。代入式 (10.1) 后，两个响应都是相对于各自漂移的仿射式，但其整个 $h$ 相同：

$$
\begin{aligned}
p_i={}&h(5)\left(\frac ze+\frac Yq\right)
+d_i\left[1-h(5)\left(\frac1e+\frac1q\right)\right],\\
v_i={}&h(6)\left(\frac ze+\frac{2Y}q\right)
+d_i\left[1-h(6)\left(\frac1e+\frac2q\right)\right].
\end{aligned}
\tag{10.11}
$$

若 $p_1=p_2,v_1=v_2$，式 (10.6) 的不同漂移迫使两个方括号中的斜率同时为零。$e,q>0$，故

$$
h(5)=\frac{eq}{e+q},\qquad h(6)=\frac{eq}{q+2e},\qquad
0<h(5)<q.
\tag{10.12}
$$

将式 (10.10) 代入两个斜率条件，清去正分母后分别是

$$
\begin{aligned}
-5e^2+(Q-6q)e+Qq&=0,\\
-32e^2+(2R-17q)e+Rq&=0.
\end{aligned}
\tag{10.13}
$$

第一式的三十二倍减去第二式的五倍，二次项相消；余下的两个系数逐项为

$$
\begin{aligned}
32Q-10R-107q&=-(10\alpha+77q+2),\\
32Q-5R&=35\alpha+75q+3.
\end{aligned}
$$

因此

$$
-(10\alpha+77q+2)e+(35\alpha+75q+3)q=0,\qquad
e=\frac{q(35\alpha+75q+3)}{10\alpha+77q+2}.
\tag{10.14}
$$

分母严格正。仅用式 (10.8) 的整个矩形，可取以下严格有理界：

$$
\begin{aligned}
q(35\alpha+75q+3)
&<\frac5{16}\left(35+\frac{375}{16}+3\right)=\frac{4915}{256},\\
10\alpha+77q+2
&>8+\frac{539}{24}+2=\frac{779}{24},\\
e&<\frac{14745}{24928}<\frac35.
\end{aligned}
\tag{10.15}
$$

最后一个比较清正分母恰为 $73725<74784$。另一方面，

$$
Q-3-q=\frac{10\alpha+11q-11}{4}
>\frac{8+77/24-11}{4}=\frac5{96}.
\tag{10.16}
$$

同一个第五样本于是同时受到

$$
h(5)=Q-5e>Q-3>q+\frac5{96}
\quad\hbox{和}\quad h(5)<q
\tag{10.17}
$$

的约束，矛盾。这排除了非单位比例下共同的实际 $p,v$，证明第 2 项。没有在两个端点分别重拟第五或第六样本，也没有使用最终方程。

余下是 $\lambda=1$。此时 $g_1=g_2=g$，式 (10.2) 给共同漂移 $d$。样本 $g(2),g(4)$ 不会同时为零，否则式 (10.1) 要求 $d=48=Y$。两端点的偶方程相减给

$$
g(2)(t_1-t_2)=0,\qquad2g(4)(t_1-t_2)=0,
$$

故 $t_1=t_2$，并有共同的 $b,u$。

样本 $g(3),g(5),g(6)$ 也不会全零。反之，第三祖先先给 $d=z$；非零三次及以下多项式有三个不同根 $3,5,6$，配合 $g(0)=-z$，只能是

$$
g(s)=\frac z{90}(s-3)(s-5)(s-6),\qquad
g(2)=-\frac{2z}{15}<0.
\tag{10.18}
$$

这与 $g(2)t_i=48-z>0$ 矛盾。因此在 $p_1=p_2,v_1=v_2$ 时，第三、第五、第六实际方程相减所给的

$$
g(3)(n_1-n_2)=g(5)(n_1-n_2)=g(6)(n_1-n_2)=0
$$

迫使 $n_1=n_2$。

若还有共同实际 $a$，必须同时使用两端点各自的首祖先和最终方程，而非只保留末端拟合。已知共同 $t,n,g,d$ 后，这两组方程分别给

$$
g(1)(r_1-r_2)=0,\qquad2g(7)(r_1-r_2)=0.
\tag{10.19}
$$

复用本卷定理 5.1 在合法世界上的 $g(1)^2+4g(7)^2>0$，得到 $r_1=r_2$。具体地，$g(1)\ne0$ 时首方程确定 $r$；$g(1)=0$ 时定理 5.1 保证 $g(7)\ne0$，由末方程确定 $r$。若 $g(7)=0$，则仍由首方程处理，$a=d$ 不被删掉。最后 $c_i=n_i-r_i-b_i$ 相同，故整个源、增益及漂移相同。第 3 项得证；单位尺度也显然不为负，与前面的父历史排除合起来证明第 1 项。∎

**推论 10.3（不同通过坐标的严格子式必要条件）。** 将两个整个增益的系数补零写为

$$
g_i(s)=\sum_{h=0}^3 a_{ih}s^h,\qquad
\mathcal N(g_1,g_2)=
\sum_{0\le h<k\le3}(a_{1h}a_{2k}-a_{1k}a_{2h})^2.
\tag{10.20}
$$

对任意两个非零三次及以下实多项式，$\mathcal N>0$ 当且仅当它们不成比例。因而同一 $z,Y,p,v,a$ 上任意两个不同通过坐标，或任意两个不同完整世界，必须满足 $\mathcal N>0$。这只是实际 MMJ 碰撞的必要条件，不是充分条件、碰撞构造或全纤维单射性。

证明。实平方和为零当且仅当每个子式为零。取第一系数向量中一个非零分量 $a_{1\ell}$；若所有子式为零，则对每个 $k$ 都有
$a_{1\ell}a_{2k}=a_{1k}a_{2\ell}$，从而
$a_{2k}=\lambda a_{1k}$，其中 $\lambda=a_{2\ell}/a_{1\ell}$。第二向量非零保证 $\lambda\ne0$。反之，成比例立即使所有子式为零。平方和总非负，故严格正恰与不成比例等价；补零使这个论证包括常数、一次、二次和三次增益。

定理 10.2 排除不同世界的比例增益；定理 6.2 的双射又保证不同通过坐标给不同世界，因为反取 $t=1+b,x=(r+b+c)/(2t-1)$ 唯一。因此两种表述的碰撞都满足式 (10.20) 的严格条件。∎

**完整共同实现与剩余分支。** 对固定的 $z,Y$，尚未解决的是是否存在同一个实际 $p,v,a$ 和两个不同端点。一个不选择源二次根的同时系统为：对每个 $i=1,2$，保留

$$
\begin{gathered}
t_i>1,\quad x_i>0,\quad u_i=2t_i-1,\quad n_i=u_ix_i,\quad
b_i=t_i-1,\quad d_i\in\mathbb R,\quad c_i=n_i-r_i-b_i,\\
0<r_i<1,\quad c_i>0,\quad
r_i^2-t_ir_i+b_in_i-b_i^2=0.
\end{gathered}
\tag{10.21}
$$

用各自的式 (2.1)–(2.4) 定义同一个整个 $g_i$ 和 $k_i=g_i(1),\gamma_i=g_i(7)$，并同时要求

$$
\begin{aligned}
k_1(n_1-r_1)&=24-d_1,&k_2(n_2-r_2)&=24-d_2,\\
p&=d_1+g_1(5)(n_1+u_1)=d_2+g_2(5)(n_2+u_2),\\
v&=d_1+g_1(6)(n_1+2u_1)=d_2+g_2(6)(n_2+2u_2),\\
a&=d_1+\gamma_1(t_1+2n_1+2r_1)
 =d_2+\gamma_2(t_2+2n_2+2r_2),\\
(t_1-t_2)^2+(x_1-x_2)^2&>0,\qquad\mathcal N(g_1,g_2)>0.
\end{aligned}
\tag{10.22}
$$

式 (10.21) 各自保留两端的秩一与严格源条件。四节点增益各自给响应 $0,48,z,Y$，两个首祖先补上 $24$，共同 $p,v$ 和两个最终方程补上其余三读；初读和时钟二不同排除了恒零增益。因此这个系统的每个解确为原模型碰撞。反过来，原模型碰撞由推论 10.3 自动满足新增的子式条件，故系统没有删除任何真实碰撞。这只是定义 6.1 的未消元共同实现表达，不重复计入既有三次图谱的内容。

增益线性无关不决定命题 7.1 的漂移方向行列式 $\Omega$。式 (7.3) 的非平行分支及式 (7.4) 的平行分支都仍须保留，并各自通过式 (10.21)–(10.22) 的全部约束。这里既没有使剩余系统矛盾的证明，也没有构造它的合法解；独立整个增益之间的不受限碰撞仍为未决。

**零层、次数与作用范围。** 比例分支中 $t_1\ne t_2$、$96g_i(4)=Yg_i(2)$、$0<d_i<Y$、正 $e,q$ 以及两个仿射斜率为零，均只在对应的假设下推得，不是对完整目标域增加的承诺。归一化只在漂移正之后进行；式 (10.12)–(10.15) 的分母 $e,q,e+q,q+2e,10\alpha+77q+2$ 均已严格正。单位尺度的相等比较不倒置任何样本；唯一的三根因式式 (10.18) 是明确的反证分支。首末非同时零直接调用定理 5.1，不重证或扩张到未过滤坐标域。

完整域仍保留 $d=0,24,48,z,Y$ 和 $p=d,v=d,a=d$ 的合法零偏移层、其他相容的多采样零、全部增益降次与重根、坐标三次式重根和源二次式重根。源可不对称，非对角元及一般漂移无上界；$r=0,1$、$b=0$、$c=0$、$t=1$、$x=0$ 仍是非法边界。本节严格限于式 (1.3) 的开窗口，不宣称其端点或另一字面父历史的结论。

**增量定位与原目标。** 《FIB 实际 JMJM 的承诺纤维与联合例外几何》定理 4.1 已给同父历史上一个预先指定的有符号整个增益方向类至多二世界及至多三次进一步读数恢复。该类级上界没有指定用实际 $M,M,J$ 即可分离。本节新增的是在相同实际 MMJ 数据下排除整个比例增益碰撞，且非单位尺度已由共同 $p,v$ 排除，负尺度已由父历史排除。四节点插值、消元、平方子式改写以及既有三次坐标双射都是支持工具或等价表达，不另计新发现；不附外部新颖性、优先权或一般神经网络主张。

在定义 8.1 的全部有限前提下，本节可直接特化到同一个精确 $z_\star,Y_\star$；这些有限表仍是未重新计算或认证的前提，比例分离的主证明不依赖它们。定义 9.1 与命题 9.2 的完整停止护栏、两个动作分句和同时八槽条件全部保留。新必要条件只约束其中 $E=M,G=J$ 的终端碰撞对，不供应或排除不受限终叶、另一最终叶、第六 $J$ 的两个最终叶、共同第五响应或整个第五 $M$ 的 $L_2$。它也不补出更早相反动作、实际祖先和原根到达义务。

因此原域完整目标在原时钟 $0,\ldots,7$ 内至多八次总读恢复与 $n_{\rm det}(3,0)\ge9$ 的二择仍为未决。本节没有全局有限纤维结论、不受限 MMJ 逆、碰撞构造、八槽见证、同父 $L_3$、原根预算结论或九读上界。所有数学限于未执行的符号推导，不主张内核、执行算术、有限表、数值实验、一般神经网络、物理、噪声、稳定性或资源认证。

## 追加锚（本行以下为增补区）

## 11. 任意第五动作的全局源图

**定义 11.1（任意实数父历史与第五纤维）。** 本节不采用式 (1.3) 的小矩形。固定任意
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
\tag{11.1}
$$

这是四个节点值的唯一插值；其中任一采样值为零、实际次数下降或出现重根都不改变定义。

**引理 11.2（时钟四、五的紧凑系数）。** 置

$$
\begin{aligned}
a_4&=1-\frac4j+\frac6t-\frac4n,&
b_4&=\frac{96}j-\frac{288}t+\frac{4z}n,\\
a_5&=4-\frac{15}j+\frac{20}t-\frac{10}n,&
b_5&=\frac{360}j-\frac{960}t+\frac{10z}n.
\end{aligned}
\tag{11.2}
$$

则

$$
g_d(4)=a_4d+b_4,\qquad g_d(5)=a_5d+b_5.
\tag{11.3}
$$

**证明。** 直接把 $s=4,5$ 代入式 (11.1)。在 $s=4$ 得到系数
$1,-4/j,6/t,-4/n$，在 $s=5$ 得到系数
$4,-15/j,20/t,-10/n$；将与 $d$ 无关的部分收集即得
式 (11.2)。这一步没有除以任何增益值。∎

**命题 11.3（第五响应的两个仿射方程）。** 定义

$$
\begin{aligned}
A_4&=1+u a_4,&B_4&=Y-u b_4,\\
A_{5,E}&=1+s_Ea_5,&B_{5,E}&=p-s_Eb_5.
\end{aligned}
\tag{11.4}
$$

给定源和 $E$，式 (11.1) 实现时钟四、五的响应 $Y,p$ 当且仅当

$$
A_4d=B_4,\qquad A_{5,E}d=B_{5,E}.
\tag{11.5}
$$

因此 $R_E=0$，其中

$$
R_E=B_4A_{5,E}-B_{5,E}A_4,
\tag{11.6}
$$

是漂移相容性的必要条件。

**证明。** 时钟四为 $d+u g_d(4)=A_4d+u b_4$，时钟五为
$d+s_Eg_d(5)=A_{5,E}d+s_Eb_5$。移项得到式 (11.5)，再交叉相减得到
式 (11.6)。∎

## 12. 两个第五动作的全局非零分母

**定理 12.1（全局漂移系数不同时消失）。** 对每个合法源和
$E\in\{J,M\}$，

$$
S_E=A_4^2+A_{5,E}^2>0.
\tag{12.1}
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
\tag{12.2}
$$

这里最后一个下界在 $b=4,t=5$ 取到，右端随 $b$ 增大而增加。因此同时为零只可能在
$0<b<4$。

在此区间设

$$
\kappa=2ut,\qquad K=t^2+3u,\qquad H=t^2-18t+5.
\tag{12.3}
$$

若 $A_4=0$，则

$$
\frac1j+\frac1n=\frac K\kappa.
\tag{12.4}
$$

令

$$
D=Kn-\kappa,\qquad N=\kappa n.
\tag{12.5}
$$

由式 (12.4) 得

$$
D=\frac{\kappa n}{j}>0,\qquad j=\frac ND.
\tag{12.6}
$$

源秩一方程 $r^2-tr+bn-b^2=0$，代入 $r=n-j$，等价于

$$
j^2+(t-2n)j+n^2-n-b^2=0.
\tag{12.7}
$$

乘以 $D^2$ 后得到 $C(n,b)=0$，其中按 $n$ 的升幂排列

$$
\begin{aligned}
C(n,b)={}&-b^2\kappa^2
+\bigl(2b^2\kappa K-(t+1)\kappa^2\bigr)n\\
&+\bigl(4\kappa^2+(t+2)\kappa K-b^2K^2\bigr)n^2\\
&-\bigl(K^2+4\kappa K\bigr)n^3+K^2n^4.
\end{aligned}
\tag{12.8}
$$

若同时 $A_{5,M}=0$，将式 (12.4) 和式 (11.2) 代入并乘以
$\kappa n$，得到

$$
Q_M(n,b)=5u\kappa+(Hu+6\kappa)n+Hn^2=0.
\tag{12.9}
$$

若同时 $A_{5,J}=0$，同样消去 $j$，并乘以 $\kappa D$，得到

$$
Q_J(n,b)=-16\kappa^2+\kappa(11K-3H)n+2KHn^2=0.
\tag{12.10}
$$

下面给出不依赖根选择的整系数证书。对两个多项式都按 $n$ 的降幂写入
六阶 Sylvester 矩阵：前两行为 $C$ 的系数向右平移，后四行为 $Q_E$ 的系数向右平移，缺项补零。其行列式就是
$\operatorname{Res}_n(C,Q_E)$。式 (12.8) 的升幂系数向量为

$$
[-b^2\kappa^2,\,
2b^2\kappa K-(t+1)\kappa^2,\,
4\kappa^2+(t+2)\kappa K-b^2K^2,\,
-K^2-4\kappa K,\,
K^2],
\tag{12.11}
$$

式 (12.9) 和式 (12.10) 的升幂系数向量分别为

$$
[5u\kappa,\,Hu+6\kappa,\,H],\qquad
[-16\kappa^2,\,\kappa(11K-3H),\,2KH].
\tag{12.12}
$$

对这个显示的 $6\times6$ 行列式作整数行列式展开并按 $b$ 收集，得到

$$
\operatorname{Res}_n(C,Q_M)
=16(1+b)^2(1+2b)^4\mathcal R_M(b),
\tag{12.13}
$$

$$
\operatorname{Res}_n(C,Q_J)
=256b^2(1+b)^4(1+2b)^4(b^2+8b+4)^2\mathcal R_J(b),
\tag{12.14}
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
\tag{12.15}
$$

$$
\begin{aligned}
\mathcal R_J(b)={}&57344+778240b+4552704b^2+15120384b^3\\
&+31699968b^4+44357120b^5+42960384b^6\\
&+29398144b^7+13939808b^8+4101632b^9\\
&+543416b^{10}-14256b^{11}-6960b^{12}\\
&-216b^{13}+9b^{14}.
\end{aligned}
\tag{12.16}
$$

Equations (12.13)–(12.16), together with the displayed Sylvester coefficient
vectors, are a finite ordinary determinant certificate: expanding the six rows
gives the left sides, and coefficient comparison with the two displayed
right sides gives the identities. No numerical root assertion enters this
calculation.

For $0<b<4$, the terms of $\mathcal R_M$ below degree $14$ are positive and its
remaining part is

$$
b^{14}(24294-198b-27b^2)
=b^{14}\bigl(23070+(4-b)(306+27b)\bigr)>0.
\tag{12.17}
$$

For $\mathcal R_J$, the terms below degree $10$ are positive,

$$
\begin{aligned}
&b^{10}(543416-14256b-6960b^2-216b^3)\\
&\qquad=b^{10}\bigl(361208+(4-b)(45552+7824b+216b^2)\bigr)>0,
\end{aligned}
\tag{12.18}
$$

and the last term is $9b^{14}>0$. Thus both resultants in
(12.13)–(12.14) are strictly positive on $0<b<4$, so $C$ has no common
root with either $Q_M$ or $Q_J$. A simultaneous zero of $A_4,A_{5,E}$
would produce precisely such a common root through (12.6)–(12.10), a
contradiction. Together with (12.2), this proves $S_E>0$. ∎

**定理 12.2（全局源到纤维的精确逆）。** 对固定的任意 $z,Y,p$、固定
$E\in\{J,M\}$ 和任意合法源，置

$$
d_E=\frac{A_4B_4+A_{5,E}B_{5,E}}{S_E}.
\tag{12.19}
$$

则该源能扩成实现第五响应 $p$ 的完整世界，当且仅当 $R_E=0$。
满足此条件时，漂移唯一为 $d_E$，整个增益唯一为式 (11.1)，第五纤维的源图
完全由 $(r,b)$ 参数化。

**证明。** 由式 (12.1) 和式 (12.19) 直接计算

$$
A_4d_E-B_4=-\frac{A_{5,E}R_E}{S_E},\qquad
A_{5,E}d_E-B_{5,E}=\frac{A_4R_E}{S_E}.
\tag{12.20}
$$

所以 $R_E=0$ 时两式 (11.5) 同时成立；反之，任一共同漂移解交叉相减即给
$R_E=0$，而式 (12.20) 给出同一唯一的 $d_E$。式 (11.1) 随后复现
时钟 $0,1,2,3$，式 (11.3) 与式 (11.5) 复现时钟 $4,5$。增益不可能恒零：
若恒零，四个节点值迫使 $d_E=0$ 和 $24=0$，矛盾。故返回的是合法完整世界。
全过程没有除以一个增益采样值、首末系数、判别式或最高次系数，所有零采样、次数下降和重根均保留。

若两个完整世界属于同一固定 $z,Y,p,E$，则它们相同当且仅当其
$(r,b)$ 相同。确实，相同的 $(r,b)$ 给出唯一 $c,j,t,n,u,s_E$，定理
12.1 给出唯一 $d_E$，式 (11.1) 给出唯一整个 $g$；反向则显然。因此
两世界不同可精确写成

$$
(r_1-r_2)^2+(b_1-b_2)^2>0.
\tag{12.21}
$$

这也是完整世界的源到世界单射和逆向恢复，不是对增益次数或漂移符号的附加假设。∎

## 13. 一个精确父点上的完整第五 M 消费者

**定义 13.1（E(z) 父曲线及其第五 J 支臂）。** 置

$$
b_z=6-\frac{336}{z},\qquad
c_z=\frac{4536-61z}{16z},\qquad
\alpha_\pm=\frac{11928\pm168\sqrt{46}}{185}.
\tag{13.1}
$$

取严格合法区间

$$
z\in(56,\alpha_-)\ \cup\ (\alpha_+,4536/61).
\tag{13.2}
$$

于是

$$
b_z>0,\qquad c_z>0,\qquad0<b_zc_z<\frac14,
$$

并令

$$
r_\pm=\frac{1\pm\sqrt{1-4b_zc_z}}2,\qquad
Y=\frac{48z-672}{35},\qquad p_J=z.
\tag{13.3}
$$

两根严格不同。对第五动作 $J$，取漂移 $d=z$ 和整个增益

$$
g_J(s)=\frac{z(s-3)(s-5)(s-7)}{105}.
\tag{13.4}
$$

其在原时钟 $0,\ldots,7$ 的增益样本为

$$
z\left(-1,-\frac{16}{35},-\frac17,0,\frac1{35},0,-\frac1{35},0\right).
\tag{13.5}
$$

由 $j=35(z-24)/(16z)$ 和 $t=7(z-48)/z$，前缀响应恰为
$0,24,48,z,Y$，第五 J 响应为 $z$。第五 J 之后，第六 J 和第六 M 的响应分别为

$$
z-\frac{(1+2b_z)z}{35},\qquad
z-\frac{(1+3b_z)z}{35},
\tag{13.6}
$$

而两种最终动作的响应都为 $z$。因此两个根分支给出第五 J 后每个第六、最终动作所需的不同世界对；该支臂是既有 E(z) 构造的精确复用。

**定义 13.2（十八变量第五 M 系统）。** 未知量为

$$
z,\ p_M,\quad (r_{EGk},b_{EGk})\quad
(E,G\in\{J,M\},\ k\in\{1,2\}),
\tag{13.7}
$$

共十八个实变量。$z$ 受式 (13.2) 的严格区间约束，$p_M$ 任意实数，并令
$Y=(48z-672)/35$。每个槽 $(E,G,k)$ 由

$$
0<r_{EGk}<1,\quad b_{EGk}>0,\quad
c_{EGk}=\frac{r_{EGk}(1-r_{EGk})}{b_{EGk}}>0
\tag{13.8}
$$

定义 $j,t,n,u,s_J,s_M$。基本系统允许 $b_{EGk}=c_{EGk}$；
若研究者另加非对称筛选，则逐槽附加 $b_{EGk}\ne c_{EGk}$，这不是源图定理的前提。

对每个槽应用定理 12.2 的 $E=M$ 情形，令

$$
R_{M,EGk}=R_M\!\left(z,Y,p_M;r_{EGk},b_{EGk}\right),\qquad
d_{EGk}=d_M\!\left(z,Y,p_M;r_{EGk},b_{EGk}\right),
\tag{13.9}
$$

并以式 (11.1) 记其整个增益为 $g_{EGk}$。系统的前八个方程是

$$
R_{M,EGk}=0\qquad(E,G\in\{J,M\},\ k=1,2).
\tag{13.10}
$$

这里 $R_M$ 是式 (11.6) 中的相容性行列式，而不是 (12.15) 的一元因子多项式 $\mathcal R_M$。

定义每个槽在第六动作后的两个实际响应

$$
\begin{aligned}
h_J(E,G,k)&=d_{EGk}+
\bigl(n_{EGk}+r_{EGk}+t_{EGk}\bigr)g_{EGk}(6),\\
h_M(E,G,k)&=d_{EGk}+
\bigl(n_{EGk}+2u_{EGk}\bigr)g_{EGk}(6).
\end{aligned}
\tag{13.11}
$$

对每个 $E$，四个槽共享同一个 $h_E$。用第一槽作参照，六个方程为

$$
\begin{aligned}
h_E(E,J,2)-h_E(E,J,1)&=0,\\
h_E(E,M,1)-h_E(E,J,1)&=0,\\
h_E(E,M,2)-h_E(E,J,1)&=0,
\end{aligned}
\qquad E\in\{J,M\}.
\tag{13.12}
$$

最后定义

$$
\begin{aligned}
f_{JJ}(E,G,k)&=d_{EGk}+(n_{EGk}+u_{EGk})g_{EGk}(7),\\
f_{JM}(E,G,k)&=d_{EGk}+(n_{EGk}+4t_{EGk}-2-r_{EGk})g_{EGk}(7),\\
f_{MJ}(E,G,k)&=d_{EGk}+(2n_{EGk}+t_{EGk}+2r_{EGk})g_{EGk}(7),\\
f_{MM}(E,G,k)&=d_{EGk}+(2n_{EGk}+3u_{EGk})g_{EGk}(7).
\end{aligned}
\tag{13.13}
$$

For each $(E,G)$, impose one final equality

$$
f_{EG}(E,G,2)-f_{EG}(E,G,1)=0,
\qquad E,G\in\{J,M\},
\tag{13.14}
$$

where $f_{EG}$ means the corresponding line of (13.13). Equations
(13.10), (13.12), and (13.14) total $8+6+4=18$ equations. In addition, every final pair has the strict distinctness guard

$$
(r_{EG1}-r_{EG2})^2+(b_{EG1}-b_{EG2})^2>0.
\tag{13.15}
$$

All guards in (13.2), (13.8), (13.15) are part of the system; no sign restriction is imposed on any $d_{EGk}$, $p_M$, gain sample, or leading coefficient.

**定理 13.3（十八方程消费者的必要性与充分性）。** The guarded system of Definition 13.2 has a solution if and only if, on the exact parent

$$
H_4(z)=\left(0,J,24,M,48,J,z,M,\frac{48z-672}{35}\right)
$$

with $z$ in (13.2), there is an unrestricted fifth M $L_2$ family whose terminal pairs are indexed by
$(E,G)\in\{J,M\}^2$, with a possibly different pair for every final action.

**证明（必要性）。** Assume the stated fifth M $L_2$ family. For each sixth action $E$, choose its actual response $h_E$ witnessing the $L_1$ clause. For each final action $G$, choose two different complete worlds in the corresponding $L_0$ leaf and label them $k=1,2$. Their source coordinates satisfy (13.8), their common fifth response is one $p_M$, and Theorem 12.2 gives (13.9)–(13.10). The actual trace table after the fifth M is

$$
\begin{array}{c|ccc}
E&\text{sixth trace}&\text{final }J\text{ trace}&\text{final }M\text{ trace}\\ \hline
J&n+r+t&n+u&n+4t-2-r\\
M&n+2u&2n+t+2r&2n+3u .
\end{array}
\tag{13.16}
$$

Thus equal sixth responses give (13.12), equal final responses give (13.14), and
distinct complete worlds give (13.15) by (12.21). No pair is forced to equal a pair under another final action; reuse is allowed precisely when the complete world itself is reused.

**证明（充分性）。** Given a solution, (13.9)–(13.10) and Theorem 12.2 construct eight legal complete worlds, all with the same $H_4(z)$ and fifth M response $p_M$. Equations (13.12) make the four worlds under each sixth action share one actual response, and (13.14) makes the two designated worlds for each final action share its actual terminal response. Guard (13.15) and (12.21) make every designated pair different. Hence the two final-action leaves under each sixth action contain an $L_0$ pair, each sixth action supplies an $L_1$ child, and the fifth M arm supplies $L_2$. Different final actions may use different pairs; the union is a set of at most eight worlds because repeated slots can be the same complete world.

The two E(z) worlds from Definition 13.1 supply the fifth J arm's $L_2$ at the same exact $z,Y$. Their union with the eight M worlds therefore supplies an $L_3$ family after the common $H_4$, using at most ten complete worlds. This is a conditional local construction: existence of a solution of the eighteen equations is not asserted. ∎

**命题 13.4（父点与祖先边界）。** The consumer of Theorem 13.3 requires the same exact $z,Y$ in both fifth arms. A fifth-M construction at a different parent cannot be substituted into this system, even when its source coordinates or responses are individually legal. A solution of the system proves only the local $H_4$ $L_3$ statement. It does not supply the earlier opposite-action fibers, their actual-response failure clauses, any original-root termination argument, the eight-versus-nine conclusion, or a nine-read upper bound. The distinctness guards and all shared literal prefixes stated in Theorem 13.3 remain necessary when those ancestor questions are later addressed.

## 14. 来源对应、普通工具与未决存在性

**命题 14.1（来源与范围对应）。** 本增补复用本卷 §§1–3 的完整世界、原时钟、迹表和四节点插值约定，复用 §§6、9 的通过坐标和失败递归语义；它把原来固定
$36<z<361/10,\ 33<Y<34$ 的 MMJ 图扩展为任意实数 $z,Y,p$ 的第五 J、第五 M 两个源图。式 (13.1)–(13.6) 的 E(z) 父曲线和第五 J 支臂对应《FIB_JMJM_PROMISED_FIBERS_AND_JOINT_EXCEPTION_GEOMETRY》中的第五 J 构造，尤其对应其第 24 节的漂移系数接口及第 31–33 节的 E(z)、终端迹和联合例外几何；本卷 §§8、9 已给出的条件性同点特化只作为语义和递归接口，不被改判。Lagrange 插值、秩一源方程、仿射消元、Sylvester 行列式和多项式根计数是标准数学工具。这里没有外部文献的新颖性、优先权或穷尽检索主张。

**证明。** 前四个量迹和增益节点直接由本卷命题 1.2、命题 2.1 的同一左乘和插值计算给出；式 (11.2) 只是把节点改为 $0,1,2,3$ 后对时钟四、五的重新收集。E(z) 的式 (13.1)–(13.6) 直接代入式 (1.2) 的迹公式，且其第五 J 两根仍由同一 $b_z,c_z$ 产生。递归接口则是本卷定义 9.1 和命题 9.2 的同一包含关系。故来源对应只说明所复用的数学对象和适用范围，不把来源文本当作本增补结论的证明。∎

**定理 14.2（本增补的未决边界）。** 定理 12.2 是同时适用于两个第五动作的全局源-only 参数化，包含对称源、任意实漂移和所有增益退化。定理 13.3 是 E(z) 同父路线的精确充分必要十八方程消费者。这里没有断言十八方程有解，没有断言任何其他第五 M 构造位于这条父曲线上，也没有断言所得局部 $L_3$ 延伸为原根结论。

**证明。** 定理 12.1 的结果式正性只排除两个漂移系数同时为零；它不制造一个满足
$R_E=0$ 的源。定理 12.2 的双向证明把存在性精确地留在行列式方程和全部源严格条件中。定理 13.3 只是把这些条件与同一父点的八个槽、六个第六响应相等式、四个最终相等式合并；方程的可解性仍是开放的。命题 13.4 列出的祖先和根层义务没有进入这十八个方程，因此也不能由它们推出。∎

## 追加锚（本行以下为增补区）

## 15. 结果式证书的显式矩阵

**命题 15.1（六阶 Sylvester 展开）。** 若

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
\tag{15.1}
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
逐项代入式 (15.1)，按 $b$ 的幂次收集，所得系数恰为式
(12.13)–(12.16) 的两个因子分解。因而这些分解是显示矩阵的整系数行列式恒等式；
它们的正性证明只使用式 (12.17)–(12.18)，不使用近似根或额外的可解性假设。∎

## 追加锚（本行以下为增补区）

## 16. E 父曲线上十八行的有理仿射编译

**定义 16.1（源槽、父区间与系数行）。** 记定义 13.1 的两个开区间之并为 $I=I_-\cup I_+$，其中

$$
I_-=(56,\alpha_-),\quad I_+=(\alpha_+,4536/61),\quad
K(z)=185z^2-23856z+762048.
\tag{16.1}
$$

等价的父点检验是 $56<z<4536/61$ 且 $K(z)>0$。确实，$K$ 的两个根是 $\alpha_\pm$，且首项系数为正。以下只使用定义 13.2 的八个源槽
$s=((r_{EGk},b_{EGk}))$，共十六个实坐标。每槽均置

$$
c=\frac{r(1-r)}b,\quad j=b+c,\quad t=1+b,\quad n=r+j,\quad
u=1+2b,\quad \sigma=n+u,
\quad 0<r<1,\quad b>0.
\tag{16.2}
$$

每个终端对保留

$$
\rho_{EG}=(r_{EG1}-r_{EG2})^2+(b_{EG1}-b_{EG2})^2>0.
\tag{16.3}
$$

这些条件允许 $b=c$。行向量作用于 $\xi=(z,p_M,1)^T$，记
$e_0=(0,0,1)$、$e_z=(1,0,0)$。在每槽内，用式 (11.2)、(11.4) 的源系数

$$
\begin{aligned}
a_4&=1-4/j+6/t-4/n,&a_5&=4-15/j+20/t-10/n,\\
A_4&=1+ua_4,&A_5&=1+\sigma a_5,\qquad S=A_4^2+A_5^2
\end{aligned}
$$

定义下列全部有理行：

$$
\begin{aligned}
L_4&=(48/35-4u/n, 0, u(288/t-96/j)-672/35),\\
L_5&=(-10\sigma/n, 1, \sigma(960/t-360/j)),\\
D&=(A_4L_4+A_5L_5)/S,\qquad T=A_5L_4-A_4L_5,\\
Q_0&=-D,\quad Q_1=(-D+24e_0)/j,\quad
Q_2=(-D+48e_0)/t,\quad Q_3=(-D+e_z)/n,\\
U_6&=-10Q_0+36Q_1-45Q_2+20Q_3,\\
U_7&=-20Q_0+70Q_1-84Q_2+35Q_3,\\
H_J&=D+(n+r+t)U_6,\qquad H_M=D+(n+2u)U_6,\\
F_{JJ}&=D+(n+u)U_7,\qquad
F_{JM}=D+(n+4t-2-r)U_7,\\
F_{MJ}&=D+(2n+t+2r)U_7,\qquad
F_{MM}=D+(2n+3u)U_7.
\end{aligned}
\tag{16.4}
$$

这里 $S>0$ 直接采用定理 12.1，不另加假设或重新证明。每个有理行只依赖自己的源槽；同一符号在不同槽上分别计算。

**命题 16.2（显式 $18\times3$ 编译与原系统的对应）。** 按以下次序组成矩阵 $L(s)$：先列八个 $T$ 行；再对每个 $E\in\{J,M\}$ 列三个

$$
H_E(s_{EGk})-H_E(s_{EJ1}),\qquad (G,k)\ne(J,1);
$$

最后列四个

$$
F_{EG}(s_{EG2})-F_{EG}(s_{EG1}),\qquad E,G\in\{J,M\}.
\tag{16.5}
$$

于是定义 13.2 的十八个等式恰为

$$
L(s)(z,p_M,1)^T=0.
\tag{16.6}
$$

它们的全部严格护栏恰为式 (16.1)–(16.3)。从解恢复的每个世界为

$$
d=D\xi,\qquad g(s')=\sum_{i=0}^3(Q_i\xi)\ell_i(s'),\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
Y=(48z-672)/35.
\tag{16.7}
$$

其中 $\ell_i$ 是定义 11.1 的同一四节点基。所有后续样本都由这个整个 $g$ 计算。

证明。代入父关系，式 (11.4) 的 $B_4,B_{5,M}$ 分别是 $L_4\xi,L_5\xi$。所以 $T\xi$ 正是式 (11.6) 的残差，$D\xi$ 正是式 (12.19) 的漂移。四个 $Q_i\xi$ 是原时钟 $0,1,2,3$ 的插值节点值。将 $6,7$ 代入相同的四个基，系数分别是 $(-10,36,-45,20)$、$(-20,70,-84,35)$，得到 $U_6,U_7$。将这些值乘以式 (13.16) 的实际迹即给 $H_E,F_{EG}$。故式 (16.5) 逐行对应式 (13.10)、(13.12)、(13.14)，没有额外响应或独立样本。定理 12.2 给全部源到世界的恢复与单射性，故式 (16.3) 恰是终端完整目标不同。式 (16.6) 因而是定理 13.3 的同一个消费者的系数编译。其局部递归含义只调用该定理，不另复制其存在性前提。∎

**定义 16.3（可消费的采样与次数行）。** 对任意实 $q$，根条件 $g(q)=0$ 在本图中就是
$\bigl(\sum_i\ell_i(q)Q_i\bigr)\xi=0$。整个增益的系数行是

$$
\begin{aligned}
C_0&=Q_0,\\
C_1&=(-11Q_0+18Q_1-9Q_2+2Q_3)/6,\\
C_2&=(2Q_0-5Q_1+4Q_2-Q_3)/2,\\
C_3&=(-Q_0+3Q_1-3Q_2+Q_3)/6.
\end{aligned}
\tag{16.8}
$$

因此 $g(s')=\sum_{h=0}^3(C_h\xi)(s')^h$。这些行只用于指定或检验某一槽的分层；不要求各槽有共同根或共同次数。式 (16.8) 由显示的四个 Lagrange 基展开而得，故亦包含重根、最高次项为零及所有采样零。

## 17. 全部秩层、两行支图与精确盒接口

**定理 17.1（十六源的全秩相容判据）。** 写 $L=[A\ e]$，其中 $A$ 有两列，$e$ 是常数列。源护栏 (16.2)–(16.3) 始终保留。

若 $\operatorname{rank}A=2$，置

$$
G=A^TA=\begin{pmatrix}g_{11}&g_{12}\\g_{12}&g_{22}\end{pmatrix},\quad
w=A^Te=\binom{w_1}{w_2},\quad
\Delta=g_{11}g_{22}-g_{12}^2>0,
$$

$$
\Phi=\Delta e^Te-g_{22}w_1^2+2g_{12}w_1w_2-g_{11}w_2^2.
\tag{17.1}
$$

则存在合法父点和第五响应的充分必要条件是 $\Phi=0$ 且

$$
z=\frac{g_{12}w_2-g_{22}w_1}{\Delta}\in I.
\tag{17.2}
$$

响应唯一，且 $p_M=(g_{12}w_1-g_{11}w_2)/\Delta$。有精确恒等式

$$
\Phi=\det(L^TL)=
\sum_{1\le i<j<k\le18}\det(L_{[i,j,k]})^2
=\Delta\|A(z,p_M)^T+e\|_2^2\ge0.
\tag{17.3}
$$

若 $\operatorname{rank}A=1$，任选 $A$ 的一个非零列 $a$，置

$$
\Psi=\|a\|_2^2\|e\|_2^2-(a^Te)^2,\quad
\alpha=\frac{a^TA_{:1}}{\|a\|_2^2},\quad
\beta=\frac{a^TA_{:2}}{\|a\|_2^2},\quad
\gamma=-\frac{a^Te}{\|a\|_2^2}.
\tag{17.4}
$$

相容性恰为 $\Psi=0$，然后全部响应恰由
$\alpha z+\beta p_M=\gamma$ 给出。若 $\beta\ne0$，可任选 $z\in I$ 并取
$p_M=(\gamma-\alpha z)/\beta$。若 $\beta=0$，则 $\alpha\ne0$，必须检验 $z=\gamma/\alpha\in I$，而 $p_M$ 自由。

若 $\operatorname{rank}A=0$，相容性恰为 $e=0$；此时任选 $z\in I,p_M\in\mathbb R$。这三种情形穷尽全部源支，包含 $A$ 的任一列恒零。

证明。秩二时令 $\theta=-G^{-1}w$。正规方程给 $A^T(A\theta+e)=0$，展开平方得到
$\Delta\|A\theta+e\|_2^2=\Phi$。所以 $\Phi=0$ 当且仅当全部十八残差为零；解的唯一性来自 $A$ 的列独立，逆矩阵给式 (17.2) 及 $p_M$。块行列式给第一恒等式，Cauchy–Binet 给其 $\binom{18}{3}=816$ 个平方子式展开。这些标准恒等式在这里承担具体十八行的相容检验。

秩一时两个系数列分别为 $\alpha a,\beta a$。正交分解
$e=((a^Te)/\|a\|^2)a+e_\perp$ 给 $\Psi=\|a\|^2\|e_\perp\|^2$。所以相容恰是 $e_\perp=0$，余下一条标量方程正是所述直线。至少一个系数非零，其与 $I\times\mathbb R$ 的交集逐分支如上。秩零时原等式就是 $e=0$。在各支最后代入命题 16.2，所得是同一实际父点与实际第五响应，而非分别拟合的父点。∎

**定理 17.2（全部 $153$ 个两行支图及正则性）。** 对每个 $1\le i<j\le18$，在
$\delta_{ij}=\det(A_{[i,j]})\ne0$ 的开集上令

$$
k=L_i\mathbin{\times}L_j=(k_1,k_2,k_3),\qquad k_3=\delta_{ij},\qquad
z(s)=k_1/\delta_{ij},\quad p(s)=k_2/\delta_{ij}.
\tag{17.5}
$$

对其余十六行逐一保留方程

$$
Q_\ell(s)=L_\ell(s)\cdot k(s)=0,\qquad \ell\notin\{i,j\}.
\tag{17.6}
$$

这给出 $\binom{18}{2}=153$ 个明确的有理十六方程支图；只使用各自非零的支点，不主张每一支点域都非空。它们覆盖定理 17.1 的全部秩二层，每支与式 (16.6) 等价，另保留原源、终端对护栏及 $z(s)\in I$。支点可正可负，父区间总在比值上检验。

在任一解处，令 $F(s,\theta)=A(s)\theta+e(s)$。把两个支点行移到最前，把变量按 $(\theta,s)$ 排列，且将其余行和 $s$ 的次序固定一致，则

$$
\det D_{(\theta,s)}F
=\delta_{ij}\det D_s\bigl(F_{\rm rem}(s,\theta(s))\bigr)
=\delta_{ij}^{-15}\det D_sQ.
\tag{17.7}
$$

因此原十八变量系统与本支十六变量系统在零点的非奇异性等价。其他行列排序只改变符号。

证明。$k$ 与两个支点行正交，且 $k_3=\delta_{ij}$，所以它们唯一解出 $\theta(s)=(z(s),p(s))$。每个余下残差恰为 $Q_\ell/\delta_{ij}$。秩二总有一个非零二阶行子式，所以这些支图完备。对导数，支点对 $\theta$ 的块是可逆的 $A_{[i,j]}$。隐式消去 $\theta$ 的 Schur 补给式 (17.7) 第一等号。在零点处
$Q=\delta_{ij}F_{\rm rem}(s,\theta(s))$，故 $D_sQ=\delta_{ij}D_sF_{\rm rem}$；十六阶行列式给第二等号。此论证只在明确非零支点上除法，秩一与秩零仍由定理 17.1 处理。∎

**命题 17.3（本支图的有理盒充分证书）。** 在一个指定支图内，给定有理中心 $s_0$、有理 $\varepsilon>0$、有理 $16\times16$ 矩阵 $C$ 和闭盒
$B=\{s:\|s-s_0\|_\infty\le\varepsilon\}$。假设在整个盒上严格成立源护栏、全部 $\rho_{EG}>0$、$\delta_{ij}\ne0$，且式 (17.5) 的 $z(s)$ 始终落在同一个 $I_-$ 或 $I_+$。所有源正分母与 $S$ 在盒上均有正下界。若有有理数 $q<1$ 使

$$
\sup_{s\in B}\|I-CDQ(s)\|_\infty\le q,\qquad
\eta=\|CQ(s_0)\|_\infty,\qquad \eta+q\varepsilon<\varepsilon,
\tag{17.8}
$$

则盒内存在唯一 $Q$ 零点。该同一零点经式 (17.5)、(16.7) 恢复同一精确父点和全部八个世界，故由定理 13.3 消费为所述局部构造。

证明。$T(s)=s-CQ(s)$ 沿盒内线段的导数界使其为 $q$-收缩，且
$\|T(s)-s_0\|\le q\varepsilon+\eta<\varepsilon$，故它是完备闭盒的严格自映射。收缩原理给唯一不动点。在中心 $\|I-CDQ(s_0)\|<1$，几何级数表明 $CDQ(s_0)$ 可逆，从而方阵 $C$ 可逆。因此不动点的 $CQ=0$ 等价于 $Q=0$；每个零点反过来是不动点。护栏使恢复合法，消费者遂适用。式 (17.8) 是一个待满足的充分接口，这里没有指定满足它的盒或主张存在实际零点。另由式 (17.3) 的平方和，$\Phi$ 在相容内点的梯度为零；因此这个方阵接口使用十六个 $Q_\ell$，不把单一 $\Phi$ 当作十六方程的替代。∎

## 18. 两个第五支臂的共同父点消元

**定义 18.1（齐次父响应与全部实际迹）。** 本节不限制 $z,Y$ 位于 E 曲线。用齐次变量 $a$ 表示原时钟一的响应，父历史写为
$(0,J,a,M,2a,J,z,M,Y)$，最后固定 $a=24$。每个第五动作 $F\in\{J,M\}$ 各有八个源槽 $s_{FEGk}$，$E,G\in\{J,M\},k=1,2$，共三十二个源坐标。每槽采用式 (16.2) 的严格源条件，每个 $(F,E,G)$ 保留式 (16.3) 的不同源对条件。第五迹为 $s_J=n+r$、$s_M=n+u$。后两步的全部迹为

$$
\begin{array}{c|c|c|c|c}
F&E&\tau_6&\tau_{7,J}&\tau_{7,M}\\ \hline
J&J&u&n+r&n+u\\
J&M&1+3b&n+2r&n+r+1+3b\\
M&J&n+r+t&n+u&n+4t-2-r\\
M&M&n+2u&2n+t+2r&2n+3u
\end{array}
\tag{18.1}
$$

所有列都在该槽自己的源上计算。对应第五之后的左乘矩阵分别为

$$
\begin{aligned}
A_{5,J}&=\begin{pmatrix}2&1\\1&0\end{pmatrix},&
A_{5,M}&=\begin{pmatrix}2&1\\3&1\end{pmatrix},\\
A_{6,JJ}&=\begin{pmatrix}1&0\\2&1\end{pmatrix},&
A_{6,JM}&=\begin{pmatrix}1&0\\3&1\end{pmatrix},\\
A_{6,MJ}&=\begin{pmatrix}3&1\\2&1\end{pmatrix},&
A_{6,MM}&=\begin{pmatrix}3&1\\5&2\end{pmatrix}.
\end{aligned}
\tag{18.2}
$$

各 $A_7$ 是 $JA_6$ 或 $MA_6$；代入式 (1.7) 直接给表 (18.1)。这些矩阵只计算原动作后的迹，不表示同时获取两个反事实读数。

**定义 18.2（齐次 $18\times4$ 支臂矩阵）。** 对每个源令

$$
\begin{aligned}
\alpha_4&=1-4/j+6/t-4/n,&\beta_4&=(4/j-12/t)a+4z/n,\\
\alpha_5&=4-15/j+20/t-10/n,&\beta_5&=(15/j-40/t)a+10z/n,\\
\alpha_6&=10-36/j+45/t-20/n,&\beta_6&=(36/j-90/t)a+20z/n,\\
\alpha_7&=20-70/j+84/t-35/n,&\beta_7&=(70/j-168/t)a+35z/n.
\end{aligned}
\tag{18.3}
$$

固定支臂 $F$，在该槽置

$$
\begin{aligned}
A_4&=1+u\alpha_4,\quad A_{5,F}=1+s_F\alpha_5,\quad
S_F=A_4^2+A_{5,F}^2,\\
B_4&=Y-u\beta_4,\quad B_5=p_F-s_F\beta_5,\\
\mathscr D&=A_4B_4+A_{5,F}B_5,\quad
\mathscr R=A_{5,F}B_4-A_4B_5,\\
\mathscr V_i(\tau)&=(1+\tau\alpha_i)\mathscr D+S_F\tau\beta_i,\qquad i=6,7.
\end{aligned}
\tag{18.4}
$$

$\mathscr D,\mathscr R,\mathscr V$ 都是 $(a,z,Y,p_F)$ 的齐次线性式，而 $S_F$ 只依赖源并由定理 12.1 严格正。令 $K_F$ 是作用于 $(a,z,Y,p_F)^T$ 的十八行矩阵：八个 $\mathscr R$ 行；对每个 $E$ 以槽 $o=(F,E,J,1)$ 为基准，对其余三槽 $i$ 各列

$$
S_o\mathscr V_{6,i}(\tau_{6,i})-S_i\mathscr V_{6,o}(\tau_{6,o});
$$

对每个 $(E,G)$ 的两槽再列

$$
S_1\mathscr V_{7,2}(\tau_{7,G,2})-S_2\mathscr V_{7,1}(\tau_{7,G,1}).
\tag{18.5}
$$

此处 $S_i$ 是相应槽的 $S_F$。写 $K_F=[B_F\mid w_F]$，其中 $B_F$ 是 $(a,z,Y)$ 三列，$w_F$ 是该支臂私有的 $p_F$ 列。

**命题 18.3（正分母交叉相乘与支臂重建）。** 在 $a=24$ 时，$K_F(a,z,Y,p_F)^T=0$ 与这八槽按指定 $(E,G,k)$ 实现同一实际第五 $F$ 响应纤维中的 $L_2$ 见证等价。其世界唯一由

$$
d=\mathscr D/S_F,\qquad
g(s')=-d\ell_0(s')+\frac{a-d}{j}\ell_1(s')
+\frac{2a-d}{t}\ell_2(s')+\frac{z-d}{n}\ell_3(s')
\tag{18.6}
$$

恢复。实际第六、七响应分别为 $\mathscr V_i(\tau_i)/S_F$。

证明。对式 (18.6) 在 $4,5,6,7$ 求值得 $g(i)=\alpha_i d+\beta_i$。定理 12.2 的残差恒等式在这些源上直接适用，故 $\mathscr R=0$ 恰使同一个 $d=\mathscr D/S_F$ 复现第四、第五响应。其余响应代入即是式 (18.4) 的 $\mathscr V/S_F$。每个 $S_F>0$，所以式 (18.5) 与实际响应相等完全等价，未引入分母零解。八个源条件、六个第六差和四个最终差的语义为命题 9.2 的同一八槽接口，对 $F=J$ 只把迹换成表 (18.1)。非零增益由时钟零和时钟一的 $0,24$ 排除恒零；源对不同由定理 12.2 恰等价于完整世界不同。所有恢复均从四节点确定一个整个多项式。∎

**定理 18.4（私有响应消元与共同父点的全秩判据）。** 对每个 $F$ 分别作以下消元。

若 $w_F$ 非零，任选分量 $w_{F,k}\ne0$，保留十七行三列矩阵

$$
(L_F)_i=w_{F,k}(B_F)_i-w_{F,i}(B_F)_k,\qquad i\ne k.
\tag{18.7}
$$

则全部支臂方程等价于

$$
L_F(a,z,Y)^T=0,\qquad
p_F=-\frac{(B_F)_k(a,z,Y)^T}{w_{F,k}}.
\tag{18.8}
$$

若 $w_F=0$，则令 $L_F=B_F$，保留十八行，$p_F$ 任意。将两个 $L_F$ 叠成 $L=[\ell\mid N]$，其中 $\ell$ 是 $a$ 列，$N$ 是 $z,Y$ 两列。$L$ 的行数为 $34,35$ 或 $36$。这些指定源槽在某个原归一化父点上组成两条第五支臂的充分必要条件为源及终端对护栏与

$$
\operatorname{rank}L=\operatorname{rank}N.
\tag{18.9}
$$

具体地，令 $a=24$ 后：$\operatorname{rank}N=2$ 时父点唯一；秩一时父点为一条仿射直线；秩零时必须 $\ell=0$，此时 $z,Y$ 均自由。

证明。非零私有列的第 $k$ 行唯一解出 $p_F$，代回其余行就是式 (18.7)。零列时没有关于 $p_F$ 的条件，故十八个 $B_F$ 行一个不能删。现在原归一化父点存在当且仅当 $N(z,Y)^T=-24\ell$ 可解，即 $\ell$ 属于 $N$ 的列空间，这恰是式 (18.9)。它也等价于齐次核内存在 $a\ne0$ 的向量：可缩放到 $a=24$。仅有 $\operatorname{rank}L\le2$ 不够，例如一行 $(1,0,0)$ 强迫 $a=0$，被式 (18.9) 正确排除。

秩二时正规方程或任一非零二阶行子式恢复唯一 $(z,Y)$。秩一时任选 $N$ 的非零列 $v$，写 $N_{:1}=\mu v,N_{:2}=\nu v,\ell=\omega v$，其中各系数由与 $v$ 的内积除以 $\|v\|^2$ 给出，则父点恰为 $\mu z+\nu Y=-24\omega$。秩零时 $N=0$，所以相容性恰为 $\ell=0$。若另指定父区域，必须让恢复点或该直线与该区域相交；本定理自身不附加父窗口。式 (18.8)、(18.6) 随后恢复各支臂自己的响应、漂移与增益。∎

**推论 18.5（三十二源的泛型方阵支图与局部消费者）。** 当两条 $w_F$ 均非零，式 (18.7) 共三十四行。若 $\operatorname{rank}N=2$，任选二行集合 $I_0$ 使 $M_0=N_{I_0}$ 可逆，令 $\delta=\det M_0$。对其余三十二行施加

$$
\delta\ell_i-N_i\operatorname{adj}(M_0)\ell_{I_0}=0,\qquad i\notin I_0.
\tag{18.10}
$$

这是三十二源坐标上的三十二个明确有理方程，保留两个私有支点非零、$\delta\ne0$ 和全部原严格护栏。恢复父点为

$$
\binom zY=-24\operatorname{adj}(M_0)\ell_{I_0}/\delta.
\tag{18.11}
$$

每个合法解给同一实际 $H_4$ 上的 $L_3$，其固定并集至多十六个完整世界。反过来，任一局部 $H_4$ 的 $L_3$ 都可选出这样的十六槽；其源落在某个式 (18.10) 支图，或落在定理 18.4 保留的零私有列、低秩支。

证明。两个支点行解出式 (18.11)，代入余下行并乘非零 $\delta$ 得式 (18.10)。因此支图等价于本支上的式 (18.9)。每条支臂由命题 18.3 给 $L_2$，两条私有第五响应允许不同。取全部十六槽的固定并集，按定义 9.1 的两个第五分句得到 $L_3$；每个被选终端对不同，使所用各非终端集合也至少二元，故提前停止护栏完整保留。反向从 $L_3$ 的每个实际第五子纤维选 $L_2$，再按命题 9.2 的终叶方式分别选对，恰得十六槽。这不要求两个最终动作复用同一对，也不要求两第五支臂的增益、漂移或第五响应相等。重复槽只能作为同一个恢复世界复用。全部证明只给精确条件与消费者，不主张这些条件已有合法解。∎

**命题 18.6（E 曲线与固定父点的直接特化）。** 在任一 $L_M$ 行写作 $(\ell_i,N_{z,i},N_{Y,i})$，代入 $Y=(48z-28a)/35$，令

$$
U_i=\ell_i-\frac45N_{Y,i},\qquad
V_i=N_{z,i}+\frac{48}{35}N_{Y,i}.
\tag{18.12}
$$

余下条件恰是 $Ua+Vz=0$。若私有列非零且 $V_h\ne0$，十七行变成十六个方程

$$
V_hU_i-V_iU_h=0\quad(i\ne h),\qquad z=-24U_h/V_h.
\tag{18.13}
$$

仍须检验 $z\in I$，随后按式 (18.8) 恢复 $p_M$。若 $V=0$，必须 $U=0$，此时任选 $z\in I$；若 $V=0,U\ne0$ 则无归一化解。若私有列恒零，使用十八行 $B_M$，同样的非零 $V$ 消元保留十七个余式，或使用其 $V=0$ 分支。若父点事先精确固定为 $(z_*,Y_*)$，则直接检验 $L_F(24,z_*,Y_*)^T=0$，仍保留零列分支。

证明。式 (18.12) 是父关系的线性代入；非零 $V_h$ 解出 $z$ 后代回即给式 (18.13)，其余情形由 $a=24\ne0$ 逐行得到。E 特化在同一个恢复 $z$ 上调用定义 13.1 的既有第五 J 对；这里不重复该对或十八方程消费者的证明。固定父点必须是同一个精确实数点，包围区间相交不代替任一显示等式。∎

## 19. 双采样零的穷尽分类与终端混合对

**定理 19.1（$g(3)=g(5)=0$ 的全部 E 世界）。** 固定任意 $z\in I$ 及 $Y=(48z-672)/35$。实现这一 $H_4$ 且 $g(3)=g(5)=0$ 的全部合法完整世界，恰为定义 13.1 的两个世界；其漂移为 $z$，整个增益为式 (13.4)，源的 $b,c$ 为式 (13.1)，$r$ 为两个严格不同的 $r_\pm$。结论包括所有原本允许的次数和重根分支。

证明。第三响应和 $g(3)=0$ 给 $d=z$。因式定理及初读零给

$$
g(s)=(s-3)(s-5)(As-z/15).
\tag{19.1}
$$

这里允许 $A=0$。时钟二给 $A=(48-z)/(6t)+z/30$，而时钟四给
$Y-z=(2t-1)(z/15-4A)$。代入父关系并乘正 $t$，恰得

$$
7zt^2+(2352-54z)t+35z-1680
=7z(t-5/7)(t-(7-336/z))=0.
\tag{19.2}
$$

$z>56$，故 $z\ne0$；源合法性给 $t=1+b>1$，只因此排除 $t=5/7$。余根为 $t=7-336/z$，于是 $A=z/105$、$b=6-336/z$。再由 $g(1)=-16z/35\ne0$ 及第一响应得到

$$
j=\frac{35(z-24)}{16z},\qquad
c=j-b=\frac{4536-61z}{16z}.
\tag{19.3}
$$

源方程只余 $r(1-r)=bc$。计算

$$
1-4bc=\frac{K(z)}{2z^2}.
\tag{19.4}
$$

在两个开区间上 $b,c>0$，且 $0<bc<1/4$，所以恰有两个 $0<r<1$ 的解 $r_\pm$。反向把这些参数代回五个原响应得到 $H_4$，其整个增益就是式 (13.4)。这也证明没有遗漏降次或额外根分支：它们已在式 (19.1) 的任意 $A$ 内，被原响应唯一确定。∎

**推论 19.2（第五 M 后的第六分离与端点必要性）。** 记上一定理的两世界类为 $\mathcal E_z$。两者的第五 M 响应均为 $z$。以 $+$ 世界减去 $-$ 世界，其实际第六 J、M 响应差分别为

$$
-\frac{2z}{35}(r_+-r_-),\qquad
-\frac{z}{35}(r_+-r_-),
\tag{19.5}
$$

均不为零。因此在任一第五 M、第六动作的实际响应纤维内，$\mathcal E_z$ 至多含一个世界。每个不同世界的终端碰撞对至少有一个端点不在 $\mathcal E_z$。若第五响应恰为 $p_M=z$，则在该第五纤维内 $d=z$ 与属于 $\mathcal E_z$ 等价，所以每个终端对至少有一个端点 $d\ne z$。

证明。$g(5)=0$ 给第五响应 $z$，且 $g(6)=-z/35$。两个源有共同 $b,c$，故 $n_+-n_-=r_+-r_-$。表 (18.1) 的第五 M 两个第六迹分别为 $n+r+t,n+2u$，其差为 $2(r_+-r_-),r_+-r_-$，得到式 (19.5)。终端对必须先共享其实际第六响应，故不能仅由这两个世界组成。在 $p_M=z,d=z$ 时，正 $n$、$n+u$ 及实际第三、第五响应迫使 $g(3)=g(5)=0$；反向由定理 19.1 已得。这个推论不要求一般的第五响应等于 $z$。∎

**命题 19.3（同对服务两个最终动作的混合根护栏）。** 在第五 M 后固定同一实际第六响应纤维。记 $\gamma_i=g_i(7)$。同一对不同世界若对两个最终动作均碰撞，则

$$
\delta_E(W_1)\gamma_1=\delta_E(W_2)\gamma_2,\qquad
\delta_J=u-r>0,\quad
\delta_M=3u-t-2r=2(1-r)+5b>0.
\tag{19.6}
$$

所以或者两个 $\gamma_i$ 均零，或者两者均非零且同号。一个末采样零端点和一个末采样非零端点不能用同一对完成两个最终分句。若这种混合对已经在某个最终动作下碰撞，则它们漂移不同，且

$$
\operatorname{sign}g_{\rm nonroot}(7)
=\operatorname{sign}(d_{\rm root}-d_{\rm nonroot}).
\tag{19.7}
$$

因而含有指定混合碰撞对的 $L_1$ 纤维至少需要第三个世界；这不限制两个最终动作使用不同对。

证明。表 (18.1) 的两最终迹相减分别给 $u-r$ 和 $3u-t-2r$，它们在严格源域上正。把两条终端碰撞等式相减消去漂移，得到式 (19.6)。正因子保留符号，给第一结论。混合对在一个最终动作下的等式则为
$d_{\rm root}-d_{\rm nonroot}=\tau_{\rm nonroot}g_{\rm nonroot}(7)$；实际迹严格正，故得式 (19.7)。只含这对的集合不能给另一最终碰撞；增加第三世界后可换对，所以这只是对复用方式的护栏。∎

## 20. 两个 E 分量上的完整仿射增益分类

**定理 20.1（无常数增益与唯一一次世界）。** 在每个 $z\in I_-$，不存在实现 $H_4(z)$ 的合法 $\deg g\le1$ 世界。在每个 $z\in I_+$，恰有一个这样的完整世界，且其增益次数恰为一。这里没有固定第五响应，也没有对漂移符号或 $b=c$ 添加条件。

更明确地，令

$$
h=\frac{12(84-z)}{35},\qquad
U_1=(48+h)b+2h,\quad U_3=(48-h)b+2h.
\tag{20.1}
$$

在 $I_+$ 上，下列四次式恰有一个正根 $b_h$，且 $0<b_h<1$：

$$
Q_h(b)=q_0+q_1b+q_2b^2+q_3b^3+q_4b^4,
\tag{20.2}
$$

$$
\begin{aligned}
q_0&=h^3(96-46h/3),\\
q_1&=h^2(6912-1440h+11h^2),\\
q_2&=h(165888-52416h+944h^2+569h^3/36),\\
q_3&=1327104-875520h+26304h^2+2660h^3/3-88h^4/9,\\
q_4&=-5640192+239616h+12320h^2-632h^3/3-1081h^4/144.
\end{aligned}
\tag{20.3}
$$

唯一完整世界由 $b=b_h$ 及

$$
\begin{aligned}
A&=-h/b,\qquad B=((48+2h)b+2h)/b^2,\qquad g(s)=As+B,\quad d=-B,\\
j&=\frac{24b^2+(48+2h)b+2h}{U_1},\qquad
n=\frac{zb^2+(48+2h)b+2h}{U_3},\\
r&=n-j,\qquad c=j-b,\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix}
\end{aligned}
\tag{20.4}
$$

给出；其所有后续实际响应仍用这个同一 $P,g,d$ 和原动作计算。

证明。先对任意非零常数增益 $g=B$，初读给 $d=-B$，时钟二给 $Bb=48$，时钟四遂给 $Y=2Bb=96$。但 $z\in I$ 蕴含 $z<4536/61<84$，父关系给 $Y<96$，故常数层为空。

现在任意仿射候选写作 $g(s)=As+B$，仍有 $d=-B$。原时钟二、四精确给

$$
48=Bb+2A(1+b),\qquad
Y=2Bb+4A(1+2b),\qquad Ab=(Y-96)/4=-h.
\tag{20.5}
$$

所以 $A,B$ 必如式 (20.4)。由 $56<\alpha_-<60$、$70<\alpha_+<4536/61<75$ 得

$$
z\in I_-\Longrightarrow8<h<10,\qquad
z\in I_+\Longrightarrow3<h<24/5.
\tag{20.6}
$$

这些端点比较可直接由式 (13.1) 平方正数比较得到，例如 $6<\sqrt{46}<7$ 已给 $56<\alpha_-<60$，而 $\sqrt{46}>13/2$ 给 $\alpha_+>70$。两个范围都使 $U_1,U_3>0$。实际 $g(1)=U_1/b^2,g(3)=U_3/b^2$，故原时钟一、三唯一解出式 (20.4) 的 $j,n$。

为同时检查源条件，置

$$
\begin{aligned}
R&=(2880-32h-35h^2/12)b^2+(216h-11h^2/6)b+4h^2,\\
C&=-(24+h)b^2+48b+2h.
\end{aligned}
\tag{20.7}
$$

将 $z=84-35h/12$ 代入式 (20.4) 后，通分给

$$
r=\frac{bR}{U_1U_3},\qquad c=\frac C{U_1},\qquad
RU_1U_3-bR^2-CU_1U_3^2=bQ_h(b).
\tag{20.8}
$$

这是显示多项式的恒等式：将左侧按 $b$ 收集并除去因子 $b$，依次即得式 (20.3) 的五个系数。因此

$$
r(1-r)-bc=\frac{b^2Q_h(b)}{U_1^2U_3^2}.
\tag{20.9}
$$

它在原严格条件下同时给必要与充分的源秩一检验，不选择任何源二次根。

在 $8<h<10$，按正项取上端点、负项取下端点，或舍去严格负项，得到

$$
\begin{array}{c|ccccc}
& q_0/h^3&q_1/h^2&q_2/h&q_3&q_4\\ \hline
\text{上界}&-80/3&-3508&-1289110/9&-6479968/3&-2012032
\end{array}
\tag{20.10}
$$

例如 $q_2/h<165888-52416\cdot8+944\cdot10^2+569\cdot10^3/36=-1289110/9$；$q_3$ 舍去最后的负项，$q_4$ 舍去最后两个负项即给表中界。其余两项直接代端点。这五项全负，故 $Q_h(b)<0$ 对每个 $b>0$ 成立。式 (20.9) 排除下分量全部仿射源。

在 $3<h<24/5$，有 $q_0,q_1>0$，且同样的逐项界给

$$
q_3<-2976768/5<0,\qquad q_4<-21030912/5<0.
\tag{20.11}
$$

具体地，$q_3$ 的正项取 $h=24/5$，项 $-875520h$ 取 $h=3$，舍去 $-88h^4/9$；$q_4$ 只保留其常数及两个正项的上端点。$q_1/h^2>6912-1440(24/5)=0$，$q_0/h^3>96-46(24/5)/3>0$。无需给 $q_2$ 指定符号。若 $q_2\ge0$，

$$
\frac{d}{db}\frac{Q_h(b)}{b^3}
=-\frac{3q_0}{b^4}-\frac{2q_1}{b^3}-\frac{q_2}{b^2}+q_4<0.
$$

若 $q_2<0$，则

$$
\frac{d}{db}\frac{Q_h(b)}{b^2}
=-\frac{2q_0}{b^3}-\frac{q_1}{b^2}+q_3+2q_4b<0.
$$

所以两种情形都至多有一个正根。另一方面，$Q_h(0)=q_0>0$，直接相加五个系数给

$$
Q_h(1)=-4313088-470016h-6880h^2+276h^3-93h^4/16<0,
\tag{20.12}
$$

因为 $276(24/5)^3<4313088$。连续性给唯一正根 $b_h\in(0,1)$。

最后证明该根确实给合法完整世界，而不只是代数解。在此 $h$ 范围内，$R$ 的三项系数全正：首项系数大于
$2880-32(24/5)-(35/12)(24/5)^2>0$，中项为 $h(216-11h/6)>0$，常数项为 $4h^2>0$。所以 $r>0$。由于 $0<b_h<1$，

$$
C=48b-(24+h)b^2+2h>(24-h)b+2h>0,
$$

故 $c>0$。式 (20.9) 给 $r(1-r)=bc>0$，结合 $r>0$ 得 $r<1$。源因此逐项严格正、迹一、秩一。式 (20.4) 与 (20.5) 复现时钟二、四，$j,n$ 的定义复现时钟一、三，$d=-B$ 复现初读；整个增益因 $h>0$ 而次数恰为一。对任意第五、第六、最终动作 $F,E,G$，表 (18.1) 还给完整续行

$$
z_5=-B+(5A+B)s_F,\qquad
z_6=-B+(6A+B)\tau_{6,F,E},\qquad
z_7=-B+(7A+B)\tau_{7,F,E,G}.
\tag{20.13}
$$

这些均为原左乘式 (1.2) 的同一世界响应，无需重选增益。所有仿射世界都先被迫具有这些公式，唯一正根又固定全部参数，因此得到完整世界的唯一性。∎

**推论 20.2（对终端槽的次数约束）。** 在下 E 分量，任一合法终端对的两个端点均为二次或三次增益。在上 E 分量，每个不同世界的终端对至少有一个端点为二次或三次增益。上分量不同槽可以复用唯一仿射世界，但那是同一个完整目标。

证明。下分量根本没有仿射世界；上分量全父历史只有一个仿射世界，不同对不能由两个仿射世界组成。该结论是整个类的分类后果，不是一个孤立一次世界的存在证书；混合次数和任意其他采样根仍然允许。∎

## 21. 根在五与七的整个类及其实际第六 M 单射

**定义 21.1（完整 $\mathcal C_{57,z}$ 类）。** 在同一个 $z\in I$ 的实际父历史上，令

$$
\mathcal C_{57,z}=\{W\in\mathcal F(H_4(z)):g_W(5)=g_W(7)=0\},\qquad
\mathcal C_{57,z}(p)=\mathcal C_{57,z}\cap\mathcal F(H_4(z),M,p).
\tag{21.1}
$$

这是完整合法世界的类，不固定源、漂移、最高次项或其余样本。它包含 $\mathcal E_z$，但后面的连续族只证明在所给变化父点上存在类外于 $\mathcal E_z$ 的成员，不断言每个固定父点都严格扩大。

**定理 21.2（在固定实际第五响应上的完整目标单射）。** 对每个 $z\in I$、每个实际第五 M 响应 $p$，实际第六 M 响应在 $\mathcal C_{57,z}(p)$ 上单射。结论包括次数下降、重复根及所有可能的其他采样零。因而固定实际第五响应后，任意实际第六 M 纤维至多含一个该类世界；任何只由该类世界组成的第五 M 支臂都不能有 $L_2$。

证明。第五迹 $n+u>0$ 且 $g(5)=0$，所以实际响应迫使 $d=p$，不是额外的共同漂移承诺。记 $t=1+b>1$、$D=48-d$、$f=D/t$。因式定理与初读零给出整个候选及其全部整数样本：

$$
\begin{aligned}
g(s)&=(s-5)(s-7)(As-d/35),\qquad A=f/30+d/70,\\
(g(0),g(1),g(2),g(3),g(4),g(5),g(6),g(7))
&=\left(-d,\frac45f-\frac{12}{35}d,f,\frac45f+\frac4{35}d,
\frac25f+\frac3{35}d,0,-\frac15f-\frac2{35}d,0\right).
\end{aligned}
\tag{21.2}
$$

从未除以 $A$；$A=0$ 的二次层仍在式中。非零一次以下不可能有两个不同根，但这也是因式表达的结论，不是先验排除。

第四响应和 E 父关系必使

$$
Q_d(t):=6dt^2+[48(42-z)+4d]t+14d-672=0.
\tag{21.3}
$$

具体地，$35Y=35d+(2t-1)(14D/t+3d)$，再代入 $35Y=48z-672$ 并乘 $t$ 即给式 (21.3)。若 $d=0$，这是非零线性式，因为 $z>56>42$；至多一个 $t$，事实上其根为负。

设有两个不同合法参数 $t,s>1$，则 $d\ne0$，Vieta 给

$$
ts=7/3-112/d=-7D/(3d),\qquad
 t+s=8(z-42)/d-2/3.
\tag{21.4}
$$

$d<0$ 会使根和为负，故 $d>0$。由 $ts>1$ 得 $d>84$。原 E 区间给 $z<4536/61<84$，所以 $d>z$、$D<0$。第三响应 $ng(3)=z-d<0$ 与 $n>0$ 给 $g(3)<0$。令

$$
L_t=dt+7D,\quad L_s=ds+7D.
$$

式 (21.2) 给 $g(3)=4L_t/(35t)$，故 $L_t,L_s<0$。用
$g(6)=-g(3)/4-d/35$ 消去第三迹 $n=(z-d)/g(3)$，其实际第六 M 响应为

$$
v(t)=\frac{5d-z}{4}-\frac{d(z-d)t}{4(dt+7D)}
-\frac{2D}{5}(2-1/t)-\frac{4d}{35}(2t-1).
\tag{21.5}
$$

两不同参数的精确差商是

$$
\begin{aligned}
\frac{v(t)-v(s)}{t-s}
&=-\frac{7dD(z-d)}{4L_tL_s}-\frac{2D}{5ts}-\frac{8d}{35}\\
&=-\frac{7dD(z-d)}{4L_tL_s}-\frac{2d}{35}<0.
\end{aligned}
\tag{21.6}
$$

第二等号用式 (21.4)；首项严格负，因为 $d>0$、$D<0$、$z-d<0$、$L_tL_s>0$。故两个不同合法 $t$ 不会共享第六 M 响应；二重二次根本来只有同一 $t$。

还须在相同 $t,d$ 下恢复整个源。它们已固定 $b,f,A$ 及整个 $g$。$g(3),g(6)$ 不会同时为零，否则非零三次及以下多项式有 $3,5,6,7$ 四个不同根。因此或由 $ng(3)=z-d$，或由 $(n+2u)g(6)=v-d$，唯一固定 $n$。若 $g(1)\ne0$，第一响应固定 $j=(24-d)/g(1)$，然后 $r=n-j,c=j-b$ 唯一。若 $g(1)=0$，则第一响应给 $d=24$；根 $1,5,7$ 及初读给

$$
g(s)=\frac{24}{35}(s-1)(s-5)(s-7),\qquad t=7/3.
\tag{21.7}
$$

在固定 $n,t$ 下，源方程 $r^2-tr+(t-1)n-(t-1)^2=0$ 对 $0<r<1$ 的导数为 $2r-7/3<0$，故至多一个合法 $r$，再固定 $c$。这个分支无需假设其存在便已给唯一性。由此所有样本零分支均已处理。

最终，同一 $p,v$ 的该类完整世界至多一个。空集或单点不能满足定义 9.1 的 $L_0$，因而该第六 M 纤维不能有 $L_1$，第五 M 的 $L_2$ 分句失败。证明使用的 $p$、$v$ 都是实际响应，不把两不同父点或不同第五响应拼成同一纤维。∎

**命题 21.3（变化父点上的非空连续三次族）。** 存在一族连续而两两不同的合法三次世界，根在 $5,7$ 而不在 $3$，且父点处于下 E 分量。具体取

$$
T=\left[\frac{2295999}{10^6},\frac{2296001}{10^6}\right],\qquad
\Delta_t=\frac{15t^2-52t+61}{24},
\tag{21.8}
$$

对每个 $t\in T$ 置

$$
\begin{aligned}
r&=(t-\sqrt{\Delta_t})/2,\quad b=t-1,\quad
n=35(3t-1)/96,\quad j=n-r,\quad c=j-b,\\
H&=4j(7+3t)-35t,\qquad d=(1344j-840t)/H,\\
f&=(48-d)/t,\quad A=f/30+d/70,\quad
g(s)=(s-5)(s-7)(As-d/35),\\
z(t)&=d+ng(3),\qquad Y(t)=d+(2t-1)g(4).
\end{aligned}
\tag{21.9}
$$

这些世界的父点 $z(t),Y(t)$ 随参数变化；本命题没有在每个固定父点上给一个连续族，也没有声称每个父点都有 $\mathcal C_{57,z}\setminus\mathcal E_z$ 成员。

证明。由二次公式，$r$ 满足

$$
r^2-tr+(t-1)(9t+61)/96=0.
\tag{21.10}
$$

给定 $n$ 时，$(t-1)n-(t-1)^2=(t-1)(9t+61)/96$，所以式 (21.10) 正是源方程，亦即 $bc=r(1-r)$。漂移的定义等价于

$$
d+j\left(\frac45\frac{48-d}{t}-\frac{12d}{35}\right)=24,
\tag{21.11}
$$

故式 (21.2) 复现第一读；它还给 $g(0)=-d,g(2)=(48-d)/t$，复现初读与时钟二。时钟三、四的响应由式 (21.9) 定义。令 $D=48-d$，直接相消给

$$
\begin{aligned}
35Y(t)-48z(t)+672
&=d(-13+3(2t-1)-192n/35)\\
&\quad+\frac Dt(14(2t-1)-192n/5)+672\\
&=-14d-14D+672=0.
\end{aligned}
\tag{21.12}
$$

因此父点精确在 E 曲线上。

以下是对整个闭区间的有理包围；表中每一端点均为精确有理数，不用浮点近似定义世界：

$$
\sqrt{\Delta_t}\in
\frac{[92830758013384676516,92831300576222224264]}{10^{20}},
\tag{21.13}
$$

$$
\begin{array}{c|c}
\text{量}&\text{有理包围}\\ \hline
r&[683842,683847]/10^6\\
c&[166817,166826]/10^6\\
H&[902460,902894]/10^6\\
d&[41408758,41439271]/10^6\\
g(3)&[7018397,7032518]/10^6\\
A&[686802,687682]/10^6\\
z(t)&[56474910,56535749]/10^6\\
K(z(t))&[3373064338,6096334706]/10^6
\end{array}
\tag{21.14}
$$

为明确这些有理界的证明方式，对式 (21.8) 的同一个有理区间依次使用区间四则运算：和的两端分别相加，乘积取四个端点乘积的最小与最大值，不含零区间的倒数为倒端点；平方的区间包含零时另取下界零。先计算 $15T^2-52T+61$ 再除以 $24$；式 (21.13) 左端的平方小于所得下界，右端的平方大于所得上界，且左端正，这两次整数交叉相乘即证根式界。然后按式 (21.9) 的顺序，用这个根式区间求 $r,b,n,j,c,H,d,f,A,g(3),z$，最后按 $185z^2-23856z+762048$ 求 $K$。每步保留精确有理端点，最后分别向外取至表中分母给式 (21.14)；每项仅用所列有理运算及两次平方比较，故整段区间而非抽样点都被覆盖。例如中心 $t=287/125$ 给 $\Delta_t=2693/3125$，与同一根式定义一致。

表中 $0<r<1,c>0,H>0$ 以及 $b=t-1>0$ 保证定义无零分母且源严格合法。$A>0$ 保证整个增益次数恰为三；$g(3)>0$ 排除 $\mathcal E_z$。又 $56<z(t)<60<\alpha_+$、$K(z(t))>0$，所以 $z(t)\in I_-$。所有公式在闭区间连续，且不同 $t$ 给不同 $b$，故世界两两不同。

还可排除父点在整个区间恒定。若 $z(t)$ 恒为 $z_0$，式 (21.3) 会给
$d(t)=[672-48(42-z_0)t]/(6t^2+4t+14)$，它是 $t$ 的有理函数。于是 $f,g(1)$ 也是有理函数；表中 $d>24$，故由式 (21.11) 及 $j>0$ 得 $g(1)\ne0$。所以 $j=(24-d)/g(1)$、$r=n-j$ 都是有理函数。这迫使 $\sqrt{\Delta_t}=t-2r$ 成为有理函数。但 $15t^2-52t+61$ 的判别式为 $-956\ne0$，其不可约因子重数为一，不可能是有理函数的平方，矛盾。因此父点确实随参数变化。全族只给具体类的非空性及这种变化父点上的扩大，不给共同父点的碰撞。∎

## 22. 仿射实际 MM 单射、并类障碍与四槽联合护栏

**定理 22.1（$32\le Y\le96$ 上的仿射实际 MM 逆）。** 固定同一个任意实数 $z$ 和 $32\le Y\le96$ 的父历史
$H_4=(0,J,24,M,48,J,z,M,Y)$。在实现此父历史的全部合法仿射增益世界上，实际第五 M、第六 M 响应对 $(p,v)$ 唯一确定完整世界。结论包括常数增益以及 $Y=32,96$ 两端点，不断言任意输入数据都能实现。

证明。令 $\lambda=(96-Y)/4\in[0,16]$、$x=1/b>0$。由式 (20.5) 的原时钟二、四消元（不需 E 关系），每个仿射世界 $g(s)=As+B,d=-B$ 都被迫满足

$$
A=-\lambda x,\qquad B=(48+2\lambda)x+2\lambda x^2.
\tag{22.1}
$$

原第三、第五 M、第六 M 的实际响应为

$$
z=-B+(B+3A)n,\quad
p=-B+(B+5A)(n+u),\quad
v=-B+(B+6A)(n+2u).
\tag{22.2}
$$

将同一个 $n$ 消去，恰得

$$
2v-3p+z=u(B+9A)=(x+2)(48-7\lambda+2\lambda x)=f_\lambda(x).
\tag{22.3}
$$

对任意不同的正 $x_1,x_2$，

$$
\frac{f_\lambda(x_1)-f_\lambda(x_2)}{x_1-x_2}
=48-3\lambda+2\lambda(x_1+x_2)>0.
\tag{22.4}
$$

当 $\lambda<16$ 第一部分正；当 $\lambda=16$ 第二部分正；$\lambda=0$ 时差商为 $48$。故 $(p,v)$ 给的同一左侧唯一固定 $x$。于是 $b,A,B,d$ 全固定。又

$$
g(1)=x(48+\lambda+2\lambda x)>0,\qquad
g(3)=x(48-\lambda+2\lambda x)>0.
\tag{22.5}
$$

可合法恢复 $j=(24+B)/g(1)$、$n=(z+B)/g(3)$、$r=n-j,c=j-b$。这是对已合法输入的整个目标唯一性；若恢复参数不满足源条件，则数据没有该类世界，不能把它当作存在性结论。∎

**推论 22.2（E 上仿射末增益严格正）。** 对任意 $z\in I$ 的仿射合法世界，$g(7)>0$。

证明。E 父关系使 $\lambda=12(84-z)/35=h$，且 $56<z<4536/61<84$ 给
$0<\lambda<48/5$。该域还蕴含 $32<Y<96$，所以式 (22.1) 适用，且

$$
g(7)=x(48-5\lambda+2\lambda x)>0.
\tag{22.6}
$$

这里正性从原响应推出，不是对一般三次世界增加符号条件。∎

**定理 22.3（$\mathcal A_z\cup\mathcal C_{57,z}$ 的第五 M 障碍）。** 令 $\mathcal A_z$ 是任意固定 $z\in I$ 父点上的全部合法仿射世界，$\mathcal C_{57,z}$ 如定义 21.1。任意子集
$K\subseteq\mathcal A_z\cup\mathcal C_{57,z}$、任意第五 M 响应 $p$，都不能使
$K\cap\mathcal F(H_4(z),M,p)$ 在该实际第五历史上具有 $L_2$。从而只用这两个类的支持不能在父点给 $L_3$。结论对任意基数支持成立，仍允许不同最终动作使用不同对。

证明。固定实际第五响应 $p$ 和任意实际第六 M 响应 $v$。定理 22.1 使其纤维至多含一个 $\mathcal A_z$ 世界；定理 21.2 使其至多含一个 $\mathcal C_{57,z}$ 世界。所以最多两个世界。空集或单点已被停止护栏排除。若有两个不同世界，它们必分别来自两类；根在 $5,7$ 的世界有 $d=p$，两个最终动作的响应都为 $p$。仿射世界的两个最终响应之差则为

$$
(3u-t-2r)g(7)=[2(1-r)+5b]g(7)>0,
\tag{22.7}
$$

由推论 22.2 及严格源条件。因此它的两个最终响应不可能都等于 $p$。至少一个最终动作把这两个世界分开，其所有响应子纤维均至多单点，故该第六 M 纤维不能有 $L_1$。这是对每个实际 $v$ 的结论，遂否定第五 M 的 $L_2$ 所需第六 M 分句。因为最多只有这对，允许两个最终动作换对也不能补足；并未把换对自由从一般消费者中删除。最后父 $L_3$ 必须有第五 M 的 $L_2$ 子纤维，所以该支持也不能给父 $L_3$。∎

**推论 22.4（四个指定第六 M 槽的联合必要增益）。** 在定义 13.2 的完整消费者或与它等价的 §§16–17 支图中，写每槽的整个增益为
$g_{EGk}(s)=\sum_{h=0}^3a_{h,EGk}s^h$；系数由式 (16.8) 给出。任一合法解必须满足

$$
\Gamma:=\sum_{G\in\{J,M\}}\sum_{k=1}^2
(a_{2,MGk}^2+a_{3,MGk}^2)
\bigl(g_{MGk}(5)^2+g_{MGk}(7)^2\bigr)>0.
\tag{22.8}
$$

这是四个第六 M 槽联合的必要条件；不要求每对的相应和正，也不要求每项正，不把它转用于第六 J 槽。全部原方程、源护栏、同父关系及各终端对不同仍然必需。

证明。每项非负。若总和为零，每个第六 M 槽要么 $a_2=a_3=0$，属于 $\mathcal A_z$；要么 $g(5)=g(7)=0$，属于 $\mathcal C_{57,z}$。这四槽的固定并集便包含于定理 22.3 的两类之并。然而原第六响应等式及两个不同终端对要求该同一实际第六 M 纤维有 $L_1$，与其证明中对每个 $p,v$ 的否定矛盾。因此至少一个指定槽既是真正二次或三次，又不属于根在 $5,7$ 的类。式 (22.8) 只表达这一个联合必要事实，不给任何合法系统解。∎

**推论 22.5（根在五、七的锚点不能独自配成两世界 $L_1$）。** 在一个固定第五 M、第六 M 的实际响应纤维内，若含 $W_0\in\mathcal C_{57,z}$，则任何 $L_1$ 支持必须另含至少两个不属于 $\mathcal C_{57,z}$ 的世界。

证明。定理 21.2 使该纤维内至多一个类内世界。若仅再有一个不同世界 $W_1$ 并用这对完成两个最终分句，式 (19.6) 及 $g_0(7)=0$ 迫使 $g_1(7)=0$。任一终端碰撞又给 $d_1=d_0=p$；实际第五响应和正第五迹给 $g_1(5)=0$。于是 $W_1$ 也在该类，与单射性矛盾。因此至少需两外部世界。这个支持约束不提供它们的存在性，也不强制一般消费者采用此锚点。∎

## 23. 具体源对应、复用方法与剩余共同实现

**注记 23.1（新增内容与复用接口）。** §§16–18 的数学对象始终是定义 1.1 的严格正、秩一、迹一源和一个固定的非零三次及以下整个增益、一个任意实漂移。源坐标 $(r,b)$ 通过 $c=r(1-r)/b$ 与原矩阵逐项对应；它不选择 $b=c$ 或 $b\ne c$。四节点值逐项对应原时钟 $0,1,2,3$；漂移恢复直接使用定理 12.1、12.2；八槽的实际纤维与提前停止含义直接使用定义 9.1、命题 9.2 及定理 13.3。式 (16.4) 的新系数编译和全部秩层判据把同一个十八行共同实现问题变为源上的精确条件；§18 进一步允许两个第五动作的独立支持，但通过同一个 $(24,z,Y)$ 连接，而非通过相近父点连接。

§19 的 E 对本身及其第五 J 支臂来自定义 13.1；新增结论是这个父点上 $g(3)=g(5)=0$ 的穷尽性和实际第六响应的覆盖限制。§20 给整个仿射类在两分量上的空或唯一分类，包含唯一根的严格源恢复；无需另立一个孤立一次世界作为该分类的替代。§21 对完整根在 $5,7$ 的类证明实际第六 M 单射，并给变化父点的明确非空族。§22 的实际 MM 消去恒等式作用于更大的 $32\le Y\le96$ 仿射域，再与该根类的单射组合成并类障碍及四槽联合护栏。这些都是所定义具体世界与实际响应的结论。

Lagrange 插值、有限维线性代数、Gram 投影、Cauchy–Binet、Schur 补、因式定理、Vieta、介值定理、有理区间运算及收缩原理是复用的标准方法。它们在这里分别承担增益一致性、共同父点相容性、正则性、次数分类和充分证书接口，不单独列为新的通用数学成果。可分变量的消元与 Golub–Pereyra 的 variable projection 以及 Shearer–Gilbert《A Generalization of Variable Elimination for Separable Inverse Problems Beyond Least Squares》的方法背景相接；本卷的精确证明是显示的有限行列式、恒等式和分支证明，不从一般反问题文献推入此模型的可实现性、唯一性或样本复杂度结论。双线性可识别性中源与增益的因素对应也不能消去这里的漂移、严格源条件或完整目标区分。这些来源对应不附外部原创性判断。

**注记 23.2（全部保留分支与未决边界）。** 全部新增系统保留任意实漂移、$b=c$、整个增益的所有一至三次及允许的常数层、采样零、重根和源二次重根；只在具体分类的结论内证明某一层为空。全局恢复没有除以增益样本、最高次项、$b-c$、源判别式或世界差。两行支点和私有响应支点只在各自非零支使用；零列和秩零、一支都有显示恢复规则。E 路线保留两个严格区间；非法源边界与各开区间端点都未通过极限加入。

十六源、三十二源及其有理盒接口均未给出一个合法联合零点，也未排除不受限的联合零点。特别是式 (22.8) 通过并类障碍只增加必要条件，其他二次、三次、根型和混合支持仍然在原实际历史问题内。不同最终动作仍可选择不同终端对；不同第五支臂仍有自己的实际第五响应；每条轨迹仍从同一源、增益与漂移出发按原左动作和时钟 $0,\ldots,7$ 读取，没有重置、复制、空动作、跳读或新观测端口。

即使某个合法共同零点给出局部 $H_4$ 的 $L_3$，命题 13.4 和 §9 的更早祖先、相反动作、实际响应及提前停止义务仍须分别完成。这里不解决原根的预算二择，也不给全局读数上界。单世界分类、变化父点的连续族、低秩相容式、平方和为零条件和充分盒接口，均不代替完整实际纤维的共同实现。

## 追加锚（本行以下为增补区）

## 24. 第六采样根父线的整个实际纤维与四节点插值

**定义 24.1（固定响应的完整纤维）。** 本节起仍采用定义 1.1 的合法完整世界、原左动作和原时钟，只重新指定父响应参数，不采用式 (1.3) 的参数小矩形。对任意实数 $z\ge54$，置

$$
Y=\frac{59z-720}{45},\qquad
H_4(z)=(0,J,24,M,48,J,z,M,Y),
$$

$$
H_5(z)=(H_4(z),M,z),\qquad
H_6(z)=(H_5(z),M,z),\qquad
\mathcal R_z=\mathcal F(H_6(z)).
\tag{24.1}
$$

因此实际动作是 $J,M,J,M,M,M$，实际读数是 $0,24,48,z,Y,z,z$。$\mathcal R_z$ 包含所有实现这个字面历史的合法完整世界；开始时不承诺漂移、增益次数、增益根型、源的对称性或终端碰撞对。每个世界仍各自携带一个固定的非零三次及以下实多项式和一个任意实常漂移。沿用 $j=b+c$、$t=1+b$、$u=1+2b$、$n=r+j$；命题 1.2 的矩阵恒等式不依赖旧参数窗口，故原时钟 $0,\ldots,6$ 的迹依次为

$$
1,\ j,\ t,\ n,\ u,\ n+u,\ n+2u.
\tag{24.2}
$$

这些迹均严格正，且 $t=(u+1)/2$、$u>1$。以下出现的辅助多项式及其字母只用于本追加部分，与旧章同名字母分别解释。

**引理 24.2（任意漂移的四节点表示）。** 对任意 $W\in\mathcal R_z$，写 $k=z-d$、$v=n+2u$，则同一个整个增益满足

$$
g(0)=k-z,\qquad g(3)=\frac{k}{n},\qquad
g(5)=\frac{k}{n+u},\qquad g(6)=\frac{k}{v}.
\tag{24.3}
$$

定义四个插值基

$$
\begin{aligned}
\ell_0(s)&=-\frac{(s-3)(s-5)(s-6)}{90},&
\ell_3(s)&=\frac{s(s-5)(s-6)}{18},\\
\ell_5(s)&=-\frac{s(s-3)(s-6)}{10},&
\ell_6(s)&=\frac{s(s-3)(s-5)}{18}.
\end{aligned}
$$

则

$$
g(s)=(k-z)\ell_0(s)+\frac{k}{n}\ell_3(s)
 +\frac{k}{n+u}\ell_5(s)+\frac{k}{v}\ell_6(s).
\tag{24.4}
$$

置

$$
\begin{aligned}
L&=4+\frac{10}{n}-\frac9{n+u}+\frac4v,\\
B&=15-t\left(2+\frac{20}{n}-\frac{12}{n+u}+\frac5v\right),\\
C&=-59+\frac{20(u+t)}n+\frac{12(3u-t)}{n+u}
                  +\frac{5(t-2u)}v.
\end{aligned}
\tag{24.5}
$$

原时钟 $1,2,4$ 的方程蕴含

$$
\begin{aligned}
q_1&=(4j-9)z+216+(9-jL)k=0,\\
q_2&=(u-14)z+720+Bk=0,\\
kC&=0.
\end{aligned}
\tag{24.6}
$$

证明。式 (24.3) 直接来自初读、第三、第五和第六实际响应。四个 $\ell_i$ 在节点 $0,3,5,6$ 上各取相应的单位值。两边之差次数至多三而有四个不同根，故式 (24.4) 对所有 $s$ 成立，包含所有降次、多重增益根和零样本情形。余下三个节点的基值为

| $s$ | $\ell_0(s)$ | $\ell_3(s)$ | $\ell_5(s)$ | $\ell_6(s)$ |
| --- | --- | --- | --- | --- |
| $1$ | $4/9$ | $10/9$ | $-1$ | $4/9$ |
| $2$ | $2/15$ | $4/3$ | $-4/5$ | $1/3$ |
| $4$ | $-1/45$ | $4/9$ | $4/5$ | $-2/9$ |

若 $F_i=d+g(i)\operatorname{tr}(A_iP)-z_i$ 表示原响应残差，其中 $z_1=24,z_2=48,z_4=Y$，代入该表得到

$$
q_1=-9F_1,\qquad q_2=-15F_2,\qquad
45F_4-q_2=kC.
\tag{24.7}
$$

最后一式使用 $45Y=59z-720$ 和 $2t=u+1$。于是三个实际方程给式 (24.6)。只除过固定节点差和正迹，没有除以 $k$、增益样本或最高次项。∎

## 25. 非零漂移差分支的源坐标与未除法消元

**引理 25.1（非零差分支的严格坐标窗）。** 若 $W\in\mathcal R_z$ 且 $k\ne0$，令 $x=n/u>0$、$h=1/u\in(0,1)$，定义

$$
\begin{aligned}
D(x)&=13x^2+41x+40,\\
N(x)&=118x^3+249x^2-49x-120,\\
V(x)&=x(x+1)(x+2).
\end{aligned}
\tag{25.1}
$$

则

$$
hD=N,\qquad u=\frac DN,\qquad 0<N<D,\qquad
\frac23<x<\frac67.
\tag{25.2}
$$

证明。$k\ne0$ 和式 (24.6) 给 $C=0$。将 $n=xu$、$t=(u+1)/2$ 代入式 (24.5)，逐项通分即得

$$
2VC=hD-N=\frac{D-uN}{u}.
\tag{25.3}
$$

因 $x>0$，有 $D,V>0$，所以 $h\in(0,1)$ 给 $0<N<D$，也允许除以此处已经证明为正的 $N$。

在 $[0,2/3]$ 上，$N''(x)=708x+498>0$，且

$$
N(0)=-120,\qquad N(2/3)=-\frac{190}{27}.
$$

凸性使整个区间上的 $N$ 不大于连接这两个负端点的弦，故 $N<0$；于是 $x>2/3$。另一方面，写 $x=2/3+y$ 时

$$
(N-D)(2/3+y)=-\frac{2164}{27}+382y+472y^2+118y^3.
\tag{25.4}
$$

它在 $y\ge0$ 上严格递增，而 $(N-D)(6/7)=3620/343>0$。$N-D<0$ 排除 $x\ge6/7$，得严格坐标窗。∎

**定义 25.2（整数消元多项式）。** 在式 (25.1) 的基础上，全部下式都是变量 $x$ 的整数系数多项式，$A,G$ 还关于源坐标 $r$ 仿射：

$$
\begin{aligned}
E&=5x^2+16x+20,\\
K&=-2D(D+N)+(D-14N)E,\\
Z_r&=xD-rN,\\
A(x,r)&=2Z_rK+9DN(D+N),\\
G(x,r)&=6912DNV+432D^2V+216DN(D+N)\\
&\hspace{1.5em}-5760DVZ_r-1440ENZ_r.
\end{aligned}
\tag{25.5}
$$

另置

$$
\begin{aligned}
A_0&=A(x,0),\qquad A_1=A(x,1)-A(x,0)=-2NK,\\
\Pi&=(5-8x)D^2+(8x-6)ND+5N^2,\\
U&=4NA_0+(D+N)A_1,\\
W&=4N^2A_0^2+2N(D+N)A_0A_1\\
&\hspace{1.5em}+(D-N)(2xD-D+N)A_1^2,\\
P_i&=54A(x,i)-G(x,i)\quad(i=0,1).
\end{aligned}
\tag{25.6}
$$

$P_0,P_1$ 在此是多项式，不表示源矩阵；$K$ 与下文的参数二次式 $K_6$ 也分别解释。

**引理 25.3（源二次式及消元恒等式）。** 在 $k\ne0$ 分支上，源坐标 $r$ 是以下首一二次式的实根：

$$
Q(R)=R^2-\frac{D+N}{2N}R
       +\frac{(D-N)(2xD-D+N)}{4N^2}.
\tag{25.7}
$$

其判别式是 $\Pi/(4N^2)$。原时钟 $1,2$ 还给

$$
A(x,r)z=G(x,r).
\tag{25.8}
$$

证明。原秩一约束在 $c=n-r-b$ 下为
$r^2-(b+1)r+b(n-b)=0$。代入 $u=D/N$、$b=(D-N)/(2N)$、$n=xD/N$ 即得 $Q(r)=0$；展开二次判别式得到 $\Pi/(4N^2)$，没有选择源二次式的某个根。

为核对式 (25.8) 的消元而不引入消元分母承诺，写

$$
\begin{aligned}
T&=30NV-2(D+N)V-N(D+N),\\
B&=\frac{T}{2NV},\qquad
L=4+\frac{NE}{DV},\qquad j=\frac{Z_r}{N},\\
9-jL&=\frac{9NDV-Z_r(4DV+NE)}{NDV}.
\end{aligned}
\tag{25.9}
$$

这里 $L$ 的分子归并使用
$10(x+1)(x+2)-9x(x+2)+4x(x+1)=E$；$B$ 的分子归并使用
$20(x+1)(x+2)-12x(x+2)+5x(x+1)=D$。代入 $q_1,q_2$ 后，$k$ 项相消，余式恰为

$$
Bq_1-(9-jL)q_2
=\frac{A(x,r)z-G(x,r)}{2NDV}.
\tag{25.10}
$$

例如通分后的 $z$ 分子为 $2Z_rK+9DN(D+N)$，常数分子为 $-G$，直接给式 (25.5)。因 $q_1=q_2=0$ 且 $N,D,V>0$，得到式 (25.8)。没有除以 $A$、$B$、$9-jL$ 或两方程的消元行列式；其中任意一项为零都仍由这个恒等式覆盖。∎

## 26. 六个符号判据的有限有理证书与源根序

**引理 26.1（六十九个系数的符号证书）。** 对定义 25.2 的六个多项式，以下是整个闭区间上的严格符号：

$$
\Pi<0\quad\hbox{于 }[2/3,3/4],\qquad
A_1,U,W,P_0,P_1>0\quad\hbox{于 }[3/4,6/7].
\tag{26.1}
$$

这些判据由下面全部有理系数给出。对任意次数至多 $m$ 的 $p(x)=\sum_{q=0}^mp_qx^q$，在区间 $[\ell,h]$ 上定义

$$
\begin{aligned}
a_j&=(h-\ell)^j\sum_{q=j}^m\binom qj p_q\ell^{q-j},\\
\beta_i&=\sum_{j=0}^i\frac{\binom ij}{\binom mj}a_j,
\qquad 0\le i\le m.
\end{aligned}
\tag{26.2}
$$

则精确恒等式为

$$
p(\ell+(h-\ell)\theta)
=\sum_{i=0}^m\beta_i\binom mi\theta^i(1-\theta)^{m-i}.
\tag{26.3}
$$

下表给出各组的精确次数、系数数目及极值。第一行取最大值，其余取最小值；这都是有理系数的极值，不是对多项式取有限样本的极值。

| 多项式 | 区间 | $m$ | 系数数目 | 精确系数极值 |
| --- | --- | --- | --- | --- |
| $\Pi$ | $[2/3,3/4]$ | $6$ | $7$ | $\max_i\beta_i=-632599/1024<0$ |
| $A_1$ | $[3/4,6/7]$ | $8$ | $9$ | $\min_i\beta_i=8340727419/4096>0$ |
| $U$ | $[3/4,6/7]$ | $11$ | $12$ | $\min_i\beta_i=6002059123197/65536>0$ |
| $W$ | $[3/4,6/7]$ | $22$ | $23$ | $\min_i\beta_i=188107333756935228463090275/68719476736>0$ |
| $P_0$ | $[3/4,6/7]$ | $8$ | $9$ | $\min_i\beta_i=9769586823/8192>0$ |
| $P_1$ | $[3/4,6/7]$ | $8$ | $9$ | $\min_i\beta_i=20829473595/8192>0$ |

为使每一个有理数均可直接核对，以下各表指定一个正整数公分母 $\delta_p$，并列出全部整数 $c_i=\delta_p\beta_i$。除 $\Pi$ 的七项全负外，其余六十二项全正；总数为 $7+9+12+23+9+9=69$。

多项式 $\Pi$ 的表取 $\delta_{\Pi}=3732480$。

| $i$ | $c_i$（对应 $\Pi$） |
| --- | --- |
| $0$ | $-4445962240$ |
| $1$ | $-9728245760$ |
| $2$ | $-13146203136$ |
| $3$ | $-14425041600$ |
| $4$ | $-13265777808$ |
| $5$ | $-9343549260$ |
| $6$ | $-2305823355$ |

多项式 $A_1$ 的表取 $\delta_{A_1}=944504995840$。

| $i$ | $c_i$（对应 $A_1$） |
| --- | --- |
| $0$ | $1923305350631144760$ |
| $1$ | $2637967636943717085$ |
| $2$ | $3528475376666968980$ |
| $3$ | $4615882309284523200$ |
| $4$ | $5923138436818017408$ |
| $5$ | $7475236653066255360$ |
| $6$ | $9299369713090867200$ |
| $7$ | $11425098230113075200$ |
| $8$ | $13884530430836736000$ |

多项式 $U$ 的表取 $\delta_{U}=14254469397217280$。

| $i$ | $c_i$（对应 $U$） |
| --- | --- |
| $0$ | $1305483521910101573310810$ |
| $1$ | $2155516890929804264435685$ |
| $2$ | $3345853293777077093696238$ |
| $3$ | $4959456508406702770783560$ |
| $4$ | $7091549062279793032919760$ |
| $5$ | $9850989889440580947030720$ |
| $6$ | $13361782648784925985297920$ |
| $7$ | $17764725741295306795241472$ |
| $8$ | $23219215921241179218247680$ |
| $9$ | $29905218316022635254251520$ |
| $10$ | $38025416655796585365504000$ |
| $11$ | $47807558571883317166080000$ |

多项式 $W$ 的表取 $\delta_{W}=62050500425182578365166648798740480$。

| $i$ | $c_i$（对应 $W$） |
| --- | --- |
| $0$ | $169852198352814165554004337294164392496815200933875$ |
| $1$ | $222783190755915179252066941254044387808379543534605$ |
| $2$ | $293317765626392541366315195065615598643381333018260$ |
| $3$ | $387217456168801119479043552452244409121957060378826$ |
| $4$ | $511881937090540564355837904337791025540951561838112$ |
| $5$ | $676724143737930532955179986859119574148122623740160$ |
| $6$ | $893615152671377787927127389105844655227473133017600$ |
| $7$ | $1177410102171494688161802208867661874344861410878720$ |
| $8$ | $1546568060450691879457045591279814844139414646231040$ |
| $9$ | $2023880590926404029613215554229596807525067848990720$ |
| $10$ | $2637325842942121515461618402031647656821945639567360$ |
| $11$ | $3421067340684425169839125404391323198511297317765120$ |
| $12$ | $4416619283631664146414182621493547169469232746332160$ |
| $13$ | $5674203142887497904641298361282006874002263405232128$ |
| $14$ | $7254323677046102792224334843346880913419688787050496$ |
| $15$ | $9229596240653058316705470240955404600741397423718400$ |
| $16$ | $11686861464110348456089350542864634021869083479244800$ |
| $17$ | $14729628097095671813298138887868089352001318551552000$ |
| $18$ | $18480890084592338152719504482049085199051660250316800$ |
| $19$ | $23086369847633696795192995266892082829577810870272000$ |
| $20$ | $28718246338403115710765302319563163304576889651200000$ |
| $21$ | $35579433806926615082332230593835705357884719104000000$ |
| $22$ | $43908485437428295993227180918063403577659883520000000$ |

多项式 $P_0$ 的表取 $\delta_{P_0}=94450499584$。

| $i$ | $c_i$（对应 $P_0$） |
| --- | --- |
| $0$ | $112639447773634446$ |
| $1$ | $124463070862431777$ |
| $2$ | $261623315857082508$ |
| $3$ | $543699526882149792$ |
| $4$ | $992274837323269248$ |
| $5$ | $1631104322024927232$ |
| $6$ | $2486295693513031680$ |
| $7$ | $3586503407459696640$ |
| $8$ | $4963137099005952000$ |

多项式 $P_1$ 的表取 $\delta_{P_1}=33732321280$。

| $i$ | $c_i$（对应 $P_1$） |
| --- | --- |
| $0$ | $85769835864235425$ |
| $1$ | $208865954587858470$ |
| $2$ | $436005296007819300$ |
| $3$ | $782346638257485840$ |
| $4$ | $1264555854045356544$ |
| $5$ | $1900930272551493120$ |
| $6$ | $2711532218690304000$ |
| $7$ | $3718332358340198400$ |
| $8$ | $4945363518947328000$ |

证明。式 (26.3) 可由下面的有限二项式恒等式逐幂得到：

$$
\sum_{i=j}^m\frac{\binom ij}{\binom mj}
 \binom mi\theta^i(1-\theta)^{m-i}
=\theta^j\sum_{i=j}^m\binom{m-j}{i-j}
 \theta^{i-j}(1-\theta)^{m-i}=\theta^j.
\tag{26.4}
$$

全部表项由式 (25.1)、(25.5)、(25.6) 及 (26.2) 决定。也可不计算系数极值，直接把每表的整数除以指定 $\delta_p$，用反向系数恒等式

$$
a_j=\binom mj\sum_{i=0}^j(-1)^{j-i}\binom ji
             \frac{c_i}{\delta_p},\qquad 0\le j\le m,
\tag{26.5}
$$

逐项核对式 (26.2) 的 $a_j$。这给出所有六十九个有理系数的有限等式与严格符号，而不仅给出一个通用正性准则。式 (26.3) 的基项在 $0\le\theta\le1$ 上非负且和为一，所以多项式值位于其全部 $\beta_i$ 的最小值与最大值之间。六组严格同号遂证明式 (26.1)，包括各闭区间端点。∎

**引理 26.2（合法源上的消元分母严格正）。** 任意 $k\ne0$ 分支的合法世界必有

$$
\frac34<x<\frac67,\qquad A(x,r)>0,\qquad
54A(x,r)-G(x,r)>0.
\tag{26.6}
$$

证明。由引理 25.1，$2/3<x<6/7$ 且 $N>0$。源二次式 $Q$ 有实根 $r$，故其判别式非负。引理 26.1 的 $\Pi<0$ 排除了整个 $[2/3,3/4]$，得到严格的剩余坐标窗。

先证 $A>0$，此处必须使用源二次式，而不是只考察非法源端点。由 $A=A_0+rA_1$ 和引理 26.1，$A_1>0$。若 $A_0\ge0$，合法源的 $r>0$ 立即给 $A>0$。若 $A_0<0$，置 $w=-A_0/A_1>0$。$Q$ 的顶点横坐标为

$$
R_* =\frac{D+N}{4N},\qquad
R_*-w=\frac{U}{4NA_1}>0.
\tag{26.7}
$$

另一方面，定义 (25.6) 正好给

$$
4N^2A_1^2Q(w)=W>0.
\tag{26.8}
$$

$Q$ 首一且有实根，故它在两个实根之间非正。$Q(w)>0$ 使 $w$ 严格在两根区间之外，而 $w<R_*$ 排除了位于较大根右侧的可能；于是 $w$ 严格小于较小根。源二次式为重根时同样成立：此时根就是顶点，式 (26.7) 已给严格次序。因此每一个合法源根都满足 $r>w$，从而 $A=A_1(r-w)>0$。这里不除以判别式，也不排除重复源根。

最后才使用关于 $r$ 的仿射端点判据：

$$
54A(x,r)-G(x,r)=(1-r)P_0(x)+rP_1(x)>0,
\tag{26.9}
$$

因为 $0<r<1$ 且 $P_0,P_1>0$。$r=0,1$ 在此仅用于计算仿射多项式端点值，没有把这两个非法源纳入世界域。式 (26.7)–(26.8) 负责 $A$ 的源根正性，式 (26.9) 负责另一个仿射量的正性，两者作用不同。∎

## 27. 不预设漂移与根型的完整世界刚性

**定理 27.1（第六 M 固定响应的整个实际纤维）。** 对每个实数 $z\ge54$，定义 24.1 的 $\mathcal R_z$ 恰由下列世界组成，且只保留严格合法的源：

$$
\begin{aligned}
d&=z,\qquad
 g(s)=\frac z{90}(s-3)(s-5)(s-6),\\
b&=\frac{13z-720}{2z},\qquad
c=\frac{1224-17z}{4z},\\
r&=\frac{1\pm\sqrt{1-4bc}}2,\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix}.
\end{aligned}
\tag{27.1}
$$

具体地，定义整数二次式

$$
K_6(z)=223z^2-28152z+881280.
\tag{27.2}
$$

在 $z\ge54$ 的域内，非空的充要条件是

$$
\frac{720}{13}<z<72,\qquad K_6(z)\ge0.
\tag{27.3}
$$

满足严格区间时，$K_6(z)>0$ 给恰好两个完整世界，$K_6(z)=0$ 给恰好一个；条件 (27.3) 失败则为空。源二次重根只计一个世界。

证明。先证任一合法竞争世界必须具有所列形式。取任意 $W\in\mathcal R_z$ 并令 $k=z-d$。若 $k\ne0$，引理 25.3、26.2 给

$$
Az=G,\qquad A>0,\qquad54A-G>0.
$$

故 $A(54-z)>0$，推出 $z<54$，与本定理的 $z\ge54$ 矛盾，等号 $z=54$ 也被严格排除。因此 $k=0$，即 $d=z$。

式 (24.3) 的三个分母严格正，于是 $g(3)=g(5)=g(6)=0$；初读又给 $g(0)=-z\ne0$。这三个不同根和次数至多三强制 $g$ 正好是式 (27.1) 的非零三次式。这里的三根是所有原方程的结论，不是对竞争世界的初始承诺。该式给

$$
g(1)=-\frac{4z}{9},\quad g(2)=-\frac{2z}{15},\quad
 g(4)=\frac z{45},\quad g(7)=\frac{4z}{45}.
\tag{27.4}
$$

首两个动作响应由此强制

$$
j=\frac{9(z-24)}{4z},\qquad
 t=\frac{15(z-48)}{2z},\qquad
 b=t-1,\quad c=j-b,
\tag{27.5}
$$

即式 (27.1) 的 $b,c$。$bc=r(1-r)$ 强制全部源根恰为式 (27.1) 的两个代数根，没有丢弃任何一个严格合法的根。

再证严格过滤与反向实现。$z\ge54>0$ 下，$b>0$ 等价于 $z>720/13$，$c>0$ 等价于 $z<72$。直接展开有

$$
1-4bc=\frac{223z^2-28152z+881280}{2z^2}
      =\frac{K_6(z)}{2z^2}.
\tag{27.6}
$$

故严格合法源必满足式 (27.3)。反之，若式 (27.3) 成立，则 $b,c>0$，且 $0\le1-4bc<1$。两个实根都在严格开区间 $(0,1)$ 内；每根均满足 $bc=r(1-r)$，因此相应源逐项正、秩恰为一、迹为一。根重合时相应完整世界也重合，除此以外两个 $r$ 给不同的源。

现在对这些候选用原时钟逐项重放，检验充分性，而不只保留必要源方程。用 $n=r+j$、$u=1+2b=14-720/z$，有

| 原时钟 $i$ | 原迹 | 同一个 $g(i)$ | 原响应 $d+g(i)\operatorname{tr}(A_iP)$ |
| --- | --- | --- | --- |
| $0$ | $1$ | $-z$ | $0$ |
| $1$ | $j$ | $-4z/9$ | $z-(4z/9)\,9(z-24)/(4z)=24$ |
| $2$ | $t$ | $-2z/15$ | $z-(2z/15)\,15(z-48)/(2z)=48$ |
| $3$ | $n$ | $0$ | $z$ |
| $4$ | $u$ | $z/45$ | $z+(14-720/z)z/45=(59z-720)/45=Y$ |
| $5$ | $n+u$ | $0$ | $z$ |
| $6$ | $n+2u$ | $0$ | $z$ |

全部矩阵仍是命题 1.2 的实际左乘矩阵；所有行使用同一 $P,g,d$。非零增益、严格源和全部七次原响应都已满足，故候选确实在 $\mathcal R_z$ 中。这证明整个世界纤维的双向等价及其精确基数。∎

**注记 27.2（零层、重根与对称源）。** 四节点插值从一开始包含所有次数 $0,1,2,3$、所有增益根的重数、任意采样零及任意实漂移。最终恰好三次、三个指定单根和 $d=z$ 是完整方程推出的结果。因此其他低次或增益重根世界被证明不能实现本实际历史，不能将这一结论反过来用作证明前提。源二次重根仍由式 (27.3) 的等号保留，没有除以 $1-4bc$。在 $k\ne0$ 分支也没有借助判别式非零来证明 $A>0$。

同样，证明始终允许 $b=c$，没有除以 $b-c$。分类后若再要求对称，则式 (27.1) 强制

$$
z=\frac{2664}{43},\qquad b=c=\frac{51}{74},\qquad
1-4bc=-\frac{1232}{1369}<0.
\tag{27.7}
$$

故这个实际纤维恰无对称合法源，这是全域分类的推论而不是删去对称源的承诺。$z=720/13$ 或 $z=72$ 分别使 $b=0$ 或 $c=0$，不得把这些严格非法端点用极限补回；$r=0,1$ 也从未成为合法源。

## 28. 两个最终动作的单射与全部子集的停止护栏

**定理 28.1（整个第六纤维均无一层失败）。** 对任意 $z\ge54$，在 $H_6(z)$ 上，最终 $J$ 与最终 $M$ 的响应映射各自在整个 $\mathcal R_z$ 上单射。更精确地，对任意两个世界 $W,W'\in\mathcal R_z$，按 $W'-W$ 的顺序写 $\Delta r=r'-r$，则

$$
\begin{aligned}
z_{7,J}(W')-z_{7,J}(W)&=\frac{16z}{45}\Delta r,\\
z_{7,M}(W')-z_{7,M}(W)&=\frac{8z}{45}\Delta r.
\end{aligned}
\tag{28.1}
$$

所以对每一个子集 $S\subseteq\mathcal R_z$，都有
$\neg L_1(S,H_6(z))$，包括空集和单点。

证明。第五、六动作均为 $M$ 时，原时钟 $6$ 的矩阵是
$\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$。最后分别左乘 $J,M$ 给

$$
A_{7,J}=\begin{pmatrix}5&2\\3&1\end{pmatrix},\qquad
A_{7,M}=\begin{pmatrix}5&2\\8&3\end{pmatrix}.
$$

由式 (1.7)，相应最终迹为

$$
\tau_{7,J}=2n+t+2r=2j+t+4r,\qquad
\tau_{7,M}=2n+3u=2j+3u+2r.
\tag{28.2}
$$

定理 27.1 已经固定整个纤维内的 $b,c,j,t,u,d,g$，仅 $r$ 可在两个源根间变化；$n=j+r$。故两个最终迹之差分别为 $4\Delta r$、$2\Delta r$。再用 $g(7)=4z/45>0$ 得式 (28.1)。若 $r'=r$，所有参数和整个目标相同；若完整目标不同，则 $\Delta r\ne0$，两个最终响应之差都非零，故两映射均单射。这也完整重放了原时钟 $7$。

对任意 $S\subseteq\mathcal R_z$，若 $|S|<2$，定义 9.1 的原基数护栏已否定 $L_1$。若 $|S|\ge2$，对每个最终动作及每个实际响应，其响应子纤维至多单点，故没有 $L_0$ 叶，也不能满足 $L_1$ 的递归分句。这里既未预设有限支持，也未要求两个最终动作使用同一终端对；每个响应叶本身都没有任何不同目标对。∎

**推论 28.2（锚定响应的饱和性）。** 任意增加合法世界、任意改变候选世界的漂移或增益根型，只要仍要求它们实现同一个 $H_6(z)$，都不能使该实际第六纤维获得 $L_1$。

证明。实现同一实际历史的全部合法世界已经是 $\mathcal R_z$；任何这样的扩充仍为其子集。应用定理 28.1。该结论只涉及式 (24.1) 中实际第六 $M$ 响应恰为 $z$ 的纤维。∎

## 29. 有理种子的两种第六延续与终端响应

**命题 29.1（固定三根种子的准确消费）。** 取已有三根表达式的明确有理种子

$$
\begin{gathered}
z_* =\frac{1728}{25},\qquad Y_* =\frac{9328}{125},\qquad
b_* =\frac{31}{24},\qquad c_* =\frac{17}{96},\\
r_- =\frac{17}{48},\qquad r_+ =\frac{31}{48},\qquad
 d_* =\frac{1728}{25},\qquad
 g_*(s)=\frac{96}{125}(s-3)(s-5)(s-6).
\end{gathered}
\tag{29.1}
$$

这两个完整世界恰好耗尽 $\mathcal R_{z_*}$。在它们各自原轨迹中，第六动作取 $J$ 或 $M$ 时，第六实际响应均为 $1728/25$，但两个最终动作的响应如下：

| 源根 $r$ | 第六动作 | 第六实际响应 | 最终 $J$ 响应 | 最终 $M$ 响应 |
| --- | --- | --- | --- | --- |
| $17/48$ | $J$ | $1728/25$ | $12792/125$ | $15272/125$ |
| $31/48$ | $J$ | $1728/25$ | $13016/125$ | $15272/125$ |
| $17/48$ | $M$ | $1728/25$ | $13744/125$ | $19696/125$ |
| $31/48$ | $M$ | $1728/25$ | $14640/125$ | $20144/125$ |

证明。$Y_*=(59z_*-720)/45$，且式 (27.1) 在 $z_*$ 处给恰好上述 $b_*,c_*,d_*,g_*$。源判别式及两源的不同性分别由

$$
1-4b_*c_* =\frac{49}{576}>0,\qquad
(r_+-r_-)^2=\frac{49}{576}>0
\tag{29.2}
$$

给出；所有源条目严格正。定理 27.1 因而证明这里恰有这两个世界，而不只是证明它们属于某个预选根类。整个增益在原时钟上的值是

| 原时钟 $i$ | $g_*(i)$ |
| --- | --- |
| $0$ | $-1728/25$ |
| $1$ | $-768/25$ |
| $2$ | $-1152/125$ |
| $3$ | $0$ |
| $4$ | $192/125$ |
| $5$ | $0$ |
| $6$ | $0$ |
| $7$ | $768/125$ |

原时钟 $0,\ldots,5$ 因而依次给 $0,24,48,1728/25,9328/125,1728/25$。$g_*(6)=0$ 使这两个世界在任一种第六动作下都给 $d_*=1728/25$；这不是在另一条轨迹上重设增益。

为核对表中第六 $J$ 后的末响应，对时钟 $5$ 的原矩阵左乘 $J$ 得
$A_{6,J}=\left(\begin{smallmatrix}3&1\\2&1\end{smallmatrix}\right)$，再分别左乘 $J,M$ 得

$$
A_{7,JJ}=\begin{pmatrix}2&1\\3&1\end{pmatrix},\qquad
A_{7,JM}=\begin{pmatrix}2&1\\5&2\end{pmatrix}.
$$

其迹分别为 $1+r+3b+c$ 和 $2+5b+c$。第六 $M$ 后的两末迹则是式 (28.2)。将两种源根和同一个 $d_*,g_*(7)$ 代入，正好得到全部四行终端表。

特别地，第六 $J$ 后最终 $M$ 的确有一个相同响应 $15272/125$，而最终 $J$ 的两响应相差 $224/125$。这个单独的碰撞只属于第六 $J$ 延续上的一个末叶。第六 $M$ 后，最终 $J$、最终 $M$ 的差分别为

$$
\frac{896}{125},\qquad \frac{448}{125},
\tag{29.3}
$$

都非零；这也等于式 (28.1) 在 $\Delta r=7/24$ 处的值。因而不能把第六 $J$ 的一个末叶搬到第六 $M$ 的实际历史中，修复已经耗尽的 $\mathcal R_{z_*}$。本命题的第六 $J$ 表只计算这两个指定世界的延续，并不分类该第六 $J$ 响应的整个兼容纤维。∎

## 30. 与全源图的接口及仍未解决的共同实现

**注记 30.1（复用内容与完整纤维增量）。** 定义 1.1 的源、一个整个增益和一个常漂移，以及命题 1.2、定义 9.1 的实际迹和失败递归，是这里的原模型接口。§§11–13 的全源图仍可容纳这里的完整世界；本追加部分不重做其任意第五动作图谱或八槽接口。因式定理得到的三根表达式也已见式 (10.18)，但该式原来的参数窗口及其反证用途不能移到新的父线上；这里单独使用其因式计算，不借用旧窗口的排除结论。

式 (29.1) 的有理种子、指定三根类中的源根恢复及单个终端碰撞是被消费的明确对象，不作为新增的全类排除理由。真正增加的结论是：在 $z\ge54$、$Y=(59z-720)/45$、第五实际 $M$ 响应为 $z$、第六实际 $M$ 响应也为 $z$ 的条件下，即使开始时允许任意实漂移、任意非零三次及以下整个增益及任意合法源，也只能得到式 (27.1) 的世界。引理 24.2–26.2 排除了所有 $k\ne0$ 竞争者，随后定理 27.1 的反向重放证明世界存在性的充分性。这一步把所选三根子类的计算提升为这一个完整实际纤维的穷尽分类；它没有把根型当作先验，也不依靠数值搜索证明连续域正性。

插值、二项式恒等式、首一二次式的根序和因式定理是复用的普通数学方法。六组有限有理系数和它们连接原响应方程的恒等式是本具体分类的证书，不把一般 Bernstein 正性本身列为新的数学成果。这里不作外部文献穷尽或全局优先权判断；全部陈述是显示的普通代数证明，不附加 Lean 或内核认证、性能、稳定性结论。

**注记 30.2（实际响应、父点与原根义务的保留）。** 定理 27.1、28.1 穷尽的只是在式 (24.1) 中完整写定的实际第六纤维。即使保持同一个 $H_5(z)$，第六 $M$ 取其他实际响应的全部世界及其 $L_1$ 问题仍未分类；第六 $J$ 的其他世界和响应也未被命题 29.1 的两世界表排除。固定此父线但改变私有第五响应、改变第五动作，或改用其他父点，均须重新满足其原实际历史，不能从本固定响应的饱和性推出不存在。

同一精确 $H_4$ 上两个第五动作所需的完整 $L_2$ 支持仍须共同实现；每一支自己的第五响应、两个第六实际响应及两种最终动作可分别选取的不同终端对，仍是命题 9.2 所述同时义务。E 路线及自由父点的十六源、三十二源共同系统也没有在这里得到合法联合解或被排除。已知父点或不同实际响应上分别存在的碰撞，不能通过取并集自动成为一个满足这些同时条件的支持。

即便某个共同父点以后获得局部 $L_3$，更早祖先的相反动作、实际响应、提前停止与从原根连接的义务仍然存在。本追加部分不解决原根八读与九读下界的二择，不给九读上界，也不声称一个局部纤维的单射构成全局恢复策略。所有路径始终只有原左动作和原时钟 $0,\ldots,7$，没有重置、复制、空动作、跳读或额外观测端口。

## 追加锚（本行以下为增补区）
