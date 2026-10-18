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

## 31. 全实父读数上的整个单增益方向障碍

**定义 31.1（有符号方向的整个第五 M 类）。** 本节采用定义 1.1 的全部合法完整世界及定义 9.1 的递归，令

$$
H_{5M}(z,Y,p)=(0,J,24,M,48,J,z,M,Y,M,p),
\qquad z,Y,p\in\mathbb R.
$$

不采用式 (1.3) 的参数窗口。对任意固定的非零实多项式 $h$，$\deg h\le3$，置

$$
\mathcal K_h(z,Y,p)=\{(P,g,d)\in\mathcal F(H_{5M}(z,Y,p)):
 g=\lambda h,\ \lambda\in\mathbb R\setminus\{0\}\}.
\tag{31.1}
$$

尺度允许两种符号，比例关系是整个多项式的关系。每个世界仍有自己的源和漂移；不增加对称性、次数恰为三、采样非零或终端对共用的条件。

**定理 31.2（任意支持的单方向第五 M 排除）。** 对所有定义 31.1 的 $z,Y,p,h$ 及任意子集 $S\subseteq\mathcal K_h(z,Y,p)$，包括无限子集，

$$
\neg L_2(S,H_{5M}(z,Y,p)).
\tag{31.2}
$$

因此一个第五 $M$ 的 $L_2$ 支持所用的整个增益不能全在同一个实方向中。

证明。沿用《[FIB 实际 JMJM 的承诺纤维与联合例外几何](FIB_JMJM_PROMISED_FIBERS_AND_JOINT_EXCEPTION_GEOMETRY.md)》定理 4.1 的有符号提升，写 $h_i=h(i)$，并置

$$
R=\lambda P=
\begin{pmatrix}A&B\\J_0-B&\lambda-A\end{pmatrix}.
\tag{31.3}
$$

初读零恰给 $d=-\lambda h_0$。反过来，满足

$$
\lambda\ne0,\qquad \det R=0,\qquad R/\lambda\text{ 逐项严格正}
\tag{31.4}
$$

的 $R$ 唯一恢复 $P=R/\lambda,g=\lambda h,d=-\lambda h_0$，且 $\operatorname{tr}P=1$。此对应保留负尺度、任意漂移、对称源和所有降次。原时钟 $i$ 的响应就是线性泛函

$$
h_i\operatorname{tr}(A_iR)-h_0\lambda.
\tag{31.5}
$$

原左乘矩阵在时钟 $0,\ldots,5$ 依次为

$$
I,\quad
\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
\begin{pmatrix}1&1\\1&0\end{pmatrix},\quad
\begin{pmatrix}1&0\\2&1\end{pmatrix},\quad
Q=\begin{pmatrix}2&1\\3&1\end{pmatrix}.
$$

故在坐标 $(A,J_0,B,\lambda)$ 中，五个实际响应方程的行及右端恰为

$$
\begin{array}{c|rrrr|r}
 i&A&J_0&B&\lambda&z_i\\ \hline
1&0&h_1&0&-h_0&24\\
2&0&0&h_2&h_2-h_0&48\\
3&h_3&h_3&0&-h_0&z\\
4&0&0&2h_4&h_4-h_0&Y\\
5&h_5&h_5&2h_5&h_5-h_0&p
\end{array}
\tag{31.6}
$$

这五式与式 (31.4) 是完整世界的充分必要条件，不只是一组必要投影。

先给出五行的穷尽秩分类。若有兼容世界，前两行独立：$h_1=h_2=0$ 会迫使 $24=48=d$；恰有一个为零时，其对应非零读数迫使 $h_0\ne0$，而另一行还有独立的 $J_0$ 或 $B$ 列。两者均非零时也立即独立。若 $h_3\ne0$ 或 $h_5\ne0$，相应行在 $A$ 列的非零项给秩至少三。只须继续处理 $h_3=h_5=0$。

若此时 $h_0=0$，则 $h_1h_2\ne0$，且 $h_4\ne0$，否则 $h$ 在 $0,3,4,5$ 有四个不同根。第 $1,2,4$ 行在列 $(J_0,B,\lambda)$ 上的行列式为 $-h_1h_2h_4\ne0$。若 $h_0\ne0$ 且 $h_1h_2\ne0$，第 $1,2,3$ 行在这些列上的行列式为 $-h_0h_1h_2\ne0$。若 $h_2=0$，则 $h_1h_4\ne0$，因为 $2,3,5$ 已用尽一个非零三次及以下多项式的不同根；第 $1,2,4$ 行的相应行列式是 $2h_0h_1h_4\ne0$。唯一剩余情形是

$$
h_1=h_3=h_5=0,\qquad
h(X)\text{ 是 }(X-1)(X-3)(X-5)\text{ 的非零倍数}.
\tag{31.7}
$$

因此，除式 (31.7) 外，所有兼容提升都在一条仿射直线或一个点内；不要求该直线与行列式零集的交点有限。

在一条仿射直线上，每个式 (31.5) 都恒定或单射。假设其中一个任意基数子集有 $L_2$。对每个第六动作 $E$，它所选实际响应纤维中须有至少两个不同完整目标，所以第六响应泛函在整条直线上恒定。再对每个最终动作 $G$，其所选 $L_0$ 叶有两个不同目标，故对应 $EG$ 的最终响应泛函也在整条直线上恒定。因此两个第六泛函和四个最终泛函全都恒定。这里先允许不同第六响应、不同末叶及不同终端对；是在证明恒定之后，才可任取支持中的两个不同世界，推出它们在整个两动作未来都相同。

下面证明这样的两个不同世界不存在。取提升之差 $V=R_2-R_1$，令 $\sigma=\operatorname{tr}V$，并写

$$
QV=\begin{pmatrix}a&\beta\\\gamma&e\end{pmatrix}.
$$

按时序 $JJ,JM,MJ,MM$，四个时钟七迹差为

$$
a+e,\quad a+\beta+e,\quad a+\gamma+e,
\quad a+\beta+\gamma+2e;
\tag{31.8}
$$

两个时钟六迹差为 $\beta+\gamma$、$\beta+\gamma+e$。完整响应相等即前四项乘 $h_7$、后两项乘 $h_6$ 后都等于 $h_0\sigma$。

若 $h_7\ne0$，四个最终等式相减给 $\beta=\gamma=e=0$；第六 $J$ 等式给 $h_0\sigma=0$，第一个最终等式再给 $a=0$。于是 $V=0$。

若 $h_7=0$、$h_6\ne0$，最终等式给 $h_0\sigma=0$，第六等式给 $e=0,\gamma=-\beta$。由 $Q^{-1}=\left(\begin{smallmatrix}-1&1\\3&-2\end{smallmatrix}\right)$，

$$
V=\begin{pmatrix}-a-\beta&-\beta\\3a+2\beta&3\beta\end{pmatrix},
\quad
\sigma=-a+2\beta,\quad
\operatorname{tr}(JV)=3a+\beta,\quad
\operatorname{tr}(A_2V)=-a+\beta.
\tag{31.9}
$$

前两个原响应给 $h_1(3a+\beta)=h_2(-a+\beta)=0$。若 $h_1h_2\ne0$，两线性式的系数行列式为 $4$，故 $a=\beta=0$。若 $h_1=0$，实际读数 $24$ 迫使 $h_0\ne0$，故 $\sigma=0$，而 $h_2\ne0$；$\sigma,-a+\beta$ 的行列式为 $1$。若 $h_2=0$，同理由读数 $48$ 得 $h_0\ne0,\sigma=0,h_1\ne0$；$\sigma,3a+\beta$ 的行列式为 $-7$。各支仍给 $V=0$。

若 $h_6=h_7=h_0=0$，则 $h(X)=\eta X(X-6)(X-7)$，$\eta\ne0$，所以 $h_1,h_2,h_3,h_4$ 均非零。第二、第四原响应差给

$$
\sigma+V_{12}=\sigma+2V_{12}=0.
$$

于是 $\sigma=V_{12}=0$；第一、第三原响应差又给 $V_{21}=V_{11}=0$，继而 $V_{22}=0$。

最后，若 $h_6=h_7=0$、$h_0\ne0$，最终等式给 $\sigma=0$，所以两世界的尺度、整个增益和漂移都相同。除根 $6,7$ 外至多还有一个不同根。若 $g(1),g(2),g(3)$ 全非零，前三个原响应恢复共同的 $j,b,n$，从而恢复整个源。若 $g(2)=0$，则 $g(1),g(3),g(4)\ne0$，第四响应恢复 $b$，第一、第三恢复 $j,n$。若 $g(3)=0$，则 $g(1),g(2),g(5)\ne0$，第一、第二恢复 $j,b$，实际第五 $M$ 的迹 $n+u$ 恢复 $n$。唯一余支 $g(1)=0$ 给

$$
d=24,\qquad g(X)=\frac47(X-1)(X-6)(X-7),\qquad
 g(2)=\frac{80}7,\quad g(3)=\frac{96}7,\quad b=\frac{11}{10}.
\tag{31.10}
$$

这里复用《[FIB 采样根坍缩与同父失败核心](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md)》引理 4.1 中的根 $1,6,7$ 计算，只用显示的代数式，不用其旧父窗口结论。$n$ 已由第三读固定，源根须满足

$$
r^2-\frac{21}{10}r+bn-b^2=0.
$$

两个不同根若都在 $(0,1)$，其和会小于 $2$，与 $21/10$ 矛盾。因此此支也至多一个源。这些分支包括在 $4$ 或 $5$ 的附加根、所有降次及所有重复根。两个世界在全部未来一致时必相同，完成非例外直线的排除。

还须处理没有被直线论证覆盖的式 (31.7)。第一读与初读分别固定 $d=24$ 和

$$
g(X)=\frac85(X-1)(X-3)(X-5).
$$

第二读固定 $b=4$。整个兼容族恰为

$$
P(r)=\begin{pmatrix}r&4\\r(1-r)/4&1-r\end{pmatrix},
\quad0<r<1,\qquad (z,Y,p)=(24,-96/5,24),
\tag{31.11}
$$

其他 $z,Y,p$ 下为空。其充分性可直接由同一个增益的样本

$$
(g(0),\ldots,g(7))=(-24,0,24/5,0,-24/5,0,24,384/5)
$$

及原迹重建。式 (31.11) 是严格合法的无限族，不是有限交点情形。其实际第六 $M$ 响应为

$$
552+24\left(r+\frac{r(1-r)}4\right)=552+30r-6r^2,
\qquad \frac{d}{dr}(552+30r-6r^2)=30-12r>18.
$$

所以第六 $M$ 的每个实际响应纤维至多单点，不能有 $L_1$。该无限族及其任意子集均无 $L_2$。点、空集和单点子集则由原停止基数条件排除。各情形合起来证明式 (31.2)。∎

**推论 31.3（只对整个支持施加的秩护栏）。** 若定义 9.2 的第五 $M$ 八槽实现 $L_2$，则以各槽为行的矩阵

$$
\bigl(g_W(0),g_W(1),g_W(2),g_W(3)\bigr)_W
\tag{31.12}
$$

秩至少为二。更一般地，任意第五 $M$ 的 $L_2$ 支持都包含两个不成比例的整个增益。

证明。四个不同节点上的取值是三次及以下多项式空间的线性同构；秩至多一使所有非零增益处于一个实方向，违反定理 31.2。这里只约束整个支持；一个混合支持中的某些成比例成员、某个终端对或某个第六纤维不因此被禁止。∎

## 32. 有理种子第五 M 的完整多项式表示

**定义 32.1（种子数据与正迹坐标）。** 本节至 §34 固定

$$
z_0=p_0=\frac{1728}{25},\qquad Y_0=\frac{9328}{125},
\qquad H_5^0=H_{5M}(z_0,Y_0,p_0).
\tag{32.1}
$$

在严格源域 $0<r<1,b>0$ 上置

$$
\begin{aligned}
c&=\frac{r(1-r)}b,& J_0&=b^2+r-r^2,& N&=J_0+br,\\
t&=1+b,&u&=1+2b,&T&=J_0tN,& V&=N+ub.
\end{aligned}
\tag{32.2}
$$

于是 $j=J_0/b$、$n=N/b$，且 $j,t,n,T,b$ 严格正。以下 $N,V$ 等字母仅用于本节至 §34；它们与 §25 的一元多项式分别解释。定义有理系数多项式

$$
\begin{aligned}
a_4&=T-4btN+6J_0N-4bJ_0t,\\
a_5&=4T-15btN+20J_0N-10bJ_0t,\\
\beta_4&=96btN-288J_0N+4z_0bJ_0t,\\
\beta_5&=360btN-960J_0N+10z_0bJ_0t,\\
E&=T+ua_4,&B&=Y_0T-u\beta_4,\\
E_5&=bT+Va_5,&B_5&=p_0bT-V\beta_5,\\
C_6&=10T-36btN+45J_0N-20bJ_0t,\\
D_6&=864btN-2160J_0N+20z_0bJ_0t,\\
C_7&=20T-70btN+84J_0N-35bJ_0t,\\
D_7&=1680btN-4032J_0N+35z_0bJ_0t.
\end{aligned}
\tag{32.3}
$$

以下四个商是 $\mathbb Q[r,b]$ 中的精确多项式商：

$$
\begin{aligned}
R&=\frac{125(E_5B-EB_5)}T,&
G_6&=\frac{C_6B+D_6E}T,\\
G_7&=\frac{C_7B+D_7E}T,&
G_{65}&=\frac{C_6B_5+D_6E_5}T.
\end{aligned}
\tag{32.4}
$$

亦即它们由将式 (32.2)–(32.3) 代入后消去公因子 $T$ 唯一确定，在 $T=0$ 的闭盒边界也作为多项式取值，不在那里作有理除法。再置

$$
\begin{aligned}
D_0&=bE,\\
H&=bB+(N+2ub)G_6,\\
F&=bB+(2N+bt+2br)G_7,\\
H_5&=bB_5+(N+2ub)G_{65},\\
Z_4&=-HE,& Z_5&=-H_5E_5,\\
K&=F-2H,\\
Q_*&=(K_rD_0-K(D_0)_r)R_b
       -(K_bD_0-K(D_0)_b)R_r.
\end{aligned}
\tag{32.5}
$$

下标 $r,b$ 表示偏导。$H_5$ 是多项式，不表示历史。为确定有限系数数组，所需的实际双次数为

$$
\begin{array}{c|rrrrrrrrrr}
p&R&E&E_5&G_6&G_7&G_{65}&H&F&H_5&Q_*\\ \hline
\deg_r p&6&4&6&4&4&6&6&6&8&15\\
\deg_b p&7&6&7&5&5&6&7&7&8&19
\end{array}
\tag{32.6}
$$

**命题 32.2（完整种子世界与分母保护）。** 任意严格合法源上的整个增益由原节点 $0,1,2,3$ 及漂移唯一给出：

$$
g(X)=-d\,\ell^{0123}_0(X)
 +\frac{24-d}{j}\ell^{0123}_1(X)
 +\frac{48-d}{t}\ell^{0123}_2(X)
 +\frac{z_0-d}{n}\ell^{0123}_3(X),
\tag{32.7}
$$

其中 $\ell^{0123}_i(X)=\prod_{0\le q\le3,q\ne i}(X-q)/(i-q)$。该源和漂移给出 $H_5^0$ 的完整合法世界，当且仅当

$$
Ed=B,\qquad E_5d=B_5.
\tag{32.8}
$$

任一这样的世界都有 $R=0$。若 $E\ne0$，其实际第六 $M$、最终 $J$ 响应分别为

$$
h=\frac H{bE},\qquad f_J=\frac F{bE},\qquad d=\frac BE.
\tag{32.9}
$$

若 $E_5\ne0$，则也有

$$
h=\frac{H_5}{bE_5},\qquad d=\frac{B_5}{E_5}.
\tag{32.10}
$$

证明。式 (32.7) 在四个原节点上取所需值，故是唯一的三次及以下多项式。其余四个值为

$$
\begin{aligned}
g(4)&=(a_4d+\beta_4)/T,&g(5)&=(a_5d+\beta_5)/T,\\
g(6)&=(C_6d+D_6)/T,&g(7)&=(C_7d+D_7)/T.
\end{aligned}
\tag{32.11}
$$

将节点 $4,5$ 的实际迹 $u,V/b$ 代入响应，清除正 $T,b$，分别恰得式 (32.8)。反向也恢复两条原响应；读数 $0,24$ 不同，故式 (32.7) 不可能为零多项式。消去式 (32.8) 的 $d$ 得 $R=0$。式 (32.4) 的多项式性可将式 (32.3) 相乘展开核对为

$$
TR=125(E_5B-EB_5),\quad TG_6=C_6B+D_6E,\quad
TG_7=C_7B+D_7E,\quad TG_{65}=C_6B_5+D_6E_5;
\tag{32.12}
$$

在 $\mathbb Q[r,b]$ 中各右端都含因子 $T$，消去后的次数是式 (32.6)。以原迹 $n+2u$、$2n+t+2r$ 代入式 (32.11)，在各自明确非零的 $E$ 或 $E_5$ 图内得到式 (32.9)–(32.10)。没有除以增益样本或最高次项，也未从 $R=0$ 单独断言世界存在。∎

## 33. 整个源域分割的有限有理系数证书

**定义 33.1（张量系数及唯一的有限二分树）。** 对一个非零有理多项式 $p(r,b)=\sum p_{kl}r^kb^l$，取其实际双次数 $(m,n)$；零多项式取 $(0,0)$。对有理闭盒 $I=[l_r,h_r]\times[l_b,h_b]$，定义

$$
\begin{aligned}
U^{m}_{ik}(l,h)
 &=\sum_{a=0}^{\min(i,k)}
 \frac{\binom ka\binom ia}{\binom ma}l^{k-a}(h-l)^a,\\
\mathcal B_I(p)_{ij}
 &=\sum_{k=0}^m\sum_{l=0}^n p_{kl}
 U^m_{ik}(l_r,h_r)U^n_{jl}(l_b,h_b),
 \quad 0\le i\le m,\ 0\le j\le n.
\end{aligned}
\tag{33.1}
$$

约定零次幂为一。即使某个盒边退化，这仍为确定的有理数组。记数组的最小、最大项为 $\underline{\mathcal B}$、$\overline{\mathcal B}$。它们包住整个盒上的多项式值，因为

$$
p(l_r+(h_r-l_r)s,l_b+(h_b-l_b)t)
 =\sum_{i,j}\mathcal B_I(p)_{ij}
 \binom mi s^i(1-s)^{m-i}\binom nj t^j(1-t)^{n-j},
\quad 0\le s,t\le1.
\tag{33.2}
$$

对某一坐标的任意系数列 $a_0,\ldots,a_q$，其中点分割完全由

$$
a_i^{(0)}=a_i,\qquad
 a_i^{(v+1)}=\frac{a_i^{(v)}+a_{i+1}^{(v)}}2
 \quad(0\le i<q-v)
\tag{33.3}
$$

确定。低半盒系数列为 $(a_0^{(0)},a_0^{(1)},\ldots,a_0^{(q)})$，高半盒为 $(a_0^{(q)},a_1^{(q-1)},\ldots,a_q^{(0)})$；另一坐标不变。各多项式始终使用自己的根数组次数，不在子盒删去端系数或改变次数。式 (33.3) 正是式 (33.2) 在两半区间的代数重写。

一个根数据由闭盒 $I$、可空的护栏多项式 $g$、有序符号列表 $(p_1,\sigma_1),\ldots,(p_q,\sigma_q)$ 及深度界 $d_*$ 构成，$\sigma_i\in\{+,-\}$。深度零数组由式 (33.1) 给出。每个节点依下列先后次序唯一归类：若护栏数组严格全正或严格全负，归类为 $X$；否则，在列表中取第一个全正且符号为 $+$、或全负且符号为 $-$ 的数组，归类为 $S_i$；否则深度等于 $d_*$ 时归类为 $U$；其余节点分为低、高两子盒，并用式 (33.3) 给各子数组。

通常深度 $d$ 偶数时分第一坐标，奇数时分第二坐标；若根盒的第二边退化，则每层都分第一坐标。每次都取精确中点，子盒按低、高次序编号。不存在护栏时不取 $X$；空符号列表时只能取 $X$ 或继续细分。归类要求严格不等式，护栏包含零的数组不能归入 $X$，零系数不能充作严格符号。

也可把这一有限定义写成接受递推。令 $\mathfrak A_d$ 为一个节点的值：$X$ 或 $S_i$ 叶取 $1$，$U$ 叶取 $0$，其他节点取两子值的乘积。节点总数在叶处为 $1$，在非叶处为 $1+$ 两子总数；最大深度取叶深度的最大值，各类叶数相加。这些递推在给定 $d_*$ 内定义了唯一有限有理证书，不需要选择任何细分位置或额外停止条件。

**定义 33.2（四个角图与十一组根数据）。** 置 $\epsilon=1/64$。在四个角图中用坐标 $(v,k)$，定义

$$
\begin{array}{c|cc|c}
\chi&r&b&0\le k\le k_\chi\\ \hline
O_A&v&kv&1\\
O_B&kv&v&1\\
T_A&1-v&kv&2\\
T_B&1-kv&v&1/2
\end{array}
\qquad 0\le v\le\epsilon.
\tag{33.4}
$$

对 $p=R,E,H$，令 $p^\chi(v,k)=p(r(v,k),b(v,k))$，并定义多项式

$$
\widehat R_\chi=R^\chi/v^3,\qquad
\widehat E_\chi=E^\chi/v^2,\qquad
\widehat H_\chi=H^\chi/v^3,\qquad
\widehat Z_\chi=-\widehat H_\chi\widehat E_\chi.
\tag{33.5}
$$

这里除掉的是精确公因子，所得多项式也在 $v=0$ 取值；不将 $v=0$ 除法代入原响应。由式 (32.2)–(32.5) 展开，每图中三个最低 $v$ 幂恰为 $3,2,3$。在 $O_A,T_A$ 中三个商的双次数依次是 $(4,7),(4,6),(4,7)$，在 $O_B,T_B$ 中依次是 $(4,6),(4,4),(4,6)$。

式 (33.1)–(33.3) 的十一组根数据如下。$\varnothing$ 表示无护栏；第十、十一行的列表次序不可交换。

| 组 | 根盒，按第一、第二坐标 | 护栏 | 有序符号列表 | $d_*$ |
| --- | --- | --- | --- | --- |
| $1$ | $[0,1]\times[5/4,5/4]$ | $\varnothing$ | $(R,+)$ | $24$ |
| $2$ | $[0,1]\times[1/2,5/4]$ | $\varnothing$ | $(R,+)$ | $24$ |
| $3$ | $[0,1]\times[5/4,8/5]$ | $\varnothing$ | $(E,-)$ | $24$ |
| $4$ | $[0,1]\times[5/4,8/5]$ | $R$ | $(R_b,-)$ | $24$ |
| $5$ | $[0,1]\times[5/4,8/5]$ | $R$ | $(Q_*,-)$ | $24$ |
| $6$ | $[0,\epsilon]\times[0,1]$ | $\varnothing$ | $(\widehat R_{O_A},+)$ | $18$ |
| $7$ | $[0,\epsilon]\times[0,1]$ | $\varnothing$ | $(\widehat R_{O_B},+)$ | $18$ |
| $8$ | $[0,\epsilon]\times[0,2]$ | $\widehat R_{T_A}$ | $(\widehat Z_{T_A},+)$ | $22$ |
| $9$ | $[0,\epsilon]\times[0,1/2]$ | $\widehat R_{T_B}$ | $(\widehat Z_{T_B},+)$ | $22$ |
| $10$ | $[0,1]\times[\epsilon,1/2]$ | $R$ | $(Z_4,+),(Z_5,+)$ | $24$ |
| $11$ | $[\epsilon,1-\epsilon]\times[0,\epsilon]$ | $R$ | $(Z_4,+),(Z_5,+)$ | $24$ |

**命题 33.3（精确有理递推值及无遗漏覆盖）。** 对上述十一组根，接受值全为一，所有 $U$ 叶数为零。有限递推的全部计数为

$$
\begin{array}{c|r|r|r|r|r|r}
\text{组}&\text{节点数}&\text{最大深度}&X&S_1&S_2&U\\ \hline
1&3&1&0&2&0&0\\
2&3&1&0&2&0&0\\
3&1&0&0&1&0&0\\
4&11&5&1&5&0&0\\
5&97&11&24&25&0&0\\
6&1&0&0&1&0&0\\
7&5&2&0&3&0&0\\
8&563&14&189&93&0&0\\
9&1&0&1&0&0&0\\
10&583&19&200&6&86&0\\
11&37&17&17&0&2&0
\end{array}
\tag{33.6}
$$

节点总数为 $1305$。取各 $S_i$ 叶的同号系数极值再取最弱界，得到

$$
\begin{array}{c|l}
1&\min\underline{\mathcal B}(R)=62656961/3072\\
2&\min\underline{\mathcal B}(R)=177773/60\\
3&\max\overline{\mathcal B}(E)=-47981/2048\\
4&\max\overline{\mathcal B}(R_b)=-15584375/256\\
5&\max\overline{\mathcal B}(Q_*)=-2204957330721986967879833331/1125899906842624000\\
6&\min\underline{\mathcal B}(\widehat R_{O_A})=1261262875/1048576\\
7&\min\underline{\mathcal B}(\widehat R_{O_B})=7616579447/50331648\\
8&\min\underline{\mathcal B}(\widehat Z_{T_A})=
3438438062541270233382653433706069588186172415006657147/
23384026197294446691258957323460528314494920687616000
\end{array}
\tag{33.7}
$$

第 $10,11$ 组中每个 $S_i$ 叶的最小系数均大于 $1/10^{30}$。第 $9$ 组根本身已是 $X$ 叶。所有这些有理数均指整个数组的界。

此外，令

$$
R(r,8/5+x)=\sum_{q=0}^7 T_q(r)x^q.
\tag{33.8}
$$

对每个 $T_q$ 在 $r\in[0,1]$ 上取次数六的式 (33.1) 系数，其最大值按 $q=0,\ldots,7$ 依次为

$$
\left(
-\frac{33053605888}{78125},
-\frac{89157107712}{15625},
-\frac{49877860352}{3125},
-\frac{2532940288}{125},
-\frac{347958816}{25},
-\frac{133963936}{25},
-\frac{5437584}{5},
-90384
\right).
\tag{33.9}
$$

所以 $R<0$ 于整个 $[0,1]\times[8/5,\infty)$。

证明。式 (33.6)–(33.7) 是定义 33.1 的有限有理递推值。其系数的完全确定数据为式 (32.2)–(32.5)、四个精确因子消去式 (33.5) 以及定义 33.2 的十一行：根处先用式 (33.1)，之后每层只用式 (33.3)，并按定义 33.1 的严格先后次序归类。这给出式 (33.6) 的各项，例如第八组有 $282$ 个叶，分别为 $189$ 个 $X$ 和 $93$ 个 $S_1$，故节点数为 $2\cdot282-1=563$；第十组有 $200+6+86=292$ 个叶，故节点数为 $583$。所有组的相同递推在所列最大深度以前终结，无 $U$ 叶。式 (33.7) 是这些确定叶数组的有理极值，不含对实根位置的额外选择。

式 (33.9) 也可不展开整个尾式而逐项得到：若 $R=\sum R_{ij}r^ib^j$，则

$$
T_q(r)=\sum_{i=0}^6\left(\sum_{j=q}^7
 R_{ij}\binom jq(8/5)^{j-q}\right)r^i.
\tag{33.10}
$$

将式 (33.10) 代入式 (33.1)，在 $[0,1]$ 上取 $m=6$，逐项最大值就是式 (33.9)。每项严格负，且 $x\ge0$，故式 (33.8) 严格负。式 (33.1)、(33.3)、(33.10) 连同根数据是从有理系数到每个终叶的有限定义，全部端点均包含在盒中。

说明这些系数如何覆盖原严格源。第 $1,2$ 组分别给 $R(r,5/4)>0$ 和整个源间隙 $[1/2,5/4]$ 上 $R>0$；式 (33.9) 排除 $b\ge8/5$。第 $3$ 组给高盒内 $E<0$。第 $4,5$ 组的 $X$ 盒没有 $R=0$ 点，其余盒分别给所有高盒 $R$ 零点的 $R_b<0,Q_*<0$。

低盒的 $b\ge\epsilon$ 部分由第十组覆盖，$r\in[\epsilon,1-\epsilon]$、$0\le b\le\epsilon$ 的部分由第十一组覆盖。余下原点角方块 $0\le r,b\le\epsilon$ 中，$b\le r$ 时用 $O_A$，$r\le b$ 时用 $O_B$；除被严格源排除的 $(0,0)$ 外总有 $v>0$。第 $6,7$ 组使这两个角图无 $R$ 零点。

在末端角方块，写 $w=1-r$，$0\le w,b\le\epsilon$。若 $b\le2w$ 且 $w>0$，用 $T_A$，$v=w,k=b/w$；若 $b\ge2w$ 且 $b>0$，用 $T_B$，$v=b,k=w/b$。这两个图还覆盖边线 $w=0$ 或 $b=0$ 的非原点部分。对严格源 $v>0$，式 (33.5) 给

$$
R^\chi=v^3\widehat R_\chi,\qquad
Z_4^\chi=v^5\widehat Z_\chi.
$$

故第八组在所有实际 $R=0$ 点给 $Z_4>0$，第九组没有这样的零点。第 $10,11$ 组在所有其余低盒零点给 $Z_4>0$ 或 $Z_5>0$。因此没有丢掉靠近 $r=0,1$、$b=0$、$E=0$ 或 $E_5=0$ 的严格源序列；这些边界只是闭系数盒的一部分，并未被当作合法世界。∎

## 34. 有理种子上整条非负第六响应半线的排除

**定理 34.1（完整高分量图与固定响应单射）。** 在定义 32.1 的同一 $H_5^0$ 上，所有合法完整世界恰位于两个源区间

$$
0<b<\frac12\qquad\text{或}\qquad \frac54<b<\frac85.
\tag{34.1}
$$

低分量的实际第六 $M$ 响应全为负。对每个 $r\in(0,1)$，高分量中恰有一个完整世界；其 $b=b(r)$ 是光滑图。沿这个整个图，$f_J-2h$ 关于 $r$ 严格递增。因而对每个实数 $h\ge0$，最终 $J$ 的响应在整个

$$
\mathcal C_h=\mathcal F(H_5^0,M,h)
\tag{34.2}
$$

上对完整目标单射；$\mathcal C_h$ 的任意子集都没有 $L_1$。

证明。任一世界满足 $R=0$，命题 33.3 的源间隙及尾部符号给式 (34.1)。在低分量每个可能的零点，$Z_4>0$ 或 $Z_5>0$。前者给 $E\ne0$ 并且

$$
h=\frac{HE}{bE^2}<0;
$$

后者给 $E_5\ne0$ 并且 $h=H_5E_5/(bE_5^2)<0$。各处先保护相应分母，两个角图也已覆盖。故低分量结论适用于全部原世界，而非只适用于某个单一恢复图。

在高闭盒内，对每个 $r\in[0,1]$，有 $R(r,5/4)>0$、$R(r,8/5)<0$，故至少有一根。每个零点又有 $R_b<0$，所以都是严格向下的简单穿越，根至多一个。确实，固定 $r$ 后零点都简单且在紧区间内部，故只有有限个；若有相邻两个，前一个右侧为负、后一个左侧为正，中间必有另一个零点，矛盾。因此恰一根，且位于开区间 $(5/4,8/5)$。隐函数定理给 $b(r)$ 的光滑性，唯一性使局部图拼成整个图。

对 $0<r<1$，取 $c=r(1-r)/b(r)>0$。高盒处 $E<0$，故 $d=B/E$ 有定义。由 $TR=125(E_5B-EB_5)=0$ 得 $E_5d=B_5$，不必除以 $E_5$。命题 32.2 用同一个式 (32.7) 恢复唯一合法世界。反向，每个高分量世界都在此图上，所以图对完整世界既充分又必要。

沿图，由 $b'=-R_r/R_b$，

$$
\frac{d}{dr}(f_J-2h)
 =\frac{d}{dr}\frac K{D_0}
 =\frac{Q_*}{D_0^2R_b}>0,
\tag{34.3}
$$

因为 $D_0=bE\ne0$，且在所有图点 $Q_*<0,R_b<0$。若两个高分量世界有同一个 $h$ 及同一个 $f_J$，式 (34.3) 迫使 $r$ 相同，从而 $b,c,d$ 和整个增益都相同。因此高分量内固定 $h$ 后最终 $J$ 单射。

当 $h\ge0$ 时，低分量不能进入式 (34.2)，所以这已是整个 $\mathcal C_h$ 的单射结论。其每个最终 $J$ 响应叶至多一个完整目标，没有 $L_0$；故任何子集均不能满足 $L_1$ 的最终 $J$ 分句。最终 $M$ 是否选择另一对不影响这一排除，空集和单点也保留原停止语义。∎

**推论 34.2（种子处第五 M 支持的必要实际响应）。** 在 $H_5^0$ 上，若某个任意基数支持有 $L_2$，则它用于第六 $M$ 分句的实际响应必须满足 $h_M<0$。

证明。该分句需要一个 $L_1$ 子纤维，而定理 34.1 排除了所有 $h_M\ge0$。对 $h_M<0$，低、高分量可同时相关，以上论证不判定整个纤维的 $L_1$，也不判定该负半线上的单射性。∎

## 35. 四个独立实际读数的完整扰动方程

**定义 35.1（四数据纤维与严格非临界中心）。** 置

$$
\begin{aligned}
\Omega(z,Y,p,h)
 &=\mathcal F(0,J,24,M,48,J,z,M,Y,M,p,M,h),\\
\lambda_s&=(s,59s/45-16,s,s),\\
\frac{720}{13}&<s<72,\qquad K_6(s)>0,
\end{aligned}
\tag{35.1}
$$

其中 $K_6$ 是式 (27.2)。$\Omega$ 包含全部原合法完整世界，不限制增益根型、源对称性、增益次数或漂移。定理 27.1 给中心的两个完整世界 $W_s^-,W_s^+$：

$$
\begin{aligned}
b_s&=\frac{13s-720}{2s},&c_s&=\frac{1224-17s}{4s},\\
r_s^\pm&=\frac{1\pm\sqrt{1-4b_sc_s}}2,&d_s&=s,\\
g_s(X)&=\frac{s}{90}(X-3)(X-5)(X-6).
\end{aligned}
\tag{35.2}
$$

以下使用 $j=b+c,t=1+b,n=r+j,u=1+2b,v=n+2u$。这与 §24 的正迹完全相同；字母 $B,C,L$ 在本节起恢复式 (24.5) 的含义，与 §32 的多项式分别解释。

**命题 35.2（不除增益样本的扰动等价式）。** 置

$$
k=z-d,\qquad a=p-z,\qquad e=h-z,\qquad
\omega=Y-\frac{59z}{45}+16.
\tag{35.3}
$$

对严格合法源，用式 (24.4) 的四个基多项式定义一个整个增益

$$
g(X)=(k-z)\ell_0(X)+\frac{k}{n}\ell_3(X)
 +\frac{k+a}{n+u}\ell_5(X)+\frac{k+e}{v}\ell_6(X),
\qquad d=z-k.
\tag{35.4}
$$

则该完整世界属于 $\Omega(z,Y,p,h)$ 当且仅当

$$
\begin{aligned}
F_1={}&(4j-9)z+216+(9-jL)k
              +\frac{9ja}{n+u}-\frac{4je}{v}=0,\\
F_2={}&(u-14)z+720+Bk
              +\frac{12ta}{n+u}-\frac{5te}{v}=0,\\
F_3={}&Ck+\frac{12(3u-t)a}{n+u}
              +\frac{5(t-2u)e}{v}-45\omega=0,
\end{aligned}
\tag{35.5}
$$

其中明确地

$$
\begin{aligned}
L&=4+10/n-9/(n+u)+4/v,\\
B&=15-t\bigl(2+20/n-12/(n+u)+5/v\bigr),\\
C&=-59+20(u+t)/n+12(3u-t)/(n+u)+5(t-2u)/v.
\end{aligned}
\tag{35.6}
$$

这是四个独立实数据的等价表示。具体地，数据变换 $(z,Y,p,h)\mapsto(z,\omega,a,e)$ 可逆，其逆为

$$
Y=59z/45-16+\omega,\qquad p=z+a,\qquad h=z+e.
\tag{35.7}
$$

证明。指定的初读、第三、第五、第六响应正好给

$$
g(0)=k-z,\qquad g(3)=k/n,\qquad
 g(5)=(k+a)/(n+u),\qquad g(6)=(k+e)/v.
$$

四节点插值给式 (35.4)。同一个多项式还满足

$$
\begin{aligned}
9g(1)&=4g(0)+10g(3)-9g(5)+4g(6),\\
15g(2)&=2g(0)+20g(3)-12g(5)+5g(6),\\
45g(4)&=-g(0)+20g(3)+36g(5)-10g(6).
\end{aligned}
\tag{35.8}
$$

令原节点 $1,2,4$ 的响应残差分别为 $\rho_1,\rho_2,\rho_4$。代入式 (35.8)，有 $F_1=-9\rho_1$、$F_2=-15\rho_2$、$F_3=45\rho_4-F_2$。最后一式使用式 (35.3)、$2t=u+1$。所以三个 $F_i$ 同时为零与三个剩余原方程等价。式 (35.4) 在节点 $0,3,5,6$ 已实现其余全部指定响应；第一响应 $24$ 与初读零不同，故增益不为零多项式。所有分母都是正迹或固定节点差；$k=0$、低次数、重复增益根及零样本均在等价式内。∎

## 36. 闭源边界上的符号供应与未除法消元

**引理 36.1（闭源上 C 为零的排除接口）。** 允许有限闭源

$$
b,c\ge0,\quad 0\le r\le1,\quad bc=r(1-r),
\qquad j=b+c>0,\quad n=r+j>0.
\tag{36.1}
$$

令 $C,L,B$ 如式 (35.6)。若 $C=0$，则 $x=n/u$ 满足 $3/4<x<6/7$；式 (25.5)–(25.6) 的多项式满足

$$
A(x,r)>0,\qquad54A(x,r)-G(x,r)>0.
\tag{36.2}
$$

所以若另有 $A(x,r)z=G(x,r)$，必有 $z<54$。这一结论包括 $r=0,1$、$b=0$、$c=0$ 及源二次重根；闭源仅用于极限，不将这些边界加入合法世界域。

证明。这里复用引理 26.1 的全部六十九个有理系数及其闭区间符号。为明确其与扰动方程的对应，沿用定义 25.2，记

$$
\begin{aligned}
D&=13x^2+41x+40,&N&=118x^3+249x^2-49x-120,\\
V&=x(x+1)(x+2),&E&=5x^2+16x+20,\\
K&=-2D(D+N)+(D-14N)E,&Z_r&=xD-rN,\\
A(x,r)&=2Z_rK+9DN(D+N),\\
G(x,r)&=6912DNV+432D^2V+216DN(D+N)\\
&\hspace{1.5em}-5760DVZ_r-1440ENZ_r.
\end{aligned}
\tag{36.3}
$$

本节的 $N,V,E,K$ 均是这些一元多项式。令 $\tau=1/u\in(0,1]$。直接通分的恒等式

$$
2VC=\tau D-N
\tag{36.4}
$$

给 $\tau D=N$，所以 $0<N\le D$。$N''=708x+498>0$、$N(0)=-120$、$N(2/3)=-190/27$ 使 $N<0$ 于 $[0,2/3]$。又

$$
(N-D)(2/3+y)=-2164/27+382y+472y^2+118y^3
$$

在 $y\ge0$ 严格递增，且 $(N-D)(6/7)=3620/343>0$。故 $2/3<x<6/7$。这在 $\tau=1$ 时仍成立。

代入 $u=D/N$，秩一式变为

$$
q(R)=R^2-\frac{D+N}{2N}R
 +\frac{(D-N)(2xD-D+N)}{4N^2}=0
\quad\text{于 }R=r.
\tag{36.5}
$$

判别式为 $\Pi/(4N^2)$，其中

$$
\Pi=(5-8x)D^2+(8x-6)DN+5N^2.
$$

源给一个实根，而引理 26.1 的七个负系数给整个 $[2/3,3/4]$ 上 $\Pi<0$，所以 $x>3/4$。

写 $A_0=A(x,0),A_1=A(x,1)-A_0$。其余六十二个正系数给整个 $[3/4,6/7]$ 上

$$
A_1>0,\quad U>0,\quad W>0,\quad P_0>0,\quad P_1>0,
\tag{36.6}
$$

其中

$$
\begin{aligned}
U&=4NA_0+(D+N)A_1,\\
W&=4N^2A_0^2+2N(D+N)A_0A_1
 +(D-N)(2xD-D+N)A_1^2,\\
P_i&=54A(x,i)-G(x,i)\quad(i=0,1).
\end{aligned}
$$

置 $w=-A_0/A_1$，$q$ 的顶点为 $R_*=(D+N)/(4N)$。准确恒等式是

$$
R_*-w=\frac{U}{4NA_1}>0,\qquad
4N^2A_1^2q(w)=W>0.
\tag{36.7}
$$

因为 $q$ 首一且有实根，$q(w)>0$ 使 $w$ 位于两根闭区间之外，$w<R_*$ 又迫使它严格小于较小根。即使两根重复，根等于顶点，仍有同一严格次序。因而每个实际源根 $r$，包括可能的端点 $0,1$，都有

$$
A(x,r)=A_1(r-w)>0.
$$

再用 $A,G$ 关于 $r$ 仿射，

$$
54A(x,r)-G(x,r)=(1-r)P_0+rP_1>0
\quad(0\le r\le1).
\tag{36.8}
$$

端点时就是相应的严格正 $P_i$，所以不需要严格 $0<r<1$。若 $Az=G$，式 (36.2) 给 $A(54-z)>0$，从而 $z<54$。

最后说明消元接口不需要 $k\ne0$。记 $\gamma=9-jL$，在 $a=e=\omega=0$ 时令

$$
q_1=(4j-9)z+216+\gamma k,\qquad
q_2=(u-14)z+720+Bk.
$$

只要 $C=0$，代入 $u=D/N$ 后，式 (25.10) 是恒等式

$$
Bq_1-\gamma q_2=\frac{Az-G}{2NDV}.
\tag{36.9}
$$

它先严格消去 $k$，不除以 $k,B,\gamma,A$ 或任何消元行列式。因此也能用于 $k=0$、无界 $k$ 已被消去后的极限，以及闭源的各退化层。∎

## 37. 任意完整世界序列的无逃逸

**定理 37.1（中心附近整个原世界类的序列控制）。** 固定定义 35.1 的任意 $s$。若

$$
\lambda_m=(z_m,Y_m,p_m,h_m)\longrightarrow\lambda_s,
\qquad W_m\in\Omega(\lambda_m),
\tag{37.1}
$$

则 $k_m=z_m-d_m\to0$，源坐标及增益系数有界；任意这样的序列都有子列收敛到 $W_s^-$ 或 $W_s^+$。更准确地，所有收敛子列的极限都在这两个严格合法世界中。因而对这两个世界的任意开邻域之并，存在 $\lambda_s$ 的数据邻域，使全部相容原世界都落在该并内。

证明。式 (35.3) 给 $a_m,e_m,\omega_m\to0$。先证 $k_m\to0$。反设有子列 $|k_m|\ge\kappa>0$，则

$$
a_m/k_m\to0,\qquad e_m/k_m\to0,
\qquad\omega_m/k_m\to0.
$$

置 $x=n/u>0,\tau=1/u\in(0,1)$。将式 (35.5) 的第三式除以此处非零的 $k$ 并通分，得到精确恒等式

$$
\begin{aligned}
f(x,\tau)&=\frac ek-\mathcal R(x,\tau)\frac ak
                       +\mathcal S(x,\tau)\frac\omega k,\\
f(x,\tau)&=\frac{\tau D(x)-N(x)}{5(3-\tau)x(x+1)},\\
\mathcal R(x,\tau)&=\frac{12(5-\tau)(x+2)}{5(3-\tau)(x+1)},\\
\mathcal S(x,\tau)&=\frac{18(x+2)}{3-\tau}.
\end{aligned}
\tag{37.2}
$$

在 $x>0,0\le\tau\le1$ 上有明确统一界

$$
0<\mathcal R\le\frac{48}5,\qquad
0<\frac{\mathcal S}{x+1}\le18.
\tag{37.3}
$$

若 $x\to0$，$f$ 一致趋于正无穷，因为分子趋于 $40\tau+120\ge120$，而式 (37.2) 右端趋于零。若 $x\to\infty$，则一致地

$$
\frac{f(x,\tau)}x+\frac{118}{5(3-\tau)}\longrightarrow0.
\tag{37.4}
$$

此时将式 (37.2) 除以 $x$，由式 (37.3)，右端仍趋于零，左端却负且远离零。故该子列的 $x$ 有正下界和有限上界。

若 $\tau\to0$，则 $u,b\to\infty$；$bc\le1/4$ 给 $c/u\to0$，且 $r/u\to0,b/u\to1/2$，故 $x\to1/2$。然而

$$
f(1/2,0)=6,
$$

与式 (37.2) 右端趋于零矛盾。因此 $\tau$ 也有正下界。抽取子列后 $r,b,c$ 都趋于有限非负值，且 $n=xu$ 的极限正。若 $j\to0$，则 $b,c\to0$，闭源秩一关系迫使 $r$ 趋于 $0$ 或 $1$；$n>0$ 的极限排除 $0$，所以 $(x,\tau)\to(1,1)$。但

$$
f(1,1)=-\frac{26}5\ne0,
$$

仍矛盾。因此 $j$ 的极限也正，所有迹分母在这个极限保持为正，式 (37.2) 给 $C=0$。

此时不能先对含 $k_m$ 的两个方程分别取极限，因为 $k_m$ 还可能无界。先在每个 $m$ 上作严格消元：令 $\gamma=9-jL$，式 (35.5) 给

$$
\begin{aligned}
0=B F_1-\gamma F_2
={}&B\bigl((4j-9)z+216\bigr)
 -\gamma\bigl((u-14)z+720\bigr)\\
&+\frac{9Bj-12\gamma t}{n+u}\,a
 +\frac{-4Bj+5\gamma t}{v}\,e.
\end{aligned}
\tag{37.5}
$$

这里 $k$ 已准确抵消；其余系数在所得紧源子列上有界。现在取极限，$a,e\to0$，且 $C=0$，由式 (36.9) 得

$$
A(x,r)s=G(x,r).
$$

引理 36.1 适用于这个可能在边界的闭源，给 $s<54$，与 $s>720/13>54$ 矛盾。故不存在 $|k_m|\ge\kappa$ 子列，已证 $k_m\to0$，于是 $d_m\to s$。

接着控制增益和所有源逃逸。原节点 $0,2,4,5$ 的值是

$$
g(0)=-d,\qquad g(2)=\frac{48-d}{t},\qquad
 g(4)=\frac{Y-d}{u},\qquad g(5)=\frac{p-d}{n+u}.
\tag{37.6}
$$

因 $t\ge1,u\ge1,n+u\ge1$，这四个实际节点值全有界。固定四节点的插值矩阵可逆，所以整个三次及以下多项式的四个系数有界，因而每个固定节点处的增益值也有界。

若 $b_m\to\infty$，则式 (37.6) 后三个值都趋于零，而 $g(0)\to-s$。唯一插值极限是

$$
g_\infty(X)=\frac s{40}(X-2)(X-4)(X-5),
\qquad g_\infty(1)=-\frac{3s}{10}\ne0.
\tag{37.7}
$$

但 $j\ge b\to\infty$，原第一响应 $24=d+jg(1)$ 迫使 $g(1)\to0$，矛盾。所以 $b$ 有界。

若 $c_m\to\infty$，则 $bc\le1/4$ 迫使 $b_m\to0$，而 $j,n,n+u\to\infty$。原方程给 $g(1),g(3),g(5)\to0$、$g(0)\to-s$，故四节点 $0,1,3,5$ 的唯一极限是

$$
g_\infty(X)=\frac s{15}(X-1)(X-3)(X-5),
\qquad g_\infty(2)=\frac s5.
\tag{37.8}
$$

另一方面，$t\to1$ 使式 (37.6) 给 $g(2)\to48-s$，迫使 $s=40$，矛盾。所以 $c$ 也有界。这两个反证分别排除了所有无界源子列，包含 $b,c$ 同时趋大的候选，因为秩一约束本已禁止后者。

抽取收敛源及增益系数子列。$j$ 不能趋于零：$g(1)$ 有界，第一响应会给 $24=s$。于是 $n\ge j$ 有正下界。式 (35.4) 给

$$
g(3)\to0,\qquad g(5)\to0,\qquad g(6)\to0,
\qquad g(0)\to-s.
$$

因此整个增益趋于 $g_s$。原时钟 $1,2$ 及其非零中心增益 $-4s/9,-2s/15$ 强迫

$$
j\longrightarrow\frac{9(s-24)}{4s},\qquad
 t\longrightarrow\frac{15(s-48)}{2s},
$$

从而 $b\to b_s>0,c\to c_s>0$。闭秩一式给 $r(1-r)=b_sc_s$，所以极限恰是 $r_s^-$ 或 $r_s^+$，二者都严格在 $(0,1)$。这同时排除了最终可能的 $r=0,1,b=0,c=0$ 边界；所有极限世界严格合法，且正好是式 (35.2)。

若最后的数据邻域结论不成立，可在趋于 $\lambda_s$ 的数据点各选一个落在所给两个世界邻域之外的相容世界。前述结论给一个收敛到 $W_s^-$ 或 $W_s^+$ 的子列，终将进入其开邻域，矛盾。这就把任意世界序列的控制变成对整个纤维的统一无逃逸。∎

## 38. 四数据开邻域的恰两世界及两个末动作单射

**定理 38.1（严格非临界中心的整个四维邻域）。** 对定义 35.1 的每个 $s$，存在包含 $\lambda_s$ 的开邻域 $V_s\subset\mathbb R^4$，使对每个 $(z,Y,p,h)\in V_s$，整个 $\Omega(z,Y,p,h)$ 恰有两个合法完整世界。这两个世界分别连续延续 $W_s^-$、$W_s^+$，并且原时钟七的最终 $J$、最终 $M$ 响应各自在整个纤维上单射。因此整个纤维有 $L_0$ 而无 $L_1$，任意子集也无 $L_1$。

这里四数据独立变化，不要求 $Y=59z/45-16$、$p=z$ 或 $h=z$。结论对每个数据点下的全部原世界成立；不作共同增益、共同漂移、指定根型、恰三次增益或固定终端对承诺。

证明。在严格源图中写 $c=r(1-r)/b$，以 $q=(r,b,k)$ 为未知量，以四个原数据为参数，令 $F=(F_1,F_2,F_3)$ 为式 (35.5)。在每个中心点 $q_s^\pm=(r_s^\pm,b_s,0)$，有 $a=e=\omega=k=0$。对 $q$ 的导数矩阵为上三角，其对角元依次为

$$
\frac{4s(1-2r_s^\pm)}{b_s},\qquad 2s,\qquad C(q_s^\pm).
$$

因此

$$
\det D_qF(q_s^\pm,\lambda_s)
 =\frac{8s^2(1-2r_s^\pm)C(q_s^\pm)}{b_s}.
\tag{38.1}
$$

$K_6(s)>0$ 给 $1-2r_s^\pm\ne0$。若中心的 $C=0$，中心的 $F_1=F_2=0$ 和式 (36.9) 给 $As=G$，引理 36.1 又给 $s<54$，矛盾。故两个中心的 $C$ 均非零，两个矩阵都可逆。

为明确局部存在与唯一性的范围，固定一个中心 $q_0$，令 $J_0=D_qF(q_0,\lambda_s)$。取围绕 $q_0$ 的足够小闭球，完全位于严格合法源图内；由连续性再缩小数据邻域，使整个闭球上

$$
\|I-J_0^{-1}D_qF(q,\lambda)\|\le\frac12,
\qquad
\|J_0^{-1}F(q_0,\lambda)\|\le\frac{\rho}{2},
\tag{38.2}
$$

其中 $\rho$ 为球半径。映射 $q\mapsto q-J_0^{-1}F(q,\lambda)$ 是球内自映射收缩，故每个邻近数据恰有一个球内零点。收缩估计也使该零点随数据连续，中心处回到 $q_0$。对两个中心分别取互不相交的小球，并取共同数据邻域。重建式 (35.4) 在两球内给合法的完整世界；源严格正，且靠近 $g_s(0)=-s\ne0$，整个增益也非零。

这时只得到两个局部世界，还须排除球外世界。若对任意更小数据邻域仍有额外世界，取这些数据趋于 $\lambda_s$，并各选一个额外世界。定理 37.1 给它们的某个子列趋于两个中心之一；相应的 $q=(r,b,z-d)$ 因而终将进入该中心球，与球内零点唯一性矛盾。因此再缩小数据邻域后，整个 $\Omega$ 恰由这两个局部世界组成。

令 $\Delta r=r_s^+-r_s^->0$。在中心，式 (28.1) 给两个末动作的实际响应差

$$
f_J(W_s^+)-f_J(W_s^-)=\frac{16s}{45}\Delta r>0,
\qquad
f_M(W_s^+)-f_M(W_s^-)=\frac{8s}{45}\Delta r>0.
\tag{38.3}
$$

原末迹分别是 $2n+t+2r$ 与 $2n+3u$，故末响应随世界和数据连续。再缩小邻域，使两支的两个差都保持非零。每个整个纤维恰有这两个不同源的完整目标，所以两末映射都单射。

两个世界共享原时钟 $0,\ldots,6$ 的所有指定实际响应，沿该历史的每个前缀均有至少两个完整目标。时钟七的每个实际响应叶却至多一个完整目标，故 $L_1$ 的分句失败；原基数及提前停止语义没有改变。允许两末动作选不同终端对也不能产生任何 $L_0$ 叶。整个构造用式 (35.7) 的四维可逆坐标，没有将数据限制在一条曲线或一个曲面上。∎

**推论 38.2（有理种子及离开三根型的消费者）。** 对式 (29.1) 的有理种子，存在有理数 $\eta>0$，使

$$
\max\left\{
\left|z-\frac{1728}{25}\right|,
\left|Y-\frac{9328}{125}\right|,
\left|p-\frac{1728}{25}\right|,
\left|h-\frac{1728}{25}\right|
\right\}<\eta
\tag{38.4}
$$

时，整个 $\Omega(z,Y,p,h)$ 恰有两个世界，最终 $J,M$ 各自单射。特别地，固定 $z=p=z_0,Y=Y_0$，若 $0<|h-z_0|<\eta$，这两个世界均满足

$$
(z_0-d)(h-z_0)>0,\qquad
 g(3)g(5)g(6)\ne0.
\tag{38.5}
$$

证明。种子两源满足

$$
\left.\frac{\partial j}{\partial r}\right|_{r=17/48}=\frac7{31},
\quad
\left.\frac{\partial j}{\partial r}\right|_{r=31/48}=-\frac7{31},
\quad
\tau=\frac{12}{43},\quad
 x_- =\frac{175}{344},\quad x_+=\frac{203}{344}.
$$

两 $x$ 都小于 $2/3$，故 $N(x)<0$；由式 (36.4) 和 $D>0$ 得两个中心的 $C>0$。连续性允许在定理 38.1 的邻域内保留两支的 $C>0$。中心两个末差是式 (29.3) 的 $896/125$、$448/125$，均严格正。

固定种子父与 $p=z_0$ 时，$a=\omega=0$，第三扰动式准确化为

$$
Ck=\frac{5(2u-t)}v e.
\tag{38.6}
$$

这里 $2u-t=1+3b>0$。当 $e\ne0$，$C>0$ 给 $ke>0$，于是 $k\ne0$，$k+e\ne0$。式 (35.4) 的原样本 $g(3)=k/n,g(5)=k/(n+u),g(6)=(k+e)/v$ 全部非零。这正是式 (38.5)，所以附近世界确实可离开中心的三根型，而结论仍适用于整个纤维。最后在所得四维开邻域中取开盒，并在其正半径以下选一个正有理数，得到 $\eta$。这里仅断言半径存在，不指定其数值。∎

## 39. 整个支持的共同父必要条件与原根边界

**推论 39.1（三个全类限制的同时消费者）。** 若在一个字面相同的

$$
H_4=(0,J,24,M,48,J,z,M,Y)
$$

上，某个第五 $M$ 实际响应 $p_M$ 的支持实现 $L_2$，则其整个增益集合至少有两个实方向，八槽形式满足式 (31.12) 的秩至少二。它用于第六 $M$ 分句的实际响应 $h_M$ 还必须满足以下条件：在 $(z,Y,p_M)=(z_0,Y_0,z_0)$ 时有 $h_M<0$；对每个定义 35.1 的严格非临界中心，有

$$
(z,Y,p_M,h_M)\notin V_s.
\tag{39.1}
$$

证明。第一项是定理 31.2、推论 31.3；种子处第二项是推论 34.2；最后一项由定理 38.1，因为 $L_2$ 的第六 $M$ 分句需要实际 $L_1$ 子纤维，而 $V_s$ 内整个纤维及其任意子集均无 $L_1$。这些条件约束同一原世界类中的整个所选支持，未要求每个终端对都不成比例，也未将不同动作的终端对合并。∎

**命题 39.2（范围与保留的共同实现问题）。** 推论 39.1 既不供应也不排除不受这些限制覆盖的共同父两支 $L_2$ 实现。第五 $J$ 和第五 $M$ 仍可各选自己的实际第五响应；每个第六动作仍可各选自己的实际响应，两个最终动作仍可使用不同终端对。任何同父并合都须实现定义 9.2 以及 §§13、18 的全部同时方程和不同完整目标护栏。

定理 34.1 只对式 (32.1) 的精确种子和 $h\ge0$ 给整个纤维的最终 $J$ 单射；$h<0$ 上的完整 $L_1$ 问题仍未判定。定理 38.1 只在每个 $720/13<s<72,K_6(s)>0$ 中心的某个存在性四维邻域内成立；不包括 $K_6(s)=0$ 的临界中心，也不提供数值半径。邻域之外的父、第五响应和第六响应，以及其他完整混合增益支持的共同实现问题均保留。

证明。三个限制分别使用单方向包含、精确种子半线以及严格非临界中心附近的数据条件，没有一个条件涵盖全部混合增益及全部父数据。共同父的相反第五动作和原根祖先分句并未由任一限制构造出来。两个第五臂即使在同一个父上实现，也只供该父的局部 $L_3$；更早的相反动作、实际响应、提前停止和原根到达仍须分别满足。因而原域至多八次总读、时钟 $0,\ldots,7$ 的确定性完整目标恢复，与 $n_{\rm det}(3,0)\ge9$ 的二择仍为未决；九读上界也未从这些限制推出。所有先前带条件的消费者继续保留其全部原前提。∎

**数学来源。** 有符号提升及其原限定范围见《[FIB 实际 JMJM 的承诺纤维与联合例外几何](FIB_JMJM_PROMISED_FIBERS_AND_JOINT_EXCEPTION_GEOMETRY.md)》定理 4.1；根 $1,6,7$ 的支持计算见《[FIB 采样根坍缩与同父失败核心](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md)》引理 4.1。中心世界、中心末差和六十九个符号系数分别由本卷 §§26–29 供应。四节点插值、张量 Bernstein 恒等式、中点 de Casteljau 恒等式、首一二次根序及收缩原理在以上证明中均按其显示条件使用。增益方向提升所涉及的双线性可识别问题可参见 Li–Lee–Bresler，*A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*，§1.3、定理 2.8，[arXiv:1501.06120](https://arxiv.org/abs/1501.06120)；该文的变换群商目标不替代本卷迹一源、漂移和整个增益组成的完整目标。

## 追加锚（本行以下为增补区）

## 40. 第五 M 后第六 J 的整个比例增益对分离

**定义 40.1（任意父数据的第六 J 方向类）。** 沿用定义 1.1 的严格合法完整世界及定义 9.1 的失败递归。对任意实数 $z,Y,p,v$，置

$$
H_{6MJ}=(0,J,24,M,48,J,z,M,Y,M,p,J,v),
\qquad
\mathcal C_h(z,Y,p,v)=\mathcal K_h(z,Y,p)\cap\mathcal F(H_{6MJ}),
\tag{40.1}
$$

其中 $0\ne h\in\mathbb R[X],\deg h\le3$，$\mathcal K_h$ 如式 (31.1)。不采用式 (1.3) 的窗口。整个增益 $g=\lambda h$ 的尺度 $\lambda\ne0$ 可正可负；每个世界各有自己的源和漂移。所有采样零、降次、重复增益根及严格合法的对称源均保留。

**引理 40.2（第六 J 后两个末动作同时相等的对刚性）。** 两个合法完整世界若整个增益成比例，实现同一 $H_{6MJ}$，并且在原时钟七的最终 $J$、最终 $M$ 下分别给相同响应，则两个完整世界相同。

证明。原时钟 $1,\ldots,5$ 的矩阵是式 (31.6) 前的五个左乘矩阵；特别地

$$
Q=A_5=\begin{pmatrix}2&1\\3&1\end{pmatrix},\quad
A_{6J}=JQ=\begin{pmatrix}3&1\\2&1\end{pmatrix},\quad
A_{7JJ}=Q,\quad A_{7JM}=\begin{pmatrix}2&1\\5&2\end{pmatrix}.
\tag{40.2}
$$

固定共同方向 $h$，对两个世界用式 (31.3)–(31.5) 的精确提升 $R_i=\lambda_iP_i$。置 $V=R_2-R_1$、$\sigma=\operatorname{tr}V$。每个相同响应恰给

$$
h(i)\operatorname{tr}(A_iV)=h(0)\sigma,
\tag{40.3}
$$

包括式 (40.2) 的第六行和两个最终行。此式没有除以采样值。

先处理 $\sigma=0$。此时尺度、整个增益 $g$ 和漂移 $d$ 都相同。写源差为 $(\delta r,\delta b,\delta c)$。

若 $g(2)=g(4)=0$，则 $d=48$，而第一读迫使 $g(1)\ne0$，故 $\delta c=-\delta b$。$g$ 已在 $2,4$ 有两个不同根，所以 $g(3),g(5),g(6)$ 中至少两个非零。对应的迹差依次是

$$
\delta r,\qquad \delta r+2\delta b,\qquad 2\delta r+\delta b.
\tag{40.4}
$$

这三个关于 $(\delta r,\delta b)$ 的系数行任意两行独立，所以源差为零。

否则，第二、第四读至少一个非零增益样本给 $\delta b=0$。若 $g(1)\ne0$，又有 $\delta c=0$；$\delta r\ne0$ 会由第三、第五、第六 $J$ 及最终 $J$ 的相同响应强迫 $g(3)=g(5)=g(6)=g(7)=0$，违背非零多项式次数至多三。

余下 $g(1)=0$，于是 $d=24$、$g(2)\ne0$。若 $g(3)=g(5)=0$，三个根 $1,3,5$ 强迫 $g(6)g(7)\ne0$；第六 $J$ 和最终 $M$ 的迹差分别给 $2\delta r+\delta c=0$、$\delta c=0$。否则，第三、第五读中至少一个给 $\delta r+\delta c=0$。若源仍不同，则 $\delta r\ne0$，第六 $J$ 和最终 $M$ 的相同响应分别迫使 $g(6)=g(7)=0$。初读 $g(0)=-24$ 遂固定

$$
g(X)=\frac47(X-1)(X-6)(X-7),\quad
g(2)=\frac{80}7,\quad g(3)=\frac{96}7,\quad b=\frac{11}{10}.
\tag{40.5}
$$

第三读固定 $n=r+b+c$。秩一式要求两个源的 $r$ 都是

$$
r^2-(1+b)r+b(n-b)=0
\tag{40.6}
$$

的根。两个不同根若都在 $(0,1)$，根和小于 $2$；此处根和却是 $21/10$。所以源仍唯一。这也包括附加根在其他节点的情形；每次使用的只是不同根数上界。

再处理 $\sigma\ne0$ 且 $h(0)=0$。两漂移均为零，读数 $24,48$ 迫使 $h(1)h(2)\ne0$。写

$$
V=\begin{pmatrix}A&B\\C&\sigma-A\end{pmatrix}.
$$

第一、第二读的差给 $C=-B$、$\sigma=-B$，所以 $B\ne0$。第四迹差是 $\sigma+2B=B$，故 $h(4)=0$。第三、第五迹差是 $A$、$A+B$，不能同时为零，因此 $h(3),h(5)$ 至少一个为零；它们不能都为零，否则加上 $0,4$ 已有四个不同根。

若 $h(3)=0$，则 $h(5),h(6)\ne0$，第五行给 $A=-B$，第六 $J$ 迹差为 $2A\ne0$，矛盾。若 $h(5)=0$，则 $h(3),h(7)\ne0$，第三行给 $A=0$，最终 $J$ 迹差 $A+B=B\ne0$，仍矛盾。

最后处理 $\sigma h(0)\ne0$。置

$$
D=V/\sigma=\begin{pmatrix}a&b\\c&1-a\end{pmatrix},
\qquad w=h/h(0).
$$

这里 $D$ 只是差矩阵的归一化，不要求它是正源。式 (40.3) 成为 $w(i)\operatorname{tr}(A_iD)=1$，故所用的全部样本及迹都非零。两个最终等式相减给 $1-a+2b=0$。置

$$
u=1+2b=a,\qquad x=\frac{b+c}{u},\qquad T=x(x+1)(x+2).
\tag{40.7}
$$

时钟 $1,3,5,7JJ$ 的迹依次为 $ux,u(x+1),u(x+2),u(x+2)$；时钟 $2,4$ 的迹是 $(u+1)/2,u$。所以 $u,x,x+1,x+2,u+1$ 均非零，$x$ 不受正性限制。

在四节点 $1,3,5,7$ 插值 $w$。节点 $0,2,4$ 的权重乘 $16$ 后分别为

$$
\begin{array}{c|rrrr}
0&35&-35&21&-5\\
2&5&15&-5&1\\
4&-1&9&9&-1
\end{array}.
\tag{40.8}
$$

这些权重由 $\prod_{j\ne i}(X-j)/(i-j)$ 在三个节点的值直接得到，故适用于所有次数至多三的 $w$。置

$$
A=16x^2+51x+70,\qquad B=16x^2+41x+10.
$$

时钟零、二、四分别给

$$
16uT=A,\qquad B(u+1)=32uT,\qquad
16T=16x^2+23x-2.
\tag{40.9}
$$

例如第三式来自 $-1/x+9/(x+1)+8/(x+2)=16$。因此

$$
\begin{aligned}
f&=16x^3+32x^2+9x+2=0,\\
G&=A(B-32T)+16BT\\
 &=-256x^5-1488x^4-4048x^3-4821x^2-780x+700=0.
\end{aligned}
\tag{40.10}
$$

这两个多项式在整个实轴上没有共同根。其精确互素证书是，置 $q=42x^2-55x-118$，有恒等式

$$
\begin{aligned}
G+(16x^2+61x+122)f&=-8q,\\
441f-(168x+556)q&=54373x+66490,\\
54373^2q(-66490/54373)&=35660057328>0.
\end{aligned}
\tag{40.11}
$$

前两式逐幂展开即得；最后一式的整数分子明确是
$42\cdot66490^2+55\cdot66490\cdot54373-118\cdot54373^2$。
共同根会先满足 $q=0$，再满足 $x=-66490/54373$，与第三式矛盾。此支未加尺度符号、源正性或增益根型条件。所有支穷尽，故 $V=0$，由提升的逆对应得到完整世界相同。∎

## 41. 任意第六 J 支持的方向秩与第六 M 反例

**定理 41.1（整个第六 J 支持的单方向障碍）。** 对定义 40.1 的每个 $z,Y,p,v,h$ 及任意子集 $S\subseteq\mathcal C_h(z,Y,p,v)$，包括无限子集，

$$
\neg L_1(S,H_{6MJ}).
\tag{41.1}
$$

证明。式 (31.6) 的五行秩分类已包括所有采样零：非空方向类的前两行独立；除 $h$ 为 $(X-1)(X-3)(X-5)$ 的倍数外，秩至少三。故非例外方向的全部第五 $M$ 提升位于一条仿射直线或一个点内。这一分类只用前五个实际读数，不要求第六动作是 $M$。

若 $S$ 有 $L_1$，它至少包含两个不同完整目标，它们的提升也不同。第六 $J$ 的实际响应是式 (31.5) 的仿射泛函；既在这两个点相同，就在包含方向类的整条直线上恒定。对最终 $J$，$L_1$ 提供某个实际响应叶中的不同目标对，所以该最终泛函也在同一条直线上恒定。最终 $M$ 可能使用另一对，仍迫使它的泛函在同一条直线上恒定。于是任取 $S$ 中两个不同世界，都同时满足引理 40.2，矛盾。这里没有预先令两个最终动作共用一对，也没有假设支持有限。

例外方向由式 (31.11) 精确重建：除 $(z,Y,p)=(24,-96/5,24)$ 外为空；非空时

$$
g(X)=\frac85(X-1)(X-3)(X-5),\quad d=24,\quad
P(r)=\begin{pmatrix}r&4\\r(1-r)/4&1-r\end{pmatrix},\quad0<r<1.
\tag{41.2}
$$

式 (31.11) 后列出的同一增益全部样本已检验其充分性。其第六 $J$ 响应是

$$
24+24\left(1+2r+8+\frac{r(1-r)}4\right)
=240+54r-6r^2,
\qquad \frac{d}{dr}=54-12r>42.
\tag{41.3}
$$

故每个实际第六 $J$ 纤维至多单点。例外类、点以及空类都由原基数护栏排除。∎

**推论 41.2（只约束整个选中支持的二秩）。** 若任意第五 $M$ 支持有 $L_2$，它为第六 $J$ 选出的实际 $L_1$ 支持中，整个增益的线性张成维数至少二；等价地，全部所选世界的四样本向量 $(g(0),g(1),g(2),g(3))$ 的张成维数至少二。

证明。四节点取值是三次及以下多项式空间的线性同构。一维张成会使整个所选支持包含在一个 $\mathcal C_h$ 中，违反定理 41.1。该论证不约束每一个终端对的秩，不给三秩下界，也不把结论搬到第六 $M$ 纤维。∎

**命题 41.3（第六 M 不满足同一方向排除）。** 取同一个整个增益和漂移

$$
g(X)=\frac4{35}(X-1)(X-7)(X-30),\qquad d=24,
\tag{41.4}
$$

以及两个源

$$
P_1=\begin{pmatrix}7/10&1/2\\21/50&3/10\end{pmatrix},\qquad
P_2=\begin{pmatrix}4/5&1/2\\8/25&1/5\end{pmatrix}.
\tag{41.5}
$$

这两个不同完整世界构成某个实际第六 $M$ 纤维的 $L_1$ 支持。

证明。两源逐项正、迹一，且 $bc$ 分别为 $21/100$、$4/25$，恰等于各自 $r(1-r)$。增益非零且三次。原时钟零至五的完整重放为

| $i$ | $\tau_i(P_1)$ | $\tau_i(P_2)$ | 同一个 $g(i)$ | 两世界的原响应 |
| --- | --- | --- | --- | --- |
| $0$ | $1$ | $1$ | $-24$ | $0$ |
| $1$ | $23/25$ | $41/50$ | $0$ | $24$ |
| $2$ | $3/2$ | $3/2$ | $16$ | $48$ |
| $3$ | $81/50$ | $81/50$ | $864/35$ | $55992/875$ |
| $4$ | $2$ | $2$ | $936/35$ | $2712/35$ |
| $5$ | $181/50$ | $181/50$ | $160/7$ | $3736/35$ |

这里的迹使用命题 1.2 的原左乘矩阵。第六 $M$ 的迹在两世界中均为 $281/50$，而 $g(6)=96/7$，所以共同响应为

$$
24+\frac{96}7\frac{281}{50}=\frac{17688}{175}.
$$

在此第六 $M$ 历史上，最终 $J$ 的两迹为 $307/50,317/50$，最终 $M$ 的两迹均为 $231/25$。同一个增益有 $g(7)=0$，两个最终动作在两世界上都给 $24$。因此每个最终动作都有这对不同完整目标构成的实际 $L_0$ 叶，确有 $L_1$。

若第六动作改为 $J$，原矩阵是式 (40.2)，两迹为 $191/50,98/25$，故实际响应分别为 $13368/175,13608/175$，严格不同；其后任一最终动作仍因 $g(7)=0$ 给 $24$。所以两世界不在同一实际第六 $J$ 纤维。这是定理 41.1 的精确动作边界，不供应同父两个第五臂的共同实现。∎

## 42. 两个临界中心及四个独立数据的原世界对应

**定义 42.1（临界中心）。** 对 $\varepsilon\in\{-1,1\}$，置

$$
\begin{aligned}
s_\varepsilon&=\frac{14076+36\varepsilon\sqrt{1241}}{223},\\
b_\varepsilon&=\frac{51+\varepsilon\sqrt{1241}}{68},\qquad
c_\varepsilon=\frac{51-\varepsilon\sqrt{1241}}{80},\\
\lambda_s&=(s,59s/45-16,s,s),\qquad
W_s=\left(\begin{pmatrix}1/2&b_s\\c_s&1/2\end{pmatrix},
 \frac{s}{90}(X-3)(X-5)(X-6),s\right).
\end{aligned}
\tag{42.1}
$$

以下每次固定其中一个 $s$。$\Omega(z,Y,p,h)$ 仍指式 (35.1) 的整个原世界纤维，但不采用该定义中对非临界参数 $s$ 的限制。

**命题 42.2（中心合法性与不受根型限制的重建）。** 两个中心均严格合法，且

$$
K_6(s)=0,\quad \frac{720}{13}<s<72,\quad
34b_s^2-51b_s+10=0,\quad b_sc_s=\frac14.
\tag{42.2}
$$

$\Omega(\lambda_s)=\{W_s\}$。对四个独立数据 $\lambda=(z,Y,p,h)$，式 (35.3)–(35.6) 与严格源护栏给整个 $\Omega(\lambda)$ 的充分必要重建。

证明。$K_6$ 的判别式是 $72^2\cdot1241$。$35<\sqrt{1241}<36$ 以及 $K_6$ 在 $57,58$、$68,69$ 的符号变化将两根分别隔离于 $(57,58)$、$(68,69)$，均在 $(720/13,72)$。式 (42.1) 直接给 $b_s,c_s>0$、$b_sc_s=(2601-1241)/5440=1/4$，以及式 (27.1) 中的相同 $b_s,c_s$。定理 27.1 本来就包含 $K_6=0$，故给中心纤维恰为这个重源根世界。

其同一增益在原节点 $0,\ldots,7$ 的值依次为

$$
(-s,-4s/9,-2s/15,0,s/45,0,0,4s/45).
\tag{42.3}
$$

原时钟 $0,\ldots,6$ 的迹是 $1,j,t,n,u,n+u,n+2u$。由式 (27.5)，$j=9(s-24)/(4s)$、$t=15(s-48)/(2s)$、$u=14-720/s$。逐项代入 $s+g(i)\tau_i$ 就得 $0,24,48,s,59s/45-16,s,s$，完整重放了原中心历史。

对任意邻近或非邻近的数据，仍写

$$
c=\frac{r(1-r)}b,\quad j=b+c,\quad t=1+b,\quad
u=1+2b,\quad n=r+j,\quad v=n+2u,
$$

并使用式 (35.3) 的 $k=z-d,a=p-z,e=h-z,\omega=Y-59z/45+16$。四节点 $0,3,5,6$ 唯一决定同一个整个增益式 (35.4)，$d=z-k$。命题 35.2 的证明给原节点残差恒等式 $F_1=-9\rho_1,F_2=-15\rho_2,F_3=45\rho_4-F_2$，其中 $F_i$ 正是式 (35.5)。所以 $F_1=F_2=F_3=0$ 与全部七个指定原响应双向等价；只有正迹分母，未除以 $k$、增益样本、最高次项或源判别式。第一读与初读不同排除了零增益。式 (35.7) 可逆，故 $z,Y,p,h$ 四个实际数据相互独立，不要求维持中心的三个增益根或任何数据间关系。∎

## 43. 临界中心的闭边界控制与整个原世界无逃逸

**引理 43.1（临界参数下的闭源供应）。** 引理 36.1 的闭源排除和式 (36.9) 的未除法消元均适用于本节两个临界中心：在有限闭源 $b,c\ge0,0\le r\le1,bc=r(1-r),j,n>0$ 上，$C=0$ 与 $Az=G$ 强迫 $z<54$。

证明。所用多项式恰为式 (25.1)、(25.5)–(25.6)，全部六十九个系数恰为引理 26.1 的六组表及式 (26.2)–(26.5)。这些多项式和闭区间符号 (26.1) 均不含 $K_6$。为明确闭边界和重根的作用，$C=0$ 时式 (36.4) 给 $\tau D=N$，其中 $x=n/u>0,\tau=1/u\in(0,1]$，于是 $0<N\le D$。式 (25.4) 的递增性及 $N$ 的凸性给 $2/3<x<6/7$。闭源的实际 $r$ 是式 (36.5) 首一二次式 $q$ 的实根；$\Pi<0$ 的闭区间符号进一步给 $x>3/4$。

其余五组符号给 $A_1,U,W,P_0,P_1>0$。式 (36.7) 使 $w=-A_0/A_1$ 严格在 $q$ 的顶点左侧且 $q(w)>0$，故严格小于它的较小实根；重复源根时同样成立。于是每一个源根都有 $A=A_1(r-w)>0$。式 (36.8) 在 $0\le r\le1$ 上仍严格正，包括两个端点。因此 $Az=G$ 强迫 $z<54$。这个论证同时保留 $b=0,c=0$ 的闭源层，只在极限中使用它们。

式 (36.9) 则是先消去 $k$ 的恒等式，不需要 $k\ne0$，不除以 $B,9-jL,A$ 或源判别式。因此可以在可能无界的 $k$ 消去后取闭源极限。以上没有使用 $K_6>0$，也没有使用定理 38.1 的两个非临界局部世界结论。∎

**定理 43.2（所有相容序列均趋于唯一临界世界）。** 若 $\lambda_m\to\lambda_s$ 且任取 $W_m\in\Omega(\lambda_m)$，则整个世界 $W_m\to W_s$，其中增益按其四个系数收敛。特别地，对 $W_s$ 的任意开邻域，充分接近 $\lambda_s$ 的数据的全部相容世界都在该邻域内。

证明。这里重用 §37 的精确代数，重新处理合并的源根。式 (35.3) 给 $a_m,e_m,\omega_m\to0$。若 $k_m\not\to0$，有子列 $|k_m|\ge\eta>0$；三个商 $a_m/k_m,e_m/k_m,\omega_m/k_m$ 都趋零，不预设 $k_m$ 有界。

在该子列令 $x=n/u,\tau=1/u$。第三方程给式 (37.2)，即

$$
\begin{aligned}
f(x,\tau)&=e/k-\mathcal R(x,\tau)a/k+\mathcal S(x,\tau)\omega/k,\\
f(x,\tau)&=\frac{\tau D-N}{5(3-\tau)x(x+1)},\quad
\mathcal R=\frac{12(5-\tau)(x+2)}{5(3-\tau)(x+1)},\quad
\mathcal S=\frac{18(x+2)}{3-\tau}.
\end{aligned}
\tag{43.1}
$$

在 $x>0,0\le\tau\le1$ 上，$0<\mathcal R\le48/5$、$0<\mathcal S/(x+1)\le18$，如式 (37.3)。当 $x\to0$，左端一致趋于正无穷，右端趋零；当 $x\to\infty$，将等式除以 $x$，左端与 $-118/[5(3-\tau)]$ 之差一致趋零，右端仍趋零。故 $x$ 有正下界和有限上界。

若 $\tau\to0$，则 $b\to\infty$，$bc\le1/4$ 给 $c/u\to0$，从而 $x\to1/2$；但 $f(1/2,0)=6$，矛盾。因此 $\tau$ 也有正下界。可抽取有限非负源极限，保留 $n>0$。若 $j\to0$，闭秩一式和 $n>0$ 强迫 $r\to1$，所以 $(x,\tau)\to(1,1)$；此时 $f(1,1)=-26/5$，仍矛盾。于是极限 $j,n$ 均正，式 (43.1) 给极限 $C=0$。

对含 $k_m$ 的方程不能分别先取极限。置 $\gamma=9-jL$，每个 $m$ 上先作式 (37.5) 的精确组合

$$
\begin{aligned}
0=BF_1-\gamma F_2={}&B((4j-9)z+216)-\gamma((u-14)z+720)\\
&+\frac{9Bj-12\gamma t}{n+u}a
 +\frac{-4Bj+5\gamma t}{v}e.
\end{aligned}
\tag{43.2}
$$

$k$ 已严格抵消，其余系数在所得紧源子列上有界。现在取极限，以 $C=0$ 及式 (36.9) 得 $As=G$。引理 43.1 给 $s<54$，而两个中心均有 $s>720/13>54$，矛盾。因此 $k_m\to0,d_m\to s$，包括排除了所有无界漂移子列。

原节点 $0,2,4,5$ 的值仍为式 (37.6)。因 $t,u,n+u\ge1$，四值有界，固定四节点插值遂使整个增益系数有界。若某子列 $b\to\infty$，这些四值趋于 $-s,0,0,0$，增益唯一趋于

$$
\frac{s}{40}(X-2)(X-4)(X-5),\qquad g_\infty(1)=-3s/10\ne0.
$$

但 $j\ge b\to\infty$，第一读要求 $g(1)=(24-d)/j\to0$，矛盾。若某子列 $c\to\infty$，则 $b\to0$，$j,n,n+u\to\infty$，故 $g(1),g(3),g(5)\to0$、$g(0)\to-s$，增益唯一趋于

$$
\frac{s}{15}(X-1)(X-3)(X-5),\qquad g_\infty(2)=s/5.
$$

第二读和 $t\to1$ 却给 $g(2)\to48-s$，迫使 $s=40$，矛盾。秩一式也禁止 $b,c$ 同时趋无穷。因此两源坐标均有界，没有遗漏无穷远源分支。

又因 $g(1)$ 有界且 $s\ne24$，第一读使 $j$ 保持正下界，$n\ge j$ 同样如此。式 (35.4) 于是给 $g(3),g(5),g(6)\to0$、$g(0)\to-s$，强制整个增益趋于式 (42.3) 的 $g_s$。第一、第二读及其非零极限增益固定

$$
j\to\frac{9(s-24)}{4s},\quad t\to\frac{15(s-48)}{2s},
\qquad b\to b_s>0,\quad c\to c_s>0.
$$

最终 $r(1-r)\to b_sc_s=1/4$，即 $(r-1/2)^2\to0$，所以 $r\to1/2$。这排除了所有 $r=0,1,b=0,c=0$ 的最终边界，且每个收敛子列的极限都是同一个严格合法世界 $W_s$。有界性及唯一极限给整个序列收敛。

若开邻域结论失败，可取趋于 $\lambda_s$ 的数据及其在该世界邻域外的相容世界，违背刚证的收敛。§37 的无逃逸代数至此只需 $s>54,s\ne24,40$ 及中心 $b_s,c_s>0$；旧结论中的 $K_6>0$ 只在最后把源二次根选为两个不同根、以及 §38 的全三变量可逆矩阵中使用。这里改用重根极限 $r=1/2$，并未把非临界定理应用到临界点。∎

## 44. 临界中心的真实约化曲率与整个纤维零一二分类

**定理 44.1（四数据临界分类）。** 对每个定义 42.1 的 $s$，存在包含 $\lambda_s$ 的开邻域 $V_s\subset\mathbb R^4$、包含 $1/2$ 的闭区间 $I\subset(0,1)$，以及光滑函数 $\beta(r,\lambda),\kappa(r,\lambda)$ 和 $\Psi_s(\lambda)$，使全部相容世界唯一由

$$
b=\beta(r,\lambda),\quad k=\kappa(r,\lambda),\quad
\phi(r,\lambda)=F_1(r,\beta(r,\lambda),\kappa(r,\lambda);\lambda)=0,
\quad r\in\operatorname{int}I
\tag{44.1}
$$

重建。全积 $I\times V_s$ 上 $\phi_{rr}<0$，两端的 $\phi$ 为负，每个数据有唯一内点最大值 $\Psi_s(\lambda)$，且

$$
|\Omega(\lambda)|=
\begin{cases}
0,&\Psi_s(\lambda)<0,\\
1,&\Psi_s(\lambda)=0,\\
2,&\Psi_s(\lambda)>0.
\end{cases}
\tag{44.2}
$$

证明。先证 $C_s\ne0$，以确定可以解的子系统。在中心 $r=1/2,c=1/(4b)$ 上

$$
x=\frac nu=\frac12+\frac1{4b(1+2b)}.
\tag{44.3}
$$

由 $35<\sqrt{1241}<36$，低中心 $0<b_-<1/4$，所以 $x>7/6$；高中心 $b_+>1$，所以 $x<7/12$。而 $C=0$ 必须有 $2/3<x<6/7$，见引理 43.1。两者均不可能，所以 $C_s\ne0$。

在中心 $q_s=(1/2,b_s,0)$，$a=e=\omega=k=0$。式 (35.5) 给

$$
D_{(b,k)}(F_2,F_3)=
\begin{pmatrix}2s&B_s\\0&C_s\end{pmatrix},\qquad
\det=2sC_s\ne0.
\tag{44.4}
$$

标准参数隐函数定理给唯一光滑 $b=\beta(r,\lambda),k=\kappa(r,\lambda)$，解出 $F_2=F_3=0$。在中心数据，对所有充分接近 $1/2$ 的 $r$，$b=b_s,k=0$ 已是此子系统的解；局部唯一性故给恒等式 $\beta(r,\lambda_s)=b_s,\kappa(r,\lambda_s)=0$。代入 $F_1$，利用 $c=r(1-r)/b_s$，得到精确式

$$
\phi(r,\lambda_s)=-\frac{4s}{b_s}(r-1/2)^2,
\qquad \phi_r(1/2,\lambda_s)=0,\qquad
\phi_{rr}(1/2,\lambda_s)=-\frac{8s}{b_s}<0.
\tag{44.5}
$$

这是约化图上的导数，包含源约束和子系统的总变化；中心有 $\beta_r=\kappa_r=\beta_{rr}=\kappa_{rr}=0$、$c_r=0,c_{rr}=-2/b_s$。保持 $c$ 不变求偏导不会得到这个曲率。

取关于 $1/2$ 对称的充分小闭区间 $I$，完全在上述子系统图内。在中心数据，$\phi$ 两端严格负，$\phi_r$ 左正右负，全区间 $\phi_{rr}<0$。连续性和紧性使这些严格不等式在缩小后的 $I\times V_s$ 上一致保持，且整个图中 $0<r<1,b,c>0$、$g(0)=k-z\ne0$。定理 43.2 允许再缩小 $V_s$，使每个相容世界的 $(r,b,k)$ 都落在子系统的唯一性邻域且 $r\in\operatorname{int}I$。所以此图没有遗漏任何额外世界；反过来，每个 $\phi$ 的根都由命题 42.2 重建为合法完整世界。

$\phi_r$ 在 $I$ 严格递减且端点异号，故有唯一内点零点 $\rho(\lambda)$。因 $\phi_{rr}\ne0$，隐函数定理使 $\rho$ 光滑。定义

$$
\Psi_s(\lambda)=\phi(\rho(\lambda),\lambda).
\tag{44.6}
$$

$\phi$ 在最大点左侧严格递增、右侧严格递减。若最大值负，无根；等于零，唯一根是最大点；大于零，两边各由介值定理得一个根且严格单调保证唯一。两个不同 $r$ 给不同源及不同完整目标。所有根都在端点内部，整个纤维均已覆盖，故得式 (44.2)。∎

## 45. 原坐标横截、精确最大值与两个末响应的分离

**命题 45.1（原四数据的归一化横截）。** $\Psi_s$ 采用式 (44.6) 的特定归一化，即约化残差 $F_1=-9\rho_1$ 的最大值。在原坐标 $(z,Y,p,h)$ 中，它在中心的梯度四个分量均非零。具体地，令 $b=b_s$、$D_*=5225026158896720$，则

| 原数据坐标 | $D_*\partial\Psi_s$ 在中心的值 | 低中心严格界 | 高中心严格界 |
| --- | --- | --- | --- |
| $z$ | $-519436669101425160+344453243031130140b$ | $(-85,-83)$ | $(-17,-15)$ |
| $Y$ | $-258723603809033904+352664221795743051b$ | $(-34,-33)$ | $(35,37)$ |
| $p$ | $313418063653134120-331808193006143460b$ | $(44,46)$ | $(-22,-20)$ |
| $h$ | $-80541260811241290+78355490776012935b$ | $(-12,-11)$ | $(3,4)$ |

最后两列是各偏导本身的界，未乘 $D_*$。因此 $\Psi_s=0$ 在中心附近是光滑分界超曲面，可对任一原数据解为其他三个数据的光滑函数；四个坐标方向分别横截它。

证明。所有下标 $s$ 的源量取中心值。置

$$
J_b=1-c_s/b_s,\quad \gamma=9-j_sL_s,\quad H=\gamma-2J_bB_s.
$$

先在独立坐标 $(z,a,e,\omega)$ 中记最大值的四个偏导为 $P_z,P_a,P_e,P_\omega$。因中心 $\phi_r=0$，最大点的导数不贡献最大值的一阶导数。对式 (44.4) 的子系统作隐式微分，再代入 $F_1$，得到

$$
\begin{aligned}
P_z&=4j_s-9-2J_b(u_s-14),\\
P_a&=\frac{9j_s-24J_bt_s}{n_s+u_s}
 -\frac{12H(3u_s-t_s)}{(n_s+u_s)C_s},\\
P_e&=\frac{-4j_s+10J_bt_s}{v_s}
 -\frac{5H(t_s-2u_s)}{v_sC_s},\\
P_\omega&=45H/C_s.
\end{aligned}
\tag{45.1}
$$

例如对任一参数 $\xi$，$k_\xi=-(F_3)_\xi/C_s$、$b_\xi=-((F_2)_\xi+B_sk_\xi)/(2s)$，而 $F_{1b}=4sJ_b,F_{1k}=\gamma$，直接给上式。式 (35.3) 的链式法则给原坐标梯度

$$
\left(P_z-P_a-P_e-\frac{59}{45}P_\omega,\ P_\omega,\ P_a,\ P_e\right).
\tag{45.2}
$$

表内整数等式可在同一个二次域逐项化简：使用

$$
b^2=\frac32b-\frac5{17},\quad c=\frac1{4b},\quad
s=\frac{720}{13-2b},\quad n=\frac12+b+\frac1{4b},
\qquad
C_s=\frac{-26860368461933+33309351623606b}{985506201827}.
\tag{45.3}
$$

将这些式及 $t=1+b,u=1+2b,v=n+2u$ 代入式 (35.6)、(45.1)–(45.2)，通分后以 $34b^2-51b+10=0$ 约去二次及以上幂，余下的常数项和一次项正是表内分子；$C_s\ne0$ 已由式 (44.3) 独立证明。所有分母均已非零。

为给出精确符号而非近似判断，令 $Q(b)=34b^2-51b+10$。有

$$
Q(23/100)=343/5000>0,\quad Q(6/25)=-176/625<0,
\quad Q(63/50)=-176/625<0,\quad Q(32/25)=266/625>0.
$$

故两根分别在 $(23/100,6/25)$、$(63/50,32/25)$。表中每个分子关于 $b$ 仿射，将两个相应有理端点代入并除以正整数 $D_*$，就分别严格落在表内两个整数界之间。这证明全部四个分量的非零性。它们是同一个超曲面的四个横截坐标方向，不是四个独立法向量。∎

**命题 45.2（原 root6 数据线的精确最大值）。** 沿

$$
\lambda(z)=(z,59z/45-16,z,z),\qquad b_z=\frac{13z-720}{2z},
$$

当 $z$ 充分接近所选 $s$ 时，约化图恰有 $\beta=b_z,\kappa=0$，且

$$
\begin{aligned}
\phi(r,\lambda(z))&=\frac{K_6(z)}{2zb_z}-\frac{4z}{b_z}(r-1/2)^2,\\
\rho(\lambda(z))&=1/2,\qquad
\Psi_s(\lambda(z))=\frac{K_6(z)}{2zb_z},\\
D\Psi_s(\lambda_s)(1,59/45,1,1)
 &=\frac{446s-28152}{2sb_s}
 =\frac{\varepsilon72\sqrt{1241}}{2sb_s}\ne0.
\end{aligned}
\tag{45.4}
$$

证明。此线上 $a=e=\omega=0$，$b=b_z,k=0$ 直接解 $F_2=F_3=0$；子系统唯一性给图的同一解。写 $j_z=9(z-24)/(4z)$、$c_z=j_z-b_z$，则

$$
F_1=4z\left(b_z+\frac{r(1-r)}{b_z}-j_z\right)
=\frac z{b_z}(1-4b_zc_z)-\frac{4z}{b_z}(r-1/2)^2.
$$

式 (27.6) 给 $1-4b_zc_z=K_6(z)/(2z^2)$，得到精确最大值。求导时 $K_6(s)=0$，只剩式 (45.4) 的分子导数。两侧因此都出现相应的空纤维和两世界纤维；零界面本身给一世界。这个线上的一致性不限制其他三个独立数据的变化，也不将局部公式外推到邻域之外。∎

**定理 45.3（两个原末动作的总导数与半斜率分离）。** 可缩小定理 44.1 的 $I,V_s$，使对每个 $\lambda\in V_s$，最终 $J,M$ 响应各自在整个 $\Omega(\lambda)$ 上单射。若其中两个世界的源根为 $r_1<r_2$，则

$$
z_{7,J}(W_2)-z_{7,J}(W_1)\ge\frac{8s}{45}(r_2-r_1)>0,
\qquad
z_{7,M}(W_2)-z_{7,M}(W_1)\ge\frac{4s}{45}(r_2-r_1)>0.
\tag{45.5}
$$

证明。第六 $M$ 后的两个原左乘矩阵及迹恰为 §28 的

$$
A_{7,J}=\begin{pmatrix}5&2\\3&1\end{pmatrix},\quad
A_{7,M}=\begin{pmatrix}5&2\\8&3\end{pmatrix},\qquad
\tau_J=2n+t+2r,\quad\tau_M=2n+3u.
$$

式 (35.4) 的同一个整个增益在时钟七为

$$
G_7=-\frac4{45}(k-z)+\frac{7k}{9n}
       -\frac{14(k+a)}{5(n+u)}+\frac{28(k+e)}{9v}.
\tag{45.6}
$$

所以约化图上的两个实际最终响应是

$$
T_J=z-\kappa+G_7(2n+t+2r),\qquad
T_M=z-\kappa+G_7(2n+3u),\qquad b=\beta,\quad k=\kappa.
\tag{45.7}
$$

在中心数据，$\beta=b_s,\kappa=0$ 在整个局部 $r$ 区间恒定，$G_7=4s/45$ 也恒定；但 $c=r(1-r)/b_s$ 并不恒定。在 $r=1/2$，$c_r=0,c_{rr}=-2/b_s,n_r=1,n_{rr}=-2/b_s$，故真实约化导数为

$$
(T_J)_r=\frac{16s}{45},\quad (T_M)_r=\frac{8s}{45},\qquad
(T_J)_{rr}=(T_M)_{rr}=-\frac{16s}{45b_s}.
\tag{45.8}
$$

这里连同 $\beta,\kappa$ 和源约束一起求总导数，未把 $c$ 误作固定常数。连续性允许先缩小 $I$，再缩小 $V_s$，使全积上 $(T_J)_r>8s/45$、$(T_M)_r>4s/45$。沿同一数据下的区间 $[r_1,r_2]$ 积分得到式 (45.5)。整个纤维已由定理 44.1 覆盖，所以两映射的单射性包括所有原竞争世界；不是对预选的两支或共同增益类的结论。∎

## 46. 任意支持的局部停止条件与保留的共同实现问题

**推论 46.1（两个临界邻域的整个支持排除）。** 对每个 $\lambda\in V_{s_-}\cup V_{s_+}$ 及任意 $S\subseteq\Omega(\lambda)$，都有 $\neg L_1(S,H_{6M}(\lambda))$。因此任意第五 $M$ 的 $L_2$ 支持为第六 $M$ 选出的实际数据 $(z,Y,p,h)$ 必须避开这两个邻域。

证明。若 $\Psi_s\le0$，整个纤维至多一个完整目标，原基数护栏直接排除 $L_1$。若 $\Psi_s>0$，恰有两个不同世界共享原时钟 $0,\ldots,6$ 的全部实际读数，各前缀的两目标条件确实成立；但定理 45.3 使每个最终动作的每个实际响应叶至多单点，没有任何 $L_0$ 叶。任意子支持同样如此。不同最终动作允许选不同终端对仍无济于事，因为每个叶本身均无不同目标对。第五 $M$ 的 $L_2$ 必须有实际第六 $M$ 的 $L_1$ 子支持，遂得避开邻域的必要条件。∎

**命题 46.2（适用边界与未决义务）。** 定理 41.1 的二秩必要条件仅施加于第五 $M$ 后整个选中的第六 $J$ 的 $L_1$ 支持；命题 41.3 阻止把它扩大到第六 $M$。定理 44.1–45.3 只断言两个临界中心各有一个存在性的四维开邻域，不指定数值半径，不给邻域外的纤维结论，也不分类种子 $z=p=1728/25,Y=9328/125$ 下的全部负 $h$ 半线。

证明。前一边界由命题 41.3 的严格合法反例给出。后一结论依赖围绕各自中心保持的严格曲率、端点符号和两个末响应总导数，以及定理 43.2 的局部全类控制；这些条件只在所构造邻域内成立。§§40–45 没有为其他数据建立它们。原世界的源严格正、完整目标不同、每世界同一个整个三次及以下增益和任意实漂移、原 LEFT 动作及时钟 $0,\ldots,7$ 始终保留。原共同父两种第五动作的混合增益联合零点系统、定义 9.2 的全部同时叶与不同完整目标护栏、各祖先相反动作和提前停止分句仍须同时满足；这些必要限制既未供应也未排除该共同实现。故原根八读与九读下界的二择，以及九读上界，仍未由本增补判定。∎

## 追加锚（本行以下为增补区）

## 47. 同一个字面父的八槽联合方程

**定义 47.1（完整模型与同一整个增益）。** 本节至第 51 节不附加式 (1.3) 的旧父读数矩形；使用定义 9.1 的失败递归及定义 1.1 的严格完整世界 $W=(P,g,d)$：$P=\left(\begin{smallmatrix}r&b\\c&1-r\end{smallmatrix}\right)$，$0<r<1$，$b,c>0$，$bc=r(1-r)$；$g$ 是一个非零实多项式，次数至多三，$d\in\mathbb R$。令 $J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$，$A_0=I$、$A_k=E_kA_{k-1}$，原读数为 $y_k=d+g(k)\operatorname{tr}(A_kP)$。初读计入，动作后立即读，时钟为 $0,\ldots,7$。下述各分支均用原世界的同一个 $g,d$，无重置、克隆、空闲、跳时钟或新端口。

八个槽按 $M1,M2,M3,M4,J1,J2,J3,J4$ 排列。它们只有一个共同 $Z$，坐标为

$$
v=(r_{M1},b_{M1},D_{M1},\ldots,r_{M4},b_{M4},D_{M4},r_{J1},b_{J1},D_{J1},\ldots,r_{J4},b_{J4},D_{J4},Z)\in\mathbb R^{25}. \tag{47.1}
$$

在每槽置 $c=r(1-r)/b$、$j=b+c$、$t=1+b$、$n=r+j$、$u=1+2b$、$d=100D$，并定义

$$
q=\left(-D,\frac{6/25-D}{j},\frac{12/25-D}{t},\frac{Z-D}{n}\right)^{\mathsf T},\qquad g(s)=100\sum_{h=0}^3q_h\prod_{\substack{0\le k\le3\\k\ne h}}\frac{s-k}{h-k},\qquad
\begin{pmatrix}h_4\\h_5\\h_6\\h_7\end{pmatrix}=\begin{pmatrix}-1&4&-6&4\\-4&15&-20&10\\-10&36&-45&20\\-20&70&-84&35\end{pmatrix}q,\quad h_k=g(k)/100. \tag{47.2}
$$

这些是 [FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md) 定义 14.1 的源图和四节点插值，在此允许 $r_{M1}$ 变化并同时加入第五 $J$ 槽；不以增益样本、判别式或三次系数作分母。原动作前缀 $J,M,J,M$ 的迹依次为 $j,t,n,u$，初迹为 $1$，所以前四读为 $0,24,48,100Z$，归一第四响应为 $Y=D+uh_4$。第五动作 $F$ 的归一响应为 $p=D+s_Fh_5$，其中 $s_M=n+u$、$s_J=n+r$。

在第五 $F$ 后作第六 $E$、最终 $G$，记归一响应 $V_E=D+\tau_6h_6$、$A_{EG}=D+\tau_{7G}h_7$；实际左乘给出全部互择迹：

| $F$ | $E$ | $\tau_6$ | $\tau_{7J}$ | $\tau_{7M}$ |
| --- | --- | --- | --- | --- |
| $M$ | $M$ | $n+2u$ | $(2n+t)+2r$ | $2n+3u$ |
| $M$ | $J$ | $(n+r)+t$ | $n+u$ | $((n+4t)-2)-r$ |
| $J$ | $M$ | $1+3b$ | $n+2r$ | $((n+r)+1)+3b$ |
| $J$ | $J$ | $u$ | $n+r$ | $n+u$ |

例如第五 $J$ 的矩阵是 $\left(\begin{smallmatrix}2&1\\1&0\end{smallmatrix}\right)$，再作 $M$ 得 $\left(\begin{smallmatrix}1&0\\3&1\end{smallmatrix}\right)$，其后 $J,M$ 分别给 $\left(\begin{smallmatrix}3&1\\1&0\end{smallmatrix}\right)$、$\left(\begin{smallmatrix}3&1\\4&1\end{smallmatrix}\right)$；第五 $J$ 后再作 $J$ 则回到 $A_4$。因此表中的 $J$ 行也确实属于同一原模型，而非另拟合的末端数据。

**定义 47.2（共同父的二十五行映射）。** 每个 $F$ 臂的四槽定义 $a_i^F=(Y_i,p_i,V_{Mi},A_{MJi},A_{MMi},V_{Ji},A_{JJi},A_{JMi})$，分量从 $0$ 编号。令

$$
\Psi_F=\big((a_2^F-a_1^F)_{0,1,2,3,4},\ (a_4^F-a_3^F)_{0,1,5,6,7},\ Y_3^F-Y_1^F,\ p_3^F-p_1^F\big),\qquad H(v)=(\Psi_M,\Psi_J,Y_1^J-Y_1^M). \tag{47.3}
$$

括号内按显示顺序逐分量连接，故每个 $\Psi_F$ 恰有十二行。两臂使用同一 $Z$，最后一行只联结第四响应；两种第五动作的响应分别由各自臂决定，不要求彼此相等。所有小数均表示精确有理数。

## 48. 二十五维零点的完整整数区间证书

**定义 48.1（有限区间运算）。** 本节及第 49 节取 $B=10^{80}$。整数对 $[a,b]$ 表示 $[a/B,b/B]$；有理输入 $w$ 编为 $[\lfloor Bw\rfloor,\lceil Bw\rceil]$，有理区间按两个端点向外编码。每一步遵守

$$
[a,b]+[c,d]=[a+c,b+d],\quad -[a,b]=[-b,-a],\quad [a,b][c,d]=\left[\left\lfloor\frac{\min(ac,ad,bc,bd)}B\right\rfloor,\left\lceil\frac{\max(ac,ad,bc,bd)}B\right\rceil\right],\quad [a,b]^{-1}=\left[\left\lfloor\frac{B^2}b\right\rfloor,\left\lceil\frac{B^2}a\right\rceil\right]\ (a>0). \tag{48.1}
$$

减法用加负号，除法用乘倒数；常数及矩阵元素也按有理输入编码。求和由零起按显示索引递增累加。先依 $c=(r(1-r))/b,j=b+c,t=1+b,n=r+j,u=1+2b$ 求值，再依式 (47.2) 求 $q$，$Lq$ 每行从第 $0$ 项至第 $3$ 项求和，然后求各响应及差。加减串从左至右求值，特别采用第 47 节迹表中所示括号。这固定以下表格的有限运算含义。

导数和高阶系数用截断多项式环

$$
\mathcal A_{T,m}=\mathbb R[\zeta,\epsilon_1,\ldots,\epsilon_m]/(\zeta^{T+1},\epsilon_i\epsilon_j\ (1\le i,j\le m)). \tag{48.2}
$$

每个系数以式 (48.1) 的区间包含；加、负、乘逐系数运算，删去商理想中的项。下式 $z-z_0$ 指直接删去常数项，不作两个常数区间的相减。若常数项 $z_0$ 严格正，令 $w=z_0^{-1}$、$\nu=-(z-z_0)w$，各幂从 $1$ 起逐次右乘 $\nu$ 取得，按 $1,\nu,\nu^2,\ldots$ 的顺序累加，再右乘 $w$，即

$$
z^{-1}=\left(\sum_{\ell=0}^{T+\mathbf1_{m>0}}\nu^\ell\right)w. \tag{48.3}
$$

因为纯时间次数至多 $T$、修正变量次数至多一，以上有限和包含所有存活项。该规则在 $(T,m)=(0,25),(0,12),(1,12),(3,0)$ 分别给普通一阶导数、混合导数和三阶时间系数。时间 $\zeta^k$ 系数为第 $k$ 导数除以 $k!$；$\zeta\epsilon_i$ 系数为相应混合导数。

置 $R=10^{-18}$、$Q=\{v:\|v-\widehat v\|_\infty\le R\}$、$C=10^{-20}N$。下表第 $i$ 行给完整中心 $\widehat v_i$、整数矩阵第 $i$ 行 $N_i$、行上取整整数 $m_i$ 和中心 $CH(\widehat v)$ 的编码端点 $f_i$；矩阵列按式 (47.3) 方程排序，行按式 (47.1) 坐标排序，绝不转置。

| $i$ | $\widehat v_i$ | $N_i$ | $m_i$ | $f_i$，单位 $1/B$ |
| --- | --- | --- | --- | --- |
| 1 | 0.4623529809454434977346899678865797426105842592397013061096473 | [3377868691339230085035,-24408852440391104288496,17416350586388630269100,1110720050165935034603,-4000829993846352594901,-648585050114982203458,2908635730183368314360,-2548484812428895143835,1683477355945082928099,-644910230011564297275,-395498647697424051174,248255753848300201778,7582002636033566716484,8615156375698920315181,-15120949398110843785523,-970018227679368173835,2224182534631765838768,-2516353274804088857508,-3360677512518530942841,6078864813399141050574,-722387937117417443843,17906384305871054460,-4133859088804810776775,5215159028121117788739,-2182601511458465776964] | 304 | [-3903233129793190726,-3903233129792030642] |
| 2 | 0.2295109253260685380304846896343562628584462952413778937819423 | [332581598845344369716,-2381914363245739950522,1698788833584286073719,102885918579456782749,-385776685769186854749,-74425696869614310333,333768472030582904394,-292440841942044982008,193180486288137872704,-74004008076419248113,-45383812748463035618,28487563009316379305,916180859925344911187,1041023296294750973921,-1827159008968127149312,-117213377077307583335,268761904345088783503,-304066724565533554140,-406091709691324037901,734547303589896831232,-87290658312691390931,2163740552336311974,-499520081514071771583,630180324697301864027,-263737408918716962750] | 37 | [-729349743992045374,-729349743991920100] |
| 3 | 0.5292151046022771897145415856229141570990766506362091422722854 | [224566087576619995400,-1695236522539210407440,1212205608993905730144,95820268825727659814,-293616674471809711257,-153565466221566063753,688677609659871933900,-603404685800023948598,398596891792871933336,-152695379156867748778,-93642205001312692823,58779508678379137096,1005015537058444951816,1141962938738182285689,-2004323898273656711978,-128578613968625528152,294821581033945355430,-333549625251648608516,-445467151260575922027,805770438025072513513,-95754530226120761189,2373541042364290183,-547954519629727513623,691283833981133277614,-289309900763966510020] | 40 | [1687181556989012005,1687181556989140259] |
| 4 | 0.696021189364131778798043222644409399564763236403034807210093 | [-4710217847069485138286,22567111505452203844511,-15347191601988968162142,-1048055703597696079735,3503920319471255090428,821942378217833789819,-3686071655540704540763,3229657648150358973931,-2133446309587406916354,817285332276379323174,501209670208599051301,-314610897503971694361,-8038612913532656089456,-9133986179939642245520,16031577003000865882954,1028435550038881302388,-2358129283676702784722,2667895396622067943294,3563067298600008935796,-6444951754088691029546,765892242281011481725,-18984758912080163080,4382812120911477648218,-5529231091313911759756,2314044130204156470905] | 322 | [2034617370151478346,2034617370152629898] |
| 5 | 0.1931002759647587474876788902833991250149586657934909892714416 | [1920165465468896802083,-9012300573842567261209,6127751024718979391132,413089157334002460791,-1395101729123212247302,-330011238883421713061,1479963931651261141405,-1296712944703467001684,856582259750100948416,-328141427152812671041,-201236520453572333903,126316801278245856856,3329960295167333063174,3783713887330294668428,-6641010764312345152043,-426024935471491950653,976844757917812005147,-1105164017470649185015,-1475985068689295821232,2669793119314777110644,-317267516747693544124,7864353473734943232,-1815560781542794465166,2290459833671560861058,-958582675609705960884] | 133 | [-3255002180305485105,-3255002180305018051] |
| 6 | 0.5474241072107808258031732411285779045453230539069798551509292 | [-190352821415534862623,1634624045480469403610,-1128261110305155925986,-67751570847181078472,250800145192801002415,-8400958778517038650,37674825940962330506,-33009881823665726427,21805658131272429345,-8353359759387925960,-5122794359315346498,3215594245102483581,-172665508791261420304,-196193595588687714940,344350502969169406120,22090297096846626402,-50651473947223126393,57305099899029014955,76532958432988073981,-138434439588634866410,16450994109954624641,-407783418867621207,94140679857804125677,-118765203633448943885,49704546220218930531] | 8 | [1883563542999707488,1883563542999757675] |
| 7 | 0.4350069765068805999638585256163244416044182177085087962101542 | [2992393309264464261449,-18825394508067508595463,13331666091888104598916,135750013066884545991,-2477707745476149866254,-1068900278371092156595,2403936040184271974487,-1923608897284171664080,2542119440927269411087,-1590808942489411605705,815595001244510760025,-665463194656382413138,5639815733799947139393,6408319385949444969682,-11247604679028607016437,-721540775591286705277,1654441478830916173670,-1871770490238628459086,-2499814735127160018514,4521717950257327792294,-537342843208695093504,13319529521629267506,-3074940045464008078851,3879256886733705319753,-1623511746941115801265] | 227 | [-4364372289798870311,-4364372289797985050] |
| 8 | 0.2262174308409851927581060597058714265219296391682978599694555 | [467945513724052283684,-2943884039862706000580,2084783881467620503490,21228362396734645276,-387459836989105849592,-174666305981847217379,427283688024877255185,-347161827162157201677,418751992112173397422,-252335962545705124770,178596150467153511554,-104064033134893182978,1059300961898217998932,1203645510792859796784,-2112586477629151898584,-135523725190513142859,310746225169502221367,-351566145836921771211,-469528842514745578740,849293735863379826168,-100926664548413899905,2501746705966772654,-577552016179916362547,728623193651500903566,-304936834173664819464] | 43 | [2924972886340897993,2924972886341048664] |
| 9 | 0.5267578809742307520302729693823864541959342164306415258394904 | [187408529821164701692,-1179002605418723662415,834939690117657062433,8501793628967210670,-155174643810553863640,-195310491643719394145,660501225568007468514,-562252639586970368116,486009892461233263293,-241790983080274527659,188734003162184132200,-41676833915693714423,831402043776358897982,944692182533461862287,-1658082809636813093733,-106367034635435826937,243892015578606245476,-275929903478629059053,-368514004347912335153,666575952596103221058,-79213215313916407471,1963518772440611887,-453296979716399653259,571866574405056855972,-239332461947709728532] | 34 | [-2792373472787341132,-2792373472787237391] |
| 10 | 0.7406016259656946384147290273577859712774948086525317662527644 | [-2496796447116573004894,15707553541771642344234,-11123690334861956781538,-113267246411781946695,2067352535759638100740,-72242313483820754735,-2475521511639646618000,2695677894938962786096,-3091170188235229750060,1697718661940810231134,-1084836032514771429255,555249918171119757612,-6110294045393884277180,-6942906937593581122551,12185889599784344753854,781732331817476337641,-1792456419447938151045,2027915205155667822919,2708351444727748857506,-4898923576673725686075,582168448432782375531,-14430656206674262108,3331454206409431480052,-4202867854973605977751,1758946502544227427511] | 245 | [2526630163067903835,2526630163068774744] |
| 11 | 0.173751292743032345096675522223968617194209432855068721867214 | [1201779006663142634276,-7560491410638851748954,5354147926835244237747,54518741020086569070,-995075461484645408712,69884639873230014882,1189970679207632274166,-1297556112829746224271,1478105149473525304442,-809581454302952209540,551711619514648677819,-267257547518580123257,3043707236780926052338,3458454852296367548500,-6070130191105410866279,-389402594687258024498,892872345415322481891,-1010160908731274646096,-1349105105388186627012,2440289948729844618903,-289994279547991687045,7188310808194612155,-1659489903713626694249,2093565254042118634106,-876180124742139312960] | 122 | [-2856180310582034758,-2856180310581609695] |
| 12 | 0.5501123011622994567941266164029645291054936405754641153219151 | [-172860082512510166025,1087477116701274655088,-770123664405420414543,-7841802876368521927,143128499852905007921,78526028848564480435,83826084621307418821,-55436929470099057477,-38876469856108502442,44478828400950737313,41117509029335899144,38441478391627589668,-19290260983051323864,-21918828424988560229,38470978474054392943,2467936990858238348,-5658803303903441828,6402149105809390556,8550293294314701316,-15465951986598316954,1837911763809805972,-45557729679683765,10517435104971190528,-13268496932784142139,5553012152480830786] | 2 | [4304908216217406945,4304908216217434891] |
| 13 | 0.01701568669634075770871075851231825979682037560879951632305887 | [85537795722499757571,-538125367691841887062,381086713193060931744,3880424692533493920,-70825468810010470715,49697098184380156863,-222870933333867214911,195274775331665948092,-128994554275883185676,49415519237321298263,30304637954457886554,-19022317229866860403,1402057484634969849757,2134581099185099059120,-3479893314490107534939,241229495169110695546,116135897793664489474,-1218349330325831918098,-1627147999374933239598,2943219836699088391857,-349760452252471064897,8669780807829334883,-2001501340426380060254,2525037153198913693705,-53399001031739902172] | 79 | [366042438000305078,366042438000446125] |
| 14 | 0.01329549734503161642002289212038610719899450606518040011565376 | [65142474338588938471,-409816709206930972447,290221781205267307267,2955190320501781805,-53938101227701430327,37847502566947252552,-169730397339429198170,148714167036580960014,-98237561194531894390,37633062281478875265,23078910131059542509,-14486704988601346728,1092998548831743299396,1659910449572470101378,-2707584549734137069127,184839024584632858356,92792365743765082483,-944607962041298480574,-1261556860065804123585,2281930824421533767210,-271175515741853725060,6721835664356003573,-1551799681046702900392,1957706332652478770768,-40666737142741323878] | 61 | [89613476832179575,89613476832288853] |
| 15 | 0.491223261309524964860813376188926025153403706385110121766426 | [-141707560684371641097,891494017982194594288,-631333413255218641695,-6428567780519542194,117334148426666082606,-82331494485165791072,369222704927432604356,-323505087332526440821,213700896470435577594,-81865012208053652016,-50204664332022999040,31513626817714188642,157537914464777723426,182641914117744603754,-318774129484879832562,-17329579114065142416,44231115337130647117,-68843999821390317656,-91943561497575879697,166309465494461714859,-19763550496604220361,489894296758116768,-113096756811099208338,142679651063082495487,88464311188693403576] | 8 | [1109077680369257808,1109077680369300326] |
| 16 | 0.7446422265304046139412637960271305148095958824074673900012335 | [-397111563451463256502,2498261783484216913794,-1769205521470657918532,-18014978098182470803,328809182113725874040,-230720141807546401452,1034684422675842922350,-906568502024111927253,598860757312528977821,-229412903820442794079,-140690113139773500695,88311629634794835401,-3354083081742984860895,-2372332084017205370928,5110683658732898405323,102537299192998468858,-627937815862234349785,1106466098156882786178,1477724042833159085004,-2672938612655082550331,317641314572628102881,-7873619087350649241,1817699836552692883320,-2293158404621095753242,247906327341595263896] | 100 | [3879017481555498287,3879017481555742324] |
| 17 | 0.1720606375337527409678845068378918408036338916979749866218084 | [195225239299762911953,-1228178173093593371825,869764577736318078296,8856398891107892361,-161646895155087244733,113425039815439073320,-508664397130599756273,445680934624601406295,-294407782129127818412,112782384520700383275,69165100019002717345,-43415152353054271685,1780114914566544109665,1280526643365535697818,-2712966298436667983525,-66417276152529347123,339922019081219797644,-577363554841315700435,-771089152994240933171,1394762425930504056991,-165747978046154445355,4108522360795052766,-948491454925480509788,1196589837241042779135,-121873993440394135915] | 53 | [4002653219520619024,4002653219520745295] |
| 18 | 0.5508992657951218907662996682583879050669908134931272818064303 | [-84896372602713664188,534090121643408261279,-378229054465469653551,-3851326513285871294,70294369162413637054,-49324434059796501443,221199688848769442540,-193810466431129023858,128027261528388528262,-49044966591589336803,-30077392264332819887,18879674390405280381,228898712995473623142,178658606928408594904,-281750096956796603105,-32972634167843692667,49629672181835156854,-38425192456266829839,-51318183935054363076,92825420305372694173,-11031001008387203429,273433889445646276,-63124813461170129379,79636468914005367057,52998577411445113665] | 7 | [-2146959327212719924,-2146959327212691474] |
| 19 | 0.02099874775199214232760593118818113384467508668958567922770172 | [100705338849529689158,-633545639552645967031,448660925372267634137,4568500745675369387,-83384225364282749264,58509376705622817429,-262390358221427957527,229900855550904581918,-151867840273090828200,58177868241593070676,35678249692296522028,-22395350337898632124,1766115851100785106643,2006773799117747104293,-3522202470463267772267,-225951460319914088116,518090565081846797027,-1509540385722761678447,-1484690390431179769182,2926509432363091699019,83702676356127539063,-366989630738649682342,-517384415901015468721,1214794490020709427132,-62867700151796690638] | 82 | [367433376795409033,367433376795565406] |
| 20 | 0.0163613230552002474371982956541862072105838602073822220895907 | [76193199413304008762,-479337737237447520268,339454806928603519971,3456506798067311343,-63088124062593813974,44267927180510781589,-198523346592035234759,173941937263647660483,-114902514311429188971,44017109390753306623,26994000760819612341,-16944219777423298366,1368711382614571833679,1555217422160153592099,-2729650271918165208700,-175108748084387598369,401511856207372279577,-1163681294962019006081,-1146317693512945991950,2258430696362502787624,62780458314580562463,-281632091222311667636,-399808560138252396821,941446193913314880753,-47565414793736315221] | 64 | [-266923388235836496,-266923388235715977] |
| 21 | 0.4912530823299878233447555601649982688486142514825796556884152 | [-141646486375030745742,891109794436415875208,-631061315902105111017,-6425797142627320935,117283578774329592594,-82296010569287195393,369063574238939233810,-323365660405115650231,213608793871291046223,-81829729340607171041,-50183026706020818137,31500044811338357515,162842702031858681490,185032294235619666831,-324760670165569678509,-20833597243128641057,47769950913784061993,-73187843544856167792,-93358494009097488194,170858077571135648020,-16742162947065567138,-2597439579641548512,46517987610639746784,112008743393072743933,88426184100194565597] | 8 | [-1141826820849276339,-1141826820849233763] |
| 22 | 0.7604049767318028204791639413808080365145237795232505258073663 | [-359797072662103906048,2263513226935008780901,-1602962558003114713839,-16322205093859462908,297912707856463356293,-209040580196267286139,937460554339532771725,-821383014790530892758,542588952939402537856,-207856176506420903289,-127470201119886790204,80013448987623545438,-2435735378522503231319,-2767638338196518954796,4857638960818752016216,311620534625183884196,-714523635503318045166,324183536735106899192,1900960204775084891551,-2533111936384846717846,37003054715362362756,138662538065712007704,851457749911528416114,-1675381552763602053355,224611870016273641317] | 100 | [223741047050233998,223741047050470980] |
| 23 | 0.1643129598701794285226781049204425113022495194922210727966568 | [187472427187163137062,-1179404589048089080997,835224364710734432022,8504692334910166814,-155227550959543834747,108920688709468546737,-488464245175518171778,427981990775405190210,-282716218950508066945,108303554632023006888,66418405856302052668,-41691043727343740714,1359938106431529747975,1545248664580870696419,-2712153540304150623579,-173986321962617199673,398938213253848956448,-170888111052232311788,-1029151190847149870551,1391578838087560724303,-31968537523473044699,-69732409072066273095,-467019425233987705125,935411636463447310793,-117034116301840459956] | 56 | [2589866502112561113,2589866502112690000] |
| 24 | 0.5519214667656311937130279378196509730434807075736399635797351 | [-78160943374103902267,491716977706351888956,-348221470508051814592,-3545773562420733718,64717420063788997436,-45411178114154732589,203650354242878830890,-178434112408095167433,117869954061407180788,-45153882775287142800,-27691140169374961362,17381816392268546902,156189571531560457382,177472581795584656777,-311492190258173356482,-19982416075537411525,45818253272706678920,46670002080692589064,-44763868521077902814,108005010452916611082,-29626548476208205131,9611584406660405731,8597837973852661864,107432494180364788480,48793825707361419628] | 7 | [-1842108159857004902,-1842108159856977390] |
| 25 | 0.6038517424266165571243426488360619789819952645337924479139631 | [79129964017694581163,-497813166949115559676,352538636843272926333,3589733213253481178,-65519771127306468889,45974175016991099759,-206175162527131025208,180646295769504170573,-119331277502680167225,45713689792176650232,28034448288626471915,-17597311986104887094,171603256729207719878,194986596849131915690,-342232031049624455700,-21954395816928168332,50339862016020685245,-56952554327188568620,-76062121532905188587,137582779810479345729,-16349786274420670028,405274702560607602,-93561518842948617148,118034550572840445305,-49398759864359634799] | 7 | [3142061228797988504,3142061228798016900] |

具体说，以 $v_i=[\widehat v_i-R,\widehat v_i+R]+\epsilon_i$ 在 $\mathcal A_{0,25}$ 求 $H$，所得 $\epsilon_b$ 系数记 $[DH(Q)]_{kb}$。逐行形成

$$
E_{ab}=\delta_{ab}-\sum_{k=1}^{25}C_{ak}[DH(Q)]_{kb},\qquad s_a=\sum_{b=1}^{25}\max(|\inf E_{ab}|,|\sup E_{ab}|),\qquad m_a=\lceil10^{12}s_a\rceil. \tag{48.4}
$$

式 (48.1)–(48.4) 对上述全部整数和有理输入给出表中 $m_a,f_a$，因而

$$
\sup_Q\|I-CDH\|_\infty\le q=322/10^{12},\qquad \|CH(\widehat v)\|_\infty\le\eta=4364372289798870311/10^{80},\qquad \eta+qR<R. \tag{48.5}
$$

同一输入还给全盒的严格守卫：每槽 $1/100<r<77/100$、$1/100<b<24/100$、$49/100<D<56/100$，且八个 $D$ 的每个差的绝对值都大于 $1/50000$。前述分母 $b,j,t,n$ 因此严格正。这里的分离直接由各中心坐标加减 $R$ 得到，不以方程零点为前提。

**命题 48.2（唯一精确联合零）。** $H$ 在 $Q$ 内恰有一个零点 $v^*$，精确定义为 $v^{(0)}=\widehat v$、$v^{(k+1)}=v^{(k)}-CH(v^{(k)})$ 的极限，并满足 $\|v^*-\widehat v\|_\infty\le\eta/(1-q)$。

证明。正分母保证 $H$ 在盒的邻域光滑。沿盒内线段积分导数，式 (48.5) 使 $T(v)=v-CH(v)$ 为 Lipschitz 常数至多 $q<1$ 的自映射。迭代差由 $q^k\eta$ 控制，几何级数、实数完备性和盒的闭性给唯一不动点及位移界。在中心，$CDH(\widehat v)$ 距单位阵的范数小于一，其 Neumann 级数给双侧逆。两个因子为同阶方阵，所以 $C$ 可逆；不动点恰为 $H$ 零点。这里复用闭盒收缩及矩阵几何级数，不将有理中心视作零点。∎

## 49. 原第五 M 方程的百片完整管状数据

**定义 49.1（原方程与二次预测管）。** 令 $\theta=r_{M1}$，$x=(b_{M1},D_{M1},r_{M2},b_{M2},D_{M2},r_{M3},b_{M3},D_{M3},r_{M4},b_{M4},D_{M4},Z)$，$G_\theta(x)=\Psi_M$。这与所引根卷式 (14.7) 是同一有理映射，只把其固定 $r_1=7/15$ 改为参数 $\theta$。置

$$
\theta_+=7/15,\quad \theta_-=0.46235298094,\quad h=(\theta_+-\theta_-)/200=647052859/30000000000000,\quad \theta_k=\theta_+-(2k+1)h\ (0\le k<100),\quad S=10^{60},\quad\rho=10^{-9}. \tag{49.1}
$$

下表每行含四个完整整数数组 $p_k,v_k,a_k,N_k$，前三个长度十二，最后一个十二乘十二，矩阵行按 $x$ 排列、列按 $G$ 方程排列。其数学含义为

$$
P_k(\theta)=S^{-1}\big(p_k+v_k(\theta-\theta_k)+\tfrac12a_k(\theta-\theta_k)^2\big),\quad C_k=10^{-20}N_k,\quad I_k=[\theta_k-h,\theta_k+h],\quad\mathcal T_k=\{(\theta,x):\theta\in I_k,\ \|x-P_k(\theta)\|_\infty\le\rho\}. \tag{49.2}
$$

下面给出后三列的精确有限求值规则；它们是数学区间界，全部数据已在本节表中。把十二维修正 $e$ 编在 $[-\rho,\rho]^{12}$，记 $\mathcal G(\theta,x)=G_\theta(x)$。在 $\mathcal A_{0,12}$ 以 $(\theta_k,p_k/S+e+\epsilon)$ 求值，取得 $D_x\mathcal G$ 的系数区间 $A_0$，置 $q_{0k}=\|I-C_kA_0\|_\infty$；区间矩阵范数指每行各元素端点绝对值最大值之和，再对行取最大值。

对 $\delta=[-h,h]$，用式 (48.1) 的区间乘法（包括 $\delta\delta$，不另作平方缩窄）形成十三维区间向量

$$
V=(\theta_k+\delta,\ S^{-1}(p_k+v_k\delta+a_k\delta\delta/2)),\quad V'=(1,S^{-1}(v_k+a_k\delta)),\quad V''=(0,a_k/S). \tag{49.3}
$$

各整数除以 $S$ 后先按有理输入编码，再依显示顺序求和、乘法，二分之一在二次项右侧相乘。在 $\mathcal A_{1,12}$ 求 $\mathcal G(V+(0,e)+V'\zeta+(0,\epsilon))$，其 $\zeta\epsilon_b$ 系数为 $A_{1,kb}$，置 $K_k=\|C_kA_1\|_\infty$、$q_k=q_{0k}+hK_k$。修正 $e$ 在此随时间固定，故该混合系数确为沿二次预测曲线的 $D_xG$ 变化界。

再在纯时间环 $\mathcal A_{3,0}$ 计算中心曲线 $\mathcal G((\theta_k,p_k/S)+(1,v_k/S)\zeta+(0,a_k/(2S))\zeta^2)$，其 $\zeta^\ell$ 系数记 $b_\ell$。用全区间曲线 $\mathcal G(V+V'\zeta+V''\zeta^2/2)$ 的 $\zeta^3$ 系数 $b_3(I_k)$ 作余项界，定义

$$
\eta_k=\|C_kb_0\|_\infty+h\|C_kb_1\|_\infty+h^2\|C_kb_2\|_\infty+h^3\|C_kb_3(I_k)\|_\infty,\quad Q_k=\lceil10^{12}q_k\rceil,\quad E_k=\lceil10^{24}\eta_k\rceil. \tag{49.4}
$$

这里 $b_2,b_3$ 已含阶乘，式 (49.4) 不再除以 $2,6$。矩阵乘法均按方程索引递增累加。最后一列 $A_k=\lceil10^{24}\|P_k(\theta_k-h)-P_{k+1}(\theta_{k+1}+h)\|_\infty\rceil$ 用精确有理数求值；末行无相邻项，记为 $-$。方括号为向量或逐行嵌套矩阵的整数数据，不是程序。

| $k$ | $p_k$ | $v_k$ | $a_k$ | $N_k$ | $Q_k$ | $E_k$ | $A_k$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | [230007806788114425661906575035836921830881703497587766696214,529780372182314944182137307133914884911632912516525437202882,691475108171147762788192788370614715164661174422894320449259,194963493891424777785808758179909014028375618120611724544292,547321808480913696749419810183215047572444627073897075662170,438173225315245541356086667510069888907086449193946572668231,226800616831863712357560325104814115873651881966119472926972,527222824659065841229311299086506479075609266451437921904787,737173739237253467028211053252342742605802869878098319162130,175448662208721598173023227978867072455725671364951572961944,550099018933060913995524921464342783627714575835547362980369,603947293907031585278214998573651821962741115828885411524752] | [110688549324959572213574264157182261473002044244400293276712,130840255504438723847015831698994947559900363341678274305154,-1058113519093313169557472722168823910499333674967581600510759,429002548787142684458728015019824801173245160785484694825402,-24896252270085727769797325032366308083138889873175486376092,731401815645694625684921614288214053760533165664106196095526,132051121544741449229046439838959495871086465763050876802230,106980513928119689164790897121323856863406419390443236565040,-791262329467483907751251310054739029087212532031663486314820,389453299616920838318497527887021098194368835048447810117166,-3635598635516976988763328000041126610959710872929380497410,21889036669282917189635424067213283231274434505459489822398] | [-2369300054340752664029048885205595461885496122210897085770397,-402454080835107165501297577649046544294403857226413494624036,493712392874081000513157556547193572119550597050147258910752,-2380606817536523251531652866510642851174459948541308459693400,-495446481238223765816995972602200504139838410519073394794315,-2993353115760819410209520864628516406793125422423481943083587,-1773426754052877731690868456020034440581088811683668334231909,-633483974022007704544007034300015043242037587875628993968759,3506047747904497783579214694799487045967526266061040401192384,-2815097259209943919345072125954025604231530458304767319751204,-247669704274551229490014338705206463130881922556810933287167,-174825997222423028289906005759417286107625915865978803665213] | [[-77308027929044767207,586652226593706618931,-419060008550713954755,-32513550337372300849,100952142221661176240,4335781497573310748,-19585661612470708294,17184341341601017073,-11348848180146451761,4345896685183198954,2620562924738910760,-1640699070692071448],[-228850594448209973823,1593351598854997873022,-1133275663930823649091,-53366441690311478622,244794900331364449425,-67424750042827069835,304572160608954320052,-267229776282903506199,176483351905218849275,-67582049020327372692,-40751776875959455892,25514137370350987705],[-1165465417310544641647,-3434695413389720856825,3231367258554582086823,134305930780749751419,-764682731015407420563,135750879517852655450,-613216046823399121309,538032060047991520817,-355326052023545986589,136067580351439159814,82048350929189882353,-51369364898860722960],[439941851304046285083,1746961730020868312492,-1552712389975986218092,-76662334943084667491,369573061198574870573,-44342237913588757370,200303467183780554542,-175745053708096209155,116065195243558036075,-44445686405121203222,-26800618237182741403,16779505281331740660],[-121408781758438273863,1121114337626573880210,-759019915467715069729,-44035819462768967904,165549574660646129562,-23666279063483784515,106905694768779396206,-93798411645077270815,61946158548529278457,-23721491452043745650,-14303989607179617808,8955534795268020835],[511721307227587343497,-721313048228037763533,407246464233607515071,-731077802328604237056,524482018295441160103,-613778292171404905442,250727087721924265606,-28864310733199181383,1345541464360143837285,-1157169867777885458978,1132360808465731464304,-866074365872287882586],[-4375236951211346433,482956871290441731664,-360350822258330820581,-136443456438940564693,175367691608962520440,-83769067211216269972,19123296429221611680,10449961346018955882,182078347812648796003,-161175950405590959706,230005799593526244884,-135595736001499254449],[-186072923542751068530,1547932930546326466766,-1110369028311662275407,-118934652349796897471,294252249593348457989,-126759120922135501717,345175709053558129914,-285619471370959329527,308251638265574662958,-175929390937925760041,234558882670137570439,-70673467095153935231],[213975121274360236030,-4083731302973630554429,3001138043605430380893,826217872226444312621,-1207358564794394258573,-585662691147711332374,-138348087577991450513,654896681555603876254,-1799483491101468427136,1225891215646932915370,-1427818241645489235705,772200703445444280808],[-149247961366803534479,2288369040933886150562,-1674118204046958240310,-408678836871288962966,630879247347246259221,323223257228803838001,23280358006936506808,-275615312972740093374,821937537913426899391,-566040789877860658823,714367114833393567374,-370641759488939906588],[-170164806366624858053,1065787865305444145052,-753615282586440665261,-4076042212264776536,137143461447248333102,77374603442707116836,93286448043828026584,-63342200434461744484,-37433409698033319486,45461706452095732960,38654028621806523140,40283975345360642642],[2941916651887072420,56817285156770493104,-43289341514927343528,-22448440534755867973,26011852632004718971,61477740225636354358,-277708232629481866027,243659527939518308584,-160917135854222667089,61621165090695244011,37157381390690929964,-23263734879837464335]] | 170485419977 | 2779331041027 | 154341045754 |
| 1 | [230003029827608668475683999349304859186855262143187378932280,529774727770468933283975256581665774027398922943374375583041,691520752322326149785335252832111217857942811121778230319369,194944985854847345166845047243326921533600338308639977123046,547322881966038428899088378655966424809466306229982680885837,438141672155125506644424855909597168691575791425599135623821,226794918911420567036488308042342282267449909590371525171036,527218209266582308327477925443828509826227883349915762569510,737207875068809318002827436991073154048966476796982507014408,175431859798317068960331362765188247144140419934517919367200,550099175530887468256199425365810893226443941477935511392721,603946349520133198181937441561545247128098569088763372504086] | [110790751353481731676654461457420740146165982352450821389337,130857614622313102200075418697805457977661814032137751608915,-1058134815332336389466560843969965665897439780445243471134222,429105237938153090922845159039505804026706919927032274939491,-24874880587885985805561565205043668672227611721327800706903,731530897452558644767948261483243859045184053254599739750016,132127626827486690275662166139124793279378172004975095132898,107007835850747602984901359292996008427062144100707142693773,-791413526408869837581568676720370220038913610482986947700187,389574724098665511739965561839342807405902164633697635124588,-3624911994174843717005072948957080610105014923827857089451,21896577472188149439035909685282005776709352789525621006419] | [-2369201298461357584256472023675267353701709232203888781305584,-402385163493720488045553502157450239006817423922901311817160,493667786998914553207608280876133873203014729118577126594169,-2380479513718127847648427026848337021223826008427859867312678,-495431551019206314562225726719718766879251892082566257685854,-2991404223644836049298548854257517740664574659088060022447752,-1773669002372512995400729154300642917255403676662136311992988,-633271401989630874267243971150982849836253418783552993375964,3504057094400099689244448460542541601408620213384636614875388,-2814635178432953943379934943368505595901809266464374697837950,-247806395974162859674704362675596802631969947862246326409047,-174796267200478428929078132273675950952698449555711944727260] | [[-77290096134435660161,586453423151212783583,-418921252248147218603,-32501225487149058927,100917950477600977292,4331855186865772634,-19566504664027008369,17167296514558136336,-11337618947981740260,4341612838454638778,2618427544547096536,-1639403729107841383],[-228791382174002797628,1592797383154319396126,-1132890665173699966678,-53346021469180618946,244710485914109192212,-67426438356628620171,304557669560107444947,-267213378623196088156,176472950301956374105,-67578318709267594220,-40756497114448411071,25517740024521768744],[-1165083127468674389806,-3433411345372595668389,3230183478881081765456,134256321910369844198,-764402504551648461515,135736067472350230429,-613104612852036436629,537926873706018612754,-355257446085704342903,136041817594942927430,82046846564891405309,-51369726269545252082],[439906788052140340074,1746554645770968338793,-1552385681026808984604,-76642209206633279888,369494444131972945863,-44350525365232665216,200326355332007630586,-175762712897210503179,116077139018494937763,-44450426436627949649,-26808060801192767285,16784590789670663957],[-121325124164268496603,1120672138955011168028,-758734039800189567971,-44019357368906169371,165488406230576197345,-23661176883344084141,106874885672087816818,-93770087391511630122,61927602791875555371,-23714474491470558032,-14302204163148752979,8954644129205167229],[511385499041730024962,-720758635174084307315,406921131012767158017,-730651983520333813590,524208350978340702007,-613497100833475413761,250621318112642436602,-28855511816488796766,1344969167087581300438,-1156696064199586316196,1132129955142262181452,-865911616944541954385],[-4370889214204804194,482783562900582899645,-360227248701610771153,-136417821210804498316,175327630410433134935,-83772486865508495629,19141753401849321354,10434035117893870762,182094449320447312147,-161187593065294729442,230044934997071796428,-135627761216605722823],[-186040879040847214042,1547407682669484160499,-1109998608543359264045,-118875683040656334491,294140399075143441725,-126732660183642464420,345138770061995207160,-285590812071693403820,308181549976011500058,-175879599308181478899,234533996305674464910,-70655508874311145876],[214096806580238486744,-4082483595562855396990,3000213325546348348761,825753128639111566473,-1206831585309178874767,-585759725284841852807,-138277784037353232409,654764707043944849482,-1798816017466182991854,1225398852840982650359,-1427570856964764514688,772028716372865931977],[-149299934251077080162,2287846255570539570252,-1673735966674382830118,-408497911898297434666,630671801816453144509,323295021049023824367,23270813991102758503,-275604295023780320448,821736792727615297144,-565883777545276133337,714327336419716039286,-370603976073158810594],[-170103050690965549668,1065365573663153880305,-753324727511045894987,-4086010642844106870,137099730833304676488,77369442776910753829,93265369537360423203,-63327600287160413247,-37404097899205046487,45434638049804321664,38669011200671137309,40271600411209356787],[2939105646532405677,56794931502060426029,-43272505366051734725,-22439076930759052701,26001688985121964642,61469336962279394856,-277650109822185937456,243605173456468353547,-160881629094266380310,61607798740802167827,37155675364008105811,-23263256940650328402]] | 170433914499 | 2779495367372 | 154241478200 |
| 2 | [229998248458520499352493028997540263566013152475053401076197,529769082609869258851178946572961972186924628614169964793227,691566397392115851922840467686911434470093854440754963278261,194926473388701127537806966312393044195564044499691690573247,547323954529269854053029349862268503613436439310286174846797,438110113428634826160011198390858972914188739108998497729406,226789217690554665410158048637521049999498904919882061500182,527213592695714649077042733224854852223345121945509882187381,737242017420674354489183308408476892192817658925479118934567,175415052150471870910563078860657673435272691354690498669574,550099331667598760586043985791141377262846777207808363253778,603945404807975937130498862361555867024126560589753390653558] | [110892949120393926264777933039477941091080696313849566676177,130874970766879407712585763339202489243078340302552908363312,-1058156109646724403780143562900711280536539106060474912771238,429207921596131337309530826735871018673037199377766693140079,-24853509550188909707889839323552836535611431553954389922662,731659895218529646565297142499981273042803449421533117261263,132204142553660893573661324239203928880697402919989490062745,107035148605458694721160615570401327563468545076777274029181,-791564637507420109522194003294218997838369377178842239020371,389696128651065303232959825948599752974910975112801308584570,-3614219458988390829722995597431648425634678724085263717869,21904116992355272693560861160593674126424471674468846023834] | [-2369102468786337953054435617539998848507628770481722760172128,-402316226191071863381060553912271791699553833099167503916064,493623158965490292536951928611957527545631342253337741475482,-2380352138245482039490402679718789370923944420065685672008863,-495416599475999003809385753195178789170923220624589594031040,-2989456638333265014117325723750802261660789966049213432485812,-1773910953878875747141110876832493571487218914816326143225853,-633058912134892096469665033625981311078780164421776088312502,3502067725093978055755132408590784107421884830295276578620405,-2814173253777384936373421264188801701378552183262241196152885,-247942966856703756718170886961686168100527104036935623273827,-174766524271416374968121595796586812023730675271886942230570] | [[-77272177847134615284,586254765682121649629,-418782598534250117069,-32488909556937199141,100883783862374439802,4327929234629733141,-19547351910380524887,17150255783067909822,-11326392374722293316,4337329983331013661,2616291884511014002,-1638108163689095768],[-228732216717500700694,1592243594875019414833,-1132505965490141219381,-53325616949200358862,244626136910520725668,-67428126839506734197,304543178165521588168,-267196980259687887360,176462548316628128718,-67574588309057656960,-40761216617506289670,25521342667588583249],[-1164701154586088530699,-3432128290421276659568,3229000639959930175347,134206752290394507060,-764122500740653859374,135721259598385855211,-612993207435548554233,537821713601011693497,-355188857410783675696,136016061427560134100,82045341037848126296,-51370087467084834983],[439871762233457330286,1746147865088978681394,-1552059221732183539117,-76622098545007213486,369415887017215055764,-44358810854671642414,200349229179681070502,-175780358491798110003,116089073960814269701,-44455163177208653294,-26815502415571586133,16789676136836085211],[-121241539349725050638,1120230288499724694557,-758448389088035770405,-44002907818478812878,165427285595359123541,-23656077298997898861,106844091646114165664,-93741776842280021312,61909056042625848924,-23707460957530608618,-14300419369502099132,8953753918683014449],[511050005261995012583,-720204841301444035172,406596175272906571859,-730226533313823967933,523934900441777073535,-613216044204748635913,250515581886162007040,-28846701647749019737,1344397132486716826747,-1156222480626222881298,1131899181639099037628,-865748917883126418027],[-4366550530797881178,482610387464473806058,-360103769323011092980,-136392198838788835511,175287595723987839074,-83775894297349601748,19160200278378039427,10418114646712231087,182110523482577051651,-161199214791267611072,230084060697946378310,-135659779590425858042],[-186008857033977140137,1546882831022578998897,-1109628470851421696675,-118816761705756657936,294028635761981570169,-126706212539685327043,345101842270960915020,-285562159066133566292,308111488453572298340,-175829827851127597683,234509113911444428177,-70637553199320118931],[214218348944190551915,-4081236693623437612485,2999289223563758016538,825288782899692337013,-1206305022282585028591,-585856679777253758263,-138207503481070097362,654632752465513572466,-1798148829901907687908,1224906713468971982471,-1427323545969809291379,771856775963200341824],[-149351866562768586312,2287323853117513256391,-1673354017050460525951,-408317133049677100026,630464519951368693807,323366761922759439953,23261270075699497219,-275593272125545454627,821536114694502578058,-565726820715292418861,714287572415496725754,-370566199663459302526],[-170041347145706870677,1064943622408927515188,-753034407215030366728,-4095968085639944145,137056033585665797426,77364285227288607449,93244298576316872467,-63313006550221934175,-37374801868168350751,45407583998677657929,38683986953770465060,40259229623898879705],[2936298123225336973,56772586069463352632,-43255675817899192779,-22429720189332073740,25991531769803403684,61460936126881942147,-277592003492257716893,243550834151520791583,-160846132307513466410,61594436187569441135,37153968950457643471,-23262778977954527538]] | 170382452326 | 2779660460538 | 154141960050 |
| 3 | [229993462681033819409074006186781822046358844165544744525775,529763436700644198619710727633506541708594675603830667505011,691612043380433825872061402923174170720744787382080628614327,194907956493223143705601833883262310760643485485328806935078,547325026170635793869798445985634475234518253471085616557568,438078549139397544264703278014092420348228295781608731011859,226783513168815786890382619985974445046135327138440348412492,527208974946858262153160576142891739736200298868227350441008,737276166289146780951215922855644785712345112399238788996584,175398239266045548104784339791368181644325736453649041430713,550099487342940661455717557341695195480791618642917009500669,603944459770615147422497212681664692574596218758658586881095] | [110995142622513057744613778987847909850565533441895801003456,130892323937276701446181254916536001419499052091278726203562,-1058177402035521473814397012739031287365685923710708620120241,429310599757986765713917718220521520656234718249492250166615,-24832139157914298690385767486819396648262957687660975559816,731788808999965261575128799314927348497960985734126603263788,132280668710463042314507724161092749008781254165102145410397,107062452195796919663816005131177021790540439635604773931945,-791715662818517259261429868607426970774993719509743677067862,389817513280852717581321123047207484847858715665928210185585,-3603521035168196579622926837569558173786880408842109118148,21911655229227572046222142960014939738099448454429087856467] | [-2369003565325575055009576207713073359033639377418721019299872,-402247268933057825618059713336967332480167847528300750982362,493578508778395053921196198786755304273555449549562466384173,-2380224691131628024026159444535272438861228908849003380470964,-495401626611352631649238803035532959927431497672964203456721,-2987510359185984599202275387480751818190101696313010715530980,-1774152608691365784621450321444940498660763152427234847145417,-632846504414678732135875522105573872542353442196685996327705,3500079639348925352881463842645415614662214169003519136755913,-2813711485146664906008771644290052959018370692389762036773862,-248079416972739461396785555016761767120616878353526192545714,-174736768437906608021367045754492148476939490194237328366005] | [[-77254273050357657372,586056254013967989372,-418644047287829467776,-32476602536323669075,100849642346357896055,4324003641039300487,-19528203352215574652,17133219147746401690,-11315168460766305374,4333048119958679956,2614155944907596460,-1636812374552281454],[-228673098022707829080,1591690233516088461347,-1132121564529928673589,-53305228112076692592,244541853244061413694,-67429815492439104846,304528686433351430918,-267180581200062015871,176452145954241462282,-67570857821583033872,-40765935384645970902,25524945299369215772],[-1164319498293210918141,-3430846247350515886590,3227818740690916224909,134157221874913274781,-763842719322021538541,135706455896858452601,-612881830581751750587,537716579740439053343,-355120286003605139457,135990311851079579056,82043834347892657345,-51370448491394426660],[439836773806713631498,1745741387617031939696,-1551733011798705077655,-76602002940594870366,369337389783905915914,-44367094383114688013,200372088736761154553,-175797990501216475194,116101000076632079633,-44459896629175181751,-26822943079672938220,16794761322577503141],[-121158027229269026785,1119788785853407248922,-758162963068153319981,-43986470796841804475,165366212699087837957,-23650980309845431887,106813312686965496055,-93713479993791219949,61890518298417779744,-23700450849325283281,-14298635226175333406,8952864163671850804],[510714825510673205098,-719651665759737888186,406271596484208763044,-729801451290868210993,523661666459987924666,-612935122257700448213,250409879060401811404,-28837880252512814329,1343825360514179989936,-1155749117016030607203,1131668487968297615266,-865586268696482298303],[-4362220889044916324,482437344818537335681,-359980384006531136355,-136366589305919411321,175247587515747342033,-83779289515526881505,19178637061629233179,10402199932478263832,182126570315400460359,-161210815596574140746,230123176696190057890,-135691791121239420261],[-185976857494979740490,1546358375148116276264,-1109258614910523834015,-118757888290173154353,293916959553701950849,-126679777988366765353,345064925684297088851,-285533512358665126574,308041453696958911696,-175780076564513227244,234484235488423147039,-70619600071142260411],[214339748541172127049,-4079990596338097100073,2998365737025736829782,824824834555964140650,-1205778875255423204619,-585953554662610020380,-138137245926446808262,654500817854501878302,-1797481928372167754032,1224414797490837996513,-1427076308672711087098,771684882225145402634],[-149403758346441747628,2286801833129873974349,-1672972354842035284554,-408136500156925115897,630257401563294540982,323438479851360529424,23251726269283801538,-275582244288422069233,821335503816755994002,-565569919386903916930,714247822822282019030,-370528430261965967663],[-169979695668846940135,1064522011137614785021,-752744321419035021094,-4105914552507958154,137012369663516731083,77359130790707066738,93223235161933376723,-63298419223296566759,-37345521600011181903,45380544294576244914,38698955880518257545,40246862984178929858],[2933494078512491611,56750248848099015594,-43238852861712175059,-22420370302474528239,25981380978342686658,61452537719933152403,-277533913643077206497,243496510027845547042,-160810645496012752448,61581077431758352351,37152262150179225831,-23262300991830549529]] | 170331033417 | 2779826320638 | 154042491337 |
| 4 | [229988672495332667061825012682401033478389973783661041552200,529757790042922067458246097910158730464157251385641851114109,691657690287196987081056275190180932256117975570971955223508,194889435168650545786268697730459750034840484260628976497978,547326096890164109682638617016334366159645639076557700859393,438046979291035274824991413417926554490451063715179714878793,226777805345754262973495010644502426694212047683799119387433,527204356020408393396014791180648806959318102437883785665834,737310321670527190288416177721083444158165600011133906045117,175381421145897354294833672631794865306503835541683804872121,550099642556659266056791820118415677435205875030225684418030,603943514408106198368977516440152372527955438070323945669641] | [111097331856656454333969172541879319718126218921674879079343,130909674132644298879605022695465662866221681075464447525464,-1058198692497772058807651358063371474312554218288089323104841,429413272420629281024436615698367646906057356366082375243822,-24810769411981833247677901951610220978259132838454644701870,731917638853195498428257435623966295824570715997983346937927,132357205285097272038910343034318687817867357971784413402166,107089746625304372647001035307482012648267079638736725096147,-791866602397516326375890786145119461206874909850347813556363,389938877994756092335340001984847472911114764580080925042748,-3592816727922657163987204710062124569903682979290852803353,21919192182248447788828270668003749016300462342629138094373] | [-2368904588088959612787734233008188007489225151271872585297114,-402178291725577651454089189208270289722500174047845831355516,493533836442218477082343818780392973445330122373957423806030,-2380097172389616988010952509649334369666651291151570645828294,-495386632428020693972967525702817791387714110125120673656909,-2985565385562454874295901545767059004844538110996365428032292,-1774393966929467091963821850265042455730990380188849386299229,-632634178785845144621598320372312347789815062583708937393139,3498092836527318018311902104470183153336416166709297823204862,-2813249872444156028586190659335832936868293859517263563826496,-248215746372873359137402261221724741698669402451681389327635,-174706999702620470712878394595117253769608470922474177331251] | [[-77236381727346844383,585857887974554729222,-418505598387880425312,-32464304414911639596,100815525899973742542,4320078406268168141,-19509058990213220968,17116186609206610296,-11303947206509971423,4328767248483241880,2612019726013845485,-1635516361813883470],[-228614026033715457266,1591137298577296176964,-1131737461943388117015,-53284854939544057598,244457634838312621578,-67431504316401408983,304514194371737872050,-267164181451988817635,176441743219795333757,-67567127248726009464,-40770653415380363621,25528547919681453241],[-1163938158221040051854,-3429565214976907504254,3226637779975538721712,134107730618087029354,-763563160035754119761,135691656368661965986,-612770482298427587224,537611472131736706710,-355051731868968732044,135964568867282048471,82042326494857640325,-51370809342388975797],[439801822730689510974,1745335212997817116849,-1551407050933424682712,-76581922375812035542,369258952361759625014,-44375375951769712207,200394934013201086826,-175815608934816550772,116112917372060125881,-44464626794837760560,-26830382792850602172,16799846346644411489],[-121074587717494182379,1119347630609384766097,-757877761477850906199,-43970046289372846055,165305187485942213010,-23645885915286142997,106782548790743782532,-93685196842449272811,61871989556885875309,-23693444165954800465,-14296851733104030856,8951974864141923655],[510379959410621044916,-719099107699976262417,405947394117732710049,-729376737033864266636,523388648807516480713,-612654334964714277209,250304209653209945578,-28829047656275479481,1343253851126404042891,-1155275973327092589604,1131437874141840557359,-865423669393001601470],[-4357900277014001786,482264434799451589960,-359857092636352194902,-136340992595256368798,175207605751891516050,-83782672528828946922,19197063754429373002,10386290975191973710,182142589835285826945,-161222395494283083546,230162282991855075336,-135723795807334975360],[-185944880396738178157,1545834314589309672330,-1108889040395843175124,-118699062739062886579,293805370350296116463,-126653356527779807359,345028020305829031142,-285504871953660475592,307971445704849447860,-175730345446071581741,234459361037580627279,-70601649490735039640],[214461005545888815639,-4078745302890756200899,2997442865301291707610,824361283156361661029,-1205253143769172281909,-586050349978609162386,-138067011390726024054,654368903245026214220,-1796815312840263635559,1223923104866360220539,-1426829145085484642198,771513035167350151767],[-149455609646595323521,2286280195163379205503,-1672590979716467155880,-407956013051792749839,630050446463819172381,323510174836198249483,23242182580395100615,-275571211522781375055,821134960096975736131,-565413073559055617291,714208087641606236237,-370490667870794595187],[-169918096198478410787,1064100739444698403684,-752454469844137682338,-4115850055289064911,136968739026109303574,77353979464032141131,93202179295439671410,-63283838306030502308,-37316257089812204503,45353518933352170616,38713917980334058799,40234500492795214050],[2930693508945906043,56727919827104047382,-43222036488746654064,-22411027262198466031,25971236603045438321,61444141741919827866,-277475840278007740616,243442201088597011353,-160775168661802891751,61567722474126341226,37150554963312561736,-23261822982358901547]] | 170279657732 | 2779992947786 | 153943072093 |
| 5 | [229983877901601218008397327724455772573803972120036644096116,529752142636831217357196397422870686664554066031474492554990,691703338112322209783128896196745845364262932175308069453327,194870909415220619180692837850309628221115320685368773272853,547327166687882702494356367522187988642522717283167093496457,438015403887167202403907610308682930544619294766285116341533,226772094220920977018013768704578445188412449104251340565391,527199735916760135891102073074326775454354750505713142653435,737344483561118562649346404581049780811871191872069017153032,175364597790886253083144653365300978577405898086687195736784,550099797308500894207589012729164384695154713576298437151895,603942568720504483288461066356691777744698248758067007993857] | [111199516819641871108854153989450796172159061222795876928834,130927021352121770026984566551968475114264823262830876900282,-1058219981032520816041330614518989619988421691204209170549355,429515939580969351310526915290974382190400735241648695683996,-24789400313311075039063949198664429076555723094341131981254,732046384834522725896727566540326922176647725002016322428192,132433752264772874259696568360786639394824683701245056256561,107117031897521286629225836741283477787169401444377385656294,-792017456299744836433643718177235739606322268541217575457005,390060222799499594980524776438670813597987687453124678631522,-3582106542457985096125075103867120603038790380877149101398,21926727850861415481032352135446534384492046897779184308040] | [-2368805537086391784153146929279586058379646744569484174715282,-402109294574533358738137545691873110417075038327443458890764,493489141961553004701802175666452363651013555431485188536797,-2379969582032509104248742399623867340872733644073467251918429,-495371616928759383597911909890049887698509492154146378161152,-2983621716821719977574566462696884773550450266723002249016730,-1774635028712747438152384117170565215110839935093687455976693,-632421935205212880612547125821611046296384397742516690468110,3496107315991118749821535105775701394271580154686655936687122,-2812788415573155044219244412561996995369918025574840993927954,-248351955107746496961469183384007933383851983446623263959406,-174677218068230906000059218998889856423160471619715512569437] | [[-77218503861370216947,585659667391952428744,-418367251713586115298,-32452015182320473318,100781434493690350458,4316153530489615677,-19489918825051279652,17099158168058473774,-11292728612347490657,4324487369049552913,2609883228106830877,-1634220125590425007],[-228555000694701818966,1590584789559189798419,-1131353657381388800764,-53264497413365279296,244373481616974484774,-67433193312367309688,304499701988808043503,-267147781023125882780,176431340118280321291,-67563396592365683355,-40775370709222406410,25532150528343084992],[-1163557134001147960845,-3428285192118884186845,3225457756717003050165,134058278474147861357,-763283822622258133801,135676861014685367420,-612659162593322966365,537506390782308443775,-354983195011653328572,135938832477940328313,82040817478575747004,-51371170019983424774],[439766908964229003216,1744929340874578538683,-1551081338843848437394,-76561856833101823739,369180574680599452269,-44383655561843536420,200417765018946995374,-175833213801942795304,116124825853205877426,-44469353676504973247,-26837821554458395076,16804931208786299056],[-120991220729126683664,1118906822361615096767,-757592784054845470340,-43953634281472391058,165244209900188894789,-23640794114718750553,106751799953545934895,-93656927384653510951,61853469815661578497,-23686440906518214420,-14295068890223664482,8951086020063439415],[510045406585259474250,-718547166274556340243,405623567645411673549,-728952390125812969984,523115847259211000781,-612373682298081345806,250198573682363891431,-28820203884494689449,1342682604279626413437,-1154803049517339964055,1131207340171637690442,-865261119981027397212],[-4353588682786966305,482091657244149402436,-359733895096837158088,-136315408689894079792,175167650398659273104,-83786043346045708913,19215480359609916655,10370387774849151738,182158582058607239193,-161233954497467399354,230201379585005822171,-135755793647009880459],[-185912925712179795206,1545310648890079872212,-1108519746983059477808,-118640284997664540539,293693868051907732669,-126626948156007856528,344991126139365538576,-285476237855479104357,307901464475898320399,-175680634493520015995,234434490559881203355,-70583701459051995756],[214582120132796560015,-4077500812466537330719,2996520607760357224481,823898128249975544435,-1204727827365978287502,-586147065762985108055,-137996799891088408278,654237008671127742430,-1796148983269271525653,1223431635555161030836,-1426582055220072039150,771341234798414853640],[-149507420507663254718,2285758938774475794154,-1672209891341631274288,-407775671566284898859,629843654464817377784,323581846878665019927,23232639017555198558,-275560173838979236210,820934483537695070742,-565256283230643202677,714168366874991640470,-370452912492052192566],[-169856548672788289861,1063679806926292837512,-752164852211852211315,-4125774605809449607,136925141632761998234,77348831244129468374,93181130978059233902,-63269263798065871642,-37287008332640827453,45326507910849133479,38728873252643196002,40222142150489433955],[2927896411083017283,56705598995631937514,-43205226690272091186,-22401691060528365434,25961098636229234365,61435748193326420850,-277417783400396013520,243387907336914068783,-160739701806912380815,61554371315427005256,37148847389997385961,-23261344949620110139]] | 170228325231 | 2780160342097 | 153843702350 |
| 6 | [229979078900023785209273329221496311301378504561546120855278,529746494482500037417726401613773829567511428685019071253369,691748986855726327005374236823998454913357098025252202118129,194852379233170782550303548269079426808721277178110642066141,547328235563819512972193065010419608962365699622326986599006,437983822931410083453708474406472862558543678784258510535741,226766379793867364022152739823503657835866722066854961522739,527195114636308430049578413741486263873520704657321871243762,737378651957226264244388278095180257907214712414624130007117,175347769201870918102690155284382963172715096019042942262440,550099951598212090258949684972752337331292350904008025285526,603941622707865419501971642661705051874452681710143607410399] | [111301697508287490410417783549161754344048139681646676945561,130944365594848939556045432792330100299091067154449134119844,-1058241267638812600960834536327974281629804288222376131245991,429618601235918008210185858871402483552237411884324380836798,-24768031862821466772192721472782771021360396750402120070320,732175047000221655001201935935490135947934137699938830796948,132510309636704300067383051438772322490668499655562008477454,107144308015986031281664836630627689224179305806576646763106,-792168224580502783196114146677200239187566097154828976559525,390181547701803220123397720199811199943487679779943041069652,-3571390483978207584710798250924623364311137300361873733165,21934262234510106019350841839394878819442677772400306860291] | [-2368706412327781158984935655101452620898142742928150534195897,-402040277485829705034013559915309835634258812952992083055387,493444425340993881076975796467918369817018756325672834779520,-2379841920073373527851642592035417271370839748586596654365413,-495356580116327589392540188302609434710220417593175459963267,-2981679352322410403713844133336144786368983699711990679926272,-1774875794160857976374617237672919864226277688133303589831802,-632209773629570850676365218321200008378588274422530182731939,3494123077101878792277503864883988549138246033774191878633781,-2812327114436893651134133875010381960607693893119109585391686,-248488043228037400834727262638159117094180408306170076924678,-174647423537412456496828267806231613091979648143214540394416] | [[-77200639435721748010,585461592094498760923,-418229007144317269308,-32439734828185693139,100747368098021976393,4312229013876509638,-19470782857404325037,17082133824908875610,-11281512678671070137,4320208481801717177,2607746451463690600,-1632923665998467396],[-228496021949931938349,1590032705963092647752,-1130970150495342383851,-53244155515331515910,244289393503865678225,-67434882481308458531,304485209292675325718,-267131379921118061916,176420936654678631606,-67559665854377973838,-40780087265685067675,25535753125171902800],[-1163176425265679089385,-3427006177596713557395,3224278669820217856949,134008865397398931646,-763004706822343236948,135662069835812665679,-612547871474150186477,537401335699525882069,-354914675436416715260,135913102684819217177,82039307298879679101,-51371530524092709693],[439732032466239786012,1744523770891114775150,-1550755875237936541618,-76541806294934626281,369102256670357625317,-44391933214541893387,200440581763937932363,-175850805111933174010,116136725526172513982,-44474077276483761353,-26845259363850172594,16810015908752649737],[-120907926179024848769,1118466360704686780061,-757308030537261412545,-43937234758563600272,165183279886181134518,-23635704907541233516,106721066171463812212,-93628671616798562719,61834959072373256127,-23679441070113418436,-14293286697469605257,8950197631406563567],[509711166658572893608,-717995840637259427701,405300116540051510376,-728528410150317168204,522843261590224237463,-612093164230000918992,250092971165570641246,-28811348962590534212,1342111619929889199342,-1154330345544552302431,1130976886069526147441,-865098620468853900511],[-4349286094459358608,481919011989817855251,-359610791272530164518,-136289837572961065940,175127721422348441879,-83789401975968357382,19233886880007293547,10354490331441383806,182174547001744540381,-161245492619204208792,230240466475718819836,-135787784638570269443],[-185880993414276022575,1544787377595053189592,-1108150734348353781310,-118581555011298272403,293582452558832306569,-126600552871124714973,344954243188698929053,-285447610068467622734,307831510008736300635,-175630943704560062790,234409624056283548081,-70565755977042744210],[214703092476102071277,-4076257124251760618245,2995598963773793796346,823435369386551197925,-1204202925588653152795,-586243702053507030978,-137926611444652737472,654105134166772440897,-1795482939622043905707,1222940389516706056271,-1426335039088342825482,771169481126891081613],[-149559190974014779618,2285238063520298597635,-1671829089385916852122,-407595475532659609265,629637025378449702639,323653495980174474785,23223095589268298789,-275549131247356186012,820734074141380474949,-565099548400513153426,714128660523948461880,-370415164127836999920],[-169795053030057760252,1063259213179143082028,-751875468244127660422,-4135688215880589516,136881577442859822184,77343686127864322428,93160090211009292334,-63254695699040752798,-37257775323557233356,45299511222902467950,38743821696876769751,40209787957999292641],[2925102781486652358,56683286342852999901,-43188423457571410544,-22392361689501109105,25950967070223578204,61427357074635037754,-277359743013572107101,243333628775920122162,-160704244933359576185,61541023956410106075,37147139430373459188,-23260866893694721221]] | 170177035872 | 2780328503684 | 153744382139 |
| 7 | [229974275490784818869326843774309475028233292171621500729619,529740845580056953840766816866679550761497398668696503441451,691794636517326130577229204452742306769789167281093715505658,194833844622738587792755204676215040593956327774607751821567,547329303518002521442691231508818295899076300311508930795485,437952236427378247509327828241362728566713937872553553225883,226760662064145410401175644754614067847100532578691314599772,527190492179448063688665770683645788816136382573883850860357,737412826855158046157725097281840612489245868720420028165883,175330935379709733197047626722922446705536864345175489991511,550100105425539622999930710073327542890852060556265790250738,603940676370244448328058755183412273891440823490541858258745] | [111403873919411922251755536567514941816720236719390876178190,130961706859965886906262901382393102231965204974086131617838,-1058262552315692467296362535808935048549916384065817817028727,429721257382386847317356354567777634475936082875761672891770,-24746664061432332086783850852322380195410088117681904705739,732303625406539321216938168542524958041025769064438400006149,132586877388111163718482612717931519774111734691433573129640,107171574984235111584224108540428326273582627395543796507928,-792318907295062610918535145888675520478539320605323188792463,390302852708382786694280767160284236995275581053560771478868,-3560668557685164920991977613920226336809946612089571250153,21941795332638265706153089874015700253331273942026480620772] | [-2368607213823046756290889332436097518261961266026371506882065,-401971240465374186182933508206440747830486268512181683589419,493399686585139150777042387657509171025843744486748386003473,-2379714186525288392496786981777720050932577853278148713017973,-495341521993486895400653693647466077872110837635635881787967,-2979738291422745286798770528925604017582809915947774037707639,-1775116263393532844253086149857156003766869141299370615994628,-631997694015675509408202251379619056548370944676513853573832,3492140119220740219488808477130656511347148887782436025145592,-2811865968938538899073111732977930613014138548248850599850134,-248624010784461893421923788080785231083542207628095826152262,-174617616112841263796364433518694188191454302066716713586615] | [[-77182788433721292572,585263661910797993640,-418090864559631860646,-32427463342158950858,100713326683528673249,4308304856601304394,-19451651087943695975,17065113580361650216,-11270299405870928448,4315930586883090830,2605609396361630729,-1631626983154610095],[-228437089743757461646,1589481047291102625708,-1130586940937201880188,-53223829227262203451,244205370422923186217,-67436571824194497857,304470716291439363059,-267114978153597480421,176410532833964109383,-67555935036635621443,-40784803084281345731,25539355709985700909],[-1162796031647349185582,-3425728170232494625259,3223100518191791744177,133959491342214333368,-762725812377221428352,135647282832922914326,-612436608948586997783,537296306890728518014,-354846173147995623251,135887379489675539112,82037795955602168355,-51371890854631760388],[439697193195693056767,1744118502691777564287,-1550430659824102430377,-76521770743808058119,369023998261075118654,-44400208911069427238,200463384258105874247,-175868382874119158877,116148616397058926093,-44478797597079424483,-26852696220379829062,16815100446292942554],[-120824703982178891290,1118026245233817819135,-757023500663629800740,-43920847706092297744,165122397388358620408,-23630618293150833453,106690347440584236803,-93600429535274366770,61816457324646207483,-23672444655837148067,-14291505154777122153,8949309698141420670],[509377239255108122621,-717445129943248297826,404977040275328991280,-728104796691580623787,522570891576012897761,-611812780732580549165,249987402120466822025,-28802482915945559868,1341540898033039662547,-1153857861366358008746,1130746511847270490389,-864936170864726553423],[-4344992500140430821,481746498873897796753,-359487781048156256025,-136264279227619919846,175087818789315645026,-83792748427389341369,19252283318462889040,10338598644956059225,182190484681083285752,-161257009872574759247,230279543664082698287,-135819768780331038506],[-185849083476042290133,1544264500249560193132,-1107782002168407431294,-118522872725365556079,293471123771516895854,-126574170671194606599,344917371457605068693,-285418988596959778198,307761582301970569485,-175581273076877470115,234384761527740682293,-70547813045652983262],[214823922749763258308,-4075014237433941549213,2994677932713385871156,822973006116487590193,-1203678437980673472781,-586340258887979204114,-137856446068476009468,653973279765851204046,-1794817181861210084925,1222449366710304581993,-1426088096702094136594,770997774161281799790],[-149610921089954550384,2284717568958669139592,-1671448573518226175650,-407415424783427597626,629430559017161901560,323725122142161413532,23213552304021028396,-275538083758237442831,820533731910431772178,-564942869067462851966,714088968589974918729,-370377422780238504371],[-169733609208662002133,1062838957800623441516,-751586317663347430477,-4145590897299276859,136838046415854173224,77338544112101621352,93139056995500834430,-63240134008589178705,-37228558057612407814,45272528865339169999,38758763312471644338,40197437916058501081],[2922312616725017778,56660981857954340263,-43171626781940972879,-22383039141165959950,25940841897369877821,61418968386325443058,-277301719120849518543,243279365408723118580,-160668798043152711309,61527680397821575856,37145431084580567977,-23260388814663300061]] | 170125789616 | 2780497432663 | 153645111492 |
| 8 | [229969467674068906419365951086317968649378807724581388489118,529735195929630429916021680671715120328608251359091873692061,691840287097038371139028631004072998483555654559263668733000,194815305584161720017591624847844693198086498645901587625147,547330370550459747886555819995873366602557655154693276209470,437920644378683598382594783785434620474316533622624050455662,226754941031307653764596240260856016005647189885753113731584,527185868546573672112119129150710688396867592421478060124334,737447008251224043158562685214106427476632962710276345613812,175314096325260792600584666079712451977880876439841587356969,550100258790230485563433895585132346085026091403624978928022,603939729707697035077817910072800015136813041988853831428836] | [111506046049834204724587824430430137355472887714312785511039,130979045146612946406951650843458193851401618868173271166772,-1058283835062205667183679599703003977326855702970722960784927,429823908017288028569153274679033298318031379745710316958977,-24725296910062875438385298882519358084753901074835446472154,732432120109695066778131939834866630396769797399320574661457,132663455506218246206585586314013355114504230147879457466503,107198832805803166429370881948003060614714926514772910379279,-792469504498669196748717217326111260499638144696846762199665,390424137825949935167032098910847317530090727928203448222492,-3549940768778508873850652412571982170680864048242581231912,21949327144689756318621667008467088447090552423119106992340] | [-2368507941582117021218545692077906367987160834559909918594638,-401902183519077034865326579488250402300916666512483280809201,493354925698589657297913144640255718677602551216492925514349,-2379586381401340806680619192096742120230435257940487846434416,-495326442563001579964826153408397413112772485510547048164342,-2977798533480534678086314330546246850035251149381537923676580,-1775356436530588764966465680421447798010520301055474612104756,-631785696320251035170501620533857965077345847725859147424771,3490158441708438210907819670102786561214528284959936840649901,-2811404978981193581803310554636613631861428711960989664992695,-248759857827772912245969672862028168097206046043274175319446,-174587795797195067793421544433867659271877200969874833499746] | [[-77164950838714537566,585065876669720472351,-417952823839274740957,-32415200713907995859,100679310220816201351,4304381058836042990,-19432523517337501820,17048097435017588485,-11259088794335299346,4311653684436283450,2603472063077925392,-1630330077175490667],[-228378204020616489149,1588929813046090708630,-1130204028359460608021,-53203518531005000821,244121412298202072776,-67438261341993063061,304456222993186079220,-267098575728183552724,176400128661102246640,-67552204141008192495,-40789518164524268899,25542958282602276067],[-1162415952779444192545,-3424451168850154231987,3221923300740029970243,133910156263038954294,-762447139028506269183,135632500006890219758,-612325375024276657702,537191304363223778408,-354777688151105762391,135861662894258156426,82036283448575976577,-51372251011515500447],[439662391111623409131,1743713535921470738678,-1550105692311211894055,-76501750162246904969,368945799382901442552,-44408482652629693585,200486172511375721939,-175885947097825728793,116160498471959715233,-44483514640595620343,-26860132123401297611,16820184821156651694],[-120741554053710664469,1117586475544854459619,-756739194172887581410,-43904473109526926787,165061562351247309903,-23625534270944056550,106659643756989008202,-93572201136466185060,61797964570102672823,-23665451662784984359,-14289724262081382173,8948422220238094372],[509043623999973363212,-716895033349064539968,404654338325790122470,-727681549334406920311,522298736992337105238,-611532531777836321058,249881866564618819639,-28793605769904809030,1340970438544730722610,-1153385596940234714340,1130516217516562833009,-864773771176842106777],[-4340707887953121925,481574117734083360199,-359364864308621032540,-136238733637067226460,175047942465976176715,-83796082709102349233,19270669677823028782,10322712715376379270,182206395113014699080,-161268506270664390958,230318611150198174600,-135851746070615831707],[-185817195870537936971,1543742016399634336095,-1107413550120401107108,-118464238085349031070,293359881590559818641,-126547801554272200215,344880510949843398807,-285390373445276474569,307691681354184769236,-175531622608142238358,234359902975199984510,-70529872665824500462],[214944611127489655864,-4073772151201788616130,2993757513951840123727,822511037990836055147,-1203154364086179268152,-586436736304240849642,-137786303779553551555,653841445502179943397,-1794151709949176739076,1221958567095109952494,-1425841228073050818424,770826113910041444727],[-149662610899722748782,2284197454648094266447,-1671068343407973603365,-407235519151351772824,629224255193684393099,323796725366081752367,23204009170282462446,-275527031381932925951,820333456847182267473,-564786245230240687139,714049291074557238425,-370339688451337454378],[-169672217147070014963,1062419040388736311413,-751297400192328429565,-4155482661847641619,136794548511262707033,77333405193705935163,93118031332738616311,-63225578726341144860,-37199356529848168681,45245560833977922587,38773698098870438043,40185092025396784661],[2919525913371689027,56638685530139823624,-43154836654690549499,-22373723407584537095,25930723110021422671,61410582128875063319,-277243711725525187961,243225117238415575057,-160633361138289913389,61514340640403523692,37143722352758524742,-23259910712606431276]] | 170074586423 | 2780667129150 | 153545890440 |
| 9 | [229964655450060772497658248322380121417281301112680643506065,529729545531348966010970669111270572093540764070784550798535,691885938594779758150566469190421481091556968183734047454192,194796762117677997521893728830526465090175297485410766679147,547331436661219251933510477310978894444178747486707727036690,437889046788935615357213032485498204732808968896765793873033,226749216694907182693224805641317560534260325778095384623751,527181243738079738190753623609422963107200465238717635886954,737481196141736772511593143597398206479924793655377582130092,175297252039381901118764163757165326040732098610353731882370,550100411692031895331765531335059976023240677418134269436283,603938782720278669049907902427538546283261737126479647355977] | [111608213896373804405809524661349376117868141915362404570454,130996380453930707395293367102373082353782138446296670189756,-1058305115877397651284824167133455587000834781029340049348925,429926553137534276632928119832540560831956001605164417372453,-24703930409632181982168694786020966563941204570588132344633,732560531165880523080404762617092761683707647962855416742661,132740043978255498816253936363276095788449724561223454952984,107226081484222967233707719393270882196610405822953074621483,-792620016246539833223916963950299008003324169614019776159217,390545403061212124795695057552613180033039035809283033220930,-3539207122455701092699719684338915327390898383152600440598,21956857670108555177683447262818722722826633211399639497010] | [-2368408595614929822063572014996011550422287581321711546457042,-401833106652851219161859114682423070328884618552863846791174,493310142685949041716378042358065744325529530005007982514973,-2379458504714626849970605732844113420034823620633093247364504,-495311341827638614849077911360719231801771420020311881770217,-2975860077853181818627392231327100583231783549527908136607441,-1775596313691924649258562704359273232145981377847428818682978,-631573780499989509427571030972410842685684370298572575040147,3488178043925303323190820764648363424378857043054129108800080,-2810944144467896628732250215881054266439366280734664297831048,-248895584408760328250968941987728096772133247404716615116649,-174557962593153206006213334675745544408063305300851407533657] | [[-77147126634072951831,584868236200402103975,-417814884863177277703,-32402946933116643867,100645318680535939772,4300457620752358012,-19413400146250628416,17031085389474443350,-11247880844450435408,4307377774603159416,2601334451889916716,-1629032948177784761],[-228319364725033407606,1588379002731699448863,-1129821412415151141811,-53183223408435735047,244037519053875252591,-67439951035669784864,304441729405987692622,-267082172652482996580,176389724141050192108,-67548473169362082672,-40794232505926895592,25546560842839427550],[-1162036188295819142131,-3423175172275443505473,3220747016374931158361,133860860114388339476,-762168686518212103600,135617721358583749244,-612214169708827986247,537086328124287071853,-354709220450441854978,135835952900307982486,82034769777633895714,-51372610994658847225],[439627626173128709905,1743308870225649154420,-1549780972408582200792,-76481744532803070581,368867659966094432470,-44416754440425159614,200508946533665301017,-175903497792371369691,116172371756965193909,-44488228409334364788,-26867567072268550269,16825269033093246540],[-120658476308873405966,1117147051234269970898,-756455110804376792204,-43888110954358506088,165000774719459262315,-23620452840316675611,106628955116754917105,-93543986416754615807,61779480806361841886,-23658462090051357061,-14287944019317450379,8947535197666627417],[508710320518837165096,-716345550012625915080,404332010166848470930,-727258667664198370669,522026797615259863393,-611252417337693096275,249776364515522902851,-28784717549775861203,1340400241420421449388,-1152913552223509672432,1130286003089022963149,-864611421413348701766],[-4336432246034041218,481401868408321483530,-359242040939010307743,-136213200784533484658,175008092418803880474,-83799404829902288891,19289045960938963063,10306832542681365712,182222278313935629332,-161279981826562503190,230357668934178031618,-135883716507757026545],[-185785330570866121896,1543219925592010589176,-1107045377882013851316,-118405651036812350669,293248725916710363966,-126521445518402632616,344843661669156962838,-285361764617725790742,307621807163939055234,-175481992296008657430,234335048399603200578,-70511934838495179133],[215065157782742851763,-4072530864745200973715,2992837706862783654930,822049464561299098204,-1202630703449972750257,-586533134340165989111,-137716184594819128535,653709631409499688127,-1793486523848128448425,1221467990630119974026,-1425594433212865549992,770654500381576007051],[-149714260447495201761,2283677720147764807006,-1670688398725084566639,-407055758469446759222,629018113721031715776,323868305653412475573,23194466196504148297,-275515974128737271424,820133248953898882626,-564629676887546158394,714009627979169678532,-370301961143205874056],[-169610876783844439909,1061999460542110963525,-751008715554320233829,-4165363521293174301,136751083688669204682,77328269369541493686,93097013223921171312,-63211029851922616995,-37170170735297195266,45218607124629121096,38788626055521513437,40172750286739889686],[2916742668005600088,56616397348630041878,-43138053067143296299,-22364414480830791908,25920610700543360626,61402198302758991163,-277185720830879526014,243170884268074604182,-160597934220759220197,61501004684894241978,37142013235047167722,-23259432587604718821]] | 170023426251 | 2780837593261 | 153446719016 |
| 10 | [229959838818945278931438579982760365830164020395986665665512,529723894385341099559866314344885941653889854873507935377359,691931591010466959899662194472671817232954037066947047255645,194778214223525371765910505860008004281889200218075188228403,547332501850309132857148795177224882870479637318845214311648,437857443661741354384497123826509683603731834432995984209546,226743489054497636516061695447928558797277235910963121033699,527176617754360592443031384812044763357576059813365659594350,737515390523011132786705689123537839072530455711330956916838,175280402522930574308568282301390800278889139448656650188383,550100564130691293842127212018918928712171095623727714949646,603937835408044863525565136076676257615852181589095295718576] | [111710377455850616763910403751172589329999702671275763439603,131013712781060014334302262613497594709302831992012137254194,-1058326394760314068908757934056937788681526042173714698055926,430029192740038881293171938299660041822952253976577169813437,-24682564561059217456762535242952333375912208961704761416671,732688858631259593181214805215555804126408054826965692247134,132816642791458046659766423342695890584968848237991367251299,107253321023025416557273893806010011431970510736172246262761,-792770442593864210865582996243408649894776723043609494450891,390666648420872630868020876022759771094866796391735199208711,-3528467623912011518197276428648618081766895500312136422100,21964386908338755216911429468551291427104873555198724452554] | [-2368309175931432447275447062033117904543203759802606139090202,-401764009872612441113678371335354735374241474420193493299544,493265337551823741343436818557556847200898308748886391849517,-2379330556478251569254375007690767661902477707747055145292236,-495296219790167664360785564153988869372573237785632317614784,-2973922923897685406755753504784801642412564604452632800508490,-1775835894997521198334070670373903643756565564687931673888942,-631361946511551095675508949390767475483263415353502841162726,3486198925231263756624905480357709674184540221006212788950007,-2810483465301623495631292644513813316750332228314808150631898,-249031190578250764768548889742852974078721723103413732420200,-174528116503396612897868949583688505719562068480269543607679] | [[-77129315803193736221,584670740332243841980,-417677047511456992465,-32390701989484745782,100611352033384797863,4296534542521472435,-19394280975344744072,17014077444326935332,-11236675556600611670,4303102857524839295,2599196563075014772,-1627735596278206099],[-228260571801618723002,1587828615852341478640,-1129439092757844266557,-53162943841458346648,243953690614233262480,-67441640906188291591,304427235537902731813,-267065768934089847338,176379319278756760597,-67544742123560520563,-40798946108002314405,25550163390514957202],[-1161656737830897051260,-3421900179335934322355,3219571664008184012761,133811602850848554224,-761890454588753281547,135602946888867738961,-612102993009815421346,536981378181161840133,-354640770050677669471,135810249509557994499,82033254942608747906,-51372970803976711864],[439592898339369976236,1742904505250317622579,-1549456499825981220889,-76461753838055524129,368789579941020038953,-44425024275657204175,200531706334885361926,-175921034967068074706,116184236258161385783,-44492938905596031877,-26875001066335598069,16830353081852191709],[-120575470663051483231,1116707971899163430235,-756171250297843776376,-43871761226100585931,164940034437692471849,-23615374000663732061,106598281515953759284,-93515785372515606443,61761006031039862366,-23651475936729547842,-14286164426420289915,8946648630397021657],[508377328437927393597,-715796679093223716940,404010055274783493497,-726836151266954927779,521755073221146520260,-610972437383984757419,249670895990605347190,-28775818280828873164,1339830306615377554929,-1152441727173360152034,1130055868576198465098,-864449121582345951468],[-4332165562533451815,481229750734811430243,-359119310824589765496,-136187680653283029010,174968268614331027321,-83802714798585268101,19307412170666851198,10290958126845869339,182238134300248507426,-161291436553362520472,230396717016147096605,-135915680090095719549],[-185753487550173734148,1542698227374124076534,-1106677485131422101511,-118347111525400030506,293137656650868502965,-126495102561621531620,344806823619272433283,-285333162118602999383,307551959729770147516,-175432382138115343845,234310197801886453310,-70493999564599004840],[215185562888736913154,-4071290377255266099992,2991918510820762195219,821588285380229205291,-1202107455617517088908,-586629453033663293880,-137646088531145050639,653577837521476685565,-1792821623520028234847,1220977637274177316378,-1425347712133118965797,770482933584243112993],[-149765869777383496780,2283158365017554235232,-1670308739139994572728,-406876142570978420918,628812134412501985377,323939863005651586949,23184923391120129883,-275504912008929847918,819933108232782291120,-564473164038029979820,713969979305274547757,-370264240857907077480],[-169549588057641382674,1061580217860002334052,-750720263473004250196,-4175233487388748658,136707651907723440453,77323136636472194372,93076002670240818773,-63196487384955538726,-37141000668983057475,45191667733094898713,38803547181878967697,40160412700809589866],[2913962877211032982,56594117302662281434,-43121276010635727829,-22355112352990984079,25910504661312674989,61393816908449989274,-277127746440176441483,243116666500761939731,-160562517292538596881,61487672532028212782,37140303731586360959,-23258954439738785977]] | 169972309062 | 2781008825113 | 153347597248 |
| 11 | [229955017780907424718399238864062683279730646170439425195380,529718242491735405052726134772160529286476234029955981683395,691977244344016603510732410217487347142038815745970668595890,194759661901941927348673294994556940202887078714341093949263,547333566117757529569780550970715440035399243027715859821350,437825835000705449279861513107424065883751614881362983159491,226737758109633205087038697319520932447940465382745350904763,527171990595810413115707779514445342899656313993585308151282,737549591391364402667948788943367655076389961611923558692126,175263547776764038659040547689753906863566132310020412477178,550100716105956346692038271316856601705371361289851980421668,603936887771051155763614971788738998838298814099068623111712] | [111812536725084966565266316338298597167005797504237843902995,131031042127141966930728472100403426468003377502772505398578,-1058347671710000768131957549095008429158784771071943548972510,430131826821715697838256389471626843459591436292983843871004,-24661199365262828068123278711769542137941572239214176666106,732817102561968434397969472133551204547663724091932862640102,132893251933066192196753043923321724346650248914222497092978,107280551425739546730556523287691757204728672028096281182472,-792920783595804400871757778916778135809350093128319293408272,390787873911630541975826772937169661037435753886814331852299,-3517722278340516800761497039541789913916867647786364028226,21971914858824565051397279295593510288402179755470890028973] | [-2368209682541581602460445885750912723579916276374403440990754,-401694893184279135281876513040898075509450061331195868298512,493220510300822988376816361663412387688700067579503679365382,-2379202536705328974986284173295847697885408115945712360688657,-495281076453361084471827501665658242548651113865428266548277,-2971987070970641860451059102556580320080108431420709635683959,-1776075180567440507639791656667206985445466020667592265225232,-631150194311564217968059683949736225176757482652116434224487,3484221084985847616428557590137533708152087211481429807641726,-2810022941385286554468312051922546832197738144303290678254367,-249166676387107416886919306409607133322496340763999425146390,-174498257530607819197459344124287610715943025885983388954394] | [[-77111518329499773818,584473388894911172673,-417539311664417200097,-32378465872728156584,100577410250105126984,4292611824314200475,-19375166005278305524,16997073600166758078,-11225472931168129268,4298828933341701219,2597058396910697515,-1626438021593506449],[-228201825195068893727,1587278651913198017454,-1129057069041647934546,-53142679812004835116,243869926903684033379,-67443330954510211442,304412741396976050849,-267049364580585472206,176368914079162442369,-67541011005463571221,-40803658970263644213,25553765925446669461],[-1161277601019667820805,-3420626188861015778644,3218397242553164042527,133762384427076047396,-761612442982943383343,135588176598601502014,-611991844934779074124,536876454541059609543,-354572336956466054168,135784552723733246280,82031738943333385547,-51373330439383999312],[439558207569571253104,1742500440642029843133,-1549132274273626553250,-76441778060610247721,368711559238152118022,-44433292159526117874,200554451924939580211,-175938558631221344346,116196091981630025797,-44497646131679353920,-26882434104956491165,16835436967182947082],[-120492537031760139455,1116269237137258509718,-755887612393438399051,-43855423910289204505,164879341450730701015,-23610297751379537943,106567622950652349487,-93487598000120466544,61742540241749848395,-23644493201911693493,-14284385483324762043,8945762518399238063],[508044647384030199795,-715248419751520139318,403688473126738869696,-726413999729273097739,521483563586664234216,-610692591888454451833,249565461007222558686,-28766907988296619326,1339260634084671884602,-1151970121746813831240,1129825813989564841752,-864286871691885022261],[-4327907825615254165,481057764552004311340,-358996673850804617054,-136162173226613951743,174928471019148194186,-83806012623948574783,19325768309867745939,10275089467840578471,182253963088361303078,-161302870464161858919,230435755396242219937,-135947636815981711879],[-185721666781651304327,1542176921294108715004,-1106309871547298724377,-118288619496837297445,293026673694084600710,-126468772681955039079,344769996803900138572,-285304565952190585628,307482139050191382348,-175382792132085277742,234285351182980252109,-70476066845066071857],[215305826618438811881,-4070050687924257463037,2990999925201238312455,821127500000627654537,-1201584620134935183017,-586725692422675935853,-137576015605342281344,653446063871702501616,-1792157008926618098110,1220487506985969914014,-1425101064845319778086,770311413526352105827],[-149817438933435096880,2282639388818017336157,-1669929364323648210106,-406696671289463387093,628606317081676353502,324011397424318061311,23175380762546971972,-275493845032774772568,819733034685967052890,-564316706680294184043,713930345054322226907,-370226527597495682977],[-169488350907210236730,1061161311942289814416,-750432043672492881054,-4185092571872644356,136664253128141049976,77318006991361610113,93054999672883672837,-63181951325057839203,-37111846325920244916,45164742655169151770,38818461477402622927,40148079268323692808],[2911186537577607338,56571845381490490939,-43104505476517691434,-22345817016163657755,25900404984718161552,61385437946418494376,-277069788556663368818,243062463939523962250,-160527110355595952758,61474344182536114208,37138593842515994267,-23258476269089275342]] | 169921234814 | 2781180824823 | 153248525170 |
| 12 | [229950192336132346008162643683938014715517785320811949190518,529712589850660494024319680554216856464186278574095890370534,692022898595345274953367653547465285229200517447151478617579,194741105153165881983593386447206744457122004255836314244803,547334629463592620617272939871776110370706450541280041082947,437794220809430112920058168649246517737996125714313516579465,226732023859868628561608932212772855239803390447401388957732,527167362262823226264536710644652632592757205546856428027041,737583798743116239761747803061079715103794058882128902922462,175246687801739231771945326369583997872441161306013982340928,550100867617574943444690163644000003611946200685570328586235,603935939809353106995480105166660521891650728597930634406083] | [111914691700897608280301064430139913409607404295277123480770,131048368491317920252899291295352061683317775456770522591106,-1058368946725503795918948165665391717334328423529880766226601,430234455379479147447012840584609414876545249832208452684378,-24639834823161740373444367241061797631687617258847154007642,732945263014115441003618794035808867081522578083812795774552,132969871390325418736756913360951319698324365712158315537776,107307772695892518489194045332972539949598563663550396989704,-793071039307494837906914443016821529095655110257022664406637,390909079540180757302151013659876257498971189864982609928530,-3506971090932098726868685889855849554688948311316444719403,21979441521010309046594573243288184033364248482185750612337] | [-2368110115455343407381929219543994973902442837583515324783465,-401625756593772467306175523594216115444063852439143225295571,493175660937558808552675215599902669402935681075061745254213,-2379074445408982037431415854677491632817659454570239763084300,-495265911819993921938965840202741157495877713959853103305939,-2970052518428247574583481058845273245972632604063188019303333,-1776314170521825671530061023263544085950277201366138997059738,-630938523856625739038969890990960172325601736149653037878534,3482244522548185168933238942802249288100015789604194733444313,-2809562572621735482350848922478284735901623292594869985624063,-249302041886229871222089119804899118740726961480589966119421,-174468385677470951220594932191287799809756096244706833545184] | [[-77093734196439580264,584276181718333602672,-417401677202546648719,-32366238572578704304,100543493301484632451,4288689466300948446,-19356055236706563902,16980073857582583897,-11214272968533319065,4294556002193382265,2594919953674510733,-1625140224240475616],[-228143124850166164137,1586729110420217382897,-1128675340921206224540,-53122431302035204539,243786227846752662865,-67445021181595174771,304398246991238844679,-267032959599538584502,176358508547199412492,-67537279816928139718,-40808371092224034253,25557368447452371388],[-1160898777497687137036,-3419353199681890668559,3217223750924930293043,133713204797797515010,-761334651443994446088,135573410488639436454,-611880725491224784117,536771557211160042150,-354503921172438970843,135758862544550881013,82030221779640691344,-51373689900795608335],[439523553823019491084,1742096676047887341393,-1548808295462184653861,-76421817183100184031,368633597788072222046,-44441558093231103167,200577183313724556745,-175956068794130186678,116207938933448560306,-44502350089881421537,-26889866187485318935,16840520688834967847],[-120409675330645240129,1115830846546902266032,-755604196831713265316,-43839098992482844325,164818695703443314429,-23605224091857677916,106536979416912535320,-93459424295935880734,61724083436101888994,-23637513884688789135,-14282607189965626165,8944876861643196733],[507712276984488992973,-714700771149545649053,403367263200720838316,-725992212638344855450,521212268488781441013,-610412880822754834936,249460059582661197472,-28757986697374532103,1338691223783184907445,-1151498735900749189878,1129595839340525636654,-864124671749968715156],[-4323659023456969598,480885909698602608353,-358874129903279259055,-136136678487858024902,174888699599904142616,-83809298314790657401,19344114381407577902,10259226565632027459,182269764694687481750,-161314283572061892621,230474784074612253807,-135979586683773494947],[-185689868238532915535,1541656006900795856496,-1105942536808812052019,-118230174896929938816,292915776947559128726,-126442455877419833851,344733181226734089933,-285275976122758265754,307412345123692763709,-175333222275525839842,234260508543809502584,-70458136680822589623],[215425949144568848937,-4068811795945632193351,2990081949380589624043,820667107976143330661,-1201062196549008434068,-586821852545181438509,-137505965834160545049,653314310493694121112,-1791492680029419551347,1219997599724031366564,-1424854491360904898980,770139940216164127220],[-149868967959633455500,2282120791110388874928,-1669550273947498156145,-406517344458668578457,628400661542418467369,324082908910951796073,23165838319183784419,-275482773210520926814,819533028315521748906,-564160304812892225972,713890725227751189836,-370188821364017627393],[-169427165271393506955,1060742742389476044887,-750144055877328690850,-4194940786468569605,136620887309703398666,77312880431072997020,93034004233029651232,-63167421671843440739,-37082707701114195939,45137831886637565037,38833368941558016493,40135749989996046496],[2908413645700269985,56549581574385249066,-43087741456152341442,-22336528462459617734,25890311663160405705,61377061417132621207,-277011847183571295663,243008276587391724613,-160491713411889158074,61461019637144826759,37136883567975983208,-23257998075736848826]] | 169870203469 | 2781353592509 | 153149502810 |
| 13 | [229945362484805316083736498951392245876509238900676338243258,529706936462245015043150497175701678927865037960878285708584,692068553764369519050914399375227166624572933011667832703071,194722543977435586474042950606045275873402772327956839123929,547335691887842624173886800034833430568825337379407630229260,437762601091515138441158538179456412174059865926816819576547,226726286304759197173186032664246633231570814336082002567847,527162732755792905835034646473756067751407931760762695293115,737618012574588679404382331928042527136919689437154089888732,175229822598712802542543964306907653118008985115458094138999,550101018665295197534233128904041494411886606568011924836258,603934991523006302420185975493768021638772552262269872956966] | [112016842380109726489518800430630745097856310695441530071244,131065691872729484848498225084795137350464442867290300780502,-1058390219805869398242778815363105650505612369053384387793925,430337078410244217575149385869267076727316926738942017276761,-24618470935674561165103208701360048801157228885060197643095,733073340043781227019508989948269488879173639918041067699855,133046501150486393924761704861068677631781438492082443665126,107334984837009619616354637185768487298181002828141895959396,-793221209784042302989007904247590248293073556931582547312937,391030265313213983925166594020405374747893456016824681227034,-3496214066875442653117169590541965632435428496016635978787,21986966894340427387132726108120260834311843835017149590325] | [-2368010474682693392957939140474273676010428418626610806585563,-401556600107016332462833746170641220724741757975970993595135,493130789466646019796495914303021974313000421012632828084069,-2378946282602342682907006722281987380873453359037225352120073,-495250725892843913423465238002219966305270261418462383821304,-2968119265626301173047148441564122278633035785380588161285259,-1776552864980900388815109637475226444781046522106359525107834,-630726935103301138021419357876481338723141632343284256436868,3480269237277011092653312835522812054921997472205939805867451,-2809102358913757649581016123029369524476792918904052638269113,-249437287126553926090668747083618067606502604417887713233578,-174438500946671730189594844859292783751586731177243263303608] | [[-77075963387487254210,584079118632704147583,-417264144006519160538,-32354020078784159078,100509601158356285673,4284767468651715605,-19336948670281570678,16963078217160069287,-11203075669074545286,4290284064218779830,2592781233644067989,-1623842204335941416],[-228084470711778398504,1586179990880113504962,-1128293908051698303365,-53102198293537409339,243702593368081188209,-67446711588400816352,304383752328708664510,-267016553998505257907,176348102687791540204,-67533548559807974694,-40813082473396664219,25560970956349872705],[-1160520266901075375621,-3418081210631571971549,3216051188040222085052,133664063917809764176,-761057079715516191853,135558648559831033282,-611769634686624174427,536666686198610987018,-354435522703207528357,135733178973720143988,82028703451363578376,-51374049188126431539],[439488937059064424400,1741693211115538406897,-1548484563102769966283,-76401871188185184059,368555695521469391106,-44449822077970274463,200599900511129817992,-175973565465087117524,116219777119690147223,-44507050782497683722,-26897297313276210092,16845604246557704524],[-120326885475483020181,1115392799727063933042,-755321003353622940125,-43822786458262388748,164758097140785113001,-23600153021491011244,106506350910791211094,-93431264256323921576,61705635611703056524,-23630537984150691412,-14280829546277539855,8943991660098776905],[507380216867203415378,-714153732450696365034,403046424975596537723,-725570789581956562676,520941187704767322012,-610133304158448313167,249354691734138301233,-28749054433220742254,1338122075665605205746,-1151027569591895901530,1129365944640412555893,-863962521764551547045],[-4319419144249723892,480714186013559697448,-358751678867816932275,-136111196420380622707,174848954323305697768,-83812571879911105374,19362450388157140035,10243369420182605180,182285539135645961682,-161325675890167920114,230513803051418030960,-136011529691838236053],[-185658091894096114729,1541135483743712933564,-1105575480595624920532,-118171777671564152006,292804966312642378159,-126416152146023154736,344696376891452008218,-285247392634563005835,307342577948741014685,-175283672566028848366,234235669885293516158,-70440209072790889192],[215545930639601078022,-4067573700514028761853,2989164582736107013352,820207108861071542039,-1200540184407175522417,-586917933439191528228,-137435939234288434645,653182577420894048092,-1790828636789734155702,1219507915446741338684,-1424607991691239562474,769968513661892198493],[-149920456899898131043,2281602571456582268982,-1669171467683504187118,-406338161912610734778,628195167608873930874,324154397467113562893,23156296069412246391,-275471696552401972243,819333089123449115568,-564003958434329086402,713851119826988024352,-370151122159510180357],[-169366031089126633673,1060324508802685710995,-749856299812483574620,-4204778142885683732,136577554412257450475,77307756952469302200,93013016351852484049,-63152898424922266435,-37053584789561326632,45110935423277636976,38848269573816391371,40123424866536545760],[2905644198179284569,56527325870633732389,-43070983940916113422,-22327246684001905704,25880224689051759609,61368687321058166502,-276953922324114790337,242954104447380977551,-160456326463366060758,61447698896577439683,37135172908106269066,-23257519859762187633]] | 169819214985 | 2781527128289 | 153050530200 |
| 14 | [229940528227111745342951442669533831196099229826131889560315,529701282326617653700433009730754810369150650523820288841604,692114209851005839489062260111041285985784905914761407181502,194703978374989524688919301736452009172132400380133522249515,547336753390535798037107832415169778002563203726219360047419,437730975850557900437275683647752968720996373532376376967713,226720545443860751009433333074770017172590657913229638026853,527158102075113173743303048090806830224281729280655100096826,737652232882106133468727458002185876750569263584276832738311,175212952168541111340486865956919649781760044808102186555862,550101169248865446170995474866231466369291598061596912755138,603934042912066351199363206795843914349915640452960004740523] | [112118988759542936289406857811455835559277686183907323640195,131083012270518526862281811499357747887732177598079084041191,-1058411490950144020205439567572365639681977376436867067222277,430439695910926462341505677386668692546828446682018432740723,-24597107703719777354646152344888034234006423998039388506539,733201333707018609105275880599135075630678428153241929103876,133123141200804973209722705784078649665279865165214087704029,107362187852614263592772213736779281824410805386712951285740,-793371295080525906473519944400556596697270561853664458239507,391151431237416734138815257815094995040516202950182868234994,-3485451211357035948039718111254813248084972968105640246771,21994490978259476145601583456489979465739689100938703982733] | [-2367910760233616498256102703606309115597774889903969307672175,-401487423729937354221774748182398616568885787147022201448527,493085895892702230873165859064919158558612636127879360134803,-2378818048298551790021309937495968771687239523811960499521263,-495235518674691484609949082854149378210114950720237976768216,-2966187311920205755789766501677551595003411966383226998181555,-1776791264064968569191098568449235067695362689052031214291544,-630515428008124687765098957978110608132706006832977413339580,3478295228530666724251630129727515798261793779128308322347930,-2808642300164078506823425578120510240919753043132611482890748,-249572412159051412083686406228554907047516593292122623623343,-174408603340897471553228155857233848973644518768755124452879] | [[-77058205886142427878,583882199468478821859,-417126711957193273515,-32341810381108202264,100475733791598236507,4280845831536095007,-19317846306652183611,16946086679481860453,-11191881033168209133,4286013119556053011,2590642237097050565,-1622543961996769661],[-228025862724858915337,1585631292800364443796,-1127912770088837389934,-53081980768527300141,243619023392428359955,-67448402175882777657,304369257417389433178,-267000147785028940701,176337696505854398258,-67529817235953671908,-40817793113294744354,25564573451956985822],[-1160142068866516508177,-3416810220544879347476,3214879552817455761279,133614961741979577338,-760779727541515257679,135543890813020884449,-611658572528414706827,536561841510528531367,-354367141553362016224,135707502012942395333,82027183958334990154,-51374408301291355383],[439454357237118449260,1741290045493177034766,-1548161076906944054179,-76381940058551955005,368477852369139944844,-44458084114940658218,200622603527037816268,-175991048653378160672,116231606546423656171,-44511748211821947901,-26904727481683332796,16850687640100603008],[-120244167382179831702,1114955096277333717179,-755038031700523170020,-43806486293231078598,164697545707796168508,-23595084539671673783,106475737428340331667,-93403117877642062440,61687196766157415114,-23623565499386121684,-14279052552195058886,8943106913735816964],[507048466660628319279,-713607302819731443062,402725957931092349898,-725149730148487888549,520670321012191273629,-609853861867007286531,249249357478801408527,-28740111220956119234,1337553189686429963845,-1150556622776835224919,1129136129900485589870,-863800421743539831844],[-4315188176198230866,480542593336079374602,-358629320630399381167,-136085727007580644092,174809235156117627697,-83815833328110629548,19380776332992072099,10227518031450563516,182301286427661071026,-161337047431589130914,230552812326832343446,-136043465838551764036],[-185626337721661824292,1540615351373082108137,-1105208702587893710824,-118113427766706394380,292694241690834173627,-126389861485762823380,344659583801715350711,-285218815491849040389,307272837523779628801,-175234143001170595879,234210835208346019656,-70422284021889429681],[215665771275763728191,-4066336400825264663470,2988247824645992850407,819747502210352840449,-1200018583257531186395,-587013935142751985902,-137365935822353518952,653050864686670406017,-1790164879168644054155,1219018454112325959270,-1424361565847617446294,769797133871701301793],[-149971905798084901187,2281084729419188263337,-1668792945204132190518,-406159123485555943496,627989835095469766887,324225863094384959405,23146754021596630567,-275460615068636366424,819133217111686178920,-563847667543061375467,713811528853447453114,-370113429986001958519],[-169304948299437817103,1059906610783664342724,-749568775203357928440,-4214604652818619713,136534254395715636948,77302636552413171497,92992036030519722512,-63138381583900247800,-37024477586249059766,45084053260858704949,38863163373654686498,40111103898651138744],[2902878191620221192,56505078259539683323,-43054232922198698496,-22317971672925776553,25870144054816319412,61360315658658612952,-276896013981492029300,242899947522492195154,-160420949511964503153,61434381961553257321,37133461863046818821,-23257041621245992257]] | 169768269323 | 2781701432282 | 152951607370 |
| 15 | [229935689563237181279881187462609415831873379291944013473522,529695627443907132599064330617823598124821236365141846851756,692159866855170698824436378532063320803783168519645008656568,194685408346066313538192503363964974351652893945129978433148,547337813971700439622472816892175668697868787674325982737075,437699345090153356160022403225213307290920389518992986512282,226714801276729679788403804366804746571599243219029739968059,527153470221177599956908865232055156583281199472637151344372,737686459661995389170263060540912677913911067340382241507116,175196076512080230190820792718387246397986086439285740743167,550101319368034250246635811040037735429403015616553093013954,603933093976588886452247082385081472349425727763517733114120] | [112221130836019283698208893337993340501308807099482986042141,131100329683827168153734188016996879784570362041793116039777,-1058432760157374306158220440320940824131604483984036056610663,430542307878442002914145456899026523386874025407570226990049,-24575745128215755856811490580054206397222976055726780329909,733329244059852589545558147883862485019319309969270769975422,133199791528542203296139495982679908782861785000278051471747,107389381746227988254422659083195821986621401421165060521457,-793521295251997071134278228870885293871440904222640499508040,391272577319471322790123613946870646837341299700299787304590,-3474682529561166441647208612797637564673186413216177888618,22002013772212127351306660646272991535773652289643534732701] | [-2367810972118107067485845246951102046520730641144635991376132,-401418227468464882802939212824457426455044977297600795097757,493040980220347840036247452250945457823209323987172265646994,-2378689742510759185909893474592824215794599167678894825775199,-495220290168319749324493542044219931618728370331927661425456,-2964256656664971140745736032808297510363576167764050139316761,-1777029367894413940550561074916404900690498488900175079374073,-630304002527599631751508716465509808367688035736668904125879,3476322495667102299408105864868464498009643658629836386542451,-2808182396275361971387404030970213911549679965976830264173173,-249707417034730013040846594656972603329625538380005293906052,-174378692862837084306027432727546852298465051867763392335838] | [[-77040461675930217736,583685424056376129838,-416989380935611883853,-32329609469330395632,100441891172133725810,4276924555123274350,-19298748146464072689,16929099245127598822,-11180689061188752411,4281743168342623971,2588502964311207407,-1621245497339864143],[-227967300834446322109,1585083015689210910896,-1127531926688869721656,-53061778709048569767,243535517844669416021,-67450092944994709119,304354762265271460503,-266983740966640470006,176327290006295272278,-67526085847212677786,-40822503011431515537,25568175934091525868],[-1159764183031257011352,-3415540228258435639935,3213708844176721440616,133565898225243576834,-760502594666394427348,135529137249048690846,-611547539023999736802,536457023153997051685,-354298777727471938152,135681831663911122732,82025663300387900680,-51374767240205260201],[439419814316656502469,1740887178829541869525,-1547837836586714735842,-76362023776914008264,368400068261987274789,-44466344205338193039,200645292371323930023,-176008518368282848102,116243427219713668641,-44516442380146379999,-26912156692060894758,16855770869213104599],[-120161520966771892258,1114517735797921595630,-754755281614170106660,-43790198483014468881,164637041349601658545,-23590018645791079969,106445138965606926249,-93374985156243190348,61668766897066029086,-23616596429482669214,-14277276207652637260,8942222622524114454],[506717025993772746313,-713061481422770466587,402405861547792248183,-724729033926910732512,520399668188922377986,-609574553919814390751,249144056833728681959,-28731157085664311525,1336984565799965456168,-1150085895412000394669,1128906395131933134925,-863638371694791761564],[-4310966107520775998,480371131505615381850,-358507055077186514161,-136060270232890435448,174769542065162522914,-83819082668191042701,19399092218792845179,10211672399390025831,182317006587162505074,-161348398209438572140,230591811901039921405,-136075395122298554937],[-185594605694594253805,1540095609339818923403,-1104842202466267391670,-118055125128403233555,292583602983783587715,-126363583894627267138,344622801961169337898,-285190244698847890998,307203123847228921270,-175184633578511886090,234186004513875164894,-70404361529032804701],[215785471225039625607,-4065099896076334106313,2987331674489359216857,819288287579571843480,-1199497392648825004226,-587109857693942498850,-137295955614922450046,652919172324317037904,-1789501407127012504528,1218529215678858220034,-1424115213841260793619,769625800853708461175],[-150023314697985876949,2280567264561473608995,-1668414706182353179703,-405980229012019169419,627784663816913880804,324297305794368361007,23137212184083827332,-275449528769427378738,818933412282104388686,-563691432137497435953,713771952308532354492,-370075744845512939779],[-169243916841447842198,1059489047934777116479,-749281481775779821791,-4224420327947506661,136490987220055726585,77297519227766957231,92971063270192747738,-63123871148379332348,-36995386086155853683,45057185395141970379,38878050340555527144,40098787087041833367],[2900115622633946080,56482838730423378147,-43037488391403017715,-22308703421378674717,25860069752889902523,61351946430395133175,-276838122158884824579,242845805815710600344,-160385582559612338731,61421068832787805444,37131750432937625120,-23256563360268982473]] | 169717366443 | 2781876504607 | 152852734350 |
| 16 | [229930846493367308466245160724181948937660220196219243754921,529689971814242211342590993329646675194329889170116446018663,692205524776780518493195011299772709120750026412532275651104,194666833890904702948436322341229725232610978968804607459099,547338873631364885958390826330139838914956866551761204787213,437667708813894046718701168722461661008213939070860231027020,226709053802922922634531463727194407969329614776055749998262,527148837194379602575822771262491737029926894991485345031455,737720692910585607872355373411050363587076541009067661885596,175179195630185942955110662082303667111087484958414298717933,550101469022550394239228567176593257470001304433139845550894,603932144716629565250674054152547744579140266019120758183501] | [112323268606361246061568224834287679936595205164347054736934,131117644111797786414659366678274309496229068979351596610693,-1058454027426607099822012027419428040169005361147579077859942,430644914309707527896286678210344585380900533705832014473570,-24554383210080743473590519826329410007388147049736638411789,733457071158280339333310751507907913542420631015615756218949,133276452120964325578708198986115775945927037963881481874702,107416566521370454457822972586946042568795051399275514673882,-793671210353479515340829549342625423145682723215240566729966,391393703566055864633163173779367759149539345427308357467845,-3463908026669920882686270508173127729411391979985056614839,22009535275643169058995009956376742909543474274325686510361] | [-2367711110346168846987915067451374358982683164693420683932163,-401349011328530993731860558678617123882275041758477827399892,492996042454206033676438201327707627772956308868260044201329,-2378561365252123642469376328349298501962891700864750127109374,-495205040376514508651959965184920040696204366591405970270084,-2962327299215216100680100263047063204567870150281640757400289,-1777267176589699657171986647254894963099283370229118343821552,-630092658618198360608048964147076602388498074847609897575500,3474351038043879188598614434577650307771169270813277241025941,-2807722647150210812624766475831716379194765732025111209365657,-249842301804633087424658904399988980589535022739584279364523,-174348769515181070307174972336663909957000732514725416895162] | [[-77022730740401175297,583488792227376557976,-416852150823001889327,-32317417333246150632,100408073270930998191,4273003639582036822,-19279654190359726051,16912115914673926548,-11169499753508661137,4277474210715179318,2586363415564355065,-1619946810482166608],[-227908784985664350351,1584535159055654793743,-1127151377508573523259,-53041592097172699356,243452076649795856332,-67451783896688272409,304340266880331458638,-266967333550858086005,176316883194013170097,-67522354395429292968,-40827212167320249379,25571778402571310723],[-1159386609033104778445,-3414271232610663387702,3212539061039779779841,133516873322608089773,-760225680834951864954,135514387868749270284,-611436534180748568534,536352231136069264782,-354230431230086045536,135656167928311954126,82024141477355314509,-51375126004783020214],[439385308257215940333,1740484610773915151373,-1547514841854535220749,-76342122326011607551,368322343131021637172,-44474602350357729785,200667967053856464137,-176025974619074220218,116255239145620478164,-44521133289761504515,-26919584943763143353,16860853933644646038],[-120078946145425033792,1114080717889656117312,-754472752836719532147,-43773923013260385607,164576584011411701873,-23584955339239924802,106414555518633112197,-93346866088475618806,61650346002026971358,-23609630773526794352,-14275500512584627233,8941338786433426091],[506385894496198909130,-712516267427290843299,402086135307136148743,-724308700506788149682,520129229013128874756,-609295380288162739022,249038789815929031214,-28722192052391786963,1336416203960327534488,-1149615387453677011431,1128676740345872114836,-863476371626117487283],[-4306752926449200069,480199800361870934594,-358384882094516064736,-136034826079775713553,174729875017320676246,-83822319908955240107,19417398048444746226,10195832523950995428,182332699630585283569,-161359728236833115197,230630801774237411864,-136107317541471717685],[-185562895786300812043,1539576257195530958841,-1104475979911886565001,-117996869702781198009,292473050093288656141,-126337319370595541907,344586031373442980214,-285161680259778384925,307133436917486080175,-175135144295598070593,234161177802783538247,-70386441595131748790],[215905030659166614399,-4063864185465405706419,2986416131646226135177,818829464524956059610,-1198976612130460178745,-587205701130876513016,-137225998628501070455,652787500367053606396,-1788838220625484411678,1218040200104258373445,-1423868935683320534671,769454514615982823593],[-150074683643329616486,2280050176447379744445,-1668036750291642310838,-405801478326763785505,627579653588194525326,324368725568686872739,23127670565203368937,-275438437664963106208,818733674636509752120,-563535252215997446458,713732390193633783421,-370038066740054477498],[-169182936654369903893,1059071819859007659820,-748994419256004171845,-4234225179937992260,136447752845320694509,77292404975392725902,92950098072026779491,-63109367117957491196,-36966310284251231141,45030331821880523872,38892930474007215287,40086474432406703770],[2897356487836611268,56460607272621595093,-43020750339945196488,-22299441921520210598,25850001775720024935,61343579636726593678,-276780246859458651163,242791679330006190322,-160350225608227448783,61407759510992837580,37130038617918706255,-23256085076911897324]] | 169666506305 | 2782052345384 | 152753911170 |
| 17 | [229925999017687948532793649388308750815346191499750303742327,529684315437751686524170615026175090703856095494946880418049,692251183615751678819632300610675057742411547959371885159018,194648255009743575838342538607250208170891126742328121663169,547339932369557513680959440219034708487020731257798659794102,437636067025370098281221716132321825363137671962890480720215,226703303021997967854474988511786313509411772996706980820707,527144202995112447913414808854221414015560228014334790393128,737754932624208323890814946228533917642714905252416935524002,175162309523713745512675130330866737385496652119863164201013,550101618212162886118283128781979683316283943504181008097141,603931195132244068614075287876562336828762512030460043413139] | [112425402067391732458041248544748209122719133070416782416017,131134955553573015286711184542945864866035626679969934217332,-1058475292756889444407547806958714042708493344095052915596804,430747515201640293712069109498779773830474471828520663272965,-24533021950232866778326693293985555119217871585161059735496,733584815058271181349499129944446295868075861292265468648560,133353122965342779560091202166411718171683589327067247893654,107443742181559444752936034985031990241941581995342523083319,-793821040439969236332147896840709424570659763837662746975245,391514809983844271699616184005346354780621584189807150587524,-3453127707863183403593674936710277619545475919209867228406,22017055487997505417551697398978406529469799526722391780595] | [-2367611174927814982221221169765428870134349570880945372173514,-401279775316070486394464989102223058113839133147211404383877,492951082598902784969221507537997295164044876501389514581411,-2378432916535812872588604617811388679661901223191953821666292,-495189769302064250052566130876383383692557764024326899233097,-2960399238925170594950646860283547906947902269213484421429654,-1777504690271367908787281810740430684995354166317205216472655,-629881396236362588221477591222684547195289164306035320223829,3472380855018172127791531649362987400042120221069315670356622,-2807263052691167036444415904181504805287581787150402768362556,-249977066519839490093865309336343616376222447036189097828075,-174318833300621523598962079601788800506656693125635242653835] | [[-77005013063131238018,583292303812722068246,-416715021500773833431,-32305233962666697724,100374280059003214974,4269083085080761952,-19260564438978455919,16895136688694492012,-11158313110498469153,4273206246809671469,2584223591134377645,-1618647901540656747],[-227850315123721691135,1583987722409457683850,-1126771122205257977999,-53021420914998904606,243368699732915217972,-67453475031913142696,304325771270532557413,-266950925545187446173,176306476073898831098,-67518622882444675848,-40831920580474248308,25575380857214161051],[-1159009346510428033555,-3413003232441781344270,3211370202330058742857,133467886989149013220,-759948985792380350239,135499642672952565465,-611325558005996509832,536247465463766278795,-354162102065732370930,135630510807822670401,82022618489070266806,-51375484594939503552],[439350839018396417840,1740082340976121664894,-1547192092423303248100,-76322235688611717135,368244676907359946218,-44482858551193031677,200690627584496650230,-176043417415018826103,116267042330200090489,-44525820942956204590,-26927012236144365731,16865936833144659541],[-119996442834434452100,1113644042153983206631,-754190445110726086156,-43757659869638882716,164516173638521194133,-23579894619408185818,106383987083456108783,-93318760670683100609,61631934078635331835,-23602668530603831709,-14273725466925279349,8940455405433467766],[506055071798021175307,-711971660002125207555,401766778691418265714,-723888729478273278638,519859003263277634209,-609016340943256163370,248933556442342235957,-28713216146147873056,1335848104121442114416,-1149145098858003431381,1128447165553348102170,-863314421545279200026],[-4302548621228882825,480028599744798249986,-358262801568903253254,-136009394531735488694,174690233979529962968,-83825545059207180131,19435693824837862610,10179998405079364005,182348365574369708123,-161371037526893422543,230669781946633357570,-136139233094472979788],[-185531207970232019172,1539057294492516488389,-1104110034606382513419,-117938661436046628036,292362582921296093580,-126311067911637354927,344549272042149104761,-285133122178846673699,307063776732925217577,-175085675149959085553,234136355075968170215,-70368524221093143835],[216024449749637976621,-4062629268191820188049,2985501195497519802131,818371032603374715930,-1198456241252492324905,-587301465491701085466,-137156064879534520239,652655848848025693759,-1788175319624486858866,1217551407346294330030,-1423622731384876408163,769283275166545739802],[-150126012677781238661,2279533464641521480257,-1667659077205977902147,-405622871264801104709,627374804224579766489,324440122418984281225,23118129173267453652,-275427341765416489321,818534004176642967676,-563379127776873524415,713692842510130992209,-370000395671629314692],[-169122007677509432752,1058654926159956858951,-748707587370711919641,-4244019220441265156,136404551231618592442,77287293792152265887,92929140437170884932,-63094869492228726651,-36937250175495808100,45003492536819370294,38907803773503719997,40074165935439896763],[2894600783849644315,56438383875487582511,-43004018759254539079,-22290187165522137026,25839940115765878607,61335215278109558808,-276722388086362674377,242737568068333761982,-160314878659717759100,61394453996876341341,37128326418130106133,-23255606771255495113]] | 169615688870 | 2782228954734 | 152655137860 |
| 18 | [229921147136385060150675454930576799494277384551533742724038,529678658314564391715528490579642092987569567732417521599947,692296843372000519024786231463834892423156246974328393358853,194629671702821948094218617651925213445756130104339158451802,547340990186306739028775959539171174622199534832504507307829,437604419728169223275742136458663182691762688627392856105354,226697548933512852712814261754879170965592061080639003921662,527139567623769250577507118651692320726973340258762963708478,737789178799197443297735159683328685135718915367618771347502,175145418193518845941935243286258013743611295069583621346053,550101766936620957249696921284384284243147002687485702817177,603930245223488101504467245815195101606488554469058933959899] | [112527531215934084104480820223706534972980538828128565619022,131152264008295744478860896047346917679431571585098024746104,-1058496556147268582735588096269719345229829942962993219589770,430850110551158124992159305249266549200043619379533935762539,-24511661349590131999852898511984855306065230948103467260402,733712475815766573638955128937809790724000450560005675564250,133429804048954206251842187439926434834415632933827978616138,107470908730310862063663724824116788097320220499464060576964,-793970785566434493586458286473214629043631360325802875512065,391635896579506250685909185055659923429887657462044175657270,-3442341578318633993130256504836700830899745888787510695123,22024574408720156738666870804614260331285423505649995251342] | [-2367511165873068014746985790929225007224120155618770320052484,-401210519437020882591096673484631135388554550327686416573740,492906100659066852521708853955368157523793813651865181967891,-2378304396375003526377269597930065340067922831163534596669305,-495174476947760146477696828509527437867581083454058228355087,-2958472475148677996195492841501922183171701360756712707424087,-1777741909060039530525842351347566457130478997053242796930785,-629670215338503527451306443429765044548222787420308144125269,3470411945946771444069252219361941756082067387907478412799340,-2806803612800712268945038055264559040538027797527323583682006,-250111711231463394475594029969081484285367495635294457967042,-174288884221852129724821748497987778547409770153754206492030] | [[-76987308627721680323,583095958643915592719,-416577992850521550356,-32293059347419055788,100340511507408367354,4265162891787426450,-19241478892956404505,16878161567759955311,-11147129132526761728,4268939276761320024,2582083491299226746,-1617348770632352171],[-227791891193911830939,1583440705261139408235,-1126391160436762201258,-53001265144654082148,243285387019250850856,-67455166351617010922,304311275443824319669,-266934516957121639484,176296068650834735549,-67514891310096846126,-40836628250406845664,25578983297837900326],[-1158632395102154248243,-3411736226593801005459,3210202266972650377420,133418939180011679700,-759672509284266515710,135484901662483651953,-611214610507044926998,536142726144077644138,-354093790238918261475,135604860304113218067,82021094335365823405,-51375843010589572268],[439316406559859768113,1739680369086527690214,-1546869588006360227372,-76302363847507950199,368167069522225567919,-44491112809036774400,200713273973098646985,-176060846765376723779,116278836779504223764,-44530505342017722085,-26934438568558888918,16871019567462572837],[-119914010950224456896,1113207708192964970020,-753908358179142494858,-43741409037842199093,164455810176309643954,-23574836485685125074,106353433656108250939,-93290668899204840629,61613531124483225794,-23595709699797993332,-14271951070608742461,8939572479493914564],[505724557529905053542,-711427658317458828632,401447791183785470042,-723469120432108271625,519588990718133631456,-608737435856209455621,248828356729839068581,-28704229391904797295,1335280266237045661117,-1148675029580971155085,1128217670765335439511,-863152521459991211561],[-4298353180118726671,479857529494598076363,-358140813387040449565,-135983975572301987978,174650618918785721222,-83828758127751864882,19453979550867066718,10164170042716920097,182364004434961319720,-161382326092743914524,230708752418448175840,-136171141779712673050],[-185499542219881419159,1538538720783763141742,-1103744366231876249929,-117880500274485527041,292252201369901010142,-126284829515713087536,344512523970884381998,-285104570460246251699,306994143291897420541,-175036226139109488333,234111536334320544971,-70350609407820025490],[216143728667702851323,-4061395143456088089522,2984586865425070826447,817912991372337588515,-1197936279565628260065,-587397150814596737173,-137086154384407343949,652524217800304901806,-1787512704084229638307,1217062837362582055035,-1423376600956937082623,769112082513370845173],[-150177301844942536348,2279017128709185686763,-1667281686599840455456,-405444407661389912910,627170115541616950914,324511496346925006686,23108588016570969887,-275416241080945327850,818334400904179558492,-563223058818389828962,713653309259391451343,-369962731642231598217],[-169061129850263921005,1058238366441841668964,-748420985847009208179,-4253802461094077307,136361382339122418977,77282185674907095111,92908190366767987353,-63080378270783079781,-36908205754841322463,44976667535695453800,38922670238544667841,40061861596831638264],[2891848507299738039,56416168528391027118,-42987293640773503153,-22280939145568325782,25829884765498308890,61326853354998294706,-276664545842729777215,242683472033632937306,-160279541715981256626,61381152291142544737,37126613833711894250,-23255128443380553393]] | 169564914098 | 2782406332776 | 152556414449 |
| 19 | [229916290849644739012788064210849136125707836656146756429599,529673000444809197455909120782434705076092714463260166353827,692342504045443337235051772027298426864908053403866426445472,194611083970378968545468752703614159939852573631686459035506,547342047081641017837743624495012121202154964532283864357486,437572766925876721593029323435753442531875628401643248920251,226691791537026163207600575095259907623905656522855180853419,527134931080742973551483423958232220525310487119401817277001,737823431431889242724615436461553976239298618589036797299406,175128521640456164701875441249736378162348586397697049524473,550101915195674062300642773755221971593251330454203240197731,603929294990417392821439307851879595703994378547948652412389] | [112629656048812074761289484157459306018952736707004491539043,131169569475109119884802373852347318265523822147110234767578,-1058517817596791957357045618480356919417277159950614717320016,430952700355179414959192837481762027138978638603870327713561,-24490301409070424906666892406107514185925283743815115420899,733840053486680092782175916884850726317781270520122724539139,133506495359080451558524259473986084619887723941146640564162,107498066171138728375911140211361037243644538236713690440988,-794120445787815792286957571320863160399303379176686699245125,391756963359707300356876279803243352319568372110032734505416,-3431549643211746976677179817373405138987334060821518972303,22032092037256259565473400785783585917406002851887710908354] | [-2367411083191959879210213405297360253947678926342573220947278,-401141243697322425089768762810708595826842710272449808621174,492861096639329779018674108047451183265931989690327905671652,-2378175804782881187391969592027090112251284710595807536765619,-495159163316396055484954266895178926621330515233151988341039,-2956547007239197311953480335573653403550717576818859241483782,-1777978833076413613733971588650221019075596121280187642313738,-629459115881002065443709929721773036382838944122915737545388,3468444310186085276182011350002623027589780711514084796326019,-2806344327381268139167159900915388788890769987636755310541072,-250246235990654115135668055204551830328018741484064842311603,-174258922281568165046935104608390207967522608152980185471260] | [[-76969617417799064740,582899756552720529315,-416441064754021810792,-32280893477346001596,100306767587249189761,4261243059869605053,-19222397552926549921,16861190552437993749,-11135947819960179161,4264673300704613127,2579943116336921407,-1616049417874308394],[-227733513141612887895,1582894107121976564293,-1126011491861454216523,-52981124768292756031,243202138434141693923,-67456857856745586059,304296779408142756589,-266918107794141200620,176285660929695113934,-67511159680220688339,-40841335176631405789,25582585724260354872],[-1158255754447769060711,-3410470213910523145087,3209035253894307599345,133370029850410723008,-759396251056590085527,135470164838162746120,-611103691691161299641,536038013183961404395,-354025495754130412292,135579216418845721919,82019569016075080871,-51376201251648082356],[439282010841329882159,1739278694756039956590,-1546547328317490380854,-76282506785520517322,368089520906948114285,-44499365125080546218,200735906229509540483,-176078262679401480485,116290622499580308738,-44535186489231657659,-26941863940361079937,16876102136347809198],[-119831650409348222448,1112771715609278505238,-753626491785318801626,-43725170503584715691,164395493570241009431,-23569780937459291115,106322895232617002987,-93262590770375508586,61595137137159802248,-23588754280192371868,-14270177323569063767,8938690008584400767],[505394351323066182119,-710884261544827024789,401129172268235651995,-723049872959623227163,519319191156759421875,-608458664998048607967,248723190695221416827,-28695231814597727450,1334712690260685674267,-1148205179578425215740,1127988255992737360544,-862990671377920035105],[-4294166591391140383,479686589451719223748,-358018917435796836367,-135958569185040578841,174611029802140632720,-83831959123395320906,19472255229432000562,10148347436801357506,182379616228810856311,-161393593947512736289,230747713189914137430,-136203043595609719299],[-185467898508785492394,1538020535622946568766,-1103378974470977569887,-117822386164463413167,292141905341346628508,-126258604180773817900,344475787163229352402,-285076025108157974715,306924536592730802105,-174986797260548494068,234086721578726609902,-70332697156211589579],[216262867584366652730,-4060161810459887474570,2983673140811612470717,817455340389993835444,-1197416726621224797066,-587492757137777306096,-137016267159443597462,652392607256888951750,-1786850373964705780907,1216574490110585964452,-1423130544410440277567,768940936664384140414],[-150228551188352089491,2278501168216329984811,-1666904578148211680032,-405266087352036002912,626965587355132174298,324582847354194055035,23099047103391520303,-275405135621692296666,818134864820730005699,-563067045338762663673,713613790442770870254,-369925074653846892928],[-169000303112122748993,1057822140309493926825,-748134614412426562399,-4263574913518766279,136318246128069990165,77277080620518468706,92887247861954874908,-63065893453206637984,-36879177017230662761,44949856814237682826,38937529868635333290,40049561417268239728],[2889099654818840278,56393961220718022301,-42970574975957674393,-22271697853854744170,25819835717399792013,61318493867844773255,-276606720131676587650,242629391228828188718,-160244214778906006103,61367854394491922486,37124900864804165667,-23254650093367868958]] | 169514181949 | 2782584479633 | 152457740968 |
| 20 | [229911430157653217815110341774569750890496676566408653272297,529667341828615011241022677409860790910609643770869923176320,692388165635996390490799194583962723437085525121605126003066,194592491812653918940058283662232286144785951058703947021580,547343103055588845535872836764848550019021194192703938384995,437541108622075481789534644171398283787695499054886355377201,226686030832097033845761213301759196348838863003712145647769,527130293366426428275454945221706069536647583427486295162988,737857690518622368164773279746858496780611587701426048476991,175111619865380334813616205910237859170714568957633093850715,550102062989071879144390892343432548570819863518236590246627,603928344433087695397138432463932303078707419643775534503214] | [112731776562849911137542434396974259425147038567445696829360,131186871953156543700294884801957678219754079921634943612546,-1058539077104507210673052645835495954720636281796860579208000,431055284610623125813053676057327803364131888390696171495312,-24468942129591510691144926708188058030870474070596342548581,733967548126897417362847462533683067121536790949737564163971,133583196883008569645058903783412496388802783611099105102128,107525214507555183433204705594413841178330790186123034355291,-794270021159025866883213799070054294711420990352281136147052,391878010331108708965914152046300144621615261072951490557592,-3420751907715789504177387994574205774001786065883379266163,22039608373051066741155076200231913138709961096470345816390] | [-2367310926894531900318477915483203379144987779236928508738248,-401071948102918076178640942326264908549892112761800676466964,492816070544325889867780654272833969847834324077474749326613,-2378047141772640368859717859289248003280593119253685466338729,-495143828410768518352448801773542567760517274400882207540737,-2954622834549805401224711258359495051389089869202422265161986,-1778215462441267117668379292207237749382064643791576397095125,-629248097820208938546518933328355321273220898873901396269281,3466477947092141790041339252942833157082857241400224933210290,-2805885196335196660965840625307554537360350462727141442752157,-250380640848595930746496378510289699902852416179702775784003,-174228947482466496063411968678756042035884531804904881766009] | [[-76951939417015193140,582703697371160238723,-416304237093233968547,-32268736342306039365,100273048269673073420,4257323589494471368,-19203320419518712082,16844223643293307309,-11124769173163420376,4260408318773308836,2577802466525548049,-1614749843383618815],[-227675180912287448407,1582347927504001058068,-1125632116138229933735,-52960999768097024350,243118953903042051854,-67458549548242597383,304282283171410343012,-266901698063714124177,176275252915345956277,-67507427994647955407,-40846041358661324116,25586188136299353884],[-1157879424187315197482,-3409205193237534358662,3207869162023440984169,133321158955629944335,-759120210855723116149,135455432200805213103,-610992801565579275435,535933326590344147163,-353957218615834899845,135553579153674497688,82018042531031166558,-51376559318029883770],[439247651822592588884,1738877317636104598415,-1546225313070919888177,-76262664485496175071,368012030992963238072,-44507615500514848079,200758524363569344556,-176095665166340172965,116302399496471488958,-44539864386881970856,-26949288350905345907,16881184539549787478],[-119749361128487538804,1112336064006214713435,-753344845673001599528,-43708944252602912752,164335223765863534995,-23564727974118520943,106292371809004972337,-93234526280525251789,61576752114251252298,-23581802270868943730,-14268404225740188834,8937807992674519869],[505064452809269319634,-710341468857112583121,400810921429616087343,-722630986652735125059,519049604358514617732,-608180028339711053145,248618058355222406253,-28686223439124811869,1334145376145721172226,-1147735548806064566784,1127758921246386111009,-862828871306684465937],[-4289988843332022850,479515779456858095401,-357897113602218073326,-135933175353549692736,174571466596704603729,-83835148054944579924,19490520863437060417,10132530587266283728,182395200972374210509,-161404841104331724770,230786664261275345441,-136234938540591616126],[-185436276810523568516,1537502738564429107026,-1103013859006784105157,-117764319052425171268,292031694738024001714,-126232391904761343706,344439061622748453101,-285047486126750078488,306854956633730552154,-174937388511760012188,234061910810066785142,-70314787467163198504],[216381866670391487536,-4058929268406061649203,2982760021040778897500,816998079215130832434,-1196897581971287540063,-587588284499489800547,-136946403220906954696,652261017250701783985,-1786188329225692085187,1216086365547619320413,-1422884561756252884549,768769837627464072202],[-150279760751485377916,2277985582729581439588,-1666527751526573518698,-405087910172491709504,626761219481229751124,324654175442496970037,23089506441989445897,-275394025397784961553,817935395927839881544,-562911087336160579137,713574286061613218070,-369887424708452195835],[-168939527402667012002,1057406247368359167094,-747848472794918071058,-4273336589323277497,136275142558763810390,77271978625847386642,92866312923862209341,-63051415039081542538,-36850163957597896792,44923060368166955029,38952382663286629135,40037265397432104573],[2886354223044143676,56371761941871036514,-42953862756275741164,-22262463282589431649,25809792963964412617,61310136817098676023,-276548910956303505910,242575325656828864424,-160208897850370166689,61354560307621202317,37123187511547040983,-23254171721298257831]] | 169463492384 | 2782763395426 | 152359117444 |
| 21 | [229906565060596866238017749234464599444690219917075978155412,529661682466110777511986407831344561376993181307445737791237,692433828143575894754997574535945646031612713771695233649715,194573895229886213919961499805127894946302973935410264616517,547344158108178757138077387914455846191902672406038322629036,437509444820345982291180708162479170475382024064027358713673,226680266818285147418359142954776065193165048991850075409499,527125654481212274727482418839404683615805491838465951301441,737891956055737833775049261866825999073538628350650463346693,175094712869145702042097638637990339264391543878071323526276,550102210316564308765065772842346010323980727510707708316499,603927393551554785991250858784560091363793922958519068830875] | [112833892754872233295980092553045153177205560185921234395360,131204171441581674540443407642992930173748814926278060114099,-1058560334669462185054969684976594895313353265282214426026467,431157863314408789115990607931177701940079643730899554974952,-24447583512071033853793596456096846812637456190407395290623,734094959792276311530874466550148764921723008888562947037846,133659908608030826287343452515768603775424046880466676058494,107552353743070483439846968005264105251059520628527811868982,-794419511734949664748025981128695653182076805063122465671031,391999037500367551691590928985724251086329617030095327618390,-3409948377001820045705095042344914942536124059600837229586,22047123415549947477525335750588739804051992822407595282108] | [-2367210696990834789818029736336483725761981455544257701617341,-401002632659753516217724224455353899501840699329976860084828,492771022378692291844002072631483655953984569223229193165350,-2377918407357484509898898412725668499662830146955000857137705,-495128472233676759192330474628600537712700845540651695502870,-2952699956433199185978549018623308739712709382010763587605929,-1778451797275454482062495818271071486851684463061572651680742,-629037161112444906825873136827093479476227796981416557040662,3464512856020591389160477434589465845141727502951449517342393,-2805426219564800614005263882400275523264007131472971783126358,-250514925856507907451975987674264975986384198906950633451950,-174198959827245578725045900835829575583977471230889725405837] | [[-76934274609047058107,582507780931517542485,-416167509750299607990,-32256587932173370369,100239353525871980117,4253404480828798716,-19184247493359558593,16827260840887624130,-11113593192499246512,4256144331100436479,2575661542143260421,-1613450047277414702],[-227616894451482404160,1581802165919998645910,-1125253032926512130013,-52940890126276505977,243035833351521372294,-67460241427049796729,304267786741536032753,-266885287773295878850,176264844612645021461,-67503696255207272169,-40850746796010027262,25589790533772729467],[-1157503403961391397583,-3407941163422203615089,3206703990290115566243,133272326451022178702,-758844388428429238741,135440703751221574737,-610881940137498724807,535828666370121054843,-353888958828477215263,135527948510246064676,82016514880067238668,-51376917209649820438],[439213329463495535387,1738476237378706113656,-1545903541981316032826,-76242836930308174724,367934599711812427984,-44515863936529093734,200781128385111001151,-176113054235433387767,116314167776216620985,-44544539037250980186,-26956711799546134159,16886266776817922145],[-119667143024452563581,1111900752987677113964,-753063419586333265600,-43692730270655327126,164275000708809588643,-23559677595049941990,106261863381289923177,-93206475425979707871,61558376053340817480,-23574853670908572251,-14266631777055961627,8936926431733824584],[504734861620827337973,-709799279428543185194,400493038153621807197,-722212461103946763812,518780230103055365979,-607901525852045904221,248512959726506522573,-28677204290347219752,1333578323845323175457,-1147266137219442468876,1127529666537043069512,-862667121253855661924],[-4285819924240746834,479345099350958220429,-357775401773525961961,-135907794061460749020,174531929269644646334,-83838324931207659616,19508776455791381492,10116719494041228361,182410758682112387370,-161416067576336375743,230825605632787714234,-136266826613094422646],[-185404677098717739453,1536985329163258452421,-1102649019522880380465,-117706298884894905219,291921569462471731596,-126206192685608204813,344402347352990044480,-285018953520178197245,306785403413178988241,-174887999890212682873,234037104029215973087,-70296880341566387636],[216500726096296571310,-4057697516498616884060,2981847505497103419621,816541207407173011121,-1196378845168469683125,-587683732938014252853,-136876562585000814207,652129447814593657798,-1785526569826749645376,1215598463630844625939,-1422638653005171088071,768598785410441613729],[-150330930577754893894,2277470371816235257505,-1666151206410907176230,-404909875958755445589,626557011736291685599,324725480613559785545,23079966040607850071,-275382910419335795018,817735994226989982333,-562755184808704475396,713534796117250744338,-369849781808015950229],[-168878802661569347493,1056990687224495440380,-747562560722860570485,-4283087500101186459,136232071591570943559,77266879687754601349,92845385553614534698,-63036943027985996153,-36821166570868300206,44896278193196182194,38967228622015096922,40024973538001734591],[2883612208618075488,56349570681268881734,-42937156973209469244,-22253235423992476517,25799756497697841341,61301782203207398199,-276491118319694731727,242521275320529213714,-160173590932242008560,61341270031223371263,37121473774080666306,-23253693327252555258]] | 169412845363 | 2782943080277 | 152260543908 |
| 22 | [229901695558662190927580097359463511817122744257357117770688,529656022357425477644260981865021411617039388845062024009352,692479491568098024921843464945010365149122402878444427585177,194555294222315400996592833297743123766141268011243198075901,547345212239439327240965695624260379505584413672054427128485,437477775524266292597855119533195628009891382588103361583166,226674499495150734775708526216097488422048299344642411947131,527121014425493021504853895543503812891337220960749759857939,737926228039579020676809076247554362214976424532773148082568,175077800652606325077873261212607770829763779364898427314022,550102357177901475162338381069755683886264238015102124071520,603926442345874465285980851029730171753751523247073135484111] | [112936004621704115057870186579345880753152541072110126010738,131221467939528427556916459186538419924655316831286681065834,-1058581590290704922964335669408559022244089287155228914149170,431260436463456506177570585308786789159766907017193308602110,-24426225557426518087539944322853669319365824510175307164382,734222288538646608660698954614756993690837130149636269195690,133736630521444702206174681137498631577854658220007168263130,107579483881192999771590911925183920970286319980251330650382,-794568917570444329929526460108591611046900635016140607521238,392120044874136688090671036643415769208678764764419680420933,-3399139056238686894646208615989091018774930823824553312740,22054637164198387423576517372553701430602120317831854087227] | [-2367110393490928643467224480313200271199830668314056347719608,-400933297373777142189813685473875114909965955260787008882744,492725952147068871733237079483262996228313598961568372504902,-2377789601550625971737671804257571282665742465164156377347468,-495113094787922684063561855601831235480223432526148084700592,-2950778372241697857616415383585459351608396751815263979366457,-1778687837699907240564336032686362020001321034343344821917573,-628826305714000928185104886725029888768711341222934770345769,3462549036326708920049085635066091740745507970306049723086029,-2804967396972323923876500127387486982912488566752488649433071,-250649091065643722628832633145142044493455745089735501976938,-174168959318605457751644085326760944737215430081799326258215] | [[-76916622977596794401,582312007066334222249,-416030882607542192303,-32244448236837862633,100205683327082356159,4249485734038960969,-19165178775072610639,16810302145779705964,-11102419878328484512,4251881337818298025,2573520343468279546,-1612150029672865167],[-227558653704828789495,1581256821883507479510,-1124874241886249432729,-52920795825068287432,242952776705264023609,-67461933494106960758,304253290126415273901,-266868876930329421627,176254436026441846551,-67499964463724138917,-40855451488190973118,25593392916498316665],[-1157127693411151339221,-3406678123313678816365,3205539737626047645242,133223532292009161703,-758568783521862903346,135425979490217517486,-610771107414085795587,535724032530155955372,-353820716396482297632,135502324490199158376,82014986063016486314,-51377274926422730281],[439179043723948067542,1738075453636366324694,-1545582014763786350622,-76223024102856211104,367857226995142804355,-44524110434311609851,200803718303960380711,-176130429895915221563,116325927344850274611,-44549210442619363219,-26964134285637932341,16891348847901623317],[-119584996014181574340,1111465782158180661944,-752782213269851196888,-43676528543522509689,164214824344795499561,-23554629799639974073,106231369945484790128,-93178438203060017492,61540008952008798084,-23567908479391010840,-14264859977450124541,8936045325731826855],[504405577390600217549,-709257692434688838440,400175521926793971489,-721794295906345700408,518511068170333827240,-607623157505814193974,248407894825669733842,-28668174393089181430,1333011533312475189163,-1146796944773966876250,1127300491875398868211,-862505421226957223953],[-4281659822430142755,479174548975209787440,-357653781837118111274,-135882425292438079025,174492417788184759985,-83841489760993544455,19527022009408822613,10100914157051651509,182426289374491462269,-161427273376665810961,230864537304718948383,-136298707811562745273],[-185373099347032772664,1536468306975166332906,-1102284455703336871951,-117648325608475790557,291811529417375687878,-126180006521237705882,344365644357486436754,-284990427292585382207,306715876929335606321,-174838631393359913469,234012301237043567906,-70278975780308871701],[216619446032358644024,-4056466553942720142242,2980935593566016754643,816084724526180699940,-1195860515766070811589,-587779102491663573307,-136806745267868405656,651997898981341251004,-1784865095727224378710,1215110784317274019064,-1422392818167920486353,768427780021100345156],[-150382060710510254455,2276955535044253486122,-1665774942477692150023,-404731984547071239379,626352963936977143811,324796762869128977811,23070425907472622679,-275371790696442192087,817536659719596461189,-562599337754467704240,713495320611003999728,-369812145954498059811],[-168818128828593762726,1056575459484572134508,-747276877925052830223,-4292827657431720893,136189033186922884585,77261783803100625311,92824465752330286036,-63022477419494270502,-36792184851958385038,44869510285030315088,38982067744342897393,40012685839651736367],[2880873608188287411,56327387428346681996,-42920457618253676611,-22244014270295992646,25789726311117312462,61293430026616052530,-276433342224918291553,242467240222808412242,-160138294026379929495,61327983565987681953,37119759652545213230,-23253214911311615696]] | 169362240847 | 2783123534309 | 152162020389 |
| 23 | [229896821652035835476841836502651688675892694690073033353658,529650361502688129936581783572139614363786414271673555499651,692525155909478914825394744085098867904421243302916491089084,194536688790181160526221450545804783165874621901234559780776,547346265449399170017627049380958415929567378520156613543380,437446100737412074488607106734377192284598239809747452985856,226668728862254574602346778997569077234488096744071469539529,527116373199661025905417994368595884379713031937842209531117,737960506466491675756246756450553600878627157717082753767236,175060883216615975719013331666723525154023712908572906664571,550102503572833725256053929004150298916203674133593253050028,603925490816102557881026486562067963832726387480634143192079] | [113038112160171064407739215042555494667596740659048438402651,131238761446140974555101395622318391986290982715519879780018,-1058602843967283667072759624412285906838827902736481511255935,431363004054686948439468892748176371791632108631400481793600,-24404868266575366162059853491994758476518190680903084208919,734349534421810195104690055824630538612530709557683223558066,133813362610552896384516104646205867487951296766529421535639,107606604925429217693816646651079309192687276381971519612126,-794718238720339186998308377702034299307378736404061628023208,392241032459064759567518251900173278543190273988979424922648,-3388323950593026678472594391269122850894223205296267665809,22062149618441988733999607079352540308582672766972287551978] | [-2367010016404882938007274953907773843863418667032768778269611,-400863942250940066250649849797828895690994067066190092113170,492680859854098294975119447343076136007474418496149691613112,-2377660724365286033929832894842740163540384288726134664996245,-495097696076310880083932683669006983283337080073796565931262,-2948858081327245078396710594124485062740527276276186320914943,-1778923583835633635044647583411684065364237612833410909512550,-628615531581138332086427734021765631226177094415109353637754,3460586487365395872569568251917219704754480800204751203135609,-2804508728459952041339707823450747580858176488847397809542185,-250783136527291489043828389584131424997206318270682732500765,-174138945959247765947932415834438425475396575664387103992169] | [[-76898984506391630550,582116375608410520172,-415894355547466712558,-32232317246205020686,100172037644585046533,4245567349290933392,-19146114265278248859,16793347558525353642,-11091249231010030704,4247619339058469433,2571378870778893657,-1610849790687177156],[-227500458618041619174,1580711894908816654308,-1124495742677915304948,-52900716846736869871,242869783890069073136,-67463625750351893219,304238793333930024124,-266852465542245211967,176244027161577756098,-67496232622020934932,-40860155434717650941,25596995284293953490],[-1156752292178302568936,-3405416071762883365234,3204376402964601600071,133174776434081396557,-758293395883568624788,135411259418593900366,-610660303402472967578,535619425077281372910,-353752491324254567249,135476707095164743088,82013456079712129576,-51377632468263445231],[439144794563921110844,1737674966062143341576,-1545260731133877780185,-76203225986066371533,367779912774706915293,-44532354995049636131,200826294129936282565,-176147792157013281473,116337678208402733089,-44553878605266156671,-26971555808535268530,16896430752550296797],[-119502920014740721527,1111031151122850568559,-752501226468487048262,-43660339057006982859,164154694619621396119,-23549584587274331363,106200891497597691887,-93150414608082837031,61521650807832561476,-23560966695394906123,-14263088826856318424,8935164674637997870],[504076599751994044778,-708716707052459313299,399858372236518246094,-721376490653603192497,518242118340597655965,-607344923271689113897,248302863669239612513,-28659133772138028626,1332445004499973685171,-1146327971424900822447,1127071397272073513355,-862343771233465276283],[-4277508526226482508,479004128171049179254,-357532253680567604145,-135857069030178850316,174452932119605813322,-83844642553112166578,19545257527207950941,10085114576218952174,182441793065982538874,-161438458518462745358,230903459277348521634,-136330582134449723508],[-185341543529176024591,1535951671556567185305,-1101920167232709067915,-117590399169849927461,291701574505568727907,-126153833409563938953,344328952639753916520,-284961907448102120089,306646377180437131419,-174789283018639914830,233987502434413465038,-70261073784274551167],[216738026648612384694,-4055236379944696812601,2980024284633845283525,815628630132848967630,-1195342593318035706160,-587874393198783404409,-136736951285592896166,651866370783647759510,-1784203906886247551899,1214623327563769666316,-1422147057255156211977,768256821467176533976],[-150433151193038313460,2276441071982263717133,-1665398959403905263024,-404554235773928272638,626149075900221927101,324868022210971417862,23060886050792464052,-275360666239186486114,817337392407010960635,-562443546171476171350,713455859544181856706,-369774517149849902785],[-168757505843595462781,1056160563755868798407,-746991424130714740548,-4302557072879782871,136146027305315431168,77256690968745738652,92803553521121798120,-63008018213176713746,-36763218795775928193,44842756639366368273,38996900029797800933,40000402303052827673],[2878138418407645443,56305212172555842001,-42903764682916208285,-22234799813744096274,25779702396751601586,61285080287767473247,-276375582675026065745,242413220366530587270,-160103007134632471445,61314700912599658889,37118045147080878808,-23252736473556312804]] | 169311678796 | 2783304757646 | 152063546914 |
| 24 | [229891943340904580407084891005040231549471768483568845752508,529644699902027789599885150689111717606368929699777250086345,692570821167634657248209633481530951874094908421451669262644,194518078933723305685369248430533123657303203489768979290675,547347317738086939212412867285940168417625903445602260458286,437414420463356583227542933316653151387990454760049780270004,226662954919157993191863891219757917313344457657597042626799,527111730804108494008972288941893145308298709602103809506843,737994791332823910463993156690747994152982313393305389317338,175043960562028139053116969555456531987511766568811842093168,550102649501111628790795573883431722712994775213661238236616,603924538962294912288552488864738728746055744257098496481942] | [113140215367099023897973181452503989536368516611083051664889,131256051960563744111197155727436590559072769228900290659902,-1058624095698246860381753769692287102444048572290430300189199,431465566085021357860096023338562224820956295789872599024224,-24383511640434859808144761775033069278208943186064736436212,734476697497540994041387806284049362439966680664826952336546,133890104862663329368146487347454645206741652391351725715708,107633716879283735087193344767036735593319035656376600897855,-794867475239435724989361061121409377645744207864970583124295,392362000261796186859839209563901087708545028232338427593037,-3377503065229262877093117930376173015281255523440187897333,22069660777726470137674468945720113216921732417759744788501] | [-2366909565742776528130328176130924862821669273978229590399522,-400794567297196114278309426097945482528390914890919655867294,492635745504426004305023620754584011753297500439634770372390,-2377531775814694890568122628768301590444244353814578180675863,-495082276101648614541316797612770979797111280092956212947364,-2946939083041411177829184731893671895801080376908340747358413,-1779159035803718230774078092163829971600949249352919042975638,-628404838670088992876002794322156857624346446042208203708100,3458625208491182575262348995334671248057566800517774339967656,-2804050213929812320692042321611048944391168257279743866488515,-250917062292773579406264018786318865048230995606897308233020,-174108919751875723519036141620835557399900165106869646857662] | [[-76881359179183840544,581920886390804640487,-415757928452759337596,-32220194950195955395,100138416449705209273,4241649326750293482,-19127053964593719219,16776397079677412518,-11080081250900854376,4243358334951802019,2569237124353458151,-1609549330437595424],[-227442309136919726503,1580167384510964761255,-1124117534962507033206,-52880653173574116190,242786854831850065965,-67465318196720427205,304224296371948765952,-266836053616461225972,176233618022885871452,-67492500731916922019,-40864858635103581442,25600597636977480957],[-1156377199905105433243,-3404155007622512740794,3203213985240786710141,133126058832798021467,-758018225261480230340,135396543537146762861,-610549528109759107089,535514844018298578459,-353684283616177958838,135451096326766024511,82011924929987419560,-51377989835086791247],[439110581943447051534,1737274774309630527660,-1544939690807575815358,-76183442562891084906,367702656982362533310,-44540597619929325427,200848855872850435336,-176165141027948685405,116349420372899993371,-44558543527468756508,-26978976367592711340,16901512490513344107],[-119420914943323781992,1110596859487421124085,-752220458927565971996,-43644161796933198212,164094611479171044232,-23544541957338024335,106170428033631944845,-93122404637360351250,61503301618386550394,-23554028317997801093,-14261318325208082611,8934284478421768066],[503747928338960011795,-708176322460101586101,399541588571023183586,-720959044939973142944,517973380394389481770,-607066823120256252798,248197866273675457352,-28650082452244234712,1331878737360428583037,-1145859217127362805410,1126842382737616505698,-862182171280808546796],[-4273366023969463289,478833836780158508645,-357410817191622664468,-135831725258412991145,174413472231245426277,-83847783316374386709,19563483012112026717,10069320751460476643,182457269773061707199,-161449623014873454329,230942371550967655909,-136362449580217015744],[-185310009618897354321,1535435422464556835203,-1101556153796036531739,-117532519515778194068,291591704630030417041,-126127673348491806007,344292272203292773276,-284933393990846351576,306576904164697568219,-174739954763475737624,233962707622184070681,-70243174354343518611],[216856468114850825148,-4054006993712028448477,2979113578087809313418,815172923788506469330,-1194825077378953149746,-587969605097751975394,-136667180654197496547,651734863254142996810,-1783543003262736306787,1214136093327044155569,-1421901370277463052386,768085909756359215289],[-150484202068563273422,2275926982199557792364,-1665023256867019698922,-404376629476060419996,625945347443237946652,324939258640874323960,23051346478758909008,-275349537057635964568,817138192290520744990,-562287810057708438301,713416412918081530191,-369736895396014345954],[-168696933646520678961,1055745999646273968706,-746706199069486501853,-4312275757995970886,136103053907308555884,77251601181549996690,92782648861095314123,-62993565408599758056,-36734268397219999878,44816017251893444880,39011725477913178040,39988122928871843868],[2875406635934219755,56283044903364015795,-42887078158717911234,-22225592046592882851,25769684747141003390,61276732987102219994,-276317839673053815726,242359215754544842896,-160067730258838337074,61301422071741104726,37116330257827885524,-23252258014067539432]] | 169261159171 | 2783486750412 | 151965123513 |
| 25 | [229887060625455343149074043216922721479027455978136031465679,529639037555573548746229564396492508059381869670706158140059,692616487342481303929990883909928542318860222316449096473926,194499464653181782446192262473093949922974710905206301392132,547348369105531328135712965634281752570284456411729898863043,437382734705670668770416002751055252931900619677207379576374,226657177665422864221589725234688226337297907951882565059278,527107087239227480758706503574730913602490625772414214137159,738029082634926199614033778872644458337541374850291983264215,175027032689696013639432386588876937037888566769675360464432,550102794962485978240384366736885090742848061510085335739810,603923586784507400928160106699058625596008731287465669796146] | [113242314239314371053287483299123449988706757880033563420696,131273339481941421689244412741343789846665299374287742822433,-1058645345482643146342508025079716440230096744112573721506291,431568122551381547299061154172678896838074041812201555888462,-24362155679922159602106729645554262354089516018553729569885,734603777821584949418384133871400978939958748751712284758081,133966857265089146549727025648071262840305508908102881699909,107660819746259261180809335048549744612085600620352441771680,-795016627182507581438596462406969708101543403905159557121656,392482948288971167540729677610591226847115988765552609504434,-3366676405309604348764424604403169110252923583010298505457,22077170641497667006130537930212069922064954064709143529460] | [-2366809041514697643444869131328816327817209565538880608138567,-400725172518501824421826099805213476582712819755740615871218,492590609102700218395266745737248894068102984091825605026246,-2377402755912091646494995832474960992991126559198148013282815,-495066834866745834004171851692203868800954210821534323849591,-2945021376735395344046088204174537483810078224626662651108898,-1779394193725321532468095849211353323324751425447211562206340,-628194226937055502712956074302898244230675231698329980144046,3456665199058230385647422385485223704405976458677478216618974,-2803591853283974397262541199504072085110697508236489685140951,-251050868413446451315204139515660238681481898655358268863994,-174078880699194137385536434947437367498008066203980822797136] | [[-76863746979750695641,581725539246832252219,-415621601206287064726,-32208081338747353860,100104819713812230011,4237731666582221803,-19107997873633138870,16759450709785777916,-11068915938356001356,4239098325628423806,2567095104470395523,-1608248649041402517],[-227384205207345601846,1579623290205738441926,-1123739618401544717638,-52860604787899198264,242703989456634804221,-67467010834146427417,304209799248326522066,-266819641160382970550,176223208615191120062,-67488768795228248030,-40869561088862316879,25604199974366743111],[-1156002416234372012739,-3402894929747031082024,3202052483391253984003,133077379443786677290,-757743271403920109120,135381831846667332821,-610438781543009521394,535410289359977640450,-353616093276615954739,135425492186618462324,82010392613675638462,-51378347026807588333],[439076405822619618007,1736874878032955467663,-1544618893501303659592,-76163673816309070879,367625459550072452411,-44548838310135743868,200871403542507497358,-176182476517936062411,116361153844363766351,-44563205211502918036,-26986395962164870032,16906594061540162524],[-119338980717251913071,1110162906858234523644,-751939910392805859101,-43627996749147494195,164034574869411686107,-23539501909215361726,106139979549586076681,-93094408287200285942,61484961381242291239,-23547093346276138241,-14259548472438854948,8933404737052527141],[503419562785993418405,-707636537837197287655,399225170419378607597,-720541958360291046753,517704854112546391937,-606788857022013835007,248092902655368415202,-28641020458121454951,1331312731846263730390,-1145390681836327171965,1126613448282506960767,-862020621376368447166],[-4269232304012191462,478663674644465155138,-357289472258206325048,-135806393960903115083,174374038090497852457,-83850912059591975124,19581698467048988020,10053532682689526853,182472719512210001767,-161460766879047741080,230981274125879300314,-136394310147334785088],[-185278497589989037444,1534919559256911179904,-1101192415078841966992,-117474686593100100119,291481919693886749674,-126101526335917041473,344255603051587325911,-284904886924923489791,306507457880308251586,-174690646625275308567,233937916801208311267,-70225277491392065090],[216974770600625762921,-4052778394453350511862,2978203473316021344628,814717605055114295287,-1194307967504054737031,-588064738226979957058,-136597433389645567407,651603376425383493405,-1782882384815394185200,1213649081563660888258,-1421655757245355570255,767915044896290271988],[-150535213380246797084,2275413265266090512817,-1664647834545004039588,-404199165490445789302,625741778383512699284,325010472160645214127,23041807199546350839,-275338403161842884830,816939059371348832586,-562132129411095824422,713376980733988598185,-369699280694925758784],[-168636412177406497598,1055331766764283999023,-746421202471427815899,-4321983724316601872,136060112953526278565,77246514438373237486,92761751773350994304,-62979119005325927111,-36705333651180991985,44789292118292761333,39026544088227989791,39975847717771744288],[2872678257431274602,56260885610255075519,-42870398037192609335,-22216390961110403939,25759673354837309414,61268388125058581746,-276260113222021211106,242305226389685285242,-160032463400826406294,61288147044090106532,37114614984926481266,-23251779532926207613]] | 169210681933 | 2783669512730 | 151866750215 |
| 26 | [229882173505875178024284872783559242249824131423403550547475,529633374463454536377711792125593104035802218454368420789599,692662154433934865576235126826429868028874399273721670634889,194480845948796669551845493979253301641291878056711585664097,547349419551761069658726842919476830179208047749581151073686,437351043467922776971907579617780002493652890235059121761661,226651397100611608527140006872024800717708873097497209041442,527102442505409890042700197370963111447651857876320918858586,738063380369151380181940021833643206416296317670365055601178,175010099600472511691084520189150133981788161312857607201418,550102939956707788712315776086672421751244615795506853843144,603922634282795920121854040720369966703759889548130759523164] | [113344408773643918775065840516880489060509861410484872200680,131290624009418949758093101709287366377205979708700997834877,-1058666593319521368975605884642094225808935611675769943188852,431670673450689900901472111417271547743618575672571577767641,-24340800385954304850221894843177549743245402645234242755982,734730775449660009989624496267634593114562962586071129753917,134043619805148721436324608732315135066630699538864725127554,107687913529856615292753277850662650824919847446114579021090,-795165694604300526513750101037349000494871630009903408013358,392603876547225673536985968471563334335486436314348743332281,-3355843975994043863544442807945522981260292860313465287193,22084679209201531421977957250199717145573808214736439914240] | [-2366708443730743885438452969949556597106733102176425444935692,-400655757920816445649042086924076936292971499229723138765714,492545450653571930495507830693703128620635445683878509215503,-2377273664670724313510847059503730490920535169049241712195675,-495051372374415163431282310278669443635970915123009060298192,-2943104961760027810157429027361935856982282276756803399060611,-1779629057721679601198398618294650999841314466725391820242437,-627983696338211344102919910730888669417893724253494728768736,3454706458420333875509510517829052680257526267907098242584921,-2803133646424450564035254824506896506694093987381771425584766,-251184554940700472600853211025811589948765585449833186757682,-174048828803909400498103240418469364821657937935132018108693] | [[-76846147891894416294,581530334010065993054,-415485373691097371217,-32195976401811449383,100071247408319636737,4233814368951502826,-19088945993007502009,16742508449397400565,-11057753293728597572,4234839311217740882,2564952811408195319,-1606947746615918759],[-227326146775285231504,1579079611509670946983,-1123361992657070264442,-52840571672058544298,242621187690565126861,-67468703663561792417,304195301970904870569,-266803228181403497582,176212798943310244776,-67485036813767950402,-40874262795507441148,25607802296279587062],[-1155627940809465058678,-3401635836992667779206,3200891896354292995318,133028738222743375505,-757468534059598463227,135367124347942034368,-610328063709256013144,535305761109057475250,-353547920309911618054,135399894676329782760,82008859130610099624,-51378704043340650554],[439042266161593762484,1736475276886778938088,-1544298338931921382286,-76143919729325289182,367548320409904285659,-44557077066852870981,200893937148705057116,-176199798636183553049,116372878628811477118,-44567863659642756009,-26993814591606394625,16911675465380145112],[-119257117253973407245,1109729292842239695670,-751659580610316582422,-43611843899518053938,163974584736393879357,-23534464442289952487,106109546041453839943,-93066425553905920565,61466630093968402352,-23540161779305262692,-14257779268481971825,8932525450499624067],[503091502728132676256,-707097352364660157553,398909117271494000805,-720125230509972940345,517436539276199415086,-606511024947372958203,247987972830641602618,-28631947814446566733,1330746987909717382512,-1144922365506624501663,1126384593917153729006,-861859121527479152934],[-4265107354721166433,478493641606141302842,-357168218768416096233,-135781075121444445842,174334629664813861807,-83854028791577592663,19599903894951435570,10037750369815368759,182488142299913359850,-161471890124138904059,231020167002398110183,-136426163834281685193],[-185247007416285680129,1534404081492084874452,-1100828950767130284708,-117416900348733640940,291372219600409870911,-126075392369726234720,344218945188105949172,-284876386254426438742,306438038325437897006,-174641358601431466612,233913129972333642925,-70207383196292686498],[217092934275248173264,-4051550581378450122986,2977293969707484341699,814262673495264822136,-1193791263249213686769,-588159792624910316864,-136527709507840725139,651471910329852596150,-1782222051502711652977,1213162292230034470962,-1421410218169278223719,767744226894564514855],[-150586185171188118753,2274899920752478350718,-1664272692116321304770,-404021843654306263035,625538368538808744462,325081662772111858744,23032268221312065279,-275327264561844489978,816739993650654127806,-561976504229522508505,713337562993177022376,-369661673048510027470],[-168575941376380689239,1054917864719001891952,-746136434067017078933,-4331680983363733187,136017204404656538974,77241430736075089364,92740862258982924687,-62964679002913843601,-36676414552540646425,44762581234237672032,39041355860286778329,39963576670411618623],[2869953279567258238,56238734282729080235,-42853724309887078393,-22207196549576644159,25749668212403785910,61260045702072580724,-276202403324931856781,242251252274771047624,-159997206562415752773,61274875830321042057,37112899328516939304,-23251301030213248551]] | 169160247042 | 2783853044726 | 151768427046 |
| 27 | [229877281982351276226114256846900437362648574369847412402453,529627710625799918375377986104872131745693761035426984107992,692707822441911311866887388699264062591556393950666952681335,194462222820808178491831163219923958348538823997005833991586,547350469076804936208229979920487821378577012462751385032665,437319346753678950793594058817353374676741612274536573784606,226645613224287193876821721955728144380225534260857503510973,527097796603047474775474615303739224056978046199396184828946,738097684531854650102417919149017298535832113882976300810808,174993161295210259257409369156189254026002907127237326887820,550103084483528297852133111821689522178445596467251275201631,603921681457216390089006418827503897055338805263353717310774] | [113446498966914915745568148171313723800054819710244029670025,131307905542141527908307289126913507309381442704698975950480,-1058687839207930572990681624581992471662272250072530737957043,431773218779869374482071715373478310245159116937368801850070,-24319445759448213473212346179281404513006098192852502610024,734857690437456113446913960419584363149683332200472454781991,134120392470165658900428507402859057798614454544089475649113,107714998233574725578129375754912092039446385360671197442985,-795314677559532447239440276397797744975634310731724420505460,392724785043191448663643908970408006319503172864731590204805,-3345005782440356644271620375349228926012767175446461484280,22092186480284132247309142039463942016662618031527148566701] | [-2366607772401022224437767372172207824355887234991087962977094,-400586323510101936293691154421753086581179676841787721788244,492500270161694907072344757056088361029638853263059145863162,-2377144502103849806579696504382364280550668969834239808775803,-495035888627471905280746216094877019348723758611435863794406,-2941189837465772035597664356784824232544474613981919618057179,-1779863627914103672169545189985563033771092873311888121552645,-627773246829701062036671663799498590737446654119245839790863,3452748985930923011174153289364825589200740504151279485319560,-2802675593253196147401890877859620267252340616578313087200720,-251318121925959747059510342091348984320156178600762406235669,-174018764068729491151704767089011395600824229853632662940589] | [[-76828561899442124177,581335270514334974350,-415349245790417866617,-32183880129355991503,100037699504685014753,4229897434022525760,-19069898323324685722,16725570299056292030,-11046593317369852624,4230581291848438749,2562810245445414072,-1605646623278502226],[-227268133786787936965,1578536347940040697959,-1122984657391646380662,-52820553808425786306,242538449459896689981,-67470396685896456889,304180804547511960251,-266786814686903418062,176202389012051813130,-67481304789345959677,-40878963754552569874,25611404602533863015],[-1155253773274296932003,-3400377728217414073242,3199732223069828726135,132980135125432366495,-757194012977612560608,135352421041752495774,-610217374615496934716,535201259272245897644,-353479764720387625761,135374303797499991158,82007324480624147595,-51379060884600786053],[439008162920585542963,1736075970526293880031,-1543978026816725077085,-76124180284970889039,367471239494030263202,-44565313891263599815,200916456701233633686,-176217107391892809764,116384594732256265220,-44572518874160744731,-27001232255271976000,16916756701782680761],[-119175324471063447359,1109296017046991133086,-751379469326599241472,-43595703233934863159,163914641026251336488,-23529429555944707726,106079127505224225597,-93038456433776100843,61448307754130602272,-23533233616159425332,-14256010713270668201,8931646618732367098],[502763747800958315237,-706558765224733504151,398593428618116896502,-719708860985014353205,517168435666773006016,-606233326866657830829,247883076815750227358,-28622864545859709802,1330181505502842681148,-1144454268092941990015,1126155819651895515772,-861697671741427683497],[-4260991164476264563,478323737507603479312,-357047056610523635305,-135755768723864742289,174295246921700623539,-83857133521144771785,19618099298756617534,10021973812743240685,182503538152662579809,-161482992763303704447,231059050180850426139,-136458010639544846112],[-185215539071664133396,1533888988729210020707,-1100465760547387672824,-117359160729675151754,291262604253017798879,-126049271447796852496,344182298616301100094,-284847891983435611751,306368645498232650965,-174592090689321999078,233888347136402060944,-70189491469914089920],[217210959307788620301,-4050323553698263815295,2976385066652090008629,813808128672180566781,-1193274964170943656791,-588254768330018174341,-136458009024626947785,651340464999960567530,-1781562003282966623192,1212675725282431106357,-1421164753059605486473,767573455758729762564],[-150637117484424155392,2274386948229998164578,-1663897829259927994018,-403844663805107040761,625335117727163182498,325152830477122233223,23022729552196234448,-275316121267663024567,816540995129531552935,-561820934510825630372,713298159696909168722,-369624072458684568970],[-168515521183661538223,1054504293120136133734,-745851893587150576653,-4341367546645184545,135974328221451069790,77236350071514978417,92719980319079125734,-62950245400918236710,-36647511096172083403,44735884595393693994,39056160793639657358,39951309787446693297],[2867231699015792871,56216590910302244824,-42837056968361021217,-22198008804283498202,25739669312415151735,61251705718577976312,-276144709984773320002,242197293412606315683,-159961959745415660429,61261608431104585977,37111183288739558260,-23250822506009612617]] | 169109854460 | 2784037346524 | 151670154037 |
| 28 | [229872386055070965801073436820032191825215394632859143434877,529622046042738897488129740349675017110789938773994144615783,692753491366326571465000765710264125997341947732452040995003,194443595269456653477330395708019299973376773671544208721246,547351517680691739761335157529103743419957462733808901181560,437287644566502831512596723778322131655815951181189414906388,226639826036013134745898629528208665091916264785379441214520,527093149532531836979598385946982297006035551391028714294826,738131995119393567066178422532274458783438059169730120736282,174976217774761596406394332245436573293078640470707531779459,550103228542698965747738173514259048640559553110663197839275,603920728307824754941317821521941501474274889786214187394967] | [113548584815955046832007138236304291831770429351931137897953,131325184079254612969007351749123288403049300079446858723911,-1058709083146920003906018810337939020613925097282002785191887,431875758535843495909210396006110560469111112779285143473690,-24298091801320681890766449155049131050969178435852628170158,734984522840635170645411827688699388222639782080882166370745,134197175247468798414497786785616940774934320552405184532280,107742073860910627784489596973317743123884963487176392787147,-795463576102893331816169632770448053913917969075204868633747,392845673783496006174707846241619688096452731735737672757191,-3334161829804098915052928781720842388222316232584647828251,22099692454191655192070751033873892147570085124182652783345] | [-2366507027535648996566026790620992858518241090121390974040898,-400516869292322962601713812813243843746054374432254575809625,492455067631725686448109858341078200460285908663845168252954,-2377015268224733940032338009493202508686070851172669842946625,-495020383628734038618206227061314613577051949799685532893002,-2939276003202726882471153429331379396393086092460763438758987,-1780097904423979773359544361482401720759438069011184529032955,-627562878367640435734442798308927609004910477595909658065007,3450792780943065328782059997738260888404070705744818541704555,-2802217693672109882045241539290713537391286297063578696291722,-251451569420681940581530946233495283397340470538622337349621,-173988686496363972299393984376135764514895335507466922869933] | [[-76810988986245794328,581140348593724287300,-415213217387655945853,-32171792511364216108,100004175974409921818,4225980861959285390,-19050854865189455825,16708636259303530133,-11035436009629063338,4226324267648483678,2560667406860675251,-1604345279146548733],[-227210166187986214533,1577993499014869852376,-1122607612268355571306,-52800551179401707706,242455774690998747629,-67472089902078393890,304166306985962525856,-266770400684250916254,176191978826216226644,-67477572723769103032,-40883663965511350499,25615006892947424300],[-1154879913273328544834,-3399120602281019662815,3198573462479418417473,132931570107686008128,-756919707907445989655,135337721928875557349,-610106714268697242503,535096783856219671236,-353411626512346301796,135348719551721384507,82005788663551158189,-51379417550502797072],[438974096059872005442,1735676958607224374368,-1543657956873446022110,-76104455466303158714,367394216734727030775,-44573548784549737068,200938962209876677201,-176234402794258997278,116396302160706984936,-44577170857327718166,-27008648952516346016,16921837770497154219],[-119093602286223862409,1108863079080647727181,-751099576288545409027,-43579574738309668173,163854743685200764754,-23524397249561842660,106048723936881476560,-93010500923105251358,61429994359291717987,-23526308855911785929,-14254242806738077635,8930768241720023781],[502436297640591992090,-706020775600987670231,398278103950831273772,-719292849381989261864,516900543065984531697,-605955762750106009136,247778214626881709730,-28613770676964326469,1329616284577508132559,-1143986389549823831083,1125927125497001001208,-861536272025453982007],[-4256883721670723091,478153962191512095456,-356925985672974416606,-135730474752024223636,174255889828721589352,-83860226257107897671,19636284681406414378,10006203011374361665,182518907086953279526,-161494074809702333735,231097923661574253185,-136489850561619860166],[-185184092530043407598,1533374280528094859459,-1100102844106580667784,-117301467682999162327,291153073555274147680,-126023163567997261346,344145663339609344412,-284819404116018949870,306299279396816141244,-174542842886309677725,233863568294250109209,-70171602313121199976],[217328845867077667296,-4049097310624875295818,2975476763540617068196,813353970149713042838,-1192759069826397561727,-588349665380810656777,-136388331955788680781,651209040468044684862,-1780902240114224978561,1212189380676968983531,-1420919361926641967733,767402731496286921600],[-150688010362929617460,2273874347270585917259,-1663523245655273130848,-403667625780556182638,625132025766887133967,325223975277544470751,23013191200321970785,-275304973289305750414,816342063809012179837,-561665420252795392303,713258770846435828012,-369586478927358345034],[-168455151539557672649,1054091051577999531601,-745567580763141681029,-4351043425654559909,135931484364725269869,77231272441552135995,92699105954721561002,-62935818198889949593,-36618623276939829654,44709202197418531452,39070958887842302647,39939047069528337831],[2864513512455664633,56194455482506908951,-42820396004187042755,-22188827717534747885,25729676647457556301,61243368175006268957,-276087033204517157403,242143349805980352503,-159926722951625639902,61248344847107716149,37109466865734662081,-23250343960396269330]] | 169059504148 | 2784222418251 | 151571931213 |
| 29 | [229867485724221711629963657395986338235378138176455569386630,529616380714400713321625108800321190244251944871236725066741,692799161207096532025401256293404886906874530913281217393637,194424963294982571416518348636752562569412198117068833201434,547352565363450331840248793976997990280671101691006754242163,437255936909955659930909943941843018077500711983024802557451,226634035535353492090717601411365311803994961130690042229591,527088501294254427867346746281651577063562214656109379665411,738166312128128047316133278557436991042450455978081736730609,174959269039978577407223852078823895439289775212416099744040,550103372133971474833639446718829993203132175925200960149799,603919774834676982677775358553571449473076921508992796068173] | [113650666317592433490493735404768040639084967633789874812518,131342459619903919124649431456729629186018564781991567292802,-1058730325135539108168090068331807992592600625346967270619252,431978292715536365488654969508175660630115618538286039250667,-24276738512488384906097655981028456787749909038341385763800,735111272714831049922899224999726339034048516014858302637444,134273968124392217269076684016447993900466669438530899254665,107769140415359464014665913730606712508097115236605491071278,-795612390289045254033053475607084585090603004195590037313600,392966542774762626330032221689664406958545343420641632351295,-3323312123238606457243694384944711482051337935915588130199,22107197130370402882406048046214383391325235550131590809532] | [-2366406209144749900697700289693435019647571147149843905585309,-400447395273446897276805386912173908848227949229629123456694,492409843068323577438864786673779129797048153226052244649811,-2376885963046651423766951190186909832791831184523912952031580,-495004857381022218224325417120992028433454106655960773100784,-2937363458320628786903698756285216804804743829487089995012183,-1780331887372768345023136068828664608690569670063036870027644,-627352590908116649996471474185934556621820784374935897660605,3448837842809468104569049896324673318560287058754955945867967,-2801759947583034284954661986208021779822190719479697286443428,-251584897476358107671723276474029951720492055282862718589681,-173958596089523990865672483006965117135813053966818179421118] | [[-76793429136182207402,580945568082574510225,-415077288366398443148,-32159713537834815606,99970676789039803498,4222064652925382908,-19031815619203472699,16691706330677264371,-11024281370853617321,4222068238745124056,2558524295932669203,-1603043714337491814],[-227152243925095575319,1577451064252922872167,-1122230856950799138775,-52780563767414191041,242373163310353933122,-67473783313033617108,304151809294057903325,-266753986180801763819,176181568390595730097,-67473840618841107800,-40888363427897462379,25618609167338127405],[-1154506360451568304392,-3397864458044989319397,3197415613526248427170,132883043125404634642,-756645618598967915515,135323027010083279306,-609996082675788551154,534992334867624558819,-353343505690069650090,135323141940578563979,82004251679224538546,-51379774040961479964],[438940065539791066413,1735278240785824619301,-1543338128820249842139,-76084745256405475165,367317252064375448661,-44581781747892003221,200961453684410569325,-176251684852470792993,116408000920168205548,-44581819611412870047,-27016064682694277614,16926918671272946126],[-119011950617282883898,1108430478551971604184,-750819901243436379448,-43563458398575933995,163794892659541706389,-23519367522522878551,106018335332405101215,-92982559018183388120,61411689907011693172,-23519387497634416252,-14252475548817232314,8929890319431820965],[502109151883695501228,-705483382678317504319,397963142762055956236,-718877195298049046240,516632861255843758430,-605678332567868633822,247673386280155803805,-28604666232327201819,1329051325085398084800,-1143518729831671599463,1125698511462668959969,-861374922386750995175],[-4252785014711124091,477984315500770986467,-356805005844387402408,-135705193189815494825,174216558353496376914,-83863307008282189367,19654460045847323728,9990437965605939780,182534249119285854926,-161505136276498381368,231136787444919239814,-136521683599010767822],[-185152667765384587097,1532859956449222465591,-1099740201132155228298,-117243821155858251939,291043627410887850980,-125997068728186749985,344109039361451382937,-284790922656231940283,306229940019289527146,-174493615189742294776,233838793446708889641,-70153715726775165163],[217446594121706286073,-4047871851371513210906,2974569059764729545383,812900197492341619651,-1192243579773366393427,-588444483815826755186,-136318678317050942580,651077636766369339423,-1780242761954341093043,1211703258369618667672,-1420674044780622532057,767232054114690066084],[-150738863849617119524,2273362117446835397028,-1663148940982297309138,-403490729418604153954,624929092476565220306,325295097175266815111,23003653173795340948,-275293820636764962362,816143199690063361445,-561509961453175160308,713219396442996236397,-369548892456431876215],[-168394832384467894728,1053678139703508053800,-745283495326720048969,-4360708631871269335,135888672795358077820,77226197843045606172,92678239166986145799,-62921397396375946845,-36589751089699846620,44682534035962100404,39085750142455942544,39926788517304071210],[2861798716570813578,56172327988891506105,-42803741408950625288,-22179653281646039262,25719690210128557571,61235033071786704078,-276029372987118942013,242089421457667523683,-159891496182835445011,61235085078993719846,37107750059642600017,-23249865393454207357]] | 169009196066 | 2784408260034 | 151473758604 |
| 30 | [229862580989991115409034383457524399062435862693693552500735,529610714640914642327174587314966451143115826422723120417983,692844831964137040203357748975962649330033107302308548822075,194406326897626541889862784549238268072982616181065905997325,547353612125109603507022303123284701728703128188488643415767,437224223787596277585403771096154488119858329131380597046620,226628241721872873122696496128606420440115347610160443532942,527083851888606547922413974729570935740517051331110845066020,738200635554420364442920537136233158855209929125082032669026,174942315091712970912929668425030868497548604749854323640660,550103515257097729795138170061615560523093997713067548540388,603918821037829065179607798130728721965292101489489998787971] | [113752743468655634169850991949574955389256245408414741396905,131359732163235418031742133104923016619534076716087033511400,-1058751565172837533271038087837990395485410515674388431177486,432080821315872656347233466554376624775505845145501208126011,-24255385893867875590541832566022657401861347570178555538056,735237940115649561512604398352676629252971142871189079991701,134350771088275233774515137449005765255869458169772555662933,107796197900414481496985582568188933405682568980820753583309,-795761120172622357774059553925857086672651158069628297543705,393087392023610353978318299771847825429176394172301162941453,-3312456667894993172902340637456606077469390105898739096348,22114700508266794928967635006812718066391491781285376560329] | [-2366305317238459995410574700335700528163776716594687322192742,-400377901459443818025197671067585846533027579727368785266603,492364596476150657991595386230601254873993194211807197032784,-2376756586582885859447179704627680334887447233198470926639797,-494989309887159773701508336779785963735573417893679432558296,-2935452202168853925407502027108458125889697603987218570909014,-1780565576882003860056499453807723745791057368724172321993562,-627142384407188466160371752033474778798033800681520137114127,3446884170882480520158908911959981974656854667850812620337717,-2801302354887756028574868807795872336899706442653240125255311,-251718106144512518361607889373479505902040271792567696432735,-173928492850922277059432062433000316784009209463425481085403] | [[-76775882333152902035,580750928815481217019,-414941458610411286734,-32147643198781909169,99937201920163908703,4218148807084026747,-19012780585965297111,16674780513712721323,-11013129401388996516,4217813205264891734,2556380912940153097,-1601741928968802701],[-227094366944414385607,1576909043173705095416,-1121854391103096184603,-52760591554918165817,242290615244558040872,-67475476919686183114,304137311479586045049,-266737571183899333952,176171157709974420814,-67470108476362604993,-40893062141224616867,25622211425523832007],[-1154133114454571059374,-3396609294372579510068,3196258675155131094999,132834554134556425836,-756371744802432338131,135308336286142949630,-609885479843669187744,534887912313075372676,-353275402257819387582,135297570965648447438,82002713527477727195,-51380130355891625214],[438906071320741395632,1734879816718877910275,-1543018542375735672719,-76065049638387253827,367240345415460391115,-44590012782470032662,200983931134604623737,-176268953575710387409,116419691016640211634,-44586465138683753995,-27023479445160584931,16931999403859433052],[-118930369382194902746,1107998215070326964519,-750540443938942418744,-43547354200688802536,163735087895656379200,-23514340374208644646,105987961687769886897,-92954630715296131113,61393394394847596410,-23512469540398303184,-14250708939441063083,8929012851836944813],[501782310167469787764,-704946585642939837644,397648544545043014374,-718461898330921448304,516365390018652340153,-605401036290010666286,247568591791624718482,-28595551236478503904,1328486626978013204249,-1143051288892744631636,1125469977559028380823,-861213622832464752993],[-4248695032017378450,477814797278526953781,-356684117013554714525,-135679924021163472090,174177252463700653623,-83866375783483680978,19672625395030445269,9974678675331180475,182549564266165438589,-161516177176858802459,231175641531246657139,-136553509750230043592],[-185121264751690745160,1532346016053749446254,-1099377831312035811241,-117186221095482904686,290934265723712886235,-125970986926215551648,344072426685232077904,-284762447608117634681,306160627363731549650,-174444407596952698877,233814022594604071618,-70135831711733364183],[217564204240026265558,-4046647175152548917323,2973661954716975054895,812446810265172383876,-1191728493570278044075,-588539223673637180580,-136249048124079430151,650946253927126135508,-1779583568760958352623,1211217358316203489122,-1420428801631712419043,767061423621346517512],[-150789677987337290612,2272850258331996941600,-1662774914921431741738,-403313974557443370714,624726317675055045616,325366196172197573568,22994115480705389708,-275282663320018004059,815944402773588863079,-561354558109661565265,713180036487818095902,-369511313047797255864],[-168334563658881011518,1053265557108179672272,-744999637010030822824,-4370363176760550769,135845893474291845863,77221126272854253196,92657379956942755832,-62906982992919321954,-36560894529299558578,44655880106666553126,39100534557047348507,39914534131417568229],[2859087308050323691,56150208419020532714,-42787093174250103676,-22170485488944859790,25709709993037100109,61226700409346275963,-275971729335518290229,242035508370427322399,-159856279440825089188,61221829127422199990,37106032870603746589,-23249386805264434496]] | 168958930175 | 2784594871998 | 151375636237 |
| 31 | [229857671852566915631124100559459791082418487347601609853795,529605047822409997790632062225093882226902048481517997648291,692890503637363901663257162986404589638429883949488810983264,194387686077629307125406099313967575354155550767986829964711,547354657965698485358298475464776782418059183274619504743581,437192505202981127958496903412896021241516340538101587121401,226622444595136431082174273609017230821094412363876829051320,527079201315979346981678714299235321201951891029705614486542,738234965394635148179763720903285300614308835241572145337605,174925355930816260143144986497868500932325858875268523687061,550103657911829857472452595200927388111980138735474995256219,603917866917337018205237749972984725705979094385500894856473] | [113854816265973644715296486725674566236955464212287530937619,131377001708395338935500432308029858012513221676762218154986,-1058772803257865127876097818480681955735028802009054474168476,432183344333777614816315902984765683808267341990041460618167,-24234033946375585168193135021738284853573820473685151193062,735364525098668442049370761092924650846549101531768485264531,134427584126462410446331599346844625769635862001741196842825,107823246319567031362852518234970796142474606331784291001529,-795909765808230841617544339737067237459595234848108163070209,393208221536653996156188693110474105131653939567252784007327,-3301595468922149655703149868237182406158591046179946972910,22122202587327367995200538362210732958846883823840285344508] | [-2366204351826923695935154810401441566340233574772789104615841,-400308387856286506099674875556258137754628133117967836825181,492319327859871773820607293440501949176567954583886944858188,-2376627138846729736697677696074865193190172221156911672160879,-494973741149972708579867829465600162335624229504309814250669,-2933542234096420376266860760844227919173848749590425408772018,-1780798973073294445222122712263902043679007750611667341514076,-626932258820886392665892499839277212989569054112609292853110,3444931764514095822876489308165780583827908862583977227510987,-2800844915488006313089326872400332067025026013486287732028604,-251851195476702485512968108287882706014664692574397232546405,-173898376783273143686474406335221812414742570685540967622509] | [[-76758348561084127316,580556430627294486710,-414805728003639154353,-32135581484235013052,99903751339415205429,4214233324598033406,-18993749766070396037,16657858808942210052,-11001980101578780742,4213559167333603371,2554237258161950865,-1600439923157990309],[-227036535192323707590,1576367435297461311387,-1121478214389882613502,-52740634524395556463,242208130420319808718,-67477170722958193614,304122813550321535096,-266721155700874615502,176160746789128257936,-67466376298131132821,-40897760105006557410,25625813667322401003],[-1153760174928437048751,-3395355110128795028139,3195102646312501615008,132786103091177276557,-756098086268477351980,135293649757817091923,-609774905779204245899,534783516199156024837,-353207316219836977194,135272006628500281948,82001174208144194105,-51380486495208017453],[438872113363182299149,1734481686063695622238,-1542699197258935326207,-76045368595383898492,367163496720570546260,-44598241889462373823,201006394570221086638,-176286208973153484553,116431372456119003361,-44591107441406283629,-27030893239270123406,16937079968005987530],[-118848858499040226769,1107566288245678924741,-750261204123122016368,-43531262130625050903,163675329340009517533,-23509315803999280114,105957602998945913362,-92926716010724716825,61375107820353629403,-23505554983273351828,-14248942978542399470,8928135838904540812],[501455772129653962724,-704410383682390966729,397334308793876171410,-718046958078909533080,516098129137003307910,-605123873886511124492,247463831177273238417,-28586425713911823933,1327922190206670951360,-1142584066687160406698,1125241523796138586107,-861052373369694448363],[-4244613762022709863,477645407368169308069,-356563319069441306659,-135654667230025308711,174137972127066020650,-83869432591529202903,19690780731911465662,9958925140439294876,182564852544101858458,-161527197523953885581,231214485920929378058,-136585329013798581948],[-185089883463006859041,1531832458903504642075,-1099015734334624449708,-117128667449181365114,290824988397747999551,-125944918159924866391,344035825314340479300,-284733978975706667638,306091341428198581488,-174395220105258831011,233789255738755901387,-70117950268849412269],[217681676390150619463,-4045423281183494258676,2972755447790783092754,811993808033937003609,-1191213810776196131995,-588633884992844220517,-136179441392480624360,650814891982433989411,-1778924660491509675294,1210731680472399931806,-1420183632490007362876,766890840023616924401],[-150840452818878884340,2272338769499976165154,-1662401167153597311303,-403137361035507746258,624523701181486679655,325437272270265069832,22984578129124163812,-275271501349027283717,815745673060428993569,-561199210219904603909,713140690982117594916,-369473740703338164105],[-168274345303375666048,1052853303404133207991,-744716005545633832728,-4380007071773491808,135803146362532213981,77216057727836768919,92636528325655235843,-62892574988059304755,-36532053590577880723,44629240405166302635,39115312131188825635,39902283912508665846],[2856379283588412942,56128096762474517323,-42770451291696640669,-22161324331770515543,25699735988803493184,61218370188109731659,-275914102252638888762,241981610547004394423,-159821072727364861904,61208576993049081377,37104315298758501566,-23248908195907977670]] | 168908706437 | 2784782256870 | 151277564139 |
| 32 | [229852758312136987566783704660039131163297550054643161365282,529599380259016129821280728162911515479338076021863107440257,692936176226692881087284739091628691473003192342696072675642,194369040835231741974030811485440495140077526167245963220484,547355702885245947520052883532552120396290400533472400616734,437160781159664257689495995302588286734945843608779437468893,226616644154709865012124055494259413967248017535704794439211,527074549576763824317021868458572199136230091900490735775479,738269301645139383196668675396105443407888132454743019145141,174908391558139643066961867531962967583790876997313687804243,550103800097920206764780761009854283433909855428808726989073,603916912473256881385230903485944190107864918268049129942716] | [113956884706375898771993073478635427175141868841085060652840,131394268254530168786436760145538354807289558253107521092300,-1058794039389671941930959828896685220230039589388857290889019,432285861766177060815130883747223814906350093134451475603263,-24212682670927822900578468208206349539434222660823833224950,735491027719437339168953065346487183645483266383024016904640,134504407226303557174255209449699660532123895106782119508361,107850285676306567431677837550739659668716103951545014846369,-796058327250448943528871151447558643326348964977951385298419,393329031320504119703302380159061408350945208716739098531914,-3290728531466741769290177906251890604433819320971332452183,22129703366998775865595630639731444732842267492503006297944] | [-2366103312920294771101402312031958071717712114229364993117835,-400238854469950444842824571148985467165886394875167263847679,492274037224154537043122984172731342182279336532846205773102,-2376497619851484429297126436523662710554464791037226033787279,-494958151172289699422438100175042036968095589115081064007494,-2931633553451990275951931270572160645754920521219079259513176,-1781032076068321503232569643295035514908120802214049311274917,-626722214105212855227639063671178071477273849147915531845985,3442980623055953481088378605708680913656130912513184103182540,-2800387629285461237839493116426823292034868788220542396117793,-251984165524518192512119579695355015110961676975770715296407,-173868247889292485461609208039319659253599519297244954187777] | [[-76740827803926795369,580362073353118414174,-414670096430205129568,-32123528384239010967,99870325018470296679,4210318205629828289,-18974723160111148468,16640941216895127504,-10990833471764651240,4209306125076361782,2552093331876953150,-1599137697022601216],[-226978748615287140462,1575826240145174338839,-1121102326476310139706,-52720692658355230414,242125708764460700750,-67478864723769797700,304108315514025604448,-266704739739046227089,176150335632825071693,-67462644085941140212,-40902457318757059639,25629415892551700539],[-1153387541519810852996,-3394101904180385631539,3193947525946414915082,132737689951370666499,-755824642748124407532,135278967425863473261,-609664360489225639857,534679146532419577275,-353139247580343660762,135246448930695656260,81999633721057440754,-51380842458825435481],[438838191627633602625,1734083848478116194262,-1542380093189312459735,-76025702110556751327,367086705912398216434,-44606469070046489317,201028844001015137263,-176303451053969302416,116443045244596296786,-44595746521844732693,-27038306064377789889,16942160363461978089],[-118767417886024838711,1107134697688592362152,-749982181544421138736,-43515182174383049789,163615616939148213607,-23504293811274235979,105927259261898566237,-92898814900746010757,61356830181081135169,-23498643825328388613,-14247177666053969719,8927259280603713785],[501129537408524320467,-703874775985524141596,397020435003469212749,-717632374140890651979,515831078393780560454,-604846845327263318436,247359104453018844811,-28577289689084216440,1327358014722506055663,-1142117063168894926469,1125013150183989351054,-860891174005492516634],[-4240541193173638859,477476145613329413244,-356442611901184637489,-135629422800390320945,174098717311379897237,-83872477441236363114,19708926059450643484,9943177360815508090,182580113969609596637,-161538197330957220631,231253320614351856432,-136617141388245683249],[-185058523873419725274,1531319284560987831372,-1098653909888799833193,-117071160164339494177,290715795337136431178,-125918862427146883371,343999235252149851152,-284705516763017274952,306022082210724677155,-174346052711963760351,233764492879979211465,-70100071398973167504],[217799010739953993116,-4044200168680999347175,2971849538380463331960,811541190364991595073,-1190699530950818830131,-588728467812081595939,-136109858137801895228,650683550964339228339,-1778266037103218030224,1210246224793738021019,-1419938537365533711752,766720303328815341848],[-150891188386968888787,2271827650525332688322,-1662027697360203623331,-402960888691472238916,624321242815262142010,325508325471417597094,22975041127106735830,-275260334733740289875,815547010551360736213,-561043917781507739675,713101359927099428655,-369436175424929881808],[-168214177258620168825,1052441378204087178953,-744432600666502800778,-4389640328347051408,135760431421147984373,77210992204851680213,92615684274181408243,-62878173381331268859,-36503228268365247194,44602614927088047119,39130082864458203221,39890037861213369519],[2853674639884423338,56105993008849989851,-42753815752914202263,-22152169802474108486,25689768190059388912,61210042408499574869,-275856491741388521551,241927727990128563122,-159785876044215345062,61195328676526616899,37102597344247289938,-23248429565465882916]] | 168858524812 | 2784970413049 | 151179542337 |
| 33 | [229847840368889343245382486782855292604748674954282954727756,529593711950862425340713977871358468461959716624628449895631,692981849732039702184109478124689067940418991227601936173613,194350391170674853884708520133945331305391823440282534093631,547356746883780999642330313339837119390552978233428497704705,437129051661197317786597300458304300479716661507615939106341,226610840400159419531729834270562871595648269203389555410984,527069896671350828717196753079133310009433125105332458128532,738303644302302407893962110664067380056682229102309513417263,174891421974534032585891150502902272107218435448622307827792,550103941815121348534302102605888069794169695630394933852148,603915957705644718217242322338088656590658901190185684527889] | [114058948786692268188467863699092220577843699552829711946606,131411531800786652356889231804872856897262639987205221524329,-1058815273567308226789074792132199732713604748927969781640659,432388373609997388233917931014985879682728231119396193341945,-24191332068440775971370558823569833112129001057909767303420,735617448033477796200227381018396277351415165948651665739948,134581240375153734374984352233971226656999458432817433674069,107877315974120645003142674347411776587691779745135652439547,-796206804553826925645895784216303701353100267793203412279805,393449821381767048893472966363452636039359101314360879947880,-3279855860673209233055479486215067775941549755304253993641,22137202846727789513913369001401607481415508163809328503278] | [-2366002200528736340282815228795507487679699538134975287780974,-400169301306413818229524339217571273092288366591490151434920,492228724573669324814080988527348668284055049112240347704057,-2376368029610460191368723201843491144785438892991144700518397,-494942539956942094929634533241373001467768121102233239102337,-2929726159583871970567882988151396717430161953253537937994168,-1781264885988839335691877899615468624330879613109829365679812,-626512250216142366616330738163092630896353448618978940163792,3441030745859341334578463554367972133913601502300494411079563,-2799930496181742171881185644654437833325794487958284179273558,-252117016339582521354327044082346585596001408715810208867998,-173838106171697778320331107854957297663909988782969370716728] | [[-76723320045656434045,580167856828310621957,-414534563774410358854,-32111483888854124540,99836922929049336599,4206403450341446526,-18955700768676851213,16624027738097963892,-10979689512286394207,4205054078617557276,2549949134364117249,-1597835250680219643],[-226921007159850661893,1575285457238563607631,-1120726727028045295603,-52700765939332946306,242043350203914690643,-67480558923039194099,304093817378446146215,-266688323305720431210,176139924245824572667,-67458911841583990325,-40907153781989931457,25633018101029600045],[-1153015213875880347727,-3392849675395842688965,3192793313006542543711,132689314671307530284,-755551413992777574405,135264289291035112020,-609553843980532158466,534574803319388292057,-353071196343540491946,135220897873788513291,81998092066051000182,-51381198246658652276],[438804306074675534896,1733686303620504116492,-1542061229886761745094,-76006050167093042985,367009972923739119004,-44614694325398756068,201051279436734888409,-176320679827320573412,116454709388059524169,-44600382382261735179,-27045717919838522755,16947240589976769293],[-118686047461480154841,1106703443010230762067,-749703375951672484472,-43499114317982721961,163555950639701759206,-23499274395412277046,105896930472588550444,-92870927381632519914,61338561474578606227,-23491736065631164386,-14245413001908400818,8926383176903527897],[500803605642893358278,-703339761742507059570,396706922669564398962,-717218146116315408433,515564237572158356009,-604569950582075085234,247254411634711836059,-28568143186416239451,1326794100476470989999,-1141650278291783094982,1124784856732501022984,-860730024746864715054],[-4236477313929966851,477307011857880231495,-356321995398094344487,-135604190716279914144,174059487984485405286,-83875510341423528484,19727061380612794205,9927435336341067499,182595348559207748276,-161549176611045666763,231292145611910106290,-136648946872109039682],[-185027185957057875167,1530806492589368437373,-1098292357663916389907,-117013699188420625517,290606686446165641632,-125892819725704803078,343962656502017697794,-284677060974055311984,305952849709321622842,-174296905414355720057,233739734019083430035,-70082195102950737127],[217916207457073069422,-4042977836862850350702,2970944225881203922211,811088956825315591839,-1190185653654477697204,-588822972170014318300,-136040298375531607069,650552230904815689243,-1777607698553096956112,1209760991235601710601,-1419693516268248547160,766549813544209310996],[-150941884734272636138,2271316900983278871132,-1661654505223148061411,-402784557364252400684,624118942396054887467,325579355777623371131,22965504482691227983,-275249163484089607155,815348415247097879545,-560888680792028003404,713062043323956819597,-369398617214439304527],[-168154059465372329716,1052029781121358650806,-744149422106024547023,-4399262957904081550,135717748611270996187,77205929700757356359,92594847803573081732,-62863778172266739090,-36474418557483639049,44576003668050794311,39144846756438825306,39877795978163859538],[2850973373642811019,56083897147759450914,-42737186549539533130,-22143021893418513794,25679806589447760466,61201717070936069829,-275798897804659096647,241873860702514854430,-159750689393127429382,61182084178503393750,37100879007210561891,-23247950914019215378]] | 168808385263 | 2785159339791 | 151081570859 |
| 34 | [229842918023012131436196718295713665595342510364854934029885,529588042898078308071711266708843453720377617708914147495883,693027524153320047697574724662656923238425705206049674839215,194331737084199782879732338233179353281782983414911294815766,547357789961332690893976223547618299720763761851209067821097,437097316711129564839546644694648244496320534212949763716580,226605033331051884609827532852298887785419609822010702761932,527065242600131058569751188524624139132673829611455581101921,738337993362495913195175835701514120507200009907881023448313,174874447180850056716924215464635604412175817123800323664640,550104083063186075510118215126117695571293021788907728291663,603915002614556616060959796720490112499951968801817655802175] | [114161008503753063419899329336935549486829651882659834465024,131428792346311792357486986206918738070302463589498084039922,-1058836505789824435328899063373167570114128532911208990235965,432490879862165565316915427483031011517863225262170007756270,-24169982139830509371139675520390695741257623425050331695346,735743786096283236950100882719577623627641841513330779262192,134658083560373256128698566121223827995998860224645952924226,107904337216494919656776391311750346138247199693677362229835,-796355197772887059157105626233493458739218514143705913278535,393570591727044863081752994471178928351986679208890883933545,-3268977461683764215324827045934881609207723557367593061018,22144701025961297171377832626311830014369934094374619691085] | [-2365901014662420870337849546622092913338610195835217575090743,-400099728371657509408664835097030644749290524811157313050113,492183389913089277960137994232332488940495860668057910618599,-2376238368136976153568144409766942477595032799109309064338560,-494926907506763915042960756422112574451279072446173466455143,-2927820051840022162346768631541481306152625117885638096231188,-1781497402956674766893324028364132545767982651987984721890962,-626302367109621696049167041865799691216996722418887082527544,3439082132275197739965714385073831530581677023247517706738552,-2799473516078416123679346445426699109278762761307275164210210,-252249747973550881117796474222948818522606121321162132229690,-173807951633208078730075804547222295456904132902128048413188] | [[-76705825270273139724,579973780888481773237,-414399129920733709483,-32099447988155883822,99803545042915946783,4202489058894533803,-18936682592353724698,16607118373074308077,-10968548223481904329,4200803028080869000,2547804665902467052,-1596532584248467438],[-226863310772642469859,1574745086100083743584,-1120351415711268442660,-52680854349891302299,241961054665728045491,-67482253321682633422,304079319151317730853,-266671906408191148348,176129512632878361050,-67455179566847964068,-40911849494219013132,25636620292573972266],[-1152643191644375659769,-3391598422645395833758,3191640006444169563919,132640977207226127867,-755278399754222806224,135249615354080285714,-609443356259889519137,534470486566553681432,-353003162513608369093,135195353459325162580,81996549242958437055,-51381553858622435018],[438770456664948611830,1733289051149748919446,-1541742607071608040534,-75986412748205842852,366933297687492187638,-44622917656694465457,201073700887121386979,-176337895302363544842,116466364892491834293,-44605015024918285451,-27053128805007302009,16952320647299721773],[-118604747143862784098,1106272523822355067753,-749424787094094741362,-43483058547465500845,163496330388381487745,-23494257555791483831,105866616626971903604,-92843053449652405271,61320301698391692767,-23484831703248357513,-14243648986038218524,8925507527773006669],[500477976472108798146,-702805340144819364666,396393771288730882298,-716804273605206625861,515297606455600805166,-604293189620669023811,247149752738135448251,-28558986230291994639,1326230447419336443992,-1141183712009519097345,1124556643451524640355,-860568925600770202130],[-4232422112764760201,477138005945935869328,-356201469449651918469,-135578970961747509057,174020284114281254208,-83878531300909806155,19745186698367275177,9911699066893251042,182610556329419980558,-161560135377399320396,231330960914011681061,-136680745463934721225],[-184995869688091490495,1530294082552484238431,-1097931077349803371222,-116956284468965422084,290497661629267038448,-125866790053412859548,343926089067285790107,-284648611612814271971,305883643921978986299,-174247778209708143026,233714979156872590322,-70064321381624483844],[218033266708906973978,-4041756284947967285173,2970039509689069793661,810637106982510616583,-1189672178448136511530,-588917398105338546979,-135970762121099223500,650420931835764817583,-1776949644797951078747,1209275979753229269465,-1419448569208039803031,766379370677019938418],[-150992541903393912080,2270806520449678548915,-1661281590424814844662,-402608366893003926945,623916799743809292545,325650363190870483483,22955968203898835948,-275237987609992932009,815149887148291147925,-560733499248976093892,713022741173871537908,-369361066073724956444],[-168093991864479290224,1051618511769862090113,-743866469597998197295,-4408874971853348867,135675097894096000557,77200870212412016427,92574018914876059919,-62849389360393398894,-36445624452746612199,44549406623665885831,39159603806719541251,39865558263988497355],[2848275481573136362,56061809168831341221,-42720563673222132085,-22133880596978357227,25669851179622880319,61193394175837245196,-275741320445326673071,241820008686863521786,-159715512775842330766,61168843499624339635,37099160287788792777,-23247472241649059291]] | 168758287749 | 2785349037227 | 150983649732 |
| 35 | [229837991274693637629480842497818671641626211854941857570264,529582373100793238527108954562260439449135889759301734877436,693073199490449559415393893312784150232237179631839562403070,194313078576047801529932808699104566678288976442727964013947,547358832117930109957363234015793437989670169402616535211825,437065576313007862232953734413615842237469003756476125234506,226599222946954595338211114650106260960487840971604566142007,527060587363495061943001216684044324315338526526956422486024,738372348822093941339280677874780270010928200470457534909015,174857467177938058775695900580182460323423991748525955665054,550104223841867402192133091421695409976341479647933053762109,603914047200048686133044254571001389518381663442675031327360] | [114263063854389033931272410763476968280439065069171475789884,131446049890252849553552603690835902723036428875934601977144,-1058857736056271222073081315639851711596380039742543763852302,432593380519609135045184065934810231958150576015781970476384,-24148632886012965782144028509174109479953514074112817154500,735870041963318950580907760929771885783812275920705654224789,134734936769327693299360718326299986343005436126512759027700,107931349406913146058833339270069382886056076131231919438046,-796503506962123609272198555869784743898785023136906789294153,393691342362935394367447164351048864557845589789675821627229,-3258093339638389933934130191443050994850446265008225337662,22152197904146304394841040776124606084606977628747953171924] | [-2365799755331530172548684773867050491865232734417326718499092,-400030135671665099244109972764686793085363518345911397594080,492138033247090299612874560038075473921220475507690860818606,-2376108635444360319268985053294788993036130594040595354315139,-494911253824591850047963448868865988191959556398600025184585,-2925915229568048051189434085517102183914540539619036138473835,-1781729627093726768472290488692708480235642755153543101118604,-626092564741570038189875768118136215955061399238190460157202,3437134781654113711171513960335425111265691004133024223583419,-2799016688876996109942465929646412684748892185385913433222771,-252382360478111036826670768715954462282296371673669944518971,-173777784276544023001055703342363392211953883262383300595333] | [[-76688343461801530223,579779845369495085905,-414263794753831428205,-32087420672235097884,99770191331877132795,4198575031450347191,-18917668631724918749,16590213122344852946,-10957409605687188308,4196552973589266275,2545659926771092991,-1595229697845004056],[-226805659400372824837,1574205126252923156612,-1119976392192672784617,-52660957872619684512,241878822077059110131,-67483947920614420411,304064820840361621368,-266655489053739971056,176119100798729935907,-67451447263518263611,-40916544454958177389,25640222467002693288],[-1152271474473568125616,-3390348144801009625497,3190487605212191454366,132592677515431915215,-755005599784627207170,135234945615742538810,-609332897334030421725,534366196280376557873,-352935146094708068072,135169815688844292746,81995005251613347722,-51381909294631545103],[438736643359153520431,1732892090725264165629,-1541424224464605564473,-75966789837134009390,366856680136659374034,-44631139065107823458,201096108361908614533,-176355097488247979371,116478011763872092790,-44609644452073738376,-27060538719239149395,16957400535180192260],[-118523516851754287802,1105841939737322533008,-749146414721291845032,-43467014848894289204,163436756131980616698,-23489243291789254484,105836317721000009421,-92815193101069494229,61302050850063210810,-23477930737245576961,-14241885618375847399,8924632333181132988],[500152649536052610719,-702271510385250152550,396080980358363126729,-716390756208158317926,515031184827861364917,-604016562412682729208,247045127779005975542,-28549818845059167463,1325667055501691796769,-1140717364275656777987,1124328510350842051686,-860407876574121616899],[-4228375578164334318,476969127721851124639,-356081033945510378877,-135553763520878468311,173981105668721626047,-83881540328515024954,19763302015687970655,9895968552345375488,182625737296774491762,-161571073643201483293,231369766521075652822,-136712537162277161620],[-184964575040732319393,1529782054014840081223,-1097570068636763938227,-116898915953591733062,290388720791015703558,-125840773408076342525,343889532951280191721,-284620168683275304331,305814464846664166620,-174198671095279697573,233690228294145339962,-70046450235833032117],[218150188662617679334,-4040535512156401812183,2969135389201000964721,810185640404799355373,-1189159104893390107501,-589011745656781446975,-135901249389875412339,650289653789015766019,-1776291875794376627744,1208791190301713667508,-1419203696194726384751,766208974734421975400],[-151043159936875064969,2270296508501045771144,-1660908952648074087370,-402432317117122207200,623714814678740143226,325721347713166854711,22946432298733852644,-275226807121353088473,814951426255528331949,-560578373149816478311,712983453478013921826,-369323522004637004278],[-168033974396877356133,1051207569764108220249,-743583742876634392835,-4418476381589556214,135632479230880535919,77195813736673736632,92553197609130149926,-62835006945235097756,-36416845948959325281,44522823789537021474,39174354014894696314,39853324719311831897],[2845580960390054117,56039729061710011040,-42703947115624227628,-22124745905539992556,25659901953250298552,61185073723618897919,-275683759666251487635,241766171945860071050,-159680346194091606640,61155606640530728967,37097441186122483090,-23246993548436517978]] | 168708232233 | 2785539505485 | 150885778982 |
| 36 | [229833060124122284017521278211589967635053100331282608249816,529576702559136713998666127883245795073312259457863628623571,693118875743343838177851335063654647241512381213168673000910,194294415646460314929877310178128529369505463961016751531213,547359873353602385023112645409073505142291524829769315339804,437033830470376681360256815739739237813107975090161529240716,226593409247435431704804442565378141932953558954190142059103,527055930961833236668056128476011877611086094206180517105741,738406710677472884672274070301159085063201755294523961072995,174840481966648097559747886522615952120345906664834641859186,550104364150918564754873152121425478004352904432951495917124,603913091462177063502067233045312340024399814117301672944035] | [114365114835431368600401515444275206436392956551999485514511,131463304431757342881441568865250067873470593233852730103108,-1058878964365699443307590199107451580445079285301099771630490,432695875579256215519265696258487885389853081371145191254761,-24127284307903965463158881088336516641631158841151251588557,735996215690022076580077889618785075011859569343448286257349,134811799989387876638846304478801402806771250026213547249620,107958352548857176776451339170784092852813715371288062719852,-796651732176002820284888230589340144068446049498818988021435,393812073296032225273017377389300123736222981423498843568553,-3247203499674839264179787771470150223208722574994715741169,22159693480729934134917533414077676070523476203175779404300] | [-2365698422546255399557335157132235544019673910611092467661725,-399960523212422864854894939244466344396158013300547006537135,492092654580351053841205160886435529561191389453411131469740,-2375978831545949560745676463293383511479991811477372706623946,-494895578913265259676435390905701267579952542607867889024448,-2924011692115209471264791208801673150007739775925384700824691,-1781961558521966084912969937576778250294852010060455386161749,-625882843067879181759015744003607752711675883714733122364823,3435188693346335054943855783318210398383777385183191712953559,-2798560014478941523597937399919716712002543835037230456754126,-252514853904982938702457227346759633693221276446634155503091,-173747604104427826596675463063557229186744547688296378480381] | [[-76670874604290697816,579586050107465847759,-414128558158536800702,-32075401931197825462,99736861767783200864,4194661368169755966,-18898658887370518379,16573311986427400778,-10946273659236368387,4192303915265009936,2543514917249151982,-1593926591587526539],[-226748052989833892365,1573665577221002632109,-1119601656139463382967,-52641076490134215586,241796652365178091972,-67485642720746916187,304050322453285788508,-266639071249636178051,176108688748114704420,-67447714933377015894,-40921238663721329497,25643824624133642578],[-1151900062012269252296,-3389098840736380219279,3189336108265111017586,132544415552297415302,-754733013836538300219,135220280076760690539,-609222467209654602368,534261932467287084060,-352867147090980275071,135144284563876983916,81993460091849360275,-51382264554600738163],[438702866118051003222,1732495422006986443484,-1541106081786937071105,-75947181417142140607,366780120204345450105,-44639358551811950783,201118501870823487861,-176372286394117155520,116489650008174882480,-44614270665985809459,-27067947661889128510,16962480253367533627],[-118442356503860939908,1105411690368085577390,-748868258583252239323,-43450983208353417916,163377227817374090384,-23484231602782306704,105806033750619611046,-92787346332143293037,61283808927133150351,-23471033166687365384,-14240122898853610832,8923757593096849116],[499827624475140041419,-701738271657895481052,395768549376679331512,-715977593526334661099,514764972472982333832,-603740068927669026492,246940536772972890376,-28540641055029067303,1325103924673945588911,-1140251235043610018284,1124100457440166034337,-860246877673785158108],[-4224337698628237769,476800377030221034782,-355960688775493949791,-135528568377790023077,173941952615816060873,-83884537433059716849,19781407335553276845,9880243792566804696,182640891477803970435,-161581991421638630715,231408562433532591580,-136744321965699144363],[-184933301989233592454,1529270406541606596940,-1097209331215574250407,-116841593589994451135,290279863836130121300,-125814769787491619602,343852988157311285202,-284591732189407232944,305745312481322443962,-174149584068314323073,233665481431694950369,-70028581666411274458],[218266973485130408396,-4039315517709335041918,2968231863814810853872,809734556661024434478,-1188646432552463214714,-589106014863101046898,-135831760197172150374,650158396796325493025,-1775634391498761952488,1208306622836002960892,-1418958897238058288039,766038625723543897144],[-151093738877197114745,2269786864714543543219,-1660536591576280860809,-402256407876241876827,623512987021332123845,325792309346540187713,22936896775183692002,-275215622028058043904,814753032569334418679,-560423302491967492475,712944180237542898033,-369285985009017271193],[-167974007003591830536,1050796954719202879911,-743301241676554501748,-4428067198493364213,135589892582944803625,77190760270400457673,92532383887369170989,-62820630926311858591,-36388083040918567486,44496255161260283471,39189097380564122242,39841095344754605883],[2842889806813303561,56017656816055689734,-42687336868420753529,-22115617811501479042,25649958903006821202,61176755714694597113,-275626215470277981736,241712350482175285386,-159645189649597172286,61142373601860189055,37095721702352158440,-23246514834462713838]] | 168658218676 | 2785730744695 | 150787958635 |
| 37 | [229828124571486629475672841080356948143512313770065438882431,529571031273238268545925404564059492999323217293287661000772,693164552911918443886508341156527867109531560548488240747073,194275748295678860673052959687392456047019773545668633407863,547360913668378683784810991528245525394336128255237342023515,437002079186778102838333708564121439504427399968894715021184,226587592232062818366699583764106755183649291829839546538891,527051273395535830420894488076077643661667708771671269468106,738441078925011484438125280939722490350386333064086234627239,174823491547829947531891863521832423642701234513477502256631,550104503990093020951247385791536525560283494155556599886598,603912135400997907083445411518042523672710094106584820092279] | [114467161443711696120821292859818794430397441804197863209397,131480555969973049564818745763476938417196342641933916142925,-1058900190717160157200782989745703620817069562268960695199017,432798365038035500341677461179630286812763396646431104972338,-24105936406419206134344405518357297382788770661034210945207,736122307331801589821865198433732513157692747882069397973150,134888673207929899874936677598548249304156462074050166358533,107985346645806961099075086734291446972830845410312081632503,-796799873468962900727722694437917476114969286887452379029359,393932784532924686438842575228416134606786596248877764207498,-3236307946928633354126229166435808075775450077380158307035,22167187755159426804089196263475550626077594719082983618590] | [-2365597016316797042299108280767572984378163727169065388914032,-399890890999919778154662747490757406378867922605490803026367,492047253917552964282993287017309344802226116343374004743239,-2375848956455089615353884435269957542456323583806745064262732,-494879882775626172207867253905724292422127131537996743851589,-2922109438828421022673776076750758598136018053985842037446586,-1782193197363434859907642188411312054418427060699892478393536,-625673202044413677755107188211622469420542379630431233591462,3433243866701764501445734122265968902373136630119134438370305,-2798103492785658500909609445598493755594020587895110870817450,-252647228305918551803315077197803657935378129011509844327533,-173717411119583283443527805185789983456498298046863275946198] | [[-76653418681814162358,579392394938760932824,-413993420019859811838,-32063391755165345683,99703556322527674782,4190748069213242438,-18879653359867549553,16556414965836868604,-10935140384461685867,4188055853229653665,2541369637615867367,-1592623265593769502],[-226690491487899585970,1573126438528973925571,-1119227207219356174696,-52621210185077703351,241714545457466846318,-67487337722990540492,304035823997784925960,-266622653003136748292,176098276485759991135,-67443982578203276137,-40925932120022407366,25647426763784703006],[-1151528953909829680627,-3387850509326932042675,3188185514559035295341,132496191274262089393,-754460641662883297071,135205618737868842705,-609112065893428887250,534157695133684822817,-352799165506545619356,135118760085946720154,81991913763500134611,-51382619638444764077],[438669124902461742889,1732099044655374363650,-1540788178760213027910,-75927587471520524637,366703617823757810625,-44647576117978883024,201140881423585859562,-176389462029107868171,116501279631370503708,-44618893668910574976,-27075355632312344910,16967559801611094913],[-118361266019013487817,1104981775328190644078,-748590318430348138378,-43434963611948604836,163317745391518423120,-23479222488146679665,105775764711772824415,-92759513139128999212,61265575927138683495,-23464138990637202198,-14238360827403731070,8922883307489056703],[499502900930318638729,-701205623158155886225,395456477842719858248,-715564785161468969517,514498969175294348365,-603463709135096204289,246835979735618963570,-28531452884476667578,1324541054886325993650,-1139785324266653113566,1123872484729140413157,-860085928906580663308],[-4220308462669236428,476631753715880425657,-355840433829597736658,-135503385516631199917,173902824923629342443,-83887522623365098459,19799502660946086969,9864524787422957874,182656018889045554636,-161592888725900379644,231447348651824544568,-136776099872771788708],[-184902050507889939018,1528759139698618920430,-1096848864777482556426,-116784317325945370065,290171090669471907047,-125788779189446158317,343816454688673798202,-284563302135166574420,305676186823877029186,-174100517126041265536,233640738570309326073,-70010715674190377711],[218383621343134036992,-4038096300829075341323,2967328932929184595496,809283855320647299680,-1188134160988209299743,-589200205763086097234,-135762294558242828015,650027160889378861428,-1774977191867288037262,1207822277310900676693,-1418714172347716717690,765868323651467981881],[-151144278766779861626,2269277588667982571177,-1660164506893274257241,-402080639010236369862,623311316592339307161,325863248093037921122,22927361641218912703,-275204432339980924719,814554706090171721693,-560268287272801440962,712904921453606002001,-369248455088699250681],[-167914089625736847248,1050386666250845884252,-743018965732789832256,-4437647433931412734,135547337911671543838,77185709810449992051,92511577750620963053,-62806261303139885139,-36359335723412786339,44469700734424160685,39203833903333127871,39828870140933762124],[2840202017567698677,55995592421544455367,-42670732923299324474,-22106496307272558967,25640022021580488661,61168440149475687928,-275568687860234828125,241658544298465250123,-159610043144071317145,61129144384246706290,37094001836618369525,-23246036099808788333]] | 168608247040 | 2785922754988 | 150690188719 |
| 38 | [229823184616975369543377788278116112136506182876956499243308,529565359243227472985068724370889856539861309872287148377001,693210230996088895512914281930599885230618426717903953979994,194257076523945108827033019214637363290357893296937670683632,547361953062288213433721626038804414224787821726089491946889,436970322465751817722755248920541866745736022594349506486543,226581771900405724423062255496625775345678147727775850672685,527046614664992940804490840843003935083795428191393403938060,738475453561090829569082247969407896623808516546733939266964,174806495922333099003671797928807698067545926766320970657045,550104643359144450016247916196973094081152991248766573149330,603911179016567399634372207397822180215478582984088450833653] | [114569203676062085404545071285825340128834381061567752494812,131497804504048005230871832471015283221384834005040967136624,-1058921415109704623922415193001574922614016049960802306859566,432900848892876258999241112065083905861784976759770019031673,-24084589182474262862152315636351352744922652200308572276671,736248316944038285720923013413965052079622348631093410222213,134965556412335122783212956457537662275065557719293193742549,108012331701240543867127704451408321733375784528942341178828,-796947930895414008618703546803542065250175048456947514048853,394053476080197854333796397309533074523514595105606590381616,-3225406686533060247253926058825972431899438083851569463014,22174680726882140344780312207315772442889750607076096182094] | [-2365495536653364926933412779268190045956631877568743587159292,-399821239040147504390340036851689531963184147029429582598865,492001831263380212775872319560901642178733866459605418259671,-2375719010185135081708389756518778681886339154207914248152503,-494864165414519283570148628918388970117593838223644909790921,-2920208469054254198185314418932024828279464206464129729240560,-1782424543740246263567259368043940394586884713596813735302777,-625463641627011007287162513238315848479518745909736598513670,3431300301069963829915048757408334601711947570155515117378034,-2797647123698500287738804140897830997429881175827889592772245,-252779483732701686050631364425311025500589476129194565567652,-173687205324735765240969947791978628781549748476543464491683] | [[-76635975678469824521,579198879699998318779,-413858380222986806684,-32051390134274128854,99670274968047212990,4186835134740902772,-18860652049789984959,16539522061085293561,-10924009781693504620,4183808787604045325,2539224088150528859,-1591319719981505108],[-226632974841525410445,1572587709702218360461,-1118853045100576992280,-52601358940119589627,241632501281418662179,-67489032928253773934,304021325481540465528,-266606234321486375052,176087864016385047207,-67440250199773031350,-40930624823375381632,25651028885773760884],[-1151158149816138150863,-3386603149449814480331,3187035823051672491080,132448004637832208625,-754188483016968369756,135190961599796387474,-609001693391987246321,534053484285938786981,-352731201345504706005,135093242256569401864,81990366266399362487,-51382974546078366997],[438635419673266247196,1731702958331407557536,-1540470515106470795062,-75908007983585090434,366627172928206276321,-44655791764779570804,201163247029908518638,-176406624402350429079,116512900639424974703,-44623513463102472114,-27082762629863946221,16972639179660221369],[-118280245316166913742,1104552194231777060364,-748312594013334790422,-43418956045806913769,163258308801451542736,-23474215947257735922,105745510600397151572,-92731693518277513921,61247351847614172572,-23457248208157506660,-14236599403958329251,8922009476326616794],[499178478543067284626,-700673564082733903926,395144765256345661453,-715152330715862672123,514233174719415880287,-603187483004348247914,246731456682460384258,-28522254357640645858,1323978446088881287307,-1139319631897921149496,1123644592227340179001,-859925030279281687854],[-4216287858813297629,476463257623903461803,-355720268997987403763,-135478214921582747810,173863722560281384136,-83890495908253052595,19817587994853776367,9848811536775317815,182671119547040791290,-161603765569179457080,231486125176405015569,-136807870882074535691],[-184870820571037303667,1528248253052375412323,-1096488669014208287009,-116727087109293042599,290062401196045536457,-125762801611718548225,343779932548646829580,-284534878524497556352,305607087872229113427,-174051470265675113133,233615999710771014066,-69992852259997789327],[218500132403081495578,-4036877860739056147494,2966426595943677359706,808833535953747098112,-1187622289764109410549,-589294318395555928902,-135692852488282353820,649895946099788736880,-1774320276855929015573,1207338153681066196930,-1418469521533314206178,765698068525230389886],[-151194779647981994549,2268768679939820009320,-1659792698283376456093,-401905010359217472793,623109803212784645589,325934163954727182774,22917826904793241909,-275193238066980032125,814356446818440010952,-560113327489644697100,712865677127339398315,-369210932245508120436],[-167854222204515204584,1049976703975329888611,-742736914780780847750,-4447217099256342345,135504815178505911726,77180662353680031378,92490779199907395354,-62791898075231569339,-36330603991222115422,44443160504609572787,39218563582812489738,39816649108462449826],[2837517589383118355,55973535867868204382,-42654135271960211769,-22097381385274635215,25630091301670554132,61160127028371295409,-275511176838934957633,241604753397371377580,-159574906679216721110,61115918988320632323,37092281589061692107,-23245557344555901983]] | 168558317285 | 2786115536495 | 150592469260 |
| 39 | [229818240260777336405167492342468600271840167202210689018639,529559686469233934877768127653796943285611635030693450541525,693255909995770671107322878094429391325515567746101573320683,194238400331500861908626813389803727350583925258608480127408,547362991535360220653491345270358861436628501019797560412772,436938560310835128723677182286766780398301156694485411733679,226575948252033663187905105645685643680750556840727306625024,527041954770594515430992792643082859674260258148687059692637,738509834582094355475343976858916845753508430010455862290802,174789495091006758318924616762869250897832602217317088999817,550104782257826752570591312948880256754860869298924451546420,603910222308941747748746436041093632895556231115072235543330] | [114671241529315045984690842119538463027844024831542710121443,131515050033130504026461762424140700717825180037499239210577,-1058942637542384305762591068280334662905563688363655770926409,433003327140708337245247396240646387633825424055833113904158,-24063242636984587944271308585781786955185464433838293308643,736374244582084765477513946016061044285797120639909230858193,135042449589990174242887308818227592920217443579338731106093,108039307718634064307913690321302348349224202357806269644016,-797095904509738236799493231000252396355611144171010805953082,394174147944432548981605736368899185853467789466383044953831,-3214499723619173512431180611470076991210468276082212998162,22182172395345550297402820946358558496049938639415444523008] | [-2365393983566178211771916893073287380863074069457345416276486,-399751567339100400680052830556626155112088640116829693650933,491956386622519737987272905548483324193085054700442720905774,-2375588992749449415858453171036878491413872179772842813050229,-494848426832791956439518793062534074707598482921097441317402,-2918308782138939505051615215485989157560405926796837758782363,-1782655597774584120482074926928407454230445553106473832023390,-625254161771481749019190368355965938001055407914164291394973,3429357995800155989403346062261041422503339959840472748752686,-2797190907118767604950068796753011396750517246662711300051289,-252911620237147826642313576234911988664473121450876761716185,-173656986722612220770281027605193597481188381509438139260126] | [[-76618545578379919137,579005504228046605496,-413723438653280152328,-32039397058675807316,99637017676321525852,4182922564912447811,-18841654957708749766,16522633272681838239,-10912881851260314603,4179562718508328295,2537078269132492485,-1590015954868543055],[-226575502997748305500,1572049390266845429295,-1118479169451860585949,-52581522737955899133,241550519764638048584,-67490728337443160231,304006826912220592304,-266589815211917479982,176077451344701059633,-67436517799859203835,-40935316773294255751,25654630989918705992],[-1150787649381620470717,-3385356759983898566204,3185887032702328899483,132399855599580725884,-753916537652477923916,135176308663268015162,-608891349711930846957,533949299930387489239,-352663254611938148590,135067731077253358192,81988817600380767586,-51383329277416285359],[438601750391404734158,1731307162696585678194,-1540153090548173806713,-75888442936677358575,366550785451102897425,-44664005493383879920,201185598699497191104,-176423773522968667404,116524513038300031934,-44628130050814299117,-27090168653899122245,16977718387264254485],[-118199294314400196613,1104122946693575900771,-748035085083349743237,-43402960496076713523,163198917994292634442,-23469211979490163325,105715271412425493964,-92703887465835454358,61229136686091178248,-23450360818309640931,-14234838628449425426,8921136099578349841],[498854356955395227179,-700142093629631596914,394833411118236722610,-714740229792384292092,513967588890252735246,-602911390504725072130,246626967628946879693,-28513045498723423959,1323416098231480318974,-1138854157890410377848,1123416779944271607103,-859764181798615583819],[-4212275875599574360,476294888599603197493,-355600194170998852405,-135453056576857065359,173824645493947115152,-83893457296546109856,19835663340268187613,9833104040481439132,182686193468335595614,-161614621964671668408,231524892007738944263,-136839634992195134164],[-184839612153052862918,1527737746170036384099,-1096128743617941149931,-116669902887962638697,289953795320998075347,-125736837052078522922,343743421740493875502,-284506461361332135551,305538015624257917595,-174002443484415831668,233591264853857213127,-69974991424657243632],[218616506831190170110,-4035660196663833786311,2965524852258712676159,808383598131019562578,-1187110818444271023521,-589388352799360312098,-135623434002427258904,649764752459096086247,-1773663646420452683672,1206854251901015141961,-1418224944804394732135,765527860351821242413],[-151245241563101199389,2268260138109158210763,-1659421165431391792303,-401729521763534879371,622908446703959463608,326005056933694743249,22908292573843598968,-275182039218898857852,814158254754476642494,-559958423139777802804,712826447259867900967,-369173416481260756211],[-167794404681218199521,1049567067509539254849,-742455088556376383650,-4456776205806815719,135462324344955353930,77175617896948153653,92469988236244374997,-62777541242095498702,-36301887839118402053,44416634467389894373,39233286418618442702,39804432247950030878],[2834836518994496612,55951487144734621344,-42637543906116319097,-22088273037940748908,25620166735987462124,61151816351788328357,-275453682409175585882,241550977781520431871,-159539780256726470799,61102697414708690230,37090560959822726982,-23245078568785234354]] | 168508429374 | 2786309089348 | 150494800283 |
| 40 | [229813291503081498871646749846784728684866024561594213844716,529554012951387298520031525053923932337526301400920882159473,693301589910879207807413601874299473092982121656096152616225,194219719718588054859013165345201055808812628083075153164354,547364029087623991614852048761612404537168000066301829562768,436906792725562951422366559560527858761586316953546626987933,226570121286516691962729520103545300107043795755472068611202,527037293712730352003948148993605576115433626971791613169891,738544221984407842834102445375725845485793416381196271714728,174772489054699848037438630298983550564283730900290995692798,550104920685894050524300961103357113334194440220623889380422,603909265278177181852098036050144959263544945239455774959923] | [114773275000303528417974677513079807014729840848051983533754,131532292556369098734210019609042510819671468609423122584217,-1058963858014250867250655040011481466132908883413321435399980,433105799778462157481455407353046663713662838476669422367725,-24041896770865510794611348014498124556201978666731546574194,736500090301265421414142226016667235020416994720805712278239,135119352728286955276608250501013679603848720883822701449930,108066274701461754878736537427366604674566897829995659526268,-797243794366289598364998317043081661618567269124763746750169,394294800132205331702953325722757059439200535492802910627012,-3203587063315790881193020637653591584899615571967220416205,22189662759997249868371768848618838917717480038546322613283] | [-2365292357065465384204059599562327298415170272727171593200652,-399681875902775514550282960017027593540868766989672367098399,491910919999661234043657555658464049818214006210346439682873,-2375458904161404927460666820812104066758835948472609671276249,-494832667033294219339767713062158302750680328664495950513580,-2916410377428368581910112575222925681259001217276985259982992,-1782886359588702538631052294009711995721623933702102445383437,-625044762433609746227245667168976152576470402341115754864050,3427416950241227214600717290525394011826431259304233262990810,-2796734842947709012962928882665276941636657515823287594270507,-253043637871103964852227410807603396396223689554936084884523,-173626755315941175203400873464279096769751954910403413163003] | [[-76601128365690968644,578812268360024534689,-413588595196277900457,-32027412518537146369,99603784419373293127,4179010359887203896,-18822662084191727372,16505748601132796020,-10901756593488735358,4175317646061942795,2534932180841180530,-1588711970372730554],[-226518075903686489765,1571511479749691397951,-1118105579942449648192,-52561701561309188516,241468600834840521381,-67492423951463308452,303992328297480259838,-266573395681650227170,176067038475411160482,-67432785380231654691,-40940007969293066090,25658233076037431612],[-1150417452257238485760,-3384111339809773683401,3184739142471905843060,132351744116147147980,-753644805323473873759,135161659929003722017,-608781034859828107549,533845142073338991888,-352595325309906601843,135042226549499359404,81987267765278105571,-51383683832373251900],[438568117017877017483,1730911657412927403500,-1539835904808210754174,-75868892314164392187,366474455325961757672,-44672217304960591494,201207936442050540608,-176440909400079930245,116536116833953130479,-44632743434297215423,-27097573703773105076,16982797424172532029],[-118118412932916074538,1103694032328908852778,-747757791391912111333,-43386976948927637063,163139572917241985068,-23464210584217976930,105685047143786165722,-92676094978045166093,61210930440098467617,-23443476820153913143,-14233078500808938594,8920263177213035715],[498530535809841115277,-699611210998148087444,394522414929890487703,-714328481994468428530,513702211472997552459,-602635431605442753505,246522512590461834912,-28503826331891208036,1322854011263812979434,-1138388902196978591647,1123189047889372375319,-859603383471263578819],[-4208272501580389468,476126646488531128834,-355480209239137899801,-135427910466698128183,173785593692856366975,-83896406797067430265,19853728700185615664,9817402298394956481,182701240669480210650,-161625457925575865838,231563649146302685601,-136871392201729626846],[-184808425228354942106,1527227618619422826110,-1095769088281340227087,-116612764609955804072,289845272949618910184,-125710885508286982050,343706922267462855504,-284478050649590016262,305468970077820741796,-173953436779448799988,233566534000339783138,-69957133168988768091],[218732744793442302074,-4034443307829085296263,2964623701275580761859,807934041423775898382,-1186599746593426893130,-589482309013379315417,-135554039115755801223,649633579998770075932,-1773007300516421013275,1206370571925119753259,-1417980442170433838682,765357699138184700538],[-151295664554374266930,2267751962755743480882,-1659049908022605826822,-401554173063775746430,622707246887422951318,326075927032046969475,22898758656290119096,-275170835805566099871,813960129898556687941,-559803574220435568267,712787231852304993632,-369135907797765745654],[-167734636997225462239,1049157756470948920283,-742173486795832866043,-4466324764907538986,135419865372589485329,77170576437111830532,92449204860641855528,-62763190803236463670,-36273187261865234915,44390122618330979041,39248002410372670577,39792219560002086133],[2832158803141812843,55929446241867148759,-42620958817493158334,-22079171257715557086,25610248317252827007,61143508120131483181,-275396204573738239956,241497217453524553677,-159504663878284075805,61089479664033980680,37088839949042099956,-23244599772577984050]] | 168458583267 | 2786503413677 | 150397181815 |
| 41 | [229808338344076962360460730632568642529510730527747880479379,529548338689817244931043460930018842187184037604760024122541,693347270741329901847018205488810869143951475468680185839930,194201034685448755018857357885760909832814653481123116924168,547365065719108851970317439227115987702047447091158637203428,436875019713467815488358696602340471122844387221492341823328,226564291003425411809036647499364420260675967885999314536363,527032631491790098400581803167563682242586441804939594410048,738578615764419416377957953637887678302271091765146575036716,174755477814261007118709014341168994441259124706794460340045,550105058643100686980230804558020538535387404076080221386979,603908307924329956196510861241666782641509034940494828292692] | [114875304085860924687071467149645554594083299552667741890185,131549532072912600888522834921571700915912679838388634517481,-1058985076524356175274023961117214672394049883873407282978617,433208266803068719139926790394715261363417755875310998820198,-24020551585032237828326821072736142675957726180898038377977,736625854156876422403396689609119543944448030310511698675318,135196265814622642074276546702884746937758871197145392238169,108093232653195940117214323154658346221415577425595377495768,-797391600519394012184116968762867638609555816424061097047380,394415432650088502873287546852960167010338379881547121077024,-3192668710749492892310557002050951678076170318676650611076,22197151820284949998090930938938376905499506462776592862663] | [-2365190657161464257619916052332024347881585527258341237847792,-399612164737172582472265866073646105327827285611539245467279,491865431399497149158963188398049315954809923500510941425725,-2375328744434382775949294203288579737436479542409008020581622,-494816886018878765740687785663530407267432121203663748142368,-2914513254268096310779375132226896864229152331882997547258824,-1783116829304925539138789112745116171998171861041254155794849,-624835443569152273469598287374948485435996000643871567203754,3425477163741729136754174053836592074991334143284592440248308,-2796278931086521275450909592503917974649731243006625349069480,-253175536686448429215208169733844371355587798338611673049593,-173596511107452729411250494802299119433056769656548858584572] | [[-76583724024573736643,578619171933300510662,-413453849737693450723,-32015436504040015260,99570575169268081621,4175098519824113686,-18803673429803765151,16488868046941596416,-10890634008703519515,4171073570383627220,2532785823556081481,-1587407766611952312],[-226460693506539305153,1570973977678317913184,-1117732276242093840505,-52541895392928495495,241386744419852390524,-67494119771216895253,303977829644961205292,-266556975737892537190,176056625413210436129,-67429052942657187317,-40944698410885882016,25661835143947834558],[-1150047558094489052185,-3382866887809744271612,3183592151322896615804,132303670144237408110,-753373285784394918681,135147015397718817981,-608670748842214751056,533741010721070956559,-352527413443450794272,135016728674800629256,81985716760925164149,-51384038210863993682],[438534519513742392276,1730516442142969441617,-1539518957609894770967,-75849356099438747975,366398182486398778756,-44680427200677402130,201230260267260169064,-176458032042795083197,116547712032337444397,-44637353615800741819,-27104977778841169204,16987876290134388078],[-118037601091040807807,1103265450753687085160,-747480712690921844791,-43371005390550540758,163080273517580827646,-23459211760814520897,105654837790402906916,-92648316051144735406,61192733107162022281,-23436596212749580457,-14231319020968686726,8919390709199413715],[498207014749472035506,-699080915388877095342,394211776193620308224,-713917086926114740446,513437042253129305511,-602359606275633762390,246418091582322412254,-28494596881274028650,1322292185135390669330,-1137923864770345499709,1122961396072011682237,-859442635303860854743],[-4204277725321219891,475958531136476746862,-355360314093079958716,-135402776575381416480,173746567125293760109,-83899344418640784950,19871784077606793029,9801706310365592773,182716261167029166878,-161636273465093916917,231602396592583989192,-136903142509282336392],[-184777259771402932477,1526717869969015138537,-1095409702697533073651,-116555672223350519062,289736833987339479197,-125684946978096013255,343670434132786138531,-284449646393178668371,305399951230753014689,-173904450147944845347,233541807150985254389,-69939277493808689558],[218848846455585387666,-4033227193461606257480,2963723142396436852914,807484865403941672629,-1186089073776933904215,-589576187076523165265,-135484667843288069736,649502428750208170118,-1772351239099190663469,1205887113707609275559,-1417736013640838751631,765187584891219043906],[-151346048663977200611,2267244153459964833660,-1658678925742784419284,-401378964100764250719,622506203585001659165,326146774251909778422,22889225160036177043,-275159627836795678115,813762072250893063829,-559648780728807171515,712748030905752849921,-369098406196823402138],[-167674919094004791023,1048748770477623269194,-741892109235813532121,-4475862787869283053,135377438223039966087,77165537971028434577,92428429074103845489,-62748846758155464965,-36244502254217971628,44363624952991183435,39262711557702296776,39780011045220421692],[2829484438570082085,55907413149004956958,-42604379997828825413,-22070076037055310449,25600336038199411607,61135202333803247749,-275338743335388785041,241443472415981284992,-159469557545563484934,61076265736915988088,37087118556860461818,-23244120956015368700]] | 168408778928 | 2786698509617 | 150299613882 |
| 42 | [229803380783952968877244573327919284927010210398686322718260,529542663684653491842000873227720542999381928096679743228410,693392952487038108564852374397528524555671679227964129492430,194182345232325162103411627095560253670323158102792459395037,547366101429844166848874763623382521691832827487420368669747,436843241278079865897240767366421945704790938172793190718324,226558457402330967320708330221133014727833825016612905803339,527027968108163252754122063121568257358851750530892459405569,738613015918519543682711847182300327708843798404067822798022,174738461370538591105789675414897553764984892360724758449200,550105196129201226137530777375449604392211863989627580887778,603907350247456348855542540572901377319964390271222467691806] | [114977328782821068602842860073124391304782506064911945342003,131566768581910080891552230978308163053812558744455875147485,-1059006293071752299196960194732363918093277542531451306558861,433310728211459599064694693097842601419514649333102544018242,-23999207080399852346878601521150455215149135737012928522068,736751536204185699386792949718722986796532072245489987890569,135273188836399689000908247464775324545963916168808495270715,108120181577307035498776591555189668225813905004324219280283,-797539323023349288511439101150723527310975256740218708068696,394536045504650099696302700477268960911838886013366364035966,-3181744671044621543634183143985852568323478322931246969123,22204639575656479428908586992982603766181196242175691689376] | [-2365088883864421968330419063124012752585253033290540462546076,-399542433848294028397630487666253549719970359262745812484459,491819920826722684262252344803608610051104180931257079410831,-2375198513581772966704100686015289053035694246615871092691286,-494801083792400953155776815033381649531168198538963532074439,-2912617412003342924156301266508447050980429561620310213602782,-1783347007045646686878693147284951013921553137243546536983913,-624626205133840202870593070578063182951839795527412243463355,3423538635649880889686820044607943099070537718787437057370528,-2795823171436349722189093378120599506386866375435019022561963,-253307316735090717097074307890783440105576550806704722006283,-173566254099878559271634648879066162597595571416709709527529] | [[-76566332539223181564,578426214785492122167,-413319202163415214874,-32003469005381358240,99537389898114263036,4171187044881736977,-18784688995106680184,16471991610608810388,-10879514097227556289,4166830491591419463,2530639197556749966,-1586103343704130512],[-226403355753587061582,1570436883581010613345,-1117359258021048822381,-52522104215589288131,241304950447610547856,-67495815797604667122,303963330962291964590,-266540555387840101146,176046212162785936466,-67425320488899550909,-40949388097586805990,25665437193467815210],[-1149677966545403011936,-3381623402867826542108,3182446058219383433862,132255633640623738616,-753101978790055821551,135132375070123934456,-608560491665593858480,533636905879830693879,-352459519016591560748,134991237454642857353,81984164587155763127,-51384392412803232100],[438500957840119521005,1730121516549765538750,-1539202248676962619750,-75829834275918427371,366321966866131525232,-44688635181700924060,201252570184810617302,-176475141460218510913,116559298639401867121,-44641960597572760593,-27112380878458631624,16992954984899153058],[-117956858708223942441,1102837201584410118931,-747203848732658999805,-43355045807157463720,163021019742671186363,-23454215508652470400,105624643348194896787,-92620550681368001596,61174544684805046420,-23429718995154852115,-14229560188860386800,8918518695506182576],[497883793417882551160,-698551206003704481559,393901494412553885637,-713506044191886932977,513172081016412804281,-602083914484347194510,246313704619779670745,-28485357170965780840,1321730619795546766576,-1137459045563093100553,1122733824501490365144,-859281937302996626402],[-4200291535400680917,475790542389467091639,-355240508623669717794,-135377654887213842775,173707565759598591080,-83902270170090537869,19889829475536874966,9786016076239167377,182731254977541241924,-161647068596430673116,231641134347081978729,-136934885913465851473],[-184746115756697208466,1526208499787951865283,-1095050586560114819318,-116498625676300957813,289628478339733004099,-125659021459248914116,343633957339680568951,-284421248595993345585,305330959080868342760,-173855483587060278712,233517084306554836878,-69921424399929640528],[218964811983132576148,-4032011852789308625931,2962823175024299540256,807036069644055706025,-1185578799560771926859,-589669987027732105550,-135415320199986088450,649371298744736228936,-1771695462123913491827,1205403877202570338380,-1417491659224948497553,765017517617776749400],[-151396393934025324029,2266736709802852750923,-1658308218278172802816,-401203894715561146738,622305316618788993821,326217598595428590845,22879692092968410735,-275148415322386750192,813564081811636660763,-559494042662036257809,712708844421302353604,-369060911680225778569],[-167615250913111987552,1048340109148215006925,-741610955613387652394,-4485390285988904879,135335042858000378983,77160502495555246480,92407660877628416981,-62734509106349720928,-36215832810923766281,44337141466921391233,39277413860239874964,39767806704203075167],[2826813422029345310,55885387855902914050,-42587807438873976255,-22060987368427831142,25590429891571105857,61126898993203905235,-275281298696877451046,241389742671473593843,-159434461260229102422,61063055633970586762,37085396783418488314,-23243642119178624950]] | 168359016317 | 2786894377299 | 150202096508 |
| 43 | [229798418822898896996555632882903722089749975290389527216955,529536987936025793684943852516473341971902157492083341701062,693438635147919142413252502770030785679767210166267573883690,194163651359459608177599195511471550053483030889992495108505,547367136219859340850671596993347249615197671308873601628418,436811457422926864149058109756441062421528910285524468871490,226552620482805046396258629101679884983699364902179527872313,527023303562239163536176107827810858772334500313733871348257,738647422443101033954540531906738728904713473541902075796577,174721439724380672309240823695742706239042524974346548896303,550105333143950453195054236446173517362361488158342524952299,603906392247612661719141407313230943574515879179873318293938] | [115079349088018236206432297556556852890810968411051958913646,131584002082510868129093882700310562855016121663324148392193,-1059027507655491510979285480055934350756917367850527019870048,433413184000566951893267355492291512268141483379417708623110,-23977863257883314423135051237370472688791322878379016869255,736877136498432930984403591229380180522015011753784431613549,135350121781025831588581334667418066734873414796207787874798,108147121477263546301325877067370597929437162815298886158809,-797686961932425114689688049522114250285565348852925283096597,394656638702453893993053038953262325868103738381462969870953,-3170814949323278951194021264366680151208176528878297790928,22212126025559784773043433715702021254695073011840044105337] | [-2364987037184594972484938362057936459382032746186323369474440,-399472683242144962293281948744776737769372791422824059165108,491774388286035791624573798125149398957908020090460693263747,-2375068211616974347215676620682400614836575848932633272832795,-494785260356718802239192727598643006693633570833148360880697,-2910722849978996107221917478182866010952697830405391786881729,-1783576892933328721921146108247579666214823554713160142358443,-624417047083378170018773686675354036361044850854255418837158,3421601365313571210925137082379529810888769185687855348114625,-2795367563898288611051480616726624857496301647604645652122931,-253438978068971326649071739629151761473156252860381981501058,-173535984295951914976726850710535710243439570801698022077630] | [[-76548953893858410431,578233396754465665352,-413184652359506281662,-31991510012773165691,99504228578062932004,4167275935218251522,-18765708780659264994,16455119292632155669,-10868396859381874968,4162588409802658242,2528492303122806706,-1584798701767224796],[-226346062592190882050,1569900196986777742286,-1116986524950075282525,-52502328012093414198,241223218846162255375,-67497512031525442615,303948832257087887563,-266524134638676394706,176035798728816684129,-67421588020719443962,-40954077028909973656,25669039224415277540],[-1149308677262544170190,-3380380883869745200290,3181300862127034393215,132207634562144544043,-752830884095646688657,135117738946925032057,-608450263336435922298,533532827555835213084,-352391642033329875058,134965752890504211486,81982611243803754475,-51384746438105682906],[438467431958186319732,1729726880296885489178,-1538885777733573881109,-75810326827046827788,366245808398979009859,-44696841249196685307,201274866204379365725,-176492237661448117683,116570876661091011837,-44646564381859515680,-27119783001980851953,16998033508216153775],[-117876185704038074287,1102409284438164700871,-746927199269783010879,-43339098184981587241,162961811539955721862,-23449221827103833517,105594463813076766967,-92592798864944569278,61156365170547974845,-23422845166426892491,-14227802004415654824,8917647136102000485],[497560871459193743375,-698022082045805797169,393591569090631719303,-713095353396911745883,512907327548898197982,-601808356200549002163,246209351718018685337,-28476107225024264171,1321169315193437093012,-1136994444527666055700,1122506333187041017869,-859121289475214220082],[-4196313920410510456,475622680093766307339,-355120792721920822620,-135352545386533679848,173668589564164719693,-83905184060241627579,19907864896985424704,9770331595857604313,182746222117579420355,-161657843332793938478,231679862410307131425,-136966622412901012879],[-184714993158779045176,1525699507646028430787,-1094691739563147271620,-116441624917037347779,289520205912514222424,-125633108949480214042,343597491891347492535,-284392857261917103606,305261993625958559536,-173806537093936930011,233492365467804429589,-69903573888160565377],[219080641541363067356,-4030797285041218572804,2961923798563049109305,806587653717268967130,-1185068923511542673879,-589763708905976257662,-135345996200753920338,649240190013608606565,-1771039969545537064712,1204920862363947336927,-1417247378932034021708,764847497324664569711],[-151446700406573388215,2266229631366077944455,-1657937785315494661002,-401028964749463325575,622104585811144715211,326288400064768285120,22870159462956744902,-275137198272123727090,813366158580876472380,-559339360017221038917,712669672400033118815,-369023424249756681178],[-167555632396190692556,1047931772101964036545,-741330025666029754683,-4494907270549368699,135292679239226107030,77155470007549462280,92386900272207714203,-62720177847312674854,-36187178926721596909,44310672155665037098,39292109317623379725,39755606537544321949],[2824145750274659737,55863370352331555949,-42571241132391802745,-22051905244312490593,25580529870122905491,61118598098731537956,-275223870660938859176,241336028222569898973,-159399375023935804131,61049849355810047050,37083674628856880121,-23243163262149008454]] | 168309295396 | 2787091016857 | 150104629720 |
| 44 | [229793452461104261842788385857575480813020804009350557584853,529531311444063941581581402920343412684723874663486626795887,693484318723888276966917588620239422211427921865911814320935,194144953067094557631081851999461762114195917536488331879883,547368170089183818041697670769550081706792875203678290483136,436779668151534189487339332444684939112363452415385208828074,226546780244419880010956627565957639233330196609285313239582,527018637854407029639154264308664130517734655639286876447889,738681835334559036816554690640180003297269902593084387417495,174704412876635039991171580073567773840000055204880740879583,550105469687103374254707708188521587492297025807675566786988,603905433924855220488560498749828894367769630539488087827002] | [115181364998287146171227023069754364175802545387951253530229,131601232573864551086421761021582053869435362030735189750809,-1059048720274626285295035548245684194492599040601336729308769,433515634167323510437966229510050304550916475613719074614140,-23956520118397460786511992387974297688873390331309827745499,737002655094829529195065549439000445510357474149863709900627,135427064635914089512502403424870424827088264876715342592382,108174052356532066477047242493109625546544047131627399571086,-797834517300863040942692887747536714083096337891128443900840,394777212250059390006663912522811656714634966473561007153129,-3159879550705326015541044364651465831259518449606775379231,22219611169442930580480615000001496723155814629820363999827] | [-2364885117132249042986219373108059888233489221467853225167992,-399402912924733178675527754582825367132091200231505301538581,491728833782137173485033283341971382333202908137355493309542,-2374937838553394603248255099947163621254450323985897411442398,-494769415714692995881960525148469343616287317154094216075996,-2908829567539613095163096223960371457062347113167189560440689,-1783806487090503191825391815687706887202542351832124929922109,-624207969373444739479842860471008161062622873722449109636981,3419665352080360537941702541614820746834424195491791641551318,-2794912108373381489159420412321346021694021266504444067071947,-253570520740061589146177567605744081491904959583912485586530,-173505701698407620340137189829072525970145275063815910093508] | [[-76531588072722632739,578040717678335667807,-413050200212204082520,-31979559516442445308,99471091181307824311,4163365190991453841,-18746732787017293260,16438251093506502079,-10857282295485648404,4158347325133984424,2526345140533938450,-1583493840919232245],[-226288813969792548074,1569363917425348766457,-1116614076700437972300,-52482566765269050686,241141549543664933987,-67499208473876114588,303934333536951153075,-266507713497572692133,176025385115973683702,-67417855539874517762,-40958765204369553932,25672641236608129149],[-1148939689899008275186,-3379139329702930175763,3180156562013100434348,132159672865704274474,-752560001456732251295,135103107028823408352,-608340063861178899824,533428775755271271570,-352323782497646882419,134940274983855349967,81981056730703022383,-51385100286686056223],[438433941829179844602,1729332533048414147561,-1538569544504310144224,-75790833736292693996,366169707018861499404,-44705045404329129839,201297148335636834985,-176509320655575328017,116582446103345211896,-44651164970905612828,-27127184148763232531,17003111859834713450],[-117795581998178613647,1101981698932623679651,-746650764055331964715,-43323162510277194316,162902648856957576902,-23444230715539953133,105564299180958614668,-92565060598099820650,61138194561908481042,-23415974725621824134,-14226044467566005868,8916776030955485088],[497238248518052254391,-697493542719643837818,393281999732605557841,-712685014146877944281,512642781636920479302,-601532931393122225041,246105032892158666006,-28466847067471222778,1320608271278040380306,-1136530061616372062357,1122278922137828108475,-858960691827011152006],[-4192344868955553347,475454944095875198330,-355001166279015557485,-135327448057710488833,173629638507440456568,-83908086097919549049,19925890344966398691,9754652869058940433,182761162603710853570,-161668597687394438350,231718580782781257479,-136998352006216899624],[-184683891952230536055,1525190893113695879755,-1094333161401158021303,-116384669893865829544,289412016611539120485,-125607209446515696128,343561037790972782407,-284364472394820818279,305193054863793774716,-173757610665702183333,233467650635484629773,-69885725959306726594],[219196335295322508383,-4029583489447474329018,2961025012417425883568,806139617197343469098,-1184559445196468560901,-589857352750255480734,-135276695860437771138,649109102588008249251,-1770384761318805166786,1204438069145542812365,-1417003172771298305840,764677524018643611823],[-151496968123615678674,2265722917731950120995,-1657567626541951206977,-400854174044003374750,621904010984694434699,326359178662113151138,22860627277854414674,-275125976695776288887,813168302558639724150,-559184732791414392225,712630514843013510233,-368985943907191683305],[-167496063484972221837,1047523758958696338086,-741049319131618849885,-4504413752819767212,135250347328534211372,77150440503868200550,92366147258827961995,-62705852980534002308,-36158540596342292917,44284217014758130590,39306797929496197232,39743410545834681459],[2821481420066089168,55841360628077056460,-42554681070158008770,-22042829657200187404,25570635966620890796,61110299650782031213,-275166459230292048496,241282329071824094512,-159364298838328953732,61036646903043041471,37081952093316362817,-23242684385007793865]] | 168259616127 | 2787288428426 | 150007213543 |
| 45 | [229788481698758715071071999203283937878779639647180891075265,529525634208897763332112207670418008268214890363588675728435,693530003214860744931656246049438864687174537951283254650710,194126250355472607153311085473724361997165433815350048416173,547369203037847081948461747217807488640613270631542219451091,436747873467424840118736319981470322148483719792699085649697,226540936686748241988821199466809438355005273998553911468457,527013970985055900458742797389227743531825130449758321712941,738716254589291041094747602006803778901539568323861416102511,174687380828149200549376945331227703752741634489477771404124,550105605758415216224743261268372553996070889722978599395695,603904475279240374671268627716774303805095589261926251015068] | [115283376510462960204686955481349981986941947673008496081960,131618460055120977464059527104969669587604167775509979829441,-1059069930928209299651055454298427229007602894520068465035386,433618078708662586067098520607084475158649936596019486955279,-23935177662857004708151682511163520223747775316994577543085,737128092048558625186954145640875946345513609532305663224950,135504017388482769551229746241682096119585382978889455794724,108200974218577277531349228830320794381937681152243895343941,-797981989182876466258680848408878093424009668492486339839911,394897766154021822222603436554763504243786851036924655622852,-3148938480308381095312327970216941297804349664574303742776,22227095006754099406837852277072492170120049609259546579905] | [-2364783123717659266402683243043329958361638305662629375577130,-399333122902069155143448208996142319445908751594077070566742,491683257319730280676075071737666324122315071951694430196253,-2374807394404450255000026401646689428884470563819002085822640,-494753549869186878307431977379136852860960700900919979147405,-2906937564029422765617508459626748536760161766923166767610820,-1784035789639770084773885292740258261769233608293486512021213,-623998971959692569925031387785966308669807075249366384130208,3417730595297483099520654154005704148292445263022540720378155,-2794456804762621553182378358076344779015191267392317780195890,-253701944800363501708691971588203750010170999011839159903966,-173475406309982072103563318199514623642739694920575195184482] | [[-76514235060083114438,577848177395464413710,-412915845607920058007,-31967617506631193360,99437977680085235305,4159454812358760044,-18727761014733525537,16421387013723876827,-10846170405856196493,4154107237701342342,2524197710069897923,-1582188761278187361],[-226231609833914345474,1568828044427172995171,-1116241912943904741388,-52462820457970653411,241059942468385952745,-67500905125551652441,303919834809470784156,-266491291971688080299,176014971328919930932,-67414123048119379883,-40963452623479749100,25676243229864281293],[-1148571004108422000400,-3377898739256513359921,3179013156846412313883,132111748508273299170,-752289330629251149022,135088479316515705603,-608229893246228266525,533324750484295424404,-352255940413503931959,134914803736159433939,81979501047687483323,-51385453958459056565],[438400487414396178594,1728938474468950443514,-1538253548714174199377,-75771354987150069597,366093662659800320883,-44713247648261617726,201319416588246386665,-176526390451685087249,116594006972100521211,-44655762366954019754,-27134584318161218534,17008190039504151756],[-117715047510463550459,1101554444686044884532,-746374542842721875754,-43307238769319629267,162843531641280222369,-23439242173331508829,105534149447746015854,-92537335877054927754,61120032856401485200,-23409107671794730811,-14224287578242854094,8915905380035213499],[496915924239629332927,-696965587230966203594,392972785844036853933,-712275026048035311635,512378443067098989667,-601257640030867220657,246000748157253076713,-28457576722292385389,1320047487998158735102,-1136065896781382225487,1122051591362948096836,-858800144364839206719],[-4188384369653745674,475287334242530786238,-354881629186304527868,-135302362885145047501,173590712557928450927,-83910976291950335517,19943905822498131859,9738979895677333595,182776076452506819773,-161679331673445788180,231757289465037479566,-137030074692050815083],[-184652812111674510766,1524682655762059619795,-1093974851769139549779,-116327760555168316959,289303910342804666929,-125581322948072418980,343524595041726864977,-284336093998563203735,305124142792122423237,-173708704299469012066,233442939810340742206,-69867880614169711007],[219311893409823389431,-4028370465239324034888,2960126815993028572158,805691959658651168861,-1184050364183391569031,-589950918599599232183,-135207419193826093028,648978036499046793253,-1769729837398258309710,1203955497501017831470,-1416759040751876485837,764507597706429415408],[-151547197127086122192,2265216568483416750086,-1657197741645220264669,-400679522440949139052,621703591962329114412,326429934389666844275,22851095545497989173,-275114750603099400442,812970513744892001982,-559030160981623959724,712591371751300663236,-368948470654298139157],[-167436544121275402673,1047116069338822850325,-740768835748437659508,-4513909744055342728,135208047087803309468,77145413981368509578,92345401838469474365,-62691534505499618440,-36129917814508562461,44257776039729280029,39321479695507115937,39731218729660923402],[2818820428168694343,55819358672941197447,-42538127243960786308,-22033760599593325290,25560748173842205401,61102003649749077119,-275109064407640502443,241228645221775574603,-159329232705044418862,61023448276274650844,37080229176937686859,-23242205487836274822]] | 168209978473 | 2787486612141 | 149909848002 |
| 46 | [229783506536052044848150568282830949807444910755025191471343,529519956230657123404040402007874743181497151118455114115842,693575688620751738153138832039924595234999381420021806293674,194107543224836485708562779603486581381682763073298306542641,547370235065878655552663541704532036661400961935364469860939,436716073374119434433275242596255020406746120981141856702727,226535089809363448774488423268781040222725739449666960287703,527009302954574675976424904898768282352575189363474809928148,738750680203696873603336453173513649802917997369907184430206,174670343579770377701568460994078955094995772914708853011233,550105741357641426722993816608622397096616182292915398479088,603903516310824497575858527237805297684195613575553271665350] | [115385383621381283450040311705561819298480371541783704065805,131635684525430254293488644478914564833601028008303245663552,-1059091139615293434505535590890045017899864651280594805417584,433720517621518069085964043461668365740936213047932119097250,-23913835892176535886140824733794768336698293523335984820069,737253447414775055178313569261066067598281450533822905193178,135580980026155468531089153804214807820287404029942438702230,108227887066861947408919639249718594090324984967770414028889,-798129377632650624363679613305711773149062604082313858384293,395018300420892153204478141586530293438306390667712093941518,-3137991743247818688003910011388480784823607476092195705415,22234577536941591881201656985563212995614070532873699431342] | [-2364681056951110039878089863331131739839091220662119532817469,-399263313180166050911511764309485860863771033032329078393159,491637658903521311247975116143130641114818711289042022112237,-2374676879183566653260951166188713207325050808166715215569011,-494737662823066454165998555421808241157897098479346228820951,-2905046838792327726249125022876017461198908407308541448975398,-1784264800703797463547839566987208425999187377579674555651015,-623790054797748578875448294436249440160656138263018338585030,3415797094311849002253217069253582764160932860835693771532683,-2794001652966952008792307905511413710610582425072840364856527,-253833250301909560406547069054635137301676027037208538597406,-173445098133413239243024973806577316585513594517691241950485] | [[-76496894840231132016,577655775744461470050,-412781588433239325016,-31955683973596366010,99404888046673938496,4155544799477206640,-18708793464357714957,16404527053773469810,-10835061190808989655,4149868147619981123,2522050012010503767,-1580883462962162047],[-226174450132158910518,1568292577523418204039,-1115870033352745575669,-52443089073078906739,240978397548702418571,-67502601987445104342,303905336082222663114,-266474870068169472705,176004557372310421924,-67410390547205597680,-40968139285754794901,25679845204001648920],[-1148202619544941929053,-3376659111421325351011,3177870645597377583173,132063861446887780490,-752018871369515214547,135073855810693918486,-608119751497957069270,533220751749034073768,-352188115784842609165,134889339148872139684,81977944194591086107,-51385807453339382849],[438367068675190318532,1728544704223606398445,-1537937790088589232324,-75751890563138248622,366017675255917668245,-44721447982156425308,201341670971864323985,-176543447058855862151,116605559273288714681,-44660356572246066308,-27141983509530298084,17013268046973784851],[-117634582160833220007,1101127521317270006644,-746098535385745963389,-43291326948405257449,162784459840607303647,-23434256199848518773,105504014609340038396,-92509624698026864705,61101880051539162231,-23402244003999660532,-14222531336377512781,8915035183309722314],[496593898269619881671,-696438214786802864313,392663926931295222548,-711865388707193644969,512114311626336925602,-600982482082501894396,245896497528289754224,-28448296213437505348,1319486965302418103411,-1135601949974731429260,1121824340871429552059,-858639647095104515366],[-4184432411136099121,475119850380705868002,-354762181335306343621,-135277289853269278718,173551811684185578656,-83913854651160540391,19961911332603322929,9723312675543070823,182790963680542684044,-161690045304164462383,231795988457620212348,-137061790469048273129],[-184621753611774453248,1524174795162878166964,-1093616810362548338627,-116270896849402357590,289195887012448546910,-125555449451858738513,343488163646764745829,-284307722076990830502,305055257408671314263,-173659817992336013987,233418232993112788447,-69850037853547436004],[219427316049445438825,-4027158211649123594901,2959229208696312621228,805244680676172868779,-1183541680040772110094,-590044406493066428539,-135138166215649688185,648846991777764662714,-1769075197738234240052,1203473147383892365662,-1416514982882835969258,764337718394692031131],[-151597387458858393412,2264710583204061834798,-1656828130313455352149,-400505009782303282371,621503328567204567712,326500667249652339433,22841564273707395065,-275103520003833327093,812772792139537380659,-558875644584812246837,712552243125940504034,-368911004492835197560],[-167377074247006410580,1046708702863338355136,-740488575255171844972,-4523395255497508263,135165778478973453557,77140390436907374519,92324664012106663016,-62677222421691685283,-36101310575935019775,44231349226099716320,39336154615310317268,39719031089606074004],[2816162771352523324,55797364476741339058,-42521579645600791572,-22024698064005791074,25550866484575035126,61093710096024178428,-275051686195672175329,241174976674949258012,-159294176625708587274,61010253476106370408,37078505879861627555,-23241726570715763942]] | 168160382394 | 2787685568135 | 149812533121 |
| 47 | [229778526973174175833246029879937823443962314667204607964261,529514277509471922920986356168213248763742613355859352423286,693621374941476407625654685239753529261169610148512247196766,194088831675429054510955475656988467363245446863229180167752,547371266173308101285860694472247208318592135962809628023744,436684267875136212225214686152923899749997374231373919275777,226529239611839359204952323674250698261217714621161425143291,527004633763352106842049611766579561203921520216972957850253,738785112174178697929500529008901723814216832694845365529657,174653301132345512669697892981556820058546892466349720242885,550105876484537673980051705246034431296175032613740632435523,603902557019663986306952069573662118463546405377819053591990] | [115487386327878164887845865079014288400435241333051403196042,131652905983942748052793176539184314365050238542673446708400,-1059112346334931773386488350180502395679349006800546050816543,433822950902824429117696283896552816497394850651059062888818,-23892494807270520330767645324781266220327586178712748588414,737378721248605346408133911465883737448670526951298360126346,135657952536361076254818691789254496938110788601683999694605,108254790904846929386879604192651151200944420763320973852876,-798276682704342569784819558252183570884363628555042973893237,395138815057217071445316122600366343727273405638700790456467,-3127039344636768117934761972981111678738846835588754058824,22242058759453826773933607202489823037465985100395155868913] | [-2364578916842895068038565625783770243862764495749418825803602,-399193483765039705341436016255867729907960805340991228455907,491592038538219209092546492836170532311488545241361311425551,-2374546292904177975568074354103494107095253275172903347252207,-494721754579200387629058108252132147939382125945779569861759,-2903157391171906397461579837538090644918569323065272941501662,-1784493520405321100342707147806028739107829547535340087614720,-623581217843214107062984414069938780561540347976683474258966,3413864848470046312170606905199002835253582898857241262886547,-2793546652887266429272891797580745827914987643012711824159538,-253964437296762593745761637395036411916583906376049133372884,-173414777171440662274682404619452872982362072174346495224192] | [[-76479567397481926694,577463512564183213950,-412647428574920344748,-31943758907609850704,99371822253395104343,4151635152503451356,-18689830136436612931,16387671214141638907,-10823954650657652303,4145630055004456000,2519902046635640487,-1579577946089265592],[-226117334812209076418,1567757516245969261563,-1115498437599731637297,-52423372593500673436,240896914713100966459,-67504299060447599470,303890837362769546648,-266458447794151623482,175994143250792162341,-67406658038881701778,-40972825190708960620,25683447158838150696],[-1147834535863253540948,-3375420445089892206681,3176729027237977573815,132016011638649548108,-751748623434208760258,135059236512045401816,-608009638622705979525,533116779555583518357,-352120308615584768288,134863881223441670907,81976386171247811948,-51386160771241728420],[438333685572976062357,1728151221978006144645,-1537622268353398020514,-75732440447801727237,365941744741436409506,-44729646407174745352,201363911496139892505,-176560490486159641553,116617103012837288607,-44664947589021444638,-27149381722226002358,17018345881992925415],[-117554185869350069171,1100700928445723482821,-745822741438573930830,-43275427033851425064,162725433402702487332,-23429272794460341604,105473894661637255195,-92481927057228419906,61083736144830949769,-23395383721289628592,-14220775741901194360,8914165440747507619],[496272170254241506870,-695911424595463730202,392355422501556902586,-711456101731721752333,511850387101820846191,-600707457516661929170,245792281020191026784,-28439005564820400615,1318926703139268734256,-1135138221148318707894,1121597170672233269783,-858479200024167633894],[-4180488982046685334,474952492357608574914,-354642822617707302871,-135252228946546179080,173512935854822830616,-83916721184377219196,19979906878309019727,9707651208482576464,182805824304397858493,-161700738592769763286,231834677761085142009,-137093499335862984300],[-184590716427234419977,1523667310888561894189,-1093259036877303981149,-116214078725100993484,289087946526748896871,-125529588955574329697,343451743609226035599,-284279356633938143617,304986398711145680104,-173610951741387446294,233393530184535516074,-69832197678234155748],[219542603378536017212,-4025946727910334537609,2958332189934588569307,804797779825497120731,-1183033392337687894459,-590137816469745306551,-135068936940581812213,648715968455131167460,-1768420842292868446387,1202991018747545669409,-1416270999173176552723,764167886090056098864],[-151647539160746021177,2264204961478104685288,-1656458792235284767124,-400330635910302850528,621303220622740960808,326571377244311885154,22832033470285940110,-275092284907703650345,812575137742418552093,-558721183597896721118,712513128967967769777,-368873545424553815688],[-167317653804158606449,1046301659153820364372,-740208537390909238660,-4532870298373868602,135123541464046009402,77135369867341724533,92303933780708045858,-62662916728588619048,-36072718875328212451,44204936569383316731,39350822688565366334,39706847626249422252],[2813508446392601891,55775378029310390023,-42505038266891121214,-22015642042962932720,25540990891618586869,61085418989996652361,-274994324597059518793,241121323433855612705,-159259130601938382956,60997062503136115938,37076782202228985035,-23241247633727592813]] | 168110827853 | 2787885296545 | 149715268926 |
| 48 | [229773543010315169158903755953389400693293878467996734654239,529508598045472099651492471178545202869183039092464001852503,693667062176949863500874474177603476529545007856470236329959,194070115707493306999452210636780826383792158449401189118955,547372296360165021024130793609233779161546060755765413040750,436652456973991035914507026769134629394391807102341370500421,226523386093750374281179620223208691365721438028157480855348,526999963411776794456448257171302836103955563995228590557851,738819550497141013217520151133263402588546568098328455584273,174636253486721264364373270764687566458644853957725664797031,550106011138859846742390783882042855275878885097294324899482,603901597405815261760102560965744870319502271365568361289651] | [115589384626790097737421725828081591687514931610573332067855,131670124429809084782241236890447184823831974025944048341778,-1059133551086177603010165399620484772243687390389223364194800,433925378549516715483937559260650956493737386873746570274849,-23871154409053300249818070765219573345209674294785778398572,737503913605147703196565170586934061989266003299186117734051,135734934906533778414478658594096973856308462871959360332108,108281685735991160975019399251178407124909065965263271053101,-798423904452081164003326351570847609230141926510470325512279,395259310069538989234301258596879128874698621393734011384365,-3116081289586112231385399057356210801639401927183769477630,22249538673739341064446670494528236198561159545392850888086] | [-2364476703403317359896997654003978534716630393283084085990022,-399123634662708636473295056331920025840927616280561452046060,491546396228535662566057866465602536518069629047591356853524,-2374415635579727222358342031930362489524832211306213176887830,-494705825140460001482235784239178876374606010949470616232274,-2901269220511415090256706723131058635398411141158379807174645,-1784721948867144112422333346779966474075416872504715063645098,-623372461051665082408341579995893479581149463308055985186765,3411933857118343131521621321281735074098907895905582104860209,-2793091804424409113284919826456978650308098944611339548795876,-254095505837015596536470668978373905427197734041965792431178,-173384443426805452560239057829470908475311606597546189795116] | [[-76462252716174658722,577271387693732361063,-412513365919894591443,-31931842298958437619,99338780272612219223,4147725871593773941,-18670871031513974841,16370819495311915263,-10812850785713966318,4141392959968629629,2517753814225258392,-1578272210777644646],[-226060263821827720174,1567222860127426758877,-1115127125358134306993,-52403671002168944620,240815493890177550163,-67505996345448350238,303876338658661080944,-266442025156757141390,175983728969004176596,-67402925524893189559,-40977510337856549184,25687049094191709040],[-1147466752718570201635,-3374182739156432203957,3175588300741764390084,131968199040725973510,-751478586580387866394,135044621421252878256,-607899554626783346492,533012833910010002723,-352052518909632564725,134838429961308771015,81974826977491674519,-51386513912080781062],[438300338069225896653,1727758027398284946629,-1537306983234862131147,-75713004624710155550,365865871050679894322,-44737842924476687220,201386138170715280856,-176577520742661936982,116628638196669461128,-44669535419518209360,-27156778955603905700,17023423544310882681],[-117473858556198423219,1100274665691411382008,-745547160755751245625,-43259539011996419050,162666452275409308308,-23424291956535678319,105443789600529757297,-92454242950868208245,61065601133783556164,-23388526822716620585,-14219020794745010438,8913296152317025004],[495950739840233570030,-695385215866536227972,392047272062803221934,-711047164729546452479,511586669281020181644,-600432566301901014700,245688098647813832657,-28429704800318993761,1318366701456985642562,-1134674710253907615879,1121370080774252389343,-858318803158343621159],[-4176554071042620314,474785260020681932638,-354523552925361076620,-135227180149469747723,173474085038505201227,-83919575900427911559,19997892462646604534,9691995494318420326,182820658340655762509,-161711411552483790136,231873357375999205815,-137125201291156841967],[-184559700532798958418,1523160202512171782591,-1092901531009788295976,-116157306130872622252,288980088792124039924,-125503741456910208289,343415334932234975808,-284250997673227480706,304917566697229225060,-173562105543693260586,233368831385338407922,-69814360089020467378],[219657755561210510927,-4024736013257521880608,2957435759116020406528,804351256682819132649,-1182525500643832801422,-590231148568753284582,-134999731383238277458,648584966562044600718,-1767766771016094665605,1202509111545216658020,-1416027089631830539167,763998100799100925816],[-151697652274502494645,2263699702890398695211,-1656089727099810674529,-400156400667418835087,621103267952622315504,326642064375906957806,22822503143020336679,-275081045324421283551,812377550553316953402,-558566778017749910794,712474029278406028641,-368836093451196772785],[-167258282734812374049,1045894937832428009293,-739928721895139076734,-4542334883898241310,135081336005083535317,77130352269528439911,92283211145236255519,-62648617425665097404,-36044142707386648663,44178538065086628634,39365483914937202640,39694668340166526118],[2810857450068923971,55753399320496778022,-42488503099657288575,-22006592529001537433,25531121387783067554,61077130332053634421,-274936979614459508244,241067685500990680397,-159224094635341282243,60983875357958229850,37075058144180584229,-23240768676953111980]] | 168061314813 | 2788085797507 | 149618055442 |
| 49 | [229768554647665222411820833896122461951385044798624323493270,529502917838787627997823990201241103188721414754596207052149,693712750327087175096617652345284372477743372723826960572625,194051395321272368812845937865135846919673938515433882495711,547373325626479056082728450900631712734133486760436437026515,436620640674197391768859183643413469423636846217624156402840,226517529254671436939599160837427347340788810665252354428912,526995291900237191054098269615194629848575985818606498754743,738853995168990652952320231304561805630097286536094029163294,174619200643744009569366616303654604767671004190834340864900,550106145320364054175432417264050876801574941563552294417133,603900637469334768616694113368584544312592447386301514175237] | [115691378514954019858140530062392243912220038349584922791694,131687339862180150199803060033291652312222879876932082114064,-1059154753868084413399415537827617212885822338120019112743383,434027800558530557585348169594301683200060390908076739252280,-23849814698439093933911036493923142741409188772849928309332,737629024539471993094858965091931703388060347469836143762729,135811927124113059488662874422069218328857820391936753367131,108308571563751662823099512172495637569218034394674953339702,-798571042929967061696994621102946967213173751324461673153619,395379785464396040538922128146465769794623496421413353039697,-3105117583204486098894681736564547571463281042476399786384,22257017279246790008951555064070548577224084214478975242684] | [-2364374416642689225754796253961496636783721972192060631320410,-399053765879194039555873894472447029901013525014978162874503,491500731979185103111365704746485768612237977540264191294798,-2374284907223666213118923035801057911259203175270336546599450,-494689874509719276217859700449313454983686844302150511259254,-2899382326153790079245560352966058762083498556073012250805458,-1784950086212136598610518814646375667042722426195376881843916,-623163784378652183616759541823360274927557917864925598686708,3410004119602689670702231408833627741738100955739102137131852,-2792637107479175441789068972892615646735923683516049134498628,-254226455974791564141958815262047865237754720001680162995320,-173354096902250291611928899446390609383336044520974256698997] | [[-76444950780672361782,577079400972457495055,-412379400355266221881,-31919934137943791187,99305762076731004584,4143816956904076985,-18651916150130565721,16353971897765008567,-10801749596287874510,4137156862625673408,2515605315059373539,-1576966257145483208],[-226003237108857609776,1566688608701105642631,-1114756096301724228520,-52383984282042789836,240734135008637233362,-67507693843334654529,303861839977433816772,-266425602163096503808,175973314531577517042,-67399193006982528653,-40982194726711897247,25690651009880250152],[-1147099269766632153891,-3372945992516852606659,3174448465083857908265,131920423610349844789,-751208760565479670843,135030010538994446013,-607789499516465250187,532908914818349766563,-351984746670868487355,134812985363906735377,81973266613156720014,-51386866875771223015],[438267026125470884435,1727365120151088224719,-1536991934459661121076,-75693583077458289544,365790054118071762003,-44746037535221277033,201408351005225621477,-176594537837421783310,116640164830704172657,-44674120065972777731,-27164175209019625724,17028501033676962473],[-117393600141684253126,1099848732674920294210,-745271793092198421835,-43243662869199427074,162607516406651017164,-23419313685442574151,105413699421905166977,-92426572375150683269,61047475015900968462,-23381673307331595430,-14217266494839971831,8912427317986689567],[495629606674856241700,-694859587810882882257,391739475123819065917,-710638577309151576765,511323157951686742953,-600157808406691076401,245583950425949838522,-28420393943775351947,1317806960203669071290,-1134211417243126597592,1121143071186312510791,-858158456503902116947],[-4172627666794048834,474618153217603422201,-354404372150288394052,-135202143446564915310,173435259203951577307,-83922418808140623245,20015868088651779454,9676345532869325814,182835465805903783096,-161722064196531408181,231912027302940571698,-137156896333599908526],[-184528705903253025671,1522653469607418175675,-1092544292456844442709,-116100579015400858454,288872313715132221841,-125477906953548752517,343378937618900464676,-284222645198669090058,304848761364584174199,-173513279396309137782,233344136596245691300,-69796525086693317209],[219772772761352724538,-4023526066926352000602,2956539915649623937730,803905110824939677487,-1182018004529515752147,-590324402829236824276,-134930549558177556198,648453986129332336763,-1767112983861645388414,1202027425730004284802,-1415783254267662854960,763828362528360564567],[-151747726841821369173,2263194807026430120966,-1655720934596608196244,-399982303896355738165,620903470380796013082,326712728646718215835,22812973299680725255,-275069801263682487590,812180030571952894801,-558412427841199503176,712434944058267699890,-368798648574498683861],[-167198960981134957894,1045488538521900932521,-739649128507751233694,-4551789023270677707,135039162064209661474,77125337640324359171,92262496106648047843,-62634324512392066753,-36015582066800824354,44152153708708893197,39380138294096130822,39682493231929218782],[2808209779166442080,55731428340164420114,-42471974135737199997,-21997549514669809797,25521257965889663113,61068844122580082208,-274879651250513669256,241014062878836101075,-159189068727515329899,60970692041163487303,37073333705857274836,-23240289700473690935]] | 168011843235 | 2788287071158 | 149520892692 |
| 50 | [229763561885414669613657039064422840036661505258894853174420,529497236889548518984764828158633196665879890914352551528276,693758439391803370905625017583980925324626385264489140531674,194032670517009497764728537183007086227669338028936105778299,547374353972279887210737432249708292924860309073588393204359,436588818979266391126388892653893118879508033138060501028805,226511669094178031823466716721520986723473510049597779028847,526990619229121599785833925506213560263322421065959971791437,738888446186136783742422294564138280637266502241638409850970,174602142604259843126212698607433835938525007230003271510776,550106279028806625766555635824796879331335187244847878092520,603899677210278975338838094464398838687328834561011126030336] | [115793367989207314150590923805362763721573613571029909428613,131704552280207089816605659933052417407104623658038371020349,-1059175954679705898001983096631582975908196718387043134007818,434130216926802165281949431990599032384097341236909244779676,-23828475676341995641872959465355363351264857134889611839209,737754054106619733124629005155843100858524941436256936414530,135888929176543705624047397696295520584632797179125206591682,108335448391583537635200480006985020587204251522766106129506,-798718098192072697071933719913323162631591042738743925368293,395500241248322078902499301208546063441273221580760979025022,-3094148230598275724698385695975251066241765763933820771683,22264494575424947208173071280182905383379508513260361657828] | [-2364272056571332274101027328306985738056849464792574738427239,-398983877420519785576270665245935406367673604486808172433842,491455045794884703879260970051265468401605368467244501341032,-2374154107849455582535037563268920941838091446182013415341222,-494673902689854849126691862678269084110125227327985551879737,-2897496707441649670819230619948399918128318547340079040770573,-1785177932563235276618728882194110810459731423778624028665493,-622955187779701003392012629976825557051453385146055089732317,3408075635268720315344482907843679912298326140419525010814703,-2792182561952312234127351772588546792787130439992026656320223,-254357287762243327108126864473315549096486883445426923841269,-173323737600519430397088729528298084611470193741047714213878] | [[-76427661575361897495,576887552239952598167,-412245531768311745626,-31908034414882421675,99272767638199336295,4139908408589886724,-18632965492824165938,16337128421978812323,-10790651082687484079,4132921763088068786,2513456549418067677,-1575660085311002603],[-225946254621221251751,1566154761501033851010,-1114385350104770355352,-52364312416107307243,240652837997293981303,-67509391554991897925,303847341326611224567,-266409178820268070718,175962899943135273151,-67395460486889160422,-40986878356789375282,25694252905721704048],[-1146732086663705511506,-3371710204068746440226,3173309519240942782848,131872685304819241716,-750939145147281660571,135015403865943586540,-607679473297995554460,532805022286609093954,-351916991903155390843,134787547432661423577,81971705078077027206,-51387219662227730999],[438233749703300553194,1726972499903570580870,-1536677121754891738538,-75674175789665943111,365714293878135749966,-44754230240566457845,201430550009298991361,-176611541779491739411,116651682920856086330,-44678701530619929824,-27171570481828823431,17033578349840467241],[-117313410546234943429,1099423129017416221997,-744996638203210303843,-43227798591840497612,162548625744430427966,-23414337980548420447,105383624121646650809,-92398915326276149340,61029357788684460364,-23374823174184488383,-14215512842116988590,8911558937724875932],[495308770405889557355,-694334539640638902409,391432031194191349145,-710230339079576973272,511059852901854232646,-599883183799422503898,245479836369325557726,-28411073018995726892,1317247479327244952827,-1133748342067469356297,1120916141917171811787,-857998160067067419899],[-4168709757984128872,474451171796284541975,-354285280184676728541,-135177118822387473194,173396458319934627175,-83925249916343808229,20033833759364551815,9660701323950178050,182850246716733235296,-161732696538140217830,231950687542498617859,-137188584461870401608],[-184497732513421907304,1522147111748659536390,-1092187320915776039598,-116043897327444395311,288764621202471347642,-125452085443163724733,343342551672316082908,-284194299214061148677,304779982710851322058,-173464473296276522997,233319445817976347201,-69778692672036006925],[219887655142615272576,-4022316888153590508535,2955644658945265149438,803459341829264004615,-1181510903565659585165,-590417579290371292513,-134861391479900883708,648323027187750928491,-1766459480783052364052,1201545961254867917612,-1415539493089471166894,763658671284323891019],[-151797762904336371967,2262690273472316863764,-1655352414415724502903,-399808345440051138212,620703827731472299320,326783370059045454094,22803443948020697914,-275058552735168886542,811982577797985687326,-558258133065028442921,712395873308554073911,-368761210796186013383],[-167139688485380301479,1045082460845558182528,-739369756969035458685,-4561232727677483795,134997019603608969486,77120325976586286147,92241788665894310382,-62620037988236749490,-35987036948253250359,44125783495742069041,39394785825717811381,39670322302105614844],[2805565430475057791,55709465078192693246,-42455451366981131186,-21988512992527349970,25511400618770517525,61060560361958779230,-274822339507848103941,240960455569859137495,-159154052880049155194,60957512553339102289,37071608887399931303,-23239810704370718113]] | 167962413081 | 2788489117634 | 149423780702 |
| 51 | [229758564723753981201828505347289577343145742975751711186678,529491555197884820248408422374873693102128114473264422739621,693804129371013438604336373208844632259022328278388938843439,194013941294948083818443421930614585402781384320439690250998,547375381397597234585717844359389033520027793519260698930638,436556991892706771618872652299185395694696813800635443016304,226505805611846185054105813477502860174812800121226772847083,526985945398818174801603787541116822273780051926028096643111,738922903544990904102308818558464848451423040789095002683059,174585079369114578118898151323053820155295618114185513112076,550106412263944111228051776299456686076294053198243276858881,603898716628704374164266657253776524634215075540299457691112] | [115895353046387808957605228647912959228132221386339571464264,131721761683041309052324044037576747954088415900389061660888,-1059197153520095953808746855418833213102766340641960488468849,434232627651268329273300490653755450879579394976086464383934,-23807137343675975486151406635250359163084039851677754807780,737879002361604076106221689156895933443533429117850278488317,135965941051275807501312710322755178679723298860975933650042,108362316222939969091105042092500923754524386144039075289217,-798865070292442270283376936170513609315949297092836655327305,395620677427846675357054742108361358444472442507066249710554,-3083173236871616763293141794734028721791935504982843108813,22271970561722704675036485700362490955790369084874023956063] | [-2364169623199577408508916500302237076461240460751790115064573,-398913969292712419788747331110947446507640928170353740095577,491409337680354378349031015399160661700668811899964901291585,-2374023237470564776635294745118204750609241373820773154188033,-494657909683746013388914839541908912602340317743303834096202,-2895612363717296266486758341956929009661658149529235987729587,-1785405488043443121208687513958985633722013989780113571954016,-622746671210312211269248099970948783836295942611340088795935,3406148403461755688572015932793824373384783485231470240326071,-2791728167744518103264498536043491889539569488983085804327059,-254488001251553386172820489168774154711156834539393731886690,-173293365524358688642315858509180474669733096136364715793569] | [[-76410385084653910029,576695841336056582849,-412111760046479696038,-31896143120105656835,99239796929507164168,4136000226806353850,-18614019060129576855,16320289068428409118,-10779555245219070068,4128687661467608575,2511307517581488189,-1574353695392461465],[-225889316306920739062,1565621318061950952870,-1114014886442038999533,-52344655387373573915,240571602785070452923,-67511089481303555931,303832842713703709508,-266392755135358098679,175952485208292580689,-67391727966349503438,-40991561227603387677,25697854781534004588],[-1146365203066581255384,-3370475372711389273917,3172171462191265459598,131824984081497411106,-750669740083960964673,135000801402769172213,-607569475977585959961,532701156320764362535,-351849254610336527913,134762116168991271645,81970142372086707507,-51387572271364976224],[438200508764362783197,1726580166323394826721,-1536362544848067126715,-75654782744977940192,365638590265495502630,-44762421041669089807,201452735192556412822,-176628532577917888837,116663192473035588456,-44683279815692808703,-27178964773387203314,17038655492550696095],[-117233289690399060613,1098997854340643474538,-744721695844455351816,-43211946166320500120,162489780236829766376,-23409364841219956544,105353563695632932710,-92371271800440773773,61011249449632600189,-23367976422324214049,-14213759836506870032,8910691011499918254],[494988230681632475350,-693810070569209774646,391124939784307490737,-709822449650417513133,510796753919837756627,-599608692448404379143,245375756492602468405,-28401742049750594826,1316688258775465369625,-1133285484678295222532,1120689292975521164358,-857837913854018565354],[-4164800333309016071,474284315604870370615,-354166276920879984361,-135152106261524002754,173357682355280690007,-83928069233866350820,20051789477829219587,9645062867372031985,182865001089739322709,-161743308590540523869,231989338095273912401,-137220265674654680295],[-184466780338171136389,1521641128510901207055,-1091830616084346283255,-115987261015836866713,288657011160978718793,-125426276923420293036,343306177095560119447,-284165959723189780319,304711230733650081270,-173415687240622660354,233294759051244119505,-69760862845828199765],[220002402868419970437,-4021108476177100129766,2954749988413658580697,803013949273800753635,-1181004197323799934413,-590510677991360823646,-134792257162852361211,648192089767986204910,-1765806261733647104193,1201064718072627714779,-1415295806105985999031,763489027073434682250],[-151847760503621507512,2262186101814807254521,-1654984166247677907812,-399634525141675256790,620504339829123790630,326853988615207558242,22793915095777321787,-275047299748547483355,811785192231013770367,-558103893685975030153,712356817030255332232,-368723780117977088945],[-167080465189888885877,1044676704427297110630,-739090607019680613538,-4570666008291241151,134954908585526872270,77115317275170997052,92221088823920070881,-62605757852662651258,-35958507346418479490,44099427421670855849,39409426509483251433,39658155551260116534],[2802924400789612227,55687509524476404815,-42438934785251703627,-21979482955145131920,25501549339268711905,61052279050570338711,-274765044389073517296,240906863576512699642,-159119047094521987949,60944336895068733724,37069883688949452792,-23239331688725600876]] | 167913024314 | 2788691937074 | 149326719495 |
| 52 | [229753563162873764010284099550915151141146936006283279638822,529485872763926616024943606972445778987178727212416742759421,693849820264632325061673288305092779462895709740447809603000,193995207655331649062021749882366138111816587658490061855934,547376407902460857808348379365532789007262997459300339777681,436525159418024898395581502544883762959588436745398011953754,226499938807252464002025271735902468505612904306360019479708,526981270409714921333274519892011990782906522137208022254069,738957367241966843234203726459333742259121539606568896215318,174568010939153746058640292325221828508676068761865979865111,550106545025533280400023912333306636286318086426911213613224,603897755724667481101223350517305663095744970836567277721018] | [115997333683333778465153175686854386443975378439717866819013,131738968069834473350508950341852133080025196671749390873104,-1059218350388308681471899433938969835263534867130124383479614,434335032728866421478508795243997885027162397315910180858395,-23785799701354879318267991467490025500410755944587094415823,738003869359409797075988506633813035469113113857965386529596,136042962735764763185475358881629295008355157736088823719900,108389175061272220774696179236810770931233735177915229366360,-799011959285091733945345807926799304428401753852126549012672,395741094009495116351487113151400269545266123221281283829020,-3072192607126393243109372287305209316641813425489108909236,22279445237589072902323849704760374779820918561247877330349] | [-2364067116537764824529726694516803757884270903509556803505038,-398844041501801160242829596610906942681265254720360104631460,491363607640316778948237412723091443701036955399310241480079,-2373892296100472048934541250071257961041364169540970802025293,-494641895494274717164374694312951592854313817990084421045282,-2893729294322718421387458868449137557733347289285527275791943,-1785632752775829003188593912472007703336056168851577962662050,-622538234625961716067237993742318618197371267447709551393919,3404222423526804708429510520149472389834884757131698830431934,-2791273924756443810190538821931676173591013655444816275651164,-254618596494933747654450595162141307637069682459256152665030,-173262980676515454137211510277042786120971431858002503476302] | [[-76393121292982780817,576504268100852824467,-411978085077390302029,-31884260243959613618,99206849923186431668,4132092411708254323,-18595076852578626500,16303453837586075873,-10768462084187078818,4124454557875398264,2509158219829848034,-1573047087508155716],[-225832422114037599353,1565088277919306789997,-1113644704988792882702,-52325013178878596259,240490429300997793446,-67512787623151196206,303818344146208626587,-266376331115440754792,175942070331656630896,-67387995447096956972,-40996243338668372819,25701456637135089511],[-1145998618632574231936,-3369241497345736010395,3171034292914631195450,131777319897812642463,-750400545134053649038,134986203150135474013,-607459507561416057044,532597316926762092637,-351781534796235581581,134736691574307304280,81968578495019905029,-51387924703097624410],[438167303270363696043,1726188119078731013874,-1536048203467116029121,-75635403927064067039,365562943214874380746,-44770609939684950344,201474906564611854269,-176645510241739840501,116674693493148788984,-44687854923422920606,-27186358083050513471,17043732461556944839],[-117153237494846122031,1098572908266923564176,-744446965771974928793,-43196105579061085302,162430979832010518123,-23404394266823271637,105323518139738306964,-92343641793836598951,60993149996241258802,-23361133050798669385,-14212007477940324769,8909823539280110232],[494667987150901936972,-693286179811268859518,390818200405353892925,-709414908631822099063,510533860794233337107,-599334334321864704161,245271710810377131453,-28392401059774696436,1316129298495909014085,-1132822845026829521886,1120462524369984251517,-857677717870889403102],[-4160899381477848221,474117584491739130981,-354047362251418184095,-135127105748591804905,173318931278869665462,-83930876769537547823,20069735247094356830,9629430162942120504,182879728941521098093,-161753900366965304761,232027978961878192981,-137251939970647231357],[-184435849352406412718,1521135519469794172138,-1091474177660777070389,-115930670029486709549,288549483497630770991,-125400481391975052856,343269813891695597199,-284137626729829073515,304642505430578531127,-173366921226360627743,233270076296757524165,-69743035608845926696],[220117016101958224477,-4019900830235838589294,2953855903466365697753,802568932737160870618,-1180497885376084109818,-590603698971438182016,-134723146621419058698,648061173900653368563,-1765153326666561386064,1200583696135965000412,-1415052193325870849417,763319429902091694289],[-151897719681191162766,2261682291641278841560,-1654616189783456962958,-399460842844630526319,620305006498484981328,326924584317542459212,22784386750671162492,-275036042313470675505,811587873870574839032,-557949709700733018443,712317775224350567508,-368686356541582114920],[-167021291037087568703,1044271268891592270504,-738811678400773912560,-4580088876270827768,134912828972269494191,77110311532935247531,92200396581664505755,-62591484105129568190,-35929993255963133564,44073085481972717934,39424060345078795470,39645992979953419910],[2800286686909876565,55665561668925763307,-42422424382423861060,-21970459395105481725,25491704120238243632,61044000188793207385,-274707765896785243509,240853286901235369173,-159084051372503674576,60931165066932491522,37068158110646763157,-23238852653619765506]] | 167863676896 | 2788895529615 | 149229709095 |
| 53 | [229748557202964761250264505378118233079790806981010436135035,529480189587804027139435513762222007155439535993855301235749,693895512072574936347826954627313056614765527128671385340980,193976469598403847683102245313457179431624185834662240021785,547377433486900555897063619114816437621186199756503953275660,436493321558724765347700806118597000313789556927364858800398,226494068679973977057914129055311213908647302498828291470387,526976594262199695777480777907000760067830297213113654910987,738991837273480759809272861924575868330383777023799450973649,174550937315222597068754985837887620807637875871293946387735,550106677313331123153231381386990740400468970381767006928467,603896794498224835923350811443731853048690988455553868560287] | [116099309896883943103101594484837514784531916945047166413493,131756171439738508293851075128217935094195010799232923502697,-1059239545283398385423067129766290090052916058409458038649525,434437432156534395416074140187077512657295332550277230532231,-23764462750292428614310530534070609253101535615696751972947,738128655154993279792252244392411990329989105398805061971289,136119994217471280960664984393919750326981507858741119581116,108416024910029635109354634125276076955747660202362829786771,-799158765224008779728961518707146792578315980751373839945406,395861490999788401695016822935876082703582042913299602446433,-3061206346462236297276874165084275849046428492911011333319,22286918602473180930300284880314128425139248835607422744310] | [-2363964536596244006584010922710825717955699097330835917685586,-398774094053817896310656747721805719591456808523266453181688,491317855679497295671710441669813413091169996650162299502217,-2373761283752664456574222976493097770398835836981758224455206,-494625860124325562682080678547285934287874914905256818760430,-2891847498599592897984958736936249970445767110863619965880692,-1785859726883527329241700047153143169895404907887627985102381,-622329877982100827960616257354165348826374056182578510952560,3402297694808566640493363897304985877390771649256034701845055,-2790819832888692617485847330194298290517676354946718432840883,-254749073544625759219334701886228493010721938569596907380066,-173232583059738682037710317843923653439335710274421693729033] | [[-76375870184806583373,576312832374668695083,-411844506748835160574,-31872385776805169950,99173926591810995811,4128184963449990169,-18576138870700175216,16286622729921289101,-10757371599894131411,4120222452421857319,2507008656443425696,-1571740261776418553],[-225775571990732643544,1564555640609260122472,-1113274805420790189299,-52305385773685260537,240409317474215427458,-67514485981414480785,303803845631610295663,-266359906767578130666,175931655317826679645,-67384262930861904466,-41000924689498803190,25705058472342900462],[-1145632333019522153765,-3368008576874417682650,3169898010392401085234,131729692711258143916,-750131560056464012639,134971609108702169188,-607349568055633378618,532493504110518996356,-351713832464656697353,134711273650013147064,81967013446710796643,-51388276957340335804],[438134133183067543474,1725796357838255466394,-1535734097340381996803,-75616039319619024573,365487352661095271163,-44778796935768734326,201497064135072230994,-176662474779990729367,116686185987097521970,-44692426856040135131,-27193750410174545711,17048809256608506007],[-117073253880366365350,1098148290419154105526,-744172447742182589413,-43180276816504645456,162372224478213277812,-23399426256723806650,105293487449832651229,-92316025302651554424,60975059426003617552,-23354293058654736704,-14210255766347960738,8908956521033705119],[494348039463031928540,-692762866582754994696,390511812569314423018,-709007715634492676082,510271173313917426615,-599060109387950628407,245167699337181308356,-28383050072767076793,1315570598435981647701,-1132360423064163942165,1120235836109117683745,-857517572123768675039],[-4157006891212729764,473950978305501755022,-353928536068977156734,-135102117268238829785,173280205059634903554,-83933672532187090744,20087671070212799165,9613803210463862518,182894430288681424059,-161764471880650182009,232066610142934346485,-137283607348550655507],[-184404939531073522219,1520630284201633823872,-1091118005343748121555,-115874124317377026341,288442038119542812558,-125374698846476048507,343233462063770298738,-284109300237741099571,304573806799213466060,-173318175250489371533,233245397555219858388,-69725210961861592588],[220231495006191421287,-4018693949569856501997,2952962403515793272577,802124291798556526740,-1179991967295269980402,-590696642269864624741,-134654059869931117633,647930279616297092872,-1764500675534727754762,1200102895397422639084,-1414808654757722306667,763149879776648739790],[-151947640478500212127,2261178842539737181124,-1654248484714519557102,-399287298392551158802,620105827564551752027,326995157168407087754,22774858920406307561,-275024780439576270654,811390622716145971330,-557795581105951712640,712278747891807803493,-368648940068703186105],[-166962165969489423436,1043866153863494320203,-738532970853800164039,-4589501342761438863,134870780726203551476,77105308746735779685,92179711940060948558,-62577216745093594145,-35901494671545930386,44046757672117907765,39438687332196116131,39633834588742521051],[2797652285640542576,55643621501466349002,-42405920150384845998,-21961442305002055907,25481864954544005533,61035723777003669302,-274650504033563272243,240799725546451423827,-159049065715554694087,60917997069506942671,37066432152632810918,-23238373599134657195]] | 167814370789 | 2789099895397 | 149132749527 |
| 54 | [229743546844217852491044022787449636634883210682591922003232,529474505669647210994601502367360368433354428346649797668975,693941204794756137743051137532214787541412278864305325573845,193957727124408465943834639380119380041348281833054464851749,547378458150946167282686400781477516648924503186835057933188,436461478318307996333330210762228273894734534086624492698595,226488195229588373403514613293376694329827652046758871677149,526971916956660205778520870742678298737800859941263929692249,739026313635951140748248265574691410610343359743871691176303,174533858498166100069612889177793368468858269549890673318410,550106809127094849291879713541715441993319993293011496251236,603895832949433002164575541721002885792171622278124540564853] | [116201281683877469945839943864191824642850574107402555866866,131773371791905599719381759041699954874989425925458060629604,-1059260738204419573991370166641404167459326123656784764336762,434539825931210786583566157715106802222660741032668683023215,-23743126491402220360464492258241603877814378965940722627662,738253359803282503329759307539624325903811303756603486517130,136197035483861382149382618888663519002001675790502919027926,108442865772659632300339532641721508101493887863560327410384,-799305488163152825049195664938308376303746649208995303855860,395981868405243242515864717993796769618586848204843821753667,-3050214459976522901466725087474541193346493143718644584816,22294390655824276414310207308019434657875958628050190077506] | [-2363861883385373724850242024591932228089577600667005242197000,-398704126954797187213582130903810612834929902475675508375297,491272081802624054699760967564707875599749753523646470466948,-2373630200440637856460261886372941006911779209887606687428848,-494609803576785805328962191899411974377297215598063715386740,-2889966975889286714950249072403959112755977396800950064944204,-1786086410489737682585987625678462512995615175130076270144915,-622121601234156420172672753033075606646292756950693654194446,3400374216651433145670903917434357251931206807435031182110381,-2790365892041820642049919139768646437307401731640849835711169,-254879432452899946027188886206152041519279520619771970933594,-173202172676778894168996277637352242264095073232265992817159] | [[-76358631744607038216,576121533998075098294,-411711024948776909978,-31860519709017936578,99141026907996547242,4124277882185590295,-18557205115020121309,16269795745900730147,-10746283792641027116,4115991345216720499,2504858827702565119,-1570433218315620420],[-225718765885245814767,1564023405668677277136,-1112905187414283621940,-52285773154882283515,240328267233970852446,-67516184556971168308,303789347177380016519,-266343482098820256363,175921240171394056611,-67380530419371717016,-41005605279609185456,25708660286975383024],[-1145266345885784602642,-3366776610201738258253,3168762613607489095203,131682102479391918433,-749862784610463885422,134957019279124348920,-607239657466353452933,532389717877922026575,-351646147619384515393,134685862397505038651,81965447226993592041,-51388629034007765201],[438100998464296596442,1725404882271149815517,-1535420226196622597361,-75596688906362380863,365411818539080397030,-44786982031074054246,201519207913537405973,-176679426201697217164,116697669960779346055,-44696995615772685416,-27201141754115135666,17053885877454668898],[-116993338767870518520,1097724000420807717088,-743898141511863370262,-43164459865114274927,162313514123757598088,-23394460810286356100,105263471621781439519,-92288422323069468988,60956977736410176179,-23347456444938286668,-14208504701660285227,8908089956728915732],[494028387267872545596,-692240130100870103062,390205775788968898724,-708600870269683244437,510008691268046423098,-598786017614728675739,245063722087482078892,-28373689112391125269,1315012158542916559444,-1131898218741256899951,1120009228201411115349,-857357476618700092748],[-4153122851248716314,473784496895001449625,-353809798266408226481,-135077140805143606614,173241503666563094790,-83936456530645048040,20105596950241629271,9598182009736871043,182909105147826933856,-161775023144833389593,232105231639076388733,-137315267807075653665],[-184374050849158256554,1520125422283358730727,-1090762098832396106928,-115817623828565448186,288334674933968763424,-125348929284562794702,343197121614816791969,-284080980250675930558,304505134837110444058,-173269449309993741220,233220722827329209799,-69707388905643982375],[220345839743851316161,-4017487833420295267887,2952069487975191765212,801680026037800039325,-1179486442654724859922,-590789507925929764801,-134584996922661853534,647799406945391619405,-1763848308290880024777,1199622315809405409907,-1414565190410070166405,762980376703414765627],[-151997522936944122179,2260675754098814630678,-1653881050732792015963,-399113891629302715532,619906802852580879141,327065707170177329045,22765331612670389831,-275013514136487502305,811193438767143755169,-557641507898236066574,712239735033584014978,-368611530701034301342],[-166903089929693579107,1043461358968628926669,-738254484120641013487,-4598903418894607633,134828763809756232908,77100308913429329092,92159034900036898445,-62562955772007127934,-35873011587817710682,44020443987569489452,39453307470532204981,39621680378180722244],[2795021193791213177,55621689012039084742,-42389422081034176317,-21952431677439819828,25472031835061765112,61027449815575849612,-274593258801972274891,240746179514570861806,-159014090125226174094,60904832903365117296,37064705815048569234,-23237894525351740034]] | 167765105957 | 2789305034558 | 149035840813 |
| 55 | [229738532086824053640655088521573038136050624195019225371374,529468821009586361559582122322722752377781985839509857776319,693986898431090753746460218373611505537047952959079745893821,193938980233589422155766736000111825398295633615763679217471,547379481894627569803055245518545260458355385571792499355584,436429629700273846403059979902436191733238483577885594619837,226482318455673842782373836105765666591712110274008917715855,526967238493484010311297896052315265830655670646368817871195,739060796325798800001480063507659215849303710292481533870721,174516774488828942963683427766180960602844685513248434541519,550106940466581888456356267103037295454882972288061236991487,603894871078348567113989768387325692764675265161058089997369] | [116303249041153973112771571422496422322016896564606443449526,131790569125488193833610099190837556511344038511585189303020,-1059281929150426959521423319949276113265134764083432649089563,434642214049834712837135157494121304931233329068507100406795,-23721790925597726938583769829133850560358235254477607341387,738377983359177028762410782249197859003874802064509266212068,136274086522406403916276072585078450892500466345161664499292,108469697652607709284135750446858331425265122636957535855479,-799452128156454999839853001307970810680849380941693494367179,396102226232372059235128370950718352676345957610989911994761,-3039216952764374618793211977758237884666433970296942601564,22301861397091725692343472922363327506345799879848257442299] | [-2363759156915522032150821114400691886745384698137032286964976,-398634140210776260548024986743635580229632271297273234982723,491226286014427917015610437547866362292714877559684720514002,-2373499046177896901398450038040589883278733224775884836441829,-494593725854545352737883512882019670920713194350830282863399,-2888087725532859191241057924823453411420256547912309861124185,-1786312803717724464463683276745485435607320288155892974311586,-621913404337531090289275698779173276294736840438665869920849,3398451988399490323195441606984366627142595288497889477097529,-2789912102116337206995138967252239911158898307819555345371180,-255009673272055847254199927011481531045845582976102422966180,-173171749530388178328005528630670183318812649814587881294139] | [[-76341405956889467892,575930372811886005147,-411577639565348903873,-31848662030988228976,99108150844400530491,4120371168068711288,-18538275586061406689,16252972885988290426,-10735198662726746822,4111761236369039151,2502708733887675658,-1569125957244169000],[-225662003745896037659,1563491572635130799141,-1112535850646019458937,-52266175305584163212,240247278509619432823,-67517883350697116238,303774848790976083903,-266327057116205114348,175910824896942174422,-67376797914350756843,-41010285108514060559,25712262080850486755],[-1144900656890242034760,-3365545596233671450923,3167628101544359103337,131634549159836640320,-749594218555691927810,134942433662052525967,-607129775799659856318,532285958234828425934,-351578480264184202647,134660457818171842953,81963879835702533790,-51388980933014561953],[438067899075931034428,1725013692047100036578,-1535106589765008625774,-75577352671038523702,365336340783851128435,-44795165226753440396,201541337909600190678,-176696364515879493101,116709145420087544948,-44701561204847168338,-27208532114228162901,17058962323844719609],[-116913492078389570282,1097300037895930925377,-743624046838173081854,-43148654711373730639,162254848717041839138,-23389497926875069962,105233470651445755165,-92260832851270082743,60938904924948760720,-23340623208694181278,-14206754283807704909,8907223846333914466],[493709030215789059138,-691717969584076806081,389900089577891576822,-708194372149198874707,509746414446056186084,-598512058970184971018,244959779075681958673,-28364318202274615441,1314453978763775023413,-1131436232008933906543,1119782700655287360669,-857197431361682414973],[-4149247250333799216,473618140109313263432,-353691148736727902243,-135052176344015173721,173202827068694160562,-83939228773741847418,20123512890242162406,9582566560556961277,182923753535567992237,-161785554172755743476,232143843450949444199,-137346921344941013243],[-184343183281686332918,1519620933292549408694,-1090406457826313774077,-115761168512183998006,288227393848300894706,-125323172703866298042,343160792547852455773,-284052666772371657281,304436489541803835011,-173220743401844524031,233196052113778465604,-69689569440958267213],[220460050477440420745,-4016282481029384972363,2951177156258653709937,801236135035302795287,-1178981311028424395023,-590882295978951434384,-134515957793827858432,647668555918340855068,-1763196224887553780717,1199141957324180379978,-1414321800291377547575,762810920688653930392],[-152047367097859056204,2260173025907769145003,-1653513887530668204467,-398940622398981677760,619707932188089545517,327136234325247977373,22755804835134610826,-275002243413813045442,810996322022924415187,-557487490074146780599,712200736650625147717,-368574128440261377131],[-166844062860385060346,1043056883833195672743,-737976217943574188601,-4608295115788225981,134786778185415080796,77095312029872631793,92138365462514028623,-62548701185318880527,-35844543999421464981,43994144423783362187,39467920759789363308,39609530348817638164],[2792393408176393004,55599764190600206771,-42372930166283621875,-21943427505035026130,25462204754678143822,61019178304881718357,-274536030204561630792,240692648807989426130,-158979124603059906788,60891672569076514719,37062979098035035874,-23237415432352497008]] | 167715892811 | 2789510947239 | 148938982977 |
| 56 | [229733512930974516926595523599399730741924628242575875077756,529463135607751709358707109892893574887841230739803961829580,694032592981493568084832325786964685247302152140104091834498,193920228926190766654715110424668627274426562659995290542509,547380504717974680697646851840571622914909189867327239831664,436397775708119203026119888138848931060815389884265158926927,226476438357809115270474873685462300650977904554977869397175,526962558873058519764306046558549398222202704368001771889410,739095285339446877328419769434664242761376244739923525715249,174499685288055532820665843608597456676455953640873949185598,550107071331549890025911875199311973105818030738946182956695,603893908885028141810730390740130305953800047070893608583511] | [116405211965553514168670588733276721433985518510034046608019,131807763439638997327596454995218203929531163761203782121570,-1059303118120475458491276885621493467885454646898820496262237,434744596509345874770856205782498100285587830780164779752962,-23700456053792296011800810294412532924741632169098160988170,738502525877547985934065182024029269396997486134648834162062,136351147320583002056468181103979294266477894124093159232251,108496520553317438684751693810457740034318414593732387888966,-799598685257818133416579085136952286675694353115237742498104,396222564487682979555819972942939002793076584627818006282156,-3028213829918656351759506960413968459045113852030969955553,22309330825725013852571426127743217642912131330671624910365] | [-2363656357197066260835466485544136057856556443641681702842341,-398564133827795010810574353409861468170542391603040750656152,491180468319642477022039724262706536351717169182064459966089,-2373367820977955036227362875252177944917723784847601457957450,-494577626960496763874916805679751948500204164355933062042037,-2886209746871063985384842199806209379920352965159648738652023,-1786538906690816536459350971585298891831861902214371037193228,-621705287247603321194493960729093713080086746125061715595301,3396531009396520748824464232673646532815436493383904688110496,-2789458463012705192706808866843201036555884609249123191162962,-255139796054421852993107396569246487152359001941507286138263,-173141313623320187585516322717219650140085248450137340882930] | [[-76324192806182752103,575739348657157991103,-411444350486854885982,-31836812733121039316,99075298373722064424,4116464821252638218,-18519350284344022501,16236154150645076654,-10724116210448456473,4107532125987182521,2500558375279232015,-1567818478680509186],[-225605285521081067984,1562960141046898106596,-1112166794793236613995,-52246592208931129772,240166351230624194412,-67519582363466283087,303760350479843802563,-266310631826758653422,175900409499046537817,-67373065417520380768,-41014964175728003807,25715863853786165210],[-1144535265692294788262,-3364315533877857539378,3166494473189021946429,131587032710279532006,-749325861652152931798,134927852258132642312,-607019923061604265850,532182225187065775739,-351510830402801484942,134635059913395061306,81962311272671897398,-51389332654275369994],[438034834979908835016,1724622786836295488125,-1534793187775123317031,-75558030597416613302,365260919330527793474,-44803346523958341048,201563454132846345907,-176713289731551274596,116720612370911127924,-44706123625488544696,-27215921489869551020,17064038595527941073],[-116833713733074541184,1096876402469143071561,-743350163478637602217,-43132861341787392719,162196228206543018545,-23384537605853455522,105203484534682303758,-92233256883429059131,60920840989104531397,-23333793348966276862,-14205004512720525869,8906358189816833299],[493389967957660983926,-691196384252096042461,389594753450449645170,-707788220885394725081,509484342637661553940,-598238233422225466311,244855870316119016566,-28354937366009744982,1313896059045446755726,-1130974462817887933297,1119556253479102510168,-857037436358669525019],[-4145380077228890104,473451907797743654616,-353572587373117567810,-135027223869593008753,173164175235121143796,-83941989270308258162,20141418893279931952,9566956862716158659,182938375468518656424,-161796064977660611181,232182445579209725758,-137378567960873594442],[-184312336803723314012,1519116816807427095406,-1090051082025549077746,-115704758317438954113,288120194770069568885,-125297429102009078458,343124474865879505620,-284024359806554407237,304367870910806868974,-173172057522998479460,233171385415255321731,-69671752568566010629],[220574127369232389890,-4015077891640442291437,2950285407781112105238,800792618372074176950,-1178476571990951455904,-590975006468275548526,-134446942497589103208,647537726565478469224,-1762544425277086877246,1198661819893877277217,-1414078484410041008619,762641511738585681812],[-152097173002521978474,2259670657556483075079,-1653146994801008631081,-398767490545915018338,619509215396854852170,327206738636032690889,22746278595453764109,-274990968281147032176,810799272482783939396,-557333527630200399008,712161752743866138315,-368536733288062261219],[-166785084704334627787,1042652728083966966652,-737698172065272745940,-4617676444546565191,134744823815727872218,77090318092922431276,92117703628408194801,-62534452984473882268,-35816091900992360450,43967858976208283642,39482527199675192918,39597384501199202042],[2789768925615479015,55577847027121235636,-42356444398057181212,-21934429780415193223,25452383706290596393,61010909245291094255,-274478818243865453427,240639133429088628965,-158944169150588364897,60878516067207109509,37061252001733233196,-23236936320218429979]] | 167666725670 | 2789717633579 | 148842176044 |
| 57 | [229728489376860530876518513571331083957334439608889471065048,529457449464273521460256422353268090277842499069420186272169,694078288445879323721417553289364883617649829211759692516765,193901473202456681775619447697732953955615918130205932073049,547381526621017456602193655436254057152829381815620894989554,436365916345338587317096886874652055438530327328706336072769,226470554935573461046747900312961346360687323257758930540419,526957878095770996022661789043350143259612428413515963409422,739129780673320837076538793093541372596163537841416334692686,174482590896689996062706663994156156750449924820382731965526,550107201721756723021288806869337241790677220779333738598956,603892946369528361038855014601603699700902231889216539296905] | [116507170453916602523904249270835241229712389803350599163387,131824954733510977491962315531793921520962019767511668284325,-1059324305113620191630297958782042331123113862017390061661387,434846973306684556095906337153148048073125593939781712858866,-23679121876899150410176131815694243008159366764918777397548,738626987413238060317206134113417122566734603995547264027820,136428217865873153768473627734110370178273737665569497732602,108523334478230467776951188340565353204882900160490810529725,-799745159521116741427686055773226040544177059910327723229528,396342883177679836467029892568359288144648263474259579351485,-3017205096529975101230839913095306544403175304428613222580,22316798941173744800852833872505457951385640585605862539594] | [-2363553484240393019661984726760407350382480726186106468710054,-398494107811895997922345755478136543499988885120800848957782,491134628723004061157257546852363458206886368581486527784328,-2373236524854334493948793831454669346261259049654869911103558,-494561506897535248125873908481795765539065238718576606711505,-2884333039244351129972698255406424477692512254485609800713859,-1786764719532406863645300977285584139940971681369722649510367,-621497249919727641628490512060281575620996158942243886692643,3394611278986005508248268713028136129410523934371963709043410,-2789004974631341387070698528647177299352615785378486510610948,-255269800852355041529725556601614029271506756472710848108596,-173110864958330139587826552920671351894317730600703204891253] | [[-76306992277039282939,575548461375189774064,-411311157601768665608,-31824971805836008503,99042469468701862862,4112558841890285445,-18500429210385014752,16219339540329416070,-10713036436101510498,4103304014178839051,2498407752157774187,-1566510782743123069],[-225548611159277342609,1562429110442960148273,-1111798019533665698037,-52227023848089096438,240085485326555619407,-67521281596150730632,303745852251415502274,-266294206237494802653,175889993982274752788,-67369332930598943685,-41019642480765624965,25719465605600375981],[-1144170171951862093038,-3363086422043600193459,3165361727529032473904,131539553088472241102,-749057713660217123662,134913275068006076795,-606910099258206511977,532078518740432044828,-351443198038962679042,134609668684548844632,81960741537735991372,-51389684197704827853],[438001806138225663718,1724232166309427953242,-1534480019956961560562,-75538722669290535088,365185554114329489747,-44811525923839122632,201585556592854582616,-176730201857719808022,116732070819134830318,-44710682879920139414,-27223309880395267782,17069114692253613093],[-116754003653196255136,1096453093765635220588,-743076491191152172108,-43117079742880225216,162137652540816661473,-23379579846584379242,105173513267343426071,-92205694415717996961,60902785926359990493,-23326966864797427056,-14203255388328953631,8905492987145763806],[493071200144881148825,-690675373325904692060,389289766921801718041,-707382416091175060819,509222475632855862185,-597964540938676166729,244751995823066991958,-28345546627153175537,1313338399334650370672,-1130512911118679776353,1119329886681146046369,-856877491615570508057],[-4141521320707805505,473285799809830059608,-353454114068923172730,-135002283366646959048,173125548134990099852,-83944738029175373523,20159314962424674989,9551352916002706923,182952970963296637155,-161806555572793881435,232221038024524514462,-137410207653608316563],[-184281511390374528223,1518613072406852527071,-1089695971130604311630,-115648393193610714065,288013077606942980565,-125271698476605190633,343088168571885019157,-283996059356938362547,304299278941611684375,-173123391670398373768,233146722732442291968,-69653938289225174667],[220688070581272407694,-4013874064497868401942,2949394241958338807575,800349475629720490265,-1177972225117495029483,-591067639433275969022,-134377951048049039812,647406918917067990730,-1761892909411619938222,1198181903470488862584,-1413835242774390663515,762472149859384834064],[-152146940692150758310,2259168648635461969733,-1652780372237139554201,-398594495914659774331,619310652304913331132,327277220104963946434,22736752901266258622,-274979688748069067378,810602290145958205651,-557179620562869407300,712122783314230934109,-368499345246106746182],[-166726155404398618833,1042248891348286953981,-737420346228804319316,-4627047416260296564,134702900663302500537,77085327099435485432,92097049398629443625,-62520211168913490065,-35787655287157767678,43941587640285893329,39497126789902586955,39585242835867671835],[2787147742932751105,55555937511588947163,-42339964768291058277,-21925438496219083824,25442568682807390199,61002642637171648477,-274421622922402616579,240585633380235775920,-158909223769334717628,60865363398319357527,37059524526284208113,-23236457189031059680]] | 167617599682 | 2789925093720 | 148745420035 |
| 58 | [229723461424673520298905327341833531650887799181558968235062,529451762579282101465216312480070313704118064813616362599074,694123984824162722864751260619374340928219484419509471283532,193882713062631481827380528202919773322488036886567658563856,547382547603785893543296457110721076404154023815919241597707,436334051615424155263217754325638146760544142682117789476277,226464668188546690163462038748454740883278139256038906724446,526953196162008552551179616990893280678520253223334167776280,739164282323848466959685938684376316066134282273910233046391,174465491315576178649702938714675140116590238454280073686135,550107331636960476007295345433247688538021205497191838475018,603891983531905883322215075240223850290655486338677296726618] | [116609124503084195834520716173891545183244444976577634888142,131842143006257362331836496162928277921967362361971526221238,-1059345490128916484036991988487351957287344085428764588381644,434949344438791624019574791901234876316031394420190923327784,-23657788395831388016387261049655499822383967697732469982703,738751368021061479959268577567722690291676027666279454854100,136505298145764160411740001401967724679183458011294005046020,108550139430786517456403193895267444277065233478772870342683,-799891551000197012892590099873190781475942015812588553280770,396463182308862166263180018173189503065589103037376110526983,-3006190757686678732418941498146148117219994634308656005120,22324265742887641328209687397054876439030880494579652198650] | [-2363450538055898190674425804559579108346120876627716658662414,-398424062169124445752591394017374051724336718551066816900730,491088767229251726509989199392515209496924280939991082619884,-2373105157820566291855712309211670363081613132129890052413670,-494545365668558664382097409152102966204587071373275651470281,-2882457601992869061371488614268082477994055051622146888643515,-1786990242365952158553054907961173907665357139329128362319603,-621289292309234786368258257521535265432467938492166574203985,3392692796511126225716333575892494718733059872228172838448457,-2788551636872616834869382061930416651021876821545433611103202,-255399687718241016995335032345762759307998812654323645844318,-173080403538174815858019206220734190991313632975751878385503] | [[-76289804354034920206,575357710807521753459,-411178060798733793875,-31813139239567398277,99009664102122155390,4108653230134197417,-18481512364698489924,16202529055496861655,-10701959339979455232,4099076901051017677,2496256864803907408,-1565202869550529918],[-225491980609039829825,1561898480363000064390,-1111429524545528083189,-52207470206249610649,240004680727091441799,-67522981049620626140,303731354113110552854,-266277780355415485298,175879578351186535724,-67365600455301802030,-41024320023141568347,25723067336111080723],[-1143805375329381082784,-3361858259641863307511,3164229863553486608382,131492110252230717751,-748789774340619468239,134898702092309652737,-606800304395454631072,531974838900695638375,-351375583176374724671,134584284133000005572,81959170630729157275,-51390035563217568674],[437968812512934764049,1723841830137690683056,-1534167086040929116464,-75519428870478852609,365110245070573896298,-44819703427545069925,201607645299196562775,-176747100903385869457,116743520770639114036,-44715238970363641733,-27230697285161325204,17074190613771012373],[-116674361760145111473,1096030111411169072814,-742803029733980691827,-43101309901197736905,162079121668496651209,-23374624648430068603,105143556845277110955,-92178145444304442404,60884739734194990216,-23320143755229485779,-14201506910563093191,8904628238288757169],[492752726429354769204,-690154936027733205050,388985129507896334792,-706976957379992275878,508960813221910462886,-597690981487283355872,244648155610735411892,-28336146009226072589,1312780999577933836116,-1130051576861738420756,1119103600269640959674,-856717597138249728334],[-4137670969557251446,473119815995340462792,-353335728717654923869,-134977354819977172183,173086945737499987690,-83947475059174593136,20177201100750317885,9535754720201076141,182967540036523259819,-161817025971403933891,232259620787572139326,-137441840421888144341],[-184250707016784989978,1518109699670324718207,-1089341124842435242145,-115592073090053658842,287906042266726897833,-125245980825260245382,343051873668840961760,-283967765427225777882,304230713631689376133,-173074745840973014411,233122064066016717091,-69636126603690126017],[220801880275377572733,-4012670998847146896687,2948503658206942928935,799906706390443895394,-1177468269983849115071,-591160194913354368617,-134308983459254703351,647276133003302904904,-1761241677243096855043,1197702208005871301679,-1413592075392690297684,762302835057181645019],[-152196670207904273928,2258666998735833380060,-1652414019532852090606,-398421638350002620582,619112242738560459413,327347678734492994437,22727227760194141999,-274968404824144244310,810405375011623107945,-557025768868582329302,712083828362632513011,-368461964316056582987],[-166667274903518788780,1041845373254070432114,-737142740177630369895,-4636408042006512014,134661008690806857194,77080339046268573495,92076402774082021108,-62505975738075394574,-35759234152537287413,43915330411450735915,39511719530189720721,39573105353361636384],[2784529856957362751,55534035634005343487,-42323491268933639229,-21916453645096683547,25432759677147584678,60994378480888908424,-274364444242676780463,240532148663783990321,-158874288460812846591,60852214562972201964,37057796671829032072,-23235978038871925706]] | 167568514810 | 2790133327803 | 148648714975 |
| 59 | [229718429074605046263720780368438796686651608614353613851752,529446074952907789496030445996549556021927727010624947048277,694169682116258426977472456239704250074121459842361807999814,193863948506959613067681867503258077756790963582687609126012,547383567666310026933032120558629929104328052858720528030578,436302181521865698952192953041694881557335609466692683705610,226458778116309152316498589959994491522555572810373532267876,526948513072158154477492078820793067860757289090015926338760,739198790287459876835887668172927191666279703941958792817499,174448386545557646264690595650827678549546165819854094764908,550107461076919456995327286241304813092587423271748878261078,603891020372217390919326050248491134804801792703098389048685] | [116711074109897700402202107038427721439078173008162277283749,131859328257031640681737632260010982600566503390423141536753,-1059366673165419865296764574942876484206990035042796608217482,435051709902608529624106172348060580687123169735513800843443,-23636455611501981651457122595933037625237212605724892180549,738875667755804002516417359166180089290219593434752851734631,136582388147748650248848696628541071379155571339597240291671,108576935414423381216733088599719582133314509151407101163915,-800037859748876797327654468221316327478523349840734143727000,396583461887725206578331054790815577681234368371848315197636,-2995170818474854747861555125144666511005602318199414253094,22331731230316545178272853888312434579430331689974147423924] | [-2363347518653986926078623867946154133813480473762839079027826,-398353996905528240641564554161678586186890548011371536079180,491042883843127259433786317262124808794399342150690184250306,-2372973719890190227657747095944555209929268470697360222077617,-494529203276467520125511514409761704309983048303856944246013,-2880583434456466644661480574950047061678596768836512173438064,-1787215475314972525969606720003385997496133292446217141463992,-621081414371431856031769304674107502461166533827518006267325,3390775561314767087888725998208738116855625630058731205532757,-2788098449636857186348624872162831969957304509131231355043289,-255529456704493747394374356443206987872139034905195066827746,-173049929365612561096816107960151520330584610610859949922260] | [[-76272629021768946864,575167096795935550376,-411045059966563240703,-31801315024764063373,98976882246806608343,4104747986136549468,-18462599747795620591,16185722696600197341,-10690884922374032339,4094850786710049133,2494105713498302092,-1563894739221286159],[-225435393819001879996,1561368250347401850449,-1111061309507534968889,-52187931266629805242,239923937362016443268,-67524680724744244580,303716856072335379177,-266261354187510632712,175869162610333722551,-67361867993341317244,-41028996802370512908,25726669045136245186],[-1143440875485805809316,-3360631045585267840983,3163098880253018412944,131444704159435092246,-748522043454458974819,134884133331675645558,-606690538479304917940,531871185673595446644,-351307985818725216504,134558906260108030624,81957598551485769789,-51390386750728220231],[437935854066146847857,1723451777992777442428,-1533854385757841833515,-75500149184824760549,365034992134677085970,-44827879036224386229,201629720261436900229,-176763986877543765449,116754962231300168073,-44719791899039105418,-27238083703523779677,17079266359829412559],[-116594787975430857552,1095607455032075878115,-742529778865755019642,-43085551803305942182,162020635538295080035,-23369672010752113966,105113615264327008221,-92150609965351900980,60866702410086740549,-23313324019303310207,-14199759079352949047,8903763943213824189],[492434546463498521368,-689635071581063236309,388680840725470461831,-706571844365845916697,508699355195374245108,-597417555035713820899,244544349693269708053,-28326735535714145308,1312223859721674928159,-1129590459997361403969,1118877394252743864036,-856557752932526906304],[-4133829012576808094,472953956204272967146,-353217431212986977656,-134952438214414026692,173048368011902561276,-83950200369137605489,20195077311334961922,9520162275091970752,182982082704823425686,-161827476186741608911,232298193869041957155,-137473466264464074284],[-184219923658139320289,1517606698177979744186,-1088986542862450244188,-115535797956196017317,287799088657364404194,-125220276145571430998,343015590159704212063,-283939478021106998363,304162174978490043720,-173026120031637284430,233097409416650773975,-69618317512711642151],[220915556613137282506,-4011468693934841704554,2947613655944369238154,799464310237041339665,-1176964706166411622526,-591252672947940095478,-134240039745196814067,647145368854306750413,-1760590728723265284203,1197222733451744535735,-1413348982273137483760,762133567338061893378],[-152246361590882516048,2258165707449345666602,-1652047936382401325966,-398248917696959444254,618913986524350174057,327418114527089813873,22717703179843123862,-274957116518923160249,810208527078894682517,-556871972543723824160,712044887889972903335,-368424590499565494541],[-166608443144722152295,1041442173429801767138,-736865353655605437998,-4645758332848744622,134619147860968713768,77075353930278502970,92055763755664381055,-62491746691393627382,-35730828491742777246,43889087285130284491,39526305420260042510,39560972054216021559],[2781915264523331669,55512141384387624161,-42307023891945469278,-21907475219709179537,25422956682241010796,60986116776806261494,-274307282207176417832,240478679282072237449,-158839363226527361706,60839069561721079371,37056068438508801027,-23235498869822586505]] | 167519471017 | 2790342335970 | 148552060885 |
| 60 | [229713392326846806083051448051126677884436166457719128374826,529440386585280962185346064723992316589351227898843663249977,694215380322081056785147258424250418696268726832873210788461,193845179535685653677795017683367999171133046719714439549142,547384586808619931563556341670603089129087371636190662855505,436270306068150647800617926959020781482190960791792687961079,226452884718441736615506303146843853835007764171989626480018,526943828826606618675213784349887371907189137657394551232151,739233304560587497484594895422330494594613441247114810737320,174431276587477684499317266116800178146449639308927105154928,550107590041392193345836655196872421343323923094118672943651,603890056890519589818234763677820292962781291381905772871189] | [116813019271198971574082703005911524338054388383153890344340,131876510484987562320392937867380054288313147950701805779789,-1059387854222186069599623475610000968387146622316394840559509,435154069695077308245376411340693552103968659043034097930423,-23615123524823778960521912431073867976470749914681645659187,738999886672222902374572428134120160289900137182097516238085,136659487859324581172411207403505185216674271850716133630448,108603722432576924133459289523187501421718056199446751847313,-800184085820945591959232224452279040490645278940737809551202,396703721920759894435508001551129782546948766228942652737950,-2984145283978329067380840877397584180744333997377582661729,22339195402910417114697560288631945586857136040764035841886] | [-2363244426045073645115125532687680132252252749786863074853937,-398283912027157929922638946725780762002413774220972697631495,490996978569375174160558412325810954475655610692341986911315,-2372842211076754875604197278312628027949101481335622203771548,-494513019724164970512933219045318935580587295577421270297762,-2878710535974695193806790799542265140582923227369010069684598,-1787440418503051108557219785021461130579612723858115755055080,-620873616061602476506108641645811272837580845196348654154657,3388859572739516862919838757847656994213882481938933334522637,-2787645412824343044955083955768755769494190066545637474621423,-255659107863555403006861596375810666916697326301890492801846,-173019442443403282483020324985247213605845943813335753621395] | [[-76255466264864024562,574976619182453548751,-410912154994239072525,-31789499151889423750,98944123875620245976,4100843110049148622,-18443691360184651017,16168920464089443214,-10679813183575182224,4090625671261587240,2491954298521693774,-1562586391873985359],[-225378850737875076568,1560838419937249024125,-1110693374098886450142,-52168407012472349762,239843255161222249548,-67526380622387970845,303702358136483476171,-266244927740758198259,175858746764260277856,-67358135546426859248,-41033672817967172331,25730270732493839249],[-1143076672082606259138,-3359404778788088666254,3161968776619797165099,131397334768029552939,-748254520763198004600,134869568786731790386,-606580801515681978256,531767559064840893692,-351240405969682436119,134533535067225092251,81956025299840236775,-51390737760151404945],[437902930760029985903,1723062009546881557824,-1533541918838924868974,-75480883596196037846,364959795242153338197,-44836052751024193562,201651781489133161572,-176780859789181333795,116766395206989909029,-44724341668164948955,-27245469134838732069,17084341930178084270],[-116515282220682361858,1095185124255255352473,-742256738345474271815,-43069805435791322049,161962194099002100445,-23364721932911470410,105083688520332441499,-92123087975019849516,60848673951509817090,-23306507656058763737,-14198011894628425224,8902900101888935292],[492116659900239619031,-689115779210625285038,388376900092047997902,-706167076663281708141,508438101344073156438,-597144261551555077215,244440578084751333616,-28317315230067686391,1311666979712081685052,-1129129560475715178776,1118651268638545112499,-856397959004177195663],[-4129995438578914414,472788220286855365832,-353099221448757133017,-134927533534818062959,173009814927502261252,-83952913967896370431,20212943597260868940,9504575580452337588,182996598984825573217,-161837906232060177423,232336757269634332378,-137505085180095121035],[-184189161289661667495,1517104067510589526571,-1088632224892509438875,-115479567741539731036,287692216686935641108,-125194584435127534565,342979318047416587463,-283911197142260477453,304093662979442839142,-172977514239292176772,233072758785011484700,-69600511017036917438],[221029099755913617067,-4010267149008595015528,2946724234588896566014,799022286752903492895,-1176461533242183272895,-591345073576490037939,-134171119919809879185,647014626500133216084,-1759940063803677144057,1196743479759692651983,-1413105963423863697225,761964346708066955729],[-152296014882126691288,2257664774368366809280,-1651682122480505427399,-398076333800774920316,618715883489094388308,327488527485243067312,22708179167802599090,-274945823841941932105,810011746346829233788,-556718231584634783176,712005961897143203602,-368387223798279189221],[-166549660071120825252,1041039291504533813211,-736588186406976396603,-4655098299836989149,134577318136575604311,77070371748322116532,92035132344269193479,-62477524028298568168,-35702438299378378253,43862858256744963808,39540884459842264457,39548842938962096411],[2779303962469530499,55490254752768157322,-42290562629299229585,-21898503212728939161,25413159691028250560,60977857525284958851,-274250136818374840043,240425225237425348762,-158804448067973617086,60825928395117925681,37054339826464635409,-23235019681964619363]] | 167470468266 | 2790552118362 | 148455457789 |
| 61 | [229708351181590633291726635130909072726839770064303907045846,529434697476532032664755198187572689613460793092951640068162,694261079441545192285097432349562925214769672960226720219921,193826406149054313737368537408329024265858429743044242371599,547385605030745721601701491076906687115693697997327885846599,436238425257764069782928078872097740224466587322128457948674,226446987994525871353939345484802353690613898920689089873451,526939143425740613847149092820456746515498105719784595912980,739267825139666079383380068241929448316889321389310333166668,174414161442179299039398932896963774033432375507582165207226,550107718530137431670747948752573821120210600525590904699239,603889093086869209731383782732321594722689594066788237804846] | [116914959983830314142432209488899287015514575854519514155825,131893689689279138085493197182208744059642682027519295859053,-1059409033298271035857820786648594511354814470038987967832822,435256423813140579851401446335903211272000679121628394931186,-23593792136709502298638487225935576706235734777425944341132,739124024825046957857475145171884447371702377769924455265341,136736597267995243416696312567040916809635510810558908959849,108630500488681081854799002197586938929826255286277034112071,-800330229270164529023703220678186131003264451789318585346692,396823962414452864311008089868181875089191644952291327540265,-2973114159278664815004519011408778039420191547218752340873,22346658260119336988548691523128595869288827056073159482701] | [-2363141260239582030929507403651314788684509772988319897216450,-398213807540066720443683700754239395821689032680687539040941,490951051412742711413326908173198171347359694507488354818832,-2372710631393817582604572718724038590370881807147529727212196,-494496815014556817459644282051694631956631140355453488953946,-2876838905886810487065928206808552021006567194978105336692118,-1787665072053833733295500468624386016355959007944534017646212,-620665897335006958000163056653187567173586806596124251387331,3386944830127670914781750179614896046526563644559008009442237,-2787192526335310314246584644421166313967664316179737885352029,-255788641247896195164976404300257481218230438413939802790044,-172988942774308448973547594858338021275739340477343392748907] | [[-76238316067966149275,574786277809338437593,-410779345770912130737,-31777691611421436880,98911388961469371807,4096938602023434390,-18424787202370902755,16152122358411860709,-10668744123871047447,4086401554810610206,2489802620154883056,-1561277827627258203],[-225322351314449087401,1560308988674323295193,-1110325717999270587885,-52148897427045401894,239762634054707127246,-67528080743416301964,303687860312935423812,-266228501022124171208,175848330817502304020,-67354403116264809897,-41038348069446295123,25733872398001836948],[-1142712764781767372252,-3358179458166251423641,3160839551647524437428,131350002036022224421,-747987206028661579743,134855008458101289658,-606471093510478780958,531663959080111986010,-351172843632895383915,134508170555696060987,81954450875626999331,-51391088591401739906],[437870042556809498688,1722672524472694967363,-1533229685015811910166,-75461632088485000924,364884654328614952220,-44844224573090532845,201673828991835867040,-176797719647279944328,116777819703575981647,-44728888279957955767,-27252853578462327841,17089417324566295134],[-116435844417647387631,1094763118708174597042,-741983907932504124225,-43054070785260785183,161903797299485776700,-23359774414268459582,105053776609128421072,-92095579469463748092,60830654355936168879,-23299694664534718950,-14196265356319325307,8902036714282020546],[491799066393014891813,-688597058142396339583,388073307125938282661,-705762653887390581599,508177051459109725567,-596871101002315592779,244336840799197879962,-28307885115701611880,1311110359495192860368,-1128668878246835475586,1118425223435068912611,-856238215358931260299],[-4126170236388852853,472622608093544714739,-352981099318966524979,-134902640766079914269,172971286453656106856,-83955615864283101724,20230799961614447005,9488994636055373883,183011088893161639469,-161848316120615310851,232375310990060616919,-137536697167548303749],[-184158419886615628177,1516601807249560621231,-1088278170634923833255,-115423382395660319298,287585426263657551097,-125168905691508963243,342943057334904869586,-283882922794352794824,304025177631956014854,-172928928460824828572,233048112171760725643,-69582707117409569267],[221142509864841721864,-4009066363317125210637,2945835393559636214083,798580635522013685065,-1175958750788766501536,-591437396838488489529,-134102223996972294642,646883905970766237637,-1759289682435689110792,1196264446881164253415,-1412863018852934431913,761795173173193883517],[-152345630122619325335,2257164199085883220072,-1651316577522344758070,-397903886506922087996,618517933459862508867,327558917611460056016,22698655731645671079,-274934526802722212035,809815032814423460125,-556564545987612426509,711967050385023602311,-368349864213835374392],[-166490925625911866922,1040636727107886834376,-736311238176381706543,-4664427954007722505,134535519480474707955,77065392497256298922,92014508540783353002,-62463307748216951863,-35674063570040541581,43836643321708173466,39555456648670353387,39536718008127479307],[2776695947639677514,55468375729194450927,-42274107472979714214,-21889537616839488735,25403368696460616574,60969600726684119184,-274193008078730223100,240371786532154046075,-158769542986637726909,60812791063711182230,37052610835837680104,-23234540475379620399]] | 167421506519 | 2790762675124 | 148358905710 |
| 62 | [229703305639028497627922106921291984697977077174761990865168,529429007626791450553530926428449515731418902103516450725936,694306779474565372755234000609378606956893595559821175809268,193807628347310435199200637918092482201494146515314979145708,547386622332717550583569531633649490726182714489478969976373,436206539094188672660903678071619825753998794968130646231477,226441087944143523778978629490207526419070660569270817922602,526934456869946660608543186531381703019814507449444578088540,739302352021132691484088286584007880314999601856255294285946,174397041110505215850559755447725938571070652395798436170889,550107846542914137735822195382393907665915413865512273819700,603888128961323004090472908323964591927921364229349825953684] | [117016896244634482744203955951904912832466799024531371052836,131910865869060639988383956756945949500892242633539754893067,-1059430210392730907823435266172084893548230207986670732231169,435358772253741549420678492546002637468878637380492885727490,-23572461448071748616631301422064563047385063308200423650155,739248082268976438521590535847435504887457245565383273983764,136813716361269262254023595961975473707833862205288549701975,108657269586167859599326915780303361963822940256782270659045,-800476290150266363154300109585699525261397367521786822616318,396944183375286446213655517190802552012850256884233590355779,-2962077449455161112833625208980499446953650002283027184479,22354119801393503805655885425221840825748833828521773429167] | [-2363038021247945027440084594986034094042316386230647981709453,-398143683450310477087694724226581911139773463953218595323933,490905102377979837018202407031642187182293268317305064605737,-2372578980854944464346666158635440093704002858046645939968319,-494480589150551508722224516900728739346147743324327378404493,-2874968543531774777649725711255375849962829797062571182508150,-1787889436091028558744488944844722209758332900388503362706764,-620458258146882453722436006749535337591627495607140975892095,3385031332821233212834498368930766615367302027941428632676920,-2786739790069950543976236531511945057509569967700369848449029,-255918056910014215403232956516142733499159092420295833283344,-172958430361091090603047148666076812079967406790425060718672] | [[-76221178415744607043,574596072519092754268,-410646632185901710877,-31765892393852570101,98878677477301490149,4093034462210479562,-18405887274856780231,16135328380011957802,-10657677743547976125,4082178437461421914,2487650678678735548,-1559969046599772480],[-225265895497591516450,1559779956101103238499,-1109958340888862481487,-52129402493642558995,239682073972575781135,-67529781088691849318,303673362609058902109,-266212074038562590621,175837914774588050340,-67350670704558566448,-41043022556322664704,25737474041478216509],[-1142349153245788063203,-3356955082637329383590,3159711204331431184884,131302705921485045984,-747720099013036693986,134840452346402820707,-606361414469556710571,531560385725059361122,-351105298811993810994,134482812726858517528,81952875278680531852,-51391439244393836882],[437837189418767847528,1722283322443407273021,-1532917684020544397831,-75442394645608457027,364809569329772060731,-44852394503568364091,201695862779088491403,-176814566460814499714,116789235726921759346,-44733431736633274414,-27260237033750757152,17094492542743309821],[-116356474488192367011,1094341438018867019675,-741711287386576115583,-43038347838341629106,161845445088691936726,-23354829454182771536,105023879526545656696,-92068084444835051963,60812643620835126206,-23292885043769060568,-14194519464355352468,8901173780360969668],[491481765595769865764,-688078907603597527450,387770061346234608535,-705358575653807705217,507916205331862585922,-596598073355425012033,244233137850563193237,-28298445215995500979,1310553999016878375433,-1128208413260627664121,1118199258650273441690,-856078522002475351148],[-4122353394844734037,472457119475026905970,-352863064717779318971,-134877759893120238047,172932782559773588090,-83958306067130249642,20248646407486236105,9473419441670535281,183025552446467021583,-161858705865665051108,232413855031043130079,-137568302225598632476],[-184127699424304168268,1516099916976933009240,-1087924379792454461996,-115367241868206744539,287478717295883621448,-125143239912287765509,342906808025080829734,-283854654981038674213,303956718933416971595,-172880362693108555368,233023469577555236564,-69564905814569644147],[221255787100830189785,-4007866336110224796792,2944947132276530367310,798139356128946846355,-1175456358384364363705,-591529642773447014273,-134033351990506446694,646753207296120094347,-1758639584570463113608,1195785634767472827922,-1412620148568349315376,761626046739395479919],[-152395207353284365884,2256663981195498558426,-1650951301203560993830,-397731575661101928181,618320136263980954254,327629284908266675126,22689132878929174971,-274923225410771203050,809618386480614579414,-556410915748910399739,711928153354483397703,-368312511747863769909],[-166432239752377122518,1040234479870047428824,-736034508708850673393,-4673747306383924180,134493751855572731787,77060416173937983812,91993892346087987262,-62449097850571875796,-35645704298318054987,43810442475426311057,39570021986483521686,39524597262236144055],[2774091216882327339,55446504303729124052,-42257658414983807131,-21880578424735492312,25393583691500131644,60961346381360732468,-274135895990685633667,240318363168554965726,-158734647983996581266,60799657568045801762,37050881466769104423,-23234061250149204556]] | 167372585739 | 2790974006398 | 148262404669 |
| 63 | [229698255699352505013746588201147065031803981976335365854983,529423317036189701947358696774902252017851516326952820660069,694352480421056096762895924569399817094781580791003062132212,193788846130698991863995512180884597068377344865925884868362,547387638714565611409120012558155579765274817810386343162737,436174647580904805213720956738182106377586884733254370472266,226435184566877199861337154371576804991309060371266299010598,526929769159611131570376234806303750969123310205711368139099,739336885201426719988446196274725461497958242312741590835454,174379915593297881363954428275039022837983675259456519887029,550107974079481496362969137837315591413553199159427423977057,603887164513937750041317760792381883912280265316367081045229] | [117118828050454682260447922241359591935103038884904695855687,131928039023486601328692886361844715412436243203560913320514,-1059451385504622034205894765823496756349846037173688984811771,435461115013824007320359808713288659425844913533981980022516,-23551131459822989346978923920691982351384130123768536210352,739372059058683092537640632856355016642276547319319688655156,136890845126660600675958690304606383051326945419032073920779,108684029728467331160470685279784117514135284822978736829612,-800622268514955458854518517052046185042653576966234663780590,397064384809738663778967365564587625478140955447492199194367,-2951035159584851881840774326631905680359531723807623037389,22361580026183235793938406656053080079438561355124016034388] | [-2362934709080604836203012009182502686077384686393642436724286,-398073539763947721292683150471896832868612193046195581544405,490859131469839240515585920339178593385134239257918607451441,-2372447259473710401412159014462922617038690748547530186834165,-494464342135060136980646903548362241304316302753830681792032,-2873099448248258799633949518929836793554674131433762726861688,-1788113510738405723127508284743401003990323431844124144854743,-620250698452443118184559012225109395658333467229002159771124,3383119080161918336650559197299210950143367882947216026041780,-2786287203928411275351651007140587414746623925670392560430367,-256047354902435274981674381419499125455423364353138415131870,-172927905206515797783112295133234183200352291527982552743797] | [[-76204053292891929812,574406003154458428811,-410514014128695242547,-31754101489689773036,98845989396105227812,4089130690760991011,-18386991578141776329,16118538529331494192,-10646614042890525336,4077956319317653217,2485498474374181811,-1558660048910233063],[-225209483236247755778,1559251321760762969944,-1109591242448323343359,-52109922195582809746,239601574845039151899,-67531481659075340853,303658865032208706080,-266195646797015559238,175827498640037922139,-67346938313008545018,-41047696278111099495,25741075662740960381],[-1141985837137680244360,-3355731651120540316017,3158583733668274838735,131255446382553650357,-747453199478871624842,134825900452250543352,-606251764398745619476,531456839005304336119,-351037771510588251011,134457461582042764802,81951298508835342090,-51391789719042302345],[437804371308244525885,1721894403132704795007,-1532605915585570751260,-75423171251507657657,364734540181432443941,-44860562543601566599,201717882860427464885,-176831400238753436267,116800643282886344768,-44737972040404418811,-27267619500060254974,17099567584458390083],[-116277172354302175695,1093920081815931258907,-741438876467786952237,-43022636581681501427,161787137415644024341,-23349887052013466569,104993997268410570395,-92040602897281223464,60794641743673408418,-23286078792798688410,-14192774218666109498,8900311300093632032],[491164757162957845906,-687561326822691770499,387467162272812735870,-704954841578711516287,507655562753986000368,-596325178578234379453,244129469252737490788,-28288995554293635843,1309997898222839771010,-1127748165466867114507,1117973374292050961965,-855918878940451382965],[-4118544902797481499,472291754282216242272,-352745117539522405792,-134852890900889647249,172894303215316558147,-83960984585270483603,20266482937970893872,9457849997063543819,183039989661380538364,-161869075480469780663,232452389393315138453,-137599900353029094576],[-184096999878069544347,1515598396275378890549,-1087570852068311531044,-115311146108901278016,287372089692103628489,-125117587095027652371,342870570120841254296,-283826393705961001262,303888286881192306165,-172831816933002885272,232998831003046629677,-69547107109253623812],[221368931624561442409,-4006667066638758346521,2944059450160350510341,797698448158868449512,-1174954355607779442618,-591621811420904312272,-133964503914178813400,646622530506039505625,-1757989770158966829117,1195307043369797116833,-1412377352578042224115,761456967412580376630],[-152444746614987285371,2256164120291432549405,-1650586293220256241887,-397559401109242941770,618122491729032674251,327699629378207368907,22679610617193700861,-274911919675581674619,809421807344280454467,-556257340864738870280,711889270806381017484,-368275166401986121601],[-166373602393883066089,1039832549421767455596,-735757997749802706040,-4683056367975096636,134452015224835793992,77055442775224160659,91973283761058465300,-62434894334782806835,-35617360478792069333,43784255713298795275,39584580473026218177,39512480701808426037],[2771489767050861702,55424640466449878259,-42241215447320459265,-21871625629122730512,25383804669119508433,60953094489669663709,-274078800556669055049,240264955148910682704,-158699763061517861995,60786527908663254433,37049151719400102076,-23233582006355005586]] | 167323705890 | 2791186112329 | 148165954689 |
| 64 | [229693201362754897535811035602375762633130239033116932293221,529417625704857309407062697326679939893345943696124652061959,694398182280931822173693853978058847703831383591692915019416,193770059499465089355103354433635673669794425564175256095019,547388654176320136336753141921537455616063985057056548434518,436142750721390458468545662511574756041581832569316797031205,226429277862309944064950016212456207858749435805024781205528,526925080295120251422700353729355388113819984896442812350676,739371424676989867123132388834626991071843496883051535263640,174362784891399462662072430033004103049699469736702467544761,550108101139598911332507834797965920610808637664971773546450,603886199744770248438705462093333694374197769766937186573311] | [117220755398134568215588479034479302282208546324267265257777,131945209151711816808893276476073556328280147897006652758400,-1059472558633000968789438737212478964458477486091695170981630,435563452090332329684258849168907054314043323491477138401451,-23529802172875570289740166216084035008079337385394630847489,739495955248810134158564366024807860129202089050454889665964,136967983551688562059345579421718451180627190068124204090145,108710780919007637917827066872385369687076932038093512867026,-800768164417907778057906813733288512442111080397933925246040,397184566724283232378195148704003263290817372825393437992443,-2939987294742504649582853946299031016629834264770793127404,22369038933938970470699781929304344001439292594981148771082] | [-2362831323748012913274780137295413691910240865582118647942831,-398003376487039629570821588177166818907982716031677007231584,490813138693076333770594795334401821527035106087757011106653,-2372315467263699035389762933089574696891900374669902513597037,-494448073970996438919635030102973768936569990191994398458649,-2871231619374643769133872820591353790562420119963459510626276,-1788337296119796993232513173521497063003106764015862239562367,-620043218206880265131070018835638167075639865531653111003401,3381208071491153476100815633734540279559215569044998393865420,-2785834767810796385470522514621020038128836203178318478131287,-256176535277712744781519409627882317929299038500894086925090,-172897367313348720601081133936563449561577199015497801646793] | [[-76186940684123851370,574216069558416329285,-410381491488947970051,-31742318889454450067,98813324690910255989,4085227287825310479,-18368100112722477964,16101752806809486474,-10635553022181464519,4073735200482263225,2483346007522217303,-1557350834677381886],[-225153114479440837917,1558723085197170825497,-1109224422358799575667,-52090456516210485902,239521136602414214352,-67533182455425623291,303644367589726760716,-266179219304413257349,175817082418364489883,-67343205943312184040,-41052369234326453017,25744677261608055262],[-1141622816120967851425,-3354509162536743366788,3157457138656336407135,131208223377427242719,-747186507189075247362,134811352776254107468,-606142143303843880130,531353318926438956151,-350970261732270051988,134432117122571840035,81949720565925971216,-51392140015261737482],[437771588187635950935,1721505766214769628290,-1532294379443745595183,-75403961890148252123,364659566819501344069,-44868728694332939145,201739889245382174086,-176848220990058724766,116812042377324570332,-44742509193483268444,-27275000976747101193,17104642449460794782],[-116197937938079908111,1093499049728530110400,-741166674936597814565,-43006937001948361187,161728874229442951828,-23344947207118977062,104964129830545309237,-92013134822945743897,60776648721915131702,-23279275910659520331,-14191029619181098837,8899449273447816686],[490848040749539000791,-687044315029381445311,387164609426329411346,-704551451278822755749,507395123517409386947,-596052416638016362713,244025835019547477443,-28279536153905041367,1309442057058610658244,-1127288134815199557760,1117747570368227935577,-855759286178457011005],[-4114744749110816427,472126512366255012407,-352627257678685097255,-134828033774368641933,172855848389799126083,-83963651427536674857,20284309556167181320,9442286301996395918,183054400554544391944,-161879424978292192679,232490914077620835862,-137631491548630641132],[-184066321223293225116,1515097244728201480417,-1087217587166153563229,-115255095067539365793,287265543360943382451,-125091947237284018547,342834343625067970139,-283798138972750841335,303819881472627859116,-172783291177353593080,232974196448881398708,-69529311002194431314],[221481943596492110462,-4005468554154660442569,2943172346632695847570,797257911197533454567,-1174452742038412759958,-591713902820426085560,-133895679781700065990,646491875630299727523,-1757340239151974174940,1194828672639181482825,-1412134630889881398676,761287935198613110564],[-152494247948535183468,2255664615968519804556,-1650221553268992161504,-397387362697500728978,617924999682856670445,327769951023845086068,22670088953963616996,-274900609606631978263,809225295404239718248,-556103821331264623658,711850402741564038536,-368237828177816214746],[-166315013493880643774,1039430935394362963719,-735481705045046576941,-4692355149777285649,134410309551289307271,77050472297971881539,91952682786564405945,-62420697200265588511,-35589032106036125025,43758083030718088977,39599132108048119005,39500368327361028316],[2768891595003480203,55402784207449469030,-42224778562010665617,-21862679222718079400,25374031622302129156,60944845051963656702,-274021721779093413140,240211562475489734751,-158664888220660058492,60773402086101533809,37047421593871891146,-23233102744078676044]] | 167274866934 | 2791398993061 | 148069555793 |
| 65 | [229688142629428053425780689330597400680604005652448336816316,529411933632924831947327289908118720861713806047559420385063,694443885054106966160358942247564739609254104967928151167872,193751268453853965093244077342056415047474792741953263232743,547389668718011396977887939207868972848441483841557970986922,436110848519121266931665343472009938583388773510907959157208,226423367830025339116549740305987767996347585163117022331530,526920390276860097018019067774462352443391389330799333708444,739405970444266149914313029126735915815731392955886296454660,174345649005651847664623522421621431237625311255547464914147,550108227723026005285375979844692434927727333852613715080555,603885234653877323841247415760616739654505047433452196862960] | [117322678284518247176566730052903575738950309928139164418647,131962376252891342648803640406879732288107019836613520437503,-1059493729776924470550520779784946314146016556663286492853004,435665783480211478790688695921158802099430805804340062788344,-23508473588141711498519853783064971418652890670487477913863,739619770893972231273699773221392804293576206938322669046636,137045131623877792817211239214221434350004040038680974884981,108737523161214987855282596943085759737421631128364649557856,-800913977912770867774031238401080247553249624886198399584006,397304729125389557242206485710076433970908556768513320663318,-2928933860000619364812093584674307591558568787775206736430,22376496524111264709892178868818029806125142499845108228488] | [-2362727865260629966072107143864357005587716005056136134341210,-397933193625650032026848893203836515777875968918355043007379,490767124052449249582714070389246966081116058113257642284232,-2372183604238502764985899175116117239847877485569709494510131,-494431784661276794309283372442472775888244007789091034799746,-2869365056249023380748098812377564704514740322120213656959489,-1788560792359095414130679933267570190277235362457146884980464,-619835817365362525096029032582035143351641422629956545774230,3379298306150080426709304106001767313631054121015627096073763,-2785382481617166430933835321144964938809567094319915651754096,-256305598088427395572692117999588062107474551534269431768972,-172866816684357568118427766298226082927444644093677362597814] | [[-76169840574179263395,574026271574185808172,-410249064156482633770,-31730544583682432881,98780683334787212318,4081324253553415379,-18349212879092571645,16084971212882213315,-10624494681701778860,4069515081057540595,2481193278403902316,-1556041404019997932],[-225096789176271288550,1558195245954888043212,-1108857880301921849160,-52071005438895214165,239440759175123776101,-67534883478599664340,303629870288942135945,-266162791567673956664,175806666114072498284,-67339473597163947723,-41057041424483613972,25748278837897492136],[-1141260089859685871159,-3353287615808435941310,3156331418295417582295,131161036864368479992,-746920021906916349453,134796809319018660551,-606032551190618437213,531249825494026042853,-350902769480611408086,134406779349761526800,81948141449786993877,-51392490132966738215],[437738840019395355395,1721117411364278701273,-1531983075328328988423,-75384766545520241198,364584649179981280260,-44876892956904200180,201761881943474962915,-176865028723685871293,116823433016086998793,-44747043198080068585,-27282381463167620730,17109717137499779930],[-116118771161746653102,1093078341386389455825,-740894682553833664940,-42991249085830440285,161670655479266952839,-23340009918857109307,104934277208767758086,-91985680217968125393,60758664553021816862,-23272476396386495175,-14189285665829722598,8898587700391292359],[490531616010979449062,-686527871454606048701,386862402328220889651,-704148404371403504840,507134887414336845677,-595779787501965475483,243922235164756461663,-28270067038103524947,1308886475469557168867,-1126828321255141445659,1117521846886565139448,-855599743722045707615],[-4110952922661242428,471961393578513067463,-352509485029918822520,-134803188498567540996,172817418052787549742,-83966306602761879203,20302126265177948622,9426728356227370352,183068785142604129538,-161889754372397261214,232529429084715323315,-137663075811202173391],[-184035663435395813068,1514596461919333808598,-1086864584790086545839,-115199088693989495023,287159078211164472904,-125066320336603963609,342798128540627869964,-283769890785027457325,303751502705048762385,-172734785422992734335,232949565915700927954,-69511517494121437110],[221594823176853413491,-4004270797910933627367,2942285821115991726897,796817744831285255878,-1173951517256262688839,-591805917011604904235,-133826879606725170101,646361242698606649162,-1756690991500065802527,1194350522526536277236,-1411891983511669558615,761118950103314200464],[-152543711394676889371,2255165467822208645492,-1649857081046789086720,-397215460272257569585,617727659953547517852,327840249847761235155,22660567896747092940,-274889295213386063147,809028850659251898920,-555950357144611159648,711811549160869206602,-368200497076959887522],[-166256472995905117398,1039029637419713123761,-735205630340779684049,-4701643662773100624,134368634798017862521,77045504739038267970,91932089423469686192,-62406506446432448140,-35560719174616178408,43731924423069722207,39613676891304118537,39488260139407027752],[2766296697603191099,55380935516835677256,-42208347751087442413,-21853739198249489417,25364264544042025323,60936598068593337767,-273964659660356602346,240158185150546646446,-158630023462872483508,60760280100895162853,37045691090325714065,-23232623463401887280]] | 167226068835 | 2791612648739 | 147973208001 |
| 66 | [229683079499564487040909910061937461599845755791833190785575,529406240820522865025413505246963084011300011919217225906497,694489588740495905211596724818087886492807829918630483596406,193732472994110988271214734017563951708034410480303386469021,547390682339669704291535469650729183435142566635436782389853,436078940977570509820156650572535507269671594337233828435643,226417454469607505775127587440994407208097878301228829734124,526915699105216597454708980148598365742024782541262685255561,739440522499701898961646423766436890036970913541134799815829,174328507936896645314503859492003789089698149640827309682210,550108353829522619625288234973494496616346979468769985216804,603884269241315824506229185946962866458009863792148899568635] | [117424596706450277151847343763069372977560921682039439628117,131979540326180496700023389067262237219344918140927331518715,-1059514898935449503775151196728576202442590858975979910612612,435768109180407003440132664607501692371835997453264648202505,-23487145706533507166474272506597775135611809578335564867457,739743506048755493048984619550862001027907183499157279709568,137122289330758285034577843434829922912771074378759701966053,108764256458513654585922730080810179592362307847371065486197,-801059709053163847820412440043713054475285386692134902206645,397424872019522731600171453991868358334941626278796227709377,-2917874860429427218969479965914483307412718035155617161690,22383952796150794809350510842299498409542986986562818977130] | [-2362624333628925950229229001318988251520378546087630744404793,-397862991185845410875734180756746435994981373854666860521684,490721087552718840294673992179318775687922164871277823803602,-2372051670411722742132917895160417941031139418870117209737929,-494415474208820225084940920416389141129261463006293680538507,-2867499758209205799278916023392180677349041937331487012898660,-1788783999580254959710979858253175708500756211598556219554820,-619628495883036002587041191123265628650017762278281466144810,3377389783479557580284021625044113014865420374155011026555357,-2784930345247538990637957267894722193297749897505860781314788,-256434543387187238652665780492660273364582075137196810981521,-172836253322311607668744371122781153331538324787329473751594] | [[-76152752947820171588,573836609045224249799,-410116732021289152262,-31718778562923953074,98748065300847623122,4077421588094919582,-18330329877742849038,16068193747983220608,-10613439021730672689,4065295961145104813,2479040287300361926,-1554731757056897208],[-225040507275916979540,1557667803579167448246,-1108491615959804184087,-52051568947031868160,239360442493696276682,-67536584729452554904,303615373137171061578,-266146363593704034167,175796249731658875401,-67335741276255329503,-41061712848097506342,25751880391427266302],[-1140897658018379371323,-3352067009859750595231,3155206571586837854249,131113886801703350402,-746653743396022948774,134782270081144855280,-605922988064804859735,531146358713599242729,-350835294759165391354,134381448264920367049,81946561160253018258,-51392840072071895217],[437706126766032679585,1720729338256402836617,-1531672002972985654316,-75365585201637930869,364509787198971863919,-44885055332455988024,201783860964221133544,-176881823448583918076,116834815205019923809,-44751574056403430512,-27289760958678183640,17114791648324598724],[-116039671947641270121,1092657956419797194191,-740622899080682557278,-42975572820036204988,161612481114371435633,-23335075186585045338,104904439398891552340,-91958239078483922764,60740689234452397083,-23265680249013575705,-14187542358541282603,8897726580891787469],[490215482603250348022,-686011995330539868375,386560540500701458413,-703745700474256223851,506874854237246686391,-595507291137198299838,243818669702064471542,-28260588230127716240,1308331153400878404659,-1126368724736080310027,1117296203854757780015,-855440251576726838736],[-4107169412338030322,471796397770587398096,-352391799488036825082,-134778355058526414071,172779012173900128928,-83968950119779319760,20319933068110120895,9411176159511036207,183083143442208605287,-161900063676052211499,232567934415364588986,-137694653139550529215],[-184005026489836966331,1514096047433337521281,-1086511844644663080137,-115143126938193060537,287052694151664014780,-125040706390526313095,342761924870372937637,-283741649146398327441,303683150575759486845,-172686299666738679330,232924939404141501316,-69493726585760465141],[221707570525651538744,-4003073797161646357339,2941399873033488067192,796377948647054631507,-1173450680841923869219,-591897854034060072866,-133758103402853486900,646230631740596889084,-1756042027153629589183,1193872592982638206756,-1411649410451144017327,760950012132460223422],[-152593136994103063858,2254666675448559930184,-1649492876251125151085,-397043693680122004124,617530472369454887626,327910525852555640008,22651047453036122720,-274877976505293491663,808832473108017544717,-555796948300858788269,711772710065122455945,-368163173101015044449],[-166197980843575908423,1038628655130259161816,-734929773383587314419,-4710921917931734858,134326990928165112782,77040540095280517702,91911503672632449567,-62392322072692003935,-35532421679090628110,43705779885732315173,39628214822554320268,39476156138455881101],[2763705071717802119,55359094384731280806,-42191923006595804325,-21844805548455964351,25354503427343857533,60928353539907219491,-273907614202841511479,240104823176321953242,-158595168789595288928,60747161953575199906,37043960208902837580,-23232144164406329424]] | 167177311554 | 2791827079508 | 147876911337 |
| 67 | [229678011973356848844559806863834041381050665320302907945997,529400547267782040529870603137204426164723694804333487117259,694535293340012975140946058016497891670179120951013314871034,193713673120481659828580652132837893498627517925566192623611,547391695041325408578867162059258940125861230082707223770961,436047028100209112294083951351264014756415848626671272115096,226411537780641102601281484421008580202270229599070071858993,526911006780575534160483359362688560703591362161228927044465,739475080839745757211760234437100280576690341484880513469647,174311361685975185763842069495286724455628466698305151529742,550108479458848814420843875195297320271138394665324257800078,603883303507142622384457476850234249703579386530303597887780] | [117526510660775667990289762361438149582155302442261122925775,131996701370734858560304546473615094435564863684093375042529,-1059536066107633238176179525549032212325603275695699815094500,435870429187865039332746978233789904632888288980335504570636,-23465818528962925512356321919358962600597966594600400118887,739867160767717457652971826324743293773074396507776848116691,137199456659865379089217706108576542823022466758266314143845,108790980814325976383713375851103224787237220517863902579078,-801205357892677398640229819901838236728267049095552408513120,397544995413143534833018228358391740445522105201389283375264,-2906810301096889474544513303656147844863159130578065486405,22391407749508356557996250130274069451807651829474911736570] | [-2362520728863380066452589439902445022978592048630872733102065,-397792769173694898959600796778631853425688816241848725825661,490675029198648676400554428154489993712023890409810544591222,-2371919665796968868094859389669329756502108297060799796358425,-494399142616548394426358659619396936453999334705101409698893,-2865635724592715646736466938977009824929620899237250118318942,-1789006917907290184029478206420598093892566068970638111215148,-619421253715024432897257292091229403226594569724004122762724,3375482502820161910831075415515584692507766455726758142103059,-2784478358601889007746881630602308320052918002109936351869098,-256563371226627366856051983203632886136231424382865883458984,-172805677229981664155314515125963118307652504460965545340919] | [[-76135677789831651917,573647081815226618790,-409984494973524305080,-31707020817743614816,98715470562243825825,4073519291599074209,-18311451109161212516,16051420412543326633,-10602386042545572853,4061077840845907482,2476887034492785929,-1553421893906932730],[-224984268727632982291,1557140757615952140878,-1108125629015043033210,-52032147024040520520,239280186488765587144,-67538286208837511291,303600876141716942254,-266129935389397985968,175785833275612741738,-67332008982274855493,-41066383504683089478,25755481922015377405],[-1140535520262102532828,-3350847343616451932205,3154082597533431631188,131066773147821053321,-746387671420381611163,134767735063228857066,-605813453932107393066,531042918590663075475,-350767837571465983432,134356123869349673142,81944979697158686138,-51393189832491793932],[437673448390114463743,1720341546566805814199,-1531361162111784212864,-75346417842539886208,364434980812669614468,-44893215822127861067,201805826317128947368,-176898605173695444344,116846188949965370520,-44756101770660331739,-27297139462635205230,17119865981684501576],[-115960640218220165937,1092237894459602175599,-740351324278694948157,-42959908191294317541,161554351084088836655,-23330143009659344757,104874616396726090643,-91930811400624745329,60722722763663225678,-23258887467573751542,-14185799697244980409,8896865914916990140],[489899640182826984199,-685496685890589658715,386259023466761966380,-703343339205722793011,506615023778890957623,-595234927510753708296,243715138645108370680,-28251099753181106898,1307776090797606886177,-1125909345207275121402,1117070641280435607827,-855280809747965740316],[-4103394207043202952,471631524794301712715,-352274200948013860444,-134753533439315013606,172740630722807098831,-83971581987422369774,20337729968074684025,9395629711598260838,183097475470009942180,-161910352902526490281,232606430070345488226,-137726223532490469546],[-183974410362115320705,1513596000855401685767,-1086159366434881532828,-115087209750164231718,286946391091474394955,-125015105396581639582,342725732617140273487,-283713414060459162978,303614825082043889791,-172637833905396147064,232900316914834311334,-69475938277833798908],[221820185802668019270,-4001877551161930962050,2940514501809257789445,795938522232358694905,-1172950232376586125742,-591989713927437497179,-133689351183628874083,646100042785837891525,-1755393346062861129311,1193394883958130699511,-1411406911715976796737,760781121291783891310],[-152642524787446301136,2254168238444245881957,-1649128938579935414409,-396872062767928416017,617333436759183070849,327980779040846495295,22641527630306547963,-274866653491789455010,808636162749178348637,-555643594796044725632,711733885455138928985,-368125856251571669813],[-166139536980596442253,1038227988159003295898,-734654133920441909478,-4720189926208985765,134285377904933657458,77035578363555911509,91890925534905114493,-62378144078449272098,-35504139614010341342,43679649414077601190,39642745901564027742,39464056325013431111],[2761116714219911292,55337260801274026148,-42175504320592741733,-21835878266087540363,25344748265222895308,60920111466251704466,-273850585408916049614,240051476555042225497,-158560324202259481527,60734047644669244665,37042228949744552735,-23231664847173711380]] | 167128595057 | 2792042285514 | 147780665821 |
| 68 | [229672940050997925386698661992618827286180312545346178216751,529394852974833026769242700345627564839681222779215287454681,694580998852572471095643115819631551706822352958510547802123,193694868833211612426350287382360593375524235708473350843144,547392706823008899477778211847241914529416462583988170244985,436015109890505646689225557527871613742885202722651387381977,226405617762711325726451227581638864747520357427859667018939,526906313303322540975897350236113059576279850502061168863889,739509645460848678731205031478699396318532165885988453450403,174294210253728520560124672937040633694348854101467259034280,550108604610764868307584040066177892085126422789014142011159,603882337451414613115104213831982568227724116181822408457152] | [117628420144339881779883675918902243521297321840662815306358,132013859385710269687859474055818571578779873463451105175670,-1059557231292533049010517009983433773927401057486025031549599,435972743499532309445695402713632406363212710649761381645944,-23444492056341808666600406991280317307265358478943157872152,739990735105387080068456425339221539097064609709402830618773,137276633598739766257386078180993952523433257951344350339874,108817696232072355221938798754616280316730723934335430574110,-801350924484873749205590368677106615392787507823370429941970,397665099312708430641622667641525746836393857086495653930703,-2895740187068696300285324073191605204863543217517960771370,22398861383634865303010931805367618205189194126688027015133] | [-2362417050974480757372931480393591495436995077069233243927817,-397722527595270278263910967771884216632927039805941849098141,490628948995005045153116908139974927453168365157183941845473,-2371787590407859789570759383862203057360516966355342787536435,-494382789887385605836101418072466765829705898550299123116365,-2863772954736795984634008877987508145651847887090918529840550,-1789229547464275873472101534351866904722481804565712585663974,-619214090816429338545921651606631030710566128734998038593223,3373576463512190955759454765102826599602498991463909939434070,-2784026521580149130845877880339477956139421764948055703467982,-256692081659409795934366308476026513334883582171978644074836,-172775088410140119348278065587387299042056224698866041172296] | [[-76118615085021806960,573457689728125009556,-409852352903511416317,-31695271338720367581,98682899092168891546,4069617364214768424,-18292576573832680703,16034651206990627204,-10591335744422132108,4056860720260233603,2474733520262428789,-1552111814688994501],[-224928073480751421438,1556614107611874187506,-1107759919150716366907,-52012739653366395080,239199991091070810092,-67539987917605877419,303586379309870372368,-266113506961638441147,175775416750415419329,-67328276716908087939,-41071053393755358188,25759083429479829467],[-1140173676256417684088,-3349628616005933508736,3152959495139545366345,131019695861173879377,-746121805744336770638,134753204265862351588,-605703948798199010927,530939505130692982252,-350700397921028107226,134330806164343539847,81943397060338672957,-51393539414141014589],[437640804854263740584,1719954035971643436202,-1531050552479196414657,-75327264452288885339,364360229957367775518,-44901374427058297971,201827778011699625976,-176915373907956567196,116857554256761096124,-44760626343056116236,-27304516974395146166,17124940137328736154],[-115881675896057071845,1091818155137213137430,-740079957909783009502,-42944255186353597850,161496265337828474437,-23325213387435946557,104844808198076547575,-91903397180518268718,60704765138108083830,-23252098051099042090,-14184057681869917339,8896005702434548209],[489584088406687865903,-684981942369392321676,385957850750168354832,-702941320184683555475,506355395832294976533,-594962696589593085473,243611642007461973901,-28241601630432090300,1307221287604609000732,-1125450182617856647107,1116845159171163032013,-855121418241183794633],[-4099627295691520016,471466774501706016587,-352156689304985894455,-134728723626032707098,172702273669230523694,-83974202214524535472,20355516968186670507,9380089012236217808,183111781242663494078,-161920622065091736233,232644916050445723586,-137757786988844664890],[-183943815027768411871,1513096321771341597885,-1085807149866185189459,-115031337079989819689,286840168939763019423,-124989517352292283737,342689551783752119585,-283685185530793926073,303546526221165262351,-172589388135756239136,232875698448405468203,-69458152571060187535],[221932669167460111230,-4000682059167981608177,2939629706868195251611,795499465175299848925,-1172450171442033388017,-592081496731409551017,-133620622962539786749,645969475863828022616,-1754744948177764224867,1192917395403524270539,-1411164487313774741859,760612277586974127124],[-152691874815281230460,2253670156406548921172,-1648765267731610991514,-396700567382736614646,617136552951590503401,328051009415270322111,22632008436018080993,-274855326182294788769,808439919581317272965,-555490296626163189659,711695075331722995914,-368088546530211841077],[-166081141350753992873,1037827636139507674736,-734378711698702331957,-4729447698547275065,134243795691584926796,77030619540721819949,91870355011134382636,-62363972463105673920,-35475872973918680140,43653533003470449570,39657270128103735482,39451960699581912613],[2758531621986897799,55315434756616600042,-42159091685147198036,-21826957343905265060,25334999050704996975,60911871847971089014,-273793573280933171922,239998145288920092457,-158525489702286938711,60720937174701444147,37040497312992174840,-23231185511785760815]] | 167079919305 | 2792258266905 | 147684471475 |
| 69 | [229667863732680639284385158425464057526603405921314150894241,529389157941806528460770469023131565179558424845850127366422,694626705278088647565490441930630622300088713936738833966580,193676060132546610421633803538865835759690825213063729608882,547393717684750605957446070980090546686650010520152385058670,435983186351926333750323877851102918262307406299674439998701,226399694415403908622041606557976117934710416701311613423031,526901618673843104237894518231957035067661863121227847955426,739544216359463927478887874353515095915085578106655838778823,174277053640997422832400202022214574708208351304926349315829,550108729285031278389998887307331660150462495989939766069113,603881371074188716020547727536199517160590942630908073927635] | [117730325153988833246348649634958504586377392313119811823049,132031014370262833515604571903287103265479977769957145476453,-1059578394489206517196298979949254105988342714483108367698339,436075052112356124410315738310139061369069810761470236011547,-23423166289581872557447100193051677729649597351357268145550,740114229116264719989511067937515954756436175947695221497885,137353820134927491304566861749817759844038474854164864456068,108844402715171255818379870359188950502645327497040585685874,-801496408883286665006159008131395848529822276797054512369923,397785183724669565229696564589508498038974273367949661784486,-2884664523408265613243194283138722475905556939610901407588,22406313697981356016979330712885571327441675275526761929789] | [-2362313299972725704394792318153766350887822641939860178310592,-397652266456645978432911848577201607224492049067823523360185,490582846946556949170365029264973438586068407392593197839409,-2371655444258022894795500430579597140146174868542719724921432,-494366416024258802217224587497156316127504412103820470735880,-2861911447978410291581544012365888091300579583641549629770978,-1789451888375346699729616413532874103947498782873257772441058,-619007007142330185348037016183488985521822522648843089492243,3371671664895664792383702735503596579308659316145127609024994,-2783574834082210054277811786228065182506653702238399687625937,-256820674738223306305402043659137226716677826375030026159780,-172744486865560911181388074542931467008806386308154897049442] | [[-76101564818221722339,573268432628088196797,-409720305701740038869,-31683530116447478937,98650350863856547867,4065715806090530222,-18273706272239394011,16017886131750500813,-10580288127634232483,4052644599487702854,2472579744890609579,-1550801519522009496],[-224871921484681328879,1556087853114253314624,-1107394486050382760350,-51993346818479819183,239119856231456080187,-67541689856607127023,303571882648909151002,-266097078317296175589,175765000160540440830,-67324544481837628662,-41075722514829342832,25762684913638630919],[-1139812125667394337574,-3348410825957214746041,3151837263411034691425,130972654900277090837,-745856146132590050934,134738677689632552330,-605594472668721467307,530836118339135373905,-350632975811347658543,134305495151188856343,81941813249627687869,-51393888816934132221],[437608196121159928102,1719566806147562594337,-1530740173810096376520,-75308125014971873512,364285534569456131470,-44909531148384697866,201849716057427352138,-176932129660296942479,116868911131240590474,-44765147775794494661,-27311893493314512578,17130014115006547412],[-115802778903842821392,1091398738084597642951,-739808799736219942836,-42928613791982985264,161438223825076403842,-23320286319270170945,104815014798743886330,-91875996414288246670,60686816355238188312,-23245311998620499460,-14182316312345094512,8895145943412069234],[489268826932313817770,-684467764002812592783,385657021875460192227,-702539643030556362422,506095970190756859872,-594690598340600549366,243508179802636162841,-28232093885014001256,1306666743766585449642,-1124991236916827808718,1116619757534439234607,-854962077061758506537],[-4095868667210462922,471302146745076191879,-352039264454249802315,-134703925603808409496,172663940982944190733,-83976810809919438951,20373294071565145313,9364554061168394824,183126060776827807811,-161930871177021750441,232683392356463824874,-137789343507443681814],[-183913240462372597796,1512597009767597592126,-1085455194644461409763,-114975508877829144782,286734027605832061034,-124963942255172375321,342653382373015884984,-283656963560974847442,303478253990366376832,-172540962354596473595,232851084005476008783,-69440369466154851828],[222045020779361170432,-3999487320437052268273,2938745487636014687116,795060777064564742134,-1171950497620642613323,-592173202485674943570,-133551918753019378158,645838931003996666498,-1754096833448151375030,1192440127269196886650,-1410922137252079635224,760443481023676141240],[-152741187118124617543,2253172428933360499605,-1648401863404998182986,-396529207371831419358,616939820775789291902,328121216978481923653,22622489877614327926,-274843994586215988467,808243743602958673607,-555337053787165495652,711656279695668274283,-368051243938509742270],[-166022793897919527854,1037427598705893318983,-734103506466113134489,-4738695245875668930,134202244251439066636,77025663623635710111,91849792102161247258,-62349807226059042854,-35447621753351527568,43627430649268888485,39671787501949119927,39439869262659958599],[2755949791900912847,55293616240926601291,-42142685092340047027,-21818042774681176609,25325255776826589595,60903634685407566917,-273736577821230905468,239944829380154266229,-158490665291090424239,60707830544192498656,37038765298787043443,-23230706158324224149]] | 167031284262 | 2792475023827 | 147588328321 |
| 70 | [229662783018598049202234415989118735175865137904304771403837,529383462168833286719087908383265624116382592975083887102300,694672412616475718391731054575453169300884645964385069743054,193657247018732549842285386361186328631030689896156744791370,547394727626580996312884026555985355732588849671468700990453,435951257487935043864855816312758641605950435112640037586936,226393767738305121868434094042387201945608372933353424834576,526896922892522562863394436710288313156191970542178564673621,739578793532047076077989596843408449426155583697007017724867,174259891848622387477561388196521202893717376789877102613661,550108853481408760143484942985806508413325594638927117291842,603880404375521874101211042316845270599146936978139254758372] | [117832225686568890151597792228552553018299046742383521644793,132048166323548915565339925101528019170152842391287161866811,-1059599555696711429429987106258507499621985474679938577063755,436177355023284382889118061171761139288571665187277173788670,-23401841229594706797107605533585141033625808459590356793180,740237642854822129803727432190726699818889764627139518952885,137431016255979955061266251022347446329676799299998276723551,108871100267039204687216687166079490512291738671803343982266,-801641811141421436122947760183585068573562034888583391921430,397905248655474765501339329134449060450760885283265989371370,-2873583315176741927635551777851501478895377563915834650001,22413764691998983365002293959578605376712322844262188199130] | [-2362209475868621824543403328267261266625434058517230327465020,-397581985763899075284343687966114139041905282382867040284320,490536723058076105041333958782275250363979754050738950327715,-2371523227361094309638211494963162051597859653089328205979745,-494350021030097564950216229217422320094334644005640983332984,-2860051203654244436185093307892312285639518030609548405474520,-1789673940764696873583562923097231213198395626796048022629035,-618800002647784538113716097972494330262911079701249725290410,3369768106310328009731763268723517403832713787880740640028075,-2783123296007920857663394946816002535075756161124902868211318,-256949150515783285171643523913297065083390899362199469835622,-172713872599019533048360003415845030288602756855806813309411] | [[-76084526974285423261,573079310359521187037,-409588353258865639417,-31671797141532507403,98617825850581101783,4061814617374527217,-18254840204860620170,16001125187245613760,-10569243192453988657,4048429478627270874,2470425708658711923,-1549491008524941640],[-224815812688908498130,1555561993671095605775,-1107029329398080482764,-51973968502876176093,239039781840870365098,-67543392026688865855,303557386166098296837,-266080649463230125808,175754583510453558591,-67320812278743122506,-41080390867420109411,25766286374309794634],[-1139450868161608228549,-3347193972400937848960,3150715901355261556549,130925650223708802269,-745590692350199588577,134724155335122208105,-605485025549285348337,530732758221407679126,-350565571245901537696,134280190831165318198,81940228264860473804,-51394238040785716682],[437575622153538722617,1719179856771700339179,-1530430025839759818913,-75288999514699917277,364210894585420824520,-44917685987243380561,201871640463799270800,-176948872439639765675,116880259579233076669,-44769666071077544591,-27319269018749856179,17135087914467177628],[-115723949164385128598,1090979642934281022333,-739537849520639295088,-42912983994971500435,161380226495395270634,-23315361804516721153,104785236194524871360,-91848609098054522796,60668876412502199203,-23238529309168211392,-14180575588599412868,8894286637817120510],[488953855417687077290,-683954150027940732221,385356536367949212065,-702138307363295620249,505836746647847055978,-594418632730583172256,243404752044079001389,-28222576540025155709,1306112459228071694734,-1124532508053064038932,1116394436377698284750,-854802786215023579587],[-4092118310540219669,471137641376913578625,-351921926291263068250,-134679139357800515779,172625632633773504305,-83979407782440801119,20391061281333191782,9349024858134601654,183140314089164585370,-161941100251592466951,232721858989209129228,-137820893087125969460],[-183882686641542981311,1512098064431233854509,-1085103500476040784922,-114919725093913904311,286627966999118207800,-124938380102727854166,342617224387724170937,-283628748154562444100,303410008386869533988,-172492556558680818728,232826473586661905601,-69422588963829490328],[222157240797481028085,-3998293334227454694346,2937861843539248647032,794622457489423227425,-1171451210495382711727,-592264831229958586885,-133483238568445600360,645708408235704321369,-1753449001823644265083,1191963079505394330685,-1410679861538368311167,760274731607491507571],[-152790461736435465738,2252675055623179937495,-1648038725299397607926,-396357982582722244412,616743240061144740731,328191401733154340956,22612971962522811729,-274832658712945225141,808047634812568424260,-555183866274960151724,711617498547757648571,-368013948478031677373],[-165964494566047553687,1037027875492839064803,-733828517970803829854,-4747932579109898086,134160723547874823420,77020710609155152347,91829236808821001548,-62335648366703631592,-35419385946837313871,43601342346824127776,39686298022881030386,39427782014742606299],[2753371220848870561,55271805244386512567,-42126284534264070308,-21809134551198282907,25315518436634648936,60895399978901233139,-273679599032132374989,239891528830929565711,-158455850970073603930,60694727753659667729,37037032907270522308,-23230226786870866547]] | 166982689892 | 2792692556428 | 147492236379 |
| 71 | [229657697908943349832866841952685889100178005513932447791883,529377765656044079044914192411793797630948100616437661459113,694718120867647856775927601425227822060490481657127162763696,193638429492015458361529298613552685833291069011347633636046,547395736648530578159489869738783004996235394670624726331021,435919323301993298297319744578846754456350141825925181885482,226387837731001772923887745764028940782314615878915208784648,526892225959746108432921027375818457665174104813155892619618,739613376975056004587369466097066374505292174987535294190075,174242724877443631346704786008706975812879254511499322369298,550108977199658247316252942040325812145332437183949295909116,603879437355471054030397270283500076379081706121231469048185] | [117934121738926873692065353568866130844935750148420380320740,132065315244725143561864863344824593718442141931053681105060,-1059620714914105778303411496858781652272550773743328012291485,436279652229265571952614609243420391042317500254392370341604,-23380516877291774567968056249432247487538155632585328500134,740360976375502442659461185296020557284617256440898031041099,137508221949453916983889254942450257910240320378090644523845,108897788891090789197639592336995511094077294210206602528741,-801787131312754865387061380408296734362869714247993752903052,398025294111567537273217929485704860702431269681881211708790,-2862496567432995210511530617028983930946165355685131095848,22421214365139021771779211333404759477030170093348183549236] | [-2362105578672685267308996962786767177686519126683193084718184,-397511685523109289323410832231159724002328660835453589433409,490490577334336941931109769707914335678301951037345657183109,-2371390939730718893698217800043375477616553920002262794473231,-494333604907834112969205075071768789958921858718986004755353,-2858192221100708645258887016386749885512369893590038264436499,-1789895704756579799501886678417785007855500191121005473464213,-618593077287828215977789146945136651018801730136838655195789,3367865787095651675665277073951917669873650964074663816049032,-2782671907257089344606623475104907152998552579842153884201495,-257077509044831569007150875383286497569092621240578300588536,-172683245613293033098813657268634246394307530674775391514064] | [[-76067501538089831157,572890322767064771169,-409456495465709284127,-31660072404597275356,98585324025657362814,4057913798214567430,-18235978372172759751,15984368373895925289,-10558200939151751323,4044215357777230537,2468271411848183939,-1548180281816791790],[-224759747042995339014,1555036528831092201458,-1106664448878326588756,-51954604690075857513,238959767850367266904,-67545094428696833892,303542889868690063059,-266064220406287402768,175744166804612753737,-67317080109301260784,-41085058451042759661,25769887811311337954],[-1139089903406140355998,-3345978054269364731851,3149595407981091376698,130878681790109861468,-745325444162579357513,134709637202909610566,-605375607445470124094,530629424782898392566,-350498184228147681067,134254893205545439341,81938642105871807531,-51394587085610332663],[437543082914191992062,1718793187521682951624,-1530120108303863305048,-75269887935608158774,364136309941844172089,-44925838944769586746,201893551240295490096,-176965602254901772806,116891599606563511664,-44774181231105710759,-27326643550057774367,17140161535459866439],[-115645186600608366686,1090560869319345316078,-739267107026034275956,-42897365782128207272,161322273298424166380,-23310439842529685260,104755472381212081014,-91821235227933042335,60650945307346227587,-23231749981771304164,-14178835510561673205,8893427785617229078],[488639173521290393309,-683441099683090220990,385056393753717853966,-701737312803391339863,505577724997407877810,-594146799726271201234,243301358745175850994,-28213049618528890411,1305558433933438404122,-1124073995975313637832,1116169195708309252745,-854643545706268992118],[-4088376214633669737,470973258249944556612,-351804674711643485850,-134654364873196833684,172587348591595380316,-83981993140922424674,20408818600617897538,9333501402870978042,183154541196338646187,-161951309302081923390,232760315949501761217,-137852435726737846073],[-183852153540933332876,1511599485349937238150,-1084752067067696296767,-114863985678548040643,286521987029192411778,-124912830892456491119,342581077830654796087,-283600539315105537064,303341789407876610218,-172444170744759726802,232801867192574075831,-69404811064792285359],[222269329380706365776,-3997100099798556396204,2936978774005246445903,794184506039727322936,-1170952309649813473619,-592356383004011463648,-133414582422141304711,645577907588242695447,-1752801453253674254518,1191486252062230565160,-1410437660180052769983,760106029343978239653],[-152839698710615117016,2252178036075113263274,-1647675853114563338687,-396186892863142684845,616546810637274880107,328261563681978808712,22603454698154995270,-274821318571860360891,807851593208554040395,-555030734085412954090,711578731888763289728,-367976660150336083675],[-165906243299175961478,1036628466135580509863,-733553745961288162878,-4757159709152377883,134119233544329429470,77015760494137826983,91808689131943246957,-62321495884430119121,-35391165548897042571,43575268091480581724,39700801690685479998,39415698956321303248],[2750795905722438903,55250001757193672288,-42109890003023934762,-21800232666250540794,25305787023186679492,60887167728790087541,-273622636915945828628,239838243643416940506,-158421046740631061346,60681628803616776091,37035300138583999382,-23229747397507471905]] | 166934136157 | 2792910864857 | 147396195671 |
| 72 | [229652608403909871877339801956517899730115878353009502854671,529372068403569719313740596372474059467686471734561619395034,694763830031519195288846562048687128148034101613508145688580,193619607552641495272569683460955032103517942777321085720402,547396744750629898427589656761674528921797446062594058555913,435887383797560270424035386210249013984741827267838410576536,226381904393081205893329953414737224477444675734840531514888,526887527875898785274271364884318598888800302636039365686107,739647966684950899272460875923083637986386929321816186930286,174225552728301093431567203034342445304990935642296676768278,550109100439540891831186452250875020234341842127251289044497,603878470014093246149122112275242045954056393522909989615183] | [118036013307910058896898139725742628876529897035357263287377,132082461132948407547029402041730436380043260591081824725687,-1059641872140447762420752601394381167867631433423410095749955,436381943727248767455981206923657929735983576595116860239829,-23359193233584412508833677802121892675237140771874716582590,740484229732720160617878471962396170279353448398972529519047,137585437202911497700734002248896946279729099831665666134443,108924468590738656639152663967861645519735364989232635805816,-801932369450735256623197406544968449859571553105682337792008,398145320099387063501339969833622817250554078799632145954749,-2851404285233619744204215087354890777515708443333229877730,22428662716852865488660106093026968304154523105283136106004] | [-2362001608395441411488522312335492275279257871746979964771361,-397441365740358984256016287283705141488191541857460787616133,490444409780116600185079344575067960769011965346535474818532,-2371258581380550236398543009460801020117442612369475261406821,-494317167660403301837434934066535901647517673970195445467910,-2856334499653939467357742162024839227939471424716392799508978,-1790117180475307731043013525875951245543757737452056312394936,-618386231017475447360236814176592298082273549123984626635378,3365964706590835299319597492874777504620044320416462692302312,-2782220667729482380586665193673763497579335792476571539922884,-257205750378136286412348085081714736114333667945005080449199,-172652605911160013533808198040462589181036132819378295210094] | [[-76050488494534720416,572701469695595078025,-409324732213257325056,-31648355896277842015,98552845362440566307,4054013348758100073,-18217120774649351680,15967615692118692703,-10547161367996110548,4040002237035213226,2466116854740538183,-1546869339516597716],[-224703724496580732684,1554511458143618001993,-1106299844176116011704,-51935255363624216215,238879814191104823950,-67546797063474907533,303528393763923952261,-266047791153303305692,175733750047468245235,-67313347975185784717,-41089725265212431139,25773489224461282727],[-1138729231068576025735,-3344763070496373951479,3148475782298890184643,130831749558183730654,-745060401335498495259,134695123293568601719,-605266218362824200356,530526118028967122896,-350430814761525092641,134229602275594564013,81937054772496499712,-51394935951322539713],[437510578365967669521,1718406798075625016458,-1529810420938483481756,-75250790261855770110,364061780575404484662,-44933990022097478200,201915448396389082365,-176982319114993241342,116902931219052586875,-44778693258077805289,-27334017086594910339,17145234977733850872],[-115566491135553347317,1090142416873428220847,-738996572015757076828,-42881759140282174976,161264364183878483682,-23305520432662537996,104725723354593920142,-91793874800035863882,60633023037213843241,-23224974015457945508,-14177096078160576205,8892569386779881733],[488324780902106126509,-682928612207795462133,384756593559617807956,-701336658971868188059,505318905033553037008,-593875099294318278356,243197999919249485827,-28203513143553602597,1305004667826891897238,-1123615700632198128554,1115944035533576323989,-854484355540741073203],[-4084642368456369013,470808997217120128194,-351687509611168859070,-134629602135214516614,172549088826338140880,-83984566894198177122,20426566032550340434,9317983695110001609,183168742115017889495,-161961498341770231654,232798763238172612962,-137883971425133485544],[-183821641136236013521,1511101272112016081535,-1084400894126642478884,-114808290582107609552,286416087605759638519,-124887294621847908954,342544942704570821623,-283572337046141269046,303273597050569104700,-172395804909570167746,232777264823818390278,-69387035769747909060],[222381286687701089670,-3995907616410778624571,2936096278462172611213,793746922305910175246,-1170453794668084499651,-592447857847610495242,-133345950327374342259,645447429090834802859,-1752154187687482864351,1191009644889688095302,-1410195533184480291950,759937374238650866625],[-152888898081007352710,2251681369888872055957,-1647313246550702037594,-396015938061050103275,616350532334049995246,328331702827664711146,22593938091906304336,-274809974172324964432,807655618789264803074,-554877657214347082214,711539979719446674692,-367939378956973545126],[-165848040041425872975,1036229370269908961692,-733279190186463383977,-4766376646892228317,134077774204298488528,77010813275441531012,91788149072351901515,-62307349778625617783,-35362960554044316527,43549207878575891785,39715298505153636700,39403620087883913346],[2748223843418030598,55228205769560246566,-42093501490736170075,-21791337112642835314,25296061529550694550,60878937935410038597,-273565691474964663650,239784973819773494801,-158386252604148313460,60668533694574219591,37033566992868886776,-23229267990315842845]] | 166885623022 | 2793129949261 | 147300206218 |
| 73 | [229647514503691082025562117154128834752611650830896241896923,529366370411541057764512504875607541437996967086949266180339,694809540108003825879347495297484458570834380235370492860470,193600781200856951463184123509732945965338409115181033884266,547397751932909543356976563721940192868703113478114601330855,435855438978092786968452958953397072095370244225487701992147,226375967724131301297037691741605339107702276059117835836596,526882828641365490546224657259117329906044515761781394041381,739682562658194251375661726015733238946617619335735023198168,174208375402034435051038307115614733788586039884071220071985,550109223200818063687651574066135921465375043989965592787753,603877502351445464460943467073611396288432974071100038427191] | [118137900390366175026010633695921968268655717017053629483632,132099603987375859993721533161149804156233601080129644860829,-1059663027374795786515462890912574483927549317389190693530111,436484229514183634415550122928120757325006892736860368128984,-23337870299383830601212847817347895167932576802764480595664,740607402980861142889602213130435542564892626172298407356046,137662662003920181543138675560569927015604218006521162654336,108951139369393513293553757147601880440008819731829285530898,-802077525608782402977698886234364926235195306095368086921621,398265326625368202522384837764751466223523873724608539070724,-2840306473632932995553709402405947084741816567276173404648,22436109746592028660667328581722190438028701060990468931556] | [-2361897565047424862024771105556578415235106722314459525400565,-397371026421733165501260560095056661002047497555195648075766,490398220400194929932411582960904489482221678541121246915573,-2371126152324250653076965824693782817175866072143134228463018,-494300709290742622822006015848681063604129814726437872244246,-2854478038649801731636895238013181264983387376313283594076899,-1790338368045251427067111411846824574793180389800584258030249,-618179463791719024558017397860996293025358756366917435412648,3364064864134808788870795315070627346689795452083129129017675,-2781769577324826230037454321053381684555647737883214435117311,-257333874568491701336146486923775546983694878974526371810753,-172621953495400629900970606317189752820110077401625631470743] | [[-76033487828542675217,572512750990223128958,-409193063392661087282,-31636647607224476473,98520389834326296902,4050113269152216338,-18198267412761078745,15950867142328476481,-10536124479253899134,4035790116498190112,2463962037617351591,-1545558181743434083],[-224647744999379886969,1553986781158730373336,-1105935514976920659214,-51915920507091518777,238799920794345313156,-67548499931865101802,303513897859026731331,-266031361711101335867,175723333243462498957,-67309615878067488875,-41094391309444297318,25777090613577655333],[-1138368850817003895679,-3343549020017457646877,3147357023320521790349,130784853486696367939,-744795563635080630588,134680613607668581417,-605156858306864970293,530422837964944640808,-350363462849453875503,134204318042570878715,81935466264569394969,-51395284637836892250],[437478108471769646997,1718020688112128498020,-1529500963480096322056,-75231706477625907857,363987306422875884047,-44942139220360138000,201937331941546085189,-176999023028817991128,116914254422516728805,-44783202154191007938,-27341389627717953199,17150308241038365384],[-115487862692377100321,1089724285230722037684,-738726244253518191240,-42866164056282440163,161206499101549771736,-23300603574268142556,104695989110454632690,-91766527810471171107,60615109599546082309,-23218201409255347510,-14175357291324722460,8891711441272525039],[488010677219615351842,-682416686842809487002,384457135313268561941,-700936345490284540984,505060286550667178977,-593603531401301660414,243094675579560207799,-28193967138092789631,1304451160852474589133,-1123157621972212612354,1115718955860738912759,-854325215723642578537],[-4080916760986534729,470644858131615502023,-351570430885776703888,-134604851129099996702,172510853307981409221,-83987129051101973842,20444303580265574512,9302471734580495748,183182916861873256781,-161971667383939548668,232837200856063324285,-137915500181174903970],[-183791149403181897972,1510603424306399029503,-1084049981360534579643,-114752639755040648876,286310268638658617079,-124861771288383603240,342508819012220576415,-283544141351195122115,303205431312108186442,-172347459049835662784,232752666480995682341,-69369263079397529421],[222493112876906703937,-3994715883325594358963,2935214356339005336490,793309705878985024861,-1169955665134934133073,-592539255800558410074,-133277342297357664014,645316972772635059449,-1751507205074122263655,1190533257937618331483,-1409953480558933551215,759768766296980509128],[-152938059887898494061,2251185056664772290188,-1646950905308472095646,-395845118024625217629,616154404981592156573,328401819172939537970,22584422151156150641,-274798625523688326636,807459711552991882579,-554724635657543193825,711501242040558605889,-367902104899486805665],[-165789884737001486946,1035830587532170388425,-733004850395609524347,-4775583403205294017,134036345491335861554,77005868949924184777,91767616630865208150,-62293210048673680311,-35334770956785363939,43523161703440949274,39729788466081814218,39391545409914722915],[2745655030836794099,55206417271713201221,-42077118989529146305,-21782447883190959019,25286341948805196293,60870710599094907098,-273508762711467452118,239731719362142511219,-158351468562001826306,60655442427038971137,37031833470266620732,-23228788565377800703]] | 166837150449 | 2793349809790 | 147204268040 |
| 74 | [229642416208480582936691393448841366967334038547429223660475,529360671680088980988306504277282825899342772554536879585232,694855251097015799883277329025768531621680091584571615000951,193581950436908249390300962767110172699478808790563412101284,547398758195400138491444836888511569512651768677474277204061,435823488847045329236967930076070121538287272665880195314166,226370027723740475839209899524560966643360753514613622248277,526878128256530974322291114454905096898104726493996913568311,739717164891250855886223130104791827075463551354196665385701,174191192899483040037748783683108872976784403216337151574935,550109345483251350863258008019319224765852862441107002097172,603876534367584746626788150166277906918149677572509403820168] | [118239782983143405968003710137785521439401488809438520531690,132116743807164915919790334097880015648165116701999022171829,-1059684180616208461567128279571678342103530362023813167352595,436586509587020427385134255909339829464762538459480661513135,-23316548075601112055641084577881345317792761837532534452509,740730496174282594155756812851740512018029181443976283461576,137739896340052819061815866934374121829228610335006036637437,108977801230464123513575211585478305979335978377432805439165,-802222599840287575330958361711522287661015619762588743884982,398385313695941486309557908789906560566587877572054797792122,-2829203137682974491885199641370643893289987483150989838804,22443555453808145393486835136323336883124351117722179596799] | [-2361793448639179446842915921137820443772801491743877588021303,-397300667573319478703205500641583403665489648017433118498707,490352009199354489688770648808998080429035771233514732476862,-2370993652575491181074633075311006429397466199782230701063732,-494284229801792201967883682423508259604731625036743205137997,-2852622837423890502046556064834918585454721669767879299545907,-1790559267590839808753284318358074315020547436967416276954796,-617972775565530457968857398103028896721696569687459494198651,3362166259066234404636919250305748307605644419502604703291776,-2781318635942806892616252248501273115045355492927468469500843,-257461881668718056664835919518699365310185123355126131870386,-172591288368796590389217961363250677744289324150106516669338] | [[-76016499525059046466,572324166496294393429,-409061488895236556735,-31624947528101630799,98487957414750412177,4046213559543650177,-18179418286975773100,15934122724937145391,-10525090273190195967,4031578996262473422,2461806960760265422,-1544246808616412430],[-224591808501184192053,1553462497427167855827,-1105571460966688510624,-51896600104072898425,238720087591455052767,-67550203034707572545,303499402161212446333,-266014932086493210435,175712916397030236739,-67305883819614224615,-41099056583253567677,25780691978478486718],[-1138008762320015023306,-3342335901769718486148,3146239130059344946819,130737993534476109072,-744530930827803212742,134666108145774514852,-605047527283078866106,530319584596132926968,-350296128495335263301,134179040507725424132,81933876581925371936,-51395633145067939587],[437445673194557669433,1717634857310281817977,-1529191735665576369465,-75212636567125667640,363912887421128122041,-44950286540689570730,201959201885225502434,-177015714005273385311,116925569222768099666,-44787707921640866339,-27348761172783638068,17155381325122641895],[-115409301194352653936,1089306474025972622623,-738456123503385736883,-42850580516997969076,161148678001305592221,-23295689266698752402,104666269644574314265,-91739194255343284444,60597204991781454963,-23211432162189769511,-14173619149982612510,8890853949062565335],[487696862133796962942,-681905322830101666569,384158018543055952379,-700536371980731539675,504801869343405419004,-593332096013722438340,242991385739305961449,-28184411625105088645,1303897912954065434039,-1122699759943726123075,1115493956696971775879,-854166126260132766225],[-4077199381215030423,470480840846829677691,-351453438431563950635,-134580111840128918043,172472642006556004821,-83989679620467761193,20462031246902615995,9286965521007637501,183197065453578694324,-161981816441874047208,232875628804026262875,-137947021993731946228],[-183760678317540297963,1510105941522633856903,-1083699328477467727136,-114697033147867047465,286204530037861590604,-124836260889536963189,342472706756337682114,-283515952233780935358,303137292189634741277,-172299133162266318013,232728072164701756970,-69351492994438816306],[222604808106542683415,-3993524899805526300303,2934333007065534938027,792872856350544173978,-1169457920635688394465,-592630576902683612181,-133208758345249421094,645186538662729378514,-1750860505362455755312,1190057091155741951042,-1409711502310630729547,759600205524394955116],[-152987184171517502535,2250689096003733183943,-1646588829088982773193,-395674432602271689795,615958428410274751005,328471912720548840408,22574906883267954805,-274787272635285476071,807263871497968461876,-554571669410739519780,711462518852839230700,-367864837979410782541],[-165731777330189925900,1035432117559264371912,-732730726338388672780,-4784779988954164189,133994947369053552794,77000927514443838625,91747091808295742993,-62279076693954306866,-35306596751619064304,43497129561399918020,39744271573271463050,39379474922894446740],[2743089464884604556,55184636253894273854,-42060742491543051514,-21773564970721591333,25276628274039155966,60862485720176429862,-273451850627717966550,239678480272653474648,-158316694615559030608,60642355001514586622,37030099570918661600,-23228309122775185519]] | 166788718403 | 2793570446594 | 147108381158 |
| 75 | [229637313518472113219514188711701171323352712310174076262536,529354972209344411917002562178607839523547574719611127295337,694900962998469128032369689543960612051258800159957858149476,193563115261041943054560398797937388996227253356194494703369,547399763538132348673318840245414576580342360228816036666193,435791533407870034355237748404523396982980306111516332955320,226364084391497682176431632657582152964088707191722072207529,526873426721779839674500418090907961923774993754935718172262,739751773380587810309640087338823246123030704563532759857622,174174005221486014924733417434727278972118034278225824804225,550109467286602559215571780780469007934920825011434043543543,603875566062568153959775723373784173595158743178393083575965] | [118341661083090390637946832523894606259824905312435788264502,132133880591473253001904862867607754461597704581508676556622,-1059705331863744604918269255239471459587045975539507435714178,436688783942709990832182542472438979593188710276011671642859,-23295226563147213198044995660014095393381268808033850807046,740853509367313052973210184534508972688400778133390486698632,137817140198887629528409093208697302303139049881712615295256,109004454177357308808169361128583232416502646212252848302333,-802367592198613510793972002597471845200455921210895975741897,398505281317533118742932849670125087755031382793255828880309,-2818094282433504703726198964190378153551775877502550613657,22450999837952969820429034777768081969811119194039800936033] | [-2361689259181258213684462388375525067599218979236284877459647,-397230289201208208241903865839085009004106055057077891031626,490305776182380544958261993933246712875865782637326535134391,-2370861082147951575822231381911136498786048911468839502452983,-494267729196494799171175139889463481216259101704765056163570,-2850768895311533026868446457816706206340385837949058034707708,-1790779879236559617421443548979732776990469545337358518734068,-617766166293860129947574137889830926511186188381592619136995,3360268890723508707520776461289661620998850024981655248973624,-2780867843483070438662432617639566650996403304396596271173544,-257589771731661418177175980536366586669888227444555395760950,-172560610534131155123073909326347324172464801234298759841557] | [[-75999523569051908822,572135716059388345613,-408930008612464068742,-31613255649587913194,98455548077188966461,4042314220078779087,-18160573397758421753,15917382440353881582,-10514058750068329368,4027368876423717715,2459651624450985200,-1542935220254681154],[-224535914951861076483,1552938606500348875872,-1105207681831842716556,-51877294138188307985,238640314513904205561,-67551906372840618628,303484906677682437378,-265998502286278876182,175702499512598445435,-67302151801490903518,-41103721086155487794,25784293318981812426],[-1137648965246701915255,-3341123714691866620199,3145122101530210522378,130691169660413549438,-744266502680496842167,134651606908446940039,-604938225296921410605,530216357927805219914,-350228811702551651669,134153769672302107052,81932285724399343328,-51395981472930225940],[437413272497347228964,1717249305349658935184,-1528882737232195984005,-75193580514586038835,363838523507126399512,-44958431984216702698,201981058236879305307,-177032392053250331293,116936875625614598013,-44792210562621296245,-27356131721148746196,17160454229735909821],[-115330806564868815535,1088888982894478339685,-738186209529784779152,-42835008509317619876,161090900833089375517,-23290777509306013068,104636564952728924687,-91711874130752672765,60579309211355953058,-23204666273286521003,-14171881654062646865,8889996910117368750],[487383335305126778479,-681394519412855427752,383859242778130718122,-700136738065832147673,504543653206692879385,-593060793098005756229,242888130411622448681,-28174846627514316163,1303344924075380368201,-1122242114494981981012,1115269038049385126234,-854007087155327472485],[-4073490218145350925,470316945216385031302,-351336532144786646967,-134555384253606070091,172434454892143838808,-83992218611129499659,20479749035604429306,9271465054112965437,183211187906811115817,-161991945528859886798,232914047082924504482,-137978536861682272563],[-183730227855118885711,1509608823350886294948,-1083348935185976096011,-114641470711178414418,286098871713474067467,-124810763422773292465,342436605939641078230,-283487769697400922514,303069179680269418772,-172250827243558857930,232703481875527399612,-69333725515565947471],[222716372534606845488,-3992334665114144868260,2933452230072362315220,792436373312757956517,-1168960560756259918854,-592721821193840050101,-133140198484153064747,645056126790135266455,-1750214088501158260986,1189581144493649259502,-1409469598446725629954,759431691926278735577],[-153036270972036079933,2250193487507276048873,-1646227017593793342573,-395503881642615715191,615762602450722014281,328541983473256187282,22565392295589169313,-274775915516437194529,807068098622369859896,-554418758469631958796,711423810157018060916,-367827578198272579613],[-165673717765361083143,1035033959988643063191,-732456817764844254130,-4793966414988192528,133953579801121596104,76995988965858679555,91726574605450423674,-62264949713843952060,-35278437933036974327,43471111447770256963,39758747826529161477,39367408627300234115],[2740527142472054817,55162862706359945981,-42044371988929869433,-21764688368072277943,25266920498351994063,60854263298984263431,-273394955225965205537,239625256553422096038,-158281930766178337397,60629271418501210843,37028365294966493809,-23227829662589856026]] | 166740326846 | 2793791859823 | 147012545593 |
| 76 | [229632206433859547412809023872003718231070995742876672548674,529349271999438309811951296795588233462556270447656228236773,694946675812277780463149268205251801096455533973098053116935,193544275673504717974859352361449280474687355659102179365338,547400767961136878037977201995529429361331060045231562945410,435759572664016696504996925385738100569410204969140800564230,226358137726992408686030626054858157509957486884605862914390,526868724037496542757229506059273732005472611785581947662081,739786388122674513436547742542877240493135487300092725368852,174156812368882189132168474153717970978106218879753693054669,550109588610633712383779920211891650796762905390457565258174,603874597436452771420039436652492369865573260375455611745528] | [118443534687056223375023621197242213129298344652242574167736,132151014339458811689348807972480644035846286993680593336049,-1059726481116463240391081685902202259359854243322862454395061,436791052578203759513766482316148753595287247506066929655993,-23273905762932963356146218281256041492040844461517996181868,740976442614252380263812321042272335235547495949296562776670,137894393568008203422306155329297549589161987277015902797915,109031098213477946934423006021796698712425702106707096546588,-802512502737094401288843091245264836418087604074503629495475,398625229496564973894247116492284856556585399323551238236298,-2806979912932003934247191620440281735197776115551438953825,22458442898478376169359186185789350692140141520762201672752] | [-2361584996684223426938617153475631468429884876256589805132482,-397159891311492275743695327275572821954588026296930927203026,490259521354061066834611894451952336056435763442680345905316,-2370728441055320306923719472553787167650955050303325195883789,-494251207477795807251674582308332732721238495246797456524909,-2848916211647790683601585010074162114974398107175437330992144,-1791000203106955073157602046247015141948407666446829923281696,-617559635931637448295499035972164456252114386079435986417210,3358372758444764502801495218961581659399883082937972374857256,-2780417199845223343847748514082697553711338101453589153915907,-257717544810193518865119974714875561874543005365654178021898,-172529919994189135456579689707390590907091386513389968630496] | [[-75982559945512017825,571947399525318022004,-408798622435987997276,-31601571962376061218,98423161795158134825,4038415250903624892,-18141732745571172057,15900646288985185686,-10503029910149880435,4023159757076921144,2457496028971280656,-1541623416777425488],[-224480064301353863493,1552415107930370460547,-1104844177259280700521,-51858002593082472936,238560601493266582492,-67553609947100684135,303470411415625353491,-265982072317246523316,175692082594586385966,-67298419825359500820,-41108384817665339432,25787894634905672628],[-1137289459266657579098,-3339912457724216643390,3144005936749458679372,130644381823461426335,-744002278960344602768,134637109896241975282,-604828952353817268727,530113157965206063899,-350161512474466629620,134128505537537712266,81930693691826255991,-51396329621338290452],[437380906343209459414,1716864031910318427635,-1528573967917624589935,-75174538304261859367,363764214617931185885,-44966575552071382145,202002901005952433424,-177049057181633281681,116948173636859859385,-44796710079324581780,-27363501272170105069,17165526954627396111],[-115252378727429952861,1088471811472089016244,-737916502097496656220,-42819448020150105026,161033167546920277240,-23285868301440963956,104606875030690300516,-91684567432795965045,60561422255703057764,-23197903741569964520,-14170144803493126039,8889140324404261211],[487070096394576650473,-680884275835465974757,383560807548407057442,-699737443368740210702,504285637935724227578,-592789622620501029992,242784909609583243371,-28165272168209507706,1302792194159972751971,-1121784685574098146191,1115044199925024746168,-853848098414299187265],[-4069789260793607360,470153171094126901933,-351219711921859661506,-134530668354865321214,172396291934877809592,-83994746031921147043,20497456949517913098,9255970333614387507,183225284238250365079,-162002054658185184672,232952455693631813135,-138010044783911345199],[-183699797991763617592,1509112069381938860239,-1082998801195032076216,-114585952395637948613,285993293575734572981,-124785278885549829956,342400516564835047176,-283459593745545689594,303001093781112679078,-172202541290396658901,232678895614058385144,-69315960643469614571],[222827806318875721214,-3991145178516066203317,2932572024790897414510,792000256358373710420,-1168463585083146895208,-592812988713907086027,-133071662727117446260,644925737183801918358,-1749567954438716805307,1189105417900800551180,-1409227768974307790172,759263225507973200160],[-153085320329568768280,2249698230777523143283,-1645865470524912232726,-395333464994505613258,615566926933808564353,328612031433843121177,22555878395451301460,-274764554176450032556,806872392924313654640,-554265902829874172038,711385115953813992157,-367790325557591500636],[-165615705986967470188,1034636114458310140317,-732183124425400309392,-4803142692143517076,133912242751267941530,76991053301027037839,91706065023130517617,-62250829107715531971,-35250294495523353782,43445107357862742727,39773217225666606573,39355346523605674871],[2737968060514446443,55141096619381415239,-42028007473853357193,-21755818068091410255,25257218614853560585,60846043335845987765,-273338076508443419334,239572048206550336168,-158247177015209153601,60616191678495583415,37026630642551625842,-23227350184903689645]] | 166691975743 | 2794014049628 | 146916761364 |
| 77 | [229627094954836895965692243776587093333967568465394452355664,529343571050501670252636338971676127880672370964841845206304,694992389538355686725841222521911562661052272645434573652314,193525431674543391162880121815381300897540940398286010565091,547401771464444470008372061750464717207461547768803863582550,435727606618932768161366846152652825298452947320647443961106,226352187729814679234326899608200733901108775544244123091559,526864020204065392891069386397235546485357336399045307619188,739821009113982664111126852336627466698873833077484510408458,174139614342510115154182759952262947295795371134979755926575,550109709455107051690307369112996746498979260532986731883221,603873628489295707609544283387616669202713240902829071626731] | [118545403791890454340040680893826960068989585526797846356773,132168145050279795317750861309519031655937378945954233009969,-1059747628373423598404117268836244351626537268325859251571654,436893315490453758852397675318283163518024296644417726567366,-23252585675869064745905382904910212654335880512991657083955,741099295969371747887429946311547878255470935738327459774750,137971656435003504902743971755826461194842372573498876471778,109057733342228970996085033285765757529017901189403759626422,-802657331509035882213034378307168222534511451143477735474929,398745158239454594326115797695712648406983173655620326870984,-2795860034223671215409915741477039077876846211781695618952,22465884634836358829597327476250809579057785882746682885259] | [-2361480661158646564471073390022954057158117368973267510497485,-397089473910267238590769644875000554450153657189874903453804,490213244719186730601581237262848130910335853710512997576559,-2370595729311294554237623234626390908488938696074660308376193,-494234664648643251024677300174954470001424128579348916391876,-2847064785767460919204576917154945529119827120117926391471698,-1791220239326627534241337826276264836797214152474213684903180,-617353184433770999383569942688459434590279482302184211087973,3356477861567872779282129362843589599565504340218716318278231,-2779966704928832823019339190229849025196152356798219867898267,-257845200957211603619604327841369810991830991420130794423340,-172499216751756893266800090369287673544636730786950802356944] | [[-75965608639452767123,571759216740129580024,-408667330257616444911,-31589896457172915064,98390798542214137246,4034516652163854521,-18122896330873337185,15883914271234881905,-10492003753694686383,4018951638316426728,2455340174602985673,-1540311398303867485],[-224424256499681627672,1551892001270006955119,-1104480946936373262548,-51838725452424844582,238480948461219446788,-67555313758322360559,303455916382217167464,-265965642186172599238,175681665647405602360,-67294687892879058848,-41113047777298440638,25791495926068112155],[-1136930244049974577255,-3338702129808684561077,3142890634734916059266,130597629982634501515,-743738259434881395676,134622617109711326648,-604719708459160299004,530009984713551356683,-350094230814425010905,134103248104661914457,81929100484041090970,-51396677590206667206],[437348574695271031035,1716479036672802576492,-1528265427459927925178,-75155509920431770612,363689960690698039050,-44974717245382379465,202024730201882795892,-177065709399300235256,116959463262303256954,-44801206473941375687,-27370869825204588520,17170599499546325283],[-115174017605655775753,1088054959395204900766,-737647000971658305655,-42803899036423953756,160975478092893035119,-23280961642454040135,104577199874226167564,-91657274157565961987,60543544122253747194,-23191144566063518524,-14168408598202250578,8888284191890528455],[486757145063613574549,-680374591343538015410,383262712384561188209,-699338487513139518408,504027823325963215371,-592518584547482165629,242681723346199905819,-28155688270044957382,1302239723151233811174,-1121327473129067571035,1114819442330872100735,-853689160042077129761],[-4066096498188512173,469989518334123179029,-351102977659356388126,-134505964129269552418,172358153104941698742,-83997261891676641693,20515154991793886327,9240481359226188903,183239354464579178851,-162012143843139986803,232990854637032621382,-138041545759312414949],[-183669388703358657979,1508615679207189686459,-1082648926214045443628,-114530478151980308527,285887795535014401658,-124759807275315770515,342364438634609239285,-283431424381694252487,302933034489244839704,-172154275299449782583,232654313380875486797,-69298198378837029167],[222939109616904925677,-3989956439276950173525,2931692390653357696916,791564505080714752211,-1167966993203432008309,-592904079502789365223,-133003151087136916733,644795369872610313490,-1748922103123430999284,1188629911326526469198,-1408986013900402596008,759094806274776592722],[-153134332284173049506,2249203325417196527748,-1645504187584796175750,-395163182507011418867,615371401690658935834,328682056605109114672,22546365190169936264,-274753188624616324966,806676754401859806114,-554113102487077677571,711346436243935323283,-367753080058879062532],[-165557741939544064490,1034238580606819768543,-731909646070860777412,-4812308831243080055,133870936183278342160,76986120516807393633,91685563062131650323,-62236714874938431147,-35222166433555191326,43419117286981492142,39787679770500605229,39343288612280805407],[2735412215931780745,55119337983244567648,-42011648938489023101,-21746954063638204887,25247522616664115319,60837825831087109935,-273281214477372135424,239518855234126429393,-158212433363991897624,60603115781991044675,37024895613815590209,-23226870689798582468]] | 166643665057 | 2794237016161 | 146821028492 |
| 78 | [229621979081598305217946733718849877730878143608913048218833,529337869362665525125331789606376747947236258734800781901953,695038104176616735793285609207073732318316689026540290020348,193506583264404911097602829579326715495766376374681581188839,547402774048085907289543420133703115410068474941523155365399,435695635276063361330656700210798733049788727801371151988253,226346234399555052944776041929344295030930018787057312302248,526859315221870552646730695493282420494693049539556579014683,739855636350986259999022065457548782629075661135386299333873,174122411143208068745741736729219159806238492774583202579744,550109829819785036042386426661527852687742565598746742811432,603872659221154094766902170490977232586500784404100260254019] | [118647268394443089912799576370900749550504139275538583193261,132185272723094670222750782525290411786300170023230904174366,-1059768773633685116088903589526257901267276535868326738860066,436995572676412605311676265474670477846746394506723112552488,-23231266302866092358006131625036141497661436858124687576688,741222069486913627298577099229420254433621242743004674626336,138048928787467874266239461966112522583086511723145491955052,109084359567011368548691395104105603995405656226430366608574,-802802078567715021187169139297787420921871112466873721836284,398865067552615189405629006483168736704056565187742691273615,-2784734651351423210807549369965685070064479819643962134842,22473325046479032418787721315607029201429673067781778405590] | [-2361376252615108314450215633280597750822667129356441487278564,-397019037003631288429997728947276030247218410364309357098473,490166946282550914332614294031387683797135294504991079161488,-2370462946929580203955895585230104547587317602822210376280600,-494218100711987786372063266295890196194427816733504577330184,-2845214617005079185701665352106536004711951506544979708129467,-1791439988020235157374173027172080160053469904135231668689839,-617146811755148700909660772064889890266891643119389876275095,3354584199430444643800561831606549919717939652462936976778550,-2779516358633427163236733321862426572628252373795718802572815,-257972740225638274280836417309164084922120400204273289747694,-172468500809622340246924701539021170391683124501530071075201] | [[-75948669635910145790,571571167550101857637,-408536131969320933480,-31578229124699390905,98358458291953162934,4030618424004780792,-18104064154121401602,15867186387504123090,-10480980280960843879,4014744520235923618,2453184061627998228,-1538999164953265995],[-224368491496939051938,1551369286072708743477,-1104117990550963684857,-51819462699909553313,238401355349543318490,-67557017807338389001,303441421584621190701,-265949211899821822302,175671248675459930791,-67290956005705690446,-41117709964570145826,25795097192287180530],[-1136571319267244083057,-3337492729888784764027,3141776194505892974122,130550914097009443993,-743474443871993274524,134608128549402295418,-604610493618313604967,529906838178028397269,-350026966725752865329,134077997374897290079,81927506100878863565,-51397025379449885247],[437316277516714045477,1716094319318136452199,-1527957115597567292463,-75136495347398172401,363615761662677425660,-44982857065277387418,202046545834101272399,-177082348715122737949,116970744507739902177,-44805699748660699587,-27378237379609116837,17175671864241919455],[-115095723123281118367,1087638426300775622912,-737377705917761592552,-42788361545087474614,160917832421177826178,-23276057531695074135,104547539479100153375,-91629994301151647649,60525674808436504016,-23184388745789660283,-14166673038118121091,8887428512543416041],[486444480974198802136,-679865465183883492484,382964956818029911232,-698939870123242868156,503770209173142219058,-592247678845147777135,242578571634422097077,-28146094955840257469,1301687510992393077736,-1120870477107758552445,1114594765273844450820,-853530272043647323859],[-4062411919371364178,469825986790663890687,-350986329254008450901,-134481271562210591231,172320038372570067099,-83999766199229885780,20532843165587074333,9224998130659039896,183253398602483149679,-162022213097016239008,233029243914022010547,-138073039786786507863],[-183638999965826303265,1508119652418651358732,-1082299309952862532578,-114475047931011482346,285782377501817370041,-124734348589512285674,342328372151638697804,-283403261609314054543,302865001801726122219,-172106029267375009285,232629735176554485075,-69280438722351928723],[223050282586029527578,-3988768446663498385961,2930813327092766609149,791129119073679353810,-1167470784704781382991,-592995093600416685715,-132934663577151426744,644665024885373310718,-1748276534503413522934,1188154624720028364878,-1408744333231971394562,758926434231944126782],[-153183306875849444913,2248708771029616923336,-1645143168476349355425,-394993034029424474641,615176026552647115489,328752058989871526642,22536852687044759368,-274741818870214206359,806481183053010779081,-553960357436811944662,711307771028079775761,-367715841703639008647],[-165499825567708157530,1033841358073275562843,-731636382452408778220,-4821464843096647653,133829660060996241224,76981190610058383568,91665068723243813641,-62222607014878509603,-35194053741602230260,43393141230423984724,39802135460853065191,39331234893792114703],[2732859605648749843,55097586788249949937,-41995296375024104462,-21738096347582683211,25237832496914308179,60829610785031067811,-273224369134956184044,239465677638224907355,-158177699813858014905,60590043729477541582,37023160208899943420,-23226391177356449255]] | 166595394752 | 2794460759573 | 146725346997 |
| 79 | [229616858814338057380333497543255214871380939031246193819853,529332166936060942611754775274662783172208437713451799298162,695083819726974776069856846536242729457802622700844564369460,193487730443336357699801667953745888226702294340587234739250,547403775712092011863128592525535591795088281809092941854266,435663658638851248788651929991820105620044994164456316432520,226340277735804623966006804120438823952157846738256408291725,526854609091296037928987716378173286701037645947558270407725,739890269830161596354776617005813848161546457112700393407094,174105202771814049109604074130406536966028416056319874325083,550109949704430341833579005879906470809738209991092156765580,603871689632085088762184204618864729353604786091787194428640] | [118749128491564593089331844857037155620001320567099094503497,132202397357062165853601123251440323313150698428283715789200,-1059789916896307437406503757345535041037399166043369561626428,437097824133033506771770186690411351896441022355820065914561,-23209947644834493844379222833183562616988678024823552542348,741344763221091778286441813482226650533941296564603110082057,138126210613001030389381002012112750473996057694509764116698,109110976891224180711271679618936307367804461186269320920851,-802946743966380306886181075930665973929083039322731552896938,398984957442455633632298081263896088232423963984474178135641,-2773603769355893125181088637727499257325556532602809711044,22480764132858631849737797922952122146122670804487953509382] | [-2361271771064198572170745719211237108828169580578206981151904,-396948580597685249681031313402110015476456429577298676322679,490120626048949697489723220525544079988417312968014536823720,-2370330093923891844680343244304727153713221403378162024387255,-494201515670782699312650712231385052603505101326370725110857,-2843365704694920871159798444438803835328589115492373530783089,-1791659449312492558707615485308827952527854719786004150815902,-616940517850637954290716482833819666454356625284350794526155,3352691771369833251110962073939466376441527385427419025385386,-2779066160858496056004105388102015675082337213330480452161862,-258100162668421335052513951114253891845397220248550110298150,-172437772170574937198964839438010269946483946238948300625796] | [[-75931742919942695745,571383251801745933956,-408405027463236095434,-31566569955690454294,98326141018011294845,4026720566571363187,-18085236215769026532,15850462638191395814,-10469959492204712374,4010538402928448359,2451027690328280333,-1537686716844916652],[-224312769243296284849,1550846961892600971454,-1103755307791366839549,-51800214319255361985,238321822090121779430,-67558722094979662355,303426927029988088057,-265932781464947195569,175660831683145508612,-67287224165492582403,-41122371378995845873,25798698433380931997],[-1136212684589554938948,-3336284256909627009694,3140662615083180604448,130504234125724713117,-743210832039916782239,134593644215857785534,-604501307836609586493,529803718363795933590,-349959720211757550043,134052753349459329215,81925910542174623393,-51397372988982468594],[437284014770775931001,1715709879527827002659,-1527649032069398812147,-75117494569487178125,363541617471214541854,-44990995012883021354,202068347912031714317,-177098975137965883833,116982017378960645460,-44810189905669944229,-27385603934740656879,17180744048463398385],[-115017495204155721892,1087222211826299155989,-737108616701652639197,-42772835533108718098,160860230482020124259,-23271155968513297736,104517893841071799700,-91602727859638201041,60507814311677323052,-23177636279769928751,-14164938123168738279,8886573286330129355],[486132103788786954605,-679356896604519319984,382667540381009176743,-698541590823791130876,503512795273261780633,-591976905479621404028,242475454487137693127,-28136492248380337969,1301135557626518829583,-1120413697457915083281,1114370168760794966129,-853371434423952673476],[-4058735513396033625,469662576318260792856,-350869766602705409697,-134456590639109145751,172281947708048151141,-84002258963414728614,20550521474056094956,9209520647620003669,183267416668650688883,-162032262433107758108,233067623525505691026,-138104526865242411869],[-183608631755126906069,1507623988608949750631,-1081949952121765410251,-114419661683608658363,285677039386779570082,-124708902825572544312,342292317118583883852,-283375105431860984146,302796995715596698887,-172057803190815871287,232605161001666176651,-69262681674694582592],[223161325383364418066,-3987581199943452202859,2929934833542952058306,790694097931739721587,-1166974959175443530733,-593086031046743868260,-132866200210046625884,644534702250835743858,-1747631248526590607131,1187679558030378656547,-1408502726975911607306,758758109384688060881],[-153232244144541614423,2248214567218702572470,-1644782412902922557670,-394823019411257024187,614980801351396078772,328822038590965558624,22527340893359579913,-274730444922507626624,806285678875711665644,-553807667674604487960,711269120306934513033,-367678610493367321991],[-165441956816159203239,1033444446497329552775,-731363333321605897975,-4830610738500829773,133788414348322659455,76976263577638807320,91644582007251374044,-62208505526898109806,-35165956414126994254,43367179183481085120,39816584296550986105,39319185368602550337],[2730310226594727745,55075843024712741936,-41978949775657545459,-21729244912805650938,25228148248745159583,60821398197999233741,-273167540483385723694,239412515420906622672,-158142976366129993455,60576975521441633609,37021424427946265958,-23225911647659223419]] | 166547164791 | 2794685280016 | 146629716899 |
| 80 | [229611734153250570514886103235880968716224374504032299892394,529326463770819027177713104813307261819578879499992778275442,695129536189343615400388203421340539503015750820706661531714,193468873211584942306524951595567251905592848158536008855730,547404776456493644981866768679659360454557776935531587748716,435631676710736865319386604132922995642066937875764827080392,226334317738155021239753634328036526486631688732163446085635,526849901812725718060660573531181096482059980952010430125283,739924909547987264788787027713168792293977999010447855206005,174087989229165779083350019797301267842503544645603374948959,550110069108805862845251994778212989532542569092976966346258,603870719722145869091730095826156732402422865249169304162422] | [118850984080105883878996934117016134142591329686037476879245,132219518951341274886704579686858847154912938370443845631752,-1059811058160350413264015585046043071781615967663779097206480,437200069857270262904725105512268789958485127388401162491748,-23188629702684589404766753646135189117150989211111260622208,741467377226091237798109369949959284474092072543984310468488,138203501899208073157014920036374025486339726058948926891735,109137585318264501284621533033923934337144735419554521130973,-803091327758251637953613518901993911514942844402748539382239,399104827915380464980315906972676929047089063759967499218612,-2762467393275429620596231451798040943626215569582587499127,22488201893427512397226578526112577495955550373824966677592] | [-2361167216516516436874731610340041758092624212562418667239599,-396878104698532578043671963225911096027750823631061705911157,490074284023181859521609019490703312887090303824232083485369,-2370197170307952763496622495847702399160415325740963400071628,-494184909527983905071820208799394385602070959178779939360490,-2841518048171003226043963423718239391066190950269069060612019,-1791878623328170475669610177569366553122655243938691808727234,-616734302675085796690261277346717038941514246341148992560850,3350800576723135729143049657280725558980029639280332705813721,-2778616111503490928699041342682033629608669162965430271816865,-258227468338533638279409211388777634649345005300352578337443,-172407030837405693326046510355981284863195162883254162382464] | [[-75914828476631469268,571195469341804690847,-408274016631659365898,-31554918940895093630,98293846694064434350,4022823080008208632,-18066412516267055409,15833743023692525446,-10458941387680917425,4006333286486386152,2448871060985857977,-1536374054098151848],[-224257089688998798233,1550325028284482273052,-1103392898346368298330,-51780980294205619404,238242348614941278658,-67560426622075227508,303412432725455892666,-265916350888290020555,175650414674850783380,-67283492373889998884,-41127032020090968211,25802299649167425553],[-1135854339688492716819,-3335076709817913410330,3139549895489048203390,130457590027980441909,-742947423707238289321,134579164109616311042,-604392151119349991097,529700625275984210135,-349892491275727740790,134027516029556447428,81924313807763454444,-51397720418718936261],[437251786420749337931,1715325716983862143480,-1527341176614672676747,-75098507571048569943,363467528053749134378,-44999131089324819429,202090136445090945821,-177115588676688316117,116993281881752076826,-44814676947154869755,-27392969489956222178,17185816051959979500],[-114939333772244017757,1086806315609820781770,-736839733089531156247,-42757320987475439387,160802672225740557853,-23266256952257343756,104488262955896574939,-91575474829107007704,60489962629399718870,-23170887167024927440,-14163203853282002964,8885718513217833629],[485820013170325139327,-678848884854665124403,382370462606452654029,-698143649240052318958,503255581422590149982,-591706264416951728503,242372371917172898919,-28126880170415506155,1300583862996518529810,-1119957134127157203243,1114145652798512838039,-853212647187893037824],[-4055067269328947288,469499286771646959431,-350753289602494466414,-134431921345414738854,172243881081711759578,-84004740193064949997,20568189920363444670,9194048909812544139,183281408679772989611,-162042291864710203169,233105993472399982587,-138136006993596663444],[-183578284047258799608,1507128687371322863845,-1081600852431471052975,-114364319360720095663,285571781100669123085,-124683469980921733302,342256273538090701353,-283346955852779392267,302729016227876739231,-172009597066402686094,232580590856776383262,-69244927236541797999],[223272238165804678807,-3986394698385590762405,2929056909438544890123,790259441249940977669,-1166479516204248298618,-593176891881750626576,-132797760998653962174,644404401997674516935,-1746986245140702514681,1187204711206521187725,-1408261195139056843031,758589831738177773866],[-153281144130136455622,2247720713588968102375,-1644421920568312322957,-394653138502241806240,614785725918777327417,328891995411244211264,22517829816382353398,-274719066790746366442,806090241867850307647,-553655033195940961514,711230484081176159836,-367641386429552238461],[-165384135629678666749,1033047845519181149678,-731090498430391475521,-4839746528239099742,133747199009216082714,76971339416407634171,91624102914933080880,-62194410410356063652,-35137874445584813006,43341231141437065505,39831026277426450569,39307140037171524490],[2727764075703761440,55054106682962729024,-41962609132599975079,-21720399752198677759,25218469865308040876,60813188070310918231,-273110728524836266603,239359368584218772596,-158108263022121379380,60563911158366498627,37019688271096162254,-23225432100788857021]] | 166498975140 | 2794910577644 | 146534138218 |
| 81 | [229606605098530398515188001916371339976434202298916868445288,529320759867070919561748029651605346451409424615071082339409,695175253563637021079101312588694253352935613235040330182913,193450011569398007645558983955842998863123317763666563497989,547405776281321707164098679942672272598802085535850647269654,435599689495158308954396130941362197997592965390272875572740,226328354406198408268684782350201293928919388415344629883153,526845193386543315866635321310446877083494417789465519445922,739959555500944152033781390737122446599806905989593569496338,174070770516100705326480971185118860395635768344717825341561,550110188032674710148006008149183154420998088664648496773459,603869749491393638872954679973579012088029284941159371348446] | [118952835156918339701442955001422155803662243434654890895025,132236637505091253339086942023460985341882972959444619539340,-1059832197424874101631010279137530303375228323638998829724521,437302309846077265549604955980974545990856658493056286061477,-23167312477326571673326531551739173099601650235721337423466,741589911556068308844782910976104508152382725403136182507906,138280802633699485875861445631208773677215821522872430525253,109164184851527475876125216416063189003262521363254904330874,-803235829996520311998868701582813377497436381540546201947452,399224678977789883255096724286767145877113271456459554195263,-2751325528146095739265104489520114127501709792292918815301,22495638327638149764782561854239698291217249293268851422847] | [-2361062588982670208570080891805570946386905401923673279103631,-396807609312279359004510139642016912269762478268872840171784,490027920210048878461019705617975755853306034865119700712634,-2370064176095494942045806023715637276197718043231826243788236,-494168282286549947150409764484452211933085230332574522586165,-2839671646767087284958036958509355415822502713213732878503576,-1792097510192095429588148298105258046532981839783176185440758,-616528166183319052681847700730786278288378304075110686919832,3348910614827195099646413862148613719655598489257169969344549,-2778166210467825275199069316399260527955938621675033447413340,-258354657288972930587751665763098085594642808187414238017681,-172376276812907165524299786163504528305195394545559004878443] | [[-75897926291079986613,571007820017252375530,-408143099367050675429,-31543276071076293675,98261575293828226086,4018925964459572271,-18047593056063519334,15817027544400681204,-10447925967642354023,4002129171001472118,2446714173882821072,-1535061176832340720],[-224201452784367245139,1549803484803823499549,-1103030761905223444237,-51761760608528213907,238162934856090938305,-67562131389452287522,303397938678150020759,-265899920176579910967,175639997654956521877,-67279760632545284845,-41131691887370976913,25805900839464724982],[-1135496284236138780477,-3333870087561935427926,3138438034747240307259,130410981763038320663,-742684218642893333640,134564688231212003522,-604283023471805965163,529597558919695015530,-349825279920933463127,134002285416389997598,81922715897480475147,-51398067668573802272],[437219592429982034339,1714941831368709850285,-1527033548973032407148,-75079534336455754091,363393493347815322106,-45007265295727242833,202111911442688765008,-177132189340142228160,117004538021896526594,-44819160875299605960,-27400334044612873055,17190887874480877938],[-114861238751624911330,1086390737289932057637,-736571054847949775419,-42741817895195061133,160745157602734768267,-23261360482275247834,104458646819325886569,-91548235205635671270,60472119759024733352,-23164141406574327283,-14161470228385716123,8884864193173653947],[485508208782252067668,-678341429184740990919,382073723028070304184,-697746044997820656177,502998567417662828091,-591435755623112792218,242269323937292362271,-28117258744661486105,1300032427045139265118,-1119500787062981349167,1113921217393723392319,-853053910340325306575],[-4051407176249073580,469336118005776373259,-350636898150580171880,-134407263666605642560,172205838463947170194,-84007209897014243629,20585848507675484745,9178582916936533769,183295374652543989981,-162052301405121046802,233144353755631794710,-138167480170773534294],[-183547956818258222257,1506633748299619670472,-1081252010593130524376,-114309020913364995100,285466602554385934198,-124658050052977078117,342220241412790521942,-283318812875502109997,302661063335566456525,-171961410890752589647,232556024742445960595,-69227175408566926021],[223383021090025949297,-3985208941259729004181,2928179554214977370783,789825148623900143477,-1165984455380605820632,-593267676145441437848,-132729345955750781362,644274124154498699368,-1746341524293304020614,1186730084197271584717,-1408019737728177010665,758421601297539840071],[-153330006872464202587,2247227209745523391143,-1644061691176760100647,-394483391152331649709,614590800086910428059,328961929453578240823,22508319463365204510,-274707684484166052778,805894872027257418906,-553502453996265252673,711191862351470821518,-367604169513674260054],[-165326361953129873493,1032651554779576116186,-730817877531081890552,-4848872223081813981,133706014007692349860,76966418123224009548,91603631447062074630,-62180321664607699432,-35109807830423847872,43315297099569627946,39845461403316615206,39295098899954919939],[2725221149914562023,55032377753344274648,-41946274438073685087,-21711560858664077018,25208797339764654797,60804980402283373617,-273053933261468704171,239306237130194922645,-158073559783136792385,60550850640731938785,37017951738491260657,-23224952536827320753]] | 166450825760 | 2795136652610 | 146438610972 |
| 82 | [229601471650372231086632726151437451036428109841365633950597,529315055224947796763772110665313724841166508494891720643257,695220971849768719858540705250944545718128342281586138310575,193431145517023027809875744989442245980511994012268661311973,547406775186607138188261375809052815926798641800377528560046,435567696995551342212446736089655349175796198544791414312308,226322387739527482884126602083028253451851202091198689967601,526840483813132407757921643793760640422751872003121046208851,739994207685515438710824819894348705021369785173784853440059,174053546633455998507589633724061122649239310049948540316590,550110306475800212003057816315507582230980709507351019752919,603868778939885624839151561205755746049801436055680572686224] | [119054681718853795783430137427807243953627556387834335304952,132253753017471620681805609243772195416714071088395373521530,-1059853334688938767655910608266926007692925841277990218447873,437404544096409499087462961872265536831578445606282081327781,-23145995969670505605276626707738881893501142680782820062869,741712366265150549490802518487805325701397267625305717395606,138358112804091137673594472914861733960542496945985802513738,109190775494406301031112605071392945004318272131193280741383,-803380250734349014677208186758937482352389853368839889609183,399344510636079748464060847921901172060024859732226690799080,-2740178179001667832997195736293662100026076428769823518236,22503073434943140151431056265364488860749546477147154957181] | [-2360957888473277384846440722169948967472662598666354541180126,-396737094445034306342835046695061628385778221594895914202796,489981534614354929521346411518391540823630492983691070351336,-2369931111300259052593522909628388962274199154833124488008607,-494151633949441996392881455937713019213576805293409802739689,-2837826499816679783778398154256843442047214586687924230316657,-1792316110029149389110782175113520400999702384089018823096675,-616322108330144485549014133065884580286737355441602701964804,3347021885018602194227136482886167819872575804241545398411496,-2777716457650874985707210656072149014105774180574518833496898,-258481729572761699387842639987097855051576164535833235229050,-172345510099873457674344962437976954322512736603224526029231] | [[-75881036348414193707,570820303675294164162,-408012275562032143466,-31531641337011009142,98229326791057982971,4015029220069358242,-18028777835603642509,15800316200706381217,-10436913232340189904,3997926056564792552,2444557029301323394,-1533748085166889127],[-224145858479797318114,1549282331006766451475,-1102668898157656585385,-51742555246015527059,238083580745762359885,-67563836397936203825,303383444895183286476,-265883489336534806433,175629580627835819128,-67276028943102869463,-41136350980351372790,25809502004090898883],[-1135138517905069350223,-3332664389091570875946,3137327031882973952373,130364409290221480818,-742421216616165961707,134550216581174619508,-604173924899218105123,529494519300001730061,-349758086150626123599,133977061511154281741,81921116811160838424,-51398414738461575682],[437187432761876801969,1714558222365317253067,-1526726148884514110503,-75060574850105716291,363319513291041417980,-45015397633213676007,202133672914227945043,-177148777137173364491,117015785805172066057,-44823641692286652556,-27407697598067716724,17195959515775306577],[-114783210066491566106,1085975476505769786077,-736302581743813383700,-42726326243294636359,160687686563473268102,-23256466557914450217,104429045427107093552,-91521008985298025010,60454285697970943264,-23157398997436869501,-14159737248407578911,8884010326164675254],[485196690288497174904,-677834528846365214521,381777321180326955994,-697348777723415649665,502741753055282111244,-591165379064004212703,242166310560199287632,-28107627993799458211,1299481249714968183520,-1119044656212760704715,1113696862553088201713,-852895223886063474948],[-4047755223247907676,469173069875823518031,-350520592144324133391,-134382617588188812572,172167819825191026926,-84009668084096200541,20603497239162427432,9163122668688261369,183309314603660336304,-162062291067639546535,233182704376138606940,-138198946395705018053],[-183517650044199242283,1506139170988298957961,-1080903426318328155408,-114253766292633370555,285361503658961447462,-124632643039147863405,342184220745300209841,-283290676503450466071,302593137035646154213,-171913244660469569472,232531462659230807152,-69209426191439867550],[223493674312484793422,-3984023927836715699255,2927302767308481672271,789391219649805125488,-1165489776294505471304,-593358383877845413504,-132660955094060426093,644143868749849621083,-1745697085931764891705,1186255676951317613607,-1407778354749978431946,758253418067858104420],[-153378832411298524504,2246734055294072436388,-1643701724432951405273,-394313777211699069635,614396023688162551900,329031840720856115754,22498809841544449939,-274696298011988174373,805699569351706707262,-553349930070979575831,711153255118474103321,-367566959747206168058],[-165268635731457858629,1032255573919805538077,-730545470376369853384,-4857987833786231636,133664859307824540892,76961499694947261540,91583167604405895154,-62166239289004848793,-35081756563085117436,43289377053149926717,39859889674063701737,39283061957405096057],[2722681446170495830,55010656226216292898,-41929945684312608055,-21702728225114885443,25199130665287015996,60796775194231797737,-272997154695429332384,239253121060855030205,-158038866650471941260,60537793969014386378,37016214830273213412,-23224472955856603938]] | 166402716618 | 2795363505069 | 146343135182 |
| 83 | [229596333808970893726666973514843233248703637023910607221901,529309349844580872033702194333993191952415771040641584395318,695266691047652397958513364661437443499620577747823523839462,193412275054707608232064407451280259533760772559929083002758,547407773172380917087378111545570418533468743734128472321930,435535699215349393339738137160307418800974470213205270541217,226316417737735477013684678111848216827423719668875348553256,526835773092876423815747884492467054751379432351607492505191,740028866098186598094855624673252169316017342009822457191945,174036317582068553491600151587954994165662875099570036560724,550110424437945913763576736455684570677687818111741544555146,603867808067679077334293875818442964444324652977726700724111] | [119156523762764545555516878817277590525679822564611544572904,132270865487642159953293637849737160197549123188980400822114,-1059874469951604883782308516741148051869831263262942010673221,437506772605222540816143041685541586105485993522659654404346,-23124680180626328363580136306319837472393185624982148579080,741834741407436761925264170474867266238531761424615928337686,138435432398004285883419443210002964540278764577502626383646,109217357250292223370734962845549454234803043043200564993779,-803524590024871808852305841124099922735278604935894431321336,399464322896641579201629769328998943813366830083093903573580,-2729025350873634499263879224136556250727889669300687524217,22510507214795200318410940123393021039853013112970249417856] | [-2360853114998964657688526024783069781041419030357236493914150,-396666560102908760635815983320217125069096580258205530804654,489935127240906883692458173973990315894243602807014025299518,-2369797975935994454096673882125651468954746265578565748669615,-494134964519623850054760105097609199523299839553302859215877,-2835982606653035072187548069666548099375325554878650547356626,-1792534422964269434418794676472621472401434548226339511513815,-616116129070348948222317974854523453389771613482132272949033,3345134386633697565783962451798829208802279512574359179465002,-2777266852951978675777806164373698291612040303642670476347373,-258608685242947019738335938310302817697748419201024683847596,-172314730701100219932375870557144999530198353406255932837906] | [[-75864158633782419961,570632920163365726417,-407881545109387772474,-31520014729490138335,98197101159548611389,4011132846981120455,-18009966855329847678,15783608992997497567,-10425903182023868865,3993723943266786185,2442399627523582522,-1532434779221239634],[-224090306725759607794,1548761566450122613472,-1102307306793860070719,-51723364190484387446,238004286216249431038,-67565541648350498399,303368951383655916670,-265867058374860986223,175619163597854107409,-67272297307204269551,-41141009298547693479,25813103142864020703],[-1134781040368354569564,-3331459613358280927849,3136216885922935898195,130317872568914379079,-742158417396688071452,134535749160029547908,-604064855406796508571,529391506421949373143,-349690909968038540892,133951844315036562821,81919516548639731753,-51398761628296760588],[437155307379891332394,1714174889657109732607,-1526418976089545739804,-75041629096418977262,363245587821149751334,-45023528102906426875,202155420869104235305,-177165352076621021840,117027025237352508177,-44828119400296879440,-27415060149677907411,17201030975592476071],[-114705247641151188385,1085560532897014986507,-736034313544378459055,-42710846018820811431,160630259058501300052,-23251575178521797533,104399458774983518717,-91493796164164143351,60436460443654467803,-23150659938630368457,-14158004913275192697,8883156912157942372],[484885457353479742042,-677328183092352056065,381481256598440884933,-696951847043681163900,502485138132516636231,-590895134705451399399,242063331798535549695,-28097987940476098679,1298930330948432931322,-1118588741523745549480,1113472588283205198395,-852736587829878718691],[-4044111399429456675,469010142237182971076,-350404371481244722884,-134357983095699822959,172129825135930237180,-84012114763144292584,20621136117998322175,9147668164760439890,183323228549821346401,-162072260865566716255,233221045334868449270,-138230405667330816993],[-183487363701193682746,1505644955032428176670,-1080555099319080726241,-114198555449685920480,285256484325558401410,-124607248936835453532,342148211538222146707,-283262546740034304370,302525237325076272265,-171865098372144497786,232506904607681873117,-69191679585827079258],[223604197989419065256,-3982839657388431484894,2926426548156088361260,788957653924413703230,-1164995478536514821692,-593449015119016170263,-132592588426252334961,644013635812200967536,-1745052930003270365214,1185781489417219536638,-1407537046211103953973,758085282054173757434],[-153427620786356624077,2246241249840912226488,-1643342020042014974735,-394144296530735864042,614201396555148015412,329101729215983973356,22489300958140621174,-274684907383420097219,805504333838914996460,-553197461415444566040,711114662382831129641,-367529757131613036235],[-165210956909689216812,1031859902581704798418,-730273276719323696317,-4867093371096534173,133623734873742865329,76956584128436907409,91562711387726489921,-62152163282895853684,-35053720638002523035,43263470997442590575,39874311089514988069,39271029209970894787],[2720144961419575596,54988942091952221144,-41913622863562295438,-21693901844474842916,25189469835057431584,60788572446469337592,-272940392828849877192,239200020378205468110,-158004183625413639344,60524741143686909713,37014477546583696630,-23223993357958714512]] | 166354647675 | 2795591135174 | 146247710866 |
| 84 | [229591191574521347705016581323598450383893492007775094947436,529303643726101394860087500983295592812592189705680769976636,695312411157201701075033295938245080463009785341499887334698,193393400182699485658746689098094270137215460522224104254254,547408770238674062143543348620425320563536112133043298396263,435503696157983557550575856218444029784447119002533281647469,226310444400416156448762401273707869878393978102471905758621,526831061226158647875693125076519180595411449651970591419762,740063530735445394879755768805178532712247445124285379486677,174019083362774989527077598822629897872160420085174007923565,550110541918875577775975271461692604044880058775413417046362,603866836874831270307832178834089161274698419121486201420302] | [119258361285503341048608274087422356112419503713923401339807,132287974914762917872639293113410467899684455634732139600683,-1059895603211933129865222150368329330681584794639966069914979,437608995369472561324911491829162263107036209336896811863290,-23103365111103849205670192394891091019417694391654755735716,741957037036996981616040302756637955123231691551803382114088,138512761403065578414183599240203102676706818752578714588358,109243930122574538736343848167408463111433190169765137540850,-803668847921194123841155064685040326939946579819628048177516,399584115765862551048397173234485974793091950280231005174976,-2717867048791195523860943045350884358975137042214575605112,22517939666647167655860833055043218875541963170828473274038] | [-2360748268570367910286877706717462587139254753174453078637342,-396596006292016687762955925277410888420635118771229792160099,489888698094514306335776140094762797704601158427338588297506,-2369664770016459188267723906354112781350150993482846365097549,-494118274000061930869344517803232396143669996320566065869162,-2834139966609157021614976970380659792304978400312117957296166,-1792752449122447422234772202812613298412328352916806250963733,-615910228358699533854011630637589593481661886878089674090748,3343248119008573395351260263098946559858424435642199155370992,-2776817396270438014543871957560068966703963740521363372413738,-258735524352600401571618494104862832767585384218436712689916,-172283938619384648020840715293269564459548695731371120432360] | [[-75847293132355336164,570445669329132791041,-407750907902063142780,-31508396239318496850,98164898373134536549,4007236845338063360,-17991160115681761554,15766905921659261330,-10414895816941114073,3989522831197245436,2440241968831879788,-1531121259114871491],[-224034797472799461819,1548241190691371892002,-1101945987504493407760,-51704187425776024579,237925051199948132710,-67567247141516855964,303354458150655565694,-265850627298253082961,175608746569369165253,-67268565726488092976,-41145666841475513533,25816704255602168767],[-1134423851299557574022,-3330255759315107132388,3135107595895279856758,130271371558562681811,-741895820754438756484,134521285968297817402,-603955814999720825328,529288520290554650740,-349623751376384976937,133926633829217076546,81917915109752377230,-51399108337993856153],[437123216247538123410,1713791832927990018924,-1526112030328946355139,-75022697059839548334,363171716875956490637,-45031656705926727069,202177155316706362547,-177181914167318050179,117038256324207408280,-44832594001509526962,-27422421698800646452,17206102253681594890],[-114627351400024812433,1085145906103891869420,-735766250017252407643,-42695377208839789111,160572875038438696030,-23246686343443544570,104369886858694461129,-91466596738300353387,60418643993488976137,-23143924229171714511,-14156273222916059091,8882303951120460007],[484574509642108019564,-676822391176709503230,381185528818382395269,-696555252585984496728,502228722446700926544,-590625022513205769325,241960387664881806879,-28088338607303619014,1298379670687802089374,-1118133042943063607496,1113248394590608786280,-852578002176499468996],[-4040475693910224763,468847334945468997049,-350288236059016785774,-134333360174702801012,172091854366701869389,-84014549942991855950,20638765147361041840,9132219404842214206,183337116507728972994,-162082210812205297707,233259376632779882538,-138261857984598328753],[-183457097765391046593,1505151100027682290052,-1080207029307836650009,-114143388335753899734,285151544465470585214,-124581867743433313088,342112213794144256450,-283234423588652001403,302457364200797433457,-171816972022355164541,232482350588345169201,-69173935592391579552],[223714592276848274117,-3981656129187786903887,2925550896195624891527,788524451045052519491,-1164501561697778597684,-593539569909031701446,-132524245964942141440,643883425369958874671,-1744409056454821626855,1185307521543410468003,-1407295812118133061617,757917193261485410156],[-153476372037299335721,2245748792992931614407,-1642982577709521930429,-393974948960052711694,614006918520727822067,329171594941885576488,22479792820358487268,-274673512607655080042,805309165486542347853,-553045048024979372482,711076084145176563268,-367492561668352243982],[-165153325432931952287,1031464540407652554031,-730001296313386666600,-4876188845743844928,133582640669634550861,76951671420552660075,91542262797780222245,-62138093645625573295,-35025700049602874236,43237578927705745003,39888725649522799394,39259000658097646630],[2717611692614451637,54967235340939992739,-41897305968079895698,-21685081709678372293,25179814842268481734,60780372159307093010,-272883647663847519863,239146935084239048184,-157969510709239819978,60511692165219218968,37012739887564410259,-23223513743215679016]] | 166306618898 | 2795819543081 | 146152338044 |
| 85 | [229586044947218690043895398484862866856534562259228719740911,529297936869640650958732827895090522327157670024988555038898,695358132178330234389271109543545855857523049537834135988477,193374520901246528124976048119284464114419413978901091398143,547409766385517630882402869673770885944474029631763389019528,435471687826882598268509620136892845120298883135898655773022,226304467727163820611977616541360238822696665246426494177571,526826348213362217611856032922973700885996625338533676704713,740098201593781883942959160626758228009432552876815930688840,174001843976411650433606220072164821196084256978015430632206,550110658918353183281154280609818156841122504738584617481923,603865865361399501309489454605615922381431332984661995113903] | [119360194283923393290367016379615867841401333153721469856973,132305081297994204952801071471442236646040457773853092792783,-1059916734468984393287292261824387095243649188482026959859700,437711212386116324868918843541575653870378443215362362072060,-23082050762012749370215244521400957191517458268185316083616,742079253207872466546004015271598125768617017542353347214198,138590099806907056106052808809904911821476909473917122082244,109270494114640591340357533112921463514301899808685426841319,-803813024476392744741132294575723234421149929191508483381578,399703889250125494984441451568982743600592276881174103999410,-2706703277781260830153556123213215538811775466544756087929,22525370789952000249474660733254627189488226477712559635791] | [-2360643349198132213846052693510779592884311760917506828303716,-396525433018474677409818061649416753252107551110421130664482,489842247179989455778587933367750579515229908227436912043902,-2369531493555419975636574205689650797730228323712829353695893,-494101562393725286113691799114767921831516639161680616544261,-2832298579017800928592517861438600292971554725941682522965586,-1792970188628729651622330822678807089816186670157669281286347,-615704406149943726030928197286512870377229609043037876525435,3341363081479075394356011495964806809421411788574041626428301,-2776368087505518052147238904414249725931964986164780105177680,-258862246954817637279725332100578828999170429172202041903958,-172253133857525482518720809619734955408669076729888057852765] | [[-75830439829325912476,570258551020490712401,-407620363833165108104,-31496785857314791339,98132718405689628006,4003341215283042720,-17972357617096220237,15750206987074267613,-10403891137337931369,3985322720445317669,2438084053508560212,-1529807524967300614],[-223979330671536844071,1547721203288661355920,-1101584939980682382353,-51685024935756022898,237845875629356346767,-67568952878255126164,303339965203257330191,-265834196113394096330,175598329546731126450,-67264834202590042074,-41150323608650444516,25820305342123426312],[-1134066950372733562055,-3329052825916668435640,3133999160829623728349,130224906218673149692,-741633426459743651827,134506827006496103845,-603846803683140308438,529185560910806002723,-349556610378861167993,133901430054869043149,81916312494334031625,-51399454867467356619],[437091159328384375667,1713409051862337291768,-1525805311343925386606,-75003778724834887156,363097900393371466626,-45039783443394732157,202198876266416032072,-177198463418090853779,117049479071502064762,-44837065498102206202,-27429782244793182414,17211173349791869347],[-114549521267647086136,1084731595767166812856,-735498390930392902528,-42679919800437291701,160515534453979736604,-23241800052025356047,104340329673975208433,-91439410703769246357,60400836344885694928,-23137191868076876869,-14154542177257579973,8881451443019192760],[484263846819778353070,-676317152354637036379,380890137376872405269,-696158993978215457395,501972505795434939575,-590355042452944962375,241857478171757614667,-28078680016859805482,1297829268875185608588,-1117677560417720395147,1113024281481769953214,-852419466930611487306],[-4036848095819198416,468684647856515142508,-350172185775471350410,-134308748810790362255,172053907488093050804,-84016973632472074739,20656384330432268977,9116776388619168881,183350978494087767194,-162092140920859732077,233297698270841978859,-138293303346462633079],[-183426852212978441910,1504657605570342627447,-1079859215997475158422,-114088264902138991693,285046683990122595389,-124556499456327027368,342076227515640030029,-283206307052690483779,302389517659730489579,-171768865607666310421,232457800601761775487,-69156194211792954519],[223824857330573948867,-3980473342508720448477,2924675810865714099877,788091610609616072739,-1164008025370017640637,-593630048287994248564,-132455927722691772693,643753237451462023785,-1743765465233236287983,1184833773278196729030,-1407054652477581989796,757749151694749168985],[-153525086203731223552,2245256684357610194096,-1642623397141484939289,-393805734350478770749,613812589418009205106,329241437901502270357,22470285435387077593,-274662113693872289765,805114064292192181930,-552892689894861751801,711037520406134624599,-367455373358873489478],[-165095741246375329322,1031069487040569714256,-729729528912376220982,-4885274268446248626,133541576659743732245,76946761568154434585,91521821835317879503,-62124030376535390989,-34997694792305914272,43211700839191034397,39903133353944499297,39246976302227176606],[2715081636712403043,54945535963582009781,-41880994990134132479,-21676267813670559266,25170165680123000331,60772174333054120299,-272826919202524922308,239093865180935044768,-157934847903219551933,60498647034077672039,37011001853357078065,-23223034111709542589]] | 166258630249 | 2796048728946 | 146057016735 |
| 86 | [229580893927258153498197060392844416652998224377573674996685,529292229275329962261316870069680055783805881861350346068519,695403854110951562576508615802680512984856323159308209419974,193355637210596734928620729124842902745373229374159233611276,547410761612942720067629009767623876949138356705302383039352,435439674225472948367934306930923672109496697888064859374767,226298487717573302324477965104970476692792464639344330624772,526821634054870124621060197973436311006368570428012441508774,740132878669688409109601314932349738966466485667611987845323,173984599423814604789235811624587514888117371495687395267616,550110775436142926315702965655096281798046011936303311903842,603864893527441091484053252769059648857194877274360653701254] | [119462022754878372701486557775889643891252967218981999302034,132322184636496595613758162716539815820586363249258647607393,-1059937863721819769074917962783787655618583498535069465004323,437813423652111189743491789177695526245759113712423626121115,-23060737134262581963924648550254932491648171782213029847775,742201389974075686531259274314033929203383976236014624160226,138667447597166155071789102003073653277137932678898560130506,109297049229875772923599341216487994476674178445499489207776,-803957119743515801839019115000114790821505891281266347717836,399823643355808895816745352411256967976114636184111656269623,-2695534042868449434888133620589608290861498688933639544183,22532800584162776947126595849641057053414964238031646436005] | [-2360538356892911824390247569171641914931383797592921541643973,-396454840288401941571026010920935374909730286566193010307599,489795774502147281907602919941361588737650521332313162043588,-2369398146566652211610015807323691816125463456563938662929305,-494084829703585586673875260897086957027744143274260661531031,-2830458443211475413531422126355216009650416784905435695948674,-1793187641608216530576745566853053358942050630646071700532006,-615498662398809548626143562293566131185839844630600759555450,3339479273380804702296066022558887535522856963192554576443007,-2775918926556447546372729149699106510189869477730848879294119,-258988853102718649660223325372461255758799785285561816016116,-172222316418323008151407578620295767705594656566294751387722] | [[-75813598709909376518,570071565085564038000,-407489912795961491767,-31485183574311593331,98100561231127125358,3999445956958566386,-17953559360007274629,15733512189622480581,-10392889143458612564,3981123611099506442,2435925881836032448,-1528493576898079567],[-223923906272666194221,1547201603800803979888,-1101224163914018180399,-51665876704314275883,237766759437073664045,-67570658859383325750,303325472548523763867,-265817764826955406771,175587912534282489042,-67261102737142917067,-41154979599588135093,25823906402245881515],[-1133710337262428868079,-3327850812119158209788,3132891579757046843445,130178476508813522626,-741371234283274281144,134492372275136737655,-603737821462173865120,529082628287663650188,-349489486978644355683,133876232993158679157,81914708702219986442,-51399801216631751326],[437059136586051889523,1713026546145006283153,-1525498818876081898908,-74984874075895853512,363024138311397995844,-45047908316429521875,202220583727607928914,-177214999837759392267,117060693484997519796,-44841533892250899241,-27437141787012811197,17216244263672503640],[-114471757168666057128,1084317601528147341185,-735230736052107223889,-42664473780718524266,160458237255893010755,-23236916303612308385,104310787216557049179,-91412238056629689122,60383037495253415848,-23130462854360906423,-14152811776227057527,8880599387821065141],[483953468552374310823,-675812465882523399290,380595081811381035497,-695763070848785446600,501716487976583614798,-590085194490273056241,241754603331621538806,-28069012191688058564,1297279125452535244738,-1117222293894599568498,1112800248963096383018,-852260982096857940047],[-4033228594297831607,468522080826373831380,-350056220528595338185,-134284148989583545615,172015984470740865524,-84019385840417964565,20673993670397482100,9101339115773335940,183364814525604842067,-162102051204836131626,233336010250034302074,-138324741751886478586],[-183396627020180507360,1504164471257295739489,-1079511659101305489209,-114033185100213180652,284941902811069593033,-124531144072894322806,342040252705268550210,-283178197135525245661,302321697698776567581,-171720779124629659786,232433254648467850254,-69138455444687363870],[223934993306180001464,-3979291296626196608878,2923801291605772705586,787659132216565711748,-1163514869145527870322,-593720450296030173172,-132387633712009548258,643623072084981736326,-1743122156285148862020,1184360244569758202764,-1406813567295903835624,757581157358878710414],[-153573763325200679165,2244764923543017179457,-1642264478044357377732,-393636652553061278303,613618409080345171328,329311258097792939376,22460778810399704566,-274650710651236816974,804919030253411399667,-552740387020328161299,710998971166319110830,-367418192204618802822],[-165038204295289722975,1030674742123918422008,-729457974270483321853,-4894349649908810853,133500542808371340457,76941854568102354571,91501388501084681348,-62109973474963221217,-34969704860524345417,43185836727143644226,39917534202642480879,39234956142797810226],[2712554790675328903,54923843950295115936,-41864689922005282835,-21667460149407132274,25160522341834055652,60763978968017435901,-272770207446970252365,239040810670259218210,-157900195208613054822,60485605750725280387,37009263444103447598,-23222554463522368957]] | 166210681693 | 2796278692924 | 145961746958 |
| 87 | [229575738514835106535669672819749746395798181562303226243523,529286520943300686904005661425701312397330136567952100841085,695449576954979209815098427845788129699467070614405708946792,193336749110998236604730667022893392950993062221718172477550,547411755920980465695391005654519905415981066188483827489329,435407655357178711416149904879065008280379410368012924996806,226292504371239967573155541056038472872902449166166814220025,526816918751065214507095680058126652020457185923277708236417,740167561959659601916213917495492596219695808346500108986391,173967349705819646117995634979726873852162871132618794733721,550110891472009219613053955289995659392548564402291593645514,603863921373013385566164950866462990835857009089213187628809] | [119563846695222409491826419337788429253553775891728313478461,132339284929430928295596320670368509834016039017322809380973,-1059958990969500560014331790085302691518503055370073527376843,437915629164415108658255073580215451921974617455144812379666,-23039424228762771848394592972656788502492711431038067340145,742323447389590312621179774213852937405340150375886311846369,138744804761485709023663012025459746427381335417164829395148,109323595471663521919092334198701064754689630148642182054861,-804101133775582760101785617127336314735175830801630672730104,399943378089286890620688455636489883085144040558261284776465,-2684359349075088410555585257592650244090655364267109877613,22540229048732697425465357954602017554323929142272031740784] | [-2360433291665370179566357612121798682319319919930926307875630,-396384228107920313052538441973429380152034166963103556218799,489749280065805424761749115844111195466897869664882098761383,-2369264729063939962528766705065767891188662637812984582111947,-494068075932617126109516437563931234232956580113726220881699,-2828619558522444314928390350816875099404824105890922164044664,-1793404808186062243405233367589470130455023689175177152874875,-615292997060005715289981413300367449104406645803146257242413,3337596694049119779846896737215196422710908649963931107118678,-2775469913322419288487622759098095808950946153560751640612659,-259115342849447340221498434864172345018354278793297308205011,-172191486304579053080178204569240025655005988832864187392584] | [[-75796769759343171551,569884711372706076984,-407359554683880783598,-31473589381155313109,98068426823399564100,3995551070506795064,-17934765344846195838,15716821529681238474,-10381889835545738739,3976925503247672760,2433767454096768726,-1527179415026797542],[-223868524226956287600,1546682391787277390628,-1100863658996556511579,-51646742715364940263,237687702555801192834,-67572365085717640757,303310980193504892253,-265801333445596789165,175577495536358124309,-67257371331776619471,-41159634813804271116,25827507435787627527],[-1133354011643680037583,-3326649716880341288602,3131784851710087210886,130132082388612404910,-741109243996047405434,134477921774727711192,-603628868341910107650,528979722426059642707,-349422381178893318001,133851042645245209149,81913103733245567983,-51400147385401524728],[437027147984216962146,1712644315461326381902,-1525192552667403857597,-74965983097536665229,362950430568132704575,-45056031326149100360,202242277709649719037,-177231523435137181706,117071899570450560056,-44845999186129959441,-27444500324816876151,17221314995072699881],[-114394059027842959416,1083903923028681106199,-734963285151051600714,-42649039136808137940,160400983395021275951,-23232035097548891475,104281259482167285126,-91385078792936835605,60365247441998503080,-23123737187037938594,-14151082019751694268,8879747785492961576],[483643374506265813193,-675308331017944374772,380300361660126200194,-695367482826626538547,501460668788276422945,-589815478590720780966,241651763156871268363,-28059335154297432387,1296729240361644992529,-1116767243320463270023,1112576297040932567406,-852102547679839473259],[-4029617178500031049,468359633711315961316,-349940340216531274279,-134259560696731748749,171978085285332252764,-84021786575662356203,20691593170445941995,9085907585983202611,183378624618989836283,-162111941677442251401,233374312571346888220,-138356173199840269530],[-183366422163259337790,1503671696686032256101,-1079164358333066075425,-113978148881418624505,284837200839997061622,-124505801590505087393,342004289365574516302,-283150093840520366198,302253904314817115640,-171672712569783953557,232408712728994638802,-69120719291727546871],[224045000359033089773,-3978109990816203926365,2922927337856009813324,787227015464928632429,-1163022092617179250184,-593810775973289828991,-132319363945350278611,643492929298722068606,-1742479129557011240091,1183886935366148687955,-1406572556579488670416,757413210258745355692],[-153622403441200019205,2244273510157810285871,-1641905820125032497524,-393467703419065150832,613424377341334045910,329381055533733964087,22451272952553986359,-274639303488899691371,804724063367690503714,-552588139396573851988,710960436426333415125,-367381018207022559147],[-164980714525026470186,1030280305301701037125,-729186632142271734962,-4903415000823597499,133459539079874992096,76936950417256758683,91480962795820287919,-62095922940243516436,-34941730248663854327,43159986586802323148,39931928195484157880,39222940180244379440],[2710031151469739538,54902159291510569324,-41848390755985155499,-21658658709854442455,25150884820624931101,60755786064502020037,-272713512399257209070,238987771554163838326,-157865552626671714496,60472568315621714870,37007524659945290167,-23222074798736240420]] | 166162773194 | 2796509435173 | 145866528730 |
| 88 | [229570578710145053317073410749617691422940839239729188121766,529280811873684219216061139224666833152258412708648179558838,695495300710326659795428570353514867083279867215988784273123,193317856602699294899888256123861709988288091577045378044764,547412749309662042988820464805622005556115021664903923079119,435375631225421662915876959712162604300828982726318303957510,226286517687759715277761481608661329365645510350378187091437,526812202302330186964996488515338749363674657952564938413191,740202251460192380373967814931684334688655988438774432592468,173950094823262293077475256620706604467803355137781361830384,550111007025716692504593770239205902964845710582023962864282,603862948898173751875106144961151450454058610736910191577832] | [119665666101810094056409539876894656550611572469834634158060,132356382175958305571529111053649772971875073599765722321489,-1059980116211088276767614053235512512283873949005384306363979,438017828919986629111083246345868950771544074094813964457129,-23018112046422615526994394012932282790149983237702177690176,742445425508371206580059433907902864184024235952369444126900,138822171287513951586034755925511092247414378776737192889797,109350132843385322622294802211932785235784480466986281827444,-804245066625584408748937964748021504469764611435484990053144,400063093456929267195578220999814662094792464015767038802631,-2673179201421211854290455190725015929356575411647010891457,22547656183115082256477854859762534906905259653940535821908] | [-2360328153526179895444473018963217130991137017661428354057605,-396313596483154243973198825647553415163432442484650544756578,489702763875784213124212476192553044114463631263385390754893,-2369131241061075961722094733735478407657454125727070745612269,-494051301083796819717591726221009137103161838088345836457041,-2826781924282728579007788623178109321914569668326159294584843,-1793621688487474418895640603470403351394757461955177780311778,-615087410088221778580927453164991152131040280452456627621349,3335715342819138297404084857383115203368627304887670823027207,-2775021047702590428287667050046756240740378745185434150005743,-259241716248171437846881326730622317347924761316272858879584,-172160643519096988191270285428523300073869511778452693454889] | [[-75779952962886914758,569697989730498469611,-407229289390511837518,-31462003268706173652,98036315156498701659,3991656556069543083,-17915975572041480582,15700135007625258626,-10370893213840183534,3972728396977036324,2431608770573304794,-1525865039473080340],[-223813184485250095385,1546163566808222616013,-1100503424920816735048,-51627622952846390337,237608704918341367795,-67574071558072428691,303296488145238227469,-265784901975966426520,175567078557285285755,-67253639988118155504,-41164289250814575725,25831108442566762504],[-1132997973192012904333,-3325449539159551009623,3130678975722738772251,130085723817759150677,-740847455369424373196,134463475505772686130,-603519944327407404196,528876843330897905533,-349355292982748400284,133825859012280877496,81911497587246137404,-51400493373691156412],[436995193486610284840,1712262359497100740234,-1524886512460267396983,-74947105774294854191,362876777101765353173,-45064152473670396381,202263958221902050537,-177248034219031295677,117083097333613717437,-44850461381912111726,-27451857857562768178,17226385543741658137],[-114316426770052000472,1083490559911154870501,-734696037996230553994,-42633615855850193318,160343772822281318538,-23227156433179010441,104251746466529243528,-91357932908742138224,60347466182524900806,-23117014865121196162,-14149352907758593070,8878896636001726418],[483333564348308263988,-674804747019660565129,380005976462072201734,-694972229541190565010,501205048028906916164,-589545894719745733133,241548957659843728641,-28049648927162674145,1296179613544151518938,-1116312408641952474746,1112352425721559917767,-851944163684114287153],[-4026013837592141444,468197306367830500925,-349824544737576999036,-134234983917912663536,171940209902603905354,-84024175847037879282,20709182833770678050,9070481798923719075,183392408790954877861,-162121812351987461015,233412605235780226029,-138387597689302052593],[-183336237618514410015,1503179281454645747094,-1078817313406923736578,-113923156197267527710,284732577988720565347,-124480472006521391045,341968337499088268868,-283121997171028526944,302186137504713949161,-171624665939654982058,232384174843868482254,-69102985753562828274],[224154878644282979626,-3976929424355753050932,2922053949057425419580,786795259954296876852,-1162529695378414754911,-593901025359947434297,-132251118435115363615,643362809120819906440,-1741836384995093165900,1183413845615296252448,-1406331620334663651569,757245310399178145392],[-153671006591165582728,2243782443811234614278,-1641547423090842593536,-393298886799972585519,613230494034819018243,329450830212319178157,22441767868991869583,-274627892215997897228,804529163632463719390,-552435947018752961509,710921916186770545760,-367343851367511491722],[-164923271881017721206,1029886176218459121998,-728915502282677328721,-4912470331869694155,133418565438668879044,76932049112478207010,91460544720258808032,-62081878771707274003,-34913770951123137325,43134150413399405076,39946315332341955825,39210928414998228595],[2707510716066747761,54880481977674015466,-41832097484377069208,-21649863487989443647,25141253109729105986,60747595622810820352,-272656834061445047885,238934747834587707847,-157830920158638098421,60459534729223311579,37005785501024400817,-23221595117433257846]] | 166114904716 | 2796740955849 | 145771362072 |
| 89 | [229565414513383633676321038108635094880021125994796336845358,529275102066611989708444834508441582822370284926217378026029,695541025376907355728892091486878555745107690174448370144251,193298959685948302746542991812788052557295421529021277036207,547413741779018666392471955940340043767642157182208440052503,435343601833621251548223993645139431537982215177762856744845,226280527666728977057921108326204484901306536145533375924505,526807484709047595865353716605125744836346056375399147133607,740236947167785947731467944081655395043791643813300942237987,173932834776977789646471709147024566643907804734930017224946,550111122097030190820728950594662570286152596020003764422377,603861976102979582309582169568276763960324641286102229669099] | [119767480971496477371281552944028381210236228608466850700648,132373476375240094260854505300524492369181101884913044238125,-1060001239445644637988646430584786038885602835223173760803096,438120022915784893761882170887013551422226005556163003573794,-22996800588151281031793190810118687285877731386868268025675,742567324384344410450177815682504344182344310941822280351840,138899547162904518593638237559698513004598160564212112914502,109376661348420704367761036628869208852084276153369880561558,-804388918346482850906233433364775772941588112211568112448253,400182789465101462534185408407472303849728475054905072177025,-2661993604924559863290486478268970568678579308416490993878,22555081986763372974022148313472313722495849812170647172919] | [-2360222942486022763315814109172827005270466706028667173158804,-396242945420230804265561042841521598751629970746025308635213,489656225936906663113719307798119002074222882609366214946854,-2368997682571861605560028250636485995784038083596893805517670,-494034505160104203595514167786760366855156097545879352023306,-2824945539824108144807277782320219589832036632893738789104501,-1793838282637713799272286691761651281812974294851747242181504,-614881901438128278737018905084857040807547594793330006704485,3333835219025739019068764025488766647680996946265787437559200,-2774572329596082798350880694055661360683465749614933667328905,-259367973352082347817046473125479686616167047232768750698196,-172129788064681726384555879185396898603928475861190674003492] | [[-75763148305822355613,569511400007750757700,-407099116809603569807,-31450425227838184629,98004226204455443585,3987762413788279164,-17897190042018856572,15683452623826642468,-10359899278581116432,3968532292374176777,2429449831548239862,-1524550450356590354],[-223757886998464645100,1545645128424442836976,-1100143461379780987113,-51608517400721172394,237529766457597759307,-67575778277260220705,303281996410748782968,-265768470424700923636,175556661601383618083,-67249908707791639498,-41168942910134809430,25834709422401389635],[-1132642221583441669661,-3324250277917686263023,3129573950830448662449,130039400756003749578,-740585868175110472064,134449033468771000823,-603411049423693929589,528773991007054286752,-349288222393331546148,133800682095410960092,81909890264057090777,-51400839181415121115],[436963273057016840600,1711880677938605382353,-1524580697997436089692,-74928242090731222451,362803177850578660799,-45072271760109263578,202285625273718554865,-177264532198242366373,117094286780235269791,-44854920481768452863,-27459214384607925848,17231455909428576460],[-114238860320280148819,1083077511818493493196,-734428994356996241381,-42618203925008123925,160286605488663814443,-23222280309845987401,104222248165362289396,-91330800400093359304,60329693714234140685,-23110295887622992101,-14147624440174757201,8878045939314163962],[483024037745841683672,-674301713147615177479,379711925756928328157,-694577310622448201380,500949625497132279164,-589276442842732589674,241446186852815193962,-28039953532724263498,1295630244941534595836,-1115857789805587335793,1112128635011196876811,-851785830114198210567],[-4022418560752930763,468035098652624087898,-349708833990185379981,-134210418638832211719,171902358293342168479,-84026553663376946016,20726762663568474610,9055061754266306194,183406167058214547984,-162131663241782716484,233450888244345237446,-138419015219257503693],[-183306073362282508772,1502687225161831585342,-1078470524037472871611,-113868206999342014531,284628034169185507992,-124455155318297505954,341932397108325814396,-283093907130391029262,302118397265309296709,-171576639230755617800,232359640993610826358,-69085254830839124231],[224264628316862906144,-3975749596522874803501,2921181124651808922557,786363865284826334458,-1162037677023249340297,-593991198496200944585,-132182897193652890837,643232711579345059695,-1741193922545482709831,1182940975265003585967,-1406090758567693134301,757077457784963913884],[-153719572814477828357,2243291724113121537799,-1641189286649558173402,-393130202547482662478,613036758994887688796,329520582136559825442,22432263566839651957,-274616476841654388825,804334331045109115520,-552283809881978606907,710883410448213145241,-367306691687504705044],[-164865876308776291349,1029492354519272429483,-728644584447007375072,-4921515653713225475,133377621849223658375,76927150650627487483,91440134275128807378,-62067840968682043075,-34885826962293925640,43108328202160831217,39960695613093303172,39198920847487220373],[2704993481442060155,54858811999245460292,-41815810099495831076,-21641074476799672435,25131627202390236334,60739407643244755551,-272600172435578605902,238881739513456185819,-157796297805745971034,60446504991983077654,37004045967482598297,-23221115419695540661]] | 166067076225 | 2796973255110 | 145676247000 |
| 90 | [229560245924746623100601354350299894357200261535675113867360,529269391522215465062416691339302863794799710961903258135021,695586750954634700356861675379963812008988089889206625364656,193280058360993784237329992135782191280105713381789280663356,547414733329081589566778722800867490125080513756386698708081,435311567185194600416103388504761466026932694305476968551220,226274534307744717000050235356719307081123380536903425672381,526802765971599849338664053885037172204877501220570885282245,740271649078941791237103706614625857274229879899466090498533,173915569567801105312702370401288597125109746589459055894622,550111236685714776791908126328274137702898938776717259345760,603861002987488292342502748224254131122086322288786247378763] | [119869291301137071389231881601504714885357079460567092161977,132390567526437925541846789095571785082280146869416079580312,-1060022360672231570439004781542457011002391135340550234760657,438222211148769640806200186279333741319386485336203632500256,-22975489854857807810527071931812415141976662301945206100229,742689144071407136196084065075776627554902216183143159711400,138976932375316450375601801319633818447509526692664034503332,109403180990147240712211888813634822946202505622017138292766,-804532688991211493340566502131231508213283858925734272319394,400302466120164561306249724128529725641676237392149616379992,-2650802564600577516741167519861625239642169087693075375442,22562506459131132140329726676164197778309159005887126811405] | [-2360117658555589746488107305040190096707339430874837244991107,-396172274925279680175991575429684033117142133072017444339995,489609666253998476775062546936943981714398514572953910542425,-2368864053610106949503156720722856760531937169665846866398478,-494017688164521433703490886009538332103207398044250822948445,-2823110404478123824714080226191894255130096737207451733474593,-1794054590762093909937715657511778124238499951310984222758365,-614676471064376892088275179680191942751897021831484655615427,3331956322003563682083248583827692384643914588806662349311729,-2774123758901983237500404191127580806292841637292700066391770,-259494114214395001190120055229983552462918181876914377508940,-172098919944139721861815306631213464658197785233008291875733] | [[-75746355773453334345,569324942053499956045,-406969036835064658056,-31438855249439116461,97972159941339769913,3983868643804127190,-17878408755201287906,15666774378654880531,-10348908030006006046,3964337189525034949,2427290637304236542,-1523235647797026547],[-223702631717590881432,1545127076197402142237,-1099783768066893310870,-51589426042975959231,237450887106574883244,-67577485244091723776,303267504997049088275,-265752038798425320775,175546244672965166171,-67246177492418297300,-41173595791280770207,25838310375109617179],[-1132286756494467983830,-3323051932117208547131,3128469776070114476481,129993113163156712733,-740324482185154281905,134434595664217677657,-603302183635767716034,528671165459376604379,-349221169413746328384,133775511895773776070,81908281763513859151,-51401184808487888740],[436931386659275801905,1711499270472588315054,-1524275109022060217876,-74909392031429798437,362729632752948130539,-45080389186580480695,202307278874445848053,-177281017381564585708,117105467916059241662,-44859376487868451748,-27466569905309835508,17236526091882650924],[-114161359603626922085,1082664778394158917866,-734162154003047803346,-42602803331464699773,160229481345233190198,-23217406726892563225,104192764574381837747,-91303681263034582464,60311930034525349313,-23103580253554732398,-14145896616927090350,8877195695397038451],[482714794366689844470,-673799228662931813895,379418209085147453746,-694182725700888054722,500694400991872881339,-589007122924993321316,241343450748001400302,-28030248993388451958,1295081134495117531879,-1115403386757767529354,1111904924915999030086,-851627546974564775342],[-4018831337173575546,467873010422620628003,-349593207872964024465,-134185864845224480709,171864530428382938648,-84028920033511734972,20744332663039857357,9039647451678863233,183419899437485844913,-162141494360140532141,233489161598063258171,-138450425788699914799],[-183275929370937652852,1502195527406885812547,-1078123989939734653694,-113813301239294002564,284523569293466892357,-124429851523179926892,341896468195788849953,-283065823721937811706,302050683593425845868,-171528632439585848209,232335111178738230272,-69067526524198948215],[224374249531489934317,-3974570506596618242672,2920308864081737635534,785932831057235745451,-1161546037146268915396,-594081295422271925488,-132114700233257733753,643102636702300356778,-1740551742154086742274,1182468324262948352308,-1405849971284778783264,756909652420847363730],[-153768102150461431229,2242801350673887590912,-1640831410509387129065,-392961650513510947849,612843172055871616990,329590311309484517121,22422760053208004950,-274605057374978105889,804139565602948725089,-552131727981322977270,710844919211233509408,-367269539168413687904],[-164808527753895513080,1029098839849757893077,-728373878390939851936,-4930550977007374499,133336708276066342510,76922255028565622260,91419731461153316701,-62053809530491931484,-34857898276561010603,43082519948306172060,39975069037620622474,39186917478135741728],[2702479444575968373,54837149346699243207,-41799528593667715012,-21632291669283228238,25122007091862135751,60731222126102719038,-272543527523688327014,238828746592681210991,-157761685569220309082,60433479104350697107,37002306059461725038,-23220635705605226835]] | 166019287683 | 2797206333116 | 145581183534 |
| 91 | [229555072944429932710485573858558576296736973568919406148968,529263680240626148118129017633575555613718107323846563714486,695632477443422055959669252572715369335465358453360695526898,193261152628084394599372406651106450723619426233428909256003,547415723959882105382503522916389923582777591495446832690951,435279527283556508288092233672115253153947345212025992148803,226268537610404431424173259218036406520859020131424011785917,526798046090369209859713400383683521709486300063536191344393,740306357190163680900958286084782683373603984529126244329948,173898299196566935260582958693477075860157590951539323015975,550111350791535728949600311254194750085531180090081948900320,603860029551757321015759776019465124925373162569488965418487] | [119971097087587849435376540620258027463905925568978331548321,132407655628713695064583754443210159980928248411601592786752,-1060043479889911209103791142229920925427764212755155800424909,438324393615901204348668817976923034452819272758242974062795,-22954179847451106613606664454961451687643290140717062060124,742810884623427755429903282513185163511162673505922367767132,139054326912414194025239611311132489007879436407009171662537,109429691771940548623999642720446395303213490233973694086664,-804676378612675036275829889671779324996452926307215133364366,400422123428475294355921600679649867506378687780478087186954,-2639606085462413864229842212119875465409555273084076427831,22569929599672043412477067338448525653241286388215992813224] | [-2360012301745580977078403682374354452697245025580135729188063,-396101585004433172764049006600939855919052972018932453056494,489563084831888040668872644400508584819216360151328212631267,-2368730354189630704150023303183989023731499420737582200019636,-494000850100033284926156701639504979610266552946734012485416,-2821276517576079180459106001672939473126170373935764633452147,-1794270612985980729999108102167016112608887688108514268363350,-614471118921600579110735360515735221927638611138923985381385,3330078651087018871724068502117134662381461791137839390762917,-2773675335519343913477647825709820271501798995661661807869347,-259620138888347704538932203303819825673291493849129660747821,-172068039160278969414611085358945326019354586132632486640365] | [[-75729575351105740499,569138615717010124801,-406839049360963240796,-31427293324410474431,97940116341260661694,3979975246257866965,-17859631712008980438,15650100272476857439,-10337919468350623393,3960143088514914102,2425131188124020790,-1521920631914124433],[-223647418593693527362,1544609409689224285847,-1099424344676058787812,-51570348863621504783,237372066798378011184,-67579192459375822881,303253013911139203717,-265735607103753107307,175535827776334384036,-67242446343616469676,-41178247893768293588,25841911300509558493],[-1131931577602080029472,-3321854500722139030593,3127366450480081542375,129946860999088958940,-740063297171947029377,134420162092603430400,-603193346968596703776,528568366692684693401,-349154134047077979833,133750348414500699506,81906672085451908608,-51401530254823924374],[436899534257280428740,1711118136786268640339,-1523969745277676046067,-74890555580997793265,362656141747341874925,-45088504754197751824,202328919033423531955,-177297489777785706429,117116640746825405034,-44863829402379949699,-27473924419026031390,17241596090853075660],[-114083924545304175547,1082252359282149162830,-733895516704430710795,-42587414062421990999,160172400343127484269,-23212535683660899292,104163295689299365820,-91276575493606223998,60294175140795255681,-23096867961926918878,-14144169437942396656,8876345904217074089],[482405833879159407340,-673297292827912266379,379124825987924642674,-693788474407515753801,500439374312311829869,-588737934931767405660,241240749357557657789,-28020535331527302258,1294532282146067603681,-1114949199444772599049,1111681295442059217357,-851469314269645290600],[-4015252156057646216,467711041534960894964,-349477666284674992943,-134161322522851659548,171826726278611562897,-84031274966274174887,20761892835389079712,9024238890825775573,183433605945488147975,-162151305720374952611,233527425297966018231,-138481829396630180767],[-183245805620891021395,1501704187789704007560,-1077777710829156226856,-113758438868845076546,284419183273769080216,-124404560618507391487,341860550763964787807,-283037746948987467392,301982996485866789033,-171480645562632808310,232310585399762375344,-69049800834281416920],[224483742442665318846,-3973392153857048735988,2919437166790575303692,785502156872805706378,-1161054775342629316970,-594171316178405425981,-132046527566171649824,642972584517621739025,-1739909843766631406182,1181995892556683540934,-1405609258492059684016,756741894311531139987],[-153816594638385379739,2242311323104533361145,-1640473794378973910211,-392793230550189097791,612649733052345870087,329660017734139188893,22413257335191996403,-274593633825063989026,803944867303248665723,-551979701311817426232,710806442476393606504,-367232393811642326449],[-164751226162049088424,1028705631856068619368,-728103383870522747221,-4939576312392401942,133295824683780189638,76917362243153874096,91399336279049839974,-62039784456457612615,-34829984888302268791,43056725647048649329,39989435605811321552,39174918307364709813],[2699968602453340448,54815494010524010224,-41783252959230440189,-21623515058448753446,25112392771408756334,60723039071681582537,-272486899327790287061,238775769074161325169,-157727083450277316947,60420457066772536624,37000565777103647121,-23220155975244472877]] | 165971539056 | 2797440190024 | 145486171691 |
| 92 | [229549895572629609240016644136803932995986399985290632300251,529257968221975577863215570381179868397773430411148985400102,695678204843182744365590605759691684323884483614769097054601,193242242487468920168567719899852440924474288733393140309732,547416713671451545915184593103066527794055758713638295447140,435247482132119450842734648010466680977648987665616621179425,226262537574306148650643643213376837088680039830480259857295,526793325065737794331995307074796767162234958032846383899153,740341071497957668256280396221410436382502106883783716204312,173881023664109700559070043696061903475814379111200847669626,550111464414258542027229700047916466840138221001505212156863,603859055795844130935002235419342185746229922885112121686793] | [120072898327705246602602535821121639083177192969321756403121,132424740681229563063709144110557911026860447617605220395169,-1060064597097745897307404872002397462310252515022821531817604,438426570314140514776272933566518740063633647701275598923542,-22932870566839959381165216825969082444974258469799319018678,742932546094245789217469548709048022191515599316143463666043,139131730761867605655647476869566949366808649881556066354821,109456193697174287678951753560681830579659462569393462365793,-804819987263749463289554736306107831189989599625469301128372,400541761396386037213106072073629130683892532329147072412553,-2628404172520920920633989906725764737728146462827993323963,22577351407839911608826471640904236808862968909594508325299] | [-2359906872066705752803341888715581873786251145752968975502395,-396030875663826196401141557531396668981189969784278735631558,489516481675406424460633800298090332555039851619855929916695,-2368596584324260231282111538288562702387031259714029727796237,-493983990969627150133484439352631681516302731393276599559930,-2819443878449042394576156968467710006451788072079098636324873,-1794486349434792363578106494129239615656807438492678328622670,-614265844964413732122667946310837965189004217645747189451661,3328202205610277891659630509594474993770633931563997866901736,-2773227059347182644826987716328661989672525956348547295249760,-259746047427201990044849327322595484016201750250012176247426,-172037145715909003711762367933494602231633798009750493012553] | [[-75712807024127471588,568952420847771942827,-406709154281526617803,-31415739443667472861,97908095378366027683,3976082221289934985,-17840858912859387152,15633430305656856896,-10326933593849045166,3955949989428481174,2422971484290381853,-1520605402827656062],[-223592247577910945607,1544092128462691447521,-1099065190901642671397,-51551285846692598846,237293305466212981045,-67580899923919583175,303238523160006735146,-265719175347286235364,175525410915788143795,-67238715263001615713,-41182899217113252753,25845512198419332061],[-1131576684583751607098,-3320657982698055621171,3126263973100140200270,129900644223731701137,-739802312908221943941,134405732754414671536,-603084539427118791691,528465594711770452768,-349087116296393424208,133725191652716171104,81905061229706740328,-51401875520337688306],[436867715814977966847,1710737276567335670030,-1523664606508205095663,-74871732724065557141,362582704772320441853,-45096618464073706641,202350545759984195501,-177313949395687043245,117127805278269280084,-44868279227469160738,-27481277925114095721,17246665906089042891],[-114006555070635891141,1081840254126997313682,-733629082231536114164,-42572036105101331580,160115362433558208705,-23207667179492579240,104133841505822425290,-91249483087845044221,60276429030438198611,-23090159011749152016,-14142442903147380743,8875496565740955053],[482097155952039060822,-672795904906034316639,378831776007195755688,-693394556373853041103,500184545257894523797,-588468878828222039884,241138082693578963060,-28010812569478727701,1293983687835396486263,-1114495227812762299718,1111457746595407643855,-851311132003828916947],[-4011681006621092419,467549191847002131214,-349362209124234512883,-134136791657503975021,171788945814962738232,-84033618470495928523,20779443183824109261,9008836071367922413,183447286598943181639,-162161097335801524857,233565679345095622559,-138513226042056786189],[-183215702088590880370,1501213205910780157283,-1077431686421609904426,-113703619839786362433,284314876022425552824,-124379282601610900475,341824644815326780018,-283009676814847261346,301915335939415869128,-171432678596370813351,232286063657190073873,-69032077761722256160],[224593107204674863250,-3972214537585246035732,2918566032222470624386,785071842333377677866,-1160563891208055286210,-594261260804869851831,-131978379204583378457,642842555053178355027,-1739268227328662588862,1181523680093637817973,-1405368620195612454368,756574183461675904416],[-153865050317463072073,2241821641016642383311,-1640116437967398699586,-392624942509864463347,612456441819128573096,329729701413587058253,22403755419871113133,-274582206200992995139,803750236143219259998,-551827729868452564329,710767980244245096229,-367195255618586917218],[-164693971478990941710,1028312730184892882736,-727833100642173364387,-4948591670495665434,133254971037004594364,76912472291253752691,91378948729530362565,-62025765745896332269,-34802086791888687123,43030945293595157893,40003795317557784674,39162923335591577907],[2697460952063612138,54793845981222687151,-41766983188533149566,-21614744637315413598,25102784234304169611,60714858480276199729,-272430287849886218940,238722806959781696538,-157692491450124441948,60407438879691651373,36998825120550254256,-23219676228695453823]] | 165923830308 | 2797674825994 | 145391211490 |
| 93 | [229544713809541835016781508755374548285239824638220032773443,529252255466395329421375778044772219890789737088650310019645,695723933153830046959834968229236632229152041387752893803664,193223327939396278363857956855654324663611611200105523510582,547417702463821282439576743447231756171508740725570706964036,435215431734293581913282093387701213041990529939743581308189,226256534199048428766767408100556803062787386503201680152508,526788602898087574172163967820297297168249609257582770585263,740375791998832085120521940793736786607452827349425276025440,173863742971263548349567474050473840436203915412167234139596,550111577553648926861067247265934574092249530755206612079274,603858081719806208264408246699693981368613337880402718611106] | [120174695018346160146873750357083311948700393649607337564805,132441822683147954471130317316193190697711933288657621942630,-1060085712294798186829252918302138627166069146690822632170374,438528741240449099131450239823224395677000367837143883873238,-22911562013933019130147206690140580476684863902488241448199,743054128537671897965090137198987043144919326032041124483340,139209143911351952641136891511735611142238908545171966937356,109482686769220159262578029165721856887496182066568427703757,-804963514997282031290134446567686155561580887056975338133061,400661380030244808618674760059059589068237897083291142530631,-2617196830784652667468305592432058160838122954404461974926,22584771883088662775436155070619452793360893179658083450698] | [-2359801369529682533766857226995505989189094127980606167126285,-395960146909596277268463387619894884842262000462163499316632,489469856789387379508946291434572470464054928414484790649206,-2368462744027831539906428234440382384689204288663801245937126,-493967110776293039240972445362851808845925986715741097058292,-2817612486427848137333424866726226193035100530139578353402711,-1794701800233998711902807209438314475021048199994123351958587,-614060649147412322623518067074489109337753426172186164545015,3326326984907282629779722020731866502551905259028115160103446,-2772778930284483221993260067657979943313123468643710684901423,-259871839884242465947622513335310081964679974984515424520424,-172006239613840898586420257365109309852638001556842926645570] | [[-75696050777888391839,568766357295502281999,-406579351491140951081,-31404193598139009340,97876097026842631203,3972189569040425198,-17822090358167213523,15616764478556566668,-10315950406733657009,3951757892349768016,2420811526086172204,-1519289960657429996],[-223537118621455000376,1543575232081242995778,-1098706306438469522557,-51532236976248021912,237214603043386008146,-67582607638528252159,303224032750626848648,-265702743535615133473,175514994095615744623,-67234984252186316218,-41187549760831558621,25849113068657061531],[-1131222077117441222663,-3319462377012090041137,3125162342971523087638,129854462797076333119,-739541529167053615323,134391307650133519599,-602975761016241887836,528362849521397892329,-349020116164741306894,133700041611537709877,81903449196113890644,-51402220604943636043],[436835931296369546203,1710356689503948042381,-1523359692457953421066,-74852923445286535872,362509321766536640883,-45104730317319900649,202372159063453415959,-177330396244043473964,117138961516122135940,-44872725965300671895,-27488630422931658836,17251735537339742967],[-113929251105057966953,1081428462573770518102,-733362850355100193986,-42556669446743283140,160058367567810211093,-23202801213728610718,104104402019654654441,-91222404041784158812,60258691700846134184,-23083453402030133750,-14140717012468647743,8874647679935325502],[481788760254598661758,-672295064161949540662,378539058685636059828,-693000971231936866823,499929913628328209081,-588199954579452353082,241035450768100111480,-28001080729546531501,1293435351503960682775,-1114041471807776940609,1111234278382011991388,-851153000181462740574],[-4008117878092228384,467387461216317649518,-349246836290712693300,-134112272234999627934,171751189008420411293,-84035950555008376559,20796983711556614209,8993438992962684462,183460941414574979681,-162170869219737270289,233603923740504531617,-138544615723995792256],[-183185618750522509217,1500722581371205530120,-1077085916433392369299,-113648844103978401766,284210647451898671948,-124354017469813737903,341788750352333743005,-282981613322813147839,301847701950837425261,-171384731537261391381,232261545951523277869,-69014357307153806769],[224702343971589278233,-3971037657063302359213,2917695459822355770859,784641887041352994537,-1160073384338839447733,-594351129341956839334,-131910255160628738838,642712548336772654867,-1738626892785546392992,1181051686821115876617,-1405128056401451355585,756406519875900409612],[-153913469226852412543,2241332304022380036247,-1639759340984176590183,-392456786245099696190,612263298191280459682,329799362350908581827,22394254314309283515,-274570774511832112849,803555672120015155571,-551675813646178351229,710729532515329348768,-367158124590636180174],[-164636763650555072629,1027920134483453122318,-727563028462677629582,-4957597061931638737,133214147300434978628,76907585169727021030,91358568813301359398,-62011753398121915519,-34774203981684387913,43005178883146287638,40018148172757363752,39150932563230341326],[2694956490400778279,54772205249312452843,-41750719273936388449,-21605980398912877609,25093181473832547537,60706680352179409862,-272373693091963537693,238669860251414142970,-157657909569960389624,60394424543547790796,36997084089943459751,-23219196466040363227]] | 165876161404 | 2797910241186 | 145296302948 |
| 94 | [229539527655362927941966321034949583621865530807845180852973,529246541974017014040954102933501914292032020144711080910523,695769662375277204693539612366124244749199484237194029074041,193204408984115517661483797717354369459185125673115558139168,547418690337022725424087581520609302768196766913175213758533,435183376093486734732868205827649527281812551214826492974885,226250527484230363393330239182414556273337527213436503698213,526783879587800375394521488615667710573737575172605465945039,740410518689297542355945056965610999631744395049619867405594,173846457118862352033896124190206254011718049925134492018468,550111690209472810291079306647268913533622365149676345730236,603857107323701062721454254322873597102690084547553587496658] | [120276487156367949882398207810920510131850783611935837661499,132458901633631559028651105568631336108244189452192838436674,-1060106825480130838019399167337913503357488077543076972181066,438630906391789081485020017420664157350732870090556348743038,-22890254189638809841437504858155085907420628416199550349046,743175632007487871386745758571990418075034430111514492210986,139286566348547915844540998662299655730516433319195990118127,109509170991447905778625855049800857222781771024022874248714,-805106961866091260574437017141765356561188912117023435407468,400780979336395269063512040893269636498249066698186890097444,-2605984065259864060675235047879256915556287298695934642905,22592191024872344252439575525633722924964464598985003640225] | [-2359695794145238939245338703795585656285604411965585604227882,-395889398747883551854210385828650427073998831423826756322830,489423210178667337453035634439117768956891367131754940933863,-2368328833314189282295684656509680437857728892802831178277321,-493950209523023578269109833996615531494083158744831370058730,-2815782340843099429144496120189190068026835996340968902164470,-1794916965509121146180673262580400684961655608720512111965837,-613855531425174048276157167616352512930860159939596957199939,3324452988311745419504071445926726146136530041673278163061627,-2772330948230195727633303224309836508167056489821637141753222,-259997516312776667350688185014919752743937201110053639706040,-171975320856887266322744373192146395562136702123989297717499] | [[-75679306597780291030,568580424910143782475,-406449640884350966518,-31392655778767639018,97844121260916017166,3968297289649089769,-17803326048344422876,15600102791535083554,-10304969907235156773,3947566797362172632,2418651313794307492,-1517974305523291293],[-223482031675610919439,1543058720108974253863,-1098347690981822347173,-51513202236370500096,237135959463303496695,-67584315604005261858,303209542689962285250,-265686311675318720189,175504577320098921701,-67231253312780277110,-41192199524439159939,25852713911040875743],[-1130867754881591177191,-3318267682632924909268,3124061559136902430616,129808316679174316514,-739280945721857352432,134376886780237806495,-602867011740843959930,528260131126303179719,-348953133655152025711,133674898292075924808,81901835984508931106,-51402565508556218328],[436804180665510079731,1709976375284732840677,-1523055002871610887433,-74834127729337227467,362435992668735369936,-45112840315046815424,202393758953149760207,-177346830331623440640,117150109466110991448,-44877169618037443495,-27495981911836399286,17256804984354364399],[-113852012574118007187,1081016984268068982930,-733096820846203512911,-42541314074607598827,160001415697241536832,-23197937785709427130,104074977226495790339,-91195338351453050126,60240963149408643154,-23076751131777670288,-14138991765832703331,8873799246766789587],[481480646456588377864,-671794769861481118078,378246673566658841183,-692607718614318484831,499675479223581534614,-587931162150481618237,240932853593095809220,-27991339834000446092,1292887273092461953504,-1113587931375737727992,1111010890807777529324,-850994918806851847281],[-4004562759711718302,467225849500696435470,-349131547683333239919,-134087764241184729544,171713455830017678265,-84038271228642601530,20814514421801949856,8978047655263951619,183474570409109849424,-162180621385500656942,233642158485255542024,-138575998441470823645],[-183155555583208127662,1500232313772667551984,-1076740400581223876005,-113594111613351026310,284106497474779441443,-124328765220431491310,341752867377430382080,-282953556476169787706,301780094516876438301,-171336804381753315768,232237032283259087797,-68996639471205030475],[224811452897264539322,-3969861511574320473543,2916825449035944919381,784212290599691877078,-1159583254331841290856,-594440921829981129301,-131842155446390727649,642582564396140484283,-1737985840082469606872,1180579912686298786929,-1404887567115528403467,756238903558781573035],[-153961851405655907710,2240843311734492442083,-1639402503139256764311,-392288761608672355243,612070302004104424082,329869000549201412782,22384754025554900034,-274559338766634377906,803361175230735445144,-551523952639904187812,710691099290177463792,-367121000729171271710],[-164579602622655409634,1027527844399504941206,-727293167089189400318,-4966592497301930915,133173353438822682859,76902700875435701701,91338196531063803106,-61997747412444773552,-34746336452046653875,42979426410896345291,40032494171312369543,39138945990691543330],[2692455214463384157,54750571805324712513,-41734461207812083108,-21597222336281298036,25083584483288143524,60698504687682041374,-272317115055995365553,238616928950917155286,-157623337810975139004,60381414058777404396,36995342685425200487,-23218716687361413148]] | 165828532308 | 2798146435760 | 145201446083 |
| 95 | [229534337110289341470394614447981234167243552139341398862899,529240827744972279083514546347747015597004834159126848567941,695815392507437418092769425589329963554475677057904228641582,193185485621875817569222609413005586333196098528266849800857,547419677291087324525208868577674509115144026538562045461788,435151315213104423180114678736284654618371621451614360161247,226244517429451575451028818532959881655544561586864010680705,526779155135257878695539160634672621951923918293453585027276,740445251565866928629802005642613446665928065356075423380930,173829166107739711462326364348344175734191811092480231079823,550111802381496335061733608316702671888146950247267048779043,603856132607586227571681350582133508492728773534614248167766] | [120378274738628438576656602060255056519913107052140539868718,132475977531843331400539827589727661018438149877169862865974,-1060127936652806819914152848117666345924215866797011042064799,438733065765123183308940989739170643684437835484910937237047,-22868947094865726347031126554880901581182848526013714483455,743297056557446618551531992044364826175973076228655465089868,139363998061141591830426143752874920178343587724500943616192,109535646367225309863968088544268725941156158890565391766828,-805250327922966924965610986454855539113989200668292220547180,400900559321176719341361516083385923980029492991274705306873,-2594765880950510044843644027809913486694894491119286838640,22599608832645124740393982454541170758215998055347592897523] | [-2359590145924111744470235842558463875174849513240003805897187,-395818631184830765450076180984330139161455182911572471791108,489376541848085408799509328171573168053179974495711833734034,-2368194852197186750026078117612391410672988970129382001849803,-493933287212814008402119981841854971993744690072630419143300,-2813953441025169498466073174038545122573732153445408684021510,-1795131845385732181251122185279231308623269484947721690695264,-613650491752258479532999925341835708981062716191538827649466,3322580215157150896577175446103902065624668581332461800278307,-2771883113083236856142796610132463502741606265530514850345020,-260123076766134907381357456971396735917685372623504545614999,-171944389447862256942181041655040678632965072077267397074110] | [[-75662574469216843423,568394623541864428924,-406320022355859656213,-31381125976509548950,97812168054850439262,3964405383255339837,-17784565983800241728,15583445244948918355,-10293992095582557783,3943376704548460418,2416490847697766477,-1516658437545121485],[-223426986691737156502,1542542592110635268450,-1097989344227441735479,-51494181611166660171,237057374659471851702,-67586023821152230990,303195052984963375606,-265669879772964417714,175494160593511855163,-67227522446390332823,-41196848507452043376,25856314725388908759],[-1130513717555126658449,-3317073898530790829413,3122961620640387341447,129762205830137068011,-739020562346388543716,134362470145201084810,-602758291605773085784,528157439531194687185,-348886168770637761633,133649761695434526501,81900221594727468540,-51402910231089881160],[436772463886508162238,1709596333598784713822,-1522750537494250450068,-74815345560917138836,362362717417753442386,-45120948458363858854,202415345438384786021,-177363251667188950730,117161249133958615944,-44881610187840809461,-27503332391186043947,17261874246882093895],[-113774839403475112598,1080605818856024973496,-732830993476270369194,-42525969975973187280,159944506773283291706,-23193076894774889383,104045567122041680967,-91168286012877578498,60223243373512938355,-23070052199998674907,-14137267163165953757,8872951266201911465],[481172814228237832165,-671295021271621646288,377954620194414020662,-692214798154062550596,499421241843884109210,-587662501506261463823,240830291180480785193,-27981589905076172440,1292339452541447744155,-1113134606462447107173,1110787583878547225434,-850836887884259396402],[-4001015640732561725,467064356558142750856,-349016343201473170962,-134063267661933238138,171675746250836685001,-84040580500229371803,20832035317779145092,8962662057922130649,183488173599276336071,-162190353846411571721,233680383580421767222,-138607374193513055407],[-183125512563206822703,1499742402717448684845,-1076395138582247454586,-113539422319903232973,284002426003787269363,-124303525850772071872,341716995893047215959,-282925506278190565643,301712513634258576392,-171288897126282637671,232212522652889761309,-68978924254501515790],[224920434135342243777,-3968686100402411784900,2915955999309732779818,783783052611912446467,-1159093500784486153118,-594530638309280441325,-131774080073899616665,642452603258951178747,-1737345069164440173904,1180108357636244345058,-1404647152343733479288,756071334514854550966],[-154010196892920762308,2240354663766305368007,-1639045924143021674516,-392120868453574514179,611877453093145074030,329938616011580358300,22375254560640841834,-274547898974438888585,803166745472423786246,-551372146844499008120,710652680569310289443,-367083884035565797648],[-164522488341285663648,1027135859581336107906,-727023516279229775704,-4975577987195305464,133132589416974857379,76897819405242083190,91317831883513172170,-61983747788171910507,-34718484197325953075,42953687872033376216,40046833313130062861,39126963618382281030],[2689957121254516911,54728945639805071102,-41718208982543519441,-21588470442471291395,25073993255975273521,60690331487072915503,-272260553743940556978,238564013060135920506,-157588776174349957857,60368407425813647524,36993600907137436892,-23218236892740834146]] | 165780942985 | 2798383409878 | 145106640912 |
| 96 | [229529142174517664590548435725052672159188663975400280958979,529235112779392808012410299292532168379740228001847586409069,695861123550223847267521471095181787292001694873266795693424,193166557852926488600610401188061398795850680369314357686544,547420663326046568581943009486644365679030286953914471144308,435119249096549843025164741047042952114743723925370721024543,226238504034312218926806989622935974511870128669270280980971,526774429540841619538412464233151397328821491809972704265426,740479990625055409174091363915091343184171531239634142762413,173811869938728953121672659177472148812104110474662082399414,550111914069485859722762850849227258926165328306336173855758,603855157571519259623458737842252582368366614943856196863646] | [120480057761985912345291983939754412319712680971200548554127,132493050376946491286032432289618059637091750680270504625603,-1060149045811889310351595957393325727402680024123775996224183,438835219357414723848898222306312732466651285061370054760081,-22847640730522034217243601073473859789201258643651370469206,743418402241272158011147370959903721940519001506619251382315,139441439036824495064242618574369905561326554289177606171848,109562112899918193609808271731999617678449225291165416289367,-805393613220670042030890453122461496197795602082369097142645,401020119990924099115438964400681806203637636077354052711890,-2583542282858244573840324851105314916947119349014284170395,22607025305861294366598169694628393535418969254150735999586] | [-2359484424877046877408117063310025049140059302564181268136379,-395747844226583270647029099207361035714658606599313584373856,489329851802483381508361919284229334181694236938940888678137,-2368060800690685870012676077617104902504368462018119872068677,-493916343848662185045982788420677885289326833978492998172444,-2812125786304203635189619099487687808597295907792486388685886,-1795346439989455150016544034986814543021744026129040234294441,-613445530083207205906552939952709678595214298786704793103232,3320708664776757851356600623207827906480600071156452048896481,-2771435424742490232399645115291679827821017990684536587835405,-260248521297670128705330836235430839482108372755826263244568,-171913445389581557489343483618647996292804792282751148322467] | [[-75645854377633566789,568208953041057127702,-406190495800527981476,-31369604182334532503,97780237382948787310,3960513849998246281,-17765810164941165134,15566791839152000835,-10283016972003192091,3939187613990765396,2414330128079590979,-1515342356842838562],[-223371983621265253898,1542026847651629581116,-1097631265871525003410,-51475175084766984700,236978848565497291314,-67587732290768967133,303180563642568054691,-265653447835108165509,175483743920121179033,-67223791654620449692,-41201496709386233614,25859915511519299898],[-1130159964817454834672,-3315881023677463485610,3121862526527521122008,129716130210135846845,-738760378814742018955,134348057745492635120,-602649600615847503670,528054774740753038367,-348819221514192509486,133624631822710338814,81898606026605145108,-51403254772459065804],[436740780923525969581,1709216564135664998907,-1522446296071327435429,-74796576924748742595,362289495952519414533,-45129054748379365394,202436918528463043371,-177379660259495578259,117172380525383530033,-44886047676870477616,-27510681860338368132,17266943324672116394],[-113697731518899671407,1080194965984301815213,-732565368017068151635,-42510637138138076671,159887640747439504779,-23188218540264287621,104016171701984297358,-91141247022079993516,60205532370543872087,-23063356605699170751,-14135543204394705868,8872103738207215309],[480865263240255249283,-670795817660530959360,377662898113786772784,-691822209484746221078,499167201289726059560,-587393972611672085040,240727763542109902852,-27971830964975419319,1291791889791311613417,-1112681497013589103934,1110564357600101856610,-850678907417906694653],[-3997476510420078987,466902982246875737889,-348901222744662533559,-134038782483146895780,171638060242008527398,-84042878378599125599,20849546402710888926,8947282200584152841,183501751001805187116,-162200066615791292710,233718599027086618150,-138638742979161199880],[-183095489667114475771,1499252847808425307819,-1076050130154028116275,-113484776175703058994,283898432951769730600,-124278299358135734517,341681135901600601243,-282897462732137607495,301644959299690240392,-171241009767272718459,232188017060902721975,-68961211657665483873],[225029287839249966763,-3967511422832694432244,2915087110090993129607,783354172682089740346,-1158604123294764206069,-594620278820215348301,-131706029055133050219,642322664952807657466,-1736704579976287661311,1179637021617887421852,-1404406812091894440607,755903812748612812362],[-154058505727638974962,2239866359731723130531,-1638689603706286226378,-391953106633012369785,611684751294188284677,330008208741177337130,22365755926584497225,-274536455144270821092,802972382842068520848,-551220396254791371165,710614276353238441292,-367046774511185826215],[-164465420752519182106,1026744179677765560015,-726754075790686408221,-4984553542187699415,133091855199754354059,76892940756008726172,91297474871339459059,-61969754524606930303,-34690647211865963845,42927963261739186159,40061165598122645806,39114985446706211277],[2687462207781796940,54707326743313306710,-41701962590525321680,-21579724710543918515,25064407785208297129,60682160750638849898,-272204009157743723633,238511112580902345064,-157554224661257417919,60355404645086387148,36991858755222152911,-23217757082260875266]] | 165733393400 | 2798621163700 | 145011887452 |
| 97 | [229523942848244621804572446657791390321058346326535542195682,529229397077410320381348541558669124181369016201414081392984,695906855503549611920734530774745978256528636836745438951388,193147625677516972249147711655063513121922580891920539596232,547421648441931985610224678146916329477626258902518005784733,435087177747223873176140781514377288394370037921579243049936,226232487298412978640097360159989632374141892212733459772498,526769702804932988237649531733248030076316186560218321324407,740514735863380424544893966314924699725392587058360646482131,173794568612663130323449701867757612434829174683738195929235,550112025273207958529886184495857348758432576590569035297327,603854182215557739222744330705260949960722345336825002621877] | [120581836223299121046860494807946268539614418721769875298663,132510120168104523531770738791227368159983966553362052401565,-1060170152956441696087049673108838543673747992789006469055569,438937367165627620496718949494822534386225324345583883060091,-22826335097515869647961990935305305135843873354583441372737,743539669112659608007233899609598152884642870122146447995518,139518889263293560097448150068391170461803050956905578363846,109588570592890417789187837258067826677425154800751117369482,-805536817811932863379204921303645160623898274344446559851825,401139661351967985498778006321074606207754465502022007174435,-2572313275982419637839068054935391682322440806695478002199,22614440443975264751379414848043138356527843365507811909611] | [-2359378631014799415538181431651562463428248018148993362366614,-395677037879289025830370796949187005482735077245055207001140,489283140046705719578229135166717000881717864405605421950733,-2367926678808557200542404852764850285961956568127427322175769,-493899379433568576885736222671970321135202123696652398949508,-2810299376010121039534129095644216973205470648792267302667327,-1795560749445963878650505044622312924004601390530465176904977,-613240646372543981884959500658992497431590264598597499982357,3318838336503601076601964037251102279813225858106970216856146,-2770987883106806729725156965926594719342568075778576520281320,-260373849960757755394975160887964849817899164880501068786380,-171882488684862391317494374075131318350013068816653600200120] | [[-75629146308487781520,568023413258339284985,-406061061113374576494,-31358090387225963817,97748329219552514773,3956622690016540478,-17747058592170962019,15550142574495684674,-10272044536722713727,3934999525770591448,2412169155222885813,-1514026063536396951],[-223317022415699705582,1541511486298013002584,-1097273455610725335885,-51456182641325767277,236900381115085659580,-67589441013653468895,303166074669701876468,-265637015868294433899,175473327304185990159,-67220060939071729345,-41206144129757793438,25863516269250193765],[-1129806496348463950320,-3314689057046260743755,3120764275845278573405,129670089779401642530,-738500394901351412502,134333649581577473284,-602540938775855662635,527952136759631155019,-348752291888792108601,133599508674993310487,81896989279977638366,-51403599132578208816],[436709131740779158057,1708837066585400845754,-1522142278348678823759,-74777821805577433954,362216328212053413471,-45137159186200596307,202458478232682075727,-177396056117292465005,117183503646100006380,-44890482087284529985,-27518030318651195700,17272012217473615104],[-113620688846273150678,1079784425300092897409,-732299944240706695973,-42495315548419378837,159830817571286991589,-23183362721516342970,103986790962011745688,-91114221375078945288,60187830137883943496,-23056664347884293626,-14133819889445167149,8871256662749185315],[480557993163826603570,-670297158297533951667,377371506870396147477,-691429952240458256572,498913357361857589148,-587125575431522454683,240625270689778271853,-27962063035865942580,1291244584782293659801,-1112228602974729665376,1110341211978160119441,-850520977411973269880],[-3993945358051896647,466741726425329024297,-348786186212584120779,-134014308690755165199,171600397774713151981,-84045164872581955044,20867047679823517028,8931908082893481663,183515302633429316843,-162209759706962461549,233756804826343783958,-138670104797461493616],[-183065486871563690050,1498763648649066600789,-1075705375014552060971,-113430173132887457418,283794518231702330056,-124253085739815098000,341645287405492756865,-282869425841261797519,301577431509858609249,-171193142301134262074,232163515507780567988,-68943501681315794398],[225138014162201616800,-3966337478151291385497,2914218780827777351139,782925650414854731545,-1158115121461229443308,-594709843403169151220,-131638002402016142559,642192749505246517310,-1736064372462663728082,1179165904578040310884,-1404166546365777231937,755736338264508212626],[-154106777948747433703,2239378399245227502255,-1638333541540296963154,-391785476000405851202,611492196443260753509,330077778741141337192,22356258130387786184,-274525007285141444946,802778087336602794802,-551068700865569552602,710575886642462321269,-367009672157389901013],[-164408399802508803316,1026352804338142410139,-726484845381812817045,-4993519172842242389,133051150752079618217,76888064924598469777,91277125495227178357,-61955767621050043453,-34662825490003599643,42902252575189362956,40075491026207252993,39103011476063556552],[2684970471057369344,54685715106423344084,-41685722024163431156,-21570985133570664944,25054828064311598768,60673992478664662218,-272147481299335259367,238458227515035077996,-157519683272861410111,60342405717022207624,36990116229821355984,-23217277256003804033]] | 165685883517 | 2798859697390 | 144917185722 |
| 98 | [229518739131667073108261000594706598923586946217934248807481,529223680639156571822950391971997381357056344287620045433874,695952588367327791357303627672904668231718098045031413384043,193128689095896840962489434686596472808364731542974091388155,547422632638775142797337580147118275982520136607679259832906,435055101168525076926022678756102434630171495425417748091692,226226467221355070008968947512467532770260283909946566457888,526764974927913230043692797470029603690537987443244812159821,740549487277361689381292033231541088347702529243115160536486,173777262130375023392089492104527509542016761541096252224419,550112135992429421345488861212703436015759821589192935822447,603853206539759270247842499430828498149982153458698014269619] | [120683610119427278677443037203904403228888197255813809484232,132527186904481178244175742533806472546291281478435345738743,-1060191258085527572908479723974613877038498201269634845427129,439039509186726389162617225193781141508466116718519756069578,-22805030196755239347936591633858607224536793108397363621032,743660857225275176758376089438689505207038560510594493386507,139596348728251143738637632071751184176607048124432639739093,109615019449503881090780005430128358824859912175227150763619,-805679941749458865038400041718250017186586640841776405815788,401259183410634591648274765869448710232237878665448027254194,-2561078865320084296732051065087696809467502468174783437519,22621854246441569074349588051619492639128813382328050354828] | [-2359272764348133582627225580981522507327978521150044993828036,-395606212149098593674077298428524585359412022705617818156835,489236406585599561630891828851379149133588568929531747934808,-2367792486564679927304645041890562520243764453688300077337323,-493882393970536264942057674866503031826177975555044347468055,-2808474209472616666447229383501937481074373145993306768351404,-1795774773880982362581892960882041997915279234414721896668540,-613035840574774872493104501776788381933982705812064387111363,3316969229670493210771793805098425047127598103337884579847294,-2770540488075004787064262577740390419236865987506036874408951,-260499062808795545150799900092013165310693242617609002029275,-171851519336523517373631147234250131793680471788538734849073] | [[-75612450247258569840,567838004044552385851,-405931718189575452665,-31346584582180772329,97716443539041566441,3952731903448615057,-17728311265890680505,15533497451328752414,-10261074789965101946,3930812439968813548,2410007929410818739,-1512709557745787500],[-223262103026617820436,1540996507616492389725,-1096915913142150932010,-51437204265021067854,236821972242042239622,-67591149990601928083,303151586073278028561,-265620583879056237671,175462910749957857143,-67216330301342412093,-41210790768082823827,25867116998399740283],[-1129453311828522423877,-3313497997612039759779,3119666867642063311620,129624084498225062850,-738240610380988527946,134319245653916357733,-602432306090556272754,527849525592454303684,-348685379897394273434,133574392253366526745,81895371354680661327,-51403943311361742058],[436677516302536764025,1708457840638484343425,-1521838484072522533325,-74759080188171487717,362143214135466965336,-45145261772933739918,202480024560332421378,-177412439249322321683,117194618501818070495,-44894913421239423101,-27525377765482399166,17277080925035771531],[-113543711311587888169,1079374196451120679406,-732034721919637642730,-42480005194153253478,159774037196475217653,-23178509437869209267,103957424897808279367,-91087209067889495682,60170136672913305942,-23049975425558294782,-14132097218243445743,8870410039794265719],[480251003670614769086,-669799042453118406266,377080446010593694865,-691038026055798124500,498659709861288538122,-586857309930550533647,240522812635221359565,-27952286139881584404,1290697537454480947771,-1111775924291317000186,1110118147018378740661,-850363097870596944731],[-3990422172917932946,466580588952150329287,-348671233505073189281,-133989846270715166844,171562758820179256735,-84047439991007590276,20884539152346998306,8916539704490120401,183528828510883770905,-162219433133249055877,233795000979297212731,-138701459647467684323],[-183035504153223717977,1498274804843433430548,-1075360872882225886501,-113375613143662172832,283690681756688266351,-124227884993095164953,341609450407111788517,-282841395608802795635,301509930261431685299,-171145294724265347345,232139017994001080874,-68925794326067951412],[225246613257197790491,-3965164265645328548158,2913351010968912972525,782497485415393348732,-1157626494882998670762,-594799332098547754221,-131570000126421575075,642062856943738126647,-1735424446568042592158,1178695006463393075882,-1403926355171085995292,755568911066951067299],[-154155013595128011285,2238890781921876621114,-1637977737356731252278,-391617976409388230025,611299788376629556267,330147326014638373266,22346761179037182829,-274513555406048138369,802583858952904677107,-550917060671581636259,710537511437472136580,-366972576975529053967],[-164351425437486711146,1025961733212344954036,-726215824811227702892,-5002474889709275620,133010476038924580761,76883191907874437840,91256783755855374886,-61941787076798073877,-34635019026069033870,42876555807553298204,40089809597305942802,39091041706851110846],[2682481908097895370,54664110719723228175,-41669487275875085101,-21562251704633421390,25045254086619568874,60665826671433173734,-272090970170631365136,238405357864339534101,-157485152010317159727,60329410642044416456,36988373331077077014,-23216797414051906438]] | 165638413301 | 2799099011110 | 144822535738 |
| 99 | [229513531024982013971028199631054714203626151433059896842827,529217963464763354037306012612437639794783684016204249690737,695998322141471424493099525355186761815466914249964798461766,193109748108315798116618591537730774048303234669501187635806,547423615916607646496326354419272033123024872181071456308541,435023019363849703199943405003145677588997362059442200712969,226220443802740238816181469641992948477225678843661090092070,526760245910163445227573564241982408811495255354603645857633,740584244863521191163874916473812455059802701680083664370212,173759950492697139853218767659855409068713331335286597299455,550112246226917253539260326477959927661598065593178564454939,603852230544181480104158955941621931308640733802802531947461] | [120785379447230063765117772856906755438304044245758248108942,132544250585240470901755956516403611351610979127814966081638,-1060212361198210745751840682823687968721012058139811110786956,439141645417676144647267294259770693696433696744757998030584,-22783726029148020426113343018310983270238881098020895129624,743781966632756152826564913247339484447450644803746332369720,139673817419405027210712544879566742362031694896971726599056,109641459473118519358955095349073214128783968979485516270609,-805822985085922737911875627653900502138796502875168232629845,401378686173245765372397868647158046379454707194420611651276,-2549839055865983719908320108108704156439886135235324490237,22629266712714862140630413012122569257231481489866912512283] | [-2359166824887822745502067613104781639323030858031863038046321,-395535367042165139634423166568432806258111470908021502291418,489189651424014719495030480805414442384723987683735685268872,-2367658223972941859419435775837023107181456907245524951123479,-493865387462570941627125633913102498517611430937920543794482,-2806650286021163065521800817245909978173017089073450022162173,-1795988513420284443253760660128692791469297913903131905203976,-612831112644388398499843340154585040050040484642880409180185,3315101343610026576835467866679876332471192238774636167619876,-2770093239545870725386021355542976894791691190037879835690423,-260624159895203441875570177764633996523356937875430720698251,-171820537347385229483174421382295892946551292787461777207723] | [[-75595766179446735105,567652725250761574306,-405802466924463703597,-31335086758209417349,97684580315834306265,3948841490432524661,-17709568186498653230,15516856469997420402,-10250107731952664471,3926626356665678995,2407846450926620396,-1511392839591037451],[-223207225405669585885,1540481911174424425304,-1096558638163364152215,-51418239940054668186,236743621880271567241,-67592859222408731863,303137097860197346907,-265604151873915149657,175452494261680829261,-67212599743027880311,-41215436623877464047,25870717698786094724],[-1129100410938477947675,-3312307844351194094343,3118570300967705089205,129578114326956222098,-737981025028762704210,134304845962965796750,-602323702564678355333,527746941243820142305,-348618485542938624154,133549282558906220905,81893752250549962520,-51404287308724092713],[436645934573121103746,1708078885985871648703,-1521534912989456706272,-74740352057322015368,362070153661962823952,-45153362509683911864,202501557520697614761,-177428809664321429141,117205725098243501542,-44899341680889988314,-27532724200189899813,17282149447107765521],[-113466798840946884651,1078964279085635698828,-731769700826653796492,-42464706062694872450,159717299574726162282,-23173658688660474798,103928073505054311102,-91060210096523129553,60152451973009774351,-23043289837724543704,-14130375190715550487,8869563869308860803],[479944294432758671411,-669301469398932828000,376789715081462093060,-690646430565875105155,498406258589287944131,-586589176073423481059,240420389390115102455,-27942500299122312532,1290150747747807933148,-1111323460908681918314,1109895162726352587463,-850205268797873910228],[-3986906944320383291,466419569686201070355,-348556364522117177585,-133965395209011616085,171525143349684192154,-84049703742705383583,20902020823514921498,8901177065010619795,183542328650905690989,-162229086907976361843,233833187487061092240,-138732807528241017819],[-183005541488800388907,1497786315996177239464,-1075016623475875799678,-113321096160301617389,283586923439958196052,-124202697115253341898,341573624908831713046,-282813372037989054658,301442455551058339503,-171097467033051460250,232114524520037234181,-68908089592534109188],[225355085277026126518,-3963991784602932864346,2912483799964002211762,782069677289445499204,-1157138243159750499206,-594888744946779539917,-131502022240169693408,641932987295686719111,-1734784802236721496848,1178224327220513897568,-1403686238513463180591,755401531160310225646],[-154203212705607660287,2238403507377303902107,-1637622190867696473704,-391450607713805731277,611107526930801703857,330216850564851444741,22337265079503737868,-274502099515974403653,802389697687797279000,-550765475667535605536,710499150738747918592,-366935488966946818258],[-164294497603764290022,1025570965950779680966,-725947013837914264416,-5011420703326370941,132969831025318550582,76878321702700045135,91236449653897631812,-61927812891144465695,-34607227814385724634,42850872953994208885,40104121311345688633,39079076139462245533],[2679996515924543890,54642513573815097740,-41653258338088795504,-21553524416824464217,25035685845476585152,60657663329225212922,-272034475773534073917,238352503630607917077,-157450630874771241619,60316419420573050048,36986630059131370346,-23216317556487486931]] | 165590982717 | 2799339105022 | - |

**命题 49.2（全参数覆盖及严格有限界）。** 上述数据满足 $\bigcup_{k=0}^{99}I_k=[\theta_-,\theta_+]$，相邻片仅共用一个端点。在每个完整 $\mathcal T_k$ 上有

$$
\|I-C_kD_xG_\theta(x)\|_\infty\le q_k<1/5,\qquad \|C_kG_\theta(P_k(\theta))\|_\infty\le\eta_k<3/10^{12},\qquad \eta_k+q_k\rho<\rho. \tag{49.5}
$$

全管还满足每个 $M$ 槽 $43/100<r<3/4$、$17/100<b<24/100$、$52/100<D<56/100$，以及 $r_{M2}-r_{M1}>22/100$、$r_{M4}-r_{M3}>29/100$。每个 $k<99$ 的相邻预测差严格小于 $10^{-11}$。

证明。参数恒等式 $\theta_k-h=\theta_{k+1}+h$、$\theta_0+h=\theta_+$、$\theta_{99}-h=\theta_-$ 给覆盖。所有整数输入、取整、乘法、倒数及有限商环运算已由式 (47.2)–(49.4) 指定；逐行代入得到表中 $Q_k,E_k,A_k$，分别严格小于 $2\cdot10^{11},3\cdot10^{12},10^{13}$。以 $V+(0,[-\rho,\rho]^{12})$ 的分量端点代入所述源界与两个差，得到相应严格不等式。故所有 $b,j,t,n$ 的区间倒数合法。由商环系数的链式法则和均值定理，$q_{0k}+hK_k$ 控制全管的 Jacobian 缺陷；沿二次曲线的三阶 Taylor 公式及式 (49.4) 控制预测残差。其余严格自映射不等式由 $3\cdot10^{-12}+(1/5)10^{-9}<10^{-9}$ 得到。这里各区间使用全参数与全修正盒，未只在预测中心求导。∎

## 50. 原精确极限种子与联合零的同一条有守卫曲线

**定义 50.1（固定的精确种子）。** 所引根卷第 14–16 节的源采用其 [固定文本的第 15 节](https://github.com/the-omega-institute/trureturing/blob/e797d4c6511927b143f95498188c318e5d04ef5a/docs/develop/theory/FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md#15-联合零点的完整有理闭盒证书)：$x_0$ 是该节依式 (14.1) 排列的完整十二维有理中心，$C_s=10^{-12}N_s$ 是该节的完整十二阶整数矩阵，$Q_s=\{x:\|x-x_0\|_\infty\le10^{-10}\}$。其有限区间尺度为 $10^{40}$，不是本增补的 $B$。原种子始终指

$$
x_\dagger=\lim_{n\to\infty}x^{(n)},\qquad x^{(0)}=x_0,\quad x^{(n+1)}=x^{(n)}-C_sG_{7/15}(x^{(n)}). \tag{50.1}
$$

该处的全部十二行导数界和中心区间给 $q_s\le300624528/10^{12}$、$\eta_s\le232712/10^{40}$，故 $x_\dagger$ 是 $Q_s$ 内唯一零点，$\|x_\dagger-x_0\|_\infty\le\eta_s/(1-q_s)<2\cdot10^{-30}$。这复用的是原极限及原矩阵，绝非以 $x_0$ 代替根。

由第 49 节首行与该 $x_0$ 的精确有理数据直接相减，有

$$
\|x_0-P_0(7/15)\|_\infty+2\cdot10^{-30}<10^{-11}. \tag{50.2}
$$

令 $\mathcal I=[\widehat v_1-R,\widehat v_1+R]$，$\widehat x=(\widehat v_2,\ldots,\widehat v_{12},\widehat v_{25})$。末行数据和第 48 节中心给

$$
\mathcal I\subset\operatorname{int}I_{99},\qquad \sup_{\theta\in\mathcal I,\ \|x-\widehat x\|_\infty\le R}\|x-P_{99}(\theta)\|_\infty<10^{-11}. \tag{50.3}
$$

式 (50.3) 的有限包含具体按 $\delta=[\widehat v_1-\theta_{99}-R,\widehat v_1-\theta_{99}+R]$、第 49 节末行二次式和式 (48.1) 求端点；对十二分量取端点绝对值最大值。式 (50.2) 使用所引完整中心而无其他隐含输入。

**定理 50.2（特定百片种子连接）。** 存在连续函数 $x:[\theta_-,\theta_+]\to\mathbb R^{12}$，满足 $G_\theta(x(\theta))=0$，在每个 $I_k$ 上属于 $\mathcal T_k$ 且唯一，并有

$$
\|x(\theta)-P_k(\theta)\|_\infty<\frac{15}{4\cdot10^{12}},\qquad x(7/15)=x_\dagger,\qquad x(r_{M1}(v^*))=(b_{M1},D_{M1},r_{M2},b_{M2},D_{M2},r_{M3},b_{M3},D_{M3},r_{M4},b_{M4},D_{M4},Z)(v^*). \tag{50.4}
$$

曲线全程保留严格源、非零整个增益及所指定两对完整目标不同的守卫，并在每个参数的实际第五 $M$ 历史供应 $L_2$。特别令 $\theta^*=r_{M1}(v^*)$，取百片零图的子路径

$$
\theta(s)=(1-s)\frac7{15}+s\theta^*,\qquad \Gamma(s)=(\theta(s),x(\theta(s)))\quad(0\le s\le1). \tag{50.5}
$$

则 $\Gamma(0)=(7/15,x_\dagger)$，$\Gamma(1)$ 恰为 $v^*$ 的十二个 $M$ 槽坐标及共同 $Z$，按 $(\theta,x)$ 排列。其终点由精确零点的 $\theta^*$ 决定，且位于末片内部。

证明。固定 $k,\theta\in I_k$，在修正闭球上用 $e\mapsto e-C_kG_\theta(P_k(\theta)+e)$。命题 49.2 给统一收缩与自映射，故有唯一不动点；与命题 48.2 相同的 Neumann 论证使 $C_k$ 可逆，不动点即为零点，且离预测的距离小于 $(3/10^{12})/(1-1/5)=15/(4\cdot10^{12})$。统一收缩常数及映射对参数的连续性给不动点连续：两参数不动点的差至多为同一点的两映射差除以 $1-1/5$，再加预测的连续差。

在相邻公共端点，一片的零距另一片预测至多为 $15/(4\cdot10^{12})+10^{-11}<\rho$；它同时属于另一闭管，唯一性使两个零相同。于是百片连续零图拼接。式 (50.2) 使原精确种子位于首管；它是同一个 $G_{7/15}$ 的零，故等于图的起点。式 (50.3) 包含整个主盒的 $M$ 投影及其参数区间，故命题 48.2 的精确 $M$ 投影也是末管中的 $G_\theta$ 零；唯一性给式 (50.4) 末项。此处不宣称主盒的非零点都在零图上。全管源守卫给 $g(0)=-100D\ne0$，两个严格 $r$ 差区分所需完整终端对。$\Psi_M=0$ 及第 51 节同一实际纤维递归给每参数的 $L_2$。∎

## 51. 两种私有第五响应、实际第六纤维与父三级失败

**定理 51.1（八个不同完整世界的同父三级失败）。** 在唯一精确零 $v^*$ 处按式 (47.1)–(47.2) 定义八个完整世界 $W_{Fi}$，置 $K_F=\{W_{F1},W_{F2},W_{F3},W_{F4}\}$、$K=K_M\cup K_J$，并取

$$
z^*=100Z(v^*),\quad Y^*=100Y_1^M(v^*)=100Y_1^J(v^*),\quad p_F^*=100p_1^F(v^*),\quad H_4^*=(0,J,24,M,48,J,z^*,M,Y^*),\quad H_{5F}^*=(H_4^*,F,p_F^*). \tag{51.1}
$$

八个世界两两不同且严格合法，$L_2(K_F,H_{5F}^*)$ 对 $F=M,J$ 同时成立，从而 $L_3(K,H_4^*)$。所有世界在动作选择前即固定；每个被服务字面前缀和被选实际后继都满足至少两个不同完整目标的停止守卫。

下面区间端点单位为 $10^{-6}$，均由第 48 节整个 $Q$ 及式 (48.1) 给出；$FE$ 行依次表示实际第六响应 $v_{FE}$、最终 $J$ 响应 $f_{FEJ}$、最终 $M$ 响应 $f_{FEM}$。当 $E=M$ 时检查该臂世界 $1,2$ 的三个表达式，当 $E=J$ 时检查世界 $3,4$；$Y,p_F$ 检查该臂全部四个表达式。

| 精确物理响应 | 包含 |
| --- | --- |
| $z$ | [60385174,60385175] |
| $Y$ | [61126831,61126832] |
| $p_M$ | [63554543,63554544] |
| $p_J$ | [61721419,61721420] |
| $MM$ | [54006672,54006673]; [50000493,50000494]; [48862200,48862201] |
| $MJ$ | [53169144,53169145]; [49619440,49619441]; [48647721,48647722] |
| $JM$ | [53824723,53824724]; [46754318,46754319]; [44922637,44922638] |
| $JJ$ | [53782728,53782729]; [46945664,46945665]; [45268512,45268513] |

证明。每个源满足 $bc=r(1-r)$、迹一及秩一，且严格正源坐标由第 48 节给出；$g(0)=-100D<0$ 保证整个次数至多三的增益非零。八个 $D$ 两两相隔大于 $1/50000$，故完整三元组两两不同。四节点插值和实际左乘表给每世界的前四读 $0,24,48,z^*$。$\Psi_M=\Psi_J=0$ 使各臂四世界的 $Y,p_F$ 分别相同；共同 $Z$ 与 $H$ 最后一行把两臂联到同一个字面 $H_4^*$。表中的窄区间不负责证明相等，相等完全来自联合零方程。

对每个 $F$，定义 $v_{FM}=100V_{M1}^F$、$v_{FJ}=100V_{J3}^F$，所有表达式均在 $v^*$ 取值。令实际第六纤维

$$
B_{FE}=K_F\cap\mathcal F(H_{5F}^*,E,v_{FE}),\qquad T_{FM}=\{W_{F1},W_{F2}\},\quad T_{FJ}=\{W_{F3},W_{F4}\}. \tag{51.2}
$$

$\Psi_F$ 的第 $3,4,5$ 行使 $T_{FM}\subseteq B_{FM}$，并使该对两种最终响应分别相同；第 $8,9,10$ 行同样供应 $T_{FJ}\subseteq B_{FJ}$ 及其两种最终共同响应。对每个 $G\in\{J,M\}$ 令 $f_{FEG}$ 为这一对的相应物理响应，则

$$
T_{FE}\subseteq B_{FE}\cap\mathcal F(H_{5F}^*,E,v_{FE},G,f_{FEG}),\qquad |T_{FE}|=2. \tag{51.3}
$$

所以每个所选终叶有 $L_0$，每个实际 $B_{FE}$ 有 $L_1$。$K_F$ 含四个不同世界，且为两种第六动作各供应一个实际 $L_1$ 纤维，故 $L_2(K_F,H_{5F}^*)$。最后 $K\cap\mathcal F(H_4^*,F,p_F^*)\supseteq K_F$；按失败递归的包含单调性，各实际第五纤维仍有 $L_2$，$|K|=8$ 遂给 $L_3(K,H_4^*)$。这逐项验证的是实际纤维，不要求这些纤维恰为指定对或指定四世界，也未从非终端失败族抽取终端对。相同世界对供应两种最终动作只是本构造的性质，不给一般模型增设配对限制。

在共同父以前被服务的字面前缀全部保留八世界；选定第五响应后至少保留对应四世界，第六及最终响应后至少保留对应二世界。因此停止不能提前识别唯一完整目标。对确定性历史依赖策略，无论第五选 $M$ 或 $J$，均有该臂的实际响应；无论随后第六与最终如何选择，式 (51.2)–(51.3) 仍给一个合法响应和不同完整目标对。互择读数从未当作同一轨迹的额外读取。∎

**命题 51.2（复用关系与结论边界）。** 本增补的 `repo-derived` 内容为式 (47.3) 指定的同时八世界共同父零点及式 (49.1)–(50.4) 指定的有限有守卫种子连接。根卷第 21 节、定理 21.3 的全实父二世界第五 $J$ 分类是既有结果，不作为本增补的新分类或直接基数消费者；本构造不要求或主张由根卷第 28–29 节建立通向本零点的桥梁。第 31 节的整个比例增益第五 $M$ 障碍、第 34 节的非负第六响应排除、第 38 节的四数据饱和邻域、第 40–41 节的第六 $J$ 方向秩及第六 $M$ 反例、第 42–46 节的两个临界邻域零一二分类与末响应单射，以及原精确 $M$ 种子、源图、插值、实际响应递归、区间包含、收缩及 Neumann 工具均按原适用范围复用。这里不提出外部原创性断言。

证明。式 (47.3) 新增的承重约束是两臂共享 $Z,Y$ 的同时实现，而非重述二世界分类；定理 50.2 只把这个零点的 $M$ 支持接到原精确极限种子。先前关于原种子四世界自身第五 $J$ 分离的结论仍针对原种子及原支持，不适用于改变父后的八世界并集。定理 51.1 服务的是一个指定 $H_4^*$ 及其所选后继；它既没有供应更早祖先的相反动作实际失败纤维，也不能强迫任意原根策略抵达该父。因此完整原根递归与可达支持、原根八读与九读二择、九读上界仍未解决。百片仅覆盖式 (49.1) 的有限参数区间，不分类整个连通分量或所有共同父。本文为普通数学证明及精确有理证书，不含 Lean 核验结论。∎

## 追加锚（本行以下为增补区）
