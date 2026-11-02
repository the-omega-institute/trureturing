# 四路径全记录恢复界续卷 I：成对能量与原生产者证书

## 28. 成对能量证书及完整径向边界上的剩余命题

**定义 28.1（两对坐标的能量）。** 承接[源卷第 21–27 节](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md)，固定其原记录、普通转置 $E^{\mathsf T}$、原生产者量 $g,\rho$，以及定义 23.1 的 $\mathcal W,A,B,P,Q,u,v,G,r$。常数仍为

$$
h=\frac1{\sqrt2},\quad c=\cos\frac\pi8,\quad s=\sin\frac\pi8,
\qquad d=2(h+c),\quad e=2(h+s),
$$

且 $\kappa$ 是源卷定理 21.3 的较小正根，$0<\kappa<1/25$。对实际共享反馈 $U\in U(4)$，只取

$$
w=\operatorname{diag}(UU_+^\dagger),\qquad
n_{12}(w)=|w_1|^2+|w_2|^2,\quad
n_{34}(w)=|w_3|^2+|w_4|^2.
\tag{28.1}
$$

对一般 $w\in\mathcal W$ 使用同样定义。置

$$
L=2+4(c-s),\qquad C=2+4s,\qquad
H(a,b)=C-\frac{La}{L-b}.
\tag{28.2}
$$

下文的 $H$ 是标量函数，区别于源卷的证书矩阵 $H_0$。由 $0\le n_{12},n_{34}\le2$ 及 $c>s$，

$$
L-n_{34}\ge L-2=4(c-s)>0.
\tag{28.3}
$$

故此函数在所用的整个闭方形 $[0,2]^2$ 上均有定义。$m$ 与 $\mathcal B_{\mathcal O}$ 分别沿用源卷 (27.1)、(27.13)，不限制为全单位模坐标环面。所有这些能量和证书条件均在一个共同标量相位 $w\mapsto\lambda w$、$|\lambda|=1$ 下不变。

**定理 28.2（立即作用于原效应的成对能量证书）。** 对每个实际 $U\in U(4)$、每个归一化效应 $E\in\operatorname{Dens}_2$（包括奇异和混合效应），以及每个实数 $\gamma\ge0$，有

$$
\boxed{
g(E,U)-\gamma\rho(E,U)
\ge H(n_{12},n_{34})-\gamma(9-A-B)
   +\gamma\bigl(1-\operatorname{Tr}(E^2)\bigr).
}
\tag{28.4}
$$

这里全部右端读数均来自 (28.1) 中同一个实际 $U$。因此

$$
H(n_{12}(w),n_{34}(w))\ge\kappa(9-A(w)-B(w))
\tag{28.5}
$$

足以保证该 $w$ 的每个实际酉提升及其每个归一化效应满足原端点 $g\ge\kappa\rho$。

**证明。** 固定同一个 $w$ 和任意总体 $p\in[0,1]$，记

$$
X(p)=2c^2p+2s^2(1-p).
\tag{28.6}
$$

取复数 $\alpha,\beta$ 使 $|\alpha|^2=p$、$|\beta|^2=1-p$。源卷 (23.2) 给出精确展开

$$
\alpha P+\beta Q
=h(\alpha+\beta)w_1+h(\alpha-\beta)w_2
 +(c\alpha+is\beta)w_3+(c\alpha-is\beta)w_4.
\tag{28.7}
$$

分别对前后两对坐标应用复 Cauchy–Schwarz，再用三角不等式。由于

$$
\begin{aligned}
|h(\alpha+\beta)|^2+|h(\alpha-\beta)|^2&=1,\\
|c\alpha+is\beta|^2+|c\alpha-is\beta|^2&=X(p),
\end{aligned}
$$

得到

$$
|\alpha P+\beta Q|
\le\sqrt{n_{12}}+\sqrt{n_{34}X(p)}.
\tag{28.8}
$$

可选 $\alpha=\sqrt p$ 并选 $\beta$ 的相对相位，使左端等于 $u\sqrt p+v\sqrt{1-p}$；当一个幅度或一个总体为零时，此等式仍可达到。于是 (28.8) 对源卷已经消去效应相对相位的幅度和成立。它同时使用同一个 $w$ 的两对能量，不要求两个 Cauchy–Schwarz 等号同时可达。

半角恒等式 $c^2-s^2=h$、$2cs=h$ 蕴含

$$
d^2-e^2=2L(c^2-s^2),\qquad e^2=C+2Ls^2,
$$

故

$$
d^2p+e^2(1-p)=C+LX(p).
\tag{28.9}
$$

结合 (28.8) 与源卷 (23.3)，在同一个总体上完成平方，得到

$$
\begin{aligned}
G(w,p)
&\ge C+LX(p)-\bigl(\sqrt{n_{12}}+
                         \sqrt{n_{34}X(p)}\bigr)^2\\
&=H(n_{12},n_{34})
 +(L-n_{34})\left(\sqrt{X(p)}-
                \frac{\sqrt{n_{12}n_{34}}}{L-n_{34}}\right)^2\\
&\ge H(n_{12},n_{34}).
\end{aligned}
\tag{28.10}
$$

分母的正性由 (28.3) 保证，包括任一对能量为零的情形。这一步把平方的零点放宽到整个实轴，仅用于下界，没有断言该点对应的总体或原反馈可达。

现在对原效应取源卷的实际总体 $p=b_+^\dagger E^{\mathsf T}b_+$ 和 $\epsilon(E)=1-\operatorname{Tr}(E^2)\ge0$。源卷 (23.14) 与 (27.11) 分别给出

$$
g-\gamma\rho\ge G(w,p)-\gamma r(w,p)+\gamma\epsilon(E),
\qquad r(w,p)\le9-A-B.
\tag{28.11}
$$

因 $\gamma\ge0$，代入 (28.10) 即得 (28.4)。两个距离分支只在它们的联合最小值 $r$ 中出现；取平均是对该最小值的上界，未另选效果符号或反馈符号。证明没有逆效应、除以幅度或除以迹的步骤，故覆盖全部总体、奇异及混合效应，以及同一对角数据的任意实际非对角提升。取 $\gamma=\kappa$ 得 (28.5) 的结论。$\square$

本定理的数学来源为源卷的精确原效应桥及 (28.7)–(28.10) 的本仓推导（`repo-derived`）；复 Cauchy–Schwarz 和完成平方是标准中间工具。

**推论 28.3（一个严格的有理截面）。** 对每个满足

$$
A(w)+B(w)>4,\qquad n_{12}(w)\le\frac{17}{10}
\tag{28.12}
$$

的实际反馈及每个归一化效应，有

$$
g(E,U)-\frac{\rho(E,U)}{25}
>\frac1{20}+\frac{1-\operatorname{Tr}(E^2)}{25}.
\tag{28.13}
$$

特别地，原 $\kappa$ 端点严格成立；在 $\mathcal B_{\mathcal O}$ 内这给出新的统一证书域。$17/10$ 仅是充分截面，不是最优性断言。

**证明。** 函数 $H(a,b)$ 关于 $a,b$ 均单调不增，故

$$
H(n_{12},n_{34})\ge C-\frac{17L}{10(L-2)}.
$$

源卷 (22.13) 的有理半角夹逼给出

$$
C>\frac{4413}{1250},\qquad L>\frac{10411}{2500}>2.
$$

而 $x\mapsto-17x/[10(x-2)]$ 在 $x>2$ 上严格递增。因此

$$
\begin{aligned}
H(n_{12},n_{34})
&>\frac{4413}{1250}
 -\frac{17}{10}\frac{10411/2500}{10411/2500-2}
 =\frac{877684}{3381875}\\
&=\frac14+\frac{128861}{13527500}>\frac14.
\end{aligned}
\tag{28.14}
$$

在 (28.4) 中取 $\gamma=1/25$。由 $9-A-B<5$，右端严格大于 $1/4-1/5+\epsilon(E)/25$，即 (28.13)。又 $\rho\ge0$、$0<\kappa<1/25$，所以 $g-\kappa\rho\ge g-\rho/25$。同样由 $5\kappa<1/5$ 可知 (28.12) 蕴含 (28.5)，且对所有总体有 $G-\kappa r>1/20$。源卷定理 23.4 因而给出 $\nu_\kappa(w)>1/20$。$\square$

**命题 28.4（三种边界中的实际新增范围）。** 置

$$
\zeta=e^{i\pi/4},\quad r_0=\sqrt{\frac{17}{20}},\quad
q=\frac{999}{1000},\quad
D_0=\operatorname{diag}(1,i,\bar\zeta,\zeta).
$$

下列三个数据均有实际非对角共享酉反馈实现，并且均属于 $\mathcal B_{\mathcal O}$ 且满足 (28.12)：

$$
\begin{aligned}
w_*&=(r_0,ir_0,\bar\zeta,\zeta),\\
w_c&=(r_0,ir_0,\bar\zeta,q\zeta),\\
w_i&=(23/25,(461/500)i,q\bar\zeta,q\zeta).
\end{aligned}
\tag{28.15}
$$

其中 $w_c$ 仅坐标饱和，$w_i$ 仅模长不平衡饱和，$w_*$ 位于二者交叠。每个数据的任意实际提升对所有归一化效应均满足 (28.13)。

**证明。** 对非负实数 $a,b,t,u$ 记

$$
w(a,b,t,u)=(a,ib,t\bar\zeta,u\zeta),\qquad
F(a,b,t,u)=(a+h(t+u))^2+(b+h(u-t))^2.
\tag{28.16}
$$

直接计算两条原迹和：

$$
\begin{aligned}
w_1+w_2+w_3+w_4&=a+h(t+u)+i(b+h(u-t)),\\
w_1-w_2+i(w_3-w_4)&=a+h(t+u)-i(b+h(u-t)).
\end{aligned}
$$

所以 $A=B=\sqrt F$。令 $\Delta(w)=\sum_j|w_j|-2\min_j|w_j|$，得到精确读数

| 数据 | $n_{12}$ | $n_{34}$ | $\max_j|w_j|$ | $\Delta$ |
| --- | --- | --- | --- | --- |
| $w_*$ | $17/10$ | $2$ | $1$ | $2$ |
| $w_c$ | $17/10$ | $1998001/1000000$ | $1$ | $1999/1000$ |
| $w_i$ | $424121/250000$ | $998001/500000$ | $q<1$ | $2$ |

特别地，$N(w_*):=n_{12}(w_*)+n_{34}(w_*)=37/10$，且

$$
A(w_*)=B(w_*)=
\sqrt{\frac{37}{10}+2\sqrt{\frac{17}{10}}}.
\tag{28.17}
$$

三例以及下文的残余例均满足 $23/25\le a,b\le1$、$q\le t,u\le1$、$|u-t|\le1/1000$。使用 $7/10<h<3/4$，有

$$
a+h(t+u)>\frac{23}{25}+\frac75q>2,
\qquad a+h(t+u)<\frac52,\qquad
|b+h(u-t)|<\frac54.
$$

因此 $2<A=B<\sqrt{125/16}<3$。这同时排除了源卷的两个已证迹帽 $A\ge2+\sqrt{8/3}$、$B\ge23/6$ 及迹三角 $A+B\le4$。表中各行又给出 $m=1$，且 $424121/250000<17/10$。这些例子不在源卷 (27.8) 的径向内域证书中：该处左端为零，而右端 $\kappa(9-A-B)>0$。

三例均有 $H(n_{12},n_{34})-\kappa(9-A-B)>1/20$。由连续性，每例在其对应边界层中都有非空相对开邻域，保留全部严格迹排除条件并满足 (28.5)；故新增范围不限于三个孤立数据。

以下给出具体酉实现。对 $w_*$，取

$$
R_{\rm pair}=
\begin{pmatrix}
r_0&\sqrt{3/20}&0&0\\
-\sqrt{3/20}&r_0&0&0\\
0&0&1&0\\0&0&0&1
\end{pmatrix},\qquad U_*=D_0R_{\rm pair}U_+.
\tag{28.18}
$$

这个实旋转的两行范数均为一且正交，所以 $U_*$ 是实际非对角酉矩阵，并有所需对角。

对 $w_c$，在坐标 $(1,2,4)$ 上令

$$
\lambda=\frac{2r_0+q-1}{2},\qquad
x=\left(\sqrt{\frac{r_0-\lambda}{1-\lambda}},
         \sqrt{\frac{r_0-\lambda}{1-\lambda}},
         \sqrt{\frac{q-\lambda}{1-\lambda}}\right)^{\mathsf T}.
$$

由 $23/25<r_0<q<1$ 可知 $0<\lambda<1$、$r_0-\lambda=(1-q)/2>0$、$q-\lambda>0$，且 $x^{\mathsf T}x=1$。记 $K_x y=x\times y$，并置

$$
R_c^{(3)}=\lambda I_3+(1-\lambda)xx^{\mathsf T}
                  +\sqrt{1-\lambda^2}K_x.
\tag{28.19}
$$

恒等式 $K_x^{\mathsf T}=-K_x$、$K_xx=0$、$K_x^2=xx^{\mathsf T}-I_3$ 直接给出 $R_c^{(3)}(R_c^{(3)})^{\mathsf T}=I_3$；其对角为 $(r_0,r_0,q)$。将它嵌入坐标 $(1,2,4)$，并固定坐标 $3$，得到 $R_c\in O(4)$，于是 $U_c=D_0R_cU_+$ 实现 $w_c$。

对 $w_i$，令 $a=23/25$、$b=461/500$，并取

$$
v=\left(\sqrt{\frac{1+a}{2}},\sqrt{\frac{1-b}{2}},
         \sqrt{\frac{1-q}{2}},\sqrt{\frac{1-q}{2}}\right)^{\mathsf T},
\quad S=\operatorname{diag}(-1,1,1,1),\quad
R_i=S(I_4-2vv^{\mathsf T}).
\tag{28.20}
$$

由 $b+2q-a=2$ 得 $v^{\mathsf T}v=1$，所以 $I_4-2vv^{\mathsf T}$ 是正交反射，$R_i$ 正交且对角恰为 $(a,b,q,q)$。故 $U_i=D_0R_iU_+$ 是所需实际提升。后两例的实正交矩阵有模小于一的对角元，行范数强制存在非零非对角元；左右乘对角酉矩阵 $D_0,U_+$ 不会消去这些元。

可实现性的一般来源是 Thompson 的奇异值与对角元定理，见 Jasper–Loreaux–Weiss，[*Thompson's theorem for compact operators and diagonals of unitary operators*, arXiv:1602.08435v1，定理 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3)。该定理针对指定复对角和指定奇异值；取维数四、四个奇异值全为一，条件正是 $|w_j|\le1$、$\Delta(w)\le2$，所得方阵即酉矩阵。这是源卷定理 23.2 使用的成熟中间工具；上述各例另由 (28.18)–(28.20) 给出实际矩阵。它们的边界位置及原生产者严格结论是 (28.10)–(28.17) 的本仓应用（`repo-derived`）。$\square$

**定理 28.5（保持原端点等价的剩余义务）。** 定义

$$
\mathcal R_H=
\left\{z\in\mathcal B_{\mathcal O}:
 H(n_{12}(z),n_{34}(z))<\kappa(9-A(z)-B(z))\right\}.
\tag{28.21}
$$

则原全局端点具有精确等价式

$$
\boxed{
\begin{aligned}
&g(E,U)\ge\kappa\rho(E,U)
 \quad\text{对所有 }E\in\operatorname{Dens}_2,\ U\in U(4)\\
&\quad\Longleftrightarrow\quad C_{\mathrm{opt}}=R_*\\
&\quad\Longleftrightarrow\quad
 \nu_\kappa(z)\ge0\quad\text{对所有 }z\in\mathcal R_H.
\end{aligned}}
\tag{28.22}
$$

此处 $R_*=\kappa^{-1}$、$\nu_\kappa$ 完全沿用源卷。每个原严格端点违反都可在 $\mathcal R_H$ 中得到实际原生产者严格违反。

**证明。** 源卷定理 27.6 已将原全局端点等价地归约为 $\mathcal B_{\mathcal O}$ 上 $\nu_\kappa\ge0$。在该边界的补集 $\mathcal B_{\mathcal O}\setminus\mathcal R_H$ 上，(28.5) 和源卷定理 23.4 已给出 $\nu_\kappa\ge0$，包括证书等号。因此全边界断言恰等价于 (28.22) 的最后一行；与 $C_{\rm opt}=R_*$ 的等价沿用源卷 (23.22)。

若有原严格违反，源卷定理 27.6 给出 $z\in\mathcal B_{\mathcal O}$、某个实际总体 $p$，使 $G(z,p)-\kappa r(z,p)<0$。由 (28.10)–(28.11)，该 $z$ 不可能满足 (28.5)，故属于 $\mathcal R_H$。再用源卷 (23.13) 的达到相对相位及 $z$ 的任意一个实际酉提升，即有同一个原效应和共享酉反馈的严格违反。源卷的实现步骤是另取一个酉矩阵，绝非把原 $U$ 物理缩放。反向必要性由源卷定理 23.4 直接给出。普通转置、联合符号、一个共同标量相位、全部总体及任意实际提升均保持不变。$\square$

**命题 28.6（残余非空且两种纯边界均保留）。** 令

$$
\begin{aligned}
z_0&=(1,i,\bar\zeta,\zeta),\\
z_c&=(q,iq,\bar\zeta,q\zeta),\\
z_i&=(499/500,(999/1000)i,(1999/2000)\bar\zeta,
                              (1999/2000)\zeta).
\end{aligned}
\tag{28.23}
$$

则三者均在 $\mathcal R_H$ 中。$z_0$ 在两种饱和的交叠，$z_c$ 仅坐标饱和，$z_i$ 仅模长不平衡饱和；后两者均有实际非对角酉提升。这些是充分证书的障碍，不是原端点的反例。

**证明。** 使用 (28.16) 的同一相位族，有

| 数据 | $n_{12}$ | $n_{34}$ | $\max_j|z_j|$ | $\Delta$ |
| --- | --- | --- | --- | --- |
| $z_0$ | $2$ | $2$ | $1$ | $2$ |
| $z_c$ | $998001/500000$ | $1998001/1000000$ | $1$ | $1999/1000$ |
| $z_i$ | $398801/200000$ | $3996001/2000000$ | $1999/2000<1$ | $2$ |

命题 28.4 中的有理界同样给出 $2<A=B<3$，因而三者均属于 $\mathcal B_{\mathcal O}$。对 $z_0$，利用 $1/(c-s)=2c$，有精确值

$$
H(2,2)=4s-2c<0.
\tag{28.24}
$$

也可同时对三例作严格有理估计：它们的两对能量均大于 $199/100$，而源卷 (22.13) 给出 $C<177/50$、$L<21/5$。函数 $C-La/(L-b)$ 关于 $C,L$ 单调不减、关于 $a,b$ 单调不增（这里 $a,b>0$ 且 $L>b$），所以

$$
H(n_{12},n_{34})
<\frac{177}{50}-
  \frac{(199/100)(21/5)}{21/5-199/100}
=-\frac{2673}{11050}<0.
\tag{28.25}
$$

另一方面，$9-A-B>3$，故 (28.21) 的严格不等式成立。

具体实现仍可直接给出。$z_0$ 由 $U_0=D_0U_+$ 实现。对 $z_c$，在 (28.19) 的构造中令三个目标对角均为 $q$，即取 $\lambda=(3q-1)/2$、$x=(1,1,1)^{\mathsf T}/\sqrt3$，嵌入坐标 $(1,2,4)$ 并固定坐标 $3$，再取 $U=D_0RU_+$。对 $z_i$，在 (28.20) 中改取 $a=499/500$、$b=999/1000$，并把后两处 $q$ 换成 $1999/2000$；等式 $b+2(1999/2000)-a=2$ 仍使反射向量为单位向量。所得两种实正交矩阵均有模小于一的对角元，因而给出非对角酉反馈。

证书下界为负不蕴含 $G-\kappa r$ 或 $g-\kappa\rho$ 为负，也不产生可行反例。未决命题仍是 (28.22) 最后一行在整个非空 $\mathcal R_H$ 上的统一非负性；其坐标饱和、模长不平衡饱和及交叠全部保留。$\square$

## 追加锚（本行以下为增补区）
