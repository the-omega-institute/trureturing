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

## 29. 联合迹平方与能量的原生产者证书

**定义 29.1（联合迹能量读数）。** 沿用源卷定义 23.1、定理 23.2 及本卷定义 28.1。对 $w\in\mathcal W$ 置

$$
N(w)=n_{12}(w)+n_{34}(w)=\sum_{j=1}^4|w_j|^2,\qquad
\mathfrak J(w)=\frac{N(w)}8+\frac{A(w)^2+B(w)^2}{20}.
\tag{29.1}
$$

此处 $\mathfrak J$ 是新的读数符号，不是源卷第 24 节的局部常数 $J$。它在一个共同标量相位 $w\mapsto\lambda w$、$|\lambda|=1$ 下不变。对原效应和实际共享反馈，始终取 $w=\operatorname{diag}(UU_+^\dagger)$，并保持普通转置 $E^{\mathsf T}$、联合优化器符号及源卷的距离 $\rho$。

**定理 29.2（联合迹能量的统一原效应下界）。** 对每个实际 $U\in U(4)$，若其上述对角满足

$$
A(w)+B(w)\ge4,\qquad \mathfrak J(w)\le1,
$$

则每个 $E\in\operatorname{Dens}_2$，包括奇异及混合效应，均满足

$$
\boxed{
g(E,U)-\frac{\rho(E,U)}{25}
\ge\left(e^2-\frac15\right)(1-\mathfrak J(w))
  +\frac{1-\operatorname{Tr}(E^2)}{25}
\ge0.
}
\tag{29.2}
$$

特别地，这些原生产者均满足 $g(E,U)\ge\kappa\rho(E,U)$。结论适用于同一对角的每个实际酉提升，包括任意非对角提升。

**证明。** 对同一个 $w$ 定义四个线性形式

$$
\begin{aligned}
\sigma_0&=w_1+w_2+w_3+w_4,&
\tau_0&=w_1+w_2-w_3-w_4,\\
\sigma_1&=w_1-w_2+i(w_3-w_4),&
\tau_1&=w_1-w_2-i(w_3-w_4).
\end{aligned}
\tag{29.3}
$$

这四个系数行两两 Hermitian 正交，平方范数均为 $4$。因此

$$
\begin{aligned}
N&=\frac{|\sigma_0|^2+|\tau_0|^2+
               |\sigma_1|^2+|\tau_1|^2}{4},\\
\mathfrak J&=\mathfrak J_0+\mathfrak J_1,\qquad
\mathfrak J_j=\frac{13}{160}|\sigma_j|^2+
                         \frac1{32}|\tau_j|^2\quad(j=0,1).
\end{aligned}
\tag{29.4}
$$

源卷的两条幅度形式同时具有精确展开

$$
P=\frac d4\sigma_0-\frac{c-h}{2}\tau_0,\qquad
Q=\frac e4\sigma_1+\frac{h-s}{2}\tau_1.
\tag{29.5}
$$

分别在这两个正交分量组上应用加权复 Cauchy–Schwarz，得到

$$
\begin{aligned}
u^2&\le\left(\frac{10}{13}d^2+8(c-h)^2\right)\mathfrak J_0,\\
v^2&\le\left(\frac{10}{13}e^2+8(h-s)^2\right)\mathfrak J_1.
\end{aligned}
\tag{29.6}
$$

所需常数比较具有严格余量。源卷 (22.13) 的有理界给出

$$
\begin{aligned}
\frac3{13}d^2-8(c-h)^2-\frac15
&>\frac{12}{13}\left(\frac{16309}{10000}\right)^2
       -8\left(\frac{2168}{10000}\right)^2-\frac15
 =\frac{610744619}{325000000}>0,\\
\frac3{13}e^2-8(h-s)^2-\frac15
&>\frac{12}{13}\left(\frac{10897}{10000}\right)^2
       -8\left(\frac{3246}{10000}\right)^2-\frac15
 =\frac{17284411}{325000000}>\frac1{20}.
\end{aligned}
\tag{29.7}
$$

又 $d^2>e^2>4$，故下面分母均为正。由 (29.4)、(29.6)–(29.7)，同一个数据的两条原幅度满足联合估计

$$
\frac{u(w)^2}{d^2-1/5}+
\frac{v(w)^2}{e^2-1/5}\le\mathfrak J(w).
\tag{29.8}
$$

这里并未断言两个幅度上界能够同时取等。对任意总体 $p\in[0,1]$，记 $D(p)=d^2p+e^2(1-p)$，再次应用 Cauchy–Schwarz：

$$
\begin{aligned}
\bigl(u\sqrt p+v\sqrt{1-p}\bigr)^2
&\le\left(\frac{u^2}{d^2-1/5}
           +\frac{v^2}{e^2-1/5}\right)
       \left((d^2-1/5)p+(e^2-1/5)(1-p)\right)\\
&\le\mathfrak J\left(D(p)-\frac15\right).
\end{aligned}
\tag{29.9}
$$

由源卷 (23.3) 及 $1-\mathfrak J\ge0$，

$$
G(w,p)\ge D(p)(1-\mathfrak J)+\frac{\mathfrak J}{5}
\ge e^2(1-\mathfrak J)+\frac{\mathfrak J}{5}.
\tag{29.10}
$$

现在取原效应的实际总体与杂质

$$
p=b_+^\dagger E^{\mathsf T}b_+,\qquad
\epsilon(E)=1-\operatorname{Tr}(E^2)\ge0.
$$

源卷 (23.14) 及 (27.11) 给出

$$
\begin{aligned}
g-\frac{\rho}{25}
&\ge G(w,p)-\frac{r(w,p)}{25}+\frac{\epsilon(E)}{25},\\
r(w,p)
&=\min\{10-2p-2A,\ 8+2p-2B\}\\
&\le\frac{(10-2p-2A)+(8+2p-2B)}2
=9-A-B\le5.
\end{aligned}
\tag{29.11}
$$

于是

$$
\begin{aligned}
g-\frac{\rho}{25}
&\ge e^2(1-\mathfrak J)+\frac{\mathfrak J}{5}
                         -\frac15+\frac{\epsilon(E)}{25}\\
&=\left(e^2-\frac15\right)(1-\mathfrak J)
                         +\frac{\epsilon(E)}{25}\ge0.
\end{aligned}
\tag{29.12}
$$

因 $\rho\ge0$ 及 $0<\kappa<1/25$，这立即推出原 $\kappa$ 端点。

本证明的幅度、迹和能量均来自同一个实际 $U$。对联合符号距离的唯一放宽是 (29.11) 中对其最小值取平均上界；相对效应相位只通过源卷对所有原效应成立的下界进入。所有总体端点、零幅度、混合与奇异效应均包含在内。分母仅有固定的正数，故不需选取非零迹或非零坐标；共同标量相位的商及普通转置保持不变。加权 Cauchy–Schwarz 与正交展开是标准中间工具，(29.5)–(29.12) 是针对源卷固定原生产者的推导。$\square$

**命题 29.3（三种边界层中的实际新增范围）。** 令

$$
\begin{aligned}
\eta&=\frac{4+3i}{5},\qquad
a=\frac{499}{500},\qquad b=q=\frac{999}{1000},
\qquad t=\frac{1999}{2000},\\
y_\star&=(\eta,1,i,-i),\\
y_{\rm c}&=(q\eta,q,i,-qi),\\
y_{\rm i}&=(a\eta,b,ti,-ti).
\end{aligned}
\tag{29.13}
$$

三者均在 $\mathcal R_H$ 中且满足 $\mathfrak J<19/20$。其中 $y_{\rm c}$ 仅坐标饱和，$y_{\rm i}$ 仅模长不平衡饱和，$y_\star$ 在二者交叠。两种纯边界各有显式非对角共享酉反馈实现；每个数据的任意实际提升及每个归一化效应都满足 (29.2)。每种边界层中均存在非空相对开新增范围。

**证明。** 对非负实数 $\alpha,\beta,\tau,\upsilon$ 写

$$
y(\alpha,\beta,\tau,\upsilon)=(\alpha\eta,\beta,i\tau,-i\upsilon).
$$

原迹读数及两对能量为

$$
\begin{aligned}
A(y)^2&=(4\alpha/5+\beta)^2+
                         (3\alpha/5+\tau-\upsilon)^2,\\
B(y)^2&=(4\alpha/5-\beta-\tau-\upsilon)^2+(3\alpha/5)^2,\\
n_{12}(y)&=\alpha^2+\beta^2,\qquad
n_{34}(y)=\tau^2+\upsilon^2.
\end{aligned}
\tag{29.14}
$$

代入三组参数，得到精确值：

| 数据 | $n_{12}$ | $n_{34}$ | $A^2$ | $B^2$ | $\mathfrak J$ |
| --- | --- | --- | --- | --- | --- |
| $y_\star$ | $2$ | $2$ | $18/5$ | $26/5$ | $47/50$ |
| $y_{\rm c}$ | $998001/500000$ | $1998001/1000000$ | $17970017/5000000$ | $25970009/5000000$ | $187730127/200000000$ |
| $y_{\rm i}$ | $398801/200000$ | $3996001/2000000$ | $17946041/5000000$ | $3248001/625000$ | $375320471/400000000$ |

每行均有

$$
\frac95<A<2,\qquad \frac{11}{5}<B<\frac52,\qquad
A+B>4,\qquad n_{12},n_{34}>\frac{199}{100},\qquad
\mathfrak J<\frac{19}{20}.
\tag{29.15}
$$

特别地，$A<A_0$、$B<23/6$。用与 (28.25) 相同的单调性估计，得到

$$
H(n_{12},n_{34})<-\frac{2673}{11050}<0
             <\kappa(9-A-B).
$$

记 $\Delta(z)=\sum_j|z_j|-2\min_j|z_j|$。三例的边界读数是

$$
\begin{array}{c|ccc}
 &y_\star&y_{\rm c}&y_{\rm i}\\ \hline
\max_j|z_j|&1&1&t<1\\
\Delta(z)&2&1+q<2&b+2t-a=2 .
\end{array}
\tag{29.16}
$$

因此三者均在 $\mathcal W$ 且 $m=1$，分别属于完整径向边界的三种层；结合 (29.15) 便知均在 $\mathcal B_{\mathcal O}\cap\mathcal R_H$。源卷 (27.8) 的内域证书在这里左端为零、右端严格为正，两个旧迹帽及迹三角也由 (29.15) 排除。因此新增结论实际作用于 (28.21) 的未覆盖范围。

下面沿用 (28.19)–(28.20) 的正交实现。置 $D_\eta=\operatorname{diag}(\eta,1,i,-i)$，并令

$$
\lambda_\circ=\frac{3q-1}{2}=\frac{1997}{2000},\qquad
x_\circ=\frac1{\sqrt3}(1,1,1)^{\mathsf T},\qquad
K_{x_\circ}v=x_\circ\times v.
$$

将

$$
\lambda_\circ I_3+(1-\lambda_\circ)x_\circ x_\circ^{\mathsf T}
                 +\sqrt{1-\lambda_\circ^2}K_{x_\circ}
$$

嵌入坐标 $(1,2,4)$ 并固定坐标 $3$，得到 $R_{\rm c}$。它正交且对角为 $(q,q,1,q)$，因为每个三维对角元为 $(1+2\lambda_\circ)/3=q$。再置

$$
\begin{aligned}
v_\circ&=\left(\sqrt{\frac{1+a}{2}},
              \sqrt{\frac{1-b}{2}},
              \sqrt{\frac{1-t}{2}},
              \sqrt{\frac{1-t}{2}}\right)^{\mathsf T},\\
R_{\rm i}&=\operatorname{diag}(-1,1,1,1)
                         (I_4-2v_\circ v_\circ^{\mathsf T}).
\end{aligned}
\tag{29.17}
$$

等式 $b+2t-a=2$ 给出 $v_\circ^{\mathsf T}v_\circ=1$，所以 $R_{\rm i}$ 正交且对角为 $(a,b,t,t)$。于是实际反馈

$$
U_\star=D_\eta U_+,\qquad
U_{\rm c}=D_\eta R_{\rm c}U_+,\qquad
U_{\rm i}=D_\eta R_{\rm i}U_+
\tag{29.18}
$$

分别实现 (29.13)。后两者的实正交因子具有模小于一的对角元，行范数强制存在非零非对角元；左右两侧的对角酉矩阵不会消去它们。这给出两种纯边界的实际非对角消费者，而 (29.2) 还同时约束这些数据的所有其他实际提升。

可实现性的普遍依据仍为源卷定理 23.2 所用的 Thompson 定理，见 Jasper–Loreaux–Weiss，[*Thompson's theorem for compact operators and diagonals of unitary operators*, arXiv:1602.08435v1，定理 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3)。在这里取维数四和四个奇异值全为一，所得条件正是源卷 (23.1)。该成熟定理仅作为实现工具；新增内容是 (29.2) 及其在此原生产者范围上的应用。

所有严格条件 (29.15) 和 $H<\kappa(9-A-B)$ 均连续。故在三个边界层中分别取各例的足够小相对邻域，仍满足这些条件，且每个邻域内的全部数据均由源卷定理 23.2 实现。由 $e^2>4$ 和 $\mathfrak J<19/20$，这些邻域中的任意实际提升对全部归一化效应均有

$$
g(E,U)-\frac{\rho(E,U)}{25}>
\frac{19}{100}+\frac{1-\operatorname{Tr}(E^2)}{25}.
$$

保持四个模长而小幅改变第一坐标相位，也仍在相应层及这些邻域内；其他三个非零坐标固定，故这不是共同标量相位作用。因此新增范围在共同相位商后也非空，并非仅为三个孤立数据或它们的共同相位副本。$\square$

**定理 29.4（联合证书后的精确剩余义务）。** 定义

$$
\mathcal R_{H,\mathfrak J}
=\{z\in\mathcal R_H:\mathfrak J(z)>1\}.
\tag{29.19}
$$

原全局端点具有精确等价式

$$
\boxed{
\begin{aligned}
&g(E,U)\ge\kappa\rho(E,U)
   \quad\text{对所有 }E\in\operatorname{Dens}_2,\ U\in U(4)\\
&\quad\Longleftrightarrow\quad C_{\rm opt}=R_*\\
&\quad\Longleftrightarrow\quad
\nu_\kappa(z)\ge0\quad\text{对所有 }z\in\mathcal R_{H,\mathfrak J}.
\end{aligned}}
\tag{29.20}
$$

每个原严格违反都在此剩余集合中产生实际原生产者严格违反。该集合在仅坐标饱和、仅模长不平衡饱和及二者交叠三种层中均非空。

**证明。** 由定理 28.5，只需判断 $\mathcal R_H$ 上的统一非负性。此集合已满足 $A+B>4$。在其中 $\mathfrak J\le1$ 的部分，定理 29.2 对每个实际提升的每个原效应给出原端点；由源卷 (23.6)–(23.7)，这恰给出全部总体上的 $G-\kappa r\ge0$，因而 $\nu_\kappa\ge0$，包括 $\mathfrak J=1$。故剩余断言精确为 (29.20) 最后一行；$C_{\rm opt}=R_*$ 的等价仍由源卷 (23.22) 给出。

若有原严格违反，定理 28.5 及源卷定理 27.6 已将其移到某个 $z\in\mathcal R_H$ 的同总体严格违反。该 $z$ 不可能有 $\mathfrak J\le1$，否则 (29.2) 与源卷的达到效应 (23.13) 矛盾。于是 $z\in\mathcal R_{H,\mathfrak J}$；其任意实际酉提升与达到相对相位给出同一个原效应、同一个共享反馈的严格违反。反向必要性由源卷定理 23.4 直接给出。这里的径向归约始终是另取可实现数据及酉提升，不是对实际 $U$ 作物理缩放。

非空性复用 (28.23) 的 $z_0,z_{\rm c},z_{\rm i}$，保持它们原有的相位与模长。这三者已经属于 $\mathcal R_H$，并分别处于交叠、仅坐标饱和及仅模长不平衡饱和层。令 $r_\circ=499/500$。在 (28.16) 的参数记法下，这三者的 $a,b,t,u$ 均至少为 $r_\circ$，且 $A^2=B^2=F(a,b,t,u)$。因此

$$
\begin{aligned}
N&\ge4r_\circ^2,\qquad
F\ge(a+h(t+u))^2\ge r_\circ^2(1+2h)^2,\\
\mathfrak J
&=\frac N8+\frac F{10}
\ge r_\circ^2\left(\frac12+\frac{(1+2h)^2}{10}\right)\\
&>r_\circ^2\frac{269}{250}
=\frac{66981269}{62500000}>1,
\end{aligned}
\tag{29.21}
$$

其中严格界只用 $h>7/10$。故三例仍在 (29.19) 中，两种纯边界的非对角实现也原样沿用命题 28.6。严格的 $\mathfrak J>1$ 及 $\mathcal R_H$ 条件还在各自层内保留非空相对开邻域。

未决断言是 (29.20) 最后一行在整个 $\mathcal R_{H,\mathfrak J}$ 上的统一非负性，或其中经源卷 (23.13) 及实际酉提升得到的原可行严格反例。$\mathfrak J>1$ 仅表示本节充分证书不适用，不蕴含 $\nu_\kappa<0$；上述剩余例也不是原端点的反例。$\square$

## 追加锚（本行以下为增补区）

## 30. 全模长域到共同相位核的继承定理

**定义 30.1（坐标相位与最小模长）。** 对 $z\in\mathbb C$ 定义

$$
\operatorname{ph}(z)=
\begin{cases}z/|z|,&z\ne0,\\
1,&z=0.
\end{cases}
$$

对 $w\in\mathcal W$ 置

$$
\widehat w=(\operatorname{ph}(w_1),\ldots,\operatorname{ph}(w_4)),
\qquad
\mu(w)=\min_j|w_j|.
\tag{30.1}
$$

于是 $\widehat w\in\mathbb T^4:=\{z\in\mathbb C^4:|z_j|=1\}$；当某坐标为零时，(30.1) 的取值约定只用于定义一个单位模代表。记

$$
F_\kappa(w,p)=G(w,p)-\kappa r(w,p).
\tag{30.2}
$$

**引理 30.2（最小模长分解保持可实现域）。** 若 $0\le t:=\mu(w)<1$，定义

$$
 y_j=\frac{|w_j|-t}{1-t}\,\widehat w_j\qquad(1\le j\le4).
\tag{30.3}
$$

则

$$
 w=t\widehat w+(1-t)y,\qquad y\in\mathcal W,\qquad
\min_j|y_j|=0,\qquad \sum_j|y_j|\le2.
\tag{30.4}
$$

若 $t=1$，则 $w=\widehat w$，无需定义 $y$；若 $t=0$，(30.3) 给出 $y=w$，不发生除以最小模长的操作。

**证明。** 由 $|w_j|\le1$，有 $0\le|y_j|\le1$，且至少一个 $y_j$ 为零。因为 $w\in\mathcal W$，

$$
\sum_j|w_j|-2t\le2.
$$

故

$$
\sum_j|y_j|
=\frac{\sum_j|w_j|-4t}{1-t}
\le\frac{2-2t}{1-t}=2.
$$

当 $\min_j|y_j|=0$ 时，最后一个不等式正是 (23.1) 的第二个不等式；因此 $y\in\mathcal W$。等式 $w=t\widehat w+(1-t)y$ 按坐标直接成立。$\square$

**引理 30.3（零坐标层的统一能量余量）。** 对满足 (30.4) 的 $y$ 及每个 $p\in[0,1]$，有

$$
G(y,p)\ge e^2-4.
\tag{30.5}
$$

**证明。** 写 $\alpha=\sqrt p$、$\beta=\sqrt{1-p}$。由 (23.2)，对某个 $|\lambda|=1$ 的系数行

$$
 a_j(\lambda)=\alpha P_j+\lambda\beta Q_j
$$
有

$$
 |P_j|^2+|Q_j|^2=1\qquad(j=1,2,3,4),
$$
因为 $(P_1,P_2,P_3,P_4)=(h,h,c,c)$、
$(Q_1,Q_2,Q_3,Q_4)=(h,-h,is,-is)$。于是复 Cauchy--Schwarz 给出
$|a_j(\lambda)|\le1$。另一方面

$$
\sqrt p\,u(y)+\sqrt{1-p}\,v(y)
 =\max_{|\lambda|=1}\left|\sum_j a_j(\lambda)y_j\right|
 \le\sum_j|y_j|\le2.
$$

而 $d^2p+e^2(1-p)\ge e^2$。代入 (23.3) 即得 (30.5)。$\square$

**引理 30.4（共同分解下的距离控制）。** 对 $w,t,y$ 如引理 30.2 及任意 $p\in[0,1]$，有

$$
 r(w,p)\le t\,r(\widehat w,p)+14(1-t).
\tag{30.6}
$$

**证明。** 置 $c_+(p)=10-2p$、$c_-(p)=8+2p$。三角不等式及 (30.4) 给出

$$
 A(w)\ge tA(\widehat w)-(1-t)A(y),
$$
从而

$$
 r_+(w,p)
 \le t r_+(\widehat w,p)+(1-t)\bigl(c_+(p)+2A(y)\bigr).
$$

同理

$$
 r_-(w,p)
 \le t r_-(\widehat w,p)+(1-t)\bigl(c_-(p)+2B(y)\bigr).
$$

由 $\sum_j|y_j|\le2$，有 $A(y),B(y)\le2$，而 $c_\pm(p)\le10$。取 $\widehat w$ 上达到 $r(\widehat w,p)$ 的同一分支，得到

$$
 r(w,p)\le t r(\widehat w,p)+14(1-t).
$$
这里没有把两个符号分支分别取到；所取分支仍是原联合距离的同一个最小化符号。$\square$

**定理 30.5（全模长域的原生产者相位继承）。** 对每个 $w\in\mathcal W$ 及每个 $p\in[0,1]$，有

$$
\boxed{
F_\kappa(w,p)
\ge \mu(w)F_\kappa(\widehat w,p)
 +(1-\mu(w))\eta_\kappa,
}
\tag{30.7}
$$

其中

$$
\eta_\kappa=e^2-4-14\kappa>\frac9{50}>0.
\tag{30.8}
$$

因此只要 $\mu(w)<1$ 且相位数据满足 $F_\kappa(\widehat w,p)\ge0$，便有严格余量

$$
F_\kappa(w,p)>0.
\tag{30.9}
$$

**证明。** $t=\mu(w)=1$ 时 $w=\widehat w$，(30.7) 是等式。以下令 $t<1$。置 $S_p(w)=\sqrt p\,u(w)+\sqrt{1-p}\,v(w)$。由

$$
S_p(w)=\max_{|\lambda|=1}
 \left|\sqrt p\,P(w)+\lambda\sqrt{1-p}\,Q(w)\right|
$$
可知 $S_p^2$ 是复线性形式平方模的逐点上确界，故是实向量 $w$ 的凸函数；因而 $G(w,p)=d^2p+e^2(1-p)-S_p(w)^2$ 是凹函数。引理 30.2、30.3 给出

$$
G(w,p)
\ge tG(\widehat w,p)+(1-t)G(y,p)
\ge tG(\widehat w,p)+(1-t)(e^2-4),
\tag{30.10}
$$
其中 $t=\mu(w)$。引理 30.4 同时给出

$$
-\kappa r(w,p)
\ge-\kappa t r(\widehat w,p)-14\kappa(1-t).
$$
两式相加即为 (30.7)。

为核验余量的严格正性，源卷 (22.13) 给出
$h<7072/10000$ 及 $s>3826/10000$，所以

$$
 e=\frac1h+2s>\frac{10000}{7072}+2\frac{3826}{10000}
 >\frac{10896}{5000}.
$$
结合源卷定理 21.3 的 $0<\kappa<1/25$，有

$$
\eta_\kappa>
\left(\frac{10896}{5000}\right)^2-4-\frac{14}{25}
=\frac{73794}{390625}>\frac9{50}.
$$
所有这些估计在 $p=0,1$ 仍是闭区间上的等式或不等式；(30.1)--(30.4) 也覆盖零坐标。故没有使用非零幅度、非零迹或可逆的归一化。$\square$

**定理 30.6（完整原端点与共同相位核的精确等价）。** 令

$$
\mathsf{Core}_\kappa:\qquad
F_\kappa(\theta,p)\ge0
\quad\text{对所有 }\theta\in\mathbb T^4/U(1),\quad p\in[0,1],
\tag{30.11}
$$
其中商只表示定义 23.1 的一个共同标量相位，不选取代表。则

$$
\boxed{
\begin{aligned}
&g(E,U)\ge\kappa\rho(E,U)
\quad\text{对所有 }E\in\operatorname{Dens}_2,\ U\in U(4)\\
&\quad\Longleftrightarrow\quad C_{\mathrm{opt}}=R_*\\
&\quad\Longleftrightarrow\quad \mathsf{Core}_\kappa.
\end{aligned}}
\tag{30.12}
$$

更具体地，在 $\mathsf{Core}_\kappa$ 成立时，每个原始可实现 $w$、每个原始总体 $p$ 都满足

$$
F_\kappa(w,p)\ge(1-\mu(w))\eta_\kappa,
\tag{30.13}
$$

且当 $\mu(w)<1$ 时严格为正。此结论覆盖坐标饱和层、模长不平衡饱和层、二者交叠、内部点以及全单位模层；这些 $w$ 均仍由定理 23.2 的实际共享酉实现，而 (30.3) 的 $y$ 只是可实现约化数据的分解，不是对任何实际反馈 $U$ 的物理缩放。对给定实际 $U$，源卷 (23.14) 在其同一总体
$p=b_+^\dagger E^{\mathsf T}b_+$ 上给出原效应结论，故普通转置、联合优化器符号、奇异或混合效应以及任意实际非对角提升均保留。

**证明。** 假设 $\mathsf{Core}_\kappa$。对任意 $w\in\mathcal W$，$\widehat w$ 是单位模可实现数据，故定理 30.5 给出 (30.13)，于是 $F_\kappa(w,p)\ge0$。定理 23.4 及 (23.14) 随即给出第一行的原端点，且对每个实际 $U$ 使用同一个 $U$ 完成全部联合计算。

反之，若原端点成立，取任意 $\theta\in\mathbb T^4$ 的实际酉提升及任意 $p$。源卷 (23.6) 的同一实际提升和达到相对相位给出
$F_\kappa(\theta,p)\ge0$；故成立 (30.11)。第一行与第二行的等价沿用源卷 (23.22)。$\square$

**命题 30.7（共同相位核中尚未支付的精确范围）。** 在 $\mathbb T^4$ 上有

$$
 n_{12}=n_{34}=2,\qquad
\mathfrak J(\theta)=\frac12+\frac{A(\theta)^2+B(\theta)^2}{20}.
\tag{30.14}
$$
源卷第 24--26 节及定理 29.2 已经处理 $A\ge A_0$、$B\ge23/6$、$A+B\le4$ 以及
$A^2+B^2\le10$ 的相位数据。又

$$
H(2,2)=4s-2c<0,\qquad 9-A(\theta)-B(\theta)\ge1,
$$
所以单位模数据均满足 $H(2,2)<\kappa(9-A-B)$；成对能量充分条件 (28.5) 不覆盖这些数据。因而 (30.11) 的唯一未付断言精确为

$$
\boxed{
\nu_\kappa(\theta)\ge0
\quad\text{对所有 }\theta\in\mathbb T^4/U(1)\text{ 满足 }
 A(\theta)<A_0,\quad B(\theta)<23/6,\quad
 A(\theta)+B(\theta)>4,\quad
 A(\theta)^2+B(\theta)^2>10.
}
\tag{30.15}
$$

该范围确实非空；例如

$$
\theta_0=(1,i,e^{-i\pi/4},e^{i\pi/4})
$$
满足

$$
 A(\theta_0)=B(\theta_0)=\sqrt{4+2\sqrt2},\qquad
 A(\theta_0)^2+B(\theta_0)^2=8+4\sqrt2>10,
$$
并且 $A(\theta_0)+B(\theta_0)>4$、$A(\theta_0)<A_0$、$B(\theta_0)<23/6$。该点及其共同相位类是原始单位酉反馈的实际数据。

**证明。** (30.14) 由 $N=4$ 代入 (29.1) 得到。若 $A^2+B^2\le10$ 且 $A+B>4$，则 $\mathfrak J\le1$，定理 29.2 给出原端点；若 $A\ge A_0$、$B\ge23/6$ 或 $A+B\le4$，则分别由源卷第 24、25、26 节给出。剩下的区域使 $H(2,2)<0<\kappa(9-A-B)$，故属于 (28.21)，并由 (30.14) 有 $\mathfrak J>1$。于是该区域正是 $\mathbb T^4\cap\mathcal R_{H,\mathfrak J}$，而定理 30.6 与源卷定理 23.4 给出所述等价。对所给 $\theta_0$，两条迹的平方均为 $4+2\sqrt2$；$2<\sqrt{4+2\sqrt2}<3<A_0$ 且 $3<23/6$，故所有严格条件成立。$\square$

(30.15) 是完整共同相位核上的相关相位不等式；本节没有把它替换为独立幅度最大值、独立符号分支或另一充分截面。它仍是原全局端点的开放数学义务；若在该集合找到负的有限判据值，源卷 (23.13) 及定理 23.2 会给出同一共享酉下的原始可行严格反例。

## 追加锚（本行以下为增补区）

## 31. A shifted support comparison and the uniform sharp endpoint

**Definition 31.1 (population and support notation).** Retain the fixed record, constants and reduced quantities of source Definition 23.1 and (30.2). Put

$$
 D(p)=d^2p+e^2(1-p),\qquad \gamma=1/25.
\tag{31.1}
$$

For nonnegative $a,b$ and $0\le x\le1$, write

$$
 \Phi_{a,b}(x)=
 \sqrt{2(a^2+b^2)+2\sqrt{(a^2+b^2)^2-4a^2b^2x}}.
\tag{31.2}
$$

Thus $\Phi_{a,b}(\cos^2\phi)=|a+be^{i\phi}|+|a-be^{i\phi}|$. The shifted support below uses the same scalar shift in all four coordinates.

**Lemma 31.2 (two uniform shifted support comparisons).** Let $\alpha,\beta\ge0$ with $\alpha^2+\beta^2=1$.

If $\alpha^2\ge1/2$ and $0\le\varepsilon\le1/50$, then, for every real $\phi$,

$$
\begin{aligned}
&|h\alpha-\varepsilon+h\beta e^{i\phi}|
 +|h\alpha-\varepsilon-h\beta e^{i\phi}|\\
&\quad+|c\alpha-\varepsilon+is\beta e^{i\phi}|
 +|c\alpha-\varepsilon-is\beta e^{i\phi}|\\
&\le2\sqrt{(h\alpha-\varepsilon)^2+h^2\beta^2}
       +2c\alpha-2\varepsilon.
\end{aligned}
\tag{31.3}
$$

If $\alpha^2\ge8/9$ and $0\le\varepsilon\le7/400$, then

$$
\begin{aligned}
&|h\alpha-\varepsilon+h\beta e^{i\phi}|
 +|h\alpha-\varepsilon-h\beta e^{i\phi}|\\
&\quad+|s\alpha-\varepsilon-ic\beta e^{i\phi}|
 +|s\alpha-\varepsilon+ic\beta e^{i\phi}|\\
&\le2h\alpha-2\varepsilon
       +2\sqrt{(s\alpha-\varepsilon)^2+c^2\beta^2}.
\end{aligned}
\tag{31.4}
$$

**Proof.** For positive $a,b$, differentiating (31.2) on its differentiability interval gives

$$
 \Phi'_{a,b}(x)=
 -\frac{2a^2b^2}
 {\Phi_{a,b}(x)\sqrt{(a^2+b^2)^2-4a^2b^2x}}.
\tag{31.5}
$$

Both factors in the denominator decrease with $x$, so this derivative is nonincreasing. In particular,

$$
 \Phi'_{a,b}(0)=-\frac{a^2b^2}{(a^2+b^2)^{3/2}},\qquad
 \Phi'_{a,b}(1)=-\frac{ab^2}{a^2-b^2}\quad(a>b).
\tag{31.6}
$$

An endpoint at which $a=b$ is treated by continuity. When $b=0$, the pair is constant.

For (31.3), set $A=h\alpha-\varepsilon$, $B=c\alpha-\varepsilon$ and $k=24/25$. Then

$$
 A\ge kh\alpha>0,\qquad B\ge kc\alpha>s\beta,
 \qquad A^2+h^2\beta^2\le h^2.
\tag{31.7}
$$

The first two bounds use $h\alpha\ge1/2$ and $c\alpha>1/2$. The support sum is
$\Phi_{A,h\beta}(x)+\Phi_{B,s\beta}(1-x)$, where $x=\cos^2\phi$. Its derivative is nonpositive if

$$
 \frac{A^2h^2}{(A^2+h^2\beta^2)^{3/2}}
 \ge\frac{Bs^2}{B^2-s^2\beta^2}.
\tag{31.8}
$$

Indeed, (31.5)--(31.6) bound the derivative above by $\beta^2$ times the right side of (31.8) minus its left side. The left side of (31.8) is at least $k^2h\alpha^2$. Since $x/(x^2-r^2)$ decreases for $x>r$, its right side is at most

$$
 \frac{kc s^2}{(k^2c^2-s^2)\alpha}.
$$

Now $\alpha\ge h$, $c<1$, $c^2>17/20$ and $s^2<3/20$ give

$$
 k^2h\alpha^3\ge\frac{144}{625}
 >\frac{1800}{7917}
 >\frac{kc s^2}{k^2c^2-s^2}.
\tag{31.9}
$$

The last rational bound replaces $c$ and $s^2$ in the numerator by $1$ and $3/20$, and the denominator by $k^2(17/20)-3/20$. Thus the maximum is at $x=0$. At that point the second pair is $2B$ by (31.7), proving (31.3).

For (31.4), set $A=h\alpha-\varepsilon$, $B=s\alpha-\varepsilon$. Here

$$
 A\ge\frac{779}{1200}>h\beta,\qquad
 B\ge\frac{189}{200}s\alpha>c\beta.
\tag{31.10}
$$

For the first inequality, $h\alpha\ge2/3$. For the second, $s\alpha>1/3$ implies
$(11/200)s\alpha>7/400$; the final strict inequality follows from
$s>3826/10000$, $\alpha>47/50$, $c<924/1000$ and $\beta\le1/3$.
The support sum is now $\Phi_{A,h\beta}(x)+\Phi_{B,c\beta}(1-x)$. Its derivative is nonnegative if

$$
 \frac{B^2c^2}{(B^2+c^2\beta^2)^{3/2}}
 \ge\frac{Ah^2}{A^2-h^2\beta^2}.
\tag{31.11}
$$

In fact, (31.5)--(31.6) bound the derivative below by $\beta^2$ times the left side minus the right side. Using $c^2/s^2=3+2\sqrt2$, $\sqrt2<99/70$ and (31.10),

$$
 \left(\frac{c\beta}{B}\right)^2
 \le\frac{3+2\sqrt2}{8(189/200)^2}<\frac{41}{50},
 \qquad
 \left(\frac{91}{50}\right)^3<\left(\frac{123}{50}\right)^2.
$$

Consequently, since $B\le s$,

$$
 \frac{B^2c^2}{(B^2+c^2\beta^2)^{3/2}}
 >\frac{853/1000}{(383/1000)(123/50)}
 =\frac{42650}{47109}>\frac9{10}.
\tag{31.12}
$$

On the other hand, $h^2\beta^2\le1/18$, and monotonicity in $A$ gives

$$
 \frac{Ah^2}{A^2-h^2\beta^2}
 \le\frac{779/1200}{2((779/1200)^2-1/18)}<\frac9{10}.
\tag{31.13}
$$

This proves (31.11), so the maximum is at $x=1$. The first pair there is $2A$, proving (31.4). If $\beta=0$, both conclusions are equalities directly. All half-angle bounds used here follow from source (22.13). $\square$

**Theorem 31.3 (global branch comparisons at the two population ends).** For every $w\in\mathcal W$,

$$
\begin{aligned}
 G(w,p)&\ge\kappa r_+(w,p)&& (1/2\le p\le1),\\
 G(w,p)&\ge\kappa r_-(w,p)&& (0\le p\le1/9).
\end{aligned}
\tag{31.14}
$$

**Proof.** First, the slightly stronger rational bound

$$
 0<\kappa<\frac7{200}
\tag{31.15}
$$

follows from the defining polynomial of source Theorem 21.3. Indeed, that polynomial is twice
$(dh-z)(e^2-2z)-d^2$. At $z=7/200$, source (22.13) gives

$$
\begin{aligned}
 &(dh-7/200)(e^2-7/100)-d^2\\
 &<\left(\frac{16311}{5000}\frac{442}{625}-\frac7{200}\right)
    \left(\left(\frac{10899}{5000}\right)^2-\frac7{100}\right)
       -\left(\frac{16309}{5000}\right)^2\\
 &=-\frac{216968701513}{78125000000000}<0.
\end{aligned}
\tag{31.16}
$$

The polynomial is positive at zero, so its smaller positive root satisfies (31.15).

We shall use two actual scalar families. For $0\le y\le\pi/2$, put $\delta=2(1-\cos y)\in[0,2]$ and

$$
 w^+(y)=(e^{-iy},e^{iy},1,1),\qquad
 w^-(y)=(1,-1,-ie^{iy},ie^{-iy}).
\tag{31.17}
$$

Their actual feedback realizations are $\operatorname{diag}(w^\pm(y))U_+$. The required family comparisons are

$$
\begin{aligned}
 G(w^+(y),p)&\ge\kappa(10-2p-2A(w^+(y))),\\
 G(w^-(y),p)&\ge\gamma(8+2p-2B(w^-(y)))
 \qquad(0\le p\le1).
\end{aligned}
\tag{31.18}
$$

Here is the extension of the existing scalar identities needed for this range of $y$. For the first family,

$$
 u=d-h\delta,\quad v^2=2\delta-\delta^2/2,\quad A=4-\delta.
$$

Use the matrix (24.17) with these exact amplitudes. The polynomial identity (24.23) holds for every $\delta$, and its determinant is $J\delta^2$, with the already established $J>21/10$. Its upper-left entry is
$\delta(2(dh-\kappa)-\delta/2)>0$ for $0<\delta\le2$; both denominators $D_\delta,F_\delta$ of (24.17) are positive on $[0,2]$, using $d>3$, $e^2>4$ and $\kappa<1/25$. At $\delta=0$ the matrix is $\operatorname{diag}(0,e^2-2\kappa)$. Thus it is positive semidefinite on this full interval. Evaluating on $(\sqrt p,\sqrt{1-p})$ proves the first line of (31.18). This uses the source determinant identity without assuming the high-trace cap or its branch selection.

For the second family,

$$
 u^2=c^2(4\delta-\delta^2),\quad v=e-s\delta,\quad B=4-\delta.
$$

Use the exact matrix (25.14), still with $\gamma=1/25$. Write

$$
\begin{aligned}
 K_1&=2(es-\gamma)(d^2-2\gamma)-4c^2e^2,\\
 K_2&=2(h+c-s)+2\gamma s^2-4\gamma es+4\gamma^2+8\gamma c^2.
\end{aligned}
$$

Expansion of its determinant gives

$$
 \det K=\delta\{K_1+\delta(K_2-2\gamma h\delta)\}.
\tag{31.19}
$$

In this expansion $e^2c^2-d^2s^2=2(h+c-s)$. The rational bounds (25.17) yield

$$
 K_1>
 2\left(\frac56-\frac1{25}\right)
   \left(\frac{53}{5}-\frac2{25}\right)
 -4\frac{171}{200}\frac{119}{25}
 =\frac{1547}{3750}>0.
$$

Since $h+c-s>1$, $es<1$, $h<1$ and $\delta\le2$,

$$
 K_2-2\gamma h\delta
 >2(h+c-s)-4\gamma(es+h)>\frac{42}{25}>0.
$$

Its lower-right entry is
$\delta(2(es-\gamma)-s^2\delta)>0$ for $\delta>0$, by $es>5/6$ and $s^2<3/20$. At zero the matrix is $\operatorname{diag}(d^2-2\gamma,0)$. This proves its positive semidefiniteness and the second line of (31.18), now on all of $[0,2]$. Since its displayed branch distance is nonnegative and $\gamma>\kappa$, the same family comparison holds with $\kappa$.

We next transfer these scalar comparisons to arbitrary correlated phases. Suppose $p\ge1/2$, put $\alpha=\sqrt p$, $\beta=\sqrt{1-p}$ and

$$
 t=\alpha u(w)+\beta v(w).
$$

If $t\le2$, then $G\ge e^2-4>2/5>10\kappa\ge\kappa r_+$, using (22.13) and $r_+\le10$. Otherwise put $z=t>2$ and $\varepsilon=\kappa/z<1/50$. There is a real $\phi$ such that

$$
 t=\left|\sum_{j=1}^4a_j(\phi)w_j\right|,\qquad
 a(\phi)=\bigl(h(\alpha+\beta e^{i\phi}),
 h(\alpha-\beta e^{i\phi}),c\alpha+is\beta e^{i\phi},
 c\alpha-is\beta e^{i\phi}\bigr).
\tag{31.20}
$$

This also holds if one of $P,Q$ is zero. Use one common scalar rotation of $w$ to make this sum equal to the real number $t$. Then $A(w)\ge\operatorname{Re}\sum_jw_j$, and the coordinate support of $|w_j|\le1$ gives

$$
\begin{aligned}
 t^2-2\kappa A(w)
 &\le2\operatorname{Re}\sum_j(za_j(\phi)-\kappa)w_j-z^2\\
 &\le2\sum_j|za_j(\phi)-\kappa|-z^2\\
 &\le2\sum_j|za_j(\pi/2)-\kappa|-z^2.
\end{aligned}
\tag{31.21}
$$

The last inequality is precisely (31.3). Define $y\in[0,\pi/2)$ by

$$
 e^{iy}=\frac{h\alpha-\varepsilon+ih\beta}
                  {|h\alpha-\varepsilon+ih\beta|}.
$$

The support in the last line of (31.21) is attained by the single actual datum $w^+(y)$: its third and fourth shifted coefficients are positive real because $c\alpha-\varepsilon>s\beta$. Write

$$
 t_0=\sum_j a_j(\pi/2)w_j^+(y)
 =\alpha(2h\cos y+2c)+2h\beta\sin y\ge0.
$$

Since $A(w^+(y))=2+2\cos y$, (31.21), a real square, and (31.18) give

$$
\begin{aligned}
 t^2-2\kappa A(w)
 &\le2zt_0-z^2-2\kappa A(w^+(y))\\
 &\le t_0^2-2\kappa A(w^+(y))
 \le D(p)-\kappa(10-2p).
\end{aligned}
\tag{31.22}
$$

This proves the first line of (31.14).

For $p\le1/9$, instead set $\alpha=\sqrt{1-p}$, $\beta=\sqrt p$ and express the same data in the fixed coordinates

$$
 \widetilde w=(w_1,-w_2,iw_3,-iw_4).
$$

The identities (25.4) give

$$
 t=\alpha v(w)+\beta u(w)
   =\left|\sum_j a^-_j(\phi)\widetilde w_j\right|,
$$

for a suitable $\phi$, where

$$
 a^-(\phi)=\bigl(h(\alpha+\beta e^{i\phi}),
 h(\alpha-\beta e^{i\phi}),s\alpha-ic\beta e^{i\phi},
 s\alpha+ic\beta e^{i\phi}\bigr).
\tag{31.23}
$$

Again $t\le2$ is immediate. If $z=t>2$, then (31.15) ensures $\varepsilon=\kappa/z<7/400$. Rotate by one common scalar phase so the sum is real. Replace $A$ by $B=|\sum_j\widetilde w_j|$ in the support calculation (31.21), and apply (31.4). The maximizing phase for that support sum is now $\phi=0$. Its coordinate support is attained by

$$
 \widetilde w_0=(1,1,e^{iy},e^{-iy}),\qquad
 e^{iy}=\frac{s\alpha-\varepsilon+ic\beta}
                  {|s\alpha-\varepsilon+ic\beta|}.
$$

Here $0\le y<\pi/2$ and the first two shifted coefficients are positive. Undoing the fixed coordinate transformation gives exactly $w^-(y)$ in (31.17). The corresponding real amplitude is

$$
 t_0=\alpha(2h+2s\cos y)+2c\beta\sin y.
$$

The same square as in (31.22), followed by the second family comparison of (31.18), therefore yields

$$
 t^2-2\kappa B(w)
 \le t_0^2-2\kappa B(w^-(y))
 \le D(p)-\kappa(8+2p).
\tag{31.24}
$$

This proves the second line of (31.14). The auxiliary families enter a support inequality; all quantities on the left of (31.22) or (31.24) continue to be calculated from the same original $w$. Neither family assigns separate controls to columns of an original effect. $\square$

**Lemma 31.4 (a uniform gap on the intervening population interval).** For every $w\in\mathcal W$ and every $1/9\le p\le1/2$,

$$
 G(w,p)>\frac7{40}.
\tag{31.25}
$$

**Proof.** Write $q=1-p$, $\tau=pq$ and

$$
 a=\sqrt{c^2p+s^2q}=\sqrt{s^2+hp},\quad
 m=cp+sq,\quad I=\sqrt2+2a,\quad
 R=\frac{4\sqrt2(c-s)^2}{a+m}.
\tag{31.26}
$$

All denominators are positive. The source identity $a^2-m^2=(c-s)^2\tau$ gives

$$
 D(p)=I^2-R\tau.
\tag{31.27}
$$

For $|x|\le1$, the elementary square-root estimate with its next even term is

$$
 \sqrt{1+x}+\sqrt{1-x}
 \le2-\frac{x^2}{4}-\frac{5x^4}{64}.
\tag{31.28}
$$

For example, use $\sqrt{1-y}\le1-y/2-y^2/8$ first with $y=x^2$ in the square of the left side, then with $y=x^2/4+x^4/16$ in the resulting square root. The omitted terms have nonpositive sign; continuity includes $|x|=1$.

For the coefficients in (31.20), the triangle inequality gives $\sqrt p\,u+\sqrt q\,v\le\max_\phi\sum_j|a_j(\phi)|$. Apply (31.28) to both opposite pairs, and put $x=\cos^2\phi$. Their sum is at most $I-\mathcal L(x)$, where

$$
\begin{aligned}
 \mathcal L(x)
 &=\tau\left(hx+\frac{1-x}{8a^3}\right)
  +\tau^2\left(\frac{5h}{4}x^2
                   +\frac{5}{256a^7}(1-x)^2\right).
\end{aligned}
\tag{31.29}
$$

Both square-root arguments used in (31.28) belong to $[-1,1]$, since they come from the squared moduli of each pair. No phase has been optimized independently between the pairs: the same $x$ occurs throughout (31.29).

We record explicit rational bounds that suffice for the whole interval. In the table, $K,E$ mean $\mathcal L(x)\ge K\tau+E$ for all $0\le x\le1$; entries for $a,m,I$ are strict lower bounds and entries for $R$ are strict upper bounds.

| Population interval | $a>$ | $m>$ | $I>$ | $R<$ | $K$ | $E$ |
| --- | --- | --- | --- | --- | --- | --- |
| $[1/9,1/8]$ | $237/500$ | $221/500$ | $59/25$ | $91/50$ | $h$ | $5h\tau^2/4$ |
| $[1/8,3/16]$ | $969/2000$ | $9/20$ | $119/50$ | $16/9$ | $h$ | $5h\tau^2/8$ |
| $[3/16,1/4]$ | $66/125$ | $121/250$ | $247/100$ | $33/20$ | $2/3$ | $0$ |
| $[1/4,5/16]$ | $71/125$ | $517/1000$ | $51/20$ | $77/50$ | $5/9$ | $0$ |
| $[5/16,3/8]$ | $303/500$ | $11/20$ | $21/8$ | $36/25$ | $15/32$ | $0$ |
| $[3/8,7/16]$ | $641/1000$ | $117/200$ | $269/100$ | $34/25$ | $2/5$ | $0$ |
| $[7/16,1/2]$ | $27/40$ | $619/1000$ | $69/25$ | $257/200$ | $7/20$ | $5h\tau^2/32$ |

Here are the verifications of the table and of the gap, including the tightest rows. For a row with left endpoint $\ell$, source (22.13) gives

$$
 a^2>\left(\frac{3826}{10000}\right)^2
                 +\frac{7071}{10000}\ell,\qquad
 m>\frac{9238\ell+3826(1-\ell)}{10000}.
\tag{31.30}
$$

Squaring the positive entries in the $a$ column verifies them from the first bound. Substitution verifies the $m$ column. Since $\sqrt2>7071/5000$, these $a$ bounds give the stated $I$ bounds. Also

$$
 4\sqrt2(c-s)^2<\frac{83}{50},
$$

so the $a,m$ columns bound $R$ above respectively by

$$
 \frac{415}{229},\quad\frac{3320}{1869},\quad
 \frac{415}{253},\quad\frac{332}{217},\quad
 \frac{415}{289},\quad\frac{830}{613},\quad\frac{830}{647}.
$$

Each is strictly below the corresponding $R$ entry by cross multiplication.

On the first row $a<1/2$, $\tau\le7/64$ and

$$
 \frac{d}{dx}\frac{\mathcal L(x)}\tau
 \le h-1+\frac{35h}{128}<0.
$$

Thus its minimum is at $x=1$, giving exactly $K=h$, $E=5h\tau^2/4$. On the second row $a<11/20$; the inequalities

$$
 8h(11/20)^3<1,\qquad 64h(11/20)^7<1
$$

follow already from $h<3/4$. Hence $1/(8a^3)>h$ and $5/(256a^7)>5h/4$; use $x^2+(1-x)^2\ge1/2$ to obtain its entries.

On the next four rows, upper bounds for $a$ are respectively
$57/100$, $607/1000$, $642/1000$, $676/1000$. They follow by squaring from $a^2=s^2+hp$ and (22.13). For each such upper bound $b$ and the listed $K$, $8Kb^3<1$ and $K<h$, proving $\mathcal L(x)\ge K\tau$. On the last row $a\le h$ exactly, because $p\le1/2$. Thus $1/(8a^3)\ge h/2>7/20$ and
$5/(256a^7)\ge5h/16$, proving its $E$ entry. These arguments establish the table for every population in its closed intervals.

In every row $I-K\tau-E>0$. Squaring the bound for the amplitude and using (31.27) now gives

$$
 G\ge\tau(2IK-R-K^2\tau)+2(I-K\tau)E-E^2.
\tag{31.31}
$$

For the first two rows, $I-K\tau>9/4$, $E<1/80$, so the last two terms exceed $4E$. For the last row $I-K\tau>8/3$, $E<1/100$, so they exceed $5E$. When $E=0$ they vanish. With $h>7/10$, the seven rows of (31.31) are therefore strictly bounded below, in order, by

$$
\begin{aligned}
 &\frac8{81}\left(\frac{10}3-\frac{91}{50}-\frac7{128}\right)
                +\frac{224}{6561},\\
 &\frac7{64}\left(\frac{84}{25}-\frac{16}9-\frac{39}{512}\right)
                +\frac{343}{16384},\\
 &\frac{39}{256}\left(\frac{247}{75}-\frac{33}{20}-\frac18\right),\\
 &\frac3{16}\left(\frac{17}6-\frac{77}{50}-\frac18\right),\\
 &\frac{55}{256}\left(\frac{315}{128}-\frac{36}{25}-\frac18\right),\\
 &\frac{15}{64}\left(\frac{269}{125}-\frac{34}{25}-\frac1{25}\right)
                       =\frac{141}{800},\\
 &\frac{63}{256}\left(\frac{483}{250}-\frac{257}{200}-\frac{49}{1600}\right)
                +\frac{138915}{4194304}.
\end{aligned}
\tag{31.32}
$$

Every displayed rational number is greater than $7/40$. For the first row one uses $2Ih>10/3$, and for the second $2Ih>84/25$, both from the table and (22.13). In the four middle rows the bound $K^2\tau\le1/8$ suffices for the first three, while the fourth uses $K^2\tau\le1/25$. The last row uses $K^2\tau\le49/1600$. The lower bounds for $\tau$ used in (31.32) are
$8/81,7/64,39/256,3/16,55/256,15/64,63/256$. This proves (31.25) on the entire closed population interval. $\square$

**Theorem 31.5 (the uniform sharp original producer endpoint).** For the unchanged four-path producer problem,

$$
 \boxed{\quad
 g(E,U)\ge\kappa\rho(E,U)
 \quad\text{for every }E\in\operatorname{Dens}_2,
                         \ U\in U(4),\qquad
 C_{\mathrm{opt}}=\kappa^{-1}=R_*.
 \quad}
\tag{31.33}
$$

In particular $\nu_\kappa(\theta)\ge0$ for every datum of (30.15), with all of its correlated scalar phases and populations. For every $w\in\mathcal W$ one also has the inherited quantitative bound

$$
 F_\kappa(w,p)\ge(1-\mu(w))\eta_\kappa
 \qquad(0\le p\le1).
\tag{31.34}
$$

**Proof.** Take any phase class in (30.15) and any $p\in[0,1]$. If $p\ge1/2$, the first branch comparison of (31.14) and $r\le r_+$ imply $F_\kappa\ge0$. If $p\le1/9$, its second branch comparison and $r\le r_-$ give the same conclusion. On the intervening interval, (31.15), (31.25) and the original joint-sign average bound give

$$
 \kappa r(w,p)
 \le\kappa(9-A(w)-B(w))<5\kappa<\frac7{40}<G(w,p),
\tag{31.35}
$$

because the residual requires $A+B>4$. Thus $F_\kappa\ge0$ for every population, including both interval junctions, on every correlated phase datum of (30.15). Source Theorem 23.4 gives precisely the required $\nu_\kappa\ge0$. Proposition 30.7 and Theorem 30.6 then establish the full common-phase assertion and its original all-effect, all-actual-unitary consumer. Theorem 30.5 gives (31.34). The lower sharpness sequence and the equivalence with $C_{\mathrm{opt}}=R_*$ are source Theorem 21.3 and (23.22); no new attainability argument is needed.

More explicitly, for any given original $U$, take its actual diagonal $w=\operatorname{diag}(UU_+^\dagger)$ and its actual population $p=b_+^\dagger E^{\mathsf T}b_+$. The same-$U$ comparison (23.14) and (31.34) give

$$
 g(E,U)-\kappa\rho(E,U)
 \ge(1-\mu(w))\eta_\kappa
            +\kappa(1-\operatorname{Tr}(E^2))\ge0.
\tag{31.36}
$$

The proof retains the ordinary transpose, singular and mixed normalized effects, all zero amplitudes or traces, and every actual nondiagonal lift. The two branch comparisons are sufficient inequalities for the original minimum; they never replace that minimum by independently attained optimizer signs. The common rotations in (31.21) and (31.24) each fix the single common scalar phase of a calculation, and introduce no extra coordinate phase quotient.

The shifted support comparisons, their transfer to the two original distance branches, and the uniform intervening gap are deductions for this fixed producer problem (`repo-derived`). Coordinate-disk support, differentiation, the square-root Taylor inequality, completing a real square and the two-by-two positive-matrix criterion are mature intermediate tools. The source identities in Sections 21, 23--26 and 30 are reused with their stated parameter correspondence. Gregoratti--Werner, [*Quantum Lost and Found*, quant-ph/0209025v1, Proposition 8 and (16)--(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8), supply the fixed-Kraus fidelity estimate and polar correction, with $t_j=\operatorname{diag}(R_0b_j)$ and input dimension four; their proposition does not assert (31.33)'s producer-distance bound. Buscemi--Chiribella--D'Ariano, [*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5, Theorem 2 and (9)](https://arxiv.org/html/quant-ph/0504195v5), supply the rank-two four-dimensional correlation example, entrywise conjugate to the Schrödinger record here. Their random-unitary and perfect-correction conclusions do not supply the shifted support or population-gap estimates. These source distinctions assert no exhaustive literature-priority claim. $\square$

## 追加锚（本行以下为增补区）

## 32. Exact equality and nonattainment of the sharp producer ratio

Retain the original record and Definitions 11.1 and 23.1 of the [source volume](QUANTUM_REALITY_FOUR_PATH_FULL_RECORD_RECOVERY_BOUND.md). In particular, a normalized positive effect means $E\succeq0$ with $\operatorname{Tr}E=1$, and each original calculation has one actual $U\in U(4)$. The constant $\kappa$ is the smaller root of source Theorem 21.3, and $\gamma=1/25>\kappa$. The global inequality is Theorem 31.5. The question here is its exact equality set, rather than the zero set of $g$ alone.

**Theorem 32.1 (complete original equality set and sharp-ratio nonattainment).** For every $E\in\operatorname{Dens}_2$ and every actual shared $U\in U(4)$,

$$
\boxed{\quad
 g(E,U)=\kappa\rho(E,U)
 \quad\Longleftrightarrow\quad
 (E,U)\in\mathcal S_+\cup\mathcal S_-
 =\{(E_\sigma,\lambda U_\sigma):
          \sigma\in\{+,-\},\ |\lambda|=1\}.
 \quad}
\tag{32.1}
$$

Consequently every original pair with $\rho(E,U)>0$ satisfies

$$
 g(E,U)>\kappa\rho(E,U),\qquad
 \frac{\rho(E,U)}{g(E,U)}<R_*=\kappa^{-1}.
\tag{32.2}
$$

The supremum $C_{\mathrm{opt}}=R_*$ from Theorem 31.5 is therefore not attained on the domain where the quotient is defined.

**Proof.** For the given original pair, use precisely its actual reduced data

$$
 w=\operatorname{diag}(UU_+^\dagger),\qquad
 p=b_+^\dagger E^{\mathsf T}b_+,\qquad
 \epsilon=1-\operatorname{Tr}(E^2).
$$

The ordinary transpose here is the one in source (23.9); no new effect is substituted. Write $F_\kappa=G-\kappa r$ as in (30.2). Source (23.14) and Theorem 31.5 give

$$
 g-\kappa\rho\ \ge F_\kappa(w,p)+\kappa\epsilon
 \ \ge (1-\mu(w))\eta_\kappa+\kappa\epsilon\ \ge0,
 \qquad \eta_\kappa>0.
\tag{32.3}
$$

If the original pair is an equality pair, then $F_\kappa(w,p)=0$ and $\epsilon=0$. Moreover, source (23.5) gives $\rho=r$ and hence $g=G$. Equation (32.3) also forces $\mu(w)=1$: mixed effects and every actual lift with a diagonal modulus below one already have a strictly positive remainder. For the actual unitary $V=UU_+^\dagger$, all four diagonal moduli then equal one, so its row norms force its off-diagonal entries to vanish and $U=\operatorname{diag}(w)U_+$. This exclusion includes arbitrary actual nondiagonal lifts; it is a consequence of equality, not a restriction of the original domain.

If $A(w)+B(w)\le4$, source Theorem 26.4 already supplies exactly the equality classes in (32.1), including its boundary. It remains to examine $A+B>4$.

For $1/9\le p\le1/2$, Lemma 31.4 and the joint-sign average bound $r\le9-A-B$ give

$$
 G>\frac7{40}>5\kappa>\kappa r,
\tag{32.4}
$$

where $0<\kappa<7/200$ is (31.15). Thus no equality occurs in this closed population interval. Its two endpoints are included.

Suppose next that $1/2\le p\le1$. Put $\alpha=\sqrt p$, $\beta=\sqrt{1-p}$ and $t=\alpha u(w)+\beta v(w)$. If $t\le2$, then $G\ge e^2-4>2/5$, whereas $\kappa r\le\kappa r_+\le10\kappa<7/20$; the inequality is strict. If $t>2$, retain the actual support parameter $z=t$ and the same auxiliary $y\in[0,\pi/2)$ from (31.21)--(31.22):

$$
 \varepsilon=\kappa/t,\qquad
 e^{iy}=\frac{h\alpha-\varepsilon+ih\beta}
               {|h\alpha-\varepsilon+ih\beta|},\qquad
 \delta=2(1-\cos y).
$$

Its real part is positive by (31.7). Let $w_0=w^+(y)$ be the actual scalar family (31.17), and use its source amplitude
$t_0=\alpha(2h\cos y+2c)+2h\beta\sin y$.
Define the auxiliary difference

$$
 H_+(y,p)=G(w_0,p)-\kappa r_+(w_0,p).
$$

The support comparison before discarding the real square is

$$
 t^2-2\kappa A(w)
 \le2tt_0-t^2-2\kappa A(w_0)
 =t_0^2-2\kappa A(w_0)-(t-t_0)^2.
$$

Subtracting this inequality from $D(p)-\kappa(10-2p)$, and then retaining the actual joint-sign minimum, yields

$$
 \boxed{\quad
 F_\kappa(w,p)\ge
 H_+(y,p)+(t-t_0)^2+\kappa\bigl(r_+(w,p)-r(w,p)\bigr).
 \quad}
\tag{32.5}
$$

The strictness of the family term is already contained in the matrix used to prove the first line of (31.18). Specifically, it is source (24.17) evaluated at
$u_0=d-h\delta$, $v_0^2=2\delta-\delta^2/2$, with $0\le\delta\le2$ as established in Theorem 31.3. Its leading entry is
$\delta(2(dh-\kappa)-\delta/2)>0$ for $\delta>0$, and its determinant is the source identity $J\delta^2$ with $J>21/10$. Thus that matrix is positive definite when $\delta>0$. At $\delta=0$ it is $\operatorname{diag}(0,e^2-2\kappa)$, with $e^2-2\kappa>0$. Its value on $(\sqrt p,\sqrt{1-p})$ is exactly $H_+(y,p)$, so

$$
 H_+(y,p)\ge0,\qquad
 H_+(y,p)=0\quad\Longleftrightarrow\quad
 \delta=0,\ p=1.
\tag{32.6}
$$

This uses the supplied full-interval scalar matrix, without extending a cap assumption to the actual $w$.

Every term on the right of (32.5) is nonnegative. Equality therefore forces $p=1$, $y=0$ and $t=t_0=d$. It follows that $G=d^2-t^2=0$. For the original equality pair we already have $g=G$, so source Lemma 11.2 gives the original optimizer class. Since $p=1$, this class is $\mathcal S_+$, by the certificate-basis correspondence (23.9)--(23.10). It has $A+B=4$, and hence cannot lie in the region $A+B>4$ under consideration.

Finally suppose $0\le p\le1/9$. Put $\alpha=\sqrt{1-p}$, $\beta=\sqrt p$, and now $t=\alpha v(w)+\beta u(w)$, which is the same reduced amplitude as before. The case $t\le2$ is strictly separated just as above, using $r\le r_-\le10$. For $t>2$, use exactly the fixed coordinates and support comparison (31.23)--(31.24):

$$
 \widetilde w=(w_1,-w_2,iw_3,-iw_4),\qquad
 \varepsilon=\kappa/t,\qquad
 e^{iy}=\frac{s\alpha-\varepsilon+ic\beta}
               {|s\alpha-\varepsilon+ic\beta|}.
$$

Here $0\le y<\pi/2$ by (31.10). With $\delta=2(1-\cos y)$, let $w_0=w^-(y)$ and
$t_0=\alpha(2h+2s\cos y)+2c\beta\sin y$ as in the source comparison. The second line of (31.18) supplies

$$
 H_-^\gamma(y,p):=G(w_0,p)-\gamma r_-(w_0,p)\ge0,
 \qquad
 r_-(w_0,p)=2(p+\delta).
$$

Retaining the real square in (31.24), and using this stronger family comparison before returning to $\kappa$, gives

$$
 \boxed{\quad
 F_\kappa(w,p)\ge
 H_-^\gamma(y,p)+2(\gamma-\kappa)(p+\delta)
 +(t-t_0)^2+\kappa\bigl(r_-(w,p)-r(w,p)\bigr).
 \quad}
\tag{32.7}
$$

All four terms are nonnegative. Since $\gamma>\kappa$, equality forces $p=0$ and $\delta=0$. The square then forces $t=t_0=e$, so $G=e^2-t^2=0$. Again $g=G$ for the original equality pair, and source Lemma 11.2, with $p=0$ in (23.9)--(23.10), gives exactly $\mathcal S_-$. Its trace sum is also $A+B=4$. Thus this population end contributes no equality in $A+B>4$.

These cases exhaust all actual populations and all trace data. Conversely each pair in $\mathcal S_+\cup\mathcal S_-$ has $g=\rho=0$ by source Lemma 11.2, proving both directions of (32.1). That lemma also gives $g>0$ when $\rho>0$, so division proves (32.2). The supremum and its lower sharpness sequence are reused from Theorem 31.5 and source Theorem 21.3; strictness at every positive-distance original pair proves nonattainment. $\square$

The two retained-square inequalities (32.5) and (32.7) propagate strictness from the supplied scalar families to the actual datum. Their consumers are the two population-end exclusions in the complete original equality proof. The nonnegative terms $r_\pm-r$ keep the actual joint optimizer-sign minimum, including ties; they do not assume which branch minimizes it. Each use of (31.21) or (31.24) takes only the original one common scalar rotation. The fixed transformation to $\widetilde w$ is the negative-optimizer correspondence, not an additional phase quotient. Each auxiliary $w^\pm(y)$ has the source actual lift $\operatorname{diag}(w^\pm(y))U_+$; it enters a one-sided support comparison and supplies no separately chosen control to any column of the original effect.

No division by a trace, by $P$ or by $Q$ occurs. The sole amplitude division is restricted to $t>2$; zero amplitudes and zero traces are covered by the same comparisons and the $t\le2$ case. The original bridge (32.3) retains singular and mixed effects, all populations, and every actual lift. Equality in the quadratic tangent form of source Section 22 and convergence of the actual sharpness sequence are different statements from (32.1). In particular, the source sequence has $\rho>0$, approaches an optimizer and satisfies $\rho/g\to R_*$. Along it $g-\kappa\rho\to0$, so the pointwise strict inequality supplies neither a uniform positive additive gap on the punctured domain nor a smaller global sharp ratio.

The equality propagation and its original nonattainment conclusion are deductions for the fixed producer problem (repo-derived). The optimizer zero set, limiting sequence, tangent form, trace-triangle equality theorem, full-interval scalar matrices and global bound remain the results of source Sections 11, 21--26 and continuation Sections 30--31. The added step is the propagation of equality through the support comparisons with their real-square and joint-branch remainders; nonnegativity of the endpoint or knowledge of the zero set alone does not supply this step.

For the external source correspondence, Gregoratti--Werner, [*Quantum Lost and Found*, quant-ph/0209025v1, Proposition 8 and (15)--(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8), give the fixed-Kraus fidelity bound and its polar-recovery equality condition. In the present notation their $t_j$ is $\operatorname{diag}(R_0b_j)$ and their input dimension is four; that equality concerns the fixed-Kraus correction bound, rather than equality in $g-\kappa\rho$. It does not permit different feedbacks for the columns of an unchanged original effect. Buscemi--Chiribella--D'Ariano, [*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5, Theorem 2 and (9)](https://arxiv.org/html/quant-ph/0504195v5), give the random-unitary context and rank-two four-dimensional correlation example. Their Heisenberg matrix (9) is entrywise conjugate to the fixed Schrödinger record here. Those results supply the record correspondence and correction context, not this producer-metric equality classification. These identified source statements and the repository results delimit the reuse and the new deduction; they imply no exhaustive literature-absence or priority claim.

## 追加锚（本行以下为增补区）

## 33. The sharp prescribed-distance strictness asymptotic

**Definition 33.1 (the original strictness envelope).** Retain the fixed record, ordinary transpose, normalized positive effects, actual shared feedback and joint scalar-quotiented distance of source Definition 11.1. On the unchanged space $\mathcal K=\operatorname{Dens}_2\times U(4)$ put

$$
\begin{aligned}
 f(E,U)&=g(E,U)-\kappa\rho(E,U),\\
 m(\xi)&=\inf\{f(E,U):(E,U)\in\mathcal K,\ \rho(E,U)=\xi\},
 \qquad \xi>0.
\end{aligned}
\tag{33.1}
$$

The infimum of an empty level is understood to be $+\infty$. Keep $h,c,s,d,e$ and $\kappa$ from source Sections 21--23, and define

$$
\begin{aligned}
 a&=dh-\kappa,& B&=e^2-2\kappa,\\
 J&=\frac{d^2-e^2}{2}+(5-4dh)\kappa+4\kappa^2,&
 C&=\frac{JB}{4(B+2a)^2}.
\end{aligned}
\tag{33.2}
$$

Here $B$ without an argument is a constant; $B(w)$ retains the trace-modulus meaning of source (23.2). Source (24.19)--(24.22) give $aB=d^2$, $B>0$ and $J>21/10$, hence $a>0$ and $C>0$. The global nonnegativity of $f$ and its exact zero set are the supplied Theorems 31.5 and 32.1.

**Theorem 33.2 (sharp leading envelope on every sufficiently small original distance level).** There is $\xi_0>0$ such that every level $\rho=\xi$ with $0<\xi<\xi_0$ is nonempty, its infimum in (33.1) is attained, and

$$
\boxed{\qquad
 m(\xi)=\frac{JB}{4(B+2a)^2}\,\xi^2+o(\xi^2)
 \quad(\xi\downarrow0).
 \qquad}
\tag{33.3}
$$

The lower asymptotic is uniform over the entire original domain: for every $\varepsilon>0$ there is $\eta>0$ such that

$$
 f(E,U)\ge(C-\varepsilon)\rho(E,U)^2
 \quad\text{whenever }(E,U)\in\mathcal K,
 \quad 0<\rho(E,U)<\eta.
\tag{33.4}
$$

There are actual original pairs at every $0<\xi<\xi_0$ with $\rho=\xi$ and $f=C\xi^2+O(\xi^3)$. These pairs use one shared $U$ and the original effect transpose.

More precisely, consider any sequence of original pairs with $0<\rho\to0$ and $f=O(\rho^2)$. For its actual data

$$
 w=\operatorname{diag}(UU_+^\dagger),\qquad
 p=b_+^\dagger E^{\mathsf T}b_+,\qquad
 \epsilon=1-\operatorname{Tr}(E^2),
$$

one eventually has $A(w)\ge A_0=2+\sqrt{8/3}$, and

$$
 \epsilon=O(\rho^2),\qquad
 \frac{4-A(w)}{\rho}\longrightarrow\frac{B}{2(B+2a)},\qquad
 \frac{1-p}{\rho}\longrightarrow\frac{a}{B+2a}.
\tag{33.5}
$$

If in addition $f/\rho^2\to C$, then $\epsilon=o(\rho^2)$. These necessary conditions permit rank changes and make no assertion that every exact minimizer has the form of the upper family.

**Proof.** All reduced data used below are evaluated on the given original pair. Source Theorem 23.2 gives, including for singular and mixed effects and every actual nondiagonal lift,

$$
 \rho=r(w,p)-\epsilon,\qquad
 f\ge G(w,p)-\kappa r(w,p)+\kappa\epsilon,
 \qquad \epsilon\ge0.
\tag{33.6}
$$

First localize the distance levels without restricting their competitors. If $\rho(E,U)=\xi$ and $\sigma$ is a minimizing sign in Definition 11.1, its feedback-distance summand is at most $\xi$. The exact common-scalar minimum (23.11) implies

$$
 |\operatorname{Tr}(UU_\sigma^\dagger)|\ge4-\frac\xi2.
\tag{33.7}
$$

For sufficiently small $\xi$, every original pair therefore lies in at least one of the two supplied caps $A(w)\ge A_0$ or $B(w)\ge23/6$. In the latter cap, source Theorem 25.3 gives

$$
 f(E,U)\ge(\gamma-\kappa)\xi,\qquad
 \gamma=1/25>\kappa.
\tag{33.8}
$$

Fix a finite $M>C$. For all sufficiently small positive $\xi$, an original pair satisfying $f\le M\xi^2$ cannot belong to the negative cap, by (33.8). Every such pair consequently lies in the positive cap. This argument applies to every bounded-ratio sequence, with a fixed $M$ larger than its eventual bound.

On that positive cap put $\delta=4-A(w)$ and $q=1-p$. Source Lemma 24.2, including its joint-sign conclusion, gives

$$
 \rho=2(q+\delta)-\epsilon,\qquad
 G(w,p)\ge G(w^{(4-\delta)},p).
\tag{33.9}
$$

The effect-distance summand is $2q-\epsilon\ge0$ by source (23.10), so $0\le\delta\le\xi/2$. Thus small original distance already makes $\delta$ small, independently of any strictness estimate.

For $\delta\ge0$ sufficiently small define the scalar quantities

$$
\begin{aligned}
 u_\delta&=d-h\delta,&
 v_\delta&=\sqrt{2\delta-\delta^2/2},\\
 \beta_\delta&=B-2\kappa\delta-v_\delta^2
             =B-2(1+\kappa)\delta+\delta^2/2,&
 \ell_\delta&=u_\delta v_\delta.
\end{aligned}
\tag{33.10}
$$

In particular $\beta_\delta\to B>0$, and we may choose the distance neighborhood so that $\beta_\delta\ge B/2$. The simultaneous cap envelopes (24.9)--(24.16) and (33.6) imply

$$
 f(E,U)\ge H_\delta(q)+\kappa\epsilon,
\tag{33.11}
$$

where the value of the supplied scalar matrix (24.17) is

$$
 H_\delta(q)
 =\left(2a\delta-\frac{\delta^2}{2}\right)(1-q)
   +\beta_\delta q-2\ell_\delta\sqrt{q(1-q)}.
\tag{33.12}
$$

The determinant identity (24.23) is exactly

$$
 \left(2a\delta-\frac{\delta^2}{2}\right)\beta_\delta
       -\ell_\delta^2=J\delta^2.
\tag{33.13}
$$

Completing the square in (33.12), with the positive denominator $\beta_\delta$, thus gives the distance-sensitive remainder

$$
\boxed{\quad
 f(E,U)\ge
 \beta_\delta\left(\sqrt q-
       \frac{\ell_\delta}{\beta_\delta}\sqrt{1-q}\right)^2
 +\frac{J\delta^2}{\beta_\delta}(1-q)
 +\kappa\epsilon.
 \quad}
\tag{33.14}
$$

The comparison preceding this square completion is a one-sided bound on the actual pair; it does not replace its feedback or its effect. Formula (33.14) remains valid at $\delta=0$, $q=0$ and $q=1$. No actual trace, amplitude or eigenvalue of an effect occurs as a divisor.

We now extract the scale from (33.14), rather than assuming an expansion of a minimizing curve. Restrict temporarily to the pairs with $f\le M\xi^2$, where $\xi=\rho>0$. Since all three terms in (33.14) are nonnegative, (33.9) gives uniformly on these pairs

$$
 0\le\epsilon\le\frac{M}{\kappa}\xi^2,\qquad
 q+\delta=\frac{\xi+\epsilon}{2}
         =\frac\xi2+O_M(\xi^2).
\tag{33.15}
$$

In particular $q,\delta=O_M(\xi)$. The square term and $\beta_\delta\ge B/2$ yield

$$
 \sqrt q-\frac{\ell_\delta}{\beta_\delta}\sqrt{1-q}
       =O_M(\xi).
\tag{33.16}
$$

From (33.10), uniformly down to $\delta=0$,

$$
 \frac{\ell_\delta}{\beta_\delta}
 =\sqrt\delta\left(\frac{\sqrt2d}{B}+O(\delta)\right).
\tag{33.17}
$$

Because $q,\delta=O_M(\xi)$, equations (33.16)--(33.17) imply
$\sqrt q-(\sqrt2d/B)\sqrt\delta=O_M(\xi)$. Multiplication by the sum of these two nonnegative square-root terms, which is $O_M(\sqrt\xi)$, proves

$$
 q-\frac{2d^2}{B^2}\delta=O_M(\xi^{3/2}),\qquad
 \frac{2d^2}{B^2}=\frac{2a}{B}.
\tag{33.18}
$$

This reasoning never divides by $q$ or $\delta$, so it also rules out exceptional zero-coordinate subsequences. Combining (33.18) with (33.15) gives

$$
 \delta=\frac{B}{2(B+2a)}\xi+O_M(\xi^{3/2}),\qquad
 q=\frac{a}{B+2a}\xi+O_M(\xi^{3/2}).
\tag{33.19}
$$

In particular the scale of $\delta$ is forced to be that of $\xi$, with a positive coefficient. The determinant remainder in (33.14) now satisfies

$$
 \frac{J\delta^2}{\beta_\delta}(1-q)
 =\frac{JB}{4(B+2a)^2}\xi^2+O_M(\xi^{5/2}).
\tag{33.20}
$$

Indeed, $(1-q)/\beta_\delta=B^{-1}+O_M(\xi)$, and (33.19) determines $\delta^2$ to error $O_M(\xi^{5/2})$. Consequently there is a finite $K_M$ such that all these original pairs satisfy

$$
 f(E,U)\ge C\xi^2+\kappa\epsilon-K_M\xi^{5/2}.
\tag{33.21}
$$

Every constant in (33.15)--(33.21) depends only on the fixed record and $M$, not on the pair or its parametrization. With the fixed choice $M>C$, the complementary pairs $f>M\xi^2$ already satisfy (33.4). Thus (33.21) proves the uniform all-original-pairs lower asymptotic (33.4). Applied to any bounded-ratio sequence, it also proves (33.5); if its ratio tends to $C$, division of (33.21) by $\xi^2$ forces $\epsilon/\xi^2\to0$. This establishes the rank-changing comparison without replacing a mixed effect by its dominant eigenprojection.

For the matching upper behavior, take a small real $\delta\ge0$, put

$$
 x_\delta=1-\frac\delta2,\qquad
 y_\delta=\sqrt{\delta-\delta^2/4},\qquad
 w_\delta=(x_\delta+iy_\delta,\ x_\delta-iy_\delta,\ 1,\ 1),
 \qquad U_\delta=\operatorname{diag}(w_\delta)U_+.
\tag{33.22}
$$

Each diagonal entry has modulus one, so $U_\delta$ is an actual single unitary. This is the simultaneous-envelope realization (24.15), for which

$$
 A(w_\delta)=4-\delta,\qquad
 P(w_\delta)=u_\delta,\qquad Q(w_\delta)=iv_\delta.
\tag{33.23}
$$

With $\beta_\delta,\ell_\delta$ as in (33.10), define

$$
\begin{aligned}
 S_\delta&=\beta_\delta^2+\ell_\delta^2,\qquad
 q_\delta=\frac{\ell_\delta^2}{S_\delta},\\
 \psi_\delta&=\frac{\beta_\delta b_+-i\ell_\delta b_-}
                    {\sqrt{S_\delta}},\qquad
 E_\delta=\overline{\psi_\delta}\,
                      \overline{\psi_\delta}^{\dagger}.
\end{aligned}
\tag{33.24}
$$

The source certificate vectors $b_+,b_-$ are orthonormal, so $E_\delta$ is a normalized rank-one positive effect, with actual population $p_\delta=1-q_\delta$ and impurity zero. Equation (33.23) shows directly that its relative phase aligns the two original amplitudes:

$$
 \sqrt{1-q_\delta}\,P(w_\delta)
       -i\sqrt{q_\delta}\,Q(w_\delta)
 =u_\delta\sqrt{1-q_\delta}+v_\delta\sqrt{q_\delta}.
\tag{33.25}
$$

Thus source (22.1), or equivalently (23.12)--(23.13), gives $g(E_\delta,U_\delta)=G(w_\delta,p_\delta)$ for this same actual $U_\delta$. The common-scalar distance and the joint sign are those of (24.9). For (33.24), the square in (33.14) vanishes, since $\beta_\delta>0$ and $\ell_\delta\ge0$. Accordingly these original pairs have the exact values

$$
\begin{aligned}
 \Delta(\delta):=\rho(E_\delta,U_\delta)
   &=2(\delta+q_\delta),\\
 f(E_\delta,U_\delta)
   &=H_\delta(q_\delta)
     =\frac{J\delta^2\beta_\delta}
            {\beta_\delta^2+\ell_\delta^2}.
\end{aligned}
\tag{33.26}
$$

Both equalities include $\delta=0$, where $\psi_0=b_+$ and $U_0=U_+$. For every positive sufficiently small $\delta$ they give positive distance and positive strictness. These identities use the original ordinary transpose, as witnessed by the conjugation in (33.24), and one common feedback for the entire effect.

To obtain every prescribed small level, observe that $\ell_\delta^2=(d-h\delta)^2(2\delta-\delta^2/2)$ and $\beta_\delta$ are polynomials in $\delta$. Hence $q_\delta$ and $\Delta(\delta)$ are smooth rational functions near zero with positive denominator, and

$$
 q_\delta=\frac{2d^2}{B^2}\delta+O(\delta^2)
          =\frac{2a}{B}\delta+O(\delta^2),\qquad
 \Delta'(0)=\frac{2(B+2a)}{B}>0.
\tag{33.27}
$$

Continuity of the derivative gives $\delta_0>0$ on which $\Delta$ is strictly increasing. Shrink $\delta_0$ to retain the positive cap and $\beta_\delta>0$, and put $\xi_0=\Delta(\delta_0)$. Since $\Delta(0)=0$, every $0<\xi<\xi_0$ has a unique $\delta\in(0,\delta_0)$ with $\Delta(\delta)=\xi$. In particular the original distance levels in this interval are nonempty. Equations (33.26)--(33.27) give

$$
 f(E_\delta,U_\delta)=\frac{J}{B}\delta^2+O(\delta^3)
   =C\Delta(\delta)^2+O(\Delta(\delta)^3).
\tag{33.28}
$$

This proves the asserted exact-level upper asymptotic. Smoothness is used only for the explicit rational distance of this constructed family; no regularity or form of an unknown minimizer is assumed.

Finally, $\mathcal K$ is compact and $g,\rho$ are continuous by source Definition 11.1 and Lemma 11.2's setup. Each nonempty level is therefore compact and $f$ attains its infimum there. The uniform lower bound (33.4) and the actual exact-level upper bound (33.28) imply (33.3). Since $C>0$, this is the first nonzero scale of the original envelope. The localization (33.7)--(33.8) covers both optimizer classes; (33.6) and (33.14) retain all mixed and singular effects and arbitrary actual nondiagonal lifts. The only scalar quotient is the original one in (23.11). Zero values of the other trace or of $P,Q$, and the endpoints of the population interval, require no extra hypothesis in these comparisons. $\square$

The fixed-record envelope asymptotic and its rank-changing comparison are repo-derived deductions. Their mathematical inputs are source Definition 11.1, Theorem 21.3's value of $\kappa$, the same-feedback identity (22.1), Theorem 23.2, the simultaneous cap comparison of Lemma 24.2, the determinant identity (24.23), and the stronger opposite-cap inequality of Theorem 25.3. The global bound, its equality classification and the quadratic tangent theorem remain the supplied results of Sections 22 and 30--32; the new conclusion follows from converting the determinant remainder into a uniform prescribed-distance lower bound and matching it on every actual small level.

For the external mathematical correspondence, Gregoratti--Werner, [*Quantum Lost and Found*, quant-ph/0209025v1, Proposition 8 and (15)--(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8), supply the fixed-Kraus correction-fidelity bound and polar recovery used in the source volume: $t_j=\operatorname{diag}(R_0b_j)$ and the input dimension is four. Buscemi--Chiribella--D'Ariano, [*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5, Theorem 2 and (9)](https://arxiv.org/html/quant-ph/0504195v5), supply the correlation-record context; their Heisenberg matrix (9) is entrywise conjugate to this fixed Schrödinger record. The prescribed-unitary-diagonal input of source Theorem 23.2 is Thompson's theorem, in [Jasper--Loreaux--Weiss, arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3), with all four singular values equal to one. The upper feedbacks (33.22) are realized directly. These source statements concern the correction context and diagonal realization; the producer distance, determinant remainder and exact-level asymptotic are the source-specific correspondence proved above.

## 追加锚（本行以下为增补区）

## 34. The exact small-distance envelope and all original minimizing pairs

**Definition 34.1 (an unsquared selecting equation).** Retain $m,f,\mathcal K$ from Definition 33.1 and $a,B,J,C$ from (33.2), with the unchanged constants $h,c,s,d,e,\kappa$ of source Sections 21--23. The vectors $b_\pm$ and feedback $U_+$ are exactly those of source (6.7) and (6.3). In particular $aB=d^2$, $a,B,C>0$. Put

$$
 z_* = \frac{B}{B+2a},\qquad
 \eta=\frac14\min\{z_*,1-z_*\},\qquad
 I=(z_*-\eta,z_*+\eta).
\tag{34.1}
$$

Thus $\overline I\subset(0,1)$. For $0\le t<\min\{\delta_*,1/2\}$ and $0\le z\le1$, where $\delta_*$ is source (24.1), define

$$
\begin{aligned}
 \mathcal A(t,z)
 &=\left(2az-\frac{tz^2}{2}\right)(1-t+tz)
   +\left(B-2(1+\kappa)tz+\frac{t^2z^2}{2}\right)(1-z),\\
 \mathcal R(t,z)
 &=z(1-z)\left(2-\frac{tz}{2}\right)(1-t+tz),\\
 \Phi(t,z)
 &=\mathcal A(t,z)-2(d-htz)\sqrt{\mathcal R(t,z)}.
\end{aligned}
\tag{34.2}
$$

Every square root in this section is the nonnegative real square root. On $\overline I$ the radicand is strictly positive, also for all sufficiently small signed $t$. The selecting equation is

$$
 \mathcal E(t,z):=
 \sqrt{\mathcal R(t,z)}\,\partial_z\mathcal A(t,z)
 +2ht\mathcal R(t,z)
 -(d-htz)\partial_z\mathcal R(t,z)=0,
 \qquad z\in I.
\tag{34.3}
$$

Here $\mathcal A,\mathcal R$ are the displayed polynomials, so (34.3) is an explicit equation using polynomial operations and one specified square root. It is not replaced by its square. The interval $I$ is part of the root selection.

**Lemma 34.2 (unique selection and strict increase of the scalar value).** There is $t_0>0$ such that, for every $0\le t<t_0$, equation (34.3) has exactly one root $z(t)$ in $I$. It has $z(0)=z_*$ and extends real analytically across $t=0$. Define

$$
 n(t)=t\Phi(t,z(t)),\qquad n(0)=0.
\tag{34.4}
$$

For $0<t<t_0$ one has the exact identity

$$
 n(t)=\min_{0\le\delta\le t}H_\delta(t-\delta),
\tag{34.5}
$$

where $H$ is the supplied expression (33.12). The minimum is unique, at $\delta=tz(t)$. After reducing $t_0$ if necessary, $n$ is strictly increasing on $[0,t_0)$.

**Proof.** Substitution of $\delta=tz$, $q=t(1-z)$ into (33.12) gives, for $t>0$,

$$
 H_{tz}(t(1-z))=t\Phi(t,z).
\tag{34.6}
$$

Indeed the cross term divided by $t$ is
$-2(d-htz)\sqrt{z(1-z)(2-tz/2)(1-t+tz)}$; the two diagonal terms give $\mathcal A$. At $t=0$ the continuous extension is

$$
\begin{aligned}
 L(z):=\Phi(0,z)
 &=2az+B(1-z)-2d\sqrt{2z(1-z)}\\
 &=\left(\sqrt{2az}-\sqrt{B(1-z)}\right)^2.
\end{aligned}
\tag{34.7}
$$

The second identity uses $aB=d^2$. Thus $L$ has its unique minimum zero on $[0,1]$ at $z_*$. In the open interval,

$$
 L''(z)=\frac{d}{\sqrt2\,[z(1-z)]^{3/2}}>0.
\tag{34.8}
$$

In particular $L'(z_*-\eta)<0<L'(z_*+\eta)$ and $L''$ has a positive minimum on $\overline I$. The function $\Phi$ is real analytic in a neighborhood of $\{0\}\times\overline I$. Continuity of its first two $z$ derivatives therefore gives, for all sufficiently small signed $t$,

$$
 \partial_z\Phi(t,z_*-\eta)<0<
 \partial_z\Phi(t,z_*+\eta),\qquad
 \partial_z^2\Phi(t,z)>0\quad(z\in\overline I).
\tag{34.9}
$$

There is exactly one zero of $\partial_z\Phi(t,\cdot)$ in $I$. Direct differentiation gives

$$
 \mathcal E(t,z)=\sqrt{\mathcal R(t,z)}\,
                         \partial_z\Phi(t,z),
\tag{34.10}
$$

so it is exactly the root specified in (34.3). Its $z$ derivative as a zero of $\partial_z\Phi$ is nonzero by (34.9). The real analytic implicit function theorem gives the asserted analytic function $z(t)$, without assuming a minimizing curve.

It remains to exclude other scalar minima, including the two endpoints. The expressions (34.2) are continuous on $[0,t_1]\times[0,1]$ for some $t_1>0$, and $\Phi(t,\cdot)\to L$ uniformly on $[0,1]$. Since $L$ is strictly positive on the compact complement of $I$ and vanishes at $z_*$, every global minimum of $\Phi(t,\cdot)$ belongs to $I$ when $t\ge0$ is sufficiently small. Its derivative vanishes there, and (34.9) makes it the unique root $z(t)$. This proves (34.5) and its uniqueness, including the exclusion of $\delta=0,t$ when $t>0$.

For the last assertion, first realize every scalar competitor in (34.5) by the original pair. For $\delta,q\ge0$ with $\delta+q=t$, put

$$
\begin{aligned}
 x&=1-\delta/2,& y&=\sqrt{\delta-\delta^2/4},\\
 w&=(x+iy,x-iy,1,1),&
 U&=\operatorname{diag}(w)U_+,\\
 \psi&=\sqrt{1-q}\,b_+-i\sqrt q\,b_-,&
 E&=\bar\psi\bar\psi^\dagger.
\end{aligned}
\tag{34.11}
$$

These are actual original normalized effects and unitaries: $x^2+y^2=1$, and $b_\pm$ are orthonormal. Source (24.9), (24.15) and (23.12)--(23.13) give, with this same $U$,

$$
 \rho(E,U)=2(\delta+q)=2t,\qquad
 f(E,U)=H_\delta(q).
\tag{34.12}
$$

In particular $m(2t)\le n(t)$. Conversely the actual exact-level upper witnesses (33.22)--(33.27) have precisely the form (34.11), with $q+\delta=t$. Their supplied estimate (33.28) and Theorem 33.2 consequently give

$$
 4Ct^2+o(t^2)=m(2t)\le n(t)
                 \le4Ct^2+O(t^3).
\tag{34.13}
$$

The expression (34.4) is real analytic across zero. The limit in (34.13) determines its Taylor coefficients through degree two, and hence

$$
 n(t)=4Ct^2+O(t^3),\qquad n'(t)=8Ct+O(t^2).
\tag{34.14}
$$

Since $C>0$, its derivative is positive for all sufficiently small positive $t$. Its value at zero is zero, proving strict increase on the claimed interval. This use of the supplied asymptotic establishes monotonicity of the scalar value; it does not assume equality between that value and the original envelope. $\square$

**Theorem 34.3 (exact original envelope and necessary-and-sufficient minimizing realizations).** There is $\xi_1>0$ such that the following statements hold for every $0<\xi<\xi_1$. Set $t=\xi/2$ and let $z(t)$ be the unique root (34.3) in the fixed interval (34.1). Then

$$
 \boxed{\quad
 m(\xi)=t\left[
 \mathcal A(t,z(t))
 -2(d-htz(t))\sqrt{\mathcal R(t,z(t))}\right].
 \quad}
\tag{34.15}
$$

This is a directly determining selected-root value: (34.1)--(34.3) contain no infimum and have exactly one admitted root at each such $t$.

All minimizing original pairs are as follows. Define

$$
\begin{aligned}
 \delta&=tz(t),& q&=t(1-z(t)),\\
 x&=1-\delta/2,& y&=\sqrt{\delta-\delta^2/4},\\
 w_\sigma&=(x+\sigma iy,x-\sigma iy,1,1),&
 \psi_\sigma&=\sqrt{1-q}\,b_+-\sigma i\sqrt q\,b_-,
 \qquad \sigma\in\{+1,-1\}.
\end{aligned}
\tag{34.16}
$$

An original pair with $\rho(E,U)=\xi$ satisfies $f(E,U)=m(\xi)$ if and only if, for one of these two signs and one scalar $|\lambda|=1$,

$$
 \boxed{\qquad
 E=\overline{\psi_\sigma}\,
                  \overline{\psi_\sigma}^{\dagger},\qquad
 U=\lambda\operatorname{diag}(w_\sigma)U_+.
 \qquad}
\tag{34.17}
$$

Thus all minimizing effects on this interval have rank one, and all their actual feedbacks have the displayed diagonal form. There are exactly two minimizing pairs modulo the original common scalar feedback phase. These restrictions are conclusions on the entire $\operatorname{Dens}_2\times U(4)$ domain.

**Proof.** Fix $M>C$. Reduce the positive interval in Lemma 34.2 as needed. By (34.14), for all sufficiently small $\xi>0$,

$$
 n(\xi/2)<M\xi^2.
\tag{34.18}
$$

We prove a matching lower bound for every original pair of distance $\xi$. Pairs with $f\ge M\xi^2$ already satisfy a strict lower bound by (34.18). Consider any remaining pair, with $f<M\xi^2$, without any rank or feedback restriction. Write its actual data as

$$
 w=\operatorname{diag}(UU_+^\dagger),\qquad
 p=b_+^\dagger E^{\mathsf T}b_+,\qquad
 q=1-p,\qquad
 \epsilon=1-\operatorname{Tr}(E^2)\ge0.
\tag{34.19}
$$

The supplied localization (33.7)--(33.8) places every such pair in the positive cap for all sufficiently small $\xi$. Explicitly, the minimizing sign of the original distance gives $A(w)\ge4-\xi/2$ or $B(w)\ge4-\xi/2$. If $\xi<\min\{2\delta_*,1/3\}$, this lies in the positive cap $A\ge A_0$ or the opposite cap $B(w)\ge23/6$. In the opposite cap, source Theorem 25.3 gives $f\ge(1/25-\kappa)\xi$. This contradicts $f<M\xi^2$ when $\xi<(1/25-\kappa)/M$. The given actual pair therefore belongs to the positive cap.

On that cap put $\delta=4-A(w)$. Source Lemma 24.2 and (33.11) give the exact distance and the one-sided bound

$$
 \xi=2(q+\delta)-\epsilon,\qquad
 f\ge H_\delta(q)+\kappa\epsilon.
\tag{34.20}
$$

The scalar $H_\delta(q)$ is nonnegative by source Lemma 24.3 applied to the simultaneous-envelope realization (24.15). Therefore

$$
 0\le\epsilon\le\frac{M}{\kappa}\xi^2,\qquad
 T:=q+\delta=\frac{\xi+\epsilon}{2}
 \le\frac\xi2+\frac{M}{2\kappa}\xi^2.
\tag{34.21}
$$

Choose $\xi_1>0$ small enough to satisfy all preceding conditions and to make the last upper bound smaller than $t_0$. Every such choice exists because the constants are positive and fixed. Since $0\le\delta\le T$ and $q=T-\delta$, Lemma 34.2 now applies at this actual value $T$. It yields the lower certificate

$$
 \boxed{\quad
 f(E,U)\ge n(T)+\kappa\epsilon
       \ge n(\xi/2)+\kappa\epsilon
       \ge n(\xi/2).
 \quad}
\tag{34.22}
$$

The middle inequality is precisely the proved strict increase of $n$, with $T=(\xi+\epsilon)/2$. It compares scalar values in a bound on the unchanged pair; it does not replace a mixed effect by a pure effect at the wrong prescribed level. Together with (34.18), this proves $f\ge n(\xi/2)$ for every original competitor, including singular and mixed effects and arbitrary actual nondiagonal lifts.

For the upper bound use (34.16)--(34.17), with either sign and any $\lambda$. Here $0<z(t)<1$ makes $\delta,q>0$; both are small, and $q<1$. All diagonal entries of $w_\sigma$ have modulus one, and $\psi_\sigma$ has norm one. Substitution gives

$$
\begin{aligned}
 A(w_\sigma)&=4-\delta,&
 P(w_\sigma)&=d-h\delta=u_\delta,\\
 Q(w_\sigma)&=\sigma i\sqrt{2\delta-\delta^2/2}
                 =\sigma i v_\delta.
\end{aligned}
\tag{34.23}
$$

The relative phase $-\sigma i$ in $\psi_\sigma$ aligns the two amplitudes for this same actual $U$. Source (23.12)--(23.13) and Lemma 24.2 consequently give

$$
 \rho(E,U)=2(q+\delta)=\xi,\qquad
 f(E,U)=H_\delta(q)=n(t).
\tag{34.24}
$$

Thus the lower bound is attained and proves (34.15). In particular each admitted exact level has an actual same-feedback witness.

It remains to prove that these are all the original minimizers. If $f=n(t)$ at distance $\xi$, (34.18) puts the pair in the preceding low-value case. Equation (34.22), with $\kappa>0$, forces $\epsilon=0$. A positive trace-one two-by-two effect with $1-\operatorname{Tr}(E^2)=0$ has eigenvalues $1,0$, so it has rank one. Now $T=t$, and equality in (34.20)--(34.22) forces $H_\delta(q)=n(t)$. The uniqueness in (34.5) forces exactly the $\delta,q$ of (34.16). In particular $p=1-q>0$, $q>0$, and $\delta>0$.

Both comparisons underlying (34.20) must also be equalities. Indeed they are the nonnegative differences $g-G(w,p)$ from source (23.12) and $G(w,p)-G(w^{(4-\delta)},p)$ from (24.16). Since $u\le u_\delta$, $v\le v_\delta$ and both population square roots are positive, equality in the second comparison gives

$$
 u(w)=u_\delta,\qquad v(w)=v_\delta.
\tag{34.25}
$$

To recover the actual feedback from these equalities, use just one common scalar phase to normalize $\sum_jw_j=A(w)>0$. Set $Y=w_3+w_4$. The source bound (24.10) is

$$
 |hA+(c-h)Y|\le hA+(c-h)|Y|
                       \le hA+2(c-h)=u_\delta.
\tag{34.26}
$$

Here $hA>0$ and $c-h>0$. Equality forces $|Y|=2$ and $Y$ positive real, hence $Y=2$. Because $|w_3|,|w_4|\le1$, it follows that $w_3=w_4=1$. Thus $w_1+w_2=A-2=2x$, with the $x>0$ of (34.16). Write

$$
 w_1=x+\zeta,\qquad w_2=x-\zeta.
\tag{34.27}
$$

Now $Q=2h\zeta$, and the second equality of (34.25) gives $|\zeta|^2=1-x^2=y^2$. The two disk constraints $|x\pm\zeta|\le1$ imply

$$
 |x+\zeta|^2+|x-\zeta|^2
      =2x^2+2|\zeta|^2=2.
\tag{34.28}
$$

Each summand is at most one, so both equal one. Their difference gives $4x\operatorname{Re}\zeta=0$. Since $x>0$ and $y>0$, this means $\zeta=\sigma iy$ for exactly one $\sigma\in\{+1,-1\}$. The normalized diagonal is therefore $w_\sigma$.

In the original phase convention, all four diagonal entries of the actual unitary $V=UU_+^\dagger$ consequently have modulus one. The norm of each row of $V$ is one; its diagonal entry already has that norm. Every off-diagonal entry in that row must vanish. Hence $V=\lambda\operatorname{diag}(w_\sigma)$ for the single scalar undone above, proving the feedback assertion of (34.17) for the actual lift itself.

Finally write the rank-one effect as $E=\bar\psi\bar\psi^\dagger$. Since $p,q>0$, its representing vector can be chosen as

$$
 \psi=\sqrt p\,b_++e^{i\varphi}\sqrt q\,b_-.
\tag{34.29}
$$

Equality in source (23.12), with the nonzero amplitudes in (34.23), requires

$$
 e^{i\varphi}=\frac{P\bar Q}{|P||Q|}=-\sigma i.
\tag{34.30}
$$

The common feedback scalar cancels from this ratio. Thus $\psi$ is exactly $\psi_\sigma$, proving necessity of the effect assertion. Sufficiency was proved in (34.24). The two choices are distinct because $p,q,y>0$, and a common feedback scalar cannot interchange them while preserving the last two normalized diagonal entries. This completes the necessary-and-sufficient classification. $\square$

The selected-root value and equality classification are repo-derived deductions for the fixed record and original metric. Their inputs are source Definition 11.1, the actual same-feedback identity (22.1), the normalized-effect and distance identities (23.9)--(23.12), the simultaneous cap envelopes and joint-sign conclusion of Lemma 24.2, the cap positivity of Lemma 24.3, the opposite-cap estimate of Theorem 25.3, and the supplied asymptotic and actual exact-level upper family of Section 33. Scalar regularity is derived by the implicit function theorem from (34.8)--(34.10); purity, feedback diagonality and phase orientation follow from equality in the all-original-pair lower bound. No regularity, branch choice or rank of an original minimizer is assumed.

For the external source correspondence, Gregoratti--Werner, [*Quantum Lost and Found*, quant-ph/0209025v1, Proposition 8 and (15)--(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8), supply the fixed-Kraus fidelity bound and polar-correction context: their $t_j$ is $\operatorname{diag}(R_0b_j)$ and their input dimension is four. Buscemi--Chiribella--D'Ariano, [*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5, Theorem 2 and (9)](https://arxiv.org/html/quant-ph/0504195v5), supply the correlation-record context; their Heisenberg matrix (9) is entrywise conjugate to this fixed Schrödinger record. The prescribed-diagonal theorem used in source Theorem 23.2 is Thompson's theorem as stated by [Jasper--Loreaux--Weiss, arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3), with all four singular values equal to one. These are intermediate source correspondences, not a formula for Definition 33.1's producer metric. The witnesses here are directly realized, and the equality proof concerns the actual unitary, rather than an auxiliary control.

The interval in Theorem 34.3 is existentially positive; its maximal endpoint is not specified. All its prescribed positive levels and all their original minimizing pairs are determined by (34.1)--(34.3) and (34.15)--(34.17). The joint optimizer sign is the positive sign because of the proved cap localization and source (24.14). The sign $\sigma$ in (34.16) is a phase orientation inside that cap, not a separately chosen optimizer sign. Only the original one common scalar feedback phase is quotiented. The conclusions concern the fixed record and this local distance interval; they make no literature-priority claim or assertion about the finite-distance envelope outside it.

## 追加锚（本行以下为增补区）

## 35. The maximal original distance, its exact envelope and a terminal obstruction

**Definition 35.1 (endpoint constants and actual data).** Retain the fixed record, $\mathcal K$, $g,\rho,f,m$ and $h,c,s,d,e,\kappa$ from source Definition 11.1, source Definition 23.1 and Definition 33.1. In particular, effects are arbitrary normalized positive semidefinite matrices, the transpose is ordinary transpose, and each original effect has one actual shared feedback. Put

$$
 \alpha=c-h,\qquad \beta=h-s,\qquad
 D_0=d^2-e^2>0,\qquad H=\frac{d^2+e^2}{2},\qquad
 U_* =\operatorname{diag}(-i,i,1,-1)U_+.
\tag{35.1}
$$

For an original pair use its actual coordinates

$$
 w=\operatorname{diag}(UU_+^\dagger),\qquad
 T^\dagger E^{\mathsf T}T=
 \begin{pmatrix}p&z\\\bar z&1-p\end{pmatrix},\qquad
 \epsilon=1-\operatorname{Tr}(E^2)
          =2\bigl(p(1-p)-|z|^2\bigr)\ge0,
\tag{35.2}
$$

where $T=(b_+\ \ b_-)$ is the source certificate basis. The letters $A,B,P,Q,u,v,r_+,r_-$ retain their meanings in source (23.2)--(23.3). Source (23.5) and (23.12) give the exact distance and the amplitude comparison

$$
\begin{aligned}
 \rho&=\min\{10-2p-2A,\ 8+2p-2B\}-\epsilon,\\
 g&=d^2p+e^2(1-p)
       -\bigl(pu^2+(1-p)v^2+2\operatorname{Re}(Pz\bar Q)\bigr)\\
  &\ge d^2p+e^2(1-p)
             -\bigl(u\sqrt p+v\sqrt{1-p}\bigr)^2.
\end{aligned}
\tag{35.3}
$$

These are identities or bounds on that same original pair, without replacing its effect or its actual unitary.

**Theorem 35.2 (full attained distance domain and the maximal level).** The attained domain of $\rho$ on the unchanged original space is exactly $[0,9]$. Moreover,

$$
 \boxed{\quad
 \rho(E,U)=9
 \quad\Longleftrightarrow\quad
 \epsilon=0,\quad p=\frac12,\quad A(w)=B(w)=0.
 \quad}
\tag{35.4}
$$

Thus every effect at maximal distance has rank one. The condition on the feedback in (35.4) is imposed on the actual unitary; no diagonality is assumed. Every positive level $0<\xi\le9$ is nonempty and compact, and $m(\xi)$ is a finite attained minimum there. For $\xi>9$ it is $+\infty$ under Definition 33.1's convention.

**Proof.** Nonnegativity of $\rho$ follows from its original definition. Averaging its two sign branches in (35.3) gives

$$
 \rho\le 9-A-B-\epsilon\le9.
\tag{35.5}
$$

In particular, if $\rho=9$, then $A=B=\epsilon=0$. The remaining minimum in (35.3) is $\min\{10-2p,8+2p\}$, which equals $9$ only at $p=1/2$. Conversely those four conditions give $\rho=9$ directly. Positivity and trace one imply that $\epsilon=0$ is equivalent to the effect eigenvalues being $1,0$: if they are $a,1-a$ with $0\le a\le1$, then $\epsilon=2a(1-a)$. This proves (35.4), including the rank assertion.

To prove that no distance value is missing, use the following continuous path of actual original pairs, with $0\le q\le1$:

$$
\begin{aligned}
 U(q)&=\operatorname{diag}
       (e^{-i\pi q/2},e^{i\pi q/2},1,e^{i\pi q})U_+,\\
 \psi(q)&=\sqrt{1-q/2}\,b_++\sqrt{q/2}\,b_-,\\
 E(q)&=\overline{\psi(q)}\,\overline{\psi(q)}^\dagger.
\end{aligned}
\tag{35.6}
$$

Each $E(q)$ is normalized, positive and rank one, and each $U(q)$ is a single unitary. At $q=0$ the pair is $(E_+,U_+)$ and has distance zero. At $q=1$ its population is $1/2$ and its feedback diagonal relative to $U_+$ is $(-i,i,1,-1)$. Both trace sums in source (23.2) vanish, so (35.4) gives distance $9$. The original distance is continuous: each sign has the continuous common-phase minimum (23.11), followed by a minimum over two signs. The intermediate value theorem applied to (35.6), together with (35.5), therefore proves that its attained values, and hence the full original attained domain, contain exactly $[0,9]$.

Finally $\operatorname{Dens}_2$ and $U(4)$ are compact. A nonempty distance level is a closed subset of their product, and $f=g-\kappa\rho$ is continuous there. Its minimum is finite and attained. The upper bound in (35.5) makes every level above $9$ empty. $\square$

**Theorem 35.3 (exact maximal-distance envelope and all original minimizers).** At the maximal original distance,

$$
 \boxed{\qquad
 m(9)=\frac{d^2+e^2}{2}-2(h-s)^2-9\kappa.
 \qquad}
\tag{35.7}
$$

For every original pair of distance $9$, the following lower certificate holds:

$$
 g(E,U)\ge H-2\beta^2.
\tag{35.8}
$$

Equality in (35.8), equivalently $f(E,U)=m(9)$, holds if and only if for some $\varphi\in\mathbb R/(2\pi\mathbb Z)$ and one scalar $|\lambda|=1$,

$$
 \boxed{\quad
 \psi_\varphi=\frac{b_++e^{i\varphi}b_-}{\sqrt2},\qquad
 E=\overline{\psi_\varphi}\,\overline{\psi_\varphi}^{\dagger},\qquad
 U=\lambda U_*.
 \quad}
\tag{35.9}
$$

The relative effect phase is arbitrary and independent of the common feedback scalar. This is the complete minimizing set in the original domain, including all actual nondiagonal lifts among the competitors.

**Proof.** The fixed constants satisfy the strict inequality

$$
 0<\alpha<\frac{\beta}{\sqrt2}.
\tag{35.10}
$$

Here $c>h>s$ gives positivity. For an exact verification of the strict upper bound, use $s=(\sqrt2-1)c$ and $c^2=(2+\sqrt2)/4$. Then

$$
\begin{aligned}
 (1+\sqrt2)^2-(4-\sqrt2)^2c^2
       &=\frac{3\sqrt2-4}{2}>0,\\
 \frac{\beta}{\sqrt2}-\alpha
       &=\frac{1+\sqrt2-(4-\sqrt2)c}{2}>0.
\end{aligned}
\tag{35.11}
$$

The second sign follows from the first because both quantities being compared before squaring are positive. Thus (35.10) uses only the fixed half-angle constants.

Now take any original pair with $\rho=9$. By Theorem 35.2 it has $p=1/2$, $\epsilon=0$ and both trace sums zero. Put

$$
 X=w_1+w_2=-(w_3+w_4),\qquad Y=w_3-w_4.
\tag{35.12}
$$

The other zero trace gives $w_1-w_2=-iY$. Consequently the actual diagonal is

$$
 w=\frac12(X-iY,\ X+iY,\ -X+Y,\ -X-Y),
 \qquad P=-\alpha X,\qquad Q=-i\beta Y.
\tag{35.13}
$$

Every diagonal entry of a unitary has modulus at most one. Therefore

$$
 |X+iY|,\ |X-iY|,\ |X+Y|,\ |X-Y|\le2.
\tag{35.14}
$$

Write $a=|X|$, $b=|Y|$. Expanding the last two squared inequalities bounds $a^2+b^2+2|\operatorname{Re}(\bar X Y)|$ by $4$; expanding the first two bounds $a^2+b^2+2|\operatorname{Im}(\bar X Y)|$ by $4$. Since the larger of those two absolute components is at least $|\bar X Y|/\sqrt2=ab/\sqrt2$, these constraints imply

$$
 a^2+b^2+\sqrt2ab\le4,\qquad
 \left(b+\frac a{\sqrt2}\right)^2
       \le4-\frac{a^2}{2}\le4.
\tag{35.15}
$$

In particular, the two amplitudes of this same actual diagonal satisfy the joint bound

$$
\begin{aligned}
 u+v=\alpha a+\beta b
 &=\beta\left(b+\frac a{\sqrt2}\right)
       -\left(\frac\beta{\sqrt2}-\alpha\right)a\\
 &\le2\beta-\left(\frac\beta{\sqrt2}-\alpha\right)a
 \le2\beta.
\end{aligned}
\tag{35.16}
$$

Its equality condition is exactly $a=0$, $b=2$: necessity follows from the strictly positive coefficient in (35.10), and sufficiency follows by substitution. This joint bound does not combine separately attained maxima of $u$ and $v$.

Apply (35.3) with the forced population $p=1/2$. It gives the global endpoint certificate

$$
 g(E,U)\ge H-\frac{(u+v)^2}{2}
          \ge H-2\beta^2.
\tag{35.17}
$$

Suppose equality holds in (35.17). Both comparisons must be equalities, and the second forces $X=0$, $|Y|=2$ by (35.16). With $Y=2\lambda$, (35.13) now gives

$$
 w=\lambda(-i,i,1,-1),\qquad |\lambda|=1.
\tag{35.18}
$$

For the actual unitary $V=UU_+^\dagger$, every diagonal entry in (35.18) has modulus one. Each row of $V$ has squared norm one, already supplied by its diagonal entry; every off-diagonal entry in that row must vanish. Hence $V=\lambda\operatorname{diag}(-i,i,1,-1)$, so the actual feedback itself is $\lambda U_*$. No alternative nondiagonal lift remains at equality.

Theorem 35.2 already forces the effect to have rank one and population $1/2$. In the orthonormal basis $b_+,b_-$, every such effect has exactly the representation in (35.9): choose a representing unit vector for $E^{\mathsf T}$ and remove its overall phase to make its $b_+$ coefficient $1/\sqrt2$. Its other coefficient then has modulus $1/\sqrt2$ and the arbitrary relative phase $e^{i\varphi}$.

Conversely, every pair in (35.9) is an original normalized positive effect with one actual shared unitary. Its data are

$$
 p=\frac12,\quad \epsilon=0,\quad A=B=0,
 \qquad P=0,\quad Q=-2i\lambda\beta.
\tag{35.19}
$$

Thus $\rho=9$, and the exact expression for $g$ in (35.3) is $H-2\beta^2$, independently of $\varphi$. The zero of $P$ is why there is no relative-phase alignment restriction on the effect at this endpoint. This proves attainment, both directions of the equality classification, and (35.7).

Both optimizer signs give distance $9$ in (35.19). Their feedback traces vanish, so every scalar phase in each original common-phase minimization attains its minimum. The classification neither chooses a sign nor introduces coordinate-dependent phase quotients. The lower proof used only constraints satisfied by the actual original unitary, and includes every singular or mixed effect before (35.4) derives purity. No trace, amplitude or effect eigenvalue was divided by. $\square$

**Definition 35.4 (the enlarged feedback shape and same-level comparison pairs).** Define the following class of original pairs, allowing every normalized positive semidefinite effect:

$$
 \mathcal C_{34}=\left\{(E,U)\in\mathcal K:
 U=\lambda\operatorname{diag}(x+iy,x-iy,1,1)U_+,\quad
 x,y\in\mathbb R,\quad x^2+y^2=1,\quad |\lambda|=1\right\}.
\tag{35.20}
$$

There is no restriction on the sign of $x$ or $y$, on the rank or relative phase of $E$, or on which optimizer sign attains the original distance. For $0\le t\le1$ and arbitrary $\varphi$, put

$$
\begin{aligned}
 p_t&=\frac{1-t}{2},&
 \psi_{t,\varphi}&=\sqrt{p_t}\,b_+
                  +e^{i\varphi}\sqrt{1-p_t}\,b_-,\\
 E_{t,\varphi}&=\overline{\psi_{t,\varphi}}\,
                         \overline{\psi_{t,\varphi}}^\dagger,&
 L(t)&=H-\frac{D_0t}{2}-2\beta^2(1+t)-\kappa(9-t).
\end{aligned}
\tag{35.21}
$$

**Theorem 35.5 (strict terminal exclusion of the entire enlarged shape).** For every $0\le t\le1$, the original pair $(E_{t,\varphi},U_*)$ has

$$
 \rho(E_{t,\varphi},U_*)=9-t,\qquad
 f(E_{t,\varphi},U_*)=L(t),\qquad m(9-t)\le L(t).
\tag{35.22}
$$

For every original pair in $\mathcal C_{34}$ at that same actual distance,

$$
 \boxed{\quad
 f(E,U)\ge L(t)+\Gamma(t),\qquad
 \Gamma(t)=2(1+t)\left[\beta^2-
                  \left(\alpha+\frac{ht}{2}\right)^2\right].
 \quad}
\tag{35.23}
$$

In particular set

$$
 \tau=4(1-c)=\frac{2(\beta-\alpha)}h\in(0,1).
\tag{35.24}
$$

For every $\xi$ in the nonempty terminal interval $9-\tau<\xi\le9$, every pair in $\mathcal C_{34}$ at distance $\xi$ satisfies

$$
 f(E,U)-m(\xi)\ge\Gamma(9-\xi)>0.
\tag{35.25}
$$

This exclusion is nonvacuous: $\mathcal C_{34}$ itself attains every level in $[8,9]$. On the closed terminal interval $9-\tau/2\le\xi\le9$ the separation is uniformly at least

$$
 2\left[\beta^2-\left(\frac{\alpha+\beta}{2}\right)^2\right]>0.
\tag{35.26}
$$

At $\xi=9$, all pairs of $\mathcal C_{34}$ on that level, and their common value, are exactly

$$
\begin{aligned}
 E&=\overline{\psi_\varphi}\,\overline{\psi_\varphi}^{\dagger},\qquad
 U=\lambda\operatorname{diag}(-1,-1,1,1)U_+,\\
 f(E,U)&=H-2\alpha^2-9\kappa
       =m(9)+2(\beta^2-\alpha^2),
 \qquad |\lambda|=1.
\end{aligned}
\tag{35.27}
$$

The competitors in (35.22) are asserted to attain the original envelope only at $t=0$, as proved in Theorem 35.3; (35.22)--(35.25) require no claim that they minimize at the other levels.

**Proof.** The diagonal of $U_*U_+^\dagger$ has $A=B=P=0$ and $Q=-2i\beta$. The effect in (35.21) is rank one with population $p_t$ and impurity zero. Consequently the exact two distance branches and the original defect are

$$
\begin{aligned}
 r_+&=10-2p_t=9+t,& r_-&=8+2p_t=9-t,\\
 \rho&=9-t,&
 g&=d^2p_t+e^2(1-p_t)-4\beta^2(1-p_t)\\
 &&&=H-\frac{D_0t}{2}-2\beta^2(1+t).
\end{aligned}
\tag{35.28}
$$

This proves (35.22) using the same actual $U_*$ for the entire original effect. At $t=0$ there is a sign tie; for $t>0$ the negative optimizer branch is the smaller one. The relative effect phase is immaterial because $P=0$. At $t=1$ its $b_+$ coefficient is zero, and all phases represent the same effect. Thus the comparison includes that population endpoint without a phase convention there.

Now take any $(E,U)\in\mathcal C_{34}$ with its actual distance $\rho=9-t$. Keep its original $p,z,\epsilon$ from (35.2). The average bound (35.5) gives

$$
 A+B+\epsilon\le t.
\tag{35.29}
$$

Each of the two branches is at least their minimum $9-t+\epsilon$. Applying this separately to the branches in (35.3) gives

$$
 \frac{1-t+\epsilon}{2}+B\le p
       \le\frac{1+t-\epsilon}{2}-A.
\tag{35.30}
$$

In particular $p,1-p\le(1+t)/2$ and

$$
 d^2p+e^2(1-p)\ge H-\frac{D_0t}{2}.
\tag{35.31}
$$

These inequalities follow from the actual joint minimum and do not select either optimizer sign.

Write the actual feedback in the form (35.20), and put $\chi=1+x\ge0$ and $Y=|y|$. Direct substitution into the source trace and amplitude formulas gives

$$
\begin{aligned}
 A&=2\chi,& B&=2Y,\\
 P&=2\lambda(\alpha+h\chi),& Q&=2i\lambda hy,\\
 u+v&=2\alpha+2h(\chi+Y)\le2\alpha+ht.
\end{aligned}
\tag{35.32}
$$

The last inequality is (35.29). The expression $\alpha+h\chi$ is positive even when $x=-1$, so the displayed amplitude sum is valid on the entire circle, including both signs of $y$. It uses only the one common feedback scalar, which cancels from the moduli.

Positivity of the original effect gives $|z|\le\sqrt{p(1-p)}$ and hence the last inequality in (35.3). With (35.30) and (35.32), its amplitude obeys

$$
 u\sqrt p+v\sqrt{1-p}
     \le\sqrt{\frac{1+t}{2}}\,(u+v)
     \le\sqrt{\frac{1+t}{2}}\,(2\alpha+ht).
\tag{35.33}
$$

Combining this with (35.31), and subtracting the actual $\kappa\rho=\kappa(9-t)$, yields

$$
\begin{aligned}
 f(E,U)
 &\ge H-\frac{D_0t}{2}
       -\frac{1+t}{2}(2\alpha+ht)^2-\kappa(9-t)\\
 &=L(t)+2(1+t)
           \left[\beta^2-\left(\alpha+\frac{ht}{2}\right)^2\right].
\end{aligned}
\tag{35.34}
$$

This proves (35.23) for arbitrary normalized effects, including mixed and singular ones. The nonnegative impurity is retained in (35.29)--(35.30); it was not removed by a rank-one substitution at a different distance.

The identity $c+s=2hc$ gives $\beta-\alpha=2h(1-c)>0$, proving the equality of the two expressions for $\tau$ in (35.24). Also $c<1$ and $c>3/4$, the latter following from $c^2=(2+\sqrt2)/4>3/4$. Thus $0<\tau<1$. For $0\le t<\tau$ one has $\alpha+ht/2<\beta$, so $\Gamma(t)>0$. Since (35.22) supplies an actual original competitor at exactly the same distance, subtracting $m(9-t)\le L(t)$ from (35.23) proves (35.25). If $0\le t\le\tau/2$, then $\alpha+ht/2\le(\alpha+\beta)/2$ and $1+t\ge1$, proving the uniform bound (35.26).

For nonvacuity, use the actual feedback

$$
 \widehat U=\operatorname{diag}(-1,-1,1,1)U_+
\tag{35.35}
$$

with the same $E_{t,\varphi}$. It belongs to (35.20) with $x=-1,y=0$, has $A=B=0$, and therefore has the two distance branches $9+t,9-t$ just as in (35.28). This realizes every level $9-t\in[8,9]$ inside $\mathcal C_{34}$.

Finally suppose a pair in $\mathcal C_{34}$ has distance $9$. Theorem 35.2 forces $p=1/2$, purity and $A=B=0$. In (35.32), $A=0$ forces $x=-1$ and hence $y=0$. Its effect is therefore exactly the arbitrary-phase balanced effect of (35.9), and its feedback is the one in (35.27). At this diagonal $P=2\lambda\alpha$, $Q=0$, so the exact original defect is $H-2\alpha^2$ for every relative effect phase. Conversely every such pair satisfies all these conditions. This proves (35.27), including its necessity and sufficiency. $\square$

The endpoint certificate (35.15)--(35.17), its equality propagation to the actual unitary, and the terminal comparison (35.29)--(35.34) are repo-derived deductions for this fixed record and original producer metric. Their inputs are the normalized-effect and actual shared-feedback identities of source (22.1) and (23.9)--(23.12). The upper estimate $\rho\le9$ is also present in source Section 14; Theorem 35.2 determines its exact attained domain and full maximal level. The simultaneous bound (35.16) concerns the two amplitudes of one diagonal with both trace sums zero, rather than the independent amplitude bounds of source Lemma 26.2.

For the primary-source condition correspondence, Gregoratti--Werner, [*Quantum Lost and Found*, quant-ph/0209025v1, Proposition 8 and (16)--(21)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8), concern a fixed Kraus decomposition and optimal correction of each of its outcomes. In this record their operator is $t_j=\operatorname{diag}(R_0b_j)$ and their input dimension is four; their bound is an intermediate fidelity bound, not an optimization of the joint distance in (35.3). Buscemi--Chiribella--D'Ariano, [*Inverting Quantum Decoherence by Classical Feedback from the Environment*, quant-ph/0504195v5, Theorem 2 and (9)](https://arxiv.org/html/quant-ph/0504195v5), give the rank-two four-dimensional correlation example: their Heisenberg matrix (9) is entrywise conjugate to $R_0R_0^\dagger$ here, consistently with their Schrödinger transpose in (6). The finite diagonal-realization result stated by [Jasper--Loreaux--Weiss, arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3) prescribes singular values and a complex diagonal; taking four singular values equal to one gives source (23.1). The new witnesses (35.6), (35.9), (35.21) and (35.35) have direct actual unitary realizations. The lower comparisons retain every actual lift, so no additional realization hypothesis is imported from that diagonal theorem.

Theorem 35.5 excludes the enlarged feedback shape on a terminal interval and supplies original competitors at its actual distance levels. It does not locate the first loss of the two-orientation minimizing family supplied by Theorem 34.3. The first boundary, the maximal connected initial interval on which that family exhausts original minimizers, its boundary inclusion or exclusion, and the first competing minimizing family remain undetermined. The root-selection interval (34.1) is not identified with any geometric boundary by these results, and no global minimizing claim on the intermediate levels follows from the comparison family (35.21).

## 追加锚（本行以下为增补区）

## 36. Prescribed-distance effect elimination and actual feedback comparisons

**Definition 36.1 (the two admissible effect arcs).** Retain the original $\mathcal K,\rho,g,f,m$, the ordinary transpose and the constants of source Definition 23.1 and Definition 33.1. Fix an actual $U\in U(4)$, and evaluate $w,A,B,P,Q,u,v$ on $w=\operatorname{diag}(UU_+^\dagger)$. Put

$$
 \Delta_+=d^2-u^2,\qquad \Delta_-=e^2-v^2,\qquad
 \omega=uv,\qquad S_+=A,\qquad S_-=B.
\tag{36.1}
$$

Both $\Delta_\pm$ are nonnegative, by source (23.12) at the two population endpoints. For a prescribed $\xi\ge0$ and $\sigma\in\{+,-\}$ define

$$
 t_\sigma=\frac{\xi-8+2S_\sigma}{2},\qquad
 J_\sigma=\frac{1+S_\sigma-S_{-\sigma}}2,\qquad
 b_\sigma=\Delta_{-\sigma}-\Delta_\sigma.
\tag{36.2}
$$

The sign is called admissible when $0\le t_\sigma\le1$ and

$$
 Q_\sigma:=\min\{\sqrt{t_\sigma},J_\sigma\}\ge t_\sigma.
\tag{36.3}
$$

For an admissible sign put $I_\sigma=[t_\sigma,Q_\sigma]$ and

$$
 R_\sigma=\sqrt{b_\sigma^2+4\omega^2}.
\tag{36.4}
$$

If $R_\sigma>0$, set

$$
\begin{aligned}
 q_\sigma^\circ
   &=\frac{\sqrt{t_\sigma}\,(-b_\sigma)_+}{R_\sigma},
       &&(-b_\sigma)_+=\max\{-b_\sigma,0\},\\
 q_\sigma^\sharp
   &=\min\{Q_\sigma,\max\{t_\sigma,q_\sigma^\circ\}\},\\
 M_\sigma(w,\xi)
   &=\Delta_\sigma+b_\sigma q_\sigma^\sharp
       -2\omega\sqrt{t_\sigma-(q_\sigma^\sharp)^2},\\
 Z_\sigma(w,\xi)&=\{q_\sigma^\sharp\}.
\end{aligned}
\tag{36.5}
$$

If $R_\sigma=0$, instead put $M_\sigma(w,\xi)=\Delta_\sigma$ and $Z_\sigma(w,\xi)=I_\sigma$. Set $M_\sigma=+\infty$ for an inadmissible sign. All square roots are the nonnegative real square roots. The letters $Q_\sigma$ in (36.3) are real interval endpoints, whereas $Q=Q(w)$ remains the complex amplitude of source (23.2).

**Theorem 36.2 (exact fixed-feedback level comparison and its full equality preimage).** For every actual $U$ and every $\xi\ge0$,

$$
 \boxed{\quad
 \min_{\substack{E\in\operatorname{Dens}_2\\\rho(E,U)=\xi}}g(E,U)
       =\min_{\sigma\in\{+,-\}}M_\sigma(w,\xi).
 \quad}
\tag{36.6}
$$

An empty level on the left has value $+\infty$. When it is nonempty, an effect minimizes the left side if and only if there are an admissible sign $\sigma$ attaining the right side, a $q\in Z_\sigma(w,\xi)$ and a complex $z$ such that

$$
\begin{aligned}
 |z|^2&=t_\sigma-q^2,\\
 \operatorname{Re}(Pz\bar Q)&=uv|z|,\\
 E&=\bigl(TF_\sigma(q,z)T^\dagger\bigr)^{\mathsf T},\\
 F_+(q,z)&=\begin{pmatrix}1-q&z\\\bar z&q\end{pmatrix},\qquad
 F_-(q,z)=\begin{pmatrix}q&z\\\bar z&1-q\end{pmatrix}.
\end{aligned}
\tag{36.7}
$$

In particular, if $uv|z|=0$ the phase condition imposes no restriction. A sign tie is retained by taking the union of the two sets in (36.7), with coincident effects counted once. The impurity of each such effect is exactly $2(q-t_\sigma)$. Thus the formula includes mixed effects, both population endpoints and all rank changes.

Consequently the full original envelope has the exact reduction

$$
 \boxed{\quad
 m(\xi)=
 \min_{\substack{w\in\mathcal W,\ \sigma\in\{+,-\}\\
                         \sigma\ \mathrm{admissible}}}
            M_\sigma(w,\xi)-\kappa\xi,
       \qquad 0<\xi\le9.
 \quad}
\tag{36.8}
$$

For a feedback diagonal attaining (36.8), every actual unitary lift of that diagonal has exactly the minimizing effect preimage (36.7). No restriction on its off-diagonal entries is implicit in this assertion.

**Proof.** For the given original effect write

$$
 T^\dagger E^{\mathsf T}T
  =\begin{pmatrix}p&z\\\bar z&1-p\end{pmatrix},\qquad
 0\le p\le1,\qquad |z|^2\le p(1-p).
\tag{36.9}
$$

Use $q=1-p$ for $\sigma=+$ and $q=p$ for $\sigma=-$. Source (23.10)--(23.11) show that the corresponding original sign distance is

$$
 \rho_\sigma(E,U)=8-2S_\sigma+2(q^2+|z|^2).
\tag{36.10}
$$

The positive sign attains the joint minimum precisely when

$$
 10-2p-2A\le8+2p-2B
 \quad\Longleftrightarrow\quad 1-p\le J_+.
\tag{36.11}
$$

The negative sign attains it precisely when $p\le J_-$. These conditions include equality; the impurity term cancels when comparing the two branches.

It follows that $\rho(E,U)=\xi$ with $\sigma$ a minimizing sign is equivalent to

$$
 q^2+|z|^2=t_\sigma,\qquad
 0\le q\le1,\qquad |z|^2\le q(1-q),\qquad q\le J_\sigma.
\tag{36.12}
$$

The first and third conditions imply $t_\sigma\le q$, while nonnegativity of $|z|^2$ implies $q\le\sqrt{t_\sigma}$. Conversely these two inequalities give both the nonnegativity of $t_\sigma-q^2$ and its upper bound by $q(1-q)$. Hence (36.12) holds exactly when the sign is admissible, $q\in I_\sigma$ and $|z|^2=t_\sigma-q^2$. This proves exact feasibility in both directions, rather than a relaxation of the positive-effect constraint. It also gives

$$
 \epsilon=2\bigl(q(1-q)-|z|^2\bigr)
         =2(q-t_\sigma).
\tag{36.13}
$$

The same-feedback identity (23.12), without discarding its coherence term, now reads

$$
\begin{aligned}
 g(E,U)
 &=\Delta_\sigma+b_\sigma q
                   -2\operatorname{Re}(Pz\bar Q)\\
 &\ge\Delta_\sigma+b_\sigma q
                   -2\omega\sqrt{t_\sigma-q^2}
       =:\mathcal H_\sigma(q).
\end{aligned}
\tag{36.14}
$$

For each feasible $q$ the inequality is attained: if $PQ\ne0$, choose $z$ with the specified modulus and phase $\bar P Q/(uv)$; if $PQ=0$, choose any phase. This choice leaves the distance and sign inequalities unchanged, because those depend on $p$ and $|z|$ only. Equality in (36.14) is precisely the phase condition in (36.7), including zero coherence or zero amplitudes.

It remains to minimize the displayed function on its explicit closed interval. Suppose first $\omega>0$ and $t_\sigma>0$. In the interior of the circular arc,

$$
 \mathcal H_\sigma'(q)
   =b_\sigma+\frac{2\omega q}{\sqrt{t_\sigma-q^2}},\qquad
 \mathcal H_\sigma''(q)
   =\frac{2\omega t_\sigma}{(t_\sigma-q^2)^{3/2}}>0.
\tag{36.15}
$$

If $b_\sigma\ge0$, the function increases on the nonnegative arc, and its minimum on $I_\sigma$ is at $q=t_\sigma$. If $b_\sigma<0$, its unique minimum on the full nonnegative arc is at

$$
 q=\frac{\sqrt{t_\sigma}(-b_\sigma)}
              {\sqrt{b_\sigma^2+4\omega^2}}.
\tag{36.16}
$$

The derivative is negative below this point and positive above it. Restriction to $I_\sigma$ therefore gives exactly the truncation in (36.5), with a unique minimizing $q$. Continuity covers the endpoint $q=\sqrt{t_\sigma}$. If $t_\sigma=0$, the admissible interval is the singleton $\{0\}$, and the same conclusion follows directly.

If $\omega=0$ and $b_\sigma\ne0$, the function is strictly affine. Its minimizing endpoint is $t_\sigma$ for $b_\sigma>0$ and $Q_\sigma$ for $b_\sigma<0$, again exactly (36.5). If both vanish, it is constant and every point of $I_\sigma$ minimizes. This is precisely the $R_\sigma=0$ case. Thus (36.5) and $Z_\sigma$ give the exact value and all scalar equality cases, without omitting a zero denominator.

Every effect at level $\xi$ has at least one minimizing sign and hence belongs to an arc just analyzed. Conversely (36.7) constructs an original normalized positive effect at the specified level, using the fixed original $U$. Taking the minimum over admissible signs proves (36.6) and its necessary-and-sufficient equality statement.

Finally source Theorem 23.2 identifies $\mathcal W$ with exactly the diagonals of $UU_+^\dagger$. Every expression in (36.1)--(36.7) depends on the actual $U$ only through that diagonal. Therefore minimizing (36.6) over the original unitaries proves (36.8). The attained-level and compactness result of Theorem 35.2 ensures attainment for $0<\xi\le9$. For each $w$ every actual lift gives the same distances, defect and effect preimage; such lifts are retained, rather than replaced by diagonal feedbacks. The original common scalar action $w\mapsto\lambda w$ preserves these expressions, including $Pz\bar Q$, and no additional scalar quotient is used. $\square$

**Theorem 36.3 (a strict same-distance purification comparison).** Let $(E,U)$ be any original pair, let $\sigma$ attain its original joint distance, and put $q=1-p$ for $\sigma=+$ or $q=p$ for $\sigma=-$, with the actual coordinates (36.9). If $b_\sigma\ge0$, there is a normalized rank-one effect $\widehat E$, using the unchanged actual $U$, such that

$$
 \rho(\widehat E,U)=\rho(E,U),\qquad
 g(E,U)-g(\widehat E,U)
       \ge\frac{b_\sigma}{2}\bigl(1-\operatorname{Tr}(E^2)\bigr).
\tag{36.17}
$$

For every original pair with $0<\rho(E,U)\le1$, this has the uniform strengthening

$$
 \boxed{\quad
 f(E,U)\ge f(\widehat E,U)
                 +\frac14\bigl(1-\operatorname{Tr}(E^2)\bigr).
 \quad}
\tag{36.18}
$$

In particular, at every level $0<\xi\le1$, the original minimum equals the minimum restricted to rank-one effects, and every original minimizing effect has rank one. This statement imposes no diagonality condition on $U$.

**Proof.** Put $\epsilon=1-\operatorname{Tr}(E^2)$ and $t=q-\epsilon/2$. By (36.12)--(36.13), $t=t_\sigma$ and $t\le q\le\sqrt t$, with $q\le J_\sigma$. Thus $q'=t$ also belongs to $I_\sigma$. Choose $\widehat E$ from (36.7) using $q'=t$ and

$$
 |z'|=\sqrt{t(1-t)},\qquad
 \operatorname{Re}(Pz'\bar Q)=uv|z'|.
\tag{36.19}
$$

It is positive, trace one and rank one, including $t=0,1$. Its sign $\sigma$ still attains the joint minimum because $q'\le q\le J_\sigma$. Equation (36.10) gives the same original distance. Moreover $|z|^2=t-q^2\le t-t^2=|z'|^2$. Applying the exact defect identity at the same $U$ gives

$$
\begin{aligned}
 g(E,U)-g(\widehat E,U)
 &=b_\sigma(q-t)
       +2\bigl(uv\sqrt{t(1-t)}
                        -\operatorname{Re}(Pz\bar Q)\bigr)\\
 &\ge\frac{b_\sigma\epsilon}{2}
       +2uv\bigl(\sqrt{t(1-t)}-|z|\bigr)
 \ge\frac{b_\sigma\epsilon}{2}.
\end{aligned}
\tag{36.20}
$$

This proves (36.17), with no phase division when $P$ or $Q$ vanishes.

For the uniform claim fix any minimizing sign at a level $0<\xi\le1$, and set $\delta=4-S_\sigma$. The nonnegative effect-distance summand and (23.11) give

$$
 0\le\delta\le\frac\xi2\le\frac12.
\tag{36.21}
$$

First take $\sigma=+$. Normalize the one common feedback scalar so that $\sum_jw_j=A=4-\delta>0$, and put $Y=w_3+w_4$. The disk constraints on the actual diagonal imply $\operatorname{Re}Y\ge A-2$ and

$$
 \sum_j|w_j-1|^2\le8-2A=2\delta.
\tag{36.22}
$$

Since $P=hA+(c-h)Y$ and $c>h$, it follows that

$$
 u\ge\operatorname{Re}P
     \ge cA-2(c-h)=d-c\delta
     \ge d-c/2>0.
\tag{36.23}
$$

The coefficients $(h,-h,is,-is)$ of $Q$ sum to zero and have squared norm $2(h^2+s^2)$. Cauchy--Schwarz and (36.22) therefore give

$$
 v^2\le4(h^2+s^2)\delta\le2(h^2+s^2).
\tag{36.24}
$$

Write $D_0=d^2-e^2$ as in Definition 35.1. Equations (36.23)--(36.24) yield

$$
\begin{aligned}
 b_+=u^2-v^2-D_0
 &\ge(d-c/2)^2-2(h^2+s^2)-D_0\\
 &=-\frac34+3c-5s+\frac{15}{4}s^2
 >\frac{15}{28}>\frac12.
\end{aligned}
\tag{36.25}
$$

Here the identity uses $2hc=c+s$, $2hs=c-s$ and $c^2+s^2=1$. For the strict rational comparison, $7/5<\sqrt2<10/7$ gives $c>11/12$, $s<2/5$ and $s^2>1/7$: indeed $c^2>17/20>121/144$ and $s^2<3/20<4/25$, while $s^2=(2-\sqrt2)/4>1/7$. Substitution in the preceding line gives the stated lower bound $15/28$.

For $\sigma=-$, use the fixed coordinates $\widetilde w=(w_1,-w_2,iw_3,-iw_4)$ of source (25.3), followed by one common scalar normalization so that $\sum_j\widetilde w_j=B=4-\delta$. Then

$$
 \sum_j|\widetilde w_j-1|^2\le2\delta,\qquad
 P=h(\widetilde w_1-\widetilde w_2)
                  -ic(\widetilde w_3-\widetilde w_4).
\tag{36.26}
$$

The coefficients in this last expression sum to zero and have squared norm $2(h^2+c^2)$. Hence

$$
 u^2\le4(h^2+c^2)\delta\le2(h^2+c^2)<3.
\tag{36.27}
$$

The fixed constants satisfy $D_0=4h+8s>4$, since $h>1/2$ and $s>1/4$. Therefore

$$
 b_-=D_0-u^2+v^2>1>\frac12.
\tag{36.28}
$$

Thus either minimizing sign has $b_\sigma>1/2$. Equation (36.20), and equality of the two original distances, prove (36.18). Every mixed normalized effect has $\epsilon>0$, so it has a strictly better rank-one competitor at the same prescribed level with the same actual feedback. Conversely rank-one effects are original competitors. Attainment from Theorem 35.2 proves the equality of minima and the rank assertion for all original minimizers. The argument covers sign ties and arbitrary actual nondiagonal feedbacks; their diagonal disk constraints are consequences of unitarity. $\square$

**Theorem 36.4 (a weighted fixed-trace comparison over all actual feedbacks).** Put $\alpha=c-h>0$. Fix $2<A<4$ and $0<p<1$, and define

$$
\begin{aligned}
 q&=1-p,&x&=(A-2)/2,&y&=\sqrt{1-x^2},\\
 \eta&=h\sqrt p-h\sqrt q\,x/y,&
 C_\eta&=c\sqrt p-\eta
           =\alpha\sqrt p+h\sqrt q\,x/y.
\end{aligned}
\tag{36.29}
$$

Suppose that

$$
 \eta\ge0,\qquad C_\eta>s\sqrt q,\qquad
 \frac{hx^2y}{\sqrt q}
       \ge\frac{C_\eta s^2}{C_\eta^2-s^2q}.
\tag{36.30}
$$

For every actual $U$ with $A(w)=A$, one then has the sharp simultaneous comparison

$$
 \boxed{\quad
 \sqrt p\,u(w)+\sqrt q\,v(w)
 \le 2(hx+c)\sqrt p+2hy\sqrt q=:S_0.
 \quad}
\tag{36.31}
$$

Equality holds if and only if, for one $\tau\in\{+1,-1\}$ and one $|\lambda|=1$,

$$
 w=\lambda(x+\tau iy,x-\tau iy,1,1),\qquad
 U=\lambda\operatorname{diag}(x+\tau iy,x-\tau iy,1,1)U_+.
\tag{36.32}
$$

In particular, for every original normalized effect with certificate population $p$,

$$
 g(E,U)\ge d^2p+e^2q-S_0^2.
\tag{36.33}
$$

Its equality set consists exactly of (36.32) and
$E=\overline{\psi_\tau}\,\overline{\psi_\tau}^{\dagger}$, where
$\psi_\tau=\sqrt p\,b_+-\tau i\sqrt q\,b_-$.
For an original pair to which the positive joint-distance sign applies, put $\delta=4-A$ and $\epsilon=1-\operatorname{Tr}(E^2)$. Evaluate $H_\delta(q)$ by the algebraic expression (33.10)--(33.12), now for $0<\delta<2$; this uses no small-$\delta$ comparison from Section 33. Then

$$
 \rho=2(q+\delta)-\epsilon,\qquad
 f(E,U)\ge H_\delta(q)+\kappa\epsilon.
\tag{36.34}
$$

This assertion includes a tie of the two distance signs. Equality in its lower bound has exactly the original-pair preimage just stated, subject to that joint-sign condition.

**Proof.** For a suitable real $\phi$ one has

$$
 S:=\sqrt p\,u+\sqrt q\,v
   =\left|\sum_j a_j(\phi)w_j\right|,
 \quad
 a(\phi)=\bigl(h(\sqrt p+e^{i\phi}\sqrt q),
 h(\sqrt p-e^{i\phi}\sqrt q),
 c\sqrt p+is e^{i\phi}\sqrt q,
 c\sqrt p-is e^{i\phi}\sqrt q\bigr).
\tag{36.35}
$$

This is the same-amplitude representation (31.20); it includes a zero of either amplitude. Rotate $w$ by one common scalar to make the sum real and nonnegative. Since $A\ge\operatorname{Re}\sum_jw_j$ and $\eta\ge0$, the disk constraints give

$$
 S-\eta A
 \le\operatorname{Re}\sum_j(a_j(\phi)-\eta)w_j
 \le\sum_j|a_j(\phi)-\eta|.
\tag{36.36}
$$

Set $a=h\sqrt p-\eta=h\sqrt q\,x/y>0$, $b=h\sqrt q>0$ and $D=s\sqrt q>0$. With the function $\Phi$ of (31.2), the last sum is

$$
 F(X)=\Phi_{a,b}(X)+\Phi_{C_\eta,D}(1-X),
 \qquad X=\cos^2\phi\in[0,1].
\tag{36.37}
$$

For positive arguments, (31.5) shows that each $\Phi'$ is strictly decreasing on the interior of its differentiability interval: both positive factors in its denominator strictly decrease. Thus $F'$ is strictly decreasing on $(0,1)$. Its right derivative at zero exists because $C_\eta>D$, and is

$$
 F'(0+)=-h\sqrt q\,x^2y
           +\frac{C_\eta s^2q}{C_\eta^2-s^2q}\le0.
\tag{36.38}
$$

Here $a^2+b^2=h^2q/y^2$ gives the first term, and the last inequality is exactly (36.30). Strict decrease implies $F(X)<F(0)$ for every $X>0$, also when equality holds in (36.38). Continuity treats a possible nondifferentiable endpoint at $X=1$. Consequently

$$
 S\le\eta A+F(0)
   =2\eta(1+x)+2h\sqrt q/y+2C_\eta
   =S_0.
\tag{36.39}
$$

The last equality uses $y^2=1-x^2$ and (36.29), proving (36.31).

If equality holds, (36.37)--(36.38) force $\phi=\pi/2$ or $-\pi/2$ modulo $2\pi$. The four shifted coefficients are then $a+ib,a-ib,C_\eta-D,C_\eta+D$, in the appropriate order. All are nonzero, and the last two are positive. Equality in each disk-support term of (36.36) therefore forces, after the one scalar rotation, $w=(x-iy,x+iy,1,1)$ or $(x+iy,x-iy,1,1)$. These diagonals give equality directly, including when $\eta=0$. Every diagonal entry has modulus one, so the row norms of the actual unitary $UU_+^\dagger$ force all its off-diagonal entries to vanish. This proves the equivalence with (36.32), without discarding any actual lift in the lower comparison.

Apply (23.12) to the original effect to get $g\ge d^2p+e^2q-S^2$, and then use (36.31). Because $S_0>0$, equality forces $S=S_0$, hence (36.32). At those diagonals $P=2\lambda(hx+c)$ and $Q=2\tau i\lambda hy$ are nonzero. Equality in (23.12) forces $|z|=\sqrt{pq}$ and its stated aligning phase. Positivity then gives precisely the rank-one effect with vector $\psi_\tau$. This proves (36.33) and its full original equality set, including the exclusion of mixed equality cases.

If the positive distance sign applies, (23.5) gives the first identity in (36.34). The quantity in (36.33) minus $2\kappa(q+\delta)$ is exactly $H_\delta(q)$, by (33.12), since $2(hx+c)=d-h\delta$ and $(2hy)^2=2\delta-\delta^2/2$. Subtracting the actual $\kappa\rho$ proves (36.34) and its equality statement.

The parameter region is not confined to the supplied cap (24.1). For example, take $A=7/2$ and $p=3/4$, so $x=3/4$, $y=\sqrt7/4$ and $q=1/4$. Then $\eta>0$ follows from $\sqrt{21}>3$, while

$$
 C_\eta=\alpha\sqrt3/2+3h/(2\sqrt7)>451/800>9/16.
\tag{36.40}
$$

The bound uses $\alpha>1/5$, $\sqrt3/2>17/20$, $h>7/10$ and $\sqrt7<8/3$, all consequences of (22.13) or positive rational squares. Since $s^2<3/20$, it follows that $C_\eta>s\sqrt q$ and

$$
 \frac{C_\eta s^2}{C_\eta^2-s^2/4}
 <\frac{36}{119}<\frac{63}{128}
 <\frac{9h\sqrt7}{32}
 =\frac{hx^2y}{\sqrt q}.
\tag{36.41}
$$

The first bound uses that the displayed quotient decreases with $C_\eta$ and increases with $s^2$; substitution of $9/16$ and $3/20$ gives $36/119$. The last strict rational comparison uses $\sqrt7>5/2$ and $h>7/10$. All conditions are strict, so they persist on a parameter neighborhood with $A<2+\sqrt{8/3}$. $\square$

**Theorem 36.5 (an actual same-distance phase-instability comparison).** Let $0<x<1$, $0<p<1$, $q=1-p$, $y=\sqrt{1-x^2}$ and $\alpha=c-h$. Suppose

$$
 1+2p+2x-2y>0.
\tag{36.42}
$$

Consider either original pair given by (36.32) and $\psi_\tau=\sqrt p\,b_+-\tau i\sqrt q\,b_-$, without imposing (36.30). Its positive sign is then the unique minimizing distance sign, and its distance is
$\xi=2(q+2(1-x))$. Define

$$
\begin{aligned}
 L_a&=\frac{hx^2}{1+x}
       \left(\frac{\alpha\sqrt p}{hx+c}+\frac{\sqrt q}{y}\right)>0,\\
 L_b&=\alpha\sqrt p+\frac{(h^2x-s^2)\sqrt q}{hy},
 \qquad \mathscr D=L_aL_b-s^2q.
\end{aligned}
\tag{36.43}
$$

If $\mathscr D<0$, the pair is not even a local minimum of $f$ on the full original level $\rho=\xi$. More precisely, there are original rank-one effects and actual diagonal feedbacks, arbitrarily close to that pair, with exactly the same distance and strictly smaller $g$ and $f$.

The sign of this obstruction has an explicit selection. Let $x_0$ be the unique root in $(0,1)$ of

$$
 (h^2+s^2)x_0^3-s^2(1+x_0)=0.
\tag{36.44}
$$

For $x\ge x_0$ one has $\mathscr D>0$ for all $0<p<1$. For $0<x<x_0$, put

$$
\begin{aligned}
 a_0&=\frac{h\alpha x^2}{(1+x)(hx+c)},&
 a_1&=\frac{hx^2}{(1+x)y},&
 b_1&=\frac{h^2x-s^2}{hy},\\
 d_x&=s^2-a_1b_1>0,&
 t_x&=a_0b_1+a_1\alpha,&
 r_*(x)&=\frac{t_x+\sqrt{t_x^2+4d_xa_0\alpha}}{2d_x}.
\end{aligned}
\tag{36.45}
$$

Then $r_*(x)$ is positive and

$$
 \mathscr D<0
 \quad\Longleftrightarrow\quad
 \sqrt{q/p}>r_*(x)
 \qquad(0<x<x_0).
\tag{36.46}
$$

Thus (36.42), $x<x_0$ and (36.46) give an explicit region of original geometric pairs eliminated by strict competitors at their own exact distances. Equations (36.44)--(36.46) select the threshold for this phase variation, not a first boundary for the original envelope.

**Proof.** It suffices initially to take $\lambda=1$. For small real $a,b$, put $L=1+x$ and define

$$
\begin{aligned}
 X(a,b)&=-\cos b\cos a+
                \sqrt{L^2-\cos^2b\sin^2a},\\
 Y(a,b)&=\sqrt{1-X(a,b)^2},\\
 w_\tau(a,b)&=\bigl(e^{ia}(X+\tau iY),
                   e^{ia}(X-\tau iY),e^{i\tau b},e^{-i\tau b}\bigr),\\
 U_\tau(a,b)&=\operatorname{diag}(w_\tau(a,b))U_+,
 \qquad \tau\in\{+1,-1\}.
\end{aligned}
\tag{36.47}
$$

All these quantities are real analytic near $(0,0)$ where appropriate, since $X(0,0)=x\in(0,1)$ and $Y(0,0)=y>0$. Each $U_\tau(a,b)$ is an actual unitary. The defining quadratic equation for $X$ gives the exact identity

$$
 A(w_\tau(a,b))=2|Xe^{ia}+\cos b|=2L.
\tag{36.48}
$$

The two amplitudes at this same feedback are

$$
 P=2(hXe^{ia}+c\cos b),\qquad
 Q=2\tau(ihYe^{ia}-s\sin b).
\tag{36.49}
$$

Both are nonzero near zero. Choose the original rank-one effect by

$$
 \psi_\tau(a,b)=\sqrt p\,b_+
           +\frac{P\bar Q}{|P||Q|}\sqrt q\,b_-,\qquad
 E_\tau(a,b)=\overline{\psi_\tau(a,b)}
                      \,\overline{\psi_\tau(a,b)}^{\dagger}.
\tag{36.50}
$$

It uses the amplitudes of that one actual $U_\tau(a,b)$, has the unchanged population $p$, and attains $g=d^2p+e^2q-(\sqrt p\,u+\sqrt q\,v)^2$ by (23.12)--(23.13). At zero it is exactly the stated geometric effect. Its two distance branches at zero differ by

$$
 r_--r_+=2(1+2p+2x-2y)>0.
\tag{36.51}
$$

Continuity preserves the strict sign for all sufficiently small $a,b$. Purity, fixed population and (36.48) therefore give
$\rho(E_\tau(a,b),U_\tau(a,b))=\xi$ identically. This verifies the original joint distance, rather than only one branch of a relaxed distance.

For completeness, the amplitude variation can be evaluated directly. The defining square roots in (36.47) give

$$
 X=x+\frac{b^2}{2}+\frac{xa^2}{2(1+x)}+o(a^2+b^2).
\tag{36.52}
$$

Squaring (36.49), and then taking the positive square roots at their nonzero base values, yields

$$
\begin{aligned}
 u&=2(hx+c)-\alpha b^2
       -\frac{h\alpha x^2}{(1+x)(hx+c)}a^2+o(a^2+b^2),\\
 v&=2hy+\frac{s^2-h^2x}{hy}b^2
       -\frac{hx^2}{(1+x)y}a^2+2sab+o(a^2+b^2).
\end{aligned}
\tag{36.53}
$$

For example, the second line follows from the exact identity
$v^2=4(h^2Y^2+s^2\sin^2b+2hsY\sin a\sin b)$; it holds for both $\tau$. Consequently

$$
 \sqrt p\,u+\sqrt q\,v
 =S_0-L_aa^2-L_bb^2+2s\sqrt q\,ab+o(a^2+b^2).
\tag{36.54}
$$

Choose $a=(s\sqrt q/L_a)b$. If $\mathscr D<0$, its quadratic increase is

$$
 \sqrt p\,u+\sqrt q\,v-S_0
   =\left(\frac{s^2q}{L_a}-L_b\right)b^2+o(b^2)>0
\tag{36.55}
$$

for every sufficiently small nonzero $b$. Since $S_0>0$, (36.50) gives a strictly smaller $g$. The actual distance is unchanged, so $f$ is strictly smaller as well. Multiplying every feedback in the construction by the original common scalar $\lambda$ proves the assertion for all representatives. This introduces no independent feedback for spectral pieces of an effect.

To verify the selection, put $r=\sqrt{q/p}$. Dividing (36.43) by $p>0$ gives

$$
 \frac{\mathscr D}{p}
   =a_0\alpha+(a_0b_1+a_1\alpha)r
                         +(a_1b_1-s^2)r^2,
\quad
 a_1b_1-s^2
   =\frac{(h^2+s^2)x^3-s^2(1+x)}{(1+x)^2(1-x)}.
\tag{36.56}
$$

The numerator has negative value at zero, positive value $h^2-s^2$ at one, strictly positive second derivative for $x>0$, and negative derivative at zero. It first decreases and then strictly increases, and therefore has exactly one zero in $(0,1)$. Moreover that zero exceeds $s^2/h^2$: writing $v=s^2/h^2\in(0,1)$, the numerator at $v$ is $h^2v(1+v)(v^2-1)<0$. Thus for $x\ge x_0$ one has $b_1>0$, and all the nonconstant coefficients in (36.56) are nonnegative, with a strictly positive constant. This proves $\mathscr D>0$ there.

For $x<x_0$ the quadratic in $r$ has positive constant $a_0\alpha$ and negative leading coefficient $-d_x$. Its two roots have negative product, so exactly one is positive. The quadratic formula gives precisely $r_*(x)$ in (36.45). The quadratic is negative exactly above this root for $r\ge0$, proving (36.46). This strict exclusion region is nonempty with (36.42): at $x=1/2$ the numerator in (36.56) is $(h^2-11s^2)/8<0$, using $h^2=1/2$ and $s^2>1/7$, whereas (36.42) is $2+2p-\sqrt3>0$ for every $p>0$. Taking $p$ sufficiently close to zero makes $\sqrt{q/p}$ exceed the finite $r_*(1/2)$. At the root the second variation in (36.54) is semidefinite; neither a tied minimizing family nor a flat family follows without higher-order and global comparisons. $\square$

The fixed-level effect comparison (36.6)--(36.7) and the strict purification estimate (36.18) are repo-derived consequences of the original normalized-effect, distance and same-feedback identities (23.9)--(23.12). Source (23.7) minimizes $g-\gamma\rho$ without prescribing $\rho$; the arc equation here instead retains the prescribed level and its impurity subtraction. The parameter $q$ is the population away from the selected distance optimizer, not an effect eigenvalue. Formula (36.13) retains its exact relation to rank. The passage to (36.8) uses the finite prescribed-diagonal theorem stated by [Jasper--Loreaux--Weiss, arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3): dimension four and four singular values equal to one give exactly $|w_j|\le1$ and $\sum_j|w_j|-2\min_j|w_j|\le2$ of (23.1); the realized square matrix is unitary. Theorem 36.4 uses the shifted coordinate support of (31.20)--(31.21) and its exact endpoint derivative, with parameter conditions (36.30) in place of (31.7)--(31.9)'s sufficient rational bounds. It gives a fixed-trace weighted comparison and its actual equality preimage, beyond the simultaneous unweighted cap (24.1). Theorem 36.5 is a same-level comparison for actual original pairs, derived from (23.2)--(23.13) and (36.47)--(36.56). Circular-arc minimization, disk support and Taylor expansion are standard intermediate tools. These fixed-record deductions carry no literature-priority assertion.

For the first-loss question, (36.6)--(36.7) remove the effect optimization for each actual feedback at every level. Theorem 36.4 removes the entire feedback comparison, including arbitrary actual nondiagonal lifts, at fixed trace and population satisfying (36.30). Theorem 36.5 eliminates geometric candidate points satisfying (36.42) and (36.46) by strict original competitors at the same distance. These comparisons do not establish that a continuation of the Section 34 minimizers reaches either parameter threshold, or that either threshold is its first loss.

For any actual continuation of that geometric family write $N(\xi)$ for its candidate value of $f$; on the supplied local interval it is $n(\xi/2)$. The remaining all-domain obligation is $M_\sigma(w,\xi)\ge N(\xi)+\kappa\xi$ for every realizable $w$ and every admissible sign, with equality exactly at the continued geometric pairs until the selected first transition. In particular, the feedback parameters outside (36.30), the opposite distance branch, extra tied original minimizers and possible mixed minimizers beyond the range of (36.18) are not eliminated by these theorems. A directly selected first distance boundary, the exact maximal connected positive-distance prefix, its endpoint inclusion or exclusion, and the full actual first transition remain undetermined. Neither $1$ in (36.18), the boundary of (36.30), nor (36.44)--(36.46)'s phase-instability curve is asserted to be that first boundary.

## 追加锚（本行以下为增补区）

## 37. Exact cap envelopes, unique scalar selection and core screening

**Definition 37.1 (cap levels and the remaining core).** Retain the original $\mathcal K=\operatorname{Dens}_2\times U(4)$, ordinary transpose, one actual shared feedback, joint optimizer-sign minimum and one common scalar quotient. Put

$$
 A_0=2+\sqrt{8/3},\qquad D_+=4-A_0,\qquad D_-=1/6,
 \qquad \gamma=1/25.
$$

The four disjoint sectors of the realizable diagonal domain are

$$
\begin{aligned}
 \mathcal C_+&=\{w\in\mathcal W:A(w)\ge A_0\},\\
 \mathcal C_-&=\{w\in\mathcal W:B(w)\ge23/6\},\\
 \mathcal T&=\{w\in\mathcal W:A(w)<A_0,\ B(w)<23/6,\ A(w)+B(w)\le4\},\\
 \mathcal O&=\{w\in\mathcal W:A(w)<A_0,\ B(w)<23/6,\ A(w)+B(w)>4\}.
\end{aligned}
\tag{37.1}
$$

Disjointness of the two caps follows from source (24.13) and (25.11). For $t=\xi/2\ge0$ define

$$
 I_\sigma(t)=[\max\{0,t-1\},\min\{D_\sigma,t\}],\qquad \sigma\in\{+,-\},
\tag{37.2}
$$

with the interval empty when its lower endpoint exceeds its upper endpoint. For $\delta\in I_+(t)$ put $q=t-\delta$ and use the exact expression of (33.12):

$$
 H^+_\delta(q)=
 \left(2a\delta-\frac{\delta^2}{2}\right)(1-q)
 +\left(B-2(1+\kappa)\delta+\frac{\delta^2}{2}\right)q
 -2(d-h\delta)\sqrt{\left(2\delta-\frac{\delta^2}{2}\right)q(1-q)}.
\tag{37.3}
$$

Here $a,B$ are the constants of (33.2), whereas $B(w)$ is the trace modulus. For $\delta\in I_-(t)$ put $p=t-\delta$ and set

$$
\begin{aligned}
 u^-_\delta&=c\sqrt{4\delta-\delta^2},\qquad v^-_\delta=e-s\delta,\\
 H^-_\delta(p)&=d^2p+e^2(1-p)
  -\bigl(u^-_\delta\sqrt p+v^-_\delta\sqrt{1-p}\bigr)^2
  -2\kappa(p+\delta).
\end{aligned}
\tag{37.4}
$$

Write

$$
 N_+(\xi)=\min_{\delta\in I_+(t)}H^+_\delta(t-\delta),\qquad
 N_-(\xi)=\min_{\delta\in I_-(t)}H^-_\delta(t-\delta),
\tag{37.5}
$$

with value $+\infty$ for an empty interval. Using Definition 36.1, also write

$$
 N_{\mathcal O}(\xi)=
 \inf_{w\in\mathcal O}\left(\min_{\sigma\in\{+,-\}}M_\sigma(w,\xi)-\kappa\xi\right),
\tag{37.6}
$$

where inadmissible signs contribute $+\infty$.

**Theorem 37.2 (all-effect cap envelopes and cap purification).** For each $\sigma\in\{+,-\}$ and every $\xi\ge0$,

$$
 \boxed{\quad
 \inf_{\substack{(E,U)\in\mathcal K,\ \rho(E,U)=\xi\\
       \operatorname{diag}(UU_+^\dagger)\in\mathcal C_\sigma}} f(E,U)
       =N_\sigma(\xi).
 \quad}
\tag{37.7}
$$

The cap attains exactly the distance interval $[0,2(1+D_\sigma)]$, and every nonempty cap level has an attained minimum. Every cap minimizer has rank-one effect. More strongly, every original pair in either cap has a rank-one competitor with the same actual $U$ and the same original distance, satisfying

$$
 f(E,U)\ge f(\widehat E,U)
                 +\frac14\bigl(1-\operatorname{Tr}(E^2)\bigr).
\tag{37.8}
$$

This assertion concerns both caps at all their levels; it makes no purity claim about minimizers in $\mathcal O$ or $\mathcal T$.

**Proof.** Source Lemmas 24.2 and 25.1 select the positive sign uniquely throughout $\mathcal C_+$ and the negative sign uniquely throughout $\mathcal C_-$, for every population. Subtracting the common impurity from both branches preserves these strict sign comparisons for every normalized effect.

The hypothesis $b_\sigma\ge0$ of Theorem 36.3 holds uniformly here, independently of the distance level. To verify this, put $D_0=d^2-e^2$. On $\mathcal C_+$ normalize $\sum_jw_j=A=4-\delta>0$ by one common scalar. Since $\delta\le D_+<1/2$, the disk estimates in (36.22)--(36.24) give

$$
 u\ge d-c\delta\ge d-c/2>0,\qquad
 v^2\le4(h^2+s^2)\delta\le2(h^2+s^2).
$$

Indeed $\operatorname{Re}(w_3+w_4)\ge A-2$ proves the first bound, and the zero-sum coefficient row of $Q$ proves the second by Cauchy--Schwarz. Thus the fixed-constant comparison (36.25) gives

$$
 b_+=u^2-v^2-D_0
 \ge(d-c/2)^2-2(h^2+s^2)-D_0>15/28>1/2.
\tag{37.9}
$$

On $\mathcal C_-$ use the fixed coordinates $\widetilde w=(w_1,-w_2,iw_3,-iw_4)$, followed by one common scalar making their sum $B=4-\delta>0$. Here $\delta\le1/6<1/2$. The zero-sum row of $P$ in (36.26) gives $u^2\le4(h^2+c^2)\delta<3$. Since $D_0>4$ as in (36.28), $b_-=D_0-u^2+v^2>1$. These arguments use the cap trace bounds rather than a bound on $\rho$. Theorem 36.3 and (36.20) now prove (37.8), also when an amplitude vanishes. Every mixed normalized effect has positive impurity, so the comparison is strict for it.

For clarity, this also proves the lower bound for the infimum over all effects, without first assuming a global minimizer. Fix any original cap pair at level $\xi$. Let $r$ be its population away from that cap's optimizer, so $r=1-p$ in the positive cap and $r=p$ in the negative cap. In the coordinates of (36.9), put

$$
 T=r^2+|z|^2=r-\epsilon/2,\qquad
 \epsilon=1-\operatorname{Tr}(E^2),\qquad
 \delta=4-S_\sigma.
$$

Its actual distance is $\xi=2(\delta+T)$. Positivity gives $0\le T\le1$, hence $\delta\in I_\sigma(t)$. The construction in Theorem 36.3 has population away from the optimizer equal to $T=t-\delta$, impurity zero, and the unchanged actual feedback. Applying the simultaneous amplitude envelopes (24.9) or (25.2) to this pure competitor gives respectively
$f(\widehat E,U)\ge H^+_\delta(t-\delta)$ or
$f(\widehat E,U)\ge H^-_\delta(t-\delta)$.
Together with (37.8), this proves the lower bound (37.7) for every original effect at the prescribed level.

Conversely, for every $\delta\in I_\sigma(t)$ the simultaneous attaining diagonal (24.15) or (25.13), its actual lift $\operatorname{diag}(w)U_+$, and the phase-aligned rank-one effect (23.13) attain the displayed scalar expression at exactly $\rho=2(\delta+t-\delta)=\xi$. The source cap sign comparisons apply to these witnesses, including both population endpoints and $\delta=0$. Thus every scalar value is realized by an original pair, proving the reverse inequality in (37.7). The intervals in (37.2) are nonempty exactly for $0\le t\le1+D_\sigma$, which proves the asserted distance ranges. Each cap level is closed in compact $\mathcal K$ and has continuous objective. Its minimum is attained; (37.8) then proves purity of every cap minimizer. All lower comparisons used the actual $U$ and include every nondiagonal lift. $\square$

**Theorem 37.3 (unique cap scalar selection and the full cap equality preimage).** For either sign and every $0\le t\le1+D_\sigma$, the scalar minimum in (37.5) is unique; write its argument as $\delta_\sigma(t)$ and put $r=t-\delta_\sigma(t)$. For $0<t<1+D_\sigma$ one has

$$
 \delta_\sigma(t)>\max\{0,t-1\},\qquad 0<r<1.
\tag{37.10}
$$

At $t=0$ one has $\delta=r=0$, and at $t=1+D_\sigma$ one has $\delta=D_\sigma$, $r=1$. The following unsquared increasing-derivative rule selects the unique argument on the entire cap interval. Set

$$
\begin{array}{c|ccccc}
 \sigma&K_\sigma&K_{-\sigma}&k_\sigma&L_\sigma(\delta)&Z_\sigma(\delta)\\ \hline
 +&d&e&h&d-h\delta&2\delta-\delta^2/2\\
 -&e&d&s&e-s\delta&c^2(4\delta-\delta^2)
\end{array}
\tag{37.11}
$$

For fixed $t$ let

$$
\begin{aligned}
 r&=t-\delta,\qquad F=L_\sigma(\delta)^2(1-r),\qquad G=Z_\sigma(\delta)r,\\
 \mathcal H_{\sigma,t}(\delta)
 &=K_\sigma^2(1-r)+K_{-\sigma}^2r-F-G-2\sqrt{FG}-2\kappa t.
\end{aligned}
\tag{37.12}
$$

This is $H^+_\delta(t-\delta)$ or $H^-_\delta(t-\delta)$ respectively. Where $\delta>0$ and $0<r<1$, its derivative is

$$
\begin{aligned}
 \mathcal H'&=K_\sigma^2-K_{-\sigma}^2-F'-G'
                 -\frac{F'G+FG'}{\sqrt{FG}},\\
 F'&=L_\sigma^2-2k_\sigma L_\sigma(1-r),\qquad
 G'=Z_\sigma' r-Z_\sigma.
\end{aligned}
\tag{37.13}
$$

For $0<t\le D_\sigma$, $\delta_\sigma(t)$ is the unique zero of (37.13) in the interior of $I_\sigma(t)$. For $D_\sigma<t<1+D_\sigma$, it is $D_\sigma$ if $\mathcal H'_{\sigma,t}(D_\sigma)\le0$, and otherwise the unique interior zero of (37.13). The two singleton cases were specified above.

All original minimizing pairs on each nonempty cap level are the following. Evaluate $\delta=\delta_\sigma(t)$, $r=t-\delta$ and
$x=1-\delta/2$, $y=\sqrt{\delta-\delta^2/4}$. For an orientation $\tau\in\{+1,-1\}$ define

$$
\begin{aligned}
 w^+_\tau&=(x+\tau iy,x-\tau iy,1,1),&
 \psi^+_\tau&=\sqrt{1-r}\,b_+-\tau i\sqrt r\,b_-,\\
 w^-_\tau&=(1,-1,-i(x+\tau iy),i(x-\tau iy)),&
 \psi^-_\tau&=\tau\sqrt r\,b_++\sqrt{1-r}\,b_-.

\end{aligned}
\tag{37.14}
$$

The necessary-and-sufficient equality preimage in (37.7) is

$$
 E=\overline{\psi^\sigma_\tau}\,
             \overline{\psi^\sigma_\tau}^{\dagger},\qquad
 U=\lambda\operatorname{diag}(w^\sigma_\tau)U_+,
 \qquad |\lambda|=1.
\tag{37.15}
$$

There are exactly two such original pairs modulo the one common feedback scalar at every positive cap level, including its maximal level. At the maximal level their effects coincide but their feedbacks remain distinct. At zero the two orientations coincide, giving the corresponding single optimizer class. In particular there are no scalar ties within either cap envelope. This does not identify a first boundary of the full original envelope.

**Proof.** Fix $t$ with nonempty $I_\sigma(t)$. Throughout that interval $0\le r\le1$, $L_\sigma>0$, $Z_\sigma\ge0$, and $F,G\ge0$. On any nondegenerate interval their second derivatives satisfy

$$
\begin{aligned}
 F''&=2k_\sigma^2(1-r)-4k_\sigma L_\sigma<0,\\
 G''&=-4+2\delta-r<0&& (\sigma=+),\\
 G''&=c^2(-8+4\delta-2r)<0&& (\sigma=-).
\end{aligned}
\tag{37.16}
$$

For the first strict sign use $K_\sigma>2k_\sigma$ and $\delta\le D_\sigma<1/2$, so $L_\sigma>3k_\sigma/2$. The other signs follow immediately from $\delta<1/2$ and $r\ge0$. Hence $F$ and $G$ are strictly concave on the feasible interval. The geometric mean $\sqrt{FG}$ is concave there: for two arguments and $0\le\theta\le1$, Cauchy--Schwarz bounds the convex combination of their geometric means by the geometric mean of the corresponding convex combinations of $F$ and $G$; concavity of $F,G$ and monotonicity of the geometric mean give the desired inequality. This argument includes zeros of $F$ or $G$. Consequently $F+G+2\sqrt{FG}$ is strictly concave. The remaining terms in (37.12) are affine in $\delta$. Thus $\mathcal H_{\sigma,t}$ is strictly convex on every nondegenerate feasible interval, and its continuous minimum is unique. A singleton also has a unique minimum. Its derivative in (37.13) is strictly increasing wherever $F,G>0$.

We verify the endpoints rather than assuming their exclusion. For $0<t<1+D_\sigma$ the lower endpoint is $\ell=\max\{0,t-1\}$. If $0<t<1$, then $F(0)>0$, $G(0)=0$ and $G'(0)>0$; the term $-2\sqrt{FG}$ makes the right derivative at $\ell$ equal to $-\infty$. If $t>1$, then $\ell>0$, $F(\ell)=0$, $F'(\ell)=L_\sigma(\ell)^2>0$ and $G(\ell)>0$, giving the same conclusion. At $t=1$, write $Z_\sigma(\delta)=z_\sigma\delta+O(\delta^2)$, where $z_+=2$ and $z_-=4c^2$. Both $F,G$ then vanish linearly and direct substitution into (37.12) gives

$$
 \mathcal H'_{\sigma,1}(0+)
 =K_\sigma^2-K_{-\sigma}^2-(K_\sigma+\sqrt{z_\sigma})^2
 =-K_{-\sigma}^2-z_\sigma-2K_\sigma\sqrt{z_\sigma}<0.
\tag{37.17}
$$

The lower endpoint is therefore never a minimum at these positive levels. If the upper endpoint is $t\le D_\sigma$, then $r=0$, $F>0$, $G=0$ and $G'=-Z_\sigma(t)<0$; the left derivative is $+\infty$. This endpoint is also excluded. If the upper endpoint is $D_\sigma<t<1+D_\sigma$, both $F,G$ are positive there. The derivative sign there, its strict increase, and the negative derivative at the lower endpoint give exactly the selection rule (37.13). These arguments prove (37.10), including $\delta>0$ and $r>0$, and deal with $t=D_\sigma$ as well. At zero and at the maximal level the interval is the asserted singleton.

The attaining pairs (37.14)--(37.15) follow by direct substitution into the original same-feedback identities. On the positive cap, $P=d-h\delta$ and $Q=\tau i\sqrt{Z_+(\delta)}$ before the common scalar is applied. On the negative cap, $P=\tau\sqrt{Z_-(\delta)}$ and $Q=e-s\delta$. Thus the displayed effects align the amplitudes, have the required population and ordinary-transpose convention, and attain the two scalar envelopes at the original distance $2t$.

For necessity, Theorem 37.2 first forces purity and then (by the uniqueness just proved) the displayed $\delta,r$. At $0<t<1+D_\sigma$, both population square roots are positive, and both attaining amplitudes are nonzero because $\delta>0$. Equality in the simultaneous envelope comparison therefore forces equality in each amplitude bound.

In the positive cap normalize $\sum_jw_j=A>0$. Equality in
$|P|=|hA+(c-h)(w_3+w_4)|\le hA+2(c-h)$ forces $w_3=w_4=1$. Write $w_1=x+\zeta$, $w_2=x-\zeta$. Equality in the other bound gives $|\zeta|^2=1-x^2=y^2$. The two disk constraints then both have squared modulus one, and their difference is $4x\operatorname{Re}\zeta=0$. Here $x\ge\sqrt{2/3}>0$ and $y>0$, the latter following from $\delta>0$, not from the population alone. Hence $\zeta=\tau iy$.

In the negative cap normalize $\sum_j\widetilde w_j=B>0$ in the fixed coordinates used above. Equality in
$|Q|=|sB+(h-s)(\widetilde w_1+\widetilde w_2)|\le sB+2(h-s)$ forces $\widetilde w_1=\widetilde w_2=1$. Write $\widetilde w_3=x+\zeta$, $\widetilde w_4=x-\zeta$. Equality in the $P$ bound forces $|\zeta|=y$, and the same disk calculation, with $x\ge11/12>0$, gives $\zeta=\tau iy$. Undoing the fixed coordinates yields $w^-_\tau$. Equality in (23.12) fixes the relative effect phase and gives exactly the effects in (37.14); the single common feedback scalar cancels from that phase condition.

At the maximal positive-cap level, $r=1$ and only the $v$ envelope is required by equality. Use its support proof (24.3)--(24.12) with $\lambda=hx/y\ge1$. The strict phase comparison (24.6) forces the two support phases $\phi=\pm\pi/2$ modulo $2\pi$. All four shifted coefficients are nonzero: the first two are $\lambda\pm ih$ and the last two are $\lambda\pm s>0$. Equality in each coordinate-disk support term forces $w=(x+\tau iy,x-\tau iy,1,1)$ after the common normalization. Thus the same feedback classification holds without requiring the unused $u$ envelope. The effect is necessarily $E_-$, since its population is zero on $b_+$.

At the maximal negative-cap level, only the $u$ envelope is required. Its support proof (25.6)--(25.10), with $\lambda=cx/y>2$, and the strict phase comparison (25.7), force $\phi=0$ or $\pi$. The first two shifted coefficients are $\lambda\pm h>0$ and the last two are $\lambda\pm ic$. Disk-support equality gives $\widetilde w=(1,1,x+\tau iy,x-\tau iy)$, hence $w^-_\tau$. Its effect is $E_+$. These endpoint arguments do not infer equality from continuity.

At zero the normalized cap diagonal is respectively $(1,1,1,1)$ or $(1,-1,-i,i)$, and the effect is $E_+$ or $E_-$. The vanishing crossed amplitude imposes no relative-phase condition; its zero population makes that phase represent the same effect. There is just the corresponding optimizer class.

In every equality diagonal all four entries have modulus one. For the actual unitary $V=UU_+^\dagger$, each diagonal entry already supplies the full squared row norm, forcing every off-diagonal entry of $V$ to vanish. This proves the assertion about every actual lift in (37.15), without excluding nondiagonal competitors beforehand. For positive levels $y>0$. In the positive cap the last two entries fix the common scalar, and in the negative cap the first two do so. The two orientations therefore cannot be identified by that scalar. At maximal levels the effects coincide because a representing vector's scalar phase does not change its projection, but the feedbacks are still distinct. This proves all the claimed equality and coalescence statements. $\square$

**Theorem 37.4 (screening with the original core effect profile retained).** Every original pair in $\mathcal T$ with $\rho=\xi>0$ satisfies

$$
 f(E,U)>(\gamma-\kappa)\xi.
\tag{37.18}
$$

For each $0<\xi\le9$ such that $N_+(\xi)<(\gamma-\kappa)\xi$, one has

$$
 \boxed{\quad m(\xi)=\min\{N_+(\xi),N_{\mathcal O}(\xi)\}.\quad}
\tag{37.19}
$$

Every original minimizing pair on such a level belongs to $\mathcal C_+$ or $\mathcal O$. Those in $\mathcal C_+$ are exactly (37.15) with $\sigma=+$, and occur if and only if $N_+(\xi)\le N_{\mathcal O}(\xi)$. Those in $\mathcal O$ retain exactly the full effect profile (36.7), including its admissible sign ties, mixed effects and zero-amplitude cases, for actual feedbacks attaining the core value equal to $m(\xi)$. Equality of $N_{\mathcal O}(\xi)$ and $N_+(\xi)$ alone does not assert the existence of a core minimizing pair, since $\mathcal O$ need not be closed.

**Proof.** Source Theorem 26.4 gives $g>\gamma\rho$ on the trace triangle with both caps removed, which is exactly $\mathcal T$; this proves (37.18) for every original effect. Source Theorem 25.3 gives $f\ge(\gamma-\kappa)\xi$ throughout $\mathcal C_-$, also for mixed effects. These two sectors consequently cannot contain a global minimizer under the stated strict screening condition; their infima are at least the screen value. On $\mathcal C_+$ Theorems 37.2--37.3 give the attained value and full equality preimage. On $\mathcal O$, Theorem 36.2 gives exactly (37.6), with no restriction to pure effects. Taking the infimum over the four-set partition proves (37.19). The full original minimum is attained by Theorem 35.2. The equality assertions follow from the same sector comparisons and the necessary-and-sufficient fixed-feedback equality of Theorem 36.2. In particular a minimizing original effect at a core feedback must minimize its fixed-feedback level problem; otherwise its same-feedback competitor would lower the original value. Conversely a core feedback and an effect from (36.7) attaining the full value give an original minimizer. No extra sign or scalar quotient has been introduced. $\square$

**Theorem 37.5 (scalar ordering throughout the rank-one geometric family up to distance four).** Let $\mathcal C_{34}$ be the full enlarged feedback shape of Definition 35.4, and restrict only the effects in this comparison to rank one. For every $0<\xi\le4$, put $t=\xi/2$ and

$$
 J(t)=[\max\{0,t-1\},t].
\tag{37.20}
$$

There is exactly one root $\delta_\circ(t)$ of (37.13) with $\sigma=+$ in the interior of $J(t)$. The exact restricted envelope is

$$
 \boxed{\quad
 \min_{\substack{(E,U)\in\mathcal C_{34},\ \operatorname{rank}E=1\\
                         \rho(E,U)=\xi}}f(E,U)
 =H^+_{\delta_\circ(t)}(t-\delta_\circ(t)).
 \quad}
\tag{37.21}
$$

Here (37.3) and (37.11)--(37.13) are evaluated by their displayed algebraic expressions for $0\le\delta\le2$, without extending a cap comparison to that range. All restricted minimizers are precisely (37.14)--(37.15) with $\sigma=+$, $\delta=\delta_\circ(t)$ and $r=t-\delta$, giving exactly two distinct original pairs modulo the common scalar. This unique scalar choice agrees with the Section 34 germ on its supplied local interval. Equation (37.21) orders every rank-one competitor in the enlarged geometric shape on these levels; it does not order general original feedbacks or mixed effects in that shape.

**Proof.** On $J(t)$ one has $0\le\delta\le t\le2$ and $0\le r=t-\delta\le1$. The positive-sign quantities in (37.12) still satisfy $F,G\ge0$. Now $L=d-h\delta\ge2c$, so

$$
 F''\le1-8hc<0,\qquad G''=-4+2\delta-r\le0.
\tag{37.22}
$$

The first strict sign follows from $c>h$ and $h^2=1/2$. Concavity of the geometric mean, as proved above, therefore makes $\mathcal H_{+,t}$ strictly convex on $J(t)$. The lower-endpoint argument (37.17) applies unchanged; it has negative right derivative, with value $-\infty$ except when $t=1$. The upper endpoint is $\delta=t$, $r=0$. There $F>0$, $G=0$, $G'=-Z_+(t)<0$ for every $0<t\le2$, so the left derivative is $+\infty$. Thus there is a unique interior root and minimum, with
$0<\delta_\circ(t)<2$ and $0<t-\delta_\circ(t)<1$.

For every scalar argument $\delta\in J(t)$ the actual geometric feedback has $x=1-\delta/2\ge0$, $y=\sqrt{1-x^2}$, $A=2(1+x)$ and $B=2y$. At population $p=1-r$ its pure-effect distance branches satisfy

$$
 r_--r_+=2(5-2t+\delta-2y)
       \ge2(7-2t-2\sqrt2)>0,
\tag{37.23}
$$

because $\delta-2y=2-2(x+y)\ge2-2\sqrt2$ and $t\le2$. Hence the phase-aligned rank-one effect really has original joint distance $2t$ and value $H^+_\delta(t-\delta)$. This proves attainment of the scalar minimum by original pairs, rather than just by a distance branch expression.

Conversely, take any rank-one original pair in $\mathcal C_{34}$ with $\rho\le4$. If its geometric feedback has $x<0$, then both feedback-distance summands alone exceed four: $8-2A=4-4x>4$ and $8-2B=8-4|y|>4$. Both effect-distance summands are nonnegative, a contradiction. Thus $x\ge0$ and $\delta=2(1-x)\in[0,2]$. The negative-branch feedback distance is $8-4|y|\ge4$. Consequently a negative minimizing sign at $\rho\le4$ is possible only at $\rho=4$, $x=0$, $|y|=1$ and $E=E_-$. Apart from this case, the positive branch gives $r+\delta=t$, so $\delta\in J(t)$. The actual amplitudes are $u=d-h\delta$ and $v=\sqrt{2\delta-\delta^2/2}$. Equation (23.12) gives $f\ge H^+_\delta(t-\delta)$ for every effect phase, and therefore the bound (37.21).

It remains to eliminate the negative-branch exception at its actual level four. Its defect is $e^2-2$. At that same level choose $\delta=3/2$, $r=1/2$ and the phase-aligned original geometric pair already constructed. Its amplitudes and defect are

$$
 u=2c+h/2,\qquad v=h\sqrt{15}/2,\qquad
 g=\frac{d^2+e^2}{2}-\frac{(u+v)^2}{2}.
\tag{37.24}
$$

The rational bounds $c>9/10$, $h>7/10$, $\sqrt{15}>3$, $h<3/4$ and $s<2/5$ give

$$
 (u+v)^2>(16/5)^2=256/25
   >51/5>D_0+4,\qquad D_0=4h+8s.
\tag{37.25}
$$

Thus (37.24) is strictly below $e^2-2$. Its distance is exactly four by (37.23), and subtracting $4\kappa$ preserves the strict comparison. The exceptional negative-sign pair cannot minimize the restricted problem.

Every restricted minimizing pair now has the unique interior scalar argument. Its two amplitudes and both population square roots are positive, so equality in (23.12) forces exactly the relative effect phase in (37.14). The feedback already has the geometric form by definition, with its two orientations. Here $x>0$, $y>0$ and $0<r<1$, so the orientations give distinct effects and distinct feedbacks after the common scalar quotient. This proves both directions of the equality assertion. On the local interval, Lemma 34.2's scalar argument is in this domain and minimizes the same expression; uniqueness therefore identifies it with $\delta_\circ(t)$. No cap purity or general-feedback comparison was used beyond its proved domain. $\square$

The all-effect cap infima (37.7)--(37.9), strict scalar convexity and selection (37.10)--(37.17), and endpoint equality propagation are fixed-record deductions. They use the supplied simultaneous envelopes (24.9), (25.2), normalized-effect identities (23.9)--(23.12), and the conditional same-level purification of Theorem 36.3 with its cap hypotheses proved above. The scalar uniqueness extends the local selection of Lemma 34.2 to both entire cap distance ranges. Theorem 37.5 further orders the entire rank-one enlarged geometric family at every original level up to four, including its exceptional negative-sign endpoint; it does not replace a full-domain comparison by that restricted envelope. The screen in (37.18) and the opposite-cap inequality are supplied results, while (37.19) records their prescribed-level consequence with the exact core effect profile retained. Concavity of the geometric mean and disk-support equality are standard intermediate tools, used here for the explicit functions (37.11)--(37.12).

For the bounded primary-source correspondence, [Jasper--Loreaux--Weiss, arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3) states Thompson's prescribed complex-diagonal and singular-value theorem. Four singular values equal to one give exactly the domain $\mathcal W$ of source (23.1); the realized square matrix is unitary. This is the realization input behind the full-domain profile, whereas the cap equality witnesses here have direct diagonal unitary realizations. [Gregoratti--Werner, quant-ph/0209025v1, Proposition 8 and (16)--(17)](https://arxiv.org/html/quant-ph/0209025v1#ThmThe8) concerns fidelity and equality for a fixed Kraus decomposition. Its operators correspond to $t_j=\operatorname{diag}(R_0b_j)$ in dimension four, as in the source volume. That result is a correction-bound input, not a prescribed producer-distance cap envelope or its scalar selection. The new deductions here concern that additional metric and its exact level constraint; no exhaustive literature-absence or priority claim is made.

For the original first-loss question, this removes the all-effect optimization and the possibility of scalar ties inside either screened cap, with a full original-pair equality preimage at every cap level. It also removes the opposite-cap and trace-triangle competitors on levels satisfying the explicit strict screen in Theorem 37.4. The remaining all-original feedback ordering compares the intrinsically continued Section 34 germ against every admissible $M_\sigma(w,\xi)$ in the core, including mixed effects. Theorem 37.5 removes rank-one geometric scalar competition through distance four, but does not compare mixed effects beyond the caps or any general feedback there; geometric scalar competition beyond that range is also unresolved. On the supplied local interval the unique positive-cap selection agrees with Lemma 34.2. A cap-selection endpoint or the failure of the linear screen is not identified with loss of the geometric germ. A core infimum tie requires attainment and an additional original pair before it can signify added minimizers. The exact maximal connected positive-distance range, a directly selected first boundary, its inclusion or exclusion, all first competing original minimizers or the precise structural event, immediate right-side failure when required, and the determinant-zero variation case remain unresolved. No finite cap interval or residual optimizer formula settles those claims.

## 追加锚（本行以下为增补区）

## 38. Uniform distance-four phase instability and strict original competitors

**Definition 38.1 (the geometric comparator in the original problem).** Keep the original $\mathcal K=\operatorname{Dens}_2\times U(4)$, $g,\rho$, $f=g-\kappa\rho$ and $m$, the ordinary transpose, and the single common feedback scalar. All effects, including mixed and singular ones, and both original optimizer signs remain in this domain. The data $w,A,B,P,Q,u,v$ are those of source Definition 23.1, evaluated on the same actual $w=\operatorname{diag}(UU_+^\dagger)$. For $0<\xi\le9$ the prescribed-level comparison is the full profile of Theorem 36.2: for either admissible sign,

$$
\begin{aligned}
 I_\sigma(w,\xi)&=[t_\sigma,\min\{\sqrt{t_\sigma},J_\sigma\}],\\
 M_\sigma(w,\xi)
 &=\min_{r\in I_\sigma(w,\xi)}
   \left[\Delta_\sigma+b_\sigma r
                  -2uv\sqrt{t_\sigma-r^2}\right],\\
 m(\xi)&=\min_{\substack{w\in\mathcal W,\ \sigma\in\{+,-\}\\
                         \sigma\ \mathrm{admissible}}}
                   M_\sigma(w,\xi)-\kappa\xi.
\end{aligned}
\tag{38.1}
$$

Here every symbol and every admissibility condition is as in (36.1)--(36.5). The effect preimage is exactly (36.7); at population $r$ its impurity is $2(r-t_\sigma)$. Thus (38.1) retains the entire mixed part $r>t_\sigma$, sign ties and zero-amplitude cases. The core value $N_{\mathcal O}$ is the infimum in (37.6), without an assumption that it is attained.

For $0<\xi\le4$ and $t=\xi/2$ define the rank-one geometric comparator by the attained restricted minimum of Theorem 37.5:

$$
 N_{\mathrm{geo}}(\xi)
 :=H^+_{\delta_\circ(t)}(t-\delta_\circ(t))
 =\min_{\delta\in[\max\{0,t-1\},t]}H^+_\delta(t-\delta).
\tag{38.2}
$$

The scalar argument $\delta_\circ(t)$ is the existing unique interior root selected in (37.13), not a new selection rule. This comparator orders rank-one pairs in $\mathcal C_{34}$; its definition makes no full-domain minimizing assertion.

**Theorem 38.2 (uniform transverse instability of the interior distance-four slice).** For every $0<x<1/2$ put

$$
 p=1-2x,\qquad q=2x,\qquad y=\sqrt{1-x^2},\qquad \alpha=c-h,
\tag{38.3}
$$

and evaluate $L_a,L_b,\mathscr D$ by (36.43). Then

$$
 \boxed{\qquad
 \frac{\mathscr D}{q}< -\frac{53}{5376}<0.
 \qquad}
\tag{38.4}
$$

For every $\tau\in\{+1,-1\}$ and $|\lambda|=1$, the original geometric pair

$$
\begin{aligned}
 w_\tau(x)&=(x+\tau iy,x-\tau iy,1,1),\\
 U_{\lambda,\tau}(x)&=\lambda\operatorname{diag}(w_\tau(x))U_+,\\
 \psi_\tau(x)&=\sqrt p\,b_+-\tau i\sqrt q\,b_-,\qquad
 E_\tau(x)=\overline{\psi_\tau(x)}\,
                          \overline{\psi_\tau(x)}^\dagger
\end{aligned}
\tag{38.5}
$$

has original joint distance four and feedback in $\mathcal O$. It is not a local minimum on that original distance level: there are arbitrarily close rank-one original pairs, also with feedback in $\mathcal O$, at exactly distance four with strictly smaller $g$ and $f$. The bound (38.4) is uniform over the slice; no common perturbation radius as $x$ approaches its endpoints is asserted.

**Proof.** The rational half-angle bounds (22.13) imply

$$
 \frac7{10}<h<\frac34,\qquad c>\frac9{10},\qquad
 0<\alpha<\frac14,\qquad s^2>\frac17.
\tag{38.6}
$$

Also $y>4/5$ and $x/(1+x)<1/3$. Since $0<p,q<1$ and $q=2x$, the first expression in (36.43) gives

$$
\begin{aligned}
 0<\frac{L_a}{q}
 &<\frac{hx}{2(1+x)}
          \left(\frac{\alpha}{c}+\frac1y\right)\\
 &<\frac18\left(\frac5{18}+\frac54\right)
   =\frac{55}{288}.
\end{aligned}
\tag{38.7}
$$

For the second expression, if $h^2x-s^2\le0$ then $L_b\le\alpha\sqrt p<1/4$. If it is positive, $h^2=1/2$, $x<1/2$, $\sqrt q<1$ and $hy>(7/10)(4/5)$ show that

$$
 L_b<\frac14+\frac{1/4}{(7/10)(4/5)}
       =\frac{39}{56}.
\tag{38.8}
$$

The same upper bound holds in the first case. No positivity of $L_b$ is required: $L_a/q>0$ and $39/56>0$ give

$$
 \frac{\mathscr D}{q}
 =\frac{L_a}{q}L_b-s^2
 <\frac{55}{288}\frac{39}{56}-\frac17
 =-\frac{53}{5376}.
\tag{38.9}
$$

This proves the uniform estimate.

At (38.5), $A=2(1+x)$, $B=2y$ and $P=2(hx+c)$, $Q=2\tau ihy$ before the common scalar. Source (23.3), with the pure effect in (38.5), gives

$$
 \rho_+=4,\qquad
 \rho_--\rho_+=2(3-2x-2y)
          \ge2(3-2\sqrt2)>0.
\tag{38.10}
$$

Thus the positive sign is uniquely selected. Moreover $A<3<A_0$, $B<2<23/6$, and $A+B>4$ because $x+y>1$ for $0<x<1$. This proves core membership. Condition (36.42) is precisely $3-2x-2y>0$ here. Theorem 36.5 now applies with (38.9): it supplies the exact same-distance phase variation and a strictly decreasing direction for every pair (38.5), including both orientations and the common scalar. All core inequalities are strict, so its sufficiently close competitors remain in $\mathcal O$. This application uses that theorem's actual feasible variation, not an unconstrained quadratic perturbation. $\square$

**Theorem 38.3 (an actual core family below the attained scalar minimum).** Put

$$
\begin{aligned}
 x_*&=1-\frac{\delta_\circ(2)}2,\qquad
 p_*=1-2x_*,\qquad q_*=2x_*,\qquad y_*=\sqrt{1-x_*^2},\\
 V_4(x)&=d^2(1-2x)+2e^2x\\
 &\hspace{6mm}
 -\left[2(hx+c)\sqrt{1-2x}
           +2h\sqrt{1-x^2}\sqrt{2x}\right]^2,
 \qquad 0\le x\le\frac12.
\end{aligned}
\tag{38.11}
$$

Then $0<x_*<1/2$ and

$$
 V_4(x_*)=\min_{0\le x\le1/2}V_4(x)
             =N_{\mathrm{geo}}(4)+4\kappa.
\tag{38.12}
$$

There is a real analytic original rank-one family $(E_\beta,U_\beta)$ near $\beta=0$, equal there to the positive-orientation comparator (38.5) at $x_*$, and a number $\eta>0$ such that every $0<|\beta|<\eta$ satisfies

$$
\begin{aligned}
 w_\beta&\in\mathcal O,\qquad \rho(E_\beta,U_\beta)=4,\\
 M_+(w_\beta,4)&\le g(E_\beta,U_\beta)
                  <N_{\mathrm{geo}}(4)+4\kappa,\\
 f(E_\beta,U_\beta)&<N_{\mathrm{geo}}(4).
\end{aligned}
\tag{38.13}
$$

All data in these comparisons arise from the single actual $U_\beta$. The value $M_+(w_\beta,4)$ itself is attained by an original effect at that same feedback, with its full mixed arc allowed. These effects are strict competitors; no global core minimizing property is asserted.

**Proof.** Theorem 37.5 puts $\delta_\circ(2)$ in $(1,2)$. Its change of variable $\delta=2(1-x)$ gives $r=2-\delta=2x$, and the geometric amplitudes in its proof are $2(hx+c)$ and $2h\sqrt{1-x^2}$. Applying (37.21) gives (38.12), with no further scalar-selection argument.

Evaluate $L_a,L_b,\mathscr D$ at $(x_*,p_*,q_*)$ and put

$$
 k=\frac{s\sqrt{q_*}}{L_a}>0,\qquad a=k\beta,\qquad b=\beta.
\tag{38.14}
$$

Use exactly the positive-orientation curve (36.47). Explicitly its specialization is

$$
\begin{aligned}
 X_\beta&=-\cos\beta\cos(k\beta)
    +\sqrt{(1+x_*)^2-\cos^2\beta\sin^2(k\beta)},\\
 Y_\beta&=\sqrt{1-X_\beta^2},\\
 w_\beta&=\bigl(e^{ik\beta}(X_\beta+iY_\beta),
               e^{ik\beta}(X_\beta-iY_\beta),
               e^{i\beta},e^{-i\beta}\bigr),\\
 U_\beta&=\operatorname{diag}(w_\beta)U_+.
\end{aligned}
\tag{38.15}
$$

The square roots are the positive branches through $X_0=x_*$ and $Y_0=y_*$. They are real analytic near zero and $0<X_\beta<1$ there. Each entry of $w_\beta$ has modulus one, so this is a direct actual unitary realization, with no appeal to a relaxed diagonal domain. The identities (36.48)--(36.49), applied to this same $w_\beta$, give

$$
\begin{aligned}
 A_\beta&=2(1+x_*),\\
 B_\beta&=2\left|iY_\beta e^{ik\beta}-\sin\beta\right|,\\
 P_\beta&=2(hX_\beta e^{ik\beta}+c\cos\beta),\\
 Q_\beta&=2(ihY_\beta e^{ik\beta}-s\sin\beta),\qquad
 u_\beta=|P_\beta|,\quad v_\beta=|Q_\beta|.
\end{aligned}
\tag{38.16}
$$

At zero, $P_0>0$, $Q_0=2ihy_*\ne0$, $B_0=2y_*<2$ and $A_\beta+B_0=2(1+x_*+y_*)>4$. Thus after shrinking the parameter interval, $P_\beta Q_\beta\ne0$, $B_\beta<2$ and $A_\beta+B_\beta>4$. Together with $A_\beta<3$, these strict inequalities put $w_\beta$ in $\mathcal O$.

Define the original effect using ordinary transpose by

$$
\begin{aligned}
 z_\beta&=\sqrt{p_*q_*}\,
                 \frac{\overline{P_\beta}Q_\beta}{u_\beta v_\beta},\\
 F_\beta&=\begin{pmatrix}p_*&z_\beta\\
                              \overline{z_\beta}&q_*\end{pmatrix},
 \qquad E_\beta=(TF_\beta T^\dagger)^{\mathsf T}.
\end{aligned}
\tag{38.17}
$$

The matrix $F_\beta$ has trace one, positive diagonal and determinant zero. Hence $E_\beta$ is positive, normalized and rank one; transpose preserves positivity. At zero, $z_0=i\sqrt{p_*q_*}$, so (38.17) is exactly the effect (38.5) with $\tau=+1$. Its phase satisfies
$\operatorname{Re}(P_\beta z_\beta\overline{Q_\beta})=u_\beta v_\beta\sqrt{p_*q_*}$, using the two amplitudes of this one feedback.

By (36.10) and the exact fixed trace in (38.16), its positive distance is

$$
 \rho_+(E_\beta,U_\beta)
   =8-2A_\beta+2(q_*^2+|z_\beta|^2)
   =8-4(1+x_*)+2q_*=4.
\tag{38.18}
$$

The opposite feedback-distance term alone is $8-2B_\beta>4$; its effect-distance term is nonnegative. Thus the negative original branch is strictly larger than four. This verifies the actual joint minimum at exactly the original distance, independently of a branch-continuity inference.

For strictness, apply the already established variation (36.54)--(36.55) along (38.14):

$$
\begin{aligned}
 S_\beta&:=\sqrt{p_*}\,u_\beta+\sqrt{q_*}\,v_\beta\\
 &=S_0+\frac{-\mathscr D}{L_a}\,\beta^2+o(\beta^2),\\
 S_0&=2(hx_*+c)\sqrt{p_*}+2hy_*\sqrt{q_*}>0.
\end{aligned}
\tag{38.19}
$$

The new estimate (38.4) makes $C=-\mathscr D/L_a>0$. By the definition of $o(\beta^2)$, there is a nonempty parameter interval on which the remainder has absolute value less than $C\beta^2/2$. For every nonzero $\beta$ in it, $S_\beta>S_0$. Source (23.12), with the phase in (38.17), consequently gives

$$
 g(E_\beta,U_\beta)
 =d^2p_*+e^2q_*-S_\beta^2
 <d^2p_*+e^2q_*-S_0^2
 =V_4(x_*).
\tag{38.20}
$$

Intersect this interval with the analytic and strict-feasibility neighborhoods above to obtain $\eta>0$. Equations (38.12), (38.18) and (38.20) prove the strict comparisons in (38.13) for every $0<|\beta|<\eta$. This proves a punctured interval of exact witnesses, without specifying a numerical scalar argument or perturbation radius.

To apply the entire original effect profile, fix any such $\beta$. At level four,

$$
 t_+=q_*,\qquad t_-=B_\beta-2<0,\qquad
 J_+=\frac{1+A_\beta-B_\beta}{2}
            >\frac12+x_*>q_*.
\tag{38.21}
$$

Thus the negative sign is inadmissible here, and the full positive arc is the nondegenerate interval
$[q_*,\min\{\sqrt{q_*},J_+\}]$. For every $r$ in this interval put

$$
 z_\beta(r)=\sqrt{q_*-r^2}\,
                \frac{\overline{P_\beta}Q_\beta}{u_\beta v_\beta},
 \qquad
 E_\beta(r)=\left[T
   \begin{pmatrix}1-r&z_\beta(r)\\
                   \overline{z_\beta(r)}&r\end{pmatrix}
                         T^\dagger\right]^{\mathsf T}.
\tag{38.22}
$$

The certificate-basis matrix has determinant $r-q_*\ge0$ and trace one; its impurity is $2(r-q_*)$. Its positive distance is exactly four by (36.10), and its negative distance exceeds four as above. It is therefore an original mixed effect whenever $r>q_*$, using the unchanged shared $U_\beta$. Theorem 36.2 applies with all these values of $r$ and gives

$$
\begin{aligned}
 M_+(w_\beta,4)
 &=\min_{r\in[q_*,\min\{\sqrt{q_*},J_+\}]}
   \left[\Delta_++b_+r
              -2u_\beta v_\beta\sqrt{q_*-r^2}\right]\\
 &\le g(E_\beta(q_*),U_\beta)
   =g(E_\beta,U_\beta)
   <N_{\mathrm{geo}}(4)+4\kappa.
\end{aligned}
\tag{38.23}
$$

The effect $E_\beta(q_+^\sharp)$, with $q_+^\sharp$ from (36.5), attains this fixed-feedback minimum. It may be mixed; no purification condition on $b_+$ was imposed. In particular
$N_{\mathcal O}(4)\le M_+(w_\beta,4)-4\kappa<N_{\mathrm{geo}}(4)$, without a claim that a core feedback attains $N_{\mathcal O}(4)$. The realization, phase alignment and both sign checks all concern the same object. $\square$

**Theorem 38.4 (strict failure on a left neighborhood and the remaining first-loss problem).** There are an actual fixed feedback $U_\beta$ with $w_\beta\in\mathcal O$ and a number $\varepsilon>0$ such that for every $4-\varepsilon<\xi\le4$ there is an original rank-one effect $E_\xi$ with

$$
\begin{aligned}
 \rho(E_\xi,U_\beta)&=\xi,\\
 m(\xi)\le N_{\mathcal O}(\xi)
 &\le M_+(w_\beta,\xi)-\kappa\xi
 \le f(E_\xi,U_\beta)<N_{\mathrm{geo}}(\xi).
\end{aligned}
\tag{38.24}
$$

Thus an initial positive-distance interval on which the Section 34 geometric pairs exhaust the full original minimizers has supremum strictly below four. This does not determine that supremum or any first competing minimizing pair.

**Proof.** Fix one $0<|\beta|<\eta$ from Theorem 38.3, together with its actual $U_\beta$ and all the amplitudes in (38.16). For $\xi$ close to four from below put

$$
\begin{aligned}
 t(\xi)&=\frac{\xi-8+2A_\beta}{2}
           =\frac\xi2-2+2x_*,\\
 z(\xi)&=\sqrt{t(\xi)(1-t(\xi))}\,
                \frac{\overline{P_\beta}Q_\beta}{u_\beta v_\beta},\\
 E_\xi&=\left[T
     \begin{pmatrix}1-t(\xi)&z(\xi)\\
                     \overline{z(\xi)}&t(\xi)\end{pmatrix}
                                T^\dagger\right]^{\mathsf T}.
\end{aligned}
\tag{38.25}
$$

At four, $t(4)=q_*\in(0,1)$ and $J_+>q_*$. Hence $0<t(\xi)<1$ and $t(\xi)<J_+$ on some left neighborhood. Formula (38.25) is then a positive trace-one rank-one effect at the pure endpoint of the full positive arc. Equation (36.10) gives $\rho_+=\xi$, whereas the negative branch is still greater than four because $B_\beta<2$. Thus its original joint distance is exactly $\xi$. Its value

$$
 g(E_\xi,U_\beta)
 =d^2(1-t(\xi))+e^2t(\xi)
       -\left[u_\beta\sqrt{1-t(\xi)}
                       +v_\beta\sqrt{t(\xi)}\right]^2
\tag{38.26}
$$

is continuous up to $\xi=4$.

The comparator in (38.2) is continuous from the left there as well. Indeed, for $\zeta=\xi/2\in[3/2,2]$ its scalar interval is $[\zeta-1,\zeta]$. Write $\delta=\zeta-1+a$, $a\in[0,1]$, so that

$$
 N_{\mathrm{geo}}(2\zeta)
    =\min_{a\in[0,1]}H^+_{\zeta-1+a}(1-a).
\tag{38.27}
$$

The displayed algebraic expression (37.3) is continuous on this fixed compact rectangle, including its square-root endpoints. Uniform continuity bounds the difference between the two minima at $\zeta$ and $2$ by
$\sup_{a\in[0,1]}|H^+_{\zeta-1+a}(1-a)-H^+_{1+a}(1-a)|$, which tends to zero as $\zeta\uparrow2$. This proves the stated one-sided continuity without differentiating the selected scalar argument.

At four the continuous difference
$N_{\mathrm{geo}}(\xi)-f(E_\xi,U_\beta)$ is strictly positive by (38.20). It remains positive on some $(4-\varepsilon,4]$, with $0<\varepsilon<1$ chosen inside the feasibility neighborhood. For these levels $t_-=(\xi-8+2B_\beta)/2<0$. Theorem 36.2 therefore gives the full fixed-feedback minimum $M_+(w_\beta,\xi)$, allowing all $r\in[t(\xi),\min\{\sqrt{t(\xi)},J_+\}]$, and its attaining effects (36.7). Since (38.25) is one feasible effect, the inequalities involving $M_+$ and $N_{\mathcal O}$ in (38.24) follow. The full-domain minimum $m$ is no larger than an infimum over its core subset, proving the remaining inequality. Neither this step nor the strict inequality requires attainment of the core infimum.

On the supplied local interval, Theorem 37.5 identifies $N_{\mathrm{geo}}$ with the Section 34 germ. Any initial interval on which that geometric family exhausts all original minimizers must avoid $(4-\varepsilon,4]$ by (38.24), so its supremum is at most $4-\varepsilon<4$. This is an upper obstruction to extending such an interval, not its selected first endpoint.

For the bounded source correspondence, the full realizable domain in (38.1) uses source Theorem 23.2 and the prescribed-diagonal theorem stated by [Jasper--Loreaux--Weiss, arXiv:1602.08435v1, Theorem 1.3](https://arxiv.org/html/1602.08435v1#S1.Thmtheorem3): four singular values equal to one give $|w_j|\le1$ and $\sum_j|w_j|-2\min_j|w_j|\le2$. The witnesses (38.15) instead have direct unitary realizations. That literature result supplies realizability, not an ordering at the producer distance. The uniform estimate (38.7)--(38.9) is a repo-derived metric-dependent deduction; the conditional phase variation is Theorem 36.5 and the attained scalar selector is Theorem 37.5, both applied here without repeating their proofs. The fixed-effect coherence identity is source (23.12), and the complete mixed-effect comparison is Theorem 36.2.

The first-loss obligation still compares $N_{\mathrm{geo}}(\xi)+\kappa\xi$ with every admissible $M_\sigma(w,\xi)$ for all realizable feedbacks on the preceding levels, and must determine the actual equality preimage there. Both signs, mixed effects $r>t_\sigma$, singular effects and all actual unitary lifts remain part of that obligation; the cap and trace-triangle comparisons of Sections 24--37 apply only within their stated hypotheses. The new strict core competitors do not exclude an earlier mixed or nonlocal loss. The exact first boundary, endpoint inclusion or exclusion, all first competing minimizers, the behavior immediately after that boundary, and the determinant-zero variation case remain unresolved. A zero of $\mathscr D$, a cap boundary, or the end of a sufficient screen is not identified with the first loss. At distance four the scalar comparator is attained, and so are the displayed strict competitors and their fixed-feedback effect minima; no global core minimizer is selected by these statements. $\square$

## 追加锚（本行以下为增补区）

## 39. Original first-transition endpoints and a selected level-eighteen-fifths obstruction

**Definition 39.1 (two original first boundaries).** Use the original
$\mathcal K=\operatorname{Dens}_2\times U(4)$, ordinary transpose,
$g,\rho,f=g-\kappa\rho$ and $m$ of source Definition 11.1 and
Definition 33.1. In particular

$$
 \rho(E,U)=\min_{\sigma\in\{+,-\},\ |\lambda|=1}
 \bigl(\|E-E_\sigma\|_{\mathrm F}^2
             +\|U-\lambda U_\sigma\|_{\mathrm F}^2\bigr).
\tag{39.1}
$$

For $0<\xi\le4$ retain exactly $N(\xi)=N_{\mathrm{geo}}(\xi)$
of (38.2) and its unique scalar argument $\delta_\circ(\xi/2)$
from Theorem 37.5. Write

$$
\begin{aligned}
 t&=\xi/2,& \delta&=\delta_\circ(t),& q&=t-\delta,&p&=1-q,\\
 x&=1-\delta/2,& y&=\sqrt{1-x^2},\\
 w_\tau&=(x+\tau iy,x-\tau iy,1,1),&
 \psi_\tau&=\sqrt p\,b_+-\tau i\sqrt q\,b_-,\\
 \mathcal G_\xi
 &=\left\{\left(\overline{\psi_\tau}\,
                    \overline{\psi_\tau}^{\dagger},
             \lambda\operatorname{diag}(w_\tau)U_+\right):
                  \tau\in\{+1,-1\},\ |\lambda|=1\right\},\\
 \mathcal A_\xi
 &=\{(E,U)\in\mathcal K:\rho(E,U)=\xi,\ f(E,U)=m(\xi)\}.
\end{aligned}
\tag{39.2}
$$

All square roots denote their nonnegative real values. Theorem 37.5
supplies $x,y,p,q>0$ and $f=N(\xi)$, $\rho=\xi$ on
$\mathcal G_\xi$. Thus $m(\xi)\le N(\xi)$, but equality is not
part of this definition. The circles in (39.2) retain every actual
feedback representative; their only identification is the one common
scalar phase in (39.1). The orientation $\tau$ is distinct from
the optimizer sign $\sigma$ in that joint minimum.

Define subsets of $(0,4)$ by

$$
\begin{aligned}
 \mathcal B
 &=\{\xi:\exists X\in\mathcal K,\ \rho(X)=\xi,
                    \ X\notin\mathcal G_\xi,\ f(X)\le N(\xi)\},\\
 \mathcal S
 &=\{\xi:m(\xi)<N(\xi)\},\\
 \alpha&=\inf\mathcal B,\qquad \beta=\inf\mathcal S,
 \qquad \inf\varnothing=+\infty.
\end{aligned}
\tag{39.3}
$$

Here $\mathcal B$ is exactly the failure set for
$\mathcal A_\xi=\mathcal G_\xi$: if the value is strictly smaller,
an attained global minimizer lies outside $\mathcal G_\xi$; if the
values coincide, its extra points are precisely additional global
minimizers. Conversely the displayed witness either lowers the value
or is such an additional minimizer. In particular
$\mathcal S\subseteq\mathcal B$. The boundaries $\alpha$ and
$\beta$ therefore concern, respectively, exhaustive geometric equality
and strict value loss in the full original domain.

**Theorem 39.2 (inward accessibility of every original point).**
For every $X\in\mathcal K$ with $0<\rho(X)=\xi\le9$, and every
sequence $\eta_n<\xi$ tending to $\xi$, there are, for all sufficiently
large $n$, original pairs $X_n\to X$ with $\rho(X_n)=\eta_n$.
The attained envelope $m$ is lower semicontinuous on $(0,9]$ and
continuous from the left at every such level. The existing comparator
$N$, the scalar argument in (39.2), and the compact sets
$\mathcal G_\xi$ are continuous on $(0,4]$; for the last assertion
use the Hausdorff metric induced by the product Frobenius norm.

*Proof.* Choose one sign $\sigma$ and one scalar $\lambda_0$
attaining (39.1) at $X=(E,U)$. Put
$a=\|E-E_\sigma\|_{\mathrm F}^2$ and choose a spectral decomposition

$$
 (\lambda_0U_\sigma)^\dagger U
       =Z\operatorname{diag}(e^{i\theta_1},\ldots,e^{i\theta_4})Z^\dagger,
 \qquad Z\in U(4),\quad -\pi\le\theta_j\le\pi.
\tag{39.4}
$$

For $0\le s\le1$ set

$$
\begin{aligned}
 E_s&=(1-s)E+sE_\sigma,\\
 U_s&=\lambda_0U_\sigma Z
       \operatorname{diag}(e^{i(1-s)\theta_1},\ldots,
                            e^{i(1-s)\theta_4})Z^\dagger,\\
 b(s)&=(1-s)^2a+\sum_{j=1}^4[2-2\cos((1-s)\theta_j)].
\end{aligned}
\tag{39.5}
$$

Convexity keeps $E_s$ positive with trace one, including when $E$
is mixed or singular. The matrix $U_s$ is one actual unitary and
$X_0=X$. Evaluating the original distance at the same chosen sign
and scalar gives $\rho(X_s)\le b(s)$ and $b(0)=\xi$.
For every $s>0$, $b(s)<b(0)$: the effect term strictly decreases
if $a>0$, and each nonzero $|\theta_j|\le\pi$ gives a strictly
decreasing chordal term. At least one of these terms is nonzero
because $\xi>0$. This argument does not require the chosen sign
or scalar to remain minimizing along the curve. In particular it
includes a sign tie, a zero feedback trace and eigenvalues $-1$.

The true joint minimum $r(s)=\rho(X_s)$ is continuous, with
$r(0)=\xi$ and $r(s)<\xi$ for $s>0$. For every fixed small
$s_0>0$, its image on $[0,s_0]$ contains $[r(s_0),\xi]$.
For $\eta<\xi$ sufficiently close to $\xi$, let $s(\eta)$ be
the first time in $[0,1]$ that $r(s)=\eta$. It exists by the
intermediate value theorem and compactness of a nonempty level
preimage. For each $s_0>0$, eventually $s(\eta)\le s_0$; hence
$s(\eta)\to0$ as $\eta\uparrow\xi$. The pairs
$X_{s(\eta_n)}$ prove accessibility without replacing the joint
minimum by a fixed sign branch.

Theorem 35.2 gives compact nonempty original levels and attained
minima throughout $(0,9]$. For any converging sequence of levels,
choose global minimizers and a subsequence realizing the lower limit
of their values. Compactness of $\mathcal K$ gives a further limit
$X_*$ at the limiting level, so continuity of $f,\rho$ yields
$m(\xi)\le f(X_*)=\liminf m(\eta_n)$. This proves lower
semicontinuity. Apply accessibility to a global minimizer at $\xi$.
The nearby lower-level pairs have values tending to $m(\xi)$,
giving the reverse upper-limit inequality from the left. Thus

$$
 \lim_{\eta\uparrow\xi}m(\eta)=m(\xi),\qquad 0<\xi\le9.
\tag{39.6}
$$

For comparator continuity, use its existing expression (38.2).
Write $\ell(t)=\max(0,t-1)$ and
$\delta=\ell(t)+[t-\ell(t)]a$, $0\le a\le1$.
The function $H^+_\delta(t-\delta)$ is continuous on this fixed
compact parameter interval, locally uniformly for $0<t\le2$.
Its minimum therefore varies continuously: differences of minima
are bounded by the supremum of differences of the objectives.
For a convergent sequence of parameters, any limit of scalar
minimizers minimizes the limiting objective. Uniqueness in Theorem
37.5 identifies that limit, proving continuity of
$\delta_\circ(t)$. Consequently all entries in (39.2) are
continuous functions of $\xi,\lambda$ for each of the two
orientations. Uniform continuity on compact parameter neighborhoods
and on the scalar circle proves Hausdorff continuity of
$\mathcal G_\xi$. No original minimizing branch has been assumed.
$\square$

**Theorem 39.3 (strict obstruction at the selected geometric minimum
of original level $18/5$).** Put $t_*=9/5$ and

$$
 \delta_*^{\mathrm g}=\delta_\circ(t_*),\qquad
 x_*=1-\delta_*^{\mathrm g}/2,\qquad
 q_*=2x_*-\frac15,\quad p_*=\frac65-2x_*,\quad
 y_*=\sqrt{1-x_*^2}.
\tag{39.7}
$$

This is the existing selected geometric minimum, and

$$
 \frac13<x_*<\frac12,\qquad
 \mathscr D(x_*,p_*)< -\frac{q_*}{56}<0,
 \qquad m(18/5)<N(18/5),
\tag{39.8}
$$

where $\mathscr D$ is exactly (36.43). Each pair in
$\mathcal G_{18/5}$ has arbitrarily close original rank-one
competitors at exactly the same joint distance, with strictly smaller
$g$ and $f$. Their actual feedback diagonals belong to $\mathcal O$.
Moreover $\mathcal S$ contains an interval $(18/5-\varepsilon,18/5]$
for some $\varepsilon>0$.

*Proof.* For fixed $t_*$, the scalar interval in (37.20) becomes
$1/10\le x\le3/5$ under $\delta=2(1-x)$. Set

$$
\begin{aligned}
 p(x)&=\frac65-2x,&q(x)&=2x-\frac15,&y(x)&=\sqrt{1-x^2},\\
 S(x)&=2(c+hx)\sqrt{p(x)}+2hy(x)\sqrt{q(x)},\\
 V(x)&=d^2p(x)+e^2q(x)-S(x)^2,\qquad D_0=d^2-e^2=4h+8s.
\end{aligned}
\tag{39.9}
$$

Theorem 37.5 makes $V(x)-18\kappa/5$ exactly the strictly convex
scalar objective whose unique minimizer is $x_*$. In its interior,

$$
\begin{aligned}
 V'(x)&=-2[D_0+S(x)S'(x)],\\
 S'(x)&=2h\sqrt p-\frac{2(c+hx)}{\sqrt p}
              -\frac{2hx\sqrt q}{y}+\frac{2hy}{\sqrt q}.
\end{aligned}
\tag{39.10}
$$

The rational half-angle bounds of source (22.13) imply

$$
 \frac7{10}<h<\frac34,\quad \frac9{10}<c<1,\quad
 \frac38<s<\frac25,\quad
 0<c-h<\frac14,\quad s^2>\frac17,\quad
 \frac{29}5<D_0<\frac{31}5.
\tag{39.11}
$$

At $x=1/3$, one has $p=8/15$, $q=7/15$,
$y=2\sqrt2/3>9/10$ and $hy=2/3$.
The positive-square comparisons
$7/10<\sqrt p<3/4$ and $\sqrt q<7/10$ give

$$
\begin{aligned}
 0<S(1/3)&<\frac{15}{8}+\frac{14}{15}<3,\\
 S'(1/3)&>\frac{49}{50}-\frac{25}{7}
                       -\frac7{18}+\frac{40}{21}
          =-\frac{242}{225}>-\frac65.
\end{aligned}
\tag{39.12}
$$

Thus $D_0+SS'>29/5-18/5=11/5>0$, so $V'(1/3)<0$.
At $x=1/2$, $p=1/5$, $q=4/5$ and $y=\sqrt3/2$. Here

$$
\begin{aligned}
 S(1/2)&=\frac{2c+h+2h\sqrt3}{\sqrt5}
                       >\frac{92}{45}>2,\\
 S'(1/2)&=\frac{2h}{\sqrt5}-2(c+h/2)\sqrt5
                  -\frac{4h}{\sqrt{15}}+\frac{h\sqrt{15}}2\\
 &<\frac34-5-\frac7{10}+\frac{11}{8}
       =-\frac{143}{40}<-\frac72.
\end{aligned}
\tag{39.13}
$$

For the first bound use $\sqrt3>3/2$ and $\sqrt5<9/4$;
for the second use $2<\sqrt5$, $\sqrt{15}<4$ and
$h\sqrt{15}/2=\sqrt{15/8}<11/8$.
Consequently $D_0+SS'<31/5-7=-4/5<0$, so $V'(1/2)>0$.
Strict scalar convexity now locates its unique minimum strictly
between these two arguments. This proves the first assertion of
(39.8) for the selected point, rather than for an arbitrary
geometric competitor.

Evaluate (36.43) with $p=p(x)$, $q=q(x)$ on
$1/3\le x\le1/2$, and abbreviate $\alpha_0=c-h$.
Here $q\ge7/15$, $y^2\ge3/4$ and
$1/(\sqrt q\,y)<2$. Also

$$
 \frac{x^2}{(1+x)q}\le\frac5{24},\qquad
 \frac{x^2}{1+x}\le\frac16,\qquad hx+c>1.
\tag{39.14}
$$

The first ratio increases on this interval: its derivative has
positive denominator and numerator $x(9x-2)/5$; its value at $1/2$
is $5/24$. The second ratio also increases. Inserting these bounds
into $L_a$ gives

$$
 0<\frac{L_a}{q}
 =\frac{hx^2}{(1+x)q}\frac{\alpha_0\sqrt p}{hx+c}
       +\frac{hx^2}{1+x}\frac1{\sqrt q\,y}
 <\frac5{128}+\frac14=\frac{37}{128}<\frac13.
\tag{39.15}
$$

For $L_b$, use $\sqrt p<3/4$, $\sqrt q<9/10$,
$y>6/7$, $hy>3/5$ and
$h^2x-s^2<1/4-1/7=3/28$. If this last numerator is nonpositive,
$L_b\le\alpha_0\sqrt p<3/16$. If it is positive, then

$$
 L_b<\frac3{16}+\frac3{28}\frac32
              =\frac{39}{112}<\frac38.
\tag{39.16}
$$

Since $L_a/q>0$, both cases imply

$$
 \frac{\mathscr D}{q}=\frac{L_a}{q}L_b-s^2
                      <\frac18-\frac17=-\frac1{56}.
\tag{39.17}
$$

All the square-root bounds used here follow by squaring positive
rational endpoints; $h^2=1/2$ is exact. This proves the strict
obstruction in particular at $x_*$.

We verify its original realization at that same selected point.
For either $\tau$ and every $|\lambda|=1$, use (39.2) with
$x=x_*$, $p=p_*$, $q=q_*$. Before multiplication by $\lambda$,
the actual diagonal data are

$$
 A=2(1+x_*),\quad B=2y_*,\quad
 P=2(hx_*+c),\quad Q=2\tau ihy_*.
\tag{39.18}
$$

The effect is positive, normalized and rank one. Its relative phase
$-\tau i=P\bar Q/(|P||Q|)$ aligns the amplitudes of this one
feedback. Its two original sign branches, including the effect term,
are

$$
 \rho_+=\frac{18}{5},\qquad
 \rho_--\rho_+
   =2\left(\frac{17}{5}-2x_*-2y_*\right)>\frac45>0,
\tag{39.19}
$$

since $x_*+y_*\le\sqrt2<3/2$.
Thus (36.42) holds strictly and the true joint distance is $18/5$.
Theorem 37.5 gives $f=N(18/5)$ at these pairs.

For explicit nearby competitors, let
$k=s\sqrt{q_*}/L_a>0$, with $L_a$ evaluated at this selected
point. Specialize the actual curve of Theorem 36.5 to $a=kb$ and
write its real parameter as $b$. Thus, near $b=0$, put

$$
\begin{aligned}
 X_b&=-\cos b\cos(kb)
       +\sqrt{(1+x_*)^2-\cos^2b\sin^2(kb)},&
 Y_b&=\sqrt{1-X_b^2},\\
 w_{\tau,b}&=(e^{ikb}(X_b+\tau iY_b),
               e^{ikb}(X_b-\tau iY_b),e^{i\tau b},e^{-i\tau b}),\\
 U_{\lambda,\tau,b}&=\lambda\operatorname{diag}(w_{\tau,b})U_+,\\
 P_{\lambda,b}&=2\lambda(hX_be^{ikb}+c\cos b),&
 Q_{\lambda,\tau,b}&=2\lambda\tau(ihY_be^{ikb}-s\sin b),\\
 \psi_{\lambda,\tau,b}&=\sqrt{p_*}\,b_+
       +\frac{P_{\lambda,b}\overline{Q_{\lambda,\tau,b}}}
              {|P_{\lambda,b}||Q_{\lambda,\tau,b}|}
                                      \sqrt{q_*}\,b_-,&
 E_{\lambda,\tau,b}&=\overline{\psi_{\lambda,\tau,b}}\,
                     \overline{\psi_{\lambda,\tau,b}}^{\dagger}.
\end{aligned}
\tag{39.20}
$$

The square roots are positive near zero, and both amplitudes are
nonzero there. Every diagonal entry has modulus one, so this is an
actual unitary, shared by the entire normalized effect. The same
$w_{\tau,b}$ determines $A,B,P,Q$. In particular (36.48) gives
$A=2(1+x_*)$ identically; the population and purity are unchanged.
The strict sign gap (39.19) persists by continuity, proving
$\rho(E_{\lambda,\tau,b},U_{\lambda,\tau,b})=18/5$ for all
sufficiently small $b$. The common scalar cancels from the effect
phase; there are no coordinate phases being quotiented.

The existing expansion (36.54)--(36.55), applied to (39.20), gives

$$
 \sqrt{p_*}|P_{\lambda,b}|+\sqrt{q_*}|Q_{\lambda,\tau,b}|
       -S(x_*)=-\frac{\mathscr D}{L_a}b^2+o(b^2)>0
\tag{39.21}
$$

for every sufficiently small nonzero $b$, for both orientations.
The exact same-feedback identity (23.12), attained by the effect
phase in (39.20), therefore gives a strictly smaller $g$; the exact
unchanged distance gives a strictly smaller $f$. These compare
against the attained selected minimum $N(18/5)$, proving
$m(18/5)<N(18/5)$.

At the base, $A<3<A_0$, $B<2<23/6$ and
$A+B=2(1+x_*+y_*)>4$. All three strict inequalities persist
along (39.20), so the feedbacks lie in $\mathcal O$. This is an
actual strict competitor and does not assert attainment of its
core infimum. Finally (39.6) and continuity of $N$ preserve the
strict value gap on a left neighborhood of $18/5$, proving the last
assertion. $\square$

**Theorem 39.4 (the original algebraic correspondence).** In real and
imaginary matrix coordinates, the graphs of $\rho,f,m,N$, the
relations $(\xi,X)$ with $X\in\mathcal A_\xi$ or
$X\in\mathcal G_\xi$, and the sets $\mathcal B,\mathcal S$ are
semialgebraic over the field of real algebraic numbers. The boundaries
in (39.3) are finite real algebraic numbers and satisfy

$$
                 0<\alpha\le\beta<\frac{18}{5}.
\tag{39.22}
$$

*Proof.* Here is the bridge to actual original matrices. Use
$V=UU_+^\dagger$ with its full real and imaginary entries and
$V^\dagger V=I_4$, and use

$$
 F=\begin{pmatrix}p&z\\\bar z&1-p\end{pmatrix},\quad
 0\le p\le1,\quad |z|^2\le p(1-p),\qquad
 E=(TFT^\dagger)^{\mathsf T},\quad U=VU_+.
\tag{39.23}
$$

These polynomial constraints describe exactly
$\operatorname{Dens}_2\times U(4)$: unitary conjugation and ordinary
transpose preserve positivity and trace, and $T$ is unitary.
No feedback entries, effect ranks or signs have been discarded.
Set $w_j=V_{jj}$ and introduce real $A,B\ge0$ with

$$
 A^2=|w_1+w_2+w_3+w_4|^2,\qquad
 B^2=|w_1-w_2+i(w_3-w_4)|^2.
\tag{39.24}
$$

These equations select precisely the original trace moduli, including
their zeros. With $P,Q$ from (23.2), the exact same-object formulas
are

$$
\begin{aligned}
 \epsilon&=2[p(1-p)-|z|^2],\\
 g&=d^2p+e^2(1-p)-p|P|^2-(1-p)|Q|^2
                                      -2\operatorname{Re}(Pz\bar Q),\\
 \rho&=\min\{10-2p-2A,\ 8+2p-2B\}-\epsilon.
\end{aligned}
\tag{39.25}
$$

The graph of the last minimum is a finite disjunction: its value
is no larger than either branch and equals at least one. Thus it
includes sign ties and the common impurity subtraction with their
original meanings. All other expressions are polynomials in real
coordinates, with (39.24) as auxiliary equations and inequalities.
In particular no positive square-root columns at singular $E$ are
needed; source (22.1) justifies their exact cancellation in $g$.

The fixed entries of $T,U_\pm$ and $h,c,s,d,e$ are algebraic by
source (6.3), (6.7) and the half-angle formulas. The root formula of
Theorem 21.3 makes $\kappa$ algebraic as well. Consequently (39.23)--
(39.25) and $f=g-\kappa\rho$ have real algebraic coefficients.
For every attained level the value graph has the exact description

$$
\begin{aligned}
 v=m(\xi)\quad\Longleftrightarrow\quad
 &\bigl[\exists X\in\mathcal K:\rho(X)=\xi,\ f(X)=v\bigr]\\
 &\text{and}\quad
 \bigl[\forall X'\in\mathcal K:\rho(X')=\xi
                                      \Longrightarrow f(X')\ge v\bigr].
\end{aligned}
\tag{39.26}
$$

Similarly use the compact interval (37.20), the displayed expression
$H^+_\delta(t-\delta)$ and existential attainment plus a universal
lower bound to describe $N$. Each radicand in that expression is
represented by a variable $r\ge0$, $r^2$ equal to that radicand;
thus no extra root sign enters. The same relation with the minimizing
$\delta$ free describes its unique argument. Formula (39.2),
with $\lambda\bar\lambda=1$ and its two orientations, then gives
$\mathcal G$ semialgebraically. Equality to (39.26) gives
$\mathcal A$. Projection, complement and the comparisons in
(39.3) describe $\mathcal B,\mathcal S$.

These are applications of real quantifier elimination to the verified
original relations. The general projection, compact-minimum and
one-dimensional finiteness tools are the same intermediates used in
[AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VII.md
§§130--132](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_VII.md).
In the primary statements, Basu,
[*Algorithms in Real Algebraic Geometry: A Survey*,
arXiv:1409.1534v1, §2.1, Theorem 2.1](https://arxiv.org/pdf/1409.1534v1),
gives quantifier elimination for first-order polynomial sign formulas;
Guo--Kim--Jiao--Pham,
[*On types of KKT points in polynomial optimization*,
arXiv:2004.12315v1, §2.1, Theorem 2.1](https://arxiv.org/html/2004.12315v1),
gives semialgebraic projection and its finite Boolean closure.
The coefficient-preserving formulation applies over the real closed
field of real algebraic numbers and then in its extension $\mathbb R$.
Hence the resulting one-variable descriptions use algebraic
coefficients. A Boolean description in one variable changes truth
only at roots of its finitely many nonzero polynomials. It follows
that all finite component endpoints are algebraic and that there are
only finitely many components. This is a use of those general tools,
not a new projection or compact-minimum theorem.

Theorems 34.3 and 37.5 identify the full minimizing set with
$\mathcal G_\xi$ on some initial positive interval, so neither bad
set meets that interval. Theorem 39.3 puts a left neighborhood of
$18/5$ in $\mathcal S$. Both sets are nonempty, and
$\mathcal S\subseteq\mathcal B$. Their infima therefore obey
(39.22) and are finite component endpoints of their semialgebraic
sets. The algebraicity assertion follows. This provides no evaluated
polynomial or selected numerical value for either boundary.
$\square$

**Theorem 39.5 (endpoint geometric optimality and exhaustive-equality
alternatives).** At both $b=\alpha$ and $b=\beta$,

$$
 m(b)=N(b),\qquad \mathcal G_b\subseteq\mathcal A_b,
 \qquad \lim_{\xi\to b}m(\xi)=m(b).
\tag{39.27}
$$

In particular neither boundary belongs to $\mathcal S$.
Below $\alpha$ the entire minimizing set is $\mathcal G_\xi$;
below $\beta$, and at $\beta$, the value is $N(\xi)$.
At either boundary the exact profile of Theorem 36.2 consequently
satisfies

$$
 M_\sigma(w,b)\ge N(b)+\kappa b
 \quad\text{for every realizable }w\text{ and every admissible sign }\sigma.
\tag{39.28}
$$

The maximal initial positive-distance prefix on which
$\mathcal A_\xi=\mathcal G_\xi$ is $(0,\alpha)$ if
$\mathcal A_\alpha\setminus\mathcal G_\alpha\ne\varnothing$,
and $(0,\alpha]$ otherwise. In the latter case there is
$\varepsilon_\alpha>0$ such that every
$\alpha<\xi<\alpha+\varepsilon_\alpha$ has an actual nongeometric
global minimizer. In the former case an additional endpoint minimizer
is attained; persistence of such a minimizer to the right does not
follow from endpoint equality alone. There is
$\varepsilon_\beta>0$ such that

$$
        m(\xi)<N(\xi)\qquad
                  (\beta<\xi<\beta+\varepsilon_\beta).
\tag{39.29}
$$

*Proof.* Definition (39.3), attainment, and the feasible set
$\mathcal G_\xi$ imply the asserted equality of minimizing sets
for $0<\xi<\alpha$ and of values for $0<\xi<\beta$.
Left continuity (39.6) and continuity of $N$ prove equality of
values at both endpoints. Every pair in $\mathcal G_b$ attains
that value at the exact original distance, proving its global
optimality there. Applying the original-pair lower bound at $b$
to each of the attainable fixed-feedback effect minima (36.6)
proves (39.28), retaining both admissible signs and every actual
lift. Conversely those inequalities and geometric attainment imply
the same endpoint value equality.

For any sequence $\xi_n\to b$, compactness gives the lower
semicontinuity inequality of Theorem 39.2, while geometric feasibility
and continuity give the upper inequality

$$
 m(b)\le\liminf m(\xi_n)
       \le\limsup m(\xi_n)\le\lim N(\xi_n)=N(b)=m(b).
\tag{39.30}
$$

This proves full value continuity specifically at these endpoints;
right accessibility of every original point has not been asserted.

At $\alpha$, (39.27) identifies membership in $\mathcal B$
exactly with an additional attained endpoint minimizer. This decides
whether the initial exhaustive prefix includes its endpoint.
If $\alpha\notin\mathcal B$, finiteness of the components of
$\mathcal B$, its nonemptiness, and its infimum $\alpha$ force
an interval immediately to the right to belong to $\mathcal B$.
At any such level, either $m<N$, in which case every global minimizer
is nongeometric, or $m=N$, in which case the witness in (39.3)
is an additional global minimizer. This proves the claimed existence.
If $\alpha\in\mathcal B$, it may instead be an isolated point
of that set; finite-component semialgebraicity does not exclude this.
Since $\beta\notin\mathcal S$, the same finite-component argument
forces a right interval in $\mathcal S$, proving (39.29).
These implications do not identify $\alpha$ with $\beta$.
$\square$

**Theorem 39.6 (actual minimizing branches and endpoint limits).**
For either $b=\alpha$ or $b=\beta$, every sequence of actual
global minimizers at levels $\xi_n\to b$ has a convergent
subsequence, and every such limit belongs to $\mathcal A_b$.
There is a sufficiently short interval $(b,b+\varepsilon)$ on which
one can choose a real analytic semialgebraic branch

$$
 \xi\longmapsto X(\xi)=(E(\xi),U(\xi))\in\mathcal A_\xi
\tag{39.31}
$$

of actual original matrices, with an actual limit
$X_b\in\mathcal A_b$ as $\xi\downarrow b$.
At $b=\beta$ this branch is strictly below $N$ at every level
of the interval. At $b=\alpha$ with
$\mathcal A_\alpha=\mathcal G_\alpha$, the branch can be chosen
nongeometric throughout that interval and has $X_\alpha\in
\mathcal G_\alpha$. More generally, whenever all levels in such
an interval have nongeometric global minimizers, a branch (39.31)
can be chosen among them.

If $\mathcal A_b=\mathcal G_b$, every choice of global minimizers
approaching $b$ has distance to $\mathcal G_\xi$ tending to zero.
If a sequence instead remains at product Frobenius distance at least
$\eta>0$ from $\mathcal G_{\xi_n}$, a subsequential limit is an
additional actual minimizer in
$\mathcal A_b\setminus\mathcal G_b$.

*Proof.* Compactness supplies subsequential limits. Equations
(39.27)--(39.30) and continuity of $\rho,f$ put each limit at
$\rho=b$, $f=N(b)=m(b)$, proving actual endpoint attainment.
Hausdorff continuity of $\mathcal G_\xi$ preserves any fixed
positive separation. If $\mathcal A_b=\mathcal G_b$ but the
distance did not tend to zero, compactness would give just such a
separated subsequential limit, a contradiction. The product norm
here tests separation from the full scalar orbits in (39.2); it
does not replace the original metric (39.1).

For selection use the semialgebraic relation of actual matrices
proved in Theorem 39.4, with nonempty compact fibers
$F(\xi)=\mathcal A_\xi$ and the semialgebraic submap
$\widetilde F(\xi)=\mathcal A_\xi\cap\mathcal G_\xi$.
Extend both by the empty set outside $(0,4)$.
Drusvyatskiy--Lewis,
[*Semi-algebraic functions have small subdifferentials*,
arXiv:1004.0368v1, Theorem 2.25 and Corollary 2.27](https://arxiv.org/html/1004.0368v1),
trivialize a semialgebraic set-valued graph over a finite partition
of its domain, compatibly with a semialgebraic submap. Specifically
these statements require a semialgebraic graph and, for the theorem,
a continuous semialgebraic projection; the coordinate projection
from our actual graph satisfies this. No finite-fiber, genericity or
smooth-minimizer hypothesis is required. Finiteness of the parameter
partition allows $(b,b+\varepsilon)$ to lie in one part after
shrinking. Its trivialization is a semialgebraic homeomorphism

$$
 \Theta:\operatorname{gph}F|_{(b,b+\varepsilon)}
                \longrightarrow (b,b+\varepsilon)\times Y,
 \qquad
 \Theta(\operatorname{gph}\widetilde F)
                =(b,b+\varepsilon)\times\widetilde Y,
 \quad \widetilde Y\subseteq Y,
\tag{39.32}
$$

preserving the first coordinate. Fixing $y_0\in Y$ gives
$(\xi,X(\xi))=\Theta^{-1}(\xi,y_0)$, a continuous
semialgebraic section. When nongeometric minimizers are required,
the fibers $F\setminus\widetilde F$ are nonempty throughout the
interval, so $Y\setminus\widetilde Y\ne\varnothing$; choose
$y_0$ there. At $\beta$, (39.29) makes every fiber strictly
nongeometric. At $\alpha$ without additional endpoint minimizers,
Theorem 39.5 supplies the needed nongeometric right-hand fibers.

Apply Drusvyatskiy--Ioffe--Lewis,
[*Generic minimizing behavior in semi-algebraic optimization*,
arXiv:1504.07694v1, Theorem 3.4](https://arxiv.org/html/1504.07694v1),
to this single-valued semialgebraic section on a real interval.
Its analytic constant-rank stratification leaves a smaller full
interval adjacent to $b$ on which the section is real analytic.
This applies to the already selected section, and requires none of
the finite-valued or small-graph hypotheses of that paper's later
selection and Sard results. For a bounded real coordinate of the
section, assign arbitrary endpoint values on a closed subinterval
$[b,b+\varepsilon/2]$. The extended function is semialgebraic.
Guo--Kim--Jiao--Pham, §2.1, Lemma 2.2 cited in Theorem 39.4,
partitions that interval into finitely many pieces where it is
constant or strictly monotone. Consequently it has a finite
one-sided limit at $b$. All real and imaginary matrix coordinates
are bounded by compactness of $\mathcal K$; taking their finitely
many limits gives $X_b\in\mathcal K$. The first paragraph puts
it in $\mathcal A_b$, and in $\mathcal G_b$ when that is the
whole endpoint minimizing set. These branches consist of actual
$E,U$; the derived $w,A,B,P,Q$ always belong to that same $U$.
The limit may lie on a boundary of $\mathcal O$ and need not
attain $N_{\mathcal O}(b)$. $\square$

**Unresolved mathematical obligations 39.7.** The inequalities
$0<\alpha\le\beta<18/5$, algebraicity and endpoint geometric
optimality do not evaluate either boundary, prove their coincidence,
or determine either full equality preimage. The outstanding comparison
remains the ordering of every admissible
$M_\sigma(w,\xi)$ against $N(\xi)+\kappa\xi$ on the preceding
levels, with its attained original equality cases. It includes mixed
and singular effects, both optimizer signs, all actual unitary lifts,
and any additional nonlocal minimizing branch. The analytic sections
in Theorem 39.6 supply existence and endpoint limits, not their
explicit identification or exhaustion. An additional separated
endpoint pair is forced only under the stated positive-separation
hypothesis; coalescence with the geometric family remains possible.
No core-infimum attainment or generic nondegeneracy is implied.
A zero of $\mathscr D$ still requires higher-order and global
comparison, and is not identified with either first boundary.

## 追加锚（本行以下为增补区）
