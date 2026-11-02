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
