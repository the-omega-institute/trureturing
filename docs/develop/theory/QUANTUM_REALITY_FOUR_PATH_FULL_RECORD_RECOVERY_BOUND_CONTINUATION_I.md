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
