# 情境时空算术的量子扩展：恢复曲率、半群与联合极限

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](284_306_RECOVERY_BUDGET_ENDPOINTS.md) · [续卷](330_350_SMALL_BUDGET_AND_CORRECTIONS.md)


<a id="entry-962"></a>

## 追加锚（本行以下为增补区）

<a id="section-307"></a>

## 307. 正定支撑分支的二参数代数重建

**定义 307.1（列权重单纯形与候选矩阵）。** 固定正半径六态模型，记 $b=(1/a_1,1/a_2,1/a_3)$、$A=\|b\|_2^2$，并令 $w_i=b_i^2/A$。对开单纯形中的点

$$
x_i>0,\qquad x_1+x_2+x_3=1,
$$

定义

$$
\begin{aligned}
\beta&=\sqrt{\sum_iw_ix_i^2},&
m&=\sum_iw_ix_i,\\
c_i&=x_i^2\left(1-2x_i+\frac{\beta^2}{w_i}\right),&
v&=\frac{\operatorname{diag}(x)b+\beta b}
{\|\operatorname{diag}(x)b+\beta b\|_2},\\
\lambda&=A\beta,&
G_x&=bb^{\mathsf T}+\lambda I-2\lambda vv^{\mathsf T},\\
Q_x&=G_x\operatorname{diag}(x),&
S_x&=\operatorname{sym}Q_x.
\end{aligned}
\tag{307.1}
$$

再记三个实数及其组合

$$
g_{ij}=(S_x)_{ij}v_iv_j\quad(i<j),
\qquad
\mathcal T_x=g_{12}g_{13}+g_{12}g_{23}+g_{13}g_{23}.
\tag{307.2}
$$

称 $x$ 可准入，当且仅当

$$
c_1=c_2=c_3=:c,
\qquad \mathcal T_x\ge0.
\tag{307.3}
$$

这里三个 $c_i$ 自动严格为正，因为 $\beta^2\ge w_ix_i^2$，故括号内至少为 $(1-x_i)^2>0$。另外 $\beta^2<m$，因为每个 $0<x_i<1$。

**定理 307.2（正定支撑的精确代数刻画）。** 第303节的实际最优支撑矩阵 $G$ 正定，当且仅当式（307.3）有一个可准入点；这个点存在时唯一。对它有 $\mathcal T_x>0$，并可重建

$$
\begin{aligned}
Z_*&=A\beta vv^{\mathsf T},&G&=G_x,\\
D_a&=\frac{A^{3/2}(m-\beta^2)}{\sqrt c},&
\kappa_a&=\frac{\sqrt c}{2\sqrt A(m-\beta^2)},\\
M_*&=\frac{G_x\operatorname{diag}(x)}{A(m-\beta^2)}.
\end{aligned}
\tag{307.4}
$$

所以第305节的奇异支撑判据未通过时，完整端点解等价于开单纯形内两个标量等式及一个标量不等式的唯一可准入解；无需在这一表述中继续把原、对偶矩阵的全部条目当作独立未知量。

证明。先对任意开单纯形点建立恒等式，不预设可准入性。令 $X=\operatorname{diag}(x)$、$n=b/\sqrt A$、$n'=Xb/(\beta\sqrt A)$。两个向量都是单位向量，且 $n\cdot n'=m/\beta>0$。由定义，$v=(n+n')/\|n+n'\|_2$。反射 $R_v=I-2vv^{\mathsf T}$ 因而满足

$$
R_vXb=-\beta b,\qquad R_vb=-Xb/\beta.
\tag{307.5}
$$

若 $\theta$ 是 $v$ 与 $n$ 的夹角，则 $\cos(2\theta)=m/\beta$。因为 $\beta^2<m$，有 $\lambda=A\beta<A\cos(2\theta)$。式（303.6）的二维块计算遂给出

$$
G_x\succ0.
\tag{307.6}
$$

这个结论对每个单纯形点都成立，不依赖式（307.3）。式（307.5）又给出

$$
Q_xb=A(m-\beta^2)b.
\tag{307.7}
$$

接着验证共同核方向。写 $v=\gamma(X+\beta I)b$、$B=b\cdot v$、$C=b\cdot Xv$、$V=v\cdot Xv$。由 $b^{\mathsf T}X^2b=A\beta^2$，有 $C=\beta B$；而 $B/\gamma=A(m+\beta)$。因此

$$
\begin{aligned}
(Q_x+Q_x^{\mathsf T})v
&=Cb+BXb-2\lambda Vv\\
&=(B/\gamma-2\lambda V)v
=(\operatorname{Tr}Q_x)v.
\end{aligned}
\tag{307.8}
$$

最后一个等式使用 $\operatorname{Tr}X=1$、$\lambda=A\beta$。所以 $\mathcal C(S_x)v=0$，其中 $\mathcal C(S)=(\operatorname{Tr}S)I-2S$。

这一核恒等式将锥可行性精确化为式（307.3）的标量条件。令 $V_0=\operatorname{diag}(v)$。对每个 $y\in\mathbb R^3$，

$$
y^{\mathsf T}V_0\mathcal C(S_x)V_0y
=2\sum_{i<j}g_{ij}(y_i-y_j)^2.
\tag{307.9}
$$

这里 $g_{ij}$ 暂不要求非负。左侧矩阵的任一二阶主子式均为 $4\mathcal T_x$。因此 $\mathcal C(S_x)$ 左上二阶主子式为 $4\mathcal T_x/(v_1^2v_2^2)$。记其余两个特征值为 $\rho_1,\rho_2$；因为单位向量 $v$ 在核中，该主子式也等于 $v_3^2\rho_1\rho_2$，包括额外零特征值的情形。另一方面，

$$
\rho_1+\rho_2
=\operatorname{Tr}\mathcal C(S_x)
=\operatorname{Tr}Q_x>0,
$$

因为 $G_x\succ0$ 且 $X\succ0$。故 $\rho_1,\rho_2$ 都非负恰好等价于其乘积非负，也就是

$$
\mathcal C(S_x)\succeq0
\quad\Longleftrightarrow\quad\mathcal T_x\ge0.
\tag{307.10}
$$

现假设 $x$ 可准入。由 $G_x=bb^{\mathsf T}+\lambda R_v$ 和式（307.5），逐列计算得到

$$
\frac{\|G_xe_i\|_2^2}{b_i^2}
=A\left(1-2x_i+\frac{\beta^2}{w_i}\right).
\tag{307.11}
$$

取 $s=1/\sqrt{Ac}$、$Q=sQ_x$，则

$$
\|Qe_i\|_2=b_i\qquad(i=1,2,3).
\tag{307.12}
$$

各列还沿着 $G_xe_i$ 的正方向。因此三条列球约束全部可行且满足支撑取等；式（307.10）保证耗散锥可行，式（307.8）保证与 $Z=\lambda vv^{\mathsf T}$ 的互补关系。原目标为

$$
b^{\mathsf T}Qb=sA^2(m-\beta^2),
$$

并与对偶列支撑值相等。第298节的弱对偶关系证明 $Q,Z$ 同时最优。代入 $s$，再按 $M_*=(A/D_a)Q$ 归一化，就得到式（307.4）。支撑矩阵为正定的 $G_x$，因此可准入点必属于实际正定支撑分支。

反过来，设实际最优支撑 $G\succ0$。第303节给出

$$
Q=GH,\qquad
H=\operatorname{diag}(h_i),\qquad
h_i=\frac{b_i}{\|Ge_i\|_2}>0,
\qquad Qb=qb,\quad q=D_a/A.
\tag{307.13}
$$

写 $s=\operatorname{Tr}H$、$\beta_H=\|Hb\|_2/\sqrt A$、$m_H=b^{\mathsf T}Hb/A$。由 $Qb=qb$ 得 $R_vHb$ 平行于 $b$。它与 $v$ 的内积等于 $-v\cdot Hb<0$，而 $v\cdot b>0$，故该比例系数为负。反射保范数，因而

$$
R_vHb=-\beta_Hb,\qquad
v=\frac{Hb+\beta_Hb}{\|Hb+\beta_Hb\|_2},
\qquad q=Am_H-\lambda\beta_H.
\tag{307.14}
$$

令 $v=\gamma(H+\beta_HI)b$。与式（307.8）相同的展开给出 $b\cdot Hv=\beta_H(b\cdot v)$，以及

$$
(Q+Q^{\mathsf T})v
=\bigl(A(m_H+\beta_H)-2\lambda(v\cdot Hv)\bigr)v.
$$

将它与实际互补关系 $(Q+Q^{\mathsf T})v=(\operatorname{Tr}Q)v$ 比较，得到

$$
\lambda s=A\beta_H.
\tag{307.15}
$$

取 $x_i=h_i/s$，则 $\beta_H=s\beta$，从而 $\lambda=A\beta$，式（307.14）中的 $v$ 正是定义307.1的向量。于是实际 $G$ 等于 $G_x$。全部列范数约束取等，将式（307.11）代入 $h_i\|Ge_i\|_2=b_i$，得到

$$
c_i=\frac1{As^2}
$$

对三个坐标同时成立。实际耗散锥可行，再由式（307.10）可得 $\mathcal T_x\ge0$，所以这个 $x$ 可准入。

最后，第298节使实际原、对偶最优矩阵均唯一。对每个可准入点，$G$ 可逆且 $H=G^{-1}Q$，故 $H$ 也唯一，进而 $x_i=h_i/\operatorname{Tr}H$ 唯一。该节还使实际 $\mathcal C(\operatorname{sym}Q)$ 的秩为二，因此上述两个非零特征值的乘积严格为正；式（307.10）的主子式关系遂给出 $\mathcal T_x>0$。证毕。

**命题 307.3（无限制曲率的列权重方差表达）。** 对定理307.2的唯一可准入点，令

$$
u_i=x_i(1-x_i),\qquad
f=\sum_iw_iu_i=m-\beta^2,\qquad
\mathcal V_x=\sum_iw_i(u_i-f)^2.
\tag{307.16}
$$

则第301节的旋转位移及无限制曲率满足

$$
\Omega_*b=\frac{(\operatorname{diag}(u)-fI)b}{2f},
\qquad
\Gamma_a=-\frac{\sqrt c\,\mathcal V_x}{4\sqrt A\,f^3}
=-\kappa_a\frac{\mathcal V_x}{2f^2}.
\tag{307.17}
$$

证明。式（307.5）与 $\lambda=A\beta$ 给出 $G_xb=A(I-X)b$，其中 $X=\operatorname{diag}(x)$。将它与式（307.7）代入 $M_*^{\mathsf T}-M_*=2\Omega_*$，得到

$$
2\Omega_*b
=\frac{XG_xb-G_xXb}{Af}
=\frac{(X(I-X)-fI)b}{f}.
$$

这证明第一个等式，并给出 $\|\Omega_*b\|_2^2=A\mathcal V_x/(4f^2)$。再用第301节的 $\Gamma_a=-\|\Omega_*b\|_2^2/D_a$ 和式（307.4），即得式（307.17）。证毕。

这里得到的是正定支撑分支的有限代数刻画和唯一重建，并未给出两个标量等式的一般根式解。条件 $\mathcal T_x\ge0$ 仍须检查；本节没有证明所有满足列范数等式的单纯形点自动满足它，也没有由正定性推出 $G_x$ 逐条目为正或半群的最大角点在所有参数上固定。

<a id="entry-964"></a>

## 追加锚（本行以下为增补区）

<a id="section-308"></a>

## 308. 整个奇异支撑分支的精确曲率与符号分离

**定理 308.1（奇异支撑的半径分离与两条曲率）。** 固定正半径六态模型。若第305节的候选坐标通过奇异支撑判据，将该坐标写在最后，沿用该节的 $p=(p_1,p_2)$、$z$、$r=\sqrt{p_1^2+p_2^2+z^2}$、$q$、$K$、$u$、$E$，并记

$$
U=p_1^2,\qquad V=p_2^2,\qquad L=r+z,
\qquad
\Delta=(z^2+U)(z^2+V)=z^2r^2+UV,
\qquad t=\sqrt{UV/\Delta}.
\tag{308.1}
$$

则

$$
z^2>U+V,\qquad 0<t<\frac13,
\tag{308.2}
$$

而第300节的两条端点二阶系数具有精确表达

$$
\begin{aligned}
\Gamma_a&=-\frac{UV(1-t)}{2r^2q^3}<0,\\
\Gamma_a+\Theta_a
&=\frac{UV(1-t)}{2r^2q^3}
\left(\frac1t-\frac zL\right)>0.
\end{aligned}
\tag{308.3}
$$

特别地，

$$
\frac{\Gamma_a+\Theta_a}{-\Gamma_a}
=\frac1t-\frac zL>\frac52,
\qquad
\Gamma_a+\Theta_a>\frac{5UV}{6r^2q^3}.
\tag{308.4}
$$

这里不要求 $p_1=p_2$，也包括最后一列范数恰好饱和的奇异支撑临界点。式（308.4）仅给出明确的比较界，不声称其中常数最优。

证明。先将范数判据转成无量纲限制。由 $U,V,z>0$ 可知 $0<t<1$。第305节的 $q$ 公式给出

$$
\begin{aligned}
q^2
&=\frac{U(z^2+U)+V(z^2+V)+2\sqrt{UV\Delta}}{r^2}\\
&=U+V+\frac{2\Delta(t-t^2)}{r^2}
=U+V+\frac{2z^2t}{1+t}.
\end{aligned}
\tag{308.5}
$$

最后一步使用 $\Delta(1-t^2)=z^2r^2$。通过的候选满足 $\|u\|_2^2+q^2\le z^2$，从而 $q^2\le z^2$。式（308.5）的最后一项严格为正，故 $z^2>U+V$。又由 $UV\le(U+V)^2/4$，以及 $y\mapsto y/(z^2r^2+y)$ 的单调性，

$$
t\le\frac{U+V}{r^2+z^2}<\frac13.
\tag{308.6}
$$

第二个严格不等式正是 $U+V<z^2$ 的结果。这证明式（308.2）。

下面计算曲率。记

$$
H=\operatorname{diag}(h_1,h_2),\qquad
h_1=\frac{p_1}{r\sqrt{z^2+U}},\qquad
h_2=\frac{p_2}{r\sqrt{z^2+V}}.
\tag{308.7}
$$

第305节给出

$$
Q=\begin{pmatrix}K&u\\0&q\end{pmatrix},
\qquad M_*=Q/q,\qquad
D_a=r^2q,\qquad \lambda=zr,
\qquad v=\frac{(p,L)}{\sqrt{2rL}}.
\tag{308.8}
$$

由于 $K=G_0H$、$G_0p=r^2p$、$Kp+zu=qp$，

$$
2q\Omega_*b
=\begin{pmatrix}(r^2H-qI_2)p\\ u\cdot p\end{pmatrix},
\qquad
u\cdot p=z(Vh_1+Uh_2).
\tag{308.9}
$$

第二个等式可由
$q=z^2(h_1+h_2)+Uh_1+Vh_2$ 代入 $zu=qp-Kp$ 得到。令

$$
\begin{aligned}
\mathcal N
&=\|(r^2H-qI_2)p\|_2^2+(u\cdot p)^2\\
&=UV(r^2+z^2)(h_1-h_2)^2\\
&\quad+z^2\left[V(z^2+V)h_1^2
+U(z^2+U)h_2^2+2UVh_1h_2\right].
\end{aligned}
\tag{308.10}
$$

将前两个分量写为 $p_1[V(h_1-h_2)-z^2h_2]$ 与
$p_2[U(h_2-h_1)-z^2h_1]$ 后平方展开，即得第二式。

这个平方和实际上大幅简化。写 $q_1=z^2+U$、$q_2=z^2+V$，则

$$
h_1h_2=\frac t{r^2},\qquad
h_1^2+h_2^2=\frac{z^2(U+V)+2UV}{r^2\Delta}.
\tag{308.11}
$$

代入式（308.10），得到

$$
\begin{aligned}
\frac{\mathcal N}{UV}
&=\frac{(r^2+z^2)[z^2(U+V)+2UV]+z^2(q_1^2+q_2^2)}{r^2\Delta}-2t\\
&=2(1-t).
\end{aligned}
\tag{308.12}
$$

最后一步仅需把 $q_1,q_2$ 展开，并使用 $r^2=U+V+z^2$，分式的分子恰为 $2r^2\Delta$。由此

$$
\|\Omega_*b\|_2^2=\frac{UV(1-t)}{2q^2}.
\tag{308.13}
$$

第301节的 $\Gamma_a=-\|\Omega_*b\|_2^2/D_a$ 立即给出式（308.3）的第一式。

令 $d_1,d_2$ 为 $S_*=\operatorname{sym}M_*$ 的两个较小特征值。第298节给出第三个特征值 $d_3=d_1+d_2$，故 $\mathcal C(S_*)$ 的谱为 $2d_1,2d_2,0$，单位核向量为 $v$。其左上二阶主子式一方面是 $\det E/q^2$，另一方面是 $4d_1d_2v_3^2$。由 $v_3^2=L/(2r)$，

$$
d_1d_2=\frac{r\det E}{2Lq^2}.
\tag{308.14}
$$

接着由 $E=(\operatorname{Tr}K+q)I_2-K-K^{\mathsf T}$ 计算行列式：

$$
\begin{aligned}
\det E
&=-V(z^2+U)h_1^2-U(z^2+V)h_2^2
+2(UV+zr^2L)h_1h_2\\
&=\frac{2UV(t-1)}{r^2}+2zLt.
\end{aligned}
\tag{308.15}
$$

为核对第一式，可写 $K_{11}=r(r-V/L)h_1$、$K_{22}=r(r-U/L)h_2$、
$K_{12}+K_{21}=rp_1p_2(h_1+h_2)/L$，再使用
$\det E=q^2-(K_{11}-K_{22})^2-(K_{12}+K_{21})^2$。
第二式则使用 $V(z^2+U)h_1^2=U(z^2+V)h_2^2=UV/r^2$ 和式（308.11）。

第301节的 $\Theta_a=\lambda d_1d_2/(2D_a)$ 与式（308.12）至（308.15）遂给出

$$
\Gamma_a+\Theta_a
=\frac{\mathcal F}{4r^2q^3},
\qquad
\mathcal F=\frac{zr^2}{L}\det E-2UV(1-t).
\tag{308.16}
$$

将行列式代入，并使用 $z^2r^2=UV(1-t^2)/t^2$，

$$
\begin{aligned}
\mathcal F
&=-2UV(1-t)\left(1+\frac zL\right)+2z^2r^2t\\
&=2UV(1-t)\left(\frac1t-\frac zL\right).
\end{aligned}
\tag{308.17}
$$

这正是式（308.3）的第二式。由于 $r>z>0$，有 $0<z/L<1/2$；再结合 $t<1/3$，

$$
\frac1t-\frac zL>3-\frac12=\frac52,
\qquad 1-t>\frac23.
$$

因此两条曲率严格异号，并得到式（308.4）的两个严格下界。证毕。

由第300节的两条二阶展开，对于上述任一固定模型，当 $\delta>0$ 充分小时，

$$
F_a^{(2)}\bigl(\eta(1-\delta)\bigr)
<\kappa_a\delta
<\widehat G_a\bigl(\eta(1-\delta)\bigr).
\tag{308.18}
$$

这个邻域允许依赖于固定的半径，不据此宣称跨退化半径的统一邻域。

本节把第302节的奇异轴向例子扩展到了第305节的整个奇异支撑分支，并给出两条曲率的精确比例。结合第306节，严格正受限曲率覆盖全部轴向模型及全部奇异支撑模型；一般三个不同半径的正定支撑分支仍需另行判定。本节不把端点二阶结论延伸为整条有限预算曲线的显式解。

<a id="entry-966"></a>

## 追加锚（本行以下为增补区）

<a id="section-309"></a>

## 309. 正定支撑模型的根式参数化与唯一标量根

**定理 309.1（从列权重反求半径权重）。** 对开单纯形中任意点 $x=(x_1,x_2,x_3)$，记

$$
x_i>0,\qquad \sum_i x_i=1,
\qquad e_2=x_1x_2+x_1x_3+x_2x_3,
\qquad e_3=x_1x_2x_3,
$$

$$
B=2e_2^2-3e_3,
\qquad
c(x)=\frac{B+\sqrt{B^2-8e_3^2}}2.
\tag{309.1}
$$

这些根式均为实数，并且

$$
c(x)>\max_i x_i^2(1-2x_i).
\tag{309.2}
$$

令

$$
d_i=c(x)-x_i^2+2x_i^3,
\qquad
\beta^2=\left(\sum_i\frac{x_i^2}{d_i}\right)^{-1},
\qquad
w_i=\frac{\beta^2x_i^2}{d_i}.
\tag{309.3}
$$

则 $w_i>0$、$\sum_iw_i=1$、$\sum_iw_ix_i^2=\beta^2$，而且第307节的三个列范数表达同时满足

$$
x_i^2\left(1-2x_i+\frac{\beta^2}{w_i}\right)=c(x).
\tag{309.4}
$$

反过来，给定这个 $x$，取任何严格正且满足 $\sum_iw_i=1$ 的权重，并定义 $\beta^2=\sum_iw_ix_i^2$。若它们使第307节的三个 $c_i$ 相等，就必由式（309.3）给出。因此列权重 $x$ 唯一决定半径的归一化权重 $w$。

证明。先暂不使用根式定义，令

$$
\alpha_i=x_i^2(1-2x_i),\qquad a=\max_i\alpha_i,
\qquad \Phi(c)=\sum_i\frac{x_i^4}{c-\alpha_i}
\quad(c>a).
\tag{309.5}
$$

函数 $\Phi$ 连续且严格递减，在 $c\downarrow a$ 时趋于无穷，在 $c\to\infty$ 时趋于零。故恰有一个 $c_*>a$ 满足 $\Phi(c_*)=1$。

该根可以精确识别。若 $\{i,j,k\}=\{1,2,3\}$，由 $x_1+x_2+x_3=1$，

$$
\alpha_i-e_3=-x_i(x_i-x_j)(x_i-x_k).
\tag{309.6}
$$

取 $x_i$ 为三个坐标的中位数，右侧非负，故 $a\ge e_3>0$。另一方面，标准平方和恒等式给出

$$
e_2^2-3e_3
=\frac12\left[(x_1x_2-x_1x_3)^2
 +(x_1x_2-x_2x_3)^2+(x_1x_3-x_2x_3)^2\right]\ge0.
\tag{309.7}
$$

这里使用 $x_1+x_2+x_3=1$ 将三个乘积的交叉项之和写为 $e_3$。因此 $B\ge3e_3$，从而 $B^2-8e_3^2\ge e_3^2>0$。二次多项式

$$
c^2-Bc+2e_3^2
\tag{309.8}
$$

有两个严格正实根 $c_-<c_+$，其中 $c_+\ge2e_3$，而由两根之积得 $c_-\le e_3$。

现在给 $\Phi(c_*)=1$ 清除分母。对任意 $c$ 的直接多项式恒等式为

$$
\prod_i(c-\alpha_i)
-\sum_i x_i^4\prod_{j\ne i}(c-\alpha_j)
=(c-e_3)(c^2-Bc+2e_3^2).
\tag{309.9}
$$

等式可以逐次幂展开，并以 $e_2,e_3$ 与 $\sum_i x_i=1$ 整理核对。由于 $c_*>a\ge e_3$，它既不是根 $e_3$，也不是不超过 $e_3$ 的根 $c_-$；所以它必为 $c_+$，即式（309.1）的 $c(x)$。这同时证明式（309.2），无需猜测根的分支或容许非正分母。

由 $d_i>0$，式（309.3）显然给出严格正且和为一的权重。而 $\Phi(c(x))=1$ 使

$$
\sum_iw_ix_i^2
=\beta^2\sum_i\frac{x_i^4}{d_i}
=\beta^2.
$$

再由 $\beta^2/w_i=d_i/x_i^2$，得到式（309.4）。

反过来，设严格正归一化权重满足列范数等式，公共值记为 $c$，并按第307节定义 $\beta^2=\sum_iw_ix_i^2$。这些等式给出

$$
c-\alpha_i=\frac{\beta^2x_i^2}{w_i}>0,
\qquad
\sum_i\frac{x_i^4}{c-\alpha_i}
=\frac1{\beta^2}\sum_iw_ix_i^2=1.
$$

因此 $c>a$ 且 $\Phi(c)=1$，唯一性迫使 $c=c(x)$。归一化 $\sum_iw_i=1$ 再唯一确定 $\beta^2$ 和全部 $w_i$，恰为式（309.3）。证毕。

**定理 309.2（自动锥可行的完整正定分支参数化）。** 对定理309.1生成的每个 $x,w$，记 $u_i=x_i(1-x_i)$、$f=\sum_iw_iu_i$。则对任意不同的 $i,j$，

$$
f>x_ix_j.
\tag{309.10}
$$

选择任意尺度

$$
A\ge\frac1{\min_iw_i},\qquad
b_i=\sqrt{Aw_i},\qquad a_i=\frac1{\sqrt{Aw_i}}.
\tag{309.11}
$$

这些半径均在 $(0,1]$ 内。第307节由 $b,x$ 构造的 $G_x$ 每个条目都严格为正，而且 $\mathcal C(S_x)\succeq0$ 的核恰为 $\mathbb Rv$。因此每个开单纯形点都自动通过该节的标量锥条件，按式（307.4）给出对应半径模型的唯一正定支撑端点最优解。

反过来，每个正定支撑的正半径模型都由这一构造得到。在保持坐标标号的归一化权重空间上，$x\mapsto w$ 为单射，其像恰为正定支撑模型的权重集合。

证明。先证明式（309.10）。固定一对坐标，并将其写为 $y,z$，剩余坐标写为 $x$；本段的 $x,y,z$ 是三个正标量，和为一。把公共值记为 $c=c(x_1,x_2,x_3)$，并令

$$
R_0=\sum_i\frac{x_i^2}{d_i}>0.
$$

由式（309.3），$w_i=x_i^2/(d_iR_0)$，且 $\sum_i x_i^4/d_i=1$。因此

$$
\frac{R_0}{x}(f-yz)
=\frac{x[x(1-x)-yz]}{d_x}
 +\frac{y^3}{d_y}+\frac{z^3}{d_z}.
\tag{309.12}
$$

这里 $d_x,d_y,d_z$ 分别表示对应坐标的 $d_i$。若 $x(1-x)\ge yz$，右侧显然严格为正。若 $yz>x(1-x)$，利用已证 $c\ge2e_3=2xyz$，

$$
\begin{aligned}
d_x-x^4-xyz
&=c-x^2+2x^3-x^4-xyz\\
&\ge x\bigl[yz-x(1-x)^2\bigr]>0.
\end{aligned}
\tag{309.13}
$$

最后一步使用 $yz>x(1-x)>x(1-x)^2$。又因 $0<y,z<1$，

$$
\frac{y^3}{d_y}+\frac{z^3}{d_z}
>\frac{y^4}{d_y}+\frac{z^4}{d_z}
=1-\frac{x^4}{d_x}.
$$

式（309.12）的第一项严格大于 $-xyz/d_x$，从而整个右侧严格大于

$$
1-\frac{x^4+xyz}{d_x}>0.
$$

这证明式（309.10）对每一对坐标均成立。

现在恢复第307节的矩阵记号。因为定理309.1已经给出 $\beta^2=\sum_iw_ix_i^2$，该节的无条件候选恒等式可直接使用：$G_x\succ0$、$\mathcal C(S_x)v=0$，且 $f=m-\beta^2>0$。展开 $v$ 的归一化因子可得，当 $\{i,j,k\}=\{1,2,3\}$ 时，

$$
(G_x)_{ij}
=b_ib_j\frac{f+\beta x_k-x_ix_j}{\beta+m}>0.
\tag{309.14}
$$

严格正性由式（309.10）与全部参数的正性得到。对角元由 $G_x\succ0$ 严格为正，故 $G_x$ 逐条目严格为正；$Q_x=G_x\operatorname{diag}(x)$ 与 $S_x=\operatorname{sym}Q_x$ 也逐条目严格为正。

令 $V_0=\operatorname{diag}(v)$。共同核恒等式给出第307节的二次型

$$
h^{\mathsf T}V_0\mathcal C(S_x)V_0h
=2\sum_{i<j}(S_x)_{ij}v_iv_j(h_i-h_j)^2.
\tag{309.15}
$$

每个系数严格为正，因此它非负，且取零恰好要求 $h_1=h_2=h_3$。$V_0$ 可逆，故 $\mathcal C(S_x)\succeq0$，其核恰为 $\mathbb Rv$。这直接证明锥可行性及秩二，而非从数值样本推断标量判据。

定理309.1已使全部列范数等式成立，所以第307节的可准入条件全部满足。定理307.2遂给出正定支撑的唯一最优解及其重建公式。式（309.11）的尺度限制等价于全部 $b_i\ge1$，因此确为所述物理半径。

反过来，对任一实际正定支撑模型，定理307.2给出唯一列权重 $x$，并使三个列范数表达相等。定理309.1的逆向结论恢复原本的归一化半径权重 $w_i=b_i^2/\|b\|_2^2$；其尺度 $A=\|b\|_2^2$ 满足式（309.11）。因此参数化无遗漏。

若两个单纯形点生成相同 $w$，取同一个满足式（309.11）的 $A$，它们就为同一模型给出两个可准入点。定理307.2的唯一性使两点相同，证明单射。证毕。

**定理 309.3（所有端点半群的固定角点与主特征值）。** 对任意正半径六态模型，在正角点规范下，第298节的唯一端点矩阵 $M_*$ 的特征值 $1$ 都是单重的，其余两个特征值均在 $(0,1)$ 内。对每个 $\tau>0$，正角点是该矩阵生成的半群残差中的唯一最大角点，整体正负号视为同一类。因此

$$
r_*(e^{-\tau M_*})
=\frac1{\|e^{\tau M_*^{\mathsf T}}b\|_2}
\qquad(\tau\ge0).
\tag{309.16}
$$

证明。奇异支撑分支已由定理305.3、305.4证明。以下只需处理正定支撑分支。由定理309.2，该分支每个实际最优 $G$ 逐条目严格为正，而 $M_*$ 是 $G\operatorname{diag}(x)$ 的正数倍，故也逐条目严格为正。

因此 $e^{\tau M_*^{\mathsf T}}$ 在每个 $\tau>0$ 逐条目严格为正。对任意混合符号角点 $b_\sigma$，逐行的严格三角不等式给出

$$
\left|e^{\tau M_*^{\mathsf T}}b_\sigma\right|
<e^{\tau M_*^{\mathsf T}}b
$$

逐坐标成立，进而其欧氏范数严格更小。第281节的角点公式给出式（309.16）及唯一性。在 $\tau=0$ 时所有角点范数相同，等式仍成立，但此时不声称角点唯一。

再由 $M_*b=b$，矩阵 $\operatorname{diag}(b)^{-1}M_*\operatorname{diag}(b)$ 逐条目严格为正且每行和为一。标准正矩阵的 Perron–Frobenius 结论使其特征值 $1$ 单重，其余特征值的模严格小于一；第303节已经证明所有特征值都为严格正实数，故另外两个都落在 $(0,1)$。这里使用的是正矩阵的既有谱性质，新增结论是它对整个任务最优端点族的适用性。证毕。

本节的根式从列权重直接生成半径权重及其最优端点矩阵，不再需要独立检查第307节的锥不等式。对于事先指定的三个半径，反求 $x$ 仍可能需要求解方程；本节没有将这个逆问题宣称为已得到一般根式解。固定角点结论描述同一个端点生成元的可行半群，不将其宣称为整条有限预算最优曲线，也未在这里确定一般三个不同半径的正定支撑模型的受限二阶曲率符号。

<a id="entry-968"></a>

## 追加锚（本行以下为增补区）

<a id="section-310"></a>

## 310. 任意正半径模型的严格正受限曲率

**定理 310.1（两类最优恢复曲线的通用端点符号）。** 对任意固定正半径六态模型，第300节的受限端点二阶系数满足

$$
\Gamma_a+\Theta_a>0.
\tag{310.1}
$$

若三个半径不全相等，则对于充分小的 $\delta>0$，

$$
F_a^{(2)}\bigl(\eta(1-\delta)\bigr)
<\kappa_a\delta
<\widehat G_a\bigl(\eta(1-\delta)\bigr).
\tag{310.2}
$$

三个半径全相等时，受限曲线仍严格位于该切线上方，而无限制二阶系数为零。邻域可以依赖于固定的半径，不宣称跨退化参数的统一余项或统一邻域。

在正定支撑分支，取第307、309节的唯一单纯形点 $x$ 及其权重 $w$，并记

$$
p=x_1x_2+x_1x_3+x_2x_3,
\qquad q=x_1x_2x_3,
\qquad h=c/q,
\qquad m=\sum_iw_ix_i,
\qquad \beta^2=\sum_iw_ix_i^2.
\tag{310.3}
$$

其中 $\beta>0$、$c=c(x)$。该分支的精确系数为

$$
\Gamma_a+\Theta_a
=\kappa_a\,
\frac{\mathcal L(h,p,\beta)}
{2(h+2)(h^2-1)(\beta+m)},
\tag{310.4}
$$

$$
\mathcal L(h,p,\beta)
=2\beta(h+1)\bigl[h-(2h+1)p\bigr]
 +h\bigl[h+1-2(h+3)p+6p^2\bigr].
\tag{310.5}
$$

证明。奇异支撑分支已由第308节给出精确正系数。以下证明正定支撑分支的公式与严格正性。

先把共同列支撑化为一个 Gram 恒等式。令

$$
n=b/\sqrt A,\qquad X=\operatorname{diag}(x),
\qquad G_0=G/A=nn^{\mathsf T}+\beta R_v,
\qquad R_v=I-2vv^{\mathsf T},
\qquad Q_0=G_0X,
\qquad f=m-\beta^2.
\tag{310.6}
$$

这里 $n_i^2=w_i$、$\|n\|_2=1$，且 $M_*=Q_0/f$。第307节的反射恒等式给出 $R_vn=-Xn/\beta$，所以

$$
G_0^2
=nn^{\mathsf T}-nn^{\mathsf T}X-Xnn^{\mathsf T}+\beta^2I.
\tag{310.7}
$$

当 $i\ne j$ 时，其 $ij$ 元为 $n_in_j(1-x_i-x_j)$。因此 $Q_0^{\mathsf T}Q_0=XG_0^2X$ 的非对角元为 $qn_in_j$；三个对角元则由共同列范数等式为 $cw_i$。从而

$$
Q_0^{\mathsf T}Q_0
=(c-q)\operatorname{diag}(w)+qnn^{\mathsf T},
\qquad \|Q_0\|_F^2=c.
\tag{310.8}
$$

另一方面，第307节的两个固定方向恒等式给出

$$
Q_0n=fn,\qquad
Q_0^{\mathsf T}n=X(I-X)n.
$$

将式（310.8）作用到 $n$，并逐坐标消去严格正的 $n_i$，得到

$$
f\,x_i(1-x_i)=(c-q)w_i+q.
\tag{310.9}
$$

三个等式相加，使用 $\sum_i x_i(1-x_i)=2p$，有

$$
f=\frac{c+2q}{2p}.
\tag{310.10}
$$

第309节给出 $c\ge2q$ 及 $c^2-(2p^2-3q)c+2q^2=0$。故 $h\ge2$，而

$$
q=\frac{2p^2h}{(h+1)(h+2)},
\qquad
f=\frac{ph}{h+1}.
\tag{310.11}
$$

由式（310.9），$w_i=[fx_i(1-x_i)-q]/(c-q)$。将其乘以 $x_i$ 后求和，并使用
$\sum_i x_i^2-\sum_i x_i^3=p-3q$，得到

$$
\begin{aligned}
m&=\frac{f(p-3q)-q}{c-q}
=\frac{h(h+1-6p)}{2(h^2-1)},\\
\beta^2=m-f
&=\frac{h\left[h+1-2(h+2)p\right]}{2(h^2-1)}.
\end{aligned}
\tag{310.12}
$$

这些是同一实际最优解的等式，未把不同模型各自可达的参数拼接起来。

下面计算受限系数。记

$$
\mathcal V=\sum_iw_i\left(x_i(1-x_i)-f\right)^2,
\qquad s_1=\operatorname{Tr}Q_0,
\qquad s_2=\operatorname{Tr}(Q_0^2).
\tag{310.13}
$$

由式（310.8），

$$
\operatorname{Tr}\bigl((\operatorname{sym}Q_0)^2\bigr)
=\frac{c+s_2}{2}.
$$

而 $S_*=(\operatorname{sym}Q_0)/f$ 的最大特征值等于另外两个之和。因此两个较小特征值的乘积为

$$
d_1d_2=\frac{s_1^2-c-s_2}{4f^2}.
\tag{310.14}
$$

结合第301、307节的曲率表达，

$$
\Gamma_a+\Theta_a
=\frac{\kappa_a}{2f^2}\mathcal K,
\qquad
\mathcal K=\frac\beta2(s_1^2-c-s_2)-\mathcal V.
\tag{310.15}
$$

给出这些迹与方差的具体展开，便可核对其因式。定义 $m_j=\sum_iw_ix_i^j$，所以 $m_1=m$、$m_2=\beta^2$。每个 $x_i$ 满足 $x_i^3-x_i^2+px_i-q=0$，故

$$
m_3=\beta^2-pm+q,
\qquad m_4=m_3-p\beta^2+qm,
\qquad
\mathcal V=(p+q)m-p\beta^2-q-f^2.
\tag{310.16}
$$

由 $v=(X+\beta I)n/\sqrt{2\beta(\beta+m)}$，记

$$
V_1=v^{\mathsf T}Xv
=\frac{m_3+2\beta^3+\beta^2m}{2\beta(\beta+m)},
\qquad
V_2=v^{\mathsf T}X^2v
=\frac{m_4+2\beta m_3+\beta^4}{2\beta(\beta+m)}.
\tag{310.17}
$$

直接展开 $Q_0=(nn^{\mathsf T}+\beta I-2\beta vv^{\mathsf T})X$，得到

$$
\begin{aligned}
s_1&=m+\beta-2\beta V_1,\\
s_2&=m^2+\beta^2(1-2p)+4\beta^2V_1^2
 -2\beta^2m-4\beta^2V_2.
\end{aligned}
\tag{310.18}
$$

第二式的交叉项使用 $v^{\mathsf T}Xn=\beta(v\cdot n)$ 与
$(v\cdot n)^2=(\beta+m)/(2\beta)$；因此其中来自 $nn^{\mathsf T}X$ 与 $\beta X$ 的 $2\beta^3$，恰与另一交叉项中的 $-2\beta^3$ 抵消。

将式（310.11）、（310.12）、（310.16）至（310.18）代入式（310.15），保留 $\beta>0$ 而用式（310.12）替换 $\beta^2$，整理为

$$
\mathcal K
=\frac{h^2p^2\,\mathcal L(h,p,\beta)}
{(h+1)^2(h+2)(h^2-1)(\beta+m)}.
\tag{310.19}
$$

再以 $f^2=h^2p^2/(h+1)^2$ 约去共同因子，正好得到式（310.4）。全部分母严格为正；这些恒等式不要求三个坐标互不相等。

最后确定分子的符号。开单纯形给出 $0<p\le1/3$，写 $d=1/3-p\ge0$。则

$$
\begin{aligned}
h-(2h+1)p&=\frac{h-1}{3}+(2h+1)d,\\
h+1-2(h+3)p+6p^2
&=\frac{h-1}{3}+2(h+1)d+6d^2.
\end{aligned}
\tag{310.20}
$$

因为 $h\ge2$、$\beta>0$，式（310.5）的两项均严格为正，故 $\mathcal L>0$。由此证明整个正定支撑分支的严格正受限曲率。结合第308节，便覆盖全部正半径模型，得到式（310.1）。

三个半径不全相等时，第301节给出 $\Gamma_a<0$，再由第300节的两条二阶展开得到式（310.2）。全等半径时，$x_i=1/3$、$p=1/3$、$h=2$、$\beta=m=1/3$，式（310.4）给出 $\Gamma_a+\Theta_a=\kappa_a/12>0$，同时 $\Gamma_a=0$，与已有等半径系数一致。证毕。

本节确定的是任意固定正半径模型在共同端点切线附近的二阶方向。一般有限预算的精确最优曲线、端点以外的整体凸性，以及由端点最优生成元形成的半群是否在其他预算处仍最优，均未由这一符号结论确定。

<a id="entry-970"></a>

## 追加锚（本行以下为增补区）

<a id="section-311"></a>

## 311. 端点最优固定生成元在有限预算下的严格次优例子

**定理 311.1（固定最优生成元的二阶超额）。** 取正半径模型

$$
a_1=a_2=a,\qquad a_3=a/\sqrt2,\qquad 0<a\le1,
$$

并令 $M_*$ 为正角点规范下唯一的端点最优矩阵。记

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\beta=\sqrt{\frac{\varphi+2}{2}},\qquad
L=1+3\varphi.
\tag{311.1}
$$

对每个 $0<\delta<1$，令 $\tau(\delta)>0$ 为使固定半群 $T_\tau=e^{-\tau M_*}$ 恰好达到残差预算 $R_\delta=\eta(1-\delta)$ 的唯一参数。则该半群的恢复误差满足

$$
\begin{aligned}
e(T_{\tau(\delta)})-\widehat G_a(R_\delta)
&=C_a\delta^2+o(\delta^2),\\
C_a&=\frac{\kappa_a}{2L^2}
\left[3+\varphi-2\beta(\varphi-1)\right]>0.
\end{aligned}
\tag{311.2}
$$

因此，对每个固定 $a$，当 $\delta>0$ 充分小时，端点最优固定生成元产生的该半群严格劣于同一残差预算下的实际受限最优恢复。这个结论只针对该固定生成元，不排除随预算改变生成元或采用其他无限小可分通道。

证明。在第306节的轴向族中取 $k=\sqrt2$。其根方程为 $2t^2-2t-2=0$，故参数 $t=\varphi$，而该节的 $\beta$ 正是式（311.1）的量。按正交基

$$
u=(1,1,0)/\sqrt2,\qquad w=(1,-1,0)/\sqrt2,\qquad z=e_3,
$$

端点矩阵为

$$
[M_*]_{(u,w,z)}
=\frac1L
\begin{pmatrix}
1+2\varphi&0&\varphi\\
0&2\beta&0\\
1&0&3\varphi
\end{pmatrix}.
\tag{311.3}
$$

在该标架中，$b=(\sqrt2,0,\sqrt2)/a$、$A=4/a^2$，且 $M_*b=b$。原坐标列仍由 $e_1=(u+w)/\sqrt2$、$e_2=(u-w)/\sqrt2$、$e_3=z$ 给出；不把加权列约束随标架改变。直接计算得到

$$
\|M_*e_1\|_2^2=\|M_*e_2\|_2^2
=\frac{5\varphi^2}{L^2},
\qquad
\|M_*e_3\|_2^2=\frac{10\varphi^2}{L^2}.
\tag{311.4}
$$

因此三列的一阶误差都达到相同值，且

$$
\kappa_a=\frac{a\sqrt5\,\varphi}{2L}.
\tag{311.5}
$$

先将半群参数与实际残差预算对齐。第306节的固定角点结论给出

$$
r_*(T_\tau)=\frac1{\|e^{\tau M_*^{\mathsf T}}b\|_2}.
\tag{311.6}
$$

第304节的严格预算顺序保证 $\tau(\delta)$ 的存在唯一性。记 $U_\Omega=\|\Omega_*b\|_2^2$。由式（311.3），

$$
U_\Omega=\frac{(\varphi-1)^2}{a^2L^2}.
\tag{311.7}
$$

又由 $M_*^{\mathsf T}b=b+2\Omega_*b$、$b\cdot\Omega_*b=0$ 及
$b^{\mathsf T}(M_*^{\mathsf T})^2b=A$，固定矩阵的指数展开给出

$$
\frac{\|e^{\tau M_*^{\mathsf T}}b\|_2^2}{A}
=1+2\tau+\left(2+\frac{4U_\Omega}{A}\right)\tau^2+O(\tau^3).
\tag{311.8}
$$

取平方根再取倒数，式（311.6）变为

$$
1-\frac{r_*(T_\tau)}\eta
=\tau-\left(\frac12-\frac{2U_\Omega}{A}\right)\tau^2+O(\tau^3).
$$

其在零点的导数为一，局部反演得到

$$
\tau(\delta)
=\delta+\left(\frac12-\frac{2U_\Omega}{A}\right)\delta^2+O(\delta^3).
\tag{311.9}
$$

下面展开这个同一通道的恢复误差。写 $m_i=M_*e_i$，并定义

$$
\rho_i=\frac{\langle m_i,M_*m_i\rangle}{\|m_i\|_2^2}.
\tag{311.10}
$$

因为各 $m_i$ 非零，

$$
\|(I-e^{-\tau M_*})e_i\|_2
=\tau\|m_i\|_2-\frac{\tau^2}{2}
\frac{\langle m_i,M_*m_i\rangle}{\|m_i\|_2}
+O(\tau^3).
\tag{311.11}
$$

式（311.4）使三列的加权首项都为 $\kappa_a\tau$，故取有限个列误差的最大值后有

$$
e(T_\tau)
=\kappa_a\tau-\frac{\kappa_a}{2}
\min_i\rho_i\,\tau^2+O(\tau^3).
\tag{311.12}
$$

这一步不要求最大列在所有参数处固定；有限个余项可取共同界。

代入式（311.3）并使用 $\varphi^2=\varphi+1$，得到

$$
\rho_1=\rho_2
=\frac{24+42\varphi+8\beta^3}{10\varphi^2L},
\qquad
\rho_3=\frac{4+32\varphi}{10L}.
\tag{311.13}
$$

例如对第一列，分子来自 $u,z$ 块的
$(1+2\varphi)^3+(1+2\varphi)\varphi+(1+2\varphi)+3\varphi$，以及 $w$ 块的 $(2\beta)^3$；前四项之和为 $24+42\varphi$。另外

$$
\rho_3-\rho_1
=\frac{12+26\varphi-8\beta^3}{10\varphi^2L}>0.
\tag{311.14}
$$

严格性可由 $\varphi>3/2$、$\beta<3/2$ 直接看出。因此式（311.12）的最小值为 $\rho_1$。再代入式（311.9），并使用第301节的
$\Gamma_a=-2\kappa_aU_\Omega/A$，得到该固定半群在精确预算下的二阶系数

$$
S_a=\Gamma_a+\frac{\kappa_a}{2}(1-\rho_1).
\tag{311.15}
$$

需要将它与实际受限最优值的系数比较。第306节给出该模型的

$$
\frac\lambda A=\frac\beta{\varphi+2}=\frac1{2\beta},
\qquad
d_1d_2=\frac{\beta(1+5\varphi-2\beta)}{L^2}.
\tag{311.16}
$$

这里 $d_1,d_2$ 是 $\operatorname{sym}M_*$ 的两个较小特征值；乘积不依赖两者的顺序。由第301节及 $\kappa_a=A/(2D_a)$，

$$
\Theta_a=\kappa_a\frac\lambda A d_1d_2
=\frac{\kappa_a(1+5\varphi-2\beta)}{2L^2}.
\tag{311.17}
$$

将式（311.13）代入式（311.15）并减去 $\Gamma_a+\Theta_a$，用
$\varphi^2=\varphi+1$ 与 $\beta^2=(\varphi+2)/2$ 整理，恰得

$$
S_a-(\Gamma_a+\Theta_a)
=\frac{\kappa_a}{2L^2}
\left[3+\varphi-2\beta(\varphi-1)\right].
\tag{311.18}
$$

括号内严格为正：被比较的 $3+\varphi$ 和 $2\beta(\varphi-1)$ 都为正，而

$$
(3+\varphi)^2-4\beta^2(\varphi-1)^2
=4+9\varphi>0.
\tag{311.19}
$$

第300节为实际受限最优值提供
$\widehat G_a(R_\delta)=\kappa_a\delta+(\Gamma_a+\Theta_a)\delta^2+o(\delta^2)$。
与固定半群的展开相减，即为式（311.2）；严格正系数保证在充分小的正预算差内误差严格更大。

最后核对操作意义。$T_\tau$ 是第296、306节给出的同一个幺元 CPTP 半群。按第281节选择达到式（311.6）的编码方向，配合相应酉旋转及逆酉解码，可在同一对完整量子比特通道中同时实现所用残差与复合恢复误差。因此这里比较的是同一个实际方案与同预算最优值，不是分别取得的两个不相容读数。证毕。

端点最优性确定了最有效的一阶方向，但不使固定该方向的整条半群自动保持最优。式（311.2）给出了这一点的明确模型和严格二阶差距；它没有确定偏离端点以后真正最优的整条通道路径。

<a id="entry-972"></a>

## 追加锚（本行以下为增补区）

<a id="section-312"></a>

## 312. 固定端点半群的精确二阶损失与奇异分支等号分类

**定理 312.1（支撑加权的二阶超额）。** 固定正半径六态模型，沿用第298至301节的唯一正角点端点解 $M_*=S_*-\Omega_*$、$G$、$Z_*=\lambda vv^{\mathsf T}$、$D_a$、$\kappa_a$，并记 $A=\|b\|_2^2$、$\alpha_i=1/a_i$。定义活跃列集合、支撑权重及列方向衰减率为

$$
I=\{i:a_i\|M_*e_i\|_2=2\kappa_a\},\qquad
\pi_i=\frac{\alpha_i\|Ge_i\|_2}{D_a},\qquad
\rho_i=\frac{\langle M_*e_i,M_*^2e_i\rangle}{\|M_*e_i\|_2^2}.
\tag{312.1}
$$

所有列都非零，$\pi_i\ge0$、$\sum_i\pi_i=1$，且 $\pi_i>0$ 蕴含 $i\in I$。令 $T_t=e^{-tM_*}$，对 $0<\delta<1$，令 $t(\delta)$ 是使 $r_*(T_{t(\delta)})=\eta(1-\delta)$ 的唯一参数。那么对每个固定模型，在 $\delta\downarrow0$ 时，

$$
e(T_{t(\delta)})-\widehat G_a\bigl(\eta(1-\delta)\bigr)
=\mathcal E_a\delta^2+o(\delta^2),
\tag{312.2}
$$

$$
\mathcal E_a
=\frac{\kappa_a}{2}
\left(\sum_i\pi_i\rho_i-\min_{i\in I}\rho_i\right)\ge0.
\tag{312.3}
$$

等号 $\mathcal E_a=0$ 恰当且仅当每个正支撑权重对应的 $\rho_i$ 都等于活跃列中的最小值。特别地，当 $G\succ0$ 时，等号恰好要求 $\rho_1=\rho_2=\rho_3$。

证明。第298节给出 $S_*\succ0$，因此 $M_*$ 可逆，式（312.1）的所有分母非零。最优对偶目标为 $D_a=\sum_i\alpha_i\|Ge_i\|_2>0$，故权重归一化；列支撑取等条件给出其支集包含于 $I$。

先证明一个由同一对最优原、对偶矩阵决定的恒等式：

$$
\sum_i\pi_i\rho_i
=1-\frac{2\lambda}{A}d_1d_2,
\tag{312.4}
$$

其中 $d_1,d_2$ 是 $S_*$ 的两个较小特征值。由 $\mathcal C(S)=(\operatorname{Tr}S)I-2S$ 及 $G=bb^{\mathsf T}+\mathcal C(Z_*)$，对任意实矩阵 $N$ 有

$$
b^{\mathsf T}Nb
=\langle G,N\rangle_F-\operatorname{Tr}\bigl(Z_*\mathcal C(\operatorname{sym}N)\bigr).
\tag{312.5}
$$

取 $N=M_*^2$。由 $M_*b=b$，左侧等于 $A$。对每个非零支撑列，最优列方向和尺度关系给出

$$
Ge_i=\frac{D_a\|Ge_i\|_2}{A\alpha_i}M_*e_i,
\qquad \|M_*e_i\|_2=\frac{A\alpha_i}{D_a}.
$$

因此 $\langle Ge_i,M_*^2e_i\rangle
=A\pi_i\rho_i$；零支撑列两侧都为零。遂有 $\langle G,M_*^2\rangle_F=A\sum_i\pi_i\rho_i$。

另一方面，第301节给出 $d_3=d_1+d_2$、$S_*v=d_3v$ 及 $v\cdot\omega=0$，其中 $\Omega_*x=\omega\times x$。所以

$$
\begin{aligned}
\operatorname{Tr}(M_*^2)&=d_1^2+d_2^2+d_3^2-2\|\omega\|_2^2,\\
v^{\mathsf T}M_*^2v&=d_3^2-\|\omega\|_2^2,\\
\operatorname{Tr}\bigl(Z_*\mathcal C(\operatorname{sym}M_*^2)\bigr)
&=-2\lambda d_1d_2.
\end{aligned}
\tag{312.6}
$$

把这些等式代入式（312.5），便得式（312.4）。这里没有将 $M_*$ 当作对称矩阵。

接着在同一实际预算下展开固定半群。第305、309节覆盖全部正半径，并保证
$r_*(T_t)=\|e^{tM_*^{\mathsf T}}b\|_2^{-1}$；第304节保证预算参数唯一。令 $U=\|\Omega_*b\|_2^2$。由 $M_*^{\mathsf T}b=b+2\Omega_*b$ 及 $M_*b=b$，与第311节相同的固定矩阵展开给出

$$
t(\delta)=\delta+\left(\frac12-\frac{2U}{A}\right)\delta^2+O(\delta^3).
\tag{312.7}
$$

对每一列展开矩阵指数和欧氏范数，有

$$
\frac{a_i}{2}\|(I-T_t)e_i\|_2
=\frac{a_i\|M_*e_i\|_2}{2}
\left(t-\frac{\rho_i}{2}t^2\right)+O(t^3).
$$

不在 $I$ 中的列与最大的首项系数有严格正间隙；列数有限，所以它们在充分小的正 $t$ 处不影响最大误差。对 $I$ 中的列取最大值得

$$
e(T_t)=\kappa_at-\frac{\kappa_a}{2}
\min_{i\in I}\rho_i\,t^2+O(t^3).
\tag{312.8}
$$

代入式（312.7），并使用第301节的
$\Gamma_a=-2\kappa_aU/A$ 与
$\Theta_a=\kappa_a(\lambda/A)d_1d_2$，再减去第300节实际受限最优值的二阶展开，得到

$$
\mathcal E_a
=\frac{\kappa_a}{2}\left(1-\min_{i\in I}\rho_i\right)-\Theta_a.
$$

以式（312.4）消去 $\Theta_a$，即为式（312.3）。非负性及等号条件直接来自支撑于 $I$ 的概率权重。$G\succ0$ 时三个权重都严格为正，且三列全部活跃，故等号等价于三个衰减率相等。

按第281节，同一个 $T_t$ 配合达到残差的酉输出坐标选择及逆酉解码，同时实现上述预算与误差；其复合恢复属于所比较的无限小可分类。式（312.2）比较的是同一个方案的两个读数。证毕。

**定理 312.2（整个奇异支撑分支的二阶等号分类）。** 当最优支撑 $G$ 奇异时，令唯一零列对应的坐标最后排列，并沿用第305节的 $p_1,p_2,z,r,L=r+z,q,K,u$。则

$$
\mathcal E_a=0\quad\Longleftrightarrow\quad p_1=p_2.
\tag{312.9}
$$

因此，零支撑列以外的两个半径不相等时，固定端点半群在每个充分接近端点的非零预算差处都严格次优。这一结论包括最后一列范数约束刚好取等的阈值。

证明。第305节给出

$$
M_*=\frac1q\begin{pmatrix}K&u\\0&q\end{pmatrix},
\qquad K>0,\quad u>0,
\qquad \pi_1,\pi_2>0,\quad \pi_3=0,
$$

其中 $K>0$ 表示每个条目严格为正。前两列始终活跃。若第三列也活跃，其衰减率为

$$
\rho_3=1+\frac{u^{\mathsf T}Ku}{q(q^2+\|u\|_2^2)}>1.
\tag{312.10}
$$

而式（312.4）使 $\pi_1\rho_1+\pi_2\rho_2<1$，因为 $\lambda,d_1,d_2$ 都严格为正。因此活跃列中的最小衰减率总是 $\min\{\rho_1,\rho_2\}$，不受第三列是否取等影响。由定理312.1，$\mathcal E_a=0$ 恰好等价于 $\rho_1=\rho_2$。

剩下只需确定这两个率何时相等。记

$$
U=p_1^2,\qquad V=p_2^2,\qquad
s_1=\frac{p_1}{\sqrt{z^2+U}},\qquad
s_2=\frac{p_2}{\sqrt{z^2+V}},\qquad \tau=s_1s_2.
$$

由第305节的 $K=G_0H$、$G_0^2=r^2(z^2I+pp^{\mathsf T})$，得到

$$
K^{\mathsf T}K=
\begin{pmatrix}U&\sqrt{UV}\,\tau\\\sqrt{UV}\,\tau&V\end{pmatrix}.
$$

将它用于 $\rho_j=(K^{\mathsf T}K^2)_{jj}/(qp_j^2)$，可得

$$
\rho_1=\frac{s_1}{q}\left[z+\frac{U+V\tau}{L}\right],\qquad
\rho_2=\frac{s_2}{q}\left[z+\frac{V+U\tau}{L}\right].
\tag{312.11}
$$

两式相减，并使用 $1-s_1^2=z^2/(z^2+U)$、$1-s_2^2=z^2/(z^2+V)$，得到

$$
q(\rho_1-\rho_2)
=z(s_1-s_2)
+\frac{z^2\left[U\sqrt{U(z^2+U)}-V\sqrt{V(z^2+V)}\right]}
{L(z^2+U)(z^2+V)}.
\tag{312.12}
$$

函数 $x\mapsto\sqrt{x/(z^2+x)}$ 与
$x\mapsto x\sqrt{x(z^2+x)}$ 在 $x>0$ 上都严格递增。故右侧两项在 $U\ne V$ 时均与 $U-V$ 同号，在 $U=V$ 时均为零。因此 $\rho_1=\rho_2$ 恰好等价于 $p_1=p_2$，证明式（312.9）。严格正二阶超额随后结合式（312.2）给出充分小正预算差处的严格次优性。证毕。

这里的等号只消除了二阶超额。它不保证误差曲线在有限预算区间内完全重合；当 $\mathcal E_a=0$ 时，更高阶差距和有限预算的真正最优通道仍需另行确定。正定支撑分支在本节只得到式（312.3）的精确判据，没有将三个 $\rho_i$ 相等进一步分类为半径条件。

<a id="entry-974"></a>

## 追加锚（本行以下为增补区）

<a id="section-313"></a>

## 313. 正定支撑分支的严格列率顺序与二阶最优性完整分类

**定理 313.1（列率严格保持单纯形坐标的顺序）。** 在第307、309节的正定对偶支撑分支，令 $x$ 为唯一的开单纯形参数，$\rho_i$ 为式（312.1）的列方向衰减率。对任意不同指标 $i,j$，有

$$
\operatorname{sign}(\rho_i-\rho_j)
=\operatorname{sign}(x_i-x_j).
\tag{313.1}
$$

因此固定端点半群的二阶超额系数在该分支满足

$$
\mathcal E_a=0
\quad\Longleftrightarrow\quad a_1=a_2=a_3.
\tag{313.2}
$$

证明。沿用第310节的归一化与参数：$n_i^2=w_i$、$X=\operatorname{diag}(x)$、$G_0=G/A$、$Q_0=G_0X$、$M_*=Q_0/f$，以及

$$
p=\sum_{i<j}x_ix_j,\quad q=x_1x_2x_3,\quad
h=c/q\ge2,\quad m=\sum_iw_ix_i,\quad
\beta^2=\sum_iw_ix_i^2,\quad f=m-\beta^2>0.
$$

记 $u_i=x_i(1-x_i)$。第310节的 Gram 恒等式与固定方向关系为

$$
Q_0^{\mathsf T}Q_0=(c-q)\operatorname{diag}(w)+qnn^{\mathsf T},
\qquad Q_0^{\mathsf T}n=\operatorname{diag}(u)n,
\qquad fu_i=(c-q)w_i+q.
\tag{313.3}
$$

所以 $\|M_*e_i\|_2^2=cw_i/f^2$，并且

$$
\rho_i
=\frac{(c-q)(Q_0)_{ii}+qu_i}{cf}.
\tag{313.4}
$$

确实，式（313.3）右乘 $Q_0$ 后的第 $ii$ 元为
$w_i[(c-q)(Q_0)_{ii}+qu_i]$；按 $M_*=Q_0/f$ 的三个尺度因子，再除以列范数平方，就得到式（313.4）。

由 $v=(X+\beta I)n/\sqrt{2\beta(\beta+m)}$ 及 $G_0=nn^{\mathsf T}+\beta I-2\beta vv^{\mathsf T}$，

$$
(Q_0)_{ii}
=x_i\left[\beta+w_i\left(1-\frac{(x_i+\beta)^2}{\beta+m}\right)\right].
$$

消去 $w_i=(fu_i-q)/(c-q)$，于是

$$
\rho_i=\frac{N(x_i)}{cf(\beta+m)},
\tag{313.5}
$$

其中是同一个多项式

$$
N(z)=(c-q)\beta(\beta+m)z
+fz^2(1-z)\bigl[\beta+m-(z+\beta)^2\bigr]
+qz\bigl[(z+\beta)^2-z(\beta+m)\bigr].
\tag{313.6}
$$

下面只需比较这个多项式在三个单纯形坐标处的值。每个 $x_i$ 满足 $x_i^3-x_i^2+px_i-q=0$。将式（313.6）除以这个三次式，并用 $\beta^2=m-f$ 约去平方，余式为 $A_2z^2+A_1z+A_0$，其中

$$
\begin{aligned}
A_2={}&-2\beta fp+\beta q-fp+fq-mq+q,\\
A_1={}&\beta cm+\beta fp+2\beta fq-\beta mq
 -cf+cm+f^2p+fp^2-pq,\\
A_0={}&-q(\beta f+f^2+fp-q).
\end{aligned}
\tag{313.7}
$$

这些余式系数保留了同一模型的 $c,q,f,m,\beta$。再代入第310节的

$$
c=hq,\qquad q=\frac{2p^2h}{(h+1)(h+2)},\qquad
f=\frac{ph}{h+1},\qquad
m=\frac{h(h+1-6p)}{2(h^2-1)},
$$

记

$$
K_0=\frac{hp^2}{(h-1)(h+1)^2(h+2)},\qquad
T=hp(2\beta+1)(h-1),
$$

并令

$$
J=2\beta(h-1)(h+1)^2+h^2(h+1)-2hp(h+2).
\tag{313.8}
$$

代入式（313.7）直接整理得到

$$
A_2=-K_0J,\qquad A_1+A_2=-K_0T.
\tag{313.9}
$$

因此对 $\{i,j,k\}=\{1,2,3\}$，使用 $x_i+x_j=1-x_k$，有精确的差值公式

$$
\rho_i-\rho_j
=\frac{K_0}{cf(\beta+m)}
(x_i-x_j)(Jx_k-T).
\tag{313.10}
$$

只需证明 $Jx_k-T>0$。由 $p\le1/3$、$h\ge2$，

$$
\begin{aligned}
2J-(2\beta+1)(h^2-1)(h+2)
&=2\beta h(h^2-1)+h^3+h+2-4hp(h+2)\\
&\ge2\beta h(h^2-1)
+\frac{(h-1)(3h^2-h-6)}3>0.
\end{aligned}
\tag{313.11}
$$

最后一式严格为正，因为 $\beta>0$、$h\ge2$，且 $3h^2-h-6\ge4$。这也证明 $J>0$，并使

$$
\frac TJ
<\frac{2ph}{(h+1)(h+2)}
=\frac qp
=\frac1{x_1^{-1}+x_2^{-1}+x_3^{-1}}
<\min_i x_i.
\tag{313.12}
$$

故式（313.10）中除 $x_i-x_j$ 外的因子都严格为正，证明式（313.1）。这个推导也包括两个或三个坐标相等的情形，不除以任何坐标差。

第312节已经证明：在正定支撑分支，$\mathcal E_a=0$ 恰好要求三个 $\rho_i$ 相等。式（313.1）使其等价于 $x_1=x_2=x_3=1/3$。第309节的唯一权重重构随后给出 $w_i=1/3$，即三个正倒数半径相等。反过来，等半径的唯一解具有这个均匀单纯形参数，三个衰减率相等。因此式（313.2）成立。证毕。

**推论 313.2（任意正半径的二阶等号范围）。** 在全部正半径六态模型中，令 $t(\delta)$ 为达到残差预算 $\eta(1-\delta)$ 的唯一半群参数。标量恢复误差之差满足

$$
e(e^{-t(\delta)M_*})-\widehat G_a\bigl(\eta(1-\delta)\bigr)
=o(\delta^2)\qquad(\delta\downarrow0),
$$

恰当且仅当模型属于下列情形之一：

- 三个半径相等；
- 在某次坐标置换后，$a_1=a_2=a$、$a_3=a/k$，其中
  $k\ge\sqrt{(3+\sqrt{17})/2}$。

这里半径仍满足原六态模型的物理范围。除此之外，存在严格正系数 $\mathcal E_a$ 使式（312.2）成立，固定半群因而在每个充分小的正预算差处严格次优。

证明。正定支撑分支由定理313.1完全处理。奇异支撑分支由定理312.2要求非零支撑的两个坐标半径相等。第305节又保证零支撑坐标具有唯一最大的倒数半径，所以经坐标置换可写成上述轴向族。第302、305节的显式阈值使该轴向模型恰在 $k\ge\sqrt{(3+\sqrt{17})/2}$ 时进入奇异支撑分支，且包含阈值本身。反向逐项使用这些结论即得等价性。其余模型的系数严格正，再用式（312.2）的余项结论即可。证毕。

这是固定端点生成元在二阶精度下的完整分类。第二类等号模型的更高阶差距、一般有限预算的最优恢复路径，以及允许生成元随预算改变时的最优性，仍未由这一分类决定。

<a id="entry-976"></a>

## 追加锚（本行以下为增补区）

<a id="section-314"></a>

## 314. 必要旋转使端点半群在正时间进入可分条件的严格内部

**定理 314.1（全部正时间的严格奇异值间隙）。** 固定正半径六态模型，令 $M_*=S_*-\Omega_*$ 为第298、301节的唯一正角点端点矩阵，$d_1\le d_2<d_3=d_1+d_2$ 为 $S_*$ 的特征值，$v$ 为其单位最大特征向量。对 $t>0$，令 $s_1(t)\ge s_2(t)\ge s_3(t)>0$ 为 $T_t=e^{-tM_*}$ 的奇异值。则

$$
s_3(t)^2\ge\det T_t=e^{-2d_3t}.
\tag{314.1}
$$

在任意一个正 $t$ 处取等，恰当且仅当三个半径相等。因此不等半径时，对每个 $t>0$ 都有

$$
s_1(t)s_2(t)<s_3(t).
\tag{314.2}
$$

这是第293节所用幺元可逆微分可分条件的严格不等式；它不声称严格满足该条件的通道就是预算最优通道。

证明。对 $y(s)=e^{sM_*}y_0$，

$$
\frac{d}{ds}\|y(s)\|_2^2
=2y(s)^{\mathsf T}S_*y(s)
\le2d_3\|y(s)\|_2^2.
$$

故 $\|e^{tM_*}\|_{\rm op}\le e^{d_3t}$。最小奇异值等于逆矩阵算子范数的倒数，所以
$s_3(t)\ge e^{-d_3t}$。又因 $\operatorname{Tr}M_*=\operatorname{Tr}S_*=2d_3$，矩阵指数的行列式给出式（314.1）。

现在设在某个 $t_0>0$ 取等。单位球紧，存在单位向量 $y_0$ 使
$\|e^{t_0M_*}y_0\|_2=e^{d_3t_0}$。沿这条轨道，

$$
\frac{d}{ds}\left(e^{-2d_3s}\|y(s)\|_2^2\right)
=-2e^{-2d_3s}y(s)^{\mathsf T}(d_3I-S_*)y(s)\le0.
\tag{314.3}
$$

起点与终点相等，使非负的连续耗散被积函数在整个 $[0,t_0]$ 上为零。由于 $d_1,d_2>0$，最大特征值 $d_3=d_1+d_2$ 单重，所以 $y(s)$ 始终位于 $\mathbb Rv$。指数矩阵可逆，轨道从不为零；在 $s=0$ 求导便迫使 $M_*v\in\mathbb Rv$。由 $S_*v=d_3v$ 及反对称性，得到 $\Omega_*v=0$。

第301节同时给出 $v\cdot\omega=0$，其中 $\Omega_*x=\omega\times x$。$\Omega_*v=0$ 使 $\omega$ 平行于 $v$，所以 $\omega=0$。第299节于是迫使三个半径相等。反过来，等半径时 $M_*=(I+nn^{\mathsf T})/2$，其最小半群奇异值恰为 $e^{-t}$，而行列式为 $e^{-2t}$，所以每个正参数处都取等。

最后，$\det T_t>0$，且等于三个奇异值的乘积。因 $s_3(t)>0$，式（314.1）的严格形式等价于式（314.2）。证毕。

**定理 314.2（严格可分间隙的首个非零阶）。** 定义坐标不变的量

$$
\Xi_a=(\Omega_*v)^{\mathsf T}(d_3I-S_*)(\Omega_*v).
\tag{314.4}
$$

则对每个固定模型，在 $t\downarrow0$ 时，

$$
\log\frac{s_3(t)^2}{\det T_t}
=\frac{\Xi_a}{6}t^3+O(t^4),
\qquad
\frac{s_3(t)^2}{\det T_t}
=1+\frac{\Xi_a}{6}t^3+O(t^4).
\tag{314.5}
$$

$\Xi_a>0$ 恰当且仅当三个半径不全相等。特别地，不等半径端点生成元虽满足耗散锥的等号，其固定半群在每个正时间严格满足可分奇异值条件，而相应间隙从三阶开始。

证明。这里直接使用既有的短时间半群范数定理，而不将三次衰减的一般机制作为新结论。Achleitner、Arnold 与 Carlen，*The hypocoercivity index for the short time behavior of linear time-invariant ODE systems*，Journal of Differential Equations 371 (2023)，[arXiv v5 定理2.7及式（2.9）](https://arxiv.org/abs/2109.10784v5)，DOI [10.1016/j.jde.2023.06.027](https://doi.org/10.1016/j.jde.2023.06.027)，给出了下述适用情形：若 $B$ 的对称部分 $B_H\succeq0$，其 hypocoercivity index 为一，则

$$
\|e^{-tB}\|_{\rm op}
=1-c_Bt^3+O(t^4),\qquad
c_B=\frac1{12}\min_{\substack{x\in\ker B_H\\\|x\|_2=1}}
(Bx)^{\mathsf T}B_H(Bx).
\tag{314.6}
$$

将它接到本模型，取

$$
B=d_3I-M_*=(d_3I-S_*)+\Omega_*,\qquad
B_H=D:=d_3I-S_*,\qquad B_A=\Omega_*.
\tag{314.7}
$$

这里 $D\succeq0$、$\ker D=\mathbb Rv$，而 $D$ 在 $v^\perp$ 上正定。对不等半径，第299、301节给出 $\Omega_*v\ne0$。于是 $D$ 本身不正定，但

$$
D+\Omega_*D\Omega_*^{\mathsf T}\succ0.
\tag{314.8}
$$

具体地，若它在 $x$ 上的二次型为零，第一项使 $x\in\mathbb Rv$。第二项随后等于 $x$ 沿 $v$ 的系数平方乘以 $\Xi_a$，而 $\Xi_a>0$；故 $x=0$。这正是所引文献定义2.1在 $m=1$ 处的正定条件，而 $m=0$ 不成立，所以 index 恰为一。

所引定理允许复向量；实矩阵在实、复欧氏空间上的算子范数相同，复单位核向量 $e^{i\theta}v$ 也都给出相同二次型值。因此可直接使用这里的实空间表述。又因 $Bv=\Omega_*v$，实单位核向量 $\pm v$ 的二次型值均为 $\Xi_a$。因此该定理在本模型上精确给出

$$
e^{-d_3t}\|e^{tM_*}\|_{\rm op}
=1-\frac{\Xi_a}{12}t^3+O(t^4).
\tag{314.9}
$$

这里精确地有 $s_3(t)^2/\det T_t=\|e^{-tB}\|_{\rm op}^{-2}$。取对数便得到式（314.5）的第一式；再取指数得到第二式。

最后，$\Omega_*v\perp v$，所以 $D$ 在该方向上的正定性说明 $\Xi_a=0$ 恰好要求 $\Omega_*v=0$。定理314.1证明中已将这个条件等价为三个半径相等。等半径时不使用 index 一的定理：直接由显式半群可知比值恒为一，$\Xi_a=0$，故式（314.5）仍成立。证毕。

能量估计与 hypocoercivity 短时间范数定理都是既有结果。本节给出的是它们在唯一端点解上的精确作用：必要的旋转把轨道带离最大耗散轴，使生成元处的等号不再沿有限时间半群保留。这个可分性间隙与第312、313节的恢复误差超额是两个不同读数；三阶奇异值间隙本身不证明三阶恢复误差差距，也不决定有限预算最优通道。

<a id="entry-978"></a>

## 追加锚（本行以下为增补区）

<a id="section-315"></a>

## 315. 内部预算最优恢复的可分边界与固定端点半群的全预算次优性

**定理 315.1（每个内部预算最优恢复都在可分边界上）。** 对任意固定正半径六态模型及 $0<R<\eta$，每个达到实际受限最优值 $\widehat G_a(R)$ 的复合恢复通道都幺元，其 Bloch 矩阵 $T$ 可逆、$\det T>0$，而排序奇异值满足

$$
0<s_3\le s_2\le s_1\le1,\qquad s_1s_2=s_3.
\tag{315.1}
$$

等价地，$s_3(T)^2=\det T$。若 $s_1<1$，该最优恢复的 Choi 矩阵正定；若 $s_1=1$，则 $s_2=s_3$，且其在独立的输入、输出酉共轭下等价于退相干通道。结论作用于实际最优复合通道，不要求原编码、解码分别幺元。

证明。第293节已经证明每个实际最优恢复都幺元。先排除奇异 Bloch 矩阵。Wolf 与 Cirac 的[定理24及式（51）](https://arxiv.org/abs/math-ph/0611057v3)，在幺元通道的对角正规形上给出两种可能：Bloch 秩小于二，或矩阵可逆且 $s_3^2\ge\det T>0$。这正是第293节所用的分类；不能把可逆情形的不等式直接延伸为允许 Bloch 秩二的判据。

若一个允许恢复 $T$ 奇异，则其像包含于某条直线 $\mathbb Ru$，其中 $u$ 取单位向量；$T=0$ 时任取一条直线。记 $P=uu^{\mathsf T}$。正交投影的最近点性质使

$$
\|(I-P)e_i\|_2\le\|(I-T)e_i\|_2
\quad(i=1,2,3),\qquad e(P)\le e(T).
\tag{315.2}
$$

矩阵 $P$ 是沿 $u$ 的完全退相干通道。对 $0<\varepsilon<1$，取

$$
T_\varepsilon=P+\varepsilon(I-P).
\tag{315.3}
$$

它的奇异值为 $1,\varepsilon,\varepsilon$，是幺元 CPTP 且微分可分的有限参数退相干半群成员。选任意单位 $n\perp u$，就有 $T_\varepsilon^{\mathsf T}n=\varepsilon n$，所以

$$
r_*(T_\varepsilon)\le\varepsilon\max_i a_i|n_i|
\le\varepsilon\max_i a_i.
$$

因 $R>0$，可取足够小的正 $\varepsilon$ 使其在预算 $R$ 下可行。同时

$$
e(T_\varepsilon)=(1-\varepsilon)e(P)<e(T),
\tag{315.4}
$$

其中 $e(P)>0$ 来自正半径三轴张成整个空间，直线投影不可能在所有输入上为恒等。这给出同预算的严格改进，故奇异恢复不能最优。上述通道与所用残差方向按第281节由同一对实际编码、解码实现。

因此最优矩阵可逆，所引分类给出 $\det T>0$ 及 $s_3^2\ge\det T$，也就是 $s_1s_2\le s_3$。CPTP 的迹距离压缩又给出 $s_1\le1$。

下面核对严格可分条件自动蕴含完全正内点。由于 $\det T>0$，左右两个正向正交变换可把 $T$ 化为对角矩阵 $\operatorname{diag}(s_1,s_2,s_3)$；这些变换对应独立的输入、输出酉操作，保持 Choi 秩。标准幺元 Pauli 正规形的四个概率是

$$
\frac{1+s_1+s_2+s_3}{4},\quad
\frac{1+s_1-s_2-s_3}{4},\quad
\frac{1-s_1+s_2-s_3}{4},\quad
\frac{1-s_1-s_2+s_3}{4}.
\tag{315.5}
$$

若 $s_1s_2<s_3$，最后一个分子为
$(1-s_1)(1-s_2)+(s_3-s_1s_2)>0$。第二个分子为 $(1-s_3)+(s_1-s_2)>0$，因为 $s_3=1$ 会迫使三个奇异值全为一而违反严格条件。第三个分子为 $(1-s_1)+(s_2-s_3)$，只能在 $s_1=1,s_2=s_3$ 时为零，但这种情况同样违反严格条件。第一个显然严格正。因此四个概率都正，$J(T)\succ0$。此处直接使用已在第285、293节引用的标准 Pauli 正规形，不另假设 Choi 内点。

最后在严格条件下应用第285节的局部完全正边界论证。需要核对的不是一般凸平均保留微分可分性，而是该证明所需的每次扰动都能留在同一个开邻域。

反设 $s_3(T)^2>\det T>0$。前面的 Pauli 概率比较已给出 $J(T)\succ0$。在代表幺元、保迹映射的实 Bloch 矩阵空间中，取包含 $T$ 的开邻域 $\mathcal U$，使每个矩阵均 Choi 正定、正行列式，并满足严格奇异值条件。Choi 矩阵、行列式及奇异值的连续性保证这种邻域存在。由第293节引用的 Wolf–Cirac 幺元可逆判据，$\mathcal U$ 内每个矩阵都是允许的微分可分 CPTP 恢复通道。

选一个使 $|n\cdot Te_i|\le R\alpha_i$ 的单位方向 $n$。沿用式（285.3）的逐列板层投影矩阵

$$
Z(n)e_i=e_i-n\operatorname{sgn}(n_i)(|n_i|-R\alpha_i)_+,
\qquad
\mu(n)=\max_i a_i|n_i|,\qquad m(n)=\frac{\mu(n)-R}{2}>0.
\tag{315.5a}
$$

这里 $\mu(n)\ge\eta>R$，并且 $e(T)\ge m(n)$。若不等式严格，取充分小的 $\lambda>0$，则
$T_\lambda=(1-\lambda)T+\lambda Z(n)$ 留在 $\mathcal U$，同时保留原方向的残差约束。范数凸性给出
$e(T_\lambda)\le(1-\lambda)e(T)+\lambda m(n)<e(T)$，与最优性矛盾。只对实际靠近 $T$ 的矩阵使用物理性，不要求 $Z(n)$ 自身完全正。因此必须有 $e(T)=m(n)$。

令 $I=\{i:a_i|n_i|=\mu(n)\}$。对 $i\in I$，板层中的最小列误差已经达到总误差，欧氏投影唯一性使 $Te_i=Z(n)e_i$。再作一次任意小的正权重混合，得到 $\overline T\in\mathcal U$：它的活跃列不变，而全部非活跃列的误差严格小于 $m(n)$。误差仍为 $m(n)$，故它也最优。

若 $I$ 不含全部三轴，按第285节的显式构造任意小地移动单位方向，使每个活跃 $a_i|n_i|$ 都严格下降：非活跃坐标部分不为零时缩小活跃部分并放大非活跃部分以保持单位范数；非活跃坐标全为零时，向一个非活跃坐标轴作小角旋转。记新方向为 $n(t)$。

新矩阵的活跃列取 $Z(n(t))e_i$，非活跃列取 $\overline Te_i$ 到新板层 $|n(t)\cdot x|\le R\alpha_i$ 的欧氏投影。板层投影关于单位法向量连续，所以新矩阵趋于 $\overline T$；充分小的 $t>0$ 使它仍在 $\mathcal U$。活跃列误差严格下降，非活跃列则靠已固定的严格余量与连续性保持较小误差。所有列仍满足同一方向的残差约束，于是得到更好的允许通道，再次矛盾。

若全部三轴活跃，则 $|n_i|=\eta\alpha_i$，且

$$
T=Z(n)=I-(1-R/\eta)nn^{\mathsf T}.
$$

其本征值为 $1,1,R/\eta$，对应的 Pauli 概率中有 $(R/\eta-1)/4<0$，所以它不是 CPTP，也产生矛盾。

因此最优恢复不可能满足严格的奇异值条件。允许类在此范围满足 $s_3(T)^2\ge\det T$，故只能取等。上述每个更好矩阵及其方向都按第281节由同一对完整二维编码、解码实现，比较的仍是实际预算最优值。


再看等号面上的 Choi 秩。代入 $s_3=s_1s_2$，式（315.5）的四个分子分别变为
$(1+s_1)(1+s_2)$、$(1+s_1)(1-s_2)$、$(1-s_1)(1+s_2)$、$(1-s_1)(1-s_2)$。若 $s_1<1$，四项均严格正；若 $s_1=1$，则谱为 $(1,s_2,s_2)$，即独立输入、输出酉操作下等价的退相干形式。这完成全部结论。证毕。

**定理 315.2（不等半径固定端点半群的全预算次优性）。** 若三个半径不全相等，则对每个 $0<R<\eta$，令 $t_R>0$ 是使固定端点半群 $T_t=e^{-tM_*}$ 的残差恰为 $R$ 的唯一参数，有

$$
\widehat G_a(R)<e(T_{t_R}).
\tag{315.6}
$$

更强地，对每个满足 $r_*(T_t)\le R$ 的有限参数 $t$，都有 $\widehat G_a(R)<e(T_t)$。

证明。第304节保证 $t_R$ 的存在唯一性。每个正参数的半群成员都是可逆、正行列式的幺元 CPTP 通道，第314节使其严格满足 $s_3(T_t)^2>\det T_t$。所以凡在预算 $R$ 下可行的成员，都不满足定理315.1要求的等号条件。

该半群成员的两个成本按第281节由同一对实际通道同时实现，故 $\widehat G_a(R)\le e(T_t)$。若等号成立，它本身就是实际最优恢复，与定理315.1矛盾。因此不等式严格；取 $t=t_R$ 即得式（315.6）。证毕。

**推论 315.3（近端点固定半群最优性恰为等半径）。** 对每个固定正半径模型，唯一端点最优生成元形成的固定半群在所有充分接近 $\eta$ 的较小预算上均达到实际受限最优值，恰当且仅当三个半径相等。

证明。不等半径由定理315.2排除。等半径时，端点半群在残差比 $q=R/\eta$ 下具有沿 $n$ 的奇异值 $q$ 和沿 $n^\perp$ 的两个奇异值 $\sqrt q$。它的恢复误差恰为第293节式（293.7）的已知精确最优值，该式覆盖整个 $1/4\le q\le1$。所以等半径在这一已知区间内达到最优。证毕。

这里排除的是由唯一端点生成元固定产生的半群，不排除随预算改变生成元的其他半群，也不排除其他无限小可分通道。第313节中的奇异轴向二阶等号族仍保留 $o(\delta^2)$ 的超额结论；本节额外证明每个内部预算处误差都严格更大，却没有给出该族近端点差距的首个非零阶或精确系数。第314节的三阶奇异值间隙仍不能直接当作三阶恢复误差差距。定理315.1确定了实际最优恢复必须满足的奇异值边界，没有把这条边界上的取向和最优奇异值全部求出。

<a id="entry-980"></a>

## 追加锚（本行以下为增补区）

<a id="section-316"></a>

## 316. 二阶等号轴向族的显式三阶可行改进

第313节的奇异轴向族使固定端点半群的二阶误差超额为零。第315节仍在每个内部预算排除了其最优性。本节直接构造同预算的更好通道，并给出严格正的三阶改进系数；所求出的系数属于这个显式改进方案，不是实际最优曲线的三阶系数。

**定理 316.1（径向归一化的三阶恢复收益）。** 取第302节的参数

$$
a_1=a_2=a,\qquad a_3=a/k,\qquad
0<a\le1,\qquad k\ge k_0=\sqrt{\frac{3+\sqrt{17}}2},
$$

记 $B=1+k^2$、$r=\sqrt{k^2+2}$、$\eta=a/r$，并令 $M_*$ 为式（302.2）的固定端点矩阵。对 $T_t=e^{-tM_*}$ 定义

$$
c(t)=\frac{s_3(T_t)^2}{\det T_t},\qquad U_t=c(t)T_t,
\tag{316.1}
$$

其中 $s_3$ 是最小奇异值。每个 $t\ge0$ 的 $U_t$ 都是幺元 CPTP 且微分可分，并精确位于奇异值边界 $s_1(U_t)s_2(U_t)=s_3(U_t)$。

对 $R_\delta=\eta(1-\delta)$，设 $t_\delta$ 是 $r_*(T_{t_\delta})=R_\delta$ 的唯一参数。对充分小的正 $\delta$，存在唯一趋于零的正参数 $\tau_\delta$，使 $r_*(U_{\tau_\delta})=R_\delta$。这两条曲线在相同实际残差预算下满足

$$
e(T_{t_\delta})-e(U_{\tau_\delta})
=\frac{ak^4r}{384B^{7/2}}\,\delta^3+O(\delta^4).
\tag{316.2}
$$

因此

$$
\liminf_{\delta\downarrow0}
\frac{e(T_{t_\delta})-\widehat G_a(R_\delta)}{\delta^3}
\ge\frac{ak^4r}{384B^{7/2}}>0.
\tag{316.3}
$$

这里 $e$ 始终是原三轴六态模型的最坏迹距离误差，所有渐近式都对固定 $a,k$ 而言，包括临界参数 $k=k_0$。

证明。先说明式（316.1）的物理性，这一步只是标准幺元 Pauli 正规形和第293节所引 Wolf–Cirac 判据的直接应用。对任意正行列式的可逆实矩阵 $T$，写其排序奇异值为 $s_1\ge s_2\ge s_3>0$，并令 $c=s_3/(s_1s_2)$。则 $cT$ 的排序奇异值满足

$$
u_1=\frac{s_3}{s_2}\le1,\qquad
u_2=\frac{s_3}{s_1}\le u_1,\qquad
u_3=\frac{s_3^2}{s_1s_2}=u_1u_2.
\tag{316.4}
$$

正行列式使左右奇异向量变换可取为正向旋转。相应 Pauli 概率恰为四个非负数 $(1\pm u_1)(1\pm u_2)/4$，故给出完整量子比特上的幺元 CPTP 通道。它又满足可逆微分可分条件的等号，所以属于允许类。将此应用于 $T_t$，得到全部有限参数下 $U_t$ 的物理性。$t=0$ 时 $c(0)=1$、$U_0=I$。这一缩放是 Bloch 矩阵的缩放，定义的新通道仍保持恒等算子；不是把保迹超算子整体乘以 $c$。

下面求同预算参数。第314节给出

$$
c(t)=1+\gamma t^3+O(t^4),\qquad
\gamma=\frac{\Xi_a}{6}.
\tag{316.5}
$$

在当前轴向标架 $(u,w,z)$ 中，反对称部分只作用于 $u,z$ 平面，其旋转强度平方为 $k^2/(8B^2)$；最大对称特征轴 $v$ 也在该平面。$d_3I-S_*$ 在该平面中垂直于 $v$ 的方向上具有特征值 $d_w=kr/(2B)$。所以

$$
\Xi_a=\frac{k^2}{8B^2}\frac{kr}{2B}
=\frac{k^3r}{16B^3},\qquad
\gamma=\frac{k^3r}{96B^3}>0.
\tag{316.6}
$$

式（316.5）确可在零点附近按通常解析函数求导和局部反解。为核对这一点，把

$$
K(t)=\frac{e^{tM_*^{\mathsf T}}e^{tM_*}-I}{2t}
\tag{316.7}
$$

在 $t=0$ 解析延拓为 $S_*$。其最大特征值 $d_3$ 单重，特征多项式的单根隐函数论证使相应特征值支在零点附近解析；对小正 $t$，它给出 $e^{tM_*^{\mathsf T}}e^{tM_*}$ 的最大特征值。因此 $c(t)=e^{2d_3t}/\|e^{tM_*}\|_{\rm op}^2$ 有相同的局部解析延拓。

第305节的固定角点公式给出

$$
f(t):=\frac{r_*(T_t)}\eta
=\frac{\|b\|_2}{\|e^{tM_*^{\mathsf T}}b\|_2},
\qquad f(0)=1,\qquad f'(0)=-1.
\tag{316.8}
$$

导数使用 $M_*b=b$。残差定义对正标量齐次，所以 $r_*(U_t)/\eta=c(t)f(t)$。这个解析函数在零点的导数也为 $-1$，故局部严格下降，并有唯一的小正预算反解。由 $f(t_\delta)=1-\delta$ 和 $c(\tau_\delta)f(\tau_\delta)=1-\delta$，式（316.5）给出

$$
t_\delta=\delta+O(\delta^2),\qquad
\tau_\delta-t_\delta=\gamma t_\delta^3+O(t_\delta^4).
\tag{316.9}
$$

于是矩阵指数展开得到

$$
U_{\tau_\delta}
=T_{t_\delta}+\gamma t_\delta^3(I-M_*)+O(t_\delta^4).
\tag{316.10}
$$

现在必须在原输入坐标中比较最大列误差，不能把 $(u,w,z)$ 当成另一个输入三轴模型。写

$$
p=\frac{r^2}{2B},\qquad h=\frac{kr}{2B},\qquad
 g=\frac{k\sqrt2}{2B},\qquad
[M_*]_{(u,w,z)}=\begin{pmatrix}p&0&g\\0&h&0\\0&0&1\end{pmatrix}.
\tag{316.11}
$$

原坐标为 $e_1=(u+w)/\sqrt2$、$e_2=(u-w)/\sqrt2$。对 $i=1,2$，直接计算得

$$
\|M_*e_i\|_2=\frac r{2\sqrt B},\qquad
\langle M_*e_i,e_i\rangle-\|M_*e_i\|_2^2
=\frac{kr}{4B}>0.
\tag{316.12}
$$

交换前两轴的对称性使其误差对两条通道曲线始终相等。若 $k>k_0$，第三轴的一阶误差严格较小，故在充分小的正参数下，最大误差恰由前两轴取得。

临界点 $k=k_0$ 不能使用这一严格一阶余量。对任一列，记

$$
\rho_i=\frac{\langle M_*e_i,M_*^2e_i\rangle}{\|M_*e_i\|_2^2}.
$$

则

$$
\frac{a_i}{2}\|(I-T_t)e_i\|_2
=\frac{a_i\|M_*e_i\|_2}{2}
\left(t-\frac{\rho_i}{2}t^2\right)+O(t^3).
\tag{316.13}
$$

式（316.11）和 $0<p,h<1$ 给出

$$
\rho_1=\rho_2=\frac{p^3+h^3}{p^2+h^2}<1,
\qquad
\rho_3=1+\frac{g^2p}{1+g^2}>1.
\tag{316.14}
$$

在临界点三个一阶系数相等，因此第三列从二阶起就严格小于前两列。式（316.10）的三阶扰动不改变这条二阶严格比较。故包括临界点在内，两条曲线的最大误差都可用任一前两列计算。

最后，对非零向量 $m_i=M_*e_i$，将式（316.10）代入欧氏范数的一阶变化。由于 $(I-T_t)e_i=t m_i+O(t^2)$，得到

$$
\begin{aligned}
e(T_{t_\delta})-e(U_{\tau_\delta})
&=\gamma t_\delta^3\frac a2
\frac{\langle m_i,e_i\rangle-\|m_i\|_2^2}{\|m_i\|_2}
+O(t_\delta^4)\\
&=\gamma\frac{ak}{4\sqrt B}\,t_\delta^3+O(t_\delta^4).
\end{aligned}
\tag{316.15}
$$

代入式（316.6）、（316.9）即得式（316.2）。每个 $U_{\tau_\delta}$ 及其残差最小方向按第281节由同一对完整二维编码、解码实现。因此 $\widehat G_a(R_\delta)\le e(U_{\tau_\delta})$，从而得到式（316.3）。证毕。

本节把第314节的三阶奇异值间隙转成了一个经过物理性与同预算检查的三阶误差改进。第313节仍只为原固定半群的实际最优超额提供 $o(\delta^2)$ 上阶信息；本节没有证明该超额为 $O(\delta^3)$，也没有认定径向归一化曲线就是最优曲线。标准 Pauli 正规形、可分判据、简单特征值的局部解析性及范数微分是既有工具，新增推导是它们在这条二阶等号族上给出的明确可达收益。

<a id="entry-982"></a>

## 追加锚（本行以下为增补区）

<a id="section-317"></a>

## 317. 任意正半径的零预算精确值与全部最优恢复

第290节给出了等半径模型的零预算值，第292节给出了所有幺元 Choi 秩二通道的系数下界 $C_2$。这里把后者识别为一般正半径模型在微分可分限制下的精确零预算值，并确定全部达到它的复合恢复。证明使用第293节的幺元化、既有可分通道分类及欧氏投影，不另提出通道分类定理。

**定理 317.1（零预算值与最优直线）。** 固定正半径六态模型，将倒数半径排序为 $0<\alpha_1\le\alpha_2\le\alpha_3$，记

$$
A=\sum_i\alpha_i^2,\qquad \eta=A^{-1/2},\qquad
E_0=\max\left\{\frac1{\sqrt{2A}},\,
\frac1{2\sqrt{\alpha_1^2+\alpha_2^2}}\right\}.
\tag{317.1}
$$

则不额外限制原编码、解码幺元性的实际受限预算函数满足

$$
\widehat G_a(0)=E_0.
\tag{317.2}
$$

每个实际最优复合恢复都恰为沿某条直线完全退相干的通道，其 Bloch 矩阵为

$$
P_u=uu^{\mathsf T},\qquad
u_i^2=(1-4E_0^2\alpha_i^2)_+.
\tag{317.3}
$$

反过来，每个满足式（317.3）的单位向量都给出零预算最优恢复。整体符号视为同一矩阵：当 $\alpha_3^2<\alpha_1^2+\alpha_2^2$ 时共有四个最优矩阵；当 $\alpha_3^2\ge\alpha_1^2+\alpha_2^2$ 时共有两个，且 $u_3=0$。这包括取等的阈值。

证明。第293节使每个实际最优恢复都幺元。零实际残差使其 $r_*(T)=0$，所以 $T$ 奇异；Wolf–Cirac 定理24在幺元类中的秩判据将其 Bloch 秩限制为至多一。若 $T$ 的像在 $\mathbb Ru$ 内，取 $u$ 为单位向量并记正交投影为 $P_u$。欧氏最近点性质给出

$$
\|(I-P_u)e_i\|_2\le\|(I-T)e_i\|_2,
\qquad
e(P_u)=\frac12\max_i a_i\sqrt{1-u_i^2}\le e(T).
\tag{317.4}
$$

$T=0$ 时任选直线亦可。$P_u$ 是标准完全退相干通道，属于闭微分可分类，并具有零最小残差；按第281节可由同一对完整二维编码、解码达到两个成本。因此问题的值等于对单位向量 $u$ 最小化式（317.4）。

给定候选误差 $E\ge0$，使 $e(P_u)\le E$ 等价于寻找非负数 $u_i^2$，满足

$$
\sum_i u_i^2=1,\qquad
u_i^2\ge(1-4E^2\alpha_i^2)_+.
\tag{317.5}
$$

这种选择存在，当且仅当三个下界之和不超过一。函数

$$
L(E)=\sum_i(1-4E^2\alpha_i^2)_+
\tag{317.6}
$$

从 $L(0)=3$ 连续下降，并在到达零以前严格下降。故最小可行误差是唯一的正根 $L(E)=1$。

若 $\alpha_3^2\le\alpha_1^2+\alpha_2^2$，取 $E=1/\sqrt{2A}$，则所有括号均非负，且其和为 $3-2=1$。第三项仅在该条件取等时为零。若 $\alpha_3^2\ge\alpha_1^2+\alpha_2^2$，取 $E=1/(2\sqrt{\alpha_1^2+\alpha_2^2})$，则前两项严格正且和为一，第三项为零。这两种表达在阈值一致；比较它们的大小便得到式（317.1）。

在最小误差处，式（317.5）的下界之和已经等于一，所以每个平方坐标必须逐项取等。这确定了全部最优投影方向。然而还须排除误差相同的非投影秩一恢复，不能只用投影支配就声称分类完毕。

设实际最优矩阵非零，写为 $T=uz^{\mathsf T}$，其中 $u$ 单位。迹距离收缩使 $\|T\|_{\rm op}=\|z\|_2\le1$。因 $e(P_u)\le e(T)=E_0$，上述唯一平方坐标结论已使 $u$ 满足式（317.3）。对每个 $u_i\ne0$ 的坐标，其投影误差达到 $E_0$，同时有正交分解

$$
\|e_i-z_i u\|_2^2
=1-u_i^2+(z_i-u_i)^2.
\tag{317.7}
$$

原误差不能超过 $E_0$，故这些坐标必须满足 $z_i=u_i$。它们已经承担 $u$ 的全部单位范数，因而

$$
1\ge\|z\|_2^2
=1+\sum_{i:u_i=0}z_i^2.
$$

于是其余 $z_i$ 也为零，得到 $T=P_u$。零矩阵的误差为 $a_1/2>E_0$，所以不可能最优。

最后，严格三项区间中三个 $u_i$ 都非零，八种符号除整体正负给出四个投影；另一区间只有前两项非零，四种符号给出两个投影。坐标排序只是重命名输入轴。所有投影均由前面的实际方案达到，完成值与全部复合恢复的分类。证毕。

**定理 317.2（从零预算最优直线出发的精确可达曲线）。** 取定理317.1的任一最优单位方向 $u$。对符号角点 $b_\sigma=(\sigma_i\alpha_i)$ 定义

$$
m_u=\min_{\sigma\in\{\pm1\}^3}(u\cdot b_\sigma)^2,
\qquad 0\le m_u<A.
\tag{317.8}
$$

对 $0\le R\le\eta$，记

$$
\varepsilon(R)=\frac{R\sqrt{A-m_u}}{\sqrt{1-m_uR^2}},
\qquad
P_{u,\varepsilon}=P_u+\varepsilon(I-P_u).
\tag{317.9}
$$

则同一对实际二维编码、解码可以具有复合恢复 $P_{u,\varepsilon(R)}$、残差恰为 $R$，以及误差

$$
e(P_{u,\varepsilon(R)})
=E_0\left(1-\frac{R\sqrt{A-m_u}}{\sqrt{1-m_uR^2}}\right).
\tag{317.10}
$$

所以式（317.10）是 $\widehat G_a(R)$ 在整个 $[0,\eta]$ 上的可达上界，并在两个端点取等。全部零预算最优方向给出相同的 $m_u$ 和这条上界曲线。

证明。式（317.3）的方向至少有两个非零坐标，因而可给其中两个坐标选相反符号，使 $|u\cdot b_\sigma|<\sum_i|u_i|\alpha_i\le\sqrt A$。这证明 $m_u<A$，并保证式（317.9）的分母在所述闭区间严格为正。直接代入可知 $0\le\varepsilon(R)\le1$，两个端点分别为零和一。

对 $0<\varepsilon<1$，矩阵 $P_{u,\varepsilon}$ 是沿 $u$ 的有限参数退相干半群成员，奇异值为 $1,\varepsilon,\varepsilon$；$\varepsilon=0$ 是其闭类极限，$\varepsilon=1$ 为恒等。它们全部幺元、CPTP 且属于允许的闭微分可分类。这里不把完全退相干端点说成有限生成元在有限参数处达到。

对 $\varepsilon>0$，正交分解给出

$$
\|P_{u,\varepsilon}^{-1}b_\sigma\|_2^2
=(u\cdot b_\sigma)^2
+\varepsilon^{-2}\bigl(A-(u\cdot b_\sigma)^2\bigr).
\tag{317.11}
$$

当 $0<\varepsilon<1$ 时，右侧在内积平方最小时最大；$\varepsilon=1$ 时所有角点相同。故第281节的精确角点公式给出

$$
r_*(P_{u,\varepsilon})
=\frac{\varepsilon}{\sqrt{A-m_u+m_u\varepsilon^2}}.
\tag{317.12}
$$

令其等于 $R$，解得式（317.9）。另一方面，$I-P_{u,\varepsilon}=(1-\varepsilon)(I-P_u)$，所以最坏误差恰为 $(1-\varepsilon)E_0$。按照第281节选择最小残差方向并配以编码酉旋转及逆酉解码，两个成本由同一方案达到。零参数处单独使用定理317.1的零残差实现。

所有最优方向的坐标绝对值相同，符号改变只置换角点集合，所以 $m_u$ 不变。式（317.10）于是成立，零预算处值为 $E_0$，$R=\eta$ 时为零，分别等于实际最优值。证毕。

这给一般不等半径模型补上了另一个精确端点及全部达到恢复，同时把第291节的等半径退相干上界接到任意正半径。等半径时 $E_0=a/\sqrt6$、$m_u=1/(3a^2)$，式（317.9）还原该节的 $\sqrt8\,q/\sqrt{9-q^2}$。内部预算处仍只是可达上界；本节没有证明最优通道沿固定直线退相干，也没有由上界的导数认定实际最优曲线的导数。

<a id="entry-984"></a>

## 追加锚（本行以下为增补区）

<a id="section-318"></a>

## 318. 不等半径近端点最优恢复恰需两个齐次演化阶段

第315节排除了固定端点生成元的半群。本节允许每个预算重新选择任意时间齐次量子比特生成元，仍然在不等半径的近端点区间排除它达到实际微分可分最优值。限制仍施加在完整二维复合恢复上；“不能由一个固定生成元实现”不等于“不能由随演化参数改变的生成元或更大系统实现”。

**定理 318.1（最优恢复的最少齐次阶段数）。** 固定三个不全相等的正半径。存在依赖于该模型的 $\delta_0>0$，使对每个 $0<\delta<\delta_0$，任何达到

$$
\widehat G_a\bigl(\eta(1-\delta)\bigr)
$$

的实际复合恢复通道 $\Phi$，都不能写成

$$
\Phi=e^{\mathcal L}
\tag{318.1}
$$

其中 $\mathcal L$ 是完整量子比特上的任何时间齐次 GKSL 生成元。生成元可以随预算改变，也不预先要求它幺元；任意正的有限演化时间已吸收到 $\mathcal L$ 中。

另一方面，对任意正半径与每个 $0<R<\eta$，每个实际最优复合恢复都可写为两个齐次阶段的复合，其中第一段是幺元 Pauli 耗散，第二段是酉演化。因此，在上述不等半径近端点区间内，任何实际最优恢复的最少齐次阶段数恰为二。这里计数的是恢复通道本身在同一个量子比特上的分段实现，各段允许任意有限 GKSL 生成元；不把阶段数解释为演化时长或能量成本。

等半径时，式（293.7）的已知最优通道在 $R/\eta\in[1/4,1]$ 上由单个齐次生成元达到。因此，单个齐次生成元能在所有充分接近端点的预算上达到最优，恰当且仅当三个半径相等。

证明。先从标准半群性质与能量估计提取一个必要条件。设一个幺元量子比特通道 $\Phi$ 的 Bloch 矩阵 $T$ 满足

$$
\|T\|_{\rm op}<1,\qquad
s_3(T)^2=\det T>0,
\tag{318.2}
$$

并假设 $\Phi=e^{\mathcal L}$。下面证明存在单位实向量 $v$，满足

$$
Tv=T^{\mathsf T}v=s_3(T)v.
\tag{318.3}
$$

先去掉对生成元幺元性的潜在假设。严格收缩且幺元的 $\Phi$ 只有一个固定密度矩阵 $I/2$。对每个 $s\ge0$，同一半群的 $e^{s\mathcal L}$ 与 $\Phi$ 交换，所以 $e^{s\mathcal L}(I/2)$ 仍是 $\Phi$ 的固定密度矩阵，只能等于 $I/2$。因此整个半群幺元，其 Bloch 生成矩阵可以写成 $-M$，其中

$$
M=S-\Omega,\qquad S=S^{\mathsf T}\succeq0,\qquad
\Omega^{\mathsf T}=-\Omega,\qquad
2S\preceq(\operatorname{Tr}S)I.
\tag{318.4}
$$

这里使用第296节中已明确的标准幺元 GKSL 条件。设 $d$ 为 $S$ 的最大特征值。对逆演化 $y(s)=e^{sM}y_0$ 的能量估计给出

$$
\|e^M\|_{\rm op}\le e^d,\qquad
s_3(T)\ge e^{-d},\qquad
\det T=e^{-\operatorname{Tr}S}.
\tag{318.5}
$$

锥条件同时使 $\operatorname{Tr}S\ge2d$。式（318.2）因此强迫两步不等式都取等：

$$
\operatorname{Tr}S=2d,\qquad
\|e^M\|_{\rm op}=e^d,\qquad s_3(T)=e^{-d}.
\tag{318.6}
$$

取一个达到最后范数等号的单位初值 $y_0$。与第314节相同，

$$
\frac{d}{ds}\left(e^{-2ds}\|y(s)\|_2^2\right)
=-2e^{-2ds}y(s)^{\mathsf T}(dI-S)y(s)
\tag{318.7}
$$

在 $[0,1]$ 上积分为零，使整个轨道都位于最大特征空间 $E_d=\ker(dI-S)$。令 $W$ 为这段轨道的实线性包。它非零，且在 $M$ 下不变：轨道导数是轨道差商的极限，属于有限维闭子空间 $W$，再用线性性即可。由于 $S$ 在 $W$ 上为 $dI$，$W$ 也在 $\Omega=S-M$ 下不变。反对称性随后使 $W^\perp$ 在 $\Omega$ 下不变。

若 $\dim W=3$，则 $S=dI$；式（318.6）给出 $3d=2d$，故 $S=0$，$T$ 正交，与严格收缩矛盾。若 $\dim W=2$，则 $S$ 在该平面上的两个特征值都为 $d$，由 $\operatorname{Tr}S=2d$，其正交轴上的特征值为零。$\Omega$ 在这条一维不变轴上只能为零，因此 $M$ 也在该轴上为零，$T$ 在该轴上为恒等，再次违反严格收缩。

所以 $\dim W=1$。在这条不变直线上，反对称算子为零。取其单位向量 $v$，便有 $Mv=M^{\mathsf T}v=dv$，进而得到式（318.3）。这个必要条件允许生成元的最大对称特征值重根，也没有选择或限制矩阵对数的分支。

现在反设定理的近端点结论不成立。则存在 $\delta_j\downarrow0$ 和各预算上的实际最优恢复 $\Phi_j=e^{\mathcal L_j}$。第293节使每个 $\Phi_j$ 幺元，记其 Bloch 矩阵为 $T_j$。第296节的共同斜率及正半径列误差控制使

$$
M_j=\frac{I-T_j}{\delta_j}
\tag{318.8}
$$

有界。取收敛子列，记极限为 $M=S-\Omega$。第296节的一阶 Choi 条件和残差展开给出端点锥约束及 $g(S)\ge A$，而最优误差满足

$$
\frac12h_a(S,\Omega)=\kappa_a
\ge\kappa_a\frac{g(S)}A\ge\kappa_a.
\tag{318.9}
$$

因 $\kappa_a>0$，有 $g(S)=A$，且极限是端点最优方向。选取其最大角点的符号共轭，便由第298节的唯一性把极限化为正角点规范下的 $M_*$。该共轭保留实际误差、残差、奇异值和半群可实现性；对角符号矩阵与其相反数给出相同共轭，其中一个是物理正向旋转。因此以下可写为

$$
T_j=I-\delta_jM_*+o(\delta_j).
\tag{318.10}
$$

第298节使 $S_*\succ0$，所以

$$
T_j^{\mathsf T}T_j=I-2\delta_jS_*+o(\delta_j)
$$

在足够大的 $j$ 上严格小于 $I$。每个这样的 $T_j$ 都严格收缩。第315节还使每个实际最优矩阵满足 $s_3(T_j)^2=\det T_j>0$。于是式（318.3）的必要条件给出单位向量 $v_j$，满足

$$
T_jv_j=T_j^{\mathsf T}v_j=s_3(T_j)v_j.
\tag{318.11}
$$

再取子列使 $v_j\to v$。由奇异值的一阶展开，

$$
s_3(T_j)=1-\delta_jd_3+o(\delta_j),
$$

其中 $d_3$ 为 $S_*$ 的简单最大特征值。将式（318.11）减去恒等并除以 $\delta_j$，再取极限，得到

$$
M_*v=M_*^{\mathsf T}v=d_3v.
\tag{318.12}
$$

因此 $S_*v=d_3v$ 且 $\Omega_*v=0$。简单最大特征值使 $v=\pm v_*$。第301节同时给出 $v_*\cdot\omega=0$，其中 $\Omega_*x=\omega\times x$；而 $\Omega_*v_*=0$ 使 $\omega$ 平行于 $v_*$，所以 $\omega=0$。第299节遂要求三个半径全相等，与假设矛盾。这排除了任意趋近端点的反例序列，故存在所述 $\delta_0$。

剩下证明两个阶段总是足够。这一步使用标准极分解与幺元 Pauli 生成元，不把一般通道分解本身作为新分类。对任意内部预算的实际最优矩阵，第315节给出可逆、正行列式及 $s_1s_2=s_3$。取实极分解

$$
T=OP,\qquad O\in SO(3),\qquad P=(T^{\mathsf T}T)^{1/2}\succ0.
\tag{318.13}
$$

令 $P$ 的正交主轴为 $r_i$，相应特征值为排序奇异值 $s_i$，并写 $\ell_i=-\log s_i\ge0$。于是

$$
\ell_3=\ell_1+\ell_2,\qquad
L_P=\sum_i\ell_i r_i r_i^{\mathsf T},\qquad P=e^{-L_P}.
\tag{318.14}
$$

第296节的标准 Pauli 生成元构造，以非负速率

$$
\gamma_i=\frac{\operatorname{Tr}L_P-2\ell_i}{4}\ge0
\tag{318.15}
$$

给出时间一 Bloch 矩阵为 $P$ 的幺元齐次耗散。$O\in SO(3)$ 则由一个固定量子比特 Hamiltonian 的有限时间酉演化产生。先施加 $P$、再施加 $O$，复合恰为原 $T$；两个阶段都作用在完整的同一个 $M_2$ 上。这里的既有背景也可参见 Dávalos、Ziman 与 Pineda，*Divisibility of qubit channels and dynamical maps*（2019），[定理4](https://arxiv.org/abs/1812.11437v4)：可逆幺元微分可分通道具有酉前后处理的齐次 Pauli 因子。本段利用极分解把实现写成一个耗散阶段和一个酉阶段；本节的新任务结论是最优恢复的阶段数下界与精确达到。

由此每个内部预算最优恢复至多需要两个齐次阶段。而已证的不等半径近端点排除说明一个阶段不够，所以该范围内最少阶段数恰为二。这是对未知最优通道的实现结构约束，不是用其极分解预先求出了该通道。等半径的单阶段结论仍直接使用第293节的精确最优值与第290节的齐次生成元实现。证毕。

这里区分了同一二维系统上的两种实现要求：允许任意细分的 CPTP 演化，以及由一个不随演化参数改变的 GKSL 生成元产生的演化。既有文献已经区分这些通道类；本节的新增结论是当前不等半径恢复任务的全部近端点最优通道都落在前一类中，却无法由后一类达到。证明没有要求 $\mathcal L_j$ 有界，也没有把可能很大的 Hamiltonian 绕转分支排除在假设之外。

本节只排除齐次生成元的精确达到，没有证明它们的下确界与 $\widehat G_a(R)$ 存在严格正间隙，也没有证明齐次可实现集合在当前预算下闭。它不限制更大环境或记忆，也不对切换时长、生成元强度或控制能量作优化。两个阶段的达到是在本节定义的无附加速率限制下；若增加这些限制，阶段数结论不自动保留。

<a id="entry-986"></a>

## 追加锚（本行以下为增补区）

<a id="section-319"></a>

## 319. 齐次生成元的严格最优值差距与端点简单实谱

第318节排除了单个齐次生成元精确达到不等半径的近端点最优恢复。本节进一步排除用一列这样的生成元任意逼近同一个最优值。关键是当前模型端点矩阵的简单正实谱：它使最优恢复附近的实矩阵对数唯一，因而不需要假设所有齐次可实现通道构成闭集。

**定理 319.1（端点简单谱的全部例外）。** 对任意三个正半径，正角点规范下的端点矩阵 $M_*$ 有一个单重特征值 $1$，其余两个特征值位于 $(0,1)$。这两个特征值相等，当且仅当三个半径全相等；相等时它们均为 $1/2$。

证明。第309节已经证明主特征值及其余谱的范围。只需判定后两者能否重合。

先考虑第305节的奇异支撑分支。其另外两个特征值来自 $K/q$，而 $K$ 相似于对称正定矩阵 $H^{1/2}G_0H^{1/2}$。该二阶矩阵的非对角元严格为正，所以两个特征值不同。这一论证包括最后列约束恰好取等的分支边界。

现在考虑正定支撑分支，并使用第307、309节的单纯形参数。记

$$
n_i=\sqrt{w_i},\qquad X=\operatorname{diag}(x_1,x_2,x_3),
\qquad m=n^{\mathsf T}Xn,\qquad
\beta^2=n^{\mathsf T}X^2n,\qquad f=m-\beta^2>0.
\tag{319.1}
$$

将支撑矩阵除以 $A$，展开第307节的反射公式，得到

$$
\overline G
=nn^{\mathsf T}+\beta I
-\frac{(X+\beta I)nn^{\mathsf T}(X+\beta I)}{m+\beta},
\qquad M_*=\frac{\overline G X}{f}.
\tag{319.2}
$$

令 $z=X^{1/2}n$。则 $\|z\|_2^2=m$，而对称矩阵

$$
B=X^{1/2}\overline G X^{1/2}
=\beta X+zz^{\mathsf T}
-\frac{(X+\beta I)zz^{\mathsf T}(X+\beta I)}{m+\beta}
\tag{319.3}
$$

满足 $Bz=fz$，且 $B/f$ 与 $M_*$ 相似。这里 $Bz=fz$ 也直接来自第307节的 $\overline G Xn=fn$。

若三个 $x_i$ 互不相同，三个向量 $z,Xz,X^2z$ 线性无关：以它们为列的矩阵行列式，是非零的 $\prod_i z_i$ 乘以 Vandermonde 行列式。对这三个向量作实正交化，取 $q_1=z/\sqrt m$，得到正交基 $q_1,q_2,q_3$。在此基中，$X$ 是对称三对角矩阵，而且

$$
X_{12}\ne0,\qquad X_{23}\ne0,\qquad X_{13}=0.
\tag{319.4}
$$

第一、三个结论来自 $Xq_1\in\operatorname{span}(q_1,q_2)$ 及其不平行于 $q_1$。若 $X_{23}=0$，前两个基向量张成的平面就在 $X$ 下不变，从而包含 $z,Xz,X^2z$，违反线性无关。

式（319.3）中两个秩一修正的向量都位于 $\operatorname{span}(q_1,q_2)$。故 $B_{23}=\beta X_{23}\ne0$。与此同时 $Bq_1=fq_1$ 及 $B$ 对称，使其第一行、列与后两维解耦。后面的二阶对称块具有非零非对角元，所以其两个特征值不同。第309节使 $f$ 对应的特征值 $1$ 单重，因而三个特征值全部不同。

若两个单纯形坐标相等，例如 $x_1=x_2$，第307节的公共列范数条件

$$
x_i^2\left(1-2x_i+\frac{\beta^2}{w_i}\right)=c
\tag{319.5}
$$

迫使 $w_1=w_2$，也就是 $a_1=a_2$。于是可使用第306节的轴向正定支撑公式，写 $a_1=a_2=a$、$a_3=a/k$，其中 $0<k<k_0$。除特征值 $1$ 外，式（306.16）的两个特征值具有同一个正分母，分子分别为 $A_0t$ 和 $A_0\beta_0$，这里为避免与式（319.1）的归一化参数混淆，将该节的参数记为

$$
A_0=2+k^2,\qquad
\beta_0^2=\frac{2+k^2t^2}{2+k^2},\qquad
(3+2/k^2-k^2)t^2-2t-2=0.
\tag{319.6}
$$

两者相等要求 $t=\beta_0$，平方后便有 $t^2=1$，故 $t=1$。根方程随后给出 $k^4+k^2-2=0$，唯一正的 $k^2$ 为 $1$。所以只有等半径能出现重合。三个 $x_i$ 全相等时，式（319.5）直接迫使全部 $w_i$ 相等，也属于同一情况。最后，等半径的已知矩阵 $M_*=(I+nn^{\mathsf T})/2$ 确有谱 $1,1/2,1/2$。证毕。

**定义 319.2（单个齐次生成元的实际恢复值）。** 在第293节同一个正半径六态任务中，对 $R>0$ 定义

$$
\widehat H_a(R)
=\inf\left\{
e(\mathcal E,\mathcal D):
r(\mathcal E)\le R,\quad
\mathcal D\circ\mathcal E=e^{\mathcal L},\
\mathcal L\text{ 为量子比特 GKSL 生成元}
\right\}.
\tag{319.7}
$$

编码与解码均为完整 $M_2$ 上的实际 CPTP 通道。生成元允许依赖预算，不预先要求幺元；任意有限正演化时间吸收到 $\mathcal L$ 中。该可行类非空：选择足够小但严格正的退极化因子，再按第281节实现残差方向，就给出满足任意正预算的齐次半群方案。定义取下确界，不预先假设达到或闭性。

**定理 319.3（不等半径的严格齐次代价）。** 固定三个不全相等的正半径。存在 $\delta_0>0$，使对每个 $R=\eta(1-\delta)$、$0<\delta<\delta_0$，

$$
F_a^{(2)}(R)<\widehat G_a(R)<\widehat H_a(R).
\tag{319.8}
$$

此外，对所有正半径及每个 $0<R<\eta$，都有

$$
0\le\widehat H_a(R)-\widehat G_a(R)
\le
\frac{a_{\max}^2A}{R}\bigl(F_a^{(2)}(R)\bigr)^2.
\tag{319.9}
$$

因此固定不等半径时，在端点附近的严格正差距为 $O(\delta^2)$，且三个最优值共享一阶系数：

$$
F_a^{(2)}(\eta(1-\delta))
=\kappa_a\delta+o(\delta),\qquad
\widehat G_a(\eta(1-\delta))
=\kappa_a\delta+o(\delta),\qquad
\widehat H_a(\eta(1-\delta))
=\kappa_a\delta+o(\delta).
\tag{319.10}
$$

证明。先证明所有实际微分可分最优恢复在足够接近端点时，都具有四个不同的正实超算子特征值。

反设不存在这样的端点邻域，便可选择 $\delta_j\downarrow0$ 及各预算的一个最优通道 $\Phi_j$ 作为反例。它们由第293节幺元，写 Bloch 矩阵为 $T_j$。与第318节相同，正半径列误差控制及共同端点斜率使 $(I-T_j)/\delta_j$ 有界。取子列并作一个固定的角点符号共轭后，第296、298节给出

$$
\frac{I-T_j}{\delta_j}\longrightarrow M_*.
\tag{319.11}
$$

定理319.1使 $M_*$ 具有三个不同的正实特征值。实矩阵在具有简单实谱的矩阵附近仍有简单实谱：给每个极限特征值选互不相交且关于实轴对称的小圆盘，连续性使各圆盘恰含一个带重数计的特征值；实系数的共轭对称性迫使它为实数。故对充分大的 $j$，$(I-T_j)/\delta_j$ 的三个特征值均实正、彼此不同且有界。于是 $T_j$ 的三个特征值不同并落在 $(0,1)$。完整幺元保迹超算子在 Hermitian 基下为 $\operatorname{diag}(1,T_j)$，故有四个不同的正实特征值，矛盾。这证明所需的统一端点邻域；没有假设最优解随预算光滑变化。

缩小这个邻域，使第318节的单阶段排除也成立。固定其中一个 $R$，反设 $\widehat H_a(R)=\widehat G_a(R)$。取一列齐次可行的实际编码、解码对，其误差趋于这一共同值。有限维 CPTP 通道集合紧，故可选子列使两因子分别收敛。残差和恢复误差连续，复合通道也连续。第293节采用的微分可分类为闭包类，而每个齐次通道均属于其中，所以极限因子对仍可行，并达到 $\widehat G_a(R)$。记其复合为 $\Phi$。

刚证明的谱结论使 $\Phi$ 的完整实超算子矩阵具有四个不同的正实特征值。原序列的完整实超算子矩阵在足够靠后时也具有这一性质，包括原序列非幺元的情形。对任何这样的实矩阵 $E$，其实矩阵对数若存在便唯一。事实上，若 $e^L=E$，则 $L$ 与 $E$ 交换，所以 $L$ 保持 $E$ 的每个一维实特征空间；在该空间上的实特征值 $\ell$ 必须满足 $e^\ell=\lambda>0$，从而只能是 $\log\lambda$。因此该对数就是主矩阵对数。

原序列的每个 GKSL 生成元都是实矩阵对数，故从某项开始必为相应通道的主对数。这些主对数随矩阵连续，遂收敛到 $\log\Phi$。有限维 GKSL 生成元锥为闭集。这里直接使用标准生成元判据：Hermiticity 保持、$\mathcal L^*(I)=0$ 以及条件 Choi 半正定性

$$
(I-\omega)(\operatorname{id}\otimes\mathcal L)(\omega)(I-\omega)\succeq0,
\tag{319.12}
$$

其中 $\omega$ 为归一化最大纠缠态的秩一投影。前两项是线性闭条件，最后一项是连续线性映射下的半正定闭条件。该判据及实矩阵对数的分支背景见 Dávalos、Ziman 与 Pineda，*Divisibility of qubit channels and dynamical maps*（2019），[式（1）与第3.2节](https://arxiv.org/abs/1812.11437v4)。本节使用的是有限生成元的指数及其局部极限，不把该文含闭包的 $\mathcal C_L$ 定义混作“每个元素都有有限对数”。

所以 $\log\Phi$ 仍是 GKSL 生成元，$\Phi=e^{\log\Phi}$，与第318节排除的实际最优恢复相矛盾。由此 $\widehat H_a(R)>\widehat G_a(R)$。式（319.8）的另一严格不等式是第293节的既有结果。

最后，第297节对达到 $F_a^{(2)}(R)$ 的实际方案，已经构造了满足同一预算的单个幺元齐次半群，误差不超过

$$
F_a^{(2)}(R)+\frac{a_{\max}^2A}{R}\bigl(F_a^{(2)}(R)\bigr)^2.
$$

结合 $F_a^{(2)}(R)\le\widehat G_a(R)\le\widehat H_a(R)$，便得到式（319.9）。当 $R=\eta(1-\delta)$ 时，第296节使 $F_a^{(2)}(R)=O(\delta)$，而 $1/R$ 在端点邻域有界，故差距为 $O(\delta^2)$。两侧夹逼及共同斜率给出式（319.10）。证毕。

本节的严格差距逐个固定预算成立；它没有给出正的二阶差距系数、精确消失阶数或显式邻域宽度。等半径时，第293节的已知最优半群在端点附近使 $\widehat H_a=\widehat G_a$，所以严格不等式确实需要不等半径条件。简单谱处实对数唯一、主对数连续和条件完全正生成元判据均为既有工具；新增内容是当前全部不等半径端点族的谱判定，以及由此得到的实际恢复最优值分离。此处没有使用任何关于全体齐次可实现通道的全局闭性断言。

<a id="entry-988"></a>

## 追加锚（本行以下为增补区）

<a id="section-320"></a>

## 320. 三阶退极化修复与齐次恢复的共同二阶系数

第319节区分了微分可分最优值与单个齐次生成元的最优下确界。两者虽严格不同，本节证明它们在端点仍共享二阶系数。这里允许生成元随预算重新优化；第312、313节某个固定端点生成元的二阶损失，不能用来代表全部齐次生成元的最优损失。

向通道对数加入最小各向同性噪声，使其成为合法 Lindblad 生成元，是 Wolf、Eisert、Cubitt 与 Cirac 的既有构造，见 *Assessing Non-Markovian Quantum Dynamics*（2008），[“Measuring Markovianity”部分](https://arxiv.org/abs/0711.3172v2)。本节在当前幺元量子比特任务中使用这个方法，计算全部近端点最优恢复所需的噪声量，并同时控制原残差预算及恢复误差。

**定理 320.1（实际最优恢复的最小标量生成元修复）。** 固定三个不全相等的正半径。使用第298、301节的正角点端点矩阵 $M_*=S_*-\Omega_*$，记 $d_3$ 为 $S_*$ 的简单最大特征值，$v_*$ 为相应单位特征向量，并令

$$
\Xi_a=(\Omega_*v_*)^{\mathsf T}(d_3I-S_*)(\Omega_*v_*)>0.
\tag{320.1}
$$

对充分小的 $\delta>0$，取任何达到 $\widehat G_a(\eta(1-\delta))$ 的实际恢复，其 Bloch 矩阵记为 $T_\delta$。定义主矩阵对数及其对称部分

$$
K_\delta=-\log T_\delta,\qquad
S_\delta^{\log}=\frac{K_\delta+K_\delta^{\mathsf T}}2,
\tag{320.2}
$$

并定义非负数

$$
\alpha_\delta=
\max\left\{0,\,
2\lambda_{\max}(S_\delta^{\log})
-\operatorname{Tr}S_\delta^{\log}\right\}.
\tag{320.3}
$$

则

$$
\alpha_\delta=\frac{\Xi_a}{6}\delta^3+o(\delta^3)>0.
\tag{320.4}
$$

此渐近式对最优恢复的选择一致成立。它是使 $K_\delta+\alpha I$ 满足幺元 GKSL 衰减生成矩阵条件的最小非负标量 $\alpha$。因此

$$
T_\delta^{\rm hom}=e^{-\alpha_\delta}T_\delta
=\exp\bigl(-(K_\delta+\alpha_\delta I)\bigr)
\tag{320.5}
$$

由单个有限齐次生成元实现，且可由同一二维任务的实际编码、解码在原预算内实现。其误差满足

$$
0\le e(T_\delta^{\rm hom})-\widehat G_a(\eta(1-\delta))
\le\frac{a_{\max}}2(1-e^{-\alpha_\delta})\|T_\delta\|_{\rm op}
\le\frac{a_{\max}\Xi_a}{12}\delta^3+o(\delta^3).
\tag{320.6}
$$

证明。第293、315节保证每个内部预算的实际最优恢复幺元、可逆、正行列式，并位于微分可分边界：

$$
s_3(T_\delta)^2=\det T_\delta.
\tag{320.7}
$$

第296、298节还保证，当 $\delta\downarrow0$ 时，$(I-T_\delta)/\delta$ 有界，其任何收敛子列经角点符号共轭后均趋于唯一 $M_*$。于是 $T_\delta$ 一致趋于 $I$，主实矩阵对数存在，且

$$
K_\delta=(I-T_\delta)+O(\delta^2).
\tag{320.8}
$$

因此 $K_\delta/\delta$ 具有相同的端点极限。下面先在正角点规范附近推导局部展开，再说明其对全部最优选择的一致性。

取任意足够接近 $M_*$ 的实矩阵 $M=S-\Omega$，其中 $S$ 对称、$\Omega$ 反对称。不要求这个暂时的 $M$ 本身满足 GKSL 锥条件。令 $d$ 为 $S$ 的最大特征值，$v$ 为其单位特征向量。由于 $S_*$ 的最大特征值简单，在足够小的邻域内 $d$ 仍简单，且

$$
D=dI-S\succeq0,\qquad \ker D=\mathbb Rv,\qquad
\Omega v\ne0.
\tag{320.9}
$$

最后一项使用第314节的 $\Xi_a>0$ 及连续性。于是 $B=D+\Omega=dI-M$ 的 Hermitian 部分为 $D$，而 $D+\Omega D\Omega^{\mathsf T}\succ0$。这正是第314节使用的 hypocoercivity index 为一的条件。

直接应用 Achleitner、Arnold 与 Carlen，*The hypocoercivity index for the short time behavior of linear time-invariant ODE systems*，[定理2.7(b)、式（2.9）](https://arxiv.org/abs/2109.10784v5)，得到当 $t\downarrow0$ 时

$$
\|e^{-tB}\|_{\rm op}
=1-\frac{\Xi(M)}{12}t^3+O(t^4),
\qquad
\Xi(M)=(\Omega v)^{\mathsf T}(dI-S)(\Omega v).
\tag{320.10}
$$

这里使用实矩阵在实或复 Euclidean 空间上的相同算子范数；单位核向量的复相位不改变系数。这是既有短时范数定理的直接应用，不是新证明的一般三阶范数规律。

本节还需要该余项对变化中的 $M$ 一致。该点可由简单特征值的标准解析扰动保证。矩阵

$$
H(t,M)=\frac{e^{tM^{\mathsf T}}e^{tM}-I}{2t}
\tag{320.11}
$$

在 $t=0$ 解析延拓为 $S$。其在 $t=0$ 的最大特征值 $d$ 简单，故在 $M_*$ 的一个固定小邻域内，相应特征值分支对 $(t,M)$ 共同解析。对正的小 $t$，这一分支仍为 $H(t,M)$ 的最大特征值，并给出 $\|e^{tM}\|_{\rm op}$ 的平方根表达。因而其对数具有在紧邻域内一致的 Taylor 余项。结合式（320.10），

$$
\log\|e^{tM}\|_{\rm op}
=td-\frac{\Xi(M)}{12}t^3+O(t^4)
\tag{320.12}
$$

对该邻域内的 $M$ 一致成立。这里只用 $t>0$ 的最大奇异值分支；不要求负 $t$ 时最大分支仍相同。

现在对任一已转到正角点极限的最优子列，令 $M=K_\delta/\delta$、$t=\delta$。由 $T_\delta=e^{-K_\delta}$ 及式（320.7），

$$
2\log\|e^{K_\delta}\|_{\rm op}
=\operatorname{Tr}K_\delta.
\tag{320.13}
$$

记 $S=\operatorname{sym}(K_\delta/\delta)$、$d=\lambda_{\max}(S)$。式（320.12）代入后得到

$$
\begin{aligned}
\lambda_{\min}\bigl(\mathcal C(S_\delta^{\log})\bigr)
&=\operatorname{Tr}S_\delta^{\log}
-2\lambda_{\max}(S_\delta^{\log})\\
&=-\frac{\Xi(K_\delta/\delta)}6\delta^3+O(\delta^4)\\
&=-\frac{\Xi_a}6\delta^3+o(\delta^3).
\end{aligned}
\tag{320.14}
$$

这里 $\mathcal C(S)=(\operatorname{Tr}S)I-2S$。符号共轭保留 $\Xi$、迹与对称特征值；角点符号类只有有限个。若式（320.14）对最优选择不一致，就可选一列违反一致性的最优解，再取端点收敛子列并作一个固定符号共轭，前面的局部一致展开即产生矛盾。所以式（320.14）对全部最优选择一致。由于 $\Xi_a>0$，它在充分小的 $\delta$ 上为负，证明式（320.4）。

剩下验证修复的合法性与同一预算。对任意对称矩阵 $S$，

$$
\mathcal C(S+\alpha I)=\mathcal C(S)+\alpha I.
\tag{320.15}
$$

故式（320.3）恰为使此矩阵半正定的最小非负标量。第296节的标准幺元生成元构造随后给出衰减矩阵 $K_\delta+\alpha_\delta I$ 的 GKSL 半群；其反对称部分保留原 Hamiltonian。这里的锥条件也保证对称衰减部分非负，因为它的每个特征值等于另外两个锥特征值之和的一半。因此不需要另加一个独立正性前提。

式（320.5）便是该半群的时间一矩阵。又由残差的正齐次性，

$$
r_*(T_\delta^{\rm hom})
=e^{-\alpha_\delta}r_*(T_\delta)
\le r_*(T_\delta)\le\eta(1-\delta).
\tag{320.16}
$$

最后一个不等式来自第281节对实际编码、解码的共同残差支配。对修复后的同一个矩阵再用该节的实际二维实现，就同时得到原预算内的残差和误差 $e(T_\delta^{\rm hom})$。逐列反三角不等式给出

$$
e(T_\delta^{\rm hom})-e(T_\delta)
\le \frac{a_{\max}}2
\|T_\delta^{\rm hom}-T_\delta\|_{\rm op}
=\frac{a_{\max}}2(1-e^{-\alpha_\delta})\|T_\delta\|_{\rm op}.
$$

原最优通道幺元，故 $\|T_\delta\|_{\rm op}\le1$。修复后属于微分可分类且仍在同一预算内，故其误差不能低于原最优值。再代入式（320.4），便得式（320.6）。证毕。

**推论 320.2（齐次与微分可分恢复共享二阶最优值）。** 对固定不等正半径，当 $\delta>0$ 充分小时，

$$
0<
\widehat H_a(\eta(1-\delta))-\widehat G_a(\eta(1-\delta))
\le\frac{a_{\max}\Xi_a}{12}\delta^3+o(\delta^3).
\tag{320.17}
$$

因此

$$
\widehat H_a(\eta(1-\delta))
=\kappa_a\delta+(\Gamma_a+\Theta_a)\delta^2+o(\delta^2).
\tag{320.18}
$$

证明。严格下界是第319节。定义319.2的下确界不大于定理320.1构造的同预算实际齐次恢复误差，故得到式（320.17）。再使用第300节对实际微分可分最优值的二阶展开，得到式（320.18）。证毕。

这给出两种近端点限制的不同作用。要求恢复微分可分，相对无限制最优值增加第300节的正二阶代价 $\Theta_a\delta^2$；进一步要求由单个齐次生成元实现，仍产生严格正代价，但可以压到三阶上界，因此不改变二阶系数。固定使用端点生成元则没有这种保证，其二阶损失已经由第312、313节分类。

本节的“最小”只针对在给定主衰减对数上增加标量 $\alpha I$ 的修复方式，不是全体生成元修正或通道误差的最优性。式（320.17）也没有给出正的三阶下界，不能将其读为差距必定恰为三阶或系数已经求出；$\widehat H_a$ 的下确界是否达到仍未在这里判定。等半径已有第293节的精确齐次最优恢复，端点附近两类值相等，无需本节的正修复量。

<a id="entry-990"></a>

## 追加锚（本行以下为增补区）

<a id="section-321"></a>

## 321. 齐次最优恢复的近端点达到与生成元边界

定义319.2把齐次恢复值写成下确界，因为一般齐次可实现通道不能直接当作闭集合。本节证明：对于当前不等半径模型，端点附近的下确界实际上达到。证明只在由任务误差限定的邻域中恢复闭性，不需要对所有通道作全局闭性假设。

**定理 321.1（齐次类的幺元约化与局部达到）。** 对任意正半径及 $R>0$，定义319.2的实际齐次恢复值等于

$$
\widehat H_a(R)
=\inf\left\{
e(T):r_*(T)\le R,\quad
T=e^{-K},\
\mathcal C(\operatorname{sym}K)\succeq0,\
K\in\mathbb R^{3\times3}
\right\}.
\tag{321.1}
$$

式中矩阵代表完整量子比特上的幺元通道，$\mathcal C(S)=(\operatorname{Tr}S)I-2S$，反对称部分编码任意有限 Hamiltonian。若某个实际方案达到这个值，其复合恢复必幺元。

固定三个不全相等的正半径，则存在 $\delta_0>0$，使每个 $R=\eta(1-\delta)$、$0<\delta<\delta_0$ 的 $\widehat H_a(R)$ 都由一对实际二维 CPTP 编码、解码达到。每个这样的最优恢复都严格收缩，完整超算子具有四个不同的正实特征值；其唯一实对数为一个有限幺元 GKSL 生成元。

证明。先直接复用第293节的去平移映射 $\mathfrak U$。它在量子比特 CPTP 通道上连续，保持恒等与复合。故对任何齐次 CPTP 半群 $\Phi_t=e^{t\mathcal L}$，

$$
\mathfrak U(\Phi_{s+t})
=\mathfrak U(\Phi_s)\mathfrak U(\Phi_t),\qquad
\mathfrak U(\Phi_0)=\mathrm{id}.
\tag{321.2}
$$

去平移后的通道本身就是连续 CPTP 半群。若原仿射生成矩阵的线性部分为 $-K$，则这个幺元半群的 Bloch 矩阵为 $e^{-tK}$。因此去平移保持“单个有限齐次生成元”这一要求。这里依赖第293节特有的复合恒等式，不使用一般凸平均保持齐次可实现性的断言；连续有限维 CPTP 半群的 GKSL 表征为标准背景。

第281、293节的同一方案支配随后给出：该幺元恢复可由实际编码、解码在不增加残差与误差的条件下实现。若原复合平移为 $h$，还保留

$$
e(T)^2\le e(\mathcal D\mathcal E)^2-\frac{\|h\|_2^2}{4}.
\tag{321.3}
$$

标准幺元量子比特生成元条件恰为式（321.1）的锥条件，反向实际实现仍由第281节给出。因此两个下确界相等；如果一个达到者有 $h\ne0$，式（321.3）给出同预算严格改进，矛盾。故每个实际达到者幺元。

下面建立一个略强于“最优解有简单谱”的局部事实。固定任意有限常数 $C$。考虑所有满足

$$
T\text{ 为幺元 CPTP 矩阵},\qquad
r_*(T)\le\eta(1-\delta),\qquad
e(T)\le\kappa_a\delta+C\delta^2
\tag{321.4}
$$

的矩阵，暂时不要求齐次或微分可分。对于固定不等半径，当 $\delta>0$ 足够小时，每个这样的矩阵都严格收缩，并有三个不同的正实 Bloch 特征值。

为证明这一点，反设可选 $\delta_j\downarrow0$ 和式（321.4）中的反例 $T_j$。正半径列误差控制使

$$
M_j=\frac{I-T_j}{\delta_j}
\tag{321.5}
$$

有界。取极限子列 $M=S-\Omega$。第296节的一阶 Choi 条件与残差展开给出端点耗散锥和 $g(S)\ge A$。另一方面，式（321.4）使

$$
\frac12h_a(S,\Omega)\le\kappa_a.
$$

端点优化的齐次下界则给出

$$
\frac12h_a(S,\Omega)\ge
\kappa_a\frac{g(S)}A\ge\kappa_a.
\tag{321.6}
$$

因此全部取等。选取一个固定角点符号共轭后，第298节的唯一性使 $M_j\to M_*$。第298节的 $S_*\succ0$ 保证 $T_j$ 最终严格收缩；第319节的简单正实谱及其稳定性证明使 $T_j$ 最终具有三个不同的正实特征值，且全部小于一。这与反例的选择矛盾，证明局部事实。这个论证对式（321.4）中的全部矩阵成立，包括尚未证明齐次可实现的极限矩阵。

第297节的齐次替换界与第300节的端点展开保证，可选一个固定 $C_0>0$ 及端点邻域，使

$$
\widehat H_a(\eta(1-\delta))
\le\kappa_a\delta+C_0\delta^2.
\tag{321.7}
$$

也可直接使用第320节更强的界；这里仅需二阶控制。取 $C>C_0$，并把邻域缩小到上述局部事实适用的范围。现在固定其中一个 $\delta$，从式（321.1）选一个趋近下确界的幺元齐次矩阵序列。丢弃有限前缀后，每个矩阵都满足式（321.4）。

幺元 CPTP 矩阵集合紧，故可取子列收敛到 $T$。残差与误差连续，使 $r_*(T)\le R$、$e(T)=\widehat H_a(R)$，且 $T$ 本身仍满足式（321.4）。局部事实使其完整矩阵 $\operatorname{diag}(1,T)$ 有四个不同的正实特征值。与第319节相同，序列充分靠后的每个实生成元对数只能是主对数，并收敛到极限的主对数。也可以只在幺元三阶 Bloch 矩阵上作这一步：每个实对数保持三个一维实特征空间，在各空间上只能取对应正特征值的实对数。

写 $K=-\log T$。因为每个序列成员的主衰减对数满足

$$
\mathcal C(\operatorname{sym}K_j)\succeq0,
$$

而该锥闭，极限 $K$ 也满足这一条件。所以 $T=e^{-K}$ 仍为齐次可实现通道，且达到式（321.1）的下确界。第281节把它实现为同预算的实际因子对。所有实际达到者幺元的结论已经证明；它们也满足式（321.4），故具有同样的收缩与简单谱性质。证毕。

**定理 321.2（齐次最优者接触生成元锥边界）。** 在定理321.1的不等半径近端点区间，取任何实际齐次最优恢复的 Bloch 矩阵 $T_\delta$，并记唯一主衰减对数为 $K_\delta=-\log T_\delta$。则

$$
\mathcal C(\operatorname{sym}K_\delta)\succeq0,\qquad
\operatorname{rank}\mathcal C(\operatorname{sym}K_\delta)=2.
\tag{321.8}
$$

另一方面，它的通道奇异值严格位于微分可分条件的内部：

$$
\log\frac{s_3(T_\delta)^2}{\det T_\delta}
=\frac{\Xi_a}{6}\delta^3+o(\delta^3)>0,
\tag{321.9}
$$

其中 $\Xi_a>0$ 是式（320.1）的模型常数，渐近式对齐次最优者的选择一致成立。

证明。先排除生成元锥的内部。若某个最优者满足 $\mathcal C(\operatorname{sym}K_\delta)\succ0$，由主对数的局部连续性，$T_\delta$ 的一个完整实矩阵邻域中的每个 $T'$ 都具有实主衰减对数 $K'$，且 $\mathcal C(\operatorname{sym}K')\succ0$。标准生成元构造使这个邻域中的全部矩阵都是幺元齐次 CPTP 通道。

第285节的局部平板投影改进，以及第315节对同一局部论证的使用，正是排除在这种完整开邻域中取得内部预算最优。具体而言，先固定达到残差的方向，若误差严格高于该方向的列投影下界，就沿投影作任意小的严格改进；若达到下界但并非所有列活跃，就微调方向并连续修正各列，仍在任意指定的小邻域内严格改进；若所有列活跃，则唯一投影候选违反完全正性。该论证只要求小邻域内的矩阵仍为可用通道，故也适用于这里的齐次邻域。于是在 $0<R<\eta$ 下产生同预算的严格齐次改进，矛盾。因此至少一个锥特征值为零。

第320节及定理321.1的界使齐次最优者都满足式（321.4）。沿任意趋近端点的选择，定理321.1的紧性论证于是给出：在子列及固定角点符号共轭后，

$$
\frac{K_\delta}{\delta}\longrightarrow M_*.
\tag{321.10}
$$

第298节使 $\mathcal C(S_*)$ 恰有两个严格正特征值。故在足够小的统一邻域内，$\mathcal C(\operatorname{sym}K_\delta)$ 至少有两个严格正特征值；结合已经证明的边界接触，得到式（321.8）。

最后直接使用第320节从既有 hypocoercivity 定理得到的局部一致范数展开。写 $M=K_\delta/\delta$、$S=\operatorname{sym}M$、$d=\lambda_{\max}(S)$。生成元边界等价于 $\operatorname{Tr}S=2d$，于是

$$
\begin{aligned}
\log\frac{s_3(T_\delta)^2}{\det T_\delta}
&=\operatorname{Tr}K_\delta
  -2\log\|e^{K_\delta}\|_{\rm op}\\
&=\delta(\operatorname{Tr}S-2d)
  +\frac{\Xi(M)}6\delta^3+O(\delta^4)\\
&=\frac{\Xi_a}{6}\delta^3+o(\delta^3).
\end{aligned}
\tag{321.11}
$$

$\Xi_a>0$ 给出严格内部性。局部展开一致、端点极限唯一至有限符号共轭且 $\Xi$ 在共轭下不变，故同第320节的子列反证一样，这个渐近式对全部最优选择一致。证毕。

第315节的微分可分最优者位于通道条件 $s_3^2=\det T$ 的边界；本节的齐次最优者则位于生成元锥的边界，并在通道条件上留下三阶正余量。这是同一恢复任务的两种不同约束面，不能只比较某个固定半群就把二者等同。结合第319、320节，近端点的齐次最优值现在确由实际方案达到，与微分可分最优值严格不同，却共享二阶系数。

本节没有给出所有正预算上的达到定理、一般最优通道的显式矩阵，或两类误差差距的精确三阶系数。式（321.9）量化的是通道奇异值的可分性余量，不能直接当作恢复误差差距。近端点达到来自任务误差诱导的简单谱邻域，不把一般齐次可实现集合宣称为闭。

<a id="entry-992"></a>

## 追加锚（本行以下为增补区）

<a id="section-322"></a>

## 322. 单个齐次生成元的精确三阶最优代价

第319至321节证明了近端点的齐次最优值达到，并且严格高于微分可分最优值，但差距只出现在二阶之后。本节计算这一差距的精确首项。关键是两类约束在生成元坐标中相隔三阶小量，而端点的对偶乘子把这个约束差转换为最优恢复误差。

**定理 322.1（精确三阶齐次代价）。** 固定三个不全相等的正半径。沿用第298、300节的唯一正角点端点解与对偶参数 $D_a>0$、$Z_*=\lambda vv^{\mathsf T}$、$\zeta_a=\lambda/(2D_a)>0$，并令 $\Xi_a>0$ 为式（320.1）的系数。则

$$
\lim_{\delta\downarrow0}
\frac{
\widehat H_a(\eta(1-\delta))
-\widehat G_a(\eta(1-\delta))
}{\delta^3}
=
\frac{\zeta_a\Xi_a}{6}
=
\frac{\lambda\Xi_a}{12D_a}
>0.
\tag{322.1}
$$

结论包含奇异支撑分支及其最后列刚好活跃、但乘子为零的临界点。它不要求有限预算最优矩阵唯一或随预算可微，也不要求归一化最优矩阵以 $O(\delta)$ 的速度趋于端点。等半径时，两类值在已知端点区间相等，所以相应差距为零。

证明。以下固定不等半径，并在正角点规范下工作。写归一化衰减对数为 $M=S-\Omega$，相应通道为 $T=e^{-\delta M}$。在 $M_*$ 的一个固定小邻域内，$S$ 保持正定且最大特征值简单，各列 $Me_i$ 非零，正角点在残差公式中唯一活跃。这里最后一个条件由第298节的严格角点间隙及一致的一阶展开保证。

先把有限预算问题写成共同的光滑局部形式。定义

$$
f_{\delta,i}(M)
=\frac{a_i}{2}
\left\|\frac{I-e^{-\delta M}}{\delta}e_i\right\|_2,
\qquad
g_\delta(M)
=\frac{\|e^{\delta M^{\mathsf T}}b\|_2^2-A/(1-\delta)^2}{2\delta},
\tag{322.2}
$$

并在 $\delta=0$ 取解析延拓

$$
f_{0,i}(M)=\frac{a_i}{2}\|Me_i\|_2,\qquad
g_0(M)=b^{\mathsf T}Sb-A.
\tag{322.3}
$$

范数的自变量在各列上非零，所以这些函数在所选邻域光滑。令

$$
c(M)=\operatorname{Tr}S-2\lambda_{\max}(S).
\tag{322.4}
$$

第320节的共同解析范数分支给出一个同样光滑的函数

$$
q_\delta(M)
=\frac1\delta
\log\frac{s_3(e^{-\delta M})^2}{\det(e^{-\delta M})}
-c(M)
=\frac{\Xi(M)}6\delta^2+O(\delta^3),
\tag{322.5}
$$

其余项对 $M$ 一致。由于 $\Xi(M_*)=\Xi_a>0$，可缩小邻域，使 $q_\delta(M)>0$ 对所有充分小的正 $\delta$ 成立。

对 $\theta\in[0,1]$，考虑以 $z$ 为目标的局部问题

$$
\min z,\qquad
f_{\delta,i}(M)\le z\ (i=1,2,3),\qquad
g_\delta(M)\ge0,\qquad
c(M)+\theta q_\delta(M)\ge0.
\tag{322.6}
$$

$\theta=0$ 是齐次生成元条件，$\theta=1$ 是微分可分条件。由于 $q_\delta>0$，可行类随 $\theta$ 增大而放宽，并且每个中间可行矩阵都满足微分可分条件。它确实是 CPTP 通道：邻域内 $S\succ0$ 使 $e^{-\delta M}$ 严格收缩，行列式为正；再由 $s_1s_2\le s_3$，标准 Pauli 条件中最小概率分子满足

$$
1-s_1-s_2+s_3\ge(1-s_1)(1-s_2)\ge0,
$$

其余概率也由奇异值排序与 $s_1<1$ 非负。第281节使每个这样的同一矩阵同时实现残差和恢复误差。正角点公式使 $g_\delta\ge0$ 恰为原残差预算，而实际误差为 $\delta\max_i f_{\delta,i}$。

为使局部最小值有固定紧载体，先把 $M$ 限制在足够小的闭球 $\overline B(M_*,\varepsilon)$，把 $z$ 限制在 $[\kappa_a-\varepsilon,\kappa_a+\varepsilon]$，记最小值为 $V_\delta(\theta)$。第321节的齐次达到与端点定位给出球内的齐次可行点；由 $q_\delta>0$，同一点对全部 $\theta\in[0,1]$ 都可行，故这些问题均非空。每个局部最优值都介于实际微分可分值除以 $\delta$ 与齐次值除以 $\delta$ 之间，因而趋于 $\kappa_a$。

更具体地，任何 $\delta_j\downarrow0$、$\theta_j\in[0,1]$ 的最优序列都可取子列收敛。极限满足第296节的端点约束及最优目标；第298节的唯一性使其只能是 $(M_*,\kappa_a)$。因此收敛对全部 $\theta$ 与最优选择一致，固定球和 $z$ 区间的边界最终都不活跃。两端的全局实际最优者经符号规范后也位于该球内部，故

$$
\delta V_\delta(0)=\widehat H_a(\eta(1-\delta)),
\qquad
\delta V_\delta(1)=\widehat G_a(\eta(1-\delta)).
\tag{322.7}
$$

下面核对局部参数变化所需的梯度独立性，而不假定最优解光滑。令

$$
I_*=\{i:f_{0,i}(M_*)=\kappa_a\},\qquad
B=bb^{\mathsf T},\qquad C_v=I-2vv^{\mathsf T},
\qquad G=B+\lambda C_v.
\tag{322.8}
$$

对每个支撑列 $Ge_i\ne0$，原问题列支撑取等，使 $M_*e_i$ 与 $Ge_i$ 同向。因此 $f_{0,i}$ 在端点的矩阵梯度为

$$
A_i=\frac{a_i}{2\|Ge_i\|_2}(Ge_i)e_i^{\mathsf T}.
\tag{322.9}
$$

全部非零支撑列都属于 $I_*$。若 $G$ 奇异，第305节说明它恰有一个零行列 $k$；该列是否属于 $I_*$ 取决于最后列是否饱和。若属于，其实际梯度为 $A_k=a_k(M_*e_k)e_k^{\mathsf T}/(2\|M_*e_k\|_2)$，只在第 $k$ 列可能非零。又因 $(M_*)_{kk}=1$，其第 $k$ 行第 $k$ 列非零。

我们证明，在变量 $(M,z)$ 上，所有 $i\in I_*$ 的梯度 $(A_i,-1)$，连同 $(B,0)$ 与 $(C_v,0)$，线性无关。设有线性关系

$$
\sum_{i\in I_*}\tau_i(A_i,-1)
+\beta_0(B,0)+\gamma_0(C_v,0)=0.
\tag{322.10}
$$

$z$ 分量给出 $\sum_i\tau_i=0$。

若 $G\succ0$，三列全支撑且活跃。令 $d_i=\tau_i a_i/(2\|Ge_i\|_2)$，矩阵部分化为

$$
G\operatorname{diag}(d_i+\gamma_0/\lambda)
+(\beta_0-\gamma_0/\lambda)bb^{\mathsf T}=0.
\tag{322.11}
$$

左乘 $G^{-1}$。因为 $b$ 的各分量严格正且 $G^{-1}b\ne0$，一个非零的 $(G^{-1}b)b^{\mathsf T}$ 不可能是对角矩阵：取其非零行，再取不同的列，即有非零非对角元。所以 $\beta_0=\gamma_0/\lambda$，进而所有 $d_i=-\gamma_0/\lambda$。若 $\gamma_0\ne0$，全部 $\tau_i$ 具有相同严格符号，与其和为零矛盾。故所有系数均零。

若 $G$ 奇异，查看第 $k$ 行。两个支撑列的梯度在这一行都是零，且 $C_v$ 的第 $k$ 行为 $-B$ 的第 $k$ 行除以 $\lambda$。先查看不同于 $k$ 的列，就得 $\beta_0=\gamma_0/\lambda$。若零支撑列也活跃，再查看第 $k$ 列，由 $(A_k)_{kk}\ne0$ 得 $\tau_k=0$。剩下在两个支撑坐标的正定 $G$ 子块上运用式（322.11），使两个支撑系数仍具有同一严格符号，除非 $\gamma_0=0$。它们之和为零，遂再次得到全部系数为零。这个证明包括零乘子活跃列，未使用严格互补性。

现在固定完整的潜在活跃指标集 $I_*$，定义不等式向量

$$
F_{\delta,\theta}(M,z)
=
\left(
(f_{\delta,i}(M)-z)_{i\in I_*},
-g_\delta(M),
-c(M)-\theta q_\delta(M)
\right).
\tag{322.12}
$$

所有未列入 $I_*$ 的列约束在端点严格不等，并在所选小邻域内保持余量。刚证出的线性无关性说明，$J_{\delta,\theta}=D_{(M,z)}F_{\delta,\theta}$ 在一个固定小邻域内保持满行秩；其最小奇异值有统一正下界，适用于全部 $\theta\in[0,1]$ 及充分小的 $\delta$。任何实际活跃约束集都是这个固定集合的子集，所以也满足梯度独立条件。

有限维 KKT 定理因而适用于每个局部最优者。将不活跃约束的乘子补零，记完整乘子为 $\Lambda_{\delta,\theta}$，便有

$$
\nabla z+J_{\delta,\theta}^{\mathsf T}\Lambda_{\delta,\theta}=0,
\qquad
\Lambda_{\delta,\theta}
=-(J_{\delta,\theta}J_{\delta,\theta}^{\mathsf T})^{-1}
J_{\delta,\theta}\nabla z.
\tag{322.13}
$$

满行秩使完整乘子唯一且连续受控。端点乘子明确为

$$
\pi_i=\frac{b_i\|Ge_i\|_2}{D_a},\qquad
\mu_a=\frac1{2D_a},\qquad
\zeta_a=\frac{\lambda}{2D_a},
\tag{322.14}
$$

其中零支撑列取 $\pi_i=0$。的确，$\sum_i\pi_i=1$，且式（322.9）给出

$$
\sum_i\pi_i A_i
=\frac{G}{2D_a}
=\mu_a B+\zeta_a C_v.
\tag{322.15}
$$

这核对了全部归一化。结合最优者一致趋于端点及式（322.13），最后一个约束乘子一致满足

$$
\zeta_{\delta,\theta}\longrightarrow\zeta_a.
\tag{322.16}
$$

剩下把乘子转换为值差。这里给出具体的可行点运输，避免把约束最优值的可微性当作前提。从任意 $\theta_0$ 的一个最优点 $W_0=(M_0,z_0)$ 出发，解局部微分方程

$$
\frac{dW}{d\theta}
=
-J_{\delta,\theta}(W)^{\mathsf T}
\left[J_{\delta,\theta}(W)
J_{\delta,\theta}(W)^{\mathsf T}\right]^{-1}
\partial_\theta F_{\delta,\theta}(W).
\tag{322.17}
$$

这是标准满行秩约束的右逆运输。链式法则给出

$$
\frac{d}{d\theta}F_{\delta,\theta}(W(\theta))=0.
\tag{322.18}
$$

因此固定列表中每个约束的值，包括原本严格为负的值，均被保留。列表外的约束原有统一余量，仍保持可行。

式（322.5）使 $\partial_\theta F$ 只有最后一个分量 $-q_\delta=O(\delta^2)$。统一满秩界于是给出 $\|W'(\theta)\|\le C\delta^2$。该向量场在满秩的固定邻域内光滑，因而局部 Lipschitz。所有最优点已一致进入更小的内邻域，其到原邻域边界有固定余量；整个参数区间上的总位移至多为 $C\delta^2$。所以对充分小的 $\delta$，路径不能在到达参数端点前离开原邻域，标准常微分方程的存在延拓保证它在整个 $[0,1]$ 上存在。这不要求路径上的点继续最优；它只运输可行性。

从两个参数处的最优点分别运输到对方，得到

$$
|V_\delta(\theta_1)-V_\delta(\theta_0)|
\le C\delta^2|\theta_1-\theta_0|.
\tag{322.19}
$$

所以 $V_\delta$ 为 Lipschitz 函数，绝对连续且几乎处处可微。固定一个可微参数 $\theta$，从其任意最优点作式（322.17）的双向可行路径。该路径的目标值在初始点的导数由 KKT 平稳性给出

$$
z'(\theta)
=
\Lambda_{\delta,\theta}^{\mathsf T}
\partial_\theta F_{\delta,\theta}
=
-\zeta_{\delta,\theta}q_\delta(M).
\tag{322.20}
$$

因为两侧邻近参数的最优值都不超过这条可行路径的目标值，分别取正、负增量后除以增量，得到

$$
V_\delta'(\theta)
=-\zeta_{\delta,\theta}q_\delta(M)
\quad\text{几乎处处}.
\tag{322.21}
$$

这里没有选择可微的最优解分支。若最优点不唯一，任取一个的双向比较在值函数可微处都给出同一个导数。

由式（322.5）、（322.16）及全部最优者的一致端点定位，

$$
V_\delta'(\theta)
=-\frac{\zeta_a\Xi_a}{6}\delta^2+o(\delta^2),
\tag{322.22}
$$

余项对这些几乎处处的参数及最优选择一致。绝对连续性允许积分，得到

$$
V_\delta(0)-V_\delta(1)
=\frac{\zeta_a\Xi_a}{6}\delta^2+o(\delta^2).
\tag{322.23}
$$

传播子范数的 $\Xi/12$ 系数，经对数奇异值条件中的因子二变成约束差 $\Xi/6$；乘子 $\zeta_a$ 再把它转换为归一化最优值差。最后乘以实际误差的外部因子 $\delta$，并使用式（322.7），便得定理。等半径结论直接由第293节的已知精确齐次最优通道给出。证毕。

本节的 KKT 条件、满秩右逆、常微分方程运输与一维 Lipschitz 函数基本定理都是既有分析工具。新增任务内容是全部端点分支上的约束梯度独立性，以及将第320节的三阶生成元缺口转成精确最优误差系数。最优点的活跃集合可以变化，零乘子也被保留；运输的是固定潜在活跃约束的数值，不是预先假设最优点组成一条光滑曲线。

由此，同一模型的三类最优恢复出现不同阶的严格代价：无限制恢复到微分可分恢复的差是第300节的 $\Theta_a\delta^2+o(\delta^2)$；从微分可分恢复到单个齐次生成元的差是本节的 $\lambda\Xi_a\delta^3/(12D_a)+o(\delta^3)$。后一个系数在每个固定不等半径模型上严格为正，但本节不据此宣称退化半径上的统一常数或统一邻域，也没有求出整条有限预算曲线。

<a id="entry-994"></a>

## 追加锚（本行以下为增补区）

<a id="section-323"></a>

## 323. 接近等半径时的旋转响应与三阶代价消失率

第322节的三阶代价对每个固定不等半径模型严格为正，而等半径模型的这一差距为零。本节计算它接近对称模型时的消失率。这里先取预算端点极限，再让半径趋于相等；这两个极限的顺序属于结论的一部分。

**定理 323.1（对称点附近的端点响应）。** 固定 $0<a<1$ 与非零向量 $u\in\mathbb R^3$，满足 $u_1+u_2+u_3=0$。令

$$
a_i(\varepsilon)=\frac{a}{1+\varepsilon u_i},
\qquad
n_0=\frac1{\sqrt3}(1,1,1)^{\mathsf T},
\qquad P=n_0n_0^{\mathsf T},\qquad U=\operatorname{diag}(u).
\tag{323.1}
$$

当实数 $\varepsilon$ 的绝对值充分小时，这些半径属于 $(0,1)$，模型位于第307节的正定支撑分支。其正角点规范下的端点最优矩阵与旋转部分满足

$$
M_*(\varepsilon)
=\frac{I+P}{2}
 +\frac\varepsilon2(I+P)U+O(\varepsilon^2),
\qquad
\Omega_*(\varepsilon)
=\frac\varepsilon4(UP-PU)+O(\varepsilon^2).
\tag{323.2}
$$

取最大耗散特征值的正单位特征向量 $v_*(\varepsilon)$，则

$$
v_*(\varepsilon)
=n_0+\frac{3\varepsilon}{2}Un_0+O(\varepsilon^2).
\tag{323.3}
$$

这些展开的余项为固定 $a,u$ 下的有限维矩阵或向量范数余项。

证明。设 $b_i=1/a_i(\varepsilon)$、$A=\sum_i b_i^2$，并记第307节的标准化半径权重 $w_i=b_i^2/A$。直接展开给出

$$
A=\frac{3+\varepsilon^2\|u\|_2^2}{a^2},
\qquad
w_i=\frac13+\frac{2\varepsilon}{3}u_i+O(\varepsilon^2),
\qquad
n:=\frac b{\sqrt A}=n_0+\varepsilon Un_0+O(\varepsilon^2).
\tag{323.4}
$$

需要先证明对应的单纯形坐标 $x$ 随 $w$ 光滑变化。第309节的正向根式映射 $x\mapsto w$ 在 $x_0=(1/3,1/3,1/3)$ 附近实解析：该点的根式判别式、全部分母及 $\beta$ 都严格为正。现在计算它在单纯形切空间上的导数。

共同列方程为

$$
c_i=x_i^2\left(1-2x_i+\frac{\beta^2}{w_i}\right)=c,
\qquad \beta^2=\sum_iw_ix_i^2.
\tag{323.5}
$$

在 $x_i=w_i=1/3$ 处，$\beta^2=1/9$。对任意切向变化 $\dot x,\dot w$，两者分量和均为零，因此 $\dot{\beta^2}=0$，而

$$
\dot c_i=\frac29\dot x_i-\frac19\dot w_i.
\tag{323.6}
$$

三个 $\dot c_i$ 相等，求和又为零，故它们都为零，并有 $\dot w=2\dot x$。这个导数在二维切空间上可逆。标准实解析逆函数定理于是给出对称点附近的唯一实解析逆映射，并结合式（323.4）得到

$$
x_i=\frac13+\frac\varepsilon3u_i+O(\varepsilon^2).
\tag{323.7}
$$

由第309节的实际模型对应，这个局部逆解正是任务的唯一正定支撑端点解。该结论还证明所有充分接近等半径的当前模型都属于这一分支；不以半径接近为由直接假定支撑类型。

沿用第310节的归一化记号

$$
X=\operatorname{diag}(x),\qquad
m=\sum_iw_ix_i,\qquad
f=m-\beta^2,\qquad
G_0=nn^{\mathsf T}+\beta(I-2vv^{\mathsf T}),
\qquad M_*=G_0X/f.
\tag{323.8}
$$

归一化恒等式与分量和为零给出

$$
m=\frac13+O(\varepsilon^2),\qquad
\beta=\frac13+O(\varepsilon^2),\qquad
f=\frac29+O(\varepsilon^2).
\tag{323.9}
$$

第307节对核方向的显式公式为

$$
v=\frac{(X+\beta I)n}{\sqrt{2\beta(\beta+m)}}.
\tag{323.10}
$$

将式（323.4）、（323.7）、（323.9）代入，分母为 $2/3+O(\varepsilon^2)$，分子为 $2n_0/3+\varepsilon Un_0+O(\varepsilon^2)$，从而得到式（323.3）。该方向是 $S_*=\operatorname{sym}M_*$ 的简单最大特征方向，见第298、307节。

令 $q=Un_0$，则 $n_0^{\mathsf T}q=0$。有

$$
nn^{\mathsf T}=P+\varepsilon(n_0q^{\mathsf T}+qn_0^{\mathsf T})+O(\varepsilon^2),
$$

$$
vv^{\mathsf T}=P+\frac{3\varepsilon}{2}(n_0q^{\mathsf T}+qn_0^{\mathsf T})+O(\varepsilon^2).
$$

因此 $G_0$ 中的一阶变化恰好抵消：

$$
G_0=\frac13(I+P)+O(\varepsilon^2).
\tag{323.11}
$$

再代入 $X=(I+\varepsilon U)/3+O(\varepsilon^2)$ 与式（323.9），便得到式（323.2）的第一式。由于约定为 $M_*=S_*-\Omega_*$，取 $\Omega_*=(M_*^{\mathsf T}-M_*)/2$，得到第二式。证毕。

**定理 323.2（两种非对称代价的二次消失）。** 在定理323.1的同一模型族中，令 $\Gamma(\varepsilon)$ 为第301节的无限制二阶系数，$\Xi(\varepsilon)$ 为第320节的生成元三阶缺口系数，并定义

$$
C_{\rm hom}(\varepsilon)
=\lim_{\delta\downarrow0}
\frac{\widehat H_{a(\varepsilon)}(\eta(\varepsilon)(1-\delta))
-\widehat G_{a(\varepsilon)}(\eta(\varepsilon)(1-\delta))}{\delta^3}.
\tag{323.12}
$$

这里 $\eta(\varepsilon)=A(\varepsilon)^{-1/2}$；当 $\varepsilon\ne0$ 足够小时，内部极限由第322节给出。则

$$
\Xi(\varepsilon)
=\frac{\|u\|_2^2}{96}\varepsilon^2+O(\varepsilon^3),
\tag{323.13}
$$

$$
\Gamma(\varepsilon)
=-\frac{a\|u\|_2^2}{48\sqrt2}\varepsilon^2+O(\varepsilon^3),
\qquad
C_{\rm hom}(\varepsilon)
=\frac{a\|u\|_2^2}{3456\sqrt2}\varepsilon^2+O(\varepsilon^3).
\tag{323.14}
$$

特别地，任意这样的非零固定扰动方向都有

$$
\lim_{\varepsilon\to0,\ \varepsilon\ne0}
\frac{C_{\rm hom}(\varepsilon)}{-\Gamma(\varepsilon)}
=\frac1{72}.
\tag{323.15}
$$

证明。对称点的耗散矩阵为 $S_*(0)=(I+P)/2$，最大特征值为 $d_3(0)=1$，另外两个特征值为 $1/2$。由式（323.2）、（323.3）及 $Pq=0$，

$$
\Omega_*(\varepsilon)v_*(\varepsilon)
=\frac\varepsilon4q+O(\varepsilon^2),
\qquad
d_3(\varepsilon)I-S_*(\varepsilon)
=\frac12(I-P)+O(\varepsilon).
\tag{323.16}
$$

代入 $\Xi=(\Omega_*v_*)^{\mathsf T}(d_3I-S_*)(\Omega_*v_*)$，得到

$$
\Xi(\varepsilon)
=\frac{\varepsilon^2}{32}\|q\|_2^2+O(\varepsilon^3)
=\frac{\varepsilon^2}{96}\|u\|_2^2+O(\varepsilon^3).
\tag{323.17}
$$

接着核对任务尺度。在 $\varepsilon=0$，端点矩阵的每一列范数为 $1/\sqrt2$，故

$$
\kappa(0)=\frac{a}{2\sqrt2},\qquad
D(0)=\frac{A(0)}{2\kappa(0)}=\frac{3\sqrt2}{a^3},
\qquad
\lambda(0)=A(0)\beta(0)=\frac1{a^2}.
\tag{323.18}
$$

这些参数在当前分支实解析。又因为 $b(\varepsilon)=\sqrt3(n_0+\varepsilon q)/a$，

$$
\Omega_*(\varepsilon)b(\varepsilon)
=\frac{\varepsilon}{4a}u+O(\varepsilon^2).
\tag{323.19}
$$

第301节的精确恒等式是 $\Gamma=-\|\Omega_*b\|_2^2/D$。结合式（323.18）、（323.19），得到式（323.14）的第一式。第322节则给出

$$
C_{\rm hom}(\varepsilon)
=\frac{\lambda(\varepsilon)\Xi(\varepsilon)}{12D(\varepsilon)}.
\tag{323.20}
$$

使用式（323.13）、（323.18），其二阶系数为

$$
\frac{a^{-2}}{12(3\sqrt2/a^3)}\frac{\|u\|_2^2}{96}
=\frac{a\|u\|_2^2}{3456\sqrt2}.
$$

这证明式（323.14）的第二式。因为 $u\ne0$，两个二次首项都非零，取比值便得式（323.15）。证毕。

这里比较的是不同预算阶次的系数：$\Gamma$ 乘以 $\delta^2$，$C_{\rm hom}$ 乘以 $\delta^3$。式（323.15）没有把两种实际误差差距宣称为固定比例。式（323.12）先在每个固定非零 $\varepsilon$ 下取 $\delta\downarrow0$，然后才研究 $\varepsilon\to0$；本节没有证明交换极限、任意联合缩放的同一渐近式，或对接近等半径的全部模型统一的预算邻域。

本节使用的实解析逆函数定理与简单特征值扰动是标准工具。新计算确定了任务最优端点在对称点的一阶矩阵响应，并由同一实际模型求出旋转缺口与两种最优值系数的二次消失率。它不把一般量子比特动力学的相干或各向异性强度等同于当前六态任务的这些系数。

<a id="entry-996"></a>

## 追加锚（本行以下为增补区）

<a id="section-324"></a>

## 324. 正定支撑上的解析逆映射与有限预算最优矩阵

第309节给出了从列权重到半径权重的根式映射，但没有证明逆映射的正则性。第322节也特意不假定有限预算最优解光滑。本节在正定支撑分支证明这两种正则性；关键是任务的列范数使约束切空间上的拉格朗日二次型严格为正。

**定理 324.1（正定支撑权重区域的解析坐标）。** 令 $\mathcal W_+$ 为第309节所有正定支撑模型的标准化权重 $w_i=b_i^2/\|b\|_2^2$ 所成的区域。则 $\mathcal W_+$ 在正权重单纯形中为开集，第309节的双射

$$
\Psi:\{x_i>0,\ \sum_i x_i=1\}\longrightarrow\mathcal W_+
\tag{324.1}
$$

为实解析微分同胚。特别地，选定整体半径尺度后，其唯一端点最优矩阵、对偶参数和列权重都在局部实解析地依赖于该区域内的半径权重。这里不主张逆映射具有一般根式表达。

证明。固定一个正定支撑模型，在正角点规范下取唯一端点最优矩阵 $M_*$，并置 $m_i=M_*e_i$、$B=bb^{\mathsf T}$。以 $W=(M,z)$ 为变量，端点问题的光滑约束写为

$$
F_i(W)=\frac{a_i}{2}\|Me_i\|_2-z\le0\quad(i=1,2,3),
\qquad
F_g(W)=A-b^{\mathsf T}Mb\le0,
$$

$$
F_c(W)=2\lambda_{\max}(\operatorname{sym}M)
-\operatorname{Tr}(\operatorname{sym}M)\le0.
\tag{324.2}
$$

目标为最小化 $z$。第298节使各 $m_i\ne0$、最大对称特征值简单；第301节式（301.1）给出 $M_*b=b$。因为 $G\succ0$，三个列约束均活跃。五个约束的端点乘子为

$$
\pi_i=\frac{b_i\|Ge_i\|_2}{D}>0,
\qquad \mu=\frac1{2D}>0,
\qquad \zeta=\frac\lambda{2D}>0,
\qquad \sum_i\pi_i=1.
\tag{324.3}
$$

这些是第322节核对的乘子归一化；其代数验证同样适用于全等半径。

五个约束梯度线性无关。为明确包括等半径，记 $C_v=I-2vv^{\mathsf T}$，则 $G=B+\lambda C_v$。三个列梯度的矩阵部分为

$$
A_i=\frac{a_i}{2\|Ge_i\|_2}(Ge_i)e_i^{\mathsf T}.
$$

若 $\sum_i\tau_i(A_i,-1)+\beta_0(B,0)+\gamma_0(C_v,0)=0$，则 $\sum_i\tau_i=0$，而矩阵部分经左乘 $G^{-1}$ 化为

$$
\operatorname{diag}(d_i+\gamma_0/\lambda)
+(\beta_0-\gamma_0/\lambda)(G^{-1}b)b^{\mathsf T}=0,
\qquad d_i=\frac{\tau_i a_i}{2\|Ge_i\|_2}.
\tag{324.4}
$$

由于 $b_i>0$ 且 $G^{-1}b\ne0$，该秩一矩阵若系数非零就必有非零非对角元。所以 $\beta_0=\gamma_0/\lambda$，全部 $d_i=-\gamma_0/\lambda$。若 $\gamma_0\ne0$，全部 $\tau_i$ 同严格符号，与其和为零矛盾。故所有系数为零。约束中实际采用的负号不改变线性无关性。

令 $L=z+\sum_i\pi_iF_i+\mu F_g+\zeta F_c$ 为端点拉格朗日函数，$J=D_WF$ 为五行约束 Jacobian。下面证明

$$
H^{\mathsf T}D_W^2L\,H>0
\quad\text{对每个非零 }H\in\ker J.
\tag{324.5}
$$

将变化写作 $H=(E,h)$，其中 $E$ 是矩阵变化、$h$ 是 $z$ 的变化。第 $i$ 个列范数对矩阵变量的二次型为

$$
\frac{a_i}{2\|m_i\|_2}
\left(
\|Ee_i\|_2^2-
\frac{\langle m_i,Ee_i\rangle^2}{\|m_i\|_2^2}
\right)\ge0.
\tag{324.6}
$$

另外，$F_g$ 为仿射函数，$F_c$ 为凸函数，且在当前简单特征值邻域光滑。因此拉格朗日 Hessian 是三个具有严格正权重的列范数 Hessian 与一个半正定特征值 Hessian 之和。

若其二次型为零，式（324.6）对每一列都为零，故存在实数 $t_i$ 使 $Ee_i=t_i m_i$。切空间中的三个列等式给出

$$
\kappa_a t_i=h\qquad(i=1,2,3).
$$

于是 $t_i=t$ 全部相同且 $E=tM_*$。残差切向等式又给出

$$
0=b^{\mathsf T}Eb=t\,b^{\mathsf T}M_*b=tA.
$$

所以 $t=0$，从而 $E=0$、$h=0$。这证明式（324.5）。这里的严格性来自三个正列乘子，故不能无修改地应用于奇异支撑分支。

考虑五个活跃等式和十个平稳性方程组成的 KKT 系统。它对变量与乘子的线性化是标准块矩阵

$$
\begin{pmatrix}
D_W^2L&J^{\mathsf T}\\
J&0
\end{pmatrix}.
\tag{324.7}
$$

若 $(H,\ell)$ 属于其核，则 $JH=0$，并有 $D_W^2L\,H+J^{\mathsf T}\ell=0$。与 $H$ 内积后由式（324.5）得 $H=0$；再由 $J$ 满行秩得 $\ell=0$。因此这个 $15\times15$ 的 KKT Jacobian 可逆。

所有方程在当前点附近实解析：列向量非零，最大对称特征值简单，正半径参数亦可解析变化。标准实解析隐函数定理遂给出唯一局部实解析 KKT 解。五个乘子原本严格正，故在足够小邻域内仍严格正。由式（324.2）的凸性，该解满足全局端点问题的充分 KKT 条件，并是第298节的唯一正角点最优解。相应 $G=B+\lambda C_v$ 连续保持正定。

现在固定一个足够大的尺度 $A_0$，把附近的标准化权重实现为 $b_i=\sqrt{A_0w_i}$，使其物理半径都严格小于一。上述解析构造说明附近权重仍属 $\mathcal W_+$，故该区域为开集。由 $\lambda=\zeta/\mu$、$D=1/(2\mu)$ 以及简单特征值的解析谱投影，端点的 $G$ 也实解析地依赖于这些权重。

第307节的矩阵重构可写为 $M_*=G\operatorname{diag}(x)/(A_0f)$。因此令

$$
t_i=\frac{\langle M_*e_i,Ge_i\rangle}{\|Ge_i\|_2^2}>0,
\qquad
x_i=\frac{t_i}{\sum_jt_j},
\tag{324.8}
$$

便从同一端点解解析地恢复其列权重。所有分母严格为正。这构造了 $\Psi$ 在每个像点的实解析局部逆。第309节已给出全局双射及正向解析根式，故这些局部逆共同组成其全局实解析逆。证毕。

**定理 324.2（固定正定支撑模型的解析最优恢复）。** 固定一个正定支撑半径模型。对于充分小的正 $\delta$，在正角点规范下，微分可分最优恢复和齐次最优恢复各自具有唯一的 Bloch 矩阵，可分别写作

$$
T_G(\delta)=e^{-\delta M_G(\delta)},
\qquad
T_H(\delta)=e^{-\delta M_H(\delta)},
\qquad
M_G(0)=M_H(0)=M_*.
\tag{324.9}
$$

$M_G,M_H$ 在 $\delta=0$ 的一个实邻域内有实解析延拓。全部实际最优复合恢复矩阵都由这些矩阵经第298节允许的有限角点符号共轭得到；这里不主张实现它们的编码、解码因子对唯一。三个列误差和残差预算均取等，且相应通道边界或生成元锥边界取等。

如果半径不全相等，则第322节的余项在这一分支可加强为

$$
\widehat H_a(\eta(1-\delta))
-\widehat G_a(\eta(1-\delta))
=\frac{\lambda\Xi_a}{12D_a}\delta^3+O(\delta^4).
\tag{324.10}
$$

证明。在第322节的归一化对数坐标中，分别取五个约束

$$
F^H_\delta=(f_{\delta,1}-z,f_{\delta,2}-z,f_{\delta,3}-z,-g_\delta,-c),
$$

$$
F^G_\delta=(f_{\delta,1}-z,f_{\delta,2}-z,f_{\delta,3}-z,-g_\delta,-c-q_\delta).
\tag{324.11}
$$

在 $\delta=0$，两套约束都等于式（324.2）。函数 $f_{\delta,i}$、$g_\delta$ 的解析延拓来自矩阵指数及非零列；$q_\delta$ 的解析延拓来自第320节的简单最大特征值分支

$$
\frac{e^{\delta M^{\mathsf T}}e^{\delta M}-I}{2\delta}.
$$

该矩阵在零点延拓为 $\operatorname{sym}M$。若 $h(\delta,M)$ 是该简单特征值分支，$d(M)=\lambda_{\max}(\operatorname{sym}M)$，则用 $2d(M)-\delta^{-1}\log(1+2\delta h(\delta,M))$ 及其零点可去奇点延拓来定义 $q_\delta$。这个解析表达只在正的小 $\delta$ 下与实际范数表达一致。此解析性只需要最大对称特征值简单；等半径时两个较小特征值重复不造成障碍，也不要求 $\Xi_a>0$。

定理324.1的 KKT 线性化可逆，因此两套问题各自存在唯一的局部解析平稳解，变量和乘子都随 $\delta$ 解析。全部乘子在零点严格正，故在小邻域内仍正；五个活跃等式给出的候选可行。对齐次类，$c=0$ 给出合法生成元；对微分可分类，$c+q_\delta=0$ 给出其奇异值条件。$\operatorname{sym}M\succ0$ 在邻域内保持，使矩阵指数严格收缩；第322节的 Pauli 条件验证保证后者为 CPTP 通道。正角点保持唯一活跃，第281节使同一矩阵同时实现预算和误差。

下面证明这两条局部解析支线就是实际最优解，而不把平稳性当作全局最优性。先取固定不等半径。第298节的端点定位与第321节的达到定理使两类全局最优者在有限符号规范之后，都趋于 $(M_*,\kappa_a)$；齐次类在这一固定模型的邻域中具有唯一实主对数。所有这些最优者满足通常的光滑 KKT 条件，因为五行约束梯度在邻域内保持独立。

把不活跃约束的乘子补零，完整乘子由

$$
\Lambda=-(JJ^{\mathsf T})^{-1}J\nabla z
\tag{324.12}
$$

唯一确定，随最优点趋近端点而趋于式（324.3）的五个严格正数。因此足够近的每个实际最优者都使全部五个约束活跃，其完整变量与乘子落在隐函数定理的唯一解邻域内。于是它们必须等于相应解析支线。这也证明正角点规范下的全局唯一性，以及式（324.9）所述的有限符号轨道结论。

等半径时，第293节已给出两类相同的实际最优值，第294节已分类全部微分可分最优复合矩阵。齐次可行类包含于微分可分类，且第293节的精确解提供实际齐次通道，所以齐次最优矩阵也属于同一有限符号轨道。它们趋于本节端点，并满足同一五个活跃等式。相同的 KKT 唯一性使其与两条解析支线相合。对于这一模型，任何其他实际微分可分最优者也由端点定位及式（324.12）落入同一支线；齐次类是其中子类且两类最优值相同，所以其最优复合矩阵也无额外解。这个步骤不把重复谱附近的一般齐次通道宣称为主对数可实现。

最后，最优值为 $\delta z_G(\delta)$、$\delta z_H(\delta)$，故在零点具有收敛的幂级数。对固定不等半径，第322节已经确定差值的三阶首项；解析性将剩余项加强为 $O(\delta^4)$，得到式（324.10）。证毕。

本节的解析隐函数定理、凸 KKT 充分条件和块矩阵可逆判据是标准工具。任务特有的步骤是式（324.5）：三个严格正的列乘子与残差切向等式排除了全部零二次方向。这一条件既产生整个正定支撑区域的解析逆坐标，也使固定模型的有限预算最优矩阵成为实际解析支线。

结论不覆盖奇异支撑分支的零列乘子。固定模型允许的预算邻域也可能随半径而变；本节没有证明在半径同时趋于相等时，所有齐次实际最优者都统一具有简单谱或主对数，因此没有据此交换第323节的两个极限。

<a id="entry-998"></a>

## 追加锚（本行以下为增补区）

<a id="section-325"></a>

## 325. 接近等半径与预算端点的联合极限

第323节给出了先取预算极限、再取半径极限的系数，第324节则证明固定正定支撑模型的解析性。要让两个参数同时变化，还需统一排除其他齐次生成元对数分支。本节用任务误差的二次增长估计与端点谱分裂完成这一步。

**定理 325.1（实际齐次代价的联合渐近式）。** 固定 $0<a<1$ 及非零实向量 $u$，满足 $\sum_i u_i=0$，并令

$$
a_i(\varepsilon)=\frac{a}{1+\varepsilon u_i},
\qquad R_{\varepsilon,\delta}=\eta(\varepsilon)(1-\delta).
\tag{325.1}
$$

存在 $\varepsilon_0,\delta_0>0$，使对 $|\varepsilon|<\varepsilon_0$、$0<\delta<\delta_0$，两类实际最优值均达到，并满足

$$
\widehat H_{a(\varepsilon)}(R_{\varepsilon,\delta})
-\widehat G_{a(\varepsilon)}(R_{\varepsilon,\delta})
=\varepsilon^2\delta^3
\left[
\frac{a\|u\|_2^2}{3456\sqrt2}
+O(|\varepsilon|+\delta)
\right].
\tag{325.2}
$$

余项在该双参数邻域内一致，常数可以依赖于固定的 $a,u$。因此对任意同时趋零且 $\varepsilon\ne0$、$\delta>0$ 的参数序列，差值除以 $\varepsilon^2\delta^3$ 都趋于式（325.2）的正系数。$\varepsilon=0$ 时差值恒为零。

在这个共同邻域中，正角点规范下的两类最优复合矩阵各自唯一，归一化主衰减对数在 $(\varepsilon,\delta)=(0,0)$ 附近共同实解析。对于 $\varepsilon\ne0$，每个实际齐次最优复合恢复的完整超算子具有四个不同的正实特征值，其任何实生成元对数均为主对数。

证明。记 $n_0=(1,1,1)^{\mathsf T}/\sqrt3$、$P=n_0n_0^{\mathsf T}$、$P^\perp=I-P$、$U=\operatorname{diag}(u)$。对称点的归一化端点矩阵为 $M_0=(I+P)/2$。

先在 $M_0$ 附近区分两种局部问题。第一种是第324节的微分可分问题，第二种只允许主衰减对数满足生成元锥条件，暂记为主对数齐次问题。第324节的 KKT 线性化在对称点可逆；五个乘子严格正，三个列向量非零，最大对称特征值简单。将半径参数一并纳入实解析隐函数定理，得到共同实解析的两条局部支线

$$
W_G(\varepsilon,\delta)=(M_G,z_G),
\qquad
W_P(\varepsilon,\delta)=(M_P,z_P).
\tag{325.3}
$$

其中 $P$ 下标在这里指主对数问题。它并不预先断言整个实际齐次优化与该局部问题相同。两个支线在正的小 $\delta$ 都给出实际可行通道；$W_P$ 尤其给出一个实际齐次竞争者，其误差为 $\delta z_P$。

下面先说明微分可分支线与所有低误差竞争者的统一定位。对满足原预算且

$$
T\text{ 幺元 CPTP},\qquad e(T)\le\delta z_P(\varepsilon,\delta)
\tag{325.4}
$$

的任意矩阵，正半径列误差控制使 $N=(I-T)/\delta$ 在 $(\varepsilon,\delta)\to(0,0)$ 时一致有界。若取任意参数序列趋于原点，极限半径为全等的 $a$，而 $z_P\to\kappa(0)$。第296节的一阶 Choi 与残差条件使 $N$ 的任一极限满足对称模型的端点约束，目标值不超过 $\kappa(0)$。端点下界迫使全部取等，第298节遂使极限经一个固定符号共轭后等于 $M_0$。

由于符号类有限，子列反证说明：缩小同一个双参数邻域后，式（325.4）的全部矩阵都经某个允许的符号共轭落入任意预先指定的 $M_0$ 小邻域。此时 $T\to I$，实主矩阵对数存在，且

$$
M=-\frac1\delta\log T
=N+O(\delta)
\tag{325.5}
$$

一致成立。因而这些归一化主对数也有同样的统一定位。这一步尚未断言 $M$ 满足生成元锥条件。

微分可分全局最优值达到，且不大于实际竞争者 $\delta z_P$。其全部最优者于是都进入上述固定邻域。第324节的五行梯度独立性与补零乘子公式在该邻域内一致成立；最优乘子趋于对称端点的五个严格正数，所以全部约束最终活跃。共同参数隐函数定理的唯一性给出

$$
\widehat G_{a(\varepsilon)}(R_{\varepsilon,\delta})
=\delta z_G(\varepsilon,\delta)
\tag{325.6}
$$

及正角点规范下的唯一实际最优矩阵。这是双参数共同邻域中的结论。

还需要一个统一的二次增长估计。对两种局部问题，在足够小的固定邻域内都存在 $c_0>0$，使每个可行 $W$ 满足

$$
z-z_j(\varepsilon,\delta)
\ge c_0\|W-W_j(\varepsilon,\delta)\|^2,
\qquad j\in\{G,P\}.
\tag{325.7}
$$

这里选任一固定 Euclidean 范数。该事实是严格二阶充分条件的标准后果，以下核对所需的一致性。第324节的约束切空间正二次型、满行秩和严格正乘子在共同参数小闭邻域内都有正下界。若不存在统一的式（325.7），可选参数与可行点，使距离 $t_n=\|W_n-W_{j,n}\|\to0$，而目标差除以 $t_n^2$ 趋于一个非正或任意小的数。取归一化方向 $d_n=(W_n-W_{j,n})/t_n$ 的收敛子列。

平稳性、非负乘子与可行性先由拉格朗日函数的 Taylor 展开给出目标差不小于 $-Ct_n^2$。结合所选上界，目标差除以 $t_n$ 趋于零。可行性的一阶展开则给出极限 $Jd\le0$。由平稳性及全部乘子严格正，$\nabla z\cdot d=-\Lambda^{\mathsf T}Jd=0$，遂有 $Jd=0$。另一方面，可行性与非负乘子给出

$$
z_n-z_{j,n}\ge L_n(W_n)-L_n(W_{j,n})
=\frac{t_n^2}{2}d_n^{\mathsf T}D_W^2L_n\,d_n+o(t_n^2).
\tag{325.8}
$$

光滑性使余项一致，而切空间上的严格正下界使右端除以 $t_n^2$ 有统一正下界，矛盾。通过先缩小邻域，再取小于该下界的 $c_0$，便得式（325.7）。这同时证明主对数支线是该固定邻域内的严格局部最小值。

定义实际误差单位下的解析支线差

$$
\Delta(\varepsilon,\delta)
=\delta\bigl(z_P(\varepsilon,\delta)-z_G(\varepsilon,\delta)\bigr).
\tag{325.9}
$$

对每个固定非零的小 $\varepsilon$，第324节的固定模型结论使主对数支线在足够小的预算邻域等于实际齐次最优值。第322节因此确定了 $\Delta$ 关于 $\delta$ 的零至二阶系数全为零，三阶系数为 $C_{\rm hom}(\varepsilon)$。各系数解析地依赖于 $\varepsilon$，所以前述消失恒等式也延拓到 $\varepsilon=0$。

等半径的精确解又使 $\Delta(0,\delta)=0$。式（325.6）以及主对数支线的实际可行性保证，在正的小 $\delta$ 下，对正负两侧的小 $\varepsilon$ 都有 $\Delta\ge0$。于是 $\partial_\varepsilon\Delta(0,\delta)=0$。这一导数也是 $\delta$ 的解析函数，故在原点邻域恒等为零。

共同收敛的幂级数中，$\delta$ 次数小于三或 $\varepsilon$ 次数小于二的系数因而全部为零。因此存在共同实解析函数 $Q$，使

$$
\Delta(\varepsilon,\delta)=\varepsilon^2\delta^3Q(\varepsilon,\delta),
\qquad
Q(0,0)=\frac{a\|u\|_2^2}{3456\sqrt2}>0.
\tag{325.10}
$$

最后一个等式使用第323节对 $C_{\rm hom}$ 的二次展开。到目前为止，这只是主对数支线与实际微分可分值之差。

现在取任意实际幺元齐次竞争者，其误差不超过 $\delta z_P$。它也是微分可分竞争者，且由式（325.4）、（325.5）落入上述统一邻域。令 $W=(M,e(T)/\delta)$。式（325.7）对 $G$ 的增长估计与式（325.10）给出

$$
\|M-M_G(\varepsilon,\delta)\|
\le C_1|\varepsilon|\delta.
\tag{325.11}
$$

为了由此控制对数分支，需要同时控制 $M_G$ 的谱间隙和特征标架。等半径时，坐标置换保持任务、正角点规范与唯一最优矩阵。故 $M_G(0,\delta)$ 与每个坐标置换矩阵交换，必可写成

$$
M_G(0,\delta)=\alpha(\delta)I+\beta(\delta)P,
\qquad \alpha(0)=\beta(0)=\frac12.
\tag{325.12}
$$

这些置换共轭可由相应的正向正交矩阵实现：对于负行列式置换，改用其整体负号不改变共轭作用。因此这里保留了物理任务的对称性。

靠近 $1$ 的简单特征值与靠近 $1/2$ 的二维谱簇之间始终有固定正间隙。标准解析谱投影可用有界的实解析相似变换将二者分块；该变换在 $\varepsilon=0$ 可取恒等。二维块因而具有形式

$$
B_2(\varepsilon,\delta)
=\alpha(\delta)I_2+\varepsilon E(\varepsilon,\delta),
\tag{325.13}
$$

其中 $E$ 共同解析。第323节的端点导数给出

$$
E(0,0)=\left.\frac12P^\perp U P^\perp\right|_{n_0^\perp}.
\tag{325.14}
$$

相似变换的导数在这一标量块内只产生零交换子，故不改变式（325.14）。该对称二维矩阵的迹为零，平方迹为 $\|u\|_2^2/12$，所以两个特征值为

$$
\pm\sqrt{\frac{\|u\|_2^2}{24}}.
\tag{325.15}
$$

它们因 $u\ne0$ 而不同。于是 $E(\varepsilon,\delta)$ 在一个共同小邻域内具有两个不同的实特征值，且可以选择条件数一致有界的实特征标架。结合先前的分块变换，$M_G$ 也具有一致有界的实对角化矩阵。它的全部特征值有统一正下界；当 $\varepsilon\ne0$ 时，两个较小特征值的间隔至少为 $c_1|\varepsilon|$，与最大特征值的间隔则至少为固定的 $c_2>0$。

将式（325.11）视为对这个可对角化矩阵的扰动。标准 Bauer–Fike 估计把 $M$ 的全部特征值限制在以 $M_G$ 特征值为中心、半径不超过 $C_2|\varepsilon|\delta$ 的圆盘内。把共同的 $\delta_0$ 取得足够小，这三个圆盘互不相交，并全部留在正实轴附近的右半平面。沿从 $M_G$ 到 $M$ 的直线扰动，每个圆盘中的代数特征值数保持为一。由于矩阵实且圆盘以实数为中心，每个非实特征值必须与其共轭同处一个圆盘，这与数目为一矛盾。因此 $M$ 具有三个不同的正实特征值。

相应 $T=e^{-\delta M}$ 的三个特征值不同且落在 $(0,1)$。完整幺元超算子 $\operatorname{diag}(1,T)$ 于是有四个不同的正实特征值。其任一实对数与超算子交换，保持每个一维实特征空间，在该空间上只能取相应正特征值的实对数。因此任何实际齐次生成元都必为主对数；这不需要预先限制生成元大小或旋转绕数。

由幺元 GKSL 条件，当前 $M$ 必满足 $\mathcal C(\operatorname{sym}M)\succeq0$。所以所有误差不超过主对数支线的实际齐次竞争者，都属于该支线的局部可行问题。式（325.7）对 $P$ 的增长估计使它们的误差不小于 $\delta z_P$，且取等时矩阵等于该支线。主对数支线自身已经是实际齐次方案，故

$$
\widehat H_{a(\varepsilon)}(R_{\varepsilon,\delta})
=\delta z_P(\varepsilon,\delta)
\tag{325.16}
$$

并真正达到。这里不要求先证明一般齐次类闭；若下确界更小，直接取一个低于支线的竞争者就与刚证出的下界矛盾。第321节的全局去平移约化覆盖原先可能非幺元的实际因子对，并保证实际达到者的复合恢复必幺元。$\varepsilon=0$ 时的相同结论由已有等半径精确解及微分可分最优矩阵唯一性给出。

最后合并式（325.6）、（325.10）、（325.16），再由解析性使用
$Q(\varepsilon,\delta)=Q(0,0)+O(|\varepsilon|+\delta)$，得到式（325.2）及联合极限。有限符号共轭保留全部约束和谱；同一矩阵的实际残差与误差由第281节共同实现。证毕。

二阶充分条件产生二次增长、解析谱投影以及 Bauer–Fike 扰动界都是既有工具。本节新增的任务估计把允许的最优性误差转成 $O(|\varepsilon|\delta)$ 的归一化矩阵距离，再与 $O(|\varepsilon|)$ 的谱分裂比较。这一比较在两参数同时变化时仍排除了其他实生成元对数，因而把局部主对数曲线识别为实际齐次最优曲线。

结论只针对固定对称参考半径 $a$ 和固定非零扰动方向 $u$ 的对称点邻域。不宣称跨零半径退化、任意改变的扰动方向或所有有限预算统一成立，也不宣称编码、解码因子对唯一。

<a id="entry-1000"></a>

## 追加锚（本行以下为增补区）

<a id="section-326"></a>

## 326. 接近对称点时两类最优通道的首个矩阵差

第325节确定了两类实际最优值在联合极限中的差距。标量误差相差二次小量，并不说明最优通道本身也只相差二次小量。本节在同一个正角点规范下计算通道矩阵的首个差项。

**定理 326.1（最优恢复矩阵的联合位移）。** 固定第325节的 $0<a<1$、非零零和向量 $u$ 及半径族 $a_i(\varepsilon)=a/(1+\varepsilon u_i)$。记

$$
n_0=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
P=n_0n_0^{\mathsf T},\qquad U=\operatorname{diag}(u),
\qquad
R_u=\frac{-U+3PU-2UP}{288}.
\tag{326.1}
$$

在第325节的共同参数邻域内，取唯一正角点最优复合矩阵，并写其归一化主衰减对数为

$$
T_G=e^{-\delta M_G(\varepsilon,\delta)},\qquad
T_H=e^{-\delta M_H(\varepsilon,\delta)}.
$$

缩小该邻域后，有一致展开

$$
\begin{aligned}
M_G-M_H
&=\varepsilon\delta^2R_u
+O\bigl(|\varepsilon|\delta^2(|\varepsilon|+\delta)\bigr),\\
T_G-T_H
&=-\varepsilon\delta^3R_u
+O\bigl(|\varepsilon|\delta^3(|\varepsilon|+\delta)\bigr).
\end{aligned}
\tag{326.2}
$$

矩阵余项可用任一固定矩阵范数理解，常数可以依赖于 $a,u$。特别地，$R_u\ne0$，首项系数不依赖共同参考半径 $a$。若按 $M_j=S_j-\Omega_j$ 分解，则

$$
\Omega_G-\Omega_H
=\frac{5\varepsilon\delta^2}{576}(UP-PU)
+O\bigl(|\varepsilon|\delta^2(|\varepsilon|+\delta)\bigr).
\tag{326.3}
$$

证明。第324、325节给出两类实际最优矩阵、目标变量和五个乘子的共同解析性。以下将它们合记为 KKT 解，并沿用第324节的不等式向量。两类约束仅在最后一个分量不同：

$$
F^G_{\varepsilon,\delta}(W)
=F^H_{\varepsilon,\delta}(W)-e_5q_\delta(M),
\qquad
q_\delta(M)=\frac{\delta^2}{6}\Xi(M)+O(\delta^3).
\tag{326.4}
$$

这里 $e_5$ 是五维约束空间的最后一个坐标向量，$W=(M,z)$。最大对称特征值简单，故 $\Xi$ 和式（326.4）所用解析分支都在对称点附近解析；第320节的系数恒等式由解析性延续到 $\Xi=0$ 的对称点。

因为两套系统的零阶及一阶 $\delta$ 系数相同，且端点 KKT 线性化可逆，两套解的对应系数相同。于是它们的差解析地含有因子 $\delta^2$。等半径时两类实际最优矩阵完全相同，所以矩阵差也含有因子 $\varepsilon$。共同幂级数因此给出

$$
M_G-M_H=\varepsilon\delta^2\mathcal R(\varepsilon,\delta)
\tag{326.5}
$$

且 $\mathcal R$ 共同解析。剩下计算 $\mathcal R(0,0)$。

固定小 $\varepsilon$，令 $V(\varepsilon)$ 为两套 $W$ 解之差的 $\delta^2$ 系数，$\ell(\varepsilon)$ 为相应乘子差的系数。所有以下端点对象均在同一 $\varepsilon$ 的唯一端点解处求值。记约束 Jacobian 为 $J$、端点拉格朗日 Hessian 为 $\mathcal H$、最后一个乘子为 $\zeta$。展开活跃等式和平稳性方程得

$$
JV=e_5\frac{\Xi(M_*)}{6},\qquad
\mathcal HV+J^{\mathsf T}\ell
=\frac\zeta6\nabla_W\Xi(M_*).
\tag{326.6}
$$

这些是 $\delta^2$ 的系数等式，没有再乘二阶导数的阶乘。公共的低阶解项在相减时消去，式（326.4）的负号使第二个等式右侧为正。

在 $\varepsilon=0$，$M_0=(I+P)/2$，其反对称部分为零，故 $\Xi(M_0)=0$、$\nabla\Xi(M_0)=0$。KKT 线性化可逆使 $V(0)=0$、$\ell(0)=0$。令

$$
V'(0)=(E,h).
$$

由第323节的展开，$\Xi(M_*(\varepsilon))=O(\varepsilon^2)$。对式（326.6）求 $\varepsilon$ 导数，所有乘以 $V(0)$ 或 $\ell(0)$ 的变化项消失，得到 $J_0(E,h)=0$，并且对每个切向量 $(F,k)\in\ker J_0$，

$$
\mathcal H_0[(E,h),(F,k)]
=\frac{\zeta_0}{6}
\left\langle
\left.\frac{d}{d\varepsilon}\nabla_M\Xi(M_*(\varepsilon))\right|_0,F
\right\rangle_F.
\tag{326.7}
$$

严格正的切空间 Hessian 使这个方程具有唯一解。其矩阵部分正是 $\mathcal R(0,0)$。

先计算式（326.7）的右端。记 $q=Un_0$，则 $q\perp n_0$。第323节给出

$$
\Omega_*(\varepsilon)
=\frac\varepsilon4(UP-PU)+O(\varepsilon^2).
$$

在对称点，$dI-S=(I-P)/2$，所以 $\Xi$ 关于反对称部分的首个二次项是 $\|\Omega n_0\|_2^2/2$。按照 $\Omega=-\operatorname{skew}M$ 的约定，对任意矩阵变化 $F$，

$$
D_M\Xi(M_*(\varepsilon))[F]
=-\frac\varepsilon8(q^{\mathsf T}Fn_0-n_0^{\mathsf T}Fq)
+O(\varepsilon^2)\|F\|_F.
$$

对称部分及最大特征向量的微分只贡献 $O(\varepsilon^2)$，因为这些项均含两个反对称因子。因此

$$
\nabla_M\Xi(M_*(\varepsilon))
=\frac\varepsilon8(PU-UP)+O(\varepsilon^2),
\qquad \zeta_0=\frac{a}{6\sqrt2}.
\tag{326.8}
$$

再计算切空间及其 Hessian。置 $m_i=M_0e_i$，则 $\|m_i\|_2=1/\sqrt2$。残差与锥切向等式给出

$$
n_0^{\mathsf T}En_0=0,\qquad \operatorname{Tr}E=0.
$$

三个列切向等式是 $a\langle m_i,Ee_i\rangle/\sqrt2=h$。将其求和，使用
$\sum_i\langle m_i,Ee_i\rangle=(\operatorname{Tr}E+n_0^{\mathsf T}En_0)/2=0$，得到

$$
h=0,\qquad \langle m_i,Ee_i\rangle=0\quad(i=1,2,3).
\tag{326.9}
$$

反过来，这些等式连同残差及迹等式描述全部切空间。对其中的任意 $E$，第324节的三个列 Hessian，取乘子 $\pi_i=1/3$，共同贡献 $a\|E\|_F^2/(3\sqrt2)$。最大特征值与两个较小特征值之间的间隔为 $1/2$，故锥项的 Hessian 贡献为 $4a\|(I-P)\operatorname{sym}(E)n_0\|_2^2/(3\sqrt2)$。于是

$$
\mathcal H_0[(E,0),(E,0)]
=\frac{a}{3\sqrt2}
\left[\|E\|_F^2+4\|(I-P)\operatorname{sym}(E)n_0\|_2^2\right].
\tag{326.10}
$$

去掉公共正因子 $a/(3\sqrt2)$，式（326.7）的右端成为

$$
\frac1{96}\langle PU-UP,F\rangle_F.
\tag{326.11}
$$

因此该线性响应不依赖 $a$。

下面完整求解这个切向线性问题。它在同时置换 $u$ 的坐标与共轭矩阵时不变，而解唯一，故 $u\mapsto E$ 是置换等变的线性映射。零和向量到三阶矩阵的每个此类映射都可写成

$$
E=\alpha U+\beta PU+\gamma UP.
\tag{326.12}
$$

为核对这个表述，固定一个对角位置，其系数在另外两个坐标交换下不变，利用 $\sum_i u_i=0$ 后只能正比于 $u_i$；固定一个非对角位置 $(i,j)$，它是 $u_i,u_j$ 的线性组合，剩余坐标由零和关系消去。三个系数恰由式（326.12）表示。坐标置换的共轭作用仍可用正向正交矩阵实现，理由与第325节相同。

式（326.12）自动使迹和 $n_0^{\mathsf T}En_0$ 为零，而

$$
\langle m_i,Ee_i\rangle
=\frac{u_i}{6}(4\alpha+2\beta+\gamma).
$$

因为 $u\ne0$，列切向条件恰好为 $\gamma=-4\alpha-2\beta$。令 $k_u=\|u\|_2^2/3=\|q\|_2^2>0$，直接内积计算得到

$$
\begin{aligned}
\|E\|_F^2+4\|(I-P)\operatorname{sym}(E)n_0\|_2^2
&=k_u(15\alpha^2+18\alpha\beta+6\beta^2),\\
\langle PU-UP,E\rangle_F
&=k_u(4\alpha+3\beta).
\end{aligned}
\tag{326.13}
$$

这些等式可由 $PU=n_0q^{\mathsf T}$、$UP=qn_0^{\mathsf T}$、$n_0^{\mathsf T}q=0$ 直接展开；相应 Hessian 双线性型由极化获得。唯一响应已知属于这一等变子空间，所以把式（326.7）限制到其两个切向系数，便得到

$$
\begin{pmatrix}15&9\\9&6\end{pmatrix}
\begin{pmatrix}\alpha\\\beta\end{pmatrix}
=\frac1{96}\begin{pmatrix}4\\3\end{pmatrix}.
\tag{326.14}
$$

这里左侧是 Hessian 双线性型，不再把式（326.13）的二次型求导而额外乘二。该矩阵行列式为九，解为

$$
\alpha=-\frac1{288},\qquad
\beta=\frac1{96},\qquad
\gamma=-\frac1{144}.
\tag{326.15}
$$

所以 $\mathcal R(0,0)=R_u$。由于 $q\ne0$ 且 $q\perp n_0$，$PU-UP=n_0q^{\mathsf T}-qn_0^{\mathsf T}\ne0$；$R_u$ 的反对称部分非零，从而 $R_u\ne0$。

共同解析性使 $\mathcal R(\varepsilon,\delta)=R_u+O(|\varepsilon|+\delta)$，与式（326.5）结合即得第一个展开。矩阵指数的标准微分或其收敛幂级数，在有界的 $M_G,M_H$ 邻域内给出

$$
e^{-\delta M_G}-e^{-\delta M_H}
=-\delta(M_G-M_H)+O\bigl(\delta^2\|M_G-M_H\|\bigr).
\tag{326.16}
$$

它不要求两个矩阵交换。代入第一个展开，得到第二个展开。最后用 $\Omega_j=(M_j^{\mathsf T}-M_j)/2$ 取反对称部分，就得到式（326.3）。证毕。

本节使用的 KKT 灵敏度、解析隐函数定理和矩阵指数微分是标准工具。新增内容是同一恢复任务的显式响应矩阵 $R_u$：两类最优通道在不对称参数的一阶已经分开，而第325节的最优误差差值直到该参数的二阶才出现。这个比较在共同正角点规范中进行，并不宣称编码、解码因子对唯一，也不扩展到奇异支撑分支或任意有限预算。

<a id="entry-1002"></a>

## 追加锚（本行以下为增补区）

<a id="section-327"></a>

## 327. 用满残差预算后的退极化修复与值近优性

第320节的标量修复将微分可分最优通道变成实际齐次通道，但也降低了残差。本节在第325节的联合邻域中把这部分预算重新用满，并比较修复误差与真正的齐次最优误差。加入最小各向同性噪声的办法仍是 Wolf、Eisert、Cubitt 与 Cirac，*Assessing Non-Markovian Quantum Dynamics*（2008），[“Measuring Markovianity”部分](https://arxiv.org/abs/0711.3172v2)的既有构造；下面新增的是同一六态任务的预算校准及其误差系数。

**定义 327.1（直接修复与预算匹配修复）。** 固定第325节的 $0<a<1$、非零零和向量 $u$，令 $a_i(\varepsilon)=a/(1+\varepsilon u_i)$。在该节的共同邻域内取正角点规范下的实际最优矩阵

$$
T_G(\varepsilon,\delta)=e^{-\delta M_G(\varepsilon,\delta)},
\qquad T_H(\varepsilon,\delta)=e^{-\delta M_H(\varepsilon,\delta)}.
$$

记目标预算为 $R_{\varepsilon,\delta}=\eta(\varepsilon)(1-\delta)$，并置

$$
G(\varepsilon,\delta)=\widehat G_{a(\varepsilon)}(R_{\varepsilon,\delta}),
\quad H(\varepsilon,\delta)=\widehat H_{a(\varepsilon)}(R_{\varepsilon,\delta}),
\quad K_u=\frac{a\|u\|_2^2}{3456\sqrt2}>0.
\tag{327.1}
$$

使用第324节的解析函数 $q_\delta(M)$，定义

$$
\alpha(\varepsilon,\delta)=\delta q_\delta(M_G(\varepsilon,\delta)),
\qquad T_{\rm raw}(\varepsilon,\delta)
=e^{-\alpha(\varepsilon,\delta)}T_G(\varepsilon,\delta).
\tag{327.2}
$$

对充分小的正 $\delta$，令 $\theta=\theta(\varepsilon,\delta)$ 为下列预算方程在零点附近的解：

$$
(1-\theta)e^{-\alpha(\varepsilon,\theta)}=1-\delta.
\tag{327.3}
$$

预算匹配修复定义为

$$
T_{\rm match}(\varepsilon,\delta)
=e^{-\alpha(\varepsilon,\theta)}T_G(\varepsilon,\theta).
\tag{327.4}
$$

以下定理同时证明这些定义中的非负性、局部唯一性及实际可实现性。误差 $e_\varepsilon(T)$ 始终使用当前半径 $a_i(\varepsilon)$。

**定理 327.2（预算匹配消去直接修复的额外首阶损失）。** 缩小第325节的共同邻域后，式（327.2）的 $\alpha$ 非负，并且是给定主衰减对数上合法幺元生成元修复所需的最小非负标量。它满足一致展开

$$
\alpha(\varepsilon,\delta)
=\varepsilon^2\delta^3
\left[\frac{\|u\|_2^2}{576}+O(|\varepsilon|+\delta)\right].
\tag{327.5}
$$

式（327.3）具有唯一局部实解析解，且 $0<\theta\le\delta$；当 $\varepsilon\ne0$ 时严格小于 $\delta$，当 $\varepsilon=0$ 时等于 $\delta$。进一步有

$$
\delta-\theta
=\varepsilon^2\delta^3
\left[\frac{\|u\|_2^2}{576}+O(|\varepsilon|+\delta)\right].
\tag{327.6}
$$

两个修复矩阵都由单个有限齐次生成元实现。直接修复的最小可实现残差为 $e^{-\alpha}\eta(\varepsilon)(1-\delta)$，预算匹配修复的最小可实现残差则恰为 $R_{\varepsilon,\delta}$。同一实际编码、解码同时实现各自的残差与恢复误差，并且

$$
\begin{aligned}
e_\varepsilon(T_{\rm raw})-G(\varepsilon,\delta)
&=\varepsilon^2\delta^3[4K_u+O(|\varepsilon|+\delta)],\\
e_\varepsilon(T_{\rm match})-G(\varepsilon,\delta)
&=\varepsilon^2\delta^3[K_u+O(|\varepsilon|+\delta)].
\end{aligned}
\tag{327.7}
$$

这里及以下余项常数可依赖固定的 $a,u$。因此存在常数 $C>0$，使

$$
0\le e_\varepsilon(T_{\rm match})-H(\varepsilon,\delta)
\le C\varepsilon^2\delta^3(|\varepsilon|+\delta).
\tag{327.8}
$$

证明。先核对修复量的共同解析性。第324、325节给出 $M_G$ 及 $q$ 的解析延拓。对任意实 $M$、$\delta>0$，对称部分的能量估计给出

$$
\|e^{\delta M}\|_{\rm op}
\le e^{\delta d(M)},\qquad d(M)=\lambda_{\max}(\operatorname{sym}M).
$$

故 $q_\delta(M)=2d(M)-2\delta^{-1}\log\|e^{\delta M}\|_{\rm op}\ge0$。该式只在正 $\delta$ 处识别实际范数；零点两侧的解析延拓仍按第324节定义。

第320、326节的解析系数恒等式使 $q_\delta(M)$ 含有因子 $\delta^2$，其系数在 $\delta=0$ 为 $\Xi(M)/6$。等半径时 $M_G(0,\delta)$ 对称，所以正 $\delta$ 处 $q_\delta(M_G(0,\delta))=0$。再由 $q\ge0$ 对正负两侧的 $\varepsilon$ 都成立，可知其对 $\varepsilon$ 的一阶导数在 $\varepsilon=0$ 为零。这些消失恒等式通过解析性延拓到零点邻域。共同幂级数因此给出

$$
\alpha(\varepsilon,\delta)=\varepsilon^2\delta^3A(\varepsilon,\delta),
\qquad A(0,0)=\frac{\|u\|_2^2}{576},
\tag{327.9}
$$

其中最后一个系数由第323节的 $\Xi(M_*(\varepsilon))=\varepsilon^2\|u\|_2^2/96+O(\varepsilon^3)$ 得到。这证明式（327.5），并使小邻域中的 $A$ 严格为正。

实际微分可分最优支线满足 $c(M_G)+q_\delta(M_G)=0$，其中 $c(M)=\operatorname{Tr}S-2\lambda_{\max}(S)$、$S=\operatorname{sym}M$。故主衰减对数 $\delta M_G$ 的锥矩阵的最小特征值为 $-\alpha$。恒等式

$$
\mathcal C(\delta S+\alpha I)=\delta\mathcal C(S)+\alpha I
$$

说明加入 $\alpha I$ 恰好将这个最小特征值移到零。这证明最小标量修复及其有限齐次实现；不把它解释为全部矩阵修正中的最小值。第281节的正齐次残差公式与共同实现，给出直接修复的精确残差及实际因子。

令 $F(\varepsilon,s)=1-(1-s)e^{-\alpha(\varepsilon,s)}$。它在原点共同解析，$F(\varepsilon,0)=0$，$\partial_sF(0,0)=1$。解析隐函数定理给出唯一局部解 $F(\varepsilon,\theta)=\delta$。缩小邻域后 $F$ 对 $s$ 严格递增；对正 $s$，$F(\varepsilon,s)\ge s$，所以 $0<\theta\le\delta$。式（327.9）的严格正系数给出所述严格性和等半径情形。

预算方程还精确给出

$$
\delta-\theta=(1-\theta)(1-e^{-\alpha(\varepsilon,\theta)}).
\tag{327.10}
$$

先用 $\theta\le\delta$ 及式（327.9）得到 $\delta-\theta=O(\varepsilon^2\delta^3)$，于是 $\theta/\delta=1+O(\varepsilon^2\delta^2)$。再将式（327.9）代回式（327.10），即得式（327.6）。在预算 $\theta$ 处施加已经证明合法的标量修复，并使用式（327.3），便得到实际齐次矩阵 $T_{\rm match}$ 的精确目标残差。

下面计算误差，不把列范数的最大值预先当作可微函数。记

$$
D_i(\varepsilon,s)=\frac{I-T_G(\varepsilon,s)}{s}e_i.
$$

它在 $s=0$ 解析延拓，且在原点等于 $m_i=M_0e_i$，其中 $M_0=(I+P)/2$、$P=n_0n_0^{\mathsf T}$、$n_0=(1,1,1)^{\mathsf T}/\sqrt3$。各列范数有共同正下界。第324、325节又使三个原列误差全部等于 $G(\varepsilon,s)$。

对固定的小正 $s$，按标量衰减 $\gamma$ 展开每一列误差，得到

$$
\begin{aligned}
\frac{a_i(\varepsilon)}2
\|(I-e^{-\gamma}T_G(\varepsilon,s))e_i\|_2
&=G(\varepsilon,s)+\gamma d_i(\varepsilon,s)
+O(\gamma^2/s),\\
d_i(\varepsilon,s)
&=\frac{a_i(\varepsilon)}2
\frac{\langle D_i(\varepsilon,s),T_G(\varepsilon,s)e_i\rangle}
{\|D_i(\varepsilon,s)\|_2}.
\end{aligned}
\tag{327.11}
$$

这是非零向量范数的 Taylor 公式。原误差向量的长度有 $cs$ 下界，而当 $0\le\gamma\le C_1\varepsilon^2s^3$ 时扰动为 $O(\gamma)=o(s)$；沿整段展开路径仍有 $c's$ 下界，所以二阶导数界为 $O(1/s)$，余项对三个列和参数一致。

在原点，$\|m_i\|_2=1/\sqrt2$、$\langle m_i,e_i\rangle=2/3$。故三个系数具有相同极限

$$
d_i(\varepsilon,s)=d_0+O(|\varepsilon|+s),
\qquad d_0=\frac{a\sqrt2}{3}.
\tag{327.12}
$$

取三个列的最大值仍保持这一一致估计。将 $\gamma=\alpha(\varepsilon,s)$ 代入，$O(\gamma^2/s)$ 被 $\gamma O(|\varepsilon|+s)$ 吸收；$\varepsilon=0$ 时两者都严格为零。于是

$$
e_\varepsilon(T_{\rm raw}(\varepsilon,s))
=G(\varepsilon,s)+\alpha(\varepsilon,s)
[d_0+O(|\varepsilon|+s)].
\tag{327.13}
$$

取 $s=\delta$ 并使用式（327.5），首项为
$d_0\|u\|_2^2/576=4K_u$，证明式（327.7）的第一式。

对预算匹配修复取 $s=\theta$。实际最优值 $G(\varepsilon,s)=s z_G(\varepsilon,s)$ 解析，故

$$
\partial_sG(\varepsilon,s)=\kappa_0+O(|\varepsilon|+s),
\qquad \kappa_0=\frac{a}{2\sqrt2}.
\tag{327.14}
$$

在 $[\theta,\delta]$ 积分得到

$$
G(\varepsilon,\theta)-G(\varepsilon,\delta)
=-(\delta-\theta)[\kappa_0+O(|\varepsilon|+\delta)].
$$

式（327.10）给出 $\delta-\theta=\alpha(\varepsilon,\theta)[1+O(\delta)]$，而式（327.5）、（327.6）使
$\alpha(\varepsilon,\theta)=\varepsilon^2\delta^3[\|u\|_2^2/576+O(|\varepsilon|+\delta)]$。将这些式子与式（327.13）合并，首项系数为

$$
(d_0-\kappa_0)\frac{\|u\|_2^2}{576}
=\frac{a}{6\sqrt2}\frac{\|u\|_2^2}{576}=K_u.
\tag{327.15}
$$

这证明第二式。最后，第325节的实际最优差满足 $H-G=\varepsilon^2\delta^3[K_u+O(|\varepsilon|+\delta)]$。相减给出式（327.8）的上界；下界来自已经构造的同预算实际齐次可行性。证毕。

**定理 327.3（值的首项最优不消去矩阵的首项偏差）。** 在同一个正角点规范中，令 $R_u$ 为式（326.1）的非零矩阵。预算匹配修复仍满足

$$
T_{\rm match}-T_H
=-\varepsilon\delta^3R_u
+O\bigl(|\varepsilon|\delta^3(|\varepsilon|+\delta)\bigr).
\tag{327.16}
$$

缩小共同邻域后，还存在常数 $c>0$，使

$$
e_\varepsilon(T_{\rm match})-H(\varepsilon,\delta)
\ge c\varepsilon^2\delta^5.
\tag{327.17}
$$

因此对非零的小 $\varepsilon$ 和正的小 $\delta$，预算匹配修复严格不是齐次最优矩阵。另一方面，对任意这样的联合趋零序列，

$$
\frac{e_\varepsilon(T_{\rm match})-G}{H-G}\longrightarrow1,
\qquad
\frac{e_\varepsilon(T_{\rm raw})-G}{H-G}\longrightarrow4.
\tag{327.18}
$$

证明。式（327.4）的主衰减对数可直接写成

$$
\widetilde M
=\frac{\theta}{\delta}M_G(\varepsilon,\theta)
+\frac{\alpha(\varepsilon,\theta)}{\delta}I,
\qquad T_{\rm match}=e^{-\delta\widetilde M}.
\tag{327.19}
$$

右侧是接近 $M_0$ 的有界实矩阵，故这里确是近恒等矩阵的主对数。利用 $M_G$ 的解析性和式（327.5）、（327.6），有

$$
\widetilde M-M_G(\varepsilon,\delta)=O(\varepsilon^2\delta^2).
$$

再用第326节得

$$
\widetilde M-M_H
=\varepsilon\delta^2R_u
+O\bigl(|\varepsilon|\delta^2(|\varepsilon|+\delta)\bigr).
\tag{327.20}
$$

标准矩阵指数微分在该有界邻域内给出
$e^{-\delta\widetilde M}-e^{-\delta M_H}
=-\delta(\widetilde M-M_H)+O(\delta^2\|\widetilde M-M_H\|)$，不要求两矩阵交换。这证明式（327.16）。

因为 $R_u\ne0$，缩小邻域后式（327.20）使
$\|\widetilde M-M_H\|\ge c_1|\varepsilon|\delta^2$。修复矩阵已经满足齐次生成元条件与同一精确预算，并留在第325节的共同局部邻域。因此将该节的齐次问题统一二次增长估计应用于

$$
W=\left(\widetilde M,\frac{e_\varepsilon(T_{\rm match})}{\delta}\right)
$$

及真正的齐次最优支线，得到

$$
\frac{e_\varepsilon(T_{\rm match})-H}{\delta}
\ge c_2\|\widetilde M-M_H\|^2
\ge c_2c_1^2\varepsilon^2\delta^4.
$$

乘以 $\delta$ 即为式（327.17）。这只提供五阶下界，不断言它是精确阶次或已经确定相应系数。式（327.18）则直接由第325节的严格正首项和式（327.7）取比值得到。证毕。

本节的局部结论同时保留了三个区别：标量生成元修复的最小噪声、给定任务预算下的最小恢复误差，以及通道矩阵本身的最优性。重新用满残差预算使这一显式构造达到最优误差差距的联合首项，但它仍保留一阶不对称矩阵偏差及严格正的更高阶误差。本节未求一般有限预算曲线，也未将这些任务系数视为一般量子动力学的普适常数。

<a id="entry-1004"></a>

## 追加锚（本行以下为增补区）

<a id="section-328"></a>

## 328. 预算匹配修复的两种剩余代价与交叉尺度

第327节的预算匹配修复达到了最优值差距的联合首项，但仍不是最优通道。本节继续分解它的剩余误差：一部分来自三个列误差不再同时活跃，另一部分来自实际矩阵在约束面上的偏移。二者由同一个实际修复通道产生。

**定理 328.1（列误差分裂与矩阵位移的联合展开）。** 保留第327节的固定 $a,u$、半径族、实际齐次最优值 $H(\varepsilon,\delta)$、预算匹配修复 $T_{\rm match}$ 及常数 $K_u=a\|u\|_2^2/(3456\sqrt2)$。记

$$
\mathcal E(\varepsilon,\delta)
=e_\varepsilon(T_{\rm match}(\varepsilon,\delta))-H(\varepsilon,\delta).
$$

在足够小的共同参数邻域内，有一致展开

$$
\mathcal E(\varepsilon,\delta)
=\varepsilon^2\delta^3\left[
4K_u\max_i(-\varepsilon u_i)
+\frac{5K_u}{144}\delta^2
+O\bigl(\varepsilon^2+|\varepsilon|\delta+\delta^3\bigr)
\right].
\tag{328.1}
$$

因此，当 $\varepsilon\ne0$、$\delta>0$ 联合趋零时，也可写成

$$
\mathcal E(\varepsilon,\delta)
=K_u\varepsilon^2\delta^3
\left[4\max_i(-\varepsilon u_i)+\frac5{144}\delta^2\right]
\left[1+O(|\varepsilon|+\delta)\right].
\tag{328.2}
$$

余项常数只需对固定 $a,u$ 一致。$\varepsilon=0$ 时误差超额严格为零。

证明。令 $\widetilde M$ 为第327节预算匹配修复的归一化主衰减对数，令 $M_H$ 为实际齐次最优支线。两者在同一正角点邻域中满足精确等式

$$
g_\delta(\widetilde M)=g_\delta(M_H)=0,
\qquad c(\widetilde M)=c(M_H)=0.
\tag{328.3}
$$

第一组等式来自精确残差预算，第二组来自最小标量修复和齐次最优支线的活跃生成元条件。这里 $g_\delta,c,f_{\delta,i}$ 均为第322、324节的同一归一化函数，半径参数取当前 $\varepsilon$。

记实际齐次最优点的列乘子、残差乘子及锥乘子分别为 $\pi_i,\mu,\zeta$。它们共同解析，且 $\sum_i\pi_i=1$。以这些固定在最优点的乘子定义矩阵变量的拉格朗日函数

$$
\mathcal L(M)=\sum_i\pi_i f_{\delta,i}(M)
-\mu g_\delta(M)-\zeta c(M).
\tag{328.4}
$$

完整拉格朗日函数的 $z$ 系数为 $1-\sum_i\pi_i=0$，所以此处没有省去任何变化项，并且 $D_M\mathcal L(M_H)=0$。

令 $E_i=\delta f_{\delta,i}(\widetilde M)$ 为修复通道的三个实际列误差。齐次最优点的三个列误差全为 $H$。由式（328.3）得到精确分解

$$
\mathcal E
=\left(\max_i E_i-\sum_i\pi_iE_i\right)
+\delta\bigl(\mathcal L(\widetilde M)-\mathcal L(M_H)\bigr).
\tag{328.5}
$$

这个恒等式保留了最大值，不假定修复后的全部列约束仍然活跃。

先计算第二项。第327节给出

$$
\Delta M:=\widetilde M-M_H
=\varepsilon\delta^2R_u
+O\bigl(|\varepsilon|\delta^2(|\varepsilon|+\delta)\bigr),
\qquad
R_u=\frac{-U+3PU-2UP}{288}.
\tag{328.6}
$$

其中 $U=\operatorname{diag}(u)$、$P=n_0n_0^{\mathsf T}$、$n_0=(1,1,1)^{\mathsf T}/\sqrt3$。归一化约束和乘子在共同邻域内解析，故 $\mathcal L$ 的三阶导数一致有界。平稳性与 Taylor 展开遂给出

$$
\delta\bigl(\mathcal L(\widetilde M)-\mathcal L(M_H)\bigr)
=\frac\delta2 D_M^2\mathcal L(M_H)[\Delta M,\Delta M]
+O(\delta\|\Delta M\|^3).
\tag{328.7}
$$

$R_u$ 属于对称端点的约束切空间。第326节已计算该切空间上的 Hessian：对切向矩阵 $E$，

$$
\mathcal H_0[E,E]
=\frac{a}{3\sqrt2}\mathscr B(E,E),
\quad
\mathscr B(E,E)=\|E\|_F^2
+4\|(I-P)\operatorname{sym}(E)n_0\|_2^2.
\tag{328.8}
$$

将式（326.13）的系数 $\alpha=-1/288$、$\beta=1/96$、$\gamma=-1/144$ 代入，得到

$$
\mathscr B(R_u,R_u)
=\frac{\|u\|_2^2}{3}
\frac{15-54+54}{288^2}
=\frac{5\|u\|_2^2}{82944}.
\tag{328.9}
$$

Hessian 的连续解析变化和式（328.6）于是把式（328.7）化为

$$
\delta\bigl(\mathcal L(\widetilde M)-\mathcal L(M_H)\bigr)
=\frac{5K_u}{144}\varepsilon^2\delta^5
+O\bigl(\varepsilon^2\delta^5(|\varepsilon|+\delta)\bigr).
\tag{328.10}
$$

这里的系数含 Taylor 公式的 $1/2$；具体为
$a(5\|u\|_2^2/82944)/(6\sqrt2)=5K_u/144$。高阶余项 $O(\delta\|\Delta M\|^3)$ 被所示界吸收。

再计算式（328.5）的第一项。记 $\theta$ 为匹配前预算，$\alpha=\alpha(\varepsilon,\theta)$。第327节逐列的范数展开给出

$$
E_i=G(\varepsilon,\theta)
+\alpha d_i(\varepsilon,\theta)+O(\alpha^2/\theta),
\tag{328.11}
$$

三个余项一致，其中 $d_i$ 为式（327.11）的解析列系数。它们在对称轴上相同，记共同值为 $d_{\rm sym}(s)$。

还需明确 $d_i$ 在原点关于 $\varepsilon$ 的一阶系数。第323节给出

$$
M_*(\varepsilon)=M_0(I+\varepsilon U)+O(\varepsilon^2),
\qquad M_0=(I+P)/2.
$$

所以第 $i$ 列在一阶只乘以 $1+\varepsilon u_i$，其单位方向没有一阶变化；同时 $a_i(\varepsilon)=a(1-\varepsilon u_i)+O(\varepsilon^2)$。在 $s=0$，式（327.11）中的 $T_G$ 等于 $I$，从而

$$
d_i(\varepsilon,0)
=d_0(1-\varepsilon u_i)+O(\varepsilon^2),
\qquad d_0=\frac{a\sqrt2}{3}.
$$

共同解析性因此给出

$$
d_i(\varepsilon,\theta)
=d_{\rm sym}(\theta)-d_0\varepsilon u_i
+O(\varepsilon^2+|\varepsilon|\theta).
\tag{328.12}
$$

实际齐次最优解及其唯一乘子在等半径时具有坐标置换对称性，所以对所有小 $\delta$ 都有 $\pi_i(0,\delta)=1/3$。解析性使 $\pi_i(\varepsilon,\delta)=1/3+O(|\varepsilon|)$，余项对 $\delta$ 一致。利用 $\sum_i u_i=0$、$\sum_i\pi_i=1$，公共的 $d_{\rm sym}(\theta)$ 完全消去，并有

$$
\max_i d_i(\varepsilon,\theta)-\sum_i\pi_i d_i(\varepsilon,\theta)
=d_0\max_i(-\varepsilon u_i)
+O(\varepsilon^2+|\varepsilon|\delta).
\tag{328.13}
$$

这一步只用有限最大值对一致误差的 Lipschitz 性。$\pi_i$ 在目标预算 $\delta$ 取值，而 $d_i$ 在匹配前预算 $\theta$ 取值；上述估计明确保留了这一区别，并使用 $0<\theta\le\delta$。

再由第327节

$$
\alpha=\varepsilon^2\delta^3
\left[\frac{\|u\|_2^2}{576}+O(|\varepsilon|+\delta)\right],
\qquad \theta/\delta=1+O(\varepsilon^2\delta^2),
$$

式（328.11）至（328.13）给出

$$
\max_i E_i-\sum_i\pi_iE_i
=\varepsilon^2\delta^3
\left[4K_u\max_i(-\varepsilon u_i)
+O(\varepsilon^2+|\varepsilon|\delta)\right].
\tag{328.14}
$$

其中 $\alpha^2/\theta=O(\varepsilon^4\delta^5)$ 被余项吸收，且 $d_0\|u\|_2^2/576=4K_u$。

将式（328.10）、（328.14）代入精确分解（328.5），即可得到式（328.1）。因为固定非零零和向量同时有正分量和负分量，存在只依赖于 $u$ 的 $c_u,C_u>0$，使

$$
c_u|\varepsilon|\le\max_i(-\varepsilon u_i)\le C_u|\varepsilon|.
$$

首项括号因此与 $|\varepsilon|+\delta^2$ 相互控制。又有

$$
\varepsilon^2+|\varepsilon|\delta+\delta^3
\le (|\varepsilon|+\delta)(|\varepsilon|+\delta^2).
$$

除以严格正的首项括号便得到式（328.2）。等半径情形由第327节的精确相等单独处理。证毕。

**定理 328.2（交叉尺度与两侧不对称系数）。** 在定理328.1的条件下，沿任何 $\varepsilon\ne0$、$\delta>0$ 的联合趋零序列，有以下结论。

若 $|\varepsilon|=o(\delta^2)$，则

$$
\frac{\mathcal E}{\varepsilon^2\delta^5}\longrightarrow\frac{5K_u}{144}.
\tag{328.15}
$$

若 $\delta^2=o(|\varepsilon|)$ 且 $\operatorname{sgn}\varepsilon=\sigma\in\{-1,1\}$ 固定，则

$$
\frac{\mathcal E}{|\varepsilon|^3\delta^3}
\longrightarrow4K_u\max_i(-\sigma u_i).
\tag{328.16}
$$

若 $\varepsilon/\delta^2\to\tau\in\mathbb R$，则

$$
\frac{\mathcal E}{\varepsilon^2\delta^5}
\longrightarrow K_u\left[\frac5{144}+4\max_i(-\tau u_i)\right].
\tag{328.17}
$$

证明。分别按所述尺度除以式（328.2），利用有限最大值的连续性，即得三式。对 $\tau=0$，式（328.17）还原式（328.15）；参数序列仍要求 $\varepsilon\ne0$，不在零分母处取比值。证毕。

本节使用标准 KKT 拉格朗日展开与有限最大值的连续性。新增内容是同一实际修复方案的两个显式代价：列误差分裂给出带方向的三次不对称项，约束面上的矩阵位移给出五阶预算项。交叉尺度由这两个非负首项共同决定，而不是把分别优化的两个方案当作同一实现。结论不确定固定正预算下的完整各向异性系数，也不扩展到奇异支撑分支。

<a id="entry-1006"></a>

## 追加锚（本行以下为增补区）

<a id="section-329"></a>

## 329. 零预算处的精确最优斜率与横向奇异值

第317节的退相干曲线给出了零预算附近的可达上界，但上界的导数本身不是实际最优值的导数。本节对任意实际最优恢复建立匹配下界。证明使用其零预算极限以及同一个矩阵的左右奇异方向，不假定最优矩阵光滑，也不要求先给出方向的收敛速度。

**定理 329.1（任意正半径的零预算右导数）。** 固定正半径六态模型，沿用第317节的 $A=\sum_i\alpha_i^2$、$\eta=A^{-1/2}$、零预算最优值 $E_0$ 及全部零预算最优投影集合 $\mathcal P_0$。任选 $P_u=uu^{\mathsf T}\in\mathcal P_0$，并记

$$
m=\min_{\sigma\in\{\pm1\}^3}(u\cdot b_\sigma)^2,
\qquad b_\sigma=(\sigma_i\alpha_i),
\qquad \beta=\sqrt{A-m}>0.
\tag{329.1}
$$

$m$ 与所选零预算最优投影无关。则当 $R\downarrow0$ 时，

$$
\widehat G_a(R)=E_0-E_0\beta R+o(R),
\qquad
\widehat G_a'(0+)=-E_0\beta.
\tag{329.2}
$$

结论包括第317节的支撑阈值和重复半径，不要求三个最优投影坐标都非零。

进一步，对每个 $0<R<\eta$ 任取一个实际最优复合恢复矩阵 $T_R$，令其排序奇异值为 $s_1(R)\ge s_2(R)\ge s_3(R)>0$。对这些选择一致地有

$$
\begin{aligned}
\operatorname{dist}(T_R,\mathcal P_0)&\longrightarrow0,
&s_1(R)&\longrightarrow1,\\
\frac{s_2(R)}R&\longrightarrow\beta,
&\frac{s_3(R)}R&\longrightarrow\beta,\\
\frac{r_*(T_R)}R&\longrightarrow1.
\end{aligned}
\tag{329.3}
$$

若该最优恢复来自原实际编码、解码，其编码残差也满足 $r(\mathcal E_R)/R\to1$。这里不声称每个正预算已经精确饱和，也不声称最优矩阵或因子唯一。

证明。第317节已证明 $m$ 对全部零预算最优方向相同，且 $m<A$。该节的可达曲线给出

$$
\widehat G_a(R)
\le E_0\left(1-\frac{\beta R}{\sqrt{1-mR^2}}\right)
=E_0-E_0\beta R+O(R^3).
\tag{329.4}
$$

这暂时只是上界。下面的下界与谱分析均作用于实际最优矩阵。

先证明全部最优矩阵向 $\mathcal P_0$ 定位。第293节使它们都幺元，允许的闭微分可分 CPTP 矩阵集合紧。第281节的最小残差可写为

$$
r_*(T)=\min_{\|n\|_2=1}\max_i a_i|n\cdot Te_i|,
$$

因此由紧球面上的连续最小化，它关于 $T$ 连续；误差也连续。对任意 $R_j\downarrow0$ 及最优选择 $T_j$，取收敛子列 $T_j\to T_0$。可行性给出 $r_*(T_0)=0$，而式（329.4）使 $e(T_0)\le E_0$。闭类性与第281节的共同实现说明 $T_0$ 是零预算可行恢复，所以必须有 $e(T_0)=E_0$。第317节的全部最优者分类于是使 $T_0\in\mathcal P_0$。

若到 $\mathcal P_0$ 的距离不对全部最优选择趋零，就可取一列距离有固定正下界的最优矩阵，再由上述紧性子列得到矛盾。因此第一项一致成立。奇异值连续性随即给出

$$
s_1(R)\to1,\qquad s_2(R),s_3(R)\to0.
\tag{329.5}
$$

第315节则在每个内部预算上给出可逆性和精确边界条件

$$
s_3=s_1s_2.
\tag{329.6}
$$

尤其 $s_3/s_2\to1$。这条关系只约束两个小奇异值的相对行为，尚未确定它们与预算的比例。

以下在任意趋于一个固定 $P_u$ 的最优子列上计算该比例；全部极限常数最终与子列选择无关。取 $T_j$ 最大奇异值的单位右、左奇异向量 $w_j,v_j$，使

$$
T_jw_j=s_{1,j}v_j,
\qquad w_j\to u,\quad v_j\to u.
\tag{329.7}
$$

这种符号选择存在：最大奇异值在极限的 $1$ 附近单重，$T_j^{\mathsf T}T_j\to P_u$，故先选 $w_j\cdot u>0$，再令 $v_j=T_jw_j/s_{1,j}$。不需要选择连续的两个较小奇异向量。

对任一 $b\in\mathbb R^3$，奇异值分解给出

$$
\begin{aligned}
\left(\frac{s_2}{s_1}\right)^2(w\cdot b)^2
+\|(I-ww^{\mathsf T})b\|_2^2
&\le s_2^2\|T^{-\mathsf T}b\|_2^2\\
&\le
\left(\frac{s_2}{s_1}\right)^2(w\cdot b)^2
+\left(\frac{s_2}{s_3}\right)^2
\|(I-ww^{\mathsf T})b\|_2^2.
\end{aligned}
\tag{329.8}
$$

这里出现的是右奇异方向 $w$：若 $T=U\operatorname{diag}(s_i)V^{\mathsf T}$，则 $T^{-\mathsf T}=U\operatorname{diag}(s_i^{-1})V^{\mathsf T}$。左侧输出旋转不改变范数。式（329.8）也避免了较小奇异子空间标架可能旋转的问题。

由式（329.5）至（329.7），两侧都趋于 $\|(I-P_u)b\|_2^2$。对有限个符号角点取最大值，并使用第281节的精确逆转置公式，得到

$$
\left(\frac{s_2}{r_*(T)}\right)^2
=s_2^2\max_\sigma\|T^{-\mathsf T}b_\sigma\|_2^2
\longrightarrow
\max_\sigma\|(I-P_u)b_\sigma\|_2^2
=A-m=\beta^2.
\tag{329.9}
$$

因为 $\beta>0$，可取平方根及倒数，得到 $r_*(T)/s_2\to1/\beta$。再用可行性 $r_*(T)\le R$，便有

$$
s_2\le\beta R[1+o(1)].
\tag{329.10}
$$

该式对所有最优选择一致：若失败，可再次取紧性子列及其零预算极限，按相同论证推出矛盾；全部极限方向具有相同的 $m$。

现在建立误差下界。将矩阵分为

$$
T=s_1vw^{\mathsf T}+B,
\qquad v^{\mathsf T}B=0,\quad Bw=0,\quad \|B\|_{\rm op}=s_2.
\tag{329.11}
$$

对原任务的第 $i$ 列，先向 $v^\perp$ 正交投影，再用反三角不等式，得

$$
\begin{aligned}
\|(I-T)e_i\|_2
&\ge\|(I-vv^{\mathsf T})e_i-Be_i\|_2\\
&\ge\sqrt{1-v_i^2}-s_2\sqrt{1-w_i^2}.
\end{aligned}
\tag{329.12}
$$

最后一步使用 $Bw=0$，所以 $\|Be_i\|_2\le s_2\|(I-ww^{\mathsf T})e_i\|_2$。置

$$
c_i(x)=\frac{a_i}{2}\sqrt{1-x_i^2}
\quad(\|x\|_2=1).
$$

沿式（329.7）的子列，连续性给出
$h_j:=\max_i|c_i(v_j)-c_i(w_j)|\to0$。式（329.12）于是给出

$$
\begin{aligned}
e(T_j)
&\ge\max_i\{c_i(v_j)-s_{2,j}c_i(w_j)\}\\
&\ge(1-s_{2,j})\max_i c_i(v_j)-s_{2,j}h_j\\
&=(1-s_{2,j})e(P_{v_j})-s_{2,j}h_j\\
&\ge E_0-E_0s_{2,j}-s_{2,j}h_j.
\end{aligned}
\tag{329.13}
$$

这里 $s_{2,j}\le1$，而每个 $P_{v_j}$ 都是零残差的完全退相干通道，可由第281节实际实现，所以 $e(P_{v_j})\ge E_0$。这一步不要求 $P_{v_j}$ 本身最优，也不要求 $v_j-u$ 或 $w_j-u$ 以指定速度趋零。它只需要左右方向具有相同极限。

由式（329.10），$s_{2,j}=O(R_j)$，所以式（329.13）成为

$$
\widehat G_a(R_j)\ge E_0-E_0\beta R_j+o(R_j).
\tag{329.14}
$$

任意最优序列都能按上述方式取子列，且所有子列给出相同系数。因此该下界与式（329.4）共同证明完整的式（329.2），而非仅证明某个子列极限。

最后，利用已经确定的实际值展开，再回到式（329.13），得到

$$
E_0\beta R_j+o(R_j)
=E_0-\widehat G_a(R_j)
\le E_0s_{2,j}+o(s_{2,j}).
$$

结合 $s_{2,j}=O(R_j)$ 及式（329.10），迫使 $s_{2,j}/R_j\to\beta$。式（329.6）和 $s_1\to1$ 随后给出 $s_3/R\to\beta$。将这个结论代入式（329.9），得到 $r_*(T_R)/R\to1$。相同子列反证使这些结论对全部最优选择一致。

对任何原实际最优因子对，第281节给出
$r_*(T_R)\le r(\mathcal E_R)\le R$。除以 $R$ 并夹逼，便得到原编码残差的比值极限。证毕。

这一斜率是第317节可达曲线与任意最优通道下界共同确定的。证明使用标准奇异值分解、紧性和投影不等式；新增的任务结论还表明，所有最优恢复的两个横向奇异值都以同一精确速率展开。结论针对每个固定正半径模型，不提供跨零半径退化的统一余项，也不确定完整小预算曲线、二阶系数或最优方向的收敛速率。
