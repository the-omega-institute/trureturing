# 情境时空算术的量子扩展：实对称、编码与恢复

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](245_263_INFORMATION_COST_AND_SPECTRA.md) · [续卷](284_306_RECOVERY_BUDGET_ENDPOINTS.md)


<a id="entry-876"></a>

## 追加锚（本行以下为增补区）

<a id="section-264"></a>

## 264. 固定全部特征值的解析曲线仍有非交换阶优势

第262节的一般曲线允许特征值和特征方向共同改变。本节固定两个特征值，只允许特征方向变化。在同一个全实轴矩阵二阶上界下，这个更小的类仍然达到三分之一次幂的信息阶。

**定义 264.1（固定谱的允许类）。** 对 $0<\eta\le1$，记

$$
C_\eta=\operatorname{diag}(1,\eta).
\tag{264.1}
$$

令 $\mathcal U_\eta$ 为全实轴上的 $C^2$ 二维密度曲线，满足

$$
\operatorname{spec}\rho(t)=\{3/4,1/4\},
\qquad \rho''(t)\preceq C_\eta
\quad(t\in\mathbb R).
\tag{264.2}
$$

记名义点信息的上确界为 $F_\eta^{\rm iso}$。其中要求矩阵元可延拓成整函数的子类，其上确界记为 $F_\eta^{\rm iso,ent}$。

**定理 264.2（固定谱下的三分之一次幂阶）。** 存在与 $\eta$ 无关的 $k_{r}>0$ 和 $\eta_0>0$，使

$$
k_{r}\eta^{1/3}
\le F_\eta^{\rm iso,ent}
\le F_\eta^{\rm iso}
\le C_*\eta^{1/3}
\qquad(0<\eta<\eta_0).
\tag{264.3}
$$

其中 $C_*=4(1/4+\sqrt{2/3})^2<5$，不要求该常数最优。

证明。 先直接证明上界。写任意允许曲线为 $\rho=I/2+\boldsymbol u\cdot\boldsymbol\sigma$，其中 $|\boldsymbol u|=b=1/4$。因 $\boldsymbol u\cdot\boldsymbol u'=0$，矩阵 $S=2\boldsymbol u'\cdot\boldsymbol\sigma$ 满足 SLD 方程，从而

$$
I_Q=4|\boldsymbol u'|^2.
\tag{264.4}
$$

记 $z=u_z$。矩阵上界的对角元及行列式给出

$$
-\eta\le z''\le1,\qquad
|\boldsymbol u''|^2\le\eta+(1-\eta)z''.
\tag{264.5}
$$

对全实轴上的非负函数 $b-z$ 使用标量正性界，得到 $z'^2\le2\eta(b-z)\le4b\eta=\eta$。因此

$$
\int_{-h}^h|\boldsymbol u''|^2
\le2h\eta+2\sqrt\eta.
\tag{264.6}
$$

两端的向量差长至多为 $2b$。应用第262节明确给出的三角核差商恒等式，其核的平方积分为 $h/6$，得到

$$
|\boldsymbol u'(0)|
\le\frac bh+\sqrt{\frac{\eta h^2}{3}+\frac{\sqrt\eta\,h}{3}}.
\tag{264.7}
$$

取 $h=\eta^{-1/6}$ 并使用 $0<\eta\le1$，可知

$$
I_Q(\rho_0)
\le4\left(b+\sqrt{\frac23}\right)^2\eta^{1/3}
=C_*\eta^{1/3}.
\tag{264.8}
$$

以下构造下界，并在解析化时保持特征值精确不变。

置 $b=1/4$。固定实值函数 $F\in C_c^\infty((-1,1))$，满足 $F(0)=0$、$F'(0)=1$，记

$$
M_1=\|F'\|_\infty,\qquad
M_2=\|F''\|_\infty,\qquad
K_0=b(M_2+M_1^2)>0,
\qquad k=16K_0^2+1.
\tag{264.9}
$$

另取 $G\in C_c^\infty((-2,2))$，满足 $0\le G\le1$ 且 $G=1$ 于 $[-1,1]$，以及非零 $B\in C_c^\infty((0,1))$，满足 $0\le B\le1$。记

$$
J_G=\int G>0,\qquad m_B=\int B>0.
\tag{264.10}
$$

固定充分小的 $r>0$，使 $4r^2/m_B\le b/16$。对每个正 $\eta$ 定义

$$
v=r\sqrt\eta,
\qquad T=\left(\frac{kJ_G}{v}\right)^{1/3},
\qquad L=\frac{4v}{\eta m_B},
\qquad\phi(t)=F(t/T).
\tag{264.11}
$$

令

$$
g(t)=\frac{k}{T^4}G(t/T)
-\frac\eta4 B\!\left(\frac{t-3T}{L}\right),
\qquad
z(t)=\int_{-\infty}^t(t-s)g(s)\,ds.
\tag{264.12}
$$

正、负两项分别支撑于 $[-2T,2T]$ 与 $[3T,3T+L]$，积分分别为 $v$ 与 $-v$。所以 $z'$ 从零增加到 $v$，再下降到零，全程非负。由此

$$
0\le z(t)\le5Tv+vL
=5Tv+\frac{4r^2}{m_B}.
\tag{264.13}
$$

由于 $Tv=O(\eta^{1/3})$，对所有充分小的 $\eta$，有

$$
0\le z\le b/2,\qquad
0\le z'\le v,\qquad
-\eta/4\le g=z''\le k/T^4\le1/4.
\tag{264.14}
$$

函数 $z$ 光滑，并在左右两个尾部各为常值。定义

$$
a(z)=\sqrt{b^2-z^2},\qquad
w(t)=a(z(t))e^{-i\phi(t)},\qquad
\rho^{(0)}(t)=
\begin{pmatrix}
1/2+z(t)&w(t)\\
\overline{w(t)}&1/2-z(t)
\end{pmatrix}.
\tag{264.15}
$$

因 $|w|^2+z^2=b^2$，两个特征值始终精确等于 $1/2\pm b$，即 $3/4,1/4$。

现证明矩阵上界还有一个对全参数有效的正余量。在 $0\le z\le b/2$ 上，

$$
|a'(z)|\le A_1=1/\sqrt3,
\qquad
|a''(z)|\le A_2=\frac8{3\sqrt3\,b}.
\tag{264.16}
$$

两次求导并使用三角不等式，得到

$$
|w''|\le
A_2v^2+A_1|g|+2A_1v|\phi'|
+b\bigl(|\phi''|+|\phi'|^2\bigr).
\tag{264.17}
$$

在相位变化的支撑 $|t|<T$ 内，$g=k/T^4$，而 $v=kJ_G/T^3$，故

$$
|w''|
\le\frac{K_0}{T^2}
+\frac{A_1k+2A_1kJ_GM_1}{T^4}
+\frac{A_2k^2J_G^2}{T^6}.
\tag{264.18}
$$

对充分大的 $T$，右侧至多为 $2K_0/T^2$。由 $k\ge16K_0^2$，

$$
|w''|^2\le\frac g4\le\frac{\eta+g}{4}.
\tag{264.19}
$$

在相位支撑外，$\phi$ 及其导数为零，所以（264.17）简化为

$$
|w''|\le A_2r^2\eta+A_1|g|.
\tag{264.20}
$$

当 $g\ge0$ 时，其平方至多为 $2A_2^2r^4\eta^2+2A_1^2g^2$。因为 $\eta\to0$ 且 $\sup g\to0$，该式对充分小的 $\eta$ 至多为 $(\eta+g)/4$。当 $g<0$ 时，$|g|\le\eta/4$，故平方至多为 $(A_2r^2+A_1/4)^2\eta^2$，也最终小于 $(\eta+g)/4$，因为 $\eta+g\ge3\eta/4$。于是（264.19）在整个实轴成立。

从而

$$
D(t)=C_\eta-(\rho^{(0)})''(t)
=\begin{pmatrix}
1-g&-w''\\
-\overline{w''}&\eta+g
\end{pmatrix}
\tag{264.21}
$$

满足 $1-g\ge3/4$、$\eta+g\ge3\eta/4$，并且

$$
\det D\ge\frac12(\eta+g)\ge\frac{3\eta}{8},
\qquad\operatorname{Tr}D=1+\eta\le2.
\tag{264.22}
$$

两个特征值为正，最大特征值至多为迹。因此

$$
C_\eta-(\rho^{(0)})''(t)
\succeq\frac{3\eta}{16}I
\quad(t\in\mathbb R).
\tag{264.23}
$$

下面计算信息。令 $\chi(t)=\arcsin(z(t)/b)$，则 $0\le\chi\le\pi/6$，并写

$$
\rho^{(0)}=I/2+\boldsymbol u\cdot\boldsymbol\sigma,
\qquad
\boldsymbol u=b(\cos\chi\cos\phi,\cos\chi\sin\phi,\sin\chi).
\tag{264.24}
$$

因为 $\boldsymbol u\cdot\boldsymbol u'=0$，Pauli 乘法关系直接表明 $S=2\boldsymbol u'\cdot\boldsymbol\sigma$ 满足 SLD 方程。因此

$$
I_Q(\rho^{(0)}_t)
=4|\boldsymbol u'(t)|^2
=4b^2\bigl(\chi'(t)^2+\cos^2\chi(t)\,\phi'(t)^2\bigr).
\tag{264.25}
$$

在中心 $\phi'(0)=1/T$ 且 $\cos^2\chi(0)\ge3/4$，所以

$$
I_Q(\rho^{(0)}_0)
\ge\frac{3b^2}{T^2}
=3b^2\left(\frac r{kJ_G}\right)^{2/3}\eta^{1/3}.
\tag{264.26}
$$

为得到整函数矩阵元，此处平滑两个实角函数，随后重建密度矩阵。对每个固定 $\eta$，$\chi,\phi$ 及其前两阶导数均有界且一致连续；导数在有限区间之外为零。令 $g_\epsilon$ 为归一化高斯核，置

$$
\chi_\epsilon=g_\epsilon*\chi,
\qquad\phi_\epsilon=g_\epsilon*\phi,
\qquad
\boldsymbol u_\epsilon
=b(\cos\chi_\epsilon\cos\phi_\epsilon,
\cos\chi_\epsilon\sin\phi_\epsilon,
\sin\chi_\epsilon),
\tag{264.27}
$$

并取 $\rho_\epsilon=I/2+\boldsymbol u_\epsilon\cdot\boldsymbol\sigma$。两个角函数延拓成整函数，三角函数的复合仍为整函数，因此矩阵元也是整函数。对实参数，角函数为实数，$|\boldsymbol u_\epsilon|=b$ 精确成立，故特征值和谱下界完全保留。

高斯逼近在这两个角函数的 $C^2$ 范数中一致收敛。链式法则与实轴上有界的三角函数导数于是给出 $\rho_\epsilon\to\rho^{(0)}$ 的全实轴一致 $C^2$ 收敛。为每个固定 $\eta$ 选择充分小的 $\epsilon$，可同时保证

$$
\sup_t\|\rho_\epsilon''(t)-(\rho^{(0)})''(t)\|_{\rm op}
\le\frac{3\eta}{32}
\tag{264.28}
$$

及中心信息至少保留（264.26）的一半。这里信息的一致谱下界固定为 $1/4$，也可直接用（264.25）的角函数形式判断一阶数据的连续性。由（264.23），

$$
C_\eta-\rho_\epsilon''(t)\succeq\frac{3\eta}{32}I,
\qquad
I_Q((\rho_\epsilon)_0)
\ge k_{r}\eta^{1/3},
\quad
k_{r}=\frac{3b^2}{2}\left(\frac r{kJ_G}\right)^{2/3}>0.
\tag{264.29}
$$

这证明了整函数子类中的下界。所有轮廓函数与常数先固定，再取充分小 $\eta$，最后按该 $\eta$ 选取平滑宽度；矩阵上界和精确特征值没有放宽。证毕。

上述解析化没有把密度矩阵作凸平均；密度的凸平均一般不能保持特征值。它先逼近角函数，再利用三角恒等式保留固定谱，并以（264.23）的严格矩阵余量吸收二阶近似误差。

**推论 264.3（固定谱变化与更大的对易比较类）。** 对上述构造的每条实参数曲线，可以写成

$$
\rho(t)=U(t)\operatorname{diag}(3/4,1/4)U(t)^*,
\quad
U(t)=e^{-i\phi(t)\sigma_z/2}
e^{-i(\pi/2-\chi(t))\sigma_y/2},
\tag{264.30}
$$

解析化后使用 $\chi_\epsilon,\phi_\epsilon$ 得到相同结论。因而所有只依赖特征值的量沿曲线恒定，但与第263节允许特征值变化的全部对易曲线相比，仍有

$$
\frac{F_\eta^{\rm iso,ent}}{F_{\rm com}(1/4,\eta)}
=\Theta(\eta^{-1/6}).
\tag{264.31}
$$

证明。 Pauli 旋转公式给出（264.30）。固定谱立即使所有谱函数恒定。再结合（264.3）与 $F_{\rm com}(1/4,\eta)=2\sqrt\eta$ 得到（264.31）。证毕。

作为更小的特殊情形，连续且两两对易的固定谱二维密度族必为常值：其共同特征基固定，而两个离散特征值不能沿连续参数互换。因此（264.31）使用的是第263节更大的对易比较类，其阶差不依赖于把比较对象预先限制成常值。

这里的酉表示描述准备曲线的数学结构，未施加哈密顿量、物理能量、带宽或原处理器的矩与分项预算约束。固定谱没有消去关系响应：本节的信息变化全部来自特征方向的组合，而精确矩阵二阶条件仍由（264.23）、（264.28）共同保证。

<a id="entry-878"></a>

## 追加锚（本行以下为增补区）

<a id="section-265"></a>

## 265. 固定实基底的平面限制与不可消去的方向变化

第264节在固定全部特征值时保留了非交换阶优势。非交换性本身还不能解释这项优势：同一个 Bloch 大圆上的状态通常已经不对易，但它们仍能在一个固定基底中同时写成实矩阵。本节允许这个固定基底任意选择，比较平面轨迹与一般固定谱轨迹。

**定义 265.1（可在固定基底中取实的曲线类）。** 对 $0<\eta\le1$，在定义264.1的允许类中，进一步要求存在一个不依赖实参数 $t$ 的酉矩阵 $V$，使

$$
V\rho(t)V^*\in M_2(\mathbb R)
\quad(t\in\mathbb R).
\tag{265.1}
$$

$V$ 可以依赖整条曲线和 $\eta$。记这一类的名义 SLD 信息上确界为 $F_\eta^{\rm real}$，其中矩阵元可延拓成整函数的子类对应 $F_\eta^{\rm real,ent}$。曲线仍在原基底中满足

$$
\operatorname{spec}\rho(t)=\{3/4,1/4\},
\qquad \rho''(t)\preceq C_\eta=\operatorname{diag}(1,\eta)
\quad(t\in\mathbb R).
\tag{265.2}
$$

这里没有要求 $V$ 同时对角化 $C_\eta$。

**定理 265.2（全部固定实基底上的二分之一次幂阶）。** 对 $0<\eta\le1$，

$$
\boxed{
\sqrt\eta
\le F_\eta^{\rm real,ent}
\le F_\eta^{\rm real}
\le\min\{1,256\sqrt\eta\}.
}
\tag{265.3}
$$

证明。 置 $b=1/4$，写 $\rho=I/2+\boldsymbol u\cdot\boldsymbol\sigma$。固定谱条件等价于 $|\boldsymbol u|=b$，而第264节的直接 SLD 计算给出

$$
I_Q=4|\boldsymbol u'|^2.
\tag{265.4}
$$

先处理 $\rho(t)$ 本身在 $C_\eta$ 的特征基中为实矩阵的情形。此时 $\boldsymbol u=(x,0,z)$ 在半径 $b$ 的圆上。实轴单连通，故有全域 $C^2$ 角函数使

$$
x=b\sin\theta,\qquad z=-b\cos\theta.
\tag{265.5}
$$

也可从任一点选择初始角，再积分 $\theta'=(xz'-zx')/b^2$ 得到此提升。先给出适用于全部固定谱曲线的一个点态估计。由 $\rho''\preceq C_\eta\preceq I$，且 $\rho''=\boldsymbol u''\cdot\boldsymbol\sigma$，可知 $|\boldsymbol u''|\le1$。对 $|\boldsymbol u|^2=b^2$ 两次求导，得到 $|\boldsymbol u'|^2=-\boldsymbol u\cdot\boldsymbol u''\le b$，故 $I_Q\le4b=1$。特别地，下面可以使用较宽松的全域速度界：

$$
4b^2\theta'^2=I_Q\le1\le4,
\qquad |\theta'|\le4.
\tag{265.6}
$$

上界矩阵差的对角元及行列式同时给出

$$
z''\ge-\eta,\qquad
b^2(\theta'^4+\theta''^2)
\le\eta+(1-\eta)b(\cos\theta\,\theta'^2+\sin\theta\,\theta'').
\tag{265.7}
$$

非负函数 $b-z$ 的二阶导数至多为 $\eta$，所以标量正性界给出

$$
z'^2\le2\eta(b-z)\le4b\eta=\eta.
\tag{265.8}
$$

另一方面，从（265.7）丢去左侧非负的 $\theta'^4$，并用 $|\sin\theta|\le|\theta|$，得到

$$
|\theta''|^2
\le16\eta+4\theta'^2+4|\theta|\,|\theta''|.
\tag{265.9}
$$

解这个关于 $|\theta''|$ 的二次不等式，并使用平方根的次可加性，可得方便的估计

$$
|\theta''|
\le4\bigl(|\theta|+|\theta'|+\sqrt\eta\bigr).
\tag{265.10}
$$

改变角函数的整数周数，使 $\theta(0)\in[-\pi,\pi]$。若 $|\theta(0)|\ge1/4$，在 $\sin\theta(0)\ne0$ 时，把（265.8）的第一式除以 $b^2\sin^2\theta(0)$，得到

$$
\theta'(0)^2
\le\frac{2\eta}{b(1-\cos\theta(0))}.
\tag{265.11}
$$

若 $\theta(0)=\pm\pi$，则 $z''(0)=-b\theta'(0)^2\ge-\eta$，仍给出同一个界。由 $1-\cos(1/4)\ge1/48$，

$$
I_Q(\rho_0)\le96\eta\le96\sqrt\eta.
\tag{265.12}
$$

余下只需处理 $|\theta(0)|<1/4$。令 $h=1/32$。式（265.6）保证

$$
|\theta(t)|\le3/8\qquad(|t|\le h).
\tag{265.13}
$$

必要时反转实参数，使 $\theta'(0)=v\ge0$；二阶矩阵上界不因此改变。若 $v\le\sqrt\eta$，则信息至多为 $\eta/4$。若 $|\theta(0)|\ge hv$，使用 $|\sin\theta(0)|\ge|\theta(0)|/2$，由（265.8）得到

$$
\sqrt\eta\ge |z'(0)|\ge\frac{bhv^2}{2},
\qquad
I_Q(\rho_0)\le\frac{8b}{h}\sqrt\eta=64\sqrt\eta.
\tag{265.14}
$$

最后考虑 $v>\sqrt\eta$ 且 $|\theta(0)|<hv$。置

$$
J(t)=|\theta(t)|+|\theta'(t)|+\sqrt\eta.
\tag{265.15}
$$

由（265.10），几乎处处有 $|J'|\le5J$。对正、负两个参数方向分别积分，

$$
J(t)\le e^{5|t|}J(0)
<e^{5h}(2+h)v<3v
\quad(|t|\le h).
\tag{265.16}
$$

最后一个常数估计可直接用 $e^{5/32}\le32/27$，于是乘积至多为 $65/27<3$。因此 $|\theta''|\le12v$，并且

$$
\theta'(t)\ge v-12vh\ge v/2
\quad(|t|\le h).
\tag{265.17}
$$

若 $\theta(0)\ge0$，取 $t_*=h$；否则取 $t_*=-h$。式（265.17）给出 $|\theta(t_*)|\ge hv/2$，再由（265.13），

$$
\sqrt\eta
\ge |z'(t_*)|
=b|\sin\theta(t_*)|\,|\theta'(t_*)|
\ge\frac{bhv^2}{8}.
\tag{265.18}
$$

所以

$$
I_Q(\rho_0)=4b^2v^2
\le\frac{32b}{h}\sqrt\eta
=256\sqrt\eta.
\tag{265.19}
$$

这证明了在上界特征基中取实的情形。

现在处理任意固定基底。式（265.1）等价于整条向量曲线 $\boldsymbol u(t)$ 包含于某个过原点的固定二维平面 $P$：实矩阵的 Pauli 向量在 $xz$ 平面内，固定酉共轭则对应一个固定旋转。写

$$
C_\eta=c_0I+\boldsymbol c\cdot\boldsymbol\sigma,
\qquad
c_0=\frac{1+\eta}{2},
\qquad
\boldsymbol c=(0,0,(1-\eta)/2).
\tag{265.20}
$$

令 $\boldsymbol c_P$ 为 $\boldsymbol c$ 到 $P$ 的正交投影，定义辅助正定矩阵

$$
\widehat C
=\sqrt{\eta+|\boldsymbol c_P|^2}\,I
+\boldsymbol c_P\cdot\boldsymbol\sigma.
\tag{265.21}
$$

对于任意 $\boldsymbol k\in P$ 及 $H=\boldsymbol k\cdot\boldsymbol\sigma$，有

$$
\det(C_\eta-H)
=\eta+2\boldsymbol c_P\cdot\boldsymbol k-|\boldsymbol k|^2
=\det(\widehat C-H).
\tag{265.22}
$$

两个 Hermitian 差矩阵的迹均严格为正。在二维中，非负行列式和正迹等价于半正定，因此

$$
C_\eta-H\succeq0
\quad\Longleftrightarrow\quad
\widehat C-H\succeq0
\qquad(\boldsymbol k\in P).
\tag{265.23}
$$

这是一条在指定平面内的约束等价，没有把原矩阵上界直接投影后当成新上界。

将 $P$ 旋转到 $xz$ 平面后，所有状态和 $\widehat C$ 都是实矩阵。再以实正交矩阵对角化 $\widehat C$，仍保持所有状态为实矩阵。其两个特征值满足

$$
\lambda_+\ge\lambda_->0,
\qquad\lambda_+\lambda_-=\det\widehat C=\eta.
\tag{265.24}
$$

以该固定基变换后的曲线记为 $\rho_1$，并令

$$
\widetilde\rho(s)=\rho_1(s/\sqrt{\lambda_+}),
\qquad r=\lambda_-/\lambda_+\in(0,1].
\tag{265.25}
$$

此曲线保持精确谱，且在同一实基底中满足 $\widetilde\rho''\preceq\operatorname{diag}(1,r)$。信息在这次参数变换下除以 $\lambda_+$，因此已证的（265.19）给出

$$
I_Q(\rho_0)
\le256\lambda_+\sqrt r
=256\sqrt\eta.
\tag{265.26}
$$

该界与平面的方向无关，故覆盖定义265.1中允许的全部固定基底。

最后给出整函数下界。取

$$
\boldsymbol u(t)=b(\cos\omega t,\sin\omega t,0),
\qquad
\omega^2=\frac{\sqrt\eta}{b},
\qquad
\rho(t)=I/2+\boldsymbol u(t)\cdot\boldsymbol\sigma.
\tag{265.27}
$$

其特征值精确固定，矩阵元为整函数。由 $\boldsymbol u''=-\omega^2\boldsymbol u$，

$$
\det(C_\eta-\rho'')=\eta-b^2\omega^4=0,
\qquad
\operatorname{Tr}(C_\eta-\rho'')=1+\eta>0.
\tag{265.28}
$$

所以原矩阵上界在全实轴成立。整条曲线在 $xy$ 平面内，经过一个固定酉旋转即能同时取实，属于所需比较类。其信息为

$$
I_Q=4b^2\omega^2=4b\sqrt\eta=\sqrt\eta.
\tag{265.29}
$$

由此得到（265.3）的全部不等式。证毕。

**推论 265.3（一般固定谱曲线与全部平面曲线的阶差）。** 当 $\eta\downarrow0$，

$$
\frac{F_\eta^{\rm iso,ent}}{F_\eta^{\rm real,ent}}
=\Theta(\eta^{-1/6}).
\tag{265.30}
$$

证明。 第264节给出分子的上下界为正固定常数乘 $\eta^{1/3}$；（265.3）给出分母的上下界为正固定常数乘 $\eta^{1/2}$。上下界分别组合即得结论。证毕。

同一 $256\sqrt\eta$ 上界还覆盖任意固定仿射平面内的轨迹，虽然这种轨迹未必能在固定基底中同时取实。确实，写 $\boldsymbol u=\boldsymbol p+\boldsymbol v$，其中 $\boldsymbol v(t)\in P$、$\boldsymbol p\perp P$ 为常向量，则 $|\boldsymbol v|=R=\sqrt{b^2-|\boldsymbol p|^2}$。$R=0$ 时曲线恒定；否则令 $\widehat{\boldsymbol u}=(b/R)\boldsymbol v$。对应密度保持所需固定谱，轨迹在过原点的平面中，矩阵上界为 $(b/R)C_\eta$。通过参数缩放，（265.26）对正数 $a$ 倍上界给出 $I_Q\le256a\sqrt\eta$；取 $a=b/R$，再按一阶向量长度换回原曲线，得到

$$
I_Q(\rho_0)
\le256\frac Rb\sqrt\eta
\le256\sqrt\eta.
\tag{265.31}
$$

因此，第264节中取得相应下界的曲线，在充分小的 $\eta$ 下不能通过任何固定二维基变换使整条曲线同时取实，也不能包含于任何固定仿射平面。这比两两不对易更严格：式（265.27）的大圆曲线已经通常不对易，但其信息仍只有二分之一次幂阶。相反，仅有非平面性也不保证任意一条曲线达到三分之一次幂阶；这里比较的是明确约束下的类上确界。

固定基底中同时取实的统计模型已有反酉对称的表述。Jisho Miyazaki 与 Keiji Matsumoto，*Imaginarity-free quantum multiparameter estimation*，Quantum 6（2022），665，[原文 arXiv:2010.15465v3](https://arxiv.org/pdf/2010.15465v3)，第3.1节定义1及附录A.2分别讨论参数无关的反酉对称与过原点的 Bloch 平面模型。本节沿用这项既有几何对应；上述证明处理额外固定矩阵二阶约束下的信息阶，并另外覆盖不经过原点的仿射平面。

本节沿用第261—264节的 SLD、Pauli 表示和标量正性背景。比较始终固定二维表示、精确谱和原矩阵二阶约束；没有排除更高维实表示，也没有限制随参数变化的基底。它不把固定基底下的复数分量单独当作资源，更不声称排除了所有实量子描述。所得区别是：在这个准备曲线问题中，任何固定平面都限制了可取得的信息阶，而一般固定谱方向变化可以超过这一限制。哈密顿量、物理能量、带宽与原处理器附加约束仍不在本节的实现范围内。

<a id="entry-880"></a>

## 追加锚（本行以下为增补区）

<a id="section-266"></a>

## 266. 精确固定谱下的布居摆幅与信息阶过渡

第265节区分了固定平面轨迹与一般固定谱轨迹。本节给出另一个有数值尺度的限制：沿矩阵上界的特征方向，允许对角布居总共改变多少。两个特征值依然完全不变；改变的是状态相对于给定上界方向的布居。

**定义 266.1（带布居摆幅限制的允许类）。** 固定 $b=1/4$。对 $0<\eta\le1$、$0\le\Delta\le b/2$，考虑全实轴上的 $C^2$ 二维密度曲线

$$
\rho(t)=I/2+\boldsymbol u(t)\cdot\boldsymbol\sigma,
\qquad |\boldsymbol u(t)|=b,
\qquad \rho''(t)\preceq C_\eta=\operatorname{diag}(1,\eta).
\tag{266.1}
$$

记 $z(t)=u_z(t)$，并要求

$$
\operatorname{osc}_{\mathbb R}z
:=\sup_{t\in\mathbb R}z(t)-\inf_{t\in\mathbb R}z(t)
\le\Delta.
\tag{266.2}
$$

记这一类的名义 SLD 信息上确界为 $F(\eta,\Delta)$，整函数矩阵元子类对应 $F_{\rm ent}(\eta,\Delta)$。式（266.2）也正是对角元 $\rho_{11}=1/2+z$ 的摆幅上界；它与固定特征值条件是不同约束。

**定理 266.2（统一二参数信息阶）。** 存在固定常数 $c>0$、$\eta_0>0$，使对所有 $0<\eta<\eta_0$ 和 $0\le\Delta\le b/2$，

$$
\boxed{
c\bigl(\sqrt\eta+(\eta\Delta)^{1/3}\bigr)
\le F_{\rm ent}(\eta,\Delta)
\le F(\eta,\Delta)
\le6\bigl(\sqrt\eta+(\eta\Delta)^{1/3}\bigr).
}
\tag{266.3}
$$

此外，对所有 $0<\eta\le1$，零摆幅端点精确满足

$$
F_{\rm ent}(\eta,0)=F(\eta,0)=\sqrt\eta.
\tag{266.4}
$$

证明。 先证明上界。沿用第264节的 SLD 与行列式计算，

$$
I_Q=4|\boldsymbol u'|^2,
\qquad
|\boldsymbol u''|^2\le\eta+(1-\eta)z'',
\qquad z''\ge-\eta.
\tag{266.5}
$$

令 $z_{\max}=\sup_{\mathbb R}z$；不要求此上确界取到。非负函数 $z_{\max}-z$ 的二阶导数至多为 $\eta$，所以

$$
z'^2\le2\eta(z_{\max}-z)\le2\eta\Delta.
\tag{266.6}
$$

对（266.5）在 $[-h,h]$ 上积分，

$$
\int_{-h}^h|\boldsymbol u''|^2
\le2h\eta+2\sqrt{2\eta\Delta}.
\tag{266.7}
$$

端点弦长至多为 $2b$。第262节的三角核恒等式及其平方积分 $h/6$ 因而给出

$$
|\boldsymbol u'(0)|
\le\frac bh+
\sqrt{\frac{\eta h^2}{3}
+\frac{h\sqrt{2\eta\Delta}}{3}}.
\tag{266.8}
$$

置

$$
S=\Delta+\sqrt\eta,\qquad h=(\eta S)^{-1/6}.
\tag{266.9}
$$

由于 $S\ge\sqrt\eta$ 且 $S\ge\Delta$，

$$
\eta h^2\le(\eta S)^{1/3},
\qquad
h\sqrt{2\eta\Delta}\le\sqrt2\,(\eta S)^{1/3}.
\tag{266.10}
$$

代入可得

$$
I_Q(\rho_0)
\le4\left(b+\sqrt{\frac{1+\sqrt2}{3}}\right)^2(\eta S)^{1/3}
<6\bigl((\eta\Delta)^{1/3}+\sqrt\eta\bigr).
\tag{266.11}
$$

这里的上界对全部 $0<\eta\le1$ 有效，只使用有限窗口积分。

当 $\Delta=0$ 时，$z$ 恒定。令 $\boldsymbol w=(u_x,u_y)$，则 $|\boldsymbol w|=R=\sqrt{b^2-z^2}$ 也恒定。若 $R=0$，曲线恒定；否则（266.5）给出 $|\boldsymbol w''|\le\sqrt\eta$，故

$$
|\boldsymbol w'|^2=-\boldsymbol w\cdot\boldsymbol w''
\le R\sqrt\eta\le b\sqrt\eta.
\tag{266.12}
$$

于是 $I_Q\le4b\sqrt\eta=\sqrt\eta$。第265节的赤道匀速旋转

$$
\boldsymbol u(t)=b(\cos\omega t,\sin\omega t,0),
\qquad \omega^2=\sqrt\eta/b
\tag{266.13}
$$

具有整函数矩阵元、零布居摆幅，且信息精确等于 $\sqrt\eta$。这同时证明（266.4），并为任意允许 $\Delta$ 给出同一个下界。

下面在较大摆幅区间建立第二项的统一下界。保留第264节的固定光滑函数 $F,G,B$ 及常数 $k,J_G,m_B,K_0,A_1,A_2$，并记 $D_0=kJ_G$。选取固定 $\gamma>0$，使

$$
\frac{4\gamma^2}{m_B}\le\frac14.
\tag{266.14}
$$

再固定 $K\ge1$，使

$$
5D_0^{1/3}\gamma^{2/3}K^{-2/3}\le\frac14.
\tag{266.15}
$$

对 $\Delta>0$，令

$$
r=\gamma\sqrt\Delta,\qquad
v=\gamma\sqrt{\eta\Delta},\qquad
T=(D_0/v)^{1/3},\qquad
L=\frac{4v}{\eta m_B}.
\tag{266.16}
$$

使用同一个相位及正、负加速度构造：

$$
\phi(t)=F(t/T),
\qquad
g(t)=\frac{k}{T^4}G(t/T)
-\frac\eta4 B\!\left(\frac{t-3T}{L}\right),
\qquad
z(t)=\int_{-\infty}^t(t-s)g(s)\,ds.
\tag{266.17}
$$

两个脉冲的积分依次为 $v$、$-v$，所以 $z$ 从零单调增加到一个常值，并且

$$
0\le z(t)\le5Tv+vL
=5D_0^{1/3}\gamma^{2/3}(\eta\Delta)^{1/3}
+\frac{4\gamma^2}{m_B}\Delta.
\tag{266.18}
$$

若 $\Delta\ge K\sqrt\eta$，则（266.14）—（266.15）给出

$$
0\le z(t)\le\Delta/2\le b/4.
\tag{266.19}
$$

因此摆幅约束保留了固定比例的余量。

取 $w=\sqrt{b^2-z^2}e^{-i\phi}$，再按（264.15）组成密度矩阵 $\rho^{(0)}$，其两个特征值精确为 $3/4,1/4$。现在须使第264节的矩阵余量估计对这两个参数统一成立，而不是逐个固定 $\Delta$ 后才选择阈值。首先

$$
r\le r_{\max}:=\gamma\sqrt{b/2},
\qquad
T\ge\left(\frac{D_0}{\gamma\sqrt{\eta b/2}}\right)^{1/3}.
\tag{266.20}
$$

因此 $T\to\infty$ 对全部 $0<\Delta\le b/2$ 统一成立。相位支撑内的（264.18）只含固定的 $D_0$ 与轮廓常数；相位支撑外的（264.20）可统一用 $r_{\max}$ 代替 $r$。特别地，可一次选择 $\eta_0>0$，使所有这些参数对均有 $g\le1/4$，相位支撑内满足 $|w''|\le2K_0/T^2$，支撑外满足

$$
|w''|^2\le(\eta+g)/4.
\tag{266.21}
$$

具体地，支撑外 $g\ge0$ 时使用
$|w''|^2\le2A_2^2r_{\max}^4\eta^2+2A_1^2g^2$，而 $\sup g=k/T^4$ 一致趋零；$g<0$ 时使用
$|w''|^2\le(A_2r_{\max}^2+A_1/4)^2\eta^2$ 及 $\eta+g\ge3\eta/4$。这些条件均由同一个充分小的 $\eta_0$ 保证。（266.19）已独立确保所用幅度导数界的适用范围。于是第264节的行列式和迹计算逐式给出

$$
C_\eta-(\rho^{(0)})''(t)\succeq\frac{3\eta}{16}I
\quad(t\in\mathbb R).
\tag{266.22}
$$

中心相位导数为 $1/T$。同处的 SLD 计算给出

$$
I_Q(\rho^{(0)}_0)
\ge\frac{3b^2}{T^2}
=3b^2\left(\frac{\gamma}{D_0}\right)^{2/3}
(\eta\Delta)^{1/3}.
\tag{266.23}
$$

为得到整函数矩阵元，仍先以高斯核平滑实角函数 $\chi=\arcsin(z/b)$ 和 $\phi$，再以三角函数重建密度。对于每一个固定参数对 $(\eta,\Delta)$，全实轴 $C^2$ 逼近及（266.22）使我们可选取充分小的平滑宽度，同时保留原矩阵上界与至少一半的中心信息。特征值由重建恒等式精确保留。

摆幅约束也在这一步精确保留：由（266.19），

$$
0\le\chi(t)\le\arcsin\!\left(\frac{\Delta}{2b}\right).
\tag{266.24}
$$

高斯正平均保持这个区间，且正弦函数在该区间单调，故重建后的 $z_\epsilon=b\sin\chi_\epsilon$ 仍包含于 $[0,\Delta/2]$。因此，在 $\Delta\ge K\sqrt\eta$ 时，

$$
F_{\rm ent}(\eta,\Delta)\ge
\kappa(\eta\Delta)^{1/3},
\qquad
\kappa=\frac{3b^2}{2}
\left(\frac{\gamma}{D_0}\right)^{2/3}>0.
\tag{266.25}
$$

所有轮廓、$\gamma,K,\kappa,\eta_0$ 均独立于参数对；只有最后的平滑宽度允许依赖它。

当 $\Delta<K\sqrt\eta$ 时，
$\sqrt\eta+(\eta\Delta)^{1/3}\le(1+K^{1/3})\sqrt\eta$，赤道曲线已给出所需下界。在互补区间，取赤道下界与（266.25）的较大者，至少是目标和式的 $\min\{1,\kappa\}/2$ 倍。因此可取

$$
c=\min\left\{
\frac1{1+K^{1/3}},
\frac{\min\{1,\kappa\}}2
\right\}>0.
\tag{266.26}
$$

这完成统一下界及定理的证明。证毕。

**推论 266.3（趋近平面与保持阶优势的尺度）。** 对固定 $\beta>0$，令 $\Delta=\eta^\beta$；当 $\eta$ 充分小时，它属于允许范围。则

$$
F_{\rm ent}(\eta,\eta^\beta)
\asymp F(\eta,\eta^\beta)
\asymp
\eta^{\min\{1/2,(1+\beta)/3\}}.
\tag{266.27}
$$

特别地，当 $0<\beta<1/2$，与第265节全部固定实基底类的比较满足

$$
\frac{F_{\rm ent}(\eta,\eta^\beta)}
{F_\eta^{\rm real,ent}}
=\Theta\!\left(\eta^{(2\beta-1)/6}\right)
\longrightarrow\infty.
\tag{266.28}
$$

证明。 直接比较（266.3）中的两个幂次，并使用（265.3）的分母上下界。证毕。

更具体地，在 $0<\beta<1/2$ 时，构造（266.17）及其解析化的整条 $\boldsymbol u$ 轨迹都距赤道平面至多 $\eta^\beta/2$，但其信息下界相对于任意固定平面轨迹的统一上界仍有发散的比例。因此，几何上任意接近平面，并不在这个退化参数族中保证信息阶接近固定平面的极值；矩阵上界本身也随 $\eta$ 退化，比较对象的信息同时趋零。摆幅进入 $\Delta\lesssim\sqrt\eta$ 区间以后，两项才共同回到二分之一次幂阶。

曲线上的导数插值已有黎曼流形版本。Igor Parasyuk，*Landau–Kolmogorov type inequalities for curves on Riemannian manifolds*，Mathematical Inequalities & Applications 22（2019），433—443页，[原文](https://files.ele-math.com/articles/mia-22-31.pdf)，定理1—2，在正 Hessian 或球面小球条件下以协变加速度控制速度。这些是相关的既有背景；本节控制的是密度矩阵在线性空间中的二阶导数，其法向分量也参与 Loewner 约束，不能直接换成球面的协变加速度。式（266.3）的二参数估计由（266.5）—（266.26）证明，没有把流形上的插值思想本身作为新增结果。

本节的摆幅沿给定矩阵上界的特征方向测量，没有给出相对于任意平面的统一厚度定理。全部特征值始终固定；摆幅控制的是对角布居及方向变化，不是谱的变化。SLD、标量正性和有限窗口插值沿用前节的既有背景，二参数常数与全域构造由上述估计给出。这里未求出正摆幅下的精确最优系数，也未施加哈密顿量、物理能量、带宽或原处理器约束。

<a id="entry-882"></a>

## 追加锚（本行以下为增补区）

<a id="section-267"></a>

## 267. 共同反酉对称的平方符号与固定实基底的区别

第265节使用的是一条曲线能否在同一个固定基底中同时取实。在二维非简并谱情形，共同反酉对称可以给出这样的实结构。高维退化谱需要额外区分反酉算子的平方：保持整族状态不变的反酉算子，其平方可以是 $-I$，而基底复共轭的平方必须是 $I$。

下面给出四个满秩状态的明确构造，再将其实现为一条周期、整函数矩阵元且精确固定谱的曲线。

**定义 267.1（共同反酉对称与共轭）。** 对有限维 Hilbert 空间上的密度族 $\mathcal R$，共同反酉对称是反酉算子 $T$，满足

$$
T\rho T^{-1}=\rho
\qquad(\rho\in\mathcal R).
\tag{267.1}
$$

称反酉算子 $J$ 为共轭，如果 $J^2=I$。密度族能在一个固定正交基中同时写成实矩阵，当且仅当它有一个共同共轭：一个方向取该基中的逐项复共轭；另一个方向使用共轭的不动实子空间的正交基。这是实结构的通常对应。

**定理 267.2（有共同反酉对称但无共同实基底的固定谱族）。** 存在四维空间中的四个满秩密度矩阵，具有同一谱

$$
\{3/8,3/8,1/8,1/8\},
\tag{267.2}
$$

其所有共同反酉对称的平方都等于 $-I_4$。同一性质也由一条全实轴周期密度曲线实现，其矩阵元为整函数，且每个实参数处的谱均精确等于（267.2）。

证明。 在 $\mathbb C^2\otimes\mathbb C^2$ 中，令 $X,Y,Z$ 为标准 Pauli 矩阵，置

$$
G_1=X\otimes I_2,\qquad
G_2=Z\otimes I_2,\qquad
G_3=Y\otimes X,\qquad
G_4=Y\otimes Y.
\tag{267.3}
$$

这些矩阵满足

$$
G_j^*=G_j,\qquad G_j^2=I_4,\qquad
\operatorname{Tr}G_j=0,\qquad
G_jG_k=-G_kG_j\quad(j\ne k).
\tag{267.4}
$$

定义

$$
\rho_j=\frac14\left(I_4+\frac12G_j\right)
\qquad(j=1,2,3,4).
\tag{267.5}
$$

每个 $G_j$ 的特征值为 $1,-1$，各重数为二，故 $\rho_j$ 迹为一、严格正定，并有谱（267.2）。

令 $K$ 为标准基中的逐项复共轭，并置

$$
U=I_2\otimes Y,\qquad T=UK.
\tag{267.6}
$$

$U$ 是酉矩阵，且 $\overline U=-U$，所以

$$
T^2=U\overline U=-I_4.
\tag{267.7}
$$

$G_1,G_2,G_4$ 为实矩阵，而 $\overline{G_3}=-G_3$。另一方面，$U$ 与 $G_1,G_2,G_4$ 对易，并且 $UG_3U^*=-G_3$。于是对每个 $j$，

$$
U\overline{G_j}U^*=G_j,
\qquad T\rho_jT^{-1}=\rho_j.
\tag{267.8}
$$

下面证明这些状态没有共同共轭。先求共同复线性交换子。若复矩阵 $A$ 同时与 $G_1,G_2$ 对易，则把它写成以第一张量因子分块的矩阵，由与 $Z\otimes I_2$ 对易可知非对角块为零，再由与 $X\otimes I_2$ 对易可知两个对角块相等。因此

$$
A=I_2\otimes B
\tag{267.9}
$$

对某个 $2\times2$ 复矩阵 $B$ 成立。继续与 $G_3,G_4$ 对易，分别给出 $BX=XB$ 和 $BY=YB$。由于 $X,Y$ 生成全部 $2\times2$ 复矩阵代数，$B$ 为标量矩阵。因此

$$
\{A\in M_4(\mathbb C):[A,G_j]=0\ \forall j\}
=\mathbb C I_4.
\tag{267.10}
$$

这也正是四个 $\rho_j$ 的共同复线性交换子。

若 $J$ 是任意共同反酉对称，则 $JT^{-1}$ 是复线性酉算子，且与全部 $\rho_j$ 对易。由（267.10），必有 $J=\zeta T$，其中 $|\zeta|=1$。反酉性使标量在第二次作用时被共轭，所以

$$
J^2=\zeta\overline\zeta\,T^2=-I_4.
\tag{267.11}
$$

特别地，不存在平方为 $I_4$ 的共同共轭，也不存在使四个状态同时取实的固定基底。

为构造一条整函数曲线，取实向量

$$
\begin{aligned}
n_1(t)&=\cos t\cos2t,&
n_2(t)&=\sin t\cos2t,\\
n_3(t)&=\cos t\sin2t,&
n_4(t)&=\sin t\sin2t,
\end{aligned}
\qquad |n(t)|^2=1.
\tag{267.12}
$$

定义

$$
\rho(t)=\frac14\left(I_4+\frac12
\sum_{j=1}^4n_j(t)G_j\right).
\tag{267.13}
$$

由反对易关系，$(\sum_j n_jG_j)^2=I_4$，且该矩阵迹为零。因此每个实参数处的谱都为（267.2）。矩阵元由正弦、余弦的乘积组成，所以延拓成整函数，曲线以 $2\pi$ 为周期。由于 $n_j(t)$ 在实轴取实值，（267.8）说明同一个 $T$ 保持整条曲线不变。

在四个参数处，

$$
\begin{aligned}
n(0)&=e_1,&n(\pi/2)&=-e_2,\\
n(\pi/4)&=(e_3+e_4)/\sqrt2,&
n(3\pi/4)&=(e_3-e_4)/\sqrt2.
\end{aligned}
\tag{267.14}
$$

这些向量张成 $\mathbb R^4$。故任何保持整条曲线不变的反酉算子，也保持四个 $G_j$ 不变；这里恢复 $G_j$ 所用的线性组合系数均为实数。由（267.11），它的平方必为 $-I_4$。这完成曲线版本。证毕。

这条曲线的信息也处处非零。写 $N(t)=\sum_jn_j(t)G_j$，则 $|n'(t)|^2=5$，所以 $N'^2=5I_4$；由 $N^2=I_4$ 又有 $NN'+N'N=0$。代入 SLD 方程可见 $L=N'/2$，故

$$
\frac{\rho L+L\rho}{2}=\rho',
\qquad
I_Q(\rho_t)=\operatorname{Tr}(\rho L^2)=5/4.
\tag{267.15}
$$

因此，上述障碍并非来自某处参数导数退化或信息为零。

这个区别也可直接从平方符号的基底不变性看出。若反酉算子写成 $T=UK$，更换酉基底后其酉部分变为 $V U\overline{V}^{-1}$，而 $T^2$ 作为复线性算子按通常酉共轭变换。因而平方为 $-I$ 的对称不能仅靠换基变为平方为 $I$ 的复共轭。定理267.2还排除了另选一个不同共同反酉对称的办法，因为该族的交换子只有标量。

与第265节所引文献的对应需要精确限制。Miyazaki–Matsumoto，*Imaginarity-free quantum multiparameter estimation*，[arXiv:2010.15465v3](https://arxiv.org/pdf/2010.15465v3)，第3.1节定义1，把存在任意共同反酉对称的模型称为具有 global antiunitary symmetry。该版本定理1随后写道：

> If a model $\{\rho_x\mid x\in X\}$ is imaginarity-free, there is a conjugation which is a GAS for $\{\rho_x\mid x\in X\}$.

其后的说明还明确允许离散参数集和一般 Hermitian 算子族。定理267.2的四态族满足该定义，却没有共同共轭；其周期曲线版本说明这个区别也存在于光滑、满秩且精确固定谱的单参数模型。因此，该版本定理1在没有其他条件的一般维数表述下不成立。

原证明中可以具体定位一个不成立的细分步骤。该版本式（44）—（46）把两个由同一反酉算子保持的正交分解，按子空间交集继续细分。对本节的矩阵，令

$$
E=\ker(G_1-I_4),\qquad
F_+=\ker(G_2-I_4),\qquad
F_-=\ker(G_2+I_4).
\tag{267.16}
$$

这些二维子空间都由 $T$ 保持，且 $F_+\oplus F_-=\mathbb C^4$。但反对易关系给出 $E\cap F_+=E\cap F_-=\{0\}$：若非零 $v$ 同时满足 $G_1v=v$ 与 $G_2v=\pm v$，则 $G_1G_2v=-G_2G_1v$ 的两边矛盾。因此

$$
E\ne(E\cap F_+)\oplus(E\cap F_-).
\tag{267.17}
$$

原文另要求被细分子空间的维数“more than 2”。按此字面条件，本四维例在首次分成两个二维谱子空间后，程序已无法继续到一维。即使把该条件改为“more than 1”，式（267.17）仍表明交集细分不成立，因此修改维数门槛不能修复该证明。

同一个反酉算子保持两个正交分解，并不保证这两个分解能由交集共同细化；这里对应的谱投影不对易。这个失败步骤与前面的完整反例相互对应。

非简并条件则足以保留所需对应。若族中有一个状态谱非简并，任一共同反酉对称都会保持它的每条一维特征空间；在单位特征向量 $v$ 上写 $Tv=\lambda v$，其中 $|\lambda|=1$，便有 $T^2v=\overline\lambda\lambda v=v$。因此 $T^2=I$。这正是同篇文献引理1(b)的情形。第265节的两个特征值不同，其直接平面证明及信息上界均不受上述高维区别影响。

以上文献判定只针对所引用 arXiv v3 的定理文本。当前 arXiv 摘要页列出的最后修订也是 v3；本文未完成期刊勘误状态的核验，不据此宣称期刊现行状态或反例发现优先权。

本节没有据此否定文献中其他估计或可达性结论；那些陈述须分别核对是否需要平方为 $I$。这里保留的结果是一个完整的矩阵反例及其适用边界：共同反酉对称、共同共轭、固定基底中同时取实，在退化谱高维模型中不能不加条件地视为同一要求。实型与四元数型反酉结构的区分属于既有背景。Armin Uhlmann，*Anti- (Conjugate) Linearity*，[arXiv:1507.06545v2](https://arxiv.org/pdf/1507.06545v2)，式（114）—（115）区分共轭与平方为负单位的 skew conjugation，第4.2.2节命题4.8给出后者的二维配对标准形。本节使用这种既有结构提供明确反例，不把平方符号的区分作为新的表示论发现。

<a id="entry-884"></a>

## 追加锚（本行以下为增补区）

<a id="section-268"></a>

## 268. 四元数型状态族的实基底扩充与辅助混合度

第267节的反例排除了原四维空间中的共同实基底。本节固定一种具体的扩充操作：给每个状态附加同一个、与参数无关的辅助密度矩阵，然后在扩充空间中作一次固定酉变换。这个操作可以保留原模型的全部统计信息；能否使扩充后的整族同时取实，则取决于辅助谱的重数。

**定义 268.1（固定乘积辅助扩充）。** 设 $\mathcal R$ 是 $\mathbb C^d$ 上的非空密度矩阵族，$\tau$ 是有限维辅助空间上的固定密度矩阵。称 $\tau$ 允许该族的固定实基底扩充，如果存在一个固定酉矩阵 $W$，使

$$
W(\rho\otimes\tau)W^*
\quad\text{对每个 }\rho\in\mathcal R\text{ 均为实矩阵。}
\tag{268.1}
$$

辅助态可以不满秩。式（268.1）要求同一个 $\tau$ 和同一个 $W$ 适用于整个族。

**定理 268.2（辅助谱的偶重数判据）。** 假设 $\mathcal R$ 满足：其共同复线性交换子只有标量；存在共同反酉对称 $T$，且 $T^2=-I_d$。则 $\tau$ 允许（268.1），当且仅当 $\tau$ 的每个正特征值都具有偶数重数。零特征值的重数不受限制。等价地，在其支撑上，$\tau$ 可酉变换为 $(I_2/2)\otimes\sigma$，其中 $\sigma$ 是某个密度矩阵。

证明。 固定实基底存在，等价于扩充族存在共同共轭 $J$，其中 $J$ 反酉且 $J^2=I$。先计算扩充族的共同复线性交换子，以排除不同辅助谱块之间的混合。

原族的共同核为零：因为全部状态 Hermitian，共同核的正交投影与每个状态对易，因而只能是零或单位投影；状态的迹为一排除了后一种情形。

在 $\tau$ 的特征基中，一个交换矩阵的系统块 $B$ 若连接辅助特征值 $\lambda,\mu$，就必须满足

$$
\lambda\rho B=\mu B\rho
\qquad(\rho\in\mathcal R).
$$

若 $\lambda,\mu>0$，取伴随并分别乘以 $B$、$B^*$，得到

$$
\mu B^*B\rho
=\lambda B^*\rho B
=\mu\rho B^*B.
$$

所以 $B^*B$ 属于原族的共同交换子，必为 $cI_d$。若 $B\ne0$，则 $c>0$，从而 $B=\sqrt c\,V$，其中 $V$ 酉。块方程变为 $\lambda\rho=\mu V\rho V^*$，取迹得 $\lambda=\mu$。当这两个特征值相等时，块方程直接说明 $B$ 为标量。

若恰有一个特征值为零，块方程或其伴随把 $B$ 或 $B^*$ 的像限制在原族的共同核中，因此 $B=0$。两个零特征值之间的块则没有限制。故若正特征值 $\lambda_a$ 的重数为 $m_a$，零特征值重数为 $m_0$，扩充族的共同交换子恰为

$$
\left(\bigoplus_a I_d\otimes M_{m_a}(\mathbb C)\right)
\oplus M_{dm_0}(\mathbb C).
$$

取标准基复共轭 $K_d$，写 $T=UK_d$，于是 $U$ 酉且 $U\overline U=-I_d$。在整个辅助空间的特征基中，$(U\otimes I)K$ 保持扩充族并逐块保持辅助特征子空间。任何共同反酉对称 $J$ 与它的商为上述交换子中的酉矩阵，因此 $J$ 也必须保持各个正谱块和零谱块。于是可逐块判断：在一个重数为 $m$ 的正谱块中令

$$
T_m=(U\otimes I_m)K_{dm},
\qquad T_m^2=-I_{dm}.
\tag{268.2}
$$

这里 $K_{dm}$ 是乘积基中的逐项复共轭；$T_m$ 保持每个 $\rho\otimes I_m$。

这族的共同复线性交换子为

$$
\{\rho\otimes I_m:\rho\in\mathcal R\}'
=I_d\otimes M_m(\mathbb C).
\tag{268.3}
$$

这也可直接按辅助指标展开成 $d\times d$ 块，由原族的标量交换子得到。

若 $J_m$ 是任意共同反酉对称，则 $J_mT_m^{-1}$ 为共同复线性酉对称，由（268.3）有

$$
J_m=(I_d\otimes V)T_m
\quad\text{对某个酉 }V\in M_m(\mathbb C).
\tag{268.4}
$$

直接计算平方得

$$
J_m^2=-I_d\otimes V\overline V.
\tag{268.5}
$$

所以 $J_m$ 为共轭，当且仅当 $V\overline V=-I_m$。取行列式，

$$
1=|\det V|^2=(-1)^m,
\tag{268.6}
$$

故 $m$ 必为偶数。反过来，若 $m=2k$，取实正交矩阵

$$
V=\bigoplus_{j=1}^k
\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\tag{268.7}
$$

则 $V\overline V=V^2=-I_m$，式（268.4）给出所需共轭。

在每个正特征值块上分别这样构造；在零特征值块上取任意共轭，因为扩充状态在该块恒为零。块的正交直和仍为共轭，并保持扩充族。由其不动实子空间的正交基得到（268.1）。将每对相同正特征值 $\lambda$ 合并为 $\sigma$ 的特征值 $2\lambda$，便得到陈述中的张量形式；反方向由该张量形式立即给出偶重数。证毕。

**推论 268.3（最小辅助熵与纯辅助态障碍）。** 在定理268.2的假设下，任何允许的辅助态均满足

$$
S(\tau):=-\operatorname{Tr}(\tau\log\tau)\ge\log2.
\tag{268.8}
$$

等号成立当且仅当辅助谱的非零部分恰为 $\{1/2,1/2\}$。因此，一个最大混合的二维辅助态充分且达到最小熵；任意有限维纯辅助态都不充分。

证明。 将每个正特征值的偶数重数写成 $m_a=2k_a$，并把相同特征值两两配对。每一对的总质量为 $q_{a,j}=2\lambda_a$，其中 $1\le j\le k_a$，且 $\sum_{a,j}q_{a,j}=1$。于是

$$
S(\tau)=\log2-\sum_{a,j}q_{a,j}\log q_{a,j}
\ge\log2.
\tag{268.9}
$$

等号当且仅当只有一对有正质量，即该对的两个特征值均为 $1/2$。纯辅助态的唯一正特征值重数为一，不满足定理268.2。证毕。

偶数秩本身还不够。例如 $\operatorname{diag}(7/10,3/10)$ 的两个正特征值各为单重，因而不能完成（268.1）。判据要求每个谱块能成对组织。

对第267节的整函数周期曲线，$n(t+\pi)=-n(t)$，故

$$
\rho(t)+\rho(t+\pi)=I_4/2.
\tag{268.10}
$$

该恒等式使曲线的对称结构直观可见；定理268.2本身并不要求单位矩阵属于状态的实线性张成。曲线的标量交换子及负平方对称已由（267.6）—（267.14）证明。取 $\tau=I_2/2$ 即得到八维空间中的共同实基底，扩充后的谱精确为

$$
\{3/16,3/16,3/16,3/16,
1/16,1/16,1/16,1/16\}.
\tag{268.11}
$$

同一结论也适用于第267节最初的四个状态；这四态族的实线性张成并不包含 $I_4$，但它依然满足定理268.2的两个假设。

原四维空间中的障碍与八维扩充中的可行性分别属于两个不同的操作范围。最小扩充还可以写出明确换基矩阵。按辅助指标将空间排列为 $\mathbb C^d\oplus\mathbb C^d$，取

$$
W=\frac1{\sqrt2}
\begin{pmatrix}I&I\\-iI&iI\end{pmatrix}
\begin{pmatrix}I&0\\0&U^*\end{pmatrix}.
$$

由 $U^*\rho U=\overline\rho$，直接相乘得

$$
W\left(\rho\otimes\frac{I_2}{2}\right)W^*
=\frac12
\begin{pmatrix}
\operatorname{Re}\rho&-\operatorname{Im}\rho\\
\operatorname{Im}\rho&\operatorname{Re}\rho
\end{pmatrix}.
$$

右侧的实部和虚部均按矩阵元取；$\rho$ Hermitian 保证右侧为实对称矩阵。这一等式对给定反酉不变族成立，不宣称同一个信道在任意输入态上都实现右侧的标准实化公式。

标量交换子假设不可省略。例如单态族 $\{I_2/2\}$ 已经取实，同时也由平方为负单位的 $YK$ 保持；它不需要混合辅助态。仅存在某个负平方对称，不能推出本节的辅助熵下界。

**命题 268.4（统计恢复与 SLD 信息保持）。** 对任意固定辅助态 $\tau$ 和固定酉矩阵 $W$，编码

$$
\mathcal E(\rho)=W(\rho\otimes\tau)W^*
\tag{268.12}
$$

为量子信道，且有与参数无关的量子信道

$$
\mathcal D(\sigma)=\operatorname{Tr}_{\rm anc}(W^*\sigma W)
\tag{268.13}
$$

满足 $\mathcal D\mathcal E(\rho)=\rho$。对光滑满秩原模型，整个 SLD 量子 Fisher 信息矩阵在该编码下保持不变，即使 $\tau$ 不满秩。

证明。 附加固定密度矩阵、酉共轭及偏迹都是完全正保迹操作；$\operatorname{Tr}\tau=1$ 直接给出恢复恒等式。原 POVM $\{E_a\}$ 对应扩充 POVM $\{W(E_a\otimes I)W^*\}$，且

$$
\operatorname{Tr}\bigl[\mathcal E(\rho)W(E_a\otimes I)W^*\bigr]
=\operatorname{Tr}(\rho E_a).
\tag{268.14}
$$

反方向可由 $\mathcal E$ 的对偶信道将扩充测量拉回原模型，因此两个模型的测量分布可以互相实现。

若原模型的第 $i$ 个 SLD 是 $L_i$，则在固定支撑 $\mathbb C^d\otimes\operatorname{supp}\tau$ 上，$L_i\otimes I$ 满足乘积模型的 SLD 方程：

$$
\frac{(\rho\otimes\tau)(L_i\otimes I)
+(L_i\otimes I)(\rho\otimes\tau)}2
=(\partial_i\rho)\otimes\tau.
\tag{268.15}
$$

零支撑块可任意补为零，不影响信息。于是

$$
\operatorname{Re}\operatorname{Tr}
\bigl[(\rho\otimes\tau)(L_i\otimes I)(L_j\otimes I)\bigr]
=\operatorname{Re}\operatorname{Tr}(\rho L_iL_j).
\tag{268.16}
$$

固定酉共轭同时变换状态及 SLD，迹不变，因此编码后仍有相同信息矩阵。证毕。

特别地，第267节曲线的 $I_Q=5/4$ 在上述八维实基底扩充后仍精确保持。辅助熵下界描述的是固定乘积辅助态所需的混合度，不是物理能耗或热力学功下界，也不表示编码损失了原模型的信息。

本节的表示论机制已有标准来源。Uhlmann，*Anti- (Conjugate) Linearity*，[arXiv:1507.06545v2](https://arxiv.org/pdf/1507.06545v2)，第4.2.2节命题4.8给出平方为负单位的反酉算子的二维配对形式，第4.2.3节说明两个这种反酉结构的张量积成为共轭。定理268.2将这一既有机制与共同交换子、辅助态的各个谱块组合；辅助谱判据与熵结论由上面的逐块证明给出，不宣称反酉配对机制的原创性。

这也须与 Miyazaki–Matsumoto，[arXiv:2010.15465v3](https://arxiv.org/pdf/2010.15465v3)，附录A.3式（136）的纯态 embedding quantum simulator 编码区别开。该文明确说明那种将态矢量与其共轭同时编码的操作不是完全正映射，且其信息矩阵可以改变。式（268.12）附加固定混合态并作固定酉变换，具有（268.13）的信道恢复，不借用该纯态编码的可实现性或信息结论。

全部最小性结论仅针对定义268.1，并使用定理268.2列出的标量交换子与负平方共同反酉对称假设。本节未给出任意通道、相关辅助系统或近似模拟的最小维数与最小熵。扩充后的维数及谱已经改变，不能把它代入第265节固定二维、固定谱、固定矩阵上界的优化类。

<a id="entry-886"></a>

## 追加锚（本行以下为增补区）

<a id="section-269"></a>

## 269. 共轭不变的轨道、实代表与有限矩阵字检验

第267节的矩阵族由共同反酉算子保持，因而每个矩阵字的迹都是实数；但该族没有共同实基底。这个现象可以精确表述为：在固定维数中，一个酉轨道与其复共轭相同，并不保证轨道内部含有全实矩阵族。轨道的不变性与不动代表的存在，需要分开判断。

本节先给出有限长度的充分检验，再计算决定实代表是否存在的平方符号。有限长度界只用于说明如何结束精确检验，不宣称最优长度或低计算成本。

**定义 269.1（矩阵字与生成长度）。** 给定 Hermitian 矩阵 $A_1,\ldots,A_r\in M_d(\mathbb C)$，矩阵字是这些矩阵的有限有序乘积，空字为 $I_d$。假设这些字的复线性张成是全部 $M_d(\mathbb C)$。选取包含空字的矩阵字基底 $W_1,\ldots,W_{d^2}$，并令 $L$ 为其中最大的字长。

总可以选到 $L\le d^2-1$：令 $V_\ell$ 为长度至多 $\ell$ 的字张成的空间。若 $V_{\ell+1}=V_\ell$，则 $V_\ell$ 在每个生成元的左乘下封闭，此后不再增长；由于最终张成全部矩阵代数，在到达维数 $d^2$ 前，每一步维数必须严格增加。起点 $V_0$ 的维数为一。

**定理 269.2（有限实迹检验）。** 在定义269.1的假设下，以下三条等价：

1. 每个长度至多 $2L+1$ 的矩阵字都具有实迹。
2. 存在共同反酉对称 $T$，使 $TA_jT^{-1}=A_j$ 对全部 $j$ 成立。
3. 任意长度的矩阵字都具有实迹。

因此，长度至多 $2d^2-1$ 是一个统一的充分检验范围。

证明。 第二条推出第三条：共同反酉对称保持每个有序乘积 $B$，且反酉共轭使迹取复共轭，所以

$$
\operatorname{Tr}B
=\operatorname{Tr}(TBT^{-1})
=\overline{\operatorname{Tr}B}.
\tag{269.1}
$$

第三条显然推出第一条。以下证明第一条推出第二条。

取矩阵字基底的 Hilbert–Schmidt Gram 矩阵

$$
G_{ki}=\operatorname{Tr}(W_k^*W_i).
\tag{269.2}
$$

由于生成元各自 Hermitian，$W_k^*$ 也是反序矩阵字；右侧的总字长至多为 $2L$，故 $G$ 的每个元素都为实数。基底的线性无关性使 $G$ 正定可逆。

对任意生成元 $A_j$ 和基底字 $W_i$，写

$$
A_jW_i=\sum_\ell c_\ell W_\ell.
\tag{269.3}
$$

系数向量满足 $Gc=b$，其中

$$
b_k=\operatorname{Tr}(W_k^*A_jW_i).
\tag{269.4}
$$

右侧的字长至多 $2L+1$，所以 $b$ 为实向量；$G$ 实可逆，故全部 $c_\ell$ 为实数。

定义复线性映射 $\Psi:M_d(\mathbb C)\to M_d(\mathbb C)$，令

$$
\Psi(W_i)=\overline{W_i}.
\tag{269.5}
$$

这里 $\Psi$ 是按基底定义的复线性映射，不是对任意矩阵逐项取共轭。由于共轭后的基底仍线性无关，它为双射，并且 $\Psi(I_d)=I_d$。式（269.3）的系数为实数，因此

$$
\Psi(A_jX)=\overline{A_j}\Psi(X)
\qquad(X\in M_d(\mathbb C)).
\tag{269.6}
$$

按字长归纳，再对矩阵字作复线性组合，得到

$$
\Psi(XY)=\Psi(X)\Psi(Y).
\tag{269.7}
$$

对任意字 $W$，式（269.6）也给出 $\Psi(W)=\overline W$；反序取伴随及生成元的 Hermitian 性质于是给出

$$
\Psi(X^*)=\Psi(X)^*.
\tag{269.8}
$$

所以 $\Psi$ 是复线性的保单位、保伴随矩阵代数自同构，因而可由某个酉矩阵 $Q$ 实现：$\Psi(X)=QXQ^*$。这一标准矩阵代数事实也可直接从矩阵单位验证：$\Psi(E_{ii})$ 是相互正交的极小投影；选取其中一个单位向量 $f_1$，令 $f_i=\Psi(E_{i1})f_1$，便得到一组正交基，使 $\Psi(E_{ij})=|f_i\rangle\langle f_j|$。

于是 $QA_jQ^*=\overline{A_j}$。令 $K$ 为标准复共轭，则

$$
T=Q^*K
\tag{269.9}
$$

是保持全部 $A_j$ 的反酉算子，完成证明。证毕。

长度中的额外一步不能一般地直接删去。对二维空间的三个 Pauli 矩阵 $X,Y,Z$，$I,X,Y,Z$ 已构成字长至多一的矩阵基底，即 $L=1$。全部长度至多二的迹都为实数，但 $\operatorname{Tr}(XYZ)=2i$。所以 $2L$ 不能在一般情况下替代定理中的 $2L+1$；这不表示统一界 $2d^2-1$ 已经最优。

**定理 269.3（有限迹数据的实表示与辅助谱证书）。** 在定理269.2的等价条件成立时，记

$$
H_{ij}=\operatorname{Tr}(W_iW_j),
\qquad
G_{ij}=\operatorname{Tr}(W_i^*W_j).
\tag{269.10}
$$

则由有限迹数据计算的数

$$
\boxed{
\varepsilon=\frac1d\sum_{i,j=1}^{d^2}(G^{-1})_{ij}H_{ij}
}
\tag{269.11}
$$

必为正一或负一。它等于任意共同反酉对称的平方符号；矩阵族存在固定实基底，当且仅当它等于正一。右侧只使用字长至多 $2L$ 的精确迹值，但定理269.2中的反酉存在性仍是本结论的前提。

若这些生成元本身为密度矩阵，负证书还给出具体的辅助谱约束：固定乘积辅助态及一次固定酉变换能使整个族取实，当且仅当辅助态的每个正特征值都具有偶数重数；最小辅助熵为 $\log2$。正证书则允许纯辅助态，最小辅助熵为零。

证明。先在本证明内使用经典的 Schur 交织论证确定平方符号，再证明它可由式（269.11）读取。共轭与平方为负单位的反酉结构之区别、配对形式及张量符号规则见 Uhlmann，*Anti- (Conjugate) Linearity*，[arXiv:1507.06545v2](https://arxiv.org/pdf/1507.06545v2)，式（114）—（115）、命题4.8及第4.2.3节。

考虑复线性交织方程组

$$
\mathcal I_A
=\{U\in M_d(\mathbb C):A_jU=U\overline{A_j}\ \forall j\}.
\tag{269.12}
$$

全矩阵代数的共同交换子只有标量。若 $U$ 满足（269.12），对方程取伴随，并利用全部 $A_j$ 和 $\overline{A_j}$ 均 Hermitian，可得 $U^*U$ 与每个 $\overline{A_j}$ 对易。因此 $U^*U=cI_d$。对非零 $U$，$c>0$，于是 $U_0=U/\sqrt c$ 酉。

若 $V$ 是另一非零解，则 $VU^{-1}$ 与每个 $A_j$ 对易，故为标量。交织空间因而至多一维；非零时恰为一维。

令 $T=U_0K$。它是共同反酉对称，而 $T^2$ 是共同复线性酉对称，故 $T^2=\lambda I_d$，其中 $|\lambda|=1$。结合律给出 $TT^2=T^2T$，反线性使左侧的标量被共轭，所以 $\overline\lambda=\lambda$，即 $\lambda=\pm1$。将 $U_0$ 乘以单位相位不改变 $U_0\overline{U_0}$，因此符号唯一。

因此存在唯一的 $\varepsilon\in\{+1,-1\}$，满足

$$
U_0\overline{U_0}=\varepsilon I_d.
\tag{269.13}
$$

正号时 $T$ 本身为共轭，从其不动实子空间取得共同实基底。负号时，全部共同反酉对称的平方都为负单位，不存在共同共轭；固定实基底若存在则会提供共同共轭，矛盾。

接着计算这个符号。此时 $G$ 是实对称正定矩阵。令 $C=G^{-1/2}$，并取

$$
B_\alpha=\sum_i W_i C_{i\alpha}.
\tag{269.14}
$$

这些矩阵构成 Hilbert–Schmidt 正交归一基底。由于 $C$ 的元素为实数，每个 $B_\alpha$ 仍由共同反酉 $T=UK$ 保持。因此

$$
\begin{aligned}
\sum_\alpha\operatorname{Tr}(B_\alpha^2)
&=\sum_{i,j}(G^{-1})_{ij}\operatorname{Tr}(W_iW_j),\\
\sum_\alpha (B_\alpha)_{ij}\overline{(B_\alpha)_{kl}}
&=\delta_{ik}\delta_{jl}.
\end{aligned}
\tag{269.15}
$$

在第一行左端展开矩阵迹，再将其中一个因子替换为 $B_\alpha=U\overline{B_\alpha}U^*$，第二行的完备关系给出

$$
\sum_\alpha\operatorname{Tr}(B_\alpha^2)
=\sum_{i,j}U_{ij}\overline{U_{ji}}
=\operatorname{Tr}(U\overline U)
=\varepsilon d.
$$

与第一行相比较即得式（269.11）。若生成元是密度矩阵，全矩阵代数生成假设使其共同交换子为标量。负号时直接适用定理268.2及推论268.3；正号时原族已有共同实基底，附加一个纯辅助态即可，且熵非负给出最小值零。证毕。

这表明符号判别是对已有精确迹数据的进一步计算，不是额外索取这些数据之外的信息。若没有先验证反酉存在性，右侧未必等于正负一；例如前面的 $I,X,Y,Z$ 基底给出右侧为二。

这里必须保留两步检验的分工。有限实迹条件判断的是酉轨道是否在复共轭下保持不变；交织解的平方符号判断这个轨道是否含有全实代表。定理269.2并未把任意共同反酉对称都当成共轭。

第267节的四个 $G_j$ 生成全部 $M_4(\mathbb C)$：它们的共同交换子为标量，而所生成的代数在伴随下封闭，有限维双交换子定理给出该结论。其共同反酉对称使每个矩阵字的迹为实数，但定理269.3的证书为 $-1$。这给出“共轭不变轨道没有实代表”的明确实例。

还可直接计算本例的有限证书。取十六个有序子集字 $W_S=\prod_{j\in S}G_j$，其中 $S\subseteq\{1,2,3,4\}$，乘积按指标递增排列。这四个生成元为两两反对易的对合。每个非空子集字都无迹：当其长度为偶数，取子集内的一个生成元共轭；当其长度为奇数，取子集外的一个生成元共轭，均使该字变号。不同子集字的乘积约化为非空子集字，故

$$
G_{\rm Gram}=4I_{16},\qquad
H_{SS}=4(-1)^{|S|(|S|-1)/2},\qquad
H_{ST}=0\quad(S\ne T).
\tag{269.16}
$$

这同时证明十六个字线性无关，因而构成矩阵基底。长度为零、一、四的字共有六个，平方为正单位；长度为二、三的字共有十个，平方为负单位。于是式（269.11）给出 $\varepsilon=(6-10)/4=-1$，从具体迹值读出了第268节辅助谱配对所需的负证书。上述矩阵族与其密度族由 $G_j=8\rho_j-2I_4$ 互相生成，且具有相同共同反酉对称，故该证书同样判断对应密度族的平方类型。

全部矩阵字的精确迹值仍然能在固定维数中区分酉轨道。上述反例没有否定这一完整性：仅知道每个值都是实数，远弱于知道并比较全部具体值。若另一个同维度的全实矩阵族与该四元数型族具有全部相同的矩阵字迹，它们就会酉等价，反而与无实代表结论矛盾。

矩阵字迹的这种完整性属于既有结果。Futorny、Horn、Sergeichuk，*Specht's criterion for systems of linear mappings*，[arXiv:1701.08826v1](https://arxiv.org/pdf/1701.08826v1)，引言式（2）陈述 Wiegmann 的同时酉相似判据：比较全部含生成元及其伴随的矩阵字迹。本文的生成元各自 Hermitian，伴随不再增加字母。该文还将闭合有向路的迹用于一般线性映射系统；本节只使用单空间矩阵族的情形。有限基底证明给出本节所需的可结束范围，不宣称矩阵字不变量、经典判据或最优长度界的原创性。

第268节的可恢复扩充进一步说明适用范围的重要性。原四维族没有共同实基底，附加一个固定最大混合量子比特后却可同时取实，而编码有量子信道恢复并保持全部测量分布与 SLD 信息。因此，若把这种扩充及恢复列为允许的等价操作，“存在共同实基底”就不是统计实验等价类上的不变量；它仍可作为固定表示、固定维数和辅助资源范围内的约束。

一个相应的成对读数是

$$
\frac14\operatorname{Tr}w(G_1,\ldots,G_4)
=\frac18\operatorname{Tr}w(G_1\otimes I_2,\ldots,G_4\otimes I_2)
\tag{269.17}
$$

对全部矩阵字成立。左边的四维表示没有共同共轭，右边的八维表示有共同共轭。这里保持的是归一化迹读数；维数和共同交换子已经改变，不能将它说成同维度完整迹不变量失效。

式（269.17）比较的是生成元 $G_j$ 的归一化矩阵字迹，不是密度编码后所有乘积迹都不变。对固定乘积编码 $\rho_j\mapsto\rho_j\otimes I_2/2$，长度为 $k$ 的密度矩阵乘积满足

$$
\operatorname{Tr}\!\left[\prod_{\ell=1}^k
(\rho_{j_\ell}\otimes I_2/2)\right]
=2^{1-k}\operatorname{Tr}(\rho_{j_1}\cdots\rho_{j_k}).
\tag{269.18}
$$

统计实验的可恢复性由编码与恢复信道证明，并不要求这些密度矩阵字迹保持原数值。

本节所有检验均针对精确矩阵及精确等式。字数可以很大，未给出高效复杂度界；在有限精度数据下如何可靠判定零交织空间、平方符号与近似实化，也未由这些等式解决。实矩阵族仍可不对易，所以共同实基底的有无不能单独充当量子与经典的通用分界。

<a id="entry-888"></a>

## 追加锚（本行以下为增补区）

<a id="section-270"></a>

## 270. 可恢复实表示的维数—熵区域与三种对称类型

第268节固定了乘积辅助扩充的形式。本节允许任意有限维完全正保迹编码，只要求一个同样完全正保迹的解码能恢复指定状态族。对共同交换子为标量的族，这个恢复条件会迫使编码在整个输入矩阵空间上可恢复。因此，辅助谱的约束可以转化为任意这类编码的精确维数—熵区域。

**定义 270.1（模型可恢复实编码）。** 设 $\mathcal R$ 是 $\mathbb C^d$ 上的非空密度矩阵族，且

$$
\mathcal R'=\mathbb C I_d.
\tag{270.1}
$$

给定正整数 $D$，一个模型可恢复实编码由两个完全正保迹复线性映射

$$
\mathcal E:M_d(\mathbb C)\longrightarrow M_D(\mathbb C),
\qquad
\mathcal D:M_D(\mathbb C)\longrightarrow M_d(\mathbb C)
\tag{270.2}
$$

组成，满足 $\mathcal D\mathcal E(\rho)=\rho$ 对全部 $\rho\in\mathcal R$ 成立，并且整个 $\mathcal E(\mathcal R)$ 在同一个固定正交基底中均为实矩阵。输出可以有从未占用的维数。熵使用自然对数，约定 $0\log0=0$。

若 $\mathcal R$ 有共同反酉对称，任意两个这样的对称之商是共同复线性酉对称，由标量交换子假设必为单位相位。对一个共同反酉 $T$，其平方也属于该交换子，故 $T^2=\lambda I_d$，其中 $|\lambda|=1$。结合律 $T(T^2)=(T^2)T$ 与反线性给出 $\overline\lambda=\lambda$，所以 $\lambda=\pm1$。给 $T$ 乘上单位相位不改变它的平方，因此平方符号为整个族唯一确定。

以下将平方符号为正一和负一的族分别称为正型和负型；没有共同反酉对称时称为无反酉型。这是经典实型、四元数型与复型区分在本节状态族上的用法；共轭与负平方反酉结构的标准定义见 Uhlmann，*Anti- (Conjugate) Linearity*，[arXiv:1507.06545v2](https://arxiv.org/pdf/1507.06545v2)，式（114）—（115）。

**定理 270.2（完整可行区域）。** 在定义270.1的条件下，每个模型可恢复实编码都满足

$$
\mathcal D\mathcal E=\operatorname{id}_{M_d(\mathbb C)}.
\tag{270.3}
$$

此外，存在一个与输入无关的数 $h$，使对每个输入密度矩阵 $\rho$ 都有

$$
S(\mathcal E(\rho))-S(\rho)=h.
\tag{270.4}
$$

固定输出维数 $D$ 时，所有可达的 $h$ 精确如下：

$$
\begin{array}{c|c|c}
\text{类型}&\text{维数可行条件}&\text{全部可达熵增}\hline
\text{正型}&D\ge d&[0,\log\lfloor D/d\rfloor]\\
\text{负型}&D\ge2d&[\log2,\log(2\lfloor D/(2d)\rfloor)]\\
\text{无反酉型}&\text{无有限维可行值}&\varnothing
\end{array}
\tag{270.5}
$$

维数未满足相应条件时，可行集合为空。负型中 $h=\log2$ 当且仅当恢复正规形的辅助态非零谱为 $(1/2,1/2)$。

证明。先将只在模型上恢复的条件提升为式（270.3）。原族的共同核为零：其正交投影与每个 Hermitian 状态对易，由（270.1）只能为零或单位，迹归一化排除单位。因此全部状态的支撑共同张成输入空间；有限维性还保证某个有限凸组合是满秩态，但不要求任何单个状态满秩。

对信道 $\Phi=\mathcal D\mathcal E$ 使用 Koashi–Imoto 的不扰动分解。这是既有结构定理：在状态族的共同支撑上，存在分解

$$
\mathbb C^d=\bigoplus_a H_{J,a}\otimes H_{K,a},
\qquad
\rho=\bigoplus_a p_a(\rho)\rho_{J,a}\otimes\tau_{K,a},
\tag{270.6}
$$

其中 $\tau_{K,a}$ 与所选状态无关；保持全部状态的信道之 Stinespring 等距实现，在每块上对 $H_{J,a}$ 作恒等作用，只能作用于 $H_{K,a}$ 与环境。其精确来源是 Koashi、Imoto，*What is Possible Without Disturbing Partially Known Quantum States?*，[arXiv:quant-ph/0101144v2](https://arxiv.org/pdf/quant-ph/0101144v2)，式（85）—（89）及定理3式（103）。

各直和块投影都与 $\mathcal R$ 对易，所以（270.1）排除多个块。若唯一的 $H_K$ 维数大于一，取与 $\tau_K$ 对易的非平凡正交投影 $P$；这样的投影总可从 $\tau_K$ 的特征基中取得，即使它是标量矩阵也一样。于是 $I_J\otimes P$ 是 $\mathcal R$ 的非标量共同交换子，矛盾。故只有一个块，且 $\dim H_K=1$。不扰动结构遂要求 $\Phi$ 在整个输入空间上为恒等信道。这一步使用不扰动定理，不把一般完全正映射当成代数同态。

由第39.1节已使用的可恢复信道正规形，存在有限维密度矩阵 $\tau$ 和等距映射 $V$，使

$$
\mathcal E(X)=V(X\otimes\tau)V^*,
\qquad V^*V=I.
\tag{270.7}
$$

可将辅助空间限制在 $\operatorname{supp}\tau$，令其维数为 $r=\operatorname{rank}\tau$；于是 $dr\le D$。这个既有正规形可由 Nayak、Sen，*Invertible quantum operations and perfect encryption of quantum states*，[arXiv:quant-ph/0605041v4](https://arxiv.org/pdf/quant-ph/0605041v4)，定理2.1证明中的式（2）—（3）直接取得：恢复使 Kraus 算子满足 $A_i^*A_j=\alpha_{ij}I$，将正矩阵 $\alpha$ 对角化后得到正交像的等距算子及固定混合权重。式（270.7）只作用于占用子空间，不要求 $D$ 是 $d$ 的倍数。

等距变换保留非零谱，乘积态的熵相加，因此

$$
S(\mathcal E(\rho))=S(\rho)+S(\tau)
\tag{270.8}
$$

对所有输入成立，得到 $h=S(\tau)$。

令 $\mathcal S=V(\mathbb C^d\otimes\operatorname{supp}\tau)$。它是全部编码状态支撑的共同张成，故输出的共同共轭 $J$ 保持 $\mathcal S$。限制到该子空间并拉回，得到

$$
J_0=V^*(J|_{\mathcal S})V,
\qquad J_0^2=I,
\qquad
J_0(\rho\otimes\tau)J_0^{-1}=\rho\otimes\tau.
\tag{270.9}
$$

这里 $V$ 被视为从乘积支撑到 $\mathcal S$ 的酉同构。输出中未占用的维数不能与占用支撑混合以消除这一限制。

先处理无反酉型，以证明任意有限扩充都不可能。将 $\tau$ 在其支撑上对角化，特征值均严格为正，写 $J_0=ZK$，其中 $Z$ 酉。对辅助指标取系统矩阵块 $B$，式（270.9）给出

$$
\lambda\rho B=\mu B\overline\rho
\qquad(\rho\in\mathcal R),
\qquad\lambda,\mu>0.
\tag{270.10}
$$

取伴随、左右乘以 $B^*$ 和 $B$，得到

$$
\mu B^*B\overline\rho
=\lambda B^*\rho B
=\mu\overline\rho B^*B.
$$

共轭族的共同交换子也为标量，所以非零块必为 $B=\sqrt c\,U$，其中 $c>0$、$U$ 酉。对（270.10）归一化后取迹，得到 $\lambda=\mu$，继而 $U\overline\rho U^*=\rho$。因此 $UK$ 是原族的共同反酉对称。酉矩阵 $Z$ 至少有一个非零块，产生矛盾。无反酉型的可行集合为空。

负型中，将定理268.2用于（270.9），每个正辅助特征值均须具有偶数重数，亦即

$$
\tau\simeq(I_2/2)\otimes\sigma.
\tag{270.11}
$$

于是 $r=2k$，其中 $k=\operatorname{rank}\sigma$，并且

$$
2dk\le D,
\qquad
h=\log2+S(\sigma).
\tag{270.12}
$$

密度矩阵的熵不超过其秩的对数，故 $h$ 位于（270.5）的负型区间中，且 $D\ge2d$。等号 $h=\log2$ 的辅助谱刻画由推论268.3给出。

正型中，原族已存在共同实基底；辅助态在其特征基中也为实，所以任意 $\tau$ 都可实现共同实表示。另一方面，任何编码的正规形均有 $r\le\lfloor D/d\rfloor$，因此

$$
0\le h=S(\tau)\le\log\lfloor D/d\rfloor.
\tag{270.13}
$$

最后证明区间中的每一点都可达。对整数 $m\ge1$，连接纯态和最大混合态的连续路径

$$
\sigma_t=(1-t)|1\rangle\langle1|+tI_m/m,
\qquad0\le t\le1,
\tag{270.14}
$$

熵连续，端点分别为零与 $\log m$，所以取遍该区间。正型取 $m=\lfloor D/d\rfloor$ 并令 $\tau=\sigma_t$。负型取 $m=\lfloor D/(2d)\rfloor$ 并令 $\tau=(I_2/2)\otimes\sigma_t$；定理268.2给出一个固定酉变换，使整个乘积族取实。把所得实矩阵族等距嵌入输出的前若干坐标，其余补零，即可在恰为 $D$ 的空间中实现。

这些等距编码确有定义在全部输出上的恢复信道。若 $P=VV^*$，固定任意输入密度矩阵 $\omega$，可取

$$
\mathcal D(Y)
=\operatorname{Tr}_{\rm anc}(V^*YV)
+\operatorname{Tr}[(I-P)Y]\,\omega.
\tag{270.15}
$$

两项完全正，迹之和为 $\operatorname{Tr}Y$；在编码像上第二项为零，第一项恢复 $X$。式（270.5）的全部可行值因而达到。证毕。

**命题 270.3（三种区域均有有限状态族实现）。** 取 Pauli 矩阵 $X,Y,Z$，并令 $\rho_A=(I_2+A/2)/2$。二态族 $\{\rho_X,\rho_Z\}$ 为正型；三态族 $\{\rho_X,\rho_Y,\rho_Z\}$ 为无反酉型；第267节的四态族为负型。它们各自的共同复线性交换子均只有标量。

证明。与 $\rho_X,\rho_Z$ 对易等价于与 $X,Z$ 对易，因而交换子为标量；二态族本身取实。若三态族存在共同反酉对称，由 $A=4\rho_A-2I_2$，该对称也保持 $X,Y,Z$，从而保持其乘积。但

$$
\operatorname{Tr}(XYZ)=2i
\tag{270.16}
$$

在反酉共轭下取复共轭，与保持不变矛盾。负型四态族的标量交换子和平方为负单位的对称已在第267节给出。证毕。

因此，负型的最小熵增不是编码损失信息的度量：式（270.3）仍使每个输入都能完全恢复。它衡量的是在完全正可恢复操作下取得共同实表示所需的额外混合度。正型允许零熵增，负型必须至少增加 $\log2$，而无反酉型在任意有限维输出中均不可行。该结论依赖精确恢复、单一固定实基底和标量共同交换子；它不包括近似恢复、仅保持部分统计量、非完全正编码或热力学功成本。

<a id="entry-890"></a>

## 追加锚（本行以下为增补区）

<a id="section-271"></a>

## 271. 共轭状态块的概率平衡与可恢复实编码

第270节的标量共同交换子假设排除了可独立读取的经典块。本节允许两个这样的块，并考察一个具体拼接：第一块承载一个状态族，第二块承载其复共轭。两块各自都没有共同反酉对称，整体却可以在概率恰好平衡时具有共同实表示。精确恢复要求使这种平衡成为任何有限维编码都无法绕开的条件。

**定义 271.1（加权共轭双块）。** 设 $\mathcal R=\{\rho_s:s\in S\}$ 是 $\mathbb C^d$ 上的非空密度矩阵族，满足共同复线性交换子为 $\mathbb CI_d$，且没有共同反酉对称。固定一组基底以定义逐项复共轭。对固定 $p\in(0,1)$，定义

$$
\Omega_p(s)=p\rho_s\oplus(1-p)\overline{\rho_s}
\quad\text{作用于 }\mathbb C^d\oplus\mathbb C^d.
\tag{271.1}
$$

所谓可恢复实编码，是固定的完全正保迹复线性映射 $\mathcal E:M_{2d}\to M_D$ 和 $\mathcal D:M_D\to M_{2d}$，使 $\mathcal D\mathcal E(\Omega_p(s))=\Omega_p(s)$ 对每个 $s$ 成立，并使全部 $\mathcal E(\Omega_p(s))$ 在同一个固定正交基底中取实。

**定理 271.2（平衡判据与完整熵区间）。** 定义271.1中存在某个有限输出维数上的可恢复实编码，当且仅当 $p=1/2$。平衡时，固定输出维数 $D$ 的可行条件为 $D\ge2d$；全部可达熵增为

$$
0\le h\le\log\lfloor D/(2d)\rfloor.
\tag{271.2}
$$

这里每个编码的 $h=S(\mathcal E(\Omega_{1/2}(s)))-S(\Omega_{1/2}(s))$ 与 $s$ 无关。更强地，同一熵增适用于任意输入块对角密度矩阵。定理不要求恢复两个输入块之间的相干，也不将该熵恒等式扩展到一般含非零非对角块的输入。

所用的加权共轭直和族已有文献先例：van Luijk、Wilming，*Sufficiency and Petz recovery for positive maps*，[arXiv:2604.08380v2](https://arxiv.org/pdf/2604.08380v2)，例4.11及第32页续证，研究同一族在正保迹映射下的充分 Jordan 代数，并由定理5.1描述正映射互换。那些允许转置的正映射不保证完全正。本定理要求编码与恢复均完全正，所断言的是该要求下的平衡条件、辅助谱配对和精确维数—熵区间；不将共轭直和构造或正映射充分代数作为新增内容。

证明。首先，原族及其共轭族的共同支撑均为整个 $\mathbb C^d$，由标量交换子和迹归一化可得。故 $\Omega_p$ 的共同支撑为整个双块空间。

令 $\Phi=\mathcal D\mathcal E$。对 $\Omega_p$ 使用 Koashi–Imoto 不扰动结构，来源及操作形式见第270节所引 [arXiv:quant-ph/0101144v2](https://arxiv.org/pdf/quant-ph/0101144v2)，定义1式（90）—（92）及定理3式（103）。这里两个直和块、各自一维的冗余因子，已经满足其极大结构判据：每块内部的共同交换投影只有零与单位；两个块之间若存在酉矩阵 $V$ 及正常数 $c$，满足

$$
p\rho_s=c(1-p)V\overline{\rho_s}V^*
\quad\text{对全部 }s,
\tag{271.3}
$$

取迹后得 $p=c(1-p)$，继而 $VK$ 为原族的共同反酉对称，与假设矛盾。

不扰动结构因而要求 $\Phi$ 的初始化 Stinespring 等距映射形如

$$
|\psi\rangle_L\longmapsto|\psi\rangle_L\otimes|e_L\rangle,
\qquad
|\psi\rangle_R\longmapsto|\psi\rangle_R\otimes|e_R\rangle.
\tag{271.4}
$$

两个环境向量不必相同。因此 $\Phi$ 固定每个块对角算子，却可以改变两个块之间的相干；特别地，它在每个输入块上都是恒等信道。

分别限制 $\mathcal E$ 到两个输入块。为核对限制后的恢复仍由保迹信道实现，令 $\iota_a:\mathbb C^d\to\mathbb C^d\oplus\mathbb C^d$ 为块 $a$ 的包含映射，$\Pi_a=\iota_a\iota_a^*$，并固定一个 $d$ 维密度矩阵 $\omega_a$。对受限编码 $\mathcal E_a(X)=\mathcal E(\iota_aX\iota_a^*)$，取

$$
\mathcal D_a(Y)
=\iota_a^*\mathcal D(Y)\iota_a
+\operatorname{Tr}[(I-\Pi_a)\mathcal D(Y)]\,\omega_a.
$$

两项均完全正，迹之和为 $\operatorname{Tr}Y$；由于 $\Phi$ 固定全部块对角算子，$\mathcal D_a\mathcal E_a(X)=X$。单独压缩原解码一般不保迹，上式的制备项补足了它。现在可以分别使用既有可恢复信道正规形，得到

$$
\mathcal E_L(X)=V_L(X\otimes\tau_L)V_L^*,
\qquad
\mathcal E_R(X)=V_R(X\otimes\tau_R)V_R^*.
\tag{271.5}
$$

该正规形仍为第39.1、270节使用的 Nayak–Sen / Knill–Laflamme 结构。将两个辅助空间分别限制到其支撑，记秩为 $r_L,r_R$，则 $V_a$ 为等距映射，$\tau_a$ 在对应辅助空间上严格为正。

两个等距映射的像必须正交，而非预先假设编码保持块标签。取分别支撑在左、右输入块上的最大混合态 $\omega_L,\omega_R$。解码精确恢复它们，迹距离的信道收缩性给出

$$
2=\|\omega_L-\omega_R\|_1
\le\|\mathcal E(\omega_L)-\mathcal E(\omega_R)\|_1
\le2.
\tag{271.6}
$$

两个密度矩阵的迹范数距离等于二，当且仅当支撑正交；而式（271.5）使这两个输出的支撑恰为 $\mathcal S_L=\operatorname{im}V_L$ 与 $\mathcal S_R=\operatorname{im}V_R$。因此它们正交，并且 $d(r_L+r_R)\le D$。对模型状态，编码在这些占用子空间上等距等同于

$$
p\rho_s\otimes\tau_L
\ \oplus
(1-p)\overline{\rho_s}\otimes\tau_R.
\tag{271.7}
$$

共同实输出给出共同共轭。该共轭保持全部输出支撑的共同张成 $\mathcal S_L\oplus\mathcal S_R$，故可以限制并拉回到式（271.7）的乘积直和空间；记所得共轭为 $J=ZK$。

先证明 $J$ 不可能在同一个经典块内有非零分量。在辅助特征基中，$Z$ 的左到左系统块 $B$ 必须满足

$$
\lambda\rho_s B=\mu B\overline{\rho_s},
\qquad\lambda,\mu>0.
\tag{271.8}
$$

取伴随并比较乘积，使 $B^*B$ 与全部 $\overline{\rho_s}$ 对易。非零 $B$ 因而为正标量乘酉矩阵；归一化后取迹得 $\lambda=\mu$，继而产生原族的共同反酉对称，矛盾。右到右块同理为零，因为共轭族也没有共同反酉对称。于是 $J$ 只能交换整个左右占用子空间。

记左右投影为 $P_L,P_R$。对式（271.7）的状态 $\widehat\Omega_p(s)$，有

$$
JP_LJ^{-1}=P_R,
\qquad
J\widehat\Omega_p(s)J^{-1}=\widehat\Omega_p(s).
$$

反酉共轭使迹取复共轭，而以下概率为实数，故

$$
p=\operatorname{Tr}(P_L\widehat\Omega_p(s))
=\operatorname{Tr}(P_R\widehat\Omega_p(s))=1-p.
\tag{271.9}
$$

因此 $p=1/2$ 必要。任意辅助混合度和额外零维数都不能改变这一质量平衡。

在平衡情形进一步比较跨块分量。若辅助特征值为 $\lambda$ 和 $\mu$，行指标位于左块、列指标位于右块的交织方程变成

$$
\lambda\rho_s B=\mu B\rho_s.
\tag{271.10}
$$

同样的伴随与标量交换子论证使非零 $B$ 为比例酉矩阵，取迹得 $\lambda=\mu$，随后 $B$ 本身为标量。由于 $Z$ 是交换两个占用空间的酉矩阵，每个正特征值的左右辅助重数必须相同。故

$$
\operatorname{spec}\tau_L=\operatorname{spec}\tau_R,
\qquad r_L=r_R=r,
\qquad2dr\le D.
\tag{271.11}
$$

反之，若两辅助谱相同，选取各自特征基后可令 $\tau_L=\tau_R=\tau$。交换两块并逐项复共轭便是保持式（271.7）的共同共轭。因此这也是对每个可恢复编码占用正规形的充分谱条件。

对任意块对角输入 $q\sigma_L\oplus(1-q)\sigma_R$，输入熵为 $H(q)+qS(\sigma_L)+(1-q)S(\sigma_R)$。正交输出块的熵公式和辅助谱相同给出

$$
S\!\left(\mathcal E(q\sigma_L\oplus(1-q)\sigma_R)\right)
-S(q\sigma_L\oplus(1-q)\sigma_R)
=S(\tau).
\tag{271.12}
$$

端点 $q=0,1$ 按零质量项为零解释。于是 $h=S(\tau)$，且 $0\le h\le\log r\le\log\lfloor D/(2d)\rfloor$。

最后给出全部可行值的构造。平衡模型本身已经有共轭 $J(v,w)=(\overline w,\overline v)$。令

$$
Q=\frac1{\sqrt2}
\begin{pmatrix}I&I\\-iI&iI\end{pmatrix}.
$$

直接相乘得

$$
Q\Omega_{1/2}(s)Q^*
=\frac12
\begin{pmatrix}
\operatorname{Re}\rho_s&-\operatorname{Im}\rho_s\\
\operatorname{Im}\rho_s&\operatorname{Re}\rho_s
\end{pmatrix}.
\tag{271.13}
$$

这是对给定双块输入的一次酉变换。附加任意对角辅助态 $\tau$，再将整体嵌入 $D$ 维输出并补零，仍得到实矩阵族。若 $m=\lfloor D/(2d)\rfloor$，在 $m$ 维辅助空间中从纯态连续插值到最大混合态，辅助熵取遍 $[0,\log m]$。上述构造的编码可以恢复全部双块输入，包括块间相干：撤销等距映射、偏迹，并在未占用输出补一个固定制备项，正如式（270.15）。因此区间中每点均可达；$D=2d$、纯辅助态给出最小维数和零熵增。证毕。

**命题 271.3（四维平衡实例及恢复范围的边界）。** 对定义271.1中的任意平衡模型，存在可恢复实编码，其块对角熵增为零，却没有全空间左逆，并且某个含块间相干的纯输入的熵增为 $\log2$。此外，取 $\rho_A=(I_2+A/2)/2$，其中 $A=X,Y,Z$。则式（271.1）的三态族在 $p=1/2$ 时有四维实表示；任意 $p\in(0,1)\setminus\{1/2\}$ 都没有任何有限维可恢复实编码。同时，对每个 $s$ 有

$$
\frac12\|\Omega_p(s)-\Omega_{1/2}(s)\|_1
=|p-1/2|.
\tag{271.14}
$$

证明。先证明恢复范围的限定。定理中的块对角限定确实不可省略。记输入块退相干为 $\Delta(X)=\Pi_LX\Pi_L+\Pi_RX\Pi_R$，在平衡点取

$$
\mathcal E(X)=Q\Delta(X)Q^*,
\qquad
\mathcal D(Y)=\Delta(Q^*YQ).
$$

这两者都是信道，且 $\mathcal D\mathcal E=\Delta$；所以模型和所有块对角输入均被精确恢复，模型输出仍取实，块对角熵增为零。但对单位向量 $v,w$ 所构成的纯态 $|\psi\rangle=(|v\rangle_L+|w\rangle_R)/\sqrt2$，编码先删去块间相干，输出为两个正交纯态的等权混合，熵增为 $\log2$。该编码没有全空间左逆。这说明定理的必要结论与达到端点时可选用的全空间可逆构造具有不同适用范围。

再考察所示三态。三态原族具有标量交换子，且不存在共同反酉对称，已由命题270.3的 Pauli 乘积论证给出。于是定理271.2适用。两模型之差为 $(p-1/2)\rho_s\oplus-(p-1/2)\overline{\rho_s}$；两块的迹范数各为 $|p-1/2|$，得到所示等式。证毕。

式（271.14）说明，这里的可行性结论使用精确相等与精确恢复；它没有给出近似恢复的误差下界。式（271.13）的物理操作以已经给定的共轭双块状态为输入，也没有声称可以用完全正信道从任意未知 $\rho$ 制备 $(\rho\oplus\overline\rho)/2$。本节所判断的是两个实际准备块的联合组织及其概率权重。

<a id="entry-892"></a>

## 追加锚（本行以下为增补区）

<a id="section-272"></a>

## 272. 共轭信道判据与六态实编码的精确恢复误差

前两节使用状态族的分块结构判断实表示。本节直接以允许的信道表述同一问题：是否可以在给定状态族上实现复共轭。这个判据不要求标量共同交换子，并把任意输出维数上的实编码问题归约为输入维数内的一个信道问题。其近似版本给出与输出维数无关的恢复误差下界。

**定义 272.1（有限模型的共轭缺口）。** 固定输入基底，设 $\mathcal R=\{\rho_1,\ldots,\rho_n\}$ 是 $M_d(\mathbb C)$ 中的非空有限密度矩阵族，定义

$$
\delta(\mathcal R)
=\min_{\mathcal C\ \mathrm{CPTP}}
\max_{1\le j\le n}
\frac12\|\mathcal C(\rho_j)-\overline{\rho_j}\|_1,
\qquad\mathcal C:M_d\to M_d.
\tag{272.1}
$$

对任意有限维编码 $\mathcal E:M_d\to M_D$、解码 $\mathcal D:M_D\to M_d$ 及固定输出基底，定义

$$
e(\mathcal D,\mathcal E)
=\max_j\frac12\|\mathcal D\mathcal E(\rho_j)-\rho_j\|_1,
\qquad
r(\mathcal E)
=\max_j\frac12\|\mathcal E(\rho_j)-\overline{\mathcal E(\rho_j)}\|_1.
\tag{272.2}
$$

全部映射均要求复线性、完全正且保迹；两处复共轭分别取所固定的输入和输出基底。$r=0$ 恰表示整个输出模型在该基底中取实。

**定理 272.2（信道归约与误差传递）。** 定义272.1中的最小值达到。存在某个有限输出维数上的精确可恢复实编码，当且仅当 $\delta(\mathcal R)=0$。可行时，输出维数 $2d$ 已经充分。

对任意有限 $D$ 和任意编码、解码，都有

$$
\boxed{e(\mathcal D,\mathcal E)+r(\mathcal E)
\ge\delta(\mathcal R).}
\tag{272.3}
$$

因此，若精确可恢复实编码不可行，任何维数上的完全实输出都具有严格正的统一恢复误差下界 $\delta(\mathcal R)$。

证明。对一个信道 $\mathcal A$ 定义其共轭信道

$$
\overline{\mathcal A}(X)
=\overline{\mathcal A(\overline X)}.
\tag{272.4}
$$

右端外层横线作用于输出矩阵，内层横线作用于输入矩阵。若 $A_k$ 是 $\mathcal A$ 的 Kraus 算子，则 $\overline{A_k}$ 是式（272.4）的 Kraus 算子；所以它仍为复线性 CPTP 映射。这里没有把单独的复共轭当成物理信道。

给定任意 $\mathcal E,\mathcal D$，取输入维数内的信道 $\mathcal C=\overline{\mathcal D}\mathcal E$。对每个模型状态，

$$
\begin{aligned}
\frac12\|\mathcal C(\rho_j)-\overline{\rho_j}\|_1
&\le\frac12\|\overline{\mathcal D}(\mathcal E(\rho_j))
-\overline{\mathcal D}(\overline{\mathcal E(\rho_j)})\|_1\\
&\quad+\frac12\|\overline{\mathcal D\mathcal E(\rho_j)}
-\overline{\rho_j}\|_1\\
&\le\frac12\|\mathcal E(\rho_j)-\overline{\mathcal E(\rho_j)}\|_1
+\frac12\|\mathcal D\mathcal E(\rho_j)-\rho_j\|_1.
\end{aligned}
\tag{272.5}
$$

第二步使用信道对密度矩阵迹距离的收缩性及复共轭保持迹范数。对 $j$ 取最大值，再在输入维数内的信道上取最小值，即得（272.3）。特别地，精确恢复且完全实输出给出 $\mathcal C(\rho_j)=\overline{\rho_j}$。

反过来，若一个 CPTP 映射 $\mathcal C$ 在整个模型上实现复共轭，则

$$
\overline{\mathcal C}(\overline{\rho_j})=\rho_j.
\tag{272.6}
$$

定义到 $2d$ 维空间的信道

$$
\mathcal F(X)=\frac12\bigl(X\oplus\mathcal C(X)\bigr),
\qquad
\mathcal E(X)=Q\mathcal F(X)Q^*,
\qquad
Q=\frac1{\sqrt2}\begin{pmatrix}I&I\\-iI&iI\end{pmatrix}.
\tag{272.7}
$$

两个对角块均由完全正映射取得，迹之和经二分之一归一化后为 $\operatorname{Tr}X$，而 $Q$ 酉。因此这是对全部输入定义的 CPTP 编码。在模型上，式（271.13）的直接乘法给出

$$
\mathcal E(\rho_j)
=\frac12
\begin{pmatrix}
\operatorname{Re}\rho_j&-\operatorname{Im}\rho_j\\
\operatorname{Im}\rho_j&\operatorname{Re}\rho_j
\end{pmatrix},
\tag{272.8}
$$

故所有输出均为实矩阵。令 $Y'=Q^*YQ$，按两个 $d$ 维块记其压缩为 $Y'_{LL},Y'_{RR}$，取

$$
\mathcal D(Y)=Y'_{LL}+\overline{\mathcal C}(Y'_{RR}).
\tag{272.9}
$$

这是两个完全正压缩及信道的和，且输出迹为两个对角块的迹之和，等于 $\operatorname{Tr}Y$。由（272.6），

$$
\mathcal D\mathcal E(\rho_j)
=\tfrac12\bigl(\rho_j+\overline{\mathcal C}\mathcal C(\rho_j)\bigr)
=\rho_j.
\tag{272.10}
$$

上述共轭直和构造具有正映射层面的文献先例。van Luijk、Wilming，*Sufficiency and Petz recovery for positive maps*，[arXiv:2604.08380v2](https://arxiv.org/pdf/2604.08380v2)，例4.11及第32页续证，以正映射研究加权共轭直和；定理5.1描述正保迹互换。其第32页显示的是 Heisenberg 图景的保单位元的正映射（unital positive maps）。取迹对偶后，相应状态图景映射为

$$
\mathcal F_p^+(X)=pX\oplus(1-p)X^{\mathsf T},
\qquad
\mathcal G^+(Y)=Y_{LL}+Y_{RR}^{\mathsf T}.
$$

这两个映射正且保迹，并有 $\mathcal G^+\mathcal F_p^+=\mathrm{id}$。当 $d\ge2$、$0<p<1$ 时，两者均不完全正：否则压缩转置分支或限制输入到该分支会使转置本身完全正。故在 $p=1/2$ 时，上述先例结合 $Q$ 已给出普遍的正映射可恢复实表示。本证明要求全部操作完全正，式（272.7）以模型上可实现的 $\mathcal C$ 替换转置分支，式（272.9）以其共轭信道恢复；这正是这里需要判定的额外条件。既有正映射互换并未消去该完全正约束。

最后，固定有限维输入与输出的 CPTP 信道集可由 Choi 矩阵 $J\succeq0$、$\operatorname{Tr}_{\rm out}J=I_d$ 表示。它闭且有界，因为 $\operatorname{Tr}J=d$，故为紧集。式（272.1）的有限个连续函数之最大值连续，最小值达到。因此 $\delta=0$ 等价于某个信道精确实现模型共轭，结合上述构造得到所述等价。不可行时最小值严格为正，而（272.3）对全部有限 $D$ 都成立。证毕。

这个归约还给出有限维半正定规划。使用输出指标在前的未归一化 Choi 矩阵，记

$$
X_j(J)=\operatorname{Tr}_{\rm in}
\left[J(I_d\otimes\rho_j^{\mathsf T})\right]
-\overline{\rho_j}.
$$

最小化实数 $t$，约束为

$$
J\succeq0,\quad\operatorname{Tr}_{\rm out}J=I_d,
\qquad
Y_j\succeq X_j(J),\quad Y_j\succeq-X_j(J),
\quad\operatorname{Tr}Y_j\le2t\quad(1\le j\le n).
\tag{272.11}
$$

其中 $Y_j$ Hermitian。这是迹范数的标准半正定表示：对 Hermitian $X$，满足 $Y\succeq\pm X$ 的最小迹为 $\|X\|_1$，可取 $Y=|X|$；反向下界由 $X$ 的正、负谱投影分别压缩两条不等式得到。因此该规划的值正是 $\delta(\mathcal R)$。它消除了对任意输出维数的搜索，不宣称有限精度下的零值判定算法。

**定理 272.3（六个 Pauli 状态的最优实编码误差）。** 对 $0<a\le1$，令

$$
\mathcal R_a=
\left\{\frac{I_2\pm aX}{2},
\frac{I_2\pm aY}{2},
\frac{I_2\pm aZ}{2}\right\}.
\tag{272.12}
$$

则

$$
\delta(\mathcal R_a)=\frac a3.
\tag{272.13}
$$

在所有有限输出维数、所有在同一基底中产生完全实模型的 CPTP 编码及所有 CPTP 解码上，最小最坏恢复误差亦为 $a/3$，并由一个四维经典输出编码达到。对允许非实残差的编码，仍有 $e+r\ge a/3$。

证明。以 Bloch 向量表示量子比特，逐项复共轭对应反射矩阵

$$
S=\operatorname{diag}(1,-1,1).
$$

将任意候选 $\mathcal C$ 在保持六个坐标轴方向的二十四个立方体旋转 $g$ 上平均。输入旋转 $g$ 由酉矩阵实现；输出旋转 $Sg^{-1}S$ 也是正旋转，故同样由酉矩阵实现。取相应的前后酉共轭后再平均，仍为 CPTP 信道。每项都仅排列六个输入并相应旋转共轭目标，最大迹距离不增加。

若原 Bloch 仿射映射为 $u\mapsto Mu+b$，平均后的映射为

$$
u\longmapsto
S\left(\frac1{24}\sum_g g^{-1}(SM)g\right)u
+\frac1{24}\sum_g Sg^{-1}Sb
=tSu,
\qquad t=\frac13\operatorname{Tr}(SM).
\tag{272.14}
$$

这些有限平均恒等式可直接由群中的坐标轴半周旋转和坐标置换验证：前者消去向量平均及矩阵非对角项，后者使三个对角项相等。因而只须考虑

$$
\mathcal C_t(A)=tA^{\mathsf T}+(1-t)\operatorname{Tr}(A)I_2/2.
\tag{272.15}
$$

其未归一化 Choi 矩阵为 $tF+(1-t)I_4/2$，其中 $F$ 是两量子比特交换算子。在三维对称空间和一维反对称空间上，特征值分别为 $(1+t)/2$ 和 $(1-3t)/2$。因此完全正的精确范围为

$$
-1\le t\le1/3.
\tag{272.16}
$$

两个量子比特状态的迹距离为其 Bloch 向量欧氏距离的一半，所以式（272.12）每个状态的共轭误差均为 $a|1-t|/2$。它在合法区间上的最小值为 $a/3$，由 $t=1/3$ 达到。有限平均没有增加误差，故这同时给出所有 CPTP 候选中的下界及达到，证明（272.13）。

这里使用的近似转置通道是既有结果。Buscemi、D’Ariano、Perinotti、Sacchi，*Optimal realization of the transposition maps*，[arXiv:quant-ph/0304175v1](https://arxiv.org/pdf/quant-ph/0304175v1)，第2节式（15）给出一般维数的 $\mathcal C(\rho)=(I+\rho^{\mathsf T})/(d+1)$，其原文优化指标为纯态转置保真度。本证明的有限旋转平均与 Choi 特征值计算将该标准通道接到这里的六态、迹距离目标，不把不同优化指标的结论直接互换。

现在对完全实编码应用（272.3），得到 $e\ge a/3$。为达到这个下界，取正四面体的四个单位向量

$$
n_1=(1,1,1)/\sqrt3,\quad
n_2=(1,-1,-1)/\sqrt3,\quad
n_3=(-1,1,-1)/\sqrt3,\quad
n_4=(-1,-1,1)/\sqrt3.
$$

它们满足 $\sum_k n_k=0$、$\sum_k n_kn_k^{\mathsf T}=4I_3/3$。令 $\boldsymbol\sigma=(X,Y,Z)$，定义 POVM 效应和制备态

$$
F_k=\frac{I_2+n_k\cdot\boldsymbol\sigma}{4},
\qquad
P_k=\frac{I_2+n_k\cdot\boldsymbol\sigma}{2}.
\tag{272.17}
$$

由 $|n_k|=1$ 得 $F_k\succeq0$、$P_k$ 为纯态；向量和为零使 $\sum_kF_k=I_2$。取

$$
\mathcal E(\rho)=\sum_{k=1}^4\operatorname{Tr}(F_k\rho)|k\rangle\langle k|,
\qquad
\mathcal D(Y)=\sum_{k=1}^4\langle k|Y|k\rangle P_k.
\tag{272.18}
$$

它们分别是测量和按记录制备的 CPTP 映射，编码的每个输出均为实对角矩阵。对任意 Bloch 向量 $u$，输出记录概率为 $(1+n_k\cdot u)/4$，所以解码后的 Bloch 向量为

$$
\sum_k\frac{1+n_k\cdot u}{4}n_k=\frac u3.
\tag{272.19}
$$

故六个模型状态的恢复误差均为 $\tfrac12|au-au/3|=a/3$，其中 $u$ 为对应单位轴向量。这达到对所有实输出量子编码的下界，完成证明。证毕。

式（272.17）是标准量子比特四面体 SIC POVM 的归一化。近似转置的量子设计与测量—制备实现见 Kalev、Bae，*Optimal approximate transpose map via quantum designs and its applications to entanglement detection*，[arXiv:1303.3096v2](https://arxiv.org/pdf/1303.3096v2)，式（1）—（2）及 SIC 实现式（6）。这里的解码制备 $P_k$ 本身，得到式（272.19）的收缩；若按该文制备共轭态，则得到近似转置。四面体设计与近似转置通道均为所用的既有构造，本节的最优实编码误差由（272.3）与上述达到共同确定。

四维输出只给出达到该误差的一种实现；本节没有证明达到时的最小输出维数。这里的误差衡量不含参考系统的六个指定状态；没有将其改称 diamond 距离或任意纠缠输入的误差。下界允许任意有限维量子输出，最优实现恰可选为经典记录；这项结论不将所有实矩阵族判为经典模型。

<a id="entry-894"></a>

## 追加锚（本行以下为增补区）

<a id="section-273"></a>

## 273. 共轭双块失衡的精确恢复误差

**定义 273.1（六轴共轭双块模型）。** 令 $0<a\le1$、$0\le p\le1$、$q=1-p$，并令 $u$ 取六个单位坐标轴向量 $\{\pm e_x,\pm e_y,\pm e_z\}$。记

$$
\rho_a(u)=\frac{I_2+a\,u\cdot\boldsymbol\sigma}{2},
\qquad
\Omega_{p,a}(u)=p\rho_a(u)\oplus q\overline{\rho_a(u)},
\qquad
\mathcal R_{p,a}=\{\Omega_{p,a}(u):u=\pm e_x,\pm e_y,\pm e_z\}.
\tag{273.1}
$$

复共轭相对于固定的 Pauli 基底；双块按所示坐标排序。令 $\delta(\mathcal R_{p,a})$ 为定义272.1中的共轭缺口，令 $e_{\mathbb R}(\mathcal R_{p,a})$ 为所有有限输出维数、所有在某个共同基底中产生实模型的 CPTP 编码与所有 CPTP 解码上的最小最坏迹距离恢复误差。下面的达到构造同时保证这个最小值存在。

**定理 273.2（不平衡质量的精确代价）。** 定义273.1中的两个量满足

$$
\boxed{\delta(\mathcal R_{p,a})
=e_{\mathbb R}(\mathcal R_{p,a})
=\frac a3|2p-1|.}
\tag{273.2}
$$

八维输出足以达到恢复误差的最小值；不要求输出维数达到最小。对允许非实残差的任意有限维编码与解码，定义272.1中的误差满足 $e+r\ge a|2p-1|/3$。在整个参数域 $0\le p\le1$ 内，精确可恢复实编码因而恰在 $p=1/2$ 时可行。

证明。交换左右输入块，并将六轴指标作反射 $u\mapsto Su$，其中 $S=\operatorname{diag}(1,-1,1)$，把参数 $p$ 的模型变成参数 $q$ 的模型。块交换为实酉矩阵，指标反射只重排六个状态，因此两个待优化量均不变。以下只需处理 $p\ge q$；此时 $p\ge1/2$。

先给出共轭缺口的下界。取任意候选信道 $\mathcal C:M_4\to M_4$。在其输入、输出两端作块退相干，仍为信道；输入模型和共轭目标原本块对角，而输出退相干收缩迹距离，所以最坏误差不增加。此后可以把信道表示为四个从 $M_2$ 到 $M_2$ 的完全正子映射 $\mathcal C_{ba}$，行指标 $b$ 为输出块，列指标 $a$ 为输入块。每一输入列的子映射之和保迹。

令 $G$ 为保持六轴集合的二十四元正旋转群。对 $g\in G$ 选量子比特酉矩阵 $U_g$，使其 Bloch 作用为 $g$，并在双块输入使用

$$
V_g=U_g\oplus\overline{U_g}.
$$

则 $V_g\Omega_{p,a}(u)V_g^*=\Omega_{p,a}(gu)$。将信道替换为

$$
\widetilde{\mathcal C}(A)
=\frac1{24}\sum_{g\in G}
\overline{V_g}^{\,*}\,
\mathcal C(V_gAV_g^*)\,
\overline{V_g}.
\tag{273.3}
$$

每个求和项仍为 CPTP，最坏共轭误差由六轴重排、酉不变性与凸性不增加。该平均也保持块对角结构。

只需分析平均后的左输出两子映射。这里子映射一般不保迹，故需同时平均迹的变化。一个保持 Hermitian 性的量子比特线性映射可写为

$$
\Lambda\!\left(\frac{tI_2+v\cdot\boldsymbol\sigma}{2}\right)
=\frac{(xt+\ell\cdot v)I_2+(tb+Mv)\cdot\boldsymbol\sigma}{2},
$$

其中 $x$ 为实数，$\ell,b$ 为实向量，$M$ 为实矩阵。有限旋转群的向量平均为零，故平均同时消去平移 $b$ 和依赖输入方向的迹项 $\ell\cdot v$。矩阵共轭平均为迹的三分之一乘单位；可由坐标轴半周旋转消去非对角项，再由坐标置换平均对角项验证。代入式（273.3）的左右旋转，左到左分量留下反射 $S$ 的标量倍，右到左分量留下单位矩阵的标量倍。因此存在实数 $x,y,\alpha,\beta$，使

$$
\widetilde{\mathcal C}_{LL}(A)
=\alpha A^{\mathsf T}+(x-\alpha)\operatorname{Tr}(A)I_2/2,
\qquad
\widetilde{\mathcal C}_{LR}(A)
=\beta A+(y-\beta)\operatorname{Tr}(A)I_2/2.
\tag{273.4}
$$

这里两者的输出迹分别为 $x\operatorname{Tr}A$ 和 $y\operatorname{Tr}A$。完全正性与输入列的保迹性给出 $0\le x,y\le1$。左到左子映射的未归一化 Choi 矩阵为 $\alpha F+(x-\alpha)I_4/2$，反对称空间上的非负特征值要求 $\alpha\le x/3$；右到左子映射的 Choi 矩阵为 $\beta|I\rangle\rangle\langle\langle I|+(y-\beta)I_4/2$，与 $|I\rangle\rangle$ 正交的空间给出 $\beta\le y$。这是第272节所用标准转置与恒等协变通道的缩放形式，未把它们另作新分类。

在输入 $\Omega_{p,a}(u)$ 上，左输出为

$$
\frac12\bigl(wI_2+a b(Su)\cdot\boldsymbol\sigma\bigr),
\qquad
w=px+qy,\quad b=p\alpha+q\beta.
$$

共轭目标的左块为 $p\overline{\rho_a(u)}$。由式（273.4）的完全正约束，

$$
b\le px/3+qy=w/3+2qy/3\le w/3+2q/3.
\tag{273.5}
$$

置 $z=w-p$，则 $p-b\ge2(p-q)/3-z/3$。对任意实数 $s,t$ 和单位向量 $v$，Hermitian 矩阵 $(sI_2+t\,v\cdot\boldsymbol\sigma)/2$ 的迹范数为 $\max\{|s|,|t|\}$。故左差块的迹范数至少为 $a[2(p-q)/3-z/3]$。右差块的迹为 $-z$，其迹范数至少为 $|z|$。两个差块直和，从而对每个六轴状态都有

$$
\begin{aligned}
\frac12\|\widetilde{\mathcal C}(\Omega_{p,a}(u))
-\overline{\Omega_{p,a}(u)}\|_1
&\ge\frac12\left[\frac{2a(p-q)}3-\frac{az}3+|z|\right]\\
&\ge\frac{a(p-q)}3.
\end{aligned}
\tag{273.6}
$$

第一行右侧的左块估计即使为负也仍是合法下界；第二行用 $|z|-az/3\ge0$，因为 $0<a\le1$。平均及退相干均未增加最坏误差，故这也是原候选的下界。对所有 $\mathcal C$ 取最小，得到 $\delta(\mathcal R_{p,a})\ge a(p-q)/3$。

为达到共轭误差下界，取第272节的标准最优近似转置通道 $\mathcal T(A)=(A^{\mathsf T}+\operatorname{Tr}(A)I_2)/3$。对任意双块矩阵 $A=[A_{ab}]$，定义

$$
\mathcal C_*(A)
=\left(A_{RR}+\frac{p-q}{p}\mathcal T(A_{LL})\right)
\ \oplus\ \frac qp A_{LL}.
\tag{273.7}
$$

压缩、信道和非负加权和均完全正，各输入块的输出迹系数之和为一，故这是全输入空间上的 CPTP 映射。对模型，它输出

$$
\bigl(q\overline{\rho_a(u)}+(p-q)\mathcal T(\rho_a(u))\bigr)
\oplus q\rho_a(u).
$$

第二块与共轭目标一致，第一块之差为 $(p-q)(\mathcal T(\rho_a(u))-\overline{\rho_a(u)})$。由第272节的六态转置误差，距离恰为 $(p-q)a/3$，证明共轭缺口的等式。

现在构造完全实输出的编码。令 $\mathcal M:M_2\to M_4$ 和 $\mathcal P:M_4\to M_2$ 分别为式（272.18）的四面体测量和制备信道，因而 $\mathcal P\mathcal M$ 将 Bloch 向量缩为原来的三分之一。令 $Q$ 为式（271.13）的四维酉矩阵。取八维输出为两个四维空间的直和，并定义

$$
\mathcal E_*(A)
=Q\left(\frac qp A_{LL}\oplus A_{RR}\right)Q^*
\ \oplus\ \frac{p-q}{p}\mathcal M(A_{LL}).
\tag{273.8}
$$

两项均完全正；其迹之和为 $\operatorname{Tr}A$，故 $\mathcal E_*$ 是信道。模型输入的第一输出块为

$$
Q\bigl(q\rho_a(u)\oplus q\overline{\rho_a(u)}\bigr)Q^*,
$$

由式（271.13）是实矩阵，第二块则为 $(p-q)\mathcal M(\rho_a(u))$，是实对角矩阵。因此所有模型输出共享一个实基底。

对任意八维输出矩阵 $Y$，记其两个四维对角块为 $Y_1,Y_2$，并令 $B=Q^*Y_1Q$。定义

$$
\mathcal D_*(Y)
=\bigl(B_{LL}+\mathcal P(Y_2)\bigr)\oplus B_{RR}.
\tag{273.9}
$$

两个输出块由完全正压缩及制备取得，输出迹为 $\operatorname{Tr}Y_1+\operatorname{Tr}Y_2=\operatorname{Tr}Y$；故这是全输出空间上的 CPTP 解码。其模型恢复为

$$
\bigl(q\rho_a(u)+(p-q)\mathcal P\mathcal M(\rho_a(u))\bigr)
\oplus q\overline{\rho_a(u)}.
\tag{273.10}
$$

仅左块有误差，其迹距离为 $(p-q)a/3$。所以 $e_{\mathbb R}\le(p-q)a/3$；定理272.2给出反向界 $e_{\mathbb R}\ge\delta$。二者结合得到式（273.2）和达到。相同的通用不等式还给出 $e+r$ 下界。$p=q$ 时残余输出分支为零映射；$q=0$ 时成对输出块只在模型输入上为零，对一般输入仍保留 $A_{RR}$ 的贡献。这一分支保证全输入空间上的保迹性，各公式仍定义合法信道。交换块覆盖 $p<q$ 的情况，证毕。

加权共轭直和是第271节所引 van Luijk–Wilming 例4.11的既有模型形式，近似转置与四面体测量亦使用第272节注明的标准构造。本定理的定量陈述将它们接到同一有限六态模型上：配对质量 $2\min(p,q)$ 可以精确恢复，剩余质量 $|p-q|$ 的最优完全实恢复误差恰为它乘以 $a/3$。误差指标只针对所列六态，不包含参考系统，也不宣称任意模型的共轭缺口都等于最优实编码误差。

<a id="entry-896"></a>

## 追加锚（本行以下为增补区）

<a id="section-274"></a>

## 274. 最小充分分块的实编码维数与熵函数

**定义 274.1（加权充分块与共轭配对）。** 设 $\{\rho_s:s\in S\}$ 是有限维复 Hilbert 空间上的非空密度矩阵族。将输入空间限制到所有状态支撑的共同张成，并采用 Koashi–Imoto 的极大分解

$$
\mathcal H=\bigoplus_{j\in J}\mathcal H_j\otimes\mathcal K_j,
\qquad
\rho_s=\bigoplus_{j\in J}p_j(s)\rho_j(s)\otimes\omega_j.
\tag{274.1}
$$

这里 $J$ 有限，$d_j=\dim\mathcal H_j$，$\omega_j$ 是与 $s$ 无关的辅助密度矩阵，并已限制到其正支撑。令

$$
A_j(s)=p_j(s)\rho_j(s).
$$

当 $p_j(s)=0$ 时直接令 $A_j(s)=0$，不赋予任意所选 $\rho_j(s)$ 额外条件。极大性具体要求：每个加权族 $\{A_j(s):s\in S\}$ 的共同复线性交换子是标量；不同块之间不存在酉矩阵 $U$ 和正常数 $c$，使 $A_j(s)=cUA_k(s)U^*$ 对全部 $s$ 成立。这是 Koashi–Imoto 定义1式（90）—（92）的有限维表述。

固定每个 $\mathcal H_j$ 的基底。若 $d_j=d_k$ 且存在酉矩阵 $U$，满足

$$
A_j(s)=U\overline{A_k(s)}U^*
\quad\text{对全部 }s,
\tag{274.2}
$$

称 $j,k$ 可以共轭配对，允许 $j=k$。自配对块按共同反酉的平方为 $+I$ 或 $-I$ 分成 $J_+$、$J_-$。非自配对的无序对记为 $\mathcal P$。下述定理同时保证这些配对没有歧义。熵采用自然对数。

**定理 274.2（完整资源区域与最小熵函数）。** 定义274.1中，每个块至多有一个共轭配对对象；配对关系在有定义处为对合。存在某个有限输出维数上的精确可恢复实 CPTP 编码，当且仅当每个块都有配对对象。

全部块均可配对时，最小输出维数为

$$
D_{\min}
=\sum_{j\in J_+}d_j
+\sum_{j\in J_-}2d_j
+\sum_{\{j,k\}\in\mathcal P}2d_j.
\tag{274.3}
$$

对任意固定 $D\ge D_{\min}$，全部可达的模型熵变化函数恰为

$$
h(s)=S(\mathcal E(\rho_s))-S(\rho_s)
=\sum_jp_j(s)\bigl(H_j-S(\omega_j)\bigr),
\tag{274.4}
$$

其中实数 $H_j$ 按如下有限整数容量约束取值：

* 对 $j\in J_+$，选择整数 $r_j\ge1$，并取 $0\le H_j\le\log r_j$。
* 对 $j\in J_-$，选择整数 $m_j\ge1$，令 $r_j=2m_j$，并取 $\log2\le H_j\le\log(2m_j)$。
* 对 $\{j,k\}\in\mathcal P$，选择整数 $r_j=r_k\ge1$，并取 $H_j=H_k\in[0,\log r_j]$。

这些容量共同满足

$$
\sum_jd_jr_j\le D.
\tag{274.5}
$$

容量允许大于实际辅助秩，因而上述区间包括秩下降的端点。若 $D<D_{\min}$，可行集为空。所有最小输出维数编码在模型上具有同一熵变化函数

$$
h_{\min}(s)
=\log2\sum_{j\in J_-}p_j(s)
-\sum_jp_j(s)S(\omega_j).
\tag{274.6}
$$

它也逐点不大于任何有限维可恢复实编码的熵变化，且由同一个编码同时达到。

证明。Koashi–Imoto 的极大分解、不扰动映射形式及唯一性使用 [arXiv:quant-ph/0101144v2](https://arxiv.org/pdf/quant-ph/0101144v2)，定义1、引理6—7及定理3。加权共轭分量、实型及四元数型矩阵块也属于已有表示结构；参见 Yamagata，*Quantum Sufficiency for Self-Adjoint Statistical Models via Likelihood-Type Operators on Real $*$-Subalgebras and Real Jordan Algebras*，[arXiv:2604.23292v4](https://arxiv.org/pdf/2604.23292v4)，定理27。该文第2节及例9区分实线性完全正与复线性完全正。这里始终要求复线性 CPTP 编码和解码；以下推导所需的是该要求下的配对质量、辅助谱和输出容量约束，不以实线性充分映射代替物理信道。

先消去固定冗余。令 $\kappa$ 压缩到各输入块后对 $\mathcal K_j$ 偏迹，令 $\beta$ 在各核心块附加 $\omega_j$；二者都是 CPTP 映射，且

$$
\sigma_s:=\kappa(\rho_s)=\bigoplus_jA_j(s),
\qquad
\beta(\sigma_s)=\rho_s.
\tag{274.7}
$$

核心族 $\sigma_s$ 的同一组块仍满足极大性条件，冗余因子现在全部一维。若 $\mathcal D\mathcal E$ 恢复原模型，则核心信道

$$
\Phi=\kappa\mathcal D\mathcal E\beta
$$

固定每个 $\sigma_s$。不扰动定理因而使 $\Phi$ 固定整个核心块对角代数，不要求固定不同块之间的相干。

把 $\mathcal E\beta$ 限制到核心块 $j$。如第271节，在 $\kappa\mathcal D$ 的对应压缩之后，用正交补的迹乘固定制备态补足，得到该受限编码的全输出 CPTP 左逆。Nayak–Sen 的可恢复信道正规形于是给出

$$
\mathcal E\beta(X_j)=V_j(X_j\otimes\tau_j)V_j^*.
\tag{274.8}
$$

这里 $V_j$ 是等距映射，$\tau_j$ 已限制到其正支撑。不同核心块上的最大混合态可被共同解码精确恢复，故其输出迹范数距离等于二，证明所有 $\operatorname{im}V_j$ 两两正交。于是

$$
\sum_jd_j\operatorname{rank}\tau_j\le D,
\qquad
\mathcal E(\rho_s)\simeq\bigoplus_jA_j(s)\otimes\tau_j
\tag{274.9}
$$

在共同占用输出空间上成立。各加权不可约族具有全共同支撑；故所有模型输出的支撑共同张成的正是式（274.9）的占用空间。

若模型输出有共同实基底，其共轭保持这个占用空间。拉回后记为 $C=ZK$，其中 $K$ 在系统基底和辅助特征基中逐项共轭。设 $Z$ 的行属于块 $j$ 的辅助特征值 $\lambda>0$，列属于块 $k$ 的辅助特征值 $\mu>0$，对应系统矩阵为 $B:\mathcal H_k\to\mathcal H_j$。固定全部模型的条件给出

$$
\lambda A_j(s)B=\mu B\overline{A_k(s)}.
\tag{274.10}
$$

取伴随并比较乘积，得到 $B^*B$ 与全部 $\overline{A_k(s)}$ 对易，$BB^*$ 与全部 $A_j(s)$ 对易。因此非零 $B$ 使两者分别为严格正的标量单位阵。这强制 $d_j=d_k$，并使 $B$ 是正标量乘一个酉矩阵。于是每个非零分量都要求两个加权族在复共轭后至多相差一个正常数和酉变换。

对于给定 $j$，这样的 $k$ 至多一个。若有两个不同对象，把两个共轭等价组合，便得到两个不同核心块之间的正常数倍酉等价，违反极大性。同理，共轭对应的平方只能回到原块。由于 $Z$ 酉，每个占用块必有非零对应，且所有分量只能落在该唯一对应块上。故 $C$ 将整个 $j$ 占用空间交换到整个 $k$ 占用空间。

对模型取这两个占用投影的迹，反酉保持实概率，得到

$$
p_j(s)=p_k(s)\quad\text{对全部 }s.
\tag{274.11}
$$

在式（274.10）中写 $B=cU$，其中 $c>0$、$U$ 酉；约去 $c$ 并右乘 $U^*$，得到 $\lambda A_j(s)=\mu U\overline{A_k(s)}U^*$。对此式取迹，有 $\lambda p_j(s)=\mu p_k(s)$。再使用式（274.11）及某个非零 $p_j(s)$，给出 $\lambda=\mu$。因此正常数比例必须消失，两个加权族满足精确关系（274.2）。这证明未配对块不可能通过改变辅助混合度或增加输出维数来补救，也证明定义中的配对唯一性与对合性。

对于自配对块，共同反酉的平方由标量交换子强制为 $+I$ 或 $-I$，且符号不依赖所选共同反酉。其标准分类及乘积共轭条件采用第267—268节的结果：正型允许任意辅助谱；负型要求每个正辅助特征值的重数为偶数，等价于

$$
\tau_j\simeq(I_2/2)\otimes\eta_j
\quad(j\in J_-).
\tag{274.12}
$$

这些结论同样适用于加权族 $A_j(s)$：任意非零权重可约去，零权重方程不施加条件，而不可约性和全共同支撑保持不变。

对于非自配对 $\{j,k\}$，选用式（274.2）的酉识别后，跨块方程化为同一加权族的交织方程。标量交换子及取迹使不同辅助特征值间的分量为零，相同特征值上的系统分量为标量。酉性于是强制两个辅助态的正谱按重数完全相同。反过来，配对权重相同且辅助谱相同时，交换两块并共轭就给出共同共轭；正型块直接使用其共轭，负型块使用系统和辅助斜共轭的乘积。把这些共轭直和，再在空余输出空间任取一个共轭，得到固定整个输出模型的共轭。因此这些谱条件也充分。

每个正型块至少占用 $d_j$ 维，每个负型块至少占用 $2d_j$ 维，每个非自配对对至少占用 $2d_j$ 维。它们两两正交，得到（274.3）的下界。分别取正型纯辅助态、负型最大混合量子比特辅助态、非自配对对的两个相同纯辅助态，便同时达到全部下界。

对熵，式（274.1）、（274.9）的正交块公式直接给出

$$
\begin{aligned}
S(\rho_s)&=H(p(s))+\sum_jp_j(s)[S(\rho_j(s))+S(\omega_j)],\\
S(\mathcal E(\rho_s))&=H(p(s))+\sum_jp_j(s)[S(\rho_j(s))+S(\tau_j)].
\end{aligned}
\tag{274.13}
$$

零权重项按零解释。相减后取 $H_j=S(\tau_j)$，得到（274.4）。正型辅助熵在 $[0,\log r_j]$；式（274.12）使负型辅助熵在 $[\log2,\log(2m_j)]$；非自配对对的辅助谱相同，因而熵相同。结合正交占用维数，得到所列全部必要条件。

为证明每组许可参数均可达到，正型辅助态在纯态与对应容量的最大混合态之间连续插值；负型取 $I_2/2\otimes\eta_j$ 并对 $\eta_j$ 作同样插值；每个非自配对对选两个相同的插值谱。各配对轨道独立选择辅助态，实际秩不超过容量，所以总占用维数不超过 $D$。

编码先执行 $\kappa$，随后对每个核心块附加所选辅助态，嵌入两两正交输出空间，再在共同共轭的实基中表达。完整解码先撤销这个固定基变换，压缩到各占用空间并对辅助系统偏迹；把未占用正交补的迹制备成一个固定核心态，最后执行 $\beta$。所有步骤完全正，压缩迹与补空间迹之和使整体保迹。对全部核心块对角输入的 $\beta$ 像，这个解码与编码的复合为恒等；特别地恢复原模型。由此得到所有熵函数的同时达到，而非分别在不同模型状态上取不可共同实现的最优值。

最后，各 $H_j$ 的逐块下界分别为 $0$、$\log2$ 和配对的 $0$。它们由达到最小输出维数的同一选择实现；所有权重非负，故（274.6）既是任何可行编码的逐点下界，也是同时达到的最小熵函数。最小维数下没有增加任何辅助秩的余量，因此所有最小维数编码都取这些辅助熵，证明其唯一的模型熵变化函数。证毕。

**命题 274.3（最小维数下的非恒定熵变化）。** 令 $\{\xi_i\}$ 为第267节四维、标量共同交换子、负反酉型的 Clifford 密度矩阵族。令 $\zeta_u=(I_2+u\cdot\boldsymbol\sigma/2)/2$，其中 $u$ 取六个单位坐标轴向量。让 $(i,u,t)$ 取 Clifford 指标、六轴指标与整个区间 $(0,1)$ 的笛卡尔积，取八维模型

$$
R_{i,u,t}
=t\xi_i
\ \oplus\ \frac{1-t}{2}\zeta_u
\ \oplus\ \frac{1-t}{2}\overline{\zeta_u}.
\tag{274.14}
$$

其最小可恢复实输出维数为十二。所有达到此维数的可行编码均满足

$$
S(\mathcal E(R_{i,u,t}))-S(R_{i,u,t})=t\log2.
\tag{274.15}
$$

证明。四维 Clifford 块不可约且负型；六轴量子比特族不可约且没有共同反酉。两个量子比特块构成唯一的非自配对对，其相等权重为 $(1-t)/2$。四维块与二维块不能酉等价，两个二维加权块若酉等价则产生六轴族的共同反酉，矛盾。因此所示三个块满足极大性条件，固定冗余全部一维。定理274.2给出 $D_{\min}=2\cdot4+2\cdot2=12$；式（274.6）中唯一负型块权重为 $t$，且所有 $S(\omega_j)=0$，得到（274.15）。证毕。

式（274.4）讨论模型本身的状态熵；固定冗余可以被丢弃后重新制备，所以熵变化允许为负。它不是不可恢复的信息损失或热功耗。熵公式可同样应用于 $\beta$ 所制备的任意核心块对角输入，但不约束任意改变原冗余因子或添加核心块间相干的输入。式（274.14）亦说明，常数熵增是特定结构的性质，不能由精确模型恢复独自推出。

**命题 274.4（固定维数下不可同时达到的最大熵函数）。** 令 $\xi_i$ 为命题274.3中的负型四维族，令 $v\in\{\pm e_x,\pm e_z\}$，并记 $\chi_v=(I_2+v\cdot\boldsymbol\sigma/2)/2$。取六维状态族

$$
T_{v,i,t}=(1-t)\chi_v\oplus t\xi_i,
\qquad (v,i,t)\in\{\pm e_x,\pm e_z\}\times\{1,2,3,4\}\times(0,1).
\tag{274.16}
$$

对这个完整模型，最小可恢复实输出维数为十。固定输出维数为十八时，全部可达熵变化函数恰为下列两族之并，且均不依赖 $v,i$：

$$
\begin{aligned}
\mathcal F_A&=\{h(t)=(1-t)H+t\log2:0\le H\le\log5\},\\
\mathcal F_B&=\{h(t)=tH:\log2\le H\le\log4\}.
\end{aligned}
\tag{274.17}
$$

按对每个 $0<t<1$ 的逐点大小比较，恰有两个极大可达函数：

$$
h_A(t)=(1-t)\log5+t\log2,
\qquad h_B(t)=t\log4.
\tag{274.18}
$$

二者互不支配；逐点上包络 $\max\{h_A,h_B\}$ 在 $t_*=\log5/\log10$ 处换支，不是任何一个固定十八维编码的熵变化函数。

证明。$\chi_v$ 全部为实，且共同交换子因包含 $X,Z$ 方向而为标量，所以构成一个正型二维块。$\xi_i$ 构成负型四维块，两个不同维数的块不能酉等价。所示分解满足极大性，且固定冗余一维。定理274.2给出 $D_{\min}=2+2\cdot4=10$。

设正型辅助容量为 $r$，负型容量为 $2m$。十八维预算为

$$
2r+8m\le18,\qquad r,m\in\mathbb N_{\ge1}.
\tag{274.19}
$$

因此只能有 $m=1,r\le5$，或 $m=2,r=1$。前一种取正型辅助熵 $H\in[0,\log5]$、负型辅助熵固定为 $\log2$；后一种正型辅助熵为零、负型辅助熵取 $H\in[\log2,\log4]$。定理274.2同时给出必要性与整个模型上的达到，得到（274.17）。

每个族内的最大参数都逐点支配同族所有其他参数，故极大函数只可能是式（274.18）两者。其差为

$$
h_A(t)-h_B(t)=\log5-t\log10,
\tag{274.20}
$$

在 $(0,1)$ 内恰改变一次符号，故两者互不支配，也都不能被另一个可达函数支配。所有可达函数关于 $t$ 为仿射函数，上包络在内部具有两个不同斜率，故不属于可达函数集。若只将两个块各自可达到的最大辅助熵 $\log5$、$\log4$ 同时填入一个编码，则分别至少需要辅助秩五和四，占用维数至少为 $2\cdot5+4\cdot4=26>18$。这亦直接显示逐块分别取得的最大值不满足共同预算。证毕。

<a id="entry-898"></a>

## 追加锚（本行以下为增补区）

<a id="section-275"></a>

## 275. 六态实编码的恢复误差、共轭缺口与预算边界

**定义 275.1（层析完备模型与实输出恢复误差）。** 对非空有限量子比特模型 $\mathcal R=\{\rho_j\}\subset M_2$，沿用定义272.1的共轭缺口 $\delta(\mathcal R)$。令

$$
e_{\mathbb R}(\mathcal R)
=\inf_{D,\mathcal E,\mathcal D}
\max_j\frac12\|\mathcal D\mathcal E(\rho_j)-\rho_j\|_1,
\tag{275.1}
$$

其中 $D$ 遍历正整数，$\mathcal E:M_2\to M_D$、$\mathcal D:M_D\to M_2$ 是复线性 CPTP 映射，且所有 $\mathcal E(\rho_j)$ 在某个共同输出基底中为实矩阵。若模型的实线性张成为整个 Hermitian 矩阵空间，称它层析完备。令 $\mathrm{EB}_2$ 为量子比特上的纠缠破坏 CPTP 映射集合；等价地，其元素可以写成有限 POVM 测量后再制备状态的形式。

**定理 275.3（各向异性六态的严格缺口与不连续点）。** 对 $0\le\varepsilon\le1$，定义

$$
\mathcal R_\varepsilon
=\left\{\frac{I_2\pm X}{2},\frac{I_2\pm Z}{2},\frac{I_2\pm\varepsilon Y}{2}\right\}.
\tag{275.6}
$$

则

$$
\delta(\mathcal R_\varepsilon)=\frac{\varepsilon}{1+2\varepsilon},
\tag{275.7}
$$

且

$$
e_{\mathbb R}(\mathcal R_\varepsilon)
=\begin{cases}
0,&\varepsilon=0,\\
\frac14,&0<\varepsilon\le\frac12,\\
\frac{\varepsilon}{1+2\varepsilon},&\frac12\le\varepsilon\le1.
\end{cases}
\tag{275.8}
$$

正参数时，至多四个经典输出符号足以达到式（275.8）；$0<\varepsilon\le1/2$ 时三个符号足够。特别地，$0<\varepsilon<1/2$ 时 $\delta(\mathcal R_\varepsilon)<e_{\mathbb R}(\mathcal R_\varepsilon)$，而

$$
\lim_{\varepsilon\downarrow0}\delta(\mathcal R_\varepsilon)=0,
\qquad
\lim_{\varepsilon\downarrow0}e_{\mathbb R}(\mathcal R_\varepsilon)=\frac14
>e_{\mathbb R}(\mathcal R_0).
\tag{275.9}
$$

证明。先以标准 Choi、PPT 与纠缠破坏判据给出所需的归约。对每个定义275.1中的层析完备模型，有

$$
e_{\mathbb R}(\mathcal R)
=\min_{\mathcal N\in\mathrm{EB}_2}
\max_j\frac12\|\mathcal N(\rho_j)-\rho_j\|_1.
\tag{275.2}
$$

式（275.1）的下确界达到，且可使用至多十六个经典输出符号达到。

取任意允许编码及使模型输出为实的基底，并将其固定为输出坐标。层析完备性与实线性给出：对每个 Hermitian 输入 $H$，$\mathcal E(H)$ 为实 Hermitian 矩阵，因而为对称矩阵。再将任意复矩阵写成两个 Hermitian 矩阵的复线性组合，得到

$$
T_{\rm out}\mathcal E=\mathcal E
\tag{275.3}
$$

在整个输入代数上的恒等式。这里 $T$ 为复线性的矩阵转置，并非逐项复共轭映射。

采用输入因子在前的未归一化 Choi 矩阵

$$
J_{\mathcal E}
=\sum_{a,b=0}^1|a\rangle\langle b|\otimes\mathcal E(|a\rangle\langle b|).
$$

完全正性与式（275.3）给出 $J_{\mathcal E}\succeq0$ 及 $J_{\mathcal E}^{T_{\rm out}}=J_{\mathcal E}$。因此

$$
J_{\mathcal E}^{T_{\rm in}}
=(J_{\mathcal E}^{T_{\rm out}})^{\mathsf T}
=J_{\mathcal E}^{\mathsf T}\succeq0.
\tag{275.4}
$$

这正是 $\mathcal E T_{\rm in}$ 的完全正性。于是恢复复合 $\mathcal N=\mathcal D\mathcal E$ 同时满足 $\mathcal N$ 与 $\mathcal NT_{\rm in}$ 完全正，其归一化 Choi 态作用于 $\mathbb C^2\otimes\mathbb C^2$，矩阵大小为 $4\times4$，满足 PPT 条件，因而可分。

这里使用的成熟结果是 Horodecki、Horodecki、Horodecki，*Separability of mixed states: necessary and sufficient conditions*，[arXiv:quant-ph/9605038v2](https://arxiv.org/pdf/quant-ph/9605038v2)，定理3及其后的第一因子转置注记；以及 Horodecki、Shor、Ruskai，*Entanglement Breaking Channels*，[arXiv:quant-ph/0302031v2](https://arxiv.org/pdf/quant-ph/0302031v2)，定理4的可分 Choi 与测量—制备刻画。由后者，$\mathcal N\in\mathrm{EB}_2$。这一步只断言恢复复合是纠缠破坏通道，未把任意输出维数的编码本身判为纠缠破坏。

反之，任意量子比特纠缠破坏通道都可写为

$$
\mathcal N(X)=\sum_{k=1}^m\operatorname{Tr}(F_kX)\tau_k,
\qquad F_k\succeq0,\quad\sum_kF_k=I_2.
\tag{275.5}
$$

取编码 $\mathcal E(X)=\operatorname{diag}(\operatorname{Tr}F_1X,\ldots,\operatorname{Tr}F_mX)$，解码 $\mathcal D(Y)=\sum_kY_{kk}\tau_k$，两者均在全矩阵代数上 CPTP，编码对全部状态产生实对角矩阵，复合正是 $\mathcal N$。故式（275.2）两侧相等。

归一化 Choi 态所在的两量子比特迹一 Hermitian 矩阵仿射空间的实维数为十五。可分态是纯乘积态的凸包，有限维 Carathéodory 定理给出至多十六项的分解

$$
J_{\mathcal N}/2=\sum_{k=1}^m w_k\alpha_k\otimes\tau_k,
\qquad m\le16.
$$

取 $F_k=2w_k\alpha_k^{\mathsf T}$，Choi 偏迹约束保证 $\sum_kF_k=I_2$，从而式（275.5）只需十六项。可分 Choi 态集合紧，保迹条件闭，有限模型的最大迹距离连续，所以右侧取得最小值，其经典因子分解也使左侧达到。十六只是充分符号数，不宣称最小。此归约只使用上述已注明的成熟判据和经典寄存器因子分解。

现在计算所列六态的精确误差。模型在 Pauli 共轭和交换 $X,Z$、反转 $Y$ 的 Hadamard 共轭下保持不变。在任一恢复通道上同时平均输入和输出的这些酉作用，最大迹距离不增加，纠缠破坏性保持。Pauli 平均消去 Bloch 平移与非对角系数，Hadamard 平均使 $X,Z$ 两个系数相等，所以可以限制到 Bloch 作用

$$
(x,y,z)\longmapsto(tx,sy,tz).
\tag{275.10}
$$

对于共轭误差，也可作相应平均：输入用 $U$、输出用 $\overline U$。所用 Pauli 和 Hadamard 矩阵的逐项共轭与自身至多相差整体相位，所以其共轭作用相同，仍得到式（275.10）。这些平均只用于相应的通道优化，不假设一般编码的输出预先对角。

先计算共轭缺口。式（275.10）的通道完全正恰要求其 Pauli 混合权重

$$
\frac{1+2t+s}{4},\quad\frac{1-s}{4},\quad
\frac{1-2t+s}{4},\quad\frac{1-s}{4}
\tag{275.11}
$$

非负，分别对应 $I,X,Y,Z$ 共轭。这也可由 Choi 矩阵在 Bell 基中的四个特征值得到。因此 $-1\le s\le1$、$2|t|\le1+s$，特别有 $t\le1$。共轭保持 $X,Z$ 而反转 $Y$，所以模型上的目标误差为

$$
\max\left\{\frac{|1-t|}{2},\frac{\varepsilon|1+s|}{2}\right\}
\ge\max\left\{\frac{1-t}{2},\varepsilon t\right\}
\ge\frac{\varepsilon}{1+2\varepsilon}.
\tag{275.12}
$$

最后一个下界可由两条仿射函数的交点取得：$t\le1/(1+2\varepsilon)$ 时第一项给出下界，反之第二项给出。取

$$
t=\frac1{1+2\varepsilon},\qquad
s=2t-1=\frac{1-2\varepsilon}{1+2\varepsilon},
\tag{275.13}
$$

式（275.11）的权重成为 $t,(1-t)/2,0,(1-t)/2$，均非负且和为一，两种误差同时等于式（275.7）。这也覆盖 $\varepsilon=0$ 的恒等通道。

当 $\varepsilon>0$ 时，模型包含全部三个 Pauli 方向，故层析完备，上面的 PPT 归约把实输出恢复优化化为纠缠破坏通道优化。在式（275.10）中，输入转置把系数 $s$ 变为 $-s$。将两组完全正条件合并，得到

$$
2|t|+|s|\le1.
\tag{275.14}
$$

借助 $2\times2$ PPT 可分性，这也是本 Pauli 对角通道纠缠破坏的充要条件；这里仅将既有 Choi 判据代入当前参数。该量子比特判据及八面体结构的专门论述见 Mary Beth Ruskai，*Qubit Entanglement Breaking Channels*，[arXiv:quant-ph/0302032v3](https://arxiv.org/pdf/quant-ph/0302032v3)，定理1、4及8；本节不将这一通道分类作为新增结论。恢复目标保持三个输入方向，故误差为

$$
\max\left\{\frac{|1-t|}{2},\frac{\varepsilon|1-s|}{2}\right\}.
\tag{275.15}
$$

把 $t,s$ 换为 $|t|,|s|$ 保持可行且不增加误差，因此可取 $t,s\ge0$。由 $2t+s\le1$，有 $t\le1/2$，故第一项至少为 $1/4$；又有 $1-s\ge2t$，式（275.12）的同一交点估计给出下界 $\varepsilon/(1+2\varepsilon)$。因此最优值至少为这两个下界的最大值。

若 $0<\varepsilon\le1/2$，取 $t=1/2,s=0$，误差为 $1/4$。若 $1/2\le\varepsilon\le1$，取

$$
t=\frac1{1+2\varepsilon},\qquad
s=\frac{2\varepsilon-1}{1+2\varepsilon},
\tag{275.16}
$$

有 $2t+s=1$，且两项误差均为 $\varepsilon/(1+2\varepsilon)$。为用四个经典符号达到，令

$$
\begin{aligned}
n_1&=(\sqrt t,\sqrt s,\sqrt t),&n_2&=(\sqrt t,-\sqrt s,-\sqrt t),\\
n_3&=(-\sqrt t,\sqrt s,-\sqrt t),&n_4&=(-\sqrt t,-\sqrt s,\sqrt t).
\end{aligned}
$$

因 $2t+s=1$，四个向量均为单位向量，并有 $\sum_kn_k=0$ 及 $\frac14\sum_kn_kn_k^{\mathsf T}=\operatorname{diag}(t,s,t)$。取 POVM $F_k=(I_2+n_k\cdot\boldsymbol\sigma)/4$，并在结果 $k$ 后制备 $(I_2+n_k\cdot\boldsymbol\sigma)/2$。这些效应非负且和为 $I_2$，第二矩恒等式使恢复 Bloch 作用正好为式（275.10）。这种测量—制备计算与第272节的四面体第二矩计算相同；这里使用的是所给各向异性向量，并不要求它们形成等角 SIC。

若 $0<\varepsilon\le1/2$，最优系数为 $t=1/2,s=0$，还可取三个平面向量 $n_\ell=(\cos(2\pi\ell/3),0,\sin(2\pi\ell/3))$，$\ell=0,1,2$。它们满足 $\sum_\ell n_\ell=0$、$\frac13\sum_\ell n_\ell n_\ell^{\mathsf T}=\operatorname{diag}(1/2,0,1/2)$。用效应 $(I_2+n_\ell\cdot\boldsymbol\sigma)/3$ 和同方向纯态制备，即以三个经典输出符号实现相同最优恢复。所有经典编码和解码都采用式（275.5）之后的全矩阵代数构造，因而是完整 CPTP 映射。

当 $\varepsilon=0$ 时，整个模型只含实的 $X,Z$ 方向及最大混合态；恒等编码和解码已经产生实模型并精确恢复，故 $e_{\mathbb R}=0$。此时层析完备性失效，不能沿用正参数时的纠缠破坏限制。其余比较和极限由两个显式公式直接得到，证毕。

式（275.9）的不连续来自完全实输出的精确约束和模型张成空间的变化。若允许非实残差，恒等编码对每个 $\varepsilon$ 都有定义272.1中的 $e=0,r=\varepsilon$，因此这不是对近似实输出恢复成本的不连续性断言。式（275.7）与（275.8）只比较所列有限状态的迹距离，不包含参考系统；它们给出第272节通用下界的严格例子，不改变该下界或第273节特定模型的等式。

**命题 275.4（精确恢复下的最小非实残差）。** 对式（275.6）的模型，在所有有限维编码与解码、所有共同输出基底中，要求模型精确恢复时，最小非实残差为

$$
\min_{\mathcal D\mathcal E(\rho)=\rho\ (\rho\in\mathcal R_\varepsilon)}r(\mathcal E)
=\frac{\varepsilon}{1+2\varepsilon}.
\tag{275.17}
$$

六维输出足够，且达到构造恢复全部量子比特输入。对于 $\varepsilon>0$ 和每个 $0\le\theta\le1$，还存在同一模型上的编码、解码达到

$$
e=\theta e_{\mathbb R}(\mathcal R_\varepsilon),
\qquad
r=(1-\theta)\delta(\mathcal R_\varepsilon).
\tag{275.18}
$$

式（275.18）给出一条可达线段；下述定理将进一步证明它是最优预算边界。

证明。下界由定理272.2的 $e+r\ge\delta$ 在 $e=0$ 时直接取得。为达到，分别选固定量子比特酉矩阵 $U_x,U_y,U_z$，使第 $b$ 个输入 Pauli 轴在 $U_b$ 共轭下成为输出 $Y$ 轴，其余两个输入坐标轴成为实的 $X,Z$ 轴，允许改变符号。可取 $U_y=I_2$；这样的其余酉矩阵由正交坐标旋转实现。令

$$
w_x=w_z=\frac{\varepsilon}{1+2\varepsilon},
\qquad w_y=\frac1{1+2\varepsilon},
\qquad
\mathcal E_{\rm rev}(X)=\bigoplus_{b=x,y,z}w_bU_bXU_b^*.
\tag{275.19}
$$

三个权重非负且和为一，故这是 CPTP 编码。对任意六维输出 $Y$，定义

$$
\mathcal D_{\rm rev}(Y)=\sum_{b=x,y,z}U_b^*Y_{bb}U_b.
\tag{275.20}
$$

压缩、酉共轭与求和保证完全正，三个对角块迹之和为整个矩阵迹，故解码保迹，并有 $\mathcal D_{\rm rev}\mathcal E_{\rm rev}=\operatorname{id}_{M_2}$。

对第 $b$ 个轴、半径 $a_b$ 的模型状态，只有对应输出块具有虚部。直接计算单个量子比特状态与其共轭的迹距离，得到非实残差 $w_ba_b$。这里 $a_x=a_z=1,a_y=\varepsilon$，三个乘积均为 $\varepsilon/(1+2\varepsilon)$。当 $\varepsilon=0$ 时两个零权重块仍保留在解码定义中，编码仅使用实模型所在的 $y$ 分支，公式照样成立。因此达到式（275.17）。

最后，取定理275.3的实输出最优编码 $\mathcal E_0$ 及解码 $\mathcal D_0$，与上述可逆编码作带正交标签的混合：

$$
\mathcal E_\theta(X)
=\theta\mathcal E_0(X)\oplus(1-\theta)\mathcal E_{\rm rev}(X),
\qquad
\mathcal D_\theta(Y)
=\mathcal D_0(Y_{00})+\mathcal D_{\rm rev}(Y_{11}).
\tag{275.21}
$$

编码和解码都在全部输入上 CPTP。复合等于 $\theta\mathcal D_0\mathcal E_0+(1-\theta)\operatorname{id}$，所以每个状态的恢复误差恰为原误差乘 $\theta$，最大值亦如此。输出直和的第一块完全实，第二块的非实残差乘 $1-\theta$，由迹范数的直和可加性得到式（275.18）。证毕。

**定理 275.5（非实残差预算下的完整最优恢复曲线）。** 固定 $0<\varepsilon\le1$，记

$$
\delta_\varepsilon=\frac{\varepsilon}{1+2\varepsilon},
\qquad b_\varepsilon=\max\left\{\frac14,\delta_\varepsilon\right\}.
$$

对 $R\ge0$，令 $F_\varepsilon(R)$ 为模型 $\mathcal R_\varepsilon$ 上、任意有限输出维数、任意编码、解码及共同输出基底中满足 $r(\mathcal E)\le R$ 时的最小最坏恢复误差。则这个最小值存在，且

$$
\boxed{F_\varepsilon(R)
=b_\varepsilon\max\left\{1-\frac R{\delta_\varepsilon},0\right\}.}
\tag{275.22}
$$

对非负预算 $E,R$，存在同一个编码、解码满足 $e\le E$、$r\le R$ 的充要条件是

$$
\frac E{b_\varepsilon}+\frac R{\delta_\varepsilon}\ge1.
\tag{275.23}
$$

输出维数十对全部预算已经充分；$0<\varepsilon\le1/2$ 时九维已经充分。这些维数不宣称最小。

证明。先证明额外的维数无关下界

$$
4e+\frac r{\delta_\varepsilon}\ge1.
\tag{275.24}
$$

取任意编码、解码和定义 $r$ 时使用的输出基底。令 $T_2,T_D$ 为相应输入、输出转置，定义

$$
\overline{\mathcal E}=T_D\mathcal ET_2,
\qquad \mathcal N=\mathcal D\mathcal E,
\qquad \mathcal C=\mathcal D\overline{\mathcal E}.
\tag{275.25}
$$

共轭 Kraus 算子给出 $\overline{\mathcal E}$ 的 CPTP 性；所以 $\mathcal N,\mathcal C$ 都是量子比特通道。由于 $T_2^2=\operatorname{id}$，对每个模型状态都有

$$
\begin{aligned}
\frac12\|\mathcal N(\rho)-\mathcal C(T_2\rho)\|_1
&=\frac12\|\mathcal D(\mathcal E\rho-T_D\mathcal E\rho)\|_1\\
&\le\frac12\|\mathcal E\rho-T_D\mathcal E\rho\|_1
\le r.
\end{aligned}
\tag{275.26}
$$

输入是 Hermitian 态，故其输出的转置等于逐项共轭，最后一项正是非实残差的逐态界。第一步收缩作用于 Hermitian 矩阵差，不把 $T_D$ 本身当作完全正映射。

同时平均通道对 $(\mathcal N,\mathcal C)$。对于保持模型的 Pauli 与 Hadamard 群元素 $U$，将二者分别变成

$$
\operatorname{Ad}_{U^*}\mathcal N\operatorname{Ad}_U,
\qquad
\operatorname{Ad}_{U^*}\mathcal C\operatorname{Ad}_{\overline U}.
\tag{275.27}
$$

恒等式 $T_2\operatorname{Ad}_U=\operatorname{Ad}_{\overline U}T_2$ 保证式（275.26）在模型标签重排后保持同一界；恢复误差也不增加。平均后两个映射仍是 CPTP。所用群中每个 $U$ 与 $\overline U$ 至多相差整体相位，故第275.3节的同一对角化给出 Bloch 系数

$$
\mathcal N:(t,s,t),\qquad
\mathcal C:(u,v,u).
\tag{275.28}
$$

这里不需要平均后的通道对仍来自原编码和解码；只把它们作为原方案必然给出的满足上述界的 CPTP 通道对。

模型的 $X,Z$ 方向为纯态，恢复误差界给出

$$
t\ge1-2e.
\tag{275.29}
$$

式（275.26）在 $X,Z$ 方向给出 $|t-u|/2\le r$，在半径 $\varepsilon$ 的 $Y$ 方向给出 $\varepsilon|s+v|/2\le r$。因此

$$
u\ge t-2r,
\qquad v\le-s+\frac{2r}{\varepsilon}.
\tag{275.30}
$$

两个通道的完全正约束分别蕴含 $s\ge2|t|-1\ge2t-1$ 和 $2u\le2|u|\le1+v$。将它们与式（275.29）—（275.30）组合，得到

$$
3-8e\le4t-1\le2t+s
\le1+\left(4+\frac2\varepsilon\right)r
=1+\frac{2r}{\delta_\varepsilon}.
\tag{275.31}
$$

整理即得式（275.24）。此推导只用最终的两个量子比特通道，没有输出维数或编码基底的限制。

再与定理272.2的 $e+r\ge\delta_\varepsilon$ 以及 $e\ge0$ 合并，可得

$$
e\ge\max\left\{
0,\ \delta_\varepsilon-r,\ \frac14\left(1-\frac r{\delta_\varepsilon}\right)
\right\}
=b_\varepsilon\max\left\{1-\frac r{\delta_\varepsilon},0\right\}.
\tag{275.32}
$$

若 $r\le\delta_\varepsilon$，两条非零仿射界共享因子 $1-r/\delta_\varepsilon$，较大系数是 $b_\varepsilon$；若 $r\ge\delta_\varepsilon$，两者均非正。右端关于 $r$ 单调不增，故 $r\le R$ 进一步给出式（275.22）的下界。

取命题275.4的混合编码，并令

$$
\theta=\max\left\{1-\frac R{\delta_\varepsilon},0\right\}.
$$

由定理275.3，$e_{\mathbb R}=b_\varepsilon$；式（275.18）于是给出 $e=\theta b_\varepsilon$、$r=(1-\theta)\delta_\varepsilon\le R$，精确达到下界。当 $R\ge\delta_\varepsilon$ 时直接使用可逆编码，恢复误差为零。两种方案的直和输出维数至多为 $4+6=10$；小参数区间的实输出方案只需三维，故九维足够。式（275.23）就是 $E\ge F_\varepsilon(R)$ 的等价预算形式。证毕。

对固定正 $\varepsilon$，式（275.22）关于非实残差预算连续。若以相对预算 $R=\lambda\delta_\varepsilon$、$0\le\lambda\le1$ 趋向 $\varepsilon\downarrow0$，最小恢复误差趋向 $(1-\lambda)/4$；特别地，趋零的非实残差预算可以与零恢复误差相容，而恒取严格的 $R=0$ 会保留 $1/4$ 的正参数极限。这些是同一预算曲线的不同极限，不把几乎为实与严格为实交换使用。

<a id="entry-900"></a>

## 追加锚（本行以下为增补区）

<a id="section-276"></a>

## 276. 三轴半径的倒数三角条件与完整误差预算

**定义 276.1（正半径三轴模型）。** 令 $0<a_i\le1$，$i=1,2,3$，并以 $\sigma_1=X,\sigma_2=Y,\sigma_3=Z$ 定义六态模型

$$
\mathcal R_a=\{(I_2\pm a_i\sigma_i)/2:i=1,2,3\}.
\tag{276.1}
$$

记

$$
\alpha_i=\frac1{a_i},\qquad
S=\alpha_1+\alpha_2+\alpha_3,\qquad
\Delta=\frac1S,
\qquad B=\max\left\{\Delta,\max_{i<j}\frac1{2(\alpha_i+\alpha_j)}\right\}.
\tag{276.2}
$$

沿用第272、275节的共轭缺口 $\delta$、恢复误差 $e$、非实残差 $r$ 及完全实输出恢复误差 $e_{\mathbb R}$。对非负预算 $R$，令 $F_a(R)$ 为在所有有限输出维数、所有复线性 CPTP 编码、解码及共同输出基底上，满足 $r\le R$ 时的最小恢复误差；下述达到构造保证最小值存在。

**定理 276.2（全部三轴半径的最优预算曲线）。** 定义276.1中有

$$
\delta(\mathcal R_a)=\Delta,
\qquad e_{\mathbb R}(\mathcal R_a)=B,
\qquad
\boxed{F_a(R)=B\max\{1-R/\Delta,0\}.}
\tag{276.3}
$$

精确恢复条件下的最小非实残差为 $\Delta$。对任意非负 $E,R$，同一编码与解码能满足 $e\le E,r\le R$ 的充要条件为

$$
E/B+R/\Delta\ge1.
\tag{276.4}
$$

十维输出对全部这些预算已经充分，不宣称最小。完全实输出的最优编码可使用四个经典结果，精确恢复且非实残差最小时可使用六维输出并恢复所有量子比特输入。

此外，

$$
\boxed{e_{\mathbb R}(\mathcal R_a)=\delta(\mathcal R_a)
\quad\Longleftrightarrow\quad
\alpha_k\le\alpha_i+\alpha_j
\text{ 对每个 }\{i,j,k\}=\{1,2,3\}.}
\tag{276.5}
$$

因此这两个误差相等，恰在三个半径的倒数满足非严格三角不等式时发生。

证明。以下 Pauli 平均仅改变允许的通道，不改变输入六态的标签集合；酉不变性与凸性保证最大迹距离不增加。它消去 Bloch 平移和非对角系数，但不置换三个半径，故不要求半径相等。

先计算共轭缺口。平均后的信道记为 Bloch 对角系数 $(\lambda_1,\lambda_2,\lambda_3)$，令

$$
(\mu_1,\mu_2,\mu_3)=(\lambda_1,-\lambda_2,\lambda_3).
$$

这将目标转置的符号吸收进系数。Pauli 信道的一个 Choi 非负条件为

$$
1-\lambda_1+\lambda_2-\lambda_3\ge0,
\qquad\text{即 }\sum_i\mu_i\le1.
\tag{276.6}
$$

若最大共轭误差为 $g$，每个方向上都有 $a_i|1-\mu_i|/2\le g$，从而 $\mu_i\ge1-2g\alpha_i$。求和并用式（276.6），得到 $3-2gS\le1$，所以 $g\ge\Delta$。

取 $\mu_i=1-2\Delta\alpha_i$，对应的实际信道系数为 $(\mu_1,-\mu_2,\mu_3)$。其 $I,X,Y,Z$ 共轭混合概率分别为

$$
p_I=\Delta\alpha_2,\qquad
p_X=\Delta\alpha_3,\qquad p_Y=0,\qquad
p_Z=\Delta\alpha_1.
\tag{276.7}
$$

这些概率非负且和为一，故定义 CPTP 信道；六个状态上的误差均为 $\Delta$。某些 $\mu_i$ 可以为负，这不影响实际信道的完全正性。由此证明 $\delta=\Delta$。

三个半径严格正，模型实线性张成整个 Hermitian 矩阵空间。因此第275节证明中的 PPT 归约适用：任意完全实输出编码的恢复复合都是量子比特纠缠破坏通道；反之每个这种通道都可经有限经典寄存器因子分解。用 Pauli 平均把恢复通道化为对角系数 $(t_1,t_2,t_3)$，其纠缠破坏条件为 $\sum_i|t_i|\le1$。这个已知条件采用 Ruskai，*Qubit Entanglement Breaking Channels*，[arXiv:quant-ph/0302032v3](https://arxiv.org/pdf/quant-ph/0302032v3)，定理1、4及8；这里使用它优化所给六态上的误差，不新增该通道分类。

将各 $t_i$ 替换为 $|t_i|$ 保持可行且不增加恢复误差，所以可取 $t_i\ge0$。一个误差预算 $b\ge0$ 在这个优化中可行，恰当且仅当

$$
\sum_i\max\{1-2b\alpha_i,0\}\le1.
\tag{276.8}
$$

必要性由逐方向误差界与 $\sum_it_i\le1$ 得到；充分性取 $t_i=\max\{1-2b\alpha_i,0\}$。

按大小记 $\alpha_1\le\alpha_2\le\alpha_3$，只用于分析这个对称标量式。令 $A=\alpha_1+\alpha_2$。若 $\alpha_3\le A$，则 $\Delta\le1/(2\alpha_3)$，三个数 $1-2\Delta\alpha_i$ 均非负且和为一，故 $b=\Delta$ 可行；小于 $\Delta$ 时未截断的和已经大于一，截断只会增加该和，因而不可行。若 $\alpha_3>A$，则取 $b=1/(2A)$ 时第三项为零，前两项之和为一；小于该值时前两项之和大于一，故不可行。因此

$$
e_{\mathbb R}
=\begin{cases}
\Delta,&\alpha_3\le\alpha_1+\alpha_2,\\
\dfrac1{2(\alpha_1+\alpha_2)},&\alpha_3>\alpha_1+\alpha_2,
\end{cases}
\tag{276.9}
$$

这正是定义276.1中的 $B$，并且证明式（276.5），因为最大的倒数满足三角不等式即保证其余两条。

为显式达到完全实输出最优值，取 $t_i=\max\{1-2B\alpha_i,0\}$；上面的分类表明 $\sum_it_i=1$。用四个向量

$$
\begin{aligned}
n_1&=(\sqrt{t_1},\sqrt{t_2},\sqrt{t_3}),&
n_2&=(\sqrt{t_1},-\sqrt{t_2},-\sqrt{t_3}),\\
n_3&=(-\sqrt{t_1},\sqrt{t_2},-\sqrt{t_3}),&
n_4&=(-\sqrt{t_1},-\sqrt{t_2},\sqrt{t_3})
\end{aligned}
\tag{276.10}
$$

定义效应 $F_k=(I_2+n_k\cdot\boldsymbol\sigma)/4$ 和制备态 $\tau_k=(I_2+n_k\cdot\boldsymbol\sigma)/2$。单位长度、零均值和第二矩 $\frac14\sum_kn_kn_k^{\mathsf T}=\operatorname{diag}(t_1,t_2,t_3)$ 保证这是一组 POVM，且测量—制备复合具有指定 Bloch 系数。因此四个实对角记录足以达到 $B$，包括某个最优系数为零的情形。

精确恢复的最小非实残差用与命题275.4相同的可逆带标签结构达到。选 $U_i$ 把第 $i$ 个输入 Pauli 轴旋到输出的 $Y$ 轴，并把其他输入坐标轴旋到实坐标轴。令

$$
w_i=\Delta\alpha_i,
\qquad
\mathcal E_{\rm rev}(X)=\bigoplus_iw_iU_iXU_i^*,
\qquad
\mathcal D_{\rm rev}(Y)=\sum_iU_i^*Y_{ii}U_i.
\tag{276.11}
$$

权重和为一，压缩迹相加，故两者都是全输入空间上的 CPTP 映射，且复合为恒等。对第 $i$ 个输入轴的状态，只有第 $i$ 个输出块有虚部，非实残差是 $w_ia_i=\Delta$。普遍下界 $e+r\ge\delta$ 在 $e=0$ 时给出反向界，因而最小值确为 $\Delta$。

现在证明完整预算曲线的下界。对任意有限维编码和解码，沿定理275.5定义

$$
\mathcal N=\mathcal D\mathcal E,
\qquad\mathcal C=\mathcal D\overline{\mathcal E},
\qquad\overline{\mathcal E}=T_D\mathcal ET_2.
$$

两个复合均为量子比特 CPTP 映射，且每个模型态满足

$$
\frac12\|\mathcal N(\rho)-\mathcal C(T_2\rho)\|_1\le r.
\tag{276.12}
$$

按照式（275.27）同时作 Pauli 平均，保持上述界和恢复误差上界。记所得 $\mathcal N$ 的 Bloch 系数为 $n_i$，所得 $\mathcal C$ 的系数经目标转置符号调整后为 $\mu_i$。逐轴误差与式（276.12）给出

$$
n_i\ge1-2e\alpha_i,
\qquad |n_i-\mu_i|\le2r\alpha_i.
\tag{276.13}
$$

由 $\mathcal C$ 的 Choi 条件（276.6），有

$$
\sum_in_i\le1+2rS.
\tag{276.14}
$$

另一方面，$\mathcal N$ 的完全正性对每个不同指标 $i,j,k$ 给出 $1+n_k\ge|n_i+n_j|$，所以

$$
\sum_\ell n_\ell
\ge2(n_i+n_j)-1
\ge3-4e(\alpha_i+\alpha_j).
\tag{276.15}
$$

合并（276.14）—（276.15），得到对每一对指标都成立的必要条件

$$
2e(\alpha_i+\alpha_j)+rS\ge1.
\tag{276.16}
$$

这些推导允许各 $n_i$ 为负，也不要求平均后的通道对仍可分解为原编码、解码；它们只是每个原方案必然满足的通道正性限制。对式（276.13）的第一组不等式求和，再用式（276.14），还直接得到 $3-2eS\le1+2rS$，即 $e+r\ge\Delta$。将它与式（276.16）和 $e\ge0$ 合并，得到

$$
e\ge B\max\{1-r/\Delta,0\}.
\tag{276.17}
$$

右端随 $r$ 不增，故 $r\le R$ 时也给出式（276.3）的下界。

最后，将四维实输出最优编码与六维可逆编码作正交标签混合，权重为 $\theta$、$1-\theta$，并由对应的两个完整解码分支求和。与式（275.21）的逐态计算相同，这给出

$$
e=\theta B,\qquad r=(1-\theta)\Delta.
$$

取 $\theta=\max\{1-R/\Delta,0\}$ 即达到下界；十维输出包含全部分支，端点也保留解码的全空间保迹性。预算等价式（276.4）随即成立。证毕。

**命题 276.3（三角缺量与退化边界）。** 若 $\alpha_1\le\alpha_2\le\alpha_3$ 且 $\alpha_3>\alpha_1+\alpha_2$，令 $A=\alpha_1+\alpha_2$，则

$$
e_{\mathbb R}(\mathcal R_a)-\delta(\mathcal R_a)
=\frac{\alpha_3-A}{2A(A+\alpha_3)}.
\tag{276.18}
$$

在允许某个半径等于零的扩展定义中，六态模型具有精确可恢复实编码，且共轭缺口为零。若另两个半径 $a,b>0$ 固定，第三半径从正值趋零，则

$$
\lim e_{\mathbb R}=\frac{ab}{2(a+b)}>0,
\qquad\lim\delta=0,
\tag{276.19}
$$

而退化模型本身的 $e_{\mathbb R}$ 为零。

证明。式（276.18）由（276.9）与 $\Delta=1/(A+\alpha_3)$ 相减直接得到。某个半径为零时，全部非零 Bloch 向量位于同一个过原点平面；用固定量子比特酉旋转把这个平面送到 $XZ$ 平面，编码后的模型全部为实，逆酉解码精确恢复。由定理272.2，该模型的共轭缺口也为零。第三半径趋零意味着其倒数趋正无穷，故最终处在（276.9）的第二种情形；代入 $A=1/a+1/b$ 即得式（276.19）。这里的三角条件属于三个模型尺度的倒数参数，不把它解释为空间距离的物理三角关系。证毕。

<a id="entry-902"></a>

## 追加锚（本行以下为增补区）

<a id="section-277"></a>

## 277. 实量子记录的最小维数与三维压缩

**定义 277.1（达到实输出最优误差的最小维数）。** 对定义276.1的正半径六态模型，令 $D_*(a)$ 为存在复线性 CPTP 编码 $\mathcal E:M_2\to M_D$、解码 $\mathcal D:M_D\to M_2$，使全部编码模型态在同一个基底中为实，且恢复误差达到 $B$ 的最小正整数 $D$。这里 $B$ 与 $\Delta$ 取式（276.2）。输出可以是互不对易的实密度矩阵，不要求是一个可完全区分的经典寄存器。

**定理 277.2（倒数三角条件决定最小实输出维数）。** 对三个严格正的半径，有

$$
D_*(a)=
\begin{cases}
3,&\alpha_k<\alpha_i+\alpha_j\quad\text{对所有不同 }i,j,k,\\
2,&\text{至少一条上述严格不等式不成立}.
\end{cases}
\tag{277.1}
$$

在第一种情形中，最优编码可以先作四结果 POVM，再制备四个不正交的实三维纯态。其解码由到两个量子比特对称子空间的等距嵌入和一个偏迹给出。若在这个严格三角区域把输出限定为对角经典记录，则最少需要四个符号。在第二种情形中，二维实量子输出已足够。

因此，定理276.2的全部误差预算边界可以分别在九维和八维输出中达到；这一预算构造的维数不宣称最小。

证明。先证明严格三角区域内最优恢复通道的唯一性。此时 $B=\Delta$，令

$$
t_i=1-2\Delta\alpha_i>0,\qquad\sum_it_i=1.
\tag{277.2}
$$

任意完全实输出编码的恢复复合 $\mathcal N=\mathcal D\mathcal E$，由第275节证明中的标准 PPT 归约，是量子比特纠缠破坏通道。写其仿射 Bloch 作用为 $v\mapsto c+Tv$。采用 Horodecki、Shor、Ruskai，*Entanglement Breaking Channels*，[arXiv:quant-ph/0302031v2](https://arxiv.org/pdf/quant-ph/0302031v2)，定理4的测量—制备表示，把 POVM 效应和制备态分别写成 $w_k(I+s_k\cdot\boldsymbol\sigma)$ 和 $(I+r_k\cdot\boldsymbol\sigma)/2$，其中 $|s_k|,|r_k|\le1$、$\sum_kw_k=1$。于是

$$
T=\sum_kw_kr_ks_k^{\mathsf T},
\qquad\operatorname{Tr}T\le1.
\tag{277.3}
$$

这只是既有纠缠破坏表示的直接估计，不作为新的通道分类。

对每个轴的正负两个模型态，误差上界 $\Delta$ 意味着

$$
\|c\pm a_i(Te_i-e_i)\|_2\le2\Delta.
$$

由这两个不等式得 $T_{ii}\ge1-2\Delta\alpha_i=t_i$。三个对角下界之和已经为一，与式（277.3）结合，迫使每个 $T_{ii}=t_i$。将同一对不等式平方后取平均，得到

$$
\|c\|_2^2+a_i^2\|Te_i-e_i\|_2^2\le4\Delta^2.
\tag{277.4}
$$

其中第 $i$ 个对角坐标单独已经贡献 $a_i^2(t_i-1)^2=4\Delta^2$，所以 $c=0$，每列的全部非对角坐标也为零。因此最优恢复通道必须是

$$
\mathcal N:\ v\longmapsto\operatorname{diag}(t_1,t_2,t_3)v.
\tag{277.5}
$$

这证明实际最优通道的唯一性，并非只确定它的 Pauli 平均。

若输出维数为二，层析完备性保证编码在整个 Hermitian 输入空间上的像都属于输出基底中的实对称矩阵空间。这个实向量空间维数为三，故恢复复合在 Hermitian 空间上的秩至多为三。然而式（277.5）在 $I,X,Y,Z$ 上的特征值为 $1,t_1,t_2,t_3$，全部非零，秩为四，矛盾。因此严格三角情形必须有 $D\ge3$。若编码输出限定在 $m$ 个经典符号的对角代数内，其 Hermitian 像空间维数至多为 $m$，同一秩四结论迫使 $m\ge4$；第276节的四结果构造达到这个经典下界。

下面给出三维达到构造。取式（276.10）的四个单位 Bloch 向量 $n_k$，并选单位量子比特向量 $\psi_k$ 使

$$
P_k=|\psi_k\rangle\langle\psi_k|
=(I+n_k\cdot\boldsymbol\sigma)/2.
$$

令 $\zeta_k=\psi_k\otimes\psi_k$，它们都位于三维复空间 $\operatorname{Sym}^2(\mathbb C^2)$。任取互异的 $i,j,k$，由 Pauli 乘法得到标准三阶 Bargmann 公式

$$
\operatorname{Tr}(P_iP_jP_k)
=\frac{1+n_i\cdot n_j+n_j\cdot n_k+n_k\cdot n_i
+i\,n_i\cdot(n_j\times n_k)}4.
\tag{277.6}
$$

四个 $n_k$ 之和为零、长度均为一，所以任意三个的两两内积之和为 $-1$。又因三个 $t_i$ 严格正，标量三重积非零。因此式（277.6）为非零纯虚数。张量平方使三阶内积乘积成为这个数的平方，故对 $\zeta_i,\zeta_j,\zeta_k$ 的相应循环乘积为严格负实数。

所有两两内积也非零：$|\langle\psi_i,\psi_j\rangle|^2$ 等于某个正的 $t_\ell$。分别改变 $\zeta_2,\zeta_3,\zeta_4$ 的整体相位，使它们与 $\zeta_1$ 的内积为正实数。每个含指标 $1$ 的三阶循环乘积为负实数，遂迫使其余两两内积全为负实数。得到的四个向量 $\zeta'_k$ 具有实 Gram 矩阵

$$
G=\begin{pmatrix}
1&t_1&t_2&t_3\\
t_1&1&-t_3&-t_2\\
t_2&-t_3&1&-t_1\\
t_3&-t_2&-t_1&1
\end{pmatrix}.
\tag{277.7}
$$

令 $h_i=\sqrt{(1-t_i)/2}$，显式取

$$
\begin{aligned}
v_1&=(h_1,h_2,h_3),&v_2&=(-h_1,h_2,h_3),\\
v_3&=(h_1,-h_2,h_3),&v_4&=(h_1,h_2,-h_3).
\end{aligned}
$$

因 $\sum_ih_i^2=1$，这些都是实三维单位向量，直接内积得到式（277.7）。以它们为列的实矩阵，其三个坐标行两两正交，行范数平方为 $4h_i^2=2(1-t_i)$。所以 $G$ 的特征值为 $0,2(1-t_1),2(1-t_2),2(1-t_3)$，秩恰为三。相同 Gram 矩阵给出复线性等距映射

$$
W:\mathbb C^3\longrightarrow\operatorname{Sym}^2(\mathbb C^2)
\subset\mathbb C^2\otimes\mathbb C^2,
\qquad Wv_k=\zeta'_k.
\tag{277.8}
$$

具体地，相同 Gram 矩阵保证规定 $v_k\mapsto\zeta'_k$ 的线性映射良定且保持内积。循环量与共同实坐标的这种联系沿用第229节所用的成熟 Gram 方法；见 Chaturvedi 等，*Null Phase Curves and Manifolds in Geometric Phase Theory*，[arXiv:1302.0206v1](https://arxiv.org/abs/1302.0206v1)，式（2.10）、（3.6）及（4.11）—（4.13）。本构造允许负的循环量，不要求文献中更强的正循环 null-phase 条件。

以 $F_k=(I+n_k\cdot\boldsymbol\sigma)/4=P_k/2$ 定义

$$
\mathcal E(X)=\sum_{k=1}^4\operatorname{Tr}(F_kX)|v_k\rangle\langle v_k|,
\qquad
\mathcal D(Y)=\operatorname{Tr}_2(WYW^*).
\tag{277.9}
$$

四个 $F_k$ 是 POVM，故编码是 CPTP，且对所有状态都产生实矩阵。等距嵌入与偏迹使解码在整个 $M_3$ 上 CPTP。由式（277.8），解码把第 $k$ 个实三维记录态送到 $P_k$，因为张量平方的偏迹恰为 $P_k$，整体相位不影响密度矩阵。因此复合正是第276节达到最优值的测量—制备通道，Bloch 系数为 $t_i$。它达到 $B$，证明严格三角情形 $D_*=3$。式（277.7）的非零非单位内积说明这些实记录态不正交，不能把它们当作四个可完全区分的经典标签。

若至少一条严格三角不等式不成立，按大小排列倒数，使 $\alpha_3\ge\alpha_1+\alpha_2$。第276节的最优系数为

$$
t_1=\frac{\alpha_2}{\alpha_1+\alpha_2},\qquad
t_2=\frac{\alpha_1}{\alpha_1+\alpha_2},\qquad t_3=0.
\tag{277.10}
$$

这里两个非零系数严格正且和为一，对应 CPTP 纠缠破坏通道 $\mathcal N$。其全部状态输出都位于某个过原点的 Bloch 平面。取酉矩阵 $U$ 将这个平面旋到实的 $XZ$ 平面，令 $\mathcal E=\operatorname{Ad}_U\mathcal N$、$\mathcal D=\operatorname{Ad}_{U^*}$，便以二维实输出达到同一个恢复通道。等号边界也包含在这个构造中。

一维输出只能产生固定恢复态。正负两个半径为 $a_i$ 的轴态之间迹距离为 $a_i$，三角不等式给出固定恢复态最坏误差至少 $\max_i a_i/2$，而最大混合态达到此值。另一方面，式（276.2）给出 $B\le\max_i a_i/3<\max_i a_i/2$，所以一维输出在所有正半径模型上都不够。由此完成式（277.1）。

最后，将本节的三维或二维实最优编码，与第276节六维可逆编码作正交直和混合，仍逐态达到 $e=\theta B,r=(1-\theta)\Delta$，输出维数分别为九或八。两个解码分支均在完整空间上保迹，故也覆盖端点。证毕。

**定理 277.3（等半径六态的二维完整预算曲线）。** 对 $a_1=a_2=a_3=a$、$0<a\le1$，令 $F_{a,2}(R)$ 为固定输出维数二、允许任意复线性 CPTP 编码、解码及共同输出基底、满足非实残差 $r\le R$ 时的最小恢复误差。则

$$
\boxed{F_{a,2}(R)=\frac{a}{2\sqrt2}
\max\{1-\sqrt3R/a,0\}.}
\tag{277.11}
$$

对任意非负预算 $E,R$，存在同一个二维方案满足 $e\le E,r\le R$，恰当且仅当

$$
\frac{2\sqrt2}{a}E+\frac{\sqrt3}{a}R\ge1.
\tag{277.12}
$$

特别地，二维记忆精确恢复时的最小非实残差为 $a/\sqrt3$。在固定输出维数 $D$ 的全部严格实模型输出编码中，最小恢复误差为

$$
e_{\mathbb R,D}=
\begin{cases}
a/2,&D=1,\\
a/(2\sqrt2),&D=2,\\
a/3,&D\ge3.
\end{cases}
\tag{277.13}
$$

证明。先证明任意二维方案的下界。固定计算非实残差时使用的输出基底，将编码写成 Bloch 仿射作用 $v\mapsto c+Av$，解码的线性部分记为 $L$。恢复复合的作用写成 $v\mapsto d+Tv$，其中 $T=LA$。输出态与其共轭的迹距离等于其 $Y$ 坐标绝对值，因此对六个模型态，

$$
r=|c_y|+a\max_i|A_{yi}|.
\tag{277.14}
$$

量子比特通道的迹距离收缩性给出 $\|L\|_{\rm op}\le1$。由最小奇异值的变分定义和式（277.14），得到

$$
s_{min}(T)\le\|L\|_{\rm op}s_{min}(A)
\le s_{min}(A)\le\|e_y^{\mathsf T}A\|_2
\le\sqrt3r/a.
\tag{277.15}
$$

这里最后两步只限制实际编码的一行，不对编码或解码作会改变共同因子分解的平均。

还需要恢复复合的完全正约束。对任意量子比特通道 $\mathcal N$，记自旋反转为 $\mathcal S(X)=Y X^{\mathsf T}Y$。虽然 $\mathcal S$ 本身不完全正，但双侧复合 $\mathcal S\mathcal N\mathcal S$ 完全正：它由 $T\mathcal NT$ 的共轭 Kraus 表示及两次酉共轭组成。两者均保迹。在 Bloch 坐标中，这个复合把平移 $d$ 变成 $-d$、保持线性部分 $T$，所以

$$
\mathcal N_0=(\mathcal N+\mathcal S\mathcal N\mathcal S)/2
\tag{277.16}
$$

是线性部分仍为 $T$ 的幺元 CPTP 通道。此步骤只提取实际恢复矩阵必然满足的完全正条件，不改变式（277.15）的来源。

设 $s_1\ge s_2\ge s_3\ge0$ 为 $T$ 的奇异值。幺元量子比特通道的酉规范形式可取对角系数 $(s_1,s_2,\epsilon s_3)$，其中 $\epsilon\in\{1,-1\}$ 吸收行列式符号，零奇异值时任选适当符号。标准 Pauli Choi 条件给出

$$
s_1+s_2\le1+\epsilon s_3\le1+s_3,
\qquad 0\le s_i\le1.
\tag{277.17}
$$

这里使用的是 Ruskai，*Qubit Entanglement Breaking Channels*，[arXiv:quant-ph/0302032v3](https://arxiv.org/pdf/quant-ph/0302032v3)，式（3）的 Bloch 酉规范形式，以及第2节式（5）和第4节的完全正条件；不把它当作新结论，也不要求当前非实输出方案的恢复通道纠缠破坏。

由 $\operatorname{Tr}T\le s_1+s_2+s_3$ 和式（277.17），有

$$
\begin{aligned}
\|I-T\|_F^2
&\ge\sum_{i=1}^3(1-s_i)^2\\
&\ge\frac12(2-s_1-s_2)^2+(1-s_3)^2\\
&\ge\frac32(1-s_3)^2.
\end{aligned}
\tag{277.18}
$$

最坏迹距离控制六个模型态的平均平方 Bloch 误差，故

$$
4e^2\ge\|d\|_2^2+\frac{a^2}{3}\|I-T\|_F^2
\ge\frac{a^2}{2}(1-s_3)^2.
$$

若 $r\le a/\sqrt3$，用式（277.15）得到 $e\ge a(1-\sqrt3r/a)/(2\sqrt2)$；若 $r\ge a/\sqrt3$，使用 $e\ge0$。右侧关于 $r$ 不增，因而得到预算 $r\le R$ 所需的下界。

为达到，取 $n=(1,1,1)/\sqrt3$、$0\le q\le1$，并定义幺元恢复通道的 Bloch 矩阵

$$
T_q=\frac{1+q}{2}(I-nn^{\mathsf T})+qnn^{\mathsf T}.
\tag{277.19}
$$

它的酉规范对角系数为 $((1+q)/2,(1+q)/2,q)$，四个 Pauli 混合概率为 $(1+q)/2,(1-q)/4,(1-q)/4,0$，均非负且和为一，故定义 CPTP 通道 $\mathcal N_q$。取酉矩阵 $U$ 将方向 $n$ 旋到输出 $Y$ 轴，令 $\mathcal E=\operatorname{Ad}_U\mathcal N_q$、$\mathcal D=\operatorname{Ad}_{U^*}$。恢复复合正是 $\mathcal N_q$，编码的输出虚坐标为 $q\,n\cdot v$，所以 $r=aq/\sqrt3$。

另一方面，$I-T_q=(1-q)(I+nn^{\mathsf T})/2$，每个轴上都有 $\|(I+nn^{\mathsf T})e_i\|_2^2=1+3n_i^2=2$，因此全部六态的迹距离恢复误差均为 $a(1-q)/(2\sqrt2)$。取 $q=\min\{\sqrt3R/a,1\}$ 即达到式（277.11）；这也证明最小值存在、式（277.12）及精确恢复的残差门槛。

令 $R=0$ 得到式（277.13）的二维值。一维值由定理277.2证明中的固定态估计给出；$D\ge3$ 的下界为定理276.2的 $a/3$，且本节三维构造达到它。更大输出维数可等距补零嵌入，并在未使用子空间上将解码补为任一固定态制备，以保持全空间 CPTP。证毕。

<a id="entry-904"></a>

## 追加锚（本行以下为增补区）

<a id="section-278"></a>

## 278. 精确恢复的三维支撑障碍与四维改进

**定义 278.1（固定输出维数的精确恢复残差）。** 对定义276.1的正半径六态模型，令 $R_D(a)$ 为所有输出维数为 $D$、在模型上精确恢复的复线性 CPTP 编码、解码及共同输出基底中，非实残差 $r$ 的下确界。对 $D\ge2$，等距编码与补全解码保证可行集非空。记

$$
\eta=\left(\sum_i\alpha_i^2\right)^{-1/2},
\qquad
\Lambda=\min_i\frac1{\alpha_i+\sqrt{\sum_{j\ne i}\alpha_j^2}},
\qquad\alpha_i=1/a_i.
\tag{278.1}
$$

**定理 278.2（二维与三维精确恢复的共同残差门槛）。** 对所有 $0<a_i\le1$，有

$$
R_2(a)=R_3(a)=\eta,
\tag{278.2}
$$

且两个下确界均达到。若三维方案达到该值，则在计算残差的共同输出基底中，其编码的二维占用支撑必对逐项共轭不变。

此外，取 $\Delta=(\sum_i\alpha_i)^{-1}$，有

$$
\Delta\le R_D(a)\le\Lambda<\eta\quad(D=4,5),
\qquad R_D(a)=\Delta\quad(D\ge6),
\tag{278.3}
$$

并且 $\Delta<\Lambda$。因此达到全维数最优精确恢复残差的最小输出维数属于 $\{4,5,6\}$。在等半径情形 $a_i=a$，这些量为

$$
\Delta=a/3,\qquad
\Lambda=a(\sqrt2-1),\qquad
\eta=a/\sqrt3.
\tag{278.4}
$$

证明。模型张成整个 Hermitian 量子比特空间，所以在六态上精确恢复，已使 $\mathcal D\mathcal E=\operatorname{id}_{M_2}$ 在整个复矩阵代数上成立。使用 Nayak–Sen，*Invertible Quantum Operations and Perfect Encryption of Quantum States*，[arXiv:quant-ph/0605041v4](https://arxiv.org/pdf/quant-ph/0605041v4)，定理2.1的可恢复信道正规形，编码在占用空间上可写成

$$
\mathcal E(X)=V(X\otimes\tau)V^*,
\qquad 2\operatorname{rank}\tau\le D.
\tag{278.5}
$$

这是已有正规形在当前完整恢复任务中的应用。对 $D=2,3$，辅助态只能秩一，故编码是等距映射 $\mathcal E(X)=VXV^*$。二维情况可在一个实的额外坐标上补零，归入三维等距编码；这种补零保持非实残差。

固定计算残差的三维输出基底，记逐项共轭为 $K$，并令 $P=\operatorname{im}V$。两个复二维子空间 $P,KP\subset\mathbb C^3$ 的交至少复一维，且这个交在 $K$ 下不变，因此其中有一个实单位向量。取它作输入某个正交基的第一个像，再作实正交输出基变换，使第一个编码列为 $e_1$。

第二列位于 $\operatorname{span}_{\mathbb C}\{e_2,e_3\}$。改变其整体相位，可以使其复双线性自内积为非负实数；当该自内积为零时任取相位。于是其实部、虚部正交，且实部范数不小于虚部范数。再对这两个实坐标作正交变换，得到

$$
V|0\rangle=e_1,
\qquad
V|1\rangle=c e_2+i s e_3,
\qquad c^2+s^2=1,\quad c\ge s\ge0.
\tag{278.6}
$$

所有输出变换均为实正交变换，故保持与 $K$ 共轭的迹距离。输入基变换将原来的三个 Pauli 轴送到三个正交单位 Bloch 向量 $n_1,n_2,n_3$，各自半径仍为 $a_i$；不把不同半径互换。

对新输入基底中 Bloch 向量为 $v=(x,y,z)$ 的状态，编码矩阵的三个上三角非实分量给出

$$
\mathcal E(\rho_v)-\overline{\mathcal E(\rho_v)}
=
\begin{pmatrix}
0&-icy&-isx\\
icy&0&-ics(1-z)\\
isx&ics(1-z)&0
\end{pmatrix}.
\tag{278.7}
$$

其特征值为零及一对相反实数，非负者为 $\sqrt{c^2y^2+s^2x^2+c^2s^2(1-z)^2}$。所以逐态的半迹范数残差满足

$$
r_v^2=c^2y^2+s^2x^2+c^2s^2(1-z)^2.
\tag{278.8}
$$

设六态最坏残差为 $R$。将 $v=\pm a_i n_i$ 的两个平方残差取平均，得到

$$
R^2\ge
 a_i^2\bigl(c^2n_{iy}^2+s^2n_{ix}^2+c^2s^2n_{iz}^2\bigr)+c^2s^2.
\tag{278.9}
$$

分别除以 $a_i^2$，对三个轴求和。因 $n_i$ 是一组正交单位基，三个坐标的平方和各为一，于是

$$
R^2\sum_i\alpha_i^2
\ge1+c^2s^2\left(1+\sum_i\alpha_i^2\right).
\tag{278.10}
$$

因此 $R\ge\eta$。若达到等号，则 $cs=0$；结合 $c\ge s\ge0$，必有 $s=0$，式（278.6）的二维占用平面遂为实平面。撤销实正交变换仍保持其共轭不变性，证明所述必要条件。

为达到，选输入 Bloch 单位向量

$$
u=(\eta\alpha_1,\eta\alpha_2,\eta\alpha_3).
$$

其长度为一。用量子比特酉矩阵将方向 $u$ 旋到输出虚轴 $Y$，并用逆酉作为解码。第 $i$ 个模型方向的非实残差恰为 $a_i|u_i|=\eta$，所有输入都被精确恢复。因此二维方案达到下界。实坐标补零嵌入到三维，并把未使用正交补上的解码补为固定态制备，即得到完整 CPTP 三维方案，证明式（278.2）。

接着构造四维改进。任取轴指标 $i$，记

$$
\beta_i=\sqrt{\sum_{j\ne i}\alpha_j^2},
\qquad w=\frac{\alpha_i}{\alpha_i+\beta_i}.
\tag{278.11}
$$

选择两个输入单位方向 $u=e_i$ 及 $v$，其中 $v_i=0$、$v_j=\alpha_j/\beta_i$（$j\ne i$）。分别选量子比特酉矩阵 $U,V$，使它们成为相应输出的虚轴方向，即输出 $Y$ 坐标分别读取输入的 $u\cdot x$ 与 $v\cdot x$。定义两个量子比特输出块的编码和解码

$$
\mathcal E(X)=wUXU^*\oplus(1-w)VXV^*,
\qquad
\mathcal D(Y)=U^*Y_{11}U+V^*Y_{22}V.
\tag{278.12}
$$

编码和解码均在全矩阵代数上 CPTP，复合为恒等。在第 $i$ 轴，只有第一块产生非实残差，值为 $wa_i=1/(\alpha_i+\beta_i)$；在任意其他轴 $j$，只有第二块产生非实残差，值为 $(1-w)a_j\alpha_j/\beta_i=1/(\alpha_i+\beta_i)$。因此每个模型态都具有相同残差，得到 $R_4(a)\le\Lambda$。实坐标补零和补全解码给出 $R_5(a)\le\Lambda$。

由于全部倒数严格正，逐个 $i$ 有

$$
\sqrt{\sum_j\alpha_j^2}
<\alpha_i+\sqrt{\sum_{j\ne i}\alpha_j^2}
<\sum_j\alpha_j.
$$

取倒数并对有限个 $i$ 取最小，得到 $\Delta<\Lambda<\eta$。定理276.2给出任意输出维数的下界 $R_D\ge\Delta$，以及六维达到构造；同样的实补零使其适用于全部 $D\ge6$。这证明式（278.3）。代入等半径得到式（278.4）。本结论只给出四、五维最优值的区间，不把两个带标签酉分支的上界声明为这两个维数的最优值。证毕。

<a id="entry-906"></a>

## 追加锚（本行以下为增补区）

<a id="section-279"></a>

## 279. 任意维等距编码的支撑代价与六维必要性

**定义 279.1（占用支撑的共轭缺口）。** 沿用定义276.1的正半径六态模型，记 $\alpha_i=1/a_i$、$\Delta=(\sum_i\alpha_i)^{-1}$、$\eta=(\sum_i\alpha_i^2)^{-1/2}$。对任意有限 $D\ge2$ 的等距编码 $\mathcal E(X)=VXV^*$，令 $\Pi=VV^*$，并在计算非实残差的固定输出基底中定义

$$
\kappa(V)=2-\operatorname{Tr}(\Pi\bar\Pi).
\tag{279.1}
$$

两个投影的秩均为二，故 $\kappa(V)=\|\Pi-\bar\Pi\|_F^2/2\ge0$，且它为零恰当且仅当占用支撑对共轭不变。

**定理 279.2（纯辅助编码不能借增加维数降低最优残差）。** 对任意上述等距编码，其六态最坏非实残差 $r$ 满足

$$
r^2\ge\eta^2+\frac{1+\eta^2}{4}\kappa(V).
\tag{279.2}
$$

因此，允许任意有限输出维数的全部等距编码，其最小残差仍为 $\eta$。达到该值必有共轭不变的占用支撑；支撑不变本身不保证输入轴方向已达到最优。在可逆信道正规形中，这说明只使用秩一辅助态时，增加未占用维数不能改进二维最优值。

证明。令 $S=V^*\bar V$。这是复对称的二阶矩阵，且

$$
\|S\|_F^2=\operatorname{Tr}(\Pi\bar\Pi)=2-\kappa(V).
\tag{279.3}
$$

对输入状态 $\rho$，置 $H=V\rho V^*-\bar V\bar\rho V^{\mathsf T}$。它 Hermitian 且迹为零。其正负特征值各自的绝对值之和均为 $\|H\|_1/2$，故平方和至多为这两个和的平方之和，得到

$$
\left(\frac12\|H\|_1\right)^2
\ge\frac12\operatorname{Tr}(H^2)
=\operatorname{Tr}(\rho^2)-\operatorname{Tr}(\rho S\bar\rho S^*).
\tag{279.4}
$$

这里的最后等式只用等距性；没有把 Hilbert–Schmidt 范数当成迹范数的等值替代。

令 $Q=\|S\|_F^2$。分别将 $\rho_{i,+}$ 和 $\rho_{i,-}$ 代入式（279.4）后取平均，线性项抵消，于是

$$
r^2\ge\frac{2-Q}{4}
+\frac{a_i^2}{4}
\left[2-\operatorname{Tr}(\sigma_i S\bar\sigma_i S^*)\right].
\tag{279.5}
$$

对称性使 $S$ 属于复线性空间 $\operatorname{span}_{\mathbb C}\{I,X,Z\}$。Pauli 乘法直接给出

$$
\sum_{i=1}^3\sigma_i S\bar\sigma_i=S,
\tag{279.6}
$$

从而三个迹项之和为 $Q$。将式（279.5）除以 $a_i^2$ 再求和，得

$$
r^2\sum_i\alpha_i^2
\ge\frac{(2-Q)\sum_i\alpha_i^2+6-Q}{4}
=1+\frac{2-Q}{4}\left(1+\sum_i\alpha_i^2\right).
$$

这就是式（279.2）。第278节的二维酉编码使输出虚轴读取单位方向 $u_i=\eta\alpha_i$，逐态残差均为 $\eta$。将它作实坐标补零即可在任意 $D\ge2$ 达到；未占用补空间上的解码补为固定态制备，仍在完整输出代数上 CPTP。证毕。

**定理 279.3（全局精确恢复残差的最小维数恰为六）。** 对所有三个严格正的半径，有

$$
\Delta<R_5(a)\le R_4(a)\le\Lambda,
\qquad
R_D(a)=\Delta\quad(D\ge6),
\tag{279.7}
$$

其中 $\Lambda$ 取式（278.1）。因此，达到全维数最优精确恢复残差的最小输出维数恰为六。本节不求出四、五维的精确最优值或它们与全局下界之间的差值。

证明。先提取达到全局下界时强制出现的通道。假设某个精确恢复方案具有残差 $r=\Delta$，定义

$$
\bar{\mathcal E}(X)=\overline{\mathcal E(\bar X)},
\qquad
\mathcal C=\mathcal D\bar{\mathcal E}.
\tag{279.8}
$$

共轭 Kraus 表示保证 $\bar{\mathcal E}$ 和 $\mathcal C$ 都是复线性 CPTP。精确恢复及解码的迹距离收缩性给出

$$
d_{\rm tr}\bigl(\rho,\mathcal C(\rho^{\mathsf T})\bigr)
\le d_{\rm tr}\bigl(\mathcal E(\rho),\overline{\mathcal E(\rho)}\bigr)
\le\Delta
\tag{279.9}
$$

对全部模型态成立。

将 $\mathcal C\mathsf T$ 的 Bloch 仿射作用写成 $v\mapsto b+Mv$，其中 $\mathsf T$ 是输入转置。对 $\mathcal C$ 的归一化 Choi 态取反对称 Bell 向量期望，完全正性给出 $(1-\operatorname{Tr}M)/4\ge0$。这是与第276节相同的 Pauli Choi 约束，对未平均的通道也成立：平移和非对角项在该期望中不贡献。

式（279.9）在第 $i$ 轴的两个符号上迫使

$$
M_{ii}\ge1-2\Delta\alpha_i=:t_i.
$$

三个下界之和为一，因此 $\operatorname{Tr}M\le1$ 迫使每个对角等号。将同一对误差平方后平均，得到

$$
\|b\|^2+a_i^2\|(M-I)e_i\|^2\le4\Delta^2.
$$

其中对角项已经等于 $4\Delta^2$，所以 $b=0$，所有非对角项也为零。故 $\mathcal C$ 是唯一的 Pauli 通道，其系数为 $(t_1,-t_2,t_3)$，四个 Pauli 概率为

$$
(p_I,p_X,p_Y,p_Z)
=(\Delta\alpha_2,\Delta\alpha_3,0,\Delta\alpha_1).
\tag{279.10}
$$

三个非零概率均严格正，因而这个必要通道的 Choi 秩恰为三。此论证不要求三个 $t_i$ 都非负，也不以倒数三角条件为前提。

现在令输出维数为四。由 Nayak–Sen，*Invertible Quantum Operations and Perfect Encryption of Quantum States*，[arXiv:quant-ph/0605041v4](https://arxiv.org/pdf/quant-ph/0605041v4)，定理2.1的已有可逆信道正规形，精确恢复编码的辅助态秩至多为二。若其秩为一，则编码是等距映射，定理279.2给出 $r\ge\eta>\Delta$，与假设矛盾。

若辅助态秩为二，其占用维数为四，编码可写成

$$
\mathcal E(X)=U(X\otimes\tau)U^*,
\qquad
\tau=\operatorname{diag}(q_0,q_1),\quad q_0,q_1>0,
\quad q_0+q_1=1,
\tag{279.11}
$$

其中 $U$ 为四阶酉矩阵。对这样占满输出空间的编码，任意 CPTP 左逆都必须为

$$
\mathcal D(Y)=\operatorname{Tr}_{\rm anc}(U^*YU).
\tag{279.12}
$$

为核对这里没有额外解码自由度，令 $B_\ell$ 为解码 Kraus 算子。复合恒等通道的 Choi 秩为一，故每个 $B_\ell U(I\otimes|\beta\rangle)$ 都为恒等矩阵的标量倍数，记为 $b_{\ell\beta}I$；因 $q_\beta>0$，两个 $\beta$ 都受此约束。解码保迹迫使 $\sum_\ell\bar b_{\ell\alpha}b_{\ell\beta}=\delta_{\alpha\beta}$。对任意分块矩阵代入，便得到式（279.12），包括跨块项归零。

在式（279.8）中代入以上编码、解码，令 $W=U^*\bar U$，得到

$$
\mathcal C(X)=\operatorname{Tr}_{\rm anc}\bigl(W(X\otimes\tau)W^*\bigr).
\tag{279.13}
$$

这里 $W$ 是两个量子比特上的酉矩阵。令

$$
W_{\alpha\beta}=(I\otimes\langle\alpha|)W(I\otimes|\beta\rangle).
$$

式（279.13）的 Kraus 算子是 $\sqrt{q_\beta}W_{\alpha\beta}$。因为两个权重都正，Choi 秩等于四个块 $W_{\alpha\beta}$ 的复线性张成维数。这个维数又恰是 $W$ 跨输入量子比特与辅助量子比特的算符 Schmidt 秩：它是系数展开 $W=\sum_{\alpha,\beta}W_{\alpha\beta}\otimes|\alpha\rangle\langle\beta|$ 的矩阵秩。

这种混合环境障碍已有成熟先例：Terhal 等，*Simulating quantum operations with mixed environments*，[arXiv:quant-ph/9806095v2](https://arxiv.org/abs/quant-ph/9806095v2)，式（13）及其后的证明，给出一族两 Pauli 通道不能由混合量子比特环境实现。本节不把混合环境障碍本身作为新结论。对这里全部正半径所需的一般秩限制，直接使用 Nielsen 等，*Quantum dynamics as a physical resource*，[arXiv:quant-ph/0208077v3](https://arxiv.org/abs/quant-ph/0208077v3)，第 IV 节命题3、式（4.1）—（4.3）：两个量子比特的酉算符 Schmidt 秩只能为一、二或四，不能为三。这是既有分类结果，不在本节重新声称为新定理。于是式（279.13）的 Choi 秩不可能为三，与式（279.10）矛盾。四维方案不能达到 $r=\Delta$。

还需排除五维输出。秩一辅助态仍由定理279.2排除。秩二时，编码占用一个四维子空间 $P$，其正交补 $Q=I-P$ 为一维。令 $V:\mathbb C^2\otimes\mathbb C^2\to\mathbb C^5$ 为占用空间的等距映射。再次选辅助态本征基，使 $\tau=\operatorname{diag}(q_0,q_1)$、$q_0,q_1>0$，并写 $\mathcal E(X)=V(X\otimes\tau)V^*$。与上面的 Kraus 推导相同，任意 CPTP 左逆在完整输出上的形式必为

$$
\mathcal D(Y)=\operatorname{Tr}_{\rm anc}(V^*YV)
+\operatorname{Tr}(QY)\omega,
\tag{279.14}
$$

其中 $\omega$ 为某个量子比特状态。跨 $P,Q$ 的项归零也由保迹直接得出：若 $q$ 张成补空间，写 $v_\ell=B_\ell q$，则保迹的交叉块条件为 $\sum_\ell\bar b_{\ell\beta}v_\ell=0$；将其代入 Kraus 和，所有跨块解码项均消失。

写 $\omega=(I+c\cdot\boldsymbol\sigma)/2$，$|c|\le1$。至少存在一个轴 $i$ 满足 $|c_i|<1$。对该轴定义 Hermitian 收缩算子

$$
F=\mathcal D^*(\sigma_i)
=V(\sigma_i\otimes I_2)V^*+c_i Q.
\tag{279.15}
$$

若整个方案达到 $r=\Delta$，已经证明的必要通道式（279.10）给出

$$
H_\pm=\mathcal E(\rho_{i,\pm})-
\overline{\mathcal E(\rho_{i,\pm})},
\qquad
\mathcal D(H_\pm)=\pm\Delta\sigma_i.
$$

另一方面，残差预算给出 $\|H_\pm\|_1\le2\Delta$。于是

$$
\operatorname{Tr}[(\pm F)H_\pm]
=2\Delta\le\|H_\pm\|_1\le2\Delta.
\tag{279.16}
$$

对 Hermitian $H$ 与 $-I\le G\le I$，等号 $\operatorname{Tr}(GH)=\|H\|_1$ 迫使 $H$ 的正部分支撑于 $G$ 的 $+1$ 特征空间，负部分支撑于 $-1$ 特征空间。这由两个非负项 $\operatorname{Tr}[(I-G)H_+]$ 和 $\operatorname{Tr}[(I+G)H_-]$ 之和为零直接得到。式（279.15）在补空间上的特征值满足 $|c_i|<1$，故式（279.16）迫使 $H_\pm Q=QH_\pm=0$。

编码本身支撑于 $P$，所以

$$
Q\,\overline{\mathcal E(\rho_{i,\pm})}\,Q=0.
$$

将正负两个状态相加，得到 $Q\,\overline{\mathcal E(I)}\,Q=0$。辅助态满秩使 $\mathcal E(I)$ 在 $P$ 上正定，其共轭的支撑正是 $\bar P$。正性因而迫使 $Q\bar P=0$，即 $\bar P\subseteq P$。两个空间同为四维，故 $\bar P=P$。这个论证同时覆盖纯轴态 $a_i=1$，因为只要求两个符号的和在输入上满秩。

因此，假如五维方案达到全局下界，它的占用四维支撑反而必须对共轭不变。此时 $W=V^*\bar V$ 在四维占用坐标上为酉矩阵，且式（279.13）重新成立，补空间制备项不再贡献。再次应用算符 Schmidt 秩限制，与必要通道的 Choi 秩三矛盾。五维也不能达到 $\Delta$。

最后说明不可达到确实给出严格的最优值差，而非只有非达到的下确界。固定有限 $D$ 时，编码与解码的 CPTP 集在 Choi 表示中均紧，精确恢复条件闭；共同输出基底的选择可吸收入编码及逆向解码，也可显式纳入紧群 $U(D)$。六态最坏残差连续，可行集非空。因此每个 $R_D(a)$ 都取得最小值。对 $D=4,5$，不可能达到 $\Delta$ 就意味着 $R_D(a)>\Delta$。第278节四维上界、实坐标补零给出的维数单调性及六维达到构造共同给出式（279.7）。二维和三维已由定理278.2排除，一维不能精确恢复两个不同状态，所以最小输出维数恰为六。证毕。

这两个结论区分了输出空间的维数与可逆编码实际使用的结构：任意大的纯等距编码仍受同一个门槛约束；四维混合辅助编码可以改进该门槛，却受必要通道的秩三条件与两量子比特酉结构之间的不相容限制。五维多出的一个坐标也不能消除此限制，因为残差收缩的等号迫使它不参与共轭后的占用支撑。

<a id="entry-908"></a>

## 追加锚（本行以下为增补区）

<a id="section-280"></a>

## 280. 不等半径模型的二维实记忆精确误差

**定义 280.1（固定二维实输出的恢复代价）。** 对定义276.1的正半径六态模型，令 $B_2(a)$ 为输出维数固定为二、全部模型输出在同一个基底中为实的复线性 CPTP 编码、解码的最小恢复误差。将倒数半径按大小重新标记为

$$
0<\alpha_1\le\alpha_2\le\alpha_3,
\qquad A=\alpha_1^2+\alpha_2^2+\alpha_3^2.
\tag{280.1}
$$

这里的标记只用于表达对三个轴对称的最优值，不对不同半径的实验作平均。输出为一般二维实量子态，不限定为两个可完全区分的经典符号。

**定理 280.2（二维实记忆误差的三段闭式）。** 对三个严格正的半径，有

$$
\boxed{
B_2(a)=
\begin{cases}
\displaystyle\frac1{2(\alpha_1+\alpha_2)},
&\alpha_3\ge\alpha_1+\alpha_2,\\[6pt]
\displaystyle\sqrt{\frac3{8A}},
&\alpha_3<\alpha_1+\alpha_2\ \text{且 }A\le6\alpha_1^2,\\[6pt]
\displaystyle\frac1{\alpha_1+\sqrt{2A-3\alpha_1^2}},
&\alpha_3<\alpha_1+\alpha_2\ \text{且 }A>6\alpha_1^2.
\end{cases}}
\tag{280.2}
$$

三个分支都由完整 CPTP 编码、解码达到。在严格倒数三角区域内，这个值严格大于第276节允许任意输出维数时的 $B=\Delta$；在其余区域，两者相等。两条分支边界处公式连续。等半径时，式（280.2）回到定理277.3的 $a/(2\sqrt2)$。

证明。先给出对任意实际编码、解码均成立的下界。写恢复复合的 Bloch 作用为 $v\mapsto d+Tv$，最坏迹距离误差记为 $b$。完全实的二维模型输出及模型的层析完备性，迫使编码的 Bloch 线性部分秩至多二，因此

$$
\operatorname{rank}T\le2.
\tag{280.3}
$$

第275节的 PPT 归约说明恢复复合是量子比特纠缠破坏通道。使用 Horodecki、Shor、Ruskai，*Entanglement Breaking Channels*，[arXiv:quant-ph/0302031v2](https://arxiv.org/pdf/quant-ph/0302031v2)，定理4的既有 Holevo 表示，可写

$$
T=\sum_k w_k r_k s_k^{\mathsf T},
\qquad \sum_k w_k=1,
\quad w_k\ge0,
\quad |r_k|,|s_k|\le1.
$$

秩一矩阵的核范数为两个向量长度的乘积，故三角不等式给出

$$
\|T\|_*\le\sum_k w_k|r_k|\,|s_k|\le1.
\tag{280.4}
$$

这里 $\|T\|_*$ 是奇异值之和，不是输入或输出态的迹范数。式（280.3）、（280.4）只作必要条件使用，不假定它们单独描述任意仿射通道的完整可行集。

第 $i$ 轴两个符号的误差上界为

$$
\|d\pm a_i(T-I)e_i\|_2\le2b.
$$

将其平方平均，得到

$$
\|d\|_2^2+a_i^2\|(T-I)e_i\|_2^2\le4b^2.
\tag{280.5}
$$

除以 $a_i^2$ 后求和，得

$$
4b^2 A\ge A\|d\|_2^2+\|I-T\|_F^2\ge\|I-T\|_F^2.
\tag{280.6}
$$

设 $s_1\ge s_2\ge0$ 为 $T$ 的两个可能非零奇异值。由 $\operatorname{Tr}T\le s_1+s_2$、$s_1+s_2\le1$，有

$$
\|I-T\|_F^2
\ge1+(1-s_1)^2+(1-s_2)^2
\ge\frac32.
\tag{280.7}
$$

所以任意方案都满足 $b\ge\sqrt{3/(8A)}$。

在 $A>6\alpha_1^2$ 时还需更强的下界。由第一轴的两符号误差，

$$
T_{11}\ge1-2b\alpha_1.
\tag{280.8}
$$

记 $u=2b\alpha_1$。若 $u<1/2$，则 $s_1\ge T_{11}\ge1-u>1/2$，且 $s_2\le1-s_1$。因此

$$
\|I-T\|_F^2
\ge1+(1-s_1)^2+s_1^2
\ge2-2u+2u^2.
\tag{280.9}
$$

最后一步使用右侧关于 $s_1\ge1/2$ 单调不减。结合式（280.6），得到

$$
2b^2(A-2\alpha_1^2)+2b\alpha_1-1\ge0,
$$

其非负根为

$$
b\ge\frac1{\alpha_1+\sqrt{2A-3\alpha_1^2}}.
\tag{280.10}
$$

若 $u\ge1/2$，则 $b\ge1/(4\alpha_1)$；当 $A>6\alpha_1^2$ 时，这已严格强于式（280.10）。所以式（280.10）在该区域无条件成立。这个下界覆盖非对称 $T$、非零平移以及任意实际编码—解码因子分解，不需要把实际通道平均成某个对称形式。

接着给出达到构造。下面使用的对称正半定矩阵均具有特征值 $(\lambda,1-\lambda,0)$、$0\le\lambda\le1$；其酉本征坐标中的 Pauli 概率为 $(1/2,\lambda/2,(1-\lambda)/2,0)$，所以定义完整 CPTP 幺元通道。先处理严格三角区域内的 $A\le6\alpha_1^2$。令 $b=\sqrt{3/(8A)}$，取单位向量 $n$ 满足

$$
n_i^2=\frac{16b^2\alpha_i^2-1}{3}.
\tag{280.11}
$$

因为 $\alpha_i\ge\alpha_1$ 且 $A\le6\alpha_1^2$，右侧均非负；三个数之和为一。定义恢复通道的 Bloch 矩阵

$$
T=\frac12(I-nn^{\mathsf T}).
\tag{280.12}
$$

它具有特征值 $1/2,1/2,0$，可由酉旋转一个标准 Pauli CPTP 纠缠破坏通道得到。其全部输出位于一个过原点的 Bloch 平面。取酉 $U$ 将该平面旋到 $XZ$，令编码 $\mathcal E=\operatorname{Ad}_U\mathcal N_T$、解码 $\mathcal D=\operatorname{Ad}_{U^*}$，便得到完全实的二维输出与恢复矩阵 $T$。

由 $(I-T)e_i=(I+nn^{\mathsf T})e_i/2$，每个模型态的恢复误差平方为

$$
\frac{a_i^2}{4}\|(I-T)e_i\|_2^2
=\frac{a_i^2}{16}(1+3n_i^2)=b^2.
$$

所以这一分支达到式（280.7）的下界。

再处理严格三角区域内的 $A>6\alpha_1^2$。令 $b$ 为式（280.10）的右侧，$u=2b\alpha_1$，则 $0<u<1/2$。取单位向量 $w=(0,w_2,w_3)$，其中

$$
w_j^2=\frac{1-4b^2\alpha_j^2}{2u-u^2},
\qquad j=2,3.
\tag{280.13}
$$

这些数确实严格正。因为 $\alpha_3<\alpha_1+\alpha_2$，

$$
2A-3\alpha_1^2-(2\alpha_3-\alpha_1)^2
=2\bigl[\alpha_2^2-(\alpha_3-\alpha_1)^2\bigr]>0,
$$

故 $\alpha_1+\sqrt{2A-3\alpha_1^2}>2\alpha_3$，即 $2b\alpha_3<1$。其余指标同样满足。式（280.10）的根方程又给出

$$
4b^2A=2-2u+2u^2,
\qquad
4b^2(\alpha_2^2+\alpha_3^2)=2-2u+u^2,
$$

所以式（280.13）的两个数之和恰为一。

定义

$$
T=(1-u)e_1e_1^{\mathsf T}+uww^{\mathsf T}.
\tag{280.14}
$$

其特征值为 $1-u,u,0$，均非负且和为一，同样是幺元 CPTP 纠缠破坏通道的 Bloch 矩阵。标准 Pauli Choi 条件及酉规范形式见 Ruskai，*Qubit Entanglement Breaking Channels*，[arXiv:quant-ph/0302032v3](https://arxiv.org/pdf/quant-ph/0302032v3)，式（3）、（5）及定理4；这些是构造所复用的既有结果。将其输出平面旋成 $XZ$，再用逆酉解码，给出完整二维实输出方案。

第一轴有 $\|(I-T)e_1\|=u$，误差为 $a_1u/2=b$。对 $j=2,3$，

$$
\|(I-T)e_j\|^2
=1-(2u-u^2)w_j^2
=4b^2\alpha_j^2.
$$

这两个轴的正负态也都具有误差 $b$，达到第二个下界。

若 $\alpha_3\ge\alpha_1+\alpha_2$，第276节任意输出维数的下界为 $1/[2(\alpha_1+\alpha_2)]$；定理277.2的平面编码已经在二维达到，直接复用该构造。这完成式（280.2）。在严格三角区域，定理277.2证明任何达到全维数最优值的恢复通道都具有 Hermitian 秩四，无法通过二维实输出分解；本节最小值已达到，故它严格大于 $\Delta$。

当 $A=6\alpha_1^2$ 时，两个严格三角区域的表达式均为 $1/(4\alpha_1)$。当 $\alpha_3=\alpha_1+\alpha_2$ 时，若 $\alpha_2>\alpha_1$，有 $A>6\alpha_1^2$，且 $\sqrt{2A-3\alpha_1^2}=\alpha_1+2\alpha_2$，第三分支接到第一分支；若 $\alpha_2=\alpha_1$，两条边界同时到达，也具有相同值。由此验证边界连续性。代入三个相等倒数即得到已知等半径值。证毕。

本节确定了不等半径模型在严格实输出端点上的二维代价；允许非零非实残差时的完整不等半径二维预算曲线仍未由本节确定。

<a id="entry-910"></a>

## 追加锚（本行以下为增补区）

<a id="section-281"></a>

## 281. 二维解码的吸收与四角残差公式

**定义 281.1（中心对称量子比特模型）。** 令 $\mathcal V\subseteq\{v\in\mathbb R^3:|v|\le1\}$ 为非空有限集合，满足 $v\in\mathcal V\Rightarrow-v\in\mathcal V$，并取模型态 $\rho_v=(I+v\cdot\boldsymbol\sigma)/2$。编码和解码均为量子比特之间的复线性 CPTP 通道。恢复误差 $e$ 仍是模型上的最大迹距离，非实残差 $r$ 是编码态与其在一个共同输出基底中逐项共轭之态的最大迹距离。

**定理 281.2（中心对称模型的酉解码正规形）。** 对任意上述方案，都存在一个幺元量子比特通道 $\mathcal N$ 与一个酉矩阵 $U$，使新方案

$$
\mathcal E'=\operatorname{Ad}_U\mathcal N,
\qquad
\mathcal D'=\operatorname{Ad}_{U^*}
\tag{281.1}
$$

的恢复误差和非实残差分别不大于原方案的对应值。因此，在这些二维模型的两个上界预算问题中，允许一般仿射编码、解码所得到的可行区域，已由式（281.1）的方案完全达到。这里的结论只比较这两个任务量，不宣称保留原方案的所有其他操作性质。

证明。在计算原方案非实残差的输出基底中，写编码与解码的 Bloch 作用为

$$
\mathcal E:\ v\longmapsto c+Av,
\qquad
\mathcal D:\ w\longmapsto d+Lw.
\tag{281.2}
$$

沿用第277节的自旋反转 $\mathcal S(X)=YX^{\mathsf T}Y$。对任意量子比特 CPTP 通道 $\Phi$，双侧复合 $\mathcal S\Phi\mathcal S$ 仍为 CPTP：若 $K_j$ 是 $\Phi$ 的 Kraus 算子，相应算子可取 $Y\bar K_jY$。因此分别定义

$$
\mathcal E_0=\tfrac12(\mathcal E+\mathcal S\mathcal E\mathcal S),
\qquad
\mathcal D_0=\tfrac12(\mathcal D+\mathcal S\mathcal D\mathcal S).
\tag{281.3}
$$

这两个通道分别具有无平移的线性部分 $A,L$。其复合 $\mathcal N=\mathcal D_0\mathcal E_0$ 是幺元 CPTP，Bloch 矩阵为 $T=LA$。这一步直接计算两个实际因子的线性部分，不假定任意独立平均都会保持复合。

原恢复通道的平移为 $h=d+Lc$。中心对称性给出，对每对 $v,-v$，

$$
\max\{\|h+(T-I)v\|_2,\|h-(T-I)v\|_2\}
\ge\|(T-I)v\|_2.
\tag{281.4}
$$

所以去掉平移后的恢复误差不增。量子比特状态与其共轭的迹距离等于虚轴 $Y$ 坐标的绝对值；同一中心对称性给出

$$
r(\mathcal E)=|c_y|+\max_{v\in\mathcal V}|e_y^{\mathsf T}Av|,
\qquad
r(\mathcal E_0)=\max_{v\in\mathcal V}|e_y^{\mathsf T}Av|.
\tag{281.5}
$$

因此编码去平移也不会增加残差。

现在令 $P=\operatorname{span}_{\mathbb R}\{e_x,e_z\}$ 为原编码输出的实 Bloch 平面。$L(P)$ 的维数至多为二，可取一个单位向量 $n$ 垂直于它。于是

$$
L^{\mathsf T}n=k e_y
\tag{281.6}
$$

对某个实数 $k$ 成立。量子比特通道的迹距离收缩性给出 $\|L\|_{\rm op}\le1$，故 $|k|\le1$。不要求 $L$ 可逆；当像空间维数更低时，仍可选择这样的 $n$。

取酉矩阵 $U$，使其 Bloch 旋转 $R$ 满足 $R^{\mathsf T}e_y=n$，并使用式（281.1）的新编码、解码。其恢复复合恰为 $\mathcal N$，所以恢复误差已经由式（281.4）控制。编码后的虚坐标为

$$
e_y^{\mathsf T}RTv
=n^{\mathsf T}LAv
=k e_y^{\mathsf T}Av.
$$

从而

$$
r(\mathcal E')
=|k|\max_{v\in\mathcal V}|e_y^{\mathsf T}Av|
\le r(\mathcal E_0)\le r(\mathcal E).
\tag{281.7}
$$

所有新通道都在完整 $M_2$ 上 CPTP。式（281.1）的方案本来就是允许的一类方案，而每个原方案都被这一类中的某个方案在两个成本上弱支配，因此两者的上界预算区域相同。证毕。

**定理 281.3（六态预算的单通道归约与四角公式）。** 对定义276.1的正半径六态模型，不要求倒数半径排序。令 $\mathcal U$ 为全部幺元量子比特 CPTP 通道的实 Bloch 矩阵集合。对 $T\in\mathcal U$，定义

$$
e(T)=\frac12\max_i a_i\|(T-I)e_i\|_2,
\qquad
r_*(T)=\min_{|n|=1}\max_i a_i|n^{\mathsf T}Te_i|.
\tag{281.8}
$$

则固定二维输出的完整预算优化恰为

$$
F^{(2)}_a(R)
=\min\{e(T):T\in\mathcal U,\ r_*(T)\le R\},
\qquad R\ge0.
\tag{281.9}
$$

具体地，对非负上界预算 $E,R$，存在一般编码、解码满足 $e\le E,r\le R$，恰当且仅当存在一个 $T\in\mathcal U$ 满足 $e(T)\le E,r_*(T)\le R$。

记 $\alpha_i=1/a_i$。当 $T$ 奇异时，$r_*(T)=0$；当 $T$ 可逆时，有精确公式

$$
\boxed{
r_*(T)=
\left[
\max_{\varepsilon\in\{(1,\varepsilon_2,\varepsilon_3):\varepsilon_2,\varepsilon_3\in\{-1,1\}\}}
\left\|T^{-\mathsf T}\operatorname{diag}(\alpha_1,\alpha_2,\alpha_3)\varepsilon\right\|_2
\right]^{-1}.}
\tag{281.10}
$$

在可逆情形，存在一个最优输出虚轴，使全部六个模型态具有同一个非实残差 $r_*(T)$。所有这些最小值都达到。

证明。定理281.2给出一般方案到式（281.1）的支配归约。对该正规形，恢复矩阵为 $T$，输出基底的选择等价于指定读取虚坐标的单位方向 $n$。半 Bloch 距离公式和虚坐标公式直接给出式（281.8）。反过来，任意 $T\in\mathcal U$ 和单位 $n$ 都可按式（281.1）构造物理方案。因此上界预算的等价关系成立。

若 $T$ 奇异，则 $T^{\mathsf T}$ 有非零核，取其中的单位向量 $n$，式（281.8）中的每一项均为零。

若 $T$ 可逆，令

$$
G=\operatorname{diag}(a_1,a_2,a_3)T^{\mathsf T}.
$$

此时

$$
r_*(T)=\min_{|n|=1}\|Gn\|_\infty
=\frac1{\displaystyle\max_{\|z\|_\infty\le1}\|G^{-1}z\|_2}.
\tag{281.11}
$$

为直接核对这个标准逆算子范数恒等式，记右侧分母为 $M$。对任意单位 $n$，有 $1=\|G^{-1}Gn\|_2\le M\|Gn\|_\infty$，给出下界。另一方面，连续凸函数 $z\mapsto\|G^{-1}z\|_2$ 在立方体上的最大值可在某个顶点 $\varepsilon\in\{-1,1\}^3$ 达到；这是因为立方体中每个点都是顶点的凸组合。取

$$
n=\frac{G^{-1}\varepsilon}{\|G^{-1}\varepsilon\|_2},
\tag{281.12}
$$

则 $|n|=1$ 且 $Gn=\varepsilon/M$，从而达到式（281.11）。$\varepsilon$ 与 $-\varepsilon$ 给出相同的范数，所以八个顶点可以保留第一坐标为正的四个。再代入 $G^{-1}=T^{-\mathsf T}\operatorname{diag}(\alpha_i)$，得到式（281.10）。由 $Gn=\varepsilon/M$，每个加权轴残差都等于 $1/M=r_*(T)$，同时给出所述六态相等性。

最后核对最小值的存在。幺元 CPTP 集在 Choi 表示中紧，因而 $\mathcal U$ 紧；单位球面也紧，式（281.8）的目标连续。$r_*(T)$ 作为在同一紧球面上的连续函数的最小值，随 $T$ 连续，包括奇异矩阵处。预算约束因此闭，且 $T=0$ 是任意 $R\ge0$ 的可行点。于是式（281.9）的最小值达到。证毕。

式（281.10）把给定恢复通道的输出基底搜索化为四个显式向量范数的比较。式（281.9）仍要求在完整幺元 CPTP 集上优化；它没有把不等半径的正残差预算曲线宣布为已求出的闭式。严格实端点接回第280节，等半径完整曲线接回第277节，精确恢复端点则以 $T=I$ 给出 $r_*(I)=(\sum_i\alpha_i^2)^{-1/2}=\eta$。

本节使用的 Bloch 通道表示、酉旋转与完全正背景沿用 Ruskai，*Qubit Entanglement Breaking Channels*，[arXiv:quant-ph/0302032v3](https://arxiv.org/pdf/quant-ph/0302032v3)，式（3）、（5）及第4节；正残差的通道在这里不被假定为纠缠破坏。新增归约所用的关键关系是解码后实平面的像与输出虚轴之间的正交性。中心对称模型和二维输出是当前证明的适用条件。

<a id="entry-912"></a>

## 追加锚（本行以下为增补区）

<a id="section-282"></a>

## 282. 不等半径二维预算的非凸性与带标签改进

**定理 282.1（不等半径二维预算不能沿端点直线混合）。** 对定义276.1的正半径六态模型，假设三个半径不全相等。记

$$
A=\sum_i\alpha_i^2,\qquad
\eta=A^{-1/2},\qquad
\beta=B_2(a),
\tag{282.1}
$$

其中 $B_2$ 是定理280.2的二维严格实输出最优误差。则对每个 $0<R<\eta$，有

$$
\boxed{
F^{(2)}_a(R)>\beta\left(1-\frac R\eta\right).
}
\tag{282.2}
$$

两个端点为 $F^{(2)}_a(0)=\beta$ 和 $F^{(2)}_a(\eta)=0$。因此，固定二维输出时，全部可行非负上界预算对 $(E,R)$ 组成的集合不是凸集。

另一方面，对每个 $0\le\theta\le1$，存在一个四维输出方案，其两项最坏成本恰为

$$
e=(1-\theta)\beta,
\qquad r=\theta\eta.
\tag{282.3}
$$

当 $0<\theta<1$ 时，这个四维方案的恢复误差严格小于相同残差预算下任意二维方案的误差。此结论不判定三维能否达到式（282.3），也不把式（282.3）称为四维完整最优曲线。

证明。先给出用于比较的二维下界。根据定理281.2、281.3，可把任意二维方案换成恢复通道幺元、解码酉的正规形，而两个成本均不增加。因此只需考察幺元量子比特通道的 Bloch 矩阵 $T$ 及一个单位输出虚轴 $n$。记实际误差为 $e$、残差为 $r\le R$，以及奇异值

$$
1\ge s_1\ge s_2\ge s_3=q\ge0.
$$

由虚轴残差的逐项上界，

$$
q\le\|T^{\mathsf T}n\|_2
\le r\sqrt A\le R\sqrt A.
\tag{282.4}
$$

幺元量子比特通道的完全正约束给出 $s_1+s_2\le1+q$，这里包括行列式符号为负时更强的约束。此处直接复用第277节式（277.17）的标准通道条件。恢复误差还给出

$$
4e^2A\ge\|I-T\|_F^2
\ge\sum_{i=1}^3(1-s_i)^2.
\tag{282.5}
$$

设 $0\le R<\eta$，并记 $t=1-q>0$。先由 $s_1+s_2\le1+q$ 得

$$
\sum_i(1-s_i)^2\ge\frac32t^2.
\tag{282.6}
$$

先考察严格倒数三角区域，并将倒数标记为 $\alpha_1\le\alpha_2\le\alpha_3$。若 $A\le6\alpha_1^2$，定理280.2给出 $\beta=\sqrt{3/(8A)}$，故式（282.5）、（282.6）推出 $e\ge\beta t$。

若 $A>6\alpha_1^2$，令 $u=2e\alpha_1$。第一轴误差给出 $T_{11}\ge1-u$。如果 $u\ge t/2$，则

$$
\frac et\ge\frac1{4\alpha_1}
>\frac1{\alpha_1+\sqrt{2A-3\alpha_1^2}}
=\beta.
$$

如果 $u<t/2$，则 $s_1\ge1-u$。令 $v_1=1-s_1$，有 $0\le v_1\le u<t/2$；由完全正约束，$1-s_2\ge t-v_1$。于是

$$
\sum_i(1-s_i)^2
\ge t^2+v_1^2+(t-v_1)^2
\ge2t^2-2ut+2u^2.
\tag{282.7}
$$

结合式（282.5），除以 $t^2$ 并令 $z=e/t$，得到

$$
2z^2(A-2\alpha_1^2)+2z\alpha_1-1\ge0.
$$

它与第280节的正根相同，所以 $z\ge\beta$。这覆盖严格三角区域的第二个情形。若 $\alpha_3\ge\alpha_1+\alpha_2$，则两条轴的误差和奇异值的 Ky Fan 变分界给出

$$
2-2e(\alpha_1+\alpha_2)
\le T_{11}+T_{22}
\le s_1+s_2\le1+q.
$$

因此仍有 $e\ge\beta(1-q)$，其中本区域的 $\beta=1/[2(\alpha_1+\alpha_2)]$。由此，对全部正半径，

$$
e\ge\beta(1-q)
\ge\beta(1-R\sqrt A).
\tag{282.8}
$$

接着证明三个半径不全相等时，任何内部点都不能达到这个直线下界。固定 $0<R<\eta$，假设某个正规形方案取得等号。因为 $\beta>0$，式（282.4）、（282.8）迫使

$$
q=r\sqrt A=R\sqrt A>0,
\qquad
\|T^{\mathsf T}n\|_2=q,
\qquad
|(T^{\mathsf T}n)_i|=R\alpha_i\quad\text{对每个 }i.
\tag{282.9}
$$

其中最后一点来自三个坐标各自上界的平方和也取得等号。

在严格倒数三角区域内，式（282.5）中的 Frobenius 下界必须同时取得等号，即 $\operatorname{Tr}T=s_1+s_2+s_3$。由于 $q>0$，这迫使 $T$ 对称正定：例如对奇异值分解 $T=O_1\operatorname{diag}(s_i)O_2^{\mathsf T}$，迹等号要求正权重所对应的每个 $(O_2^{\mathsf T}O_1)_{ii}=1$，故 $O_2^{\mathsf T}O_1=I$。因此最小奇异方向也是最小本征方向，式（282.9）给出

$$
Tn=qn,
\qquad |n_i|=\frac{\alpha_i}{\sqrt A}>0.
\tag{282.10}
$$

先看 $A\le6\alpha_1^2$ 的区域。式（282.6）的等号使 $s_1=s_2=(1+q)/2$，所以

$$
T=\frac{1+q}{2}(I-nn^{\mathsf T})+qnn^{\mathsf T}.
\tag{282.11}
$$

式（282.5）左侧的等号还使全部轴的恢复误差都等于 $e$。然而由式（282.10）、（282.11），第 $i$ 轴的误差平方为

$$
e_i^2
=\frac{(1-q)^2a_i^2}{16}(1+3n_i^2)
=\frac{(1-q)^2}{16}\left(a_i^2+\frac3A\right).
\tag{282.12}
$$

因为 $q<1$，三个误差相等迫使三个 $a_i$ 相等，与假设矛盾。这也覆盖 $A=6\alpha_1^2$ 的交界。

再看 $A>6\alpha_1^2$ 的区域。等号时 $e=\beta(1-q)$，令 $u_0=2\beta\alpha_1<1/2$，则 $u=u_0(1-q)>0$。式（282.7）和第一轴估计的等号迫使

$$
s_1=1-u,\qquad s_2=q+u,\qquad s_3=q,
\qquad T_{11}=s_1.
\tag{282.13}
$$

这三个本征值严格有序，因为 $0<2u<1-q$。对称正定矩阵的 Rayleigh 商在 $e_1$ 处等于最大本征值，故 $e_1$ 是最大本征向量。最小本征向量 $n$ 必与其正交，因此 $n_1=0$，与式（282.10）中 $|n_1|=\alpha_1/\sqrt A>0$ 矛盾。

剩下 $\alpha_3\ge\alpha_1+\alpha_2$ 的区域。若直线下界取等号，则两条轴估计与 Ky Fan 界也都取等号。记

$$
t_1=1-2e\alpha_1,\qquad t_2=1-2e\alpha_2.
$$

因为 $e=(1-q)/[2(\alpha_1+\alpha_2)]$ 且 $0<q<1$，有 $t_1,t_2>q$。每条轴的误差范数已被对应对角分量用尽，所以矩阵必为

$$
T=\begin{pmatrix}
t_1&0&x\\
0&t_2&y\\
0&0&z
\end{pmatrix},
\qquad s_1+s_2=t_1+t_2.
\tag{282.14}
$$

此时 $q>0$ 使 $T$ 可逆。由 $\|T^{-1}e_3\|\ge1/|z|$，得到 $q\le|z|$；行列式恒等式又给出

$$
s_1s_2q=t_1t_2|z|,
\qquad s_1s_2\ge t_1t_2.
$$

把 $s_1+s_2=t_1+t_2$ 代入 Frobenius 范数恒等式，得到

$$
x^2+y^2
=2(t_1t_2-s_1s_2)+q^2-z^2\le0.
$$

因此 $x=y=0$、$|z|=q$。由于 $t_1,t_2>q$，式（282.9）的最小左奇异方向只能为 $n=\pm e_3$。于是 $T^{\mathsf T}n$ 的前两个坐标为零，与同式要求的 $|(T^{\mathsf T}n)_i|=R\alpha_i>0$ 矛盾。此论证包括倒数三角等号边界。

因此，对所有不全相等的正半径，任何 $0<R<\eta$ 都没有方案达到式（282.8）的直线等号。定理281.3已经证明每个固定预算的最小值达到，所以这给出严格不等式（282.2），而不只是某类方案无法取得一个可能仍相等的下确界。两个端点分别来自定理280.2与定理278.2。

令二维可行上界预算集合为

$$
\mathcal B^{(2)}_a
=\{(E,R)\in\mathbb R_{\ge0}^2:
\exists\,\mathcal E,\mathcal D\text{ 使 }e\le E,\ r\le R\}.
$$

它包含 $(\beta,0)$ 与 $(0,\eta)$。式（282.2）说明这两个点的每个严格凸组合 $((1-\theta)\beta,\theta\eta)$ 都不在该集合中，故该集合非凸。

最后构造四维达到方案。取第280节的二维实输出最优编码、解码 $(\mathcal E_0,\mathcal D_0)$，以及第278节残差为 $\eta$ 的二维精确恢复酉方案 $(\mathcal E_1,\mathcal D_1)$。在两个正交量子比特块上定义

$$
\mathcal E_\theta(X)
=(1-\theta)\mathcal E_0(X)\oplus\theta\mathcal E_1(X),
\qquad
\mathcal D_\theta(Y)
=\mathcal D_0(Y_{00})+\mathcal D_1(Y_{11}).
\tag{282.15}
$$

这是第276节已经使用的内部旗标混合构造。编码、解码都在完整矩阵代数上 CPTP，两个标签包含在四维输出中。恢复复合与恒等通道之差为 $(1-\theta)(\mathcal D_0\mathcal E_0-\operatorname{id})$，故误差恰为 $(1-\theta)\beta$。第一块全部模型输出为实，第二块的每个模型态残差为 $\eta$；迹范数对正交块相加，遂使总残差恰为 $\theta\eta$。这也覆盖两个零权重端点，因为解码仍在全部输出上保迹。式（282.3）及严格维数改进得证。证毕。

等半径时，定理277.3已给出二维完整预算直线，式（282.12）也恰好允许等号。因此，不等半径给出当前非凸障碍；等半径的完整上界预算区域则由第277节的直线公式给出，为凸集。不能仅从“存在多个编码方案”推出凸性。这里的维数差别具体体现在：四维输出能够同时携带两个方案所需的分支记录，而固定二维预算受到上述共同等号条件的约束。

<a id="entry-914"></a>

## 追加锚（本行以下为增补区）

<a id="section-283"></a>

## 283. 内部预算的最优恢复必须混合原 Pauli 轴

**定理 283.1（对角恢复的严格改进与内点排除）。** 对定义276.1的任意正半径六态模型，记 $\eta=(\sum_i\alpha_i^2)^{-1/2}$。若一个幺元量子比特通道的 Bloch 矩阵 $T$ 在模型原来的三条 Pauli 轴上为正定对角矩阵，且 $T\ne I$，则存在另一个幺元 CPTP 矩阵 $S$，使定理281.3的两个成本同时严格改善：

$$
e(S)<e(T),\qquad r_*(S)<r_*(T).
\tag{283.1}
$$

进一步，对每个 $0<R<\eta$，二维预算最优值 $F^{(2)}_a(R)$ 的任何达到方案，其恢复通道的 Bloch 线性部分都不是对角矩阵；这一结论包括允许仿射编码与解码的方案。因而，不能通过把恢复通道限制为相对于原三轴的 Pauli 协变通道来求取这个内部预算最优值。

这里不禁止在一个新的旋转坐标系中对某个对称恢复矩阵作谱分解；被排除的是相对于给定输入模型轴的对角限制。定理也不假定所有最优矩阵都对称。

证明。先证明正定对角矩阵的严格改进。写

$$
T=\operatorname{diag}(t_1,t_2,t_3),\qquad 0<t_i\le1,
\qquad e_0=e(T)>0,
\qquad r_0=r_*(T)>0.
$$

上界 $t_i\le1$ 来自迹距离收缩性，$e_0>0$ 则来自正半径与 $T\ne I$。

先设存在 $t_i\ne t_j$。令 $Q_\theta$ 为 $i,j$ 平面中的正向实旋转，并置

$$
T_\theta=Q_\theta TQ_\theta^{\mathsf T}.
\tag{283.2}
$$

正向旋转由量子比特酉共轭实现，所以 $T_\theta$ 仍是幺元 CPTP 矩阵。每条轴的恢复误差平方为

$$
\frac{a_k^2}{4}\|(I-T_\theta)e_k\|_2^2
=\frac{a_k^2}{4}
\left[Q_\theta(I-T)^2Q_\theta^{\mathsf T}\right]_{kk}.
\tag{283.3}
$$

右侧的对角元与 $\theta=0$ 时的差都是 $O(\theta^2)$。取有限个轴的最大值，再利用 $e_0>0$，得到

$$
e(T_\theta)=e_0+O(\theta^2).
\tag{283.4}
$$

这一步无需最大误差轴唯一。

令 $D_\alpha=\operatorname{diag}(\alpha_1,\alpha_2,\alpha_3)$。由定理281.3，$r_*(T_\theta)^{-2}$ 是四个二次式

$$
\varepsilon^{\mathsf T}D_\alpha
Q_\theta T^{-2}Q_\theta^{\mathsf T}
D_\alpha\varepsilon,
\qquad \varepsilon=(1,\pm1,\pm1),
\tag{283.5}
$$

的最大值。当 $\theta=0$ 时，它们全等于

$$
M_0^2=\sum_k\frac{\alpha_k^2}{t_k^2}=r_0^{-2}.
$$

旋转后的 $i,j$ 非对角元的一阶系数，除旋转方向符号外，为 $t_i^{-2}-t_j^{-2}$。在四个顶点中，$\varepsilon_i\varepsilon_j$ 可以分别取正、负，因此当 $\theta\downarrow0$ 时，

$$
r_*(T_\theta)^{-2}
=M_0^2+2\alpha_i\alpha_j|t_i^{-2}-t_j^{-2}|\theta
+O(\theta^2).
\tag{283.6}
$$

有限个余项可以统一控制，故取最大值不改变这个展开。于是存在 $c>0$，使

$$
r_*(T_\theta)=r_0-c\theta+O(\theta^2).
\tag{283.7}
$$

再处理 $T=tI$，其中 $0<t<1$。这时旋转不会改变 $T$，但对应通道的四个 Pauli 概率为 $(1+3t)/4,(1-t)/4,(1-t)/4,(1-t)/4$，全部严格为正，故它是幺元 CPTP 集的内点。取任意 $i\ne j$，令

$$
H=e_ie_j^{\mathsf T}+e_je_i^{\mathsf T},\qquad
T_\theta=tI+\theta H.
\tag{283.8}
$$

此时三个本征值为 $t+\theta,t-\theta,t$，相应主轴中的 Pauli 概率为

$$
\frac{1+3t}{4},\quad
\frac{1-t+2\theta}{4},\quad
\frac{1-t-2\theta}{4},\quad
\frac{1-t}{4}.
$$

因此，$0<\theta<\min\{t,(1-t)/2\}$ 显式保证完全正性与三个本征值的正性。每条轴的误差平方只增加 $O(\theta^2)$，故式（283.4）仍成立。另一方面，

$$
T_\theta^{-2}=t^{-2}I-2\theta t^{-3}H+O(\theta^2).
$$

四角最大式的一阶增加为 $4\alpha_i\alpha_jt^{-3}\theta$，所以式（283.7）也仍成立，只需相应取另一个正数 $c$。

现在把上述两种扰动都与恒等通道作少量混合。先注意由式（281.8）的定义，对任意矩阵 $A,B$，都有

$$
|r_*(A)-r_*(B)|
\le\max_i a_i\|(A-B)e_i\|_2
\le a_{\max}\|A-B\|_{\rm op},
\qquad a_{\max}=\max_i a_i.
\tag{283.9}
$$

这是先对每个单位方向比较两个最大值，再对方向取最小值得到的统一估计；因此在最优方向不唯一处也有效。

取固定 $k>0$，令

$$
S_\theta=(1-k\theta)T_\theta+k\theta I.
\tag{283.10}
$$

充分小的 $\theta>0$ 使它是两个幺元 CPTP 通道的凸组合。恢复差恰好按 $1-k\theta$ 缩放，所以

$$
e(S_\theta)
=(1-k\theta)e(T_\theta)
=e_0-ke_0\theta+O(\theta^2)<e_0.
\tag{283.11}
$$

两个通道的 Bloch 算子范数都不超过一，因而 $\|I-T_\theta\|_{\rm op}\le2$。由式（283.9），

$$
r_*(S_\theta)
\le r_*(T_\theta)+2a_{\max}k\theta.
$$

先选择 $0<k<c/(4a_{\max})$，再取充分小的 $\theta>0$，结合式（283.7）即得 $r_*(S_\theta)<r_0$。这证明式（283.1）。整个构造仍只使用二维输出。

接着排除内部预算的对角最优恢复。记 $\beta=B_2(a)>0$，并取第280节的严格实端点最优幺元矩阵 $T_0$。对 $p>0$ 足够小，

$$
T_p=(1-p)T_0+pI
$$

仍为幺元 CPTP，且 $e(T_p)=(1-p)\beta<\beta$。由于 $r_*(T_0)=0$ 及式（283.9）的连续性，可以同时使 $r_*(T_p)\le R$。因此每个 $R>0$ 都有

$$
F^{(2)}_a(R)<\beta.
\tag{283.12}
$$

奇异矩阵的 $r_*$ 为零，所以任何奇异幺元 CPTP 矩阵都满足 $e\ge\beta$。于是内部预算的最优矩阵必可逆。

设有一个对角幺元 CPTP 矩阵 $T=\operatorname{diag}(t_i)$ 达到内部预算最优值。先把可能的负对角元换成绝对值，记 $T_+=\operatorname{diag}(|t_i|)$。这个矩阵仍为 CPTP：若 $\det T>0$，则符号矩阵 $\operatorname{diag}(\operatorname{sgn}t_i)$ 是正向旋转，左乘它是一个酉输出变换；若 $\det T<0$，四个标准 Pauli 完全正不等式中包含 $1-\sum_i|t_i|\ge0$，故 $T_+$ 位于幺元纠缠破坏八面体内。这里直接使用第277节所引的标准 Pauli 通道条件，不引入新的通道分类。

对角情形的四角公式与轴误差给出

$$
r_*(T_+)=r_*(T),\qquad e(T_+)\le e(T).
\tag{283.13}
$$

因为 $R<\eta=r_*(I)$，不可能有 $T_+=I$。于是 $T_+$ 满足已经证明的正定对角严格改进条件。存在 $S$，使 $r_*(S)<r_*(T_+)\le R$ 且 $e(S)<e(T_+)\le e(T)$，与最优性矛盾。

最后考虑任意仿射编码、解码的达到方案。定理281.2在不改变原恢复线性部分 $T=LA$ 的条件下，得到一个幺元正规形，且两个成本不增。如果原方案最优，所得正规形也必最优，否则就已构造出更小的可行恢复误差。前面的论证已经排除对角 $T$，所以原方案的恢复线性部分也不能对角。全部最小值的存在由定理281.3保证。证毕。

本节的共同约束是：输入模型轴保持固定，而输出读取非实分量的轴允许优化。对角矩阵处，四个候选方向的二次式恰好相等；非对角扰动可以使其中一个成为更大的逆范数，从而一阶降低最优残差。恢复误差在同一扰动下却只二阶变化。这一阶次差异给出了内部预算中不能施加原轴对角限制的原因；它不等于已经求出完整预算曲线。
