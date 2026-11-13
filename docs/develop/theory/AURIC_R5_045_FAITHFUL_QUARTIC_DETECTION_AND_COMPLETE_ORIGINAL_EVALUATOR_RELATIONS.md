# 四次检测的忠实性与原首一评价族的完整关系

## 167. 原系数中的完整四次关系与有限正规形

**定义 167.1（原域、连续幂窗口与原系数源）。** 设 $F$ 为任意特征零域，$D/F$ 为实际可分域扩张，$[D:F]=2m$，$m\ge7$。任取本原元 $\theta$，固定非零体积形式 $\nu:\det_FD\to F$，置

$$
C=\langle1,\theta,\ldots,\theta^{m-1}\rangle_F,
\qquad d=m-4,\qquad V=F[T]_{\le m-2},\qquad W=\bigwedge^2V.
\tag{167.1}
$$

对实际窗口 $C'\subset D$ 及其包含帧 $E_{C'}$，使用同一个域的乘法 $M_x$ 定义

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr).
\tag{167.2}
$$

在有限 Galois 分裂域 $L/F$ 中，保持原嵌入标签及其固定次序，系数为

$$
P_{C'}(x)=\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}x_\lambda,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{167.3}
$$

$p_I$ 是实际包含帧的行子式，$\epsilon_I$ 是互补行序符号，$\alpha$ 来自 $\nu$。在全部 $p_I\ne0$ 的统一开集上，令 $S_F$ 为这个原带符号、带标签系数映射的像环。其扩底是原比值 $(c_I/c_{I_0})^{\pm1}$ 的像代数。采用 [039，定义 111.1、命题 111.2、定理 113.1](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 的同一个商 $X_D=U/T_D$、Gale 对合 $\iota$ 和有限正规化 $B_F=\mathcal O(X_D)^\iota$，其中 $T_D=(\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m$。令 $p=[P_C]$，$y$ 为其正规化点，并记

$$
S=(S_F)_p,\quad B=(B_F)_y,\quad
\mathscr T=\widehat S,\quad\mathscr B=\widehat B,
\qquad J:\mathfrak m_S/\mathfrak m_S^2\longrightarrow
\mathfrak m_B/\mathfrak m_B^2.
\tag{167.4}
$$

两个剩余域均为 $F$。这些对象始终来自 (167.2) 的原系数映射。

**定义 167.2（同一负识别与实际正纤维）。** 采用 [042，§§133--134](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) 的实际对合相容横截面。正切空间记为 $P_+$，$a=\dim P_+=m(m-1)/2$；在光滑覆盖上，正变量为 $U$，负变量为 $Y$，且

$$
\mathscr B=F[[U,Y]]^{Y\mapsto-Y}.
$$

对 $e_i=T^i\in V$，固定负余切识别

$$
e_i\wedge e_j\longleftrightarrow
z_{ij}(Y)=Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1}).
\tag{167.5}
$$

置

$$
w_2:\operatorname{Sym}^2W\to\bigwedge^4V,
\quad w_2(\xi\zeta)=\xi\wedge\zeta,
\qquad K=\ker w_2,\qquad
P_4=\operatorname{im}\bigl(\operatorname{Sym}^2K\xrightarrow{\mathrm{mult}}\operatorname{Sym}^4W\bigr).
\tag{167.6}
$$

由 [040，定理 122.1 的 (122.8)、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md)，在原 $F$ 上有

$$
\mathfrak m_B/\mathfrak m_B^2=P_+^\vee\oplus\operatorname{Sym}^2W,
\qquad M=\operatorname{im}J,
$$

$$
M\cap(0\oplus\operatorname{Sym}^2W)=0\oplus K,
\qquad\operatorname{pr}_{P_+^\vee}M=P_+^\vee.
\tag{167.7}
$$

合法实际原 $F$ 正枢轴是 $s_1,\ldots,s_a\in\mathfrak m_S$，使 $J[s_i]=(\ell_i,q_i)$ 的正分量 $\ell_i$ 构成 $P_+^\vee$ 的一组基。“正”表示对合的正特征方向。对每一组这样的 $s$，定义

$$
B_{0,s}=\mathscr B/(s)\mathscr B\simeq F[[Y]]^{Y\mapsto-Y},
\quad\pi_s:\mathscr T\longrightarrow B_{0,s},
$$

$$
\mathfrak L_s=\ker\pi_s,\qquad
A_s=A_{0,s}=\operatorname{im}\pi_s=\mathscr T/\mathfrak L_s.
\tag{167.8}
$$

只使用实际像；不假设 $\mathfrak L_s=(s)\mathscr T$。保留 (167.5) 后，实际消元是 $U=\phi_s(Y)=O(Y^2)$。在覆盖中记 $\mathfrak q=(Y)$，并置

$$
A_{r,s}=A_s\cap\mathfrak q^r,\qquad
\mathfrak n_s=A_{2,s}=\mathfrak m_{A_s},\qquad
J_{4,s}=\operatorname{im}(A_{4,s}\to\mathfrak q^4/\mathfrak q^6)
\subseteq\operatorname{Sym}^4W.
\tag{167.9}
$$

所有纤维函数均为偶函数。$\sigma_{r,s}$ 表示相应的 $r$ 次齐次项；$O(Y^6)$ 始终表示六阶及以上余项，不表示六次项已被消去。

**定义 167.3（六向量式与原首一评价）。** 对任意有限维 $F$ 空间 $V$ 中的六向量 $\mathbf v=(\alpha,\beta,\gamma,a,b,c)$，不要求独立，置

$$
\begin{array}{lll}
\beta_{01}=\alpha\wedge a,&
\beta_{02}=\alpha\wedge b+\beta\wedge a,&
\beta_{03}=\alpha\wedge c+\beta\wedge b+\gamma\wedge a,\\
\beta_{12}=\beta\wedge b,&
\beta_{13}=\beta\wedge c+\gamma\wedge b,&
\beta_{23}=\gamma\wedge c,
\end{array}
$$

$$
p_{\mathbf v}=\beta_{01}\beta_{23}-\beta_{02}\beta_{13}
+\beta_{03}\beta_{12}\in\operatorname{Sym}^2(\bigwedge^2V),
$$

$$
\Omega_{\mathbf v}=\alpha\wedge\beta\wedge\gamma\wedge a\wedge b\wedge c,
\quad\eta_{\mathbf v}=2\beta\wedge b-\alpha\wedge c-\gamma\wedge a,
\quad Q_{\mathbf v}=2\Omega_{\mathbf v}\otimes\eta_{\mathbf v}.
\tag{167.10}
$$

对实际族，令 $\mathcal M_d(F)$ 为全部首一 $d$ 次原域多项式。对 $h\in\mathcal M_d(F)$ 取六向量 $(1,T,T^2,h,Th,T^2h)$，所得式记为 $p(h),\Omega(h),\eta(h),Q(h)$。实际原函数是

$$
\mathcal E_h(C')=\frac{P_{C'}(h(\theta))}{P_{C'}(\theta^m)}\in S.
\tag{167.11}
$$

分子分母均为原系数上的 $F$ 线性评价；分母在 $C$ 处为非零幂基体积 $\nu(1\wedge\theta\wedge\cdots\wedge\theta^{2m-1})$，故是原局部环中的单位。其分裂表达式为

$$
\mathcal E_h=
\frac{\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}h(\lambda)}
{\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}\lambda^m}.
\tag{167.12}
$$

沿用 042，命题 135.2、(136.4)--(136.5)、命题 137.2 的原函数首项与检测恒等式：$\mathcal E_h$ 在完整 Grassmann 图中至少四阶消失，$[\mathcal E_h]\in\ker J$，且对每组合法实际枢轴，

$$
\pi_s(\mathcal E_h)=p(h)^2+O(Y^6),
\qquad\operatorname{in}_2(A_s)=K,\qquad P_4\subseteq J_{4,s}.
\tag{167.13}
$$

这些是上述固定版本的纸面数学输入。

**定理 167.4（全部原评价的关系判据与有限源正规形）。** 在定义 167.1--167.3 的每个 $F,D,\theta,m$ 下，可以在原 $S$ 中一次性选定 $K$ 的基 $k_1,\ldots,k_k$ 的提升 $u_1,\ldots,u_k\in\mathfrak m_S$，以及一个 $F$ 线性映射

$$
\mathcal L:P_4\longrightarrow\mathfrak m_S^2,
\qquad\sigma_{4,s}(\pi_s\mathcal L(q))=q
\quad\text{对所有合法 }s.
\tag{167.14}
$$

对任意有限个 $h_i\in\mathcal M_d(F)$、$c_i\in F$，置 $G=\sum_i c_i\mathcal E_{h_i}$、$q=\sum_i c_ip(h_i)^2$。下列条件等价：

$$
\begin{aligned}
&\sum_i c_i\Omega(h_i)\otimes\eta(h_i)=0;\\
&q\in P_4;\\
&\text{存在 }v\in\mathfrak m_S^2\text{，使 }\pi_s(G-v)\in A_{6,s}
  \text{ 对某一组合法 }s\text{ 成立};\\
&\text{存在同一个 }v\in\mathfrak m_S^2\text{，使 }\pi_s(G-v)\in A_{6,s}
  \text{ 对每组合法 }s\text{ 成立}.
\end{aligned}
\tag{167.15}
$$

条件成立时，可取同一个 $v=\mathcal L(q)$，它是固定 $u_a$ 的二次乘积的有限 $F$ 线性组合。

令

$$
r_d=d\binom d3-3\binom d4
=\frac{d(d-1)(d-2)(d+9)}{24}.
\tag{167.16}
$$

存在恰好 $r_d$ 个实际首一多项式 $h_1,\ldots,h_{r_d}$，使其原函数的四次类构成整个首一评价四次类空间的一组基。固定它们、上述 $u_a$ 及 $\mathcal L$ 后，对每个 $h=T^d+\sum_{r=0}^{d-1}b_rT^r$ 都有原 $S$ 中的等式

$$
\mathcal E_h=
\sum_{j=1}^{r_d}c_j(h)\mathcal E_{h_j}
+\sum_{a\le b}\beta_{ab}(h)u_au_b+R_h,
\qquad\pi_s(R_h)\in A_{6,s}\quad\text{对每个合法 }s.
\tag{167.17}
$$

$c_j,\beta_{ab}$ 可取为 $b_1,\ldots,b_{d-1}$ 中总次数至多四的 $F$ 多项式，所有选择均在枢轴以前固定。$c_j$ 是检测基中的唯一坐标；$\beta_{ab}$ 依赖固定的乘积截面。余项 $R_h$ 是同一个原源元素，其六阶及更高源类未由本式计算。

证明。定理 168.2 给通用核等式，定理 169.1 给跨支撑的共同线性正规形。引理 170.1 和定理 170.2 将它们提升到原 $S$，证明 (167.14)--(167.15)。定理 171.1 结合 043 的精确检测秩给基的个数；定理 171.2 给 (167.17) 及其多项式性质。各证明均保留这里的原域、实际像及全体合法枢轴量词。

## 168. 任意特征零域上的通用忠实检测

**定义 168.1（通用映射和 Pfaffian 规范）。** 本节令 $F$ 为任意特征零域，$V$ 为任意有限维 $F$ 空间，包括零维，$W=\bigwedge^2V$。$K,P_4$ 仍按 (167.6) 定义。令

$$
w_r:\operatorname{Sym}^rW\to\bigwedge^{2r}V,
\qquad w_r(\xi_1\cdots\xi_r)=\xi_1\wedge\cdots\wedge\xi_r,
$$

$$
\Psi_V:\operatorname{Sym}^4W\to\bigwedge^6V\otimes W,
\qquad
\Psi_V(\xi_1\xi_2\xi_3\xi_4)
=\sum_{i=1}^4\left(\bigwedge_{j\ne i}\xi_j\right)\otimes\xi_i.
\tag{168.1}
$$

二向量的外积交换，故这些映射良定义。定义自然交替映射

$$
j_{2r}(v_1\wedge\cdots\wedge v_{2r})
=\frac1{2^rr!}\sum_{\sigma\in\mathfrak S_{2r}}\operatorname{sgn}(\sigma)
\prod_{a=1}^r(v_{\sigma(2a-1)}\wedge v_{\sigma(2a)}).
\tag{168.2}
$$

每个无序完全匹配恰出现一次；将乘积改为外积后，每项的交替符号相消，故

$$
w_rj_{2r}=(2r-1)!!\operatorname{id}.
\tag{168.3}
$$

取基 $e_1,\ldots,e_n$，写 $x_{ij}=e_i\wedge e_j$、$Q_{2r}=j_{2r}(e_1\wedge\cdots\wedge e_{2r})$。例如 $Q_4=x_{12}x_{34}-x_{13}x_{24}+x_{14}x_{23}$；它的外乘是 $3e_{1234}$，故 $Q_4$ 本身不属于 $K$。

**定理 168.2（通用核等于实际二次乘法像）。** 对上述所有 $F,V$，均有

$$
\boxed{\ker\Psi_V=P_4=K\cdot K.}
\tag{168.4}
$$

这里 $K\cdot K$ 是两个 $K$ 元素相乘的线性张成，不是 $K$ 乘以全部 $\operatorname{Sym}^2W$ 的空间。

证明。令 $\delta(ab)=a\otimes b+b\otimes a$，并约定 $\omega\wedge(x\otimes y)=(\omega\wedge x)\otimes y$。直接对 $q=ab,r=cd$ 分组四项，再双线性延拓，得到

$$
\Psi_V(qr)=w_2(q)\wedge\delta(r)+w_2(r)\wedge\delta(q).
\tag{168.5}
$$

所以 $P_4\subseteq\ker\Psi_V$。若 $\mu_\wedge:\bigwedge^6V\otimes W\to\bigwedge^8V$ 为外乘，则逐项外乘还有

$$
\mu_\wedge\Psi_V=4w_4.
\tag{168.6}
$$

先在复数上证明反包含。使用 Michael Perlman，[*Regularity and Cohomology of Pfaffian Thickenings*，arXiv:1711.02777v2，§2，(2.1)、(2.2) 及紧接的最高权与轨道张成段落](https://arxiv.org/html/1711.02777v2#S2) 的经典表示论输入。该文的 (2.1) 将 $\operatorname{Sym}(\bigwedge^2V)$ 无重数分解为 $\mathbf S_{(z_1,z_1,z_2,z_2,\ldots)}V$，并明确归引 Weyman，*Cohomology of Vector Bundles and Syzygies*，Proposition 2.3.8；(2.2) 的主 Pfaffian 乘积给相应最高权向量，其 $\operatorname{GL}(V)$ 轨道张成该不可约分量。次数四恰给

$$
\operatorname{Sym}^4(\bigwedge^2V)=
\mathbf S_{(4,4)}V\oplus\mathbf S_{(3,3,1,1)}V
\oplus\mathbf S_{(2,2,2,2)}V
\oplus\mathbf S_{(2,2,1,1,1,1)}V\oplus\bigwedge^8V,
\tag{168.7}
$$

其最高权向量依次为

$$
x_{12}^4,\qquad x_{12}^2Q_4,\qquad Q_4^2,
\qquad x_{12}Q_6,\qquad Q_8.
\tag{168.8}
$$

超过 $n=\dim V$ 行的项删去。此分解和最高权规则只是本证明的中间输入；还须确定真正的乘法像。

当 $n\ge4$，令 $V_4=\langle e_1,e_2,e_3,e_4\rangle$。直接复用 [041，定理 127.1 证明中的四维乘积引理 (127.3)--(127.5)](https://github.com/the-omega-institute/trureturing/blob/b8e8de83c050ee1e125c8eb3bd40b7be0d05e002/docs/develop/theory/AURIC_R5_041_COMPLETE_ACTUAL_FORMAL_FIBRES_IN_DEGREES_TEN_AND_TWELVE.md)：

$$
\operatorname{Sym}^4(\bigwedge^2V_4)
=\operatorname{im}\bigl(\operatorname{Sym}^2K(V_4)\xrightarrow{\mathrm{mult}}
\operatorname{Sym}^4(\bigwedge^2V_4)\bigr).
\tag{168.9}
$$

包含 $V_4\hookrightarrow V$ 与外乘交换，将每个 $K(V_4)$ 元素送到 $K(V)$，并将两个这样的元素的实际乘积送到 $P_4(V)$。前三个最高权向量全在 (168.9) 的左侧，故全有由该引理提供的有限 $K(V_4)$ 乘积表达式，其像确实属于 $P_4(V)$。由于 $P_4(V)$ 是 $\operatorname{GL}(V)$ 稳定子空间，前三个完整不可约分量都包含于 $P_4(V)$。这一步使用乘法映射，而非仅凭表示中出现某个分量推断包含。对 $n<4$，$w_2=0$，$K=\operatorname{Sym}^2W$，四次单项式可两两分组，故直接有 $P_4=\operatorname{Sym}^4W$。

余下须检验六行、八行两个分量。由 (168.1)，在上述基中有

$$
\Psi_V(f)=\sum_{i<j}w_3\left(\frac{\partial f}{\partial x_{ij}}\right)\otimes x_{ij}.
\tag{168.10}
$$

对 $f=x_{12}Q_6$，基指标多重次数为 $(2,2,1,1,1,1)$。留下 $x_{12}$ 以外的因子后，其余六个指标仍有重复，外乘为零。又 $\partial Q_6/\partial x_{12}=Q_{3456}$，所以

$$
\begin{aligned}
\Psi_V(x_{12}Q_6)
&=w_3(Q_6+x_{12}Q_{3456})\otimes x_{12}\\
&=(15+3)e_{123456}\otimes x_{12}
=18e_{123456}\otimes x_{12}\ne0.
\end{aligned}
\tag{168.11}
$$

在八行分量的纯最高权向量上，(168.3)、(168.6) 给

$$
\mu_\wedge\Psi_V(Q_8)=4w_4(Q_8)=420e_{12345678}\ne0.
\tag{168.12}
$$

故八次外幂并不进入核。$\Psi_V$ 等变，在这两个简单分量上分别非零，因而分别单射；它们的简单像互不同构，不能产生混合核。由 (168.7) 的无重数直和，核恰为前三项之和，结合已经证明的两端包含，得到复数上的 (168.4)。维数不足时删去不存在的分量即可；$n=4,5$ 时核是全空间，$n=6,7$ 时只保留六行非核项。

最后固定任意有限维数 $n$，在 $\mathbb Q^n$ 上定义上述全部空间与映射。有限维线性映射的核、像，以及对称幂、外幂均与域扩张交换。因此 $K_F=K_{\mathbb Q}\otimes_{\mathbb Q}F$，$P_{4,F}=P_{4,\mathbb Q}\otimes_{\mathbb Q}F$。复数上核与乘法像相等，由 $\mathbb Q\to\mathbb C$ 的忠实平坦性下降到 $\mathbb Q$，再沿 $\mathbb Q\to F$ 扩张即得 (168.4)。不要求任意 $F$ 嵌入 $\mathbb C$。证毕。

## 169. 任意六向量的共同全空间 Pfaffian 正规形

**定理 169.1（共享线性重构及跨支撑全部关系）。** 对任意特征零 $F$、有限维 $V$，定义同一个全空间线性映射

$$
\mathcal B_V:\bigwedge^6V\otimes\bigwedge^2V\to\operatorname{Sym}^4(\bigwedge^2V),
\qquad\mathcal B_V(\omega\otimes\xi)=j_6(\omega)\xi.
\tag{169.1}
$$

对定义 167.3 的任意六向量，均有

$$
\Psi_V(p_{\mathbf v}^2)=Q_{\mathbf v},\qquad
p_{\mathbf v}^2\equiv\frac19j_6(\Omega_{\mathbf v})\eta_{\mathbf v}\pmod{P_4}.
\tag{169.2}
$$

因此，对任意有限多组六向量 $\mathbf v_i$、任意 $c_i\in F$，无论它们的支撑是否相同，

$$
\sum_i c_ip_{\mathbf v_i}^2\in P_4
\quad\Longleftrightarrow\quad
\sum_i c_i\Omega_{\mathbf v_i}\otimes\eta_{\mathbf v_i}=0.
\tag{169.3}
$$

若 $\mathcal C_6(V)=\operatorname{span}_F\{Q_{\mathbf v}\}$，则 $(1/18)\mathcal B_V$ 在该空间上是 $\Psi_V$ 的线性右逆。

证明。042，命题 137.2 的证明是在任意六个向量上进行的外代数恒等式，给出第一式，包括六向量相关的情形；其归一化与 (167.10)、(168.1) 完全一致。

先在形式六维空间 $E=\langle e_1,\ldots,e_6\rangle$ 中令六向量为这组基。由 (168.11) 及置换基，对任意 $\xi\in\bigwedge^2E$ 都有

$$
\Psi_E(j_6(e_{123456})\xi)=18e_{123456}\otimes\xi.
\tag{169.4}
$$

代入 $\xi=\eta$，第一式说明 $p^2-(1/9)j_6(\Omega)\eta$ 的检测值为零。定理 168.2 将它放入真正的 $P_4(E)$。对任意六向量，取线性映射 $E\to V$ 将形式基送到这些向量；外乘、$j_6$、$\Psi$ 与乘法均自然，$K(E)$ 的像在 $K(V)$ 中，所以 $P_4(E)$ 的像在 $P_4(V)$ 中。这证明第二式，且允许 $\Omega=0$。

现在在同一个 $V$ 中对任意有限族求和。第二式给

$$
\sum_i c_ip_{\mathbf v_i}^2\equiv
\frac19\mathcal B_V\left(\sum_i c_i\Omega_{\mathbf v_i}\otimes\eta_{\mathbf v_i}\right)
\pmod{P_4}.
\tag{169.5}
$$

张量和为零即得一个方向；反向对乘积空间应用 $\Psi(P_4)=0$ 与第一式即可。所有支撑始终通过同一个 $\mathcal B_V$ 连接，因而没有从逐个六维结论跳到跨支撑结论的缺口。(169.4) 经上述自然性对每个 $Q_{\mathbf v}$ 给 $\Psi_V\mathcal B_V(Q_{\mathbf v})=18Q_{\mathbf v}$，线性延拓即得右逆断言。证毕。

## 170. 一次选定的原源乘积提升与六阶消元判据

**引理 170.1（同一原源提升适用于所有合法枢轴）。** 固定 $K$ 的任意一组 $F$ 基 $k_1,\ldots,k_k$。可选 $u_a\in\mathfrak m_S$ 满足

$$
J[u_a]=(0,k_a),\qquad
\pi_s(u_a)=k_a+O(Y^4)\quad\text{对所有合法 }s.
\tag{170.1}
$$

令 $u:K\to\mathfrak m_S$ 为它们确定的 $F$ 线性提升。对有限维满射 $\mathrm{mult}:\operatorname{Sym}^2K\twoheadrightarrow P_4$，固定任一 $F$ 线性截面 $\tau$，并置

$$
\mathcal L=\mathrm{mult}_S\circ\operatorname{Sym}^2u\circ\tau:
P_4\longrightarrow\mathfrak m_S^2.
\tag{170.2}
$$

则 (167.14) 对所有合法 $s$ 同时成立。此外

$$
\sigma_{4,s}(\pi_s(\mathfrak m_S^2))=P_4,
\qquad\sigma_{4,s}(\mathfrak n_s^2)=P_4.
\tag{170.3}
$$

证明。由原域上的 (167.7)，每个 $(0,k_a)$ 都有原 $S$ 中的余切代表。042，(134.7) 的实际二次消元映射为

$$
(\ell,q)\longmapsto q-\ell L_s^{-1}q_s,
\tag{170.4}
$$

其中 $L_s$ 是枢轴的可逆正线性项。在 $(0,k_a)$ 上此式恒为 $k_a$，故同一批 $u_a$ 给出 (170.1)，不随枢轴重选。每个乘积 $\pi_s(u_au_b)$ 的四次符号为 $k_ak_b$，所以 (170.2) 给 (167.14)。

任意零常数源元素在实际纤维上至少二阶，二次符号在 $K$ 中。因此源极大理想平方的每个有限乘积和，其四次符号在 $P_4$ 中；$\mathcal L$ 给反向实现。实际像极大理想中的元素同样有二次符号在 $K$ 中，给第二个包含，而 $\pi_s\mathcal L$ 又给反向包含。这证明 (170.3)。证毕。

**定理 170.2（原源关系、实际像关系与检测零的等价）。** 定理 167.4 中 (167.15) 的四个条件等价，并且还等价于对某一组、等价地对每组合法 $s$ 有

$$
\sum_i c_i\pi_s(\mathcal E_{h_i})\in\mathfrak n_s^2+A_{6,s}.
\tag{170.5}
$$

任意 $f\in A_{4,s}$ 也满足

$$
f\in\mathfrak n_s^2+A_{6,s}
\quad\Longleftrightarrow\quad
\Psi_V(\sigma_{4,s}f)=0.
\tag{170.6}
$$

证明。由 (167.13)，$G$ 在每个实际纤维上的共同四次项都是 $q$。定理 169.1 将张量和为零与 $q\in P_4$ 等同。若 $q\in P_4$，则引理 170.1 的同一个 $v=\mathcal L(q)\in\mathfrak m_S^2$ 在每个纤维上都有四次项 $q$。因此 $\pi_s(G-v)$ 四次项相消，且无低于四次的项；偶性使余项从六阶开始。这给全体枢轴同时成立的源乘积消元，当然也给单个枢轴的存在性。

反之，若对某组 $s$ 存在任意 $v\in\mathfrak m_S^2$ 使差为六阶，则 $q=\sigma_{4,s}\pi_s(v)\in P_4$，这里用的是 (170.3) 对全部源乘积的结论，而非只对选定提升的结论。(170.5) 同样由 (170.3) 取四次项得到双向等价。最后，对任意 $f\in A_{4,s}$，定理 168.2 给 $\Psi\sigma_4f=0$ 当且仅当 $\sigma_4f\in P_4$；用 $\pi_s\mathcal L(\sigma_4f)$ 相消即得 (170.6)，反向仍取四次项。证毕。

## 171. 整个首一族的精确四次维数与有限源正规形

**定理 171.1（整个评价第四符号类的精确维数）。** 令

$$
\mathcal C_d=\operatorname{span}_F\{Q(h):h\in\mathcal M_d(F)\},
\qquad\mathcal T_d^{\mathrm{ev}}=\operatorname{span}_F\{p(h)^2:h\in\mathcal M_d(F)\},
$$

$$
\mathcal V_{d,s}=(\mathcal T_d^{\mathrm{ev}}+P_4)/P_4
\subseteq J_{4,s}/P_4.
\tag{171.1}
$$

对每组合法实际原 $F$ 正枢轴，检测器诱导同构

$$
\mathcal V_{d,s}\xrightarrow{\ \overline\Psi\ }\mathcal C_d,
\qquad[p(h)^2]\longmapsto Q(h),
\qquad\dim_F\mathcal V_{d,s}=r_d.
\tag{171.2}
$$

特别地，043，(148.4) 中的受限核交为零：

$$
\frac{\mathcal T_d^{\mathrm{ev}}\cap\ker\Psi}
{\mathcal T_d^{\mathrm{ev}}\cap P_4}=0.
\tag{171.3}
$$

证明。定理 168.2 使整个 $\operatorname{Sym}^4W/P_4$ 到检测目标单射，故在 (171.1) 的整族子空间上也单射；(167.13) 和 (169.2) 给满射到 $\mathcal C_d$。或者直接对所有有限组合应用 (169.3)，得到同一结论，且涵盖不同六维支撑之间的关系。

现在使用 [043，定理 144.2、命题 146.3](https://github.com/the-omega-institute/trureturing/blob/a04ff473c699f559cff7dab3d0b1208a53a24681/docs/develop/theory/AURIC_R5_043_EXACT_MONIC_EVALUATOR_DETECTOR_RANK_AND_ACTUAL_COTANGENT_GAIN.md) 的精确检测族秩：$\dim_F\mathcal C_d=r_d$。这仅在最后一步给出数值，核等式和关系判据不依赖该秩计算。有限维空间 $\mathcal C_d$ 已由实际首一原域值张成，故可从这些值中选出基 $Q(h_1),\ldots,Q(h_{r_d})$。相应的完整原函数正是 (167.11)，没有以参数截断取代它们。其四次类由同构给出基，得到 (171.2)--(171.3)。证毕。

**定理 171.2（参数多项式坐标与同一源余项）。** 固定定理 171.1 的实际检测基、引理 170.1 的原 $K$ 基提升及截面 $\tau$。存在唯一的检测基坐标 $c_j(h)$，满足

$$
Q(h)=\sum_{j=1}^{r_d}c_j(h)Q(h_j).
\tag{171.4}
$$

令

$$
F_h=p(h)^2-\sum_jc_j(h)p(h_j)^2\in P_4,
\qquad\tau(F_h)=\sum_{a\le b}\beta_{ab}(h)k_ak_b,
\tag{171.5}
$$

其中后式的乘积是在 $\operatorname{Sym}^2K$ 中。则 $c_j,\beta_{ab}$ 均为 $b_1,\ldots,b_{d-1}$ 的总次数至多四的原域多项式，且 (167.17) 可取

$$
R_h=\mathcal E_h-\sum_jc_j(h)\mathcal E_{h_j}-\mathcal L(F_h)\in S.
\tag{171.6}
$$

同一个 $R_h$ 对每组合法枢轴均为六阶及以上，且

$$
[\mathcal E_h]-\sum_jc_j(h)[\mathcal E_{h_j}]=[R_h]
\quad\text{在 }\mathfrak m_S/\mathfrak m_S^2\text{ 中}.
\tag{171.7}
$$

证明。取检测基的对偶坐标并线性延拓到有限维环境 $\bigwedge^6V\otimes W$，记为 $\lambda_j$。于是 $c_j(h)=\lambda_j(Q(h))$。$\Omega(h)$ 对 $h$ 的系数为三次式，$\eta(h)$ 为一次式，所以首一限制后的 $Q(h)$ 为次数至多四的向量多项式；$c_j$ 具有相同次数界。

常数参数不会出现。把 $h$ 改成 $h+t$，六向量的后三个分别增加 $t\alpha,t\beta,t\gamma$。每个 $\beta_{ij}$ 的新增项或为重复向量外积，或为两个反号外积之和，故全部为零。因此 $p(h+t)=p(h)$；$\Omega$ 因已含前三向量而不变，$\eta$ 的新增项为 $2t\beta\wedge\beta-t\alpha\wedge\gamma-t\gamma\wedge\alpha=0$，故 $Q$ 也不变。原函数本身满足 $\mathcal E_{h+t}=\mathcal E_h$：在 (167.2) 的第二块列减去第一块列的 $t$ 倍即可。这同时说明坐标只需 $b_1,\ldots,b_{d-1}$。

由 (171.4) 和定理 168.2，$F_h$ 对每个原域参数值均在 $P_4$ 中。为使 (171.5) 成为系数上的多项式恒等式，而不只是逐点选择，考虑有限维商 $\operatorname{Sym}^4W/P_4$。$F_h$ 在此商中的向量多项式在所有 $F^{d-1}$ 点为零。任一标量坐标在无限域的全部点为零，逐变量使用一元根数界即为零多项式。因此 $F_h$ 的每个向量系数都在 $P_4$ 中。固定线性截面 $\tau$ 可逐系数作用，给出同样次数至多四的 $\beta_{ab}$。

(170.2) 使 $\mathcal L(F_h)=\sum_{a\le b}\beta_{ab}(h)u_au_b$。取任意合法 $s$，(167.13)、(167.14)、(171.5) 说明 (171.6) 的四次项为零。各项原本至少四阶，且为偶函数，故 $\pi_s(R_h)\in A_{6,s}$。表达式本身在选取 $s$ 以前已是原 $S$ 中的固定元素，所以此结论同时适用于全部枢轴。$\mathcal L(F_h)\in\mathfrak m_S^2$ 给 (171.7)。唯一的是检测基坐标；截面以及乘积表达式不要求唯一。次数四只断言 $c_j,\beta_{ab}$ 和四次符号的参数性质，未把完整 $\mathcal E_h$ 或 $R_h$ 断言为四次参数多项式。证毕。

**定理 171.3（所选原函数生成的有限截断代数）。** 取 $P_4$ 的一组基 $q_1,\ldots,q_p$，令 $v_\ell=\mathcal L(q_\ell)\in\mathfrak m_S^2$。在有限环

$$
\overline B_s=B_{0,s}/(B_{0,s}\cap\mathfrak q^6)
\tag{171.8}
$$

中，令 $\mathcal A_{\mathrm{ev},s}^{<6}$ 为所有 $\pi_s(u_a)$ 和所有 $\pi_s(\mathcal E_h)$ 的像生成的 $F$ 子代数。则每个元素恰有一个表示

$$
c+\sum_a A_a\pi_s(u_a)+\sum_{\ell=1}^p B_\ell\pi_s(v_\ell)
+\sum_{j=1}^{r_d}C_j\pi_s(\mathcal E_{h_j})\pmod{\mathfrak q^6},
\tag{171.9}
$$

系数均在 $F$ 中。因此该特定截断子代数的维数为 $1+k+p+r_d$。其乘法由 $k_ak_b$ 在 $P_4$ 基中的展开决定：$u_a u_b$ 等于相应 $v_\ell$ 组合，$v_\ell$ 和 $\mathcal E_{h_j}$ 均乘杀极大理想，三个 $u$ 的乘积为零。这些带原生成元标记的代数在所有合法枢轴下具有同一个表示。

证明。$B_{0,s}$ 中只有偶次项，模六阶后只剩常数、二次与四次，故 (171.8) 有限。定理 171.2 将每个评价生成元写成有限基评价加 $u_a$ 的二次式，模六阶余项为零。任意三次 $u$ 乘积、评价与任意零常数生成元的乘积都至少六阶；二次 $u$ 乘积的四次符号属于 $P_4$，按 $q_\ell$ 展开后与相应 $v_\ell$ 组合模六阶相同。因此 (171.9) 张成所定义的子代数。

若一个这样的表示为零，先取常数项得 $c=0$，再取二次项，由 $k_a$ 独立得所有 $A_a=0$。对剩余四次项应用 $\Psi$，$P_4$ 项被消去，$Q(h_j)$ 的独立性给所有 $C_j=0$；最后 $q_\ell$ 独立给所有 $B_\ell=0$。这证明唯一性。相同的阶数论证和 (170.1) 给所述乘法规则，均只依赖固定符号及原生成元，不受 $u_a$ 未计算的四次尾项影响。该代数按定义只是选定原函数生成的截断子代数；证明未将它认作整个实际像的六阶截断。证毕。

## 172. 源与纤维的高阶余类及完整实际像义务

**定理 172.1（四次商与未计算的源余类）。** 对每组合法 $s$，令

$$
H_{6,s}=\{\xi\in\ker J:\text{存在 }g\in\mathfrak m_S,
\ [g]=\xi,\ \pi_s(g)\in A_{6,s}\}.
\tag{172.1}
$$

采用 042，定理 139.1 的满射 $\overline\lambda_s:\ker J\twoheadrightarrow J_{4,s}/P_4$。则

$$
H_{6,s}=\ker\overline\lambda_s,\qquad
\ker J/H_{6,s}\simeq J_{4,s}/P_4\simeq\Psi(J_{4,s}).
\tag{172.2}
$$

若 $\mathcal R_{\mathrm{ev}}=\operatorname{span}_F\{[\mathcal E_h]:h\in\mathcal M_d(F)\}\subseteq\ker J$，则有短正合列

$$
0\longrightarrow\mathcal R_{\mathrm{ev}}\cap H_{6,s}
\longrightarrow\mathcal R_{\mathrm{ev}}
\xrightarrow{\ [\mathcal E_h]\mapsto Q(h)\ }\mathcal C_d
\longrightarrow0.
\tag{172.3}
$$

该限制映射及其核不随合法 $s$ 改变；但核的维数及其中高阶源类未在此计算。对实际像纤维的余切空间 $Q_s=\mathfrak n_s/\mathfrak n_s^2$，置 $F^rQ_s=(A_{r,s}+\mathfrak n_s^2)/\mathfrak n_s^2$，则

$$
F^4Q_s/F^6Q_s\simeq J_{4,s}/P_4.
\tag{172.4}
$$

证明。若一个源类有六阶代表，其四次符号为零，故在 $\ker\overline\lambda_s$ 中。反向，取 $\xi\in\ker J$ 的原代表 $g$。其纤维限制至少四阶；若 $\overline\lambda_s(\xi)=0$，则四次项 $q_s$ 属于 $P_4$。用原源乘积 $\mathcal L(q_s)$ 相消，不改变源余切类，并得到六阶代表。因此第一个等式成立；满射和定理 168.2 分别给后两个同构。

每个评价的像由 (167.13) 送到 $Q(h)$，故在 $\mathcal R_{\mathrm{ev}}$ 上给出到 $\mathcal C_d$ 的满射，核正是其与 $H_{6,s}$ 的交。这也证明该限制映射良定义。对任意评价有限组合，定理 170.2 给同一个源乘积修正适用于所有枢轴，故限制映射及其核共同。即使其检测值为零，剩下的 (171.7) 仍只是 $H_{6,s}$ 中的源类，不必为零。

最后，$\mathfrak n_s^2\subseteq A_{4,s}$ 且其全部四次符号恰为 $P_4$，由 (170.3) 得

$$
F^4Q_s/F^6Q_s
=A_{4,s}/(A_{6,s}+\mathfrak n_s^2)
\simeq J_{4,s}/P_4.
$$

这是余切的一个滤过商，不是整个 $Q_s$。证毕。

**定义 172.2（完整实际像的剩余商）。** 令 $\mathcal E_s^{\mathrm{act}}=\Psi(J_{4,s})$。由定理 168.2，限制检测器给出

$$
J_{4,s}/P_4\simeq\mathcal E_s^{\mathrm{act}},
\qquad
J_{4,s}/(P_4+\mathcal T_d^{\mathrm{ev}})
\simeq\mathcal E_s^{\mathrm{act}}/\mathcal C_d.
\tag{172.5}
$$

待确定的完整四次像义务是计算 $\mathcal E_s^{\mathrm{act}}/\mathcal C_d$，以及它随合法枢轴的关系。一般原系数函数消元后的 $U^2$、$UY^2$、正向二次与四次补偿都可能参与该商；特殊评价的完整图四阶消失不能删除这些一般贡献。即使此商为零，仍须计算 (172.1)、(172.3) 以及实际纤维中的六阶及更高不可分解余类，才能确定完整源余切、完整评价余切或完整纤维余切维数。(171.2) 的精确数 $r_d$ 只属于整个首一评价族的第四符号类空间。

**定理 172.3（完整中文普通语言表述）。** 在任意特征零域中，固定一个次数至少十四的偶数次实际可分域扩张，任选本原元，并保留其从零次幂开始的连续半维窗口及原来的带符号、带嵌入标签系数。对所有首一 $m-4$ 次原域多项式作原评价，所得函数的全部四次线性关系，可以由指定外积检测张量完整读出：一组有限评价的张量和为零，当且仅当可以减去真正属于原系数局部环极大理想平方的函数，使实际纤维中的剩余项从六阶开始。

可以预先选定同一组原二次方向提升和一个乘积提升规则，使该消元同时适用于每一组合法原域正枢轴。还可以从完整原评价中固定选出 $r_d$ 个函数，使所有评价在减去二次提升的乘积并保留六阶余项后，都由这有限组函数表示；其坐标是原多项式参数的次数至多四的多项式。整个首一族的四次符号类空间恰有 $r_d$ 维。完整实际四次像、完整评价源余切与更高余类仍分别承担定义 172.2 的额外义务。

证明。可见的二次信息由完整耦合像精确确定为 $K$。通用核定理说明检测器消去的四次式恰是两个这样的二次信息相乘的线性组合，没有其他隐藏核。证明中的前三个表示分量确实来自四维乘积引理，另外两个分别有非零的六行、八行检测，因而八次外幂不能被误加进核。

每个六向量评价平方还有同一个全空间线性 Pfaffian 正规形。不同评价虽可落在不同六维支撑，它们的正规形仍由同一个线性映射产生；所以张量之间的所有跨支撑抵消，也恰好对应四次项模二次乘积的抵消。把 $K$ 的基在原局部环中提升，并给乘法映射固定一个线性截面，就将这种符号抵消变成真正的原源乘积消元。纯负提升的二次项不受正枢轴补偿影响，因此所有枢轴共享这些原函数和同一修正规则。

043 已给整个实际首一族的精确检测秩。忠实性把该秩直接转为整个评价第四符号类的精确维数，而不只给下界。从实际检测值中选基后，每个检测值有唯一线性坐标；检测张量是参数四次式，所以这些坐标为次数至多四的多项式。余下的四次差在 $P_4$ 中，固定乘积截面给同样次数界的原源修正。四次项消去后因偶性留下六阶及以上项。

这个剩余项仍是实际函数，可能在源余切或纤维余切中给非零类。精确的有限维结论只读取四次滤过商；一般原系数还可能给评价族以外的四次方向。因此本定理同时给出了完整四次关系判据、有限原源正规形，以及继续计算完整实际像和高阶结构所需的确切剩余对象。证毕。

## 173. 数学来源及对应范围

**约定 173.1（经典中间输入与原族推导）。** 定理 168.2 中的无重数分解、主 Pfaffian 最高权向量及其轨道张成，使用 Perlman，*Regularity and Cohomology of Pfaffian Thickenings*，arXiv:1711.02777v2，§2，(2.1)--(2.2) 及紧接段落，为 `literature-attested` 的经典输入。该文关于 Pfaffian 理想幂的 (2.4)--(2.7) 未用来代替本题不同二次空间 $K$ 的实际乘法像证明。这里不需要目标空间的 Pieri 分解或表示目录。

039 的原系数、有限正规化与实际横截面，040 的完整耦合像，041 的抽象四维乘积引理，以及 042 的全 $m\ge7$ 实际二次桥、原单位分母评价、完整图四阶消失、任意六向量检测恒等式和源余切满射，均按正文所列固定版本使用。041 关于完整实际纤维的结论只覆盖 $m=5,6$，不作为这里 $m\ge7$ 的环等式前提。043 在固定版本给出的精确检测秩只用于 (171.2) 的数值及有限基个数，未被重述为完整实际像维数。

本卷的 `repo-derived` 结论是通用核与实际乘法像的相等、共享六向量正规形、全体跨支撑关系的双向判据、同一原源乘积提升对全部合法枢轴的实现，以及有限实际评价正规形和对应四次滤过商。经典分解、既有检测秩及既有余切下界各保留原有出处；这些对应不构成文献范围之外的原创性或完整局部芽分类断言。

## 追加锚（本行以下为增补区）
