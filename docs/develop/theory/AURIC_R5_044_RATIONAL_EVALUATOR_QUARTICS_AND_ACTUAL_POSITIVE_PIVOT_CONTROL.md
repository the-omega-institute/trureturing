# 原域有理评估的四次方向与实际正枢轴控制

## 151. 同一个十四次域、原系数与实际像

**约定 151.1（范围与证明地位）。** 全文固定特征零域 $F$、次数十四的实际可分域扩张 $D/F$、任一本原元 $\theta$、其首一最小多项式 $f(T)$，以及非零体积形式 $\nu:\det_FD\to F$。置

$$
D=F[\theta],\qquad C=\langle1,\theta,\ldots,\theta^6\rangle_F,
\qquad V=F[T]_{\le5},\qquad W=\bigwedge^2V.
\tag{151.1}
$$

本卷是参考输入，给出普通数学的 PAPER 定义、定理和证明；未经 Lean kernel 验证，不承担冻结真值。关于原商和完整耦合余切像，使用 [039，§§111、113、115--117](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 与 [040，定理 122.1、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) 的 PAPER 结论。全部具体乘法块、核、单位和枢轴变化在下文说明。

**定义 151.2（原带符号系数局部环）。** 对实际七维窗口 $C'\subset D$ 的包含帧 $E_{C'}$，令

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr),\qquad x\in D,
\tag{151.2}
$$

其中 $M_x$ 是这个 $D$ 的乘法。换帧只乘一个公共平方，换体积只乘公共标量。取有限 Galois 分裂域 $L/F$，保留十四个原嵌入标签；在固定标签序下，原系数为

$$
P_{C'}(x)=\sum_{|I|=7}c_I(C')x_I,
\qquad c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{151.3}
$$

这里 $p_I$ 是实际帧子式，$\epsilon_I$ 为互补行序符号，$\alpha$ 为体积因子。令 $S$ 为此射影系数像在 $[P_C]$ 处的原 $F$ 局部环，$\mathscr T=\widehat S$。等价地，在任一原 $F$ 系数线性泛函非零的图上取实际系数像，再局部化。连续幂窗口的全部最大子式是非零 Vandermonde 行列式，故属于 039 的统一开集。

原乘法环面为 $T_D=(\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m$；039 给出实际光滑商 $X_D$，其 Gale 不变量环是原系数像的有限双有理正规化。在固定点取正规化完成局部环 $\mathscr B$。全文在这个实际环内消元，不把它的任意子代数认作原系数环。

**定义 151.3（原评估函数）。** 对实际 $x\in D$，置

$$
\mathcal E(x)(C')=\frac{P_{C'}(x)}{P_{C'}(\theta^7)}.
\tag{151.4}
$$

分母在 $C$ 是非零幂基体积。分子、分母是原系数空间上的 $F$ 线性泛函，所以 $\mathcal E(x)\in S$。特别地，若 $p,q\in F[T]$、$q\ne0$、$\deg q<14$，则 $q(\theta)\ne0$；由 Bézout 恒等式 $aq+bf=1$，$p(\theta)/q(\theta)=p(\theta)a(\theta)$ 有原 $F$ 坐标，仍给同一个 $S$ 中的函数。所有出现的 $f(a)$，$a\in F$，均非零。又由后七列加前七列的倍数，

$$
\mathcal E(x+b)=\mathcal E(x)\qquad(b\in F).
\tag{151.5}
$$

对 $t\in D^\times$，乘法交换性给 $P_{tC'}(x)=\operatorname{Norm}_{D/F}(t)P_{C'}(x)$，故比值下降到实际乘法商。这里没有使用分裂域中的自由矩阵替换原乘法。

## 152. 残数双曲帧、完整图与负商坐标

**引理 152.1（原域双曲化与实际核）。** 定义

$$
\ell(x)=\operatorname{Tr}_{D/F}\frac{x}{f'(\theta)},\qquad
\beta(x,y)=\ell(xy).
\tag{152.1}
$$

则 $\beta$ 非退化，$C^{\perp_\beta}=C$，并有

$$
\ell(\theta^j)=0\ (0\le j\le12),\qquad \ell(\theta^{13})=1.
\tag{152.2}
$$

取 $c_i=\theta^i$、$r_j=\theta^{13-j}$，$0\le i,j\le6$，置

$$
Q_{ij}=\ell(c_ir_j),\quad
\widetilde d_j=\sum_k r_k(Q^{-1})_{kj},\quad
G_{ij}=\ell(\widetilde d_i\widetilde d_j),\quad
d_j=\widetilde d_j-\frac12\sum_kc_kG_{kj}.
\tag{152.3}
$$

则 $(c_i,d_j)$ 是原 $F$ 双曲帧。实际乘法块严格为

$$
M_x=\begin{pmatrix}B_x^{\mathsf T}&D_x\\H_x&B_x\end{pmatrix},\qquad
(H_x)_{ij}=\ell(xc_ic_j),\quad
(B_x)_{ij}=\ell(xc_id_j),\quad
(D_x)_{ij}=\ell(xd_id_j),
\tag{152.4}
$$

其中 $H_x,D_x$ 对称，且

$$
\ker H_x=\{u\in C:xu\in C\}.
\tag{152.5}
$$

证明。在分裂域作 Lagrange 插值，比较次数至多十三的多项式的最高次系数，即得 (152.2)，该恒等式下降到 $F$。也可直接验证非退化：若 $a\in D$ 的次数为 $j\le13$、最高系数为 $a_j\ne0$，则 $\ell(a\theta^{13-j})=a_j$。于是 $C$ 是七维各向同性空间，等于自己的正交补。矩阵 $Q$ 下三角且对角线全一；(152.3) 逐项配对给 $\beta(c_i,d_j)=\delta_{ij}$ 和 $\beta(d_i,d_j)=0$。乘法自伴随给 (152.4)。最后，$H_xu=0$ 等价于 $\beta(xu,C)=0$，再用 $C^\perp=C$ 即得 (152.5)。

**引理 152.2（完整图公式与归一化单位）。** 令 $C_Z=\operatorname{col}\binom I Z$，则

$$
L_x(Z)=H_x+B_xZ-ZB_x^{\mathsf T}-ZD_xZ,\qquad
\mathcal E(x)(C_Z)=\frac{\det L_x(Z)}{\det L_{\theta^7}(Z)},
\tag{152.6}
$$

$$
\det H_{\theta^7}=(-1)^{21}=-1.
\tag{152.7}
$$

写 $Z=U+Y$，其中 $U^{\mathsf T}=-U$、$Y^{\mathsf T}=Y$，则 $L_x(U-Y)=L_x(U+Y)^{\mathsf T}$。所以原评估关于 $Y$ 为偶函数。

证明。在实际双曲帧中，帧与乘法帧的并置矩阵为

$$
\begin{pmatrix}I&B_x^{\mathsf T}+D_xZ\\Z&H_x+B_xZ\end{pmatrix}.
$$

从右块列减左块列乘 $B_x^{\mathsf T}+D_xZ$，即得 (152.6)，没有交换行列。共同帧体积在比值中抵消。$H_{\theta^7}$ 在 $i+j<6$ 时为零，在 $i+j=6$ 时为一；反转七列后是三角矩阵，故行列式为 $-1$。这说的是消去公共帧因子后的矩阵分母常数，未将任意原体积下的 $P_C(\theta^7)$ 数值误写成 $-1$。转置 (152.6) 并代入 $U^{\mathsf T}=-U$、$Y^{\mathsf T}=Y$，给最后的恒等式。

**定义 152.3（固定实际横截面）。** 乘法环面的对称切像是全部十三维 Hankel 空间 $\mathcal O$：其条目为 $\ell(t\theta^{i+j})$，$t\in D$。因为 $1,\theta,\ldots,\theta^{12}$ 独立且 $\beta$ 非退化，这个矩映射满射到十三个反对角线参数，核为 $F\cdot1$。固定任一原 $F$ 线性补空间

$$
\operatorname{SymMat}_7(F)=\mathcal O\oplus N,
\qquad Y\in N,
\tag{152.8}
$$

保留全部二十一维交错参数 $U$。由 039 的实际横截面形式逆，$Z=U+Y$ 计算实际商的完成局部环；Gale 对合为 $(U,Y)\mapsto(U,-Y)$，故

$$
\mathscr B=F[[U,Y]]^{Y\mapsto-Y}.
\tag{152.9}
$$

置 $e_i=T^i\in V$，严格采用

$$
z_{ij}(Y)=Y(T^{i+1},T^j)-Y(T^i,T^{j+1}),\qquad
z_{ij}\longleftrightarrow e_i\wedge e_j,
\quad0\le i<j\le5.
\tag{152.10}
$$

并约定 $z_{ji}=-z_{ij}$、$z_{ii}=0$。这些差分同时为零恰好意味着 Hankel 型，故在 $N$ 上给十五个独立线性坐标。作为对称二元多项式，对应的乘法核张量是

$$
T^{i+1}\odot T^j-T^i\odot T^{j+1}
=\frac{(s-t)(s^it^j-s^jt^i)}2.
\tag{152.11}
$$

这里 $a\odot b$ 用平均对称化表示为 $(a(s)b(t)+b(s)a(t))/2$。因此 $N^\vee=W$；此约定固定下文所有数字因子。涉及 $C$ 的多项式向量均在 $\theta$ 处评价，简记 $H_h=H_{h(\theta)}$、$B_h=B_{h(\theta)}$、$D_h=D_{h(\theta)}$。不同枢轴始终在同一横截面、同一负坐标中比较。

## 153. 合法正枢轴与全部可达的二阶差

**定义 153.1（实际像纤维）。** 记

$$
Q_2=\operatorname{Sym}^2W,\qquad
\mu_2:Q_2\longrightarrow\bigwedge^4V,\quad \mu_2(ab)=a\wedge b,
\qquad K=\ker\mu_2.
\tag{153.1}
$$

040 的原域耦合像为

$$
M=\operatorname{im}\left(\mathfrak m_S/\mathfrak m_S^2
\longrightarrow\mathfrak m_{\mathscr B}/\mathfrak m_{\mathscr B}^2\right)
\subset P^\vee\oplus Q_2,
\qquad M\cap Q_2=K,\qquad \operatorname{pr}_{P^\vee}M=P^\vee,
\tag{153.2}
$$

其中 $\dim P=21$。把 (153.2) 中的余切映射记为 $J$。一组合法实际正枢轴是 $p_{ij}\in\mathfrak m_S$，$0\le i<j\le6$，其正向一次项构成基。“正”表示对合正特征方向，不要求 $F$ 有序。作可逆 $F$ 线性归一化后，令一次项严格为 $u_{ij}=U(T^i,T^j)$。写

$$
q_{ij}(Y)=[p_{ij}(0,Y)]_2.
$$

实际隐函数方程唯一解为

$$
p(U,Y)=0\quad\Longleftrightarrow\quad
U=U_p(Y)=U_{2,p}(Y)+O(Y^4),\qquad
(U_{2,p})_{ij}=-q_{ij}.
\tag{153.3}
$$

偶性来自隐函数的唯一性。未归一化的一次矩阵为 $L$ 时是 $U_2=-L^{-1}q$。通过 $(U,Y)\mapsto(p,Y)$ 的等变形式坐标变换，正规化一侧的实际纤维为

$$
B_{0,p}=\mathscr B/(p)\mathscr B\simeq F[[Y]]^{Y\mapsto-Y}.
$$

令

$$
\varphi_p:\mathscr T\longrightarrow B_{0,p},\qquad
A_p=\operatorname{im}\varphi_p,
\qquad
\mathfrak L_p=\ker\varphi_p.
\tag{153.4}
$$

只自动有 $(p)\mathscr T\subseteq\mathfrak L_p$；不预设等号。记 $[a]_{r,p}$ 为实际代入后的 $r$ 次齐次项，$\mathfrak q=(Y)\subset F[[Y]]$，并置

$$
J_4(A_p)=\operatorname{im}(A_p\cap\mathfrak q^4\longrightarrow
\mathfrak q^4/\mathfrak q^6),\qquad
P_4=K K=\operatorname{span}_F\{kk':k,k'\in K\}.
\tag{153.5}
$$

这里 $KK$ 是两个可见二次空间的乘积子空间，不是 $K\operatorname{Sym}^2W$。

**引理 153.2（实际二次桥）。** 对每组已经固定的合法枢轴，实际二次像恰为 $K$，且 $P_4\subset J_4(A_p)$。

证明。若源的正规化余切类为 $(\ell,q)\in M$，则代入 (153.3) 的二次项是 $q-\ell(q_{ij})$。枢轴类 $(u_{ij},q_{ij})$ 张成 $M$ 中正投影同构的补空间，由 (153.2)，其补恰为 $0\oplus K$。约化映射在枢轴类上为零，在 $K$ 上为恒等，故实际二次像正是 $K$。正规化极大理想限制后从二次起，其平方从四次起，所以没有遗漏二次项。将 $K$ 中任意两个元素的实际源提升相乘，四次符号为其乘积，得到 $P_4$ 的包含。此证明也见 [042，引理 134.2](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md)；此处列出完整桥以固定本卷坐标。

**定理 153.3（归一化合法修正差恰为 $K^{21}$）。** 固定一次正坐标 $u_{ij}$ 及一组起始枢轴 $p$。当 $p'$ 遍历具有同一次正坐标的全部实际原 $F$ 合法枢轴时，

$$
\{(q'_{ij}-q_{ij})_{i<j}\}=K^{21},\qquad
\{U_{2,p'}-U_{2,p}\}=K^{21}.
\tag{153.6}
$$

第二式逐条目解释为交错矩阵；其具体符号是 $U_{2,p'}-U_{2,p}=-(q'-q)$。任意指定的二十一条 $K$ 值可同时由原 $S$ 函数实现。

证明。$p'_{ij}-p_{ij}$ 没有一次正项；由 (153.2)，其纯 $Y$ 二次项必在 $K$。反向的实际提升可以一次性固定如下。取原 $F$ 多项式坐标中 $P_{C'}(x)/P_{C'}(\theta^7)$ 的有限系数函数 $s_\alpha$；这些函数在指定图上生成原系数代数，其中心化类生成源余切，故其成对类 $(\ell_\alpha,q_\alpha)$ 张成 $M$。在这些有限列的 $F$ 线性组合中，先取满足 $\sum t_\alpha\ell_\alpha=0$ 的全部组合。由 (153.2)，其二次像张成 $K$。选出其中 $105$ 个函数 $r_\beta\in S$，使

$$
r_\beta(C)=0,\qquad J[r_\beta]=(0,k_\beta),\qquad
(k_\beta)\text{ 是 }K\text{ 的一组基}.
\tag{153.7}
$$

这里 $\dim K=\dim Q_2-\dim\bigwedge^4V=120-15=105$，因为外乘满射。每个 $r_\beta$ 都是中心化原系数的有限 $F$ 线性组合，普通完整图一次项为零。选取二次单项式坐标的 $105$ 行投影 $\pi$，使列矩阵 $C_K=(\pi k_\beta)_\beta$ 可逆。于是

$$
\mathcal L(k)=\sum_\beta\bigl(C_K^{-1}\pi k\bigr)_\beta r_\beta
\quad(k\in K)
\tag{153.8}
$$

是实际原 $F$ 线性提升，$J[\mathcal L(k)]=(0,k)$。这个公式只反演一个已选非零的 $F$ 行列式；不存在单个分裂矩形下降的额外假设。给任意 $(\kappa_{ij})\in K^{21}$，同时置 $p'_{ij}=p_{ij}+\mathcal L(\kappa_{ij})$。一次矩阵不变，每条纯二次差为 $\kappa_{ij}$，所以仍合法，并由 (153.3) 得全部结论。各条源函数同时存在，未把分别可达的数值假作共同实现。

## 154. 只需的四次检测恒等式

**定义 154.1（检测器）。** 令 $\Omega=e_0\wedge\cdots\wedge e_5$，定义

$$
\begin{aligned}
\Psi:\operatorname{Sym}^4W&\longrightarrow\det(V)\otimes W,\\
\Psi(abcd)&=(a\wedge b\wedge c)\otimes d
 +(a\wedge b\wedge d)\otimes c\\
&\quad +(a\wedge c\wedge d)\otimes b
 +(b\wedge c\wedge d)\otimes a.
\end{aligned}
\tag{154.1}
$$

二向量外乘交换，故右端对称、良定义。令 $\delta(ab)=a\otimes b+b\otimes a$，其中第一因子也属于 $W$。在 $q=ab,r=cd$ 上展开四项并线性延拓，得到

$$
\Psi(qr)=\mu_2(q)\wedge\delta(r)+\mu_2(r)\wedge\delta(q),
\qquad q,r\in Q_2.
\tag{154.2}
$$

外乘作用于 $\delta$ 的第一因子。因此

$$
\Psi(P_4)=0.
\tag{154.3}
$$

这个消去式只提供检测下界。本文不需要关于整个 $\ker\Psi$ 的分类。

## 155. 正三次的精确四次符号

**命题 155.1（原多项式评估）。** 对 $c,d\in F$，令

$$
h=T^3+cT^2+dT,\qquad \mathcal P_{c,d}=\mathcal E(h(\theta)).
$$

核为 $R_4=F[T]_{\le3}$。在其基 $1,T,T^2,T^3$ 上，核的一次负向斜形式 $\rho_h(u,v)=Y(hu,v)-Y(u,hv)$ 的六个条目为

$$
\begin{aligned}
r_{01}&=z_{03}+cz_{02}+dz_{01},\\
r_{02}&=z_{04}+z_{13}+c(z_{03}+z_{12})+dz_{02},\\
r_{03}&=z_{05}+z_{14}+z_{23}+c(z_{04}+z_{13})+dz_{03},\\
r_{12}&=z_{14}+cz_{13}+dz_{12},\\
r_{13}&=z_{15}+z_{24}+c(z_{14}+z_{23})+dz_{13},\\
r_{23}&=z_{25}+cz_{24}+dz_{23}.
\end{aligned}
\tag{155.1}
$$

置

$$
b_{c,d}=r_{01}r_{23}-r_{02}r_{13}+r_{03}r_{12},\qquad
Q_{c,d}=b_{c,d}^2.
\tag{155.2}
$$

则 $\mathcal P_{c,d}$ 在完整图 $(U,Y)$ 中至少四阶消失，且对每组已经固定的合法正枢轴，

$$
[\mathcal P_{c,d}]_{4,p}=Q_{c,d}.
\tag{155.3}
$$

证明。若 $hu=v\in C$，则相关次数不超过九，小于十四；故这是多项式恒等式，等价于 $\deg u\le3$。由 (152.5)，核正是 $R_4$。补空间 $\langle T^4,T^5,T^6\rangle$ 上的 $H_h$ 在指标和小于十时为零、等于十时为一，故补块行列式为 $-1$。按核和补分块作 Schur 补，核块常数为零，一次部分来自 $B_hZ-ZB_h^{\mathsf T}$；交叉校正从二阶起。因此分子在完整 $Z$ 中至少四阶，四次项是补块行列式乘核的一次块行列式。

限制到 $U=U_{2,p}+O(Y^4)$ 后，完整图四阶单项式中若含一个 $U$，代入后至少五阶；高阶单项式亦不能贡献四次。这是保留完整图后按阶数得到的独立性，不是将真实纤维设成 $U=0$。核上只需 $\rho_h$。恒等式

$$
Y(T^{i+r},T^j)-Y(T^i,T^{j+r})
=\sum_{k=0}^{r-1}z_{i+k,j+r-1-k}
\tag{155.4}
$$

按相邻项相消证明 (155.1)。四阶斜矩阵行列式为三项 Pfaffian 的平方；补块 $-1$ 除以分母常数 $-1$，得到 (155.3)。偶性使余项从六次开始。反三角论证没有将另一侧的实际残数条目设为零。

**引理 155.2（检测值的纸面展开）。** 定义

$$
v_0=2z_{14}-z_{05}-z_{23},\qquad
v_1=2z_{13}-z_{04},\qquad
v_2=3z_{12}-z_{03}.
\tag{155.5}
$$

则

$$
\Psi(Q_{c,d})=2\Omega\otimes(v_0+cv_1+dv_2).
\tag{155.6}
$$

证明。记 $e_{ijkl}=e_i\wedge e_j\wedge e_k\wedge e_l$。将 (155.1) 的三项乘积改为外积，重复指标项消失，得到

$$
\begin{aligned}
\mu_2(b_{c,d})={}&2e_{0145}-e_{0235}+2e_{1234}
+c(2e_{0135}-e_{0234})+3d e_{0125}\\
&+2(c^2-d)e_{0134}+3cd e_{0124}+3d^2e_{0123}.
\end{aligned}
\tag{155.7}
$$

以 $\mu_2(b_{c,d})\wedge w=\lambda(w)\Omega$ 定义 $\lambda$。按互补指标求系数给

$$
\lambda(r_{01})=\lambda(r_{02})=\lambda(r_{13})=\lambda(r_{23})=0,
\qquad \lambda(r_{03})=3,\quad\lambda(r_{12})=-1.
\tag{155.8}
$$

例如 $\lambda(z_{05})=2$、$\lambda(z_{14})=-1$、$\lambda(z_{23})=2$；还分别有 $\lambda(z_{15})=c$、$\lambda(z_{24})=-2c$、$\lambda(z_{25})=2(c^2-d)$。故 $r_{13}$ 中 $c-2c+c=0$，$r_{23}$ 中 $2(c^2-d)-2c^2+2d=0$，其余各式同由 (155.7) 的互补项给出。对 $b_{c,d}^2$ 使用 (154.2)，即得

$$
\Psi(b_{c,d}^2)=2\Omega\otimes(3r_{12}-r_{03}),
$$

而 $3r_{12}-r_{03}=v_0+cv_1+dv_2$。

## 156. 逆三次的原域成员、单位与反转归一化

**命题 156.1（原逆三次评估）。** 对任意 $a,c,d\in F$，令 $t=T-a$，定义

$$
x_{a;c,d}=\frac{1+ct(\theta)+dt(\theta)^2}{t(\theta)^3},\qquad
\mathcal I_{a;c,d}=-f(a)^3\mathcal E(x_{a;c,d})\in S.
\tag{156.1}
$$

其实际核及一个补块为

$$
\ker H_{x_{a;c,d}}=t^3F[t]_{\le3},\qquad
\det\left(H_{x_{a;c,d}}|_{\langle1,t,t^2\rangle}\right)=f(a)^{-3}.
\tag{156.2}
$$

令 $\jmath(z_{ij})=z_{5-j,5-i}$，令 $g_a(e_i)=(T-a)^i$，并将其作用延拓到外幂与对称幂。则对每个已经固定的实际枢轴，

$$
[\mathcal I_{a;c,d}]_{4,p}=g_a\jmath(Q_{c,d}).
\tag{156.3}
$$

这些函数在完整图中至少四阶消失。

证明。$t(\theta)$ 及 $f(a)$ 的非零性已由不可约性保证。若 $xu=v\in C$，则

$$
(1+ct+dt^2)u=t^3v
$$

两边次数都小于十四，故是原多项式恒等式。分子与 $t^3$ 互素，所以 $u=t^3r$；次数约束恰为 $\deg r\le3$。反向这样的 $r$ 给 $xu=(1+ct+dt^2)r\in C$，证明核等式。

写 $f(T)-f(a)=(T-a)b_a(T)$，其中 $b_a$ 首一十三次。在 $D$ 中

$$
(\theta-a)^{-1}=-b_a(\theta)/f(a),\qquad
\ell((\theta-a)^{-1})=-f(a)^{-1}.
\tag{156.4}
$$

在补基 $1,t,t^2$ 上，$H_x$ 的条目为 $\ell(t^{i+j-3}+ct^{i+j-2}+dt^{i+j-1})$。当 $i+j>2$ 时，由 (152.2) 全为零；当 $i+j=2$ 时为 $-f(a)^{-1}$。三阶反三角行列式因此为 $f(a)^{-3}$，未知的另一侧条目不参与行列式。总基

$$
(t^3,t^4,t^5,t^6,1,t,t^2)
$$

对原幂基的行列式为一：平移幂基为幺三角，两个连续块的交换产生 $(-1)^{4\cdot3}=1$。核四维又给完整图四阶消失。补块行列式除以分母 $-1$，恰由 $-f(a)^3$ 归一化。

为核对反转，在 $a=0$ 时反转四个核基，行列式为 $(-1)^6=1$。核上条目原为

$$
Y((1+cT+dT^2)T^i,T^{3+j})
-Y(T^{3+i},(1+cT+dT^2)T^j).
\tag{156.5}
$$

令 $Y^{\mathrm{rev}}(T^i,T^j)=Y(T^{6-i},T^{6-j})$，则反转核基后的 (156.5) 恰为 $\rho_h(Y^{\mathrm{rev}})$；且 (152.10) 给 $z_{ij}(Y^{\mathrm{rev}})=\jmath(z_{ij})(Y)$。故归一化首项为 $\jmath(Q_{c,d})$。一般 $a$ 使用同一个 $C$ 的 $t$ 幂基，(152.2) 对 $t^j$ 仍成立，差分坐标相应变为 $g_a z$，得 (156.3)。整个比较只在负余切商进行；即使所选 $N$ 不被平移保持，也因 Hankel 差被消去而不影响公式。完整图的阶数论证保证没有 $U_{2,p}$ 贡献。

**引理 156.2（反转及平移的检测）。** 令

$$
v_3=2z_{24}-z_{15},\qquad v_4=3z_{34}-z_{25},\qquad
w=z_{05}+z_{14}-8z_{23}.
\tag{156.6}
$$

则

$$
\Psi(g_a\jmath Q_{c,d})=2\Omega\otimes g_a(v_0+cv_3+dv_4),
\qquad
g_a(v_3)=v_3+aw+3a^2v_1-2a^3v_2.
\tag{156.7}
$$

证明。若 $R(e_i)=e_{5-i}$，则 $\jmath=-\bigwedge^2R$、$\det R=-1$。四次输入的四个负号相消，而目标的 $\det R$ 与 $\bigwedge^2R$ 合为 $\jmath$；因此 (155.6) 变成 $2\Omega\otimes(v_0+cv_3+dv_4)$，没有额外反转负号。又 $\det g_a=1$，$\Psi$ 的外代数定义给自然性。令 $\mathcal D(e_i)=ie_{i-1}$ 并按导子延拓；直接求得

$$
\mathcal Dv_3=-w,\quad \mathcal Dw=-6v_1,\quad
\mathcal Dv_1=2v_2,\quad \mathcal Dv_2=0.
\tag{156.8}
$$

有限二项式公式 $g_a=\exp(-a\mathcal D)$ 给第二式。这是多项式恒等式，不依赖数值样本。

## 157. 对任意固定实际枢轴成立的六个原函数

**定理 157.1（统一六方向）。** 在 (151.1) 的每个实际域和每个本原元中，定义下列六个原 $S$ 局部函数：

$$
\begin{aligned}
F_0&=\mathcal P_{0,0},\\
F_1&=\mathcal P_{1,0}-\mathcal P_{0,0},\\
F_2&=\mathcal P_{0,1}-\mathcal P_{0,0},\\
F_3&=\mathcal I_{0;1,0}-\mathcal I_{0;0,0},\\
F_4&=\mathcal I_{0;0,1}-\mathcal I_{0;0,0},\\
F_5&=\mathcal I_{1;1,0}-\mathcal I_{1;0,0}-F_3-3F_1+2F_2.
\end{aligned}
\tag{157.1}
$$

对每组预先固定的合法实际正枢轴 $p$，这六函数的共同四次符号模 $P_4$ 独立。特别地，若 $E_6$ 为这些符号的张成，则

$$
P_4\oplus E_6\subset J_4(A_p),\qquad
\dim E_6=6,\qquad \dim(J_4(A_p)/P_4)\ge6.
\tag{157.2}
$$

证明。原函数只使用已证明为单位的系数分母，以及 $\theta$、$\theta-1$ 在 $D$ 中的逆和 $f(0),f(1)\in F^\times$。命题 155.1、156.1 给完整图四阶消失及精确符号

$$
\begin{gathered}
Q_{0,0},\quad Q_{1,0}-Q_{0,0},\quad Q_{0,1}-Q_{0,0},\quad
\jmath(Q_{1,0}-Q_{0,0}),\quad \jmath(Q_{0,1}-Q_{0,0}),\\
(g_1-1)\jmath(Q_{1,0}-Q_{0,0})-3(Q_{1,0}-Q_{0,0})
+2(Q_{0,1}-Q_{0,0}).
\end{gathered}
\tag{157.3}
$$

由 (155.6)、(156.7)，检测值依次为

$$
2\Omega\otimes(v_0,v_1,v_2,v_3,v_4,w).
\tag{157.4}
$$

$v_2,v_1,v_3,v_4$ 分别支撑在 $i+j=3,4,6,7$，彼此权不同；$v_0,w$ 支撑在 $i+j=5$，其 $z_{05},z_{14}$ 系数矩阵行列式为 $-3$。特征零使六向量独立。因 $\Psi(P_4)=0$，得到模 $P_4$ 独立；引理 153.2 给包含。全部符号在代入前已经由完整图确定，故本结论的量词是对每个已经固定的 $p$，无需另选方便的 $U_2$。记

$$
L_6=\langle v_0,v_1,v_2,v_3,v_4,w\rangle_F\subset W.
\tag{157.5}
$$

## 158. 全部互素二元三次有理评估的实际归一化

**定义 158.1（二元三次条件）。** 对 $p,q\in F[T]_{\le3}$，令 $\widetilde p(X,Z)=Z^3p(X/Z)$、$\widetilde q(X,Z)=Z^3q(X/Z)$。令 $R_3(p,q)$ 为二次二元式对到五次二元式的 Sylvester 映射

$$
(A,B)\longmapsto A\widetilde p+B\widetilde q
\tag{158.1}
$$

的行列式，符号约定为 $R_3(T^3,1)=1$。只考虑

$$
R_3(p,q)\ne0.
\tag{158.2}
$$

等价地，两齐次三次式无共同射影根，即 $\gcd(p,q)=1$ 且 $\max(\deg p,\deg q)=3$。特别地 $q\ne0$，$q(\theta)$ 是实际单位。此条件包括正三次与逆三次及其全部平移；不只要求仿射互素。

**命题 158.2（一般分母的核与首项）。** 令 $x=p(\theta)/q(\theta)$。则

$$
\ker H_x=qF[T]_{\le3}.
\tag{158.3}
$$

取核基 $n_i=qT^i$，$0\le i\le3$，任选原 $F$ 补基 $m_0,m_1,m_2$。记 $d_{p,q}$ 为总基 $(n_0,\ldots,n_3,m_0,m_1,m_2)$ 对 $1,T,\ldots,T^6$ 的行列式，记

$$
\Gamma_{p,q}=\bigl(\ell(xm_im_j)\bigr)_{0\le i,j\le2},\qquad
\mathcal J_{p,q}=-\frac{d_{p,q}^2}{\det\Gamma_{p,q}}\mathcal E(x)\in S.
\tag{158.4}
$$

标量 $d_{p,q}$ 与 $\det\Gamma_{p,q}$ 均非零。定义四维斜形式，并在有序基 $1,T,T^2,T^3$ 上取 Pfaffian：

$$
\rho_{p,q}(u,v)=Y(pu,qv)-Y(qu,pv),\quad u,v\in F[T]_{\le3},
\qquad b_{p,q}=\operatorname{Pf}(\rho_{p,q}).
\tag{158.5}
$$

对每个已固定的实际枢轴，

$$
[\mathcal J_{p,q}]_{4,p_{\mathrm{pivot}}}=b_{p,q}^2.
\tag{158.6}
$$

证明。$xu=v\in C$ 蕴含 $pu=qv$，相关次数至多九，小于十四。互素性给 $u=qr$、$v=pr$，两个次数约束合为 $\deg r\le3$，反向成立。由 (152.5) 得 (158.3)。$H_x$ 的根基恰为该四维空间，所以其在任一补空间的限制非退化；这证明 $d_{p,q},\det\Gamma_{p,q}\in F^\times$，并给所有归一化单位的原域依据。

核上 $xn_i=pT^i\in C$，故一次负块正是 (158.5)。每个条目消去 Hankel 型，因为 $(pu)(qv)=(qu)(pv)$，所以属于 $W$。按此总基对 $L_x$ 作合同变换，行列式乘 $d_{p,q}^2$；Schur 补给四次首项 $\det\Gamma_{p,q}\,b_{p,q}^2$。再除以分母常数 $-1$ 及总基平方，就得 (158.4)--(158.6) 的确切符号。完整图仍至少四阶，故实际正消元不改首项。不同补基只改变已被消去的标量表示。

## 159. 完整结式除法、六个基值与检测上限

**定理 159.1（全互素二元三次族的精确检测空间）。** 存在唯一线性映射

$$
\mathcal M:\bigwedge^2F[T]_{\le3}\longrightarrow W
\tag{159.1}
$$

满足

$$
\begin{array}{lll}
\mathcal M(T^3\wedge1)=v_0,&
\mathcal M(T^2\wedge1)=v_1,&
\mathcal M(T\wedge1)=v_2,\\
\mathcal M(T^3\wedge T)=v_3,&
\mathcal M(T^3\wedge T^2)=v_4,&
\mathcal M(T^2\wedge T)=3z_{23}-z_{14}=-(v_0+w)/3.
\end{array}
\tag{159.2}
$$

对所有三次系数，包括结式为零的参数，均有多项式恒等式

$$
\boxed{\Psi(b_{p,q}^2)=2R_3(p,q)\,\Omega\otimes\mathcal M(p\wedge q).}
\tag{159.3}
$$

因此，对每个已经固定的实际枢轴，所有满足 (158.2) 的原 $\mathcal J_{p,q}$ 的四次检测值，其线性张成恰好为 $\Omega\otimes L_6$。这个六维上限只涉及此整个有理三次族的检测像，不是整个 $J_4(A_p)/P_4$ 的上界。

证明。把 $p,q$ 的八个系数作为参数，只研究 (158.5) 已给出的多项式。条目在 $p,q$ 中双次数为 $(1,1)$，所以 $\Phi(p,q)=\Psi(b_{p,q}^2)$ 双次数为 $(4,4)$。这些参数不替代实际 $H_x$：它们只是已经证明的实际核首项的系数。

先证明 $\Phi$ 在结式超曲面上消失。若 $p,q$ 共享有限根 $a$，写 $p=(T-a)p_2$、$q=(T-a)q_2$，其中次数至多二。按照 (152.11)，$\rho_{p,q}(T^i,T^j)$ 对应的交错二元多项式为

$$
\frac{p(s)q(t)-q(s)p(t)}{s-t}\,(s^it^j-s^jt^i).
\tag{159.4}
$$

它带有因子 $(s-a)(t-a)$，且各变量除去该因子后次数至多四。故全部六条目属于

$$
\bigwedge^2\bigl((T-a)F[T]_{\le4}\bigr).
\tag{159.5}
$$

括号内只有五维，三个这样的二向量外乘为零，故 $\Phi=0$。若共同根是无穷远，则 $\deg p,\deg q\le2$；(159.4) 各变量次数至多四，全部条目属于 $\bigwedge^2F[T]_{\le4}$，同理消失。共同根在代数闭包中的情形完全相同。

下面证明这里确实可除以一个既约结式，而不只在其零集消失。Sylvester 映射 (158.1) 有核当且仅当两齐次式有共同因子。两式同时为零时核非零显然；其余情形中，互素时 $\widetilde q\mid A$、$\widetilde p\mid B$，次数不容许非零解；若共同因子为 $r$，则 $(\widetilde q/r,-\widetilde p/r)$ 乘一个次数 $\deg r-1$ 的非零二元式即给核向量。故结式零集恰为公共根集合。

在代数闭包上，关联簇

$$
\{(p,q,[X:Z]):\widetilde p(X,Z)=\widetilde q(X,Z)=0\}
\tag{159.6}
$$

是 $\mathbb P^1$ 上秩六向量丛的总空间，因而不可约，维数七。其到八维系数空间的投影因 $\mathbb P^1$ 完备而闭；在恰有一个共同简单根的非空开集，投影纤维为一个点，故像是不可约超曲面。这个开集非空，例如两个各有三个互异根、只共享其中一个根的首一多项式。结式行列式双次数为 $(3,3)$。在 $p$ 有三个互异有限根的图上，其乘积公式为

$$
R_3(p,q)=p_3^3\prod_{p(r)=0}q(r),\qquad p_3=[T^3]p.
\tag{159.7}
$$

这可由在 $F[T]/(p)$ 上乘以 $q$ 的行列式求出，也可将 Sylvester 消元按三个评价分解得到。固定这样的 $p$，让 $q$ 只在其中一个根处简单变为零，(159.7) 给横向一重零点。因而结式不是该不可约超曲面方程的高次幂，而是其既约不可约方程，符号由 (158.1) 固定。

$\Phi$ 的每个坐标在整个超曲面上消失，故在多项式唯一分解环中均被 $R_3$ 整除。商的双次数为 $(1,1)$。交换 $p,q$ 时 $\rho$ 变号，$b$ 及 $b^2$ 不变；但 $R_3(q,p)=(-1)^9R_3(p,q)=-R_3(p,q)$。所以商交错双线性，唯一写成 $2\Omega\otimes\mathcal M(p\wedge q)$。该恒等式先在代数闭包成立；除法商的唯一性或忠实扩域后的系数比较使它在 $F$ 上成立。

现在确定全部六个基值。取 $p=T^3+cT^2+dT$、$q=1$，结式为一，(155.6) 决定 (159.2) 前三值。取 $p=1+cT+dT^2$、$q=T^3$，结式为 $-1$，而 (156.3) 的核 Pfaffian 平方给 $\Phi=2\Omega\otimes(v_0+cv_3+dv_4)$。比较 $c,d$ 系数，确定第四、第五值。

最后确定尚未决定的 $T^2\wedge T$。平移 $T\mapsto T-a$ 在 $V$ 及 $F[T]_{\le3}$ 上的行列式均为一；在 (158.5) 同时改四维核基为 $(T-a)^i$，不改变 Pfaffian。由自然性，$\Phi$ 对平移等变；结式在此行列式一的变量变换下不变。因此在结式非零的稠密开集可相除，得到 $\mathcal M$ 的平移等变性，再由多项式恒等延及全部参数。展开

$$
\begin{aligned}
(T-a)^3\wedge(T-a)={}&T^3\wedge T-aT^3\wedge1-3aT^2\wedge T\\
&+3a^2T^2\wedge1-2a^3T\wedge1.
\end{aligned}
\tag{159.8}
$$

左端经 $\mathcal M$ 等于 $g_a(v_3)$。比较 (156.7) 的 $a$ 系数，得

$$
-v_0-3\mathcal M(T^2\wedge T)=w,
$$

即 (159.2) 最后一值。六个外积是一组基，故全部基值已定，证明 (159.3)。其像为 $L_6$：前五值给 $v_0,\ldots,v_4$，最后一值再给 $w$，而定理 157.1 已证独立。实际族上界由 (159.3) 给出，下界由 (157.1) 的六个实际函数给出；这些函数是本族评估的有限线性组合，归一化与 (158.4) 一致。整个结式证明未使用表示论分类，也没有对全部四次像作上界推断。

## 160. 余秩三的真实第四式保留实际 $U_2$

**定理 160.1（首一四次评估）。** 固定任一实际枢轴 $p$ 及其真实 $U_{2,p}$。对

$$
h=T^4+cT^3+dT^2+eT,\qquad c,d,e\in F,
$$

实际核为 $N_3=\langle1,T,T^2\rangle$，取补空间 $M_4=\langle T^3,T^4,T^5,T^6\rangle$，令

$$
\mathcal H_h=(H_h)_{M_4M_4},\qquad R_h=B_hY-YB_h^{\mathsf T},
\qquad \det\mathcal H_h=1.
\tag{160.1}
$$

置

$$
\begin{aligned}
a_h&=z_{04}+cz_{03}+dz_{02}+ez_{01},\\
b_h&=z_{05}+z_{14}+c(z_{04}+z_{13})+d(z_{03}+z_{12})+ez_{02},\\
c_h&=z_{15}+cz_{14}+dz_{13}+ez_{12},\qquad
v_h=(c_h,-b_h,a_h)^{\mathsf T},\\
\mathcal G_{h,p}&=(B_hU_{2,p}-U_{2,p}B_h^{\mathsf T}-YD_hY)_{N_3N_3}
 +(R_h)_{N_3M_4}\mathcal H_h^{-1}(R_h)_{N_3M_4}^{\mathsf T}.
\end{aligned}
\tag{160.2}
$$

则 $\varphi_p(\mathcal E(h(\theta)))$ 至少从四次起，且精确四次符号为

$$
\boxed{[\mathcal E(h(\theta))]_{4,p}=-v_h^{\mathsf T}\mathcal G_{h,p}v_h.}
\tag{160.3}
$$

证明。$hu\in C$ 的次数比较给 $\deg u\le2$，故核恰为 $N_3$。补块在指标和小于九时为零，等于九时为一；四阶反转列符号为 $(-1)^6=1$，故 (160.1) 成立。将真实图 $U=U_{2,p}+O(Y^4)$ 代入 (152.6)，按 $N_3\oplus M_4$ 作 Schur 补。核补的一次项为

$$
A_h=\begin{pmatrix}0&a_h&b_h\\-a_h&0&c_h\\-b_h&-c_h&0\end{pmatrix},
\qquad \det A_h=0,\qquad \operatorname{adj}(A_h)=v_hv_h^{\mathsf T}.
\tag{160.4}
$$

条目由 (155.4) 给出。其二次项恰是 $\mathcal G_{h,p}$：原二次块为 $B_hU_2-U_2B_h^{\mathsf T}-YD_hY$；一次交叉块满足 $(R_h)_{M_4N_3}=-(R_h)_{N_3M_4}^{\mathsf T}$，故 Schur 校正具有 (160.2) 的正号。三阶行列式的最低三次项为零，四次项唯一来自两个一次因子与一个二次因子，等于

$$
\operatorname{tr}(\operatorname{adj}(A_h)\mathcal G_{h,p})
=v_h^{\mathsf T}\mathcal G_{h,p}v_h.
$$

三阶及更高的核补项乘两个一次因子至少五阶；补块行列式的非常数项乘最低三次行列式也不能贡献四次，因为该三次项为零。补块常数一、公共分母常数 $-1$ 给 (160.3)。偶性排除五次。特别地，

$$
-v_h^{\mathsf T}(B_hU_{2,p}-U_{2,p}B_h^{\mathsf T})_{N_3N_3}v_h
\tag{160.5}
$$

正是允许参与第四项的真实贡献，不能删去。

**命题 160.2（原枢轴二次数据的提取）。** (160.3) 中 $U_{2,p}$ 由原 $p$ 决定。更具体地，对实际 $x\in D$，令

$$
\mathfrak b_x(Y)=-\operatorname{tr}(\operatorname{adj}(H_x)YD_xY)
+[t^2]\det(H_x+tR_x),\qquad R_x=B_xY-YB_x^{\mathsf T}.
\tag{160.6}
$$

则

$$
[\mathcal E(x)(0,Y)]_2
=\frac{\mathfrak b_x(Y)-\mathcal E(x)(C)\mathfrak b_{\theta^7}(Y)}{-1}.
\tag{160.7}
$$

证明。在 $\det(H_x+tR_x-t^2YD_xY)$ 中取 $t^2$ 系数，得到 (160.6)。一次项为零，因为对称矩阵的伴随与斜矩阵迹配对为零。对分子、分母作二次商法则并使用 (152.7)，得到 (160.7)。对 $x$ 的原 $F$ 多项式坐标取系数，便得到生成函数 $s_\alpha$ 的二次数据；若枢轴为这些系数的局部有理函数，在 $U=0$ 时各系数增量从 $Y^2$ 起，其二次项只用在基点的一阶系数泛函，更高导数从四次起。于是可由原系数表达式取得每个 $q_{ij}$，再由 (153.3) 得 $U_{2,p}$。此公式不将 $q_{ij}$ 当成任意独立二次参数。

## 161. 九个原评估实现 $z_{23}^2$

**命题 161.1（显式原 $S$ 函数）。** 令

$$
p_s(T)=T^2+sT^5,\quad q_b(T)=T^3+b,\quad
s\in\{2,3,4\},\quad b\in\{1,2,3\},\quad
x_{s,b}=p_s(\theta)/q_b(\theta).
\tag{161.1}
$$

取实际补基 $\mathcal M_5=(1,T,T^2,T^5,T^6)$，定义

$$
\Gamma_{s,b}=\bigl(\ell(x_{s,b}m_im_j)\bigr)_{m_i,m_j\in\mathcal M_5},
\qquad G_{s,b}=-\frac{\mathcal E(x_{s,b})}{\det\Gamma_{s,b}},
\tag{161.2}
$$

$$
H_b=6G_{2,b}-8G_{3,b}+3G_{4,b},\qquad
 g=3H_1-3H_2+H_3.
\tag{161.3}
$$

全部分母是原单位，$g\in S$，且

$$
g(C)=0,\qquad [g]_{1,(U,Y)}=0,\qquad [g(0,Y)]_2=z_{23}^2.
\tag{161.4}
$$

证明。$q_b(\theta)\ne0$ 因次数小于十四。模 $q_b$ 有 $p_s\equiv(1-sb)T^2$，而 $b(1-sb)\ne0$，故 $p_s,q_b$ 互素。若 $x_{s,b}u=v\in C$，清分母所得等式次数至多十一，小于十四，因此为多项式恒等式。互素性给 $u=q_br$、$v=p_sr$，次数五的分子强制 $\deg r\le1$，反向成立。所以

$$
\ker H_{x_{s,b}}=q_bF[T]_{\le1}.
\tag{161.5}
$$

核基 $q_b,Tq_b$ 与 $\mathcal M_5$ 合成七元基，其对原幂基的行列式为一：去掉 $b$ 的低次列贡献后，其次数序列是 $(3,4,0,1,2,5,6)$，交换符号 $(-1)^6=1$。根基为二维，故补块 $\Gamma_{s,b}$ 非退化，$\det\Gamma_{s,b}\in F^\times$。

核上的首阶负向斜条目为

$$
\begin{aligned}
Y(p_s,Tq_b)-Y(Tp_s,q_b)
&=-z_{23}+bz_{02}+sz_{35}+sbz_{05}.
\end{aligned}
\tag{161.6}
$$

二阶斜行列式为它的平方。总基行列式平方一、补块行列式以及公共分母 $-1$，连同 (161.2) 的负号，给

$$
[G_{s,b}(0,Y)]_2=(z_{23}-bz_{02}-sz_{35}-sbz_{05})^2.
\tag{161.7}
$$

完整图中这些函数至少二阶，所以没有一次项；代入 $U=O(Y^2)$ 不改变该纯二次项。对任意次数至多二的一元多项式 $r$，Lagrange 插值恒等式为

$$
r(0)=6r(2)-8r(3)+3r(4),\qquad
r(0)=3r(1)-3r(2)+r(3).
\tag{161.8}
$$

依次对 (161.7) 的 $s$、$b$ 应用，得到 $z_{23}^2$。这些固定节点只是精确插值定义，未以数值实验代替证明。$g$ 是九个已给出原评估的有限 $F$ 线性组合，全部额外分母已由实际根基和补基证明非零。

## 162. 原源关系造成不可删去的正枢轴依赖

**定理 162.1（明确的一参数枢轴变化）。** 固定任一合法归一化实际枢轴 $p$。对每个 $\lambda\in F$，在原 $S$ 内定义

$$
p_{\lambda,15}=p_{15}+\lambda g,\qquad
p_{\lambda,ij}=p_{ij}\quad((i,j)\ne(1,5)),
\tag{162.1}
$$

其中 $g$ 是 (161.3)。每组 $p_\lambda$ 均合法，且在同一负坐标中有

$$
[\mathcal E(\theta^4)]_{4,p_\lambda}
-[\mathcal E(\theta^4)]_{4,p}
=-2\lambda(z_{05}+z_{14})^2z_{23}^2,
\tag{162.2}
$$

$$
\boxed{\Psi\left([\mathcal E(\theta^4)]_{4,p_\lambda}
-[\mathcal E(\theta^4)]_{4,p}\right)
=-8\lambda\,\Omega\otimes z_{23}.}
\tag{162.3}
$$

若 $\lambda\ne0$，该四次差不在 $P_4$。

证明。$g$ 没有完整图一次项，故一次正 Jacobian 不变。令 $E_{ij}$ 表示在 $(i,j)$ 处为一、$(j,i)$ 处为负一的交错矩阵，(153.3) 给

$$
U_{2,p_\lambda}-U_{2,p}=-\lambda z_{23}^2E_{15}.
\tag{162.4}
$$

专取 $h=T^4$。在 (160.2) 中，$a=z_{04}$、$b=z_{05}+z_{14}$、$c_0=z_{15}$，$v=(c_0,-b,a)^{\mathsf T}$。视它为 $N_3$ 中向量 $v=c_0-bT+aT^2$，有 $hv=c_0T^4-bT^5+aT^6\in C$。对任意交错型 $U$，实际乘法块给

$$
v^{\mathsf T}(B_hU-UB_h^{\mathsf T})_{N_3N_3}v
=2U(hv,v).
\tag{162.5}
$$

其中 $E_{15}(hv,v)=-b^2$，因为唯一相关的非零配对是 $T^5$ 与 $T$。将 (162.4) 代入 (160.3)，严格得到 (162.2)。

又 $\mu_2(b^2)=2e_{0145}$，而 $\mu_2(z_{23}^2)=0$。外乘 $e_{0145}\wedge z_{23}=\Omega$，故 (154.2) 给

$$
\Psi(b^2z_{23}^2)=4\Omega\otimes z_{23},
$$

证明 (162.3)。非零检测值不可能属于 $\Psi(P_4)=0$。

**推论 162.2（改变枢轴后的一般七方向）。** 对每个起始 $p$，沿 (162.1) 的实际枢轴族，除至多一个 $\lambda$ 外，

$$
\dim\Psi(J_4(A_{p_\lambda}))\ge7,\qquad
\dim(J_4(A_{p_\lambda})/P_4)\ge7.
\tag{162.6}
$$

证明。$z_{23}\notin L_6$。事实上权五部分只有 $v_0,w$；若 $z_{23}=\alpha v_0+\beta w$，比较 $z_{05},z_{14}$ 系数得 $\beta=\alpha$、$3\alpha=0$，与 $z_{23}$ 系数矛盾。令 $\Psi([\mathcal E(\theta^4)]_{4,p})=\Omega\otimes d_p$；在 $W/L_6$ 中，(162.3) 是斜率非零的仿射直线 $[d_p]-8\lambda[z_{23}]$，至多一个参数给零。其余参数下，再加定理 157.1 的六个共同方向即得七方向。这里改变了实际纤维；不把它改写成对每个事先固定 $p$ 的统一七方向断言。

## 163. 单个四次评估的跨纤维仿射目标轨道

**引理 163.1（$\partial_{23}:K\to W$ 的显式右逆）。** 在对称代数中令 $\partial_{23}=\partial/\partial z_{23}$。定义原 $F$ 线性映射 $\mathcal R:W\to Q_2$，在基元上为

$$
\begin{aligned}
\mathcal R(z_{23})&=\tfrac12z_{23}^2,\\
\mathcal R(z_{ij})&=z_{23}z_{ij}
&&\bigl(\{i,j\}\cap\{2,3\}\ne\varnothing,\ (i,j)\ne(2,3)\bigr),\\
\mathcal R(z_{ij})&=z_{23}z_{ij}+z_{2i}z_{3j}
&&\bigl(\{i,j\}\cap\{2,3\}=\varnothing\bigr),
\qquad i<j.
\end{aligned}
\tag{163.1}
$$

则 $\mathcal R(W)\subset K$，且 $\partial_{23}\mathcal R=\operatorname{id}_W$。特别地 $\partial_{23}:K\to W$ 满射。

证明。前两类的外乘有重复指标，故为零。第三类满足

$$
e_2\wedge e_3\wedge e_i\wedge e_j
+e_2\wedge e_i\wedge e_3\wedge e_j=0,
$$

因此也在 $K$ 中。第三类的修正乘积不含 $z_{23}$；前两类的导数也直接为指定基元。三个公式覆盖 $W$ 的全部基，证明右逆性质。

**定理 163.2（单一评估的任意检测目标）。** 固定实际 $D,F,\theta$、横截面和任一起始枢轴 $p$，写

$$
\Psi([\mathcal E(\theta^4)]_{4,p})=\Omega\otimes d_p.
$$

对任意指定 $\tau\in W$，存在原 $F$ 合法枢轴 $p^{(\tau)}$，只改变第 $(1,5)$ 条，具有同一次正坐标，并满足

$$
\Psi([\mathcal E(\theta^4)]_{4,p^{(\tau)}})=\Omega\otimes\tau.
\tag{163.2}
$$

可用同一个实际源提升 (153.8) 明确指定：

$$
\kappa=\mathcal R((d_p-\tau)/4),\qquad
p^{(\tau)}_{15}=p_{15}+\mathcal L(\kappa),\qquad
p^{(\tau)}_{ij}=p_{ij}\ ((i,j)\ne(1,5)).
\tag{163.3}
$$

证明。对任意 $\kappa\in K$，只改变 $p_{15}$ 为 $p_{15}+\mathcal L(\kappa)$，实际二阶图差为 $-\kappa E_{15}$。沿用 (162.5) 和 (160.3)，得到

$$
\Delta[\mathcal E(\theta^4)]_4=-2b^2\kappa,
\qquad b=z_{05}+z_{14}.
\tag{163.4}
$$

由 $\mu_2(\kappa)=0$ 和 $\mu_2(b^2)=2e_{0145}$，而 $e_{0145}$ 只与 $W$ 中 $z_{23}$ 的分量外乘非零，(154.2) 精确给

$$
\Psi(b^2\kappa)=2\Omega\otimes\partial_{23}\kappa,
\qquad
\Delta\Psi=-4\Omega\otimes\partial_{23}\kappa.
\tag{163.5}
$$

代入 (163.3)，右逆性质给变化量 $\Omega\otimes(\tau-d_p)$，证明目标值。合法性和原源成员资格由定理 153.3 保证；所有提升都在同一个实际 $S$ 中，未引入抽象二次函数作为新源。

**注记 163.3（精确的量词边界）。** 定理 157.1 是每个已经固定枢轴的统一六维结论；推论 162.2 是明确改变枢轴的一参数族中除至多一个参数外的七维结论；定理 163.2 是同一个函数在不同纤维间的完整仿射检测目标轨道。最后一个结论允许选择 $\tau=0$，所以 $\mathcal E(\theta^4)$ 这个单独评估不能承担“对每组枢轴都给第七个非零检测方向”的证明。它没有否定其他函数给统一第七方向的可能性。分别可达的 $\tau$ 属于分别改变后的纤维，不能拼成一组固定 $A_p$ 中同时存在的十五个方向。上述比较也不判定两个 $A_p$ 是否抽象同构，或它们的整个四次空间是否相同。

## 164. 实际像的余切核、正规化侧余核与嵌入维数

**定理 164.1（两个方向不同的余切结论）。** 令 $\mathfrak m_p$ 为实际像 $A_p$ 的极大理想，$\mathfrak n_p$ 为 $B_{0,p}$ 的极大理想，记

$$
J_p^A:\mathfrak m_p/\mathfrak m_p^2\longrightarrow
\mathfrak n_p/\mathfrak n_p^2.
\tag{164.1}
$$

对每个已固定的合法枢轴，

$$
\operatorname{im}J_p^A=K,\qquad
\operatorname{coker}J_p^A\simeq Q_2/K\simeq\bigwedge^4V,
\qquad \dim\operatorname{coker}J_p^A=15,
\tag{164.2}
$$

$$
\dim\ker J_p^A\ge6,\qquad
\operatorname{edim}A_p\ge105+6=111.
\tag{164.3}
$$

沿推论 162.2 的参数族，除至多一个参数外可将 (164.3) 的下界加强为 $7$ 与 $112$。对于原 $S$ 到正规化的映射 $J$，还有

$$
\operatorname{rank}J=21+105=126,\qquad
\dim\ker J\ge6,\qquad \operatorname{edim}S\ge132.
\tag{164.4}
$$

证明。偶幂级数环的极大理想模平方只保留 $Y$ 二次项，所以 $\mathfrak n_p/\mathfrak n_p^2=Q_2$。引理 153.2 确定实际像为 $K$，外乘满射给 (164.2)。这里的 $B_{0,p}$ 是既有正规化环的实际正纤维；没有额外宣称它必然是 $A_p$ 自己的正规化。

每个 $F_i$ 的实际像从四次起，故其 $A_p$ 余切类映到零。若其某个非零 $F$ 线性组合属于 $\mathfrak m_p^2$，取四次符号时，每个乘积因子的最低阶至少二，且其二次符号在 $K$，所以该线性组合的四次符号属于 $KK=P_4$。这与 (157.4) 的独立检测值矛盾。故源核至少六维。再从 $K$ 取一组基的实际提升，先取二次符号可见这些类与六个四次类联合独立，得到嵌入维数下界 $111$。有七个独立检测值的改变后纤维使用同一论证得 $112$。

原 $S$ 的映射秩由 (153.2) 给 $126$。六个 $F_i$ 在完整图四阶消失，故一次 $U$ 和纯二次 $Y$ 均为零，它们的原源类在 $\ker J$ 中；若存在源余切线性关系，代入任一实际纤维同样会给 $P_4$ 中的四次符号，与独立检测矛盾。所以 (164.4) 成立。这里 $\ker J_p^A$、$\ker J$ 是两个源的核；$\bigwedge^4V$ 是目标侧余核。$A_p=\mathscr T/\mathfrak L_p$ 的源还涉及 $\mathfrak L_p$，不能以 $S/(p)$ 代替；数字十五也不是原源嵌入维数。

## 165. 原始来源、有限重叠与开放数学问题

**约定 165.1（引用承担的范围）。** 下列条目仅承担所列数学输入或工具对应。本卷的文献状态为 `repo-derived` 的原族综合推导，配以表内 `literature-attested` 的工具对应；不作全球原创或最小性判断。

| 原始来源 | 精确对应与边界 |
| --- | --- |
| [039，固定版本 e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb，§§111、113、115--117](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) | `repo-derived`：原符号系数、原乘法商、有限正规化与实际对合横截面。 |
| [040，固定版本 f32f2d3b8219fae2014e5db4ab3c31575edf0672，定理 122.1、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) | `repo-derived`：同一原域的完整耦合像 $M\cap Q_2=K$ 与正投影满射；支付 (153.7)--(153.8) 的实际同时源提升。 |
| [042，固定版本 fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6，§§134--140](https://github.com/the-omega-institute/trureturing/blob/fd9d6f7737ac0bf2274eddc48d5bde4ac0da1db6/docs/develop/theory/AURIC_R5_042_UNIFORM_ORIGINAL_QUARTIC_LIFTS_BEYOND_QUADRATIC_PRODUCTS.md) | `repo-derived`：实际正纤维二次桥、完整图四阶机制、检测器与十四次域的三个正三次方向。本卷复用其接口并给出所需具体计算；这些部分不是新增内容。 |
| Masoumeh Sepideh Shafiei, [*Apolarity for determinants and permanents of generic matrices*, arXiv:1212.0515v2，Lemma 4.6、Lemma 4.7、Theorem 4.11](https://arxiv.org/html/1212.0515v2) | `literature-attested`：Lemma 4.6 描述四阶 Pfaffian 空间的二次消去空间；Lemma 4.7 接到大 Pfaffian 的导数空间；Theorem 4.11 说泛型偶阶斜矩阵 Pfaffian 的 apolar ideal 由二次式生成。原文这些条款不提供实际原系数像。 |
| Jesse Leo Kass and Kirsten Wickelgren, [*A classical proof that the algebraic homotopy class of a rational function is the residue pairing*, arXiv:1602.08129v2，§3，式 (19) 及紧随其后的残数公式](https://arxiv.org/html/1602.08129v2#S3) | `literature-attested`：简单根前提下，式 (19) 的泛函为 $\phi(a)=\operatorname{Tr}(a/(f'g))$，其后区分 $\operatorname{Res}(a)=\operatorname{Tr}(ag/f')$。本卷对应 $g=1$、$F[T]/(f)=D$，两者才同为 $\ell$。本卷所需矩恒等式另由 (152.2) 的插值证明承担。 |

**注记 165.2（文献工具不能支付的结论）。** 固定 $\Omega$ 后，六维 $V$ 的二向量空间 $W$ 上的 Pfaffian 三次型可写为 $\operatorname{Pf}(w)=\Omega^*(w\wedge w\wedge w)/6$。其二次微分算子对应的线性形式是 $w\mapsto\Omega^*(\mu_2(q)\wedge w)$；$\bigwedge^4V$ 与 $\bigwedge^2V$ 的外乘配对非退化，所以其二次 apolar 核对应 $K$。这说明 Shafiei 的工具与本卷 $K$ 的对应条件。但该 apolar 理想由 $K$ 生成时，其四次部分是

$$
K\operatorname{Sym}^2W,
$$

不是本文更窄的 $KK$。所以二次生成定理既不能推出检测器核的特定等式，也不能推出 $A_p$ 的四次满像。Kass--Wickelgren 在所列段落将残数--迹公式归于 Scheja--Storch 的 (4.2) Satz；这里只引用已列原作者论文的精确条文，不把该转引冒充对另一原文的核对。残数配对、泛 Pfaffian 工具、实际有理三次族的六个函数与原枢轴关系，是不同层次的结论。

在以上有限源范围内，039/040 承担原商与完整二次像，042 承担正三次机制；§§156--159 的反向有理评估、完整结式除法和六维检测确定，以及 §§160--163 的真实第四式与原源枢轴控制，在本文给出纸面推导。此有限重叠说明不声称穷尽其他仓内内容或全部文献。

**问题 165.3（固定纤维的首个缺失方向，open）。** 对任意已经给定且不再改变的 $p$，构造实际原源函数 $a$，使其常数和实际二次项均为零而

$$
\Psi([a]_{4,p})\notin\Omega\otimes L_6.
\tag{165.1}
$$

一个明确补空间是

$$
W=L_6\oplus\langle z_{01},z_{02},z_{03},z_{04},z_{23},z_{15},z_{25},z_{35},z_{45}\rangle_F.
\tag{165.2}
$$

按指标和分组，再在权五中比较 $z_{05},z_{14},z_{23}$，可验证此直和。具体商测试可用

$$
\kappa_0(v)=5[z_{05}]v+3[z_{14}]v+[z_{23}]v;
\qquad \kappa_0(L_6)=0,\quad\kappa_0(z_{23})=1.
\tag{165.3}
$$

已证明的 $-8\lambda z_{23}$ 是换纤维的差，不是固定 $p$ 下 (165.1) 的解；定理 163.2 还表明单一 $\theta^4$ 检测值可被合法改到零。定理 159.1 排除了在整个互素二元三次评估族内部取得第七个检测方向，故这个固定纤维问题需要该族之外的原函数或实际系数关系。

**问题 165.4（完整像与关系边界，open）。** 本文没有确定固定 $p$ 的全部 $\Psi(J_4(A_p))$、全部 $J_4(A_p)/P_4$ 或其精确维数，也未分析检测器看不见的四次类及其实际源像。即使某个固定纤维的检测像达到整个十五维目标，也仍须另行处理检测器核中模 $P_4$ 的部分，才能确定完整四次像。本文也未确定 $\mathfrak L_p=(p)\mathscr T$，未判定不同枢轴实际像的抽象同构或整个四次空间的相等性，未从这些局部四次公式推出完整形式芽、全局导子、算术可判定性或物理主张。统一七方向以及任意固定纤维的检测满像仍未由本文建立。

## 166. 中文普通语言的数学解释

**命题 166.1（六方向与枢轴控制的量词说明）。** 在任意特征零十四次实际域里，使用任一本原元的前七个连续幂，并保留原来的全部带符号、带标签系数，逆三次评估确实给出了正三次评估之外的实际四次信息。正三次留下低次四维核，逆三次留下移到高次的四维核；两个窗口再配合一次平移，产生六个明确原函数。它们的行列式在全部图变量中本来就从四次开始，而真实正枢轴补偿从负变量二次开始，所以这些最低第四项对每组已经固定的合法枢轴都相同。检测器消去所有可见二次信息的两两乘积，却区分这六项，因此六方向确实超出这些乘积。

把分子、分母推广到全部互素二元三次式，也无法在这个检测器下取得第七方向。原因不是只检查了若干倒数样本，而是完整结式恒等式：检测值等于结式乘一个六维外积空间的固定线性像，且六个基值已经全部确定。这个上限只约束该评估族的检测值，不是整个原系数四次信息的上限。

四次多项式评估留下三维核，机制不同。三阶斜矩阵的行列式为零，但它的二阶余子式不为零；余子式乘上真实枢轴二次补偿，恰好成为第四项。所以不能删去 $U_2$。九个实际原评估组成的函数 $g$ 实现了一个明确原系数关系：改变一条正枢轴后，四次检测差严格为 $-8\lambda\Omega\otimes z_{23}$，且非零时不属于二次乘积。

允许的归一化枢轴二阶差恰好是二十一个 $K$ 值，不能任意取整个二次空间；040 的完整耦合像同时提供这些差的实际原源提升。即便有这个约束，$\partial_{23}:K\to W$ 的明确右逆仍使同一个 $\theta^4$ 评估在改变后的不同纤维间取得任意检测目标，包括零。因此必须区分任意固定枢轴下的六方向、自由改选枢轴后一般能有七方向，以及单个检测值跨不同纤维的任意赋值。后两者都没有解决任意给定固定纤维的第七方向问题。

最后，原实际像的余切源核至少六维，嵌入维数至少一百一十一；正规化一侧的余切余核则是十五维外四次空间。这些数字属于方向相反的映射信息，不能互相替换。上述陈述分别由 §§153--164 的构造、阶数、结式和实际源提升证明承担；它们保留全部固定域、固定本原元、固定原系数及固定或改变枢轴的条件。

## 追加锚（本行以下为增补区）

## 190. 实际二项式域中原四三系数的全固定枢轴消失反例

**定义 190.1（同一个实际源与待测系数）。** 取

$$
F=\mathbb Q,\qquad D=\mathbb Q[T]/(T^{14}-2),\qquad
\theta=T\bmod(T^{14}-2),\qquad C=\langle1,\theta,\ldots,\theta^6\rangle.
\tag{190.1}
$$

保留定义 151.2 的全部带符号、带原嵌入标签系数、任意非零体积形式，以及定义 151.3 的原函数

$$
\mathcal E(x)=P_{C'}(x)/P_{C'}(\theta^7)\in S.
\tag{190.2}
$$

负横截面固定为对称七阶矩阵空间中的

$$
N=\{Y=Y^{\mathsf t}:Y_{0j}=Y_{6j}=0\ (0\le j\le6)\}.
\tag{190.3}
$$

所有七阶矩阵指标均为 $0,\ldots,6$。置 $V=\mathbb Q[T]_{\le5}$、$e_i=T^i$、$W=\bigwedge^2V$，保持原约定

$$
z_{ij}=Y_{i+1,j}-Y_{i,j+1}\longleftrightarrow e_i\wedge e_j,
\qquad \Omega=e_0\wedge\cdots\wedge e_5.
\tag{190.4}
$$

这里 $z_{ji}=-z_{ij}$、$z_{ii}=0$。$\mu_2$、$K$、$\delta$、$\Psi$ 分别是 (153.1)、(154.1)--(154.2) 的映射和空间。已知六维空间仍为

$$
\begin{aligned}
L_6=\langle&2z_{14}-z_{05}-z_{23},\ 2z_{13}-z_{04},\ 3z_{12}-z_{03},\\
&2z_{24}-z_{15},\ 3z_{34}-z_{25},\ z_{05}+z_{14}-8z_{23}\rangle_{\mathbb Q}.
\end{aligned}
\tag{190.5}
$$

先固定任意一组合法原源对合偶正枢轴 $s$，将一次正项线性归一化为 $u_{ij}=U(T^i,T^j)$，$0\le i<j\le6$。记

$$
q_{ij}=[s_{ij}(0,Y)]_2,\qquad
U_s(Y)=U_{2,s}(Y)+O(Y^4),\qquad (U_{2,s})_{ij}=-q_{ij}.
\tag{190.6}
$$

枢轴在任何评估与系数提取以前固定，始终使用其真实消元。用两个标量不定元 $u,v$ 定义原源函数

$$
\mathcal E(u\theta^4+v\theta)=\sum_{a+b=7}u^av^b g_{ab},
\qquad g_{43}=[u^4v^3]\mathcal E(u\theta^4+v\theta)\in S,
\tag{190.7}
$$

并定义其商检测类

$$
C_{43}=\left[\Omega^{-1}\Psi([g_{43}]_{4,s})\right]\in W/L_6.
\tag{190.8}
$$

$\Omega^{-1}$ 表示对 $\det(V)$ 因子使用与 $\Omega$ 对偶的线性泛函，不是矩阵逆。下文 $T$ 始终表示多项式变量，转置写为 ${}^{\mathsf t}$；移位矩阵另写作 $\mathsf S$。

**定理 190.2（实际域、原源及每个预固定枢轴的精确值）。** 在定义 190.1 中，$D$ 是实际十四次可分域，$N$ 是合法十五维负补空间。对于每个预先固定的合法原源枢轴 $s$，有

$$
\boxed{\Psi([g_{43}]_{4,s})=2\Omega\otimes(3z_{12}-z_{03}),\qquad C_{43}=0.}
\tag{190.9}
$$

此结论保持任意非零原体积形式、完整带符号系数源、同一原分母及同一实际正纤维。

证明。（一）先确定实际乘法和横截面。$T^{14}-2$ 在素数 $2$ 处满足 Eisenstein 判据，故在 $\mathbb Q[T]$ 不可约；特征零保证可分。使用 (152.1) 的残数泛函 $\ell$。它在次数至多十三的代表元上取 $T^{13}$ 的系数，所以

$$
\ell(\theta^n)=0\quad(n\not\equiv13\pmod {14}),\qquad
\ell(\theta^{13})=1,\qquad \ell(\theta^{27})=2
\tag{190.10}
$$

对下面出现的非负指数成立。于是 $c_i=\theta^i$、$d_i=\theta^{13-i}$ 已经是实际残数双曲帧：$\ell(c_id_j)=\delta_{ij}$，而 $d_id_j$ 的指数在 $14,\ldots,26$ 内，故 $\ell(d_id_j)=0$。特别地，(152.3) 的 $Q=I_7$、$G=0$，没有额外双曲化修正。

令 $J_7$ 是七阶反转矩阵，$\mathsf S_{i,i+1}=1$，其余条目为零。对 $1\le k\le7$，由 (152.4) 逐项得到真实乘法块

$$
(H_k)_{ij}=\begin{cases}1&i+j=13-k,\\0&\text{其余},\end{cases}
\quad B_k=\mathsf S^k,\quad
(D_k)_{ij}=\begin{cases}2&i+j=k-1,\\0&\text{其余}.\end{cases}
\tag{190.11}
$$

这里下标 $k$ 表示乘以 $\theta^k$，不是自由块参数。尤其

$$
H_7=J_7,\quad B_7=0,\quad D_7=2J_7,\quad \det H_7=-1.
\tag{190.12}
$$

在原体积下，$P_C(\theta^7)$ 是非零幂基体积；$-1$ 仅是消去共同帧体积后的矩阵行列式。比值 (190.2) 不依赖这个共同非零体积因子。

对称七阶矩阵维数为 $28$。条件 (190.3) 施加 $13$ 个独立线性条件，留下中间 $1,\ldots,5$ 的任意对称五阶矩阵，故 $\dim N=15$。Hankel 空间 $\mathcal O$ 的条目是 $Y_{ij}=h_{i+j}$；其第零行给 $h_0,\ldots,h_6$，第六行给 $h_6,\ldots,h_{12}$。所以 $N\cap\mathcal O=0$，且 $28=15+13$，即 $\operatorname{SymMat}_7=\mathcal O\oplus N$。由 (152.10) 的差分核刻画，十五个 $z_{ij}$ 正是 $N$ 的独立线性坐标。这是在实际域的实际商中取横截面。

（二）定义并限制原源耦合映射。由 (153.2) 的正投影满射，对每个正一次类 $u_{ij}$ 选任一源提升 $(u_{ij},q_{ij})\in M$，定义

$$
\Gamma:P^\vee\longrightarrow\bigwedge^4V,\qquad
\Gamma(u_{ij})=\mu_2(q_{ij}).
\tag{190.13}
$$

若换源提升，两个二次项之差属于 $M\cap Q_2=K$，故其 $\mu_2$ 相同。因而 $\Gamma$ 是由完整原源决定的线性映射；换任一归一化合法枢轴仍得到同一映射。这正是 040 的 (122.12)、(122.15)--(122.16) 的耦合修正在此坐标中的表示，不能将 $q_{ij}$ 指定为自由二次图。

仅为证明权恒等式，扩标量到含原始十四次单位根 $\zeta$ 的域。代数自同构 $\theta\mapsto\zeta\theta$ 保持二项式关系、窗口 $C$ 和 (190.3)。完整带标签系数源在此作用下等变；$\theta^7$ 为特征向量，所以原归一化分母只引入共同非零标量。图坐标和差分坐标的权为

$$
u_{ij}\mapsto\zeta^{13-i-j}u_{ij},\qquad
z_{ab}\mapsto\zeta^{12-a-b}z_{ab}.
\tag{190.14}
$$

给 $e_a$ 赋权 $6-a$，则 $z_{ab}\leftrightarrow e_a\wedge e_b$ 保持权。由 $\Gamma$ 的内在定义与等变性，其 $e_a\wedge e_b\wedge e_c\wedge e_d$ 分量只能满足

$$
a+b+c+d\equiv11+i+j\pmod {14}.
\tag{190.15}
$$

四个不同指标的和介于 $6$ 与 $14$ 之间。因此

$$
\begin{array}{c|c}
\text{输入}&\Gamma\text{ 的可能支撑}\\ \hline
u_{01}&e_{0345},\ e_{1245}\\
u_{02}&e_{1345}\\
u_{03},\ u_{12}&e_{2345}\\
u_{13},\ u_{23}&0
\end{array}
\tag{190.16}
$$

其中 $e_{abcd}=e_a\wedge e_b\wedge e_c\wedge e_d$，指标递增。这一步只在标量扩张上证明原有理数据的恒等式；忠实扩标量使零等式下降到 $\mathbb Q$。反例的对象始终是 (190.1) 的实际域，并未用分裂代数作见证。

（三）从原函数提取所需六个耦合类。置

$$
x=\theta^7+t\theta+r\theta^2+w\theta^3,\qquad
R_k=\mathsf S^kY-Y(\mathsf S^{\mathsf t})^k.
\tag{190.17}
$$

这里 $t,r,w$ 是标量不定元，$R_k$ 是七阶交错矩阵。由真实乘法块，

$$
\begin{aligned}
H_x&=J_7(I_7+t\mathsf S^6+r\mathsf S^5+w\mathsf S^4),&\det H_x&=-1,\\
H_x^{-1}&=J_7-t\mathsf S^6J_7-r\mathsf S^5J_7-w\mathsf S^4J_7,\\
B_x&=t\mathsf S+r\mathsf S^2+w\mathsf S^3,&R_x&=tR_1+rR_2+wR_3.
\end{aligned}
\tag{190.18}
$$

显示的高次移位之间乘积为零，故逆式是精确式。$\mathcal E(x)$ 的 $t,r,w$ 系数都是同一个原 $S$ 中的函数。其正一次项由完整行列式给出

$$
\operatorname{tr}\bigl((H_x^{-1}B_x-B_x^{\mathsf t}H_x^{-1})U\bigr).
\tag{190.19}
$$

原分母没有一次 $U$ 项。代入 (190.18)，四个系数函数的一次项严格为

$$
\begin{array}{c|c}
\text{原函数}&\text{正一次项}\\ \hline
[t^2]\mathcal E(x)&2u_{01}\\
[tr]\mathcal E(x)&4u_{02}\\
[tw]\mathcal E(x)&4u_{03}\\
[r^2]\mathcal E(x)&2(u_{03}+u_{12})
\end{array}
\tag{190.20}
$$

例如 $\mathsf S^6J_7=E_{00}$，$t^2$ 项的迹矩阵是 $-E_{01}+E_{10}$，与交错 $U$ 配对得 $2u_{01}$；$tr$、$tw$、$r^2$ 的矩阵依次为 $-2E_{02}+2E_{20}$、$-2E_{03}+2E_{30}$、$-E_{03}+E_{30}-E_{12}+E_{21}$，给表中其余常数与符号。这里 $E_{ij}$ 是七阶普通矩阵单位。

还须保留分母的二次修正。对称 $H_x$ 与交错 $R_x$ 的迹配对为零，故 (160.7) 在本族化为

$$
[\mathcal E(x)(0,Y)]_2
=-\operatorname{tr}(H_x^{-1}YD_xY)
-\frac12\operatorname{tr}\bigl((H_x^{-1}R_x)^2\bigr)
+2\operatorname{tr}(J_7YJ_7Y).
\tag{190.21}
$$

最后一项来自同一原分母 $\det(J_7-2YJ_7Y)$，不能省略。$t=r=w=0$ 时，第一项是 $-2\operatorname{tr}(J_7YJ_7Y)$，恰与分母修正抵消。

为核对所取四个系数，记 $A_j=\mathsf S^{6-j}J_7$，$j=0,1,2$。于是

$$
\begin{gathered}
A_0=E_{00},\quad A_1=E_{01}+E_{10},\quad
A_2=E_{02}+E_{11}+E_{20},\\
D_x=2(J_7+tA_0+rA_1+wA_2),\quad
H_x^{-1}=J_7-tA_0-rA_1-wA_2.
\end{gathered}
\tag{190.22}
$$

第一项对 $t^2,tr,tw,r^2$ 的系数分别由 $A_0YA_0Y$、$A_0YA_1Y+A_1YA_0Y$、$A_0YA_2Y+A_2YA_0Y$、$A_1YA_1Y$ 的迹给出。每一项含第零行或第零列的 $Y$ 因子，在 $N$ 上全为零。第二项取这些二参数系数时，只需用 $H_x^{-1}$ 的常数 $J_7$；其余项至少含三个参数。分母修正不含参数。因此四个负二次项经过 $\mu_2$ 后依次为

$$
-\tfrac12\mu_2\operatorname{tr}(J_7R_1J_7R_1),\quad
-\mu_2\operatorname{tr}(J_7R_1J_7R_2),\quad
-\mu_2\operatorname{tr}(J_7R_1J_7R_3),\quad
-\tfrac12\mu_2\operatorname{tr}(J_7R_2J_7R_2).
\tag{190.23}
$$

将 (190.20) 与内在映射 (190.13) 对应，得

$$
\begin{aligned}
\Gamma(u_{01})&=-\tfrac14\mu_2\operatorname{tr}(J_7R_1J_7R_1),\\
\Gamma(u_{02})&=-\tfrac14\mu_2\operatorname{tr}(J_7R_1J_7R_2),\\
\Gamma(u_{03})&=-\tfrac14\mu_2\operatorname{tr}(J_7R_1J_7R_3),\\
\Gamma(u_{03})+\Gamma(u_{12})&=-\tfrac14\mu_2\operatorname{tr}(J_7R_2J_7R_2).
\end{aligned}
\tag{190.24}
$$

这些是已给原源函数的实际系数提取，未自由赋值任何正枢轴二次图。

（四）逐项外乘使六类消失。各 $R_k$ 的第六行、第六列均为零，故

$$
\operatorname{tr}(J_7R_kJ_7R_l)
=\sum_{a,b=1}^5(R_k)_{ab}(R_l)_{6-b,6-a}.
\tag{190.25}
$$

在这些条目中，差分望远镜恒等式为

$$
(R_k)_{ab}=\sum_{j=0}^{k-1}z_{a+k-1-j,b+j}.
\tag{190.26}
$$

越出 $0,\ldots,6$ 的 $Y$ 条目按零延拓，含指标至少 $6$ 的 $z$ 在此切片也按零解释。因此 (190.25) 只含指标至少为 $1$ 的 $z$；特别地，不产生 $e_{0345}$。

对于 (190.16) 剩余允许的四形式分量，(190.25)--(190.26) 给下面的全部相关互异指标单项式；重复外指标的项在 $\mu_2$ 下为零。

$$
\begin{array}{c|c|c|c}
\text{迹}&\text{外分量}&\text{相关二次项}&\mu_2\text{ 的系数}\\ \hline
\operatorname{tr}(J_7R_1J_7R_1)&e_{1245}&4z_{12}z_{45}+4z_{14}z_{25}&4-4\\
\operatorname{tr}(J_7R_1J_7R_2)&e_{1345}&4z_{13}z_{45}+4z_{14}z_{35}&4-4\\
\operatorname{tr}(J_7R_1J_7R_3)&e_{2345}&4z_{24}z_{35}+4z_{25}z_{34}&-4+4\\
\operatorname{tr}(J_7R_2J_7R_2)&e_{2345}&4z_{23}z_{45}+8z_{24}z_{35}+4z_{25}z_{34}&4-8+4
\end{array}
\tag{190.27}
$$

例如 $z_{14}\wedge z_{25}=-e_{1245}$，$z_{24}\wedge z_{35}=-e_{2345}$，$z_{25}\wedge z_{34}=e_{2345}$，固定了表中符号。四行分别消失；与 (190.16)、(190.24) 合起来，得到实际源的六个值

$$
\boxed{\Gamma(u_{01})=\Gamma(u_{02})=\Gamma(u_{03})
=\Gamma(u_{12})=\Gamma(u_{13})=\Gamma(u_{23})=0.}
\tag{190.28}
$$

（五）保留并处理真实 $U_2$。以下 $U_2=U_{2,s}$ 始终由已固定 $s$ 的方程给出。令 $e$ 为新的标量不定元，取 $h_e=T^4+eT$。在 (160.2) 中，

$$
v(e)=v_0+ev_1,\qquad
v_0=(z_{15},-z_{05}-z_{14},z_{04})^{\mathsf t},\quad
v_1=(z_{12},-z_{02},z_{01})^{\mathsf t}.
\tag{190.29}
$$

把这些三元列视为 $\langle1,T,T^2\rangle$ 中的多项式向量，由 (162.5)，(160.3) 中真实 $U_2$ 部分为 $-2U_2(h_ev(e),v(e))$。其 $e^3$ 系数严格为

$$
-2U_2(Tv_1,v_1).
\tag{190.30}
$$

这里 $Tv_1\in\langle T,T^2,T^3\rangle$，故只使用 $0\le i<j\le3$ 的六个 $U_{2,ij}$。每个相应系数都是 $z_{12},-z_{02},z_{01}$ 中两项的乘积。这三个二向量均在 $\bigwedge^2\langle e_0,e_1,e_2\rangle$ 中，任两项外乘为零，所以这些二次系数全在 $K$。同时

$$
\mu_2(U_{2,ij})=-\Gamma(u_{ij})=0\qquad(0\le i<j\le3).
\tag{190.31}
$$

对每个乘积使用原检测器恒等式

$$
\Psi(qr)=\mu_2(q)\wedge\delta(r)+\mu_2(r)\wedge\delta(q)
\tag{190.32}
$$

即得 (190.30) 的检测值为零。这里消去的是这一个贡献在 $\Psi$ 下的像；$U_2$ 本身始终保留，六个二次条目也没有被当作零多项式。

（六）写出其余 Schur 项。核、补分别为 $N_3=\langle1,T,T^2\rangle$、$M_4=\langle T^3,T^4,T^5,T^6\rangle$。$\mathcal H_{h_e}$ 是全局指标 $3,4,5,6$ 的四阶块。令 $J_4$ 为此顺序的四阶反转矩阵，$E^{\mathrm G}_{ij}$ 表示仍按全局指标标注的块内矩阵单位，则

$$
\mathcal H_{h_e}=J_4+eE^{\mathrm G}_{66},\qquad
\mathcal H_{h_e}^{-1}=J_4-eE^{\mathrm G}_{33}.
\tag{190.33}
$$

这里 $E^{\mathrm G}_{33}$ 是全局 $(3,3)$，即局部 $0,1,2,3$ 编号中的 $(0,0)$；它不是局部 $(3,3)$。$R_{h_e}=R_4+eR_1$ 是七阶矩阵，其 $N_3M_4$ 块为 $3\times4$，而

$$
\mathbf w(e)=(R_{h_e})_{N_3M_4}^{\mathsf t}v(e)
\tag{190.34}
$$

是按全局 $3,4,5,6$ 编号的四元列。

为具体展开，临时记

$$
a=z_{12},\quad b=-z_{02},\quad c=z_{01},\qquad
f_0=z_{15},\quad g_0=z_{14}+z_{05},\quad j_0=z_{04}.
\tag{190.35}
$$

从 (190.3)--(190.4) 有 $Y_{13}=z_{03}$、$Y_{14}=j_0$、$Y_{15}=z_{05}$、$Y_{24}=g_0$、$Y_{25}=f_0$、$Y_{34}=z_{24}+f_0$、$Y_{35}=z_{25}$、$Y_{44}=z_{34}+z_{25}$、$Y_{45}=z_{35}$、$Y_{55}=z_{45}$。这些等式直接给出

$$
\begin{aligned}
w_{30}&=f_0(z_{24}+f_0)-g_0z_{25},\\
w_{31}&=a(z_{24}+f_0)+bz_{25}+f_0z_{03}-g_0z_{13}+j_0z_{23},\\
p_3&=az_{03}+bz_{13}+cz_{23},\\
w_{41}&=a(z_{34}+z_{25})+bz_{35}+f_0j_0-g_0z_{14}+j_0z_{24},\\
p_4&=aj_0+bz_{14}+cz_{24},\\
w_{51}&=az_{35}+bz_{45}-f_0z_{14}+j_0z_{25},\\
p_5&=az_{05}+bf_0+cz_{25}.
\end{aligned}
\tag{190.36}
$$

更确切地，$w_3(e)=w_{30}+ew_{31}+e^2p_3$，$w_4(e)=w_{40}+ew_{41}+e^2p_4$，$w_5(e)=w_{50}+ew_{51}+e^2p_5$，而 $w_6(e)=0$；$w_{40},w_{50}$ 的值不参与 $e^3$ 系数。于是

$$
-\mathbf w(e)^{\mathsf t}\mathcal H_{h_e}^{-1}\mathbf w(e)
=-2w_4(e)w_5(e)+ew_3(e)^2.
\tag{190.37}
$$

另一项 $v(e)^{\mathsf t}(YD_{h_e}Y)_{N_3N_3}v(e)$ 中，$D_{h_e}=D_4+2eE_{00}$。因 $YE_{00}Y=0$，它的 $e$ 次数至多为二，不贡献 $e^3$。故在真实 $U_2$ 项以外，(160.3) 的 $e^3$ 系数精确为四次式

$$
\boxed{P=w_{31}^2+2w_{30}p_3-2(w_{41}p_5+p_4w_{51}).}
\tag{190.38}
$$

这里整个四次符号仍来自原完整图和同一分母；没有替换原源。

（七）展开 $P$ 的检测系数。写 $\partial_{ij}=\partial/\partial z_{ij}$，定义六阶 Pfaffian 的三阶微分算子

$$
\begin{aligned}
\mathcal D_{\mathrm{Pf}}={}&
\partial_{01}(\partial_{23}\partial_{45}-\partial_{24}\partial_{35}+\partial_{25}\partial_{34})\\
&-\partial_{02}(\partial_{13}\partial_{45}-\partial_{14}\partial_{35}+\partial_{15}\partial_{34})\\
&+\partial_{03}(\partial_{12}\partial_{45}-\partial_{14}\partial_{25}+\partial_{15}\partial_{24})\\
&-\partial_{04}(\partial_{12}\partial_{35}-\partial_{13}\partial_{25}+\partial_{15}\partial_{23})\\
&+\partial_{05}(\partial_{12}\partial_{34}-\partial_{13}\partial_{24}+\partial_{14}\partial_{23}).
\end{aligned}
\tag{190.39}
$$

由 (154.1) 在四个二向量单项式上的四项展开，逐项有

$$
\mathcal D_{\mathrm{Pf}}(P)=\Omega^{-1}\Psi(P).
\tag{190.40}
$$

偏导自动计入重复因子的重数。给 $z_{ij}$ 赋整数权 $12-i-j$，则 (190.36) 中 $w_{31}$ 权为 $15$，$w_{30},p_3$ 的权为 $12,18$，$w_{41},p_5$ 的权为 $14,16$，$p_4,w_{51}$ 的权为 $17,13$。因此 $P$ 权为 $30$。每个完全匹配的三个偏导总权为 $-21$，输出权为 $9$，只能是 $z_{03},z_{12}$ 的线性组合。

为逐项确定 $z_{03}$ 系数，(190.36) 中含 $z_{03}$ 的部分只有 $w_{31}$ 中的 $f_0z_{03}$ 和 $p_3$ 中的 $az_{03}$。后一项乘 $w_{30}$ 时，余下三个因子不能构成 $0,\ldots,5$ 的完全匹配。前一项在 $w_{31}^2$ 中唯一可用的乘积为

$$
2z_{15}z_{04}z_{23}z_{03}.
\tag{190.41}
$$

其匹配 $(04)(15)(23)$ 的符号为负，故输出为 $-2z_{03}$。

对于输出 $z_{12}$，先列出只含一次 $z_{12}$ 的全部有效单项式。表中“符号”是删去输出因子 $z_{12}$ 后的完全匹配符号，最后一栏已乘上单项式系数。

| 来自的项 | 单项式 | 系数 | 符号 | 对 $z_{12}$ 系数的贡献 |
| --- | --- | --- | --- | --- |
| $w_{31}^2$ | $z_{12}z_{03}z_{15}z_{24}$ | $2$ | $+$ | $2$ |
| $w_{31}^2$ | $z_{12}z_{05}z_{13}z_{24}$ | $-2$ | $-$ | $2$ |
| $w_{31}^2$ | $z_{12}z_{04}z_{15}z_{23}$ | $2$ | $-$ | $-2$ |
| $2w_{30}p_3$ | $z_{12}z_{03}z_{15}z_{24}$ | $2$ | $+$ | $2$ |
| $2w_{30}p_3$ | $z_{12}z_{03}z_{14}z_{25}$ | $-2$ | $-$ | $2$ |
| $-2w_{41}p_5$ | $z_{12}z_{02}z_{15}z_{34}$ | $2$ | $-$ | $-2$ |
| $-2w_{41}p_5$ | $z_{12}z_{01}z_{25}z_{34}$ | $-2$ | $+$ | $-2$ |
| $-2p_4w_{51}$ | $z_{12}z_{02}z_{14}z_{35}$ | $2$ | $+$ | $2$ |
| $-2p_4w_{51}$ | $z_{12}z_{01}z_{24}z_{35}$ | $-2$ | $-$ | $2$ |

还有恰好两项因含两份 $z_{12}$ 而在偏导时多出重数 $2$：

$$
\begin{array}{c|c|c|c}
\text{来源}&\text{单项式及系数}&\text{匹配符号}&\text{贡献}\\ \hline
-2w_{41}p_5&-2z_{12}^2z_{05}z_{34}&+&-4z_{12}\\
-2p_4w_{51}&-2z_{12}^2z_{04}z_{35}&-&+4z_{12}
\end{array}
\tag{190.42}
$$

它们恰好抵消，不能漏掉重数，也不能把它们计入一次因子表。其他单项式删去拟输出因子后有重复指标，不能组成完全匹配。故四个加数的一次因子贡献依次为 $2,4,-4,4$，再加重复项的 $-4+4$，总计为 $6$。结合 (190.41)，得到

$$
\Psi(P)=\Omega\otimes(-2z_{03}+6z_{12}).
\tag{190.43}
$$

（八）回接原 $g_{43}$ 与同一消元。原行列式分子对 $x$ 齐次七次，原分母与 $x$ 无关。因此先在 $u\ne0$ 上有

$$
\mathcal E(u\theta^4+v\theta)=u^7\mathcal E(\theta^4+(v/u)\theta),
\tag{190.44}
$$

两侧都是 $u,v$ 的七次齐次多项式，所以这是原源系数恒等式，进而

$$
g_{43}=[e^3]\mathcal E(\theta^4+e\theta).
\tag{190.45}
$$

定理 160.1 还保证整个 $h_e$ 族在实际纤维中从四次起，所以这些系数函数的实际常数、二次项均为零。同一个已固定 $s$ 的消元映射 $\varphi_s$ 与这些标量系数提取交换，且 $U_s(Y)$ 不依赖 $u,v,e$。所以 (190.45) 的四次项正是步骤（五）--（七）计算的 $e^3$ 系数，使用的分母始终是 $P_{C'}(\theta^7)$。由 (190.30)--(190.32)，真实 $U_2$ 贡献在 $\Psi$ 下为零；由 (190.38)、(190.43)，其余贡献是 $2\Omega\otimes(3z_{12}-z_{03})$。这证明 (190.9) 的第一式。最后 $3z_{12}-z_{03}\in L_6$，故第二式成立。证明没有选择依赖于 $h_e$ 的枢轴；归一化后的任意合法原枢轴均适用。可逆线性归一化不改变原枢轴方程的零纤维，故结论适用于每组原合法枢轴。证毕。

**约定 190.3（来源与新增计算的承担范围）。** 本章是 `repo-derived` 的原源专属综合推导，不作外部文献新颖性或优先权主张。Eisenstein 判据、残数配对、行列式的二阶展开、Schur 补与 Pfaffian 微分仅作为定理 190.2 证明内的工具，不作为新的抽象定理提出。使用的仓内来源为：

| 来源 | 精确复用范围 |
| --- | --- |
| [044，固定版本 74b08723d9c5fb45657df8015bfd47a366f7b199，§§151--166](https://github.com/the-omega-institute/trureturing/blob/74b08723d9c5fb45657df8015bfd47a366f7b199/docs/develop/theory/AURIC_R5_044_RATIONAL_EVALUATOR_QUARTICS_AND_ACTUAL_POSITIVE_PIVOT_CONTROL.md) | 原带符号标签源和同一评估分母；残数图、负坐标、合法枢轴、二次像、$\Psi$ 乘积恒等式及真实 $U_2$ 四次 Schur 公式。尤其使用 (152.4)、(152.6)、(153.2)--(153.3)、(154.2)、(160.3)、(160.7)、(162.5)，以及六方向 $L_6$。 |
| [040，固定版本 f32f2d3b8219fae2014e5db4ab3c31575edf0672，(122.12)、(122.15)--(122.16)](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) | 原源耦合修正、纯负交为 $K$、正投影满射与源提升的对应；这些接口不提供本章六个 $\Gamma$ 值。 |
| [047，固定版本 61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9，§§182--189，尤其 §187](https://github.com/the-omega-institute/trureturing/blob/61ab64d2844eb22ed95cd3c9e7fe6cfa343870b9/docs/develop/theory/AURIC_R5_047_EXACT_QUADRATIC_POWERS_AND_UNIFORM_ACTUAL_FIBRE_CUTOFF.md) | 实际高尾吸收和余切的有限截断，以及次数十四的剩余完整四次像问题；本章不重证高尾吸收，不把它作为新增内容。 |

本章新增的承重计算是：在 (190.1)、(190.3) 的实际模型中，从原函数系数提取并求出 (190.28) 的六个耦合外类；保留真实消元后，具体得到 (190.43) 与全预固定枢轴结论 (190.9)。已知接口只限定这些数值的取得方式，并未预先给出这些数值。

**注记 190.4（反例的量词及剩余数学范围）。** 定理 190.2 给出一组实际域、原窗口和合法负补空间，使每个事先固定的合法原枢轴均有 $C_{43}=0$。因此它反驳对所有这些实际数据断言 $C_{43}\ne0$ 的普遍命题。它没有断言所有十四次域中的 $C_{43}$ 都为零，也没有确定其他负补空间或其他源系数的值。

$C_{43}=0$ 只说明这个特定原系数的检测值落在已知 $L_6$ 中；这里的检测值本身并非零。它不排除同一固定纤维中别的首一四次评估、首一族的其他系数或完整原源提供第七方向。因此 044 的问题 165.3、完整首一族的第七方向目标和 047 的完整实际四次像问题不由本反例解决。本章既未计算整个 $\Psi(J_4(A_s))$，也未把固定纤维结论替换为允许改选枢轴的结论；047 的高尾吸收仍只是所复用的既有结果。

## 追加锚（本行以下为增补区）
