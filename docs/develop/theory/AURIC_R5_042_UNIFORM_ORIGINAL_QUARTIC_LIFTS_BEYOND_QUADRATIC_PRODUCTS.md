# 原连续幂系数纤维中超出二次乘积的统一四次提升

## 132. 原系数、完成环与全次数输入

**定义 132.1（同一个原域中的系数代数）。** 设 $F$ 为特征零域，$D/F$ 为次数 $2m$ 的可分域扩张，$m\ge7$。固定任一本原元 $\theta$、其首一最小多项式 $f(T)$，以及非零体积形式 $\nu:\det_FD\to F$。置

$$
C=\langle1,\theta,\ldots,\theta^{m-1}\rangle_F,
\qquad d=m-4,
\qquad V=F[T]_{\le m-2},
\qquad W=\bigwedge^2V.
\tag{132.1}
$$

对变化中的实际 $m$ 维子空间 $C'\subset D$ 及其包含帧 $E_{C'}$，定义

$$
P_{C'}(x)=\nu\bigl(\det[E_{C'},M_xE_{C'}]\bigr),
\tag{132.2}
$$

其中 $M_x$ 是同一个 $D$ 中的乘法。换帧只把多项式乘以一个公共非零平方，故其射影系数点 $[P_{C'}]$ 定义良好。取有限 Galois 分裂域 $L/F$，根集为 $\Lambda$，保留原嵌入标签。在固定根序下，原带符号系数为

$$
P_{C'}(x)=\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}x_\lambda,
\qquad
c_I=\alpha\epsilon_Ip_Ip_{I^c}.
\tag{132.3}
$$

这里 $p_I$ 是实际包含帧的最大行子式，$\epsilon_I$ 是互补行序符号，$\alpha$ 来自同一个体积形式。令 $U$ 为全部 $p_I\ne0$ 的统一开集。连续幂窗口 $C$ 在此开集中，因为所有相应行列式均为非零 Vandermonde 行列式。

沿用 [039，定义 111.1、命题 111.2、定理 113.1](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 的原系数像环 $S_F$、光滑几何商

$$
X_D=U/T_D,
\qquad T_D=(\operatorname{Res}_{D/F}\mathbb G_m)/\mathbb G_m,
\qquad B_F=\mathcal O(X_D)^\iota.
\tag{132.4}
$$

$T_D$ 按原域乘法作用，$\iota$ 为迹正交补诱导的 Gale 对合，$B_F$ 是 $S_F$ 的有限双有理正规化。$S_F\otimes_FL$ 是原带标签比值 $(c_I/c_{I_0})^{\pm1}$ 的像代数，而非全部抽象不变量的替代定义。

**定义 132.2（源余切与正规化余切）。** 令 $p=[P_C]$，令 $y$ 为其唯一正规化点，置

$$
S=(S_F)_p,
\quad B=(B_F)_y,
\quad \mathscr T=\widehat S,
\quad \mathscr B=\widehat B,
\quad
J:\mathfrak m_S/\mathfrak m_S^2
\longrightarrow\mathfrak m_B/\mathfrak m_B^2.
\tag{132.5}
$$

完成取指定极大理想拓扑，两个剩余域均为 $F$。039 的有限正规化及固定点形式模型给出原 $F$ 上的单射 $\mathscr T\hookrightarrow\mathscr B$。记

$$
a=\frac{m(m-1)}2,
\qquad b=\dim_FW=\frac{(m-1)(m-2)}2,
\qquad Q_2=\operatorname{Sym}^2W,
$$

$$
w:Q_2\longrightarrow\bigwedge^4V,
\qquad w(\xi\zeta)=\xi\wedge\zeta,
\qquad K=\ker w.
\tag{132.6}
$$

对称代数乘积写作 $\xi\zeta$，外积写作 $\xi\wedge\zeta$，二者在全文中区分。

**约定 132.3（复用的完整耦合像）。** 在原域对合相容横截面上，设 $P$ 为正切空间，负余切为 $W$。复用 [040，定理 122.1 的 (122.8)、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md) 的全 $m\ge5$ 结论：

$$
\mathfrak m_B/\mathfrak m_B^2=P^\vee\oplus Q_2,
\qquad M=\operatorname{im}J,
$$

$$
M\cap(0\oplus Q_2)=0\oplus K,
\qquad \operatorname{pr}_{P^\vee}M=P^\vee,
\qquad \dim_FP=a.
\tag{132.7}
$$

这是同一个余切空间中的交、投影与耦合关系。它给

$$
\operatorname{rank}J=a+\dim K,
\qquad
\dim K=\frac{b(b+1)}2-\binom{m-1}{4}.
\tag{132.8}
$$

本文所用的既有输入是 (132.4)、固定点形式模型与 (132.7)，而不是关于低维完整纤维的环等式。

## 133. 残数迹帧与实际乘法商的负坐标

**定义 133.1（实际双曲帧及线性坐标）。** 定义

$$
\ell(x)=\operatorname{Tr}_{D/F}\bigl(x/f'(\theta)\bigr),
\qquad \langle x,z\rangle=\ell(xz).
\tag{133.1}
$$

可分性保证 $f'(\theta)\ne0$，故此配对非退化。对次数不超过 $2m-1$ 的多项式，在全部根处作 Lagrange 插值并比较最高次系数，得到

$$
\ell(\theta^j)=0\quad(0\le j\le2m-2),
\qquad \ell(\theta^{2m-1})=1.
\tag{133.2}
$$

因此 $C$ 最大各向同性。固定幂帧 $E=(1,\theta,\ldots,\theta^{m-1})$，选原 $F$ 上的各向同性对偶补帧 $E'$，使配对在 $[E,E']$ 中为 $\left(\begin{smallmatrix}0&I\\I&0\end{smallmatrix}\right)$。其存在性可直接实现：先取任意对偶补帧 $E'_0$，若其 Gram 矩阵为 $G$，则 $E'=E'_0-EG/2$ 满足要求。

邻近窗口写为 $C_Z=\operatorname{col}(E+E'Z)$。分解

$$
Z=U+Y,
\qquad U^{\mathsf T}=-U,
\qquad Y^{\mathsf T}=Y.
\tag{133.3}
$$

相对于 (133.1) 的正交补严格给 $Z\mapsto-Z^{\mathsf T}$。它与迹正交补只差固定乘数 $1/f'(\theta)$，所以在实际乘法商上就是 $\iota$，作用为 $(U,Y)\mapsto(U,-Y)$。

环面的无穷小乘法 $t\in D$ 给对称矩阵

$$
Y_t(\theta^i,\theta^j)=\ell(t\theta^{i+j}).
\tag{133.4}
$$

这些矩阵恰好组成全部 Hankel 矩阵空间 $\mathcal O$。确实，$1,\theta,\ldots,\theta^{2m-2}$ 独立，非退化配对使这 $2m-1$ 个矩任意，故 (133.4) 的秩为 $2m-1$；其核是标量方向。固定任意原 $F$ 线性补空间

$$
\operatorname{SymMat}_m(F)=\mathcal O\oplus N.
\tag{133.5}
$$

在 (133.3) 中令 $Y\in N$。实际横截面到 $X_D$ 的切映射为

$$
\operatorname{AltMat}_m\oplus N
\longrightarrow
(\operatorname{AltMat}_m\oplus\operatorname{SymMat}_m)/\mathcal O,
\tag{133.6}
$$

是同构。源与目标均光滑、剩余域均为 $F$，故形式逆函数定理给完成局部环同构；这正是 [039，定理 117.1](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md) 的实际横截面。于是

$$
\mathscr R=F[[U,Y]],
\qquad \mathscr B=\mathscr R^{\iota},
\qquad \iota(U,Y)=(U,-Y).
\tag{133.7}
$$

这里坐标来自实际商映射的形式逆，没有把商替换成另一族矩阵。

令 $e_i=T^i\in V$，定义线性函数

$$
z_{ij}(Y)=Y(\theta^{i+1},\theta^j)-Y(\theta^i,\theta^{j+1}),
\quad 0\le i,j\le m-2,
\quad z_{ji}=-z_{ij}.
\tag{133.8}
$$

每个 $z_{ij}$ 消去 $\mathcal O$。更精确地，映射

$$
e_i\wedge e_j\longmapsto
\theta^{i+1}\odot\theta^j-\theta^i\odot\theta^{j+1}
\tag{133.9}
$$

给出 $W\simeq\ker(\operatorname{Sym}^2C\to D)=N^\vee$。理由是：以平均对称化表示对称张量，右侧对应

$$
\frac{(s-t)(s^it^j-s^jt^i)}2.
\tag{133.10}
$$

这些多项式线性独立，且乘法像为 $\langle1,\theta,\ldots,\theta^{2m-2}\rangle$，故核的维数恰为 $b$。与 $Y$ 配对正好得到 (133.8)。以下严格约定 $e_i\wedge e_j\leftrightarrow z_{ij}$。它与 039 的 $(s-t)A(s,t)$ 识别相差的至多是公共非零标量，故 (132.7) 中的外乘核 $K$ 保持相同；所有具体检测值均采用 (133.8) 的归一化。

## 134. 任意实际正枢轴及其二次消元桥

**定义 134.1（实际形式纤维与四次符号）。** 一组合法实际正系数枢轴是 $s_1,\ldots,s_a\in\mathfrak m_S$，满足

$$
J[s_i]=(\ell_i,q_i)\in M,
\qquad \ell_1,\ldots,\ell_a\text{ 为 }P^\vee\text{ 的一组基}.
\tag{134.1}
$$

这里“正”指对合的正特征方向，不要求 $F$ 带序。所有枢轴均为原 $F$ 上的实际系数局部函数。它们存在，因为 (132.7) 在 $F$ 上给出满射 $M\to P^\vee$，可直接选择基的源提升。单个分裂根标签函数不自动具有此原域性质。

固定任意这样一组枢轴，定义

$$
B_{0,s}=\mathscr B/(s_1,\ldots,s_a)\mathscr B,
\quad
\mathfrak L_s=\ker(\mathscr T\to B_{0,s}),
\quad
A_{0,s}=\operatorname{im}(\mathscr T\to B_{0,s})
         =\mathscr T/\mathfrak L_s.
\tag{134.2}
$$

因此仅有 $(s)\mathscr T\subseteq\mathfrak L_s$ 自动成立。$A_{0,s}$ 的定义始终使用实际像。

记 $L(U)=(\ell_i(U))_i$，$q_s=(q_i)_i$。在光滑覆盖中，实际方程 $s(U,Y)=0$ 唯一解为

$$
U=\phi_s(Y),
\qquad \phi_s(-Y)=\phi_s(Y),
\qquad \phi_s(Y)=O(Y^2),
\qquad (\phi_s)_2=-L^{-1}q_s.
\tag{134.3}
$$

事实上 $s=L(U)+q_s(Y)+r_s$，其中 $r_s\in\mathfrak m_{\mathscr B}^2$；$L$ 可逆给形式隐函数定理，偶性来自唯一性和 $s(U,-Y)=s(U,Y)$。等变坐标变换 $(U,Y)\mapsto(s,Y)$ 在形式幂级数环上可逆。对二阶群取平均，并在这组坐标中取商，得到真正的正规化形式纤维

$$
B_{0,s}\simeq F[[Y]]^{Y\mapsto-Y}.
\tag{134.4}
$$

以下在覆盖 $F[[Y]]$ 中记 $\mathfrak q=(Y)$，$O(Y^r)$ 表示属于 $\mathfrak q^r$，并置

$$
\operatorname{in}_2(A_{0,s})
=\{\text{零常数像元素的二次齐次项}\}\subseteq Q_2,
$$

$$
J_4(A_{0,s})
=\operatorname{im}\left(A_{0,s}\cap\mathfrak q^4
\longrightarrow\mathfrak q^4/\mathfrak q^6\right)
\subseteq\operatorname{Sym}^4W,
\qquad P_4=\mu(\operatorname{Sym}^2K).
\tag{134.5}
$$

因所有元素均为偶函数，最后的符号商只有四次部分。$\mu$ 为对称代数乘法。$A_{0,s}$ 是完整 Noetherian 局部环 $\mathscr T$ 的商；其极大理想由零常数元素构成。

**引理 134.2（全次数实际二次桥）。** 对每个满足 (134.1) 的实际枢轴，有

$$
\operatorname{in}_2(A_{0,s})=K,
\qquad P_4\subseteq J_4(A_{0,s}).
\tag{134.6}
$$

证明。设一个源函数在正规化余切中的类为 $(\ell,q)\in M$。将 (134.3) 代入，它的二次符号精确为

$$
R_s(\ell,q)=q-\ell L^{-1}q_s.
\tag{134.7}
$$

$\mathfrak m_{\mathscr B}$ 限制到纤维后至少二阶，故其平方至少四阶；这证明 (134.7) 包含全部二次贡献。令 $H_s$ 为枢轴余切类的张成，由 (132.7) 和正投影独立性，

$$
M=H_s\oplus(0\oplus K).
\tag{134.8}
$$

映射 $R_s$ 在 $H_s$ 上为零，在 $0\oplus K$ 上为恒等。因此 $R_s(M)=K$。完成化不改变源的有限维余切空间，源极大理想平方又只贡献四次及更高项，所以这正好给全部实际二次像。每个 $k\in K$ 都有源函数提升，将两个这样的提升相乘，其四次符号就是两个二次符号的乘积，得到第二个包含。证毕。

## 135. 原评价函数在完整图中的四阶消失

**定义 135.1（带原单位分母的评价）。** 对 $H\in F[T]$，置

$$
\mathcal E_H(C')=
\frac{P_{C'}(H(\theta))}{P_{C'}(\theta^m)}.
\tag{135.1}
$$

分母在 $C$ 处是非零幂基体积

$$
\nu(1\wedge\theta\wedge\cdots\wedge\theta^{2m-1}).
\tag{135.2}
$$

分子分母都是原系数空间上的 $F$ 线性评价泛函，故 (135.1) 属于 $S$。在分裂域中，其精确表达式为

$$
\mathcal E_H=
\frac{\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}H(\lambda)}
{\sum_{|I|=m}c_I(C')\prod_{\lambda\in I}\lambda^m}.
\tag{135.3}
$$

全部原符号、原标签及分母均保留。换帧与换体积的公共因子在比值中消去。原乘法 $C'\mapsto tC'$ 使两项同乘 $\operatorname{Norm}_{D/F}(t)$，故它下降到实际乘法商；又因来自 $S$，其拉回为 Gale 不变函数。这给出原 $F$ 下降，无须把单个分裂标签函数当作原域函数。

**命题 135.2（余秩四的实际评价首项）。** 设 $H$ 次数为 $d=m-4$，最高项系数 $a_H$ 为单位；系数也允许属于一个外部形式参数环。则 $\mathcal E_H$ 在全部 Grassmann 图变量 $Z$ 中属于 $(Z)^4$，因而在实际横截面中属于 $(U,Y)^4$。对每组实际枢轴，

$$
\mathcal E_H|_{B_{0,s}}
=a_H^d\operatorname{Pf}(\rho_H(Y))^2+O(Y^6),
$$

$$
\rho_H(Y)(u,v)=Y(Hu,v)-Y(u,Hv),
\qquad u,v\in R_4:=\langle1,T,T^2,T^3\rangle_F.
\tag{135.4}
$$

证明。实际乘法 $M_H=M_{H(\theta)}$ 对 (133.1) 自伴随，在双曲帧中写成

$$
M_H=\begin{pmatrix}B_H^{\mathsf T}&D_H\\H_H&B_H\end{pmatrix},
\qquad H_H^{\mathsf T}=H_H,
\quad D_H^{\mathsf T}=D_H.
\tag{135.5}
$$

实际帧矩阵满足

$$
[E+E'Z,M_H(E+E'Z)]
=[E,E']\begin{pmatrix}I&B_H^{\mathsf T}+D_HZ\\Z&H_H+B_HZ\end{pmatrix}.
$$

从右块列减去左块列乘 $B_H^{\mathsf T}+D_HZ$，不交换行列，得精确恒等式

$$
L_H(Z)=H_H+B_HZ-ZB_H^{\mathsf T}-ZD_HZ,
\qquad
\mathcal E_H(C_Z)=\frac{\det L_H(Z)}{\det L_{T^m}(Z)}.
\tag{135.6}
$$

这始终是同一个域的乘法块。由 (133.2)，

$$
(H_H)_{ij}=\ell(H(\theta)\theta^{i+j}),
\qquad0\le i,j\le m-1.
\tag{135.7}
$$

当行指标或列指标不超过 $3$ 时，条目为零。余下指标 $4\le i,j\le m-1$ 给 $d\times d$ 块 $H'_H$，满足

$$
(H'_H)_{ij}=0\quad(i+j<m+3),
\qquad (H'_H)_{ij}=a_H\quad(i+j=m+3).
\tag{135.8}
$$

因此

$$
\ker H_H=R_4,
\qquad \det H'_H=(-1)^{d(d-1)/2}a_H^d,
\qquad \det H_{T^m}=(-1)^{m(m-1)/2}.
\tag{135.9}
$$

这里 (135.8) 只是反三角零区加固定反对角线。反转列后得到三角矩阵，才给出 (135.9)；另一侧条目由高次残数矩决定，无须为零。两个符号的比值为 $1$，因为

$$
\frac{m(m-1)-d(d-1)}2=4m-10
\tag{135.10}
$$

为偶数。

按 $R_4\oplus\langle T^4,\ldots,T^{m-1}\rangle$ 对 $L_H$ 分块。非核块在原点可逆，其余三个块常数项均为零。Schur 补的核块为一次核块加至少二阶项；交叉块相乘的校正从二阶开始。因此整个分子至少四阶，四次部分等于 $\det H'_H$ 乘一次核块的四阶行列式。分母是完整图上的单位，不改变这个消失阶数。

对 $u,v\in R_4$，$Hu,Hv\in C$，故 $B_H^{\mathsf T}u$ 就是 $Hu$ 的幂基坐标。由 (135.6)，一次核块在对称方向上准确为

$$
u^{\mathsf T}(B_HY-YB_H^{\mathsf T})v
=Y(Hu,v)-Y(u,Hv).
\tag{135.11}
$$

它斜对称，且添加任一 Hankel 形式 $Y_t$ 后，两项同为 $\ell(tHuv)$ 而消去。因此 $\rho_H$ 只依赖实际负商方向。

现在限制到实际方程 $U=\phi_s(Y)=O(Y^2)$。一个在完整图中已经至少四阶的函数，其四次符号只使用输入的一次部分；含一个 $U$ 的单项式经此替换后至少五阶。等价地，在四维核行列式中以任一二阶修正替换一次因子，总次数即至少为五。这同时处理正向消元、非核块变化和 Schur 混合校正。结合 (135.9)--(135.10)，四次项为 $a_H^d\det\rho_H$。四维斜对称行列式为

$$
\det\rho_H=
(\rho_{01}\rho_{23}-\rho_{02}\rho_{13}+\rho_{03}\rho_{12})^2.
\tag{135.12}
$$

这是标准四指标 Pfaffian 恒等式，符号与 Knuth 的 *Overlapping Pfaffians*，§0，(0.2) 一致。原函数与实际纤维都保持 $Y\mapsto-Y$，故五次项为零，余项从六次开始。证毕。

## 136. 最高项变化时的单位校正与明确四次式

**定义 136.1（原评价的校正系数族）。** 对任意 $h\in F[T]_{\le d}$，记 $h_d=[T^d]h$，定义同一个 $S$ 中的元素

$$
G_h=[u^4]\bigl((1+uh_d)^{-d}\mathcal E_{T^d+uh}\bigr).
\tag{136.1}
$$

参数 $u$ 仅用于有限系数提取。展开单位的前五项即可得到

$$
G_h=\sum_{j=0}^4(-1)^{4-j}
\binom{d+3-j}{4-j}h_d^{4-j}
[u^j]\mathcal E_{T^d+uh}.
\tag{136.2}
$$

所以 $G_h$ 是原系数局部函数的有限 $F$ 线性组合，唯一的窗口分母仍为 (135.2) 的评价单位。若 $h$ 还含外部多项式参数，(136.2) 仍给参数多项式的有限系数，不引入域扩张或新的窗口分母。

为写明四次式，在 $V$ 中置

$$
\alpha=e_0,\quad\beta=e_1,\quad\gamma=e_2,
\qquad a_h=h,\quad b_h=Th,\quad c_h=T^2h.
\tag{136.3}
$$

下列外积均视为 $W=N^\vee$ 中的线性函数：

$$
\begin{array}{lll}
\beta_{01}=\alpha\wedge a_h,&
\beta_{02}=\alpha\wedge b_h+\beta\wedge a_h,&
\beta_{03}=\alpha\wedge c_h+\beta\wedge b_h+\gamma\wedge a_h,\\
\beta_{12}=\beta\wedge b_h,&
\beta_{13}=\beta\wedge c_h+\gamma\wedge b_h,&
\beta_{23}=\gamma\wedge c_h.
\end{array}
\tag{136.4}
$$

定义

$$
p(h)=\beta_{01}\beta_{23}-\beta_{02}\beta_{13}
      +\beta_{03}\beta_{12}\in Q_2.
\tag{136.5}
$$

**命题 136.2（原域校正族的共同符号）。** 每个 $G_h$ 在完整图中至少四阶消失，且对每组合法实际枢轴，

$$
G_h|_{B_{0,s}}=p(h)^2+O(Y^6).
\tag{136.6}
$$

证明。$H=T^d+uh$ 在 $F[[u]]$ 上的最高项系数为单位 $1+uh_d$。命题 135.2 给

$$
(1+uh_d)^{-d}\mathcal E_{T^d+uh}|_{B_{0,s}}
=\operatorname{Pf}(\rho_{T^d}+u\rho_h)^2+O(Y^6).
\tag{136.7}
$$

Pfaffian 对矩阵条目二次齐次，故右边的 $u^4$ 系数为 $\operatorname{Pf}(\rho_h)^2$。单位校正恰好消去非核块行列式的 $(1+uh_d)^d$ 因子；当最高项随参数变化时，此因子必须保留到这一步。

为核对 $\operatorname{Pf}(\rho_h)=p(h)$，对 $h=T^r$ 逐项望远镜相消：

$$
Y(\theta^{i+r},\theta^j)-Y(\theta^i,\theta^{j+r})
=\sum_{k=0}^{r-1}z_{i+k,j+r-1-k}.
\tag{136.8}
$$

再用 $z_{ji}=-z_{ij}$，在 $R_4$ 的基 $1,T,T^2,T^3$ 上得到恰好 (136.4) 的六个条目。$r=0$ 时两侧均为零，线性性给任意 $h$。所有所用指标不超过 $d+2=m-2$。因此 (136.7) 的 $u^4$ 系数就是 (136.6)。命题 135.2 在提取前已给完整图四阶消失；有限系数提取仍保持这一性质。证毕。

## 137. 消去全部可见二次乘积的外积检测

**定义 137.1（有确定类型的检测器）。** 定义

$$
\Psi:\operatorname{Sym}^4W\longrightarrow\bigwedge^6V\otimes W
$$

在 $a,b,c,d\in W=\bigwedge^2V$ 的乘积上为

$$
\begin{aligned}
\Psi(abcd)={}&(a\wedge b\wedge c)\otimes d
+(a\wedge b\wedge d)\otimes c\\
&+(a\wedge c\wedge d)\otimes b
+(b\wedge c\wedge d)\otimes a.
\end{aligned}
\tag{137.1}
$$

二向量彼此外积交换，所以此式对四个变量对称，确实在对称幂上良定义。令

$$
\delta:Q_2\longrightarrow W\otimes W,
\qquad\delta(ab)=a\otimes b+b\otimes a,
$$

$$
\omega\wedge(x\otimes y):=(\omega\wedge x)\otimes y,
\qquad \omega\in\bigwedge^4V,\quad x,y\in W.
\tag{137.2}
$$

对 $q,r\in Q_2$，将 $q=ab,r=cd$ 的四项按保留因子分组，再线性延拓，得有确定类型的极化恒等式

$$
\Psi(qr)=w(q)\wedge\delta(r)+w(r)\wedge\delta(q).
\tag{137.3}
$$

因此 $\Psi(P_4)=0$。此结论使用 $q,r\in K$ 的外乘为零；对任意二向量的平方并无同样断言。

**命题 137.2（原评价四次式的精确检测值）。** 以 (136.3) 定义

$$
\Omega(h)=\alpha\wedge\beta\wedge\gamma\wedge a_h\wedge b_h\wedge c_h,
\qquad
\eta(h)=2\beta\wedge b_h-\alpha\wedge c_h-\gamma\wedge a_h.
\tag{137.4}
$$

则

$$
\boxed{\Psi(p(h)^2)=2\Omega(h)\otimes\eta(h).}
\tag{137.5}
$$

证明。将 (136.5) 的三个乘积改取外积，消去重复向量项，得到

$$
\begin{aligned}
w(p(h))={}&-\alpha\wedge\gamma\wedge a_h\wedge c_h\\
&+2\alpha\wedge\beta\wedge b_h\wedge c_h
+2\beta\wedge\gamma\wedge a_h\wedge b_h.
\end{aligned}
\tag{137.6}
$$

例如首项来自 $(\alpha\wedge a_h)(\gamma\wedge c_h)$；第二项分别从 $-(\alpha\wedge b_h)(\beta\wedge c_h)$ 与 $(\alpha\wedge c_h)(\beta\wedge b_h)$ 各得一份，第三项同理。再分别与六个条目外乘，有

$$
\begin{aligned}
w(p(h))\wedge\beta_{03}&=3\Omega(h),\\
w(p(h))\wedge\beta_{12}&=-\Omega(h),\\
w(p(h))\wedge\beta_{ij}&=0\quad(ij=01,02,13,23).
\end{aligned}
\tag{137.7}
$$

在第一行中，$\alpha\wedge c_h,\beta\wedge b_h,\gamma\wedge a_h$ 的贡献依次为 $2\Omega(h),-\Omega(h),2\Omega(h)$，从而固定全部符号。由 (137.3)，

$$
\Psi(p(h)^2)
=2w(p(h))\wedge\delta(p(h))
=2\Omega(h)\otimes(3\beta_{12}-\beta_{03}),
$$

正是 (137.5)。这些是任意六个向量的外代数恒等式，向量重合时仍成立。证毕。

## 138. 共同四次子空间与统一下界

**定义 138.1（展示函数与展示符号）。** 对 $j=1,2$，定义原函数及四次式

$$
A_j=[t]G_{T^3+tT^j},
\qquad a_j^{(4)}=[t]p(T^3+tT^j)^2.
\tag{138.1}
$$

若 $d=3$，再置 $A_3=G_{T^3}$、$a_3^{(4)}=p(T^3)^2$，令

$$
E_m=\langle a_1^{(4)},a_2^{(4)},a_3^{(4)}\rangle_F.
\tag{138.2}
$$

若 $d\ge4$，对 $3\le r\le d-1$、$0\le k\le4$，置

$$
B_{r,k}=[t^k]G_{T^r+tT^{r+1}},
\qquad b_{r,k}^{(4)}=[t^k]p(T^r+tT^{r+1})^2,
\tag{138.3}
$$

并令

$$
E_m=\operatorname{span}_F\left(
\{a_1^{(4)},a_2^{(4)}\}
\cup\{b_{r,k}^{(4)}:3\le r\le d-1,\ 0\le k\le3\}
\cup\{b_{d-1,4}^{(4)}\}\right).
\tag{138.4}
$$

式 (136.2)、(136.4)--(136.5) 将每个函数与每个符号都写成有限明确表达式。所有函数均在原 $S$ 中；包括 $r=d-1$ 的边界在内，最高项变化由 (136.1) 的单位校正处理。

**定理 138.2（每个实际正纤维中的统一非乘积四次提升）。** 对定义 132.1 的每个 $F,D,\theta,m$，以及定义 134.1 的每组实际原 $F$ 正系数枢轴，均有

$$
\operatorname{in}_2(A_{0,s})=K,
\qquad P_4\oplus E_m\subseteq J_4(A_{0,s}),
\qquad \dim_FE_m=4m-25.
\tag{138.5}
$$

因此

$$
\boxed{\dim_F(J_4(A_{0,s})/P_4)\ge4m-25>0.}
\tag{138.6}
$$

比较不同枢轴时使用 (133.8)--(133.9) 的同一个连续幂负余切识别。共同子空间 $E_m$ 由 (138.1)--(138.4) 展示，其符号不随这些枢轴改变。

证明。引理 134.2 给二次像和 $P_4$ 的包含，命题 136.2 给每个展示函数的共同四次符号。只需证明展示符号模 $P_4$ 的独立性。

记

$$
\Omega_3=e_0\wedge e_1\wedge e_2\wedge e_3\wedge e_4\wedge e_5,
\qquad
\eta_r=2e_1\wedge e_{r+1}-e_0\wedge e_{r+2}-e_2\wedge e_r.
\tag{138.7}
$$

特别地，

$$
\eta_1=3z_{12}-z_{03},
\quad \eta_2=2z_{13}-z_{04},
\quad \eta_3=2z_{14}-z_{05}-z_{23}.
\tag{138.8}
$$

对 $h=T^3+tT^j$、$j=1,2$，在模掉 $e_0,e_1,e_2$ 后，$h,Th,T^2h$ 是对角线全一的三角列变换，故

$$
\Omega(T^3+tT^j)=\Omega_3,
\qquad
\Psi(a_j^{(4)})=2\Omega_3\otimes\eta_j\ne0.
\tag{138.9}
$$

当 $d=3$ 时，第三个值为 $\Psi(a_3^{(4)})=2\Omega_3\otimes\eta_3\ne0$。

当 $d\ge4$ 时，记 $e_{012}=e_0\wedge e_1\wedge e_2$，对 $3\le r\le d-1$ 置

$$
\begin{aligned}
\Omega_{r,0}&=e_{012}\wedge e_r\wedge e_{r+1}\wedge e_{r+2},\\
\Omega_{r,1}&=e_{012}\wedge e_r\wedge e_{r+1}\wedge e_{r+3},\\
\Omega_{r,2}&=e_{012}\wedge e_r\wedge e_{r+2}\wedge e_{r+3},\\
\Omega_{r,3}&=e_{012}\wedge e_{r+1}\wedge e_{r+2}\wedge e_{r+3}.
\end{aligned}
\tag{138.10}
$$

这是四个不同的非零外幂基元，且 $r+3\le m-2$。将三个因子直接展开，得

$$
\Omega(T^r+tT^{r+1})=\sum_{j=0}^3t^j\Omega_{r,j},
\qquad \eta(T^r+tT^{r+1})=\eta_r+t\eta_{r+1}.
\tag{138.11}
$$

所以全部检测值准确为

$$
\begin{aligned}
\Psi(b_{r,0}^{(4)})&=2\Omega_{r,0}\otimes\eta_r,\\
\Psi(b_{r,k}^{(4)})&=2(\Omega_{r,k}\otimes\eta_r
+\Omega_{r,k-1}\otimes\eta_{r+1})\quad(1\le k\le3),\\
\Psi(b_{r,4}^{(4)})&=2\Omega_{r,3}\otimes\eta_{r+1}.
\end{aligned}
\tag{138.12}
$$

$\eta_r,\eta_{r+1}$ 非零，内侧两项有不同的第一张量基元，端点是非零纯张量，因此 (138.12) 的每一个值都非零。

在环境向量空间中赋辅助权 $\operatorname{wt}(e_i)=i$，在外幂、对称幂和张量积上相加。$p(T^r+tT^{r+1})$ 中每个 $t^k$ 系数的权为 $2r+4+k$，所以 $b_{r,k}^{(4)}$ 及其检测像的权均为

$$
4r+8+k.
\tag{138.13}
$$

同样，$a_1^{(4)},a_2^{(4)}$ 的检测权分别为 $18,19$。当 $d=3$ 时第三个权为 $20$。当 $d\ge4$ 时，(138.4) 所选检测像的权依次为

$$
18,19,20,\ldots,4d+8.
\tag{138.14}
$$

它们两两不同，共 $4d-9=4m-25$ 个，故这些非零检测像线性独立。权仅是环境张量空间的分次，不要求原系数映射或实际消元具有群等变性。由于 $\Psi(P_4)=0$，展示符号模 $P_4$ 线性独立，其本身也独立，且其张成与 $P_4$ 的交为零。全部展示函数在完整图中至少四阶消失，故相同符号对每组合法枢轴成立。证毕。

## 139. 原系数余切核的关系提升及嵌入维数

**定理 139.1（实际关系提升的源与像）。** 对每组实际枢轴，有良定义的原 $F$ 线性满射

$$
\overline\lambda_s:\ker J\longrightarrow J_4(A_{0,s})/P_4,
\qquad
[g]\longmapsto[\operatorname{in}_4(g|_{B_{0,s}})].
\tag{139.1}
$$

每个展示函数的源余切类属于 $\ker J$，其像为对应的展示符号类。因此

$$
\dim_F\ker J\ge4m-25,
\tag{139.2}
$$

$$
\operatorname{edim}S\ge
a+\frac{b(b+1)}2-\binom{m-1}{4}+4m-25,
\tag{139.3}
$$

$$
\operatorname{edim}A_{0,s}\ge
\frac{b(b+1)}2-\binom{m-1}{4}+4m-25.
\tag{139.4}
$$

这里 $\ker J$ 是原系数余切映射的源核；(132.8) 中外四次空间计算的是同一映射的余核，两者不同。

证明。若 $[g]\in\ker J$，则 $g$ 在 $\mathscr B$ 中属于 $\mathfrak m_{\mathscr B}^2$。纤维映射将 $\mathfrak m_{\mathscr B}$ 送入 $(Y)^2$，故 $g|_{B_{0,s}}$ 至少四阶。若更换源代表，差属于 $\mathfrak m_S^2$；它在纤维上的四次符号是实际二次符号的乘积之和，由引理 134.2 属于 $P_4$。因此 (139.1) 良定义且线性。

反之，任取 $h_0\in A_{0,s}\cap(Y)^4$，在 $\mathscr T$ 中取零常数提升 $g$，写 $J[g]=(\ell,q)$。纤维二次项为零，故由 (134.7)，$q-\ell L^{-1}q_s=0$。令常系数行向量 $c=\ell L^{-1}$，并置

$$
g'=g-\sum_i c_i s_i.
\tag{139.5}
$$

则 $J[g']=0$，而 $g'|_{B_{0,s}}=h_0$。完成化不改变源余切空间，可以把 $[g']$ 视为 $\mathfrak m_S/\mathfrak m_S^2$ 中的类。故 (139.1) 满射。

每个展示函数在完整图中至少四阶消失，并且对合不变。在 $\mathfrak m_{\mathscr B}/\mathfrak m_{\mathscr B}^2$ 中只保留一次 $U$ 与纯二次 $Y$；二者均为零，所以其源类属于 $\ker J$。由定理 138.2，这些类在 (139.1) 下有 $4m-25$ 个独立像，给 (139.2)。再用 (132.8) 的秩与有限维线性映射的秩核公式，得到 (139.3)。

最后取 $K$ 的一组基，在 $A_{0,s}$ 中取实际二次提升。若这些提升与展示函数在 $\mathfrak m_{A_{0,s}}/\mathfrak m_{A_{0,s}}^2$ 中有线性关系，先取二次符号，$K$ 的基独立性迫使全部二次提升系数为零。剩下的展示函数组合若属于极大理想平方，其四次符号必为 $K$ 中元素两两乘积之和，即属于 $P_4$；定理 138.2 又迫使其余系数全零。故源纤维余切中至少有 $\dim K+4m-25$ 个独立类，得到 (139.4)。证毕。

## 140. 十四次原域中的三个明确方向

**命题 140.1（端点 $m=7$）。** 当 $m=7$ 时，对每个题设域、本原元及每组合法实际枢轴，可直接取三个原函数

$$
F_1=[t]\mathcal E_{T^3+tT},
\qquad F_2=[t]\mathcal E_{T^3+tT^2},
\qquad F_3=\mathcal E_{T^3}.
\tag{140.1}
$$

它们的共同分母为 $P_{C'}(\theta^7)$，各自在完整图中至少四阶消失。令 $q_j=\operatorname{in}_4(F_j|_{B_{0,s}})$，则

$$
q_1=[t]p(T^3+tT)^2,
\qquad q_2=[t]p(T^3+tT^2)^2,
$$

$$
q_3=\left[z_{03}z_{25}-(z_{04}+z_{13})(z_{15}+z_{24})
+(z_{05}+z_{14}+z_{23})z_{14}\right]^2,
\tag{140.2}
$$

其中 $p$ 的六个线性因子已由 (136.4) 给全。它们的精确检测值为

$$
\begin{aligned}
\Psi(q_1)&=2\Omega_3\otimes(3z_{12}-z_{03}),\\
\Psi(q_2)&=2\Omega_3\otimes(2z_{13}-z_{04}),\\
\Psi(q_3)&=2\Omega_3\otimes(2z_{14}-z_{05}-z_{23}).
\end{aligned}
\tag{140.3}
$$

因此 $\dim(J_4(A_{0,s})/P_4)\ge3$。

证明。三次首一铅笔的非核块行列式符号固定，命题 135.2 可直接取 $t$ 系数。模 $\langle e_0,e_1,e_2\rangle$ 后的三角列变换给 $\Omega(T^3+tT^j)=\Omega_3$，命题 137.2 给 (140.3)。三个非零检测权为 $18,19,20$，而 $\Psi(P_4)=0$，故模 $P_4$ 独立。它们与定义 138.1 的端点展示符号相同。证毕。

## 141. 中文普通语言的完整定理表述

**定理 141.1（原系数在四次层确有二次乘积之外的信息）。** 在任意特征零域上，固定一个次数为 $2m$、$m\ge7$ 的可分域扩张，取任一本原元，并以它的前 $m$ 个连续幂组成半维窗口。保留这个实际窗口的原始带符号、带标签系数。无论选择哪一组合法的原域正系数枢轴，原完成系数环在正规化实际纤维中的像，都有至少 $4m-25$ 个独立四次方向，不能由全部可见二次方向的乘积线性组合得到。当 $m=7$、域次数为十四时，已有三个这样的方向。

证明。先说明这里的实际纤维。原系数的微小变化同时包含正方向的一次信息和负方向的二次信息。用真实系数枢轴把正方向固定在基点，等于把正变量解成负变量的偶次级数。原函数的二次项须减去通过这个解带入的正向贡献。040 的完整耦合像保证减完之后，全部实际可见二次信息恰好是 $K$。因此允许相乘的二次信息已经全部计入，而实际像始终是原完成系数环映入这个纤维的像。

接着直接在原系数上造函数：把原系数多项式放在同一个域元素 $H(\theta)$ 上评价，再除以在基点不为零的 $P_C(\theta^m)$。这仍是原域的合法局部函数。让 $H$ 的次数为 $m-4$，残数迹保证它的真实乘法行列式恰有四维核。行列式要出现非零项，必须在这四个核方向各取得一次变化，所以这个函数在消去正变量以前就已经至少四阶消失。

这四维核上的负向一次变化是一个写明了六个条目的斜对称矩阵，其行列式为 Pfaffian 的平方。正参数虽然一般会影响四次项，但这里的特殊函数在整个图中已经四阶消失，而正参数的补偿从负变量的二次开始；代入后只会提高次数，无法改变第一次出现的四次项。若 $H$ 的最高项系数也变化，还须先除去非核块贡献的外部参数单位；定义 136.1 正好完成这个有限校正，所得函数仍在原系数局部环中。

一个四次式写成某个二次式的平方，并不表示它来自实际可见二次信息的乘积。检测器 $\Psi$ 消去所有允许的 $K$ 乘积，却把这些实际构造的四次式送到明确的非零张量。因此它们无法改写成任何这样的乘积线性组合。

把单项式改成相邻两个单项式的铅笔，提取参数的各个系数，再加入两个低次扰动，就得到定义 138.1 的函数。它们的非零检测值处在连续而不同的辅助指标权 $18$ 到 $4m-8$ 上，彼此不能抵消，共有 $4m-25$ 个。这里的权只用来证明线性独立，不要求原系数族具有额外对称性。相同的一批四次符号对每组合法正枢轴都成立。

这些函数也给原系数余切核中的独立关系提升：正规化余切的最低层看不见它们，但实际纤维的四次层检测得到它们，而且它们不能由原系数极大理想中的元素相乘消去。因此原系数余切核至少有 $4m-25$ 维，原环与实际像纤维的嵌入维数分别满足 (139.3)--(139.4)。这证明了所述有限下界及其源余切后果。证毕。

## 142. 文献对应与完整四次像的剩余问题

**约定 142.1（数学来源的对应范围）。** 原系数、原乘法商、正规化和负余切识别使用 [039，§§111、113、115--117](https://github.com/the-omega-institute/trureturing/blob/e5f5994ce4e5c1e553f9fcafb37a5e8fd21f1dbb/docs/develop/theory/AURIC_R5_039_UNIFORM_COEFFICIENT_NORMALIZATION_AND_HIGHER_DEGREE_DEFECT.md)。完整耦合余切像使用 [040，定理 122.1、命题 122.2](https://github.com/the-omega-institute/trureturing/blob/f32f2d3b8219fae2014e5db4ab3c31575edf0672/docs/develop/theory/AURIC_R5_040_EXACT_COTANGENT_DEFECT_AND_RECTANGLE_INTERPOLATION.md)。引理 134.2 是这些全次数输入与实际枢轴消元之间的直接桥接。

四指标 Pfaffian 的三项符号对应 Donald E. Knuth，[*Overlapping Pfaffians*，math/9503234v1，§0，(0.1)--(0.2)](https://arxiv.org/html/math/9503234v1)。经典 Bianchi 核与外四次补空间的对应见 Renato G. Bettiol、Mario Kummer、Ricardo A. E. Mendes，[*Convex Algebraic Geometry of Curvature Operators*，1908.03713v2，§§2.1--2.2，(2.2)、(2.4)](https://arxiv.org/html/1908.03713v2)：在实内积识别下，外乘的伴随把外四次空间嵌入对称二次空间，其正交补为 Bianchi 核。本文在任意特征零 $F$ 上使用外积和有确定类型的极化恒等式；实际 $K$ 来自 (132.7)，而非从实内积表示直接转移原族结论。

上述经典恒等式作为实际评价构造的中间步骤使用。本文关于原评价、实际消元后共同符号和 $4m-25$ 个独立类的推导属于这些输入上的综合结果。所用文献对应不包含完整四次乘积商的表示分解，也不承担原系数完整像的分类。

**问题 142.2（第一处完整像缺口）。** 在相同原族和实际枢轴下，确定

$$
\operatorname{im}\overline\lambda_s=J_4(A_{0,s})/P_4
\tag{142.1}
$$

的全部方向，以及这些完整像在改变合法正枢轴时的关系。定理 138.2 给其中共同的 $4m-25$ 维子空间；尚未给出排除其余原系数取消方向的上界。即使 $m=7$，$\bigwedge^6V\otimes W$ 的十五维环境中也仅展示了 (140.3) 的三个独立检测方向。

一般原函数的 $U^2$、$UY^2$、正变量的二次和四次补偿均可参与消元后的四次项。命题 135.2 的完整图四阶消失只为特殊评价函数建立，不能据此删除一般函数的这些贡献。因而 $E_m$ 的共同性不等于整个 $J_4(A_{0,s})$ 或整个实际纤维环与枢轴无关；本文也未确定 $\ker\Psi=P_4$。完整四次像、实际像环的完整表示及更高阶结构均不由本下界决定。

## 追加锚（本行以下为增补区）
