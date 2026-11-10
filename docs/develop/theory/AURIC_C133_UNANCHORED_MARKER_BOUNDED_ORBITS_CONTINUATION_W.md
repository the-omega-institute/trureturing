# 无锚三相配平的有界轨道与有限历史预算

## 1. 全变量关系与实际轨道

**定义 1.1（比较来源与轨道预算）。**令 $M$ 为带双侧单位 $1$ 的 magma，$U:M\to M$ 任意，$c:M^2\to[0,\infty)$ 处处有限且对角为零。不预设结合、交换、逆元、对称性、距离、$U1=1$ 或任何线性表示。要求对全部 $a,b,u,v$ 成立

$$
\sum_{k=0}^2 c(a\cdot U^ku,b\cdot U^kv)=3c(a,b)+3c(u,v).
\tag{R}
$$

写 $p_j=U^j1$、$q(x)=c(x,1)$、$r(x)=c(1,x)$，并定义有限非负预算

$$
\Omega(a)=c(a,Ua)+c(a,U^2a)+q(p_1)+q(p_2).
\tag{1.1}
$$

所有下文历史均为实际有限配方，保留原有次序和二叉括号。这里的预算不预设五点负型或完整 Hilbert 表示。

**引理 1.2（同步等距与单项控制）。**有 $c(Ux,Uy)=c(x,y)$，且

$$
c(a\cdot u,b\cdot v)\le3\bigl(c(a,b)+c(u,v)\bigr),\qquad
c(x,y)\le3\bigl(q(x)+r(y)\bigr).
\tag{1.2}
$$

**证明。**第一项复用[《任意标记的五点正性桥梁与仿射复几何》](AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE.md)引理 2.1 的非负递推，那里仅使用 (R)。原式的第零项不大于三项总和，给第一条界；再取 $(a,b,u,v)=(x,1,1,y)$ 得第二条界。没有使用尚未取得的三角不等式。

## 2. 四项余量迫出双向轨道界

**定理 2.1（精确轨道余量）。**对全部 $a\in M$、整数 $n\ge0$，有

$$
\begin{aligned}
&3\bigl(\Omega(a)-q(U^na)-r(U^na)\bigr)\\
&\quad=\sum_{k=1}^2\sum_{j=1}^2
c\bigl((U^na)\cdot p_{k+j},(U^{n+k}a)\cdot p_j\bigr)\ge0.
\end{aligned}
\tag{2.1}
$$

**证明。**固定 $x$，令 $h_k(x)=c(x\cdot p_k,U^kx)$。(R) 取 $(a,b,u,v)=(x,1,1,x)$，第零项为零，故

$$
h_1(x)+h_2(x)=3q(x)+3r(x).
\tag{2.2}
$$

对 $k=1,2$，分别取 $(a,b,u,v)=(x,U^kx,p_k,1)$，得到

$$
\begin{aligned}
&3c(x,U^kx)+3q(p_k)-h_k(x)\\
&\qquad=\sum_{j=1}^2c\bigl(x\cdot p_{k+j},(U^kx)\cdot p_j\bigr).
\end{aligned}
\tag{2.3}
$$

这里仅用 $U^jp_k=p_{k+j}$ 与双侧单位，没有重括号。对 $k$ 求和并用 (2.2)，再令 $x=U^na$；同步等距给 $c(U^na,U^{n+k}a)=c(a,U^ka)$，即得 (2.1)。

**推论 2.2（独立标记次数的统一界）。**对全部 $a,b$ 和独立整数 $n,m\ge0$，

$$
q(U^na)+r(U^na)\le\Omega(a),\qquad
c(U^na,U^mb)\le3\bigl(\Omega(a)+\Omega(b)\bigr).
\tag{2.4}
$$

特别，单位轨道的双向费用不超过 $q(p_1)+r(p_1)+q(p_2)+r(p_2)$。

**证明。**第一条由 (2.1) 右侧非负。第二条将其代入 (1.2) 的第二条界。取 $a=1$ 时，$\Omega(1)=r(p_1)+r(p_2)+q(p_1)+q(p_2)$。

**推论 2.3（任意固定探针的双侧预算）。**在自由实差空间 $E$ 中写 $e_a=\delta_a-\delta_1$、$B(e_a,e_b)=(q(a)+r(b)-c(a,b))/2$。则对全部 $a,z$、$n\ge0$，

$$
|B(e_{U^na},e_z)|\le\Omega(a)+r(z),\qquad
|B(e_z,e_{U^na})|\le q(z)+\Omega(a).
\tag{2.5}
$$

**证明。**(1.2) 与 $c\ge0$ 给 $-(q(x)+r(y))\le B(e_x,e_y)\le(q(x)+r(y))/2$，再分别用 (2.4) 控制两种配对次序。对任意固定有限线性组合探针，还可按系数绝对值求和取得有限界；这不把 $B$ 变成正定内积。

**命题 2.4（有界标记不等于有界来源）。**若整个 $c$ 一致有界，则 $c=0$。非零模型的整体费用因此无界，仍须满足 (2.4) 对每两条固定标记轨道的统一控制。

**证明。**设 $C=\sup_{a,b}c(a,b)<\infty$。若 $C>0$，选两对输入使各自费用大于 $3C/4$；(R) 的右端大于 $9C/2$，左端至多 $3C$，矛盾。第一条不对单条轨道的有界性作全局外推。

## 3. 任意固定有序树的完整费用传递

**定义 3.1（实际标记树）。**设 $T$ 是具有 $N\ge1$ 个有序叶子的满二叉树。在每个内部结点选择 $\kappa_v\in\{0,1,2\}$。叶子输入为 $\mathbf a=(a_1,\ldots,a_N)$；内部结点按 $H_{\rm left}\cdot U^{\kappa_v}(H_{\rm right})$ 递推，所得实际配方记为 $H_{T,\kappa}(\mathbf a)$。全部内部标记配置组成有限集 $\mathcal K_T$，其基数为 $3^{N-1}$。

**定理 3.2（全树平均与固定树预算）。**对全部两组叶子输入，

$$
\frac1{3^{N-1}}\sum_{\kappa\in\mathcal K_T}
 c\bigl(H_{T,\kappa}(\mathbf a),H_{T,\kappa}(\mathbf b)\bigr)
=\sum_{i=1}^Nc(a_i,b_i).
\tag{3.1}
$$

若第 $i$ 个叶子的深度为 $d_i$，则对每个固定内部配置 $\kappa$ 及全部独立叶子指数 $n_i,m_i\ge0$，

$$
\begin{aligned}
&c\bigl(H_{T,\kappa}(U^{n_1}a_1,\ldots,U^{n_N}a_N),
 H_{T,\kappa}(U^{m_1}b_1,\ldots,U^{m_N}b_N)\bigr)\\
&\qquad\le3\sum_{i=1}^N3^{d_i}\bigl(\Omega(a_i)+\Omega(b_i)\bigr).
\end{aligned}
\tag{3.2}
$$

**证明。**对内部结点数归纳。固定根下的两棵子树配置，对根的三个标记平均，由 (R) 得左右子树费用之和；再分别取子树平均，即得 (3.1)。逐结点使用 (1.2) 的第一条界及同步等距，给每个叶子费用至多乘 $3^{d_i}$，然后代入 (2.4)，得到 (3.2)。两端使用同一个 $T,\kappa$；叶子标记次数可以独立。树形变化或深度增长时，(3.2) 不提供与树深无关的预算。

**推论 3.3（不定号配对的精确传递）。**沿用推论 2.3 的自由实差空间 $E$ 和双线性型 $B$。令 $h_{T,\kappa}=H_{T,\kappa}(1,\ldots,1)$、$\Xi_{T,\kappa}(\mathbf a)=e_{H_{T,\kappa}(\mathbf a)}-e_{h_{T,\kappa}}$，则

$$
\frac1{3^{N-1}}\sum_{\kappa}
 B\bigl(\Xi_{T,\kappa}(\mathbf a),\Xi_{T,\kappa}(\mathbf b)\bigr)
=\sum_iB(e_{a_i},e_{b_i}).
\tag{3.3}
$$

**证明。**用 $2B(e_x-e_s,e_y-e_t)=-c(x,y)+c(x,t)+c(s,y)-c(s,t)$，对 (3.1) 的叶子输入对 $(\mathbf a,\mathbf b)$、$(\mathbf a,\mathbf1)$、$(\mathbf1,\mathbf b)$、$(\mathbf1,\mathbf1)$ 作四点极化即可。式 (3.3) 传递的是起初可非对称、不定号的 $B$；实际成对费用非负不能替代任意带符号组合的平方非负。

## 4. 可消费的约束与未解决的桥

**例 4.1（精确余量可以严格为正）。**取 $M=\mathbb Z[\omega]$，二元运算为加法，原单位 $1_M=0$，$Uz=\omega z+1$、$c(z,w)=|z-w|^2$，其中 $\omega^2+\omega+1=0$。该模型满足完整 (R)，整体费用无界。单位轨道为 $p_0=0,p_1=1,p_2=1+\omega,p_3=0,p_4=1$。取定理 2.1 的 $a=1_M,n=0$，则 $\Omega(1_M)=4$，右侧四项分别都是 $3$，总余量为 $12$。因此四项余量不是应当逐项归零的缺陷；完整仿射表示也允许它们严格为正。

**证明。**$Fz=z$ 给前述五点桥梁的仿射表示，故满足 (R)。四项差依次为 $\omega-1,-(2+\omega),-(2+\omega),-(1+2\omega)$，平方模均为 $3$。$c(n,0)=n^2$ 给整体无界。

**问题 4.2（轨道预算到五点根性的缺口）。**前述五点桥梁已经证明，在当前原始假设与 (R) 下，五点负型、乘法四点缺陷 $D(a,u)=e_{a\cdot u}-e_a-e_u$ 的双侧根性、全有限负型与完整仿射复 Hilbert 表示等价。仍未证明的是仅从 (R) 推出这些条件。直接根性路线的精确目标为

$$
B(D(a,u),e_z)=B(e_z,D(a,u))=0
\qquad(a,u,z\in M).
$$

轨道预算给每个固定探针与独立标记次数的有限控制；全树平均给精确配对关系。它们尚未给目标根性、原始 $U^3$ 的完整行列周期或五点负型。若采用带 $1/n$ 误差的有限历史消去，必须取得与 $n$ 无关的有限费用预算，或另证实际误差趋零；(3.2) 中随树深增长的系数不能省略。若改走负型路线，对称性也须单独证明，因为二次型不探测反对称部分。

**对应 4.3（用途与量子接口范围）。**`repo-derived`：本卷的无条件新增约束是精确轨道余量及独立轨道上界；有序树恒等式把同一 (R) 传递到全部有限实际历史。它们限制反例和误差预算，不把一般去锚分类记为完成，也不额外供应准备、记录、参考、联合或时间操作。三历史强正 Gram、完整测试效果、最小输入空间上的 Kraus 延拓及其实际接口，继续依赖前述五点桥梁列出的表示条件。有限平均、非负界与四点极化是常规工具；此处不作独立文献优先权主张。

## 追加锚（本行以下为增补区）


## 5. 独立有限窗口的固定边框预算

**定义 5.1（轨道方窗与实际右平移）。**对整数 $L\ge1$，置

$$
C_L(u,v)=\frac1{L^2}\sum_{0\le n,m<L}c(U^nu,U^mv),\qquad
K_L(a,u;b,v)=\frac1{L^2}\sum_{0\le n,m<L}c(a\cdot U^nu,b\cdot U^mv).
\tag{5.1}
$$

在自由实差空间 $E$ 上定义线性算子

$$
\mathcal T_L^u e_a=\frac1L\sum_{n=0}^{L-1}
\bigl(e_{a\cdot U^nu}-e_{U^nu}\bigr),\qquad
\mathcal A_L=\mathcal T_L^1.
\tag{5.2}
$$

单位 $a=1$ 时右端为零，故此定义与 $e_1=0$ 相容。这些平均只是有限标量和或自由空间向量，不作为 $M$ 中的新对象或单位。

**定理 5.2（独立轨道平均律）。**在定义 1.1 与 (R) 下，令

$$
W(a,b;u,v)=3c(a,b)+9\bigl(\Omega(u)+\Omega(v)\bigr).
$$

对全部四标签及 $L\ge1$，有

$$
\left|K_L(a,u;b,v)-c(a,b)-C_L(u,v)\right|
\le\frac{2W(a,b;u,v)}L.
\tag{5.3}
$$

**证明。**令 $H_{n,m}=c(a\cdot U^nu,b\cdot U^mv)$、$Q_L=\{0,\ldots,L-1\}^2$，并写 $Q_L+k=\{(n+k,m+k):(n,m)\in Q_L\}$。引理 1.2 与推论 2.2 给 $0\le H_{n,m}\le W(a,b;u,v)$，对全部独立 $n,m\ge0$ 成立。对 (R) 的输入 $(a,b,U^nu,U^mv)$ 在 $Q_L$ 上求和，得到精确式

$$
\begin{aligned}
&3L^2\bigl(K_L(a,u;b,v)-c(a,b)-C_L(u,v)\bigr)\\
&\quad=\sum_{k=1}^2\left(
\sum_{Q_L\setminus(Q_L+k)}H_{n,m}
-\sum_{(Q_L+k)\setminus Q_L}H_{n,m}\right).
\end{aligned}
\tag{5.4}
$$

两差集基数相等，每个至多 $2kL$。各项属于同一 $[0,W]$，故第 $k$ 个括号绝对值至多 $2kLW$。对 $k=1,2$ 求和并除以 $3L^2$，即得 (5.3)。此外，同步等距给 $\Omega(U^ru)=\Omega(u)$；用 $U^ru,U^sv$ 替换 $u,v$，同一预算也适用于任意独立起点 $r,s\ge0$。这里仅增长一元标记次数，所有乘积仍有一个二元结点；未使用随树深增长的预算。

**定理 5.3（平均右平移恢复原配对）。**对全部 $a,b,u,v$ 与 $L\ge1$，有

$$
\left|B(\mathcal T_L^ue_a,\mathcal T_L^ve_b)-B(e_a,e_b)\right|
\le\frac{3[c(a,b)+q(a)+r(b)]+27[\Omega(u)+\Omega(v)]}L.
\tag{5.5}
$$

**证明。**四点极化给

$$
\begin{aligned}
2B(\mathcal T_L^ue_a,\mathcal T_L^ve_b)
={}&-K_L(a,u;b,v)+K_L(a,u;1,v)\\
&+K_L(1,u;b,v)-C_L(u,v).
\end{aligned}
$$

前三项分别用 (5.3)，其主项为 $c(a,b)+C_L(u,v)$、$q(a)+C_L(u,v)$、$r(b)+C_L(u,v)$。共同的 $C_L$ 精确抵消，剩余 $2B(e_a,e_b)$。三个误差预算相加后除以二，得到 (5.5)。此式不预设 $B$ 对称或正定。

**推论 5.4（平均缺陷的双向消去）。**置

$$
D_n(a,u)=e_{a\cdot U^nu}-e_{a\cdot p_n}-e_{U^nu}+e_{p_n},\qquad
\overline D_L(a,u)=\frac1L\sum_{n=0}^{L-1}D_n(a,u).
$$

则 $D_0(a,u)=D(a,u)$、$\overline D_L(a,u)=(\mathcal T_L^u-\mathcal A_L)e_a$，且

$$
\left|B(\overline D_L(a,u),\mathcal A_Le_z)\right|
\le\frac{6[c(a,z)+q(a)+r(z)]+27\Omega(u)+81\Omega(1)}L,
\tag{5.6}
$$

$$
\left|B(\mathcal A_Le_z,\overline D_L(a,u))\right|
\le\frac{6[c(z,a)+q(z)+r(a)]+27\Omega(u)+81\Omega(1)}L.
\tag{5.7}
$$

**证明。**第一方向对 $(u,1)$ 与 $(1,1)$ 两次使用 (5.5) 并相减；第二方向对 $(1,u)$ 与 $(1,1)$ 使用同式。主配对均精确抵消，不借对称性对调 $B$。固定 $v$ 时，测试向量也可换为 $\mathcal T_L^ve_z$，相同计算给有限固定预算除以 $L$ 的界。

## 6. 三次滑移保留的未来测试域

**命题 6.1（尾部行列恒等式）。**令 $P_nx=x\cdot p_{3n}$、$Y_n(a,u)=a\cdot U^{3n}u$。对全部 $m\ge n\ge0$ 及 $a,u,z$，

$$
\begin{aligned}
c(Y_n(a,u),P_mz)
&=c(P_n(a\cdot u),P_mz)\\
&=c(U^{3n}(a\cdot u),P_mz)\\
&=c(a\cdot u,P_{m-n}z),
\end{aligned}
\tag{6.1}
$$

交换两个参数后的四项也相等。因此前三种实际历史对 $\bigcup_{m\ge n}P_m(M)$ 的全部测试具有相同行列。

**证明。**置 $f_j=c(a\cdot U^ju,b\cdot U^jv)$。(R) 与同步等距给 $f_j+f_{j+1}+f_{j+2}=3c(a,b)+3c(u,v)$；相邻两式相减得 $f_{j+3}=f_j$。式 (6.1) 每一项都能从两个右输入同步撤去 $3n$ 次标记。例如首项为

$$
c\bigl(a\cdot U^{3n}u,z\cdot U^{3n}p_{3(m-n)}\bigr)
=c(a\cdot u,z\cdot p_{3(m-n)}).
$$

第二项的右输入取 $(1,p_{3(m-n)})$，第三项的左背景取 $1$、右输入取 $(a\cdot u,p_{3(m-n)})$，同样得到最后一项。反向式逐项使用相同滑移。没有将 $(a\cdot u)\cdot p_{3n}$ 重括号为 $a\cdot(u\cdot p_{3n})$。引理 1.2 还给全部独立 $m,n\ge0$ 的统一界

$$
c(Y_n(a,u),P_mz)\le3c(a,z)+9[\Omega(u)+\Omega(1)].
$$

此测试域不被宣告等于 $M$；命题没有把 $P_mz$ 换成任意原始 $z$。

## 7. 复制历史对一致次线性项的消去

**定理 7.1（有符号关系解的一致次线性消去）。**设处处有限的 $d:M^2\to[0,\infty)$、$h:M^2\to\mathbb R$ 都满足与 (R) 相同的四变量线性关系。若

$$
\forall\varepsilon>0\ \exists C_\varepsilon<\infty\ \forall a,b,\qquad
|h(a,b)|\le\varepsilon d(a,b)+C_\varepsilon,
\tag{7.1}
$$

则 $h=0$。

**证明。**令 $\Phi_k(x)=x\cdot U^kx$，并对函数定义正平均算子

$$
(Pf)(a,b)=\frac13\sum_{k=0}^2f(\Phi_k(a),\Phi_k(b)).
$$

关系的输入 $(u,v)=(a,b)$ 给 $Pd=2d$、$Ph=2h$，从而

$$
2^n|h(a,b)|=|P^nh(a,b)|\le P^n|h|(a,b)
\le\varepsilon2^nd(a,b)+C_\varepsilon.
$$

先除以 $2^n$ 并令 $n\to\infty$，再令 $\varepsilon\downarrow0$。所有迭代都使用原始实际历史 $x_{j+1}=x_j\cdot U^{k_j}x_j$，复制已带完整括号的 $x_j$，不改变其内部括号。平均精确放大因子为 $2^n$，没有用逐历史的最坏深度界替代平均。

**推论 7.2（对称性的一致次线性充分条件）。**若定义 1.1 与 (R) 下还满足：对每个 $\varepsilon>0$ 存在有限 $C_\varepsilon$，使全部 $a,b$ 有

$$
|c(a,b)-c(b,a)|\le\varepsilon\frac{c(a,b)+c(b,a)}2+C_\varepsilon,
\tag{7.2}
$$

则 $c$ 对称。

**证明。**$d=(c+c^{\mathsf T})/2$ 与 $h=c-c^{\mathsf T}$ 都满足同一关系，应用定理 7.1。原始非负性只给 $|h|\le2d$，未给 (7.2)。对固定 $a,u$ 的缺陷配对也未被证明组成满足完整四变量关系的函数，故本推论不消去该缺陷。

## 8. 不能由平均或有界性替代的关系

**问题 8.1（撤平均与回拉）。**沿用问题 4.2，目标仍为全部 $a,u,z$ 上 $B(D(a,u),e_z)=B(e_z,D(a,u))=0$。定理 5.3 保留原配对，推论 5.4 消去平均缺陷对平均探针的配对，二者不等于以下尚未取得的回拉：

$$
\begin{aligned}
B(D(a,u),e_z)-B(\overline D_L(a,u),\mathcal A_Le_z)&\longrightarrow0,\\
B(e_z,D(a,u))-B(\mathcal A_Le_z,\overline D_L(a,u))&\longrightarrow0.
\end{aligned}
\tag{8.1}
$$

标量序列 $\cos(2\pi n/3)$ 的平均为零极限而第零项非零，故单有平均消失不能恢复原值；该序列不是完整 (R) 模型的反例。命题 6.1 的未来测试域也尚未回拉到任意原始探针。这些是原目标的未证步骤，不作为新增公理。

**命题 8.2（合法模型中的平均锚费用可正）。**在 $M=\mathbb C$ 的加法来源中，单位为 $0$，取 $Ua=\omega a+t$、$c(a,b)=|a-b|^2$。若 $3\mid L$，则

$$
C_L(1_M,1_M)=\frac23|t|^2.
\tag{8.2}
$$

**证明。**单位轨道依次为 $0,t,(1+\omega)t$，三点两两距离平方均为 $|t|^2$。有序独立选取两个相位的九种情形中，六种不同；对三的倍数窗口计数即得。该来源满足完整 (R)，所以共同平均锚费用不能被要求为零，平均也不产生新的真实单位。

**命题 8.3（有界同步核不保证根稳定或均值换序）。**存在对称、非负、对角零且同步 $U$ 等距的核，满足推论 2.2 的两项轨道上界，但相应 $S$ 不保持双侧根；其有界双序列费用还可有不同的两个迭代极限。本命题不提供满足 (R) 的乘法。

**证明。**取标签 $1,a_n,b_n$，$n\ge0$，令 $U1=1$、$Ua_n=a_{n+1}$、$Ub_n=b_{n+1}$。在自由差空间定义对称 $B$：

$$
B(e_{a_n},e_{a_m})=0,\qquad B(e_{b_n},e_{b_m})=\delta_{nm},\qquad
B(e_{a_n},e_{b_m})=\frac12\mathbf1_{n>m}.
$$

置 $c(x,y)=B(e_x-e_y,e_x-e_y)$。则 $q(a_n)=r(a_n)=0$、$q(b_n)=r(b_n)=1$，且 $c(a_n,b_m)=\mathbf1_{n\le m}$；两个不同 $b$ 标签间费用为 $2$，其余由上述定义取得。所有费用非负，同步移位保持它们。预算为 $\Omega(a_n)=0$、$\Omega(b_n)=4$、$\Omega(1)=0$，故推论 2.2 的两项数值界成立。可是 $e_{a_0}$ 为根向量，$B(Se_{a_0},e_{b_0})=1/2$。$B$ 也可连续扩张到这些自由基的 $\ell^1$ 完成，$S$ 的算子范数为 $1$，故加入这些连续性与幂有界条件仍不保证根稳定。另外

$$
\lim_{n\to\infty}\lim_{m\to\infty}c(a_n,b_m)=1,\qquad
\lim_{m\to\infty}\lim_{n\to\infty}c(a_n,b_m)=0.
$$

因此轨道上界本身不授权均值换序。该核整体有界且非零，由命题 2.4 可知它不可能与任何乘法一起满足全部 (R)；它只排除丢失完整关系后的工具捷径。

**对应 8.4（平均结果与表示条件）。**`repo-derived`：第 5–7 节把原始关系的轨道预算用于有限窗口边界、双侧配对及复制历史；有限求和、极化与正平均算子是通常工具，不主张这些工具的文献新意。上述结果尚未推出五点负型、双侧根性或一般仿射表示。三历史强正几何、效果与 Born 读数、最小输入空间上的 Kraus 延拓继续以五点桥梁的表示与实际接口为前件；平均不补充准备、参考、联合或时间操作。

## 追加锚（本行以下为增补区）

## 9. 精确保留比较矩阵的右梳复制

**定义 9.1（带终端的实际右梳）。**对整数 $N\ge0$，置 $\Sigma_N=\{0,1,2\}^N$。对 $\sigma=(\sigma_1,\ldots,\sigma_N)$，严格按下列括号递推：

$$
H_0(a;z)=z,\qquad
H_N^\sigma(a;z)
=a\cdot U^{\sigma_1}H_{N-1}^{(\sigma_2,\ldots,\sigma_N)}(a;z).
\tag{9.1}
$$

每条历史含有 $N$ 个左叶 $a$ 和一个终端 $z$；标记施于整个右子树。记 $s(\sigma)=\sum_i\sigma_i$。

**定理 9.2（右梳的精确费用与真实单位预算）。**在定义 1.1 与 (R) 下，对全部 $a,b,z,w$，

$$
3^{-N}\sum_{\sigma\in\Sigma_N}
c(H_N^\sigma(a;z),H_N^\sigma(b;w))
=N c(a,b)+c(z,w).
\tag{9.2}
$$

此外，严格有 $H_N^\sigma(1;z)=U^{s(\sigma)}z$，因而

$$
q(H_N^\sigma(1;1))+r(H_N^\sigma(1;1))
\le\Omega(1).
\tag{9.3}
$$

**证明。**(9.2) 对 $N=0$ 成立。固定内层的 $N-1$ 个相位，最外层相位的三项平均由 (R) 恰为 $c(a,b)$ 加内层比较；再作有限平均并归纳。单位左叶使每个结点严格成为 $U^{\sigma_i}$ 的作用，指数相加给第二项的对象等式。其终端为 $1$ 时，输出为 $p_{s(\sigma)}$，推论 2.2 给 (9.3)。预算指向真实单位 $1$，且不依赖梳深；没有用一般固定树的深度增长预算取代此处的界。

**定理 9.3（完整关系模型中的核保持复制）。**对 $N\ge1$，令 $M_N=M^{\Sigma_N}$，逐坐标定义乘法和 $U_N$，真实双侧单位为常数组 $\mathbf1$。置

$$
c_N(f,g)=\frac1{N3^N}\sum_{\sigma\in\Sigma_N}c(f(\sigma),g(\sigma)),
\qquad
\Gamma_N(a)(\sigma)=H_N^\sigma(a;1).
\tag{9.4}
$$

则 $c_N$ 有限、非负、零对角，且在 $M_N$ 的全部四个数组上满足同一 (R)。对全部 $a,b$，

$$
c_N(\Gamma_N(a),\Gamma_N(b))=c(a,b).
\tag{9.5}
$$

若 $\mathbf p_j$ 表示值为 $p_j$ 的常数组，则

$$
\begin{aligned}
c_N(\Gamma_N(1),\mathbf1)+c_N(\mathbf1,\Gamma_N(1))&\le\frac{\Omega(1)}N,\\
c_N(\mathbf p_j,\mathbf1)+c_N(\mathbf1,\mathbf p_j)&\le\frac{\Omega(1)}N
\qquad(j\ge0).
\end{aligned}
\tag{9.6}
$$

**证明。**逐坐标的实际 (R) 求有限和并除以 $N3^N$，给复制模型的完整关系。乘法单位与比较的其余性质逐坐标成立。(9.5) 为 (9.2) 的终端 $z=w=1$；(9.6) 分别由 (9.3) 和 $q(p_j)+r(p_j)\le\Omega(1)$ 得到。这里没有断言 $\Gamma_N$ 保持乘法、标记或真实单位，也未把它当作原始配方的同态。

**推论 9.4（小单位漂移下仍可精确保留有限违反量）。**若某个原始 (R) 模型的费用不对称，或某个有限标签配置违反条件负型，则对每个 $\varepsilon>0$，存在满足全部原始前件与 (R) 的模型，其中单位轨道各点到真实单位的双向费用和不超过 $\varepsilon$，同时逐项保留该有限比较矩阵及其违反量。

**证明。**取 $N$ 使 $\Omega(1)/N\le\varepsilon$，使用定理 9.3。对称性之差和任意固定零和系数的负型二次和只依赖比较矩阵，所以由 (9.5) 原值保留。单纯缩放原费用会一并缩小违反量；此处复制保留原矩阵。这是对假定存在的违反量的传递命题，不断言原始 (R) 已有反例。乘法缺陷涉及运算，不能因核保持就断言其同样由 $\Gamma_N$ 传递。

## 10. 外移复制的精确未来测试域

**定理 10.1（共同外移与有限正交域）。**沿用定理 9.3，取整数 $L\ge2N$，定义实际数组

$$
X_{N,L}(a)(\sigma)=U^{L-s(\sigma)}H_N^\sigma(a;1),
\qquad Z_L(z)=\mathbf{U^Lz},\qquad o_{N,L}=\mathbf p_L.
\tag{10.1}
$$

则 $X_{N,L}(1)=o_{N,L}$，并且

$$
\begin{aligned}
c_N(X_{N,L}(a),X_{N,L}(b))&=c(a,b),\\
c_N(X_{N,L}(a),Z_L(z))&=q(a)+\frac{r(z)}N,\\
c_N(Z_L(z),X_{N,L}(a))&=r(a)+\frac{q(z)}N.
\end{aligned}
\tag{10.2}
$$

在以 $o=o_{N,L}$ 为展开基点的自由差空间中，置 $\epsilon_x=\delta_x-\delta_o$ 和

$$
B_N^o(\epsilon_x,\epsilon_y)
=\frac{c_N(x,o)+c_N(o,y)-c_N(x,y)}2.
$$

则有精确的双向配对关系

$$
\begin{aligned}
B_N^o(\epsilon_{X_{N,L}(a)},\epsilon_{X_{N,L}(b)})&=B(e_a,e_b),\\
B_N^o(\epsilon_{X_{N,L}(a)},\epsilon_{Z_L(z)})
&=B_N^o(\epsilon_{Z_L(z)},\epsilon_{X_{N,L}(a)})=0.
\end{aligned}
\tag{10.3}
$$

**证明。**$s(\sigma)\le2N$ 保证全部外移指数非负。两端共同施加同一 $U$ 次数不改比较，故第一式由 (9.5) 得到。再将 (9.2) 的另一棵右梳取为 $H_N^\sigma(1;z)=U^{s(\sigma)}z$；共同外移后它严格变成 $U^Lz$，得到其余两式。取 $a=1$，得

$$
c_N(o,Z_L(z))=r(z)/N,\qquad c_N(Z_L(z),o)=q(z)/N.
$$

取 $z=1$，得 $c_N(X_{N,L}(a),o)=q(a)$ 及反向值 $r(a)$。分别代入四点展开，所有交叉项精确抵消，给 (10.3)。换展开基点不把 $o$ 变成乘法单位，也不预设双线性型正定或对称。

**推论 10.2（全部未来常数标记的统一余量）。**若 $r\ge L$，则

$$
\begin{aligned}
c_N(X_{N,L}(a),\mathbf p_r)&=q(a)+\frac{r(p_{r-L})}N,\\
c_N(\mathbf p_r,X_{N,L}(a))&=r(a)+\frac{q(p_{r-L})}N.
\end{aligned}
\tag{10.4}
$$

两个余项之和不超过 $\Omega(1)/N$，对全部 $a$ 及 $r\ge L$ 一致。

**证明。**在 (10.2) 取 $z=p_{r-L}$，再用推论 2.2。

**问题 10.3（小费用到上下文行列的缺桥）。**定理 9.3 和定理 10.1 没有把未来域 $Z_L(M)$ 宣告为全部 $M_N$，也未控制 $c_N(X_{N,L}(a),\mathbf1)$ 及其反向值。即使移动基点到真实单位的费用趋零，仍需另证所需读数的有限性及下列上下文识别：将 $U_N\mathbf1$ 换成 $\mathbf1$ 时，每个相关实际历史与每个探针的双向比较均有相同极限。零费用本身尚不等于完整行列相等或可取商的对象等式。

对任意 $x\in M$，单项界确实给出

$$
\begin{aligned}
c(p_jx,x),\ c(xp_j,x)&\le3q(p_j),\\
c(x,p_jx),\ c(x,xp_j)&\le3r(p_j).
\end{aligned}
\tag{10.5}
$$

但这些成对小费用尚不控制任意第三探针的读数差。原始目标仍是问题 4.2 的全部双侧根性；小单位漂移与精确有限核保持是归约工具，不是额外公理或已完成的去锚分类。

## 11. 缺陷形式的两个非平凡三相通道

**定理 11.1（在自由空间中的缺陷角色）。**在 $E$ 上定义实际左乘的线性延拓

$$
L_ae_u=e_{a\cdot u}-e_a,\qquad T_a=L_a-I,\qquad
Se_u=e_{Uu}-e_{p_1}.
\tag{11.1}
$$

$e_1=0$ 与左乘定义相容，且 $T_ae_u=D(a,u)$。对全部 $a,b$ 和 $x,y\in E$，

$$
\sum_{k=0}^2 B(L_aS^kx,L_bS^ky)=3B(x,y),
\tag{11.2}
$$

$$
\begin{aligned}
\sum_{k=0}^2B(T_aS^kx,S^ky)&=0,\\
\sum_{k=0}^2B(S^kx,T_aS^ky)&=0,\\
\sum_{k=0}^2B(T_aS^kx,T_bS^ky)&=0.
\end{aligned}
\tag{11.3}
$$

若对双线性形式置 $(\mathscr C F)(x,y)=F(Sx,Sy)$，则下列三个形式各满足 $(I+\mathscr C+\mathscr C^2)F=0$ 及 $\mathscr C^3F=F$：

$$
F_a^{\rm L}(x,y)=B(T_ax,y),\quad
F_a^{\rm R}(x,y)=B(x,T_ay),\quad
G_{a,b}(x,y)=B(T_ax,T_by).
\tag{11.4}
$$

在这些形式生成的复化循环空间上，令

$$
P_rF=\frac13\sum_{k=0}^2\omega^{-rk}\mathscr C^kF,
\qquad r=0,1,2,
$$

则 $P_0F=0$、$F=P_1F+P_2F$，且 $\mathscr C P_rF=\omega^rP_rF$。

**证明。**对 (R) 关于右输入 $u,v$ 分别在单位取交替差，左边成为

$$
-2\sum_k B(e_{aU^ku}-e_{ap_k},e_{bU^kv}-e_{bp_k}),
$$

右边为 $-6B(e_u,e_v)$。由 $S^ke_u=e_{U^ku}-e_{p_k}$，得到 (11.2)，再双线性延拓。取 $b=1$ 或 $a=1$ 并减去 $\sum_kB(S^kx,S^ky)=3B(x,y)$，得前两个零和式；四项相减给第三式。由多项式恒等式 $(\mathscr C-I)(I+\mathscr C+\mathscr C^2)=\mathscr C^3-I$，得到三次周期。有限三角色投影的公式随即给最后结论。没有预先使 $S$ 下降到双侧根商；这里的复化只是形式空间上的代数运算。

**命题 11.2（删除非负性后的完整关系与残余缺陷）。**若去掉实际费用非负这一前件，即使保留固定单位标记、三次周期和全部四变量 (R)，也可有非根的乘法缺陷。

**证明。**取 $M=\mathbb C^3$ 为实空间，单位 $1_M=0$，写 $x=(z,w,h)$。定义

$$
\begin{aligned}
\beta(x,y)&=\operatorname{Re}(z\overline{w'}+w\overline{z'}+h\overline{h'}),\\
a\star u&=(z_a+z_u+h_ah_u,\ w_a+w_u,\ h_a+h_u),\\
U(z,w,h)&=(\omega z,\omega w,\omega^2h),\\
c_*(a,b)&=\beta(a-b,a-b).
\end{aligned}
\tag{11.5}
$$

$\beta$ 为非退化的不定号对称型；$0$ 为双侧单位，$U0=0$、$U^3=I$，且 $U$ 保持 $\beta$。令 $A=a-b$、$d=u-v$、$v_0=(h_ah_u-h_bh_v,0,0)$，则

$$
a\star U^ku-b\star U^kv=A+U^kd+\omega^{2k}v_0.
$$

$v_0$ 的方向各向同性。平方的三个纯项求和给 $3\beta(A,A)+3\beta(d,d)$；含 $A$ 的交叉项按 $\omega^k$ 或 $\omega^{2k}$ 求和为零，$U^kd$ 与 $\omega^{2k}v_0$ 的交叉项也按非平凡三角色求和为零。因此完整 (R) 成立。

自由空间的锚定型满足 $B_*(e_x,e_y)=\beta(x,y)$。取 $a=u=(0,0,1)$、$z=(0,1,0)$，有 $a\star a=(1,0,2)$，故 $B_*(D(a,a),e_z)=1$，缺陷不在根空间。与此同时，实际重复历史 $z^{\star n}=(0,n,0)$ 给

$$
c_*(a\star a,z^{\star n})=4-2n<0\qquad(n\ge3).
\tag{11.6}
$$

所以该模型明确违反原始非负性，不是原始问题的反例。它表明仅有代数三相消去不足；排除其缺陷必须消费实际历史闭包上的非负性。

## 12. 单均值产生的非负势与实际 Poisson 方程

**定理 12.1（单位轨道势的精确递推）。**取 $\ell^\infty(\mathbb N_0)$ 上的正、归一、移位不变实均值 $\Lambda$，置

$$
f(a)=\Lambda_n c(a,p_n),\qquad g(a)=\Lambda_n c(p_n,a).
\tag{12.1}
$$

则 $f,g$ 有限非负，$f\circ U=f$、$g\circ U=g$，且

$$
\begin{aligned}
\frac13\sum_{k=0}^2f(a\cdot U^ku)&=q(a)+f(u),\\
\frac13\sum_{k=0}^2g(a\cdot U^ku)&=r(a)+g(u).
\end{aligned}
\tag{12.2}
$$

**证明。**由 (1.2) 与推论 2.2，$c(a,p_n)\le3(q(a)+\Omega(1))$，反向不超过 $3(r(a)+\Omega(1))$，所以均值有定义。取 (R) 的 $(b,v)=(1,p_n)$ 后对 $n$ 取同一个均值。每个左项的第二标签为 $p_{n+k}$，移位不变性给第一式；对转置核重复给第二式。这里只交换有限求和与一个线性均值，没有交换两个无限均值。

取 $a=1$，两种势沿 $U$ 轨道均满足 $x_{n+1}+x_{n+2}=2x_n$。轨道上界保证其有界，因而通解的 $(-2)^n$ 项为零，得到 $fU=f$、$gU=g$。正移位均值的存在与有限加权复合算子的均值相容性是经典工具；参见 El-hady、Brzdęk，*Banach Limit and Fixed Point Approach in the Ulam Stability of the Quadratic Functional Equation*，DOI 10.3390/axioms14030206，第 3 节及 Remark 1。这里不调用其 Theorem 8 的交换群二次方程结论。

**推论 12.2（有限右梳上的势增长）。**定义实际算子 $(K_ah)(u)=\frac13\sum_{k=0}^2h(a\cdot U^ku)$。则 $K_af=f+q(a)$、$K_ag=g+r(a)$，从而对全部 $n\ge0$，

$$
3^{-n}\sum_{\sigma\in\Sigma_n}f(H_n^\sigma(a;u))=f(u)+nq(a),
\quad
3^{-n}\sum_{\sigma\in\Sigma_n}g(H_n^\sigma(a;u))=g(u)+nr(a).
\tag{12.3}
$$

**证明。**反复使用 (12.2)；每次只作有限三分支平均，常数函数被 $K_a$ 保持。右梳递推给其实际括号。

**命题 12.3（减去单位势可破坏非负性）。**非负势 $f$ 不保证 $f-f(1)$ 非负。

**证明。**取合法模型 $M=(\mathbb C,+)$，$Ua=\omega a+t$、$c(a,b)=|a-b|^2$，并令 $m=t/(1-\omega)$。单位为 $0$，其轨道为 $m(1-\omega^n)$，任意移位不变均值在这个三周期序列上均为三项平均。因此

$$
f(a)=|a-m|^2+|m|^2,\qquad f(1_M)=2|m|^2.
$$

若 $t\ne0$，实际标签 $a=m$ 给 $f(m)-f(1_M)=-|m|^2<0$。故单位轨道势不能经此减常数就被当成新的非负平方范数。

**对应 12.4（归约结果与未证边界）。**`repo-derived`：右梳复制在另一个满足完整 (R) 的真实单位模型中精确保留原比较矩阵，并把全部单位轨道费用压至任意小；外移复制给精确的未来双向测试域；缺陷形式被定位在两个非平凡三角色；单位轨道势满足实际 Poisson 方程。有限乘积、有限平均、Fourier 投影和移位均值是通常工具，不主张其文献优先权。这些关系仍未给问题 4.2 的双侧根性、五点负型或完整仿射分类；也不供应实际非零准备、参考、全效果、联合或时间接口。未来测试域的回拉、上下文读数对小费用的控制及非平凡缺陷通道的消去仍是证明义务。

## 追加锚（本行以下为增补区）

## 13. 有向三角条件给出的定量上下文控制

**定义 13.1（有向三点条件）。**沿用定义 1.1 的全部原始前件与完整关系 (R)，置 $d(x,y)=\sqrt{c(x,y)}$。额外条件 $\mathrm{DT}$ 是

$$
d(x,z)\le d(x,y)+d(y,z)\qquad(x,y,z\in M).
\tag{13.1}
$$

此处不预设对称性，也不要求零费用分离不同标签。$\mathrm{DT}$ 是本节与下一节新增的承重前件，尚未证明它由原始 (R) 推出。

**引理 13.2（双向小费用控制全部行列）。**若有 $\mathrm{DT}$，且 $d(x,y),d(y,x)\le\delta$，则对全部 $z$，

$$
\begin{aligned}
|d(x,z)-d(y,z)|&\le\delta,\\
|d(z,x)-d(z,y)|&\le\delta,\\
|c(x,z)-c(y,z)|&\le\delta(2d(y,z)+\delta),\\
|c(z,x)-c(z,y)|&\le\delta(2d(z,y)+\delta).
\end{aligned}
\tag{13.2}
$$

**证明。**三角条件分别给 $d(x,z)\le\delta+d(y,z)$ 及 $d(y,z)\le\delta+d(x,z)$；列方向交换相应输入。再用平方差分解，以及两数之和不超过较指定一项的两倍加 $\delta$，得到后两式。这是非负实数的运算，不使用自由空间中尚未正定的 $B$ 的 Cauchy–Schwarz 不等式。

**命题 13.3（单位右因子缺陷的显式界）。**置 $p=p_j$、$\delta=\max\{\sqrt{q(p)},\sqrt{r(p)}\}$，并定义

$$
H_c(a,p;z)=c(ap,z)-c(a,z)-c(p,z)+r(z)-q(ap)+q(a)+q(p).
\tag{13.3}
$$

若有 $\mathrm{DT}$，则对全部 $a,z$ 和 $j\ge0$，

$$
\begin{aligned}
|H_c(a,p;z)|
&\le2\delta\left[
\sqrt3\bigl(\sqrt{c(a,z)}+\sqrt{q(a)}\bigr)+\sqrt{r(z)}
\right]+8\delta^2,\\
|H_{c^{\mathsf T}}(a,p;z)|
&\le2\delta\left[
\sqrt3\bigl(\sqrt{c(z,a)}+\sqrt{r(a)}\bigr)+\sqrt{q(z)}
\right]+8\delta^2.
\end{aligned}
\tag{13.4}
$$

这里 $c^{\mathsf T}(x,y)=c(y,x)$；它的锚定费用是 $q^{\mathsf T}=r$、$r^{\mathsf T}=q$。

**证明。**式 (10.5) 给 $d(ap,a),d(a,ap)\le\sqrt3\,\delta$。在 (13.3) 中，将读数分为 $c(ap,z)-c(a,z)$、$c(p,z)-c(1,z)$、$q(ap)-q(a)$ 及 $q(p)$。引理 13.2 分别给三个平方差的上界

$$
2\sqrt3\,\delta\sqrt{c(a,z)}+3\delta^2,\qquad
2\delta\sqrt{r(z)}+\delta^2,\qquad
2\sqrt3\,\delta\sqrt{q(a)}+3\delta^2.
$$

最后 $q(p)\le\delta^2$，合计得到第一式。转置核仍满足完整 (R) 及 $\mathrm{DT}$，同一推导给第二式。没有将小费用无条件解释为上下文不可区分。

## 14. 保留有限核的极限给出完整三点几何桥

**定理 14.1（原始关系类中的有向三角分类）。**在定义 1.1 与完整关系 (R) 下，若有 $\mathrm{DT}$，则存在复 Hilbert 空间 $H$ 与映射 $F:M\to H$，满足

$$
F1=0,\qquad F(ab)=Fa+Fb,\qquad
c(a,b)=\|Fa-Fb\|^2,\qquad
FUa=\omega Fa+t,\quad t=FU1.
\tag{14.1}
$$

因此 $c$ 的对称性也是结论。零模型与非忠实原档案包含在内；原始括号、次序与记录没有被删除。

**证明。**固定任意有限原标签 $a_1,\ldots,a_m$。在定理 9.3 的全部数组模型上，置

$$
d_N=\sqrt{c_N},\qquad \eta_N=\sqrt{\Omega(1)/N},\qquad
\eta=\sqrt{\Omega(1)}.
$$

逐坐标的 $\mathrm{DT}$ 与有限实数数组的加权 $\ell^2$ Minkowski 不等式给

$$
d_N(f,h)\le d_N(f,g)+d_N(g,h).
\tag{14.2}
$$

定理 9.3 同时保留原比较矩阵，并将单位叶锚到真实单位的双向费用和控制为 $\eta_N^2$。因此

$$
\begin{aligned}
d_N(\Gamma_Na,\mathbf1)&\le\sqrt{q(a)}+\eta_N,\\
d_N(\mathbf1,\Gamma_Na)&\le\sqrt{r(a)}+\eta_N.
\end{aligned}
\tag{14.3}
$$

这里使用真实乘法单位 $\mathbf1$，不是第 10 节的外移展开基点。式 (14.3) 补出了原始 (R) 单独尚未提供的预算。

令 $\mathcal T$ 是由变量 $x_1,\ldots,x_m$、单位符号、二元运算和一元符号 $U$ 生成的自由含幺项代数；仅施加双侧单位恒等式，保留其余括号和次序。它可数。在第 $N$ 个模型中取 $x_i\mapsto\Gamma_Na_i$、$1_{\mathcal T}\mapsto\mathbf1$，实际递归求值得到 $s_N$。即使某个 $a_i$ 原来等于 $1$，变量 $x_i$ 与单位符号也不在语法中预先合并。

取 $\mathcal T$ 的单位约简正规形：单位符号、变量与 $Us$ 都是正规项；两个非单位正规项的有序二元节点也是正规项。含单位因子的乘积先按双侧单位律约简，不对 $U1_{\mathcal T}$ 作额外约简。各项有唯一这样的正规形。只在这些正规形上递归定义有限预算

$$
\begin{aligned}
R(1_{\mathcal T})&=0,\\
R(x_i)&=\max\{\sqrt{q(a_i)},\sqrt{r(a_i)}\}+\eta,\\
R(Us)&=R(s)+\eta,\\
R(st)&=\sqrt{3\bigl(R(s)^2+R(t)^2\bigr)}\qquad(s,t\ne1_{\mathcal T}).
\end{aligned}
\tag{14.4}
$$

因此对任意 $s,t\in\mathcal T$ 都有 $R(st)\le\sqrt{3(R(s)^2+R(t)^2)}$；有单位因子时，左端就是另一因子的预算，而右端为其 $\sqrt3$ 倍。这一不等式不把表达式树复杂度当作含幺等价类上无条件成立的递推等式。对所有 $N\ge1$ 及每个固定正规项，有

$$
d_N(s_N,\mathbf1),d_N(\mathbf1,s_N)\le R(s),\qquad
c_N(s_N,t_N)\le3\bigl(R(s)^2+R(t)^2\bigr).
\tag{14.5}
$$

变量情形来自 (14.3)。标记情形用同步等距及 (14.2)：

$$
d_N(U_Ns_N,\mathbf1)
\le d_N(U_Ns_N,\mathbf p_1)+d_N(\mathbf p_1,\mathbf1)
=d_N(s_N,\mathbf1)+d_N(\mathbf p_1,\mathbf1),
$$

反向同理；两种单位费用均不超过 $\eta_N$。两个非单位正规子项的乘法情形用 (R) 的第零项，给 $q_N(st)\le3(q_N(s)+q_N(t))$ 及其反向式；有单位因子时，乘积先约简为另一子项，其预算不变。最后的有序项对界使用式 (1.2)。所以预算允许随固定项的复杂度增长，却不随 $N$ 增长；初始预算只需要原有限标签到单位的读数及 $\Omega(1)$。

枚举 $\mathcal T$ 的全部有序项对，用 (14.5) 逐个取收敛子列，再取对角子列 $N_\ell\to\infty$，得到处处有限的核

$$
c_\infty(s,t)=\lim_{\ell\to\infty}c_{N_\ell}(s_{N_\ell},t_{N_\ell}).
\tag{14.6}
$$

非负性、零对角、每条 $\mathrm{DT}$ 和每条完整四变量 (R) 都只涉及有限个连续标量表达式，故在同一个项代数上保留。特别，没有将收敛仅限于初始比较矩阵，也没有假设 $\Gamma_N$ 保持运算。

令 $p_1^{\mathcal T}=U1_{\mathcal T}$。定理 9.3 的单位轨道界给

$$
c_\infty(p_1^{\mathcal T},1_{\mathcal T})
=c_\infty(1_{\mathcal T},p_1^{\mathcal T})=0.
\tag{14.7}
$$

在此极限模型中定义

$$
s\sim t\quad\Longleftrightarrow\quad
c_\infty(s,t)=c_\infty(t,s)=0.
\tag{14.8}
$$

三角条件使其成为等价关系，且引理 13.2 在 $\delta=0$ 时保证等价标签的全部行、列读数相同。式 (1.2) 的第零项界保证二元运算保此等价：若 $s\sim s'$、$t\sim t'$，则 $st\sim s't'$。同步等距保证 $Us\sim Ut$。因此可合法取得含幺 magma $\mathcal T/{\sim}$、其有限有向核及诱导标记；完整 (R) 也下降。由 (14.7)，商上的标记严格固定商单位。

现在直接应用已合并的《无结合律的双端三相比较：可见代数与复几何共同生成》定理 1.3，得到此商核的复 Hilbert 表示，因而其核对称且全有限负型。这一步不依赖单位轨道根性归约，也不要求原始 $U$ 满射。

初始变量仍精确保留

$$
c_\infty(x_i,x_j)=c(a_i,a_j).
\tag{14.9}
$$

所以原来的任意有限比较矩阵都对称且条件负型。原有限标签集任意，故原 $c$ 对称且全有限负型。最后应用已合并的《任意标记的五点正性桥梁与仿射复几何》定理 1.3，取得原模型上的 (14.1)。证毕。整个取商只发生在已经证明三角条件的极限模型中；没有从原始小费用直接取商，也没有回拉未经证明的运算同态。

**定义 14.2（三标签负型条件）。**$\mathrm N_3$ 要求 $c$ 对称，且对每个 $n\le3$、每组原标签 $a_1,\ldots,a_n$ 及全部零和实系数 $\alpha_1,\ldots,\alpha_n$，有 $\sum_{i,j}\alpha_i\alpha_jc(a_i,a_j)\le0$。

**引理 14.3（三标签负型与平方根三角条件）。**对任何对称、非负、零对角核，$\mathrm N_3$ 当且仅当 $\sqrt c$ 满足三角不等式。

**证明。**对三标签 $x_0,x_1,x_2$，写 $d_{ij}=\sqrt{c(x_i,x_j)}$。零和系数写成 $(-u-v,u,v)$，其负型二次式等于 $-2(u,v)G(u,v)^{\mathsf T}$，其中

$$
G=
\begin{pmatrix}
d_{01}^2 & (d_{01}^2+d_{02}^2-d_{12}^2)/2\\
(d_{01}^2+d_{02}^2-d_{12}^2)/2 & d_{02}^2
\end{pmatrix}.
\tag{14.10}
$$

对角元非负，故 $G$ 半正定当且仅当 $|d_{01}^2+d_{02}^2-d_{12}^2|\le2d_{01}d_{02}$，亦即 $|d_{01}-d_{02}|\le d_{12}\le d_{01}+d_{02}$。这正是该三标签配置的全部三角不等式，包含重复标签及退化情形。

**推论 14.4（原始关系类中的三点桥与反例定位）。**在完整原始前件及 (R) 下，

$$
\mathrm{DT}\ \Longleftrightarrow\ \mathrm N_3
\ \Longleftrightarrow\ \mathrm N_5
\ \Longleftrightarrow\ \mathrm N_{\rm fin}
\ \Longleftrightarrow\ \mathrm{BR}
\ \Longleftrightarrow\ \text{存在 (14.1) 的表示}.
\tag{14.11}
$$

若某个原始 (R) 模型不具有目标表示，则必有三个不同的有序标签 $x,y,z$ 满足

$$
\sqrt{c(x,z)}>\sqrt{c(x,y)}+\sqrt{c(y,z)}.
\tag{14.12}
$$

**证明。**$\mathrm{DT}$ 经定理 14.1 给表示，表示给全部其余条件；$\mathrm N_3$ 经引理 14.3 给 $\mathrm{DT}$；其余等价复用既有五点桥梁。反例定位是定理 14.1 的逆否；三标签中任意两者相同都会使 (14.12) 不可能，故可取三个不同标签。这里未证明对称性或二标签条件单独充分，也未主张三标签数最小。

**问题 14.5（剩余的三点关系）。**原始 (R) 是否自行推出 $\mathrm{DT}$ 仍未解决。式 (14.11) 降低了充分有限正性条件的标签数，不把新增的三角前件算作原关系的后果。完整条件几何入口是 (R) 加 $\mathrm{DT}$；它不等于原始量子起源目标已经完成。

## 15. 合法仿射模型中的有界调和花纹

**命题 15.1（单个实际平均算子不必有 Liouville 性）。**存在满足全部原始前件与完整 (R)、且 $U1_M\ne1_M$ 的模型，同时具有连续、非负、有界、非常数的 $h$ 与非负势 $f$，满足

$$
hU=h,\qquad K_{a_\star}h=h,\qquad
0\le h\le f,\qquad fU=f,\qquad K_{a_\star}f=f+1.
\tag{15.1}
$$

**证明。**取 $M=(\mathbb C,+)$，原单位 $1_M=0$，$Uz=\omega z+1$、$c(z,w)=|z-w|^2$，并取实际背景 $a_\star=1\in\mathbb C$。标记迭代的两端差为 $\omega^k(u-v)$，三角色求和立即给完整 (R)，而 $U1_M=1\ne0$。令

$$
\mathcal L=\mathbb Z+\omega\mathbb Z,\qquad
h(z)=\operatorname{dist}(z,\mathcal L)^2.
\tag{15.2}
$$

这是连续的非负函数。将任意 $z$ 按格基 $1,\omega$ 写成整数部分与有界基本平行四边形中的余项，得 $h$ 有界；$h(0)=0$、$h(1/2)>0$ 给非常数。格满足 $\omega\mathcal L=\mathcal L$、$1+\mathcal L=\mathcal L$，所以 $U$ 及每个 $z\mapsto a_\star+U^kz$ 都是保持该格的欧氏等距变换，故逐项有 $hU=h$、$h(a_\star+U^kz)=h(z)$，从而 $K_{a_\star}h=h$。

单位轨道为 $p_0=0,p_1=1,p_2=1+\omega$、三步重复。置 $m=1/(1-\omega)$，则第 12 节的实际移位均值势为

$$
f(z)=\frac13\sum_{j=0}^2|z-p_j|^2
=|z-m|^2+|m|^2.
\tag{15.3}
$$

$U^kz=m+\omega^k(z-m)$，所以三项平方平均给 $fU=f$ 与 $K_af=f+|a|^2$，特别 $K_{a_\star}f=f+1$。各 $p_j$ 均在格中，故 $h(z)\le|z-p_j|^2$ 对每个 $j$ 成立，平均后得 $h\le f$。

**对应 15.2（方法反例的范围）。**本例具有完整复表示，乘法缺陷在可见表示中为零，即自由差空间中的缺陷属于双侧根；$h$ 不是一个被证明来自非零乘法缺陷的函数，也不是非零有界 (R) 核。它排除的是：仅由一个 $K_a$ 的非负 Poisson 势、势的线性增长、$U$ 不变性、连续性和势支配，就断言全部有界调和函数恒定。若要消去具体缺陷，还须证明它具有额外的实际通道关系或足够的可达性。该例不反驳原始分类猜想。

**对应 15.3（新增内容、来源与量子接口）。**本批的条件几何推导与实际平均算子路线排除是仓内综合推导；有限 Minkowski 不等式、可数对角子列、零费用商与二维 Gram 判据是标准工具，不主张文献优先权。新增承重方向是 (R) 加有向三角条件足以给完整仿射分类，证明只消费本卷的核保持复制及两份已合并的分类前置。三点负型不在任意核上推出全有限负型，式 (14.11) 始终保留完整 (R)。

分类后的实际纠偏配方 $V(a)=U(a\cdot p_2)$ 仍给 $F(Va)=\omega Fa$；三条实际历史 $a\cdot V^ku$ 的表示、事件核与总核各自的表示及支配、非零准备与完整效果、全成对细记录校准与共同纠偏相位、参考和联合张量、实际时间接口，继续按前述五点桥梁第 6 节逐项保留其前件。这里没有仅以三个形式向量的子集和宣称八个原事件已有来源，也没有从静态核存在推出全部物理操作。原始 (R) 到三点三角条件的蕴涵尚待证明或反驳。

## 追加锚（本行以下为增补区）

## 16. 原始关系把三角偏差放大到无界

**定义 16.1（三角超额与有限来源闭包）。**只用定义 1.1 及完整 (R)，仍置 $d=\sqrt c$，不预设三角条件。对三个有序标签定义非负超额

$$
\Delta(x,y,z)=\bigl[d(x,z)-d(x,y)-d(y,z)\bigr]_+,
\qquad [t]_+=\max\{t,0\}.
\tag{16.1}
$$

记 $\langle a,b,c\rangle$ 为包含真实单位及 $a,b,c$、并对原二元运算和 $U$ 闭合的最小子代数。它保留实际括号与次序。

**定理 16.2（实际右梳中的三角超额放大）。**对任意 $a,b,c$ 和 $N\ge1$，置 $A_\sigma=H_N^\sigma(a;1)$、$B_\sigma=H_N^\sigma(b;1)$、$C_\sigma=H_N^\sigma(c;1)$，则

$$
3^{-N}\sum_{\sigma\in\Sigma_N}
\Delta(A_\sigma,B_\sigma,C_\sigma)^2
\ge N\Delta(a,b,c)^2.
\tag{16.2}
$$

因此至少一条相位历史满足 $\Delta(A_\sigma,B_\sigma,C_\sigma)\ge\sqrt N\,\Delta(a,b,c)$。所有这些标签都属于同一个 $\langle a,b,c\rangle$。

**证明。**在有限相位集合上取概率权 $3^{-N}$，并记其标量 $\ell^2$ 范数为 $\|\cdot\|_{2,N}$。对每个 $\sigma$，非负实数的定义立即给

$$
d(A_\sigma,C_\sigma)
\le d(A_\sigma,B_\sigma)+d(B_\sigma,C_\sigma)
+\Delta(A_\sigma,B_\sigma,C_\sigma).
\tag{16.3}
$$

这里只把缺失的三角关系逐项写成带实际超额的恒真不等式。由有限实数组的单调性、Minkowski 以及定理 9.2，

$$
\sqrt N\,d(a,c)
\le\sqrt N\,d(a,b)+\sqrt N\,d(b,c)
+\bigl\|\Delta(A_\sigma,B_\sigma,C_\sigma)\bigr\|_{2,N}.
\tag{16.4}
$$

若原超额为零，(16.2) 来自非负性；若为正，将前三项移项并平方即得 (16.2)。有限集合上最大值不小于其均方根，给单条历史的结论。证明只消费完整 (R) 已供应的精确右梳费用，不使用 $d$ 的三角不等式、核的对称性、正定性或 $\Gamma_N$ 的运算同态。

**推论 16.3（有界超额已经充分）。**在原始 (R) 类内，以下条件都等价于定理 14.1 的完整仿射表示：

1. $\Delta$ 在 $M^3$ 上有一个有限的统一上界。
2. 对每个 $a,b,c$，$\Delta$ 在 $\langle a,b,c\rangle^3$ 上有有限上界，允许上界随这三个来源变化。
3. 对每个 $a,b,c$，存在趋于无穷的整数序列 $N_j$，使实际同步右梳超额的均方根为 $o(\sqrt{N_j})$。

**证明。**表示给 $\mathrm{DT}$，所以全部超额为零，供应三项条件。第一项推出第二项。第二项对 (16.2) 左端给一个与 $N$ 无关的上界，故 $N\to\infty$ 迫使原超额为零。第三项直接由 (16.2) 迫使原超额为零。后两项都是对任意原三标签成立，故给全部 $\mathrm{DT}$，再用定理 14.1。这里没有将某个固定有限截断的预算当作所有重复次数的统一预算。

**推论 16.4（反例的必要无界特征与有限精度界）。**任何不具有目标表示的完整原始 (R) 模型，都有三个不同的原标签，使三角超额在其共同有限来源闭包内无界。特别，全域超额上确界只能为 $0$ 或 $+\infty$，不存在有限正值。若某一深度 $N$ 的全部同步右梳超额都不超过 $K_N$，则原超额不超过 $K_N/\sqrt N$；有限预算只提供这个明确的近似界。

**对应 16.5（较弱入口与原目标）。**有界超额对一般非负零对角核严格弱于精确三角：例如三标签的对称核，平方根边长取 $1,1,3$，超额非零但全域有界；该例不满足完整 (R)，不是原始分类反例。推论 16.3 说明完整 (R) 会把这种有界容差压到零，因而不必一开始就要求逐三标签精确三角。这里仍未证明原始 (R) 自行供应任一有界或次平方根增长前件；非表示模型是否存在仍未解决。新增推导是定理 9.2 与有限实数组范数不等式的仓内综合，不主张文献优先权；量子过程与操作继续保留对应 15.3 的全部实际接口前件。

## 追加锚（本行以下为增补区）

## 17. 实际单位碰撞与全部探针上的标记消去

**引理 17.1（同层实际历史的交叉等距）。**只用定义 1.1 与完整 (R)，令 $Sx=U^3x$、$Tx=x\cdot p_3$，则

$$
c(Sx,Sy)=c(Sx,Ty)=c(Tx,Sy)=c(Tx,Ty)=c(x,y).
\tag{17.1}
$$

因此对任意两个长度均为 $n$ 的有序复合词 $W,V\in\{S,T\}^n$，有 $c(Wx,Vy)=c(x,y)$。

**证明。**固定背景与右输入，序列 $f_j=c(a\cdot U^ju,b\cdot U^jv)$ 由 (R) 与同步等距满足 $f_j+f_{j+1}+f_{j+2}=3c(a,b)+3c(u,v)$，故 $f_{j+3}=f_j$。分别取 $(a,b,u,v)=(1,y,x,1),(x,1,1,y),(x,y,1,1)$，得到两个混合式与 $T,T$ 式；$S,S$ 式来自同步等距。逐对消去两个词的最外层操作，归纳得到同层结论。此式未将未推进探针等同于推进后的探针。

**定理 17.2（跨模三的实际单位碰撞）。**若存在 $r\ge0$、$h\ge1$，满足 $3\nmid h$ 以及原对象的实际等式 $p_{r+h}=p_r$，则存在复 Hilbert 空间与映射 $F$，满足

$$
F1=0,\qquad F(ab)=Fa+Fb,\qquad
c(a,b)=\|Fa-Fb\|^2,\qquad FUa=\omega Fa.
\tag{17.2}
$$

特别，$\Omega(1)=0$ 与仿射漂移 $t=0$ 都是结论。

**证明。**固定全部 $a,b,i,j$，置 $g_n=c(a p_{i+n},b p_{j+n})$。引理 17.1 证明中给出的周期式使 $g$ 三周期。实际碰撞使 $p_{n+h}=p_n$ 对全部 $n\ge r$ 成立，故 $g$ 的尾部还具有周期 $h$。由于 $\gcd(3,h)=1$，尾部的三个周期值相等，三周期性再使全部 $g_n$ 相等。将其代入 (R)，得

$$
c(a p_i,b p_j)=c(a,b)+c(p_i,p_j).
\tag{17.3}
$$

取 $(a,b,i,j)=(p_\ell,1,0,\ell)$，左端为零，故 $q(p_\ell)+r(p_\ell)=0$。非负性给两项分别为零，再由 (1.2) 得 $c(p_i,p_j)=0$。所以

$$
c(a p_i,b p_j)=c(a,b)\qquad(a,b\in M,\ i,j\ge0).
\tag{17.4}
$$

令 $i$ 或 $j$ 为零，已经证明任意右插入 $p_\ell$ 在全部原探针的两种配对次序下不可见；这一步没有从零费用擅取商。

定义实际辅助标记 $\widehat U1=1$，对 $a\ne1$ 置 $\widehat Ua=Ua$。对任意 $u$ 及 $k=0,1,2$，若截至第 $k$ 步原 $U$ 轨道没有命中 $1$，两个迭代相同；若首次在第 $j\le k$ 步命中 $1$，则 $\widehat U^ku=1$、$U^ku=p_{k-j}$。因此由 (17.4)，将 $U$ 换成 $\widehat U$ 后，(R) 左端每个费用分别保持原值。同一 magma 与同一核遂满足严格固定单位的完整关系。

调用已合并《无结合律的双端三相比较：可见代数与复几何共同生成》定理 1.3，得到同一核的表示及 $F\widehat Ua=\omega Fa$。已知 $c(p_1,1)=0$，此时由平方距离表示得 $Fp_1=0$。原 $U$ 与 $\widehat U$ 只在对象 $1$ 处可能不同，其 $F$ 像在该处也相同，故同一个 $F$ 满足 (17.2)。证毕。

**推论 17.3（反例单位轨道的三色限制）。**任何非表示的原始 (R) 模型，其单位轨道上都有良定义的着色 $\chi(p_n)=n\bmod3$；亦即 $p_i=p_j$ 必有 $i\equiv j\pmod3$。该着色仅定义于实际单位轨道，不是全 $M$ 的相位函数或同态。定理 17.2 的实际碰撞不能换成双向零费用。

## 18. 实际原像终端给出的精确单位复制

**定义 18.1（单位的任意深度原像）。**本节额外对象条件为

$$
1\in\bigcap_{n\ge1}U^n(M).
\tag{18.1}
$$

等价地，对每个 $N\ge1$ 可选实际 $z_N\in M$，使 $U^{2N}z_N=1$。这些原像不要求彼此兼容，不要求原 $U$ 可逆或保持乘法。

**定理 18.2（精确保核且保真实单位的实际历史）。**在 (18.1) 下，存在满足全部原始前件及 (R) 的有限直积模型 $(M_N,c_N,U_N)$ 及映射 $\Lambda_N:M\to M_N$，满足

$$
\Lambda_N1=\mathbf1,\qquad
c_N(\Lambda_Na,\Lambda_Nb)=c(a,b),\qquad
q_N(\Lambda_Na)=q(a),\quad r_N(\Lambda_Na)=r(a).
\tag{18.2}
$$

这些结论不使用任何三角条件。

**证明。**定义三个实际操作

$$
A_k(a,u)=U^{2-k}(a\cdot U^ku),\qquad k=0,1,2.
\tag{18.3}
$$

同步等距与 (R) 给 $\frac13\sum_k c(A_k(a,u),A_k(b,v))=c(a,b)+c(u,v)$，而双侧单位给严格对象等式 $A_k(1,u)=U^2u$。递归定义

$$
K_0(a;z)=z,\qquad
K_N^\sigma(a;z)=
A_{\sigma_1}\bigl(a,K_{N-1}^{(\sigma_2,\ldots,\sigma_N)}(a;z)\bigr).
\tag{18.4}
$$

逐层有限平均与单位代入分别给

$$
\begin{aligned}
3^{-N}\sum_{\sigma\in\Sigma_N}
c(K_N^\sigma(a;z),K_N^\sigma(b;w))&=Nc(a,b)+c(z,w),\\
K_N^\sigma(1;w)&=U^{2N}w.
\end{aligned}
\tag{18.5}
$$

取 $M_N=M^{\Sigma_N}$，保留逐坐标的原乘法与原 $U$，真实单位为 $\mathbf1$，并置

$$
c_N(X,Y)=\frac1{N3^N}\sum_\sigma c(X_\sigma,Y_\sigma),
\qquad
\Lambda_Na=(K_N^\sigma(a;z_N))_\sigma.
\tag{18.6}
$$

逐坐标求和保留完整 (R)。终端项 $c(z_N,z_N)=0$，而单位历史严格等于 $U^{2N}z_N=1$，故得全部 (18.2)。

对任意 $j\ge0$，将另一历史终端取为 $U^jz_N$，其单位历史逐条等于 $p_j$。同步 $U^{2N}$ 等距给 $c(z_N,U^jz_N)=r(p_j)$，反向为 $q(p_j)$，从而还有精确探针式

$$
c_N(\Lambda_Na,\mathbf p_j)=q(a)+\frac{r(p_j)}N,\qquad
c_N(\mathbf p_j,\Lambda_Na)=r(a)+\frac{q(p_j)}N.
\tag{18.7}
$$

没有删除或更换终端费用，也没有断言 $\Lambda_N$ 保持乘法或标记。

**定理 18.3（全部固定项的有限预算与零漂移归约）。**在 (18.1) 下，每个原有限比较矩阵都能在某个处处有限、非负、零对角、满足全部原始 (R) 且 $\Omega(1)=0$ 的可数含幺项模型中精确保留。

**证明。**取 $v=Uz_1$，则 $Uv=1$，同步等距给 $q(v)=r(p_1)$、$r(v)=q(p_1)$。对任意实际数组 $s\in M_N$，原上界 (1.2) 给

$$
\begin{aligned}
q_N(U_Ns)&=c_N(s,\mathbf v)
\le3\left(q_N(s)+\frac{q(p_1)}N\right),\\
r_N(U_Ns)&\le3\left(r_N(s)+\frac{r(p_1)}N\right),\\
q_N(st)&\le3(q_N(s)+q_N(t)),\\
r_N(st)&\le3(r_N(s)+r_N(t)).
\end{aligned}
\tag{18.8}
$$

固定原标签 $a_1,\ldots,a_m$，用自由含幺项代数的唯一单位约简正规形，解释 $x_i\mapsto\Lambda_Na_i$、单位符号为真实 $\mathbf1$。置 $C_1=\max\{q(p_1),r(p_1)\}$，在正规形上递归定义

$$
\begin{aligned}
B(1)&=0,&
B(x_i)&=\max\{q(a_i),r(a_i)\},\\
B(Us)&=3(B(s)+C_1),&
B(st)&=3(B(s)+B(t))\quad(s,t\ne1).
\end{aligned}
\tag{18.9}
$$

含单位因子的乘积先约简，故任意 $s,t$ 都有 $B(st)\le3(B(s)+B(t))$，而非无条件的递推等式。式 (18.2)、(18.8) 逐项给

$$
q_N(s_N),r_N(s_N)\le B(s),\qquad
0\le c_N(s_N,t_N)\le3(B(s)+B(t)).
\tag{18.10}
$$

每个预算有限且不依赖 $N$。对全部可数有序项对取共同对角子列，得到处处有限核 $c_\infty$；非负、零对角及每条完整 (R) 都通过有限标量等式传到极限。单位符号始终是真单位，且

$$
q_N(\mathbf p_j)=q(p_j)/N,\qquad
r_N(\mathbf p_j)=r(p_j)/N.
\tag{18.11}
$$

故 $\Omega_\infty(1)=0$，同时 $c_\infty(x_i,x_j)=c(a_i,a_j)$。此构造没有进行零费用商。

**推论 18.4（原像类的剩余关口）。**若全部零漂移原始 (R) 模型都具有完整表示，则全部满足 (18.1) 的原始模型也具有完整仿射表示。反之，若满足 (18.1) 的模型中有一个三标签三角违反，则存在完整零漂移原始 (R) 模型，精确保留这组三标签的违反。

**证明。**第一方向对每个原有限矩阵用定理 18.3，再调用已合并的任意标记有限正性桥。第二方向仅对违反的三个标签应用同一定理。没有把一个尚未供应的坏模型宣告为已经构造的反例。一般 $\Omega(1)=0$ 仍未证明足够；式 (18.7) 对初始变量的常标记探针读数也尚未传播到全部实际项和全部上下文。

## 19. 可返回的有限右标记上下文

**定义 19.1（实际成对右标记轨道）。**置 $R_i(x)=x p_i$、$A_{ij}(x,y)=(R_i x,R_j y)$。记 $\mathcal O_{(x,y)}$ 为全部 $A_{ij}$ 的有限复合所生成的实际前向轨道，包括长度为零的复合；所有括号按实际操作保留。

**引理 19.2（一个有界上下文轨道迫出零漂移）。**若存在一个 $\mathcal O_z$，使 $c$ 在该轨道上有有限统一上界，则 $c(p_i,p_j)=0$ 对全部 $i,j$ 成立，因而 $\Omega(1)=0$。

**证明。**将 $c((x,y))$ 简写为 $c(x,y)$。原 (R) 给

$$
\sum_{k=0}^2c(A_{i+k,j+k}w)=3c(w)+3c(p_i,p_j).
\tag{19.1}
$$

令 $C=\sup_{w\in\mathcal O_z}c(w)<\infty$。给定 $\varepsilon>0$，取 $c(w)>C-\varepsilon$。三个后继都在同一轨道，故 $3c(w)+3c(p_i,p_j)\le3C$。于是 $0\le c(p_i,p_j)<\varepsilon$；任意 $\varepsilon$ 给所需结论。

**定理 19.3（有限且强连通的上下文分类）。**若每个 $\mathcal O_z$ 都有限，且其由实际 $A_{ij}$ 动作构成的有向图强连通，则原模型具有 (17.2) 的完整表示。

**证明。**引理 19.2 先给 $c(p_i,p_j)=0$。在任意一个有限轨道取最大值 $C$；最大点处 (19.1) 的三项均不超过 $C$，其平均恰为 $C$，故每个 $A_{ij}$ 后继仍是最大点。强连通性使每个状态都可从最大点到达，所以 $c$ 在该轨道上恒定。特别，$c(a p_i,b p_j)=c(a,b)$ 对全部原标签成立。此后使用定理 17.2 从 (17.4) 起的辅助标记归约与同一 $F$ 恢复原 $U$ 的证明。没有从仅有的零费用直接推出行列一致。

**例 19.4（三个实际颜色可以仍然存在）。**取 $M=\mathbb C\times\mathbb Z/3$，

$$
(z,i)(w,j)=(z+w,i+j),\qquad
1=(0,0),\qquad
U(z,i)=(\omega z,i+1),\qquad
c((z,i),(w,j))=|z-w|^2.
\tag{19.2}
$$

三相正交消去交叉项，给完整 (R)。单位最小实际周期为三，故不满足定理 17.2 的跨模三碰撞；每个右标记仅在三色标签上作置换，全部成对轨道有限且强连通，故满足定理 19.3。整体费用无界。仅有限而不具返回性时，最大值传播未覆盖起点，不能省去该前件。

## 20. 任一统一正幂三角都会恢复平方根几何

**定理 20.1（正幂三点分类）。**在全部原始前件及完整 (R) 下，若存在对全模型统一的 $\alpha>0$，使

$$
c(x,z)^\alpha\le c(x,y)^\alpha+c(y,z)^\alpha
\qquad(x,y,z\in M),
\tag{20.1}
$$

则具有定理 14.1 的完整仿射表示。因此在原始 (R) 类内，存在任一这样的正指数，与 $\mathrm{DT}$ 及完整仿射表示等价。

**证明。**将指数降为 $\beta=\min\{\alpha,1/2\}$：非负实数的幂 $\beta/\alpha\le1$ 保三角。取第 9 节的原右梳数组模型，置 $D_N=c_N^\beta$。它是数组 $(c(X_\sigma,Y_\sigma)^\beta)_\sigma$ 的加权 $\ell^{1/\beta}$ 范数，故有限 Minkowski 保有向三角。记 $W=\Omega(1)$，核保持与单位预算给

$$
D_N(\Gamma_Na,\mathbf1)\le q(a)^\beta+(W/N)^\beta,\qquad
D_N(\mathbf1,\Gamma_Na)\le r(a)^\beta+(W/N)^\beta.
\tag{20.2}
$$

在第 14 节相同的单位约简正规形上，可取

$$
\begin{aligned}
B(1)&=0,\\
B(x_i)&=\max\{q(a_i)^\beta,r(a_i)^\beta\}+W^\beta,\\
B(Us)&=B(s)+W^\beta,\\
B(st)&=3^\beta
\bigl(B(s)^{1/\beta}+B(t)^{1/\beta}\bigr)^\beta
\quad(s,t\ne1).
\end{aligned}
\tag{20.3}
$$

一般乘积仍只用相应 $\le$ 界。同步等距、有向三角和 (R) 第零项给 $D_N(s_N,\mathbf1),D_N(\mathbf1,s_N)\le B(s)$，继而全部有序项对的 $c_N$ 有 $N$ 一致的有限界。

取全部项对的共同极限，保留完整 (R)、$c_\infty^\beta$ 的有向三角及单位轨道到真单位的双向零费用。此时双向零费用才成为等价关系，且三角条件给全部 $c_\infty^\beta$ 行列不变；正幂单射性再给全部 $c_\infty$ 行列不变。原第零项界与同步等距分别给乘法与 $U$ 同余。因此合法商上标记严格固定单位，调用固定单位分类，再由初始有限矩阵保持调用任意标记的有限正性桥，得到原模型的完整仿射表示。

**推论 20.2（指数边界与反例限制）。**非表示的原始 (R) 模型对每个 $\alpha>0$ 都存在三个不同的有序标签违反 (20.1)。若非零原始 (R) 模型满足 (20.1)，则必有 $\alpha\le1/2$，且其全部三角指数恰为 $(0,1/2]$。

**证明。**第一句是定理 20.1 的逆否。对第二句，分类后选 $q(a)>0$，实际标签 $1,a,aa$ 给 $c(1,aa)=4q(a)$ 与 $c(1,a)=c(a,aa)=q(a)$，故 $4^\alpha\le2$。平方根距离的全部不超过一的进一步幂均保三角，给完整指数区间。非零性与表示保证存在这样的 $a$。对一般核，$c(x,y)=|x-y|^4$ 在整条实线上有四分之一次幂三角而无平方根三角；该例不满足完整 (R)，仅说明这里使用的前件在一般核上更弱。

## 21. 实际关系的来源、量子消费者与未解边界

**对应 21.1（文献提供的结构及缺失映射）。**[D’Andrea–Landi–Lizzi，Tolerance relations and quantization](https://arxiv.org/pdf/2112.09698) 第 3.1 节引理 6、命题 7 在其有限容差代数中，将非传递的三点链与非幂结合联系起来；结论依赖具体截断卷积乘法，不是任意 magma 上的零费用传递定理。[Schupp–Szabo，An algebraic formulation of nonassociative quantum mechanics](https://arxiv.org/pdf/2311.03647v3) 定义 3.1、引理 3.3 及式 (3.6) 在包络代数上预设正线性泛函，并对任意复线性组合 $(z_1A+z_2B)^*(z_1A+z_2B)$ 使用正性；原实际历史的费用非负性尚未供应这个前件。[Schlather，An algebraic generalization of the entropy and its application to statistics](https://arxiv.org/pdf/2404.05854) 定义 3.22、命题 3.23 的广义 Cauchy–Schwarz 使用熵层面的结合、全域重复增长常数及非退化增长比条件；原右梳的平均增长尚未供应这些条件。这三项原作者稿的对应段落均可直接读取；它们没有闭合原始 (R) 到三点几何的缺口。本批实际历史与周期归约是仓内综合推导，不主张文献优先权。

**对应 21.2（几何候选与完整量子接口）。**本批给出的更弱条件几何入口是：完整二元比较关系 (R)，以及“存在一个统一正指数，使三点比较的该次幂可逐段相加”的约束。由定理 20.1，这足以恢复加法、复相位、平方距离与全有限强正 Gram；但尚未从 (R) 内生该正指数，故不宣称已经取得严格更简洁且完整的量子起源候选。

表示后的实际纠偏 $V(a)=U(a\cdot p_2)$ 给 $FVa=\omega Fa$，三条实际历史 $a\cdot V^ku$ 的像为 $Fa+\omega^kFu$。采用第二变量线性的内积约定，三次真实读数恢复

$$
\langle Fa,Fu\rangle
=\frac13\sum_{k=0}^2\omega^{-k}q(a\cdot V^ku).
\tag{21.1}
$$

总核与各实际事件核分别取得表示后，其强正支配与完整和式给唯一效果 $0\le E_e\le I$ 及 $K_e(a,b)=\langle Fa,E_eFb\rangle$；非零准备的归一化才给 Born 概率。全成对细记录校准、共同纠偏相位及完整记录和式才给最小输入空间上的复线性 Kraus 延拓。非零准备、原八事件的来源与完整性、全效果的实际可实现性、共同参考、联合张量、可组合过程及时间仍分别保留既有接口前件；静态表示不供应这些操作。

**问题 21.3（精确剩余区域）。**一般 $\Omega(1)=0$ 是否足以给全上下文行列识别，仍未解决。原 (R) 是否允许保核、全域有限、非负的扩展，使单位获得任意深度实际原像，也未解决；不能只形式倒置尚未证明保乘法的 $U$。第 16 节要求的同一三源闭包内有限或次平方根超额预算，仍未从原 (R) 单独取得。若非表示原模型存在，它必须同时满足单位轨道模三着色、至少一个右标记成对轨道不同时有限且强连通，以及对每个统一正幂的三标签三角失败；这些必要条件不构成反例存在证明。

**对应 21.4（直观图景）。**三盏灯轮流照同一对来源，完整配平要求三次比较的总量只按两端来源相加。新的外层补齐使每个空分支都准确走两步；若有足够深的真实空输入原像，每条空历史便能准确回到真正单位，所有固定配方的预算随之保住。若不同颜色真的合成同一个原对象，两个不相容的周期会迫使标记在所有探针下消失。一般世界里还缺的是：空历史费用为零，能否保证它在每个后续配方中都可替换；没有这条关系，就不能把局部看不见直接当成整体相同。

## 追加锚（本行以下为增补区）

## 22. 从实际右等距回到真实单位的无条件预算

**约定 22.1（本批的单位预算）。**继续只使用定义 1.1 与全部 (R)，简写

$$
\Omega=\Omega(1)=q(p_1)+q(p_2)+r(p_1)+r(p_2).
\tag{22.1}
$$

它不是任意 $a$ 的 $\Omega(a)$。推论 2.2 已给 $q(p_j)+r(p_j)\le\Omega$。以下不增加有向三角、对称性、正定性、单位原像或 $U$ 保乘法条件。

**引理 22.2（三倍数右标记的单位比较）。**若 $3\mid L$，则对全部 $a,b,y$ 有

$$
\begin{aligned}
c(a p_L,b p_L)&=c(a,b),\\
q(y)&\le3c(y,p_L)+3\Omega,\\
r(y)&\le3c(p_L,y)+3\Omega.
\end{aligned}
\tag{22.2}
$$

**证明。**令 $g_j=c(a p_j,b p_j)$。(R) 取右输入 $p_j,p_j$，给 $g_j+g_{j+1}+g_{j+2}=3c(a,b)$，故 $g_{j+3}=g_j$。又 $g_0=c(a,b)$，得到第一式。特别有 $q(y)=c(y p_L,p_L)$。对这一费用使用实际拆分 $(y\cdot p_L,p_L\cdot1)$ 与引理 1.2，得

$$
q(y)\le3\bigl(c(y,p_L)+q(p_L)\bigr).
$$

反向拆分 $(p_L\cdot1,y\cdot p_L)$ 给 $r(y)\le3(c(p_L,y)+r(p_L))$。用单位轨道预算结束证明。这是先作精确等距改写，再用实际乘法单项界；没有由小费用推出连续性或全行列识别。

**定理 22.3（任意标记与任意迭代的统一单位控制）。**对全部 $y,x$ 及 $j,n\ge0$，有

$$
\begin{aligned}
q(y)&\le9c(y,p_j)+12\Omega,&
r(y)&\le9c(p_j,y)+12\Omega,\\
q(U^nx)&\le9q(x)+12\Omega,&
r(U^nx)&\le9r(x)+12\Omega.
\end{aligned}
\tag{22.3}
$$

**证明。**选 $e\in\{0,1,2\}$ 使 $j+e$ 为三的倍数。引理 22.2 与同步等距给

$$
q(U^ey)\le3c(U^ey,p_{j+e})+3\Omega
=3c(y,p_j)+3\Omega.
$$

另一方面，$q(y)=c(U^ey,p_e)\le3q(U^ey)+3r(p_e)\le3q(U^ey)+3\Omega$，合并给第一式。转置核仍满足全部原关系，得到第二式。对任意 $n$，取 $L\ge n$ 且 $3\mid L$，则

$$
q(U^nx)\le3c(U^nx,p_L)+3\Omega
=3c(x,p_{L-n})+3\Omega
\le9q(x)+12\Omega.
$$

转置给反向结论。常数不含 $n$，也不需要未知的 $c(x,Ux)$ 或 $c(x,U^2x)$。

## 23. 任意有限比较矩阵的零漂移实现

**引理 23.1（同步右梳的真实单位预算）。**对 $\sigma\in\Sigma_N=\{0,1,2\}^N$，定义实际右梳

$$
H_0(a;z)=z,\qquad
H_N^\sigma(a;z)=a\cdot U^{\sigma_1}
H_{N-1}^{(\sigma_2,\ldots,\sigma_N)}(a;z).
\tag{23.1}
$$

写 $s_\sigma=\sum_i\sigma_i$，以 $\mathbb E_\sigma$ 表示同步均匀有限平均，则

$$
\begin{aligned}
\mathbb E_\sigma c(H_N^\sigma(a;z),H_N^\sigma(b;w))
&=Nc(a,b)+c(z,w),\\
H_N^\sigma(1;1)&=p_{s_\sigma},\\
\mathbb E_\sigma q(H_N^\sigma(a;z))
&\le9Nq(a)+9q(z)+12\Omega.
\end{aligned}
\tag{23.2}
$$

反向预算将 $q$ 换为 $r$。

**证明。**对最外层标记先取平均，(R) 把费用变成 $c(a,b)$ 加内层费用；对深度归纳，得到第一式。单位历史的实际等式由 $1\cdot U^ku=U^ku$ 逐层得到，不使用结合律。将定理 22.3 的第一式用于 $y=H_N^\sigma(a;z)$、$j=s_\sigma$，再用第一式与单位历史等式，得最后一式。全部来源使用同一 $\sigma$，没有把分别最优的历史混在一起。

**定理 23.2（有限矩阵的无条件零漂移实现）。**给定任意满足原始前件与全部 (R) 的模型，以及其中任意有限标签集 $A$，存在一个可数、由 $|A|$ 个来源及真实单位生成的含幺 $U$-magma 模型 $(\mathcal T,c_\infty,U)$，使全部原始前件与 (R) 成立，并满足

$$
\Omega_\infty(1)=0,\qquad
c_\infty(x_a,x_b)=c(a,b)\quad(a,b\in A).
\tag{23.3}
$$

这是一项有限比较矩阵的实现定理，不断言原 $M$ 到 $\mathcal T$ 有保运算或保单位的嵌入。

**证明。**对每个 $N\ge1$，取数组模型 $M_N=M^{\Sigma_N}$，乘法与 $U_N$ 均逐坐标采用原运算，真实单位为常值数组 $\mathbf1$，并置

$$
c_N(X,Y)=\frac1{N3^N}\sum_{\sigma\in\Sigma_N}c(X_\sigma,Y_\sigma).
\tag{23.4}
$$

逐坐标完整 (R) 求和后仍是完整 (R)，且其真实单位预算精确为 $\Omega_N=\Omega/N$。

为每个 $\sigma$ 统一选择 $e_\sigma\in\{0,1,2\}$，使 $L_\sigma=s_\sigma+e_\sigma$ 被三整除，定义

$$
\widetilde\Gamma_Na(\sigma)
=U^{e_\sigma}H_N^\sigma(a;1).
\tag{23.5}
$$

同一坐标中全部来源都采用同一 $e_\sigma$。同步等距与 (23.2) 给

$$
c_N(\widetilde\Gamma_Na,\widetilde\Gamma_Nb)=c(a,b),
\qquad \widetilde\Gamma_N1(\sigma)=p_{L_\sigma}.
\tag{23.6}
$$

每个 $L_\sigma$ 都可应用引理 22.2。因此先在原模型逐坐标估计，再除以 $N$ 取平均，得到

$$
\begin{aligned}
q_N(\widetilde\Gamma_Na)&\le3q(a)+3\Omega/N,\\
r_N(\widetilde\Gamma_Na)&\le3r(a)+3\Omega/N.
\end{aligned}
\tag{23.7}
$$

这里控制的是到真实数组单位 $\mathbf1$ 的费用。$\widetilde\Gamma_N1$ 无需等于 $\mathbf1$；它的双向单位费用由 (23.7) 控制。

取有限变量 $x_a$、单位符号、二元运算及一元符号 $U$ 上的自由含幺项代数 $\mathcal T$，只施加双侧单位恒等式。沿用第 14 节的唯一单位约简正规形；$U1$ 不约简为 $1$。在第 $N$ 个模型中令 $x_a$ 求值为 $\widetilde\Gamma_Na$，单位求值为真实 $\mathbf1$，再按实际运算递归求值为 $s_N$。

在正规形上定义与 $N$ 无关的有限预算

$$
\begin{aligned}
B(1)&=0,\\
B(x_a)&=3(q(a)+r(a))+6\Omega,\\
B(Us)&=9B(s)+24\Omega,\\
B(st)&=3(B(s)+B(t))\qquad(s,t\ne1).
\end{aligned}
\tag{23.8}
$$

一般乘积只用 $B(st)\le3(B(s)+B(t))$；有单位因子时先约简。式 (23.7) 给变量预算。在数组模型中应用定理 22.3，标记节点满足

$$
q_N(U_Ns_N)+r_N(U_Ns_N)
\le9(q_N(s_N)+r_N(s_N))+24\Omega/N.
$$

乘法节点用 (R) 第零项的两种次序，故归纳得到

$$
q_N(s_N)+r_N(s_N)\le B(s),\qquad
c_N(s_N,t_N)\le3(B(s)+B(t)).
\tag{23.9}
$$

枚举可数的全部有序项对，依次取收敛子列并取同一个对角子列 $N_\ell\to\infty$，定义 $c_\infty(s,t)=\lim_\ell c_{N_\ell}(s_{N_\ell},t_{N_\ell})$。式 (23.9) 保证每个坐标有限。非负性、零对角和每条完整四变量 (R) 都只涉及有限个连续标量表达式，故共同保留。$\Omega_N=\Omega/N$ 给 $\Omega_\infty(1)=0$，(23.6) 给原有限矩阵的精确保留。没有取零费用商，也没有预设来源映射保持运算。即使 $A$ 含原标签 $1$，变量 $x_1$ 也未被等同于新模型的真实单位。证毕。

**推论 23.3（全局分类恰好归约到零漂移三点问题）。**以下两项等价：每个原始 (R) 模型都有定理 14.1 的完整仿射复 Hilbert 表示；每个 $\Omega(1)=0$ 的原始 (R) 模型都满足 $\mathrm{DT}$。

**证明。**表示给平方根三角。反向固定任意原模型的三个标签，用定理 23.2 在零漂移模型中精确保留该有序三点矩阵，再将该模型的 $\mathrm{DT}$ 拉回这三个读数。三标签任意，原模型有 $\mathrm{DT}$，由定理 14.1 得全部表示。

**推论 23.4（反例可选为可数三生成零漂移模型）。**若存在非表示的原始 (R) 模型，则存在一个可数三来源生成、满足全部 (R) 及 $\Omega(1)=0$ 的模型，具有真实三点三角超额。

**证明。**定理 14.1 的逆否给原模型中的三点超额；定理 23.2 精确保留这三个来源的全部比较。此结论没有构造该反例，也未证明反例存在。第 18 节的单位原像条件仍给更强的保真实单位复制，但已不是有限矩阵零漂移约化的前置。

## 24. 零漂移子代数与全部长度的双操作预算

**定理 24.1（单位零纤维的实际封闭性）。**若 $\Omega=0$，则对全部 $x,j,n$ 有

$$
\begin{aligned}
q(x)/9&\le c(x,p_j)\le3q(x),&
r(x)/9&\le c(p_j,x)\le3r(x),\\
q(x)/3&\le q(U^nx)\le9q(x),&
r(x)/3&\le r(U^nx)\le9r(x).
\end{aligned}
\tag{24.1}
$$

集合 $Z=\{x:q(x)=r(x)=0\}$ 是包含真实单位的 $U$-子代数；$Ux\in Z$ 当且仅当 $x\in Z$，且 $c|_{Z\times Z}=0$。所有仅由真实单位、乘法和 $U$ 生成的实际项均属于 $Z$。

**证明。**首行用定理 22.3 与引理 1.2。次行上界用定理 22.3，下界用同步等距得到的 $q(x)=c(U^nx,p_n)\le3q(U^nx)$；反向同理。乘法单项界给 $q(st)\le3(q(s)+q(t))$、$r(st)\le3(r(s)+r(t))$，故 $Z$ 对乘法封闭。次行给标记封闭与反射性。最后，$c(z,w)\le3(q(z)+r(w))=0$。全程没有把零费用关系视为等价关系。

**定理 24.2（任意长度 $S,T$ 词的共同单位预算）。**不要求 $\Omega=0$。沿用 $S=U^3$、$T(x)=x p_3$，若 $W,V$ 为任意有限 $S,T$ 复合词，长度可以不同，则

$$
\begin{aligned}
q(Wx)&\le3q(x)+3\Omega,&r(Wx)&\le3r(x)+3\Omega,\\
c(Wx,Vy)&\le9(q(x)+r(y))+18\Omega.
\end{aligned}
\tag{24.2}
$$

**证明。**若 $W$ 长度为 $n$，引理 17.1 对 $W$ 与 $S^n$ 的同层交叉等距给 $c(Wx,p_{3n})=q(x)$、$c(p_{3n},Wx)=r(x)$，因为 $S^n1=p_{3n}$。引理 22.2 给首行；引理 1.2 给第二行。这是所有词长相对未推进真实单位的统一预算；一般三来源右梳与任意右标记词没有被证明属于这个双操作轨道。

**问题 24.3（零对象的外部行列仍有缺口）。**定理 24.1 没有推出 $c(x,z)=q(x)$、$c(z,x)=r(x)$ 对全部 $z\in Z$ 成立；也未推出每个固定 $z\in Z$ 存在有限 $C_z$，使 $q(x)\le C_zc(x,z)$ 对全部外部 $x$ 成立。实际单位轨道 $p_j$ 已由 (24.1) 得到这一控制，复合零对象的传播仍未取得。

具体地，若 $s,t\in Z$，(R) 取 $(a,b,u,v)=(1,s,x,t)$ 给

$$
c(x,st)+c(Ux,s\cdot Ut)+c(U^2x,s\cdot U^2t)=3c(x,t).
\tag{24.3}
$$

即使第一项为零，另外两项仍可能承担右端费用；这指出当前推导的缺失步骤，没有构造满足全部关系的反例。零漂移单位生成子代数上的全行列识别，也仍未取得，不能先取商再调用固定单位分类。

## 25. 有有限推导预算的正锥紧致性

**引理 25.1（仅用有限条原关系的标记预算）。**不借助由无限非负递推得到的同步等距，有限条 (R)、零对角与非负性已给

$$
\begin{aligned}
q(Ux)&\le12q(x)+9r(p_1)+\tfrac32(q(p_1)+q(p_2)),\\
r(Ux)&\le12r(x)+9q(p_1)+\tfrac32(r(p_1)+r(p_2)).
\end{aligned}
\tag{25.1}
$$

因此显式四项零漂移约束给 $q(Ux)\le12q(x)$、$r(Ux)\le12r(x)$，且每个具体实例均有有限关系推导。

**证明。**$R(1,1,x,1)$ 的第零项为 $q(x)$，故 $c(Ux,p_1)\le2q(x)$。$R(1,1,x,p_1)$ 的第零项为 $c(x,p_1)$，故

$$
c(Ux,p_2)\le2c(x,p_1)\le6(q(x)+r(p_1)).
$$

后一单项界也是一条具体 (R) 与非负性的后果。又由 $R(Ux,1,1,1)$，

$$
2q(Ux)=\sum_{i=1}^2c((Ux)p_i,p_i)
\le3\sum_{i=1}^2\bigl(c(Ux,p_i)+q(p_i)\bigr).
$$

最后两个单项界分别用实际拆分 $((Ux)\cdot p_i,p_i\cdot1)$。代入前两界即得首式。将这些有限关系全部转置，得到第二式。这里没有将 $c(U^2x,p_2)$ 错换为 $c(Ux,p_2)$。

**定理 25.2（自由零漂移项上有限可行性供应全域有限模型）。**令 $\mathcal T$ 为有限来源上的自由含幺 $U$-项代数，固定各来源 $x_i$ 的有限非负上界 $q(x_i)\le Q_i$、$r(x_i)\le R_i$。考虑全部 (R)、全部非负与零对角条件、显式四项 $q(p_1)=q(p_2)=r(p_1)=r(p_2)=0$，以及任意族每条只含有限多个坐标的闭线性约束。整个系统有处处有限的非负核解，当且仅当每个有限子系统可行。

**证明。**只需证反向。在唯一单位约简正规形上递归定义

$$
\begin{aligned}
Q(1)&=R_0(1)=0,&Q(x_i)&=Q_i,&R_0(x_i)&=R_i,\\
Q(Us)&=12Q(s),&R_0(Us)&=12R_0(s),\\
Q(st)&=3(Q(s)+Q(t)),&
R_0(st)&=3(R_0(s)+R_0(t))\quad(s,t\ne1).
\end{aligned}
\tag{25.2}
$$

一般乘积仍先作单位约简。引理 25.1、乘法单项界及单位费用分解给

$$
0\le c(s,t)\le B_{s,t}=3(Q(s)+R_0(t))<\infty.
\tag{25.3}
$$

对每个具体有序项对，这个预算只需有限条约束即可推出：按其有限正规项树递归展开对应的引理 25.1 和乘法界，再用一条单位分解界。预算随固定项增长，但不依赖截断系统的规模。

在紧空间 $K=\prod_{(s,t)\in\mathcal T^2}[0,B_{s,t}]$ 中，每条原约束切出闭集。对任意有限组原约束，收集它们涉及的有限坐标，并把这些坐标的有限预算推导所需约束一起加入。有限可行性给一组满足原有限约束及其坐标区间的数值；其余坐标在各自区间任意填入，即得 $K$ 中满足原有限约束的点。因此这些闭集有有限交性质，紧致性给全局解。每个坐标的区间有有限端点，故全局解处处有限。正向由限制显然成立。

**定理 25.3（三点反例的固定有理线性见证）。**非表示的原始 (R) 模型存在，当且仅当存在固定的 $\lambda\in\mathbb Q_{>0}$ 与整数 $B\ge1$，使自由三来源 $a,b,d$ 上下列系统的每个有限子系统都可行：全部 (R)、非负、零对角、显式四项零漂移、六个来源预算 $q(a),r(a),q(b),r(b),q(d),r(d)\le B$，以及

$$
L_\lambda=c(a,d)-(1+\lambda)c(a,b)
-(1+\lambda^{-1})c(b,d)\ge1.
\tag{25.4}
$$

每个固定有限系统均为有理线性非负可行性问题；若不可行，存在有理 Farkas 证书。

**证明。**对 $u,v\ge0$，

$$
(\sqrt u+\sqrt v)^2
=\inf_{\lambda>0}\bigl((1+\lambda)u+(1+\lambda^{-1})v\bigr).
\tag{25.5}
$$

严格的有向平方根三角失败，等价于存在正有理 $\lambda$ 使 $L_\lambda>0$：正实参数先由下确界取得，再由连续性选附近的有理数；当 $u=0$ 或 $v=0$ 时，下确界可由趋向无穷或零的正参数逼近，同样保留严格余量。若 $u=v=0$，任意正参数均可。

若原反例存在，推论 23.4 先给完整零漂移三点反例。对全部费用作同一正比例缩放，可令 $L_\lambda\ge1$；缩放保留全部原关系。三个来源的六个单位费用仍有限，选一个整数 $B\ge1$ 同时控制，便得所述固定系统的所有有限限制。反向，定理 25.2 将同一个 $(\lambda,B)$ 的全部有限可行性变成全域有限零漂移模型，(25.4) 使其有真实三角失败，因而不能有目标表示。

固定有限系统的所有数据均有理。引入非负松弛变量后写成 $Ax=b$、$x\ge0$，不可行的充要证书为存在有理 $y$，使

$$
A^{\mathsf T}y\ge0,\qquad b^{\mathsf T}y<0.
\tag{25.6}
$$

若解存在则 $b^{\mathsf T}y=x^{\mathsf T}A^{\mathsf T}y\ge0$，故证书排除解；反向是有限维有理 Farkas 引理。证毕。此定理不混用不同 $B$ 的有限解，没有给出任何固定 $(\lambda,B)$ 的全有限可行族，也没有给出排除全部参数的证书模式。

## 26. 无条件约化后的几何候选与量子接口

**对应 26.1（本批结果的承重与未解处）。**定理 23.2 的新内容是：原始 (R) 已经供应到真实单位的复制预算，所以任意漂移的有限比较矩阵可以无条件移到零漂移完整模型。第 18 节的额外单位原像与第 14 节的三角前件都不再是这个矩阵约化的条件。定理 25.2 进一步排除了“固定有限系统都可行，但某个新项费用只能趋于无穷”的逃逸；剩下的正锥问题是真实的有限可行性，不是缺少全域有限性。

这些结论仍未使零费用在全部外部行列中可替换，未给三来源右梳的 $\mathbb E\Delta^2=o(N)$ 预算，也未解决原 (R) 是否单独给 $\mathrm{DT}$。右梳费用的线性预算只对应平方根长度的 $O(\sqrt N)$ 控制，不能冒作所需严格更小的尺度。第 24 节的 $S,T$ 全长预算不是一般三来源闭包预算。这里的单位比较、矩阵实现与有限正锥接口是仓内综合推导；紧致性、Farkas 对偶、负型核及 Hilbert 完成是经典工具，不据本批主张文献优先权。第 21 节已核对的三篇文献仍不供应上述缺失条件。

**对应 26.2（完整候选的条件状态）。**当前可完整证明的几何候选仍是原始二元比较关系 (R)，加上“存在统一 $\alpha>0$，使 $c^\alpha$ 的三点比较可逐段相加”。定理 20.1 给定理 14.1 的全部表示，非零模型的全部可行指数为 $(0,1/2]$。本批把这项额外几何条件能否删除的问题精确收缩到零漂移模型，没有证明它已经内生，故不宣称已经取得严格更简洁且完整的新量子公理。

在已有表示的条件下，实际纠偏 $V(a)=U(a p_2)$ 给 $FVa=\omega Fa$。于是三条实际历史 $a\cdot V^ku$ 的像为 $Fa+\omega^kFu$；按第二变量线性的内积约定，三次真实读数恢复 (21.1) 的复内积。若三历史的八个子集事件有实际记录、且其合成含义已供应，令 $v_E=\sum_{i\in E}Fh_i$，则 $D(E,F)=\langle v_E,v_F\rangle$ 为强正 Gram，且 $\mu(E)=\|v_E\|^2$ 无三阶干涉。这一有限几何描述不把子集符号自动当作可执行事件。

总核与每个实际事件核分别取得表示、共同纠偏相位、强正支配与完整和式，才在最小总空间给效果 $0\le E_e\le I$ 及 $K_e(a,b)=\langle Fa,E_eFb\rangle$。非零准备的归一化给 Born 概率。全成对细记录校准、共同相位和完整记录和式，才给复线性 Kraus 延拓。非零准备、失败与停止的事件语义、原记录和返回、全效果的实现、共同参考、联合张量、实际可组合过程及时间仍各保原接口；几何表示没有供应这些独立来源。

**对应 26.3（直观图景）。**仍是三盏灯轮流比较同一对来源，三次总账只按两端来源相加。这次不必先给空输入补一条能倒走的路：每条历史走完后，把所有来源一起补到同一种灯色，就能保住它们之间的全部读数，同时把空输入到真正单位的费用压到零。于是任何会破坏量子几何的有限三点图形，若真的存在，也一定能搬到一个空输入完全不漂移的世界。现在要解决的是：这个世界中所有空配方，能否在任意外部比较中都当作真正的空；这一步未证，不能把“空之间看不出差别”直接当成“它们对整个世界都一样”。

## 追加锚（本行以下为增补区）

## 27. 零左因子递推与外部差式的确切范围

**定义 27.1（实际单位词上的外部行列）。**只在本节的零漂移前件下，令 $E=\langle1\rangle_{\cdot,U}$ 为同一原实现的实际单位生成子代数。定理 24.1 已给 $E\subseteq Z$ 及 $c|_{E\times E}=0$。对任意固定外部 $x\in M$，记

$$
f_n^x(t)=c(U^nx,t),\qquad g_n^x(t)=c(t,U^nx)
\quad(n\ge0,\ t\in E).
\tag{27.1}
$$

这些函数只是原核的限制，不另行指定准备、探针或实际操作。

**引理 27.2（完整关系所给的行递推与非零差式）。**全部原始前件、(R) 及 $\Omega=0$ 给

$$
\begin{aligned}
\sum_{k=0}^2 f_{n+k}^x(s\cdot U^kt)&=3f_n^x(t),&
f_{n+1}^x(Ut)&=f_n^x(t),\\
\sum_{k=0}^2 g_{n+k}^x(s\cdot U^kt)&=3g_n^x(t),&
g_{n+1}^x(Ut)&=g_n^x(t),\\
0\le f_n^x(t)&\le27q(x),&0\le g_n^x(t)&\le27r(x)
\end{aligned}
\quad(s,t\in E).
\tag{27.2}
$$

另一方面，对任意外部 $a,u,v\in M$ 与 $s\in E$，准确的差式是

$$
\sum_{k=0}^2\{c(aU^ku,sU^kv)-c(aU^ku,U^kv)\}
=3\{c(a,s)-q(a)\}.
\tag{27.3}
$$

证明。(R) 分别取 $(1,s,U^nx,t)$ 与 $(s,1,t,U^nx)$，零单位费用给两种递推；同步等距给两个标记式。由 $r(t)=q(t)=0$、单项界及定理 22.3，$f_n^x(t)\le3q(U^nx)\le27q(x)$，转置同理。最后相减 $R(a,s,u,v)$ 与 $R(a,1,u,v)$，公共 $3c(u,v)$ 消去，得到 (27.3)。这里右端并未消失；它就是尚待控制的外部行差。

例如，取 $a=1$ 时，该右端因单位零费用为零；对一般外部 $a$，这一余项尚未被消去。若置 $D_n^x(s;t)=f_n^x(st)-f_n^x(t)$，则同步关系与首个递推给 $\sum_{k=0}^2D_{n+k}^x(s;U^kt)=0$。这些差值可以带符号，原 $c\ge0$ 不使它们逐项非负。因此三项和为零尚不推出每项为零。∎

## 28. 同一实际三点轨道上的有限消去

**引理 28.1（右作用重合给全部外部行列重合）。**只用原始前件与完整 (R)，不要求零漂移。若同一原实现中的 $s,t,v\in M$ 满足三个实际对象等式

$$
s\cdot U^kv=t\cdot U^kv\qquad(k=0,1,2),
\tag{28.1}
$$

则对全部原 $x$ 有 $c(x,s)=c(x,t)$ 及 $c(s,x)=c(t,x)$。

证明。$R(x,s,1,v)$ 与 $R(x,t,1,v)$ 的左端由 (28.1) 逐项相同，故右端相减得 $3c(x,s)=3c(x,t)$。$R(s,x,v,1)$ 与 $R(t,x,v,1)$ 同理给反向行列。所有费用有限，所消去的公共项也有限。这里比较的是同一个实际三点轨道；没有重括号、相位混配或零费用商。∎

若实际单位词 $z$ 有一个实际 $v$ 使 $z\cdot U^kv=U^kv$ 对三个 $k$ 同时成立，则引理取 $s=z,t=1$，给 $c(x,z)=q(x)$、$c(z,x)=r(x)$。这是有限的充分条件，尚未由一般单位词的构造取得。即使 $s,t$ 分别固定这三个对象，也不能在任意 magma 中把 $(st)U^kv$ 重括号成 $s(tU^kv)$。所以这条有限消去不提供一般二元括号传播，也不将 (28.1) 的实际等式弱化为零费用关系。

## 29. 全部自由单位项上的有界递推反例

**定理 29.1（行递推子系统不供应复合词下界）。**令 $\mathcal T_0$ 是只施加双侧单位律的自由含幺 $U$-项代数，无外部来源变量。存在全域函数 $h_n:\mathcal T_0\to[0,2]$，对全部 $n,j\ge0$ 和全部 $s,t\in\mathcal T_0$ 满足

$$
\begin{aligned}
h_n(1)&=h_n(U^j1)=1,\\
h_{n+1}(Ut)&=h_n(t),\\
\sum_{k=0}^2h_{n+k}(s\cdot U^kt)&=3h_n(t),
\end{aligned}
\tag{29.1}
$$

但 $z=(U1)\cdot(U1)$ 满足 $h_0(z)=0$。因此这些全项递推、非负有界性及精确单位轨道读数，并不蕴含对该 $z$ 的任意有限比较 $h_0(1)\le C_zh_0(z)$。这是所列行递推子系统的反例，不是完整 (R) 的核反模型。

证明。令 $\omega=e^{2\pi i/3}$、$\Theta=\{\pm1,\pm\omega,\pm\omega^2\}$，取九个不同符号组成的辅助代数

$$
A=\{e,p,q\}\sqcup\{b_\zeta:\zeta\in\Theta\}.
\tag{29.2}
$$

这里的 $q$ 是辅助对象标签，不是原函数 $q(x)$。定义一元运算

$$
U_0e=p,\quad U_0p=q,\quad U_0q=e,\qquad
U_0b_\zeta=b_{\omega^2\zeta}.
\tag{29.3}
$$

令 $e$ 是乘法 $\odot$ 的双侧单位，其余乘积由下列规则全部给定：

$$
\begin{aligned}
a\odot b_\zeta&=b_\zeta&&(a\in A),\\
b_\zeta\odot p=b_\zeta\odot q&=b_\zeta,\\
a\odot p&=b_{-1}&&(a\in\{p,q\}),\\
a\odot q&=b_{\omega^2}&&(a\in\{p,q\}).
\end{aligned}
\tag{29.4}
$$

单位规则与第一行在 $e\odot b_\zeta$ 一致。这是完整二元运算；例如 $(p\odot q)\odot p=b_{\omega^2}$，但 $p\odot(q\odot p)=b_{-1}$，所以没有把辅助代数预设为结合代数。

定义 $\chi(e)=\chi(p)=\chi(q)=0$、$\chi(b_\zeta)=\zeta$。它满足

$$
\chi(U_0t)=\omega^2\chi(t),\qquad
\sum_{k=0}^2\omega^k\chi(s\odot U_0^kt)=3\chi(t)
\quad(s,t\in A).
\tag{29.5}
$$

第一式由定义直接得到。第二式在 $t=b_\zeta$ 时，右吸收规则使第 $k$ 项为 $\omega^k\omega^{2k}\zeta=\zeta$。在 $t=e$ 时，待算的是 $\chi(s)+\omega\chi(s\odot p)+\omega^2\chi(s\odot q)$：$s=e$ 时为零；$s=p,q$ 时为 $-\omega+\omega^4=0$；$s=b_\zeta$ 时为 $(1+\omega+\omega^2)\zeta=0$。由于 $U_0^3=I$，$t=p,q$ 是这个三项和的循环移位，只多一个非零相位因子，仍为零。故 (29.5) 对所有对象成立。

置

$$
H_n(t)=1+\operatorname{Re}(\omega^n\chi(t)).
\tag{29.6}
$$

$|\chi(t)|\le1$ 给 $0\le H_n\le2$，而 (29.5) 给

$$
H_{n+1}(U_0t)=H_n(t),\qquad
\sum_{k=0}^2H_{n+k}(s\odot U_0^kt)=3H_n(t).
\tag{29.7}
$$

并且 $H_n(e)=H_n(p)=H_n(q)=1$，$H_0(p\odot p)=H_0(b_{-1})=0$。

自由性给唯一的求值映射 $\pi:\mathcal T_0\to A$，满足 $\pi(1)=e$、$\pi(Us)=U_0\pi(s)$、$\pi(st)=\pi(s)\odot\pi(t)$。取 $h_n=H_n\circ\pi$，(29.7) 与单位轨道取值逐项提升为 (29.1)，指定括号词 $z$ 的像为 $b_{-1}$，得到零值。这个通用公式同时覆盖全部有限单位项与全部括号深度，不留下有限截断以后的延拓义务。若 $h_0(1)\le C_zh_0(z)$，便要求 $1\le0$，故任何有限 $C_z$ 都不成立。∎

**命题 29.2（辅助代数的实际等式禁止所述外部核延拓）。**若完整 (R) 模型含有一份保持 $\odot,U_0$ 及单位的实际 $A$ 子代数，则其全部 $s\in A$ 都满足 $c(x,s)=q(x)$、$c(s,x)=r(x)$，对所有外部 $x$ 同时成立。因此不可能又有 $q(x)=1$、$c(x,b_{-1})=0$。

证明。任取 $v=b_\zeta$。三个 $U^kv$ 都属于 $b$ 类，(29.4) 给 $sU^kv=U^kv=1U^kv$，对全部 $s\in A$ 成立。引理 28.1 遂给全部行列识别，所述两个读数直接矛盾。∎

这区分了两个不同域上的结论：$\mathcal T_0$ 上的统一行函数确实存在；若额外把辅助求值相等提升为实际对象相等，这些实际乘法等式与完整 (R) 又禁止所述读数。自由项上的 $\pi(s)=\pi(t)$ 既不是原项相等，也不是已证的全行列相等。不能据此取商，不能据此宣称定理 25.3 某个固定 $(\lambda,B)$ 的全部有限系统可行。一般外部左因子的 (27.3) 及其他外部复合项的四变量约束，并未由 (29.1) 实现。

## 30. 延拓文献、纤维方法与完整候选的边界

**对应 30.1（正延拓工具所需的未付前件）。**Muhamadiev–Diab，*On the extension of positive linear functionals*，IJMMS 23(1), 31–35，[原文](https://www.maths.tcd.ie/EMIS/journals/HOA/IJMMS/Volume23_1/457269.pdf)，Theorem 2.1 在实向量空间 $V$、锥 $K$、子空间 $L$ 上，以一个处处有限、次线性且对 $K$ 单调的支配泛函作为 $f_0:L\to\mathbb R$ 正延拓的充要条件；Theorem 2.2 可用更强的全混合支配 $f_0(\ell)\le p(\ell+k)$、$\ell\in L,k\in K$ 替代预给单调性。定理 25.2 的逐坐标预算并未给包含全部原关系的商空间上这些带符号混合向量的支配，也未给定理 29.1 行数据对全部四变量有限系统的可行性。该文不把本节行函数自动延拓为完整非负核。

Tian，*Extensions of Operator-Valued Kernels on $\mathbb F_d^+$*，[arXiv:2510.10935v3 原文](https://arxiv.org/html/2510.10935v3)，Theorem 3.1 要求截断核正定及内部的 Loewner 支配 $K_\Sigma\preceq K$，才给保内部数据的全域正定延拓；Theorem 3.2 另用 Definition 2.4 的列收缩与全部内外边界 Gram 匹配，才保整个截断域。原 $c\ge0$ 是逐点费用非负，不是该正定前件；零对角正定核本身只能为零，不能直接把 $c$ 当成该文的 $K$。极化后要使用它，仍须先付相应强正性、Loewner 支配与忠实的上下文移位一致性。自由半群上下文索引也不自动保原 magma 括号、任意 $U$ 和全部 (R)。

Akkaoui–Fadli，*New results about quadratic functional equation on semigroups*，Ann. Math. Sil. 39(2), 209–222，[原文](https://journals.us.edu.pl/index.php/AMSIL/article/download/18119/15367)，Theorem 3.3 的二次分解针对结合半群、两个保乘法自同态、唯一二可除的阿贝尔值群及 $f(x\phi(y))+f(\psi(y)x)=2f(x)+2f(y)$。不要求自同态为对合，并不删除结合与保乘法；原 (R) 尚未给这些对象层面前件。这三篇原文只提供所列工具及应用边界，不供应本卷未证的零词括号传播，也不据本节检索主张文献不存在或历史优先权。

**对应 30.2（同纤维差分需要的实际桥梁）。**《原生切口配平续篇》定义 107.1 与定理 107.2 在已有有限 EJA、原正 Frobenius 比较及实双线性作用上，通过 $W_c(a-b)=0$ 限制同纤维输入，再将 $b=a+n$ 与 $b=a$ 的等式相减，得到所有 $n\in\ker P_c$ 上的配对湮灭。那里既有 $W_c=\|P_c\cdot\|^2/2$，也有任意线性零方向平移；全幂等元与谱展开继续恢复全域关系。原 C133 magma 尚未供应这些纤维与扰动操作，定理 24.1 的 $Z\times Z$ 零费用不能替代它们。定理 29.1 进一步说明，只留下单位词上的有界行递推仍不能付这份桥梁。两个模块的结构类比是研究路线，不是从 EJA 正性反向证明本卷正性的许可。

**对应 30.3（保留的完整量子候选与白话）。**本节没有证明原 (R) 单独给复 Hilbert 表示，没有证明一般实际单位词的外部比较下界，也没有构造全域有限非负的原反例。当前完整可证明的几何候选仍是对应 26.2 的原始 (R) 加统一正幂的三点可相加条件；本节未删除这项独立输入，未达到严格更简洁且完整的新量子公理候选。

在该表示前件下，实际 $V(a)=U(a p_2)$ 给纯三相，三条实际历史的像为 $Fa+\omega^kFu$；若三历史及八个子集事件的来源与向量和对应已供应，同一 Gram 给强正及无三阶干涉。总核与各事件核分别表示、共同纠偏相位、强正支配和完整和式，才给原最小空间的效果与 Born 评价；全成对细记录校准、共同相位及完整记录，才给 Kraus 延拓。非零准备、全效果、参考、实际联合张量、真实可执行过程及物理时间继续保各自原接口；失败、停止、记录、返回和合法历史均保原定义。

白话说，三盏灯的总账可以守恒，但一份复杂的空配方仍可能在这套局部递推中，把外部读数从一盏灯挪到另外两盏。上面的全项公式说明，连所有空配方的有界非负行读数和每个标记锚的精确读数都检查过，也不能仅靠这套递推堵住转移。完整四变量关系还有额外的消去力：只要两个配方在同一实际三点轨道上真的作出相同动作，它们对全部外部比较就相同。尚缺的是把这种消去力覆盖到每个原非结合空括号；没有这座桥，就不能把“空配方之间费用为零”当作“它们对整个世界都是真正的空”。

## 追加锚（本行以下为增补区）

## 31. 只检验两种单位标记插入的一致次线性条件

**定义 31.1（两族读数条件 S）。**保留定义 1.1 的全部原始对象：有真实双侧单位 $1$ 的任意 magma $M$，任意 $U:M\to M$，以及处处有限、非负、零对角的 $c$。完整 (R) 仍要求

$$
\forall a,b,u,v\in M:\qquad
\sum_{k=0}^2c\bigl(a\cdot(U^ku),b\cdot(U^kv)\bigr)=3c(a,b)+3c(u,v).
$$

置 $p_j=U^j1$、$q(a)=c(a,1)$、$r(a)=c(1,a)$，并对全部 $a,z\in M$、$j\in\{1,2\}$ 定义

$$
\begin{aligned}
B(a,z)&=q(a)+r(a)+q(z)+r(z),\\
\Delta_j(a,z)&=|c(a\cdot p_j,z)-c(a,z)|+|c(z,a\cdot p_j)-c(z,a)|.
\end{aligned}
\tag{31.1}
$$

额外条件为

$$
\forall\varepsilon>0\ \exists C_\varepsilon\in[0,\infty)\ \forall a,z\in M\ \forall j\in\{1,2\}:\qquad
\Delta_j(a,z)\le\varepsilon B(a,z)+C_\varepsilon.
\tag{S}
$$

同一个有限 $C_\varepsilon$ 必须独立于 $a,z,j$；$B=0$ 也在量词内。只检验将盖一次或两次标记的空输入插在右端这两族比较，不要求任意零费用来源可替换，也不预设对称性、三角、拓扑、固定幂、结合律或 $U1=1$。(S) 是明确增列的一致次线性增长前件，尚未从 (R) 推出；这不声称已证明二者逻辑独立。

白话说，三次成对比较的总账精确配平；再要求两种局部空输入插入造成的双向读数变化，不能随着任意增大的全局比较预算保持正比例增长。它容许标记空输入的有限效应，每个比例容差有一笔共同有限余量，而非要求原模型的插入效应为零。事件完整性、过程接续、联合系统和时间仍分别保留各自的实际前件。

**引理 31.2（真实单位复制中的余项缩放）。**若原模型满足 (S)，则定理 23.2 的实际数组模型，对全部数组 $A,Z\in M^{\Sigma_N}$、$j=1,2$ 和每个 $\varepsilon>0$ 满足

$$
\Delta_{N,j}(A,Z)\le\varepsilon B_N(A,Z)+\frac{C_\varepsilon}{N}.
\tag{31.2}
$$

这里所有下标量均按 (31.1) 在 $c_N$ 和真实数组单位 $\mathbf1$ 上定义，且

$$
c_N(A,Z)=\frac1{N3^N}\sum_{\sigma\in\Sigma_N}c(A_\sigma,Z_\sigma),\qquad
U_N^j\mathbf1=(p_j)_{\sigma\in\Sigma_N},\qquad \Sigma_N=\{0,1,2\}^N.
\tag{31.3}
$$

**证明。**乘法和标记逐坐标采用原运算，$\mathbf1$ 是常值原单位，故 $A\cdot(U_N^j\mathbf1)$ 的坐标确为 $A_\sigma\cdot p_j$。对两个绝对值分别用有限和的三角不等式，再用原 (S)，得

$$
\begin{aligned}
\Delta_{N,j}(A,Z)&\le\frac1{N3^N}\sum_\sigma\Delta_j(A_\sigma,Z_\sigma)\\
&\le\frac\varepsilon{N3^N}\sum_\sigma B(A_\sigma,Z_\sigma)+\frac{C_\varepsilon}{N}
=\varepsilon B_N(A,Z)+\frac{C_\varepsilon}{N}.
\end{aligned}
$$

预算 $B_N$ 是四个真实单位费用的精确加权和；不要求任一未缩放坐标的费用有统一界，也未把复制来源 $\widetilde\Gamma_N1$ 当作真实单位。证毕。

## 32. 两族次线性读数与完整仿射复几何等价

**定理 32.1（条件 S 的完整分类）。**在定义 31.1 的原始签名及完整 (R) 下，(S) 当且仅当存在复 Hilbert 空间 $H$ 与映射 $F:M\to H$，对全部 $a,b\in M$ 满足

$$
F1=0,\qquad F(a\cdot b)=Fa+Fb,\qquad
F(Ua)=\omega Fa+t,\quad t=F(U1),\qquad
c(a,b)=\|Fa-Fb\|^2,\quad \omega=-\tfrac12+i\tfrac{\sqrt3}{2}.
\tag{32.1}
$$

最小空间 $H=\overline{\operatorname{span}_{\mathbb C}F(M)}$ 唯一到唯一的保标签酉同构；零模型、非忠实来源和任意仿射漂移均包含在内。反向可显式选

$$
C_\varepsilon=(4/\varepsilon+2)\|t\|^2.
\tag{32.2}
$$

**证明。**先设 (S)。固定任意原三标签 $a,b,d$，允许重复，使用定理 23.2 的实际复制模型、共同相位补齐和全部自由含幺 $U$-项 $\mathcal T$。只约简双侧单位恒等式，其余实际次序和括号均保留；$U1$ 不约简为 $1$。即使原三标签含 $1$，其来源变量也不与新模型的真实单位合并。

记 $s_N$ 为项 $s$ 在第 $N$ 个数组模型的实际求值。式 (23.8)–(23.9) 给每个固定项有限的、与 $N$ 无关的预算，因而每个固定项对 $s,z$ 的 $B_N(s_N,z_N)$ 有界。取定理 23.2 对全部有序项对的同一个有限值点态收敛子列 $N_\ell\to\infty$，得到 $c_\infty$。非负性、零对角、完整 (R) 及原三标签全部有向比较矩阵同时保留。

令 $p_{\infty,j}=U^j1_{\mathcal T}$。对任意固定 $s,z\in\mathcal T$ 及 $j=1,2$，引理 31.2 沿上述同一子列给

$$
\Delta_{\infty,j}(s,z)\le\varepsilon B_\infty(s,z)
\qquad(\varepsilon>0).
\tag{32.3}
$$

这是有限个费用、加减与绝对值的极限，$C_\varepsilon/N_\ell\to0$；每个 $\varepsilon$ 的不等式都沿原子列成立，无须另换极限模型。$B_\infty(s,z)$ 有限，令 $\varepsilon\downarrow0$，得到在这个同一模型内

$$
s\cdot p_{\infty,j}\approx s\qquad(s\in\mathcal T,\ j=1,2),
\tag{32.4}
$$

其中 $\approx$ 要求对全部 $z\in\mathcal T$ 的完整行与完整列同时相等。

取 $s=1_{\mathcal T}$ 得 $p_{\infty,j}\approx1_{\mathcal T}$。在[有限正性桥引理 2.3、定理 8.2](AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE.md)的自由实差空间与双侧根空间 $\mathcal N_\infty$ 中，(32.4) 因而给

$$
e_{p_{\infty,j}}\in\mathcal N_\infty,\qquad
e_{s\cdot p_{\infty,j}}-e_s\in\mathcal N_\infty,\qquad
D(s,p_{\infty,j})=e_{s\cdot p_{\infty,j}}-e_s-e_{p_{\infty,j}}\in\mathcal N_\infty.
\tag{32.5}
$$

这正是全部 $s$、两个 $j$ 上的 $\mathrm{UC}$；直接调用所引定理 8.2，取得极限模型的完整仿射 Hilbert 表示。其平方根距离给被保留三标签的

$$
\sqrt{c(a,d)}\le\sqrt{c(a,b)}+\sqrt{c(b,d)}.
$$

原三标签任意，原核遂有 $\mathrm{DT}$。定理 14.1 及有限正性桥定理 1.3 给原模型的全部 (32.1) 与最小唯一性。这里不回拉未经证明的运算嵌入，不需要精确零费用条件的极限封闭性，也未使用 $\Omega_\infty(1)=0$ 作为推理前件。定理 14.1 内调用的[续卷 V 定理 1.3](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md)仍只在其真实固定单位商的适用域内复用，未将原始 $U$ 假定为保单位。

反向设 (32.1)。置 $v_j=F(p_j)$，则 $v_1=t$、$v_2=(1+\omega)t$，故两个 $\|v_j\|$ 都等于 $T=\|t\|$。对任意 $a,z$，置 $x=Fa$、$y=Fz$；表示的对称性及 Cauchy–Schwarz 给

$$
\begin{aligned}
B(a,z)&=2(\|x\|^2+\|y\|^2),\\
\Delta_j(a,z)&=2\bigl|\|x+v_j-y\|^2-\|x-y\|^2\bigr|\\
&\le4T\|x-y\|+2T^2\le4T\sqrt{B(a,z)}+2T^2\\
&\le\varepsilon B(a,z)+(4/\varepsilon+2)T^2.
\end{aligned}
\tag{32.6}
$$

最后一步是 $(\sqrt\varepsilon\sqrt B-2T/\sqrt\varepsilon)^2\ge0$。$B=0$ 时 $x=y=0$，直接有 $\Delta_j=2T^2$；$T=0$ 时两个缺陷都为零；全零模型也包含在内，均未除以费用或向量范数。若从表示出发核对 (R)，实际端点像差为 $(Fa-Fb)+\omega^k(Fu-Fv)$，漂移在差中抵消，三次求和即得完整 (R)。证毕。

## 33. 两族入口的比较范围与未解条件

**命题 33.1（已完成关系类相同，检验族减少）。**在原始完整 (R) 类内，(S)、定理 20.1 的某个统一正幂三角、$\mathrm{DT}$、$\mathrm{UC}$、五点及全有限负型与 (32.1) 等价。这里的简化是仅检验两种单位插入族、一个增长条件及直接的 $C_\varepsilon/N$ 证明，不是严格扩大已完成的 (R) 模型类，也不是减少独立物理前提的数量。

**证明。**定理 32.1、20.1、14.4 与有限正性桥定理 8.2 直接给等价。不能把定理 7.1 直接作用于 $\Delta_j$：该定理要求被消去函数自身满足完整四变量关系，此处未证明两种插入缺陷满足它。新的桥梁是引理 31.2 对真实单位、实际自由项和共同极限的缩放估计。亦未声称正幂三角单独在任意原始 magma 上给 (S)：它约束核，不控制任意单位插入动作。证毕。

**命题 33.2（有限原始核不区分该增长条件）。**任意有限 $M$ 上的有限值核均满足 (S)，但其中有核违反每个正幂三角。

**证明。**有限多个 $\Delta_j$ 有共同上界，可取作每个 $C_\varepsilon$。例如标签 $(1,a,b)$ 上令 $U=I$，$1$ 为双侧单位，非单位间取 $x\cdot y=x$，并令核矩阵为

$$
\begin{pmatrix}0&0&1\\1&0&0\\2&0&0\end{pmatrix}.
$$

此时 $p_j=1$，两个缺陷全零，但 $c(1,b)^\alpha=1>c(1,a)^\alpha+c(a,b)^\alpha=0$ 对每个 $\alpha>0$ 成立。它不满足完整 (R)：非零有限核违反命题 2.4 的全局有界结论；不是 (R) 的反模型，也不证明原目标的否定。证毕。

**问题 33.3（保留的充分性缺口）。**(R) 单独是否迫出 (S) 或完整表示，仍未解决。精确条件 $(Z)$，即 $c(s,t)+c(t,s)=0$ 蕴涵对每个 $z$ 有 $c(s,z)=c(t,z)$ 及 $c(z,s)=c(z,t)$，与 (R) 合用是否充分，也仍未解决。一般零漂移条件同样未由本定理取得充分性；(S) 并非从这些未决前件推出。

## 34. 同一候选的几何、事件与过程适用域

**推论 34.1（可见几何与来源接口）。**在定理 32.1 的前件下，可见零费用商的聚合为加法，交换次序和改变括号不改变可见比较；原始档案仍保留。实际纠偏配方

$$
V(a)=U\bigl(a\cdot p_2\bigr),\qquad F(Va)=\omega Fa
\tag{34.1}
$$

给 $120^\circ$ 相位及全有限半正定 Gram。采用第二变量线性的内积约定，三条实际历史 $a\cdot(V^ku)$ 给

$$
\langle Fa,Fu\rangle=\frac13\sum_{k=0}^2\omega^{-k}q\bigl(a\cdot(V^ku)\bigr).
\tag{34.2}
$$

它不限定物理空间三维。若三历史的全部八个子集事件实际对应同一组向量和，有限正性桥命题 6.1 才给其共同强正 Gram 与无三阶干涉。

对每个实际完整有限测试 $C$，总核 $c_*$ 与每个事件核 $c_e$ 须在同一 $M,\cdot,1,U$ 上分别满足原始签名、完整 (R) 和各自的 (S)，并保持原来的完整和式 $\sum_{e\in C}c_e=c_*$。在最小总空间有唯一

$$
0\le E_e\le I,\qquad \sum_{e\in C}E_e=I,\qquad
c_e(a,b)=\langle Fa-Fb,E_e(Fa-Fb)\rangle.
\tag{34.3}
$$

实际准备差 $x=Fa-Fb\ne0$ 按同一测试总质量归一时，Born 权重为 $\langle x,E_ex\rangle/\|x\|^2$；总量为零不定义 $0/0$。不从总核的 (S) 推断事件核的 (S)，也不从 $F1=0$ 获得非零准备。

若输入、输出各取上述最小表示，即 $H_{\rm in}=\overline{\operatorname{span}_{\mathbb C}F_{\rm in}(M_{\rm in})}$、$H_{\rm out}=\overline{\operatorname{span}_{\mathbb C}F_{\rm out}(M_{\rm out})}$，实际完整有限细分支 $T_{e,r}$ 保持单位，全部输入对与原记录满足

$$
c_e(a,b)=\sum_r c_{\rm out}(T_{e,r}a,T_{e,r}b),\qquad
\sum_{e\in C}c_e(a,b)=c_{\rm in}(a,b),\qquad
c_{\rm out}\bigl(T_{e,r}(V_{\rm in}a),V_{\rm out}(T_{e,r}a)\bigr)=0,
\tag{34.4}
$$

其中前两式对全部 $a,b$、末式对全部 $a,e,r$ 成立，细记录读数也须逐记录对应，则有唯一有界复线性 Kraus 延拓 $K_{e,r}F_{\rm in}a=F_{\rm out}(T_{e,r}a)$，且 $\sum_{e,r}K_{e,r}^*K_{e,r}=I$。仅到单位的范数校准不替代全成对校准，保距离不替代共同纠偏相位。

**证明。**几何及 (34.1) 由 (32.1) 和 $1+\omega+\omega^2=0$ 得到，(34.2) 复用式 (21.1)。对总核与每个事件核分别应用定理 32.1，随后直接消费[有限正性桥定理 6.2、对应 6.3](AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE.md)的完整测试与细过程接口。

[续卷 V 第 6 节](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md#6-标准量子接口的来源与结论)的原始分类要求标记固定单位；此处使用有限正性桥的仿射版本与共同 $V$，未将原 $U$ 填入固定单位前件。[续卷 II 第 6 节](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_II.md#6-完整事件过程复合与时间)的整数群接口也只在可见加法与共同相位已取得后消费：实际联合须有可见双可加性、复相位平衡和乘积质量，才给复张量嵌入，乘积像稠密才给整个联合空间。聚合加法本身不供应联合张量。

Kraus 形式给数学上的完全正扩张；实际参考系统上的过程等于它仍需原参考接口。全效果域上一致、非负、归一、可加评价在有限维给密度态，无限维还需正规性或相应可数可加；全效果的实际供应仍为前件。实际可逆、保单位、保全部比较及共同纠偏相位的过程给酉表示，一参数群和强连续时间另行供应才给自伴生成元。Lüders 更新仍需结果子空间内的无扰动条件，效果和结果可重复性不单独决定它。非零准备、失败、停止、记录、返回及合法历史均保留原定义；静态几何不供应上述实际操作，也不完成量子起源目标。证毕。

**对应 34.2（数学来源与新增范围）。**有限和的绝对值比较、Cauchy–Schwarz、Young 平方估计和可数有限值对角抽取均为经典工具。已有定理 20.1、23.2、14.1、有限正性桥定理 1.3、8.2 及所引量子接口各按原前件复用。这里的 repo-derived 增量是两种单位插入缺陷的统一次线性界，经真实单位复制产生 $C_\varepsilon/N$，在同一全项极限中取得完整 $\mathrm{UC}$，再由有限三点保持恢复原模型的表示。群上极化的文献条件仍沿用有限正性桥第 11 节所引 de Place Friis–Stetkær，*On the quadratic functional equation on groups*，DOI 10.5486/pmd.2006.3270，Theorem 1.2；只在已有交换群处使用。这里不主张历史新颖性、文献穷尽性或完整物理前提的减少。

## 追加锚（两族单位插入次线性分类；本行以下为增补区）

## 35. 第一标记双向读数与第三标记单侧返回

**定义 35.1（三个有向比较族的条件）。**沿用定义 31.1 的原始签名：$M$ 是有真实双侧单位 $1$ 的任意 magma，$U:M\to M$ 任意，$c:M^2\to[0,\infty)$ 处处有限且 $c(x,x)=0$。完整 (R) 对全部 $a,b,u,v$ 要求

$$
\sum_{k=0}^2c\bigl(a\cdot(U^ku),b\cdot(U^kv)\bigr)=3c(a,b)+3c(u,v).
\tag{35.1}
$$

置 $p_j=U^j1$、$q(a)=c(a,1)$、$r(a)=c(1,a)$、$x_+=\max\{x,0\}$，并定义

$$
\begin{aligned}
B(a,z)&=q(a)+r(a)+q(z)+r(z),\\
\Delta_1(a,z)&=|c(a\cdot p_1,z)-c(a,z)|+|c(z,a\cdot p_1)-c(z,a)|,\\
\Xi(a,z)&=\Delta_1(a,z)+[c(a,z)-c(a\cdot p_3,z)]_+.
\end{aligned}
\tag{35.2}
$$

条件 $\mathrm S_{13}^{-}$ 为

$$
\forall\varepsilon>0\ \exists C_\varepsilon\in[0,\infty)\ \forall a,z\in M:\qquad
\Xi(a,z)\le\varepsilon B(a,z)+C_\varepsilon.
\tag{S13-}
$$

$C_\varepsilon$ 有限且独立于标签；零预算也在量词内。这里只比较第一标记在两个端点的插入，以及第三标记在第一端点造成的下降；不假定第二标记的任一方向、第三标记的上升缺陷或反向端点读数。没有增列原始代数律、对称性、度量、$U$ 满射性、$U1=1$、未见正性或物理操作。

**引理 35.2（单侧第三返回迫出第二标记不可见）。**在上述原始签名和完整 (R) 下，记 $x\approx y$ 为对全部 $z$ 同时有 $c(x,z)=c(y,z)$、$c(z,x)=c(z,y)$。若

$$
a\cdot p_1\approx a,\qquad c(a\cdot p_3,z)\ge c(a,z)
\qquad(a,z\in M),
\tag{35.3}
$$

则 $a\cdot p_2\approx a$ 对全部 $a$ 成立，进而满足 $\mathrm{UC}$ 并有完整仿射复 Hilbert 表示。

**证明。**置 $T_2a=a\cdot p_2$。(R) 取 $(a,b,1,1)$，第一标记的完整行列相等给

$$
c(T_2a,T_2b)=c(a,b).
\tag{35.4}
$$

取 $a=1$ 得 $p_1\approx1$，所以 $q(p_1)=0$。再取 $R(a,b,p_1,1)$，得到

$$
\begin{aligned}
3c(a,b)&=c(a\cdot p_1,b)+c(a\cdot p_2,b\cdot p_1)+c(a\cdot p_3,b\cdot p_2)\\
&\ge c(a,b)+c(T_2a,b)+c(a,T_2b).
\end{aligned}
\tag{35.5}
$$

末项仅用了 (35.3) 的单侧下界，没有把它替换成第三标记的等式。因此

$$
c(T_2a,b)+c(a,T_2b)\le2c(a,b).
\tag{35.6}
$$

固定任意 $a,b$，令 $g_n=c(T_2^na,b)$、$h_n=c(a,T_2^nb)$，$n\ge0$；两列均处处有限非负，且 $g_0=h_0=c(a,b)$。在 $(T_2^na,b)$ 和 $(a,T_2^nb)$ 分别应用 (35.6)，再用同步等距 (35.4)，得对 $n\ge1$

$$
g_{n+1}+g_{n-1}\le2g_n,\qquad
h_{n+1}+h_{n-1}\le2h_n.
\tag{35.7}
$$

对这两列中的任一列 $v$，相邻差非增，故 $v_n\le v_0+n(v_1-v_0)$。若 $v_1<v_0$，取足够大的有限整数 $n$，右端为负，与 $v_n\ge0$ 矛盾。因此 $g_1,h_1\ge c(a,b)$；(35.6) 又给 $g_1+h_1\le2c(a,b)$，迫使

$$
c(T_2a,b)=c(a,b)=c(a,T_2b).
\tag{35.8}
$$

$a,b$ 任意，故第二标记有完整行列不可见性。这是经典的非负凹序列论证在 (R) 中的应用；没有使用核的对称性、$T_2$ 满射、三角、结合律或 Hilbert 正性。$T_2^na$ 只是逐次右乘 $p_2$ 的指定有限项，不要求无限可执行历史或新资源。

现在对 $j=1,2$，取 $a=1$ 有 $p_j\approx1$。由[有限正性桥引理 2.3](AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE.md)在自由实差空间及完整双侧根空间 $\mathcal N$ 中得到

$$
e_{p_j}\in\mathcal N,\qquad e_{a\cdot p_j}-e_a\in\mathcal N,\qquad
D(a,p_j)=e_{a\cdot p_j}-e_a-e_{p_j}\in\mathcal N.
\tag{35.9}
$$

这正是 $\mathrm{UC}$；直接应用同卷定理 8.2 得完整表示。在取得 $\mathrm{UC}$ 前没有另行假定或证明 $U$ 的商稳定性。证毕。

## 36. 三个比较族的完整仿射分类

**定理 36.1（条件 $\mathrm S_{13}^{-}$ 的分类）。**在定义 35.1 的原始签名及完整 (R) 下，$\mathrm S_{13}^{-}$ 当且仅当存在复 Hilbert 空间 $H$ 与映射 $F:M\to H$，对全部 $a,b$ 满足

$$
F1=0,\qquad F(a\cdot b)=Fa+Fb,\qquad
F(Ua)=\omega Fa+t,\quad t=F(U1),\qquad
c(a,b)=\|Fa-Fb\|^2,\quad \omega=-\tfrac12+i\tfrac{\sqrt3}{2}.
\tag{36.1}
$$

最小空间 $H=\overline{\operatorname{span}_{\mathbb C}F(M)}$ 唯一到唯一的保标签酉同构，如定理 32.1；零模型、非忠实来源和任意仿射漂移均包含在内。反向可取 $C_\varepsilon=(4/\varepsilon+2)\|t\|^2$。

**证明。**先设 $\mathrm S_{13}^{-}$。在定理 23.2 的实际数组模型中，$\Sigma_N=\{0,1,2\}^N$，乘法与 $U_N$ 逐坐标采用原运算，真实单位为常值原单位数组 $\mathbf1$，且

$$
c_N(A,Z)=\frac1{N3^N}\sum_{\sigma\in\Sigma_N}c(A_\sigma,Z_\sigma),\qquad
U_N^3\mathbf1=(p_3)_{\sigma\in\Sigma_N}.
\tag{36.2}
$$

所有下标量均按定义 35.1 在真实数组单位上计算。对 $\Delta_1$ 的两个绝对值分别用有限和三角不等式，对第三项用 $[\sum_i d_i]_+\le\sum_i[d_i]_+$，得到对全部数组 $A,Z$

$$
\begin{aligned}
\Xi_N(A,Z)&\le\frac1{N3^N}\sum_\sigma\Xi(A_\sigma,Z_\sigma)\\
&\le\frac\varepsilon{N3^N}\sum_\sigma B(A_\sigma,Z_\sigma)+\frac{C_\varepsilon}{N}
=\varepsilon B_N(A,Z)+\frac{C_\varepsilon}{N}.
\end{aligned}
\tag{36.3}
$$

预算是四个真实单位费用的精确加权和；不要求未缩放坐标有共同预算，也未将 $\widetilde\Gamma_N1$ 代作真实单位。

固定任意原三标签 $a,b,d$，允许重复。定理 23.2 给共同相位补齐的来源数组、全部自由含幺 $U$-项 $\mathcal T$ 的实际求值 $s_N$、每个固定项的有限统一预算，以及对全部有序项对同一个有限值点态收敛子列 $N_\ell\to\infty$。只约简双侧单位律，保留括号、次序和 $U1$；即使原标签等于 $1$，来源变量也不与真实单位符号合并。

记共同极限为 $c_\infty$。它仍非负、零对角、满足完整 (R)，并精确保留原三标签全部有向比较矩阵。对每个固定 $s,z\in\mathcal T$，沿同一子列把 (36.3) 的有限个费用、绝对值和正部取极限，得

$$
\Xi_\infty(s,z)\le\varepsilon B_\infty(s,z)\qquad(\varepsilon>0).
\tag{36.4}
$$

每个 $\varepsilon$ 的不等式都沿这个已选子列成立，不另选模型；$C_\varepsilon/N_\ell\to0$，而 $B_\infty(s,z)$ 有限。令 $\varepsilon\downarrow0$，非负各项遂分别为零，即

$$
s\cdot p_{\infty,1}\approx s,\qquad
c_\infty(s\cdot p_{\infty,3},z)\ge c_\infty(s,z),\qquad
p_{\infty,j}=U^j1_{\mathcal T}.
\tag{36.5}
$$

此时第三标记仅取得下界，未预设等式。引理 35.2 随即给极限模型的 $\mathrm{UC}$ 和完整表示。平方根 Hilbert 距离在被保留的三标签上给

$$
\sqrt{c(a,d)}\le\sqrt{c(a,b)}+\sqrt{c(b,d)}.
\tag{36.6}
$$

原三标签任意，原核有 $\mathrm{DT}$；定理 14.1 与有限正性桥定理 1.3 恢复原模型的全部 (36.1) 及最小唯一性，包括乘法和原 $U$。这里只回拉三个比较值，不回拉未证的原运算嵌入；不使用零费用商、全局零费用来源的封闭性或 $U$ 满射性。定理 23.2 同时给的零漂移不作为额外推理前件，更未令原模型的 $t$ 为零。

反向设 (36.1)。由仿射标记公式及 $F1=0$ 得

$$
F(p_3)=(1+\omega+\omega^2)t=0,\qquad
c(a\cdot p_3,z)=c(a,z).
\tag{36.7}
$$

故第三项正部为零，而式 (32.6) 对第一标记直接给

$$
\Xi(a,z)=\Delta_1(a,z)\le\varepsilon B(a,z)+(4/\varepsilon+2)\|t\|^2.
\tag{36.8}
$$

零预算、$t=0$ 及全零核均在此估计内，没有除以预算或范数。漂移任意；表示满足完整 (R) 的核对仍由定理 32.1 的端点差消去漂移给出。证毕。

## 37. 同一模型类与完整量子候选的来源边界

**对应 37.1（比较族的减少与数学来源）。**在完整 (R) 类内，定理 36.1 与定理 32.1 分类同一个完整仿射模型类：旧 (S) 的四个有向插入比较族，改由 $\mathrm S_{13}^{-}$ 的三个比较族刻画，第三个还只约束下降。增长关系仍是额外前件，未由 (R) 推出；这不是严格扩大已分类模型类，也不表示独立物理公理更少。

承重的 repo-derived 增量是 (R) 下第一标记完整行列等式与单侧第三下界共同迫出第二标记不可见，再由真实单位复制的余项收缩把这条精确桥传回原模型的完整表示。非负凹序列、有限和三角与正部次可加、共同对角抽取都是经典工具，分别附于上述推导内；定理 23.2、14.1、32.1、式 (32.6) 和有限正性桥引理 2.3、定理 8.2 直接复用。群上极化的文献边界仍是对应 34.2 所引 de Place Friis–Stetkær 的 Theorem 1.2，只用于已取得的交换群；这里不主张历史新颖性或文献穷尽性。

白话对应为：三盏灯比较同一组成对来源，总账精确配平；一次标记的空输入可以在原读数的两个端点产生有限或次线性扰动，而一整圈标记的空输入不能随着预算增长持续造成正比例的读数下降。数学数组复制使第一种扰动在共同极限中严格不可见，使整圈条件成为单侧下界。若第二标记仍保持一个下降差异，同步等距与配平会迫出最终降到负值的非负比较序列；若差异向上，配对端点的不等式迫使另一端下降。因此第二标记也消失，复平方距离几何随之得到。这些数组是证明构造，不供应物理复制或测量操作；事件、校准过程、联合系统与时间仍须各自的实际来源。

**对应 37.2（完整候选的逐接口前件）。**定理 36.1 供应推论 34.1 的几何入口，以下各项继续消费该推论及其所引接口，唯一替换是对每个适用核用 $\mathrm S_{13}^{-}$ 代替 (S)。其来源与结论的对应为：

- 可见聚合为加法、$c$ 为平方距离，实际纠偏 $V(a)=U(a\cdot p_2)$ 的像为 $120^\circ$ 相位，并有全有限 Gram 正性；这些几何结论不限制物理维数为三。三历史的全部八个子集若实际对应同一向量和，才有共同强正 Gram 与无三阶干涉。
- 在同一签名和同一 $U$ 上，总核与每个事件核须各自满足原始前件、完整 (R) 及 $\mathrm S_{13}^{-}$；各自常数可不同。实际完整有限菜单与 $\sum_{e\in C}c_e=c_*$ 仍须供应，才在最小总空间给唯一效果及其完整和式。Born 归一还须实际非零准备及共同总质量；不从总核的增长条件推断事件核的条件。
- 输入、输出均取最小 Hilbert 张成，实际完整有限细过程保单位，并对全部输入对满足 (34.4) 的事件分解与完整核和式，同时保留全部细记录读数及共同纠偏相位，才给推论 34.1 的唯一有界复线性 Kraus 延拓与 $\sum_{e,r}K_{e,r}^*K_{e,r}=I$。Kraus 形式给数学上的完全正扩张；它等于实际参考系统上的过程，仍须原参考实现接口。
- 实际联合的双可加、复相位平衡及乘积质量给复张量嵌入，乘积像稠密才给整个联合空间。全效果域的一致非负归一可加评价在有限维给密度态，无限维仍需正规性或相应可数可加；全效果域的实际供应未从几何取得。
- 实际可逆过程连同保单位、保全部比较及共同纠偏相位给酉表示；实际一参数群与强连续性另行给时间和自伴生成元。Lüders 更新还须结果子空间内无扰动。失败、停止、记录、返回和合法历史均保留原定义，静态几何不供应这些操作。

因此候选由原始签名、完整 (R)、三个比较族的增长条件，以及各适用接口的实际来源前件组成。事件效果、Born、过程、复合、状态与时间的条件推导均沿推论 34.1 原接口成立；本分类只压缩几何入口的比较族，没有完成量子起源。

**对应 37.3（尚缺的充分性与实际实现）。**完整 (R) 单独是否迫出 $\mathrm S_{13}^{-}$ 或完整表示，仍未解决。只保留第一标记两个绝对缺陷的统一次线性条件是否充分，以及只保留第三标记单侧下降条件是否充分，也均未解决；这里没有供应完整 (R) 的反模型，不声称这些前件的独立性已证。要达到完整量子起源，还需为对应 37.2 各项实际来源给出共同实现或独立依据，或在明确适用域内证明它们可由更弱前件推出；几何分类不能替代这些存在与操作义务。

## 追加锚（三个有向比较族的单侧返回分类；本行以下为增补区）

## 38. 纯相位支配残差的固定两来源归约与有理穷尽

**定义 38.1（纯相位支配残差类）。**令 $M$ 为任意带真实双侧单位 $1$ 的 magma，$U:M\to M$ 任意，$H$ 为复 Hilbert 空间，$\omega=\exp(2\pi i/3)$。给定映射 $F:M\to H$，要求

$$
F1=0,\qquad F(a\cdot b)=Fa+Fb,\qquad F(Ua)=\omega Fa.
\tag{38.1}
$$

残差是处处有限的实函数 $D:M^2\to\mathbb R$，满足反对称性与全域支配

$$
D(b,a)=-D(a,b),\qquad |D(a,b)|\le\|Fa-Fb\|^2,
\tag{38.2}
$$

并对全部 $a,b,u,v\in M$ 满足完整四变量关系

$$
\sum_{k=0}^2D(a\cdot U^ku,b\cdot U^kv)=3D(a,b)+3D(u,v).
\tag{R_D}
$$

另记 $p_3=U^31$、$P_3a=a\cdot p_3$，分别要求全部 $a,b\in M$ 上的两条恒等式

$$
D(P_3a,b)=D(a,b),
\tag{38.3L}
$$

$$
D(a,P_3b)=D(a,b).
\tag{38.3R}
$$

这里保留一切次序、括号、单位标签与重复标签；不要求原乘法结合、$U$ 保乘法、$F$ 忠实或 $D$ 沿 $F$ 的纤维下降，也不添加群、拓扑或物理操作。对称 Hilbert 几何与纯相位规则 (38.1)、两条第三标记规则是此残差类的输入。

复用[有限正性桥 §12](AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE.md#12-自由有单位项上的归一化反模型归约)的自由含幺项，将其两个生成元与一元构造子改记为 $x,y,U$，所得项集记为 $T$。除双侧单位约简外不加恒等式；特别 $U1$、$U^31$ 与 $1$ 是不同项。固定标准 $\mathbb C^2$ 中的正交单位向量 $e_1,e_2$，递归定义

$$
f1=0,\quad fx=e_1,\quad fy=e_2,\quad
f(s\cdot t)=fs+ft,\quad f(Us)=\omega fs,\quad
K_0(s,t)=\|fs-ft\|^2.
\tag{38.4}
$$

单位规则与 $f1=0$ 相容。固定模型残差指 $(M,H,F)=(T,\mathbb C^2,f)$ 上满足 (38.2)、$(R_D)$、(38.3L) 和 (38.3R) 的 $d$；所有等式仍在原项上解释。

**定理 38.2（非零残差存在性的固定几何等价）。**下列三项等价：

1. 存在满足定义 38.1 的一组 $(M,U,H,F,D)$，且 $D\not\equiv0$。
2. 固定模型存在残差 $d$，使 $d(x,y)>0$。
3. 固定 $T$ 上存在处处有限、非负、零对角的核 $c$，满足完整 (R)，并对全部 $s,t\in T$ 分别满足 $c(P_3s,t)=c(s,t)$ 与 $c(s,P_3t)=c(s,t)$，且

$$
\frac{c(s,t)+c(t,s)}2=K_0(s,t)\quad(s,t\in T),\qquad c(x,y)>c(y,x).
\tag{38.5}
$$

因此，这个任意来源类的普遍 $D=0$，既等价于所有固定模型残差恒为零，也等价于所有固定模型残差的单个指定坐标 $d(x,y)=0$。

**证明。**由第一项选 $a,b\in M$ 使 $D(a,b)\ne0$。自由项求值给保单位、乘法与 $U$ 的总映射 $\phi:T\to M$，其中 $\phi(x)=a,\phi(y)=b$。这是有限正性桥式 (12.2) 的直接复用；经典自由代数来源为 Burris–Sankappanavar，*A Course in Universal Algebra*，作者版 II§10，[原文](https://www.math.uwaterloo.ca/~snburris/htdocs/UALG/univ-algebra2012.pdf)。求值不要求单射、满射或原乘法结合。

定义复线性映射 $V:\mathbb C^2\to H$ 及实数

$$
V(z_1,z_2)=z_1Fa+z_2Fb,\qquad S=\|Fa\|^2+\|Fb\|^2.
\tag{38.6}
$$

逐构造子归纳给 $F\phi(s)=Vfs$：三个叶项直接成立；一元步骤用 $F(U\phi(s))=\omega F\phi(s)$；乘积步骤用 (38.1)，单位约简的两种位置均由 $F1=0$ 保证。因而所有括号与次序都被保留。支配使 $Fa\ne Fb$，故 $S>0$。三角不等式与二维 Cauchy–Schwarz 给每个 $z\in\mathbb C^2$ 上同一个界

$$
\|Vz\|\le |z_1|\|Fa\|+|z_2|\|Fb\|\le\sqrt S\,\|z\|.
\tag{38.7}
$$

取 $\varepsilon\in\{1,-1\}$ 使 $\varepsilon D(a,b)>0$，置

$$
d(s,t)=\frac{\varepsilon}{S}D(\phi(s),\phi(t)).
\tag{38.8}
$$

于是对所有项对同时有

$$
|d(s,t)|\le S^{-1}\|V(fs-ft)\|^2\le K_0(s,t),\qquad d(x,y)>0.
\tag{38.9}
$$

原反对称性直接拉回。对任意 $s,t,u,v\in T$，求值将 $(R_D)$ 的三个左项分别变为 $D(\phi(s)\cdot U^k\phi(u),\phi(t)\cdot U^k\phi(v))$；故原四变量等式除以同一常数并乘 $\varepsilon$，就是所需完整等式。又有 $\phi(p_3)=p_3$、$\phi(P_3s)=P_3\phi(s)$，所以原第一端点恒等式给 $d(P_3s,t)=d(s,t)$，原第二端点恒等式另给 $d(s,P_3t)=d(s,t)$。没有将一个方向替代另一个方向。两列 $Fa,Fb$ 相关、其中一列为零、$V$ 奇异乃至 $H$ 为零空间都不破坏 (38.7)；零空间中支配使 $D=0$，不会产生需要除以零的非零见证。这证明第一项推出第二项；反向直接取固定模型本身。

为证明第二、三项等价，令 $A=fa-fb,Q=fu-fv$。平方范数展开与 $1+\omega+\omega^2=0$ 给

$$
\sum_{k=0}^2\|A+\omega^kQ\|^2=3\|A\|^2+3\|Q\|^2.
\tag{38.10}
$$

所以 $K_0$ 满足完整 (R)。又 $fp_3=0$，故 $f(P_3s)=fs$，$K_0$ 的两种 $P_3$ 恒等式分别成立。若有第二项的 $d$，置 $c=K_0+d$；支配给 $c\ge0$，反对称性给零对角，线性相加给全部 (R) 与两种 $P_3$ 等式。$K_0$ 对称，故 (38.5) 成立，且 $c(x,y)-c(y,x)=2d(x,y)>0$。反之，给定第三项的 $c$，置 $d=c-K_0$。(38.5) 给 $d(t,s)=-d(s,t)$；$c(s,t)\ge0$ 与 $c(t,s)\ge0$ 分别给 $d(s,t)\ge-K_0(s,t)$ 与 $d(s,t)\le K_0(s,t)$。相减给完整 $(R_D)$ 与两种 $P_3$ 等式，指定坐标为正。

最后，若某固定模型残差在其他项对 $(s,t)$ 非零，把该固定模型当作第一项的来源，并在 (38.6)–(38.8) 中取 $a=s,b=t$，就得到另一个固定模型残差，其 $d(x,y)>0$。因此“所有残差的指定坐标为零”确实排除所有其他非零坐标；没有声称某一个残差仅凭自身 $d(x,y)=0$ 就恒为零。证毕。

**定义 38.3（同一项对坐标上的有限系统）。**对单位约简后的正规项定义大小

$$
|1|=|x|=|y|=1,\quad |Us|=1+|s|,\quad
|s\cdot t|=1+|s|+|t|\quad(s,t\ne1).
\tag{38.11}
$$

一般乘积先作单位约简。对整数 $N\ge1$，置

$$
\begin{aligned}
T_N&=\{s\in T:|s|\le N\},\\
E_N&=T_N\ \cup\ \{a\cdot U^ku:a,u\in T_N,\ 0\le k\le2\}
\ \cup\ \{P_3a:a\in T_N\}.
\end{aligned}
\tag{38.12}
$$

在唯一一组实变量 $z=(z_{s,t})_{(s,t)\in E_N^2}$ 上定义 $\mathcal P_N$。令 $\mathcal E_N$ 为下列等式左端的有限族，全部要求为零：

$$
\begin{aligned}
z_{s,t}+z_{t,s}&\qquad(s,t\in E_N),\\
\sum_{k=0}^2z_{a\cdot U^ku,b\cdot U^kv}-3z_{a,b}-3z_{u,v}
&\qquad(a,b,u,v\in T_N),\\
z_{P_3a,b}-z_{a,b}&\qquad(a,b\in T_N),\\
z_{a,P_3b}-z_{a,b}&\qquad(a,b\in T_N).
\end{aligned}
\tag{38.13}
$$

再对每个有序对 $(s,t)\in E_N^2$ 和每个 $\sigma\in\{1,-1\}$ 保留界

$$
K_0(s,t)-\sigma z_{s,t}\ge0.
\tag{38.14}
$$

特别，$K_0(s,t)=0$ 的项对也保留两条界，此时 $z_{s,t}=0$。没有把同一可见值的不同项合并为一个变量，也没有删去任何一种 $P_3$ 等式。所有行共享这个变量族，而不是分别求解再拼接。记

$$
m_N=\max_{z\in\mathcal P_N}z_{x,y},\qquad
\mathcal P_N(q)=\{z\in\mathcal P_N:z_{x,y}\ge q\}.
\tag{38.15}
$$

**定理 38.4（固定几何的完整有理阈值穷尽）。**上述有限系统的数据均有理，$m_N$ 是存在的非负有理数，且 $m_{N+1}\le m_N\le2$。令 $\mathscr D$ 为全部固定模型残差，则

$$
\max_{d\in\mathscr D}d(x,y)=\inf_{N\ge1}m_N.
\tag{38.16}
$$

定义 38.1 所规定的整个模型类中存在非零残差，当且仅当

$$
\exists q\in\mathbb Q_{>0}\quad\forall N\ge1\quad
\exists z_N\in\mathcal P_N(q)\cap\mathbb Q^{E_N^2}.
\tag{38.17}
$$

该类的普遍 $D=0$，则等价于

$$
\forall q\in\mathbb Q_{>0}\ \exists N\ge1:\quad m_N<q,
\tag{38.18}
$$

也等价于对每个这样的 $q$，存在 $N$、正有理数 $\delta$、非负有理数 $\lambda_{s,t,\sigma}$ 和有理数 $\rho_e$，使共同变量上的仿射恒等式

$$
q-z_{x,y}=\delta+
\sum_{(s,t)\in E_N^2,\ \sigma=\pm1}
\lambda_{s,t,\sigma}\bigl(K_0(s,t)-\sigma z_{s,t}\bigr)
+\sum_{e\in\mathcal E_N}\rho_e e(z)
\tag{38.19}
$$

成立。这里是对常数项及每个共同变量系数的恒等式，$\delta>0$ 保留严格阈值间隔。

**证明。**由 (38.4) 归纳，$fs\in\mathbb Z[\omega]^2$。若 $fs-ft=(m_1+n_1\omega,m_2+n_2\omega)$，则

$$
K_0(s,t)=\sum_{j=1}^2(m_j^2-m_jn_j+n_j^2)\in\mathbb Z_{\ge0}.
\tag{38.20}
$$

有限系统因此是整数数据的线性系统；各 $T_N,E_N$ 有限、嵌套，且并为 $T$。每个坐标有固定有限闭区间 $[-K_0(s,t),K_0(s,t)]$，包括退化为单点的区间。零向量可行，故 $\mathcal P_N$ 非空紧致，最大值存在。符号替换 $z\mapsto-z$ 保留所有行，所以最大绝对值也等于 $m_N$，只需一个正向目标；$K_0(x,y)=2$ 给上界。$\mathcal P_{N+1}$ 的限制落在 $\mathcal P_N$，给单调性。

这里使用的有限有理线性规划事实作为中间工具：非空有界有理多面体有有理顶点，线性目标的最大值在这样的顶点取得。先在原目标的最大值面上依次最大化全部坐标，所得嵌套非空紧面最后只有一个点，因而是原可行域的极点。在极点处，等式及活跃不等式的法向量必须张成整个坐标空间，否则沿一个非零共同零方向作充分小的双向移动仍可行，违背极点的定义。选取满秩有理行并作有理消元，便给有理坐标。这同样涵盖等式相关、低维可行域和被零距离固定的坐标。因此 $m_N\in\mathbb Q$；对有理 $q$，$\mathcal P_N(q)$ 若非空也有有理点。

完整性的关键是每条全域行最终出现。给定四个原项 $a,b,u,v$，取 $N$ 不小于其大小，则它们同属 $T_N$，全部三个乘积端点同属 $E_N$，对应完整四变量行就在 (38.13) 中。给定 $a,b$，足够大的 $N$ 同时包含两条 $P_3$ 行及其端点。给定任意项对，足够大的 $N$ 包含其反对称行与全部界，零距离对也不例外。因此任何有限组全域行均被某一个共同系统收纳。

应用本卷定理 25.2 证明中的共同盒紧致性方法及有限正性桥定理 13.1 的对角抽取，盒改为

$$
\mathcal B=\prod_{(s,t)\in T^2}[-K_0(s,t),K_0(s,t)].
\tag{38.21}
$$

具体地，对每个 $N$ 取 $\mathcal P_N$ 的一个最大值点，在未出现坐标补零，均得到 $\mathcal B$ 中的点。可数项对的每个坐标都在同一个紧区间内，逐坐标抽子序列，再取原指标严格递增的对角子序列。每条固定行从某处起均成立，且只含有限坐标，故传到极限。极限 $d_*$ 满足全部反对称、全部支配、完整 $(R_D)$ 和两种 $P_3$ 等式，处处有限；其指定坐标等于单调极限 $\inf_Nm_N$。另一方面，每个全域 $d$ 的限制可行，所以 $d(x,y)\le m_N$ 对全部 $N$ 成立。这证明 (38.16)，没有要求有限层最大值点彼此一致，也没有假定 $M$ 上的拓扑。

若存在非零原残差，定理 38.2 给某个固定 $d$ 的正坐标，选同一个有理数 $0<q\le d(x,y)$，则每个 $\mathcal P_N(q)$ 非空，前述有理顶点事实给 (38.17)。反之，(38.17) 给每个 $m_N\ge q$，所以 (38.16) 的全域最大值至少为这个固定正数，再用定理 38.2。也可直接对这些有理点作同一盒抽取，闭不等式 $d(x,y)\ge q$ 随极限保留；极限不要求有理。不能将此处 $\exists q\,\forall N$ 改成 $\forall N\,\exists q_N>0$。

因零残差可行，(38.16) 的右侧非负。它等于零当且仅当 (38.18) 成立。若该下确界为正，就能选严格小于它的正有理 $q$，与 (38.18) 矛盾。指定坐标与普遍消失的联系使用定理 38.2 最后一段的重新求值，而不是遗漏其他坐标。

最后，对固定有理 $q>0$，$m_N<q$ 恰指 $\mathcal P_N(q)$ 不可行。复用本卷 (25.6) 的有理 Farkas 形式；经典有限维替代定理参见 Boyd–Vandenberghe，*Convex Optimization* §5.8，印刷页 263，[原文](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)。将自由变量拆成正负部分、给不等式加松弛变量后，不可行性等价于某个有理线性组合产生常数负值。归一化为 $-1$，写回原坐标即得

$$
-1=\sum\lambda'_{s,t,\sigma}(K_0(s,t)-\sigma z_{s,t})
+\sum\rho'_e e(z)+\mu(z_{x,y}-q),
\tag{38.22}
$$

其中 $\lambda'\ge0,\mu\ge0$ 有理，$\rho'$ 有理。必有 $\mu>0$：若 $\mu=0$，代入 $z=0\in\mathcal P_N$，右侧非负而左侧为 $-1$。除以 $\mu$ 并移项便得 (38.19)，其中 $\delta=1/\mu>0$。反之，(38.19) 在 $\mathcal P_N$ 上给 $z_{x,y}\le q-\delta<q$，因而就是严格上界。符号对称性同时给反向上界，无需把不同变量族或不同几何的最优值组合。证毕。

**命题 38.5（有限可见窗口不能精确迫零）。**从反对称性、完整 $(R_D)$、两种 $P_3$ 恒等式及支配界中任取有限组行，令 $E$ 包含它们全部项对端点以及 $1,x,y$。若整数 $L\ge1$ 满足 $\|fs\|\le L$ 对全部 $s\in E$ 成立，则该有限系统即使加入 $E^2$ 上的全部支配和反对称行，仍有显式有理可行点使 $d(x,y)=1/L>0$。特别，对定义 38.3 的整套有限系统有

$$
m_N\ge\frac1{2N}>0.
\tag{38.23}
$$

因此，任何有限条原始行的有效线性证书都不能迫出 $d(x,y)=0$；这不排除 (38.18)–(38.19) 随窗口扩大的一族严格正上界趋零。

**证明。**在 $\mathbb C^2$ 上使用经典实交替双线性型

$$
\beta(z,w)=\operatorname{Re}(z_1\overline{w_2}-z_2\overline{w_1}),\qquad
b(s,t)=\beta(fs,ft).
\tag{38.24}
$$

直接取共轭给 $\beta(w,z)=-\beta(z,w)$，Cauchy–Schwarz 给 $|\beta(z,w)|\le\|z\|\|w\|$，共同相位消去给 $\beta(\omega z,\omega w)=\beta(z,w)$，且 $\beta(e_1,e_2)=1$。设 $A=fa,B=fb,Q=fu,R=fv$。实双线性展开中，$\sum_{k=0}^2\omega^kQ=\sum_{k=0}^2\omega^kR=0$ 使两组交叉项消失，而共同旋转项各等于 $\beta(Q,R)$，故

$$
\sum_{k=0}^2\beta(A+\omega^kQ,B+\omega^kR)
=3\beta(A,B)+3\beta(Q,R).
\tag{38.25}
$$

这对全部四个原项成立，所以 $b$ 满足完整 $(R_D)$。$f(P_3s)=fs$ 分别给 $b(P_3s,t)=b(s,t)$ 和 $b(s,P_3t)=b(s,t)$；没有取项商。若 $K_0(s,t)=0$，则 $fs=ft$，交替性给 $b(s,t)=0$，所以零距离对也保留。

在有限 $E$ 上限制全项函数 $b/L$。当 $K_0(s,t)>0$ 时，(38.20) 给 $K_0(s,t)\ge1$，于是

$$
\begin{aligned}
|b(s,t)|&=|\beta(fs-ft,ft)|\\
&\le L\sqrt{K_0(s,t)}\le L K_0(s,t).
\end{aligned}
\tag{38.26}
$$

零距离情形已单独处理，故 $E^2$ 上全部支配成立；其余等式由全项 $b$ 继承，指定坐标为 $1/L$。Eisenstein 整数乘积的实部属于 $\tfrac12\mathbb Z$，所以全部 $b(s,t)/L$ 有理。对 $T_N$ 按正规项归纳有 $\|fs\|\le |s|\le N$；(38.12) 中的乘积端点范数至多 $2N$，第三标记端点范数不变。因此 $E_N$ 可取 $L=2N$，得到 (38.23)。若一个有限原始行证书迫出指定坐标为零，取其全部端点组成 $E$，以上正可行点立即反驳该证书。这也说明窗口范数至多 $L$ 时，任何小于 $1/L$ 的上界都不能由该窗口的行推出。

这个中间交替型不供应全域反模型。保留括号递归定义 $r_0=1,r_{n+1}=r_n\cdot y,s_n=x\cdot r_n$，则

$$
fr_n=ne_2,\quad fs_n=e_1+ne_2,\quad
K_0(s_n,r_n)=1,\quad b(s_n,r_n)=n.
\tag{38.27}
$$

故任何固定非零倍数 $\alpha b$ 在 $|\alpha|n>1$ 时违反全域支配。有号等式解与非负完整核的区别，已见[续卷 V 命题 5.4](AURIC_C133_THREE_READ_CLOSURE_VISIBLE_COMPLEX_GEOMETRY_CONTINUATION_V.md#5-保留括号的非零模型与完整三历史提升)的有号立方机制；此处交替型只承担有限窗口下界的中间用途。证毕。

**对应 38.6（几何图景与适用边界）。**定理 38.2 的归约是给全部自由配方换一把具有统一支配证明的尺：原来两个来源的像不必正交，甚至可以相关；标准两根坐标轴与同一缩放仍能承载一个非零残差见证。它改变比较值，不保持原始比较矩阵，也不供应物理准备。命题 38.5 则说有限窗内总能留下一滴有向面积；同一滴面积沿长配方却会超过固定的距离预算，因而有限窗可行不能冒充全域反模型。“两两可比较，比较结果跟顺序无关”在这里对应端点交换 $c(a,b)=c(b,a)$，与先测哪一个的顺序测量可交换是不同命题。

承重的 repo-derived 内容是此残差类到固定标准几何中指定坐标的精确存在性等价，以及该几何下保留全部原始行的有理穷尽及其有限窗口障碍。自由项求值、共同盒紧致性、有理 Farkas 与交替双线性型均为推导内的经典工具，不作为新的独立数学成果。本节没有给出 (38.19) 的趋零证书族、任何消失速率或有限截止，也没有构造满足全域支配的非零残差；有限层有理可行不要求全域解有理。不主张历史新颖性、文献穷尽性、计算复杂度优势或物理维数为二。

定义 38.1 的对称 Hilbert 背景、纯相位 $F$ 与两种 $P_3$ 前件没有从每个原始完整 (R) 模型取得；因此对应 37.3 的更大蕴涵仍未解决。对应 37.2 的全部实际来源前件继续保留，本节没有完成量子起源。

## 追加锚（三个有向比较族的单侧返回分类；本行以下为增补区）

## 39. 支配残差的端点均值与有限插入矩形

**定义 39.1（原标签上的标记插入）。**取定义 38.1 的全部前件：$M$ 是带真实双侧单位 $1$ 的任意 magma，$U:M\to M$ 任意，$H$ 是任意维复 Hilbert 空间，$\omega=\exp(2\pi i/3)$，且 $F:M\to H$ 满足

$$
F1=0,\qquad F(a\cdot b)=Fa+Fb,\qquad F(Ua)=\omega Fa.
\tag{39.1}
$$

处处有限的实函数 $D:M^2\to\mathbb R$ 对全部 $a,b,u,v\in M$ 满足

$$
\begin{aligned}
D(b,a)&=-D(a,b),& |D(a,b)|&\le\|Fa-Fb\|^2,\\
\sum_{k=0}^2D\bigl(a\cdot(U^ku),b\cdot(U^kv)\bigr)
&=3D(a,b)+3D(u,v).
\end{aligned}
\tag{39.2}
$$

对整数 $j\ge0$，置 $p_j=U^j1$、$P_j(a)=a\cdot p_j$；两个第三标记规则分别为

$$
D(P_3(a),b)=D(a,b),\qquad D(a,P_3(b))=D(a,b)
\qquad(a,b\in M).
\tag{39.3}
$$

所有变量取实际标签，保留原有次序、二叉括号、单位标签与重复标签。不假设乘法结合、$U$ 保乘法或满射、$F$ 单射，亦不假设 $D$ 沿 $F$ 的纤维下降。$P_3$ 由 $U^31$ 定义，不将它等同于 $P_1$ 的三次复合。Hilbert 背景和纯相位规则 (39.1) 是假设；三相指数的个数不限制 $H$ 的维数。

**定理 39.2（两端均值与四种基本混合矩形）。**在定义 39.1 的全部条件下，对每个有序标签对 $a,b\in M$，有

$$
\begin{aligned}
D(P_1(a),b)+D(P_2(a),b)&=2D(a,b),\\
D(a,P_1(b))+D(a,P_2(b))&=2D(a,b).
\end{aligned}
\tag{39.4}
$$

并且对每个 $i,j\in\{1,2\}$，同时有

$$
D(P_i(a),P_j(b))-D(P_i(a),b)-D(a,P_j(b))+D(a,b)=0.
\tag{39.5}
$$

**证明。**由 (39.1) 对 $j$ 归纳，$F(p_j)=\omega^jF1=0$，所以 $F(P_j(a))=Fa$。支配界给 $D(1,1)=D(p_1,1)=D(1,p_1)=0$。

固定任意实际标签 $a_0,b_0$，令 $\xi=Fa_0$、$\eta=Fb_0$，取整个有序纤维对

$$
E=\{(a,b)\in M^2:Fa=\xi,\ Fb=\eta\},\qquad
h=D|_E,\qquad \|h\|_\infty\le C:=\|\xi-\eta\|^2<\infty.
\tag{39.6}
$$

在实 Banach 空间 $\ell^\infty(E;\mathbb R)$ 上，对 $j=1,2,3$ 定义

$$
(L_jg)(a,b)=g(P_j(a),b),\qquad
(R_jg)(a,b)=g(a,P_j(b)).
\tag{39.7}
$$

插入保持各端的 $F$ 值，故这些都是线性压缩算子。任意 $L_i$ 与任意 $R_j$ 交换，因为两种复合在 $(a,b)$ 上均取值 $g(P_i(a),P_j(b))$；不假设同端点的两个插入算子交换。式 (39.3) 给 $L_3h=h$ 与 $R_3h=h$。

在完整四变量关系中依次取 $(u,v)=(1,1),(p_1,1),(1,p_1)$，保留全部实际乘积，得到

$$
\begin{aligned}
D(a,b)+D(a\cdot p_1,b\cdot p_1)+D(a\cdot p_2,b\cdot p_2)
&=3D(a,b),\\
D(a\cdot p_1,b)+D(a\cdot p_2,b\cdot p_1)+D(a\cdot p_3,b\cdot p_2)
&=3D(a,b),\\
D(a,b\cdot p_1)+D(a\cdot p_1,b\cdot p_2)+D(a\cdot p_2,b\cdot p_3)
&=3D(a,b).
\end{aligned}
\tag{39.8}
$$

这里第零项只约简真实单位；$U(p_1)=p_2$、$U^2(p_1)=p_3$ 只是一元迭代。第二式末项用第一端点的 (39.3)，第三式末项另用第二端点的 (39.3)，于是

$$
\begin{aligned}
(L_1R_1+L_2R_2)h&=2h,\\
(L_1+L_2R_1+R_2)h&=3h,\\
(R_1+L_1R_2+L_2)h&=3h.
\end{aligned}
\tag{39.9}
$$

这些等式作用于 $h$，不作为整个函数空间上的算子恒等式。

置

$$
S=\frac{L_1+L_2}{2},\qquad T=\frac{R_1+R_2}{2},\qquad
Q_S=\frac{I+2S}{3},\qquad Q_T=\frac{I+2T}{3}.
\tag{39.10}
$$

$S,T$ 是交换的压缩算子，$Q_S,Q_T$ 亦然。将 (39.9) 三式相加，得

$$
(4ST+2S+2T)h=8h,\qquad
Q_SQ_Th=\frac{I+2S+2T+4ST}{9}h=h.
\tag{39.11}
$$

以下用经典二项式公式与有限加权 Cauchy–Schwarz 给出取极限所需的中间估计。对任意实 Banach 空间上的线性压缩算子 $Z$，令 $Q_Z=(I+2Z)/3$。对每个整数 $n\ge0$，有

$$
\|(I-Z)Q_Z^n\|\le\frac{3}{\sqrt{2(n+1)}}.
\tag{39.12}
$$

确实，置 $q=2/3$，令 $b_{n,k}=\binom nkq^k(1-q)^{n-k}$ 当 $0\le k\le n$，区间外置零。有限二项式展开给

$$
(I-Z)Q_Z^n=\sum_{k=0}^{n+1}(b_{n,k}-b_{n,k-1})Z^k.
\tag{39.13}
$$

写 $N=n+1$、$c_k=\binom Nkq^k(1-q)^{N-k}$。直接约去阶乘得

$$
b_{n,k}-b_{n,k-1}=\frac{Nq-k}{Nq(1-q)}c_k
\qquad(0\le k\le N),
\tag{39.14}
$$

包括 $k=0,N$ 两端。多项式 $(1-q+qt)^N$ 在 $t=1$ 的取值及一、二阶导数给

$$
\sum_{k=0}^Nc_k=1,\quad
\sum_{k=0}^Nkc_k=Nq,\quad
\sum_{k=0}^Nk(k-1)c_k=N(N-1)q^2,\quad
\sum_{k=0}^N(k-Nq)^2c_k=Nq(1-q).
\tag{39.15}
$$

因此加权 Cauchy–Schwarz 给

$$
\sum_{k=0}^N|b_{n,k}-b_{n,k-1}|
\le\frac{\sqrt{\bigl(\sum_kc_k\bigr)\bigl(\sum_k(k-Nq)^2c_k\bigr)}}{Nq(1-q)}
=\frac{3}{\sqrt{2N}}.
\tag{39.16}
$$

结合 $\|Z^k\|\le1$ 和 (39.13) 即证 (39.12)，对每个 $n\ge0$ 均成立。

由 (39.11) 和交换性，对全部 $n\ge0$ 都有 $h=Q_S^nQ_T^nh$。用 (39.12) 分别取 $Z=S,T$，并用另一算子幂的压缩性，得到

$$
\|(I-S)h\|_\infty\le\frac{3\|h\|_\infty}{\sqrt{2(n+1)}},\qquad
\|(I-T)h\|_\infty\le\frac{3\|h\|_\infty}{\sqrt{2(n+1)}}.
\tag{39.17}
$$

所有插入历史均留在同一个 $E$，共享 (39.6) 的同一个有限界 $C$。令 $n\to\infty$，得 $Sh=h$、$Th=h$，即两个端点均值恒等式在整个 $E$ 上成立。没有为不同 $n$ 更换来源或支配常数，也不需要 $M$ 上的拓扑。

最后置 $\delta_i=L_i-I$、$\varepsilon_j=R_j-I$，$i,j\in\{1,2\}$。均值等式给 $(\delta_1+\delta_2)h=0$ 与 $(\varepsilon_1+\varepsilon_2)h=0$。只用异端点交换，分别在前一式上作用 $\varepsilon_j$、在后一式上作用 $\delta_i$，得到

$$
\delta_2\varepsilon_jh=-\delta_1\varepsilon_jh,\qquad
\delta_i\varepsilon_2h=-\delta_i\varepsilon_1h.
\tag{39.18}
$$

展开 (39.9) 的第一式，并消去两端均值项，得

$$
(\delta_1\varepsilon_1+\delta_2\varepsilon_2)h=0.
\tag{39.19}
$$

式 (39.18) 又给 $\delta_2\varepsilon_2h=\delta_1\varepsilon_1h$，故 $2\delta_1\varepsilon_1h=0$，继而四个 $\delta_i\varepsilon_jh$ 全部为零。在 $(a_0,b_0)$ 取值即为 (39.5)，两个均值同样给 (39.4)。$a_0,b_0$ 任意，所以结论覆盖全部原标签及两种端点次序。

若 $\xi=\eta$，则 $C=0$ 且 $h=0$，上述证明仍成立，没有除以 $C$。这也包含零维 Hilbert 空间；任意维数、非单射 $F$、重复标签和线性相关的像均不改变论证。证毕。

**推论 39.3（任意有限插入字的混合矩形）。**在定义 39.1 的全部条件下，对字母表 $\{1,2\}$ 上的有限字递归定义

$$
W_{\varnothing}(a)=a,\qquad W_{wi}(a)=P_i(W_w(a))=W_w(a)\cdot p_i.
\tag{39.20}
$$

对任意两个有限字 $w,z$（允许空字）及全部实际 $a,b\in M$，有

$$
D(W_w(a),W_z(b))-D(W_w(a),b)-D(a,W_z(b))+D(a,b)=0.
\tag{39.21}
$$

**证明。**在定理 39.2 的同一个实际纤维对 $E$ 上，若 $w=i_1\cdots i_m$、$z=j_1\cdots j_\ell$，令

$$
L_w=L_{i_1}\cdots L_{i_m},\qquad R_z=R_{j_1}\cdots R_{j_\ell},
\qquad L_{\varnothing}=R_{\varnothing}=I.
\tag{39.22}
$$

由拉回的复合次序，$L_wg(a,b)=g(W_w(a),b)$、$R_zg(a,b)=g(a,W_z(b))$，恰好保留 (39.20) 中逐次插入的括号和字母顺序。有限望远镜恒等式给

$$
\begin{aligned}
L_w-I&=\sum_{r=1}^m L_{i_1}\cdots L_{i_{r-1}}(L_{i_r}-I),\\
R_z-I&=\sum_{s=1}^{\ell} R_{j_1}\cdots R_{j_{s-1}}(R_{j_s}-I).
\end{aligned}
\tag{39.23}
$$

不需要同端点交换。将两个有限和相乘并作用于 $h$，仅用异端点交换，每一项成为

$$
L_{i_1}\cdots L_{i_{r-1}}R_{j_1}\cdots R_{j_{s-1}}
(L_{i_r}-I)(R_{j_s}-I)h=0,
\tag{39.24}
$$

其中最后的零是定理 39.2 在整个 $E$ 上的四种矩形恒等式。因此 $(L_w-I)(R_z-I)h=0$，在任意 $(a,b)\in E$ 取值即得 (39.21)。若有空字，对应有限和为空，结论同样成立。证毕。

## 追加锚（三个有向比较族的单侧返回分类；本行以下为增补区）

## 40. 原支配残差的个别标记桥与普遍消失

**定理 40.1（定义 38.1 全域类的残差消失）。**设 $M$ 是任意带真实双侧单位 $1$ 的 magma，$U:M\to M$ 任意，$H$ 是任意维复 Hilbert 空间，$\omega=\exp(2\pi i/3)$。设 $F:M\to H$ 满足

$$
F1=0,\qquad F(a\cdot b)=Fa+Fb,\qquad F(Ua)=\omega Fa
\qquad(a,b\in M).
\tag{40.1}
$$

设处处有限的实函数 $D:M^2\to\mathbb R$ 对全部原标签 $a,b,u,v\in M$ 满足

$$
\begin{aligned}
D(b,a)&=-D(a,b),\qquad |D(a,b)|\le\|Fa-Fb\|^2,\\
\sum_{k=0}^2D\bigl(a\cdot(U^ku),b\cdot(U^kv)\bigr)
&=3D(a,b)+3D(u,v).
\end{aligned}
\tag{40.2}
$$

记 $p_j=U^j1$、$P_j(a)=a\cdot p_j$，并对全部 $a,b\in M$ 分别要求

$$
D(P_3(a),b)=D(a,b),\qquad D(a,P_3(b))=D(a,b).
\tag{40.3}
$$

则在同一个原始 $M$ 上，两个端点的个别插入均不可见，且残差恒为零：

$$
\begin{aligned}
D(P_j(a),b)&=D(a,b)=D(a,P_j(b))
&& (a,b\in M,\ j=1,2),\\
D(a,b)&=0 && (a,b\in M).
\end{aligned}
\tag{40.4}
$$

所有量词包含重复标签、零像与非忠实 $F$。不要求乘法结合或交换、$U$ 保乘法或满射，也不预设 $D$ 沿 $F$ 的纤维下降。$P_3$ 仍由 $U^31$ 定义，不与 $P_1$ 的三次复合相认。

**证明。**在原 $M$ 上置

$$
K(a,b)=\|Fa-Fb\|^2,\qquad c(a,b)=K(a,b)+D(a,b).
\tag{40.5}
$$

由 (40.1)，$F(p_j)=0$、$F(P_j(a))=Fa$ 对每个整数 $j\ge0$ 成立。故 $K$ 在两种端点插入下均不变，且支配界给 $0\le c(a,b)\le2K(a,b)$、$c(a,a)=0$。对 $A=Fa-Fb$、$Q=Fu-Fv$，有

$$
\sum_{k=0}^2\|A+\omega^kQ\|^2=3\|A\|^2+3\|Q\|^2.
\tag{40.6}
$$

因此 $K$ 与 $c$ 均满足原乘法、原 $U$ 上的完整四变量 (R)。由 (40.3) 和定理 39.2 的两个端点均值，$c$ 满足

$$
\begin{aligned}
c(P_3(a),b)&=c(a,b),& c(a,P_3(b))&=c(a,b),\\
c(P_1(a),b)+c(P_2(a),b)&=2c(a,b),\\
c(a,P_1(b))+c(a,P_2(b))&=2c(a,b).
\end{aligned}
\tag{40.7}
$$

这里直接使用 (39.4)；不需要混合矩形 (39.5) 或有限字结论。均值本身尚未给出任一个别插入相等。

先取得完整三次返回。对固定 $u,v$，令 $s_n=c(U^nu,U^nv)$。完整 (R) 在背景 $(1,1)$ 给 $s_{n+1}+s_{n+2}=2s_n$，而 (40.1)、(40.5) 给对全部 $n\ge0$ 的共同界 $0\le s_n\le2K(u,v)$。递推解为 $A_0+A_1(-2)^n$，有界性迫 $A_1=0$。所以 $c(Uu,Uv)=c(u,v)$。对任意原 $a,b,u,v$ 再置 $t_j=c(a\cdot(U^ju),b\cdot(U^jv))$。完整 (R) 用于来源 $(U^ju,U^jv)$ 后给

$$
t_j+t_{j+1}+t_{j+2}=3c(a,b)+3c(u,v),\qquad t_{j+3}=t_j
\quad(j\ge0).
\tag{40.8}
$$

第二式由相邻两条第一式相减。取 $v=1$，用 (40.7) 的第二端点 $P_3$ 返回消去 $t_3$ 中的 $b\cdot p_3$；取 $u=1$，另用第一端点返回。于是

$$
\begin{aligned}
c(a\cdot(U^3u),b)&=c(a\cdot u,b),\\
c(a,b\cdot(U^3v))&=c(a,b\cdot v),\\
c(U^3u,b)&=c(u,b),\qquad c(b,U^3u)=c(b,u).
\end{aligned}
\tag{40.9}
$$

末行分别在首式取 $a=1$、次式取 $b=1$，并重命名自由探针。它是全部探针上的两种配对次序，未断言对象等式 $U^3u=u$。

沿用[有限正性桥引理 2.1、2.3](AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE.md)的自由实差空间构造，对此处同一个核 $c$ 定义

$$
\begin{aligned}
E_0&=\operatorname{span}_{\mathbb R}\{e_a=\delta_a-\delta_1:a\in M\},\qquad e_1=0,\\
q(a)&=c(a,1),\qquad r(a)=c(1,a),\\
B(e_a,e_b)&=\frac{q(a)+r(b)-c(a,b)}2,\\
\mathcal N&=\{n\in E_0:B(n,E_0)=B(E_0,n)=0\}.
\end{aligned}
\tag{40.10}
$$

$B$ 先按自由生成元双线性延拓，不要求对称或正定。特别，$\mathcal N$ 同时包含两个方向的全部零配对条件。该引理的完整行列刻画为：$e_x-e_y\in\mathcal N$ 当且仅当对每个原标签 $z$ 同时有 $c(x,z)=c(y,z)$、$c(z,x)=c(z,y)$；反向刻画使用 $c\ge0$，不以零比较传递性为前提。四点公式为

$$
2B(e_x-e_s,e_y-e_t)=-c(x,y)+c(x,t)+c(s,y)-c(s,t).
\tag{40.11}
$$

在自由空间上定义线性映射 $Se_a=e_{Ua}-e_{p_1}$。逐次展开可得 $S^ke_a=e_{U^ka}-e_{p_k}$。由同步等距 $c(Ux,Uy)=c(x,y)$ 及 (40.11)，有 $B(Sx,Sy)=B(x,y)$。式 (40.9) 的完整行列返回给 $e_{U^3a}-e_a\in\mathcal N$；式 (40.7) 在插入端点取 $1$ 又给 $e_{p_3}\in\mathcal N$。因此

$$
(S^3-I)e_a=e_{U^3a}-e_a-e_{p_3}\in\mathcal N,
\qquad (S^3-I)E_0\subseteq\mathcal N.
\tag{40.12}
$$

现在验证根稳定性。对任意 $n\in\mathcal N$、$y\in E_0$，两个次序分别满足

$$
\begin{aligned}
B(Sn,y)&=B(Sn,S^3y)=B(n,S^2y)=0,\\
B(y,Sn)&=B(S^3y,Sn)=B(S^2y,n)=0.
\end{aligned}
\tag{40.13}
$$

第一步只使用 $S^3y-y\in\mathcal N$，第二步使用自由空间上的等距。因此 $S\mathcal N\subseteq\mathcal N$，此后才在 $V=E_0/\mathcal N$ 上定义诱导算子 $T$，并记 $\beta(a)=[e_a]$。商上的 $B$ 满足

$$
T^3=I,\qquad B(Tx,Ty)=B(x,y),\qquad
\bigl[B(w,x)=B(x,w)=0\ \text{对全部 }x\in V\bigr]\Longrightarrow w=0.
\tag{40.14}
$$

最后一项来自完整双侧根空间的定义；没有假定任一个单侧根空间为零。$\beta(M)$ 实线性张成 $V$，维数可任意，也可为零。

接着把端点均值译成根向量，并保留锚。对每个原标签 $z$，置 $v_z=e_{P_1(z)}+e_{P_2(z)}-2e_z$。由 (40.7)，对每个原探针 $w$，有

$$
\begin{aligned}
2B(v_z,e_w)
&=q(P_1(z))+q(P_2(z))-2q(z)\\
&\quad-c(P_1(z),w)-c(P_2(z),w)+2c(z,w)=0,\\
2B(e_w,v_z)
&=r(P_1(z))+r(P_2(z))-2r(z)\\
&\quad-c(w,P_1(z))-c(w,P_2(z))+2c(w,z)=0.
\end{aligned}
\tag{40.15}
$$

这里 $q$ 的相消使用第一端点均值的探针 $1$，$r$ 的相消另用第二端点均值的探针 $1$。故 $v_z\in\mathcal N$。尤其 $v_1=e_{p_1}+e_{p_2}\in\mathcal N$。对 $j=0,1,2$ 定义

$$
\begin{aligned}
A_j(z)&=e_{P_j(z)}-e_z-e_{p_j},&
\alpha_j(z)&=[A_j(z)],& \tau_j&=\beta(p_j),\\
A_0(z)&=0,& \alpha_2(z)&=-\alpha_1(z),& \tau_2&=-\tau_1.
\end{aligned}
\tag{40.16}
$$

其中 $A_1(z)+A_2(z)=v_z-v_1$。各个 $\alpha_j(z)$ 仍按原标签 $z$ 定义，没有将 $\alpha_1$ 视为 $\beta(z)$ 上已经良定义的函数或线性算子。

完整四变量关系提供消去这些个别缺陷的另一组约束。在 $E_0$ 上置 $X_k(a,u)=e_{a\cdot(U^ku)}-e_{p_k}$。有限正性桥式 (2.3) 在这里恰为

$$
\sum_{k=0}^2B(X_k(a,u),X_k(b,v))
=3B(e_a,e_b)+3B(e_u,e_v).
\tag{40.17}
$$

具体地，左侧的两倍由 (40.11) 展开，依次对原输入 $(a,b,u,v)$、$(a,1,u,1)$、$(1,b,1,v)$ 使用 (R)，得到

$$
-3c(a,b)-3c(u,v)+3q(a)+3q(u)+3r(b)+3r(v),
\tag{40.18}
$$

即右侧的两倍；所有乘积均保持原有次序和括号。分别用两个输入对 $(1,u),(z,1)$ 及其交换次序代入 (40.17)。因为 $X_k(1,u)=S^ke_u$、$X_k(z,1)=e_z+A_k(z)$，右侧均为零，遂得有限正性桥式 (8.6) 的两个方向：

$$
\begin{aligned}
B((I+S+S^2)e_u,e_z)&=-\sum_{k=0}^2B(S^ke_u,A_k(z)),\\
B(e_z,(I+S+S^2)e_u)&=-\sum_{k=0}^2B(A_k(z),S^ke_u).
\end{aligned}
\tag{40.19}
$$

在合法商空间上置 $L=I+T+T^2$、$J=T-T^2$。固定任意原标签 $z$，记 $y=\beta(z)$、$n_z=\alpha_1(z)$。由 (40.16)、(40.19)，先对 $x=\beta(u)$，再由张成性对每个 $x\in V$，得到

$$
B(Lx,y)=-B(Jx,n_z),\qquad
B(y,Lx)=-B(n_z,Jx).
\tag{40.20}
$$

由于 $T^3=I$ 且 $T$ 保持 $B$，移动算子到配对的另一侧时，有 $B(Tx,y)=B(x,T^2y)$、$B(x,Ty)=B(T^2x,y)$。因此 $L$ 移到另一侧仍为 $L$，$J$ 则变为 $-J$。式 (40.20) 给

$$
B(x,Ly-Jn_z)=0,\qquad B(Ly-Jn_z,x)=0
\quad(x\in V).
\tag{40.21}
$$

完整双侧非退化性遂给 $Ly=Jn_z$。只由 $T^3=I$ 展开的多项式恒等式为

$$
L^2=3L,\qquad LJ=0,\qquad J^2=L-3I.
\tag{40.22}
$$

对 $Ly=Jn_z$ 再作用 $L$，得到 $3Ly=0$，故 $Ly=0$、$Jn_z=0$。由于 $z$ 任意且 $\beta(M)$ 张成 $V$，有 $L=0$。再由 $J^2n_z=(L-3I)n_z=-3n_z$ 得 $n_z=0$。结合 (40.16)，这证明

$$
A_j(z)\in\mathcal N
\quad(z\in M,\ j=1,2),\qquad
B(A_j(z),e_w)=B(e_w,A_j(z))=0
\quad(w\in M).
\tag{40.23}
$$

这正是同一自由空间中有限正性桥定义 8.1 的 $\mathrm{UC}$，包含每个原 $z$、每个原探针 $w$ 和两个配对次序。

还须消去个别插入的仿射锚。由 (40.16) 和 $Se_{p_1}=e_{p_2}-e_{p_1}$，有 $T\tau_1=\tau_2-\tau_1=-2\tau_1$。已经取得的 $L=0$ 因而给

$$
0=L\tau_1=\tau_1-2\tau_1+4\tau_1=3\tau_1,
\qquad \tau_1=\tau_2=0.
\tag{40.24}
$$

故 $\beta(P_j(a))=\beta(a)+\tau_j+\alpha_j(a)=\beta(a)$，$j=1,2$。由 (40.10) 的完整行列根刻画，回到原标签可得

$$
c(P_j(a),b)=c(a,b),\qquad c(a,P_j(b))=c(a,b)
\quad(a,b\in M,\ j=1,2).
\tag{40.25}
$$

减去在两端标记插入下不变的 $K$，得到 (40.4) 的两种个别插入恒等式。这里没有把 $p_1,p_2$ 与实际单位相认，没有以 $U$ 的满射性提升探针，也没有把第一端点插入缺陷当成反对称函数。

最后将有限正性桥定理 8.2 应用于原来的 $M,\cdot,1,U$ 和恰为 (40.5) 的核 $c$：处处有限、非负、零对角及完整 (R) 已由 (40.5)–(40.6) 取得；该定理的 $E,B,\mathcal N$ 分别就是 (40.10) 的 $E_0,B,\mathcal N$，其全部 $\mathrm{UC}$ 前件正是 (40.23)。标签映射为 $M$ 上的恒等映射，不替换原对象或原核。故存在复 Hilbert 空间 $H_c$ 和 $G:M\to H_c$，满足

$$
\begin{aligned}
G1&=0,\qquad G(a\cdot b)=Ga+Gb,\\
G(Ua)&=\omega Ga+t,\qquad t=G(U1),\\
c(a,b)&=\|Ga-Gb\|^2\qquad(a,b\in M).
\end{aligned}
\tag{40.26}
$$

因此同一个 $c$ 对称。无需将 $G$ 与输入 $F$ 或其 Hilbert 空间相认；由 $K$ 对称及 $D$ 反对称，直接有

$$
2D(a,b)=c(a,b)-c(b,a)=0.
\tag{40.27}
$$

上述商空间论证对任意维数及零空间均成立；全域支配允许零距离纤维，未要求除以范数或另设非退化来源。证毕。

**推论 40.2（固定窗口阈值的全域极限）。**对定义 38.3 的同一有限系统与 (38.15) 的 $m_N$，有

$$
\mathscr D=\{0\},\qquad \inf_{N\ge1}m_N=0,\qquad
\forall q\in\mathbb Q_{>0}\ \exists N\ge1:\ m_N<q,
\tag{40.28}
$$

其中 $\mathscr D$ 仍为全部固定模型残差。每个固定有理 $q>0$ 都有定理 38.4 中 (38.19) 形式的严格有理 Farkas 证书；同时每个有限 $N\ge1$ 仍满足

$$
m_N\ge\frac1{2N}>0.
\tag{40.29}
$$

**证明。**定理 40.1 用于固定 $(T,\mathbb C^2,f)$ 给 $\mathscr D=\{0\}$。定理 38.4 的 (38.16)、(38.18)–(38.19) 分别给下确界、严格阈值及证书存在性；命题 38.5 给 (40.29)。这里不指定任何 $N$、趋零速率或证书系数；有限原始行不能精确迫零的结论仍由命题 38.5 保留。证毕。

**适用边界 40.3（新增桥梁与量子接口的范围）。**定理 40.1 的 repo-derived 增量是：由原完整关系及两条第三标记返回先取得合法三阶商作用，再由端点均值和两个轴配对次序推出 $L\beta(z)=J\alpha_1(z)$，继而消去全部单位轨道缺陷与仿射锚。端点均值复用定理 39.2；自由差空间、完整行列根刻画与轴恒等式分别复用有限正性桥引理 2.1、2.3 和式 (8.6)；取得 $\mathrm{UC}$ 后的分类直接复用同卷定理 8.2。线性递推和三阶算子多项式是推导内的经典工具，不另作独立新结果。不主张历史新颖性或文献穷尽性。

消失结论覆盖定义 38.1 的所有原项、所有四变量和所有支配读数；该定义输入的复 Hilbert 背景、可加 $F$、纯相位规则和两条 $P_3$ 返回，尚未从对应 37.3 的更大原始完整 (R) 类取得。因此这里没有把这个受支配残差类等同于更大的原始类，也没有从比较几何推出原始物理公理。

在唯一整体态 $\Omega$ 的建模前提下，观察者、参考、记录和读出仍须由 $\Omega$ 内部的实际有限门历史实现；上述自由项或商向量本身不供应实际历史。实际非零准备、事件与效果及完整菜单、共同联合与条件历史、可组合物理过程及其参考实现、连续时间与生成元，仍分别保留对应 37.2 及其所引接口的前件。三相指标 $k=0,1,2$、三标签测试、复 Hilbert 维数与物理或 Bloch 三维具有不同定义；本结论没有给出它们之间的新映射，也没有完成量子起源。

## 追加锚（三个有向比较族的单侧返回分类；本行以下为增补区）
