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
