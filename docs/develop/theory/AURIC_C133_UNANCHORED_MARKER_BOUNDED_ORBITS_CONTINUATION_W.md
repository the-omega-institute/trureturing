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
