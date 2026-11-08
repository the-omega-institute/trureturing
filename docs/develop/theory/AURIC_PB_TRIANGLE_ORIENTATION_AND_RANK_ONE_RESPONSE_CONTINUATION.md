# AURIC：配平三角的共同取向与秩一响应续卷

## 128. 同一二元关系的完整候选与实际角

**定义 128.1（原候选与续卷接口）。** 本卷承接 [《任意维小窗口单位桥》](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md) 的定义 64.1、119.1、120.1–120.3，沿用其编号。固定同一原实 Archimedean 序单位空间 $(E,C,u,N)$、同一原正实线性评价族 $\mathcal P$、同一总映射 $S,D:E^2\to E$。原评价分离 $E$，且

$$
x\in C\quad\Longleftrightarrow\quad\alpha(x)\ge0\quad(\alpha\in\mathcal P),
\qquad m_\alpha=\alpha(u).
\tag{128.1}
$$

保留全部零、不等与次归一质量，不将全部数学态认作实际准备。原 A1 要求全部实际有向 Hermitian 二表正性；原 A2 要求相加三表 $(a+b,a,b)$ 及其排列的实部在 $\mathbb R^3$ 上半正定，且原指定向量 $(1,-1,-1)$ 的二次值为零；原 A3 为 $S(u,u)=u$，并对同一个固定有理数 $0<\theta\le1$ 要求 $0\le e\le\theta u\Rightarrow S(e,e)\le e$。直接使用无 $R$ 接口已经得到的同一乘法 $a\circ b=S(a,b)$ 与忠实、等距、含单位、稠密 Jordan 包含

$$
E\subset X,\qquad C=E\cap X_+,\qquad N=\|\cdot\|_X|_E,
\tag{128.2}
$$

其中 $X$ 是含单位实 JB 代数。以下定理只消费这个既有接口和下列两个条件，不重新证明该接口。P2 是全部原 $a,b,\alpha$ 的

$$
\begin{pmatrix}
\alpha(a^2)&\alpha(a\circ b)-i\alpha D(a,b)\\
\alpha(b\circ a)-i\alpha D(b,a)&\alpha(b^2)
\end{pmatrix}\succeq0.
\tag{128.3}
$$

令

$$
\begin{aligned}
Q_\alpha(b,c)&=\alpha\bigl(b^2+c^2+2D(b,c)\bigr),\\
r_\pm&=b\pm D(a,b)\mp a\circ c,\\
s_\pm&=c\pm a\circ b\pm D(a,c).
\end{aligned}
$$

完整 PB 是对全部原 $a,b,c\in E$、$\alpha\in\mathcal P$ 要求

$$
Q_\alpha(r_+,s_+)=Q_\alpha(r_-,s_-).
\tag{128.4}
$$

不另加 $D$ 的可加、齐次、连续、酉协变、中央平移、NN、Jacobi、全部有限 Gram 正性或完成延拓。原目标仍是同一个旧 $D$ 的分别可加及全部原输入上的

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)).
\tag{128.5}
$$

原 $\Omega/\mathrm{native}$、全词 $K/J/q$、父位置和 ready 类型、原中心与不等维块、实际准备与完整效果菜单、共同记录与真正分组遗忘、全仪器及其环境和全部输出、实际相关联合与递归同源参考、全部合法顺序／自适应／并行历史及每个仍合法未来、停止／拒绝／销毁、同数两侧与真实逆向返回，均保持母卷的原量词。完整 CountRead 无穷、正常性与前对偶、物理钟、能量及共同 $\hbar$ 仍各有其原来源前件；有限数学角不截断这些量词。

**定义 128.2（已付有限差分与角内旧关系）。** 由原评价分离性和已知 Jordan 平方展开，PB 的元素形式为母卷的同一有限差分

$$
\begin{aligned}
v&=D(a,b)-a\circ c,& w&=a\circ b+D(a,c),\\
D(b+v,c+w)-D(b-v,c-w)&=-2b\circ v-2c\circ w.
\end{aligned}
\tag{128.6}
$$

这不展开未知 $D$ 对输入和的作用。母卷 119.2–119.3 给每个实际原幂等元 $k\in E$ 的闭合角 $E_k=E\cap X_2(k)$ 及其准确接口，121.1 将完整 PB 原样限制到该角，114.1 给完整自旋角分类。因而在一个实际有限复矩阵角 $J\cong_J H_n(\mathbb C)$ 中，每个秩二投影 $P$ 都有一个固定符号 $\varepsilon(P)\in\{1,-1\}$，满足

$$
D(x,y)=\varepsilon(P)\frac{[x,y]}{2i}\quad(x,y\in PJP).
\tag{128.7}
$$

所有符号均相对于同一个固定环境复矩阵乘法；$x\circ y=(xy+yx)/2$。这里没有认回一般高秩旧值。有限维 $X_k$ 时，119.3 的稠密性与有限维闭性给 $E_k=X_k$，所以该角的全部矩阵和投影都是原输入。

## 129. 读取同一二表的数学正泛函

**引理 129.1（数学读取的准确预算）。** 在定义 128.1 下，任何数学正实线性泛函 $\phi:E\to\mathbb R$ 都能读取同一个 P2。特别地，在实际复矩阵角中，取内积 $\langle x,y\rangle=x^*y$ 和 $\phi_\xi(t)=\xi^*t\xi$，有

$$
|\phi_\xi(D(x,y))|^2\le\Delta_\xi(x,y)
:=\|x\xi\|^2\|y\xi\|^2-
\bigl(\operatorname{Re}\langle x\xi,y\xi\rangle\bigr)^2.
\tag{129.1}
$$

证明。P2 的 Hermitian 性和分离性先给 $D(y,x)=-D(x,y)$。对任意 $z_1,z_2\in\mathbb C$，同一 P2 使元素

$$
|z_1|^2x^2+|z_2|^2y^2
+2\operatorname{Re}(\overline{z_1}z_2)x\circ y
+2\operatorname{Im}(\overline{z_1}z_2)D(x,y)
$$

被全部原评价读为非负。准确锥 (128.1) 使它属于 $C$，故任何数学正泛函也读为非负，正是同一二表的正性。矩阵向量读取的对角值是 $\|x\xi\|^2,\|y\xi\|^2$，实非对角值是 $\operatorname{Re}\langle x\xi,y\xi\rangle$，取行列式即得 (129.1)。角内正泛函作用于角内这个正元素即可，不要求先将它延到环境。这里使用准确锥的数学对偶，不新增实际准备，不供应三表或全有限 Gram 正性。∎

## 130. 有限 PB 三角证书

**定理 130.1（相邻二级角不能异号）。** 在实际 $H_3(\mathbb C)$ 角内，固定任意正交坐标框架 $e_1,e_2,e_3$，令 $p_j=e_je_j^*$、$P_{ij}=p_i+p_j$。则

$$
\varepsilon(P_{12})=\varepsilon(P_{13})=\varepsilon(P_{23}).
\tag{130.1}
$$

证明。先假设 $\eta=\varepsilon(P_{12})$、$\varepsilon(P_{13})=-\eta$，其中 $\eta^2=1$。约定 $X_{ij}=E_{ij}+E_{ji}$、$Y_{ij}=(E_{ij}-E_{ji})/i$。取全部有限的原输入

$$
a=\frac12p_1,\qquad
b=-p_1-\frac12p_2+X_{12},\qquad
c=3p_1+\frac12p_3+X_{13},\qquad
\xi=(1,2,-2)^T.
\tag{130.2}
$$

记 $\phi(t)=\xi^*t\xi$，则 $b\xi=c\xi=e_1$。两个内层输入对分别完全位于 $12$ 角和 $13$ 角，故且仅故可以用 (128.7) 得

$$
D(a,b)=\frac\eta4Y_{12},\qquad
D(a,c)=-\frac\eta4Y_{13}.
$$

在同一次 (128.6) 中，已知乘法给出

$$
v=-\frac32p_1+\frac\eta4Y_{12}-\frac14X_{13},\qquad
w=-\frac12p_1+\frac14X_{12}-\frac\eta4Y_{13}.
\tag{130.3}
$$

令 $r_\pm=b\pm v$、$s_\pm=c\pm w$、$d_\pm=D(r_\pm,s_\pm)$。不把这两个外层旧值认成交换子。直接相乘得

$$
v\xi=(-1-i\eta/2,\ i\eta/4,\ -1/4)^T,\qquad
w\xi=(-i\eta/2,\ 1/4,\ -i\eta/4)^T.
$$

所以 $\phi(b\circ v)=-1$、$\phi(c\circ w)=0$，同一次有限差分强迫

$$
\phi(d_+-d_-)=2.
\tag{130.4}
$$

另一方面，四个外层向量准确为

$$
\begin{aligned}
r_+\xi&=(-i\eta/2,\ i\eta/4,\ -1/4)^T,\\
s_+\xi&=(1-i\eta/2,\ 1/4,\ -i\eta/4)^T,\\
r_-\xi&=(2+i\eta/2,\ -i\eta/4,\ 1/4)^T,\\
s_-\xi&=(1+i\eta/2,\ -1/4,\ i\eta/4)^T.
\end{aligned}
\tag{130.5}
$$

它们的实 Gram 数据为

| 输入对 | $\|r_\pm\xi\|^2$ | $\|s_\pm\xi\|^2$ | $\operatorname{Re}\langle r_\pm\xi,s_\pm\xi\rangle$ | $\Delta_\xi(r_\pm,s_\pm)$ |
| --- | --- | --- | --- | --- |
| $+$ | $3/8$ | $11/8$ | $1/4$ | $29/64$ |
| $-$ | $35/8$ | $11/8$ | $9/4$ | $61/64$ |

分别对两个实际输出使用 129.1，得到

$$
|\phi(d_+)|\le\frac{\sqrt{29}}8<1,\qquad
|\phi(d_-)|\le\frac{\sqrt{61}}8<1.
$$

故 $|\phi(d_+-d_-)|<2$，与 (130.4) 矛盾。$\phi$ 在本角单位上的质量为 $9$；若改用 $\phi/9$，等式和界同时缩放，矛盾不变。再以 $p_2$ 为共同顶点，重标同一证明，给出余下两个角的比较。证明只认回两个角内的内层旧值；外层始终是同一总映射的未知值，分别受各自 P2 约束。所有数均固定有限，没有未知 $D$ 的极限、增量估计或可加展开。∎

## 131. 从三维相交传播到整个简单块

**定理 131.1（全部真实二级角的共同符号）。** 对一个实际 $J=H_n(\mathbb C)$ 角、$n\ge2$，存在由旧 $D$ 确定的单一符号 $\varepsilon_J$，使全部共同支撑于任一秩至多二角的 $x,y$ 满足

$$
D(x,y)=\varepsilon_J\frac{[x,y]}{2i}.
\tag{131.1}
$$

证明。$n=2$ 是已付完整角分类。先在任一三维复子空间 $W$ 中，令射线函数 $f(\ell)=\varepsilon(W\cap\ell^\perp)$。两条正交射线可以补成正交框架，130.1 给 $f(\ell)=f(m)$。两条不同而不正交的射线有共同正交射线 $t\subset W\cap(\ell+m)^\perp$，故 $f(\ell)=f(t)=f(m)$；同一射线直接相等。于是 $W$ 内所有二级角同号。

一般有限维中，两个不同二维子空间 $P,Q$ 若交于一条射线，则 $P+Q$ 三维，直接比较。若交为零，取射线 $\ell\subset P$、$m\subset Q$，令 $R=\ell+m$。$P+R$ 与 $Q+R$ 分别三维，故 $\varepsilon(P)=\varepsilon(R)=\varepsilon(Q)$。相同子空间无需比较。对每个实际框架使用 130.1 即可；没有假定 $D$ 酉协变或角参数连续。∎

**推论 131.2（原域与中央块边界）。** 一般原 $E\subset X$ 若实际含有 $k^2=k$，且 $X_2(k)\cong_J H_n(\mathbb C)$ 有限维，则同一个旧 $D|_{E_k^2}$ 满足 130.1–131.1。在有限直和 $E=\bigoplus_jH_{n_j}(\mathbb C)$ 中，每个非经典简单块各有一个共同 $\varepsilon_j$；不同中央块不必同号。

证明。128.2 给 $E_k=X_2(k)$ 以及原 P2/PB 的逐值继承。每个证明输入及外层调用都在该原角中。有限直和对每颗原中央单位应用这个结论。母卷 122.2 的逐块正、负交换子存在见证允许不同块选不同符号，故不能要求中央块间同号。此项未将任意混合块输入的旧 $D$ 分解为块和。∎

## 132. 任意高秩演员的秩一谱行

**定理 132.1（保留射线的演员对该射线响应为零）。** 在 $H_n(\mathbb C)$ 中，设 $p=ee^*$、$\|e\|=1$ 是秩一投影，$a=a^*$ 为任意阶数的原输入，且 $[a,p]=0$。则

$$
D(a,\mu p)=0\quad(\mu\in\mathbb R).
\tag{132.1}
$$

本结论不依赖 131.1 的全块取向一致性。

证明。$\mu=0$ 由 P2 的零对角预算给出。设 $\mu\ne0$，令 $d=D(a,\mu p)$、$q=1-p$，则 $ap=pa=\lambda p$，$\lambda\in\mathbb R$。对全部 $\zeta\in q\mathbb C^n$，第二输入的平方读数为零，129.1 给 $\zeta^*d\zeta=0$。对这个固定 Hermitian 矩阵作普通极化，得 $qdq=0$。对 $e$，两输入分别作用为 $\lambda e$、$\mu e$，实 Gram 行列式也是零，故 $pdp=0$。于是存在 $z\perp e$，使

$$
d=ze^*+ez^*,\qquad p\circ d=d/2.
\tag{132.2}
$$

若 $z=0$ 即得结论。若非零，$p,d$ 共同支撑于真实二级子空间 $K=\operatorname{span}_{\mathbb C}\{e,z\}$。在原 PB 中准确取 $(a,b,c)=(a,\mu p,0)$，则 $v=d$、$w=\mu\lambda p$。两个外层旧值均在同一个 $K$ 角中，由完整角公式它们同等于

$$
\begin{aligned}
D(\mu p+d,\mu\lambda p)
&=\varepsilon_K\frac{\mu\lambda[d,p]}{2i},\\
D(\mu p-d,-\mu\lambda p)
&=\varepsilon_K\frac{\mu\lambda[d,p]}{2i}.
\end{aligned}
$$

但 (128.6) 强迫其差为 $-2\mu p\circ d=-\mu d$，所以 $d=0$。没有从各个谱投影的零值展开一般输入和。∎

**推论 132.2（明确 $B(H)$ 完成中的原秩一消费者）。** 若另已给定 $X=B(H)_{\mathrm{sa}}$ 的忠实完成识别，$p\in E$ 是实际秩一投影，原 $a\in E$ 满足 $ap=\lambda p$，则 (132.1) 仍成立，包括无限维 $H$。

证明。129.1 的全部向量读取给同样的 $d=ze^*+ez^*$。若 $z\ne0$，其二级支撑投影为

$$
k=d^2/\|z\|^2\in E.
$$

因此 119.2–119.3 与有限角闭性给 $E_k=X_2(k)\cong_J H_2(\mathbb C)$，132.1 的两个外层调用合法，原证明直接成立。没有从完成随意借投影送入旧 $D$，也没有把一般 JB 完成识别成 $B(H)_{\mathrm{sa}}$。∎

## 133. 跨连接方向的受限真实可加性

**定理 133.1（整个连接子空间上的秩一行）。** 在一个实际复矩阵块中，固定 $p=ee^*$、$q=1-p$，记 $H(z)=ze^*+ez^*$、$z\in q\mathbb C^n$。对实线性空间

$$
\mathcal V_p=\{\beta p+H(z):\beta\in\mathbb R,\ z\in q\mathbb C^n\}
$$

及全部实 $\mu$，同一个旧映射满足

$$
D(\mu p,\beta p+H(z))
=\mu\varepsilon_J\frac{[p,H(z)]}{2i}
=H(i\mu\varepsilon_Jz/2).
\tag{133.1}
$$

因此固定首输入 $\mu p$ 后，原关系在整个 $\mathcal V_p$ 上实线性。

证明。每对输入共同支撑于 $\operatorname{span}_{\mathbb C}\{e,z\}$ 的秩至多二角，128.7 和 131.1 给所述公式。$z=0$ 时秩一角输出为零。对不同连接方向相加，先将合成输入认回 $e,z_1+z_2$ 的真实角，再使用已证共同符号；然后展开已知矩阵交换子即可。不在公式取得之前展开未知 $D$。例如

$$
D(p_1,X_{12}+X_{13})
=D(p_1,X_{12})+D(p_1,X_{13})
=\frac{\varepsilon_J}2(Y_{12}+Y_{13}).
$$

另一方面，132.1 和反对称给 $D(p,\beta p+B)=0$，其中 $B=qBq=B^*$。这两个子空间上的限制并不自动支付其混合输入上的相加。∎

## 134. 固定秩一输入的全部二表余量

**定理 134.1（单对 P2 的准确输出参数）。** 固定 $p=ee^*$，写任意 Hermitian 输入

$$
a=\beta p+H(z)+B,\qquad B=qBq=B^*.
$$

对这一对 $(p,a)$，其全部数学正读取的二表正性，准确等价于输出为 $d=\delta p+H(w)$，并存在 $h\in q\mathbb C^n$、$\tau\in\mathbb R$，满足

$$
\|h\|^2+\tau^2\le1,\qquad
\delta=\operatorname{Re}\langle h,z\rangle,\qquad
2w=Bh+i\tau z.
\tag{134.1}
$$

反向表的输出取 $-d$。参数 $\beta$ 不进入该单对可行集，辅助参数 $(h,\tau)$ 不要求唯一。

证明。首输入在 $q\mathbb C^n$ 上的零平方预算与固定矩阵极化先给 $qdq=0$，所以 $d=\delta p+H(w)$。取 $\xi=e+y$，$y\in q\mathbb C^n$，则

$$
p\xi=e,\qquad
a\xi=(\beta+\langle z,y\rangle)e+z+By.
$$

故其准确行列式预算为 $\|z+By\|^2+(\operatorname{Im}\langle z,y\rangle)^2$，二表正性要求

$$
\bigl(\delta+2\operatorname{Re}\langle w,y\rangle\bigr)^2
\le\|z+By\|^2+(\operatorname{Im}\langle z,y\rangle)^2
\quad(y\in q\mathbb C^n).
\tag{134.2}
$$

在已知有限维实 Hilbert 空间上定义实线性对象

$$
\ell(s,y)=s\delta+2\operatorname{Re}\langle w,y\rangle,\qquad
T(s,y)=(sz+By,\operatorname{Im}\langle z,y\rangle).
$$

对 $s\ne0$，在 (134.2) 中代入 $y/s$ 得 $|\ell(s,y)|\le\|T(s,y)\|$；对 $s=0$，比较 (134.2) 沿 $ty$ 的二次最高系数给同一不等式。这只比较固定矩阵产生的已知多项式。因而 $\ell$ 在 $\ker T$ 上消失，下降为 $\operatorname{ran}T$ 上范数至多一的实线性泛函。有限维实 Hilbert Riesz 表示、再在正交补取零，给范数至多一的 $(h,\tau)$，使

$$
\ell(s,y)=\operatorname{Re}\langle h,sz+By\rangle
+\tau\operatorname{Im}\langle z,y\rangle.
$$

比较 $s,y$ 的系数，利用 $B=B^*$ 和 $\operatorname{Re}\langle i z,y\rangle=\operatorname{Im}\langle z,y\rangle$，得到 (134.1)。反向由实 Cauchy–Schwarz 立即得到 (134.2)。一般向量 $te+y$ 在 $t\ne0$ 时通过复标量缩放归入该式，$t=0$ 时零预算已处理。任意正泛函是向量正泛函的非负和，正二表之和仍正，故得到全部数学正读取。这里的核下降只涉及一个固定矩阵对的已知实线性 $T$，不涉及自由标签上的未知 $D$ 算子，也不提供全域可加性。∎

**命题 134.2（单对正性留下跨背景余量）。** 取 $p=p_1$、$a=X_{12}+p_3$，则 $d=X_{13}/2$ 满足这一对的全部 P2，但不同于 $\varepsilon_JY_{12}/2$。

证明。在 (134.1) 中取 $z=e_2$、$B=p_3$、$h=e_3$、$\tau=0$，范数预算恰为一，且 $\delta=0$、$2w=e_3$。不同矩阵位置使它不能等于所需交换子输出。此例仅给单对 P2 的余量，不构造满足全部 PB 的总映射。∎

## 135. 几何、量子对应与准确未证桥梁

**定义 135.1（共同取向的几何位置）。** 一个二级复矩阵角的归一数学态空间是 Bloch 三球，角内旧关系选择其两种取向之一。131.1 表明，三维复子空间的相交迫使同一简单块的全部三球共同定向，无需另给取向连续性。按原约定 $x\star y=x\circ y-iD(x,y)$，已识别角内的 $\varepsilon_J=-1$ 对应通常矩阵乘法，$\varepsilon_J=+1$ 对应相反乘法。这是对已识别输入的乘法判断，未将任意高秩旧 $\star$ 宣布为结合乘法。

成熟的几何位置见 Alfsen–Shultz，[*Orientation in operator algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，PNAS 95，6596–6601，DOI [10.1073/pnas.95.12.6596](https://doi.org/10.1073/pnas.95.12.6596)，“Dynamical Correspondences”、Theorem 1 与 “Geometric Orientations”。该文的动力对应从定义起即为到斜序导子的线性映射，几何全局取向采用有向三球丛的连续截面；这些是其定理的前件，不能用来支付本卷尚未证明的旧 $D$ 全域可加性。130.1 的有限证书、131.1 的旧关系取向识别、132.1 的谱行、133.1 的受限可加及 134.1 的单对余量是此处的 $\texttt{repo-derived}$ 综合，不宣称历史原创优先权。

**定义 135.2（与既有量子公理的条件对应）。** 母卷 122 的有限存在分类已经把 Jordan 底层选为有限个、不必等维的 $H_{n_j}(\mathbb C)$ 直和，包含经典块与空直和。124.1 的原正评价表示为

$$
\alpha(a)=\sum_j\operatorname{Tr}(\rho_{\alpha,j}a_j),\qquad
\rho_{\alpha,j}\succeq0,\qquad
\sum_j\operatorname{Tr}\rho_{\alpha,j}=m_\alpha.
$$

因此只有原来源实际供应完整效果菜单 $\sum_\ell e_\ell=u$，且 $m_\alpha>0$ 时，才取得该菜单的 Born 读数

$$
p_\alpha(\ell)=\frac{\sum_j\operatorname{Tr}(\rho_{\alpha,j}e_{\ell,j})}{m_\alpha}.
$$

质量零不作归一。矩阵识别与数学正读取不供应实际准备的满射性、测量仪器、共同张量或动力时钟。共同角取向把各局部复乘法的方向锁在同一块内，仍须下列旧值桥梁才能得到全域关系与相应动力生成元。

**定义 135.3（准确剩余目标）。** 由 132.1 与 133.1，固定秩一 $p$ 后，块对角输入和纯连接输入分别已确定；还须从同一完整 PB 证明

$$
D(p,\beta p+H(z)+B)=H(i\varepsilon_Jz/2).
\tag{135.1}
$$

在 134.1 中，这要求唯一识别实际输出 $\delta=0$、$2w=i\varepsilon_Jz$，不要求每份辅助证书唯一。标准输出可取 $h=0,\tau=\varepsilon_J$。即使 (135.1) 得证，还须支付实际旧值的有限谱相加，例如

$$
D\!\left(\sum_i\lambda_i p_i,b\right)=\sum_i\lambda_iD(p_i,b),
\tag{135.2}
$$

以及混合中央块独立性，才能在这些有限对象上认回任意给定旧 $D$。一般原 $E$ 的分别可加和 (128.5) 仍是更广目标。单对参数余量不是全 PB 反例，逐块存在标准见证也不解决任意旧关系的识别。

## 136. 二元正表如何锁住三维共同取向

**定义 136.1（完整白话）。** 候选仍是同一张二元有向关系：每对对象的正表必须成立，同一评价读到的正反两份平方必须配平。在已经由这些条件选出的有限复矩阵底层里，每个二级窗口各有一个正向或反向。把两个相邻窗口放进同一个三维角，选两份带不同对角成分的输入，使一个数学观察者看见它们落到同一条向量上；若两窗口反向，配平会要求后续两个旧输出的读数相差二，但每份输出自己的正表都只允许其读数绝对值小于一，于是反向选择不可能。这个有限矛盾沿真实三维子空间传递，使一个简单块里的全部窗口共用一个方向。再固定一条秩一射线：若演员保留它，正表把可能的输出压成一条连接向量；该向量与射线只占一个二级角，配平就把输出消掉。因此全部纯连接方向的响应已经真正可相加，整个保留射线的块对角背景响应也已为零。尚未完成的是把连接和背景同时放进一个输入时，旧关系是否仍只读取连接；单对正表允许的额外余量已经由一个单位球参数式完整写出。消去混合余量，再证明一般谱和的响应相加，才能认回全部原输入的同一个交换子关系和原量子恒等式。复数几何与条件 Born 读数有既有数学对应，真实仪器、无限记录、合法未来返回和物理时钟仍由原来源承担。

## 追加锚（本行以下为增补区）

## 137. 有限原对象与同一旧关系的比较缺陷

**定义 137.1（完整候选、有限模型与量词）。** 沿用 128.1–128.2 的同一原候选、准确锥、原评价标签、全部质量和全部来源量词。候选仍是原 P2 与完整 PB，不增添旧 $D$ 的可加、齐次、连续、可测、酉协变、单位平移、NN、Jacobi 或原 $R$。先在原域确实等于

$$
J=\bigoplus_{j=1}^kH_{n_j}(\mathbb C),\qquad n_j\ge1,\qquad
u=(I_{n_1},\ldots,I_{n_k})
\tag{137.1}
$$

的模型中证明；允许不等维、经典块与 $k=0$。全部矩阵均是原输入。对一般原 JB 完成的有限情形，143.1 再由母卷 122.1 支付 (137.1)，不把复数选型作为其新增假设。每个非经典块的共同角符号 $\varepsilon_j$ 已由 131.1–131.2 得到。

**定义 137.2（统一取向坐标与已知比较映射）。** 若第 $j$ 块 $\varepsilon_j=+1$，在这一块使用转置坐标；若 $\varepsilon_j=-1$ 或 $n_j=1$，使用原坐标。记这个实线性、保单位 Jordan 同构为 $T$。它保持正锥与范数；按

$$
\widetilde D(x,y)=T D(T^{-1}x,T^{-1}y),\qquad
\widetilde\alpha(x)=\alpha(T^{-1}x)
\tag{137.2}
$$

运输同一原关系和原评价，保留全部原标签和质量。因为 $[x^{\mathsf T},y^{\mathsf T}]^{\mathsf T}=-[x,y]$，所有非经典角在新坐标中取向均为 $-1$。这是对整个模型的坐标运输，不要求原 $D$ 转置协变。P2 和 PB 仅使用原实线性运算、Jordan 乘法和同一旧输出，因此逐值随这个同构运输。

在这个统一坐标中暂省略波浪，定义已知矩阵比较对象及未知缺陷

$$
K(x,y)=\frac i2[x,y],\qquad
F(x,y)=D(x,y)-K(x,y),\qquad
\mathfrak F(Z)=F(\operatorname{Re}Z,\operatorname{Im}Z),
\tag{137.3}
$$

其中 $Z\in\mathcal A=\bigoplus_jM_{n_j}(\mathbb C)$，$\operatorname{Re}Z=(Z+Z^*)/2$、$\operatorname{Im}Z=(Z-Z^*)/(2i)$。$K$ 是已知双线性比较映射，并非将旧 $D$ 改定义为 $K$；$F,\mathfrak F$ 不预付任何正则性。标准 $K$ 的 PB 是母卷 114.2 的结合矩阵见证，以下只把它用于相减。

## 138. 任意中央背景下的小连接幅由原条件支付

**引理 138.1（不增加假设的混合背景识别）。** 固定第 $j$ 块内的秩一投影 $p=ee^*$，$\|e\|=1$，并把其余块分量取零。记 $q=I_{n_j}-p$、$H(z)=ze^*+ez^*$。任意原 $a\in J$ 在本块写成

$$
a_j=\beta p+H(z)+B,\qquad z\in q\mathbb C^{n_j},\qquad B=qBq=B^*.
$$

只要 $\|z\|<2$，则对任意实 $\mu$，

$$
D(\mu p,a)_j=\mu H(-iz/2),\qquad
D(\mu p,a)_l=0\quad(l\ne j).
\tag{138.1}
$$

$\beta,B$、其他块输入和 $\mu$ 均无幅度限制。原取向坐标中对应公式为 $\mu H(i\varepsilon_jz/2)$。

证明。$\mu=0$ 由 P2 的零对角预算给出。设 $\mu\ne0$，记同一旧输出 $d=D(\mu p,a)$。对其他块 $l$ 的任一数学向量读取，首输入平方为零，129.1 使 $d_l$ 的全部向量二次值为零；固定 Hermitian 矩阵极化给 $d_l=0$。对第 $j$ 块 $q\mathbb C^{n_j}$ 的全部向量，同理给 $qd_jq=0$。所以

$$
d_j=\delta p+H(w),\qquad \delta\in\mathbb R,\quad w\in q\mathbb C^{n_j}.
\tag{138.2}
$$

这一步只定位输出，没有对未知输入和展开。定义仅支撑于第 $j$ 块的原元

$$
c_0=p\circ a=\beta p+\tfrac12H(z).
$$

在 (128.6) 中准确取演员 $a$、第二输入 $\mu p$、第三输入零。反对称性给 $v=-d$、$w_{\rm PB}=\mu c_0$，于是

$$
D(\mu p-d,\mu c_0)-D(\mu p+d,-\mu c_0)=2\mu p\circ d.
\tag{138.3}
$$

此时外层输入只支撑于第 $j$ 块，但尚不认定共同位于二级角。分别使用两份外层 P2，并除以 $|\mu|$，得到每个本块向量 $\xi$ 的

$$
2|\phi_\xi(p\circ d)|
\le\sqrt{\Delta_\xi(\mu p-d,c_0)}
   +\sqrt{\Delta_\xi(\mu p+d,c_0)}.
\tag{138.4}
$$

除法来自已知第二矩阵输入的向量 Gram 行列式缩放，不来自 $D$ 的齐次性。

令 $v$ 为 $w$ 在复正交补 $(\mathbb Cz)^\perp$ 中的分量；$z=0$ 时取 $v=w$。设 $\kappa=\langle w,v\rangle=\|v\|^2$，取 $\xi_s=e+sv$、$s\in\mathbb R$。则

$$
c_0\xi_s=\beta e+z/2,\qquad
(\mu p+\sigma d)\xi_s=A_\sigma(s)e+\sigma w,\qquad
A_\sigma(s)=\mu+\sigma\delta+\sigma s\kappa .
$$

记 $r=\operatorname{Re}\langle w,z\rangle$。两个已知矩阵的准确实 Gram 行列式为

$$
\Delta_{\xi_s}(\mu p+\sigma d,c_0)
=\frac{\|z\|^2}{4}A_\sigma(s)^2
 -\sigma\beta r A_\sigma(s)
 +\|w\|^2\left(\beta^2+\frac{\|z\|^2}{4}\right)-\frac{r^2}{4}.
\tag{138.5}
$$

因此它们的二次最高系数均为 $\kappa^2\|z\|^2/4$，而 (138.4) 左边为 $2|\delta+s\kappa|$。比较这些固定矩阵多项式的增长，得 $2\kappa\le\kappa\|z\|$。严格条件 $\|z\|<2$ 迫使 $\kappa=0$，即 $w\in\mathbb Cz$。$z=0$ 时同一计算使 $w=0$；(138.5) 这时为常数。这里没有对未知 $D$ 取极限。

现在 $p,d,c_0$ 才共同支撑于 $\operatorname{span}_{\mathbb C}\{e,z\}$ 的真实秩至多二角。对 (138.3) 的两个外层调用原样使用该角完整旧公式，得到

$$
2\mu p\circ d=2\mu^2K(p,c_0)=\mu^2H(-iz/2).
$$

而 $2\mu p\circ d=2\mu\delta p+\mu H(w)$。比较对角与连接分量，得 $\delta=0$、$w=-i\mu z/2$，即 (138.1)。秩一角直接使用其零公式；无需二级角存在。所有其他块背景始终保留在原演员 $a$ 中，未进入这两个外层输入。∎

## 139. 同一 PB 中减去已知标准关系

**引理 139.1（两个内层旧值已知时的精确缺陷运输）。** 若原 $t,x,y\in J$ 满足 $F(t,x)=F(t,y)=0$，且 $Z=x+iy$，则

$$
\mathfrak F((u+it)Z)=\mathfrak F((u-it)Z).
\tag{139.1}
$$

证明。原 PB 的两个增量准确为 $v=K(t,x)-t\circ y$、$w=t\circ x+K(t,y)$。对已知矩阵乘法展开得

$$
\operatorname{Re}((u\pm it)Z)=x\pm v,\qquad
\operatorname{Im}((u\pm it)Z)=y\pm w.
$$

标准 $K$ 满足同一 PB，因而

$$
\begin{aligned}
D(x+v,y+w)-D(x-v,y-w)&=-2x\circ v-2y\circ w,\\
K(x+v,y+w)-K(x-v,y-w)&=-2x\circ v-2y\circ w.
\end{aligned}
$$

相减即得 (139.1)。展开的只有已知比较映射 $K$；每个外层 $D$ 仍是其实际原值。∎

## 140. 大 Cayley 参数给出全部精确秩一相位

**引理 140.1（允许方向上的整圆不变性）。** 固定 $Z\in\mathcal A$ 与第 $j$ 块秩一 $p=ee^*$。若

$$
\|qZ_je\|<4,\qquad q=I_{n_j}-p,
\tag{140.1}
$$

则对每个实 $\theta$，原缺陷满足

$$
\mathfrak F(U_{\theta,p}Z)=\mathfrak F(Z),\qquad
U_{\theta,p}=u+(e^{i\theta}-1)p.
\tag{140.2}
$$

证明。对实 $t$ 置 $A_t=(u-itp)^{-1}$，本块为 $q+\alpha p$、$\alpha=(1-it)^{-1}$，其他块为单位。写 $Z_0=A_tZ=x_0+iy_0$，令 $v=qZ_je$、$w=qZ_j^*e$，则

$$
qx_{0,j}e=(v+\bar\alpha w)/2,\qquad
qy_{0,j}e=(v-\bar\alpha w)/(2i).
\tag{140.3}
$$

由 $\|v\|<4$，可选有限 $T>0$，使全部 $|t|>T$ 均有 $\|v\|+\|w\|/\sqrt{1+t^2}<4$。于是两连接范数都严格小于二。138.1 对演员 $tp$ 和这两个原输入分别给 $F(tp,x_0)=F(tp,y_0)=0$，无论其他块分量多大。139.1 因而给

$$
\begin{aligned}
\mathfrak F((u+itp)(u-itp)^{-1}Z)&=\mathfrak F(Z),\\
(u+itp)(u-itp)^{-1}&=U_{2\arctan t,p}.
\end{aligned}
\tag{140.4}
$$

负号一侧准确为 $(u-itp)Z_0=Z$。这里只送入 $D$ 各矩阵的原 Hermitian 实部和虚部。

还须支付所有相位，不能用稠密性代替未知缺陷的连续性。令 $\theta_0=2\arctan T<\pi$、$\delta=\pi-\theta_0>0$。已取得 (140.2) 的相位包括 $(\pi-\delta,\pi)$ 与 $(-\pi,-\pi+\delta)$。并且对任意已作用的 $W=U_{\theta,p}Z$，

$$
qW_je=qZ_je,\qquad qW_j^*e=e^{-i\theta}qZ_j^*e.
\tag{140.5}
$$

所以同一个 $T$ 适用于同一 $p$ 的整条相位轨道。给定 $0<\gamma<2\delta$，选 $a,b\in(0,\delta)$、$a+b=\gamma$。两个已允许相位 $\pi-a,\pi-b$ 之和模 $2\pi$ 恰为 $-\gamma$；逐次用 (140.4) 与 (140.5)，给 $-\gamma$ 的缺陷不变性。两个允许负相位 $-\pi+a,-\pi+b$ 同理给 $+\gamma$。零相位直接成立。任意实 $\theta$ 选正整数 $N$ 使 $|\theta/N|<2\delta$，再精确作用 $N$ 次这个短相位，即得 (140.2)。每次都使用同一实际旧映射、同一允许界和有限矩阵乘法。∎

## 141. 一片允许射影方向给出酉群邻域

**定理 141.1（缺陷在每点的酉邻域上不变）。** 令 $G=\prod_jU(n_j)$。对每个 $Z\in\mathcal A$，存在 $G$ 单位元的开邻域 $V_Z$，满足

$$
\mathfrak F(UZ)=\mathfrak F(Z)\qquad(U\in V_Z).
\tag{141.1}
$$

这包括任意非正规、不可对角化或奇异的 $Z$。

证明。在每个非空块，定义秩一投影的允许集

$$
\mathcal O_j(Z)=\{p=ee^*:\|e\|=1,\
       \|(I_{n_j}-p)Z_je\|<4\}.
\tag{141.2}
$$

任意有限复矩阵 $Z_j$ 都有复特征向量，故此集合非空。条件也可写成连续量 $\|(I_{n_j}-p)Z_jp\|<4$，所以它在 $\mathbb{CP}^{n_j-1}$ 中开。

这片开集实线性张成 $H_{n_j}(\mathbb C)$。确实，若 Hermitian $H$ 满足 $\operatorname{Tr}(Hp)=0$ 对这片开集成立，则 $e^*He$ 在其单位球面逆像上为零。乘以全部正实半径，得到 $\mathbb C^{n_j}\setminus\{0\}$ 的非空开锥；齐次实二次多项式 $z^*Hz$ 在该开锥为零，故恒为零。固定 Hermitian 二次型极化给 $H=0$。有限维实对偶性于是给张成结论，可选本块 $n_j^2$ 个允许投影构成实基。$n_j=1$ 时其唯一投影直接张成。

合并各块，得 $M=\sum_jn_j^2$ 个原投影 $p_1,\ldots,p_M$，它们是 $J$ 的实基。所有允许条件都是严格的，故存在 $Z$ 的矩阵邻域 $\mathcal N$，使这些固定投影对每个 $W\in\mathcal N$ 仍全部允许。考虑已知光滑群映射

$$
\Psi:\mathbb R^M\longrightarrow G,\qquad
\Psi(\theta)=U_{\theta_M,p_M}\cdots U_{\theta_1,p_1}.
\tag{141.3}
$$

其原点微分为 $\theta\mapsto i\sum_r\theta_rp_r$，是 $\mathbb R^M$ 到 $\mathfrak g=\bigoplus_j\mathfrak u(n_j)$ 的实线性同构。有限维逆函数定理因此给 $G$ 中的单位元邻域。这个成熟有限乘积坐标方法在母卷 92.2 已用于已知旋转群；这里应用于已知矩阵酉群。

缩小参数邻域，使每个有限前缀乘积 $U_{\theta_r,p_r}\cdots U_{\theta_1,p_1}Z$ 都留在 $\mathcal N$。这由有限个已知连续矩阵乘法在原点的值都是 $Z$ 得到。140.1 遂可逐步实际应用，给 $\mathfrak F(\Psi(\theta)Z)=\mathfrak F(Z)$。取这个参数邻域在 $\Psi$ 下的单位元开像，即得 (141.1)。逆函数定理施于 $\Psi$，从未施于 $\theta\mapsto\Psi(\theta)Z$，所以无需 $Z$ 可逆。所有光滑性均属于已知矩阵群，不属于旧 $D$。∎

## 142. 极分解把整个旧关系送回零输入

**定理 142.1（任意有限复直和的旧关系自动识别）。** 在 137.1 的同一原 P2、完整 PB 与已付角取向下，任意给定旧 $D$ 必须满足

$$
\boxed{\quad
D(a,b)_j=\varepsilon_j\frac{[a_j,b_j]}{2i}
\quad(a,b\in J).\quad}
\tag{142.1}
$$

经典块输出为零，非经典块符号由原二级角确定。任意混合中央块输入也适用，不预付逐块独立性。

证明。先在统一取向坐标中固定任意 $Z$，定义集合值无正则性要求的函数

$$
g_Z:G\longrightarrow J,\qquad g_Z(U)=\mathfrak F(UZ).
$$

任意 $U_0\in G$ 处，141.1 对 $W=U_0Z$ 给一个单位元邻域 $V_W$，使

$$
g_Z(VU_0)=g_Z(U_0)\qquad(V\in V_W).
\tag{142.2}
$$

因此 $g_Z$ 处处局部常值，邻域是左乘后的 $V_WU_0$。有限酉群连通：谱定理写每个 $U_j=V_j\operatorname{diag}(e^{i\theta_{j,r}})V_j^*$，将所有角同时乘 $s\in[0,1]$ 就给单位元到 $U$ 的路径。局部常值函数的每个纤维及其补集均开；连通性故使 $g_Z$ 常值。此处没有假定 $g_Z$ 或旧 $D$ 连续。

对各块取有限矩阵极分解 $Z_j=V_jP_j$、$P_j\ge0$。即使奇异，奇异值分解 $Z_j=A_j\Sigma_jB_j^*$ 也直接给酉因子 $V_j=A_jB_j^*$ 和 $P_j=B_j\Sigma_jB_j^*$。于是

$$
\mathfrak F(Z)=\mathfrak F(P)
=D(P,0)-K(P,0)=0.
\tag{142.3}
$$

最后一个零值来自原 P2。任取 $Z=a+ib$，得到统一坐标中的同一旧 $D(a,b)=K(a,b)$，并非只构造了一个正确 $K$。恢复 137.2 的逐块转置坐标即得 (142.1)。其他块背景已经在 138.1 中保留，在 140–141 中由乘积群处理，所以逐块独立性也是结论。空直和为唯一零映射；经典块对应 $U(1)$，同一论证适用。∎

## 143. 有限原 JB 完成的完整旧关系分类

**定理 143.1（有限完成时分别可加与原量子恒等式成为结论）。** 在 128.1 的完整原背景、P2 和 PB 下，若同一 JB 完成 $X$ 有限维，则 $E=X$，存在保单位 Jordan 识别

$$
E\cong_J\bigoplus_{j=1}^kH_{n_j}(\mathbb C),
$$

且任意给定旧 $D$ 在此识别中准确为 (142.1)。因此该旧 $D$ 分别实双线性，有限谱相加和混合中央块独立性全部成立，原 (128.5) 对所有原输入成立。由原公式定义的 $\star=\circ-iD$ 延拓到 $E+iE$ 后，是各块通常或相反的结合复矩阵乘法；全部原有限有向 Gram 表为半正定。

证明。有限维闭性与原稠密性给 $E=X$。直接消费母卷 122.1 的无 NN、无 Jacobi 的有限底层必要分类，取得上述原 Jordan 识别。每个中央投影和秩二投影都在原域；119.2–119.3、121.1 与 114.1 的接口按 128.2 原样可用，131.1–131.2 给各块共同角取向。故 138–142 对同一个原 $D$ 全部适用，不再留下高秩、谱和或中央拼接假设。

比较 (142.1) 的矩阵交换子立刻给原双线性及全部实际谱和等式。若 $\varepsilon_j=-1$，则 $a_j\star b_j=a_jb_j$；若 $\varepsilon_j=+1$，则 $a_j\star b_j=b_ja_j$。这两种乘法都结合，实部的结合律准确为 (128.5)。平方及正锥与原 Jordan 平方及正锥一致。对任意有限原 $a_1,\ldots,a_m$、复数 $\lambda_i$ 和原 $\alpha$，置 $Z=\sum_i\lambda_i a_i$，则

$$
\sum_{r,s}\bar\lambda_r\lambda_s
\bigl(\alpha(a_r\circ a_s)-i\alpha D(a_r,a_s)\bigr)
=\alpha_{\mathbb C}(Z^*\star Z)\ge0.
\tag{143.1}
$$

这里 $\alpha_{\mathbb C}$ 是同一原实线性评价的复线性延拓；$Z^*\star Z$ 是原正锥中的 Hermitian 元。通常块为 $Z_j^*Z_j$，相反块为 $Z_jZ_j^*$，所以不等式直接由原正性成立，包括原质量零。故全部有限 Gram 正性成为结论，不是前件。标准交换子的 NN 与 Jacobi 同样是矩阵恒等式的消费者。

此外，一般可不完备原 $E\subset X$ 若实际含有幂等元 $k$，且 $X_2(k)$ 有限维，则同一结论适用于同一个 $D|_{E_k^2}$：119.3 先给 $E_k=X_2(k)$ 及全部原限制评价，121.1 使完整 PB 遗传，随后应用本定理。不向原 $D$ 输入完成中新借的投影，也不将有限角识别扩张为任意原输入识别。∎

## 144. 更简洁的几何与量子公理对应

**定义 144.1（从二元约束到整条酉轨道）。** 在有限背景中，完整候选仍只是同一原 P2 与 PB，配以 128.1 已给的实 Jordan 接口。二级角选择共同取向之后，138.1 将任意大的背景压回小连接的标准旧值；140.1 把这份旧值识别送到整圆相位；一个复特征向量附近的射影开集提供整组矩阵生成元；141.1 与连通性使同一个残差沿整条酉轨道不变；极分解把它送到已知零输入。这个几何不再要求额外输入旧值加法、齐次、连续、有限谱传播或中央块独立性。严格阈值二与四只是证明中取得开集的界，不增加尺度公理。

这里的 Cayley 恒等式、实多项式开集唯一性、有限维逆函数定理、酉谱定理、连通性与矩阵极分解均为成熟工具。母卷 92.2 已有有限群乘积坐标的同类用途；Alfsen–Shultz 的动力对应及其线性前件边界仍按 135.1 的原始出处保留。本增补的 $\texttt{repo-derived}$ 综合是从原二元条件支付 138.1，并将同一旧输出依次送入 139–142；不是将成熟极分解或 Lie 群坐标另列为新量子定理，不宣称文献穷尽或历史原创优先权。

**定义 144.2（有限量子运动学与数学动力学消费者）。** 143.1 使同一个旧 $\star$ 成为完整有限复矩阵代数的乘法，因此标准复 Hilbert 空间表示、正元、投影及效果空间有准确代数对应。原评价的正密度矩阵表示仍直接消费母卷 124.1；只有原来源实际供应完整菜单且质量正，才取得那里给出的归一 Born 概率。原质量零保持零，实际准备与实际菜单的供应不由数学表示产生。

对一个原 Hermitian 元 $a$，旧行 $D_a(b)=D(a,b)$ 现在确是已证明的实线性 Jordan 导子。在所选矩阵坐标中，其数学一参数群为

$$
\begin{aligned}
e^{sD_a}b\big|_j
&=U_{j,s}b_jU_{j,s}^*,\\
U_{j,s}&=\exp\!\left(\frac{\varepsilon_js\,a_j}{2i}\right).
\end{aligned}
\tag{144.1}
$$

对已知矩阵指数求导即给 $D_a$，保单位、正锥和谱。参数 $s$ 在这里是数学参数；与原物理时钟、能量及共同 $\hbar$ 的识别仍须原来源桥梁。有限 Gram 正性和幺正数学运动已由原关系恢复，不额外许诺实际可制备性、全仪器更新、共同张量、实际相关联合或物理动力尺度。

## 145. 有限缺口的闭合范围与一般原目标

**定义 145.1（旧未证式的准确适用更新）。** 在 143.1 的有限原完成或其明确的实际有限角范围内，135.1 的混合背景消去、135.2 的有限谱相加、同一有限直和的中央混合独立性及原 (128.5) 全部由 142–143 给出。不需要先建立一般的倍增函数方程，也不从小幅公式未经证明地缩放到大幅。135.3 所保留的一般不完备原域义务仍不因此消失。

一般原 $E$ 的任意输入不保证落入一个实际有限矩阵角；允许投影开集及有限维酉群坐标也未对任意 JB 完成建立。故一般原分别可加、原 $R$、全部合法来源与历史消费者继续保持 128.1 的原量词。无限 CountRead、正常性和前对偶、实际准备、全仪器与环境及全部输出、共同记录与真正分组遗忘、实际相关联合与递归同源参考、全部合法顺序／自适应／并行历史及每个仍合法未来、停止／拒绝／销毁、同数两侧与真实逆向返回，以及物理钟、能量和共同 $\hbar$，均不由一次数学极分解供应。

## 146. 任意高秩关系怎样被送回零输入

**定义 146.1（完整白话）。** 候选仍是同一张二元有向关系：每对对象的正表必须成立，同一评价读到的正反平方必须配平。前面的三维三角已经让一个有限复矩阵块里的全部二维窗口共同定向，但高秩背景还能否改变旧输出仍须证明。现在先固定一条射线：正表把输出压成这条射线上的一项加一条连接向量，配平又让两份真实外层返回共同受限。把数学读取沿可能多出的连接方向放大，两个正表的最高增长便不允许这条多余方向存在；只要原连接足够小，无论背景多大，旧输出都被锁回真实二维角。接着不再硬把未知关系拆成许多小输入，而是把任意两个 Hermitian 输入合成一个复矩阵。Cayley 变换把已经确定的内层返回变成整圆相位上的残差不变。任意有限复矩阵总有一条特征射线，其附近一片射线都可使用；这片方向足以组成整个酉群的局部坐标，所以残差在每个酉位置附近都不变。酉群连通，这些局部关系就连成整个轨道。最后，极分解能把任意复矩阵沿这条轨道送成正矩阵，也就是第二输入为零的情形；原正表早已规定它没有残差。因此同一个给定旧关系在全部有限高秩输入上只能是共同取向的交换子，实加法、全部有限正表、原量子恒等式和数学幺正运动一起成为结论。不同中央块可以保留各自方向，混合背景也不能新增影响。一般不完备或无限原域还须建立自己的投影与传播桥梁，真实仪器、无限记录、合法未来返回和物理时钟仍由原来源承担。

## 追加锚（本行以下为增补区）
