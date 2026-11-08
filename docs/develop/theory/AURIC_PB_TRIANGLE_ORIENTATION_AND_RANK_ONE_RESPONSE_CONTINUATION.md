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
