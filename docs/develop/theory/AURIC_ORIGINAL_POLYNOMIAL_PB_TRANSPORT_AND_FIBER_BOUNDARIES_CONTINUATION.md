# AURIC 原多项式 PB 输运与纤维边界续卷

**定义 96.0（同一原域的续卷接口）。** 本卷承接[《原多项式零响应与 Cayley 原域边界》](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的同一原对象、全部原评价与来源量词。以下96–102在同一个原域中定义全部实际演员的端点图、有限路径分量及其原标签纤维边界；外卷条目均由其所属卷链接指定。

## 96. 全部实际演员的 PB 端点图

**定义 96.1（同一标量零点原域与标准旧值）。** 固定[原多项式卷8.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的 $n=3$ 分支，写

$$
\begin{gathered}
B=\{F\in C([0,1],M_3(\mathbb C)):F(0)\in\mathbb CI\},\qquad
A_0=\{P\in M_3(\mathbb C[t]):P(0)\in\mathbb CI\},\\
X=B_{\rm sa},\qquad E=(A_0)_{\rm sa},\qquad
u=I,\quad C=E\cap B_+,\quad N=\|\cdot\|_B|_E,\\
a\circ b=(ab+ba)/2,\qquad D_*(a,b)=i[a,b]/2,\qquad
\pi=\operatorname{ev}_1:X\longrightarrow H_3(\mathbb C).
\end{gathered}
\tag{96.1}
$$

多项式在区间上的限制与其唯一系数表示相识别。$A_0=E+iE$，且
$\operatorname{Re}Z=(Z+Z^*)/2$、$\operatorname{Im}Z=(Z-Z^*)/(2i)$
均指伴随实部、虚部，不是逐矩阵元取实虚部。$\pi$ 也记其在 $B,A_0$ 上的
复线性求值映射。$E$ 的原评价沿用[原多项式卷8.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)：$B$ 上全部数学正泛函的限制，
保留全部非负质量，包括零、不等与次归一质量，不把这些数学读取视为实际准备。

[原多项式卷8.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)及[静态重构卷](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)
35.1–35.2的 $\mathcal A=B,\mathcal A_0=A_0,\kappa=1$ 直接供应全部原静态
A1–A3、全部原P2、全部有限有向复Gram正性与完整原PB。原有理小窗口不变。
这是同一个已给标准模型的应用；不另构造响应表，也不把已知双线性 $D_*$
当作一般候选中未知旧 $D$ 的免费性质。原域仍含任意有限次数并且不完备。

**定义 96.2（无演员限制的实际端点图）。** 图 $\mathcal H$ 的顶点为全部
$E^2$，用双射 $(a,b)\leftrightarrow a+ib\in A_0$ 同时记顶点。对每个实际
$r,x,y\in E$，以同一份实际内值定义

$$
\begin{aligned}
\nu_r&=D_*(r,x)-r\circ y,&
\omega_r&=r\circ x+D_*(r,y),\\
P_\pm&=x\pm\nu_r,&Q_\pm&=y\pm\omega_r.
\end{aligned}
\tag{96.2}
$$

在 $(P_+,Q_+)$ 与 $(P_-,Q_-)$ 间放无向边；可有环及不同演员表示的重边。
不要求 $r$ 交换 $x,y$，不要求 $x,y$ 交换，不限制演员或输入的次数、范数、
共同生成代数及内值是否为零。每步可换任意实际演员和输入。连通只指任意长
有限路径，包含长度零，不取无限路径、路径极限或完成中的闭包。

**命题 96.3（每份实际调用的准确复标签与读数）。** 令 $W=x+iy$。对96.2
的每份表示、两个符号以及每个原正读取 $\phi$，有

$$
\begin{aligned}
T_\pm:=P_\pm+iQ_\pm&=(I\pm ir)W,\\
Q_\phi(P_\pm,Q_\pm)
&:=\phi\bigl(P_\pm^2+Q_\pm^2+2D_*(P_\pm,Q_\pm)\bigr)\\
&=\phi_{\mathbb C}\bigl(W^*(I+r^2)W\bigr).
\end{aligned}
\tag{96.3}
$$

这里 $\phi_{\mathbb C}$ 是原评价的复延拓。全部内值、端点和外层输出都在
原 $E$；两侧相等正是[配平主卷128.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)的完整有向PB，不是另选端点的比较。
其同一实际元素差为

$$
D_*(P_+,Q_+)-D_*(P_-,Q_-)
=-2x\circ\nu_r-2y\circ\omega_r.
\tag{96.4}
$$

证明。只展开已经给定的矩阵乘法，有

$$
\begin{aligned}
\nu_r+i\omega_r
&=\tfrac i2(rx-xr)-\tfrac12(ry+yr)
 +\tfrac i2(rx+xr)-\tfrac12(ry-yr)\\
&=irx-ry=irW.
\end{aligned}
$$

故端点恰为96.3所写实际标签。对任意原自伴 $P,Q$，
$P^2+Q^2+2D_*(P,Q)=(P+iQ)^*(P+iQ)$。
$r=r^*$ 使两个端点平方均为 $W^*(I+r^2)W$，给全部读取、全部质量及两个
符号的PB。对这同一恒等式展开已知Jordan平方，再用原评价分离性，给96.4；
外层值仍准确为 $i[P_\pm,Q_\pm]/2$。未对未知响应作分配展开。∎

## 97. 多项式单位种子的整个全演员分量

**定理 97.1（全部相邻表示的标量刚性与整分量）。** 取任意 $Z\in A_0$，
要求 $\det Z$ 是非零常数多项式。则每条与 $Z$ 相接边的每一种96.2表示，
其演员均为 $r=cI$，其中 $c\in\mathbb R$ 是常数。并且

$$
\boxed{\operatorname{Comp}_{\mathcal H}(Z)
=\{\zeta Z:\zeta\in\mathbb C,\ |\zeta|=1\}.}
\tag{97.1}
$$

这包括每步任换演员、任意中间原顶点和所有有限路径长度。除 $\zeta=-1$
外每个相位可由一条边实现；$-1$ 可由两条四分之一转边实现。

证明。先固定任意相接边及其任意一份表示，不假定表示唯一。对某个
$\varepsilon\in\{1,-1\}$，96.3给多项式恒等式

$$
Z=(I+\varepsilon ir)W,\qquad
\det Z=\det(I+\varepsilon ir)\det W\ne0.
\tag{97.2}
$$

即使起初只在 $[0,1]$ 上相等，每个矩阵元的多项式恒等原理也给同一系数
等式。$\mathbb C[t]$ 中两个多项式乘积为非零常数，故两因子各为非零常数。
写 $\det(I+\varepsilon ir)=d\ne0$。

$r\in E$ 的每个系数Hermitian，所以对每个实数 $s$，$r(s)$ 都是Hermitian
矩阵。其三个实特征值记为 $\lambda_j(s)$，于是

$$
\prod_{j=1}^3(1+\lambda_j(s)^2)
=|\det(I+\varepsilon ir(s))|^2=|d|^2=:K,
\qquad 1+\lambda_j(s)^2\le K.
\tag{97.3}
$$

有限维谱定理给 $\|r(s)\|\le\sqrt{K-1}$，在整条实轴上统一成立。
$r$ 每个矩阵元的实部、虚部都是有界实多项式，故均为常数。再用实际原域
条件 $r(0)\in\mathbb RI$，得到 $r=cI$。这是任意相邻边、任一端点及每份
表示的结论。区间外的 $s$ 只用来证明多项式系数恒等式与有界性；没有增加
$[0,1]$ 外的原评价、实际输入或 $D_*$ 调用。

因此97.2的另一端准确为

$$
T_{-\varepsilon}
=\frac{1-\varepsilon ic}{1+\varepsilon ic}Z,
\qquad
\left|\frac{1-\varepsilon ic}{1+\varepsilon ic}\right|=1.
\tag{97.4}
$$

每个 $\zeta Z$ 的行列式仍为非零常数，所以刚证相邻表示结论可在下一步
重新应用。对路径长度归纳，所有有限可达顶点都在97.1右侧；无需各步演员
相同，也无需预选边的表示。

反向，给 $\zeta=\alpha+i\beta$、$\alpha^2+\beta^2=1$。
若 $\alpha\ne-1$，置

$$
c=\frac{\beta}{1+\alpha},\qquad
r=cI,\qquad W=(1-ic)^{-1}Z,\qquad
x=\operatorname{Re}W,\ y=\operatorname{Im}W.
\tag{97.5}
$$

所有除法均为非零复标量除法，故 $W\in A_0$、$r,x,y\in E$。
96.3给负端点 $Z$ 与正端点 $\zeta Z$，因为
$(1+ic)/(1-ic)=\zeta$。$\zeta=-1$ 时，两次取 $c=1$，依次从 $Z$ 到
$iZ$、再到 $-Z$。$\zeta=1$ 可取零长度路径，或 $r=0$ 的环。
两包含均已证明。∎

**命题 97.2（逐点可逆不能供应这类原端点）。** 任取非零实 $\mu$ 和
秩一投影 $p$，实际演员 $r=t\mu p$ 给出逐点可逆的原端点 $I-ir$，
但这份相邻表示的演员不是常数标量。对每个满足97.1单位条件的 $Z$，
环境逆所给 $(I-ir)^{-1}Z$ 均不属于 $A_0$。所以逐点可逆性既不能替代
97.1的演员刚性前件，也不能供应其原域内的回溯输入。

证明。先用成熟的伴随矩阵公式：当 $\det Z$ 为非零常数时，
$Z^{-1}=\operatorname{adj}(Z)/\det Z$ 为矩阵多项式。
$Z(0)=\lambda I$ 且 $\lambda^3=\det Z\ne0$，故其逆在零点也是标量，属于
$A_0$。反向，对 $A_0$ 内的逆取行列式，两多项式乘积为一，故行列式为
非零常数。这解释了97.1所用的是多项式单位，而不是仅有环境逆。
现在取实际 $r=t\mu p,x=I,y=0$；96.3的两端正是 $I\pm ir$。
它们在每个实 $t\in[0,1]$ 可逆，演员却非标量常数，且
$\det(I-ir)=1-i\mu t$。其 $B$ 内的逆为

$$
(I-i\mu tp)^{-1}=I-p+(1-i\mu t)^{-1}p\notin A_0.
\tag{97.6}
$$

若该逆为多项式，沿 $p$ 的矩阵系数将给多项式 $f$ 满足
$(1-i\mu t)f(t)=1$，与次数相矛盾。若对多项式单位 $Z$ 有
$(I-ir)^{-1}Z\in A_0$，再右乘刚证属于 $A_0$ 的 $Z^{-1}$，又会使
$(I-ir)^{-1}\in A_0$，同样矛盾。这在同一实际调用中区分了环境逆元
与原回溯输入。∎

## 98. 非零响应种子与全部秩一像演员的排除

**命题 98.1（没有零响应顶点的完整分量）。** 记常数矩阵单位为 $E_{jk}$，取

$$
\begin{aligned}
Z_0&=I+tE_{12},\qquad \det Z_0=1,\\
a&=\operatorname{Re}Z_0=I+\tfrac t2(E_{12}+E_{21}),\qquad
b=\operatorname{Im}Z_0=\tfrac{t}{2i}(E_{12}-E_{21}).
\end{aligned}
\tag{98.1}
$$

则 $a,b\in E$，且整个97.1分量中的实际响应恒为

$$
D_*(a,b)=-\tfrac{t^2}{4}(E_{11}-E_{22})\ne0.
\tag{98.2}
$$

对每个秩一投影 $p\in M_3(\mathbb C)$、每个非零实 $\mu$，全部满足
$\pi r=\mu p$ 的实际 $r\in E$ 都不能出现在该分量任一相接边的任一表示中。
这样的实际演员存在，例如 $r(t)=t\mu p$，故排除不是空量词。

证明。$E_{12}^2=0$，故 $Z_0^{-1}=I-tE_{12}\in A_0$，行列式为一。
对98.1的两个伴随部分直接相乘给98.2。若 $\zeta=\alpha+i\beta$、
$|\zeta|=1$，对应原对为

$$
(a_\zeta,b_\zeta)=(\alpha a-\beta b,\ \beta a+\alpha b).
\tag{98.3}
$$

在这个已知标准响应内，双线性与反对称性给
$D_*(a_\zeta,b_\zeta)=(\alpha^2+\beta^2)D_*(a,b)=D_*(a,b)$。
97.1分类全部顶点，所以分量没有零响应顶点。又97.1在每个分量顶点的
全部相邻表示中迫使 $r=cI$，其商像为 $cI$，不可能等于非零秩一矩阵
$\mu p$。演员 $t\mu p$ 则Hermitian且零点为零，确实属于原域。∎

**命题 98.2（同像原标签可以有不同端点分量）。** $Z_0=I+tE_{12}$ 与
$Z_1=I+t^2E_{12}$ 具有相同商像，属于不同的 $\mathcal H$ 分量，而其
实际响应的商像相等。

证明。两者行列式均为一。若 $Z_1=\zeta Z_0$，零点读取迫使 $\zeta=1$，
再比较一次与二次系数得矛盾；97.1因此分开两分量。另一方面
$\pi Z_0=\pi Z_1=I+E_{12}$，两个原响应分别为
$-t^2(E_{11}-E_{22})/4$ 与 $-t^4(E_{11}-E_{22})/4$，求值于一后相等。
因此端点分量比响应读数更细；这个例子不反驳同像响应不变性。∎

## 99. 全代表小连接行与同一原目标回溯的准确对应

**定理 99.1（全部秩一方向及全部实际提升的小窗）。** 固定98.1的原目标
$(a,b)$，写 $T=\pi Z_0=I+E_{12}$、$A=\pi a$、$B_1=\pi b$。
对每个秩一投影 $p=ee^*$、$\|e\|=1$，令 $q=I-p$。则

$$
\|qAe\|\le\tfrac12,\qquad \|qB_1e\|\le\tfrac12.
\tag{99.1}
$$

对每个实 $0<|\mu|<1/4$，置

$$
W_\mu=(I-i\mu p)^{-1}T.
\tag{99.2}
$$

其伴随实、虚部两条连接均严格小于一，因而严格小于[原多项式卷83.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)所需阈值二。
对每份实际提升

$$
r,x,y\in E,\qquad
\pi r=\mu p,\quad \pi x=\operatorname{Re}W_\mu,
\quad \pi y=\operatorname{Im}W_\mu,
\tag{99.3}
$$

[原多项式卷83.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)都支付两份实际内行的商像，符号为本标准取向 $\sigma=1$：

$$
\begin{aligned}
\pi D_*(r,x)&=\tfrac{i\mu}{2}[p,\operatorname{Re}W_\mu],\\
\pi D_*(r,y)&=\tfrac{i\mu}{2}[p,\operatorname{Im}W_\mu].
\end{aligned}
\tag{99.4}
$$

96.2中这份实际调用的负端点满足

$$
\pi(P_-+iQ_-)=T,
\qquad (P_-,Q_-)\ne(a,b).
\tag{99.5}
$$

不等式对99.3的每个实际提升都成立。

证明。写 $A=I+H$、$B_1=J$，其中
$H=(E_{12}+E_{21})/2$、$J=(E_{12}-E_{21})/(2i)$，二者算子范数均为
$1/2$。$qIe=0$，立即给99.1。又 $\|T\|\le2$，且已知矩阵逆满足

$$
\begin{aligned}
(I-i\mu p)^{-1}&=q+(1-i\mu)^{-1}p,\\
\|W_\mu-T\|
&\le\frac{|\mu|}{\sqrt{1+\mu^2}}\|T\|
\le2|\mu|<\tfrac12.
\end{aligned}
\tag{99.6}
$$

伴随实部、虚部均为范数收缩，故

$$
\begin{aligned}
\|q(\operatorname{Re}W_\mu)e\|
&\le\|qAe\|+\|\operatorname{Re}(W_\mu-T)\|<1,\\
\|q(\operatorname{Im}W_\mu)e\|
&\le\|qB_1e\|+\|\operatorname{Im}(W_\mu-T)\|<1.
\end{aligned}
\tag{99.7}
$$

这是同时对所有 $p$ 的同一参数窗，不依赖任何原提升的范数或次数。
按[原多项式卷83.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)把任一自伴矩阵写成 $\beta p+H(z)+qBq$ 时，连接正是 $z=qMe$。
99.7于是逐个支付99.3的两份实际调用；[原多项式卷83.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的表达与99.4相同。提升确实
存在，可取 $r=t\mu p$、$x=t\operatorname{Re}W_\mu$、
$y=t\operatorname{Im}W_\mu$，但结论没有限制在这个截面。

对任意提升令 $U=x+iy\in A_0$。原PB先在 $E$ 调用，96.3随后给

$$
\begin{aligned}
T_-^{\rm orig}&=(I-ir)U,&\pi T_-^{\rm orig}&=(I-i\mu p)W_\mu=T,\\
T_+^{\rm orig}&=(I+ir)U,&\pi T_+^{\rm orig}&=U_{\mu,p}T,\\
U_{\mu,p}&=(I+i\mu p)(I-i\mu p)^{-1}
=q+\frac{1+i\mu}{1-i\mu}p.
\end{aligned}
\tag{99.8}
$$

若 $T_-^{\rm orig}=Z_0$，这就是与 $Z_0$ 相接的一份96.2表示。
97.1迫使 $r=cI$，与 $\pi r=\mu p$ 矛盾，故99.5对所有提升成立。
同理，$U_{\mu,p}T$ 不在 $\pi(\operatorname{Comp}_{\mathcal H}(Z_0))$：
否则它等于某个 $\zeta T$；$T$ 可逆，使 $U_{\mu,p}=\zeta I$，而其在
$q$ 与 $p$ 上的两个相位不同。故任意有限端点链也不能从原目标到达具有
这个秩一相位商像的原顶点。∎

**命题 99.2（未返回原标签不等于未认回响应）。** 在96.1这个合法完整
标准模型中，[原多项式卷85.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的全域公式与[原多项式卷85.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的响应等式均成立；99.5只否定把它们
普遍供应为原标签精确回溯或任意有限端点链的那一种方法。

证明。$\pi$ 为已给乘法的星同态，故对全部原 $v,w\in E$，

$$
\pi D_*(v,w)=\tfrac i2[\pi v,\pi w].
\tag{99.9}
$$

这是已知标准值的公式，不是为一般未知 $D$ 预付的商下降。
99.8于是准确给

$$
\pi D_*(P_-,Q_-)=\tfrac i2[A,B_1]=\pi D_*(a,b),
\qquad (P_-,Q_-)\ne(a,b).
\tag{99.10}
$$

所以[原多项式卷83.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的全部代表内行、完整PB及[原多项式卷85.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)响应相等在这里同时为真，精确原
端点供应仍失败。98.1又说明把任意有限链送到零响应顶点的普遍供应失败。
它们不构成满足P2/PB却否定[原多项式卷85.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)、响应重构或一般双线性的反模型。∎

## 100. 同一原域上的投影、逆元与序零截面比较

**命题 100.1（数学截面不供应原投影框架或逆闭合）。** 在96.1的同一
$B,A_0,X,E,\pi$ 中，商中的非平凡投影不能提升为 $X$ 中的投影，
因此也不能提升为原 $E$ 中的投影；不存在[中央响应平方续卷173–181](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)所需
非平凡实际单位平方正交三轴。然而有一个值域落在 $A_0$ 的c.p.c.序零截面

$$
\theta:M_3(\mathbb C)\longrightarrow B,\qquad
\theta(M)(t)=tM,\qquad \pi\theta=\operatorname{id}.
\tag{100.1}
$$

这个截面、原域稠密性和环境中的函数演算均不等于原逆闭合或未知旧响应
的相容性前件。

证明。连续矩阵投影的秩是局部常数，在连通 $[0,1]$ 上恒定；其零点是
标量投影，只能为零或 $I$。秩恒定迫使投影在全部区间分别为零或 $I$。
故非平凡商投影甚至没有完成 $X$ 内的投影提升。若实际自伴 $h$ 满足
$h^2=I$，则 $(I+h)/2$ 是这样的投影，故 $h=\pm I$；两条此类轴的Jordan
乘积不为零。因而[中央响应平方续卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)
173.1的实际 $h,e,j$ 前件在这里不成立，不能只凭商矩阵中的轴移入该分支。

100.1的映射本来复线性，每个矩阵放大在点 $t$ 都是乘以非负标量 $t$，
所以完全正且压缩。若 $M,N\ge0$ 且 $MN=0$，则
$\theta(M)\theta(N)(t)=t^2MN=0$，故序零；其零点为零且为多项式，值域
确在 $A_0$。但 $\theta(I)=tI$ 不是投影，$\theta$ 不是星同态。
对自伴 $M,N$ 更有准确原值比较

$$
D_*(\theta(M),\theta(N))(t)=t^2\tfrac i2[M,N],\qquad
\theta\bigl(\tfrac i2[M,N]\bigr)(t)=t\tfrac i2[M,N].
\tag{100.2}
$$

非交换时二者在原域不相等，虽商像相同。这只比较这个给定截面，未以此
否定别的响应证明。

这里可用的成熟序零结构定理是Winter–Zacharias，
[*Completely positive maps of order zero*](https://www.uni-muenster.de/FB10/mjm/vol_2/mjm_vol_2_14.pdf)，
Münster J. Math. **2** (2009), 311–324，Theorem3.3（印刷页317起）及
Corollary4.1（印刷页319–320）；其[预印本](https://arxiv.org/html/0903.3290v1)
相应编号为2.3与3.1。定理的两端必须是C*代数，且映射已是线性完全正
序零映射；它不从二元原表或未知 $D$ 产生这些前件。故100.1的正确C*值域
是 $B$，不能把不完备 $A_0$ 写成该定理的C*值域。

在此应用中 $C^*(\theta(M_3))$ 是锥理想

$$
J=\{F\in B:F(0)=0\}\cong C_0((0,1])\otimes M_3(\mathbb C).
\tag{100.3}
$$

确实，$tM$ 与 $tI$ 的乘积生成各 $t^kM$，零点消失的标量多项式一致
逼近给整个 $J$。结构定理的 $h=\theta(I)=tI$，支持同态
$\rho_\theta:M_3\to M(J)$ 在 $t>0$ 为 $\rho_\theta(M)(t)=M$；
$h\rho_\theta(M)=\theta(M)$。非标量 $M$ 的这份常值乘子没有零点标量
延拓，因而不在 $B$ 或 $A_0$。该定理只保证乘子代数中的同态，不保证
实际原投影或三轴。Corollary4.1的锥同态在这里是 $J$ 到 $B$ 的包含，
同样没有把支持同态的非标量常值提升变成 $B$ 元素。

逆元方面，97.6已经在同一原域给出可逆环境元素而无原逆元。稠密性不能
删除这个区别。Schweitzer的[funct-an/9211009v2](https://arxiv.org/html/funct-an/9211009v2)
Definitions1.1–1.2定义的是连续嵌入的稠密Fréchet子代数及强谱不变性，
其Definition1.2在Banach环境中要求给定子代数拓扑的半范数和乘积估计

$$
\exists C_0>0\ \forall m\ \exists D_m>0\ \exists p_m\ge m\quad
\forall n\ \forall a_1,\ldots,a_n:\quad
\|a_1\cdots a_n\|_m
\le D_m C_0^n\!\sum_{k_1+\cdots+k_n\le p_m}
\|a_1\|_{k_1}\cdots\|a_n\|_{k_n}.
\tag{100.4}
$$

其中 $m,k_j,p_m\in\mathbb N_0$、$n\ge1$ 为整数，$a_j$ 属于该Fréchet
子代数，零号范数给环境Banach拓扑。其Theorem1.17由这些前件推出谱不变性，
环境为Banach已足够，不必限定为C*。这里没有给 $A_0$ 供应这样的完整
Fréchet结构和估计；单有范数稠密、Jordan闭合、c.p.c.序零截面或原PB
都不是引用该定理的同一组前件。即使另有合法谱不变子代数，仍须逐值证明
它与同一个未知旧 $D$ 的关系，不能把环境函数演算当作原 $D$ 的延拓。∎

## 101. 全演员结论与既有原像接线的范围

**定义 101.1（新增承重关系与成熟中间输入）。** 97.1的全部实际演员、
全部相邻边表示与全部有限路径的多项式单位分量分类，98.1的非零响应分量，
以及99.1–99.2对[原多项式卷83.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)和[原多项式卷85.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的全代表接线，归为 $\texttt{repo-derived}$
的纸面应用。标准模型、行列式乘法、多项式环的单位、Hermitian谱定理、
有界实多项式恒定及标量Cayley半角公式只作中间工具，不各立为新发现。
100.1的投影与序零比较只为这个同一原域澄清可用供应；所引Schweitzer与
Winter–Zacharias结论按100.1的原文前件使用，不作新独立定理。
不主张历史优先权、穷尽文献或独立公理数减少。

[原多项式卷8.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的图要求演员同时交换两标签，在标准响应中只用零内行；[原多项式卷9.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的种子是
零点消失且 $A^2+B^2>0$ 的线性对。96.2包含该通勤图的全部边，但没有
保留其演员限制；98.1的种子零点为 $I$、行列式为一，亦不是[原多项式卷9.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)种子。
所以97.1不由把旧通勤分量改名而得。其关键新接线是：不消去任何实际
内值，先用96.3把任意相邻表示转成左因子，再由97.2的多项式单位条件
约束全部演员。[原多项式卷31–35](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的单位第三标签、一次外层及删除完整PB的修改响应
各守原范围，不在这里重复，亦不被升级为完整候选反模型。

[原多项式卷80–84](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)已经支付二阶角、共同取向和任意背景下的秩一小连接行，不另计为
本组的新公式。99.1消费这些全代表公式后，仍在这个合法模型中分开商像
返回与原标签返回：每个 $p$、同一非零小窗及所有实际提升都在量词内。
失败的是精确原标签回溯或任意有限端点链这个供应类，不是[原多项式卷85.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的响应
等式本身，更不是原P2、PB或一般响应重构的不可能性。

## 102. 全域推导与七项实际来源的未缩减目标

**定义 102.1（端点图与完整原推导的区别）。** $\mathcal H$ 只记录每次
实际PB的两个端点可怎样相接，不是P2/PB的完整演绎闭包。96.4的非零荷、
多次调用共用的实际内值以及P2约束的耦合网络，均可提供超出无向可达性的
信息；97.1没有穷尽这些推导。不能从分量不连通推出响应不可识别，也不能
把增加端点边或步数当作已经支付另一种关系。

一般同一原 $D$ 在任意有限商、任意原代表上的[原多项式卷85.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)仍是所要求的生产
结论；99.9只是在给定标准模型中为真，没有生产一般未知映射的纤维不变性。
即使全部有限商的[原多项式卷85.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)另获证明，一般 $X$ 的有限商分离仍须支付。
一般无原子、无限维及可能不完备的原域保留，不能先把原域完成，再把完成
输入当作原输入。全部原对上的分别双线性、旧R、同一旧复乘法的结合闭合
及全部原评价的有限复Gram正性仍按[原多项式卷§85](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的准确一般边界要求证明。
没有加入无限端点链、未知输入连续性、响应极限或完成延拓。

**定义 102.2（七项同源物理合同）。** [原多项式卷87.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的七项完整合同逐项保留，
都指同一原 $\Omega$、原 $E/D$、原门序列与读出，而非另添物理模型：

1. Hilbert、可观察量和相干叠加仍需原全词 $K/J/q$、parent/ready、可取得
   标签、合法控制及实际相干准备。数学表示、商矩阵和射线不制造这些来源。
2. Born、态、效果及质量仍需原事件、准确效果区间与实际完整菜单，保留
   零／不等／次归一质量、中心权、不等维及静默块；只对正总质量归一。
   原抽签、共同根、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、
   预定强度、P9、独立 $W_e$、全部中间切口及固定支持全质量不省略。
3. native和张量仍需非零真实相关联合、忠实同向交换局部腿、共同实现、
   联合生成与分离、所需重数、所有相关输入和递归同源参考；相同边缘、
   相同商像或分别可达不能代替这份共同来源。
4. typed CP、Kraus与参考仍需原未归一回溯、合法前后接、反变复合、typed
   分区、全未来自然性与箭头下降。递归参考覆盖整台实际箭头、整个环境、
   全部成功／失败／细记录／port／post-port输出及每份输出所有仍合法未来；
   真实共同支持的三投影、支持内补、准确运输、全部相关正输入的intertwining
   与夹界、每个所需有限深度及累计支持完整链不因数学序零截面而取得。
5. 仪器、TP、更新和Lüders仍需完整typed菜单、原接受端、整个环境和上述
   全部输出未来、真正分组遗忘、AC、精确 $N_u$、X/Xs与原平方根词及接受
   条件；TP另需完整单位分区，Lüders另需完整输出校准的像内射线保持。
   只归一正输出质量，零分支保留；密度、迹类和Kraus公式仍守合格有限
   全矩阵域，或已供正规表示、指定前对偶及所需收敛的范围。
6. 历史、未来、真实返回和CountRead保留全部合法顺序／自适应／并行历史、
   每份输出的每个合法未来、整个环境与细记录泄漏、停止／拒绝／销毁、真正
   遗忘、同数两侧真实返回及同数逆向真实返回；读后同一原完整活动输入、
   负提升两条活路的分别控制和相干聚合、完整菜单接线、精确正生成 $B$
   与闭正生成 $B_{\rm cl}$ 的区别不省略。无限／非离散记录、可数可加、
   正常性及指定前对偶仍须各自来源。这里的 $B$ 仅在本项沿用[原多项式卷87.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的生成
   符号，不与96.1的C*代数名称相混；原 $q$ 零集及AC方向也不由商像决定。
7. 动力仍需同一旧全域乘法、保持原可能不完备域的流、实际相位与门序列、
   可逆一参数群、物理钟、强连续酉实现、生成元定义域、Hamiltonian能量、
   共同作用量、共同正 $\hbar$ 和共同仪器。原 $\sigma,t_0,d$、固定域、
   resolvent与 $3s+r\le1$ 预算保持[原多项式卷87.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)原义。多项式坐标 $t$、Cayley相位、
   证明参数和数学商均不是物理时间、能量、控制或共同尺度的供应。

上述合同保持全部原历史、未来和真实返回的量词；有限三维商、原多项式
单位和整体相位分量只界定所证方法的范围，不把完整量子起源目标结算为
有限窗口、标准响应例子或数学相容性。

## 追加锚（本行以下为增补区）
