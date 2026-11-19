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

## 103. 同一原总响应中联合检验族仍不足以识别原纤维

**定义 103.1（原域、固定读取与唯一修改轨道）。** 本续卷103–109的编号只指本续卷；引用外卷时均另列卷名。原多项式卷96–108与本续卷同号条目分别按所属卷引用。完整量子候选仍取[《AURIC：原多项式零响应与 Cayley 原域边界》80.1、89.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的同一原A1–A3、准确锥、全部原P2和完整PB，以及该卷87.1、95.1的全部实际来源合同。以下构造检验其中一个明确子系统的充分性，不把它改称完整PB候选。

对每个整数 $m\ge2$，令 $n=2m$。直接复用[《AURIC：原多项式零响应与 Cayley 原域边界》8.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的原域：

$$
\begin{aligned}
E_n&=\left\{\lambda I_n+\sum_{j=1}^d t^jA_j:
 \lambda\in\mathbb R,\ d<\infty,\ A_j=A_j^*\in M_n(\mathbb C)\right\},\\
\mathcal A_n&=\{a\in C([0,1],M_n(\mathbb C)):a(0)\in\mathbb C I_n\},
\qquad X_n=(\mathcal A_n)_{\rm sa},\\
u&=I_n,\qquad S(a,b)=a\circ b=(ab+ba)/2,\\
C_n&=E_n\cap(X_n)_+,\qquad
N(a)=\sup_{0\le t\le1}\|a(t)\|_{\rm op},\qquad
\pi=\operatorname{ev}_1:X_n\longrightarrow H_n(\mathbb C).
\end{aligned}
\tag{103.1}
$$

所有多项式都作为 $[0,1]$ 上的函数；区间上相等即系数相等。原评价取 $\mathcal A_n$ 上全部正泛函在 $E_n$ 的限制，保留每个非负质量，包括零、不等和次归一质量。这个 $E_n$ 含单位、无限维、在 $X_n$ 中稠密而不完备，不截断次数，也不将 $X_n$ 上的输入加入响应定义域。

固定标准Pauli矩阵的放大系数

$$
H=\sigma_z\otimes I_m,\qquad V=\sigma_x\otimes I_m,\qquad
W=\sigma_y\otimes I_m,\qquad
F=2tH,\qquad G=tV.
\tag{103.2}
$$

$H,V,W$ 是系数矩阵，不是原 $E_n$ 输入；$F,G$ 是原标签。已知比较映射为 $D_*(a,b)=i[a,b]/2$，于是 $D_*(F,G)=-2t^2W$。令

$$
\begin{aligned}
\mathcal S&=\{(o_{11}F+o_{12}G,\ o_{21}F+o_{22}G):O\in O(2)\},\\
\mathcal L&=\{\alpha F+\beta G:\alpha,\beta\in\mathbb R,\
                       \alpha^2+\beta^2=1\},\\
\widetilde D(a,b)&=
 \begin{cases}
 -D_*(a,b),&(a,b)\in\mathcal S,\\
 D_*(a,b),&(a,b)\notin\mathcal S.
 \end{cases}
\end{aligned}
\tag{103.3}
$$

这是全部 $E_n^2$ 上的一份总函数，$\mathcal L$ 准确为 $\mathcal S$ 的首槽投影。只在整条实际轨道上反号的机制直接复用[《AURIC：原多项式零响应与 Cayley 原域边界》32.1–32.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)，不另计为新的逐对正性机制。

对实际原 $r,x,y$，本节的 $\operatorname{PB}_{\widetilde D}(r;x,y)$ 始终指

$$
\begin{gathered}
v=\widetilde D(r,x)-r\circ y,\qquad
w=r\circ x+\widetilde D(r,y),\\
\widetilde D(x+v,y+w)-\widetilde D(x-v,y-w)
       =-2x\circ v-2y\circ w.
\end{gathered}
\tag{103.4}
$$

这是[《AURIC：配平三角的共同取向与秩一响应续卷》128.4、128.6](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)的原平方读取式及其元素形式；所有内外标签均为同一 $\widetilde D$ 真正生成的原标签，不换成同像代表。

**定理 103.2（全部联合族的一份原总映射反模型）。** 对每个偶数 $n=2m\ge4$，103.3的同一份 $\widetilde D$ 同时满足下列整个联合系统：

1. 原A1–A3与全部P2，原锥、单位、范数及全部评价质量不变；反对称、每槽奇性及全部普通 $SO(2)$ 槽旋转不变性成立。完整交换零集、同生成元多项式零行及范数界均保留：
   $$
   \widetilde D(a,b)=0\Longleftrightarrow[a,b]=0,\qquad
   \widetilde D(f(a),g(a))=0,\qquad
   N(\widetilde D(a,b))\le N(a)N(b).
   \tag{103.5}
   $$
   若 $a\circ b=0$，还有 $a\circ\widetilde D(a,b)=b\circ\widetilde D(a,b)=0$ 与 $\widetilde D(a,b)^2=a^2b^2$。
2. 对全部原演员 $r$、全部原 $x$ 及每个实数 $\tau$，包括 $\tau=0$，实际 $\operatorname{PB}_{\widetilde D}(r;x,\tau u)$ 成立；演员不要求中央或与 $x$ 交换。
3. 对每个原 $r\notin\mathcal L$，实际 $\operatorname{PB}_{\widetilde D}(r;x,y)$ 对全部原 $x,y$ 成立，不限制它们的核部分。更一般地，只要两份实际内值均等于对应 $D_*$ 值，该次PB便成立。
4. 在固定 $\pi=\operatorname{ev}_1$ 下，任一槽的像秩至多二时，原元素值本身满足 $\widetilde D(a,b)=D_*(a,b)$；像为标量的任一槽也如此。因此全部共同秩至多二Peirce角、全部秩一行和全部双支线星形行使用同一个固定取向 $+1$，包含全部实际代表、幅度及允许的背景。所有像为核、标量或秩至多二的演员都在第3项中。[《AURIC：原多项式零响应与 Cayley 原域边界》80–84、89–95](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的相应固定 $\pi$ 接口逐项保留，准确读法见106。

尽管这些条件在同一原域、同一总映射、同一固定 $\pi$ 下联合成立，原纤维不变性仍失败。确切地，取 $k=t(t-1)u$、$a_j=F+jk$，则对全部整数 $j$，

$$
\pi k=0,\qquad \pi a_j=2H,\qquad
f_j:=\pi\widetilde D(a_j,G)=
\begin{cases}
 2W,&j=0,\\
 -2W,&j\ne0,
\end{cases}
\quad
\|f_j\|=2,\qquad f_2-2f_1+f_0=4W\ne0.
\tag{103.6}
$$

而且全原域误差及加性缺陷有与 $m$ 和全部输入无关的统一界：

$$
\sup_{a,b\in E_n}N(\widetilde D(a,b)-D_*(a,b))=4,\qquad
N(\delta_a(b,c))\le12,\qquad
\delta_F(G,G)=-8t^2W\ne0,
\tag{103.7}
$$

其中 $\delta_a(b,c)=\widetilde D(a,b+c)-\widetilde D(a,b)-\widetilde D(a,c)$。完整PB确实失败：实际 $\operatorname{PB}_{\widetilde D}(F;G,F)$ 的元素两边为 $-8t^3V$ 和 $+8t^3V$，同一质量一正读取对原平方两边给出 $9$ 和 $41$。

证明分为104–107。这里结论是否定上述明确联合子系统的充分性，不是否定完整PB或完整量子起源。

## 104. 任意演员的相邻边都保持同一缺陷分支

**定理103.2的证明：全部相邻边。** 只在已知环境多项式乘法中记

$$
Z_0=F+iG=t(2H+iV),\qquad Z=x+iy,\qquad
Z_\pm=(u\pm ir)Z.
\tag{104.1}
$$

$(2H+iV)^2=3u$，并且

$$
\det Z_0=\det Z_0^*=(-3)^m t^n.
\tag{104.2}
$$

轨道 $\mathcal S$ 的复记录准确分成两个不相交的相位分支：

$$
\mathscr S_+=\{\eta Z_0:|\eta|=1\},\qquad
\mathscr S_-=\{\eta Z_0^*:|\eta|=1\}.
\tag{104.3}
$$

相交会给 $\eta(F+iG)=\zeta(F-iG)$；比较独立的 $F,G$ 系数便要求同时 $\eta=\zeta$、$\eta=-\zeta$，不可能。这两个分支分别对应 $\det O=+1,-1$。

现在令原 $r,x,y$ 完全任意，不作任何通勤假设。若 $Z_+$ 或 $Z_-$ 属于104.3，行列式乘法给

$$
P_\pm(t):=\det(u\pm ir(t))
        \ \mid\ c\,t^n\quad\text{于 }\mathbb C[t],
\qquad c\ne0.
\tag{104.4}
$$

因原演员 $r(0)=\rho u$、$\rho\in\mathbb R$，有 $P_\pm(0)=(1\pm i\rho)^n\ne0$。一个除 $t$ 外没有可能根的多项式若常数项非零，只能为常数；等价地，$\mathbb C[t]$ 中 $ct^n$ 的因子均为单项式。因此这份 $P_\pm$ 为非零常数。对系数取共轭并用 $r(s)^*=r(s)$，另一份 $P_\mp$ 也为常数。由此得到整条实轴上的系数恒等式

$$
\det(u+r(s)^2)=(1+\rho^2)^n=:K>0
\qquad(s\in\mathbb R).
\tag{104.5}
$$

每个实 $s$ 上 $r(s)$ 都Hermitian。若其特征值为 $\lambda_j(s)$，则

$$
\prod_{j=1}^n(1+\lambda_j(s)^2)=K,\qquad
\|r(s)\|_{\rm op}\le\sqrt{K-1}.
\tag{104.6}
$$

所以每个矩阵元的实部与虚部都是整条实轴上的有界实多项式，均为常数。$r$ 因而是常矩阵，标量端点再迫使 $r=\rho u$。这直接复用成熟的行列式因子、有界多项式和有限Hermitian谱工具；[《AURIC：原多项式零响应与 Cayley 原域边界》9.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)已有通勤运输中的这些工具，此处内部论证覆盖所有104.1演员。

此时两端只差一个单位复相位：

$$
Z_-=\frac{1-i\rho}{1+i\rho}Z_+.
\tag{104.7}
$$

因此只要任一端入轨道，另一端就在同一分支，而不能跳到反射分支。若没有端点入轨道，两端都在轨道外。没有用矩阵逆元产生原标签；104.7只除非零复标量。104.5–104.6的区间外值只证明多项式系数恒等式，响应和正读取仍只定义在原区间 $[0,1]$。

对任意复记录 $Z=a+ib$，在原域上定义缺陷

$$
\Delta(Z)=\widetilde D(a,b)-D_*(a,b)=
\begin{cases}
 4t^2W,&Z\in\mathscr S_+,\\
 -4t^2W,&Z\in\mathscr S_-,\\
 0,&Z\notin\mathscr S_+\cup\mathscr S_-.
\end{cases}
\tag{104.8}
$$

104.7给全部标准相邻边的同分支零余差关系

$$
\Delta((u+ir)Z)-\Delta((u-ir)Z)=0
\qquad(r,x,y\in E_n,\ Z=x+iy).
\tag{104.9}
$$

沿任意有限边链求和也为零；不取路径极限。这是标准PB边上的缺陷关系，不把未知响应预先下降为商函数。

若某次实际两内值为标准值，103.4的位移就是

$$
v_*=D_*(r,x)-r\circ y,\qquad
w_*=r\circ x+D_*(r,y),
\qquad
Z_\pm=(x\pm v_*)+i(y\pm w_*).
\tag{104.10}
$$

$D_*$ 满足完整PB；104.9说明把两份标准外值换成同一 $\widetilde D$ 时，差值不变，右端也未变，故实际103.4成立。这个“减去已知标准PB”的步骤直接使用[《AURIC：配平三角的共同取向与秩一响应续卷》139.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)的对应方式；没有在一般 $\widetilde D$ 内分配展开输入和。

特别是 $r\notin\mathcal L$ 时，两份 $(r,x),(r,y)$ 都不在 $\mathcal S$，全部实际内值标准。于是对这个演员及任意 $x,y$，包括任意不可见核部分，实际PB成立。没有把演员限制到交换类，也没有假定其两份内值为零。

## 105. 原正性与全部单位第三标签共同保留

**定理103.2的证明：静态条件及修改内值的PB。** 标准 $D_*$ 的原静态条件和完整PB直接取[《AURIC C128：任意维原对象保持的静态量子重构》35.1–35.2](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)，准确参数为 $\mathcal A=\mathcal A_n$、$\mathcal A_0=E_n+iE_n$、$\kappa=1$。对每份固定实际对 $(a,b)$ 及每个正实读取 $\phi$，其P2表

$$
\begin{pmatrix}
\phi(a^2)&\phi(a\circ b)-i\phi\widetilde D(a,b)\\
\phi(a\circ b)+i\phi\widetilde D(a,b)&\phi(b^2)
\end{pmatrix}
\tag{105.1}
$$

准确等于标准正表或该表的逐项复共轭，故仍正。未归一向量读取、一般正泛函及其全部非负质量均包括；若 $\phi(u)=0$，序单位界 $|\phi(a)|\le\phi(u)N(a)$ 使 $\phi=0$，不进行零质量除法。

$S$ 不变，所以A2的所有原实相加三表保持半正定；指定相加向量 $(1,-1,-1)$ 的实二次值为零，虚部则由反对称性成对抵消，排列同理。A3的 $u^2=u$ 和同一固定有理 $0<\theta\le1$ 上的小效果平方收缩完全不变。这并不证明任意三标签复表或全有限复Gram正性。

整条 $O(2)$ 轨道对换槽、任一槽反号及 $O(2)$ 换基封闭。已知 $D_*$ 在实槽换基下乘 $\det O$；103.3因而在全域保留反对称、每槽奇性及 $SO(2)$ 不变性。逐对乘 $\pm1$ 还保留完整零集和范数界，给103.5，包括全部单位行、中央多项式行与同生成元多项式零行。若 $a\circ b=0$，已知乘法给 $ab=-ba$、$D_*(a,b)=iab$；它与两输入反交换且平方为 $a^2b^2$，反号后这些等式仍成立。

现在固定任意原 $r,x$ 及任意实 $\tau$。总有 $\widetilde D(r,\tau u)=0$。若 $(r,x)\notin\mathcal S$，两内值标准，104已经支付这份实际PB。

若 $(r,x)\in\mathcal S$，Clifford系数给

$$
F^2=4t^2u,\qquad G^2=t^2u,\qquad F\circ G=0,\qquad
q:=r\circ x=\gamma t^2u,\qquad
e:=\widetilde D(r,x)=\pm2t^2W,
\tag{105.2}
$$

其中 $\gamma$ 是某个实数。$W$ 与 $H,V$ 反交换，所以 $x\circ e=0$。此时实际位移为 $v=e-\tau r$、$w=q$；两份真实外层的第二标签 $\tau u\pm q$ 都是原中央多项式，因此两份外值都为零。右端准确为

$$
-2x\circ(e-\tau r)-2\tau q
=-2x\circ e+2\tau q-2\tau q=0.
\tag{105.3}
$$

这覆盖修改内值的整个轨道、全部 $\tau$ 和 $\tau=0$，没有删除非中央演员或将实际外层换成辅助标签。故全部单位第三标签族与104的全部圈外演员族在同一个总映射中同时成立。

## 106. 固定读取的全部小角、秩一行与侧面接口

**定理103.2的证明：秩排除及实际代表。** 轨道中任一槽 $a=\alpha F+\beta G$ 满足

$$
\pi a=2\alpha H+\beta V,\qquad
(\pi a)^2=(4\alpha^2+\beta^2)u,\qquad
\alpha^2+\beta^2=1.
\tag{106.1}
$$

所以 $\pi a$ 可逆、秩准确为 $n\ge4$，且非标量；例如其迹为零而平方严格正。相同结论适用于第二槽。因此只要任一槽的 $\pi$ 像秩至多二，或像为标量，两槽就不可能组成异常对，响应在 $E_n$ 中本身等于 $D_*$。核扰动不改变这项秩排除；没有先删去原标签的核部分。

对固定 $Y=H_n(\mathbb C)$ 的任意秩至多二投影 $p$，两像共同位于Peirce角 $Y_2(p)=pYp$ 时，全部实际代表因此有

$$
\pi\widetilde D(a,b)=\frac i2[\pi a,\pi b].
\tag{106.2}
$$

它给[《AURIC：原多项式零响应与 Cayley 原域边界》80.2、82.1、84.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)所写固定 $\pi$ 角内全部混合值、共同取向及其角内消费者。[《AURIC：配平三角的共同取向与秩一响应续卷》240.1、243.1、244.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)中的自旋对象是这样一个Peirce角；在本固定满矩阵 $Y$ 中，非经典自旋Peirce角是秩二角。这里不将任意同构于自旋因子的嵌入子代数改称Peirce角。

更明确地，取任意数学单位向量 $e$，令 $p=ee^*$、$q=u-p$、$H_e(z)=ze^*+ez^*$，$z\perp e$。这些只是商矩阵坐标，不因此成为原标签。若实际 $r,a\in E_n$ 满足

$$
\pi r=\mu p,\qquad \pi a=\beta p+H_e(z)+B,\qquad B=qBq,
\tag{106.3}
$$

则任意实 $\mu,\beta$、任意 $z,B$ 及全部实际代表均有

$$
d:=\pi\widetilde D(r,a)
=\mu H_e(-iz/2).
\tag{106.4}
$$

幅度不设小窗。特别 $\pi r=0$ 时输出像为零。每个这样的 $r$ 都不在 $\mathcal L$，故其任意第二、第三原标签的实际PB也已支付。对任意演员 $a$，实际 $\operatorname{PB}_{\widetilde D}(a;r,0)$ 的两内值仍标准，故104同样支付它，即使 $a\in\mathcal L$。

对于双支线实际对

$$
A=\pi a=\alpha p+H_e(v),\qquad
B=\pi b=\beta p+H_e(w),
\tag{106.5}
$$

每个单独输入像秩至多二，尽管共同支撑 $\operatorname{span}_{\mathbb C}\{e,v,w\}$ 可以三维。因此全部幅度和实际代表均有

$$
\begin{aligned}
\pi\widetilde D(a,b)&=\frac i2[A,B]
 =-\operatorname{Im}(v^*w)p
   +H_e\!\left(\frac i2(\beta v-\alpha w)\right)+J(v,w),\\
J(v,w)&=\frac i2(vw^*-wv^*).
\end{aligned}
\tag{106.6}
$$

当 $v,w$ 复线性无关时，[《AURIC：原多项式零响应与 Cayley 原域边界》89–91](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的唯一侧面系数准确为 $\chi=1$。

再逐项核对同一次秩一PB的两份实际外值，避免只检查其孤立像。按106.3–106.4，写 $d=\delta p+H_e(w)$，则

$$
\delta=0,\qquad w=-i\mu z/2,\qquad C_0=p\circ\pi a=\beta p+H_e(z)/2.
\tag{106.7}
$$

实际 $\operatorname{PB}_{\widetilde D}(a;r,0)$ 的两份外值是

$$
\ell_+=\pi\widetilde D(r-\widetilde D(r,a),r\circ a),\qquad
\ell_-=\pi\widetilde D(r+\widetilde D(r,a),-r\circ a).
\tag{106.8}
$$

两对实际外层的像准确为 $(\mu p-d,\mu C_0)$、$(\mu p+d,-\mu C_0)$，共同支撑于 $\operatorname{span}_{\mathbb C}\{e,z\}$。由已证原值等于 $D_*$，直接得到

$$
\ell_+-\ell_-=2\mu p\circ d,\qquad
q\ell_+q=q\ell_-q=J_0,\qquad
J_0=-\frac{\mu i}{4}(wz^*-zw^*).
\tag{106.9}
$$

这正支付[《AURIC：原多项式零响应与 Cayley 原域边界》92.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的实际外层接线，且可取共同系数 $1$；$J_0=0$ 时不宣称系数唯一。[《AURIC：原多项式零响应与 Cayley 原域边界》93.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的非退化前提 $w\notin\mathbb Cz$ 在本模型中从不出现，故其条件预算在这里是真空满足，不是由本模型生产了一项新的饱和定理。[《AURIC：原多项式零响应与 Cayley 原域边界》94–95](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)保留的一般来源及待解生产者也不因此完成。

这些都是固定 $\pi$ 下明确列出的接口。没有宣称保留完整PB的全部已发表后果，或其他任意商表示、任意自旋子域上的全部识别。

## 107. 全整数原核曲率、统一有限缺陷与实际PB失败

**定理103.2的证明：同一总映射的残差。** 取 $k=t(t-1)u$ 与全部整数 $j$ 的 $a_j=F+jk$。它们始终是原标签，$\pi k=0$，$\pi a_j=2H$。若 $(a_j,G)\in\mathcal S$，在 $t=1$ 比较 $H,V$ 系数会迫使其正交系数矩阵为恒等矩阵。再比较实际多项式便得 $jk=0$，故 $j=0$。由于 $k$ 中央，

$$
\widetilde D(a_0,G)=2t^2W,\qquad
\widetilde D(a_j,G)=D_*(a_j,G)=-2t^2W\quad(j\ne0).
\tag{107.1}
$$

这给103.6，包含全部正、负整数及零。每份读取达到同一预算 $\|2H\|\|V\|=2$；同像原首标签的响应像却不相同，前向二阶差为范数四的 $4W$。特别是核标签本身的零响应与核平移不变性是不同命题。

104.8中非零偏差的原范数均准确为四，所以全局上确界为四且由 $(F,G)$ 取得。已知 $D_*$ 双线性，故

$$
\begin{aligned}
\delta_a(b,c)
 &=\Delta(a+i(b+c))-\Delta(a+ib)-\Delta(a+ic),\\
N(\delta_a(b,c))&\le4+4+4=12.
\end{aligned}
\tag{107.2}
$$

轨道保持已知平方和 $F^2+G^2=5t^2u$，而 $F^2+(2G)^2=8t^2u$，故 $(F,2G)$ 不在轨道。因此

$$
\widetilde D(F,2G)=-4t^2W,\qquad
\delta_F(G,G)=-8t^2W,\qquad N(\delta_F(G,G))=8.
\tag{107.3}
$$

这个缺陷也不在 $X_n$ 的Jordan中心：若 $\delta=-8t^2W$，则 $\delta\circ F=0$ 而

$$
[L_\delta,L_F]F=\delta\circ F^2=-32t^4W\ne0.
\tag{107.4}
$$

至此仍须直接核对完整PB，不能用非加性代替实际调用。取演员 $F$、第二标签 $G$、第三标签 $F$。实际内值为 $\widetilde D(F,G)=2t^2W$、$\widetilde D(F,F)=0$、$F\circ G=0$，所以

$$
v=2t^2W-4t^2u,\qquad w=0.
\tag{107.5}
$$

两份真实外层 $(G+v,F)$、$(G-v,F)$ 的首标签各有非零二次项，均不在 $\mathcal S$，故此时才使用标准双线性计算：

$$
\begin{aligned}
\widetilde D(G+v,F)&=2t^2W-4t^3V,\\
\widetilde D(G-v,F)&=2t^2W+4t^3V,\\
\text{103.4左端}&=-8t^3V,\qquad
\text{103.4右端}=+8t^3V.
\end{aligned}
\tag{107.6}
$$

同一原平方PB的两份元素更准确为

$$
\begin{aligned}
Q_+&=(G+v)^2+F^2+2\widetilde D(G+v,F)\\
   &=(5t^2+20t^4)u+(4t^2-16t^4)W-16t^3V,\\
Q_-&=(G-v)^2+F^2+2\widetilde D(G-v,F)\\
   &=(5t^2+20t^4)u+(4t^2-16t^4)W+16t^3V.
\end{aligned}
\tag{107.7}
$$

令 $\xi=(1,1)^T/\sqrt2\otimes e_1$，$e_1\in\mathbb C^m$ 为单位向量。正泛函 $\phi(a)=\xi^*a(1)\xi$ 的质量为一；系数矩阵的向量值为 $\xi^*V\xi=1$、$\xi^*W\xi=0$，这里不把 $V,W$ 送入原泛函的定义域。它读取107.6的两边为 $-8,+8$，读取107.7为 $9,41$。因此同一实际响应、实际嵌套标签与同一原正读取已给完整PB的非零失败。定理103.2证毕。∎

## 108. 原条件、完整商纤维与共同插值的准确边界

**定义 108.1（联合定理的来源和适用范围）。** 定理103.2的承重综合归为 $\texttt{repo-derived}$：同一放大总映射联合保留全部单位第三标签、精确圈外的全部演员PB、固定 $\pi$ 的全部小角／秩一／星形行和实际侧面接口，同时保留有界非零原核曲率。标准原域、反号轨道、Pauli／Clifford乘法、行列式因子和有界多项式均是复用的工具，不各立为新发现；不主张历史优先权或文献穷尽。

[《AURIC：原多项式零响应与 Cayley 原域边界》96–101](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)是在一个 $H_3(\mathbb C)$ 总映射中保全部P2、共同秩二角和两份指定演员次序的零第三标签PB，并实现[《AURIC：原多项式零响应与 Cayley 原域边界》93.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的侧面预算等号；[《AURIC：原多项式零响应与 Cayley 原域边界》100.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)还给出该总映射的实际重复第三标签失败。那个结果没有断言本节的全部单位第三标签、所有精确圈外演员和固定 $\pi$ 联合族。本节则将全部秩一行认成标准值，根本没有该结果的非共线连接泄漏，不能代替它的尖锐预算结论。

[《AURIC：原多项式零响应与 Cayley 原域边界》102–108](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的另一结论保留完整PB。其载体是任意秩三Euclidean丛的全部连续自旋截面，原稠密域的每点评价都满到整个 $H_2(\mathbb C)$，这些完整商共同分离截面。[《AURIC：原多项式零响应与 Cayley 原域边界》80.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)于是对每点的所有原输入共用一个符号；固定实际输出的连续性才将符号拼成连续取向，之后才推出同一旧表的线性与完成。

本节的给定载体并不满足这个对应：在 $t>0$，$X_n$ 的实际点评价满到 $H_n(\mathbb C)$，$n\ge4$，完整纤维不是 $H_2(\mathbb C)$；在 $t=0$，实际点评价像只有 $\mathbb Ru$。秩二Peirce压缩不是整个 $X_n$ 的Jordan满商，不能把106.2改说成每点所有输入都被同一二阶商识别。每份输出仍连续，甚至是多项式，但这不补完整PB和该共同符号前件。

还须明确保留一个实质排除项。原子域

$$
\mathcal R=\{a\otimes I_m:a\in E_2\}\subset E_n
\tag{108.1}
$$

对Jordan乘法与 $\widetilde D$ 都闭合，因为 $D_*$ 及其反号均保留此形式。它的 $\pi$ 像 $H_2(\mathbb C)\otimes I_m$ 是一个自旋子代数，却不是固定 $H_n(\mathbb C)$ 中的秩二Peirce角：其单位为秩 $n$ 的 $u$，而 $Y_2(u)=Y$；其中103.2的非标量轴像也有秩 $n$。在这个响应闭合子域上，$(F,G)$ 取反向值而 $(F,2G)$ 取标准值，违反[《AURIC：原多项式零响应与 Cayley 原域边界》36.2、51.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的共同取向结论。它们的完整PB前提也准确由107.6失败，故不存在矛盾，但绝不能宣称本节保留任意复制 $E_2$ 子域或完整PB的全部已付后果。

即使只看这个复制子域，其完成也是零点必须标量的 $X_2$，而非整条区间上常秩的 $C([0,1],H_2)$。零点向量部必须消失，原域在后一个空间中并不稠密，零点也没有满 $H_2$ 评价。因此不能将它直接送入[《AURIC：原多项式零响应与 Cayley 原域边界》102.1–102.3](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的秩三截面域假设。[《AURIC：原多项式零响应与 Cayley 原域边界》51.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)已在它自己的标量端点域中以完整PB支付识别；本节没有重新打开那项已付结论。

**命题 108.2（系数轴不成为实际单位平方框架）。** 原 $h\in E_n$ 若 $h^2=u$，则 $h=\pm u$，故此原域没有非平凡的实际单位平方三轴框架。

证明。$h^2=u$ 从区间成为多项式恒等式。每个实 $s$ 上 $h(s)$ 自伴且平方为单位，故 $\|h(s)\|=1$；有界多项式矩阵元均为常数。标量端点使常矩阵只能为 $\pm u$。∎

因此[《AURIC：中央响应平方与径向一致续卷》173.1、182.1–184.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)所需实际 $h,e,j$、实际反射系数及其扇区条件在这里没有实例。$H,V,W$ 只在系数计算中出现；不对它们或域外平方根、逆元、谱投影、谱符号及完成标签调用 $\widetilde D$，也不把 $F/(2t)$ 当作合法输入。

[《AURIC：中央响应平方与径向一致续卷》188–195](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)中的189.1在实际 $h,e,j$ 框架下给出全部实 $\alpha,\beta$ 的仿射交换零行 $[h,y]=0\Rightarrow D(\alpha u+\beta h,y)=0$；192.1–192.2再取182.1的同一实际交换反射 $s$，把双偶余量及纯跨反射扇区的同一旧值识别扩至任意实首强度 $R$。它们均保留完整原P2/PB；一般混合扇区不能由两条纯分支直接相加，无实际框架的分支也仍未付。本节的108.2排除了其非平凡实际 $h,e,j$ 前件，且107.6明确不满足完整PB，故这些条件结果不把103.3的旧总表变成线性，也不消去103.6的原核曲率。

**定义 108.3（有界缺陷与原生产者）。** 107.2直接给全原域 $\mathsf{BD}$，并使球内缺陷函数 $A(R)\le12$，所以还满足 $\mathsf{SL}$；107.4则直接否定本映射的 $\mathsf C_{\rm add}$。[《AURIC C128：任意维原对象保持的静态量子重构》89.2、91.1、95.1](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)的中心缺陷桥、有界误差刚性和次线性刚性都在完整PB背景中陈述。本模型缺该共同前提，故不反驳其中任一结果，更不构成完整PB加有界缺陷的反模型。一般完整原P2/PB是否自动生产零曲率、一般纤维一致性或 $\mathsf C_{\rm add}$，以及所有重复第三标签PB是否足够，均仍是原目标中的未解生产者问题。107.6只证明一份重复第三标签确实能够检出当前缺陷。

**定义 108.4（共同插值文献的未付前件）。** 成熟文献 [Cabello–Peralta，*Weak-2-local symmetric maps on C*-algebras*，arXiv:1510.00915v1，Theorem 2.5](https://arxiv.org/html/1510.00915v1)要求在完整复C*代数上，对每两个输入和每个对偶泛函存在同一个复线性保星插值器；[ *2-Local and local derivations on Jordan matrix rings over commutative involutive rings*，arXiv:2108.03993v4，Theorem 4](https://arxiv.org/html/2108.03993v4)要求其完整自伴矩阵Jordan环上每一对输入共用一个内导子，系数环保持文内的含单位、交换、对合及二可逆条件。这些是共同插值前提，不是逐对另选正负交换子。

本例甚至有一个固定读取直接排除相应共同线性插值。取 $W$ 的单位正特征向量 $\eta$ 并用质量一泛函 $\psi(a)=\eta^*a(1)\eta$，则同一行 $T(b)=\widetilde D(F,b)$ 满足

$$
\psi(T(G))=2,\qquad \psi(T(2G))=-4.
\tag{108.2}
$$

若一个加性映射或实／复线性插值器同时匹配这两份读取，第二个数必须等于第一个数的两倍，即四，矛盾。共同内导子也至少加性，故同样不能匹配。没有一个与该行相容的延拓能够修复这两点矛盾；也未给未知原响应以完整复C*域或完整矩阵环为定义域的合法延拓。文献在此仅用于精确辨认缺少的前件，不参与103.2的证明，亦不以未命中文献宣称原创。

## 109. 原量子起源的完整消费者与联合边界的含义

**定义 109.1（数学结论与七项实际来源合同）。** 完整原候选仍要求同一原 $\Omega/\mathrm{native}$、原 $E/S/D$、全部A1–A3/P2和完整PB，不以103.2的子系统替换。一般原域可以不完备、无限维、不可分或没有原最小投影；不能先完成、添轴或挑选有限商后冒认原问题已经解决。以下逐项与[《AURIC：原多项式零响应与 Cayley 原域边界》87.1、95.1、107.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)及其原合同合取，保留所有实际对象和原量词。

1. **Hilbert、可观察量与相干准备。** 同一唯一 $\Omega$ 中的全词同一 $K/J/q$、任意词及零词、parent/ready类型、可取得原标签、合法控制和实际相干准备仍须同源供应。数学矩阵表示、连续函数和原标签的线性空间不制造准备，也不给全 $B(H)$ 的实际可取得像；一般无轴、无原子和不完备域仍在完整目标内。
2. **态、效果、质量与Born。** 原评价必须绑定同源原事件、准确效果及实际完整菜单，保留全部零、不等、次归一质量、中心经典权、不等维与静默块。共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定强度、P9、独立 $W_e$、全部中间切口和固定支持全质量仍须原来源。Born只归一实际完整菜单的严格正总质量；零质量不除。向量正读取不证明实际菜单齐备、正规态或实际准备。
3. **相关联合、张量与递归参考。** 仍需同一个真实非零相关联合、忠实同向且交换的局部腿、交叉关系、共同实现、联合生成与分离、所需重数、所有相关输入及每层递归同源参考；中心对、经典和不等维块保留。103.2中的 $I_m$ 仅为代数重数，既不供应实际联合也不供应参考。相同边缘、分别可达或同一取向不能替代共同实现。
4. **typed CP、Kraus接线与全部输出。** 原未归一回溯、合法typed前接后接、反变复合、typed分区、全未来自然性及箭头／支持下降仍须真实来源。参考覆盖系统、整个环境、全部成功、失败、细记录、port和post-port输出，以及每份输出每个仍合法未来；共同真实支持的三投影、支持内补、准确运输、所有相关正输入的intertwining与夹界、每个所需有限递归深度和累计支持完整链均保留。这里没有将商矩阵投影提升为原实际投影，也没有构造这些箭头或参考。
5. **完整仪器、TP、更新与Lüders。** 完整typed菜单、原接受端、整台环境及上述全部输出和未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及其接受条件仍须原合同。TP另需完整单位分区；Lüders另需同一完整输出的像内射线校准。更新只归一严格正输出质量，零分支及其未来保留。密度、迹类和算子Kraus公式限于合格有限全矩阵物理域，或另已供应正常物理表示、指定前对偶及所需收敛的适用域。
6. **全部历史、未来、真实返回与CountRead。** 全部合法顺序、自适应和并行历史，每份输出的全部合法未来，环境及细记录泄漏、停止、拒绝、销毁、真正分组遗忘、同数两侧以及同数逆向／双向实际返回均保留。读后同一原完整活动输入、负提升两条活路的分别控制与相干聚合、具名分析词接回原完整菜单及接受端仍须实际构造。精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 不混同；无限历史、无限或非离散记录、可数可加、normality和指定前对偶不被有限矩阵计算代付。相同商像或相同读数不等同程序、实际读取次序、原 $q$ 零集或AC方向。
7. **原域动力、物理钟、能量与共同尺度。** 同一旧全域乘法、保持可能不完备原域的流、实际门序列与相位、可逆一参数群、物理钟、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同作用量、共同正 $\hbar$ 和共同仪器仍须同源供应。原 $\sigma,t_0,d$、固定域、resolvent与 $3s+r\le1$ 的预算不改含义。多项式坐标 $t$、槽相位、重数 $m$、整数平移 $j$ 及辅助行列式界都不是物理时间、控制、能量或作用量尺度。

**定义 109.2（联合检验与同一来源的几何含义）。** 单独的两两比较可以保持正性、反向符号和共同旋转；现在还把所有单位第三标签、圈外每个演员的所有三元接法，以及固定读取下每个真正二维小角和每条秩一连接同时接上。103.2表明，这些要求即使由同一张总表全部履行，也仍有一整圈满秩输入对可以反向而不被它们检出：触到这圈的标准配平边只能用标量演员，只在同一分支上转动；单位第三标签触到修改内值时，Clifford关系又使两张真实外表和电荷同时归零；真正的小角则因秩不够根本碰不到它。于是两份原输入即使在固定读取中完全同像，整圈内外的旧输出仍可不同，并留下有界非零曲率。让第一对象真实地再次进入第三槽，原配平立即读出矛盾。

这里减少的是一条联合子系统足够性的候选路线，没有减少完整原公理数。二元归一化和有限三方向的几何直观仍可用于寻找更紧的真实接线，但每条接线必须来自同一原世界、同一门序列及其真实读出；不能把同像代表、辅助标准乘法、数学完成或重数当作这个来源。一般完整PB的零曲率／纤维／可加性生产者与上述七项物理合同，保持各自完整未解范围。

## 追加锚（本行以下为增补区）

## 110. 混合反射余量的固定元组域

**定义 110.1（必要关系域与全部标量读取）。** 本节另用一个固定元组域，
不沿用96.1的多项式原模型。设 $\mathcal B$ 是含单位复C*代数，单位记 $I$，
$h,e,s,Q,z,r$ 是其中的自伴元素，满足

$$
\begin{gathered}
h^2=e^2=s^2=Q^2=I,\quad he=-eh,\quad [s,h]=[s,e]=0,
\quad Q\in Z(\mathcal B),\\
hz=-zh,\quad [r,h]=[r,s]=0,\quad
z_{\rm e}=\tfrac12(z+szs),\quad z_{\rm o}=\tfrac12(z-szs),
\quad z_{\rm e}\circ r=0,\\
c=\lambda h+\nu s,\quad x=c+z,\quad
\tau=iQhz,\quad g=\tau+r,\quad k=h\circ x=hc,
\quad a\circ b=(ab+ba)/2,
\end{gathered}
\tag{110.1}
$$

其中 $\lambda,\nu\in\mathbb R$、$\nu\ne0$。特别 $[r,c]=0$，
$\tau,g,k$ 自伴。这里没有总映射 $D$，也没有把 $g$ 定义成其某个值；
只有这一份共同的输入、候选输出和余量。所检验的固定P2是

$$
\phi(I)\phi(x^2)\ge[\phi(k)]^2+[\phi(g)]^2
\quad\text{对每个连续正泛函 }\phi:\mathcal B\to\mathbb C.
\tag{110.2}
$$

所有质量 $\phi(I)\ge0$ 都在量词内，包含零、不等与次归一质量。
这些泛函是数学读取，不是另行供应的实际物理准备。

**定理 110.2（同一八阶元组的全态固定P2与非零混合余量）。** 令
$\mathcal B=M_2(\mathbb C)^{\otimes3}=M_8(\mathbb C)$，采用标准Pauli矩阵

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
P_\pm=(I_2\pm Z)/2.
\tag{110.3}
$$

固定精确常数及第三因子上的自伴矩阵

$$
A=\operatorname{diag}(0,1/2),\quad t=1/16,\quad
\varepsilon=2^{-52},\quad L_1=A,\quad L_2=-A+tX.
\tag{110.4}
$$

对每个预先给定的实 $\lambda,\nu\ne0$，在同一个代数中同时取

$$
\begin{gathered}
h=I_2\otimes Z\otimes I_2,\quad e=I_2\otimes X\otimes I_2,
\quad s=I_2\otimes I_2\otimes Z,\quad Q=I_8,\\
z_0=P_+\otimes X\otimes L_1+P_-\otimes X\otimes L_2,
\quad r_0=\varepsilon X\otimes I_2\otimes I_2,\\
z=\nu z_0,\quad r=\nu r_0,\quad c=\lambda h+\nu s,
\quad x=c+z,\quad \tau=ihz,\quad g=\tau+r.
\end{gathered}
\tag{110.5}
$$

则110.1全部成立，110.2对全部连续正泛函成立，并且

$$
\boxed{r\ne0,\qquad z_{\rm e}\circ r=0,\qquad
z_{\rm o}\circ r=\nu^2 2^{-57}X\otimes X\otimes X\ne0.}
\tag{110.6}
$$

同一个元组还满足全实参数算子铅笔正性

$$
\boxed{x^2+2ak+2bg+(a^2+b^2)I_8\ge0
\qquad(a,b\in\mathbb R).}
\tag{110.7}
$$

元组不随 $a,b$ 或 $\phi$ 改变。证明在111–113给出；非正规矩阵的逆界
由显式多项式投影支付，不使用正规算子的距离谱公式。

## 111. 同一元组的偶奇与全参数归约

证明110.2。由Pauli乘法，$h,e,s,Q$ 自伴且平方为单位；$h,e$ 反交换，
$s$ 与二者交换，$Q$ 中央。还可在同一代数取

$$
j=ihe=-I_2\otimes Y\otimes I_2,
\quad j^2=I_8,\quad hj=-jh,\quad ej=-je,\quad ihej=I_8.
\tag{111.1}
$$

这是矩阵框架身份，不是宣告存在一个满足全部原公理的 $D$ 且 $D(h,e)=j$。
$A,L_1,L_2,z_0,r_0$ 自伴，故 $z,r,c,x$ 自伴。
$z$ 的中间因子为 $X$，所以 $hz=-zh$；$r$ 只作用于第一因子，
所以它与 $h,s,c$ 交换，也与 $e,j$ 交换。
$hz$ 反自伴，因此 $\tau=ihz$、$g$ 自伴。
由 $h\circ z=0$ 得 $k=hc=\lambda I_8+\nu hs$ 自伴，且

$$
\tau^2=z^2,\qquad z\circ\tau=h\circ\tau=0,\qquad k^2=c^2.
\tag{111.2}
$$

沿第三因子的 $Z$ 反射，$A$ 为偶、$X$ 为奇。因此准确地

$$
z_{\rm e}=\nu Z\otimes X\otimes A,
\qquad z_{\rm o}=\nu tP_-\otimes X\otimes X.
\tag{111.3}
$$

两者均非零，故该输入不是纯偶或纯奇分支。
$ZX=-XZ$ 给 $z_{\rm e}\circ r=0$；
$P_-X+XP_-=X$ 则给

$$
z_{\rm o}\circ r
=\frac{\nu^2\varepsilon t}{2}X\otimes X\otimes X
=\nu^2 2^{-57}X\otimes X\otimes X.
\tag{111.4}
$$

$r^2=\nu^2\varepsilon^2I_8$，故 $r\ne0$；111.4的右侧也非零。
这些都是同一组矩阵的关系，没有更换余量或删去 $[r,h]=[r,s]=0$。

为证明110.7，对任意实 $a,b$ 置

$$
\alpha=(a+\lambda)/\nu,\quad \beta=b/\nu,\quad
u_0=s+z_0,\quad w=\alpha-i\beta.
\tag{111.5}
$$

展开已经给定的结合乘法，原铅笔除以正数 $\nu^2$ 后恰为

$$
\begin{aligned}
K(\alpha,\beta)
&=u_0^2+2\alpha hs+2\beta(ihz_0+r_0)
 +(\alpha^2+\beta^2)I_8\\
&=C(w)^*C(w)+2\beta r_0,\qquad
C(w)=s+z_0+wh.
\end{aligned}
\tag{111.6}
$$

确实 $\{h,u_0\}=2hs$、$[h,u_0]=2hz_0$，所以
$C(w)^*C(w)=u_0^2+2\alpha hs+(\alpha^2+\beta^2)I_8+2i\beta hz_0$。
其中 $\lambda$ 的消失是完整平方的准确相消，不是旧响应的单位平移规律。
$\nu<0$ 同样合法，且111.5仍遍历全部实 $\alpha,\beta$。

按第一因子的 $P_+,P_-$ 分块，在 $\mathbb C^4\oplus\mathbb C^4$ 上有

$$
C(w)=\operatorname{diag}(C_1(w),C_2(w)),\quad
C_j(w)=I_2\otimes Z+X\otimes L_j+wZ\otimes I_2,
\tag{111.7}
$$

$$
K(\alpha,\beta)=
\begin{pmatrix}
C_1(w)^*C_1(w)&2\beta\varepsilon I_4\\
2\beta\varepsilon I_4&C_2(w)^*C_2(w)
\end{pmatrix}.
\tag{111.8}
$$

$\beta=0$ 时111.8已正。其余参数要控制两个块在同一个 $w$ 处的逆，
不能只各自寻找最小值后假定它们同时可达。

## 112. 两个非正规块的显式多项式投影

证明110.2（续）。为111.7定义四阶矩阵

$$
J_j=(Z\otimes I_2)(I_2\otimes Z+X\otimes L_j),
\qquad C_j(w)=(Z\otimes I_2)(J_j+wI_4).
\tag{112.1}
$$

这里 $J_j$ 不假设正规。直接乘法给

$$
J_j^2=I_2\otimes(I_2-L_j^2)+X\otimes[Z,L_j].
\tag{112.2}
$$

对 $j=1$，$[Z,A]=0$，于是

$$
J_1^2=I_2\otimes\operatorname{diag}(1,3/4),\qquad
(J_1^2-I_4)(J_1^2-\tfrac34 I_4)=0.
\tag{112.3}
$$

对 $j=2$，使用

$$
L_2=\begin{pmatrix}0&t\\t&-1/2\end{pmatrix},\quad
I_2-L_2^2=(7/8-t^2)I_2+\tfrac18Z+\tfrac t2X,\quad
[Z,L_2]=2itY.
\tag{112.4}
$$

令 $B=J_2^2-(7/8-t^2)I_4$。112.4中三个非标量Pauli项两两反交换，故

$$
B^2=\left(\frac1{64}+\frac{t^2}{4}-4t^2\right)I_4
=\frac1{1024}I_4\qquad(t=1/16).
\tag{112.5}
$$

因此设

$$
\mathcal M_1=\{1,3/4\},\qquad
\mathcal M_2=\{231/256,215/256\},
\tag{112.6}
$$

则两个矩阵都满足
$\prod_{\mu\in\mathcal M_j}(J_j^2-\mu I_4)=0$。
112.6只来自 $7/8-t^2=223/256$ 及112.5的两个根 $\pm1/32$，
不是对矩阵作数值谱近似。

对每个 $\mu\in\mathcal M_j$，以 $\mu'$ 记同一集合中另一元素，定义

$$
E_{j,\mu}=\frac{J_j^2-\mu'I_4}{\mu-\mu'},\qquad
F_{j,\mu,\sigma}=\frac12\left(I_4+\frac{\sigma J_j}{\sqrt\mu}\right)E_{j,\mu}
\quad(\sigma=\pm1).
\tag{112.7}
$$

平方多项式恒等式给 $E_{j,\mu}^2=E_{j,\mu}$、
$E_{j,\mu}E_{j,\mu'}=0$、$E_{j,\mu}+E_{j,\mu'}=I_4$、
$J_j^2E_{j,\mu}=\mu E_{j,\mu}$。于是112.7进一步给

$$
\sum_{\mu,\sigma}F_{j,\mu,\sigma}=I_4,\qquad
J_jF_{j,\mu,\sigma}=\sigma\sqrt\mu\,F_{j,\mu,\sigma}.
\tag{112.8}
$$

这些是代数投影，不是正交投影。特别，若所有分母非零，则

$$
(J_j+wI_4)^{-1}
=\sum_{\mu\in\mathcal M_j,\,\sigma=\pm1}
\frac{F_{j,\mu,\sigma}}{w+\sigma\sqrt\mu}.
\tag{112.9}
$$

左乘和右乘 $J_j+wI_4$ 都由112.8给单位，因此112.9直接证明可逆，
不需要从实特征根推断一个未经支付的正规性或条件数。

下面逐项支付投影范数。$\|L_1\|=1/2$、$\|L_2\|\le1/2+t=9/16$ 给
$\|J_j\|\le25/16<2$、$\|J_j^2\|<4$。
112.6中 $0<\mu\le1$、$\sqrt\mu>1/2$，而
$|\mu-\mu'|\ge1/16$，所以

$$
\|E_{j,\mu}\|\le80,\qquad
\|F_{j,\mu,\sigma}\|<\frac52\,80=200,
\qquad \sum_{\mu,\sigma}\|F_{j,\mu,\sigma}\|<800<2^{10}.
\tag{112.10}
$$

令实根集合及其复平面距离为

$$
\mathcal S_1=\{\pm1,\ \pm\sqrt3/2\},\qquad
\mathcal S_2=\{\pm\sqrt{231}/16,\ \pm\sqrt{215}/16\},\qquad
 d_j(w)=\min_{q\in\mathcal S_j}|w-q|.
\tag{112.11}
$$

两集合关于零对称。由112.1、112.9–112.10，在 $\beta\ne0$ 时

$$
\|C_j(\alpha-i\beta)^{-1}\|\le\frac{2^{10}}{d_j(\alpha-i\beta)}.
\tag{112.12}
$$

这条界包含了代数投影的范数，正是非正规性所需的代价。

两个集合的正根均小于或等于一；跨集合的正根平方差至少为 $23/256$，
因为分子四种差为 $25,41,39,23$。同号根之差因而至少为 $23/512$；
异号根之差大于一。故

$$
\delta:=\min_{q_1\in\mathcal S_1,q_2\in\mathcal S_2}|q_1-q_2|
\ge23/512>1/32.
\tag{112.13}
$$

对同一个 $w=\alpha-i\beta$，取各集合中的最近根，用三角不等式得
$d_1(w)+d_2(w)\ge\delta$；又因两集合实，$d_j(w)\ge|\beta|$。
所以在 $\beta\ne0$ 时

$$
\frac{|\beta|}{d_1(w)d_2(w)}\le\frac2\delta<2^6,
\qquad
|\beta|\,\|C_1(w)^{-1}\|\,\|C_2(w)^{-1}\|\le2^{26}.
\tag{112.14}
$$

第一式只需较大的那个距离至少为 $\delta/2$，另一个至少为 $|\beta|$。
这是同时对全部实 $\alpha,\beta\ne0$ 的同一界。

## 113. 全铅笔正性与全部质量的准确等价

证明110.2（续）。在111.8中取任意 $v_1,v_2\in\mathbb C^4$。
$\beta\ne0$ 时令 $u_j=C_j(w)v_j$。112.14给

$$
\begin{aligned}
\langle(v_1,v_2),K(\alpha,\beta)(v_1,v_2)\rangle
&=\|u_1\|^2+\|u_2\|^2+4\beta\varepsilon\operatorname{Re}\langle v_1,v_2\rangle\\
&\ge\|u_1\|^2+\|u_2\|^2
 -4\varepsilon|\beta|\|C_1^{-1}\|\|C_2^{-1}\|\|u_1\|\|u_2\|\\
&\ge(1-2\varepsilon 2^{26})(\|u_1\|^2+\|u_2\|^2)\\
&=(1-2^{-25})(\|u_1\|^2+\|u_2\|^2)\ge0.
\end{aligned}
\tag{113.1}
$$

只用了 $2\|u_1\|\|u_2\|\le\|u_1\|^2+\|u_2\|^2$。
$\beta=0$ 时扰动项本来为零，$K=C^*C\ge0$。
111.5–111.6于是给110.7，包含铅笔的所有可能奇异参数。
所给 $\varepsilon$ 原值已足够，不需要更换常数或随态调节。

现在在任意含单位C*代数中说明所用等价的两个方向。
固定自伴 $x,k,g$，记 $m=\phi(I)$。正泛函在自伴元上的序界给
$|\phi(y)|\le m\|y\|$；因此 $m=0$ 时 $\phi=0$，110.2自动成立，
且每个铅笔的读取均为零。不对零质量作除法。
若 $m>0$，110.7的正读取是对全部实 $a,b$ 的不等式

$$
\phi(x^2)+2a\phi(k)+2b\phi(g)+m(a^2+b^2)\ge0.
\tag{113.2}
$$

取 $a=-\phi(k)/m$、$b=-\phi(g)/m$，便得110.2。
反过来，110.2使113.2可写成

$$
 m\left(a+\frac{\phi(k)}m\right)^2
 +m\left(b+\frac{\phi(g)}m\right)^2
 +\phi(x^2)-\frac{[\phi(k)]^2+[\phi(g)]^2}{m}\ge0.
\tag{113.3}
$$

故每个铅笔被全部正泛函读为非负；正泛函分离自伴正锥，遂给110.7。
零质量方向已单列，因此两者等价的量词是全部正泛函、全部实铅笔参数，
没有先取一份态再重选输出。110.2也对任意正质量缩放保持齐次，因而
不等与次归一质量全部包括。对 $M_8$ 的证明没有要求正常态、忠实态、
纯态或任何物理可取得性。110.2至此得证。∎

## 114. 同一元组的算子二表为何能检出余量

**定理 114.1（标量二表与算子二表的严格差别）。** 在110.1的 $Q=I$ 分支，
对同一个 $x,k,g$ 定义 $M_2(\mathcal B)$ 中的自伴矩阵

$$
\mathcal W=\begin{pmatrix}x^2&k+ig\\k-ig&I\end{pmatrix}.
\tag{114.1}
$$

则 $\mathcal W\ge0$ 当且仅当 $r=0$。
对110.5这个同一元组，每个连续正泛函给出的标量矩阵

$$
\begin{pmatrix}\phi(x^2)&\phi(k)+i\phi(g)\\
\phi(k)-i\phi(g)&\phi(I)\end{pmatrix}
\tag{114.2}
$$

均半正定，然而 $\mathcal W$ 本身不是正元，并有下述明确负向量。

证明。置 $B_0=k+ig=xh+ir$，利用 $[r,h]=[r,c]=0$，直接得到

$$
B_0B_0^*=x^2+r^2+2ih(z\circ r),\qquad
\Delta:=x^2-B_0B_0^*=-r^2-2ih(z\circ r).
\tag{114.3}
$$

$z\circ r$ 为 $h$-奇，而 $r^2$ 为 $h$-偶。
Schur补在这里就是准确的可逆三角因子分解

$$
\mathcal W=
\begin{pmatrix}I&B_0\\0&I\end{pmatrix}
\begin{pmatrix}\Delta&0\\0&I\end{pmatrix}
\begin{pmatrix}I&0\\B_0^*&I\end{pmatrix}.
\tag{114.4}
$$

因此 $\mathcal W\ge0$ 等价于 $\Delta\ge0$。
若后者成立，则 $h\Delta h\ge0$，而

$$
\tfrac12(\Delta+h\Delta h)=-r^2.
\tag{114.5}
$$

自伴平方又为正，故 $r^2=0$、$r=0$。反向 $r=0$ 时114.3给
$\Delta=0$，114.4给 $\mathcal W\ge0$。

对110.5，由111.4及 $ZX=iY$，114.3准确成为

$$
\Delta=\nu^2\varepsilon\bigl(tV-\varepsilon I_8\bigr),
\qquad V=X\otimes Y\otimes X.
\tag{114.6}
$$

取单位向量

$$
\eta=|+\rangle_X\otimes|+\rangle_Y\otimes|-\rangle_X,
\quad |\pm\rangle_X=2^{-1/2}(1,\pm1)^{\mathsf T},
\quad |+\rangle_Y=2^{-1/2}(1,i)^{\mathsf T}.
\tag{114.7}
$$

$V\eta=-\eta$，故在同一个 $\mathbb C^8\oplus\mathbb C^8$ 中

$$
\left\langle(\eta,-B_0^*\eta),
\mathcal W(\eta,-B_0^*\eta)\right\rangle
=\langle\eta,\Delta\eta\rangle
=-\nu^2\varepsilon(t+\varepsilon)<0.
\tag{114.8}
$$

另一方面，114.2的对角非负，行列式正好是110.2的差。
$m>0$ 时由该行列式判准给正性，$m=0$ 时整表为零。
特别以向量正泛函读取时，$\mathcal W$ 对每个乘积向量
$\xi\otimes v\in\mathbb C^2\otimes\mathbb C^8$ 的二次值都非负，
却在114.8所给联合向量上为负。两个分量可分别选择的联合读取，严格
强于同一个标量系数乘同一向量的读取。∎

114.1是对一张给定算子表的条件，不是对某个已给线性映射的二正性或CP
结论；本节没有定义这种映射，更没有从原P2取得其矩阵放大正性。
若要把114.1当作原物理消费者的输入，须另从同一原资料供应这整张
算子二表的正性，或供应足以推出它的合法联合来源；不能把它加入原
A1–A3/P2/PB而不记为新增前件。

## 115. 固定P2的必要对边界与原PB已付的反射排除

**定义 115.1（原接口的逐项对应）。** 以下中央条目均指
[中央响应平方续卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)。
110–114的固定元组与原候选的对应只限于下表所列关系；中央201.1及其现有
扩展[谱混合响应卷27.1](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md)
则在完整196.1、实际182.1–182.2及199.2全部七项来源合同下识别整条混合
反射行，不以固定元组满足这些必要关系代替其完整前件。

| 原接口 | 110.5的准确对应 | 准确适用范围与未付部分 |
| --- | --- | --- |
| 173.1、173.2的框架及 $x=c+z$、$t=iQhz$、$d=t+r$ | 单位为 $I_8$，111.1给矩阵 $j,Q$，原 $t$ 对应 $\tau$，候选 $d$ 对应 $g$，$k=hc$；111.2支付平方与正交身份 | 没有总 $D$，故没有声称 $j=D(h,e)$、$\tau=D(h,z)$ 或 $g=D(h,x)$ 已由同一总映射实现 |
| 173.2的原P2 | 第一标签固定为 $h$，因 $h^2=I_8$，恰为110.2；113同时覆盖全部质量 | 未给其他任意原对的响应，更未给全部嵌套调用 |
| 182.1–182.4的反射分支 | 实际矩阵 $s^2=I_8$、$[s,h]=[s,e]=0$，同一 $c=\lambda h+\nu s$，同一有限偶奇分解 | 反射矩阵的存在不供应原 $\Omega$ 内的实际标签取得或物理子系统 |
| 183.1与192.1的余量结论 | $[r,h]=[r,s]=[r,c]=0$、$z_{\rm e}\circ r=0$ 全部保持；192.1的首强度取 $R=1$ | 当前元组没有总 $D$，不供应全部 $D(Rh,x)$；完整原候选的整条行由201.1承担，不把两个纯分支相加 |
| 184.1、192.2、198.1的已付纯分支 | 111.3的 $z_{\rm e},z_{\rm o}$ 同时非零，故两个纯分支的前件均不满足 | 198.1已将纯偶分支也扩至任意实首强度；两种纯分支均直接复用，不作为新结论 |
| 197.1的全态锐平方界 | $[h,r]=[c,r]=0$ 及准确全态固定P2均成立，但111.4给 $z\circ r=z_{\rm o}\circ r\ne0$ | 该界还要求 $z\circ r=0$；前件齐备时，统一二表误差 $\epsilon_{\rm P2}\ge0$ 已给 $\|r\|^2\le\epsilon_{\rm P2}$，准确P2即排零；$\epsilon_{\rm P2}$ 不同于110.4的固定系数 $\varepsilon$ |
| 198.1的任意实首强度单项判据 | 固定元组只对应 $R=1$ 的必要关系，奇交叉项由111.4明确非零 | 在196.1的全部原合同下，原行身份 $D(Rh,x)=RiQhz$ 等价于 $z_{\rm o}\circ r_R=0$；201.1已在实际反射分支生产后者，不再留下该分支的交叉生产或其后的排零缺口 |
| 201.1的完整混合反射行 | 若同一元组来自196.1、182.1–182.2及199.2全部七项来源合同的完整原实现，且实际 $j=D(h,e)$ 为111.1、$g=D(h,x)$，则取 $R=1,Q=I_8$ 必须有 $g=ihz$，与 $r\ne0$ 冲突 | 201.1覆盖全部实 $R,\lambda,\nu$ 和任意原 $h$-奇 $z$，不限制其 $s$-奇偶；其现有扩展谱混合响应卷27.1在同一完整前件下进一步覆盖全部实 $R,\mu,\lambda,\nu$、输入 $c=\mu u+\lambda h+\nu s$ 及任意原 $h$-奇 $z$。完整原A1–A3、准确锥、全部正评价、全部P2/PB及实际框架均不可省略；一般 $h$-交换背景和任意首标签仍不在这些结论内 |

因此110.2反驳的准确推断是：仅凭110.1的这些共同必要关系和固定对的
全部标量P2，就能迫使同一 $r=0$。它没有反驳完整原A1–A3/P2/PB，
也没有给出总响应反模型。特别，“全部正泛函”没有弥补“只给一对输入”
与“所有原PB调用共用一张旧表”之间的量词差别。
中央201.1正是利用后一种共同关系排除这份元组的实际反射扩充；必要
条件的反例与完整原条件下的排除相容。

**定义 115.2（共同外值约束与实际已付的供应）。** 若110.1中的候选真来自
中央196.1及182.1–182.2的同一个完整原 $D$ 和实际框架，且
$g=D(h,x)$、$\tau=D(h,z)$，则必须同时
保留至少以下两类准确调用。第一类为中央183.2–183.3：已付
$D(h,k)=0$ 后，原 $\operatorname{PB}(h,x,k)$ 要求同一个实际外值为

$$
D(z+g,2k)=-2x\circ g+2z\circ c,
\qquad D(2k,z+g)=2x\circ g-2z\circ c.
\tag{115.1}
$$

第二类交换演员，原 $\operatorname{PB}(x,h,0)$、原反对称性和零输入行给

$$
\boxed{D(h-g,k)-D(h+g,-k)=2h\circ g=2hr.}
\tag{115.2}
$$

同一 $g$ 必须既进入这些真实外层标签，又成为其右侧的荷；外层P2还须
对这些同一标签、同一旧外值及每个共同正读取成立。110.7没有为这些
外值选择答案，更未证明115.1–115.2及其他PB可同时实现。

一种可选的排除供应是：从其他已识别原行或有限原P2/PB网络，直接生产
115.2中两份实际外值相等。若有该项供应，115.2给 $hr=0$，再乘
$h$ 就有 $r=0$。这说明该联合等式足以排除余量，不把它作为新增前提，
也不把它当作201.1实际采用的生产步骤。对当前元组，115.2所要求的差明确为

$$
2hr=2\nu\varepsilon X\otimes Z\otimes I_2\ne0.
\tag{115.3}
$$

纯奇分支中，中央192.2能用第二框架 $H=hs$ 上的仿射交换零行使两份
外值各为零。混合时，111.3的偶分量为 $H$-奇，$h\pm g$ 不再全为
$H$-偶，不能照搬该消元。固定P2只限制每份输出的均值预算，没有生产
两份外值之间的这条等式。114.1提供另一种准确排除供应，但它是更强的
矩阵关系；把它作为独立供应使用时，其正性来源仍须另付，不能将它
当作原P2、二正性或CP。

实际已付的反射供应是中央201.1的共享输出两角机制。保持196.1的同一
原A1–A3、准确锥、全部正评价、全部P2和完整PB，以及182.1–182.2的
实际 $h,e,j=D(h,e),s,H,Q$ 及199.2全部七项来源合同。说明一般参数时，
记实际 $g_R=D(Rh,x)=RiQhz+r_R$。201.3–201.4对每个实偏移 $\alpha$ 调用
$\operatorname{PB}(Rh,x,Rk+\alpha u)$，使其实际正外值始终等于同一个
$K_R=-2x\circ g_R+2R^2z\circ c$，负外值由已付全单位零行归零。
对 $\sigma=\pm1$，取 $\alpha_\sigma=-2R(\lambda+\sigma\nu)$，同一
正外值的第二输入便在 $p_\sigma=(u+\sigma H)/2$ 角中平方预算为零。
两份原P2分别给 $p_\sigma K_Rp_\sigma=0$；201.6–201.7再对同一个 $K_R$
取 $H$-偶及 $h$-奇偶投影，生产 $cr_R=0$ 和 $z_{\rm o}\circ r_R=0$。
198.1连同197.1随即给 $r_R=0$。这一路先生产交叉零值，再消费谱排零，
没有先令115.2的两份外值相等，也没有使用旧 $D$ 的平移或线性。

因此若110.5的同一元组能成为上述完整原实现中的实际资料，保持111.1
的实际 $j=D(h,e)$、$Q=I_8$ 及 $g=D(h,x)$，201.1取 $R=1$ 就强迫
$g=ihz$、$r=0$，与110.6及111.4冲突。这是既有201.1的当前应用，
不构造这样的总 $D$。排除依据只要求该定理的完整前件，不要求原域为
全有限矩阵代数：其一般JC域可以不完备、无限维、不可分，且不填满
环境自伴部；同样不允许所列元组成为满足这些前件的实际反射网络。

另在整个原域恰为 $H_8(\mathbb C)$、所有原输入和全部原P2/PB均已供应，
并要求 $D(h,e)=j$ 的情形，已有
[配平主卷142.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)
直接排除任何这样的总扩充：全有限矩阵旧表识别及该框架取向迫使
$D(a,b)=i[a,b]/2$，从而 $D(h,x)=ihz$，与 $g=ihz+r$、$r\ne0$ 冲突。
这是独立的有限全表消费者，不是从单对110.2重证它，也不将142.1移给
一般JC原域；上述一般反射排除由201.1自己的前件和证明承担。
中央定义181.2中的显示式181.1是允许任意原 $h$-交换 $c$ 的一般生产
目标，仍未解，也未被这里反驳；201.1支付其中
$c=\lambda h+\nu s$ 的实际反射分支，现有谱混合响应卷27.1在同一
准确前件下把它扩展到 $c=\mu u+\lambda h+\nu s$，所以额外任意单位偏置
的混合行已在该准确范围内覆盖；一般 $h$-交换背景和任意首标签仍须各自原桥。原多项式卷85.1的一般有限商纤维目标及
一般有限商分离保留各自准确范围，不由这一实际反射结论代替。

## 116. 必要对边界、已付反射行与全部量子消费者

**定义 116.1（文献用途与数学新意边界）。** Lagrange多项式投影、三角
不等式、正泛函分离、实二次式配方和Schur补因子分解都是成熟中间工具。
112.7–112.10把非正规投影的范数实际放入估计，未引用一个把实谱误当作
正规谱的逆范数公式。110.2的承重差量限于所列同一混合元组的全部参数
统一正性、非零奇重叠及其与原余量接口的接线，归为
$\texttt{repo-derived}$ 的纸面构造；不是单独把这些成熟工具改名为结果。
115对中央201.1的反射排除只作当前应用衔接，不把该已付混合行、
197.1–198.1或两个纯分支重复计作新数学。

乘积向量正性与算子正性的区别已有经典文献：Lewenstein、Kraus、Cirac、
Horodecki，[*Optimization of entanglement witnesses*](https://arxiv.org/html/quant-ph/0005014v3)，
Phys. Rev. A **62**, 052310，§II的条件(I)要求所有乘积向量非负，
条件(II)仍容许负特征值，条件(III)另作迹归一。114.1–114.8对应其前两个
数学性质；本文不使用其迹归一、最优性或探测能力定理。
这一区别本身属于 $\texttt{literature-attested}$ 的成熟先例。
本构造另须同时保持110.1的框架、双偶余量、零偶重叠和固定原输入的P2，
这些附加对应由111–113逐项证明，不由一般纠缠见证的存在替代。
没有历史优先权、文献穷尽或完整量子起源的主张。

本组亦不重复96–102的全演员端点图分类。那里固定的是合法完整标准
多项式模型，研究有限PB端点链不能供应哪类精确原标签返回；这里没有
总 $D$，研究列出的必要余量关系与全部固定P2不能供应哪条排零结论。
两种方法边界涉及不同关系，不能互相升级为完整原候选的反模型。
原多项式卷80–88的全部实际二阶角及小连接行、102–108在分离截面域上
的同旧表识别与连续取向保持已付范围；它们没有预先给一般旧 $D$ 正则性。

本续卷已发表103.2是在同一多项式原域的一份总响应中联合保持单位第三标签、
圈外演员PB和固定小角接口的结果；其实际重复第三标签PB在107.6失败，
108.2排除了非平凡实际反射框架。本组110.2具有实际矩阵反射元，却只供应
必要输入输出元组和固定P2，没有总 $D$。在196.1、182.1–182.2全部前件
及199.2全部七项来源合同下，中央201.1已排除它成为实际反射网络，
范围包括该定理的一般JC原域；
115.2所引配平主卷142.1另在完整 $H_8(\mathbb C)$ 原域识别整张旧表，
保留为独立有限消费者。103.2与110.2分别界定联合检验族与固定对的
充分性，前者不替代本组的混合余量结论，二者均不否定完整原候选。

**定义 116.2（量子公理的同源来源保持）。** 102.2、
[中央186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)
及[原多项式卷87.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)
的全部七项合同继续合取，数量、来源和量词均不缩减。110.5只供应一份
数学固定元组，114.1只标出额外联合关系的强度，不供应下列任何物理来源。

1. 复Hilbert、可观察量与相干叠加仍要求唯一原 $\Omega/\mathrm{native}$、
   全词同一 $K/J/q$、parent/ready、可取得原标签、合法控制和实际相干
   准备；一般同旧表全域复乘法仍须生产。数学 $\mathbb C^8$、矩阵张量因子
   和三轴不产生原全 $B(H)$ 的可取得像、原完备性或准备。
2. 态、效果与Born仍绑定原评价、原事件、准确效果区间、全部实际完整
   菜单及接受归属；全部零／不等／次归一质量、中心经典权、不等维及
   静默块保留，只归一该菜单严格正总质量。原抽签、共同根、mark、
   $\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、P9、独立
   $W_e$、全部中间切口及固定支持全质量保持。数学正泛函不供应实际菜单
   齐备、正规物理态或密度算子解释。
3. native与张量仍须同一个实际非零相关联合、忠实同向交换局部腿、
   共同实现、联合生成与分离、所需重数、全部相关输入、中央对、经典及
   不等维块和递归同源参考。三个数学二阶因子没有赋予它们物理子系统
   身份，相同边缘、分别可达及相同取向均不代替这份联合来源。
4. typed CP、Kraus接线及参考仍要求原未归一回溯、合法typed前接后接、
   反变合法复合、typed分区、全未来自然性和箭头商下降。参考覆盖整台
   实际箭头的系统、整个环境、全部成功／失败／细记录／port／post-port
   输出及每个输出每个仍合法未来；三实际投影、各支持内补、共同真实
   支持的准确运输、全部相关正输入的intertwining与夹界、每个所需有限
   递归深度和累计支持完整链保持。114.1未供应该整台箭头的二正性或CP。
5. 仪器、TP、更新和Lüders仍要求完整typed菜单、原接受端、整台环境与
   全部上述输出未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及
   接受条件。TP另需完整单位分区，Lüders另需同一完整输出校准的像内射线
   保持。只归一正输出质量，零分支保留；密度、迹类和Kraus公式仍限合格
   有限全矩阵域，或另付正常物理表示、指定前对偶及所需收敛的范围。
6. 历史、未来、真实返回与CountRead保留全部合法顺序／自适应／并行
   历史，每份输出每个合法未来、整个环境与细记录泄漏、停止／拒绝／
   销毁、真正遗忘、同数两侧及同数逆向真实返回。读后同一完整活动输入、
   负提升两条活路的分别控制和相干聚合、原完整菜单接线、精确正生成
   $B$ 与闭正生成 $B_{\rm cl}$ 的区别不省略。无限／非离散记录、可数可加、
   正常性及指定前对偶仍各须来源；矩阵相同不决定程序、读取次序、原
   $q$ 零集及AC方向。
7. 动力、物理钟、能量和共同尺度仍需同一旧全域乘法、保持可能不完备
   原域的流、实际相位与门序列、可逆一参数群、物理钟、所需强连续酉
   实现、一般无界生成元定义域、Hamiltonian能量解释、共同作用量、共同
   正 $\hbar$ 与共同仪器。原 $\sigma,t_0,d$、固定域、resolvent及
   $3s+r\le1$ 预算保留原义。110.4的 $t$ 是精确矩阵系数，110.5的
   $\lambda,\nu$ 是数学输入参数，都不是物理时间、控制成本或钟能量。

以上七项仍针对同一原世界和全部原历史未来，未由有限矩阵例子替代。
中央201.1已付实际反射分支的全部混合行，现有谱混合响应卷27.1在同一
196.1、182.1–182.2及199.2全部前件下进一步覆盖全部实 $R,\mu,\lambda,\nu$
与任意原 $h$-奇 $z$ 的 $c=\mu u+\lambda h+\nu s$ 混合行；额外任意单位偏置
因此不再列为该分支的未付项。中央定义181.2所列任意 $h$-交换背景的一般目标、
任意首标签、一般旧双线性、原R、全部有限旧复Gram、同一旧结合乘法及原完成运输
仍须各自前件。原多项式有限商纤维和分离边界另守其原范围，固定P2的
充分性失败不否定完整候选，也没有减少其独立公理数。本组结论属于
纸面定义与证明，不具有内核认证。

## 117. 固定对泄漏与共享输出两角排零的完整图景

**定义 117.1（标量可见与共同关系可见的区别）。** 可以把这份比较想成
同一物体上的两扇窗口：每扇窗口都用同一把二元刻度尺，反射再把横向
联系分成保留方向与跨侧方向。余量既不改变原轴的反射，也不改变第二次
反射；保留方向与它的对称乘积已经完全抵消，但跨侧方向还留下一份明确
非零联系。若只看这一对输入，哪怕允许所有数学态、所有质量和所有标量
斜率，两扇窗口最薄弱的位置仍彼此错开：当一个块接近零，另一个块离它
有统一的根间距；代数投影的范数把非正规倾斜的代价也计入后，一份固定
而非随态变化的微小余量仍能通过所有标量预算。这不是少测了某个态，
而是这些读取始终把两条输出腿系在同一个向量和同一组标量上。让两腿
分别携带不同向量，114.8立即出现负方向；这样一张联合算子表的正性
是更强关系，其来源须另付，不能免费叫作原P2或CP。完整原PB则已有
另一条修补：在196.1的同一完整原候选及182.1–182.2的实际反射框架中，
保持199.2全部七项来源合同，中央201.1移动第三标签的单位偏移，让
两份不同接法必须读回同一输出。第一种接法在一个角中没有第二平方
预算，第二种接法在另一个角中也没有；同一输出的两角因而都为零，
再由原轴的奇偶区别迫使跨侧联系与余量的对称乘积为零。
197.1–198.1随即排除整个余量，两个反射成分混在一份输入中也不能逃过。
因此110.2的固定对泄漏仍成立，但不能扩成满足
这些完整原前件的实际反射网络；这项排除不限于有限全矩阵域，也没有
把两种纯输入响应相加。修补覆盖任意实首强度及全部
$c=\lambda h+\nu s$、任意原 $h$-奇横向输入；现有谱混合响应卷27.1在同一
完整前件下进一步覆盖带额外单位偏置的 $c=\mu u+\lambda h+\nu s$ 混合行；一般 $h$-交换背景、
任意首标签和全域双线性、有限旧复Gram、
原R、旧乘法与完成运输仍各有未付桥梁，原多项式有限商问题也另守
其范围。三份数学二元因子不生成真实相关系统；这条已付反射行同样
不供应二正性或CP的物理来源、实际Born菜单、整台仪器和环境全部输出、
递归参考、全部历史未来与真实返回、计数或物理钟能量。完整量子起源
继续保持116.2全部七项同源合同与这些更广的未解决范围。

## 追加锚（本行以下为增补区）

## 118. 任意原偶背景、第一实际框架与同一余量

**定义 118.1（完整原条件与引用范围）。** 以下称[《中央响应平方与径向一致续卷》](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)为中央续卷，称[《原多项式零响应与 Cayley 原域边界》](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)为原多项式卷，称[《配平三角的共同取向与秩一响应续卷》](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)为配平卷，称[《谱混合响应与直接窗口边界》](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md)为谱混合卷。数学前件取中央续卷161.1、173.1–173.2的同一原 $(E,C,u,N,\mathcal P,S,D)$ 及第一实际框架，准确如下。

$E$ 是实 Archimedean 序单位空间；原正实线性评价族 $\mathcal P$ 分离元素并准确决定锥，全部原评价及其零、不等、次归一质量保留：

$$
C=\{a\in E:\gamma(a)\ge0\text{ 对每个 }\gamma\in\mathcal P\},
\qquad m_\gamma=\gamma(u)\ge0.
$$

$S,D:E^2\to E$ 始终是同一原总映射。A1保留每对原实标签的两条实际有向 Hermitian 二表正性；A2保留 $(a+b,a,b)$ 及全部排列的实际实部三表在整个 $\mathbb R^3$ 上半正定及相应 $(1,-1,-1)$ 零二次值；A3保留 $S(u,u)=u$ 及同一个固定有理 $0<\vartheta_0\le1$ 上的 $0\le v\le\vartheta_0u\Rightarrow S(v,v)\le v$。沿既有忠实、含单位、等距且准确保锥的稠密实 Jordan 包含，记

$$
\begin{gathered}
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E^{\|\cdot\|}=X,\qquad \mathcal A=C^*(X),\\
S(a,b)=a\circ b=(ab+ba)/2,\qquad
C=E\cap\mathcal A_+,\qquad N=\|\cdot\||_E.
\end{gathered}
\tag{118.1}
$$

$X$ 是含单位JC代数；$E$ 可以不完备、无限维、不可分，不要求 $X=\mathcal A_{\rm sa}$。唯一使用的实际框架为

$$
\begin{gathered}
h,e,j=D(h,e)\in E,\qquad h^2=e^2=j^2=u,\\
h\circ e=h\circ j=e\circ j=0,\qquad
Q=ihej\in Z(\mathcal A),\quad Q^*=Q,\quad Q^2=u.
\end{gathered}
\tag{118.2}
$$

$Q$ 是辅助元，不要求属于 $E$。不另给实际反射 $s$ 或第二框架，不预付旧 $D$ 的一般可加、齐次、连续、可测、单位平移、协变、商下降或完成延拓。全部P2/PB取定义118.2，七项物理来源合同则逐项完整取定义122.1的精确引用。

**定义 118.2（全部原二表与完整配平）。** P2及PB完整取配平卷128.1–128.2的 (128.3)–(128.6)，输入及评价量词均不缩减。特别，对每个原 $a,b,q\in E$，

$$
\begin{gathered}
v=D(a,b)-a\circ q,\qquad w=a\circ b+D(a,q),\\
D(b+v,q+w)-D(b-v,q-w)=-2b\circ v-2q\circ w.
\end{gathered}
\tag{118.3}
$$

每个数学正实线性泛函 $\phi:E\to\mathbb R$ 均可读取同一张原表，并满足

$$
|\phi D(a,b)|^2
\le B_\phi(a,b):=\phi(a^2)\phi(b^2)-\phi(a\circ b)^2.
\tag{118.4}
$$

合法性直接取配平卷129.1：固定两个复数系数后，原 Hermitian 二表的二次型是 $E$ 中的一个元素，全部原评价读它非负，准确锥便使它属于 $C$，所以每个数学正泛函也读它非负。传递的是同一张表的正性；不把原评价族换成新准备族。环境态的限制、子代数态的正延拓及 $\phi(a)=\omega(rar)$ 都如此读取；质量不作归一，左端始终是输出均值的平方。

**定义 118.3（任意背景与原固定值）。** 任取原 $c,z\in E$ 满足 $[h,c]=0$、$hz=-zh$，置 $x=c+z$。等价地，对任意原 $x$，只用保持 $E$ 的有限 Jordan 算子作分解，并对每个实 $R$ 固定同一个实际输出与余量：

$$
\begin{gathered}
L_a y=a\circ y,\qquad U_h=2L_h^2-I,\quad U_hy=hyh,\quad
P_h^\pm=(I\pm U_h)/2,\\
c=P_h^+x,\quad z=P_h^-x,\quad k=h\circ x=hc,\\
T=[L_j,L_e],\quad t=Tz=iQhz=D(h,z),\\
g=D(Rh,x),\qquad r=g-Rt.
\end{gathered}
\tag{118.5}
$$

$c,z,k,t,g,r$ 全在原 $E$。中央续卷161.2、163.1和173.2给

$$
\begin{gathered}
P_h^-D(\alpha u+\beta h,y)=\beta T P_h^-y
\quad(\alpha,\beta\in\mathbb R,\ y\in E),\\
[h,c]=[h,r]=0,\quad hz=-zh,\quad ht=-th,\quad
z\circ t=0,\quad k^2=c^2.
\end{gathered}
\tag{118.6}
$$

这没有把 $D(Rh,x)$ 拆成两个旧响应。中央续卷161.5另给全单位零行与原反对称性；P2给全部比例零值 $D(a,\lambda a)=D(a,0)=0$。

本处还复用中央续卷189–191的整个证明，在以下准确前件包中取得

$$
[h,y]=0\quad\Longrightarrow\quad D(\alpha u+\beta h,y)=0
\qquad(\alpha,\beta\in\mathbb R,\ y\in E).
\tag{118.7}
$$

所需前件为 (118.1) 的含单位稠密原 Jordan 域、准确锥和全部正读取，(118.3)–(118.4) 的同一总 $D$、全部P2/PB、反对称性和比例零值，以及 (118.6) 对全部仿射首槽和原第二输入的投影公式。证明中的 $p=(u\pm h)/2$ 和 $\mathcal U_p=2L_p^2-L_p$ 均保持原域；$\kappa(v)=pvp$ 保正，且仅当 $v$ 为 $h$-偶时使用 $\kappa(v^2)=(\kappa v)^2$、$\kappa(v\circ w)=\kappa v\circ\kappa w$。189.6的仿射输出偶性由 (118.6) 供应；190.2的有界网由原多项式卷4.8–4.15及中央174.8–174.17所列JB支撑、Peirce和Kaplansky工具及原域稠密性供应，每项是原偶有符号平方；190.4只估计固定输出的读取。191.2–191.4取原多项式卷4.17的同一两张固定表计算；191.5–191.7对最后可能非偶的 $k_0$ 只用偶因子的压缩乘法和第二平方零预算。这些前件已全部包含于定义118.1–118.3，不使用 $s,H$ 或182.2的第二框架。因此这里复用189–191的证明在第一框架下所得的 (118.7)，不是直接删去189.1陈述所援引的188.1、182.1前件；一般角压缩仍不是全域同态，亦未给未知 $D$ 取极限。

## 119. 一项原 Jordan 二元关系的充要判据

**定理 119.1（任意偶背景与实际余量的交换判据）。** 在定义118.1–118.3的完整原条件下，对每个实 $R$、每个原偶 $c$ 和原奇 $z$ 及其同一固定 $x,g,r$，准确有

$$
\boxed{
\begin{gathered}
c^2\circ r=c\circ(c\circ r)
\quad\Longleftrightarrow\quad[c,r]=0
\quad\Longleftrightarrow\quad cr=0\\
\Longleftrightarrow\quad r=0
\quad\Longleftrightarrow\quad D(Rh,c+z)=RiQhz.
\end{gathered}}
\tag{119.1}
$$

第一项只含原有限 Jordan 二元关系；乘积和交换子在同一忠实环境计算。充分方向只有这一项待生产的二元条件；不要求 $z\circ r=0$、$[c,z]=0$、$c$ 中央、可逆或有限谱，也不要求原域完备。本定理不从原公理无条件生产一般 $[c,r]=0$。

证明。先说明第一项与环境交换的等价，直接复用原多项式卷 (15.8)–(15.10) 的成熟有界自伴算子论证，参数取 $(a,b)=(c,r)$。已知乘法给

$$
4\{c^2\circ r-c\circ(c\circ r)\}=[c,[c,r]].
\tag{119.1a}
$$

若左端为零，在 $\mathcal A$ 中令 $\delta(y)=i[c,y]$；这是有界导子，$\delta^2(r)=0$。范数收敛的指数级数给

$$
e^{i\theta c}r e^{-i\theta c}
=e^{\theta\delta}(r)=r+i\theta[c,r]
\qquad(\theta\in\mathbb R).
\tag{119.1b}
$$

$c$ 自伴使左端范数恒为 $\|r\|$，故对每个非零实 $\theta$ 有 $\|[c,r]\|\le2\|r\|/|\theta|$；令 $|\theta|\to\infty$ 得 $[c,r]=0$。反向由 (119.1a) 直接成立。这只是既有成熟推论的应用，指数和参数仅属于辅助已知乘法，不是原标签、$D$ 输入或物理时间，不要求旧 $D$ 连续。

若原对象为零，全部等式直接成立。若 $R=0$，零输入P2及原评价分离给 $g=r=0$。以下设原对象非零且 $R\ne0$。保留同一个实际 $x,g,r$，对每个实 $\alpha$ 选择原第三标签 $q_\alpha=Rk+\alpha u=Rhc+\alpha u\in E$。(118.7) 给 $D(Rh,q_\alpha)=0$。完整PB取 $(a,b,q)=(Rh,x,q_\alpha)$，其位移及两份完整外层为

$$
\begin{gathered}
v_\alpha=g-R^2c-R\alpha h,\qquad w_\alpha=Rk,\\
A_\alpha=(1-R^2)c+z+g-R\alpha h,
\qquad B_\alpha=2Rk+\alpha u,\\
A_\alpha^-=(1+R^2)c+z-g+R\alpha h,
\qquad B_\alpha^-=\alpha u.
\end{gathered}
\tag{119.2}
$$

全单位零行及反对称性消去第二份实际外值 $D(A_\alpha^-,\alpha u)$。只展开已知 Jordan 乘法，用 $x\circ h=k$、$k^2=c^2$，得到

$$
\begin{aligned}
D(A_\alpha,B_\alpha)
&=-2x\circ(g-R^2c-R\alpha h)
  -2(Rk+\alpha u)\circ Rk\\
&=-2x\circ g+2R^2(x\circ c-k^2)
  +2R\alpha(x\circ h-k)\\
&=-2x\circ g+2R^2z\circ c=:K.
\end{aligned}
\tag{119.3}
$$

所以对全部实 $\alpha$，整个实际旧输出都是同一个 $K$。这段接线已见中央续卷 (201.3)–(201.4) 及谱混合卷 (27.3)–(27.4) 的 $\beta=0$，其计算只需 $[h,c]=0$，不需反射背景或 $[c,r]=0$。

现在假定 $[c,r]=0$。由 (118.6)，

$$
\mathcal B=C^*(u,h,c,r)\subset\mathcal A
\tag{119.4}
$$

是含同一单位的交换复 C* 子代数，不要求它是整个环境的中心。任取其字符 $\chi$，写

$$
\chi(h)=\epsilon\in\{1,-1\},\qquad
\chi(c)=a\in\mathbb R,\qquad \chi(r)=b\in\mathbb R.
$$

字符是 $\mathcal B$ 上归一正泛函。含单位 C* 子代数的态正延拓给环境态 $\phi$ 满足 $\phi|_{\mathcal B}=\chi$，其限制合法读取 (118.4)。在该态的 GNS 表示 $(\pi,\mathcal H_\phi,\xi)$ 中，$\|\xi\|=1$，对 $y=h,c,r$ 有

$$
\|\pi(y-\chi(y)u)\xi\|^2
=\chi\bigl((y-\chi(y)u)^2\bigr)=0.
\tag{119.5}
$$

所以 $\pi(h)\xi=\epsilon\xi$、$\pi(c)\xi=a\xi$、$\pi(r)\xi=b\xi$。这是辅助 GNS 向量关系，不要求原物理表示具有相应谱点的特征向量。在已经对全部实数成立的 (119.3) 中，选择有限实数

$$
\alpha_\chi=-2R\epsilon a.
\tag{119.6}
$$

因 $c$ 有界，其字符值 $a$ 是有限实数，故这是合法原标量偏移，$q_{\alpha_\chi}\in E$。由 $\pi(hc)\xi=\epsilon a\xi$，同一张实际外表满足

$$
\pi(B_{\alpha_\chi})\xi=0,\qquad
\phi(B_{\alpha_\chi}^2)=0,\qquad
\phi(A_{\alpha_\chi}\circ B_{\alpha_\chi})=0.
\tag{119.7}
$$

最后一式由自伴性及 GNS 内积给出。因此对这张原表应用P2，得

$$
|\phi(K)|^2
\le\phi(A_{\alpha_\chi}^2)\phi(B_{\alpha_\chi}^2)
     -\phi(A_{\alpha_\chi}\circ B_{\alpha_\chi})^2=0.
\tag{119.8}
$$

若自伴 $y$ 为 $h$-奇，$hyh=-y$ 及 $\pi(h)\xi=\epsilon\xi$ 给 $-\phi(y)=\phi(hyh)=\epsilon^2\phi(y)=\phi(y)$，故 $\phi(y)=0$。另一方面，由 $g=Rt+r$、$z\circ t=0$，(119.3) 准确展开为

$$
K=-2c\circ r-2R c\circ t-2z\circ r+2R^2z\circ c.
\tag{119.9}
$$

后三项全为 $h$-奇，故

$$
0=\phi(K)=-2\phi(c\circ r)
=-2\chi(cr)=-2ab.
\tag{119.10}
$$

对每个字符都如此；字符分离交换 C* 代数，遂给 $cr=0$。字符 $\chi$ 始终只读取 $\mathcal B$；可能不在其中的 $A_\alpha,K$ 一直由环境延拓态 $\phi$ 读取。

最后消费中央续卷176.1–176.3的原支撑机制，强度保持当前 $R$；谱混合卷 (27.10)–(27.11) 已写明其任意实强度版本。为明确一般 $c$ 下的参数对应，实际PB $(x,Rh,0)$ 用内值 $D(x,Rh)=-g$、$D(x,0)=0$，准确给

$$
D(Rh-g,Rk)-D(Rh+g,-Rk)=2Rhr.
\tag{119.11}
$$

两张实际表对同一个数学正读取 $\psi$ 用P2、三角不等式及 $(\sqrt A+\sqrt B)^2\le2(A+B)$，只丢掉非负交叉均值平方，得

$$
\begin{aligned}
4R^2|\psi(hr)|^2
&\le2R^2\psi(c^2)
  \{\psi((Rh-g)^2)+\psi((Rh+g)^2)\}\\
&=4R^2\psi(c^2)\{R^2\psi(u)+\psi(g^2)\}.
\end{aligned}
$$

只约去非零实数 $R$ 的显式平方，得到

$$
|\psi(hr)|^2
\le\psi(c^2)\{R^2\psi(u)+\psi(g^2)\}.
\tag{119.12}
$$

这一步对一般 $c,r$ 成立，不借旧 $D$ 的强度齐次。对任意环境归一态 $\omega$，取正实读取

$$
\psi(a)=\omega(rar)=\omega(\mathcal U_r(a)),\qquad
\mathcal U_r=2L_r^2-L_{r^2}.
$$

它在原准确锥上正，质量 $\omega(r^2)$ 可以为零，不除以它。$cr=0$ 给

$$
\psi(c^2)=\omega(rc^2r)=\omega((cr)^*(cr))=0,
\qquad \psi(hr)=\omega(hr^3).
\tag{119.13}
$$

所以所有环境态都读 $hr^3$ 为零。因 $[h,r]=0$ 且 $h,r$ 自伴，$hr^3$ 自伴；态分离得 $hr^3=0$。左乘 $h$ 得 $r^3=0$，进而 $r^4=0$，C*范数恒等式给 $\|r\|^4=\|r^4\|=0$，故 $r=0$。这一支撑结论只需 $cr=0$，无需另外假定交换。反向 $r=0\Rightarrow cr=0\Rightarrow[c,r]=0$，第二步由自伴性同时给 $rc=(cr)^*=0$；$r=0$ 与实际行恒等式按定义等价，完成证明。∎

全程没有除以 $c$、字符值 $a,b$ 或读取质量；零谱值、零支撑、零质量都在范围内，环境态不要求正常。谱、根、投影、逆及指数从未被补作物理标签或 $D$ 输入，也未对未知响应作极限操作。

## 120. 已有范围、成熟工具与新增承重

**定义 120.1（准确复用关系）。** 下列地址均指相应 canonical 理论正文的指定编号；不将成熟工具或已有原调用计为新数学。

| 既有地址 | 已有范围与119.1的关系 |
| --- | --- |
| 中央续卷174.1、175.1–175.2、176.1–176.3 | 174.1给整条 $h$-交换零行；175.1仍留横向平方预算；176.3已给 $cr=0\Longleftrightarrow r=0$。新增连接是由单项 $[c,r]=0$ 和共同输出族生产任意背景的 $cr=0$；原支撑直接复用，并在 (119.11)–(119.13) 保留当前强度。 |
| 中央续卷177.1、(177.10)–(177.14) | 条件自举另需 $[c,z]=0$、$c\circ r=0$；119.1不取该零重叠路线，不要求 $[c,z]=0$。 |
| 中央续卷179.1、静态卷5.7的该处应用 | 单位强度的 $[r,x]=0\Longleftrightarrow r=0$ 已付。$r,c$ 偶、$z$ 奇使 $[r,x]=0$ 同时要求 $[r,c]=[r,z]=0$；119.1只取 $[c,r]=0$，不重证标量铅笔定理。 |
| 中央续卷188.2、189–191；原多项式卷4.2、4.8–4.20 | (118.7)明确其整个证明实际使用的第一框架前件，不把189.1的较强陈述删前件后套用，不把一般角压缩或字符延拓当作响应商下降。 |
| 中央续卷197.1–198.1 | 固定二表锐界另需 $z\circ r=0$。119.1使用完整PB的其他实际表，不删除197.1前件，也不声称推广其误差稳定性。 |
| 中央续卷192.1、201.1、(201.3)–(201.7) | $c=\lambda h+\nu s$ 的实际反射分支已生产交换关系并识别原行；共同输出接线已付。119.1只将其后读取接到任意偶背景，不要求实际 $s$。 |
| 谱混合卷27.1、(27.3)–(27.11)、28.1 | $c=\mu u+\lambda h+\nu s$ 的交换生产及完整原行已付；任意强度支撑直接复用。字符读取代替有限背景角读取，但仍须一般 $[c,r]=0$。 |
| 谱混合卷30.1–32.1，尤其 (30.3)–(30.11) | 已覆盖全部 $c=\mu u+\lambda h+\nu s+\xi hs$、全部实 $R$ 和任意原奇 $z$，包括整角零背景：失效系数分支由同一支撑PB排零。该范围已生产 $[c,r]=0$ 并完整识别；119.1不重复四角定理。30.1未生产一般偶背景的交换关系。 |
| 谱混合卷33.1–35.1，尤其 (33.1)–(33.9) | 对任意有限原投影分割 $p_a$，$\sum_a p_a=u$、$[p_a,h]=[p_a,e]=0$，已识别全部 $c=\sum_a(\mu_a u+\lambda_a h)p_a$、全部实 $R$ 和任意原 $h$-奇 $z$；逐对实际反射先生产 $[c,r]=0$，共同输出角读取及同一支撑PB再给 $r=0$，包括零角、零值和重值。该有限共同分割结论直接复用，不重计为119.1的新内容；它未支付任意偶 $c$、连续谱或没有这份共同 $h,e$ 交换分割的情形，也未给旧 $D$ 连续运输。 |
| 谱混合卷24.1、(24.3)、25.1–26.1 | 固定二表可有 $[h,r]=[c,r]=0$、$r\ne0$，其中 $cr=I/16$。它没有总 $D$ 或完整PB族；共同实际输出及其全部外层P2才在 (119.3)–(119.10) 强迫 $cr=0$，两结论相容。 |
| 本卷110.1–117.1，尤其110.2、115.1–115.2 | 同一 $M_8$ 必要对保留 $[c,r]=0$、全部固定P2和非零余量，却没有总 $D$。119.1的条件性PB排除不反驳该固定对证明，也不反驳完整原候选；中央201.1及其已有扩展已排除其成为相应完整实际反射网络。 |
| 中央续卷180.1–180.3、181.1–181.2；原多项式卷51–79、102–108 | 指定多项式域、连续域及分离截面域的全表结论保持各自前件。119.1不要求该分离纤维、原谱函数闭合或输出唯一传播，不把那些指定域替换一般JC域。 |

本组承重增量归为 $\texttt{repo-derived}$：对全部原实偏移共享的同一 $K$，接到 $C^*(u,h,c,r)$ 的每个字符及其正延拓，生产任意偶背景的 $cr=0$，再消费已付原支撑。相对于表中指定来源，新增仅是任意背景的这一条件连接；谱混合卷33.1的有限共同分割中，交换关系及同一原行均已支付，不再重复计入；不作文献穷尽、历史优先权或外部开放问题解决的主张。

Gelfand字符分离、含单位子代数的态正延拓、GNS零方差向量关系、态分离及自伴幂零排除均为成熟工具，准确沿中央续卷181.1、185.3、199.1复用。态正延拓取其所引 Blackadar，[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，II.6.3.1；态分离取该处II.6.3.3、II.6.3.5，GNS零方差关系已在 (119.5) 直接展开。(119.1a)–(119.1b)只是原多项式卷 (15.8)–(15.10) 已有有界自伴推论的应用；该处所列 Kleinecke，*On operator commutators*，DOI [10.1090/S0002-9939-1957-0087914-4](https://doi.org/10.1090/S0002-9939-1957-0087914-4)，是成熟导子来源，不将内在Jordan表述或酉共轭单列为新结果。原多项式卷4.2与中央174、189–191的支撑、Peirce和逼近机制只作已付零行前置。

## 121. 原二元条件、有限三标签与共同读取几何

**定义 121.1（偏移量词与原标签边界）。** (119.3)先对全部实 $\alpha$ 成立，再选择字符 $\chi$、其环境延拓态及有限实数 $\alpha_\chi=-2R\chi(h)\chi(c)$。逻辑为

$$
\bigl[\forall\alpha\in\mathbb R,\ D(A_\alpha,B_\alpha)=K\bigr]
\quad\Longrightarrow\quad
\bigl[\forall\chi\in\widehat{\mathcal B},\ \chi(cr)=0\bigr].
\tag{121.1}
$$

每个字符使用一次实际三标签调用 $(Rh,x,Rhc+\alpha_\chi u)$，每份标签及其内外表达式均在原 $E$；另一次支撑调用 $(x,Rh,0)$ 读取同一实际余量。这不是整个依赖证明的调用成本，也不声称有覆盖全部字符的固定有限菜单。字符可有无限多个，每个仍只需一个有限原偏移；全称PB使这种逐字符选择成为合法实例化，而非随读取重选未知输出。

几何只需实际轴 $h$ 的偶奇分解：$c,r$ 保持两侧，$z,t$ 连接两侧。原条件 $c^2\circ r=c\circ(c\circ r)$ 说明“先用背景平方比较余量”与“连续两次用同一背景比较余量”一致；有界自伴环境使它准确等价于 $[c,r]=0$。因此可在一个辅助交换窗口共同读取 $h,c,r$ 为 $\epsilon,a,b$。移第三标签的单位分量，使外表第二输入在该GNS向量上平方预算为零，P2便迫使同一个 $K$ 的读取为零。尖锐 $h$ 读取消去奇连接，剩下 $ab=0$；支撑PB排除余量藏在背景零部位的可能。这里简化的是共同读取窗口，不是把整个世界压成二维，也未给有限物理状态数。

对任意 $c,z,R$，仍须从原关系生产这一项二元条件。119.1不减少完整A1–A3/P2/PB的独立条件数，不给一般首标签识别、全域旧双线性、全部有限旧复Gram、原换括号关系或完整旧复乘法。固定 $R$ 的判据也不单独给 $D(Rh,x)=R D(h,x)$；该比例还须同时识别同一个 $x$ 在单位强度的旧值。第一框架中的有限Jordan条件并不供应第二实际框架或任何新物理来源。

## 122. 七项同源合同与完整直观说明

**定义 122.1（完整来源引用与消费者对应）。** [中央续卷定义199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#199-来源几何与量子消费者的完整边界)的第1、2、3、4、5、6、7项逐项全文作为本组的合同组成部分，连同其完整援引的[定义194.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#194-新连接完整候选与量子消费者的范围)、[定义186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#186-七项原量子来源合同的准确消费者)及各项全部上游量词，均不缩减、不更换原世界。下表仅定位119.1的数学供应与合同接口，不代替这些完整原文。

| 量子消费者及精确合同地址 | 本判据的供应与仍须的来源 |
| --- | --- |
| 复Hilbert、可观测量、相干叠加：199.2第1项、194.2第1行、186.1及其全部上游 | 只条件性识别同一实际 $h$ 行；全域旧共同乘法、完成运输及实际可取得性、控制和相干准备继续守该完整合同。 |
| 原态、效果、全部质量、Born：199.2第2项、194.2第2行、186.2及其全部上游 | 数学正读取不增加准备；实际事件、接受归属及完整Born菜单仍由该合同供应，零质量不归一。 |
| native、真正相关联合、张量：199.2第3项、194.2第3行、186.3及其全部上游 | 交换读取窗口不供应实际相关联合、局部腿或递归同源参考；共同实现仍按完整合同取得。 |
| typed CP、Kraus及参考：199.2第4项、194.2第4行、186.4及其全部上游 | 态正延拓不是原箭头或CP；整台系统环境、全部输出及每个有限递归深度的合法接线仍须该完整合同。 |
| 仪器、TP、更新、Lüders：199.2第5项、194.2第5行、186.5及其全部上游 | P2及原支撑读取不供应完整仪器、遗忘、接受端或更新校准；正常物理表示、前对偶和所需收敛继续另付。 |
| 全部历史未来、真实返回、CountRead：199.2第6项、194.2第6行、186.6及其全部上游 | 逐字符数学读取不供应实际历史、泄漏控制、真遗忘或同数双向返回；无限非离散记录仍须原可数可加、正常性和前对偶来源。 |
| 动力、物理钟、能量、共同尺度：199.2第7项、194.2第7行、186.7及其全部上游 | 辅助 $e^{i\theta c}$ 不供应保持原域的物理流、钟、无界生成元域、能量或共同正 $\hbar$；完整动力合同原样保留。 |

**定义 122.2（完整中文直观说明）。** 原来的世界和比较表始终是一份：两两有向比较要有正预算，相加三角和单位小窗保持原样，任意三个原标签的正反重接必须配平。固定一根已经真实存在的比较轴，把任意输入分成保持轴两侧的背景和连接两侧的横向部分；已认清横向输出后，未知的是同一旧输出剩下的一份偶余量。所需的一项二元关系可以完全用原比较写出：先以背景的平方比较余量，等于连续两次以同一背景比较余量。在现有有界自伴环境中，这准确等价于背景与余量交换；证明只借数学酉共轭保持范数，不把指数当成实际控制或物理钟。只要这项关系成立，就不用再要求背景与横向输入交换，或横向输入与余量的对称乘积先为零。给第三标签加上任意有限实数的单位偏移，原配平会让一整族不同外表共用完全相同的输出，不能为不同读法另选答案。背景和余量交换，便能在一个数学窗口同时看清它们的数值；针对每个这样的读法选一个实际标量偏移，就使外表第二输入没有平方预算，正表迫使共同输出的读取为零。横向连接在尖锐轴读取下没有均值，留下的恰是背景数值与余量数值的乘积，故每个读法都要求该乘积为零。即使背景不可逆、有零部位或连续谱，余量也不能藏在那里：把同一输入和轴再用零第三标签重接，原支撑预算会把这份余量读成自伴幂零元，而它只能为零。每个读法只用有限原标签，没有把谱点、根或新投影当成物理输入，也没有说无限多个读法合成固定有限菜单。简化的是把任意偶背景这条实际混合行的识别，归约为背景与同一余量的一项原Jordan二元关系；该关系的一般原生产仍待完成。已有完整四角、有限共同分割背景行及固定对反例各保持原范围，全部实际量子来源仍逐项遵守122.1完整援引的中央199.2及其上游合同。

## 追加锚（本行以下为增补区）

## 123. 同一总映射的全部自作用层级与原乘积铅笔

**定义 123.1（既有总表上的有限自作用）。** 对每个整数 $m\ge2$、$n=2m$，完全沿用103.1–103.3的同一原 $E_n,C_n,u,N$、全部原正评价及其全部非负质量、同一 $F,G,\mathcal S,\mathcal L$ 和同一总映射 $\widetilde D$。不重选轨道、原域或响应值。记

$$
L_A X=A\circ X,\qquad
\mathcal Z_n=E_n\cap Z(\mathcal A_n),\qquad
P(s)=\sum_{j=0}^{d}p_js^j,\quad
Q(s)=\sum_{k=1}^{\ell}q_ks^k,
\qquad p_j,q_k\in\mathbb R.
$$

$P,Q$ 是任意有限实多项式，$Q(0)=0$；零多项式包括在内，次数没有共同上界。$P(A)$ 和 $Q(L_A)B$ 只用有限原Jordan表达式，仍属于 $E_n$。$P(A)$ 的幂也可在103.1的已知比较代数中计算；没有以函数演算补入原标签。每个 $Z\in\mathcal Z_n$ 必须本来就是原元素；不将任意完成中的中央函数加入输入。

**定理 123.2（全部自作用与实际原乘积铅笔的联合不足）。** 在123.1的每个原域上，103.3的同一份 $\widetilde D$ 除同时保留103.2的整个联合子系统外，还同时满足

$$
\boxed{\widetilde D\bigl(A,Q(L_A)B+P(A)\bigr)
       =Q(L_A)\widetilde D(A,B)}
\qquad(A,B\in E_n),
\tag{123.1}
$$

以及全部实际调用

$$
\boxed{\operatorname{PB}_{\widetilde D}
       \bigl(A;B,\tau(A\circ B)+Z\bigr)}
\qquad(A,B\in E_n,\ \tau\in\mathbb R,\ Z\in\mathcal Z_n).
\tag{123.2}
$$

两式对所有上述多项式和参数在同一张总表上共同成立。尽管如此，令
$\delta_a(b,c)=\widetilde D(a,b+c)-\widetilde D(a,b)-\widetilde D(a,c)$、
$K_yv=v\circ y^2-y\circ(v\circ y)$，仍有 $K_F\delta_F(G,G)\ne0$。
因此103.2加上整个123.1及整个123.2，仍不蕴涵所有原 $a,b,c,y$ 的目标
$K_y\delta_a(b,c)=0$。这里检验的是这个明确联合子系统，不将其替换为完整原PB。

证明先核对123.1。若 $A\notin\mathcal L$，其整行 $\widetilde D(A,\cdot)$ 准确等于已知标准行 $D_*(A,\cdot)$，包括改变后的第二输入。只在这条标准行中使用线性与已知乘法：对每个原 $X$，

$$
D_*(A,L_AX)=\frac i4[A^2,X]
           =L_AD_*(A,X),\qquad D_*(A,P(A))=0.
\tag{123.3}
$$

逐次应用123.3，再按有限多项式相加，便得123.1。没有展开一般未知原响应。

若 $A\in\mathcal L$，写 $A=\alpha F+\beta G$、$\alpha^2+\beta^2=1$。105.2的Clifford乘法给

$$
A^2=(4\alpha^2+\beta^2)t^2u\in Z(\mathcal A_n),\qquad
[A,L_AX]=\tfrac12[A^2,X]=0,
\qquad L_AD_*(A,X)=0.
\tag{123.4}
$$

同一 $\widetilde D(A,B)$ 在每个实际输入对上只是 $D_*(A,B)$ 的一个正负号，故 $L_A\widetilde D(A,B)=0$。于是 $Q(0)=0$ 使123.1右端为零。对每个 $k\ge1$，$L_A^kB$ 与 $A$ 交换；$P(A)$ 也与 $A$ 交换。故第二输入 $Q(L_A)B+P(A)$ 与 $A$ 交换，103.5的完整零集使左端也为零。这覆盖修改行里的全部第二输入，不要求该第二输入仍在轨道上。123.1得证，特别给出

$$
\widetilde D(A,A\circ B+\lambda u)
       =A\circ\widetilde D(A,B)
\qquad(A,B\in E_n,\ \lambda\in\mathbb R).
\tag{123.5}
$$

123.2的全部实际内外层及非零检测器分别在124、125完成。

## 124. 原乘积铅笔的标准内值与修改内值共同闭合

**定理123.2的证明：全部实际铅笔。** 固定任意原 $A,B$、实 $\tau$ 及原中央 $Z\in\mathcal Z_n$，始终使用同一组实际值

$$
\begin{gathered}
p=A\circ B,\qquad C=\tau p+Z,\qquad
d=\widetilde D(A,B),\qquad e=\widetilde D(A,C),\qquad
v=d-A\circ C,\qquad w=p+e.
\end{gathered}
\tag{124.1}
$$

须证的恰是103.4的
$\widetilde D(B+v,C+w)-\widetilde D(B-v,C-w)=-2B\circ v-2C\circ w$；两份改变后的外调用仍是同一总表的真正调用。

先取 $(A,B)\notin\mathcal S$，故 $d=D_*(A,B)$。若 $A\notin\mathcal L$，整行标准，$e=D_*(A,C)$。若 $A\in\mathcal L$，123.4给
$[A,p]=0$，原中央 $Z$ 再给 $[A,C]=0$，所以
$e=0=D_*(A,C)$。这两个分支都准确满足103.2第3项的“两内值标准”前件，104.9–104.10遂支付该次实际PB。

更明确地，置 $T=B+iC$，并沿104.8记缺陷 $\Delta$。这时实际位移就是标准位移，实际复端点为 $T_\pm=(u\pm iA)T$，且

$$
\begin{aligned}
&\widetilde D(B+v,C+w)-\widetilde D(B-v,C-w)\\
&\quad=D_*(B+v,C+w)-D_*(B-v,C-w)
       +\Delta(T_+)-\Delta(T_-),\\
&\Delta(T_+)-\Delta(T_-)=0.
\end{aligned}
\tag{124.2}
$$

最后一式直接取自104.9。故实际外缺陷的差消失，标准PB给所需右端；并未把任一改变后的外调用单独认成标准值。

再取 $(A,B)\in\mathcal S$。直接消费105.2：对某个实 $\gamma$，

$$
p=\gamma t^2u,\qquad d=\pm2t^2W,\qquad
B\circ d=0.
\tag{124.3}
$$

所以 $C=\tau p+Z$ 本身中央，$e=0$，实际 $w=p$，两份外层第二标签准确为 $C+p$、$C-p$。它们都是原中央元素，故两份实际外响应各自为零。右端只展开已知Jordan乘法，并利用中央乘法的结合性，得到

$$
\begin{aligned}
-2B\circ v-2C\circ w
 &=-2B\circ d+2B\circ(A\circ C)-2C\circ p\\
 &=0+2C\circ(A\circ B)-2C\circ p=0.
\end{aligned}
\tag{124.4}
$$

这证明修改内值的全部分支，而不借用标准内值结论。两个情形穷尽所有原 $A,B$；任意实 $\tau$、$\tau=0$、任意原中央 $Z$ 和全部退化输入均已包括。单位第三标签是其中 $\tau=0,Z=\lambda u$ 的子族。两族123.1、123.2均由既有103.3的同一总映射履行。

## 125. 自作用的核、原加性检测器与完整配平的分界

**定理123.2的证明：联合子系统的消费者。** 直接消费103.7及107.3–107.4的同一原缺陷，不重造反模型。它满足

$$
\begin{gathered}
\delta:=\delta_F(G,G)=-8t^2W,\qquad L_F\delta=0,\\
K_F\delta=\delta\circ F^2-F\circ(\delta\circ F)
        =[L_\delta,L_F]F=-32t^4W\ne0.
\end{gathered}
\tag{125.1}
$$

123.1在修改行上通过 $L_A$ 消去了响应，却不能把 $L_F$ 的核当成 $K_F$ 的核。103.2与123.1–123.2既已在同一个总映射上联合成立，125.1便严格否定它们对全原域检测器目标的蕴涵。这是一项整个联合类的不足性，与所取有限多项式次数或其中调用的有限次数无关。

完整PB仍有这组铅笔之外的信息。107.5–107.7已经给同一个实际重复标签调用 $\operatorname{PB}_{\widetilde D}(F;G,F)$：$p=F\circ G=0$、$d=2t^2W$、$e=0$，实际 $v=d-F^2$、$w=0$；两份实际外层均在 $\mathcal S$ 外，其值准确为

$$
\begin{aligned}
\widetilde D(G+v,F)&=2t^2W-4t^3V,\\
\widetilde D(G-v,F)&=2t^2W+4t^3V.
\end{aligned}
\tag{125.2}
$$

其差为 $-8t^3V$，而PB要求 $+8t^3V$。这里 $p=0$ 使123.2中所有第三标签都只能为原中央 $Z$；$F$ 非中央，因为 $[F,G]=4it^2W\ne0$。所以这份重复标签调用确实在123.2类外。107.7之后的同一质量一正读取将元素两边读成 $-8,+8$，将原平方两边读成 $9,41$；没有混合不同读取的最优值。这仍是旧的完整PB失败，不是完整候选的反模型。

层级的零常数项限制也有准确边界。若允许 $Q\equiv2$，取 $P=0,A=F,B=G$，107.3给

$$
\widetilde D(F,2G)=-4t^2W
\ne 4t^2W=2\widetilde D(F,G).
\tag{125.3}
$$

故不能从123.1删掉 $Q(0)=0$ 而仍断言整个多项式族。中央第三标签铅笔也不供应一般响应平移：$(F,G+u)\notin\mathcal S$，因为第二输入在零点为 $u$，而轨道第二输入在零点均为零。因此

$$
\widetilde D(F,G+u)=-2t^2W
\ne 2t^2W=\widetilde D(F,G).
\tag{125.4}
$$

123.5只移动特定第二输入 $A\circ B$，不能改读成任意第二输入的中央平移不变性。联合不足性及上述边界均已成立，定理123.2证毕。∎

**定义 125.1（完整原候选中仍未支付的生产者）。** 对一般原 $E$，在不变的A1–A3、准确锥、全部原P2及完整原PB下，任意原 $A,B$ 和任意实 $\lambda$ 的
$D(A,A\circ B+\lambda u)=A\circ D(A,B)$ 在这里既未推出，也未反驳。123.5的总映射本来满足这条规律，却缺完整PB；它不裁决完整候选中的该中间规律。所有原 $a,b,c,y$ 的 $K_y\delta_a(b,c)=0$、$\mathsf C_{\rm add}$、一般原纤维一致性和旧 $D$ 的全域可加性生产者仍未解决。123.2仅排除只靠所列联合子系统完成检测器的路线；不排除使用其他完整PB调用的有限或依赖具体违规的网络，也不表明自作用规律与那些额外调用合用时没有价值。完整重构仍未完成。

**定义 125.2（已付表示、实际有限分割行、条件判据与原域对应）。** [《配平三角的共同取向与秩一响应续卷》240.1–240.2、248.1、250.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)已在同一完整原候选下支付整个自身JB完成 $X$ 的忠实、含单位、等距且锥准确JC包含，以及所有原Jordan正交对的旧响应正交与准确平方面积；这些前件不再作为一般候选中的欠项。该结论不要求 $E=\mathcal A_{\rm sa}$，也不识别一般旧 $D$ 为所选环境交换子。

[《谱混合响应与直接窗口边界》33.1–35.1](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md)在同一完整原候选、实际 $h,e,j=D(h,e)$ 框架、辅助中央自伴对合 $Q=ihej$ 及该卷31.1全部七项原来源合同下，已识别任意给定有限共同原投影分割上的完整原行。准确地，对任意 $m\ge1$ 及原分割

$$
\begin{gathered}
p_a\in E,\qquad p_a^2=p_a,\qquad p_ap_b=0\ (a\ne b),\qquad
\sum_{a=1}^m p_a=u,\qquad [p_a,h]=[p_a,e]=0,\\
c=\sum_{a=1}^m(\mu_a u+\lambda_a h)p_a,\qquad
\boxed{D(Rh,c+z)=R\,iQhz=R\,D(h,c+z)},
\end{gathered}
\tag{125.5}
$$

其中全部 $\mu_a,\lambda_a,R\in\mathbb R$ 任意，$z\in E$ 为任意原 $h$-奇元素 $hz=-zh$。零投影、零背景值、重值及退化联合角均包括。这里完整保留该卷30.1、31.1及[《中央响应平方与径向一致续卷》161.1–161.2、173.1、182.1–182.2、196.1、199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)的全部前件：原A1–A3、准确锥、全部原正评价与所有质量、全部原P2和完整PB，实际三轴均为原单位平方且两两Jordan正交，旧 $D$ 始终为同一总映射；七项合同及其上游量词不变。

该卷34.1还将任意有限个两两交换且与 $h,e$ 交换的原自伴反射 $s_1,\ldots,s_n$ 纳入125.5：它们的有限乘积给出共同原分割，零角允许，$n=0$ 取 $p=u$；由 $h,s_1,\ldots,s_n$ 生成的整个有限实交换代数中的背景和所有混合乘积系数均已覆盖。特别，该卷30.1–32.1的原四角结论仍作为 $p_\pm=(u\pm s)/2$ 的已付特例复用：

$$
D(Rh,\mu u+\lambda h+\nu s+\xi hs+z)=R\,iQhz
\qquad(R,\mu,\lambda,\nu,\xi\in\mathbb R,\ z\in E,\ hz=-zh),
\tag{125.6}
$$

其中 $s$ 是同一实际框架内与 $h,e$ 交换的原单位平方反射。共同有限原分割是125.5的明确分支资料，不能由此断言任意 $h$-交换背景都具有这种分割；没有这种表示的一般背景和任意首标签仍须原桥。所给任意有限共同原分割上的响应识别已支付；该结论不由有限逼近补入连续谱、极限响应、一般旧 $D$ 的线性或连续性，更不供应实际物理来源。

本卷118–122在定义118.1–118.3的同一完整原A1–A3、准确锥、全部原正评价、全部数学正读取及所有质量、全部P2和完整PB，以及第一实际 $h,e,j=D(h,e)$ 框架和同一辅助中央自伴对合 $Q=ihej$（不要求 $Q\in E$）下，已支付任意原 $h$-偶 $c$、原 $h$-奇 $z$ 和全部实 $R$ 的条件判据。
令 $g=D(Rh,c+z)$、$r=g-RiQhz$，定理119.1准确给出 $c^2\circ r=c\circ(c\circ r)\Longleftrightarrow[c,r]=0\Longleftrightarrow cr=0\Longleftrightarrow r=0\Longleftrightarrow D(Rh,c+z)=RiQhz$。
该判据不要求有限共同分割、旧 $D$ 连续性或额外物理来源；其结论及122.1的完整七项合同在此直接复用。
待付的是从原关系一般生产这一Jordan条件或等价交换关系，而非该条件成立后的原行识别；谱混合卷33.1–35.1已在125.5的有限共同分割范围生产原行。
123.2的约化联合子系统不足性与这个完整原条件下的已付充要判据各守其范围，不将后者的一般条件生产宣告完成。

103.3的原域由108.2没有非平凡实际单位平方框架，而且107.6缺完整PB，故125.5、125.6及定理119.1均没有在这里供应隐藏的实际演员，也不使103.3满足完整PB或解除123.2的联合子系统分界。103.2的系数 $H,V,W$ 不是该实际框架的原轴，不可用 $F/(2t)$ 添入轴来套用这些原行。

本卷110–117则固定另一份 $M_8(\mathbb C)$ 输入输出元组：它满足所列必要混合框架关系及同一固定输入对的全态、全质量P2，仍有非零余量，却没有总 $D$。114.1的整张算子二表正性更强且能排除该余量，其来源不能免费认作原P2、二正性或CP。在完整原候选与实际反射框架的全部前件下，115.2复用的中央201.1已排除该元组的实际实现，125.5不把这项排除重新列为未付；完整原域恰为 $H_8(\mathbb C)$ 时的旧全表识别另为该处的独立消费者。这个必要固定对的不足性与123.2在103.3同一总映射上对整个约化联合族的不足性分属不同量词域，二者均不是完整原候选的反模型。

**定义 125.3（完整来源量词与有限表达式边界）。** 109.1、122.1、[配平三角续卷250.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)及[中央续卷199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)的全部七项实际来源合同及其全部上游合同、对象与量词逐项合取保留，123.2不解除或缩小其中任何一项：同一原 $\Omega/\mathrm{native}$、全词 $K/J/q$ 与实际相干准备；原事件、效果、全部质量和实际完整Born菜单；同一个真实非零相关联合、局部腿、联合生成分离及递归同源参考；typed CP、Kraus、整台环境与每个所需有限递归深度的准确接线；完整仪器、单位分区、全部成功失败细记录、port及post-port输出、更新和Lüders；全部合法顺序、自适应、并行历史及每个输出每个仍合法未来、泄漏、停止拒绝销毁、真遗忘、同数两侧与真实逆向双向返回、完整CountRead和两条负提升活路；保持可能不完备原域的动力、真实控制、物理钟、生成元域、Hamiltonian能量、同一仪器与共同正 $\hbar$。所需可数可加、正常性、指定前对偶、原 $\sigma,t_0,d$、定义域、resolvent及 $3s+r\le1$ 的预算均保持各自原合同含义。

一般原目标仍允许不完备、无原子和不可分的 $E$，不以本例的偶数矩阵族替换。123.1–123.2只用原有限表达式，不用无限级数、解析响应演算或极限响应值；没有多项式次数的共同上限，也没有有限偶数维数的共同上限。零多项式、零输入、$\tau=0$、重合及重复标签、奇异平方和非可逆输入均包括且不作除法。125.1–125.4的诊断函数在 $t=0$ 归零，在 $t>0$ 非零；$W$ 只作系数，所用 $t^kW$ 的指数 $k\ge1$，均为原表达式。零原对象的结论平凡。每次比较沿用同一原正读取，全部零、不等及次归一质量保持，零质量不归一；没有由数学读取新增准备、控制、参考或物理尺度。这里不生产一般旧响应的齐次、连续、可测、商下降、共同取向、全有限复Gram、原R、兼容的旧结合乘法或完成运输，也不把原检测器 $K_y$ 作用后的表当作另一个满足PB的响应。

**定义 125.4（承重应用的来源）。** 123.2的整个联合类不足性归为 $\texttt{repo-derived}$。103.1–103.3供应原域与唯一总表，104.9–104.10供应标准内值下的实际外缺陷相消，105.2供应修改轨道的Clifford关系，103.7及107.3–107.7供应同一原缺陷、检测值与完整PB失败。结合交换子与Jordan乘法算子的恒等式只作123.3–123.4的中间步骤；旧模型、旧缺陷和旧失败不另计为新构造。新增承重是它们与所有有限自作用多项式、所有原中央平移乘积铅笔在同一总表上同时成立之后，对全原检测器目标仍不足的应用。没有历史优先权、文献穷尽或全部有限完整PB见证不可能性的声称。

## 追加锚（本行以下为增补区）

## 126. 同一原候选的有限不可约读取与准确复用

**定义 126.1（原世界、全部关系与第一实际框架）。** 完整采用118.1–118.3的同一原 $E,C,u,N,\mathcal P,S,D$ 及122.1全文援引的七项同源合同。为明确本组的全部输入，仍有

$$
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E=X,\qquad \mathcal A=C^*(X),\qquad
S(a,b)=a\circ b=(ab+ba)/2,\qquad
C=E\cap\mathcal A_+,\quad N=\|\cdot\||_E.
\tag{126.1}
$$

$E$ 是含单位实Jordan子代数，$X$ 是其JC完成；$E$ 允许不完备、无限维、不可分，$X$ 不必等于 $\mathcal A_{\rm sa}$。原正评价族 $\mathcal P$ 分离元素且准确决定 $C$，保留每个原评价 $\gamma$ 及全部零、不等、次归一质量 $m_\gamma=\gamma(u)$。A1保留全部有向Hermitian二表正性；A2保留每份实际相加三表 $(a+b,a,b)$ 及全部排列的实部在整个 $\mathbb R^3$ 上半正定和对应相加零向量；A3保留 $S(u,u)=u$，以及同一个固定有理 $0<\vartheta_0\le1$ 下的 $0\le a\le\vartheta_0u\Rightarrow a^2\le a$。全部原P2明确为

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(a\circ b)+i\gamma D(a,b)&\gamma(b^2)
\end{pmatrix}\succeq0
\qquad(a,b\in E,\ \gamma\in\mathcal P).
\tag{126.2}
$$

其中反对称性 $D(b,a)=-D(a,b)$ 是已付结论。全部原PB取118.2及配平主卷128.1–128.2的完整表等式；其等价元素形式对每个实际 $a,b,q\in E$ 为

$$
\begin{gathered}
v=D(a,b)-a\circ q,\qquad w=a\circ b+D(a,q),\\
D(b+v,q+w)-D(b-v,q-w)=-2b\circ v-2q\circ w.
\end{gathered}
\tag{126.3}
$$

数学正实线性泛函 $\phi:E\to\mathbb R$ 读取的是同一份实际表，配平主卷129.1由准确锥支付

$$
|\phi D(a,b)|^2
\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2.
\tag{126.4}
$$

这不增加实际准备，亦不把左端换成 $\phi(D(a,b)^2)$。原总映射 $D:E^2\to E$ 不预付可加、齐次、连续、可测、一般单位平移、协变、商下降、小图表输出闭合或完成延拓。

本组固定并消费的第一实际框架为

$$
h,e,j=D(h,e)\in E,\qquad h^2=e^2=j^2=u,\qquad
h\circ e=h\circ j=e\circ j=0,\qquad
Q=ihej\in Z(\mathcal A),\quad Q^*=Q,\quad Q^2=u.
\tag{126.5}
$$

$Q$ 只属辅助环境，不要求 $Q\in E$。对每个实际 $x\in E$、每个实 $R$，固定同一实际输出及余量

$$
\begin{gathered}
L_a y=a\circ y,\quad U_h=2L_h^2-I,\quad P_h^\pm=(I\pm U_h)/2,\\
c=P_h^+x,\quad z=P_h^-x,\quad k=h\circ x=hc,\\
t=iQhz=D(h,z)=[L_j,L_e]z,\qquad
g=D(Rh,x),\qquad r=g-Rt.
\end{gathered}
\tag{126.6}
$$

118.3已支付 $c,z,k,t,g,r\in E$、$[h,c]=[h,r]=0$、$hz=-zh$、$ht=-th$、$z\circ t=0$、$k^2=c^2$，以及

$$
[h,y]=0\ \Longrightarrow\
D(\alpha u+\beta h,y)=0
\qquad(y\in E,\ \alpha,\beta\in\mathbb R).
\tag{126.7}
$$

这里完整消费118.3对中央续卷189–191证明的接线及其全部准确前件，不另给第二实际框架。所有 $U_h$、$P_h^\pm$ 及下文有限Jordan表达式保持原 $E$；所有实际 $D$ 调用都留在原 $E$。

**定义 126.2（有限数学读取及符号）。** 取含单位不可约复 $*$-表示

$$
\pi:\mathcal A\longrightarrow M_n(\mathbb C),\qquad n\ge1,
$$

记 $H=\pi h$、$F=\pi e$、$J=\pi j$、$C_0=\pi c$、$Z=\pi z$、$\Theta=\pi t$、$G=\pi g$、$\rho=\pi r$。$C_0$ 不表示原正锥。不可约性给 $\pi(\mathcal A)=M_n(\mathbb C)$；中央自伴对合及Schur给

$$
\pi Q=\varepsilon I,\quad \varepsilon\in\{1,-1\},\qquad
\Theta=i\varepsilon HZ,\qquad G=R\Theta+\rho.
\tag{126.8}
$$

$F$ 酉地交换 $H$ 的正负特征空间，故 $n=2d$、$d\ge1$。矩阵读取只作用于同一个实际元素，尚未定义商响应 $D_\pi$。

**定义 126.3（已付范围及来源地址）。** 以下简名仅缩短准确引文，不改变前件、域或量词。

| 简名与canonical源 | 直接复用的结果 |
| --- | --- |
| [PB：配平主卷](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) | 128–129的原关系与正读取；137.1、138–142的完整有限原矩阵识别；240–251的有限Jordan商、原像支撑和类型限制。 |
| [OP：原多项式零响应卷](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md) | 59–61的全部幅度纯像；80.2的二阶角全部混合实际原像；82.1的同块取向；83.1的任意背景小连接；85.1–85.2的全域纤维及Cayley端点缺口；89–101的更强侧面约束与其反向边界。 |
| [C：中央响应续卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md) | 161–163的第一实际框架投影；182.2的有前件第二实际框架；189–191的零行证明；199.2、194.2、186.1–186.7的全部来源合同。 |
| [SM：谱混合卷](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md) | 24.1的固定二表边界；33.1–35.1的实际有限共同反射分割及逐对接法。 |
| 本卷100.1、118–122 | 无投影提升机制、第一实际框架的原调用、任意背景交换判据和七项合同。 |

PB241.1的零核吸收 $\pi a=0\Rightarrow\pi D(a,b)=0$ 不包含核平移不变 $\pi D(a+k,b)=\pi D(a,b)$。PB245.4的小纯正交行不是现有范围的终点：OP59.2已经识别全部纯像，OP80.2又识别任意二阶商角内全部混合像及其每份实际原代表。OP82.1统一同一简单块的符号；OP83.1在任意其他背景下识别秩一首行的严格小连接。这些结果直接复用，不重新证明或另计新增内容。OP89–101还已支付三射线侧面实收缩、同次PB的共同系数及增强预算；它们没有被忽略，也未被本组升级为任意高阶行公式。

全有限旧响应自动识别的准确地址是PB主卷142.1，前件为137.1及138–141；它要求原域本身就是完整有限复矩阵直和。C142.1只是同域矩阵坐标运输，C142.2明确保留全旧 $D$ 识别缺口。OP85.2所欠的是Cayley回溯端点与当前原目标的响应相同，不能用同像替代。本组不把PB主卷142.1套给尚未下降的 $\pi D$，也不重复PB185.1的原SO$(2)$槽不变性。

## 127. 不可约读取的满像与已付角取向

**命题 127.1（当前原条件支付全部自伴矩阵原像）。** 在126.1–126.2下，

$$
\boxed{\pi(E)=\pi(X)=H_n(\mathbb C).}
\tag{127.1}
$$

证明。$Y=\pi(X)$ 是有限维含单位JC代数，$\pi|_X:X\to Y$ 为满Jordan同态。$\pi(E)$ 是有限维实线性子空间，由原稠密性在 $Y$ 中稠密，故等于 $Y$；这正是PB241.1已用的闭性机制。PB247.1适用于这个有限Jordan商，直接给 $Y\cong_J\bigoplus_lH_{m_l}(\mathbb C)$。实、四元数、其他自旋及Albert块的排除已经由原PB支付，不在这里重作分类。

各简单块的单位在 $Y\subset M_n$ 中是正交投影。相对这些投影展开算子块，每个简单块中的元素都只支撑于该块单位，因而这些单位与 $C^*(Y)$ 交换。又

$$
C^*(Y)=\pi(C^*(X))=\pi(\mathcal A)=M_n(\mathbb C),
$$

故只留一个非零块，$Y\cong_JH_m(\mathbb C)$。仅有抽象类型还不够，必须排除有重数的Jordan嵌入；下述成熟矩阵单位论证只作为本命题的中间步骤。

若 $m=1$，$Y$ 只含实标量，$C^*(Y)=M_n$ 迫使 $n=1$，与实际第一框架矛盾。以下设 $m\ge2$。令 $\varphi:H_m(\mathbb C)\to H_n(\mathbb C)$ 为相应含单位嵌入，$P_i=\varphi(E_{ii})$。这些投影正交且和为 $I$。对 $i<j$ 令

$$
X_{ij}=E_{ij}+E_{ji},\qquad Y_{ij}=(E_{ij}-E_{ji})/i.
$$

Jordan关系使 $\varphi(X_{ij})$、$\varphi(Y_{ij})$ 仅有 $P_i,P_j$ 间的连接块，平方都是 $P_i+P_j$，故连接块是两空间间的酉映射，各 $P_i$ 秩相等，记为 $d_0$。若 $m\ge3$，关系 $X_{ij}\circ X_{jk}=X_{ik}/2$ 使实连接相容；选定各空间一次酉坐标，所有实连接都成为 $X_{ij}\otimes I_{d_0}$。若 $m=2$，直接用唯一实连接选坐标。

在这些坐标中，$X_{ij}\circ Y_{ij}=0$ 及 $Y_{ij}^2=E_{ii}+E_{jj}$ 使虚连接的上块为斜自伴酉 $W$，$W^2=-I_{d_0}$；对 $m\ge3$，$X_{ij}\circ Y_{jk}=Y_{ik}/2$ 和 $Y_{ij}\circ X_{jk}=Y_{ik}/2$ 使各虚连接使用同一个 $W$。$m=2$ 只有一个 $W$。于是生成的结合代数为 $M_m(\mathbb C)\otimes C^*(W)$。若 $d_0>1$，在 $W$ 非标量时取一个非平凡谱投影，在 $W$ 标量时任取一个非平凡投影；对应的 $I_m\otimes p$ 与全部生成元交换，违反不可约性。因此 $d_0=1$、$n=m$。嵌入是通常或转置坐标，像都是整个 $H_n(\mathbb C)$。得到(127.1)。∎

**命题 127.2（已付二阶角与第一框架共用取向）。** 在当前固定矩阵坐标中，OP82.1的块符号为 $\varepsilon$；已付角公式为 $\varepsilon i[\ ,\ ]/2$。

证明。取不与 $H$ 交换的秩一投影 $p$，由127.1任取实际 $a\in E$ 满足 $\pi a=p$。对实际对 $(a,h)$，$H$ 相对 $p$ 的连接范数至多 $\|H\|=1<2$，故OP83.1及反对称性给

$$
\pi D(h,a)=\sigma\,i[H,p]/2,
$$

其中 $\sigma$ 为OP82.1的同块符号。C163.1在原第一框架上，又给这份同一输出的 $H$-奇投影为 $\varepsilon i[H,p]/2$。交换子本来为 $H$-奇且非零，故 $\sigma=\varepsilon$。只比较一份已付小连接行的投影，不在全矩阵像中先定义响应。∎

## 128. 同一实际余量在有限读取中的完整判据

**定理 128.1（读取判据不要求响应下降或读取忠实）。** 对126.1的每个实际 $x,R,g,r$ 及126.2的每份读取，准确有

$$
\boxed{
\begin{aligned}
C_0^2\circ\rho=C_0\circ(C_0\circ\rho)
&\ \Longleftrightarrow\ [C_0,\rho]=0\\
&\ \Longleftrightarrow\ C_0\rho=0\\
&\ \Longleftrightarrow\ \rho=0\\
&\ \Longleftrightarrow\ \pi D(Rh,x)=Ri\pi(Qhz).
\end{aligned}}
\tag{128.1}
$$

这一证明也适用于任意有限维含单位 $*$-表示，不要求不可约、127.1的满像或 $\pi Q$ 为标量。它将119.1的共享输出与支撑机制接到同一有限读取，不从 $[\pi c,\pi r]=0$ 倒推原 $[c,r]=0$。

证明。$R=0$ 时零输入P2给 $g=r=0$。设 $R\ne0$。119.2–119.3的实际PB对每个实 $\alpha$ 给

$$
\begin{gathered}
a_\alpha=(1-R^2)c+z+g-R\alpha h,\qquad
b_\alpha=2Rk+\alpha u,\\
D(a_\alpha,b_\alpha)=K,\qquad
K=-2x\circ g+2R^2z\circ c,\qquad
P_H^+\pi K=-2C_0\circ\rho,
\end{gathered}
\tag{128.2}
$$

其中 $P_H^\pm Y=(Y\pm HYH)/2$。内值由(126.7)支付，负外值由实际全单位零行支付；整个实际 $K$ 对全部偏移相同，不是逐读取重选的商输出。

若 $[C_0,\rho]=0$，已知 $[H,C_0]=[H,\rho]=0$ 使三个自伴矩阵可同时对角化。对任一共同单位特征向量 $v$，写特征值为 $\tau\in\{1,-1\},a,b$。在已经对全部实数成立的(128.2)中，取有限实数 $\alpha=-2R\tau a$，则 $\pi(b_\alpha)v=0$。数学正读取 $\phi_v(y)=v^*\pi(y)v$ 的第二平方预算为零，(126.4)给 $v^*\pi K v=0$。$H$-奇矩阵在此向量上读取为零，故 $ab=0$。遍历共同特征基得 $C_0\rho=0$。

再直接使用119.11–119.12保持当前强度的原支撑PB和估计：

$$
D(Rh-g,Rk)-D(Rh+g,-Rk)=2Rhr,
\tag{128.3}
$$

$$
|\psi(hr)|^2\le\psi(c^2)\{R^2\psi(u)+\psi(g^2)\}
\qquad(\psi:E\to\mathbb R\text{ 为任意数学正读取}).
\tag{128.4}
$$

对任意矩阵向量 $v$ 取 $\psi_v(y)=v^*\rho\pi(y)\rho v$。它在原准确锥上正，质量 $\psi_v(u)=\|\rho v\|^2$ 可以为零。若 $C_0\rho=0$，则 $\psi_v(c^2)=\|C_0\rho v\|^2=0$，于是 $v^*H\rho^3v=0$。$[H,\rho]=0$ 使 $H\rho^3$ 自伴；二次型分离给 $H\rho^3=0$，乘 $H$ 后 $\rho^3=0$，自伴性给 $\rho=0$。不除读取质量，也不假定原 $cr=0$。

反向 $\rho=0\Rightarrow C_0\rho=0\Rightarrow[C_0,\rho]=0$ 用自伴性。第一项的等价只用

$$
4\{C_0^2\circ\rho-C_0\circ(C_0\circ\rho)\}
=[C_0,[C_0,\rho]].
\tag{128.5}
$$

在 $C_0$ 的特征基上，右端的 $ab$ 块为 $(v_a-v_b)^2\rho_{ab}$，为零恰当且仅当 $[C_0,\rho]=0$。最后一项按(126.6)等价于 $\rho=0$。整个证明读取固定原输出，没有商纤维平移或未知输入极限。∎

**推论 128.2（任意有限阶的仿射读取背景）。** 若当前实际背景满足

$$
\pi c=\mu I+\lambda H\qquad(\mu,\lambda\in\mathbb R),
\tag{128.6}
$$

则 $\pi r=0$，不要求原 $c=\mu u+\lambda h$，也不要求原背景有限谱或核部分消失。更一般地，对可约有限读取，$\pi c\in C^*(H,\pi Q)$ 足够。

证明。第一式和 $[H,\rho]=0$ 给 $[C_0,\rho]=0$。一般式还用 $\pi Q$ 与所有读取元素交换，故 $\rho$ 与 $C^*(H,\pi Q)$ 交换。128.1遂给结论。∎

二阶不可约读取的 $H$ 正负空间各一维，(128.6)自动成立；其全部实际原像早已包含在OP80.2、82.1中，不另计新二阶结果。一般 $n\ge4$ 时，同号空间内部有矩阵自由度，(128.6)不自动成立。SM24.1的固定四阶P2边界不具有总PB族，不是完整原候选的反模型。

## 129. 虚拟反射图表与同一实际外值的准确缺口

**定义 129.1（像中几何及原域中的有限标签）。** 固定 $R\ne0$、同一实际 $x,g,r$ 及不可约读取。将交换的 $H,C_0$ 同时对角化，取共同秩一投影分割 $(q_a)_{a=1}^n$：

$$
\sum_aq_a=I,\qquad Hq_a=\tau_aq_a,\qquad
C_0q_a=v_aq_a,\qquad \tau_a\in\{1,-1\},\quad v_a\in\mathbb R.
\tag{129.1}
$$

只选 $a<b$、$\tau_a=\tau_b=\tau$、$v_a\ne v_b$ 的对。对每一对，在矩阵像中定义

$$
P_{ab}=q_a+Fq_aF,\qquad S_{ab}=I-2P_{ab},\qquad H_{ab}=HS_{ab}.
\tag{129.2}
$$

$Fq_aF$ 位于相反的 $H$ 符号空间，所以 $P_{ab}$ 是秩二投影，且与 $H,F$ 交换；$S_{ab}$ 是与 $H,F$ 交换的自伴反射，在 $q_a,q_b$ 上分别为 $-I,+I$。这些幂等、反射和平方关系目前只存在于读取像。

由127.1，任取一份实际 $w_{ab}\in E$ 满足 $\pi w_{ab}=S_{ab}$，再在原域定义

$$
s_{ab}=\tfrac14(I+U_h)(I+U_e)w_{ab},\qquad
f_{ab}=h\circ s_{ab}.
\tag{129.3}
$$

$U_hy=hyh$、$U_ey=eye$ 都是保持 $E$ 的有限Jordan算子，且由 $he=-eh$ 可知两者交换。因此 $s_{ab},f_{ab}\in E$，

$$
[s_{ab},h]=[s_{ab},e]=0,\qquad
\pi s_{ab}=S_{ab},\qquad \pi f_{ab}=H_{ab}.
\tag{129.4}
$$

没有得到 $s_{ab}^2=u$ 或 $f_{ab}^2=u$。置实系数及实际标签

$$
\begin{gathered}
A_{ab}=R\tau(v_a+v_b),\qquad B_{ab}=R(v_b-v_a),\\
T_{ab}=A_{ab}u+B_{ab}f_{ab},\qquad V_{ab}=T_{ab}-2Rk,\\
a_+=x+g+R^2c-Rh\circ T_{ab},\\
a_-=x-g-R^2c+Rh\circ T_{ab}.
\end{gathered}
\tag{129.5}
$$

$T_{ab},V_{ab},a_\pm$ 及第三标签 $T_{ab}-Rk$ 全在原 $E$。$[h,T_{ab}]=0$，故(126.7)支付 $D(Rh,T_{ab}-Rk)=0$；不要求实际 $[c,T_{ab}]=0$。

**命题 129.2（原PB无条件支付的压缩等式）。** 对129.1的每一对及(129.3)的任意实际原像选择，准确有

$$
\boxed{q_a\pi D(T_{ab},a_+)q_b=(v_a+v_b)q_a\rho q_b.}
\tag{129.6}
$$

证明。取实际PB $(Rh,x,T_{ab}-Rk)$，位移为 $v=g+R^2c-Rh\circ T_{ab}$、$w=Rk$，两份完整外层恰为 $(a_+,T_{ab})$、$(a_-,V_{ab})$。只展开已知Jordan乘法得

$$
\begin{gathered}
D(a_+,T_{ab})-D(a_-,V_{ab})=\mathcal J,\\
\mathcal J=-2x\circ g-2R^2z\circ c
             +2Rz\circ(h\circ T_{ab}),\qquad
P_h^+\mathcal J=-2c\circ r.
\end{gathered}
\tag{129.7}
$$

即使 $c,T_{ab}$ 不交换，$[h,c]=[h,T_{ab}]=0$ 仍给 $c\circ(h\circ T_{ab})=T_{ab}\circ(hc)$；这使全部背景交叉项抵消。$k^2=c^2$ 消去平方项，$z\circ t=0$ 及偶奇关系给最后一式，没有展开未知 $D$。

令 $W=D(V_{ab},a_-)$。反对称性将(129.7)写成 $W-D(T_{ab},a_+)=\mathcal J$。在 $q_a,q_b$ 上，$\pi T_{ab}$ 分别为 $2R\tau v_a,2R\tau v_b$，$\pi k=HC_0$，故对 $q=q_a+q_b$ 有

$$
(\pi V_{ab})q=q(\pi V_{ab})=0.
\tag{129.8}
$$

对 $q\mathbb C^n$ 内的每个向量 $\xi$，取同一原正读取 $\phi_\xi(y)=\xi^*\pi(y)\xi$。实际表 $(V_{ab},a_-)$ 的第一平方预算 $\phi_\xi(V_{ab}^2)$ 为零，P2使 $\xi^*\pi W\xi=0$。自伴二次型极化于是给 $q\pi Wq=0$。取元素等式的 $ab$ 块；因两端 $H$ 同号，$\mathcal J$ 的奇部分没有贡献，且

$$
q_a\pi\mathcal Jq_b=-(v_a+v_b)q_a\rho q_b.
$$

得到(129.6)。这里只在指定两射线上消去 $\pi V_{ab}$，没有宣称其整个像为零，也没有把零核吸收替代压缩预算。∎

**定义 129.3（未付的特定外值投影关系）。** 对129.1中已固定的分割及每对已固定的实际原像，所需关系是

$$
\boxed{
q_a\pi D(T_{ab},a_+)q_b
=i\varepsilon B_{ab}\,q_aH_{ab}(\pi a_+)q_b.
}
\tag{VP}
$$

每个当前实际 $x\in E,R\ne0$ 各有一份有限关系族；要求它在所有这些实际输入、所有同号异背景特征对上成立。129.4的等价对任意预先固定的一份提升族适用，既不要求整条虚拟轴行，也不要求整个商的纤维不变。式(VP)是准确待证关系，本组不从原PB无条件推出它。

不能从 $H_{ab}^2=I$ 对实际 $f_{ab}$ 套C163.1：该定理要求原平方和实际框架，C182.2也要求原反射。OP80.2不能仅凭压缩后的两射线直接支付(VP)，因为 $T_{ab},a_+$ 的完整像一般不共同支撑于同一个二阶角；压缩正读取不使 $D$ 下降，也不提供角间纤维。OP89–101的侧面预算仍是已有约束，不在这里被省略或宣称已饱和。

**定理 129.4（有限投影族恰好等价于当前目标）。** 对任意129.1的共同分割，并为其每个相关对任意固定一份(129.3)的实际原像，全部有限个(VP)成立，当且仅当当前同一实际余量的像 $\rho=0$，亦即128.1中任一条件成立。

证明。两端同号且 $a\ne b$，故 $Z,\Theta$ 的该块为零，$C_0$ 的该块为零，$\pi T_{ab}$ 在这两条射线上对角。因此

$$
q_a(\pi a_+)q_b=q_a\rho q_b,\qquad
q_aH_{ab}=-\tau q_a.
\tag{129.9}
$$

(VP)右端成为 $i\varepsilon R\tau(v_a-v_b)q_a\rho q_b$。与129.2对同一个实际外值的(129.6)比较，

$$
\{i\varepsilon R\tau(v_a-v_b)-(v_a+v_b)\}q_a\rho q_b=0.
\tag{129.10}
$$

系数模平方为 $(v_a+v_b)^2+R^2(v_a-v_b)^2>0$，所以该块为零；反向块由 $\rho$ 自伴也为零。不同 $H$ 符号的块已由 $[H,\rho]=0$ 为零。同号同背景特征值的块不妨碍与 $C_0$ 交换。因此全部(VP)给 $[C_0,\rho]=0$，128.1给 $\rho=0$。若没有相关对，交换条件本已自动成立，结论相同。

反之若 $\rho=0$，129.6使(VP)左端为零，129.9使右端为零；对所有实际提升选择均成立。故任意一份预先固定的有限提升族都具有所述等价。∎

准确缺口由此可写成像中的二元Jordan关系 $C_0^2\circ\rho=C_0\circ(C_0\circ\rho)$，或特定实际外值的有限(VP)族。已付PB给同一外值的实系数 $v_a+v_b$；未付投影若由原PB生产，会给纯虚系数 $i\varepsilon R\tau(v_a-v_b)$。二者同时约束同一实际输出才排除跨高度余量。这不是新增公理，也不是一般高阶(VP)的证明。

## 130. 保留第一实际框架的总响应与无反射提升模型

**命题 130.1（全部数学原条件不强制框架相容反射提升）。** 存在满足126.1全部数学A1–A3/P2/PB、具有实际第一框架及四阶不可约读取的原域，其中一个与读取框架交换的虚拟自伴反射，没有任何与实际 $h,e$ 交换的实际自伴反射提升，甚至没有完成中的这种提升。该模型的轴行目标本身成立。

证明。采用本卷100.1已用的连续投影秩机制，并保留一份常值实际二阶框架。以 $X_2,Y_2,Z_2$ 记通常Pauli矩阵，定义

$$
\mathcal A=\{f\in C([0,1],M_4(\mathbb C)):
f(0)\in M_2(\mathbb C)\otimes I_2\},\qquad X=\mathcal A_{\rm sa}.
\tag{130.1}
$$

令 $E$ 为其中全部自伴矩阵多项式，$u=I_4$、$C=E\cap\mathcal A_+$，$N$ 为上确界算子范数，$S(a,b)=a\circ b$。若自伴矩阵多项式 $p$ 一致逼近 $f\in X$，则 $p-p(0)+f(0)$ 仍是自伴矩阵多项式，满足边界条件，误差至多原误差两倍。因此 $E$ 在 $X$ 中稠密。常数项的边界代数对乘法闭合，故Jordan乘法和下面的总响应都保持 $E$：

$$
D(a,b)=\frac i2[a,b]\qquad(a,b\in E).
\tag{130.2}
$$

原评价族 $\mathcal P$ 取所有下列逐点向量泛函：

$$
\gamma_{\sigma,\xi,m}(a)=m\,\xi^*a(\sigma)\xi,\qquad
\sigma\in[0,1],\quad \|\xi\|=1,\quad m\ge0.
\tag{130.3}
$$

它们分离 $E$、准确决定逐点正锥，质量为 $m$；全部零、不等及次归一质量保留。逐点序使 $E$ 为Archimedean序单位空间，其序单位范数就是 $N$。

对每个这样的评价，$a\circ b-iD(a,b)=ab$，所以同一P2正是两个向量 $\sqrt m\,a(\sigma)\xi,\sqrt m\,b(\sigma)\xi$ 的复Gram表；交换顺序的另一份有向表也正，给全部A1及P2。A2的任意实际相加三表，是向量 $(a+b)(\sigma)\xi,a(\sigma)\xi,b(\sigma)\xi$ 的实Gram表，故在整个实三空间半正定，指定相加向量及其排列的二次值为零。$S(u,u)=u$；对原固定 $0<\vartheta_0\le1$，若 $0\le a\le\vartheta_0u$，逐点矩阵谱给 $a^2\le a$，支付A3。这些证明对每个质量 $m\ge0$ 同时成立。

完整PB也在全部原三元组上逐元素成立。任取实际 $a,b,c\in E$，令 $\mathcal Z=b+ic$，并按PB原定义置

$$
r_\pm=b\pm D(a,b)\mp a\circ c,\qquad
s_\pm=c\pm a\circ b\pm D(a,c).
$$

直接用(130.2)展开得

$$
\begin{gathered}
r_\pm+is_\pm=(I\pm ia)\mathcal Z,\\
r_\pm^2+s_\pm^2+2D(r_\pm,s_\pm)
=(r_\pm+is_\pm)^*(r_\pm+is_\pm)
=\mathcal Z^*(I+a^2)\mathcal Z.
\end{gathered}
\tag{130.4}
$$

两符号给相同元素，故每个原评价读取的完整PB均成立，不局限于某个固定三元组。

取实际常值 $h=Z_2\otimes I_2$、$e=X_2\otimes I_2$，则

$$
j=D(h,e)=-Y_2\otimes I_2,\qquad Q=ihej=I_4.
\tag{130.5}
$$

三轴平方为 $u$ 且两两Jordan正交。令 $\pi(f)=f(1)$；对每个自伴 $B\in M_4$，函数 $\sigma\mapsto\sigma B$ 都在原 $E$，故 $\pi(E)=H_4$、$\pi(\mathcal A)=M_4$，$\pi$ 不可约。矩阵

$$
S=I_2\otimes Z_2
\tag{130.6}
$$

为与 $\pi h,\pi e$ 交换的虚拟反射，有实际原像 $\sigma\mapsto\sigma S$，该原像也与实际 $h,e$ 交换，但其平方不是 $u$。

若有完成 $X$ 中的自伴 $s$ 满足 $s^2=u$、$[s,h]=[s,e]=0$、$s(1)=S$，则 $s(0)\in M_2\otimes I_2$。与 $Z_2\otimes I_2,X_2\otimes I_2$ 同时交换，迫使 $s(0)=\lambda I_4$；平方关系给 $\lambda=\pm1$。连续投影 $(I+s(\sigma))/2$ 的秩在连通区间上恒定，但其零点秩为零或四，一点秩为二，矛盾。故完成中也不存在所需框架相容提升，原 $E$ 中更不存在。

另一方面，本模型对全部原 $x,R$ 都有

$$
D(Rh,x)=\frac{Ri}{2}[h,x]=Ri\,hP_h^-x=RiQhP_h^-x.
\tag{130.7}
$$

因此反驳的仅是框架相容实际反射提升捷径，不是(VP)、轴行目标或完整原量子起源。本模型验证全部数学原关系，但没有供应七项物理来源合同的实际实现。∎

## 131. 联合忠实读取如何接回同一原余量

**命题 131.1（条件性回接与RFD分支）。** 另给一族有限维不可约含单位 $*$-读取 $(\pi_\eta)$，满足

$$
\bigcap_\eta\ker\pi_\eta=\{0\}\quad\text{于同一 }\mathcal A.
\tag{131.1}
$$

固定任一实际 $x\in E,R\in\mathbb R$ 及(126.6)的同一 $r$。若每份读取均已由原关系支付 $[\pi_\eta c,\pi_\eta r]=0$，等价地对 $R\ne0$ 支付129.3的有限(VP)族，则

$$
D(Rh,x)=RiQhP_h^-x.
\tag{131.2}
$$

若这些前件对全部原 $x$、全部实 $R$ 成立，才同时得到

$$
D(Rh,x)=R\,D(h,x)\qquad(x\in E,\ R\in\mathbb R).
\tag{131.3}
$$

证明。128.1逐份给 $\pi_\eta(r)=0$；每份读取中的 $r$ 都是同一个已固定实际原元素，不按 $\eta$ 重选原代表或输出。联合忠实性给 $r=0$，即(131.2)。若对全部强度成立，再取单位强度识别同一 $x$ 的 $D(h,x)$，得到(131.3)。$R=0$ 直接由P2包含。∎

残余有限维性RFD表示存在联合忠实的有限维表示族；将每个有限维表示拆为不可约块，便得到131.1可用的读取族。它是明确的环境分支资料，不由原A1–A3/P2/PB在这里制造。127.1已支付每份不可约读取的满像，因此满像不是该分支的另一项额外假设。128.2所述读取背景范围无须(VP)新前件；二阶读取范围直接已有OP80.2。一般 $n\ge4$ 的(VP)生产仍未支付，所以本组没有关闭一般RFD分支。没有这类联合忠实有限读取的一般环境，更不能仅凭各有限窗口的结论认定原余量消失。

## 132. 有限读取几何、成熟来源与七项同源消费者

**定义 132.1（几何与承重来源）。** 第一实际轴 $h$ 把矩阵像分成正负两面，C163.1已确定跨面的全部输出，余量 $\rho$ 只住在每面内部。背景 $C_0$ 在各面画出有限高低线。128.1说明，只要不同高度之间没有余量连接，共享输出族及同一支撑PB就排除全部余量，连背景零部位也不能藏余量。129.2把每份指定实际外值的跨高度块读成高度之和乘余量；(VP)若由原PB支付，会把同一块读成纯虚的高度差乘余量。两系数不相容消掉这条连接；同高块只需128.1的剩余支撑处理。数学虚拟镜面只用于选这两条线，130.1不允许把像中镜面自动解释为实际原反射。

本组承重综合归为 $\texttt{repo-derived}$：127.1把PB247.1的有限Jordan商类型接到不可约生成关系以支付满像；128.1把119.1共享输出机制接到可能非忠实的同一有限读取；129.2–129.4将SM33.1的实际反射接法缩到准确的特定外值投影条件；130.1在本卷100.1的提升障碍中保留第一实际框架和全部数学总响应。原域119.1、全纯像OP59–61、二阶混合角OP80–82、小连接OP83、OP89–101侧面预算及实际有限分割SM33–35均直接复用，不重新计为这里的数学增量。

PB247.1已引用的Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，Theorem2.9.6、§2.9.7、Theorem2.9.8、Remark2.9.9供应有限形式实分类。127.1中的矩阵单位及重数分解、有限谱定理、Schur、二次型极化、矩阵Weierstrass逼近及连续投影秩不变性都是成熟中间工具，不另立新一般分类。正读取、态正延拓和表示分离保持C185.3、C199.1及本卷120.1所引Blackadar，[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)的原用途；正延拓不是正常性，也不产生物理准备。这里不主张文献穷尽、历史优先权、外部开放问题解决或形式化核验。

**定义 132.2（七项合同全文援引及本组供应）。** [C定义199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#199-来源几何与量子消费者的完整边界)第1、2、3、4、5、6、7项逐项全文，连同其完整援引的[C定义194.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#194-新连接完整候选与量子消费者的范围)、[C定义186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#186-七项原量子来源合同的准确消费者)和各项全部上游量词，均作为126–133的合同组成部分，经本卷122.1接回同一第一实际框架。以下七行只解释本组的数学供应，不能替代或缩减任何完整原合同。

| 量子消费者及全文合同地址 | 有限读取供应与仍须的同源实现 |
| --- | --- |
| 复Hilbert、可观测量、相干叠加：199.2第1项、194.2第1行、186.1及全部上游 | 127.1给完整自伴矩阵读取像，128.1及129.4只条件性识别同一实际第一轴行。同一全域旧乘法和完成运输、唯一原 $\Omega/\mathrm{native}$、全词 $K/J/q$、parent/ready、可取得标签、合法控制及实际相干准备仍须完整原来源；矩阵满像不是全部物理可取得性。 |
| 原态、效果、质量、Born：199.2第2项、194.2第2行、186.2及全部上游 | 数学正读取只读原表。Born仍绑定原评价、原事件、准确效果区间、实际完整菜单及接受归属，只归一该菜单的正总质量。全部零、不等、次归一质量、原 $q$、中心权、经典不等维与静默部分，以及原抽签、共同根、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定强度、P9、独立 $W_e$、全部中间切口和固定支持全质量均保留。 |
| native、真正相关联合、张量：199.2第3项、194.2第3行、186.3及全部上游 | 数学矩阵块和框架交换不产生子系统。仍须同一个真实非零相关联合、忠实同向交换局部腿、交叉零、共同实现、联合生成与分离、重数、全部相关输入、中央对、经典及不等维块和递归同源参考；相同边缘及分别可达不替代联合。 |
| typed CP、Kraus及整台递归参考：199.2第4项、194.2第4行、186.4及全部上游 | 正读取和压缩预算不产生原箭头。未归一回溯、全部合法typed前后接、反变复合、分区、全未来自然性和箭头商下降保留；系统、整个环境、全部成功失败细记录及port/post-port输出、每份输出每个仍合法未来、三实际投影及支持内补、共同真实支持、全部相关正输入的intertwining与夹界、每个所需有限递归深度和累计支持准确运输仍须完整来源。 |
| 仪器、TP、更新、Lüders：199.2第5项、194.2第5行、186.5及全部上游 | 有限输出识别不提供原仪器、接受端或平方根词。完整typed菜单、整台环境及全部输出未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词和接受条件仍须原合同；TP另需完整单位分区，Lüders另需同一完整输出的像内射线校准。只归一正输出，零分支保留；正常物理表示、指定前对偶和所需收敛另付。 |
| 全历史、全未来、真实返回、CountRead：199.2第6项、194.2第6行、186.6及全部上游 | 有限读取不改写程序或原读取次序。全部合法顺序、自适应、并行历史、每个输出的每个仍合法未来、环境细记录泄漏、停止拒绝销毁、真遗忘、同数两侧及同数逆向真实返回保持；读后同一原完整活动输入、负提升两活路分别控制与相干聚合、具名分析词到完整原菜单及接受端、精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 均守原域。无限非离散记录的可数可加、正常性和指定前对偶不能由有限图表补出。 |
| 动力、物理钟、能量、共同尺度：199.2第7项、194.2第7行、186.7及全部上游 | $R$、谱值和虚拟反射都不是时间或控制成本。同一旧全域乘法、保持可能不完备原域的流、真实相位及门序列、可逆一参数群、物理钟、所需强连续酉实现、生成元域、Hamiltonian能量、共同作用量、共同正 $\hbar$ 及共同仪器仍须同源；原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 预算保持原合同含义。 |

独立原公理数没有减少。数学 $\pi$、投影、原像及正读取不是实际系统、准备、来源商、仪器或参考。即使131.1在一个环境分支适用，也只支付第一实际轴行；任意首标签的全域旧双线性、全部有限旧复Gram、原R、完整同一结合乘法及完整量子来源仍须各自原桥。

## 133. 两面、高低线与未付投影的完整中文说明

**定义 133.1（同一响应表的有限几何与准确止点）。** 始终只有原世界中的同一张实际响应表。两标签的有向正比较、相加三角、单位小窗和任意三标签的完整正反配平全部保留，方向反转仍可改变符号，实际仪器先后仍可有不同结果。有限读取可以把不同原对象照成同一个矩阵，却不能因此合并它们的实际响应。已有结论已经认回全部纯像，也认回任意二阶窗口中的全部混合输入和全部实际原代表，并处理任意背景下的小连接及更强侧面预算；这些都不再作为缺口重做。当前不可约读取还保证每个自伴矩阵都有实际原像，但原像不必继承投影或反射的平方关系。

固定一次真正的原比较后，第一根实际轴把读取像分成两面，跨面的响应已经认清，未知余量只留在每面的内部。背景在每面有一些高低线。只要余量不在不同高度之间搭线，原配平产生的一整族外表便共享完全相同的实际输出；先对全部实偏移成立，再为每个共同读法选一个有限偏移，让第二输入的平方预算恰好为零，同一正表就迫使背景数值与余量数值的乘积为零。另一份同强度支撑配平接着排除余量躲在背景零部位的可能。二阶读取每面只有一条线，内部搭线本来不存在；高阶读取每面有多条线，不能照搬二阶结论，更不能把几个已知小角的响应直接相加。

高阶所欠的接口已经写成(VP)。在同一面上挑两个高度不同的点，在读取像中画一面翻转指定框架线对的虚拟镜面，再用它的实际原像和有限Jordan运算造出所有真正调用的标签。原PB已经让某个指定实际外值的这条连接等于两端高度之和乘未知余量；若原关系还能生产(VP)，同一个实际外值就必须同时等于纯虚的高度差乘同一余量。非零实强度下这两个系数不能相等，连接便消失。全部这类有限投影与当前同一余量为零准确等价；给缺口命名没有填上它，一般高阶(VP)仍待由实际PB生产。

也不能宣称虚拟镜面总有实际反射副本来越过缺口。130.1给出一份全部数学正表和全部三标签配平均成立的标准总响应模型，其中第一实际框架真实存在，某个像中镜面却没有与这份框架相容的实际反射提升：连续投影的秩不能从零或四跳成二。模型自己的轴行公式全部正确，所以它只排除提升捷径，不反驳(VP)或原目标，也不证明目标独立于原条件。

如果每份有限读取都从原关系付出了(VP)，还必须有联合忠实性，才能把“各窗口都看不见余量”接回“同一个原余量为零”。RFD是这一分支的明确资料，不是所有背景默认具有的性质；其一般高阶接口仍未关闭，没有这种分离族的一般环境也未被有限结论覆盖。本组没有得到无条件全阶轴行，也没有构造违反它的完整反模型。完整原量子来源仍为OPEN：数学满像、几何和读取不制造实际准备、完整Born菜单、真正相关联合、整台仪器与环境全部输出、递归同源参考、全部历史未来、真实双向返回、无限计数、物理钟、能量或共同作用量；132.2全文援引的七项合同及全部上游量词始终保留。

## 追加锚（本行以下为增补区）

## 134. 同一实际输出在正夹读下的准确方差预算

**定义 134.1（原条件、尖锐读取与两个不同的检测对象）。** 完整沿用118.1–118.3、126.1的同一原 $E,C,u,N,\mathcal P,S,D$：原A1–A3、准确锥、全部原正评价及其零、不等、次归一质量、全部P2和完整PB，以及唯一使用的第一实际 $h,e,j=D(h,e),Q$ 框架。七项实际来源合同完整取137.3的全文引用。原域允许不完备、无限维、无原子或不可分；不增加 $[c,e]=0$、原共同谱分割、根或逆、旧 $D$ 正则性、算子二表正性或CP。对任意原 $h$-偶 $c$、原 $h$-奇 $z$ 和任意实 $R$，始终固定

$$
x=c+z,\qquad t=iQhz,\qquad g=D(Rh,x),\qquad r=g-Rt,
\qquad [h,c]=[h,r]=0.
\tag{134.1}
$$

对原自伴 $d,y,v$ 定义保持原域的有限Jordan表达式

$$
\begin{aligned}
U_d(y)&=2d\circ(d\circ y)-d^2\circ y=dyd,\\
V_c(d)&=2U_c(d^2)+2U_d(c^2)-4(c\circ d)^2
       =[c,d]^*[c,d]\in C,\\
K_c(v)&=c^2\circ v-c\circ(c\circ v)=\tfrac14[c,[c,v]].
\end{aligned}
\tag{134.2}
$$

这些环境乘积恒等式只说明有限原表达式的值；$K_c(v)$ 一般不为正。它与下述实际共享输出 $K$ 不同。数学环境正读取 $\phi$ 称为 $(h,c)$ 尖锐，若对某个 $\epsilon\in\{1,-1\}$、$a\in\mathbb R$ 有

$$
\phi((h-\epsilon u)^2)=\phi((c-au)^2)=0.
\tag{134.3}
$$

这里不要求 $\phi(u)=1$，亦不要求对 $r$ 尖锐。零正泛函包括在内；非零归一尖锐态的非空性在135.3的显式模型中另证，不把它们作为物理准备。

**命题 134.2（读取改变而实际表不变的精确电荷）。** 对任意满足(134.3)的 $\phi$ 和任意原 $h$-偶自伴 $d$，取 $\alpha=-2R\epsilon a$。准确有

$$
\begin{gathered}
\phi(U_d(B_\alpha^2))=4R^2\phi(V_c(d)),\\
\boxed{
|\phi(U_d K)|^2+\phi(U_d(A_\alpha\circ B_\alpha))^2
\le 4R^2\phi(V_c(d))\,\phi(U_d(A_\alpha^2)).}
\end{gathered}
\tag{134.4}
$$

其中实际表完整复用119.2–119.3：对全部实 $\alpha$，原PB $(Rh;x,Rhc+\alpha u)$ 的内值为 $g,0$，两份外层及其旧输出为

$$
\begin{gathered}
A_\alpha=(1-R^2)c+z+g-R\alpha h,\qquad
B_\alpha=2Rhc+\alpha u,\\
A_\alpha^-=(1+R^2)c+z-g+R\alpha h,\qquad
B_\alpha^-=\alpha u,\qquad D(A_\alpha^-,B_\alpha^-)=0,\\
D(A_\alpha,B_\alpha)=K=-2x\circ g+2R^2z\circ c.
\end{gathered}
\tag{134.5}
$$

负外值由原全单位零行支付，整个 $K$ 对全部偏移相同。(134.4)只给这张原表更换正读取，不为任何未知演员指定交换子响应。

证明。在 $\phi$ 的GNS表示中省略表示符号，循环向量 $\xi$ 的平方范数为 $\phi(u)$。(134.3)给 $h\xi=\epsilon\xi$、$c\xi=a\xi$。$[h,d]=0$ 及 $[h,c]=0$ 给

$$
B_\alpha d\xi
=2Rhc d\xi-2R\epsilon a d\xi
=2Rh[c,d]\xi
=2R\epsilon[c,d]\xi.
\tag{134.6}
$$

所以 $\phi(dB_\alpha^2d)=\|B_\alpha d\xi\|^2=4R^2\phi([c,d]^*[c,d])$。$U_d$ 在准确原锥上为正，故 $\phi_d=\phi\circ U_d$ 是118.4的合法数学正读取，质量为 $\phi(d^2)$。对同一实际表 $(A_\alpha,B_\alpha,K)$ 用P2，并保留交叉均值平方，得到(134.4)。没有对未知 $D$ 展开、换值或取极限。∎

特别，$d=r$ 和每个实 $s$ 对应的 $d=u+sr$ 都合法，且

$$
\phi\bigl(U_{u+sr}(B_\alpha^2)\bigr)
=4R^2s^2\phi(V_c(r)).
\tag{134.7}
$$

这就是该夹读的第二平方预算；一般情形没有生产它为零。$V_c(u+sr)=s^2V_c(r)$ 只用已知乘法的交换子展开，不是旧响应的可加性。所有式子包含零原对象、$R=0$、$s=0$ 和零读取质量；没有除以强度、谱值或任何质量。零原对象只需零读取，毋须归一态或字符。

## 135. 合法连续谱原域与非空的共同尖锐态

**定义 135.1（固定原域的标准模型对应）。** 令 $H_0=L^2([0,1],ds)$、$f(s)=1$，$M$ 为乘以 $s$ 的算子，$P=|f\rangle\langle f|$。取

$$
\begin{gathered}
\mathcal B_0=\operatorname{alg}_{\mathbb C}^*(I,M,P),\qquad
\mathcal B=\overline{\mathcal B_0}^{\|\cdot\|},\\
\mathcal A_0=M_2(\mathcal B_0),\qquad
\mathcal A=M_2(\mathcal B),\qquad E=(\mathcal A_0)_{\rm sa},\\
u=I,\quad C=E\cap\mathcal A_+,\quad N=\|\cdot\||_E,\quad
S(a,b)=a\circ b,\quad D(a,b)=\tfrac i2[a,b].
\end{gathered}
\tag{135.1}
$$

$\mathcal P$ 取全部数学正实线性泛函，保留每份质量及其所有非负倍数。原域从一开始就是这份代数星域的自伴部，只含有限代数表达式。它是Archimedean序单位空间，在 $\mathcal A_{\rm sa}$ 稠密，范数及锥准确继承；全部有界原输入的Jordan乘积及此处显式定义的总 $D$ 都返回 $E$。

完整数学合法性直接取[静态重构卷35.1–35.2](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md#35-全输入缩放交换子族的精确缺陷)，其 $(\mathcal A,\mathcal A_0,E,\mathcal P,\kappa)$ 准确取(135.1)及 $\kappa=1$。简短核对其接口：$a\circ b-iD(a,b)=ab$，正泛函对 $w^*w$ 的非负性给全部有向Gram二表；相加标签的实Gram给A2及指定相加零向量；$0\le v\le\vartheta_0u$、固定有理 $0<\vartheta_0\le1$ 给 $v^2\le v$，支付A3。完整PB使用与130.4相同的恒等式：对任意原 $a,b,q$，置 $Z=b+iq$ 及原端点

$$
\begin{gathered}
b_\pm=b\pm D(a,b)\mp a\circ q,\qquad
q_\pm=q\pm a\circ b\pm D(a,q),\\
b_\pm+iq_\pm=(I\pm ia)Z,\\
b_\pm^2+q_\pm^2+2D(b_\pm,q_\pm)
=Z^*(I+a^2)Z.
\end{gathered}
\tag{135.2}
$$

两符号给同一元素，故全部原输入、全部正读取和全部质量的FULLPB成立。这是已有标准模型结论的参数对应，不是另一套一般模型定理，更不把该模型的双线性赋给未知原 $D$。

取实际原标签

$$
\begin{gathered}
h=\begin{pmatrix}I&0\\0&-I\end{pmatrix},\quad
e=\begin{pmatrix}0&I\\I&0\end{pmatrix},\quad
j=D(h,e)=\begin{pmatrix}0&iI\\-iI&0\end{pmatrix},\quad Q=ihej=I,\\
c=\begin{pmatrix}M&0\\0&M+2I\end{pmatrix},\qquad
v=\begin{pmatrix}P&0\\0&P\end{pmatrix}.
\end{gathered}
\tag{135.3}
$$

三轴平方为 $u$、两两Jordan正交，$[h,c]=[h,v]=0$，而 $[c,e]=\left(\begin{smallmatrix}0&-2I\\2I&0\end{smallmatrix}\right)\ne0$。对每个原 $h$-奇 $z$、每个实 $R$，此模型的同一实际响应准确为

$$
g=D(Rh,c+z)=Ri hz=Rt,\qquad r=0.
\tag{135.4}
$$

非零 $v$ 始终只是分离性测试元素，不是实际非零余量。

**命题 135.2（环境紧理想与原域部分）。** 在(135.1)中有固定的非零闭双边理想

$$
J=M_2(\mathcal K(H_0))\subset\mathcal A,\qquad
J_0=J\cap\mathcal A_0.
\tag{135.5}
$$

$v,K_c(v),V_c(v)$ 都属于 $(J_0)_{\rm sa}$，其中 $V_c(v)\in C$。

证明。向量 $M^nf$ 的复线性包是多项式，在 $H_0$ 稠密；$M^nPM^m=|M^nf\rangle\langle M^mf|$ 是原代数中的秩一多项式核。逼近两端向量并用秩一算子的范数恒等式，得到所有秩一算子属于 $\mathcal B$，继而 $\mathcal K(H_0)\subset\mathcal B$。紧算子在 $B(H_0)$ 中为双边理想，故(135.5)确为 $\mathcal A$ 的闭双边理想。$v\in J_0$，而(134.2)给出的检测器与电荷只用有限原Jordan运算；其每个环境乘积均含紧因子，所以仍在 $J_0$，电荷的正性由(134.2)给出。∎

**命题 135.3（非空但遗漏整个理想的尖锐态族）。** 令 $\mathscr S_{h,c}$ 为 $\mathcal A$ 上满足(134.3)的全部归一态。它非空，且每个 $\phi\in\mathscr S_{h,c}$ 都在整个 $J$ 上为零。

证明。$h,c$ 交换，$C^*(u,h,c)$ 是含单位交换子代数。对每个 $b\in[0,1]$，可在 $h$ 的正角以 $c$ 值 $b$ 取字符，也可在负角以 $c$ 值 $b+2$ 取字符；这就是 $M$ 的连续谱 $[0,1]$ 上的点值。含单位子代数的态正延拓给环境态，字符在两个平方上的读取为零，故得到 $\mathscr S_{h,c}$ 的成员。这不要求具体 $M$ 有特征向量。

反之，任取尖锐态及其 $\epsilon,a$，令 $p=(u+\epsilon h)/2$。由 $\phi(u-p)=0$ 和正泛函Cauchy–Schwarz，$\phi(y)=\phi(pyp)$。因此它约化为相应角上的 $\mathcal B$ 态 $\rho$，且

$$
\rho((M-bI)^2)=0,\qquad
b=\begin{cases}a,&\epsilon=1,\\a-2,&\epsilon=-1.\end{cases}
\tag{135.6}
$$

每个实 $b$ 的 $M-bI$ 都无核：单点集合的Lebesgue测度为零。它自伴，因而值域稠密。对任意 $\eta\in H_0$ 及 $w=(M-bI)\eta$，算子不等式

$$
0\le |w\rangle\langle w|
\le\|\eta\|^2(M-bI)^2
\tag{135.7}
$$

使 $\rho(|w\rangle\langle w|)=0$。值域稠密及态的范数连续性把该零值扩展到每个秩一算子；有限秩线性包和范数闭包再给 $\rho|_{\mathcal K(H_0)}=0$。压回 $p$ 角便得 $\phi|_J=0$。这些逼近只作用于已定义的有界算子与正读取，没有输入旧 $D$。∎

## 136. 任意原夹读的全部有限组合仍遗漏同一理想

**定理 136.1（整个指定夹读族的理想边界）。** 对135.1的每个原自伴标签 $d\in E$，无论它是否与 $h$ 或 $c$ 交换，都有

$$
U_d(J)\subset J,\qquad U_d(J_0)\subset J_0.
\tag{136.1}
$$

因而对任意有限个词及任意非负实权重，映射

$$
\begin{gathered}
W_j=U_{d_{j,n_j}}\circ\cdots\circ U_{d_{j,1}},\qquad
n_j\ge0,\quad d_{j,k}\in E,\\
T=\sum_{j=1}^m\lambda_jW_j,\qquad m\ge0,\quad\lambda_j\ge0
\end{gathered}
\tag{136.2}
$$

都保正、保持原域，并将 $J,J_0$ 各自映入自身。$n_j=0$ 表示恒等映射，$m=0$ 表示零映射。没有标签集或有限长度的共同上限；有限复合与有限正和的任意交错可展开成(136.2)。整个读取族

$$
\mathscr R=\left\{\sum_{j=1}^m\lambda_j\phi_j\circ W_j:
\phi_j\in\mathscr S_{h,c},\ \lambda_j\ge0,\ W_j\text{ 如上}\right\}
\tag{136.3}
$$

在 $J$ 上恒为零，其原限制在 $J_0$ 上恒为零。零质量、各不相等及次归一质量均不剔除，不作归一。

证明。双边理想性使 $dy d\in J$ 对每个 $y\in J$ 成立；$d,y\in\mathcal A_0$ 时结果仍在 $\mathcal A_0$。自伴 $d$ 的夹乘保正，原限制又等于(134.2)的有限Jordan算子。逐次复合及非负有限求和保持这些性质，135.3于是逐项给(136.3)的零值。这里任意标签的理想保持不同于134.2的精确电荷公式；后者仍要求 $[h,d]=0$。结论只涉及指定夹乘生成的映射类，不涉及任意正映射。∎

**命题 136.2（同一正常见证的两个严格正读取）。** 令 $\psi$ 是具体 $H_0\oplus H_0$ 上单位向量 $(f,0)$ 的向量态。它的原限制合法、对 $h$ 尖锐而对 $c$ 不尖锐。准确有

$$
\boxed{\psi(K_c(v))=\frac1{24},\qquad
\psi(V_c(v))=\frac1{12}.}
\tag{136.4}
$$

证明。$\mu_1=\langle f,Mf\rangle=\int_0^1s\,ds=1/2$，$\mu_2=\langle f,M^2f\rangle=\int_0^1s^2\,ds=1/3$。在该态读取的第一角中，

$$
\begin{aligned}
K_M(P)&=\tfrac14(M^2P-2MPM+PM^2),\\
\psi(K_c(v))&=\tfrac12(\mu_2-\mu_1^2)=\tfrac1{24},\\
\psi(V_c(v))&=\|[M,P]f\|^2
=\|(M-\mu_1I)f\|^2
=\mu_2-\mu_1^2=\tfrac1{12}.
\end{aligned}
\tag{136.5}
$$

故 $K_c(v)\ne0$ 且正元 $V_c(v)\ne0$，全部(136.3)的读取却都读它们为零。第一式是检测器的正读数，不宣称整个 $K_c(v)$ 为正。$\psi$ 的 $c$ 方差为 $1/12$，所以它不在尖锐态族中。∎

**命题 136.3（具体表示中的正常性边界）。** 在显示的 $\mathcal A\subset B(H_0\oplus H_0)$ 表示中，$\mathscr S_{h,c}$ 的态均非正常；这里正常指能由该表示上的正迹类密度读取。若有非零正常尖锐态，$h$ 尖锐使其密度支撑于一角，$c$ 零方差使该角密度平方根的像落在 $\ker(M-bI)$，而此核为零，矛盾。相反，136.2的 $\psi$ 在此具体表示中正常且不尖锐。

正常性依赖表示。态在自己的GNS表示中具有循环向量，或延拓到包络双对偶，并不把它变成上述具体表示的正常物理态，也不供应指定物理前对偶或任何物理准备。字符延拓保证非空，不能被解释为连续谱中已经取得了正常本征态。

## 137. 原域、成熟来源与七项同源目标的保留

**定义 137.1（分离性结论的准确适用域）。** 134.2保留同一实际表的整个第二平方预算；135–136给出一份满足全部数学原条件、实际余量为零的模型，其中整个尖锐态及有限原夹读族仍不分离非零的原正测试元。所否定的是对任意测试缺陷的推断

$$
\bigl[\ell(V_c(v))=0\text{ 对全部 }\ell\in\mathscr R\bigr]
\ \Longrightarrow\ V_c(v)=0,
\tag{137.1}
$$

检测器 $K_c(v)$ 的同类推断也失败。它不表明实际FULLPB余量能够非零地落入 $J_0$，不证明一般实际 $V_c(r)$ 被这些读取全部消去，更不构造违反119.1的实际响应。显式模型始终有(135.4)的实际 $r=0$。119.1先假定交换再作共同字符读取，121.1先取得全偏移共享输出再实例化；这些原结论直接复用。谱混合卷33.1–35.1先逐对控制非对角块再读有限共同分割，也直接复用。128.1、129.4、131.1的有限读取判据及条件回接保持各自前件；一般(VP)没有由这里生产，联合忠实性也没有由尖锐族补出。

所有实际 $D$ 输入、输出、$A_\alpha,B_\alpha,K,r,U_d,V_c(d),K_c(v)$ 均为有限原Jordan表达式或实际原输出。$J$ 是环境闭理想，$J_0$ 才是其原星域部分；两者不可混同，任意完成中的紧算子不自动成为原标签。原正读取的序单位界 $|\phi(y)|\le\phi(u)N(y)$ 保证连续性；在135.1的稠密全自伴原域中，它们可正延拓到完成。完成、GNS向量、字符和紧算子范数极限仅用于这些数学读取的论证，不定义商 $D$，不延拓未知 $D$，不添根、逆、投影、准备、控制、参考或极限响应。一般原域仍可严格小于环境自伴部。

**定义 137.2（成熟来源与承重综合）。** 119.1–119.3、118.3的原零行、119.11–119.13的原支撑、谱混合卷33–35的有限共同分割，以及126–133的条件有限读取接口均为既有结果。135.1–135.2只作[静态重构卷35.1–35.2](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md#35-全输入缩放交换子族的精确缺陷)的标准模型对应，130.4已有同一配平恒等式。它们不另计为新的模型供应者或一般旧表识别。

态正延拓、分离及GNS采用120.1所引 Blackadar，[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，II.6.3.1、II.6.3.3–II.6.3.6及II.6.4；多项式稠密、秩一逼近、紧理想和正泛函连续性也是成熟工具。全态分离不能转交给指定尖锐子族。更强的线性化工具仍有自己的前件：Cabello–Peralta，[*Weak-2-local symmetric maps on C*-algebras*](https://arxiv.org/abs/1510.00915)，v1的定义及Theorem2.5要求每对复输入和每个对偶泛函共用一个复线性对称插值映射；这里的原实域P2/PB没有供应该全C*域插值。Niestegge，[*Dynamical Correspondence in a Generalized Quantum Theory*](https://arxiv.org/abs/1402.0158)，v2的Lemma3从有界线性算子起步，Definition1还要求到斜序导子的线性赋值及混合交换子关系；这里没有生产这些前件。

本组的承重综合归为 $\texttt{repo-derived}$ 应用：将同一原共享输出接到精确的夹读方差预算，并在一份合法连续谱原域中证明整个指定有限夹读族遗漏同一非零理想。成熟状态与理想工具不另计为新一般定理；不主张历史优先权、文献穷尽、外部开放问题解决或形式化核验。

**定义 137.3（七项完整合同的全文引用）。** [中央续卷定义199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#199-来源几何与量子消费者的完整边界)第1、2、3、4、5、6、7项逐项全文，连同其完整援引的[定义194.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#194-新连接完整候选与量子消费者的范围)、[定义186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#186-七项原量子来源合同的准确消费者)及各项全部上游对象、条件和量词，均经本卷122.1、132.2完整合取纳入134–137。下表只标出接口，不替代这些完整原文。

| 全文合同地址与消费者 | 本组读取边界所保留的实际来源 |
| --- | --- |
| 199.2第1项、194.2第1行、186.1及全部上游：复Hilbert、可观察量、相干叠加 | 唯一原 $\Omega/\mathrm{native}$、全词同一 $K/J/q$、parent/ready、原可取得标签、合法控制及实际相干准备不变；辅助代数及GNS不供应全旧乘法或物理准备。 |
| 199.2第2项、194.2第2行、186.2及全部上游：原态、效果、质量、Born | 原事件、准确效果、全部实际完整菜单及接受归属不变；全部零、不等、次归一质量和中心／经典／不等维／静默部分保留，零质量不归一。原抽签、共同根、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定强度、P9、独立 $W_e$、全部中间切口和固定支持全质量仍各须来源。 |
| 199.2第3项、194.2第3行、186.3及全部上游：真正相关联合、native、张量 | 同一个实际非零相关联合、忠实同向交换局部腿、共同实现、联合生成分离、所需重数、全部相关输入、中央对、经典及不等维块和递归同源参考不变；矩阵两角和分别可达不替代联合。 |
| 199.2第4项、194.2第4行、186.4及全部上游：typed CP、Kraus、递归参考 | 原未归一回溯、typed前后接与反变复合、分区、全未来自然性和箭头商下降不变；整台系统环境、全部成功失败细记录及port/post-port输出、每份输出每个仍合法未来、三实际投影及支持内补、共同真实支持、相关正输入的intertwining与夹界、每个所需有限递归深度和累计支持准确运输仍须原桥。 |
| 199.2第5项、194.2第5行、186.5及全部上游：整台仪器、TP、更新、Lüders | 完整typed菜单、接受端、整个环境及全部输出未来、真分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词和接受条件不变；TP的完整单位分区、Lüders的同一完整输出射线校准、正常物理表示、指定前对偶及所需收敛不由正夹读产生。 |
| 199.2第6项、194.2第6行、186.6及全部上游：全部历史未来、真实返回、CountRead | 全部合法顺序、自适应、并行历史、每份输出每个仍合法未来、环境细记录泄漏、停止拒绝销毁、真遗忘、同数两侧与真实逆向双向返回不变；读后同一原完整活动输入、负提升两活路、相干聚合、完整原菜单、精确正生成 $B$ 与闭正生成 $B_{\rm cl}$、无限非离散记录及其可数可加、正常性、指定前对偶不由有限夹读供应。 |
| 199.2第7项、194.2第7行、186.7及全部上游：动力、物理钟、能量、共同尺度 | 保持可能不完备原域的流、实际相位和门序列、可逆一参数群、所需强连续酉实现、物理钟、生成元域、Hamiltonian能量、共同仪器及共同正 $\hbar$ 不变；原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 预算保持各自原义。 |

**定义 137.4（剩余的实际生产问题）。** 一般原 $K_y\delta_a(b,c)=0$ 的全部原 $a,b,c,y$ 量词、任意首标签、全旧 $D$ 恢复及完整量子起源目标仍保留。134.7没有给实际 $V_c(r)$ 的零预算；136.1没有给任意正映射闭包、普遍不可能性或有限见证数的界，也不排除其他有限、自适应、依缺陷选择的实际PB生产路线。所缺仍是从原关系取得能控制同一实际非对角余量的读取，或证明向能看见遗漏理想的非尖锐读取的运输，同时保留整个方差预算和同一实际输出。给缺口列出明确预算与非分离见证，不等于已经生产一般交换、一般(VP)、一般原行或任何物理来源。

直观上，尖锐读取把背景的一个高度看成确定值；夹读虽然能改变被读取的向量，却不能使一个双边理想跑出自身。在这份连续谱模型里，所有这样的尖锐读法都经过去掉紧理想的部分，因此任意多但有限的原夹乘与正和仍看不见其中的测试元。正常的非尖锐见证能够看见它，代价是第二平方预算不能被默认为零。这定位了读取路线的缺口，没有把一般原世界压成有限矩阵、补成完备物理域或宣告完整量子起源已经完成。

## 追加锚（本行以下为增补区）

## 138. 一般原平方局域化与固定的真加性缺陷

**定义 138.1（一般原候选与不变的检测对象）。** 完整采用[三角续卷128.1–128.2、129.1、183.1、240.1及248.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)的同一原 $\Omega/\mathrm{native}$、$E,C,u,N,\mathcal P,S,D$、A1–A3、准确锥、全部原P2及全部原三元组的FULLPB。$S=\circ$，$E$ 是自身含单位JB完成 $X$ 中稠密的含单位实Jordan子代数，$C=E\cap X_+$、$N=\|\cdot\|_X|_E$。全部零、不等、次归一质量保留。$E$ 允许不完备、无限维、无原子或不可分。消费248.1已付的忠实、含单位、等距且反映锥的JC包含 $j:X\to A_{\rm sa}$；以下省略 $j$，但不要求 $X=A_{\rm sa}$，也不要求 $E+iE$ 对环境结合乘法闭合。

任意固定原 $a,b,c,y\in E$，始终保持

$$
\begin{gathered}
s=b+c,\qquad d_s=D(a,s),\quad d_b=D(a,b),\quad d_c=D(a,c),\\
\delta=\delta_a(b,c)=d_s-d_b-d_c,\\
w=K_y(\delta)=\delta\circ y^2-y\circ(\delta\circ y).
\end{gathered}
\tag{138.1}
$$

一般目标仍是全部原 $a,b,c,y$ 的 $w=0$。不增加第一实际 $h,e,Q$ 框架；118或134的额外框架不是本节前件。旧 $D:E^2\to E$ 不预设可加、齐次、连续、可测、协变、商下降、单位平移或完成延拓。环境结合表达式只用于读取已定义的原Jordan元素，不定义新的响应。

**定义 138.2（作为中间工具的原正平方供应）。** 若固定 $w\ne0$，成熟态分离给 $X$ 的纯JB态 $\beta$ 使 $\beta(w^2)>0$。对任意这样的 $\beta$，直接复用三角续卷183证明中的(183.4)、有界强稠密性和原平方逼近，以及[中央续卷174.8–174.10](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#174-原交换第二输入的整个零行)的相同逼近工具。它们供应最小支撑 $p\in X^{**}$ 和原收缩元网 $e_i\in E$，使

$$
\begin{gathered}
U_p(t)=\beta(t)p\quad(t\in X),\qquad \beta(p)=1,\\
q_i=e_i^2\in E,\qquad 0\le q_i\le u,\qquad
q_i\longrightarrow p\quad\text{有界强收敛}.
\end{gathered}
\tag{138.2}
$$

这里 $U_z(t)=2z\circ(z\circ t)-z^2\circ t$；在JC包含中等于 $ztz$，在原域上保正并返回原域。收缩元的选择使用已引单位球强稠密性，再以 $E$ 的范数稠密性逼近并缩回单位球；平方仍是原运算。有界乘法的强连续性给最后的收敛。采用网，不将不可分情形压成序列。此处只引用成熟支撑与密度作下文应用的供应，不另立支撑或密度定理。

取 $\beta$ 到 $A$ 的一个正的态延拓 $\phi$，此处“态”指质量一的数学正泛函，不要求正常性；它在双对偶上有正常延伸。正的保单位子空间态延拓已足够，不使用延拓的纯性或不可约性。在其GNS表示中令 $\|\xi\|=1$，并令 $P$ 为 $p$ 经双对偶Jordan包含和该表示的正常延伸所得投影。支撑关系给

$$
P\xi=\xi,\qquad P tP=\beta(t)P,\qquad
P t\xi=\beta(t)\xi\quad(t\in E).
\tag{138.3}
$$

$P$ 不必是环境秩一投影。强半范数包括每个原 $z$ 对应的正泛函 $\beta\circ U_z$；在省略表示符号的记法下，$\|(q_i-P)z\xi\|^2=\beta^{**}(U_z((q_i-p)^2))\to0$，所以(138.2)给 $q_i z\xi\to Pz\xi$。特别，同一网可控制 $\xi,a\xi,b\xi,c\xi,y\xi,d_s\xi,d_b\xi,d_c\xi,w\xi$ 及任意指定的有限原向量表。$p,P$ 均不送入 $D$；没有将根、投影、极限或环境有限矩阵框架添入 $E$。

对每个原 $z$，$\beta\circ U_z$ 是三角续卷129.1许可的数学正读取，实际质量是 $\beta(z^2)$，包括零。特别

$$
\psi_i=\beta\circ U_{q_i},\qquad
\psi_i(u)=\beta(q_i^2)\in[0,1].
\tag{138.4}
$$

不除以这个质量。数学态、GNS向量及这些读取均不供应物理准备。$X=0$ 或 $w=0$ 时无需选择检测态；后续有限PB等式和全部正读取预算仍适用。

## 139. 三张实际PB的有符号返回与六项预算

**定理 139.1（保留辅助缺陷的同一三调用恒等式）。** 在138.1下，取(138.2)的任一原 $q_i$。按顺序使用三次实际调用

$$
\mathrm{PB}(s;a,q_i),\qquad
\mathrm{PB}(b;a,q_i),\qquad
\mathrm{PB}(c;a,q_i),
\tag{139.1}
$$

其中记号 $\mathrm{PB}(t;a,q_i)$ 的首槽演员是 $t$，另两槽依次是 $a,q_i$。对这个有重数的三项表 $t=s,b,c$ 定义

$$
\begin{aligned}
f_{ti}&=D(t,q_i),&
v_{ti}&=-d_t-t\circ q_i,& z_{ti}&=t\circ a+f_{ti},\\
A_{ti}^\pm&=a\pm v_{ti},&
B_{ti}^\pm&=q_i\pm z_{ti},&
O_{ti}^\pm&=D(A_{ti}^\pm,B_{ti}^\pm),\\
\eta_i&=f_{si}-f_{bi}-f_{ci}
=-\delta_{q_i}(b,c).
\end{aligned}
\tag{139.2}
$$

则准确有

$$
\boxed{
O_{si}^+-O_{si}^- -O_{bi}^++O_{bi}^- -O_{ci}^++O_{ci}^-
=2a\circ\delta-2q_i\circ\eta_i.}
\tag{139.3}
$$

三张表的系数依次为 $+1,-1,-1$；即使 $b=c$ 或有其他输入重合，仍保留全部六个输出occurrence及其重数，不将有重数表改成集合。

证明。原P2给反对称性，所以 $D(t,a)=-d_t$。三角续卷(128.6)逐次应用于(139.1)，准确给

$$
O_{ti}^+-O_{ti}^-
=-2a\circ v_{ti}-2q_i\circ z_{ti}
=2a\circ d_t+2a\circ(t\circ q_i)
 -2q_i\circ(t\circ a)-2q_i\circ f_{ti}.
\tag{139.4}
$$

以系数 $+1,-1,-1$ 相加，已知Jordan乘法的实双线性及 $s=b+c$ 消去两个混合乘积和，得到(139.3)。未将任何 $d_t$、$f_{ti}$ 或外层旧输出对输入和拆开；$\eta_i$ 是保留的实际辅助加性缺陷。∎

**推论 139.2（任意质量的实际六预算）。** 对任意数学正实线性读取 $\psi:E\to\mathbb R$，定义六个实际Gram预算

$$
\Gamma_{ti}^\pm(\psi)
=\psi((A_{ti}^\pm)^2)\psi((B_{ti}^\pm)^2)
 -\psi(A_{ti}^\pm\circ B_{ti}^\pm)^2\ge0.
\tag{139.5}
$$

则

$$
\begin{aligned}
2\bigl|\psi(a\circ\delta-q_i\circ\eta_i)\bigr|
\le{}&\sqrt{\Gamma_{si}^+(\psi)}+\sqrt{\Gamma_{si}^-(\psi)}\\
 &+\sqrt{\Gamma_{bi}^+(\psi)}+\sqrt{\Gamma_{bi}^-(\psi)}\\
 &+\sqrt{\Gamma_{ci}^+(\psi)}+\sqrt{\Gamma_{ci}^-(\psi)}.
\end{aligned}
\tag{139.6}
$$

证明。三角续卷129.1将同一原P2交给任意正读取，对六个实际输出逐个给 $|\psi(O_{ti}^\pm)|\le\sqrt{\Gamma_{ti}^\pm(\psi)}$；再对(139.3)用三角不等式。不归一化 $\psi$，其质量可为任意非负数；零质量由序单位界使 $\psi=0$，两边同为零。质量缩放使每个 $\Gamma$ 按质量平方缩放，故次归一和不等质量也原样包含。特别适用于全部 $\beta\circ U_z$ 及(138.4)的实际质量。∎

**推论 139.3（实际输入与输出的一致范数界）。** 记

$$
M_t=\|a\|+\|t\|(\|a\|+1),\qquad
L_t=1+\|t\|(\|a\|+1),\qquad
T=\|s\|+\|b\|+\|c\|.
$$

对全部 $i$、$t=s,b,c$ 及两个符号，有

$$
\begin{gathered}
\|d_t\|\le\|a\|\|t\|,\quad
\|f_{ti}\|\le\|t\|,\quad
\|A_{ti}^\pm\|\le M_t,\quad
\|B_{ti}^\pm\|\le L_t,\quad
\|O_{ti}^\pm\|\le M_tL_t,\\
\|\eta_i\|\le T,\qquad
\|\delta\|\le\|a\|T,\qquad
\|w\|\le2\|y\|^2\|a\|T.
\end{gathered}
\tag{139.7}
$$

证明。对任意原 $x,z$，质量一的数学正泛函读取P2给 $|\rho D(x,z)|\le\|x\|\|z\|$；全态取范数得到 $\|D(x,z)\|\le\|x\|\|z\|$。结合 $\|q_i\|\le1$、Jordan乘积的范数界及(139.2)逐项得到结论。这些态无需算子代数正常性。范数界没有给 $\eta_i$ 或任一输出的衰减；(139.3)返回的是带辅助缺陷的 $a\circ\delta$，尚不是 $K_y(\delta)$。∎

## 140. 方差预算的极限、横向Jordan作用与夹读稳定性

**定理 140.1（状态保持局域化的定量预算）。** 固定138.2–138.3的数学态及其同一局域化网。对任意固定原 $t$，令

$$
\varepsilon_i=\|(q_i-u)\xi\|\longrightarrow0,\qquad
\operatorname{Var}_\beta(t)=\beta(t^2)-\beta(t)^2,
$$

并保留实际内值 $f_{ti}=D(t,q_i)$ 的P2上预算

$$
G_i(t)=\beta(t^2)\beta(q_i^2)-\beta(t\circ q_i)^2.
\tag{140.1}
$$

则

$$
|\beta(f_{ti})|^2\le G_i(t),\qquad
\boxed{\ |G_i(t)-\operatorname{Var}_\beta(t)|
\le\|t\|^2(4\varepsilon_i+\varepsilon_i^2).\ }
\tag{140.2}
$$

同一表示中的两种作用有不同极限：

$$
\begin{aligned}
(t\circ q_i)\xi&\longrightarrow
\tfrac12\bigl(t\xi+\beta(t)\xi\bigr),\\
U_{q_i}(t)\xi&\longrightarrow\beta(t)\xi,\\
\|(t\circ q_i)\xi-\beta(t)\xi\|
&\longrightarrow\tfrac12\sqrt{\operatorname{Var}_\beta(t)}.
\end{aligned}
\tag{140.3}
$$

此外，对任意一致有界的原自伴元网 $H_i$，即使它是随 $i$ 改变的实际旧输出，仍有

$$
\boxed{\ |\beta(U_{q_i}(H_i))-\beta(H_i)|
\le2\varepsilon_i\|H_i\|.\ }
\tag{140.4}
$$

证明。置 $\mu=\beta(t)$、$r_i=\beta(t\circ q_i)$、$m_i=\beta(q_i^2)$。GNS的实内积及收缩性给

$$
|m_i-1|\le2\varepsilon_i,\qquad
|r_i-\mu|\le\|t\|\varepsilon_i,\qquad
|\mu|\le\|t\|.
$$

故 $|r_i^2-\mu^2|\le\|t\|^2(2\varepsilon_i+\varepsilon_i^2)$；代入 $G_i(t)-\operatorname{Var}_\beta(t)=\beta(t^2)(m_i-1)-(r_i^2-\mu^2)$ 即得(140.2)。这是实际P2预算的估计，不是对未知输出作连续性假设。

(138.3)及有界强收敛给 $tq_i\xi\to t\xi$、$q_it\xi\to\beta(t)\xi$，故Jordan作用趋于二者的平均。再用 $q_itq_i\xi\to\beta(t)\xi$ 得二次表示的极限。最后 $\|t\xi-\mu\xi\|^2=\operatorname{Var}_\beta(t)$，得到横向项的准确范数。这里没有把Jordan乘法替换成单侧结合压缩。

对变动的自伴 $H_i$，直接比较同一有界算子的两次向量读取：

$$
\begin{aligned}
|\beta(U_{q_i}(H_i))-\beta(H_i)|
&=|\langle q_i\xi,H_iq_i\xi\rangle-\langle\xi,H_i\xi\rangle|\\
&\le\|H_i\|\,\|q_i\xi-\xi\|\,(\|q_i\xi\|+1)
\le2\varepsilon_i\|H_i\|.
\end{aligned}
$$

只用 $\|q_i\|\le1$，不对 $H_i$ 或 $D$ 取极限，不使用固定态下夹心的循环性或交换性。∎

**推论 140.2（上预算与实际响应的区别）。** 对 $t=s,b,c$，(140.4)和(139.7)同时适用于全部 $f_{ti}$、$\eta_i$ 及全部六个 $O_{ti}^\pm$。因此这些有界实际输出在 $\beta\circ U_{q_i}$ 下的读取与在 $\beta$ 下的读取之差一致趋零；这没有使其读取本身趋零。若 $\operatorname{Var}_\beta(t)>0$，(140.2)使 $G_i(t)$ 最终至少为该方差的一半，定位了该项P2上预算的不消失部分。这是上预算的正极限，绝不是 $|\beta(f_{ti})|$ 或任一响应的正下界。六个外预算及 $\eta_i$ 仍须按(139.2)、(139.5)保留；本结论没有生产 $\beta(w^2)\le C\varepsilon_i$，也未把(139.6)变成检测器的零预算。

## 141. 全数学PB下的零误差Pauli诊断与原目标边界

**命题 141.1（精确状态保持不强迫单个实际外输出消失）。** 存在满足138.1全部数学A1–A3、P2及所有三元组FULLPB的候选，及已经属于原域的正收缩局域化子，使全部局域化误差为零，而(139.1)中的实际单个外输出及其读取不为零。这里精确否定的只是由状态保持局域化本身推出逐输出压零的无条件推断。

证明。取

$$
E=X=M_2(\mathbb C)_{\rm sa},\quad
C=M_2(\mathbb C)_+,\quad u=I,\quad N=\|\cdot\|,
\quad S(A,B)=A\circ B,\quad D(A,B)=\tfrac i2[A,B],
\tag{141.1}
$$

原评价族取全部正实线性泛函及其全部非负质量倍数。它分离原域并准确决定锥。此处是[静态重构卷35.1–35.2](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md#35-全输入缩放交换子族的精确缺陷)、本卷130.4和135.1–135.2既有标准模型的参数对应，不另作分类或新模型供应定理。完整对应如下：

- A1：$S(A,B)-iD(A,B)=AB$，故每张实际有向二表是同一正泛函的复Gram表；$\alpha(V^*V)\ge0$ 给其正性。
- A2：相加三表及其每个排列的实部是实Gram表；原指定向量 $(1,-1,-1)$ 对应 $(A+B)-A-B=0$，准确给零二次值。
- A3：$S(u,u)=u$。对原固定有理 $0<\theta\le1$ 及全部 $0\le e\le\theta u$，效果谱演算给 $S(e,e)=e^2\le e$。
- P2：C*的Cauchy–Schwarz给 $|\alpha(AB)|^2\le\alpha(A^2)\alpha(B^2)$，其中 $\alpha$ 对 $AB$ 使用其正的复线性延伸，且 $\alpha(AB)=\alpha(A\circ B)-i\alpha D(A,B)$。因此原二表及其完整Gram行列式预算成立；不除以质量，零及次归一读取也包含。
- FULLPB：直接消费135.2的全三元组端点分解。任意原演员 $H$ 和原 $B,C$，置 $\mathcal Z=B+iC$、$v=D(H,B)-H\circ C$、$z=H\circ B+D(H,C)$，则

$$
\begin{gathered}
\mathcal Q(B,C)=B^2+C^2+2D(B,C)=\mathcal Z^*\mathcal Z,\qquad
v+iz=iH\mathcal Z,\\
(B\pm v)+i(C\pm z)=(I\pm iH)\mathcal Z,\\
\mathcal Q(B\pm v,C\pm z)=\mathcal Z^*(I+H^2)\mathcal Z.
\end{gathered}
\tag{141.2}
$$

两端是同一元素，故对全部原三元组、全部正读取和全部质量成立。这里复用的是标准模型的全PB恒等式，不是仅满足自作用或单位第三标签的子系统。

采用通常的Pauli矩阵

$$
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
$$

保持(138.1)的原对象，具体取

$$
\begin{gathered}
a=b=\sigma_x,\qquad c=y=\sigma_z,\qquad s=\sigma_x+\sigma_z,\\
\beta(T)=T_{11},\qquad \xi=(1,0)^T,\qquad
q_i=p=(u+\sigma_z)/2\quad\text{对全部 }i.
\end{gathered}
\tag{141.3}
$$

$pTp=\beta(T)p$ 对全部 $T$ 成立，$p\xi=\xi$，所以(138.2)–(138.3)的局域化在原域内已经准确，$\varepsilon_i=0$。固定的实际内值为

$$
\begin{gathered}
d_s=d_c=\sigma_y,\qquad d_b=0,\qquad
f_{si}=f_{bi}=\sigma_y/2,\qquad f_{ci}=0,\\
\delta=0,\qquad w=0,\qquad\eta_i=0.
\end{gathered}
\tag{141.4}
$$

在同一三张表上按(139.2)逐项保留所有六个实际外输出，得到

| 实际调用的 $t$ occurrence | $O_{ti}^+$ | $O_{ti}^-$ |
| --- | --- | --- |
| $s=b+c$，系数 $+1$ | $(\sigma_x+\sigma_y-\sigma_z)/4$ | $3(-\sigma_x+\sigma_y+\sigma_z)/4$ |
| $b=a$，系数 $-1$ | $(\sigma_y-\sigma_z)/4$ | $3(\sigma_y+\sigma_z)/4$ |
| $c=y$，系数 $-1$ | $(\sigma_x+\sigma_y)/2$ | $(-\sigma_x+\sigma_y)/2$ |

这些值只用 $\sigma_j\sigma_k=\delta_{jk}u+i\sum_l\epsilon_{jkl}\sigma_l$ 和(141.1)相乘。特别，$t=b=a$ 的同一次实际PB具有

$$
\begin{gathered}
v_{bi}=-a/2,\qquad z_{bi}=u+\sigma_y/2,\\
A_{bi}^+=a/2,\quad B_{bi}^+=p+u+\sigma_y/2,\qquad
A_{bi}^-=3a/2,\quad B_{bi}^-=p-u-\sigma_y/2,\\
\beta(O_{bi}^+)=-1/4,\qquad
\beta(O_{bi}^-)=3/4,\qquad
\beta(O_{bi}^+-O_{bi}^-)=-1.
\end{gathered}
\tag{141.5}
$$

两项决定性的实际P2预算为

$$
\begin{aligned}
\beta((A_{bi}^+)^2)&=1/4,&
\beta((B_{bi}^+)^2)&=17/4,&
\beta(A_{bi}^+\circ B_{bi}^+)&=0,\\
\beta((A_{bi}^-)^2)&=9/4,&
\beta((B_{bi}^-)^2)&=1/4,&
\beta(A_{bi}^-\circ B_{bi}^-)&=0,\\
\Gamma_{bi}^+(\beta)&=17/16,&&
\Gamma_{bi}^-(\beta)=9/16.&&
\end{aligned}
\tag{141.6}
$$

因此即使误差恒为零，这两个实际输出的读取也不趋零；$\beta\circ U_p$ 在这些输出上与 $\beta$ 相同。另一方面，全部三次差值分别为 $\sigma_x-\sigma_y/2-\sigma_z$、$-\sigma_y/2-\sigma_z$、$\sigma_x$，按 $+1,-1,-1$ 相加正好为零，准确符合(139.3)。内层亦有 $G_i(b)=\operatorname{Var}_\beta(b)=1$ 而 $\beta(f_{bi})=0$，直接展示正的上预算不是响应下界。∎

**定义 141.2（非蕴涵的准确范围与承重来源）。** 141.1中的目标是 $\delta=w=0$，并非非零检测器模型。它没有给出满足 $\beta(w^2)>0$ 的反例，因而不反驳使用非零检测态条件的路线，也不反驳先保留相同实际输出作跨调用有符号相消的路线。被否定的恰是仅凭状态保持正局域化，就将这些单个实际外输出逐一当作趋零误差的无条件规则。一般 $D$ 的可加性、任意首标签识别、全原 $K_y(\delta_a(b,c))=0$ 及完整量子起源仍未由139–141支付。

本组承重属于 $\texttt{repo-derived}$ 应用：原平方供应接到三张实际PB的精确返回、六预算、横向方差项与全数学PB的零误差诊断。三角续卷183–184的纯态支撑和原平方逼近、240/248的整个JC包含、129.1的正读取及本卷135.2的标准端点分解均直接复用。成熟支撑来源是Hamhalter，[*Pure states on Jordan algebras*](https://dml.cz/handle/10338.dmlcz/133911)，§1，第83页，DOI 10.21136/MB.2001.133911；有界强稠密和乘法连续性取Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)，4.1.9、4.4.3、4.5.12。正的态延拓及GNS取137.2已引Blackadar的态延拓接口；这里不要求纯延拓。上述成熟结论只作为中间工具，不计为新贡献；不主张新分类、历史优先权或文献穷尽。[谱混合卷79–87](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md#79-完整有限-continuous-原域与中央取向候选)已支付的完整有限连续类识别亦不在这里重做或宣称仍未解。

**定义 141.3（全部上游七合同与仍缺的原返回）。** 将137.3及其全文引用的中央续卷199.2第1–7项、194.2、186.1–186.7和每项全部上游对象、条件与量词，逐项全文、无删减地合取纳入138–141；该引用不以任何摘要替代原文。唯一原 $\Omega/\mathrm{native}$、全词 $K/J/q/u/N/\mathcal P/S/D$、parent/ready、原可取得标签与合法控制保持；全部零、不等、次归一质量、中心、经典、不等维及静默块保持。数学态与读取不新增原准备、实际完整菜单、接受归属、共同记录、真正分组遗忘、完整仪器及其全部系统环境和成功／失败／细记录／port／post-port输出，亦不新增真正相关联合或每个所需递归深度的同源参考。全部合法顺序／自适应／并行历史、每个输出每个仍合法未来、环境泄漏、停止／拒绝／销毁、同数两侧与真实逆向双向返回保持。CountRead、精确正生成 $B$ 与闭正生成 $B_{\rm cl}$、无限非离散记录、可数可加、正常性及指定前对偶各守原来源；物理钟、流保持原不完备域、能量、共同仪器、共同正 $\hbar$、原固定域、resolvent及预算也各守原合同。

一般原目标仍须在同一 $a,b,c,y,d_s,d_b,d_c,\delta,w$ 上，生产有检测力的实际PB返回和预算，而不是新增公理、局域化供应者或将等价目标换名。若进一步采用两向量或矩阵式标签，仍须同时支付所需标签确属原 $E$ 的供应，以及保留 $\eta_i$ 与全部六个实际输出后的相消和返回；环境中可插值不等于原Jordan域内可取得。139.3没有允许丢弃 $q_i\circ\eta_i$，140.2没有给检测平方的零预算，141.1也不排除依赖非零 $w$、非状态保持读取或其他相关相消的生产路线。

## 追加锚（本行以下为增补区）

## 142. 固定实权重的实际演员差与共同运输条件

**定义 142.1（完整测试域与原配平的约定）。** 本组的一般原目标仍取138.1及141.3的全部前件、来源和量词。只为检验一条普遍的块运输规则，另取一个给定含单位复C*代数 $\mathcal M$ 的完整自伴原域

$$
E_{\rm test}=\mathcal M_{\rm sa},\qquad u=1,\qquad
x\circ z=(xz+zx)/2,\qquad D(x,z)=i[x,z]/2.
\tag{142.1}
$$

这里和下文的每个嵌套 $D$ 都是这一份总映射的值。原评价可取全部正泛函限制及其全部非负质量倍数，不将数学正泛函认作物理准备。本卷135.2、141.1及[半有限卷SF98.3、SF103.1](AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md#103-每个中央取向的反向静态后果与可积域)已给标准模型的完整数学对应：$x\circ z-iD(x,z)=xz$，全部有限复Gram正性给原二表和P2，相加实Gram给A2及全部排列的指定零向量，效果平方给同一个有理小窗A3。对全部原三元组的FULLPB亦已成立。这些既有模型事实只作为下文应用的前件，不是新增分类。

为不混淆元素与正读取，写

$$
\begin{aligned}
\mathcal Q(x,z)&=x^2+z^2+2D(x,z)=(x+iz)^*(x+iz),\\
\mathrm{PB}(a;x,z):\quad
v&=D(a,x)-a\circ z,\qquad k=a\circ x+D(a,z),\\
(x^\epsilon,z^\epsilon)&=(x+\epsilon v,z+\epsilon k),\qquad
Z=x+iz,\quad Z^\epsilon=(1+\epsilon ia)Z,
\quad\epsilon\in\{1,-1\}.
\end{aligned}
\tag{142.2}
$$

每个单调用满足 $\mathcal Q(x^+,z^+)=\mathcal Q(x^-,z^-)=Z^*(1+a^2)Z$。这是同一调用两端的相等，不是它们与 $\mathcal Q(x,z)$ 相等，也没有给不同调用的交叉项配平。$\mathcal Q$ 的正性是完整测试域中的结论；对一般原 $D$ 不由此加入输出平方正性或响应线性。

**定理 142.2（实际块的固定标量权重判据，作为循环障碍的中间计算）。** 固定有限个自伴演员 $a_1,\ldots,a_n$ 和实数 $c_1,\ldots,c_n$。对于任意独立选择的原列 $Z_l=x_l+iz_l\in\mathcal M$，令

$$
U^\epsilon=\sum_{l=1}^n c_l(1+\epsilon ia_l)Z_l.
$$

则有准确元素恒等式

$$
\boxed{(U^+)^*U^+-(U^-)^*U^-
=2i\sum_{l,m=1}^n c_lc_m Z_l^*(a_m-a_l)Z_m.}
\tag{142.3}
$$

对每份独立原列选择都配平，当且仅当全部活动演员相同，即

$$
\bigl[(U^+)^*U^+=(U^-)^*U^-\text{ 对所有 }Z_1,\ldots,Z_n\bigr]
\quad\Longleftrightarrow\quad
\bigl[a_l=a_m\text{ 只要 }c_lc_m\ne0\bigr].
\tag{142.4}
$$

证明。置 $S=\sum_lc_lZ_l$、$A=\sum_lc_la_lZ_l$，则 $U^\epsilon=S+\epsilon iA$，直接相乘给

$$
(U^+)^*U^+-(U^-)^*U^-
=2i(S^*A-A^*S)
=2i\sum_{l,m}c_lc_mZ_l^*(a_m-a_l)Z_m.
$$

对角项为零，活动演员相同时其余项也为零。反之，取两个活动指标 $l,j$，令 $h=a_j-a_l=h^*$，选择真正原列

$$
Z_l=c_l^{-1}1,\qquad Z_j=c_j^{-1}ih,\qquad Z_k=0\ (k\notin\{l,j\}).
$$

完整自伴原域保证这都是合法复坐标。两项交叉和为

$$
2i\{1^*h(ih)+(ih)^*(-h)1\}=-4h^2.
$$

若普遍配平，便有 $h^2=0$；C*范数恒等式给 $h=0$。空活动支撑及单点活动支撑的条件均为真，零权重的演员完全不受约束；负权重已由上面实数公式包含。未对未知函数作极化；极化只用于已知的结合平方。∎

同一中间计算允许一个明确的中央约定：若 $J\in Z(\mathcal M)$、$J^*=-J$、$J^2=-1$，取 $D_J(x,z)=J[x,z]/2$、$Z=x+Jz$。每个 $Z\in\mathcal M$ 的唯一自伴坐标为 $x=(Z+Z^*)/2$、$z=-J(Z-Z^*)/2$，且 $\mathcal Q_J=Z^*Z$、$Z^\epsilon=(1+\epsilon Ja)Z$。式(142.3)中 $i$ 全部换成 $J$；必要性选择 $Z_j=Jh/c_j$，仍得 $-4h^2$。此处只断言完整域、中央 $J$ 及实标量权重下的这个恒等式和判据。

142.4量化独立原列，并不把下文由同一旧表生成的六列当作独立。因此它本身还不足以判定实际循环；143–144保留循环的全部依赖后直接计算。

## 143. 同一总响应生成的三循环与六张配对调用

**定义 143.1（原三调用及其字面关联）。** 在142.1的测试类中，固定原 $A,B,y$，先读取同一份

$$
O=D(A,B),\qquad G=D(A,y),\qquad J_0=D(B,y).
$$

对每个 $\tau\in\{1,-1\}$，取三张实际原调用 $\mathrm{PB}(A;B,y)$、$\mathrm{PB}(B;y,A)$、$\mathrm{PB}(y;A,B)$ 的同一个 $\tau$ 端点：

$$
\begin{aligned}
R_1&=B+\tau(O-A\circ y),& S_1&=y+\tau(A\circ B+G),\\
R_2&=y+\tau(J_0-B\circ A),& S_2&=A+\tau(B\circ y-O),\\
R_3&=A+\tau(-G-y\circ B),& S_3&=B+\tau(y\circ A-J_0).
\end{aligned}
\tag{143.1}
$$

$J_0$ 是实际旧回复，不是142的中央 $J$。下文所有指标模三，$R_4=R_1,S_4=S_1$；$\tau$ 暂省于下标。再读取

$$
M_j=D(R_j,S_j),\qquad K_j=D(R_j,S_{j+1})\qquad(j=1,2,3).
\tag{143.2}
$$

接着的六张调用及两个符号的全部端点为

$$
\begin{aligned}
\mathsf X_j&=\mathrm{PB}(R_j;S_j,S_{j+1}),\\
X_j^\epsilon&=\bigl(S_j+\epsilon(M_j-R_j\circ S_{j+1}),
S_{j+1}+\epsilon(R_j\circ S_j+K_j)\bigr),\\
\mathsf Y_j&=\mathrm{PB}(S_{j+1};R_{j+1},R_j),\\
Y_j^\epsilon&=\bigl(R_{j+1}+\epsilon(-M_{j+1}-R_j\circ S_{j+1}),
R_j+\epsilon(S_{j+1}\circ R_{j+1}-K_j)\bigr),\\
N_j^\epsilon&=D((X_j^\epsilon)_1,(X_j^\epsilon)_2),\qquad
Z_j^\epsilon=D((Y_j^\epsilon)_1,(Y_j^\epsilon)_2).
\end{aligned}
\tag{143.3}
$$

第二调用的内回复正是 $D(S_{j+1},R_{j+1})=-M_{j+1}$ 与 $D(S_{j+1},R_j)=-K_j$，不是新选的自由量。相同的 $M_j,K_j$ 在相邻调用中保持字面同一；输入偶然相等时，同一总 $D$ 也必须给相同值。全部零标签、重复标签及其出现重数都保留。

**定理 143.2（全部三参数、两个循环符号的实际回复）。** 取任意给定非零 $\mathrm{II}_1$ 因子 $\mathcal R$ 及其忠实正规归一有限迹 $\operatorname{tr}_{\mathcal R}$，令

$$
\mathcal M=M_2(\mathbb C)\,\overline\otimes\,\mathcal R,
\qquad E_{\rm test}=\mathcal M_{\rm sa},\qquad
(A,B,y)=(\alpha\sigma_x,\beta_0\sigma_y,\gamma\sigma_z),
\quad\alpha,\beta_0,\gamma\in\mathbb R.
\tag{143.4}
$$

横线张量积是von Neumann张量积；每个Pauli矩阵均指其与 $1_{\mathcal R}$ 的张量。$\mathcal M$ 仍是 $\mathrm{II}_1$ 因子，归一迹为 $\tfrac12\operatorname{Tr}_2\otimes\operatorname{tr}_{\mathcal R}$，故没有非零type I中央直和项。这是SF98、SF103的完整continuous类的 $Q=1$ 标准取向实例。$\beta_0$ 是本条的实参数，与145的检测态 $\beta$ 区分。

实际旧回复及三个端点准确为

$$
\begin{gathered}
O=-\alpha\beta_0\sigma_z,\qquad
G=\alpha\gamma\sigma_y,\qquad J_0=-\beta_0\gamma\sigma_x,\\
R_1=\beta_0\sigma_y-\tau\alpha\beta_0\sigma_z,\qquad
S_1=\gamma\sigma_z+\tau\alpha\gamma\sigma_y,\\
R_2=\gamma\sigma_z-\tau\beta_0\gamma\sigma_x,\qquad
S_2=\alpha\sigma_x+\tau\alpha\beta_0\sigma_z,\\
R_3=\alpha\sigma_x-\tau\alpha\gamma\sigma_y,\qquad
S_3=\beta_0\sigma_y+\tau\beta_0\gamma\sigma_x.
\end{gathered}
\tag{143.5}
$$

为同时列出全部进一步回复，写 $a_1=\alpha,a_2=\beta_0,a_3=\gamma$，$\sigma_1=\sigma_x,\sigma_2=\sigma_y,\sigma_3=\sigma_z$。对任意循环指标 $j$，置

$$
p=a_j,\quad q=a_{j+1},\quad r=a_{j+2},\qquad
d_j=p^2q^2,\quad F_j=1+q^2(1+p^2),\quad G_j=1+p^2(1+q^2).
$$

则无除法的全部公式是

$$
\begin{aligned}
R_j&=q\sigma_{j+1}-\tau pq\sigma_{j+2},&
S_j&=r\sigma_{j+2}+\tau pr\sigma_{j+1},\\
R_j\circ S_j&=0,& R_j\circ S_{j+1}&=-d_j1,\\
M_j&=-qr(1+p^2)\sigma_j,\\
K_j&=-\tau pq^2\sigma_j+\tau p^2q\sigma_{j+1}+pq\sigma_{j+2},\\
X_j^\epsilon&=(S_j+\epsilon(M_j+d_j1),\ S_{j+1}+\epsilon K_j),\\
Y_j^\epsilon&=(R_{j+1}+\epsilon(-M_{j+1}+d_j1),\ R_j-\epsilon K_j),\\
N_j^\epsilon
&=-p^2qr\sigma_j-prF_j\sigma_{j+1}
 +\tau p^2rF_j\sigma_{j+2}-\epsilon d_jS_j,\\
Z_j^\epsilon
&=qrG_j\sigma_j+pq^2r\sigma_{j+1}
 +\tau q^2rG_j\sigma_{j+2}-\epsilon d_jR_{j+1}.
\end{aligned}
\tag{143.6}
$$

证明。对实向量 $v,w\in\mathbb R^3$，Pauli乘法给

$$
(v\cdot\sigma)\circ(w\cdot\sigma)=(v\cdot w)1,
\qquad D(v\cdot\sigma,w\cdot\sigma)=-(v\times w)\cdot\sigma.
\tag{143.7}
$$

原三元组的两两Jordan乘积为零；其三个叉积给143.5，再代入143.1。固定正循环顺序 $(j,j+1,j+2)$，$R_j,S_j$ 的向量是 $(0,q,-\tau pq)$、$(0,\tau pr,r)$，内积为零，负叉积为 $(-qr(1+p^2),0,0)$。$S_{j+1}$ 的向量是 $(p,0,\tau pq)$，故它与 $R_j$ 的内积为 $-p^2q^2$，负叉积为 $(-\tau pq^2,\tau p^2q,pq)$。这逐项给出内值和六张实际端点。

端点中的实标量单位项与一切交换，不影响旧响应。$X_j^\epsilon$ 两个坐标的向量依次为

$$
\begin{aligned}
v_X&=(-\epsilon qr(1+p^2),\ \tau pr,\ r),\\
w_X&=(p(1-\epsilon\tau q^2),\ \epsilon\tau p^2q,\ pq(\tau+\epsilon)).
\end{aligned}
$$

逐坐标计算负叉积得到

$$
-v_X\times w_X
=(-p^2qr,\ -prF_j-\epsilon\tau p^3q^2r,
\tau p^2rF_j-\epsilon p^2q^2r),
$$

正是 $N_j^\epsilon$。$Y_j^\epsilon$ 的向量依次为

$$
\begin{aligned}
v_Y&=(-\tau qr,\ \epsilon pr(1+q^2),\ r),\\
w_Y&=(\epsilon\tau pq^2,\ q(1-\epsilon\tau p^2),\ -pq(\tau+\epsilon)),\\
-v_Y\times w_Y
&=(qrG_j+\epsilon\tau p^2q^3r,\ pq^2r,
\tau q^2rG_j-\epsilon p^2q^2r),
\end{aligned}
$$

即所列 $Z_j^\epsilon$。因此所有十二个外回复都由同一个总 $D$ 实际算出，绝非先指定配平差再任意填表。作为符号和因子的另一核对，由这些式子直接有

$$
N_j^+-N_j^-=-2d_jS_j,\qquad
Z_j^+-Z_j^-=-2d_jR_{j+1}.
\tag{143.8}
$$

FULLPB右侧也分别给这两个值：第一张表的两项为 $-2S_j\circ(M_j+d_j1)-2S_{j+1}\circ K_j$，其中 $S_j\circ M_j=S_{j+1}\circ K_j=0$；第二张表用 $R_{j+1}\circ M_{j+1}=R_j\circ K_j=0$ 得同样结论。所有式子是对全部实参数和两个 $\tau$ 的多项式恒等式，不排除任何零值或重合。∎

## 144. 实际六列的非零混合漂移及三种聚合

**定理 144.1（整个实际三参数类的求和障碍）。** 对143.1–143.6的每个 $\tau$，写

$$
\begin{gathered}
L=\sum_{j=1}^3(R_j+S_j)
=2(\alpha\sigma_x+\beta_0\sigma_y+\gamma\sigma_z),\\
c_0=\alpha^2\beta_0^2+\beta_0^2\gamma^2+\gamma^2\alpha^2,\\
C_{\rm own}=\sum_j R_j\circ S_j=0,\qquad
C_{\rm cross}=\sum_jR_j\circ S_{j+1}=-c_0 1,\\
\mathcal B_\tau^\epsilon=\sum_{j=1}^3(X_j^\epsilon+Y_j^\epsilon).
\end{gathered}
$$

有序对按坐标相加，且

$$
\mathcal B_\tau^\epsilon=(L-2\epsilon C_{\rm cross},\ L+2\epsilon C_{\rm own})
=(L+2\epsilon c_0 1,L).
\tag{144.1}
$$

定义混合部分时扣除六张单表能量，准确取

$$
C_{{\rm mix},\tau}^\epsilon
=\mathcal Q(\mathcal B_\tau^\epsilon)
-\sum_{j=1}^3\{\mathcal Q(X_j^\epsilon)+\mathcal Q(Y_j^\epsilon)\}.
\tag{144.2}
$$

则

$$
\boxed{\ C_{{\rm mix},\tau}^+-C_{{\rm mix},\tau}^-
=\mathcal Q(\mathcal B_\tau^+)-\mathcal Q(\mathcal B_\tau^-)
=8c_0L.\ }
\tag{144.3}
$$

证明。143.5中的 $\tau$ 项按循环相消，给 $L$；143.6的Jordan内积给两个 $C$。一般地，143.3的第一坐标增量之和为

$$
\sum_j\{M_j-R_j\circ S_{j+1}-M_{j+1}-R_j\circ S_{j+1}\}
=-2C_{\rm cross},
$$

第二坐标为 $\sum_j\{R_j\circ S_j+K_j+S_{j+1}\circ R_{j+1}-K_j\}=2C_{\rm own}$。这里消掉的是同一实际 $M,K$ 的出现，不是把 $D$ 作用于一个和拆开。六张单表各由FULLPB给零漂移，所以144.2的差就是求和表能量之差。两坐标 $L+2\epsilon c_01,L$ 交换，实际回复 $D(L+2\epsilon c_01,L)=0$。故

$$
\mathcal Q(\mathcal B_\tau^\epsilon)
=(L+2\epsilon c_01)^2+L^2
=2L^2+4\epsilon c_0L+4c_0^21,
$$

取差得144.3。特别 $L^2=4(\alpha^2+\beta_0^2+\gamma^2)1$；$L=0$ 当且仅当三参数全零，而 $c_0=0$ 当且仅当至多一个参数非零。因此漂移非零恰在至少两个参数非零时。端点或回复之间的偶然相同不改变实际相加的重数，退化情形全部保留。∎

**推论 144.2（两个循环符号与读取约定）。** 两个 $\tau$ 各自的漂移都是 $8c_0L$。若先分别取能量再相加，漂移为 $16c_0L$；若对这两个能量取半和，漂移为 $8c_0L$；若把两个符号共十二个端点对先全部相加，再取一次能量，则

$$
\sum_{\tau=\pm1}\mathcal B_\tau^\epsilon
=(2L+4\epsilon c_01,2L),\qquad
\Delta\mathcal Q=32c_0L.
\tag{144.4}
$$

证明。前两项直接相加及除以二。最后的和等于 $2\mathcal B_\tau^\epsilon$；在当前已知标准响应中 $\mathcal Q(2x,2z)=4\mathcal Q(x,z)$，得到最后的因子。这里没有对一般未知 $D$ 使用齐次性。∎

元素不等与每份正读取不等须分开。置 $r_0=(\alpha^2+\beta_0^2+\gamma^2)^{1/2}$。非零漂移时 $r_0>0$，取 $2\times2$ 矩阵中 $\alpha\sigma_x+\beta_0\sigma_y+\gamma\sigma_z$ 的 $+r_0$ 单位特征向量 $v_+$，令

$$
\phi_+(T)=(\langle v_+,\cdot\,v_+\rangle\otimes\operatorname{tr}_{\mathcal R})(T).
$$

这是质量一的数学正读取，$\phi_+(8c_0L)=16c_0r_0>0$。负特征向量读取给相反号，归一迹读取则因 $L$ 无迹而给零。对任意 $m\ge0$，$m\phi_+$ 保持实际质量 $m$，读取为 $16mc_0r_0$；$m=0$ 时仍保留该零分支。因而反例是否被某份读取看见，不等于其算子漂移是否非零；尤其不能只用有限迹的零读数宣告块恒等式成立。

**定义 144.3（被否定规则的准确量词）。** 144.1否定的是所有实际三元组、全部参数与循环符号上，六张等权配对表的原始求和能量普遍零漂移。它在完整非零 $\mathrm{II}_1$ 测试类内已经失败；既有完整continuous分类并不修复这条规则。142.4则指出独立列普遍运输恰需要共同活动演员。二者不否定P2或FULLPB：此处它们对每个原输入和每个质量均成立。

这份标准响应本来可加，故任何真实加性缺陷 $\delta$ 及 $K_y\delta$ 都为零。没有把它作为非零真缺陷模型，也未断言143的三元组能够成为一份 $w\ne0$ 检测网络中的实际外层出现。没有排除依赖非零 $w$ 的条件预算、非线性或算子权重、特定原列的额外相消，尤其没有排除145的十二个外层出现按其 $\chi$ 权重共同相消。边界只撤去“单表配平或完整块正性足够推出这个普遍求和等距”的推理步骤；一般原目标的充分性与完整量子起源均不由此裁决。

## 145. 同一原检测器的两行锚定平方返回

**定义 145.1（一般原域、固定缺陷及全部十二个外出现）。** 返回138.1的一般原候选，不采用142.1的标准响应或完整自伴域限制。整个JB完成的忠实、含单位、等距且锥准确JC包含由三角续卷240–248支付；原 $E$ 仍可不完备、无原子、不可分，并只在自己的完成中稠密。不预付旧 $D$ 的可加、齐次、连续、协变、单位平移、输出闭合、商下降或完成延拓。

固定同一原 $a,b,c,y$。为保留重数，令 $\mathcal T=(s,b,c)$ 是一个出现表而非集合，其中 $s=b+c$，对应系数 $\kappa=(1,-1,-1)$。定义

$$
\begin{gathered}
r_\lambda=a+\lambda u,\quad \lambda\in\{0,1\},\qquad
d_{\lambda,t}=D(r_\lambda,t),\quad d_t=d_{0,t},\quad d'_t=d_{1,t},\\
\delta=\sum_{t\in\mathcal T}\kappa_td_t,\qquad
H=\sum_{t\in\mathcal T}\kappa_t(d'_t-d_t),\qquad
w=K_y(\delta)=\delta\circ y^2-y\circ(\delta\circ y).
\end{gathered}
\tag{145.1}
$$

$H$ 是两个实际加性缺陷之差，不置零，不将 $d'_t$ 换成 $d_t$。对每个原 $q\in E$，同一内回复 $f_t=D(t,q)$ 被两行共同使用。逐次调用 $\mathrm{PB}(t;r_\lambda,q)$，得到

$$
\begin{aligned}
v_{\lambda,t}&=-d_{\lambda,t}-t\circ q,&
z_{\lambda,t}&=t\circ r_\lambda+f_t,\\
A_{\lambda,t}^\epsilon&=r_\lambda+\epsilon v_{\lambda,t},&
B_{\lambda,t}^\epsilon&=q+\epsilon z_{\lambda,t},\\
O_{\lambda,t}^\epsilon&=D(A_{\lambda,t}^\epsilon,B_{\lambda,t}^\epsilon),&
\rho_{\lambda,t}&=(2\lambda-1)\kappa_t,\\
\chi_{\lambda,t,\epsilon}&=\rho_{\lambda,t}\epsilon,&
T(q)&=\sum_{\lambda,t,\epsilon}\chi_{\lambda,t,\epsilon}O_{\lambda,t}^\epsilon.
\end{aligned}
\tag{145.2}
$$

两个符号的和均遍历 $\{1,-1\}$。$D(t,r_\lambda)=-d_{\lambda,t}$ 是原P2的反对称性，未对旧响应作单位平移。$f_t$、相同的实际端点及实际外回复保持字面同一；即使 $s,b,c$ 或两行中的某些值重合，十二个出现仍各带原 $\rho,\chi$。每个外出现若再使用143.1的三循环，其 $O,G,J_0$ 和全部进一步回复也须是这一份总 $D$ 的实际值；不得用144的测试类表替代它们。

**定理 145.2（共同锚的平方功与保留 $H$ 的精确返回）。** 对同一个原锚 $g\in E$，只对已知Jordan平方定义

$$
\begin{aligned}
\mathcal S_g(A,B)&=(A-g)^2+B^2,\\
W_g(q)&=\sum_{\lambda,t}\rho_{\lambda,t}
\{\mathcal S_g(A_{\lambda,t}^+,B_{\lambda,t}^+)
-\mathcal S_g(A_{\lambda,t}^-,B_{\lambda,t}^-)\}.
\end{aligned}
\tag{145.3}
$$

所有 $\mathcal S_g$ 都是原正元素，$W_g$ 则是它们的有符号和。对全部原 $q,g$ 有

$$
W_g(q)=-2T(q)+4g\circ H.
\tag{145.4}
$$

在同一个准确锚 $g=r_1=a+u$ 上，还独立有

$$
\boxed{W_{a+u}(q)=-4\delta,\qquad
T(q)-2(a+u)\circ H=2\delta\quad(q\in E).}
\tag{145.5}
$$

证明。对每张实际PB，令 $\Delta O=O^+-O^-$。原有限差分和已知Jordan平方给

$$
\begin{aligned}
\Delta O&=-2r_\lambda\circ v_{\lambda,t}-2q\circ z_{\lambda,t},\\
\Delta(A^2+B^2)&=4r_\lambda\circ v_{\lambda,t}+4q\circ z_{\lambda,t}=-2\Delta O,\\
\Delta\mathcal S_g&=-2\Delta O-4g\circ v_{\lambda,t},\\
\sum_{\lambda,t}\rho_{\lambda,t}v_{\lambda,t}
&=\sum_t\kappa_t(v_{1,t}-v_{0,t})=-H.
\end{aligned}
\tag{145.6}
$$

按原出现重数相加便得145.4。另一路只展开已知平方以核对符号和因子：

$$
\begin{aligned}
W_{r_1}(q)
&=4\sum_{\lambda,t}\rho_{\lambda,t}
\{(r_\lambda-r_1)\circ v_{\lambda,t}+q\circ z_{\lambda,t}\}\\
&=4\sum_t\kappa_t\{v_{0,t}+q\circ(z_{1,t}-z_{0,t})\}.
\end{aligned}
$$

这里 $r_\lambda-r_1=(\lambda-1)u$，而两行实际共享同一个 $f_t$，所以

$$
z_{1,t}-z_{0,t}=t\circ(r_1-r_0)=t,\qquad
v_{0,t}+q\circ t=-d_t.
$$

逐项得到 $W_{r_1}=-4\sum_t\kappa_td_t=-4\delta$。与145.4比较得第二式。整个证明只对已知Jordan运算作双线性展开，没有拆开任何 $D$ 的输入和、没有丢掉一个实际回复，也没有通过未知 $D$ 运输近似误差。∎

中心化原平方没有中心化原响应。式145.3既不声称

$$
D(A-r_1,B)=D(A,B)-D(r_1,B),
$$

也不把 $(A-r_1,B)$ 宣告为原PB在移基后的端点。原位移仍含 $D(t,r_\lambda)$，没有被改成 $D(t,r_\lambda-r_1)$。此种重基若用于下一条原关系，须另外支付实际标签、内回复和两端外回复的完整对应。

## 146. 固定检测读取的正分量、全部质量与未付预算

**定义 146.1（同一个 $w$ 的有符号读取）。** 若 $w\ne0$，保持138.2的同一数学态 $\beta$，满足 $\beta(u)=1$、$\beta(w^2)>0$；不预付von Neumann正常性。定义原实线性算子 $L_z(v)=z\circ v$、正二次表示 $U_z=2L_z^2-L_{z^2}$，以及

$$
\ell(v)=\beta(w\circ K_y(v))
=\beta L_w(L_{y^2}-L_y^2)(v).
\tag{146.1}
$$

$\ell$ 本身不被称作正泛函。其精确正分量全部保留如下：对各独立符号 $\eta,\sigma,\theta\in\{1,-1\}$，置

$$
\begin{aligned}
\psi_{\eta\sigma}
&=\beta\circ U_{u+\eta w}\circ U_{u+\sigma y^2},\\
\varphi_{\eta\sigma\theta}
&=\beta\circ U_{u+\eta w}\circ U_{u+\sigma y}\circ U_{u+\theta y},\\
m_{\eta\sigma}
&=\psi_{\eta\sigma}(u)
=\beta\bigl(U_{u+\eta w}((u+\sigma y^2)^2)\bigr),\\
n_{\eta\sigma\theta}
&=\varphi_{\eta\sigma\theta}(u)
=\beta\bigl(U_{u+\eta w}U_{u+\sigma y}((u+\theta y)^2)\bigr).
\end{aligned}
\tag{146.2}
$$

每个 $\psi,\varphi$ 都是同一原域上的数学正实线性泛函，质量分别是所列 $m,n\ge0$。质量可零、可不等，不归一，也不将相同限制但不同出现或来源的读取合并。这些原正二次表示由已知Jordan闭合给出；它们不是对未知响应的正性或物理制备声明。

**定理 146.2（每份原正分量下的同检测器返回）。** 有精确泛函恒等式

$$
\boxed{\ell=
\frac1{16}\sum_{\eta,\sigma}\eta\sigma\psi_{\eta\sigma}
-\frac1{64}\sum_{\eta,\sigma,\theta}\eta\sigma\theta\varphi_{\eta\sigma\theta}.}
\tag{146.3}
$$

因此对每个原 $q$，尤其对每个实际原 $Q_i$，有

$$
\ell(W_{a+u}(Q_i))=-4\beta(w^2),\qquad
\ell(T(Q_i)-2(a+u)\circ H)=2\beta(w^2).
\tag{146.4}
$$

证明。已知二次表示给

$$
U_{u+z}-U_{u-z}=4L_z.
$$

依照146.2所写的复合次序，两个差的乘积给 $16\beta L_wL_{y^2}$，三个差的乘积给 $64\beta L_wL_yL_y$；相减就是146.3。正性来自每个 $U$ 保正；质量由 $U_z(u)=z^2$ 直接得到，没有除以任何读数。零质量的正泛函由序单位界恒零，但相应出现仍保留。最后对145.5作用同一 $\ell$，用 $K_y\delta=w$，得到 $\ell(\delta)=\beta(w\circ w)=\beta(w^2)$ 及146.4。∎

对每个单独的正分量 $\omega\in\{\psi_{\eta\sigma},\varphi_{\eta\sigma\theta}\}$，145.5给的是 $\omega(W_{a+u}(q))=-4\omega(\delta)$，不把右侧换成 $-4\beta(w^2)$；检测平方是在146.3全部有符号分量合回同一个 $\ell$ 后取得。对每个 $\lambda,t,\epsilon$，同一原P2的完整预算仍是

$$
\begin{aligned}
\Gamma_{\lambda,t}^\epsilon(\omega)
&=\omega((A_{\lambda,t}^\epsilon)^2)\,
\omega((B_{\lambda,t}^\epsilon)^2)
-\omega(A_{\lambda,t}^\epsilon\circ B_{\lambda,t}^\epsilon)^2\ge0,\\
|\omega(O_{\lambda,t}^\epsilon)|
&\le\sqrt{\Gamma_{\lambda,t}^\epsilon(\omega)}.
\end{aligned}
\tag{146.5}
$$

正质量缩放使 $\Gamma$ 按质量平方缩放，零质量则全部为零。将这些预算分别用于十二个实际外出现，只能直接得到

$$
2|\omega(\delta)|
\le\sum_{\lambda,t,\epsilon}|\chi_{\lambda,t,\epsilon}|
\sqrt{\Gamma_{\lambda,t}^\epsilon(\omega)}
+2|\omega((a+u)\circ H)|.
\tag{146.6}
$$

证明是对145.5和145.2用三角不等式及146.5。右侧既保留所有实际外预算，也保留 $H$；这里没有取得它们由原框架误差平方控制或趋零的结论。

**定义 146.3（保留同一检测器的非退化原实框架）。** 在 $w\ne0$ 的分支，保持138.2及146.1的同一个 $\beta$、任一正的数学态延拓 $\phi$ 的GNS向量 $\xi$ 和同一个原平方网。此延拓不要求von Neumann正常性；其双对偶延伸取正常延伸。写 $\operatorname{Var}_\beta(z)=\beta(z^2)-\beta(z)^2$，按下列确定规则选择原标签：

$$
h=\begin{cases}
w-\beta(w)u,&\operatorname{Var}_\beta(w)>0,\\
y-\beta(y)u,&\operatorname{Var}_\beta(w)=0,
\end{cases}
\qquad \nu=\beta(h^2),\qquad
\eta=\frac{h\xi}{\sqrt\nu},\qquad
\mathcal K=\operatorname{span}_{\mathbb C}\{\xi,\eta\}.
$$

这确实给 $\nu>0$。第一分支的 $\nu$ 就是 $\operatorname{Var}_\beta(w)>0$。第二分支若还有 $\operatorname{Var}_\beta(y)=0$，令 $\mu=\beta(y)$，便有 $y\xi=\mu\xi$。只计算已知固定Jordan元素的向量读取，得到

$$
\beta(\delta\circ y^2)=\mu^2\beta(\delta),\qquad
\beta(y\circ(\delta\circ y))
=\mu\beta(\delta\circ y)=\mu^2\beta(\delta).
$$

于是 $\beta(w)=0$，再由 $\operatorname{Var}_\beta(w)=0$ 得 $\beta(w^2)=0$，与所选检测态矛盾。因此第二分支的 $\nu=\operatorname{Var}_\beta(y)$ 也严格正。两分支均有 $\beta(h)=0$，所以 $\xi,\eta$ 正交且均为单位向量。第一分支有 $w\xi=\beta(w)\xi+\sqrt\nu\eta$；第二分支由零方差有 $w\xi=\beta(w)\xi$。故同一个固定 $\mathcal K$ 在两分支中都包含 $\operatorname{span}_{\mathbb C}\{\xi,w\xi\}$，没有换掉 $w$ 或检测态。

将138.2的 $q_i=e_i^2$ 记为 $P_i$，定义全部原框架标签

$$
\begin{gathered}
P_i=e_i^2,\qquad Q_i=\frac{U_h(P_i)}{\nu},\qquad
X_i=\frac{2P_i\circ h}{\sqrt\nu},\\
Z_i=P_i-Q_i,\qquad R_i=P_i+Q_i.
\end{gathered}
\tag{146.7}
$$

每个标签均是原元素的有限Jordan多项式及实线性组合，因而属于原 $E$。$\sqrt\nu$ 只是一个固定正实数，不是对原元素取平方根。由原二次表示保正及 $0\le P_i\le u$，有 $0\le Q_i\le h^2/\nu$、$R_i\ge0$。令 $M=\|h\|$，全部网指标上一致有

$$
\begin{gathered}
\|P_i\|\le1,\qquad \|Q_i\|\le\frac{M^2}{\nu},\qquad
\|X_i\|\le\frac{2M}{\sqrt\nu},\\
\|Z_i\|\le1+\frac{M^2}{\nu},\qquad
\|R_i\|\le1+\frac{M^2}{\nu}.
\end{gathered}
\tag{146.8}
$$

这些界只用已知Jordan运算的范数界；未要求 $Z_i,X_i$ 正。$p$ 仍是138.2的最小Jordan支撑，$P$ 仍是138.3中它的表示投影，均不当作原标签。特别，$P$ 不必是环境秩一投影，环境态延拓不要求纯性，GNS表示不要求不可约性。

**定理 146.4（同一两向量空间上的完整作用与三误差）。** 对146.3的固定选择，定义三个准确的作用误差

$$
e_{0i}=\|P_i\xi-\xi\|,\qquad
e_{1i}=\|P_i h\xi\|,\qquad
e_{2i}=\|P_i h^2\xi-\nu\xi\|.
\tag{146.9}
$$

三者均趋于零。在正交基 $(\xi,\eta)$ 下，146.7的五个标签在同一个 $\mathcal K$ 上趋向以下实自伴矩阵的完整作用：

$$
\begin{aligned}
P^{(0)}&=\begin{pmatrix}1&0\\0&0\end{pmatrix},&
Q^{(0)}&=\begin{pmatrix}0&0\\0&1\end{pmatrix},&
X^{(0)}&=\begin{pmatrix}0&1\\1&0\end{pmatrix},\\
Z^{(0)}&=\begin{pmatrix}1&0\\0&-1\end{pmatrix},&
R^{(0)}&=\begin{pmatrix}1&0\\0&1\end{pmatrix}.
\end{aligned}
\tag{146.10}
$$

这些矩阵只描述极限作用，不宣称是原 $E$ 中的准确矩阵单位。准确的逐列误差界为

$$
\begin{aligned}
\|P_i\xi-\xi\|&=e_{0i},&
\|P_i\eta\|&=\frac{e_{1i}}{\sqrt\nu},\\
\|Q_i\xi\|&\le\frac{M e_{1i}}{\nu},&
\|Q_i\eta-\eta\|&\le\frac{M e_{2i}}{\nu\sqrt\nu},\\
\|X_i\xi-\eta\|&\le\frac{e_{1i}+M e_{0i}}{\sqrt\nu},&
\|X_i\eta-\xi\|&\le\frac{e_{2i}+M e_{1i}}{\nu},\\
\|Z_i\xi-\xi\|&\le e_{0i}+\frac{M e_{1i}}{\nu},&
\|Z_i\eta+\eta\|&\le\frac{e_{1i}}{\sqrt\nu}
+\frac{M e_{2i}}{\nu\sqrt\nu},\\
\|R_i\xi-\xi\|&\le e_{0i}+\frac{M e_{1i}}{\nu},&
\|R_i\eta-\eta\|&\le\frac{e_{1i}}{\sqrt\nu}
+\frac{M e_{2i}}{\nu\sqrt\nu}.
\end{aligned}
\tag{146.11}
$$

证明。138.3对固定原 $h,h^2$ 给

$$
PhP=0,\qquad Ph^2P=\nu P,\qquad P\xi=\xi,
\qquad Ph\xi=0,\qquad Ph^2\xi=\nu\xi.
$$

只需固定有限向量表 $\{\xi,h\xi,h^2\xi\}$。138.2的同一有界强网及相应正强半范数给

$$
\begin{aligned}
e_{0i}^2&=\beta^{**}((P_i-p)^2)\longrightarrow0,\\
e_{1i}^2&=\beta^{**}\bigl(U_h((P_i-p)^2)\bigr)\longrightarrow0,\\
e_{2i}^2&=\beta^{**}\bigl(U_{h^2}((P_i-p)^2)\bigr)\longrightarrow0.
\end{aligned}
\tag{146.12}
$$

这些双对偶式子仅用于证明强收敛。在环境表示中，原标签的已知Jordan定义给 $Q_i=hP_i h/\nu$、$X_i=(P_i h+hP_i)/\sqrt\nu$。于是

$$
\begin{aligned}
Q_i\xi&=\frac{hP_i h\xi}{\nu},&
Q_i\eta-\eta&=\frac{h(P_i h^2\xi-\nu\xi)}{\nu\sqrt\nu},\\
X_i\xi-\eta
&=\frac{P_i h\xi+h(P_i\xi-\xi)}{\sqrt\nu},&
X_i\eta-\xi
&=\frac{P_i h^2\xi-\nu\xi+hP_i h\xi}{\nu}.
\end{aligned}
$$

范数不等式逐项给146.11；$P_i$ 的两列直接由定义，$Z_i,R_i$ 的两列由加减得到。令 $\iota:\mathcal K\hookrightarrow\mathcal H_\phi$ 为包含映射，对每个 $A_i\in\{P_i,Q_i,X_i,Z_i,R_i\}$，取146.11中相应两列的右侧为 $b_{\xi i},b_{\eta i}$，则Cauchy–Schwarz给

$$
\|A_i|_{\mathcal K}-\iota A^{(0)}\|_{B(\mathcal K,\mathcal H_\phi)}
\le\sqrt{b_{\xi i}^2+b_{\eta i}^2}\longrightarrow0.
\tag{146.13}
$$

因此结论对 $\mathcal K$ 的整个单位球一致，包括泄漏到 $\mathcal K^\perp$ 的分量：若 $\Pi_{\mathcal K}$ 是仅供数学估计的Hilbert投影，便有 $\|(1-\Pi_{\mathcal K})A_i|_{\mathcal K}\|\le\sqrt{b_{\xi i}^2+b_{\eta i}^2}\to0$。不是仅压缩后的两个乘两个矩阵元收敛。常数依赖所固定的 $h,\nu$，不依赖 $i$；没有对全部检测器选择供应统一的正方差下界。全程用网保留不可分情形。∎

**定义 146.5（三误差与已知原平方读取的准确对应）。** 写 $\omega_z=\beta\circ U_z$，这是138.2已许可的原数学正读取，质量准确为 $\omega_z(u)=\beta(z^2)$。146.9还可以完全用原标签和已知原平方读取表示为

$$
\begin{aligned}
e_{0i}^2&=\beta((P_i-u)^2),\\
e_{1i}^2&=\omega_h(P_i^2),\\
e_{2i}^2&=\omega_{h^2}(P_i^2)
-\frac{\nu}{2}\{\omega_{u+h^2}(e_i^2)-\omega_{u-h^2}(e_i^2)\}
+\nu^2\beta(u^2).
\end{aligned}
\tag{146.14}
$$

证明。前两式是自伴作用的范数平方。第三式展开同一向量误差给

$$
e_{2i}^2=\beta(U_{h^2}(P_i^2))-2\nu\beta(P_i\circ h^2)+\nu^2.
$$

再用 $U_{u+h^2}-U_{u-h^2}=4L_{h^2}$ 和 $P_i=e_i^2$ 即得146.14。这里的每个被读取元素 $(P_i-u)^2,P_i^2,e_i^2,u^2$ 都是已知原平方；最后一行整体非负，是有符号组合，不将其中每个正项另判为趋零。所用读取的全部实际质量是

$$
\begin{gathered}
\beta(u)=1,\qquad \omega_h(u)=\nu,\qquad
\omega_{h^2}(u)=\beta(h^4),\\
\omega_{u\pm h^2}(u)=\beta((u\pm h^2)^2)
=1\pm2\nu+\beta(h^4)\ge0.
\end{gathered}
\tag{146.15}
$$

不除以这些质量，零质量的出现也保留；这与146.2各份 $m,n$ 的正分量是不同的读取表，不能用此表替换它们。146.12证明三误差趋零，146.14给相同误差的纯原平方表达，均没有读取未知响应的极限。∎

145.2在这里取的仍是同一个原 $q=Q_i$，两行均读取 $f_t=D(t,Q_i)$；式(146.4)的同检测器返回在每个有限 $i$ 已经准确。$\nu$ 只用于146.7这些既定原标签，式(146.2)的每个正分量仍以原 $m,n$ 读取，不因此归一化、删去零质量或获得实际准备。$w=0$ 时无须这份检测框架，145的全部恒等式及146.2的正分量预算仍保持原量词。

这只供应近似的实自伴两向量框架：$X^{(0)},Z^{(0)}$ 是实轴，没有供应原虚Pauli轴或原域中的准确矩阵单位。即使已知完整作用及泄漏误差趋零，也不识别 $D(P_i,t)$、$D(Z_i,X_i)$ 或任何变动外回复，不把相同或渐近相同的输入作用替换成相同输出。没有给旧 $D$ 增加连续性、可加性、协变、局部闭合或响应运输。尤其146.11–146.15没有使式(146.5)的十二个实际外预算或 $H$ 趋零。

## 147. 原域预算缺口、成熟交叉配平工具与全部来源合同

**定义 147.1（精确返回与仍缺的原预算供应）。** 145–146只生产同一检测器的准确返回接口，不生产其趋零预算。一般原 $E$ 中仍须用合法实际PB，把两行、全部 $d_t,d'_t$、共享 $f_t$ 及十二个外回复保持在一起，按原 $\rho,\chi$ 返回

$$
W_{a+u}(q)=-2\{T(q)-2(a+u)\circ H\}=-4\delta,
$$

并在146的同一正分量及实际质量下，给它与146.9、146.14中已知原框架误差平方的目标相关界。146.11–146.13已控制同一两向量空间上的完整原标签作用，仍未给这份检测预算的支配。仅有输出相关平方 $\mathcal S_{a+u}\ge0$、统一有界性、单列PB配平，或另一列和的守恒，均未支付这个界。145.5是恒等式，不是新的充分性生产者；把它另命名也不增加来源信息。

一个目标相关的联合通量估计仍未被144否定，但它必须在全部外 $\chi$ 求和后到达同一 $W_{a+u}$ 或 $T-2(a+u)\circ H$。同样，可以尝试精确运输固定元素 $T(q)-2(a+u)\circ H=2\delta$ 再配原平方衰减预算；只运输与它无返回关系的能量不足。任何中间调用的两端及全部内外回复均须来自同一总 $D$。没有取得这份一般原域的实际运输字或衰减预算，也没有证明其不存在。

**定义 147.2（已付完整域运输与不能移用的输入）。** [SF100.5、SF101.1–101.2、SF102.12–102.14](AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md#101-中央复坐标中的唯一精确运输接口)在其完整半有限continuous原域 $E=M_{\rm sa}$ 中，已经支付全部有限支撑首行、同一个 $\mathfrak F(Z)$ 的实际Cayley运输、有界四分之一辐角的有限两步酉运输，以及保持固定缺陷而使已知原平方预算衰减的中央局部读取。直接复用这些结论，不重新分类，也不将它们列为同类模型中的欠项。

那里逆元重选的原坐标、有界Borel辐角、极分解和原投影均由其完整域供应。一般JC包含只给 $E\subset X\subset A_{\rm sa}$，不保证这些坐标属于原 $E$，也不保证 $E+iE$ 结合闭合。因此这些输入、原行识别和运输都不能仅凭忠实JC包含迁入一般不完备原域。142–144的完整 $\mathrm{II}_1$ 测试实例亦不替换145–146的一般原候选。

成熟交叉配平的相邻背景是J. M. Sanz-Serna，[*Symplectic Runge–Kutta Schemes for Adjoint Equations, Automatic Differentiation, Optimal Control, and More*](https://arxiv.org/html/1503.04021v1#S2.SS2)，arXiv:1503.04021v1，§2.2，Theorem 3、Lemma 1及式(16)–(18)；正式版为 *SIAM Review* 58(1), 3–33，DOI [10.1137/151002769](https://doi.org/10.1137/151002769)。对已有实双线性不变量 $S(q,p)$ 的有限维分块ODE，配对PRK系数的条件是

$$
b_i=B_i,\qquad b_iA_{ij}+B_ja_{ji}-b_iB_j=0\quad\text{对所有阶段 }i,j,
\qquad c_i=C_i\quad\text{在非自治情形}.
\tag{147.1}
$$

Lemma 1用这些联立系数条件消去准确双线性增量中的交叉阶段项；自治情形不需要横坐标条件。它保持的是所给双线性跨块不变量，不能改读成任意分块算法的全部二次不变量都保持。此处只将其作为成熟的交叉更新相容机制引用；没有给原 $D$ 供应可微ODE、PRK实现、伴随动力或未知响应的双线性，也不从该定理推导144。143–145的关系直接由实际原调用和已知平方证明。

142.3的普通Gram展开、Pauli乘法、C*正性和正泛函分离均是成熟中间工具，不单独计算为新内容。146.3–146.5的支撑及有界强网直接消费138.2–138.3和141.2所引Hamhalter及Hanche-Olsen–Størmer的准确接口；正的数学态延拓和GNS仍按137.2、141.2的同一来源使用，不加强为纯延拓或不可约表示。新增的 $\texttt{repo-derived}$ 应用是：把演员差的活动支撑判据接到同一总表生成的完整三参数实际配对循环，保留两个循环符号后计算其非零漂移，再将两行实际源表接回保留 $H$ 的同一原检测器，并给保留该检测器的原实框架、完整作用及已知平方误差对应。它不同于141.1的逐输出零误差诊断，也不重复SF98的标准模型分类。145.5及近似框架均不单独计为检测目标生产；这里不作历史优先权、文献穷尽、Lean核验或物理实现的声称。

**定义 147.3（全部七项原合同的无删减合取）。** 本组将[本卷141.3](#141-全数学pb下的零误差pauli诊断与原目标边界)、137.3、122.1，及[SF105.1第1–7项全文](AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md#105-七项真实同源物理来源的完整合同)无删减地合取为完整来源义务。这包括SF105.1明确完整合取的SF96.1，SM86.1、SM78.2、SM43.2、SM49.1、SM61.1、SM69.1，C199.2、C194.2、C186.1–186.7、C181.3、C171.1–171.7、C160.3、C155.1、C145.1–145.7，A8.3–8.4、A14.2、A25.1、A53.1，R3 8.1–8.5、R3 80.1，W95.2、W116.1，以及这些各项逐一纳入的全部上游对象、条件、实现、原域、质量和量词；固定源身份仍按各原文给定。字母缩写取SF98.1的原文地址。这里是完整子句的共同合取，不是只引标题、消费者索引或下述说明来代替原文。

第一项保持唯一原 $\Omega/\mathrm{native}$、同一原 $E,C,u,N,\mathcal P,S,D$、具名可取得标签、指定跨评价配对、共同全词 $q/K/J$、全部原 $\xi_\gamma$、parent/ready和合法控制。SF105.1的式(105.1)及其全部原标签、原评价、全部 $z,w\in V$、所有 $n\ge0$ 原词和正标签量词完整保留：同一个第一槽共轭线性的半正定Hermitian型 $K$ 及同一总集合映射 $J_a$，准确原词复合后的有限复线性包、零长度词和每份原程序自己的身份均不换。数学表示不预付 $J_a$ 线性、$J_0=0$、$J_1=I$、全部 $B(H)$ 的取得、任意向量准备或实际相干控制；原门序列及 $\sigma,t_0$ 保持自身来源。

第二项保持原准备、事件、准确效果区间、每份实际完整菜单及接受归属，全部共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、P9的每个分支和每份独立 $W_e$、全部中间切口及固定支持全质量。只有原事件已经绑定、菜单和为单位且实际质量严格正，才按SF105.2归一；条件角菜单另须原支持、条件化身份和正支持质量。所有零、不等、次归一质量、中心权、经典不等维和静默块均保留；原强度不等于概率质量。各块AS/EC、菜单外OB、忠实二维到三维适配器及互探的有限维／最小可见／实尺度范围不变。原 $g^*$、$d_s^*$、共同根的读取顺序和不同程序身份不因同矩阵而合并；数学态、正延拓、迹和GNS不新增物理准备或正常性。

第三项保持同一个非零真正相关原联合、原全词网络、交叉零、旧局部乘法、忠实同向交换局部腿、共同实现、联合生成分离和重数、全部真正相关输入、中央对、经典和不等维块、实际复制及各层同源参考。要求局部全矩阵的消费者仍守其准确前件；数学type II张量测试域不直接供应这些物理腿。相同边缘、分别可达、共同数学取向、两个角或一个辅助张量表示都不替代这份共同实现。

第四项保持每条实际原细分支 $r:A\to B$ 的全部typed前后接、每份完整输出的每个仍合法未来、每份评价的未归一回溯SF105.3、反变复合、typed分区、全未来自然性、质量运输和原箭头商下降。CP仍须完整同标签单位区间比较，或整台实际箭头可再应用的递归同源参考；整个系统和环境、全部成功／失败／细记录／port／post-port输出，以及真正遗忘、返回和合法复合均在原规则类中。SF105.4–105.6的两端共同真支持、忠实同向交换系统腿和 $M_2$ 腿、三颗实际参考投影与 $I_2$ 的实张成、支持内补、全部原相关正输入和决定锥评价上的intertwining与夹界，以及对每条根箭头、每个所需有限 $L$、每个 $k\le L$ 的实际长链和精确累计支持运输逐项保留。累计支持不换成新环境单位；每个正精度和精确根身份保持，固定正误差不代付精确结论。有限深度全称不暗中要求物理无限链；数学参考不制造原参考。Kraus另守有限全矩阵或已付正规表示、指定前对偶和收敛范围，不假定一般子代数等于全 $B(H)$、存在可数Kraus和或其指标就是原记录。

第五项保持整台仪器的全输入运输、完整typed菜单和接受端、整个环境、全部成功失败细记录及port/post-port输出和每份输出的全部合法未来。真分组遗忘、AC、精确 $N_u$、X/Xs、每份原平方根词及各自接受条件不删；完成中有平方根不等于原词可执行。正次单位只给TNI，TP另需完整typed单位分区；Lüders另需同一完整输出的投影效果、像内每条射线保持与完整校准，同效果或同概率不代付。仅严格正输出质量归一，失败和零分支保留原类型、记录和未来；细输出可相加仍须真正粗事件和实际分组接头。密度、迹类和Kraus公式各守已付表示、指定前对偶及收敛域，不用给定迹抹去来源身份。

第六项保持全部合法顺序、自适应和并行历史，每份完整输出的每个仍合法未来，整个环境、参考副本、全部细记录和泄漏，停止、拒绝、销毁，真遗忘，同数两侧和同数逆向的真实双向返回。未定义请求仍未定义；同数学算子不合并原程序、读取顺序、原 $q$ 零集或AC方向。CountRead绑定读后同一原完整活动输入和其全未来实际返回，活动ready接头、接受叶活动输出及第一合法消费者、具名分析词到原完整菜单和接受端的接线不删；负提升两条活路的分别控制及相干聚合都须实际取得。精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 保持区别；原两只独立九叶彩票及各自第九空程序、十六拒绝叶和相干 $I_3/3$ 返回仍保身份。初始取得、指定有限树、被动精确混合解码、已付CountRead精确表的支持事件和整支质量、已付有限返回数值校准各守原平稳、真实同源、同初始版本和实际域，既有成果不重新列为欠项；它们也不代付完整输出的全未来Return。无限历史、无限或非离散记录、可数可加、正常性、指定前对偶和所需收敛继续由原扩展来源供应，不截成有限角。

第七项保持同一旧全域乘法、保持可能不完备原域的流、实际相位和原门序列、同一实际过程内可逆一参数群及实际逆、原物理钟和单位、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同仪器、共同作用量及同一个正 $\hbar$。原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 的预算保持各自原设备、参数、定义域与量纲；不与这里的矩阵参数或网指标混同。只有这些前件齐备，才在原适用域消费SF105.7的Schrödinger、密度和Heisenberg方程，伴随乘法也必须是识别后的同一个 $\star$。向量、密度和观测量微分各守原生成元、迹类可微及实际可微域；有界数学内导子、谱、辅助钟或形式CP均不生产物理时间、控制成本、一般无界域、能量意义或跨装置共同尺度。

七项必须在唯一原世界内共同实现，不能每项各换来源。142–144只给一种完整数学测试类中的方法障碍，145–146只给一般原域的同检测器接口；它们都没有同时供应这七项的物理实现。原量子起源目标、所有原输入的 $K_y\delta_a(b,c)=0$、原全域旧乘法、全部合法历史／未来／真实返回和物理尺度未因这些局部结果而缩减。数学兼容性、纸面证明与物理本体真实性仍分别评价。

## 追加锚（本行以下为增补区）

## 148. 行列式着色的全部重复演员族与同检测器混合障碍

**定义 148.1（同一个原多项式域上的总响应）。** 复用原多项式卷8.1的标量端点域，取两个乘两个矩阵，改以 $x\in[0,1]$ 记多项式变量：

$$
\begin{aligned}
E&=\left\{\alpha I+\sum_{k=1}^d x^kA_k:
\alpha\in\mathbb R,\ d<\infty,\ A_k=A_k^*\in M_2(\mathbb C)\right\},\\
\mathcal A&=\{A\in C([0,1],M_2(\mathbb C)):A(0)\in\mathbb CI\},
\qquad \mathcal X=\mathcal A_{\rm sa},\\
C&=E\cap\mathcal X_+,\qquad u=I,\qquad
N(A)=\sup_{0\le x\le1}\|A(x)\|_{\rm op},\qquad
S(A,B)=A\circ B=(AB+BA)/2.
\end{aligned}
\tag{148.1}
$$

次数有限但没有共同上界。$E$ 含单位，在 $\mathcal X$ 中稠密且不完备；这里 $E+iE$ 本身是结合星多项式代数，这是此例的性质，不是一般原Jordan域的前件。原评价族取 $E$ 上全部数学正实线性泛函，保留全部非负质量。原锥准确，点评价的正向量读取分离 $E$ 并决定此锥。

对所有原 $A,B\in E$，定义同一总函数

$$
\begin{gathered}
C_0(A,B)=\frac i2[A,B],\qquad
\varepsilon(A,B)=
\begin{cases}
+1,&\det(A+iB)\equiv0\text{ 于 }\mathbb C[x],\\
-1,&\det(A+iB)\not\equiv0\text{ 于 }\mathbb C[x],
\end{cases}\\
D(A,B)=\varepsilon(A,B)C_0(A,B).
\end{gathered}
\tag{148.2}
$$

判别的是整个复多项式恒零，不是某一点的行列式，也不是整个输入矩阵恒零。$C_0(A,B)$ 是原自伴多项式，且在零点为零，所以 $D:E^2\to E$ 确实是总响应；每份内回复、外回复及重合输入都由148.2唯一确定。

为固定系数取向，记标准Pauli系数矩阵

$$
X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
\tag{148.3}
$$

$X,Y,Z$ 只作系数，均不作为非标量常数输入交给 $D$。本组所有PB均指103.4的实际有限差分及配平三角续卷128.4的同一个原 $Q$ 平衡。

**定理 148.2（重复演员不能排除的总表及全实共同标签的排除）。** 148.2的同一份 $D$ 有以下联合性质。

1. 原A1–A3、全部原P2、准确锥、单位及范数保持；量化全部正读取和全部非负质量。反对称、每槽奇性、全部 $SO(2)$ 槽旋转、交换零集、同生成元多项式零行、全单位零行、交换子范数界及Jordan正交对的平方／面积关系均成立，准确形式见149.3–149.4。
2. 对每个原 $r,t\in E$，两类实际调用
   $$
   \operatorname{PB}_D(r;r,t),\qquad
   \operatorname{PB}_D(r;t,r)
   \tag{148.4}
   $$
   同时成立，包括退化、零和重合标签。这恰是所断言的两个重复演员族，不扩大为其它重复标签、多项式自作用或所有标量第三标签族。
3. 在同一原表中取 $a=F=2xX$、$G=xZ$、$(s,b,c)=(3G,G,2G)$、$y=x(X+Y)/\sqrt2$，使用145.1和146.1的原定义，准确有
   $$
   \delta=-8x^2Y,\qquad H=8x^2Y=-\delta,\qquad
   w=K_y\delta=4x^4(X-Y)\ne0.
   \tag{148.5}
   $$
   150给出同一质量一检测态、全部十二份正分量及实际质量，以及原平方框架的三个准确零误差。在 $q=0$ 上，145.2的六张实际调用均成立，十二个外出现全部保留。
4. 对每个实数 $j,\mu$，置 $t_j=jG$、$r_\lambda=F+\lambda I$、$q_\mu=\mu G$，其中 $\lambda=0,1$。以151.1的残差 $\mathcal R_{\lambda,j}(\mu)$ 记实际 $\operatorname{PB}_D(t_j;r_\lambda,q_\mu)$ 左侧减所需右侧，并置
   $$
   \sigma_j=\begin{cases}+1,&j=2\text{ 或 }j=-2,\\-1,&\text{其它实 }j.\end{cases}
   $$
   则全实参数上准确有
   $$
   \mathcal R_{0,j}(\mu)=4j\mu(\sigma_j\sigma_\mu-1)x^3X,
   \qquad \mathcal R_{1,j}(\mu)=0.
   \tag{148.6}
   $$
   在同一个出现表 $j=(3,1,2)$、原权重 $\kappa=(1,-1,-1)$ 和 $\rho_{\lambda,j}=(2\lambda-1)\kappa_j$ 下，使用同一个 $g=F+I$、$T$ 和 $\ell$，有
   $$
   \begin{aligned}
   \sum_{\lambda,j}\rho_{\lambda,j}\mathcal R_{\lambda,j}(\mu)
   &=T(q_\mu)-2g\circ H-2\delta
   =T(q_\mu)=2\sigma_\mu C_0(\delta,q_\mu),\\
   \ell\bigl(T(q_\mu)-2g\circ H-2\delta\bigr)
   &=64\mu\sigma_\mu.
   \end{aligned}
   \tag{148.7}
   $$
   每个非零共同实 $\mu$ 都在同一检测器下检出至少一张实际混合调用失败；$\mu=0$ 返回第3项的有效包。
5. 更一般地，在此原域上，按 $\det(A+iB)$ 恒零／非恒零两类各指定一个固定颜色 $s_0,t_0\in\{1,-1\}$，令响应为相应颜色乘 $C_0$。若它满足152的全部非零多项式轮廓混合调用，则 $s_0=t_0$。因此排除的是这个明定的不同两色行列式类，未分类任意总响应。

证明分为149–152。第3、4项应用145–146的既有定义和恒等式，不将其重新计作一般域运输定理；第5项的常色终点直接复用普通／相反乘法模型。

## 149. 全部正读取及左右因子的重复演员证明

**定理148.2第1、2项的证明。** 若 $\phi:E\to\mathbb R$ 正，原序单位界立即给

$$
|\phi(A)|\le\phi(I)N(A).
\tag{149.1}
$$

所以每个这样的读取都连续；零质量时它恒零。它唯一延拓为 $\mathcal X$ 上正实线性泛函，再复线性延拓到 $\mathcal A$ 上的正泛函：若正 $A\in\mathcal X$ 由 $A_n\in E$ 一致逼近，取 $\epsilon_n\ge N(A_n-A)$ 趋零，则 $A_n+\epsilon_nI\in C$，极限给正性。于是没有只检查点评价或一部分质量。

在148.2的每一个固定输入对上，$D$ 的P2表恰为

$$
\begin{pmatrix}
\phi(A^2)&\phi(A\circ B)-i\phi(D(A,B))\\
\phi(A\circ B)+i\phi(D(A,B))&\phi(B^2)
\end{pmatrix}=\begin{cases}
\begin{pmatrix}\phi(A^2)&\phi(AB)\\\phi(BA)&\phi(B^2)\end{pmatrix},&\varepsilon=+1,\\
\overline{\begin{pmatrix}\phi(A^2)&\phi(AB)\\\phi(BA)&\phi(B^2)\end{pmatrix}},&\varepsilon=-1.
\end{cases}
\tag{149.2}
$$

普通正Gram表及其逐项共轭均半正定，故全部原P2成立。A2只读已知Jordan实Gram表，$(A+B,A,B)$ 的指定关系向量给零；A3由 $I^2=I$ 和 $0\le e\le\theta I\Rightarrow e^2\le e$ 给出，其中原固定有理 $0<\theta\le1$ 任取。每个质量及其任意非负缩放均保留。

令 $Z_0=A+iB$。实槽旋转对应乘单位复相位，交换两槽或单槽变号对应乘相位后的 $Z_0^*$。行列式恒零与否在这些操作下不变，所以颜色也不变。对 $C_0$ 用同一操作，得到

$$
\begin{gathered}
D(B,A)=-D(A,B),\qquad
D(-A,B)=D(A,-B)=-D(A,B),\\
D(cA-sB,sA+cB)=D(A,B)\quad(c^2+s^2=1),\\
D(A,B)=0\Longleftrightarrow[A,B]=0,\qquad
D(p(A),q(A))=0,\qquad D(\alpha I,A)=0,\\
N(D(A,B))\le N(A)N(B).
\end{gathered}
\tag{149.3}
$$

这里 $p,q$ 是任意实多项式，$\alpha$ 是任意实数。又若 $A\circ B=0$，已知结合乘法给 $AB=-BA$，所以

$$
A\circ D(A,B)=B\circ D(A,B)=0,\qquad
D(A,B)^2=A^2B^2.
\tag{149.4}
$$

这些平方和正交关系不受正负号影响。这里只证明每个二表的正性；没有断言同一个多输入有限复Gram表正。

现在固定任意原 $r,t$，记 $\sigma=\varepsilon(r,t)$、$Z_r=r+it$。在 $\operatorname{PB}_D(r;r,t)$ 中，实际内值给

$$
v=-r\circ t,\qquad z=r^2+\sigma C_0(r,t).
$$

两份实际外复坐标准确为

$$
(r\pm v)+i(t\pm z)=
\begin{cases}
(I\pm ir)Z_r,&\sigma=+1,\\
Z_r(I\pm ir),&\sigma=-1.
\end{cases}
\tag{149.5}
$$

因为 $r(0)=\rho I$、$\rho\in\mathbb R$，

$$
\det(I\pm ir)(0)=(1\pm i\rho)^2\ne0.
\tag{149.6}
$$

$\mathbb C[x]$ 是整环；由行列式乘法性，149.5两端外对的行列式恒零当且仅当 $\det Z_r\equiv0$。故两份实际外颜色都等于内颜色 $\sigma$。两份内回复及两份外回复因此都与固定响应 $\sigma C_0$ 相同。该固定响应的完整PB由普通或相反结合乘法的既有平方恒等式供应，直接应用即得当前实际调用的元素式及全部读取的 $Q$ 平衡。

对另一族 $\operatorname{PB}_D(r;t,r)$，实际内值是

$$
v=\sigma C_0(r,t)-r^2,\qquad z=r\circ t.
$$

此时种子 $W_r=t+ir=iZ_r^*$ 与 $Z_r$ 同属一个行列式类，且

$$
(t\pm v)+i(r\pm z)=
\begin{cases}
(I\pm ir)W_r,&\sigma=+1,\\
W_r(I\pm ir),&\sigma=-1.
\end{cases}
\tag{149.7}
$$

用149.6重复同一个整环论证，两个实际外颜色仍等于 $\sigma$，故此族也完整配平。若交换子为零或标签退化，因子公式及颜色判别仍逐字成立。没有使用 $I\pm ir$ 的逆元，没有向完成添加输入，也没有对 $D$ 取极限。第1、2项得证。∎

## 150. 原两行缺陷、非零检测与准确零框架误差

**定理148.2第3项的证明及固定数据。** 取148.2第3项的 $F,G$、出现表及权重，记 $r_\lambda=F+\lambda I$。对任意实 $j$，

$$
\det(F+ijG)=(j^2-4)x^2,\qquad
\det(r_1+ijG)=1+(j^2-4)x^2.
\tag{150.1}
$$

故 $D(F,jG)=2j\sigma_jx^2Y$，而 $D(r_1,jG)=-2jx^2Y$。按出现次序 $j=(3,1,2)$ 写出全部内值，得到

$$
(d_{0,j})=(-6,-2,4)x^2Y,\qquad
(d_{1,j})=(-6,-2,-4)x^2Y.
\tag{150.2}
$$

直接应用145.1给148.5；尤其 $H$ 不为零。令

$$
U=\frac{X-Y}{\sqrt2},\qquad V=\frac{X+Y}{\sqrt2},\qquad
\beta(A)=\frac12\operatorname{Tr}((I+U)A(1)),\qquad y=xV.
\tag{150.3}
$$

这是数学正读取，质量为一。$w=4\sqrt2x^4U$，所以

$$
\beta(w^2)=32,\qquad \beta(w)=4\sqrt2,\qquad
\operatorname{Var}_\beta(w)=0,\qquad \beta(y)=0,\qquad\beta(y^2)=1.
\tag{150.4}
$$

146.3的指定选择因此恰为 $h=y$、$\nu=1$，不是另换检测框架。同一有符号泛函仍是

$$
\ell(v)=\beta(w\circ K_y(v)),\qquad
\ell(\delta)=32,\qquad \ell(x^3X)=4.
\tag{150.5}
$$

在 $q=0$ 下，对每个 $j\in(3,1,2)$ 和每个 $e\in\{1,-1\}$，145.2的实际外出现为

$$
\begin{aligned}
A_{0,j}^e&=F-e d_{0,j},& B_{0,j}^e&=0,& O_{0,j}^e&=0,\\
A_{1,j}^e&=r_1+e\,2jx^2Y,& B_{1,j}^e&=e jxZ,&
O_{1,j}^e&=2j^2x^3X-e\,2jx^2Y.
\end{aligned}
\tag{150.6}
$$

第二行外复坐标的常数项是 $I$，故两个颜色都是 $-1$；第一行输出由全零第二槽确定。这十二份值均来自148.2，不是逐端另赋值。两行外差分别为 $0$ 和 $-4jx^2Y$，恰等于各自PB右侧。已知普通平方差分别为 $0$ 和 $8jx^2Y$，所以全部六张 $Q$ 平衡成立。按原权重相加给

$$
T(0)=0,\qquad g=F+I,\qquad g\circ H=H=-\delta,
\qquad W_g=32x^2Y=-4\delta,
\tag{150.7}
$$

以及 $\ell(W_g)=-128$、$\ell(T(0)-2g\circ H)=64$。这是145–146的同一返回的代入，没有将 $\delta$ 换为 $H$ 或 $w$。

保留146.2的精确复合次序及每个独立符号 $\eta,\sigma,\theta\in\{1,-1\}$，全部正读取和质量为

$$
\begin{aligned}
\psi_{\eta\sigma}&=\beta\circ U_{I+\eta w}\circ U_{I+\sigma y^2},&
m_{\eta\sigma}&=(1+\sigma)^2(1+4\sqrt2\eta)^2,\\
\varphi_{\eta\sigma\theta}
&=\beta\circ U_{I+\eta w}\circ U_{I+\sigma y}\circ U_{I+\theta y},&
n_{\eta\sigma\theta}
&=\begin{cases}8(1+4\sqrt2\eta)^2,&\sigma=\theta,\\0,&\sigma\ne\theta.
\end{cases}
\end{aligned}
\tag{150.8}
$$

这里 $U_z(A)=zAz$ 是148.1中已知Jordan二次表示。证明这些质量只需在 $x=1$ 使用 $y^2=I$、$w=4\sqrt2U$，以及 $\beta$ 支撑于 $U$ 的正特征射线且 $\beta(V)=0$。于是 $I+\eta w$ 在该射线上给因子 $1+4\sqrt2\eta$；两个同号 $I\pm V$ 的四次方读取为八，异号乘积为零。四个 $m$ 和八个 $n$ 全部保留，包括零与不等质量，不除法、不合并出现。

同一泛函的正分量分解仍逐字采用146.3。更明确地，对151中的每个实际外出现和每个 $\omega\in\{\psi_{\eta\sigma},\varphi_{\eta\sigma\theta}\}$，全部P2给

$$
|\omega(O_{\lambda,j}^e)|\le
\sqrt{\omega((A_{\lambda,j}^e)^2)\omega((B_{\lambda,j}^e)^2)
-\omega(A_{\lambda,j}^e\circ B_{\lambda,j}^e)^2}.
\tag{150.9}
$$

这逐份保持全部十二个外出现、每份正读取和原质量；没有从单表预算推导残差为零。

最后令系数 $p_+=(I+U)/2$，仅将下列多项式当作原输入：

$$
e_n=x^np_+\in E,\qquad 0\le e_n\le I,\qquad
P_n=e_n^2=x^{2n}p_+\in E\quad(n\ge1).
\tag{150.10}
$$

在 $\beta$ 的点评价GNS表示中，$p_+\xi=\xi$、$p_+V\xi=0$、$V^2\xi=\xi$。所以同一个 $h=y$ 满足

$$
P_n\xi=\xi,\qquad P_nh\xi=0,\qquad P_nh^2\xi=\xi,
\qquad e_{0n}=e_{1n}=e_{2n}=0.
\tag{150.11}
$$

误差恰是146.9的三个误差。$P_n=(xp_+)^{2n}$ 在双对偶中单调强降到点评价正射线的最小支撑，故与原平方支撑构造相容。这里没有对 $p_+$、极限支撑或完成标签调用 $D$；也没有识别任何框架标签上的未知回复。第3项得证。∎

## 151. 全实共同第三标签的两行实际残差与原检测器返回

**定理148.2第4项的证明。** 保留150全部固定数据、正读取和实际质量。对任意实 $j,\mu$，取同一个原 $q_\mu=\mu xZ$，仍按145.2逐次生成 $v,z,A,B,O$。只为度量是否满足PB，定义残差

$$
\mathcal R_{\lambda,j}(\mu)
=O_{\lambda,j}^+-O_{\lambda,j}^-
+2r_\lambda\circ v_{\lambda,j}+2q_\mu\circ z_{\lambda,j}.
\tag{151.1}
$$

残差为零等价于该实际调用的元素PB；没有预先假定这些混合PB成立。两行共享同一份 $f_j=D(t_j,q_\mu)=0$，实际内值准确是

$$
\begin{aligned}
v_{0,j}&=-2j\sigma_jx^2Y-j\mu x^2I,& z_{0,j}&=0,\\
v_{1,j}&=2jx^2Y-j\mu x^2I,& z_{1,j}&=jxZ.
\end{aligned}
\tag{151.2}
$$

因此对两个实际端点符号 $e=1,-1$，

$$
\begin{aligned}
A_{0,j}^e&=F-e(2j\sigma_jx^2Y+j\mu x^2I),&
B_{0,j}^e&=\mu xZ,\\
A_{1,j}^e&=r_1+e(2jx^2Y-j\mu x^2I),&
B_{1,j}^e&=(\mu+ej)xZ.
\end{aligned}
\tag{151.3}
$$

普通Pauli行列式给出

$$
\det(A_{0,j}^e+iB_{0,j}^e)
=(\mu^2-4)x^2(1+j^2x^2).
\tag{151.4}
$$

因为 $1+j^2x^2$ 不是零多项式，两份实际外颜色都恰为 $\sigma_\mu$，包含 $j=0$、$\mu=0$ 和 $\mu=\pm2$。第二行复行列式的常数项为一，两份实际外颜色都为 $-1$。逐个应用148.2，而不拆开 $D$ 的输入和，得到

$$
\begin{aligned}
O_{0,j}^e&=\sigma_\mu
\bigl(2\mu x^2Y+e\,2j\mu\sigma_jx^3X\bigr),\\
O_{1,j}^e&=-2(\mu+ej)x^2Y+e\,2j(\mu+ej)x^3X.
\end{aligned}
\tag{151.5}
$$

故实际外差与PB所需右侧的逐行对照为

$$
\begin{aligned}
O_{0,j}^+-O_{0,j}^-&=4j\mu\sigma_j\sigma_\mu x^3X,&
-2r_0\circ v_{0,j}-2q_\mu\circ z_{0,j}&=4j\mu x^3X,\\
O_{1,j}^+-O_{1,j}^-&=-4jx^2Y+4j\mu x^3X,&
-2r_1\circ v_{1,j}-2q_\mu\circ z_{1,j}&=-4jx^2Y+4j\mu x^3X.
\end{aligned}
\tag{151.6}
$$

相减即148.6。对 $j\mu\ne0$，第一行成立当且仅当 $\sigma_j=\sigma_\mu$；第二行在全部实参数上成立。$j\mu=0$ 时第一行也成立，没有从非零参数外推其值。

返回原出现表 $j=(3,1,2)$、原 $\kappa,\rho,\chi$，不删除任何一个外出现。由

$$
\sum_j\kappa_jj=0,\qquad
M:=\sum_j\kappa_jj\sigma_j
=3\sigma_3-\sigma_1-2\sigma_2=-4,
$$

和151.5逐项相加，得到

$$
\begin{aligned}
T(q_\mu)
&=\sum_{\lambda,j,e}\rho_{\lambda,j}eO_{\lambda,j}^e
=-4\mu\sigma_\mu Mx^3X
=16\mu\sigma_\mu x^3X,\\
H&=-\delta,\qquad g\circ H=H,\qquad
C_0(\delta,q_\mu)=8\mu x^3X.
\end{aligned}
\tag{151.7}
$$

145.6中只展开已知平方的部分，以及 $z_{1,j}-z_{0,j}=t_j$，仍在当前总表中准确成立。保留PB残差后，该既有锚定计算的形式是

$$
\sum_{\lambda,j}\rho_{\lambda,j}\mathcal R_{\lambda,j}(\mu)
=T(q_\mu)-2g\circ H-2\delta.
\tag{151.8}
$$

这里没有在不满足PB的表中套用145.5的零残差结论。由于当前 $g\circ H=-\delta$，151.8等于151.7的 $T(q_\mu)$，给148.7第一行。再用同一个150.5的 $\ell$，得到 $64\mu\sigma_\mu$。

全部正分量也逐份保留：对150.8的每个 $\omega$，都有

$$
\sum_{\lambda,j}\rho_{\lambda,j}\omega(\mathcal R_{\lambda,j}(\mu))
=\omega(T(q_\mu)-2g\circ H-2\delta)
=16\mu\sigma_\mu\omega(x^3X).
\tag{151.9}
$$

按146.3的原有符号和系数合回同一个 $\ell$，才得到148.7的检测值；不是把每个正分量的右侧都换成该检测值。正分量仍有150.8的原质量，且150.9逐个控制全部外出现。任何零质量或数值重合都不删去。

因此 $\mu=0$ 准确返回150.6，而每个非零实 $\mu$ 都检出混合失败。例如 $j=2,\mu=1$ 时 $\mathcal R_{0,2}(1)=-16x^3X$、$\ell(\mathcal R_{0,2}(1))=-64$。这是全实公式的一个代入，不是只靠该有限样本断言统一结论。第4项得证。∎

## 152. 非零多项式轮廓中的不同两色行列式机制被排除

**定理148.2第5项的证明。** 固定两个颜色 $s_0,t_0\in\{1,-1\}$，在148.1的全部原输入上定义

$$
\varepsilon_{s_0,t_0}(A,B)=
\begin{cases}s_0,&\det(A+iB)\equiv0,\\t_0,&\det(A+iB)\not\equiv0,
\end{cases}
\qquad D_{s_0,t_0}=\varepsilon_{s_0,t_0}C_0.
\tag{152.1}
$$

这限定的是固定两色总表类，不允许颜色另依赖输入、读者、次数或端点。取任意非零实多项式 $p_0,h_0$，满足 $p_0(0)=h_0(0)=0$，并令

$$
F_0=p_0X,\qquad G_0=h_0Z,\qquad
\sigma_j=\varepsilon_{s_0,t_0}(F_0,jG_0).
\tag{152.2}
$$

此处 $h_0$ 是多项式轮廓，不是150固定检测器的 $h$。对任意实 $j,\mu$，考虑同一总表实际生成的 $\operatorname{PB}_{D_{s_0,t_0}}(jG_0;F_0,\mu G_0)$。其共享同轴回复为零，实际位移为

$$
v=-j\sigma_jp_0h_0Y-j\mu h_0^2I,\qquad z=0.
$$

对每个端点 $e=\pm1$，直接计算

$$
\begin{aligned}
\det\bigl(F_0+ev+i\mu G_0\bigr)
&=(\mu^2h_0^2-p_0^2)(1+j^2h_0^2),\\
D_{s_0,t_0}(F_0+ev,\mu G_0)
&=\sigma_\mu\bigl(\mu p_0h_0Y
+e j\mu\sigma_jp_0h_0^2X\bigr).
\end{aligned}
\tag{152.3}
$$

因 $1+j^2h_0^2$ 的常数项为一，外颜色恰等于 $\sigma_\mu$，并不需要除以 $p_0$ 或 $h_0$。所需PB右侧为 $2j\mu p_0h_0^2X$，故实际残差准确为

$$
2j\mu(\sigma_j\sigma_\mu-1)p_0h_0^2X.
\tag{152.4}
$$

非零多项式之积非零。因此若这个轮廓上所有非零 $j,\mu$ 的混合行都成立，则所有非零 $j$ 上的 $\sigma_j$ 必相同。若再要求对全部152.2的轮廓成立，可取任意实 $c\ne0$ 及 $p_0=ch_0$。种子行列式为 $(j^2-c^2)h_0^2$；$j=\pm c$ 取色 $s_0$，而任何其它非零 $j$ 取色 $t_0$。152.4迫使 $s_0t_0=1$，即 $s_0=t_0$。

反之常色表是已知的 $+C_0$ 或 $-C_0$ 普通／相反乘法模型，完整PB直接复用原多项式卷8.1所引的模型接口。不另作标准模型分类。上述计算还包括零参数的零残差，但排除不同颜色只用两个非零参数。没有取点评价、使用逆元、加入原投影或假定响应正则性。第5项得证，定理148.2全部证明完成。∎

## 153. 共同插值、完整原域与七项来源的准确适用边界

**定义 153.1（新增关系与复用结果的分界）。** 148–152的承重增量是同一个行列式着色总表上两个全原重复演员族的共同保持，以及在全部实共同第三标签下保留两行、$H$、十二个外出现和全部正分量质量的同检测器混合残差；152将它用于明定的多项式轮廓两色类。行列式乘法性、Pauli恒等式、正C*二表、正读取延拓与GNS均为成熟中间工具，145的锚定平方、146的正分量和原框架、普通／相反乘法、既有核恢复和完整域分类均只作复用，不另计为新的定理。

103–108及123–125的轨道反号总表与148.2不是同一映射。前者已付的标量第三标签、乘积铅笔及多项式自作用族不转给当前表；其107.6和125.2的重复演员失败也不转给当前表。148.4只断言准确写出的两个全原族。反过来，151已经证明当前表不满足完整PB，因此它不是FULLPB模型，不反驳完整PB充分性，也不是一般重构。

共同插值的准确成熟参照是Ayupov、Arzikulov、Umrzaqov、Nuriddinov，[*2-Local and local derivations on Jordan matrix rings over commutative involutive rings*](https://arxiv.org/html/2108.03993v4)，arXiv:2108.03993v4，§2的定义和Theorem 4。该定理在其含单位、交换、对合且二可逆系数环上的完整自伴矩阵Jordan环中，要求每两个输入共用同一个内导子；该内导子本身加性。这里不能以Banach范数不完备解释其不适用，因为该环定理没有Banach完备前提。对当前同一行 $T_F(B)=D(F,B)$，150.1直接给

$$
T_F(G)=-2x^2Y,\qquad T_F(2G)=4x^2Y\ne2T_F(G).
\tag{153.1}
$$

所以甚至这两个输入都没有共同加性插值器；该两点算术复用108.4所用的共同插值判据，不另立为新定理。并且标量端点的 $E$ 不直接等于该文要求的完整矩阵环。文献只辨认缺失前件，不参与149–152的证明。此处归为 $\texttt{repo-derived}$ 的有界范围综合，不声称历史优先权、文献穷尽、形式核验或物理实现。

完整域中已付的中央抽取及运输，继续按[混合响应续卷126–130](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES_CONTINUATION.md#126-已分类中央角的背景独立性不需要有限性)与147.2使用；它们要求同一个完整原 $E=M_{\rm sa}$ 及其合法坐标、酉元或谱构造。148的域不是该完整域，且一般原域甚至未必使 $E+iE$ 结合闭合。行列式坐标和152的符号表示没有推广为任意原 $D$ 的表示。

**定义 153.2（一般原检测预算及全部同源义务保持）。** 一般原域中未解决的仍是147.1的同一任务：从全部实际原P2及完整PB，在不预设 $D$ 线性、连续、协变、符号交换子表示或原谱标签的条件下，控制同一个 $T(q)-2(a+u)\circ H=2\delta$，在146的同一个 $\ell$ 及全部实际正分量质量下给出目标相关联合预算或实际运输。151的残差计算只排除一个类，既没有给该一般预算，也没有证明该预算不存在。原域可不完备、无原子、不可分；不能以此多项式例或已分类完整域替换它。对148.4这两个重复演员族继续抽样已无法排除148.2，因为149已证明它们的完整量词；真正增加区分信息的是151的实际混合调用。

本组完整合取[147.3](#147-原域预算缺口成熟交叉配平工具与全部来源合同)及[SF105.1第1–7项全文、式105.1–105.7](AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md#105-七项真实同源物理来源的完整合同)，连同其中SF96.1及全部逐项引用的上游定义、源身份、条件和量词；该合取不由下面的范围说明替代。唯一原 $\Omega/\mathrm{native}$、原 $E,C,u,N,\mathcal P,S,D$、全原标签全向量的共同全词 $K/J/q$、零及任意有限词长、跨评价配对、parent/ready、实际控制和相干准备均保持原要求。150的数学 $\beta$、GNS、$x,j,\mu$ 不改认作这些物理来源。

全部原准备、事件、效果、完整Born菜单及接受端、共同根、抽签、mark、C12/A12/BI12/P9及独立 $W_e$、中间切口、零／不等／次归一质量、中央／经典／不等维／静默块继续保留。真正相关的非零原联合、共同实现、忠实同向交换局部腿、生成分离、重数和每层实际同源参考不由相同边缘或数学张量代替。每条typed未归一CP回溯、Kraus适用域、每个有限参考深度与每个正精度、精确累计支持、全系统环境及全部成功／失败／细记录／port／post-port输出、每份输出的每个仍合法未来仍按原合同供应。

整台仪器、完整typed单位分区、TP、原平方根可执行词、Lüders的全输出逐射线校准、真正分组遗忘、AC、$N_u$、X/Xs保持各自全部前件。全部合法顺序／自适应／并行历史与未来、环境记录泄漏、停止拒绝销毁、同数两侧及逆向真实双向返回、完整活动输入读后CountRead、两条负提升活路及相干聚合、精确 $B$ 与闭 $B_{\rm cl}$、原独立彩票和全部拒绝叶，均不截成有限角。无限或非离散记录、可数可加、正常性、指定前对偶与收敛仍须原扩展来源；未定义请求保持未定义。

保持原域的动力、实际门和相位及逆、可逆一参数群、物理钟与单位、强酉实现、生成元域、Hamiltonian能量、共同仪器和同一个正 $\hbar$ 继续保持同源。原 $\sigma,t_0,d$、固定域、resolvent和 $3s+r\le1$ 不与本组着色或多项式参数混同。七项须在同一原世界共同实现，不能分别另选来源。即使以后在一般原域证明 $w=0$，后续全域旧乘法、概率、仪器、相关联合、全部合法历史／未来／真实返回及物理尺度的原桥仍须逐项连接；本组没有完成、否定或缩减完整量子起源目标。

## 追加锚（本行以下为增补区）

## 154. 同一实际输入的投影基锚定与准确未证接头

**约定 154.1（原响应、已构造乘法与实际标签）。** 原问题仍取[平方丛卷51.1、61–64][AP-SQ]的完整截面原域及同一未知总映射 $D:E^2\to E$，保留准确锥、原单位、范数、全部A1–A3、两向P2和全部实际三元组PB，以及全部零、不等、次归一质量。基空间为任意非空紧Hausdorff空间，固定有限秩 $n\ge3$。先用既有取向构造同一复代数丛 $M$，取 $E=M_{\rm sa}$，在该乘法中写

$$
r\circ t=(rt+tr)/2,\qquad K(r,t)=i[r,t]/2.
\tag{154.1}
$$

这不预设旧 $D=K$，也不预设旧 $D$ 线性、连续、局部、协变或下降。这里 $K$ 是已知候选，与物理来源中的共同全词核 $K$ 区分。对任意总响应，实际 $\mathrm{PB}(a;b,d)$ 的标签为

$$
v=D(a,b)-a\circ d,\quad w=a\circ b+D(a,d),\qquad
r_\pm=b\pm v,\quad s_\pm=d\pm w.
\tag{154.2}
$$

原平方PB与响应差版准确为

$$
\begin{gathered}
q_D(r_++is_+)=q_D(r_-+is_-),\qquad
q_D(r+it)=r^2+t^2+2D(r,t),\\
D(r_+,s_+)-D(r_-,s_-)=-2b\circ v-2d\circ w.
\end{gathered}
\tag{154.3}
$$

原评价分离使这些成为元素等式。展开平方差即见两式等价；平方版左端减右端的残差是响应差版残差的两倍。

**命题 154.2（一个实际截断取得完整投影基）。** 给定任意实际 $a\in E$ 及 $x_0\in X$，存在图 $O\ni x_0$、实连续截断 $h$ 和图内常值秩一投影 $p_1,\ldots,p_{n^2}$，使

$$
0\le h\le1,\quad h=1\text{ 于 }x_0\text{ 邻域},\quad
\operatorname{supp}h\subset O,\qquad
\operatorname{span}_{\mathbb R}\{p_j\}=H_n(\mathbb C).
\tag{154.4}
$$

令 $q_j=hp_j$ 于图内、图外延零，则它们是同一原域中的实际截面，且 $D(a,q_j)=K(a,q_j)$ 是完整截面等式。

证明。在乘法图中取 $a_0=a(x_0)$ 的秩一特征投影 $p_0$。对附近秩一 $p$，有

$$
\|(1-p)a(x)p\|\le\|a(x)-a_0\|+2\|a_0\|\,\|p-p_0\|.
\tag{154.5}
$$

缩小 $O$ 和 $p_0$ 附近开放投影片 $V$，使右端对全部 $x\in O,p\in V$ 小于 $1<2$。[平方丛卷55.1证明中55.9之后][AP-SQ]的开放投影片张成性质给 $n^2$ 个实基投影；紧Hausdorff正规性给同一个 $h$。

完整截面域中，图内常值矩阵乘支撑截断后延零，故点评价满射。在 $h(x)\ne0$ 处，对原实际标签 $(q_j,a)$ 应用[OP80.1、82.1、83.1][AP-OP]：首像为 $h(x)p_j$，连接为 $(1-p_j)a(x)p_j$。OP83.1允许任意实首系数、任意对角部分、任意补空间及其他块背景和全部实际原代表；不删除 $a$ 的背景。其共同符号按已构造取向给154.1，故 $D(q_j,a)(x)=K(q_j,a)(x)$。

在 $h(x)=0$ 处，按[平方丛卷41.4、62.1][AP-SQ]，当前完整 $E$ 本身是含单位实JB环境，锥与范数准确，$\pi=\operatorname{ev}_x:E\to H_n(\mathbb C)$ 是满Jordan商，原域包含取恒等即满足OP80.1。任选该纤维中 $a(x)$ 的秩一特征投影 $p$，则 $\pi q_j=0=0p$ 且 $\|(1-p)a(x)p\|=0<2$；对同一实际 $(q_j,a)$ 直接应用[OP83.1][AP-OP]的 $\mu=0$ 情形及其全部实际原代表结论，得 $D(q_j,a)(x)=0=K(q_j,a)(x)$。这里 $p$ 只是商内数学投影，无须实际提升或连续选择；没有替换原输入，也不先设 $D$ 下降。原反对称性及点评价分离合并全部点，得到完整截面等式。只使用已知截面 $a$ 的连续性，未使用未知 $D$ 的输入连续性。∎

**说明 154.3（基完备与迹相容分开）。** 对上述实际锚，尚需从原关系推出

$$
\mathsf{TS}_j:\quad
\operatorname{Tr}_{x_0}\{D(a,b)(x_0)p_j+b(x_0)D(a,q_j)(x_0)\}=0.
\tag{154.6}
$$

若这些等式全部成立，154.2及迹循环恒等式 $\operatorname{Tr}(bK(a,p))=-\operatorname{Tr}(K(a,b)p)$ 给 $\operatorname{Tr}_{x_0}(\Delta p_j)=0$，其中 $\Delta=(D(a,b)-K(a,b))(x_0)$。投影实基及迹配对非退化性给 $\operatorname{Tr}_{x_0}(\Delta^2)=0$，遂有 $\Delta=0$。这只是充分性，不把154.6添成原公理。以下构造检验一组指定有限PB关系的推理边界。

## 155. 固定有理矩阵、同一旧值与严格正余量

**定义 155.1（实际矩阵模型）。** 取一点基空间及完整 $E=H_4(\mathbb C)$，使用通常乘法、单位 $I_4$、正锥、算子范数和全部数学正读取 $\gamma(T)=\operatorname{Tr}(\rho T)$，$\rho\ge0$，质量不归一。置

$$
\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
\sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
c=\frac{12}{13},\quad s=\frac5{13},\quad B=\frac5{24}=\frac{s}{2c},
\tag{155.1}
$$

$$
a=\frac{\sigma_z}{2}\oplus\frac{\sigma_z}{2},\qquad
b=B\sigma_x\oplus\left(\frac{I_2}{2}+\sigma_x\right),\qquad
q_0=\frac{I_2+c\sigma_z+s\sigma_y}{2}\oplus0
=\frac{(5e_1+ie_2)(5e_1+ie_2)^*}{26}.
\tag{155.2}
$$

这里 $e_j$ 为 $\mathbb C^4$ 标准基，故 $q_0$ 是秩一投影。对全部秩一 $q$，$\|(1-q)aq\|\le\|a\|=1/2<1$。预定旧行值为零、全部秩一行值为 $K$，并据此定义同一实际PB的标签

$$
\begin{gathered}
C=a\circ b,\quad G(q)=K(a,q),\quad v(q)=-a\circ q,\quad w(q)=C+G(q),\\
r_\varepsilon(q)=b+\varepsilon v(q),\quad
s_\varepsilon(q)=q+\varepsilon w(q),\qquad
R(q)=-2b\circ v(q)-2q\circ w(q),\quad\varepsilon=\pm1.
\end{gathered}
\tag{155.3}
$$

Pauli乘法及 $Bc=s/2$ 给

$$
\begin{gathered}
C=0\oplus\sigma_z/4,\quad G(q_0)=s\sigma_x/4\oplus0,\\
v(q_0)=-(\sigma_z+cI_2)/4\oplus0,\quad
w(q_0)=s\sigma_x/4\oplus\sigma_z/4,\\
b\circ v(q_0)=-s\sigma_x/8\oplus0,\quad
q_0\circ w(q_0)=s\sigma_x/8\oplus0,\quad R(q_0)=0,\\
\operatorname{Tr}(bG(q_0))=Bs/2=s^2/(4c)=25/624>0.
\end{gathered}
\tag{155.4}
$$

**引理 155.2（非奇异实铅笔留出P2余量）。** 对自伴 $r,t$、单位向量 $\xi$，记

$$
g_{r,t}(\xi)=\|r\xi\|^2\|t\xi\|^2-
\bigl(\operatorname{Re}\langle r\xi,t\xi\rangle\bigr)^2.
\tag{155.5}
$$

若全部非零实组合 $\mu r+\nu t$ 可逆，则 $g_{r,t}(\xi)>0$：实Cauchy–Schwarz等号会使两个向量实线性相关，产生消去 $\xi$ 的非零实组合，矛盾。反过来，所有单位向量上的严格正性也排除任何非零实组合奇异。

在 $q_0$，外行的两块准确为

$$
\begin{gathered}
r_\varepsilon^{(1)}=B\sigma_x-\varepsilon(\sigma_z+cI_2)/4,\quad
s_\varepsilon^{(1)}=(I_2+c\sigma_z+s\sigma_y)/2+\varepsilon s\sigma_x/4,\\
r_\varepsilon^{(2)}=I_2/2+\sigma_x,\qquad s_\varepsilon^{(2)}=\varepsilon\sigma_z/4.
\end{gathered}
\tag{155.6}
$$

使用 $\det(xI+y\cdot\sigma)=x^2-|y|^2$，得两个负定实二次式

$$
\begin{aligned}
\det(\mu r_\varepsilon^{(1)}+\nu s_\varepsilon^{(1)})
&=-\frac{s^2}{16}\left\{\mu^2+
\left(\nu+\varepsilon\frac{4B}{s}\mu\right)^2\right\},\\
\det(\mu r_\varepsilon^{(2)}+\nu s_\varepsilon^{(2)})
&=-3\mu^2/4-\nu^2/16.
\end{aligned}
\tag{155.7}
$$

第一式可由单位及Pauli系数 $-\varepsilon\mu c/4+\nu/2$、$\mu B+\varepsilon\nu s/4$、$\nu s/2$、$-\varepsilon\mu/4+\nu c/2$ 直接展开；两式对 $(\mu,\nu)\ne(0,0)$ 严格负。紧单位球面及两个符号给

$$
g_0=\min_{\varepsilon,\|\xi\|=1}
g_{r_\varepsilon(q_0),s_\varepsilon(q_0)}(\xi)>0.
\tag{155.8}
$$

已知155.3的连续性、$R(q_0)=0$ 及155.4的严格正迹，给秩一投影开放邻域 $U\ni q_0$，对全部 $q\in U$、符号和单位向量同时有

$$
g_{r_\varepsilon(q),s_\varepsilon(q)}(\xi)\ge g_0/2,\qquad
\|R(q)\|^2/4<g_0/4,\qquad \operatorname{Tr}(bG(q))>0.
\tag{155.9}
$$

于是外行输出 $C_\varepsilon(q)=\varepsilon R(q)/2$ 的纯向量P2行列式大于 $g_0/4$。其对角非负，二表严格正；外值之差为 $R(q)$。这些是构造的连续函数，不是未知旧响应的正则性假设。

任意 $\rho\ge0$ 的谱分解将相应二表写成纯向量正二表的有限非负和，故覆盖全部质量 $\operatorname{Tr}\rho$；零质量给零表，全程不作质量除法。旧行输出零有实Gram正性，标准行输出 $K$ 有复Gram正性。这里没有拼接一般复三表，也没有生产物理准备。∎

## 156. 三十三张实际二维平面的严格选择

**引理 156.1（旧、正、负三平面分离）。** 置

$$
\Pi_0=\operatorname{span}_{\mathbb R}(a,b),\qquad
\Pi_\varepsilon(q)=\operatorname{span}_{\mathbb R}(r_\varepsilon(q),s_\varepsilon(q)).
\tag{156.1}
$$

旧平面的两块行列式为

$$
\det(\mu a_1+\nu b_1)=-\mu^2/4-B^2\nu^2,\qquad
\det(\mu a_2+\nu b_2)=-\mu^2/4-3\nu^2/4.
\tag{156.2}
$$

故旧平面每个非零元可逆，且 $a,b$ 实独立；155.9同样保证所有外平面为二维、每个非零元可逆。

在 $q_0$，外行第二块为 $r_\varepsilon^{(2)}=b_2$、$s_\varepsilon^{(2)}=\varepsilon a_2/2$。若 $\Pi_\varepsilon(q_0)=\Pi_0$，将 $r_\varepsilon=\alpha a+\beta b$ 逐块比较，第二块的 $a_2,b_2$ 独立迫使 $\alpha=0,\beta=1$；第一块遂迫使 $v(q_0)=0$，与155.4矛盾。若 $\Pi_+(q_0)=\Pi_-(q_0)$，写 $s_-=\alpha r_++\beta s_+$，第二块迫使 $\alpha=0,\beta=-1$，但 $s_-+s_+=2q_0\ne0$。三者两两不同。

在实Hilbert空间 $(E,\langle X,Y\rangle=\operatorname{Tr}(XY))$ 中，令 $L_\varepsilon(q):\mathbb R^2\to E$ 的两列为外行，其平面的正交投影为 $L_\varepsilon(L_\varepsilon^*L_\varepsilon)^{-1}L_\varepsilon^*$。独立性保证Gram逆存在，故平面连续。取三个基点平面的两两不交Grassmann邻域，缩小 $U$，使全部正外平面、全部负外平面分别落入各自邻域，旧平面在第三邻域。因此任意 $q,q'\in U$ 均有 $\Pi_+(q)\ne\Pi_-(q')$，且外平面均异于 $\Pi_0$。∎

**引理 156.2（固定平面的坏集无内点）。** 对任意固定二维实平面 $\Pi$ 及符号，集合

$$
F_{\Pi,\varepsilon}=\{q\in U:\Pi_\varepsilon(q)=\Pi\}
\tag{156.3}
$$

相对闭且无内点。闭性来自156.1的连续性。为证后者，定义实线性 $K_a(X)=i[a,X]/2$。迹循环性给 $\langle X,K_aY\rangle=-\langle K_aX,Y\rangle$，故

$$
\langle X,(I\pm K_a)X\rangle=\|X\|_{\rm HS}^2.
\tag{156.4}
$$

于是 $I\pm K_a$ 核零，有限维使之可逆。若 $q\in F_{\Pi,\varepsilon}$，必要地 $s_\varepsilon(q)=(I+\varepsilon K_a)q+\varepsilon C\in\Pi$，故

$$
F_{\Pi,\varepsilon}\subset
(I+\varepsilon K_a)^{-1}(\Pi-\varepsilon C).
\tag{156.5}
$$

右端是实仿射二维空间，线性包维数至多三。若坏集含非空开放投影片，该投影片就全部包含在右端，从而其线性包至多三维；但任意非空开放秩一投影片张成实维十六的 $E$，矛盾。这里使用的是坏集包含于仿射空间的必要方向，未将其误作等价。

所用开放张成性质可由迹零化核对：若Hermitian $H$ 在开放投影片上满足 $\operatorname{Tr}(Hq)=0$，则 $z^*Hz$ 在投影逆像这个非空实开集上恒零。实二次多项式恒零及极化给 $H=0$。因而真线性子空间与投影片的交也闭且无内点。∎

**命题 156.3（完整基与全部平面互异）。** 从 $q_1=q_0$ 开始，已选 $m<16$ 个实独立锚时，避开其真线性包及全部 $F_{\Pi_\eta(q_j),\varepsilon}$，其中 $j\le m$、$\eta,\varepsilon=\pm1$。有限个相对闭无内点集不能覆盖非空开集：逐一移除时，每个非空开集仍留有非空开子集。故可选下一 $q_{m+1}\in U$。新锚的两外平面彼此不同且异于旧平面由156.1保证，与以前全部外平面的区别由所避坏集保证。递归至十六个即得实基，且 $\Pi_0$ 与三十二张 $\Pi_\varepsilon(q_j)$ 两两不同。此证明不需要迹水平互异，也不以“通常位置”代替存在论证。∎

## 157. 每张平面的有向面积定义一个总响应

**定理 157.1（全部实换基协变的有限关系反例）。** 对156.3的锚存在同一个总映射 $\widehat D:E^2\to E$，具有全部数学A1–A3、全部正读取P2，并对每个实 $2\times2$ 矩阵 $T$（包括奇异矩阵）满足

$$
\widehat D\!\left(T\binom XY\right)=\det(T)\widehat D(X,Y).
\tag{157.1}
$$

它保持全部秩一行、交换零行、标量零行，满足全部十六个实际 $\mathrm{PB}(a;b,q_j)$ 和全部标量演员PB；然而 $\widehat D(a,b)=0$，且每个 $\mathsf{TS}_j$ 都失败，其中首读数为 $25/624$。

证明，先定义总响应。在 $\Pi_0$ 以有序基 $(a,b)$ 取面积输出 $0$；在 $\Pi_\varepsilon(q_j)$ 以有序基 $(r_\varepsilon(q_j),s_\varepsilon(q_j))$ 取面积输出 $C_{j,\varepsilon}=\varepsilon R(q_j)/2$。对实独立输入 $X,Y$，若其平面是上述某张异常平面，唯一写成

$$
X=\alpha r+\beta s,\quad Y=\gamma r+\delta s,\qquad
\widehat D(X,Y)=(\alpha\delta-\beta\gamma)C_{\Pi}.
\tag{157.2}
$$

其他独立输入取 $K(X,Y)$；全部依赖输入统一取零，与 $K$ 一致。独立输入的张成平面唯一，三十三张平面互异且各基独立，所以定义无冲突。单个向量可属于多个平面，唯一性并不依赖向量所属平面唯一。

若 $T$ 可逆，输入的张成平面不变；异常分支的系数矩阵左乘 $T$，行列式相乘，默认分支则由 $K$ 的交替双线性给157.1。若 $T$ 奇异，输出对依赖，等式两边均零；原输入依赖时对任何 $T$ 也均零。因此157.1覆盖所有实矩阵。特别得到每槽实齐次、反对称、每槽奇性、$SO(2)$相位不变，以及每张实二维平面内部的剪切、放缩和全部换基一致性。

对任意正读取，写输出为 $C'$ 的二表为

$$
M_\gamma(r,t;C')=
\begin{pmatrix}\gamma(r^2)&\gamma(r\circ t)-i\gamma(C')\\
\gamma(r\circ t)+i\gamma(C')&\gamma(t^2)\end{pmatrix}.
\tag{157.3}
$$

Jordan实Gram部分按任意实 $T$ 合同变换；虚部为 $\gamma(C')\begin{pmatrix}0&-i\\i&0\end{pmatrix}$，二维反对称矩阵满足 $TJT^{\mathsf T}=\det(T)J$。故包括奇异 $T$ 在内，

$$
M_\gamma\!\left(T\binom rt;\det(T)C'\right)
=T M_\gamma(r,t;C')T^{\mathsf T}.
\tag{157.4}
$$

155.9已使所有异常外基表正，旧基表有实Gram正性，合同遂使每张异常平面全部独立对的P2成立。其余对有标准复Gram正性，依赖对的零输出有实Gram正性。155.2的正和论证给全部未归一质量和零质量，两向表由换序同样成立，故A1准确支付。

每个异常平面的每个非零元都可逆，所以异常独立对不含非零秩一输入。任意 $\lambda p$ 秩一行（含 $\lambda=0$）遂保持 $K$。若异常独立对交换，则有共同特征向量；其两个实特征值总有一组非全零实系数使组合为零。输入独立保证该组合矩阵非零，却消去该向量，与非奇异性矛盾。因此全部交换对默认 $K=0$；同生成元实多项式行、全部标量及单位零行也保持。

A2只读同一固定Jordan实部：任意实系数的二次值为 $\gamma((\sum t_j a_j)^2)\ge0$，相加三表 $(x+y,x,y)$ 的向量 $(1,-1,-1)$ 及所有排列准确给零。A3由 $I_4^2=I_4$ 及谱演算的 $0\le e\le\vartheta I_4\Rightarrow e^2\le e$ 给出，保留同一固定有理 $0<\vartheta\le1$。不由此声称一般复三表正性。

秩一行已付，故155.3确是该总映射从同一个旧值 $\widehat D(a,b)=0$ 生成的实际标签；157.2给两外值之差 $R(q_j)$，同时支付十六次实际PB。各迹读数均为 $\operatorname{Tr}(bG(q_j))>0$，首个由155.4为 $25/624$。没有为不同调用另换内值。

对标量演员 $\lambda I_4$，两内值均零，外对由 $(b,d)$ 分别经 $\begin{pmatrix}1&-\lambda\\\lambda&1\end{pmatrix}$、$\begin{pmatrix}1&\lambda\\-\lambda&1\end{pmatrix}$ 产生。两行列式均为 $1+\lambda^2$，157.1使两外响应相等；PB右端 $2\lambda b\circ d-2\lambda d\circ b=0$。故全部标量演员PB成立。∎

**命题 157.2（同一个三维实窗口中的共同边可加性失败）。** 对157.1的同一总响应，置

$$
V=\operatorname{span}_{\mathbb R}(a,b,q_0),\qquad
\Pi_t=\operatorname{span}_{\mathbb R}(a,b+tq_0)\quad(t\in\mathbb R).
\tag{157.5}
$$

则 $\dim_{\mathbb R}V=3$，且存在 $t\in\{1,\ldots,33\}$，使 $\Pi_t$ 不属于157.1的三十三张异常平面，并有

$$
\widehat D(a,b+tq_0)-\widehat D(a,b)-t\widehat D(a,q_0)
=K(a,b)=-\frac B2\sigma_y\oplus\left(-\frac12\sigma_y\right)\ne0.
\tag{157.6}
$$

证明。155.2式中的 $q_0$ 是非零秩一投影，而156.2式保证旧平面 $\Pi_0$ 的每个非零元可逆，故 $q_0\notin\Pi_0$。结合 $a,b$ 实独立，得到 $a,b,q_0$ 实独立，因而 $V$ 恰为三维。

对每个实 $t$，$a,b+tq_0$ 独立，故 $\Pi_t$ 确为二维。若 $\Pi_t=\Pi_s$，则 $b+tq_0=\alpha a+\beta(b+sq_0)$；比较这三个独立向量的系数，得 $\alpha=0,\beta=1,t=s$。所以各平面两两不同，所有非零 $t$ 还满足 $\Pi_t\ne\Pi_0$。

异常平面共三十三张，其中一张为旧平面 $\Pi_0$。因此 $t\in\{1,\ldots,33\}$ 的三十三张互异候选平面至多命中其余三十二张，至少一张非异常。这只是有限鸽巢存在证明，不指定或枚举哪个 $t$ 可用。

对选定的 $t$，总响应的默认分支给 $\widehat D(a,b+tq_0)=K(a,b+tq_0)=K(a,b)+tK(a,q_0)$；同时 $\widehat D(a,b)=0$，秩一行给 $\widehat D(a,q_0)=K(a,q_0)$。相减即为157.6，非零值由155.2式的Pauli乘法得到。这里展开的是已知双线性 $K$，没有展开或假定未知响应可加；157.1的实齐次性还给 $t\widehat D(a,q_0)=\widehat D(a,tq_0)$，故这准确检出以 $a$ 为共同边、在第二槽将 $b$ 与 $tq_0$ 相加时的失败。所有输入 $a,b,q_0,tq_0,b+tq_0$ 均在同一 $V$ 中。∎

这里只限制输入所在的实线性窗口；未要求 $V$ 对乘法或PB标签生成闭合，也不将它解释为物理三维空间。原完整PB及一般旧 $D$ 的研究目标保持。

两张平面可以交于一条线；该线上依赖对都输出零，不迫使它们各自的面积输出满足跨平面关系。GL(2)是构造时额外保持的更强对称，不声称由原PB已经推出。

## 158. 一条原PB用奇异铅笔检出同一总响应

**命题 158.1（已知内行与准确实际端点）。** 对157.1的同一 $\widehat D$，取

$$
P=E_{11},\quad Z_0=a+ib,\quad Z=(I_4+iP)^{-1}Z_0=u+id,
\qquad u=u^*,\ d=d^*.
\tag{158.1}
$$

此处 $u$ 是实际自伴标签，单位仍为 $I_4$。两内行 $\widehat D(P,u),\widehat D(P,d)$ 都等于 $K$。直接计算 $Z_0^*Z_0$ 的两块为 $(1/4+B^2)I_2-B\sigma_y$、$3I_2/2+\sigma_x-\sigma_y$，故

$$
\|Z_0\|^2=\max\{(1/2+B)^2,\ 3/2+\sqrt2\}<4.
\tag{158.2}
$$

这里 $1/2+B=17/24<1$ 且 $\sqrt2<3/2$。因 $\|(I_4+iP)^{-1}\|\le1$，有 $\|u\|,\|d\|\le\|Z\|<2$，两连接 $\|(1-P)uP\|,\|(1-P)dP\|$ 均严格小于二，也准确落在OP83.1的实际小连接范围，未删背景。

将这两个已知内值代入154.2，得到

$$
v+iw=iPZ,\qquad r_++is_+=(I_4+iP)Z=Z_0,\qquad
r_-+is_-=UZ_0,\quad U=(I_4-iP)(I_4+iP)^{-1}=\operatorname{diag}(-i,1,1,1).
\tag{158.3}
$$

正端实际标签恰为 $(a,b)$。写负端 $UZ_0=x+iy$，其第一块为

$$
x_1=\begin{pmatrix}0&k\\\bar k&-1/2\end{pmatrix},\qquad
y_1=\begin{pmatrix}-1/2&k\\\bar k&0\end{pmatrix},\qquad k=B(1-i)/2,
\tag{158.4}
$$

所以

$$
f(t):=\det(x_1+ty_1)=t/4-(B^2/2)(1+t)^2,\quad
f(0)=-B^2/2<0,\quad f(1)=1/4-2B^2=47/288>0.
\tag{158.5}
$$

连续性给 $t_0\in(0,1)$ 使第一块奇异；第二块未被 $U$ 改动，为 $x_2=a_2,y_2=b_2$，其行列式 $-1/4-3t_0^2/4<0$。故 $x+t_0y$ 奇异且非零。此外 $a_2,b_2$ 独立，故 $x,y$ 独立。其二维平面包含非零奇异元，不可能等于任何异常平面，因此负端响应默认 $K(x,y)$。

标准 $K$ 满足全部PB：对任意自伴演员 $A$ 及输入 $W$，已知内行给外端 $(I_4\pm iA)W$，两份 $q_K$ 均为 $W^*(I_4+A^2)W$。本调用与标准表共用两个内值及负外值，只将正外值从 $K(a,b)$ 改为零，故响应差版残差为

$$
\mathcal R_D=-K(a,b)=\frac B2\sigma_y\oplus\frac12\sigma_y\ne0,\qquad
\langle\xi,\mathcal R_D\xi\rangle=1/2,\quad \xi=(0,0,1,i)/\sqrt2.
\tag{158.6}
$$

原平方PB残差准确为 $q_{\widehat D}(Z_0)-q_{\widehat D}(UZ_0)=2\mathcal R_D=-2K(a,b)$，同一向量读数为 $1$。这条实际调用排除所定义的该份延续，不排除所有其他延续，也不是完整PB反模型。∎

## 159. 同转相位、完整来源与原目标的保留

**命题 159.1（相位改写不增加第二检测）。** 仅用反对称和每槽奇性，固定实际演员 $a$，将 $(b,d)$ 改成 $(-d,b)$。154.2给 $v'=-w,w'=v$，故 $r_\pm'=-s_\pm,s_\pm'=r_\pm$，两外响应及PB右端均不变。若 $e=D(a,b)-K(a,b)$、$g=D(a,d)-K(a,d)$、$Z=b+id$、$T=e+ig$，则 $Z'=iZ,T'=iT$，且

$$
(iZ)^*(iT)+(iT)^*(iZ)=Z^*T+T^*Z,\qquad q_D(i(r+it))=q_D(r+it).
\tag{159.1}
$$

因此同转只是同一实际关系的改写，不供应独立实部检测，也不能用一个抽象核内的误差替代实际总响应。∎

**约定 159.2（所有来源的无删减合取）。** 本组完整合取[本卷153.2、147.3][AP-PB]及其所纳入[SF105.1第1–7项全文、式105.1–105.7、SF96.1][AP-SF]和全部逐项上游定义、源身份、原域、对象、条件、实现、质量与量词。平方丛分支严格完整合取[平方丛卷64.1–64.3、47.1–47.13及48.1–48.3][AP-SQ]的全部候选、合同、公式、重构等价与七项条件消费者，包括根、静默及其他静态分支。各原文规定的固定上游版本身份不变；以下展开与原文同时合取，不以展开代替全文。

① 仍是唯一原 $\Omega/\mathrm{native}$、同一原 $E,C,u,N,\mathcal P,S,D$。具名可取得标签、全原向量与指定跨评价配对、同一共同全词 $K/J/q$、全部 $z,w$、空词及任意有限词长、parent／ready、原总映射先实际复合再取有限复线性包、合法控制、原门及相干准备均保持。数学迹、Gram、GNS及本模型的 $\widehat D$ 不替换指定共同网络，不生产任意向量准备或全 $B(H)$ 可取得像。

② 原态、事件、准确效果区间、完整Born菜单与接受归属、共同根、抽签、mark、C12/A12/BI12、预定有限强度、P9每个分支及独立 $W_e$、原 $g^*,d_s^*$ 读取顺序、AS/EC、菜单外OB、忠实二维到三维适配器、固定支持全质量及每个中间切口均保留。全部零、不等、次归一、中央、经典、不等维及静默质量保留；只有正确完整菜单和严格正总质量处归一，角菜单另需原条件化与正支持质量，更新另需严格正输出质量。

③ 每个实际非零真正相关联合仍须同一共同实现、忠实同向交换局部腿、旧局部乘法、共同生成分离、重数、全部真正相关输入、中央对、实际复制及每层同源参考。消费者要求的局部全矩阵前件不删；分别可达、相同边缘、辅助张量或共同数学取向不代付联合。

④ 每条typed原细分支的全部合法前后接、每份完整输出的每个仍合法未来、未归一回溯、反变复合、typed分区、全未来自然性、质量运输和原箭头商下降均保持。CP仍取完整同标签单位区间比较或整台实际递归参考；系统、整个环境、成功／失败／细记录／输入输出port／post-port及真遗忘、返回、合法复合都在同一可再应用规则类。每条根箭头、每个所需有限深度、每个正精度、忠实同向系统和参考腿、三个实际投影及单位实张成、支持内补、全部相关正输入、精确累计支持及交织夹界均保留；不要求一条物理无限链，不以形式参考代实际参考。

⑤ 整台仪器的全输入运输、完整typed菜单和接受端、全部环境及输出未来、真分组遗忘、AC、精确 $N_u$、X/Xs、每份原平方根可执行词及接受条件保持。逐支CP及完整typed单位分区才给TP；Lüders另需同一完整输出的投影效果、像内每条射线保持及完整校准。失败和零分支保类型、记录及未来；异类型不免费并成物理直和。同效果或概率不代付全输出。

⑥ 全部合法顺序／自适应／并行历史、环境、参考、细记录、泄漏、停止／拒绝／销毁、真分组遗忘、同数两侧及逆向真实双向返回、读后同一完整活动输入的全未来CountRead、活动ready、接受叶活动输出、第一消费者及具名分析词到全菜单接线均保持。两条负提升活路分别受控及相干聚合、精确 $B$ 与闭 $B_{\rm cl}$、两只独立九叶彩票、第九空程序、十六拒绝叶、相干 $I_3/3$ 返回保持。初始取得、有限树、被动精确解码和既有有限返回校准守原平稳、同源、同初始版本及实际域，不替代全未来Return。未定义请求仍未定义；无限或非离散记录、可数可加、正常性、指定前对偶及收敛另由原扩展来源承担。密度、迹类和Kraus均守原合格表示及收敛域。

⑦ 原全域乘法、保持可能不完备原域的流、实际门与相位及实际逆、同一过程的连续可逆CPTP一参数群、物理钟与单位、强连续酉实现、生成元域、Hamiltonian能量、共同仪器、共同作用量及同一个正 $\hbar$ 均保持。原 $\sigma,t_0,d$、固定域、resolvent和 $3s+r\le1$ 仍取原设备、参数和量纲；数学参数不生产物理钟。Schrödinger、密度及Heisenberg方程只在同一已识别乘法与各自可微域消费。七项必须在唯一原世界共同实现，不能逐项更换来源。

**说明 159.3（原分类与一般预算仍有准确边界）。** 原任意紧基上，合法旧响应强制复类型及连续乘法取向的既有结论保留；取向存在判据不等于认回任意给定旧响应的全部值。平方丛64的完整候选及重构仍保留 $\overline{L(X)}=X$，或明确另用56.2的 $\mathsf T_D$ 条件。56.1仍是 $\forall W\,\forall x_0\,\exists(O,h,f)$ 下同一旧值 $D(hx(W),hy(W))(x_0)=D(x(W),y(W))(x_0)$ 的受限比较；没有升级为任意截断或全部同像标签下降。55.1只运输实际截断 $hW$，原关系推出56.1的前件仍未证，本组既未证明也未反驳它。

准确说，沿64的原记号与完整定义，原候选与其重构保持为

$$
\begin{gathered}
\Gamma_{\rm fin}+[\overline L=X]+\mathsf H_{\rm fin}(D)+\mathcal C_{47}(\Omega;S,D)\\
\Longleftrightarrow\quad
\Gamma_{\rm fin}+[\overline L=X]+[\mathfrak J_x\cong_J H_n(\mathbb C)\ (\forall x)]+
\exists!\sigma\in\Gamma(X,\mathcal O_{\rm alg}),\quad
D=K_\sigma\ \land\ \mathcal C_{47}(\Omega;S,K_\sigma).
\end{gathered}
\tag{159.2}
$$

$\Gamma_{\rm fin}$、$\mathcal C_{47}$ 等仍取原完整定义。唯一性相对于给定旧 $D$，不声称全体数学取向唯一，也不把完整来源变成取向无关的自由附加数据。

一般原域从完整PB生产TS、识别全部旧值、去除稠密前件，以及147.1、153.2所述同一 $T(q)-2(a+u)\circ H=2\delta$ 在146同一 $\ell$ 和全部实际正分量质量下的目标相关联合预算或实际运输，均仍未解决。一般不完备、无原子、不可分原域、一般JB／type III、表示及全物理消费者不由此有限实例分类。未从原关系取得的共同实现者、加权迹等式或GL(2)律不作为原问题新增输入。

## 160. 面积几何的关系增量与完整中文图景

**定义 160.1（新增结果的归属与范围）。** 本组 $\texttt{repo-derived}$ 纸面综合是：用同一总映射中三十三张互异实际二维平面的有向面积，实现完整投影实基的十六个共享旧内值PB，保留全实配对矩阵协变、全部P2及秩一／交换行，却使全部所选TS读数严格正；再用非零奇异铅笔把另一条已知内行的实际PB接回旧行，明确检出这份构造。开放投影片张成、迹配对、Pauli乘法、谱演算、Gram正性、有限维紧性和二维面积行列式律均为复用工具，不另计新增定理或全球优先成果。

准确的不蕴含关系仅是“这些已列数学关系及十六个指定实际PB，不推出所选TS”；完整PB仍可能通过更多共用标签关系迫使TS，另一组有限调用也未被排除。158只排除所定义的该份延续，不证明所有延续均失败。本组不制造物理producer，不宣称原公理的新推论、完整PB反模型、全分类、文献穷尽、kernel证明或世界来源认证。

白话说，一对实独立输入确定一张二维平面。在这张平面上，本构造只指定一份有向面积的输出；以后无论怎样剪切、放缩、旋转或换坐标，答案都按面积行列式变化，所以平面内部的线性关系已经全部一致。两个向量退化到一条线上时面积为零，也与所有奇异换坐标一致。这比仅检查旋转多，但没有替原问题增加一条必须服从的新物理公理。

十六个投影探针构成完整线性读数基，每个探针的秩一行和相应直接PB都在同一张总响应表里正确，共用同一个旧答案；每张二表也对全部数学正读取和所有质量正确。然而旧答案与标准答案的迹偏差仍严格非零。探针的线性完备只是说“若全部正确迹读数为零，就能读出误差为零”，并不自动使读数归零，也不把这些投影变成正权组成的物理完整菜单。

不同二维平面可交于一条线；在线上面积都为零，并不能强迫两张平面的面积输出在跨平面相加时配合。157.2中，三根边已足以暴露跨平面相加不一致，全部输入同处一个三维实线性窗口。缺少的是跨平面共享实际标签的联合关系。158的额外检验把正端准确接到原旧行，负端则因含非零奇异方向落在所有异常平面之外，于是标准区域与旧答案直接相遇，读出非零残差并排除该构造。完整PB能否在原一般域中组织足够的这种关系，仍是原来的研究问题。即使静态数学接头补齐，原世界的准备、完整菜单、相关共同实现、全过程及全未来、真实返回和物理钟仍各须上述完整来源。

[AP-PB]: https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md
[AP-SQ]: https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_ZERO_DIMENSIONAL_CENTER_SQUARE_ORBIT_RECONSTRUCTION.md
[AP-OP]: https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md
[AP-SF]: https://github.com/the-omega-institute/trureturing/blob/39a0505470ea889dd9d4301ad60cd9506a5e8b58/docs/develop/theory/AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md

## 追加锚（本行以下为增补区）
