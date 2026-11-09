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
