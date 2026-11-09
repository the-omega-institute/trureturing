# 谱混合响应与直接窗口的边界

## 0. 记号与来源约定

**约定 0.1（编号与数学来源）。** 未加卷名的章节、声明及圆括号公式编号只指本卷 1–9。[中央卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 指《中央响应平方与径向一致》0–80（[所引版本](https://github.com/the-omega-institute/trureturing/blob/430db8df9f280f7cd6ffbc284b0b769d58da93eb/docs/develop/theory/AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)）；[三角卷](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 指《配平三角的共同取向与秩一响应续卷》；[静态卷](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md) 指《任意维静态量子重构》；[原多项式零响应卷](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md) 指《原多项式零响应与 Cayley 域边界》。各卷的同号陈述互不识别。[仿射平方固定文本](https://github.com/the-omega-institute/trureturing/blob/fb5e782ecc7b8f3bfc18856eacc6cb2f793db78a/docs/develop/theory/AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 53–59 专指该版本的仿射两平方坐标窗口；[中央卷 53–59](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 则是实际中央平方首标签的带权圆、模块及中央 Gram，不能以编号相同互换前件或结论。

**约定 0.2（同一原对象与环境运算）。** $E,C,u,N,\mathcal P,S,D$ 始终是同一原资料，$X$ 为其自身任意含单位实 JB 完成；只沿已给忠实含单位 JC 包含在 $A_0=C^*(X)$ 中读取。$ab$、$[a,b]$、谱和连续函数演算在指定环境中使用，$a\circ b$ 是同一原 Jordan 乘法；凡原输入调用 $D$，输入和输出都属于原 $E$。环境根、逆、谱投影、商代表、延伸态与极限不自动成为原标签、原操作或实际准备。固定 $h$ 的响应 $J=D(h,\cdot)$ 只先在每个自身圆使用，与原全词的 $J$ 角色区分；交叠 $P$ 与正评价族 $\mathcal P$ 区分；6.1 的 Jordan 同态 $q$ 与全词读数 $q$ 区分；例子中的 $R$ 是明确指定的矩阵函数，不能代替尚未全域恢复的原 R 关系。零对象、零输入、零质量、不同自身圆及所有原来源量词均保留。

## 1. 同一原候选与交叠的谱平方条件

**定义 1.1（完整原资料和固定原行）。** 完整保留 [中央卷 16.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)、[中央卷 32.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)、[中央卷 46.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的同一原 $(E,C,u,N,\mathcal P,S,D)$、A1–A3、准确锥、全部原 P2 与完整原 PB。原正实线性评价分离元素并准确决定锥，全部质量 $m_\alpha=\alpha(u)$ 允许为零、不等或次归一。A1 保持全部有向 Hermitian 二表正性；A2 保持原相加三表及排列的实部半正定和指定零二次值；A3 保持 $S(u,u)=u$ 及同一固定有理小效果窗。P2、PB 对全部原标签的准确元素式仍为 ([中央卷 32.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md))，不只要求下述条件分支成立。原来源与七项消费者完整取 [中央卷 52.1–52.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)。

仍令 $S=\circ$，$E$ 仅在自身任意含单位实 JB 完成 $X$ 中稠密，可不完备。沿 [中央卷 16.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的同一忠实、含单位、等距、保锥并反映锥的 JC 包含识别原元素，记

$$
E\subset X\subset(A_0)_{\rm sa},\qquad A_0=C^*(X).
\tag{1.1}
$$

不要求 $X=(A_0)_{\rm sa}$，不要求原域有原子、投影分解、谱根或逆元。一般 JB、无原子、型 II／III、中心、经典、不等维块及静默域的原量词均保留；这里使用的是完整候选已给的 JC 包含，而不是以一个有限矩阵世界替换它。零对象 $X=0$ 单列平凡成立。

固定真正原 $h\in E$、$h^2=u$，置

$$
V_h=\{v\in E:h\circ v=0\},\qquad Jv=D(h,v),\qquad
\mathcal R_\theta v=\cos\theta\,v+\sin\theta\,Jv.
\tag{1.2}
$$

准确复用 [中央卷 19.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)、[中央卷 20.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)、[中央卷 35.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)、([中央卷 46.3](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md))：$J$ 返回 $V_h$，且对全部原 $v\in V_h$ 和实 $s,\alpha,\beta$，

$$
\begin{gathered}
D(sh,v)=sJv,\qquad (Jv)^2=v^2,\qquad v\circ Jv=0,\\
J(\alpha v+\beta Jv)=\alpha Jv-\beta v,\qquad
\mathcal R_\theta\mathcal R_\psi v=\mathcal R_{\theta+\psi}v.
\end{gathered}
\tag{1.3}
$$

这些只在每个实际自身平面使用。不同平面之间的可加性不在前件内；也不另加旧 $D$ 的一般齐次、连续、可测、协变、一般单位或中央平移、$\mathsf F$、NN／Jacobi、原 R、输出局部闭合、一般商下降或完成延拓。

[中央卷 60–67](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的条件分支直接复用：对实线性原子空间 $W$，若每个 $w\in W$ 均有 $w^2\in\mathbb Ru$，则 [中央卷 62.1–62.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已给同一旧 $D|_{W\times W}$ 的实交替双线性及同一首方向混合 Gram，无须 $D(W,W)\subset W$；[中央卷 63.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已给原正交单位对及其响应生成的闭合三轴。这些作为既有结果，不在下述谱分支中重证或另计为新内容；一般 $V_h$ 不被替换成这样的 $W$。进一步，[中央卷 76.2、77.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已识别每个自身生成三轴 $U$ 上全部 $D(su+x,tu+y)=x\times y$；[中央卷 77.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已支付任意标量平方片 $W_0$ 的整个 $(\mathbb Ru+W_0)^2$ 上旧双线性，无需输出闭合。[中央卷 78.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已给生成四维窗的内在复 $M_2$ 乘法、原 R、有限复 Gram 及正质量实际完整菜单下的 Born。以下不重证或另计这些已付分支。

**定义 1.2（已知原交叠的非共振条件）。** 对原自伴 $P$，谱取同单位环境 $A_0$ 中的谱，定义

$$
\operatorname{NR}(P)\quad\Longleftrightarrow\quad
\sigma_{A_0}(P)\cap\bigl(-\sigma_{A_0}(P)\bigr)\subset\{0\}.
\tag{1.4}
$$

等价地，$t\mapsto t^2$ 在紧集 $\sigma_{A_0}(P)$ 上单射。这里允许零谱、零的聚点、正负连续谱和非中央 $P$，不要求谱隙。该条件只选择已知输入的 Jordan 几何，不是添加给全部原输入的公理。

## 2. 两份实际面积与既有两圆方程的准确复用

**引理 2.1（标量平方差的原两圆接口）。** 在 1.1 下，取真正原 $y,z\in V_h$，满足 $y^2-z^2\in\mathbb Ru$，并记

$$
\begin{gathered}
P=y\circ z,\quad Q=Jy\circ Jz,\quad
U=y\circ Jz,\quad V=Jy\circ z,\\
X_0=P-Q,\qquad Y_0=U+V.
\end{gathered}
\tag{2.1}
$$

则同一原响应给

$$
P^2=Q^2,\qquad X_0^2=Y_0^2,\qquad
X_0\circ Y_0=0,\qquad P\circ Y_0=0.
\tag{2.2}
$$

这是[三角卷 定理 212.1 及式 (212.2)](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 的两圆计算；下面只写明 [中央卷 18.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 在当前一般 JC 入口中逐次成立的理由，不将这些方程计为新的混合刚性。

证明。固定实数 $r=1/2$，令 $\ell=1+r^2$。原 PB $(rh,y,z)$ 的位移准确为 $rJy,rJz$，右端因自身正交为零。因此两份真正原外层共用一个旧值

$$
K=D(y+rJy,z+rJz)=D(y-rJy,z-rJz).
\tag{2.3}
$$

两份外层的两个输入平方分别为 $\ell y^2,\ell z^2$，其差是标量单位；[中央卷 18.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 因而分别适用。由 $y^2-z^2\in\mathbb Ru$，$y^2,z^2$ 交换；两份准确面积是同一环境乘积的等式

$$
K^2+(P+r^2Q+rY_0)^2
=\ell^2y^2z^2
=K^2+(P+r^2Q-rY_0)^2.
\tag{2.4}
$$

相减得到 $(P+r^2Q)\circ Y_0=0$。没有拆开任何未知的 $D$ 值。

对任意两份独立原圆标签 $y_\eta=\mathcal R_\eta y,z_\zeta=\mathcal R_\zeta z$，自身平方仍为 $y^2,z^2$，实际响应由 (1.3) 识别，故上面的每个前件继续合法。置

$$
A=P+Q,\quad B=U-V,\quad
\alpha=(1+r^2)/2,\quad\beta=(1-r^2)/2>0,
\quad\sigma=\eta+\zeta,\quad\delta=\zeta-\eta.
$$

[三角卷 式 (212.2)](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 的已知乘积展开给

$$
\bigl[\alpha(A\cos\delta+B\sin\delta)
+\beta(X_0\cos\sigma+Y_0\sin\sigma)\bigr]
\circ(Y_0\cos\sigma-X_0\sin\sigma)=0.
\tag{2.5}
$$

$\sigma,\delta$ 独立。比较 $\delta$ 与 $\delta+\pi$ 的和，取 $\sigma=0,\pi/4$，得到 $X_0\circ Y_0=0$、$X_0^2=Y_0^2$；比较其差，再取 $\delta=0$ 和 $\sigma=0,\pi/2$，得到 $A\circ Y_0=A\circ X_0=0$。其中 $A\circ X_0=P^2-Q^2$，且 $P=(A+X_0)/2$，所以有 (2.2)。内层参考演员始终是同一原 $rh$，两份外层准确保留 (2.3) 的原输入及旧 $D$；没有构造商响应或以数学代表替换演员。∎

## 3. 谱平方单射消去同一原对的混合残余

**定理 3.1（非共振交叠的混合桥）。** 在 1.1 的同一完整原候选下，对任意真正原 $y,z\in V_h$，若

$$
y^2-z^2\in\mathbb Ru,\qquad \operatorname{NR}(y\circ z),
\tag{3.1}
$$

则同一原 $J=D(h,\cdot)$ 满足

$$
\boxed{\quad Jy\circ Jz=y\circ z,\qquad
 y\circ Jz+Jy\circ z=0.\quad}
\tag{3.2}
$$

并有 $(Jy-Jz)^2=(y-z)^2$。更一般地，若存在实 $t>0$ 使 $y^2-t^2z^2\in\mathbb Ru$，且 $\operatorname{NR}(y\circ z)$，同样的两份混合等式和距离平方等式成立。不要求这些输入、平方或交叠中央、可逆或有限谱。

证明。先取 (3.1)。沿用 (2.1) 的原 $P,Q,X_0,Y_0$，2.1 给

$$
PY_0=-Y_0P,\qquad [P^2,Y_0]=0.
\tag{3.3}
$$

承重的扩域步骤只涉及已知环境算子。由 NR，平方映射从紧集 $\sigma(P)$ 到 $\sigma(P^2)$ 是连续双射，故有连续逆 $f$，满足

$$
f(t^2)=t\quad(t\in\sigma(P)),\qquad P=f(P^2).
\tag{3.4}
$$

后式是同一个固定自伴算子的连续函数演算。也可在紧实谱 $\sigma(P^2)$ 上一致用实多项式逼近 $f$；$Y_0$ 与每个这样的 $P^2$ 多项式交换，故与其范数极限 $P$ 交换。结合 (3.3) 得

$$
PY_0=Y_0P=0.
\tag{3.5}
$$

这里的范数极限仅用于环境乘法和固定算子交换关系；$f(P^2)$ 没有作为新标签送入 $D$，也不要求该函数演算在原 $E$ 内可执行。

于是由 $X_0^2=Y_0^2$，

$$
PX_0^2P=PY_0^2P=0,
\qquad PX_0^2P=(X_0P)^*(X_0P).
\tag{3.6}
$$

C* 正定性给 $X_0P=PX_0=0$。将 $Q=P-X_0$ 代入 $Q^2=P^2$，得到 $X_0^2=0$，所以 $X_0=0$；再由 $Y_0^2=X_0^2$ 得 $Y_0=0$。这是 (3.2)。平方保持给

$$
(Jy-Jz)^2=y^2+z^2-2Q=(y-z)^2.
\tag{3.7}
$$

这些都是原 $E$ 中元素的等式，由忠实包含认回原域。

在实缩放分支中，对真正原对 $(y,tz)$ 应用刚证结果。其交叠为 $tP$，NR 在非零实缩放下不变；已付 $J(tz)=tJz$，故两份所得混合等式只需除非零实数 $t$ 即回到 (3.2)。不除任何原元、强度或评价质量。∎

**命题 3.2（到一般原三角的准确止点）。** 对同一原 $b,c\in V_h$，置 $B=b+c$、$j=Jb,k=Jc,g=JB$。若 $(b,c)$ 满足 3.1 的某一分支，则

$$
j\circ k=b\circ c,\qquad
(g-j-k)^2=2B^2-2g\circ(j+k).
\tag{3.8}
$$

因而本桥支付三份实际交叉比较中的 $(j,k)$ 项；若另已支付 $g\circ j=B\circ b$ 和 $g\circ k=B\circ c$，才由此得到 $g=j+k$。

证明。第一式为 3.1。自身平方保持和第一式使 $(j+k)^2=B^2=g^2$，展开已识别的元素即得第二式。另两份关系若成立，右端为零，自伴平方零给所述加法。这是 [中央卷 12.3](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的既有三对缺陷计算的消费者，不假设 $J(B)$ 可展开。$(b,c)$ 的前件不会自动传给 $(B,b)$ 和 $(B,c)$；3.1 不宣称全部 $V_h$ 可加。∎

## 4. 不定号连续谱、原域不完备与删条件检查

**命题 4.1（谱分支严格超出半定及直接窄窗口）。** 存在满足全部数学 A1–A3、准确锥、P2、完整 PB 的稠密不完备原域，其中 3.1 适用于一对原输入；交叠不定号，具有连续谱及零谱，平方非中央且具有无限谱。该对的原二平面不属于任一仿射两平方坐标窗口，也不满足共同中心系数强度或中央 Gram 的直接前件。

证明。在 $\mathfrak A=C([0,1],M_4(\mathbb C))$ 中，所有下列二阶对角函数均按同一参数 $s\in[0,1]$ 定义：

$$
\begin{gathered}
R(s)=\operatorname{diag}(1+s,3+s),\qquad
T(s)=\operatorname{diag}(s/4,-2-s/4),\\
A(s)=(I_2+R(s))^{1/2},\qquad
Z(s)=A(s)^{-1}T(s)+i\bigl(R(s)-A(s)^{-2}T(s)^2\bigr)^{1/2},\\
h=\begin{pmatrix}I_2&0\\0&-I_2\end{pmatrix},\quad
y=\begin{pmatrix}0&A\\A&0\end{pmatrix},\quad
z=\begin{pmatrix}0&Z\\Z^*&0\end{pmatrix}.
\end{gathered}
\tag{4.1}
$$

第二根号中两个对角元分别至少为 $31/32$ 和 $111/64$：第一项用 $1+s\ge1$、$s^2/[16(2+s)]\le1/32$；第二项用 $3+s\ge3$、$(2+s/4)^2/(4+s)\le81/64$。所以所有函数在区间的一个开邻域中实解析。

取含单位复 *-代数 $\mathcal A$ 为全部常值矩阵、$sI_4$、$y,z$ 在 $\mathfrak A$ 中代数生成的 *-子代数，令

$$
E=\mathcal A_{\rm sa},\qquad X=\mathfrak A_{\rm sa},\qquad
D_0(F,G)=i(FG-GF)/2.
\tag{4.2}
$$

原锥、范数为限制的通常锥和上确界范数，原评价取全部正点向量评价及任意非负质量倍数。所有显示标签本来就在这个指定原域；$E$ 对 $\circ$ 和 $D_0$ 闭合，包含全部自伴矩阵多项式，故逐项 Weierstrass 逼近给稠密。每个原矩阵项实解析，而 $|s-1/2|I_4$ 不实解析，所以 $E$ 是稠密真子空间，因而不完备。

完整数学合同准确复用[原多项式零响应卷](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)式 (6.6)–(6.7) 的任意矩阵尺寸乘法计算。具体地，$F\circ G-iD_0(F,G)=FG$ 给全部原复二表；相加三表是同一向量的实 Gram，A3 由 $0\le e\le\theta u\le u\Rightarrow e^2\le e$。对全部原 $a,x,w$，若 $\zeta=x+iw$，PB 两份实际外层满足

$$
r_\pm+is_\pm=(u\pm ia)\zeta,\qquad
r_\pm^2+s_\pm^2+2D_0(r_\pm,s_\pm)=\zeta^*(u+a^2)\zeta.
\tag{4.3}
$$

所以 PB 对整个原域成立，而非只对显示矩阵成立；没有删去任何质量。此处只给数学合同实例，不声称这些数学评价是实际准备。

对角函数相互交换，直接相乘得

$$
\begin{gathered}
h\circ y=h\circ z=0,\qquad
 y^2=\operatorname{diag}(I_2+R,I_2+R),\quad
 z^2=\operatorname{diag}(R,R),\\
y^2-z^2=u,\qquad
P=y\circ z=\operatorname{diag}(T,T),\qquad
\sigma(P)=[0,1/4]\cup[-9/4,-2].
\end{gathered}
\tag{4.4}
$$

故 NR 成立而 $P$ 非半定，零还是谱聚点；两个平方都有无限谱且非 $Z(X)$ 中元。因而任何包含 $y,z$ 的原窗口都不满足 ([中央卷 60.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md))，本例不由 [中央卷 62.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的标量平方窗口前件覆盖。它也不落在 [中央卷 77.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的任何仿射标量平方片中：若 $y=au+w$、$a\in\mathbb R$、$w^2\in\mathbb Ru$，则 $w^2=y^2-2ay+a^2u$。其非对角块为 $-2aA$，而 $A$ 可逆，故标量平方迫使 $a=0$；此时 $w^2=y^2$ 非标量，矛盾。因此 [中央卷 68–75](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的生成三轴单位输入及 [中央卷 76–80](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的完整仿射窗都不能作为该对的直接前件。$u,\operatorname{diag}(R,R),P$ 实线性无关：若 $T=\alpha I_2+\beta R$，第一项的 $s$ 系数要求 $\beta=1/4$，第二项却要求 $\beta=-1/4$；$u,R$ 也线性无关。因此包含 $y,z$ 的实窗口不可能满足

$$
w^2=q_0(w)u+q_1(w)R'\quad\text{对全部 }w,
\tag{4.5}
$$

即使删去 $q_1$ 正定性亦然。这是[仿射平方固定文本](https://github.com/the-omega-institute/trureturing/blob/fb5e782ecc7b8f3bfc18856eacc6cb2f793db78a/docs/develop/theory/AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)中两平方坐标的数学条件，与[中央卷 53.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的中央平方首标签条件区分。

若 $y^2,z^2$ 是同一正环境元的中央系数倍数，在每个点 $s$，两者之差为 $I_4$ 会迫使该共同正元为标量矩阵，继而迫使 $z(s)^2$ 为标量；其两种不同特征值排除此情形。所以 [中央卷 48.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的直接前件不成立。中央 Gram 前件也由非中央平方排除；有限共同 Gram 代数的每个元素都有有限谱，不可能包含这里的 $y^2$。这些只区分直接前件，不否定借其他关系求出此标准模型中已知的全域线性。∎

**命题 4.2（条件删除的准确逻辑）。** 3.1 的谱条件允许删除半定限制，但不能从所消费的有限两圆方程中直接删除全部谱条件；这些检查不构成完整原候选下混合结论的独立性分类。

证明。$P=0$ 时 NR 成立，(3.3)–(3.6) 不需任何除法，直接消去 $X_0,Y_0$；$y=0$ 或 $z=0$ 同样包含。4.1 则给不定号、连续谱、零聚点和不完备原域的非退化实例。一般证明中唯一的连续函数演算作用于固定环境算子 $P^2$，故无需原根、逆、谱投影或旧响应延拓。

若删 NR，只保留有限两圆方程，在 $M_2(\mathbb C)$ 中取

$$
P=\sigma_z,\quad Q=-\sigma_z,\quad U=V=\sigma_x,
\quad X_0=2\sigma_z,\quad Y_0=2\sigma_x.
\tag{4.6}
$$

则 $A=B=0$，$X_0\circ Y_0=P\circ Y_0=0$，$X_0^2=Y_0^2=4u$，$P^2=Q^2$、$U^2=V^2$；代入 (2.5) 对全部角均为零，残余却非零。这里 $P$ 的谱为 $\{1,-1\}$，平方不能区分符号。此例只是所消费方程的反例，没有给出整个 $E^2$ 上满足全部 P2/PB 的总 $D$。

反过来，在标准有效模型中取 $h=\sigma_z\otimes I_2$、$y=\sigma_x\otimes I_2$、$z=\sigma_x\otimes\sigma_z$，有 $y^2=z^2=u$，$y\circ z=I_2\otimes\sigma_z$，NR 不成立而标准 $J$ 仍满足 (3.2)。所以 NR 不是完整候选的普遍后果，也不是混合结论的必要条件，不能把它升格为普适公理。

若删去标量平方差及其明确实缩放版本，(2.4) 两份实际外层的 [中央卷 18.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 前件不再由本证明供应；没有因此得到全域结论的反例。若只保留原两圆的平方和正交，也没有自动得到 (2.3) 的跨圆共同输出；该式在这里由完整原 PB 支付。∎

## 5. 任意横向原对的同步圆与共同输出预算

**引理 5.1（同一旧响应的同步圆不变性）。** 在 1.1 的完整候选中，对全部真正原 $b,c\in V_h$ 及全部实 $\theta,\psi$，不加任何平方窗口条件，有

$$
\begin{gathered}
D(\mathcal R_\theta b,\mathcal R_\theta c)=D(b,c),\\
D(Jb,Jc)=D(b,c),\qquad D(Jb,c)=-D(b,Jc),\\
D(\mathcal R_\theta b,\mathcal R_\psi c)
=D(b,\mathcal R_{\psi-\theta}c).
\end{gathered}
\tag{5.1}
$$

这是完整 PB 与已付自身圆接口的直接辅助消费者，不作为独立的全域线性原理。

证明。对任意实 $t$ 和真正原 $x,w\in V_h$，原 PB $(th,x,w)$ 的位移是 $tJx,tJw$，右端为零，故

$$
D(x+tJx,w+tJw)=D(x-tJx,w-tJw).
\tag{5.2}
$$

取真正原标签

$$
x=\frac{b+tJb}{1+t^2},\qquad
w=\frac{c+tJc}{1+t^2}.
\tag{5.3}
$$

(1.3) 只在两个各自平面内计算，给 $x-tJx=b,w-tJw=c$，以及

$$
x+tJx=\frac{1-t^2}{1+t^2}b+\frac{2t}{1+t^2}Jb,
\qquad
w+tJw=\frac{1-t^2}{1+t^2}c+\frac{2t}{1+t^2}Jc.
\tag{5.4}
$$

半角代换覆盖所有非反点圆角；反点由已付的各槽奇性给 $D(-b,-c)=D(b,c)$。因此得到第一式，未对未知 $D$ 缩放或相加。取四分之一圆得第二行；其中交叉斜式也可将第一式用于 $(b,Jc)$ 并用 $J^2=-I$、奇性取得。再对输入对 $(\mathcal R_\theta b,\mathcal R_\psi c)$ 同步施加角 $-\theta$，用自身圆作用律即得最后一式。全部标签仍在原 $E$。∎

**推论 5.2（一个实际输出的联合 P2 预算）。** 对固定同一原 $b,c$，记

$$
d=D(b,c),\quad P=b\circ c,\quad Q=Jb\circ Jc,\quad
Y=b\circ Jc+Jb\circ c.
$$

对每个数学正实泛函 $\phi:X\to\mathbb R$，包括原评价的连续延拓，不要求归一化，令

$$
a=\phi(b^2),\quad e=\phi(c^2),\quad
p=\phi(P),\quad q=\phi(Q),\quad s=\phi(Y),\quad
\delta=\phi(d).
$$

则 $ae-\delta^2\ge0$，且

$$
\boxed{\quad |p+q|+\sqrt{(p-q)^2+s^2}
\ \le\ 2\sqrt{ae-\delta^2}.\quad}
\tag{5.5}
$$

证明。5.1 使每个同步圆角使用同一实际 $d$，自身平方使对角读数始终为同一 $a,e$。唯一变动的交叠读数是已知实三角多项式

$$
\phi(\mathcal R_\theta b\circ\mathcal R_\theta c)
=\frac{p+q}{2}+\frac{p-q}{2}\cos2\theta+\frac{s}{2}\sin2\theta.
\tag{5.6}
$$

逐角原 P2 给其绝对值不超过 $\sqrt{ae-\delta^2}$。实式 $A+B\cos t+C\sin t$ 的绝对值最大值为 $|A|+\sqrt{B^2+C^2}$，代入即得 (5.5)。这一步只优化已知的同一交叠，不把分别可达的旧输出拼成一个输出。零泛函、$a=0$ 或 $e=0$ 时原 P2 先给相应零预算，仍无需除法。

这份预算不消除所有正余量；特别 (5.1) 中的 $D(Jb,c)+D(b,Jc)=0$ 是旧响应关系，不等于 Jordan 乘积关系 $Y=0$。因而本推论只辅助一般混合问题，不由它宣布 $P=Q$、$Y=0$ 或 $J$ 可加。∎

## 6. 非零同态与实换基不能普遍压入直接平方窗口

**命题 6.1（满三平方坐标的严格路线边界）。** 存在同一完整数学 P2/PB 原域和真正原 $h,b,c$，其中 $h^2=u$、$b,c\in V_h$，使以下结论同时成立。令 $W=\operatorname{span}_{\mathbb R}\{b,c\}$，对到任意实 JB 代数 $Y$ 的非零连续 Jordan 同态 $q:X\to Y$，以像的相对单位 $p=q(u)$ 计，有

$$
\dim\operatorname{span}_{\mathbb R}\{p,q(b^2),q(c^2),q(b\circ c)\}=4.
\tag{6.1}
$$

所以平方坐标空间 $\Gamma_q(W)=\operatorname{span}_{\mathbb R}\{q(w^2):w\in W\}$ 在模 $\mathbb Rp$ 后的秩为 $3$，达到二维实输入的二次极化所容许的最大值。此外，以 $L_xv=x\circ v$ 记 Jordan 乘法算子，

$$
[L_{q(b^2)},L_{q(b\circ c)}]\bigl(q(b^2)\bigr)\ne0.
\tag{6.2}
$$

对 $W$ 的全部 $\mathrm{GL}_2(\mathbb R)$ 换基，上述四维张成与三项 Gram 不全算子通勤的性质保持。因此任何非零同态像都不能将同一原二平面直接放进标量平方窗口 ([中央卷 60.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md))、[中央卷 77.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的仿射标量平方片、仿射两平方坐标、共同中央系数强度、共同交换有限 Gram 或全中央 Gram 窗口；用这些直接窗口像组成联合分离族也不能做到。

证明。取[原多项式零响应卷式 (6.6)–(6.7)](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md) 的四阶矩阵版本：

$$
E=M_4(\mathbb C)_{\rm sa}[t],\quad
X=C([0,1],M_4(\mathbb C))_{\rm sa},\quad
D_0(F,G)=i(FG-GF)/2.
\tag{6.3}
$$

原锥、范数、全部正点向量评价及其非负质量倍数照取，数学前件与整个原域上的 PB 由 (4.3) 的同一恒等式供应。$E$ 稠密不完备；它也无非零最小原 Jordan 投影，因为对任何非零原投影 $e$，$e,te$ 都在 $U_e(E)$ 且实线性无关。这里没有删除原投影，只有“原最小投影”的供应不成立。

以下均为该同一 $E$ 中的常值原标签：

$$
\begin{gathered}
h=\operatorname{diag}(I_2,-I_2),\qquad
B=\operatorname{diag}(1,2),\quad
T=\begin{pmatrix}0&1\\2&0\end{pmatrix},\\
b=\begin{pmatrix}0&B\\B&0\end{pmatrix},\qquad
c=\begin{pmatrix}0&T\\T^*&0\end{pmatrix}.
\end{gathered}
\tag{6.4}
$$

直接块乘法给 $h\circ b=h\circ c=0$，且令 $A=b^2,F=c^2,P=b\circ c$，有

$$
A=\operatorname{diag}(1,4,1,4),\quad
F=\operatorname{diag}(1,4,4,1),\quad
P=\operatorname{diag}(2\sigma_x,(5/2)\sigma_x).
\tag{6.5}
$$

若 $\alpha u+\beta A+\gamma F+\delta P=0$，非对角元先给 $\delta=0$，比较第一个与第三个对角元给 $\gamma=0$，比较第一个与第四个给 $\beta=0$，最后 $\alpha=0$。所以这四个常值元素实线性无关。

任何这样的非零 $q$ 都忠实保留常值 $H_4(\mathbb C)$。事实上 $q(u)=0$ 会使 $q(x)=q(u\circ x)=0$ 对全部 $x$ 成立；故 $q(u)\ne0$，而常值限制的核是 Jordan 理想。其简单性在此可直接证明：非零理想中取非零自伴 $a$，选非零特征值 $\lambda$ 及单位特征向量 $v$。秩一 $e_v$ 给 $U_{e_v}(a)=\lambda e_v$，所以理想包含 $e_v$。补全正交基，连接 $v$ 与其余基向量的自伴矩阵单位 $f_{1j}$ 满足 $e_v\circ f_{1j}=f_{1j}/2$，因而也在理想中；$f_{1j}^2=e_v+e_j$ 再给全部 $e_j$。求和得单位，理想遂为全体。因此核只能为零，(6.1) 得证。

交换子见证同样是常值 Jordan 多项式。van de Wetering，[*Commutativity in Jordan operator algebras*](https://arxiv.org/html/1912.01903v1)，Proposition 3.2 证明中的式 (2)，给 JC 中的准确恒等式

$$
[L_A,L_P]A=\frac14[[A,P],A]
=\operatorname{diag}(-(9/2)\sigma_x,-(45/8)\sigma_x)\ne0.
\tag{6.6}
$$

Jordan 同态保持左边这个内在多项式，且常值限制单射，故 (6.2) 成立，不依赖目标的通常或相反环境乘法取向。

若以可逆实矩阵把 $(b,c)$ 换成 $(b',c')$，二次单项式的对称平方变换仍可逆；明确地，若 $b'=\alpha b+\beta c,c'=\gamma b+\delta c$，则

$$
\begin{pmatrix}b'^2\\c'^2\\b'\circ c'\end{pmatrix}
=
\begin{pmatrix}
\alpha^2&\beta^2&2\alpha\beta\\
\gamma^2&\delta^2&2\gamma\delta\\
\alpha\gamma&\beta\delta&\alpha\delta+\beta\gamma
\end{pmatrix}
\begin{pmatrix}A\\F\\P\end{pmatrix}.
\tag{6.7}
$$

逆输入换基给逆二次变换。因此 $\Gamma_q(W)$ 与 (6.1) 的四维张成保持，且换基后的三项 Gram 的线性张成不可能成为交换空间：否则其中的 $qA,qP$ 会算子通勤，与 (6.2) 矛盾。

标量平方窗口 ([中央卷 60.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)) 会使全部 $q(w^2)$ 落在 $\mathbb Rp$，模单位秩为零，已与 (6.1) 矛盾；仿射两平方坐标会使所有 Gram 落在 $\operatorname{span}\{p,R'\}$，与 (6.1) 矛盾；即使放宽成两个非单位平方坐标，连同 $p$ 也至多三维，仍不足。共同环境中央系数乘同一强度的三项 Gram 在任何忠实 JC 环境中普通交换，继而其 Jordan 乘法算子交换，与 (6.2) 矛盾。共同交换有限系数或目标 Jordan 中心的窗口也有同一矛盾。这里 $q$ 只作用于已知 Jordan 多项式，没有借它定义未知响应。

对于 [中央卷 77.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的更宽仿射片，若 $q(b)=sp+x,q(c)=tp+y$ 且 $x,y\in W_0$、$v^2\in\mathbb Rp$ 对全部 $v\in W_0$ 成立，则 $x\circ y\in\mathbb Rp$。展开这两个已知 Jordan 平方与交叠可知 $q(b^2),q(c^2),q(b\circ c)$ 全在 $\operatorname{span}_{\mathbb R}\{p,q(b),q(c)\}$，连同 $p$ 的张成至多三维，仍与 (6.1) 的四维矛盾。这也排除 [中央卷 77.1、78.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的生成四维窗作为任何非零像的直接覆盖入口；没有把内在复乘法的取向误当成指定 JC 环境的共同取向。

$(b,c)$、$(b+c,b)$、$(b+c,c)$ 都是同一 $W$ 的基，故这些直接窗口障碍保留同一原三标签，而非另换一个较小输入问题。所有能直接满足上述窗口的像只能是零像，不能组成分离原非零元的族。∎

**定义 6.2（路线反例的范围）。** 6.1 排除的是用非零 Jordan 同态与可逆实换基将同一实际二平面直接覆盖到所列窄窗口的普遍策略。奇异换基、丢弃一个原标签或零像确可降低秩，但不能回收同一原 $b,c,b+c$；一般正压缩不必是 Jordan 同态，若使用它，旧响应的纤维及混合运输仍须另证。本例的 $D_0$ 已实双线性，$Jv=ihv$，所以不是 P2/PB 下不可加的反模型，也不否定 3.1。它不排除加入新原标签的更长 PB 网络、不同观察或新的共同预算；并且没有实现全部 $\Omega/\mathrm{native}$ 物理合同，不能据此反驳完整量子来源目标。

## 7. 两元、三标签与谱反射的几何

**定义 7.1（关系的关系与有限提升）。** 3.1 受影响的两元是同一原 $y,z$；$P=y\circ z$ 与 $Q=Jy\circ Jz$ 比较两者在响应前后的交叠，$Y_0=y\circ Jz+Jy\circ z$ 比较两份交叉关系。实际三标签 $(rh,y_\eta,z_\zeta)$ 的 PB 将两个不同自身圆放到同一外层输出预算中；第三标签是原 $rh$，没有把数学谱值、商或支撑变成原演员。原 $h,y,Jy$ 各自产生的有限三方向图像不规定原世界总维数、物理三空间或实际三系统联合。[中央卷 63.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的闭合三轴以真正原正交单位对为入口；这里平方可非中央的任意 $y$ 不由三个原标签便满足该前件。[中央卷 64.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 还允许四维而不输出闭合的标量平方窗口，故自身三轴闭合不限制任意窗口至多三维。

反交换 $PY_0=-Y_0P$ 的谱含义是：在忠实表示中，若 $P\xi=\lambda\xi$，则 $P(Y_0\xi)=-\lambda Y_0\xi$。连续谱时不依赖特征向量，准确内容仍为 (3.3)–(3.4) 的函数演算。NR 表示非零等模异号通道不存在；平方还记得原符号，故残余同时必须保持和翻转同一交叠，只能落在零核，再被其余平方方程消尽。式 (4.6) 的两根 Pauli 轴展示等模反射通道可容纳有限方程的非零残余。

5.1 另外说明任意两只原圆同步转动时，同一旧响应不变；这还不是它们的 Jordan 交叠不变。6.1 的两个原方向则在模单位后有三份独立二次坐标：$[b^2],[c^2],[b\circ c]$。这是二次极化的满三坐标几何，换基与非零同态不能把它压成一个共同强度或一份非单位平方坐标；它同样不指定物理维数。

**定义 7.2（数学归属与准确复用）。** 3.1 的承重连接是下列结果的综合：在一般原 JC 入口中复用 [中央卷 18.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的准确面积、[中央卷 19–20](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 与 [中央卷 35.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的实际自身圆及强度，再将[三角卷 式 (212.2)](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 的有限角度方程接到“平方在已知交叠谱上单射”的消去条件。[三角卷 213.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 的半定消去是其特例；2.1 的角度代数不计新内容。[仿射平方固定文本式 (53.6)–(53.10)](https://github.com/the-omega-institute/trureturing/blob/fb5e782ecc7b8f3bfc18856eacc6cb2f793db78a/docs/develop/theory/AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已有同一标量平方差适配与半定消去，这里也不将该适配计作新内容。[中央卷 53–59](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 则是中央平方实际首标签的带权模块入口，不与该固定文本的编号混用。

若 $\operatorname{span}_{\mathbb R}\{h,y,z\}$ 本来满足 ([中央卷 60.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md))，则 (3.2) 已由 [中央卷 62.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 及其所复用的 ([中央卷 29.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)) 给出，无须再加 NR；[中央卷 62.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 更已支付整个该窗口上的旧双线性。3.1 另处理任意原 $y,z\in V_h$ 只有标量平方差及 NR 的分支，4.1 的非中央平方和不定号交叠明确不落在上述标量平方窗口内。6.1 则是对所有非零 Jordan 像及可逆实换基的覆盖路线边界，不是旧 $D$ 不可加的反模型。这三种输入关系与结论范围分别保持，不将 [中央卷 60–67](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的成果计作本谱分支的新内容。在更大的已付范围中，[中央卷 68–75](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的有限 SO(3) 运输、角压缩、同时反交换及面积占优零区也不属于本谱分支的新内容；[中央卷 76.2、77.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已消去其中全部生成三轴仿射余量，包含原来 $P>W$ 的区域，故这一区域不再列为缺口。[中央卷 77.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 又支付任意标量平方片的全部仿射双线性。4.1 的解析例子由其非对角块论证排除这些直接前件，6.1 则以四维平方坐标排除所有非零像上的同类入口。非中央平方、连续不定号且满足 NR 的条件混合连接与全像／全可逆换基的直接路线边界分别保留；它们不保证其他未来结论的新增性。

紧到 Hausdorff 的连续单射有连续逆、连续函数演算、多项式一致逼近、C* 中 $T^*T=0\Rightarrow T=0$、自伴平方零、二次极化和简单矩阵 Jordan 代数的理想计算均是成熟中间工具，不单立为新定理。式 (6.6) 所引论文式 (2) 只供应内在交换子恒等式，不供应旧 $D$ 的线性；该命题的新路线边界是对所有非零像及所有可逆实换基保留同一满秩平方坐标和非通勤见证。5.1–5.2 是同一原 PB 的辅助消费者，不把一次半角代换宣称成独立的量子公理削减。这里不主张文献穷尽或历史优先权。

## 8. 剩余原关系与七项量子消费者

**定义 8.1（完整目标的未付部分）。** 独立原 A1–A3、准确锥、全部 P2 与完整 PB 不变。3.1 在标量平方差的实际输入分支中，用 NR 代替半定，支付两份原混合等式；NR 是选择分支的前件，不对全部原对作新规定。其中满足 ([中央卷 60.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)) 的原窗口上，同一旧 $D$ 的双线性及同一首方向混合已由 [中央卷 62.1–62.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 支付，不列为未付义务；还须复用 [中央卷 76.2、77.1–77.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)：每个生成三轴的全部带单位输入及任意标量平方片 $W_0$ 的整个 $(\mathbb Ru+W_0)^2$ 已识别；其中一般单位平移、旧双线性和生成四维窗内的输出闭合均不是未付项。[中央卷 78.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的局部原 R、有限复 Gram、同一结合复乘法及正质量实际菜单下 Born 也已支付。下述一般缺口仅指这些已付条件窗口及本卷 NR 分支之外的原输入，尤其一般非标量平方输入的全原域拼接。一般任意原 $b,c,b+c\in V_h$ 的共同混合关系、全部 $V_h$ 可加、跨 $h$ 一般共同取向、任意第一输入的可加及同一原 $D$ 全域实双线性仍未由此支付。也未由此取得已付窗口之外的一般中央平移、全域 NN／Jacobi、$\mathsf F$、全域原 R、全域输出闭合、一般商下降、完成延拓或同一全域结合乘法。

只有另已支付同一旧 $D$ 在全部原 $E$ 上分别可加时，[静态卷 32.2](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md) 才由原 P2 的范数界得到实双线性和全部有限复 Gram；完整 PB 再经[静态卷 23.1、33.2](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md) 恢复原 R 及同一乘法 $a\star b=a\circ b-iD(a,b)$ 的结合性。这条直接路线允许原域不完备；经 $\mathsf F$ 的路线仍保留满 $E=A_{\rm sa}$ 的准确前件。局部混合桥、同步圆和标准模型不代付这个全域入口。

**定义 8.2（七项消费者的原条件）。** 完整保留 [中央卷 52.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 及[三角卷 250.1、221.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 的同一原合同；下表给本混合桥与每个消费者的准确连接。其中“全域桥另付”始终指整个原 $E$；[中央卷 78.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已识别生成四维窗 $B$ 的同一旧乘法、原 R、有限复 Gram 与局部 Born，凡所需标签和实际菜单确在同一 $B$ 中就直接消费该结果，不重列为缺口。该内在乘法不保证所选环境 JC 包含保其复取向，也不供应表内的实际联合或仪器来源。

| 原消费者 | 仍须满足的同一来源条件 |
| --- | --- |
| 1. 复 Hilbert、可观测量、叠加 | JC 包含保持旧 $S,C,u,N$；同一旧 $D$ 全域代数桥另付后才接全部复 Gram、原 R 和同一结合星乘法。原可取得标签、跨评价配对、共同核 $K$、同一 $J_a$、全部有限及零长度全词、native、父位置／ready、合法控制和实际相干叠加准备均不能由数学表示或谱演算供应，也不默认全 $B(H)$ 或任意向量准备。 |
| 2. 态、效果、质量、Born | 全部原评价、准确效果、零／不等／次归一质量和中心权保留。只对原实际完整菜单 $\sum_l e_l=u$ 且 $m_\alpha>0$ 用 $\alpha(e_l)/m_\alpha$，零质量不除。共同根、准备、接受、抽签、mark、接线、全部 P9 分支、独立 $W_e$、AS／EC、菜单外 OB、实际二维到三维适配器、固定支持和全部切口均保持原量词。数学态不是实际准备，输入平方强度也不是质量。 |
| 3. native、真正相关联合、张量 | 仍需同一非零实际共同来源、全部中心对、经典／不等维块、忠实同向交换的局部全矩阵两腿、交叉零、生成分离、共同联合生成与重数、全部乘积和真正相关输入；分别可得的数学像和边缘不能合成共同实现，所用实际局部腿的旧乘法仍须识别；落在 [中央卷 78.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已付窗内者复用该识别，环境共同取向及联合前件仍须原合同。 |
| 4. CP、整台递归同源参考 | 原 typed 前接、真实未归一回溯、合法后口、全未来自然性、反变复合、typed 分区及箭头商下降保留。还需整台仪器连环境及全部成功／失败／记录／后口的同规则实际 $r^+$、系统腿与 $M_2$ 腿共同真支持、三颗实际投影及 $I_2$ 实张成、支持内补事件、全部相关正输入的 intertwining 与夹界、每个所需有限递归深度及累计支持的准确运输。响应行、谱函数和 Jordan 像不是该合同。 |
| 5. 完整仪器、更新、TP、Lüders | 同一旧星乘法另已识别后才有其原正夹心；完整 typed 单位分区才给 TP，全部输出的像内射线校准才接 Lüders。全输入运输、成功／失败、记录／后口、停止／拒绝／销毁、接受、真正遗忘、AC、精确 $N_u$、X／Xs、原平方根词和接受端均保留。Kraus、密度、迹类及收敛只在有限全矩阵域，或另给正常物理表示、指定前对偶与适用分解／收敛接口后使用。 |
| 6. 全历史、未来、遗忘、真实返回 | 全部合法顺序／自适应／并行历史、环境泄漏、细记录及每个输出仍合法的每个未来、停止／拒绝／销毁、共同记录真正分组遗忘均保身份，未定义请求仍未定义。$B,B_{\rm cl}$、同数两侧真实逆向返回、CountRead 完整输出至全部活动 ready 接头、两条负提升活路和相干聚合、全菜单及接受端、九叶彩票、空程序、拒绝叶与相干返回保持[三角卷 250.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 的原合同。非离散／无穷记录、可数可加、无限历史、正常性和指定前对偶仍须原桥；$J^2=-I$ 及数学圆逆不是实际返回。 |
| 7. 物理动力与共同尺度 | 全域旧乘法另已识别后才消费数学导子与完成指数流，不完备原 $E$ 的流保持另证。原相位、实际门序列、可逆一参数群、物理钟、所需强连续酉实现、生成元域、Hamiltonian 能量、作用量与共同 $\hbar>0$ 齐备后才用 $\dot b=2D(H,b)/\hbar$。原 $\sigma,t_0,d$、固定域、resolvent 与 $3s+r\le1$ 不扩张；数学角、谱参数和函数演算不供应时间、能量或作用量。 |

**定义 8.3（全部原实际量词）。** 原 $\Omega/\mathrm{native}$、全词 $K/J/q/u/N/\mathcal P/S/D$、父位置与 ready、原中心／经典／不等维块／静默域、全部质量、全部实际准备与完整菜单、共同记录真正遗忘、全仪器及环境和全部输出、同一个实际相关联合与递归同源参考、全部合法顺序／自适应／并行历史和每个合法未来、停止／拒绝／销毁、同数两侧真实双向返回，一律取[三角卷 128.1、206.1、250.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md) 及[中央卷 52.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 的同一原资料。6.1 的 $q$ 只是数学 Jordan 同态，与原全词读数 $q$ 区分；4.1、6.1 的数学模型没有制造这些实际来源。局部结论不声明完整量子起源成立，也不缩小原目标的完成量词。


**约定 8.4（不同原来源的几何）。** [《原来源能量与正测度纤维几何》18–19](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_ENERGY_FIBRE_GEOMETRY.md) 的固定有限合法包库、全部有限深度 $\Gamma_d$ 树、完成观察因子损失和热半群边界，依赖同一 $G=H^1\times\mathbb R$、$m=h^2\mu$、完整端点 $A=\rho C$、原形式域及源迹；[《原有限记录的局部能量配对取得》17–18](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md) 的有限证书、逐来源的最终有限取得及词配对另守其校准、精度、资源与共同事件前件。它们不提供本卷的原 $D$、两圆 PB 或全域复取向，本卷也不从这些特定能量纤维推出一般 $V_h$ 的结论。尚未给出把这些解析来源的实际标签、正评价、操作、联合和取得成本同本卷完整 $\Omega/\mathrm{native}$ 合同对应的映射，故不能据同名 $h,K,D$、有限提升或谱术语相互代付；它们保留的实际返回与所有中间到达标签的取得边界也不由本卷数学模型消去。

## 9. 谱反射混合桥的完整白话

**定义 9.1（完整白话）。** 还是同一个原世界、同一张二元响应表、同一正表和完整正反配平，每个原方向与自己的响应已经能画一只可靠的圆。平方全落在单位实线的方向片上，[中央卷 62–63](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 已把同一旧响应接成双线性面积表并从两根正交单位轴生出闭合三轴，不必先要求输出留在方向片内；而 [中央卷 76–80](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md) 更已把生成三轴的全部带单位输入、任意标量平方片的仿射双线性和生成四维窗的内在复乘法接通，这些都不再是未付余量；这里另接平方可非中央、交叠可不定号的输入分支，不把已有的方向片当作全部原世界。现在要接通两只圆，第三个真正原标签把它们放进同一次配平，先迫使可能的不相容残余只能把交叠的一份正读数搬到大小相同的负读数。只要这两个输入的平方在合法实缩放后只差一个单位倍数，而且非零正负读数的大小不重合，平方就仍能分清原来的符号，残余便同时被要求保持和翻转同一个交叠，最后只能消失；正负谱可以同时存在，也可以连续变化并碰到零，原世界不必补根、逆或谱投影。这样锁住的是这两个实际原输入的两份混合关系。对任意两只横向圆，还能直接确定同步旋转保持同一旧响应，但这并不等于它们的交叠不变，更不等于查相加输入等于把两个响应相加。确有满足全部数学正表和配平的原域，其两个输入与它们的和需要三份不能由非零同态或可逆换基压掉的非单位平方坐标，所以不能承诺总把任意原三角直接送进已经解决的窄窗口；这个例子自己的响应已经可加，限制的是这条覆盖路线。这些已付条件窗口之外任意方向的共同混合、跨参考的共同复取向、全域同一结合乘法，以及实际准备、一般实际 Born 菜单、整台仪器、相关联合、递归参考、全部历史每个未来、真正遗忘、真实返回、计数与正常性、物理钟、能量和共同作用量，仍各守原来的未付条件，完整原目标保持不变。

## 追加锚（本行以下为增补区）

## 10. 同一原对的缺陷代数与中心锥

**约定 10.0（追加部分的引用范围）。** 本追加部分的无卷名编号均指本卷；中央卷在这里包括 94–99，条件窗口的准确范围取 14.3。本卷 1–9 的固定版本引用仍按其各自限定读取。

**定义 10.1（原三标签、缺陷四元组与诊断代数）。** 保持 1.1 的同一原资料、同一原 $h^2=u$、全部原 P2 与完整 PB。固定真正原 $y,z\in V_h$，满足

$$
y^2-z^2\in\mathbb Ru.
\tag{10.1}
$$

仍令

$$
P=y\circ z,\qquad Q=Jy\circ Jz,\qquad
U=y\circ Jz,\qquad V=Jy\circ z.
\tag{10.2}
$$

为避免与 0.2 的 JB 完成 $X$ 混淆，定义

$$
\mathsf A=P+Q,\qquad
\mathsf X=P-Q,\qquad
\mathsf Y=U+V,\qquad
\mathsf R=P^2,\qquad
\mathsf T=\mathsf X^2.
\tag{10.3}
$$

这些全是原 Jordan 元。在给定忠实含单位 JC 环境 $A_0=C^*(X)$ 中记

$$
\mathfrak B_{y,z}=C^*(u,\mathsf A,\mathsf X,\mathsf Y)\subset A_0.
\tag{10.4}
$$

这是由同一原对及其实际响应生成的诊断 C* 代数。其谱、表示、商和双对偶只用于读取固定元素，不作为新输入送回原 $D$。原域可不完备；只要求 1.1 的弱 JC 包含，不要求 $X=(A_0)_{\rm sa}$。若原对象为零，则此代数、下述元素与理想全为零，不可约表示集合为空；以下需要态或非零单位的步骤只在非零对象中使用。

**定理 10.2（同一原 PB 响应的中心锥关系）。** 在 10.1 下，原两圆接口 2.1 给出的四个等式进一步推出

$$
\begin{gathered}
\mathsf A\circ\mathsf X=\mathsf A\circ\mathsf Y
=\mathsf X\circ\mathsf Y=0,
\qquad
\mathsf X^2=\mathsf Y^2=\mathsf T,
\\
\mathsf R=\frac{\mathsf A^2+\mathsf X^2}{4},
\qquad
\mathsf A^2=4\mathsf R-\mathsf T,
\\
0\le \mathsf T\le4\mathsf R,
\qquad
\mathsf R,\mathsf T\in Z(\mathfrak B_{y,z}).
\end{gathered}
\tag{10.5}
$$

这三份 Jordan 正交等价于 $\mathsf A,\mathsf X,\mathsf Y$ 在环境结合乘法中两两反交换。这里的中心性只是在诊断代数 $\mathfrak B_{y,z}$ 内成立；不宣称 $\mathsf R$、$\mathsf T$ 或任一取向元在 $A_0$ 或整个原世界中中央。

证明。2.1 给 $P^2=Q^2$、$\mathsf X^2=\mathsf Y^2$、$P\circ\mathsf Y=0$ 与 $\mathsf X\circ\mathsf Y=0$。由

$$
\mathsf A\circ\mathsf X=P^2-Q^2=0
\tag{10.6}
$$

得第一份反交换。又 $\mathsf X\circ\mathsf Y=0$ 与 $P\circ\mathsf Y=0$ 给 $Q\circ\mathsf Y=0$，所以 $\mathsf A\circ\mathsf Y=0$。对自伴元，Jordan 正交正是环境乘法的反交换，故三者两两反交换。

在环境中展开平方，交叉项相消，得

$$
\mathsf A^2+\mathsf X^2=2(P^2+Q^2)=4P^2=4\mathsf R.
\tag{10.7}
$$

自伴平方正性给 $\mathsf R\ge0$、$\mathsf T\ge0$，而 $4\mathsf R-\mathsf T=\mathsf A^2\ge0$。若自伴元 $a$ 与自伴元 $b$ 反交换，则 $a^2b=ba^2$；逐一对三生成元使用此事实，$\mathsf A^2$、$\mathsf X^2$、$\mathsf Y^2$ 与 $\mathfrak B_{y,z}$ 的每个生成元交换。由 (10.7) 得 $\mathsf R,\mathsf T$ 在 $\mathfrak B_{y,z}$ 内中央。全程只用了 2.1 的有限原关系和环境中的固定乘法，没有使用未知 $D$ 的连续性、可加性、闭合性或原域中的谱投影。∎

## 11. 连续中心谱上的不可约 Clifford 纤维

**定义 11.1（中心纤维与边界分层）。** 令 $\widehat{\mathfrak B}_{y,z}$ 为 $\mathfrak B_{y,z}$ 的非零不可约 *-表示类。由 10.2 和 Schur 引理，任一 $\pi\in\widehat{\mathfrak B}_{y,z}$ 有唯一 $r,t\in\mathbb R$ 使

$$
\pi(\mathsf R)=rI,\qquad \pi(\mathsf T)=tI.
\tag{11.1}
$$

记 $s=4r-t$。$\Sigma_{y,z}$ 是中央子代数 $Z_0=C^*(u,\mathsf R,\mathsf T)$ 的字符空间，以字符在 $(\mathsf R,\mathsf T)$ 上的值作坐标；非零对象时它是紧集，可含连续部分。由 10.2，

$$
\Sigma_{y,z}\subset\{(r,t):r\ge0,\ 0\le t\le4r\}.
\tag{11.2}
$$

对 $(r,t)\in\Sigma_{y,z}$，令 $\mathfrak B_{r,t}$ 为按该中心字符取的商，即模去由 $\mathsf R-ru,\mathsf T-tu$ 生成的闭理想。每个这样的商非零：中心字符有态延伸，而其延伸态的 GNS 循环向量被这两份中央关系消灭，故整个循环表示均被它们消灭。反向，每个不可约表示限制到 $Z_0$ 都是字符；每个非零纤维商也有不可约表示。因此 $\Sigma_{y,z}$ 正是 (11.1) 的全部可能坐标。商只读取诊断代数，不定义原 $D$ 的商响应。

**定理 11.2（全部不可约纤维的精确分类）。** 在 11.1 下，对每个不可约表示 $\pi$ 有如下穷尽分类。

1. 若 $r=0$，则 $t=0$，且 $\pi(\mathsf A)=\pi(\mathsf X)=\pi(\mathsf Y)=0$；该纤维只有一维标量不可约表示。
2. 若 $t=0$，则 $\pi(\mathsf X)=\pi(\mathsf Y)=0$，且纤维的不可约表示均为一维；当 $r>0$ 时 $\pi(\mathsf A)=2\sqrt r$ 或 $-2\sqrt r$，实际纤维可保留其中一个或两个符号。
3. 若 $t>0$，则纤维不可约表示恰为二维。令

   $$
   e_1=\frac{\pi(\mathsf X)}{\sqrt t},\qquad
   e_2=\frac{\pi(\mathsf Y)}{\sqrt t}.
   \tag{11.3}
   $$
   它们是反交换的自伴酉元。若 $0<t<4r$，再令 $e_3=\pi(\mathsf A)/\sqrt s$；则

   $$
   e_1^2=e_2^2=e_3^2=I,
   \qquad e_i e_j=-e_j e_i\ (i\ne j),
   \tag{11.4}
   $$
   且取向只能有两种；实际纤维可保留其中一种或二者

   $$
   \varepsilon(\pi)=-\mathrm i e_1e_2e_3\in\{+I,-I\}.
   \tag{11.5}
   $$
   适当选取二维基后，准确写成

   $$
   \pi(\mathsf X)=\sqrt t\,\sigma_z,
   \qquad
   \pi(\mathsf Y)=\sqrt t\,\sigma_x,
   \qquad
   \pi(\mathsf A)=\varepsilon\sqrt{4r-t}\,\sigma_y.
   \tag{11.6}
   $$
   若 $t=4r>0$，则 $\pi(\mathsf A)=0$，而 $(\pi(\mathsf X),\pi(\mathsf Y))$ 仍是一份二维 Pauli 对；此边界没有第三轴取向。 因而任何一维标量不可约纤维必有 $t=0$。

证明。若 $r=0$，(11.2) 给 $t=0$，再由 (10.5) 的三个平方等式和自伴平方零得到三像全为零。若 $t=0$，$\mathsf X^2=\mathsf Y^2=0$ 给两像为零；剩下的像由一个自伴元 $\pi(\mathsf A)$ 生成，且平方为 $4rI$，不可约性遂给一维表示及所列两个标量值。

设 $t>0$。式 (10.5) 给 $e_1,e_2$ 为反交换自伴酉元。令 $H_+$、$H_-$ 为 $e_1$ 的正、负特征空间；$e_2$ 在二者之间给酉双射。因此存在 Hilbert 空间 $K$ 使

$$
H_\pi\cong\mathbb C^2\otimes K,\qquad
 e_1=\sigma_z\otimes I_K,\qquad
 e_2=\sigma_x\otimes I_K.
\tag{11.7}
$$
当 $s=0$，这两元生成 $M_2(\mathbb C)\otimes I_K$；不可约性迫使 $K=\mathbb C$，故表示二维。

当 $s>0$，$e_3$ 也是与前两元反交换的自伴酉元。与 (11.7) 的两元反交换的算子必为

$$
 e_3=\sigma_y\otimes W
\tag{11.8}
$$
其中 $W=W^*$ 且 $W^2=I_K$。前两元已生成 $\sigma_y\otimes I_K$，与 $e_3$ 相乘又给 $I_2\otimes W$，故生成代数为 $M_2(\mathbb C)\otimes C^*(W)$。$W$ 的正、负特征空间正交直和为 $K$；任取其中一个非零特征向量，其张成的一维空间与 $\mathbb C^2$ 的张量积是生成代数的不变子空间。不可约性迫使 $K$ 一维、$W=\varepsilon I$，其中 $\varepsilon=\pm1$。标准 Pauli 乘法 $\sigma_z\sigma_x=\mathrm i\sigma_y$ 遂给 (11.5)–(11.6)。

这对应成熟的 $\mathrm{Cl}_2(\mathbb C)\simeq M_2(\mathbb C)$ 与 $\mathrm{Cl}_3(\mathbb C)\simeq M_2(\mathbb C)\oplus M_2(\mathbb C)$ 表示分类；各纤维只保留实际商中存在的表示。∎

## 12. 双对偶中的最大反射支撑

**定理 12.1（残余的满支撑角与两种 Clifford 取向）。** 在 10.1 下，令 $M=\mathfrak B_{y,z}^{**}$，对正中心元置 $s_M(a)=1_{(0,\infty)}(a)\in Z(M)$，并记

$$
\mathsf C=-\mathrm i\,\mathsf A\mathsf X\mathsf Y,
\qquad
z_{\rm res}=s_M(\mathsf T),
\qquad
z_{\rm ref}=s_M\bigl(\mathsf T(4\mathsf R-\mathsf T)\bigr).
\tag{12.1}
$$

则 $\mathsf C$ 是 $\mathfrak B_{y,z}$ 内的中央自伴元，且

$$
\mathsf C^2=\mathsf T^2(4\mathsf R-\mathsf T).
\tag{12.2}
$$

在 $Z(M)$ 中作有界 Borel 函数演算，令 $\Omega=\operatorname{sgn}(\mathsf C)$，其中 $\operatorname{sgn}(0)=0$。则

$$
\Omega^2=z_{\rm ref},\qquad
z_\pm=\frac{z_{\rm ref}\pm\Omega}{2}
\tag{12.3}
$$

是两个正交中央投影。在 $0<t<4r$ 的每个不可约表示的正常双对偶延伸下，$\Omega$ 的像恰为 (11.5) 的 $\varepsilon(\pi)$。准确的最大性是：对任一中央投影 $e\in Z(M)$，

$$
\begin{aligned}
s_{eM}(e\mathsf T)=e
&\iff e\le z_{\rm res},\\
s_{eM}(e\mathsf T)=s_{eM}\bigl(e(4\mathsf R-\mathsf T)\bigr)=e
&\iff e\le z_{\rm ref}.
\end{aligned}
\tag{12.3a}
$$

故 $z_{\rm res}$ 是 $\mathsf T$ 满支撑的最大中央角，$z_{\rm ref}$ 是两份正元同时满支撑的最大中央角。满支撑表示在该角的忠实正常表示中核为零；不要求谱与零分离或正元可逆。

证明。三生成元两两反交换，故 $\mathsf A\mathsf X\mathsf Y$ 与每个生成元交换；反转三个自伴因子的次序给 $(\mathsf A\mathsf X\mathsf Y)^*=-\mathsf A\mathsf X\mathsf Y$，所以 $\mathsf C$ 中央且自伴。三次反交换的平方恒等式为

$$
(\mathsf A\mathsf X\mathsf Y)^2=-\mathsf A^2\mathsf X^2\mathsf Y^2,
$$

代入 (10.5) 得 (12.2)。Borel 函数演算给 $\Omega^2=s_M(\mathsf C^2)$。对交换正元，乘积的支撑是两支撑之交；它们可同时按非负函数读取，乘积非零的集合恰是两者同时非零的集合。因此

$$
s_M(\mathsf C^2)
=s_M(\mathsf T)s_M(4\mathsf R-\mathsf T)
=z_{\rm ref}.
\tag{12.4}
$$

于是 (12.3) 的两元自伴、平方等于自身且乘积为零。中央投影 $e$ 与谱投影交换，故 $s_{eM}(ea)=e\,s_M(a)$；分别用于两份正元便得 (12.3a) 及最大性。在这些角上零仍可为谱的聚点。

对内点纤维，(11.6) 给 $\pi(\mathsf C)=\varepsilon\,t\sqrt{4r-t}\,I$；正常延伸保留相应谱支撑，故 $\Omega$ 的像为 $\varepsilon I$。边界 $t=0$ 或 $t=4r$ 的表示消灭 $z_{\rm ref}$；前者无残余，后者有二维 Pauli 对但没有第三轴取向。上述投影属于诊断双对偶，不因此属于原 $E$ 或全环境中心。∎

## 13. 同一原混合残余的交换子理想

**定理 13.1（原混合误差的精确闭理想与交换化）。** 在 10.1 的同一原资料、同一原 $h,y,z,J$ 下，简记 $B=\mathfrak B_{y,z}$，以 $\operatorname{Id}_B(a)$ 表示包含 $a$ 的最小范数闭双边星理想。令

$$
\mathcal K=\overline{\operatorname{span}}
\{b[c,d]e:b,c,d,e\in B\},\qquad
\mathsf H=[\mathsf X,\mathsf Y].
\tag{13.1}
$$

则同一原响应的两份误差满足

$$
\begin{gathered}
\mathsf H=2\mathsf X\mathsf Y,\qquad
\mathsf H^*\mathsf H=4\mathsf T^2,\qquad
|\mathsf H|=2\mathsf T,\\
\boxed{\mathcal K
=\operatorname{Id}_B(\mathsf H)
=\operatorname{Id}_B(\mathsf T)
=\operatorname{Id}_B(\mathsf X)
=\operatorname{Id}_B(\mathsf Y)
=\overline{\mathsf T B}.}
\end{gathered}
\tag{13.2}
$$

特别地，下列条件等价：$B$ 交换、$\mathcal K=0$、$\mathsf H=0$、$\mathsf T=0$、两份原混合式

$$
Jy\circ Jz=y\circ z,\qquad
y\circ Jz+Jy\circ z=0
\tag{13.3}
$$

同时成立。商 $B/\mathcal K$ 是此诊断代数的最大交换 C* 商，允许为零；任意到 C* 代数的 *-同态 $\rho$ 均满足

$$
\rho(B)\text{ 交换}
\iff\rho(\mathsf T)=0
\iff\rho(\mathsf X)=\rho(\mathsf Y)=0.
\tag{13.4}
$$

在 12.1 的 $M=B^{**}$ 中，还有精确支撑关系

$$
\overline{\mathcal K}^{\,w^*}=z_{\rm res}M.
\tag{13.5}
$$

所有闭包和商均只在固定的诊断 C* 代数中使用，不给原 $D$ 新增商论域、连续性或可加性前件。

证明。10.2 的反交换给 $\mathsf H=2\mathsf X\mathsf Y$；自伴性和 $\mathsf X^2=\mathsf Y^2=\mathsf T$ 给

$$
\mathsf H^*\mathsf H
=4\mathsf Y\mathsf X^2\mathsf Y
=4\mathsf T\mathsf Y^2=4\mathsf T^2.
\tag{13.6}
$$

$\mathsf T\ge0$，所以唯一正平方根是 $|\mathsf H|=2\mathsf T$。令 $I=\operatorname{Id}_B(\mathsf T)$。在 C* 商 $B/I$ 中，$\mathsf X$ 和 $\mathsf Y$ 的自伴像平方均为零，故两像为零。商由单位像和一个自伴元 $\mathsf A+I$ 生成，因而交换，包含零商情形。因此全部交换子在 $I$ 中，$\mathcal K\subset I$。

另一方面 $\mathsf H\in\mathcal K$，而包含 $\mathsf H$ 的闭星理想包含 $\mathsf H^*\mathsf H$ 及其连续函数演算的正平方根。故 $\mathsf T=|\mathsf H|/2\in\operatorname{Id}_B(\mathsf H)\subset\mathcal K$，从而 $I\subset\operatorname{Id}_B(\mathsf H)\subset\mathcal K\subset I$。其中平方根函数在零处为零，故可在该理想内作演算，不需理想有单位。

$\mathsf T=\mathsf X^2$ 给 $I\subset\operatorname{Id}_B(\mathsf X)$；上段的商平方零又给 $\mathsf X\in I$，故两理想相等。$\mathsf Y$ 同理。$\mathsf T$ 中央，$\mathsf TB$ 本身是双边星理想，故其范数闭包就是 $I$。这证明 (13.2)。单位存在时 $[c,d]=u[c,d]u\in\mathcal K$；交换子换序取伴随仍在所定义的闭线性包内，所以 $\mathcal K$ 确是全部交换子生成的闭星理想。

由 (13.2)，$\mathcal K=0\iff\mathsf T=0\iff\mathsf H=0$；自伴平方零给 $\mathsf T=0\iff\mathsf X=\mathsf Y=0$，后者按 (10.2)–(10.3) 正是 (13.3)。全部交换子为零等价于 $B$ 交换。任一交换像的 *-同态都消灭全部交换子及 $\mathcal K$，反向消灭 $\mathcal K$ 的同态经交换商因子化。这既证明最大交换商的泛性质，也给 (13.4)，包括零同态。

最后令 $e_n=\mathsf T(\mathsf T+n^{-1}u)^{-1}\in\mathsf TB$。这是固定环境正元的连续函数演算；有界递增序列 $e_n$ 在 $M$ 中强收敛、亦弱星收敛到 $z_{\rm res}$。故 $\overline{\mathcal K}^{w^*}$ 包含 $z_{\rm res}$。范数闭双边理想的弱星闭包是 $M$ 的双边理想：先固定一个 $B$ 元取弱星极限，再用 $B$ 在 $M$ 的弱星稠密性和乘法分别弱星连续性，便允许两侧乘任意 $M$ 元。因此它包含 $z_{\rm res}M$；反向由 $(u-z_{\rm res})\mathsf T=0$ 及 $\mathcal K=\overline{\mathsf TB}$ 得到。式 (13.5) 成立。这里只逆 $\mathsf T+n^{-1}u$，从未逆 $\mathsf T$，故零谱及向零积聚的连续谱均在证明内。∎

**定理 13.2（残余读取的存在、量词与精确范数）。** 在 13.1 下，(13.3) 等价于 $z_{\rm res}=0$，也等价于不存在满足 $\pi(\mathsf T)>0$ 的不可约表示。若 $\mathsf T\ne0$，存在满足

$$
\pi(\mathsf T)=\|\mathsf T\|I>0
\tag{13.7}
$$

的二维不可约商表示。准确的全称结论是：每个实际读取 $t>0$ 的不可约表示为二维，每个读取 $t=0$ 的不可约表示为一维；同一个有非零残余的 $B$ 可以兼有两类表示。对每个不可约表示，

$$
\begin{gathered}
\|\pi(\mathsf X)\|=\|\pi(\mathsf Y)\|=\sqrt t,
\qquad \|\pi(\mathsf A)\|=\sqrt{4r-t},\\
\|\pi(\mathsf H)\|=2t.
\end{gathered}
\tag{13.8}
$$

全局则有

$$
\begin{gathered}
\|\mathsf X\|=\|\mathsf Y\|=\sqrt{\|\mathsf T\|},
\qquad \|\mathsf A\|=\sqrt{\|4\mathsf R-\mathsf T\|},\\
\boxed{\|[\mathsf X,\mathsf Y]\|
=2\|\mathsf T\|=2\|\mathsf X\|^2=2\|\mathsf Y\|^2.}
\end{gathered}
\tag{13.9}
$$

证明。正元支撑为零当且仅当该元为零；13.1 遂给与 $z_{\rm res}=0$ 的等价。若 $\mathsf T=0$，所有表示当然消灭它。反向设 $m=\|\mathsf T\|>0$。在 $C^*(u,\mathsf T)$ 上取正谱最大点 $m$ 的评价态，并将它正延伸到 $B$。因此

$$
F=\{\phi\in S(B):\phi(\mathsf T)=m\}
\tag{13.10}
$$

是非空弱星紧凸集。它还是整个态空间的面：若 $0<\lambda<1$ 且 $\lambda\phi_1+(1-\lambda)\phi_2\in F$，由 $0\le\phi_i(\mathsf T)\le m$，必有两份读数都等于 $m$，即两态均属 $F$。Krein–Milman 定理给 $F$ 的一个极点 $\phi$；面的性质使它也是 $S(B)$ 的极点，故为纯态。

纯态的循环 GNS 表示 $\pi_\phi$ 非零且不可约。中央性和 Schur 引理给 $\pi_\phi(\mathsf T)=tI$，循环单位向量的读数给 $t=\phi(\mathsf T)=m>0$。11.2 遂给二维表示，像为 $M_2(\mathbb C)$，所以也是所述商表示。这完成不存在正残余不可约读取与 $\mathsf T=0$ 的双向证明。11.2 给两类表示的准确量词；(10.5)、(13.6) 与 C* 范数恒等式分别在表示中和 $B$ 中给 (13.8)–(13.9)。不需谱隙、原投影、原纯态准备或全局矩阵分解。∎

## 14. 退化边界与已付原窗口

**命题 14.1（第三轴为零仍有完整残余理想）。** 只保留 2.1 的代数关系，在 $M_2(\mathbb C)$ 中取

$$
P=\sigma_z,\qquad Q=-\sigma_z,\qquad U=V=\sigma_x.
\tag{14.1}
$$

则 $\mathsf A=0$、$\mathsf X=2\sigma_z$、$\mathsf Y=2\sigma_x$、$\mathsf R=I$、$\mathsf T=4I$。这是 $t=4r$ 的二维边界纤维；两份混合式均失败，且

$$
\mathsf C=0,\qquad z_{\rm ref}=0,\qquad
\mathcal K=M_2(\mathbb C),\qquad
|[\mathsf X,\mathsf Y]|=8I.
\tag{14.1a}
$$

所以第三轴取向支撑不能代替残余理想的支撑。有限方程也允许非零残余与标量读取并存、以及连续残余向零积聚。

证明。Pauli 乘法给 $P^2=Q^2$、$\mathsf X^2=\mathsf Y^2=4I$、$\mathsf X\circ\mathsf Y=P\circ\mathsf Y=0$，且 $\mathsf A=0$。故 $r=1,t=4$，而 $\mathsf X,\mathsf Y$ 生成 $M_2(\mathbb C)$；$\mathsf T=4I$ 生成整个理想，13.1 给 (14.1a)。

与标量块 $P=Q=1/2,U=V=0$ 直和后，$\mathsf A=1\oplus0$，$\mathsf X=0\oplus2\sigma_z$，$\mathsf Y=0\oplus2\sigma_x$，故诊断代数为 $\mathbb C\oplus M_2(\mathbb C)$，$\mathcal K=0\oplus M_2(\mathbb C)$。其一维表示读取 $r=1/4,t=0$，二维表示读取 $r=1,t=4$，两者确实并存。

另将 (14.1) 的四元组同时乘以参数 $\lambda\in[0,1]$，在 $C([0,1],M_2)$ 中生成诊断代数。固定坐标函数给 $\mathsf R(\lambda)=\lambda^2I$、$\mathsf T(\lambda)=4\lambda^2I$、$\mathsf A=0$。每个 $\lambda>0$ 的取值表示为二维，$\lambda=0$ 的像为标量；$\mathsf T$ 的谱为 $[0,4]$，所以不具有正下界。其 $z_{\rm res}$ 角仍满支撑，且每个正 $\lambda$ 的表示延伸在此角上为单位，因而该角中的谱也含向零积聚的正值。上述构造只实现有限两圆代数关系，不提供整个原 $E^2$ 上满足全部 P2 与完整 PB 的总 $D$。∎

**定义 14.2（同一原三标签与整体障碍）。** 三标签仍是同一真正原 $(h,y,z)$：$h$ 是原第三标签，$Jy,Jz$ 是同一旧 $D$ 的实际响应；$\mathsf A,\mathsf X,\mathsf Y$ 由这五个原元素通过 Jordan 组合得到。在给定原 JC 包含中有

$$
\text{同一原 PB 两圆接口}
\Longrightarrow
\text{三元反交换及中心锥 }0\le\mathsf T\le4\mathsf R
\Longrightarrow
\mathcal K=\operatorname{Id}_{\mathfrak B_{y,z}}([\mathsf X,\mathsf Y])
=\overline{\mathsf T\mathfrak B_{y,z}}
\Longrightarrow
\bigl(\mathfrak B_{y,z}\text{ 交换}\iff\text{两份原混合式成立}\bigr).
\tag{14.2}
$$

这个闭理想结论针对未归一化的同一原混合误差，并连接所有纤维的公共交换商；不只是将每个正纤维除以长度得到 Pauli 轴。任意标量读取必消灭该理想，读取正残余的二维表示则不能消灭它；14.1 说明第三轴退化时这份障碍仍完整存在。结论是给定弱 JC 包含中的诊断，不断言不同忠实 JC 环境的全部诊断代数已被规范识别。

**定义 14.3（已付半正定窗与全域边界）。** 在本追加部分引用中央卷时，同时采用其 94–99。中央卷 97.1 已给：若原标量平方子空间 $K\subset V_h$ 满足 $z\circ K\subset\mathbb Ru$，则同一个旧 $J$ 对全部 $k\in K$ 满足 $J(z+k)=Jz+Jk$。中央卷 97.2 已将其用于 91.1 的全部核方向：若原实线性 $W\subset V_h$、$R_1\in E\setminus\mathbb Ru$ 及实二次型 $q_0,q_1$ 满足

$$
w^2=q_0(w)u+q_1(w)R_1\quad(w\in W),\qquad q_1\ge0,
\tag{14.3}
$$

则同一旧 $J|_W$ 实线性，且对全部 $v,w\in W$ 有

$$
Jv\circ Jw=v\circ w,\qquad
v\circ Jw+Jv\circ w=0.
\tag{14.4}
$$

包括 $q_1=0$、退化、任意秩、无限维、连续谱及不定 $q_0$；不要求 $R_1$ 在全环境中央、正或可逆，也不要求 $J(W)\subset W$。该特定核匹配与窗口内加法因而属于已付条件结论。若 10.1 的 $y,z$ 同属这样的 $W$，则直接有 $\mathsf T=0$、$\mathcal K=0$；NR 分支和已有标量平方窗也保持其既有结论。

尚须另外证明的是这些前件之外的一般原输入加法、不同原首标签的共同取向、任意第一输入的可加，以及同一旧 $D$ 在全部 $E^2$ 上的实双线性与完整原复乘法。一般原域未必有非零原正交单位方向，故本窗不是全原域的普遍入口。一般商下降、完成延拓、全域原 R、输出闭合及七项消费者仍各守原合同；环境读取的商、支撑和结合乘法不提供这些桥。

## 15. 七项量子消费者的准确接线

**定义 15.1（局部障碍与七项原合同）。** 10.1–14.3 只约束同一标量平方差原对的混合残余、诊断表示及交换子理想；下列七项原合同逐项保持原量词。

| 原消费者 | 局部结果提供与仍必须保持的原条件 |
| --- | --- |
| 1. 复 Hilbert 载体、可观测量与叠加 | $\mathfrak B_{y,z}$ 只给同一原对的数学 C* 诊断和局部 Pauli 纤维。仍须忠实 JC 包含保持同一 $S,C,u,N$，以及同一旧 $D$ 在全部原 $E$ 上的实双线性，才可接全部有限复 Gram、原 $R$ 和 $a\star b=a\circ b-\mathrm iD(a,b)$ 的同一结合乘法；$\mathsf F$ 路线仍守其完整 $E=A_{\rm sa}$ 前件。原可取得标签、跨评价配对、共同核 $K$、同一 $J_a$、全部有限及零长度全词、native、父位置、ready、合法控制和实际相干叠加准备，均不能由纤维表示供应。 |
| 2. 态、效果、质量与 Born | 全部原正实评价、准确效果、零／不等／次归一质量和中心权保持；只有原实际完整菜单 $\sum_l e_l=u$ 且 $m_\alpha=\alpha(u)>0$ 时才用 $\alpha(e_l)/m_\alpha$，零质量不除。共同根、准备、接受、抽签、mark、接线、全部 P9 分支、独立 $W_e$、AS／EC、菜单外 OB、实际二维到三维适配器、固定支持和全部切口仍取中央卷 52.1、三角卷 250.1 的同一合同；数学态、纯态 GNS 和 $\mathfrak B_{y,z}$ 的二维表示不变成实际准备或质量。 |
| 3. native、真正相关联合与张量 | 仍须同一个非零实际共同来源、全部中心对、经典／不等维块、忠实同向交换的局部全矩阵两腿、交叉零、生成分离、共同联合生成与重数，以及全部乘积和真正相关输入。分别可得的二维诊断商、边缘表示或中心谱不能拼成同一实际相关联合，也不能替代局部旧乘法的共同取向。 |
| 4. CP 与整台递归同源参考 | 原 typed 前接、真实未归一回溯、合法后口、全未来自然性、反变复合、typed 分区及箭头商下降全部保留。还需整台仪器连环境及每一个成功、失败、记录、后口输出的同规则实际 $r^+$，系统腿和 $M_2$ 腿共同真支持、三颗实际投影及 $I_2$ 实张成、支持内补事件、全部相关正输入的 intertwining 与夹界、每个所需有限递归深度及累计支持的准确运输；一个二维不可约诊断商不支付任何 CP 或递归实际箭头。 |
| 5. 完整仪器、更新、TP 与 Lüders | 同一旧星乘法另已在全部原域识别后，才有原正夹心；完整 typed 单位分区才给 TP，全部输出的像内射线校准才接 Lüders。全输入运输、成功／失败、记录／后口、停止／拒绝／销毁、接受、真正遗忘、AC、精确 $N_u$、X／Xs、原平方根词和接受端均保留。Kraus、密度、迹类及收敛只在有限全矩阵域，或另有正常物理表示、指定前对偶和适用分解／收敛接口时使用。 |
| 6. 全历史、全部未来、遗忘与真实返回 | 全部合法顺序／自适应／并行历史、环境泄漏、细记录及每个输出仍合法的每个未来、停止／拒绝／销毁、共同记录真正分组遗忘均保身份，未定义请求仍未定义。$B,B_{\rm cl}$、同数两侧真实逆向返回、CountRead 完整输出至全部活动 ready 接头、两条负提升活路和相干聚合、全菜单及接受端、九叶彩票、空程序、拒绝叶与相干返回继续保持三角卷 250.1 的原合同；非离散／无穷记录、可数可加、无限历史、正常性和指定前对偶仍须原桥。 |
| 7. 物理动力与共同尺度 | 全域旧乘法另被识别且流保持原域后，才可消费完成上的指数流；还须原相位、实际门序列、可逆一参数群、物理钟、所需强连续酉实现及生成元域、Hamiltonian 能量解释、作用量、共同 $\hbar>0$ 与共同仪器齐备，才按原规范使用 $\dot b=2D(H,b)/\hbar$。$r,t$、Pauli 坐标、$\Omega$ 和双对偶支撑不是物理时间、能量、作用量或共同尺度。 |

原 $\Omega/\mathrm{native}$、全词 $K/J/q/u/N/\mathcal P/S/D$、父位置与 ready、原中心／经典／不等维块／静默域、全部质量、全部实际准备与完整菜单、共同记录真正分组遗忘、全仪器及其每一个环境／输出／成功／失败／记录／后口、同一实际相关联合与递归同源参考、全部合法顺序／自适应／并行历史和每个合法未来、停止／拒绝／销毁、同数两侧真实双向返回、CountRead 正常性与前对偶、物理钟／能量／共同 $\hbar$，一律继续取 8.2–8.4、中央卷 52.1、三角卷 128.1、206.1、250.1 的完整原资料与全部量词。

## 16. 数学接口与完整直观

**定义 16.1（成熟工具与原响应的对应）。** 2.1 及三角卷 212.1–213.1 给等平方差两圆关系和半定消去；三角卷 190.1–190.3、219.1 给已归一固定三轴及局部体积元。中央卷 88–91 的仿射陪集和核差公式与 94–99 的核匹配按 14.3 一并使用。任意弱 JC 包含下的固定原对由这些实际两圆关系得到 (10.5)，而 (13.2) 进一步将其未归一化误差与整个诊断代数的闭交换子理想、最大交换商及 (13.5) 的支撑连接。

Lundholm–Svensson，[*Clifford algebra, geometric algebra, and applications*](https://www.math.lmu.de/~lundholm/clifford.pdf)，§2.1–§2.3、Example 5.2、Theorem 8.4 分别供应反交换关系、Pauli 实现和有限维复 Clifford 不可约分类。Landsman，[*Lecture Notes on C*-Algebras, Hilbert C*-modules, and Quantum Mechanics*](https://arxiv.org/abs/math-ph/9807030)，§2.5 的连续函数演算、Theorems 2.7.2–2.7.3 的近似单位与闭理想商、Theorem 2.12.4 的纯态 GNS 不可约性及 Theorems 2.12.10–2.12.11 的极点和谱值支撑，分别用于 13.1 的理想计算和 13.2 的紧面分离。它们均是原响应定理内的中间工具。

[小窗口单位桥卷](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md) 70.1–70.2 已有具体连续矩阵代数的闭交换子理想与乘子取向；75.2–77.1 讨论原有限词的代数理想和最小取向载体。13.1 的 $\mathcal K$ 则是同一对实际 PB 响应误差生成的诊断 C* 代数内的范数闭理想；不将它认作原有限词代数理想，不以闭包论证替代原域成员关系，也不把它认作全域旧 $D$ 的最小取向载体。

**定义 16.2（完整白话）。** 固定同一个原参考方向和同一对原输入，仍使用那张旧响应表；只选择两输入平方之差是标量单位的情形。原配平使两个混合误差成为彼此反交换、平方相同的两根数学轴，共同平方 $T$ 就是误差强度。它们交换先后顺序的差，其绝对值恰好是 $2T$。因此，允许在诊断代数中左右相乘、相加并取范数极限后，所有换序差生成的部分，正好就是原两份误差生成的部分；把这一部分取商消去，剩余代数必交换。反过来，诊断代数若交换，两份原误差便同时为零。这是一条对同一原对的整体障碍，不只是一份归一化矩阵形状。

只有实际读到 $T>0$ 的不可约截面才必为二维；一个有误差的代数仍可同时有读到 $T=0$ 的一维截面。第三轴尚在时，每个实际内部截面保留两种可能取向中的一种；第三轴退化时两根误差轴仍可非零；总平方为零时则全部消失。中心读数可连续向零靠近，满支撑只保证没有核，不保证能求逆。中央卷 94–99 已使所述半正定平方窗口的核内外转向一致，该窗口内的加法和混合关系属于已有结论；窗口之外的全原域加法与不同参考方向的共同取向仍须另证。这里没有给原响应增加连续性，没有把商、谱或支撑变成原演员，也没有从有限矩阵片段造出总 P2/PB 模型。原世界仍可无原子、投影贫乏、含型 II／III、中心、经典、不等维块及静默域；全部零、不等和次归一质量以及七项消费者的实际准备、完整仪器及全部输出、共同相关联合、递归同源参考、每个合法历史与未来、真正遗忘与真实返回、计数、钟、能量和共同作用量，继续保留各自原条件。

## 追加锚（本行以下为增补区）

## 17. 实际配平提取的同读取极限面积族

**约定 17.0（所属源与子系统范围）。** 17–23的无卷名编号指本卷；[中央续卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)指《中央响应平方与径向一致续卷》，其中133–156的编号及公式仍只属于该源。中央续卷137–146已给有限四系数、内部闭合的规范候选及同一原矩阵坐标运输，候选响应不等于尚未全域识别的旧 $D$。中央续卷150.1已在完整原PB、P2和实际三轴前件下识别每个混合原输入的横向输出；本卷下面的总映射故意不满足完整PB，只分离被提取的极限绝对预算，绝不反驳该已付身份。完整候选、全部来源和七项消费者保持22.2的全量合同。

**定义 17.1（完整候选与被提取的子系统）。** 完整研究候选仍是中央续卷130.1、136.2、147.1的同一原 $\mathsf H_{\rm orig}+\mathsf{PB}$，并逐句纳入[多项式零响应卷24.1、29.2](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)和[C139续卷155.1–155.2](AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md)的全部原来源及递归合同。以下另外定义一个估计子系统，只研究它丢失了什么信息；该子系统不替换完整候选。

沿中央续卷123.2记 $B_\phi(v,w)=\phi(v^2)\phi(w^2)-\phi(v\circ w)^2$。固定实际原 $a,b$，记 $x=D(a,b)$、$q=a\circ b$。若某个实际 $z$ 满足

$$
a\circ z=0,\qquad D(a,tz)=tT_a z\quad(t\in\mathbb R),\qquad z\circ T_a z=0,
\tag{17.1}
$$

则实际 $\mathsf{PB}(a;b,tz)$ 的两份外层及右端准确为

$$
\begin{gathered}
(b+x,\ t(z+T_a z)+q),\qquad
(b-x,\ t(z-T_a z)-q),\\
-2b\circ x-2t z\circ q.
\end{gathered}
\tag{17.2}
$$

对同一个正实读取 $\phi$，两份实际P2和标量三角不等式给，当 $t\ne0$ 时，

$$
2\left|\phi(z\circ q)+\frac{\phi(b\circ x)}t\right|
\le
\sqrt{B_\phi(b+x,z+T_a z+q/t)}
+\sqrt{B_\phi(b-x,z-T_a z-q/t)}.
\tag{17.3}
$$

只用了 $B_\phi(v,tw+q)=t^2B_\phi(v,w+q/t)$。对固定 $v,w,q$，$B_\phi(v,w+s q)$ 是非负实二次多项式；令 $t\to+\infty$ 只对这些已知标量式和平方根取极限，得到

$$
\boxed{
2|\phi(z\circ q)|\le
\sqrt{B_\phi(b+x,z+T_a z)}
+\sqrt{B_\phi(b-x,z-T_a z)}.}
\tag{17.4}
$$

这里没有对未知旧响应取输入极限，也没有识别两份外层值。原实际三轴 $a=h,e,j$ 的全部 $z\in V_a$ 由中央续卷133.1及其同条件的循环应用供应(17.1)。这份预算推导是既有PB/P2的直接消费，本身不作为新增刚性。

在一个另外指定的总映射中，若全部 Jordan 正交对的响应已知为 $T_a z$，称“全部极限面积族”为(17.4)对每个 $a,b,z$、每个 $a\circ z=0$ 及每个正实读取同时成立。以下模型甚至满足这份全首标签的较大族。它不被要求满足(17.3)的全部有限 $t$ 关系。

## 18. 两块上保留全部准确横向行的单一总映射

**定义 18.1（域、三轴及三个混合对）。** 取

$$
\begin{gathered}
E=X=(M_2(\mathbb C)\oplus M_2(\mathbb C))_{\rm sa},\qquad u=(I,I),\\
S(A,B)=A\circ B=\tfrac12(AB+BA),\qquad
C=E\cap(M_2\oplus M_2)_+,\qquad
N(A)=\max_r\|A_r\|,\\
D_*(A,B)=\tfrac{\mathrm i}{2}[A,B],\\
H=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
K=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
J=\begin{pmatrix}0&\mathrm i\\-\mathrm i&0\end{pmatrix},\\
h=(H,H),\qquad e=(K,K),\qquad j=(J,J),\\
b=(H+K+J,\ 2H+3K+4J).
\end{gathered}
\tag{18.1}
$$

评价族取全部正实线性泛函，保留全部非负质量。特别 $D_*(h,e)=j$、$D_*(e,j)=h$、$D_*(j,h)=e$，且

$$
b^2=(3I,29I),\qquad
h\circ b=(I,2I),\quad e\circ b=(I,3I),\quad j\circ b=(I,4I).
\tag{18.2}
$$

令 $\mathcal S$ 是三个实际对 $(h,b),(e,b),(j,b)$ 的完整 $O(2)$ 轨道之并。换基作用是

$$
O\cdot(A,B)=(o_{11}A+o_{12}B,\ o_{21}A+o_{22}B).
$$

在整个 $E^2$ 定义同一个总函数

$$
\widehat D(A,B)=
\begin{cases}
-D_*(A,B),&(A,B)\in\mathcal S,\\
D_*(A,B),&(A,B)\notin\mathcal S.
\end{cases}
\tag{18.3}
$$

重叠轨道也给相同规则，不需为三条行各选一个映射。$\widehat D$ 只用于下面明确列出的子系统。

**定理 18.2（准确横向行与整个估计族仍不识别混合行）。** 定义18.1的同一总映射满足全部原A1–A3/P2、准确锥及范数条件，并有以下共同性质。

1. 对全部 $A\circ B=0$，$\widehat D(A,B)=D_*(A,B)$。因此每个实际单位轴的整条横向行及其标准复合、平方、混合Gram和斜关系均准确，特别保留中央续卷133.1在本模型中的准确横向原值。对 $a=h,e,j$、$z\in V_a$ 和全部实 $s,\ell$，还有 $\widehat D(sa,z+\ell u)=sD_*(a,z)$。
2. 对每个 $O\in O(2)$，$\widehat D(O\cdot(A,B))=\det(O)\widehat D(A,B)$。反对称、每槽奇性及全部 $SO(2)$ 不变性成立；$N(\widehat D(A,B))\le N(A)N(B)$，且 $\widehat D(A,B)=0$ 当且仅当 $[A,B]=0$。单位、中央、仿射同轴及同一生成元多项式零行均保持。任意 Jordan 商中的中央输入，以及任意连续含单位 Jordan 同态的标量输入像，均给响应零像，准确范围见19节。
3. 取其真正的横向值 $T_Az=\widehat D(A,z)=D_*(A,z)$，(17.4)对全部 $A,B,z\in E$、全部 $A\circ z=0$ 和每个正实读取同时成立，包括零、单块零、不等和次归一质量。
4. 对同一个 $b$ 和每个 $a=h,e,j$，记 $q_a=a\circ b$、$b_{+,a}=q_a a$、$b_{-,a}=b-q_a a$。则

   $$
   \begin{gathered}
   \widehat D(a,b_{+,a})=0,\qquad
   \widehat D(a,b_{-,a})=D_*(a,b_{-,a}),\\
   \widehat D(a,b)=-D_*(a,b_{-,a})\ne D_*(a,b_{-,a}).
   \end{gathered}
   \tag{18.4}
   $$

   混合加性缺陷恰为 $-2D_*(a,b_{-,a})$，非零且非中央。
5. 对每个实 $t\ne0$，同一总映射违反真实原 $\mathsf{PB}(h;b,tb_{-,h})$；$t=1$ 时左端减右端恰为 $(8H,100H)$。

本定理是准确横向行加整个极限估计族的反模型，不是全PB、原完整系统或其所有已付后果的反模型；它违反中央续卷150.1已经识别的混合横向投影，不挑战该定理。证明在19–21节。

## 19. 共同轨道避开全部正交对及零像边界

证明18.2的第1、2项。固定 $a\in\{h,e,j\}$，写 $a\circ b=(I,kI)$，其中 $k=2,3,4$。任意行列式一的换基可写成

$$
R=ca-sb,\qquad W=sa+cb,\qquad c^2+s^2=1.
$$

记 $U=c^2-s^2$、$V=cs$，直接用(18.2)得

$$
R\circ W=((U-2V)I,\ (kU-28V)I),\qquad U^2+4V^2=1.
\tag{19.1}
$$

若 $R\circ W=0$，则 $U=2V$、$(2k-28)V=0$；$k\in\{2,3,4\}$ 使 $U=V=0$，矛盾。任意行列式负一的换基是这种旋转后将一个标签反号，Jordan乘积仅反号，所以全部反射也不可能产生正交对。两个块中的原向量 $a_r,b_r$ 各自实线性独立，因此轨道中每个标签在每块都非零且无迹；两块交换子也都非零，因为换基只乘 $\det O$。这些结论对三个轨道的并仍成立。

所以任何实际 $A\circ B=0$ 均不在修改集，完整响应准确为标准值。特别全部实际单位平方轴的横向行保持，不只保留横向响应的平方。对第1项最后的仿射行，$a,z$ 逐块无迹；若 $\ell\ne0$，第二标签有非零块标量部分，不能进入 $\mathcal S$；若 $\ell=0$，两输入正交。两种情形均给所述准确标准值，包括 $s=0$。

标准 $S-iD_*$ 正是矩阵乘法。任意正读取下，它的二表正性来自成熟的正泛函Gram事实。$\mathcal S$ 对整个 $O(2)$ 封闭，且

$$
D_*(O\cdot(A,B))=\det(O)D_*(A,B).
\tag{19.2}
$$

因此(18.3)保留同一反对称及全部换基关系。每份实际二表只会由标准正表变成其复共轭，仍半正定。A2的整个实相加三表由同一 $S$ 决定，保持原样；指定实零向量的虚二次值由反对称性成对抵消。全部排列、零、重复、实尺度和实平移的原输入均已包含。A3的单位及同一有理小效果窗口也完全由标准 $S$ 支付。这没有断言任意三标签复Gram正性。

标准交换子满足 $N(D_*(A,B))\le N(A)N(B)$；整体反号保留此逐点范数界及其完整零集，故给第2项的全部零行。为核对零像的准确范围，任取闭 Jordan 理想 $I_0\subset E$。成熟的简单块事实在这里也可直接核对：$H_2(\mathbb C)=\mathbb RI\oplus\mathbb R^3$，乘法为

$$
(\lambda,v)\circ(\mu,w)=(\lambda\mu+v\cdot w,\lambda w+\mu v).
\tag{19.3}
$$

一个理想若含非零纯向量，其平方给单位；若含 $\lambda I+v$ 且 $\lambda\ne0$，取非零 $w\perp v$，与 $w$ 的乘积给 $\lambda w$，也得到单位。因此每块简单。块的Jordan中心恰为 $\mathbb RI$：若纯向量 $v\ne0$，取非零 $w\perp v$，则 $[L_v,L_w]w=|w|^2v\ne0$。用两个中央块单位相乘分离任一理想，得 $I_0$ 是若干整块之和。若 $A+I_0$ 在商中中央，每个保留块的 $A_r$ 为标量，故 $D_*(A,B)_r=0$；整体反号不改零像，所以 $\widehat D(A,B)+I_0=0$。

再取任意含单位实JB代数 $Y$ 和连续含单位 Jordan 同态 $\rho:E\to Y$。其核是上述理想。若 $\rho(A)=\mu1_Y$，则 $A-\mu u\in\ker\rho$，每个保留块的 $A_r=\mu I$，从而

$$
\rho\widehat D(A,B)=0.
\tag{19.4}
$$

零目标同样成立，反对称性处理第二槽。这里只证明商中心或标量像的零吸收，不在任意商上定义响应，也不把两个同像原输入的任意旧值认作相同。∎

## 20. 同一个正读取支付整个极限面积族

证明18.2第3项。先取 $(A,B)\notin\mathcal S$。此时 $x=\widehat D(A,B)=D_*(A,B)$，所有横向值也都是 $D_*(A,z)$。预算(17.4)仅含这些内层值及已知Jordan乘积，所以与标准完整PB模型提取的同一预算逐项相同，因而成立。这里比较的是标量预算，没有假称 $\widehat D$ 的实际外层满足PB。

以下取任意 $(A,B)\in\mathcal S$。19节已给每块 $A_r,B_r$ 无迹且 $A_r\ne0$。用(19.3)的欧氏坐标写

$$
\begin{gathered}
A_r=\alpha_r\cdot\sigma,\quad \rho_r=|\alpha_r|>0,\quad
n_r=\alpha_r/\rho_r,\quad B_r=\beta_r\cdot\sigma,\\
c_r=n_r\cdot\beta_r,\qquad
x=\widehat D(A,B)=-D_*(A,B),\qquad q=A\circ B.
\end{gathered}
\tag{20.1}
$$

Pauli坐标可用通常的三轴；(18.1)中 $J=-\sigma_y$ 的符号不改变点积、正交或长度。$x_r$ 无迹且垂直 $n_r$，而 $q_r=\rho_rc_rI$。

每一个正实读取恰可写为

$$
\phi(v)=\sum_{r=1}^2m_r(\lambda_r+\eta_r\cdot v_r),
\qquad v_r^{\rm matrix}=\lambda_r I+v_r\cdot\sigma,
\qquad m_r\ge0,\quad |\eta_r|\le1.
\tag{20.2}
$$

$m_r=0$ 时可任取 $\eta_r=0$。此处不令 $m_1+m_2=1$，也不在证明中除以任何质量。对逐块无迹的 $v,w$，同一读取的实Gram恰为

$$
\phi(v\circ w)=\sum_rm_rv_r\cdot w_r,
\qquad
B_\phi(v,w)=\|v\|_m^2\|w\|_m^2-\langle v,w\rangle_m^2,
\tag{20.3}
$$

其中 $\langle v,w\rangle_m=\sum_rm_rv_r\cdot w_r$ 可以退化。普通 Cauchy–Schwarz 仍适用，或将每块向量乘 $\sqrt{m_r}$ 后使用通常欧氏内积。

任取实际 $A\circ z=0$。每块 $A_r\ne0$ 使 $z_r$ 的标量部分为零且向量垂直 $n_r$。令

$$
T_Az=D_*(A,z),\qquad w_\pm=z\pm T_Az,\qquad
C_0=\sum_rm_rc_r^2,\quad Z=\sum_rm_r|z_r|^2,\quad
R_0=\sum_rm_r\rho_r^2|z_r|^2.
\tag{20.4}
$$

在每块，$T_Az$ 垂直 $z_r,n_r$ 且长度为 $\rho_r|z_r|$。所以两份 $w_\pm$ 都垂直共同纵向向量 $L=(c_rn_r)_r$，并且

$$
\|w_+\|_m^2=\|w_-\|_m^2=Z+R_0,\qquad \|L\|_m^2=C_0.
$$

将 $B\pm x=L+P_\pm$，其中 $P_\pm$ 逐块垂直 $n_r$。在同一个加权Gram中分离 $L$，再用 Cauchy–Schwarz，得到

$$
\begin{aligned}
B_\phi(B\pm x,w_\pm)
&=C_0(Z+R_0)+\|P_\pm\|_m^2\|w_\pm\|_m^2
 -\langle P_\pm,w_\pm\rangle_m^2\\
&\ge C_0(Z+R_0).
\end{aligned}
\tag{20.5}
$$

另一方面，$q_r=\rho_rc_rI$ 及同一个(20.2)给

$$
\begin{aligned}
|\phi(z\circ q)|
&=\left|\sum_rm_r\rho_rc_r\,\eta_r\cdot z_r\right|\\
&\le\sqrt{\Bigl(\sum_rm_rc_r^2\Bigr)
                 \Bigl(\sum_rm_r\rho_r^2(\eta_r\cdot z_r)^2\Bigr)}
\le\sqrt{C_0R_0}.
\end{aligned}
\tag{20.6}
$$

两式一起给

$$
2|\phi(z\circ q)|\le2\sqrt{C_0R_0}
\le2\sqrt{C_0(Z+R_0)}
\le\sqrt{B_\phi(B+x,w_+)}+\sqrt{B_\phi(B-x,w_-)}.
\tag{20.7}
$$

这就是全部(17.4)。整个证明允许 $C_0,Z,R_0$ 任一为零、读取全零或只读一块；两根号和左端始终使用同一个正读取。它没有分别选择两个优化读取，也没有对未知响应作连续性假设。对三个指定单位轴，$\rho_r=1$，于是 $R_0=Z$，右端至少 $2\sqrt{2C_0Z}$，左端至多 $2\sqrt{C_0Z}$。当 $C_0Z>0$，这份严格余量具体显示绝对面积没有强迫所需取向饱和。∎

## 21. 三条混合行反号及同一实际配平的有符号检出

证明18.2第4、5项。对 $a=h,e,j$，$q_a$ 是(18.2)的中央元，$b_{+,a}=q_a a$ 与 $a$ 交换，而 $a\circ b_{-,a}=0$。标准响应 $D_*(a,b)=D_*(a,b_{-,a})$ 非零；(18.3)在指定混合对反号，却在交换对及全部正交对保持标准值。这给(18.4)和缺陷 $-2D_*(a,b_{-,a})$。该元素在两块都是非零无迹矩阵，故不在 $Z(X)=\mathbb RI\oplus\mathbb RI$。特别

$$
\widehat D(h,b)=(K-J,\ 4K-3J),\qquad
D_*(h,b)=(J-K,\ 3J-4K).
\tag{21.1}
$$

为保留原有符号调用，置

$$
z=b_{-,h}=(K+J,\ 3K+4J),\qquad
y=D_*(h,z),\quad q=(I,2I),\quad b=qh+z,
\quad z^2=(2I,25I).
\tag{21.2}
$$

于是 $\widehat D(h,b)=-y$，而 $\widehat D(h,tz)=ty$。真实 $\mathsf{PB}(h;b,tz)$ 的两份外层准确为

$$
(b-y,\ t(z+y)+q),\qquad
(b+y,\ t(z-y)-q).
\tag{21.3}
$$

它们第二标签的块标量部分分别为 $q$、$-q$，均非零；$\mathcal S$ 中每个标签逐块无迹，所以这两份外层都在修改集之外，实际使用 $D_*$。这一步只识别本显式总映射的实际外层，不是假定一般原旧值双线性。

现在才展开已知双线性 $D_*$。由 $hz=-zh$、$y=ihz$、$q$ 中央，

$$
D_*(h,y)=-z,\qquad D_*(z,y)=hz^2,\qquad
b\circ y=z\circ y=0.
$$

因此

$$
\begin{aligned}
\text{PB左端}
 &=2tD_*(b,y)-2tD_*(y,z)
 =-2tqz+4thz^2,\\
\text{PB右端}&=-2tqz,\\
\text{左端}-\text{右端}&=4thz^2.
\end{aligned}
\tag{21.4}
$$

$t=1$ 时差恰为 $(8H,100H)\ne0$；任意 $t\ne0$ 也失败。同一个产生极限预算的实际非单位第三标签族，在保留有符号等式时已经排除这个总映射。全部极限绝对值预算仍接受它，故其不足来自提取时丢失的联系。没有据此断言全部有限 $t$ 预算成立，也没有断言单位第三标签PB成立。18.2证毕。∎

在这个显式模型中，$P_{\rm tr}w=(w-hwh)/2$，且 $y=Tz$。对同一个混合 $b=qh+z$，实际有 $P_{\rm tr}\widehat D(h,b)=-Tz\ne Tz=T P_{\rm tr}b$。所以该总映射也明确违反中央续卷150.1的已付投影；上面的有限有符号PB差与这一排除一致。这里不先假定一般旧输出横向，也不将一般交换残余认作单独交换输入的响应。

## 22. 与既有反号构造及完整原来源的准确关系

**定义 22.1（承重增量与成熟工具）。** [多项式零响应卷31–35](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)已经使用整个 $O(2)$ 轨道反号，证明单位第三标签子系统不足。该反号机制、标准矩阵模型和逐对复共轭正性在这里直接复用，不计新内容。那个指定轨道含其原正交对，因而不保留准确标准横向值；其32.5只保留相应平方和正交身份。18.2的承重增量是用两块不同的共同正交化条件，使修改轨道避开**所有** Jordan 正交对，再由20节同一读取的纵向Gram分离证明**整个**极限面积族仍成立。单位第三标签子族与极限估计族是不同子系统，没有声称本模型也满足前者。17节的预算代入和取极限单独不构成新增结论。

[多项式零响应卷36–45](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)在其指定标量端点多项式原域已经识别全部无迹输入对的共同取向，并消去全部混合输出的常数和一次项。这些结论直接复用，不能把18.1的两个完整矩阵块当作那个原域，或把明确违反全PB的 $\widehat D$ 当作它们的反例。该卷46–50进一步在同一标量端点多项式原域，支付常数单位偏置下纯轴横向行的整份输出无迹性、对两个输入的正交性及实多项式模线性；非零仿射参数的幅度、一般非横向输入及非恒定中央偏置仍守该卷49.1的准确未付范围。这些结论不由18.2证明或反驳。中央续卷133–135的准确原横向行、中央 $Q$ 及标量平方差运输全部保持原范围；中央续卷150.1、151.1、152.1和153.2的已付混合投影、有限检出、实轴偏移完整值及两份非对角块也完整保留，准确剩余见22.3。

本处结果归为 $\texttt{repo-derived}$ 的精确子系统分离，不主张历史优先权或文献穷尽。Pauli乘法、实二阶正交换基、有限简单 Jordan 块、正泛函Gram和 Cauchy–Schwarz 是成熟中间工具；Jordan与自旋背景沿 Hanche-Olsen–Størmer，[*Jordan Operator Algebras*](https://hanche.folk.ntnu.no/joa/joa-m.pdf)。它们各只承担19–20中写出的有限矩阵和正读取步骤。

Cabello–Peralta，[*Weak-2-local symmetric maps on C*-algebras*](https://arxiv.org/html/1510.00915v1)，Theorem 2.5要求对每两个完整复输入和每份对偶读取，存在一个共同复线性保星映射准确实现两份读取值；面积上界没有供应这种共同等值插值。Ayupov–Arzikulov–Umrzaqov–Nuriddinov，[*2-Local and local derivations on Jordan matrix rings over commutative involutive rings*](https://arxiv.org/html/2108.03993v4)，Theorem 3在其含单位、交换、带对合且 $2$ 可逆的系数环及 $H_2$ 入口要求每两个输入由同一个真实内导子实现；本模型没有这种前件，也不以该分类承担证明。Alfsen–Shultz，[*Orientation in Operator Algebras*](https://pmc.ncbi.nlm.nih.gov/articles/PMC22571/)，Dynamical Correspondences及Theorem 1的入口已要求到斜序导子的全域线性动力对应。局部横向线性和两份绝对预算不支付该入口。三种文献关系都不能由名称相近替代其准确共同实现或线性条件。

**定义 22.2（同一完整候选与七项消费者）。** 完整候选逐句采用17.1所引原合同，仍为同一原 $\mathsf H_{\rm orig}+\mathsf{PB}$ 及全部来源，绝不以 $\widehat D$ 替代。保留 C139 155.1–155.2及其全部递归前件的 $\mathsf Q^{\rm root}_{46}$、整个 $F_3$、全部十一端点、$\rho=0,k=0$、XV23.2／全原E1、同一ready两标量词和176长度选项，原根关系仍为

$$
s=(3,7,1,2,4,5,6,8,9),\qquad
\operatorname{tr}(L_r^\dagger L_r)=2,\qquad
\|U_si_rL_r\|_{\rm HS}^2\le2\quad(r\in\mathfrak K_{\rm r}).
\tag{22.1}
$$

原 $\Omega$ 的全部准备、事件、程序／过程、native及全词同一 $K/J/q$、parent/ready、控制、旗标、环境、参考／副本和真实相关联合均保身份。中心、经典、不等维、静默块及全部零／不等／次归一质量仍在；固定支持的全质量、每个已量化切口和全部菜单不缩减。全部合法顺序／自适应／并行历史、每个完整输出和细记录、每个仍合法未来、真正分组遗忘、失败／拒绝／停止／销毁、同数两侧及真实逆向返回均保留；未定义请求不补零。

七项消费者**全量采用**多项式零响应卷29.2和C139 155.2的原充分条件及其递归合同，以下只说明18.2没有生产它们，不能把本段当作更短的充分集合。实际相干准备、全词共同核及同一旧乘法识别齐备才接Hilbert／叠加；实际完整效果菜单及正输入质量齐备才作Born归一。实际非零忠实同向、交换且共同生成的两腿、原重数和全部相关输入齐备才认回真实张量。每条整台箭头的全槽比较或实际递归同源参考齐备才取得CP；返回复合CP不替因子CP。全部输入／全部输出的typed CP仪器、环境和成功失败细记录、真实单位分区齐备才接Kraus与TP；更新另需正输出质量，Lüders另需该输出的完整绑定与像内射线校准。全部合法历史／未来、真实遗忘和全输出真实返回仍需同一原生产者；无限／非离散CountRead、可数可加、正常性及指定前对偶各守原合同。物理动力学仍需实际可逆CPTP时间群及实际逆、所需强连续酉实现、生成元域、物理钟／能量和共同正 $\hbar$。根迹、两块矩阵、标签旋转及极限参数不供应任何这些来源。

因此估计子系统不足已有18.2的完整反模型；中央续卷已识别混合横向投影之后，一般交换输出余量是否为零、完整混合整行和全域旧响应实双线性，仍未由本反模型判定。没有取得新实际来源、较少独立公理、模型类扩大、资源改进或完整量子目标完成结论。

**定义 22.3（已付混合投影与准确剩余）。** 全量采用中央续卷147.1–147.4的同一原域、实际三轴、完整原PB/P2及有限Jordan投影。对每个原 $x=c+v$、$c=P_{\rm com}x$、$v=P_{\rm tr}x$，中央续卷150.1、153.1给

$$
P_{\rm tr}D(h,x)=Tv,\qquad
D(h,c+v)=Tv+\rho_h(c+v),\qquad
\rho_h(c+v)=P_{\rm com}D(h,c+v).
\tag{22.2}
$$

中央续卷151.1为任何投影违反者给一份有限实际PB及同一读取两张P2的检出，不是一张统一有限资源表；152.1支付每个实常数 $\lambda$ 和原 $v\in V_h$ 的 $D(h,\lambda h+v)=Tv$；153.2在同一原矩阵坐标识别两份非对角输出块。一般 $\rho_h(c+v)=0$、$\rho_h(c+v)=D(h,c)$ 及其与 $v$ 无关性均未由153.3支付。不能先假设整个旧输出横向，再把已付投影当作完整混合行；也不能把实轴偏移与另已付单位偏移未经证明地叠加。一般原首标签、旧全域可加／实双线性、旧P3、原R、同一旧结合乘法及实际来源，继续按中央续卷153.3、155.1的准确范围保留。

[OTF卷13–15](OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md)的已给资源／返回协议及[原生接口卷21](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ORIGINAL_INTERFACE_EXPOSURE_AND_RECOVERY.md)的固定配对码深度障碍，各守其指定来源与条件，不生产本候选的原AURIC来源，也不推出这些来源不存在。22.2仍完整采用唯一原世界及七项消费者的原合同；本处没有新的来源供应、资源界或公理独立性结论。

## 23. 共同转动与有符号接回的几何

**定义 23.1（完整候选的直观含义）。** 原候选仍是同一张二元正表与完整三标签正反配平，连同22.2全量采用的原来源和七项消费者。这个有限反向检验说明：即使所有真正正交的比较已经准确，同一个混合比较仍可在三条参考行上一起反号。两块各自都能用一个角度把输入对变成正交，但它们需要的角度不同；原输入对只能共同转动，所以没有一个合法共同角度把这圈混合对送进已知正交行。只翻转这三圈，其余比较保留原值，就得到一张共同的总表。

每个正读取的面积预算也看不出这次翻转。沿参考方向留下的共同纵向分量给两份Gram同时提供余量；它足以支付全部横向方向、全部正读取和全部质量的极限绝对预算。这不是分别给两份比较挑选方便答案。可是把同一混合对和它的实际横向部分一起送入原有符号配平，两条外层路径认回原标准方向，左右两边便留下明确非零差。因此这份被提取的极限绝对预算不能代替有符号的跨路径联系。完整原配平已按中央续卷150.1锁住每个混合输入的横向输出，这个总映射正因违反它而被排除；仍待识别的是一般交换输出余量，而不是整份混合横向投影。

这里的三方向来自二阶矩阵的无迹系数，两块也不是两套已实现的物理系统。比较换序的反号、共同旋转不变、所有正交值正确，以及三标签嵌套路径接回同一结果，是不同关系。这个结论严格区分了它们，未把未知混合值写成定义后宣布已经解决，也未减少完整候选的独立来源条件。实际准备、完整菜单、所有质量、整台仪器及全部输出、真实联合和递归参考、全部历史未来及真实遗忘返回、完整计数、物理钟、能量和共同作用量继续按原合同保留。

## 追加锚（本行以下为增补区）

## 24. 固定二表正性与两个交换关系不足以消除余量

**定理 24.1（四阶全态预算的非零余量）。** 在 $M_4(\mathbb C)$ 中存在自伴 $h,x,r$，$h^2=I$，取中央自伴对合 $Q=I$ 并按原式定义

$$
c=(x+hxh)/2,\quad z=(x-hxh)/2,\quad
k=h\circ x=hc,\quad t=i[h,x]/2=ihz,\quad g=t+r,
\tag{24.1}
$$

使 $[h,r]=[c,r]=0$，且每个归一数学态 $\varphi$ 均满足

$$
\varphi(g)^2+\varphi(k)^2<\varphi(x^2),\qquad
r^2=(z\circ r)^2=I/256.
\tag{24.2}
$$

因此，删去 [中央续卷197.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md) 的 $z\circ r=0$ 后，仅由上述两个交换关系及全态定表预算，既不能推出零误差下 $r=0$，也不能推出 $\|r\|^2\le\varepsilon$。这是固定表子系统的反例，不是定义在全部原域上的 $D$，不声称满足完整原PB。

证明。取 $\eta=(1-i)/\sqrt2$，明确令

$$
\begin{gathered}
h=\operatorname{diag}(1,1,-1,-1),\qquad
c=\operatorname{diag}(1,-1,-1,1),\qquad r=c/16,\\
x=\begin{pmatrix}
1&0&1&\eta\\
0&-1&\eta&1\\
1&\bar\eta&-1&0\\
\bar\eta&1&0&1
\end{pmatrix}.
\end{gathered}
\tag{24.3}
$$

这里的 $c$ 确为24.1的偶部分，$h,x,r$ 自伴且所需两个交换关系成立。为完整证明全部态预算，以下保留所有非交换项，给出整个实参数平面的解析正性证书。

写标准Pauli矩阵为 $X,Y,Z$，置 $U=Y$、$V=(Y-X)/\sqrt2$、$C=Z\otimes Z$。则

$$
\begin{gathered}
UV=(I+iZ)/\sqrt2,\qquad VU=(I-iZ)/\sqrt2,\qquad U^2=V^2=I,\\
h=Z\otimes I,\quad c=C,\quad k=I\otimes Z,\\
z=X\otimes I+(X+Y)\otimes X/\sqrt2,\qquad
t=-U\otimes I-V\otimes X,\quad r=\rho C,
\end{gathered}
\tag{24.4}
$$

最终取 $\rho=1/16$。先置 $A=hx=k-it$；准确乘法给

$$
\begin{aligned}
A^*A=x^2&=3I+\sqrt2\,I\otimes X-2V\otimes Y,\\
A^2&=-I-\sqrt2\,I\otimes X+2iU\otimes Z.
\end{aligned}
\tag{24.5}
$$

$x^2$ 的两个非标量项反交换，平方之和为 $6I$，所以 $x^2\ge(3-\sqrt6)I>0$。$A^2+I$ 的平方为 $-2I$，且 $\operatorname{Tr}A=\operatorname{Tr}A^3=0$、$\operatorname{Tr}A^2=\operatorname{Tr}A^4=-4$。Newton恒等式遂给

$$
f(\zeta):=\det(A-\zeta I)=\zeta^4+2\zeta^2+3.
\tag{24.6}
$$

任取实 $p,q$，记 $s=p^2+q^2$、$d=s+3$ 及

$$
\begin{gathered}
H=(A-(p-iq)I)^*(A-(p-iq)I)=dI+N,\\
N=\sqrt2 F-2G-2pK_0+2qL+2qM,\\
F=I\otimes X,\quad G=V\otimes Y,\quad K_0=I\otimes Z,\quad
L=U\otimes I,\quad M=V\otimes X,\\
P_\rho(p,q)=H-2q\rho C
=x^2+(p^2+q^2)I-2pk-2qg.
\end{gathered}
\tag{24.7}
$$

下面的行列式等式包含全部参数和全部交叉项：

$$
\begin{aligned}
\det P_\rho(p,q)
={}&|f(p-iq)|^2+64\rho q^2\\
&-8\rho^2q^2\bigl[(s+3)^2+4p^2+2\bigr]+16\rho^4q^4.
\end{aligned}
\tag{24.8}
$$

为逐项核对该等式，$C$ 共轭 $F,G,K_0,L,M$ 的符号依次为 $(-,+,+,-,+)$。Pauli迹正交性给

$$
\operatorname{Tr}(CH)=0,\quad
\operatorname{Tr}((CH)^2)=4(d^2+4p^2+2),\quad
\operatorname{Tr}(CN^2)=0.
\tag{24.9}
$$

$\operatorname{Tr}(CN^3)$ 中只有 $F,G,L$ 的六个排列有贡献。它们的未带系数乘积之和为 $i(UV-VU)\otimes Z=-\sqrt2 C$，乘共同系数 $\sqrt2(-2)(2q)$ 后为 $8qC$。故

$$
\operatorname{Tr}(CH^2)=0,\quad
\operatorname{Tr}(CH^3)=32q,\quad
\operatorname{Tr}(C\operatorname{adj}H)=-32q.
\tag{24.10}
$$

最后一式用四阶伴随矩阵的特征多项式表达，其他含 $C$ 的低次迹均为零。由 $C^2=I,\det C=1$，四次行列式的常数、一次、二次、三次及四次系数分别确定为

$$
\det(H-\delta C)
=\det H+32q\delta-2(d^2+4p^2+2)\delta^2+\delta^4.
\tag{24.11}
$$

其中二次系数是 $\bigl[(\operatorname{Tr}CH)^2-\operatorname{Tr}((CH)^2)\bigr]/2$，三次系数为 $-\operatorname{Tr}(CH)=0$。代入 $\delta=2q\rho$ 及 $\det H=|f(p-iq)|^2$，得到24.8。

现固定 $\rho=1/16$。当 $0\le s\le6$，有 $(s+3)^2+4p^2+2\le s^2+10s+11\le107$。在24.8只丢掉非负的四次项，得

$$
\det P_{1/16}(p,q)
\ge |f(p-iq)|^2+\frac{21}{32}q^2>0.
\tag{24.12}
$$

$q=0$ 时严格性来自 $f(p)=p^4+2p^2+3>0$。当 $s\ge6$，有 $|f(p-iq)|\ge s^2-2s-3\ge s^2/2$、$(s+3)^2+4p^2+2\le3s^2$ 和 $q^2\le s$，故

$$
\det P_{1/16}(p,q)
\ge\frac{s^4}{4}-\frac{3s^3}{32}>0.
\tag{24.13}
$$

整个实参数平面上的 $P_{1/16}$ 均为连续Hermitian非奇异矩阵，而 $P_{1/16}(0,0)=x^2>0$。沿原点到任意参数点的线段，惯性若改变便须出现零特征值；24.12–24.13排除了这一点。因此 $P_{1/16}(p,q)>0$ 对全部实 $p,q$ 成立。对任意归一数学态取 $p=\varphi(k)$、$q=\varphi(g)$，读取同一个正铅笔便得24.2的严格预算。最后24.4直接给

$$
z\circ r=-\frac1{16}V\otimes Y,\qquad
r^2=(z\circ r)^2=I/256,
\tag{24.14}
$$

从而全部反例条件均在同一张固定表中成立。若原正泛函 $\alpha$ 的质量为 $m=\alpha(I)>0$，取 $\varphi=\alpha/m$，24.2乘以 $m^2$ 给 $\alpha(g)^2+\alpha(k)^2<m\alpha(x^2)$；质量为零时 $\alpha=0$，相应非严格P2为等号。∎

## 25. 原配平生产与定表反例的不同范围

**定义 25.1（来源与准确排除项）。** 24.1归为 $\texttt{repo-derived}$。新增承重是同一四阶复表、24.8的完整行列式证书及整个参数平面的正性。Pauli乘法与迹正交性、Newton和伴随矩阵恒等式、Hermitian惯性连续性、全部态分离正锥以及实均值平方配方是成熟中间工具，不各立为新结果；没有文献穷尽或历史优先权声称。

Magajna，[*Variance of operators and derivations*](https://arxiv.org/html/1302.1958v2)，Theorem3.5及Corollary3.6要求主算子正规，并要求全部向量态或全部态上的算子方差支配，再取得Lipschitz函数演算。此处 $A=hx$ 满足 $A^*A-AA^*=-4V\otimes Y\ne0$，且 $|\varphi(A-ir)|^2\le\varphi(A^*A)$ 并非该方差支配；不能直接套用该文结论消去余量。24.1更直接证明这个指定定表结论为假，而不否定文献定理。

[中央续卷178.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md) 已有全态P2容许非零余量的孤立表，但其背景与余量不交换。24.1同时保留 $[h,r]=[c,r]=0$，排除的是这两个交换关系加全态定表P2仍足以取代197.1交叉反交换前件的更强断言；不将既有局部预算反例另计为新内容。

中央续卷197.1在另外支付 $z\circ r=0$ 后给锐界，其前提没有被24.1满足。完整原候选仍为中央续卷196.1的A1–A3、准确原锥与全部原正读取、全部P2和完整PB；24.1没有定义总 $D$，也没有验证任何完整PB族，不是该候选的反模型。原域、原输出、同一读取和实际共享关系不能被这张孤立表替换。一般原值识别、旧双线性、有限复Gram、原R、结合乘法及完成运输各守已付原范围和未付接口，独立公理数未由本反例减少。

中央续卷199.2的七项原来源合同及全部上游量词原样保留：实际Hilbert与相干准备；原态效果、零及非归一质量和完整Born菜单；真正相关联合与张量；typed CP、Kraus与递归同源参考；整台仪器、环境全部输出与更新；全部历史未来、泄漏、真实双向返回和CountRead；保持原域的动力、正常性与前对偶、物理钟、能量和共同正 $\hbar$。所有原 $\Omega/\mathrm{native}$、全词、共同根、真实支持与完整接线不变。固定数学态、矩阵相位与复参数均不供应这些物理来源。

## 26. 四条交叉连线为何容许定表余量

**定义 26.1（完整白话）。** 同一原候选的两两有向正比较、相加三角、单位小窗和完整正反配平仍全部保留。这里单独取出一张二元表，严格检查它究竟能排除多少可能：余量与原轴、交换背景都交换，所有数学读取也都还有正的比较预算，余量却确实非零。四阶表的交叉连线绕一圈带有相位 $i$；完整行列式把这一取向、全部读数和全部参数一起保留，证明这份余量没有破坏孤立二表的正性。因此“所有读取都正”不能直接代替不同原比较之间的共同配平。这个例子没有造出一张满足完整原公理的总响应表；它排除的是删掉交叉关系后仅凭定表正性的证明路线。比较的等价重组仍需真实共享关系，实际测量先后也仍可有影响，全部七项真实量子来源并未由四阶图画取得。

## 追加锚（本行以下为增补区）

## 27. 两根实际轴的重接消去同时三种偏置的余量

**定理 27.1（带单位偏置的完整反射混合行）。** 保持[中央续卷196.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md) 的完整原候选、182.1–182.2的实际 $h,e,j,s,H,Q$ 和199.2全部七项原来源合同。对全部实 $R,\mu,\lambda,\nu$ 及任意原 $h$-奇 $z$，准确有

$$
\boxed{D(Rh,\mu u+\lambda h+\nu s+z)=R\,iQhz
       =R\,D(h,\mu u+\lambda h+\nu s+z).}
\tag{27.1}
$$

不要求 $z$ 为纯 $s$-奇偶，不要求 $z^2$ 中央、可逆或有限谱，不增加旧 $D$ 的可加、齐次、连续、单位平移或商下降。原域、准确锥、全部原正读取及全部质量、A1–A3、全部P2和完整PB保持不变。

证明。$R=0$ 由原零输入P2成立；$\nu=0$ 直接复用中央续卷166.1。以下 $R\nu\ne0$，保持同一实际输入和输出，定义

$$
c=\mu u+\lambda h+\nu s,\quad x=c+z,\quad
k=hc=\mu h+\lambda u+\nu H,\quad
t=iQhz,\quad g=D(Rh,x)=Rt+r.
\tag{27.2}
$$

中央续卷163.1给 $[h,r]=0$；不能在此调用只对 $\mu=0$ 支付的192.1。记 $P_a^\pm(y)=(y\pm aya)/2$，$r_{\rm o}=P_s^-r$。$h,s$ 交换，故其有限奇偶投影交换，且 $r_{\rm o}$ 仍为 $h$-偶。

先对任意实 $\alpha,\beta$ 调用实际PB $(Rh,x,Rk+\beta h+\alpha u)$。中央续卷189.1给内值 $D(Rh,Rk+\beta h+\alpha u)=0$；完整位移和两份外层为

$$
\begin{gathered}
v=g-R^2c-R\beta u-R\alpha h,\qquad w=Rk,\\
A_+=(1-R^2)c+z+g-R\beta u-R\alpha h,\quad
B_+=2Rk+\beta h+\alpha u,\\
A_-=(1+R^2)c+z-g+R\beta u+R\alpha h,\quad
B_-=\beta h+\alpha u.
\end{gathered}
\tag{27.3}
$$

只展开已知Jordan乘法，利用 $x\circ h=k$、$h\circ k=c$、$k^2=c^2$，得到准确差值

$$
D(A_+,B_+)-D(A_-,B_-)=K+2R\beta z,\qquad
K=-2x\circ g+2R^2z\circ c.
\tag{27.4}
$$

取 $\beta=-2R\mu$，则 $B_+=(2R\lambda+\alpha)u+2R\nu H$，而 $B_-=\beta h+\alpha u$。置真正原输出 $W_\alpha=D(B_-,A_-)$。原反对称性把27.4改写成

$$
-D(B_+,A_+)+W_\alpha=K+2R\beta z.
\tag{27.5}
$$

中央续卷163.1在实际第二框架 $(H,e,sj)$ 上给 $P_H^-D(B_+,A_+)=2R\nu iQH P_H^-A_+$。$A_+$ 的 $h$-偶、$s$-奇部分恰是 $r_{\rm o}$，所以其对应输出投影为 $2R\nu iQH r_{\rm o}$。另一方面，$z,t$ 为 $h$-奇且 $z\circ t=0$，故 $P_h^+K=-2c\circ r$，其 $s$-奇部分是 $-2(\mu u+\lambda h)r_{\rm o}$；这里 $s\circ r_{\rm o}=0$，只用了 $[h,r]=0$。因此27.5给

$$
P_h^+P_s^-W_\alpha
=2\bigl[R\nu iQH-(\mu u+\lambda h)\bigr]r_{\rm o}
=:L,
\tag{27.6}
$$

右侧与 $\alpha$ 无关；没有声称整个 $W_\alpha$ 不变。

对 $\epsilon=\pm1$ 置数学投影 $p_\epsilon=(u+\epsilon h)/2$，在27.3–27.6选择 $\alpha_\epsilon=-\epsilon\beta$。于是 $B_-p_\epsilon=p_\epsilon B_-=0$。对任意环境正泛函 $\omega$，合法原正读取 $\phi_\epsilon(a)=\omega(p_\epsilon a p_\epsilon)$ 在实际表 $(B_-,A_-,W_{\alpha_\epsilon})$ 的第一平方上为零；P2和正泛函分离给 $p_\epsilon W_{\alpha_\epsilon}p_\epsilon=0$。因 $p_\epsilon$ 与 $s$ 交换，对此式取 $s$-奇投影，27.6便给 $p_\epsilon Lp_\epsilon=0$。$L$ 为 $h$-偶，两符号合起来得 $L=0$。这一步消去的是同一固定投影值，不是在角上定义新响应。

令 $T_0=\mu u+\lambda h$。$T_0$ 与 $Q,H$ 交换，且 $(iQH)^2=-u$；从27.6的 $L=0$，在环境中左乘 $-R\nu iQH-T_0$，得到

$$
\bigl[(R\nu)^2u+T_0^2\bigr]r_{\rm o}=0.
\tag{27.7}
$$

再左乘 $p_\epsilon$，系数为严格正实数 $(R\nu)^2+(\mu+\epsilon\lambda)^2$，所以 $p_\epsilon r_{\rm o}=0$，即 $r_{\rm o}=0$。从而 $[s,r]=[c,r]=0$。所有除法只对所写严格正实数进行；不引入原逆元。

再取27.3的 $\beta=0$。中央续卷161.5消去第二外层 $D(A_-,\alpha u)$，故对全部实 $\alpha$，同一个实际原输出满足 $D(A_+,2Rk+\alpha u)=K$。四个数学联合投影和偏移取为

$$
q_{\epsilon,\delta}=\tfrac14(u+\epsilon h)(u+\delta s),\qquad
\alpha_{\epsilon,\delta}
=-2R(\mu\epsilon+\lambda+\nu\epsilon\delta),
\qquad \epsilon,\delta\in\{1,-1\}.
\tag{27.8}
$$

第二输入在对应角上归零。与前面相同的合法正读取和P2给 $q_{\epsilon,\delta}Kq_{\epsilon,\delta}=0$。此时 $c,r$ 都与 $h,s$ 交换，且 $z\circ t=0$，故27.4中除 $-2cr$ 外的项均为 $h$-奇；四角压缩消去它们，却完整保留 $cr$。因此

$$
0=\sum_{\epsilon,\delta}q_{\epsilon,\delta}Kq_{\epsilon,\delta}=-2cr.
\tag{27.9}
$$

最后消费中央续卷176.1–176.3的同一支撑机制，保留当前强度。实际PB $(x,Rh,0)$ 准确给

$$
D(Rh-g,Rk)-D(Rh+g,-Rk)=2Rhr.
\tag{27.10}
$$

同一个正读取对两张实际表使用P2及三角不等式，约去非零 $R$ 的显式平方因子，得到

$$
|\phi(hr)|^2\le\phi(c^2)\,[R^2\phi(u)+\phi(g^2)].
\tag{27.11}
$$

这是176.5相同的两根式估计，不假定 $D$ 的强度齐次。对任意环境归一数学态 $\omega$ 取 $\phi(a)=\omega(rar)$；27.9给 $rc^2r=(cr)^*(cr)=0$，所以27.11迫使 $\omega(hr^3)=0$。这些态分离固定自伴元素，结合 $[h,r]=0$ 及 $h^2=u$ 给 $hr^3=0$、$r^3=0$，自伴性遂给 $r=0$；不要求任何算子代数意义的正常性，也未除以读取质量。取 $R=1$ 再得27.1第二等号。零角、零质量、负系数、$\mu=0$、退化联合角及非完备无限原域均已包含。∎

## 28. 两轴投影与共同四角输出的准确范围

**定义 28.1（来源与剩余桥）。** 本组归为 $\texttt{repo-derived}$。中央续卷163.1供应仿射首标签的奇投影，189.1供应内交换零值，161.5供应单位零行，176.1–176.3供应余量支撑消费者，182.2供应第二实际框架。新增承重是27.3–27.7：保留非零第二外值，把一份实际PB的两端放在不同已知轴上，使它的同一有限投影值不随单位偏移变化，再由两个第一平方零角消去该值，真正生产带单位背景的 $[s,r]=0$。随后27.8–27.11用原共同输出排除余量。数学压缩保正、正泛函分离及有限对合奇偶是成熟C*工具，出处保持中央续卷185.3、199.1的Blackadar来源，不各立为新发现。

27.1将中央续卷201.1的完整混合行扩到单位、原轴及反射偏置同时非零，并复用166.1的无反射分支；不把两条旧行相加，也不改写既有条目。没有历史优先权或文献穷尽声称。完整原候选及独立公理数不变；一般 $h$-交换背景、任意首标签、全域旧双线性、有限旧复Gram、原R、同一结合乘法及完成运输仍须原桥。尤其没有支付任意额外 $hs$ 系数或任意谱函数，也没有要求 $X=\mathcal A_{\rm sa}$ 或原域谱完备。

中央续卷199.2全部七项同源合同及上游量词保持：原 $\Omega/\mathrm{native}$、全词、具名合法控制与实际相干准备；原事件、准确效果、零及非归一质量和实际完整Born菜单；共同真实相关联合、张量及递归参考；typed CP、Kraus及每个有限递归深度的同源接线；整台仪器、环境全部成功失败细记录及输出未来、TP与更新；全部合法历史未来、泄漏、停止销毁、真遗忘、同数真实双向返回和CountRead，所需可数可加、正常性及指定前对偶；保持可能不完备原域的动力、真实相位、物理钟、生成元域、能量和共同正 $\hbar$。数学投影与正读取均不新增物理准备、系统、箭头或时间尺度。

## 29. 两种比较接法共同认回跨角连线的白话

**定义 29.1（完整候选与实际简化）。** 同一个世界仍用两两有向正比较、相加三角、单位小窗及完整正反配平，没有增加线性或实际测量换序公理。给输入同时加入单位、原轴和一面实际反射的偏置，原先不知道余量会不会跨过反射两侧。现在同时移动第三标签的单位和原轴分量，让同一次配平的两端分别落在两根已经认识的实际轴上。第二根轴给出一份确定的投影值，第一根轴上的未知输出必须认回它；这一份投影值在两种偏移下不变，而两次读取各让一个角没有第一平方预算，于是它只能为零。跨反射的余量被排除后，四个联合角的读取才完整约束剩余余量与背景的乘积；同一原支撑配平再消去余量。因此三种偏置可以同时存在，横向两种反射成分也可以混合，不再额外要求余量与反射交换。减少的是这整个原分支的一项未付证明，独立公理数没有减少。这里的角是数学读取窗口，等价比较重组保持一致仍不要求实际仪器先后可交换；七项真实量子来源继续逐项守28.1的同一原合同。

## 追加锚（本行以下为增补区）

## 30. 完整四角背景上的原横向响应

**定理 30.1（任意四角背景的完整原行）。** 保持27.1的同一完整原候选、实际框架 $h,e,j,s,H=hs,Q$ 及28.1全部七项原来源合同。对任意原 $c\in\operatorname{span}_{\mathbb R}\{u,h,s,H\}$、任意原 $h$-奇 $z$ 及任意实 $R$，准确有

$$
\boxed{D(Rh,c+z)=R\,iQhz=R\,D(h,c+z).}
\tag{30.1}
$$

四个背景系数均可任意；不排除任何零角、整角零背景、退化或负参数。不增加原响应的可加、齐次、连续、商下降或一般单位平移前提。

证明。$R=0$ 由原零输入P2成立。以下 $R\ne0$，写

$$
\begin{gathered}
c=\mu u+\lambda h+\nu s+\xi H,\quad x=c+z,\quad
k=hc=\mu h+\lambda u+\nu H+\xi s,\\
t=iQhz,\quad g=D(Rh,x)=Rt+r,\quad [h,r]=0,\quad
r_{\rm o}=P_s^-r.
\end{gathered}
\tag{30.2}
$$

分解和 $[h,r]=0$ 只用中央续卷163.1，尚未假定 $[s,r]=0$。所有 $P_a^\pm$ 沿27.1的有限奇偶定义。

在实际PB中取 $(Rh,x,Rk+\beta h+\gamma s+\zeta H+\alpha u)$。第三标签与 $h$ 交换，中央续卷189.1给内值零。完整位移和两份实际外层为

$$
\begin{gathered}
v=g-R^2c-R\beta u-R\gamma H-R\zeta s-R\alpha h,\qquad w=Rk,\\
A_+=(1-R^2)c+z+g-R\beta u-R\gamma H-R\zeta s-R\alpha h,\\
A_-=(1+R^2)c+z-g+R\beta u+R\gamma H+R\zeta s+R\alpha h,\\
B_+=2Rk+\beta h+\gamma s+\zeta H+\alpha u,\qquad
B_-=\beta h+\gamma s+\zeta H+\alpha u.
\end{gathered}
\tag{30.3}
$$

由 $x\circ h=k$、$h\circ k=c$、$s\circ k=Hc$、$H\circ k=sc$ 和 $k^2=c^2$，只展开已知Jordan乘法，准确有

$$
\begin{gathered}
D(A_+,B_+)-D(A_-,B_-)
=K+2R\beta z+2R\gamma(z\circ H)+2R\zeta(z\circ s),\\
K=-2x\circ g+2R^2z\circ c.
\end{gathered}
\tag{30.4}
$$

固定 $\beta=-2R\mu$、$\gamma=-2R\xi$，仍让 $\alpha,\zeta$ 为实数。于是 $B_+=(2R\lambda+\alpha)u+(2R\nu+\zeta)H$。置真正原输出 $W_{\alpha,\zeta}=D(B_-,A_-)$，保留30.4中的非零负外值。中央续卷163.1在同一实际 $H$ 框架上供应正外值的奇投影。$A_+$ 的 $h$-偶、$s$-奇部分为 $r_{\rm o}$，而30.4新增的三个偏移项均为 $h$-奇。又由 $z\circ t=0$ 得 $P_h^+K=-2c\circ r$；其 $s$-奇部分为 $-2(\mu u+\lambda h)r_{\rm o}$，因为 $s\circ r_{\rm o}=H\circ r_{\rm o}=0$。原反对称性遂给

$$
P_h^+P_s^-W_{\alpha,\zeta}
=\bigl[(2R\nu+\zeta)iQH-2(\mu u+\lambda h)\bigr]r_{\rm o}
=:L_\zeta.
\tag{30.5}
$$

这里只说该投影与 $\alpha$ 无关，不说整个输出不变，也不说它与 $\zeta$ 无关。

对每个 $\epsilon=\pm1$，取数学投影和实际实参数

$$
p_\epsilon=(u+\epsilon h)/2,\qquad
\alpha_\epsilon=2R\mu\epsilon,\qquad
\zeta_\epsilon=2R\xi\epsilon.
\tag{30.6}
$$

由 $Hp_\epsilon=\epsilon sp_\epsilon$，30.3准确给 $B_-p_\epsilon=p_\epsilon B_-=0$。任意环境正泛函 $\omega$ 的合法原正读取 $\phi_\epsilon(a)=\omega(p_\epsilon a p_\epsilon)$，在实际 $(B_-,A_-,W_{\alpha_\epsilon,\zeta_\epsilon})$ 表的第一平方为零；P2及正泛函分离给该输出的 $p_\epsilon$ 压缩为零。$p_\epsilon$ 与 $s$ 交换，取 $s$-奇投影后，由30.5得到

$$
\bigl[R(\nu+\epsilon\xi)iQH-(\mu+\epsilon\lambda)u\bigr]
p_\epsilon r_{\rm o}=0.
\tag{30.7}
$$

左乘相应的共轭因子，使用 $(iQH)^2=-u$，得

$$
d_\epsilon p_\epsilon r_{\rm o}=0,\qquad
d_\epsilon=(\mu+\epsilon\lambda)^2+R^2(\nu+\epsilon\xi)^2\ge0.
\tag{30.8}
$$

若 $d_\epsilon>0$，直接得 $p_\epsilon r_{\rm o}=0$。若 $d_\epsilon=0$，由于 $R\ne0$，两个实平方分别为零，故

$$
cp_\epsilon=
\bigl[(\mu+\epsilon\lambda)u+(\nu+\epsilon\xi)s\bigr]p_\epsilon=0,
\qquad kp_\epsilon=0.
\tag{30.9}
$$

此时不除以失效系数，而使用同一实际支撑PB $(x,Rh,0)$：

$$
D(Rh-g,Rk)-D(Rh+g,-Rk)=2Rhr.
\tag{30.10}
$$

两张实际外表的第二输入都在 $p_\epsilon$ 上归零。同一个 $\phi_\epsilon$ 分别使用P2，使两个实际输出的 $p_\epsilon$ 压缩均为零；压缩30.10便给 $2R\epsilon p_\epsilon rp_\epsilon=0$。因此 $p_\epsilon r=0$，再取 $s$-奇投影得到 $p_\epsilon r_{\rm o}=0$。这里仅用了 $d_\epsilon=0\Rightarrow cp_\epsilon=0$；不要求反向成立，也不要求两种 $s$-角都非零。两个符号共同给 $r_{\rm o}=0$，故 $[s,r]=[H,r]=[c,r]=0$。

现在在30.3取 $\beta=\gamma=\zeta=0$。中央续卷161.5消去负外层 $D(A_-,\alpha u)$，所有实 $\alpha$ 的同一个实际旧输出均为 $D(A_+,2Rk+\alpha u)=K$。定义

$$
q_{\epsilon,\delta}=\tfrac14(u+\epsilon h)(u+\delta s),\qquad
\alpha_{\epsilon,\delta}
=-2R(\mu\epsilon+\lambda+\nu\epsilon\delta+\xi\delta).
\tag{30.11}
$$

第二输入在对应联合角上归零，故合法正读取和P2给 $q_{\epsilon,\delta}Kq_{\epsilon,\delta}=0$。$cr$ 已与 $h,s$ 交换，30.4的 $K$ 除 $-2cr$ 外均为 $h$-奇，因此四角压缩相加准确给 $cr=0$。没有由四个对角读取推出任意非对角元素为零；保留全乘积的依据是先已生产的共同交换关系。

最后消费中央续卷176.1–176.3在27.10–27.11已经写明的同一强度支撑机制：30.10的两份P2给 $|\phi(hr)|^2\le\phi(c^2)[R^2\phi(u)+\phi(g^2)]$。取 $\phi(a)=\omega(rar)$，$cr=0$ 使右侧为零，所有环境归一数学态遂有 $\omega(hr^3)=0$。态分离固定自伴元素、$h^2=u$ 及自伴性给 $r=0$。整个证明未除以读取质量，未要求态正常，未限制横向平方、维数、可分性或原域完备性。取 $R=1$ 得30.1第二等号，所有分支共同完成证明。∎

## 31. 四角背景的几何与准确来源

**定义 31.1（有限背景与新增承重）。** 任意实函数 $f$ 在四个可能联合符号 $(\epsilon,\delta)$ 上给定的背景，均可写为 $c=\sum_{\epsilon,\delta}f(\epsilon,\delta)q_{\epsilon,\delta}\in\operatorname{span}_{\mathbb R}\{u,h,s,H\}$；相应背景值为 $f(\epsilon,\delta)=\mu+\epsilon\lambda+\delta\nu+\epsilon\delta\xi$。这是两根交换对合的成熟有限谱分解，不把四角当作四个物理系统，也不生成任意新原谱标签。30.1因此识别同一原轴在完整四角背景上的横向响应，允许四个角上的背景值独立；原角可能为零。

本组归为 $\texttt{repo-derived}$。新承重是30.3–30.9中额外的原 $H$ 偏移，它保持正外层在已知第二轴上，又在选定的整个第一轴角内抵消另一反射项。系数失效时，30.9–30.10将同一角接回原支撑PB，消除非退化条件；不把“系数为零”解释成原响应不受约束。27.1、中央续卷163.1、161.5、189.1及176.1–176.3是已付前置。投影压缩保正、正泛函分离、有限奇偶与有限谱分解是成熟C*工具，准确沿28.1及中央续卷185.3、199.1的Blackadar来源复用，不各立为新发现；没有历史优先权或文献穷尽声称。

完整原候选及独立公理数不变。一般 $h$-交换背景不必属于这份四角背景代数；任意首标签、全域旧双线性、全部有限旧复Gram、原R、同一结合乘法和原完成运输仍须各自原桥。28.1及中央续卷199.2全部七项同源合同和上游量词继续保持：原 $\Omega/\mathrm{native}$、全词、合法控制及实际相干准备；原事件、效果、全部质量和完整Born菜单；真实相关联合、张量及递归参考；typed CP、Kraus和全部有限递归深度的同源接线；整台仪器、环境全部成功失败细记录、所有输出未来及更新；全部合法历史未来、泄漏、停止销毁、真遗忘、同数真实双向返回、CountRead及所需可数可加、正常性和指定前对偶；保持可能不完备原域的动力、真实相位、物理钟、生成元域、能量和共同正 $\hbar$。有限角与数学读取不替代任何实际来源。

## 32. 背景在一整角消失时仍没有额外自由度的白话

**定义 32.1（同一候选的完整四角图景）。** 原来的两两有向正比较、相加三角、单位小窗及完整正反配平全部保留。两根交换的两面反射给出一个四角方形；现在四个角上的背景高低可以各自独立，横向连线也可以同时跨越不同反射方向。给第三个实际标签再加一份已有的两轴乘积偏移，便能让同一次配平的一端仍落在已知第二轴上，另一端在选定的整个第一轴半边没有平方预算。这排除通常会留下的跨反射余量。若消元系数恰好为零，背景就在那个完整半边消失；原支撑配平的两张外表也因此同时没有第二平方预算，直接排除该半边的整份余量。两种情形共同覆盖四角背景，不再需要非退化条件。余量与两根反射都交换后，共同旧输出的四角读取和已有支撑关系完成排零；没有把不同输入的响应相加。减少的是完整四角分支的一份未付证明，独立公理数没有减少。方形描述关系的有限几何，等价比较重组一致仍允许实际仪器的先后有影响；一般背景和七项真实量子来源继续守31.1的原合同。

## 追加锚（本行以下为增补区）
