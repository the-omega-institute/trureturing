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
