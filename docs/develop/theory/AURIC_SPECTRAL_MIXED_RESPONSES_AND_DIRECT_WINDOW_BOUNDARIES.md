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

## 33. 逐对角读取识别任意有限分割背景的原行

**定理 33.1（有限共同分割的完整原响应）。** 保持30.1的同一完整原候选、实际 $h,e,j,Q$ 及31.1全部七项原来源合同。给定任意有限原投影分割

$$
p_a\in E,\qquad p_a^2=p_a,\qquad
p_ap_b=0\ (a\ne b),\qquad \sum_{a=1}^m p_a=u,\qquad
[p_a,h]=[p_a,e]=0,
\tag{33.1}
$$

其中 $m\ge1$，允许零投影。对任意实 $\mu_a,\lambda_a,R$、任意原 $h$-奇 $z$，置 $c=\sum_a(\mu_a u+\lambda_a h)p_a$，则

$$
\boxed{D(Rh,c+z)=R\,iQhz=R\,D(h,c+z).}
\tag{33.2}
$$

不要求不同格子的背景值相同，不排除零值或重值；不增加旧响应的线性、连续性、谱延拓或商下降。

证明。所有所列乘积都是交换原元素的Jordan乘积，故 $c$ 为原标签。$R=0$ 用P2。以下 $R\ne0$，置 $x=c+z$、$k=hc$、$t=iQhz$、$g=D(Rh,x)=Rt+r$。中央续卷163.1给 $[h,r]=0$；尚未取得 $[p_a,r]=0$。定义原数学联合角

$$
q_{\epsilon,a}=\tfrac12(u+\epsilon h)p_a,\qquad
v_{\epsilon,a}=\mu_a+\epsilon\lambda_a,
\qquad \epsilon\in\{1,-1\}.
\tag{33.3}
$$

这些角正交且和为 $u$，并有 $cq_{\epsilon,a}=v_{\epsilon,a}q_{\epsilon,a}$、$kq_{\epsilon,a}=\epsilon v_{\epsilon,a}q_{\epsilon,a}$。不同 $h$ 符号之间的 $r$ 块已经为零。现固定同一个 $\epsilon$ 和两个不同格子 $a,b$，简写 $v_a=v_{\epsilon,a}$、$v_b=v_{\epsilon,b}$、$q_a=q_{\epsilon,a}$、$q_b=q_{\epsilon,b}$。取同一原域内的实际反射及实系数

$$
s=u-2p_a,\quad H=hs,\quad
A=R\epsilon(v_a+v_b),\quad B=R(v_b-v_a),\quad
T=Au+BH,\quad V=T-2Rk.
\tag{33.4}
$$

$s^2=u$ 且 $s$ 与 $h,e,c$ 交换，中央续卷182.2因此给实际 $H$ 框架及同一个 $Q$。在 $q_a$ 上 $s=-u$，在 $q_b$ 上 $s=u$，故 $Vq_a=Vq_b=q_aV=q_bV=0$。

对实际PB $(Rh,x,T-Rk)$，第三标签与 $h$ 交换，中央续卷189.1给内值零。完整两份实际外层是

$$
\begin{gathered}
A_+=x+g+R^2c-RhT,\qquad A_-=x-g-R^2c+RhT,\\
B_+=T,\qquad B_-=V,\\
D(A_+,T)-D(A_-,V)
=J,\qquad
J=-2x\circ g-2R^2z\circ c+2Rz\circ(hT).
\end{gathered}
\tag{33.5}
$$

这里仅展开已知Jordan乘法：$h\circ x=k$、$k^2=c^2$、$[c,T]=0$，所有含 $cT$ 的项抵消；$P_h^+J=-2c\circ r$，因为 $z\circ t=0$，其余 $z$ 项均为 $h$-奇。

置同一实际旧输出 $W=D(V,A_-)$。对 $q=q_a+q_b$，合法原正读取 $\phi(y)=\omega(qyq)$ 在实际表 $(V,A_-,W)$ 的第一平方为零。P2及正泛函分离给 $qWq=0$，特别 $q_aWq_b=0$。另一方面，中央续卷163.1在实际 $H$ 框架上给 $P_H^-D(T,A_+)=B iQH P_H^-A_+$。两端角具有相同的 $h$ 符号、相反的 $s$ 符号，故提取这份块只保留 $A_+$ 的 $h$-偶、$s$-奇部分，即 $P_s^-r$。原反对称性把33.5写成 $W-D(T,A_+)=J$，于是准确得到

$$
\bigl[iQ\epsilon R(v_a-v_b)-(v_a+v_b)u\bigr]
q_arq_b=0.
\tag{33.6}
$$

这里 $BHq_a=\epsilon R(v_a-v_b)q_a$，而 $q_a(2c\circ r)q_b=(v_a+v_b)q_arq_b$；没有使用 $[c,r]=0$。中央 $Q^2=u$ 给

$$
\bigl[(v_a+v_b)^2+R^2(v_a-v_b)^2\bigr]q_arq_b=0.
\tag{33.7}
$$

若实系数严格正，得 $q_arq_b=0$。若系数为零，$R\ne0$ 迫使 $v_a=v_b=0$，于是 $cq=kq=0$。同一实际支撑PB仍是

$$
D(Rh-g,Rk)-D(Rh+g,-Rk)=2Rhr.
\tag{33.8}
$$

两个实际第二平方在上述 $q$ 读取下均为零；P2使两份实际输出的 $q$ 压缩都为零。因 $hq=\epsilon q$，压缩33.8给 $2R\epsilon qrq=0$，特别 $q_arq_b=0$。此处理包括零角，不要求反向的非退化判据。所有同符号的不同格子对因此都为零；加上原有不同 $h$ 符号零块，得到 $[p_a,r]=0$ 对所有 $a$ 成立，继而 $[c,r]=0$。

最后对所有实 $\alpha$ 调用实际PB $(Rh,x,Rk+\alpha u)$，中央续卷161.5消去单位负外层，得到同一个实际旧输出

$$
\begin{gathered}
D\bigl((1-R^2)c+z+g-R\alpha h,\,2Rk+\alpha u\bigr)=K,\\
K=-2x\circ g+2R^2z\circ c.
\end{gathered}
\tag{33.9}
$$

对角 $q_{\epsilon,a}$ 取 $\alpha=-2R\epsilon v_{\epsilon,a}$，第二平方在该角读取下为零，P2给 $q_{\epsilon,a}Kq_{\epsilon,a}=0$。此时 $cr$ 已对整份共同分割分块对角，$K$ 的其余项均为 $h$-奇，故把全部有限角压缩相加准确给 $cr=0$。此处没有由对角读取排除任意非对角元素；非对角块已由33.6–33.8逐对支付。

33.8的两份P2及中央续卷176.1–176.3的同一根式估计，保持当前强度，给 $|\phi(hr)|^2\le\phi(c^2)[R^2\phi(u)+\phi(g^2)]$。对所有环境归一数学态 $\omega$ 取 $\phi(y)=\omega(ryr)$，$cr=0$ 给 $\omega(hr^3)=0$，态分离、自伴性及 $h^2=u$ 遂给 $r=0$。没有除以读取质量，未要求态正常或 $D$ 连续。取 $R=1$ 得33.2第二等号。∎

## 34. 任意有限交换反射的几何与来源

**定义 34.1（同一逐对关系覆盖有限方格）。** 若原 $s_1,\ldots,s_n$ 是任意有限个两两交换、且均与 $h,e$ 交换的自伴对合，则

$$
p_\sigma=2^{-n}\prod_{j=1}^n(u+\sigma_js_j),\qquad
\sigma\in\{1,-1\}^n
\tag{34.1}
$$

是33.1的原有限分割，零角允许存在。因而33.2覆盖 $h,s_1,\ldots,s_n$ 生成的整个有限实交换代数中任意背景，包括所有混合乘积系数；$n=0$ 用 $p=u$。这只是有限原Jordan多项式，未把原域外谱投影、连续谱函数或极限输入旧 $D$。30.1是两格分割 $p_\pm=(u\pm s)/2$ 的已付特例，不重计为新内容。

本组归为 $\texttt{repo-derived}$。新承重是33.4–33.8的逐对连接：每对同轴角单独选一根原反射，让同一次配平的一端处在已知实际轴，另一端在这两个角的共同读取下没有第一平方预算；由同一旧输出识别相应余量块。两背景值同时为零时原支撑PB闭合退化块。成熟有限谱分解、正压缩、正泛函分离和奇偶运算沿31.1、中央续卷185.3与199.1的Blackadar来源复用；163.1、161.5、189.1、182.2及176.1–176.3为已付原接口，没有历史优先权或文献穷尽声称。

独立公理数不变。任意有限格子的共同分割存在是本定理的明确分支资料，不由原公理推断每个背景都具有这种分割；一般 $h$-交换背景、连续谱或不能由这份共同交换分割表示的背景仍未由本组识别。也不以有限背景逼近和未知 $D$ 的连续运输补缺。任意首标签、全原双线性、全部有限旧复Gram、原R、同一结合乘法和原完成运输各守原桥。31.1及中央续卷199.2的全部七项同源合同和上游量词原样保持：原 $\Omega/\mathrm{native}$、全词、合法控制及实际相干准备；原事件效果、全部质量及完整Born菜单；真实相关联合、张量和递归参考；typed CP、Kraus及全部有限递归深度的同源接线；整台仪器、环境全部成功失败细记录、全部输出未来及更新；全部合法历史未来、泄漏、停止销毁、真遗忘、同数真实双向返回、CountRead及所需可数可加、正常性和指定前对偶；保持可能不完备原域的动力、真实相位、物理钟、生成元域、能量和共同正 $\hbar$。有限数学分格不供应这些实际物理来源。

## 35. 格子再多也只检查两两关系的白话

**定义 35.1（同一候选的有限分割图景）。** 原来的两两有向正比较、相加三角、单位小窗和完整正反配平都保留。现在两面的方形可以细分成任意有限多个格子，每个格子的背景高低各自独立。处理格子之间的余量时，每次只挑同一面上的两个格子，沿其中一个格子画一面已有的反射，再调两份普通实数偏移，让这两个格子共同没有第一平方预算；另一端仍沿一根已经认识的实际轴，因此两种比较必须认回同一个跨格结果。除非两个背景同时为零，这就排除该跨格余量；同时为零时，原支撑配平直接排除它。逐对连接以后，全部余量才与共同分格相容，各格读取和原支撑关系完成排零。格子数增加不需要新一类公理；所得结论覆盖任意有限共同分割，独立公理数仍未减少。等价有向比较重组一致继续允许实际仪器先后有影响；一般背景及七项真实量子来源仍守34.1的原边界。

## 追加锚（本行以下为增补区）

## 36. 保留全部小连接的同参照配平反向检验

**定义 36.1（完整候选与所检验的较弱接口）。** 完整候选仍取[原多项式零响应卷](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)89.1的同一原 $E,C,u,N,\mathcal P,S,D$、A1–A3、准确锥、全部质量、全部原P2及完整PB；一般原域与全部实际来源不变。本增补另给一个不满足完整PB的总映射，检验以下资料能否消去该卷93.1的全幅秩一余量：全部P2、全部共同二阶角的标准值、全部严格小连接秩一行、同一参照任意两份实倍数的整族PB，以及交换演员后的零标签与重复标签PB。这里不消费本卷27–35的额外实际全局标架。

取 $E=X=H_3(\mathbb C)$，单位、Jordan乘法、锥、范数及全部正实线性评价均为标准者，全部零、不等和次归一质量保留。记

$$
\begin{gathered}
p=E_{11},\quad q=E_{22}+E_{33},\quad X_{ij}=E_{ij}+E_{ji},\\
A=2X_{12}+q,\quad T=X_{12},\quad
0<\varepsilon\le1/\sqrt5,\quad d=\varepsilon X_{13},\\
K(x,y)=\frac i2[x,y],\quad
K_0=-\varepsilon\{2(E_{31}-E_{13})+E_{32}-E_{23}\},\quad
H_{K_0}(x,y)=\frac{xK_0y-yK_0x}{2}.
\end{gathered}
\tag{36.1}
$$

直接复用原多项式零响应卷96.2、97.2的五份正表，按下表记其实际有序基和已付输出：

$$
\begin{array}{c|c|c|c}
i&a_i&b_i&h_i\\ \hline
0&p&A&d\\
+&p-d&T&-p+d/2\\
-&p+d&-T&-p-d/2\\
s+&A+d&T&H_{K_0}(A+d,T)\\
s-&A-d&-T&H_{K_0}(A-d,-T)
\end{array}
\tag{36.2}
$$

令 $P_i=\operatorname{span}_{\mathbb R}\{a_i,b_i\}$。五个平面两两不同，每个基实线性无关，且均由实对称矩阵组成；这些事实复用该卷98.1的平面比较。对实线性无关的 $(x,y)\in P_i^2$，唯一写成

$$
\binom{x}{y}=M\binom{a_i}{b_i},\qquad M\in GL_2(\mathbb R).
\tag{36.3}
$$

定义同一个总映射 $\widetilde D:E^2\to E$：实线性相关输入取零；独立输入属于某个 $P_i^2$ 时，若 $i\ne0$，取 $(\det M)h_i$；若 $i=0$ 且 $M_{12}^2+M_{22}^2\ge1$，仍取 $(\det M)d$；其他全部输入取 $K(x,y)$。独立输入不能同时属于两个不同 $P_i^2$，所以定义单值。相关输入的标准交换子及上述行列式值也均为零，不发生交叠矛盾。

记 $\operatorname{PB}_{\widetilde D}(a;b,c)$ 为同一原PB的元素式：置

$$
v=\widetilde D(a,b)-a\circ c,\qquad
w=a\circ b+\widetilde D(a,c),
\quad
\widetilde D(b+v,c+w)-\widetilde D(b-v,c-w)
=-2b\circ v-2c\circ w.
\tag{36.4}
$$

本节保留的只是下面逐项证明的PB子族，不把它们改称完整候选。

## 37. 行列式延拓同时保住正表与全部严格小窗

**定理 37.1（同一个总映射的全部保留项）。** 定义36.1满足全部A1–A3、P2、每槽奇性、反对称性及实际 $SO(2)$ 槽旋转不变性。在每个共同秩至多二角上，$\widetilde D=K$；在全部交换输入对上也有 $\widetilde D=K=0$，故保留所有同生成元多项式零值。对任意单位向量 $e$、$r=\mu ee^*$ 及任意 Hermitian $a$，若相对 $ee^*$ 的连接向量 $z=(I-ee^*)ae$ 满足 $\|z\|<2$，则

$$
\widetilde D(r,a)=K(r,a).
\tag{37.1}
$$

与此同时，$\widetilde D(p,A)=d$ 的连接向量是 $\varepsilon e_3\notin\mathbb C(2e_2)$，且原多项式零响应卷93.1的同源预算仍取等号 $\|2e_2\|^2(1-0^2)=4$。

证明。对任意正实线性评价 $\phi$，记已知实Gram行列式

$$
\Gamma_\phi(x,y)=\phi(x^2)\phi(y^2)-\phi(x\circ y)^2.
$$

实合同的成熟二阶行列式恒等式给

$$
\Gamma_\phi\bigl(M\cdot(a_i,b_i)\bigr)
=(\det M)^2\Gamma_\phi(a_i,b_i).
\tag{37.2}
$$

36.2的五个 $h_i$ 已对全部 $\phi$ 满足原P2。因此赋值 $(\det M)h_i$ 满足同一个P2；标准分支 $K$ 的P2则直接复用该卷98.3所用的标准矩阵正表。相关输入给零预算及零输出。整个证明不除以质量。反对称性使二表Hermitian，非负对角元和以上行列式界给全部A1。A2的实相加三表及指定实零向量、A3的单位和固定有理小效果窗仍由未改的Jordan平方给出。

实正交槽变换 $O$ 保持每个实平面，且将36.3中的 $M$ 变成 $OM$；第零平面的切换量是 $M$ 的第二列长度平方，故同样不变。于是

$$
\widetilde D\bigl(O\cdot(x,y)\bigr)
=(\det O)\widetilde D(x,y)\qquad(O\in O(2)).
\tag{37.3}
$$

这同时给所列对称性；没有宣称整个总映射在任意 $GL_2$ 变换下协变。

五个基对都无共同非零核且其交换子非零，准确复用原多项式零响应卷98.3的矩阵检查。独立实换基保持共同核，并将交换子乘以非零行列式。因此修改分支既不进入共同二阶角，也不进入交换输入对，得到两项保留结论。

最后核对全部严格小连接行，不能只检查所选 $p$。平面 $P_\pm$ 的任意非零元为 $\alpha(p\mp d)+\beta T$；其从第一位置伸出的侧腿 $(\beta,\mp\alpha\varepsilon)$ 非零，所以秩为二。平面 $P_{s\pm}=\operatorname{span}_{\mathbb R}\{q\pm d,T\}$ 的元若 $q$ 系数非零，其右下二阶块已可逆；若该系数为零，则是非零 $T$，秩仍为二。因此四个辅助平面都不含非零秩一元。

第零平面的非零秩一元只能是 $\mu p$：非零的 $A$ 系数会使右下二阶块为非零标量单位。若独立有序对的首元为 $\mu p$，第二元写成 $\alpha p+\delta A$，其相对连接向量为 $2\delta e_2$，而36.1的切换量恰为 $\delta^2$。严格小窗要求 $|\delta|<1$，所以该对取标准分支。其他所有含秩一元的独立对亦取标准分支；相关对及 $\mu=0$ 取零。于是37.1对全部射线、全部幅度 $\mu$、全部背景成立。所选 $(p,A)$ 的连接长度恰为二，切换量恰为一，故仍给 $d$；两份36.2的侧面压缩均零，等号参数与原多项式零响应卷99.1相同。∎

## 38. 整条同参照配平族仍遗漏另一强度的接法

**定理 38.1（全部参照倍数和两个重复接法）。** 同一个 $\widetilde D$ 满足

$$
\operatorname{PB}_{\widetilde D}(A;sp,tp)
\qquad(s,t\in\mathbb R),
\tag{38.1}
$$

并满足 $\operatorname{PB}_{\widetilde D}(p;A,0)$ 与 $\operatorname{PB}_{\widetilde D}(p;A,A)$。特别，两个演员方向的零第三标签接法与重复第三标签接法都成立。

证明。第零平面给 $\widetilde D(A,sp)=-sd$、$\widetilde D(A,tp)=-td$，包括零系数；这里第二列长度恒为一，不随 $s,t$ 改变。因 $A\circ p=T$，38.1的准确位移为

$$
v=-sd-tT,\qquad w=sT-td.
\tag{38.2}
$$

其正、负两侧外层对分别是

$$
\begin{pmatrix}s&-t\\t&s\end{pmatrix}\cdot(p-d,T),
\qquad
\begin{pmatrix}s&-t\\t&s\end{pmatrix}\cdot(p+d,-T).
\tag{38.3}
$$

$s^2+t^2>0$ 时，定义36.1使它们的输出分别为 $(s^2+t^2)h_+$、$(s^2+t^2)h_-$。其差为 $(s^2+t^2)d$；36.4的右侧也为 $2(s^2+t^2)p\circ d=(s^2+t^2)d$。$s=t=0$ 两侧都零，故全部38.1成立。这是对明确赋值的计算，不是未知原 $D$ 的齐次性推断。

交换演员后的零第三标签给两对 $(A+d,T)$、$(A-d,-T)$，直接复用原多项式零响应卷99.3的同一赋值恒等式

$$
h_{s+}-h_{s-}=-2A\circ d.
\tag{38.4}
$$

第三标签再取 $A$ 时，两对外层分别为 $(A+d-T,A+d+T)$、$(A-d+T,A-d-T)$，恰为38.3同一个系数矩阵在 $s=t=1$ 时作用于 $(A+d,T)$、$(A-d,-T)$。两输出的差为 $2(h_{s+}-h_{s-})=-4A\circ d$，与该次PB右侧一致。∎

**定理 38.2（同一参照改换强度便有非零失败）。** 对每个实 $t$ 满足 $0<|t|<1$，同一个 $\widetilde D$ 不满足 $\operatorname{PB}_{\widetilde D}(p;A,tA)$。在质量为一的原正读取 $\phi(x)=e_1^*xe_1$ 下，36.4的左端为 $4t$，右端为零。

证明。置 $J=K(p,A)=i(E_{12}-E_{21})$。第零平面的切换量对 $(p,tA)$ 为 $t^2<1$，所以该次两个内值准确为 $d$、$tJ$，位移是

$$
v=d-tT,\qquad w=T+tJ.
\tag{38.5}
$$

两对外层为 $(A\pm v,tA\pm w)$。每个第二标签都有非零纯虚矩阵分量 $\pm tJ$，而五个 $P_i$ 都只含实对称矩阵；每个第一标签是非零实矩阵。因此外层对实线性无关且不属于任何修改平面，两个外值均准确取 $K$。只有现在才对已知 $K$ 展开，得左端

$$
2K(A,T+tJ)+2tK(d-tT,A).
\tag{38.6}
$$

实对称矩阵的交换子在第一对角的读取为零；直接矩阵乘法给

$$
\phi(K(A,J))=2,\qquad
\phi(A\circ d)=\phi(A\circ J)=0.
\tag{38.7}
$$

故38.6读成 $4t$。右端为 $-2A\circ d-2t^2A\circ J$，读取为零。例如 $t=1/2$ 的有限差分残差为二。未对总映射取极限或假定输入连续。∎

## 39. 不能用反复校准一条参照替代完整相容

**定义 39.1（新增内容、几何与完整候选）。** 本增补的 $\texttt{repo-derived}$ 承重内容是同一个带第零平面切换的总映射同时保留37.1的全部小连接公式、38.1的无限参照倍数族与两个演员方向的重复接法，却由38.2的一次有限正读取检出完整PB失败。原多项式零响应卷96–101的种子正表、平面分离、98.3的标准P2及99.3的有限矩阵恒等式直接复用；实Gram的合同协变和二阶行列式是成熟工具，不另列新公理或一般定理，不主张文献穷尽或历史优先权。原98.1的赋值只沿 $O(2)$ 轨道，原100.1的重复标签失败不适用于当前不同的总映射；本增补没有改写它的结论。 另与[原PB运输续卷](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md)103–109区分：那里保留全部秩一行，故没有这里的阈值侧向偏离；其108.3保留的“所有演员、所有重复第三标签PB是否足够”仍未解决。本增补只保留38.1及明确列出的反向接法，不把它升级为该全称命题。

37.1保留全部严格小窗而允许阈值上的全幅偏离，38.1还让同一参照的任意两份实倍数全部通过。因而把这两项资料相加，仍不能推出全幅秩一行或完整PB；也不能把38.1误读成交换演员后所有强度都通过。38.2恰用另一演员方向的小倍数与原大输入共同配平，检出跨强度的接线失败。五个实二维输入平面均处于 $H_3(\mathbb C)$ 中；这里的三是数学支撑阶数，不是物理空间维数。总映射没有被赋予连续性、一般可加性或全域齐次性。这些是纸面定义、定理与证明，未作Lean kernel核验、摄入或冻结。

完整量子候选仍是同一原二元有向正表、相加三角、单位小效果窗及全部三标签正反配平。独立公理数没有减少；一般有限商85.1的原代表不变性、一般原域分别可加与原R、全有限复Gram和完整旧乘法仍须各自证明。七项消费者完整取原多项式零响应卷87.1、95.1：同一 $\Omega/\mathrm{native}$ 与全词 $K/J/q$、parent/ready、实际准备和相干控制；原事件、效果、全部零／不等／次归一质量和完整实际Born菜单；真实相关联合、忠实同向局部腿、共同生成及递归同源参考；typed CP/Kraus与整台环境、全部成功／失败／细记录／port／post-port输出及各份输出全部合法未来；完整仪器、TP、接受端、更新、Lüders和真正分组遗忘；全部合法顺序／自适应／并行历史、泄漏、停止拒绝销毁、真实双向返回、CountRead、无限／非离散记录的可数可加、正常性与指定前对偶；保持原域的动力、真实物理钟、能量、生成元域及共同正 $\hbar$。此数学反模型不供应这些来源，也不反驳保留完整PB的候选。

**定义 39.2（完整白话）。** 候选仍要求每对有向比较为正，并让所有规定的三者接法在同一份读数里配平。反向检验先保住每个二维窗口和所有足够小的连接，再让一个参照的任意两份复制与缩放都通过；把演员交换过来，零标签和重复标签也能通过。可同一张表仍能在连接阈值处偷偷转向：换一个演员方向，把原来的大对象与它的一份小副本放在同一次配平里，一份正读取就得到不同答案。因此反复校准一条参照并未替代全部关系之间的相容；需要补的是跨演员、跨强度的真实接线，不能靠更多相同形式的检查或改名来省去。交换比较方向的符号和实际测量的先后仍分别保留，原候选及全部量子来源条件不变。

## 追加锚（本行以下为增补区）

## 40. 单个原有限谱背景与同一固定余量

**定义 40.1（完整原条件与第一实际框架）。** 完整采用[原PB运输续卷118.1–118.3](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#118-任意原偶背景第一实际框架与同一余量)的定义及其全部前件：同一原 $(E,C,u,N,\mathcal P,S,D)$、A1–A3、准确锥、分离元素且准确决定锥的全部原正实线性评价、全部零／不等／次归一质量、全部原P2和完整原PB。$E$ 为实Archimedean序单位空间。A1的两条实际有向Hermitian二表、A2的相加三表及全部排列在整个实三空间的正性和指定零二次值、A3的单位及同一固定有理小效果窗均保留。称[《中央响应平方与径向一致续卷》](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)为中央续卷。沿同一已付忠实、含单位、等距且准确保锥的JC包含，记

$$
\begin{gathered}
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E^{\|\cdot\|}=X,\qquad \mathcal A=C^*(X),\qquad
S(a,b)=a\circ b=(ab+ba)/2,\qquad C=E\cap\mathcal A_+,\quad N=\|\cdot\||_E,\\
h,e,j=D(h,e)\in E,\qquad h^2=e^2=j^2=u,\qquad
h\circ e=h\circ j=e\circ j=0,\\
Q=ihej\in Z(\mathcal A),\qquad Q^*=Q,\qquad Q^2=u.
\end{gathered}
\tag{40.1}
$$

$Q$ 不要求属于 $E$。原域可以不完备、无限维、不可分，也不要求 $X=\mathcal A_{\rm sa}$。$D:E^2\to E$ 始终是同一个原总映射；不预付一般线性、第一槽齐次、连续、可测、单位平移中性、协变、商下降、完成延拓，或原域对所选环境交换子输出的闭合。七项实际来源逐项完整取43.2。

为固定接线，原PB及其正读取写作

$$
\begin{gathered}
v=D(a,b)-a\circ d,\qquad w=a\circ b+D(a,d),\\
D(b+v,d+w)-D(b-v,d-w)=-2b\circ v-2d\circ w
\qquad(a,b,d\in E),\\
|\phi(D(a,b))|^2\le
\phi(a^2)\phi(b^2)-\phi(a\circ b)^2.
\end{gathered}
\tag{40.2}
$$

最后一式对每个原输入对及每个数学正实线性读取 $\phi$ 成立，准确沿原PB运输续卷118.2从同一原表的正性与准确锥取得。环境正泛函的压缩限制属于这种读取，不因此成为新的实际准备；不除以读取质量。

**定义 40.2（原有限谱投影与固定输出）。** 任取原 $h$-偶自伴 $c\in E$，即 $[h,c]=0$，并只假定其在同一环境中的谱有限。非零原对象上写成互异实数的集合

$$
\Lambda=\sigma_{\mathcal A}(c)=\{a_1,\ldots,a_n\},\qquad n\ge1.
$$

对每个 $a\in\Lambda$ 定义实Lagrange多项式及原联合角

$$
\begin{gathered}
f_a(t)=\prod_{\substack{b\in\Lambda\\b\ne a}}\frac{t-b}{a-b},
\qquad p_\epsilon=\frac{u+\epsilon h}{2},\\
q_{\epsilon,a}=p_\epsilon\circ f_a(c)
=\frac{u+\epsilon h}{2}
\prod_{\substack{b\in\Lambda\\b\ne a}}\frac{c-bu}{a-b},
\qquad \epsilon\in\{1,-1\}.
\end{gathered}
\tag{40.3}
$$

空乘积取 $u$。单个原元的Jordan幂和交换原元的Jordan乘积均留在 $E$，故这些是原标签。有限谱的多项式演算给出自伴投影，且

$$
\begin{gathered}
q_{\epsilon,a}q_{\delta,b}=0\quad((\epsilon,a)\ne(\delta,b)),
\qquad \sum_{\epsilon,a}q_{\epsilon,a}=u,\\
cq_{\epsilon,a}=a q_{\epsilon,a},\qquad
hq_{\epsilon,a}=\epsilon q_{\epsilon,a}.
\end{gathered}
\tag{40.4}
$$

这里只用实际 $c$ 的有限谱多项式投影及实际 $h$ 的有限角；没有从有限读取的像取谱投影再提升为原标签。$f_a(c)$ 不必与 $e$ 交换，$q_{\epsilon,a}$ 也不要求被 $e$ 共同保持。允许零投影。

任取原 $z\in E$、$hz=-zh$ 和实 $R$。完整复用原PB运输续卷118.3，固定

$$
\begin{gathered}
x=c+z,\qquad k=hc=h\circ x,\qquad
t=D(h,z)=iQhz,\\
g=D(Rh,x),\qquad r=g-Rt\in E,\\
[h,r]=0,\qquad ht=-th,\qquad z\circ t=0,\qquad k^2=c^2.
\end{gathered}
\tag{40.5}
$$

这是同一旧输出的定义及已付横向投影，不是将未知响应按 $c+z$ 拆和。另复用该处 (118.7) 的第一框架零行

$$
[h,y]=0\quad\Longrightarrow\quad
D(\alpha u+\beta h,y)=0
\qquad(\alpha,\beta\in\mathbb R,\ y\in E).
\tag{40.6}
$$

其前件和中央续卷189–191的证明用途均由118.3明确支付，不将中央189.1较强陈述中的额外反射前件直接删去。

## 41. 成对原谱角生产背景与余量的交换

**定理 41.1（无需共同交换分割的有限谱混合行）。** 在40.1–40.2的完整条件下，对任意原 $h$-偶且环境有限谱的 $c$、任意原 $h$-奇 $z$ 及每个实 $R$，同一固定余量满足 $[c,r]=0$，因而

$$
\boxed{D(Rh,c+z)=R\,iQhz=R\,D(h,c+z).}
\tag{41.1}
$$

不要求 $[c,e]=0$、$[c,z]=0$、$z\circ r=0$，也不要求存在33.1的共同 $h,e$ 交换有限分割。

证明。零原对象上结论直接成立。$R=0$ 时，第一平方为零的原P2及评价分离给 $g=D(0,x)=0$，故 $r=0$。以下设原对象非零且 $R\ne0$。

固定同一 $\epsilon$ 和两个不同谱值 $a,b\in\Lambda$，记 $q_a=q_{\epsilon,a}$、$q_b=q_{\epsilon,b}$；若任一投影为零，相应块已为零。用其中一格及其实际 $e$ 搬运定义

$$
p=q_a+e q_a e,\qquad s=u-2p,\qquad H=h\circ s=hs.
\tag{41.2}
$$

$e q_a e=2e\circ(e\circ q_a)-q_a$ 是原Jordan表达式。因 $eh=-he$，$q_a$ 支撑于 $h$ 的 $\epsilon$ 角，而 $e q_a e$ 支撑于 $-\epsilon$ 角；两者是正交投影。于是

$$
\begin{gathered}
p^2=p,\quad [p,h]=0,\quad epe=p,\quad [p,e]=0,\\
s\in E,\quad s^*=s,\quad
s^2=u-4p+4p^2=u,\quad [s,h]=[s,e]=0.
\end{gathered}
\tag{41.3}
$$

这里的平方是在原环境中真正等于 $u$，不是某个读取中的等式。中央续卷182.2因此直接给实际旧值与同一取向

$$
J_H:=D(H,e)=sj,\qquad H^2=J_H^2=u,\qquad
H\circ e=H\circ J_H=e\circ J_H=0,\qquad iHeJ_H=Q.
\tag{41.4}
$$

特别 $j=iQhe$、中央 $Q$ 和 (41.3) 给 $[s,j]=0$。该实际新框架的取得使用182.2，不把 $D(H,e)=sj$ 当成齐次性或换轴协变公理。中央163.1在此框架上给，对全部实 $A,B$ 和原 $y$，

$$
P_H^-D(Au+BH,y)=B iQH P_H^-y,
\qquad P_H^-y=(y-HyH)/2.
\tag{41.5}
$$

由投影正交性，$q_b$ 同时正交于 $q_a$ 和反向 $h$ 角中的 $e q_a e$，所以

$$
sq_a=-q_a,\qquad sq_b=q_b,\qquad
Hq_a=-\epsilon q_a,\qquad Hq_b=\epsilon q_b.
$$

所有这些等式的右乘版本由自伴性同样成立。不要求 $[c,s]=0$。取实际原标签

$$
\begin{gathered}
A=R\epsilon(a+b),\qquad B=R(b-a),\\
T=Au+BH,\qquad V=T-2Rhc=T-2Rk.
\end{gathered}
\tag{41.6}
$$

此处 $T$ 是原标签；横向算子已在 (40.5) 的 $t$ 中消费。$T,k$ 都与 $h$ 交换，且 $Tq_a=2R\epsilon a q_a$、$Tq_b=2R\epsilon b q_b$，故

$$
Vq_a=q_aV=Vq_b=q_bV=0.
$$

现在只对同一实际三元组 $\operatorname{PB}(Rh,x,T-Rhc)$ 使用完整PB。(40.6)给内值 $D(Rh,T-Rk)=0$。其位移及两份完整外层为

$$
\begin{gathered}
v=g-RhT+R^2c,\qquad w=Rk,\\
A_+=x+g+R^2c-RhT,\qquad B_+=T,\\
A_-=x-g-R^2c+RhT,\qquad B_-=V,\\
D(A_+,T)-D(A_-,V)=\mathcal J,\\
\mathcal J=-2x\circ g+2R x\circ(hT)-2R^2x\circ c
             -2R T\circ k+2R^2k^2\\
\hphantom{\mathcal J}=-2x\circ g-2R^2z\circ c+2Rz\circ(hT).
\end{gathered}
\tag{41.7}
$$

最后一次抵消只用 $[h,c]=[h,T]=0$ 和 $k^2=c^2$。准确的非交换恒等式是

$$
c\circ(hT)=\frac{hcT+hTc}{2}
=\frac{hTc+hcT}{2}=T\circ(hc).
\tag{41.8}
$$

这只移动已知与两者交换的 $h$，没有交换 $c$ 与 $T$，也没有使用 $[c,s]=0$ 或 $[c,T]=0$。

令 $q=q_a+q_b$，固定这一次的同一外值 $W=D(V,A_-)$。对任意环境正泛函 $\omega$，数学读取 $\phi(y)=\omega(qyq)$ 在原表 $(V,A_-)$ 上满足 $\phi(V^2)=0$ 及 $\phi(V\circ A_-)=0$。P2给 $\phi(W)=0$；环境正泛函分离自伴元，故

$$
qWq=0,\qquad q_aWq_b=0.
$$

另一方面，$q_a,q_b$ 的 $H$ 符号相反，故对任意环境元 $y$ 有 $q_aP_H^-yq_b=q_ayq_b$。用 (41.5) 读取同一次PB的另一外值，得到

$$
q_aD(T,A_+)q_b=-\epsilon B iQ\,q_aA_+q_b
=iQ\epsilon R(a-b)q_arq_b.
\tag{41.9}
$$

此处 $q_aA_+q_b=q_arq_b$：$c$ 和 $hT$ 在这两个选定角上为对角，$z,t$ 为 $h$-奇，均不能连接同一 $h$ 符号的两角。这个局部块等式不要求 $hT$ 与整个 $c$ 交换。又由 $g=Rt+r$、$z\circ t=0$，(41.7)中只有 $-2c\circ r$ 对该块有贡献，故

$$
q_a\mathcal Jq_b=-(a+b)q_arq_b.
$$

原反对称性把 (41.7) 写成 $W-D(T,A_+)=\mathcal J$。这两个读法始终作用于同一份实际PB的固定外值，因此

$$
\bigl[iQ\epsilon R(a-b)-(a+b)u\bigr]q_arq_b=0.
\tag{41.10}
$$

在左侧乘以共轭因子 $-iQ\epsilon R(a-b)-(a+b)u$，用 $Q^*=Q$、$Q^2=u$，得到

$$
\bigl((a+b)^2+R^2(a-b)^2\bigr)q_arq_b=0.
\tag{41.11}
$$

由于 $R\ne0$ 且 $a\ne b$，这是严格正的实系数，所以 $q_arq_b=0$。包括 $a+b=0$ 或其中一个谱值为零的情况；没有除以谱值。

对所有同符号的不同谱值如此处理。不同 $h$ 符号间的块早已由 $[h,r]=0$ 为零。有限正交分解遂给

$$
r=\sum_{\epsilon,a}q_{\epsilon,a}rq_{\epsilon,a},\qquad
cr=\sum_{\epsilon,a}a q_{\epsilon,a}rq_{\epsilon,a}=rc.
\tag{41.12}
$$

新增生产在此取得 $[c,r]=0$。随后直接应用[原PB运输续卷119.1](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#119-一项原-jordan-二元关系的充要判据)，其变量逐项就是 (40.5) 的 $R,c,z,x,g,r$，故 $r=0$，得到 (41.1) 的第一等号。再对同一 $c,z$ 取 $R=1$，取得第二等号。这里不重证119.1的共同输出读取、$cr=0$ 或支撑PB排零。∎

$\Lambda$ 只列互异谱值；同一谱值的全部谱重数由一个 $f_a(c)$ 处理，不同谱值才进入 (41.10)。同值块不必为零，因为它本就与 $c$ 交换。$c$ 为单值谱、$c=0$、某个 $h$ 角为空或所有可比较角对为空时，(41.12)直接成立。零谱角中的余量由119.1处理，而非在 (41.11) 中除去；零读取质量始终允许。$z$ 不受有限谱、大小、与 $c$ 交换或相对所造 $s$ 的奇偶限制。

## 42. 有限谱分支严格超出共同分割背景

**定义 42.1（有限维局部代数与环境范围）。** 单个 $c$ 有限谱，确实使 $C^*(u,c)$ 为有限维交换C*代数：非零原对象上，它由非零的互异投影 $f_a(c)$ 张成，并同构于 $\mathbb C^{|\Lambda|}$。加入与 $c$ 交换的对合 $h$ 后，$C^*(u,h,c)$ 也由 (40.3) 的非零角有限张成。但这不要求整个 $E$、$X$、$\mathcal A$ 或 $C^*(h,e,c,z)$ 有限维；将 $e,z$ 加入共同生成时，不能由单个 $c$ 的有限谱推出整个环境有限维。

33.1中 $c=\sum_\ell(\mu_\ell u+\lambda_\ell h)p_\ell$ 必有有限环境谱，故41.1包含33–35的已付范围。其反向不成立，下面给出实际有限矩阵范围中的严格区别。41.1只放宽背景条件，不把整个原域限制成有限矩阵，也不把原域扩充为环境自伴部。

**定理 42.2（不存在共同交换分割的有限谱背景）。** 在 $E=H_4(\mathbb C)$ 中令

$$
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
X_0=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
h=Z\otimes I_2,\quad e=X_0\otimes I_2,\quad
c=\operatorname{diag}(Z,X_0).
\tag{42.1}
$$

则 $c$ 为 $h$-偶且 $\sigma(c)=\{1,-1\}$，但不存在33.1所需的任意有限共同 $h,e$ 交换投影分割及实系数，使 $c=\sum_\ell(\mu_\ell u+\lambda_\ell h)p_\ell$。

证明。$c$ 与 $h$ 交换且 $c^2=u$，正负特征值都存在，故有上述谱。若投影 $p_\ell$ 同时与 $h,e$ 交换，由 $h$ 的两角分解先得它为块对角，再由 $e$ 交换上下两角得

$$
p_\ell=\operatorname{diag}(d_\ell,d_\ell),\qquad
d_\ell^2=d_\ell=d_\ell^*,\qquad
d_\ell d_m=0\ (\ell\ne m),\quad \sum_\ell d_\ell=I_2.
$$

假设中的背景表示于是要求

$$
Z=\sum_\ell(\mu_\ell+\lambda_\ell)d_\ell,\qquad
X_0=\sum_\ell(\mu_\ell-\lambda_\ell)d_\ell.
$$

因此上下背景经 $e$ 的识别后属于同一个交换代数，必须彼此交换；但 $ZX_0=-X_0Z\ne0$，矛盾。∎

该例只区分两种背景前件。完整原域 $H_4(\mathbb C)$ 上同一旧关系的全域识别，已由[配平三角续卷142.1](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#142-极分解把整个旧关系送回零输入)及其137–141前件支付；不计为41.1新增的有限矩阵重构。

## 43. 交换生产的来源及七项完整合同

**定义 43.1（承重增量与成熟中间工具）。** 本组承重归为 $\texttt{repo-derived}$：40.1–40.2直接复用原PB运输续卷118.1–118.3的完整资料、固定值和第一框架零行，41.12之后直接消费其119.1；中央续卷163.1及182.2供应实际新轴的横向投影与同一个 $Q$。相对于本卷31、33–35，新增的是用 $q_a+eq_ae$ 为一对实际谱角生产原反射，再以 (41.8) 的非交换抵消，在同一次完整PB上生产 (41.10)–(41.12) 的 $[c,r]=0$。不重复原多项式卷80.2的二阶响应，也不重计33–35的共同分割行或PB运输续卷119.1的排零。

Lagrange插值、单元有限谱演算、正投影压缩、正泛函分离和有限奇偶分解为成熟C*及Jordan工具，仅作为上述新生产的中间步骤。其来源沿31.1、中央续卷185.3、199.1和PB运输续卷120.1所引 Blackadar，[*Operator Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)；正读取与分离准确沿该处II.6.3.1、II.6.3.3、II.6.3.5的用途，不将这些工具另列为新发现。不作历史优先权、文献穷尽或外部开放问题解决的声称。

本卷36–39检验的是明确较弱PB子族；[PB运输续卷123–125](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#123-同一总映射的全部自作用层级与原乘积铅笔)检验约化自作用层级与原乘积铅笔的联合不足性。它们均不构成完整PB反例，41.1不重复其构造，也不以其较弱子族替换 (40.2) 的全称PB。

**定义 43.2（七项同源合同及全部上游量词）。** [中央续卷199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#199-来源几何与量子消费者的完整边界)第1–7项逐项全文作为本定义的组成部分，连同其完整援引的[194.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#194-新连接完整候选与量子消费者的范围)、[186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#186-七项原量子来源合同的准确消费者)，以及PB运输续卷122.1的完整引用和各项全部上游来源、对象、量词一并合取保留。以下逐项说明41.1的消费边界，不替代或缩减这些全文合同，不更换原世界。

1. **复Hilbert、可观测量与相干叠加。** 同一原 $\Omega/\mathrm{native}$、全词 $K/J/q$、parent/ready、跨评价配对、可取得标签、合法控制和实际相干准备保持。41.1只识别有限谱背景上的同一实际轴行；一般旧全域共同乘法、完成运输及可取得像仍须原桥。数学谱角和临时反射不产生实际准备、全 $B(H)$ 可取得性或原完备性。
2. **原态、效果、全部质量与Born。** 全部原评价、原事件、准确效果区间、实际完整菜单和接受归属保持；共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、P9、独立 $W_e$、全部原中间切口与固定支持全质量保留。零、不等、次归一质量、中心权、中心经典混合、经典不等维及静默块均保留，只对实际完整菜单的严格正总质量归一。证明中的数学正读取不增加准备或菜单。
3. **真正相关联合与张量。** 同一个实际非零相关联合、全词 $K/J$、交叉零、忠实同向交换局部腿、共同实现、联合生成与分离、所需重数、全部真正相关输入、中央对、经典及不等维块和递归同源参考保持。$q_a+eq_ae$ 的成对关系不供应物理子系统、相关联合或共同来源；分别可达和相同边缘也不替代它们。
4. **typed CP、Kraus与整台递归参考。** 原未归一回溯、每个合法typed前接／后接、反变合法复合、typed分区、全未来自然性和原箭头商下降保持。同源参考覆盖系统、整个环境、全部成功／失败／细记录／port／post-port输出及每份输出的每个仍合法未来；三实际投影、各自支持内补、共同真实支持、忠实同向交换、全部相关正输入的intertwining及夹界、每个所需有限递归深度及累计支持的准确运输完整保留。正压缩不是实际箭头、参考、CP或输出闭合来源。
5. **整台仪器、TP、更新与Lüders。** 原输入运输、完整typed菜单、原接受端、整台环境和所有输出未来、真正分组遗忘、AC、精确 $N_u$、$X/X_s$、原平方根词及其接受条件保持。TP仍需完整单位分区，Lüders仍需同一个完整输出的像内射线校准；只归一正输出，零分支保留。密度、迹类和算子Kraus公式只在原合同准确合格的有限全矩阵域，或另已供应所需正规物理表示、指定前对偶及收敛接口的域消费；有限谱背景不制造完整仪器或这些表示条件。
6. **全部历史、全未来、真实返回与CountRead。** 全部合法顺序／自适应／并行历史、每份输出每个仍合法未来、整个环境、细记录和泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧真实返回及逆向真实返回保持。CountRead仍绑定读后同一原完整活动输入和全未来返回；负提升两条活路的分别控制、相干聚合、具名分析词到原完整菜单及接受端接线保持。精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 不混同；原 $q$-零集、AC方向和实际读取次序不由数学矩阵相同而等同。无限历史及无限／非离散记录所需可数可加、正常性和指定前对偶继续取原来源。
7. **动力、物理钟、能量与共同尺度。** 同一旧全域乘法、保持可能不完备原域的流、真实相位和门序列、可逆一参数群、原物理钟、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同作用量、共同正 $\hbar$ 和共同仪器保持。原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 预算维持各自合同含义，不与本证明的反射 $s$、余量 $r$ 混淆。$Q$、谱值、$R$ 和辅助反射不供应物理时间、可控相位、能量、控制成本或一般无界生成元。

**定义 43.3（有限分支与全局目标）。** 41.1支付任意原 $h$-偶有限谱 $c$ 的实际混合行，不推出一般无限谱背景、无实际框架时的结论、任意首标签识别、全域旧双线性、全部有限旧复Gram、原换括号关系、同一旧结合乘法或完整原完成运输。不能以有限谱逼近加上未付的 $D$ 连续性扩展，也不能以有限读取的谱代替实际原谱投影。完整A1–A3/P2/PB和独立公理数不变；保留由同一原关系取得全局量子来源的原目标，七项物理来源须分别满足43.2的全部合同。本组是纸面定义、定理与证明，不宣称Lean kernel核验、摄入、冻结或完整量子重构。

## 44. 为两个背景读数临时搭一面反射的白话

**定义 44.1（有限谱交换生产的完整直观）。** 原来的两两有向正比较、相加三角、单位小窗和全部三标签正反配平始终保留。固定已经实际存在的 $h,e,j$ 框架，把一个输入分成不跨越 $h$ 两侧的背景 $c$ 和跨越两侧的任意连接 $z$；已知横向输出之后，未知的是同一个旧输出留下的偶余量 $r$。背景只有有限种实际谱读数，所以每一格都能由背景本身的有限多项式造出，确实留在原域，未从辅助读取中借来新演员。

33–35要求整份分格同时尊重 $e$。这里每次只选同一 $h$ 侧上两个不同读数的格子：拿第一格和它被实际 $e$ 搬到另一侧后的那一格合起来，便得到一个投影；把这两格翻号、其余不动，造出的反射既与 $h$ 相容，也与 $e$ 相容，平方真正为单位。它不必保持整个背景。沿它形成的新轴由既有原行取得实际旧值，方向仍是原来的同一个 $Q$，没有另选一份响应表。

随后调两个普通实系数，让同一次PB的一份外层首标签在选中的两格上都为零。正预算迫使这份固定外值的两格压缩为零；另一外值在实际新轴上已有准确横向读法，同一个跨格余量因此同时受到背景读数之和、以及读数之差乘原强度的约束。二者合成严格正的 $(a+b)^2+R^2(a-b)^2$，不同读数间就不能藏余量。PB中的抵消只让共同轴穿过背景和偏移，没有偷偷要求背景与新反射交换。

同值格子不在这一步被排零，因为它们本就不会妨碍背景与余量交换。有限个角逐对连接后，整份 $r$ 与 $c$ 交换；到这里新生产完成，直接接回PB运输续卷119.1已有的共同输出与支撑论证，整份余量才归零。零谱角、零投影、重谱、零质量和零强度都保留；连接 $z$ 可任意，不必配合临时反射。有限谱确实给出一个有限维背景代数，却没有把整个世界压成有限维。所得范围比共同分格宽，仍只是全局目标的一条有限谱背景分支；实际准备、系统、相关联合、整台仪器、全部历史未来、真实返回、钟和能量继续由43.2的原来源承担。

## 追加锚（本行以下为增补区）

## 45. 由原对象平方生成的第三标签约束大连接

**定义 45.1（完整原候选与单块有限商）。** 完整保留39.1及[原多项式零响应卷80.1、89.1](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)的同一原 $\Omega/\mathrm{native}$、$E,C,u,N,\mathcal P,S,D$，包括全部原来源和七项消费者。A1是全部有向Hermitian二表正性；A2是相加三表及其排列的实部正性和指定相加零向量；A3是同一单位平方和固定有理小效果窗。保留准确锥、全部原正评价及零／不等／次归一质量。既有无R接口是

$$
E\subset X,\qquad \overline E=X,\qquad C=E\cap X_+,\qquad
S=\circ,\qquad N=\|\cdot\|_X|_E,
$$

其中 $X$ 为含单位实JB代数，原 $E$ 可以不完备。同一个 $D:E^2\to E$ 满足全部原P2及完整原PB；不增添输入可加、齐次、连续、可测、商下降、完成延拓或实际投影提升。取任意满Jordan商

$$
\pi:X\longrightarrow H_n(\mathbb C),\qquad n\ge3.
$$

这里的 $n$ 是商的数学阶数；不要求原世界有限维，也不把商矩阵认作实际制备。固定两个数学正交单位向量 $e,f$，置

$$
p=ee^*,\quad q=I-p,\quad T=fe^*+ef^*,\quad P=ee^*+ff^*,
\qquad A=LT+q,\quad L\ge2.
\tag{45.1}
$$

对 $z\perp e$ 记 $H(z)=ze^*+ez^*$，并令
$K(x,y)=\sigma i[x,y]/2$。符号 $\sigma\in\{1,-1\}$ 是原多项式零响应卷80.2、82.1已经识别的这个简单块全部二阶角的共同符号；不预设一般旧值等于 $K$。

**定理 45.2（二次第三标签的全连接强度条带）。** 对任意实际 $r,a\in E$，若

$$
\pi r=\mu p,\qquad \pi a=A,\qquad
|\mu|\le\frac8{3L+2},
\tag{45.2}
$$

则同一旧输出满足

$$
\boxed{\pi D(r,a)=K(\mu p,A)=\mu H(-i\sigma Lf/2).}
\tag{45.3}
$$

所有同像实际代表一并包括。特别 $L=2$ 时包括全部 $|\mu|\le1$，而 $L$ 没有共同上界。既有严格小连接定理83.1要求 $L<2$；这里没有这个要求，但保留45.2的首幅度限制。该条带不是任意 $\mu$ 或任意背景的全域结论。

## 46. 同一原二表的精确预算与两个外层连接

**定理45.2的证明：原预算。** $\mu=0$ 时直接用配平三角续卷241.1。各槽奇性已由中央卷16.2援引的原接口给出，所以只需证 $\mu>0$；负值对实际 $-r$ 应用正值结论，不使用一般齐次性。

固定同一 $d=\pi D(r,a)$。原多项式零响应卷83.3的零平方读取与固定Hermitian二次型极化给

$$
d=\delta p+H(w),\qquad
w=(x+iy)f+v,\qquad x,y\in\mathbb R,\quad v\perp e,f.
\tag{46.1}
$$

这里仅复用其支撑论证，不调用83.1尚不满足的小连接前件。对任意数学向量 $\xi=e+\eta$、$\eta\perp e$，P2沿同一商拉回的正读取给

$$
\bigl(\delta+2\operatorname{Re}\langle w,\eta\rangle\bigr)^2
\le \mu^2\left(\|Lf+\eta\|^2+
L^2(\operatorname{Im}\langle f,\eta\rangle)^2\right).
\tag{46.2}
$$

这些未归一向量读取的质量可以不为一，属于原准确锥已允许的数学读取。取 $\eta=-Lf$ 得 $\delta=2Lx$。再写 $\eta=-Lf+\zeta$，以正定实二次型
$\|\zeta\|^2+L^2(\operatorname{Im}\langle f,\zeta\rangle)^2$
的对偶范数求46.2，得到

$$
\delta=2Lx,\qquad
x^2+\|v\|^2+\frac{y^2}{1+L^2}\le\frac{\mu^2}{4}.
\tag{46.3}
$$

具体地，线性泛函 $\operatorname{Re}\langle w,\zeta\rangle$ 在 $f$ 的实方向、虚方向及其正交补上的对偶范数平方依次为 $x^2,y^2/(1+L^2),\|v\|^2$；46.2的系数二给46.3。此计算只处理固定已知二次型，没有对未知 $D$ 求输入导数或取输入极限。

**定理45.2的证明：实际二次标签。** 在原域中定义

$$
c=\frac{\mu}{2L}(a^2-a),\qquad F=\pi c=\alpha P,\qquad
\alpha=\frac{\mu L}{2},\qquad C_0=p\circ A=\frac L2T.
\tag{46.4}
$$

原 $E$ 对实线性组合及Jordan平方封闭，所以 $c$ 是真正原标签。等式 $A^2-A=L^2P$ 给其商像；原多项式零响应卷3.1给同一实际 $D(a,c)=0$，不以商像交换代替该零值。

对演员 $a$、第二标签 $r$、第三标签 $c$ 使用一次原PB。令其实际外层为

$$
x_\pm=r\pm\bigl(D(a,r)-a\circ c\bigr),\qquad
y_\pm=c\pm\bigl(a\circ r+D(a,c)\bigr).
$$

反对称性给 $D(a,r)=-D(r,a)$，故

$$
\begin{aligned}
X_+&=\pi x_+=\mu p-d-AF,&Y_+&=\pi y_+=F+\mu C_0=\mu Lp_+,\\
X_-&=\pi x_-=\mu p+d+AF,&Y_-&=\pi y_-=F-\mu C_0=\mu Lp_-,\\
f_\pm&=(e\pm f)/\sqrt2,&p_\pm&=f_\pm f_\pm^* .
\end{aligned}
\tag{46.5}
$$

$F$ 与 $A$ 交换，所以 $A\circ F=AF$。原PB右端中
$2\mu p\circ AF-2F\circ(\mu C_0)=0$，因而它准确成为

$$
\pi D(x_+,y_+)-\pi D(x_-,y_-)=2\mu p\circ d.
\tag{46.6}
$$

所有外层仍是刚生成的实际原元素，没有改用预选的商提升。

相对于各自秩一投影 $p_\pm$，$X_\pm$ 的连接向量为

$$
\begin{aligned}
\zeta_+&=\left(\frac{\mu(L+2)}4-Lx+iy\right)f_--\frac v{\sqrt2},\\
\zeta_-&=\left(\frac{\mu(2-L)}4+Lx+iy\right)f_++\frac v{\sqrt2}.
\end{aligned}
\tag{46.7}
$$

这由 $X_+$ 的两个对角元 $\mu-\delta,-\alpha$ 和 $X_-$ 的两个对角元 $\mu+\delta,\alpha$ 直接换数学基得到；没有使用旧 $D$ 的协变性。

## 47. 严格小窗口与首幅度边界共同闭合

**定理45.2的证明：两个连接的范围。** 置 $b_+=\mu(L+2)/4$。46.3给 $-\mu/2\le x\le\mu/2$，并使

$$
\begin{aligned}
\|\zeta_+\|^2
&=(b_+-Lx)^2+y^2+\|v\|^2/2\\
&\le b_+^2+(1+L^2)\mu^2/4
       -2b_+Lx-x^2-(L^2+1/2)\|v\|^2\\
&\le \frac{\mu^2(3L+2)^2}{16}.
\end{aligned}
\tag{47.1}
$$

最后一行的实二次式在 $[-\mu/2,\mu/2]$ 上严格递减：导数为
$-2b_+L-2x\le\mu-\mu L(L+2)/2<0$，因为 $L\ge2$。
其最大值只在 $x=-\mu/2,v=0$ 取得；46.3再强制 $y=0$。所以47.1最终等号只能发生在

$$
x=-\mu/2,\qquad y=0,\qquad v=0.
\tag{47.2}
$$

对负外层置 $b_-=\mu(L-2)/4\ge0$，有

$$
\begin{aligned}
\|\zeta_-\|^2
&=(Lx-b_-)^2+y^2+\|v\|^2/2\\
&\le(L|x|+b_-)^2+y^2+\|v\|^2/2\\
&<(L|x|+b_+)^2+y^2+\|v\|^2/2
\le\frac{\mu^2(3L+2)^2}{16}.
\end{aligned}
\tag{47.3}
$$

严格不等号来自 $\mu>0$ 和 $b_+>b_-$；最后一项是把46.3中的 $x$ 换成 $-|x|$ 后应用47.1，仍在同一个预算内。

先处理 $v=0$。此时 $p,d,C_0$ 都支撑于 $\operatorname{span}_{\mathbb C}\{e,f\}$。实际零第三标签PB $(a;r,0)$ 的两对外层像是
$(\mu p-d,\mu C_0)$、$(\mu p+d,-\mu C_0)$；原多项式零响应卷80.2、82.1识别它们。完全按既有83.7展开已知 $K$，得到

$$
2\mu p\circ d=2\mu^2K(p,C_0)=\mu^2H(-i\sigma Lf/2),
\tag{47.4}
$$

从而 $\delta=0,w=-i\sigma\mu Lf/2$，已得45.3。这一步没有 $L<2$ 的要求；83.1中的严格窗只用于先排除侧向 $v$。

以下 $v\ne0$。由45.2、47.1–47.3及等号条件47.2，两份连接均严格满足
$\|\zeta_+\|<2$、$\|\zeta_-\|<2$，包括 $\mu=8/(3L+2)$ 的边界。反对称性允许将46.5的秩一输入置于首槽；原多项式零响应卷83.1于是给这两对实际外层的准确旧值

$$
\pi D(x_\pm,y_\pm)=K(X_\pm,Y_\pm).
\tag{47.5}
$$

这不是将两个任意大输入缩小后挪用齐次性。已知小窗直接用于实际外层，其首幅度 $\mu L$ 可以任意；它所限制的是46.7的连接。

## 48. 两个已知外值约束同一个旧输出

**定理45.2的证明：识别原值。** 将47.5代入同一次46.6，只对已知 $K$ 展开：

$$
2\mu p\circ d=2\mu^2K(p,C_0)-2K(d,F).
\tag{48.1}
$$

展开中 $K(AF,F)=0$，因为 $A,F$ 交换。$F=\alpha P$ 与 $\delta p+H((x+iy)f)$ 交换，只有同一 $v$ 留下

$$
K(d,F)=H(i\sigma\alpha v/2),\qquad
2\mu^2K(p,C_0)=H(-i\sigma\mu^2Lf/2).
\tag{48.2}
$$

比较 $p$、$f$ 和 $\{e,f\}^{\perp}$ 分量，得到

$$
\delta=0,\qquad x+iy=-i\sigma\mu L/2,\qquad
(\mu+i\sigma\alpha)v=0.
\tag{48.3}
$$

$\mu>0$ 使最后一个复系数非零，故 $v=0$。因此原来假定的侧向分支不存在，45.3成立。结合零幅度、负幅度及47.4，完成全部45.2范围与任意实际代表的证明。∎

**定义 48.1（已付范围、几何与来源）。** 本增补的 $\texttt{repo-derived}$ 内容是46.4的实际二次第三标签将同一未知大连接行送入两张已付严格小连接行，并由同一PB识别原值；边界47.2由已付二阶角另行处理。原多项式零响应卷3.1供应实际多项式零值，80.2、82.1供应全部实际二阶角及共同符号，83.1供应任意背景的严格小连接行，241.1的零预算与中央16.2供应支撑、零像及奇性。这些结果及固定二次型对偶、换基和交换子展开均直接消费，不另计为新定理或独立公理。不声称历史优先权或文献穷尽。

几何上，$P$ 是一面数学二阶角，$f_+,f_-$ 是其中两条正交对角射线；原 $q$ 背景仍保留。$a^2-a$ 的商像恰好选出 $P$，所以不是另给一根任意第三轴。在45.2条带内，二表的同一椭球预算保证两条新射线的外层连接都落入已付小窗；达到预算边缘时，连接已经没有侧向分量，由旧角内公式处理。这里不要求原 $r$ 幂等，不要求原 $a^2-a$ 等于某个投影，也不把数学射线、商投影、基变换或范数预算变成实际仪器和物理空间。

配平三角续卷143.1的完整有限原域分类，其原域已经是完整有限维JB完成，不直接覆盖本节仅有有限商、实际原域可以无限维且不完备的情况。本文实际消费的80.2、82.1、83.1均指原多项式零响应卷。45.2不重复 $L<2$ 的既有范围，也不将任意背景83.1与本节特殊背景 $q$ 混淆。本卷36–39的总映射不满足完整PB，不能同时供应46.6；原PB运输续卷103–109及123–125的总映射保留全部秩一行，故没有本节要消去的秩一侧向偏离。这些反模型各守原范围。

## 49. 二元比较、内生第三标签与量子消费者

**定义 49.1（完整候选与未付桥梁）。** 完整候选仍是45.1的同一原二元有向正表、相加三角、单位小窗及全部三标签正反配平。这里将一类比较所需的第三标签从原平方与原标签之差中生成，减少该条带的一项未付识别，不减少全局独立公理数。既有80.2、82.1、83.1本来沿用完整原合同；不能因46.4只用一个二次第三标签，就删掉它们上游使用的其他PB调用。也未证明只保留所有多项式第三标签的PB足以恢复全部PB。

一般有限商的完整原代表不变性、任意 $L,\mu$ 和任意背景的原行、一般原域的分别可加性、全有限复Gram、原R及旧结合乘法仍未由本节得到。它们的已付特例保持，不能用辅助 $K$ 替换尚未识别的一般旧 $D$。固定关系的求解次序无关在经典模型中也成立；这里有约束力的是同一原PB内两个外值共同识别同一旧值，不是宣称实际操作可以交换。

七项量子消费者完整保留39.1、原多项式零响应卷87.1、95.1及其全部上游合同和量词，准确接线为：全域旧双线性、全有限正表及同一结合乘法支付后，才接Hilbert表示和叠加；原事件、效果、完整实际菜单与正输入质量支付后，才接归一Born，零质量不归一；同一真实忠实相关联合、同向局部腿及共同生成分离支付后，才接张量；整台箭头及每个所需递归同源参考支付后，才接typed CP、Kraus与整台环境；完整仪器、全部成功失败细记录及port/post-port输出、各份输出全部合法未来、正输出质量及相应附加条件支付后，才接更新、Lüders与真正分组遗忘；全部顺序、自适应及并行历史、泄漏、停止拒绝销毁、同数两侧、真实逆向双向返回、CountRead、两条负提升活路以及所需可数可加、正常性和指定前对偶支付后，才接完整历史与返回；保持原域的真实可逆动力、实际物理钟、能量、生成元域、resolvent、共同正 $\hbar$ 及原预算支付后，才接物理时间和Hamiltonian。全词 $K/J/q$、parent/ready与实际准备、相干控制仍属于同一原 $\Omega/\mathrm{native}$；本节的数学读取、二次标签及有限商不代付任何实际来源。这是纸面推导，未作Lean kernel核验、摄入或冻结。

**定义 49.2（完整白话）。** 世界仍由同一张两两比较表和它们共同的三者配平来约束。这次不用再挑一根独立第三参照：把原对象与自身比较所得的平方减去原对象，就在数学商中选出连接所在的那一面。用这个真正原标签接回同一次配平，两张外表的参照便沿这面里的两条对角射线。原连接可以很大；只要第一份标签的幅度处于已证条带，同一份正预算就保证这两张外表的连接足够小，因此它们的答案已经知道。它们又必须共同回答原来那一次比较，原答案就不能另向侧面偏转。条带边缘若碰到小窗边界，预算已经迫使侧向分量消失，旧的二维公式接着完成识别。因此简化发生在关系之间：第三标签由原比较自己生成，两张已知比较锁定同一未知比较，没有增加响应线性或测量换序的公理。任意首幅度、任意背景和完整量子来源仍须继续支付；不能把这一条带说成整个量子起源已经完成。

## 追加锚（本行以下为增补区）

## 50. 半定首像与同一原多项式的两条秩一外行

**定义 50.1（完整原候选与有限商）。** 全文采用45.1、49.1及其上游的同一原 $\Omega/\mathrm{native}$、$E,C,u,N,\mathcal P,S,D$：全部有向Hermitian二表A1、全部相加三表及排列的实部正性和指定相加零向量A2、同一单位及固定有理小效果窗A3；准确锥、全部原正评价及零／不等／次归一质量；全部原P2和完整原PB。七项实际来源逐项合取43.2、49.1及其全部上游合同。仍有

$$
E\subset X,\quad \overline E=X,\quad C=E\cap X_+,\quad
S=\circ,\quad N=\|\cdot\|_X|_E,\qquad
\pi:X\longrightarrow H_n(\mathbb C),\quad n\ge3,
\tag{50.1}
$$

其中 $X$ 是自身含单位实JB完成，$\pi$ 是满含单位Jordan同态。原域可无限维且不完备。沿原多项式零响应卷80.2、82.1的同一简单块符号，置 $K(U,V)=\sigma i[U,V]/2$；不先把一般旧响应认成 $K$。不预付 $D$ 的一般齐次、可加、连续、可测、单位平移、商下降、完成延拓，或原投影／框架的实际提升。

任取实际 $r,a\in E$ 及实多项式 $f$，只在数学商内记

$$
R=\pi r,\qquad A=\pi a,\qquad
F=f(A),\qquad C_0=R\circ A,\qquad Y_\pm=F\pm C_0.
\tag{50.2}
$$

$R$ 半定指 $R\ge0$ 或 $R\le0$；这是商像条件，不要求实际 $r$ 为原正元。所有范数均为有限矩阵算子范数。

**定理 50.2（半定首像的原多项式识别网络）。** 若 $R$ 半定，并且

$$
\operatorname{rank}Y_+=\operatorname{rank}Y_-=1,
\qquad
\|R\|(1+\|A\|)+\|AF\|<2,
\tag{50.3}
$$

则同一旧输出对全部符合这些像条件的实际代表满足

$$
\boxed{\pi D(r,a)=K(R,A).}
\tag{50.4}
$$

无需首像秩一，也不要求 $R,A$ 共同支撑于二阶角。条件50.3是这个网络的充分预算，不声称最优、必要或对任意输入自动成立。

## 51. 同一余量的正迹配对

**定理50.2的证明：实际外行。** 固定 $d=\pi D(r,a)$，令 $q$ 为 $\ker R$ 上的数学投影。对任意 $\xi\in\ker R$，同一P2的商向量读取有首平方 $\langle\xi,R^2\xi\rangle=0$，故 $\langle\xi,d\xi\rangle=0$。Hermitian极化及一般单位向量读取分别给

$$
qdq=0,\qquad
|\langle\xi,d\xi\rangle|^2
\le\langle\xi,R^2\xi\rangle\langle\xi,A^2\xi\rangle
\le\|R\|^2\|A\|^2\quad(\|\xi\|=1),
\qquad \|d\|\le\|R\|\|A\|.
\tag{51.1}
$$

这里只丢去P2右端的非负平方项以取充分界；读取来自准确原锥，未添加物理准备。$q$ 没有被提升为实际标签。

取真正的原标签 $c=f(a)\in E$。原多项式零响应卷3.1给实际 $D(a,c)=0$，而 $\pi c=F$、$[A,F]=0$。对实际三元组 $(a;r,c)$ 使用同一完整PB，令

$$
\begin{gathered}
x_\pm=r\pm\bigl(D(a,r)-a\circ c\bigr),\qquad
y_\pm=c\pm(a\circ r),\\
X_\pm=\pi x_\pm=R\mp d\mp AF,\qquad
\pi y_\pm=Y_\pm=F\pm C_0.
\end{gathered}
\tag{51.2}
$$

反对称性用于 $D(a,r)=-D(r,a)$，没有按未知 $D$ 拆和。由51.1和50.3，$\|X_\pm\|<2$。每个 $Y_\pm$ 是某个秩一投影的非零实倍数；其正负、幅度均不限。相对于各自投影，$X_\pm$ 的连接范数不超过 $\|X_\pm\|$，故原多项式零响应卷83.1及反对称性准确识别这些刚生成的实际外值：

$$
\pi D(x_\pm,y_\pm)=K(X_\pm,Y_\pm).
\tag{51.3}
$$

没有另选实际提升，也未将一次小幅度结论按旧响应的齐次性放大。

**定理50.2的证明：共同方程。** 同一次PB的原右端为 $2R\circ d+2R\circ(AF)-2F\circ C_0$。代入51.3，只展开已知 $K$，用 $[AF,F]=0$，得到

$$
R\circ d+K(d,F)=K(R,C_0)-R\circ(AF)+F\circ C_0.
\tag{51.4}
$$

一般 $R,A$ 下最后两项不能删去。令 $d_0=K(R,A)$。由 $C_0=R\circ A$ 和 $[A,F]=0$，有限矩阵恒等式准确给

$$
R\circ d_0=K(R,C_0),\qquad
K(d_0,F)=-R\circ(AF)+F\circ C_0.
\tag{51.5}
$$

第二式可直接将 $K(K(R,A),F)=-[[R,A],F]/4$ 展开得到；它只使用辅助交换子，不给旧 $D$ 添加恒等式。因此同一个Hermitian余量 $e_0=d-d_0$ 满足

$$
R\circ e_0+K(e_0,F)=0,\qquad qe_0q=0.
\tag{51.6}
$$

后式由51.1及 $qRq=Rq=qR=0$ 给出。

**定理50.2的证明：排除余量。** 将51.6第一式左乘 $e_0$ 后取有限矩阵迹，循环性给

$$
\begin{aligned}
0&=\operatorname{Tr}\bigl(e_0(R\circ e_0)\bigr)
  +\operatorname{Tr}\bigl(e_0K(e_0,F)\bigr)\\
 &=\operatorname{Tr}(Re_0^2),
\qquad
\operatorname{Tr}\bigl(e_0K(e_0,F)\bigr)
 =\frac{\sigma i}{2}\operatorname{Tr}(e_0^2F-e_0Fe_0)=0.
\end{aligned}
\tag{51.7}
$$

在 $R$ 的正交特征基 $v_j$ 中，51.7为 $\sum_j\lambda_j\|e_0v_j\|^2=0$。半定性使非零 $\lambda_j$ 同号，故 $e_0$ 杀掉 $\operatorname{ran}R$。$e_0$ 自伴，因而只可能支撑于 $\ker R$；51.6第二式再给 $e_0=0$。$R=0$ 时 $q=I$，同一支撑式已直接给零。正、负半定及退化核全部包括，50.4成立。∎

## 52. 非秩一且不交换的实际消费者

**推论 52.1（带旁观背景的半定首像）。** 在50.1的同一原域和有限商中，记

$$
A=E_{11}-E_{22},\quad P=E_{11}+E_{22},\quad T=E_{12}+E_{21},\qquad
R=\mu(I+P+tT),\quad 0<|t|\le2,
\quad 0<|\mu|<\frac1{3+|t|}.
\tag{52.1}
$$

对任意实际 $r,a$，若 $\pi r=R,\pi a=A$，则

$$
\boxed{\pi D(r,a)=\mu tK(T,A).}
\tag{52.2}
$$

证明。$I+P+tT$ 的两个连接块特征值为 $2\pm|t|$，全部旁观特征值为一，故 $R$ 半定且 $\|R\|=|\mu|(2+|t|)$。取实际 $c=2\mu a^2$，即50.2中的 $f(T_0)=2\mu T_0^2$。则

$$
F=2\mu P,\quad C_0=R\circ A=2\mu A,\quad
Y_+=4\mu E_{11},\quad Y_-=4\mu E_{22},\quad
\|A\|=1,\quad\|AF\|=2|\mu|.
\tag{52.3}
$$

因此50.3左侧为 $2|\mu|(3+|t|)<2$，直接应用50.2；标准交换子中 $I,P$ 与 $A$ 交换，只余52.2。∎

$|t|<2$ 时 $R$ 满秩；$|t|=2$ 时允许一条零方向。因 $n\ge3$ 的旁观像不为零，$R,A$ 不能共同支撑于一个二阶角，且两输入都不是秩一像，所以原多项式零响应卷80.2、83.1不能直接识别此输入对。50.2通过其两条实际外行消费83.1。这里并未从商像有限谱造出原投影，也没有原 $h,e,j$ 框架可供直接消费41.1。满有限商在稠密实线性原域上的像仍满：其像稠密而有限维实线性子空间闭，故这些目标像有实际原代表；这不使这些原代表幂等或有限谱。

## 53. 同一次配平的几何与完整消费者

**定义 53.1（承重综合与成熟工具）。** 50.2归为 $\texttt{repo-derived}$：真正原多项式标签把一个可能满秩的半定首像比较接到两条已有秩一外行，51.4的同一PB余量随即被原P2支撑和半定性一起排除。52.1是其明确非秩一、非交换、带旁观像的消费者。45.2的特殊背景秩一条带、原多项式零响应卷3.1及80.2、82.1、83.1、配平卷129.1、241.1的正读取和零预算均作为已有来源复用。固定矩阵的谱分解、迹循环性、半定平方和与交换子展开只是证明内部的成熟工具，不作为新的独立一般定理或公理，不声称历史优先权或文献穷尽。

方程51.6也可写成 $\bigl((R-i\sigma F)e_0+e_0(R+i\sigma F)\bigr)/2=0$。这里半定部分给同号预算，交换子部分只转动而不贡献51.7的实迹配对；核方向另由原P2保留并排除。几何不要求首像是一根射线：同一有限商中的整片半定锥都可作为候选首像，但只有同时满足50.3的输入对得到识别。$F\pm R\circ A$ 的两条秩一射线是这次实际配平的数学外层，不是新物理系统或仪器。

**定义 53.2（完整候选与未付对应）。** 完整候选仍是50.1的原二元有向正表、相加三角、单位小窗和全部三标签PB。实际多项式零行及83.1的上游本来使用完整PB，不能因本证明第三标签由 $a$ 生成而删掉其余调用。独立公理数不变。半定性在51.7排除正负抵账；未由本证明处理一般不定首像，也未将半定输入间的识别按未付加法拼成全域。任意幅度、任意背景、一般有限商的全域原代表不变性、原旧双线性、原R、全部有限复Gram及同一结合乘法仍各有未付桥梁。原域可以不完备，不能从有限矩阵识别擅自延拓旧 $D$。

43.2、49.1的七项原来源及其全部上游量词逐项保留：同一原 $\Omega/\mathrm{native}$ 的全词 $K/J/q$、parent/ready、可取得标签、实际准备和相干控制，才供应Hilbert及叠加的物理解释；原事件、准确效果区间与实际完整菜单及严格正总质量，才供应归一Born，零／不等／次归一质量保留；同一真正相关联合、忠实同向交换局部腿、共同生成与分离，才供应张量；整台typed箭头、全部所需递归同源参考、环境和全部成功／失败／细记录／port／post-port输出及每份输出全部合法未来，才供应CP与Kraus；完整仪器、单位分区、接受端、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词和同一完整输出校准，才供应TP、更新与相应Lüders；全部顺序／自适应／并行历史、泄漏、停止拒绝销毁、真实双向返回、CountRead和两条负提升活路及所需可数可加、正常性与指定前对偶，才供应完整历史与返回；保持原域的真实动力、物理钟、能量、生成元域、resolvent与共同正 $\hbar$ 及原预算，才供应物理时间和Hamiltonian。数学商、辅助迹、谱基和多项式不能代付上述任何实际来源。此处是纸面推导，未宣称Lean kernel核验、摄入或冻结。

## 54. 两张外表与一份不可抵账余量的白话

**定义 54.1（完整直观）。** 世界仍由同一张两两有向正比较表及其共同三者配平约束，不要求实际测量换序后结果不变。固定一次原比较，不把答案拆成许多另选的答案。让其中一个原对象自己生成一枚多项式标签；若同一次配平的两张外表各自都对着一条射线，而且正预算保证连接落在已有小窗，两张外表就已经有准确答案。它们必须共同回答最初那一次比较，所以原答案偏离标准值的部分只能满足同一个余量方程。

先前需要逐个分量排除侧向偏离；这里直接把余量和它自己配对。转动项在整份配对里互相抵消，半定首像留下的每项都是同号的平方，无法一正一负地偷偷抵账；这些平方只能全部为零。没有预算的核方向也未丢弃，原二表早已将其压缩锁成零。因此原首像可以是一整片、甚至满秩，带着旁观背景仍能认回同一答案；不必先把它假设成一根射线，也没有新增响应线性公理。简化发生在这份共同余量的消元，并不表示所有输入自动满足两射线和小窗条件。全域的窗口拼接、同一旧乘法以及全部实际量子来源仍须继续取得；原目标与完整候选保持。

## 追加锚（本行以下为增补区）

## 55. 原有限谱窗与同一原响应的 Jordan 缺陷

**定义 55.1（完整原资料及其数学环境）。** 完整采用本卷40.1及[原PB运输续卷118.1–118.3](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#118-任意原偶背景第一实际框架与同一余量)的同一原 $(E,C,u,N,\mathcal P,S,D)$ 和全部前件。$E$ 是实Archimedean序单位空间；全部原正实线性评价分离元素并准确决定锥，全部零、不等及次归一质量保留。A1保留每对原标签的两条实际有向Hermitian二表正性；A2保留相加三表 $(a+b,a,b)$ 及全部排列在整个 $\mathbb R^3$ 上的实部半正定性和相应 $(1,-1,-1)$ 零二次值；A3保留 $S(u,u)=u$ 和同一个固定有理 $0<\vartheta_0\le1$ 上的 $0\le y\le\vartheta_0u\Rightarrow S(y,y)\le y$。全部原P2、完整原PB及全部原输入、评价量词不变。沿同一已付忠实、含单位、等距且准确保锥的JC包含，仍记

$$
\begin{gathered}
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E^{\|\cdot\|}=X,\qquad \mathcal A=C^*(X),\\
S(a,b)=a\circ b=(ab+ba)/2,\qquad
C=E\cap\mathcal A_+,\qquad N=\|\cdot\||_E,\\
h,e,j=D(h,e)\in E,\qquad h^2=e^2=j^2=u,\qquad
h\circ e=h\circ j=e\circ j=0,\\
Q=ihej\in Z(\mathcal A),\qquad Q^*=Q,\qquad Q^2=u.
\end{gathered}
\tag{55.1}
$$

$Q$ 不要求属于 $E$。原域可不完备、无限维、不可分，也不要求 $X=\mathcal A_{\rm sa}$。$D:E^2\to E$ 始终为同一原总映射，不预付一般可加、齐次、连续、可测、单位平移中性、协变、商下降、完成延拓或一般环境交换子输出闭合。七项物理消费者及其各自全部来源前件完整取61.1；数学包含和实际框架不被当成这些来源已获供应的证明。

为明确全部PB及正读取的用途，对任意原 $a,b,d\in E$，有

$$
\begin{gathered}
\eta=D(a,b)-a\circ d,\qquad \zeta=a\circ b+D(a,d),\\
D(b+\eta,d+\zeta)-D(b-\eta,d-\zeta)
=-2b\circ\eta-2d\circ\zeta,\\
|\phi D(a,b)|^2\le
\phi(a^2)\phi(b^2)-\phi(a\circ b)^2
\qquad(\phi:E\to\mathbb R\text{ 正实线性}).
\end{gathered}
\tag{55.2}
$$

最后一行准确消费运输续卷118.2的同表正读取：准确锥把原二表的正性传给每个数学正泛函，不增添实际准备，不除以读取质量。

**定义 55.2（由原背景内生定义的全部有限窗）。** 固定任意原 $h$-偶自伴 $c\in E$，即 $[h,c]=0$。令 $W(c,h)$ 为所有如下有限和组成的集合：

$$
\begin{gathered}
p=\sum_{k=1}^n q_k,\qquad n\ge0,\qquad q_k\in E,\\
q_k^*=q_k=q_k^2,\qquad q_iq_j=0\quad(i\ne j),\\
cq_k=a_kq_k,\qquad hq_k=\epsilon_kq_k,
\qquad a_k\in\mathbb R,\quad \epsilon_k\in\{1,-1\}.
\end{gathered}
\tag{55.3}
$$

最后两式等价于完全用原Jordan运算书写的 $c\circ q_k=a_kq_k$、$h\circ q_k=\epsilon_kq_k$。确实，对自伴 $b$ 和投影 $q$，若 $b\circ q=\alpha q$，左右乘 $q$ 得 $qbq=\alpha q$，再将原式分别右乘、左乘 $q$ 得 $bq=qb=\alpha q$；反向立即成立。两投影的正交条件也可写成原 $q_i\circ q_j=0$，由同一论证等价于 $q_iq_j=0$。因此55.3及下述共同核只由原 $c,h,E$ 和已知原Jordan运算定义，环境乘法只是其等价读法。

空和是 $0$；允许零投影、重复本征值、重复符号及任意谱重数。非零 $q_k$ 自动有 $|a_k|\le\|c\|$，零投影不限制其标量标签。每个 $p$ 都是原自伴投影，且与 $c,h$ 交换。“实际”只表示这个投影确属同一原 $E$，不表示已生产一个物理准备或测量菜单。投影可以无限秩，也不要求最小。$W(c,h)$ 不依赖 $z,R,D$ 的输出或另选表示；不先选一套总覆盖族，不要求这些投影由 $c$ 的多项式给出，也不借用未在 $E$ 中的环境谱投影。

对原 $p,y\in E$ 定义有限Jordan算子

$$
U_p(y)=2p\circ(p\circ y)-p^2\circ y=pyp.
$$

环境表达式由展开已知乘法取得；左侧保证其值仍在原 $E$。特别对55.3的投影，$U_p$ 是原实线性正压缩。定义同一个窗盲实子空间

$$
K(c,h)=\bigcap_{p\in W(c,h)}\ker(U_p|_E)
=\{y\in E:pyp=0\text{ 对全部 }p\in W(c,h)\}.
\tag{55.4}
$$

称 $K(c,h)=\{0\}$ 为原有限窗分离。它约束全部原 $y$，不只约束待识别的响应。此处 $K(c,h)$ 不同于45–49的辅助交换子值、运输续卷的共享输出以及物理全词合同中的 $K$。这里只使用原实线性读数的共同核，不赋予它Jordan理想、乘法或响应下降的含义。

**定义 55.3（所有强度均保持的同一原余量）。** 对任意原 $h$-奇自伴 $z\in E$、$hz=-zh$，及任意实 $R$，完整复用运输续卷118.3，固定

$$
\begin{gathered}
x=c+z,\qquad k=hc=h\circ x,\qquad
t=D(h,z)=iQhz,\\
g=D(Rh,x),\qquad r=g-Rt\in E,\\
[h,r]=0,\qquad ht=-th,\qquad z\circ t=0,\qquad k^2=c^2,\\
v=c^2\circ r-c\circ(c\circ r)\in E.
\end{gathered}
\tag{55.5}
$$

$r$ 始终来自这一次实际旧输出；没有把 $D(Rh,c+z)$ 拆成两个旧值。$v$ 是同一原Jordan缺陷，不要求它为正。虽然环境中有 $4v=[c,[c,r]]$，$[c,r]$ 一般不是原自伴标签，不能送入55.4的原核。另完整消费118.3已经在第一实际框架下支付的零行

$$
[h,y]=0\quad\Longrightarrow\quad
D(\alpha u+\beta h,y)=0
\qquad(\alpha,\beta\in\mathbb R,\ y\in E),
\tag{55.6}
$$

以及原反对称性和P2给出的零首输入值；不删去这些既有结论上游使用的PB。

## 56. 每个原有限窗消去同一个 Jordan 缺陷

**定理 56.1（不加分离前件的原缺陷定位）。** 在55.1–55.3的完整原条件下，对任意原 $h$-偶 $c$、任意原 $h$-奇 $z$ 及每个实 $R$，同一55.5的 $r,v$ 满足

$$
\boxed{\quad U_p(v)=0\quad(p\in W(c,h)),\qquad v\in K(c,h).\quad}
\tag{56.1}
$$

不要求 $c$ 有限谱、所给窗有全局共同分割、$[c,e]=0$、$[c,z]=0$、谱值孤立或存在总覆盖；不先假定 $[c,r]=0$ 或 $K(c,h)=0$。

证明。零原对象上各项均为零。$R=0$ 时，P2在首平方为零的原输入 $(0,x)$ 上及原评价分离给 $D(0,x)=0$，故 $r=v=0$。以下固定任意非零实 $R$，全程保持同一原 $c,z,x,g,r$。

先说明本卷41.2–41.11的局部生产为何不需要全局有限谱。任选两个正交实际原投影 $q_a,q_b$，满足

$$
\begin{gathered}
cq_a=aq_a,\qquad cq_b=bq_b,\qquad a\ne b,\\
hq_a=\epsilon q_a,\qquad hq_b=\epsilon q_b,
\qquad \epsilon\in\{1,-1\}.
\end{gathered}
$$

若有零投影，则 $q_arq_b=0$ 已成立。非零时，准确沿41.2–41.6取

$$
\begin{gathered}
p'=q_a+eq_ae,\qquad s=u-2p',\qquad H=h\circ s=hs,\\
A=R\epsilon(a+b),\qquad B=R(b-a),\qquad
T=Au+BH,\qquad V=T-2Rhc.
\end{gathered}
\tag{56.2}
$$

这些全是原标签。确实，$eq_ae=2e\circ(e\circ q_a)-q_a\in E$；它位于 $h$ 的 $-\epsilon$ 角，与 $q_a$ 以及 $q_b$ 正交。故 $p'$ 为投影，$ep'e=p'$、$[p',h]=0$，从而 $s^2=u$、$[s,h]=[s,e]=0$。两选中角上有 $Hq_a=-\epsilon q_a$、$Hq_b=\epsilon q_b$。不要求 $s$ 与整个 $c$ 交换。

[中央续卷182.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#182-原系数反射给出的第二份实际框架)于是供应真正旧值 $J_H=D(H,e)=sj$ 和同一取向 $iHeJ_H=Q$。该引理若按182.1的完整参数实例化，可取其背景为 $s$、$\lambda=0,\nu=1,z_0=0$；这只支付新框架，不替换当前目标背景 $c$，也不调用该背景的混合行结论。继而中央163.1在实际框架 $(H,e,J_H)$ 上对全部实 $A,B$ 及原 $y$ 给

$$
P_H^-D(Au+BH,y)=BiQH P_H^-y,
\qquad P_H^-y=(y-HyH)/2.
\tag{56.3}
$$

$B=0$ 也在163.1的范围内。该式是实际旧输出的已付投影，不是换轴协变或首槽齐次假设。

56.2的两角本征等式给 $Vq_a=q_aV=Vq_b=q_bV=0$。因此41.7–41.11准确作用于同一个原三元组 $\operatorname{PB}(Rh,x,T-Rhc)$。为展示其全部局部前件，记这一次的实际外层与右端为

$$
\begin{gathered}
A_+=x+g+R^2c-RhT,\qquad A_-=x-g-R^2c+RhT,\\
D(A_+,T)-D(A_-,V)=\mathcal J,\\
\mathcal J=-2x\circ g-2R^2z\circ c+2Rz\circ(hT).
\end{gathered}
\tag{56.4}
$$

内值 $D(Rh,T-Rhc)=0$ 由55.6支付。41.8的抵消只用 $[h,c]=[h,T]=0$ 和

$$
c\circ(hT)=\frac{hcT+hTc}{2}=T\circ(hc),
$$

没有交换 $c,T$。令 $q=q_a+q_b$，固定同一外值 $\mathscr O=D(V,A_-)$。对每个环境正泛函 $\omega$，$\phi(y)=\omega(qyq)$ 是55.2的合法数学正读取，且 $\phi(V^2)=0$。P2迫使 $\phi(\mathscr O)=0$；全部环境正泛函分离自伴元，故 $q\mathscr Oq=0$。这只读取同一原表，不产生新准备。

另一外值用56.3读取。$q_a,q_b$ 的 $H$ 符号相反，而 $z,t$ 为 $h$-奇，$c,hT$ 在选中两角上对角；所以41.9–41.10逐项给

$$
\begin{gathered}
q_aA_+q_b=q_arq_b,\qquad
q_aD(T,A_+)q_b=iQ\epsilon R(a-b)q_arq_b,\\
q_a\mathcal Jq_b=-(a+b)q_arq_b,\\
\bigl[iQ\epsilon R(a-b)-(a+b)u\bigr]q_arq_b=0.
\end{gathered}
\tag{56.5}
$$

最后一式还消费原反对称性，将56.4左端准确写为 $\mathscr O-D(T,A_+)$。左乘共轭因子并用同一个中央自伴对合 $Q$，正是已刊41.11：

$$
\bigl((a+b)^2+R^2(a-b)^2\bigr)q_arq_b=0,
\qquad q_arq_b=0.
\tag{56.6}
$$

严格正性只用 $R\ne0,a\ne b$。$a+b=0$、$a=0$ 或 $b=0$ 均包含在内。以上局部生产只用了选中两投影的实际性、正交性和本征等式；41.12的全局有限求和尚未使用，所以没有从有限谱定理41.1直接删去前件，也没有假定两个投影是完整本征投影或多项式投影。

现任取 $p\in W(c,h)$ 的任意55.3表示 $p=\sum_{i=1}^nq_i$。在原已知结合环境中直接展开同一个55.5的 $v$：

$$
\begin{aligned}
q_i(c^2\circ r)q_j
&=\frac{a_i^2+a_j^2}{2}\,q_irq_j,\\
q_i\{c\circ(c\circ r)\}q_j
&=\frac{(a_i+a_j)^2}{4}\,q_irq_j,\\
q_ivq_j&=\frac{(a_i-a_j)^2}{4}\,q_irq_j.
\end{aligned}
\tag{56.7}
$$

本征等式的右乘版本来自自伴性。若 $\epsilon_i\ne\epsilon_j$，则55.5的 $[h,r]=0$ 给 $(\epsilon_i-\epsilon_j)q_irq_j=0$。若符号相同而 $a_i\ne a_j$，用56.6。若 $a_i=a_j$，56.7的系数直接为零，不要求重数块内 $q_irq_j=0$。这三类穷尽全部 $i,j$，包括对角项、重复值及零投影。因此

$$
U_p(v)=pvp=\sum_{i,j=1}^nq_ivq_j=0.
$$

空和也为零。对每个原有限窗分别如此，得到56.1。进入55.4交集的始终是原 $v\in E$；未对环境交换子应用原核分离。∎

## 57. 原窗分离的响应识别及其静态供应

**推论 57.1（充分分支、有限谱与任意指标强覆盖）。** 在55.1的完整条件下，若某个原 $h$-偶 $c$ 满足 $K(c,h)=\{0\}$，则对所有原 $h$-奇 $z$ 和每个实 $R$，同一实际旧响应满足

$$
\boxed{D(Rh,c+z)=RiQhz=R\,D(h,c+z).}
\tag{57.1}
$$

该分离有以下两种供应：本卷40.3–40.4的原有限谱背景；或存在任意指标集 $I$ 上的两两正交实际联合本征投影 $q_i\in E$，满足55.3的本征条件，且在某个含单位忠实表示 $\rho:\mathcal A\to B(\mathcal H)$ 中

$$
P_F=\sum_{i\in F}q_i\in E,\qquad
\rho(P_F)\xrightarrow[F\in\operatorname{Fin}(I)]{\rm strong}I_{\mathcal H}.
\tag{57.2}
$$

有限子集按包含有向；允许不可数指标、无限秩角、任意重数及非孤立谱值。不需要物理正评价正规、指定前对偶或 $D$ 的输入正则性。

证明。56.1和 $K(c,h)=0$ 先给同一原 $v=0$。此时才直接应用[运输续卷119.1](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#119-一项原-jordan-二元关系的充要判据)，变量逐项为55.5的原 $R,c,z,x,g,r$，全部前件由55.1完整保留。该定理对这个同一实际余量给

$$
v=0\quad\Longleftrightarrow\quad[c,r]=0
\quad\Longleftrightarrow\quad cr=0
\quad\Longleftrightarrow\quad r=0.
\tag{57.3}
$$

故得57.1第一等号。分离只依赖 $c,h,E$，对同一 $c,z$ 另取 $R=1$ 也适用，得到第二等号；不预付 $D(h,c+z)=D(h,z)$。119.1的共同输出读取、零谱支撑排除和全部正性前件直接消费，不另重证。

有限谱情形直接沿40.3–40.4：$c$ 的有限Lagrange多项式投影与 $(u\pm h)/2$ 的交换Jordan乘积是真正原联合投影，有限和为 $u$。故 $u\in W(c,h)$，而 $U_u=I_E$，从而 $K(c,h)=0$。这只是已付41.1分支在当前记号中的供应；没有以环境谱投影一般属于 $E$ 为前提。

对57.2的供应，固定任意 $y\in K(c,h)$。每个 $P_F\in W(c,h)$，所以 $P_FyP_F=0$。省略表示记号，对每个固定 $\xi\in\mathcal H$，

$$
\begin{aligned}
\|y\xi\|
&\le\|(I-P_F)y\xi\|+\|P_Fy(I-P_F)\xi\|
       +\|P_FyP_F\xi\|\\
&\le\|(I-P_F)y\xi\|+\|y\|\,\|(I-P_F)\xi\|
\longrightarrow0.
\end{aligned}
\tag{57.4}
$$

只用固定有界算子 $y$、$\|P_F\|\le1$ 及静态强覆盖。故 $\rho(y)=0$，忠实性给原 $y=0$。这里没有把 $P_FcP_F$、截断背景或任何输入网送给 $D$；原域也未被替换成强闭包。零对象及空指标的合法情形同样包含。∎

**定义 57.2（充分范围的准确含义）。** 57.2是 $K(c,h)=0$ 的一个静态供应条件；这里不声称原窗分离严格弱于强覆盖，也不给二者必要性或等价性。整个 $W(c,h)$ 可含多套不同有限表示；56.1逐窗成立，不需它们预先构成同一套共同 $e$-交换分割。所选强覆盖族若存在，则所有有限子和已经足够，不要求 $\|u-P_F\|\to0$。

强覆盖允许谱集含聚点：一个谱聚点可以不是本征值，也可以是非孤立本征值；各不同本征值的间距可任意趋零。证明逐对只使用56.6的精确零，不用统一谱隙。相同本征值的重数连接无需归零。若给定族只强和到某个 $P<I$，有限子和对固定 $y\in K(c,h)$ 只给 $P\rho(y)P=0$；其他原窗能否看见余部须另判，不能由这份不完整覆盖宣布 $K=0$ 或 $K\ne0$。

## 58. II₁ 无限谱且无共同交换分割的范围见证

**命题 58.1（分离供应超出有限谱与有限秩原域）。** 存在满足55.1全部静态数学前件的完整原模型，以及满足57.2的无限谱 $h$-偶背景 $c$，使本卷33.1的共同 $h,e$ 交换分割不存在，且 $c\notin Z(\mathcal A)_{\rm sa}+Z(\mathcal A)_{\rm sa}h$。该模型不具配平三角续卷142.1、152.1、157–160、167–174各自要求的有限全矩阵、完整有界type I、全部原有限秩或本质复紧理想结构。本命题只给57.1分支的相容范围见证，不给任意II₁原总响应的全域分类。

证明。取具有可分迹GNS空间的超有限II₁因子 $\mathcal R$，带忠实正规归一数学迹 $\tau$，在其迹GNS空间 $\mathcal H_\tau$ 上忠实正规表示。使用成熟的II₁投影维数与比较理论，在逐步余投影内选非零正交 $d_n\in\mathcal R$，使

$$
\tau(d_n)=2^{-n},\qquad
\sum_{n\ge1}^{\rm strong}d_n=1.
\tag{58.1}
$$

确实，有限和的余投影迹为 $2^{-N}$；投影上确界存在，迹正规性及忠实性使最终余投影为零。再选 $f_1\le d_1$、$\tau(f_1)=1/4$，令 $f_2=d_2$。等迹投影等价，故有部分等距元 $v_0\in\mathcal R$ 满足

$$
v_0^*v_0=f_1,\qquad v_0v_0^*=f_2,
\qquad f_1f_2=0.
$$

令 $p_0=f_1+f_2$，并取酉元

$$
w=(1-p_0)+\frac{p_0+v_0-v_0^*}{\sqrt2}.
\tag{58.2}
$$

在 $p_0$ 角内，$v_0-v_0^*$ 斜自伴、平方为 $-p_0$，故58.2在此角为酉；补角为单位。令 $\lambda_n=1/n$，定义

$$
c_+=\sum_{n\ge1}\lambda_nd_n,\qquad
c_-=wc_+w^*,\qquad c=\operatorname{diag}(c_+,c_-).
\tag{58.3}
$$

第一式范数收敛，尾范数为 $1/(N+1)$。每个 $d_n\mathcal H_\tau$ 上取值 $\lambda_n$，故所有 $1/n$ 在谱中，谱闭性加入 $0$；闭集外的逆由有界倒数系数在这些正交角上定义，故

$$
\sigma(c_+)=\sigma(c_-)=\sigma(c)=\{1/n:n\ge1\}\cup\{0\}.
\tag{58.4}
$$

总覆盖和各 $\lambda_n\ne0$ 给 $\ker c_+=0$，故 $0$ 是非本征谱聚点。这个范数和只在所选完整模型内定义已知自伴元，不对未知响应取输入极限。

$p_0$ 减约 $c_+$ 和 $c_-$，并且

$$
\begin{gathered}
p_0c_+p_0=\lambda_1f_1+\lambda_2f_2,\\
p_0c_-p_0=\frac{\lambda_1+\lambda_2}{2}p_0
 +\frac{\lambda_1-\lambda_2}{2}(v_0+v_0^*),\\
p_0[c_+,c_-]p_0
=\frac{(\lambda_1-\lambda_2)^2}{2}(v_0^*-v_0)\ne0.
\end{gathered}
\tag{58.5}
$$

最后的非零性可由 $f_1(v_0^*-v_0)f_2=v_0^*\ne0$ 直接读取。

现在取完整原域及实际框架

$$
\begin{gathered}
\mathcal A=M_2(\mathcal R),\qquad E=X=\mathcal A_{\rm sa},\qquad u=1_{\mathcal A},\\
h=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
e=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
j=\begin{pmatrix}0&i\\-i&0\end{pmatrix},\\
S(a,b)=a\circ b,\qquad D_*(a,b)=i[a,b]/2.
\end{gathered}
\tag{58.6}
$$

矩阵各条目均乘 $1_{\mathcal R}$。锥和范数取标准算子锥及算子范数；原评价族取全部正实线性泛函，包括它们的全部非负质量倍数、零、不等和次归一质量，不排除奇异泛函。它们分离元素并准确决定锥。$E$ 是实Archimedean序单位空间；$D_*$ 对全部原对有自伴输出且在原域内。

全部A1–A3/P2/PB的对应准确复用[原多项式零响应卷6.6–6.7](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md#6-四份独立平方根预算的严格正下确界)的标准乘法身份，系数代数取当前 $\mathcal A$：$S-iD_*$ 就是 $ab$，两条有向二表为正Gram表；相加三表的实部为实Gram表，指定相加零向量仍为零。$0\le a\le\vartheta_0u\le u$ 给 $a^2\le a$，所以同一固定小窗的A3成立。对全部原自伴 $A,B,C$，记 $Z=B+iC$，PB的实际外层 $r_\pm,s_\pm$ 满足

$$
r_\pm+i s_\pm=(u\pm iA)Z,\qquad
r_\pm^2+s_\pm^2+2D_*(r_\pm,s_\pm)=Z^*(u+A^2)Z.
\tag{58.7}
$$

两份平方完全相同，故完整PB作为原元素恒等式成立，对全部正评价及全部质量也成立。直接相乘有 $D_*(h,e)=j$、框架各平方为 $u$、两两Jordan正交、$Q=ihej=u$。这些身份只核对见证模型的数学前件，不把标准 $D_*$ 代入56.1中的任意未知响应。

在 $\mathcal H_\tau\oplus\mathcal H_\tau$ 上的含单位忠实表示中，原投影

$$
q_{+,n}=\operatorname{diag}(d_n,0),\qquad
q_{-,n}=\operatorname{diag}(0,wd_nw^*)
\tag{58.8}
$$

彼此正交，满足 $cq_{\pm,n}=\lambda_nq_{\pm,n}$、$hq_{\pm,n}=\pm q_{\pm,n}$，强和为单位。因此57.2成立，$K(c,h)=0$，但58.4的背景谱无限。可取 $z=e$ 为非零真正混合输入；57.1仍允许任意原奇 $z$。若改取 $\lambda_1=0$、$\lambda_n=1/n$（$n\ge2$），其他构造完全保持，则 $0$ 成为非孤立本征值，58.5仍非零，也仍有总覆盖。两种情形分别包含非本征聚点和非孤立本征值。

若存在33.1的共同 $h,e$ 交换投影分割，则每个分割元都为 $\operatorname{diag}(b_\ell,b_\ell)$：与 $h$ 交换先给块对角，与 $e$ 交换再使两块相同。33.1的背景式遂使 $c_+,c_-$ 都是同一正交投影族 $b_\ell$ 的实线性组合，因而相互交换，与58.5矛盾。即使允许该类投影有任意指标强总覆盖，只要两块在每格上为标量，二者仍在稠密角和上交换，有界性使全交换，结论相同。$\mathcal A$ 又是因子，自伴中心为 $\mathbb Ru$，而 $Z(\mathcal A)_{\rm sa}+Z(\mathcal A)_{\rm sa}h$ 的上下块各为标量；58.4排除 $c$ 属于其中。

最后明确原域结构的区别。II₁因子及其有限矩阵放大没有非零最小投影，每个非零角仍为II₁型。若某个忠实Hilbert表示中有非零有限秩投影 $q\in\mathcal A$，有限维 $q\mathcal A q$ 的最小投影便也是 $\mathcal A$ 的最小投影，矛盾；非零紧算子的模还会由非零孤立谱值产生这种有限秩投影，故该表示中 $\mathcal A\cap K(\mathcal H)=0$。这里的Murray–von Neumann有限投影绝非有限秩投影。

若 $X$ 有非零Jordan理想 $I\cong_J K(H)_{\rm sa}$，取其中对应秩一的投影 $p$。理想性给 $U_pX\subset I$；$U_p$ 在其像上为恒等，故 $U_pX\subset U_pI=\mathbb Rp$。这将给出 $X$ 的最小Jordan投影，与II₁角矛盾。因此167.1所需的本质复紧理想亦不存在。有限全矩阵142.1、完整有界type I原域152.1、全部单块有限秩157.1及本质紧理想167.1的结构前件都没有被此见证暗中供应。

更强地，$\mathcal A$ 没有非零有限维 $*$-表示，连不要求正规的表示也没有。II₁比较理论给任意大的含同一单位 $M_m(\mathbb C)\subset\mathcal A$。若 $\pi:\mathcal A\to M_k(\mathbb C)$ 非零，令 $r_0=\operatorname{rank}\pi(u)>0$，取 $m>r_0$。该 $M_m$ 的 $m$ 个等价正交对角投影之像均为等秩非零投影，和为 $\pi(u)$，将要求 $r_0\ge m$，矛盾。故本例也不借有限维表示族分离原域。这个模型只证明所写无限谱分支真实非空，并未生产七项实际物理来源。∎

## 59. 连续谱模型中分离失败而目标响应仍成立

**命题 59.1（原有限窗分离的非必要性）。** 存在满足55.1全部静态数学前件的标准连续谱模型，具有非零原域及原 $h$-偶背景 $c$，使

$$
W(c,h)=\{0\},\qquad K(c,h)=E,
\tag{59.1}
$$

但对每个原 $h$-奇 $z$ 及每个实 $R$，57.1的目标公式成立。故 $K(c,h)=0$ 是该识别的一条充分分支，不能作为目标公式的必要条件或普遍新量子公理。

证明。取Lebesgue测度的 $H_0=L^2([0,1],dt)$，令 $M_f$ 表示乘以 $f$ 的算子，置

$$
\begin{gathered}
\mathcal H=H_0\oplus H_0,\qquad
\mathcal A=B(\mathcal H),\qquad E=X=\mathcal A_{\rm sa},\\
h=\operatorname{diag}(I,-I),\qquad
e=\begin{pmatrix}0&I\\I&0\end{pmatrix},\qquad
j=\begin{pmatrix}0&iI\\-iI&0\end{pmatrix},\\
c=\operatorname{diag}(M_t,M_{t^2}),\qquad
S(a,b)=a\circ b,\qquad D_*(a,b)=i[a,b]/2.
\end{gathered}
\tag{59.2}
$$

单位、锥、范数及全部正实线性评价取58.6的同一标准约定，含全部质量与奇异评价。58.7是任意含单位C*代数的乘法身份，因此逐全部原输入给这里的A1–A3、P2与完整PB。直接计算仍有 $j=D_*(h,e)$、$Q=u$、全部实际框架等式，且 $[h,c]=0$。

对任意实数 $a$，$\{t:t=a\}$ 与 $\{t:t^2=a\}$ 均为零测集，所以

$$
\ker(M_t-aI)=\ker(M_{t^2}-aI)=0,
\qquad \ker(c-au)=0.
\tag{59.3}
$$

两乘法算子的谱均为 $[0,1]$：区间外的倒数为有界乘法逆；对区间内每个 $a$，取支撑于 $|t-a|<\delta$ 或 $|t^2-a|<\delta$ 的归一函数给近似本征向量。这些支持在任意 $\delta>0$ 时有正测度，故不能有有界逆；59.3又排除点谱。因而这是无点谱的连续谱背景。

若实际投影 $q\in E$ 满足 $cq=aq$，其像便包含于59.3的零核，所以 $q=0$；这甚至不必使用 $h$ 本征条件。55.3只可能由零投影组成，故 $W(c,h)=\{0\}$、$U_0=0$，得到59.1，且 $E\ne0$。

另一方面，这份标准模型中的已知 $D_*$ 可直接计算：

$$
D_*(Rh,c+z)=\frac{iR}{2}[h,c+z]
=\frac{iR}{2}[h,z]=Rihz=RiQhz,
\qquad D_*(h,c+z)=ihz.
\tag{59.4}
$$

这里只对已指定的标准响应展开双线性，不转用于56.1的未知原映射。因此同一模型中所有目标余量 $r$ 和缺陷 $v$ 本来为零，而窗盲子空间却为整个 $E$。这反驳的是“目标公式成立必有原窗分离”，并非完整PB反例，也不是非零实际PB余量的构造。∎

## 60. 原缺陷定位的来源与各类盲区的区别

**定义 60.1（承重综合及直接复用）。** 56.1及其57.1消费归为 $\texttt{repo-derived}$：实际两角PB生产、原缺陷56.7与全部原有限窗的共同核接成同一实际响应的定位。这里不把56.7的代数展开、共同核定义或成熟谱工具单独计为新发现。本卷40–44已付有限谱分支，41.2–41.11的实际两角生产原样消费；运输续卷118.1–118.3给完整原条件、第一框架零行及固定输出，119.1只在同一 $v=0$ 后消去同一 $r$；中央182.2及163.1给实际反射框架和同一 $Q$ 的横向读取。

本卷45–49处理有限商内二次第三标签与秩一连接的幅度条带，其辅助 $K$、预算及代表量词不等于55.4的原共同核。它没有替代这里对任意实际联合本征角的局部PB接线。运输续卷134–137保留尖锐态夹读的完整方差预算，并给整个指定有限夹读族遗漏非零紧理想的模型；那里检测的是指定标量读数，59.1这里则由原背景没有非零本征投影而使原压缩窗集合只剩零。两类非分离都不产生非零实际PB余量，不能相互代付一般 $v=0$ 的生产。

配平三角续卷142.1、152.1、157–160、167–174的全域旧表分类保持各自结构前件。58.1只说明当前背景范围超出有限谱和那些有限秩／type I／紧理想前件，不把这些既有全域结论重列为新结果。59.1使用完整type I标准模型证明分离非必要，也没有扩展任意连续谱未知旧表的识别。

**定义 60.2（成熟数学的准确归属）。** 下列工具均为 $\texttt{literature-attested}$ 的中间步骤，来源取Blackadar，[*Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)的相应条目，不赋予本组新的谱论或因子理论名义。

| 成熟工具 | 原来源与当前参数范围 |
| --- | --- |
| 强算子拓扑、固定有界算子的静态分离 | I.3.1、I.3.2.1及III.1.1.1；正交投影任意族取有限部分和网。57.4另由定义直接给出所需估计，不要求旧 $D$ 连续，也不将表示强覆盖变成物理正常性。 |
| 自伴谱、多项式投影、非孤立谱值与本征空间 | I.4.1、I.6.1及II.2.3；有限谱原标签准确沿本卷40.3，58.3–58.4和59.3按显示的模型直接计算。一般Borel谱投影没有原标签资格。 |
| 正泛函分离及准确锥读取 | II.6.3.1、II.6.3.3、II.6.3.5及运输续卷118.2；56.4读取的是原表，零质量无需归一。 |
| II₁连续投影维数、指定子投影和等维等价 | III.1.1.2、III.1.7.3–III.1.7.6、III.1.7.9–III.1.7.10；58.1选用可分Hilbert空间上的超有限II₁实例，满足III.1.7.9明确的可数可分解范围。投影比较与部分等距沿Murray–von Neumann理论，不作为新构造原理。 |
| 忠实正规数学迹、II型边界与因子实例 | III.2.5.6–III.2.5.7、III.1.4.4–III.1.4.7及III.3.1、III.3.4。58.1只在见证模型的迹中用正规性；全部原物理评价并未被限制为正规。 |
| 矩阵单位与有限因子的表示边界 | III.1.5.1、III.2.5.4(iii)及III.1.7.11(i)；58.1另以任意大含单位矩阵子代数直接排除有限维表示，以最小投影排除紧理想前件。 |
| 标准响应的全原正表与PB | 原多项式零响应卷6.6–6.7的同一C*乘法身份；58.7及59.2只作系数代数对应，标准模型不替代一般未知原 $D$。 |

上述文献支持成熟工具和模型材料；本组仅主张所写条件下的仓内综合，不主张历史优先权、文献穷尽或外部开放问题结算。

## 61. 七项完整同源合同与未付的量子桥梁

**定义 61.1（全部上游量词合取保留）。** 本卷43.2及[中央续卷199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#199-来源几何与量子消费者的完整边界)第1、2、3、4、5、6、7项逐项全文作为本定义的组成部分，连同其完整纳入的[194.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#194-新连接完整候选与量子消费者的范围)、[186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#186-七项原量子来源合同的准确消费者)、运输续卷122.1及各项所有上游来源、对象、条件和量词一并合取保留。不以以下定位说明替代这些全文合同，不更换原世界，也不将其中尚未取得的充分前件作为已成立事实。

1. 复Hilbert、可观测量与相干叠加：同一原 $\Omega/\mathrm{native}$、跨评价配对、全词同一 $K/J/q$、parent/ready、可取得标签、合法控制及实际相干准备保持全部原合同。56.1只定位一条原响应的缺陷，57.1只在分离背景上认回实际行；一般旧全域双线性、全有限复Gram、同一旧结合乘法与完成运输支付后才接完整Hilbert／叠加消费者。忠实表示、数学本征空间及临时反射不供应全 $B(H)$ 可取得性、原完备性或实际准备。
2. 原态、效果、质量与Born：原评价、原事件、准确效果区间、全部实际完整菜单和接受归属不变；共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、P9、独立 $W_e$、全部原中间切口及固定支持全质量仍取原来源。零、不等、次归一质量、原 $q$、中心权、中心经典混合、经典不等维和静默块全部保留。只对该实际完整菜单的严格正总质量归一；数学压缩读取不增加准备，强覆盖不赋予无限菜单可加性。
3. 真正相关联合、native与张量：同一个实际非零相关联合、全词 $K/J$、交叉零、忠实同向交换局部腿、共同实现、联合生成分离、所需重数、全部真正相关输入、中央对、经典及不等维块和递归同源参考保持。只有这些共同来源及其原前件取得后才接张量消费者；$q_a+eq_ae$ 是同一对象内的数学反射构造，不供应实际子系统，相同边缘与分别可达不替代真正联合。
4. typed CP、Kraus与整台递归参考：原未归一回溯、每个合法typed前后接、反变合法复合、typed分区、全未来自然性和原箭头商下降不变。同源参考仍覆盖系统、整个环境、全部成功／失败／细记录／port／post-port输出及每份输出的每个仍合法未来；三实际投影、各自支持内补、共同真实支持、忠实同向交换、全部相关正输入的intertwining与夹界、每个所需有限递归深度及累计支持的准确运输完整保持。这些前件支付后才接CP和Kraus；55.4的原正压缩与57.2的数学总覆盖不供应实际箭头或参考。
5. 整台仪器、TP、更新与Lüders：原输入运输、完整typed菜单、原接受端、整个环境及全部输出未来、真正分组遗忘、AC、精确 $N_u$、$X/X_s$、原平方根词及接受条件均保持。TP需完整单位分区，Lüders需同一完整输出的像内射线校准；只归一正输出，零分支保留。密度、迹类和算子Kraus公式只在准确合格的有限全矩阵域，或另已供应所需正规物理表示、指定前对偶及适用收敛接口的域消费。58.1的数学迹和59.2的完整算子域不替一般原模型支付这些条件。
6. 全部历史、全未来、真实返回与CountRead：所有合法顺序／自适应／并行历史、每份输出的每个仍合法未来、整个环境及细记录泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧和逆向真实双向返回全部保留。CountRead仍绑定读后同一原完整活动输入及全未来返回；负提升两条活路的分别控制、相干聚合、具名分析词到原完整菜单及接受端接线保持。精确正生成 $B$ 与闭正生成 $B_{\rm cl}$ 不混同，原 $q$-零集、AC方向及实际读取次序不由矩阵相同而等同。无限历史、无限／非离散记录的可数可加、正常性和指定前对偶仍取各自来源，不能由57.4的数学有限子集网推出。
7. 动力、物理钟、能量与共同尺度：同一旧全域乘法、保持可能不完备原域的流、真实相位与门序列、可逆一参数群、原物理钟、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同作用量、共同正 $\hbar$ 和共同仪器均保持。原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 预算继续取原合同含义，不与临时反射 $s$、当前余量 $r$ 混淆。数学谱值、强度 $R$、中央 $Q$ 和静态强覆盖不供应物理时间、能量、可控相位、控制成本或一般无界生成元。

**定义 61.2（已定位的同一缺口与其余原目标）。** 完整候选仍为同一原A1–A3、全部P2及全部PB，没有以有限窗分离替换原关系，也没有减少全局独立公理数。56.1对每个背景定位同一原缺陷为 $v\in K(c,h)$；57.1在 $K(c,h)=0$ 的充分分支关闭原混合行，58.1提供超出有限谱的真实供应，59.1说明该供应不是目标公式的必要条件。

对一般 $K(c,h)\ne0$ 的背景，仍须从原PB生产同一实际 $v=0$，或另给能消去其实际余部的关系。$K\ne0$ 本身既不证明 $v\ne0$，也不证明存在这样的完整PB响应；59.1中实际 $v=r=0$ 而 $K=E$。一般具有非零连续谱部分的未知原响应、无实际框架的原域、任意首标签、一般旧可加性与双线性、全有限旧复Gram、原R、同一旧全域结合乘法、完整原完成运输及完整量子物理起源仍保留各自未付桥梁。不对截断输入的 $D$ 取极限，不假定所有背景均有分离窗，不把数学窗当作测量菜单；这些限制不否定其他保留完整原关系的生产路线。

## 62. 同一个缺陷与所有有限窗的完整中文图景

**定义 62.1（原关系、有限窗及充分分支的含义）。** 同一原世界仍由两两有方向的正比较、相加三角、单位小窗和全部三标签正反配平约束。固定实际存在的三根轴，把第二输入分成保持 $h$ 两侧的背景 $c$ 和跨侧连接 $z$。横向输出已经知道，尚未识别的是同一次旧输出里的偶余量 $r$，不能把混合输入的响应擅自拆成两份响应相加。

这里问的不是能否先把整个背景分解成有限个格子。只要某个格子真在原域中，并且背景与 $h$ 在格子内各取一个确定数值，它就可成为原有限窗的一部分。每次从任意两个同侧而数值不同的实际格子出发，利用已有 $e$ 把一格搬到另一侧，造一面临时反射。新轴的实际旧值及取向由既有关系取得；同一次完整PB的一张外表在这两格上有零平方预算，另一张外表则由新轴的已知横向公式读取。两张表约束的是同一个旧输出，因而两个不同背景数值之间的余量连接必须为零。这项局部生产不关心还有多少其他格子，也不要求临时反射保持整个背景。

不同 $h$ 侧之间的余量连接本来已经为零；同侧同值的连接则不必消失，因为它不妨碍余量与背景交换。为把这几类结论合在原域中，检查的对象不是未必属于原域的环境交换子，而是“先拿背景平方比较余量”与“连续两次拿同一背景比较余量”之差，即固定原缺陷 $v$。两格数值相同时，这个差自动为零；数值不同时，局部PB已经消去了所需连接。于是每个原有限窗都压不出这同一份缺陷，它只能落在所有有限窗共同看不见的原实子空间 $K(c,h)$ 中。这就是对任意背景已经取得的定位，尚不等于每个背景的缺陷都为零。

如果所有这些原窗合起来能区分原域每一个元素，共同盲区只有零，缺陷便为零；随后既有运输判据才把整份实际余量消去。有限谱是原有的一种供应，因为有限多项式格子已经铺满单位。无限多个实际正交本征角若在一个忠实表示中共同覆盖全部向量，也供应分离：只让一个早已固定的有界原元素作用于向量，有限格子和便足以识别它为零。没有把越来越精细的背景送进未知响应，没有假定响应连续，没有把数学强收敛变成物理态的正常性。

II₁见证说明这样的格子可以全都无限秩，背景可以有无限多个数值和谱聚点，上下两侧还可以没有共同的 $e$-交换分割；因此原有限窗方法不限于有限矩阵或有限谱。连续谱见证又说明这条分离要求不能变成普遍量子公理：乘以 $t$ 或 $t^2$ 的背景没有任何非零本征格子，所有这类窗只剩零，标准响应却仍然完全满足目标公式。窗的看不见不等于实际响应有错，它只暴露这条识别方法仍缺哪种关系。

实际准备、完整Born菜单与全部原质量、真正相关联合、整台仪器及环境全部输出未来、递归同源参考、完整历史和真实双向返回、无限记录、保持原域的动力、物理钟、能量与共同作用量，继续逐项承担61.1的完整来源合同。数学窗定位了同一响应的一份缺陷，尚未把这些量子公理的全部物理来源一并生产出来。

## 追加锚（本行以下为增补区）

## 63. 固定原世界、总响应及准确来源

**定义 63.1（来源、记号与承重范围）。** 下列缩写只用于指明数学来源；SM 指本卷。

| 缩写 | 准确来源及采用的接口 |
| --- | --- |
| OP | [《原多项式零响应与 Cayley 原域边界》](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md)，3.1 的原多项式零值、80.1–80.2 的全部实际二阶角、82.1 的同块共同符号、83.1 的秩一小连接原像行、84–85 的已付与未付商接口。 |
| SM | 本卷 50–54 的完整原候选、实际多项式两射线网络、共同余量方程及半定消费者；43.2、49.1、61.1 的全部来源合同。55–62 的原窗识别保留实际原框架、原投影和分离条件。 |
| PB | [《配平三角的共同取向与秩一响应续卷》](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)，128.1–128.2 的全原关系、129.1 的数学正读取、142.1–143.1 的完整有限原域识别、240–241 的有限商与实际原像接口。 |
| C | [《中央响应平方与径向一致续卷》](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)，199.2、194.2、186.1–186.7 的七项同源合同及其全部上游对象、条件、来源与量词。 |
| PT | [《原多项式 PB 输运与纤维边界续卷》](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md)，118–122 的实际框架入口、原响应运输与完整来源边界，以及 126–133 的有限读取和虚拟反射边界。 |

64.3 的承重综合归为 $\texttt{repo-derived}$：准确消费 OP83.1 的原像接口，将同一实际 PB 网络接到带任意自伴旁观块的不定首像。有限谱分解、Hermitian 极化、Pauli 乘法和 Sylvester／Lyapunov 方程只作为成熟内部工具；它们不各自取得新定理或量子公理的名义。有限自伴谱分解沿 SM60.2 所引 Blackadar 的 I.4.1；Hermitian 极化、Pauli 乘法及行列式在 65–66 中只作内部计算。Sylvester／Lyapunov 判据的成熟出处附于 67.3，不主张历史优先权、文献穷尽或外部开放问题结算。

**定义 63.2（完整原前件）。** 固定 SM50.1、OP80.1 与 PB128.1 的同一原 $\Omega/\mathrm{native}$、$E,C,u,N,\mathcal P,S,D$，完整保留：

- A1：全部原有向 Hermitian 二表正性；
- A2：每份相加三表 $(a+b,a,b)$ 及其排列的实部在整个 $\mathbb R^3$ 上半正定，并保留指定相加零向量 $(1,-1,-1)$ 的零二次值；
- A3：$S(u,u)=u$，并对同一个固定有理数 $0<\theta\le1$ 要求 $0\le e\le\theta u\Rightarrow S(e,e)\le e$。

原正实线性评价分离 $E$，准确决定原锥，全部质量 $m_\gamma=\gamma(u)$ 允许零、不等和次归一。消费既有无原 R 的 Jordan 接口

$$
E\subset X,\quad \overline E=X,\quad C=E\cap X_+,\quad
S(a,b)=a\circ b,\quad N=\|\cdot\|_X|_E,
\qquad \pi:X\longrightarrow H_n(\mathbb C),\quad n\ge3.
\tag{63.1}
$$

其中 $X$ 是含单位实 JB 完成，$E$ 是含单位稠密实 Jordan 子代数，$\pi$ 是满含单位 Jordan 同态。$E$ 可以无限维、不完备。$D:E^2\to E$ 是同一个未知总映射；反对称性由原 Hermitian 性和分离性取得。全部原 P2 是

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(a\circ b)+i\gamma D(a,b)&\gamma(b^2)
\end{pmatrix}\succeq0
\qquad(a,b\in E,\ \gamma\in\mathcal P).
\tag{63.2}
$$

完整原 PB 保持为对每个实际 $a,b,c\in E$ 和每个原 $\gamma$，

$$
\begin{gathered}
v=D(a,b)-a\circ c,\qquad w=a\circ b+D(a,c),\\
r_\pm=b\pm v,\qquad s_\pm=c\pm w,\\
\gamma\bigl(r_+^2+s_+^2+2D(r_+,s_+)\bigr)
=\gamma\bigl(r_-^2+s_-^2+2D(r_-,s_-)\bigr).
\end{gathered}
\tag{63.3}
$$

其由原评价分离性得到的等价元素式为

$$
D(b+v,c+w)-D(b-v,c-w)=-2b\circ v-2c\circ w.
\tag{63.4}
$$

不是只对本文使用的三元组要求 PB。C199.2、C194.2、C186.1–186.7 的逐项全文及全部上游量词，与 SM43.2、SM49.1、SM61.1 的全部来源合同共同作为本定义的组成部分；69 逐项说明消费者边界。本文不预付 $D$ 的一般齐次、可加、连续、可测、协变、单位平移、商下降、输出小代数闭合或完成延拓，也不从商内投影制造实际原投影或原框架。

沿 OP80.2、OP82.1 固定这一简单块的同一符号 $\sigma\in\{1,-1\}$。只定义数学辅助运算

$$
K(U,V)=\frac{\sigma i}{2}[U,V],\qquad
U\circ V=\frac{UV+VU}{2}.
\tag{63.5}
$$

$K$ 尚不是全域旧响应，也与原全词合同中的同名字母区分。以下向量范数为欧氏范数，矩阵范数为算子范数。

## 64. 小窗口只看跨射线连接

**定义 64.1（射线连接及已有原像接口）。** 对数学单位向量 $e$，记 $p=ee^*$、$q=I-p$。任意自伴 $X$ 唯一分解为

$$
X=\beta p+(ze^*+ez^*)+qXq,
\qquad \beta=e^*Xe,\quad z=qXe.
\tag{64.1}
$$

直接沿用 OP83.1：其严格条件是 $\|z\|<2$。若实际标签 $y,x\in E$ 满足 $\pi y=\mu p$、$\pi x=X$，则它对任意实 $\mu$、任意 $\beta$、任意自伴 $qXq$ 和所有同像实际代表给

$$
\pi D(y,x)=\mu\bigl(we^*+ew^*\bigr),\qquad
w=-i\sigma z/2,
\tag{64.2}
$$

也就是 $K(\mu p,X)$。交换两槽，原反对称性给 $\pi D(x,y)=K(X,\mu p)$。非零秩一像可有任意符号和幅度；$\mu=0$ 的零像由原 P2 处理。严格阈值二不乘以 $|\mu|$，不约束 $\|X\|$，不要求实际 $y$ 是某个原投影的倍数。对角项和旁观块可以任意大。

SM51.2 的实际两条外行是

$$
X_\pm=R\mp d\mp AF,\qquad Y_\pm=F\pm R\circ A,
\quad d=\pi D(r,a),\quad c=f(a),\quad F=f(A).
\tag{64.3}
$$

只要 $Y_\pm=\mu_\pm p_\pm$ 为非零秩一像，OP83.1 分别消费

$$
\|q_\pm X_\pm e_\pm\|<2,
\qquad p_\pm=e_\pm e_\pm^*,\quad q_\pm=I-p_\pm.
\tag{64.4}
$$

SM 的式 (50.3) 中，整体范数预算是保证这两条连接界的一种充分估计；这里仅将它作为充分预算使用。以下不改变 OP83.1，只准确支付 64.4。

**定义 64.2（尺度化第二标签族）。** 令 $m=n-2\ge1$，在固定数学商坐标内置

$$
Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
T=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\qquad P=I_2\oplus0_m.
$$

取实 $\alpha,t,s$ 满足 $\alpha ts\ne0$，以及任意自伴 $B\in H_m(\mathbb C)$，记

$$
\begin{gathered}
A=sZ\oplus0_m,\qquad R=(\alpha Z+tT)\oplus B,
\qquad F=\alpha A,\\
b=\|B\|,\qquad L=\|R\|=\max\{\sqrt{\alpha^2+t^2},b\},\\
\mathfrak b_0=|t|+|s|L,\qquad
\mathfrak b_1=\sqrt{|t|^2(1+|s|)^2+s^2b^2/4}.
\end{gathered}
\tag{64.5}
$$

对每一对实际 $r,a\in E$ 满足 $\pi r=R,\pi a=A$，第三标签始终取实际 $c=\alpha a$。这里改变 $s$ 是选择另一个实际输入的像，不是对未知旧响应作齐次搬运。

**定理 64.3（同一原响应的两种充分连接预算）。** 在 63.2 的全部原前件下，对 64.2 的任意参数、任意自伴 $B$ 和全部符合像条件的实际代表，只要以下任一条件成立，

$$
\boxed{\mathfrak b_0<2\quad\text{或}\quad\mathfrak b_1<2,}
\tag{64.6}
$$

就有

$$
\boxed{\pi D(r,a)=K(R,A)=\sigma stY\oplus0_m.}
\tag{64.7}
$$

$B$ 无正负性、非奇异性、谱隙或无相反谱要求。$R$ 是不定首像。定理没有要求 $R-i\sigma F$ 全谱非共振。第一预算为 $|t|+|s|\|R\|<2$；第二预算是同一原 P2 的较局部读取，消去 $\alpha$ 的依赖。两者都是充分条件，本文不宣称第二个在全部参数上小于第一个，也不宣称其中任一为完整原 PB 的必要条件。证明分为 65–66 两节。

## 65. 同一 P2 支付连接与旁观零压缩

**证明（64.3，同一原二表的读取）。** PB129.1 由准确原锥推出每个数学正泛函均可读取同一 P2。对任意 $\xi\in\mathbb C^n$，将向量正泛函经 $\pi$ 拉回原域，得到

$$
|\xi^*d\xi|^2
\le(\xi^*R^2\xi)(\xi^*A^2\xi)
-(\xi^*(R\circ A)\xi)^2.
\tag{65.1}
$$

没有把这个数学读取新增为实际准备，也没有归一任何原质量。对单位向量丢去右端的非负平方项给

$$
\|d\|\le\|R\|\|A\|=|s|L.
\tag{65.2}
$$

对 $\xi\in\ker A$，65.1 的第二平方对角为零，故 $\xi^*d\xi=0$。在该子空间作 Hermitian 极化给

$$
q_A d q_A=0,\qquad q_A=0_2\oplus I_m.
\tag{65.3}
$$

同样还可得 $q_Rdq_R=0$，其中 $q_R$ 是 $\ker R$ 的数学正交投影；以下真正消去任意 $B$ 的是第二槽的 65.3，不把第一槽的核压缩冒充它。数学核投影不作原标签。

直接计算

$$
C_0=R\circ A=\alpha sP,\quad
Y_+=F+C_0=2\alpha sE_{11},\quad
Y_-=F-C_0=-2\alpha sE_{22},\quad
AF=\alpha s^2P.
\tag{65.4}
$$

因为 $\alpha s\ne0$，两条 $Y$ 均非零秩一，分别取 $e_+=e_1,e_-=e_2$。相对于 $p_+=E_{11}$ 和 $p_-=E_{22}$，$AF$ 都没有跨射线连接，并且

$$
\|q_+Re_1\|=\|q_-Re_2\|=|t|.
\tag{65.5}
$$

故对于式 (64.3) 的两份实际 $X$，

$$
\|q_\pm X_\pm e_\pm\|
\le |t|+\|d\|\le |t|+|s|L=\mathfrak b_0.
\tag{65.6}
$$

这已经完整证明第一充分预算，常数二和任意秩一幅度准确沿 OP83.1，不需要 $\|X_\pm\|<2$，也不需要计入 $\|AF\|$。

**证明续（64.3，完整 Gram 减项）。** 为准确支付第二预算，按 $\mathbb C^2\oplus\mathbb C^m$ 写

$$
d=\begin{pmatrix}d_2&G\\G^*&0\end{pmatrix},\qquad d_2=d_2^*.
\tag{65.7}
$$

右下零块就是 65.3 的原结论，尚未利用 PB 认回 $d$。对任意 $x\in\mathbb C^2,y\in\mathbb C^m$，65.1 给出完整不等式

$$
\begin{aligned}
|x^*d_2x+2\operatorname{Re}(x^*Gy)|^2
&\le\Delta(x,y)\\
&=\bigl((\alpha^2+t^2)\|x\|^2+\|By\|^2\bigr)
 s^2\|x\|^2-\alpha^2s^2\|x\|^4\\
&=s^2t^2\|x\|^4+s^2\|x\|^2\|By\|^2.
\end{aligned}
\tag{65.8}
$$

这里 $\alpha$ 的消失来自同一准确 Gram 行列式的减项，不能从丢弃该项的粗范数界读取它。取 $y=0$ 给

$$
|x^*d_2x|\le |st|\|x\|^2,
\qquad \|d_2\|\le |st|.
\tag{65.9}
$$

对固定 $x,y$，将同一读取向量换成 $(x,\tau e^{i\vartheta}y)$。由于 65.7，左端是

$$
\bigl(x^*d_2x+2\tau\operatorname{Re}(e^{i\vartheta}x^*Gy)\bigr)^2,
$$

右端为 $s^2t^2\|x\|^4+s^2\tau^2\|x\|^2\|By\|^2$。此二次多项式不等式对每个实 $\tau$ 成立，所以二次项系数必须满足

$$
4\bigl(\operatorname{Re}(e^{i\vartheta}x^*Gy)\bigr)^2
\le s^2\|x\|^2\|By\|^2.
$$

选择标量相位使实部为 $|x^*Gy|$，再对单位 $x,y$ 取上确界，得到

$$
|x^*Gy|\le\frac{|s|}{2}\|x\|\|By\|,
\qquad \|G\|\le\frac{|s|b}{2}.
\tag{65.10}
$$

所改变的只有读取向量；$r,a,d$ 自始至终固定。这里是固定标量多项式的系数比较，没有让未知 $D$ 的输入趋近任何极限。

在两条相应射线的正交补中，活动方向与旁观方向正交。因此 65.7 给准确分量式

$$
\begin{aligned}
\|q_+X_+e_1\|^2&=|t-(d_2)_{21}|^2+\|G^*e_1\|^2,\\
\|q_-X_-e_2\|^2&=|t+(d_2)_{12}|^2+\|G^*e_2\|^2.
\end{aligned}
\tag{65.11}
$$

65.9–65.10 遂给两式统一上界

$$
\|q_\pm X_\pm e_\pm\|^2
\le |t|^2(1+|s|)^2+s^2b^2/4=\mathfrak b_1^2.
\tag{65.12}
$$

因而 64.6 的任一分支都使两条实际外行满足准确的 64.4。第二估计不使用 $\alpha$，但仍支付真正可能通往旁观方向的未知输出连接；没有把 $G=0$ 预写成假设。

## 66. 实际网络与不定余量的完整消元

**证明续（64.3，实际原第三标签与原外值）。** 取实际 $c=\alpha a$。OP3.1 作用于同一原生成元 $a$ 的多项式 $T$ 和 $\alpha T$，给

$$
D(a,c)=0,\qquad \pi c=F=\alpha A.
\tag{66.1}
$$

不是先假设 $D(a,\alpha a)=\alpha D(a,a)$。将实际三元组 $(a;r,c)$ 放入完整原 PB，保留刚生成的实际标签

$$
\begin{aligned}
x_\pm&=r\pm\bigl(D(a,r)-a\circ c\bigr),&
y_\pm&=c\pm a\circ r,\\
\pi x_\pm&=R\mp d\mp AF=X_\pm,&
\pi y_\pm&=F\pm C_0=Y_\pm.
\end{aligned}
\tag{66.2}
$$

两条连接均已在 65 支付。故 OP83.1 及原反对称性准确识别同一总 $D$ 的这两个实际输出：

$$
\pi D(x_\pm,y_\pm)=K(X_\pm,Y_\pm).
\tag{66.3}
$$

没有把实际外层换成其他同像代表；实际标签中可能属于 $\ker\pi$ 的部分全部保留。OP83.1 本来就包括这些实际代表及任意非零幅度 $\pm2\alpha s$。

同一次 PB 的右端读为

$$
2R\circ d+2R\circ(AF)-2F\circ C_0.
$$

只展开辅助双线性 $K$，而不展开未知 $D$，得到

$$
\begin{aligned}
K(X_+,Y_+)-K(X_-,Y_-)
&=2K(R,C_0)-2K(d,F)-2K(AF,F)\\
&=2K(R,C_0)-2K(d,F),
\end{aligned}
$$

最后一步使用 $[AF,F]=0$。所以同一个 $d$ 满足

$$
R\circ d+K(d,F)=K(R,C_0)-R\circ(AF)+F\circ C_0.
\tag{66.4}
$$

这正是 SM51.4 的实际网络方程；半定性未用于该式。令 $d_0=K(R,A)$，仅对已知矩阵交换子使用 SM51.5 的恒等式

$$
R\circ d_0=K(R,C_0),\qquad
K(d_0,F)=-R\circ(AF)+F\circ C_0.
\tag{66.5}
$$

它们分别由交换子展开及 $[A,F]=0$ 给出。这里还可直接核对 $d_0=\sigma stY\oplus0$，66.5 的第一式两边为零，第二式两边为 $-\alpha s^2tT\oplus0$；一般网络中 66.4 的最后两项不能无故删除。

对同一 Hermitian 余量 $H=d-d_0$，相减即得

$$
R\circ H+K(H,F)=0,
\qquad q_AHq_A=0.
\tag{66.6}
$$

第二式来自 65.3 与 $q_Ad_0q_A=0$。完整保留了原第二槽的零预算。

**证明续（64.3，活动块和交叉块消元）。** 定义 $M=R-i\sigma F$。准确算子恒等式为

$$
MH+HM^*=2\bigl(R\circ H+K(H,F)\bigr).
\tag{66.7}
$$

因此 66.6 写成

$$
M=M_2\oplus B,\quad
M_2=\alpha(1-i\sigma s)Z+tT,\qquad
H=\begin{pmatrix}U&V\\V^*&W\end{pmatrix},\quad
MH+HM^*=0,\quad W=0.
\tag{66.8}
$$

$W=0$ 已由同一 P2 取得；不能只凭 $BW+WB=0$ 推出它。左上和右上块分别给

$$
M_2U+UM_2^*=0,\qquad M_2V+VB=0.
\tag{66.9}
$$

写 $U=u_0I_2+u_1T+u_2Y+u_3Z$，所有 $u_j\in\mathbb R$。由 $[T,Z]=-2iY$、$[Y,Z]=2iT$，第一式除以二后的 $I_2,T,Y,Z$ 系数准确为

$$
\begin{cases}
t u_1+\alpha u_3=0,\\
t u_0-\sigma\alpha s u_2=0,\\
\sigma\alpha s u_1=0,\\
\alpha u_0=0.
\end{cases}
\tag{66.10}
$$

$\alpha s\ne0$ 依次给 $u_0=u_1=u_2=u_3=0$，故 $U=0$。

只对自伴 $B$ 使用成熟有限谱分解。若 $Bv=\beta v$，则 $\beta\in\mathbb R$，第二式给 $(M_2+\beta I_2)Vv=0$。准确行列式为

$$
\begin{aligned}
\det(M_2+\beta I_2)
&=\beta^2-t^2-\alpha^2(1-i\sigma s)^2\\
&=\beta^2-t^2-\alpha^2(1-s^2)+2i\sigma s\alpha^2\ne0.
\end{aligned}
\tag{66.11}
$$

非零虚部来自 $\alpha s\ne0$，不要求 $\beta$ 非零或同号。因此 $Vv=0$；$B$ 的特征向量张成整个旁观空间，故 $V=0$。结合 $W=0$，得到 $H=0$，即 64.7。没有对非正规 $M_2$ 作 Hermitian 对角化，也没有借全谱条件代替原压缩。∎

## 67. 严格扩大的符号消费者

**命题 67.1（整体预算的严格放宽与所有实际代表）。** 在 64.2 的形状中，SM50.3 型整体充分量为

$$
\mathfrak q=L(1+|s|)+|\alpha|s^2.
\tag{67.1}
$$

第一连接量满足

$$
\mathfrak q-\mathfrak b_0=L-|t|+|\alpha|s^2>0.
\tag{67.2}
$$

故在这一形状下，$\mathfrak q<2$ 蕴含 $\mathfrak b_0<2$；反向不成立，以下无限符号族通过第一连接预算而不通过整体预算。

具体地，对任意 $n\ge3$、任意 $B=B^*\ne0$、任意实 $\alpha\ge2$，令

$$
t=\frac12,\qquad
L=\max\{\sqrt{\alpha^2+1/4},\|B\|\},\qquad
s=\frac1{4L}.
\tag{67.3}
$$

则 $\alpha ts\ne0$，且

$$
\mathfrak b_0=\frac34<2,
\qquad \mathfrak q=L+\frac14+\frac{\alpha}{16L^2}>2.
\tag{67.4}
$$

若另取未尺度化的第二像 $A_0=Z\oplus0_m$，同一 $R$ 对应的 50.3 型粗整体量为 $2L+\alpha>2$。这只是充分估计的比较，不将 $A_0$ 的实际旧值搬运到 $A$。$\alpha$ 与 $\|B\|$ 均可任意有限大；这里只选择非零小 $s$ 支付当前实际连接。

**证明。** $\alpha\ne0$ 给 $L> |t|$，所以式 (67.2) 严格。式 (67.3) 有 $L\ge\sqrt{\alpha^2+1/4}>2$，各式直接成立。$\pi(E)=H_n(\mathbb C)$ 来自 PB241.1：$\pi(E)$ 是稠密的有限维实线性子空间，因而闭且为全空间。因此每份 $R,A$ 均有实际原代表，$c=\alpha a$ 及 66.2 的全部外层仍在原域。定理 64.3 对每个参数及所有这些代表重新适用；未把 $s=1$ 的某个旧值按未知齐次性缩放。

活动块的特征值为 $\pm\sqrt{\alpha^2+t^2}$，故 $R$ 不定；$[R,A]=-2istY\oplus0\ne0$。$\operatorname{rank}A=2$、$\operatorname{rank}R=2+\operatorname{rank}B\ge3$，所以两输入不是秩一像，也不共同支撑于任一二阶角。式 (67.3) 因而给明确的非共同二阶角不定原对消费者。∎

**命题 67.2（对角幅度完全退出局部预算）。** 任取有限自伴 $B$ 和 $0<|t|<2$。对任意 $\alpha\ne0$，只要

$$
0<|s|<\frac{2-|t|}{|t|+\|B\|/2},
\tag{67.5}
$$

就有 $\mathfrak b_1<2$，从而 64.7 对全部实际代表成立。$s$ 的这个区间完全不依赖 $\alpha$。当 $B\ne0$ 时为前述非共同二阶角消费者；$B=0$ 时全部结论直接复用 OP80.2，零新增。

还存在第二预算通过而第一预算也不通过的无限符号族。任取 $B=B^*\ne0$，记 $b=\|B\|$，令

$$
t=1,\qquad s=\frac1{4(1+b)},\qquad
\alpha\ge4(1+b).
\tag{67.6}
$$

则

$$
\mathfrak b_1^2
=(1+s)^2+(sb/2)^2
\le\frac{25}{16}+\frac1{64}=\frac{101}{64}<4,
\qquad
\mathfrak b_0=1+sL>2,
\qquad \mathfrak q>2.
\tag{67.7}
$$

**证明。** 对非负 $a,c$ 有 $\sqrt{a^2+c^2}\le a+c$，故

$$
\mathfrak b_1\le |t|+|s|(|t|+b/2)<2
$$

由 67.5 给出。67.6 有 $0<s\le1/4$、$sb/2<1/8$，得到 67.7 的平方界。又 $L\ge\sqrt{\alpha^2+1}>\alpha\ge4(1+b)$，故 $sL>1$，第一预算不通过；$L>4$ 也使整体预算不通过。所有结论仍只调用当前实际原对。∎

**命题 67.3（任意自伴旁观谱与全谱共振）。** 命题 67.1、67.2 的消费者允许任意零谱、重谱及非零相反旁观谱。特别 $n\ge4$ 时可取

$$
B=\operatorname{diag}(b,-b,0_{n-4}),\qquad b>0,
\tag{67.8}
$$

再按式 (67.3) 或式 (67.6) 选择参数。定理 64.3 仍识别同一个实际输出，虽然 $M=R-i\sigma F$ 的全 Sylvester 算子存在非零 Hermitian 核。

**证明。** 若 $u,v$ 分别是旁观 $b,-b$ 的单位特征向量，则数学矩阵

$$
H_{\rm res}=0_2\oplus(uv^*+vu^*)\ne0
$$

满足 $MH_{\rm res}+H_{\rm res}M^*=0$，且 $q_RH_{\rm res}q_R=0$；但 $q_AH_{\rm res}q_A=H_{\rm res}\ne0$。它被原第二槽零预算排除，并非原 P2 允许的余量。若旁观块有零特征向量，支撑于该方向的秩一矩阵同样给全算子的核，也被 $q_A$ 排除。定理不需要排除这些谱。

成熟 Sylvester 判据说，整个复矩阵空间上的 $H\mapsto MH+HM^*$ 可逆，当且仅当 $\operatorname{spec}(M)\cap(-\overline{\operatorname{spec}(M)})=\varnothing$。其准确经典来源可取 Nicholas J. Higham，[*What Is the Sylvester Equation?*](https://nhigham.com/2020/09/01/what-is-the-sylvester-equation/)，其中对 $AX-XB=C$ 用 Schur／Kronecker 说明唯一性，本文相应代入 $B=-M^*$；该来源亦列 Lyapunov 变体。本文只将其作为内部范围说明，66 的实际证明直接消元，不以它取得新内容名义。

上述 $H_{\rm res}$ 只是单独矩阵方程的核见证，没有构造一个满足 A1–A3、准确锥、全部 P2 与完整 PB 的总 $D$。它不是完整原 PB 的反模型，不能用来声称谱非共振是必要量子公理。∎

## 68. 复用、新增与未付桥梁

**定义 68.1（准确新增范围）。** 本文复用 SM51.1–51.6 的原网络，不重复计算一个已经全域识别的响应。所增加的是准确消费 OP83.1 的跨射线预算，并在尺度化第二标签族中把同一原 P2 的旁观零压缩接到活动和交叉消元；65.8 的完整 Gram 减项还让独立对角幅度 $\alpha$ 从第二充分预算退出。承重结论始终是同一个旧 $D$ 的 64.7，不是定义一个候选 $K$，也不是单独解一个与原网络未接线的矩阵方程。

复用边界逐项保持：

1. 若原域本身已经是完整有限复矩阵直和，或同一原 JB 完成有限维，PB142.1–143.1 已识别全部旧响应；本文在该处零新增。仅有有限商时，$\pi(E)$ 满射不等于 $\pi D$ 已下降，不能预先应用该完整有限原域分类。PB152.1、160.1、167.2–174.1 的全域分类也直接复用，各自保留完整有界 type I 原域、全部单块原有限秩包含，或本质复紧理想及非零原有限角等准确结构前件；这些已识别域中的相同输出不计为本节新增。
2. 若 $B=0$，两输入共同支撑于同一二阶角，OP80.2 包括任意幅度、任意标量部分及全部实际代表；本文零新增。
3. OP82.1 已给共同符号，OP83.1 已给秩一首像任意背景的小连接行；本族 $B\ne0$ 的目标首像秩至少三、第二像秩二，不是这两个接口直接识别的目标对。本文真正消费的是它们识别的两条实际外行。OP89–95 的三射线侧面约束仍保留其未付饱和条件，不被当作一般原响应分类。
4. SM50.2、52.1 的首像半定；本族活动块有正负谱，不从它们取得不定消元。SM51.4–51.6 不用半定性的原网络部分可复用，SM51.7 的同号迹论证不能移植为不定消元。
5. SM55–62、PT118–122、PT126–133 及中央卷中要求实际原反射或实际三轴框架的入口，仍守各自的原存在前件及分离前件。商内的 $E_{11},E_{22},Z,T$ 只是数学坐标，不供应实际原幂等元、反射、框架或相应原域闭合。

本文不声称穷尽仓内全部特殊入口或一般不定首像分类；所称新增仅为上述一般原像接口上实际接出的局部消费者，不取得成熟矩阵理论或历史新定理的名义。

**定义 68.2（充分预算的使用范围）。** 64.4 是使用 OP83.1 识别本次两条实际外值的足够条件，65.6 和 65.12 则是它的两种足够估计。条件达到或超过二时，本文的相应估计不供应识别；这既不证明实际连接超过二，也不证明 64.7 错误。尤其 $B=0$ 时旧二阶角分类已给任意参数的公式，可直接说明本预算不是普遍必要条件。即便 $B\ne0$，某组局部余量方程留核也不等于存在完整原模型的歧义。

本结论覆盖的 $R,A$ 形状仍有限制：$A$ 的非零谱为相反的两点，$R$ 无活动与旁观之间的输入交叉块，活动块取指定 $\alpha Z+tT$，并须通过至少一份充分预算。没有把任意对输入化到此形状，没有恢复未知 $D$ 的一般缩放或分配律，也没有将不同已付输入对相加。$s=0$ 或 $\alpha=0$ 会使两条非零秩一外行退化；$t=0$ 则非交换消费者消失。本文不将这些退化分支按该证明自动补齐，也不影响既有零像、同轴或二阶角结果。

**定义 68.3（仍待取得的原目标）。** 对一般有限商仍须证明 OP85.1 的全部实际输入结论

$$
\pi D(a,b)=K(\pi a,\pi b)\qquad(a,b\in E),
\tag{68.1}
$$

及等价的全域核平移不变性。64.7 在本族所有同像实际代表上的相同性是结论的受限纤维不变性，不是 68.1 的全商下降。OP85.2 中 Cayley 负端点与原目标的旧值相同仍须实际接线，不能由同像替代。即使全部有限商分别识别，还须证明相应读取联合分离原元素，或另给一般原载体直接桥；一般 JB 不预设有分离有限商族。

全域旧双线性、原换括号关系 R、全部原评价的有限复 Gram、同一个结合乘法 $\circ-iD$、原域与完成之间的准确运输继续各有原义务。完整量子重构与下面七项消费者的实际来源亦未由一个有限商局部公式支付。独立原公理数没有减少；简化的是这族实际网络中所需估计和可另选响应的自由度。上游 OP3.1、80.2、82.1、83.1 使用完整原 PB，末端只取线性第三标签不能据此删除其余 PB。

## 69. 七项原量子合同与全部上游量词

**定义 69.1（逐项全文保留）。** 以下各项分别合取 [C199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#199-来源几何与量子消费者的完整边界) 对应项、[C194.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#194-新连接完整候选与量子消费者的范围) 对应行、[C186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#186-七项原量子来源合同的准确消费者) 对应条的逐项全文，以及 SM43.2、SM49.1、SM61.1、PT122.1 及各项全部上游合同，不用下面的消费者说明替换任何原量词。完整保持同一原世界、来源、对象和实现；原中心、经典、不等维块及静默部分不因选取一个数学简单商而删除。

1. **复 Hilbert、可观测量和相干叠加。** 完整保持 C145.1–145.7、C155.1、C160.3、C171.1–171.7、C181.3、OP87.1 及其上游。C139–140 的数学 Hilbert 载体、系数几何及此处有限商公式都仍需全域旧响应识别，才能成为同一旧全域共同乘法。唯一原 $\Omega$、原 $E/S/D$、跨评价配对、具名可取得标签、native、任意有限长度及零长度的全词同一 $q,K,J$、parent/ready、合法控制和实际相干叠加准备完整取 C171.1 及其静态卷8.3–8.4、14.2、25.1和三标签卷8.2–8.5、80.1。辅助正读取、数学射线及活动二阶面不产生全 $B(H)$ 的可取得像、任意向量准备、原完备性或无轴一般原域结论。

2. **原态、效果、质量与 Born。** 保留 C171.2、C145.2 及静态卷25.1第2行的同一原评价、原事件、准确效果区间、全部实际完整菜单和接受归属。仅对该实际完整菜单的严格正总质量归一；零、不等、次归一质量、原 $q$、中心权、中心经典混合、经典不等维块及静默部分完整保留。共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、全部 P9 分支、独立 $W_e$、全部原中间切口和固定支持全质量仍须原来源。65.1 的数学向量读取及任何数学正延拓都不证明实际准备或菜单齐备，也不将一般无限维态替换成有限密度矩阵。

3. **native、真正相关联合与张量。** 保留 C171.3、C145.3、静态卷25.1第3行、静态卷53.1及单位桥95.2、116.1 要求的同一个实际非零相关联合。原全词 $K/J$、交叉零、共同生成与分离、满足局部全矩阵前件的忠实同向交换两腿、共同实现、所需重数、全部真正相关输入、中央对、经典和不等维块及递归同源参考均保留。分别可达、相同边缘、同一数学商、相同取向或框架交换不供应共同来源。这里的活动／旁观直和不是物理张量分解，自伴旁观矩阵 $B$ 不自动成为物理子系统。

4. **typed CP、Kraus 接线与整台参考。** 保留 C171.4、C145.4 及静态卷25.1第4行的原未归一回溯、每个合法 typed 前接／后接、反变合法复合、typed 分区、全未来自然性和原箭头商下降。CP 所需同源参考覆盖整台实际箭头，包括系统、整个环境、全部成功／失败／细记录／port／post-port 输出及每份输出的每个仍合法未来。系统腿和参考腿须共同真支持且忠实同向交换；三实际投影、各自支持内补、共同真实支持上的准确运输、全部相关正输入的 intertwining 与夹界、每个所需有限递归深度及累计支持完整链均保留。支持内补不改为环境补，数学正读取、行列式可逆及余量唯一性不构造实际箭头、参考或 CP。

5. **整台仪器、TP、更新与 Lüders。** 保留 C171.5、C145.5 及静态卷25.1第5行的全部原输入运输、完整 typed 菜单、整个环境和全部成功／失败／细记录／port／post-port 输出与每份输出所有合法未来、原接受端、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及其接受条件。TP 需要完整单位分区，Lüders 另需同一个完整输出的像内射线校准。只对正输出质量归一，零分支保留。密度、迹类和算子 Kraus 公式仅在准确合格的有限全矩阵原域，或另已供应所需正规物理表示、指定前对偶与所需收敛且确实适用的域消费。有限商不是这些前件的替代。

6. **全部历史、全未来、真实返回与 CountRead。** 保留 C171.6、C145.6、静态卷8.4、25.1第6行及单位桥原消费者的全部量词：所有合法顺序／自适应／并行历史、每份输出每个仍合法未来、整个环境、全部细记录和泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧真实返回和同数逆向真实返回。CountRead 绑定读后同一原完整活动输入及全未来返回；负提升两条活路的分别控制与相干聚合、具名分析词到原完整菜单及接受端的接线须原生构造。原 $B$ 的精确正生成与另名 $B_{\rm cl}$ 的闭正生成不混同，二者也不与本文旁观矩阵混淆。无限历史、无限／非离散记录、可数可加、正常性和指定前对偶保留各自来源。程序、实际读取次序、原 $q$-零集及 AC 方向不由矩阵相同而等同；未定义请求仍未定义，局部识别不供应真实双向返回或无限记录可加性。

7. **动力、物理钟、能量与共同尺度。** 保留 C171.7、C145.7 及静态卷25.1第7行的同一旧全域乘法、保持可能不完备原域的流、实际相位和门序列、可逆一参数群、原物理钟、所需强连续酉实现、生成元定义域、Hamiltonian 能量解释、共同作用量、共同正 $\hbar$ 与共同仪器。原 $\sigma,t_0,d$、固定域、resolvent 及 $3s+r\le1$ 保持各自合同含义，与本文块符号和参数区分。数学 $\alpha,t,s$、复矩阵铅笔、辅助谱及有限预算不供应物理时间、控制成本、钟能量或共同作用量；有界候选导子不替代一般无界生成元。原受限旧值不能升级成全域旧响应动力或完整量子物理来源。

## 70. 跨界连线的完整中文图景

**定义 70.1（更简洁的关系几何）。** 从同一原世界的两两有向正比较、相加三角、单位小窗和所有三标签正反配平出发，固定正在询问的那一个实际旧答案。第一对象在两条活动方向上一正一负，这两条方向间有真实的数学连接；旁观方向可以带任意自伴背景。第二对象只在活动方向取一对相反强度，是否可用由两份连接预算中的任一份决定。第三标签不另找来源，只取第二个实际原标签的实倍数，因此两者之间的旧响应由原多项式零值认定为零。

把这三个实际标签送进同一次配平，两张外表的第二标签恰好各落在一根非零射线上。既有小窗口接口只检查对象怎样从该射线连到外面，并不检查沿射线的对角读数或完全旁观的背景幅度。因此，原先把整张矩阵压小的要求可以改为准确支付跨界连接；第三标签乘积虽能在活动面内产生很大的共同对角项，却没有跨过任一射线的边界，不需要为它交连接预算。第一份充分估计直接用原 P2 控制未知输出的总幅度；在所写块形状中，只要原横向连接严格小于二，活动对角与旁观背景便可任意有限大，由另选的非零小第二强度支付；更局部地保留同一 Gram 行列式的减项后，与第二对象平行的对角幅度完全抵消，只有原横向连接和可能通往旁观方向的输出连接仍需估计。

两张外表一旦都通过已有接口，给出的就是那两份刚生成的实际旧输出，不能另换同像代表或各选方便答案。它们共同约束最初同一个答案，使标准值之外的偏差满足一个确定的余量方程。不定首对象容许正负抵账，不能照搬半定迹法；这里由非零第二强度提供的有向项直接排除活动偏差，并使活动方向与任何实旁观谱之间的偏差都不能留下。旁观内部就算出现零谱或相反谱，也早已被第二对象平方预算为零的原 P2 压缩排除。因此无需另加谱非共振、旧响应线性或背景独立性公理，就在所写局部族内认回同一个原答案。减少的是无关幅度造成的估计负担与这一族旧响应的自由度，原公理数、一般原域目标和所有量子消费者的完成标准都保持：实际相干准备、完整 Born 菜单及全部质量、真正共同联合、整台仪器与环境全部输出、每层递归参考、所有历史未来与真实双向返回、无限 CountRead、正常性与前对偶、保持原域的动力、物理钟、能量和共同正作用量仍逐项需要完整同源接口；这里识别的是所写局部族中的同一个实际原响应，完整量子起源仍须上述全域及实际来源桥梁。

## 追加锚（本行以下为增补区）

## 71. 同一原背景的区间窗与有限迹族

**定义 71.1（完整原条件与固定对象）。** 完整采用55.1–55.3和[原PB运输续卷118.1–118.3](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#118-任意原偶背景第一实际框架与同一余量)的同一原 $(E,C,u,N,\mathcal P,S,D)$、A1–A3、准确原锥、全部原P2和完整原PB。原评价及全部零、不等、次归一质量保留；PB仍对全部原三标签成立，不限于下文选用的网络。七项实际来源逐项合取61.1、69.1及其纳入的全部上游合同全文，具体消费者范围取78.2；区间窗和数学迹不替换任何原前件。沿同一个忠实、含单位、等距且准确保锥的JC包含，仍有

$$
E\subset X\subset\mathcal A_{\rm sa},\qquad
\overline E=X,\quad \mathcal A=C^*(X),\quad
S(a,b)=a\circ b=(ab+ba)/2.
\tag{71.1}
$$

此包含的原候选来源已由[配平三角续卷240–251](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md#240-一般原候选的有限商障碍与无种子复载体)支付；不再另列特殊性缺口，也不把JC包含提升为 $E=\mathcal A_{\rm sa}$。原域可不完备、不可分、无原子，$X$ 不必填满环境自伴部。固定实际原框架

$$
h,e,j=D(h,e)\in E,\quad h^2=e^2=j^2=u,\quad
h\circ e=h\circ j=e\circ j=0,\qquad
Q=ihej\in Z(\mathcal A),\quad Q^*=Q,\quad Q^2=u.
\tag{71.2}
$$

$Q$ 不要求是原标签。对任意原 $h$-偶 $c$、原 $h$-奇 $z$ 及实数 $R$，保留55.5的同一次实际输出：

$$
\begin{gathered}
x=c+z,\qquad t=D(h,z)=iQhz,\qquad
g=D(Rh,x),\qquad r=g-Rt,\qquad [h,r]=0,\quad z\circ t=0,\\
v_c=K_c(r):=c^2\circ r-c\circ(c\circ r)\in E,\qquad
4v_c=[c,[c,r]].
\end{gathered}
\tag{71.3}
$$

这些 $c,z,R,x,t,g,r,Q$ 在全部窗和全部PB调用中保持不变。$K_c$ 是显示的有限Jordan算子，区别于55.4的窗盲空间、辅助交换子和原全词合同的同名字母。下文的实数

$$
C=\|c\|,\qquad Z=\|z\|,\qquad G=\|g\|,\qquad \rho=\|r\|
\tag{71.4}
$$

只作范数常数；71.4中的 $C$ 不表示原正锥。

**定义 71.2（同一环境的静态有限迹分离）。** 给定一族 $\mathcal T$，每个成员都是同一含单位C*代数 $\mathcal A$ 上的有限正复线性泛函，满足

$$
\tau(ab)=\tau(ba)\quad(a,b\in\mathcal A),\qquad
m_\tau=\tau(u)<\infty,\qquad
\|w\|_{2,\tau}^2=\tau(w^*w).
\tag{71.5}
$$

要求它们分离正元：$a\in\mathcal A_+$ 且对全部 $\tau\in\mathcal T$ 有 $\tau(a)=0$，则 $a=0$。单个忠实有限正迹足够，但不要求存在单个忠实迹，不要求归一、正规、可分性或指定前对偶。正泛函在含单位C*代数上自动有界，$\|\tau\|=m_\tau$；$m_\tau=0$ 时它就是零泛函，该成员的整个半范数为零，不独自提供分离。数学迹族不是新增物理准备。

**定义 71.3（真正原域中的减约区间分割）。** 当 $C>0$ 时，给定一个无上界的正整数集合 $\mathcal N_c$。对每个 $N\in\mathcal N_c$，令

$$
\varepsilon_N=C/N,\qquad a_i=-C+(2i-1)\varepsilon_N\quad(1\le i\le N).
\tag{71.6}
$$

要求存在 $2N$ 个可为零的实际原投影 $q_{\sigma,i}^{(N)}\in E$，$\sigma\in\{+1,-1\}$，使

$$
\begin{gathered}
(q_{\sigma,i}^{(N)})^*=(q_{\sigma,i}^{(N)})^2=q_{\sigma,i}^{(N)},\qquad
q_{\sigma,i}^{(N)}q_{\sigma',j}^{(N)}=0\quad((\sigma,i)\ne(\sigma',j)),\\
\sum_{\sigma,i}q_{\sigma,i}^{(N)}=u,\qquad
hq_{\sigma,i}^{(N)}=\sigma q_{\sigma,i}^{(N)},\qquad
[c,q_{\sigma,i}^{(N)}]=0,\\
\|(c-a_i u)q_{\sigma,i}^{(N)}\|\le\varepsilon_N.
\end{gathered}
\tag{71.7}
$$

这是近似标量窗，不要求 $cq=a_iq$。投影不必最小、有限秩或本征投影，不要求与 $e$ 交换，也不要求不同 $N$ 的分割相容。全零的个别窗及其原指标保留。供应条件只依赖 $c,h,E,N$，与 $z,R,g,r$ 及未知响应值无关。每个正整数都有这份分割是一种方便的充分条件；无上界集合已经足够。环境Borel投影若不在原 $E$ 中，不能作为71.7的标签；迹分离也不蕴涵该成员资格。

## 72. 保留全部分割成本的同输出定量识别

**定理 72.1（原区间窗的有限迹平方预算）。** 在71.1的完整原条件下，若71.2成立，且所选原偶背景 $c$ 满足71.3，则对式(71.3)的同一个 $g,r,v_c$，每个供应的 $N$ 及每个 $\tau\in\mathcal T$ 都有

$$
\boxed{\begin{aligned}
\|[c,r]\|_{2,\tau}^2
&\le m_\tau\frac{C^2}{N^2}
       \bigl[4\rho^2+16(N-1)M^2\bigr],\\
\|v_c\|_{2,\tau}^2
&\le m_\tau\frac{C^4}{N^2}
       \bigl[\rho^2+4(N-1)M^2\bigr],\\
M&=(1+3R^2)C+Z+G.
\end{aligned}}
\tag{72.1}
$$

在这些界中可同时作完全由固定源数据决定的替换

$$
\begin{gathered}
G\le |R|(C+Z),\qquad \|t\|=Z,\qquad
\rho\le |R|(C+2Z),\\
M\le M_0:=(1+3R^2+|R|)C+(1+|R|)Z.
\end{gathered}
\tag{72.2}
$$

没有依赖 $N$ 的未知响应值进入这些常数。于是同一个原元素满足

$$
\boxed{v_c=0,\qquad r=0,\qquad D(Rh,c+z)=RiQhz.}
\tag{72.3}
$$

供应条件独立于 $R,z$；所以对每个具此分割的固定 $c$，72.3同时覆盖每个原奇 $z$ 和每个实 $R$。分别取 $R=1$ 后还得到此范围内的结论 $D(Rh,c+z)=R D(h,c+z)$，未将其当作首槽齐次前件。

零原代数中各项为零。$R=0$ 时原P2和分离性给 $D(0,x)=0$；$c=0$ 时 $K_c(r)=0$ 直接成立，[运输续卷119.1](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md#119-一项原-jordan-二元关系的充要判据)即给 $r=0$。这些分支无需分割，也不除以 $R$ 或 $C$；72.1在 $c=0$ 时两边为零。零窗、零迹、$N=1$、相反中心和零中心均保留。

证明。72.2首先只用固定原表 $(Rh,x,g)$ 的P2。每个环境态 $\phi$ 限制到原域都是55.2的合法正读取，故

$$
|\phi(g)|^2\le R^2\phi(u)\phi(x^2)
\le R^2\|x\|^2\quad(\phi(u)=1).
$$

自伴元的态范数分离及 $\|x\|\le C+Z$ 给 $G$ 的界。由71.2，$iQh$ 是酉元，因而 $t=iQhz$ 有范数 $Z$；三角不等式给其余72.2。这只估计一次实际输出，未按输入缩放未知 $D$。以下在 $C>0,R\ne0$ 时证明72.1，最后使用119.1；其他分支如陈述。

## 73. 两个近似窗上的实际反射与非零外预算

**定理72.1的证明：保留同一实际网络。** 固定一个 $N$、一个符号 $\sigma$ 及不同指标 $i,j$。略去上标，置

$$
q_i=q_{\sigma,i}^{(N)},\quad q_j=q_{\sigma,j}^{(N)},\quad
q=q_i+q_j,\quad a=a_i,\quad b=a_j,\quad \varepsilon=\varepsilon_N.
$$

零角允许；若某角为零，则该矩形角上的全部结论直接为零。准确沿56.2的原有限Jordan构造取

$$
\begin{gathered}
p'=q_i+eq_ie,\qquad s=u-2p',\qquad H=h\circ s=hs,\\
T=R\sigma(a+b)u+R(b-a)H,\qquad V=T-2Rhc.
\end{gathered}
\tag{73.1}
$$

$eq_ie=2e\circ(e\circ q_i)-q_i\in E$；它在相反 $h$ 角，且与 $q_i,q_j$ 正交。故 $p'$ 为原投影，$s^2=u$、$[s,h]=[s,e]=0$，并有

$$
Hq_i=-\sigma q_i,\qquad Hq_j=\sigma q_j.
\tag{73.2}
$$

[中央续卷182.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#182-原系数反射给出的第二份实际框架)给实际 $D(H,e)=sj$ 及 $iHeD(H,e)=Q$。其182.1参数可取背景 $s$、$\lambda=0,\nu=1,z_0=0$，只为取得新框架，未将本次 $c$ 换成 $s$。随后[中央续卷163.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#163-正负强度均适用的仿射首标签投影)在该实际框架上给每个原 $y$ 的准确横向输出

$$
P_H^-D(T,y)=R(b-a)iQH P_H^-y.
\tag{73.3}
$$

不借用协变性或未知首槽齐次性；$s,T$ 均无需与整个 $c$ 交换。

55.6给内值 $D(Rh,T-Rhc)=0$。对原三元组 $(Rh,x,T-Rhc)$ 用同一完整PB，沿56.4保留两份实际外层：

$$
\begin{gathered}
A_+=x+g+R^2c-RhT,\qquad A_-=x-g-R^2c+RhT,\\
\mathcal J=-2x\circ g-2R^2z\circ c+2Rz\circ(hT),\\
D(A_+,T)-D(A_-,V)=\mathcal J,\qquad
O=D(V,A_-).
\end{gathered}
\tag{73.4}
$$

此抵消只需 $[h,c]=[h,T]=0$ 及
$c\circ(hT)=(hcT+hTc)/2=T\circ(hc)$，不需 $[c,T]=0$。所有输入均在原 $E$；$O$ 是这张实际外表的输出，不是可自由指定的余量。

两个窗均减约 $c$ 和 $T$，故也减约 $V$。由73.1–73.2，

$$
Vq_i=-2Rh(c-au)q_i,\qquad
Vq_j=-2Rh(c-bu)q_j,
$$

从而

$$
\|Vq\|\le2|R|\varepsilon,\qquad
qV^2q\le4R^2\varepsilon^2q.
\tag{73.5}
$$

又因 $|a|,|b|\le C$，有

$$
\|T\|\le |R|\bigl(|a+b|+|a-b|\bigr)
=2|R|\max(|a|,|b|)\le2|R|C,\qquad \|A_-\|\le M.
\tag{73.6}
$$

对每个环境正泛函 $\omega$，$\phi(y)=\omega(qyq)$ 是同一原表 $(V,A_-,O)$ 的正读取。只丢去P2右端的非负均值平方项，便有

$$
|\omega(qOq)|^2\le
\omega(qV^2q)\omega(qA_-^2q)
\le4R^2\varepsilon^2M^2\omega(q)^2.
\tag{73.7}
$$

没有除以 $\omega(q)$；零质量包含在式中。由于 $O=O^*$，全部正泛函的序分离给

$$
-2|R|\varepsilon Mq\le qOq\le2|R|\varepsilon Mq,
\qquad \|qOq\|\le2|R|\varepsilon M.
\tag{73.8}
$$

这以非零但统一的小预算取代56.4的零外表，未比较不同输入的 $D$ 值。

**定理72.1的证明：准确矩形角方程。** 记

$$
X_{ij}=q_i r q_j,\quad c_i=q_icq_i,\quad c_j=q_jcq_j,\quad
O_{ij}=q_iOq_j,\quad \eta=\sigma R(a-b).
$$

$z,t$ 是 $h$-奇，$c,hT$ 在所选两窗上对角。因此 $q_iA_+q_j=X_{ij}$。两窗属于相反的 $H$ 角，73.3给
$q_iD(T,A_+)q_j=i\eta QX_{ij}$。再用 $g=r+Rt$、$z\circ t=0$，73.4的右端在此角准确为

$$
q_i\mathcal Jq_j=-(c_iX_{ij}+X_{ij}c_j).
$$

原反对称性将73.4写为 $O=D(T,A_+)+\mathcal J$，故

$$
\boxed{O_{ij}=i\eta QX_{ij}-(c_iX_{ij}+X_{ij}c_j).}
\tag{73.9}
$$

$c_i,c_j$ 仍是原背景的真实压缩，不把它们换成中心后送入旧响应。令
$\delta_i=c_i-aq_i,\delta_j=c_j-bq_j$，则

$$
\|\delta_i\|,\|\delta_j\|\le\varepsilon,\qquad
[i\sigma R(a-b)Q-(a+b)u]X_{ij}
=O_{ij}+\delta_iX_{ij}+X_{ij}\delta_j.
\tag{73.10}
$$

该误差式不要求 $a+b\ne0$；下一步也不以中心和作分母。

## 74. 同一中央取向的迹正交性与全分割求和

**定理72.1的证明：保留小间距的强制预算。** 固定任意 $\tau\in\mathcal T$，在矩形角 $q_i\mathcal A q_j$ 上用半内积
$\langle X,Y\rangle_\tau=\tau(X^*Y)$。左乘 $c_i$ 自伴；右乘 $c_j$ 的自伴性由迹循环性给出。二者对易，故
$L(X)=c_iX+Xc_j$ 自伴。左乘中央 $Q$ 又是与 $L$ 对易的自伴等距算子。因此
$\langle QX,LX\rangle_\tau$ 为实数，73.9中虚系数的交叉项准确为零：

$$
\|O_{ij}\|_{2,\tau}^2
=R^2(a-b)^2\|X_{ij}\|_{2,\tau}^2
 +\|c_iX_{ij}+X_{ij}c_j\|_{2,\tau}^2.
\tag{74.1}
$$

这也可直接展开有限迹表达式取得，不要求 $\tau$ 忠实；无需完成原域，更没有完成或下降旧 $D$。令 $m_i=\tau(q_i),m_j=\tau(q_j)$。由73.8，

$$
O_{ij}^*O_{ij}\le4R^2\varepsilon^2M^2q_j,\qquad
O_{ij}O_{ij}^*\le4R^2\varepsilon^2M^2q_i.
$$

两者的迹相同，故74.1给

$$
\|O_{ij}\|_{2,\tau}^2
\le4R^2\varepsilon^2M^2\min(m_i,m_j),\qquad
\|X_{ij}\|_{2,\tau}
\le\frac{2\varepsilon M}{|a-b|}\sqrt{\min(m_i,m_j)}.
\tag{74.2}
$$

这里只约去同一个非零 $R^2$，未优化强度，也未将分别可达的表拼接成共同实现。中心间距的倒数明确保留；$a+b=0$、某一中心为零及某一窗质量为零均不造成例外。

**定理72.1的证明：固定交换子的整个能量。** 置固定环境算子 $B=[c,r]$。它不是新的 $D$ 输入；$[h,r]=[h,c]=0$ 使相反 $h$ 符号的角为零。同号异指标角满足

$$
q_iBq_j=(a-b)X_{ij}+\delta_iX_{ij}-X_{ij}\delta_j.
$$

迹半范数中的左右乘法界及74.2给

$$
\|q_iBq_j\|_{2,\tau}
\le2\varepsilon M\left(1+\frac{2\varepsilon}{|a-b|}\right)
\sqrt{\min(m_i,m_j)}
\le4\varepsilon M\sqrt{\min(m_i,m_j)}.
\tag{74.3}
$$

最后一步用等距中心 $|a_i-a_j|=2\varepsilon|i-j|$，包括相邻窗。对角角上常数中心与压缩余量交换，故

$$
\|q_iBq_i\|_{2,\tau}\le2\varepsilon\rho\sqrt{m_i}.
\tag{74.4}
$$

恢复全部 $2N$ 个指标。有限迹循环性与投影正交性使不同矩形角在半内积中正交；具体地，
$\tau((q_\alpha Bq_\beta)^*q_\gamma Bq_\delta)$ 在 $\alpha\ne\gamma$ 时由中间投影为零，在 $\beta\ne\delta$ 时由循环后 $q_\delta q_\beta=0$ 为零。所以

$$
\|B\|_{2,\tau}^2
=\sum_{\sigma,i,j}\|q_{\sigma,i}^{(N)}Bq_{\sigma,j}^{(N)}\|_{2,\tau}^2.
\tag{74.5}
$$

每一列在同一符号下至多有 $N-1$ 个异指标行，且 $\min(m_i,m_j)\le m_j$。因此，包括全部零窗，

$$
\begin{aligned}
\sum_{\sigma,i\ne j}\min(m_{\sigma,i},m_{\sigma,j})
&\le(N-1)\sum_{\sigma,j}m_{\sigma,j}=(N-1)m_\tau,\\
\sum_{\sigma,i}m_{\sigma,i}&=m_\tau.
\end{aligned}
\tag{74.6}
$$

将74.3–74.6相加，准确得到

$$
\|[c,r]\|_{2,\tau}^2
\le m_\tau\varepsilon^2[4\rho^2+16(N-1)M^2].
\tag{74.7}
$$

$N=1$ 时无异指标项。不能把 $N-1$ 丢去；此处的总平方预算是 $O(\varepsilon^2N)$，不是单个角的 $O(\varepsilon^2)$。

由 $4v_c=[c,B]$ 及有限迹的左右乘法界，

$$
\|v_c\|_{2,\tau}\le\tfrac C2\|B\|_{2,\tau}.
\tag{74.8}
$$

右乘界例如由
$\tau((Bc)^*Bc)=\tau(B^*Bc^2)\le C^2\tau(B^*B)$ 取得；左乘界直接由 $c^2\le C^2u$ 取得。代入 $\varepsilon=C/N$ 即为72.1的两条准确平方界。对固定 $\tau$，沿无上界 $\mathcal N_c$ 的右端趋零，而 $v_c$ 始终是同一个原元素，故 $\tau(v_c^2)=0$。71.2分离正元给 $v_c^2=0$，于是 $v_c=0$。这时才将同一个 $R,c,z,x,g,r$ 送入运输续卷119.1，得到 $r=0$ 和72.3。∎

整个极限只作用于固定数 $\tau(v_c^2)$ 的上界；没有 $D(c_N,\cdot)$ 或 $D(\cdot,c_N)$ 的输入极限。$\tau\mapsto\lambda\tau$、$\lambda\ge0$ 时两条平方半范数界整体乘 $\lambda$；73.7的原P2界对读取质量为二次，73.8之前的未平方输出读取界为一次。没有舍弃不等质量或次归一质量，也没有用数学迹替换原评价族。

## 75. 有限 von Neumann 供应与无本征窗的非交换背景

**命题 75.1（完整自伴原域上的区间供应及弥散消费者）。** 若71.1的同一环境 $\mathcal A$ 是有限von Neumann代数，且原 $E=\mathcal A_{\rm sa}$，则对每个原偶背景 $c$ 都有71.2–71.3的供应；只要实际框架存在，72.3便对全部原奇 $z$ 和实 $R$ 成立。存在一个超有限II₁实例和原偶 $c$，其两块背景不交换且

$$
W(c,h)=\{0\},\qquad K(c,h)=E,
\tag{75.1}
$$

但该区间供应对每个 $N$ 成立。后一实例只证明供应相容且超出原本征窗，不提供非零实际余量。

证明。先用成熟的有限von Neumann谱演算。将 $[-C,C]$ 分成互不相交的 $N$ 个长度 $2C/N$ 的区间 $I_i$，中心为71.6的 $a_i$；可取第一段为闭左端的 $[-C,-C+2\varepsilon_N]$，其余取左开右闭。令

$$
q_{\sigma,i}^{(N)}=\frac{u+\sigma h}{2}\,1_{I_i}(c).
\tag{75.2}
$$

$[h,c]=0$ 使此为正交投影，全部和为 $u$，且满足71.7的减约和范数条件。这里 $E=\mathcal A_{\rm sa}$，故它们确实是原标签；一般稠密或不完备 $E$ 没有这一推论。

同一有限von Neumann代数有忠实正含单位中心值迹 $\operatorname{Tr}_Z$。将其与中心 $Z(\mathcal A)$ 的全部态 $\chi$ 复合，得有限正标量迹 $\tau_\chi=\chi\circ\operatorname{Tr}_Z$。非零正 $a$ 的中心值迹仍非零正，某一中心态读它严格为正，故该族分离 $\mathcal A_+$。这里使用的是Dixmier的成熟中心值迹定理，准确出处附于78.1；不要求 $\mathcal A$ 可分、可数可分解或存在单个忠实标量态。一般定理72.1本身只需明示的静态迹族和原窗，不要求von Neumann结构。

具体复用58.6的超有限II₁因子 $\mathcal R$ 及其忠实归一迹 $\tau_{\mathcal R}$，取标准无限张量积
$\mathcal R=\overline{\bigotimes_{n\ge1}(M_2,\operatorname{tr}_2)}^{\rm weak}$。
在第 $n$ 因子中取对角秩一投影 $p_n$，令

$$
a=\sum_{n\ge1}2^{-n}p_n,\qquad
w=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}
\text{（作用在第一因子）},\qquad
c_+=a,\quad c_-=waw^*,\quad c=\operatorname{diag}(c_+,c_-).
\tag{75.3}
$$

级数范数收敛，尾范数至多 $2^{-n}$；它只定义此完整模型中的一个固定自伴元。前 $n$ 个二进位的 $2^n$ 种组合各有迹 $2^{-n}$，部分和在各柱集上取 $k/2^n$，全和落在 $[k/2^n,(k+1)/2^n]$。任一固定实点至多属于其中两个闭区间，故其谱点投影的迹至多 $2^{1-n}$，对每个 $n$ 都如此。忠实性使所有谱点投影为零。由同一柱集估计，或对连续函数作均匀逼近取得的二进位Riemann和，$a$ 的迹分布为 $[0,1]$ 上均匀分布；每个相交开区间有正谱质量，所以其谱为整个 $[0,1]$。$waw^*$ 具有同样分布和无原子性。

第一因子与尾和交换，因而

$$
[c_+,c_-]=\tfrac14[p_1,wp_1w^*]\ne0.
\tag{75.4}
$$

非零性也可在第一二阶因子直接读取：$p_1=\operatorname{diag}(1,0)$，而 $wp_1w^*$ 的两个非对角元均为 $1/2$。取58.6的同一标准原资料

$$
\mathcal A=M_2(\mathcal R),\quad E=X=\mathcal A_{\rm sa},\quad
S(A,B)=A\circ B,\quad D_*(A,B)=i[A,B]/2,
\tag{75.5}
$$

以及该条的Pauli $h,e,j$，有 $j=D_*(h,e)$ 和 $Q=u$。原锥、单位、范数及原评价取58.6的完整约定：全部正实线性泛函及其全部非负质量倍数，含零、不等、次归一和奇异评价。A1–A3、全部输入的P2与完整PB逐项复用58.7和[原多项式零响应卷6.6–6.7](AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md#6-四份独立平方根预算的严格正下确界)的同一乘法与Gram身份；并未只验证有限个标签。

$\operatorname{tr}_2\otimes\tau_{\mathcal R}$ 是同一环境的忠实有限迹；75.2的原窗供应全部 $N$。任意原奇 $z$ 均合法，包括非零的 $z=e$。因 $c$ 没有非零谱点投影，若 $cq=\lambda q$，在忠实正规表示中 $q$ 的像位于该零谱点空间，故 $q=0$。因此55.3的原本征窗只有零，75.1成立；72.1仍通过区间预算识别同一固定行。

若存在33.1型的共同 $h,e$ 交换标量分割，则各投影均为 $\operatorname{diag}(b_\ell,b_\ell)$，并使 $c_+,c_-$ 在每格上同时为标量；它们便交换，与75.4矛盾。即便允许任意指标强总覆盖，有界性也将稠密角和上的交换延伸到整个表示，矛盾仍在。所用代数仍是58.1的同一个II₁代数，故该条已证明的无最小投影、无非零有限秩或紧角、无非零有限维表示及无所需本质复紧Jordan理想的边界全部适用；这里不重复取得那些分类。

标准 $D_*$ 的实际 $r,v_c$ 和真正可加缺陷均为零。它只见证静态供应在无本征窗、非交换背景中真实存在，不是完整PB反模型，更不证明存在非零实际缺陷。72.1的证明才适用于具这些供应但未知的同一原 $D$；未用 $D_*$ 的双线性证明一般旧行。∎

## 76. 有限迹并不自动供应原区间投影

**命题 76.1（多项式原域及其连续完成中的成员资格边界）。** 存在满足71.1全部静态数学前件的不完备原域，且同一环境有忠实有限迹，但一个原偶背景不具有71.3。其连续函数范数完成中的同一背景也不具有该供应。两者的标准响应都无真正可加缺陷；该命题只反驳自动原窗成员资格推断。

证明。令

$$
\begin{gathered}
E=\bigl(M_2(\mathbb C[t]|_{[0,1]})\bigr)_{\rm sa},\qquad
X=\bigl(M_2(C([0,1]))\bigr)_{\rm sa},\\
\mathcal A=M_2(C([0,1])),\qquad
c(t)=\operatorname{diag}(t,t^2),\qquad
S(A,B)=A\circ B,\qquad D_*(A,B)=i[A,B]/2.
\end{gathered}
\tag{76.1}
$$

乘法、锥、单位和范数均逐点继承；多项式原域含单位，对这两种运算闭合，是实Archimedean序单位空间，在 $X$ 中稠密而不完备。取全部原正实线性泛函及全部质量；其有界性和正性延拓到 $X$，或直接由原二表二次型的逐点正性，保证同一Gram验证对每份原正读取成立。全部A1–A3、P2、PB准确沿58.7的乘法身份成立。常数Pauli框架有 $j=D_*(h,e)$、$Q=u$，而

$$
\tau(F)=\int_0^1\operatorname{tr}_2(F(t))\,dt
\tag{76.2}
$$

是同一 $\mathcal A$ 上的忠实有限迹：非零正连续函数的矩阵迹在一个开邻域严格正。

任何满足 $hq=+q$ 的自伴投影都必须为 $q(t)=\operatorname{diag}(f(t),0)$；负号时为 $\operatorname{diag}(0,f(t))$。$f^2=f$ 迫使多项式 $f$ 恒为零或一。因此非零 $h$-符号投影只有整个符号角。$t$ 和 $t^2$ 在 $[0,1]$ 上的值域均为 $[0,1]$，与任何实常数的最大距离至少 $1/2$。当 $\varepsilon_N<1/2$ 时，任何非零符号角都不满足71.7。有限窗还需和为 $u$，所以不存在无上界的供应指标集。

在连续完成 $X$ 中，同一推理仍成立：连续幂等函数在连通区间上的值域在 $\{0,1\}$ 中，只能恒定。故即使把原域确实改成整个 $X$，同一个 $c(t)$ 也没有71.3的分割。更大von Neumann环境虽有相应可测区间投影，它们并非这里的连续标签，更不是原多项式标签。此处也没有把未知旧 $D$ 延拓到完成。

标准 $D_*$ 对这些原输入本来可加，实际行余量及真正可加缺陷均为零。因此本例不是满足完整PB而目标失败的反模型，不声称FULLPB不足，也不以缺少这条充分供应否定其他原关系路线。它精确说明：有限迹、原域稠密性，乃至连续函数范数完备性，都不能替代实际区间投影的成员资格。∎

## 77. 三份实际输出共同消去真正可加缺陷

**推论 77.1（标量反射首槽的真正缺陷消费者）。** 在71.1–71.2下，固定同一实际框架 $h,e,j,Q$ 和实数 $R$。任取原 $b,c$，保持带重数的实际出现表

$$
s=b+c,\qquad (s,b,c),\qquad
c_\ell=P_h^+\ell,\quad z_\ell=P_h^-\ell\quad(\ell=s,b,c).
\tag{77.1}
$$

若三个所需偶背景 $c_\ell$ 分别有71.3的供应，或为零背景，则对同一个原 $D$ 的三份实际输出

$$
d_s=D(Rh,s),\qquad d_b=D(Rh,b),\qquad d_c=D(Rh,c)
\tag{77.2}
$$

有

$$
\boxed{\begin{gathered}
\delta_{Rh}(b,c):=d_s-d_b-d_c=0,\\
K_y\bigl(\delta_{Rh}(b,c)\bigr)=0\qquad(y\in E),\\
K_y(w)=y^2\circ w-y\circ(y\circ w).
\end{gathered}}
\tag{77.3}
$$

不要求三个分割相同或共同细化，也不因标签重复而删除任一输出出现。若每个原偶背景都有供应，特别在75.1的完整有限von Neumann供应域中，本结论覆盖全部原 $b,c,y$ 和实 $R$，首槽仍限于这份实际框架的 $a=Rh$。

证明。$P_h^\pm=(I\pm U_h)/2$、$U_hy=2h\circ(h\circ y)-y$ 是保持原 $E$ 的已付实线性有限Jordan算子。分别对三个实际输入调用72.1，保留每次自己的 $g,r$，得到

$$
d_\ell=RiQhP_h^-\ell\quad(\ell=s,b,c).
\tag{77.4}
$$

已知辅助乘法和 $P_h^-$ 的实线性给

$$
d_s-d_b-d_c
=RiQh\bigl(P_h^-s-P_h^-b-P_h^-c\bigr)=0.
$$

零标签、重复标签、相等标签及 $R=0$ 都包含；当某一 $c_\ell=0$ 时使用72.1的零背景分支。最后把同一零缺陷送进有限Jordan算子 $K_y$ 即得77.3。∎

**定义 77.2（与全原目标的准确对应）。** 72.1估计的量是固定行余量
$r=D(Rh,c+z)-RiQhz$ 的 $v_c=K_c(r)$，不是
$\delta_a(b,c)=D(a,b+c)-D(a,b)-D(a,c)$。77.1通过保留三份定义输出，才取得真正缺陷的一个完整首槽子族。只给一个背景的供应时，不能推断另两份偶背景也有供应；77.1已将全部所需背景列出。

未由此证明对每个原 $a,b,c,y$ 都有 $K_y\delta_a(b,c)=0$。任意原首标签 $a$ 未必是某份实际框架的实数倍；不能把它近似成反射之和，再按未证的首槽可加或输入连续性拼接旧响应。一般原域未必具有71.2的分离有限迹或71.3的实际原窗，也未由本条生产实际框架。一般旧分别可加／双线性、全有限原复Gram、原换括号关系R、同一旧结合乘法 $S-iD$、准确完成运输及完整物理来源继续保留各自原义务。这里已付的JC包含不等于这些更强结论。

## 78. 区间能量综合的来源与七项完整消费者

**定义 78.1（仓内综合及成熟工具的准确分界）。** 72.1归为 $\texttt{repo-derived}$：新增承重是73.7–73.9的非零实际外窗预算与准确矩形角方程，74.1同一中央取向的迹平方分解，以及74.5–74.7保留 $N-1$ 的全分割能量求和；它们共同将同一个原 $K_c(r)$ 送入运输续卷119.1。75.1给旧本征窗完全不可见的弥散原供应，76.1给原成员资格边界，77.1保留三份实际输出接回真正缺陷。未将标准模型的零缺陷当作一般证明。

复用55–62的固定输出与两角构造、运输118–119的零行和消费者、中央182.2的实际新框架与163.1的横向读数。中央162.2、163.4、163.6的仿射预算及锚身份是163.1证明中已有的子接口；不能将这些预算直接当作本条的区间迹求和，也不将它们重列为新增结果。配平三角240–251的一般JC包含和原Jordan正交响应面积亦已支付。完整有限、完整type I、有限秩或本质复紧理想的旧分类仍按60.1、68.1的全部原前件直接复用。

[三标签刚性卷36.1、43.1、49.2、63.1](AURIC_C128_THREE_LABEL_POSITIVITY_AND_ORIGINAL_RELATION_RIGIDITY.md#36-固定原第二型有限因子上的再生与全局取向)已有完整II₁平方背景上的全域分类分支；它们保留各自实际共轭、实部换括号式R、生成／辨识或关系读数律，以及相应前对偶、迹和评价条件。本条保留原A1–A3/P2/FULLPB而不另给一般R或全域旧识别，得到的是显式迹／原窗条件下的标量实际反射行和77.1的真正缺陷子族，不是重述那些更强前件下的全域II₁分类。

谱演算、正泛函分离、迹循环性、矩形角半内积、Sylvester算子形式和超有限模型都是 $\texttt{literature-attested}$ 的成熟中间工具，不分别列为本组新增定理。其准确数学引文与当前用途如下：

- J. Dixmier，[*Les anneaux d’opérateurs de classe finie*](https://www.numdam.org/item/ASENS_1949_3_66__209_0/)，*Annales scientifiques de l’É.N.S.*，3e série **66** (1949)，209–261，Théorème 10，印刷页249–250；引言页211明确不要求Hilbert空间可分。该定理的中心值映射固定中心、复线性、循环、正且在正元上忠实。75.1只用它与中心态复合取得分离有限正迹族，不从中取得原 $E$ 的投影或任何 $D$ 正则性。
- B. Blackadar，[*Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*](https://www.bruceblackadar.com/Mathematics/Cycr.pdf)，II.6.8.1–II.6.8.3的迹与矩阵放大，III.2.5.6–III.2.5.8的忠实中心值迹及分离标量迹，III.3.1.4与III.3.4.2(ii)的超有限二阶张量积，III.3.4.7的迹二范数；自伴谱演算仍沿60.2所引I.4.1、I.6.1。这里只作成熟工具的参数对应；有限角正交及72.1全部常数在73–74中直接给出。
- Q. Fang、C. E. Shin、Q. Sun，[*On Sylvester Equations in Banach Subalgebras*](https://arxiv.org/abs/2407.09752v2)，arXiv:2407.09752v2，Theorems 2.1–2.2。2.1要求逆闭Banach子代数及不交谱，2.2另要求正规算子和可控逆，估计依赖谱距离倒数与算子范数。任意不完备原 $E$ 没有这些自动资格；该文不供应原窗、不供应PB预算，也不为这里的 $1/|a-b|$ 常数背书。74.1的特殊有限迹平方身份已直接证明，无需一般双算子积分或Schur乘子定理。

这些引文支持成熟工具及其适用边界；承重综合不主张历史优先权、穷尽文献或解决外部开放问题。

**定义 78.2（七项同源合同逐项合取）。** 以下各项分别完整合取61.1、69.1相应项、[中央续卷199.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#199-来源几何与量子消费者的完整边界)、[194.2](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#194-新连接完整候选与量子消费者的范围)、[186.1–186.7](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md#186-七项原量子来源合同的准确消费者)、运输122.1及其全部上游来源、对象、条件和量词全文。以下是本定理的消费者对应，不是更短的替代合同；原世界、中心、经典、不等维块与静默部分均不删除。

1. 复Hilbert、可观测量与相干叠加：唯一原 $\Omega/\mathrm{native}$、原 $E/S/D$、跨评价配对、具名可取得标签、任意有限长度及零长度的全词同一 $q,K,J$、parent/ready、合法控制和实际相干准备完整保持。数学JC包含已付；但完整原复Gram、同一旧全域乘法和准确完成运输仍须其原桥梁。迹半内积、区间投影和临时反射不供应全 $B(H)$ 可取得像、任意向量准备或原完备性。
2. 原态、效果、质量与Born：原评价、原事件、准确效果区间、全部实际完整菜单与接受归属完整保持；共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、全部P9、独立 $W_e$、每个原中间切口及固定支持全质量继续取同一原来源。零、不等、次归一质量、原 $q$、中心权和中心经典混合保留，只对实际完整菜单的严格正总质量归一。$m_\tau$ 是辅助数学迹质量，不能替代任何原 $m_\gamma$ 或实际准备。
3. native、真正相关联合与张量：同一个实际非零相关联合、全词 $K/J$、交叉零、共同生成与分离、满足原局部全矩阵前件的忠实同向交换两腿、共同实现、所需重数、全部真正相关输入、中央对及递归同源参考完整保持。分别可达或边缘相同不等于联合；75.3的数学张量积只构造供应实例，不制造原物理子系统、联合准备或全原张量识别。
4. typed CP、Kraus与整台递归参考：原未归一回溯、每个合法typed前后接、反变合法复合、typed分区、全未来自然性和原箭头商下降完整保持。参考须覆盖系统、整个环境、全部成功／失败／细记录／port／post-port输出及每份输出的每个仍合法未来；三实际投影、各自支持内补、共同真实支持、忠实同向交换、全部相关正输入的intertwining与夹界、每个所需有限递归深度及累计支持的准确运输全部保留。数学压缩 $qyq$ 的正性与能量求和不构造这些实际箭头、参考或CP。
5. 整台仪器、TP、更新与Lüders：全部原输入运输、完整typed菜单、原接受端、整个环境和全部成功／失败／细记录／port／post-port输出及每份输出所有合法未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词和接受条件均保持。TP需完整单位分区，Lüders另需同一完整输出的像内射线校准；只归一正输出，零分支保留。密度、迹类和算子Kraus公式仍限准确合格的有限全矩阵原域，或另供应正规物理表示、指定前对偶及实际适用的收敛接口。有限数学迹及75.2的数学分割不代付这些条件。
6. 全部历史、全未来、真实返回与CountRead：全部合法顺序／自适应／并行历史、每份输出每个仍合法未来、整个环境、细记录和泄漏、停止／拒绝／销毁、真正分组遗忘、同数两侧及同数逆向真实返回完整保持。CountRead仍绑定读后同一原完整活动输入及全未来返回；负提升两条活路的分别控制与相干聚合、具名分析词到原完整菜单及接受端接线必须原生取得。精确正生成 $B$ 和闭正生成 $B_{\rm cl}$ 不混同；原程序、读取次序、$q$-零集及AC方向不因算子相同而等同。无限历史、无限／非离散记录、可数可加、正常性和指定前对偶各守原合同；辅助迹极限不供应物理无限记录或真实双向返回，未定义请求仍未定义。
7. 动力、物理钟、能量与共同尺度：同一旧全域乘法、保持可能不完备原域的流、真实相位及门序列、实际可逆一参数群及实际逆、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、原物理钟、共同作用量、共同正 $\hbar$ 和共同仪器完整保持。原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 继续取原合同含义；区间指标 $N$、数学迹、强度 $R$、谱中心与误差趋零都不生产物理时间、钟能量、控制成本或一般无界生成元。

**定义 78.3（非迹范围与剩余关系）。** 在一般非迹表示中，右乘 $c_j$ 对所选态半内积未必自伴，74.1的准确正交平方分解与74.5的迹角正交不能直接使用。若仅在算子范数中累积 $N$ 行角，可能保留 $\varepsilon_NN=C$，并不趋零；73.8的逐角小预算本身不足以宣告全局消失。因此不删除静态迹或原窗供应而把72.1移到型III、任意适当JC原域或任意不完备域。此处只限定这份证明，未断言完整PB在那些域中语义不足。

整个论证没有预付旧 $D$ 的一般可加、齐次、连续、可测、单位平移、协变、商／接触核下降、输出平方正性、完成延拓或与环境交换子的全域相同。几何上，背景不必在每格内完全恒定；同一次实际PB的剩余外表预算与格宽同阶，而同一中央取向把转动项和自伴项在迹能量中分开。同一有限迹的角质量使全部角的平方预算只积累 $N-1$，于是固定原缺陷被越来越细的实际测试认定为零。改变的是测试网络，原答案始终只有一份。一般无原窗／无分离有限迹的供应，以及任意原首标签的真正缺陷生产，仍是未由此解决的关系；完整量子起源及七项实际来源的完成标准不变。

## 追加锚（本行以下为增补区）

## 79. 完整有限 continuous 原域与中央取向候选

**定义 79.1（同一原对象及明确模型类）。** 本组以 SM、C、PT、PB、A 分别指[本谱混合卷](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md)、[中央续卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)、[原 PB 运输续卷](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md)、[配平三角续卷](AURIC_PB_TRIANGLE_ORIENTATION_AND_RANK_ONE_RESPONSE_CONTINUATION.md)及[任意维静态卷](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)。完整有限原域的反射行直接取 SM72.1与SM75.1，七项同源合同完整取 SM78.2及86.1；这些源中的完整原前件、实际框架、原输入及评价量词均保留。

保持唯一原 $\Omega/\mathrm{native}$ 及同一 $(E,C,u,N,\mathcal P,S,D)$。本组的明确数学环境是任意有限 continuous 复 von Neumann 代数 $M$，即纯 type $\mathrm{II}_1$ 代数：没有非零 type I 中央直和项。取

$$
E=M_{\rm sa},\qquad u=1,\qquad C=M_+,\qquad
N(a)=\|a\|,\qquad S(a,b)=a\circ b=\frac{ab+ba}{2}.
\tag{79.1}
$$

中心值迹是本模型明列的数学结构：

$$
T:M\longrightarrow Z(M),\qquad T(1)=1,
\tag{79.2}
$$

它正、忠实、正规、复线性、$Z(M)$-线性，并满足 $T(ab)=T(ba)$。不要求 $M$ 为因子、可分、可数可分解或存在全局忠实正规标量迹。结合乘法、伴随、范数、Borel 函数演算、极分解和 $T$ 属于此模型类的数学结构；它们的存在并未由一般 JB 原域的关系重新推出，也不代表实际物理准备、操作或正常读取。

$\mathcal P$ 是原正实线性评价族，分离 $E$ 且准确决定 $C$。每份原质量 $m_\gamma=\gamma(1)$ 保持原值，包含零、不等和次归一质量。保留完整 A1：每对原标签两条有向 Hermitian 二表正性；完整 A2：全部相加三表 $(a+b,a,b)$ 及其排列的实部在整个 $\mathbb R^3$ 上半正定，并有指定相加向量 $(1,-1,-1)$ 的零二次值；完整 A3：$S(u,u)=u$，且在同一个固定有理 $0<\theta\le1$ 上，$0\le y\le\theta u$ 蕴含 $S(y,y)\le y$。特别对全部原 $a,b\in E$、$\gamma\in\mathcal P$ 有完整 P2：

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(a\circ b)+i\gamma D(a,b)&\gamma(b^2)
\end{pmatrix}\succeq0.
\tag{79.3}
$$

同一原总映射 $D:E^2\to E$ 反对称。对全部原 $a,b,d\in E$ 保留完整 PB：

$$
\begin{gathered}
v=D(a,b)-a\circ d,\qquad w=a\circ b+D(a,d),\\
D(b+v,d+w)-D(b-v,d-w)=-2b\circ v-2d\circ w.
\end{gathered}
\tag{79.4}
$$

不预付 $D$ 的可加、齐次、连续、可测、协变、单位平移中性、输出小代数闭合或中央投影下降。所有辅助标签均须实际属于同一个完整原 $E$；“实际标签”在数学证明中只指原域成员，不宣称它已由物理程序制备。完整候选的七项实际来源合同取86.1，不能由79.1的模型类限制删去其中的原对象或量词。

**定义 79.2（正读取与中心平衡反射）。** PT118.2、PB129.1使每个数学正实线性泛函 $\phi:E\to\mathbb R$ 都能读取同一张原表，且

$$
|\phi D(a,b)|^2\le
\phi(a^2)\phi(b^2)-\phi(a\circ b)^2.
\tag{79.5}
$$

确实，对固定两个复系数，原二表的二次型是 $E$ 中的元素；全部原评价读它非负，准确锥就使它为正，所以其他数学正泛函也读它非负。这不增加实际准备族。特别 $D(a,0)=D(0,a)=0$，且 $\|D(a,b)\|\le\|a\|\|b\|$；零读取质量从不作除法。

记

$$
\mathcal H_0=\{h\in M_{\rm sa}:h^2=1,\ T(h)=0\}.
\tag{79.6}
$$

“中心平衡”指 $T((1+h)/2)=T((1-h)/2)=1/2$，比任取一个标量迹为零更准确。

**定理 79.3（全域原响应的唯一共同中央取向）。** 在79.1的全部原前件下，存在唯一

$$
Q\in Z(M)_{\rm sa},\qquad Q^2=1,
\tag{79.7}
$$

使同一原响应在全部原输入上满足

$$
\boxed{D(a,b)=\frac{iQ}{2}[a,b]\qquad(a,b\in M_{\rm sa}).}
\tag{79.8}
$$

在任意实际反交换反射框架 $h^2=e^2=1,he=-eh$ 上，取向由旧响应内生给出：

$$
Q=iheD(h,e).
\tag{79.9}
$$

反过来，每个79.7的中央自伴对合按79.8定义的响应都满足全部数学 A1–A3、P2、PB，保留同一锥、范数、原评价及全部质量。证明见80–84；实际物理来源的条件接回另见86。零代数时 $E=0$，唯一 $Q=0=1_M$，全部式子平凡成立；以下构造对非零 $M$ 叙述。

## 80. 中心比较、实际配对轴与既有完整反射行

**引理 80.1（原代数内的投影供应）。** 对79.1的 $M$，有

$$
T(p)=T(q)\quad\Longleftrightarrow\quad p\sim q
\qquad(p,q\text{ 为投影}).
\tag{80.1}
$$

每个投影 $p$ 均有实际等半分解

$$
p=p_1+p_2,\qquad p_1p_2=0,\qquad p_1\sim p_2,
\qquad T(p_1)=T(p_2)=\tfrac12T(p).
\tag{80.2}
$$

证明。先说明80.1中需要的中心比较。等价投影的中心迹相同由迹性给出。反向，在 $p,q$ 下选极大的匹配部分等距族，使各初投影两两正交、各末投影两两正交；其强和 $v$ 仍为部分等距。余投影 $p_0=p-vv^*$、$q_0=q-v^*v$ 满足 $p_0Mq_0=0$，否则非零角元素的极分解可添加一项。投影生成的弱闭双侧理想由其中央载体生成，故 $p_0Mq_0=0$ 使 $p_0,q_0$ 的中央载体正交。另一方面，$T(p_0)=T(q_0)$；这个共同中央正元分别支撑于两个正交中央投影，只能为零。$T$ 忠实，故 $p_0=q_0=0$，于是 $p\sim q$。

对80.2，在 $pMp$ 中选极大的投影对族 $(a_\alpha,b_\alpha)$，所有投影共同两两正交且每对非零、等价。若其和的余投影 $r$ 非零，纯 type II 性保证 $rMr$ 不交换：非零交换角会给非零 type I 中央部分。非交换 von Neumann 角内有非中央投影 $e$，因而有非零 $eM(r-e)$ 元素；其极分解产生另一对正交等价子投影，违背极大性。所以余投影为零。取两列的强和为 $p_1,p_2$，对应部分等距的强和实现 $p_1\sim p_2$，迹性给80.2。$p=0$ 时两半取零。此处只使用已给代数的投影、极分解及强闭合，没有涉及 $D$ 的下降或极限。∎

这是成熟投影比较及连续投影切割的应用，不另计数学新内容。80.2在 $p=1$ 给 $\mathcal H_0\ne\varnothing$。对每个 $h\in\mathcal H_0$，80.1将 $p_-=(1-h)/2$ 匹配到 $p_+=(1+h)/2$；取

$$
v^*v=p_-,\quad vv^*=p_+,\qquad e=v+v^*.
\tag{80.3}
$$

于是 $e=e^*$、$e^2=1$、$he=-eh$，且 $T(e)=0$。这些都是原 $E$ 的元素。反过来，任何具有全域反交换反射轴的反射均中心平衡，因为 $ehe=-h$ 及迹性给 $T(h)=-T(h)$。

**复用 80.2（SM72.1、SM75.1的准确实例）。** 固定80.3的实际 $h,e$，令 $j=D(h,e)$。[中央原卷62.1、77.1–77.2、100.1](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md)及 C123.1、C133.1–134.1在这些相同原前件下已经给

$$
j^2=1,\quad hj=-jh,\quad ej=-je,\qquad
Q_h=ihej\in Z(M)_{\rm sa},\quad Q_h^2=1.
\tag{80.4}
$$

这里 $\mathcal A=C^*(M_{\rm sa})=M$，所以该源中的全局中央性正好是 $Z(M)$ 的中央性；不要求 $Q_h$ 为标量。对任意原 $x$，取

$$
c=\frac{x+hxh}{2},\qquad z=\frac{x-hxh}{2}.
\tag{80.5}
$$

SM71.1的同一原域、Jordan乘法、准确锥、单位、范数、总 $D$、全部原评价及其质量、完整 A1–A3、全部 P2和完整 PB，逐项取79.1的相同对象；其中 $X=E=M_{\rm sa}$、$\mathcal A=M$。80.3–80.4供应该源要求的实际 $h,e,j=D(h,e)$ 框架及中央取向 $Q=Q_h$。80.5中的 $c,z$ 均在完整原域，分别满足 $[h,c]=0$、$hz=-zh$。

SM75.1适用于这同一个有限 von Neumann 代数及完整自伴原域，因而供应 SM71.2–71.3：以79.2的 $T$ 与中心的全部态 $\chi$ 复合，$\tau_\chi=\chi\circ T$ 是分离正元的有限正标量迹族；$T$ 的忠实性与中心态分离性支付该分离条件，不要求单个忠实标量迹。每个非零偶背景 $c$ 的全部所需有限区间投影都属于原 $E$，且给每个正整数 $N$ 的原分割；$c=0$ 时直接取 SM72.1的零背景分支。这些静态供应与未知输出无关，也不是新增物理评价或准备。

因此对这份固定 $x=c+z$，取 SM72.1中的 $R=1$，直接由其式(72.3)取得同一个原输出的完整第二输入行：

$$
\boxed{D(h,x)=iQ_hhz=\frac{iQ_h}{2}[h,x]
\qquad(h\in\mathcal H_0,\ x\in E).}
\tag{80.6}
$$

这条完整行及其谱窗证明属于 SM72.1、SM75.1的既有结果，不作为本组新增。它们还给全部实 $R$ 的 $D(Rh,c+z)=RiQ_hhz$；这里仅消费 $R=1$，不需要额外仿射行。若对同一 $h$ 另选轴得到 $\widetilde Q_h$，两份80.6都能在旧轴 $x=e$ 上使用，故 $(Q_h-\widetilde Q_h)he=0$；$he$ 可逆，取向相同。因此80.6已消除配对轴选择的歧义。

## 81. 全部反射行的唯一共同中央取向

**定理 81.1（不使用中央下降的拼接）。** 80.6中的全部 $Q_h$ 相同。

证明。任取 $h,k\in\mathcal H_0$。对完整原行使用原反对称性，得到全域等式

$$
(Q_h-Q_k)[h,k]=0.
\tag{81.1}
$$

记 $z_0=\mathrm c_Z([h,k])$ 为交换子的中央载体，即满足 $z_0[h,k]=[h,k]$ 的最小中央投影。中央投影 $(1-Q_hQ_k)/2$ 正好是 $Q_h-Q_k$ 的支撑；81.1使它在该交换子上为零，所以

$$
z_0(Q_h-Q_k)=0.
\tag{81.2}
$$

在余中央投影 $p=1-z_0$ 上，$ph,pk$ 交换。其四个真正联合投影为

$$
p_{\epsilon\delta}=\frac p4(1+\epsilon h)(1+\delta k),
\qquad \epsilon,\delta\in\{1,-1\}.
\tag{81.3}
$$

由 $T(ph)=T(pk)=0$，有

$$
T(p_{++})=T(p_{--}),\qquad
T(p_{+-})=T(p_{-+}).
\tag{81.4}
$$

80.1遂给实际部分等距 $v_1,v_2$，满足

$$
v_1^*v_1=p_{++},\quad v_1v_1^*=p_{--},\qquad
v_2^*v_2=p_{+-},\quad v_2v_2^*=p_{-+}.
\tag{81.5}
$$

若某对为零，该部分等距取零；若一侧为零，中心迹相等及忠实性已使另一侧也为零。四角支撑共同正交，所以

$$
f=v_1+v_1^*+v_2+v_2^*
\tag{81.6}
$$

满足

$$
f=f^*,\quad f^2=p,\quad T(f)=0,\qquad
f(ph)=-(ph)f,\quad f(pk)=-(pk)f.
\tag{81.7}
$$

中心迹为零来自各个非对角项的迹性，不是从两个边缘分布另选联合实现。两对部分等距同时支撑于这同一份实际四角分割。

取 $h$ 的80.3配对轴 $e_h$，在原 $M$ 内定义一枚全域反射

$$
\ell=z_0e_h+f.
\tag{81.8}
$$

中央正交使 $\ell=\ell^*$、$\ell^2=z_0+p=1$、$T(\ell)=0$，并且 $h\ell=-\ell h$。因此 $\ell\in\mathcal H_0$，$[h,\ell]=2h\ell$ 可逆。将81.1应用于完整原行 $h,\ell$，立即得

$$
Q_\ell=Q_h.
\tag{81.9}
$$

对完整原行 $k,\ell$ 同样有 $(Q_k-Q_\ell)[k,\ell]=0$。只在这条已经成立的全域等式上乘中央投影 $p$。若 $p\ne0$，81.7给

$$
p[k,\ell]=2pk\ell,
\tag{81.10}
$$

它在 $pM$ 中可逆，所以 $p(Q_k-Q_h)=0$。若 $p=0$，这部分结论本来为空。结合81.2，得 $Q_k=Q_h$。

这也覆盖 $z_0=0$、$h=k$、$h=-k$、任意联合角为零以及没有剩余补角的情形。全程没有使用 $D(pa,pb)=pD(a,b)$；中央投影只用于制造原元素，以及乘已经成立的全域等式。记共同值为 $Q$。任取一份实际反交换框架即由80.4给79.9，也给唯一性。∎

## 82. 六反射文献工具与十二个中心平衡因子

**复用 82.1（精确有限群工具）。** B. V. Rajarama Bhat、Soumyashant Nayak、P. Shankar，[*On products of symmetries in von Neumann algebras*，arXiv:2204.00009v1](https://arxiv.org/pdf/2204.00009v1)，Theorem 3.9，印刷第8页、证明第8–9页，给出：type $\mathrm{II}_1$ von Neumann 代数中，每个酉元是该代数内六个 symmetries，即六个自伴酉元的精确乘积。

该源并未把结论限于因子。其 Lemma 3.5通过 Kadison 的 MASA 切割供应与指定酉元交换的等中心迹投影；Lemmas 3.7–3.8使用二、三阶角和中心值迹。Theorem 3.9按 $T(F^{(n)})=3\cdot4^{-n}1$ 构造相互正交、与指定酉元交换的块，将相邻等中心迹角配对为 $\operatorname{diag}(B,B^*)$；四列强和给四枚实际反射，剩余强和为另两枚反射之积。强和是在已给代数中构造六个元素，最终结论是有限精确等式。这里只消费 Theorem 3.9；Theorem 3.12及其 Corollary 3.13的有限谱四反射／范数稠密结论不足以代替它。

**引理 82.2（中央直和与平衡化的实际桥）。** 79.1的每个酉元 $U$ 都可写成

$$
\boxed{U=h_1h_2\cdots h_{12},\qquad h_j\in\mathcal H_0.}
\tag{82.1}
$$

证明。为使引用不依赖 Kadison 切割的非可数可分解版本，先在中心取极大的正交非零投影族 $(z_\alpha)$，使各 $z_\alpha Z(M)$ 有忠实正规归一状态 $\omega_\alpha$。这族和为1：任一非零中央余部上都有非零正规正泛函，其支撑是该余部内一个新的非零中央投影，限制后归一即为其支撑角的忠实正规状态，违背极大性。因此

$$
\tau_\alpha=\omega_\alpha\circ T|_{z_\alpha M}
\tag{82.2}
$$

是 $z_\alpha M$ 的忠实正规归一标量迹，使该中央直和项可数可分解；并未要求其预对偶可分。在这些纯 type II₁ 中央直和项上使用82.1的文献工具，得

$$
z_\alpha U=s_{\alpha,1}\cdots s_{\alpha,6},
\qquad s_{\alpha,j}=s_{\alpha,j}^*,\quad s_{\alpha,j}^2=z_\alpha.
\tag{82.3}
$$

对每个固定编号 $j$，取中央正交强和 $s_j=\sum_\alpha s_{\alpha,j}$。部分和一致有界，强和属于 $M$；各中央角上的计算给 $s_j=s_j^*$、$s_j^2=1$，并给

$$
U=s_1\cdots s_6.
\tag{82.4}
$$

这里可有不可数多个中央直和项，但只拼接六列实际算子；没有因子直积分中的可测选择，也从未拆分未知 $D$。

对任意一枚自伴酉元 $s$，记 $p_\pm=(1\pm s)/2$。由80.2，在两个角内分别选半投影 $r_\pm\le p_\pm$，使 $T(r_\pm)=T(p_\pm)/2$，零角取零。置

$$
h=2(r_++r_-)-1,\qquad k=sh.
\tag{82.5}
$$

$h$ 与 $s$ 交换，故 $h,k$ 都是自伴酉元、$hk=s$。并且

$$
\begin{aligned}
T(h)&=2T(r_+)+2T(r_-)-1=0,\\
T(k)&=2T(r_+)-T(p_+)-2T(r_-)+T(p_-)=0.
\end{aligned}
\tag{82.6}
$$

所以每个 $s_j$ 都是两个 $\mathcal H_0$ 元素之积，82.4给82.1。包括 $s=1$、$s=-1$ 在内的端点也已覆盖。∎

这些是成熟六反射工具的中央直和和平衡化消费者，不宣称最短长度。82.1不要求这十二枚反射来自某个固定因子中的共轭类；下文只需要它们各自拥有81.1支付的同一完整原行。十二是完整反射行取得后的运输长度，不是包括所有上游调用在内的 PB 总次数。

## 83. 同一个正平方的有限原 PB 运输

**定义 83.1（原标签对的中央复坐标）。** 置 $J=iQ$。于是

$$
J\in Z(M),\qquad J^*=-J,\qquad J^2=-1.
\tag{83.1}
$$

原实标签对与 $M$ 之间有双射

$$
Z=x+Jy,\qquad
x=\frac{Z+Z^*}{2},\qquad y=-\frac J2(Z-Z^*).
\tag{83.2}
$$

逆式的两个标签均自伴，且属于完整原 $E$。这里只重排原标签对，没有定义 $D$ 的复线性延拓。以同一原响应定义函数

$$
q_D(Z)=x^2+y^2+2D(x,y).
\tag{83.3}
$$

此时不赋予 $q_D$ 可加、齐次、连续或二次型性质。79.5使每个数学正读取都给

$$
\phi(q_D(Z))\ge
\phi(x^2)+\phi(y^2)-2\sqrt{\phi(x^2)\phi(y^2)}\ge0,
\tag{83.4}
$$

所以 $q_D(Z)\in M_+$。这个正平方函数保留原输出，而非另选一个标准响应。

**定理 83.2（正平方的精确共同轨道）。** 对所有 $Z\in M$、$U\in\mathcal U(M)$，

$$
q_D(UZ)=q_D(Z)=Z^*Z.
\tag{83.5}
$$

证明。固定 $h\in\mathcal H_0$ 及任意原标签 $x,y$。在真正原三元组 $\operatorname{PB}(h,x,y)$ 中置

$$
v=D(h,x)-h\circ y,\qquad
w=h\circ x+D(h,y).
\tag{83.6}
$$

80.6、81.1已经同时识别这两份实际内值为 $J[h,x]/2$、$J[h,y]/2$。只在已知结合代数内计算，得

$$
v+Jw=Jh(x+Jy)=JhZ,
\qquad (x\pm v)+J(y\pm w)=(1\pm Jh)Z.
\tag{83.7}
$$

而完整 PB 恰好是

$$
q_D((1+Jh)Z)=q_D((1-Jh)Z).
\tag{83.8}
$$

两边之差的展开为 $4x\circ v+4y\circ w$ 加上两份外响应之差的两倍，故79.4准确消去它；没有展开未知 $D$ 的输入和。

对给定 $Z$，另取实际原坐标对83.2对应的

$$
Z_0=(1-Jh)^{-1}Z=\frac{1+Jh}{2}Z.
\tag{83.9}
$$

因为 $(Jh)^2=-1$，有 $(1+Jh)(1-Jh)^{-1}=Jh$。将83.8应用于这另一份实际输入，直接得到

$$
q_D(JhZ)=q_D(Z).
\tag{83.10}
$$

83.9中的 $1/2$ 没有从未知函数中提出；它只属于重新选定的原标签。

对82.1的十二个中心平衡反射，有

$$
(Jh_1)\cdots(Jh_{12})=J^{12}U=U,
\qquad J^{12}=(iQ)^{12}=1.
\tag{83.11}
$$

有限次使用83.10，便给 $q_D(UZ)=q_D(Z)$。这没有使用 $D$ 或 $q_D$ 的任何正则性、酉协变假设、稠密酉群或输入极限。

最后取原 $Z$ 的极分解 $Z=v|Z|$，记 $p=v^*v$、$q=vv^*$。迹性给 $T(p)=T(q)$，所以 $T(1-p)=T(1-q)$。80.1给实际补部分等距 $w$：

$$
w^*w=1-p,\qquad ww^*=1-q.
\tag{83.12}
$$

于是 $V=v+w$ 为酉元，且 $V^*Z=|Z|$。这包括 $Z=0$、不可逆 $Z$、任意初末支撑及补角为零的情况。$|Z|$ 的83.2坐标为 $(|Z|,0)$，故零槽 P2 给

$$
q_D(Z)=q_D(V^*Z)=q_D(|Z|)=|Z|^2=Z^*Z.
\tag{83.13}
$$

证明83.5。∎

对83.2再直接展开 $Z^*Z=(x-Jy)(x+Jy)=x^2+y^2+J[x,y]$。比较83.3、83.13，得到79.8。若另一中央对合 $\widetilde Q$ 给同一原响应，在任一实际反交换框架上有 $(Q-\widetilde Q)he=0$；$he$ 可逆，故 $Q=\widetilde Q$。正向及唯一性证明完成。

## 84. 反向、同一旧乘法与完整静态等价

**命题 84.1（每个中央取向的全域反向）。** 固定79.1的数学环境、原评价和全部质量，任给79.7的 $Q$，按79.8定义 $D_Q$，则全部原数学关系成立。

证明。置 $q_\pm=(1\pm Q)/2$，在同一个复向量空间上取

$$
A_Q=q_+M\oplus(q_-M)^{\rm op},\qquad
X\star Y=q_+XY+q_-YX.
\tag{84.1}
$$

这是既有代数与相反代数的中央直和，保持同一伴随、单位、范数及正锥。对原自伴标签，

$$
a\star b=a\circ b-iD_Q(a,b).
\tag{84.2}
$$

每个原正实评价在 $A_Q$ 上仍有其正复线性延拓。C*正泛函的 Cauchy–Schwarz 因而给

$$
\gamma(a\circ b)^2+\gamma D_Q(a,b)^2
\le\gamma(a^2)\gamma(b^2),
\tag{84.3}
$$

即全部原 P2和两条有向 Hermitian 二表正性。无须评价归一；零质量处正泛函恒零。相加三表的实部是同一实双线性正型 $\gamma(a\circ b)$ 的 Gram 表，相加向量的平方准确为零；$0\le y\le\theta1\le1$ 时函数演算给 $y^2\le y$，且 $S(1,1)=1$。所以完整 A1–A3亦成立。

对任意原 $a,b,d$，令 $J=iQ$、$Z=b+Jd$，并用 $D_Q$ 取79.4的 $v,w$。已知乘法直接给

$$
v+Jw=JaZ,\qquad q_{D_Q}(Z)=Z^*Z.
\tag{84.4}
$$

由于 $a=a^*$、$J$ 中央且 $J^*=-J$，

$$
q_{D_Q}((1\pm Ja)Z)=Z^*(1+a^2)Z.
\tag{84.5}
$$

两符号的平方相等，正是全部原三元组的 PB。证明没有只检查重复、单位或线性第三标签的子族。反向只实现数学关系，不制造任何原物理来源。∎

**推论 84.2（同一旧静态结构的准确消费者）。** 在79.1下，79.8使原 $D$ 实双线性，中央平移及中央投影下降成为结论；例如对中央投影 $p$，

$$
D(pa,pb)=pD(a,b).
\tag{84.6}
$$

它并未用于81、82的拼接。每个固定 $a$ 的同一有界内导子

$$
L_a(X)=[iQa/2,X]\qquad(X\in M)
\tag{84.7}
$$

同时实现全部 $L_a(b)=D(a,b)$，并且

$$
T(D(a,b)\circ c)=-T(b\circ D(a,c)).
\tag{84.8}
$$

这些由已识别的交换子和迹性直接读出，不是逐对共同实现的入口假设。

A32.2现在以原 $\gamma\circ S,\gamma\circ D$ 为其相同参数，给完整原 $\mathsf P_3$ 和全部有限原复 Gram 正性；原词卷400.1–400.2不重证。A23.1继而以同一 $\mathsf H_{\rm orig}+\mathsf P_3+\mathsf{PB}$ 给全部原输入上的原 R：

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)).
\tag{84.9}
$$

此时才按原 $\star=S-iD$ 作复双线性延拓。其乘法正好是84.1，故同一原复化为 $A_Q$，自伴部、锥、单位和范数准确保持。A6.3、A7.1–7.3、A8.1–8.5、A14.2、A25.1的既有消费者逐项适用，参数是这同一个原 $S,D,\mathcal P$；它们不要求 $M$ 为因子，不把各原质量合成一份迹。完整七项实际来源仍取86.1。

**定义 84.3（完整候选及减少的独立数学要求）。** 在明确的79.1模型类 $\Gamma_{\rm cont}$ 内，有全域分类

$$
\mathsf H_{\rm orig}+\mathsf{PB}
\quad\Longleftrightarrow\quad
\exists!Q\in Z(M)_{\rm sa},\ Q^2=1,\
D(a,b)=iQ[a,b]/2\ (a,b\in E).
\tag{84.10}
$$

因此，在同一完整原来源合同 $\mathcal C_{\rm src}$ 下，完整条件候选有同域等价

$$
\begin{aligned}
&\Gamma_{\rm cont}+\mathsf H_{\rm orig}+\mathsf{PB}
+\mathcal C_{\rm src}\\
&\qquad\Longleftrightarrow\quad
\Gamma_{\rm cont}+\mathsf H_{\rm orig}+\mathsf P_3
+\mathsf{PB}+\mathcal C_{\rm src}.
\end{aligned}
\tag{84.11}
$$

原 R、双线性、全部有限复 Gram 和共同乘法不必另列为此模型类中的独立数学要求。没有计算一般量子起源的最小独立公理数，也没有证明模型类、准确锥、完整原域或七项来源合同之间的独立性。完整物理来源同时成立仍是候选的实际条件。

## 85. 中央取向与一个正平方的几何、反事实及来源边界

**定义 85.1（两元关系的三元提升）。** 二元原表限制同一输入对在每个原评价中的正预算；第三标签的 PB 把不同外表绑定到同一次原内值。SM72.1、SM75.1的谱窗结果固定同一个 $g=D(Rh,c+z)$ 和余量 $r$，只细化已知背景的有限区间读取。其 SM74.1的同一中央取向平方分解与 SM74.5–74.7保留全部角数成本的迹质量求和，共同迫使固定余量消失；分离有限正迹族由同一中心值迹与中心态供应。它不把一列近似输入的响应当作旧答案的极限。

完整反射行之后，81.1用同一实际联合四角连通行取向，而不是逐因子挑选符号。一个中央对象 $Q$ 同时决定全原域；中央投影 $q_+,q_-$ 分别采用给定乘法和相反乘法。83.2的辅助坐标随该共同取向调整，三标签 PB 随即保持一个原正平方 $q_D$。每个精确左酉轨道都有正代表 $|Z|$；零第二标签处的原预算确定它的平方。十二个精确因子的共同相位消除，使同一个平方沿整条轨道被认回为 $Z^*Z$。

在因子中，中央取向退化为全局正负号；本表述允许任意中心，不要求因子或全局忠实标量迹，以一个共同中央取向及一个正平方轨道组织全域识别，反射行取得后的精确运输用十二项即可。它没有删除79.1的背景结构、准确锥、完整原域或物理来源；三轴、中央两分支及三标签都不规定物理空间维数。

**命题 85.2（偏离结论的实际矛盾位置）。** 若两条完整反射行在某个非零中央部分取向不一致，81.8的同一全域 $\ell$ 使81.9成立，并在交换补部使81.10可逆，故它们不能同时满足原反对称性。若全部反射行已共同取向，而某份原对 $(x,y)$ 仍偏离79.8，令 $Z=x+Jy$，则

$$
q_D(Z)\ne Z^*Z=q_D(|Z|).
\tag{85.1}
$$

取83.12的补角酉 $V$，将 $V^*$ 按82.1分解。依其乘积作用次序形成十二步左作用链；链的两端分别为 $Z$ 和 $|Z|$。若每步83.10均成立，两端平方必相等，与85.1矛盾，所以至少一步违反83.10。每一步都是在当时输入 $W$ 上重新选择实际 $W_0=(1-Jh)^{-1}W$ 后的一份原 PB，其两份已知内值由完整原行供应。因此这一偏离必与一份实际原三标签关系冲突，不能由给未知 $D$ 增加正则性来解释。这里“实际”仍指同一原域内的合法数学输入，不宣称构造了实验操作。∎

**定义 85.3（准确复用、新连接及未扩大范围）。** 完整反射行及其原区间窗、中央取向迹平方分解和全分割能量求和属于 SM72.1、SM73–75。有限全矩阵、完整 type I、原有限秩和紧背景的既有分类继续按 PB142–143、152、160、167–174的准确前件复用，相同输出均为零新增。完整 II₁平方背景的既有全域分类按 SM78.1所引三标签刚性卷36.1、43.1、49.2、63.1的实际共轭、原 R、生成／辨识或关系读数律及相应迹、评价和前对偶等各自准确前件复用，不把这些较强前件加入79.1。本组不再把这些已有结论当新成果。

本组新增连接归为 $\texttt{repo-derived}$ 综合：81的全域中央载体与相反联合角拼接，82对所需精确群工具的中央直和／平衡化适配，以及83将同一原正平方经有限 PB 运输到正代表的全域识别。投影比较、连续投影等半、极分解、C*相反代数和正泛函 Cauchy–Schwarz是成熟工具；Bhat–Nayak–Shankar v1 Theorem 3.9是 $\texttt{literature-attested}$ 的六反射供应。这些辅助工具的应用不各自取得新数学内容名义。不声称文献穷尽、外部开放问题结算或历史优先权。

79.1要求原域本身为完整 $M_{\rm sa}$：所有投影、辅助反射、中央坐标与83.9重基后的标签都因此属于原域。纯 type II₁用于每个角内的平分和六反射供应；有限性与中心值迹用于投影比较和极分解补角，SM75.1还以中心态复合的分离有限迹族供应 SM72.1的固定谱窗余量识别。没有使用原物理评价正规性，也未使用未知 $D$ 的输入极限。

一般稠密不完备原域、一般 JB 原域、仅有有限商的原载体、type III以及混有其他类型的全域拼接，不在本定理的声明范围内；不将其改判为已证或给出反例。数学 $T$ 及82.2的辅助状态不支付实际正常性、无限历史、CountRead或指定物理前对偶。此处为纸面定义、定理与证明，不是 Lean kernel 认证。

## 86. 完整七来源合同与量子公理的逐项消费者

**定义 86.1（逐项全文合取）。** $\mathcal C_{\rm src}$ 分别完整纳入 SM78.2、C199.2对应项、C194.2对应行、C186.1–186.7对应条的全文及其全部上游来源、对象、条件、实现和量词，并与 SM43.2、49.1、61.1、69.1、PT122.1、A8.3–8.4、14.2、25.1共同合取。以下逐项列明保留的合同及本组消费者，不以某个简短表格替换原合同。不更换原 $\Omega/\mathrm{native}$，不削去原中心、经典、不等维块或静默部分；79.1只选择本定理处理的数学原域，其他实际来源义务保持原身份。

1. **复 Hilbert、可观测量与实际相干叠加。** 完整保持 C145.1–145.7、C155.1、C160.3、C171.1–171.7、C181.3、原多项式卷87.1及其上游。79.8、84.2支付同一旧全域乘法、全部有限旧复 Gram 和原 R，随后消费 A6.3、8.1的数学 Hilbert 表示。唯一原 $\Omega$、原 $E/S/D$、跨评价指定配对、具名可取得标签、native、任意有限长度及零长度的全词同一 $q,K,J$、parent/ready、合法控制及实际相干准备，仍完整取 C171.1、A8.3–8.4、14.2、25.1、三标签卷8.2–8.5、80.1。全部根、静默及零活动分支、具名原程序和各自原词身份保持其上游量词；数学表示、谱投影、反射和辅助酉元不供应全 $B(H)$ 可取得性、任意向量准备或实际控制。

2. **原态、效果、全部质量与完整 Born 菜单。** 完整保持 C171.2、C145.2、A25.1第2行的同一原评价、原事件、准确效果区间、所有实际完整菜单及接受归属。共同根、抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度、全部 P9分支、各自独立 $W_e$、全部原中间切口及固定支持全质量均守原来源。原 $q$、中心权、中心经典混合、经典不等维块、静默部分以及零、不等、次归一质量全部保持；只对该实际完整菜单的严格正总质量归一。A7.1、7.3给原正权和准确效果的数学入口；$T$、82.2的辅助迹、压缩读取和数学正延拓不增加实际准备、效果或菜单。一般无限维态保留其自身的正泛函或已付前对偶表示，不擅自写成有限密度矩阵。

3. **native、真正相关联合与张量。** 完整保持 C171.3、C145.3、A25.1第3行、A53.1及单位桥95.2、116.1要求的同一个实际非零相关联合。原全词 $K/J$、交叉零、忠实同向交换局部腿、共同实现、联合生成与分离、所需重数、全部真正相关输入、中央对、经典和不等维块、实际复制及递归同源参考均保持；原要求局部全矩阵前件之处仍须支付该前件。只有这些条件和同一旧乘法同时齐备，才消费其适用域的原张量识别。分别可达、相同边缘、相同取向和同一数学轨道不能替代真正共同来源；80的两角、81的联合投影及82的矩阵角不制造物理子系统或自由参考。

4. **typed CP、Kraus 接线与每层递归同源参考。** 完整保持 C171.4、C145.4、A25.1第4行的原未归一回溯 $\alpha_A(\beta_rb)=\alpha_B^r(b)$、每个合法 typed 前接／后接、反变合法复合、typed 分区、全未来自然性、全质量运输和原箭头商下降。CP需原完整同标签单位区间过程比较，或原整台递归同源参考。参考覆盖整台当前实际箭头：系统、整个环境、全部成功／失败／细记录／port／post-port输出及每份完整输出的每个仍合法未来。系统腿和参考腿共同真支持且忠实同向交换；三实际投影、各自支持内补、共同真实支持上的准确运输、全部相关正输入上的 intertwining与夹界、锥分离、每个所需有限递归深度及累计支持完整链均保留。任意精度路线保留每个正精度、每个有限深度及精确根身份，固定正误差不足。支持内补不改成环境补，累计真支持不改成环境单位。只有合格有限全矩阵 CP域，或另有适用正规物理表示、指定前对偶与所需收敛时，才消费算子 Kraus公式；一般正规子代数的正常 CP对偶不自动成为全 $B(H)$ 上的算子 Kraus表示。84.7的数学内导子和数学正压缩不构造实际箭头、参考或 CP。

5. **整台仪器、TP、更新与 Lüders。** 完整保持 C171.5、C145.5、A25.1第5行的全部原输入运输、完整 typed 菜单、原接受端、整个环境、所有成功／失败／细记录／port／post-port输出及每份输出的全部合法未来、真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及接受条件。原星乘法和 A7.3的正夹心供给代数入口；次单位只给 TNI，TP仍需整个原测试的完整单位分区。Lüders仍需同一个完整输出的投影效果、像内每条射线保持及完整输出校准，同效果、同概率或重复性不足。仅严格正的实际输出质量可归一，失败及零分支连同其未来都保留。密度、迹类和算子 Kraus公式只在准确合格的有限全矩阵原域，或另有适用正规物理表示、指定前对偶与所需收敛时消费；数学 $T$ 的存在及正规性不支付这些物理前件，也不允许密度公式抹去细记录或 port未来。

6. **全部合法历史、全未来、真遗忘、两侧返回与 CountRead。** 完整保持 C171.6、C145.6、A8.4、25.1第6行及单位桥原消费者的所有合法顺序／自适应／并行历史，每份输出的所有仍合法未来，整个环境、参考副本、全部细记录和泄漏，停止／拒绝／销毁，真正分组遗忘，同数两侧真实返回及同数逆向真实返回。只有原真正粗事件可相加，丢弃记录不是真遗忘。CountRead绑定读后同一原完整活动输入及全未来返回；负提升两条活路的分别控制、相干聚合、具名分析词到完整原菜单及接受端的接线仍须原生供应。精确正生成 $B$ 与另名闭正生成 $B_{\rm cl}$ 区分；原 $q$零集、AC方向、程序身份和实际读取次序不由算子相同而等同。无限历史、无限／非离散记录的可数可加、正常性、指定前对偶及所需收敛各守原来源。既有 native initialRead和指定有限树／被动精确混合解码仍守其平稳、真实同源、同初始版本的范围；初始取得不供应整份后续输出的全部未来 Return。数学中心迹、辅助状态和十二步精确运输不供应无限物理记录；未定义请求仍未定义。

7. **动力、物理钟、能量与共同正作用量。** 完整保持 C171.7、C145.7、A25.1第7行的原动力合同：同一旧全域乘法、保持原域的流、真实相位和门序列、实际过程内可逆一参数群及其逆、原物理钟与单位、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同仪器和作用量以及同一个正 $\hbar$。这些前件齐备后，才消费 $U(t)=e^{-itH/\hbar}$ 及适用域上的 $i\hbar\dot\rho=[H,\rho]$。原 $\sigma,t_0,d$、固定域、resolvent和 $3s+r\le1$ 保持各自含义，与本组 $Q,J$、反射及谱窗参数区分。84.7只给数学有界内导子，不给物理时间、实际门流、可控相位、钟能量、控制成本、一般无界生成元域或共同 $\hbar$。

**定义 86.2（与旧 QM 公理的准确条件映射）。** 下表的消费者均是已存在的条件结果；本组供应其同一旧静态入口，86.1的每项全文和全部量词均留在每一行的适用条件中。

| 旧 QM 结构 | 本组实际支付及被消费的既有结果 | 仍须同一原世界支付的物理条件 |
| --- | --- | --- |
| 复 Hilbert、可观测量、相干叠加 | 79.8、84.1–84.2识别同一 $A_Q$；A32.2、23.1、6.3及8.1给全部有限 Gram、原 R与忠实保锥等距表示 | 86.1第1项：全词 $K/J/q$、原标签与跨评价配对、parent/ready、合法同源控制及实际相干准备；表示不自动满射到 $B(H)$ |
| 态、效果、Born概率与质量 | A7.1、7.3、8.1、25.1第2行：原效果是 $[0,1]$，原权为 $\gamma(f)$，只在 $m_\gamma>0$ 时用 $\gamma(f)/m_\gamma$；GNS向量范数平方为原质量 | 86.1第2项：完整原菜单、准备、接受归属、全部支持和中间切口；零／不等／次归一质量及中心权保留，密度式另需准确表示条件 |
| 复合系统、真正相关联合与张量 | 84.1的同一乘法进入 A53.1、A25.1第3行及单位桥95.2、116.1的既有联合消费者 | 86.1第3项：同一个非零相关实现、忠实同向交换局部腿、生成分离与重数、所有相关输入及每个参考；中央角不是物理张量因子 |
| 合法过程、typed CP与 Kraus | A8.3、14.2、25.1第4行以同一星代数和准确锥接原回溯、过程比较或整台递归参考消费者 | 86.1第4项：整台环境及所有输出的每个合法未来、每个所需深度与支持链；Kraus算子表示另需其有限全矩阵或适用正规表示条件 |
| 仪器、TP、条件更新与 Lüders | A7.3、8.4、14.2、25.1第5行：同一正夹心及星乘法作为仪器代数入口 | 86.1第5项：全输入输出接线、完整单位分区、真遗忘与接受条件；正质量才归一，Lüders需同一完整输出的像内射线校准 |
| 历史、全未来、记录与真实返回 | A8.4、14.2、25.1第6行在其合格域消费同一代数上的原合法复合和记录公式 | 86.1第6项：所有合法历史未来、环境泄漏、两侧和逆向真实返回、CountRead及真遗忘；无限记录的正常性／前对偶／可数可加另付 |
| 动力学、物理钟、能量与正 $\hbar$ | 84.7及 A6.3、14.2、25.1第7行供应同一静态代数和数学有界导子入口 | 86.1第7项：原钟、真实流、强连续实现、生成元域、能量解释及共同正作用量；数学酉元和指数参数不替代物理时间 |

这些条件消费者的数学结论已按原定理成立；仍须由实际来源满足其前件，不等于这些既有条件定理尚未证明。本组没有构造同一 $\Omega$ 上同时实现所有来源的 producer，也未把条件候选升级为无前提的宇宙本体结论。

## 87. 一个中央方向、一份正平方的完整中文图景

**定义 87.1（原关系怎样认回全部答案）。** 原问题仍从同一世界的两两有方向的正比较、相加三角、单位小窗和全部三标签正反配平出发。我们明确选择一个数学范围：所有原标签正好是某个有限 continuous von Neumann代数的全部自伴元素。这个范围可以有任意复杂的中心，也可以没有一份覆盖全体的忠实正规标量迹；给定的是中心值迹。它是一把数学汇总尺，不是一种已经取得的物理准备。

已有完整反射行先解决一件局部而实质的事。固定一枚正负两侧中心质量相等的反射，以及一份任意原输入，整份旧答案必须采用该反射对应的中央方向。背景可以有连续谱，不能拆成确切本征格；证明便用窄区间读取同一个固定旧答案。每次真实 PB的两张外表连接到这同一答案，P2的实际平方预算限制它在两个区间之间留下的偏移。区间数变多时，由中心值迹与全部中心态组成的分离有限迹族，让各块按平方和各自迹质量相加；总预算保留区间数的成本而仍随细分趋零，固定旧偏移因此消失。细化的是读取固定答案的尺子，没有假定越来越精细的输入会让未知响应连续变化。这条完整行直接取已有成果。

接着需要排除“每一枚反射各有自己的方向”。两枚反射只要在某个中央部分不交换，原反对称性就强迫它们在那里方向一致。在剩下恰好交换的中央部分，同时观察它们的四个联合角；中心平衡使每对相反角的中心质量相等，能够在同一个原代数里真正连起来。再把这份连线与其他中央部分上已有的配对轴拼成一枚完整反射，它同时接通所需方向。于是全部反射只能服从同一个中央对象 $Q$。没有把世界拆成许多因子后各自猜一个符号，也没有先假定未知响应能够按中央投影下降。

最后把一对实标签写成 $Z=x+iQy$。原答案自然给出一份正平方 $q_D(Z)=x^2+y^2+2D(x,y)$。第三标签 PB说，用已认清的反射共同重组这一对输入，平方保持不变。为了使重组成为精确左酉作用，可以重新选择另一份实际输入；那个二分之一只在输入里，绝不从未知答案中提出。

成熟的六反射定理给每个酉元一份精确有限分解。每枚反射又能在正、负两角内分别平分，变成两枚中心平衡反射，所以共用十二枚足够。各步带的共同中央相位恰好在十二步后消掉。这里不存在“酉变换可以逼近，所以未知答案也跟着逼近”的跳跃；每一步都是一份真正的原 PB。

任意 $Z$ 都有自己的正绝对值 $|Z|$。有限代数中的中心比较能把极分解缺少的角补齐为一份完整酉元，因此十二步能把整对原标签精确搬到 $(|Z|,0)$。第二标签为零时，P2已经确定响应为零，所以正代表的平方只能是 $|Z|^2$。沿途平方不变，出发处也只能是 $Z^*Z$。比较两式，所有原输入上的旧答案便只能为 $D(x,y)=iQ[x,y]/2$。一个中央方向和一份共同正平方，就把完整原域中的全部旧答案认回；线性、连续和中央下降随后成为结果。

当 $Q=1$ 的中央部分采用原结合乘法，当 $Q=-1$ 的部分采用相反乘法，两边保持相同的自伴对象、正锥和范数。在因子中只剩一个整体正负号，回到已有因子结论；带中心时保留的是实际中央投影，不是另加一套逐点可测选择。简化在于放宽模型限制、压缩共同运输的几何表达和运输长度，而非宣称没有前提。

同一个旧乘法一旦认回，已有后端给全部有限复 Gram、原换括号关系和忠实 Hilbert表示；在这个明确模型类中，不必再独立要求旧响应双线性或三标签复正性。物理量子候选仍完整保留七项原来源：实际相干准备，完整 Born菜单及全部零、不等和次归一质量，真正相关联合，整台过程与仪器及整个环境的全部输出，每个所需深度的递归同源参考，全部合法历史和每个合法未来、真遗忘及两侧和逆向真实返回，无限 CountRead的可数可加、正常性与指定前对偶，以及原物理钟、能量、生成元域和共同正作用量。数学结构严格认回一份旧响应；这些实际来源须在同一原世界同时满足，才进入相应完整量子消费者。一般 JB、不完备原域和 type III的问题保留各自边界，不能由这个完整有限 continuous模型代答。

## 追加锚（本行以下为增补区）

## 续卷导航

**约定（同主题接续）。** [谱混合续卷](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES_CONTINUATION.md)第88–114节完整保留双号刚性、对向多项式有限商、有限代数连续背景轴行及II₁因子精确32反射证明；第115节起接续中央混合行与同一原响应的中央拼接。框架轴及因子分类的共同结论已由本卷72.1、75.1、79.3覆盖，续卷保留其不同证明与来源。

## 追加锚（本行以下为增补区）
