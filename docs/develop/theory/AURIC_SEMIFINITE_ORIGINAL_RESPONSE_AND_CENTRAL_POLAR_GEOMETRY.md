# 半有限原始响应与中央极分解几何

> **恒定卷首与追加约定。** 本卷使用 `generic-v1`，是只增不减的参考输入。
> 卷首与各章合入后保持原字节；修订、勘误和增补写在文末追加锚之后，并保留新的追加锚。

## 1. 定位、状态与产地

**定位。** 本卷研究完整半有限 II∞ 因子原域上的同一原响应、有限支撑运输与极分解几何，并保留量子消费者所需的全部实际来源条件。

**证明状态。** 本卷是参考输入，不是数学真源；Lean 形式化才承载本库的数学真值。本卷给出纸面定义、定理与证明，未经 Lean kernel 验证，不声明形式化、冻结或消化状态。

**产地。** 数学内容的 skill 上下文为 `formal-thinking-and-answer`、`sshx`、`theory-volume-template`。内容由独立 codex-cli 作者形成，oracle 仅提供研究线索；纸面评审采用输入隔离的同 GPT6 族 CLI，未取得模型多样性。

**适用范围。** 分类使用下述完整 II∞ 模型及给定的 SM79.3 纸面前件。七项实际同源条件完整列于96.1；本卷不宣称已处理非因子、type III 或全物理 producer。

## 2. 记号与约定

**约定 2.1（卷间引用与编号）。** 本卷保留88–97的章节、条目及公式编号。SM79–87 指[前谱混合卷的固定来源](https://github.com/the-omega-institute/trureturing/blob/2359a7fbd1e23e1d59cf864c78f13bba3aabb54f/docs/develop/theory/AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md#79-完整有限-continuous-原域与中央取向候选)，其中 SM79.3 的完整有限 continuous 分类作为给定纸面前件。后续新章从98起在末尾追加锚之后增补。

**约定 2.2（完整模型与原关系）。** 模型为任意复 type $\mathrm{II}_\infty$ von Neumann 因子 $M$，配给忠实正规半有限迹 $\tau$；取 $E=M_{\rm sa}$、$C=M_+$、$u=1$、$N(a)=\|a\|$、$S(a,b)=(ab+ba)/2$。原评价族保留全部原索引与质量，分离 $E$ 并准确决定 $C$。全部原关系取88.1–88.2的完整 $\mathsf H_{\rm orig}$、反对称性、全部 P2 和完整 PB；不预付 $D$ 的线性、连续或其他正则性，也不将迹加入物理准备族。其余缩写与量词按88.1–88.2及各对应条目使用。

## 88. 完整半有限 II∞ 原域与唯一共同响应

**定义 88.1（固定来源与同一原资料）。** 本组的 SM 指[前谱混合卷](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md)，A 指[任意维静态卷](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)，C 指[中央续卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)，PT 指[原 PB 运输续卷](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md)，W 指[单位桥](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md)，R3 指[三标签刚性卷](AURIC_C128_THREE_LABEL_POSITIVITY_AND_ORIGINAL_RELATION_RIGIDITY.md)。SM79–87，尤其 SM79.3，专指[固定公开文本](https://github.com/the-omega-institute/trureturing/blob/2359a7fbd1e23e1d59cf864c78f13bba3aabb54f/docs/develop/theory/AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md#79-完整有限-continuous-原域与中央取向候选)的完整有限 continuous 单元；它是本组明确给定的纸面前件。其余仓内引用取[固定源](https://github.com/the-omega-institute/trureturing/tree/6aee3d786c0/docs/develop/theory)。本组不重新证明有限谱窗行、SM79.3或既有量子条件消费者。

保持唯一原 $\Omega/\mathrm{native}$ 及同一 $(E,C,u,N,\mathcal P,S,D)$。明确数学模型类 $\Gamma_{\mathrm{II}_\infty}$ 是任意复 type $\mathrm{II}_\infty$ von Neumann 因子 $M$，给定忠实正规半有限迹 $\tau:M_+\to[0,\infty]$，并取

$$
E=M_{\rm sa},\qquad C=M_+,\qquad u=1,\qquad
N(a)=\|a\|,\qquad S(a,b)=a\circ b=\frac{ab+ba}{2}.
\tag{88.1}
$$

不要求 Hilbert 空间或预对偶可分，不要求 $M$ 可数可分解或存在忠实正规状态。结合乘法、伴随、极分解、Borel 函数演算及所给迹是模型结构，不是从一般 JB 原域重新推出的结论。$\mathcal P$ 是全部原索引的正实线性评价族，分离 $E$ 并准确决定 $C$：

$$
a\in C\ \Longleftrightarrow\ (\forall\gamma\in\mathcal P)\ \gamma(a)\ge0,
\qquad m_\gamma=\gamma(1)\ge0.
\tag{88.2}
$$

原索引、相同限制但不同来源的评价、全部零、不等和次归一质量均保留；不把 $\tau$ 加入物理准备族或用它替换原评价。数学正泛函不是实际准备。

**定义 88.2（完整原关系的全部数学量词）。** 记 $\mathsf H_{\rm orig}$ 为同一原资料的完整 A1–A3，连同上述准确锥和原范数。对每个原 $\gamma$ 及全部原标签，定义原表项

$$
g_\gamma(a,b)=\gamma(a\circ b)-i\gamma D(a,b).
$$

A1 要求全部有向二表 $G_\gamma(a,b)=(g_\gamma(c_j,c_k))_{j,k=1}^2$ 正半定，其中 $(c_1,c_2)=(a,b)$，并保留反向次序、零、重复、任意实缩放和平移标签。原 $D:E^2\to E$ 为同一个总映射且反对称，故 $D(a,a)=0$。A2 要求对全部 $a,b\in E$，$(c_1,c_2,c_3)=(a+b,a,b)$ 及其每个相应排列的原三表，其实部在整个 $\mathbb R^3$ 上半正定，指定相加向量 $(1,-1,-1)$ 及排列后的相应向量有零二次值。A3 要求 $S(1,1)=1$，并存在同一个固定有理 $0<\theta\le1$，使全部原 $0\le y\le\theta1$ 满足 $S(y,y)\le y$。这里量化的全部实缩放、实平移、相加及后述嵌套输入本来都是完整原 $E$ 的成员，未假设 $D$ 保持这些输入运算。

特别，完整原 P2 是对每个 $\gamma\in\mathcal P$ 和全部 $a,b\in E$ 的

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(a\circ b)+i\gamma D(a,b)&\gamma(b^2)
\end{pmatrix}\succeq0.
\tag{88.3}
$$

完整 PB 对全部实际原三元组 $a,b,d\in E$ 要求

$$
\begin{gathered}
v=D(a,b)-a\circ d,\qquad w=a\circ b+D(a,d),\\
D(b+v,d+w)-D(b-v,d-w)=-2b\circ v-2d\circ w.
\end{gathered}
\tag{88.4}
$$

这与每个原评价所读的正反平方配平相同，因为评价分离元素。不得只保留重复、零第三槽、线性第三槽或某个框架内的子族。不预付 $D$ 的线性、连续、可测、齐次、单位平移中性、压缩下降、共同导子、局部实现或物理来源。“实际原标签”在以下数学证明中只指同一原 $E$ 的元素；其可取得、可控制和可制备身份仍须96.1。

准确锥将88.3的同一元素二次型读给每个数学正实线性泛函 $\phi:E\to\mathbb R$，正如 SM79.2、PT118.2 所用的读取机制：固定复系数后，原评价全部读非负使该元素为正，再由 $\phi$ 读取。因此

$$
|\phi D(a,b)|^2\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2
\qquad(\phi\ge0;\ a,b\in E).
\tag{88.5}
$$

这不假设原评价正规，也不增加物理评价。特别 $D(a,0)=D(0,a)=0$；后文选用的正规正泛函只是其中一族数学读取。

**定理 88.3（完整 II∞ 原响应的正反分类）。** 以 SM79.3 为给定纸面前件。在88.1的同一模型和全部原评价上，下列两项等价：

1. 同一原总 $D$ 满足88.2的全部 $\mathsf H_{\rm orig}$、反对称性、全部 P2 和完整 PB。
2. 存在唯一整体符号 $\sigma\in\{1,-1\}$，使

   $$
   \boxed{D(a,b)=\frac{\sigma i}{2}[a,b]\qquad(\forall a,b\in M_{\rm sa}).}
   \tag{88.6}
   $$

反向保持原 $E,C,u,N,S,\mathcal P$ 和每份原质量。正向不以混合行、有限支撑运输或任何 $D$ 正则性为附加前件；这些均在89–92生产。识别后同一个原乘法 $a\star b=a\circ b-iD(a,b)$ 正好是给定乘法或其相反乘法。证明的有限分类部分仅消费 SM79.3 的因子特化，实际物理来源的条件接回在94、96–97。

## 89. 有限角资格、有限支撑及共同符号

**定义 89.1（迹有限支撑与投影供应）。** 令

$$
\mathcal F_\tau=\{p\in M:p=p^*=p^2,\ \tau(p)<\infty\},
\quad
\mathcal I_{\rm fs,sa}=\bigcup_{p\in\mathcal F_\tau}(pMp)_{\rm sa}.
\tag{89.1}
$$

“有限支撑”专指这个集合，不指有限维或有限秩，也不把它当作完整原域。以下只调用成熟投影工具的这些准确形式：任意因子中任意两个投影 Murray–von Neumann 可比较；有限因子中，忠实归一迹相等的投影等价；任意 von Neumann 代数中

$$
(p\vee q)-p\sim q-(p\wedge q).
\tag{89.2}
$$

据89.2，$\mathcal F_\tau$ 对有限并有向，$\tau(p\vee q)\le\tau(p)+\tau(q)$。其上确界为1：若上确界的补 $r\ne0$，忠实半有限性给 $0\ne a\le r$ 且 $\tau(a)<\infty$；某个非零谱投影 $e=1_{[\varepsilon,\infty)}(a)\le r$ 满足 $\tau(e)\le\tau(a)/\varepsilon<\infty$，矛盾。因此所有迹有限投影按包含排序构成 $e\uparrow1$ 的强收敛网。不将网换成序列。每个非零迹有限角 $pMp$ 是 II₁ 因子，其忠实正规归一迹为 $\tau_p=\tau|_{pMp}/\tau(p)$。原 $M$ 的无限迹不用于两个无穷值之间的相减。

**复用 89.2（同角闭合和完整关系的角限制）。** A50.2、A51.1给：对每个原投影 $p$，同角输入满足

$$
a,b\in(pMp)_{\rm sa}\quad\Longrightarrow\quad D(a,b)\in(pMp)_{\rm sa}.
\tag{89.3}
$$

其参数在此为 $X=E=M_{\rm sa}$、$U_p(x)=pxp$，故原角正好是整个 $(pMp)_{\rm sa}$，不是一个待完成子域。这一 P2 支撑机制和完整 A1–A3/PB 的角继承是既有结果，不再作为新增桥或新增 JB 保正性成果。

明确核对本次消费的所有量词。限制评价仍按每个原 $\gamma$ 索引，$\gamma_p=\gamma|_{(pMp)_{\rm sa}}$；它们分离角、准确决定角锥，且局部辅助质量是 $m_{\gamma,p}=\gamma(p)$，不改全域质量 $m_\gamma=\gamma(1)$，不合并评价或删零限制。角内全部零、重复、实缩放、以 $p$ 平移、相加三表及排列原样继承。$p\circ p=p$；若 $0\le y\le\theta p$，则 $0\le y\le\theta1$，同一小效果不等式成立。89.3使角内每次 PB 的两个内值、位移、四个外层输入和两个外值均仍在角内，所以完整88.4逐层继承。角上任意数学正泛函 $\psi$ 还有正延拓 $x\mapsto\psi(pxp)$，因而88.5也对角上全部数学正读取成立。所有角内辅助标签都已属于原 $E$。

这些是辅助数学限制资料；不声明在每个角另有物理 $\Omega$、native、准备或菜单。SM79.3的数学分类与其86的实际来源消费者分开使用，不以虚构角系统支付实际来源。

**命题 89.3（SM79.3的准确因子实例与唯一拼接）。** 对每个非零 $p\in\mathcal F_\tau$，向 SM79.1–79.3代入

$$
(M,E,u,C,N,S,D,\mathcal P,T)
=(pMp,(pMp)_{\rm sa},p,(pMp)_+,\|\cdot\|,\circ,D_p,
\{\gamma_p\}_{\gamma\in\mathcal P},\tau_p(\cdot)p).
\tag{89.4}
$$

89.2支付完整原关系，89.1支付有限 continuous 环境和忠实正规中心值迹。因此 SM79.3的中央自伴对合恰为 $Q_p=\sigma_pp$，$\sigma_p\in\{1,-1\}$，并有

$$
D(a,b)=\frac{\sigma_pi}{2}[a,b]\qquad(a,b\in(pMp)_{\rm sa}).
\tag{89.5}
$$

若 $0\ne p\le g\in\mathcal F_\tau$，II₁ 因子 $pMp$ 非交换，故有不交换自伴 $a,b\in pMp$。在同一个旧 $D(a,b)$ 上比较89.5，给 $\sigma_p=\sigma_g$。任意两个非零迹有限投影有共同迹有限上界 $p\vee q$，所以全部符号相同，记为 $\sigma$。存在非零迹有限投影由半有限性保证；上述不交换对也证明这个共同符号唯一。零角只含零值，无须给它另选符号。

此后固定

$$
J=\sigma i1,\qquad K(a,b)=\frac J2[a,b].
\tag{89.6}
$$

$J,K$ 仅是辅助数学记号，与96.1的 native 全词 $J_a,K$ 区分。至此只知道全部有限角内的旧值，并没有得到任意输入的压缩相容律。

**引理 89.4（一个有限支撑输入的实际输出）。** 若 $h=php\in\mathcal I_{\rm fs,sa}$、$x\in E$ 任意，则 $D(h,x)$、$h\circ x$ 和 $K(h,x)$ 都有某个迹有限支撑，但不必支撑于同一个原 $p$。

证明。置 $q=1-p$、$r=D(h,x)=r^*$。对每个支撑在 $q$ 的数学正泛函，88.5的 $h^2$ 预算为零，故读取 $r$ 为零；这些泛函分离 $qMq$ 的自伴部，因此 $qrq=0$。取 $qrp$ 的左支撑 $s\le q$，极分解使 $s\precsim p$，所以 $\tau(s)\le\tau(p)$。自伴性及这个左支撑给

$$
r=(p+s)r(p+s),\qquad \tau(p+s)\le2\tau(p)<\infty.
\tag{89.7}
$$

$h\circ x$、$K(h,x)$ 也自伴且 $q(\cdot)q=0$；对它们各作相同块支撑论证即可。有限多个此类支撑可取迹有限并。证明没有展开 $D$，也没有声称 $pD(a,b)p=D(pap,pbp)$。∎

## 90. 同一次三标签 PB 生产全部有限支撑混合行

**引理 90.1（有限投影的完整全域行）。** 对每个 $p\in\mathcal F_\tau$ 和每个 $x\in E$，有 $D(p,x)=K(p,x)$。

证明。$p=0$ 用88.5。其余情形固定同一旧值 $r=D(p,x)$，并置 $k=p\circ x$。89.4使 $p,r,k$ 有共同迹有限支撑。在真正原三元组 $\operatorname{PB}(x,p,0)$ 中，$v=-r,w=k$，所以

$$
D(p-r,k)-D(p+r,-k)=2p\circ r.
\tag{90.1}
$$

四个实际外层输入都属于同一个完整有限角；89.5用同一个 $\sigma$ 读它们，故

$$
\begin{aligned}
D(p-r,k)-D(p+r,-k)
&=\frac J2\bigl([p-r,k]+[p+r,k]\bigr)\\
&=J[p,k]=\frac J2[p,x].
\end{aligned}
\tag{90.2}
$$

于是 $pr+rp=J[p,x]/2$。已知 $K(p,x)$ 也满足 $pK+Kp=J[p,x]/2$。令 $t=r-K(p,x)$，则 $pt+tp=0$；其 $p,p$ 块和两个交叉块均为零。89.4的零补角块又给 $(1-p)t(1-p)=0$，所以 $t=0$。展开的只有已知 $K$，没有对未知 $D$ 使用奇性或可加性。∎

**定理 90.2（有限支撑首标签对全部原输入的整行）。** 对全部 $h\in\mathcal I_{\rm fs,sa}$ 和全部 $x\in E$，有

$$
\boxed{D(h,x)=K(h,x).}
\tag{90.3}
$$

证明。固定 $r=D(h,x)$、$t=r-K(h,x)$。89.4使 $r,t$ 均有迹有限支撑。对任意迹有限投影 $d$，在同一原 $\operatorname{PB}(x,h,d)$ 中有

$$
v=-r-x\circ d,\qquad w=x\circ h+D(x,d).
$$

90.1及反对称性已给 $D(x,d)=K(x,d)$。令 $v_0,w_0$ 为把这两份内响应都改用已知 $K$ 算出的位移，则

$$
v=v_0-t,\qquad w=w_0.
\tag{90.4}
$$

89.4保证 $h,d,v,w,v_0,w_0,t$ 全部落在某个共同迹有限角；允许这个角依赖当前固定的 $h,x,d$。因此两份原外响应准确等于 $K$ 的值。

先说明此处消费的已知 PB：对任意自伴 $a,b,d$，令 $Z=b+Jd$，以 $K$ 取位移 $v_0,w_0$，则

$$
v_0+Jw_0=JaZ,\qquad
\bigl((1\pm Ja)Z\bigr)^*\bigl((1\pm Ja)Z\bigr)=Z^*(1+a^2)Z.
\tag{90.5}
$$

已知平方的坐标展开就是 $K$ 的完整 PB。这是 SM 的式(84.4)–(84.5)所用结合乘法身份，在此不需要有限性或 $D$ 的任何性质。

将本次原 PB 与 $K$ 对同一 $x,h,d$ 的 PB 相减。已知双线性给外层差的差为 $-2K(t,d)=-J[t,d]$，右端差为 $2h\circ t=ht+th$，故

$$
\boxed{-J[t,d]=ht+th\qquad(d\in\mathcal F_\tau).}
\tag{90.6}
$$

取 $d=0$ 得 $ht+th=0$，再得 $[t,d]=0$ 对全部迹有限投影成立。选迹有限 $e$ 支撑 $t$。$1-e\ne0$，半有限性给非零迹有限 $f\le1-e$；置 $g=e+f$。对 $gMg$ 内每个投影 $d$，有 $d\in\mathcal F_\tau$，故 $t$ 与之交换。自伴元素的谱投影属于 $gMg$，所以 $t\in Z(gMg)=\mathbb Cg$。但 $t=ete$，且 $g-e=f\ne0$，该标量只能为零。于是90.3成立。∎

90.1和90.6是实际跨角共同关系：任意全域 $x$ 留在同一次 PB 的第一标签，未知的同一个原输出进入外层；那些实际外层共同落回已分类的有限角。第三投影遍历所有迹有限投影，排除同一有限支撑残差；没有分别选择两份局部实现或把两个已知纯输入行相加。

## 91. 同一个旧缺陷的精确有限支撑酉运输

**定义 91.1（原输入对的坐标）。** 对每个 $Z\in M$，唯一写成

$$
Z=b+Jd,\qquad b=\frac{Z+Z^*}{2},\qquad
 d=-\frac J2(Z-Z^*)\in E,
\quad \mathfrak F(Z)=D(b,d)-K(b,d)\in E.
\tag{91.1}
$$

这是同一原标签对的双射重索引，不是 $D$ 的复线性延拓，不赋予 $\mathfrak F$ 连续、齐次或可加性质。

**引理 91.2（一次实际 Cayley 运输）。** 若 $a\in\mathcal I_{\rm fs,sa}$，则对全部 $Z\in M$，

$$
\mathfrak F(C_aZ)=\mathfrak F(Z),\qquad
 C_a=(1+Ja)(1-Ja)^{-1}.
\tag{91.2}
$$

证明。90.3同时识别 $\operatorname{PB}(a,b,d)$ 的两个实际内值。故其位移满足 $v+Jw=JaZ$，两份外层标签对正好是 $(1\pm Ja)Z$ 的91.1坐标。原 PB 与90.5的已知 PB 有相同位移和右端，相减给

$$
\mathfrak F((1+Ja)Z)=\mathfrak F((1-Ja)Z).
\tag{91.3}
$$

$a$ 自伴使 $1-Ja$ 可逆。对任意目标 $W$，重新选取真正原输入 $Z_0=(1-Ja)^{-1}W$ 的两个自伴坐标；完整原域保证它们合法。把91.3用于 $Z_0$ 即得91.2。没有把输入中的逆元、标量或和从未知函数中提出。∎

**推论 91.3（所有有限支撑酉元的精确作用）。** 令

$$
\mathcal U_{\rm fs}=\{(1-p)+u:p\in\mathcal F_\tau, u\in\mathcal U(pMp)\}.
$$

对全部 $U\in\mathcal U_{\rm fs}$ 和全部 $Z\in M$，有

$$
\boxed{\mathfrak F(UZ)=\mathfrak F(Z).}
\tag{91.4}
$$

证明。若 $U=(1-p)+u$，在 $pMp$ 中用有界 Borel 辐角取自伴 $H=pHp$，$\|H\|\le\pi$，使 $U=e^{JH}$。取 $a=\tan(H/4)$，在补角取零。它有迹有限支撑，且 $C_a=e^{JH/2}$，所以 $U=C_a^2$。有限两次91.2给91.4。包括 $u$ 有 $-1$ 谱及 $p=0$ 的情形；$\tan$ 只在 $[-\pi/4,\pi/4]$ 使用，因而有界。这是原代数内的精确两步作用，不使用酉群稠密性或未知响应的极限。∎

**引理 91.4（不预付奇性的方向交换）。** 置 $\mathcal T(Z)=JZ^*$。若 $Z=b+Jd$，则 $\mathcal T(Z)=d+Jb$，所以仅由原反对称性，

$$
\boxed{\mathfrak F(\mathcal T(Z))=-\mathfrak F(Z).}
\tag{91.5}
$$

此式不借用 $\mathfrak F(Z^*)=-\mathfrak F(Z)$ 或 $\mathfrak F(JZ)=\mathfrak F(Z)$；91.4只需要实际有限支撑酉元，而标量 $J1$ 通常不在该族。

## 92. 无限极分解的正确方向及固定预算排零

**引理 92.1（因子比较给两个方向之一的等距扩充）。** 对每个 $Z\in M$，在 $Y=Z$ 与 $Y=\mathcal T(Z)$ 中，至少一个具有表示

$$
Y=wA,\qquad A=|Y|\ge0,\qquad w^*w=1.
\tag{92.1}
$$

证明。取 $Z=v|Z|$，$p=v^*v$、$q=vv^*$。因子比较给 $1-p\precsim1-q$ 或 $1-q\precsim1-p$。第一分支取部分等距 $s$，$s^*s=1-p$、$ss^*\le1-q$。两对初末支撑正交，故 $w=v+s$ 为等距，$w|Z|=Z$。第二分支对 $\mathcal T(Z)=JZ^*$ 使用相同构造，其极部分等距为 $Jv^*$，初末投影为 $q,p$。$Z=0$ 可直接取 $w=1,A=0$。比较不需要迹有限、可分或 $\sigma$-finite。∎

这是必要的方向检查：若 $Z$ 是真余等距，$ZZ^*=1$ 而 $Z^*Z=p<1$，就不可能有酉网 $U_\alpha$ 使 $U_\alpha Z\to|Z|$ 强*收敛；否则 $1=U_\alpha ZZ^*U_\alpha^*\to|Z|^2=p$。这只是错误方向的端点障碍，不是88.3的反例。91.5允许选用正确方向，而不要求每个极部分等距都补成酉元。

**引理 92.2（实际有限角内的酉扩充）。** 若92.1成立，则存在 $U_e\in\mathcal U_{\rm fs}$，按全部 $e\in\mathcal F_\tau$ 排序，使

$$
U_e e=we,\qquad U_e\longrightarrow w\text{ 强收敛},\qquad
U_e^*Y\longrightarrow A\text{ 强*收敛}.
\tag{92.2}
$$

证明。取 $f_e=e\vee wew^*$。迹性和89.2给 $\tau(f_e)\le2\tau(e)<\infty$。部分等距 $we$ 的初末投影为 $e,wew^*$，在有限因子 $f_eMf_e$ 内二者等迹，两个补投影 $f_e-e,f_e-wew^*$ 也等迹。有限角内的忠实归一迹比较给部分等距 $s_e$，

$$
s_e^*s_e=f_e-e,\qquad s_es_e^*=f_e-wew^*.
$$

于是 $u_e=we+s_e$ 是这个角内的酉元，$U_e=u_e+(1-f_e)$ 是原 $M$ 内的有限支撑酉元。零角时取 $U_0=1$。对每个表示向量 $\xi$，

$$
\|(U_e-w)\xi\|\le2\|(1-e)\xi\|\longrightarrow0.
\tag{92.3}
$$

再置 $\delta_e=U_e^*w-1$，则 $\|\delta_e\|\le2$、$\delta_e e=\delta_e^*e=0$，且

$$
\|(U_e^*w-1)\xi\|=\|(w-U_e)\xi\|,
\quad
\|(w^*U_e-1)\xi\|\le\|(U_e-w)\xi\|.
$$

故 $U_e^*w\to1$ 强*收敛，乘固定有界 $A$ 得92.2。没有声称 $U_e^*\to w^*$ 强收敛；也没有把原 $M$ 换成其矩阵放大。∎

**定理 92.3（同一固定缺陷的正平方预算）。** 88.3的正向结论成立于全部原输入。

证明。任取 $Z\in M$，按92.1选 $Y=Z$ 或 $\mathcal T(Z)$，并按92.2取有限支撑酉网。写

$$
W_e=U_e^*Y=x_e+Jy_e,\qquad x_e,y_e\in E.
$$

91.4对每个 $e$ 给同一元素的精确等式

$$
\mathfrak F(W_e)=\mathfrak F(Y).
\tag{92.4}
$$

又有 $\|x_e\|,\|y_e\|\le\|Y\|$，$x_e\to A$、$y_e\to0$ 强收敛。为明确正常读数极限只作用于已知预算，给出直接序界。由 $\delta_e e=\delta_e^*e=0$，

$$
\delta_e^*\delta_e\le4(1-e),\qquad
\delta_e\delta_e^*\le4(1-e).
$$

令 $B_e=W_e-A=\delta_e A$；因 $A$ 自伴，$y_e=-J(B_e-B_e^*)/2$。已知算子不等式给

$$
\begin{aligned}
y_e^2&\le\tfrac12(B_e^*B_e+B_eB_e^*),\\
B_e^*B_e&\le4A(1-e)A,\qquad
B_eB_e^*\le4\|A\|^2(1-e).
\end{aligned}
\tag{92.5}
$$

因此对每个数学正规正泛函 $\phi\in M_*^+$，

$$
\phi(y_e^2)\le2\phi(A(1-e)A)+2\|A\|^2\phi(1-e)\longrightarrow0.
\tag{92.6}
$$

最后一步只用 $e\uparrow1$、$AeA\uparrow A^2$ 和 $\phi$ 正规；没有要求原评价族正规或以序列穷尽投影。

原88.5及已知 C* 正泛函 Cauchy–Schwarz分别给

$$
|\phi D(x_e,y_e)|\le\sqrt{\phi(x_e^2)\phi(y_e^2)},\qquad
|\phi K(x_e,y_e)|\le\sqrt{\phi(x_e^2)\phi(y_e^2)}.
\tag{92.7}
$$

第二式来自 $|\phi(x_ey_e)|,|\phi(y_ex_e)|\le\sqrt{\phi(x_e^2)\phi(y_e^2)}$，只估计已知交换子。于是

$$
\begin{aligned}
|\phi\mathfrak F(Y)|
&=|\phi\mathfrak F(W_e)|\\
&\le2\sqrt{\phi(x_e^2)\phi(y_e^2)}\\
&\le2\|Y\|\sqrt{\phi(1)\phi(y_e^2)}\longrightarrow0.
\end{aligned}
\tag{92.8}
$$

左端从始至终为同一个固定旧缺陷的读数，故等于零。正规正泛函分离 $M_{\rm sa}$，所以 $\mathfrak F(Y)=0$。若 $Y=\mathcal T(Z)$，再用91.5得 $\mathfrak F(Z)=0$；另一分支直接得到。$Z$ 任意，91.1遂给全部 $a,b\in E$ 上的88.6。

$\phi(1)=0$ 时正泛函恒零，上式仍成立且无除法。任何非零固定读数都会在某个足够大的实际有限投影处，已与92.8的有限 PB 运输及 P2 预算矛盾。这里没有 $D(x_e,y_e)\to D(A,0)$ 的断言。∎

## 93. 反向、同一旧乘法与合法迹配对

**命题 93.1（正反取向的完整反向）。** 在88.1的相同原资料上，任给 $\sigma\in\{1,-1\}$，按88.6取 $D=K$，则88.2的全部数学关系成立。

证明。令 $M_\sigma=M$ 或 $M^{\rm op}$，对应 $\sigma=1$ 或 $-1$。它们有相同自伴部、锥、单位、范数和原正评价，且对自伴标签 $a\star b=a\circ b-iK(a,b)$。原评价的正复延拓与 Cauchy–Schwarz给全部原 P2及有向二表；实部是同一实 Gram 型，故全部相加三表及其排列正性与指定零方向成立。函数演算给全部小效果的 $y^2\le y$，且 $1^2=1$。90.5已在整个结合代数内证明 $K$ 的完整 PB，对每个原三元组均成立。这正是 SM84.1中不使用有限性的反向代数计算之消费，不重做有限分类。每份原评价及质量始终未变；零质量处无归一。结合89.3的唯一性，完成88.3。∎

**推论 93.2（识别之后的同一对象后果）。** 原 $D$ 此时才取得实双线性、分别范数及超弱连续、单位平移中性和共同有界内导子实现：

$$
L_a(X)=[\sigma ia/2,X],\qquad L_a(b)=D(a,b),
\qquad \|D(a,b)\|\le\|a\|\|b\|.
\tag{93.1}
$$

全部原 $a,b,c$ 满足同一个原 R：

$$
(a\circ b)\circ c-D(D(a,b),c)
=a\circ(b\circ c)-D(a,D(b,c)).
\tag{93.2}
$$

其完整有限旧复 Gram、$\mathsf P_3$、R及忠实静态表示准确接 A32.2、A23.1、A6.3、A7.1–7.3、A8.1；参数始终为原 $S,D,\mathcal P,C,u,N$。亦可直接读同一个 $M_\sigma$ 的正平方。对每个有限 $n$、全部原 $a_1,\ldots,a_n$、全部 $z_1,\ldots,z_n\in\mathbb C$ 和每份原 $\gamma$，有

$$
\sum_{j,k=1}^n\overline z_jz_k
[\gamma(a_j\circ a_k)-i\gamma D(a_j,a_k)]\ge0.
\tag{93.3}
$$

全部质量保留，包括 $n=0$、零标签和重复标签。这里没有宣称任意压缩成为原响应的同态：即使已识别 $D$，一般仍不能写 $pD(a,b)p=D(pap,pbp)$；跨越补角的交换子项会使这两式不同。

迹偏斜性限定于合法可积域。令

$$
\mathfrak m_\tau=\{c\in M:\tau(|c|)<\infty\}=M\cap L^1(M,\tau).
$$

对全部 $a,b\in M_{\rm sa}$ 和 $c\in\mathfrak m_\tau\cap M_{\rm sa}$，两侧乘积均在 $\mathfrak m_\tau$，并由93.1及迹循环性得

$$
\tau(D(a,b)c)=-\tau(bD(a,c)).
\tag{93.4}
$$

这包括所有有限支撑自伴 $c$，不要求 $a,b$ 可积。一般三个有界自伴元不保证这些乘积可积，不在93.4量词内；不对 $\infty-\infty$ 作运算。93.4是识别后的后果，不是证明旧响应线性的前件。

## 94. 完整条件量子候选及同域等价

**定义 94.1（同一个原世界的候选）。** 在模型类 $\Gamma_{\mathrm{II}_\infty}$ 内，完整条件候选为

$$
\Gamma_{\mathrm{II}_\infty}
+\mathsf H_{\rm orig}+\mathsf{PB}+\mathcal C_{\rm src},
\tag{94.1}
$$

其中 $\mathsf H_{\rm orig},\mathsf{PB}$ 逐字取88.2的全部量词，$\mathcal C_{\rm src}$ 是96.1的七项全文及所纳入全部上游量词的合取。特别不以另加90.3或91.4替换原关系，不把全部数学正读取当作物理准备。以给定 SM79.3为纸面前件，88.3、93.2使同域有

$$
\begin{aligned}
&\Gamma_{\mathrm{II}_\infty}+\mathsf H_{\rm orig}+\mathsf{PB}
+\mathcal C_{\rm src}\\
&\quad\Longleftrightarrow\quad
\Gamma_{\mathrm{II}_\infty}+\mathsf H_{\rm orig}+\mathsf P_3+\mathsf{PB}
+\mathcal C_{\rm src}.
\end{aligned}
\tag{94.2}
$$

因此在这一个明确模型类中，旧 $D$ 双线性、完整有限复 Gram、P3、R和同一个旧结合乘法都不必作为额外独立数学要求；这不是一般 JB 的公理削减，也没有计算原起源任务的最小独立信息量或实际取得成本。

**命题 94.2（条件消费者的准确接回）。** 若同一原世界确实满足94.1中相应全部实际来源条件，A8.2–8.5、A14.2、A25.1、R3 8.2–8.5及其所引消费者，在各自原适用域、原对象和全部原量词下成立。

证明。88.6、93.1–93.3供应这些既有条件定理所需的同一原静态代数 $M_\sigma$、锥、范数、单位、评价和全部质量。各项实际前件仍严格由96.1逐项提供；将同一静态入口代入即可，不重新证明条件桥。张量只消费有共同实现的合法局部腿；CP只消费原合格过程比较或整台实际递归参考；更新、记录与动力各守其原域。由此不能反向推出这些实际来源存在。∎

## 95. 成熟来源、综合增量与适用边界

**定义 95.1（准确来源及其条件）。** 本组采用以下可定位的纸面接口，不把定理名称或模型回复的成立判断当作证明。

| 来源 | 准确条件、消费与边界 |
| --- | --- |
| 固定公开 SM79.3及其79.1–84.1 | 完整有限 continuous 原域、全部原关系及给定忠实正规中心值迹；仅按89.4消费非零有限角的因子特化。有限谱窗行、中央取向和有限全域分类均为给定纸面前件，不在本组重新认领；不使用另一版本的同号74.1替代。 |
| 固定源 A50.2、A51.1及其来源 W108.2–108.3固定稿 | P2 已给同角旧输出支撑，完整原 A1–A3和PB逐层限制；89.2只作准确参数匹配。这也不新增一般 JB 二次表示保正的证明。 |
| Claire Anantharaman、Sorin Popa，[*An introduction to II₁ factors*，作者全文](https://www.math.ucla.edu/~popa/Books/IIunV15.pdf)，§2.4，Theorem 2.4.1、Proposition 2.4.5、Theorem 2.4.8、Corollaries 2.4.9、2.4.11 | 该节从任意 Hilbert 空间上的 von Neumann 代数开始，用网和任意索引的正交族。2.4.9是任意因子投影比较；2.4.11额外要求忠实有限 tracial state，故只在 $f_eMf_e$ 等有限角上使用。2.4.5给89.2，2.4.1给有界单调网的强收敛。不能以两边无限迹相等替代等价。 |
| Shavkat Ayupov、Farkhad Arzikulov，[*2-local derivations on semi-finite von Neumann algebras*，原文](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0017089512000870)，Glasgow Math. J. 56，9–12，DOI 10.1017/S0017089512000870，§§2–3 | §3明确使用忠实正规半有限迹、$\mathfrak m_\tau$ 双侧理想、可积乘积的迹循环律及迹有限投影趋向1的网；这些成熟半有限工具对应89.1、93.4。其主定理还要求每对输入由同一个导子同时实现，即2-local前件，本组并未取得或使用该前件来证明88.6。不能把 P2 的两个标量预算当作共同导子实现。 |
| Bhat–Nayak–Shankar，[*On products of symmetries in von Neumann algebras*，arXiv:2204.00009v1](https://arxiv.org/pdf/2204.00009v1)，Theorem 3.9 | 原文给 type II₁ von Neumann 代数内六个 symmetry 的精确乘积。它已由给定 SM79–84在有限分类内消费；本组不将它当作 II∞ 的全域反射行或另写一套全酉运输，91只用有限支撑 Borel 对数。 |
| 固定源 A32.2、A23.1、A6.3、A7、A8、A14.2、A25.1，SM86.1及96.1所列原来源 | 93–94只在识别同一个旧 $D$ 后接回全有限复 Gram、R、表示及七项既有条件消费者。表示、CP、张量、仪器和动力的实际原条件一项也不由成熟工具的名字代付。 |

本组的 $\texttt{repo-derived}$ 综合增量是90.1与90.6把任意全域首标签、同一个实际有限支撑输出和第三有限投影接到一个有限角中，生产完整90.3；随后91的精确有限支撑作用与92的方向选择、实际有限角酉扩充及同一固定缺陷预算共同完成全域识别。一般 P2 支撑闭合、有限分类、投影比较、半有限迹、极分解、Borel 对数、C* Cauchy–Schwarz和既有条件桥均为复用工具，不各立新成果。不声称历史原创、文献穷尽或外部开放问题结算。

**定义 95.2（边界）。** 定理处理任意给定忠实正规半有限迹的完整 II∞ 因子；有限性仅在辅助角及其比较中使用，原 $M$ 的全局有限性已经删除。有限角的符号、全部有限支撑混合行及全部原输入的传播都由同一个旧总映射支付，没有留下待假设的运输接口。给定 SM79.3仍是承重纸面前件，本组不宣称为它提供独立审查或 kernel 认证。

这里没有一般 JB、type III、半有限非因子、适当或不完备原域的分类，也没有把 II∞ 模型类本身从裸 $\Omega$ 生产出来。完整原域用于全部谱投影、有限支撑标签和91.3的重基输入合法；因子性用于角内标量取向拼接、90.6的中心排零及92.1的二选一；半有限性用于有限支撑和有向穷尽。原评价不必正规，正规性只用于辅助数学读取92.6。物理正常性、原指定前对偶、无限记录和 CountRead继续由96.1承担。全文为纸面定义、定理与证明，不宣称 Lean、kernel、冻结或独立评审结论。

## 96. 七项真实同源物理合同的完整保留

**定义 96.1（七项全文及全部上游量词）。** $\mathcal C_{\rm src}$ 逐项全文合取固定 SM86.1、SM78.2、SM43.2、49.1、61.1、69.1，C199.2、194.2、186.1–186.7、181.3、171.1–171.7、160.3、155.1、145.1–145.7，PT122.1，A8.3–8.4、14.2、25.1、53.1，R3 8.1–8.5、80.1，W95.2、116.1，以及它们各项纳入的全部上游来源、对象、条件、实现和量词。下列全文展开这些同源义务；引用的原来源全文仍为合取项，不被七行消费者表或本组 II∞ 模型限制替换。所有“每个”“全部”“任意有限长度／深度”“每个正精度”均沿原适用域量化；未定义的请求保持未定义，不扩大原合同的合法域。唯一原世界、中心、经典、不等维块和静默部分保持原身份，数学因子选择不删除完整起源任务的其他原分支。

1. **复 Hilbert、可观测量与实际相干叠加。** 同一原 $\Omega$、原 $E/S/D$、跨评价指定配对、具名且可取得的原标签、native、全部原词同一 $q,K,J$、准备父位置 parent、ready 类型、合法控制及实际相干准备，完整保持 C171.1及其 A8.3–8.4、14.2、25.1、R3 8.1–8.5、80.1和原多项式卷87.1的条件。根、静默和零活动分支、所有具名原程序及各自词身份一份不少。

   在原消费者要求共同全词网络的接口处，沿 R3 8.1保留同一复空间 $V$、第一槽共轭线性的半正定 Hermitian 型 $K$、全部原 $\xi_\gamma$ 和总集合映射 $J_a:V\to V$。对全部原 $a,b$、全部原 $\gamma$、全部 $z,w\in V$，要求

   $$
   \begin{aligned}
   K(\xi_\gamma,J_a\xi_\gamma)&=\gamma(a),\\
   K(J_a z,J_b w)&=K(z,J_{a\circ b}w)-iK(z,J_{D(a,b)}w),\\
   V&=\operatorname{span}_{\mathbb C}
   \{J_{a_1}\cdots J_{a_n}\xi_\gamma:n\ge0,\ a_j\in E,\ \gamma\in\mathcal P\},\\
   K(\xi_\gamma,\xi_\gamma)&\le m_\gamma,\\
   K(J_a\xi_\gamma,J_c(J_a\xi_\gamma))&\ge0\qquad(c\in C).
   \end{aligned}
   \tag{96.1}
   $$

   原词先按原总映射实际复合，再取有限复线性包；包括零长度和任意有限长度。共同 $K$ 保留指定跨评价配对，不能用逐评价独立核替代。该式不预付原 $J_a$ 线性、$J_0=0$ 或 $J_1=I$；相应恢复按原词消费者。原 $q$、词 $J_a$ 和比较型 $K$ 不是89.6的辅助 $J,K$。93.2给数学忠实 Hilbert 表示与有限 Gram，不制造具名实际准备、所有 $B(H)$ 算子的可取得像、任意向量制备或可执行相干控制。

2. **原态、效果、全部质量与完整 Born 菜单。** 原评价、原事件、准确原效果区间 $[0,1]$、每个实际完整菜单及接受归属必须来自同一原来源。原准备、共同根、实际抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度尺度、全部 P9 分支、每个分支独立的 $W_e$、全部原中间切口和固定支持上的全质量保留 C171.2、145.2及 A25.1第2行的原量词。互探接口仍按其有限维／最小可见和实尺度范围使用；原强度、原 $q$、中心比较权与概率质量不混同。其他块自己的 AS/EC、菜单外 OB及所需实际忠实二维到三维适配器保留。

   对同一实际完整有限菜单 $\{e_j\}$，只有 $\sum_j e_j=1$、原事件已绑定且 $m_\gamma>0$ 时，才用 $p_\gamma(j)=\gamma(e_j)/m_\gamma$；条件角菜单则只有在原来源实际供应 $\sum_j e_j=p$、相应条件化身份和 $\gamma(p)>0$ 时，才用 $\gamma(e_j)/\gamma(p)$。全部零、不等、次归一质量、中心权、中心经典混合、经典不等维块、静默部分及其未归一原读数均保留，零质量不除法、不删分支。一般无限或非离散菜单的可数可加及正常性仍取第6项的相应扩展来源。

   具名分析词与原菜单事件沿其原接线和实际读取次序：先原 $g^*$，再原 $d_s^*$，最后共同根；矩阵相同不能交换这个实际顺序，也不能合并相同矩阵但不同原程序。数学有限角、$\tau$、正延拓及正规正读取不增加物理准备、效果或菜单；一般无限维原态保持自身正泛函或已支付前对偶身份，不擅改为有限密度矩阵。

3. **native、真正相关联合与张量。** C171.3、145.3、A25.1第3行、A53.1及 W95.2、116.1要求的同一个实际非零相关联合完整保持。原全词 $K/J$、交叉零、旧局部乘法、忠实同向交换局部腿、共同实现、联合生成与分离、所需重数、全部真正相关输入、中央对、经典和不等维块、实际复制及每层递归同源参考均仍须原生取得。在消费者要求局部全矩阵代数的地方，仍须支付该准确前件，不能把一般 II∞ 局部腿直接代入有限全矩阵定理。

   每份所需系统与参考属于同一个共同来源，不能分别挑选后声称共同生成。相同边缘、分别可达、相同数学取向、两个有限角、一个数学张量表示或共同酉轨道都不供应真正联合。88.6只固定同一单域的旧乘法；只有原消费者全部联合条件同时满足时，才在其适用域接回原张量识别。

4. **typed CP、Kraus 接线与每层整台递归同源参考。** 对每条实际原细分支 $r:A\to B$、每个原合法 typed 前接和后接、每个输出的每个仍合法未来及每份原评价，保持未归一回溯

   $$
   \gamma_A(\beta_r b)=\gamma_B^r(b),
   \tag{96.2}
   $$

   连同反变合法复合、typed 分区、全未来自然性、全质量运输及原箭头商下降。正延拓本身不等于 CP。CP 取原完整同标签单位区间过程比较，或原整台实际箭头可再应用的递归同源二元参考规则；每条完整箭头连同系统、整个环境、全部成功／失败／细记录／port／post-port输出及每份输出每个仍合法未来，都属于同一规则类。真正遗忘、实际返回及合法复合箭头同样须在规则类内，不能由形式 CP 制造。

   递归参考路线的两端各有共同真实支持 $p_A,p_B$，以及忠实同向交换的系统腿和参考腿，例如

   $$
   i_A:\mathcal A_A\hookrightarrow p_A\mathcal A_{A^+}p_A,
   \quad j_A:M_2\hookrightarrow p_A\mathcal A_{A^+}p_A,
   \quad i_A(1)=j_A(I_2)=p_A,
   \tag{96.3}
   $$

   $B$ 端同理。三个实际参考投影 $q_1,q_2,q_3$ 与 $I_2$ 实张成 $(M_2)_{\rm sa}$。每次真实接线保留

   $$
   \beta_{r^+}i_B=i_A\beta_r,\qquad
   0\le\beta_{r^+}(j_B(q))\le j_A(q)
   \quad(q\in\{q_t,I_2-q_t:1\le t\le3\}).
   \tag{96.4}
   $$

   支配及 intertwining 要在全部原相关正输入和决定锥的全部原联合评价上成立；支持内补保持为支持内补，不变成环境补，两腿也不必生成整个环境或整个支持角。下一层系统是整台实际 $r^+$ 的全部响应，不只是原根代码。

   对每条根箭头和每个所需有限 $L$，必须给实际长 $L$ 链；对每个 $k\le L$ 保持忠实嵌入和精确累计支持运输

   $$
   M_A^k:\mathcal A_{A_0}\otimes M_{2^k}\hookrightarrow\mathcal A_{A_k},
   \quad \beta_kM_B^k=M_A^k(\beta_0\otimes\operatorname{id}_{2^k}),
   \quad P_A^{k+1}=i_{A,k}(P_A^k)\le p_{A,k+1}.
   \tag{96.5}
   $$

   累计真支持不改成新环境单位。任意精度版本保持每个正精度、每个有限深度及精确根身份；固定正误差不足。每个有限长度的实际链不要求一条实际无限链或物理无限张量积；任意多形式参考也不能替代完整实际链。Kraus算子公式只在准确合格有限全矩阵域，或另有适用正规物理表示、指定前对偶与所需收敛的域消费；一般正规子代数的正常 CP 对偶不自动成为全 $B(H)$ 上的算子 Kraus表示。90–92的数学投影和酉扩充不供应原箭头、共同参考或 CP。

5. **整台仪器、TP、条件更新与 Lüders。** 对每台原实际仪器保留全部原输入运输、完整 typed 菜单、原接受端、整个环境、全部成功／失败／细记录／port／post-port输出及每份完整输出所有仍合法未来。真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词与各自接受条件全取 C171.5、145.5、A25.1第5行及其原来源；数学存在平方根不等于原可执行平方根词。

   原星乘法和正夹心 $a\star c\star a$ 仅给代数入口。正次单位只给 TNI；TP还须整台原测试的完整 typed 单位分区。Lüders另须同一个完整输出的投影效果、像内每条射线保持及完整输出校准；同效果、同概率和统计重复性不代付该条件。只有严格正的实际输出质量可以归一，失败和零分支连同所有未来均保留。密度、迹类、算子 Kraus及迹公式仍限于其准确合格有限全矩阵域，或另已供应适用正规物理表示、指定前对偶及所需收敛的域；不得用 $\tau$ 的存在抹去细记录、port未来或这些表示前件。

6. **全部合法历史、全未来、真实遗忘、两侧和逆向返回及 CountRead。** 全部合法顺序、自适应和并行历史，每份完整输出的每个仍合法未来，整个环境、参考副本、全部细记录与泄漏，停止、拒绝、销毁，真正分组遗忘，同数两侧真实返回及同数逆向真实返回，均保持 C171.6、145.6、A8.4、25.1第6行及单位桥原消费者的完整量词。只有原真正粗事件可相加，丢弃记录不能充当真实遗忘；数学算子相同也不合并不同原程序、实际读取次序、原 $q$ 零集或 AC 方向。

   CountRead仍绑定读后同一原完整活动输入及其所有合法未来的实际返回；读后活动 ready接头、接受叶活动输出及第一合法消费者、具名分析词到原实际全菜单和接受端的接线，必须原生供应。负提升两条活路的分别受控实现与相干聚合实现各守原合同，数学负号不制造任何一条活路。原精确正生成 $B$ 与另名闭正生成 $B_{\rm cl}$ 区分；初始取得、指定有限树和被动精确混合解码的已有成果，只在其原平稳、真实同源和同初始版本范围使用，不用初始取得替代整份后续输出的全未来 Return。

   无限历史、无限／非离散记录、可数可加、物理正常性、指定前对偶及所需收敛各取原扩展来源；有限返回数值校准不供应这些条件。92中的数学投影网和正规正读取不生产物理无限记录，不证明读后真实双向返回，也不把未定义请求变成定义良好的操作。

7. **动力、物理钟、能量、定义域与共同正作用量。** C171.7、145.7、A25.1第7行的同一旧全域乘法、保持原域的流、实际相位和门序列、同一实际过程内可逆一参数群及实际逆、原物理钟与单位、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同仪器、共同作用量及同一个正 $\hbar$ 完整保持。原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 仍按各自来源的参数、设备、域和量纲使用；它们与本组取向符号、投影网及残差参数没有身份替换。

   只有这些物理前件齐备，才在相应物理表示和生成元域消费 $U(t)=e_\star^{-itH/\hbar}$、适用态域上的 $i\hbar\dot\rho=[H,\rho]_\star$ 和原旧响应动力。括号取识别后的同一 $\star$ 乘法；相反取向不能暗中换回环境乘法。93.1只给数学有界内导子，不生产物理时间、可控相位、实际门流、能量解释、控制成本、一般无界生成元域或跨装置共同 $\hbar$。

七项是同一原世界中相应条件的共同合取，不能让不同项各换一份来源。94.2只消费这些条件下已存在的定理；既有条件定理成立与实际前件是否已取得是两件事。本组没有构造同时供应七项的物理 producer。

## 97. 旧 QM 的七行对应与完整直观图景

**定义 97.1（准确条件对应）。** 下表每行都合取96.1该项全文及全部上游量词；短表仅定位数学消费者。

| 旧 QM 结构 | 本组支付的同一数学入口与既有消费者 | 必须同源支付的实际条件 |
| --- | --- | --- |
| 复 Hilbert、可观测量与相干叠加 | 88.6、93.2识别 $M_\sigma$；A6.3、8.1给忠实保锥、保单位和等距表示，93.3给全部有限旧复 Gram | 96.1第1项：原 $\Omega$/native、全词共同 $q/K/J$、跨评价配对、parent/ready、具名取得、合法控制和实际相干准备；表示不自动满射全 $B(H)$ |
| 态、效果、Born与全部质量 | A7.1、7.3及25.1第2行：原效果为 $[0,1]$，未归一权为 $\gamma(e)$，仅合格菜单的正质量归一 | 96.1第2项：每份原准备、完整菜单和接受归属、全部中间切口与固定支持全质量；零、不等、次归一、中心权和静默块保持 |
| 复合系统、真实相关联合与张量 | 同一 $\star$ 乘法进入 A53.1、25.1第3行及 W95.2、116.1的适用联合接口 | 96.1第3项：同一个非零相关实现、合法忠实同向交换局部腿、联合生成分离、重数、全部相关输入及每个实际参考 |
| 合法过程、typed CP与 Kraus | A8.3、14.2、25.1第4行以相同代数、锥和原回溯接过程比较或整台递归参考 | 96.1第4项：整台系统环境、全部输出每个合法未来、三实际投影及支持内补、每个所需有限深度与累计支持；Kraus另守准确表示域 |
| 完整仪器、TP、更新与 Lüders | A7.3、8.4、14.2、25.1第5行消费同一星乘法与正夹心 | 96.1第5项：全输入输出接线、完整单位分区、真实分组、接受条件、平方根词；正质量才归一，Lüders需同一完整输出的射线校准 |
| 历史、全未来、记录、遗忘与真实返回 | A8.4、14.2、25.1第6行在其合格域消费同一原代数上的合法复合和记录公式 | 96.1第6项：所有合法历史与未来、环境泄漏、两侧和逆向实际返回、CountRead、活动ready及真遗忘；无限记录的可数可加、正常性和前对偶另付 |
| 动力、物理钟、能量与共同正 $\hbar$ | 93.1给有界数学导子，A6.3、14.2、25.1第7行取得相同静态代数入口 | 96.1第7项：原钟、真实可逆流及实际逆、强连续实现、生成元域、能量与共同作用量；数学酉元、迹和指数参数不替代物理尺度 |

**定义 97.2（完整中文直观说明）。** 原来的问题是：同一个世界给出的两两有方向比较、相加三角、单位小窗及任意三标签的正反配平，能否认回那张原先未知的响应表。这里选择的数学范围是一个任意大的半有限 II∞ 因子的全部自伴对象；它可以不可分，也不必有一份覆盖全体的忠实正规状态。给定迹是一把定位有限预算区域的数学尺，不是已经获得的物理准备。每个迹有限区域内部仍可能无限维。原 P2已经保证同角输入的旧答案留在同角，完整原关系也能逐层限制；因此直接调用给定的有限 continuous 分类，在每个区域里认回原答案。两个区域都能放进一个更大的有限区域，同一个不交换输入对不能同时服从正反两个公式，故所有有限区域只能共享一个整体符号。

只知道这些有限区域各自正确，还没有解决带着无限支撑的输入。真正的三元连接首先固定任意全域对象 $x$，拿一个有限投影 $p$ 与它比较。P2使这份真实输出虽未必留在原来的 $p$，却只能占据某个更大的有限支撑。把 $x,p,0$ 放进同一次 PB，两份实际外层便共同落回一个已经认清的有限区域；读回的是同一个旧输出，不是另外挑的标准答案，于是有限投影对全部全域输入的整行被钉住。再换成任意有限支撑对象 $h$，把第三标签换成任意有限投影 $d$。原 PB与已知交换子配平相减，要求同一残差同时满足一个对称乘积关系并与每个有限投影交换。残差又只占有限支撑，在稍大一点的有限因子里只能成为标量；多出来的非零补角迫使这个标量为零。这样得到的是真正的完整混合行，没有先假定未知响应能拆和或按投影下降。

现在把一对原实标签记成 $Z=b+\sigma i d$。PB允许用已经认清的有限支撑首标签共同重组它们，且标准交换子之外的那份偏差保持完全相同。重选另一份合法原输入，就得到 Cayley 变换；有界辐角让每个有限支撑酉元都只需两次这样的精确重组。这条运输始终作用于同一份旧偏差，没有用稠密性宣布未知函数连续。

无限端点必须看清方向：一个真余等距不能直接靠左酉变换搬到自己的正绝对值。因子投影比较保证，原对象与交换两原标签后的对象至少有一个能把极部分补成等距。对这个正确方向，每个有限投影和它的等距像都落在同一个有限角；在那个角内补齐的是真正酉元，补角也真的有相同有限迹。让有限投影按有向网扩大，这些酉变换就把该方向的虚部压向零。取极限的是已知正平方的读数；原 P2说虚部平方预算越小，容许的响应读数也越小。但精确运输又说这仍是出发时那同一份固定偏差，所以任何非零读数都会在某个实际有限步骤撞上预算矛盾。正规正读取分离元素，偏差只能为零；若用了交换方向，再由原反对称性读回原方向。于是全部原输入上的同一旧响应都被认回为一个共同符号的交换子，线性、连续、共同导子与同一复乘法随后才成为结论。

这删除了所选因子模型的全局有限性，没有删掉完整原域、准确锥、原评价和任何原质量。正取向给环境乘法，反取向给相反乘法；同一个原自伴对象、锥、单位和范数都保持。已有后端随即给有限复 Gram、原换括号关系和忠实 Hilbert 表示。完整量子候选同时保留七项实际来源：相干准备与全词共同网络，全部 Born 菜单及零、不等、次归一质量，真实相关联合，整台过程和仪器连同整个环境的全部输出，每个所需深度与支持的递归同源参考，所有合法历史和每个未来、真遗忘、两侧及逆向真实返回与完整 CountRead，以及物理钟、能量、生成元域和共同正作用量。数学的迹、投影、酉元和正规读取没有替同一个原世界制造这些东西；只有七项实际条件齐备，才进入各自准确域的量子消费者。一般 JB、type III、非因子和不完备原域仍有自己的问题，不能由这一完整 II∞ 分类代答。

## 追加锚（本行以下为增补区）

## 98. 任意半有限 continuous 原域的中央分类候选

本组将88–97的因子模型扩展为任意半有限continuous代数，统一允许有限与无限中央混合；卷首88–97的适用范围按原条目保持。

**定义 98.1（固定纸面前件与同一原模型）。** SM 指[前谱混合卷](AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md)，SF 指[本半有限原始响应卷](AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md)，A 指[任意维静态卷](AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md)，C 指[中央续卷](AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY_CONTINUATION.md)，PT 指[原 PB 运输续卷](AURIC_ORIGINAL_POLYNOMIAL_PB_TRANSPORT_AND_FIBER_BOUNDARIES_CONTINUATION.md)，W 指[单位桥](AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md)，R3 指[三标签刚性卷](AURIC_C128_THREE_LABEL_POSITIVITY_AND_ORIGINAL_RELATION_RIGIDITY.md)。有限分类的准确前件是 [dev23dae 的 SM79.1–84.1，尤其 SM79.3](https://github.com/the-omega-institute/trureturing/blob/23dae741512cdf450fc5b2d76b63ed51780f9915/docs/develop/theory/AURIC_SPECTRAL_MIXED_RESPONSES_AND_DIRECT_WINDOW_BOUNDARIES.md#79-完整有限-continuous-原域与中央取向候选)。半有限证明的复用接口是[公开固定源 SF88–97](https://github.com/the-omega-institute/trureturing/blob/efef304808f06caec5026b013ca9707c8495aa23/docs/develop/theory/AURIC_SEMIFINITE_ORIGINAL_RESPONSE_AND_CENTRAL_POLAR_GEOMETRY.md#88-完整半有限-ii∞-原域与唯一共同响应)。其余仓内源固定取 [dev23dae 理论树](https://github.com/the-omega-institute/trureturing/tree/23dae741512cdf450fc5b2d76b63ed51780f9915/docs/develop/theory)。这些是纸面前件和消费者，不是 kernel 或独立验证证据。

保持唯一原 $\Omega/\mathrm{native}$ 及同一 $(E,C,u,N,\mathcal P,S,D)$。本组明确模型类 $\Gamma_{\rm sf,cont}$ 是任意半有限 continuous 复 von Neumann 代数 $M$，即没有非零 type I 中央直和项，允许有限 type $\mathrm{II}_1$、无限 type $\mathrm{II}_\infty$ 及任意中央混合；给定忠实正规半有限标量迹 $\tau$。取

$$
E=M_{\rm sa},\qquad C=M_+,\qquad u=1,\qquad
N(a)=\|a\|,\qquad S(a,b)=a\circ b=\frac{ab+ba}{2}.
\tag{98.1}
$$

不要求因子、Hilbert 空间或预对偶可分、可数可分解或全局忠实正规状态。结合乘法、伴随、极分解、Borel 函数演算和 $\tau$ 是给定模型结构。$\mathcal P$ 保持全部原索引，是分离 $E$ 且准确决定 $C$ 的正实线性评价族：

$$
a\in C\ \Longleftrightarrow\ (\forall\gamma\in\mathcal P)\ \gamma(a)\ge0,
\qquad m_\gamma=\gamma(1)\ge0.
\tag{98.2}
$$

相同限制但不同来源的评价不合并；全部零、不等、次归一质量、中心权和静默部分保留。$\tau$、角迹及下文的数学正规正泛函都不加入物理准备族。模型类的选择不从裸 $\Omega$ 自动产生。

**定义 98.2（完整原关系）。** 同一原总映射 $D:E^2\to E$ 反对称。对每份原 $\gamma$ 及全部原标签，记

$$
g_\gamma(a,b)=\gamma(a\circ b)-i\gamma D(a,b).
$$

完整 A1 要求每对有向二表 $G_\gamma(a,b)=(g_\gamma(c_j,c_k))_{j,k=1}^2$ 正半定，$(c_1,c_2)=(a,b)$，并保留反向次序、零、重复及所有实缩放、实平移标签。完整 A2 要求对全部 $a,b\in E$，相加三表 $(a+b,a,b)$ 及其全部相应排列的实部在整个 $\mathbb R^3$ 上半正定，指定向量 $(1,-1,-1)$ 及排列后的相应向量有零二次值。完整 A3 要求 $S(1,1)=1$，并有同一个固定有理 $0<\theta\le1$，使全部原 $0\le y\le\theta1$ 满足 $S(y,y)\le y$。这些条件连同98.1–98.2记为 $\mathsf H_{\rm orig}$；不缩成一个框架或谱标签子域。

特别，全部原 $a,b\in E$、$\gamma\in\mathcal P$ 满足完整 P2：

$$
\begin{pmatrix}
\gamma(a^2)&\gamma(a\circ b)-i\gamma D(a,b)\\
\gamma(a\circ b)+i\gamma D(a,b)&\gamma(b^2)
\end{pmatrix}\succeq0.
\tag{98.3}
$$

完整 PB 对每个实际原三元组 $a,b,d\in E$ 要求

$$
\begin{gathered}
v=D(a,b)-a\circ d,\qquad w=a\circ b+D(a,d),\\
D(b+v,d+w)-D(b-v,d-w)=-2b\circ v-2d\circ w.
\end{gathered}
\tag{98.4}
$$

这是全部原评价读取的正反平方配平的元素形式，评价分离性保证两者等价。任意实尺度的原标签及每次嵌套输入仍在完整原域量词中。没有预付 $D$ 的线性、齐次、连续、可测、中央下降、压缩下降、局部共同导子或物理 producer；也不以只含多项式第三槽的子族替换完整 PB。

固定二表的复系数后，其二次型是 $E$ 中的元素；98.2使该元素为正，再由任意数学正实线性泛函 $\phi$ 读取。这是 SM79.2、SF88.5、PT118.2 的既有准确锥机制，给

$$
|\phi D(a,b)|^2\le\phi(a^2)\phi(b^2)-\phi(a\circ b)^2
\qquad(\phi\ge0;\ a,b\in E).
\tag{98.5}
$$

因此 $D(a,0)=D(0,a)=0$。正实泛函通过唯一复线性延拓成为 $M$ 上的正泛函；其范数是 $\phi(1)$，不要求归一或正规。原评价无须正规。

**定理 98.3（完整半有限 continuous 原响应的正反分类）。** 以固定 SM79.3 为纸面前件，在98.1–98.2的同一模型及全部原评价上，以下两项等价：

1. 同一原总 $D$ 满足完整 $\mathsf H_{\rm orig}$、反对称性、全部 P2 和完整 PB。
2. 存在唯一 $Q\in Z(M)_{\rm sa}$、$Q^2=1$，使

   $$
   \boxed{D(a,b)=\frac{iQ}{2}[a,b]\qquad(\forall a,b\in M_{\rm sa}).}
   \tag{98.6}
   $$

反向保持同一个 $E,C,u,N,S,\mathcal P$ 和每份原质量。令 $q_\pm=(1\pm Q)/2$，同一原乘法 $a\star b=a\circ b-iD(a,b)$ 的复双线性延拓为

$$
X\star Y=q_+XY+q_-YX,
\qquad A_Q=q_+M\oplus(q_-M)^{\rm op}.
\tag{98.7}
$$

证明见99–103。有限首行是100的结论，中央局部极部桥是102的结论，均不是额外前件。零代数取唯一 $Q=0=1_M$，所有关系为零；以下对非零 $M$ 叙述。实际物理来源另取105的完整七项。

## 99. 有限角的局部取向、中央提升与兼容

**定义 99.1（迹有限网与规范角结构）。** 记

$$
\mathcal F_\tau=\{p=p^*=p^2\in M:\tau(p)<\infty\},\qquad
\mathcal I_{\rm fs,sa}=\bigcup_{p\in\mathcal F_\tau}(pMp)_{\rm sa},
\qquad z_p=c_M(p).
\tag{99.1}
$$

有限支撑指99.1，既不指有限维，也不替换全域。成熟投影公式

$$
(p\vee q)-p\sim q-(p\wedge q)
\tag{99.2}
$$

给 $\tau(p\vee q)\le\tau(p)+\tau(q)$，故 $\mathcal F_\tau$ 对有限并有向。其上确界为1：若非零余投影 $r$ 存在，忠实半有限性给 $0\ne a\le r$、$\tau(a)<\infty$；某个非零谱投影 $e=1_{[\varepsilon,\infty)}(a)$ 满足 $e\le r$、$\tau(e)\le\tau(a)/\varepsilon<\infty$，矛盾。因此按包含排序的全部迹有限投影构成 $e\uparrow1$ 的强收敛网，且 $z_e\uparrow1$。不将此网换成序列。

对非零 $p\in\mathcal F_\tau$，$\tau_p=\tau|_{pMp}/\tau(p)$ 是忠实正规 tracial state，故 $pMp$ 有规范忠实正规中心值迹

$$
T_p:pMp\longrightarrow Z(pMp),\qquad T_p(p)=p.
\tag{99.3}
$$

它是中心双模线性的正含单位映射，满足 $T_p(XY)=T_p(YX)$。这是有限角自己的规范迹，不把 $T_p$ 的值域或单位改成 $Z(z_pM)$ 或 $z_p$。有限性也由 $\tau_p$ 保证：角内真等距会违反有限忠实迹。无 type I 中央项等价于没有非零交换投影角；其性质传给 $pMp$，因为 $r\le p$ 时 $r(pMp)r=rMr$。所以每个非零迹有限角都是完整有限 continuous 代数，正好属于 SM79.1 的环境。

另有规范中心同构

$$
\rho_p:Z(z_pM)\xrightarrow{\ \cong\ }Z(pMp),\qquad c\longmapsto cp.
\tag{99.4}
$$

其满射性是成熟角中心定理：若投影 $f\in Z(pMp)$，则 $(p-f)Mf=0$，中央载体性质给 $f=c_M(f)p$；再对中央自伴元作谱演算即得 $Z(pMp)=Z(M)p$。核在 $z_pZ(M)$ 上为零，因为中央元 $c$ 若 $cp=0$，其谱支撑与 $z_p$ 正交，故 $cz_p=0$。这一区分只涉及已给代数，不涉及 $D$。

**复用 99.2（完整有限角的准确调用）。** A50.2、A51.1及 SF89.2 的 P2 支撑接口给

$$
D\bigl((pMp)_{\rm sa},(pMp)_{\rm sa}\bigr)\subset(pMp)_{\rm sa}.
\tag{99.5}
$$

参数为 $X=E=M_{\rm sa}$、$U_p(x)=pxp$；角原域正好是完整 $(pMp)_{\rm sa}$。限制评价仍逐原 $\gamma$ 索引，$\gamma_p=\gamma|_{(pMp)_{\rm sa}}$，分离角且准确决定角锥；局部辅助质量 $\gamma(p)$ 与原总质量 $m_\gamma=\gamma(1)$ 分开，不归一、不删零限制。全部零、重复、实缩放、以 $p$ 平移、相加三表及每个排列原样继承。$p^2=p$；$0\le y\le\theta p$ 蕴含 $0\le y\le\theta1$，所以同一小窗成立。99.5使每次角内 PB 的内值、位移、四个外层标签和外值逐层留在角内。角上数学正泛函 $\psi$ 可正延拓为 $x\mapsto\psi(pxp)$，所以全部正读取也继承。没有另造角的物理 $\Omega$、native、准备或菜单。

因此 SM79.3 的准确参数代入为

$$
(M,E,u,C,N,S,D,\mathcal P,T)
=(pMp,(pMp)_{\rm sa},p,(pMp)_+,\|\cdot\|,\circ,
D|_{(pMp)_{\rm sa}^2},\{\gamma_p\}_{\gamma\in\mathcal P},T_p).
\tag{99.6}
$$

它给唯一局部取向

$$
Q_p\in Z(pMp)_{\rm sa},\quad Q_p^2=p,\qquad
D(a,b)=\frac{iQ_p}{2}[a,b]\quad(a,b\in(pMp)_{\rm sa}).
\tag{99.7}
$$

定义其唯一中央提升 $\widehat Q_p=\rho_p^{-1}(Q_p)\in Z(z_pM)_{\rm sa}$，故

$$
Q_p=\widehat Q_pp,\qquad \widehat Q_p^2=z_p.
\tag{99.8}
$$

有限分类及同角支撑均为复用，不重证 SM79.3，也不将 $Q_p$ 与 $\widehat Q_p$ 当作同一个角单位下的对象。

**命题 99.3（嵌套兼容只比较同一个旧值）。** 若 $0\ne p\le g\in\mathcal F_\tau$，则

$$
Q_p=pQ_g,\qquad \widehat Q_p=z_p\widehat Q_g.
\tag{99.9}
$$

证明。$pQ_g$ 中央于 $pMp$、自伴且平方为 $p$；把99.7的 $g$ 角公式用于任意 $a,b\in(pMp)_{\rm sa}$，它给这同一个旧 $D(a,b)$ 的公式。SM79.3在 $p$ 角的唯一性遂给 $Q_p=pQ_g$。也可在 $pMp$ 内取实际反交换框架 $h^2=k^2=p$、$hk=-kh$，使用其角单位的恢复式直接核对：

$$
i hkD(h,k)=i hk(iQ_ghk)=pQ_g=Q_p.
\tag{99.10}
$$

这里 $(hk)^2=-p$；没有称 $h$ 为 $g$ 角反射，没有把 $h^2=p$ 改成 $g$，也不需要声称 $h$ 在 $gMg$ 中中心平衡。由 $Q_g=\widehat Q_gg$ 得 $Q_p=\widehat Q_gp$；99.4的单射性给提升式99.9。∎

**定理 99.4（不先下降 $D$ 的全局中央拼接）。** 存在唯一 $Q\in Z(M)_{\rm sa}$、$Q^2=1$，使所有非零迹有限 $p$ 满足

$$
z_pQ=\widehat Q_p,\qquad pQ=Q_p.
\tag{99.11}
$$

证明。置 $e_p^\pm=(z_p\pm\widehat Q_p)/2$；零角取零。若 $p\le g$，99.9给 $e_p^\pm=z_pe_g^\pm$，故两族都是递增的中央投影网。任意两角有共同迹有限上界，所以 $e_p^+e_q^-=0$。令 $e^\pm=\sup_p e_p^\pm$，得 $e^+e^-=0$，且 $e^++e^-=\sup_p z_p=1$。取 $Q=e^+-e^-$ 即给99.11。若另一个中央对合也满足这些式子，其差乘每个 $z_p$ 为零，而 $z_p\uparrow1$，故差为零。这里只拼已经识别的中央算子，未对未知 $D$ 作中央分解、加法或极限。∎

此后固定辅助数学记号

$$
J=iQ\in Z(M),\quad J^*=-J,\quad J^2=-1,\qquad
K(a,b)=\frac J2[a,b].
\tag{99.12}
$$

它们与105的 native 全词 $J_a,K$ 区分。99.7、99.11已给任意同一迹有限角内的原值 $D(a,b)=K(a,b)$；尚未给跨角或任意中央切分输入的原值。

## 100. 同一原 PB 生产非因子的全部有限首行

**复用 100.1（一个有限支撑输入的实际输出支撑）。** SF89.4的块支撑证明不使用因子性，参数现在为99.12的中央 $J$。准确地，若 $h=php\in\mathcal I_{\rm fs,sa}$、$x=x^*\in M$，置 $r=D(h,x)$、$q=1-p$，则

$$
qrq=0,
\qquad r=(p+s)r(p+s),\quad s\le q,\quad s\precsim p,
\quad\tau(p+s)\le2\tau(p).
\tag{100.1}
$$

为明确实际支撑输入：支撑在 $q$ 的任意正泛函在98.5中有 $\phi(h^2)=0$，故读取 $r$ 为零，分离性给 $qrq=0$。取 $qrp$ 的左支撑 $s$；极分解把它与某个 $p$ 的子投影等价，所以 $\tau(s)\le\tau(p)$。自伴性给100.1。$h\circ x$ 与 $K(h,x)$ 也自伴且零 $q,q$ 块，完全相同的块支撑机制适用；$J$ 中央保证 $K(h,x)$ 的这些性质。有限多个此类输出和标签有共同迹有限支撑。没有删除交叉块，也没有断言输出留在原 $p$ 角；这只是已刊支撑机制的准确非因子实例。

**引理 100.2（迹有限投影对全域的原整行）。** 对全部 $p\in\mathcal F_\tau$、$x\in E$，有 $D(p,x)=K(p,x)$。

证明。$p=0$ 用98.5。固定其余 $p,x$ 的同一个旧值 $r=D(p,x)$，令 $k=p\circ x$。100.1使 $p,r,k$ 共同支撑于某个迹有限角 $gMg$。实际原 $\operatorname{PB}(x,p,0)$ 的位移是 $v=-r,w=k$，故

$$
D(p-r,k)-D(p+r,-k)=2p\circ r.
\tag{100.2}
$$

四个外层标签同属 $gMg$，99.7、99.11在这一个共同角中给

$$
\begin{aligned}
D(p-r,k)-D(p+r,-k)
&=\frac J2\bigl([p-r,k]+[p+r,k]\bigr)\\
&=J[p,k]=\frac J2[p,x].
\end{aligned}
\tag{100.3}
$$

所以 $pr+rp=J[p,x]/2$。已知 $K(p,x)$ 满足同式。置 $t=r-K(p,x)$，得 $pt+tp=0$；这杀掉 $p,p$ 块及两侧交叉块。100.1另给 $(1-p)t(1-p)=0$，故 $t=0$。展开的只有已知交换子；未知 $D$ 没有使用奇性、齐次性或相加性。∎

**引理 100.3（已知候选在全域的 PB 身份）。** 对任意自伴 $a,b,d$，以 $K$ 取98.4的位移 $v_0,w_0$，令 $Z=b+Jd$。则

$$
\begin{gathered}
v_0+Jw_0=JaZ,\
Z^*Z=b^2+d^2+2K(b,d),\
\bigl((1\pm Ja)Z\bigr)^*\bigl((1\pm Ja)Z\bigr)=Z^*(1+a^2)Z.
\end{gathered}
\tag{100.4}
$$

这些是 SM84.4–84.5、SF90.5的结合乘法身份，实际只用 $J$ 中央、$J^*=-J$、$J^2=-1$。两符号平方差展开为 $4b\circ v_0+4d\circ w_0$ 加上两外层 $K$ 差的两倍，所以恰是 $K$ 的完整 PB。与有限性、因子性和未知 $D$ 无关。

**定理 100.4（全部有限支撑首标签的完整全域行）。** 对全部 $h\in\mathcal I_{\rm fs,sa}$、$x\in E$，有

$$
\boxed{D(h,x)=K(h,x).}
\tag{100.5}
$$

证明。$h=0$ 用98.5；否则取它的实际支撑 $p=s(h)\in\mathcal F_\tau$，固定

$$
r=D(h,x),\qquad t=r-K(h,x).
$$

100.1给 $r,t$ 有迹有限支撑，并保留原来的零补角块

$$
(1-p)t(1-p)=0.
\tag{100.6}
$$

对任意迹有限投影 $d$，实际原三元组 $\operatorname{PB}(x,h,d)$ 有

$$
v=-r-x\circ d,\qquad w=x\circ h+D(x,d).
$$

100.2和反对称性已经给 $D(x,d)=K(x,d)$。若 $v_0,w_0$ 用 $K$ 计算同一三元组，则

$$
v=v_0-t,\qquad w=w_0.
\tag{100.7}
$$

100.1使 $h,d,v,w,v_0,w_0,t$ 全部落在某个共同迹有限角；角可依赖这次固定的 $h,x,d$。因此这份原 PB 的两外值准确等于该角中的 $K$，可与100.3对同一三元组的 PB 相减。用已知双线性展开外值，外层差的差为 $-2K(t,d)=-J[t,d]$；右端差为 $2h\circ t=ht+th$。故

$$
\boxed{-J[t,d]=ht+th\qquad(d\in\mathcal F_\tau).}
\tag{100.8}
$$

先取 $d=0$，得 $ht+th=0$；再代回，因 $J$ 可逆，得到

$$
[t,d]=0\qquad(\forall d\in\mathcal F_\tau).
\tag{100.9}
$$

现在支付非因子的中心性。对每个 $e\in\mathcal F_\tau$，$eMe$ 的所有投影都仍在 $\mathcal F_\tau$ 中。100.9使 $t$ 与这些投影及其谱线性组合交换，故与整个 $eMe$ 交换。对任意 $y\in M$，已知算子网 $eye\to y$ 强收敛；乘固定有界 $t$，得 $ty=yt$。所以

$$
t\in Z(M)_{\rm sa},\qquad ht=0.
\tag{100.10}
$$

最后同时使用原支撑与100.10，而不寻找因子标量或额外补角。$p=s(h)$ 且 $ht=0$，由支撑的核定义或 $h$ 的谱投影得 $pt=0$。中央性使100.6变为 $(1-p)t=0$。两式相加即 $t=0$。等价地，中央性和100.6先使 $t$ 支撑在 $p$，而 $ht=0$ 又迫使它支撑在 $1-p$；两者只能同时为零。这个论证在每个有限及无限中央部分共同成立，即使 $p=1$ 或 $M$ 有非零有限中央项也不漏项。没有假定 $h^2=p$，只使用任意自伴 $h$ 的真实支撑。∎

100.2的实际投影 PB、100.8的实际第三投影 PB和100.6的原支撑共同支付有限首行；不能用只知道 $[t,d]=0$、只消无限中央部分或另加 FR 来代替。证明对未知映射始终只使用同一次原输出及已分类的共同有限角。

## 101. 中央复坐标中的唯一精确运输接口

**定义 101.1（同一旧缺陷的重索引）。** 对每个 $Z\in M$，有唯一原自伴坐标

$$
Z=b+Jd,\qquad b=\frac{Z+Z^*}{2},\qquad
 d=-\frac J2(Z-Z^*),\qquad
\mathfrak F(Z)=D(b,d)-K(b,d)\in M_{\rm sa}.
\tag{101.1}
$$

$J$ 中央且 $J^*=-J,J^2=-1$，保证逆式自伴并确实互逆。这不是未知 $D$ 的复线性延拓；$\mathfrak F$ 不预带齐次、可加、连续或中央下降性质。

**命题 101.2（复用 SF91.2–91.4并核对中央参数）。** 对全部 $Z\in M$，有

$$
\begin{gathered}
\mathfrak F(C_aZ)=\mathfrak F(Z),\qquad
C_a=(1+Ja)(1-Ja)^{-1}\quad(a\in\mathcal I_{\rm fs,sa}),\\
\mathfrak F(UZ)=\mathfrak F(Z)\quad
\left(U\in\mathcal U_{\rm fs}:=
\{1-p+u:p\in\mathcal F_\tau,\ u\in\mathcal U(pMp)\}\right),\\
\mathfrak F(\mathcal T Z)=-\mathfrak F(Z),\qquad \mathcal T Z=JZ^*.
\end{gathered}
\tag{101.2}
$$

证明及复用核对。SF91的实际输入在此是同一完整 $E$、100.5的完整有限首行及99.12的 $J=iQ$。在 $\operatorname{PB}(a,b,d)$ 中，100.5同时识别两个内值；100.4给 $v+Jw=JaZ$。两份实际外层正是 $(1\pm Ja)Z$ 的101.1坐标。与已知 $K$ 的 PB 相减，得到

$$
\mathfrak F((1+Ja)Z)=\mathfrak F((1-Ja)Z).
\tag{101.3}
$$

$1-Ja$ 可逆，因为 $(1-Ja)^*(1-Ja)=1+a^2$。对任意目标 $W$ 重选真正原输入 $Z_0=(1-Ja)^{-1}W$，101.3给 Cayley 等式；没有把逆元或任何系数从未知函数中提出。这里只需 $J$ 中央，不需 $J$ 是标量。

对 $U=1-p+u$，在 $pMp$ 内取有界 Borel 辐角 $L=L^*$、$\|L\|\le\pi$、$u=e^{iL}$，在补角置零。令

$$
H=QL,\qquad a=\tan(H/4).
\tag{101.4}
$$

$Q$ 中央使 $H=H^*$、$H=pHp$、$\|H\|\le\pi$，且 $e^{JH}=U$。$a$ 迹有限支撑且有界；中央 $J$ 的两个谱分支上的标量函数身份共同给

$$
C_a=e^{JH/2},\qquad U=C_a^2.
\tag{101.5}
$$

有限两次 Cayley 等式即给全部 $\mathcal U_{\rm fs}$ 作用。$-1$ 谱也包含在内；$\tan$ 仅用于 $[-\pi/4,\pi/4]$。不使用可能无界的 $\tan(H/2)$、反射归一化、稠密群或未知响应的极限。

最后，$\mathcal T(b+Jd)=d+Jb$，故原反对称性直接给第三式。它不要求分别奇性、$\mathfrak F(JZ)=\mathfrak F(Z)$ 或 $\mathfrak F(Z^*)=-\mathfrak F(Z)$。SF91的这一重索引、实际 Cayley、bounded $H/4$ 两步和方向交换均按上述准确参数复用；不另立第二套完整运输。∎

## 102. 中央局部极部桥与两个全局原输入的排零

**引理 102.1（中央比较只选择读数方向）。** 固定任意 $Z\in M$，写极分解 $Z=v|Z|$，$p=v^*v,q=vv^*$。有中央投影 $z$，以及同一个全局等距 $w\in M$、$w^*w=1$，使

$$
\begin{aligned}
zZ&=zw|Z|,\\
(1-z)\mathcal T Z&=(1-z)w|\mathcal T Z|.
\end{aligned}
\tag{102.1}
$$

证明。任意 von Neumann 代数的中央比较给

$$
z(1-p)\precsim z(1-q),\qquad
(1-z)(1-q)\precsim(1-z)(1-p).
\tag{102.2}
$$

取部分等距 $s_+$、$s_-$，分别满足

$$
\begin{gathered}
s_+^*s_+=z(1-p),\quad s_+s_+^*\le z(1-q),\\
s_-^*s_-=(1-z)(1-q),\quad s_-s_-^*\le(1-z)(1-p).
\end{gathered}
$$

$\mathcal T Z=JZ^*$ 的极部分等距是 $Jv^*$，初末投影为 $q,p$，因为 $J$ 中央且酉；其绝对值是 $|Z^*|$。令

$$
w_+=zv+s_+,\qquad w_-=(1-z)Jv^*+s_-,\qquad w=w_++w_-.
\tag{102.3}
$$

各对初末支撑正交，故 $w_+^*w_+=z$、$w_-^*w_-=1-z$；中央正交使 $w^*w=1$。新增部分在相应绝对值上为零，给102.1。$z=0,1$ 和零输入同样成立。

这里仅拼已知极分解的等距元；两个待读对象仍分别是完整的原输入 $Z$ 和完整的原输入 $\mathcal T Z$。不引入混合输入 $zZ+(1-z)\mathcal T Z$ 的未知响应，也不推断 $\mathfrak F(zZ)=z\mathfrak F(Z)$。∎

**引理 102.2（有限角补酉的准确非因子比较）。** 对任意全局等距 $w$，存在按全部 $e\in\mathcal F_\tau$ 排序的 $U_e\in\mathcal U_{\rm fs}$，使

$$
U_ee=we,\quad U_e\longrightarrow w\text{ 强收敛},\qquad
\delta_e=U_e^*w-1,\quad
\delta_ee=\delta_e^*e=0,\quad\|\delta_e\|\le2.
\tag{102.4}
$$

证明。置 $r_e=wew^*$、$f_e=e\vee r_e$。$we$ 的初末投影为 $e,r_e$，$\tau(r_e)=\tau(e)$，99.2给 $\tau(f_e)\le2\tau(e)<\infty$。在实际有限角 $f_eMf_e$ 中，用其规范中心值迹 $T_{f_e}$ 计算：

$$
\begin{aligned}
T_{f_e}(e)&=T_{f_e}(r_e),\\
T_{f_e}(f_e-e)
&=f_e-T_{f_e}(e)
=f_e-T_{f_e}(r_e)=T_{f_e}(f_e-r_e).
\end{aligned}
\tag{102.5}
$$

有限中心值迹比较给 $f_e-e\sim f_e-r_e$；这不是从两个投影等标量迹推等价。取实现该等价的 $s_e$，则 $u_e=we+s_e$ 是 $f_eMf_e$ 的酉元，$U_e=u_e+(1-f_e)$ 为所需实际有限支撑酉元。只需这份中心迹相减，不使用对任意 $f$ 均不成立的补角等价公式。$e=0$ 时取 $U_0=1$。

在任意忠实具体表示中，

$$
\|(U_e-w)\xi\|\le2\|(1-e)\xi\|\longrightarrow0.
\tag{102.6}
$$

并且 $U_e^*we=e$、$w^*U_ee=e$，给102.4的两个零式；同样有

$$
\|(U_e^*w-1)\xi\|=\|(w-U_e)\xi\|,\qquad
\|(w^*U_e-1)\xi\|\le\|(U_e-w)\xi\|.
\tag{102.7}
$$

故 $U_e^*w\to1$ 强*收敛。SF92.2的支撑、强收敛和这两份估计均不使用因子性；本引理替换的是补酉中的比较前件，准确使用102.5。没有声称 $U_e^*\to w^*$ 强收敛。∎

**引理 102.3（中央局部正读取的固定平方预算）。** 若中央投影 $c$、全局输入 $Y\in M$ 和全局等距 $w$ 满足

$$
cY=cwA,\qquad A=|Y|,
\tag{102.8}
$$

则 $c\mathfrak F(Y)=0$。

证明。对102.2的同一网令

$$
W_e=U_e^*Y=x_e+Jy_e,\qquad x_e,y_e\in E.
$$

101.2对每个有限阶段给同一元素的精确等式

$$
\mathfrak F(W_e)=\mathfrak F(Y),\qquad
\|x_e\|,\|y_e\|\le\|Y\|.
\tag{102.9}
$$

现在只取任意支撑在 $c$ 的数学正规正泛函 $\phi$，即 $\phi(X)=\phi(cX)$。不对未知映射作中央限制。102.8及中央性使

$$
cW_e=c(1+\delta_e)A,\qquad
cy_e=-\frac J2c(B_e-B_e^*),\quad B_e=\delta_e A.
\tag{102.10}
$$

由102.4，自伴的支撑等式给

$$
\delta_e^*\delta_e\le4(1-e),\qquad
\delta_e\delta_e^*\le4(1-e).
$$

设 $\eta_e=-J(B_e-B_e^*)/2$。$J$ 中央、酉且反自伴，所以 $\eta_e$ 自伴，并由 $(B_e+B_e^*)^2\ge0$ 得

$$
\begin{aligned}
\eta_e^2&\le\tfrac12(B_e^*B_e+B_eB_e^*),\\
B_e^*B_e&\le4A(1-e)A,\qquad
B_eB_e^*\le4\|A\|^2(1-e).
\end{aligned}
\tag{102.11}
$$

$c y_e=c\eta_e$、$\phi$ 支撑在 $c$，因此 SF92.5–92.6 的同一 normal-square 预算现在准确变成

$$
\phi(y_e^2)=\phi(\eta_e^2)
\le2\phi(A(1-e)A)+2\|A\|^2\phi(1-e)\longrightarrow0.
\tag{102.12}
$$

只用 $e\uparrow1$、$AeA\uparrow A^2$ 和 $\phi$ 正规。全局虚部无须在另一个中央部分趋零；只有这份支撑读数的已知平方预算取极限。

为核对中央 $J$ 不改变交换子预算，对任意数学正 $\phi$ 及自伴 $x,y$，C* Cauchy–Schwarz分别用于 $Jxy$ 与 $Jyx$，因为 $J^*J=1$ 且 $J$ 中央，给

$$
|\phi(Jxy)|,\ |\phi(Jyx)|
\le\sqrt{\phi(x^2)\phi(y^2)},\qquad
|\phi K(x,y)|\le\sqrt{\phi(x^2)\phi(y^2)}.
\tag{102.13}
$$

例如第一式取 Cauchy–Schwarz 的第一元为 $-Jx$、第二元为 $y$，其第一平方就是 $x^2$；第二式互换 $x,y$。由98.5、102.9和102.13，

$$
\begin{aligned}
|\phi\mathfrak F(Y)|
&=|\phi\mathfrak F(W_e)|\\
&\le2\sqrt{\phi(x_e^2)\phi(y_e^2)}
\le2\|Y\|\sqrt{\phi(1)\phi(y_e^2)}\longrightarrow0.
\end{aligned}
\tag{102.14}
$$

左端始终为同一个固定旧缺陷的读数，故为零；$\phi(1)=0$ 时泛函恒零，不除法。任意 $cM$ 上的正规正泛函 $\psi$ 都可延拓为 $X\mapsto\psi(cX)$，所以这些支撑在 $c$ 的正规正泛函分离 $(cM)_{\rm sa}$，给 $c\mathfrak F(Y)=0$。这应用的是两个全局标签 $x_e,y_e$ 的原 P2，绝不是 $D(cx_e,cy_e)$ 的读数。没有把极限穿过 $D$。∎

**定理 102.4（完整全域排零）。** 对全部原 $Z\in M$，$\mathfrak F(Z)=0$，因此98.6成立。

证明。对 $Z$ 取102.1的 $z,w$，再对这一份全局 $w$ 取102.2的网。102.3分别用于

$$
(c,Y,A)=(z,Z,|Z|),\qquad
(c,Y,A)=(1-z,\mathcal T Z,|\mathcal T Z|),
$$

给

$$
z\mathfrak F(Z)=0,\qquad(1-z)\mathfrak F(\mathcal T Z)=0.
\tag{102.15}
$$

101.2的原反对称交换式是全局准确身份 $\mathfrak F(\mathcal T Z)=-\mathfrak F(Z)$，故另一个中央部分也为零，两者给 $\mathfrak F(Z)=0$。这里相加的是同一已存在输出元素的两份中央投影，不是两份未知输入响应。任意 $Z$ 的101.1坐标遍历全部原标签对，遂给98.6。另一中央对合若也给98.6，限制到任意迹有限角便由 SM79.3唯一性给 $pQ=p\widetilde Q$；$p\uparrow1$ 得 $Q=\widetilde Q$。正向和唯一性完成。∎

102.2–102.14只对已知算子、支撑和正常正读取取极限。若某个中央部分的固定缺陷有非零正规读数，102.14在某个足够大的实际有限投影处就与精确 PB 运输冲突；并不需要未知响应的连续性。全域因子中的二选一已被中央比较与两侧局部读取取代，有限与无限中央混合均在同一个证明内。

## 103. 每个中央取向的反向、静态后果与可积域

**命题 103.1（完整反向）。** 在98.1–98.2的同一原资料上，每个中央自伴对合 $Q$ 按98.6定义的 $D_Q$ 都满足完整98.2。

证明。SM84.1的反向代数论证仅使用中央直和与相反代数，无有限性或因子前件；参数现在取98.7的同一个 $A_Q$。这个代数与 $M$ 具有相同伴随、单位、正锥和范数。对自伴 $a,b$ 有 $a\star b=a\circ b-iD_Q(a,b)$，所以每份原正评价的正复延拓在 $A_Q$ 上的 Cauchy–Schwarz给全部原 P2及双向二表正性。相加三表的实部是同一正实双线性型 $\gamma(a\circ b)$ 的 Gram 表，指定相加向量的平方为零，全部排列也成立。$1^2=1$，而 $0\le y\le\theta1\le1$ 的函数演算给 $y^2\le y$。100.4给任意原三元组的完整 PB。原评价及其所有质量逐份不变；零质量的正泛函恒零，无归一。结合102.4，完成98.3的正反证明。∎

**推论 103.2（识别之后才取得的同一对象结构）。** 同一旧 $D$ 现在实双线性、分别范数及超弱连续，并满足

$$
\begin{gathered}
L_a(X)=[iQa/2,X],\quad L_a(b)=D(a,b),\qquad
\|D(a,b)\|\le\|a\|\|b\|,\\
D(c,a)=0\quad(c\in Z(M)_{\rm sa}),\qquad
D(za,zb)=zD(a,b)\quad(z=z^*=z^2\in Z(M)).
\end{gathered}
\tag{103.1}
$$

证明。直接读98.6，左右乘固定有界元是正规有界线性映射，中央元与交换子交换，给全部断言。中央下降直到此处才成为结论。它不等于任意压缩下降；一般非中央 $p$ 仍不能写 $pD(a,b)p=D(pap,pbp)$，跨补角交换子项并不消失。∎

同一 $\star$ 乘法是98.7。标准关联代数后果及 A32.2、A23.1、A6.3、A7–8的准确消费者给全部原有限复 Gram、$\mathsf P_3$、原 R和忠实保锥等距含单位 Hilbert 表示。明确地，对每个有限 $n$、全部原 $a_1,\ldots,a_n$、全部复系数 $\lambda_1,\ldots,\lambda_n$ 和每份原 $\gamma$，取 $X=\sum_j\lambda_ja_j$，有

$$
\begin{aligned}
\sum_{j,k=1}^n\overline\lambda_j\lambda_k
[\gamma(a_j\circ a_k)-i\gamma D(a_j,a_k)]
&=\gamma(X^*\star X)\ge0,\\
(a\circ b)\circ c-D(D(a,b),c)
&=a\circ(b\circ c)-D(a,D(b,c)).
\end{aligned}
\tag{103.2}
$$

第二式是同一结合乘法的实部；全部嵌套仍是原值。$n=0$、零标签、重复和每份零、不等、次归一质量均保留。表示不自动满射全 $B(H)$，原评价也不因此变成正规评价。

**命题 103.3（迹配对的准确可积域）。** 令

$$
\mathfrak m_\tau=\{c\in M:\tau(|c|)<\infty\}=M\cap L^1(M,\tau).
$$

对全部 $a,b\in M_{\rm sa}$、$c\in\mathfrak m_\tau\cap M_{\rm sa}$，两侧乘积均可积且

$$
\tau(D(a,b)c)=-\tau(bD(a,c)).
\tag{103.3}
$$

证明。$\mathfrak m_\tau$ 是双侧 $*$-理想，故 $Jabc,Jbac,bJac,bJca$ 等均可积；迹循环律和 $J$ 中央给

$$
\tau(D(a,b)c)
=\tfrac12\tau(Jabc-Jbac)
=\tfrac12\tau(bcJa-bJac)
=-\tau(bD(a,c)).
$$

每个有限支撑自伴 $c$ 都在此域，因为 $|c|\le\|c\|p$、$\tau(p)<\infty$。不要求 $a,b$ 可积，也不声称任意三个有界自伴元均可取这份有限复数迹配对；不作 $\infty-\infty$ 运算。这是识别后的后果，不作为共同导子、线性或有限首行的前件。∎

## 104. 完整条件候选、准确来源及综合增量

**定义 104.1（同域完整量子候选）。** 在明确模型类 $\Gamma_{\rm sf,cont}$ 中，完整条件候选为

$$
\Gamma_{\rm sf,cont}+\mathsf H_{\rm orig}+\mathsf{PB}+\mathcal C_{\rm src},
\tag{104.1}
$$

其中 $\mathsf H_{\rm orig}$、PB保留98.2的全部数学量词，$\mathcal C_{\rm src}$ 是105逐项全文及全部纳入的上游量词的共同合取。由98.3、103.2，准确有

$$
\begin{aligned}
&\Gamma_{\rm sf,cont}+\mathsf H_{\rm orig}+\mathsf{PB}+\mathcal C_{\rm src}\\
&\quad\Longleftrightarrow\quad
\Gamma_{\rm sf,cont}+\mathsf H_{\rm orig}+\mathsf P_3+
\mathsf{PB}+\mathcal C_{\rm src}.
\end{aligned}
\tag{104.2}
$$

所以在这个模型类内，旧 $D$ 双线性、全有限复 Gram、P3、R与共同乘法不必另列为独立数学要求。并未计算一般量子起源的最小独立信息量、公理数或实际取得成本。

**命题 104.2（条件消费者的同一参数接回）。** 同一原世界另满足105相应全部实际前件时，A8.2–8.5、A14.2、A25.1、R3 8.2–8.5及其所引消费者，在各自原适用域和全部原量词下成立。

证明。98.7、103.1–103.2供应这些既有定理的同一原静态代数、自伴对象、锥、范数、单位、评价和全部质量。将这一入口代入相应原条件定理即可；联合、过程、仪器、记录和动力前件分别由105提供。要求有限全矩阵局部腿的定理仍只在实际供应该腿时调用，一般 type II 域不直接满足这个前件。正规密度、Kraus、无限记录和物理时间仍分别守原域。未由静态数学推出这些实际前件存在。∎

**定义 104.3（原来源核对与准确复用）。** 以下工具只在列明条件内使用；它们的名称不替代前件。

| 原来源 | 原条件及本组的实际对应 |
| --- | --- |
| 固定 dev23dae 的 SM79.1–84.1，尤其79.3 | 任意完整有限 continuous 自伴原域，给定忠实正规中心值迹，全部原关系及评价质量。99.6用完整 $pMp$、角单位 $p$、规范 $T_p$ 和同一 $D_p$ 精确代入。有限谱窗、完整有限分类及其六反射消费者都是复用，不重新认领。 |
| 固定 dev23dae 的 A50.2、A51.1及其 W108.2–108.3固定源 | 原 P2给同角旧输出闭合；完整原关系和PB逐层限制。99.2只消费这一接口；不新增一般JB Peirce保正性证明，不把同角闭合变成任意压缩律。 |
| 固定公开efef304的 SF89.4；SF90的式(90.1)–(90.6)；SF91.1–91.4及式(91.5)；SF92.2–92.3及式(92.2)–(92.8)；SF93–94、SF96.1 | 块支撑、实际投影PB和有限首行残差方程、实际Cayley、bounded $H/4$ 两步及normal-square预算是已完成纸面工具。100–102逐项核对 $J=iQ$ 的中央性、反自伴性、酉性和平方；100.10替换因子中心排零，102.2替换因子补角比较，102.1、102.15替换全局二选一。没有复制整套II∞运输另计新结果。 |
| Claire Anantharaman、Sorin Popa，[*An introduction to II₁ factors*，作者全文](https://www.math.ucla.edu/~popa/Books/IIunV15.pdf)，Propositions 2.2.1、2.2.4，Theorem 2.4.1，Proposition 2.4.5，Lemmas 2.4.6–2.4.7，Theorem 2.4.8，Proposition 4.2.1，Theorem 5.5.7 | 原文在任意Hilbert空间上的von Neumann代数中给Borel演算、极分解、任意有向网、99.2、中央载体、任意代数的中央投影比较及角中心。99.4与102.2均消费实际代数中的投影。102.1用2.4.8的中央两分，不套因子Corollary 2.4.9。 |
| 同一作者书 Theorem 9.1.2、Proposition 9.1.6、Proposition 9.1.8 | 这些节的前件是具有忠实正规tracial state的代数，不要求因子。每个非零迹有限角已有 $\tau_p$，所以取得其含单位规范中心值迹及等中心迹投影等价。102.5先由实际 $we$ 取得等价，再以中心值迹比较补角；不以等标量迹代替非因子等价。未使用该书§9.2明列的可分中心值权表示，也不需要全局中心值半有限权。 |
| 同一作者书 Definition 2.5.1、Theorem 2.5.5及C*正泛函Cauchy–Schwarz | 正规性针对有界递增网；102.12只读取已知正预算，102.13用中央酉 $J$ 核对两次平方。辅助正规正泛函分离自伴元，不要求原评价正规、存在忠实正规状态或序列穷尽。 |
| Shavkat Ayupov、Farkhad Arzikulov，[*2-local derivations on semi-finite von Neumann algebras*，原文](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0017089512000870)，DOI 10.1017/S0017089512000870，§§2–3 | 原文的半有限工具包括给定忠实正规半有限迹、 $\mathfrak m_\tau$ 双侧理想、合法可积乘积的循环律和迹有限投影网。99.1、103.3只消费这些工具。其主定理另需每对输入同一导子同时实现的2-local前件；本组不借用该主定理生产未知 $D$ 的线性。 |
| Bhat–Nayak–Shankar，[*On products of symmetries in von Neumann algebras*，arXiv:2204.00009v1](https://arxiv.org/pdf/2204.00009v1)，Lemmas 3.5、3.7–3.8、Theorem 3.9 | 原文3.9给type II₁代数内六个symmetries的精确乘积，不限因子。它属于已给SM79–84的有限分类供应；101只消费实际Cayley及有界对数，不把六反射工具重新当半有限全域运输或FR证明。 |
| 固定dev23dae的 A6.3、A7–8、A14.2、A23.1、A25.1、A32.2、A53.1，R3 8.1–8.5、80.1及105所列来源 | 103–104识别原 $D$ 后才接同一个原乘法、有限Gram、R、表示及七项条件消费者。全部实际合同及其原适用域保持；数学迹与正规读数不供应它们。 |

**定义 104.4（新增内容与准确边界）。** 本组的 $\texttt{repo-derived}$ 综合增量集中于三处：99.9–99.11区分局部 $Q_p$ 与中央提升并以同一个旧值、正确角单位和唯一性拼接；100.6–100.10把已完成的实际PB残差方程接到全代数中心性和原支撑，统一排除有限及无限中央余项；102.1、102.5、102.15以中央比较和规范中心迹补酉，对两个完整全局原输入分别作局部正常读取，完成不预付中央下降的极部桥。成熟投影、角中心、中心值迹、半有限迹、极分解、Borel对数、正读取、已刊有限分类及未变的II∞运输步骤均准确归为复用。这里不声称历史优先、文献穷尽或外部开放问题结算。

98.3是以准确SM79.3为前件的完整纸面分类候选；在所述模型与前件内，证明没有留下需另加的FR、未知 $D$ 正则性或下降接口。本组作者论证不构成独立评审，也不是Lean、kernel、摄入或冻结认证。模型类、完整 $M_{\rm sa}$、准确锥和给定半有限迹仍是承重前件；完整原域支付全部投影、Borel标签、原重基及每次嵌套的成员身份。一般JB、type III、混有type I中央项或适当不完备原域的分类不在本定理内。物理七项实际来源和同时供应它们的同一producer仍由105承担；源中其它无轴、经典、不等维和静默分支没有因本组选择一个数学模型类而被删除。数学条件推导与经验实现、可取得性、控制和物理本体主张分别保持边界。

## 105. 七项真实同源物理来源的完整合同

**定义 105.1（七项全文与全部上游量词的共同合取）。** $\mathcal C_{\rm src}$ 完整合取固定公开SF96.1的七项全文，以及固定dev23dae的SM86.1、SM78.2、SM43.2、SM49.1、SM61.1、SM69.1，C199.2、C194.2、C186.1–186.7、C181.3、C171.1–171.7、C160.3、C155.1、C145.1–145.7，PT122.1，A8.3–8.4、A14.2、A25.1、A53.1，R3 8.1–8.5、R3 80.1，W95.2、W116.1及它们逐项纳入的全部上游来源、对象、条件、实现和量词。下列逐项全文展开同源义务；原来源全文仍作为合取项，不被本组数学模型、消费者短表或未列出的默认简化替换。全部“每个”“任意”“所有有限长度／深度”“每个正精度”均在原合同的准确适用域内量化；未定义请求保持未定义。唯一原世界、全部中心、经典、不等维块、无轴和静默分支保持原身份，数学模型选择不删去完整起源任务的其它原分支。

1. **复 Hilbert、可观测量与实际相干叠加。** 同一原 $\Omega$、原 $E/S/D$、跨评价指定配对、具名且可取得的原标签、native、全部原词同一 $q,K,J$、准备父位置 parent、ready 类型、合法控制及实际相干准备，完整保持C171.1及其A8.3–8.4、A14.2、A25.1、R3 8.1–8.5、R3 80.1和原多项式卷87.1的条件。根、静默和零活动分支、所有具名原程序及每份程序自己的词身份一份不少。原门序列及其 $\sigma,t_0$ 保持各自原来源身份。

   在原消费者要求共同全词网络的接口处，沿R3 8.1保留同一个复空间 $V$、第一槽共轭线性的半正定Hermitian型 $K$、全部原 $\xi_\gamma$ 和总集合映射 $J_a:V\to V$。对全部原 $a,b\in E$、全部原 $\gamma\in\mathcal P$、全部 $z,w\in V$，保持

   $$
   \begin{aligned}
   K(\xi_\gamma,J_a\xi_\gamma)&=\gamma(a),\\
   K(J_a z,J_b w)&=K(z,J_{a\circ b}w)-iK(z,J_{D(a,b)}w),\\
   V&=\operatorname{span}_{\mathbb C}
   \{J_{a_1}\cdots J_{a_n}\xi_\gamma:
   n\ge0,\ a_j\in E,\ \gamma\in\mathcal P\},\\
   K(\xi_\gamma,\xi_\gamma)&\le m_\gamma,\\
   K(J_a\xi_\gamma,J_c(J_a\xi_\gamma))&\ge0
   \qquad(c\in C).
   \end{aligned}
   \tag{105.1}
   $$

   首行量化全部原评价与标签，第二行量化全部原标签及全部 $V$ 中向量，最后一行量化全部原 $a,c,\gamma$。原词先按原总映射实际复合，再取有限复线性包；包含零长度和任意有限长度。共同 $K$ 保留全部有限正表和指定跨评价配对，不能改成逐评价的独立核。该式不预付 $J_a$ 线性、$J_0=0$、$J_1=I$；相应可见恢复沿原词消费者。这里原 $q$、全词 $J_a$ 和比较型 $K$ 与99.12的辅助数学 $J,K$ 无身份替换。

   103.2给数学忠实Hilbert表示、原共同乘法和全部有限Gram；它不制造具名实际准备、任意向量制备、全部 $B(H)$ 算子的可取得像、实际相干控制或实际采用这份表示。不能以另选满足同样矩阵等式的替代模型支付指定原共同网络和同源对应。

2. **原态、效果、全部质量与完整 Born 菜单。** 原评价、原事件、准确原效果区间 $[0,1]$、每个实际完整菜单及接受归属必须来自同一原来源。原准备、共同根、实际抽签、mark、$\mathrm C_{12},\mathrm A_{12},\mathrm{BI}_{12}$、预定有限强度尺度、全部P9分支、每个分支独立的 $W_e$、全部原目标、全部原中间切口与固定支持上的全质量，完整保留C171.2、C145.2及A25.1第2行的原量词。互探接口保持其有限维／最小可见与实尺度范围；原强度、原 $q$、中心比较权与概率质量不混同。其它块自己的AS/EC、菜单外OB，以及消费者所需实际忠实二维到三维适配器，均按原合同供应。

   对同一实际完整有限菜单 $\{e_j\}$，只有原事件已绑定、$\sum_je_j=1$ 且 $m_\gamma>0$，才取

   $$
   p_\gamma(j)=\gamma(e_j)/m_\gamma.
   \tag{105.2}
   $$

   条件角菜单只有在原来源实际供应 $\sum_je_j=p$、相应条件化身份及 $\gamma(p)>0$ 时，才取 $\gamma(e_j)/\gamma(p)$。全部零、不等和次归一质量、中心权、中心经典混合、经典不等维块、静默部分及每份未归一原读数均保留，零质量不除法、不删分支。一般无限或非离散菜单的可数可加与正常性仍取第6项的相应扩展来源。

   具名分析词与菜单事件沿原接线和实际读取次序：先原 $g^*$，再原 $d_s^*$，最后共同根。矩阵相同不能交换实际读取顺序，也不合并相同矩阵但不同原程序。数学有限角、$\tau$、正延拓、中央分解及正规正读取均不增加物理准备、效果或菜单。一般无限维原态保持自己的正泛函或已支付前对偶身份，不擅改成有限密度矩阵；GNS向量也不证明另一个指定物理表示中的正规性。

3. **native、真正相关联合与张量。** C171.3、C145.3、A25.1第3行、A53.1及W95.2、W116.1要求的同一个实际非零相关联合完整保持。原全词 $K/J$、交叉零、旧局部乘法、忠实同向交换局部腿、共同实现、联合生成与分离、所需重数、全部真正相关输入、中央对、经典与不等维块、实际复制及每层递归同源参考都仍须原生取得。凡消费者要求局部全矩阵代数，仍须支付该准确前件；一般type II局部腿不能直接代入有限全矩阵张量定理。

   每份所需系统和参考须属于同一个共同来源，不能分别挑选后声称共同生成。相同边缘、分别可达、相同数学取向、两个有限角、辅助共同表示、一个数学张量表示、同一酉轨道或中央谱分支都不供应真正联合，也不自动给出物理子系统身份。98.6只固定同一单域的旧乘法；只有原联合消费者的全部实际条件共同满足，才在其原适用域接回张量识别。重数一或不可约性仍需要原重数条件，不能从存在忠实交换局部腿中免费取得。

4. **typed CP、Kraus 接线与每层整台递归同源参考。** 对每条实际原细分支 $r:A\to B$、每个原合法typed前接和后接、每份输出的每个仍合法未来及每份原评价，保持未归一回溯

   $$
   \gamma_A(\beta_r b)=\gamma_B^r(b),
   \tag{105.3}
   $$

   连同合法反变复合、typed分区、全未来自然性、全部质量运输和原箭头商下降。原合法请求仍须原类型允许，未定义请求不被补成操作。正有界延拓本身不等于CP。CP按原完整同标签单位区间过程比较，或按整台实际箭头可再应用的递归同源二元参考规则取得；每条完整箭头连同系统、整个环境、全部成功／失败／细记录／port／post-port输出及每份完整输出的每个仍合法未来，都在同一规则类中。真正遗忘、实际返回和合法复合箭头也须在此规则类，不能由形式CP制造。

   递归参考路线两端各有共同真实支持 $p_A,p_B$，以及忠实同向交换的系统腿和参考腿，例如

   $$
   i_A:\mathcal A_A\hookrightarrow p_A\mathcal A_{A^+}p_A,
   \quad j_A:M_2\hookrightarrow p_A\mathcal A_{A^+}p_A,
   \quad i_A(1)=j_A(I_2)=p_A,
   \tag{105.4}
   $$

   $B$端同理。三个实际参考投影 $q_1,q_2,q_3$ 与 $I_2$ 实张成 $(M_2)_{\rm sa}$。每次真实接线保持

   $$
   \beta_{r^+}i_B=i_A\beta_r,\qquad
   0\le\beta_{r^+}(j_B(q))\le j_A(q)
   \quad(q\in\{q_t,I_2-q_t:1\le t\le3\}).
   \tag{105.5}
   $$

   intertwining和夹界须在全部原相关正输入、决定锥的全部原联合评价上成立。支持内补保持为支持内补，不变成环境补；两腿不必生成整个环境或整个支持角。下一层系统是整台实际 $r^+$ 的全部响应，包含所有输出和未来，不能只递归原根代码。

   对每条根箭头和每个所需有限 $L$，必须给实际长 $L$ 链；对每个 $k\le L$ 保持忠实嵌入与精确累计支持运输

   $$
   \begin{gathered}
   M_A^k:\mathcal A_{A_0}\otimes M_{2^k}\hookrightarrow\mathcal A_{A_k},\\
   \beta_kM_B^k=M_A^k(\beta_0\otimes\operatorname{id}_{2^k}),\qquad
   P_A^{k+1}=i_{A,k}(P_A^k)\le p_{A,k+1}.
   \end{gathered}
   \tag{105.6}
   $$

   累计真支持不改成新环境单位。任意精度版本保持每个正精度、每个有限深度和精确根身份；固定正误差不足。每个有限长度的实际链不要求一条实际无限链或物理无限张量积；任意多形式参考不能代替完整实际链，也不预设全局旁接函子。

   算子Kraus公式只在准确合格的有限全矩阵域，或另已供应适用正规物理表示、指定前对偶与所需收敛的域消费。一般正规子代数的正常CP对偶不自动成为全 $B(H)$ 上的算子Kraus表示；非有限情形也不自动有可数Kraus和。数学Kraus指标不自动是原细记录或P9分支，其识别须有全过程接线。99–102的投影和酉扩充不供应原箭头、共同参考或CP。

5. **整台仪器、TP、条件更新与 Lüders。** 对每台原实际仪器保留全部原输入运输、完整typed菜单、原接受端、整个环境、所有成功／失败／细记录／port／post-port输出及每份完整输出全部仍合法未来。真正分组遗忘、AC、精确 $N_u$、X/Xs、原平方根词及每份词自己的接受条件完整取C171.5、C145.5、A25.1第5行及其全部原来源；数学存在平方根不等于原可执行平方根词。

   同一原星乘法与正夹心 $a\star c\star a=2a\circ(a\circ c)-a^2\circ c$ 只给代数入口。正次单位只给TNI；TP另需整台原测试的完整typed单位分区，保持每个输出自己的原类型。Lüders另需同一个完整输出的投影效果、像内每条射线保持及完整输出校准；同效果、同概率、统计重复性或另一输出空间中的匹配不代付它。只有严格正的实际输出质量可以归一；失败和零分支连同其类型、记录和所有合法未来都保留。只有原真正粗事件及实际分组接头允许细输出相加，不能只由相同效果推出同一输出。

   密度、迹类、算子Kraus和迹公式仍只在准确合格的有限全矩阵原域，或另已供应适用正规物理表示、指定前对偶与所需收敛的域消费；一般子代数只给自己的前对偶及CP对偶。不得用给定 $\tau$ 抹去细记录、port未来、接受归属或这些表示前件。

6. **全部合法历史、全未来、真遗忘、两侧及逆向真实返回与 CountRead。** 全部合法顺序、自适应和并行历史，每份完整输出的每个仍合法未来，整个环境、参考副本、全部细记录和泄漏，停止、拒绝、销毁，真正分组遗忘，同数两侧真实返回与同数逆向真实返回，均保持C171.6、C145.6、A8.4、A25.1第6行及单位桥原消费者的完整量词。只对原真正粗事件作实际可加；丢弃记录不是实际遗忘。相同数学算子或矩阵不合并不同原程序、实际读取次序、原 $q$ 零集及AC方向。

   CountRead仍绑定读后同一原完整活动输入与它的全部合法未来的实际返回。读后活动ready接头、接受叶活动输出及第一合法消费者、具名分析词到原实际完整菜单和接受端的接线，都须原生供应。负提升两条活路的分别受控实现及相干聚合实现各守原合同，数学负号不制造任何一条活路。原精确正生成 $B$ 与另名闭正生成 $B_{\rm cl}$ 区分。初始取得、指定有限树、被动精确混合解码和已供应CountRead精确表中的支持事件及整支质量、已供应有限返回的数值校准，均只在原平稳、真实同源、同初始版本及各自实际域内消费；既有成果不重新列为缺口，但初始取得或有限分组校准不替代整份后续输出的全未来Return及完整接线。

   无限历史、无限／非离散记录、可数可加、物理正常性、指定前对偶和所需收敛分别取原扩展来源；有限返回数值校准不供应这些前件。完整CountRead若已强迫无限维忠实响应商，不把它截成一个有限自旋角来声称解决全域。数学投影网、正规正读取和有限PB运输不生产物理无限记录，不证明读后真实双向返回，也不把未定义请求变成合法操作。

7. **动力、物理钟、能量、定义域与共同正作用量。** C171.7、C145.7、A25.1第7行的同一旧全域乘法、保持原域的流、实际相位与门序列、同一实际过程内可逆一参数群及实际逆、原物理钟和单位、所需强连续酉实现、生成元定义域、Hamiltonian能量解释、共同仪器、共同作用量及同一个正 $\hbar$ 全部保持。原 $\sigma,t_0,d$、固定域、resolvent及 $3s+r\le1$ 仍按各原来源的参数、设备、定义域和量纲使用；不与本组中央投影、辅助 $J$、有限网或证明参数混同。

   只有这些物理前件齐备，才在相应物理表示和生成元域消费

   $$
   U(t)=e_\star^{-itH/\hbar},\qquad
   i\hbar\frac{d\psi}{dt}=H\psi,\qquad
   i\hbar\dot\rho=[H,\rho]_\star,
   \qquad \dot b=2D(H,b)/\hbar.
   \tag{105.7}
   $$

   向量微分限于自伴生成元定义域，密度微分限于相应迹类可微域；Heisenberg响应守其实际可微观测量域。括号和指数使用识别后的同一 $\star$ 乘法及相应表示，相反取向不能暗中换回环境乘法。103.1只给数学有界内导子，不生产物理时间、可控相位、实际门流、Hamiltonian能量解释、控制成本、一般无界生成元定义域或跨装置共同 $\hbar$。数学酉元、指数参数、谱、辅助随机钟和形式CP均不替代原物理钟与共同尺度。

七项是唯一原世界内相应条件的共同合取，不能让不同项各换一份来源。104.2消费的是条件齐备时已存在的定理；既有条件定理成立与实际前件是否取得必须分开。本组没有构造同一 $\Omega$ 上同时供应七项的物理producer，也不把数学兼容性当作宇宙本体真实性的证明。

## 106. 旧 QM 七行对应及条件几何

**定义 106.1（每行完整合取105的对应全文）。** 下表只定位数学消费者；每行都保留105相应项全文及其全部上游量词，不以一行摘要改写合同。

| 旧 QM 结构 | 本组供应的同一数学入口及既有消费者 | 仍须同源支付的完整实际条件 |
| --- | --- | --- |
| 复 Hilbert、可观测量、相干叠加 | 98.6–98.7、103.2识别同一 $A_Q$，A6.3、A8.1给忠实保锥、保单位、等距表示及全部有限原复Gram | 105第1项：原 $\Omega$/native、全词共同 $q/K/J$ 与跨评价配对、parent/ready、具名取得、合法控制及实际相干准备；表示不自动满射全 $B(H)$ |
| 原态、效果、Born与全部质量 | A7.1、A7.3、A25.1第2行：效果为准确 $[0,1]$，权为 $\gamma(e)$，只对合格实际完整菜单的正质量归一 | 105第2项：每份准备、原事件和接受归属、完整菜单、全部中间切口与固定支持全质量；零、不等、次归一质量、中心权和静默块保持 |
| 真正相关联合、复合与张量 | 同一 $\star$ 乘法进入A53.1、A25.1第3行及W95.2、W116.1的适用联合接口 | 105第3项：同一个非零相关实现、满足原全矩阵条件的忠实同向交换局部腿、联合生成分离、重数、全部相关输入及每个实际参考；中央角不是物理张量因子 |
| 合法过程、typed CP与Kraus | A8.3、A14.2、A25.1第4行以相同原代数、锥和回溯接完整过程比较或整台递归参考 | 105第4项：整台系统环境、全部输出每个合法未来、三实际投影及支持内补、每个所需有限深度和累计支持；Kraus另守准确表示、前对偶及收敛域 |
| 完整仪器、TP、更新与Lüders | A7.3、A8.4、A14.2、A25.1第5行消费同一正夹心和原星乘法 | 105第5项：全输入输出接线、完整typed单位分区、真分组遗忘、接受条件与平方根词；正质量才归一，Lüders另需同一完整输出的像内射线校准 |
| 历史、全未来、记录、遗忘与真实返回 | A8.4、A14.2、A25.1第6行在其合格域消费原合法复合及记录公式 | 105第6项：所有合法历史未来、环境泄漏、两侧和逆向实际返回、CountRead、活动ready和真遗忘；无限非离散记录的可数可加、正常性、指定前对偶另付 |
| 动力、物理钟、能量及共同正 $\hbar$ | 103.1的有界数学导子及A6.3、A14.2、A25.1第7行取得同一静态入口 | 105第7项：原钟、真实可逆流及实际逆、强连续实现、生成元域、Hamiltonian能量、共同仪器与作用量；数学迹、酉元和参数不替代物理尺度 |

**定义 106.2（二元关系的三元提升及简化所在）。** 二元P2约束每份原输出在全部正读数中的预算；同一份PB将这次实际内值绑定到两份共同外层标签。有限角分类不是各自挑一张替代表；同一个 $D$ 在嵌套角内给同一值，使局部中央取向的提升在重叠中央载体上相同，因而形成一个全局 $Q$。第三投影PB再把有限首输入的同一残差迫到全代数中心，而原支撑和 $ht=0$ 排除它。全域端点只保留一份有限支撑Cayley运输；有界两步给实际酉作用，中央比较决定哪一侧读 $Z$、哪一侧读 $JZ^*$。正平方预算在对应中央局部趋零，运输保持的却始终是同一固定旧缺陷。

$q_+M$ 采用给定乘法，$q_-M$ 采用相反乘法；一个共同中央取向决定全部原标签对。在因子中它退化为整体正负号，有限和无限因子结果都是准确特例。本组删去的是factor限制并统一有限／无限中央混合，未删去完整原域、准确锥、原评价、全部质量、给定半有限结构或七项实际来源。三标签、反交换框架和中央两分支都不规定物理空间维数；数学操作的求解相容也不意味着实际测量次序可以交换。

## 107. 一份中央方向与两侧正读取的完整白话

**定义 107.1（原响应怎样在有中心的半有限世界中被认回）。** 问题始终是同一个世界给出的两两有方向比较、相加三角、单位小窗和任意三标签正反配平，能否认回原先未知的整张响应表。这里的明确数学范围是任意半有限continuous算子代数的全部自伴对象：世界可以有很复杂的中心，有些中央部分整体有限，另一些无限，也不要求能用一列有限区域覆盖全体。给定迹只是定位有限预算区域的数学尺，不是实际准备。每个迹有限区域内部仍能无限维；原正预算保证同区域的旧答案仍在该区域，完整原关系也逐层留在里面，所以直接调用已经给定的完整有限分类。

每个有限区域认出的方向是它自己中心里的一个对象。把这个对象提升到原世界对应的中央部分后，才能比较两个区域，不能把局部单位和中央载体混为一谈。小区域放进大区域，同一个不交换输入对仍读同一份旧答案；有限分类的唯一性要求大区域的方向压回小区域恰是原方向。这里并未把小区域里的反射说成整个大区域的反射。任意两个有限区域都能放进一个共同的有限区域，因此这些提升在每份重叠上相容，最后组成一个全世界的中央方向 $Q$。拼接的是已经识别的方向算子，还没有拆分未知响应。

接着必须支付跨越有限区域的输入。先固定任意全域对象 $x$，拿一个有限投影 $p$ 与它比较。二表预算允许旧输出有交叉块，却使它们总共占据某个更大的有限支撑。把 $x,p,0$ 放进同一次原PB，两份真正外表便共同回到一个已认清的有限区域，因而钉死起初那一份输出。这给有限投影对全部原输入的整行。再把投影换成任意有限支撑自伴对象 $h$，把第三标签换成所有有限投影 $d$。两份外表仍共同回到有限区域；和已知交换子配平比较后，同一残差既与 $h$ 的对称乘积为零，又必须和每个有限投影交换。有限区域按有向网扩大后，它只能属于整个代数的中心。原预算还说它在 $h$ 的支撑以外没有块；中心性配合 $ht=0$ 又说它在该支撑以内也不能有块。因此残差为零。这个排零不要求世界是因子，不靠另找一块无限余地，也不会遗漏整体有限的中央部分；没有增加“有限首行已经正确”的新条件。

完整有限首行取得后，把一对原实标签记作 $Z=b+iQd$。PB允许共同重组选定的一对标签，且标准响应之外的那份偏差保持完全相同。重新选取另一份合法原输入，就把这种重组变成实际Cayley作用；一个有限支撑酉元的有界辐角只需取四分之一角，再连续两次这种精确作用。整个过程不从未知函数中提取系数，也不拿稠密性代替连续性；运输的是同一份固定旧偏差。

无限端点需要根据中心选择方向。一个对象的极部分在某些中央部分能补成等距，在其它中央部分则要先交换两个原标签，也就是改读完整的 $JZ^*$。成熟中央比较给这两部分；把对应的等距元接起来，可以得到一份全局等距。在每个真正有限角中，它的有限投影像和原投影已经由同一个部分等距匹配。两个补角必须用规范中心值迹比较才能补成酉元，仅有标量迹相等不足以作非因子比较。如此取得的实际有限支撑酉元按网扩大，便能在第一中央部分把原 $Z$ 的虚部预算压小，在另一部分把原 $JZ^*$ 的虚部预算压小。

这里不把这两份输入混合后送进未知表，也不要求未知表先按中央投影下降。第一侧的正规正读数始终读取完整原 $Z$ 的同一固定偏差，第二侧始终读取完整原 $JZ^*$ 的同一固定偏差。每个有限阶段的精确PB运输让偏差读数保持，原P2却把它限制在越来越小的已知正平方预算里，所以两侧的相应读数只能为零。原反对称性准确连接这两个完整输入：交换两标签只把偏差变号。于是同一原偏差在两个中央部分都为零，所有原标签对的旧响应都被认回为 $iQ[a,b]/2$。线性、连续、中央下降、共同内导子与同一复乘法到这一步才成为结论。

$Q=1$ 的中央部分沿用给定乘法，$Q=-1$ 的部分使用相反乘法，两边保留相同自伴对象、正锥、单位、范数和原读数质量。这给已有静态后端的同一入口：全部有限复Gram、原换括号关系、忠实Hilbert表示、效果和未归一Born权。不把有限预算角当物理子系统，不用辅助迹取代准备；可积迹配对也只用于其中一个标签确实可积的合法域。本文提供的是以给定有限分类为前件的纸面候选证明，作者判断不算独立验证或kernel认证。

完整量子候选仍要求同一原世界同时满足七项实际来源：具名标签、全词共同网络和相干准备；全部Born菜单及零、不等、次归一质量；真正相关联合、合法同向局部腿和所需重数；整台过程与每层实际递归同源参考，覆盖整个环境、所有输出和各自全部未来；完整仪器、接受端、真正遗忘、TP及额外的Lüders校准；所有合法历史、读后同一活动输入、两侧与逆向真实返回、完整CountRead及无限记录的可数可加、正常性和指定前对偶；以及原物理钟、实际可逆动力、能量、生成元域、共同仪器和正作用量。这些来源齐备时，既有量子消费者在各自准确域中成立；数学迹、投影、正规读数、酉元和中央方向没有替原世界制造它们。一般JB、type III、其它类型或不完备原域仍有各自问题，这个完整半有限continuous分类没有代答那些问题，也没有把条件数学统一升级成无前提物理起源。

## 追加锚（本行以下为增补区）
