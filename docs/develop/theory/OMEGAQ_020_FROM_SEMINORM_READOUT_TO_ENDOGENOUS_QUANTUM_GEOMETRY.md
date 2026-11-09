# ΩQ-020：从范数读出到内生量子几何

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。原图以文内文字和公式呈现。

$\Omega Q$-020

从范数读出到内生量子几何

一个较弱输入的完整候选：二元乘性、三元忠实与观察者记录

项目主快照：2026-11-07 21:30:57 UTC；增量核读截止：21:39:03 UTC

**本轮唯一候选。** 原对象只带实线性结构、双线性乘法和半范数读出。 读出非零、乘性、有可读双侧单位，并存在同一对 $a,b$，使

$$
p\bigl((ab-ba)c+a(bc)-b(ac)\bigr)=0\Longrightarrow p(c)=0
\quad(\forall c).
$$

这些条件推出原读出的平行四边形恒等式和内积；同一可读商随后被迫为四元数， 见证对给出内部复结构，得到复二维幅度与 Bloch 球。 本轮将 *内积的预先输入* 移到 *由二元关系证明的输出* 。 六个命名条件组仍为六组，其中一组严格弱化；不声称零输入或语言无关的最小公理数。

**结论范围。**

本稿给出该候选的完整数学分类，并在明确的事件、复合、过程与时钟接口下发展有限量子理论。 观察者、记录、控制与参考可以放入同一个复合模型，但把它们内置不会自动消除源相关、仪器选择和时间标定的条件。 “线、面、时间都是同一存在”在这里分别落实为可检验的类型与等式； 未由这些等式推出的物理识别不写成定理。

<a id="section-1"></a>

## 1　项目进展、研究来源与本轮推进位置

### 1.1　固定版本与相关结构

本轮基准为提交 `840da33992b6`，递归取得理论目录的 1350 份 Markdown， 共 161,580,271 字节，并按 Git blob 校验；这是一份完整目录检索， 并非声称逐段证明审计了全部文稿。 之后在提交 `142923373ceb` 上补读新出现的 OTF-005 与 C139 延续稿； 最终合并索引含 1351 份理论文稿、161,686,413 字节，默认分支为 `dev`。 固定版本链接使以下判断可复查。[\[1\]](#ref-repo)

| 结构 | 已有结论与保留前件 | 本轮使用方式 |
|:---|:---|:---|
| OTF-005 | 给定有限维正定内积与线面对偶要求；区分单态稳定子面与转向面；余弦–相位斜积的精确共轭。 | 将内积放回更前端推导；保留其面积类型和完整反馈边界。 |
| C128 §§16–21 | 在指定自旋/Jordan 背景与 PY、NN 下，一个纯锚的自由 Gram 正性和原左作用零稳定恢复原 $D$ 的双线性，并排除三轴外方向。 | 给出混锚趋边界与同一原作用统一有界的衔接推论，不重计为第二候选。 |
| 小窗口单位桥 §§57–63 | 原 Jordan 图册可带标准/反向混合嵌入；原 $D$ 约束决定其兼容性，不能先假定共同复乘法。 | 提醒复合与同源识别有独立成本。 |
| C139 与 V89、V94 | 全部原参考、允许后续、零关系下降与递归过程正性已有精细合同。 | 有限 CP 完成和观察者菜单只在声明的来源合同内使用。 |
| R5-022、OTF-004 | 余弦固定点、切换政策、内生记录反馈与有限线性提升边界已有结果。 | 本轮重证所需命题，明确新旧归属。 |

上述来源分别见 [\[2\]](#ref-otf5), [\[3\]](#ref-c128), [\[4\]](#ref-jbbridge), [\[6\]](#ref-c139cp), [\[5\]](#ref-c139cont), [\[7\]](#ref-v89), [\[8\]](#ref-r522), [\[9\]](#ref-otf4)。

OTF-005 的 C1 已给正定内积，不能据其后面的球面几何反过来说内积已经无条件内生。 本轮的真正回溯点在更前端：只给半范数，证明每个二元截面必须是欧氏平面。 这与 C128 的“同一个原关系能否在所有第三元上稳定下降”相呼应， 但两条入口的背景和类型不同，不能相加后声称输入更少。

### 1.2　与问题最贴近的外部研究

| 研究线 | 已建立的结果 | 对本问题的用途 |
|:---|:---|:---|
| 绝对值代数 | Rodríguez Palacios (1992) 研究单侧除法绝对值代数，建立内积范数性质；左单位本身还容许无限维实例。 | 内积恢复有成熟数学背景；本稿提供自足证明，并由额外忠实条件选出有限四元数。 |
| 几何量子力学 | 射影态的度量、辛形式和几何相位；现代投影算子微积分统一这些几何量。 | 线长、面积与相位可以来自同一几何，仍需要明确归一化和具体历史。 |
| 波–粒–纠缠 | Ding 等 (2025) 给出资源量之间的守恒关系并有集成光子实验。 | 波粒表现必须把量子记忆和所选读出一并纳入。 |
| 量子擦除推断 | Siddiqui (2026-11-02，预印本) 研究与擦除记录相容的最少纠缠；条件条纹本身不能认证纠缠。 | 区分“看到了什么”与“记录迫使整体具有何种结构”。 |
| 内生时钟与操作 | Baumann–Lock (2026) 比较多个时间参考，强调把操作写入约束及其解的因果一致性。 | 内部时钟与操作都须进入模型，不能仅重命名外部参数。 |

来源为 [\[10\]](#ref-rodriguez), [\[12\]](#ref-ashtekar), [\[13\]](#ref-projector), [\[15\]](#ref-ding), [\[16\]](#ref-siddiqui), [\[23\]](#ref-baumann)。 这些结果共同支持精确的关系模型；它们没有证明“任意面积就是物理时长”或“只凭存在已经唯一得到全部量子物理”。

**证明归属。**

本轮新增的是较弱读出入口与候选的合并推导、混锚统一界的项目衔接， 以及有明确来源条件的读出菜单分类表述。 内积代数理论、Pauli/Born 表示、Choi–Kraus、量子几何、量子擦除与关系钟均有先行研究。 下面给出可独立检查的证明，不作全领域优先权声明，也不把文稿证明称为已获 Lean 形式化认证。

## 目录

- [1　项目进展、研究来源与本轮推进位置](#section-1)
- [2　唯一候选 Q20：纯数学输入–输出区域](#section-2)
- [3　由二元稳定乘法推出内积：完整证明](#section-3)
- [4　同一对比较的三元闭合及四元数分类](#section-4)
- [5　反向删除：哪些条件真正承担了工作](#section-5)
- [6　同一合读结构的几何完成：方向、复幅度与正读出](#section-6)
- [7　线、面积、相位与钟：同一几何的准确分工](#section-7)
- [8　有限量子理论的完整数学完成及实际接口](#section-8)
- [9　内生注意力的可检验边界：一个菜单何时能排除可分替身](#section-9)
- [10　固定点、有限三维提升与完整内部时间](#section-10)
- [11　项目衔接推论：混态序列的统一读出界代替实际纯锚](#section-11)
- [12　全理论账本与本轮白话](#section-12)

<a id="section-2"></a>

## 2　唯一候选 Q20：纯数学输入–输出区域

**签名。**

$$
\Sigma=(\mathcal A,+,\cdot_{\mathbb R},0;m,p),\quad
\mathcal A\in\mathbf{Vect}_{\mathbb R},\quad
m:\mathcal A^2\to\mathcal A,\quad p:\mathcal A\to[0,\infty).
$$

**背景输入。**

$$
\mathsf B_1:\ m\in\operatorname{Bil}_{\mathbb R}(\mathcal A^2,\mathcal A),\qquad xy:=m(x,y),
$$

$$
\mathsf B_2:\quad p(tx)=|t|p(x),\quad p(x+y)\le p(x)+p(y)
\quad(x,y\in\mathcal A,\ t\in\mathbb R).
$$

**原关系输入。**

$$
\begin{aligned}
\mathsf E&:\quad\exists x\quad p(x)>0,\\
\mathsf N&:\quad\forall x,y\quad p(xy)=p(x)p(y),\\
\mathsf U_p&:\quad\exists\varepsilon\ \forall x\quad
p(\varepsilon x-x)+p(x\varepsilon-x)=0,\\
\mathsf F&:\quad\exists a,b\ \forall c\quad
p\bigl((ab-ba)c+a(bc)-b(ac)\bigr)=0\Longrightarrow p(c)=0.
\end{aligned}
$$

$$
\boxed{\mathsf Q_{20}=\mathsf E\land\mathsf N\land\mathsf U_p\land\mathsf F.}
$$

**定义。**

$$
q=p^2,\quad N=p^{-1}(0),\quad A=\mathcal A/N,\quad 1=[\varepsilon],\quad \mathsf U_q:=\mathsf U_p,
$$

$$
k=ab-ba,\quad X(c)=kc,\quad Y(c)=a(bc)-b(ac),\quad T=X+Y,
$$

$$
\mathcal B(x,y)=\tfrac14\bigl(q(x+y)-q(x-y)\bigr),\quad B([x],[y])=\mathcal B(x,y),
$$

$$
W=1^\perp,\quad J=\frac{T}{2\sqrt{q(k)}},\quad h(x,y)=B(x,y)+iB(Jx,y).
$$

**闭合输出。**

$$
q(x+y)+q(x-y)=2q(x)+2q(y),\quad
\mathcal B\in\operatorname{SymBil}_{\mathbb R}(\mathcal A),\quad\operatorname{rad}\mathcal B=N,
$$

$$
\mathcal AN+N\mathcal A\subseteq N,\quad
(A,m,p)\cong(\mathbb H,\cdot,|\cdot|),\quad
\dim_{\mathbb R}A=4,\quad\dim_{\mathbb R}W=3,
$$

$$
q(k)>0,\quad p(Tx-Ty)=2p(k)p(x-y),\quad
q((xy)z-x(yz))=0,
$$

$$
J^2=-I,\quad J^*=-J,\quad J^*J=I,\quad
(A,J,h)\cong\mathbb C^2,\quad \mathbb P(A,J)\cong S^2.
$$

**计数。**

$$
\mathcal I_{\rm bg}=\{\mathsf B_1,\mathsf B_2\},\quad
\mathcal I_{\rm rel}=\{\mathsf E,\mathsf N,\mathsf U_p,\mathsf F\},\qquad
|\mathcal I_{\rm bg}|+|\mathcal I_{\rm rel}|=2+4=6.
$$

$$
\mathsf B_2^{19}\Longrightarrow\mathsf B_2^{20},\qquad
\mathsf B_2^{20}\not\Longrightarrow\mathsf B_2^{19},\qquad
\mathsf B_1+\mathsf B_2^{20}+\mathsf E+\mathsf N+\mathsf U_p
\Longrightarrow\mathsf B_2^{19}.
$$

### 2.1　简化量与类型的准确说明

上一区域中的六组是固定实线性签名下的命名组数。 实数、线性组合、半范数诸条公理以及通常的数学证明基础均仍被使用； 它不是六个独立原子命题的最小性证明。 从 $p$ 定义 $q=p^2$ 并未推出实际概率必须等于 $q$；实际 Born 绑定仍在后续接口中列出。 半范数齐次性已经包含 $q(tx)=t^2q(x)$，本轮移除的是平行四边形与内积极化的预设。

#### 命题 2.1：背景弱化严格

在 $\mathbb R^2$ 上，$p(s,t)=|s|+|t|$ 是范数，但 $q=p^2$ 不是二次型。

**证明。**

齐次性与三角不等式逐坐标成立。取 $u=(1,0),v=(0,1)$，则

$$
q(u+v)+q(u-v)=8\ne4=2q(u)+2q(v).
$$

所以新背景严格弱于旧背景；后文证明它不能同时承载所列乘性与左单位。

$\square$

在同一完整模型类内删除一个可导性质，是本轮的实际压缩； 不能把“改写为定义”当作任意前件已经不存在。 例如把某结构定义成满足 $\mathsf F$ 的对象，并不证明原世界必属于这个结构类。

$\mathsf F$ 比较的是同一对原元产生的 $X(c)$ 与 $Y(c)$，并对全部原第三元量化。 它允许一般幅度相消，也允许实际测量丢失信息。 之后生成的多项式仍在原域中，自动受相同量词约束； 一般事件、记录、概率分布和复合通道则有各自的类型与关系，不能全被强迫成同一个四元数乘性幅度块。

#### 命题 2.2：有限原上下文的零识别

令 $\mathfrak C$ 为由原常量、原实线性组合、带确定括号的原乘法生成的全部有限单变量表达式。 则

$$
x-y\in N\iff p(C(x))=p(C(y))\quad(\forall C\in\mathfrak C).
$$

**证明。**

$N$ 的线性与双边理想性由下一节证明；据此对表达式复杂度归纳。 乘法步用 $x_1x_2-y_1y_2=(x_1-y_1)x_2+y_1(x_2-y_2)$。 反向选择 $C(z)=z-y$。结论只针对声明的读出语言；原档案和其他未下降读口仍须保留。

$\square$

<a id="section-3"></a>

## 3　由二元稳定乘法推出内积：完整证明

本节先不使用忠实条件 $\mathsf F$。$p$ 是原半范数，$q=p^2$；$\mathsf S$ 表示账本中的 $\mathsf B_2$。完成与复化均是证明辅助对象，结论最终拉回同一原域。单侧除法绝对值代数的 Hilbert 范数性质有既有研究；这里给出自足的谱证明，不作历史首创声明。[\[10\]](#ref-rodriguez)

### 3.1　零读出商、完成与左除法

#### 引理 3.1：同一个零读出商

在 $\mathsf S+\mathsf N$ 下，$N=p^{-1}(0)$ 为原乘法双边理想， $p(x+n)=p(x)$ 对 $n\in N$ 成立。因此

$$
A_0:=\mathcal A/N,\qquad \|[x]\|:=p(x)
$$

为实赋范代数，满足 $\|xy\|=\|x\|\|y\|$。 若另有 $\mathsf E+\mathsf U_q$，则 $A_0\ne0$ 且 $1:=[e]$ 为双侧单位， $\|1\|=1$。

**证明。**

三角不等式和绝对齐次性使 $N$ 线性，并给

$$
p(x+n)\le p(x),\qquad
p(x)\le p(x+n)+p(-n)=p(x+n).
$$

乘性给 $p(xn)=p(nx)=0$，所以 $N$ 为双边理想。 双线性保证商乘法良定，原乘性下降为范数乘性。 $\mathsf E$ 保证商非零。可读单位的两个非负零差下降为精确单位律。 选 $x\ne0$，由 $\|ex\|=\|e\|\|x\|=\|x\|$ 得 $\|e\|=1$。

$\square$

#### 引理 3.2：完成只是证明工具

任意实赋范代数 $A_0$ 若满足范数乘性，则其范数完成 $B$ 上存在唯一连续延拓的 实双线性乘法，仍满足范数乘性。原左单位或双侧单位仍是完成中的相应单位。

**证明。**

若 $x_n\to x$、$y_n\to y$，由

$$
\|x_ny_n-x_my_m\|
\le\|x_n-x_m\|\|y_n\|+\|x_m\|\|y_n-y_m\|
$$

知 $x_ny_n$ 为柯西列，且更换逼近序列不改变极限。 定义 $xy:=\lim_nx_ny_n$ 即得唯一连续双线性延拓。 对原乘性和单位律取极限，得到结论。 此处没有向物理系统增添态：后续先在 $B$ 中证明一个恒等式，再限制回原 $A_0$。 尤其不把原忠实性 $\mathsf F$ 未经证明地延拓到 $B$。

$\square$

#### 引理 3.3：一个左单位使全部非零左乘成为满射相似

设 $B\ne0$ 为实 Banach 空间，带实双线性乘法， $\|xy\|=\|x\|\|y\|$，并有左单位 $e$。 则对每个 $x\ne0$，$L_x:y\mapsto xy$ 为可逆有界线性算子，且

$$
\|L_x\|=\|x\|,\qquad \|L_x^{-1}\|=\|x\|^{-1}.
$$

**证明。**

$\|L_xy\|=\|x\|\|y\|$ 先给单射及闭像。 若 $\dim_{\mathbb R}B=1$，单射立即给满射。 以下设维数至少为二。令

$$
G:=\{x\in B\setminus\{0\}:L_x\text{ 满射}\}.
$$

由于 $L_e=I$，$G$ 非空。 若 $x\in G$，则 $L_x^{-1}$ 存在且其范数为 $\|x\|^{-1}$。 当 $\|y-x\|<\|x\|$ 时，

$$
L_y=\bigl(I+(L_y-L_x)L_x^{-1}\bigr)L_x,
\qquad
\|(L_y-L_x)L_x^{-1}\|\le\frac{\|y-x\|}{\|x\|}<1.
$$

由 Neumann 级数 $\sum_{n\ge0}(-R)^n$ 可逆化括号，故 $G$ 相对开。 若 $x_n\in G$ 且 $x_n\to x\ne0$，则对充分大的 $n$， $\|x-x_n\|<\|x_n\|$；使用同一扰动式即得 $x\in G$，所以 $G$ 相对闭。

维数至少为二时，$B\setminus\{0\}$ 路径连通。 事实上，两点之间的直线段若经过零，则选一个不在该共同直线上的点， 用经过该点的两条线段连接即可避开零。 非空开闭集 $G$ 因而等于 $B\setminus\{0\}$。 最后由精确相似律计算 $L_x$ 与其逆的范数，得所列等式。

$\square$

### 3.2　每个二元平面都被迫成为欧氏平面

下面仅构造一个复线性证明辅助空间；它不预先赋予原系统任何复数结构。

#### 引理 3.4：保持相似倍率的复化

对实 Banach 空间 $B$，在 $B_{\mathbb C}:=B\oplus iB$ 上定义

$$
\|u+iv\|_{\mathbb C}
:=\sup_{\theta\in[0,2\pi]}
\|u\cos\theta-v\sin\theta\|.
$$

这给出复 Banach 空间范数。 若 $R:B\to B$ 为满射实线性相似，倍率为 $r>0$，则其复化 $R_{\mathbb C}(u+iv):=Ru+iRv$ 仍为满射相似，倍率同为 $r$。

**证明。**

正定性和三角不等式逐点成立。 乘以 $e^{i\phi}$ 仅把上式中的角度 $\theta$ 平移为 $\theta+\phi$， 故范数具有复绝对齐次性。并且

$$
\max\{\|u\|,\|v\|\}\le\|u+iv\|_{\mathbb C}
\le\|u\|+\|v\|,
$$

所以该范数完备。 相似律直接给

$$
\|Ru+iRv\|_{\mathbb C}
=\sup_\theta r\|u\cos\theta-v\sin\theta\|
=r\|u+iv\|_{\mathbb C}.
$$

实逆算子的复化是复逆，因此满射性也保持。

$\square$

#### 引理 3.5：仅用到的谱事实及证明

设 $X\ne0$ 为复 Banach 空间，$S\in\mathcal L(X)$。 定义

$$
\sigma(S):=\{\lambda\in\mathbb C:\lambda I-S\text{ 无有界双侧逆}\}.
$$

则 $\sigma(S)\ne\varnothing$。 若 $S$ 是倍率为 $r>0$ 的满射相似，则

$$
\sigma(S)\subset\{\lambda:|\lambda|=r\}.
$$

若 $\lambda\in\sigma(S)$、$\alpha,\beta\in\mathbb R$，则 $\alpha\lambda+\beta\in\sigma(\alpha S+\beta I)$。

**证明。**

先证非空。若处处可逆，则 $R(z):=(zI-S)^{-1}$ 为处处解析的算子值函数； 这一解析性来自每一点附近的 Neumann 级数。 当 $|z|>\|S\|$，

$$
R(z)=z^{-1}\sum_{n\ge0}(S/z)^n,
\qquad \|R(z)\|\le\frac1{|z|-\|S\|}.
$$

对任意 $v\in X$ 和连续复线性泛函 $\ell$， $z\mapsto\ell(R(z)v)$ 为在无穷远趋零的有界整函数， 由 Liouville 定理恒为零。连续线性泛函分离点，故 $R(z)=0$， 与 $(zI-S)R(z)=I\ne0$ 矛盾。

对满射相似，$\|S\|=r$、$\|S^{-1}\|=r^{-1}$。 若 $|\lambda|>r$，则对 $\lambda I-S$ 使用外圈 Neumann 级数； 若 $|\lambda|<r$，则

$$
S-\lambda I=S(I-\lambda S^{-1})
$$

可由内圈 Neumann 级数求逆。 所以谱只能在 $|\lambda|=r$ 上。

最后若 $\alpha\ne0$，

$$
(\alpha\lambda+\beta)I-(\alpha S+\beta I)
=\alpha(\lambda I-S)
$$

给出所需非可逆性；若 $\alpha=0$，则 $\sigma(\beta I)=\{\beta\}$。

$\square$

#### 定理 3.6：二元平面欧氏化

设 $B$ 满足引理 3.3 的条件。 任给 $x,y\in B$、$y\ne0$，存在一个复数 $\lambda$，使所有 $\alpha,\beta\in\mathbb R$ 同时满足

$$
\boxed{\quad
\|\alpha x+\beta y\|^2
=\|y\|^2\,|\alpha\lambda+\beta|^2.
\quad}
\tag{P}
$$

因此原范数满足平行四边形恒等式。

**证明。**

令 $S:=L_xL_y^{-1}$，并按引理 3.4 将其复化。 选取一个 $\lambda\in\sigma(S_{\mathbb C})$。 对实数 $\alpha,\beta$，双线性给原实算子等式

$$
\alpha S+\beta I=L_{\alpha x+\beta y}L_y^{-1}.
$$

若 $\alpha x+\beta y\ne0$，引理 3.3 使右式成为 倍率

$$
r_{\alpha,\beta}=\frac{\|\alpha x+\beta y\|}{\|y\|}
$$

的满射相似。复化保留此倍率，而 $\alpha\lambda+\beta$ 属于其谱，因此谱圆结论给 $|\alpha\lambda+\beta|=r_{\alpha,\beta}$。 若 $\alpha x+\beta y=0$，对应算子为零，其谱仅为 $\{0\}$， 所以 $\alpha\lambda+\beta=0$；同一公式仍成立。 这证明 (P)。

由 (P) 对 $(\alpha,\beta)=(1,1),(1,-1),(1,0)$ 使用同一个 $\lambda$，得

$$
\begin{aligned}
\|x+y\|^2+\|x-y\|^2
&=\|y\|^2\bigl(|\lambda+1|^2+|\lambda-1|^2\bigr)\\
&=2\|y\|^2(|\lambda|^2+1)
=2\|x\|^2+2\|y\|^2.
\end{aligned}
$$

$y=0$ 时该式直接成立。 若 $x,y$ 独立，$\operatorname{Im}\lambda\ne0$，否则 $(\alpha,\beta)=(1,-\lambda)$ 会使一个非零实线性组合的范数为零。 故独立二元张成的平面等距于通常的欧氏平面。

$\square$

#### 引理 3.7：极化双线性无需再次输入

设实范数 $\|\cdot\|$ 满足平行四边形恒等式。则

$$
B(x,y):=\frac14\bigl(\|x+y\|^2-\|x-y\|^2\bigr)
$$

为实内积，并满足 $B(x,x)=\|x\|^2$。

**证明。**

记 $Q(x)=\|x\|^2$。$Q$ 偶性给 $B(x,y)=B(y,x)$， 且 $B(0,y)=0$、$B(x,x)=Q(x)$。 将平行四边形恒等式分别应用于 $(x+y,z)$ 与 $(x-y,z)$，相减得

$$
B(x+z,y)+B(x-z,y)=2B(x,y).
$$

取 $z=x$ 得 $B(2x,y)=2B(x,y)$。 再令 $x=(u+v)/2$、$z=(u-v)/2$，得到

$$
B(u,y)+B(v,y)=2B((u+v)/2,y)=B(u+v,y).
$$

于是第一槽可加，继而有有理数齐次性。 由于范数连续，$B$ 连续；对有理数序列取极限得到实数齐次性。 对称性再给第二槽线性。 最后 $B(x,x)=\|x\|^2>0$ 对 $x\ne0$ 成立，故为内积。

$\square$

#### 推论 3.8：恢复的是原 $q$

在实双线性乘法、$\mathsf S+\mathsf E+\mathsf N+\mathsf U_q$ 下，

$$
q(x+y)+q(x-y)=2q(x)+2q(y)
$$

对原 $\mathcal A$ 的所有 $x,y$ 成立，并且

$$
\mathcal B(x,y):=\frac14\bigl(q(x+y)-q(x-y)\bigr)
$$

为半正实双线性型，$\mathcal B(x,x)=q(x)$， $\operatorname{rad}\mathcal B=N$。 此结论的证明只使用 $\mathsf U_q$ 中的左单位部分。

**证明。**

依次构造 $A_0$ 及其完成 $B$，在 $B$ 中用上面两条定理得到平行四边形和内积。 将恒等式限制回 $A_0$，再经原商映射拉回 $\mathcal A$，得到所列原函数公式。 核为 $N$，因为商中内积正定。 整个过程没有改变原乘法、原 $q$ 或原零读出等价关系。

$\square$

证明采用通常实、复分析，包括 Neumann 级数、Liouville 定理，以及 Hahn–Banach 的连续泛函分离结论。这些属于明示数学基础；谱证明中的辅助 $i$ 并非原物理幅度已经拥有复结构。原幅度的复结构在下一节由原见证对导出。

<a id="section-4"></a>

## 4　同一对比较的三元闭合及四元数分类

上一节已经由较弱半范数背景恢复原半正二次型。以下始终在原商 $A=\mathcal A/N$ 上工作，不向辅助完成延伸 $\mathsf F$。全部使用的投影恒等式在此重新证明。

#### 引理 4.1：忠实合成自动产生同一对非交换见证

候选中的同一对 $a,b$ 必满足 $q(k_{a,b})>0$。

**证明。**

在正定商中，单位律给

$$
T_{a,b}(1)=(ab-ba)+ab-ba=2k_{a,b}.
$$

若 $q(k_{a,b})=0$，则 $q(T_{a,b}(1))=0$，忠实性迫使 $q(1)=0$， 与 $q(1)=1$ 矛盾。 这也说明原 $q$ 非零不可删除，否则 $\mathsf F$ 会真空成立。

$\square$

### 4.1　只由单位与乘性恢复的代数恒等式

以下在任意非零实正内积空间 $A$ 上工作，乘法双线性且有单位 $1$， 满足 $q(xy)=q(x)q(y)$。仍不假定有限维或结合性。 令

$$
L_x(y):=xy,\quad R_x(y):=yx,\quad
t(x):=B(1,x),\quad \bar x:=2t(x)1-x,\quad W:=1^\perp.
$$

#### 引理 4.2：共轭、交替性与纯方向 Clifford 关系

对全部 $x,y,z\in A$，

$$
B(xy,z)=B(y,\bar xz),\quad
B(yx,z)=B(y,z\bar x),
$$

$$
L_{\bar x}L_x=L_xL_{\bar x}=q(x)I,\qquad
R_{\bar x}R_x=R_xR_{\bar x}=q(x)I,
$$

$$
x^2-2t(x)x+q(x)1=0,\qquad L_x^2=L_{x^2},\quad R_x^2=R_{x^2}.
$$

对 $x,y\in W$，

$$
x^2=-q(x)1,\quad xy+yx=-2B(x,y)1,
$$

$$
L_x^2=-q(x)I,\qquad L_xL_y+L_yL_x=-2B(x,y)I.
$$

**证明。**

单位非零且 $q(1)=q(1)^2$，故 $q(1)=1$。 比较 $q((1+sx)y)=q(1+sx)q(y)$ 关于 $s$ 的一次项，再对 $y$ 极化， 得 $B(xy,z)=B(y,(2t(x)1-x)z)$。右槽同理。 极化 $q(xy)=q(x)q(y)$ 得 $B(xy,xz)=q(x)B(y,z)$。 与配对伴随合用并由正定性消去配对，得 $L_{\bar x}L_x=q(x)I$。 由于 $L_{\bar x}=2t(x)I-L_x$，两个左乘算子交换；右乘同理。 所以 $L_x^2-2t(x)L_x+q(x)I=0$。作用于单位给元素二次式， 将该元素式左乘线性化即得 $L_x^2=L_{x^2}$；右式相同。 纯方向有 $t(x)=0$；分别将其元素平方和左乘平方对 $x+y$ 极化，即得所列反交换关系。 全程伴随均以显式配对给出，没有调用有限维 Riesz 表示。

$\square$

### 4.2　主恒等式：合成读出本来就是内部四维投影

#### 定理 4.3：单对内生投影与反射公式

在上节背景中，给定任意不交换对 $a,b$，令

$$
k=ab-ba,\qquad M=[L_a,L_b],\qquad T=L_k+M,
\qquad \mathscr A_{a,b}=L_{ab}-L_aL_b.
$$

则由同一对内生生成一个四维四元数子代数 $H$，其正交投影 $P$ 与补投影 $Q=I-P$ 满足

$$
\boxed{M=L_k(2P-I),\quad T=2L_kP,\quad\mathscr A_{a,b}=L_kQ.}
$$

特别地，

$$
\boxed{P=-\frac{L_kT}{2q(k)},\qquad
P(c)=-\frac{k\,\bigl(kc+a(bc)-b(ac)\bigr)}{2q(k)}.}
$$

每个括号均如式中所写。这个公式由原乘法、实标量与原读数在同一可读商上下降得到。

$$
\operatorname{ran}T=H,\qquad \ker T=H^\perp,
\qquad\operatorname{rank}_{\mathbb R}T=4.
$$

算子 $K:=2P-I$ 为正交自伴反射；$K=+I$ 于 $H$，$K=-I$ 于 $H^\perp$。

**证明。**

写 $a=\alpha1+x$、$b=\beta1+y$，其中 $x,y\in W$。 若 $x,y$ 线性相关，则 $a,b$ 交换，故两纯部独立。 Gram–Schmidt 给正交单位纯方向 $u,v$ 及 $r,h>0$、$s\in\mathbb R$，使

$$
a=\alpha1+ru,\qquad b=\beta1+su+hv.
$$

令 $w=uv$。配对恒等式与乘性给 $q(w)=1$ 及 $w\perp1,u,v$。 由左右交替性和纯方向反交换，

$$
u^2=v^2=w^2=-1,\quad uv=w=-vu,\quad
uw=-v,\quad wu=v,\quad wv=-u,\quad vw=u.
$$

因此 $H=\operatorname{span}\{1,u,v,w\}$ 为四维四元数子代数。 此处只建立 $H$ 内的乘法表，未把 $L_uL_v$ 误认作整个 $A$ 上的 $L_w$。

定义整个 $A$ 上的算子

$$
K:=-L_wL_uL_v.
$$

三个纯方向左乘平方均为 $-I$，且两两反交换。 因此 $K$ 与 $L_u,L_v,L_w$ 分别交换。 又

$$
K1=-w(uv)=-w^2=1,
$$

故 $K$ 在 $1,u,v,w$ 上均为恒等，因而在 $H$ 上为 $+I$。

若 $z\perp H$，则 $z\in W$ 且 $L_z$ 与 $L_u,L_v,L_w$ 分别反交换。 三次翻号给

$$
KL_z=-L_zK.
$$

作用于单位便得 $Kz=-z$。 任意 $c\in A$ 都可减去在这四个正交单位向量上的有限投影，故 $A=H\oplus H^\perp$，不需预给维数或完备性。 显式地，$P(c)=B(1,c)1+B(u,c)u+B(v,c)v+B(w,c)w$。 所以 $K=2P-I$，它是正交自伴反射。

左乘 $L_w$ 于 $K=-L_wL_uL_v$ 得

$$
L_uL_v=L_wK.
$$

双线性展开给

$$
k=2rh\,w,\qquad
M=rh[L_u,L_v]=2rhL_uL_v=L_kK.
$$

因此 $T=L_k(I+K)=2L_kP$。 再令 $F(x,y)=L_xL_y-L_{xy}$。 它双线性，$F(1,y)=F(x,1)=F(x,x)=0$，所以

$$
\mathscr A_{a,b}=-F(a,b)
=-rh(L_uL_v-L_w)
=rhL_w(I-K)=L_kQ.
$$

$k$ 为纯方向且 $q(k)>0$，故 $L_k^2=-q(k)I$， 给出显示的内生投影公式。 $L_k$ 可逆并保持 $H$ 和 $H^\perp$（因 $K$ 与 $L_w$ 交换）， 所以 $\operatorname{ran}T=H$、$\ker T=H^\perp$，秩恰为四。

$\square$

#### 推论 4.4：二元响应的精确正分解

对所有 $c,d\in A$，

$$
q(Tc)=4q(k)q(Pc),\qquad
q(\mathscr A_{a,b}c)=q(k)q(Qc),
$$

$$
B(Tc,\mathscr A_{a,b}d)=0,
$$

$$
\boxed{q(Tc)+4q(\mathscr A_{a,b}c)=4q(k)q(c).}
$$

两条被比较的响应 $X=L_k$、$Y=M$ 有同样预算：

$$
q(Xc)=q(Yc)=q(k)q(c).
$$

其中 $Yc=Xc$ 在 $H$ 上成立，而 $Yc=-Xc$ 在 $H^\perp$ 上成立。

**证明。**

使用 $T=2L_kP$、$\mathscr A=L_kQ$、$M=L_kK$，以及 $B(L_kx,L_ky)=q(k)B(x,y)$、$P\perp Q$ 即得。

$\square$

**图示（文字版）。** 从 $c=Pc+Qc$ 出发，上支经 $P$ 得到 $Pc\in H$，两份响应同向，合读为 $Tc=2L_kPc$；下支经 $Q=I-P$ 得到 $Qc\in H^\perp$，两份响应反向，由结合缺口读出 $\mathscr A c=L_kQc$。

**图 1。** 同一第三元的正交分解。上支由合读 $T$ 读出；下支在合读中抵消，由结合缺口 $\mathscr A$ 精确读出。忠实条件排除下支中的非零可读元。

#### 定理 4.5：一对忠实合成的完整分类

在本轮固定原半范数签名中，$\mathsf N+\mathsf U_q+\mathsf E+\mathsf F$ 成立， 当且仅当 $N=q^{-1}(0)$ 为双边理想，且由同一原乘法与同一原读数下降得到的 $\mathcal A/N$ 等距代数同构于标准四元数 $\mathbb H$。 此时原候选对已经不交换，商上的全部三元精确结合，原层全部结合缺口具有零读数。

**证明。**

正向，上一节的半范数商和内积恢复给非零正定幺商，$\mathsf F$ 下降为 $T$ 的单射性。 在单位上计算 $T1=2k$，故 $k\ne0$，投影定理可用。 但 $\ker T=H^\perp$，因此 $H^\perp=0$，全部商就是四维 $H$。 全局商结合性及原层零结合缺口随即成立。

反向，若同一商等距同构于 $\mathbb H$，选择 $1,i,j$ 的原代表作为 $\varepsilon,a,b$。 四元数范数给乘性，可读单位成立且读数非零。 结合性给 $T(c)=2k c$，其中 $k=2k_{\mathbb H}$ 非零。 所以 $q(Tc)=4q(k)q(c)$，得到原层忠实条件。

$\square$

#### 推论 4.6：新产生的过程也满足有限二元、三元闭合

在内生投影定理的背景中，

$$
T^2=-4q(k)P,\quad T^3=-4q(k)T,\qquad
\mathscr A_{a,b}^2=-q(k)Q,\quad
\mathscr A_{a,b}^3=-q(k)\mathscr A_{a,b}.
$$

定义 $J:=T/(2\sqrt{q(k)})$，则

$$
J^2=-P,\qquad J^3=-J,\qquad J^*J=P.
$$

若候选忠实条件成立，则 $P=I$，故

$$
J^2=-I,\qquad J^*=-J,\qquad J^*J=I.
$$

并且原层任意二元差满足

$$
\boxed{q(Tx-Ty)=4q(k)q(x-y).}
$$

**证明。**

$P,Q$ 与 $L_k$ 交换，而 $L_k^2=-q(k)I$，故各算子乘积直接得出。 忠实性给 $P=I$。最后把尺度公式应用于 $x-y$，并使用 $T$ 的原实线性性。

$\square$

#### 命题 4.7：由同一对内生的复二维表示

在正定可读商中，忠实比较给出的 $J$ 定义复标量作用

$$
(s+it)x:=sx+tJx.
$$

若约定第二槽复线性，则

$$
h(x,y):=B(x,y)+iB(Jx,y)
$$

是正定 Hermitian 内积，$h(x,x)=q(x)$，且 $\dim_{\mathbb C}A=2$。

**证明。**

$J^2=-I$ 保证复标量乘法律。$`J^*=-J`$ 给共轭对称性；

$$
h(x,Jy)=B(x,Jy)+iB(Jx,Jy)
=-B(Jx,y)+iB(x,y)=i h(x,y).
$$

实双线性性给其余标量律。$B(Jx,x)=0$，所以 $h(x,x)=q(x)>0$ 对非零 $x$ 成立。 实维四意味着复维二。

$\square$

这个 $J$ 是原左乘 $L_{k/\sqrt{q(k)}}$。 若把 $J$ 用作复标量，$e^{tJ}$ 就是该复结构的相位圆，射影化后作用为恒等；不能同时称其为必然的可观测时钟。 下文统一采用此处的左复标量约定；实际可转向的酉作用由与之交换的右乘给出。

#### 推论 4.8：存在、反向与逆的正读数

在该可读商中，每个 $x\ne0$ 都有双侧逆

$$
x^{-1}=\frac{\bar x}{q(x)},\qquad
q(x^{-1})=\frac1{q(x)}>0,\qquad q(-x)=q(x)>0.
$$

因此按 $q(x)>0$ 定义可读存在时，反向和取逆都不产生负存在； 取逆是非零可读元素集合上的对合双射。

**证明。**

元素二次式给 $x\bar x=\bar x x=q(x)1$， 而 $q(\bar x)=q(x)$ 由共轭定义与极化直接得到。 结合性给显示的双侧逆；平方齐次性给其读数和 $q(-x)=q(x)$。 逆的唯一性给 $(x^{-1})^{-1}=x$。

$\square$

<a id="section-5"></a>

## 5　反向删除：哪些条件真正承担了工作

#### 反例 5.1：删除忠实条件：八元数的尖锐边界

令 $\mathbb O=\mathbb H\oplus\mathbb H$，乘法为

$$
(a,b)(c,d)=(ac-\bar d b,\;da+b\bar c),\qquad q(a,b)=|a|^2+|b|^2.
$$

四元数平方展开及实部循环性给

$$
|ac-\bar d b|^2+|da+b\bar c|^2=(|a|^2+|b|^2)(|c|^2+|d|^2),
$$

故其范数确实乘性。取 $a=(i,0)$、$b=(j,0)$、$c=(0,1)$。 则 $k=ab-ba=(2k_{\mathbb H},0)$，

$$
X(c)=(0,2k_{\mathbb H}),\qquad
Y(c)=(0,-2k_{\mathbb H}),\qquad T(c)=0,
$$

而 $q(c)=1$，$q(k)=4$，且

$$
(ab)c-a(bc)=(0,2k_{\mathbb H}).
$$

因此缺口比恰为一，证明严格阈值不能放宽成 $\le1$。 同一对生成的所有有限代数表达式都在 $\mathbb H\oplus0$ 内； 在该子代数上 $T=2L_k$ 忠实。只检验自生成的小域会漏掉 $c$。

#### 反例 5.2：删除存在性

取任意实双线性代数和 $q\equiv0$。其他三组关系均真，$\mathsf F$ 真空成立， 但可读商为零。故存在性不能被没有非零域的条件蕴含偷偷代替。

#### 反例 5.3：即使保留左单位，右单位仍不可删除

在实空间 $\mathbb C$ 上定义 $x\star y=\bar x y$，$p(x)=|x|$。 乘法实双线性，范数乘性，$1$ 是左单位。取 $a=1,b=i$，则

$$
k=a\star b-b\star a=2i,\quad
Y(c)=a\star(b\star c)-b\star(a\star c)=0,\quad T(c)=-2ic.
$$

所以 $T$ 全域忠实。右单位只能是 $1$，但 $i\star1=-i\ne i$。 该商实维二，不是四元数原乘法。 因此范数恢复只需要左单位，不意味着最终候选也可删除右单位。

#### 反例 5.4：删除乘性

令 $A=M_3(\mathbb R)$，通常乘法，$q(X)=\operatorname{Tr}(X^{\mathsf T}X)/3$。 取 $a=E_{12}+E_{23}$、$b=E_{21}+2E_{32}$，则

$$
k=ab-ba=\operatorname{diag}(1,1,-2)
$$

可逆。结合性给 $T(c)=2kc$，所以 $T$ 忠实；正性、单位、存在均成立。 但是 $q(E_{12}E_{21})=1/3\ne1/9=q(E_{12})q(E_{21})$。 可读维数九，不能得到本结论。

#### 反例 5.5：删除半范数背景

在通常 $\mathbb H$ 上取 $q_p(x)=|x|^p$，$p>0$ 且 $p\ne2$。 其余全部关系仍成立，$T=4L_k$ 忠实，但原读数不具有二次齐次性。 其平方根不满足所列半范数齐次性；所以平方指数仍由半范数背景支付；不能由非负、存在与本轮忠实条件单独推出。

#### 反例 5.6：删除原双线性：一个连续例子

在通常四元数实空间及通常平方范数上，令

$$
\phi(t)=\frac\pi4t(t-1),\qquad s(x)=e^{i\phi(\operatorname{Re}x)},
\qquad x\star y=x\,s(x)^{-1}ys(x).
$$

范数乘性成立，且 $1\star y=y$、$x\star1=x$。 对纯方向 $i,j,2k$，均有 $s(x)=1$，所以同一见证 $a=i,b=j$ 仍给 $T=4L_k$ 忠实。 然而 $s(2)=i$，故

$$
2\star j=-2j\ne2(1\star j),
$$

原乘法不对原实线性结构双线性。

#### 反例 5.7：原算子等式只能模同一读出核成立

取原代数 $\mathcal A=\mathbb H\times M_3(\mathbb R)$，逐分量通常乘法， $q(h,X)=|h|^2$。令

$$
A_0=E_{12}+E_{23},\qquad B_0=E_{21}+2E_{32},\qquad
K=[A_0,B_0]=\operatorname{diag}(1,1,-2),
$$

并取原见证 $a=(i,A_0)$、$b=(j,B_0)$。 全部候选条件成立，$N=0\times M_3(\mathbb R)$，$q([a,b])=4$。 但是原合成算子为

$$
\mathcal T(h,X)=(4k_{\mathbb H}h,\,2KX).
$$

所以

$$
(\mathcal T^3+16\mathcal T)(0,I)
=(0,8K^3+32K)\ne0.
$$

原投影表达式在矩阵分量上的作用是 $X\mapsto-K^2X/4$，也不精确幂等。 这些算子差的读数仍为零；商上的 $T^3=-16T$ 与 $P^2=P$ 均准确成立。 这说明原层与可读商的区别有真实反例，不能省略。

这些反例分别否定指定删除后的蕴含；并不声称六组条件构成某个语言无关的最小公理基。

<a id="section-6"></a>

## 6　同一合读结构的几何完成：方向、复幅度与正读出

本节只使用主定理已得的

$$
A=\mathcal A/N\cong\mathbb H,\qquad
B(x,y)=\operatorname{Re}(\bar x y),\qquad q(x)=B(x,x),\qquad W=\mathbf 1^\perp.
$$

原单位类、原乘法与原二次读数均保持不变。以下定义及定理不是第二个候选公理。 记 $L_ax=ax$、$R_ax=xa$；算子复合从右向左作用，故 $R_aR_b=R_{ba}$。始终用 $H_J$ 表示复幅度空间，用 $W$ 表示实三维方向空间。

### 6.1　三维叉积、面积与二元关系的三元返回

#### 定义 6.1：同一乘法的对称部分与反对称部分

对 $x,y,z\in W$ 定义

$$
x\times y:=\frac{xy-yx}{2},\qquad
\nu(x,y,z):=B(x\times y,z).
$$

#### 定理 6.2：二元长度、面积与三元返回

对全部 $x,y,z\in W$，有

$$
\begin{aligned}
xy&=-B(x,y)\mathbf 1+x\times y,
\end{aligned}
\tag{6.1}
$$

$$
\begin{aligned}
B(x\times y,x)&=B(x\times y,y)=0,
\end{aligned}
\tag{6.2}
$$

$$
\begin{aligned}
q(x\times y)&=q(x)q(y)-B(x,y)^2,
\end{aligned}
\tag{6.3}
$$

$$
\begin{aligned}
x\times(y\times z)&=B(x,z)y-B(x,y)z,
\end{aligned}
\tag{6.4}
$$

$$
\begin{aligned}
(x\times y)\times z&=B(x,z)y-B(y,z)x.
\end{aligned}
\tag{6.5}
$$

三线性型 $\nu$ 交替；$\times$ 满足 Jacobi 恒等式。

**证明。**

纯方向反交换关系 $xy+yx=-2B(x,y)\mathbf 1$ 给式 (6.1)。 共轭反转乘法次序，故 $x\times y\in W$。 原配对伴随恒等式给

$$
B(xy,x)=q(x)B(y,\mathbf 1)=0,\qquad
B(xy,y)=q(y)B(x,\mathbf 1)=0.
$$

标量部分与 $W$ 正交，得到式 (6.2)。 将乘性二次型分成这两个正交部分，得到

$$
q(x)q(y)=q(xy)=B(x,y)^2+q(x\times y),
$$

即式 (6.3)。 取主定理中的正交单位基 $u,v,w=uv$。原乘法表给 $u\times v=w$、$v\times w=u$、$w\times u=v$，反序取负。 对三个变量作实三线性展开，即得两条三元返回式。 同一张表给 $\nu(u,v,w)=1$ 并在交换任意两槽时变号，故 $\nu$ 交替。 式 (6.4) 的循环和为零，得到 Jacobi 恒等式。

$\square$

这是四元数纯部的标准三维几何；本轮的推进在于先从半范数关系恢复内积，再用同一对忠实合读取得该原代数。 R5-022 已从另一种三元返回入口研究同一三维结果。[\[11\]](#ref-baez), [\[8\]](#ref-r522)

#### 推论 6.3：归一化二元二次式

若 $r,s\in W$ 为单位方向，则

$$
q(\alpha r+\beta s)
=\alpha^2+2B(r,s)\alpha\beta+\beta^2,
\qquad -2\le2B(r,s)\le2.
$$

当 $r\perp s$ 时，$q(\alpha r+\beta s)=1$ 的全部解构成平面圆； 一个已指定的非零直角三角形归一化只确定其中一个点。

**证明。**

极化恒等式给二次式，Cauchy–Schwarz 给系数范围。 正交时归一方程为 $\alpha^2+\beta^2=1$， 映射 $(\alpha,\beta)\mapsto\alpha r+\beta s$ 是平面的等距映射。 给定两条直角边的长度并除以斜边，只给这个方程的一组解。

$\square$

#### 命题 6.4：由原乘法导出的各向同性与半角

单位集合 $\mathcal U=\{u\in A:q(u)=1\}$ 是群。 共轭 $\operatorname{Ad}_u(x)=ux\bar u$ 在 $W$ 上保持 $B$ 与 $\times$， 其像恰为 $\operatorname{SO}(W,B)$，核为 $\{\pm\mathbf 1\}$。 若 $n\in W$ 为单位，$u=\cos(\theta/2)\mathbf 1+n\sin(\theta/2)$，则

$$
\operatorname{Ad}_u(x)=\cos\theta\,x
+(1-\cos\theta)B(n,x)n+\sin\theta\,(n\times x).
$$

**证明。**

原乘性和 $u^{-1}=\bar u$ 给群律。 共轭保持乘法、单位、共轭与 $q$，所以保持 $W,B,\times$。 把 $x$ 分成 $B(n,x)n$ 与垂直分量，使用纯部反交换式展开 $ux\bar u$，即得显示公式。每个单位四元数均可写成所示半角形式， 故所得作用是定向正交变换。 反之，三维实定向正交变换必有本征值 $1$：非实本征值成共轭对， 实本征值为 $\pm1$，行列式为一。其固定轴的正交平面上是二维旋转， 因而由显示公式实现。若共轭固定全部纯部，则 $u$ 与三个纯基元交换； 原乘法表迫使 $u$ 为实标量，单位范数再给 $u=\pm\mathbf 1$。

$\square$

### 6.2　忠实合读直接给出左复标量

沿用候选的同一对见证，令

$$
k=[a,b],\qquad e=\frac{k}{\sqrt{q(k)}},\qquad
J=\frac{T_{a,b}}{2\sqrt{q(k)}}=L_e.
$$

前文已得 $q(k)>0$、$e\in W$、$q(e)=1$，以及 $J^2=-I$、$`J^*=-J`$、$`J^*J=I`$。

#### 定义 6.5：内部复标量与幅度比较

以内部平面 $\mathbb C_e=\operatorname{span}_\mathbb R\{\mathbf 1,e\}$ 表示复数，规定

$$
(\alpha+i\beta)x:=\alpha x+\beta Jx,
\qquad h(x,y):=B(x,y)+iB(Jx,y),\qquad H_J=(A,J,h).
$$

这里的 $i$ 从左作用；下文的 $h$ 第一槽共轭线性、第二槽线性。

#### 定理 6.6：复二维幅度与完整复线性算子空间

$H_J$ 是复二维 Hilbert 空间，$h(x,x)=q(x)$。 记 $R_A=\{R_a:a\in A\}$，则有实线性直和

$$
\boxed{\operatorname{End}_{\mathbb C}(H_J)=R_A\oplus J R_A.}
$$

其共轭伴随为

$$
(R_a+JR_b)^*=R_{\bar a}-JR_{\bar b}.
$$

**证明。**

$J$ 反自伴给共轭对称性，并给

$$
h(Jx,y)=-ih(x,y),\qquad h(x,Jy)=ih(x,y).
$$

又 $h(x,x)=B(x,x)>0$ 对 $x\ne0$ 成立。 选单位 $f\in W$、$f\perp e$，则 $\{\mathbf 1,f\}$ 为复正交基： 其复张成是实基 $\mathbf 1,e,f,ef$ 的张成，两个基向量的 $h$ 配对为零。 因而复维二，有限维保证完备。

结合性使每个 $R_a$ 与 $J$ 交换，故两类算子均复线性。 若 $R_a=JR_b$，在 $\mathbf 1$ 上作用得 $a=eb$，于是 $(xe-ex)b=0$ 对全部 $x$ 成立。 若 $b\ne0$，右乘 $b^{-1}$ 得 $xe=ex$ 对全部 $x$ 成立， 这与取 $x=f\perp e$ 矛盾。因此 $a=b=0$，直和实维八。 $\operatorname{End}_{\mathbb C}(H_J)$ 的实维也是八，故该直和为全部算子空间。 原配对伴随式给 $`R_a^*=R_{\bar a}`$；$`J^*=-J`$ 且左右乘交换， 得到显示伴随式。对复线性算子，这个实伴随同时保持 $h$ 的虚部，故也是复伴随。

$\square$

### 6.3　Pauli 关系、自伴锥与 Born 表示

#### 定义 6.7：由原右乘定义观测算子

对 $z\in W$ 定义

$$
\sigma_z:=-JR_z=-L_eR_z.
$$

算子正性定义为 $`F=F^*`$ 且 $h(x,Fx)\ge0$ 对全部幅度 $x$ 成立。

#### 定理 6.8：Pauli 乘法与自伴算子的全部形式

对 $z,t\in W$，有

$$
\begin{aligned}
\sigma_z^*&=\sigma_z,\qquad
\sigma_z\sigma_t=B(z,t)I+i\sigma_{z\times t},
\end{aligned}
\tag{6.6}
$$

$$
\begin{aligned}
\operatorname{Tr}\sigma_z&=0,\qquad
\operatorname{Tr}(\sigma_z\sigma_t)=2B(z,t).
\end{aligned}
\tag{6.7}
$$

每个自伴算子唯一为 $F=sI+\sigma_z$，其本征值为 $s\pm\sqrt{q(z)}$。因此

$$
E:=\operatorname{Herm}(H_J)=\mathbb RI\oplus\sigma(W),\qquad
E_+=\{sI+\sigma_z:s\ge\sqrt{q(z)}\}.
$$

**证明。**

纯元右乘和 $J$ 都反自伴且交换，所以 $-JR_z$ 自伴。 注意右乘次序反转，故

$$
\sigma_z\sigma_t=J^2R_zR_t=-R_{tz}
=B(z,t)I+R_{z\times t}
=B(z,t)I+i\sigma_{z\times t}.
$$

若 $z\ne0$，选单位 $t\perp z$；上式给 $\sigma_t\sigma_z\sigma_t=-\sigma_z$ 与 $\sigma_t^2=I$。 迹在相似变换下不变，故 $\operatorname{Tr}\sigma_z=0$；$z=0$ 也成立。 再次取迹即得配对公式。

上一全算子表示中，自伴性等价于 $a=\bar a$、$b=-\bar b$， 所以自伴算子恰为 $sI+\sigma_z$，且表示唯一。 式 (6.6) 给 $\sigma_z^2=q(z)I$；自伴性与迹零给两个本征值 $\pm\sqrt{q(z)}$，包括 $z=0$ 的退化情形。 加上 $sI$ 后逐一判定本征值非负，得到正锥。

$\square$

#### 推论 6.9：同一比较的正锥与可读性

$$
E_+=\{F^2:F=F^*\},\qquad E_+\cap(-E_+)=\{0\},
$$

且 $E_+$ 对迹配对自对偶：

$$
G\in E_+\iff\operatorname{Tr}(GF)\ge0\quad\forall F\in E_+.
$$

每个非零 $G\in E_+$ 都满足 $\operatorname{Tr}G>0$。

**证明。**

自伴平方的本征值非负；反之，对正算子的两个非负本征值取平方根， 得到自伴平方根。正锥及其负锥只能在两个本征值全零时相交。 若 $F=sI+\sigma_z$、$G=tI+\sigma_w$ 都正，则

$$
\operatorname{Tr}(FG)=2(st+B(z,w))\ge2(st-\lVert z\rVert\lVert w\rVert)\ge0.
$$

若 $G\notin E_+$ 且 $w\ne0$，取 $F=I-\sigma_{w/\lVert w\rVert}$， 得到 $\operatorname{Tr}(FG)=2(t-\lVert w\rVert)<0$。 若 $w=0,t<0$，取 $F=I$ 即可。最后非零正算子至少有一个正本征值，故迹为正。

$\square$

幅度集合 $A$ 与正对象集合 $E_+$ 类型不同。$q(-x)=q(x)$ 表示幅度反向不产生负读数， 而 $G,-G$ 同为正对象只可能 $G=0$。两者都由显示关系表达，不需赋予负幅度“负存在”的含义。

#### 定义 6.10：正读出状态与效果

$$
\operatorname{St}(E)=\{\ell:E\to\mathbb R:\ell\text{ 实线性},\
\ell(E_+)\ge0,\ \ell(I)=1\},\qquad
\operatorname{Eff}(E)=\{F:0\le F\le I\}.
$$

这里定义的是数学读出对象；实际准备、装置与这些对象的对应另需给定。

#### 定理 6.11：密度球、效果与二元平方律

全部正读出状态唯一表示为

$$
\rho_r=\frac{I+\sigma_r}{2},\qquad q(r)\le1,
\qquad\ell_r(F)=\operatorname{Tr}(\rho_rF).
$$

效果 $F=\eta I+\sigma_b$ 的准确条件是

$$
\sqrt{q(b)}\le\min\{\eta,1-\eta\}.
$$

极点状态恰对应 $q(r)=1$；对单位 $n,m\in W$，

$$
P_n=\frac{I+\sigma_n}{2},\qquad
\operatorname{Tr}(P_nP_m)=\frac{1+B(n,m)}2.
$$

**证明。**

非退化迹配对使每个实线性泛函唯一为 $F\mapsto\operatorname{Tr}(\rho F)$、$`\rho=\rho^*`$。 正锥自对偶使其正性等价于 $\rho\ge0$，单位评价等价于 $\operatorname{Tr}\rho=1$。 自伴形式及其两个本征值立即给 $\rho_r$ 和 $q(r)\le1$。 对 $F$ 与 $I-F$ 同时应用正锥条件，得到效果条件。

若 $\lVert r\rVert<1$，可沿任意小的非零方向作对称扰动 $r\pm v$，仍在球内， 故该态不是极点。若 $\lVert r\rVert=1$ 且 $r=\lambda a+(1-\lambda)b$、 $0<\lambda<1$、$\lVert a\rVert,\lVert b\rVert\le1$，与 $r$ 配对迫使 $B(r,a)=B(r,b)=1$；Cauchy–Schwarz 的等号条件给 $a=b=r$，故为极点。 $P_n^2=P_n$ 由 Pauli 式得出，其迹为一，故秩一。 最后展开两个投影并使用迹配对，得到二元概率式。

$\square$

### 6.4　Hopf 圆纤维与表示轴独立性

#### 定理 6.12：从幅度到方向的准确相位商

对 $x\ne0$ 定义

$$
r_e(x)=\frac{\bar x e x}{q(x)}\in W.
$$

它是单位方向。对归一幅度 $x,y$，有

$$
r_e(x)=r_e(y)\iff y=e^{\phi e}x=e^{\phi J}x
\quad\text{对某个 }\phi\in\mathbb R.
$$

该映射满射，所以

$$
S^1\longrightarrow S^3\longrightarrow S^2,
\qquad \mathbb P(H_J)=\mathbb{CP}^1\cong S(W).
$$

并有

$$
P_{r_e(x)}y=\frac{h(x,y)}{q(x)}\,x,\qquad
\operatorname{Tr}(P_{r_e(x)}P_{r_e(y)})
=\frac{|h(x,y)|^2}{q(x)q(y)}.
$$

右端系数均按前述左复标量约定作用。

**证明。**

共轭和范数乘性给 $r_e(x)\in W$、$q(r_e(x))=1$。 已证共轭覆盖全部三维旋转，所以 $\bar x e x$ 在单位幅度上取遍单位球。 若归一 $x,y$ 具有相同方向，置 $u=y\bar x$，则 $q(u)=1$ 且 $ue=eu$。 由纯部乘法式，$e$ 的中心化子恰为 $\mathbb R\mathbf 1+\mathbb Re$； 其中单位元恰为 $\cos\phi\mathbf 1+e\sin\phi$，得到纤维式。 反向把 $y=e^{\phi e}x$ 代入即可。 一般非零幅度先除以 $\sqrt{q(x)}$，故相同方向恰对应同一复射线。

结合性给 $x r_e(x)=e x$，于是

$$
\sigma_{r_e(x)}x=-e(xr_e(x))=-e(e x)=x.
$$

秩一投影 $P_{r_e(x)}$ 的像因此是复线 $\mathbb Cx$；正交投影的系数由 $h(x,y-\lambda x)=0$ 唯一确定为 $\lambda=h(x,y)/q(x)$。 两个秩一投影的迹乘积遂为所示平方模。

$\square$

射线商并不等于原零读出商：$\mathbf 1$ 与 $e$ 有相同的 $r_e$， 但原带参考表达式给 $q(\mathbf 1+\mathbf 1)=4$、$q(e+\mathbf 1)=2$。 因此实际相位参考若仍可使用，必须作为内部对象保留； 只有经过上述相位不变读出的菜单才将这些幅度识别为同一纯态。 一般复 $d$ 维幅度的射线空间为 $\mathbb{CP}^{d-1}$，局部用 $d-1$ 个复坐标表示， 实维为 $2d-2$；本节三维球面的方向表示只对应 $d=2$。

#### 定理 6.13：见证所选复轴仅改变表示坐标

对任意单位 $e,e'\in W$，存在单位 $u\in A$，使 $F=L_u$ 满足

$$
J_{e'}F=FJ_e,\qquad h_{e'}(Fx,Fy)=h_e(x,y),
$$

$$
\sigma_z^{e'}F=F\sigma_z^e\quad(\forall z\in W),\qquad
r_{e'}(Fx)=r_e(x).
$$

因此无需在见证之外再指定一个物理上优先的复轴。

**证明。**

若 $e'\ne-e$，定义

$$
u=\frac{\mathbf 1-e'e}{\sqrt{2(1+B(e,e'))}}.
$$

分母是分子的范数，且 $(\mathbf 1-e'e)e=e+e'=e'(\mathbf 1-e'e)$，故 $e'u=ue$。 若 $e'=-e$，取任意单位 $u\perp e$，纯部反交换仍给 $e'u=ue$。 所以 $J_{e'}L_u=L_uJ_e$。左乘单位元是实等距映射， 从而保持 $h$ 的实部及虚部；它又与全部右乘交换，得到 Pauli 交织式。 最后 $\bar u e'u=e$，所以

$$
r_{e'}(ux)=\frac{\bar x\bar u e'ux}{q(x)}=r_e(x).
$$

该证明消除的是表示坐标的额外选择，不删除主候选中忠实见证对的存在条件。

$\square$

### 6.5　酉门、整体相位与端点未确定的自由度

#### 定理 6.14：全部单比特酉门及其方向作用

单位四元数右乘的集合恰为 $\operatorname{SU}(H_J)$；每个酉算子都可写成

$$
U=e^{\phi J}R_u,\qquad q(u)=1.
$$

对单位 $z\in W$，

$$
U_z(\theta)=e^{-i\theta\sigma_z/2}=R_{e^{-\theta z/2}},
\qquad
r_e(U_z(\theta)x)=e^{\theta z/2}r_e(x)e^{-\theta z/2}.
$$

整体相位 $e^{\phi J}$ 保持 $r_e(x)$ 不变。

**证明。**

在复基 $\{\mathbf 1,f\}$ 中写 $u=\alpha+\beta f$，$\alpha,\beta\in\mathbb C_e$。 由 $f\alpha=\bar\alpha f$、$f\beta f=-\bar\beta$，右乘矩阵为

$$
R_u\ \widehat{=}\quad
\begin{pmatrix}\alpha&-\bar\beta\\ \beta&\bar\alpha\end{pmatrix}.
$$

$q(u)=|\alpha|^2+|\beta|^2=1$ 恰使该矩阵酉且行列式为一。 反过来，二维酉矩阵的列正交和行列式一迫使它具有这个形式。 给任意 $U\in U(2)$，选 $e^{2i\phi}=\det U$，则 $e^{-i\phi}U\in SU(2)$， 得到分解。这里 $u\mapsto R_u$ 是反表示；若需群同态，应取 $u\mapsto R_{u^{-1}}$。

由于 $-i\sigma_z=-J(-JR_z)=-R_z$，指数幂级数给门公式。 直接代入 Hopf 映射得到 $r_e(xu)=\bar u r_e(x)u$； 代入 $u=e^{-\theta z/2}$ 给正角度的 Rodrigues 旋转。 左相位与 $e$ 交换，故在 $\bar x e x$ 中抵消。

$\square$

<a id="section-7"></a>

## 7　线、面积、相位与钟：同一几何的准确分工

本节没有新增核心候选。固定已导出的 $W=1^\perp\cong\mathbb R^3$、内积与取向， 用 $a\cdot b$ 表示 $B(a,b)$。外积空间 $\Lambda^2W$ 带导出的欧氏面积范数， Hodge 星满足 $\star(a\times b)=a\wedge b$。 这些是同一结构的构造；指定哪条历史实际发生，仍是另一个输入。

#### 定理 7.1：单态稳定子面与转向面

对单位 $n$，定义

$$
\pi_n:\Lambda^2W\to T_nS^2,\qquad
\pi_n(\beta)=(\star^{-1}\beta)\times n.
$$

则每个 $\beta$ 唯一分解为

$$
\boxed{\beta=\lambda\star n+n\wedge v,\quad v\perp n,\quad
\pi_n(\beta)=v,\quad \|\beta\|^2=\lambda^2+\|v\|^2.}
$$

特别地，$\ker\pi_n=\mathbb R\star n$。

**证明。**

取正交定向基 $(n,u_1,u_2)$。 $u_1\wedge u_2=\star n,n\wedge u_1,n\wedge u_2$ 构成 $\Lambda^2W$ 的正交单位基。 第一项对应旋转轴 $n$，故在 $n$ 上作用为零。 对 $v\perp n$， $\pi_n(n\wedge v)=(n\times v)\times n=v$。 逐基展开给分解、唯一性、范数与核。

$\square$

这与最新 OTF-005 的轴面分解一致。[\[2\]](#ref-otf5) 单态所决定的 $\star n$ 是绕自身方向的生成面； 把该态转往别处所需的面由 $n\wedge\dot n$ 给出。 一个方向不自动确定横向的零相位： 若旋转等变地给每个 $n$ 选非零 $v(n)\perp n$， 绕 $n$ 的半周转动既固定 $n$ 又把 $v(n)$ 变成 $-v(n)$，产生矛盾。

#### 命题 7.2：端点、最短扇形与非唯一的实际门

设单位 $a,b$ 不平行，$\theta=\arccos(a\cdot b)\in(0,\pi)$，

$$
u=\frac{b-(a\cdot b)a}{\sin\theta},\quad
c=a\times u,\quad \Sigma=\frac\theta2\,a\wedge u.
$$

单位平面扇形从 $a$ 到 $b$ 的有向面积是 $\Sigma$，对应门

$$
U_{ab}=\exp(-i\theta\sigma_c/2)
=\frac{(1+a\cdot b)I-i\sigma_{a\times b}}{\sqrt{2(1+a\cdot b)}}
$$

满足 $`U_{ab}P_aU_{ab}^*=P_b`$。 端点还容许全部 $e^{-i\chi\sigma_b/2}U_{ab}$，故不能恢复唯一的实际门。

**证明。**

参数化扇形 $X(r,t)=r(\cos t\,a+\sin t\,u)$，$0\le r\le1,0\le t\le\theta$。 有 $\partial_rX\wedge\partial_tX=r\,a\wedge u$，积分得到 $\Sigma$。 Pauli 关系使指数为 $\cos(\theta/2)I-i\sin(\theta/2)\sigma_c$； 半角恒等式给显示分式。已证 Rodrigues 公式把 $a$ 旋转到 $b$。 任意主角 $\phi\in[0,\pi]$ 的轴旋转若把 $a$ 送到 $b$， 则 $a\cdot b=\cos\phi+(1-\cos\phi)(a\cdot d)^2\ge\cos\phi$， 故 $\theta\le\phi$；所构造的垂直轴达到下界。 绕 $b$ 的任意后续旋转固定 $P_b$，所以显示族共享端点。

$\square$

垂足 $C=(a\cdot b)a$ 是 $a,b$ 的确定函数，不是额外自由数据。 若 $b=-a$，转向平面不唯一；若 $b=a$，最短门可取恒等而实际历史仍可闭路。 两端点上的 $\sin\theta$、$\sin\theta/2$ 与 $\theta/2$ 分别是平行四边形、三角形与单位扇形的面积模， 球面闭路的立体角又是另一种量。

#### 定理 7.3：同一投影张量内的长度与面积

对 $n\in S^2$、$v,w\in T_nS^2$，令

$$
\mathcal Q_n(v,w)=\operatorname{Tr}\bigl(P_n\,dP_n(v)\,dP_n(w)\bigr).
$$

则

$$
\boxed{\mathcal Q_n(v,w)=\frac14\bigl(v\cdot w+i\,n\cdot(v\times w)\bigr).}
$$

其实部为 Fubini–Study 度量，约定 $d_{\rm FS}=\arccos|h(\psi,\phi)|$； 虚部给有向面积的四分之一。 采用联络 $\mathcal A=i\langle\psi,d\psi\rangle$ 时，曲率为 $\mathcal F=-2\operatorname{Im}\mathcal Q$，闭路几何相位为 $-\Omega/2$ 模 $2\pi$。

**证明。**

$dP_n(v)=\sigma_v/2$。代入 Pauli 乘法和迹公式即得张量等式。 单位幅度的水平微分满足 $ds_{\rm FS}^2=\langle d\psi,d\psi\rangle-|\langle\psi,d\psi\rangle|^2$， 以 $P=|\psi\rangle\langle\psi|$ 展开，恰等于 $\operatorname{Re}\mathcal Q$。 在球面局部坐标选 $\psi=(\cos(\vartheta/2),e^{i\varphi}\sin(\vartheta/2))^{\mathsf T}$， 直接计算

$$
\mathcal A=-\tfrac12(1-\cos\vartheta)d\varphi,\qquad
d\mathcal A=-\tfrac12\sin\vartheta\,d\vartheta\wedge d\varphi.
$$

后者等于所列 $-2\operatorname{Im}\mathcal Q$。 在可选局部截面的曲面片上用 Stokes 定理；换片只改变相位的 $2\pi$ 整数倍，得闭路式。

$\square$

这是几何量子力学与投影算子几何的标准结构。[\[12\]](#ref-ashtekar), [\[13\]](#ref-projector), [\[14\]](#ref-berry) 同一 $\mathcal Q$ 包含长度和面积，并不赋予它们相同的物理量纲。

#### 命题 7.4：同一方向路径不能确定唯一 Hamiltonian 或时长

给定 $C^1$ 的 $n(t)\in S^2$，全部使其满足薛定谔方向运动的自伴生成元为

$$
H(t)=h_0(t)I+\frac\hbar2\sigma_{n\times\dot n+\lambda(t)n},
\qquad h_0,\lambda\text{ 任意实连续函数}.
$$

其射影速度为 $ds_{\rm FS}/dt=\Delta H/\hbar=\|\dot n\|/2$。 同一几何路径和闭路面积在重新参数化后不变，而经过的钟时可以改变。

**证明。**

写 $H=h_0I+(\hbar/2)\sigma_\omega$。 Pauli 对易式将 $\dot P=-i[H,P]/\hbar$ 化为 $\dot n=\omega\times n$。 上一分解给其全部解 $\omega=n\times\dot n+\lambda n$。 纯态方差为

$$
(\Delta H)^2=\frac{\hbar^2}{4}
\bigl(\|\omega\|^2-(\omega\cdot n)^2\bigr)
=\frac{\hbar^2}{4}\|\dot n\|^2.
$$

度量公式给速度。取 $t=a\tau$、$a>0$， 新生成元 $H'(\tau)=aH(a\tau)$ 描述相同轨迹， 总参数时长由 $T$ 变成 $T/a$，面积不变，证明不可唯一识别。

$\square$

### 7.1　正性、正交与“存在”的类型

#### 命题 7.5：两个不同的正交关系

Bloch 方向 $n\cdot m=0$ 当且仅当 $\operatorname{Tr}(P_nP_m)=1/2$； 幅度射线正交当且仅当 $\operatorname{Tr}(P_nP_m)=0$，也即 $m=-n$。 复二维幅度空间不存在三个非零两两正交的幅度。

**证明。**

前两项代入 $\operatorname{Tr}(P_nP_m)=(1+n\cdot m)/2$。 最后，非零正交向量线性无关，而复维数仅为二。 因此三根相互正交的是比较方向，不是三个相互排斥的 qubit 纯态。

$\square$

对指定的二路径基，$\rho_r=(I+r\cdot\sigma)/2$ 的可预测性和干涉可见度可定义为

$$
P=|r_z|,\qquad V=\sqrt{r_x^2+r_y^2},\qquad P^2+V^2=\|r\|^2\le1.
$$

证明只需将 $\rho_r$ 的对角差与非对角条目写出；混合态和基的选择都会改变这些数值。 一个纯态可同时有非零 $P,V$，所以方向本身没有被唯一分成“粒子时刻”与“波时刻”。 与记忆的纠缠和条件读出会进一步改变可访问的干涉关系。[\[15\]](#ref-ding), [\[19\]](#ref-englert), [\[16\]](#ref-siddiqui)

#### 命题 7.6：幅度乘性不能不分类型地施加于全部事件

若对全部事件要求 $p(XY)=p(X)p(Y)$，并要求每个非零正投影都有正读数， 则任何含两个非零正交投影的量子事件代数都不满足该要求。

**证明。**

取 $P,Q\ne0$、$PQ=0$。左边为 $p(0)=0$，右边严格为正，矛盾。

$\square$

因此主候选的 $p$ 是基本幅度比较的读出。 事件正性、过程完全正性与记录 Gram 保持是它们各自的二元、三元相容关系， 不能把不同类型的条件压成同一个无区别的乘法等式。

<a id="section-8"></a>

## 8　有限量子理论的完整数学完成及实际接口

核心候选选择了一个复二维幅度块。下面先定义其有限数学完成， 再证明状态、概率、过程、记录和连续可逆演化的标准形式。 数学完成中的对象可由内部有限构造得到；某个原实际世界是否供应全部这些对象，是另一个命题。

### 8.1　本区域的输入与输出

$$
\mathsf D_0:\quad H_J\cong\mathbb C^2,\quad M_2=\operatorname{End}_{\mathbb C}(H_J),
$$

$$
\mathsf D_1:\quad \mathsf{QFin}:=
\langle M_2,\mathbb C\rangle_{\otimes_{\mathbb C},\ \oplus,\ P\mathcal M P\ (P\ne0)},
\qquad\mathcal M_+:=\{X=X^*: \langle v,Xv\rangle\ge0\ \forall v\},
$$

$$
\mathsf D_2:\quad \operatorname{State}(\mathcal M)=
\{\omega\in\mathcal M^*:\omega(\mathcal M_+)\ge0,\ \omega(I)=1\},
\quad\operatorname{Eff}(\mathcal M)=[0,I],
$$

$$
\Phi\in\operatorname{Hom}_{\mathbb C}(M_d,M_e),\qquad \mathsf P_{\rm ref}(\Phi):\quad
\forall n\ge0,\quad(\Phi\otimes\operatorname{id}_{2^n})((M_d\otimes M_{2^n})_+)\subseteq
(M_e\otimes M_{2^n})_+,
$$

$$
\begin{gathered}
T:\mathbb R\longrightarrow\operatorname{End}_{\mathbb C}(M_d),\qquad \mathsf P_{\rm time}(T):\\
T_{s+t}=T_sT_t\ (s,t\in\mathbb R),\quad T_0=\operatorname{id},\quad t\mapsto T_t\text{ 连续},\\
T_t\text{ 满足 }\mathsf P_{\rm ref}\text{ 且保迹}\qquad(t\in\mathbb R).
\end{gathered}
$$

$$
\mathsf{QFin}=\left\{\bigoplus_{j=1}^rM_{d_j}(\mathbb C):r,d_j\in\mathbb N_{\ge1}\right\},
\quad\omega(X)=\sum_j\operatorname{Tr}(\rho_jX_j),
\quad\Phi(X)=\sum_\mu K_\mu XK_\mu^*,
$$

$$
T_t(\rho)=e^{-itH/\hbar}\rho e^{itH/\hbar}\qquad(H=H^*,\ \hbar>0).
$$

上面 $\mathsf D_i$ 是数学完成与对象类型的定义， $\mathsf P_{\rm ref},\mathsf P_{\rm time}$ 是作用在待识别原过程上的条件。 不能把定义某类良好过程，改写成所有原过程已自动属于该类。 若原资料要识别为标准有限量子力学，至少应逐项绑定以下四组接口：

| 接口 | 数学关系 | 原来源须说明的对象 |
|:---|:---|:---|
| 原事件绑定 | $p_h(k)=\omega_h(E_k)$，$E_k\ge0$，$\sum_kE_k=I$ | 实际准备、全部结果、失败与归一化，及其是否经所选相位不变表示下降。 |
| 联合绑定 | $\mathcal M_{AB}\cong\mathcal M_A\otimes_\mathbb C\mathcal M_B$，使用完整正锥 | 同一复中心、真实相关准备、原系统分解与观察者记录。 |
| 完整过程绑定 | 原箭头复线性下降，全部迭代参考满足 $\mathsf P_{\rm ref}$ | 每次旁接的都是整个箭头，保留环境、记录、失败与仍合法未来。 |
| 时间与更新绑定 | 可逆钟流满足 $\mathsf P_{\rm time}$；理想投影分支有指定无扰动条件 | 实际时钟、时间单位、具体生成元及测量装置性质。 |

这些接口不计入本轮六组核心输入，也没有被它们全部证明。 项目 C139 对完整参考递归已有专门的来源条件与误差版本，正说明此处不能只写“再加入一个环境”就略过实际供应。[\[6\]](#ref-c139cp)

#### 定理 8.1：有限矩阵代数完成

上面的 $\mathsf{QFin}$ 恰为全部有限直和复矩阵代数。 若原联合是非零复含幺结合 $`*`$-代数，并有两个同复中心的可交换含幺 $`*`$-嵌入 $M_m(\mathbb C),M_n(\mathbb C)$， 且它们的乘积线性张成全部联合代数，则联合代数同构于 $M_{mn}(\mathbb C)$。

**证明。**

$M_2^{\otimes k}=M_{2^k}$。对任意 $d$，选 $2^k\ge d$，取秩 $d$ 投影的角便得 $M_d$； 有限直和给全部显示代数。反向，张量、直和与投影角都留在这一类中。 对于原联合，映射 $A\otimes B\mapsto\iota_A(A)\iota_B(B)$ 为含幺 $`*`$-同态且由张成条件满射。 $M_{mn}$ 没有非平凡双边理想：任意非零理想元素有一个非零矩阵条目， 左右乘矩阵单位便得到所有矩阵单位。因此该同态核只能是零或全部；单位不被消掉，故核为零。

$\square$

#### 定理 8.2：密度、观测与平方律

对 $\mathcal M=\bigoplus_jM_{d_j}(\mathbb C)$，每个归一正线性泛函唯一为

$$
\omega(X)=\sum_j\operatorname{Tr}(\rho_jX_j),\quad
\rho_j\ge0,\quad\sum_j\operatorname{Tr}\rho_j=1.
$$

单块的纯态为秩一投影；一般纯态只占一个块且在该块秩一。 POVM $E_k\ge0,\sum_kE_k=I$ 给归一概率 $p_k=\omega(E_k)$。 对正交投影测量和纯态，$p_k=\|P_k\psi\|^2$。

**证明。**

每块的非退化迹配对给唯一自伴 $\rho_j$。在所有向量秩一投影上非负等价于各 $\rho_j\ge0$， 单位评价给总迹一。反向由正算子迹乘积非负成立。 若有两个正本征权重，可作一正一负的小扰动并保持归一，故不是极点； 若仅一个权重为一，其秩一支撑不能非平凡分解为正态凸组合，故为极点。 POVM 式的非负与归一直接求和得到；纯投影概率由 $\operatorname{Tr}(|\psi\rangle\langle\psi|P_k)=\langle\psi,P_k\psi\rangle=\|P_k\psi\|^2$ 得出。

$\square$

#### 定理 8.3：递归二元参考充分恢复完全正性

对复线性 $\Phi:M_d\to M_e$，以下三项等价：

1.  $\mathsf P_{\rm ref}(\Phi)$ 成立；

2.  $C_\Phi=(\Phi\otimes\operatorname{id}_d)(|\Gamma\rangle\langle\Gamma|)\ge0$， 其中 $|\Gamma\rangle=\sum_{i=1}^d|i\rangle|i\rangle$；

3.  存在有限矩阵族 $K_\mu$，使 $`\Phi(X)=\sum_\mu K_\mu XK_\mu^*`$。

而 $\Phi$ 迹不增、保迹，分别等价于 $`\sum_\mu K_\mu^*K_\mu\le I`$、$=I$。

**证明。**

选 $2^n\ge d$，将 $\mathbb C^d$ 等距嵌入参考 $\mathbb C^{2^n}$。 对嵌入后的 $|\Gamma\rangle\langle\Gamma|$ 用第一项，再压回该参考子空间，得到第二项。 将正矩阵 $C_\Phi$ 分解成有限秩一和 $\sum_\mu|v_\mu\rangle\langle v_\mu|$， 按输出、输入两个指标把 $v_\mu$ 重排成矩阵 $K_\mu$。 比较 $C_\Phi$ 中每个输入矩阵单位的系数即得第三项。 反向，任意参考上的 $`\sum_\mu(K_\mu\otimes I)X(K_\mu^*\otimes I)`$ 都保持正性。 最后 $`\operatorname{Tr}\Phi(X)=\operatorname{Tr}[X\sum_\mu K_\mu^*K_\mu]`$， 在全部正 $X$ 上比较迹即得相应算子不等式或等式。

$\square$

这是 Choi–Kraus 表示的完整有限证明，其标准等价式见 Watrous 定理 2.22。[\[20\]](#ref-watrous) 对直和源 $\bigoplus_iM_{d_i}$ 与目标 $\bigoplus_jM_{e_j}$，完全正过程恰为

$$
\Phi((X_i)_i)_j=\sum_{i,\mu}K_{ji\mu}X_iK_{ji\mu}^*,
\qquad K_{ji\mu}:\mathbb C^{d_i}\to\mathbb C^{e_j}.
$$

证明只需将输入块嵌入、输出块压缩与原箭头复合，对每个分量应用单块定理； 反向是这些完全正分量的有限和。 保迹条件为每个 $i$ 的 $`\sum_{j,\mu}K_{ji\mu}^*K_{ji\mu}=I_{d_i}`$， 迹不增将等号换成 $\le$。 只要求局部正性不够：转置 $T$ 保正，但 $(T\otimes\operatorname{id})(|\Gamma\rangle\langle\Gamma|)$ 是交换算子， 在反对称二体向量上取负本征值。二元参考的递归量词不能删除。

#### 定理 8.4：内部仪器与记录的酉实现

若分支 $`\Phi_k(X)=\sum_\mu K_{k\mu}XK_{k\mu}^*`$ 满足 $`\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I`$，则

$$
V\psi=\sum_{k,\mu}K_{k\mu}\psi\otimes|k,\mu\rangle
$$

是等距映射；读取内部记录投影 $Q_k=\sum_\mu|k,\mu\rangle\langle k,\mu|$ 并取环境偏迹，恰得到原分支 $\Phi_k$。 该等距映射在适当有限扩张中可延为酉算子。

**证明。**

内积展开给 $`V^*V=I`$。展开 $`VX V^*`$，记录投影保留同一 $k$， 偏迹只保留相同 $\mu$，得到给定 Kraus 和。 把输入与输出放进一个足够大的等维空间，补全等距像的正交基，就得到酉扩张。

$\square$

#### 定理 8.5：理想投影更新的准确条件

设完全正分支 $\Phi$ 的效果为投影 $P$，即 $`\sum K_\mu^*K_\mu=P`$， 并且 $\Phi$ 固定每个支撑在 $P$ 内的归一态。 则 $\Phi(X)=PXP$。成功概率非零时，条件态为 $P\rho P/\operatorname{Tr}(\rho P)$。

**证明。**

若 $P=0$，则全部 $K_\mu=0$，结论直接成立；以下设 $P\ne0$。 对 $x\in\ker P$，$\sum\|K_\mu x\|^2=0$，故 $K_\mu=K_\mu P$。 对每个 $x\in\operatorname{im}P$ 的秩一态，输出仍为该秩一态， 正和的每一项必须留在同一条线，故 $K_\mu x$ 与 $x$ 平行。 线性算子若保持一个空间的每条线，则在其上为标量：用两个独立向量及其和即可证明。 所以 $K_\mu=c_\mu P$，效果式给 $\sum|c_\mu|^2=1$，遂得结论。

$\square$

只固定某组基态不够：在 $P$ 内退相干的通道会破坏其叠加态，仍可保持那些基态。

#### 定理 8.6：连续可逆过程给薛定谔形式

固定单块 $M_d$ 上满足 $\mathsf P_{\rm time}$ 的群，必为

$$
T_t(\rho)=U_t\rho U_t^*,\qquad U_t=e^{-itH/\hbar},\quad H=H^*.
$$

因此 $i\hbar\dot\psi=H\psi$、$\dot\rho=-i[H,\rho]/\hbar$。

**证明。**

先取任一 $T$ 及其完全正逆 $S$，令其 Kraus 为 $A_i,B_j$。 $ST=\operatorname{id}$ 的 Choi 矩阵秩一，故各 $B_jA_i$ 都为单位矩阵的标量倍。 某一倍数非零，所以对应 $B_{j_0}$ 可逆；于是所有 $A_i$ 均互相成比例， $T$ 只有一个有效 Kraus 矩阵。保迹迫使该矩阵酉。 故每个 $T_t$ 为矩阵代数的 $`*`$-自同构。

有限维连续矩阵一参数群可写成 $T_t=e^{t\delta}$：在单位附近取连续矩阵对数， 用群律、交换性和有理细分得到局部对数对 $t$ 线性，再以群律延到全部实数。 对乘法恒等式求导得 $\delta(XY)=\delta(X)Y+X\delta(Y)$。 用矩阵单位定义 $B=\sum_i\delta(E_{i1})E_{1i}$， 对 $\delta(E_{kl}E_{i1})$ 求和直接得 $[B,E_{kl}]=\delta(E_{kl})$，所以 $\delta=[B,\cdot]$。 $`*`$ 保持性使 $`B+B^*`$ 为标量，去掉该标量后 $B$ 反自伴，写成 $B=-iH/\hbar$ 即得。

$\square$

具体 $H$、与实际时钟的对应及作用量单位 $\hbar$ 没有由上述代数分类选择。 同一静态结构允许许多不同的可逆流。

#### 命题 8.7：标准结构的若干直接后果

在该数学完成中，局部保迹过程不改变另一方边缘态； 任意两个自伴量满足 Robertson 不等式；标准二体纯态可以纠缠。

**证明。**

局部无信号性由 $\operatorname{Tr}_B[(\operatorname{id}\otimes\Phi)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB}$， 将 Kraus 和与 $`\sum K^*K=I`$ 代入即可。 对 $`\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho X^*Y)`$ 用 Cauchy–Schwarz， 取中心化自伴 $\Delta A,\Delta B$，便得 $(\Delta_\rho A)^2(\Delta_\rho B)^2\ge|\operatorname{Tr}(\rho[A,B])/(2i)|^2$。 最后 $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ 的约化态为 $I/2$， 不可能是纯乘积；其秩一投影也不能是乘积态的凸组合，因为正和的各项必须落在同一条射线上。

$\square$

这些结论均来自明确的有限完成。若只供应可分离联合锥，也能保留全部局域 qubit， 却不会自动得到纠缠准备。无限维位置、动量、场方程与引力仍未由本候选恢复； 例如有限矩阵不可能满足 $[X,P]=i\hbar I$、$\hbar\ne0$，因为取迹立即矛盾。

<a id="section-9"></a>

## 9　内生注意力的可检验边界：一个菜单何时能排除可分替身

**本区域的输入。**

继承已经重构或明示采用的复量子态、Born 配对和有限张量复合； 再给路径位 $A$、标记位 $M$，$H_A=H_M=\mathbb C^2$。 实际标记菜单是有限族已校准效果

$$
\mathcal E=\{E_{b|c}:0\le E_{b|c}\le I,\quad
                 \sum_bE_{b|c}=I\},
$$

其中 $c$ 由整体内部控制器编码。 记录须包含各结果概率及路径侧的完整条件态：

$$
\tau_{b|c}(\rho)=\operatorname{Tr}_M[(I\otimes E_{b|c})\rho].
$$

不同 $c$ 的记录来自同一个制备态 $\rho_{AM}$，或对同一保留历史 $h$ 已建立共同条件源 $\rho_{AM|h,c}=\rho_{AM|h}$； 这里只比较终端读出，不把未执行的相干复用算入菜单； 竞争源允许任意混合态，没有另加整体纯态承诺。 可信校准、条件层析、标记维数、共源条件和终端限制均是前件， 并不由“观察者在整体内部”自动推出。

**定义。**

写 $\rho\equiv_{\mathcal E}\omega$ 表示全部 $\tau_{b|c}$ 相同。 称 $\omega$ 为可分替身，若 $\omega=\sum_jp_j\alpha_j\otimes\beta_j$，其中两侧因子均为密度矩阵。 因为每个菜单完备，记录同时确定 $\rho_A=\sum_b\tau_{b|c}$。

#### 定理 9.1：标记 qubit 的终端菜单分类

在上述前件下，以下两项等价：

$$
\begin{split}
 & [E,F]=0\qquad(\forall E,F\in\mathcal E);\\
 & \forall\rho_{AM}\quad\exists\omega_{AM}\text{ 可分},\qquad
       \rho\equiv_{\mathcal E}\omega.
\end{split}
$$

若菜单含两个不对易效果，则 Bell 态 $\Phi=\lvert\Phi^+\rangle\langle\Phi^+\rvert$、 $\lvert\Phi^+\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$ 的完整条件记录唯一确定 $\Phi$，即使竞争解释允许任意混合态。

**证明。**

若全部效果对易，取共同正交本征基 $\lvert 0\rangle,\lvert 1\rangle$，令

$$
P_j=\lvert j\rangle\langle j\rvert,\qquad
 \Delta_M(\rho)=\sum_{j=0}^1(I\otimes P_j)\rho(I\otimes P_j)
               =\sum_{j=0}^1\tau_j\otimes P_j,
 \quad \tau_j=(I\otimes\langle j\rvert)\rho(I\otimes\lvert j\rangle).
$$

各 $\tau_j\ge0$ 且总迹为一，故 $\Delta_M(\rho)$ 可分。 对任意路径算子 $O$ 及菜单效果 $E$，

$$
\operatorname{Tr}[(O\otimes E)\Delta_M(\rho)]
   =\operatorname{Tr}[(O\otimes\sum_jP_jEP_j)\rho]
   =\operatorname{Tr}[(O\otimes E)\rho].
$$

这正是全部非归一条件态相同。

反之，qubit 效果写成 $E=aI+b\sigma_n$、$F=dI+e\sigma_m$， 其中 $b,e>0$，$n,m$ 为单位实向量。 不对易等价于 $n\times m\ne0$。 校准的 $a,b,d,e$ 和已记录的 $\rho_A$ 给出

$$
\tau(\sigma_n)=\frac{\tau(E)-a\rho_A}{b},\qquad
 \tau(\sigma_m)=\frac{\tau(F)-d\rho_A}{e}.
$$

这是记录的线性重组，没有新增物理测量。 Bell 记录满足 $\tau_\Phi(X)=X^{\mathsf T}/2$； 故任一兼容态 $\omega$ 满足

$$
\operatorname{Tr}(\omega C_n)=\operatorname{Tr}(\omega C_m)=1,
 \qquad C_v=\sigma_v^{\mathsf T}\otimes\sigma_v.
$$

这里转置相对于定义 $\Phi$ 的共同基。 $I-C_v\ge0$，且 $\operatorname{Tr}[\omega(I-C_v)]=\|(I-C_v)^{1/2}\omega^{1/2}\|_2^2=0$ （$`\|X\|_2^2=\operatorname{Tr}(X^*X)`$）， 所以 $\omega$ 的支撑位于 $C_n,C_m$ 的共同 $+1$ 子空间。

任意双 qubit 向量唯一写为 $(I\otimes X)\lvert\Phi^+\rangle$。 它被 $C_v$ 固定等价于 $\sigma_vX\sigma_v=X$，即 $[X,\sigma_v]=0$。 展开 $X=x_0I+z\cdot\sigma$，$z\in\mathbb C^3$； 同时对易要求 $n\times z=m\times z=0$。 两轴不平行迫使 $z=0$，因此共同子空间只有 Bell 射线。 迹一性给 $\omega=\Phi$，它不可分，证明反向及唯一性。

$\square$

这一分类没有说“不对易菜单能认证每一个源的纠缠”； 它说这样的菜单已能认证某些源，而对易菜单对任何源都做不到。 判据计算的是效果之间是否对易：一个单独的非投影 POVM 也可能已有不对易效果，不能把“单个设置”一概等同于“单根轴”。 效果不对易不等价于 POVM 之间不可联合测量；本定理保留维数与校准信任。 单个正交擦除基的可分替身是上述前向的特例。 经典相关能够复现条件条纹的现象已有实验研究； 最新预印本进一步严格区分完整擦除记录、独立最优辨路量与额外联合记录。 本定理仅将这些边界压成 qubit 实际菜单上的等价命题， 不作基础量子公理或历史首创的声明。[\[17\]](#ref-gogo05), [\[16\]](#ref-siddiqui)

#### 反例 9.2：完美条件条纹仍可来自可分源

令

$$
\rho_X=\tfrac12(\lvert++\rangle\langle++\rvert+\lvert--\rangle\langle--\rvert).
$$

对标记测 $X$，它与 $\Phi$ 给同样的两个非归一条件态 $\tau_{\pm}=\tfrac12\lvert\pm\rangle\langle\pm\rvert$。 每个子样本均有单位可见度，未分类的路径态均为 $I/2$。 但 $\rho_X$ 可分。再测标记 $Z$ 并保留路径条件态时， $\Phi$ 给 $\lvert 0\rangle,\lvert 1\rangle$，而 $\rho_X$ 两支均给 $I/2$，于是可区分。 若只保留条件条纹的可见度，两者在 $Z$ 菜单均为零、在 $X$ 菜单均为一， 仍无法区分；这里必须保留条件路径布居等完整记录。

### 9.1　两个稳定相关怎样迫使第三个相关闭合

取正交轴 $u,v$，令 $w=u\times v$。Pauli 乘法给

$$
C_uC_v=C_vC_u=C_w,
 \qquad \Phi=\frac14(I+C_u)(I+C_v).
$$

转置反转乘积次序，正好消去另一侧的 $\mathrm i^2$ 符号。 因而两个轴上的完美共同相关同时锁定第三轴； 这利用整体的正性和同一个源，不是逐个条件子样本分别挑一个解释。 所锁定的是这份共同态的相关，并未自动新增可执行的第三轴仪器； 对任意局部态仅保留 $X,Z$ 读数，仍不能普遍恢复 $Y$ 分量。

#### 命题 9.3：正交相关的误差闭合

令 $\delta_j=1-\operatorname{Tr}(\rho C_j)\ge0$，则

$$
\delta_w\le\delta_u+\delta_v,
 \qquad \operatorname{Tr}(\rho\Phi)\ge1-\frac{\delta_u+\delta_v}{2}.
$$

每个可分态还满足 $\operatorname{Tr}[\rho(C_u+C_v)]\le1$。

**证明。**

$C_u,C_v$ 对易且取值 $\pm1$，故其共同谱上 $1-ab\le(1-a)+(1-b)$。 同理，对 $P_j=(I+C_j)/2$ 有 $I-P_uP_v\le(I-P_u)+(I-P_v)$；取期望给两个误差界。 对乘积态，两局部 Bloch 向量长度至多一， Cauchy–Schwarz 给两项相关之和至多一，再以凸性延到可分态。 这是标准稳定子证书的双 qubit 形式。[\[18\]](#ref-toth05)

$\square$

#### 命题 9.4：非平行两轴的紧谱界

设 $c=n\cdot m$、$|c|<1$， $W=C_n+C_m$、$\varepsilon=2-\operatorname{Tr}(\rho W)$。 仅使用这两条相关便有

$$
\operatorname{Tr}(\rho\Phi)\ge
 \max\left\{0,\ 1-\frac{\varepsilon}{2(1-|c|)}\right\},
 \qquad
 \operatorname{Tr}(\omega W)\le1+|c|\quad(\omega\text{ 可分}).
$$

第二界可达到；第一界作为由 $\operatorname{Tr}(\rho W)$ 单独给出的下界也可达到。 因此 $\varepsilon<1-|c|$ 足以认证纠缠。

**证明。**

共同作 $\overline U\otimes U$ 的参考变换保持 $\Phi$，可设 $n=e_z$、$m=(\sin\theta,0,\cos\theta)$，$c=\cos\theta$。 在 $\Phi^+,\Psi^-$ 上 $W$ 分别取 $2,-2$； 在 $\operatorname{span}\{\Phi^-,\Psi^+\}$ 上为

$$
\begin{pmatrix}
  1+\cos2\theta&\sin2\theta\\
  \sin2\theta&-1-\cos2\theta
 \end{pmatrix},
$$

其本征值为 $\pm2|c|$。 故 $W\le2\Phi+2|c|(I-\Phi)$，直接给 Bell 重叠的下界。 混合 $\Phi$ 与本征值 $2|c|$ 的正交本征态达到线性边界； 更低的相关可在 $\Phi^\perp$ 内达到，故零界也紧。

对乘积态，反射转置一侧的 Bloch 向量后，相关和为 $a^{\mathsf T}(nn^{\mathsf T}+mm^{\mathsf T})b$。 中间实矩阵的最大奇异值是 $1+|c|$，两向量长度至多一，故得界。 取两向量同为最大本征方向即可达到；凸性给全部可分态。

$\square$

若实际二元效果为 $E_{\pm|j}=(I\pm\eta_j\sigma_j)/2$，$0<\eta_j\le1$， 记录中的原始相关为 $r_j=\eta_j\operatorname{Tr}(\rho C_j)$。 若估计误差 $|\widehat r_j-r_j|\le e_j$， 可用下界 $\sum_{j=n,m}(\widehat r_j-e_j)/\eta_j$ 代入上述证书。 小强度使误差放大 $1/\eta_j$。 近共线时 $1-|c|$ 趋于零，原始两相关证书的容差按夹角平方消失。 完整条件层析也可重组正交方向

$$
v=\frac{m-cn}{\sqrt{1-c^2}},\qquad
 \tau(\sigma_v)=
 \frac{\tau(\sigma_m)-c\tau(\sigma_n)}{\sqrt{1-c^2}},
$$

但记录误差被 $1/\sqrt{1-c^2}$ 放大。 上面的紧谱界只对两条原始相关而言，不声称使用全部条件层析后仍最优。

### 9.2　内生控制仍须保留共同源关系

#### 反例 9.5：删去共同源条件，完全可分整体也能伪装两轴记录

令

$$
\rho_Z=\tfrac12(\lvert 00\rangle\langle 00\rvert+\lvert 11\rangle\langle 11\rvert),\qquad
 \rho_X=\tfrac12(\lvert++\rangle\langle++\rvert+\lvert--\rangle\langle--\rvert),
$$

并取内部控制整体

$$
\omega_{CAM}=\tfrac12\lvert\mathsf z\rangle\langle\mathsf z\rvert\otimes\rho_Z
             +\tfrac12\lvert\mathsf x\rangle\langle\mathsf x\rvert\otimes\rho_X.
$$

它是三个部分上的完全可分态。 控制为 $\mathsf z$ 时读标记 $Z$，控制为 $\mathsf x$ 时读标记 $X$， 逐菜单都给 Bell 源的完整条件态记录。 但两次记录作用于不同条件源，不能拼成同一个 $\rho_{AM}$ 的两条相关。 所以把控制器写进整体后，还必须传播其与制备的相关，不能默认独立。

#### 反例 9.6：qubit 维数限定不能直接删除

取 $H_M=\mathbb C^3\oplus\mathbb C^2$，令 $n_1,n_2,n_3$ 为同一平面上 间隔 $120^\circ$ 的三个单位向量，$\sum_i n_i=0$。 在第二个直和块定义 $B_i=(I+n_i\cdot\sigma)/3$，并令

$$
E_i=\lvert i\rangle\langle i\rvert\oplus B_i\qquad(i=1,2,3).
$$

这些效果构成 POVM，且彼此不对易。 但是任意源的记录 $\tau_i$ 都由可分态 $\omega=\sum_i\tau_i\otimes\lvert i\rangle\langle i\rvert$ 复现， 因为 $\langle i\rvert E_j\lvert i\rangle=\delta_{ij}$。 所以高维中，仅从效果不对易不能照搬本节的等价分类。

**操作闭合。**

对实际内部仪器选 Kraus 算子 $K_{b\mu|c}$， $`\sum_{b\mu}K_{b\mu|c}^*K_{b\mu|c}=I`$，则

$$
V(\lvert c\rangle\otimes\psi)=
 \sum_{b\mu}\lvert c\rangle\otimes K_{b\mu|c}\psi\otimes\lvert b,\mu\rangle
 \quad\Longrightarrow\quad V^*V=I.
$$

因此每个被添加的控制或记录步骤保持整体二元 Gram 表； 有限复合也保持它，所有三元限制随之保持。 条件化和偏迹必须由这个整体过程计算，不能另行修改已确立的跨菜单关系。 内生“注意力”在这里完全是控制设置、可访问效果及条件记录的变量。

<a id="section-10"></a>

## 10　固定点、有限三维提升与完整内部时间

**本区域的输入。**

$$
I=[-1,1],\quad s\in\{-1,1\},\quad F_s(x)=s\cos x,
\quad \omega:I\to\mathbb R\text{ Lipschitz},
$$

$$
T_s:I\times S^1\to I\times S^1,\qquad
T_s(x,z)=(F_s(x),e^{i\omega(x)}z).
$$

角度编码、反馈函数、符号政策和相位更新均为本区域给定资料， 不是六组主条件自行选定。$z$ 表示可访问的内部 *相对* 相位； 若它只是整体共同相位，应先按实际菜单取相位商。 本节的余弦与相位结论已经出现在 OTF-004、OTF-005， 以下给出所需证明并保留其输入。[\[9\]](#ref-otf4), [\[2\]](#ref-otf5)

#### 定义 10.1：固定点的二元关系

对 $f:X\to X$，定义 $\Gamma_f=\{(x,f(x)):x\in X\}$、 $\Delta_X=\{(x,x):x\in X\}$。 固定点集合准确为 $\Gamma_f\cap\Delta_X$ 在第一坐标的投影。

#### 定理 10.2：正负余弦与政策二周期

存在唯一 $r\in(0,1)$ 满足 $\cos r=r$。 $F_s$ 在实轴的唯一固定点为 $sr$，任意实初值一步后进入 $I$， 并以常数 $L=\sin1<1$ 几何收敛到 $sr$。 两方程 $\cos x=x$ 与 $\cos x=-x$ 没有共同实解。 若给定内部政策 $G(s,x)=(-s,-s\cos x)$，则

$$
(1,r)\longleftrightarrow(-1,-r)
$$

是一条二周期。

**证明。**

$\cos x-x$ 在 $0,1$ 端点异号。 任何实固定点模至多为一；在 $I$ 上中值定理给 $|F_s(x)-F_s(y)|\le L|x-y|$。 余弦偶性给 $F_s(sr)=sr$，压缩估计给唯一性与迭代误差 $|x_n-sr|\le L^{n-1}|x_1-sr|$。 同时满足两方程将迫使 $x=0$，与 $\cos0=1$ 矛盾。 把 $(1,r),(-1,-r)$ 依次代入 $G$ 即得二周期。

$\square$

若每步允许任意符号 $s_n$，则一步后 $|x_{n+1}|=\cos|x_n|$，故模长仍趋 $r$； 符号却可持续切换。这是给定政策的结论，未唯一规定自然常数、粒子种类或时间箭头。

#### 定理 10.3：标量固定不保证相位固定

令 $`x_*=sr`$、$`\omega_*=\omega(x_*)`$。级数

$$
A(x)=\sum_{j=0}^{\infty}\bigl(\omega(F_s^j x)-\omega_*\bigr)
$$

一致绝对收敛，且 $\operatorname{Lip}(A)\le K/(1-L)$，其中 $K=\operatorname{Lip}(\omega)$。 同胚 $\mathcal H(x,z)=(x,e^{iA(x)}z)$ 满足

$$
\boxed{\mathcal H\circ T_s=(F_s\times R_{\omega_*})\circ\mathcal H,\quad
R_{\omega_*}(z)=e^{i\omega_*}z.}
$$

因此完整模型有固定点，当且仅当 $`\omega_*\in2\pi\mathbb Z`$； 有理非整数 $`\omega_*/2\pi=p/q`$ 给极限 $q$ 周期， 无理比值给极限圆上的稠密旋转。

**证明。**

每项绝对值至多 $`KL^j|x-x_*|\le2KL^j`$，给一致收敛； 逐项比较 $x,y$ 给 Lipschitz 界。 去掉首项得到

$$
A(x)-A(F_sx)=\omega(x)-\omega_*.
$$

将其代入 $\mathcal H(T_s(x,z))$ 即得共轭；逆为 $(x,z)\mapsto(x,e^{-iA(x)}z)$。 对迭代求和还给

$$
z_n=e^{i[n\omega_*+A(x_0)-A(x_n)]}z_0,
\quad |A(x_n)|\le\frac K{1-L}L^n|x_0-x_*|.
$$

固定或周期点的基底必须是 $`x_*`$，因为 $F_s^q$ 仍压缩。 余下分类就是圆周旋转：有理转角返回，无理转角的整数倍模 $2\pi$ 稠密。 后者可由鸽巢原理得到任意小的非零整数倍角，再以其倍数逼近任意圆周角。

$\square$

#### 命题 10.4：完整幺正整体没有非平凡吸引固定点

若 $`\rho_n=U^n\rho_0(U^*)^n`$ 在迹范数下收敛到 $`\rho_*`$，则 $`\rho_0=\rho_*`$ 且 $`U\rho_0U^*=\rho_0`$。 若完整状态还包含严格追加的记录 $m\mapsto m+1$，也不存在固定点。

**证明。**

极限连续性给 $`U\rho_*U^*=\rho_*`$。 于是 $`\|\rho_n-\rho_*\|_1=\|\rho_0-\rho_*\|_1`$ 对全部 $n$ 成立； 左边趋零使初始差已经为零。记录部分的不动要求 $m=m+1$，不可能。

$\square$

### 10.1　三维图像与有限动态闭合

#### 命题 10.5：静态三维归一化

$$
v(x)=(1,x,\cos x),\quad n(x)=v(x)/\|v(x)\|_2
$$

给球面中的曲线，并且 $\cos x=\pm x$ 分别等价于 $n_3(x)=\pm n_2(x)$。 但若要求提升中线性读出原 $x$，余弦迭代没有任何精确有限维线性提升。

**证明。**

第一坐标非零，归一化不改变第二、第三坐标的等比关系，给静态结论。 对第二项，若存在有限特征 $\Theta$、固定矩阵 $K$， $\Theta(\cos x)=K\Theta(x)$，且 $1,x$ 均为 $\Theta$ 的线性读数， 则 $1,x,\cos x,\cos(\cos x),\ldots$ 全在同一个有限维函数空间。

这些函数实际上在每个非空实开区间上线性无关。 设 $f_0(x)=x,f_{j+1}=\cos f_j$，有限关系 $c_{-1}+\sum_{j=0}^Nc_jf_j=0$ 在区间成立。 各项整函数，解析恒等定理将关系延到实轴。 $f_0$ 无界，而所有 $j\ge1$ 项在实轴有界，故 $c_0=0$。 以 $y=\cos x$ 遍历 $[-1,1]$，余下关系变为 $c_{-1}+\sum_{j=1}^Nc_jf_{j-1}(y)=0$；再次解析延拓，得 $c_1=0$。 有限重复消去全部系数，矛盾。

$\square$

该命题没有排除状态依赖矩阵、近似、无限维表示或改变读出坐标的共轭。 归一化后的 $x=n_2/n_1$ 是比值读数，不能直接拿上一线性读数判据排除一切射影模型。 对所写自然坐标本身，还可独立证明不存在固定非零射影推进，附完整短证如下。

#### 命题 10.6：自然三维坐标没有固定射影线性推进

不存在固定 $M\in M_3(\mathbb R)$ 使 $Mv(x)=\lambda(x)v(\cos x)\ne0$ 在一个非空实开区间恒成立。

**证明。**

将三行记为 $(a,b,c),(d,e,f),(g,h,k)$。 首行给 $\lambda=a+bx+c\cos x$。 次行的整函数恒等式延拓到 $x=iy$，虚部给 $ey=by\cosh y$，故 $b=e=0$；实部给 $d+(f-a)\cosh y-c\cosh^2y=0$，故 $c=d=0,f=a$。 因此 $\lambda=a\ne0$。 第三行成为 $g+hx+k\cos x=a\cos(\cos x)$。 再置 $x=iy$，虚部使 $h=0$，右端有界而 $\cosh y$ 无界使 $k=0$。 取 $\cosh y=\pi,2\pi$，分别给 $g=-a,g=a$，矛盾。

$\square$

### 10.2　把钟和操作写进整体的一个有限模型

#### 定理 10.7：有限内部历史态与传播约束

给定门序列 $U_1,\ldots,U_N$，令 $V_0=I$、$V_k=U_k\cdots U_1$，

$$
|\Psi\rangle=\frac1{\sqrt{N+1}}\sum_{k=0}^N|k\rangle_T\otimes V_k|\psi\rangle,
\quad L_k=\langle k|\otimes I-\langle k-1|\otimes U_k,
\quad G_{\rm hist}=\sum_{k=1}^NL_k^*L_k.
$$

则 $G_{\rm hist}\ge0$、$G_{\rm hist}|\Psi\rangle=0$。 条件于内部钟记录 $k$ 的系统态为 $V_k|\psi\rangle$。

**证明。**

平方和给正性。每个 $L_k|\Psi\rangle$ 等于 $(V_k-U_kV_{k-1})|\psi\rangle/\sqrt{N+1}=0$。 钟投影 $|k\rangle\langle k|$ 的概率为 $1/(N+1)$，收缩并归一即得条件态。

$\square$

这属于关系时钟的有限数学实现；门、标签次序及初始数据均留在式中。[\[21\]](#ref-pw), [\[22\]](#ref-trinity), [\[23\]](#ref-baumann) 它不自动选择秒、连续时长或唯一宇宙态；$G_{\rm hist}$ 是传播约束，未被默认为驱动实际装置的 Hamiltonian。

若实验二值结果 $Y\in\{-1,1\}$ 仅满足 $\mathbb E[Y\mid x]=\cos x$， 则单次反馈 $x'=sY$ 一步后只取 $\pm1$，到 $sr$ 的距离至少为 $1-r>0$。 因此理想期望反馈的压缩不等于单次量子结果的轨迹。 重复准备、估计误差和控制资源均须作为内部协议继续保留。

<a id="section-11"></a>

## 11　项目衔接推论：混态序列的统一读出界代替实际纯锚

本节是主候选之外的一个有明确前件的项目衔接推论， 不是第二个新公理候选，也不从主候选自动取得所列来源资料。[\[3\]](#ref-c128) 仓库 C128 新增第16–21节证明了指定自旋背景上一个数学纯锚的零空间下降定理。 以下说明，若原来源只供应趋向该方向的一列混态读出， 怎样以统一稳定性取得同一结论，而不增加一份可制备纯态。

**既有背景 $\mathsf B$.**

取实 Hilbert 空间 $H$ 及稠密实线性子空间 $V\subset H$， 原域 $E=\mathbb Ru\oplus V$，同一原 Jordan 乘法、锥和范数为

$$
S(su+x,tu+y)=(st+\langle x,y\rangle)u+sy+tx,
\quad C=E\cap\{su+x:s\ge\|x\|\},
\quad N(su+x)=|s|+\|x\|.
$$

旧 $D:E^2\to E$ 初始仅为反对称总映射。在全部原输入上支付

$$
\begin{aligned}
\mathrm{PY}:\quad D(a,b)^2
&=\tfrac12\bigl(U_a(b^2)+U_b(a^2)\bigr)-S(a,b)^2,\\
\mathrm{NN}:\quad D(a,D(a,b))&=(L_a^2-L_{a^2})b,
\end{aligned}
$$

其中 $L_ab=S(a,b)$、$U_a=2L_a^2-L_{a^2}$、$a^2=S(a,a)$。 完整 $\mathrm R$ 在这里准确指

$$
S(S(a,b),c)-D(D(a,b),c)=S(a,S(b,c))-D(a,D(b,c))\quad(\forall a,b,c).
$$

同一原评价族、质量、来源身份和全部操作合同保持；本节不新造这些来源。 不预设 $D$ 双线性、连续性、完整换括号 $\mathrm R$ 或有限维。 既有 W32.2 的仅用 PY+NN 的部分给

$$
D(su+x,tu+y)=\kappa(x,y)\in V,\quad
\kappa(x,y)\perp x,y,
$$

$$
\|\kappa(x,y)\|^2=\|x\|^2\|y\|^2-\langle x,y\rangle^2,
\qquad
\kappa(x,\kappa(x,y))=\langle x,y\rangle x-\|x\|^2y.
\tag{B}
$$

**本推论另付的资料.**

设 $V\ne0$。固定一个原单位方向 $n\in V$，并由原来源供应评价

$$
\alpha_j(su+v)=m_j\bigl(s+r_j\langle n,v\rangle\bigr),
\quad m_j>0,\quad 0\le r_j<1,\quad r_j\longrightarrow1.
\tag{M}
$$

每个有限 $j$ 都是混态边界以内的读出。质量可以变化，不要求其正下界。 在自由复标签空间 $\mathcal F=\mathbb C^{(E)}$ 上定义

$$
h_j([a],[b])=\alpha_j(S(a,b))-i\alpha_j(D(a,b)),
\qquad
\mathscr A_t[a]=[S(t,a)]-i[D(t,a)].
$$

第一式按第一槽共轭线性、第二槽线性延拓；第二式自由复线性延拓。 另要求以下两项，而不是从混态的名称推定它们：

$$
\begin{aligned}
\mathrm G &: \quad h_j(f,f)\ge0\quad(\forall j,\forall f\in\mathcal F),\\
\mathrm{UB} &: \quad
\forall t\in E\;\exists C_t<\infty\;\forall j,\forall f\in\mathcal F,\quad
h_j(\mathscr A_t f,\mathscr A_t f)\le C_t^2h_j(f,f).
\end{aligned}
$$

各 $C_t$ 可以不同；统一性只针对同一原 $t$ 的评价序列。 G检查这条序列的全部有限原标签 Gram 表，不要求全部原评价的 Gram 表。

#### 定理 11.1：混态序列统一界的充要性

在上述固定 $\mathsf B$、M和G下，UB与同一个原 $D$ 的完整R等价。 成立时 $D$ 自动有界实双线性，且 $\dim H\in\{1,3\}$、$E=\mathbb Ru\oplus H$； 一轴支为 $\mathbb C\oplus\mathbb C$，三轴支为 $M_2(\mathbb C)$。 若原 $V$ 至少含两个独立方向，就只留下三轴支。 标量支 $V=0$ 另外直接给 $D=0$、代数 $\mathbb C$，不需要M。 完整R成立后可取 $C_t=N(t)$。

**证明。**

先仅固定任意一个 $j_0$。PSD型的Cauchy–Schwarz使 $\mathcal N_{j_0}=\{f:h_{j_0}(f,f)=0\}$为复线性子空间。 若实系数关系 $r=\sum_k c_k[a_k]$ 满足 $\sum_k c_ka_k=0$， 则S双线性及D反对称使虚部成对抵消，给

$$
h_{j_0}(r,r)
=\alpha_{j_0}\!\left(S\!\left(\sum_kc_ka_k,\sum_kc_ka_k\right)\right)=0.
$$

故 $\eta:E\to\mathcal F/\mathcal N_{j_0}$、$a\mapsto[a]+\mathcal N_{j_0}$ 为实线性映射，并且由(B)

$$
\|\eta(v)\|^2=m_{j_0}\|v\|^2\qquad(v\in V).
\tag{1}
$$

UB给 $\mathscr A_t\mathcal N_{j_0}\subseteq\mathcal N_{j_0}$。 将其用于 $[a+b]-[a]-[b]$ 与 $[\lambda a]-\lambda[a]$， S项由已知双线性消去，于是相应D线性缺陷的$\eta$像为零。 这些缺陷在V中，(1)使它们真正为零。 反对称性给另一槽线性。因此同一个旧D双线性； 由(B)也有 $N(D(a,b))\le N(a)N(b)$。 这一步只使用一个混态读出的正性与每个作用的有限界，不使用纯性。

若V没有与n独立的方向，则 $V=\mathbb Rn$，(B)使D为零，得到一轴支。 否则在原V中取单位 $x\perp n$，令

$$
y=\kappa(n,x),\quad W=\operatorname{span}\{n,x,y\},\quad z=x-iy.
$$

由(B)，三轴正交单位；在现在已经合法的复双线性乘法 $a\star b=S(a,b)-iD(a,b)$中有

$$
z^*\star z=2(u-n).
\tag{2}
$$

假设有原单位 $w\perp W$。记 $p=\kappa(w,x)$、$q=\kappa(w,y)$。 双线性及(B)经极化给交替三形式$\langle\kappa(a,b),c\rangle$和

$$
\kappa(a,\kappa(b,c))+\kappa(b,\kappa(a,c))
=\langle a,c\rangle b+\langle b,c\rangle a-2\langle a,b\rangle c.
$$

从而 $\|p\|=\|q\|=1$、$\kappa(n,q)=p$， $\langle n,\kappa(q,p)\rangle=1$，且 $w\star z=-q-ip$。 因此

$$
h_j(z,z)=2m_j(1-r_j),\qquad
h_j(w\star z,w\star z)=2m_j(1+r_j).
\tag{3}
$$

这里把自由表达式$[x]-i[y]$送入UB即可； D双线性已使自由型因子化至$E+iE$，原$\mathscr A_w$准确下降为$w\star$。 UB及(3)要求

$$
C_w^2\ge\frac{1+r_j}{1-r_j}\longrightarrow\infty,
$$

矛盾。若原V中有任意$v\notin W$，则$w=(v-P_Wv)/\|v-P_Wv\|$仍属原V， 正是所排除的单位向量。故V=W。 有限维V闭且在H中稠密，故V=H。 交替三形式在三维中只有一个系数，面积式使该系数为$\pm1$； 同一原$\kappa$于是为固定取向的$\pm$叉积。 既有显式Pauli同构给同一$S-iD$的$M_2(\mathbb C)$乘法，因而完整R成立。

反向，$\mathsf B$加完整R的既有恢复给同一兼容C\*结构。 对每个正评价$\alpha_j$和$t\in E$，

$$
\alpha_j((t\star a)^*\star(t\star a))
\le N(t)^2\alpha_j(a^*\star a).
$$

由自由标签求和映射拉回即给全部j、f的UB，取$C_t=N(t)$。

$\square$

**条件审计.**

本推论另付的是M、G、UB，依赖既有B/PY/NN，未从主候选免费导出。 M所含原方向、实际评价供应、全量程$r_j\to1$均要列账。 G不是只检查二阶或三阶Gram；UB不是逐态各自有界。 无需可实施纯态，也无需把数学极限添加为原准备。 若$r_j$始终离1有正距离，则Spin7的同一作用界可统一有限，不能排除七轴。 若仅每个j分别有界，C12819.1的Spin7给准确发散比$(1+r_j)/(1-r_j)$。 若删指定单一自旋背景，隐藏直和块反例依然有效。 任何有限深度的验证都不能替代上述全序列、全原输入量词。 此结果只是项目中纯锚接口的一条替代供应定理，不声称全局最少公理或物理时间起源。

<a id="section-12"></a>

## 12　全理论账本与本轮白话

| 层次 | 明确输入 | 已闭合输出 |
|:---|:---|:---|
| 基本幅度关系 | 实线性签名；双线性；半范数；E、N、U、F，共六个命名组 | 原内积、原四元数商、三维方向、内部复结构、复二维幅度。 |
| 数学事件与几何 | 在所得幅度上定义全复线性算子、正锥及正归一线性读出 | Pauli 代数、Bloch 球、Born 配对、相位纤维、度量和面积张量。 |
| 有限复合理论 | 有限复张量、直和与角；原联合和正锥的实际供应另绑定 | 全部有限复矩阵块、密度态、纠缠态及标准有限事件。 |
| 过程和测量 | 原过程复线性；所有递归二元参考保持正性；完整仪器 | CP/Kraus、内部记录酉实现；指定无扰动投影分支给 Lüders。 |
| 时间 | 连续可逆实参数群与钟标定；或指定内部历史合同 | 薛定谔形式；关系钟条件态。具体 $H,\hbar$ 与秒未由几何选择。 |
| 观察者认证 | 同源、可信 qubit 菜单、完整终端条件记录 | 对易菜单的可分替身分类、两轴 Bell 证书、三元相关闭合及误差界。 |
| 余弦闭环 | 函数、弧度编码、符号政策、相位/记忆更新 | 标量 $\pm r$、政策二周期、相位圆分类；不等于整体自动静止。 |

六组核心输入是一个基本幅度块的条件；后续实际绑定明确另计。 将整个构造命名为 $\Omega$，可以确保模型里没有外置的物理观察者。 这个命名不能证明给定源、菜单、复合和动力学自动满足所有约束， 也不能把形式定义的选择消去。更简洁的目标应是将某条可检验的前件真正移成定理， 并指出删除剩余前件后的反模型。

本轮已完成这样的一个移动：在输入位置移除内积与平行四边形， 由范数大小、双线性组合、乘性及单位推出它们，再由全第三槽忠实性选出三维纯方向。 这是一项条件重建。它尚未从同一来源恢复无限维场、局域性、引力、相互作用与具体钟速率， 所以没有把有限 qubit 几何宣布为全部物理已经终结。

**本轮完整白话。** 先不画球，也不先规定直角；只让每种可比较的响应有一个非负的大小， 两份响应能够线性合成，接上同一个响应时大小按同一比例改变，还有一个接上去保持读数的单位。 这些关系会把每一对响应张成的平面逼成圆的几何，内积和正交从这里出现。 再选同一对响应：一种办法先比较它们再作用到第三个，另一种办法让它们按两种次序作用后再比较。 如果把这两份结果合读，绝不会把原来可读的第三个变成零，整个可读基本块便只剩一个标量和三根方向。 方向给出态，转向平面给出门，相位圆记录同一方向背后仍可与内部参考比较的差别。 观察者也是这个整体里的控制、参考和记忆；看哪套关系由实际菜单决定， 但换菜单时是否换了源也必须记账。 一个读数到达余弦固定点，只说明这项比较平衡了；其相位、钟和记忆是否也停止，仍由同一整体的完整关系来判断。

## 参考来源

<a id="ref-repo"></a>

\[1\] Trureturing，默认分支 `dev`。主快照 [840da33992b6](https://github.com/the-omega-institute/trureturing/commit/840da33992b600d8d4808b04ff82dde323089212)，2026-11-07 21:30:57 UTC；末次 [142923373ceb](https://github.com/the-omega-institute/trureturing/commit/142923373ceb82823ffce0ddd26a796501c4fb60)，21:39:03 UTC。末次查询 21:40:13 UTC；合并理论目录 1351 份。

<a id="ref-otf5"></a>

\[2\] Trureturing， *OTF-005：轴面几何、相位纤维与内生闭合* ，尤其 C1–C7、§§6、9–10。<https://github.com/the-omega-institute/trureturing/blob/142923373ceb82823ffce0ddd26a796501c4fb60/docs/develop/theory/OTF_005_AXIS_PLANE_GEOMETRY_PHASE_FIBRES_AND_ENDOGENOUS_CLOSURE.md>。

<a id="ref-c128"></a>

\[3\] Trureturing， *C128：任意维原对象保持的静态量子重构* ，§§16–21：纯锚、原映射线性恢复、轴外距离、混态边界与隐藏直和反例。<https://github.com/the-omega-institute/trureturing/blob/840da33992b600d8d4808b04ff82dde323089212/docs/develop/theory/AURIC_C128_ARBITRARY_DIMENSIONAL_STATIC_QUANTUM_RECONSTRUCTION.md>。

<a id="ref-jbbridge"></a>

\[4\] Trureturing， *任意维小窗口的同一原单位桥* ，§§57–63：原 Jordan 图册、混合标准/反向嵌入与原值 $D$。<https://github.com/the-omega-institute/trureturing/blob/840da33992b600d8d4808b04ff82dde323089212/docs/develop/theory/AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE.md>。

<a id="ref-c139cont"></a>

\[5\] Trureturing， *C139：有限返回标定与负载稳定性续卷* ，末次关于完整 CountRead 支持和有限分组收敛的增补。<https://github.com/the-omega-institute/trureturing/blob/142923373ceb82823ffce0ddd26a796501c4fb60/docs/develop/theory/AURIC_C139_FINITE_RETURN_CALIBRATION_AND_LOAD_STABILITY_CONTINUATION.md>。

<a id="ref-c139cp"></a>

\[6\] Trureturing， *C139: Fixed-source comparators and native event boundary* ，定义 66.1、定理 67.1，第 68、74–85 节。 <https://github.com/the-omega-institute/trureturing/blob/840da33992b600d8d4808b04ff82dde323089212/docs/develop/theory/AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md>。

<a id="ref-v89"></a>

\[7\] Trureturing， *V89：平方闭合、递归稳定与关系量子场* ，第 4–7 节，UCP 背景下的乘法域。<https://github.com/the-omega-institute/trureturing/blob/840da33992b600d8d4808b04ff82dde323089212/docs/develop/theory/AURIC_SQUARE_CLOSURE_RECURSIVE_STABILITY_RELATIONAL_QUANTUM_FIELD_V89.md>。

<a id="ref-r522"></a>

\[8\] Trureturing， *R5-022：有向面积与三元返回* ，定理 2.2，第 9 节。<https://github.com/the-omega-institute/trureturing/blob/840da33992b600d8d4808b04ff82dde323089212/docs/develop/theory/AURIC_R5_022_ORIENTED_AREA_AND_TERNARY_RETURN.md>。

<a id="ref-otf4"></a>

\[9\] Trureturing， *OTF-004：内生观察、注意、控制与余弦反馈* ，第 2、6–7 节。<https://github.com/the-omega-institute/trureturing/blob/840da33992b600d8d4808b04ff82dde323089212/docs/develop/theory/OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md>。

<a id="ref-rodriguez"></a>

\[10\] Á. Rodríguez Palacios， *One-sided division absolute valued algebras* ，Publicacions Matemàtiques 36(2B) (1992), 925–954。<https://doi.org/10.5565/PUBLMAT_362B92_12>；作者机构原文目录与摘要 <https://ddd.uab.cat/record/60222>。其单侧除法理论包括内积范数结论与无限维左单位实例。

<a id="ref-baez"></a>

\[11\] J. C. Baez， *The Octonions* ，Bull. Amer. Math. Soc. 39 (2002), 145–205。 作者原稿 <https://math.ucr.edu/home/baez/octonions/octonions.pdf>。 合成代数、Clifford 关系、spinor 与射影几何的既有背景；本稿不认领这些一般结构的历史优先权。

<a id="ref-ashtekar"></a>

\[12\] A. Ashtekar and T. A. Schilling， *Geometrical Formulation of Quantum Mechanics* ，1997。 <https://arxiv.org/abs/gr-qc/9706069>。

<a id="ref-projector"></a>

\[13\] J. Mitscherling, A. Avdoshkin and J. E. Moore， *Gauge-invariant projector calculus for quantum state geometry and applications to observables in crystals* ，arXiv:2412.03637v2，2025-05-22 版本，§II.6.1。<https://arxiv.org/html/2412.03637v2>。

<a id="ref-berry"></a>

\[14\] M. V. Berry， *Quantal phase factors accompanying adiabatic changes* ，Proc. R. Soc. Lond. A 392 (1984), 45–57。 <https://doi.org/10.1098/rspa.1984.0023>；作者稿 <https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry120.pdf>。

<a id="ref-ding"></a>

\[15\] Z. Ding, Y. Deng, S.-M. Fei et al.， *Universal conservation laws of the wave-particle-entanglement triad: theory and experiment* ，Light: Science & Applications 14, 82 (2025)，2025-02-12。<https://doi.org/10.1038/s41377-025-01759-4>。

<a id="ref-siddiqui"></a>

\[16\] M. A. Siddiqui， *Entanglement inference from quantum erasure and path discrimination* ，arXiv:2611.02679v1，2026-11-02 预印本，§§II–IV 及相应补充材料。<https://arxiv.org/abs/2611.02679>；全文 <https://arxiv.org/pdf/2611.02679>。本稿不将预印本标作已同行评审。

<a id="ref-gogo05"></a>

\[17\] A. Gogo, W. D. Snyder and M. Beck， *Comparing quantum and classical correlations in a quantum eraser* ，Phys. Rev. A 71, 052103 (2005)。<https://doi.org/10.1103/PhysRevA.71.052103>；作者稿 <https://people.reed.edu/~beckm/QM/qe/qe.pdf>。

<a id="ref-toth05"></a>

\[18\] G. Tóth and O. Gühne， *Detecting Genuine Multipartite Entanglement with Two Local Measurements* ，Phys. Rev. Lett. 94, 060501 (2005)。<https://arxiv.org/abs/quant-ph/0405165>；<https://doi.org/10.1103/PhysRevLett.94.060501>。

<a id="ref-englert"></a>

\[19\] B.-G. Englert， *Fringe Visibility and Which-Way Information: An Inequality* ，Phys. Rev. Lett. 77 (1996), 2154。 <https://doi.org/10.1103/PhysRevLett.77.2154>。

<a id="ref-watrous"></a>

\[20\] J. Watrous， *The Theory of Quantum Information* ，Chapter 2，尤其 Theorem 2.22。 作者原稿 <https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf>。

<a id="ref-pw"></a>

\[21\] D. N. Page and W. K. Wootters，  *Evolution without evolution: Dynamics described by stationary observables* ，Phys. Rev. D 27 (1983), 2885–2892。 <https://doi.org/10.1103/PhysRevD.27.2885>。

<a id="ref-trinity"></a>

\[22\] P. A. Höhn, A. R. H. Smith and M. P. E. Lock，  *Trinity of relational quantum dynamics* ，Phys. Rev. D 104 (2021), 066001。 <https://arxiv.org/abs/1912.00033>。

<a id="ref-baumann"></a>

\[23\] V. Baumann and M. P. E. Lock， *Time delocalization and causality across temporal quantum reference frames* ，Phys. Rev. D 114, 086005 (2026)，2026-10-05。<https://doi.org/10.1103/9pl6-z9g4>。
