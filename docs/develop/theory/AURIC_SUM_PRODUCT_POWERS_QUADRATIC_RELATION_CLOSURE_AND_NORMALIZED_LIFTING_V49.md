> **原稿归属与转换说明。** 以下题名、摘要、正文、证明、表格、来源核对与生产过程陈述均归原稿作者 AURIC research continuation；“本轮取得”“实际通读”“核对”等措辞保留作者原有陈述，不表示 Markdown 编者实施了这些历史行为。编者补充单列为署名“编者注”，不替换原断言。原稿为完整 v49.0；保存源文件 UTF-8 41,344 字节，SHA-256 <code>62ca790aa1f871b2<wbr>bf6624d82ac04cf8<wbr>19288f801e7d0ce0<wbr>b46e557105be807d</code>。数学为纸面论证，未作 Lean 核验。

**原稿 PDF 元数据**

- 标题：AURIC：加乘指数、二次关系闭合与归一化升维
- 作者：AURIC research continuation
- 主题：Quadratic polarization, logarithmic odds, symmetric powers and source-specific square-law selection
- 原稿排版：XeLaTeX；11pt、A4、23mm 页边距、16pt 页眉高度；编译两遍；可用 `AURICFontPath` 指定 Noto CJK OTF 字体目录，依次采用 Noto Serif CJK SC 或 FandolSong；等宽字体 Latin Modern Mono。页眉左为“AURIC：加乘指数与二次关系闭合”，右为“v49 / 2026-10-31”，页脚为页码。标题两行间距 7pt，副题前间距 8pt，日期前间距 5pt；这些为版式参数，不是数学显示。

# AURIC：加乘指数、二次关系闭合<br>与归一化升维

**定义、定理与纸面证明　v49.0**

2026 年 10 月 31 日　Asia/Singapore

## 摘要
本文研究加法、乘法、幂与对数如何在二元关系及归一化中相容。
先区分运算元数、图像维数、齐次次数、特征空间维数及归一化态自由度，
说明按运算名称排列一维、二维、三维尚不是一个确定的维数定理。
平方的两个精确特征是：非负权重的叠加修正若实双线性，则权重必为二次型；
若关系保留振幅乘积、尺度权重兼容乘法且二元矩阵全域为正，则倒数关系强制平方权重。
完整二变量二次提升有三个对称特征，交叉项恰补足归一化；
一般整数 $m$ 次有 $m+1$ 个特征，但其非线性像、射影态域与环境空间维数不同。
Hermitian 二次提升则给出四个实量，经迹归一化形成三条 Bloch 轴。
本轮项目量子续卷 III 新增的自主过程定理先由整数回返导出共同赔率，
再由四角一致性及 log 得到一般幂律，最后由原生阻塞单点的概率守恒选择指数二。
全文区分此来源特定证明、抽象平方闭合以及高次复合读出，
并给出收缩前提下的酉误差拆分。数学全部采用纸面推导，
不运行数学程序、数值计算、CAS、枚举、Lean 或量子门搜索。

> **编者注（Markdown 编者）：正整数范围。** 摘要中“一般整数 $m$ 次”的特征计数按第 6 节定义的正整数 $m\ge1$ 理解；负整数不属于该多项式对称幂构造，零次也不具有随后所述的非零像局部二维性质。依据：原稿定义 6.1 与命题 6.4 的域。

<a id="section-1"></a>

## 1 固定项目、真正增量与研究对象

本轮只成功取得一次活动 `dev` 的 HEAD，随后固定为

<code>e168d4bbef773d94<wbr>df790275d1f4f2a9<wbr>e373103f</code>。

 提交时间为 2026-10-31 20:24:39（新加坡）。
相对上一轮固定的

<code>c292ab048b2a68d8<wbr>b318657b2c0e1d10<wbr>d2fdf189</code>，

 完整 theory 树含 1107 项，发现八个理论路径变更。
这里最相关的是量子续卷 III 追加 §§177–182，
以及新的收敛余量与酉误差递归稿。V14、V17、V19、V41 和无序相容原子稿
在这两个快照之间没有变化；它们是既有工具，不列为本轮新增。[1](#ref-head)、[2](#ref-compare)、[3](#ref-iii)、[8](#ref-residual)、[5](#ref-v14)、[4](#ref-v17)、[9](#ref-v19)、[6](#ref-v41)、[7](#ref-unordered)

本轮主张是：

> 平方是把线性叠加、双线性关系、非负权重和共同尺度归一化同时闭合起来的一种特殊次数。
> 这种特殊性必须由明确的代数或来源条件证明；运算名字、二元语法和总和为一并不单独选择它。

下文的自主过程结果是对项目新定理的条件保真整理；
极化、正矩阵、对称幂等是自足的标准数学推论与本题综合，
不主张这些工具的全球原创性。实际核对范围是所引用段落及其本轮差分，
不是整个仓库、全部旧引用或形式化依赖的认证。

采用用户的内生约定：向量、相位参考、观察者、记录、辅助槽位和调用索引
都属于同一个静态整体。引入数学直和、张量或过程参数不表示存在本体之外的对象，
也不自动证明相应参考、复合态或连续操作可以实际取得。

<a id="section-2"></a>

## 2 先把“维度”与逆运算定型

#### 定义 2.1（五种不同计数）

对于 $f:D\subseteq\mathbb{R}^k\to\mathbb{R}^\ell$，区分：
输入元数 $k$；关系图像的内在维数；图像所在环境维数 $k+\ell$；
多项式或缩放的齐次次数；用于完整表达一组关系的线性特征维数。
另须区分这些计数与归一化后可区分状态的实际自由度。

#### 命题 2.2（普通运算图像不随运算层级自动升维）

若 $D$ 是开集而 $f$ 光滑，则

$$
\Gamma_f=\{(x,f(x)):x\in D\}
$$

与 $D$ 微分同胚，因此内在维数为 $k$。

**证明。**

投影 $(x,f(x))\mapsto x$ 与 $x\mapsto(x,f(x))$ 互为光滑逆；
后者的导数含单位矩阵块，秩恒为 $k$。

□

| 对象 | 标量输入数 | 图像内在维数 | 图像环境维数 |
| --- | --- | --- | --- |
| $x+y$，$xy$ | 2 | 2 | 3 |
| $x^2$，固定整数 $m$ 的 $x^m$ | 1 | 1 | 2 |
| 固定 $a>0,\ a\ne1$ 的 $a^x$ | 1 | 1 | 2 |
| $x^y$，$x>0,\ y\in\mathbb{R}$ | 2 | 2 | 3 |

例如 $xy$ 的齐次次数为二，但其输出只有一个标量；
$x^2$ 的图像是一维曲线；二变量完整二次特征却有三个坐标。
若用超立方体体积解释 $x^m$，$m$ 是所选几何模型的维数，
平方对应面积而非体积。不同定义之间不能只按名字递进。
后文会给“平方对应三维”的两种准确版本。

> **编者注（Markdown 编者）：图像域与零次幂。** 运算图像表采用各函数的实开定义域：负整数幂在 $\mathbb{R}\setminus\{0\}$ 上，非负整数幂在 $\mathbb{R}$ 上。若自然数约定包含零，有限加乘命题中的零次幂取空积 $x^0=1$；这是常数多项式的约定。依据：图像命题的开域前提及有限乘积定义。

#### 命题 2.3（有限加乘表达的范围）

有限个实或复常数与变量经过有限次加法、乘法，所得函数为多项式。
固定自然数幂可由此表达；一般变量指数 $x^y$ 需要另给指数函数、极限或其他结构。

**证明。**

按表达式树归纳，常数和变量为多项式，多项式的和与积仍为多项式。
固定 $m$ 的 $x^m$ 是 $m$ 个因子的积。
若 $x^y$ 可在 $x>0,y\in\mathbb{R}$ 上由有限加乘表达，固定 $x=e$
便得到一个多项式等于 $e^y$；取高于其次数的导数，左边为零、右边非零，矛盾。

□

| 要求解的关系 | 逆运算及必须保留的域 |
| --- | --- |
| $x+a=b$ | $x=b-a$；实数上无额外除零条件 |
| $ax=b$ | $a\ne0$ 时 $x=b/a$；$a=0$ 时应另分无解或多解 |
| $a^x=b$ | $a>0,\ a\ne1,\ b>0$ 时 $x=\log b/\log a$ |
| $x^a=b$ | 在 $x>0$ 上，$a\ne0,\ b>0$ 时 $x=b^{1/a}$ |
| $x^2=b$ | 实数域要求 $b\ge0$；$b>0$ 有两个符号分支，限制 $x\ge0$ 后才唯一 |

减法、除法和 log 都可承担逆运算，但必须说清固定哪个变量。
零、单位底数、平方的符号丢失以及复对数的分支均是关系的一部分。

> **编者注（Markdown 编者）：逆运算退化情形。** 逆运算表的退化情形为：$a=0$ 的 $ax=b$ 在 $b=0$ 时任意实 $x$ 都解，在 $b\ne0$ 时无解；$a=1$ 的 $a^x=b$ 在 $b=1$ 时任意实 $x$ 都解，其余无解；零底数不在该行 $a>0$ 的域内。在 $x>0$ 的幂方程中，$a=0$ 时同样由 $b=1$ 区分全解与无解。实平方在 $b=0$ 时只有 $x=0$，在 $b<0$ 时无解。依据：把这些值代回各原方程。

<a id="section-3"></a>

## 3 log 把乘法化为加法，也把一般权重分类成幂

#### 定理 3.1（对数半环坐标）

<a id="thm:log"></a>

在 $\mathbb{R}\cup\{-\infty\}$ 上定义

$$
u\oplus v=\log(e^u+e^v),\qquad u\odot v=u+v,
$$

并约定 $e^{-\infty}=0$，$\log0=-\infty$，$-\infty\odot u=-\infty$。
则 log 与 exp 给出

$$
(\mathbb{R}_{\ge0},+,\times)
\cong
(\mathbb{R}\cup\{-\infty\},\oplus,\odot).
$$

在正实数域，

$$
\log(ab)=\log a+\log b,\quad
\log(a/b)=\log a-\log b,\quad
\log(a^t)=t\log a.
$$

**证明。**

逐项使用指数乘法公式；零由约定处理。log 与 exp 互逆，
因此结合、交换、分配以及单位结构均随坐标变换转移。

□

这是 V17 §2 的既有精确桥。[4](#ref-v17)
它没有把原加法与原乘法变成同一个运算：
原加法变成 log-sum-exp，原乘法才变成普通加法。
两个运算也不会仅凭该坐标转换成为两条正交轴；正交性还需要度量。

#### 定理 3.2（乘法兼容权重的幂分类）

<a id="thm:character"></a>

若连续 $w:(0,\infty)\to(0,\infty)$ 满足

$$
w(rs)=w(r)w(s),\qquad w(1)=1,
$$

则存在 $\beta\in\mathbb{R}$ 使 $w(r)=r^\beta$。
若连续延伸到零且 $w(0)=0$，则 $\beta>0$。

**证明。**

令 $g(t)=\log w(e^t)$，则 $g(s+t)=g(s)+g(t)$。
可加性先给 $g(q)=qg(1)$ 对全部有理数成立，连续性给全部实数上的同式。
令 $\beta=g(1)$ 即得结论。若 $\beta=0$，零点极限为一；
若 $\beta<0$，该极限发散，均与 $w(0)=0$ 矛盾。

□

#### 推论 3.3（增加欧氏正交合并，才选择二）

在定理 [3.2](#thm:character) 下，若另要求

$$
w\bigl(\sqrt{r^2+s^2}\bigr)=w(r)+w(s)\qquad(r,s>0),
$$

则 $\beta=2$。

**证明。**

取 $r=s=1$，得到 $2^{\beta/2}=2$。

□

因此 log 负责揭示一般指数，正交合并条件负责选择指数。
对任意 $\beta>0$，$\frac{a^\beta}{a^\beta+b^\beta}$ 都是合法的二结果归一化数值，
并满足

$$
\log\frac{p_\beta}{1-p_\beta}=\beta\log\frac ab.
$$

这些事实本身没有选出 $\beta=2$。

> **编者注（Markdown 编者）：赔率的正数域。** 上述有限 log 赔率等式使用 $a,b>0$。允许非负端点但排除 $a=b=0$ 时，归一概率仍有定义；$a=0$ 或 $b=0$ 分别给 $p_\beta=0$ 或 $1$，有限 log 赔率则须改作扩展实数极限。依据：原分式分母与实 log 的定义域。

#### 命题 3.4（复 log 的全局障碍）

不存在 $L:\mathbb{C}^\times\to\mathbb{C}$ 同时满足
$e^{L(z)}=z$ 和 $L(zw)=L(z)+L(w)$ 对全部非零复数成立。

**证明。**

同态条件给 $L(1)=0$，而 $(-1)^2=1$ 给 $2L(-1)=0$，
所以 $L(-1)=0$，与 $e^{L(-1)}=-1$ 矛盾。

□

这个反证不需要连续性。复指数的核是 $2\pi i\mathbb Z$；
局部 log 的虚部需要分支，沿路径的未缠绕相位需要保留绕数。
绕数是覆盖或历史信息，不能只从终点恢复，也不是新添的一条连续空间轴。

<a id="section-4"></a>

## 4 平方的第一种唯一性：非负二元双线性关系闭合

#### 定义 4.1（叠加修正）

设 $V$ 为实向量空间，$Q:V\to[0,\infty)$ 且 $Q(0)=0$。
定义

$$
C_Q(u,v)=\frac{Q(u+v)-Q(u)-Q(v)}2.
$$

它是两个输入合并时超出各自权重之和的关系贡献。

#### 定理 4.2（非负权重的双线性闭合）

<a id="thm:closure"></a>

若 $C_Q$ 对两变量实双线性，则

$$
\boxed{Q(v)=C_Q(v,v)}
$$

且 $C_Q$ 为对称半正定双线性形式。
反之，每个对称半正定双线性形式 $B$ 通过 $Q(v)=B(v,v)$ 给出 $C_Q=B$。
若 $Q(v)>0$ 对所有 $v\ne0$ 成立，则得到实内积。

**证明。**

由定义 $C_Q$ 对称。记 $B=C_Q$，置
$L(v)=Q(v)-B(v,v)$。
展开 $Q(u+v)$ 与 $B(u+v,u+v)$，得到 $L(u+v)=L(u)+L(v)$。
故对每个正整数 $n$，

$$
0\le Q(\pm v/n)=\frac{B(v,v)}{n^2}\pm\frac{L(v)}n.
$$

两式给 $B(v,v)\ge n\vert L(v)\vert$，对任意 $n$ 成立，只能有 $L(v)=0$。
于是 $Q(v)=B(v,v)\ge0$。反向直接展开二次型即可。

□

这里不预设 $Q$ 的连续性、偶性或二次齐次性；它们中相应的二次代数结构来自结论。
但“实双线性”本身是一个明确前提，不能降为“可以写成两个输入的函数”。
事实上任何高阶多项式都能用二元加乘门表达；二元语法并不保证二阶关系闭合。

#### 命题 4.3（幂函数的同一检验）

在非零实内积空间上令 $Q_\beta(v)=\Vert v\Vert ^\beta$，$\beta>0$。
若 $C_{Q_\beta}$ 实双线性，则 $\beta=2$。

**证明。**

取单位向量 $e$。由 $Q_\beta(0)=0$，
$C_{Q_\beta}(e,-e)=-1$。双线性给 $C_{Q_\beta}(e,e)=1$；
另一方面它等于 $(2^\beta-2)/2$，故 $2^\beta=4$。

□

#### 命题 4.4（范数的平行四边形与极化）

设 $Q(v)=\Vert v\Vert ^2$ 来自实范数，且

$$
Q(u+v)+Q(u-v)=2Q(u)+2Q(v).
$$

则唯一产生该范数的内积为

$$
g(u,v)=\frac{Q(u+v)-Q(u-v)}4.
$$

**证明。**

对 $Q$ 的平行四边形律分别应用于 $(x+y,z)$ 与 $(x-y,z)$，
相减得到
$g(x+z,y)+g(x-z,y)=2g(x,y)$。
取 $z=x$ 得 $g(2x,y)=2g(x,y)$；
再令 $x=(u+v)/2,z=(u-v)/2$，得第一变量可加。
范数连续性将有理齐次延伸为实齐次。由 $Q$ 偶性得对称，
由范数齐次性得 $g(v,v)=Q(v)$，正定性随之成立。
任何产生该范数的内积展开后都满足这条极化式，故唯一。

□

若仅给任意非负函数的平行四边形律，不能略掉上述正则性：
不连续可加函数 $L:\mathbb{R}\to\mathbb{R}$ 所给 $Q(x)=L(x)^2$ 仍满足该律，
却未必是关于实标量的二次型。

#### 命题 4.5（实关系、复关系与手性的范围）

给实内积 $g$，另给正交复结构 $J$，即 $J^2=-I$ 且 $J$ 保内积。
以第一变量共轭线性为约定，置

$$
h(u,v)=g(u,v)+i\,g(Ju,v).
$$

则 $h$ 是相容复内积，且 $h(v,v)=g(v,v)$。
在已给复标量结构时，

$$
h(u,v)=\frac14\{Q(u+v)-Q(u-v)-iQ(u+iv)+iQ(u-iv)\}.
$$

**证明。**

正交性与 $J^2=-I$ 给 $g(Ju,v)=-g(u,Jv)$，
逐项核对 Hermitian 对称以及第一变量的 $i$ 乘法规则。
由反对称性 $g(Jv,v)=0$。最后展开四个平方，分别提取实部和虚部即可。

□

将 $J$ 换成 $-J$，$h$ 复共轭而 $Q$ 不变。
所以平方自身恢复实度量，不单独选择手性方向。

<a id="section-5"></a>

## 5 平方的第二种唯一性：正关系矩阵、乘法与倒数

#### 定理 5.1（二元正性与倒数选出平方）

<a id="thm:positive"></a>

设 $w:(0,\infty)\to(0,\infty)$ 满足
$w(rs)=w(r)w(s)$、$w(1)=1$。
对全部非零 $z_1,z_2\in\mathbb{C}$，要求

$$
G_w(z_1,z_2)=
\begin{pmatrix}
w(\vert z_1\vert )&\overline{z_1}z_2\\
\overline{z_2}z_1&w(\vert z_2\vert )
\end{pmatrix}\succeq0.
$$

则 $w(r)=r^2$ 对所有 $r>0$ 成立，无需连续性。

**证明。**

取 $(z_1,z_2)=(r,1)$，行列式非负给 $w(r)\ge r^2$。
对 $1/r$ 同理得 $w(1/r)\ge r^{-2}$。
但乘法条件给 $w(r)w(1/r)=1$，所以 $w(r)\le r^2$。
两向合并即得结论。平方情形的矩阵本来就是秩一正 Gram 矩阵。

□

该证明准确使用了用户所指的逆关系：除法或倒数把一个方向的不等式
变成另一个方向的不等式。其结构前提也很明确：
非对角项被规定为通常的振幅乘积，而非任意可重新定义的“关系”。

#### 命题 5.2（归一化中的次数匹配）

<a id="prop:scale"></a>

若对角权重为 $\vert z_j\vert ^\beta$，非对角关系仍为
$\overline{z_1}z_2$，则共同正尺度变换 $z_j\mapsto\lambda z_j$
使归一化后的非对角项乘上 $\lambda^{2-\beta}$。
要求所有非零关系在共同尺度归一化后不变，迫使 $\beta=2$。

**证明。**

对角总量乘 $\lambda^\beta$，非对角项乘 $\lambda^2$，取商即得。
取非零关系且任意 $\lambda>0$，比例恒一当且仅当 $\beta=2$。

□

而且 $\beta\ne2$ 的这种混合次数矩阵不能在全部尺度为正：
取 $z_1=z_2=t>0$，

$$
\det G_\beta=t^{2\beta}-t^4.
$$

$\beta>2$ 时取 $0<t<1$，$0<\beta<2$ 时取 $t>1$，
均得到负行列式。

> **编者注（Markdown 编者）：混合次数的实指数域。** 次数匹配命题在 $z_1z_2\ne0$、$\beta\in\mathbb{R}$ 时有正的对角总量。若“$\beta\ne2$”涵盖全部实指数，原行列式论证的余下 $\beta\le0$ 情形也取 $t>1$：$t^{2\beta}\le1<t^4$，故行列式仍负；下一命题另行限定 $\beta>0$，才能在零点按给定方式连续延拓。依据：原行列式及 $F_\beta$ 的模长。

#### 命题 5.3（改写成平方不等于保留线性振幅）

对 $\beta>0$ 定义

$$
F_\beta(z)=
\begin{cases}\vert z\vert ^{\beta/2-1}z,&z\ne0,\\0,&z=0.\end{cases}
$$

则 $\vert F_\beta(z)\vert ^2=\vert z\vert ^\beta$，且
$F_\beta(zw)=F_\beta(z)F_\beta(w)$。
但 $F_\beta$ 保持加法当且仅当 $\beta=2$。

**证明。**

前两式由模长与相位的乘法规则直接成立。
若保持加法，取 $z=w=1$ 得 $2^{\beta/2}=2$，故 $\beta=2$；
此时映射为恒等映射，反向成立。

□

因此任意幂权重都可重新参数化为某个新变量的平方；
真正要保持的是原有线性叠加及关系。平方的特殊性发生在这些兼容条件的交点。

<a id="section-6"></a>

## 6 两个振幅的完整整数幂提升

#### 定义 6.1（对称幂特征）

对整数 $m\ge1$，定义

$$
\Phi_m(a,b)=
\left(\sqrt{\binom mk}\,a^{m-k}b^k\right)_{k=0}^{m}
\in\mathbb{C}^{m+1}.
$$

这是 $\operatorname{Sym}^m(\mathbb{C}^2)$ 的标准正交特征坐标；
实数输入给 $\mathbb{R}^{m+1}$ 中的相应构造。

#### 定理 6.2（完整特征维数与归一化）

<a id="thm:sym"></a>

对所有 $z,w\in\mathbb{C}^2$，

$$
\boxed{\langle\Phi_m(z),\Phi_m(w)\rangle=\langle z,w\rangle^m},
\qquad
\boxed{\Vert \Phi_m(z)\Vert ^2=\Vert z\Vert ^{2m}}.
$$

其像的复线性包络维数恰为 $m+1$。

**证明。**

写 $z=(a,b),w=(c,d)$，采用第一变量共轭线性的内积。
二项式定理给

$$
\sum_{k=0}^m\binom mk
\overline a^{\,m-k}\overline b^{\,k}c^{m-k}d^k
=(\overline ac+\overline bd)^m.
$$

取 $w=z$ 得范数式。
若线性包络维数不足，则存在非零系数使
$\sum_{k=0}^m d_k a^{m-k}b^k=0$ 对所有 $a,b$ 成立；
取 $a=1$，恒零多项式的全部系数只能为零，矛盾。

□

#### 推论 6.3（平方的第三特征恰补足归一化）

<a id="cor:three"></a>

若 $\vert a\vert ^2+\vert b\vert ^2=1$，则

$$
\Phi_2(a,b)=(a^2,\sqrt2\,ab,b^2),\qquad
\vert a^2\vert ^2+\vert \sqrt2\,ab\vert ^2+\vert b^2\vert ^2=1.
$$

只保留 $(a^2,b^2)$ 时，平方范数少掉 $2\vert a\vert ^2\vert b\vert ^2$。

**证明。**

展开 $(\vert a\vert ^2+\vert b\vert ^2)^2$ 即得。

□

这给出用户“平方三维”的一个正面准确版本：
两个纯平方特征与一个交叉关系特征，组成完整二次对称表示。
一般整数 $m$ 次共有 $m+1$ 个特征；若写成 $N+2$，只能明确规定 $N=m-1$，
这只是重编号，不能由此认定指数本身具有 $N+2$ 个物理维度。
单独计算 $(a+b)^m$ 只输出一个数，也不需要把所有特征作为独立输出。

#### 命题 6.4（完整空间、非线性像与射影自由度）

对 $m\ge1$，$\Phi_m(\mathbb{C}^2\setminus\{0\})$ 的局部复维数为二；
取非零复尺度之商，得到

$$
[a:b]\longmapsto
\left[\sqrt{\binom mk}a^{m-k}b^k\right]_{k=0}^m
$$

的射影像，复维数为一、实维数为二。
它的线性包络为 $\mathbb{C}^{m+1}$。当 $m>1$ 时，射影像不是整个该空间的纯态域；
$m=1$ 时则是整个 $\mathbb{CP}^1$。

**证明。**

在 $a\ne0$ 的图中，第二坐标与第一坐标之比是 $\sqrt m\,b/a$，
第一坐标是 $a^m$；在非零 $a$ 附近，$a\mapsto a^m$ 的导数非零，
故局部有两个复参数。$b\ne0$ 的图同理。
射影后只剩 $b/a$ 这个复参数，并能由特征比恢复；两图覆盖全部射影直线。

□

#### 命题 6.5（高幂读出与条件化）

设整数 $m\ge1$，归一化 $\psi=(a,b),\phi\in\mathbb{C}^2$，则

$$
\vert \langle\phi^{\otimes m},\psi^{\otimes m}\rangle\vert ^2
=\vert \langle\phi,\psi\rangle\vert ^{2m}.
$$

若只保留 $\Phi_m(a,b)$ 的两个端点扇区，则成功权重为

$$
s_m=\vert a\vert ^{2m}+\vert b\vert ^{2m},
$$

第一端点的条件概率为 $\vert a\vert ^{2m}/s_m$。
$m>1$ 且 $ab\ne0$ 时，$s_m<1$。

**证明。**

张量内积逐因子相乘，得到第一式。
端点投影的平方范数就是 $s_m$，条件化后再除以它。
完整二项式展开还含正的中间项，故端点权重严格小于一。

□

这里的 $2m$ 来自 $m$ 份复合振幅再取普通平方。
它没有把基础读出改成另一个概率公理；丢弃的混合扇区也不能被称为无成本归一化。

#### 命题 6.6（特征提升不提供单份未知态的复制门）

当 $m>1$ 时，不存在对所有单位 $\psi$ 都满足
$V\psi=\psi^{\otimes m}$ 的线性等距映射 $V$。

**证明。**

取两单位态使 $0<\vert \langle\psi,\phi\rangle\vert <1$。
等距性要求该模长不变，而目标的模长为
$\vert \langle\psi,\phi\rangle\vert ^m$，严格更小，矛盾。

□

对称幂的物理使用因此需要已供应的多份制备或明确的编码来源。
若 $U$ 已给，则 $U^{\otimes m}$ 在对称子空间上诱导酉变换；
这只给诱导操作族，不等于取得整个 $U(m+1)$ 或通用控制。

<a id="section-7"></a>

## 7 三维的第二个来源：Hermitian 二次关系与归一化

#### 定理 7.1（二元正矩阵的三轴表示）

<a id="thm:bloch"></a>

设

$$
M=\begin{pmatrix}A&C\\\overline C&B\end{pmatrix}\succeq0,\qquad
N=A+B>0.
$$

采用标准 Pauli 矩阵，定义

$$
r=\frac{(2\Re C,-2\Im C,A-B)}N.
$$

则

$$
\frac MN=\frac{I+r\cdot\sigma}{2},\qquad
1-\Vert r\Vert ^2=\frac{4(AB-\vert C\vert ^2)}{N^2}\ge0.
$$

**证明。**

逐项比较矩阵元素即得表示；

$$
N^2-\{4\vert C\vert ^2+(A-B)^2\}=4(AB-\vert C\vert ^2).
$$

正矩阵的行列式非负，结论随之成立。

□

对两个复振幅 $z=(a,b)$，取 $M=zz^\dagger$，于是 $C=a\bar b$。
设

$$
X=2\Re(\bar a b),\quad
Y=2\Im(\bar a b),\quad
Z=\vert a\vert ^2-\vert b\vert ^2,\quad
N=\vert a\vert ^2+\vert b\vert ^2.
$$

则

$$
\boxed{X^2+Y^2+Z^2=N^2}.
$$

三个归一坐标为 $(X,Y,Z)/N$。四个实 Hermitian 二次量减去一个迹条件，
得到三轴表示；纯态还受球面条件约束，所以只有两个实自由度。
允许一般正矩阵或凸混合后才得到整个三维球。
这个区别与 V41 §4 的齐次正锥、Gram 分类完全相容。[6](#ref-v41)

> **编者注（Markdown 编者）：Gram 约定与共同酉商。** 按第一变量共轭线性的约定，第 5 节振幅 Gram 的上右元为 $\overline a b$，本节 $zz^\dagger$ 的上右元为 $a\overline b$；两矩阵互为转置，不能沿用同一上右元而省去 Bloch 第二轴的负号。V41 定理 4.4 所分类的是同一记录空间中的有序向量对，取共同记录酉作用的商；这不把有固定 Pauli 参考轴的全部二能级态再按任意二能级酉作用等同，也不保留相对额外参考或未来读口的方向。依据：原稿定理 7.1 的矩阵元素及固定引用 V41 §§4.1、4.4。

| 二次构造 | 空间类型与剩余约束 |
| --- | --- |
| 实对称平方 $(x^2,\sqrt2xy,y^2)$ | 环境 $\mathbb{R}^3$；满足 $B^2=2AC$；若 $x^2+y^2=1$，还满足 $A+C=1$，像为一维圆 |
| 复对称平方 $(a^2,\sqrt2ab,b^2)$ | 环境 $\mathbb{C}^3$；射影像为实二维的 Veronese 曲线，非整个 qutrit 纯态域 |
| Hermitian 平方 $zz^\dagger$ | 四个实系数；迹归一化后三轴；秩一时球面，混合时球内 |

实对称平方中的一维圆可直接验证：
由 $A+C=1$ 和 $A^2+B^2+C^2=1$ 得 $B^2=2AC$；
两个端坐标位于 $[0,1]$，故整个交圆由相应 $(x,y)$ 实现。
这不能与 Bloch 球的三维内部混称。

#### 定理 7.2（加法、乘法、对数差与圆）

<a id="thm:hyperbolic"></a>

对 $A,B>0$，令

$$
S=A+B,\quad P=AB,\quad
\delta=\tfrac12(\log A-\log B).
$$

则

$$
\frac{A-B}{S}=\tanh\delta,\qquad
\frac{2\sqrt P}{S}=\operatorname{sech}\delta,
$$

因而

$$
\left(\frac{A-B}{A+B}\right)^2+
\left(\frac{2\sqrt{AB}}{A+B}\right)^2=1.
$$

**证明。**

置 $h=(\log A+\log B)/2$，则
$A=e^{h+\delta},B=e^{h-\delta}$，
$S=2e^h\cosh\delta$，$\sqrt P=e^h$，取商即得。
平方和也可由 $(A-B)^2+4AB=(A+B)^2$ 直接证明。

□

若 $A=\vert a\vert ^2,B=\vert b\vert ^2$，并另给内部相位
$\theta=\arg b-\arg a$，则

$$
r=(\operatorname{sech}\delta\cos\theta,\ \operatorname{sech}\delta\sin\theta,\ \tanh\delta).
$$

归一化消去共同尺度 $e^h$，留下相对偏置与相位。
正数 $A,B$ 或它们的 log 本身不提供 $\theta$。
零振幅处不定义有限 log 坐标，应以极限或另一张坐标图处理。

<a id="section-8"></a>

## 8 二阶关系、干涉与上一轮 Clifford 接口

#### 命题 8.1（固定分支的二阶闭合）

给正二次型 $Q(v)=g(v,v)$ 与固定分支向量 $v_1,v_2,v_3$，
令 $\mu(S)=Q(\sum_{j\in S}v_j)$，$\mu(\varnothing)=0$。
则

$$
\begin{split}
I_3={}&\mu(123)-\mu(12)-\mu(13)-\mu(23)\\
&+\mu(1)+\mu(2)+\mu(3)=0.
\end{split}
$$

**证明。**

展开二次型，每个单体项的系数为 $1-2+1=0$，
每个两两关系项的系数为 $1-1=0$。

□

例如取标量非负权重 $Q(x)=\vert x\vert ^3$ 和三个相同的单位实输入，
相应 $I_3=27-3\cdot8+3=6$。
所以高次权重一般引入超出固定二阶展开的项。
但是“全子集权非负且 $I_3=0$”仍不足以得到正 Gram 核：
V14 §10 给出了相应不定二次型反例。[5](#ref-v14)
这里不把不同装置中改变后的分支向量强行当作同一族。

#### 命题 8.2（平方与 Clifford 对称部分）

在任意含单位结合代数中，

$$
(u+v)^2-u^2-v^2=uv+vu.
$$

设 $V$ 是该含单位实或复结合代数中的实线性子空间；
若对每个 $v\in V$ 均规定 $v^2=Q(v)1$，且 $Q(v)=g(v,v)$，
则对所有 $u,v\in V$，

$$
\boxed{uv+vu=2g(u,v)1}.
$$

**证明。**

由分配律展开；对 $Q(u+v)$ 使用极化关系。

□

这接回上一轮的量子代数路线：平方控制乘积的对称部分，

$$
uv=g(u,v)1+\tfrac12[u,v].
$$

反对称部分还需要另外结构；在三维 Clifford 模型中才进一步写成
$\iota(u\times v)$。[7](#ref-unordered)

> **编者注（Markdown 编者）：对称双线性前提。** Clifford 命题中的 $g$ 须沿用第 4 节的对称实双线性形式。若仅知道 $Q(v)=g(v,v)$ 而不规定对称双线性，展开不能推出所写的 $2g(u,v)$；对一般双线性形式只给 $g(u,v)+g(v,u)$。若还要由标量乘 $1$ 的等式反推标量相等，另需非零含单位代数的忠实标量嵌入。依据：直接展开 $g(u+v,u+v)$；固定引用无序相容原子稿定义 4.1 使用正定内积。

各向同性可限制 $g$ 和允许的关系张量，但不能用“二元”一词替代双线性、
正性、复结构或结合复合。

<a id="section-9"></a>

## 9 项目新进展：先导出幂律，再选择平方

<a id="sec:native"></a>

本节消费冻结快照中续卷 III 新增 §§177–179，
而不是重新把旧的正交可加定理称为最新结果。[3](#ref-iii)
下面完整列出密度选择的承重条件，并给出相关证明链。

<a id="section-9-1"></a>

### 9.1 固定来源与未知密度

原配置集为

$$
E=\{q\subseteq\{1,\ldots,9\}:q\text{ 不含相邻整数}\},
\qquad \vert E\vert =89,\qquad \mathcal K=\mathbb{C}^E.
$$

固定边界为 $b_{-1}b_0=10$、$b_{10}b_{11}b_{12}=010$，
沿用原十一地址；对 $1\le j\le9$，
可翻转分量是按中心占位 $0,1$ 排序的二点块，阻塞分量是单点。
共同的活动块为

$$
Q=\begin{pmatrix}x&c\\c&x^2\end{pmatrix},\qquad
x+x^2=1,\quad x>0,\quad y=\sqrt x,\quad c=xy>0.
$$

故 $Q^2=Q$，$\operatorname{Tr} Q=1$。
原全空间投影为 $\mathcal P_j$，并给定

$$
H_j=-\alpha(I+\mathcal P_j),\quad
\alpha=3\pi/5,\quad
U_j(t)=e^{i\alpha t}\{I+(e^{i\alpha t}-1)\mathcal P_j\}.
$$

端点地址为 $\mathcal P_0=n_1,\mathcal P_{10}=n_9$，其分量均为单点；
$n_j$ 是第 $j$ 位占位投影，内部地址的活动块为这个 $Q$。
未知量是连续密度

$$
\Pi:\mathbb P(\mathcal K)\longrightarrow\Delta(E),\qquad
\Pi_q(z)=0\iff z_q=0.
$$

它对全部非零复尺度不变，且在全数学射线域定义。
尚未假设逐坐标幂律、径向性、可分性或赔率的背景无关性。

#### 定义 9.1（来源条件 A 与 B）

**A：** 每个原活动块使用同一对在非节点局部射线上连续、有限、非负的强度
$\gamma_\pm$。给定完整隐藏过去后，强度只依当前局部射线，
不依地址、块号、旁观幅度、调用年龄或其他记忆。
存在含节点合法接续的适定因果纯跳 Markov 族；不跨块、单点保持；
同址整数调用不重抽、不复位。
对每个数学输入和每个内部数学时刻，
配置边缘等于同一个未知函数 $\Pi(U_j(t)z)$。

**B：** 每条模长非恒定、并在十次同址调用内避开两个局部坐标节点的轨道，
满足

$$
\int_0^{10}(\gamma_++\gamma_-)(\ell(t))\,dt>0.
$$

这些是动态与全域相容前提。数学上的所有射线和所有内部时刻
不等于已经具有实际任意制备或任意停止权限。

<a id="section-9-2"></a>

### 9.2 回返与四角关系导出权重形状

#### 命题 9.2（整数回返与安全轨道）

原同址十调用满足 $U_j(10)=I$。
在局部射影直线中，模长不恒定且永不碰节点的起点构成稠密集。

**证明。**

$10\alpha=6\pi$，代入 $U_j$ 立即得到回返。
写 $Q=(I+n\cdot\sigma)/2$，其中
$n=(2c,0,x-x^2)$ 为单位向量且不平行于 $e_z$。
局部 Bloch 轨道绕 $n$ 旋转。模长恒定的仅为两个特征方向 $\pm n$；
经过两个坐标节点的起点分别在
$n\cdot r=\pm(x-x^2)$ 的两条圆上。
去掉两条圆与两个点后的集合稠密，并满足所需条件。
此处使用内部数学轨道判定安全性，不取得额外可执行分数调用。

□

#### 定理 9.3（回返收缩产生共同赔率）

在 A+B 下，存在连续正函数 $\mathcal O:\mathbb{C}^\times\to(0,\infty)$，
对每条原定向边 $q_0\to q_1$ 有

$$
\frac{\Pi_{q_1}(z)}{\Pi_{q_0}(z)}
=\mathcal O(z_{q_1}/z_{q_0})
\qquad(z_{q_0}z_{q_1}\ne0).
$$

**证明。**

先固定安全局部起点，比较具有同一局部射线的两个背景。
A 给相同的连续有界强度 $a(t),b(t)$。
由于块质量为正且保持，条件概率 $Y$ 满足

$$
Y'=a(t)(1-Y)-b(t)Y.
$$

两解之差为

$$
D(t)=D(0)\exp\left(-\int_0^t(a+b)(s)\,ds\right).
$$

十调用的全向量回返与等变性给每个 $Y(10)=Y(0)$，
B 使差值乘子严格小于一，因此 $D(0)=0$。
用固定参考边 $\varnothing\to\{1\}$ 的两点支撑输入定义 $\mathcal O$。
未知密度的连续性和节点外严格正性使它连续正。
安全起点稠密，保持旁观幅度不变而逼近任意非节点局部射线，
便将赔率等式延伸到全部非节点输入。

□

这个收缩比较的是同一局部轨道上的两种条件概率解，
没有声称两个全量子态在同一个酉作用下距离缩小。

#### 定理 9.4（四角一致性与 log 选择一般幂族）

<a id="thm:nativepower"></a>

在以上条件下，存在 $k>0,\beta>0$ 使

$$
\mathcal O(w)=k\vert w\vert ^\beta,\qquad
\Pi_q(z)=
\frac{k^{\vert q\vert }\vert z_q\vert ^\beta}
{\sum_{r\in E}k^{\vert r\vert }\vert z_r\vert ^\beta}.
$$

**证明。**

原合法图包含四角
$\varnothing,\{1\},\{1,3\},\{3\}$。
令它们的非零幅度分别为 $a,b,c_0,d_0$。
沿两条路径计算同一赔率，得到

$$
\mathcal O(b/a)\mathcal O(c_0/b)
=\mathcal O(d_0/a)\mathcal O(c_0/d_0).
$$

取 $a=d_0=1,b=s,c_0=st$，得
$\mathcal O(s)\mathcal O(t)=\mathcal O(1)\mathcal O(st)$。
置 $k=\mathcal O(1)$，则 $F=\mathcal O/k$ 为连续正乘法特征。
相位圆的像为正乘法群中的紧子群，因非一元素或其逆的正整数幂无界，
该像只能为 $\{1\}$。故 $F(w)=F(\vert w\vert )$。
取 $\log F(e^t)$ 得连续可加函数，定理 [3.2](#thm:character) 给
$F(w)=\vert w\vert ^\beta$。

原单比特合法翻转图连通：删除占据位始终合法且最终到达空集。
每加一个位使 $\vert q\vert$ 增一，因此全支撑输入上
$\Pi_q/(k^{\vert q\vert }\vert z_q\vert ^\beta)$ 对全部 $q$ 相同。
归一化给所述公式。
让一个坐标趋于零、其余保持非零；若 $\beta=0$，
该坐标概率不趋零，若 $\beta<0$ 则趋于一，均违反节点连续性。
故 $\beta>0$，其公式在全部非零向量上连续，全支撑稠密性完成延拓。

□

<a id="section-9-3"></a>

### 9.3 原生旁观单点的守恒选择指数二

#### 定理 9.5（来源特定的平方选择）

<a id="thm:nativesquare"></a>

条件 A+B 蕴含

$$
\boxed{\Pi_q(z)=\frac{\vert z_q\vert ^2}{\Vert z\Vert ^2}}
\qquad(q\in E,\ z\ne0).
$$

**证明。**

由定理 [9.4](#thm:nativepower)，只需确定 $k,\beta$。
取原地址一的活动块
$u=\varnothing,v=\{1\}$，以及原有的阻塞单点 $r=\{2\}$。
令只有这三个幅度非零，分别为 $a,b,h$，$h\ne0$。
单点的幅度模长及配置概率都保持，因此

$$
\frac{k\vert h\vert ^\beta}
{\vert a(t)\vert ^\beta+k\vert b(t)\vert ^\beta+k\vert h\vert ^\beta}
$$

恒定。正的固定分子迫使
$\vert a(t)\vert ^\beta+k\vert b(t)\vert ^\beta$ 恒定。

此时幂形已经证明，故可在 $ab\ne0$ 上求导。
由原块方程 $\dot v=i\alpha(I+Q)v$，令
$J=2\alpha c\,\Im(\bar a b)$，则

$$
\frac d{dt}\vert b\vert ^2=J,\qquad
\frac d{dt}\vert a\vert ^2=-J.
$$

所以

$$
0=\frac\beta2 J
\left(k\vert b\vert ^{\beta-2}-\vert a\vert ^{\beta-2}\right).
$$

任取 $a=A>0,b=iB$，$B>0$，有 $J>0$。
先令 $A=B$ 得 $k=1$，再改变 $A/B$ 得 $\beta=2$。
节点情况已经由上一定理的连续延拓覆盖。

□

本定理来自项目新增的 179.1。
其特殊性在于没有先把未知密度限定为逐坐标幂函数；
共同赔率与幂形都经过了中间推导。
log 在此负责幂律分类，固定旁观单点的概率与原生混合相容负责选择二。

<a id="section-9-4"></a>

### 9.4 密度选择、最小路径律与实际来源的边界

续卷另加条件 C：每个数学输入、每个原单位脉冲的跳数都有有限本质上界。
它用于选择规范最小率，不是定理 [9.5](#thm:nativesquare) 的前提。
若某个非节点局部射线上两个方向的率都正，连续性给一个短区间上的正下界，
于是任意有限次交替跳转都具有正概率，违反 C。
因此 C 排除对称交通，才从已选平方密度的净流确定最小率。
在 A+B 下，对任意常数 $\lambda>0$，仍可加

$$
\gamma_+^\lambda=\gamma_+^{\min}+\lambda w_1,\qquad
\gamma_-^\lambda=\gamma_-^{\min}+\lambda w_0,\quad
w_j=\frac{\vert z_j\vert ^2}{\vert z_0\vert ^2+\vert z_1\vert ^2},
$$

保持密度而不满足有限本质跳数条件。
有限期望、非爆炸或几乎必然有限跳数不能代替 C。[3](#ref-iii)

> **编者注（Markdown 编者）：规范最小率及节点版本。** 这里的最小率按续卷 III 定理 180.1 的规范正支撑版本理解：$\gamma_+^{\min}=[J]_+/|a|^2$、$\gamma_-^{\min}=[-J]_+/|b|^2$，其中 $[s]_+=\max(s,0)$，在两局部幅度非零时逐点成立。到达幅度趋零而出发幅度非零时规范率延伸为零；出发节点与零质量块不指定可占据的 $0/0$。完整路径律的唯一性不选择孤立节点时刻任意补偿子版本的点值；III §§181–182 仍另行保留报告、纯更新、原因果档案、驱动耦合、读器提升及真实失败合同。上述对称交通采用块内归一的 $w_j$。依据：固定引用 III 定理 180.1、命题 180.2 及 §§181–182。

本文核对的是上述新增段落的条件链。
原复载体、自伴驱动、全数学输入、全部内部时刻等变、
适定自主 Markov 族和正活动仍是供应前提。
实际报告、纯更新、档案、相位控制和真实失败预算并未由这条密度分类自动得到。
项目 §182 同样保留这些来源义务。

<a id="section-10"></a>

## 10 指数如何进入误差递归而不改变平方读出

V17 已有如下组合规则：在给定 Hilbert 结构中，

$$
\Vert u\oplus v\Vert ^2=\Vert u\Vert ^2+\Vert v\Vert ^2,\qquad
\Vert u\otimes v\Vert ^2=\Vert u\Vert ^2\Vert v\Vert ^2,
$$

而相干相加有交叉项 $2\Re\langle u,v\rangle$。[4](#ref-v17)
本轮新增余量稿则给出收缩条件下的明确酉拆分。[8](#ref-residual)
为避免把其算术前件一并假定为已证，下面仅证明抽象 Hilbert 结论。

#### 定理 10.1（平方守恒与几何余量）

<a id="thm:recursion"></a>

设 $\mathcal H$ 是内部 Hilbert 空间，$T$ 是有界自伴算子，

$$
0\preceq T\preceq qI,\qquad 0\le q<1.
$$

定义

$$
\mathcal U=
\begin{pmatrix}
\sqrt{I-T}&-\sqrt T\\
\sqrt T&\sqrt{I-T}
\end{pmatrix}
\quad\text{于 }\mathcal H\oplus\mathcal H.
$$

则 $\mathcal U$ 酉。对 $h_0\in\mathcal H$，令

$$
h_j=T^{j/2}h_0,\qquad d_j=\sqrt{I-T}\,h_j,
$$

有

$$
\Vert h_j\Vert ^2=\Vert d_j\Vert ^2+\Vert h_{j+1}\Vert ^2,
$$

$$
\boxed{\Vert h_0\Vert ^2=\sum_{j=0}^{n}\Vert d_j\Vert ^2+\Vert h_{n+1}\Vert ^2},
\qquad
\Vert h_{n+1}\Vert ^2\le q^{n+1}\Vert h_0\Vert ^2.
$$

**证明。**

$\sqrt T$ 与 $\sqrt{I-T}$ 都是同一自伴算子的连续函数，彼此交换，
且两者平方和为 $I$。块矩阵相乘给
$\mathcal U^\dagger\mathcal U=\mathcal U\mathcal U^\dagger=I$。
又有
$\mathcal U(h_j,0)=(d_j,h_{j+1})$，保范数给逐层恒等式，
求和望远镜消去得到有限层公式。
由谱界 $T^{n+1}\preceq q^{n+1}I$ 得余量界。

> **编者注（Markdown 编者）：递归指标与零余量。** 递归指标为非负整数 $j,n$，并取 $T^0=I$。$q=0$ 时 $T=0$，首层已分离全部能量，后续余量为零；$h_0=0$ 或零 Hilbert 空间同样满足全部未归一等式。三轴归一化仍只用于迹严格正的步骤。依据：定理的算子序界和递归定义。

□

两个输出的完整二元关系可以继续装入正 Gram 矩阵

$$
G_j=
\begin{pmatrix}
\Vert d_j\Vert ^2&\langle d_j,h_{j+1}\rangle\\
\langle h_{j+1},d_j\rangle&\Vert h_{j+1}\Vert ^2
\end{pmatrix}.
$$

迹正时，由定理 [7.1](#thm:bloch) 再次得到三轴表示；
原迹仍须另保留。若某一步 $h_j=0$，后续余量为零，
不对零矩阵强行归一化。
在本例中 $\sqrt{I-T}$ 与 $\sqrt T$ 是交换正算子，
故交叉项等于
$\langle h_j,\sqrt{I-T}\sqrt T\,h_j\rangle\ge0$，是实数。
所得三轴位于 $r_y=0,r_x\ge0$ 的截面；
一般复相位关系需要另外的操作来源。

这给出“每层平方守恒，层数产生指数衰减”的严格区分：
$2$ 是权重次数，$n+1$ 是递归深度。总酉系统的范数没有减少，
减少的是指定剩余分支。幂 $q^{n+1}$ 来自已给的严格收缩界，
不是每一步除以总量便自动出现。
直和槽位在内生解释下是整体中的不同分支或记录；
实际实现这些槽位与门还需要明确操作来源。

项目余量稿的编辑条件注将尚缺的完成能量空间、自伴余项实现、
Fourier 归一与常数标为 `ASSUMED-UNVERIFIED`，
并要求有限节点空间包含固定粗网格、在同一完成空间中嵌套且稠密。
本文不由抽象酉公式推出这些算术前件，亦不由它推出实际剩余核心的最终符号。

<a id="section-11"></a>

## 11 指数翻倍与维数增长的另一个区别

为接回项目 V19 的算术谱例子，设 $a>1/2$，
在明确给定的 $\ell^2(\mathbb{N})$ 上定义

$$
\lvert \chi_a\rangle=
\frac{\sum_{n\ge1}n^{-a}\lvert n\rangle}{\sqrt{\zeta(2a)}},
\qquad
W_t\lvert n\rangle=n^{-it}\lvert n\rangle.
$$

> **编者注（Markdown 编者）：正整数基与实参数。** 这里的基指标取正整数 $n\ge1$，即 V19 所用 $\mathbb{N}_{\ge1}$；参数 $t\in\mathbb{R}$，才使每个 $n^{-it}$ 为单位相位并给出酉算子。依据：原归一化级数的求和域及固定引用 V19 §§7.1–7.3。

其归一化与合法酉重叠为

$$
\langle\chi_a,W_t\chi_a\rangle
=\frac{\zeta(2a+it)}{\zeta(2a)}.
$$

证明只需把每个幅度与其共轭相乘，得到 $n^{-2a}$，再乘单位相位并求和；
该级数在 $2a>1$ 绝对收敛。[9](#ref-v19)

这里指数从 $a$ 变为 $2a$，但载体始终是同一个已给的可数无限维空间。
直接求和振幅以取得 $\zeta(a+it)$，则需要另一个读出；
全一系数序列不在 $\ell^2$，不能把它当作有界 Hilbert 配对。
此例仅说明平方读出的指数变化，不供应 RH 临界带上的实际测量。

<a id="section-12"></a>

## 12 可复用的总命题与剩余问题

#### 定理 12.1（本轮的条件结构总结）

以下结论各自依赖所列前提，不能相互省略：

1. 非负全域权重的叠加修正实双线性，等价于正半定二次型；
   严格正性再给内积。

2. 常规双线性振幅关系、乘法尺度权重与全域二元正性，
   通过倒数条件唯一选择平方权重。

3. 二变量完整整数 $m$ 次对称特征的线性维数为 $m+1$，
   其范数平方为原范数平方的 $m$ 次幂。

4. 二元 Hermitian 正矩阵经迹归一化有三实坐标；
   纯态约束与所取共同酉等价的商必须保留。

5. 在项目原复载体及精确块动力学上，A+B 由共同赔率与
   四角关系先导出幂族，再由内部旁观单点守恒选择指数二。

6. 给定范数严格小于一的正算子 $0\preceq T\preceq qI<I$，
   可以同时保持整体平方范数并令指定余量按递归深度几何衰减。

**证明。**

依次为定理 [4.2](#thm:closure)、[5.1](#thm:positive)、[6.2](#thm:sym)、
[7.1](#thm:bloch)、[9.5](#thm:nativesquare) 与 [10.1](#thm:recursion)。

> **编者注（Markdown 编者）：总结的类型约定。** 总结中的“正”沿原式 $\succeq0$ 包含半正定，迹归一化另需非零矩阵；第 3 项沿用 $m\ge1$。第 2 项的复振幅关系为 $\overline{z_1}z_2$，对复标量是半双线性（第一变量共轭线性），对实标量才是双线性；不能把这里的用语变成复双线性前提。第 4 节的复内积使用由 $iv=Jv$ 给定的复标量结构。依据：原稿定理 5.1、6.2、7.1 和复内积命题的显式公式。

□

因此可以把原直觉精确改写为：

> 两个线性振幅的关系若需要在同一尺度下保持非负、双线性及可复合，
> 平方会成为自权重与交叉关系的共同次数。
> 其完整二次特征或 Hermitian 二次关系可以出现三坐标表示，
> 但那是给定表示与约束的结论，而不是运算名称自带的空间维数。

对于“量子起源”的继续研究，承重问题已经具体化：
为什么实际稳定关系支持所需线性和正性；
为什么原生过程具有共同自主局部率、全时等变与正活动；
为什么内部制备、复合、相位参考及读出能够实现这些数学接口。
本轮证明把幂形和指数选择分开，也把概率密度选择与最小路径律分开；
没有把唯一静态本体的解释框架本身宣称为已由这些代数公式证明。

<a id="references"></a>

## 固定来源与证明范围

<a id="ref-head"></a>

[1] 
[trureturing，本轮固定快照 e168d4b](https://github.com/the-omega-institute/trureturing/tree/e168d4bbef773d94df790275d1f4f2a9e373103f)。
提交时间 2026-10-31 20:24:39（新加坡）；固定后未再追踪活动 HEAD。

<a id="ref-compare"></a>

[2] 
[相对 v48 的固定版本比较](https://github.com/the-omega-institute/trureturing/compare/c292ab048b2a68d8b318657b2c0e1d10d2fdf189...e168d4bbef773d94df790275d1f4f2a9e373103f)。
理论树八项变更；该元数据不等于所有变更内容的数学认证。

<a id="ref-iii"></a>

[3] 
[《量子原理与相干重建续卷 III》](https://github.com/the-omega-institute/trureturing/blob/e168d4bbef773d94df790275d1f4f2a9e373103f/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md)，新增 §§177–182。
本轮实际通读新追加全文，重点复核 178.1、178.2、179.1；
保留 A、B、C 与实际来源义务。

<a id="ref-v17"></a>

[4] 
[《加乘电路、对数与量子勾股》V17](https://github.com/the-omega-institute/trureturing/blob/e168d4bbef773d94df790275d1f4f2a9e373103f/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)，§2、§8。
既有对数半环、正交直和、张量乘积与相干交叉项。

<a id="ref-v14"></a>

[5] 
[《存在量词、电路半环与量子记录》V14](https://github.com/the-omega-institute/trureturing/blob/e168d4bbef773d94df790275d1f4f2a9e373103f/docs/develop/theory/AURIC_EXISTENTIAL_QUANTIFIERS_CIRCUIT_SEMIRINGS_AND_QUANTUM_RECORDS_V14.md)，§§9–10。
固定记录 Gram、正核重构、三阶交叉项及正性边界。

<a id="ref-v41"></a>

[6] 
[《归一化单位、观察者原点与三轴二次不变量》V41](https://github.com/the-omega-institute/trureturing/blob/e168d4bbef773d94df790275d1f4f2a9e373103f/docs/develop/theory/AURIC_NORMALIZATION_UNITS_OBSERVER_ORIGINS_AND_QUADRATIC_INVARIANTS_V41.md)，§§3–4。
归一化态维数、Hermitian 正锥与共同酉商下的二元 Gram 表示。

<a id="ref-unordered"></a>

[7] 
[《无序相容原子与量子表示理论》](https://github.com/the-omega-institute/trureturing/blob/e168d4bbef773d94df790275d1f4f2a9e373103f/docs/develop/theory/AURIC_UNORDERED_COMPATIBLE_ATOM_AND_QUANTUM_REPRESENTATION_THEORY.md)，§4、§6.1。
Clifford 复合和非负正交可加平方权重；相关内容与上轮相同。

<a id="ref-residual"></a>

[8] 
[《收敛余量证书、酉误差递归与容差 Robin 判据》](https://github.com/the-omega-institute/trureturing/blob/e168d4bbef773d94df790275d1f4f2a9e373103f/docs/develop/theory/AURIC_CONVERGENT_RESIDUAL_CERTIFICATES_UNITARY_ERROR_RECURSION_AND_TOLERANT_ROBIN_CRITERION.md)，第二区条件注与第五区定理3。
仅消费已给正收缩后的抽象酉拆分；不认证尚缺的算术完成空间与自伴实现。

<a id="ref-v19"></a>

[9] 
[《加乘、对数与算术谱》V19](https://github.com/the-omega-institute/trureturing/blob/e168d4bbef773d94df790275d1f4f2a9e373103f/docs/develop/theory/AURIC_SUM_PRODUCT_LOGARITHMS_AND_ARITHMETIC_SPECTRA_V19.md)，§7.3。
振幅平方使实指数加倍；载体与实际读出边界另列。

## 13. 固定三端口来源的有限相干标定

**定义 13.1（乘性权重与互斥端口读数）。** 令
$w:\mathbb C\to[0,\infty)$ 为有限值函数，满足

$$
w(0)=0,\qquad w(1)=1,\qquad w(zz')=w(z)w(z'),
\qquad \sup_{|z|\le1}w(z)<\infty.
$$

最后一个条件约束未归一权重。对有限非零向量
$v\in\mathbb C^m$ 和端口事件 $C\subseteq\{1,\ldots,m\}$，定义

$$
\Pi_w(C\mid v)=\frac{\sum_{j\in C}w(v_j)}{\sum_{j=1}^m w(v_j)}.
$$

非零 $z$ 满足 $w(z)w(z^{-1})=1$，故权重严格正，分母严格正；
乘性也给 $\Pi_w(C\mid cv)=\Pi_w(C\mid v)$（$c\ne0$）。
允许的零指数约定为 $w_0(0)=0$、$w_0(z)=1$（$z\ne0$），
不在零点使用 $0^0$，也不预设零点连续性。
共同局域权重及保留事件的前例见
[V46 定义 3.2、定理 3.3、命题 3.4](AURIC_LOG_RECURSION_SQUARED_PROBABILITIES_AND_ENDOGENOUS_ERROR_GEOMETRY_V46.md)；
连续乘性分类见本卷定理 3.2 与
[V47 定理 4.2](AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)。

**假设 13.2（同源相干控制及事件合同）。** 固定同一个完整来源 $\Omega$，
观察者包含环境、参考、控制、记录、预测与自我读出。
在其内部声明三端口复线性接口、同一幅度标定以及

$$
\psi=(a,0,b)^{\mathsf T},\qquad a,b\in\mathbb C,\quad ab\ne0,
\qquad H_0=\begin{pmatrix}1&1\\1&-1\end{pmatrix},
\qquad G_\lambda=(\lambda H_0)\oplus1,\quad \lambda\in\mathbb C^\times.
$$

第三端口的系数固定为一，是非零的直和旁观分支。
端口是互斥记录标签；粗事件固定为 $C=\{1,2\}$。
若将 $\Pi_w$ 解释为实际概率，供应前件包括端口与报告的对应、
一次作用前后同一事件的对应、同源制备及相干比较。
两次控制采用同一个 $\lambda$，中途不重标定活动块与旁观块的相对幅度。
记 $[v]$ 为非零向量的复射线，完整相干回返指全部相对幅度和相位的射线相等。

该接口是完整来源内部的直和，未声明张量参考、任意复制、任意输入制备、
任意停止时刻或任意控制的取得。精确矩阵的数学定义不供应实际精确控制；
门族稠密也须另给逼近、相干比较与读数误差合同。
若采用酉实现后的门前缀记号，则 $\Psi_k=U_k\cdots U_1\Omega$；
有限接口仍只是其中的指定坐标。
本卷定理 9.5 的原生连续驱动及局部 Markov 条件保持其原域，
这里另行声明有限控制合同，不由其替换或取得那些条件。

**定理 13.3（两次相干回返与一次粗事件守恒的指数标定）。**
在定义 13.1、假设 13.2 下，若同一来源实际供应

$$
[G_\lambda^2\psi]=[\psi],\qquad
\Pi_w(C\mid G_\lambda\psi)=\Pi_w(C\mid\psi),
$$

则

$$
\boxed{\lambda=\pm\frac1{\sqrt2},\qquad w(z)=|z|^2\quad(z\in\mathbb C),
\qquad G_\lambda^\dagger G_\lambda=I_3.}
$$

证明中只由定义 13.1 即得到唯一 $p\ge0$ 使
$w(z)=|z|^p$（$z\ne0$），零点仍单独取零。
这一分类是下述有限标定所需的标准 Cauchy 正则性步骤，
不另立为新的乘性函数分类原理。

证明。先给所需的完整分类。若 $|z|\le1$ 而 $w(z)>1$，
则所有 $z^n$ 仍在闭单位盘内，$w(z^n)=w(z)^n$ 却无界，矛盾。
所以盘内权重实际不超过一。对 $|u|=1$，
$w(u),w(u^{-1})\le1$ 且乘积为一，故 $w(u)=1$。
写 $z=ru$，$r>0$，便有 $w(z)=w(r)$；相位不变性由此推出。
令 $f(r)=w(r)>0$。当 $0<r\le s$ 时，
$f(r)=f(s)f(r/s)\le f(s)$，故 $f$ 单调不减。
于是

$$
F(t)=\log f(e^t),\qquad F(s+t)=F(s)+F(t)
$$

为实值单调可加函数。置 $p=F(1)\ge0$，加性给
$F(q)=pq$（$q\in\mathbb Q$）。以两侧有理数夹逼任意实数 $t$，
单调性给 $F(t)=pt$，故 $f(r)=r^p$。
在 $r=e$ 处取值确定 $p$，所以唯一。
反向，每个 $p\ge0$ 连同上述零点约定都满足定义 13.1，
包括在零点不连续的 $p=0$。
这里采用经典可加方程的正则性机制：
[Hamel，*Eine Basis aller Zahlen und die unstetigen Lösungen der Funktionalgleichung:
f(x+y)=f(x)+f(y)*，Math. Ann. 60，459–462](https://doi.org/10.1007/BF01457624)，
特别是第 462 页关于有限实值解的正则性；
所需单调情形已在上文用有理数夹逼直接证明。

再作有限相干标定。由 $H_0^2=2I_2$，

$$
G_\lambda^2\psi=(2\lambda^2a,0,b)^{\mathsf T}.
$$

射线回返给某个 $c\ne0$，使此向量等于 $c\psi$。
$b\ne0$ 先给 $c=1$，$a\ne0$ 再给

$$
2\lambda^2=1.
$$

这一等式来自相干复合和旁观幅度标定，未使用平方概率或预设酉性。
令 $A=w(a)>0$、$B=w(b)>0$、$k=2w(\lambda)>0$。
由于 $G_\lambda\psi=(\lambda a,\lambda a,b)^{\mathsf T}$，
同一粗事件守恒等于

$$
\frac{kA}{kA+B}=\frac A{A+B}.
$$

交叉相乘给 $(k-1)AB=0$，于是 $2w(\lambda)=1$。
对 $2\lambda^2=1$ 用乘性，得到

$$
w(2)w(\lambda)^2=1,\qquad w(2)=4.
$$

分类给 $w(2)=2^p$，故 $p=2$。
复数方程 $2\lambda^2=1$ 的解为 $\lambda=\pm1/\sqrt2$，且

$$
G_\lambda^\dagger G_\lambda
=\operatorname{diag}(2|\lambda|^2,2|\lambda|^2,1)=I_3.
$$

本卷 §9.3 已用原生旁观单点选择二；V46 §3.2 已在给定正交细分下选择二。
这里增加的是未知复缩放的指定控制、同源两次射线回返与一次事件守恒的联合有限合同。
分类步骤及旁观思想分别沿用上述先例；这一合同推导不承担文献优先权结论。
∎

**命题 13.4（标定条件的非退化域）。**
若在假设 13.2 的向量形状中允许 $a=0$ 或 $b=0$，
上述两个合同不再确定指数与控制缩放。
完整射线回返也不能换成只在指定端口基底中的概率返回。

证明。若 $b=0$、$a\ne0$，任意 $\lambda\ne0$ 都给
$G_\lambda^2\psi=2\lambda^2\psi$，而一次作用前后 $C$ 的概率均为一。
若 $a=0$、$b\ne0$，控制根本没有作用到非零活动幅度，两项合同均自动成立。
二者可配任意定义 13.1 所允许的 $p\ge0$。
再取 $ab\ne0$、$w(z)=|z|^2$、$\lambda=i/\sqrt2$，则
$G_\lambda^2\psi=(-a,0,b)^{\mathsf T}$ 与 $\psi$ 的端口概率完全相同，
但 $b$ 固定使可能的射线比例只能为一，而 $-a\ne a$，故射线不相等。
此外只有平衡输入 $(1,0)$ 时，任意非零 $(\lambda,\lambda)$
在归一读数下都给 $(1/2,1/2)$，不能据此区分 $p$。
∎

**命题 13.5（有限二分标定不替代权重正则性）。**
去掉定义 13.1 的闭单位盘有界性后，存在有限值、非负、乘性且相位不变的
$w:\mathbb C\to[0,\infty)$，使

$$
w(0)=0,\quad w(1)=1,\quad w(2)=4,
\quad w(1/\sqrt2)=1/2,\quad w(3)=27.
$$

它对 $\lambda=\pm1/\sqrt2$、任意 $ab\ne0$ 通过定理 13.3 的两个有限合同，
却不是平方权重。其归一读数始终在 $[0,1]$。

证明。$\log2,\log3$ 在 $\mathbb Q$ 上线性无关：
非平凡有理关系清除分母后将给 $2^m3^n=1$ 的非平凡整数关系，
与唯一素分解矛盾。采用 Hamel 基扩张，取含这两个数的 $\mathbb Q$ 基，
指定基值并作 $\mathbb Q$ 线性延拓，构造可加 $F:\mathbb R\to\mathbb R$，使

$$
F(\log2)=2\log2,\qquad F(\log3)=3\log3.
$$

这一基构造及基值的任意有限实值指定，采用上述 Hamel 文第 459–461 页的标准机制。
令 $w(0)=0$、$w(z)=\exp F(\log|z|)$（$z\ne0$）。
实 log 的乘加关系与 $F$ 的加性给乘性，相位不变性来自取模。
加性又给 $F(-\tfrac12\log2)=-\log2$，故所有指定值成立。
射线回返由 $2\lambda^2=1$；粗事件守恒由 $2w(\lambda)=1$，
两者均不需要先把此 $w$ 分类为幂。
若它在闭单位盘有界，定理 13.3 证明内的分类将给单一幂律；
$w(2)=4$ 将迫使 $w(3)=9$，矛盾。
任意有限非零向量的权重和严格正且有限，归一值仍在 $[0,1]$。
因此归一读数有界不能供应未归一权重有界；该反例只界定函数类，
不主张它是实际可实现的概率响应。
∎

## 14. 有限细分深度下的指数可辨识性

**定义 14.1（已标定幅度的有限二分族）。**
取 $p\ge0$，令 $w_p(0)=0$、$w_p(z)=|z|^p$（$z\ne0$），并取
$|\lambda|=1/\sqrt2$。固定同源非零活动幅度 $a$、旁观幅度 $b$。
对每个给定整数 $n\ge0$，活动分支细分为 $2^n$ 个互斥记录叶，
每层把当前活动幅度 $x$ 变成 $(\lambda x,\lambda x)$，旁观幅度仍为 $b$。
所有活动叶始终对应同一粗事件 $C$，记其归一质量为 $q_n$。
这是幅度标定及精确幂族内的比较族，未加入定理 13.3 的粗事件守恒条件。

若解释为实际比较，每个给定有限深度所需的同源制备、相位及幅度标定、
空端口初始化、记录容量、内部控制与同一事件读出均须供应。
数学递归不供应免费子系统，也不从有限层供应实际无限层。
树上振幅的乘法与平方守恒复用
[V46 定理 6.1、命题 6.2](AURIC_LOG_RECURSION_SQUARED_PROBABILITIES_AND_ENDOGENOUS_ERROR_GEOMETRY_V46.md)；
log 赔率坐标沿用本卷 §3。

**定理 14.2（细分深度与粗事件 log 赔率漂移）。**
在定义 14.1 下，置 $A=|a|^p>0$、$B=|b|^p>0$，则

$$
q_n=\frac{A2^{n(1-p/2)}}{A2^{n(1-p/2)}+B}\in(0,1),
\qquad \operatorname{logit}q=\log\frac q{1-q},
$$

$$
\boxed{\operatorname{logit}q_n-\operatorname{logit}q_0
=n\left(1-\frac p2\right)\log2.}
$$

对任一整数 $n\ge1$，$q_n=q_0$ 当且仅当 $p=2$。
形式数列在 $p<2$ 时趋于一，在 $p>2$ 时趋于零，在 $p=2$ 时恒定。

证明。第 $n$ 层每个活动叶的幅度为 $a\lambda^n$，模长为 $|a|2^{-n/2}$。
$2^n$ 个活动叶的总权重为 $A2^{n(1-p/2)}$，旁观权重为 $B$，归一得到 $q_n$。
其赔率为 $(A/B)2^{n(1-p/2)}$，取实 log 即得公式。
所有 log 参数严格正，$p=0$ 时 $A=B=1$ 也成立。
$n=0$ 不提供指数约束；$n\ge1$ 时严格单调的 logit 给所述等价。
数列极限直接由指数符号得出，仅为数学极限。
这个有限深度公式把 V46 已有的一层 $2^{1-p/2}$ 因子与树乘法、
本卷已有的 log 赔率接成指数灵敏度；它没有把上一层概率再平方，
也不把该合成另称为新的通用细分原则。
∎

**推论 14.3（两种读数误差下的指数界）。**
在定理 14.2 下，给定整数 $n\ge1$ 和有限 $\epsilon\ge0$，若

$$
|\operatorname{logit}q_n-\operatorname{logit}q_0|\le\epsilon,
$$

则

$$
\boxed{|p-2|\le\frac{2\epsilon}{n\log2}.}
$$

若掌握的是 $|q_n-q_0|\le\delta_q$（$\delta_q\ge0$），且
$q_0,q_n\in[\tau,1-\tau]$、$0<\tau<1/2$，则

$$
\boxed{|p-2|\le\frac{2\delta_q}{n\tau(1-\tau)\log2}.}
$$

证明。第一式整理定理 14.2 的精确等式。
第二式用中值定理及
$(\operatorname{logit}q)'=1/[q(1-q)]\le1/[\tau(1-\tau)]$；
两端点之间的闭区间也包含在 $[\tau,1-\tau]$ 内。
接近零或一时这个转换常数发散，故概率误差本身没有这里所需的统一 logit 控制。
两式条件均在精确幂族及精确细分幅度内使用，不处理全域近似乘性。
∎

## 15. 相干回返与分裂权重同时近似时的区间

**定理 15.1（双缺陷给出的必要指数区间）。**
设非零输入上的权重已严格分类为 $w(z)=|z|^p$、$p\ge0$，零点取零。
在假设 13.2 的同一控制形状及幅度标定下，给定 $\lambda\ne0$，分别有

$$
|2\lambda^2-1|\le\delta_r,\qquad
|2|\lambda|^p-1|\le\eta_s,
\qquad 0\le\delta_r<1,\quad0\le\eta_s<1.
$$

则

$$
\boxed{
\frac{2\log(2/(1+\eta_s))}{\log(2/(1-\delta_r))}
\le p\le
\frac{2\log(2/(1-\eta_s))}{\log(2/(1+\delta_r))}.}
$$

并有较松的对称估计

$$
\boxed{|p-2|\le
\frac{2[-\log(1-\delta_r)-\log(1-\eta_s)]}
{\log(2/(1+\delta_r))}.}
$$

这里 $\delta_r$ 是已标定相干系数的缺陷，$\eta_s$ 是未归一分裂权重的缺陷；
二者都不是任意报告概率差或未标定射线距离的别名。

证明。反三角不等式和第二个前件分别给

$$
1-\delta_r\le2|\lambda|^2\le1+\delta_r,
\qquad 1-\eta_s\le2|\lambda|^p\le1+\eta_s.
$$

置 $u=\log(2|\lambda|^2)$、$v=\log(2|\lambda|^p)$，则

$$
\log(1-\delta_r)\le u\le\log(1+\delta_r),\qquad
\log(1-\eta_s)\le v\le\log(1+\eta_s),
$$

$$
p=2\frac{\log2-v}{\log2-u}.
$$

因 $1+\delta_r<2$、$1+\eta_s<2$，分子分母严格正，
故分别取上述区间端点得到必要区间，分母取端点时不反转错误方向。
特别地 $p=0$ 不可能满足 $\eta_s<1$，与正的下界一致。
又有

$$
|u|\le-\log(1-\delta_r),\qquad
|v|\le-\log(1-\eta_s),\qquad
\log2-u\ge\log\frac2{1+\delta_r}>0.
$$

将其代入 $p-2=2(u-v)/(\log2-u)$ 即得对称界。
$\delta_r=\eta_s=0$ 恢复 $p=2$。
本区间没有反向断言任意区间内的 $p$ 都满足原复相干缺陷。
∎

**推论 15.2（同一粗事件读数到分裂缺陷的条件转换）。**
在定理 15.1 的精确幂族与指定控制形状下，取 $ab\ne0$，令
$q=\Pi_w(C\mid G_\lambda\psi)$、$q_0=\Pi_w(C\mid\psi)$，则

$$
k=2|\lambda|^p=\frac{q(1-q_0)}{q_0(1-q)},\qquad
|k-1|=\frac{|q-q_0|}{q_0(1-q)}.
$$

若 $q,q_0\in[\tau,1-\tau]$、$0<\tau<1/2$，且
$|q-q_0|\le d<\tau^2$，则可在定理 15.1 中取 $\eta_s=d/\tau^2<1$，
前提是相干缺陷 $\delta_r<1$ 已独立取得。

证明。由 $q_0=A/(A+B)$、$q=kA/(kA+B)$，其中
$A=|a|^p>0$、$B=|b|^p>0$，消去 $A/B$ 得第一式，减去一得第二式。
因 $q_0(1-q)\ge\tau^2$，得所需界。
若旁观质量或初始活动质量趋零，分母可趋零，不能从任意小的报告差
直接取得同样小的分裂缺陷；控制矩阵的误差也需另给通向实际报告的桥。
∎

## 16. 平方标定的几何与动力学扩展接口

**定义 16.1（沿用的关系坐标与支撑约定）。**
在平方标定后的二元接口 $v=(\alpha,\beta)^{\mathsf T}$ 上，采用
[V52 定义 2.1、定理 2.2、推论 2.3](AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)
的保尺度外积坐标，记作

$$
N=|\alpha|^2+|\beta|^2,\quad
(X,Y,Z)=(2\Re(\bar\alpha\beta),2\Im(\bar\alpha\beta),|\alpha|^2-|\beta|^2).
$$

这些是满足 $N^2=X^2+Y^2+Z^2$、$N\ge0$ 的纯关系坐标；
一般二阶正矩阵则采用本卷定理 7.1 的 $N^2\ge X^2+Y^2+Z^2$。
非零外积只消去共同相位，归一再消去正尺度；纯态球面与混态球体分开使用。
在 $\alpha\beta\ne0$ 的图上，令
$\beta/\alpha=e^{u+i\theta}$、$u=\log|\beta/\alpha|$，采用本卷定理 7.2 的

$$
(X,Y,Z)/N=(\operatorname{sech}u\cos\theta,
\operatorname{sech}u\sin\theta,-\tanh u),
\qquad \log(p_1/p_0)=2u.
$$

两极换图；相位与模长 log 分开。共同相位下的全域多项式关系采用
V52 定理 5.2、推论 5.3 的生成元 $g_{ij}=z_i\bar z_j$，
局部比值是有理不变量，不属于其最低多项式次数的断言。
二维实线性复乘法的行列式 $\det_{\mathbb R}m_z=|z|^2$
沿用 V47 §4 的代数范数解释，未据此单独指定概率。

对高维 Hermitian 关系矩阵，约定 $p_i=g_{ii}\ge0$，
在纯二元边上要求 $|g_{ij}|^2=p_ip_j$，并采用
[V51 定理 8.2](AURIC_CONSTRAINT_RECURSION_PURE_STATE_DUALITY_AND_ENDOGENOUS_STATIC_HISTORY_V51.md)
及 [V44 定理 7.4、命题 9.1](AURIC_BOUNDARY_EXTENSION_AND_HIGHER_DIMENSIONAL_RELATIONAL_ATLAS_V44.md)
的闭路相容条件。在全边情形可写为
$g_{ij}g_{jk}=p_jg_{ik}$；有 $p_a>0$ 时以
$z_i=g_{ia}/\sqrt{p_a}$ 恢复共同相位之外的振幅。
零质量行列先由 $|g_{ij}|^2=p_ip_j$ 置零，不为它们定义相位或作除法。
部分图在每个正支撑连通分量内取闭路乘积为一，各分量各留一个共同相位。
相位 log 的闭路和只要求属于 $2\pi\mathbb Z$。
高维纯态的 $2d-2$ 个归一实自由度采用 V52 定理 4.1；
单个固定三实坐标不能作所有 $d\ge3$ 纯态的局部光滑可逆坐标，
须保留 V44 §12 的维数边界。

**假设 16.2（扩展到过程所需的额外供应）。**
若要从标定操作扩展到一般 $U:\mathbb C^d\to\mathbb C^m$，
另给其复线性及全部数学输入上的平方总质量保持；
一般等距与等维酉性采用
[V52 命题 8.5](AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)
的极化论证。单一固定输入的保质量不替代这个全称量词。
直和旁观分支不供应张量参考、联合读出或完全正更新的认证。

若另给连续 $U:\mathbb R\to U(d)$、$U(0)=I$ 及
$U(t+s)=U(t)U(s)$，采用
[《相容预测波与关系谱》定理 4.9 及其有限维连续群说明](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md)
的指数表示 $U(t)=e^{-itH}$、$H=H^\dagger$（相位单位取 $\hbar=1$）。
连续复合参数、平移齐次群律、物理钟的对应及单位标定另行供应；
固定 $t$ 时的指数算子对输入态仍复线性。
指定 Hermitian $H(t)$ 及非零实常数 $\hbar$ 后的比值 Riccati 方程，采用
[V55 定理 10.2](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)，
只在所用非零图上求商。
保二次锥的滤波与保总质量的酉操作，采用同卷 §9 的区分；
条件分支须另留成功质量及互补记录。

实 log 的乘加坐标采用
[V17 §2](AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)
与本卷 §3；复 log 使用局部图或支信息，采用
[DLMF §4.2(i)](https://dlmf.nist.gov/4.2#i) 及
[§4.8(i)，式 4.8.1–4.8.2](https://dlmf.nist.gov/4.8#i) 的一般值与主支条件。
非交换控制的矩阵对数不作无条件的加法替换。

**假设 16.3（实际关系与理论结论的范围）。**
平方标定保留复线性域、乘性及未归一正则性、互斥报告、同源相干控制和同一事件合同。
原生 $F[\cdot]$ 读出与 $(N,X,Y,Z)$ 的对应仍需具体定义及变换桥；
共轭使 $Y$ 反号的坐标事实不指定物理手性。
同一推导可在实振幅上作相应标定，故这里未选择复数域、张量复合、
空间维数、Hamiltonian、实际时间尺度或全部量子物理的起源。
门词长度的单增也未给范数、熵、记录容量或可解码复杂度的单增条件。

若接入实际历史关系，必须保留各自来源前件：
[量子续卷 IV §§206–208](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)
的平方探测权重、既定率律及历史桥属于其输入；
[RRO §§62–67](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)
的自然过去域、档案及可测恢复限定属于其输入。
自然域内的必要恢复条件不无条件转移到更大的过去域；
可测精确恢复不供应有限存储、有限精度或统一在线恢复过程。
这些关系未充当定理 13.3 的指数起源前提或实际取得证明。
全域近似乘性的稳定性及实际控制到已标定相干缺陷的误差桥在此仍未供应。

## 追加锚（本行以下为增补区）
