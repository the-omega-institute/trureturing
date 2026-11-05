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

## 17. 同一固定来源的射线误差与控制可行域

**定义 17.1（独立标定的有限误差合同）。** 沿用定义 13.1、假设 13.2 的同一来源、同一非零 $a,b$、同一幅度坐标、同一实际互斥事件 $C=\{1,2\}$，以及精确候选族

$$
w_p(0)=0,\quad w_p(z)=|z|^p\ (z\ne0),\quad p\ge0,
\qquad G_\lambda=(\lambda H_0)\oplus1,\quad 0<|\lambda|<\infty.
$$

这里的幂分类直接采用定理 13.3 证明中的有界乘性分类；
不把近似乘性、零点连续性或有界归一概率当作它的替代条件。
以下另给幅度比标定

$$
r=|a|/|b|\in(0,\infty),\qquad \ell=\log r,\qquad L=\log2,
$$

以及非零向量射线上的接口几何

$$
D([u],[v])=\sqrt{1-\frac{|\langle u,v\rangle|^2}{\|u\|^2\|v\|^2}}.
$$

另供有限实数 $\varepsilon\ge0$ 和两个非空闭区间
$I_j=[\underline q_j,\overline q_j]\subset(0,1)$（$j=0,1$，允许单点），合同为

$$
D([G_\lambda^2\psi],[\psi])\le\varepsilon,\qquad
q_0=\Pi_{w_p}(C\mid\psi)\in I_0,\qquad
q_1=\Pi_{w_p}(C\mid G_\lambda\psi)\in I_1.
\tag{17.1}
$$

$I_j$ 包含的是该指定来源与事件的真概率；其取得不在合同内。
$D$ 是所声明复内积的几何量，不被定义为未知 $w_p$ 探测器的返回概率。
$r$ 的标定也不能先用平方读数反解 $r=\sqrt{q_0/(1-q_0)}$。
如果实际使用 (17.1)，独立的幅度比标定、射线误差证书及真概率区间均须供应。
这里不规定抽样、独立同分布、置信度、复制、重置或额外控制权限。
该合同与定理 13.3 的精确回返及精确守恒合同分别使用。

所用几何的代数先例是
[V52 推论 2.3](AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)
的纯态内积，以及
[V55 定理 9.2](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)
的二元行列式距离。
[Fuchs–van de Graaf，*Cryptographic Distinguishability Measures for Quantum Mechanical States*，§§4.2–4.3，命题 3](https://arxiv.org/html/quant-ph/9712042v2)
给出迹距离及纯态重叠的标准背景；其测量概率解释不作为未知幂权的输入。

**定理 17.2（射线证书的精确模长域与相位纤维）。** 在定义 17.1 下，置

$$
x=2\lambda^2=h e^{i\theta},\qquad h=2|\lambda|^2>0,
\qquad \alpha=\arctan r\in(0,\pi/2),
\qquad \beta=\arcsin(\min\{\varepsilon,1\}).
$$

则

$$
D([G_\lambda^2\psi],[\psi])^2
=\frac{r^2|x-1|^2}{(1+r^2)(1+r^2h^2)}.
\tag{17.2}
$$

存在满足射线证书的相位，当且仅当 $h$ 属于下列区间 $H$：

$$
\begin{aligned}
h_-&=\begin{cases}
\tan(\alpha-\beta)/r,&\beta<\alpha,\\
0,&\beta\ge\alpha,
\end{cases}\\
h_+&=\begin{cases}
\tan(\alpha+\beta)/r,&\alpha+\beta<\pi/2,\\
+\infty,&\alpha+\beta\ge\pi/2,
\end{cases}\\
H&=\{h\in(0,\infty):h_-\le h\le h_+\}.
\end{aligned}
\tag{17.3}
$$

$h_-=0$ 与 $h_+=+\infty$ 都不表示取得相应端点。
每个有限正端点均取得，且 $1\in H$。
对一个给定 $h>0$，全部允许相位恰满足

$$
\cos\theta\ge T_\varepsilon(r,h),\qquad
T_\varepsilon(r,h)=
\frac{h^2+1-\varepsilon^2(1+r^2)(1+r^2h^2)/r^2}{2h}.
\tag{17.4}
$$

$T>1$ 时无相位；$-1<T\le1$ 时为模 $2\pi$ 的闭相位弧；
$T\le-1$ 时所有相位均可。每个允许 $h,\theta$ 对应
$\lambda=\pm\sqrt{h/2}\,e^{i\theta/2}$。

证明。$G_\lambda^2\psi=(xa,0,b)^{\mathsf T}$。
在其与 $\psi$ 所在的二维坐标平面，Gram 行列式为
$|a|^2|b|^2|x-1|^2$；除以两向量的平方范数乘积给 (17.2)。
$a,b$ 的各自相位相消，但相干控制的相位 $\theta$ 保留。
固定 $h$ 后，$|he^{i\theta}-1|^2=h^2+1-2h\cos\theta$
在 $\theta=0$ 最小，因此存在相位的充要条件是

$$
f_r(h):=\frac{r|h-1|}{\sqrt{(1+r^2)(1+r^2h^2)}}\le\varepsilon.
\tag{17.5}
$$

两个实正方向的角分别为 $\arctan(rh)$ 和 $\alpha$，故
$f_r(h)=\sin|\arctan(rh)-\alpha|$。
这个角差绝对值小于 $\pi/2$；$\varepsilon<1$ 时可在其上取单调的反正弦，
$\varepsilon\ge1$ 时全部 $h>0$ 均可。
由 $0<\arctan(rh)<\pi/2$ 反解角区间，即得 (17.3)，
包括与零、$\pi/2$ 相接时的开端点。
不极小化相位而直接整理 (17.2)，则给 (17.4)。
取 $\theta=0$ 证明每个 $h\in H$ 都有同一形状的有限非零候选矩阵。
∎

**推论 17.3（源条件数、临界容差与端点）。** 上述 $H$ 的全部容差域为

$$
\begin{aligned}
h_->0&\iff \varepsilon<\frac r{\sqrt{1+r^2}},\\
h_+<\infty&\iff \varepsilon<\frac1{\sqrt{1+r^2}},\\
h_+<2&\iff \varepsilon<\varepsilon_*(r),\qquad
\varepsilon_*(r)=\frac r{\sqrt{(1+r^2)(1+4r^2)}}.
\end{aligned}
\tag{17.6}
$$

等于前两个阈值时，分别已经失去正下端点、有限上端点。
在 $\varepsilon=\varepsilon_*(r)$ 时，$h_+=2$ 为可取得端点。
特别地，在信息性有限端点域

$$
0\le\varepsilon<\varepsilon_*(r)
\tag{17.7}
$$

内有 $0<h_-\le1\le h_+<2$；$\varepsilon=0$ 给 $H=\{1\}$。

证明。前两式由 (17.3) 分别在 $\beta=\alpha$、
$\beta=\pi/2-\alpha$ 处得到。
$f_r$ 在 $[1,\infty)$ 严格递增，且
$f_r(2)=\varepsilon_*(r)$；此值严格小于前两个阈值，给余下结论。
$r\downarrow0$ 或 $r\to\infty$ 时 $\varepsilon_*(r)\to0$。
这说明同一几何精度在极不平衡来源上失去固定的模长分辨力，
不把它误当成来源无关的控制系数误差。
例如 (17.2) 实际只给

$$
|x-1|\le\frac\varepsilon r\sqrt{(1+r^2)(1+r^2h^2)},
$$

右端同时含来源比与未知控制模。∎

## 18. 任意非零固定振幅的联合指数逆问题

**定理 18.1（显式且共同可取得的指数集合）。** 在定义 17.1 下，记

$$
J_j=[A_j,B_j]=
[\operatorname{logit}\underline q_j,\operatorname{logit}\overline q_j],
\qquad \operatorname{logit}q=\log\frac q{1-q},
$$

并由定理 17.2 的 $H$ 定义扩展实端点

$$
c_-=\ell+\tfrac12\log(h_-/2),\qquad
c_+=\ell+\tfrac12\log(h_+/2).
\tag{18.1}
$$

$h_-=0$ 时 $c_-=-\infty$，$h_+=+\infty$ 时 $c_+=+\infty$；
相应无限端点不属于所定义的实数区间

$$
\mathcal C=\{c\in\mathbb R:c_-\le c\le c_+\}.
$$

为计算全部正指数，建立如下有限不等式表；无限端点对应的行省略：

| 条件 | 写成 $s p\le t$ 的系数 $(s,t)$ |
| --- | --- |
| 初始区间的上界 | $(\ell,B_0)$ |
| 初始区间的下界 | $(-\ell,-A_0)$ |
| $c_->-\infty$ 时的输出上界 | $(c_-,B_1-L)$ |
| $c_+<+\infty$ 时的输出下界 | $(-c_+,L-A_1)$ |

若表中某行 $s=0,t<0$，置 $P_+=\varnothing$。
否则丢弃 $s=0$ 的行，定义

$$
P_{\rm lo}=\max\bigl(\{0\}\cup\{t/s:s<0\}\bigr),\qquad
P_{\rm hi}=\min\bigl(\{+\infty\}\cup\{t/s:s>0\}\bigr),
$$

$$
P_+=\{p\in(0,\infty):P_{\rm lo}\le p\le P_{\rm hi}\}.
\tag{18.2}
$$

于是 (17.1) 的必要且充分兼容指数集合恰为

$$
\boxed{P=P_+\ \cup\
\begin{cases}
\{0\},&0\in J_0\text{ 且 }L\in J_1,\\
\varnothing,&\text{其余情形}.
\end{cases}}
\tag{18.3}
$$

它是同一固定 $a,b$ 上对一个共同有限非零 $\lambda$ 的存在结论。
对每个 $p\in P_+$，可从非空交集

$$
\mathcal C\cap\left[\frac{A_1-L}{p},\frac{B_1-L}{p}\right]
\tag{18.4}
$$

任选一个有限 $c$，并用同一个见证

$$
h=2e^{2(c-\ell)},\qquad \lambda=\sqrt{h/2}>0
\tag{18.5}
$$

同时实现几何证书及两个概率区间。
全部复相位见证再由 (17.4) 给出；不能把各项约束分别优化所得的不同控制拼成见证。

证明。令 $A=|a|^p$、$B=|b|^p$，二者严格正，$p=0$ 时均为一。
由同一端口归一式，精确有

$$
q_0=\frac{r^p}{1+r^p},\qquad
q_1=\frac{2|\lambda|^p r^p}{1+2|\lambda|^p r^p},
$$

$$
\operatorname{logit}q_0=p\ell,\qquad
\operatorname{logit}q_1=L+p\left(\ell+\tfrac12\log(h/2)\right).
\tag{18.6}
$$

这直接复用本卷 §3 的赔率坐标与推论 15.2 的精确消元。
实 log 的正数域及幂公式采用
[NIST DLMF 4.8.13](https://dlmf.nist.gov/4.8#E13)；
复相位始终留在 (17.4)，不取一个全局复 log。

$p>0$ 时，$h\mapsto\ell+\tfrac12\log(h/2)$
把 $H$ 双射到 $\mathcal C$。
$q_0\in I_0$ 恰为 $A_0\le p\ell\le B_0$。
$q_1\in I_1$ 则恰为 (18.4) 非空。
由于 (18.4) 中第二个区间为有限闭区间，交集非空当且仅当

$$
c_-p\le B_1-L\quad(c_->-\infty),\qquad
c_+p\ge A_1-L\quad(c_+<+\infty).
$$

无限端点没有附加约束，也不被选作 $c$。
因此全部条件恰是表中的有限线性不等式。
$s>0$ 给上界 $p\le t/s$，$s<0$ 给下界 $p\ge t/s$；
$s=0$ 的矛盾与恒真行按陈述处理，得到 (18.2)。这证明必要性。

反向，若 $p\in P_+$，这些不等式保证 (18.4) 含有限 $c$。
(18.5) 给 $h\in H$ 和 $\theta=0$，故定理 17.2 保证几何证书；
(18.6) 保证两个概率区间，使用的 $a,b,p,\lambda$ 全部相同。
若 $p=0$，原两概率恰为 $1/2,2/3$，与 $h$ 无关；
选 $h=1,\lambda=1/\sqrt2$ 给零几何误差。
故零指数的条件恰是 (18.3)，而非对 (18.1) 的无限端点作 $0\cdot\infty$。
∎

**推论 18.2（闭性、有限端点与全部退化类型）。** 在定理 18.1 的域内，
$P_+$ 是 $(0,\infty)$ 中的相对闭区间或空集。
有限正端点若存在就实际取得；零和无穷必须分别按 (18.3) 及 $p<\infty$ 处理。
具体地，$P_{\rm hi}\le0$ 或 $P_{\rm lo}>P_{\rm hi}$ 给空的正部分；
$P_{\rm lo}=P_{\rm hi}>0$ 给单点；
$0<P_{\rm lo}<P_{\rm hi}<\infty$ 给双闭有界区间；
$P_{\rm lo}=0<P_{\rm hi}<\infty$ 给 $(0,P_{\rm hi}]$；
$P_{\rm hi}=+\infty$ 给相应无界区间。还可只有 $P=\{0\}$。

若 $r\ne1$，初始区间本身给有限的正指数范围：

$$
\begin{cases}
\max\{0,A_0/\ell\}\le p\le B_0/\ell,&\ell>0,\\
\max\{0,B_0/\ell\}\le p\le A_0/\ell,&\ell<0,
\end{cases}
\qquad p>0.
\tag{18.7}
$$

若 $r=1$，初始约束恰为 $1/2\in I_0$，否则整个 $P$ 为空。
因此非平衡来源的 $P$ 总有界，而不预设它非空或包含二。

若 $0<h_-\le h_+<\infty$，整个 $P$ 在 $[0,\infty)$ 中闭。
在信息性域 (17.7) 内，$P$ 还是紧区间或空集，全部有限端点取得。
超出该域时，(17.3)、(18.2)–(18.3) 仍给全部容差情形，
不一概宣称集合闭或指数有有限上界。

证明。对正指数的结论直接由有限个非严格线性不等式及 (18.5) 得到。
(18.7) 是 $A_0\le p\ell\le B_0$ 按 $\ell$ 的符号求解。
若 $p_k\downarrow0$ 且 $h_k\in[h_-,h_+]$ 是共同见证，
在紧模长域内 $\ell+\tfrac12\log(h_k/2)$ 一致有界。
由 (18.6)，两 logit 必趋于 $0,L$，闭区间条件便给 $0\in P$。
这证明紧模长域内不会漏掉零极限，连同正端点取得即得闭性。
若零指数可行，表中各右端均非负；任一正解与零之间的所有正数亦满足表中不等式。
因此加入零不会产生分离的区间。

在 (17.7) 内模长域紧。$r\ne1$ 时由 (18.7) 有界；
$r=1$ 时 $c_+<0$，表中最后一行给有限上界
$p\le(L-A_1)/(-c_+)$，或判为不相容。
故此域内 $P$ 紧。

闭性在退化模长域内确实会失败：取 $r=1$、
$\varepsilon\ge1/\sqrt2$、$I_0=I_1=\{1/2\}$。
此时 $H=(0,\infty)$，对每个 $p>0$ 取
$\lambda=2^{-1/p}$，两概率均为 $1/2$，而 $p=0$ 给 $q_1=2/3$。
所以 $P=(0,\infty)$，下端点零不取得。
这也展示为什么闭概率区间并不自动给闭的投影参数集合。
空集可由 $r=1,1/2\notin I_0$ 实现；
$\varepsilon=0,r=1,I_0=I_1=\{1/2\}$ 给单点 $\{2\}$；
同取 $I_1=\{2/3\}$ 给单点 $\{0\}$。
下节给出有界非单点及无界集合的共同见证。∎

## 19. 平衡来源的锋利端点与失去有限上界的阈值

**定理 19.1（平衡来源的全部容差域）。** 在定义 17.1 下令 $r=1$。
若 $1/2\notin I_0$，则 $P=\varnothing$。
以下设 $1/2\in I_0$，并记 $v_-=A_1,v_+=B_1$、
$\varepsilon_*=1/\sqrt{10}$。
对 $0\le\varepsilon<1/\sqrt2$，令

$$
t=\frac{\varepsilon}{\sqrt{1-\varepsilon^2}},\qquad
h_- =\frac{1-t}{1+t},\qquad h_+=\frac{1+t}{1-t},
\qquad a_\varepsilon=\log(2/h_-)>0,
\qquad b_\varepsilon=\log(2/h_+).
\tag{19.1}
$$

兼容集合精确如下，所有方括号内的有限端点都取得。

1. 若 $0\le\varepsilon<\varepsilon_*$，则 $b_\varepsilon>0$。
   $v_->L$ 时 $P=\varnothing$；$v_-\le L$ 时

$$
\boxed{P=\left[
\frac{2\max\{0,L-v_+\}}{a_\varepsilon},\
\frac{2(L-v_-)}{b_\varepsilon}
\right].}
\tag{19.2}
$$

2. 若 $\varepsilon=\varepsilon_*$，则 $h_+=2$、$b_\varepsilon=0$。
   $v_->L$ 时 $P=\varnothing$；$v_-\le L$ 时

$$
\boxed{P=\left[\frac{2\max\{0,L-v_+\}}{a_\varepsilon},\infty\right).}
\tag{19.3}
$$

3. 若 $\varepsilon_*<\varepsilon<1/\sqrt2$，则 $b_\varepsilon<0$，且

$$
\boxed{P=\left[
\max\left\{0,\frac{2(L-v_+)}{a_\varepsilon},
\frac{2(v_--L)}{-b_\varepsilon}\right\},\infty\right).}
\tag{19.4}
$$

4. 若 $\varepsilon\ge1/\sqrt2$，则

$$
\boxed{P=(0,\infty)\ \cup\
\begin{cases}
\{0\},&v_-\le L\le v_+,\\
\varnothing,&\text{其余情形}.
\end{cases}}
\tag{19.5}
$$

证明。$\alpha=\pi/4$，在 $\beta<\pi/4$ 时用正切和差公式得到 (19.1)。
此时 $h_-h_+=1$，且
$c_-=-a_\varepsilon/2<0$、$c_+=-b_\varepsilon/2$。
定理 18.1 的初始约束自动满足，其余两行恰是

$$
-\tfrac12a_\varepsilon p\le v_+-L,\qquad
-\tfrac12b_\varepsilon p\ge v_--L.
\tag{19.6}
$$

当 $b_\varepsilon>0$，两式分别给 (19.2) 的下、上界；
$v_->L$ 时连 $p=0$ 也不可能。
当 $b_\varepsilon=0$，第二式恰为 $v_-\le L$，没有指数上界，给 (19.3)。
当 $b_\varepsilon<0$，第二式也变成下界，给 (19.4)。
这些式子中的零端点恰在 $v_-\le L\le v_+$ 时出现，
故 (18.3) 正好将其纳入，没有把不允许的零指数填入。
当 $\varepsilon\ge1/\sqrt2$，$H=(0,\infty)$，
$\mathcal C=\mathbb R$，任意 $p>0$ 均可用 (18.5) 实现，给 (19.5)。

端点的共同见证也可直接写出。
在 (19.2) 的正下端点取 $h=h_-$、$\operatorname{logit}q_1=v_+$；
在其正上端点取 $h=h_+$、$\operatorname{logit}q_1=v_-$。
(19.3) 的正下端点取前一个见证。
(19.4) 若正的最大项来自第二项或第三项，分别取
$(h_-,v_+)$ 或 $(h_+,v_-)$；并列最大时同样满足另一不等式。
零端点均可取 $h=1$。
每个见证统一使用 $\lambda=\sqrt{h/2}$ 与原固定 $a,b,p$；
区间内部的共同取得由 (18.4)–(18.5) 保证。
∎

**推论 19.2（有限上界的精确丧失与共享参数族）。**
仍设 $r=1$、$1/2\in I_0$。
若 $I_1\cap(0,2/3]\ne\varnothing$，兼容集合非空，
且具有有限上界当且仅当 $\varepsilon<1/\sqrt{10}$。
若 $I_1\subset(2/3,1)$，则在 $\varepsilon\le1/\sqrt{10}$ 时为空，
在 $\varepsilon>1/\sqrt{10}$ 时非空且无界。
特别地，精确输出 $q_1=1/2$ 也在临界容差处失去有限指数上界。

证明。有限域及空集部分由定理 19.1 得到。
为给出无界性所需的共同见证，固定一个 $v\in J_1$，对 $p>0$ 置

$$
\lambda_p=e^{(v-L)/p},\qquad
h_p=2e^{2(v-L)/p}.
\tag{19.7}
$$

同一个候选在两次相干作用及一次概率读数中均用 $\lambda_p$。
由 (18.6)，$q_0=1/2$、$q_1=(1+e^{-v})^{-1}$，
且 $h_p\to2$。
临界 $\varepsilon=1/\sqrt{10}$ 时，若 $v\le L$，则 $h_p\le2=h_+$，
而对全部充分大的 $p$ 又有 $h_p\ge h_->0$；$v=L$ 时恒为端点二。
所以恰在临界处已取得任意大的有限指数。
超过临界时二是 $H$ 的内点，任意固定有限 $v$ 都对充分大的 $p$ 给 $h_p\in H$。
这证明所有声称的无界性，而没有把模长和概率的独立最优值相拼。
每个 $p$ 对应一个候选合同；没有断言同一装置同时具有不同的 $p$ 或 $\lambda_p$。
∎

## 20. 固定不确定控制的有限细分与校准歧义

**定义 20.1（分别供应的有限深度读数）。** 保留定义 17.1 的同一个固定
$a,b,p,\lambda$、幅度比和两次作用的几何证书。
对每个另行供应的有限深度 $n\ge1$，按定义 14.1 的树形细分操作，
每个节点均将活动幅度 $z$ 变成 $(\lambda z,\lambda z)$，
全树共用这个未知但固定的 $\lambda$，旁观幅度仍为 $b$。
这里只取消定义 14.1 中预先确定的 $|\lambda|=1/\sqrt2$；
空端口、同源比较、同一粗事件及每个给定有限深度的资源仍须供应。
每个被供应深度的真概率 $q_n$ 另有非空闭区间 $I_n\subset(0,1)$。
若同时保留一次读数，深度集合须含 $1$ 且使用原来的 $I_1$。
各节点的控制不允许单独选择不同的误差符号或缩放。

**定理 20.2（一个共同漂移的有限深度联合逆像）。**
对任意非空有限深度集合 $F\subset\mathbb N_{>0}$，
令 $J_n=[A_n,B_n]=\operatorname{logit}I_n$（$n\in F$），并仍用 $J_0$。
在定义 20.1 下精确有

$$
\begin{aligned}
q_n&=\frac{r^p(2|\lambda|^p)^n}{1+r^p(2|\lambda|^p)^n},\\
\operatorname{logit}q_n&=p\ell+n d,\qquad
 d=L+\tfrac p2\log(h/2),\quad h=2|\lambda|^2.
\end{aligned}
\tag{20.1}
$$

对 $p>0$，构造两组仿射函数：

$$
\begin{aligned}
\mathcal L_p&=\left\{\frac{A_n-p\ell}{n}:n\in F\right\}
\cup\left\{L+\tfrac p2\log(h_-/2):h_->0\right\},\\
\mathcal U_p&=\left\{\frac{B_n-p\ell}{n}:n\in F\right\}
\cup\left\{L+\tfrac p2\log(h_+/2):h_+<\infty\right\}.
\end{aligned}
$$

则共同兼容的正指数集合恰为

$$
\boxed{P_{F,+}=\{p>0:A_0\le p\ell\le B_0,\quad
\max\mathcal L_p\le\min\mathcal U_p\}.}
\tag{20.2}
$$

这是显式有限线性不等式组：对每个下函数 $a+sp$ 和上函数 $b+tp$
加入 $(s-t)p\le b-a$，再加入初始区间的两行，
按 (18.2) 的同一端点规则即得完整区间及空集判据。
零指数应且仅应在

$$
0\in J_0,\qquad nL\in J_n\quad\text{对每个 }n\in F
\tag{20.3}
$$

时另加。
对每个 $p\in P_{F,+}$，从
$[\max\mathcal L_p,\min\mathcal U_p]$ 取一个共同的有限 $d$，并令

$$
\lambda=\exp((d-L)/p),\qquad h=2\exp(2(d-L)/p).
\tag{20.4}
$$

这一个 $\lambda$ 同时实现所有被供应深度及几何证书。
仅取各深度分别得到的指数集合之交，而不检查共同 $d$，一般不等于 (20.2)。

证明。第 $n$ 层有 $2^n$ 个互斥活动叶，振幅全为 $a\lambda^n$；
其总权重为 $|a|^p(2|\lambda|^p)^n$，旁观权重仍为 $|b|^p$。
直接归一得到 (20.1)，包括 $p=0$ 的 $q_n=2^n/(1+2^n)$。
对 $p>0$，$h\in H$ 恰使 $d$ 落在两个几何仿射端点之间，
无限端点不施加有限限制。
第 $n$ 个读数恰要求 $(A_n-p\ell)/n\le d\le(B_n-p\ell)/n$。
由于 $F$ 非空有限，所有读数端点有限，两组函数均非空，
共同实数 $d$ 存在当且仅当 (20.2) 的最大下界不超过最小上界。
两两比较就是陈述中的有限线性组；因此不需要将各深度的控制分别优化。

反向取其交中的 $d$，(20.4) 给有限非零的实正 $\lambda$，
同一个 $h\in H$，故几何证书成立，(20.1) 则同时给全部概率区间。
零指数由上述 $q_n$ 的精确值独立结算，得到 (20.3)。
这证明必要性及共同取得性。
例如令 $r=1,\varepsilon\ge1/\sqrt2,F=\{1,2\}$，
$J_1=\{0\},J_2=\{1\}$。
每个深度单独都允许任意 $p>0$，联合却要求 $d=0$、$2d=1$，故为空。
这里全部概率均严格在零一之间，矛盾只来自缺少共同控制。
∎

**推论 20.3（平衡来源在任意给定深度的锋利集合）。**
若 $r=1,1/2\in I_0$，仅另供一个有限深度 $n\ge1$ 的区间 $I_n$，
则定理 19.1 的所有公式逐字采用

$$
v_-=A_n/n,\qquad v_+=B_n/n
\tag{20.5}
$$

替换原来的 $A_1,B_1$ 后，便是这一深度的精确兼容集合。
特别地，$\varepsilon<1/\sqrt{10}$ 且 $B_n<nL$ 时，两个锋利正端点为

$$
\boxed{\frac{2(L-B_n/n)}{a_\varepsilon}
\le p\le
\frac{2(L-A_n/n)}{b_\varepsilon}.}
\tag{20.6}
$$

证明。$\ell=0$ 使 (20.1) 化为 $\operatorname{logit}q_n/n=d$，
所以输出约束正好变成 $d\in[A_n/n,B_n/n]$。
这与定理 19.1 中的一次输出 logit 条件完全相同，
同一端点见证、相位条件、零指数规则及无界阈值随之适用。
这里的替换在证明内部使用既有区间求解，不另设一个一般 logit 分类。
∎

**定理 20.4（固定系统控制误差留下不可由深度消除的精确歧义）。**
取同一个平衡来源 $r=1$，并供应 $q_0=1/2$。
任意非空有限深度集合 $F$ 上，若供应的精确读数均为 $q_n=1/2$，
则所有兼容指数与控制模恰满足

$$
p>0,\qquad |\lambda|=2^{-1/p},\qquad h(p)=2^{1-2/p}\in H.
$$

每个这样的指数可取 $\lambda=2^{-1/p}$ 作为共同实正见证：

$$
2|\lambda|^p=1.
\tag{20.7}
$$

相应的全部指数集合与 $F$ 的大小及深度无关，精确为

$$
\boxed{P_F=
\begin{cases}
[2L/a_\varepsilon,\ 2L/b_\varepsilon],
 &0\le\varepsilon<1/\sqrt{10},\\
[2L/a_\varepsilon,\ \infty),
 &1/\sqrt{10}\le\varepsilon<1/\sqrt2,\\
(0,\infty),&\varepsilon\ge1/\sqrt2.
\end{cases}}
\tag{20.8}
$$

$\varepsilon=0$ 时仅有 $p=2$；任意固定 $\varepsilon>0$ 都留下非单点歧义。
在有界情形两个端点均由同一个来源及各自一个共同控制取得。
对一个分别供应的深度 $n$，若误差给为
$|\operatorname{logit}q_n-\operatorname{logit}q_0|\le E$，则精确约束是

$$
\left|L+\tfrac p2\log(h/2)\right|\le E/n.
\tag{20.9}
$$

因此深度可缩小共同漂移，却不能单凭它把固定的控制不确定性从指数中分离。

证明。任一正深度的 $q_n=q_0=1/2$，由 (20.1) 都恰给 $d=0$。
$p=0$ 给 $d=L\ne0$，被排除。
$p>0$ 时，$d=0$ 等价于 $2|\lambda|^p=1$，
即 $|\lambda|=2^{-1/p}$ 及 (20.7) 的 $h(p)$。
实正相位使几何证书当且仅当 $h(p)\in H$；
其他允许相位仍由 (17.4) 限定，不要求它们都合格。
函数 $p\mapsto h(p)$ 在 $(0,\infty)$ 严格递增，
像为 $(0,2)$，其反解为 $p=2L/\log(2/h)$。
与定理 17.2 的 $H$ 相交并反解，或在定理 19.1 中取 $v_-=v_+=0$，
即得 (20.8)，包括临界 $h_+=2$ 只对应 $p\to\infty$，
及 $h_-=0$ 只对应 $p\downarrow0$ 的非取得端点。
若 $0<\varepsilon<1/\sqrt{10}$，则 $h_-<1<h_+$，
所以严格有 $2L/a_\varepsilon<2<2L/b_\varepsilon$。
更大容差的集合包含这些非单点见证，故亦不唯一。

对每个固定 $p$ 采用 (20.7) 中的同一个 $\lambda$，
所有活动树上均有 $2|\lambda|^p=1$，所以每个被供应的有限深度都保持质量一半。
这不是为每层选择一个新的控制，也不需要更换 $a,b$。
(20.9) 则由 (20.1) 直接除以 $n$。
这些共同见证即使在零读数误差时仍存在，故任何有限加深都不能排除它们。
这里没有假定实际无限细分，也没有让一个装置同时实现全部候选指数。
∎

**定义 20.5（条件综合所消费的先例与适用边界）。**
(17.2)–(20.9) 是固定三端口候选族上的条件逆问题及其细分应用，
作为 `repo-derived` 的纸面综合使用，不提出全球优先权。
本卷定理 13.3、14.2、15.1 及推论 15.2 分别供应精确平方标定、
已知幅度的细分漂移、系数双缺陷界及真概率到权重的消元；
这里的逆像还使用独立幅度比和指定几何证书，不改动那些结论的前提。
[V17 定理 2.3](AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)、
[V47 定理 4.2、命题 10.1](AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)
及本卷 §3 的 log／幂工具只作中间步骤；
V52 §§2、5 的商几何与二次不变量、V55 §§9–10 的滤波及 Riccati 结构亦不由本应用重新提出。

[Lax，*The Born Rule for Projective Measurements from Metric Non-Expansion and Calibration*，§§2–6、10.2](https://arxiv.org/html/2604.27339v2)
研究全曲线 Fisher 非扩张、平方根读数正则性和基准备标定下的 PVM 刚性。
这里的有限固定来源证书不是其全曲线条件，也不将其精确刚性结论当作本合同的误差逆像。
[Söllner 等，*Testing Born's Rule in Quantum Mechanics for Three Mutually Exclusive Events*，§§1.2、2.1](https://arxiv.org/html/1201.0195v1)
区分干涉偏离与独立探测器非线性标定；其计数、探测器与统计假设不提供 (17.1) 的幅度或射线证书。
这些几何、正则性及校准先例属于 `literature-attested` 的中间结构，
不作为新增的通用度量、分类或平方起源定理。

若把本合同接入实际来源，仍须保留假设 16.3 的范围。
[量子续卷 IV §§206–208](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)
把平方纤维权重、旧源率及检测响应列为输入；
[RRO §§62–67](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)
在指定自然过去域内讨论可测恢复。
二者均不替代本合同的独立证书，不把可测恢复提升为有限精度取得。
候选族外的一般门误差、近似乘性稳定性、源复制、完整过程认证、
复数域唯一性、张量结构或物理时间仍不由这个有限逆问题给出。

## 追加锚（本行以下为增补区）

## 21. 同一事件的相干幂读数与全部参数纤维

**假设 21.1（分别供应的有限相干前缀合同）。** 保留定义 13.1 和假设 13.2 的
复线性三端口、同一幅度坐标、非零 $a,b,\lambda$ 及同一事件 $C=\{1,2\}$。
权重采用定理 13.3 证明中已分类的 $w_p$，$p\ge0$，零点权重仍单独为零。
给定非空有限集合 $K\subset\mathbb N_0$，另行供应

$$
Q_k=\Pi_{w_p}(C\mid G_\lambda^k\psi),\qquad k\in K.
\tag{21.1}
$$

每个被供应的前缀从同一来源的同一 $\psi=(a,0,b)^{\mathsf T}$ 出发，
在读出之前执行同一个精确 $G_\lambda$ 的相干复合；中间不插入端口测量、
去相干、细分叶记录或活动块相对旁观块的重新标定。
$a,b,p,\lambda$ 在一个候选实现的所有前缀中固定；不同候选实现可以具有不同参数。
初始读数仅在 $0\in K$ 时列入本合同，不因记号而额外供应。
如果 (21.1) 被解释为实际概率，则同源制备、精确控制、指定前缀、端口对应及
同事件真概率的供应均是前件；这里只比较各前缀分别供应的律，未指定它们的联合抽样律。
不附加定理 13.3 的精确相干回返或粗事件守恒。
来源比 $r=|a|/|b|$ 与控制模 $|\lambda|$ 初始均未知，但都有限、严格正。

用 $Q_k$ 区别定义 20.1 中树形细分的 $q_n$。
本合同的相干复合与保留叶记录的区别，沿用
[V17 命题 13.1](AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)
中相干幂与逐步去相干递归的区别；它不将两个合同的报告互相替换。

**定理 21.2（奇偶 logit 关系及完整可观察纤维）。** 在假设 21.1 下，令

$$
L=\log2,\qquad e_k=k-2\lfloor k/2\rfloor\in\{0,1\},\qquad
Z_k=\operatorname{logit}Q_k.
$$

全部 $Q_k$ 严格在 $(0,1)$ 内，并精确满足

$$
\frac{Q_k}{1-Q_k}
=r^p|\lambda|^{kp}2^{p\lfloor k/2\rfloor+e_k}.
\tag{21.2}
$$

对 $p>0$ 定义

$$
u=p\log r,\qquad v=p\log(\sqrt2|\lambda|),\qquad t=\frac{pL}{2}>0.
$$

则

$$
\boxed{Z_k=u+kv+e_k(L-t),\qquad
Y_k:=Z_k-e_kL=u+kv-e_kt.}
\tag{21.3}
$$

给定任意精确报告 $Q=(Q_k)_{k\in K}\in(0,1)^K$，记
$M_K$ 的第 $k$ 行为 $(1,k,-e_k)$。它的全部正指数候选恰为

$$
\mathcal F_+(Q)=\{(u,v,t)\in\mathbb R^2\times(0,\infty):
M_K(u,v,t)^{\mathsf T}=Y\}.
\tag{21.4}
$$

对每个这样的点，全部原参数见证可且仅可写成

$$
\begin{gathered}
p=2t/L,\qquad r=e^{u/p},\qquad
|\lambda|=2^{-1/2}e^{v/p},\qquad h=2|\lambda|^2=e^{2v/p},\\
b=c,\qquad a=cr e^{i\phi},\qquad
\lambda=2^{-1/2}e^{v/p}e^{i\eta},\\
c\in\mathbb C^\times,\qquad \phi,\eta\in\mathbb R/(2\pi\mathbb Z).
\end{gathered}
\tag{21.5}
$$

所以即使 $(u,v,t)$ 唯一，来源的共同非零复尺度 $c$、来源相对相位 $\phi$
及控制相位 $\eta$ 仍全部自由。
零指数纤维则存在当且仅当

$$
\boxed{Z_k=e_kL\ (k\in K),\quad\text{即}\quad
Q_k=\begin{cases}1/2,&k\text{ 偶},\\2/3,&k\text{ 奇}.
\end{cases}}
\tag{21.6}
$$

在此纤维上 $r,|\lambda|$ 可分别为任意有限正数，$c,\phi,\eta$ 仍自由；
不得由 $u=v=t=0$ 反解除以 $p$ 的公式。
如果同时供应三个端口的概率，则偶数前缀恰为 $(Q_k,0,1-Q_k)$，
奇数前缀恰为 $(Q_k/2,Q_k/2,1-Q_k)$；它们在本模型内不细化上述纤维。

证明。由 $H_0^2=2I_2$，对每个 $m\ge0$ 有

$$
G_\lambda^{2m}\psi=((2\lambda^2)^ma,0,b)^{\mathsf T},\qquad
G_\lambda^{2m+1}\psi=(2^m\lambda^{2m+1}a,
2^m\lambda^{2m+1}a,b)^{\mathsf T}.
\tag{21.7}
$$

所有写出的活动幅度和旁观幅度均非零。偶数前缀有一个非零活动端口，
奇数前缀有两个相等的非零活动端口；其权重和除以旁观权重即得 (21.2)。
该计算对 $p=0$ 使用非零端口权重一、空端口权重零，给 (21.6)，
并未在空端口上使用 $0^0$。
对 $p>0$ 取实 log，并用 $\lfloor k/2\rfloor=(k-e_k)/2$，得到 (21.3)。

反向，任取 (21.4) 的一个点，以 (21.5) 构造参数。
指数、来源比和控制模均属于原允许域，且同一个 $a,b,\lambda$ 同时满足所有前缀等式。
任意原参数又由 $c=b$、$\phi=\arg(a/b)$、$\eta=\arg\lambda$ 唯一确定这些自由度，
故没有遗漏额外尺度或相位。$p=0$ 的任意非零原参数都给相同支持签名，
反之不符合该签名的报告不可能由 $p=0$ 产生。
奇数两个活动端口权重相等，偶数第二端口为空，给最后的端口断言。∎

**命题 21.3（概率族不认证相干回返）。** 在假设 21.1 的整个候选族上，
任意有限 $K$，乃至形式上全部非负整数前缀的概率族，都不能识别 $\phi$ 或 $\eta$，
也不能单凭这些概率认证 $[G_\lambda^2\psi]=[\psi]$。

证明。(21.2) 与两相位无关，故固定 $p,r,|\lambda|,c$ 而任意改变两相位保持全部报告。
尤其取 $|\lambda|=1/\sqrt2$，$\eta=0$ 给 $G_\lambda^2\psi=\psi$，
$\eta=\pi/2$ 给 $G_\lambda^2\psi=(-a,0,b)^{\mathsf T}$。
因 $ab\ne0$，后一向量与 $\psi$ 不同射线，而两个实现的全部前缀概率相同。
这是本卷命题 13.4 的同一相位障碍在完整前缀族中的保留。
相位与基概率的分离还见
[V47 命题 10.1](AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)
及 [V52 §§2、5](AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)；
这里未把完整外积关系缩减为其对角概率。∎

## 22. 未知来源比与未知控制模的最小前缀设计

**定理 22.1（指数识别的必要充分设计）。** 在假设 21.1 的未知 $r,|\lambda|$ 域内，
下列条件等价：

1. 精确报告在整个 $p\ge0$ 候选域识别指数，即相同报告的任意两个实现具有相同 $p$。
2. $K$ 至少含三个不同整数，且同时含奇数与偶数。
3. $M_K$ 的列秩为三。

满足这些条件时，正指数报告还唯一确定 $r,|\lambda|$，
但保留 (21.5) 的全部相位与尺度；零指数报告只确定 $p=0$，不确定两模长。
不满足这些条件时，每个具有正指数见证的精确报告，都具有每一个 $p>0$ 的见证。
特别地，零指数签名也与所有正指数相容。
因此最少需要三个不同前缀，三个中的奇偶不能全同。

证明。若 $K$ 至少有三个数且兼有奇偶，从同一奇偶类取 $i<j$，另一类取 $k$。
若 $A+Bn+Ce_n=0$ 对 $n\in K$ 成立，则在 $i,j$ 相减给 $B=0$，
再与 $k$ 比较给 $C=0$，最后 $A=0$。所以秩为三。
此时 (21.4) 至多一个解；两个正指数见证必有同一 $t,u,v$，
由 (21.5) 取得相同指数及两模长。
若一个正指数实现与零指数有同一报告，则其 $Y=0$，
满列秩迫使 $u=v=t=0$，与 $t>0$ 矛盾。
零指数内部的模长自由度已由定理 21.2 给出。

反之，若 $K$ 只有一种奇偶，$e_n$ 在 $K$ 上恒定；
若 $K$ 至多两个数，则总有实数 $\alpha,\beta$ 使 $e_n=\alpha+\beta n$ 对 $n\in K$ 成立。
这些情形覆盖条件 2 的全部否定情形，且使 $M_K$ 不满列秩。
固定任一正指数解 $(u_0,v_0,t_0)$，对任意 $t>0$ 置

$$
u(t)=u_0+\alpha(t-t_0),\qquad
v(t)=v_0+\beta(t-t_0).
\tag{22.1}
$$

于是 $u(t)+nv(t)-e_nt=u_0+nv_0-e_nt_0$。
(21.5) 对每个 $t>0$ 给一个有限非零的具体候选参数组，
不是仅有参数计数或无穷小变化。
对零指数签名 $Y=0$，直接取 $u=\alpha t,v=\beta t$ 即得所有正指数的见证。
因此条件 1 失败，且最后的强断言成立。∎

**推论 22.2（三个前缀的闭式与有效性判据）。** 若另供 $K=\{0,1,2\}$ 的精确概率，
置

$$
\widehat p=2+\frac{Z_0-2Z_1+Z_2}{L}.
\tag{22.2}
$$

若 $\widehat p>0$，全部正指数纤维的模长参数恰为

$$
p=\widehat p,\qquad u=Z_0,\qquad v=(Z_2-Z_0)/2,\qquad
r=e^{Z_0/p},\qquad h=e^{(Z_2-Z_0)/p}.
\tag{22.3}
$$

若 $\widehat p<0$，无允许候选。若 $\widehat p=0$，仅当
$(Z_0,Z_1,Z_2)=(0,L,0)$ 时有候选，且全部为零指数；其余报告无候选。
一般三个不同前缀也有闭式：取同奇偶的 $i<j$，另一奇偶的 $k$，令

$$
s=e_i=e_j,\quad \delta=e_k-s\in\{-1,1\},\quad
\alpha=\frac{j-k}{j-i},\quad \beta=\frac{k-i}{j-i}.
$$

则

$$
v=\frac{Z_j-Z_i}{j-i},\qquad
t=L-\frac{Z_k-\alpha Z_i-\beta Z_j}{\delta},\qquad
u=Z_i-iv-s(L-t).
\tag{22.4}
$$

$k$ 不必介于 $i,j$ 之间；这些式子包括外插。

证明。(21.3) 在同奇偶的 $i,j$ 相减确定 $v$。
$\alpha+\beta=1$、$\alpha i+\beta j=k$ 使差分消去 $u,v$，
留下 $Z_k-\alpha Z_i-\beta Z_j=\delta(L-t)$，即 (22.4)。
取 $i=0,j=2,k=1$ 得 (22.2)–(22.3)。
该三行矩阵可逆，所以 $t>0$ 时任意三个实 logits 均由唯一正指数点实现；
$t<0$ 不允许；$t=0$ 时正指数不允许，而零指数只允许 (21.6)。∎

**推论 22.3（另知来源比时最小数目可变）。** 若来源比已独立固定为 $r_*$，
令 $\ell_* =\log r_*$，$c_k=\ell_*-e_kL/2$。
在这个受限域内，指数可识别当且仅当

$$
(c_k)_{k\in K}\notin\operatorname{span}\{(k)_{k\in K}\}.
\tag{22.5}
$$

例如 $r_*\ne1$ 时，单独供应 $Q_0$ 已识别指数；
$r_*=1$ 时，前缀 $\{1,2\}$ 足够，而 $\{0,1\}$ 不足。
这些情形不降低定理 22.1 在未知来源比域中的最小数目。

证明。对 $p>0$，(21.3) 化为
$Y_k=pc_k+kv$，其中 $v$ 仍可为任意实数。
两个不同指数给相同 $Y$ 当且仅当 $c$ 是向量 $(k)$ 的倍数；
若 $c=\gamma(k)$，任意改变 $p>0$ 并把 $v$ 改为 $v-\gamma\,\Delta p$ 即给见证。
此时 $Y=0$ 也有所有正指数见证 $v=-\gamma p$，与零指数不能区分。
若 (22.5) 成立，线性关系迫使两个指数相等，
并排除正指数与 $Y=0$ 的零指数签名相交。
对 $K=\{0\}$，$(k)=0$ 而 $c_0=\ell_*$；
对 $r_*=1,K=\{1,2\}$，$c=(-L/2,0)$ 不与 $(1,2)$ 成比例；
$K=\{0,1\}$ 则 $c=(0,-L/2)$ 与 $(0,1)$ 成比例，得到各例。∎

## 23. 任意有限内区间报告的锋利共同参数逆像

**定义 23.1（确定性区间输入与正指数坐标域）。** 在假设 21.1 下，
每个 $k\in K$ 另供非空闭区间

$$
I_k=[\underline Q_k,\overline Q_k],\qquad
0<\underline Q_k\le\overline Q_k<1,
$$

含该前缀同事件的真概率，允许单点。
这些是确定性包含前件，不指定置信度或样本取得。
记

$$
[A_k,B_k]=\operatorname{logit}I_k,\qquad
 a_k=A_k-e_kL,\qquad b_k=B_k-e_kL,
$$

$$
\mathcal Q_K=\{(u,v,t)\in\mathbb R^3:
 a_k\le u+kv-e_kt\le b_k\ (k\in K)\}.
\tag{23.1}
$$

这里暂不限制 $t$，以便投影后另行施加 $t>0$；
$t=0$ 的形式坐标点不自动代表原零指数候选。

**定理 23.2（有限消元、全部端点及共同取得）。** 在定义 23.1 下，
对 $i,j\in K$ 定义仿射函数

$$
C_{ij}(t)=b_j-a_i+(e_j-e_i)t.
$$

当 $|K|\ge2$ 时定义两组有限非空仿射函数

$$
\mathcal V_-(t)=\left\{\frac{C_{ij}(t)}{j-i}:j<i\right\},\qquad
\mathcal V_+(t)=\left\{\frac{C_{ij}(t)}{j-i}:j>i\right\}.
\tag{23.2}
$$

构造关于实数 $t$ 的有限不等式表 $\mathcal T_K$：
对每个 $f\in\mathcal V_-$ 和 $g\in\mathcal V_+$ 加入 $f(t)\le g(t)$，
写成 $c_\nu t\le d_\nu$。
当 $|K|=1$ 时取空表。
若某行 $c_\nu=0,d_\nu<0$，置 $D_K=\varnothing$；
否则定义扩展实端点

$$
\tau_- =\max\left(\{-\infty\}\cup
 \{d_\nu/c_\nu:c_\nu<0\}\right),\qquad
\tau_+ =\min\left(\{+\infty\}\cup
 \{d_\nu/c_\nu:c_\nu>0\}\right),
$$

$$
D_K=\{t\in\mathbb R:\tau_-\le t\le\tau_+\}.
\tag{23.3}
$$

$\tau_->\tau_+$ 时此集为空；无限端点不表示有限参数的取得。
则所有区间同时兼容的指数恰为

$$
\boxed{P_{K,+}=\{2t/L:t\in D_K\cap(0,\infty)\},\qquad
P_K=P_{K,+}\cup P_{K,0},}
\tag{23.4}
$$

$$
P_{K,0}=\begin{cases}
\{0\},&A_k\le e_kL\le B_k\quad(k\in K),\\
\varnothing,&\text{其余情形}.
\end{cases}
\tag{23.5}
$$

这些判据为必要且充分。
特别地，$P_{K,+}$ 可能为空、正单点、有限区间、正半直线或整个 $(0,\infty)$。
在没有零系数矛盾行时，它非空当且仅当
$\tau_-\le\tau_+$ 且 $\tau_+>0$。
非空时每个有限正上端点、每个严格正下端点均取得；
若下确界为零，正指数支不取得零，仅按 (23.5) 决定是否另有零指数支。
$D_K=\{0\}$ 或 $D_K\subset(-\infty,0]$ 时没有正指数，
即使形式坐标可行，也不得用它宣告原候选存在。

对每个 $t\in D_K\cap(0,\infty)$，全部正指数见证由下面同一组参数给出：
当 $|K|\ge2$，任选

$$
\max\mathcal V_-(t)\le v\le\min\mathcal V_+(t),\qquad
\max_{k\in K}(a_k-kv+e_kt)\le u\le
\min_{k\in K}(b_k-kv+e_kt),
\tag{23.6}
$$

再应用 (21.5)；$|K|=1$ 时 $v$ 任取实数，再按同一式取 $u$。
全部自由相位与尺度均保留。
零指数兼容时，任意非零 $a,b,\lambda$ 同时实现所有区间。

证明。给定 $v,t$，共同 $u$ 存在当且仅当 (23.6) 的下界不大于上界。
有限最大下界不超过有限最小上界，等价于对所有 $i,j\in K$ 有

$$
a_i-iv+e_it\le b_j-jv+e_jt,
\quad\text{即}\quad (j-i)v\le C_{ij}(t).
\tag{23.7}
$$

$i=j$ 的条件是已有的 $a_i\le b_i$。
$j<i$ 给 $v$ 的下界，$j>i$ 给上界；因两组非空有限，
共同有限 $v$ 存在当且仅当两组的每个下界都不超过每个上界。
这正是表 $\mathcal T_K$，且反向可以先取一个 $v$，再取一个 $u$。
单前缀时一个 $u$ 总能实现该区间，故投影为全实轴。
按每行 $c_\nu$ 的符号反解，得到 (23.3)，
包括零系数矛盾、无上界、无下界及端点相等的情形。
所以 $D_K$ 正是 $\mathcal Q_K$ 在 $t$ 轴上的投影，且每个属于投影的有限点都有原像。

对 $t>0$，(21.5) 将这些原像逐点还原为一个共同的 $p,a,b,\lambda$；
(21.3) 和严格递增的 logit 使全部真概率落入给定区间。
任一正指数原候选又必须产生该表中的一个点，故两向包含均成立。
正下端点和有限正上端点属于闭集 $D_K$，以上反向构造证明其同时取得，
不需要把每个报告各自取得的不同控制拼接。
$p=0$ 时只允许 (21.6)，恰给 (23.5)，并保留其全部原参数自由度。
这也证明所列空集及零端点判据。

上述消元在此仅消费标准的有限半空间投影：
[Goemans，*Linear Programming and Polyhedral Combinatorics*，§3 开篇，定义 3.4 后的 Fourier–Motzkin 消元](https://math.mit.edu/~goemans/18433S15/polyhedral.pdf)
明确给出最大下界与最小上界的反向见证；
[Boyd–Vandenberghe，*Convex Optimization*，§§2.2.4、4.3](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)
给出多面体与线性约束表述。
(23.7) 已把所需两次消元完整写出，不另提出一般线性规划或投影定理。∎

**推论 23.3（充分设计的有限锋利界）。** 若 $K$ 满足定理 22.1 的设计条件，
则 $\mathcal Q_K$ 或为空，或为有界闭集，故非空 $D_K$ 有有限且取得的两端点。
因此非空正指数集合总有有限上端点，但其下确界仍可为不取得的零。
若设计条件失败而 $\mathcal Q_K$ 非空，则 $D_K=\mathbb R$，
从而 $P_{K,+}=(0,\infty)$；单凭这些区间不能给正指数上界。

取同奇偶的 $i<j$ 和另一奇偶的 $k$，使用 (22.4) 的 $\alpha,\beta,\delta$，
置仅支撑在这三个前缀上的系数

$$
\gamma_i=\alpha/\delta,\qquad
\gamma_j=\beta/\delta,\qquad \gamma_k=-1/\delta.
$$

则对所有共同候选均有 $t=\sum_n\gamma_nY_n$，因此

$$
T_-:=\sum_{\gamma_n\ge0}\gamma_na_n+
       \sum_{\gamma_n<0}\gamma_nb_n
\le t\le
T_+:=\sum_{\gamma_n\ge0}\gamma_nb_n+
       \sum_{\gamma_n<0}\gamma_na_n.
\tag{23.8}
$$

若 $K$ 恰为这三个数，$D_K=[T_-,T_+]$，界为锋利界；
若另有其他前缀，(23.8) 只是必要界，全部兼容性仍由定理 23.2 决定。
特别地，对 $K=\{0,1,2\}$，正指数集合精确为

$$
\boxed{(0,\infty)\ \cap\
\left[2+\frac{A_0+A_2-2B_1}{L},\quad
      2+\frac{B_0+B_2-2A_1}{L}\right],}
\tag{23.9}
$$

零指数仍单独检验 $0\in[A_0,B_0]$、$L\in[A_1,B_1]$、$0\in[A_2,B_2]$。

证明。满列秩允许选出三个可逆行。
这三行的 $Y$ 分别属于有限闭区间，逆矩阵将其盒子映为有界闭集，
$\mathcal Q_K$ 是其中的闭子集，故紧致；投影的端点亦取得。
设计条件失败时，证明 22.1 中的 $e_n=\alpha+\beta n$ 成立。
对 $\mathcal Q_K$ 任一点沿 (22.1) 的同一方向平移，保持全部区间，
并能将 $t$ 变成任意实数，所以 $D_K=\mathbb R$。

(22.4) 减去 $e_nL$ 后给 $t=\sum\gamma_nY_n$。
按每个系数的符号取区间端点，即得 (23.8)。
恰有三行时可逆矩阵将整个 logits 盒子双射到 $\mathcal Q_K$，
线性函数 $\sum\gamma_nY_n$ 的最小值和最大值均在所述盒角取得。
盒子内连接这两个角的线段又实现两值之间的每一点，故没有缺口。
这证明三前缀的锋利性；更多前缀要过滤同一盒像，不保证各三行的见证相同。
代入 $i=0,j=2,k=1$ 得 (23.9)。∎

**命题 23.4（不一致、单点与不取得的零下界）。** 令
$\sigma(x)=e^x/(1+e^x)$，以下用 $J_k=[A_k,B_k]$ 指定
$I_k=\sigma(J_k)$；所有概率区间均为严格内区间。

(a) 对 $K=\{0,2,4\}$，精确 logits $Z_0=Z_2=0,Z_4=1$ 无候选，
尽管任一单前缀报告都分别具有每个 $p>0$ 的见证。

(b) 对 $K=\{0,1,2\}$，取任意 $t_*>0,c\in\mathbb R$，
$J_0=J_2=\{c\},J_1=\{c+L-t_*\}$，则指数集合恰为 $\{2t_*/L\}$。
$J_0=J_2=\{0\},J_1=\{L\}$ 则恰给 $\{0\}$。

(c) 取 $c>0,d>0$，$J_0=J_2=\{c\}$、$J_1=[c+L-d,c+L]$，
则全部指数集合为 $(0,2d/L]$，下确界零不取得。
把 $d$ 置为零时，形式坐标域非空而原候选集合为空。

证明。(a) 偶数前缀要求 $Z_k=u+kv$。
前两个报告给 $u=v=0$，与 $Z_4=1$ 矛盾；零指数也不满足最后一个报告。
任意一个报告则可先任选 $p>0,|\lambda|>0$，再按 (21.2) 选择 $r>0$ 实现。

(b) 三行逆式给 $u=c,v=0,t=t_*>0$，故唯一指数如述。
第二组报告只有 $t=0,u=v=0$，正指数不允许而支持签名恰合格。

(c) 三行约束给 $u=c,v=0,0\le t\le d$。
每个 $0<t\le d$ 均由 $p=2t/L,r=e^{c/p},|\lambda|=1/\sqrt2$ 同时实现，
所有相位与非零共同尺度任取。零指数却要求 $Z_0=0$，与 $c>0$ 矛盾。
当 $p\downarrow0$ 时，此见证族的 $r\to\infty$；每个见证的振幅比仍有限，
但不存在一个有限比的零指数极限候选。
$d=0$ 时 $\mathcal Q_K=\{(c,0,0)\}$，没有正指数，支持签名又失败。
这说明投影中的零点与原零指数支不可混同。∎

## 24. 在同一前缀纤维中保留旧标定与射线证书

**定理 24.1（独立来源限制及射线证书的同见证过滤）。** 在定义 23.1 下，
另行供应非空来源比集合 $R\subset(0,\infty)$ 及有限 $\varepsilon\ge0$，
要求同一候选满足

$$
r\in R,\qquad D([G_\lambda^2\psi],[\psi])\le\varepsilon.
\tag{24.1}
$$

若同时保留旧合同的初始、一次概率区间，则将已供应的 $0,1$ 纳入同一索引集合；
同一前缀的多个区间先取交，空交即无候选。
这一合并只联合已有供应，不为缺少的前缀增添读数。

令 $H_\varepsilon(r)$ 与 $T_\varepsilon(r,h)$ 逐个 $r$ 按 (17.3)–(17.4) 定义。
全部正指数候选恰为 (23.1) 中满足

$$
\begin{gathered}
t>0,\quad p=2t/L,\quad r=e^{u/p}\in R,\quad h=e^{2v/p},\\
h\in H_\varepsilon(r),\qquad
\cos(2\eta)\ge T_\varepsilon(r,h)
\end{gathered}
\tag{24.2}
$$

的点及相位，再由 (21.5) 还原；来源的 $c,\phi$ 仍自由。
若仅求存在一个合格相位，可省略 (24.2) 的最后一行，但不能省略
同一点的 $h\in H_\varepsilon(r)$。
该判据给全部允许相位弧及 $\lambda$ 的两个平方根分支。
零指数候选先检验 (23.5)，再以任意 $r\in R$、$h>0$ 及同一相位条件过滤；
因 $h=1,\eta=0$ 总合格，$R$ 非空时零指数存在性恰由 (23.5) 决定。

特别地，若旧合同独立固定 $r=r_*$，在同一 $\mathcal Q_K$ 中加入

$$
u=(2\log r_*/L)t,
\tag{24.3}
$$

然后使用 $H_\varepsilon(r_*)$ 即可。
若另给 $0<r_-\le r\le r_+<\infty$，比值限制等价于
$(2\log r_-/L)t\le u\le(2\log r_+/L)t$。
但 $r$ 未固定时，射线条件仍含 $r=e^{u/p}$ 与 $h=e^{2v/p}$ 的联合非线性关系，
不能把某个先选的来源比给出的 $H$ 当作与 $u,t$ 无关的固定线性条件。
若旧合同固定的是字面 $a_*,b_*$，还须在 (21.5) 中固定
$c=b_*$、$re^{i\phi}=a_*/b_*$，而不是为不同前缀另取来源。

证明。定理 17.2 的距离恒等式对任意有限 $r,h>0$ 及
$2\lambda^2=he^{2i\eta}$ 都成立；它不依赖 $p$。
把 (21.5) 还原的同一参数代入 (17.2)，完整距离条件恰为
$\cos(2\eta)\ge T_\varepsilon(r,h)$。
存在这样的相位恰为 $h\in H_\varepsilon(r)$，且实正相位 $\eta=0$ 可实现每个这样的 $h$。
故 (24.2) 与全部概率区间、来源限制及射线证书同时等价。
反向选取同一点、同一相位并用 (21.5)，就得到所需共同见证；
不同条件分别存在见证不替代这个共同存在量词。
$p=0$ 时概率只依赖支持，而几何仍检验所选择的实际 $r,h,\eta$；
$h=1,\eta=0$ 使距离为零，证明零指数存在性断言。
(24.3) 及有界比值条件由 $u=p\log r$、$p>0$ 直接等价变换得到。
未知比值时，存在相位所需的条件具体为

$$
\frac{e^{u/p}|e^{2v/p}-1|}
{\sqrt{(1+e^{2u/p})(1+e^{2u/p}e^{4v/p})}}\le\varepsilon,
\tag{24.4}
$$

其 $r$ 与 $h$ 必须来自同一点；(23.3) 对纯概率的区间形状不自动扩展到该过滤像。
字面固定来源只需在完整还原纤维中取其对应的尺度与相位，距离式保持不变。∎

**定理 24.2（额外相干概率对定理 20.4 歧义的直接消费）。** 保留定理 20.4 的
平衡来源 $r=1$、任意非空有限树深度集合 $F$、全部精确树报告
$q_0=q_n=1/2$（$n\in F$）及同一几何容差。
令 $P_F$ 为 (20.8) 的精确候选指数集合。
现在另按假设 21.1 供应同一来源、同一控制、同事件的相干前缀概率。
对每个这样的共同候选，精确有

$$
\boxed{\operatorname{logit}Q_k=\lfloor k/2\rfloor(p-2)L.}
\tag{24.5}
$$

因此单独另供任一 $k\ge2$ 的相干真概率便确定

$$
p=2+\frac{\operatorname{logit}Q_k}{\lfloor k/2\rfloor L},
\tag{24.6}
$$

并仅在此值属于 $P_F$ 时兼容。
若另供有限集合 $K$ 上的闭内区间 $I_k$，记其 logits 为 $[A_k,B_k]$，
则全部共同指数精确为

$$
\boxed{P_F\ \cap\!
\bigcap_{\substack{k\in K\\k\ge2}}
\left[2+\frac{A_k}{\lfloor k/2\rfloor L},\quad
      2+\frac{B_k}{\lfloor k/2\rfloor L}\right],}
\tag{24.7}
$$

前提是每个供应的 $k\in\{0,1\}$ 都满足 $0\in[A_k,B_k]$；
若任一个失败，集合为空。
每个允许指数均由同一个 $|\lambda|=2^{-1/p}$ 实现全部树与相干报告，
允许相位恰按 (17.4) 用 $r=1,h=2^{1-2/p}$ 过滤。
特别地，另供 $Q_2=1/2$ 给 $p=2,h=1$；单供 $Q_0,Q_1$ 不缩小 $P_F$。

证明。定理 20.4 已给 $p>0$ 和 $|\lambda|=2^{-1/p}$，
故 (21.3) 的 $u=0$、$v=(p/2-1)L$。
代入得

$$
Z_k=(k-e_k)(p/2-1)L=\lfloor k/2\rfloor(p-2)L,
$$

即 (24.5)。$k\ge2$ 时系数严格正，反解给 (24.6)，
逐个单调反解区间给 (24.7)；$k=0,1$ 时恒为零。
任一 $p\in P_F$ 取实正 $\lambda=2^{-1/p}$，由定理 20.4 同时实现所有旧树报告和几何证书，
又由 (24.5) 同时实现新相干区间。
其余允许相位不影响这些概率，并由原距离条件逐点限定，所以必要性与共同取得性均成立。
新增约束来自另行供应的相干复合报告；在固定树合同内增加 $F$ 的深度或大小仍保持
定理 20.4 的原歧义，不能据此取得 (24.5) 的数据。∎

**命题 24.3（平方标定后仍保留的相位歧义）。** 在定理 24.2 的额外报告
$Q_2=1/2$ 下，任意 $\varepsilon>0$ 仍允许不精确回返的相位见证。
当 $\varepsilon=0$ 时，原射线证书另行迫使 $\lambda=\pm1/\sqrt2$；
这一相位结论来自证书而非概率。

证明。此时 $p=2,r=h=1$。由 (17.2)，
$D([G_\lambda^2\psi],[\psi])=|\sin\eta|$。
任意 $\varepsilon>0$ 可取 $0<\eta<\pi/2$ 且 $\sin\eta\le\varepsilon$，
并置 $\lambda=e^{i\eta}/\sqrt2$。
全部树报告及全部相干报告均为一半，射线证书合格，却有 $e^{2i\eta}\ne1$，故不回返。
$\varepsilon=0$ 则要求 $\sin\eta=0$，即 $\eta=0$ 或 $\pi$ 模 $2\pi$，得到两个实根。
来源相对相位及共同尺度在两种情形下仍未由概率识别。∎

**定义 24.4（条件综合的来源与适用域）。** (21.1)–(24.7) 的对象是本卷指定
三端口候选族上的同事件有限逆问题，作为 `repo-derived` 的条件纸面综合使用。
承重增量是未知来源比与控制模下相干奇偶报告的完整纤维、最小设计、
任意有限内区间的共同取得及其对 (20.8) 的额外数据过滤；
不把标准秩计算、有限半空间消元、乘性分类、Hopf 坐标或酉群表示另立为新通用结果。
来源复用为本卷定义 13.1、假设 13.2、定理 17.2 及 §§18–20，
[V17 §2、命题 13.1](AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)
的 log 坐标和两种递归，
[V47 §§4、10](AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)
的幂分类与相位限制，
[V52 §§2、5](AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)
的商几何及共同相位不变量，
[V55 §§9–10](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)
的几何与条件动力学边界。
标准有限半空间工具的文献适用域见定理 23.2 所附作者来源；
上述有限三端口综合不据此主张全球优先权。

实际供应仍须满足假设 21.1 和 16.3；(23.4) 的可识别性是精确概率或确定性包含区间上的
纤维结论，不等于有限样本可取得、可认证或具有给定资源界的估计。
[量子续卷 IV §§206–208](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)
的平方检测权重、既定率和历史桥仍是其各自输入，不供应这里的概率或控制。
概率 $0,1$ 若作为单点报告，在本卷 $ab\lambda\ne0$ 的有限前缀域没有见证；
本节内区间反演不把无穷 logit 当作有限参数。
正指数纤维的闭包不替代 (21.6) 的零指数支，端口概率不补回相位回返。
一般过程认证、实际控制或复制权限、近似乘性稳定性、复数域唯一性、
张量复合、物理时间及无前件量子起源均不属于这个逆问题的结论。

## 追加锚（本行以下为增补区）

## 25. 共享变动标定路径的相干前缀纤维

**假设 25.1（一条路径、全部连续前缀与两种分别声明的漂移承诺）。**
沿用定义 13.1 的有限值非负乘性权重及未归一闭单位盘有界性，
采用定理 13.3 证明中已分类的 $w_p$，$p\ge0$；零点始终单独取零。
保留假设 21.1 的同源、复线性三端口、同一幅度坐标、
$\psi=(a,0,b)^{\mathsf T}$、$ab\ne0$、旁观系数一及同一事件 $C=\{1,2\}$。
将其中重复的同一个标量改为一条预先固定、各项有限非零的路径

$$
G_j=(\lambda_jH_0)\oplus1,\quad \lambda_j\in\mathbb C^\times,
\qquad P_0=I_3,\quad P_k=G_k\cdots G_1\quad(1\le k\le N).
\tag{25.1}
$$

每个候选共用同一 $a,b,p,\lambda_1,\ldots,\lambda_N$；
第 $k$ 个比较使用这条路径的前 $k$ 项，不为不同终点重新选择路径。
另行供应全部连续前缀 $k=0,\ldots,N$ 的同事件真概率
$Q_k=\Pi_{w_p}(C\mid P_k\psi)$，或含这些真概率的确定性闭内区间。
中间不测量、不去相干、不记录细分叶，也不重新标定活动块相对旁观块。
各前缀分别供应的概率不被当作逐步测量的联合抽样律。
主要结论取有限 $N\ge2$，记 $m=N-1$、$L=\log2$；
$N\le1$ 的空约束边界另述。

定义实 log 模长、奇偶记号及相邻变化

$$
x_j=\log(\sqrt2|\lambda_j|),\qquad
 e_k=k-2\lfloor k/2\rfloor,\qquad s_i=(-1)^i,
\qquad \delta_i=x_{i+1}-x_i\quad(1\le i\le m).
\tag{25.2}
$$

以下是两种不同的、必须分别供应的承诺，预算均有限非负：

$$
\mathsf E_D:\quad |\delta_i|\le D\quad(1\le i\le m),
\qquad
\mathsf T_V:\quad \sum_{i=1}^m|\delta_i|\le V.
\tag{25.3}
$$

$x_j$ 加同一个常数不改变这两个承诺；没有对 $x_1$、原始模长、
控制相位或相位变化给出界。$\mathsf T_V$ 只含一个全路径预算，
不表示每个相邻变化都可各花一次 $V$。
两者若同时供应就同时检验，未供应者不自动加入。
来源比 $r=|a|/|b|$ 初始未知且有限正；若另知来源，则在下面的同一纤维中限制它。
这些前件不供应制备、复制、重置、相干控制、概率区间的取得或置信度。

**定理 25.2（全部正指数与零指数原参数纤维）。**
给定任意精确 logits $z_k=\operatorname{logit}Q_k\in\mathbb R$，$0\le k\le N$。
对 $p>0$，全部原参数见证恰为

$$
\begin{aligned}
u&=z_0,\qquad r=\exp(z_0/p),\\
x_j&=\frac{z_j-z_{j-1}-(-1)^{j+1}(L-pL/2)}p,
       &&1\le j\le N,\\
b&=c,\qquad a=cr e^{i\phi},\qquad
\lambda_j=2^{-1/2}e^{x_j}e^{i\eta_j},\\
c&\in\mathbb C^\times,\qquad
\phi,\eta_1,\ldots,\eta_N\in\mathbb R/(2\pi\mathbb Z),
\end{aligned}
\tag{25.4}
$$

其中仅保留满足已供应漂移承诺的 $x$。
每个正指数及整个 logit 向量确定唯一 $r$ 和唯一模长路径，
但共同非零复尺度、来源相对相位及每步控制相位全部自由。
不加漂移承诺时，任意有限实 $z$ 都有每个 $p>0$ 的见证。
若另行固定 $r=r_*$，就在同一纤维中加入 $z_0=p\log r_*$；
若字面固定来源 $a_*,b_*$，还须取 $c=b_*$、$re^{i\phi}=a_*/b_*$。
这些限制对所有前缀共同施加，不为不同终点重新选择来源。

零指数有见证当且仅当

$$
z_k=e_kL\quad(0\le k\le N),\qquad
Q_k=\begin{cases}1/2,&k\text{ 偶},\\2/3,&k\text{ 奇}.
\end{cases}
\tag{25.5}
$$

此时 $r$ 为任意有限正数，$c,\phi,\eta_j$ 自由，
$x$ 为满足所供应承诺的任意有限实路径。
两种预算均非负，故常路径 $x_j=0$ 总给零指数的一个合格模长见证。
不能把 (25.4) 在 $p=0$ 代入，或从形式坐标 $u=0$ 推断零指数的 $r=1$。

若另供完整端口概率，偶数前缀为 $(Q_k,0,1-Q_k)$，
奇数前缀为 $(Q_k/2,Q_k/2,1-Q_k)$，在这个控制形状内不再细化纤维。

证明。令 $\Lambda_k=\prod_{j=1}^k\lambda_j$，$\Lambda_0=1$。
活动块是标量乘同一个 $H_0$，故所有标量可交换，$H_0^2=2I_2$ 给

$$
P_{2h}\psi=(2^h\Lambda_{2h}a,0,b)^{\mathsf T},\qquad
P_{2h+1}\psi=(2^h\Lambda_{2h+1}a,
                2^h\Lambda_{2h+1}a,b)^{\mathsf T}.
\tag{25.6}
$$

所有显示的活动幅度及旁观幅度非零，因此归一分母有限正，且

$$
\frac{Q_k}{1-Q_k}
=r^p|\Lambda_k|^p2^{p\lfloor k/2\rfloor+e_k},\qquad
z_k=u+p\sum_{j=1}^kx_j+e_k(L-pL/2),\quad u=p\log r.
\tag{25.7}
$$

这里实 log 只用于正数，未取复 log。
$p>0$ 时，$k=0$ 确定 $u$；相邻两式相减唯一确定每个 $x_j$，即 (25.4)。
反向按 (25.4) 取任意相位与尺度，逐项求和使 (25.7) 望远镜消去，
同时恢复所有给定 $z_k$，没有为不同终点另取来源或控制。
任一原参数组又可由 $c=b$、$\phi=\arg(a/b)$、$\eta_j=\arg\lambda_j$ 表示，
所以这确为全部纤维。
$p=0$ 时每个非零端口权重一、空端口权重零，(25.6) 直接给 (25.5)，
不对空端口使用 $0^0$。支持签名外没有零指数见证；签名内的模长与相位均不影响概率。
最后，奇数的两个活动幅度相等，偶数的第二活动幅度为零，给端口断言。∎

**命题 25.3（无模长漂移、无承诺及相位边界）。**
$D=0$ 或 $V=0$ 恰要求全部 $|\lambda_j|$ 相同。
此时 (25.7) 的概率式化为 (21.3)，故概率层面恢复 §§21–23 的固定模长逆问题；
只有再要求 $\eta_j$ 相同，才恢复字面上重复同一个复控制。
若去掉两种漂移承诺，则任意内区间报告都兼容所有正指数，
零指数仍只按 (25.5) 单独判断。
即使知道全部模长路径，端口概率也不认证 $[P_2\psi]=[\psi]$。

证明。非负绝对值的和为零当且仅当每一项为零，
故两种零预算都给 $x_j=x_1$；反向显然。
将常值代入 (25.7) 即得 (21.3)，相位仍未进入等式。
无承诺时从每个内区间各取一个有限 logit，(25.4) 对任意 $p>0$ 给共同见证。
回返方面，$P_2\psi=(2\lambda_2\lambda_1a,0,b)^{\mathsf T}$；
因 $ab\ne0$，射线回返当且仅当 $2\lambda_2\lambda_1=1$。
在 $|\lambda_1|=|\lambda_2|=1/\sqrt2$ 时，将 $\eta_1+\eta_2$ 从零改成 $\pi$
保持全部概率与两种漂移预算，却将活动幅度反号，故不回返。
这是命题 21.3 的相位障碍在共享变动路径上的保留。∎

## 26. 精确连续报告的两种预算逆像与阈值

**定理 26.1（逐相邻 log 模长界的完整精确逆像）。**
在假设 25.1 下，对 $1\le i\le m$ 置

$$
\Delta^2z_i=z_{i+1}-2z_i+z_{i-1},\qquad
R_i=2L-s_i\Delta^2z_i,\qquad
R_{\min}=\min_iR_i,\quad R_{\max}=\max_iR_i.
\tag{26.1}
$$

仅供应 $\mathsf E_D$ 时，兼容正指数恰满足

$$
\boxed{|R_i-pL|\le pD\quad(1\le i\le m),\quad p>0.}
\tag{26.2}
$$

完整闭式如下；所有集合再与 $(0,\infty)$ 相交。

(a) $0\le D<L$：若有 $R_i\le0$，集合为空；否则为

$$
\left[\frac{R_{\max}}{L+D},\frac{R_{\min}}{L-D}\right],
\tag{26.3}
$$

下端点大于上端点时仍为空，相等时为正单点。

(b) $D=L$：若有 $R_i<0$，集合为空；否则为

$$
(0,\infty)\cap\left[\frac{R_{\max}}{2L},\infty\right).
\tag{26.4}
$$

(c) $D>L$：总为非空无界集合

$$
(0,\infty)\cap
\left[\max\left\{0,\frac{R_{\max}}{L+D},
                         \frac{-R_{\min}}{D-L}\right\},\infty\right).
\tag{26.5}
$$

每个有限正端点由 (25.4) 的同一个来源与路径取得。
零指数应且仅应在 (25.5) 成立时另加，不能由正支的下确界代替。
特别地，$D=0$ 时正支存在当且仅当所有 $R_i$ 等于同一个正数，
其指数为该数除以 $L$。

证明。对 (25.7) 取二阶差分，因 $\Delta^2e_i=2s_i$，得到

$$
\Delta^2z_i=p\delta_i+s_i(2-p)L,
\qquad R_i=p(L-s_i\delta_i).
\tag{26.6}
$$

因此 (26.2) 与全部相邻漂移界等价。
反向由 (25.4) 还原路径时，同一个恒等式给
$\delta_i=s_i(L-R_i/p)$，恰满足所需承诺，故判据充分。
若 $D<L$，(26.2) 等价于
$p(L-D)\le R_i\le p(L+D)$，强迫 $R_i>0$，
并分别给 (26.3) 的共同上下界。
$D=L$ 时等价于 $0\le R_i\le2pL$，得到 (26.4)。
$D>L$ 时正 $R_i$ 只给第一种下界，负 $R_i$ 只给第二种下界，
零值不给限制，合并就是 (26.5)。
这些是不严格有限线性不等式；任一属于其中的有限正端点均经 (25.4) 给有限非零参数。
零指数签名与漂移无关，且有常路径见证，故只按 (25.5) 判断。∎

**定理 26.2（一个总变差预算的完整精确逆像）。**
仅供应 $\mathsf T_V$ 时，兼容正指数恰为

$$
\boxed{\sum_{i=1}^m|R_i-pL|\le pV,\qquad p>0.}
\tag{26.7}
$$

以下有限表给其全部端点，包括空集及单点。
对每个 $\sigma\in\{-1,1\}^m$ 置

$$
A_\sigma=\sum_i\sigma_iR_i,\qquad
C_\sigma=V+L\sum_i\sigma_i.
\tag{26.8}
$$

若某行 $C_\sigma=0,A_\sigma>0$，正支为空；否则定义

$$
p_- =\max\left(\{0\}\cup\{A_\sigma/C_\sigma:C_\sigma>0\}\right),
\qquad
p_+ =\min\left(\{+\infty\}\cup\{A_\sigma/C_\sigma:C_\sigma<0\}\right).
\tag{26.9}
$$

正支精确为 $(0,\infty)\cap[p_-,p_+]$。
它非空当且仅当没有上述矛盾行、$p_-\le p_+$ 且 $p_+>0$；
$p_-=p_+>0$ 给单点，其余有限正端点均取得。
零指数仍仅按 (25.5) 另加。

有界性的全部阈值为：

1. $V<mL$ 时，每个非空正支有有限正上端点，且
   $p\le\sum_iR_i/(mL-V)$。
2. $V=mL$ 时，正支非空当且仅当 $\sum_iR_i\ge0$；一旦非空便无界。
3. $V>mL$ 时，对任意有限报告，总有全部充分大的有限 $p$ 合格。

若至少一个 $R_i\ne0$，非空正支的下端点严格正；
若全部 $R_i=0$，则 $V<mL$ 时正支为空，$V\ge mL$ 时正支为 $(0,\infty)$。

证明。(26.6) 给
$\sum_i|\delta_i|=p^{-1}\sum_i|R_i-pL|$，
故 (26.7) 必要且经 (25.4) 充分。
有限实向量 $v$ 满足 $\sum_i|v_i|=\max_\sigma\sum_i\sigma_iv_i$：
任意符号和不超过绝对值和，按每个非零项的符号取 $\sigma_i$ 即取等。
应用于 $v_i=R_i-pL$，(26.7) 等价于全部 $A_\sigma\le C_\sigma p$。
按 $C_\sigma$ 的正、负、零分别解出下界、上界和矛盾行，即得 (26.9) 及所有端点判据。
反向见证仍为同一个 (25.4)，不将各项分别取得的路径拼合。

对全负号一行，有 $(mL-V)p\le\sum_iR_i$，证明第一项。
为判定临界及超临界域，令 $\rho=1/p>0$，则 (26.7) 等价于

$$
f(\rho):=\sum_i|\rho R_i-L|\le V,\qquad f(0)=mL.
\tag{26.10}
$$

全部充分小的正 $\rho$ 都满足 $\rho R_i<L$，所以
$f(\rho)=mL-\rho\sum_iR_i$。
若 $V=mL$ 且和非负，这已给任意大的合格 $p$；
若和为负，则对所有 $\rho>0$ 有
$f(\rho)\ge\sum_i(L-\rho R_i)>mL$，故没有正支。
若 $V>mL$，由上述小 $\rho$ 公式同样得到所有充分大的 $p$ 合格。
又由三角不等式，(26.7) 推出
$\sum_i|R_i|\le p(V+mL)$，故非零 $R$ 给严格正下界。
$R=0$ 时 (26.7) 就是 $mL\le V$。
零指数的判断独立，证明完毕。∎

**推论 26.3（支持签名的精确正零混淆边界）。**
对完整零指数签名 $z_k=e_kL$，所有 $R_i=0$。
它与正指数混淆，当且仅当逐相邻预算 $D\ge L$，
或在单独使用总变差承诺时 $V\ge mL$。
越过相应阈值后，该签名与每个 $p>0$ 相容；阈值本身已取得。
一个共同平衡来源上的正指数见证为

$$
a=b=1,\qquad
\lambda_j=\begin{cases}1,&j\text{ 奇},\\1/2,&j\text{ 偶},\end{cases}
\qquad x_j=(-1)^{j+1}L/2.
\tag{26.11}
$$

它有 $|\delta_i|=L$、总变差 $mL$，并且每两个相邻控制复合均为 $I_3$。
$p=0$ 则可在同一平衡来源上取常控制 $\lambda_j=1/\sqrt2$。

证明。将 $R=0$ 代入 (26.2)、(26.7) 即得必要阈值及正支的全部指数。
(26.11) 中任意两个相邻标量的乘积为 $1/2$，所以
$G_{j+1}G_j=((\lambda_{j+1}\lambda_j)H_0^2)\oplus1=I_3$。
偶数前缀回到 $\psi$，奇数前缀为 $(1,1,1)^{\mathsf T}$，
故对所有 $p\ge0$ 读数恰为 (25.5)。
$x$ 的相邻差绝对值为 $L$，直接取得阈值。
这里是指定变动控制的回返，不能据此声称同一个控制重复两次也回返。∎


## 27. 共享真 logit 向量的有限内区间逆像

**定义 27.1（共同区间盒及两种路径约束）。**
对所有 $k=0,\ldots,N$，另供非空闭区间

$$
I_k\subset(0,1),\qquad J_k=\operatorname{logit}I_k=[\alpha_k,\beta_k],
\qquad \mathcal B=\prod_{k=0}^NJ_k.
\tag{27.1}
$$

端点均为有限实数，允许单点；同一前缀若已有多个区间，先取交。
空交即无候选。对一个共同 $z\in\mathcal B$ 定义
$R_i(z)=2L-s_i(z_{i+1}-2z_i+z_{i-1})$。
记下列两个有限线性约束域；此处暂允许 $p\in\mathbb R$，正支再另取 $p>0$：

$$
\begin{aligned}
\mathcal H_E&=\{(z,p):z\in\mathcal B,\
 -pD\le R_i(z)-pL\le pD\ (1\le i\le m)\},\\
\mathcal H_T&=\{(z,p):z\in\mathcal B,\
 \sum_i\sigma_iR_i(z)\le p(V+L\sum_i\sigma_i)
 \quad(\sigma\in\{-1,1\}^m)\}.
\end{aligned}
\tag{27.2}
$$

$\mathcal H_T$ 在 $p>0$ 上等价于
$\sum_i|R_i(z)-pL|\le pV$。
两种承诺同时供应时取这两个域之交，始终只用一份 $z$。

**定理 27.2（必要充分的有限端点表与全部共同原参数）。**
选择与所供应承诺对应的 $\mathcal H$。
将 (27.1)–(27.2) 的各行展开成关于 $z_0,\ldots,z_N,p$ 的线性不等式，
依次消去 $z_0,\ldots,z_N$，所需规则具体如下。
在一次消元中，当前变量为 $w$，其余变量为 $\xi$；
将每行写成 $a w+f(\xi)\le c$。
$a=0$ 的行保留；$a<0$ 给下函数 $\ell(\xi)=(c-f(\xi))/a$，
$a>0$ 给上函数 $h(\xi)=(c-f(\xi))/a$。
以每一对 $\ell\le h$ 替换所有含 $w$ 的行。
若只有下函数或只有上函数，不生成配对行。
所得最终有限表写作

$$
c_\nu p\le d_\nu.
\tag{27.3}
$$

若有 $c_\nu=0,d_\nu<0$，置 $D_{\mathcal H}=\varnothing$。
否则令

$$
\pi_- =\max\left(\{0\}\cup\{d_\nu/c_\nu:c_\nu<0\}\right),\qquad
\pi_+ =\min\left(\{+\infty\}\cup\{d_\nu/c_\nu:c_\nu>0\}\right).
\tag{27.4}
$$

则全部共同兼容的原指数为

$$
\boxed{P_+=(0,\infty)\cap[\pi_-,\pi_+],\qquad
P=P_+\ \cup\
\begin{cases}
\{0\},&\alpha_k\le e_kL\le\beta_k\quad(0\le k\le N),\\
\varnothing,&\text{其余情形},
\end{cases}}
\tag{27.5}
$$

有矛盾行时取 $P_+=\varnothing$。
正支非空当且仅当没有矛盾行、$\pi_-\le\pi_+$ 且 $\pi_+>0$。
$\pi_-=\pi_+>0$ 为正单点；$\pi_+\le0$ 或上下界反序给空正支。
每个严格正下端点和每个有限正上端点均取得；
$\pi_-=0$ 时正支不取得零，是否有原零指数仅由 (27.5) 的支持签名检验决定。
无穷上端点只表示任意大的有限候选，不表示无限参数。

每个合格 $p>0$ 的全部原参数，可且仅可按以下方式取得：
反向恢复被消去的变量，在每一步取
$\max\ell\le w\le\min h$ 中的任意有限值，恢复一个共同 $z$，
再用 (25.4)。只有一侧约束时取满足该侧的任意有限值，两侧都无约束则任取实数。
遍历所有这些选择及 (25.4) 的自由相位与尺度，恰得全部见证。
零指数存在时，任意有限正来源比及任意满足已供应漂移承诺的路径均合格，
相位与尺度仍自由。

证明。固定其余变量 $\xi$，有限行对 $w$ 的可行集就是所有下半直线与上半直线的交。
两侧均有约束时，最大下值不超过最小上值，当且仅当每一个下值不超过每一个上值；
这正是配对规则，且闭区间中可取有限 $w$。
仅有一侧时有限最大值或最小值总能被某个有限 $w$ 满足；
无约束时亦然。零系数行须原样成立。
因此每一步保留投影的两向等价，并保留反向选择的全部纤维。
归纳到全部 $z$ 消去后，(27.3) 恰是 $\mathcal H$ 在实 $p$ 轴上的投影。
按 $c_\nu$ 符号求解即得 (27.4) 及全部空集、单点和端点判据。

对任一合格有限正 $p$，逆序选择给一个有限共同 $z\in\mathcal B$。
定理 25.2 给唯一来源比与模长路径；(26.6) 保证该路径满足所供应预算。
logit 严格单调，因此同一参数组的每个概率落入对应 $I_k$。
反过来，任一原正指数见证给出其全部真 logits，满足 (27.2)，
并在逐次消元中被保留，所以没有遗漏。
有限正端点本身满足所有最终非严格行，反向选择与指数还原说明端点也有共同见证。
$p=0$ 的原概率只能是 (25.5)，恰给 (27.5)；
常路径满足所有非负预算，证明零支的充分性。
这与将形式线性域中的 $p=0$ 当作原零指数无关。

此处消费的是定理 23.2 已使用的有限半空间投影机制，
[Goemans，*Linear Programming and Polyhedral Combinatorics*，§3、定义 3.4 后的 Fourier–Motzkin 消元](https://math.mit.edu/~goemans/18433S15/polyhedral.pdf)
给出相同的上下函数配对与反向存在性。
这里将它用于共享路径的具体 (27.2)，不把一般消元另立为新结果。∎

**推论 27.3（区间逆像的无界阈值与小长度边界）。**
$\mathcal B$ 非空且有限时，两种单独承诺有下列精确阈值。

(a) 对 $\mathsf E_D$，$D<L$ 时非空正支总有有限上端点；
$D=L$ 时，正支非空当且仅当

$$
\exists z\in\mathcal B\quad R_i(z)\ge0\quad(1\le i\le m),
\tag{27.6}
$$

一旦非空便无界；$D>L$ 时总有全部充分大的有限正指数。

(b) 对 $\mathsf T_V$，$V<mL$ 时非空正支总有有限上端点；
$V=mL$ 时，正支非空当且仅当

$$
\max_{z\in\mathcal B}\sum_iR_i(z)\ge0,
\tag{27.7}
$$

一旦非空便无界；$V>mL$ 时总有全部充分大的有限正指数。

(c) $N=0$ 或 $N=1$ 时相邻变化索引为空，两个承诺均无额外约束。
任意非空内区间盒都兼容每个 $p>0$，零指数仍只按支持签名判断。
$N=0$ 时没有控制参数，$N=1$ 时有一个任意有限非零控制；
不在这些情形使用含 $m$ 的除法或长度阈值。

证明。$D<L$ 时，对每个见证都有
$p\le R_i(z)/(L-D)$。例如固定 $i=1$，
$R_1$ 在有限闭盒上有有限最大值，给统一有限上界；
若最大值非正就无正支。
$D=L$ 时，定理 26.1 对每个 $z$ 的存在条件正是全部 $R_i(z)\ge0$。
选一个满足 (27.6) 的共同 $z$，固定它并令
$p\ge\max_iR_i(z)/(2L)$，就得到任意大的见证。
$D>L$ 时对盒中任意固定 $z$ 应用 (26.5) 即可。

$V<mL$ 时，定理 26.2 给
$p\le\max_{z\in\mathcal B}\sum_iR_i(z)/(mL-V)$；
最大值存在且有限。临界时定理 26.2 对每个固定 $z$ 的充要条件是和非负；
闭盒上的线性函数取得最大值，故 (27.7) 等价于存在这样的同一个 $z$。
选定该向量便给无界正支。超临界时固定任一 $z$ 再应用定理 26.2。
最后 $N\le1$ 时 (25.4) 对任意正指数、任意盒中 logits 均可反解，
没有相邻变化需要检验；零支仍由非零端口的支持数给出。∎

**命题 27.4（重叠局部见证不保证同一全路径）。**
取 $N=3,p=2,D=0$，或将 $D=0$ 换为 $V=0$，并给

$$
J_0=J_3=\{0\},\qquad J_1=J_2=[1,2].
\tag{27.8}
$$

前缀三元组 $\{0,1,2\}$ 与 $\{1,2,3\}$ 各自都有合法的正指数二见证，
但不存在同时满足这四个区间的该指数与路径。
事实上，这四个区间在零漂移下没有任何原指数见证。

证明。第一个三元组可取 logits $(0,1,2)$，
在 (21.3) 中取 $p=2,u=0,v=1$；第二个可取其索引 $1,2,3$ 上的
$(2,1,0)$，取 $p=2,u=3,v=-1$。
二者都是有限非零来源与常模长控制，由 (25.4) 可直接还原。
但一个共同 $p=2$ 的零漂移见证必须有 $z_k=u+kv$，
两端 $z_0=z_3=0$ 迫使 $u=v=0$，违反中间两个区间。
对任意 $p>0$，零漂移的完整式为
$z_k=u+kv+e_k(L-pL/2)$。
$z_0=0$ 给 $u=0$；$z_3=0$ 给 $3v=-(L-pL/2)$；
于是 $z_1=-2v$、$z_2=2v$，不可能同时为正。
零指数又在 $k=1$ 要求 $L<1$，也不在 $J_1$。
所以整个候选集合为空。
局部实现使用不同的重叠 logits 和来源，不能把它们的残差界独立优化后合并。
(27.2) 中的一份共同 $z$ 正是排除这个错误拼接所需的量词。∎

**命题 27.5（形式零点与原零指数的区别）。**
在 (27.2) 中代入形式 $p=0$，两种约束都恰要求所有 $R_i(z)=0$，
即

$$
z_k=e_kL+c+kv\quad(0\le k\le N)
\tag{27.9}
$$

对某些实 $c,v$ 成立。
原零指数却还须 $c=v=0$；因此消元域含零不等于有原零指数。
例如固定 $c\ne0$，给精确报告 $z_k=e_kL+c$：
在 $D<L$ 或分别在 $V<mL$ 下，形式投影含零而全部原指数集合为空；
在 $D\ge L$ 或分别在 $V\ge mL$ 下，原指数集合恰为 $(0,\infty)$，零下确界不取得。

证明。形式 $p=0$ 时逐项上下界强迫 $R_i=0$；
总变差的全部符号行也等价于 $\sum_i|R_i|\le0$。
$R_i=0$ 等价于 $\Delta^2(z_i-e_iL)=0$；
一阶差分因此为常数，得到 (27.9)。
原零指数签名由 (25.5) 唯一给定，$k=0,1$ 即迫使 $c=v=0$。
示例的 $R=0$，正支按定理 26.1–26.2 的阈值判断；
$c\ne0$ 排除原零指数。
阈值以上的每个 $p>0$ 可取 $r=e^{c/p}$ 及 (26.11) 的模长路径，
所有相位与共同非零尺度任取，直接实现全部报告。
$p\downarrow0$ 时允许的来源比可趋零或无穷；
每个有限正指数的来源仍有限非零，不能借这种极限填入原零支。∎


## 28. 同报告歧义的锋利模量与长度量词

**定理 28.1（精确同报告的最佳相对歧义界）。**
设两个正指数候选 $p,p'>0$ 都满足假设 25.1，
在全部 $k=0,\ldots,N$ 上给出相同精确概率；
每个候选各用自己的一条共同路径，且都服从相同的已供应预算。
记 $S=p+p'$、$\Delta=|p'-p|$。则

$$
\mathsf E_D:\quad L\Delta\le DS,
\qquad
\mathsf T_V:\quad mL\Delta\le VS.
\tag{28.1}
$$

这些界对每一对正指数都是充足的存在判据：
相应不等式成立，当且仅当存在两个合法候选给出同一整族报告。
充足性甚至可要求两个候选使用完全相同的平衡来源 $a=b=1$、实正控制，
以及每两个相邻控制精确复合为 $I_3$。
这里的充足性是对某个共同报告族的存在结论，
不表示任意指定报告只要满足该数值界便都有这两个候选；指定报告仍用 §§26–27。

若 $D<L$ 或分别 $V<mL$，设
$\epsilon=D/L$ 或分别 $\epsilon=V/(mL)$，则

$$
\frac{\Delta}{S}\le\epsilon<1,
\qquad
\frac{1-\epsilon}{1+\epsilon}
\le\frac{p'}p\le
\frac{1+\epsilon}{1-\epsilon}.
\tag{28.2}
$$

在上述亚临界域，每个有限边界均取得。
在全部有限非负预算域内，同报告正指数候选对的 $\Delta/S$ 的最佳上确界分别为
$\min\{D/L,1\}$ 与 $\min\{V/(mL),1\}$。
对应预算严格低于阈值时，上确界取得，包括零预算时的零歧义。
当 $D\ge L$ 或分别 $V\ge mL$ 时，任意一对有限正指数均可同报告，
最佳相对上确界为一，但有限正指数恒有 $\Delta/S<1$，故上确界不取得；
此时也没有统一的有限比值界。零指数混淆的精确阈值仍是推论 26.3。

证明。共同报告给共同 $R_i$。对两个候选用 (26.6) 相减，得到

$$
(p'-p)L=s_i(p'\delta'_i-p\delta_i).
\tag{28.3}
$$

逐项取绝对值得 $L\Delta\le D(p+p')$；
先取绝对值再对全部 $m$ 项求和，则得 $mL\Delta\le V(p+p')$。
故两种必要界均成立。

为给出完整反向见证，可交换两个候选，设 $p'\ge p$，置

$$
\gamma=\frac{L(p'-p)}{p+p'}\in[0,L),\qquad
x_j^{(p)}=-\frac\gamma2(-1)^{j+1},\qquad
x_j^{(p')}=\frac\gamma2(-1)^{j+1},
\qquad
\lambda_j^{(q)}=2^{-1/2}e^{x_j^{(q)}}\quad(q=p,p').
\tag{28.4}
$$

两个候选都用 $a=b=1$，故 $u=u'=0$。
其每个相邻变化的绝对值恰为 $\gamma$，总变差恰为 $m\gamma$，
所以 (28.1) 的对应前件正好保证所供应预算。
每个相邻 $x$ 之和为零，故 $2\lambda_{j+1}^{(q)}\lambda_j^{(q)}=1$，
两步复合精确为 $I_3$。
由 (25.7)，两个候选都给

$$
z_{2h}=0,\qquad
z_{2h+1}=L-\frac{pp'}{p+p'}L.
\tag{28.5}
$$

例如在较小指数候选上，奇数前缀为
$L-p(L+\gamma)/2$，代入 $\gamma$ 就得 (28.5)；
较大指数候选为 $L-p'(L-\gamma)/2$，值相同。
同一个平衡来源、各自同一条嵌套路径因而同时实现所有前缀。
$\gamma=0$ 给两个相同指数；其余情形未重置路径或改变终点的标量。
整理 (28.1) 得 (28.2)，在 $\epsilon<1$ 时取
$p'=p(1+\epsilon)/(1-\epsilon)$ 就使对应预算和比值界均取等。
在临界或超临界域，任意有限正指数对都有
$\gamma<L\le D$ 或分别 $m\gamma<mL\le V$，故 (28.4) 仍合格。
取 $p=1,p'=t\ge1$，则相对差 $(t-1)/(t+1)$ 随 $t\to\infty$ 趋于一，
而任意有限正指数对的相对差严格小于一；同时比值 $p'/p=t$ 无界。
这证明全部预算域的最佳上确界、取等范围及存在断言。∎

**推论 28.2（固定逐步预算与固定总预算的长度区别）。**
长度增长指另行供应更长的连续前缀族，仍使用假设 25.1 的嵌套路径和同事件；
它不指树形细分，也不指重复抽样次数。
固定有限逐步预算 $D\ge0$ 时，同报告正指数候选对的最佳相对上确界
$\min\{D/L,1\}$ 不随 $N$ 改变。
$D<L$ 时该上确界取得；$D\ge L$ 时它为一且不取得。
对任意满足 $\Delta/S\le D/L$ 的两个固定正指数，
(28.4) 的一对交替路径可延长到每个有限长度，
始终满足同一个逐步预算并保持全部同报告。

固定有限总预算 $V\ge0$ 时，对每个给定有限 $N\ge2$，
精确同报告正指数候选对的最佳相对上确界为
$\min\{V/((N-1)L),1\}$。
$V<mL$ 时，相对边界 $V/(mL)$ 取得，包括 $V=0$ 的零歧义；
$V\ge mL$ 时，任意一对有限正指数均可同报告，上确界为一且不取得，
也没有统一的有限比值界。
固定 $V$ 并令 $N$ 增大时，该最佳相对上确界趋零。
固定真指数 $p>0$ 且 $mL>V$ 时，任一同报告正指数满足

$$
|p'-p|\le\frac{2pV}{mL-V}.
\tag{28.6}
$$

但不限制指数尺度时，固定正总预算 $V>0$ 并不给趋零的统一绝对歧义界；
$V=0$ 时精确同报告的正指数歧义为零。
若另有 $p+p'\le S_*$，则有绝对界 $V S_*/(mL)$。
这些不同量词不能互换。

证明。逐步预算部分使用 (28.4)，其 $\gamma$ 与长度无关，
最佳上确界及取得范围由定理 28.1 的分域结论给出。
总预算部分的上界由 (28.1) 及 $\Delta/S<1$ 给出。
在 $V<mL$ 时，令 $\gamma=V/m\in[0,L)$，
再按 (28.2) 选指数对，就取得相对边界。
在 $V\ge mL$ 时，在 (28.4) 中取 $p=1,p'=t\ge1$，
两条路径各花总变差 $mL(t-1)/(t+1)<mL\le V$，
而相对歧义 $(t-1)/(t+1)$ 随 $t\to\infty$ 趋于一且在有限 $t$ 时小于一。
这证明临界及超临界域的最佳上确界为一而不取得。
上述亚临界域的取等候选可随有限长度变化，
不能声称一对固定不同指数在所有长度上都服从同一个有限总预算。
在 $mL>V$ 下，(28.2) 的上比值界给
$p'-p\le2pV/(mL-V)$，下比值界给
$p-p'\le2pV/(mL+V)$，取较大者得 (28.6)。
对 $V>0$，在每个充分大 $m$ 取
$p=m^2$、$p'=m^2(mL+V)/(mL-V)$，则
$\Delta=2m^2V/(mL-V)$ 不趋零，而 (28.4) 仍是合法的有限长度见证。
$V=0$ 时精确报告的两个正指数当然相同。
有尺度上界时直接将 $S\le S_*$ 代入 (28.1)。

若另行假设同一对无限路径的所有有限限制均有统一总预算 $V$，
且其每个前缀都同报告，则 (28.1) 对任意 $m$ 成立，迫使 $\Delta=0$。
这仅是该额外全称数学前件的推论；
任何给定有限供应或可延长的数学记号都不自动供应全部无限报告。∎

## 29. 有限 logit 宽度的完整可达歧义与不消失下限

**定理 29.1（同一内区间盒的统一界与最佳存在模量）。**
给定有限 $w\ge0$，所有报告的 logit 区间满宽至多为 $w$，
即 $\beta_k-\alpha_k\le w$；$w$ 是全宽而非半宽。
两个正指数候选 $p,p'>0$ 均满足同一个区间盒及同一类预算时，必有

$$
\boxed{\mathsf E_D:\quad L\Delta\le D S+4w,\qquad
\mathsf T_V:\quad mL\Delta\le V S+4mw,}
\quad S=p+p',\quad\Delta=|p'-p|.
\tag{29.1}
$$

而且，对任意给定 $p,p',w$，对应不等式是存在这种共同区间盒及合法候选对的充要条件。
可以同时要求两个候选的控制实正、每两个相邻控制复合为 $I_3$。
有限宽度下来源比允许各候选不同，均在候选内部固定；
$w=0$ 时可取定理 28.1 的同一平衡来源。
与定理 28.1 一样，这个最佳存在模量不替代指定区间盒的共同可行性检验。

若各宽度不同，记 $w_k=\beta_k-\alpha_k$，还有必要界

$$
L\Delta\le DS+w_{i-1}+2w_i+w_{i+1}\quad(1\le i\le m),
\tag{29.2}
$$

$$
mL\Delta\le VS+\sum_{i=1}^m(w_{i-1}+2w_i+w_{i+1}).
\tag{29.3}
$$

不将这些局部必要界当作一般不等宽盒的充分条件。

证明。令两个候选的真 logit 向量为 $z,z'$，$h=z'-z$。
同盒给 $|h_k|\le w_k$，所以

$$
|\Delta^2h_i|\le w_{i-1}+2w_i+w_{i+1}.
\tag{29.4}
$$

由 $R_i(z')-R_i(z)=-s_i\Delta^2h_i$ 及 (26.6)，有

$$
(p'-p)L=p's_i\delta'_i-ps_i\delta_i-s_i\Delta^2h_i.
\tag{29.5}
$$

逐项三角不等式给 (29.2)；对全部 $i$ 求和并各用一个总预算给 (29.3)。
所有 $w_k\le w$ 时即得 (29.1)，证明必要性。

反向设 $p'\ge p$，令 $B=D$ 或分别 $B=V/m$，并置

$$
\gamma=\min\left\{B,\frac{L(p'-p)}{p+p'}\right\},\qquad
A=\frac{L(p'-p)-(p+p')\gamma}{4}\ge0.
\tag{29.6}
$$

对应 (29.1) 恰保证 $A\le w$。
使用交替路径

$$
x_j=-\tfrac\gamma2(-1)^{j+1},\qquad
x'_j=\tfrac\gamma2(-1)^{j+1},\qquad
u=-A/2,\quad u'=A/2,
\tag{29.7}
$$

并以 (25.4) 取来源比 $r=e^{u/p}$、$r'=e^{u'/p'}$、共同尺度 $c=1$ 和全部相位零。
两条路径的相邻变化绝对值均为 $\gamma$，总变差为 $m\gamma$，
故相应预算成立；每个相邻 $x$ 之和为零，故两步复合为 $I_3$。
由 (25.7)，偶数前缀之差为 $u'-u=A$；奇数前缀之差为

$$
A-\frac{L(p'-p)}2+\frac{(p+p')\gamma}{2}=-A.
\tag{29.8}
$$

故对每个前缀取以 $(z_k+z'_k)/2$ 为中心、满宽 $w$ 的闭 logit 区间，
两个真值都在其中。有限端点经 logistic 变换给严格内概率区间。
所有前缀使用同一来源参数及各自同一条路径，因而这是共同取得，
不是独立调节每个二阶残差。
$p'=p$ 或 $w=0$ 仍由相同公式处理；$w=0$ 时 $A=0$，恢复平衡来源见证。
这证明最佳存在模量的完整充分性。∎

**推论 29.2（零预算下锋利且不随长度消失的宽度下限）。**
即使 $D=0$ 或 $V=0$，任意有限 $N\ge2$ 及任意 $w>0$，
都存在满宽为 $w$ 的共同区间盒，使两个正指数相差恰为

$$
\boxed{4w/L.}
\tag{29.9}
$$

不能单凭更长连续前缀把任意确定性同盒候选的统一绝对歧义压到此值以下。
对固定总预算及相同满宽 $w$，(29.1) 给

$$
\Delta\le\frac{V}{mL}S+\frac{4w}{L};
\tag{29.10}
$$

相对预算项随长度缩小，确定性区间项保持不变。
若另给固定真指数 $p$ 且 $mL>V$，则

$$
|p'-p|\le\frac{2Vp+4mw}{mL-V}.
\tag{29.11}
$$

在 $mL>V$ 下，(29.11) 的界亦可由合法候选和某个共同满宽盒取得；
它随长度的极限为 $4w/L$，是当前确定性宽度模型的最坏情形界，
不表示每个实际盒都留下这么大的歧义。

证明。令 $p'=p+4w/L$，在定理 29.1 取 $B=0$，
得到 $\gamma=0,A=w$、$u=-w/2,u'=w/2$。
两候选的全部控制均为 $1/\sqrt2$，来源比分别为
$e^{-w/(2p)}$ 和 $e^{w/(2p')}$，均有限正。
偶数前缀真 logits 为 $-w/2,w/2$；奇数前缀为
$-w/2+L-pL/2$、$w/2+L-p'L/2$，两值相差 $-w$。
所以全部区间可同时以满宽 $w$ 容纳这两个候选，且所有两步都精确回返。
任意长度均可用这同一对常路径与来源，故下限确实不依赖长度。

(29.10) 只是 (29.1) 的总预算式除以 $mL$。
若 $p'\ge p$，将 $S=2p+(p'-p)$ 代入 (29.1)，整理得 (29.11)。
若 $p'\le p$，同理得较小上界 $(2Vp+4mw)/(mL+V)$。
取 $p'=p+(2Vp+4mw)/(mL-V)$，则 (29.1) 的总预算式取等，
其合法取得由 (29.6)–(29.8) 给出。
当 $w=0$ 时恢复精确报告界；当 $w>0$ 固定时，(29.11) 的极限为 (29.9)。
来源比若另行独立固定，须在定理 27.2 中加入对应的 $z_0=p\log r$，
上述允许来源比变化的最坏盒见证不被冒称为固定来源比下的锋利常数。
这里没有抽样独立性、平均误差或随次数缩窄区间的前件，故也没有统计精度结论。∎

**定理 29.3（有限宽度下正指数与支持签名的完整混淆模量）。**
取 $p>0$、满宽上限 $w\ge0$。
存在一个同时容纳零指数和正指数 $p$ 的全部连续前缀内区间盒、
且两个候选分别服从同一类预算，当且仅当

$$
\mathsf E_D:\quad p(L-D)\le4w,
\qquad\text{或分别}\qquad
\mathsf T_V:\quad p(mL-V)\le4mw.
\tag{29.12}
$$

可要求所有两步相邻复合精确为 $I_3$，并可令两个候选使用同一个来源。
因此在预算低于相应精确混淆阈值且 $w>0$ 时，可与零支同盒的最大正指数分别为
$4w/(L-D)$ 与 $4mw/(mL-V)$，这些正端点均取得。
$w=0$ 时恰恢复推论 26.3，不能由形式 $p=0$ 连续代入来证明。

证明。零指数的真 logit 为 $z_k^0=e_kL$，故全部 $R_i(z^0)=0$。
若另一个候选为 $z$，同盒给 $|z_k-z_k^0|\le w$，
于是 $|R_i(z)|\le4w$。
由 (26.6)，$pL\le|R_i(z)|+p|\delta_i|$；
逐项使用逐步预算或求和后使用一个总预算，即得必要式 (29.12)。

反向置 $B=D$ 或分别 $B=V/m$，令

$$
\gamma=\min\{B,L\},\qquad
A=p(L-\gamma)/4,\qquad
x_j=\tfrac\gamma2(-1)^{j+1},\qquad u=A.
\tag{29.13}
$$

(29.12) 保证 $0\le A\le w$。
正指数取 $r=e^{A/p}$、$c=1$、来源相对相位零、
$\lambda_j=2^{-1/2}e^{x_j}$。
其相邻变化绝对值为 $\gamma$、总变差 $m\gamma$，两步相邻复合为 $I_3$。
它相对零指数签名的 logit 差在偶数前缀为 $A$，奇数前缀为
$A-p(L-\gamma)/2=-A$。
对每个前缀取以这两个值为端点的区间，再按需扩大到满宽 $w$，便有共同内区间盒。
零指数可用同一 $r$、同一来源尺度与相对相位，但取常控制 $1/\sqrt2$；
其漂移为零、两步回返精确，全部报告恰为支持签名。
因而给出了原零指数支的独立见证，没有借用除以 $p$ 的公式处理零支。
在预算低于阈值且 $w>0$ 时，取 (29.12) 等号即取得所述正端点。
$w=0$ 时它要求 $D\ge L$ 或分别 $V\ge mL$，与精确结论一致。∎

## 30. 共享路径逆问题的来源与条件范围

**定义 30.1（消费的先例与结论归属）。**
(25.1)–(29.13) 是本卷三端口候选族上共享变动模长路径的条件纸面综合，
按 `repo-derived` 使用，不据此主张全球优先权。
它把固定标量的 §§21–24 扩展为每次使用各有标量、但所有终点共用一条路径的逆问题；
完整原参数纤维、两种独立漂移承诺、共同内区间取得、
支持签名混淆阈值及锋利的长度与宽度模量是这里的具体结论。
固定标量的既有结论保留原来的固定条件；
允许标量变化后的反例不反驳定理 13.3 对同一个控制重复两次的标定。
(28.4) 的精确两步回返也不认证每一步酉性：
若 $x_j\ne0$，则 $G_j^\dagger G_j=\operatorname{diag}(e^{2x_j},e^{2x_j},1)\ne I_3$。

权重的有界乘性分类、log 赔率及相干奇偶结构分别消费本卷定义 13.1、
定理 13.3 的分类证明、§3 及定理 21.2；
[V17 §2、命题 13.1](AURIC_SUM_PRODUCT_LOGARITHMS_AND_QUANTUM_PYTHAGOREAN_GEOMETRY_V17.md)
供应实 log 坐标及相干幂与记录后递归的区分；
[V47 §§4、10](AURIC_EXISTENTIAL_QUANTIFIERS_SQUARE_WEIGHTS_AND_PROMPT_ERROR_RELATIONS_V47.md)
供应幂族与概率不定相位的既有边界。
[V52 §§2、5](AURIC_PURE_STATE_QUOTIENT_GEOMETRY_QUADRATIC_RELATION_GENERATORS_AND_LOSSLESS_RECURSION_V52.md)
的完整外积、Hopf 商及共同相位不变量保留其全部非对角关系；
本节的事件概率并未供应那些关系。
[V55 §§9–10](AURIC_EXTERIOR_CLOSURE_OF_BINARY_RELATIONS_THREE_AXIS_ERRORS_AND_CONDITIONAL_QUANTUM_ORIGIN_V55.md)
的滤波、保质量和条件动力学仍各守自己的前件，
不由某个指定来源的两步回返推广到全部输入或全部过程。

二阶差分与斜率变差属于标准有限差分结构：
[Kim–Koh–Boyd–Gorinevsky，*l1 Trend Filtering*，SIAM Review 51(2)，339–360，DOI 10.1137/070690274](https://web.stanford.edu/~boyd/papers/l1_trend_filter.html)
使用二阶差分的绝对值惩罚来控制斜率变化。
这里消费的是该已知结构，(26.6) 则明确给出它与本模型交替支撑项及指数的对应；
没有采用其统计估计假设、惩罚参数选择或趋势估计误差结论。
定理 27.2 的有限消元使用其所附 Goemans 来源及本卷定理 23.2 的既有机制。
它们作为 `literature-attested` 中间工具，不被另立为新增的通用差分、总变差或多面体定理。

**假设 30.2（解释与取得的独立前件）。**
上述结论始终限于精确 $w_p$、精确控制形状、非零活动及旁观来源、
嵌套路径、已供应真概率或确定性包含区间，以及明确供应的 log 模长漂移承诺。
漂移承诺不是由端口概率推得的实际标定证书，也不限制自由控制相位。
两步回返见证是数学构造，不把任何未供应的相干回返当作观测事实。
报告为概率零或一的单点时，非零有限参数域内无见证；
这里不以无穷 logit 或零控制填补该边界。
一般控制误差、近似乘性稳定性、概率区间的有限资源取得、置信度、
重复性、源复制及内部控制权限均须另行建立。

[量子续卷 IV §§206–208](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md)
的平方检测权重、既定率及历史桥，和
[RRO §§62–67](RECURSIVE_RELATIONAL_OBSERVATION_FIBONACCI_NATIVE_TERMINAL_CERTIFICATION.md)
的自然过去域、档案及可测恢复，各是其原结论的输入；
它们不供应本逆问题的同源前缀概率、模长漂移预算或相位比较。
这里没有从归一读数有界推出原始权重有界，
也没有推出复数域唯一性、张量结构、物理时间、全部输入酉性、一般过程认证或无条件量子起源。
可辨识性只比较声明候选族的纤维，不自动给出取得、可操作性或认证的资源界。

## 追加锚（本行以下为增补区）
## 31. 原生两调用旧终端事件的有限平方标定

本节把第 13 节的全局权重类接到原来源的一个实际有限字。它不使用
Hadamard 块、非原生连续旋钮或任意输入；所用两次调用都是旧菜单中的
正向整数调用。第 13 节已经证明的全局分类在这里直接复用，不重新证明。

**定义 31.1（原 ready、三条旧配置和全载体事件）。** 取续卷 III
(138.1)、(151.9) 的同一个 \(89\) 配置载体、唯一 ready \(e_0=R_0v\)、
固定边界以及

$$
x=\varphi^{-1},\qquad c=x\sqrt{x},\qquad
\zeta=e^{3\pi i/5},\qquad x+x^2=1.
\tag{31.1}
$$

ready 的内部位为
\((b_1,\ldots,b_9)=(0,0,1,0,0,0,1,0,0)\)。
令 \(e_{\rm r}=e_0\)，令 \(e_-\) 为只把 \(b_7\) 从 \(1\) 改为 \(0\) 的合法基配置，
令 \(e_+\) 再把 \(b_8\) 从 \(0\) 改为 \(1\)；三者的旧十位标签分别是

$$
w_{\rm r}=1000100010,\qquad
w_-=1000100000,\qquad
w_+=1000100001.
\tag{31.2}
$$

这些是原 \(N_w\) 的标签，不是新增读口。按续卷 IV (205.1)、(211.1) 的
同一 \(\Xi\)，写

$$
\widehat e_s=\Xi(e_s\otimes|0\rangle),
\qquad z_*=01000,
\qquad s\in\{{\rm r},-,+\}.
\tag{31.3}
$$

完整载体仍是全部 \(610\) 个配置，包含原 \(178\) 维接口和 \(432\) 维补空间；
这里只列出本有限历史实际支撑的三列。定义旧终端配置事件

$$
 C_{\rm r}=\{Q:(b_{-1},\ldots,b_8)(Q)=w_{\rm r}\}.
\tag{31.4}
$$

在完整载体上它是同一个字面旧标签的全支撑集合，报告仍有全部
\(\Omega_{10}=\{0,1\}^{10}\) 的 \(1024\) 个标签。因为 \(C_{\rm r}\) 固定
\(b_7=1\)，地址 \(8\) 的合法翻转边在 \(C_{\rm r}\) 内不存在；又因为地址 \(8\)
不改变 \(b_7\)，任何边也不能从补集进入 \(C_{\rm r}\)。这是配置支撑和局部性
给出的事件不变性；它不把相干矩阵局部性偷换成实际配置局部性。

**假设 31.2（有限原生历史和忠实事件响应）。** 保留第 13 节定义 13.1
的一个全局函数 \(w:\mathbb C\to[0,\infty)\)：

$$
w(0)=0,\qquad w(1)=1,\qquad w(zz')=w(z)w(z'),\qquad
\sup_{|z|\le1}w(z)<\infty,
\tag{31.5}
$$

并对非零有限向量使用同一未归一权重的归一读数 \(\Pi_w\)，零点仍按第 13
节的 \(p=0\) 约定单独处理。取原正向调用字

$$
P=(7),\qquad G=(8).
\tag{31.6}
$$

它们都只调用一次 \(K_j\)，没有分数调用、逆字、隐藏准备、额外端口或后选择。
在同一个唯一 ready 上，准备历史是 \(\mathsf T(P)\)，控制历史是
\(\mathsf T(PG)\)；二者都在原前缀域 \(\{0,\ldots,10\}^{<\infty}\) 内。
实际终端报告是原 \(W=(b_{-1},\ldots,b_8)\)，并保留真实调用顺序、跳时、
细档案、失败、拒绝、停止和告警坐标。若使用 \(\mathsf R(P,\epsilon)\) 或
\(\mathsf R(PG,\epsilon)\)，则还保留 IV 的十五次 \(d\)、实际 \(J=b_{13}\)
报告和其完整微历史；本节的校准事件仍只读原 \(W\)。

在两个端点历史上，假设实际终端响应忠实地由 \(\Pi_w\) 给出，并且原事件
确实守恒：

$$
\Pr(C_{\rm r}\mid\mathsf T(P))
 =\Pi_w(C_{\rm r}\mid K_7e_0),\qquad
\Pr(C_{\rm r}\mid\mathsf T(PG))
 =\Pi_w(C_{\rm r}\mid K_8K_7e_0),
\tag{31.7}
$$

$$
\Pr(C_{\rm r}\mid\mathsf T(P))
 =\Pr(C_{\rm r}\mid\mathsf T(PG)).
\tag{31.8}
$$

式 (31.8) 是实际报告事件的来源合同，不能由 (31.4) 的矩阵支撑不变性
单独推出。它也不是成功后选择：两条完整有限历史的所有失败坐标均保留，
理想零失败若采用则是独立的显式前件。续卷 III (138.2)、(145.2)、
(152.8)、(169.2) 和续卷 IV (211.2)、(212.2) 的同一 causal-prefix、
接缝和档案条件全部保留；没有为这两个字另抽源、另置时钟或重写旧核。

**定理 31.3（原生旧终端事件选择平方响应）。** 在定义 31.1 和假设
31.2 的全部前件下，

$$
\boxed{w(z)=|z|^2\quad(z\in\mathbb C),\qquad
\Pi_w(C\mid v)=\frac{\sum_{j\in C}|v_j|^2}{\sum_j|v_j|^2}}
\tag{31.9}
$$

对所有非零有限波幅成立，包括 \(p=0\) 的排除；零波幅仍取 \(w(0)=0\)。

**证明。** 先把三个配置上的原生矩阵写出。按地址 \(7\) 的中心位
\(b_7=0,1\) 排列 \((e_-,e_{\rm r})\)，按 (138.2a) 有

$$
K_7=\zeta\,[I+(\zeta-1)Q],
\qquad Q=\begin{pmatrix}x&c\\c&x^2\end{pmatrix}.
\tag{31.10}
$$

所以存在

$$
s=\zeta\bigl(1+(\zeta-1)x^2\bigr),\qquad
\mu=\zeta(\zeta-1)c
\tag{31.11}
$$

使得

$$
K_7e_0=s\,e_{\rm r}+\mu e_- .
\tag{31.12}
$$

在 \(e_-\) 所在的地址 \(8\) 二点块中，\(b_7=b_9=0\)；按同一局部矩阵，

$$
u=\zeta\bigl(1+(\zeta-1)x\bigr),\qquad
K_8e_-=u\,e_-+\mu e_+ .
\tag{31.13}
$$

而 \(b_7=1\) 使 \(e_{\rm r}\) 在地址 \(8\) 为单点块，故
\(K_8e_{\rm r}=\zeta e_{\rm r}\)。由 (31.12)--(31.13)，端点波幅精确为

$$
\psi_P=s\,e_{\rm r}+\mu e_-,\qquad
\psi_{PG}=\zeta s\,e_{\rm r}+\mu u\,e_-+\mu^2e_+ .
\tag{31.14}
$$

这两个等式在全 \(89\) 维空间成立，其他 \(86\) 个配置的幅度为零；在完整
\(610\) 维空间则由 (31.3) 逐列提升，其他 \(607\) 个配置仍在载体中。

由 \(\zeta+\bar\zeta=-x\)、\(|\zeta-1|^2=2+x=x^{-2}\) 和 \(c^2=x^3\)，

$$
|\mu|^2=(2+x)x^3=x,\qquad |s|^2=1-|\mu|^2=x^2,\qquad
|u|^2=x^2.
\tag{31.15}
$$

因此 \(|\mu|=\sqrt{x}\)、\(|s|=|u|=x\)，且三者都非零。第 13 节定理
13.3 的分类部分已从 (31.5) 得到唯一 \(p\ge0\)，使
\(w(z)=|z|^p\) 对 \(z\ne0\)；相位权重为一，所以 (31.14) 和 (31.7)--(31.8)
给出

$$
\frac{x^p}{x^p+x^{p/2}}
=\frac{x^p}{x^p+x^{3p/2}+x^p},\qquad\text{即}\qquad
1=x^p+x^{p/2}.
\tag{31.16}
$$

令 \(r=x^{p/2}\in(0,1]\)。则 \(r^2+r=1\)。正方程在 \((0,1]\) 中只有
\(r=x\)，因为 \(x^2+x=1\) 且另一根为负；由于 \(0<x<1\)，
\(x^{p/2}=x\) 给 \(p=2\)。特别地，\(p=0\) 时左边为 \(1\) 而右边为 \(2\)，
所以零指数约定没有被隐去。代回已供应的全局分类即得 (31.9)。∎

**命题 31.4（有限实际历史关系和边界）。** 在定理 31.3 的同一来源前件
下，令 \(a\in\{(7),(7,8)\}\)。存在可测的完整历史双射

$$
\widehat{\mathsf H}_{a,\epsilon}
\longleftrightarrow
\mathsf H_{a,\epsilon}
\tag{31.17}
$$

其在本有限校准段逐时刻为

$$
\widehat Q_t=(q_t,z_*)\quad(0\le t\le |a|),
\tag{31.18}
$$

并保留每个旧配置、每个跳时、每个单位调用及接缝左右值。它同时保留
所有 \(1024\) 个 \(W\) 标签、无路径零标签、完整真实档案、失败／拒绝／停止／
告警坐标和（若采用 \(\mathsf R\)）读器的十五次实际调用及 \(J\)；它不增加
配置隐藏读口、跳时读口、准备或复位。

**证明。** 续卷 III (152.8)、(169.2) 的旧前缀历史取同一个 ready、旧
源驱动和旧档案核。续卷 IV (211.2) 对每个 \(j\le10\) 给出
\(\widehat K_j\Xi=\Xi(K_j\otimes I)\)，且在 \(z_*\) 上地址 \(10\) 只有对角
作用；故 \(j=7,8\) 的两次调用逐段把旧配置路径送到 (31.18)，不改变
\(z_*\)，也不在接缝重抽。IV 定理 212.2 证明中的“无读器程序”条款直接由
(211.3)、(212.5) 给出原完整 \(\mathsf T(a)\) 历史的 ready 嵌入，故得到
本节 \(\mathsf T\) 的关系。对 \(\mathsf R(a,f)\)，该定理的既有历史映射另行把
相同源／档案种子、调用次序、跳时、报告、垃圾和所有失败坐标逐项保留；
即使 \(f=\epsilon\)，十五次原读器调用和实际 \(J\) 仍全部保留。
映射与逆映射均只在既有合法生成支持上逐坐标作用，故可测且不把实际历史
投影成另一条比较波。∎

[首续卷](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION.md)
§§68--71 已在固定黄金门下研究归一终端响应。定理 68.2 从五站点全零源经
\(K_2,K_1\) 制备，用 Bob 的 \(I,K_3\) 两设置及 Alice 边缘无信号，在归一
幂律 \(p>0\) 族内选择 \(p=2\)。定理 71.1 则在共同连续径向逐坐标响应类内，
对十站点唯一初态、地址 \(0,\ldots,6\) 的全部有限制备字和 Bob 的 \(I,K_5\)
两设置，利用制备闭包与响应连续性得到平方响应的必要充分条件。这些既有
机制和前件各保其域，本节不主张一般指数选择或平方响应的全球新颖性。

本节的来源特定增量限于从原唯一 ready 出发的 \(P=(7),G=(8)\)、字面旧
事件 \(C_{\rm r}\) 的两调用端点守恒应用、(31.14)--(31.16) 的有限推导，
以及全部 \(89/610\) 配置载体和完整历史的对应；没有把上述 Bob 设置、
无信号或全字量词移作本节前件。第 13 节的权重分类、III 的 native-wave
矩阵和 IV 的全历史提升均为既有供应。它没有声称所列事件合同自动来自矩阵、全时配置率、
所有时间概率、创新律、仪器后继、CP、张量复合或完整量子起源。端点权重
也不决定速率、全历史核或未来报告；任何源改变都必须另给其完整微观历史。

Aaronson，[quant-ph/0401062v2] §2，直接讨论乘性振幅权重、\(p\)-范数保持
和 \(2\)-范数的特殊性；它没有本来源的 \(K_7,K_8\)、旧标签或全历史接口。
Galley--Masanes，[1801.06414v4] §5.2 把无信号作为复合系统和测量框架中的
额外约束；这里没有把它当作单一 \(89/610\) 终端事件的替代证明。
Dürr--Goldstein--Tumulka--Zanghì，[quant-ph/0407116v1] §§2.7、5.2
把平方分布等变和最小跳率作为给定 Hamiltonian／配置过程的动力学输入；
这里的 (31.8) 同样是明确来源合同，不是由文献或矩阵局部性自动得到。
## 32. 有限观测菜单的共同漂移阈值

**定义 32.1（菜单商与同一条完整路径）。**
保留假设 25.1 的权重、来源、事件、控制形状和无中间测量合同，
但只指定菜单 $K\subseteq\{0,\ldots,N\}$ 上的报告，允许 $K$ 为空及 $N=0,1$。
令 $m=\max\{N-1,0\}$，$L=\log2$，$h_k=e_kL/2$，并定义

$$
A_K\beta=(\beta_0+k\beta_1)_{k\in K},\qquad
(T_Kd)_k=\sum_{i=1}^m(k-i)_+d_i.
\tag{32.1}
$$

空和为零。取矩阵 $W_K$，其行为 $A_K$ 左零空间的任一基；置

$$
B_K=W_KT_K,\qquad b_K=W_Kh_K,\qquad
\mathcal G_K=\{g\in\mathbb R^m:B_Kg=b_K\}.
\tag{32.2}
$$

没有左零空间时取零行矩阵。以下结论不依赖这组基。
路径预算集是分别选择的

$$
\mathcal C_E(D)=\{d:\|d\|_\infty\le D\},\qquad
\mathcal C_T(V)=\{d:\|d\|_1\le V\},\qquad
\mathcal C_{ET}(D,V)=\mathcal C_E(D)\cap\mathcal C_T(V).
\tag{32.3}
$$

只加入实际供应的预算；均为有限非负数。
$m=0$ 时三个集合均为 $\mathbb R^0=\{0\}$。
$K$ 以外的前缀虽不报告，其控制仍属于同一条长度 $N$ 路径并计入预算。

**定理 32.2（任意菜单上两指数共同报告的完整存在分类）。**
来源比未另行固定，选定 (32.3) 中的一个预算集 $\mathcal C$。
对指定的两个有限正指数 $p,p'>0$，记

$$
\gamma=\frac{|p'-p|}{p+p'}\in[0,1).
\tag{32.4}
$$

存在两个合法的完整原参数候选，在 $K$ 上给出同一族精确报告，当且仅当

$$
\boxed{\exists d\in\mathcal C:\quad B_Kd=\gamma b_K.}
\tag{32.5}
$$

对任意指定 $p>0$，存在该正指数候选在 $K$ 上与零指数支持签名同报告，
当且仅当

$$
\boxed{\mathcal G_K\cap\mathcal C\ne\varnothing.}
\tag{32.6}
$$

这是“存在某一共同报告”的分类；指定报告的可行性还要检验定理 33.3 的同一全向量。
若另知来源比或字面来源，上述存在分类不自动保留，须在同一原参数见证中加入该限制。
两个零指数始终可同报告，且不以正指数除法处理。

证明。对正指数写 $u=p\log r$、$a=px_1$；$N=0$ 时省略 $a$。
将 $x_j=x_1+\sum_{i<j}\delta_i$ 代入 (25.7)，得到

$$
z_K=e_KL+A_K\beta+p(T_K\delta-h_K),\qquad\beta=(u,a).
\tag{32.7}
$$

反向任意有限 $\beta,\delta$ 都给同一条完整路径：$N\ge1$ 时取
$x_1=a/p$、$x_j=x_1+\sum_{i<j}\delta_i$，并取

$$
r=e^{u/p},\quad b=c,\quad a_{\rm src}=cr e^{i\phi},\quad
\lambda_j=2^{-1/2}e^{x_j}e^{i\eta_j},\quad c\in\mathbb C^\times.
\tag{32.8}
$$

所有相位自由，全部数值有限且所要求的参数非零；$N=0$ 时没有控制。
符号 $a_{\rm src}$ 指来源分量，区别于斜率坐标 $a$。

交换候选后可设 $p'\ge p$，令 $S=p+p'$、$\Delta=p'-p$。
共同报告使 (32.7) 相减，左乘 $W_K$ 得

$$
B_K(p'\delta'-p\delta)=\Delta b_K.
\tag{32.9}
$$

$\mathcal C$ 凸且中心对称，所以
$d=(p'\delta'-p\delta)/S\in\mathcal C$，证明必要性。
反向给定 (32.5)，有
$T_Kd-\gamma h_K=A_Kf$，因为 $\ker W_K=\operatorname{im}A_K$。
取 $\delta'=d$、$\delta=-d$，以及
$\beta=Sf/2$、$\beta'=-Sf/2$，则两个 (32.7) 之差为零。
(32.8) 实现全部前缀；两个预算同时存在时，这里也只用一份 $d$。
$p'=p$ 时可直接取两个相同的零漂移候选，(32.5) 同样成立。

与零指数同报告要求正支的 (32.7) 等于 $e_KL$。
除以这个正 $p$，得到 $T_K\delta-h_K\in\operatorname{im}A_K$，即 (32.6)。
反向取 $g\in\mathcal G_K\cap\mathcal C$、$T_Kg-h_K=A_Kf$，
令 $\delta=g$、$\beta=-pf$，再用 (32.8)。
零指数另取常路径 $x_j=0$ 和任意有限非零来源，直接由支持计数给 $e_kL$。
也可让零指数使用上述正支的同一来源；它不限制零支的来源比。
未使用 $p=0$ 的倒数，证明两支及其完整原参数存在性。∎

**定理 32.3（内禀菜单阈值、可取得的对偶与联合预算证书）。**
$\mathcal G_K$ 总非空，$B_K$ 满行秩。定义可取得的有限阈值

$$
D_K^*=\min_{g\in\mathcal G_K}\|g\|_\infty,\qquad
V_K^*=\min_{g\in\mathcal G_K}\|g\|_1.
\tag{32.10}
$$

它们有可取得的对偶表达式

$$
D_K^*=\max_{\|B_K^{\mathsf T}y\|_1\le1}b_K^{\mathsf T}y,
\qquad
V_K^*=\max_{\|B_K^{\mathsf T}y\|_\infty\le1}b_K^{\mathsf T}y.
\tag{32.11}
$$

仅供应逐边预算时，(32.5) 恰为 $\gamma D_K^*\le D$；
仅供应全路径总预算时，恰为 $\gamma V_K^*\le V$。
(32.6) 则分别为 $D_K^*\le D$、$V_K^*\le V$。
所有这些闭边界都取得，但有限正指数的 $\gamma$ 始终小于一。

两种预算同时供应时，定义

$$
H_{D,V}(c)=\min_{t\ge0}\left\{Vt+D\sum_{i=1}^m(|c_i|-t)_+\right\}.
\tag{32.12}
$$

则 (32.5) 的完整对偶判据为

$$
\boxed{\gamma b_K^{\mathsf T}y\le
H_{D,V}(B_K^{\mathsf T}y)\quad\text{对所有 }y.}
\tag{32.13}
$$

任何违反该式的 $y$ 都是不可行的证书；(32.6) 将 $\gamma$ 换为一。
若 $b_K\ne0$，还可把联合阈值写成可取得的数

$$
\begin{aligned}
\kappa_K(D,V)
&=\max\{\tau\ge0:\exists d\in\mathcal C_{ET}(D,V),\ B_Kd=\tau b_K\}\\
&=\min_{b_K^{\mathsf T}y=1}H_{D,V}(B_K^{\mathsf T}y).
\end{aligned}
\tag{32.14}
$$

此时两正指数可混淆当且仅当 $\gamma\le\kappa_K(D,V)$，
正指数与零支可混淆当且仅当 $1\le\kappa_K(D,V)$。
若 $b_K=0$，约定 $\kappa_K=+\infty$，所有这些存在判据均成立。
特别地，$D_K^*=V_K^*=0$ 当且仅当
$|K|\le2$ 或 $K$ 仅含一种奇偶；其余菜单的两个阈值均严格正。
这保留定理 22.1 的零漂移设计结论，新增的是非零预算的精确阈值与共同取得。

证明。$N\ge1$ 时全体前缀有恒等式

$$
h_k=\frac L2k+\sum_{i=1}^{N-1}(k-i)_+Ls_i.
\tag{32.15}
$$

两侧在 $k=0,1$ 相同，二阶差分也同为 $Ls_i$，故逐项相同。
$N=0$ 时 $h_0=0$。限制到 $K$ 即给 $\mathcal G_K$ 的一个元素。
全菜单上的 $[A\ T]$ 可由初值和全部二阶差分表示任意实向量，故满行秩；
限制行后仍满行秩。若 $y^{\mathsf T}B_K=0$，则
$y^{\mathsf T}W_K$ 同时消去 $A_K,T_K$，因而为零；$W_K$ 行独立给 $y=0$。
所以 $B_K$ 满行秩。非空闭仿射集上的任一范数在有界次水平集内取得最小值，
证明 (32.10) 的存在性，包括零维情形。

说明 (32.11) 所消费的标准范数对偶在这里的具体对应。
记 $B=B_K,b=b_K$，令 $\|\cdot\|$ 依次为无穷范数、一范数，
$U=\{g:\|g\|\le1\}$。任意 $\|B^{\mathsf T}y\|_*\le1$ 给
$b^{\mathsf T}y=g^{\mathsf T}B^{\mathsf T}y\le\|g\|$，这是弱对偶。
若 $b\ne0$，最小值 $a>0$，$b/a$ 是紧凸集 $BU$ 的边界点。
满行秩使 $BU$ 含原点的一个邻域。
在该边界点取非零支撑向量 $y$，得到
$b^{\mathsf T}y/a=\sup_{v\in BU}y^{\mathsf T}v
=\|B^{\mathsf T}y\|_*>0$；缩放 $y$ 就取得对偶值 $a$。
这里支撑向量的存在可直接如下验证：对趋近该边界点的外点取最近点，
最近点最优性给单位外法向量的支撑不等式；取单位球上的收敛子列，
极限仍为单位支撑向量。原点内邻域使其支撑值严格正。
若 $b=0$，$g=0,y=0$ 同时取得零值。无左零空间时同样如此。
因而无需假设额外的严格预算可行性。(32.5) 的单预算结论由缩放立即得到。

对联合预算集 $\mathcal C=\mathcal C_{ET}(D,V)$，任意 $d\in\mathcal C,t\ge0$ 有

$$
c^{\mathsf T}d\le\sum_i|c_i||d_i|
\le tV+D\sum_i(|c_i|-t)_+.
\tag{32.16}
$$

把 $|c_i|$ 降序排列，依次给最大的坐标放质量，
每坐标至多 $D$，总质量至多 $V$，符号取 $\operatorname{sgn}c_i$。
若 $V\ge mD$，全部放满并取 $t=0$；
若 $0<V<mD,D>0$，放满 $r=\lfloor V/D\rfloor$ 个坐标，
下一坐标放 $V-rD$，取 $t$ 为该下一坐标的绝对值。
这使 (32.16) 取等。$V=0$ 时取 $d=0,t=\max_i|c_i|$；
$D=0$ 时取 $d=0,t=0$；$m=0$ 时空和给零。
故 (32.12) 正是 $\sup_{d\in\mathcal C}c^{\mathsf T}d$，最小值也取得。

紧凸集 $B_K\mathcal C$ 的成员关系由所有支撑不等式刻画。
为验证反向，若 $v=\gamma b_K$ 在集外，取其最近点 $v_0$，令 $y=v-v_0$。
沿集内任意线段对距离平方在 $v_0$ 取右导数，给
$y^{\mathsf T}(w-v_0)\le0$；而 $y^{\mathsf T}(v-v_0)>0$。
于是 $y$ 违反 (32.13)。这证明充要性及分离证书。

$b_K\ne0$ 时，紧性使 (32.14) 的左侧最大值有限且取得。
若 $D,V>0$，$B_K\mathcal C$ 含原点内邻域；
在径向边界 $\kappa_K b_K$ 取上述支撑向量，其在 $b_K$ 上的值严格正，
归一为 $b_K^{\mathsf T}y=1$ 就取得右侧的最小值 $\kappa_K$。
弱对偶给反向不等式。若 $D=0$ 或 $V=0$，集为 $\{0\}$，
两侧均为零，任意 $b_K^{\mathsf T}y=1$ 都取得。
凸性和含零性又使可达的 $\tau$ 恰为 $[0,\kappa_K]$。

最后，两个最小范数为零当且仅当 $b_K=0$，即 $h_K$ 是 $K$ 上的仿射函数。
至多两个点或同一奇偶时显然成立；
至少三个点且有两种奇偶时，同奇偶的两点强迫仿射斜率为零，另一奇偶点给矛盾。
这也处理空菜单及 $N\le1$ 的全部退化边界。∎

**命题 32.4（连续菜单恢复与稀疏菜单的联合预算差别）。**
全菜单 $K=\{0,\ldots,N\},N\ge2$ 有

$$
\mathcal G_K=\{(Ls_i)_{i=1}^m\},\qquad D_K^*=L,\qquad V_K^*=mL.
\tag{32.17}
$$

故单预算恢复定理 28.1 及推论 26.3，双预算同时要求
$\gamma L\le D$、$\gamma mL\le V$，零签名则取 $\gamma=1$。

对偶数 $N\ge2$ 的稀疏菜单 $K=\{0,1,N\}$，则有

$$
\mathcal G_K=\left\{g:\sum_{i=1}^m(N-i)g_i=-NL/2\right\},\quad
D_K^*=\frac L{N-1},\quad V_K^*=\frac{NL}{2(N-1)}.
\tag{32.18}
$$

定义 $F_N(D,V)=0$ 若 $D=0$。$D>0$ 时，置
$W=\min\{V,mD\}$、$r=\lfloor W/D\rfloor$、$w=W-rD$，令

$$
F_N(D,V)=D\sum_{j=1}^r(N-j)+w(N-r-1).
\tag{32.19}
$$

$r=m$ 时 $w=0$，最后一项取零。
双预算下两正指数共同报告存在当且仅当
$\gamma NL/2\le F_N(D,V)$；正指数与零签名取 $\gamma=1$。
例如 $N=4,D=L/3,V=2L/3$ 同时达到两个单预算零签名阈值，
却有 $F_4=5L/3<2L$，所以不能与零签名同报告。
同样，对任意指定的两个不同正指数，以
$D=\gamma L/3,V=2\gamma L/3$ 同时达到两个单预算阈值，仍不能共同报告。

证明。全菜单上二阶差分唯一确定 $g_i=Ls_i$，给 (32.17)。
稀疏菜单中 $h_0=0,h_1=L/2,h_N=0$，
故 $h_K=A_K\beta+T_Kg$ 先定 $\beta_0=0,\beta_1=L/2$，再给 (32.18) 的单方程。
权重和为 $N(N-1)/2$，最大权重为 $N-1$，
所以三角不等式分别给所列最小无穷范数与最小一范数。
前者由全部 $g_i=-L/(N-1)$ 取得，后者由
$g_1=-NL/(2(N-1)),g_i=0\ (i>1)$ 取得；这些同一方程的归一化权重也给对偶证书。
双预算时，带权和绝对值的最大值，依 (32.16) 的质量分配，恰为 (32.19)。
符号对称及沿线段缩放使每个介于零与该最大值的负值均可取得。
(32.5)–(32.6) 因而给出完整判据。代入 $N=4$ 得最后两个断言。
这些是完整路径预算上的删行效应，不能用相邻已观测端点之间的独立逆拟合替代。∎

## 33. 历史条件抽样律与全参数的随时反演

**假设 33.1（另外声明的共同参数 Bernoulli 实验）。**
令 $\Theta$ 为假设 25.1 的完整有限原参数域，加入实际供应的路径预算和已知来源限制。
一次实验固定一个未知 $\theta=(p,a,b,\lambda_1,\ldots,\lambda_N)\in\Theta$，
$p\ge0$。记 $q_k(\theta)=Q_k\in(0,1)$，由定理 25.2 计算，零支用其支持签名。
观察历史是有限词 $H_t=((J_1,Y_1),\ldots,(J_t,Y_t))$，
其中 $J_t\in\{0,\ldots,N\}$、$Y_t\in\{0,1\}$。
在每个未停止历史后，已声明的核 $\pi_t(\cdot\mid H_{t-1})$
选择停止符号 $\partial$ 或一个前缀 $J_t$；核只依赖已读历史和已知设计，
不依赖未知 $\theta$。选择 $J_t=k$ 后要求

$$
\Pr_\theta(Y_t=1\mid H_{t-1},J_t=k)=q_k(\theta).
\tag{33.1}
$$

停止后记录吸收，所有计数不再改变。
这允许基于全部历史的随机前缀选择、停用某些前缀及可选停止；
没有假设实际取得的 $Y_t$ 无条件 iid。
有限词的联合概率由 $\pi_t$ 和 (33.1) 逐步相乘定义。
这一条件律是附加的抽样假设，不由确定性概率公式、预算或相干路径的存在推出。
每次 $Y_t$ 是所选终点的同事件指示量，
不把它解释为同一次相干演化中的中间测量，也不据此建立复制、重置或物理制备权限。

**定义 33.2（计数、端点区间及同一完整见证）。**
事先固定 $0<\alpha<1$ 和 $\alpha_k>0$，使 $\sum_{k=0}^N\alpha_k\le\alpha$。
令 $n_k(t)$ 为前缀 $k$ 的观察次数、$s_k(t)$ 为其中的一次数。
记 $\mathrm B(a,b)=\int_0^1v^{a-1}(1-v)^{b-1}\,dv$。
对 $0\le s\le n$ 定义

$$
C_k(n,s)=\{q\in[0,1]:q^s(1-q)^{n-s}\ge
\alpha_k\mathrm B(s+1,n-s+1)\},\qquad
I_{k,t}=\bigcap_{v=0}^t C_k(n_k(v),s_k(v)).
\tag{33.2}
$$

这里只对 Bernoulli 似然的零次幂取一；它不是权重的 $0^0$ 约定。
令 $\operatorname{logit}(0)=-\infty$、$\operatorname{logit}(1)=+\infty$，
$J_{k,t}=\{z\in\mathbb R:\operatorname{logistic}z\in I_{k,t}\}$。
空交给空集；无穷边界只表示有限 $z$ 的约束缺失，不是原参数。
置信逆像保留原参数本身：

$$
\mathcal F_t=\{\theta\in\Theta:q_k(\theta)\in I_{k,t}\ (0\le k\le N)\},
\qquad P_t=\{p(\theta):\theta\in\mathcal F_t\}.
\tag{33.3}
$$

**定理 33.3（自适应全时间覆盖及正、零两支的完整原参数反演）。**
在假设 33.1 下，对每个固定真参数 $\theta\in\Theta$，都有

$$
\boxed{\Pr_\theta\{\theta\in\mathcal F_t\text{ 对所有有限 }t\}\ge1-\alpha.}
\tag{33.4}
$$

完整正支可且仅可如下取得：取 $p>0$ 和一份有限实向量
$z\in\prod_{k=0}^NJ_{k,t}$，令

$$
R_i(z)=2L-s_i\Delta^2z_i,
\qquad
|R_i(z)-pL|\le pD\quad\text{若供应 }\mathsf E_D,
\qquad
\sum_{i=1}^m|R_i(z)-pL|\le pV\quad\text{若供应 }\mathsf T_V,
\tag{33.5}
$$

再按 (25.4) 取 $r,x,c,\phi,\eta_j$。
两种预算同时供应就同时检验 (33.5)，只用同一份 $z$ 和它还原的同一路径。
已知 $r_*$ 加入 $z_0=p\log r_*$；字面来源 $a_*,b_*$ 再要求
$c=b_*$、$re^{i\phi}=a_*/b_*$，其余已知限制也过滤同一原参数。
$N\le1$ 时 (33.5) 为空约束。

完整零支存在当且仅当每个 $I_{k,t}$ 包含 $1/2$（偶 $k$）或 $2/3$（奇 $k$），
并且另行供应的原参数限制有见证。
存在时保留所有满足这些原参数限制与预算的有限非零来源、完整模长路径及相位，
不由形式 $p=0$ 的 (33.5) 推断零支。
没有额外限制时常路径保证模长见证存在，来源比任意有限正。

每个 $I_{k,t}$ 是闭区间或空集，未访问前缀恰有 $I_{k,t}=[0,1]$、$J_{k,t}=\mathbb R$。
当 $n\ge1$ 时，单次计数区间的边界为

$$
\begin{aligned}
C_k(n,0)&=[0,\ 1-(\alpha_k/(n+1))^{1/n}],\\
C_k(n,n)&=[(\alpha_k/(n+1))^{1/n},\ 1].
\end{aligned}
\tag{33.6}
$$

$0<s<n$ 时两个端点严格处于 $(0,1)$。
故全零、全一计数或未访问端点不能强行改成有限闭 logit 盒。
若所有非空 $I_{k,t}$ 均为闭内区间，则精确回到定理 27.2；
其余情形 (33.5) 仍是完整逆像，省略无穷端对应的不等式即可。
原概率单点 $0$ 或 $1$ 若被要求精确成立，仍没有有限非零参数见证。

对任意历史可测停止时刻 $\tau$，允许 $\tau=\infty$，有

$$
\Pr_\theta\{\tau<\infty,\ \theta\notin\mathcal F_\tau\}\le\alpha.
\tag{33.7}
$$

这不是条件在 $\tau<\infty$ 后的覆盖率下界，也不保证 $\tau$ 有限。
在覆盖事件上，任何仅当 $P_\tau\subseteq A$ 才作出的指数集合宣告 $p\in A$ 均正确；
来源、相位、尺度或路径的集合宣告也必须由同一个 $\mathcal F_\tau$ 蕴含。

证明。这里将已知混合鞅方法作为共同路径反演的中间步骤。
固定端点 $k$、真值 $q=q_k(\theta)\in(0,1)$ 及 $v\in[0,1]$，令

$$
L_{k,t}(v,q)=
\prod_{\substack{j\le t\\J_j=k}}
\left(\frac vq\right)^{Y_j}
\left(\frac{1-v}{1-q}\right)^{1-Y_j}.
\tag{33.8}
$$

没有访问时乘积为一。给定历史与所选 $J_t$，若 $J_t=k$，
下一乘因子的条件均值为
$q(v/q)+(1-q)(1-v)/(1-q)=1$；否则因子为一。
再对同一个参数无关选择核取条件期望，得 $L_{k,t}$ 是非负均值一鞅。
对固定有限 $t$，分母非零，乘积可积；对 $v$ 积分可由非负性交换条件期望，得到

$$
M_{k,t}(q)=\int_0^1L_{k,t}(v,q)\,dv
=\frac{\mathrm B(s+1,n-s+1)}{q^s(1-q)^{n-s}},
\quad n=n_k(t),\ s=s_k(t),\quad M_{k,0}=1.
\tag{33.9}
$$

由 Ville 最大不等式，$\Pr_\theta\{\sup_tM_{k,t}(q_k)\ge1/\alpha_k\}\le\alpha_k$。
对 $k$ 作有限并集，除去概率至多 $\alpha$ 的事件后，
每个真 $q_k$ 同时属于每一行 (33.2)，从而属于所有运行交集。
这直接给 (33.4)，没有对随机计数套用固定样本量尾界。
亦可直接验证所用最大不等式：在首次越界与固定 $T$ 的较小值处停止，
逐步条件期望给停止鞅均值一，非负性给
$\Pr(\text{在 }T\text{ 前越界})\le\alpha_k$；再令 $T$ 递增。
无需预设停止时刻有限或可积。

(33.9) 的均匀 Beta 混合、Ville 及自适应抽样下的混合鞅均是
`literature-attested` 中间方法：
[Howard–Ramdas–McAuliffe–Sekhon，1808.03204v8，Lemma 1、式 (2.11)、§6.1](https://arxiv.org/html/1808.03204v8)，
[同作者，1810.08240，§3.2、§4.4 及附录 A.3 的共轭混合](https://arxiv.org/html/1810.08240)，
[Kaufmann–Koolen，JMLR 22(246)，§2.3、§6](https://www.jmlr.org/papers/v22/18-798.html)。
这里只消费固定真条件概率、参数无关历史选择及非负混合的前提，
没有采用其最优阈值、期望停止时间或最优采样结论。
Howard 等 §4.4 的 iid 例子不直接承担自适应性；这里由 (33.8) 的条件期望逐项核对。
JMLR §6 的通用置信集合映射也属既有工具，不计为新增数学内容。
[事件卷 §§219–222](RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md)
已给节点—时间联合预算；
[四角卷 C-121.3](AURIC_FIB_ATOM_FOUR_CORNER_COHERENCE_AND_SINGLE_COPY_CERTIFICATION.md)
和[奇偶隐藏箭头 §12](PARITY_HIDDEN_ARROW.md)已消费历史条件鞅。
本条新增的是这些供应与完整变动模长路径、原来源及零支的同见证反演，
不把通用置信序列或自适应抽样方法另立为新的理论结论。

对正支，定理 25.2 的双向还原及 (26.6) 把 (33.5) 精确变为路径预算，
也保留所有自由尺度与相位，故既不遗漏候选，也不加入只局部可行的拼接候选。
对零支直接使用非零端口支持数即可，附加来源限制仍须有原参数见证。
这些论证对无限区间边界仍然成立，因为每个被选择的 $z_k$ 必须有限。

似然 $q^s(1-q)^{n-s}$ 在 $[0,1]$ 上连续，且在正处对数凹，
其正水平超集是闭区间；连续交仍是闭区间或空集。
$n=0$ 时 $\mathrm B(1,1)=1>\alpha_k$，所以为 $[0,1]$。
积分或分部积分给
$\mathrm B(s+1,n-s+1)=s!(n-s)!/(n+1)!$，
特别地全零或全一时为 $1/(n+1)$，即得 (33.6)。
$0<s<n$ 时似然在两端为零，超集端点因而在内部，
且其积分不大于最大值，故正水平低于最大值，单次区间非空。
运行交集可以为空，那只表示这次数据没有保留下来的共同候选。
最后，(33.4) 的同一事件蕴含每个有限停止点的包含关系，
所以 (33.7) 及全部集合宣告结论成立。∎

**命题 33.4（正确边缘律仍可使上述反演以概率一失去覆盖）。**
存在满足任意非负路径预算的有限原参数，以及每轮均正确的 Bernoulli 边缘，
但若不满足 (33.1)，(33.4) 对这些数据不成立；即使每个前缀都访问无穷多次也如此。

证明。取 $p=2,a=b=1,x_j=0$，所有控制实正。
由 (25.7)，全部 $q_k=1/2$，两种漂移预算均为零。
预先固定循环访问 $0,\ldots,N$。只抽一次 $U\sim\operatorname{Bernoulli}(1/2)$，
令所有轮次 $Y_t=U$。每个固定轮次、固定所选前缀的边缘都正确，
但第一轮后的历史条件概率为零或一，违背 (33.1)。
每个端点在它的 $n$ 次访问后全零或全一，故

$$
M_{k,t}(1/2)=\frac{2^n}{n+1}\longrightarrow\infty.
\tag{33.10}
$$

每条数据路径最终都排除真 $q_k$，从而排除真原参数，失败概率为一。
因此共同条件律是覆盖证明的实质前提，正确边缘和访问次数都不能补上它。∎

## 34. 策略可达菜单上的同律与不可辨识障碍

**定义 34.1（策略可达前缀）。**
固定假设 33.1 的同一个参数无关策略，包括其停止核。
若存在有限非停止历史 $h$，其每步策略因子均严格正，
并且下一步选择 $k$ 的策略概率严格正，则称 $k$ 策略可达。
记全部此类前缀为 $K_\pi$。
由于每个 $q_k(\theta)\in(0,1)$，该历史在每个 $\theta\in\Theta$ 下都具有严格正概率；
所以 $K_\pi$ 不依赖未知参数。
它包含所有可在某条正概率历史上访问的前缀，不限于某次实现实际访问者，
更不限于无限多次访问者。

**定理 34.2（全部有限自适应记录同律的精确菜单判据）。**
对同一策略下的两个完整候选 $\theta,\theta'$，
以下条件等价：所有有限记录（含停止标签）同律；以及

$$
q_k(\theta)=q_k(\theta')\quad(k\in K_\pi).
\tag{34.1}
$$

因而，来源未另限时，预算内存在指定两个正指数的同律候选，
当且仅当 (32.5) 对 $K=K_\pi$ 成立；
指定正指数与零指数存在同律候选，当且仅当 (32.6) 成立。
两个预算同时存在仍须共用 (32.5) 中的一份漂移。
已知来源则在完整原参数纤维中再检验，不能仅用菜单阈值宣布同律候选存在。

仅在无限多次访问的前缀上概率相同不足以推出同律。
即使所有前缀都可达乃至都反复访问，
共同非零复尺度、来源相对相位及控制相位的自由度仍不能由这些概率识别。

证明。每个有限记录词的概率是其策略因子与
$q_{J_j}^{Y_j}(1-q_{J_j})^{1-Y_j}$ 的乘积。
若 (34.1) 成立，所有正策略因子所对应的前缀均在 $K_\pi$，
故两个乘积相等；零策略因子的词在两者下概率均为零。
停止核相同，含停止标签的词亦然。
反向，取使 $k$ 可达的有限历史 $h$。
两个模型下 $\Pr(H=h,J=k)>0$；联合词概率相等时，
其条件概率比给
$\Pr_\theta(Y=1\mid H=h,J=k)=\Pr_{\theta'}(Y=1\mid H=h,J=k)$，
再用 (33.1) 就得 (34.1)。
将定理 32.2 的全部原参数见证代入即给两个存在分类。
这使用的是全部有限可达历史，不是只比较某个极限频率。

反例取 $N=2,a=b=1,x_j=0$，分别取 $p=1$、$p'=2$，两者预算均为零。
策略先访问前缀一一次，以后始终访问前缀零。
无限多次访问的前缀只有零，两候选在此均为 $1/2$；
第一轮概率却分别为 $\operatorname{logistic}(L/2)$ 与 $1/2$，故有限记录不同律。
最后，(25.7) 不含共同复尺度、$\phi$ 或 $\eta_j$，
改变它们不改任何概率，也不改模长预算。
命题 25.3 的控制相位变动还可改变射线回返，所以同律不认证该回返。
这些全菜单自由度在任意策略下都保留。∎

**命题 34.3（同律、单次推断及置信集合收缩的不同量词）。**
若 $\theta,\theta'$ 满足 (34.1)，任何对数据可测、且使用相同额外随机化的二元检验，
在必须选择这两个候选之一时，其两种错误概率之和为一。
若其指数不同，不存在对这两个候选都依概率收敛到真指数的同一个估计程序。
若一个全参数集合程序对两候选分别有至少 $1-\alpha$ 的全时间覆盖，则在共同记录律下

$$
\Pr\{\theta,\theta'\text{ 同时属于所有有限时刻的集合}\}\ge1-2\alpha.
\tag{34.2}
$$

在该事件上指数投影直径始终至少为 $|p-p'|$。
这些限制不把两个同律候选当作同时真实，也不把覆盖当作一致性。

有限次访问也可阻止收缩，即使相应候选的完整记录律并不相同。
具体地，存在零漂移、固定正指数的模型和策略，
在定理 33.3 的覆盖事件上，无穷多次后仍保留一段非退化的模长路径候选。

证明。共同记录律记作 $P$。若二元检验选择 $\theta'$ 的事件为 $A$，
两错误概率是 $P(A)$ 和 $P(A^c)$，和为一。
若指数相异，取小于指数差一半的两个不交邻域；
同一估计量在共同律下不可能落入两者的概率都趋于一。
两个全时间包含事件各有 $P$ 概率至少 $1-\alpha$，取交即得 (34.2)。
直径结论由集合同时含两个指数直接得到，适用于任意有限停止时刻。

有限访问例子取 $N=2,p=2,a=b=1$，真路径 $x_1=x_2=0$，
策略仍先访问一一次，以后只访问零。
考虑同样 $p,a,b$、但 $x_1=x_2=v\in\mathbb R$ 的候选。
全部候选漂移为零，$q_0=1/2$、$q_1=\operatorname{logistic}(2v)$。
第一次结果为零时，$I_1=[0,1-\alpha_1/2]$；
为一时，$I_1=[\alpha_1/2,1]$。
因为 $\alpha_1<1$，两种情形都包含 $1/2$ 的开邻域，
所以各有一个 $\varepsilon>0$，使所有 $|v|\le\varepsilon$ 的候选满足该区间。
前缀二从未访问，$I_2=[0,1]$。
在覆盖事件上 $I_{0,t}$ 始终包含 $1/2$，
故上述整段候选在每个时刻都属于 $\mathcal F_t$，其模长路径不收缩。
这些候选的首轮概率随 $v$ 严格变化，所以完整记录律实际不同。
一次访问留下的统计不确定性与定理 34.2 的完全同律障碍是两个不同限制。∎

## 35. 访问条件下的集合极限与取得边界

**定理 35.1（显式附加紧性下向完整响应纤维的收缩）。**
除假设 33.1 外，另给一个确定的紧子类 $\Theta_*\subseteq\Theta$，
其拓扑来自原坐标 $(p,a,b,\lambda_1,\ldots,\lambda_N)$ 的通常实、复拓扑，
所有来源分量及控制在此仍非零；允许 $p=0$。
假设真参数 $\theta_*\in\Theta_*$。
策略只访问固定菜单 $K$，在所讨论的数据路径上每个 $k\in K$ 均满足 $n_k(t)\to\infty$。
定义完整响应纤维

$$
\mathcal E_K=\{\vartheta\in\Theta_*:
q_k(\vartheta)=q_k(\theta_*)\ (k\in K)\},\qquad
F_t^*=\mathcal F_t\cap\Theta_*.
\tag{35.1}
$$

在定理 33.3 的覆盖事件与上述无限访问事件之交上，有

$$
\bigcap_{t\ge0}F_t^*=\mathcal E_K,
\qquad
\sup_{\vartheta\in F_t^*}\operatorname{dist}(\vartheta,\mathcal E_K)\longrightarrow0.
\tag{35.2}
$$

若 $f:\Theta_*\to\mathbb R^d$ 连续，使用通常欧氏直径，则

$$
\operatorname{diam} f(F_t^*)\longrightarrow
\operatorname{diam} f(\mathcal E_K).
\tag{35.3}
$$

因此在这些附加条件下，目标 $f$ 的置信集合趋于一个点，当且仅当 $f$ 在完整响应纤维上恒定。
对指数取 $f(\theta)=p$；对原参数整体取恒等映射。
相位与尺度的同律自由度若仍在 $\Theta_*$ 内，整体点识别即失败。
若无限访问条件以概率一成立，上述交事件的概率至少为 $1-\alpha$；
没有该取得条件时不由覆盖率推出此下界。

可直接控制的是已访问次数下的概率宽度。
对 $n=n_k(t)\ge1$，任何 $q\in I_{k,t}$ 满足

$$
|q-s_k(t)/n|\le
r_{k,n}:=\sqrt{\frac{\log((n+1)/\alpha_k)}{2n}},
\qquad \operatorname{diam}I_{k,t}\le2r_{k,n}.
\tag{35.4}
$$

这不是原参数或全局轮数的统一速率。
特别地，不对无紧性约束的 $P_t$ 宣称投影与无限交可以交换，
也不由本定理给出有限期望停止时间或有界物理取得成本。

证明。先验证 (35.4) 及所需的实际缩宽。
令 $\widehat q=s/n$，端点的零次幂仍按似然约定。
二项式分布在 $\widehat q$ 的第 $s$ 项概率至多为一，所以

$$
\frac{\widehat q^{s}(1-\widehat q)^{n-s}}
 {\mathrm B(s+1,n-s+1)}
=(n+1)\binom ns\widehat q^{s}(1-\widehat q)^{n-s}\le n+1.
\tag{35.5}
$$

若 $q\in C_k(n,s)$，取对数得到
$n\,\mathrm{kl}(\widehat q\Vert q)\le\log((n+1)/\alpha_k)$。
这里 $\mathrm{kl}$ 为 Bernoulli 相对熵。
所用标准下界 $\mathrm{kl}(a\Vert q)\ge2(a-q)^2$ 可直接核对：
固定 $q\in(0,1)$，差函数在 $a=q$ 的值和导数均为零，
二阶导数为 $1/(a(1-a))-4\ge0$，端点由连续极限取得。
$q=0,1$ 若相对熵有限只能是 $a=q$，否则下界平凡。
于是 (35.4) 对全部计数边界成立，$r_{k,n}\to0$。
在覆盖事件上真 $q_k(\theta_*)$ 也在区间中，
所以任何保留候选在端点 $k$ 的响应与真值之差至多为 $2r_{k,n_k(t)}$。

由 (25.7)，用原参数写出的统一公式为

$$
\operatorname{logit}q_k(\vartheta)
=e_kL+p\left(\log\frac{|a|}{|b|}
+\sum_{j=1}^kx_j-e_kL/2\right).
\tag{35.6}
$$

它在 $p=0$ 也精确给支持签名，并在 $\Theta_*$ 上连续。
故 $F_t^*$ 是非空嵌套紧集；$\mathcal E_K$ 是非空闭子集。
覆盖事件上整个 $\mathcal E_K$ 都在每个 $F_t^*$ 中，
因为已访问菜单上的真响应相同，其外未访问区间为 $[0,1]$。
反过来，属于全部 $F_t^*$ 的候选由 (35.4) 及无限访问满足全部精确响应等式，
证明第一个等式。

若 (35.2) 的距离不趋零，则存在 $t_j\to\infty$ 及
$\vartheta_j\in F_{t_j}^*$，其到 $\mathcal E_K$ 的距离至少为某个 $\epsilon>0$。
紧性给收敛子列 $\vartheta_j\to\vartheta$。
对每个 $k\in K$，(35.4) 及响应连续性给
$q_k(\vartheta)=q_k(\theta_*)$，故 $\vartheta\in\mathcal E_K$，与距离下界矛盾。
$f$ 在紧集上一致连续，故每个 $f(F_t^*)$ 的点到 $f(\mathcal E_K)$ 的距离一致趋零；
又后者包含在前者中，三角不等式证明 (35.3)。
直径为零的非空紧像恰为单点，给出目标收缩的充要条件。
若纤维恒定且固定 $\varepsilon>0$，首次在 $F_t^*\ne\varnothing$ 且
$\operatorname{diam}f(F_t^*)\le\varepsilon$ 的时刻在这两个事件之交上有限；
有限字母历史使此直径及该停止规则历史可测。
这只由极限推出路径上的最终发生，没有给出该时刻在覆盖失败事件上的行为或期望界。
概率断言由 (33.4) 与概率一访问条件取交得到。∎

**定义 35.2（本模型综合的来源、复用与适用范围）。**
(32.1)–(35.6) 按 `repo-derived` 使用：新增承重内容是删行菜单在完整漂移预算下的
正正、正零同报告分类、可取得阈值与联合预算见证，
以及其同一全参数纤维与显式历史条件观察律的连接。
本卷 §§22–23 的零漂移菜单秩、§25 的原参数逆像及 §§26–29 的连续报告界被直接复用；
它们不另计为新结论。
有限维范数对偶、紧凸分离、Beta 混合、Ville、Bernoulli 相对熵下界及紧集极限都是已知中间工具，
上述条目只给出其在本模型中的参数对应和完整推导，不主张这些方法或本综合的全球优先权。
二阶差分和斜率变差的经典背景沿用定义 30.1 的 Kim–Koh–Boyd–Gorinevsky 来源；
其趋势估计结论不提供这里的相干路径或抽样律。

[Kaufmann–Cappé–Garivier，1407.4443v2，§1 与附录 A](https://arxiv.org/html/1407.4443v2)
明确以所选臂的新观察条件律定义自适应实验，并用完整历史似然作换测度；
[Kaufmann–Koolen，JMLR 22(246)，§2.3](https://www.jmlr.org/papers/v22/18-798.html)
在同一历史过滤下构造臂的混合鞅。
这些是 (33.8)–(33.9) 的已知概率供应，
不是任意来源边缘自动具有该条件律的论据，也不提供本模型的指数可辨识性。
Howard 等的最大不等式及共轭混合定位附于定理 33.3；
本库的事件、四角及奇偶卷仍保留各自的来源与历史合同。

所有预算只约束同一完整有限路径的相邻 log 模长，不约束自由相位，
也不构成实际预算真实的证书。
任意菜单的存在阈值不替代指定报告或置信区间的共同可行性；
区间覆盖不替代收缩，响应收缩不替代原参数点识别，同律不替代实际取得。
假设 33.1 与定理 35.1 的紧性、重复访问条件均是明列附加条件，
没有从确定性相干路径推出共同抽样、源复制、重置、任意控制、物理钟或一般过程认证。

## 追加锚（本行以下为增补区）
