# ΩQ-022：有限合成、内生表示与自评价边界

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。原图以文内文字和公式呈现。

QUANTUM ORIGINS / $\Omega Q$-022

有限合成、内生表示\
与自评价边界

从统一有限读出界恢复精确量子几何

面积、增维、哥德尔与同一整体中的关系闭合

**本轮唯一候选。** 在实双线性、一次齐次、非零、乘法读出、可读单位和同对忠实比较的同一签名下， 把上一轮的幂三角前提进一步削弱为： 两份单位大小的读出合成以后，只有一个共同的有限上界。 本文证明原读出自行恢复连续性、普通三角不等式与内积， 随后同一对比较的忠实性把可读商锁定为四元数。

**对新增问题的准确回应。** 正面积检测指定表示中的线性独立；它不是非零存在的同义词。 表达一个对象不一定新增维数；新增维数也不一定新增信息。 哥德尔及对角化约束的是有效证明、全域自评价和表达闭包，不给出面积或几何升维定律。

2026 年 11 月 8 日（新加坡时间）

|              |                                            |
|:-------------|:-------------------------------------------|
| 研究分支     | `the-omega-institute/trureturing / dev`    |
| 主要固定快照 | `c424643d6929e124fcd872a0e42f9f277b931521` |
| 提交时间     | 2026-11-08 19:56:02（Asia/Singapore）      |
| 末检提交     | `8a24ea4e79de962725aab9d9b49cc605fcc211d8` |
| 末检结果     | 同一理论树；2026-11-08 20:14 后核对        |
| 检索覆盖     | 1359 份理论文件；关键依赖逐段核对          |
| 证明状态     | 自足普通数学证明；未宣称本稿已有 Lean 认证 |
| 输入账本     | 六组核心条件；四组实际量子接口另列         |

## 摘要

用户把存在、面积、内部表达和哥德尔不完备连接到同一几何直觉。 本稿先把其中五种不同的增长分别定义： 增加一个名字、增加读出区别、增加线性秩、增加可表达函数、增加可证命题。 它们都有准确的关系判据，但互不等同。

本轮核心推进是一个严格的前提弱化。 在非结合实代数上，非负一次齐次读出 $p$ 只支付统一局部合成有界， 不预设其连续性、普通三角或任何精确幂三角。 精确乘性先消除零核陪集的有界倍率歧义，再由固定括号乘法幂恢复有界集一致连续。 直接 Cauchy 完备化和局部 Neumann 论证给所有非零左除。 最后把二元比较改写成一个算子与单位的比较， 用平衡二叉合成的多项式损失和同一相似的指数重复，推出原 $p$ 的精确三角不等式。 这一结论不需要原乘法结合、有限维、完备性或预给复结构。 后续内积恢复、同对投影、四元数分类与复二维纯态球面全部在同一原商上完成。

读出背景相对 $\Omega Q$-021 严格弱化： 一个不连续但与欧氏范数有界等价的读出满足新条件，却不满足任何旧精确幂三角。 同时，四元数多项式代数的最低系数读出满足其他所有条件， 却没有统一局部合成界；它给出该有限界在本候选中的尖锐删除反例。 两轮完整模型类仍然等价，输入分组数量也没有降为零。

在量子表示中，本稿给出三种面积的不同零集、正核的最小内生实现、 Schur 余量和增秩公式，以及状态和过程的三元相容。 项目的新特征例表明：旧随机量 $X$ 已知时，$X^2$ 无新增信息， 但相对线性特征 $\operatorname{span}\{1,X\}$ 有严格正余量。 最新原多项式响应模型又给出实际差为零而四份独立面积预算的下确界严格为正， 因而预算残差不能未经证明就解释成新增存在。

逻辑部分完整证明受限 Lawvere 对角论证、显式定义保守性及第二不完备的条件性核心。 固定尺寸、代数常数、多项式关系的有限量子片段可译入实闭域； 另一方面，全局余弦与实加乘可定义整数并解释自然数算术。 因此一个可计算的余弦不动点不使整个表达系统变成可判定系统。 这个联系发生在语言的表达能力中，没有要求新的几何维度。

## 目录

- [1　来源核对、继承部分与本轮改动](#section-1)
- [2　唯一候选、基础语言与输入输出账本](#section-2)
- [3　由有限局部合成界恢复完整范数几何](#section-3)
- [4　由原二元乘性恢复内积](#section-4)
- [5　同一对比较的三元闭合及四元数分类](#section-5)
- [6　反向删除：哪些条件真正承担了工作](#section-6)
- [7　同一合读结构的几何完成：方向、复幅度与正读出](#section-7)
- [8　线、面积、相位与钟：同一几何的准确分工](#section-8)
- [9　态的三元相位：第三个方向保留了哪一份关系](#section-9)
- [10　存在、面积与最小内部表示](#section-10)
- [11　有限量子理论的完整数学完成及实际接口](#section-11)
- [12　把控制器和过程也放回关系中：相干拼接的全部自由度](#section-12)
- [13　固定点、有限三维提升与完整内部时间](#section-13)
- [14　内部表示、对角边界与全局余弦的算术表达力](#section-14)
- [15　最新项目接口：忠实包含与面积预算不能混同](#section-15)
- [16　闭合范围、存在类型与下一条可删除前提](#section-16)

<a id="section-1"></a>

## 1　来源核对、继承部分与本轮改动

### 1.1　项目的新进展和直接前驱

本轮的理论发展分支是 `dev`。 固定快照的 1359 个理论文件均按 Git blob 标识核对， 共 163360015 字节。 相对上一轮最终固定提交 `d1dcf3b7952abf4879645d2d3d1ed29a73ad2429`， 主要快照有四份修改、没有新增或删除理论文件。 2026-11-08 20:14（新加坡时间）开始的唯一末检取得 `8a24ea4e79de962725aab9d9b49cc605fcc211d8`， 该提交时间为 20:06:25，理论目录与主要快照完全相同，逐 blob 复验也全部通过。 这个覆盖数字表示检索与来源完整性，不表示已形式化验证全仓数学。[\[1\]](#ref-repo)

末检在理论目录外另有 30 份新增与 4 份修改，涉及一维逆幂平衡、 指定 Fubini 序列的素数模周期、Hanna 形式级数及公开既有 Pringsheim 障碍。 我们核对了固定增量与相关命题范围，没有执行这些 Lean 模块的重新构建。 它们未新增本候选所需的量子接口；形式级数的负系数也不是负概率或负存在。

| 来源 | 核对到的直接内容 | 本稿的使用方式 |
|:---|:---|:---|
| R5-006 | 第 2–4 节区分读口精化与 Gram 增秩； 第 8–9 节处理 Lawvere、Gödel、Tarski 和定义保守性 | 继承既有判据，补充面积类型和全局余弦解释的联系。[\[2\]](#ref-r5006) |
| 中心响应平方与径向一致性 | 新增第 11–23 节； 删除环境稠密要求，改为一般 JB 完成与已得忠实 JC 包含； 在明确条件下给平方闭式、全径向与共同强度跨平面可加 | 只保留源内明确前提；不将局部结果扩大为全域双线性或完整时间律。[\[3\]](#ref-radial22) |
| 原多项式零响应与 Cayley 域边界 | 第 4.2 节的标量像吸收； 第 6.2 节的实际零差与正预算下界 | 重新核对一个完整标准矩阵模型，反驳错误的预算消零步骤。[\[4\]](#ref-poly22) |
| 原有限能量取得 | 第 9–12 节的有限递归取得与误差证书； 第 12.2 节的线性特征余量不等于新信息 | 给出 $X^2$ 的短证明；取得日程、共同源及数值服务仍是输入。[\[5\]](#ref-energy22) |
| 原源 jet 认证 | 原源读数、方向响应和有限 jet 之间的校验接口 | 保留源绑定条件，不把有限样本或名称当作全域关系已成立。[\[6\]](#ref-jet22) |

上一轮 $\Omega Q$-021 的范数恢复后半段及标准量子接口在本文中重新给出， 因此本稿不要求读者另开旧 PDF 才能检查核心结论。 项目 C133 已在其自身三步成本恒等式前提下研究幂三角与 Hilbert 恢复； 本轮不把“由弱读出恢复几何”这一研究方向宣称为首次出现。[\[7\]](#ref-c133), [\[8\]](#ref-q20repo)

### 1.2　外部研究的角色

Lawvere 的原始对角定理把自应用、评价和反转置于统一框架， 比“更大空间”更准确地描述全域自评价的限制。[\[9\]](#ref-q022-lawvere) Gödel–Rosser 与 Tarski 的定理分别处理有效算术证明和同层真值， 其前提在逻辑章节中逐项列出。[\[10\]](#ref-q022-godel), [\[11\]](#ref-q022-rosser), [\[12\]](#ref-q022-tarski-truth), [\[13\]](#ref-q022-paulson) Breuer 的自测量工作研究内部观察者不能区分整体全部当前状态的条件， 不是从自指推出量子 Born 律。[\[14\]](#ref-breuer22)

量子与不可判定性的一个强而精确的既有连接是 Cubitt–Pérez-García–Wolf 的谱隙定理： 在特定二维、平移不变、最近邻、固定局部维数的 Hamiltonian 家族中， 热力学极限的有隙与无隙问题不可判定。[\[15\]](#ref-cpw22) 它不声称固定有限矩阵的谱计算自动不可判定。 2026 年的 AdS/CFT 不可判定性构造已有 10 月 27 日公开 Comment 与 Reply； 本稿把它记录为有明确争论和附加假设的最新方向， 不以其作为“面积来自哥德尔”的已证明前提。[\[16\]](#ref-ads22), [\[17\]](#ref-adsComment22), [\[18\]](#ref-adsReply22)

量子重建、复振幅比较和完全正过程拼接分别采用相应的标准条件与表示结果； 本稿在有限维情形重新给出使用到的证明。[\[19\]](#ref-cdp), [\[20\]](#ref-masanes), [\[21\]](#ref-magnot), [\[22\]](#ref-aberg), [\[23\]](#ref-vanrietvelde)

**本轮新旧边界。**

有限局部合成界下的原读出恢复及其删除反例，是本稿相对上一轮的前提推进。 Gram、Schur、Lawvere、标准量子表示及项目已有的面积预算反例，均按既有结果标识。 本稿不主张文献首创，不把仓库收录或普通证明改称形式化认证。

<a id="section-2"></a>

## 2　唯一候选、基础语言与输入输出账本

### 2.1　定义与六组核心输入

基础语言为通常实数、集合、函数、逻辑及可用的实复分析。 设 $\mathcal A$ 为实向量空间，

$$
m:\mathcal A\times\mathcal A\to\mathcal A,\qquad
p:\mathcal A\to[0,\infty),\qquad xy:=m(x,y).
$$

定义

$$
q(x)=p(x)^2,\quad N=p^{-1}(0),\quad
k_{a,b}=ab-ba,\quad L_x(c)=xc,
$$

$$
T_{a,b}c=(ab-ba)c+a(bc)-b(ac).
$$

以下六组是全部核心输入；每一行中的量词都在同一原对象上成立。

$$
\begin{aligned}
\mathsf B_1:\;&m\text{ 为实双线性};\\
\mathsf B_2^{22}:\;&p(tx)=|t|p(x),\\[-1mm]
&\exists M<\infty\ \forall x,y,\quad
p(x)\le1,\ p(y)\le1\Longrightarrow p(x+y)\le M;\\
\mathsf E:\;&\exists x,\quad p(x)>0;\\
\mathsf N:\;&\forall x,y,\quad p(xy)=p(x)p(y);\\
\mathsf U:\;&\exists\varepsilon\ \forall x,\quad
p(\varepsilon x-x)+p(x\varepsilon-x)=0;\\
\mathsf F:\;&\exists a,b\ \forall c,\quad
p(T_{a,b}c)=0\Longrightarrow p(c)=0.
\end{aligned}
$$

允许把 $M$ 换成一个更大的正数，所以其符号不构成额外条件。 后文写 $\mathsf U_q$ 时表示等价的平方读数版本： $q(\varepsilon x-x)+q(x\varepsilon-x)=0$。 非负性使两个版本的零条件等价。

$$
\boxed{\text{单位读出二元合成只有共同有限上界。}}
$$

该上界同时约束所有原输入；不能随一对对象、一个历史或一次试验改变。 这里未输入任何精确幂三角、普通三角、读出连续性、内积、有限维或结合律。 一次齐次性仍在输入中，故平方读数的二次齐次性仍有明确来源。

### 2.2　闭合输出区域

$$
p(x+y)\le p(x)+p(y),\qquad
q(x+y)+q(x-y)=2q(x)+2q(y),
$$

$$
\mathcal B(x,y)=\tfrac14(q(x+y)-q(x-y))
\in\operatorname{SymBil}_{\mathbb R}(\mathcal A),\qquad
N=\operatorname{rad}\mathcal B,
$$

$$
(A:=\mathcal A/N,m,p)\cong(\mathbb H,\cdot,|\cdot|),
\qquad
\dim_{\mathbb R}A=4,\quad\dim_{\mathbb R}1^\perp=3,
$$

$$
J=\frac{T_{a,b}}{2p(k_{a,b})},\qquad
J^2=-I,\qquad
h(x,y)=B(x,y)+iB(Jx,y),
$$

$$
(A,J,h)\cong\mathbb C^2,\qquad
S^1\longrightarrow S^3\longrightarrow\mathbb{CP}^1\cong S^2.
$$

算子恒等式在同一可读商上成立；原层的对应差只保证读数为零。 $\mathsf F$ 从未被擅自扩展到辅助完成。

### 2.3　与上一轮的精确比较

$$
\mathsf B_2^{21}:
\quad p(tx)=|t|p(x),\quad
\exists r\in(0,1]\ \forall x,y,\quad
p(x+y)^r\le p(x)^r+p(y)^r.
$$

$$
\boxed{\mathsf B_2^{21}\Longrightarrow\mathsf B_2^{22}
\quad\text{且背景上的反向蕴含不成立。}}
$$

加入其余五组后，新候选恢复普通三角，因而恢复旧条件（取 $r=1$）。 两轮的完整模型类等价，分组计数仍为六。 “更简洁”准确指第二个背景组严格弱化； 它不指总页数、证明长度或语言无关的最少公理数。

### 2.4　完整量子接口与逻辑接口分开计数

有限量子理论另保留四组实际接口：

$$
\mathsf I_{\rm read},\qquad
\mathsf I_{\rm comp},\qquad
\mathsf I_{\rm proc},\qquad
\mathsf I_{\rm time}.
$$

它们分别绑定原准备与事件、同复中心复合与完整正锥、 全部有限参照下的原过程正性、实际连续可逆钟流及理想更新。 定义标准矩阵对象不自动证明原数据已经满足这些接口。

逻辑章节又独立列出自应用、允许的读出类、有效公理化、算术可表达性、 一致性及标准可证明性条件。 这些用于逻辑定理，不被藏进六组量子候选，也不由量子球面自动推出。

<a id="section-3"></a>

## 3　由有限局部合成界恢复完整范数几何

本节使用上一节的同一原签名与六组条件。恢复普通三角只需要左单位，不需要右单位或 $\mathsf F$。

$$
p(x),p(y)\le1\Longrightarrow p(x+y)\le M\quad(M<\infty\text{ 对所有原输入共同适用}).
\tag{3.1}
$$

### 3.1　准三角与有限加和的准确代价

#### 引理 3.1：有限单位合成界等价于某个统一准三角界

对绝对一次齐次的非负函数 $p$，式 (3.1) 的局部有界部分 等价于存在有限常数 $C\ge1$ 使

$$
p(x+y)\le C\bigl(p(x)+p(y)\bigr)\qquad(\forall x,y).
\tag{3.2}
$$

**证明。**

准三角在 $p(x),p(y)\le1$ 上给局部界 $2C$。 反向令 $s=p(x)+p(y)$。若 $s>0$，则 $p(x/s),p(y/s)\le1$， 局部界与齐次性给 $p(x+y)\le Ms$。 若 $s=0$，则对每个 $t>0$ 都有 $p(tx)=p(ty)=0\le1$， 从而 $t p(x+y)\le M$。令 $t\to\infty$ 得 $p(x+y)=0$。 取 $C=\max\{1,M\}$ 即可。

$\square$

下文固定这样一份由原局部界导出的 $C$。这没有增加另一个独立输入条件。 定义

$$
K_n=C^{\lceil\log_2n\rceil}\qquad(n\ge1).
$$

#### 引理 3.2：平衡二叉加和界

对任意 $n\ge1$ 与 $z_1,\ldots,z_n\in\mathcal A$，

$$
p\!\left(\sum_{j=1}^nz_j\right)
\le K_n\sum_{j=1}^np(z_j).
\tag{3.3}
$$

**证明。**

补零到 $2^h$ 项，其中 $h=\lceil\log_2n\rceil$。 按等深二叉树逐层相加，在每一层使用一次 (3.2)， 共乘以 $C^h$。向量加法可重新分组；本证明未使用原乘法结合性。

$\square$

### 3.2　零核与连续性均须由乘法重复推出

#### 引理 3.3：原零核上的精确不变性

在 $\mathsf B_1+\mathsf B_2^{22}+\mathsf N$ 下， $N=p^{-1}(0)$ 为实线性双边理想，且

$$
\boxed{p(x+n)=p(x)\qquad(x\in\mathcal A,\ n\in N).}
\tag{3.4}
$$

因此原商 $A_0$ 上的 $p([x])=p(x)$ 良定、正定、绝对一次齐次、 满足同一个准三角界且精确乘性。 在 $\mathsf E$ 与可读左单位下，商非零，并有真正左单位 $1=[\varepsilon]$，$p(1)=1$。 原条件若含右单位，它也分别下降。

**证明。**

齐次性与准三角给 $N$ 线性，乘性给 $p(xn)=p(nx)=0$，故 $N$ 为理想。 此时只由准三角尚只能得到 $p(x+n)\le Cp(x)$，不能直接下推 $p$。

对每个正整数 $k$ 固定一份完全括号方式，记含 $k$ 个 $x$ 的乘法单项式为 $x^{[k]}$。 由双线性与理想性，

$$
(x+n)^{[k]}-x^{[k]}\in N.
$$

精确乘性与准三角给

$$
p(x+n)^k
=p\bigl((x+n)^{[k]}\bigr)
\le C p\bigl(x^{[k]}\bigr)
=C p(x)^k.
$$

取 $k$ 次根，再令 $k\to\infty$，得到 $p(x+n)\le p(x)$。 对 $x+n$ 和 $-n$ 反向重复，得等式。 商乘法由理想性良定，原各条件继承。 可读单位的零差在商中成为真正等式。 非平凡性给非零 $x$，从 $p(1x)=p(1)p(x)=p(x)$ 消去 $p(x)$，得到 $p(1)=1$。

$\square$

#### 引理 3.4：有限乘法幂的差界

若 $p(x),p(y)\le R$、$R>0$，并记 $\delta=p(x-y)$， 则对任意 $n\ge1$ 及任意固定完全括号的乘法单项式有

$$
p\bigl(x^{[n]}-y^{[n]}\bigr)
\le nK_nR^{n-1}\delta.
\tag{3.5}
$$

**证明。**

固定括号方式给一个实 $n$ 线性映射 $F_n$。 逐个槽替换的望远镜展开为

$$
F_n(x,\ldots,x)-F_n(y,\ldots,y)
=\sum_{j=1}^nF_n(y,\ldots,y,x-y,x,\ldots,x).
$$

第 $j$ 项的读出由乘性精确等于 $p(y)^{j-1}\delta p(x)^{n-j}$，至多为 $R^{n-1}\delta$。 应用引理 3.2 即得。

$\square$

#### 引理 3.5：原读出在有界集合上一致连续

对 $p(x),p(y)\le R$、$R>0$ 及 $\delta=p(x-y)$，

$$
\boxed{
|p(x)-p(y)|
\le (C^{1/n}-1)R+
\bigl(CnK_nR^{n-1}\delta\bigr)^{1/n}
\quad(\forall n\ge1).
}
\tag{3.6}
$$

特别地，$p$ 在每个 $p$ 有界集合上一致连续。

**证明。**

原准三角、乘性及引理 3.4 给

$$
p(x)^n\le C p(y)^n+CnK_nR^{n-1}\delta.
$$

对非负数使用 $(a+b)^{1/n}\le a^{1/n}+b^{1/n}$，得

$$
p(x)-p(y)
\le(C^{1/n}-1)p(y)+\bigl(CnK_nR^{n-1}\delta\bigr)^{1/n}.
$$

将 $p(y)$ 换为上界 $R$，再交换 $x,y$，得到显示式。 给定 $\epsilon>0$，先选有限 $n$ 使 $(C^{1/n}-1)R<\epsilon/2$； 再令 $\delta$ 足够小，使余项小于 $\epsilon/2$。 次序是先固定一个有限幂，再缩小输入差，不是无依据地交换两个极限。

$\square$

### 3.3　精确保留原乘法读出的完成

#### 引理 3.6：直接 Cauchy 完成

原商 $A_0$ 可嵌入一个非零完备实向量空间 $B$，其读出 $p$ 和乘法 保留原准三角界、绝对一次齐次性、精确乘性以及原单位律。 完成不需要先把 $p$ 改换为等价的幂次准范数。

**证明。**

称 $(x_n)$ 为 Cauchy 序列，若 $p(x_n-x_m)\to0$。 准三角给它 $p$ 有界：固定一个足够晚的 $x_N$，对其后的项用 $p(x_n)\le C(p(x_N)+p(x_n-x_N))$。 引理 3.5 因而给 $p(x_n)$ 为实 Cauchy 序列。

对两个 Cauchy 序列规定

$$
(x_n)\sim(y_n)\quad\Longleftrightarrow\quad p(x_n-y_n)\to0.
$$

准三角保证传递性。令 $B$ 为这些序列的商，并定义

$$
p([x_n])=\lim_{n\to\infty}p(x_n).
$$

有界集一致连续性保证代表无关。 该极限为零恰好表示 $(x_n)$ 等价于零序列，因此完成中的 $p$ 正定。 和、固定实数倍按逐项运算定义；准三角与齐次性保证良定。

若 $x_n,y_n$ 为 Cauchy 序列，双线性与准三角给

$$
\begin{split}
p(x_ny_n-x_my_m)
\le C\bigl(&p(x_n-x_m)p(y_n)\\
&+p(x_m)p(y_n-y_m)\bigr).
\end{split}
$$

两序列有界，故乘积也 Cauchy；同一估计说明更换代表不改变乘积等价类。 精确乘性由

$$
p([x_n][y_n])
=\lim_n p(x_n)p(y_n)
=p([x_n])p([y_n])
$$

保留。双线性、原准三角、一次齐次性和单位等式也逐项下降。

常值序列给原商的等读出嵌入。任一 $X=[x_n]$ 满足

$$
p(X-x_N)=\lim_{n\to\infty}p(x_n-x_N)\longrightarrow0\quad(N\to\infty),
$$

其中最后一步由原 Cauchy 条件给出，故原商稠密。 为证明 $B$ 完备，设 $(X_j)$ 是 $B$ 中 Cauchy 序列。 由稠密性选 $a_j\in A_0$ 使 $p(X_j-a_j)<1/j$。 三项加和界给

$$
p(a_j-a_k)
\le K_3\bigl(1/j+p(X_j-X_k)+1/k\bigr),
$$

所以 $(a_j)$ 为原商中的 Cauchy 序列。 令 $X=[a_j]$，则 $p(a_j-X)\to0$，再由

$$
p(X_j-X)\le C\bigl(p(X_j-a_j)+p(a_j-X)\bigr)
$$

得到 $X_j\to X$。

引理 3.5 的证明只使用已保留的代数与准三角条件， 所以同样适用于 $B$。 其读出球是开集并构成可数邻域基：若 $p(x-a)<\epsilon$， 由连续性可选足够小的 $p(y-x)$ 保证 $p(y-a)<\epsilon$。 向量运算连续由准三角与齐次性给出，乘法在有界邻域上由上述乘积差估计连续。 因此此完成是所需的完备拓扑代数。

$\square$

完成仅作证明工具。后续所有分类结论必须限制回同一个原商； 原 $\mathsf F$ 的量词没有自动扩张到 $B$。

### 3.4　算子、左除和有限重复

对 $B$ 的有界实线性算子，定义

$$
\|R\|_{\rm op}
=\sup_{x\ne0}\frac{p(Rx)}{p(x)}.
$$

#### 引理 3.7：算子完成与小半径 Neumann 公式

有界算子构成完备实向量空间，满足

$$
\|R+S\|_{\rm op}\le C(\|R\|_{\rm op}+\|S\|_{\rm op}),
\qquad
\|RS\|_{\rm op}\le\|R\|_{\rm op}\|S\|_{\rm op}.
$$

若 $\|R\|_{\rm op}<1/C$，则

$$
(I+R)^{-1}=\sum_{n=0}^{\infty}(-R)^n.
$$

**证明。**

逐个作用于 $x$ 并取上确界给两个不等式。 若 $R_n$ 是算子 Cauchy 序列，则每个 $R_nx$ 在 $B$ 中收敛。 向量运算连续，故逐点极限 $R$ 实线性。 原算子序列的读数统一有界；$p$ 的连续性给极限算子有界。 对

$$
p((R_n-R_m)x)
\le\|R_n-R_m\|_{\rm op}p(x)
$$

令 $m\to\infty$，再取上确界，即得 $R_n\to R$ 的算子准范数收敛。

令 $\rho=\|R\|_{\rm op}<1/C$。 对有限尾和采用右嵌套加和，每一步用原准三角，得

$$
\left\|\sum_{k=m}^{n}(-R)^k\right\|_{\rm op}
\le C\rho^m\sum_{j=0}^{n-m}(C\rho)^j
\le\frac{C\rho^m}{1-C\rho}.
$$

它随 $m\to\infty$ 一致趋零，故级数在完整算子空间中收敛。 有限几何恒等式给部分和与 $I+R$ 的两侧乘积均趋于 $I$； 算子复合连续性使极限为双侧逆。 这里只使用算子复合的结合律，未使用 $B$ 原乘法的结合律。

$\square$

#### 引理 3.8：所有非零左乘为满射相似

对每个非零 $x\in B$，$L_x:y\mapsto xy$ 为满射，且

$$
\|L_x\|_{\rm op}=p(x),
\qquad
\|L_x^{-1}\|_{\rm op}=p(x)^{-1}.
$$

**证明。**

乘性给 $p(L_xy)=p(x)p(y)$，因此 $L_x$ 单射，算子读数恰为 $p(x)$； 若满射，逆读数必为其倒数。 实维数一时非零线性单射自动满射。 实维数至少二时，令

$$
\mathcal G=\{x\in B\setminus\{0\}:L_x\text{ 满射}\}.
$$

左单位使 $\mathcal G$ 非空。 若 $x\in\mathcal G$ 且 $p(y-x)/p(x)<1/C$，则

$$
L_y=L_x\bigl[I+L_x^{-1}(L_y-L_x)\bigr],
\qquad
\|L_x^{-1}(L_y-L_x)\|_{\rm op}
\le\frac{p(y-x)}{p(x)}<1/C.
$$

Neumann 引理给 $L_y$ 可逆，故 $\mathcal G$ 相对开。 若 $x_n\in\mathcal G$ 且 $x_n\to x\ne0$，读出连续性给 $p(x_n)\to p(x)>0$，充分大的 $n$ 满足同一小扰动条件，故 $x\in\mathcal G$。 读出球构成可数邻域基，因此这证明相对闭。

穿孔实向量空间 $B\setminus\{0\}$ 在维数至少二时路径连通： 直线段若过零，就取不在该直线上的一个中间点，用两条避零线段连接。 每条线段在当前拓扑中连续，因为其参数差的读出等于参数差绝对值乘以一个固定读数。 因此非空开闭集 $\mathcal G$ 等于整个穿孔空间。

$\square$

#### 定理 3.9：有限局部界恢复普通三角不等式

在实双线性乘法、$\mathsf B_2^{22}+\mathsf E+\mathsf N$ 以及可读左单位下， 原读出满足

$$
\boxed{p(x+y)\le p(x)+p(y)\qquad(\forall x,y\in\mathcal A).}
\tag{3.7}
$$

**证明。**

在上述完成中取 $y\ne0$，定义

$$
S=L_xL_y^{-1},\qquad
S+I=L_{x+y}L_y^{-1},\qquad
\alpha=\frac{p(x)}{p(y)},\quad
\beta=\frac{p(x+y)}{p(y)}.
$$

它们是比例分别为 $\alpha,\beta$ 的精确相似；零比例的情形按零算子理解。 因此

$$
\|S^k\|_{\rm op}=\alpha^k\quad(k\ge1),\qquad
\|(S+I)^n\|_{\rm op}=\beta^n,
$$

且 $\|S^0\|_{\rm op}=\|I\|_{\rm op}=1$。 算子复合的有限二项式与引理 3.2 的算子版本给

$$
\begin{aligned}
\beta^n
&=\left\|\sum_{k=0}^{n}\binom nk S^k\right\|_{\rm op}\\
&\le K_{n+1}\sum_{k=0}^{n}\binom nk\alpha^k
=K_{n+1}(1+\alpha)^n.
\end{aligned}
$$

故

$$
\beta\le C^{\lceil\log_2(n+1)\rceil/n}(1+\alpha).
$$

因为 $\lceil\log_2(n+1)\rceil/n\to0$，令 $n\to\infty$ 得 $\beta\le1+\alpha$，即完成中的普通三角不等式。 $y=0$ 情形直接成立。 限制回原商，再使用精确零核下降，得到原 $\mathcal A$ 上同一读出的显示结论。

$\square$

#### 推论 3.10：本轮删去的前提与保留的理论

固定原有 $\mathsf B_1,\mathsf E,\mathsf N,\mathsf U,\mathsf F$， 把 $\mathsf B_2^{21}$ 的统一幂三角条件换成 $\mathsf B_2^{22}$ 的有限局部界后， 完整模型类不变；原范数、内积、四元数及后续有限量子结构结论仍适用。 原读出背景本身则严格变弱。

**证明。**

旧幂三角在 $p(x),p(y)\le1$ 时给 $p(x+y)\le2^{1/r}$，故旧背景蕴含新背景。 反向，在其余核心条件下，定理 3.9 给普通三角， 这就是旧条件取 $r=1$ 的情形。 背景严格性由下面的反例给出。

$\square$

#### 反例 3.11：有限局部界不自带任何精确幂三角

在 $\mathbb R^2$ 上定义

$$
p(s,t)=
\begin{cases}
\sqrt{s^2+t^2},&t=0,\\
2\sqrt{s^2+t^2},&t\ne0.
\end{cases}
$$

它正定、绝对一次齐次、满足有限局部合成界， 但不满足任何固定 $r>0$ 的精确幂三角。

**证明。**

有 $\|x\|_2\le p(x)\le2\|x\|_2$，故

$$
p(x+y)\le2\|x+y\|_2
\le2\bigl(p(x)+p(y)\bigr).
$$

由引理 3.1 它满足有限局部界。 若某个 $r>0$ 的精确幂三角成立，对 $x=(1,0)$、$y=(0,\epsilon)$ 得

$$
\bigl(2\sqrt{1+\epsilon^2}\bigr)^r
\le1+(2\epsilon)^r.
$$

令 $\epsilon\downarrow0$，得到 $2^r\le1$，矛盾。

$\square$

这个二维反例只用于区分读出背景；没有声称它还满足原乘法读出等其余核心条件。 全部新条件恰恰通过乘法重复排除它的不连续行为。

#### 反例 3.12：删去局部有限界而保留其余全部核心条件

取中央不定元 $t$ 的四元数多项式代数 $\mathbb H[t]$。 若 $f\ne0$ 的最低非零系数为 $a_m$，定义

$$
f(t)=\sum_{k=m}^na_kt^k,\quad a_m\ne0,
\qquad p(f)=|a_m|,\qquad p(0)=0.
$$

则 $\mathsf B_1,\mathsf E,\mathsf N,\mathsf U,\mathsf F$ 和一次齐次性全成立， 但有限局部合成界失败，原可读出商也不是 $\mathbb H$。

**证明。**

该多项式代数实双线性、结合、带双侧单位，且作为实向量空间无限维。 $p$ 正定且绝对一次齐次，并有 $p(1)=1$。 若 $g$ 的最低非零系数为 $b_\ell$，则 $fg$ 的最低非零次幂为 $m+\ell$， 系数为 $a_mb_\ell\ne0$。四元数乘法范数给

$$
p(fg)=|a_mb_\ell|=|a_m||b_\ell|=p(f)p(g).
$$

取 $a=i,b=j$。结合性给

$$
T_{i,j}c=(ij-ji)c+i(jc)-j(ic)=4kc,
\qquad p(T_{i,j}c)=4p(c),
$$

因此同一个比较对对全部 $c$ 不失读。 然而对任意 $R>0$，取

$$
f_R=1+Rt,\qquad g=-1.
$$

则

$$
p(f_R)=p(g)=1,
\qquad p(f_R+g)=R.
$$

故不存在统一有限局部合成界。 这里 $\ker p=0$，原商仍为无限维 $\mathbb H[t]$， 而且 $t$ 在多项式代数中无逆，故不可能同构于 $\mathbb H$。

$\square$

该反例隔离了局部稳定条件的实际作用：低阶项相消后， 原先被遮住的高阶系数可以使新读出任意大。 在全部候选条件下，恢复的普通三角则给两个单位输入之和的读出至多为 $2$。

本轮证明既未把 $p$ 换成等价但失去乘性的重范数， 也未预先给原空间补入连续性、除法、内积或有限维数。 六个命名输入组仍为六个；这里没有证明原子公理组数最小，也不主张相关范数定理的文献首创。

<a id="section-4"></a>

## 4　由原二元乘性恢复内积

上一节已经证明原 $p$ 是半范数。所构造的同一 Cauchy 完成 $B$ 现在是普通实 Banach 空间；无需另加完备性条件。 所有非零左乘的满射相似性质已由引理 3.8 证明。 本节不使用 $\mathsf F$，也不把它延拓到辅助完成。 单侧除法绝对值代数的内积范数性质有既有研究；以下给出自足谱证明。[\[24\]](#ref-rodriguez)

### 4.1　每个二元平面都被迫成为欧氏平面

下面仅构造一个复线性证明辅助空间；它不预先赋予原系统任何复数结构。

#### 引理 4.1：保持相似倍率的复化

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

#### 引理 4.2：仅用到的谱事实及证明

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

#### 定理 4.3：二元平面欧氏化

设 $B$ 满足引理 3.8 的条件。 任给 $x,y\in B$、$y\ne0$，存在一个复数 $\lambda$，使所有 $\alpha,\beta\in\mathbb R$ 同时满足

$$
\boxed{\quad
\|\alpha x+\beta y\|^2
=\|y\|^2\,|\alpha\lambda+\beta|^2.
\quad}
\tag{P}
$$

因此原范数满足平行四边形恒等式。

**证明。**

令 $S:=L_xL_y^{-1}$，并按引理 4.1 将其复化。 选取一个 $\lambda\in\sigma(S_{\mathbb C})$。 对实数 $\alpha,\beta$，双线性给原实算子等式

$$
\alpha S+\beta I=L_{\alpha x+\beta y}L_y^{-1}.
$$

若 $\alpha x+\beta y\ne0$，引理 3.8 使右式成为 倍率

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

#### 引理 4.4：极化双线性无需再次输入

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

#### 推论 4.5：恢复的是原 $q$

在实双线性乘法及 $\mathsf B_2^{22}+\mathsf E+\mathsf N+\mathsf U_q$ 下，

$$
q(x+y)+q(x-y)=2q(x)+2q(y)
$$

对原 $\mathcal A$ 的所有 $x,y$ 成立，并且

$$
\mathcal B(x,y):=\frac14\bigl(q(x+y)-q(x-y)\bigr)
$$

为半正实双线性型，$\mathcal B(x,x)=q(x)$， $\operatorname{rad}\mathcal B=N$。 此结论的证明只使用 $\mathsf U_q$ 中的左单位部分。

**证明。**

使用前节的同一个原商 $A_0$ 与辅助完成 $B$，在 $B$ 中用上面两条定理得到平行四边形和内积。 将恒等式限制回 $A_0$，再经原商映射拉回 $\mathcal A$，得到所列原函数公式。 核为 $N$，因为商中内积正定。 整个过程没有改变原乘法、原 $q$ 或原零读出等价关系。

$\square$

证明采用通常实、复分析，包括 Neumann 级数、Liouville 定理，以及 Hahn–Banach 的连续泛函分离结论。这些属于明示数学基础；谱证明中的辅助 $i$ 并非原物理幅度已经拥有复结构。原幅度的复结构在下一节由原见证对导出。

<a id="section-5"></a>

## 5　同一对比较的三元闭合及四元数分类

前两节已经由有限局部合成界恢复原普通三角不等式与原半正二次型。以下始终在原商 $A=\mathcal A/N$ 上工作，不向辅助完成延伸 $\mathsf F$。全部使用的投影恒等式在此重新证明。

#### 引理 5.1：忠实合成自动产生同一对非交换见证

候选中的同一对 $a,b$ 必满足 $q(k_{a,b})>0$。

**证明。**

在正定商中，单位律给

$$
T_{a,b}(1)=(ab-ba)+ab-ba=2k_{a,b}.
$$

若 $q(k_{a,b})=0$，则 $q(T_{a,b}(1))=0$，忠实性迫使 $q(1)=0$， 与 $q(1)=1$ 矛盾。 这也说明原 $q$ 非零不可删除，否则 $\mathsf F$ 会真空成立。

$\square$

### 5.1　只由单位与乘性恢复的代数恒等式

以下在任意非零实正内积空间 $A$ 上工作，乘法双线性且有单位 $1$， 满足 $q(xy)=q(x)q(y)$。仍不假定有限维或结合性。 令

$$
L_x(y):=xy,\quad R_x(y):=yx,\quad
t(x):=B(1,x),\quad \bar x:=2t(x)1-x,\quad W:=1^\perp.
$$

#### 引理 5.2：共轭、交替性与纯方向 Clifford 关系

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

### 5.2　主恒等式：合成读出本来就是内部四维投影

#### 定理 5.3：单对内生投影与反射公式

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

#### 推论 5.4：二元响应的精确正分解

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

**图示（文字版）。** 同一第三元 $c=Pc+Qc$ 分为两条正交支路：经 $P$ 得到 $Pc\in H$，再由同向的两份响应得到 $Tc=2L_kPc$；经 $Q=I-P$ 得到 $Qc\in H^\perp$，两份响应在合读中反向抵消，而结合缺口给出 $\mathscr A c=L_kQc$。

**图 1。** 同一第三元的正交分解。上支由合读 $T$ 读出；下支在合读中抵消，由结合缺口 $\mathscr A$ 精确读出。忠实条件排除下支中的非零可读元。

#### 定理 5.5：一对忠实合成的完整分类

在本轮固定实双线性与有限合成读出背景中，$\mathsf N+\mathsf U_q+\mathsf E+\mathsf F$ 成立， 当且仅当 $N=q^{-1}(0)$ 为双边理想，且由同一原乘法与同一原读数下降得到的 $\mathcal A/N$ 等距代数同构于标准四元数 $\mathbb H$。 此时原候选对已经不交换，商上的全部三元精确结合，原层全部结合缺口具有零读数。

**证明。**

正向，前两节的原商、三角与内积恢复给非零正定幺商，$\mathsf F$ 下降为 $T$ 的单射性。 在单位上计算 $T1=2k$，故 $k\ne0$，投影定理可用。 但 $\ker T=H^\perp$，因此 $H^\perp=0$，全部商就是四维 $H$。 全局商结合性及原层零结合缺口随即成立。

反向，若同一商等距同构于 $\mathbb H$，选择 $1,i,j$ 的原代表作为 $\varepsilon,a,b$。 四元数范数给乘性，可读单位成立且读数非零。 结合性给 $T(c)=2k c$，其中 $k=2k_{\mathbb H}$ 非零。 所以 $q(Tc)=4q(k)q(c)$，得到原层忠实条件。

$\square$

#### 推论 5.6：新产生的过程也满足有限二元、三元闭合

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

#### 命题 5.7：由同一对内生的复二维表示

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

#### 推论 5.8：存在、反向与逆的正读数

在该可读商中，每个 $x\ne0$ 都有双侧逆

$$
x^{-1}=\frac{\bar x}{q(x)},\qquad
q(x^{-1})=\frac1{q(x)}>0,\qquad q(-x)=q(x)>0.
$$

因此按 $q(x)>0$ 定义可读存在时，反向和取逆都不产生负存在； 取逆是非零可读元素集合上的对合双射。

**证明。**

元素二次式给 $x\bar x=\bar x x=q(x)1$， 而 $q(\bar x)=q(x)$ 由共轭定义与极化直接得到。 结合性给显示的双侧逆；平方齐次性给其读数和 $q(-x)=q(x)$。 逆的唯一性给 $(x^{-1})^{-1}=x$。

$\square$

<a id="section-6"></a>

## 6　反向删除：哪些条件真正承担了工作

#### 反例 6.1：删除忠实条件：八元数的尖锐边界

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

这给出非零可读第三元上两份响应完全抵消的显式例子。 更一般地，任意非交换对的 $T$ 由投影定理都只有实秩四， 而 $\mathbb O$ 实维八，故不可能忠实；交换对则有 $T(1)=0$。 所以不存在其他见证对能够挽救八元数上的 $\mathsf F$。 同一对生成的所有有限代数表达式都在 $\mathbb H\oplus0$ 内； 在该子代数上 $T=2L_k$ 忠实。只检验自生成的小域会漏掉 $c$。

#### 反例 6.2：删除存在性

取任意实双线性代数和 $q\equiv0$。其他三组关系均真，$\mathsf F$ 真空成立， 但可读商为零。故存在性不能被没有非零域的条件蕴含偷偷代替。

#### 反例 6.3：即使保留左单位，右单位仍不可删除

在实空间 $\mathbb C$ 上定义 $x\star y=\bar x y$，$p(x)=|x|$。 乘法实双线性，范数乘性，$1$ 是左单位。取 $a=1,b=i$，则

$$
k=a\star b-b\star a=2i,\quad
Y(c)=a\star(b\star c)-b\star(a\star c)=0,\quad T(c)=-2ic.
$$

所以 $T$ 全域忠实。右单位只能是 $1$，但 $i\star1=-i\ne i$。 该商实维二，不是四元数原乘法。 因此范数恢复只需要左单位，不意味着最终候选也可删除右单位。

#### 反例 6.4：删除乘性

令 $A=M_3(\mathbb R)$，通常乘法，$q(X)=\operatorname{Tr}(X^{\mathsf T}X)/3$。 取 $a=E_{12}+E_{23}$、$b=E_{21}+2E_{32}$，则

$$
k=ab-ba=\operatorname{diag}(1,1,-2)
$$

可逆。结合性给 $T(c)=2kc$，所以 $T$ 忠实；正性、单位、存在均成立。 但是 $q(E_{12}E_{21})=1/3\ne1/9=q(E_{12})q(E_{21})$。 可读维数九，不能得到本结论。

#### 反例 6.5：删除读出背景中的一次齐次

在通常 $\mathbb H$ 上取 $q_\beta(x)=|x|^\beta$，$\beta>0$ 且 $\beta\ne2$。 其余全部关系仍成立，$T=4L_k$ 忠实，但原读数不具有二次齐次性。 其平方根不满足所列绝对一次齐次性；所以平方指数仍由读出背景支付；不能由非负、存在与本轮忠实条件单独推出。

#### 反例 6.6：删除原双线性：一个连续例子

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

#### 反例 6.7：原算子等式只能模同一读出核成立

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

八元数反例没有出现负读出或逻辑矛盾；它出现的是本候选所指定合读的盲方向。 要求这个合读忠实仍是选模型的关系输入，并未由“读出非负”单独证明。

本轮的三角恢复使用精确乘性。若只给近似乘性，重复合成的误差可能指数积累， 取第 $n$ 次根后仍留下非一常数；本稿没有把精确结论宣称为任意噪声下的稳定性定理。

<a id="section-7"></a>

## 7　同一合读结构的几何完成：方向、复幅度与正读出

本节只使用主定理已得的

$$
A=\mathcal A/N\cong\mathbb H,\qquad
B(x,y)=\operatorname{Re}(\bar x y),\qquad q(x)=B(x,x),\qquad W=\mathbf 1^\perp.
$$

原单位类、原乘法与原二次读数均保持不变。以下定义及定理不是第二个候选公理。 记 $L_ax=ax$、$R_ax=xa$；算子复合从右向左作用，故 $R_aR_b=R_{ba}$。始终用 $H_J$ 表示复幅度空间，用 $W$ 表示实三维方向空间。

### 7.1　三维叉积、面积与二元关系的三元返回

#### 定义 7.1：同一乘法的对称部分与反对称部分

对 $x,y,z\in W$ 定义

$$
x\times y:=\frac{xy-yx}{2},\qquad
\nu(x,y,z):=B(x\times y,z).
$$

#### 定理 7.2：二元长度、面积与三元返回

对全部 $x,y,z\in W$，有

$$
\begin{aligned}
xy&=-B(x,y)\mathbf 1+x\times y,
\end{aligned}
\tag{7.1}
$$

$$
\begin{aligned}
B(x\times y,x)&=B(x\times y,y)=0,
\end{aligned}
\tag{7.2}
$$

$$
\begin{aligned}
q(x\times y)&=q(x)q(y)-B(x,y)^2,
\end{aligned}
\tag{7.3}
$$

$$
\begin{aligned}
x\times(y\times z)&=B(x,z)y-B(x,y)z,
\end{aligned}
\tag{7.4}
$$

$$
\begin{aligned}
(x\times y)\times z&=B(x,z)y-B(y,z)x.
\end{aligned}
\tag{7.5}
$$

三线性型 $\nu$ 交替；$\times$ 满足 Jacobi 恒等式。

**证明。**

纯方向反交换关系 $xy+yx=-2B(x,y)\mathbf 1$ 给式 (7.1)。 共轭反转乘法次序，故 $x\times y\in W$。 原配对伴随恒等式给

$$
B(xy,x)=q(x)B(y,\mathbf 1)=0,\qquad
B(xy,y)=q(y)B(x,\mathbf 1)=0.
$$

标量部分与 $W$ 正交，得到式 (7.2)。 将乘性二次型分成这两个正交部分，得到

$$
q(x)q(y)=q(xy)=B(x,y)^2+q(x\times y),
$$

即式 (7.3)。 取主定理中的正交单位基 $u,v,w=uv$。原乘法表给 $u\times v=w$、$v\times w=u$、$w\times u=v$，反序取负。 对三个变量作实三线性展开，即得两条三元返回式。 同一张表给 $\nu(u,v,w)=1$ 并在交换任意两槽时变号，故 $\nu$ 交替。 式 (7.4) 的循环和为零，得到 Jacobi 恒等式。

$\square$

这是四元数纯部的标准三维几何；本轮的推进在于先从有限合成界恢复原半范数及内积，再用同一对忠实合读取得该原代数。 R5-022 已从另一种三元返回入口研究同一三维结果。[\[25\]](#ref-baez), [\[26\]](#ref-r522)

#### 推论 7.3：归一化二元二次式

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

#### 命题 7.4：由原乘法导出的各向同性与半角

单位集合 $\mathcal U=\{u\in A:q(u)=1\}$ 是群。 共轭 $\operatorname{Ad}_u(x)=ux\bar u$ 在 $W$ 上保持 $B$ 与 $\times$， 其像恰为 $\operatorname{SO}(W,B)$，核为 $\{\pm\mathbf 1\}$。 若 $n\in W$ 为单位，$u=\cos(\theta/2)\mathbf 1+n\sin(\theta/2)$，则

$$
\operatorname{Ad}_u(x)=\cos\theta\,x
+(1-\cos\theta)B(n,x)n+\sin\theta\,(n\times x).
$$

**证明。**

原乘性和 $u^{-1}=\bar u$ 给群律。 共轭保持乘法、单位、共轭与 $q$，所以保持 $W,B,\times$。 把 $x$ 分成 $B(n,x)n$ 与垂直分量，使用纯部反交换式展开 $ux\bar u$，即得显示公式。每个单位四元数均可写成所示半角形式， 故所得作用是定向正交变换。 反之，三维实定向正交变换必有本征值 $1$：非实本征值成共轭对， 实本征值为 $\pm1$，行列式为一。其固定轴的正交平面上是二维旋转， 因而由显示公式实现。若共轭固定全部纯部，则 $u$ 与三个纯基元交换； 原乘法表迫使 $u$ 为实标量，单位范数再给 $u=\pm\mathbf 1$。

$\square$

### 7.2　忠实合读直接给出左复标量

沿用候选的同一对见证，令

$$
k=[a,b],\qquad e=\frac{k}{\sqrt{q(k)}},\qquad
J=\frac{T_{a,b}}{2\sqrt{q(k)}}=L_e.
$$

前文已得 $q(k)>0$、$e\in W$、$q(e)=1$，以及 $J^2=-I$、$`J^*=-J`$、$`J^*J=I`$。

#### 定义 7.5：内部复标量与幅度比较

以内部平面 $\mathbb C_e=\operatorname{span}_\mathbb R\{\mathbf 1,e\}$ 表示复数，规定

$$
(\alpha+i\beta)x:=\alpha x+\beta Jx,
\qquad h(x,y):=B(x,y)+iB(Jx,y),\qquad H_J=(A,J,h).
$$

这里的 $i$ 从左作用；下文的 $h$ 第一槽共轭线性、第二槽线性。

#### 定理 7.6：复二维幅度与完整复线性算子空间

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

### 7.3　Pauli 关系、自伴锥与 Born 表示

#### 定义 7.7：由原右乘定义观测算子

对 $z\in W$ 定义

$$
\sigma_z:=-JR_z=-L_eR_z.
$$

算子正性定义为 $`F=F^*`$ 且 $h(x,Fx)\ge0$ 对全部幅度 $x$ 成立。

#### 定理 7.8：Pauli 乘法与自伴算子的全部形式

对 $z,t\in W$，有

$$
\begin{aligned}
\sigma_z^*&=\sigma_z,\qquad
\sigma_z\sigma_t=B(z,t)I+i\sigma_{z\times t},
\end{aligned}
\tag{7.6}
$$

$$
\begin{aligned}
\operatorname{Tr}\sigma_z&=0,\qquad
\operatorname{Tr}(\sigma_z\sigma_t)=2B(z,t).
\end{aligned}
\tag{7.7}
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

上一全算子表示中，自伴性等价于 $a=\bar a$、$b=-\bar b$， 所以自伴算子恰为 $sI+\sigma_z$，且表示唯一。 式 (7.6) 给 $\sigma_z^2=q(z)I$；自伴性与迹零给两个本征值 $\pm\sqrt{q(z)}$，包括 $z=0$ 的退化情形。 加上 $sI$ 后逐一判定本征值非负，得到正锥。

$\square$

#### 推论 7.9：同一比较的正锥与可读性

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

#### 定义 7.10：正读出状态与效果

$$
\operatorname{St}(E)=\{\ell:E\to\mathbb R:\ell\text{ 实线性},\
\ell(E_+)\ge0,\ \ell(I)=1\},\qquad
\operatorname{Eff}(E)=\{F:0\le F\le I\}.
$$

这里定义的是数学读出对象；实际准备、装置与这些对象的对应另需给定。

#### 定理 7.11：密度球、效果与二元平方律

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

### 7.4　Hopf 圆纤维与表示轴独立性

#### 定理 7.12：从幅度到方向的准确相位商

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

#### 定理 7.13：见证所选复轴仅改变表示坐标

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

### 7.5　酉门、整体相位与端点未确定的自由度

#### 定理 7.14：全部单比特酉门及其方向作用

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

<a id="section-8"></a>

## 8　线、面积、相位与钟：同一几何的准确分工

本节没有新增核心候选。固定已导出的 $W=1^\perp\cong\mathbb R^3$、内积与取向， 用 $a\cdot b$ 表示 $B(a,b)$。外积空间 $\Lambda^2W$ 带导出的欧氏面积范数， Hodge 星满足 $\star(a\times b)=a\wedge b$。 这些是同一结构的构造；指定哪条历史实际发生，仍是另一个输入。

#### 定理 8.1：单态稳定子面与转向面

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

这与最新 OTF-005 的轴面分解一致。[\[27\]](#ref-otf5) 单态所决定的 $\star n$ 是绕自身方向的生成面； 把该态转往别处所需的面由 $n\wedge\dot n$ 给出。 一个方向不自动确定横向的零相位： 若旋转等变地给每个 $n$ 选非零 $v(n)\perp n$， 绕 $n$ 的半周转动既固定 $n$ 又把 $v(n)$ 变成 $-v(n)$，产生矛盾。

#### 命题 8.2：端点、最短扇形与非唯一的实际门

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

#### 定理 8.3：同一投影张量内的长度与面积

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

这是几何量子力学与投影算子几何的标准结构。[\[28\]](#ref-ashtekar), [\[29\]](#ref-projector), [\[30\]](#ref-berry) 同一 $\mathcal Q$ 包含长度和面积，并不赋予它们相同的物理量纲。

#### 命题 8.4：同一方向路径不能确定唯一 Hamiltonian 或时长

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

### 8.1　正性、正交与“存在”的类型

#### 命题 8.5：两个不同的正交关系

Bloch 方向 $n\cdot m=0$ 当且仅当 $\operatorname{Tr}(P_nP_m)=1/2$； 幅度射线正交当且仅当 $\operatorname{Tr}(P_nP_m)=0$，也即 $m=-n$。 复二维幅度空间不存在三个非零两两正交的幅度。

**证明。**

前两项代入 $\operatorname{Tr}(P_nP_m)=(1+n\cdot m)/2$。 最后，非零正交向量线性无关，而复维数仅为二。 因此三根相互正交的是比较方向，不是三个相互排斥的 qubit 纯态。

$\square$

对指定的二路径基，$\rho_r=(I+r\cdot\sigma)/2$ 的可预测性和干涉可见度可定义为

$$
P=|r_z|,\qquad V=\sqrt{r_x^2+r_y^2},\qquad P^2+V^2=\|r\|^2\le1.
$$

证明只需将 $\rho_r$ 的对角差与非对角条目写出；混合态和基的选择都会改变这些数值。 一个纯态可同时有非零 $P,V$，所以方向本身没有被唯一分成“粒子时刻”与“波时刻”。 与记忆的纠缠和条件读出会进一步改变可访问的干涉关系。[\[31\]](#ref-ding), [\[32\]](#ref-englert), [\[33\]](#ref-siddiqui)

#### 命题 8.6：幅度乘性不能不分类型地施加于全部事件

若对全部事件要求 $p(XY)=p(X)p(Y)$，并要求每个非零正投影都有正读数， 则任何含两个非零正交投影的量子事件代数都不满足该要求。

**证明。**

取 $P,Q\ne0$、$PQ=0$。左边为 $p(0)=0$，右边严格为正，矛盾。

$\square$

因此主候选的 $p$ 是基本幅度比较的读出。 事件正性、过程完全正性与记录 Gram 保持是它们各自的二元、三元相容关系， 不能把不同类型的条件压成同一个无区别的乘法等式。

<a id="section-9"></a>

## 9　态的三元相位：第三个方向保留了哪一份关系

**本区域的输入。**

沿用已经构造的复二维幅度空间 $H_J$， 第一槽共轭线性、第二槽线性的内积 $h$， 三维实纯部 $(W,B,\times)$， 以及

$$
\sigma_a\sigma_b=B(a,b)I+i\sigma_{a\times b},\qquad
 P_a=\frac{I+\sigma_a}{2}\quad(q(a)=1).
$$

以下没有新增基础公理。 为每个单位方向 $a$ 选择一个归一射线代表 $\psi_a$， $P_a=|\psi_a\rangle\langle\psi_a|$。 记

$$
g_{ab}=h(\psi_a,\psi_b),\qquad
 p_{ab}=|g_{ab}|^2=\operatorname{Tr}(P_aP_b),\qquad
 \mathcal B_{abc}=g_{ab}g_{bc}g_{ca}.
\tag{Q21-B1}
$$

#### 定理 9.1：三元幅度的坐标无关公式

对任意三个单位方向 $a,b,c\in W$，

$$
\boxed{\quad
 \mathcal B_{abc}
 =\operatorname{Tr}(P_aP_bP_c)
 =\frac{1+B(a,b)+B(b,c)+B(c,a)+iB(a,b\times c)}4 .
 \quad}
\tag{Q21-B2}
$$

改变各射线代表的相位不改变 $\mathcal B_{abc}$； 交换其中两个方向使其复共轭。

**证明。**

秩一投影的作用为 $P_a x=h(\psi_a,x)\psi_a$。 连续复合三个投影，再取迹，得到 $\operatorname{Tr}(P_aP_bP_c) =h(\psi_a,\psi_b)h(\psi_b,\psi_c)h(\psi_c,\psi_a)$。 另一方面，Pauli 公式给

$$
\operatorname{Tr}I=2,\quad
 \operatorname{Tr}\sigma_a=0,\quad
 \operatorname{Tr}(\sigma_a\sigma_b)=2B(a,b),\quad
 \operatorname{Tr}(\sigma_a\sigma_b\sigma_c)=2iB(a\times b,c).
$$

展开 $(I+\sigma_a)(I+\sigma_b)(I+\sigma_c)/8$ 并逐项取迹， 即得 (Q21-B2)；三重积的循环对称性给 $B(a\times b,c)=B(a,b\times c)$。 若 $\psi_a'=e^{i\alpha_a}\psi_a$， 则 $g_{ab}'=e^{i(\alpha_b-\alpha_a)}g_{ab}$， 三个因子相乘时相位全部相消。 最后，公式中的实部对三个方向对称，而三重积在一次交换下变号。

$\square$

#### 定理 9.2：复二维 Gram 约束与二元数据的剩余歧义

令 $G=(g_{jk})_{j,k\in\{a,b,c\}}$。则

$$
G\ge0,\qquad \operatorname{rank}G\le2,\qquad
 0=\det G
 =1-p_{ab}-p_{bc}-p_{ca}+2\operatorname{Re}\mathcal B_{abc}.
\tag{Q21-B3}
$$

因而

$$
\operatorname{Re}\mathcal B_{abc}
 =\frac{p_{ab}+p_{bc}+p_{ca}-1}{2},\qquad
 |\mathcal B_{abc}|^2=p_{ab}p_{bc}p_{ca},
\tag{Q21-B4}
$$

$$
(\operatorname{Im}\mathcal B_{abc})^2
 =p_{ab}p_{bc}p_{ca}
  -\frac{(p_{ab}+p_{bc}+p_{ca}-1)^2}{4}.
\tag{Q21-B5}
$$

所以三份二元概率确定三元幅度的实部及虚部绝对值， 一般不确定虚部符号。

**证明。**

对任意 $\lambda_a,\lambda_b,\lambda_c\in\mathbb C$，

$$
\sum_{j,k}\overline{\lambda_j}g_{jk}\lambda_k
 =h\!\left(\sum_j\lambda_j\psi_j,\sum_k\lambda_k\psi_k\right)\ge0.
$$

三向量位于复二维空间，故 Gram 矩阵秩不超过二。 展开行列式，三个对角元给 $1$， 三项交换给 $-|g_{ab}|^2-|g_{bc}|^2-|g_{ca}|^2$， 两个三循环给 $g_{ab}g_{bc}g_{ca}+\overline{g_{ab}g_{bc}g_{ca}}$。 这证明 (Q21-B3)，第一条推论随即成立。 取乘积的绝对值平方得到第二式，再用 $|\mathcal B|^2=(\operatorname{Re}\mathcal B)^2+ (\operatorname{Im}\mathcal B)^2$ 即得最后一式。

$\square$

#### 命题 9.3：相同全部二元概率、相反三元方向

取 $(e_1,e_2,e_3)$ 为 $W$ 的定向正交单位基， $e_1\times e_2=e_3$。 两组三元组

$$
(a,b,c)=(e_1,e_2,e_3),\qquad
 (a',b',c')=(e_1,e_2,-e_3)
$$

的三份二元转移概率均为 $1/2$，但

$$
\mathcal B_{abc}=\frac{1+i}{4},\qquad
 \mathcal B_{a'b'c'}=\frac{1-i}{4}.
\tag{Q21-B6}
$$

这里三根 Bloch 轴两两正交，三个射线代表却没有两两正交： 其两两内积绝对值都为 $1/\sqrt2$。

**证明。**

两组三元组的不同方向内积均为零， 故 $p=(1+B)/2=1/2$。 第一组三重积为 $1$，第二组为 $-1$， 代入 (Q21-B2) 即得。 最后一句由 $|g|^2=p=1/2$ 成立。

$\square$

**关系的关系。**

当三个重叠均非零，定义

$$
u_{ab}=\frac{g_{ab}}{|g_{ab}|},\qquad
 \kappa_{abc}=u_{ab}u_{bc}u_{ca}
             =\frac{u_{ab}u_{bc}}{u_{ac}}
             =\frac{\mathcal B_{abc}}{|\mathcal B_{abc}|}.
\tag{Q21-B7}
$$

第二个等号使用 $u_{ca}=u_{ac}^{-1}$。 因此 $\kappa$ 比较的是两条二元比较链： 先 $a\to b\to c$，以及直接 $a\to c$。 它是相位代表无关的三元闭路量； 若某个重叠为零，$\mathcal B$ 仍有定义， 但 $u$ 与 $\kappa$ 在该闭路上不再有定义。

#### 命题 9.4：把第三点设为端点会退化闭路

若 $c=a$ 或 $c=b$，则

$$
\mathcal B_{aba}=\mathcal B_{abb}=p_{ab}\ge0 .
\tag{Q21-B8}
$$

当 $p_{ab}>0$ 时相应 $\kappa=1$； 当 $p_{ab}=0$ 时相应归一相位未定义。 这项端点选择不能确定任意第三方向的闭路不变量。

**证明。**

若 $c=a$，则 $g_{ab}g_{ba}g_{aa}=|g_{ab}|^2$； 若 $c=b$ 同理。 或者用投影幂等性和迹循环性得到同一结果。 固定 $a=e_1,b=e_2$ 后，上一命题的 $c=\pm e_3$ 已给不同闭路不变量， 而两端点及它们的二元概率完全不变。

$\square$

第三点可以是整体内部已有的参考态、记录态或经过确定操作产生的态。 若使用既有叉积，还可在 $a\times b\ne0$ 时明确规定 $`c_*=(a\times b)/\|a\times b\|`$； 这是一个特定的内部构造，不能代替所有实际闭路的第三点。 选择 $c=a$ 或 $c=b$ 是合法的退化选择， 它把相应三元相位压为零，并没有从两个端点唯一恢复一般的闭路面积。 相位、长度或面积公式中仍没有时间参数， 故这些运动学恒等式本身不推出“场等于时间”。

**与过程相关矩阵的严格区别。**

本节 $G$ 是同一复二维空间中纯态代表的 Gram 矩阵， 所以 $\operatorname{rank}G\le2$、三个向量的行列式等于零。 过程节的 $(\gamma_{jk})$ 来自一般内部环境记录； 其秩可以大于二，三阶行列式只须非负。 环境内生不把它自动压成同一个单 qubit， 也不把一般过程三元不等式改成这里的等式。

**外部结果的准确角色。**

Magnot 的 2026 年论文   *Remarks on pairwise comparisons, transition amplitudes, and qubit states*   以既定的 $\mathbb C^2$ qubit 为起点， 讨论复振幅、转移概率、相位比较与 Bargmann 三角不变量之间的对应， 以及 Gram 正性与秩约束。 它为本节提供非常直接的研究对应， 没有从不含量子结构的前件完成量子力学重建。 上面的公式均由本轮已声明的 Pauli 和 Hilbert 结构逐项证明。[\[21\]](#ref-magnot)

<a id="section-10"></a>

## 10　存在、面积与最小内部表示

本节继承项目 R5-006 的纤维精化、正核与 Schur 秩判据，[\[2\]](#ref-r5006) 不把这些既有结果另计为本轮新发现。 本轮将它们与三种不同的量子面积、最新有限获取稿的线性特征反例连接， 以检验“表达存在必然增加维数”的准确范围。

**输入：** 已取得的复内积结构；或另行给定的 Hermitian 关系核与全部有限正性。 **输出：** 最小关系表示、面积与独立余量、严格增秩判据。 此分支不单独产生复数、Born 接口、物理复合律或时间律。

### 10.1　面积的三个类型

#### 定义 10.1：振幅面积

内积 $h$ 对第二变量复线性，$q(x)=h(x,x)$。 定义复 Gram 面积与实 Gram 面积

$$
\mathcal S_{\mathbb C}(x,y)^2=q(x)q(y)-|h(x,y)|^2,\qquad
 \mathcal S_{\mathbb R}(x,y)^2=q(x)q(y)-(\operatorname{Re}h(x,y))^2.
$$

前者是复外积的平方范数；后者把同一振幅空间视为实内积空间。

#### 定理 10.2：面积读取旧线之外的成分

若 $x\ne0$，令

$$
y_\parallel=\frac{h(x,y)}{q(x)}\cdot x,\qquad
 y_\perp=y-y_\parallel.
$$

这里 $\alpha\cdot x$ 是 $J$ 定义的左复标量作用，不能改读为四元数右乘。 则

$$
h(x,y_\perp)=0,\qquad
 q(y)=\frac{|h(x,y)|^2}{q(x)}+q(y_\perp),\qquad
 \mathcal S_{\mathbb C}(x,y)^2=q(x)q(y_\perp).
$$

特别地，$\mathcal S_{\mathbb C}(x,y)=0$ 当且仅当 $x,y$ 复线性相关。 它不等价于 $q(x)=0$ 或 $q(y)=0$。

**证明。**

第二变量线性给 $h(x,y_\parallel)=h(x,y)$，故得到正交分解。 展开 $q(y_\parallel+y_\perp)$，交叉项为零， 且 $q(y_\parallel)=|h(x,y)|^2/q(x)$。 代回定义即得。若 $x=0$，面积本来为零；若 $x\ne0$， 正定性使零面积等价于 $y_\perp=0$。

$\square$

#### 命题 10.3：实、复与 Bloch 面积不能互换

有

$$
\mathcal S_{\mathbb R}(x,y)^2
 =\mathcal S_{\mathbb C}(x,y)^2+(\operatorname{Im}h(x,y))^2.
$$

单位振幅 $x$ 与 $ix$ 的实面积为 $1$，复面积为 $0$， 但它们代表同一量子射线。 对单位量子比特振幅 $x,y$，对应 Bloch 方向为 $n,m$， 记 $p=|h(x,y)|^2$，则

$$
\mathcal S_{\mathbb C}(x,y)^2=1-p=\frac{1-n\cdot m}{2},
 \qquad
 \lVert n\wedge m\rVert^2=4p(1-p).
$$

**证明。**

第一式由 $|h|^2=(\operatorname{Re}h)^2+(\operatorname{Im}h)^2$ 得到。 $h(x,ix)=i$，而 $ix$ 与 $x$ 的秩一投影相同。 最后使用 $p=(1+n\cdot m)/2$ 与 $\lVert n\wedge m\rVert^2=1-(n\cdot m)^2$。

$\square$

取 $x=y\ne0$，已有非零存在而零复面积。 若要求不同纯态，可取正交振幅；它们的 Bloch 方向互反， 因此 Bloch 面积为零，而复振幅面积最大。 故任何“面积即存在”的定义首先必须说明对象类型与所用面积； 上述几种既有面积均不与单元的非零存在等价。

#### 命题 10.4：中央响应面积的 Pauli 分支

令 $n,m\in\mathbb R^3$，$A=n\cdot\sigma$、$B=m\cdot\sigma$，并置

$$
A\circ B=(AB+BA)/2,\qquad D_{\rm P}=i(AB-BA)/2.
$$

则

$$
D_{\rm P}=-(n\times m)\cdot\sigma,\qquad
 D_{\rm P}^2=A^2B^2-(A\circ B)^2
 =\bigl(\lVert n\rVert^2\lVert m\rVert^2-(n\cdot m)^2\bigr)I.
$$

**证明。**

Pauli 乘法为 $(n\cdot\sigma)(m\cdot\sigma) =(n\cdot m)I+i(n\times m)\cdot\sigma$。 交换 $n,m$，分别相加、相减，再用 $(v\cdot\sigma)^2=\lVert v\rVert^2I$，即得全部等式。

$\square$

这是项目中央响应面积在明确矩阵模型中的实现； 此处采用 $A\circ B-iD_{\rm P}=AB$ 的项目乘法恢复约定。 响应 $D_{\rm P}=0$ 不要求 $A=0$ 或 $B=0$。 新稿的较弱 JC 载体证明另有完整的源条件，不能从本例反向推广到任意未知响应。

### 10.2　无需先指定外在载体的最小 Gram 实现

#### 定理 10.5：关系决定最小生成空间

给定 $m$ 阶 Hermitian 正半定矩阵 $G$，令

$$
\mathcal H_G=\mathbb C^m/\ker G,\qquad
 \langle[c],[d]\rangle_G=c^*Gd.
$$

这是正定内积空间，$v_i=[e_i]$ 满足

$$
\langle v_i,v_j\rangle_G=G_{ij},\qquad
 \dim_{\mathbb C}\mathcal H_G=\operatorname{rank}G.
$$

任意具有相同 Gram 数据的向量族 $w_i$，均给出唯一的标签保持酉同构

$$
[c]\longmapsto\sum_i c_iw_i:
 \mathcal H_G\longrightarrow\operatorname{span}\{w_i\}.
$$

**证明。**

正半定性给 $`c^*Gc=0\iff Gc=0`$，例如用 $G$ 的正平方根即可验证。 所以配对与代表元无关，且商上正定。 标准基的像张成商空间，秩–零度公式给维数。 另一实现的组合范数恰为 $`\lVert\sum c_iw_i\rVert^2=c^*Gc`$， 故线性映射的零核恰为 $\ker G$，能下降为等距映射。 其像按定义为全部张成空间；标签像已确定，所以唯一。

$\square$

对无限标签集，先在有限支撑自由空间上使用同一正核， 商去零长度部分，再按需要完成，即得相应核表示。 所有有限正性是明确输入；它不是仅检查最初标签的任意两两正性。 这是成熟的正核表示构造，参见 Aronszajn 的原论文[\[34\]](#ref-q022-aronszajn)。

#### 命题 10.6：过程必须保持同一零核

系数线性操作 $M:\mathbb C^m\to\mathbb C^m$ 下降为 $\mathcal H_G$ 上操作， 当且仅当 $M\ker G\subseteq\ker G$。 若 $`M^*GM=G`$，则它保持全部二元关系，并自动下降为酉操作。 若 $M,N$ 都保持关系，则 $MN$ 也保持关系。

**证明。**

下降等价于 $c-d\in\ker G\Rightarrow M(c-d)\in\ker G$。 矩阵等式给 $`\langle Mc,Md\rangle_G=c^*M^*GMd=c^*Gd`$， 从而零核条件自动成立，商映射为等距自映射。 商空间有限维，所以等距自映射满射。 最后 $`(MN)^*G(MN)=N^*(M^*GM)N=N^*GN=G`$。

$\square$

### 10.3　最小增维判据及其信息边界

#### 定理 10.7：新关系的最小独立余量

设旧表 $G\ge0$，新关系向量为 $g\in\mathbb C^m$，新元平方读出为 $s\ge0$。 则

$$
\widetilde G=\begin{pmatrix}G&g\\g^*&s\end{pmatrix}\ge0
 \iff
 g\in\operatorname{ran}G,\quad
 \delta=s-g^*G^+g\ge0.
$$

成立时

$$
\operatorname{rank}\widetilde G=\operatorname{rank}G+\mathbf1_{\{\delta>0\}}.
$$

在最小旧空间中，新增元可以取成

$$
v_{\rm new}=[G^+g]+\sqrt{\delta}\,e_\perp,
$$

其中 $\delta=0$ 时不加入 $e_\perp$， $\delta>0$ 时只需一个正交单位元。

**证明。**

若 $z\in\ker G$，在 $(tz,1)$ 上的块二次型为 $`s+2\operatorname{Re}(\bar t z^*g)`$。 若 $`z^*g\ne0`$，选相位并放大 $t$ 即得负值。 故 $g\perp\ker G$，即 $g\in\operatorname{ran}G$。 置 $y=G^+g$，有 $Gy=g$，并且

$$
\binom{x}{t}^{\!*}\widetilde G\binom{x}{t}
 =(x+yt)^*G(x+yt)+\delta|t|^2.
$$

取 $x=-yt$ 得必要性；同式给充分性。 可逆变量替换将矩阵合同到 $G\oplus[\delta]$，给出秩式。 实现公式中的旧配对为 $GG^+g=g$，范数为 $`g^*G^+g+\delta=s`$，故精确保持全部数据。

$\square$

此判据与 R5-006 §4.1 一致。 增维说的是 *最小生成线性空间* ； 若整体已经有尚未使用的正交方向，就可在整体内部使用它。 当旧振幅已张成 $\mathbb C^2$，任何新的量子比特振幅仍有 $\delta=0$， 即便它是此前未列出的不同纯态。

若旧向量独立，则 $\det\widetilde G=(\det G)\delta$； 只有一个旧元时，恰是 $\mathcal S_\mathbb C(x,y)^2=q(x)\delta$。 所以面积可以读取相对独立余量，而不等同于绝对存在。

#### 命题 10.8：线性残差不等于新增信息

令 $X$ 均匀分布于 $[-1,1]$，在实 $L^2$ 中取

$$
V=\operatorname{span}\{1,X\},\qquad S=L^2(\sigma(X)),\qquad z=X^2.
$$

则

$$
\operatorname{dist}(z,V)^2=\frac4{45}>0,\qquad
 \operatorname{dist}(z,S)^2=0.
$$

**证明。**

有 $\mathbb E X=\mathbb E X^3=0$、 $\mathbb E X^2=1/3$、 $\mathbb E X^4=1/5$。 故对实数 $a,b$，

$$
\mathbb E(X^2-a-bX)^2
 =(a-\tfrac13)^2+\frac{b^2}{3}+\frac4{45}.
$$

最小值为 $4/45$。 另一方面 $X^2$ 是旧读口 $X$ 的确定函数，属于 $S$。

$\square$

在三个标签 $1,X,X^2$ 上，关系表精确为

$$
G_3=\begin{pmatrix}
1&0&1/3\\0&1/3&0\\1/3&0&1/5
\end{pmatrix},\qquad
\det G_3=\frac4{135}>0.
$$

旧 $G=\operatorname{diag}(1,1/3)$、新 $g=(1/3,0)^T$、$s=1/5$，故 $\delta=1/5-1/9=4/45$。 这是一个明确的二维到三维最小线性提升，仍没有超出旧读口 $X$ 的信息。

该反例来自本次项目有限获取稿 §12.2。[\[5\]](#ref-energy22) 它严格说明：正的线性余量迫使扩充指定特征空间， 却不迫使增加完整旧读口的信息。 一般地，目标 $f:X\to Y$ 能由旧读口 $q:X\to S$ 恢复， 当且仅当 $f$ 在每个 $q$-纤维上为常数； 存在唯一 $\bar f:q(X)\to Y$ 使 $f=\bar f\circ q$； 直接定义 $\bar f(q(x))=f(x)$ 即证明其必要充分性。 这与 Gram 秩判据属于不同的类型。

<a id="section-11"></a>

## 11　有限量子理论的完整数学完成及实际接口

核心候选选择了一个复二维幅度块。下面先定义其有限数学完成， 再证明状态、概率、过程、记录和连续可逆演化的标准形式。 数学完成中的对象可由内部有限构造得到；某个原实际世界是否供应全部这些对象，是另一个命题。

### 11.1　本区域的输入与输出

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

这些接口不计入本轮六组核心输入，也没有被它们全部证明。 项目 C139 对完整参考递归已有专门的来源条件与误差版本，正说明此处不能只写“再加入一个环境”就略过实际供应。[\[35\]](#ref-c139cp)

#### 定理 11.1：有限矩阵代数完成

上面的 $\mathsf{QFin}$ 恰为全部有限直和复矩阵代数。 若原联合是非零复含幺结合 $`*`$-代数，并有两个同复中心的可交换含幺 $`*`$-嵌入 $M_m(\mathbb C),M_n(\mathbb C)$， 且它们的乘积线性张成全部联合代数，则联合代数同构于 $M_{mn}(\mathbb C)$。

**证明。**

$M_2^{\otimes k}=M_{2^k}$。对任意 $d$，选 $2^k\ge d$，取秩 $d$ 投影的角便得 $M_d$； 有限直和给全部显示代数。反向，张量、直和与投影角都留在这一类中。 对于原联合，映射 $A\otimes B\mapsto\iota_A(A)\iota_B(B)$ 为含幺 $`*`$-同态且由张成条件满射。 $M_{mn}$ 没有非平凡双边理想：任意非零理想元素有一个非零矩阵条目， 左右乘矩阵单位便得到所有矩阵单位。因此该同态核只能是零或全部；单位不被消掉，故核为零。

$\square$

#### 定理 11.2：密度、观测与平方律

对 $\mathcal M=\bigoplus_jM_{d_j}(\mathbb C)$，每个归一正线性泛函唯一为

$$
\omega(X)=\sum_j\operatorname{Tr}(\rho_jX_j),\quad
\rho_j\ge0,\quad\sum_j\operatorname{Tr}\rho_j=1.
$$

单块的纯态为秩一投影；一般纯态只占一个块且在该块秩一。 POVM $E_k\ge0,\sum_kE_k=I$ 给归一概率 $p_k=\omega(E_k)$。 对正交投影测量和纯态，$p_k=\|P_k\psi\|^2$。

**证明。**

每块的非退化迹配对给唯一自伴 $\rho_j$。在所有向量秩一投影上非负等价于各 $\rho_j\ge0$， 单位评价给总迹一。反向由正算子迹乘积非负成立。 若有两个正本征权重，可作一正一负的小扰动并保持归一，故不是极点； 若仅一个权重为一，其秩一支撑不能非平凡分解为正态凸组合，故为极点。 POVM 式的非负与归一直接求和得到；纯投影概率由 $\operatorname{Tr}(|\psi\rangle\langle\psi|P_k)=\langle\psi,P_k\psi\rangle=\|P_k\psi\|^2$ 得出。

$\square$

#### 定理 11.3：锐读出的共同相容性有确定条件

对两个正交投影 $P,Q$，存在四个正效果 $G_{ij}$、$i,j\in\{0,1\}$， 总和为 $I$ 且满足

$$
G_{10}+G_{11}=P,\qquad G_{01}+G_{11}=Q,
$$

当且仅当 $PQ=QP$。

**证明。**

若 $0\le A\le P$，则对 $v\in\ker P$ 有 $0\le\langle v,Av\rangle\le0$；正平方根给 $Av=0$， 故 $PA=AP=A$。 于是 $PG_{11}=G_{11}=G_{11}P$； $G_{01}\le I-P$ 又给 $PG_{01}=G_{01}P=0$。 由 $Q=G_{11}+G_{01}$ 得 $PQ=QP=G_{11}$。 反向，若 $P,Q$ 交换，取 $G_{11}=PQ$、$G_{10}=P(I-Q)$、 $G_{01}=(I-P)Q$、$G_{00}=(I-P)(I-Q)$； 这些都是正投影且有要求的边缘和。

$\square$

所以允许更大的联合系统，并不自动使原来的全部锐读出共同可测。 替换原效果或降低读出精度，可以定义另一组相容任务；原投影是否相容仍由上述等式判定。 这里的等价仅针对锐投影，不把一般 POVM 的非交换直接等同于不可联合测量。

#### 定理 11.4：递归二元参考充分恢复完全正性

对复线性 $\Phi:M_d\to M_e$，以下三项等价：

1.  $\mathsf P_{\rm ref}(\Phi)$ 成立；

2.  $C_\Phi=(\Phi\otimes\operatorname{id}_d)(|\Gamma\rangle\langle\Gamma|)\ge0$， 其中 $|\Gamma\rangle=\sum_{i=1}^d|i\rangle|i\rangle$；

3.  存在有限矩阵族 $K_\mu$，使 $`\Phi(X)=\sum_\mu K_\mu XK_\mu^*`$。

而 $\Phi$ 迹不增、保迹，分别等价于 $`\sum_\mu K_\mu^*K_\mu\le I`$、$=I$。

**证明。**

选 $2^n\ge d$，将 $\mathbb C^d$ 等距嵌入参考 $\mathbb C^{2^n}$。 对嵌入后的 $|\Gamma\rangle\langle\Gamma|$ 用第一项，再压回该参考子空间，得到第二项。 将正矩阵 $C_\Phi$ 分解成有限秩一和 $\sum_\mu|v_\mu\rangle\langle v_\mu|$， 按输出、输入两个指标把 $v_\mu$ 重排成矩阵 $K_\mu$。 比较 $C_\Phi$ 中每个输入矩阵单位的系数即得第三项。 反向，任意参考上的 $`\sum_\mu(K_\mu\otimes I)X(K_\mu^*\otimes I)`$ 都保持正性。 最后 $`\operatorname{Tr}\Phi(X)=\operatorname{Tr}[X\sum_\mu K_\mu^*K_\mu]`$， 在全部正 $X$ 上比较迹即得相应算子不等式或等式。

$\square$

这是 Choi–Kraus 表示的完整有限证明，其标准等价式见 Watrous 定理 2.22。[\[36\]](#ref-watrous) 对直和源 $\bigoplus_iM_{d_i}$ 与目标 $\bigoplus_jM_{e_j}$，完全正过程恰为

$$
\Phi((X_i)_i)_j=\sum_{i,\mu}K_{ji\mu}X_iK_{ji\mu}^*,
\qquad K_{ji\mu}:\mathbb C^{d_i}\to\mathbb C^{e_j}.
$$

证明只需将输入块嵌入、输出块压缩与原箭头复合，对每个分量应用单块定理； 反向是这些完全正分量的有限和。 保迹条件为每个 $i$ 的 $`\sum_{j,\mu}K_{ji\mu}^*K_{ji\mu}=I_{d_i}`$， 迹不增将等号换成 $\le$。 只要求局部正性不够：转置 $T$ 保正，但 $(T\otimes\operatorname{id})(|\Gamma\rangle\langle\Gamma|)$ 是交换算子， 在反对称二体向量上取负本征值。二元参考的递归量词不能删除。

#### 定理 11.5：内部仪器与记录的酉实现

若分支 $`\Phi_k(X)=\sum_\mu K_{k\mu}XK_{k\mu}^*`$ 满足 $`\sum_{k,\mu}K_{k\mu}^*K_{k\mu}=I`$，则

$$
V\psi=\sum_{k,\mu}K_{k\mu}\psi\otimes|k,\mu\rangle
$$

是等距映射；读取内部记录投影 $Q_k=\sum_\mu|k,\mu\rangle\langle k,\mu|$ 并取环境偏迹，恰得到原分支 $\Phi_k$。 该等距映射在适当有限扩张中可延为酉算子。

**证明。**

内积展开给 $`V^*V=I`$。展开 $`VX V^*`$，记录投影保留同一 $k$， 偏迹只保留相同 $\mu$，得到给定 Kraus 和。 把输入与输出放进一个足够大的等维空间，补全等距像的正交基，就得到酉扩张。

$\square$

#### 定理 11.6：理想投影更新的准确条件

设完全正分支 $\Phi$ 的效果为投影 $P$，即 $`\sum K_\mu^*K_\mu=P`$， 并且 $\Phi$ 固定每个支撑在 $P$ 内的归一态。 则 $\Phi(X)=PXP$。成功概率非零时，条件态为 $P\rho P/\operatorname{Tr}(\rho P)$。

**证明。**

若 $P=0$，则全部 $K_\mu=0$，结论直接成立；以下设 $P\ne0$。 对 $x\in\ker P$，$\sum\|K_\mu x\|^2=0$，故 $K_\mu=K_\mu P$。 对每个 $x\in\operatorname{im}P$ 的秩一态，输出仍为该秩一态， 正和的每一项必须留在同一条线，故 $K_\mu x$ 与 $x$ 平行。 线性算子若保持一个空间的每条线，则在其上为标量：用两个独立向量及其和即可证明。 所以 $K_\mu=c_\mu P$，效果式给 $\sum|c_\mu|^2=1$，遂得结论。

$\square$

只固定某组基态不够：在 $P$ 内退相干的通道会破坏其叠加态，仍可保持那些基态。

#### 定理 11.7：连续可逆过程给薛定谔形式

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

#### 命题 11.8：标准结构的若干直接后果

在该数学完成中，局部保迹过程不改变另一方边缘态； 任意两个自伴量满足 Robertson 不等式；标准二体纯态可以纠缠。

**证明。**

局部无信号性由 $\operatorname{Tr}_B[(\operatorname{id}\otimes\Phi)(\rho_{AB})]=\operatorname{Tr}_B\rho_{AB}$， 将 Kraus 和与 $`\sum K^*K=I`$ 代入即可。 对 $`\langle X,Y\rangle_\rho=\operatorname{Tr}(\rho X^*Y)`$ 用 Cauchy–Schwarz， 取中心化自伴 $\Delta A,\Delta B$，便得 $(\Delta_\rho A)^2(\Delta_\rho B)^2\ge|\operatorname{Tr}(\rho[A,B])/(2i)|^2$。 最后 $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$ 的约化态为 $I/2$， 不可能是纯乘积；其秩一投影也不能是乘积态的凸组合，因为正和的各项必须落在同一条射线上。

$\square$

这些结论均来自明确的有限完成。若只供应可分离联合锥，也能保留全部局域 qubit， 却不会自动得到纠缠准备。无限维位置、动量、场方程与引力仍未由本候选恢复； 例如有限矩阵不可能满足 $[X,P]=i\hbar I$、$\hbar\ne0$，因为取迹立即矛盾。

<a id="section-12"></a>

## 12　把控制器和过程也放回关系中：相干拼接的全部自由度

**本区域的输入。**

本节继承有限维复量子态、Born 配对和张量复合的数学接口。 取有限维复 Hilbert 空间 $H=\mathbb C^d$、 控制空间 $C=\mathbb C^n$ 及其正交标签 $|1\rangle,\ldots,|n\rangle$。 给定 $n$ 个完全正保迹映射 $\Phi_j:\mathcal L(H)\to\mathcal L(H)$。 完整过程要求为完全正保迹映射 $\Lambda:\mathcal L(C\otimes H)\to\mathcal L(C\otimes H)$， 并满足标签保持条件

$$
\Lambda(|j\rangle\langle j|\otimes X)
 =|j\rangle\langle j|\otimes\Phi_j(X)
 \qquad(j=1,\ldots,n;\ X\in\mathcal L(H)).
\tag{Q21-C1}
$$

这些是本区域的接口前件；它们并不由一个 qubit 的球面图像单独推出。 控制、记录和相位参考均可作为有限附属系统纳入同一整体， 但该整体不被要求仍具有单个 qubit 的四维实振幅空间。

**与项目已有结论的关系。**

项目 `RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md` 第 335 节已指出：普通通道的相等不保证相干控制后的相等。 相关 tester 和后继闭包陈述，应采用第 396 节及第 400 节修订后的条件： 过程差须满足合法归一化约束，实际 tester 还须与该可实现差有非零配对。 下面把这一存在性边界补成全部相容过程的参数分类。 有限维通道拼接的基本非唯一性及其分类属于已知结果， 不是本轮新基础公理；参见 Åberg 及 Vanrietvelde–Chiribella。 本轮的作用是给出可直接核算的接口、证明和删项反例。[\[37\]](#ref-waveprocess), [\[22\]](#ref-aberg), [\[23\]](#ref-vanrietvelde)

### 12.1　二元过程的完整正性条件

**定义。**

采用输出在前、输入在后的 Choi 约定：

$$
J(\Psi)=\sum_{a,b=1}^{d}\Psi(|a\rangle\langle b|)
                       \otimes|a\rangle\langle b|,
 \qquad
 |A\rangle\!\rangle=\sum_a A|a\rangle\otimes|a\rangle .
$$

这里 $\Psi$ 可以是一般复线性映射，并不要求它单独完全正。 线性映射与 Choi 矩阵一一对应，因为矩阵的输入侧第 $(a,b)$ 块 正好是 $\Psi(|a\rangle\langle b|)$。

前面的递归参考定理已证明 Choi–Kraus 等价。 以下复用该定理；一般线性映射的交叉 Choi 块不要求单独为正。

#### 定理 12.1：全部标签保持拼接

满足 (Q21-C1) 的所有完全正保迹映射，恰好由一个正块矩阵

$$
\mathcal J=(J_{jk})_{j,k=1}^n\ge0,\qquad
 J_{jj}=J(\Phi_j)
\tag{Q21-C2}
$$

参数化。若 $\Gamma_{jk}$ 是 $J_{jk}$ 唯一确定的线性映射，则

$$
\Lambda\left(\sum_{j,k}|j\rangle\langle k|\otimes X_{jk}\right)
 =\sum_{j,k}|j\rangle\langle k|\otimes\Gamma_{jk}(X_{jk}).
\tag{Q21-C3}
$$

等价地，存在共同索引的 Kraus 族 $A_{j\mu}$，使

$$
\Phi_j(X)=\sum_\mu A_{j\mu}X A_{j\mu}^\dagger,\qquad
 \Gamma_{jk}(X)=\sum_\mu A_{j\mu}X A_{k\mu}^\dagger.
\tag{Q21-C4}
$$

其中 $J_{kj}=J_{jk}^\dagger$ 等价于 $\Gamma_{kj}(X)=[\Gamma_{jk}(X^\dagger)]^\dagger$。

**证明。**

先设 $\Lambda$ 完全正，写 Kraus 族 $K_\mu$。 记 $P_j=|j\rangle\langle j|\otimes I$。 对任意 $\psi\in H$ 和 $\ell\ne j$， 标签保持给出

$$
0=\operatorname{Tr}\!\left[
 P_\ell\Lambda(|j,\psi\rangle\langle j,\psi|)\right]
 =\sum_\mu\|P_\ell K_\mu|j,\psi\rangle\|^2 .
$$

各项非负，故每个 $K_\mu$ 都保持每个标签子空间。 于是 $K_\mu=\sum_j|j\rangle\langle j|\otimes A_{j\mu}$。 展开 $K_\mu X K_\mu^\dagger$ 得 (Q21-C3)–(Q21-C4)。 各分支保迹给 $\sum_\mu A_{j\mu}^\dagger A_{j\mu}=I$， 因而 $\sum_\mu K_\mu^\dagger K_\mu=I$。

由向量化恒等式， $J_{jk}=\sum_\mu|A_{j\mu}\rangle\!\rangle \langle\!\langle A_{k\mu}|$， 所以 $\mathcal J\ge0$。 反之，将任意满足 (Q21-C2) 的正块矩阵分解为 $\mathcal J=\sum_\mu v_\mu v_\mu^\dagger$， 把每个块分量 $v_{j\mu}$ 写成 $|A_{j\mu}\rangle\!\rangle$。 对角块条件给各 $\Phi_j$ 的 Kraus 表示与保迹条件。 以上述块对角 $K_\mu$ 构造 $\Lambda$，立即完全正、保迹且保持标签。 Choi 对应的一一性给参数化的一一性。

$\square$

#### 引理 12.2：两个正块之间只剩一个收缩

设 $A,B\ge0$ 是有限维正矩阵。则

$$
\begin{pmatrix}A&Z\\Z^\dagger&B\end{pmatrix}\ge0
 \quad\Longleftrightarrow\quad
 Z=A^{1/2}K B^{1/2},\qquad \|K\|\le1 ,
\tag{Q21-C5}
$$

其中 $K:\operatorname{supp}B\to\operatorname{supp}A$。 在这两个支撑空间间 $K$ 唯一，零延拓仍是收缩。 在支撑之外作其他扩展虽不改变 $Z$，若要求扩展后仍为收缩， 仍须另满足其算子范数不超过一。

**证明。**

记左侧正矩阵为 $M$。 若 $x\in\ker A$，则 $(x,0)^\dagger M(x,0)=0$。 对正矩阵，$v^\dagger Mv=\|M^{1/2}v\|^2=0$ 蕴含 $Mv=0$， 故 $Z^\dagger x=0$。同理 $Zy=0$ 对所有 $y\in\ker B$ 成立。 因此 $Z$ 只连接所列支撑空间。 在支撑上 $A,B$ 可逆，作可逆合同变换得到

$$
\begin{pmatrix}A^{-1/2}&0\\0&B^{-1/2}\end{pmatrix}
 M
 \begin{pmatrix}A^{-1/2}&0\\0&B^{-1/2}\end{pmatrix}
 =\begin{pmatrix}I&K\\K^\dagger&I\end{pmatrix},
 \qquad K=A^{-1/2}ZB^{-1/2}.
$$

最后一个矩阵的二次型为

$$
\|x+Ky\|^2+\|y\|^2-\|Ky\|^2 .
$$

它对所有 $x,y$ 非负，当且仅当 $\|Ky\|\le\|y\|$。 反向将该正矩阵与 $\operatorname{diag}(A^{1/2},B^{1/2})$ 作合同变换即得结论。唯一性来自支撑上的可逆性。

$\square$

#### 推论 12.3：二元过程的精确缺项

对两个已给分支通道 $\Phi_0,\Phi_1$，全部允许交叉映射 $\Gamma$ 恰好满足

$$
\boxed{\;
 J(\Gamma)=J(\Phi_0)^{1/2}KJ(\Phi_1)^{1/2},\qquad
 \|K\|\le1 .
 \;}
\tag{Q21-C6}
$$

两个普通通道固定了两个对角块，未固定这个收缩 $K$。 将 $K$ 包入内部实现后，完整过程才有确定的相干输出。

**证明。**

在全部拼接定理中取 $n=2$，应用上一引理。

$\square$

### 12.2　记录内生：酉分支的相关矩阵

#### 定理 12.4：酉分支的全部相干拼接

若各分支为酉通道 $\Phi_j(X)=U_jXU_j^\dagger$，则全部允许拼接恰好具有形式

$$
\Gamma_{jk}(X)=\gamma_{jk}U_j XU_k^\dagger,\qquad
 G=(\gamma_{jk})\ge0,\qquad \gamma_{jj}=1 .
\tag{Q21-C7}
$$

每个这样的 $G$ 都有一个完全内生的有限环境实现

$$
V(|j\rangle\otimes\psi)
 =|j\rangle\otimes U_j\psi\otimes e_j,\qquad
 \langle e_j,e_j\rangle=1,\qquad
 \gamma_{jk}=\langle e_k,e_j\rangle.
\tag{Q21-C8}
$$

这里内积采用物理 convention，即对第一变量共轭线性。 所需最小纯环境维数为 $\operatorname{rank}G$。

**证明。**

$J(\Phi_j)=|U_j\rangle\!\rangle\langle\!\langle U_j|$ 为秩一矩阵。 正块矩阵的零空间传播性质说明：$J_{jk}$ 的像包含于 $\operatorname{span}|U_j\rangle\!\rangle$， 其伴随的像包含于 $\operatorname{span}|U_k\rangle\!\rangle$。 故 $J_{jk}=\gamma_{jk}|U_j\rangle\!\rangle \langle\!\langle U_k|$。 各 $|U_j\rangle\!\rangle$ 的范数为 $\sqrt d$； 它们放在不同标签块后互相正交。 因此 $\mathcal J\ge0$ 等价于 $G\ge0$，而对角条件等价于 $\gamma_{jj}=1$。 反向由拼接定理成立。

将 $G$ 分解成 $G=BB^\dagger$，其中 $B$ 只有 $r=\operatorname{rank}G$ 列。 取 $e_j=\sum_{\alpha=1}^rB_{j\alpha}|\alpha\rangle$， 即有 $\langle e_k,e_j\rangle=\gamma_{jk}$ 和 $\|e_j\|=1$。 不同控制标签彼此正交，所以 (Q21-C8) 的 $V$ 保持全部内积； 对环境取偏迹得到 (Q21-C7)。 反之，完整通道的 Choi 矩阵是 $\mathcal J$ 在 输出标签等于输入标签子空间中的等距嵌入， 而前述秩一块分解给 $\operatorname{rank}J(\Lambda)=\operatorname{rank}\mathcal J =\operatorname{rank}G$。 任意维数为 $m$ 的纯环境等距实现， 沿环境正交基展开即产生至多 $m$ 个 Kraus 算子， 故其 Choi 秩不超过 $m$。 所以任意纯环境实现都需 $m\ge r$， 所构造的 $r$ 维环境达到下界。

$\square$

#### 推论 12.5：两分支的圆盘、相位规范与实际读出

当 $n=2$，全部自由度是一个复数 $\gamma=\gamma_{01}$，满足 $|\gamma|\le1$。 取控制初态 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$， 目标初态 $\rho$，以及 $|+_\phi\rangle=(|0\rangle+e^{i\phi}|1\rangle)/\sqrt2$， 则

$$
p_+(\phi)=\frac12\left[
 1+\operatorname{Re}
 \left(e^{i\phi}\gamma\operatorname{Tr}
              (U_0\rho U_1^\dagger)\right)\right].
\tag{Q21-C9}
$$

酉矩阵代表改为 $U_j'=e^{i\alpha_j}U_j$ 时， 同一个完整过程要求 $\gamma'=e^{-i(\alpha_0-\alpha_1)}\gamma$。 因此普通分支的整体相位不会自动成为可观测量； 可观测量是完整交叉映射 $\Gamma$。

**证明。**

$G=\left(\begin{smallmatrix}1&\gamma\\ \bar\gamma&1\end{smallmatrix}\right)\ge0$ 当且仅当 $1-|\gamma|^2\ge0$。 目标取偏迹后，控制态为 $\frac12\left(\begin{smallmatrix}1&z\\\bar z&1\end{smallmatrix}\right)$， $z=\gamma\operatorname{Tr}(U_0\rho U_1^\dagger)$。 与 $|+_\phi\rangle\langle+_\phi|$ 配对即得公式。 最后直接要求 $\gamma'U_0'XU_1'^\dagger=\gamma U_0 XU_1^\dagger$ 即得规范变换。

$\square$

**相位参考也留在公式内。**

式 (Q21-C9) 中的 $\phi$ 是控制效果的标定参数， 不能在声称完全内生时把它当成无代价的外部旋钮。 若参考 $R$ 取有限正交标签 $|\ell\rangle$，以 $\xi_R=\sum_\ell q_\ell|\ell\rangle\langle\ell|$ 编码实际可用相位 $\phi_\ell$，定义整体效果

$$
F_+=\sum_\ell|\ell\rangle\langle\ell|_R
                  \otimes|+_{\phi_\ell}\rangle\langle+_{\phi_\ell}|_C .
$$

在这一独立参考制备模型内，实际概率正好是

$$
\operatorname{Tr}[F_+(\xi_R\otimes\rho_C)]
 =\frac12\left[1+\operatorname{Re}(\eta z)\right],
 \qquad \eta=\sum_\ell q_\ell e^{i\phi_\ell}.
\tag{Q21-C10}
$$

这是有限维 Born 配对的直接展开，不另外假定一个外部观察者。 若 $R$ 已与控制、目标或源相关，必须使用实际联合态 $\rho_{RCT}$，不能继续把它替换成 $\xi_R\otimes\rho_{CT}$。 本模型没有宣称从任意初态免费产生相位参考，也没有预设能量守恒的 $U(1)$ 协变操作限制；若另加该限制，需要另列资源前件。

### 12.3　三元不是三个独立的二元

以下四分支反例在项目 UPPM-RG-001 例 5.3 已出现，在此重证并接入过程记录。[\[38\]](#ref-uppm)

#### 定理 12.6：三分支兼容与四分支反例

三个酉分支的交叉系数可以放进同一个完整过程，当且仅当

$$
|\gamma_{12}|,\ |\gamma_{23}|,\ |\gamma_{31}|\le1,
$$

$$
\boxed{\quad
 1+2\operatorname{Re}(\gamma_{12}\gamma_{23}\gamma_{31})
 -|\gamma_{12}|^2-|\gamma_{23}|^2-|\gamma_{31}|^2\ge0 .
 \quad}
\tag{Q21-C11}
$$

然而，每个三分支子系统兼容，并不保证任意多个分支整体兼容。

**证明。**

三阶 Hermitian 矩阵半正定当且仅当全部主子式非负： 正性显然使每个主子矩阵半正定；反向， $\det(tI+G)$ 的各系数是相应阶主子式之和，最高项为 $t^3$， 故当这些主子式均非负时，$\det(tI+G)>0$ 对全部 $t>0$ 成立。 若 $G$ 有负特征值 $\lambda$，取 $t=-\lambda$ 即矛盾。 一阶子式为 $1$，二阶子式为 $1-|\gamma_{jk}|^2$， 展开三阶行列式即得 (Q21-C11)。 对最后一句，取四阶相关候选

$$
G_4=\frac75 I_4-\frac25\mathbf1_4\mathbf1_4^\dagger .
\tag{Q21-C12}
$$

它的对角元均为 $1$，非对角元均为 $-2/5$。 任一三阶主子矩阵的特征值是 $7/5,7/5,1/5$，因而正定； 但整个矩阵在 $\mathbf1_4$ 上的特征值为 $-1/5$。 故全部原始三元测试通过而整体不合法。

$\square$

#### 定理 12.7：新增分支的递归兼容判据

设已有 $G\ge0$，新增一个归一分支，与旧分支的交叉列为 $g$。 记 $G^+$ 为 Moore–Penrose 广义逆。则

$$
\begin{pmatrix}G&g\\g^\dagger&1\end{pmatrix}\ge0
 \quad\Longleftrightarrow\quad
 g\in\operatorname{ran}G,\qquad
 g^\dagger G^+g\le1 .
\tag{Q21-C13}
$$

这里 $^\dagger$ 始终表示共轭转置。

**证明。**

正性先迫使 $g$ 正交于 $\ker G$，即 $g\in\operatorname{ran}G$。 写 $h=G^{+}g$，便有 $Gh=g$。 对任意列向量 $x$ 与标量 $t$，块二次型为

$$
x^\dagger Gx+2\operatorname{Re}(x^\dagger gt)+|t|^2
 =(x+ht)^\dagger G(x+ht)
   +|t|^2(1-g^\dagger G^{+}g).
$$

若块矩阵为正，取 $x=-ht$ 即得第二条件。 反向由同一公式立即得到。

$\square$

式 (Q21-C13) 保留的是新分支与全部已有线性组合的关系。 因此可以逐次添加有限分支，并在每一步保存已经确定的比较； 但不能把这个条件换成“只检查原始标签中的每一组三个”。 若已经显式构造同一个环境内的记录向量 $e_j$， 则所有有限相关矩阵的正性由同一个内积自动保证。 这是构造性闭合，不是把四元以上的反例用定义删掉。

### 12.4　新过程的组合与同一记忆的回声

#### 定理 12.8：无共享记忆时的交叉映射组合律

设 $\Lambda$ 和 $\mathcal M$ 为同一控制标签上的两次确定完全正保迹操作， 其交叉映射分别为 $\Gamma_{jk}$ 和 $\Delta_{jk}$。 作为完整控制–目标系统上的普通通道组合， $\mathcal M\circ\Lambda$ 的交叉映射是

$$
(\Delta\circ\Gamma)_{jk}=\Delta_{jk}\circ\Gamma_{jk}.
\tag{Q21-C14}
$$

若两次酉分支为 $U_j,V_j$，相关矩阵为 $G,D$， 则合成酉分支是 $V_jU_j$，相关矩阵是 $D\circ G=(\delta_{jk}\gamma_{jk})$。

**证明。**

对 $|j\rangle\langle k|\otimes X$ 连续应用 (Q21-C3) 即得第一式。 代入酉分支公式，得 $\delta_{jk}\gamma_{jk}V_jU_jXU_k^\dagger V_k^\dagger$。 相应有限环境实现使用记录 $e_j\otimes f_j$， 其反序 Gram 元为 $\langle e_k,e_j\rangle\langle f_k,f_j\rangle$， 故 $D\circ G\ge0$。

$\square$

#### 命题 12.9：同一个内部记忆不能被重置公式替代

存在两次完全相同的整体酉操作，使第一次约化控制过程完全去相干， 第二次操作后却恢复全部相干。 因此不能用第一次约化通道的自复合来描述同一记忆的再次使用。

**证明。**

目标取一维，控制 $C$ 与环境 $E$ 各取一个 qubit， 环境初态为 $|0\rangle$。 整体酉操作为

$$
W=|0\rangle\langle0|_C\otimes I_E
   +|1\rangle\langle1|_C\otimes X_E .
$$

第一次作用后，两个内部记录为 $e_0=|0\rangle,e_1=|1\rangle$， 故 $\gamma_{01}=0$，约化控制通道为完全去相干 $\mathcal D$。 再在同一个 $E$ 上作用同一个 $W$，有 $W^2=I$， 整体及约化控制初态全部恢复，合成过程的 $\gamma_{01}=1$。 但 $\mathcal D\circ\mathcal D=\mathcal D$，不会恢复相干。 更强地，控制初态 $|+\rangle$ 与 $|-\rangle$ 在第一次约化后 同为 $I/2$，第二次整体作用后却分别恢复为两个不同纯态； 因此不存在仅以第一次约化状态为输入、能同时给出这两个后继的函数。 差别在于第二次操作前 $C$ 与 $E$ 已相关； 从第二次的约化输入态单独出发，并不存在本例中所假定的同一个 与环境无关的约化通道 $\mathcal D$。

$\square$

**本区域闭合推出的内容。**

在已声明的有限维复量子接口和标签保持条件下： 完整过程由正 Choi 块矩阵分类； 两个分支之间的全部未定量是一个支撑空间间的收缩； 酉分支时缩为内部记录的相关矩阵； 三元约束给出精确行列式，新增分支由 Schur 条件逐次验收； 保留环境时全部步骤由同一个有限等距或酉实现闭合。 没有从普通分支通道唯一推出相干控制， 没有从三元原始数据推出所有有限整体， 没有从“观察者内生”推出任意参考资源都已可用。

<a id="section-13"></a>

## 13　固定点、有限三维提升与完整内部时间

**本区域的输入。**

$$
I=[-1,1],\quad s\in\{-1,1\},\quad F_s(x)=s\cos x,
\quad \omega:I\to\mathbb R\text{ Lipschitz},
$$

$$
T_s:I\times S^1\to I\times S^1,\qquad
T_s(x,z)=(F_s(x),e^{i\omega(x)}z).
$$

角度编码、反馈函数、符号政策和相位更新均为本区域给定资料， 不是六组主条件自行选定。$z$ 表示可访问的内部 *相对* 相位； 若它只是整体共同相位，应先按实际菜单取相位商。 本节的余弦与相位结论已经出现在 OTF-004、OTF-005， 以下给出所需证明并保留其输入。[\[39\]](#ref-otf4), [\[27\]](#ref-otf5)

#### 定义 13.1：固定点的二元关系

对 $f:X\to X$，定义 $\Gamma_f=\{(x,f(x)):x\in X\}$、 $\Delta_X=\{(x,x):x\in X\}$。 固定点集合准确为 $\Gamma_f\cap\Delta_X$ 在第一坐标的投影。

#### 定理 13.2：正负余弦与政策二周期

存在唯一 $r\in(0,1)$ 满足 $\cos r=r$。 $F_s$ 在实轴的唯一固定点为 $sr$，任意实初值一步后进入 $I$， 并以常数 $L=\sin1<1$ 几何收敛到 $sr$。 两方程 $\cos x=x$ 与 $\cos x=-x$ 没有共同实解。 若给定内部政策 $G(s,x)=(-s,-s\cos x)$，则

$$
(1,r)\longleftrightarrow(-1,-r)
$$

是一条二周期。

**证明。**

$\cos x-x$ 在 $0,1$ 端点异号。 任何实固定点模至多为一；在 $I$ 上中值定理给 $|F_s(x)-F_s(y)|\le L|x-y|$。 余弦偶性给 $F_s(sr)=sr$，压缩估计给唯一性与迭代误差 $|x_n-sr|\le L^{n-1}|x_1-sr|$。 同时满足两方程将迫使 $x=0$，与 $\cos0=1$ 矛盾。 把 $(1,r),(-1,-r)$ 依次代入 $G$ 即得二周期。

$\square$

若每步允许任意符号 $s_n$，则一步后 $|x_{n+1}|=\cos|x_n|$，故模长仍趋 $r$； 符号却可持续切换。这是给定政策的结论，未唯一规定自然常数、粒子种类或时间箭头。

#### 定理 13.3：标量固定不保证相位固定

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

#### 命题 13.4：完整幺正整体没有非平凡吸引固定点

若 $`\rho_n=U^n\rho_0(U^*)^n`$ 在迹范数下收敛到 $`\rho_*`$，则 $`\rho_0=\rho_*`$ 且 $`U\rho_0U^*=\rho_0`$。 若完整状态还包含严格追加的记录 $m\mapsto m+1$，也不存在固定点。

**证明。**

极限连续性给 $`U\rho_*U^*=\rho_*`$。 于是 $`\|\rho_n-\rho_*\|_1=\|\rho_0-\rho_*\|_1`$ 对全部 $n$ 成立； 左边趋零使初始差已经为零。记录部分的不动要求 $m=m+1$，不可能。

$\square$

### 13.1　三维图像与有限动态闭合

#### 命题 13.5：静态三维归一化

$$
v(x)=(1,x,\cos x),\quad n(x)=v(x)/\|v(x)\|_2
$$

给球面中的曲线，并且 $\cos x=\pm x$ 分别等价于 $n_3(x)=\pm n_2(x)$。 但若要求提升中线性读出原 $x$，余弦迭代没有任何精确有限维线性提升。

**证明。**

第一坐标非零，归一化不改变第二、第三坐标的等比关系，给静态结论。 对第二项，若存在有限特征 $\Theta$、固定矩阵 $K$， $\Theta(\cos x)=K\Theta(x)$，且 $1,x$ 均为 $\Theta$ 的线性读数， 则 $1,x,\cos x,\cos(\cos x),\ldots$ 全在同一个有限维函数空间。

这些函数实际上在每个非空实开区间上线性无关。 设 $f_0(x)=x,f_{j+1}=\cos f_j$，有限关系 $c_{-1}+\sum_{j=0}^Nc_jf_j=0$ 在区间成立。 各项整函数，解析恒等定理将关系延到实轴。 $f_0$ 无界，而所有 $j\ge1$ 项在实轴有界，故 $c_0=0$。 以 $y=\cos x$ 遍历 $[-1,1]$，余下关系变为 $c_{-1}+\sum_{j=1}^Nc_jf_{j-1}(y)=0$；再次解析延拓，得 $c_1=0$。 有限重复消去全部系数，矛盾。

$\square$

该命题没有排除状态依赖矩阵、近似、无限维表示或改变读出坐标的共轭。 归一化后的 $x=n_2/n_1$ 是比值读数，不能直接拿上一线性读数判据排除一切射影模型。 对所写自然坐标本身，还可独立证明不存在固定非零射影推进，附完整短证如下。

#### 命题 13.6：自然三维坐标没有固定射影线性推进

不存在固定 $M\in M_3(\mathbb R)$ 使 $Mv(x)=\lambda(x)v(\cos x)\ne0$ 在一个非空实开区间恒成立。

**证明。**

将三行记为 $(a,b,c),(d,e,f),(g,h,k)$。 首行给 $\lambda=a+bx+c\cos x$。 次行的整函数恒等式延拓到 $x=iy$，虚部给 $ey=by\cosh y$，故 $b=e=0$；实部给 $d+(f-a)\cosh y-c\cosh^2y=0$，故 $c=d=0,f=a$。 因此 $\lambda=a\ne0$。 第三行成为 $g+hx+k\cos x=a\cos(\cos x)$。 再置 $x=iy$，虚部使 $h=0$，右端有界而 $\cosh y$ 无界使 $k=0$。 取 $\cosh y=\pi,2\pi$，分别给 $g=-a,g=a$，矛盾。

$\square$

### 13.2　把钟和操作写进整体的一个有限模型

#### 定理 13.7：有限内部历史态与传播约束

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

这属于关系时钟的有限数学实现；门、标签次序及初始数据均留在式中。[\[40\]](#ref-pw), [\[41\]](#ref-trinity), [\[42\]](#ref-baumann) 它不自动选择秒、连续时长或唯一宇宙态；$G_{\rm hist}$ 是传播约束，未被默认为驱动实际装置的 Hamiltonian。

若实验二值结果 $Y\in\{-1,1\}$ 仅满足 $\mathbb E[Y\mid x]=\cos x$， 则单次反馈 $x'=sY$ 一步后只取 $\pm1$，到 $sr$ 的距离至少为 $1-r>0$。 因此理想期望反馈的压缩不等于单次量子结果的轨迹。 重复准备、估计误差和控制资源均须作为内部协议继续保留。

<a id="section-14"></a>

## 14　内部表示、对角边界与全局余弦的算术表达力

**输入：** 指定的表达语言、合法读出类与评价规则。 讨论不完备时还需有效公理化、一致性及足够的算术表达力。 **输出：** 表达像的对角障碍、定义保守性及相应不可证性。 本节不以这些逻辑结果代替几何正性、复线性、Born 或时间接口。

### 14.1　不需要负存在的对角障碍

#### 定理 14.1：内部自评价的精确对角条件

设 $E:A\times A\to Y$ 为全域评价表， $\alpha:Y\to Y$ 为指定响应。 若存在 $a\in A$ 使

$$
E(a,x)=\alpha(E(x,x))\qquad(x\in A),
$$

则 $\alpha$ 有不动点。

**证明。**

取 $y=E(a,a)$，代入 $x=a$，即得 $y=\alpha(y)$。

$\square$

这就是 Lawvere 固定点定理的集合形式[\[9\]](#ref-q022-lawvere)， 也已见项目 R5-006 §8。 如果全部允许响应都可由旧行表示， 且允许响应类包含 $x\mapsto\alpha(E(x,x))$， 则每个允许的 $\alpha$ 都必须有不动点。

取两个正的存在标签 $Y=\{1,2\}$，令 $\alpha(1)=2,\alpha(2)=1$，便没有不动点。 因此“全域评价、全部表示、允许该对角反转”不能同时成立。 这不使用任何负存在。 若改用 $Y=[0,1]$、$\alpha(y)=1-y$， 不动点 $1/2$ 只解除这一特定反转的矛盾， 没有推出 Born 规则。 $\cos$ 有不动点也不能反向证明全部内部表示条件。

### 14.2　定义、证明与真值应分别计账

#### 定理 14.2：显式关系定义的保守性

设 $T$ 使用语言 $L$，$\varphi(x)$ 是旧语言公式。 加入新关系符号 $R$ 及定义 $R(x)\leftrightarrow\varphi(x)$，得到 $T'$。 对任意旧语言句子 $\psi$，有

$$
T'\vdash\psi\iff T\vdash\psi.
$$

**证明。**

先对绑定变量重命名以免捕获， 再把新证明中 $R(t)$ 的每次出现替换为 $\varphi(t)$。 定义公理化为逻辑恒真式，旧公理与推理步骤仍有效， 得到 $T$ 中的证明。反向由 $T\subseteq T'$。

$\square$

所以把约束写进定义能明确研究对象，却不会自动证明原世界满足这些约束。 若引入函数符号，相关唯一存在必须先在旧理论中证明， 才能按通常规则称为保守定义扩展。

#### 引理 14.3：对角句的条件性构造

固定句法编码：$\#\varphi\in\mathbb N$ 表示公式代码， $\ulcorner\varphi\urcorner:=\overline{\#\varphi}$ 表示对象语言中的对应数码。 令 $d(n)$ 为把代码 $n$ 的单自由变量公式 代入其自身代码数码后得到的句子代码；非法或非单自由变量代码统一取 $d(n)=0$。 假设理论 $T$ 中的关系 $D(x,y)$ 对每个标准自然数 $n$ 满足

$$
T\vdash\forall y\,[D(\bar n,y)\leftrightarrow y=\overline{d(n)}].
$$

则对每个单自由变量公式 $\theta(y)$，存在句子 $G$ 使

$$
T\vdash G\leftrightarrow\theta(\ulcorner G\urcorner).
$$

**证明。**

令 $\beta(x):=\exists y\,[D(x,y)\land\theta(y)]$， $b:=\#\beta$，并令 $G:=\beta(\bar b)$。 按 $d$ 的定义，$d(b)=\#G$。 使用关于固定标准数 $b$ 的显示条件，得

$$
T\vdash G\leftrightarrow
\exists y\,[y=\overline{d(b)}\land\theta(y)]
\leftrightarrow\theta(\ulcorner G\urcorner).
$$

$\square$

这里的句法编码与递归代入可表示性是明确逻辑基础， 在足够算术中由标准算术化取得；本稿不把它们算成由量子面积导出的事实。 新句子的代码仍是同一自然数域中的一个数。

#### 定理 14.4：第二不完备的条件性核心

令 $T$ 为一致经典理论，具有上述对角构造。 记 $\Box\varphi:=\operatorname{Prov}_T(\ulcorner\varphi\urcorner)$， 并明确要求 Hilbert–Bernays–Löb 三个可导性条件：

$$
\begin{aligned}
T\vdash\varphi&\ \Longrightarrow\ T\vdash\Box\varphi,\\
T&\vdash\Box(\varphi\to\psi)\to(\Box\varphi\to\Box\psi),\\
T&\vdash\Box\varphi\to\Box\Box\varphi.
\end{aligned}
$$

若 $\operatorname{Con}(T):=\neg\Box\bot$，则

$$
T\nvdash\operatorname{Con}(T).
$$

**证明。**

对角构造给 $T\vdash G\leftrightarrow\neg\Box G$。 首先 $T\nvdash G$：否则第一可导性条件给 $T\vdash\Box G$， 而该等价式给 $T\vdash\neg\Box G$，违反一致性。

在 $T$ 内，由 $G\to\neg\Box G$ 和前两可导性条件有

$$
\Box G\to\Box\neg\Box G.
$$

第三条件又给 $\Box G\to\Box\Box G$。 将经典恒真式 $\neg\Box G\to(\Box G\to\bot)$ 用前两条件搬入可证明性中，得到

$$
\Box\neg\Box G\to(\Box\Box G\to\Box\bot).
$$

因此 $T\vdash\Box G\to\Box\bot$。 经典逆否及对角等价式给

$$
T\vdash\operatorname{Con}(T)\to\neg\Box G,\qquad
T\vdash\neg\Box G\to G.
$$

故

$$
T\vdash\operatorname{Con}(T)\to G.
$$

若 $T\vdash\operatorname{Con}(T)$，就有 $T\vdash G$， 与第一段矛盾。

$\square$

这是在列明可导性条件后的完整短证明，不把任意自称“可证明”的谓词 都视为标准证明谓词，也不把第二不完备用于任意有限关系表。 有关 Gödel 两个定理的作者级机器形式化可参见 Paulson[\[13\]](#ref-q022-paulson)。

#### 命题 14.5：Gödel–Rosser 的适用范围

一致、有效可公理化且包含或有效解释足够算术的经典理论， 例如包含 Robinson $Q$ 的理论，不完备。 即存在句子 $R_T$，使

$$
T\nvdash R_T,\qquad T\nvdash\neg R_T.
$$

这里引用标准 Gödel–Rosser 定理，而不把对原始 Gödel 句的 单侧不可证短证当成 Rosser 的完整证明。 Gödel 原文与 Rosser 的加强分别见 [\[10\]](#ref-q022-godel), [\[11\]](#ref-q022-rosser)。 项目 R5-006 §9.2–9.4 已明确保留对角引理、 原始句与 Rosser 句的区别，以及第二不完备的可导性条件； 作者级机器形式化可参见 Paulson[\[13\]](#ref-q022-paulson)。

#### 定理 14.6：同层全真值障碍

设经典理论 $T$ 具有所需语法编码与对角引理。 若同一语言中的谓词 $\operatorname{Tru}$， 对包含该谓词自身的每个句子 $\varphi$ 都满足

$$
T\vdash\operatorname{Tru}(\ulcorner\varphi\urcorner)
       \leftrightarrow\varphi,
$$

则 $T$ 不一致。

**证明。**

对角引理给句子 $L$，使

$$
T\vdash L\leftrightarrow
        \neg\operatorname{Tru}(\ulcorner L\urcorner).
$$

对 $L$ 使用真值条件，得到 $T\vdash L\leftrightarrow\neg L$， 与经典一致性不相容。

$\square$

这是一种 Tarski 型真值障碍[\[12\]](#ref-q022-tarski-truth)。 语法代码可以仍在同一个自然数域里； 分层真值关系也可以作为同一整体中的有类型对象。 这些定理没有推出空间每次增加一根轴。

### 14.3　固定有限的代数量子关系可判定

#### 定理 14.7：有限代数量子片段的有效归约

考虑每次给定固定有限矩阵尺寸的公式， 只使用实代数常数、复向量与矩阵的加乘、伴随、有限张量积、 迹、秩约束、正性、归一化和有限次一阶量词。 该公式能有效翻译为实闭域公式，其闭句真值可判定。

**证明。**

每个复坐标以两个实坐标表示。 复加乘、共轭及固定尺寸的矩阵运算均变为有限个实多项式。 正性可写成 $`X=B^*B`$ 对某个同尺寸复矩阵 $B$ 成立， 故也能用一阶多项式关系表示。 秩不超过 $r$ 由全部 $(r+1)$ 阶子式为零表达； 酉性为 $`U^*U=I`$，密度态、效果和 Choi 条件均由这些关系组合。 实代数常数用整系数多项式及隔离区间有效指定。 因此每个公式翻译为有限个实变量上的有序域公式。 应用 Tarski 的有效消去量词定理，即得判定算法 [\[43\]](#ref-q022-tarski-decision), [\[44\]](#ref-q022-marker)。

$\square$

这里完整证明的是到实闭域的归约，量词消去作为明确的成熟定理引用。 该片段不包含任意实数输入 oracle，不包含对无界离散历史或矩阵维数的 内层量化，也不包含全局 $\cos,\exp$ 或任意微分方程。 实闭域语言不能定义完整自然数算术； 其一维可定义集合是有限个点与区间的并， 特别地不能定义 $\mathbb Z$[\[44\]](#ref-q022-marker)。

### 14.4　全局余弦却可在同一实轴中定义整数

#### 定理 14.8：全局余弦的算术解释

在标准结构

$$
\mathcal R_{\cos}
   =(\mathbb R;0,1,+,\times,<,\cos)
$$

中定义

$$
\begin{split}
 \operatorname{Per}(p)\ \Longleftrightarrow\
 &p>0\ \land\ \cos p=1\\
 &{}\land\forall u\,(0<u<p\Rightarrow\cos u\ne1).
\end{split}
$$

则 $\operatorname{Per}$ 恰好定义 $p=2\pi$。 进而

$$
\operatorname{Int}(x)
 \ \Longleftrightarrow\
 \exists p\,[\operatorname{Per}(p)\land\cos(px)=1]
$$

恰好定义 $\mathbb Z$。 再令 $\operatorname{Nat}(x)\leftrightarrow \operatorname{Int}(x)\land x\ge0$， 实加乘在该定义集上的限制就是标准自然数加乘。

**证明。**

全局余弦满足 $\cos t=1\iff t=2\pi k$ 对某个 $k\in\mathbb Z$ 成立。 故最小正根恰为 $2\pi$，且 $\cos(2\pi x)=1\iff x\in\mathbb Z$。 自然数定义与加乘限制随即成立。

$\square$

#### 定理 14.9：完整真理论不可判定，但语义上完备

所有真句组成的 $\operatorname{Th}(\mathcal R_{\cos})$ 是完备理论，但不可判定，也不可有效公理化。

**证明。**

把任意算术句 $\varphi$ 的量词限制到 $\operatorname{Nat}$：

$$
(\exists n\,\psi)^*
 =\exists x\,(\operatorname{Nat}(x)\land\psi^*),
$$

$$
(\forall n\,\psi)^*
 =\forall x\,(\operatorname{Nat}(x)\Rightarrow\psi^*).
$$

加乘项不变。对公式结构归纳得到

$$
\mathbb N\models\varphi
 \iff
 \mathcal R_{\cos}\models\varphi^*.
$$

若后者的全部真句可判定，就能判定全部真算术，矛盾。 所有真句的集合按定义对每个句子包含它或其否定，因此语义上完备。 若该集合还可有效公理化，则同时枚举某句与其否定的证明， 完备性保证其中一个搜索终止，得到判定算法，再次矛盾。

$\square$

这里的算术不可判定性可由 Gödel–Rosser 得到： 若全部真算术可判定，它本身就给出一致、有效、完备且包含足够算术的理论。 全局周期函数与算术不可判定性的关系也属于成熟研究范围； Richardson 的原论文研究更受限表达式类的不同判定问题， 其具体前提不能与上述全一阶归约互换[\[45\]](#ref-q022-richardson)。

因此应分开三个对象：

1.  单个任务 $\cos x=x$：有唯一可计算实不动点；

2.  限制区间上的余弦：本节的全局周期编码证明不适用；

3.  全局余弦加上实加乘与任意一阶量化： 能定义整数，整个真理论不可判定。

不完备结论作用于一致、有效且足够表达算术的公理体系； 不能把完整真理论 $\operatorname{Th}(\mathcal R_{\cos})$ 本身误写成“语义不完备”。

这给出用户所提余弦与不完备之间的一条准确联系： 改变的是允许的运算、编码和量化范围； 一个不动点已经找到，不代表同一语言内的全部命题已经封闭判定。 该联系没有从逻辑推出面积、量子概率或物理时间。

<a id="section-15"></a>

## 15　最新项目接口：忠实包含与面积预算不能混同

### 15.1　共同原接口与输出范围

此节继承项目的另一条 Jordan 响应路线，而非把它冒充本稿六组振幅读出条件的直接结论。 其原对象为实 Archimedean 序单位空间 $(E,C,u)$、准确决定原锥且分离原元的正实线性评价族， 以及两槽总映射 $S,D:E^2\to E$。其入口保留：

1.  原有向 Hermitian 二表正性（A1/P2）；在已得 Jordan 接口 $S(a,b)=a\circ b$ 下， 对每个相应正读取 $\beta$，

    $$
    \begin{pmatrix}
    \beta(a^2)&\beta(a\circ b)-i\beta(D(a,b))\\
    \beta(a\circ b)+i\beta(D(a,b))&\beta(b^2)
    \end{pmatrix}\ge0.
    $$

2.  $(a+b,a,b)$ 及排列的实三表正性，且指定系数 $(1,-1,-1)$ 给零二次值（A2）。

3.  $S(u,u)=u$，以及同一固定有理 $0<\theta\le1$ 上 $0\le e\le\theta u\Rightarrow S(e,e)\le e$（A3）。

4.  完整三元配平（PB）：对所有原 $a,b,c$，令

    $$
    \nu=D(a,b)-a\circ c,\quad
    \omega=a\circ b+D(a,c),\quad
    r_\pm=b\pm\nu,\quad s_\pm=c\pm\omega,
    $$
    则保留同一原元素式

    $$
    D(r_+,s_+)-D(r_-,s_-)
    =-2b\circ\nu-2c\circ\omega.
    $$

原零、不等和次归一评价质量均不删除。 使用的完成、正读取与忠实包含必须有各自来源； 未知 $D$ 的双线性、连续性或完成延拓不作为默契条件加入。 这些条件及其前置 Jordan 恢复均是所引用源路线的一部分。[\[3\]](#ref-radial22), [\[4\]](#ref-poly22)

**新近扩大的范围。**

固定源的中心响应稿第 16–22 节已不再要求 $E$ 在整个指定复载体的自伴部分中稠密。 它保留一般 JB 原完成、已经得到的忠实 JC 包含及原接口。 第 18.1 条在明确的 $a\circ b\in\mathbb Ru$ 或 $a^2-b^2\in\mathbb Ru$ 条件下给平方闭式

$$
D(a,b)^2=a^2b^2-(a\circ b)^2
$$

并保留原响应的正交关系；第 20.1 条处理全径向， 第 21.1 条处理共同强度结构上的跨平面可加。 一般全域 $D$ 双线性、跨参考一致及全部实际量子和时钟接口仍须分别支付。 本稿核对其源前提与有限矩阵消费者，不重新认证一般 JB 表示论的整条外部依赖。 显示平方式的右侧在该忠实复载体中计算；不是未经定义的 Jordan 三元重括号。

#### 命题 15.1：忠实表示不要求填满环境

在有限矩阵模型中，$M_2(\mathbb C)_{\rm sa}$ 可通过

$$
\iota(a)=a\otimes I_m
$$

忠实嵌入 $M_{2m}(\mathbb C)_{\rm sa}$，保留单位、Jordan 乘法、算子范数、 平方和交换子响应。若 $m>1$，其像是严格真子空间。 所以“在更大结构内部表达”不等于“必须具有整个环境的全部独立方向”。

**证明。**

张量计算给 $\iota(a\circ b)=\iota(a)\circ\iota(b)$、$\iota(I)=I$， 以及 $\iota([a,b])=[\iota(a),\iota(b)]$。 $a\otimes I_m=0$ 蕴含 $a=0$，故忠实； 其本征值是 $a$ 本征值的重复，故保范数与正锥。 源空间实维四，而目标自伴空间实维 $(2m)^2>4$，所以像严格。

$\square$

#### 命题 15.2：平方面积闭式的有限矩阵核对

令 $a,b$ 为自伴矩阵，并在本命题中明确给定

$$
D(a,b)=\frac{i}{2}(ab-ba),\qquad a\circ b=\frac{ab+ba}{2}.
$$

若 $a\circ b$ 为标量矩阵，或者 $a^2-b^2$ 为标量矩阵，则

$$
D(a,b)\circ a=D(a,b)\circ b=0,\qquad
D(a,b)^2=a^2b^2-(a\circ b)^2\ge0.
$$

**证明。**

若 $ab+ba=2\gamma I$，则 $ab^2=(2\gamma I-ba)b=2\gamma b-bab=b^2a$； 交换 $a,b$ 同理得 $a^2b=ba^2$。 若 $a^2-b^2=\gamma I$，这两条交换关系也立即成立。 因此

$$
D(a,b)\circ a=\frac{i}{4}(a^2b-ba^2)=0,
\quad
D(a,b)\circ b=\frac{i}{4}(ab^2-b^2a)=0.
$$

直接展开给

$$
(a\circ b)^2+D(a,b)^2
=\frac12(ab^2a+ba^2b)=a^2b^2.
$$

$D(a,b)$ 自伴，所以它的平方为正。

$\square$

该命题明确支付了交换子表示；它核对已给表示中的几何恒等式， 不能替代源路线中从未知原 $D$ 推出相应结构的证明。

下面的面积预算反例是固定源第 6.2 节的新近结果； 它在一个完整具体模型中重新证明，不依赖“面积即存在”的解释。

### 15.2　原响应已经相同，而四份面积预算仍有严格正底

**对象与目标。**

令 $E$ 为含单位 $u$ 的实 Jordan 空间，乘法记为 $\circ$， 并给定同一个原响应 $D:E^2\to E$。 固定 $a,b\in E$、$s\in\mathbb R$，对两个演员位置 $\tau=0,s$ 定义

$$
a_\tau=a+\tau u,\qquad d_\tau=D(a_\tau,b),\qquad
 \delta=d_s-d_0.
$$

取一个实际共同零辅助标签 $c$，即

$$
D(a,c)=D(a+su,c)=0.
$$

对每个 $\tau$ 与 $\epsilon\in\{+1,-1\}$，保留完整原输入

$$
R_{\tau,\epsilon}=b+\epsilon d_\tau-\epsilon(a_\tau\circ c),
 \qquad
 S_{\tau,\epsilon}=c+\epsilon(a_\tau\circ b).
$$

给定同一正实线性读取 $\beta$，定义四个实 Gram 面积平方

$$
\Delta_{\tau,\epsilon}(c)
 =\beta(R_{\tau,\epsilon}^2)\beta(S_{\tau,\epsilon}^2)
   -\beta(R_{\tau,\epsilon}\circ S_{\tau,\epsilon})^2,
 \qquad
 W_\beta(c)=\sum_{\tau\in(0,s)}\sum_{\epsilon=\pm1}
                  \sqrt{\Delta_{\tau,\epsilon}(c)}.
$$

这里 $(0,s)$ 表示两个有标号的演员位置；即使 $s=0$，也保留两次。

若原响应满足项目所列的完整正反配平 PB，则令

$$
\mathcal B_\tau(c)
 =D(R_{\tau,+},S_{\tau,+})-D(R_{\tau,-},S_{\tau,-})
$$

可得

$$
\mathcal B_\tau(c)
 =-2b\circ d_\tau
 +2\{b\circ(a_\tau\circ c)-c\circ(a_\tau\circ b)\},
 \qquad
 \mathcal B_s(c)-\mathcal B_0(c)=-2b\circ\delta.
$$

最后一步只在已知 Jordan 乘法上消去 $s(b\circ c-c\circ b)=0$，没有展开未知 $D$ 的输入。 若四张原二元正表 P2 均可由同一 $\beta$ 读取，逐份取绝对值仅给

$$
2|\beta(b\circ\delta)|\le W_\beta(c).
$$

#### 命题 15.3：零目标缺陷与严格正的独立面积预算

这里称投影 $p$ 为最小 Jordan 投影，当且仅当 $U_p(X)=\mathbb R p$；不以投影偏序极小代替这一条件。 存在一个不完备原域及其无非零上述最小 Jordan 投影的完成， 满足全部原 A1–A3、P2、PB；对每个 $s\ne0$，存在同一固定正读取，满足

$$
\boxed{
 \delta=0,\qquad
 \inf_{c\in\mathbb R[a]}W_\beta(c)
 =\inf_{\substack{c\in E:\,D(a,c)=0\\D(a+su,c)=0}}W_\beta(c)
 =2|s|>0.}
$$

所以，四份独立面积上界不能普遍被压到零；其正下界也不证明目标差 $\delta$ 非零。

**证明。**

取矩阵值实变量多项式

$$
E=M_2(\mathbb C)_{\rm sa}[t],\qquad
 X=C([0,1],M_2(\mathbb C))_{\rm sa},\qquad u=I,
$$

并定义

$$
F\circ G=\frac{FG+GF}{2},\qquad
 D(F,G)=\frac{i}{2}(FG-GF),\qquad
 C=E\cap X_+.
$$

范数取上确界算子范数；原评价取全部正点向量评价及其任意非负质量倍数。 这些评价分离原元素且准确决定 $C$，包括零质量。 多项式逼近使 $E$ 在 $X$ 中稠密， 而 $|t-1/2|I\notin E$，所以原域不完备。

逐点有 $F\circ G-iD(F,G)=FG$，故原 Hermitian 二表就是 向量 $F(t)\xi,G(t)\xi$ 的复 Gram 表，给 A1 与 P2。 相加三表的实部是同一组向量的实 Gram 表， 指定系数 $(1,-1,-1)$ 给零向量，故 A2 成立。 任一固定有理 $0<\theta\le1$ 下， $0\le e\le\theta I$ 蕴含 $e^2\le e$，且 $I^2=I$，故 A3 成立。

还需核对 PB 的全部三元输入，不能只核对所用 Pauli 点。 任取原 $A,B,C$，令

$$
\nu=D(A,B)-A\circ C,\qquad
 \omega=A\circ B+D(A,C),\qquad
 r_\pm=B\pm\nu,\quad s_\pm=C\pm\omega,
 \quad Z=B+iC.
$$

已知矩阵乘法直接给

$$
r_\pm+i s_\pm=(I\pm iA)Z,
$$

从而

$$
r_\pm^2+s_\pm^2+2D(r_\pm,s_\pm)
 =Z^*(I+A^2)Z.
$$

两式相减便得到

$$
D(r_+,s_+)-D(r_-,s_-)
 =-2B\circ\nu-2C\circ\omega,
$$

这正是完整 PB。所有原调用仍在 $E$ 中。

这个模型也没有全局非零最小 Jordan 投影。 若 $p\in E$ 或 $X$ 是非零投影，连续整数值 $\operatorname{rank}p(t)$ 在 $[0,1]$ 上为非零常数。 于是 $p,tp$ 都在 $U_p(E)$ 或 $U_p(X)$ 中，并且实线性独立； 这里 $U_p(x)=pxp$。因此 $U_p(E)\ne\mathbb Rp$， $U_p(X)\ne\mathbb Rp$。

现在取常值

$$
a=\sigma_x,\qquad b=\sigma_y,\qquad z=\sigma_z,
 \qquad
 \beta(F)=\frac12\int_0^1\operatorname{Tr}F(t)\,dt.
$$

$\beta$ 是固定正数学读取；不据此增加实际准备资源。 Pauli 乘法给 $a\circ b=0$、$[a,b]=2iz$，所以

$$
d_\tau=D(a+\tau I,b)=-z\quad(\tau\in\mathbb R),
 \qquad\delta=0.
$$

所有共同零辅助标签恰为

$$
c(t)=r(t)I+q(t)a,\qquad r,q\in\mathbb R[t],
$$

因为这是 $a$ 的点态自伴通勤子空间；其系数由 $r=\operatorname{Tr}c/2$、$q=\operatorname{Tr}(ac)/2$ 给出。 较小的族 $\mathbb R[a]$ 只取常数 $r,q$。

在实内积 $\langle F,G\rangle_\beta=\beta(F\circ G)$ 中， $I,a,b,z$ 正交且各为单位向量。 对 $\tau=s$，写

$$
S_{s,\epsilon}=c+\epsilon s b,
 \qquad
 R_{s,\epsilon}=R'_{s,\epsilon}+\epsilon d_s,
 \qquad
 R'_{s,\epsilon}=b-\epsilon(a_s\circ c).
$$

其中

$$
a_s\circ c=(q+sr)I+(r+sq)a.
$$

因此 $d_s=-z$ 同时与 $S_{s,\epsilon},R'_{s,\epsilon}$ 正交， 且 $\|d_s\|_\beta=1$。逐个符号得到

$$
\begin{aligned}
 \Delta_{s,\epsilon}(c)
 &=\|S_{s,\epsilon}\|_\beta^2
 +\bigl(\|R'_{s,\epsilon}\|_\beta^2\|S_{s,\epsilon}\|_\beta^2
        -\langle R'_{s,\epsilon},S_{s,\epsilon}\rangle_\beta^2\bigr)\\
 &\ge\|S_{s,\epsilon}\|_\beta^2
 =\int_0^1(r(t)^2+q(t)^2)\,dt+s^2\ge s^2.
 \end{aligned}
$$

括号非负只用实 Cauchy–Schwarz。 另外两份 Gram 行列式非负，因此对整个共同零辅助族

$$
W_\beta(c)\ge2|s|.
$$

取合法辅助标签 $c=0$，有 $S_{0,\pm}=0$，故两份零位预算为零； 而

$$
R_{s,\pm}=b\pm d_s,\qquad S_{s,\pm}=\pm s b
$$

给

$$
\Delta_{s,\pm}(0)=2s^2-s^2=s^2.
$$

因此 $W_\beta(0)=2|s|$，两个下确界都实际达到。

$\square$

**精确消费边界。**

上述命题重证的是项目新近加入的一个反例， 针对的是把四个独立绝对值上界之和普遍压到零的中间证明方案。 它不反驳本模型的单位平移，因为本模型已经满足 $\delta=0$； 也不声称所有面积均无意义。 它说明必须保留四次原输出之间的符号和共同约束， 而不能把独立面积预算的剩余量等同于目标缺陷、新对象或新的几何维数。

<a id="section-16"></a>

## 16　闭合范围、存在类型与下一条可删除前提

### 16.1　同一整体中的五类合法性

| 对象类型 | 正性或合法性 | 不能混同的内容 |
|:---|:---|:---|
| 原振幅读出 | $q(x)\ge0$；商中 $q(x)>0\iff x\ne0$ | $x$ 与 $-x$ 可同为非零；相消不等于负概率。 |
| 事件 | $0\le E\le I$ | 非零正交投影的积可为零，所以不能要求事件积都遵守振幅的乘法范数。 |
| 关系表 | 每个有限 Gram 二次型非负 | 只查原标签的二元或三元主块不够；须检查全部有限组合。 |
| 过程 | 全部有限参照上的正性与指定总量条件 | 分支通道不决定交叉相干；当前边缘不决定含记忆的全部未来。 |
| 逻辑评价 | 保持给定语言、合法输入与推理规则 | 非负标签不能消除无不动点的交换；内生性不保证全域自评价完备。 |

### 16.2　本轮真正完成的移动

$$
\underbrace{\text{统一有限二元合成界}}_{\text{输入}}
\Longrightarrow
\underbrace{\text{原读出连续、精确三角、内积}}_{\text{输出}}
\Longrightarrow
\underbrace{\mathbb H,\ \mathbb C^2,\ S^2}_{\text{同对忠实条件下输出}}.
$$

$$
\underbrace{\text{正核及指定新关系}}_{\text{关系输入}}
\Longrightarrow
\underbrace{\text{最小内生表示与精确秩余量}}_{\text{表示输出}}.
$$

$$
\underbrace{\text{自应用、表达闭包与无不动点反转}}_{\text{逻辑输入}}
\Longrightarrow
\underbrace{\text{全域无遗漏自评价不可能}}_{\text{逻辑输出}}.
$$

三条蕴含有不同的签名与前提；只有显式构造相应映射，才可以把它们连接。 不能因它们都使用“关系”“整体”或“提升”，便把一个结论直接替换为另一个。

同一结构允许相容的内部观察者、记忆、参照和有限历史钟。 实际 $H$、时钟单位、空间结构、场方程和无限维极限并未由六组核心条件选择。 本稿得到闭合的有限量子数学完成及其实际绑定条件， 没有证明“所有场都等于时间”或“任何面积都等于存在”。

### 16.3　输入总账

$$
\mathcal I_{\rm core}
=\{\mathsf B_1,\mathsf B_2^{22},\mathsf E,\mathsf N,\mathsf U,\mathsf F\},
\qquad |\mathcal I_{\rm core}|=6.
$$

$$
\mathcal I_{\rm actual}
=\{\mathsf I_{\rm read},\mathsf I_{\rm comp},
\mathsf I_{\rm proc},\mathsf I_{\rm time}\},
\qquad |\mathcal I_{\rm actual}|=4.
$$

这是命名组计数，不是十条相互独立原子公理的最小性定理。 数学基础和逻辑分支的附加前件均另有明示。 本轮已经给出有限局部合成界自身的删除反例， 但没有证明一切可能的更弱替代条件都不成立。

**本轮的一段白话。**

先只要求两份大小受控的存在方式放在一起比较时，不会出现没有共同上界的放大。 如果同一比较反复执行仍严格遵守同一乘法读出，原来容许的粗放大就会被一致性压掉， 精确长度、夹角和球面由此出现。面积说的是两种表示中有多少不能互相代替的方向， 所以一条已经存在的线也可以给出零面积； 多加一个坐标有时只是把原来已知的关系写直，并没有向整体外借入新信息。 观察者也留在这个整体中，它的参照、记忆和后续操作都要继续保留原关系。 如果再要求它无遗漏地评价包括自身反转在内的所有关系，就会遇到对角化的边界； 这个边界限制的是评价能力，不是命令世界每次新增一块面积。 因此可以把量子几何与内部表达放进同一套关系账本，但每一步新增了什么、 哪一步只是换了表示，都必须由相应的等式证明。

## 参考来源

<a id="ref-repo"></a>

\[1\] Trureturing，研究分支 `dev`。 主要快照 [c424643d6929](https://github.com/the-omega-institute/trureturing/commit/c424643d6929e124fcd872a0e42f9f277b931521)， 2026-11-08 19:56:02（Asia/Singapore）。 末检 [8a24ea4e79de](https://github.com/the-omega-institute/trureturing/commit/8a24ea4e79de962725aab9d9b49cc605fcc211d8)，提交时间 20:06:25；20:14 后核对。 理论树相同：1359 文件、163360015 字节，逐 Git blob 验证成功。 本稿只认领已列出的来源阅读及普通数学证明，不认领全仓库证明认证。

<a id="ref-r5006"></a>

\[2\] Trureturing， *R5-006：关系角色、反思与对角化* ，第 2–4、8–9 节；本轮未修改的直接前驱。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/AURIC_R5_006_RELATIONAL_ROLES_REFLECTION_AND_DIAGONALIZATION.md>。

<a id="ref-radial22"></a>

\[3\] Trureturing， *中央响应平方与径向一致性* ，本次新增第 11–23 节，重点定义 16.1、定理 18.1、20.1、21.1。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/AURIC_CENTRAL_RESPONSE_SQUARE_AND_RADIAL_CONSISTENCY.md>。

<a id="ref-poly22"></a>

\[4\] Trureturing， *原多项式零响应与 Cayley 域边界* ，本次新增第 4–7 节，重点 4.2、6.2。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/AURIC_ORIGINAL_POLYNOMIAL_ZERO_RESPONSES_AND_CAYLEY_DOMAIN_BOUNDARIES.md>。

<a id="ref-energy22"></a>

\[5\] Trureturing， *原有限能量取得* ，本次新增第 9–13 节，重点 12.2 的特征空间与信息边界。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md>。

<a id="ref-jet22"></a>

\[6\] Trureturing， *原源 jet 认证* ，本次新增第 15–17 节。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_SOURCE_JET_CERTIFICATION.md>。

<a id="ref-c133"></a>

\[7\] Trureturing， *C133：无锚标记有界轨道续卷 W* ，§§20–21：统一正幂三角、三相费用关系与平方几何。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/AURIC_C133_UNANCHORED_MARKER_BOUNDED_ORBITS_CONTINUATION_W.md>。

<a id="ref-q20repo"></a>

\[8\] Trureturing， *$\Omega Q$-020：从半范数读出到内生量子几何* ，§§2–4。既有第 20 轮结果，本稿保留并重证其分类部分。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/OMEGAQ_020_FROM_SEMINORM_READOUT_TO_ENDOGENOUS_QUANTUM_GEOMETRY.md>。

<a id="ref-q022-lawvere"></a>

\[9\] F. W. Lawvere.  *Diagonal arguments and cartesian closed categories* . Lecture Notes in Mathematics 92 (1969), 134–145; reprinted with author commentary in Reprints in Theory and Applications of Categories 15 (2006), 1–13. <https://tac.mta.ca/tac/reprints/articles/15/tr15.pdf>. Theorem 1.1.

<a id="ref-q022-godel"></a>

\[10\] K. Gödel. *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*. Monatshefte für Mathematik und Physik 38 (1931), 173–198. DOI: 10.1007/BF01700692. English translation by B. Meltzer: <https://gtts.ehu.es/German/Docencia/2021/MTBYC/pdf/Godel.pdf>. Original Proposition VI and the explicit assumptions following its proof.

<a id="ref-q022-rosser"></a>

\[11\] B. Rosser. *Extensions of some theorems of Gödel and Church*. Journal of Symbolic Logic 1(3) (1936), 87–91. DOI: <https://doi.org/10.2307/2269028>. Publisher extract consulted; it explicitly distinguishes simple from omega consistency.

<a id="ref-q022-tarski-truth"></a>

\[12\] A. Tarski.  *The Semantic Conception of Truth and the Foundations of Semantics* . Philosophy and Phenomenological Research 4(3) (1944), 341–376. Original text: <https://www.jfsowa.com/logic/tarski.htm>. Sections 8–10.

<a id="ref-q022-paulson"></a>

\[13\] L. C. Paulson. *A Mechanised Proof of Gödel’s Incompleteness Theorems using Nominal Isabelle*. Journal of Automated Reasoning 55 (2015), 1–37. DOI: 10.1007/s10817-015-9322-8. Author-uploaded version: <https://arxiv.org/abs/2104.13792>.

<a id="ref-breuer22"></a>

\[14\] T. Breuer， *The Impossibility of Accurate State Self-Measurements* ， Philosophy of Science 62(2) (1995), 197–214。 <https://doi.org/10.1086/289852>；原文大学镜像 <https://cqi.inf.usi.ch/qic/Breuer95.pdf>。

<a id="ref-cpw22"></a>

\[15\] T. S. Cubitt, D. Pérez-García and M. M. Wolf，  *Undecidability of the spectral gap* ， Forum of Mathematics, Pi 10 (2022), e14。 <https://doi.org/10.1017/fmp.2021.15>；完整作者稿 <https://arxiv.org/abs/1502.04573>。 早期短文发表于 Nature 528 (2015), 207–211， <https://doi.org/10.1038/nature16059>。

<a id="ref-ads22"></a>

\[16\] S. A. Mir et al.， *Undecidability in spacetime geometry via the AdS/CFT correspondence* ， Physical Review D 113 (2026), L021904，2026-01-28。 <https://doi.org/10.1103/zqgf-6qp7>；<https://arxiv.org/abs/2601.22761>。

<a id="ref-adsComment22"></a>

\[17\] A. H. Budiyanto，*Comment on “Undecidability in spacetime geometry via the AdS/CFT correspondence”*， Physical Review D 114 (2026), 088901，2026-10-27。 <https://doi.org/10.1103/kfyd-zy1m>。

<a id="ref-adsReply22"></a>

\[18\] S. A. Mir et al.，*Reply to “Comment on ‘Undecidability in spacetime geometry via the AdS/CFT correspondence’ ”*， Physical Review D 114 (2026), 088902，2026-10-27。 <https://doi.org/10.1103/vjcd-bk2j>。

<a id="ref-cdp"></a>

\[19\] G. Chiribella, G. M. D’Ariano and P. Perinotti，  *Informational derivation of quantum theory* ，Physical Review A 84 (2011), 012311。 <https://doi.org/10.1103/PhysRevA.84.012311>；<https://arxiv.org/abs/1011.6451>。

<a id="ref-masanes"></a>

\[20\] L. Masanes and M. P. Müller，  *A derivation of quantum theory from physical requirements* ，New Journal of Physics 13 (2011), 063001。 <https://doi.org/10.1088/1367-2630/13/6/063001>；<https://arxiv.org/abs/1004.1483>。

<a id="ref-magnot"></a>

\[21\] J.-P. Magnot，  *Remarks on pairwise comparisons, transition amplitudes, and qubit states*  ， Physics Letters A 591 (2026), 131886，2026-09-28 卷期。 <https://doi.org/10.1016/j.physleta.2026.131886>； <https://arxiv.org/html/2605.04092v1>。既定 qubit 中的比较词典与 Gram 实现约束，并非完整重构。

<a id="ref-aberg"></a>

\[22\] J. Åberg， *Gluing of completely positive maps* ，2003 预印本，Propositions 2–3； 与相关研究合并发表于  *Subspace preservation, subspace locality, and gluing of completely positive maps* ， Annals of Physics 313 (2004), 326–367。 <https://doi.org/10.1016/j.aop.2004.04.013>； <https://arxiv.org/html/quant-ph/0302182v2>。

<a id="ref-vanrietvelde"></a>

\[23\] A. Vanrietvelde and G. Chiribella，  *Universal control of quantum processes using sector-preserving channels* ， Quantum Information and Computation 21 (2021), 1320–1352。 <https://doi.org/10.26421/QIC21.15-16-5>； <https://arxiv.org/abs/2106.12463>。

<a id="ref-rodriguez"></a>

\[24\] Á. Rodríguez Palacios， *One-sided division absolute valued algebras* ，Publicacions Matemàtiques 36(2B) (1992), 925–954。<https://doi.org/10.5565/PUBLMAT_362B92_12>；作者机构原文目录与摘要 <https://ddd.uab.cat/record/60222>。其单侧除法理论包括内积范数结论与无限维左单位实例。

<a id="ref-baez"></a>

\[25\] J. C. Baez， *The Octonions* ，Bull. Amer. Math. Soc. 39 (2002), 145–205。 作者原稿 <https://math.ucr.edu/home/baez/octonions/octonions.pdf>。 合成代数、Clifford 关系、spinor 与射影几何的既有背景；本稿不认领这些一般结构的历史优先权。

<a id="ref-r522"></a>

\[26\] Trureturing， *R5-022：有向面积与三元返回* ，定理 2.2，第 9 节。<https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/AURIC_R5_022_ORIENTED_AREA_AND_TERNARY_RETURN.md>。

<a id="ref-otf5"></a>

\[27\] Trureturing， *OTF-005：轴面几何、相位纤维与内生闭合* ，尤其 C1–C7、§§6、9–10。<https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/OTF_005_AXIS_PLANE_GEOMETRY_PHASE_FIBRES_AND_ENDOGENOUS_CLOSURE.md>。

<a id="ref-ashtekar"></a>

\[28\] A. Ashtekar and T. A. Schilling， *Geometrical Formulation of Quantum Mechanics* ，1997。 <https://arxiv.org/abs/gr-qc/9706069>。

<a id="ref-projector"></a>

\[29\] J. Mitscherling, A. Avdoshkin and J. E. Moore， *Gauge-invariant projector calculus for quantum state geometry and applications to observables in crystals* ，arXiv:2412.03637v2，2025-05-22 版本，§II.6.1。<https://arxiv.org/html/2412.03637v2>。

<a id="ref-berry"></a>

\[30\] M. V. Berry， *Quantal phase factors accompanying adiabatic changes* ，Proc. R. Soc. Lond. A 392 (1984), 45–57。 <https://doi.org/10.1098/rspa.1984.0023>；作者稿 <https://michaelberryphysics.wordpress.com/wp-content/uploads/2013/07/berry120.pdf>。

<a id="ref-ding"></a>

\[31\] Z. Ding, Y. Deng, S.-M. Fei et al.， *Universal conservation laws of the wave-particle-entanglement triad: theory and experiment* ，Light: Science & Applications 14, 82 (2025)，2025-02-12。<https://doi.org/10.1038/s41377-025-01759-4>。

<a id="ref-englert"></a>

\[32\] B.-G. Englert， *Fringe Visibility and Which-Way Information: An Inequality* ，Phys. Rev. Lett. 77 (1996), 2154。 <https://doi.org/10.1103/PhysRevLett.77.2154>。

<a id="ref-siddiqui"></a>

\[33\] M. A. Siddiqui， *Entanglement inference from quantum erasure and path discrimination* ，arXiv:2611.02679v1，2026-11-02 预印本，§§II–IV 及相应补充材料。<https://arxiv.org/abs/2611.02679>；全文 <https://arxiv.org/pdf/2611.02679>。本稿不将预印本标作已同行评审。

<a id="ref-q022-aronszajn"></a>

\[34\] N. Aronszajn.  *Theory of Reproducing Kernels* . Transactions of the American Mathematical Society 68(3) (1950), 337–404. DOI: 10.1090/S0002-9947-1950-0051437-7. Original-paper university mirror: <https://www.mit.edu/~9.520/spring09/Papers/aron.pdf>.

<a id="ref-c139cp"></a>

\[35\] Trureturing， *C139: Fixed-source comparators and native event boundary* ，定义 66.1、定理 67.1，第 68、74–85 节。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/AURIC_C139_FIXED_SOURCE_COMPARATORS_AND_NATIVE_EVENT_BOUNDARY.md>。

<a id="ref-watrous"></a>

\[36\] J. Watrous， *The Theory of Quantum Information* ，Chapter 2，尤其 Theorem 2.22。 作者原稿 <https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf>。

<a id="ref-waveprocess"></a>

\[37\] Trureturing， *递归关系观察：波、粒与事件* ，§335 的相干控制实例；§396、§400 对旧 §§336–338 的修订。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md>。

<a id="ref-uppm"></a>

\[38\] Trureturing， *UPPM-RG-001：几何计算中的内生关系与可验证证明* ，定理 4.3、4.6，例 5.3。 <https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/UPPM_RG_001_ENDOGENOUS_RELATIONS_AND_VERIFIABLE_PROOFS_IN_GEOMETRIC_COMPUTATION.md>。

<a id="ref-otf4"></a>

\[39\] Trureturing， *OTF-004：内生观察、注意、控制与余弦反馈* ，第 2、6–7 节。<https://github.com/the-omega-institute/trureturing/blob/c424643d6929e124fcd872a0e42f9f277b931521/docs/develop/theory/OTF_004_ENDOGENOUS_OBSERVATION_ATTENTION_CONTROL_AND_COSINE_FEEDBACK.md>。

<a id="ref-pw"></a>

\[40\] D. N. Page and W. K. Wootters，  *Evolution without evolution: Dynamics described by stationary observables* ，Phys. Rev. D 27 (1983), 2885–2892。 <https://doi.org/10.1103/PhysRevD.27.2885>。

<a id="ref-trinity"></a>

\[41\] P. A. Höhn, A. R. H. Smith and M. P. E. Lock，  *Trinity of relational quantum dynamics* ，Phys. Rev. D 104 (2021), 066001。 <https://arxiv.org/abs/1912.00033>。

<a id="ref-baumann"></a>

\[42\] V. Baumann and M. P. E. Lock， *Time delocalization and causality across temporal quantum reference frames* ，Phys. Rev. D 114, 086005 (2026)，2026-10-05。<https://doi.org/10.1103/9pl6-z9g4>。

<a id="ref-q022-tarski-decision"></a>

\[43\] A. Tarski.  *A Decision Method for Elementary Algebra and Geometry* , prepared for publication with J. C. C. McKinsey. RAND Report R-109, revised edition, 1951. <https://www.rand.org/pubs/reports/R109.html>.

<a id="ref-q022-marker"></a>

\[44\] D. Marker.  *Model Theory II: Quantifier Elimination* . MSRI introductory lectures, October 14, 2020. Author’s University of Illinois at Chicago notes: <https://homepages.math.uic.edu/~marker/MSRI-2.pdf>. Real closed fields and the o-minimality consequence.

<a id="ref-q022-richardson"></a>

\[45\] D. Richardson.  *Some Undecidable Problems Involving Elementary Functions of a Real Variable* . Journal of Symbolic Logic 33(4) (1968), 514–520. DOI: 10.2307/2271358. Original-paper university mirror: <https://www.math.tecnico.ulisboa.pt/~lgodin/Seminario/richardson.pdf>. Its expression-class assumptions are not silently replaced by the full first-order cosine language.
