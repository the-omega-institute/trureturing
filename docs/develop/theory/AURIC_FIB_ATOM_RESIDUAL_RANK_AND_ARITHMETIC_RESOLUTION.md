# Auric FIB-ATOM：隐藏关系的秩、面积与算术分辨率

从有限域反例，到不同观察切面的共同完成。

**参考输入与真源边界。** 本卷整理用户供应的同名文本，作为开放参考输入；Lean 声明、证明项及其公理闭包才承担本库的形式数学真值。下文全部新增散文陈述均为 `Claim status: open`，包括编号条目的纸面证明、实例和收束；此标记不声称形式不可判定。历史源码引文只描述固定来源，不赋予本卷当前 kernel 结论，也不宣告任何覆盖或冻结状态。

**来源。** Original author: unknown；Original model: unknown；delivery: mixed；接收日期：2026-10-10。混合交付只标识来源载体，不推断有人类作者署名。原文的数学陈述、证明和适用边界在本卷保留；文献归属依下面的数学引文，不主张全球优先性。

**数学引文 0.1（固定版本与复用范围）。** 固定项目快照为 [`14ef6ca31dac20465804d044ab021e5775ea1a9a`](https://github.com/the-omega-institute/trureturing/tree/14ef6ca31dac20465804d044ab021e5775ea1a9a)。以下简称均指该不可变版本，而不是可变分支。

| 标记 | 固定来源与数学使用范围 |
| --- | --- |
| R0 | [PR #14846](https://github.com/the-omega-institute/trureturing/pull/14846) 的 [SumFreeCodeDimensionRefutation 源码](https://github.com/the-omega-institute/trureturing/blob/14ef6ca31dac20465804d044ab021e5775ea1a9a/D5/S3/Arith/SumFreeCodeDimensionRefutation.lean)：第一节的具体函数、直线非零条件及两个核维数；不扩张到所引论文的其他问题。 |
| R1 | [FIB_RELATIONAL_CONTINUATION_GEOMETRY §7.1、§7.3、§7.5](https://github.com/the-omega-institute/trureturing/blob/14ef6ca31dac20465804d044ab021e5775ea1a9a/docs/develop/theory/FIB_RELATIONAL_CONTINUATION_GEOMETRY.md)：高到低原生窗口、独立错误标签、行为核及另行供应的原子动作。 |
| R2 | [FIB-ATOM 观察者与算术关系 §§2–5](https://github.com/the-omega-institute/trureturing/blob/14ef6ca31dac20465804d044ab021e5775ea1a9a/docs/develop/theory/AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md)：五函数展开、整数与模数、有限 $p$ 进精度及动作类型；这些机制作为既有项目推导复用。 |
| R3 | [金字塔续篇命题 10.5](https://github.com/the-omega-institute/trureturing/blob/14ef6ca31dac20465804d044ab021e5775ea1a9a/docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)：当前奇偶与同源后续守卫的联合关系。 |

**数学引文 0.2（历史反驳断言的精确范围）。** R0 取 $V(n)=\operatorname{Fin}(n)\to\mathbb Z/3\mathbb Z$；`SumFree s f` 指对每个线性独立方向族参数化的仿射 $s$ 平面，函数值之和非零。`parityMatrix n s f` 使用总次数不超过 $2s-1$ 的约化单项式行，再加 $f$ 的坐标行；`codeDim n s f` 是该校验线性映射核的有限维数。源码的 `claim` 逐量词为

$$
\begin{aligned}
\forall n,s\in\mathbb N,\quad &(2\le n)\Rightarrow(1\le s)\Rightarrow(s\le n-1)\Rightarrow\\
&\forall f,g:V(n)\to V(n),\\
&\operatorname{SumFree}(s,f)\Rightarrow\operatorname{SumFree}(s,g)\Rightarrow\\
&\operatorname{codeDim}(n,s,f)=\operatorname{codeDim}(n,s,g).
\end{aligned}
$$

固定源码含 `D5.S3.Arith.SumFreeCodeDimensionRefutation.result : ¬ claim`；私有见证为 $f(u,v)=(u^2+v^2,0)$ 和 $g(u,v)=(u^2,v^2)$，`witness_dimensions` 分别给 `codeDim 2 1 f = 5` 与 `codeDim 2 1 g = 4`。这些是历史来源中的精确声明，不是本卷新增的形式化结论。

**数学引文 0.3（归属与合同）。** 有限维秩—零化度、单纯形行列式体积、满秩整数矩阵的行列式—像指数、循环群乘法核和标准 Pauli 关系是 `literature-attested` 的经典中间输入，分别在其消费条目中使用。五模式与原生合同的既有推导依 R1–R3 复用。将剩余秩、提升体积、算术分辨率以及占位／行为边界的共同完成接回这个明确来源域，是用户供应的综合推导，按 `repo-derived` 的用途呈现而不主张新颖性认证。所谓“一阶 sum-free”的外部文献范围只取 R0 的已写定义，不把未给出全文定位的 Hou–Zhao 论文视为更强断言的出处。

**约定 0.4（载体与观察）。** 实几何和概率只在实数域及明确的同一非负归一化来源律上使用；任意域的函数空间、整数计数和模数代数计数分别定型。联合乘积和回复事件必须来自同一来源。原生三步窗口与额外单原子动作分别定型；代数可逆性不自动提供物理接口、重置、独立样本或稳定的噪声恢复。以下各节的 `open` 同时约束其正文与解释，不以图形、维数或命名代替这些条件。

**有限域反例提供了一个接回金字塔的切入点：两个对象满足同一种“局部合法性”，并不意味着它们提供了同样多的独立信息。真正决定剩余自由度的，是新增读数相对于已有读数增加了多少秩。**

沿着这个方向，可以建立三项具体联系：

$$
\boxed{\text{同一项四角关系，同时控制新增维数、提升体积和模素数下的可恢复性。}}
$$

$$
\boxed{\text{一个实数意义上充分的二阶读数，到了模 }2\text{ 或模 }5\text{ 下，可能完全失去新增信息。}}
$$

$$
\boxed{\text{同样是三个独立统计坐标，一种形成占位金字塔，另一种形成行为四面体；两者保留的来源区别并不相同。}}
$$

## 一、有限域结果说明：同类不等于同维，合法性不等于信息量

Claim status: open

数学引文 0.2 的具体反例定义在九点平面：

$$
\Omega=\mathbb F_3^2.
$$

取：

$$
\boxed{f(u,v)=(u^2+v^2,0),\qquad g(u,v)=(u^2,v^2).}
$$

这里取 $n=2,s=1$；“一阶 sum-free”指：**沿每条仿射直线，对函数值求和，结果都不是零向量。** 它不是通常集合论里“不含 $a+b=c$”的那个同名条件。固定来源的 `SumFree 1` 采用前一种含义。

### theorem 1（两份函数具有相同的直线非零性质，却增加不同数量的独立读数）

Claim status: open

设已有读数空间为：

$$
\mathcal R=\operatorname{span}_{\mathbb F_3}\{1,u,v\}.
$$

则：

$$
\boxed{\dim\bigl(\mathcal R+\operatorname{span}\{f_1,f_2\}\bigr)=4,}
$$

$$
\boxed{\dim\bigl(\mathcal R+\operatorname{span}\{g_1,g_2\}\bigr)=5.}
$$

因此，相应九坐标校验核的维数分别为：

$$
\boxed{9-4=5,\qquad9-5=4.}
$$

**证明。**

一条仿射直线可写为：

$$
(u,v)+t(a,b),\qquad t\in\mathbb F_3,
$$

其中 $(a,b)\ne(0,0)$。

利用：

$$
\sum_t1=0,\qquad\sum_tt=0,\qquad\sum_tt^2=-1,
$$

得到：

$$
\sum_tf((u,v)+t(a,b))=(-(a^2+b^2),0),
$$

$$
\sum_tg((u,v)+t(a,b))=(-a^2,-b^2).
$$

在 $\mathbb F_3$ 中，平方只有零与一。非零方向使两式都不为零。

但是，$f$ 只增加一个非零函数 $u^2+v^2$；$g$ 增加的是两个函数 $u^2,v^2$。

在九点上，函数：

$$
1,u,v,u^2,v^2
$$

线性独立。可通过依次代入 $(0,0),(\pm1,0),(0,\pm1)$ 直接验证。

最后使用秩—零化度公式，得到两个核维数。证毕。

这是仓库反例的核心机制。PR #14846 将结果定位为 Hou–Zhao 问题的维数部分；这里引用的是固定源码中的具体断言，不扩张为对该论文其他问题或全球优先性的判断。

**对金字塔最重要的启发是：不能只问“这个新公式是否也满足我们的分类规则”，还要问“它真的增加了一项此前没有的关系吗”。**

---

## 二、把“新增信息”定义为相对于旧边界的剩余秩

Claim status: open

### 定义 1（线性读出边界）

设有限来源域为 $\Omega$，大小为 $N$，系数域为 $K$。

已经保留的函数张成：

$$
\mathcal R\subseteq K^\Omega.
$$

对来源权重向量 $a=(a_s)_{s\in\Omega}$，读数为：

$$
\langle r,a\rangle=\sum_sr(s)a_s,\qquad r\in\mathcal R.
$$

未被这些读数区分的线性变化为：

$$
\boxed{\mathcal N(\mathcal R)=\{d:\langle r,d\rangle=0\quad\forall r\in\mathcal R\}.}
$$

在实概率模型中，$d$ 是两份概率律的差；实际扰动还须满足非负性。
在有限域模型中，$a$ 是代数坐标或计数余数，**不将有限域元素直接当作非负概率。**

### theorem 2（新增读口真正减少的自由度，等于它们在商空间中的秩）

Claim status: open

增加函数 $f_1,\ldots,f_m$，令：

$$
\mathcal R'=\mathcal R+\operatorname{span}\{f_1,\ldots,f_m\}.
$$

则：

$$
\boxed{\dim\mathcal N(\mathcal R)-\dim\mathcal N(\mathcal R')=\dim\operatorname{span}\{[f_1],\ldots,[f_m]\}}
$$

其中 $[f_i]\in K^\Omega/\mathcal R$。

**证明。**

$$
\dim\mathcal N(\mathcal R)=N-\dim\mathcal R.
$$

两式相减，所得正是 $\dim\mathcal R'-\dim\mathcal R$。这等于新增函数在商空间中的维数。证毕。

因此：

$$
\boxed{\text{新增公式数量}\ne\text{新增独立关系数量}.}
$$

重复计算旧函数、把旧函数可逆地换坐标、加入旧函数的线性组合，都不会减少这类隐藏自由度。这也正是校验矩阵中重复行不改变码的原因。[GUAVA 3.6 文档，第 5 章](https://web.mit.edu/sage/export/guava-3.6/doc/chap5.html)

---

## 三、FIB 五模式中，全部新增关系只需检验一个四角差

Claim status: open

沿用：

$$
\Sigma=\{\mathsf F[\varnothing],\mathsf F[1],\mathsf F[2],\mathsf F[3],\mathsf F[1,3]\}.
$$

记低端、高端、中间占位为 $x,y,z$，满足：

$$
x^2=x,\quad y^2=y,\quad z^2=z,\quad xz=yz=0.
$$

五个模式依次是：

$$
(0,0,0),\quad(1,0,0),\quad(0,0,1),\quad(0,1,0),\quad(1,1,0).
$$

已有边界函数为：

$$
\boxed{\mathcal R_0=\operatorname{span}\{1,x,y,z\}.}
$$

既有五模式推导 [R2，§§2–3] 给出：这个边界能给出三个占位均值，但条件更新通常还会读取 $xy$。

### 定义 2（目标的四角差）

对五模式函数 $f$，定义：

$$
\boxed{J_f=f_{\varnothing}+f_{13}-f_1-f_3.}
$$

### theorem 3（$J_f$ 是新增关系的完整坐标）

Claim status: open

在任意域 $K$ 上：

$$
\boxed{\begin{aligned}
f={}&f_{\varnothing}+(f_1-f_{\varnothing})x+(f_3-f_{\varnothing})y\\
&+(f_2-f_{\varnothing})z+J_fxy.
\end{aligned}}
$$

因此：

$$
\boxed{f\in\mathcal R_0\iff J_f=0.}
$$

若 $J_f\ne0$，则：

$$
\boxed{\operatorname{span}\{1,x,y,z,f\}=K^\Sigma.}
$$

**证明。** 在五个合法模式上逐项代入即可。$xy$ 只有在联合模式上为一，所以其系数恰好是四角差。证毕。

这里秩包含常数函数一。四个函数对应的是归一化以后三个统计坐标，不是四根物理空间轴。

### 三角形为何再次出现？

已有评价矩阵的核为：

$$
\boxed{\ker\begin{pmatrix}1\\x\\y\\z\end{pmatrix}=K(1,-1,0,-1,1).}
$$

每个非零核向量都恰好涉及四个模式。

因此：

$$
\boxed{\text{任何三个纯模式之间，都不存在这种非零仿射再分配；}}
$$

$$
\boxed{\text{四个底角第一次能够在保持边界的同时互相补偿。}}
$$

三角形的特殊性在这里是**没有四角冗余**，而不是三条边天然包含所有关系。

---

## 四、二阶读数是否有效，要看它有没有真正碰到两个端点

Claim status: open

### 定义 3（两个线性读口的剩余配对）

取：

$$
\ell=ax+by+cz,\qquad m=a'x+b'y+c'z.
$$

定义：

$$
\boxed{\mathcal B(\ell,m)=J_{\ell m}.}
$$

### theorem 4（两个读口的新增二阶关系，只来自交叉端点）

Claim status: open

$$
\boxed{\mathcal B(\ell,m)=ab'+a'b.}
$$

特别地：

$$
\boxed{J_{\ell^2}=2ab.}
$$

**证明。**

展开乘积，使用 $x^2=x,y^2=y,z^2=z,xz=yz=0$。平方项仍在 $\mathcal R_0$ 中，涉及中间与端点的交叉项归零，只有 $(ab'+a'b)xy$ 留下。证毕。

这解释了一个容易被公式外观掩盖的区别：$x^2,y^2,z^2$ 看起来是二阶，实际没有增加任何关系，因为它们分别等于 $x,y,z$。

而 $xy$ 才是当前模型真正缺少的共同项。

### 换到不同算术切面，结论会变化

若系数域特征不是二，且 $ab\ne0$，那么 $\ell^2$ 能补全隐藏方向。

但在特征二中：

$$
\boxed{J_{\ell^2}=0\quad\text{对全部线性 }\ell.}
$$

这时 $(a+b)^2=a^2+b^2$，自乘无法产生所需的交叉项。

不过：

$$
\boxed{J_{xy}=1}
$$

仍然成立。

**所以，特征二下失效的是“通过平方取得交叉项”这条方法，不是共同关系 $xy$ 不存在。**

该剩余配对在两个端点系数上为：

$$
\mathcal B((a,b),(a',b'))=ab'+a'b.
$$

在特征二中，它满足 $\mathcal B(v,v)=0$，却不恒为零。这是一种交替配对，不是正定距离。不能把“自配对为零”解释成“没有信息”。

---

## 五、同一个 $J_f$，竟然同时控制体积、整数缺口与素数盲区

Claim status: open

这里把四角关系的秩与提升体积、整数格点和模数读出连接起来。

### 定义 4（提升后的关系体）

取实值函数 $f:\Sigma\to\mathbb R$，令 $v_s=(x(s),y(s),z(s))$。把每个模式提升为 $(v_s,f_s)\in\mathbb R^4$，定义：

$$
\mathcal K_f=\operatorname{conv}\{(v_s,f_s):s\in\Sigma\}.
$$

如果 $f$ 没有新增关系，这五个提升点仍落在同一个三维仿射空间中。

### theorem 5（提升体积与新增关系系数相同源）

Claim status: open

在固定坐标单位下：

$$
\boxed{\operatorname{Vol}_4(\mathcal K_f)=\frac{|J_f|}{24}.}
$$

**证明。** 用齐次坐标组成五阶矩阵，其行分别为 $1,x,y,z,f$。从最后一行减去 theorem 3 中的前四项，最后一行只剩 $J_fxy$。

直接计算基础矩阵：

$$
\det\begin{pmatrix}1\\x\\y\\z\\xy\end{pmatrix}=-1.
$$

所以提升行列式为 $-J_f$。四维单纯形体积是其绝对值除以 $4!=24$。证毕。

现在不再用实概率，而用整数模式计数：

$$
n=(n_{\varnothing},n_1,n_2,n_3,n_{13})\in\mathbb Z^5.
$$

保留：

$$
N=\sum_sn_s,\quad A=\sum_sx(s)n_s,\quad B=\sum_sy(s)n_s,\quad C=\sum_sz(s)n_s,
$$

以及 $F=\sum_sf_sn_s$。完整边界映射记为 $B_f:n\mapsto(N,A,B,C,F)$；这里的整数定义域是全部 $\mathbb Z^5$，不预设非负性。

由 theorem 3：

$$
\boxed{F-f_{\varnothing}N-(f_1-f_{\varnothing})A-(f_3-f_{\varnothing})B-(f_2-f_{\varnothing})C=J_fn_{13}.}
$$

### theorem 6（整数恢复与模数恢复，由 $J_f$ 的可逆性决定）

Claim status: open

假设 $f_s\in\mathbb Z$。

当 $J_f\ne0$，完整整数边界映射的像在 $\mathbb Z^5$ 中的指数为：

$$
\boxed{|J_f|.}
$$

取整数 $m\ge2$，在完整代数计数域 $(\mathbb Z/m\mathbb Z)^5$ 上，每个处于 $B_f$ 像中的边界恰有：

$$
\boxed{\gcd(m,J_f)}
$$

个原像。因此：

$$
\boxed{\text{模 }m\text{ 唯一恢复}\iff\gcd(m,J_f)=1.}
$$

**证明。**

前四个边界相同的两个计数向量，只能相差 $t(1,-1,0,-1,1)$。

增加第五个读口后，剩余条件为 $J_ft=0\pmod m$。这个方程恰有 $\gcd(m,J_f)$ 个解。

整数情形则由前面的齐次矩阵行列式 $\pm J_f$，或直接化成四个自由整数坐标加一个 $J_ft$，得到像指数。证毕。

若另加非负计数、固定样本数或其他可达性限制，原像须再与该受限域相交；上面的 $\gcd(m,J_f)$ 不自动成为受限原像数。整数像指数也不同于某个非负计数集合的大小。

所以，同一个数 $J_f$ 同时表示：

$$
\boxed{\begin{aligned}
\text{实几何中}&:\text{提升体积的尺度};\\
\text{整数模型中}&:\text{可达边界的格点指数};\\
\text{模素数模型中}&:\text{新增关系是否消失}.
\end{aligned}}
$$

但体积变大不代表信息维数增加得更多：$J_f=1$ 与 $J_f=1000$ 都只增加一维。其数值还依赖读口单位；不能把任意缩放当成提高信息效率。

---

## 六、$p$ 进精度的损失，可以直接读出是哪几位

Claim status: open

设 $J_f\in\mathbb Z\setminus\{0\}$，$p$ 为素数，$e=v_p(J_f)\ge0$，$J_f=p^eu$，$p\nmid u$；有限精度指数 $k\ge1$。

### corollary 6.1（有限 $p$ 进精度下，补充读口的损失由 $e$ 控制）

Claim status: open

在模 $p^k$ 下，方程 $J_ft=r$ 对每个可达 $r$ 有：

$$
\boxed{p^{\min(e,k)}}
$$

个解。若 $k>e$，它只能确定：

$$
\boxed{t\bmod p^{k-e}.}
$$

**证明。** 非零因子 $u$ 可逆，剩下 $p^et=r$；其核大小正是所列值。证毕。

这给“分辨率不足”一个很具体的语义：某个实数读口可以精确补出一项关系，却可能需要多取得若干位整数精度，才能在 $p$ 进读口中恢复同一项关系。

精确完整的 $p$ 进整数上，非零 $J_f$ 的乘法仍然是单射；这里丢失的是**固定有限精度下的区分能力**，不是无限极限中自动存在非零核。

---

## 七、代回 FIB 数量：为什么素数二、五会成为不同的读口障碍？

Claim status: open

对同一个初始五模式来源，其组成是 $c_s=(x+y,\ y+z)^{\mathsf T}$。

取：

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad q=(2,3),
$$

定义代数阶段读数 $N_k(s)=qM^kc_s$。

特别地：

$$
\boxed{N_0=2x+5y+3z,}
$$

$$
\boxed{N_1=3x+8y+5z,}
$$

$$
\boxed{N_3=8x+21y+13z.}
$$

固定来源 [R1，定义 7.1、7.5] 的原生三位窗口推进使用 $S=M^3$，所以当前与继续空贡献窗口的阶段读数为 $N_0,N_3,N_6,\ldots$。本卷下标 $k$ 始终计单原子代数阶段；$N_1=qMc_s$ 是一原子阶段，$N_3=qSc_s$ 才是一个窗口阶段。既有卷若按窗口取样把 $qSc_s$ 记为局部 $N_1$，那是另一套局部下标，不与本卷的 $N_1$ 混用。一原子步接口是另行声明的扩展动作，不能当作原窗口读者已经免费提供。

由 theorem 4：

| 补充读口 | 四角系数 $J$ | 模素数下丢失新增秩的情形 |
|---|---:|---|
| $N_0^2$ | $20$ | $p=2,5$ |
| $N_1^2$ | $48$ | $p=2,3$ |
| $N_3^2$ | $336$ | $p=2,3,7$ |
| $N_0N_1$ | $31$ | $p=31$ |
| $xy$ | $1$ | 没有素数障碍 |

### 一个最小计数例子

比较两份各含两个样本的来源：

$$
n^{(A)}=\delta_{\varnothing}+\delta_{13},\qquad n^{(B)}=\delta_1+\delta_3.
$$

它们具有相同总数与占位计数 $(N,A,B,C)=(2,1,1,0)$。

但 $N_0^2$ 的总读数分别为 $49$、$4+25=29$。差为 $20$。在整数中可以区分；模二或模五后完全相同。

**素数在这里不是某个顶点的素因子，而是“一个新读口能否切开原有来源纤维”的障碍素数。**

### 两个平方读口也未必消除全部算术障碍

因为 $\gcd(20,336)=4$，只增加 $N_0^2,N_3^2$，仍留下共同的二进精度损失。

实际上：

$$
\boxed{4xy=17N_0^2-N_3^2-4x+16y+16z.}
$$

这是一项逐模式恒等式。

而加入同源的混合读数 $N_0N_1$ 后，$\gcd(20,31)=1$，可以得到不需要除法的恢复：

$$
\boxed{xy=14N_0^2-9N_0N_1-2x+10y+9z.}
$$

**证明。** 展开 $N_0N_1=6x+40y+15z+31xy$，与 $N_0^2=4x+25y+9z+20xy$ 联立即得。证毕。

这不是免费取得混合矩：必须保存同一来源上的两个读数或供应相应联合实验。分别取得两个边缘分布，不等于取得它们的乘积平均。

此外，这个整数恢复式含有较大正负系数，可能放大噪声。**算术上可逆与数值上稳定，仍须分别检验。**

---

## 八、只旋转原来的标量读口，可能永远没有新增信息；保留接缝却能改变答案

Claim status: open

取 $F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$。沿原生三步阶段：

$$
N_{3j}=F_{3j+3}x+F_{3j+5}y+F_{3j+4}z.
$$

Fibonacci 数模二每三步重复，因此：

$$
\boxed{N_{3j}\bmod2=y+z\qquad\forall j\ge0.}
$$

这里 $y+z$ 本来就只能为零或一。

所以，**只保留这些空窗口阶段的标量奇偶读数，无论重复多少次，再对这些二值读数作多少单变量非线性加工，都不能新增 $xy$ 关系。**

但是不能由此说：原生模二读者对 $xy$ 完全失明。它还有一个真实接口——拒绝结果。

**原生合同（固定来源 [R1，定义 7.1]）。** 从初态 $(\eta,C)=(0,0)$ 高到低读入一个合法窗口；印刷三位仍为低、中、高 $(x,z,y)$。$\eta$ 是历史接缝，$z$ 是当前中位，两者不混用。对输入 $\sigma$，先检查 $\eta y(\sigma)=0$；合法时

$$
C'=SC+d_\sigma,\qquad \eta'=x(\sigma),\qquad
S=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad q=(2,3),
$$

并回复 $qC'$；非法时进入独立的吸收错误态 $\bot$，其错误标签不同于所有数量余数。按 $(\varnothing,1,2,3,13)$ 的模式顺序，

$$
(d_\varnothing,d_1,d_2,d_3,d_{13})=
\bigl((0,0)^{\mathsf T},(1,0)^{\mathsf T},(0,1)^{\mathsf T},(1,1)^{\mathsf T},(2,1)^{\mathsf T}\bigr).
$$

下面只对从该初态实际读入一个模式后得到的五个当前来源使用这份合同；不把任意长历史的接缝认作某个单窗占位。

### theorem 7（原生守卫与当前奇偶的共同记录，可以直接读取联合模式）

Claim status: open

考虑五个模式各自读入后形成的当前可达状态。保存当前模二数量，再输入原生高端模式 $[5]=\mathsf F[3]$。

项目的守卫会拒绝，当且仅当当前历史接缝为一。对于这五个单窗来源，该接缝恰为 $x$。

因此：

$$
\boxed{\mathbf1_{\{\text{当前余数}=1\}}\mathbf1_{\{\text{下一步拒绝}\}}=(y+z)x=xy.}
$$

**证明。** 初接缝为零，五个首次模式都合法；更新后接缝为 $x$，当前数量模二为 $q c_s\bmod2=y+z$。追加 $[5]$ 的最高位为一，故拒绝恰当且仅当 $x=1$。两个同源事件指示相乘，再使用 $xz=0$，得到 $(y+z)x=xy$。证毕。

由上述合同逐模式代入得到回复表：

| 初始模式 | 当前模二数量 | 追加 $[5]$ 后 |
|---|---:|---|
| $\mathsf F[\varnothing]$ | 0 | 1 |
| $\mathsf F[1]$ | 0 | 拒绝 |
| $\mathsf F[2]$ | 1 | 0 |
| $\mathsf F[3]$ | 1 | 0 |
| $\mathsf F[1,3]$ | 1 | 拒绝 |

**联合模式恰好对应“先读到一，随后被拒绝”。** 这是既有 [R3，命题 10.5] 的奇偶—守卫关系在模二下的应用，不主张该接口关系首次出现于本卷。

这里没有新增非法的平方根或逆动作；使用的是原协议已有的守卫。但必须保留**同一次来源上的两个回复**，不能把拒绝标签丢掉，也不能把两侧独立采样的记录冒充共同档案。

这是一项逐可达状态的恒等式，并不自动供应未知模式的制备、重复实验或精确概率估计。

---

## 九、三维边界的对照：占位金字塔与行为四面体，维数相同却互不包含

Claim status: open

上一节的同源记录还给出另一种边界对照。

在原生模二窗口合同中 $M^3\equiv I\pmod2$。

同接缝的两个组成，如果只差第一组成分量，其后续所有共同输入都会保持相同的第二分量；数量读口 $q\equiv(0,1)\pmod2$ 无法区分它们。

因此，单窗模式 $\mathsf F[2]$ 与 $\mathsf F[3]$ 具有相同的全部后续行为。其他三种模式可由上一节的回复区分。这也是固定来源 [R1，定理 7.3] 中同接缝行为核 $\{(a,0):2a=0\bmod m\}$ 在 $m=2$ 和这五个单窗来源上的限制。

### 定义 5（两个不同的边界函数空间）

在任意系数域 $K$ 上比较以下两个函数空间；模式的行为等价仍由前述原生模二合同定义。占位几何边界：

$$
\boxed{\mathcal R_{\mathrm{geo}}=\operatorname{span}\{1,x,y,z\}.}
$$

原生模二行为边界，在这五个当前来源上为：

$$
\boxed{\mathcal R_{\mathrm{beh}}=\operatorname{span}\{1,x,y+z,xy\}.}
$$

后者是四个行为类上的全部函数。

### theorem 8（两个边界秩都为四，但遗漏不同；合并以后恢复全部五模式概率）

Claim status: open

$$
\boxed{\dim\mathcal R_{\mathrm{geo}}=\dim\mathcal R_{\mathrm{beh}}=4,}
$$

$$
\boxed{\dim(\mathcal R_{\mathrm{geo}}\cap\mathcal R_{\mathrm{beh}})=3,}
$$

$$
\boxed{\mathcal R_{\mathrm{geo}}+\mathcal R_{\mathrm{beh}}=\operatorname{span}\{1,x,y,z,xy\}=K^\Sigma.}
$$

**证明。**

两者的公共部分包含 $1,x,y+z$。

几何边界区分 $y$ 与 $z$，但没有 $xy$。行为边界保留 $xy$，但不能区分两个具有同样 $y+z$ 的中间、高端模式。

直接比较五个模式上的函数值，得到所列维数。证毕。

### 两种几何外形

几何解释取 $K=\mathbb R$，并对同一份非负、归一化的五模式概率律求均值。令 $X=\mathbb E[x],Y=\mathbb E[y],Z=\mathbb E[z],\kappa=\mathbb E[xy]$。几何边界 $(X,Y,Z)$ 形成熟悉的三维金字塔。

行为边界 $(X,W,\kappa)$，其中 $W=\mathbb E[y+z]$，的纯类顶点为：

$$
(0,0,0),\quad(1,0,0),\quad(0,1,0),\quad(1,1,1).
$$

它们形成一个体积为 $1/6$ 的四面体。

但这座四面体已经把两个不同原模式合并成一个行为类。

**因此：“边界是三维”不够说明它保留了什么；“三维体是单纯形、混合分解唯一”也只意味着行为类概率唯一，不意味着原始模式概率唯一。**

这与第一节的有限域码结果形成了呼应：

$$
\boxed{\text{同一种合法性质，不一定同秩；}}
$$

$$
\boxed{\text{即使同秩，也不一定保存同一批关系。}}
$$

---

## 十、量子里也有“平方不增加信息”，但原因不能与模二混为一谈

Claim status: open

原文给出的量子续篇条件是标准 Pauli 实现：$a=-iX,b=-iY$，$X^2=Y^2=Z^2=I$，$XY=iZ,YX=-iZ$。此节的 $X,Y,Z$ 是复二维 Hilbert 空间上的 Pauli 算符，与第九节的占位均值同名而不同型。

以下只以这些明确写出的非交换关系为假设。这是一份额外的具体实现，不是五模式自身自动给出的物理操作；也不把未给出可定位引文的量子续篇升级为本卷结论的独立证据。

### theorem 9（同一方向组合的平方可以完全看不见态，次序关系却能显露第三个量）

Claim status: open

对实数 $s,t$：

$$
\boxed{(sX+tY)^2=(s^2+t^2)I.}
$$

但：

$$
\boxed{\frac{XY-YX}{2i}=Z.}
$$

**证明。** 使用 $X^2=Y^2=I$ 与 $XY+YX=0$。证毕。

所以，反复取得 $(sX+tY)^2$ 的平均值，并不能恢复未知态的 $Z$ 分量；它始终只返回与态无关的常数。

例如 $\varrho_\pm=\frac12(I\pm Z)$ 具有相同的 $X,Y$ 均值零，但 $Z$ 均值为 $\pm1$。

**这与有限域例子的共同方法论是：不要用“二阶”这个名字判断信息量，要计算新增函数或算符是否真的超出旧空间。**

但两种抵消机制不同：

$$
\boxed{\text{模二平方：交换代数中 }2=0;}
$$

$$
\boxed{\text{Pauli 平方：非交换乘积的反对易抵消}.}
$$

不能因此把有限域算术直接认作量子理论。

而且，形式上写出 $Z=[X,Y]/(2i)$，不表示只知道两个平均数就能免费取得它。必须供应实际可执行的测量或相干控制。原文所援引的续篇断言另行区分单独通道与相干比较；这里保留该操作条件，不从两个期望值推出相干比较接口。

---

## 十一、观察者内生的分类，应该检查四件不同的事

Claim status: open

以上结果提示，研究一个候选“新关系”时，可以依次建立四层判据。

**第一，代数上是否真的新增。**

$$
\boxed{[f]\ne0\quad\text{于 }K^\Sigma/\mathcal R.}
$$

五模式中就是检验 $J_f$。

**第二，当前分辨率是否仍能读取这个新增量。**

整数精确可逆、实数可逆、模 $p^k$ 可逆，是不同条件。本篇的 $J_f$ 与 $v_p(J_f)$ 将它们分开。

**第三，实际操作是否允许取得它。**

平方、联合乘积、原子步、窗口步、拒绝结果，各有不同合同。第八节说明，保留实际守卫有时比继续精炼同一种标量更有效。

**第四，得到的边界是否对未来仍然闭合。**

项目的要求是：相同摘要经过同一个允许动作，必须继续给出相同的后继摘要与回复；否则它只对当前目标充分。

在有限经典状态域上，约定概率列向量按 $a'=K_o a$ 更新，$K_o$ 是对应的列随机核；则对期望边界 $\mathcal R$ 的闭合条件为：

$$
\boxed{K_o^{\mathsf T}\mathcal R\subseteq\mathcal R.}
$$

但即使五模式概率已经完整，原树括号、相干相位以及以后会再次作用的共同环境，仍然可能不在这个来源域里。原文所援引的附件还给出两项断言：经典概率相同仍可有不同的相干响应；同一个以后仍会参与作用的隐藏环境，不能被当作每一步重新准备的新环境。这里将它们保留为开放的来源断言和适用边界，不宣称已从本卷的有限经典核证明了这些额外实现中的结论。

**有限窗口的完成，不等于整个递归来源的完成。**

---

## 实质收束：同一隐藏关系的不同读出层

Claim status: open

把同一条四角关系写成带符号的模式重分配：

$$
\boxed{\mathsf F[\varnothing]+\mathsf F[1,3]-\mathsf F[1]-\mathsf F[3]}
$$

这里带正负号的模式记号表示 $h=(1,-1,0,-1,1)$，不是声称这些来源对象在原语法中可以相减。它在几种不同读口下有如下表现。

| 读出层 | 同一条隐藏关系的表现 |
|---|---|
| 函数空间 | 唯一剩余方向，坐标为 $J_f$ |
| 实几何 | 提升体积为 $|J_f|/24$ |
| 整数边界 | 可达格点指数为 $|J_f|$ |
| 模数读出 | 完整代数计数域上的可达边界原像数为 $\gcd(m,J_f)$ |
| 有限 $p$ 进精度 | 损失位数由 $v_p(J_f)$ 控制 |
| FIB 阶段读取 | 三步取样可以重复同一盲区 |
| 原生后续 | 保存数量与拒绝关系，可以重新读出 $xy$ |
| 不同观察切面 | 相同秩可以遗漏完全不同的来源区别 |

最值得保留的三个式子是：

$$
\boxed{f=\text{已有仿射读数}+J_fxy;}
$$

$$
\boxed{\operatorname{Vol}_4(\mathcal K_f)=\frac{|J_f|}{24},\qquad|\ker B_f\bmod m|=\gcd(m,J_f);}
$$

$$
\boxed{\mathcal R_{\mathrm{geo}}+\mathcal R_{\mathrm{beh}}=K^\Sigma,\qquad\mathcal R_{\mathrm{geo}}\ne\mathcal R_{\mathrm{beh}}.}
$$

有限精确检查只能约束实际覆盖的实例或后缀，不能替代一般证明，也不赋予本卷 Lean kernel 结论。

**隐藏关系可以进一步分成三个可分别检验的问题：**

$$
\boxed{\text{它有没有独立增加？}\quad\text{当前精度能不能看见？}\quad\text{实际后续会不会重新读取？}}
$$

三角形表示某些最小关系没有内部仿射补偿；正方形第一次提供四角再分配；金字塔保留三个占位均值，却未必保留联合项。换到真实行为切面，同一批原子又可能形成四面体，但丢掉另一种区别。

**因此，“多找角度”最有效的含义，不是不断旋转一份已经失真的数据，而是寻找保留不同核的实际读口，并证明它们的共同边界足以恢复指定来源、分辨率与未来任务。**

## 追加锚（本行以下为增补区）
