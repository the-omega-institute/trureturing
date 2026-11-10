# 二元参考、内生充分约化与量子可见代数

从规范补全到完全正实现、模相容与关系动力学

**AURIC v94：一个完整候选的定义、定理与反向审计**

项目连续研究稿

2026 年 11 月 3 日（新加坡）

## 摘要

v93 已给出任意有限量子读出纤维中的唯一最小相对熵补全。
v94 研究它什么时候能够由同一个量子过程对全部输入实现。
本轮唯一候选 C94 要求一种全域线性的局部约化：保留当前全部读数，
把同读数的输入送到同一个完整局部输出，固定忠实的内部参照，
并且在只附加一个二元量子参考时仍保持正性。

不预设可见关系对乘法闭合，也不预设全部完全正性。
证明上述条件成立，当且仅当可见关系的复线性张成是普通有限维算符代数，
并且内部参照的模流保持该代数。
约化于是唯一，具有块偏迹与隐藏参照重置形式，自动完全正，
并在每一个读出纤维上恰好实现 C93 的规范补全。

反向分析以具体二态、正缺额和归一二元三维报告说明各条件的用途：
删去二元参考检查会出现负概率；参照不忠实时，正缺额可藏在零支撑中；
可见关系成为代数以后，参照仍必须与这项切分相容。
内部等距实现把被约去的区别保留在 $\Omega$ 的记录与关联中。
再证明动态自治与规范态协变的区别、嵌套分辨率的塔式相容，
并说明它们怎样接到项目已有的量子状态、效果、门、复合与时间重建。

本文是条件明确的有限维理论接续；数学机制属于条件期望与量子充分性。
本轮新内容指项目内的接续与证明组织，不主张这些标准数学机制首次发现。
全部数学采用解析证明与独立解析复核，未运行数学程序、CAS、数值求值、枚举或测试。

## 目录

- [1. 项目接续：从能选代表到能够实现代表](#section-1)
- [2. 候选的地位：关系内部的约束仍要有明确前件](#section-2)
- [3. 有限读出、同资料关系与一个二值量子参考](#section-3)
- [4. 唯一候选 C94：二值参考下的内生规范回缩](#section-4)
- [5. 二态关系怎样锁定对偶过程的像](#section-5)
- [6. 二值参考、平方缺额与忠实参照](#section-6)
- [7. 正反与相位比较迫使通常乘法闭合](#section-7)
- [8. 有限可见代数的块结构](#section-8)
- [9. 双模关系唯一确定加权条件期望与块重置](#section-9)
- [10. 参照的模关系何时保留同一可见代数](#section-10)
- [11. 哪些 C93 规范补全可以成为同一全域量子门](#section-11)
- [12. 可见压缩、精确信息分解与 Petz 恢复接口](#section-12)
- [13. 反向审计：同一个平方缺额怎样暴露不同前件](#section-13)
- [14. 其余条件的反例：保留、融合与参照稳定各管什么](#section-14)
- [15. 相干二支复用，把遗漏的第三轴直接读出来](#section-15)
- [16. 补齐一个逻辑三轴，与保留全部重叠边际，要求不同](#section-16)
- [17. 内部等距实现：局部融合没有删除整个 $\Omega$ 的区别](#section-17)
- [18. 未来自治与规范代表的动态交换](#section-18)
- [19. 相对锚下的精确酉协变条件](#section-19)
- [20. 完整历史中，哪些实际整理可以随时插入](#section-20)
- [21. 关系层级就是分辨率层级：共同参照下的塔式相容](#section-21)
- [22. 怎样接回现有量子力学公理](#section-22)
- [23. 球、轨迹、参照与关系场：保留直觉的准确形式](#section-23)
- [24. 近期研究的连接与本轮完整白话](#section-24)
- [来源、版本与核读范围](#references)

<a id="section-1"></a>

## 1. 项目接续：从能选代表到能够实现代表

<a id="sec-c94-position"></a>

本轮由 v93 递增到 v94。项目当前公开首页的默认分支为 `dev`；
其目标恢复判据将“目标能由当前读数恢复”写成同一纤维上目标恒定，
并把失败严格落实成一对被当前读口合并、却有不同目标值的状态
 [1](#ref-currentrepo)、[2](#ref-targetcriterion)。
这正是本轮反向分析采用的二态形式。
已阅读相关声明及源码，未执行 Lean 构建，不据此认证仓库其余证明。

当前页面没有取得可固定的最新提交 SHA，API 读取亦未成功。
本轮理论核对采用已取得的
`c63ab162315fddd0801cbe9f47dbf3eda6e13360`
快照（2026 年 11 月 2 日），并与当前公开页面的声明分开记录。
Atlas III 已有读出纤维宽度、线性预测闭包、全态动态自治、
逐分支历史闭包和可见代数的自治酉结构 [3](#ref-atlas)。
$\Omega$ 静态相容纤维理论已经区分统计逆、物理恢复与含全部目标的等价关系，
并包含实部投影的非完全正例子 [4](#ref-omega)。
这些内容在本文中作为既有接口与已有反例使用。

v93 的 C93 则解决规范推断：在一份合法读出纤维内，
用内部参照 $\tau>0$ 选出唯一的最小相对熵代表。
这一选择通常依赖资料而非线性，因而不能直接称为量子门 [8](#ref-v93)。
本轮新增的连接是

$$
\boxed{\quad
\begin{gathered}
\text{全态同读数合并 + 保持读数 + 忠实固定参照}\\
\text{+ 一个二元量子参考的正性}
\end{gathered}
\quad\Longleftrightarrow\quad
\begin{gathered}
\text{普通可见算符代数}\\
\text{+ 参照模相容}
\end{gathered}\quad}
$$

并由此得到 C93 的唯一完全正实现。
此处“充分”首先指对当前全部读数充分；
不自动表示恢复未知输入的全部量子信息。

条件期望与模相容的联系已有 Takesaki 理论；相对熵、充分子代数与恢复已有 Petz 理论。
Koashi–Imoto 的部分已知态分解也将信息分为经典、量子与共同冗余部分
 [9](#ref-takesaki1972)、[10](#ref-petz1986)、[11](#ref-koashi2002)。
本文给出所需的有限维自足证明，并保留它们不同的量词：
本轮约化对全部输入与全部同资料态对成立；
不能直接用只对一组指定状态成立的恢复结论替代它。

**白话图景。**上一轮能替一份不完整资料选出最合理的代表。
这一轮追问：有没有同一台内部装置，无论实际输入是什么，都保持这些资料，
又把当前无法区分的内容整理成同一份可见代表？
若这台装置还经得住一个二元参考的联合比较，
可见关系就不能任意挑选，它们会被迫组成能相乘、能保留相位的完整代数。
参照也必须适合这个切分，规范补全才成为真正可实现的局部量子过程。

<a id="section-2"></a>

## 2. 候选的地位：关系内部的约束仍要有明确前件

<a id="sec-c94-status"></a>

“全部概念都在 $\Omega$ 内部”在本轮落实为：状态、读口、比较装置、参照和记录
共同属于同一内部关系模型；不另外引入一位无记录、无反作用的外部观察者。
但“某件对象属于整体”并不自动说明它满足任意欲求的正性、复合或连续性条件。
本轮把这些条件写成定义之间可被违反、可被见证的关系。

逻辑载体仍继承项目 V80 已声明的共同有限复比较结构：
有限维 $\mathcal H$、密度算符、迹配对、复线性组合，以及可与一个二元参考联合比较的接口
 [5](#ref-v80)。
本轮没有把这些结构伪装成单凭“内容即地址”已经推出。
在这个载体中，C94 定义哪些观察切分可以具有*全域物理充分约化*。
某个读口不满足 C94，不意味着它不是合法的量子测量；
它意味着当前读口不能同时满足这里声明的全部约化任务。

这也避免一项不必要的绝对化：一个观察者可以只测两个非对易读数，
却不能因此要求存在一台物理门，既对所有态精确保留这两个读数，
又彻底删除它们相干复用能显露的第三个方向。
反向见证将在后文给出。

**白话图景。**公理内生，不是把公理的文字改名为一个内部对象。
它是把“保持资料”“同资料可合并”“参照不漏方向”“联合报告不为负”接成同一个任务，
然后检查这些要求能否共同成立。
成立时，代数、隐藏部分和合法约化一起被锁定；
不成立时，能指出哪两份内容、哪一次比较暴露了冲突。

<a id="section-3"></a>

## 3. 有限读出、同资料关系与一个二值量子参考

<a id="sec-c94-interface"></a>

本轮继承前稿已经声明的有限复量子接口 [5](#ref-v80)、[8](#ref-v93)。
令 $H$ 为 $d\ge1$ 维复 Hilbert 空间，
$\mathcal S\subseteq\operatorname{Herm}(H)$ 为含单位 $I$ 的实线性读出空间，
并给定同一载体上的忠实内部参照

$$
\tau>0,\qquad \operatorname{Tr}\tau=1.
$$

不预设 $\mathcal S$ 对平方或乘积闭合。
记其复线性包为

$$
\mathcal A=\mathcal S+i\mathcal S\subseteq B(H).
$$

它已经含单位并对伴随闭合；是否对通常矩阵乘法闭合，是本轮要推出的结论。

### 定义 3.1（同资料二态与可见读出）

<a id="def-c94-same-data"></a>

对密度态 $\rho,\sigma$，定义

$$
\rho\sim_{\mathcal S}\sigma
 \quad\Longleftrightarrow\quad
 \operatorname{Tr}(\rho s)=\operatorname{Tr}(\sigma s)\quad(s\in\mathcal S).
$$

以 $q_{\mathcal S}(\rho)$ 记泛函
$s\mapsto\operatorname{Tr}(\rho s)$。同资料态组成 v93 的相容纤维。
这里同资料只指当前读口不能区分二态，不把它们直接等同为同一完整物理态。

待检查的过程使用前稿的复线性、保迹表示接口
$R:B(H)\to B(H)$。本轮不把复线性从零前件推出，
也不在定义中预设 $R$ 完全正、幂等，或预设其对偶的像为代数。
我们只先给它一个二值量子参考的组合检查。

### 定义 3.2（二值参考保正）

称 $R$ 满足二值参考保正，如果

<a id="eq-c94-two-positive"></a>

$$
(\operatorname{id}_2\otimes R)(T)\ge0
 \qquad\bigl(T\ge0\text{ 于 }\mathbb C^2\otimes H\bigr).
\tag{3.1}
$$

这正是二正性。参考只有二维，但量词包括其与 $H$ 的全部正联合输入，
包括纠缠输入；它不是只检查某一份选定 Bell 态或有限个试样。

式 [(3.1)](#eq-c94-two-positive) 蕴含 $R$ 在单份输入上为正：
把 $X\ge0$ 放到 $\lvert 0\rangle\langle 0\rvert\otimes X$ 即可。
结合保迹性，$R$ 把每份密度态送到密度态。

**白话图景。**当前读口给一个内容摘要；同摘要可以对应多个完整状态。
如果要把这份摘要真的整理成一份可继续使用的量子输出，
就要同时说明旧读数是否保留、隐藏区别怎样处理、内部参照是否被改变，
以及旁边留着一个二值量子参考时是否仍给合法状态。
本轮把这四个要求放在同一个过程上。

<a id="section-4"></a>

## 4. 唯一候选 C94：二值参考下的内生规范回缩

<a id="sec-c94-candidate"></a>

### 定义 4.1（本轮唯一候选 C94）

<a id="def-c94-candidate"></a>

给定 $(H,\mathcal S,\tau)$，称这个读出截口具有*内生规范回缩资格*，
若存在同一个复线性保迹映射 $R:B(H)\to B(H)$，同时满足：

1. **二值参考保正：**
    $\operatorname{id}_2\otimes R$ 为正；

2. **全部可见读数保持：**


   $$
   \operatorname{Tr}(R(\rho)s)=\operatorname{Tr}(\rho s)
     \quad(\rho\text{ 为密度态},\ s\in\mathcal S);
   $$

3. **同资料同输出：**


   $$
   \rho\sim_{\mathcal S}\sigma
     \ \Longrightarrow\ R(\rho)=R(\sigma)
     \quad(\rho,\sigma\text{ 为密度态});
   $$

4. **内部参照固定：**$R(\tau)=\tau$。

这四条共同组成本轮一个候选，记为 C94。

由于 $I\in\mathcal S$，读数保持已经包含迹保持；把保迹写进过程接口只是明确类型，
并非再添一个独立条件。二正性是具有直接参考意义的充分要求，
本文没有证明它是所有可能逻辑表述中的最弱前件。
事实上，代数证明所消费的是对偶的 Schwarz 性；
在参考维数这一层级上，后文反例证明一维不足，而本轮证明二维足够。

第二、三条还给出一个完整的二态等价：

<a id="eq-c94-exact-fiber-collapse"></a>

$$
R(\rho)=R(\sigma)
 \quad\Longleftrightarrow\quad
 \rho\sim_{\mathcal S}\sigma.
\tag{4.1}
$$

右向左是第三条；左向右先对输出读 $s$，再用第二条。
所以该过程在输出层合并的恰好是当前资料没有区分的那些状态，
不会额外合并已经可见的区别。

这一资格针对所声明读出截口与过程。
它不要求每一份任意删减的读口菜单都能在保持旧读数的同时实现这种全域整理。
后文的分类定理恰好判定哪些菜单可以，哪些必须补入关系或放弃某项要求。

### 定理 4.2（C94 的完整分类与唯一性）

<a id="thm-c94-main"></a>

对上述有限 $(H,\mathcal S,\tau)$，以下条件等价：

1. 存在满足 C94 的映射 $R$；

2. $\mathcal A=\mathcal S+i\mathcal S$ 是通常矩阵乘法下的含单位
    $C^*$ 子代数，且


   <a id="eq-c94-modular-condition"></a>

   $$
   \tau^{it}\mathcal A\tau^{-it}=\mathcal A
     \qquad(t\in\mathbb R);
   \tag{4.2}
   $$

3. 在某个共同酉坐标下，存在有限直和分解


   $$
   H=\bigoplus_k(H_{L,k}\otimes H_{R,k}),\qquad
     \mathcal A=\bigoplus_k\bigl(B(H_{L,k})\otimes I_{R,k}\bigr),
   $$


    且忠实参照具有块乘积形式


   $$
   \tau=\bigoplus_kq_k\tau_{L,k}\otimes\tau_{R,k},
     \qquad q_k>0,\quad\sum_kq_k=1,
   $$


    其中各 $\tau_{L,k},\tau_{R,k}$ 都为忠实密度态。

一旦存在，满足 C94 的 $R$ 唯一，且自动完全正、保迹、幂等。
它由式 [(9.2)](#eq-c94-reset) 的块重置给出，
并且对每份资料都等于 v93 的唯一 C93 相对熵规范补全。

**证明。**
定理 [7.2](#thm-c94-algebra) 从条件 1 推出通常乘法的代数闭合；
定理 [9.1](#thm-c94-block-reset) 随后推出唯一块重置和参照块乘积，给条件 3，
并用显式 Kraus 算符证明反向及完全正性。
定理 [10.1](#thm-c94-modular) 证明条件 2 与条件 3 等价。
定理 [11.1](#thm-c94-c93-implementation) 证明该唯一映射与全部 C93 规范补全相同。
下面逐步给出这些证明。

这是一条存在且唯一的分类：如果先任意给定某个 $R$，
仅知道条件 2 或 3 并不能说那个任意映射自动满足 C94；
它还必须等于所分类的唯一块重置。
二正性升级为完全正性也依赖 C94 的整组条件，不能推广成任意二正映射都完全正。

**白话图景。**同一份摘要要成为可重复使用的量子内容，
就不能保留旧区别的同时又偷偷改变它们相互组合的结果。
把一个二值参考和一份不漏方向的内部参照一起保留，
这项要求会迫使读口形成完整的代数结构。
随后规范输出的形式也被锁定，而不需要再任意选一种重置规则。

<a id="section-5"></a>

## 5. 二态关系怎样锁定对偶过程的像

<a id="sec-c94-dual-range"></a>

令 $E=R^*$ 为迹配对下的对偶，即

$$
\operatorname{Tr}(R(X)B)=\operatorname{Tr}(XE(B))\qquad(X,B\in B(H)).
$$

$R$ 正且保迹，所以 $E$ 正且保持单位。
$\operatorname{id}_2\otimes E$ 是 $\operatorname{id}_2\otimes R$ 的伴随；
有限矩阵正锥在迹内积下自对偶，故 $E$ 同样二正。
参照固定等价于

<a id="eq-c94-dual-reference"></a>

$$
\operatorname{Tr}(\tau E(B))=\operatorname{Tr}(\tau B)\qquad(B\in B(H)).
\tag{5.1}
$$

### 引理 5.1（同资料条件精确确定对偶像）

<a id="lem-c94-dual-range"></a>

若 $R$ 保留全部 $\mathcal S$ 读数且同资料同输出，则

<a id="eq-c94-range"></a>

$$
E(s)=s\quad(s\in\mathcal S),\qquad
 \operatorname{ran}E=\mathcal A.
\tag{5.2}
$$

因此 $E^2=E$、$R^2=R$。

**证明。**
对全部密度态的读数保持给
$\operatorname{Tr}\rho(E(s)-s)=0$。密度态实线性张成 $\operatorname{Herm}(H)$，
故 $E(s)=s$。

对任意 $X=X^\dagger\in\mathcal S^\perp$，
因为 $I\in\mathcal S$，有 $\operatorname{Tr} X=0$。
若 $X\ne0$，取
$0<\varepsilon<1/(d\left\lVert X\right\rVert_{\mathrm{op}})$，
则 $\rho_\pm=I/d\pm\varepsilon X$ 都为严格正密度态，
并且 $\rho_+\sim_{\mathcal S}\rho_-$。
同资料条件给 $R(X)=0$；$X=0$ 情形显然。

任取 $B=B^\dagger$，对全部这样的 $X$ 都有

$$
\operatorname{Tr}(XE(B))=\operatorname{Tr}(R(X)B)=0.
$$

由于 $E(B)$ 自伴，有限维双正交给 $E(B)\in\mathcal S$。
再由复线性性得 $\operatorname{ran}E\subseteq\mathcal A$。
另一方面 $E$ 固定 $\mathcal S$ 及其复线性包，故像恰为 $\mathcal A$。
像上的恒等性给 $E^2=E$，取对偶得 $R^2=R$。

目前只知道像是一个算符系统；幂等本身没有证明它对通常乘法闭合。
另外，对偶像 $\operatorname{ran}E$ 与状态映射像 $\operatorname{ran}R$ 是两个不同对象。
后者一般不对普通矩阵乘法闭合。

**白话图景。**如果两份输入对当前全部问题给相同答案，规范输出就必须一样。
这迫使输出的每一个问题，拉回输入后都只能使用当前已经读到的关系。
反过来，每个旧问题都被原样保留。
因此对偶过程恰好投到当前读口空间；但这个空间能否承担乘法，还需要下一步检查。

<a id="section-6"></a>

## 6. 二值参考、平方缺额与忠实参照

<a id="sec-c94-schwarz"></a>

### 引理 6.1（二值参考给出 Schwarz 不等式）

<a id="lem-c94-schwarz"></a>

若 $E$ 保持单位且二正，则对任意 $a\in B(H)$，

<a id="eq-c94-schwarz"></a>

$$
E(a^\dagger a)-E(a)^\dagger E(a)\ge0.
\tag{6.1}
$$

**证明。**
矩阵

$$
\begin{pmatrix}a^\dagger a&a^\dagger\\a&I\end{pmatrix}
 =
 \begin{pmatrix}a^\dagger\\I\end{pmatrix}
 \begin{pmatrix}a&I\end{pmatrix}
$$

为正。对其施加 $\operatorname{id}_2\otimes E$，得到正块矩阵

$$
\begin{pmatrix}
 E(a^\dagger a)&E(a)^\dagger\\E(a)&I
 \end{pmatrix}.
$$

在向量 $(v,-E(a)v)$ 上取二次型，正性恰给
$\langle v,[E(a^\dagger a)-E(a)^\dagger E(a)]v\rangle\ge0$，
所以式 [(6.1)](#eq-c94-schwarz) 成立。

这个证明只用了一个二维参考的块正性，
没有调用以完全正性为前件的 Stinespring 表示。

### 引理 6.2（忠实不变参照锁死可见平方缺额）

<a id="lem-c94-zero-defect"></a>

在 C94 条件下，对每个 $s=s^\dagger\in\mathcal S$，

<a id="eq-c94-zero-defect"></a>

$$
D_s:=E(s^2)-s^2=0.
\tag{6.2}
$$

**证明。**
因为 $E(s)=s$，引理 [6.1](#lem-c94-schwarz) 给 $D_s\ge0$。
参照不变又给

$$
\operatorname{Tr}(\tau D_s)
 =\operatorname{Tr}(R(\tau)s^2)-\operatorname{Tr}(\tau s^2)=0.
$$

取 $m=\lambda_{\min}(\tau)>0$，有
$0\le m\operatorname{Tr} D_s\le\operatorname{Tr}(\tau D_s)=0$。
正矩阵迹为零只能是零矩阵，故 $D_s=0$。

这里忠实性作用于已经声明的有限载体。
若参照在某方向为零，一项非零正缺额可能恰好躲在这个方向，
仅凭其参照期望为零便不能排除它。
因此，必要时先明确工作载体，再使用本定理。
若改到压缩载体，须在该载体上重新声明全部输入、读出及过程条件；
只把非忠实参照的零支撑方向删去，不能自动保留原载体上的分类结论。
v93 随资料改变的最小支撑，也不能替代这里同一个过程使用的共同载体。

**白话图景。**把同一个问题平方以后，二值参考要求它的比较缺额只能是非负的。
参照不变又说，这份缺额的总读数为零。
只要参照在每个允许方向都留有正权重，非负缺额就没有地方可藏，只能全部为零。
这样，平方关系由一个二元组合检查和一个内部参照共同固定。

<a id="section-7"></a>

## 7. 正反与相位比较迫使通常乘法闭合

<a id="sec-c94-multiplicative-domain"></a>

### 引理 7.1（零平方缺额给双模关系）

<a id="lem-c94-bimodule"></a>

设 $s=s^\dagger$、$E(s)=s$、$E(s^2)=s^2$，且 $E$ 满足
式 [(6.1)](#eq-c94-schwarz)。则对任意 $b\in B(H)$，

<a id="eq-c94-bimodule-one"></a>

$$
E(sb)=sE(b),\qquad E(bs)=E(b)s.
\tag{7.1}
$$

**证明。**
记

$$
F=E(sb)-sE(b),\qquad
 D_b=E(b^\dagger b)-E(b)^\dagger E(b)\ge0.
$$

对 $s+zb$ 使用 Schwarz 不等式，常数缺额为零，展开得到

<a id="eq-c94-polarized-defect"></a>

$$
zF+\bar zF^\dagger+|z|^2D_b\ge0\qquad(z\in\mathbb C).
\tag{7.2}
$$

对任意向量 $v$ 取二次型，依次令 $z=t,-t,it,-it$，再令 $t\downarrow0$。
实部和虚部的一阶项都必须为零，所以 $\langle v,Fv\rangle=0$。
复极化说明 $F=0$，得到第一式。
取伴随，再将 $b^\dagger$ 替换为 $b$，得到第二式。

### 定理 7.2（C94 迫使可见读出成为通常乘积的代数）

<a id="thm-c94-algebra"></a>

若 $R$ 满足 C94，则 $\mathcal A=\mathcal S+i\mathcal S$
是 $B(H)$ 中的含单位 $C^*$ 子代数，$\mathcal S=\mathcal A\cap\operatorname{Herm}(H)$。
对全部 $a,c\in\mathcal A$ 与 $B\in B(H)$，还有

<a id="eq-c94-full-bimodule"></a>

$$
E(aBc)=aE(B)c.
\tag{7.3}
$$

**证明。**
对任意 $s,t\in\mathcal S$，前两引理给

$$
E(st)=sE(t)=st.
$$

因为 $\operatorname{ran}E=\mathcal A$，所以 $st\in\mathcal A$。
复线性展开使 $\mathcal A$ 对全部通常乘法闭合。
它已含单位、对伴随闭合，而且有限维故范数闭，因而是 $C^*$ 子代数。
若 $s+it\in\mathcal A$ 自伴，其中 $s,t\in\mathcal S$，则 $t=0$，
所以其自伴部分正好是 $\mathcal S$。
对式 [(7.1)](#eq-c94-bimodule-one) 作复线性延拓，再连续使用左右两式，
便得到式 [(7.3)](#eq-c94-full-bimodule)。

从逻辑上看，本轮没有先要求乘法闭合再把它重新命名为内生。
它由同资料二态、可见读数保持、二值参考正性和忠实参照不变共同推出。
更大的结构随后是这个通常乘积代数上的条件期望。
这是有限量子接口内的结构分类，不独立供应该接口最初的复标量、状态空间和概率标定。

**白话图景。**一个可见问题的平方已经被锁定后，再把它与另一个关系作正反以及相位方向的比较。
如果乘积还留下额外缺额，这四种一阶比较总有一边会违反正性。
因此乘积也必须被同一读口体系保留。
重复使用这一要求，可见内容就形成了能承受关系组合的代数，
而不只是一串彼此孤立的数值。

<a id="section-8"></a>

## 8. 有限可见代数的块结构

<a id="sec-c94-finite-blocks"></a>

上一节已经从 C94 推出通常乘积的 $C^*$ 代数 $\mathcal A$。
本节使用其有限表示，把可见内容与可重置部分精确分开。
这种直和与张量结构是有限量子操作理论的标准结构，
与不扰动部分已知状态的分解相邻 [11](#ref-koashi2002)。
为使本轮依赖明确，先给所需有限表示的矩阵单位证明。

### 引理 8.1（有限代数的标准块表示）

<a id="lem-c94-finite-algebra-blocks"></a>

任意含单位的有限维 $C^*$ 子代数 $\mathcal A\subseteq B(H)$，
在共同酉坐标下均有

<a id="eq-c94-finite-blocks"></a>

$$
H=\bigoplus_k(H_{L,k}\otimes H_{R,k}),\qquad
 \mathcal A=\bigoplus_k\bigl(B(H_{L,k})\otimes I_{R,k}\bigr).
\tag{8.1}
$$

各因子维数为正整数。记对应的最小中央投影为 $P_k$。

**证明。**
先同时对角化中心中的自伴算符，取其最小中央投影 $P_k$。
它们把问题分为中心只有标量的有限代数块。

在一个这样的块中，选择极大组互相正交的代数内最小投影
$e_1,\ldots,e_n$。其和必须是该块单位，否则剩余非零投影中还能继续选取。
最小性给 $e_i\mathcal Ae_i=\mathbb C e_i$：
若存在非标量自伴元，其谱投影就给一个更小的非零投影。

若 $0\ne a\in e_i\mathcal Ae_j$，则
$a^\dagger a=\lambda e_j$、$aa^\dagger=\mu e_i$，
其中 $\lambda,\mu>0$。由 $aa^\dagger a$ 的两种写法得 $\lambda=\mu$，
归一后得到连接 $e_j$ 与 $e_i$ 的部分等距。
任意两个这样的角元相差标量，因为将一个左乘另一个的伴随会落在
$e_j\mathcal Ae_j=\mathbb C e_j$ 中。

非零角之间的连通关系是等价关系：连接的部分等距可以相乘。
每个等价类内投影之和与整个代数对易，故是中央投影。
本块中心只有标量，因此所有 $e_i$ 都连通。
固定 $e_1$，取部分等距 $v_i$ 满足
$v_i^\dagger v_i=e_1$、$v_iv_i^\dagger=e_i$，并令 $v_1=e_1$。
则 $e_{ij}=v_iv_j^\dagger$ 是矩阵单位，张成这个代数块。

令 $H_R=e_1H$、$H_L=\mathbb C^n$。
映射 $\lvert i\rangle\otimes\xi\mapsto v_i\xi$ 是酉同构，
并将矩阵单位变成 $\lvert i\rangle\langle j\rvert\otimes I_R$。
逐块组合即得式 [(8.1)](#eq-c94-finite-blocks)。

可见资料在这些坐标中恰为一组未归一正矩阵

<a id="eq-c94-visible-data"></a>

$$
a_k(\rho)=\operatorname{Tr}_{R,k}(P_k\rho P_k),\qquad
 a_k\ge0,\qquad\sum_k\operatorname{Tr} a_k=1.
\tag{8.2}
$$

所有 $B(H_{L,k})\otimes I_{R,k}$ 的响应共同确定它们，反过来也一样。
块标签 $k$ 是可见的经典区块标签，实际取得它仍需相应读出过程；
每块中的左因子承载可见量子内容。

**白话图景。**一个能够完整组合的有限读口体系，会自动分成若干有标签的区域。
每个区域里，一部分内容可以被当前问题完整读取，另一部分只以单位关系出现。
这个分解来自读口的乘法结构；它不是先任意把整体切成两个外部系统。
接下来，规范门能怎样处理那部分未读内容，也会被同一结构限制。

<a id="section-9"></a>

## 9. 双模关系唯一确定加权条件期望与块重置

<a id="sec-c94-weighted-expectation"></a>

### 定理 9.1（C94 的唯一块重置与完全正性）

<a id="thm-c94-block-reset"></a>

若 $R$ 满足 C94，则在式 [(8.1)](#eq-c94-finite-blocks) 的坐标中，
忠实参照必须具有

<a id="eq-c94-reference-product"></a>

$$
\tau=\bigoplus_kq_k\tau_{L,k}\otimes\tau_{R,k},
 \quad q_k>0,\quad\sum_kq_k=1,
\tag{9.1}
$$

其中各因子态忠实。
该 $R$ 唯一，并且

<a id="eq-c94-reset"></a>

$$
\boxed{\quad
 R(\rho)=R_{\mathcal A,\tau}(\rho)
 =\bigoplus_k\operatorname{Tr}_{R,k}(P_k\rho P_k)\otimes\tau_{R,k}.
 \quad}
\tag{9.2}
$$

它完全正、保迹、幂等。
反过来，给定式 [(8.1)](#eq-c94-finite-blocks) 与
式 [(9.1)](#eq-c94-reference-product)，式 [(9.2)](#eq-c94-reset) 满足全部 C94 条件。

**证明。**
先利用上一节已经证明的双模关系。
对不同中央块，

$$
E(P_kBP_l)=P_kE(B)P_l=0\qquad(k\ne l),
$$

因为 $E(B)\in\mathcal A$ 块对角。

在第 $k$ 块内，对任意 $b\in B(H_{R,k})$，
$I_L\otimes b$ 与全部 $a\otimes I_R$ 对易。
双模关系因而使 $E(I_L\otimes b)$ 与这些可见算符对易。
它又属于 $B(H_L)\otimes I_R$，所以只能是标量：

$$
E(I_L\otimes b)=\varphi_k(b)I_L\otimes I_R.
$$

这里按第 $k$ 块理解单位；$E(P_k)=P_k$。
正性与单位保持说明 $\varphi_k$ 是正归一泛函。
有限维迹配对给唯一密度矩阵 $\eta_k$，使
$\varphi_k(b)=\operatorname{Tr}(\eta_k b)$。
再由双模关系，

<a id="eq-c94-weighted-expectation"></a>

$$
E(a\otimes b)
 =a\otimes I_R\,\operatorname{Tr}(\eta_k b).
\tag{9.3}
$$

简单张量张成整个块，故这已确定 $E$，取对偶即得

$$
R(\rho)=\bigoplus_k a_k(\rho)\otimes\eta_k.
$$

现在使用参照固定：

$$
\tau=R(\tau)=\bigoplus_k a_k(\tau)\otimes\eta_k.
$$

由于 $\tau>0$，各 $a_k(\tau)>0$，各 $\eta_k$ 也必须严格正。
取 $q_k=\operatorname{Tr} a_k(\tau)$、$\tau_{L,k}=a_k(\tau)/q_k$、
$\tau_{R,k}=\eta_k$，便得到式 [(9.1)](#eq-c94-reference-product)。
而

$$
\tau_{R,k}
 =\frac{\operatorname{Tr}_{L,k}(P_k\tau P_k)}{q_k}
$$

已由给定参照唯一确定，所以 $R$ 唯一。

为了不预设完全正性，直接给 Kraus 表示。
写 $\tau_{R,k}=\sum_a\lambda_{ka}\lvert u_{ka}\rangle\langle u_{ka}\rvert$，
并选择右因子的任意正交基 $\lvert e_{kj}\rangle$。
将下式按零延拓到其余块：

<a id="eq-c94-reset-kraus"></a>

$$
M_{kaj}
 =\sqrt{\lambda_{ka}}
 \bigl(I_{L,k}\otimes\lvert u_{ka}\rangle\langle e_{kj}\rvert\bigr)P_k.
\tag{9.4}
$$

展开矩阵单位便得

$$
\sum_{k,a,j}M_{kaj}\rho M_{kaj}^\dagger
 =\bigoplus_k a_k(\rho)\otimes\tau_{R,k},
 \qquad
 \sum_{k,a,j}M_{kaj}^\dagger M_{kaj}=I.
$$

每个夹乘在任意参考扩张下都保持正性，故 $R$ 完全正；
第二式给保迹性。
再次取右侧部分迹不改变 $a_k$，所以 $R^2=R$。

反向，给定上述代数与参照块结构，显式公式显然只依赖 $a_k$，
并保留全部 $a_k$，固定 $\tau$；Kraus 表示给完全正性及保迹性，
尤其满足二值参考检查。因此全部 C94 条件成立。

$E$ 是保持 $\tau$ 期望的加权条件期望。
一般而言，$E$ 保持单位但不保持普通迹；$R$ 保迹但不保持单位。
还须区分

$$
\operatorname{ran}E=\mathcal A,
 \qquad
 \operatorname{ran}R
 =\left\{\bigoplus_kx_k\otimes\tau_{R,k}:x_k\in B(H_{L,k})\right\}.
$$

后一个线性空间通常不对普通乘法闭合，
因为乘法会出现 $\tau_{R,k}^2$。

式 [(9.4)](#eq-c94-reset-kraus) 给有限量子通道的数学表示。
要把它供应为某个具体装置，仍须前稿中的实际内部记录、控制和过程接口 [5](#ref-v80)；
这里没有由表示存在性推断实现成本或物理时间。

**白话图景。**当前可见内容必须原样保留；当前读不出的部分又不能偷偷依赖被合并的输入。
这迫使每块未读部分统一重置为一份固定状态。
参照本身要保持不变，就进一步规定那份固定状态只能来自参照自己的右侧部分。
因此加权条件期望、规范重置和内部参照的乘积结构一起被确定了。

<a id="section-10"></a>

## 10. 参照的模关系何时保留同一可见代数

<a id="sec-c94-modular"></a>

对忠实 $\tau$，有限矩阵函数演算定义酉族 $\tau^{it}$。
以下参数 $t$ 是对数参照的数学参数，没有自动被标定为实际物理时间。

### 定理 10.1（模不变性与块乘积参照等价）

<a id="thm-c94-modular"></a>

对式 [(8.1)](#eq-c94-finite-blocks) 的可见代数与忠实 $\tau$，
以下条件等价：

1. $\tau^{it}\mathcal A\tau^{-it}=\mathcal A$ 对全部 $t\in\mathbb R$ 成立；

2. $\log\tau$ 对中央块为块对角，且每块满足


   <a id="eq-c94-modular-generator"></a>

   $$
   (\log\tau)|_{P_kH}
     =h_{L,k}\otimes I_{R,k}+I_{L,k}\otimes h_{R,k}
   \tag{10.1}
   $$


    对某些自伴 $h_{L,k},h_{R,k}$ 成立；

3. $\tau$ 具有式 [(9.1)](#eq-c94-reference-product) 的块乘积形式。

**证明。**
条件 3 给每块
$\log q_k+\log\tau_{L,k}\otimes I+I\otimes\log\tau_{R,k}$，
把标量项并入任一因子即可得条件 2。
条件 2 的两个张量项对易，指数化并分别归一可得条件 3；
块的迹为 $q_k$，总迹一给 $\sum_kq_k=1$。

条件 3 还直接给

$$
\tau^{it}(a\otimes I)\tau^{-it}
 =(\tau_{L,k}^{it}a\tau_{L,k}^{-it})\otimes I,
$$

故得到条件 1。

反过来，若条件 1 成立，模共轭是 $\mathcal A$ 的连续一参数自同构。
它必须置换有限个最小中央投影；连续性和 $t=0$ 的恒等性迫使每个 $P_k$ 始终固定。
所以 $\tau^{it}$、继而 $\log\tau$ 与全部 $P_k$ 对易。

固定第 $k$ 块，令 $K_k=(\log\tau)|_{P_kH}$。
对模不变性在零点微分，有

$$
[K_k,a\otimes I]\in B(H_{L,k})\otimes I\qquad(a\in B(H_{L,k})).
$$

记 $r_k=\dim H_{R,k}$，取
$h_{L,k}=r_k^{-1}\operatorname{Tr}_{R,k}K_k$。
对上述交换子取右侧部分迹，说明

$$
[K_k-h_{L,k}\otimes I,\ a\otimes I]=0
 \qquad(a\in B(H_{L,k})).
$$

矩阵单位直接给
$(B(H_{L,k})\otimes I)'=I\otimes B(H_{R,k})$，
所以余项等于 $I\otimes h_{R,k}$。
它自伴，故 $h_{R,k}$ 自伴，得到条件 2。

这一有限生成元分解与项目 Atlas 的正规化群接口相接 [3](#ref-atlas)。
在一般 von Neumann 代数中，忠实参照下的条件期望存在性与模不变性的对应，
是 Takesaki 的既有定理 [9](#ref-takesaki1972)。
本轮没有重新宣称该对应为数学首创；这里的推进是从任意读出算符系统出发，
先由 C94 的二态与二值参考条件迫使通常代数，再接上这个结构。

**白话图景。**参照不仅给一份概率表，它的对数也定义一族内部关系变换。
如果这族变换始终把可见问题送回可见问题，参照就不能在可见与未读因子之间
夹带一项会混合两边的对数耦合。
每个块里它因而分成左右两项，指数化以后正好成为块乘积。
这使“参照与读口相容”有了一个可证明的充要条件。

<a id="section-11"></a>

## 11. 哪些 C93 规范补全可以成为同一全域量子门

<a id="sec-c94-information-projection"></a>

先回到任意 $\mathcal S$ 与忠实 $\tau$。
v93 已证明每份资料的非空纤维具有唯一相对熵规范补全 [8](#ref-v93)。
因此可定义态集合上的选择器

$$
\mathfrak m_{\mathcal S,\tau}(\rho)
 =\operatorname*{arg\,min}_{\omega\sim_{\mathcal S}\rho}D(\omega\Vert\tau).
$$

这一定义本身不保证对未知输入线性，更不保证带参考保正。
它自动保留当前资料、同资料同输出，并固定 $\tau$。

### 定理 11.1（C93 全资料物理实现的完整判据）

<a id="thm-c94-c93-implementation"></a>

对有限 $\mathcal S$ 与忠实 $\tau$，以下条件等价：

1. $\mathfrak m_{\mathcal S,\tau}$ 在全部密度态上具有同一个 CPTP 实现；

2. 它具有复线性保迹、二值参考保正的实现；

3. $(H,\mathcal S,\tau)$ 满足 C94 的存在性条件；

4. $\mathcal S+i\mathcal S$ 是通常 $C^*$ 子代数，且被 $\tau$ 的模群保持。

此时实现唯一，正是式 [(9.2)](#eq-c94-reset)。
对每份输入 $\rho$，令 $\sigma=R_{\mathcal A,\tau}(\rho)$，则

<a id="eq-c94-pythagorean"></a>

$$
\boxed{\quad
 D(\rho\Vert\tau)
 =D(\rho\Vert\sigma)+D(\sigma\Vert\tau).
 \quad}
\tag{11.1}
$$

同一恒等式对 $\rho$ 所在纤维的全部状态成立，规范态 $\sigma$ 不变。

**证明。**
条件 1 给条件 2。
该选择器自动保读数、同资料同输出、固定 $\tau$，
所以条件 2 给条件 3。
前面的分类证明给条件 3 与条件 4 等价。
只需证明分类所得块重置就是相对熵选择器，即可从条件 4 返回条件 1。

在块坐标中，固定资料 $a_k=a_k(\rho)$。
记 $P_{L,k}=\operatorname{supp} a_k$；当 $a_k=0$ 时取 $P_{L,k}=0$。
该纤维全部状态共同允许的最小支撑恰为

<a id="eq-c94-fiber-support"></a>

$$
P_*^{\rho}=\bigoplus_kP_{L,k}\otimes I_{R,k}.
\tag{11.2}
$$

事实上，任何兼容态对正投影
$P_k-P_{L,k}\otimes I_{R,k}$ 的期望为零，
故其支撑不能含这些方向。
另一方面
$\sigma=\bigoplus_k a_k\otimes\tau_{R,k}$
具有给定资料，并因 $\tau_{R,k}>0$ 而在式 [(11.2)](#eq-c94-fiber-support) 上忠实，
所以这个支撑正好是最小共同支撑。

所有对数都限制在相应正支撑上。
对每个非零 $a_k$，有

$$
\log\sigma
 =\log a_k\otimes I+I\otimes\log\tau_{R,k}
$$

于该块允许支撑。
与 $P_*^{\rho}\log\tau P_*^{\rho}$ 相减，右因子的对数项相消，留下

<a id="eq-c94-log-difference-visible"></a>

$$
\begin{split}
 G_k={}&\bigl(
 \log a_k-(\log q_k)P_{L,k}
 -P_{L,k}(\log\tau_{L,k})P_{L,k}
 \bigr)\otimes I_{R,k}.
 \end{split}
\tag{11.3}
$$

它属于压缩后的可见代数；在支撑外作零延拓后仍属于 $\mathcal A$。
这里仍按 v93 的规则先取 $\log\tau$ 再压缩，
没有用 $\log(P\tau P)$ 偷换次序。

令 $G=\bigoplus_kG_k$。
任意同纤维状态 $\omega$ 与 $\sigma$ 对 $G$ 的响应相同，因此

$$
\begin{split}
 D(\omega\Vert\tau)-D(\omega\Vert\sigma)
 &=\operatorname{Tr}(\omega G)\\
 &=\operatorname{Tr}(\sigma G)=D(\sigma\Vert\tau).
 \end{split}
$$

相对熵非负及其严格等号条件说明，$\sigma$ 是该纤维唯一最小点。
这既给式 [(11.1)](#eq-c94-pythagorean)，也给全部规范选择器的 CPTP 实现。
最后，密度态线性张成全部自伴矩阵，再复线性张成 $B(H)$，
故一个实现若对全部密度态相同，其线性延拓也唯一。

上述证明包括 $a_k$ 奇异或整块为零的资料，不要求每份输入本身忠实。
忠实的是共同参照及其右因子；具体资料的支撑由
式 [(11.2)](#eq-c94-fiber-support) 单独确定。

这项实现是一个实际改变未知输入的规范重置。
若 $\rho\ne R(\rho)$，它会消去当前不可见的关联；
不能把“可实现规范完成”解释为原实际态本来就没有那些关联。
这一点保留 v93 对规范推断与实际来源的区分。

**白话图景。**上一轮为每份资料选出一个唯一代表，却不保证所有代表能由同一台量子门产生。
本轮给出了完整判据：读口必须形成通常代数，参照必须与它模相容。
条件成立时，同一台块重置门确实为每份未知输入产生对应规范代表；
条件不成立时，不能把一个数学上的选态规则直接当成全域物理操作。

<a id="section-12"></a>

## 12. 可见压缩、精确信息分解与 Petz 恢复接口

<a id="sec-c94-visible-compression"></a>

定义可见资料代数
$\mathcal D=\bigoplus_k B(H_{L,k})$，其迹取各块迹之和。
可见压缩映射为

<a id="eq-c94-compression"></a>

$$
C(\rho)=\bigoplus_k\operatorname{Tr}_{R,k}(P_k\rho P_k)
 =\bigoplus_k a_k(\rho).
\tag{12.1}
$$

它是 CPTP 映射，且

$$
C(\tau)=\bigoplus_kq_k\tau_{L,k}>0.
$$

对 $b=\bigoplus_kb_k\in\mathcal D$，其对偶为
$C^*(b)=\bigoplus_k b_k\otimes I_{R,k}$。

### 推论 12.1（可见与不可见信息的精确分解）

<a id="cor-c94-visible-relative-entropy"></a>

在 C94 的结构下，对每个密度态 $\rho$ 都有

<a id="eq-c94-information-chain"></a>

$$
\boxed{\quad
 D(\rho\Vert\tau)
 =D(\rho\Vert R(\rho))
 +D(C(\rho)\Vert C(\tau)).
 \quad}
\tag{12.2}
$$

因此压缩保持相对于 $\tau$ 的全部相对熵，当且仅当 $\rho=R(\rho)$。

**证明。**
块乘积与对数张量公式给

$$
\begin{split}
 D(R(\rho)\Vert\tau)
 &=\sum_k\operatorname{Tr}\!\left[
 a_k(\rho)\bigl(\log a_k(\rho)-\log(q_k\tau_{L,k})\bigr)
 \right]\\
 &=D(C(\rho)\Vert C(\tau)).
 \end{split}
$$

零块项按零处理。代入式 [(11.1)](#eq-c94-pythagorean)，得到分解。
最后由 $D(\rho\Vert R(\rho))=0$ 当且仅当二态相同，得到等号判据。

这个结果直接表达了可见资料与实际整体之间还差多少内容。
它不声称任意带关联输入都能由其可见压缩完全恢复。

### 命题 12.2（Petz 恢复在该结构中成为同一规范截面）

<a id="prop-c94-petz-section"></a>

定义

<a id="eq-c94-petz-map"></a>

$$
\mathcal P_{\tau,C}(b)
 =\tau^{1/2}C^*\!\left(
 C(\tau)^{-1/2}bC(\tau)^{-1/2}
 \right)\tau^{1/2}.
\tag{12.3}
$$

则

<a id="eq-c94-petz-section"></a>

$$
\mathcal P_{\tau,C}(b)=\bigoplus_kb_k\otimes\tau_{R,k},\qquad
 C\mathcal P_{\tau,C}=\operatorname{id}_{\mathcal D},\qquad
 R_{\mathcal A,\tau}=\mathcal P_{\tau,C}C.
\tag{12.4}
$$

其中 $\mathcal P_{\tau,C}:\mathcal D\to B(H)$ 是 CPTP。

**证明。**
各 $q_k\tau_{L,k}$ 忠实，因此逆平方根良好定义。
在第 $k$ 块中代入
$\tau^{1/2}=\sqrt{q_k}\tau_{L,k}^{1/2}\otimes\tau_{R,k}^{1/2}$，
左右的可见因子与其逆平方根相消，得到
$b_k\otimes\tau_{R,k}$。
其余恒等式随部分迹与迹一性直接成立。
张量固定正态及直和保持完全正性，并保持总迹。

式 [(12.3)](#eq-c94-petz-map) 是已有 Petz 恢复接口 [10](#ref-petz1986)。
这里 $\mathcal P_{\tau,C}$ 从可见资料空间返回完整空间，
而 $R=\mathcal P_{\tau,C}C$ 从完整空间回到同一完整空间，二者的类型不同。
对一般非模相容参照，Petz 公式仍可定义并固定参照的压缩与恢复，
但不能因此宣称 $C\mathcal P_{\tau,C}=\operatorname{id}$ 对全部可见资料成立。
本轮的模相容与块结构正好保证这个全域右逆条件。

**白话图景。**把完整状态压成当前可见资料，会失去一部分区别。
规范截面再用内部参照补齐未读部分，返回唯一代表。
总信息差精确分成可见资料保留的部分，以及实际状态相对于代表仍多出的部分。
当后一部分为零时，这份实际状态才真的能够从当前压缩完整恢复。
条件期望、规范补全和恢复因此在同一结构中相遇，同时保留各自的输入与输出类型。

<a id="section-13"></a>

## 13. 反向审计：同一个平方缺额怎样暴露不同前件

<a id="sec-c94-reverse-defect"></a>

定义 [4.1](#def-c94-candidate) 将读出保持、同读数融合、内部参照稳定与二元参考正性
作用在同一个实际线性映射 $R$ 上。
主定理的关键量是 $E=R^*$ 在可见 $a$ 上的平方缺额

$$
D_a=E(a^\dagger a)-a^\dagger a.
$$

二元参考使 $D_a\ge0$，固定参照给 $\operatorname{Tr}(\tau D_a)=0$，
忠实覆盖再迫使 $D_a=0$。下面逐项删除条件，直接看这条链在哪里断开。
所用转置与不完全正例子在项目 $\Omega$ 稿、V80 及 v93 中已有背景
 [4](#ref-omega)、[5](#ref-v80)、[8](#ref-v93)；这里用它们审计 C94 的准确前件，不作例子首创声明。

### 命题 13.1（只保单系统正性，平方缺额仍可正负相消）

<a id="prop-c94-positive-not-two-positive"></a>

在一个 qubit 上取

$$
R=\frac{\operatorname{id}+\mathsf T}{2},\qquad
 \mathcal S=\operatorname{span}_{\mathbb R}\{I,X,Z\},\qquad
 \tau=I_2/2,
$$

其中 $\mathsf T$ 是固定计算基的转置。
$R$ 正、保迹，保持全部 $\mathcal S$ 读数，融合所有同读数状态，并固定忠实 $\tau$。
但它不是 $2$-positive，且 $\mathcal S+i\mathcal S$ 不是普通乘积下的代数。

**证明。**
转置保持单个正矩阵的正性和迹，故其与恒等的平均也如此。
对 Bloch 态，$R$ 的作用为 $(x,y,z)\mapsto(x,0,z)$，
因而读数保持、融合及 $R\tau=\tau$ 均直接成立。
但是 $XZ=-iY$ 不属于 $\mathcal S+i\mathcal S$。

取 $a=(X+iZ)/2$，则 $E(a)=a$，且

$$
a^\dagger a=\frac{I+Y}{2},\qquad
 \boxed{D_a=-\frac Y2.}
$$

所以 $\operatorname{Tr}(\tau D_a)=0$，但 $D_a$ 的特征值为 $\pm1/2$。
缺少二元参考检查时，零响应允许正负相消，不能推出平方闭合。

更直接地，令 $\Phi=\lvert \Phi\rangle\langle \Phi\rvert$，
$\lvert \Phi\rangle=(\lvert 00\rangle+\lvert 11\rangle)/\sqrt2$，$F$ 为交换算符。
逐项转置给

$$
(\operatorname{id}\otimes R)(\Phi)=\frac12\Phi+\frac14F.
$$

反对称向量 $\lvert \psi_-\rangle=(\lvert 01\rangle-\lvert 10\rangle)/\sqrt2$
满足 $\Phi\lvert \psi_-\rangle=0$、$F\lvert \psi_-\rangle=-\lvert \psi_-\rangle$，
故该输出在此方向的响应为 $-1/4$。
它不是正算符，证明 $R$ 不具 $2$-positive 性。

这个负响应可集中成一个有限三维报告。
问事件 $\lvert \psi_-\rangle\langle \psi_-\rvert$ 与其补，得到候选表

$$
\operatorname{diag}(-1/4,5/4)=\frac12\left(I-\frac32Z\right),
 \qquad \mathbf b=(0,0,-3/2).
$$

这不是一份合法 qubit 态；它是落在 Bloch 球外的失败见证。
只看单系统的实 Bloch 圆盘时没有负概率，接上一个内部二元参考才暴露失败。

<a id="fig-c94-bloch-witness"></a>

```text
                         z
                         ↑
                    · ·  1  · ·
                 ·       │       ·
               ·         │         ·
         ─────·──────────0──────────·────→ x
               ·         │         ·
                 ·       │       ·
                    · · −1  · ·
                         │
                         ● −3/2   ← 球外失败证书

           合法截面：y = 0，x² + z² ≤ 1
           参考检查：Q = diag(−1/4, 5/4)，p₋ = −1/4
```

字符图仅作示意；原图的精确区域与失败报告如下：

| 图示对象 | 精确区域或数值 |
|---|---|
| 合法二元报告截面 | y = 0，x² + z² ≤ 1；单位圆边界的 z 轴交点为 ±1。 |
| 球外红点 | b = (0, 0, −3/2)，位于单位圆盘之外。 |
| 归一候选报告 | Q = diag(−1/4, 5/4)，总迹为一，含负响应 p₋ = −1/4。 |
| 图示资格 | 参考检查的失败证书；不是可制备态或物理轨迹。 |

**图 1。**二元报告的精确 Bloch 截面。单位圆盘是 $y=0$ 的合法截面；
红点是参考检查得到的球外失败证书，不是可制备态或物理轨迹。

**白话图景。**单独看这份整理规则，它把球压成圆盘，每个单独输出仍然合法。
但它允许平方比较中的正负缺额互相抵消。
把同一规则接到一个二元参考旁边，原先隐藏的负方向就出现了。
因此二元参考的作用，是保证整个平方缺额本身非负，不能只检查平均数恰好为零。

### 命题 13.2（参照没有覆盖的方向，可以藏住整个正缺额）

<a id="prop-c94-nonfaithful-qutrit"></a>

在 $\mathbb C^3$ 上定义

$$
E(x)=\operatorname{diag}\left(x_{11},x_{22},\frac{x_{11}+x_{22}}2\right),
 \quad
 R(\rho)=\operatorname{diag}\left(\rho_{11}+\frac{\rho_{33}}2,
                    \rho_{22}+\frac{\rho_{33}}2,0\right).
$$

令 $D=\operatorname{diag}(1,-1,0)$、$\mathcal S=\operatorname{span}_{\mathbb R}\{I,D\}$。
$R$ 是 CPTP，保持 $\mathcal S$ 读数，融合全部同读数态，并固定
$\tau=\operatorname{diag}(1/2,1/2,0)$。
但是 $D^2\notin\mathcal S$，所以原载体上的可见空间不成为代数。

**证明。**
$R$ 的 Kraus 算符可取

$$
P_1,\quad P_2,\quad
 \frac{\lvert 1\rangle\langle 3\rvert}{\sqrt2},\quad
 \frac{\lvert 2\rangle\langle 3\rvert}{\sqrt2}.
$$

其伴随乘积之和为 $I_3$，并直接给出上述 $R$。
设 $d=\operatorname{Tr}(\rho D)$；迹一性使

$$
R\rho=\operatorname{diag}((1+d)/2,(1-d)/2,0).
$$

故输出只依赖当前读数，且该读数保持。所给 $\tau$ 也确实固定。

然而 $D^2=\operatorname{diag}(1,1,0)$ 不可能写成 $aI+bD$：
前两坐标迫使 $a=1,b=0$，第三坐标便应为一而非零。
平方缺额在此恰为

$$
\boxed{E(D^2)-D^2=P_3\ge0,\qquad \operatorname{Tr}(\tau P_3)=0.}
$$

它不含负方向，却完整地落在参照的零支撑中，因而未被零平均排除。

两份状态 $P_3$ 与 $(P_1+P_2)/2$ 对当前 $D$ 读数同为零，
对新增关系 $D^2$ 的读数却分别为零与一。
这给一个准确的遗漏二态对。压到 $P_1+P_2$ 后，可见空间才成为对角代数；
原三维结论与压缩后的结论不能互换。
若在同一个例子中改选忠实参照 $I_3/3$，
则 $R(I_3/3)\ne I_3/3$，说明删除参照固定条件也允许这种非代数像。

**白话图景。**这里的整理过程连参考一起检查都合法，缺额也确实非负。
问题在于参照完全没有第三方向，整块缺额可以藏在那里，平均数仍是零。
忠实性表达的正是“参照覆盖当前声明的全部载体”。
若实际任务只在参照支撑内进行，可以明确压缩；若仍要比较原三维全部状态，就不能把第三方向悄悄删去。

<a id="section-14"></a>

## 14. 其余条件的反例：保留、融合与参照稳定各管什么

<a id="sec-c94-other-counterexamples"></a>

### 14.1 去掉读出保持：所有内容可以被一起抹平

取任意忠实 $\tau=I_2/2$ 和
$\mathcal S=\operatorname{span}_{\mathbb R}\{I,X,Z\}$，令
$R(\rho)=\tau\operatorname{Tr}\rho$。
这是 CPTP 映射，固定 $\tau$，也把所有同读数态送到同一输出。
但 $X$ 的正负纯态原有读数 $\pm1$ 都被变成零。
此时 $E$ 的像仅为 $\mathbb C I$，严格小于所声明的可见空间。
因此同读数融合不能替代已经可见内容的保持。

### 14.2 去掉同读数融合：原样保留可以留下任意不可见方向

对同一个 $\mathcal S$ 与 $\tau$，令 $R=\operatorname{id}$。
它保持读数、固定参照并完全正，但

$$
\rho_\pm=(I\pm Y)/2
$$

具有相同的 $X,Z$ 读数，却仍给出不同的完整输出。
这时 $E$ 的像是全部 $B(\mathbb C^2)$，而非 $\mathcal S+i\mathcal S$。
所以融合条件承担将完整输出限定为当前资料规范代表的任务。

### 14.3 去掉参照固定：物理整理可以偏离所声明的信息投影

### 命题 14.1（相干参照与去相干整理选择不同代表）

<a id="prop-c94-reference-not-fixed"></a>

令 $\mathcal S=\operatorname{span}_{\mathbb R}\{I,Z\}$，
$R(\rho)=P_0\rho P_0+P_1\rho P_1$，
并声明忠实参照

$$
\tau=\frac12(I+rX),\qquad 0<r<1.
$$

$R$ 满足 C94 的其余过程条件，却不固定 $\tau$。
在 $Z$ 读数为零的纤维中，v93 的 C93 选择 $\tau$，
而 $R$ 选择 $I_2/2$；二者不同。

**证明。**
去相干是 CPTP，保持 $Z$ 读数，且输出由该读数唯一决定。
但 $R\tau=I_2/2\ne\tau$。
$\tau$ 自己具有零 $Z$ 读数，且
$D(\tau\Vert\tau)=0$，因此它是该纤维的唯一最小相对熵态。
另一方面，对 $\tau$ 的两个本征值 $(1\pm r)/2$ 求对数，有

$$
D(I_2/2\Vert\tau)=-\frac12\log(1-r^2)>0.
$$

故物理去相干不实现这一参照下的 C93 选择。

这些反例的后果不同：有的删去已知内容，有的保留未读区别，
有的无法与内部参考共同保正，有的没有覆盖整个载体，
还有的实现了另一种参照下的整理。
它们均有合法的局部数学部分；不能把所有失败都称为“不是量子态”。

**白话图景。**保持要求已经看到的内容不丢；融合要求没被当前资料区分的输入不再产生不同规范输出；
稳定参照要求整理前后的比较起点相同。
三者作用在不同位置，删掉任何一个，都可以明确指出哪两份内容被错误合并、错误保留或错误偏置。

<a id="section-15"></a>

## 15. 相干二支复用，把遗漏的第三轴直接读出来

<a id="sec-c94-coherent-binary-axis"></a>

### 命题 15.1（实平方闭合仍会漏掉有向相位关系）

<a id="prop-c94-two-arm-y"></a>

在 $\mathcal S=\operatorname{span}_{\mathbb R}\{I,X,Z\}$ 中，Hermitian 平方及反交换子均闭合，
但相对相位为 $i$ 的两支仪器

$$
M_\pm=\frac{X\pm iZ}{2}
$$

会完全区分同资料的 $\rho_\pm=(I\pm Y)/2$。

**证明。**
对实数 $a,b,c$，
$(aI+bX+cZ)^2=(a^2+b^2+c^2)I+2abX+2acZ$，
故平方闭合，反交换子由平方极化得到。
但

$$
M_+^\dagger M_+=\frac{I+Y}{2},\qquad
 M_-^\dagger M_-=\frac{I-Y}{2},
$$

两效果相加为单位，所以它们构成完整仪器的两个分支。
正分支在 $\rho_+$、$\rho_-$ 上的概率分别为一、零，证明结论。

这个实际操作若被声明可用，它就供应一个旧读数无法回答的新问题。
仅从 $X,Z$ 可测，不能自动断言同根两支干涉、相对 $i$ 相位和相应控制已经可用。
Atlas 已明确区分数学生成一个代数与实际供应其读口 [3](#ref-atlas)。

一般地，对两个自伴关系 $A,B$ 与状态 $\rho$，定义

$$
\Gamma_\rho(A,B)=
 \begin{pmatrix}
 \operatorname{Tr}\rho A^2&\operatorname{Tr}\rho AB\\
 \operatorname{Tr}\rho BA&\operatorname{Tr}\rho B^2
 \end{pmatrix}\ge0.
$$

正性来自任意复数 $u,v$ 的
$\operatorname{Tr}\rho(uA+vB)^\dagger(uA+vB)\ge0$。
若 $T=\operatorname{Tr}\rho(A^2+B^2)>0$，其归一三维坐标为

<a id="eq-c94-operator-pair-bloch"></a>

$$
\boxed{\quad
 x=\frac{\operatorname{Tr}\rho(AB+BA)}{T},\qquad
 y=\frac{\operatorname{Tr}\rho\,i[A,B]}{T},\qquad
 z=\frac{\operatorname{Tr}\rho(A^2-B^2)}{T}.
 \quad}
\tag{15.1}
$$

因为 $\Gamma_{12}/T=(x-iy)/2$，其正性等价于 $x^2+y^2+z^2\le1$。
$T=0$ 时正 Gram 矩阵为零，全部相关支路权重为零，不作归一。
实相位比较读取反交换子，四分之一周比较读取交换子，第三方向记录两支平方量的差。
这三个量都来自同一对关系的正比较表。

**白话图景。**两个已知方向可以在实平面里反复组合，仍一直看不到另一侧的相位。
给两支加上一个明确的四分之一周相对方向，原来相同的两份内容就给出相反结果。
三维提升在这里同时记录共同变化、有向交叉与两支大小差；
代数闭合意味着这些复用所需的关系也必须被当前接口保留。

<a id="section-16"></a>

## 16. 补齐一个逻辑三轴，与保留全部重叠边际，要求不同

<a id="sec-c94-logical-versus-full-marginals"></a>

沿用 v91 的

$$
K=X_AX_BI_C,\quad L=I_AZ_BZ_C,\quad M=iKL=X_AY_BZ_C.
$$

它们是两两反对易的自伴对合，故

$$
\operatorname{Alg}^*(I,K,L)
 =\operatorname{span}_\mathbb C\{I,K,L,M\}\simeq M_2\otimes I_4.
$$

因此只给逻辑菜单 $I,K,L$ 时，补读一个 $M$ 就得到这个逻辑量子位的完整代数。
v93 已证明一个 $M$ 足以闭合指定的未来 $K$ 读出轨道 [7](#ref-v91)、[8](#ref-v93)。
它不能被推广为“一个 $M$ 决定全部三体内容”。

### 定理 16.1（完整重叠边际保持迫使全态恒等）

<a id="thm-c94-no-universal-decorrelation"></a>

设 $R$ 是 $H_A\otimes H_B\otimes H_C$ 上的保迹 $2$-positive 映射。
若对所有输入状态都保持完整 $AB$ 与 $BC$ 边际，则 $R=\operatorname{id}$。
因此，只要这些边际具有非单点纤维，就不存在同时融合全部同边际态的这种普适整理。

**证明。**
令 $E=R^*$。边际保持使 $E$ 逐点固定

$$
\mathcal A_{AB}=B(H_A\otimes H_B)\otimes I_C,
 \qquad
 \mathcal A_{BC}=I_A\otimes B(H_B\otimes H_C).
$$

对这两个代数内的任意 $a$，$a,a^\dagger a,aa^\dagger$ 均被固定。
主定理所用的 $2$-positive Schwarz 极化因此将每个这样的 $a$ 放入乘法域。
两个代数中分别含有全部单端算符；它们的乘积包括
$A\otimes B\otimes C$，这些简单张量线性张成全部整体矩阵空间。
乘法域关系遂迫使 $E$ 在全部矩阵上恒等，故 $R=\operatorname{id}$。

例如三 qubit 的 $\omega_\pm=(I\pm M)/8$ 均合法，
具有相同的 $AB$、$BC$ 完全混合边际，但它们支撑正交且整体不同。
恒等映射不融合这对状态，所以对应的融合要求不可能同时成立。

这个结论不需要参照稳定；读出保持与一个二元参考已经足够。
完整边际的普通乘积代数是全部 $B(H_A\otimes H_B\otimes H_C)$，
而逻辑 $K,L$ 菜单生成的只是一个带重数的 $M_2$。
v93 的最大熵补全始终可以作为已有经典资料的推断规则；
本定理限制的是对每份未知输入都精确保留这些边际的同一线性过程。

**白话图景。**只问两个逻辑方向，补上它们的交叉方向，确实可以闭合一个逻辑量子位。
但如果要求所有 $AB$ 问题和所有 $BC$ 问题都原样保留，
它们的复用已经能够组成整个三体的全部问题。
一扇对任意输入都满足这个要求的量子过程，只能原样保留整体，不能同时把不同关联抹成同一个输出。

<a id="section-17"></a>

## 17. 内部等距实现：局部融合没有删除整个 $\Omega$ 的区别

<a id="sec-c94-internal-dilation"></a>

采用式 [(9.2)](#eq-c94-reset) 的有限块形式，在本节记

$$
H=\bigoplus_\alpha(V_\alpha\otimes W_\alpha),\qquad
 \mathcal A=\bigoplus_\alpha(B(V_\alpha)\otimes I_{W_\alpha}),
$$

并将隐藏因子的忠实重置态记为 $\eta_\alpha$。
于是

$$
R(\rho)=\bigoplus_\alpha
 \operatorname{Tr}_{W_\alpha}(P_\alpha\rho P_\alpha)\otimes\eta_\alpha.
$$

该式描述局部可见输出。要理解完整内部过程，还应把产生这个输出的记录一起保留。

### 定理 17.1（块重置的显式内部记录等距）

<a id="thm-c94-record-isometry"></a>

将 $\eta_\alpha$ 对角化为
$\sum_r\lambda_{\alpha r}\lvert r\rangle\langle r\rvert$，定义

$$
K_{\alpha rs}
 =\sqrt{\lambda_{\alpha r}}
 (I_{V_\alpha}\otimes\lvert r\rangle\langle s\rvert)P_\alpha.
$$

若记录载体具有正交基 $\lvert \alpha,r,s\rangle$，则

<a id="eq-c94-record-isometry"></a>

$$
V\psi=\sum_{\alpha,r,s}K_{\alpha rs}\psi\otimes\lvert \alpha,r,s\rangle
\tag{17.1}
$$

满足 $V^\dagger V=I$ 且

$$
R(\rho)=\operatorname{Tr}_{\rm rec}(V\rho V^\dagger).
$$

完整记录输出保留全部输入区别；特别地
$V^\dagger(V\rho V^\dagger)V=\rho$。

**证明。**
对每个扇区求和，

$$
\sum_{r,s}K_{\alpha rs}^\dagger K_{\alpha rs}
 =I_{V_\alpha}\otimes\sum_s\lvert s\rangle\langle s\rvert=P_\alpha,
$$

这里使用 $\sum_r\lambda_{\alpha r}=1$，并将算符视为该扇区的嵌入。
再对 $\alpha$ 求和得到单位，所以 $V^\dagger V=I$。
对记录偏迹消去不同标签之间的交叉项，留下

$$
\sum_{\alpha,r,s}K_{\alpha rs}\rho K_{\alpha rs}^\dagger
 =\bigoplus_\alpha
   \operatorname{Tr}_{W_\alpha}(P_\alpha\rho P_\alpha)\otimes\eta_\alpha,
$$

即所需重置式。最后一个恢复恒等式由 $V^\dagger V=I$ 直接得到。

记录维数 $\sum_\alpha(\dim W_\alpha)^2$ 已足以完成这个构造。
若坚持纯初始记录的标准等距表示，且全部 $\eta_\alpha$ 忠实，
这些 Kraus 算符线性独立：不同扇区支撑不同，同扇区的右因子为独立矩阵单位。
其向量化外积之和是 Choi 矩阵，秩因而等于该数；
任何纯记录等距的 Kraus 数至少等于这个秩。
这只是所给通道的标准有限表示维数，不等同于原生装置取得成本或项目其他共享历史预算。

取记录的一份固定纯态，有限维等距可通过补齐正交基扩张成更大系统上的酉矩阵。
这承接 V80 的完整记录表示与 v90 的恢复区分 [5](#ref-v80)、[6](#ref-v90)。
实际供应何种门、初始记录与控制仍是过程合同的一部分；数学表示不自动采购装置。

若 $R\rho=R\sigma$ 而 $\rho\ne\sigma$，完整输出仍然不同。
区别可能位于记录边际，也可能位于系统与记录的联合关联，
不能一概宣称记录边际独自包含全部输入内容。

**白话图景。**局部整理可以让两份状态给出同一个可见输出。
把内部记录也保留下来，整个等距过程仍然能区分原来的两份内容。
区别被转移到记录和联合关联中，而非从整个 $\Omega$ 消失。
当前读口不访问这些区别，正是局部融合的含义。

### 17.1 参照非忠实时，可以在哪里合法压缩

### 命题 17.2（固定参照支撑是不变载体）

<a id="prop-c94-reference-support-invariant"></a>

若 $R$ 正、保迹，且 $R\tau=\tau$，令 $P=\operatorname{supp}\tau$。
那么支撑在 $PH$ 上的状态经 $R$ 后仍支撑在 $PH$。
若其余 C94 条件也成立，则压缩到 $PH$ 后可应用主定理，
得到 $\mathcal S_P+i\mathcal S_P$ 的普通代数闭合。

**证明。**
$\tau|_{PH}>0$。任意支撑在 $PH$ 的密度态都满足 $\rho\le c\tau$，
例如取 $c\ge1/\lambda_{\min}(\tau|_{PH})$。
正性给 $R\rho\le cR\tau=c\tau$，故输出支撑也在 $P$。
压缩后的 $R$ 仍保迹和 $2$-positive；原读数保持与同读数融合在该输入子域上继续成立。
$\tau$ 在此载体上忠实，故可应用定理 [4.2](#thm-c94-main)。

命题 [13.2](#prop-c94-nonfaithful-qutrit) 表明，压缩后的结论不能升级为原载体的结论。
此外，$R^2=R$ 时 $\tau_R=R(I/d)$ 自动固定。
由 $\rho\le I=d(I/d)$ 可知 $R\rho\le d\tau_R$，
故 $\operatorname{supp}\tau_R$ 容纳全部输出。
如果把输入任务也限制到这个输出支撑，必须明确改变了比较范围，
不能用它替代原全域的忠实参照前件。

**白话图景。**参照没有覆盖整个空间时，可以明确只研究它覆盖的那一部分。
稳定性保证这部分不会被过程送到外面，压缩后的参照便是忠实的。
但原来还允许其他输入时，不能因它们后来都被整理掉，就说原始全域的问题已经相同。

<a id="section-18"></a>

## 18. 未来自治与规范代表的动态交换

<a id="sec-c94-dynamics"></a>

以下设 $R=R_\tau$ 已满足 C94，$E=R^*$ 为保 $\tau$ 的条件期望。
对一个通道 $\Phi$，令 $F=\Phi^*$。
Atlas III 已证明当前代数上的未来自治当且仅当
$F(\mathcal A)\subseteq\mathcal A$ [3](#ref-atlas)。
本轮的接续是把这个既有条件写成实际规范整理 $R$ 的精确相容式。

### 定理 18.1（可见自治只给一侧相容）

<a id="thm-c94-autonomy-versus-commutation"></a>

有

$$
F(\mathcal A)\subseteq\mathcal A
 \quad\Longleftrightarrow\quad
 R\Phi=R\Phi R.
$$

在这个条件下，$R\Phi=\Phi R$ 当且仅当 $\Phi$ 保持 $R$ 的像空间，
等价地，当且仅当

$$
\Phi R=R\Phi R.
$$

**证明。**
因为 $E$ 的像是 $\mathcal A$、且在其上恒等，
$F(\mathcal A)\subseteq\mathcal A$ 等价于 $FE=EFE$。
取迹对偶即得 $R\Phi=R\Phi R$。
另一方面，$\Phi$ 保持 $\operatorname{ran} R$ 当且仅当
$R\Phi R=\Phi R$，因为 $R$ 是该像上的恒等投影。
两项结合即给交换；若已经交换，两项也同时成立。

特别地，额外要求 $\Phi\tau=\tau$ 仍不自动给出第二项。
一份稳定参照并不代表所有规范态都被该过程送成规范态。

### 命题 18.2（固定忠实参照的三态自治过程仍可不交换）

<a id="prop-c94-classical-noncommutation"></a>

在 $\mathbb C^3$ 上令

$$
\mathcal A=\operatorname{span}_\mathbb C\{P_1+P_2,P_3\},\qquad \tau=I_3/3,
$$

并取

$$
R(\rho)=\operatorname{diag}\left(
 \frac{\rho_{11}+\rho_{22}}2,
 \frac{\rho_{11}+\rho_{22}}2,\rho_{33}\right).
$$

定义测量–准备通道

$$
\Phi(\rho)=\sum_{i,j}p_{ij}\rho_{ii}P_j,
 \qquad
 (p_{ij})=
 \begin{pmatrix}
 1/2&1/4&1/4\\
 0&3/4&1/4\\
 1/2&0&1/2
 \end{pmatrix}.
$$

这里行标输入、列标输出。
则 $\Phi\tau=\tau$，其 $\mathcal A$ 读数自治，但 $R\Phi\ne\Phi R$。

**证明。**
Kraus 算符 $\sqrt{p_{ij}}\lvert j\rangle\langle i\rvert$ 给完全正性；
每行和为一给保迹，每列和为一给 $\Phi(I/3)=I/3$。
当前资料只需 $c=\rho_{33}$，未来第三方向概率为

$$
\frac14(\rho_{11}+\rho_{22})+\frac12\rho_{33}
 =\frac{1+c}{4}.
$$

故全部可见资料由当前资料决定，即自治成立。
但在 $P_3$ 处，

$$
\Phi R(P_3)=\operatorname{diag}(1/2,0,1/2),\qquad
 R\Phi(P_3)=\operatorname{diag}(1/4,1/4,1/2).
$$

两者不同，证明不交换。
它们具有同一可见资料；差为 $\operatorname{diag}(1/4,-1/4,0)$，
因此迹距离为 $1/4$，并由效果 $P_1$ 的概率差达到。

这对合法状态的差异也可通过等概率正反标签形成二元报告：
正标签问第一态的 $P_1$，反标签问第二态的 $I-P_1$，得到

$$
\gamma=\frac12\operatorname{diag}(1+\delta,1-\delta)
 =\frac12(I+\delta Z),\qquad\delta=\frac14.
$$

它是球内的动态不交换报告，与前节负概率的球外报告不同。
更一般地，自治时

$$
\Phi R-R\Phi=(\operatorname{id}-R)\Phi R.
$$

右侧准确表达：一个规范输入经过实际过程后，可以产生当前代数看不见的非规范内容。

**白话图景。**未来可见读数可以完全由当前可见读数决定，但实际过程仍可能在看不见的方向写入新内容。
所以“先整理再变化”与“先变化再整理”未必给同一个完整输出。
两份输出可以对所有当前仪表一致，却仍由一个新增读口区分。
要让两种次序真正交换，还要证明实际过程保持整族规范代表。

<a id="section-19"></a>

## 19. 相对锚下的精确酉协变条件

<a id="sec-c94-unitary-covariance"></a>

### 定理 19.1（酉变化与规范整理交换的充要条件）

<a id="thm-c94-unitary-reference-gauge"></a>

设 $U$ 为酉矩阵，且 $U^\dagger\mathcal AU=\mathcal A$。
记 $\kappa=U\tau U^\dagger$。则

<a id="eq-c94-unitary-reference-gauge"></a>

$$
R_\tau\operatorname{Ad}_U
 =\operatorname{Ad}_U R_\tau
 \quad\Longleftrightarrow\quad
 \log\tau-\log\kappa\in\mathcal A.
\tag{19.1}
$$

特别地，$U\tau U^\dagger=\tau$ 是充分条件，但一般比必要条件更强。

**证明。**
由定理 [11.1](#thm-c94-c93-implementation)，$R_\tau$ 是全部资料纤维的 C93 选择器。
$U$ 规范化 $\mathcal A$，故共轭把每份 $\mathcal A$ 资料纤维双射到另一份这样的纤维。
相对熵酉不变性与唯一最优给

$$
R_\kappa\operatorname{Ad}_U
 =\operatorname{Ad}_U R_\tau.
$$

这里 $\kappa$ 仍有相应块乘积形式，所以同一实现定理适用。
因此式 [(19.1)](#eq-c94-unitary-reference-gauge) 的左侧
等价于两个全域选择器 $R_\tau=R_\kappa$。

若 $\log\tau-\log\kappa\in\mathcal A$，
则 $D(\rho\Vert\tau)-D(\rho\Vert\kappa)$
在每份资料纤维上均为常数，故唯一最优点相同。
反过来，取包含 $I/d$ 的那份资料纤维。
它的最小共同支撑是 $I$，两种最优点均忠实。
若选择器相同，记共同最优为 $\sigma$，C93 平衡给

$$
\log\sigma-\log\tau\in\mathcal A,
 \qquad
 \log\sigma-\log\kappa\in\mathcal A.
$$

两式相减便得右侧条件。这也正是 v93 的参照等价判据在满支撑纤维上的应用 [8](#ref-v93)。

在块表示中，酉规范化子只在匹配的中心扇区间作置换，
并在对应左右因子上分别作用；这是 Atlas 的既有有限代数正规化子定理 [3](#ref-atlas)。
式 [(19.1)](#eq-c94-unitary-reference-gauge) 只要求隐藏参照
$\eta_\alpha$ 被送到目标扇区的隐藏参照。
只改变可见参照因子时，对数参照差属于 $\mathcal A$，
可以改变已知读数而不改变整理规则。

### 推论 19.2（连续自治历史只需稳定隐藏参照）

<a id="cor-c94-continuous-hidden-reference"></a>

若连续酉群从单位出发并保持 $\mathcal A$，则使用 Atlas 的已有生成元形式

$$
H_0=\bigoplus_\alpha
 (h_\alpha\otimes I+I\otimes k_\alpha).
$$

相应 $U_t=e^{-itH_0}$ 与 $R_\tau$ 对全部 $t$ 交换，当且仅当

$$
[k_\alpha,\eta_\alpha]=0\quad\text{对全部 }\alpha.
$$

不要求可见 $h_\alpha$ 固定其参照因子。

**证明。**
连续路径不置换离散中心扇区。
在每块中 $U_t=e^{-ith_\alpha}\otimes e^{-itk_\alpha}$。
将块重置式代入两种复合次序，左因子的演化与偏迹相容，
两式唯一可能的差别是
$\eta_\alpha$ 与 $e^{-itk_\alpha}\eta_\alpha e^{itk_\alpha}$。
它们对全部 $t$ 相同当且仅当在零点的导数
$-i[k_\alpha,\eta_\alpha]$ 为零；反向由对易的指数展开直接成立。

**白话图景。**整体换一套酉坐标，规范代表会跟着一起变。
如果要求仍用同一套整理规则，真正需要检查的是未读部分的参照是否被改变。
可见部分可以正常演化；它的变化已经被当前关系记录。
因此精确的锚不变条件比“整份参照完全不动”更弱，也更符合相对描述。

<a id="section-20"></a>

## 20. 完整历史中，哪些实际整理可以随时插入

<a id="sec-c94-history-insertion"></a>

### 定理 20.1（逐分支自治下的整理插入不变性）

<a id="thm-c94-history-insertion"></a>

给定有限历史中实际使用的完整仪器，若每个分支
$\Phi_x$ 都满足 $\Phi_x^*(\mathcal A)\subseteq\mathcal A$，
则在这些历史任意节点插入 $R$，不会改变完整结果概率或末端 $\mathcal A$ 读数。
该结论允许根据先前记录选择后续仪器，并允许一个始终未被操作的任意有限参考。

**证明。**
从任一结果路径的末端 $\mathcal A$ 效果开始，逐层沿对应分支拉回。
逐分支闭合保证每一层的拉回量仍在 $\mathcal A$；
插入整理只是在该处再作用一次 $E$，而 $E|_{\mathcal A}=\operatorname{id}$，故概率不变。
取末端效果为单位，保留该路径的发生概率；
对全部末端效果比较，保留其未归一的受限后态。
按记录自适应选择时，每条给定路径的分支顺序已固定，同一个证明逐条适用。

加入未操作参考后，$E\otimes\operatorname{id}$ 逐点固定
$\mathcal A\otimes B(H_{\rm ref})$，
而每个分支的张量扩张也保持这个空间。
已推出的完全正性保证联合对象合法，同样的逐层论证继续成立。

Atlas 已给出逐分支自治与非选择性自治的区别，V80 已给完整结果树的拉回闭合
 [3](#ref-atlas)、[5](#ref-v80)。
本轮利用新取得的物理整理 $R$，将它们接成上述实际插入不变性。
只检查分支总和的通道不足以得到该结论；被忽略的结果标签可能携带区别。
以后若访问整理记录或引入不保持 $\mathcal A$ 的门，观察合同已经扩大，
必须重新检查相应闭合，不能继续援引本定理。

**白话图景。**如果每一条实际后续分支都只使用当前闭合的关系，
就在历史中加入一次规范整理，也不会改变任何该合同下的结果。
所有成功、失败和其他标签都要保留在检查里。
一旦后来打开原来不读的记录，或者用新门把隐藏关系转回来，问题就已经变大，需要新的闭合分析。

<a id="section-21"></a>

## 21. 关系层级就是分辨率层级：共同参照下的塔式相容

<a id="sec-c94-tower"></a>

本节在同一有限载体、同一忠实内部参照 $\tau$ 上考虑不同可见代数。
它把单次约化放回一个更大的关系结构：哪些细分可以一致组合，
何时新增一层确实增加内容，何时只是在重复已经稳定的描述。

### 定理 21.1（嵌套分辨率的塔式关系）

<a id="thm-c94-tower"></a>

设 $\mathcal A\subseteq\mathcal B\subseteq B(\mathcal H)$ 为含单位的普通
$C^*$ 子代数，二者均由同一忠实 $\tau$ 的模流保持。
分别记 C94 的唯一约化为 $R_{\mathcal A},R_{\mathcal B}$。
则

<a id="eq-c94-tower"></a>

$$
\boxed{R_{\mathcal A}R_{\mathcal B}
=R_{\mathcal A}=R_{\mathcal B}R_{\mathcal A}.}
\tag{21.1}
$$

对任意密度态 $\rho$，还有

<a id="eq-c94-three-entropy"></a>

$$
D(\rho\Vert\tau)
={}D(\rho\Vert R_{\mathcal B}\rho)
 +D(R_{\mathcal B}\rho\Vert R_{\mathcal A}\rho)
 +D(R_{\mathcal A}\rho\Vert\tau),
\tag{21.2}
$$

<a id="eq-c94-resolution-loss"></a>

$$
D(\rho\Vert R_{\mathcal A}\rho)
={}D(\rho\Vert R_{\mathcal B}\rho)
 +D(R_{\mathcal B}\rho\Vert R_{\mathcal A}\rho).
\tag{21.3}
$$

**证明。**
令 $E_{\mathcal A}=R_{\mathcal A}^*$、$E_{\mathcal B}=R_{\mathcal B}^*$。
因为 $E_{\mathcal B}$ 在 $\mathcal B$ 上为恒等，且
$\operatorname{ran} E_{\mathcal A}=\mathcal A\subseteq\mathcal B$，
有 $E_{\mathcal B}E_{\mathcal A}=E_{\mathcal A}$。
另一方面，$E_{\mathcal A}E_{\mathcal B}$ 为 unital CP 映射，值域在
$\mathcal A$，固定 $\mathcal A$ 并保持 $\tau$。
两映射的双模性质给出

$$
E_{\mathcal A}E_{\mathcal B}(a_1xa_2)
=a_1E_{\mathcal A}E_{\mathcal B}(x)a_2
\quad(a_1,a_2\in\mathcal A).
$$

因此它也是保 $\tau$ 的 $\mathcal A$ 条件期望。
由本轮块形式的唯一性，它等于 $E_{\mathcal A}$。
取迹伴随即得式 [(21.1)](#eq-c94-tower)。

先对 $\rho$ 使用 $\mathcal B$ 的式 [(11.1)](#eq-c94-pythagorean)，
再对 $R_{\mathcal B}\rho$ 使用 $\mathcal A$ 的同一恒等式，
并代入 $R_{\mathcal A}R_{\mathcal B}\rho=R_{\mathcal A}\rho$，
得到式 [(21.2)](#eq-c94-three-entropy)。
与直接使用 $\mathcal A$ 的勾股恒等式比较，得到式
[(21.3)](#eq-c94-resolution-loss)。

这些运算对非满秩输入也成立。
对任何 C94 块重置和正态 $\sigma$，可见边缘的零方向在原正态中也必为零；
正块矩阵的跨块项不能越出对角块支撑。
隐藏参照忠实，故块式给
$\operatorname{supp}\sigma\subseteq\operatorname{supp} R_{\mathcal C}\sigma$。
依次应用可得

$$
\operatorname{supp}\rho\subseteq\operatorname{supp} R_{\mathcal B}\rho
\subseteq\operatorname{supp} R_{\mathcal A}\rho\subseteq\operatorname{supp}\tau.
$$

全部相对熵均有限，对数在相应支撑上使用，没有无穷量相减。

### 推论 21.2（递归停止的两个层次）

<a id="cor-c94-stop"></a>

对给定输入 $\rho$，新增这一层不改变规范补全，当且仅当

$$
D(R_{\mathcal B}\rho\Vert R_{\mathcal A}\rho)=0
\quad\Longleftrightarrow\quad
R_{\mathcal B}\rho=R_{\mathcal A}\rho.
$$

若对全部输入都不改变，则当且仅当 $\mathcal A=\mathcal B$。

**证明。**
第一条由相对熵的非负性与等号条件。
第二条由全态相等推出两个线性约化相等，再取伴随与值域；反向显然。

对一个输入停止，不意味着已经恢复它的全部内容。
例如 $\rho=\tau$ 时，无论 $\mathcal A\subsetneq\mathcal B$ 是否严格，
两种规范代表都为 $\tau$。
也不能先执行粗约化、再执行细约化来恢复丢失资料；
塔式关系恰好说明这种次序的输出仍是粗代表。
式 [(21.2)](#eq-c94-three-entropy) 中的细代表，取自原输入的细读数。

在固定 $M_d(\mathbb C)$ 中，每一次严格增加代数都严格增加其实自伴维数，
故这样的严格层级至多增加 $d^2-1$ 次。
这只是固定有限载体中的结论；若继续引入内部记录、扩大载体或改变可访问关系，
本文没有推出整个 $\Omega$ 存在一个绝对最高分辨率。
共同参照与嵌套关系都被证明实际使用了，不能删掉它们而宣称任意两种切分都能交换。

**白话图景。**粗读口看见的内容包含在细读口里面。
在同一参照下，先用细读口整理再退回粗读口，和一开始就只用粗读口整理，会得到同一个结果。
多看这一层究竟增加了多少信息，有一项严格非负的差额。
差额为零，表示这份内容在这一次细分中已经稳定；
它不表示所有更深关系都不存在，更不表示粗化以后还能凭空找回细节。

<a id="section-22"></a>

## 22. 怎样接回现有量子力学公理

<a id="sec-c94-qm"></a>

C94 解决的是项目重建链中的“可见切分何时成为物理约化”这一环。
为避免将一环写成无前件的全部理论，以下把各环所消费的关系条件明确列出。
基础接口取自项目 V80；本轮定理负责其中可见代数、完全正约化、内部记录及分辨率相容的加强
 [5](#ref-v80)、[8](#ref-v93)。

### 22.1 从共同正比较到 Hilbert 表示

设内部有限关系标签为 $x$，共同复比较核为 $K(x,y)$，
每一个有限 Gram 矩阵都半正定。
在形式向量的有限线性组合上定义

$$
\left\langle\sum_x c_xe_x,\sum_y d_ye_y\right\rangle
=\sum_{x,y}\overline{c_x}d_yK(x,y).
$$

正半定形式的零范数向量与全部向量正交，故可以商去零空间。
若共同核的秩为有限 $d$，所得空间即 $d$ 维复 Hilbert 空间，
且 $K(x,y)=\langle x|y\rangle$。
这是表示定理；*共同复核与所有有限比较的正性是前件*。
单凭每一个二元或三元窗口分别合法，并不能保证它们来自同一个全局正核。

### 22.2 从可加读出到效果与 Born 概率

在这一表示内，假设二元事件读出对混合仿射、归一且在全部密度态上非负。
有限维迹配对给唯一 Hermitian $F$，使

$$
p_F(\rho)=\operatorname{Tr}(\rho F).
$$

在全部秩一态上有 $0\le p_F\le1$，等价于 $0\le F\le I$。
互斥穷尽结果的可加性给 $\sum_xF_x=I$，即 POVM 结构。
当同根相干比较的读出被校准为方向投影
$F=\lvert \phi\rangle\langle \phi\rvert$ 时，

$$
p_F(\lvert \psi\rangle\langle \psi\rvert)=|\langle\phi|\psi\rangle|^2.
$$

因此平方律的表示依赖相干比较、线性混合与共同正性；
“递归可以停止”本身不能替代这几个前件。
C94 增加的是平方比较的 Schwarz 缺额如何被忠实参照迫为零，
从而把已保留的读出锁成普通乘积闭合的代数。

### 22.3 从完整关系保持到酉门与 Schrödinger 方程

若实际线性过程保持共同内积，它满足 $U^\dagger U=I$，是等距。
在同一有限载体上可逆时即为酉矩阵。
项目 V80 从更具体的完整强度关系与定向锚点给出这一接口，
不能把仅保持某一个当前态、某条曲线或少量读数替代完整关系保持 [5](#ref-v80)。

对满足 $U(0)=I$ 的实际 $C^1$ 酉族 $U(t)$，令

$$
H(t)=i\hbar\dot U(t)U(t)^\dagger.
$$

微分 $U(t)U(t)^\dagger=I$ 得 $H(t)^\dagger=H(t)$。
于是 $\lvert \psi(t)\rangle=U(t)\lvert \psi(0)\rangle$ 满足

$$
i\hbar\frac{d}{dt}\lvert \psi(t)\rangle=H(t)\lvert \psi(t)\rangle,
\qquad
i\hbar\dot\rho=[H,\rho].
$$

若还具有一参数群结构，生成元可取常量。
平滑门参数只有在与内部时钟及单位校准连接以后才是物理时间。
内部参照的模参数不因同样写成 $t$ 就自动成为实验室时间。

### 22.4 从内部等距与记录到一般量子过程

若实际整体过程为等距 $V$，只读系统而不读内部记录，
则 $\Phi(\rho)=\operatorname{Tr}_E(V\rho V^\dagger)$。
取记录正交基给 $K_j=(I\otimes\langle j\rvert)V$，于是

$$
\Phi(\rho)=\sum_jK_j\rho K_j^\dagger,
\qquad\sum_jK_j^\dagger K_j=I.
$$

附加任意参考后，每一项仍为正算符的共轭变换，故 $\Phi$ 完全正且保迹。
反向由 Kraus 族可构造 $V=\sum_jK_j\otimes\lvert j\rangle$。
这里是有限维表示的双向对应；某台具体装置是否实际可制备，还须给其内部资源关系。

C94 对特殊但重要的一类过程完成了更强的推导：
它只要求一个二元参考的正性，就由同纤维融合、读数保持及忠实参照
推出全部 Kraus 结构。*这不是任意 2-positive 映射都完全正的命题。*
全域投影与忠实固定参照是该加强不可省略的条件。

### 22.5 从独立复合到张量积，从非扰动到 Lüders 更新

若两个独立内部关系系统的共同核按
$K_{AB}((a,b),(a',b'))=K_A(a,a')K_B(b,b')$ 组合，
其形式向量商空间自然等距于 $\mathcal H_A\otimes\mathcal H_B$。
这是独立复合的条件，不能把任意两个有关联的内部对象都预先认作独立因子。

对一个有记录结果的 CP 操作分支 $\Phi_P$，若效果为投影 $P$，
且对 $P\mathcal H$ 中*每一个*纯态都不扰动，才得到 Lüders 分支
$\Phi_P(\rho)=P\rho P$。
简证如下。若 $P=0$，全部 Kraus 算符均为零，结论直接成立。
以下设 $P\ne0$。Kraus 条件 $\sum_jK_j^\dagger K_j=P$ 给
$K_j(I-P)=0$。每个纯态输出仍沿自身方向，迫使
$K_j\lvert \psi\rangle=c_{j,\psi}\lvert \psi\rangle$；再对同子空间内两向量的叠加使用同一条件，
得 $K_jP=c_jP$。最后 $\sum_j|c_j|^2=1$，结论成立。
仅要求结果可重复，并不固定子空间内的附加酉变化 [5](#ref-v80)。

### 22.6 重建依赖总表

| 标准结构 | 实际使用的内部关系条件 | 本轮位置 |
|---|---|---|
| 复 Hilbert 状态空间 | 共同复比较、全有限 Gram 正性、商去零方向 | 继承 V80 的表示起点；C94 不重新推导复数 |
| 效果与 Born 读出 | 全态仿射读出、二元归一、同根方向强度校准 | $0\le F\le I$、$p=\operatorname{Tr}\rho F$；平方缺额闭合由本轮加强 |
| 普通可见算符代数 | 保读数、同纤维融合、二元参考正性、忠实固定参照 | C94 推出原矩阵乘法闭合 |
| 局部物理约化 | 上一行加由定理推出的参照模相容 | 唯一块重置，自动 CPTP，恰为 C93 |
| 封闭可逆酉过程 | 保持共同完整关系、同载体可逆 | 既有酉接口；本轮给观察切分的协变条件 |
| 一般过程与记录 | 内部等距、未读取的内部记录 | Kraus 表示；C94 构造具体内部等距 |
| 独立系统张量积 | 独立核的乘法组合与一致复比较 | 显式独立复合前件 |
| 投影测量后态 | 投影效果，并对其全部纯态不扰动 | 推出 Lüders；不由仅重复性推出 |
| 连续量子动力学 | 实际 $C^1$ 酉族与内部时钟校准 | Schrödinger 方程；模流不自动等于时间 |
| 分辨率递归相容 | 同一忠实参照、嵌套且模相容的可见代数 | 塔式关系与精确信息增量 |

**白话图景。**态描述当前可被共同检验的关系，效果提出一次有正反两个结果的问题。
门改变关系，记录把结果和未读区别留在整体内部。
当全部关系保持而过程可逆时，门就是酉门；当一部分记录不再被当前读口访问时，
局部看到的是完全正过程。
这一轮补齐的是：一个读口到底保留了哪些关系，才足以支持这样一台对全部输入都合法的整理装置。
答案是一个与内部参照相容的可见代数。

<a id="section-23"></a>

## 23. 球、轨迹、参照与关系场：保留直觉的准确形式

<a id="sec-c94-field"></a>

### 23.1 二元三维是共同比较的局部坐标

任一归一二元正报告可写为

$$
Q=\frac{I+xX+yY+zZ}{2},\qquad x^2+y^2+z^2\le1.
$$

这个球包含相位敏感的两个横向坐标与一个强度差坐标。
本轮的二元参考见证与两个关系的 Gram 提升，使用同一三坐标表示；
合法报告落在球内，失效候选可以落在球外。
不同二元比较可以共享、组合和互相制约；
但“每个窗口有三个坐标”不等于“整个多体状态仅有三个自由度”。
例如一个 $d$ 维密度态通常有 $d^2-1$ 个实参数，多个窗口还须满足共同相容关系。
内容寻址使同一内容在不同描述中需要一致识别，
不会取消这些独立比较所实际拥有的自由度。

### 23.2 切向量描述门在一点的作用，不能替代完整门

给归一纯态曲线选取水平相位规范，可令
$\langle\psi|\dot\psi\rangle=0$。
酉演化在这一规范下的切向量为

$$
v_H(\psi)=-\frac{i}{\hbar}
\bigl(H-\langle\psi|H|\psi\rangle I\bigr)\lvert \psi\rangle.
$$

所以“态与切向正交”是局部水平描述。
若取两态相位使 $\langle A|B\rangle=\cos\theta\ge0$，且
$0<\theta\le\pi/2$，则有精确分解

$$
\lvert B\rangle=\cos\theta\lvert A\rangle+\sin\theta\lvert \eta\rangle,
\qquad\langle A|\eta\rangle=0,\quad\left\lVert \eta\right\rVert=1.
$$

$B=A+\delta v$ 只是一阶近似，不能直接作为有限态变化的归一等式。
不同门在一个态上可以有相同切向作用，却在其他态上不同；
因此内容即地址的识别须声明比较范围，是单态、全态、结果历史还是完整内部记录。

### 23.3 圆、椭圆与周期需要哪些关系

对 qubit 的固定 Hamiltonian，Bloch 向量绕固定轴旋转。
非平凡纯态轨迹是单位球面上的圆；能量本征态或纯标量 Hamiltonian 给定点，
混态则在其固定半径球面上运动。
只有相应非平凡圆位于过球心的平面时才是大圆测地线。
这个圆投影到另一读出平面可以成为椭圆或线段。
因此椭圆可由读出投影产生，不能仅由“禁止某方向”或“有逆门”唯一推出。

在更高维纯态中，固定 Hamiltonian 的轨迹可能同时含多个独立能隙频率。
若初态在能量本征值 $E_j$ 上有非零分量，射线周期 $T>0$ 必须满足

$$
(E_j-E_k)T/\hbar\in2\pi\mathbb Z
\quad\text{对全部实际占据的 }j,k.
$$

没有共同这样的 $T$，就不能把恒定门生成元的演化概称为一条闭圆。
该结论直接由各本征分量的相位差得到。

能量在已校准的时间关系中表现为生成元，控制改换是整个系统、控制器与记录的联合过程。
仅计算出一个新门的描述，尚不等于已经供应实施该门所需的内部装置状态。
把装置和记录都纳入 $\Omega$，使这些条件成为可追问的内部关系，
并不会让它们无条件消失。

### 23.4 换描述与换物理参照要分别检查

共同改变坐标 $\rho\mapsto U\rho U^\dagger$、
$\mathcal A\mapsto U\mathcal AU^\dagger$、$\tau\mapsto U\tau U^\dagger$
时，全部定理协变，概率不变。
固定读口却把 $\tau$ 换成另一实际状态，则是在改变规范比较，
只有满足已证明的参照等价条件才保证同一规范代表。
本轮的模相容和酉协变判据给出了这条界线。
“没有绝对 anchor”适合表达描述应共同协变；
它并不等于每一种物理参考态在固定装置下都等效，也不单独推出空间各向同性。

有限算符代数及其模流、嵌套和状态关系，确实形成一个关系动力学框架。
把它进一步称为物理场论，需要另给哪些关系定义时空区域、
局域组合、传播规律及连续极限。
本文没有由有限 C94 推出具体规范群、引力场方程或 Yang–Mills 质量隙。
这些目标要在同样的反向二态方法下继续声明与检验新的内部条件。

**白话图景。**球是每一次二元比较的统一语言，许多这样的球通过共同内容相互约束。
切向量告诉你一扇门此刻怎样推动态，完整门还告诉你它对其他内容怎样作用。
圆和周期来自生成元及频率关系，椭圆可以来自读口的投影。
换坐标时把态、读口和参照一起换，描述仍一致；
换一份实际参照，则要重新检查它与当前切分的相容。
这让“所有概念都是关系”成为能够逐项检验的理论，而不只是一幅图。

<a id="section-24"></a>

## 24. 近期研究的连接与本轮完整白话

<a id="sec-c94-close"></a>

### 24.1 相关初态赋值与全域合法性的边界

2026 年 10 月 19 日的 Fullwood–Ye 预印本
*Assignment maps for arbitrary reduced quantum dynamics*
研究将系统态赋为相关系统–环境初态的映射。
原摘要明确说明，其赋值映射保持 Hermitian 性和迹，但牺牲全域正性；
它们的合法性须在声明的输入域上分析，某些非零体积有效域可以容纳初始纠缠
 [12](#ref-fullwoodye2026)。
本轮仅核读官方摘要与元数据，未据此援引未核读的定理。

这与 C94 的边界直接相接：如果只要求一组实际输入上的合法性，
相关赋值可以丰富得多；若要求同一线性映射对全部输入、并对一个二元参考都合法，
就进入本轮的刚性范围。
因此需要写出模型的有效域，不能把子域实现与全域量子门混在一起。
本轮的块重置定理也不排除实际宇宙中的系统–环境初始关联；
它限制的是指定观察切分是否存在所要求的全域规范约化。

### 24.2 一个完整候选的白话表述

> 在整体内部选一个读口，它只看见一部分关系。
> 两份内容若给这个读口完全相同的回答，就属于当前同一份可见资料。
> 如果存在一种统一的内部整理：对任何输入都保持这些回答，
> 把同资料的输入整理成同一个局部代表，
> 保持一份照到当前全部方向的参照，
> 并且旁边放一个二元量子参考时，联合回答仍没有负概率，
> 那么这个读口所保留的关系必须能完整地相乘。
> 它们组成一个可见代数。
>
> 整体随之分成可见内容与当前不读的内容。
> 可见内容保持，未读部分按共同参照整理；这台装置唯一，
> 也正是上一轮最小相对熵原则选出的代表。
> 在上述保留完整记录的等距实现中，整理出去的区别没有从整个模型消失，
> 它仍在 $\Omega$ 的内部记录以及记录和系统的关联中。
>
> 不同分辨率若使用同一参照并相互嵌套，
> 它们的整理顺序按严格的塔式关系一致。
> 每增加一层关系，新增多少内容都有一项明确的信息差额。
> 某次差额为零，就表示这份内容在这一层已经稳定；
> 是否还有更细关系，仍由更大的内部比较决定。

这段话对应的正式候选只有 C94 一项。
代数闭合、完全正性、隐藏重置、模相容、C93 实现、内部等距与塔式相容均为其
在明确继承载体中的定理或推论。
这既保留了“关系在关系中寻找自己的约束”的思路，
也给出了每个逻辑步骤可以在哪里被一对状态或一个二元报告反驳。

### 24.3 本轮交付与核对范围（原稿记录）

本文包含候选、主定理、有限维证明、各条件的反向见证、三维二元提升、
标准量子结构的依赖表以及与项目和近期文献的对应范围。
数学结论采用解析推导，并由独立审阅交叉核查。
文档生成与版面渲染仅用于交付 PDF 与 TeX；
未执行数学程序、CAS、数值求值、枚举、模拟或测试。
项目保持只读；没有声称本轮新定理已经加入仓库或通过 Lean 形式化。

<a id="references"></a>

## 来源、版本与核读范围

<a id="ref-currentrepo"></a>

### [1]

the-omega-institute，*trureturing* 项目公开首页，
[GitHub 项目](https://github.com/the-omega-institute/trureturing)。
2026 年 11 月 3 日（新加坡）核读当前默认 `dev` 分支页面。
当前页面读取未取得可固定的新 SHA；理论精确版本使用下列已存固定快照。

<a id="ref-targetcriterion"></a>

### [2]

trureturing，*TargetRecoveryCriterion.lean*，
[当前源码](https://github.com/the-omega-institute/trureturing/blob/dev/D5/S3/ConceptDynamics/Restoration/TargetRecoveryCriterion.lean)。
本轮核读 `target_recovery_criterion` 的声明与证明：
非空来源上的目标因子化、同纤维恒定及缺陷关系为空等价。
该文件使用已有因子化判据；不据此推断可计算性、完全正性或实现成本。
未执行 Lean 构建。

<a id="ref-atlas"></a>

### [3]

trureturing，*Quantum Origin: Endogenous Cut Atlas and Discrete Reconstruction Boundaries III*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/QUANTUM_ORIGIN_ENDOGENOUS_CUT_ATLAS_AND_DISCRETE_RECONSTRUCTION_BOUNDARIES_III.md)。
固定提交为 `c63ab162315fddd0801cbe9f47dbf3eda6e13360`，2026 年 11 月 2 日。
本轮核读第 9–17 节的预测纤维、条件期望、动态自治、逐分支历史、
预测与物理整理之别、有限代数正规化子和生成元结构；并核对后续自适应历史接口。
本文把这些已有结果接到新取得的物理充分约化，不重新计作新定理。

<a id="ref-omega"></a>

### [4]

trureturing，*AURIC Omega Static Compatibility Fiber Theory*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。
本轮核读同资料及全目标等价、未来统计关系、统计逆与量子恢复的区别，
以及实部投影的非完全正性例子。
本文 Bell 输入已归一，因此负特征值为 $-1/4$；
原稿未归一 Choi 表中的 $-1/2$ 与此是同一归一尺度差异。

<a id="ref-v80"></a>

### [5]

trureturing，V80：*全结果二元差分不增、有限有向锚与内生量子过程*，
[固定提交原文](https://github.com/the-omega-institute/trureturing/blob/c63ab162315fddd0801cbe9f47dbf3eda6e13360/docs/develop/theory/AURIC_ALL_OUTCOME_BINARY_DIFFERENCE_NONEXPANSION_FINITE_ORIENTED_ANCHORS_AND_ENDOGENOUS_QUANTUM_PROCESSES_V80.md)。
沿用共同有限复比较接口、实际完整过程、读出效果、记录仪器、独立复合及连续时间的分层前件。
本轮核对重建总表与完整结果树接口，并承接前稿已核读的相关证明。

<a id="ref-v90"></a>

### [6]

本对话研究稿，*AURIC v90：二元内生中点、平方可恢复性与共享量子结构*，2026。
用于完整记录、局部恢复与共同内部参考的已有区分。

<a id="ref-v91"></a>

### [7]

本对话研究稿，*AURIC v91：重叠二元关系、三轴提升与量子 Markov 拼接*，2026。
用于指定逻辑三轴 $K,L,M$ 的已有构造；不将这一受限菜单当成全部重叠边际资料。

<a id="ref-v93"></a>

### [8]

本对话研究稿，*AURIC v93：内生纤维平衡、支撑递归与量子关系场*，2026，32 页。
本轮承接共同最小支撑、C93、唯一相对熵补全、先对数后压缩、参照等价、
精确勾股、固定纤维预测及规范选择器不自动为量子通道的边界。

<a id="ref-takesaki1972"></a>

### [9]

Masamichi Takesaki，
*Conditional expectations in von Neumann algebras*，
Journal of Functional Analysis **9**(3)，306–321，1972。
[DOI: 10.1016/0022-1236(72)90004-3](https://doi.org/10.1016/0022-1236(72)90004-3)。
本轮核读出版商摘要与元数据：模不变性与保持相应忠实权的条件期望存在性相连。
未取得全文；本文有限维版本另给完整证明，不冒称已核读一般情形的全部技术证明。

<a id="ref-petz1986"></a>

### [10]

Dénes Petz，
*Sufficient Subalgebras and the Relative Entropy of States of a von Neumann Algebra*，
Communications in Mathematical Physics **105**，123–131，1986。
[作者公开全文](https://math.bme.hu/~petz/pdf/29suff.pdf)；
[DOI: 10.1007/BF01212345](https://doi.org/10.1007/BF01212345)。
本轮核读充分性定义、定理 4、推论 5 和定理 6 的相关内容。
本文不把指定状态对的充分性与对全部输入的回缩混同；特殊块情形的恢复与熵分解均自足证明。

<a id="ref-koashi2002"></a>

### [11]

Masato Koashi、Nobuyuki Imoto，
*Operations that do not disturb partially known quantum states*，
Physical Review A **66**，022318，2002。
[DOI: 10.1103/PhysRevA.66.022318](https://doi.org/10.1103/PhysRevA.66.022318)。
[作者预印本 quant-ph/0101144v2](https://arxiv.org/pdf/quant-ph/0101144)
的标题为 *What is Possible Without Disturbing Partially Known Quantum States?*。
本轮核读导言及第五节分解与定理 3，用作已知态族分解的背景；其量词不同于 C94 全输入要求。

<a id="ref-fullwoodye2026"></a>

### [12]

James Fullwood、Weixiang Ye，
*Assignment maps for arbitrary reduced quantum dynamics*，
[arXiv:2610.27338](https://arxiv.org/abs/2610.27338)，2026 年 10 月 19 日提交。
本轮仅核读官方原摘要和元数据。
其 Hermitian 保持、保迹赋值映射牺牲全域正性，并分析含初始关联的有效输入域；
本文仅据此说明全域与有效域条件的必要区分，没有引用未核读定理或宣称同行评审状态。
